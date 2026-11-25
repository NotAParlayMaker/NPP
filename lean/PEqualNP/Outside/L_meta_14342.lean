import PEqualNP.Defs

-- The signed live-wire calculus follows L-meta-10532 and L-meta-12325.

namespace PEqualNP.Outside.L_meta_14342

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

end PEqualNP.Outside.L_meta_14342

namespace PEqualNP.Outside.L_meta_14342

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

end PEqualNP.Outside.L_meta_14342

namespace PEqualNP.Outside.L_meta_14342
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







end PEqualNP.Outside.L_meta_14342

namespace PEqualNP.Outside.L_meta_14342

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
end PEqualNP.Outside.L_meta_14342

namespace PEqualNP.Outside.L_meta_14342

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
end PEqualNP.Outside.L_meta_14342

namespace PEqualNP.Outside.L_meta_14342
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

end PEqualNP.Outside.L_meta_14342

namespace PEqualNP.Outside.L_meta_14342

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
end PEqualNP.Outside.L_meta_14342

namespace PEqualNP.Outside.L_meta_14342.B0
def bank : List ℕ := [0x88888888888888888888840092885266024a94a000001fe000001fe01fe218024f21c998193e73,0x22a2a2a2a2a2a2a2a2a2810c4e3010055138cc600000000001fe0001fe00063138c0601fe6e339c,0x98989898989898989898c008d80c1c784360f800001fe000001fe00000038023f03871e18fc3e0,0x50505050505050505050010a002009006c0029601fe0001fe000001fffe4043c00c07e01f003ff,0x16161616161616161616401a00033a0003c95001fe0000000001fffe0001807c000ff8001fffc00,0x585858585858585858587ee00001ef6aa800000000000001fffe00000001ff80000fffffe000000,0x6060606060606060606033a55254000000000001fffffffe000000000001fffffff000000000000]
def f0 : ℕ := 0x4104104104402288cc8ac000fc003f006023cccccfc
def f1 : ℕ := 0x14514514514042820a0d0503f03f000fc843c30f0f0f
def f2 : ℕ := 0x38e38e38e3a06803700750fc000003f0307c03f00ff0
def f3 : ℕ := 0x492492492481313020a2ca000000fc0fc1b13030f3cf
def f4 : ℕ := 0xa28a28a28a3e8001d5500000003ffc003f8003fff000
def f5 : ℕ := 0xc30c30c30c1b9554000000ffffc000003ffffc000000
def s0 : List ℕ := [f0,f1,f2,f3,f4,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w0 : Wide 88 6 s0 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p0 : Weak 158 88 := relaxed (pick [2,3,7,8,14,15,17,18,21,22,23,24,25,26,29,30,33,34,36,37,41,42,43,44,46,47,52,53,55,56,58,59,60,61,62,63,64,65,66,69,70,71,72,74,75,76,86,87,88,90,91,92,102,103,104,106,107,108,110,111,112,114,115,116,118,119,120,122,123,124,134,135,136,138,139,140,142,143,144,146,147,148,150,151,152,154,155,156] (by decide) (by decide) (by decide))
def r0 : Rule 158 8 := cutRule 8 p0 w0
def f6 : ℕ := 0x28f
def f7 : ℕ := 0x53c
def f8 : ℕ := 0x873
def s1 : List ℕ := [f6,f7,f8]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w1 : Wide 6 3 s1 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p1 : Weak 158 6 := relaxed (pick [14,15,52,53,62,63] (by decide) (by decide) (by decide))
def r1 : Rule 158 8 := cutRule 8 p1 w1
def f9 : ℕ := 0x78c
def f10 : ℕ := 0xd70
def s2 : List ℕ := [f7,f9,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w2 : Wide 6 3 s2 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p2 : Weak 158 6 := signedPick 17 [17,18,55,56,64,65] (by decide) (by decide) (by decide)
def r2 : Rule 158 8 := cutRule 8 p2 w2
def f11 : ℕ := 0x4080bccf870e1f
def f12 : ℕ := 0x21532530318f993
def f13 : ℕ := 0xaaa8982b003c64c1fc
def f14 : ℕ := 0x15557015400f0f80fe0
def f15 : ℕ := 0x1fffdaa000f00fff000
def s3 : List ℕ := [f11,f12,f13,f14,f15]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w3 : Wide 37 5 s3 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p3 : Weak 158 37 := relaxed (pick [0,1,2,3,4,25,26,27,28,33,34,35,48,49,50,51,58,59,60,67,68,69,70,74,83,84,91,92,115,116,123,124,131,132,147,148,157] (by decide) (by decide) (by decide))
def r3 : Rule 158 8 := cutRule 8 p3 w3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p4 : Weak 158 6 := relaxed (pick [2,3,25,26,33,34] (by decide) (by decide) (by decide))
def r4 : Rule 158 7 := cutRule 7 p4 w1
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w4 : Wide 6 2 s1 := viaSearch (by decide +kernel)
def r5 : Rule 158 7 := cutRule 7 p4 w4
def f16 : ℕ := 0x35a3ff
def f17 : ℕ := 0x4a0fe0
def f18 : ℕ := 0x805c1f
def s4 : List ℕ := [f16,f17,f18]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w5 : Wide 12 3 s4 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p5 : Weak 158 12 := relaxed (pick [10,11,14,15,16,48,49,52,53,54,62,63] (by decide) (by decide) (by decide))
def r6 : Rule 158 7 := cutRule 7 p5 w5
def f19 : ℕ := 0xe1c
def f20 : ℕ := 0xaa03e0
def f21 : ℕ := 0xaeee6c
def f22 : ℕ := 0xfb5f94
def s5 : List ℕ := [f19,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w6 : Wide 12 3 s5 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p6 : Weak 158 12 := signedPick 17 [17,18,26,30,42,55,56,64,65,70,111,115] (by decide) (by decide) (by decide)
def r7 : Rule 158 7 := cutRule 7 p6 w6
def r8 : Rule 158 7 := cutRule 7 p1 w4
def r9 : Rule 158 7 := cutRule 7 p1 w1
def f23 : ℕ := 0x4a06e
def f24 : ℕ := 0x61431c
def f25 : ℕ := 0x9a03e0
def f26 : ℕ := 0xfff36c
def s6 : List ℕ := [f23,f24,f25,f26]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w7 : Wide 12 3 s6 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p7 : Weak 158 12 := signedPick 3 [3,8,17,18,22,55,56,60,64,65,87,91] (by decide) (by decide) (by decide)
def r10 : Rule 158 7 := cutRule 7 p7 w7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w8 : Wide 6 2 s2 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p8 : Weak 158 6 := signedPick 43 [43,44,71,72,75,76] (by decide) (by decide) (by decide)
def r11 : Rule 158 7 := cutRule 7 p8 w8
def r12 : Rule 158 7 := cutRule 7 p2 w8
def f27 : ℕ := 0x50505050505050505050010a002009006c0029601fe0001fe000001fffe4043c00c07e01f003ff
def f28 : ℕ := 0x88888888888888888888840092885266024a94a000001fe000001fe01fe218024f21c998193e73
def f29 : ℕ := 0x98989898989898989898c408da8c5e7e436afca0001fffe0001fffe01fe39823ff39f9f99ffff3
def f30 : ℕ := 0x16161616161616161616401a00033a0003c95001fe0000000001fffe0001807c000ff8001fffc00
def f31 : ℕ := 0x22a2a2a2a2a2a2a2a2a2810c4e3010055138cc600000000001fe0001fe00063138c0601fe6e339c
def f32 : ℕ := 0x585858585858585858587ee00001ef6aa800000000000001fffe00000001ff80000fffffe000000
def f33 : ℕ := 0x6060606060606060606033a55254000000000001fffffffe000000000001fffffff000000000000
def s7 : List ℕ := [f27,f28,f29,f30,f31,f32,f33]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b1 : Ban 158 8 s7 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1027721473,r4),(1589736626,r5),(1399936101,r5),(656272975,r6),(380478907,r5),(1575375024,r4),(183562681,r4),(439796727,r4),(1880925202,r5),(1569905567,r4),(1740016178,r4),(98791254,r5),(2059406736,r7),(1121086587,r8),(1456174711,r9),(344568812,r4),(906583965,r5),(1653349209,r10),(1057513246,r8),(965720282,r9),(1271515339,r4),(1833530492,r5),(825513761,r10),(608131378,r8),(648981899,r11),(1059042910,r12),(943999437,r5),(617676086,r4),(1589019517,r4),(1157162695,r5),(1748816268,r4),(1938260486,r4),(1351140989,r5),(1657463023,r5),(815738508,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r13 : Rule 158 8 := cutRule 8 p4 w1
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p9 : Weak 158 6 := signedPick 7 [7,8,29,30,36,37] (by decide) (by decide) (by decide)
def r14 : Rule 158 7 := cutRule 7 p9 w8
def f34 : ℕ := 0x10101010101010101010400848040c1841206800001fe000001fe00000018021b018306186c180
def s8 : List ℕ := [f34,f27,f28,f30,f31,f32,f33]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b2 : Ban 158 8 s8 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1140728296,r4),(1575375024,r4),(1898508526,r14),(1531746871,r14),(42213455,r14),(220694989,r7),(1962121109,r10),(1134285661,r10),(245108934,r14),(1252771337,r14),(1465934595,r14),(1966234923,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r15 : Rule 158 8 := cutRule 8 p9 w2
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p10 : Weak 158 6 := relaxed (pick [10,11,48,49,62,63] (by decide) (by decide) (by decide))
def r16 : Rule 158 8 := cutRule 8 p10 w1
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p11 : Weak 158 6 := signedPick 12 [12,13,50,51,64,65] (by decide) (by decide) (by decide)
def r17 : Rule 158 8 := cutRule 8 p11 w2
def f35 : ℕ := 0x252273
def f36 : ℕ := 0x31839c
def s9 : List ℕ := [f35,f36,f17,f18]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w9 : Wide 12 4 s9 := viaSearch (by decide +kernel)
def r18 : Rule 158 8 := cutRule 8 p5 w9
def f37 : ℕ := 0x484aa06781333f
def f38 : ℕ := 0x494001fe07ff000
def f39 : ℕ := 0x2aaa26263019809cdcc
def f40 : ℕ := 0x555580194181e700ff0
def f41 : ℕ := 0x7fff303816601ce0e0f
def s10 : List ℕ := [f37,f38,f39,f40,f41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w10 : Wide 38 5 s10 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p12 : Weak 158 38 := relaxed (pick [0,1,5,6,10,11,14,15,16,20,23,24,48,49,52,53,54,58,59,61,62,63,66,78,80,94,96,102,104,126,128,134,136,142,144,150,152,157] (by decide) (by decide) (by decide))
def r19 : Rule 158 8 := cutRule 8 p12 w10
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p13 : Weak 158 6 := signedPick 21 [21,22,41,42,46,47] (by decide) (by decide) (by decide)
def r20 : Rule 158 8 := cutRule 8 p13 w2
def f42 : ℕ := 0x54f
def f43 : ℕ := 0xa3c
def f44 : ℕ := 0x10f3
def s11 : List ℕ := [f42,f43,f44]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w11 : Wide 7 3 s11 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p14 : Weak 158 7 := relaxed (pick [0,1,48,49,58,59,157] (by decide) (by decide) (by decide))
def r21 : Rule 158 8 := cutRule 8 p14 w11
def f45 : ℕ := 0x9240da
def f46 : ℕ := 0x141831c
def f47 : ℕ := 0x22c03e0
def f48 : ℕ := 0x3ffe3d8
def s12 : List ℕ := [f45,f46,f47,f48]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w12 : Wide 13 4 s12 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p15 : Weak 158 13 := signedPick 10 [10,12,20,21,22,39,41,42,46,47,95,96,98] (by decide) (by decide) (by decide)
def r22 : Rule 158 8 := cutRule 8 p15 w12
def r23 : Rule 158 8 := cutRule 8 p8 w2
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p16 : Weak 158 6 := signedPick 39 [39,40,67,68,75,76] (by decide) (by decide) (by decide)
def r24 : Rule 158 8 := cutRule 8 p16 w2
def f49 : ℕ := 0x2982a5038e1cc3f3
def f50 : ℕ := 0x49248153301c7060fd9c
def f51 : ℕ := 0x924a040c0be07f870e1f
def f52 : ℕ := 0x124917aa000fc01fff000
def f53 : ℕ := 0x1ffffd01d400381f80fe0
def s13 : List ℕ := [f49,f50,f51,f52,f53]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w13 : Wide 41 5 s13 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p17 : Weak 158 41 := relaxed (pick [0,1,2,3,4,10,11,12,13,20,21,22,25,26,27,28,33,34,35,39,40,41,42,46,47,79,80,82,87,88,90,95,96,98,111,112,114,119,120,122,157] (by decide) (by decide) (by decide))
def r25 : Rule 158 8 := cutRule 8 p17 w13
def f54 : ℕ := 0x7fa3e0
def f55 : ℕ := 0xdadd8c
def s14 : List ℕ := [f36,f17,f54,f55]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w14 : Wide 12 4 s14 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p18 : Weak 158 12 := signedPick 12 [12,13,17,18,19,50,51,55,56,57,64,65] (by decide) (by decide) (by decide)
def r26 : Rule 158 8 := cutRule 8 p18 w14
def f56 : ℕ := 0x4104104120288cc8ac03f000fc0303cccccfc
def f57 : ℕ := 0x14514514500020a0d05000fc003f00030f0f0f
def f58 : ℕ := 0x38e38e38e8283700750fc0000fc0c3c3f00ff0
def f59 : ℕ := 0x4924924920b3020a2ca00003f03f0f3030f3cf
def f60 : ℕ := 0xa28a28a28f401d55000000fff000fc03fff000
def f61 : ℕ := 0xc30c30c305d54000000fff000000fffc000000
def s15 : List ℕ := [f56,f57,f58,f59,f60,f61]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w15 : Wide 76 6 s15 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p19 : Weak 158 76 := relaxed (pick [2,3,7,8,14,15,17,18,21,22,23,24,25,26,29,30,33,34,36,37,41,42,43,44,46,47,52,53,55,56,62,63,64,65,69,70,71,72,75,76,86,87,88,90,91,92,102,103,104,106,107,108,110,111,112,114,115,116,118,119,120,122,123,124,134,135,136,138,139,140,150,151,152,154,155,156] (by decide) (by decide) (by decide))
def r27 : Rule 158 8 := cutRule 8 p19 w15
def f62 : ℕ := 0x1111100814803c008235a
def f63 : ℕ := 0x22222040233c00021c09c
def f64 : ℕ := 0x88888e80000003c3e00e0
def f65 : ℕ := 0xbbbbbedb7fffffc396df8
def f66 : ℕ := 0xcccccfb5c03c3c02ec300
def f67 : ℕ := 0xcccccfb5c03ffc03fff00
def s16 : List ℕ := [f62,f63,f64,f65,f66,f67]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w16 : Wide 42 6 s16 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p20 : Weak 158 42 := signedPick 2 [2,7,21,23,24,34,37,47,52,55,58,59,60,61,62,64,66,69,70,71,74,75,86,88,91,92,118,120,123,124,134,136,139,140,142,144,147,148,150,152,155,156] (by decide) (by decide) (by decide)
def r28 : Rule 158 8 := cutRule 8 p20 w16
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p21 : Weak 158 12 := signedPick 39 [39,40,43,44,45,67,68,71,72,73,75,76] (by decide) (by decide) (by decide)
def r29 : Rule 158 8 := cutRule 8 p21 w14
def f68 : ℕ := 0x98989898989898989898c008d80c1c784360f800001fe000001fe00000038023f03871e18fc3e0
def s17 : List ℕ := [f28,f31,f68,f27,f30,f32,f33]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b0 : Ban 158 9 s17 := viaRules (ws := [s7,s8]) (consBan b1 (consBan b2 (nilBan _ _)))
  (dictionary [(928314641,r0),(508592363,r1),(2008911971,r2),(1544470111,r0),(1588350095,r3),(319020776,r13),(627792676,r15),(444044922,r0),(1208750441,r3),(506433061,r16),(1571747210,r3),(1184969858,r17),(80139125,r0),(645145441,r1),(1856174274,r18),(2037822247,r0),(549809235,r19),(1758972733,r16),(88550662,r18),(1727744102,r17),(191546809,r3),(1438092907,r16),(1517902417,r18),(239048694,r3),(371327701,r3),(622323219,r13),(1574929313,r20),(792433830,r0),(1307146329,r3),(920053677,r21),(1590755517,r3),(233839152,r19),(1231328395,r3),(1576622114,r13),(386110173,r20),(700925835,r15),(1181597157,r3),(821448827,r22),(2333180,r3),(1077682873,r18),(845090992,r0),(18137934,r1),(933863931,r23),(323932991,r0),(1463399907,r19),(1246017524,r16),(1286868045,r24),(1696929056,r17),(1010151724,r3),(1472606583,r16),(941446818,r24),(2139009645,r3),(143751708,r19),(1695399392,r16),(163241692,r24),(926347217,r18),(987117502,r3),(1840796525,r21),(1865157004,r19),(1409747808,r3),(1795048841,r0),(801233920,r13),(1105445398,r25),(990678138,r0),(19495571,r19),(545037917,r26),(341872047,r26),(1859285841,r19),(2048208244,r3),(1169380350,r13),(745050123,r25),(481335814,r15),(1581885583,r27),(1255562232,r28),(1239720901,r25),(79422016,r18),(147865522,r3),(1453624654,r13),(1898867774,r25),(1804160042,r20),(1686629790,r19),(56506734,r29),(1503732953,r29),(451230390,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
theorem cert6 : Ban 158 9 bank := b0
end PEqualNP.Outside.L_meta_14342.B0

namespace PEqualNP.Outside.L_meta_14342.B1
def bank : List ℕ := [0x210842108420024a055024a94bfffffffffffff0001f003e0f80093c154193e73,0x2b5ad6b5ad6b3138c466138cc600000000000000000000001f04c4e311986e339c,0x6318c6318c6023601784360f800000000000000003e007c000008fc05e18fc3e0,0x14a5294a5294428009806c00297fffffffffffff07c000001ff90f002601f003ff,0x18c6318c631868000e003c950000000000000000f800007fe001f0003801fffc00,0xf80000600003ffe000000,0x2108421084219549500000000000000000000000fffff0000007ffffc000000000]
def f0 : ℕ := 0x90957ffffffffffffe06781333f
def f1 : ℕ := 0x9280000000000000001fe07ff000
def f2 : ℕ := 0x55544c4c60000000000000019809cdcc
def f3 : ℕ := 0xaaab003280000000000000181e700ff0
def f4 : ℕ := 0xfffe60702fffffffffffffe601ce0e0f
def s0 : List ℕ := [f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w0 : Wide 91 5 s0 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p0 : Weak 158 91 := relaxed (pick [0,1,5,6,10,11,14,15,16,20,23,24,38,39,42,43,44,48,49,51,52,53,56,60,62,70,72,75,77,85,87,90,92,95,97,100,102,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r0 : Rule 158 8 := cutRule 8 p0 w0
def f5 : ℕ := 0x28f
def f6 : ℕ := 0x53c
def f7 : ℕ := 0x873
def s1 : List ℕ := [f5,f6,f7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w1 : Wide 6 2 s1 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p1 : Weak 158 6 := relaxed (pick [14,15,42,43,52,53] (by decide) (by decide) (by decide))
def r1 : Rule 158 7 := cutRule 7 p1 w1
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w2 : Wide 6 3 s1 := viaSearch (by decide +kernel)
def r2 : Rule 158 7 := cutRule 7 p1 w2
def r3 : Rule 158 6 := cutRule 6 p1 w1
def r4 : Rule 158 6 := cutRule 6 p1 w2
def f8 : ℕ := 0x12504a3f87f
def f9 : ℕ := 0x1b7a19c0f8c
def f10 : ℕ := 0x2485a1f8ff0
def f11 : ℕ := 0x2dac940764f
def s2 : List ℕ := [f8,f9,f10,f11]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w3 : Wide 21 3 s2 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p2 : Weak 158 21 := relaxed (pick [2,3,21,22,48,49,50,52,53,54,55,56,66,67,68,96,97,98,101,102,103] (by decide) (by decide) (by decide))
def r5 : Rule 158 6 := cutRule 6 p2 w3
def f12 : ℕ := 0x92486d5b50fff0fffff
def f13 : ℕ := 0x124950004af03ff003ff
def f14 : ℕ := 0x2492292a007fc0fffc00
def s3 : List ℕ := [f12,f13,f14]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w4 : Wide 39 3 s3 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p3 : Weak 158 39 := relaxed (pick [10,11,12,13,14,15,16,17,18,19,38,39,40,41,42,43,44,45,46,47,52,53,54,55,69,71,73,74,76,78,84,86,88,89,91,93,99,101,103] (by decide) (by decide) (by decide))
def r6 : Rule 158 6 := cutRule 6 p3 w4
def f15 : ℕ := 0x249195407fc7ff80
def f16 : ℕ := 0x2db5fff68fc0ff80
def f17 : ℕ := 0x36db954970070000
def s4 : List ℕ := [f15,f16,f17]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w5 : Wide 31 3 s4 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p4 : Weak 158 31 := signedPick 11 [11,12,13,16,17,18,19,38,39,40,41,42,44,45,46,47,52,54,55,69,71,73,84,86,88,89,91,93,99,101,103] (by decide) (by decide) (by decide)
def r7 : Rule 158 6 := cutRule 6 p4 w5
def f18 : ℕ := 0x89c7f
def f19 : ℕ := 0x406783
def f20 : ℕ := 0xfb73bfc
def s5 : List ℕ := [f18,f19,f20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w6 : Wide 14 3 s5 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p5 : Weak 158 14 := relaxed (pick [14,15,38,40,42,43,45,52,53,54,78,88,93,103] (by decide) (by decide) (by decide))
def r8 : Rule 158 6 := cutRule 6 p5 w6
def f21 : ℕ := 0xf80000600003ffe000000
def f22 : ℕ := 0x6318c6318c60236a17d436afcbfffffffffffff003ff07fe0f808ffc5f59ffff3
def f23 : ℕ := 0x14a5294a5294428009806c00297fffffffffffff07c000001ff90f002601f003ff
def f24 : ℕ := 0x18c6318c631868000e003c950000000000000000f800007fe001f0003801fffc00
def f25 : ℕ := 0x2108421084219549500000000000000000000000fffff0000007ffffc000000000
def f26 : ℕ := 0x2b5ad6b5ad6b313ce47713ced6bfffffffffffff0001f003fffcc4f3d1dc7f3fff
def s6 : List ℕ := [f21,f22,f23,f24,f25,f26]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b2 : Ban 158 7 s6 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(177417700,r3),(1078915450,r4),(1704132680,r4),(1666991462,r3),(1435339773,r3),(1640812446,r4),(818480076,r3),(1384308080,r4),(561975710,r3),(197270904,r3),(966936514,r3),(1437236433,r3),(1063166098,r4),(135207992,r4),(1042685523,r3),(1752241611,r5),(277658917,r3),(1116853757,r3),(1601213986,r4),(1472631768,r4),(695563605,r4),(566981387,r4),(437047078,r3),(252381923,r3),(1380876041,r4),(1067007062,r3),(1538507082,r4),(389257451,r4),(878605082,r3),(392844786,r6),(929148588,r3),(1820597575,r6),(1592952506,r7),(1758263027,r8)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f27 : ℕ := 0x1078
def f28 : ℕ := 0x2aa019f80
def f29 : ℕ := 0x2af7b93b8
def f30 : ℕ := 0x3faa41c50
def s7 : List ℕ := [f27,f28,f29,f30]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w7 : Wide 17 4 s7 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p6 : Weak 158 17 := signedPick 11 [11,12,13,26,27,28,36,39,40,41,54,55,58,71,73,86,88] (by decide) (by decide) (by decide)
def r9 : Rule 158 7 := cutRule 7 p6 w7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w8 : Wide 17 3 s7 := viaSearch (by decide +kernel)
def r10 : Rule 158 7 := cutRule 7 p6 w8
def f31 : ℕ := 0x2879f0
def f32 : ℕ := 0x1505060f
def f33 : ℕ := 0x2ac2e7cf
def f34 : ℕ := 0x3f96193c
def s8 : List ℕ := [f31,f32,f33,f34]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w9 : Wide 15 3 s8 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p7 : Weak 158 15 := relaxed (pick [14,15,23,24,48,49,52,53,56,75,77,95,97,100,102] (by decide) (by decide) (by decide))
def r11 : Rule 158 7 := cutRule 7 p7 w9
def f35 : ℕ := 0x530
def s9 : List ℕ := [f5,f35,f6,f7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w10 : Wide 6 3 s9 := viaSearch (by decide +kernel)
def r12 : Rule 158 7 := cutRule 7 p1 w10
def f36 : ℕ := 0x15951f3f
def f37 : ℕ := 0x2a02860f
def f38 : ℕ := 0x3fc661cc
def s10 : List ℕ := [f31,f36,f37,f38]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w11 : Wide 15 3 s10 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p8 : Weak 158 15 := relaxed (pick [14,15,23,24,42,43,48,49,51,75,77,90,92,95,97] (by decide) (by decide) (by decide))
def r13 : Rule 158 7 := cutRule 7 p8 w11
def f39 : ℕ := 0x301c
def f40 : ℕ := 0x499b5fd9b4
def f41 : ℕ := 0x932e01f060
def f42 : ℕ := 0x932e0fffe0
def f43 : ℕ := 0xb77eee378c
def s11 : List ℕ := [f39,f40,f41,f42,f43]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w12 : Wide 20 4 s11 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p9 : Weak 158 20 := signedPick 21 [21,22,35,36,37,48,50,52,53,54,55,56,57,58,96,97,98,101,102,103] (by decide) (by decide) (by decide)
def r14 : Rule 158 7 := cutRule 7 p9 w12
def f44 : ℕ := 0x50c
def s12 : List ℕ := [f5,f44,f6,f7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w13 : Wide 6 3 s12 := viaSearch (by decide +kernel)
def r15 : Rule 158 7 := cutRule 7 p1 w13
def f45 : ℕ := 0x78c
def f46 : ℕ := 0xd70
def s13 : List ℕ := [f6,f45,f46]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w14 : Wide 6 3 s13 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p10 : Weak 158 6 := signedPick 17 [17,18,45,46,54,55] (by decide) (by decide) (by decide)
def r16 : Rule 158 7 := cutRule 7 p10 w14
def f47 : ℕ := 0x2a8f0ff
def f48 : ℕ := 0x568173f0f
def f49 : ℕ := 0xa9543cff0
def s14 : List ℕ := [f47,f48,f49]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w15 : Wide 18 3 s14 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p11 : Weak 158 18 := relaxed (pick [10,11,12,13,38,39,40,41,52,53,54,55,71,73,86,88,101,103] (by decide) (by decide) (by decide))
def r17 : Rule 158 7 := cutRule 7 p11 w15
def f50 : ℕ := 0x92468340e00f878
def f51 : ℕ := 0x36dbb5597e076830
def s15 : List ℕ := [f50,f15,f16,f51]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w16 : Wide 31 4 s15 := viaSearch (by decide +kernel)
def r18 : Rule 158 7 := cutRule 7 p4 w16
def f52 : ℕ := 0x4444411515801fe008fcfc
def f53 : ℕ := 0x888890105940001e0003cf
def f54 : ℕ := 0x155556141a0a1e01f0f0f0f
def f55 : ℕ := 0x19999b400ea1e01e1f00ff0
def f56 : ℕ := 0x222220aaa001ffe01fff000
def s16 : List ℕ := [f52,f53,f54,f55,f56]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w17 : Wide 45 5 s16 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p12 : Weak 158 45 := relaxed (pick [2,3,7,8,14,15,17,18,21,22,23,24,42,43,45,46,48,49,50,51,52,53,54,55,56,65,66,67,68,75,76,77,78,90,91,92,93,95,96,97,98,100,101,102,103] (by decide) (by decide) (by decide))
def r19 : Rule 158 7 := cutRule 7 p12 w17
def f57 : ℕ := 0x210842108420024a055024a94bfffffffffffff0001f003e0f80093c154193e73
def f58 : ℕ := 0x6318c6318c6023601784360f800000000000000003e007c000008fc05e18fc3e0
def s17 : List ℕ := [f21,f57,f58,f23,f24,f25,f26]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b1 : Ban 158 8 s17 := viaRules (ws := [s6]) (consBan b2 (nilBan _ _))
  (dictionary [(660730957,r1),(1955453985,r2),(890189494,r1),(1718417905,r2),(653153414,r1),(919636022,r1),(1413681924,r1),(1262602681,r2),(1746243371,r2),(250931015,r2),(734571705,r2),(132102150,r1),(1917163987,r9),(368258806,r2),(2078659096,r2),(1539692911,r2),(1818064766,r1),(2023537439,r2),(1201205069,r1),(1767033073,r2),(944700703,r1),(579995897,r1),(948706357,r1),(2096812561,r2),(1031548070,r1),(1012106290,r1),(1644798065,r2),(579533574,r1),(1765928957,r2),(77150758,r1),(961637853,r2),(1819961426,r1),(1445891091,r2),(643213353,r2),(517932985,r2),(1862738894,r2),(1425410516,r1),(1450937202,r1),(838876902,r1),(94273842,r10),(1189469018,r2),(265384866,r2),(660383910,r1),(1499578750,r1),(1983938979,r2),(1855356761,r2),(1078288598,r2),(949706380,r2),(819772071,r1),(1774792545,r1),(1247382316,r2),(19263227,r2),(1533147605,r1),(1570014721,r11),(1896335098,r12),(635106916,r1),(1057087202,r2),(1763601034,r2),(1371083426,r1),(2031654079,r13),(1579168613,r14),(1243377074,r15),(1449732055,r1),(1921232075,r2),(310052230,r1),(771982444,r2),(1308286246,r1),(1261330075,r1),(1561293763,r2),(2107209117,r16),(1808390499,r2),(775569779,r17),(1311873581,r1),(1153954171,r1),(55838921,r17),(592142723,r1),(1217746538,r2),(1975677499,r18),(364497654,r2),(2140988020,r19),(529808175,r1),(592156510,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r20 : Rule 158 8 := cutRule 8 p1 w2
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w18 : Wide 6 2 s13 := viaSearch (by decide +kernel)
def r21 : Rule 158 7 := cutRule 7 p10 w18
def f59 : ℕ := 0x66c3b7
def f60 : ℕ := 0x1082c47
def f61 : ℕ := 0x2901f80
def s18 : List ℕ := [f27,f59,f60,f61]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w19 : Wide 13 3 s18 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p13 : Weak 158 13 := relaxed (pick [10,11,13,25,26,28,35,38,39,41,52,53,57] (by decide) (by decide) (by decide))
def r22 : Rule 158 7 := cutRule 7 p13 w19
def f62 : ℕ := 0x181c
def f63 : ℕ := 0x2b6c1ffe0
def f64 : ℕ := 0x2b7dc78ec
def f65 : ℕ := 0x3feeb9f14
def s19 : List ℕ := [f62,f63,f64,f65]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w20 : Wide 17 4 s19 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p14 : Weak 158 17 := signedPick 17 [17,18,27,31,36,42,45,46,52,54,55,57,58,91,93,101,103] (by decide) (by decide) (by decide)
def r23 : Rule 158 7 := cutRule 7 p14 w20
def f66 : ℕ := 0x111111100a50cdb7ffffffffffffe001e1fe014f39ff
def f67 : ℕ := 0x333333308b04e1c0000000000000001e1e0011f0de38
def f68 : ℕ := 0x4444444a000312000000000000001e001fe1e000ffc0
def f69 : ℕ := 0x66666668a007004fffffffffffffe1e0001f1e00e03f
def f70 : ℕ := 0x8888888554a800000000000000001fffe001ffff0000
def s20 : List ℕ := [f66,f67,f68,f69,f70]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w21 : Wide 115 5 s20 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p15 : Weak 158 115 := relaxed (pick [0,1,4,5,6,9,10,11,13,14,15,16,19,20,23,24,38,39,40,41,42,43,44,45,47,48,49,50,51,52,53,54,56,59,60,62,63,69,70,72,73,74,75,77,78,84,85,87,88,89,90,92,93,94,95,97,98,99,100,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r24 : Rule 158 7 := cutRule 7 p15 w21
def f71 : ℕ := 0x294a5294a5293118442211844200000000000000000000001f04c460108866018c
def s21 : List ℕ := [f21,f57,f58,f23,f24,f25,f71]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b3 : Ban 158 8 s21 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(951691784,r21),(98931165,r2),(1181150321,r1),(2009378732,r16),(944114241,r21),(1210596849,r21),(1704642751,r21),(1553563508,r16),(541891842,r16),(423062977,r21),(659219633,r16),(222136276,r16),(2109025593,r21),(167014619,r2),(1492165896,r1),(2057993900,r16),(1235661530,r21),(870956724,r21),(1239667184,r21),(1322508897,r1),(1303067117,r21),(2110922253,r21),(1736851918,r16),(934174180,r16),(808893812,r16),(1716371343,r21),(385234669,r22),(951344737,r21),(1790539577,r21),(127416159,r16),(2146317588,r16),(1369249425,r16),(1110732898,r21),(1538343143,r16),(1860975548,r22),(926067743,r21),(799012990,r21),(1995624697,r2),(675405679,r1),(1511753352,r16),(384931031,r21),(1561293763,r2),(1816248290,r2),(583113466,r17),(1410378095,r21),(1856064987,r21),(1128582946,r17),(1665988901,r23),(610858078,r24)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r25 : Rule 158 8 := cutRule 8 p10 w14
def f72 : ℕ := 0x31839c
def f73 : ℕ := 0x4a0fe0
def f74 : ℕ := 0x7fa3e0
def f75 : ℕ := 0xdadd8c
def s22 : List ℕ := [f72,f73,f74,f75]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w22 : Wide 12 4 s22 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p16 : Weak 158 12 := signedPick 12 [12,13,17,18,19,40,41,45,46,47,54,55] (by decide) (by decide) (by decide)
def r26 : Rule 158 8 := cutRule 8 p16 w22
def f76 : ℕ := 0x2aaaa98985940001ec4c3cf
def s23 : List ℕ := [f52,f54,f55,f56,f76]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w23 : Wide 45 5 s23 := viaSearch (by decide +kernel)
def r27 : Rule 158 8 := cutRule 8 p12 w23
def f77 : ℕ := 0x21c
def f78 : ℕ := 0x1286b
def f79 : ℕ := 0x44593
def f80 : ℕ := 0xa83e0
def s24 : List ℕ := [f77,f78,f79,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w24 : Wide 10 3 s24 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p17 : Weak 158 10 := relaxed (pick [14,15,25,29,35,42,43,52,53,57] (by decide) (by decide) (by decide))
def r28 : Rule 158 7 := cutRule 7 p17 w24
def r29 : Rule 158 7 := cutRule 7 p12 w23
def f81 : ℕ := 0x4a06e
def f82 : ℕ := 0x61431c
def f83 : ℕ := 0x9a03e0
def f84 : ℕ := 0xfff36c
def s25 : List ℕ := [f81,f82,f83,f84]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w25 : Wide 12 3 s25 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p18 : Weak 158 12 := signedPick 3 [3,8,17,18,22,45,46,50,54,55,66,68] (by decide) (by decide) (by decide)
def r30 : Rule 158 7 := cutRule 7 p18 w25
def r31 : Rule 158 7 := cutRule 7 p2 w3
def f85 : ℕ := 0xcdbfffffffffffff383ff
def f86 : ℕ := 0x52000000000000000e7f80
def f87 : ℕ := 0x3f2107fffffffffffff4cc47
def f88 : ℕ := 0x3f8120000000000000097078
def s26 : List ℕ := [f85,f86,f87,f88]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w26 : Wide 74 4 s26 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p19 : Weak 158 74 := relaxed (pick [0,1,6,10,11,16,20,38,39,44,48,49,52,53,56,62,72,87,97,102,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r32 : Rule 158 7 := cutRule 7 p19 w26
def f89 : ℕ := 0x10818c
def f90 : ℕ := 0x252273
def f91 : ℕ := 0x805c1f
def s27 : List ℕ := [f89,f90,f73,f91]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w27 : Wide 12 4 s27 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p20 : Weak 158 12 := relaxed (pick [10,11,14,15,16,38,39,42,43,44,52,53] (by decide) (by decide) (by decide))
def r33 : Rule 158 7 := cutRule 7 p20 w27
def f92 : ℕ := 0x35a3ff
def s28 : List ℕ := [f92,f73,f91]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w28 : Wide 12 3 s28 := viaSearch (by decide +kernel)
def r34 : Rule 158 7 := cutRule 7 p20 w28
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w29 : Wide 10 4 s24 := viaSearch (by decide +kernel)
def r35 : Rule 158 7 := cutRule 7 p17 w29
def f93 : ℕ := 0x562b0c8fc
def f94 : ℕ := 0xa932834cf
def s29 : List ℕ := [f93,f48,f94,f49]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w30 : Wide 18 3 s29 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p21 : Weak 158 18 := relaxed (pick [2,3,7,8,42,43,45,46,48,49,50,51,65,68,90,93,95,98] (by decide) (by decide) (by decide))
def r36 : Rule 158 7 := cutRule 7 p21 w30
def f95 : ℕ := 0x6318c6318c11b5436afcbfffffffffffff003ffffc1f047ff9ffff3
def f96 : ℕ := 0x14a5294a52a14006c00297fffffffffffff07c00003ff87801f003ff
def f97 : ℕ := 0x18c6318c63340003c950000000000000000f8000ffc00f8001fffc00
def f98 : ℕ := 0x1ad6b5ad6b741253edf94bffffffffffffff801fffc1ff849ffffe73
def f99 : ℕ := 0x21084210840aa4a80000000000000000000fffff00000ffffe000000
def f100 : ℕ := 0x2b5ad6b5ad589c6138cc60000000000000000000003e0627186e339c
def s30 : List ℕ := [f95,f96,f97,f98,f99,f100]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w31 : Wide 138 6 s30 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p22 : Weak 158 138 := relaxed (pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r37 : Rule 158 7 := cutRule 7 p22 w31
def f101 : ℕ := 0x111111045428c00fff0047e7fc
def f102 : ℕ := 0x5555558506c050f000f8787c0f
def f103 : ℕ := 0x666666d003d70f00ff0f807ff0
def f104 : ℕ := 0x8888882aa8000fff000fff8000
def f105 : ℕ := 0xaaaaaa626132a00000f6261b2f
def s31 : List ℕ := [f101,f102,f103,f104,f105]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w32 : Wide 52 5 s31 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p23 : Weak 158 52 := relaxed (pick [2,3,7,8,10,12,14,15,17,18,20,21,22,23,24,42,43,45,46,48,49,50,51,52,53,54,55,56,65,66,67,68,70,71,72,73,75,76,77,78,90,91,92,93,95,96,97,98,100,101,102,103] (by decide) (by decide) (by decide))
def r38 : Rule 158 7 := cutRule 7 p23 w32
def f106 : ℕ := 0x1ddddf515ff9e1fe1f8fffc
def s32 : List ℕ := [f52,f54,f55,f106,f56,f76]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w33 : Wide 45 5 s32 := viaSearch (by decide +kernel)
def r39 : Rule 158 7 := cutRule 7 p12 w33
def f107 : ℕ := 0x2318c6318c4ab6f824a94bffffffffffffffffff07c1fffffe193e73
def s33 : List ℕ := [f95,f96,f97,f99,f107,f100]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w34 : Wide 138 6 s33 := viaSearch (by decide +kernel)
def r40 : Rule 158 7 := cutRule 7 p22 w34
def f108 : ℕ := 0x444444114456007ff8023fcfc
def f109 : ℕ := 0x1555556140682878007c3c0f0f
def f110 : ℕ := 0x199999b4003a87800787c00ff0
def f111 : ℕ := 0x2222220aab8007fff807fff000
def f112 : ℕ := 0x2aaaaa9899165000007b1323cf
def s34 : List ℕ := [f108,f109,f110,f111,f112]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w35 : Wide 51 5 s34 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p24 : Weak 158 51 := relaxed (pick [2,3,7,8,14,15,17,18,21,22,23,24,38,40,42,43,45,46,48,49,50,51,52,53,54,55,56,65,66,67,68,75,76,77,78,85,86,87,88,90,91,92,93,95,96,97,98,100,101,102,103] (by decide) (by decide) (by decide))
def r41 : Rule 158 7 := cutRule 7 p24 w35
def f113 : ℕ := 0x569d7da74
def f114 : ℕ := 0xada833600
def f115 : ℕ := 0xada83ffe0
def f116 : ℕ := 0xadfb8f1ec
def s35 : List ℕ := [f39,f113,f114,f115,f116]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w36 : Wide 18 4 s35 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p25 : Weak 158 18 := signedPick 7 [7,8,29,31,34,42,43,45,46,48,50,51,57,58,90,93,95,98] (by decide) (by decide) (by decide)
def r42 : Rule 158 7 := cutRule 7 p25 w36
def f117 : ℕ := 0x222220aaa001fe001f70000
def s36 : List ℕ := [f52,f54,f55,f117,f56,f76]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w37 : Wide 45 5 s36 := viaSearch (by decide +kernel)
def r43 : Rule 158 7 := cutRule 7 p12 w37
def f118 : ℕ := 0x81c
def f119 : ℕ := 0x29833a20
def f120 : ℕ := 0x2983ffe0
def f121 : ℕ := 0x56fb8f9ec
def f122 : ℕ := 0xabbd7ced4
def s37 : List ℕ := [f118,f119,f120,f121,f122]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w38 : Wide 18 4 s37 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p26 : Weak 158 18 := signedPick 23 [23,24,33,34,37,42,48,49,51,52,56,57,90,92,95,97,100,102] (by decide) (by decide) (by decide)
def r44 : Rule 158 7 := cutRule 7 p26 w38
def f123 : ℕ := 0x129aff34
def f124 : ℕ := 0x242e0e0c
def f125 : ℕ := 0x242e7ffc
def f126 : ℕ := 0x2d7f70f0
def s38 : List ℕ := [f123,f124,f125,f126]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w39 : Wide 15 3 s38 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p27 : Weak 158 15 := signedPick 21 [21,22,48,50,52,53,54,55,56,96,97,98,101,102,103] (by decide) (by decide) (by decide)
def r45 : Rule 158 7 := cutRule 7 p27 w39
def f127 : ℕ := 0x222220aaa0001fe000ff000
def s39 : List ℕ := [f52,f54,f55,f127,f56,f76]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w40 : Wide 45 5 s39 := viaSearch (by decide +kernel)
def r46 : Rule 158 7 := cutRule 7 p12 w40
def f128 : ℕ := 0xbba6c
def f129 : ℕ := 0xed794
def s40 : List ℕ := [f77,f80,f128,f129]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w41 : Wide 10 3 s40 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p28 : Weak 158 10 := signedPick 17 [17,18,27,31,36,45,46,54,55,58] (by decide) (by decide) (by decide)
def r47 : Rule 158 7 := cutRule 7 p28 w41
def f130 : ℕ := 0xca5c00
def s41 : List ℕ := [f73,f74,f130]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w42 : Wide 12 3 s41 := viaSearch (by decide +kernel)
def r48 : Rule 158 7 := cutRule 7 p16 w42
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p29 : Weak 158 18 := relaxed (pick [14,15,17,18,42,43,45,46,52,53,54,55,76,78,91,93,101,103] (by decide) (by decide) (by decide))
def r49 : Rule 158 7 := cutRule 7 p29 w15
def f131 : ℕ := 0x2b5ad6b5ad6b3138c466138cc600000000000000000000001f04c4e311986e339c
def s42 : List ℕ := [f21,f57,f22,f23,f24,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b4 : Ban 158 8 s42 := viaRules (ws := [s6]) (consBan b2 (nilBan _ _))
  (dictionary [(324809197,r28),(1619532225,r2),(554267734,r1),(1382496145,r29),(317231654,r28),(583714262,r30),(224220933,r30),(1125718683,r29),(161369889,r31),(1750935913,r29),(786587119,r31),(1713794695,r30),(1144158870,r32),(1043243173,r33),(1482143006,r28),(1687615679,r2),(865283309,r1),(1431111313,r29),(608778943,r28),(244074137,r30),(1678049088,r34),(612784597,r28),(695626310,r1),(1741449021,r34),(676184530,r28),(243611814,r28),(1384300357,r28),(772515477,r35),(1013739747,r28),(332225137,r31),(1484039666,r30),(1109969331,r29),(307291593,r36),(182011225,r29),(1526817134,r36),(1089488756,r30),(1115015442,r28),(1436202298,r37),(370937807,r36),(1568219633,r38),(502955142,r28),(1799044844,r36),(797423549,r39),(1200843055,r36),(1056176363,r31),(853547258,r35),(2076946753,r36),(324462150,r28),(1163656990,r30),(1648017219,r29),(1519435001,r29),(742366838,r29),(613784620,r29),(483850311,r30),(1438870785,r28),(1976725047,r40),(911460556,r29),(1830825114,r29),(115006689,r41),(1197225845,r28),(1018982917,r31),(1102296656,r42),(1998114698,r43),(1804370806,r31),(299185156,r28),(721165442,r44),(1427679274,r35),(1035161666,r28),(1695732319,r36),(1243246853,r45),(907455314,r46),(1906579762,r36),(1078146692,r28),(223654654,r2),(1872026180,r1),(1856422357,r16),(1357310236,r21),(1703602175,r47),(934411176,r2),(368258806,r2),(659219633,r16),(1089612725,r48),(2055180097,r49),(1556067976,r28),(1985507837,r1),(442987039,r21),(1827484593,r49),(1328372472,r28),(115567661,r47),(1504246729,r28),(23165843,r23),(1671537369,r47),(904575337,r19),(405463216,r28),(567538971,r47)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p30 : Weak 158 6 := relaxed (pick [10,11,38,39,52,53] (by decide) (by decide) (by decide))
def r50 : Rule 158 7 := cutRule 7 p30 w2
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p31 : Weak 158 12 := signedPick 3 [3,4,12,13,22,40,41,50,54,55,66,68] (by decide) (by decide) (by decide)
def r51 : Rule 158 7 := cutRule 7 p31 w25
def f132 : ℕ := 0xa152fffffffffffffc0fc700f3f3
def f133 : ℕ := 0x12492820605fffffffffffffc703f870e1f
def f134 : ℕ := 0x1b6dbd00ea00000000000000381c0f80fe0
def f135 : ℕ := 0x249242d500000000000000003fe00fff000
def f136 : ℕ := 0x249242df152ffffffffffffffffc7fff3f3
def f137 : ℕ := 0x2db6d64c99800000000000000003864cd9c
def s43 : List ℕ := [f132,f133,f134,f135,f136,f137]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w43 : Wide 96 5 s43 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p32 : Weak 158 96 := relaxed (pick [0,1,2,3,4,10,11,12,13,20,21,22,38,39,40,41,48,49,50,52,53,54,55,56,61,62,63,66,67,68,71,72,73,86,87,88,96,97,98,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r52 : Rule 158 7 := cutRule 7 p32 w43
def s44 : List ℕ := [f21,f57,f58,f22,f23,f24,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b5 : Ban 158 8 s44 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2103172915,r2),(1077760164,r30),(1410321611,r50),(1943664037,r30),(1790873295,r28),(1144158870,r32),(1672210417,r51),(1609359373,r31),(87092956,r31),(1014300532,r51),(23772722,r50),(1430007197,r50),(1888712645,r28),(625716093,r31),(1780214621,r31),(1593610021,r31),(1905835729,r36),(1099550681,r36),(2131657909,r31),(312882090,r52),(1234092961,r31),(1560413338,r43),(319488754,r31),(1917163987,r9),(1418051866,r2),(391337140,r17)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f138 : ℕ := 0x363f
def f139 : ℕ := 0x48f8
def f140 : ℕ := 0x81c7
def s45 : List ℕ := [f138,f139,f140]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w44 : Wide 8 3 s45 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p33 : Weak 158 8 := relaxed (pick [10,11,16,38,39,44,52,53] (by decide) (by decide) (by decide))
def r53 : Rule 158 7 := cutRule 7 p33 w44
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w45 : Wide 8 2 s45 := viaSearch (by decide +kernel)
def r54 : Rule 158 7 := cutRule 7 p33 w45
def f141 : ℕ := 0xdbfffffffffffff3f
def f142 : ℕ := 0x1200000000000000f8
def f143 : ℕ := 0x207fffffffffffffc7
def s46 : List ℕ := [f141,f142,f143]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w46 : Wide 62 3 s46 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p34 : Weak 158 62 := relaxed (pick [0,1,6,38,39,44,48,49,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r55 : Rule 158 7 := cutRule 7 p34 w46
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p35 : Weak 158 13 := relaxed (pick [10,11,16,25,26,30,35,38,39,44,52,53,57] (by decide) (by decide) (by decide))
def r56 : Rule 158 7 := cutRule 7 p35 w19
def f144 : ℕ := 0x12afffffffffffffcf33f
def f145 : ℕ := 0x15884000000000000030cc0
def f146 : ℕ := 0x2a65000000000000003cff0
def f147 : ℕ := 0x3fe05fffffffffffffc3e0f
def s47 : List ℕ := [f144,f145,f146,f147]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w47 : Wide 72 3 s47 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p36 : Weak 158 72 := relaxed (pick [0,1,5,6,10,11,14,15,16,20,23,24,60,62,70,72,75,77,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r57 : Rule 158 7 := cutRule 7 p36 w47
def f148 : ℕ := 0x4081c070c
def f149 : ℕ := 0x923360ffffe0
def f150 : ℕ := 0xb6bffa1f8fe0
def f151 : ℕ := 0xdb776dfc770c
def s48 : List ℕ := [f148,f149,f150,f151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w48 : Wide 24 4 s48 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p37 : Weak 158 24 := signedPick 12 [12,13,17,18,19,38,40,41,42,45,46,47,52,54,55,84,86,88,89,91,93,99,101,103] (by decide) (by decide) (by decide)
def r58 : Rule 158 7 := cutRule 7 p37 w48
def f152 : ℕ := 0x20850b0c
def f153 : ℕ := 0x452284f3
def f154 : ℕ := 0x20059f01f
def f155 : ℕ := 0xfd9a0e7fe0
def s49 : List ℕ := [f152,f153,f154,f155]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w49 : Wide 20 4 s49 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p38 : Weak 158 20 := relaxed (pick [10,11,14,15,16,38,39,40,42,43,44,45,52,53,54,73,78,88,93,103] (by decide) (by decide) (by decide))
def r59 : Rule 158 7 := cutRule 7 p38 w49
def f156 : ℕ := 0x421084210840212012841206800000000000000003e007c0000086c04a186c180
def s50 : List ℕ := [f21,f57,f156,f23,f24,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b6 : Ban 158 8 s50 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2035209487,r28),(1182448868,r2),(117184377,r1),(945412788,r33),(2027631944,r28),(146630905,r30),(640652392,r30),(2109994036,r53),(708561885,r54),(86360618,r33),(117772629,r30),(1144158870,r32),(1480326530,r29),(1045059649,r28),(1250532322,r2),(428199952,r1),(994027956,r33),(171695586,r28),(1954474427,r30),(175701240,r28),(239101173,r28),(1789925151,r28),(1046956309,r30),(672885974,r55),(2017691883,r36),(1892411515,r33),(652405399,r30),(1993803577,r56),(2034862440,r28),(726573633,r30),(1210933862,r33),(1082351644,r57),(305283481,r33),(46766954,r30),(1001787428,r28),(474377199,r29),(760142488,r28),(2009585446,r28),(641063335,r28),(1934054944,r2),(1419339000,r16),(1266518818,r47),(2078659096,r2),(222136276,r16),(1618096740,r49),(1118984619,r28),(1390401236,r49),(1733566133,r58),(467491980,r59)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f157 : ℕ := 0x257ffffffffffffe707f
def f158 : ℕ := 0x15000000000000001cfe0
def f159 : ℕ := 0xfc88fffffffffffffe9993
def f160 : ℕ := 0xfe0a000000000000012e1c
def s51 : List ℕ := [f157,f158,f159,f160]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w50 : Wide 71 4 s51 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p39 : Weak 158 71 := relaxed (pick [0,1,10,11,20,38,39,48,49,52,53,56,62,72,87,97,102,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r60 : Rule 158 8 := cutRule 8 p39 w50
def r61 : Rule 158 8 := cutRule 8 p30 w2
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p40 : Weak 158 6 := signedPick 12 [12,13,40,41,54,55] (by decide) (by decide) (by decide)
def r62 : Rule 158 8 := cutRule 8 p40 w14
def s52 : List ℕ := [f90,f72,f73,f91]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w51 : Wide 12 4 s52 := viaSearch (by decide +kernel)
def r63 : Rule 158 8 := cutRule 8 p20 w51
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w52 : Wide 18 2 s14 := viaSearch (by decide +kernel)
def r64 : Rule 158 6 := cutRule 6 p11 w52
def r65 : Rule 158 6 := cutRule 6 p11 w15
def r66 : Rule 158 6 := cutRule 6 p29 w15
def f161 : ℕ := 0x55fffffffffffffb3f
def f162 : ℕ := 0x103fffffffffffffdc3
def f163 : ℕ := 0xea800000000000006fc
def s53 : List ℕ := [f161,f162,f163]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w53 : Wide 65 3 s53 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p41 : Weak 158 65 := relaxed (pick [0,1,38,39,40,41,48,49,63,88,98,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r67 : Rule 158 6 := cutRule 6 p41 w53
def f164 : ℕ := 0xa50fc1ff
def f165 : ℕ := 0x1b7a0af1fe1f
def f166 : ℕ := 0x2485507e3fe0
def s54 : List ℕ := [f164,f165,f166]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w54 : Wide 23 3 s54 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p42 : Weak 158 23 := relaxed (pick [10,11,12,13,20,38,39,40,41,52,53,54,55,56,71,72,73,86,87,88,101,102,103] (by decide) (by decide) (by decide))
def r68 : Rule 158 6 := cutRule 6 p42 w54
def f167 : ℕ := 0xf801f0604003ffe60039c
def s55 : List ℕ := [f167,f57,f58,f23,f24,f25]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b8 : Ban 158 7 s55 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1871339698,r64),(2090025068,r65),(1024760577,r65),(1695806737,r65),(877449573,r64),(935186756,r65),(1360081056,r65),(1235756932,r64),(1578778742,r66),(1141695385,r66),(1625336075,r64),(942055560,r64),(1086573728,r65),(558577021,r65),(1790515833,r64),(11742646,r64),(1905691219,r65),(1103013481,r65),(587179874,r65),(1144302161,r64),(1304793778,r64),(1074837677,r67),(545752569,r68),(1870903846,r64),(1054691899,r65),(84959213,r65),(1667316138,r64),(310418605,r66),(642204902,r67)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r69 : Rule 158 7 := cutRule 7 p11 w52
def f168 : ℕ := 0x54bfffffffffffff79ff
def f169 : ℕ := 0x1017fffffffffffffbe1f
def f170 : ℕ := 0x3ea800000000000000cfe0
def s56 : List ℕ := [f168,f169,f170]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w55 : Wide 70 3 s56 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p43 : Weak 158 70 := relaxed (pick [0,1,2,3,4,38,39,40,41,48,49,50,63,68,88,98,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r70 : Rule 158 6 := cutRule 6 p43 w55
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p44 : Weak 158 23 := relaxed (pick [14,15,17,18,23,42,43,45,46,52,53,54,55,56,76,77,78,91,92,93,101,102,103] (by decide) (by decide) (by decide))
def r71 : Rule 158 6 := cutRule 6 p44 w54
def f171 : ℕ := 0x210842108420024a055024a94bfffffffffffff0001f003fff80493c154793fff
def s57 : List ℕ := [f21,f171,f58,f23,f24,f25]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b9 : Ban 158 7 s57 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1573216762,r64),(343201330,r65),(726726446,r65),(1539737640,r65),(1832121827,r64),(178684082,r64),(27604839,r65),(1163416820,r65),(1044587955,r64),(112519287,r66),(1823202535,r66),(159359578,r64),(583066924,r64),(788539597,r65),(532035231,r65),(1492481702,r64),(76875739,r64),(210893249,r65),(1555699158,r65),(1430418790,r65),(190412674,r64),(1006759647,r64),(776803546,r70),(247718438,r71),(1572869715,r64),(748941137,r65),(1990774403,r65),(1732257876,r64),(1022611911,r66),(344170771,r70)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f172 : ℕ := 0x210842108049424aafffffffffffffc0007c1ff8049e64ff
def f173 : ℕ := 0x6318c631826c1360c0000000000000000f83e00027e1bf0c
def f174 : ℕ := 0x14a5294a543001c005fffffffffffffc1f00000fc3801c00f
def f175 : ℕ := 0x18c6318c668000c95000000000000003e0003ff07c001fff0
def f176 : ℕ := 0x2108421081492a000000000000000003ffffc0007fffe0000
def s58 : List ℕ := [f172,f173,f174,f175,f176]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w56 : Wide 124 5 s58 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p45 : Weak 158 124 := relaxed (pick [0,1,5,6,10,11,12,13,14,15,16,17,18,19,20,23,24,38,39,40,41,42,43,44,45,46,47,48,49,51,52,53,54,55,56,59,60,61,62,63,69,70,71,72,73,74,75,76,77,78,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r72 : Rule 158 7 := cutRule 7 p45 w56
def r73 : Rule 158 7 := cutRule 7 p29 w52
def f177 : ℕ := 0x1607c
def f178 : ℕ := 0xa55fffffffffffffa87ab
def f179 : ℕ := 0x2083fffffffffffffc9843
def f180 : ℕ := 0xfd500000000000000067f80
def s59 : List ℕ := [f177,f178,f179,f180]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w57 : Wide 73 4 s59 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p46 : Weak 158 73 := relaxed (pick [0,1,25,26,27,28,33,38,39,40,41,48,49,57,58,63,83,88,98,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r74 : Rule 158 7 := cutRule 7 p46 w57
def f181 : ℕ := 0x2957ffffffffffffe07fc07ff
def f182 : ℕ := 0x800fffffffffffffe381c1803
def f183 : ℕ := 0x6db7a02a00000000000001c0e3e07c
def f184 : ℕ := 0x9248554000000000000001ff03ff80
def s60 : List ℕ := [f181,f182,f183,f184]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w58 : Wide 87 4 s60 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p47 : Weak 158 87 := relaxed (pick [0,1,10,11,12,13,20,38,39,40,41,48,49,52,53,54,55,56,61,62,63,71,72,73,86,87,88,96,97,98,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r75 : Rule 158 7 := cutRule 7 p47 w58
def f185 : ℕ := 0x54bfffffffffffff51f3
def f186 : ℕ := 0x3ea800000000000000effc
def s61 : List ℕ := [f185,f169,f186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w59 : Wide 70 3 s61 := viaSearch (by decide +kernel)
def r76 : Rule 158 6 := cutRule 6 p43 w59
def f187 : ℕ := 0xa143f079f
def f188 : ℕ := 0x1b7a0ebc7f87f
def f189 : ℕ := 0x2485501f8ffe0
def s62 : List ℕ := [f187,f188,f189]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w60 : Wide 25 3 s62 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p48 : Weak 158 25 := relaxed (pick [10,11,12,13,20,21,22,38,39,40,41,52,53,54,55,56,71,72,73,86,87,88,101,102,103] (by decide) (by decide) (by decide))
def r77 : Rule 158 6 := cutRule 6 p48 w60
def f190 : ℕ := 0x2108421084219549500000000000000000000000fffff0001f07ffffc00060039c
def s63 : List ℕ := [f21,f57,f58,f23,f24,f190]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b10 : Ban 158 7 s63 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(247783540,r64),(1542506568,r65),(477242077,r65),(1305470488,r65),(506688605,r64),(1000734507,r64),(849655264,r65),(1985467245,r65),(1866638380,r64),(2102795036,r66),(1665711679,r66),(1868722,r64),(1405117349,r64),(1610590022,r65),(1354085656,r65),(167048480,r64),(535758940,r64),(1032943674,r65),(230265936,r65),(104985568,r65),(1012463099,r64),(1828810072,r64),(1598853971,r76),(1069768863,r77),(247436493,r64),(1455351808,r65),(2124936623,r65),(406824654,r64),(1844662336,r66),(2047881469,r76)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s64 : List ℕ := [f185,f169,f170,f186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w61 : Wide 70 3 s64 := viaSearch (by decide +kernel)
def r78 : Rule 158 6 := cutRule 6 p43 w61
def s65 : List ℕ := [f21,f57,f58,f23,f24,f25,f190]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b11 : Ban 158 7 s65 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1413924350,r65),(904361456,r65),(1442409344,r65),(406824654,r64),(1166221196,r78),(1721305951,r66)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f191 : ℕ := 0xf0c07fc0
def f192 : ℕ := 0x1111250b2a0f0f278b3f
def f193 : ℕ := 0x5555304c30f000384c30
def f194 : ℕ := 0x6666007015000f00703f
def f195 : ℕ := 0x8888ca8000ff00ff8000
def s66 : List ℕ := [f191,f192,f193,f194,f195]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w62 : Wide 40 4 s66 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p49 : Weak 158 40 := relaxed (pick [14,15,17,18,23,24,25,27,29,31,33,34,35,36,37,42,43,45,46,48,49,51,57,58,75,76,77,78,80,81,82,83,90,91,92,93,95,96,97,98] (by decide) (by decide) (by decide))
def r79 : Rule 158 7 := cutRule 7 p49 w62
def f196 : ℕ := 0x49250820fffffffffffffe381e1843
def f197 : ℕ := 0xfffff56a00000000000001ffe3fffc
def s67 : List ℕ := [f181,f196,f183,f184,f197]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w63 : Wide 87 4 s67 := viaSearch (by decide +kernel)
def r80 : Rule 158 7 := cutRule 7 p47 w63
def f198 : ℕ := 0x11112557ffffffffffffe1fe64ff
def f199 : ℕ := 0x3339b0600000000000001e01bf0c
def f200 : ℕ := 0xaaae002fffffffffffffe01fc00f
def f201 : ℕ := 0xccc64a800000000000001fe1fff0
def s68 : List ℕ := [f198,f199,f200,f201]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w64 : Wide 83 3 s68 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p50 : Weak 158 83 := relaxed (pick [0,1,5,6,10,11,12,13,14,15,16,17,18,19,20,23,24,59,60,61,62,69,70,71,72,74,75,76,77,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r81 : Rule 158 7 := cutRule 7 p50 w64
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w65 : Wide 73 3 s59 := viaSearch (by decide +kernel)
def r82 : Rule 158 7 := cutRule 7 p46 w65
def f202 : ℕ := 0x1f000400000060039c
def s69 : List ℕ := [f202,f21,f57,f58,f23,f24,f25]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b7 : Ban 158 8 s69 := viaRules (ws := [s55,s57,s63,s65]) (consBan b8 (consBan b9 (consBan b10 (consBan b11 (nilBan _ _)))))
  (dictionary [(199477900,r17),(955026025,r17),(275219346,r69),(1355973694,r69),(1663469604,r49),(656991894,r17),(1739211050,r17),(2097327562,r17),(1032063071,r17),(583113466,r17),(658854912,r69),(200168601,r69),(1494891629,r17),(429627138,r17),(1257855549,r17),(192591058,r17),(459073666,r69),(1356503982,r69),(661664862,r17),(1923956482,r17),(260113525,r69),(2072982902,r69),(953119568,r69),(802040325,r17),(1285681015,r69),(1937852306,r17),(274009349,r69),(1819023441,r69),(1666232699,r69),(2055180097,r49),(391337140,r17),(1618096740,r49),(2101737430,r69),(13866064,r17),(1127990430,r17),(2026064246,r72),(1203731876,r69),(1357502410,r69),(1562975083,r17),(740642713,r69),(1306470717,r17),(484138347,r69),(119433541,r69),(488144001,r69),(551543934,r69),(118971218,r17),(1764072049,r69),(501075497,r69),(1462659118,r69),(245117419,r17),(1589923328,r17),(952610474,r17),(149932736,r17),(1022067921,r69),(1359399070,r69),(985328735,r17),(182650997,r17),(57370629,r17),(1402176538,r17),(964848160,r69),(990374846,r73),(246297211,r49),(840361904,r49),(378314546,r73),(1781195133,r69),(2093155934,r17),(609845504,r69),(1158235887,r69),(1551239032,r74),(728906662,r17),(1952306157,r17),(1022153924,r75),(199821554,r69),(1498849455,r69),(1479042319,r17),(1350460101,r17),(1274056132,r17),(1145473914,r17),(1723831139,r17),(1799572585,r69),(1039016394,r69),(1523376623,r17),(1394794405,r17),(617726242,r17),(489144024,r17),(359209715,r69),(1314230189,r73),(786819960,r49),(1706184518,r49),(1072585249,r73),(1109452365,r69),(1435772742,r17),(629725038,r69),(174544560,r69),(1303038678,r17),(910521070,r69),(1571091723,r79),(1118606257,r80),(782814718,r81),(1781939166,r82)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f203 : ℕ := 0x568170b00
def s70 : List ℕ := [f93,f203,f48,f49]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w66 : Wide 18 3 s70 := viaSearch (by decide +kernel)
def r83 : Rule 158 7 := cutRule 7 p21 w66
def f204 : ℕ := 0x377776beba0bffe01fffc00
def s71 : List ℕ := [f52,f54,f55,f56,f204]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w67 : Wide 45 5 s71 := viaSearch (by decide +kernel)
def r84 : Rule 158 7 := cutRule 7 p12 w67
def f205 : ℕ := 0x14a5294a5294428009806c00297fffffffffffff07c0000000f90b002601900063
def s72 : List ℕ := [f21,f57,f58,f205,f23,f24,f25]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b12 : Ban 158 8 s72 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2119956744,r83),(1267196125,r17),(201931634,r83),(1030160045,r17),(2112379201,r83),(231378162,r83),(725424064,r83),(574344821,r17),(1710156802,r17),(1591327937,r83),(1827484593,r49),(1390401236,r49),(1129806906,r83),(956949144,r17),(804995086,r69),(136904560,r17),(2132434149,r69),(2039221684,r83),(1577612676,r83),(1833193994,r49),(55838921,r17),(2051368510,r69),(1335279579,r17),(512947209,r69),(1078775213,r17),(256442843,r69),(260448497,r83),(343290210,r17),(323848430,r69),(2038759361,r83),(1355685934,r17),(2026064246,r72),(1203731876,r69),(1131703566,r83),(757633231,r17),(1977158772,r17),(737152656,r83),(762679342,r83),(150619042,r83),(1553499629,r83),(2119609697,r69),(1295681119,r17),(1167098901,r17),(390030738,r17),(261448520,r17),(131514211,r83),(559124456,r49),(844889745,r83),(881756861,r69),(271153111,r69),(571421178,r84),(1743129515,r17),(2094332703,r69)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f206 : ℕ := 0x16641b2
def f207 : ℕ := 0x167f83c
def f208 : ℕ := 0x3fa8180
def f209 : ℕ := 0x3fa99fc
def s73 : List ℕ := [f206,f207,f208,f209]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w68 : Wide 13 3 s73 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p51 : Weak 158 13 := signedPick 1 [1,4,10,11,12,13,20,21,22,61,62,71,72] (by decide) (by decide) (by decide)
def r85 : Rule 158 7 := cutRule 7 p51 w68
def f210 : ℕ := 0x1ad6b5ad6b5a6824ae553edf94bffffffffffffff801f07fe0f9f093f955fffe73
def s74 : List ℕ := [f21,f57,f58,f23,f24,f210,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b13 : Ban 158 8 s74 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1958132986,r2),(1436202298,r37),(370937807,r36),(2026216440,r2),(1448570092,r36),(108810294,r28),(1994825757,r35),(1776664732,r51),(173341834,r51),(1950944626,r28),(1986617980,r85),(1740118596,r36),(246297211,r49)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f211 : ℕ := 0x4afffffffffffffc6b
def f212 : ℕ := 0x111fffffffffffffd93
def f213 : ℕ := 0x2a000000000000003e0
def s75 : List ℕ := [f77,f211,f212,f213]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w69 : Wide 64 4 s75 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p52 : Weak 158 64 := relaxed (pick [0,1,25,26,33,38,39,48,49,57,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r86 : Rule 158 8 := cutRule 8 p52 w69
def f214 : ℕ := 0xafffffffffffffcf
def f215 : ℕ := 0x1400000000000003c
def f216 : ℕ := 0x21ffffffffffffff3
def s76 : List ℕ := [f214,f215,f216]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w70 : Wide 60 3 s76 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p53 : Weak 158 60 := relaxed (pick [0,1,38,39,48,49,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r87 : Rule 158 8 := cutRule 8 p53 w70
def r88 : Rule 158 7 := cutRule 7 p53 w70
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p54 : Weak 158 10 := relaxed (pick [10,11,25,26,35,38,39,52,53,57] (by decide) (by decide) (by decide))
def r89 : Rule 158 7 := cutRule 7 p54 w24
def r90 : Rule 158 7 := cutRule 7 p20 w51
def f217 : ℕ := 0x21084210840125024a94bfffffffffffff0001f07c1f0049e193e73
def f218 : ℕ := 0x6318c6318c11b04360f800000000000000003e0f8000047e18fc3e0
def f219 : ℕ := 0x1ce739ce73b54007c95297fffffffffffffffc00fffffff801ffffff
def f220 : ℕ := 0x39ce739ce73ea4abc950000000000000000fffffffc00ffffffffc00
def s77 : List ℕ := [f217,f218,f96,f219,f99,f100,f220]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w71 : Wide 138 6 s77 := viaSearch (by decide +kernel)
def r91 : Rule 158 7 := cutRule 7 p22 w71
def f221 : ℕ := 0x152ffffffffffffff33f3
def f222 : ℕ := 0x1599800000000000000cd9c
def f223 : ℕ := 0x2a605fffffffffffffcfe1f
def f224 : ℕ := 0x3fea0000000000000030fe0
def s78 : List ℕ := [f221,f222,f223,f224]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w72 : Wide 72 3 s78 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p55 : Weak 158 72 := relaxed (pick [0,1,2,3,4,10,11,12,13,20,21,22,61,62,66,67,71,72,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r92 : Rule 158 7 := cutRule 7 p55 w72
def f225 : ℕ := 0x250fcff0
def f226 : ℕ := 0x5512a0f13f
def f227 : ℕ := 0xaac05c3e0f
def f228 : ℕ := 0xffd8df3fcf
def s79 : List ℕ := [f225,f226,f227,f228]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w73 : Wide 20 3 s79 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p56 : Weak 158 20 := relaxed (pick [14,15,23,24,42,43,48,49,51,52,53,56,75,77,90,92,95,97,100,102] (by decide) (by decide) (by decide))
def r93 : Rule 158 7 := cutRule 7 p56 w73
def f229 : ℕ := 0x444444409284abfffffffffffff000f0ff024f33f
def f230 : ℕ := 0xccccccc4d82630000000000000000f0f0013f0dcc
def f231 : ℕ := 0x1111111300019400000000000000f000ff0e000ff0
def f232 : ℕ := 0x1999999a6003817fffffffffffff0f0000f9c00e0f
def f233 : ℕ := 0x2222222092540000000000000000ffff000ffff000
def s80 : List ℕ := [f229,f230,f231,f232,f233]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w74 : Wide 110 5 s80 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p57 : Weak 158 110 := relaxed (pick [0,1,5,6,10,11,14,15,16,20,23,24,38,39,40,41,42,43,44,45,46,47,48,49,51,52,53,56,59,60,62,63,69,70,72,73,74,75,77,78,84,85,87,88,89,90,92,93,94,95,97,98,99,100,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r94 : Rule 158 7 := cutRule 7 p57 w74
def f234 : ℕ := 0x924a90e49f3
def f235 : ℕ := 0x9360c707e1c
def f236 : ℕ := 0x12800281801f
def f237 : ℕ := 0x2449507fffe0
def s81 : List ℕ := [f234,f235,f236,f237]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w75 : Wide 23 4 s81 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p58 : Weak 158 23 := relaxed (pick [12,13,17,18,19,38,39,40,41,42,43,44,45,46,47,54,55,84,86,88,89,91,93] (by decide) (by decide) (by decide))
def r95 : Rule 158 7 := cutRule 7 p58 w75
def f238 : ℕ := 0x248c181c0f1c
def s82 : List ℕ := [f238,f149,f150,f151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w76 : Wide 24 4 s82 := viaSearch (by decide +kernel)
def r96 : Rule 158 7 := cutRule 7 p37 w76
def f239 : ℕ := 0x1ce739ce739c6a800f807c95297fffffffffffffffc0007ffff9ff003e01ffffff
def s83 : List ℕ := [f21,f57,f58,f23,f24,f239,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b14 : Ban 158 8 s83 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(293258790,r2),(1747891133,r50),(853547258,r35),(361342244,r50),(191685245,r2),(926066132,r50),(1931179543,r88),(1994825757,r35),(1382240032,r89),(1948350100,r89),(785325755,r51),(805932443,r90),(707026484,r90),(357374667,r51),(985295324,r28),(1772451634,r89),(321743784,r90),(719651156,r91),(152649986,r92),(1044864866,r50),(1189469018,r2),(1551239032,r74),(1052126911,r93),(728906662,r17),(1758381826,r94),(1875445767,r95),(844376055,r96)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r97 : Rule 158 7 := cutRule 7 p0 w0
def r98 : Rule 158 7 := cutRule 7 p30 w1
def r99 : Rule 158 6 := cutRule 6 p30 w1
def f240 : ℕ := 0xa6cffc
def f241 : ℕ := 0xa7e31c
def f242 : ℕ := 0xfedce0
def s84 : List ℕ := [f240,f241,f242]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w77 : Wide 12 3 s84 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p59 : Weak 158 12 := signedPick 12 [12,13,38,40,41,52,54,55,86,88,101,103] (by decide) (by decide) (by decide)
def r100 : Rule 158 6 := cutRule 6 p59 w77
def f243 : ℕ := 0x531f
def f244 : ℕ := 0x20de3
def f245 : ℕ := 0x3da6fc
def s85 : List ℕ := [f243,f244,f245]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w78 : Wide 11 3 s85 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p60 : Weak 158 11 := relaxed (pick [10,11,38,39,40,52,53,54,73,88,103] (by decide) (by decide) (by decide))
def r101 : Rule 158 6 := cutRule 6 p60 w78
def f246 : ℕ := 0x210842108420024a055024a94bfffffffffffff0001ff83e0fe0093fffe193e73
def f247 : ℕ := 0x14a5294a5294428009806c00297fffffffffffff07c00f801fff0f003ffff003ff
def s86 : List ℕ := [f246,f58,f247,f24,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b16 : Ban 158 7 s86 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(4536559,r4),(1112662141,r4),(1109256981,r99),(2065193852,r3),(85159442,r99),(1275706696,r3),(417851073,r4),(981737716,r3),(1215664268,r99),(800049951,r4),(390571228,r4),(1042326952,r65),(543214831,r99),(1555839603,r65),(349973203,r100),(1231382697,r101)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f248 : ℕ := 0x12a7f
def f249 : ℕ := 0x4479f
def s87 : List ℕ := [f248,f249,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w79 : Wide 10 2 s87 := viaSearch (by decide +kernel)
def r102 : Rule 158 6 := cutRule 6 p54 w79
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p61 : Weak 158 12 := signedPick 17 [17,18,42,45,46,52,54,55,91,93,101,103] (by decide) (by decide) (by decide)
def r103 : Rule 158 6 := cutRule 6 p61 w77
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p62 : Weak 158 11 := relaxed (pick [14,15,42,43,45,52,53,54,78,93,103] (by decide) (by decide) (by decide))
def r104 : Rule 158 6 := cutRule 6 p62 w78
def f250 : ℕ := 0x18c6318c631868000e003c950000000000000000f8000fffe007f0003ffffffc00
def s88 : List ℕ := [f246,f58,f23,f250,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b17 : Ban 158 7 s88 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1574373858,r4),(535015793,r4),(1395593235,r3),(1969834767,r3),(371079792,r102),(698060348,r3),(1987688372,r4),(404091368,r3),(222403603,r4),(1960408527,r4),(1804341109,r66),(1305228988,r3),(1576645605,r66),(1919810502,r103),(653736349,r104)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w80 : Wide 60 2 s76 := viaSearch (by decide +kernel)
def r105 : Rule 158 7 := cutRule 7 p53 w80
def f251 : ℕ := 0xa83fc
def s89 : List ℕ := [f248,f79,f251]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w81 : Wide 10 2 s89 := viaSearch (by decide +kernel)
def r106 : Rule 158 6 := cutRule 6 p54 w81
def f252 : ℕ := 0x2108421084219549500000000000000000000000ffffff800007fffffffe000000
def s90 : List ℕ := [f246,f58,f23,f24,f252,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b18 : Ban 158 7 s90 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2112421746,r4),(1073063681,r4),(1933641123,r3),(87988042,r3),(2025595392,r3),(45560982,r106),(306694054,r3),(378252613,r4),(605311970,r3),(760451491,r4),(350972768,r4),(194905350,r66),(1843276876,r3),(2114693493,r66),(487424949,r103),(878710536,r104)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s91 : List ℕ := [f246,f58,f23,f24,f25,f252,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b19 : Ban 158 7 s91 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1983839528,r4),(378252613,r4),(139003365,r3),(771059211,r3),(631869273,r4),(310374743,r103),(1191784237,r104)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r107 : Rule 158 7 := cutRule 7 p61 w77
def r108 : Rule 158 7 := cutRule 7 p62 w78
def s92 : List ℕ := [f21,f246,f58,f23,f24,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b15 : Ban 158 8 s92 := viaRules (ws := [s86,s88,s90,s91]) (consBan b16 (consBan b17 (consBan b18 (consBan b19 (nilBan _ _)))))
  (dictionary [(436749865,r2),(683001982,r97),(1904426833,r1),(517471696,r1),(366392453,r50),(850033143,r98),(1502204434,r2),(1985845124,r2),(1383375569,r1),(501984025,r1),(1264924378,r2),(1748565068,r2),(225566313,r2),(709207003,r2),(1022524061,r1),(921854538,r1),(984801520,r50),(1127327211,r50),(304994841,r98),(870822845,r2),(48490475,r1),(363592348,r2),(1831269316,r1),(1086143755,r1),(932609081,r1),(1548114797,r1),(359876593,r1),(1179407040,r1),(869718729,r98),(1328424177,r1),(65427625,r2),(923751198,r1),(426809804,r88),(549680863,r2),(1894486772,r2),(1769206404,r2),(966528666,r2),(1209006967,r2),(529200288,r1),(1387974321,r1),(1646550567,r2),(945256919,r2),(1178098024,r1),(1345547261,r51),(781079258,r105),(1657508062,r36),(174197632,r51),(722588015,r1),(293258790,r2),(1516658285,r2),(1911657329,r1),(603368522,r1),(1087728751,r2),(959146533,r2),(182078370,r2),(53496152,r2),(603368522,r2),(2071045490,r1),(388610868,r1),(1678238892,r2),(359275045,r2),(94641888,r1),(673804493,r51),(1000124870,r92),(194077166,r51),(1886380335,r1),(160876974,r2),(867390806,r2),(474873198,r1),(1135443851,r13),(682958385,r45),(347166846,r92),(1346291294,r36),(517858224,r1),(1810849833,r50),(1311737712,r98),(1296133889,r2),(797021768,r1),(1143313707,r1),(31503237,r1),(2060437770,r2),(1561325649,r1),(1650959047,r2),(1151846926,r1),(856336343,r1),(1509370100,r1),(1609411069,r1),(1157847195,r2),(1494891629,r17),(995779508,r1),(1425219369,r98),(2030182218,r1),(1267196125,r17),(768084004,r1),(219753789,r1),(2001590923,r1),(1702762840,r2),(943958261,r1),(1610361022,r107),(1111248901,r2),(344286869,r108),(1992658395,r1),(7250503,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f253 : ℕ := 0x12863
def s93 : List ℕ := [f77,f253,f79,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w82 : Wide 10 3 s93 := viaSearch (by decide +kernel)
def r109 : Rule 158 7 := cutRule 7 p54 w82
def r110 : Rule 158 7 := cutRule 7 p40 w14
def f254 : ℕ := 0xed79c
def s94 : List ℕ := [f77,f80,f128,f254]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w83 : Wide 10 3 s94 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p63 : Weak 158 10 := signedPick 12 [12,13,27,28,36,40,41,54,55,58] (by decide) (by decide) (by decide)
def r111 : Rule 158 7 := cutRule 7 p63 w83
def f255 : ℕ := 0x884abfffffffffffff0071f802733f
def f256 : ℕ := 0x9249210c26300000000000000038e00478dcc
def f257 : ℕ := 0x12492540019400000000000000e00fc7800ff0
def f258 : ℕ := 0x1b6db71403817fffffffffffff1c003c780e0f
def f259 : ℕ := 0x249248ab340000000000000000fff007fff000
def s95 : List ℕ := [f255,f256,f257,f258,f259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w84 : Wide 102 5 s95 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p64 : Weak 158 102 := relaxed (pick [0,1,5,6,10,11,14,15,16,20,23,24,38,39,40,42,43,44,45,48,49,50,51,52,53,54,56,60,62,63,70,72,73,75,77,78,85,87,88,90,92,93,95,97,98,100,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r112 : Rule 158 7 := cutRule 7 p64 w84
def f260 : ℕ := 0x210842108420024a055024a94bfffffffffffff0001f003e0f80093c000193e73
def s96 : List ℕ := [f21,f260,f58,f23,f24,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b20 : Ban 158 8 s96 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(436749865,r2),(920038062,r2),(1904426833,r1),(280435616,r109),(129356373,r50),(1265168354,r97),(1146339489,r51),(411938554,r29),(1361222769,r33),(2046499785,r28),(684818458,r109),(890291131,r50),(67958761,r98),(633786765,r97),(1958938042,r109),(1594233236,r51),(1962943696,r109),(2026343629,r109),(118714762,r28),(686715118,r51),(312644783,r88),(1657450692,r36),(1532170324,r97),(292164208,r51),(317690894,r28),(1089739432,r28),(1108511181,r109),(1674621249,r109),(366332442,r51),(850692671,r97),(722110453,r92),(2092525937,r97),(1834009410,r51),(641546237,r28),(2020513679,r29),(53912510,r28),(436768413,r109),(1649344255,r109),(280822144,r109),(1573813753,r50),(1059097809,r110),(906277627,r111),(614053752,r2),(1605339074,r16),(1986526273,r28),(1257855549,r17),(758743428,r109),(1030160045,r17),(1373324942,r96),(107250789,r112)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f261 : ℕ := 0x2b5ad6b5ad6b3138c466138cc60000000000000000000f801f06c4e33ffe6e339c
def s97 : List ℕ := [f57,f58,f247,f24,f25,f261]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b22 : Ban 158 7 s97 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1110750482,r4),(673667125,r4),(162925386,r99),(1581368578,r3),(836765518,r99),(369800574,r3),(1989873992,r4),(128155634,r3),(660844256,r4),(2088722044,r4),(1086573728,r65),(1478273378,r99),(1024000388,r65),(387817714,r100),(670654711,r101)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f262 : ℕ := 0x492803070219c
def f263 : ℕ := 0x9242f807e01e0
def f264 : ℕ := 0x9242f83fe3fe0
def f265 : ℕ := 0xb6d654800195a
def f266 : ℕ := 0xffffffff03f98
def s98 : List ℕ := [f262,f263,f264,f265,f266]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w85 : Wide 26 4 s98 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p65 : Weak 158 26 := signedPick 10 [10,12,20,21,22,38,40,48,50,52,53,54,55,56,71,72,73,86,87,88,96,97,98,101,102,103] (by decide) (by decide) (by decide)
def r113 : Rule 158 7 := cutRule 7 p65 w85
def s99 : List ℕ := [f21,f57,f58,f23,f24,f25,f261]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b21 : Ban 158 8 s99 := viaRules (ws := [s97]) (consBan b22 (nilBan _ _))
  (dictionary [(516126805,r98),(1810849833,r50),(745585342,r50),(1573813753,r50),(508549262,r50),(775031870,r98),(1269077772,r98),(1117998529,r50),(1601639219,r98),(106326863,r50),(2134981645,r98),(1982190903,r98),(223654654,r2),(1934054944,r2),(329824268,r50),(1673460614,r98),(1736407596,r50),(1878933287,r50),(1056600917,r98),(1622428921,r50),(800096551,r98),(1115198424,r50),(435391745,r98),(804102205,r98),(886943918,r50),(867502138,r98),(434929422,r50),(1621324805,r98),(2080030253,r98),(817033701,r98),(1675357274,r98),(1301286939,r50),(373328833,r50),(1280806364,r98),(1306333050,r1),(694272750,r1),(2097153337,r98),(1532685334,r50),(261630491,r50),(925803708,r98),(1044864866,r50),(120780714,r50),(515779758,r98),(1354974598,r98),(1839334827,r50),(1710752609,r50),(933684446,r50),(805102228,r50),(675167919,r98),(1630188393,r1),(1102778164,r2),(2022142722,r2),(1388543453,r1),(1425410569,r98),(1751730946,r50),(490502764,r98),(912483050,r50),(1618996882,r50),(1226479274,r98),(1887049927,r13),(1434564461,r113),(1098772922,r88),(80950876,r50),(1156928194,r110),(1548627844,r98),(1817240491,r98),(1921232075,r2),(165448078,r50),(1201626216,r2),(1593325866,r98),(827684782,r50),(1342715469,r17),(1734415119,r98),(1630220081,r98),(136904560,r17),(528604210,r98),(523413915,r50),(1648205533,r96),(1931042530,r112),(175258533,r98),(310278814,r50)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r114 : Rule 158 7 := cutRule 7 p40 w18
def f267 : ℕ := 0x2b5ad6b5ad6b3138c466138cc600000000000000000000001f00c4e300006e339c
def s100 : List ℕ := [f21,f57,f58,f23,f24,f25,f267]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b23 : Ban 158 8 s100 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1410861,r114),(1296133889,r2),(230869398,r1),(1059097809,r110),(2141316965,r110),(260315926,r114),(754361828,r114),(603282585,r50),(1739094566,r110),(1620265701,r114),(1856422357,r16),(1419339000,r16),(1158744670,r114),(1364217343,r50),(541884973,r98),(1107712977,r110),(285380607,r114),(2068159448,r114),(289386261,r114),(352786194,r114),(1160641330,r114),(786570995,r110),(2131376904,r110),(2006096536,r110),(766090420,r114),(791617106,r21),(179556806,r21),(1582437393,r114),(1063814,r114),(840258654,r114),(1324618883,r110),(1196036665,r110),(418968502,r110),(290386284,r110),(160451975,r114),(1115472449,r21),(588062220,r16),(873827509,r21),(910694625,r114),(2123270467,r114),(80950876,r50),(1671644138,r50),(1548627844,r98),(711946167,r2),(1511753352,r16),(1355685934,r17),(1232669640,r114),(992531914,r114),(1127990430,r17),(1158235931,r96),(2039491120,r112)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w86 : Wide 10 3 s87 := viaSearch (by decide +kernel)
def r115 : Rule 158 6 := cutRule 6 p17 w86
def f268 : ℕ := 0x378ff
def f269 : ℕ := 0x483e0
def f270 : ℕ := 0x8071f
def s101 : List ℕ := [f268,f269,f270]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w87 : Wide 10 3 s101 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p66 : Weak 158 10 := relaxed (pick [10,11,16,26,30,38,39,44,52,53] (by decide) (by decide) (by decide))
def r116 : Rule 158 6 := cutRule 6 p66 w87
def r117 : Rule 158 6 := cutRule 6 p17 w79
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p67 : Weak 158 8 := relaxed (pick [10,11,13,38,39,41,52,53] (by decide) (by decide) (by decide))
def r118 : Rule 158 6 := cutRule 6 p67 w44
def f271 : ℕ := 0x6318c6318c6023601784360f800000000000000003e0ffc000608fc3fff8fc3e0
def s102 : List ℕ := [f57,f271,f23,f250,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b25 : Ban 158 7 s102 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1435168163,r115),(1424788075,r116),(1816577952,r99),(943373688,r117),(1306891823,r99),(495180493,r117),(2115253911,r115),(253535553,r117),(810619366,r99),(1572052161,r115),(1863012988,r118),(1111489805,r65),(612377684,r99),(883794301,r65),(1226959198,r100),(2108368692,r101)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w88 : Wide 10 3 s89 := viaSearch (by decide +kernel)
def r119 : Rule 158 6 := cutRule 6 p17 w88
def f272 : ℕ := 0x483f8
def f273 : ℕ := 0x80707
def s103 : List ℕ := [f268,f272,f273]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w89 : Wide 10 3 s103 := viaSearch (by decide +kernel)
def r120 : Rule 158 6 := cutRule 6 p66 w89
def r121 : Rule 158 6 := cutRule 6 p17 w81
def s104 : List ℕ := [f57,f271,f23,f24,f252,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b26 : Ban 158 7 s104 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1973216051,r119),(1962835963,r120),(207142193,r99),(97312738,r121),(1994214335,r99),(1409941234,r121),(1832884956,r119),(445594654,r121),(2066972143,r99),(2110100049,r119),(253577229,r118),(1649537693,r65),(1150425572,r99),(1421842189,r65),(1942057292,r100),(185859232,r101)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s105 : List ℕ := [f248,f79,f80,f251]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w90 : Wide 10 3 s105 := viaSearch (by decide +kernel)
def r122 : Rule 158 6 := cutRule 6 p17 w90
def f274 : ℕ := 0xa50cf8
def f275 : ℕ := 0xa7dc38
def f276 : ℕ := 0xfd20c0
def s106 : List ℕ := [f274,f275,f276]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w91 : Wide 12 3 s106 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p68 : Weak 158 12 := signedPick 11 [11,12,13,39,40,41,54,55,71,73,86,88] (by decide) (by decide) (by decide)
def r123 : Rule 158 6 := cutRule 6 p68 w91
def s107 : List ℕ := [f57,f271,f23,f24,f25,f252,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b27 : Ban 158 7 s107 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1844633833,r122),(505818152,r122),(78207907,r99),(1981517831,r123),(1765007086,r100),(498932933,r101)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r124 : Rule 158 7 := cutRule 7 p59 w77
def r125 : Rule 158 7 := cutRule 7 p60 w78
def s108 : List ℕ := [f21,f57,f271,f23,f24,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b24 : Ban 158 8 s108 := viaRules (ws := [s102,s104,s107]) (consBan b25 (consBan b26 (consBan b27 (nilBan _ _))))
  (dictionary [(1219153072,r98),(366392453,r50),(1448611609,r50),(129356373,r50),(1211575529,r50),(1478058137,r98),(1972800499,r50),(1362998739,r97),(1292993820,r98),(2101483566,r98),(1125718683,r29),(1055713764,r50),(1115338595,r33),(1045333676,r98),(1590684561,r50),(229003234,r98),(434475907,r50),(1759627184,r98),(177971541,r50),(1503122818,r98),(1138418012,r98),(1507128472,r98),(1589970185,r50),(1570528405,r98),(1137955689,r50),(1924917959,r98),(1327949556,r98),(1895404033,r98),(230899894,r98),(1881442147,r88),(2004313206,r50),(1201635468,r50),(1076355100,r50),(516155663,r50),(1983832631,r98),(2009359317,r30),(1859346375,r36),(1397299017,r30),(1146716967,r98),(224905976,r50),(558172053,r50),(1418777132,r98),(1747891133,r50),(823806981,r50),(1218806025,r98),(2058000865,r98),(394877447,r50),(266295229,r50),(1636710713,r50),(1508128495,r50),(2058000865,r50),(1378194186,r98),(185731013,r30),(1805804431,r29),(577685342,r92),(2091569720,r30),(501169886,r98),(406200111,r50),(1921555334,r98),(1193529031,r98),(1615509317,r50),(174539502,r50),(1929505541,r98),(442592547,r36),(2137590728,r45),(1801799189,r88),(653439990,r36),(1972490567,r98),(1117998529,r50),(618886408,r98),(603282585,r50),(450462403,r98),(1372331164,r98),(1262602681,r2),(763490560,r50),(1553563508,r16),(1054451387,r98),(918692109,r50),(918179613,r98),(321487112,r98),(802040325,r17),(302928204,r98),(1337330914,r98),(574344821,r17),(75232700,r98),(1009911536,r50),(251106957,r98),(917509718,r124),(1798919212,r125),(1299807091,r98),(1461882846,r50)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r126 : Rule 158 7 := cutRule 7 p17 w82
def r127 : Rule 158 7 := cutRule 7 p63 w41
def f277 : ℕ := 0x6318c6318c6023601784360f800000000000000003e007c000008fc00018fc3e0
def s109 : List ℕ := [f21,f57,f277,f23,f24,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b28 : Ban 158 8 s109 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(207481406,r126),(1502204434,r2),(436939943,r1),(1265168354,r97),(199903863,r126),(466386471,r51),(1972800499,r50),(227186758,r50),(1292993820,r98),(901781332,r29),(86360618,r33),(1364815215,r89),(1570287888,r50),(747955518,r98),(1313783522,r97),(491451152,r89),(126746346,r51),(495456806,r89),(558856739,r89),(1366711875,r51),(992641540,r88),(189963802,r36),(64683434,r97),(972160965,r51),(997687651,r126),(385627351,r126),(1788507938,r89),(207134359,r89),(1046329199,r51),(1530689428,r97),(1402107210,r92),(625039047,r97),(366522520,r51),(1321542994,r126),(794132765,r29),(1079898054,r126),(1116765170,r89),(181857365,r89),(960818901,r89),(106326863,r50),(1739094566,r110),(1586274384,r127),(250931015,r2),(541891842,r16),(1937852306,r17),(1438740185,r89),(1710156802,r17),(2053321699,r96),(787247546,r112)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s110 : List ℕ := [f57,f58,f247,f24,f252,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b30 : Ban 158 7 s110 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(387629400,r4),(2098029690,r4),(1587287951,r99),(858247496,r3),(113644436,r99),(23392345,r3),(446336067,r4),(1206529412,r3),(314828969,r99),(723551160,r4),(1014511987,r4),(1070811946,r65),(571699825,r99),(1584324597,r65),(555508403,r100),(946793990,r101)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s111 : List ℕ := [f57,f58,f247,f24,f25,f252,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b31 : Ban 158 7 s111 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(259047182,r4),(1794163139,r3),(1552518199,r3),(278645378,r4),(839142665,r99),(594968942,r4),(378458197,r100),(1259867691,r101),(387817714,r100)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s112 : List ℕ := [f21,f57,f58,f247,f24,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b29 : Ban 158 8 s112 := viaRules (ws := [s86,s110,s111,s97]) (consBan b16 (consBan b30 (consBan b31 (consBan b22 (nilBan _ _)))))
  (dictionary [(1980087830,r98),(741869399,r2),(1127327211,r50),(62062720,r50),(890291131,r50),(1972510287,r50),(771315927,r50),(91509248,r98),(585555150,r98),(434475907,r50),(1570287888,r50),(2053928578,r98),(1451459023,r98),(1298668281,r98),(1687615679,r2),(23772722,r50),(1250532322,r2),(1734173012,r98),(1793785293,r50),(796380608,r50),(731617150,r97),(116573929,r98),(739790583,r98),(1000692535,r50),(593340674,r98),(423834296,r50),(538369070,r98),(1164103007,r98),(1147267895,r98),(991834652,r98),(617764317,r50),(1837289858,r50),(1034612120,r50),(597283742,r98),(622810428,r1),(2026216440,r2),(472797486,r2),(10750128,r1),(1413630715,r98),(849162712,r50),(1725591516,r50),(242281086,r98),(1013221592,r50),(2014465779,r50),(1701229108,r98),(671451976,r98),(1155812205,r50),(1027229987,r50),(250161824,r50),(121579606,r50),(671451976,r50),(2139128944,r98),(946665771,r1),(419255542,r2),(1338620100,r2),(705020831,r1),(741887947,r98),(1068208324,r50),(262160620,r98),(396651894,r98),(432444294,r50),(1103855860,r50),(366351927,r98),(1203527305,r36),(751041839,r113),(415250300,r92),(1414374748,r36),(585941678,r98),(2059627845,r50),(1878933287,r50),(1379821166,r98),(1364217343,r50),(865105222,r98),(1891203840,r50),(1211397161,r98),(2133265922,r98),(2023537439,r2),(1524425318,r50),(167014619,r2),(1815386145,r98),(1679626867,r50),(1577453554,r98),(1677494523,r98),(1225930649,r98),(223314578,r17),(1871686104,r98),(692708530,r98),(823725236,r98),(736827229,r17),(237715108,r98),(287837243,r98),(2069674377,r98),(1770846294,r50),(1012041715,r98),(1678444476,r124),(1179332355,r50),(412370323,r125),(2060741849,r98),(75333957,r50)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f278 : ℕ := 0x13833c460
def f279 : ℕ := 0x1383fcfe0
def f280 : ℕ := 0x5548483025a
def f281 : ℕ := 0xaaa03300c1c
def f282 : ℕ := 0xfffffff0fd8
def s113 : List ℕ := [f278,f279,f280,f281,f282]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w92 : Wide 22 4 s113 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p69 : Weak 158 22 := signedPick 0 [0,5,20,23,24,38,42,48,49,51,52,56,60,62,85,87,90,92,95,97,100,102] (by decide) (by decide) (by decide)
def r128 : Rule 158 7 := cutRule 7 p69 w92
def f283 : ℕ := 0x14a5294a5294428009806c00297fffffffffffff07c000001ff90f000001f003ff
def s114 : List ℕ := [f21,f57,f58,f283,f24,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b32 : Ban 158 8 s114 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1723583464,r28),(870822845,r2),(1953042001,r1),(633786765,r97),(1716005921,r28),(1982488529,r51),(329050784,r89),(177971541,r50),(1313783522,r97),(1194954657,r51),(1431111313,r29),(994027956,r33),(796380608,r50),(988121516,r50),(116573929,r98),(2011558864,r89),(1493764154,r1),(1359693885,r89),(735330286,r51),(361259951,r88),(1706065860,r36),(1580785492,r97),(340779376,r51),(366306062,r28),(1901729409,r28),(1157126349,r89),(1226243276,r89),(414947610,r51),(899307839,r97),(770725621,r92),(2141141105,r97),(1882624578,r51),(690161405,r28),(162751176,r29),(448516465,r28),(485383581,r89),(1697959423,r89),(191361448,r128),(1518244358,r89),(329437312,r89),(1622428921,r50),(1107712977,r110),(954892795,r127),(1767033073,r2),(2057993900,r16),(1306470717,r17),(807358596,r89),(87689343,r17),(1421940110,r96),(155865957,r112)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w93 : Wide 12 3 s52 := viaSearch (by decide +kernel)
def r129 : Rule 158 7 := cutRule 7 p20 w93
def s115 : List ℕ := [f78,f249,f251]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w94 : Wide 10 3 s115 := viaSearch (by decide +kernel)
def r130 : Rule 158 6 := cutRule 6 p17 w94
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w95 : Wide 10 2 s115 := viaSearch (by decide +kernel)
def r131 : Rule 158 6 := cutRule 6 p54 w95
def r132 : Rule 158 6 := cutRule 6 p17 w95
def r133 : Rule 158 6 := cutRule 6 p8 w11
def f284 : ℕ := 0x28aa3303caf
def f285 : ℕ := 0x5528305cffc3ff
def f286 : ℕ := 0xaad5400fcffff0
def s116 : List ℕ := [f284,f285,f286]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w96 : Wide 28 3 s116 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p70 : Weak 158 28 := relaxed (pick [10,11,12,13,25,26,27,28,35,36,38,39,40,41,52,53,54,55,57,58,71,73,81,83,86,88,101,103] (by decide) (by decide) (by decide))
def r134 : Rule 158 6 := cutRule 6 p70 w96
def f287 : ℕ := 0x2adb07fffc
def f288 : ℕ := 0x2adf7180e0
def f289 : ℕ := 0x3ffbae7f14
def s117 : List ℕ := [f287,f288,f289]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w97 : Wide 19 3 s117 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p71 : Weak 158 19 := signedPick 12 [12,13,27,28,36,38,40,41,52,54,55,57,58,81,83,86,88,101,103] (by decide) (by decide) (by decide)
def r135 : Rule 158 6 := cutRule 6 p71 w97
def f290 : ℕ := 0x94a0eb
def f291 : ℕ := 0x4237f1f
def f292 : ℕ := 0x3fb41dffc
def s118 : List ℕ := [f290,f291,f292]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w98 : Wide 17 3 s118 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p72 : Weak 158 17 := relaxed (pick [10,11,25,26,35,38,39,40,52,53,54,57,58,73,83,88,103] (by decide) (by decide) (by decide))
def r136 : Rule 158 6 := cutRule 6 p72 w98
def s119 : List ℕ := [f57,f58,f23,f250,f252,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b34 : Ban 158 7 s119 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1957466699,r130),(1520383342,r130),(390430603,r131),(875904075,r132),(1664709986,r132),(399564786,r131),(1593229644,r132),(2016173366,r130),(628883064,r132),(272215602,r131),(2041216852,r133),(145904812,r130),(436865639,r130),(1832826103,r134),(1333713982,r131),(1605130599,r134),(2125345702,r135),(369147642,r136)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s120 : List ℕ := [f78,f249,f80,f251]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w99 : Wide 10 3 s120 := viaSearch (by decide +kernel)
def r137 : Rule 158 6 := cutRule 6 p17 w99
def f293 : ℕ := 0x9406e
def f294 : ℕ := 0x142871c
def f295 : ℕ := 0x2b407e0
def f296 : ℕ := 0x3ffe76c
def s121 : List ℕ := [f293,f294,f295,f296]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w100 : Wide 13 3 s121 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p73 : Weak 158 13 := signedPick 3 [3,4,12,13,22,40,41,50,54,55,58,66,68] (by decide) (by decide) (by decide)
def r138 : Rule 158 6 := cutRule 6 p73 w100
def f297 : ℕ := 0x2b6c1fffc
def f298 : ℕ := 0x2b7dc60e0
def s122 : List ℕ := [f297,f298,f65]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w101 : Wide 17 3 s122 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p74 : Weak 158 17 := signedPick 12 [12,13,27,28,36,38,40,41,52,54,55,57,58,86,88,101,103] (by decide) (by decide) (by decide)
def r139 : Rule 158 6 := cutRule 6 p74 w101
def s123 : List ℕ := [f57,f58,f23,f250,f25,f252,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b35 : Ban 158 7 s123 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1828884481,r137),(1216516791,r132),(689106562,r137),(974871851,r132),(261496317,r138),(17322594,r137),(1948295496,r139),(682221343,r136)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f299 : ℕ := 0x26544
def f300 : ℕ := 0x267fc
def f301 : ℕ := 0x3f33c
def f302 : ℕ := 0x3eeed8
def s124 : List ℕ := [f299,f300,f301,f302]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w102 : Wide 11 3 s124 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p75 : Weak 158 11 := signedPick 5 [5,6,38,42,43,44,48,51,85,90,95] (by decide) (by decide) (by decide)
def r140 : Rule 158 7 := cutRule 7 p75 w102
def f303 : ℕ := 0x17fffffffffffff61f
def f304 : ℕ := 0x54bfffffffffffffbf3
def f305 : ℕ := 0x3a8000000000000009e0
def f306 : ℕ := 0x3e60000000000000059c
def s125 : List ℕ := [f303,f304,f305,f306]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w103 : Wide 66 3 s125 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p76 : Weak 158 66 := relaxed (pick [0,1,2,3,4,38,39,40,41,63,68,88,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r141 : Rule 158 7 := cutRule 7 p76 w103
def f307 : ℕ := 0xff98c309cc
def s126 : List ℕ := [f225,f226,f227,f307]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w104 : Wide 20 3 s126 := viaSearch (by decide +kernel)
def r142 : Rule 158 7 := cutRule 7 p56 w104
def f308 : ℕ := 0x15fffffffffffffb1f
def f309 : ℕ := 0x83fffffffffffffde3
def f310 : ℕ := 0xf6800000000000006fc
def s127 : List ℕ := [f308,f309,f310]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w105 : Wide 65 3 s127 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p77 : Weak 158 65 := relaxed (pick [0,1,38,39,40,48,49,50,63,88,98,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r143 : Rule 158 7 := cutRule 7 p77 w105
def s128 : List ℕ := [f21,f57,f58,f23,f250,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b33 : Ban 158 8 s128 := viaRules (ws := [s88,s102,s119,s123]) (consBan b17 (consBan b25 (consBan b34 (consBan b35 (nilBan _ _)))))
  (dictionary [(1402441482,r51),(164223051,r2),(549680863,r2),(1631900019,r1),(312644783,r88),(1394863939,r30),(193669579,r88),(1661346547,r51),(7908802,r51),(1020276928,r50),(2004313206,r50),(340470249,r98),(992641540,r88),(1476282230,r51),(1553619354,r88),(873812675,r51),(721021933,r51),(1109969331,r29),(1593610021,r31),(672885974,r55),(1156526664,r51),(1216138945,r30),(412291644,r51),(617764317,r50),(1942915594,r98),(361259951,r88),(1686411228,r88),(1321706422,r51),(1690416882,r30),(1773258595,r1),(1753816815,r129),(1321244099,r30),(669844146,r51),(360155835,r98),(818861283,r88),(1703348378,r51),(1136772451,r88),(1630000709,r97),(456965772,r36),(28406707,r30),(1136987673,r36),(261926094,r36),(817212618,r30),(1699551065,r51),(408194386,r105),(218604064,r36),(1880197894,r51),(435575244,r88),(70147183,r36),(905101294,r88),(93805628,r51),(578165857,r88),(449583639,r88),(1819999123,r88),(1691416905,r88),(93805628,r88),(1561482596,r51),(369019423,r30),(1989092841,r29),(760973752,r92),(127374483,r30),(164241599,r51),(330117547,r140),(490561976,r88),(1831997919,r51),(1376817441,r141),(1798797727,r128),(357827912,r92),(2112793951,r129),(1294575246,r36),(100685975,r113),(85008089,r88),(1413377488,r36),(8295330,r51),(1301286939,r50),(786570995,r110),(287458874,r114),(633750813,r51),(1555619574,r30),(1445891091,r2),(946778970,r1),(1736851918,r16),(1237739797,r21),(1101980519,r51),(999807206,r51),(1099848175,r114),(648284301,r51),(985328735,r17),(486216614,r142),(915656475,r98),(1520619324,r114),(757633231,r17),(258521110,r51),(1123799682,r142),(221645262,r51),(434395367,r142),(1100798128,r96),(601686007,r51),(1982207622,r143),(1483095501,r142),(1645171256,r51)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f311 : ℕ := 0x44583
def s129 : List ℕ := [f77,f78,f311,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w106 : Wide 10 3 s129 := viaSearch (by decide +kernel)
def r144 : Rule 158 7 := cutRule 7 p17 w106
def r145 : Rule 158 7 := cutRule 7 p54 w106
def f312 : ℕ := 0xbba7c
def s130 : List ℕ := [f77,f80,f312,f129]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w107 : Wide 10 3 s130 := viaSearch (by decide +kernel)
def r146 : Rule 158 7 := cutRule 7 p63 w107
def f313 : ℕ := 0x18c6318c631868000e003c950000000000000000f800007fe001f0000001fffc00
def s131 : List ℕ := [f21,f57,f58,f23,f313,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b36 : Ban 158 8 s131 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(474483376,r144),(1769206404,r2),(703941913,r1),(1532170324,r97),(466905833,r144),(733388441,r51),(1227434343,r145),(1076355100,r50),(64683434,r97),(2093338216,r51),(182011225,r29),(1892411515,r33),(1631817185,r145),(1837289858,r50),(1014957488,r98),(1580785492,r97),(758453122,r145),(393748316,r51),(762458776,r145),(825858709,r145),(1136772451,r88),(410475168,r88),(456965772,r36),(1264689621,r144),(652629321,r144),(2055509908,r145),(539035816,r145),(1313331169,r51),(1797691398,r97),(1669109180,r92),(892041017,r97),(633524490,r51),(1588544964,r144),(1061134735,r29),(1346900024,r144),(1383767140,r145),(448859335,r145),(1227820871,r145),(373328833,r50),(2006096536,r110),(1853276354,r146),(517932985,r2),(808893812,r16),(57370629,r17),(1705742155,r145),(1977158772,r17),(172840022,r96),(1054249516,r112)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f314 : ℕ := 0x2480fcff80
def f315 : ℕ := 0x2692fcff93
def f316 : ℕ := 0x55135b0f13ff
def f317 : ℕ := 0xaac024c3e07c
def f318 : ℕ := 0xff9861309c63
def s132 : List ℕ := [f314,f315,f316,f317,f318]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w108 : Wide 24 4 s132 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p78 : Weak 158 24 := relaxed (pick [5,6,14,15,16,23,24,42,43,44,48,49,51,52,53,56,75,77,90,92,95,97,100,102] (by decide) (by decide) (by decide))
def r147 : Rule 158 7 := cutRule 7 p78 w108
def f319 : ℕ := 0xa152000000000000000fc000f1e0
def s133 : List ℕ := [f319,f133,f134,f135,f136,f137]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w109 : Wide 96 5 s133 := viaSearch (by decide +kernel)
def r148 : Rule 158 7 := cutRule 7 p32 w109
def f320 : ℕ := 0x18c6318c608a86c1f000000000000000007fe000011f8fc3e0
def f321 : ℕ := 0x5294a52950a0d80052fffffffffffffe0f8000ffe1e1f003ff
def f322 : ℕ := 0x6318c6319a00792a0000000000000001f003ff003e01fffc00
def f323 : ℕ := 0x8c6318c625550495297ffffffffffffffffc1f07fffe193e73
def f324 : ℕ := 0xad6b5ad6ac4c27198c00000000000000000000f818986e339c
def s134 : List ℕ := [f320,f321,f322,f323,f324]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w110 : Wide 127 5 s134 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p79 : Weak 158 127 := relaxed (pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,42,43,45,46,48,49,50,51,52,53,54,55,56,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r149 : Rule 158 7 := cutRule 7 p79 w110
def f325 : ℕ := 0x249242d5000000000000000038e0078f000
def s135 : List ℕ := [f132,f133,f134,f325,f136,f137]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w111 : Wide 96 5 s135 := viaSearch (by decide +kernel)
def r150 : Rule 158 7 := cutRule 7 p32 w111
def f326 : ℕ := 0x6f23e0
def s136 : List ℕ := [f90,f72,f73,f326,f91]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w112 : Wide 12 4 s136 := viaSearch (by decide +kernel)
def r151 : Rule 158 7 := cutRule 7 p20 w112
def f327 : ℕ := 0x49440d00000c
def s137 : List ℕ := [f238,f327,f149,f150,f151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w113 : Wide 24 4 s137 := viaSearch (by decide +kernel)
def r152 : Rule 158 7 := cutRule 7 p37 w113
def f328 : ℕ := 0x124a201900000030
def s138 : List ℕ := [f50,f328,f15,f16,f51]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w114 : Wide 31 4 s138 := viaSearch (by decide +kernel)
def r153 : Rule 158 7 := cutRule 7 p4 w114
def f329 : ℕ := 0x2318c6318c63956df055024a94bffffffffffffffffff003e0ffffffc154193e73
def s139 : List ℕ := [f21,f57,f58,f23,f24,f25,f329,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b37 : Ban 158 8 s139 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(351172088,r2),(114136008,r29),(1805804431,r29),(794132765,r29),(1976725047,r40),(312882090,r52),(911460556,r29),(474377199,r29),(2082894661,r147),(419255542,r2),(162751176,r29),(492530664,r2),(40516168,r148),(1989092841,r29),(1061134735,r29),(379657082,r29),(1621490348,r29),(1364357357,r149),(1235775139,r92),(299092866,r28),(1627729468,r92),(57447926,r28),(1728871170,r44),(287901355,r150),(103468934,r14),(1451934965,r51),(1539033197,r29),(933815542,r29),(1715034206,r51),(2124686297,r89),(1406610388,r89),(1337162170,r36),(1580131511,r151),(497731682,r28),(1102778164,r2),(588062220,r16),(1247382316,r2),(1538343143,r16),(786819960,r49),(559124456,r49),(902289353,r152),(1783698847,r19),(1975677499,r18),(1476565378,r127),(1406811525,r153),(610858078,r24),(41992104,r19),(1672444593,r127)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f330 : ℕ := 0x444444114456007878023ccfc
def f331 : ℕ := 0x2222220aab8007ff8007ffc000
def s140 : List ℕ := [f330,f109,f110,f331,f112]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w115 : Wide 51 5 s140 := viaSearch (by decide +kernel)
def r154 : Rule 158 7 := cutRule 7 p24 w115
def f332 : ℕ := 0x246181c79c
def f333 : ℕ := 0x919a0fffe0
def f334 : ℕ := 0xb5ffa1c7e0
def f335 : ℕ := 0xdbbadffb8c
def s141 : List ℕ := [f332,f333,f334,f335]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w116 : Wide 20 4 s141 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p80 : Weak 158 20 := signedPick 12 [12,13,17,18,19,40,41,42,45,46,47,52,54,55,89,91,93,99,101,103] (by decide) (by decide) (by decide)
def r155 : Rule 158 7 := cutRule 7 p80 w116
def f336 : ℕ := 0x24255fffffffffffff8038fc01333f
def f337 : ℕ := 0x249248431318000000000000001c70023cdcc
def f338 : ℕ := 0x492495000ca000000000000007007e3c00ff0
def f339 : ℕ := 0x6db6dc501c0bfffffffffffff8e001e3c0e0f
def f340 : ℕ := 0x924922aca00000000000000007ff803fff000
def s142 : List ℕ := [f336,f337,f338,f339,f340]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w117 : Wide 101 5 s142 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p81 : Weak 158 101 := relaxed (pick [0,1,5,6,10,11,14,15,16,20,23,24,38,39,42,43,44,45,48,49,50,51,52,53,54,56,60,62,63,70,72,73,75,77,78,85,87,88,90,92,93,95,97,98,100,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r156 : Rule 158 7 := cutRule 7 p81 w117
def f341 : ℕ := 0x2108421084219549500000000000000000000000fffe00000007ff6c0000000000
def s143 : List ℕ := [f21,f57,f58,f23,f24,f341,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b38 : Ban 158 8 s143 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1270536646,r2),(577685342,r92),(1830825114,r29),(1338620100,r2),(760973752,r92),(464162827,r51),(1161913624,r92),(1931839795,r51),(1627729468,r92),(211966393,r29),(1747174640,r89),(1299021640,r92),(393371259,r92),(1218457424,r28),(2042076975,r154),(976812484,r28),(739376622,r28),(2022142722,r2),(19263227,r2),(1706184518,r49),(1164763854,r155),(617314493,r156)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w118 : Wide 17 3 s19 := viaSearch (by decide +kernel)
def r157 : Rule 158 7 := cutRule 7 p14 w118
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w119 : Wide 12 2 s84 := viaSearch (by decide +kernel)
def r158 : Rule 158 7 := cutRule 7 p61 w119
def f342 : ℕ := 0x114180ee
def f343 : ℕ := 0x15602981c1c
def f344 : ℕ := 0x2a9ec1f9fe0
def f345 : ℕ := 0x3fffff99cec
def s144 : List ℕ := [f342,f343,f344,f345]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w120 : Wide 21 3 s144 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p82 : Weak 158 21 := signedPick 3 [3,4,12,13,22,38,40,41,48,50,52,54,55,66,68,86,88,96,98,101,103] (by decide) (by decide) (by decide)
def r159 : Rule 158 7 := cutRule 7 p82 w120
def r160 : Rule 158 7 := cutRule 7 p74 w118
def r161 : Rule 158 7 := cutRule 7 p59 w119
def f346 : ℕ := 0x3eee00000000000000effc
def s145 : List ℕ := [f185,f169,f170,f346]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w121 : Wide 70 3 s145 := viaSearch (by decide +kernel)
def r162 : Rule 158 7 := cutRule 7 p43 w121
def f347 : ℕ := 0x2db6d6dd99800000000000003fe38fffd9c
def f348 : ℕ := 0x3fffffd5ea000000000000003ffc0ffffe0
def s146 : List ℕ := [f132,f133,f134,f135,f347,f348]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w122 : Wide 96 5 s146 := viaSearch (by decide +kernel)
def r163 : Rule 158 7 := cutRule 7 p32 w122
def f349 : ℕ := 0x56230000c
def f350 : ℕ := 0xff773cffc
def s147 : List ℕ := [f47,f349,f48,f350]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w123 : Wide 18 4 s147 := viaSearch (by decide +kernel)
def r164 : Rule 158 7 := cutRule 7 p11 w123
def f351 : ℕ := 0x2b5ad6b5ad6bb579d466138cc600000000000000fffff0001f07ffffd1986e339c
def s148 : List ℕ := [f21,f57,f58,f23,f24,f25,f351]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b39 : Ban 158 8 s148 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(315637994,r157),(1610361022,r107),(545096531,r158),(1373324942,r96),(308060451,r157),(574543059,r159),(1068588961,r160),(917509718,r124),(2053321699,r96),(1934492834,r159),(23165843,r23),(1733566133,r58),(129335457,r157),(1472971803,r160),(1678444476,r124),(856112106,r161),(1421940110,r96),(599607740,r160),(234902934,r159),(603613394,r160),(686455107,r158),(667013327,r160),(234440611,r157),(1879541442,r160),(1474868463,r159),(1100798128,r96),(298120390,r162),(172840022,r96),(1080317553,r159),(1105844239,r157),(493783939,r157),(1896664526,r160),(844376055,r96),(315290947,r160),(1154485787,r159),(1638846016,r96),(1510263798,r92),(733195635,r96),(474679108,r159),(902289353,r152),(1188054642,r157),(290013953,r160),(840576457,r96),(1547090289,r96),(1025990463,r160),(1686561116,r162),(1234075650,r163),(1037518912,r159),(1648205533,r96),(1839416372,r160),(633027307,r124),(824238146,r161),(1226766213,r160),(1975677499,r18),(19404691,r160),(1900275452,r107),(137083472,r160),(1060134457,r17),(1251345296,r160),(80280615,r161),(1743129515,r17),(524874231,r164),(205081174,r112)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f352 : ℕ := 0x581c
def f353 : ℕ := 0x4232713
def f354 : ℕ := 0x3fb419fe0
def s149 : List ℕ := [f352,f290,f353,f354]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w124 : Wide 17 3 s149 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p83 : Weak 158 17 := relaxed (pick [14,15,25,29,35,42,43,45,52,53,54,57,58,78,83,93,103] (by decide) (by decide) (by decide))
def r165 : Rule 158 7 := cutRule 7 p83 w124
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w125 : Wide 11 2 s85 := viaSearch (by decide +kernel)
def r166 : Rule 158 7 := cutRule 7 p62 w125
def f355 : ℕ := 0x228300f
def s150 : List ℕ := [f355,f93,f48,f49]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w126 : Wide 18 3 s150 := viaSearch (by decide +kernel)
def r167 : Rule 158 7 := cutRule 7 p21 w126
def r168 : Rule 158 7 := cutRule 7 p72 w124
def r169 : Rule 158 7 := cutRule 7 p60 w125
def f356 : ℕ := 0xc01c
def f357 : ℕ := 0x249b5c1c7d860
def f358 : ℕ := 0x249b5c1ffffe0
def f359 : ℕ := 0x2dbbfdc3fc7ec
def f360 : ℕ := 0x36df7ebf8fb94
def s151 : List ℕ := [f356,f357,f358,f359,f360]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w127 : Wide 25 4 s151 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p84 : Weak 158 25 := signedPick 23 [23,24,33,34,37,42,45,48,49,50,51,52,54,56,57,58,90,92,93,95,97,98,100,102,103] (by decide) (by decide) (by decide)
def r170 : Rule 158 7 := cutRule 7 p84 w127
def f361 : ℕ := 0xa5294a5294a20308466138cc600000000000000000000001f00000011986e339c
def s152 : List ℕ := [f21,f57,f58,f361,f23,f24,f25]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b40 : Ban 158 8 s152 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1197047488,r165),(344286869,r108),(1426506025,r166),(107250789,r112),(1189469945,r165),(1455952553,r167),(1949998455,r168),(1798919212,r125),(787247546,r112),(668418681,r167),(904575337,r19),(467491980,r59),(952139227,r168),(2073894677,r125),(999031363,r169),(2039491120,r112),(277361600,r167),(334669500,r108),(610858078,r24),(206897650,r168),(412370323,r125),(1737521600,r169),(155865957,r112),(1481017234,r168),(1116312428,r167),(1485022888,r168),(1548422821,r168),(1723831139,r17),(648967825,r168),(1679127845,r17),(891848815,r168),(208794310,r167),(1982207622,r143),(1179529884,r167),(1054249516,r112),(1961727047,r167),(1987253733,r165),(1375193433,r165),(630590373,r168),(1196700441,r168),(372771863,r112),(244189645,r92),(1614605129,r112),(1356088602,r167),(163625429,r165),(1783698847,r19),(2069464136,r165),(1471155327,r96),(524874231,r164),(1593403733,r170)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f362 : ℕ := 0x5305a20
def f363 : ℕ := 0x5307fe0
def f364 : ℕ := 0x5f739ec
def f365 : ℕ := 0x3f7aeed4
def s153 : List ℕ := [f118,f362,f363,f364,f365]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w128 : Wide 15 5 s153 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p85 : Weak 158 15 := signedPick 5 [5,6,29,30,34,38,42,43,44,48,51,57,85,90,95] (by decide) (by decide) (by decide)
def r171 : Rule 158 8 := cutRule 8 p85 w128
def f366 : ℕ := 0x6f2e73
def s154 : List ℕ := [f90,f72,f73,f366,f91]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w129 : Wide 12 4 s154 := viaSearch (by decide +kernel)
def r172 : Rule 158 7 := cutRule 7 p20 w129
def f367 : ℕ := 0x4abfffffffffffff313f
def f368 : ℕ := 0x9400000000000000a630
def f369 : ℕ := 0x3e6300000000000000000c
def f370 : ℕ := 0x3f017fffffffffffff9e0f
def s155 : List ℕ := [f367,f368,f369,f370]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w130 : Wide 70 4 s155 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p86 : Weak 158 70 := relaxed (pick [0,1,5,6,38,39,42,43,44,48,49,51,60,85,90,95,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r173 : Rule 158 7 := cutRule 7 p86 w130
def f371 : ℕ := 0x246180071c
def f372 : ℕ := 0x91960fffe0
def f373 : ℕ := 0xdbb6de3b0c
def s156 : List ℕ := [f371,f372,f334,f373]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w131 : Wide 20 4 s156 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p87 : Weak 158 20 := signedPick 12 [12,13,17,18,19,38,40,41,45,46,47,52,54,55,84,86,88,99,101,103] (by decide) (by decide) (by decide)
def r174 : Rule 158 7 := cutRule 7 p87 w131
def f374 : ℕ := 0x44255fffffffffffff8038fc02733f
def f375 : ℕ := 0x249248461318000000000000001c700238dcc
def f376 : ℕ := 0x924922a9a00000000000000007ff803fff000
def s157 : List ℕ := [f374,f375,f338,f339,f376]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w132 : Wide 101 5 s157 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p88 : Weak 158 101 := relaxed (pick [0,1,5,6,10,11,14,15,16,20,23,24,38,39,40,42,43,44,48,49,50,51,52,53,54,56,60,62,63,70,72,73,75,77,78,85,87,88,90,92,93,95,97,98,100,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r175 : Rule 158 7 := cutRule 7 p88 w132
def f377 : ℕ := 0x2108421084219549500000000000000000000000ffc1f0000007f703c000000000
def s158 : List ℕ := [f21,f57,f58,f23,f24,f377,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b41 : Ban 158 8 s158 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1000124870,r92),(307273566,r50),(1560413338,r43),(1068208324,r50),(490561976,r88),(464162827,r51),(1150176719,r92),(1931839795,r51),(1352373154,r172),(1028609864,r92),(1927383454,r173),(534598798,r89),(1751730946,r50),(1896335098,r12),(1435772742,r17),(138159307,r174),(1321439927,r175)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w133 : Wide 18 5 s37 := viaSearch (by decide +kernel)
def r176 : Rule 158 8 := cutRule 8 p26 w133
def f378 : ℕ := 0x250cc630
def f379 : ℕ := 0xff98c0000c
def s159 : List ℕ := [f378,f226,f227,f379]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w134 : Wide 20 4 s159 := viaSearch (by decide +kernel)
def r177 : Rule 158 7 := cutRule 7 p56 w134
def f380 : ℕ := 0x249248461318000000000000001c700278dcc
def f381 : ℕ := 0x6db6dc601c0bfffffffffffff8e001e380e0f
def f382 : ℕ := 0x92492299a00000000000000007ff803fff000
def s160 : List ℕ := [f374,f380,f338,f381,f382]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w135 : Wide 101 5 s160 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p89 : Weak 158 101 := relaxed (pick [0,1,5,6,10,11,14,15,16,20,23,24,38,39,40,42,43,44,45,48,49,51,52,53,54,56,60,62,63,70,72,73,75,77,78,85,87,88,90,92,93,95,97,98,100,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r178 : Rule 158 7 := cutRule 7 p89 w135
def f383 : ℕ := 0x2108421084219549500000000000000000000000f83ff0000006f0ffc000000000
def s161 : List ℕ := [f21,f57,f58,f23,f24,f383,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b42 : Ban 158 8 s161 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(867390806,r2),(174539502,r50),(1427679274,r35),(935474260,r50),(357827912,r92),(464162827,r51),(1842529905,r92),(1931839795,r51),(739376622,r28),(497731682,r28),(895875800,r92),(2137709066,r92),(287901355,r150),(1233934835,r177),(1747174640,r89),(1618996882,r50),(1763601034,r2),(1303038678,r17),(276234990,r96),(591366783,r178),(1547090289,r96)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f384 : ℕ := 0x484abfffffffffffff0cf1333f
def f385 : ℕ := 0x940000000000000000fc0ff000
def f386 : ℕ := 0x15566263000000000000003309cdcc
def f387 : ℕ := 0x2aa801940000000000000003c00ff0
def f388 : ℕ := 0x3fff03817fffffffffffffc03e0e0f
def s162 : List ℕ := [f384,f385,f386,f387,f388]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w136 : Wide 86 5 s162 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p90 : Weak 158 86 := relaxed (pick [0,1,5,6,10,11,14,15,16,20,23,24,38,39,42,43,44,48,49,51,60,62,70,72,75,77,85,87,90,92,95,97,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r179 : Rule 158 8 := cutRule 8 p90 w136
def f389 : ℕ := 0x4abfffffffffffff0fc1ff
def f390 : ℕ := 0x2a000000000000000fc3f80
def f391 : ℕ := 0x2aac1400000000000000c33870
def f392 : ℕ := 0x3ff9117fffffffffffff30e64f
def s163 : List ℕ := [f389,f390,f391,f392]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w137 : Wide 78 4 s163 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p91 : Weak 158 78 := relaxed (pick [0,1,5,6,10,11,20,38,39,48,49,52,53,56,60,62,70,72,85,87,95,97,100,102,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r180 : Rule 158 7 := cutRule 7 p91 w137
def f393 : ℕ := 0xaaab92b2800000000000001e66763230
def s164 : List ℕ := [f0,f1,f3,f393,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w138 : Wide 91 5 s164 := viaSearch (by decide +kernel)
def r181 : Rule 158 7 := cutRule 7 p0 w138
def f394 : ℕ := 0x39ce739ce739fd495e003c950000000000000000fffff07fe007fffff801fffc00
def s165 : List ℕ := [f21,f57,f58,f23,f24,f25,f131,f394]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b43 : Ban 158 8 s165 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(682958385,r45),(2137590728,r45),(1243246853,r45),(751041839,r113),(173395491,r113),(719651156,r91),(711443379,r113),(103468934,r14),(1561836217,r92),(1434564461,r113),(1579168613,r14),(1118606257,r80),(1234075650,r163),(467877229,r51),(170742475,r45),(1017042394,r51),(2069911628,r28),(25717045,r180),(509357735,r89),(1555376294,r181)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f395 : ℕ := 0x6f23f3
def s166 : List ℕ := [f90,f72,f73,f395,f91]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w139 : Wide 12 4 s166 := viaSearch (by decide +kernel)
def r182 : Rule 158 7 := cutRule 7 p20 w139
def f396 : ℕ := 0x15000000000000000c1e0
def f397 : ℕ := 0xfe0a00000000000000201c
def s167 : List ℕ := [f157,f396,f159,f397]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w140 : Wide 71 4 s167 := viaSearch (by decide +kernel)
def r183 : Rule 158 7 := cutRule 7 p39 w140
def f398 : ℕ := 0x24c18e0f1c
def f399 : ℕ := 0x91360fffe0
def f400 : ℕ := 0xb5ffafcfe0
def f401 : ℕ := 0xdb76de370c
def s168 : List ℕ := [f398,f399,f400,f401]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w141 : Wide 20 4 s168 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p92 : Weak 158 20 := signedPick 12 [12,13,17,18,19,38,40,41,42,45,46,47,54,55,84,86,88,89,91,93] (by decide) (by decide) (by decide)
def r184 : Rule 158 7 := cutRule 7 p92 w141
def f402 : ℕ := 0x249248861318000000000000001c700478dcc
def f403 : ℕ := 0x492496000ca000000000000007007e3800ff0
def f404 : ℕ := 0x6db6dca01c0bfffffffffffff8e001e780e0f
def f405 : ℕ := 0x92492159a00000000000000007ff803fff000
def s169 : List ℕ := [f374,f402,f403,f404,f405]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w142 : Wide 101 5 s169 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p93 : Weak 158 101 := relaxed (pick [0,1,5,6,10,11,14,15,16,20,23,24,38,39,40,42,43,44,45,48,49,50,51,52,53,56,60,62,63,70,72,73,75,77,78,85,87,88,90,92,93,95,97,98,100,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r185 : Rule 158 7 := cutRule 7 p93 w142
def f406 : ℕ := 0x210842108421954950000000000000000000000007fff00000060fffc000000000
def s170 : List ℕ := [f21,f57,f58,f23,f24,f406,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b44 : Ban 158 8 s170 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(347166846,r92),(1801799189,r88),(907455314,r46),(415250300,r92),(1985087599,r88),(464162827,r51),(528442973,r92),(1931839795,r51),(739376622,r28),(367387742,r182),(497731682,r28),(534598798,r89),(375651840,r92),(1565474339,r183),(1098772922,r88),(1243377074,r15),(782814718,r81),(200303201,r184),(1493285390,r185)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f407 : ℕ := 0x96255fffffffffffff819e04f33f
def f408 : ℕ := 0x92800000000000000007f81fff000
def f409 : ℕ := 0x55544c531800000000000000660272dcc
def f410 : ℕ := 0xaaab000ca000000000000006079c00ff0
def f411 : ℕ := 0xfffe601c0bfffffffffffff9807380e0f
def s171 : List ℕ := [f407,f408,f409,f410,f411]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w143 : Wide 93 5 s171 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p94 : Weak 158 93 := relaxed (pick [0,1,5,6,10,11,14,15,16,20,23,24,26,30,38,39,42,43,44,48,49,51,52,53,56,60,62,70,72,75,77,85,87,90,92,95,97,100,102,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r186 : Rule 158 7 := cutRule 7 p94 w143
def f412 : ℕ := 0x2484abfffffffffffff033c09a33f
def f413 : ℕ := 0x24a00000000000000000ff03fff000
def f414 : ℕ := 0x1555131e63000000000000000cc04e7dcc
def f415 : ℕ := 0x2aaac0019400000000000000c0f3800ff0
def f416 : ℕ := 0x3fff9813817fffffffffffff300e704e0f
def s172 : List ℕ := [f412,f413,f414,f415,f416]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w144 : Wide 94 5 s172 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p95 : Weak 158 94 := relaxed (pick [0,1,5,6,10,11,14,15,16,20,23,24,29,30,34,38,39,42,43,44,48,49,51,52,53,56,60,62,70,72,75,77,85,87,90,92,95,97,100,102,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r187 : Rule 158 7 := cutRule 7 p95 w144
def f417 : ℕ := 0x2404abfffffffffffff033c09833f
def f418 : ℕ := 0x1555130a63000000000000000cc04e2dcc
def f419 : ℕ := 0x2aaac0119400000000000000c0f3804ff0
def f420 : ℕ := 0x3fff981f817fffffffffffff300e707e0f
def s173 : List ℕ := [f417,f413,f418,f419,f420]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w145 : Wide 94 5 s173 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p96 : Weak 158 94 := relaxed (pick [0,1,5,6,10,11,14,15,16,20,23,24,33,34,37,38,39,42,43,44,48,49,51,52,53,56,60,62,70,72,75,77,85,87,90,92,95,97,100,102,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r188 : Rule 158 7 := cutRule 7 p96 w145
def f421 : ℕ := 0x53fc
def f422 : ℕ := 0x1294f
def f423 : ℕ := 0xe0483
def f424 : ℕ := 0xf8ef3
def s174 : List ℕ := [f421,f422,f423,f424]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w146 : Wide 10 3 s174 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p97 : Weak 158 10 := relaxed (pick [5,6,10,11,14,15,16,24,70,75] (by decide) (by decide) (by decide))
def r189 : Rule 158 7 := cutRule 7 p97 w146
def f425 : ℕ := 0x90255fffffffffffff819e04c33f
def f426 : ℕ := 0x55544c131800000000000000660270dcc
def f427 : ℕ := 0xaaab006ca000000000000006079c03ff0
def f428 : ℕ := 0xfffe605c0bfffffffffffff9807382e0f
def s175 : List ℕ := [f425,f408,f426,f427,f428]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w147 : Wide 93 5 s175 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p98 : Weak 158 93 := relaxed (pick [0,1,5,6,10,11,14,15,16,20,23,24,35,37,38,39,42,43,44,48,49,51,52,53,56,60,62,70,72,75,77,85,87,90,92,95,97,100,102,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r190 : Rule 158 7 := cutRule 7 p98 w147
def f429 : ℕ := 0xa81e0
def s176 : List ℕ := [f78,f79,f429,f251]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w148 : Wide 10 4 s176 := viaSearch (by decide +kernel)
def r191 : Rule 158 7 := cutRule 7 p54 w148
def s177 : List ℕ := [f21,f57,f58,f23,f24,f252,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b45 : Ban 158 8 s177 := viaRules (ws := [s90,s104,s110,s119]) (consBan b18 (consBan b26 (consBan b30 (consBan b34 (nilBan _ _)))))
  (dictionary [(1940489370,r51),(702270939,r2),(1087728751,r2),(22464260,r1),(850692671,r97),(1932911827,r30),(731717467,r186),(51910788,r51),(545956690,r51),(1558324816,r50),(394877447,r50),(878518137,r98),(1530689428,r97),(2014330118,r51),(2091667242,r187),(1411860563,r51),(1259069821,r51),(1648017219,r29),(2131657909,r31),(1210933862,r33),(1694574552,r51),(1754186833,r30),(950339532,r51),(1013286514,r50),(1155812205,r50),(333479835,r98),(899307839,r97),(76975469,r129),(392077342,r188),(1859754310,r51),(80981123,r30),(163822836,r1),(144381056,r129),(1859291987,r30),(1207892034,r51),(898203723,r98),(1356909171,r189),(93912619,r51),(952236192,r51),(455294798,r88),(578165857,r88),(1922971766,r36),(1797691398,r97),(995013660,r36),(1237491961,r190),(557685282,r51),(583211968,r30),(1986617980,r85),(433199026,r36),(2118635315,r30),(1374032255,r51),(809564252,r105),(1685993056,r36),(202682626,r51),(751073009,r36),(321743784,r90),(1545143279,r36),(1940142323,r129),(761787825,r191),(42872675,r97),(81981146,r92),(1283780164,r30),(1706723886,r29),(1477015866,r92),(319433584,r30),(2110249769,r51),(1340320604,r92),(1873383939,r51),(1933783243,r92),(392845834,r128),(841295998,r92),(1735150264,r129),(812096588,r36),(638733863,r113),(679373676,r92),(1124957114,r36),(546343218,r51),(1839334827,r50),(1324618883,r110),(825506762,r114),(1171798701,r51),(2093667462,r30),(1983938979,r2),(1484826858,r1),(127416159,r16),(1775787685,r21),(1640028407,r51),(1537855094,r51),(1637896063,r114),(1186332189,r51),(1523376623,r17),(1024264502,r142),(1453704363,r98),(2058667212,r114),(1295681119,r17),(796568998,r51),(248238783,r36),(2030075917,r142),(1731247834,r51),(1766450473,r142),(1815896222,r96),(1316784101,r51),(59698162,r112),(1708069688,r142),(318665123,r51)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f430 : ℕ := 0x1111110450b22b003c3c011e2ccfc
def f431 : ℕ := 0x5555558504c34143c003e1e130f0f
def f432 : ℕ := 0x666666d00701d43c003c3e01c0ff0
def f433 : ℕ := 0x8888882aa800003fffc03fffff000
def f434 : ℕ := 0xaaaaaa626228b2800003d8988a3cf
def s178 : List ℕ := [f430,f431,f432,f433,f434]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w149 : Wide 58 5 s178 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p99 : Weak 158 58 := relaxed (pick [2,3,7,8,14,15,17,18,21,22,23,24,25,27,29,31,33,34,35,36,37,42,43,45,46,48,49,50,51,52,53,54,55,56,65,66,67,68,75,76,77,78,80,81,82,83,90,91,92,93,95,96,97,98,100,101,102,103] (by decide) (by decide) (by decide))
def r192 : Rule 158 7 := cutRule 7 p99 w149
def f435 : ℕ := 0x1181c
def f436 : ℕ := 0x14c1aa20
def f437 : ℕ := 0x14c1efe0
def f438 : ℕ := 0x17dd79ec
def f439 : ℕ := 0x3fdebded4
def s179 : List ℕ := [f435,f436,f437,f438,f439]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w150 : Wide 17 4 s179 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p100 : Weak 158 17 := signedPick 5 [5,6,15,16,24,38,42,43,44,48,51,52,75,85,90,95,100] (by decide) (by decide) (by decide)
def r193 : Rule 158 7 := cutRule 7 p100 w150
def f440 : ℕ := 0x381c
def f441 : ℕ := 0xa60cfa20
def f442 : ℕ := 0xa60fcfe0
def f443 : ℕ := 0x55bee3f9ec
def f444 : ℕ := 0xaaef5f3ed4
def s180 : List ℕ := [f440,f441,f442,f443,f444]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w151 : Wide 20 4 s180 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p101 : Weak 158 20 := signedPick 23 [23,24,33,34,37,42,48,49,51,52,56,57,80,82,90,92,95,97,100,102] (by decide) (by decide) (by decide)
def r194 : Rule 158 7 := cutRule 7 p101 w151
def s181 : List ℕ := [f21,f57,f58,f23,f24,f25,f252,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b46 : Ban 158 8 s181 := viaRules (ws := [s91,s107,s111,s123]) (consBan b19 (consBan b27 (consBan b31 (consBan b35 (nilBan _ _)))))
  (dictionary [(573688721,r2),(959146533,r2),(722110453,r92),(603135249,r92),(1429742598,r50),(266295229,r50),(1402107210,r92),(1963085024,r92),(1519435001,r29),(1082351644,r57),(884704296,r50),(1027229987,r50),(770725621,r92),(263495124,r92),(326712580,r88),(449583639,r88),(1669109180,r92),(1108909743,r92),(1311660195,r192),(1183077977,r92),(631853516,r51),(761787825,r191),(633205607,r92),(81981146,r92),(2099530484,r51),(907067311,r30),(379657082,r29),(1299021640,r92),(665422371,r30),(702289487,r51),(868165435,r193),(1028609864,r92),(222562160,r51),(1914865329,r92),(189361968,r128),(895875800,r92),(503358192,r129),(1163928845,r36),(711443379,r113),(375651840,r92),(1374776288,r36),(1116089475,r28),(1539033197,r29),(1309325177,r92),(151742895,r28),(1942559080,r89),(1172629915,r92),(1766092554,r89),(225155145,r194),(673605309,r92),(1567459575,r89),(644405899,r36),(511682987,r92),(1931839795,r51),(1710752609,r50),(1196036665,r110),(1855356761,r2),(2146317588,r16),(1394794405,r17),(1167098901,r17),(972443255,r142),(1638846016,r96),(1139733895,r51),(1510263798,r92),(372771863,r112),(2021143389,r142),(244189645,r92),(35735497,r51),(1648205533,r96),(1687314004,r92),(2039491120,r112),(2078599591,r92),(150974434,r127)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s182 : List ℕ := [f77,f78,f79,f429]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w152 : Wide 10 3 s182 := viaSearch (by decide +kernel)
def r195 : Rule 158 7 := cutRule 7 p17 w152
def r196 : Rule 158 7 := cutRule 7 p54 w152
def s183 : List ℕ := [f77,f429,f128,f129]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w153 : Wide 10 3 s183 := viaSearch (by decide +kernel)
def r197 : Rule 158 7 := cutRule 7 p63 w153
def f445 : ℕ := 0x2108421084219549500000000000000000000000fffff0000001ffffc000000000
def s184 : List ℕ := [f21,f57,f58,f23,f24,f445,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b47 : Ban 158 8 s184 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1034838989,r195),(182078370,r2),(1264297526,r1),(2092525937,r97),(1027261446,r195),(1293744054,r51),(1787789956,r196),(1636710713,r50),(625039047,r97),(506210182,r51),(742366838,r29),(305283481,r33),(44689151,r196),(250161824,r50),(1575313101,r98),(2141141105,r97),(1318808735,r196),(954103929,r51),(1322814389,r196),(1386214322,r196),(46585811,r51),(1819999123,r88),(1017321385,r36),(892041017,r97),(1799518548,r51),(1825045234,r195),(1212984934,r195),(468381874,r196),(1034491942,r196),(761787825,r191),(948523056,r97),(81981146,r92),(1416930,r195),(1510703624,r29),(1907255637,r195),(1944122753,r196),(1009214948,r196),(1788176484,r196),(933684446,r50),(418968502,r110),(266148320,r197),(1078288598,r2),(1369249425,r16),(617726242,r17),(118614121,r196),(390030738,r17),(196017844,r96),(256784420,r112)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f446 : ℕ := 0x1212afffffffffffffc0cf01333f
def f447 : ℕ := 0x92500000000000000003fc07ff000
def f448 : ℕ := 0x155509898c0000000000000033009cdcc
def f449 : ℕ := 0x2aaa6006500000000000000303c700ff0
def f450 : ℕ := 0x3fff4c0e05fffffffffffffcc034e0e0f
def s185 : List ℕ := [f446,f447,f448,f449,f450]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w154 : Wide 92 5 s185 := viaSearch (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def p102 : Weak 158 92 := relaxed (pick [0,1,5,6,10,11,14,15,16,20,23,24,38,39,42,43,44,48,49,51,52,53,56,57,60,62,70,72,75,77,85,87,90,92,95,97,100,102,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157] (by decide) (by decide) (by decide))
def r198 : Rule 158 7 := cutRule 7 p102 w154
def s186 : List ℕ := [f21,f57,f58,f23,f24,f445,f25,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b48 : Ban 158 8 s186 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(53496152,r2),(1508128495,r50),(613784620,r29),(121579606,r50),(1691416905,r88),(633205607,r92),(819940838,r92),(739376622,r28),(101179669,r29),(497731682,r28),(534598798,r89),(1747174640,r89),(1384954450,r113),(1873686782,r51),(761787825,r191),(81981146,r92),(1873686782,r198),(1193880103,r51),(1416930,r195),(1621490348,r29),(393371259,r92),(1907255637,r195),(1944122753,r196),(1009214948,r196),(2137709066,r92),(464162827,r51),(805102228,r50),(290386284,r110),(949706380,r2),(489144024,r17),(261448520,r17),(933977536,r96),(994744112,r112),(733195635,r96),(1614605129,r112)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s187 : List ℕ := [f57,f131,f58,f23,f24,f21,f25]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b0 : Ban 158 9 s187 := viaRules (ws := [s17,s21,s42,s44,s50,s69,s72,s74,s83,s92,s96,s99,s100,s108,s109,s112,s114,s128,s131,s139,s143,s148,s152,s158,s161,s165,s170,s177,s181,s184,s186]) (consBan b1 (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b20 (consBan b21 (consBan b23 (consBan b24 (consBan b28 (consBan b29 (consBan b32 (consBan b33 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (consBan b40 (consBan b41 (consBan b42 (consBan b43 (consBan b44 (consBan b45 (consBan b46 (consBan b47 (consBan b48 (nilBan _ _))))))))))))))))))))))))))))))))
  (dictionary [(1925976773,r0),(1317136169,r20),(1608096996,r25),(1472337718,r26),(1091379132,r27),(1526883863,r60),(1586496144,r27),(1370164405,r0),(1414941136,r61),(1018641500,r26),(1470205374,r62),(2060774081,r63),(2143615794,r20),(2124174014,r63),(1691601298,r27),(856573813,r0),(1286013674,r61),(628878309,r63),(1890976523,r62),(1040201345,r63),(730513034,r61),(1189218482,r63),(2073705577,r60),(415521279,r27),(265508337,r86),(1950944626,r27),(80548094,r0),(2128648550,r87),(1563557145,r26),(1862385228,r0),(1206341566,r60),(641873563,r87),(1518302367,r86),(34991937,r60),(583382320,r63),(1377452590,r86),(1772451634,r63),(1772798681,r0),(2002257218,r20),(2031703746,r0),(1765221138,r27),(378652529,r0),(1172532017,r61),(1004108012,r0),(657816073,r62),(378266001,r0),(710827448,r61),(1244169874,r0),(1846639429,r60),(782648843,r0),(165789146,r61),(1692063621,r0),(2056768427,r63),(784545503,r0),(1755281077,r87),(389994593,r0),(827322971,r86),(739376622,r27),(497731682,r27),(804752566,r0),(972043206,r26),(2015528455,r26),(1853452700,r0),(534598798,r60),(700474746,r171),(54871471,r60),(1747174640,r63),(21671279,r176),(335667503,r63),(996238156,r179),(1207085599,r86),(464162827,r0),(1931839795,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
theorem cert6 : Ban 158 9 bank := b0
end PEqualNP.Outside.L_meta_14342.B1

namespace PEqualNP.Outside.L_meta_14342
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def target (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def witness : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.and,[4,8]⟩,⟨.or,[5,7]⟩,⟨.or,[0,2]⟩,⟨.and,[10,11]⟩,⟨.or,[1,3]⟩,⟨.or,[4,13]⟩,⟨.and,[6,14]⟩,⟨.or,[4,5]⟩,⟨.and,[7,16]⟩,⟨.or,[9,12]⟩,⟨.or,[15,18]⟩,⟨.or,[17,19]⟩],20⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem shaped : Monotone2 witness := by simp [witness,Monotone2]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem cost : witness.size=13 := rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem valid : ∀ x,witness.eval (List.ofFn x)=target x := by decide +kernel
def inputs : List ℕ := [0x42108421084004940aa04952904444444444444444444442004944293301254a4fffffffffffffc0007c00f83e0024f055064f9ce000001fe000001fe01fe218024f21c998193e73,0x56b5ad6b5ad6627188cc27198c11515151515151515151408627180802a89c663000000000000000000000007c13138c4661b8ce700000000001fe0001fe00063138c0601fe6e339c,0xc6318c6318c046c02f086c1f004c4c4c4c4c4c4c4c4c4c60046c060e3c21b07c00000000000000000f801f0000023f017863f0f800001fe000001fe00000038023f03871e18fc3e0,0x1fffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffffffc000000000000000000000000000000000000000,0x294a5294a52885001300d80052828282828282828282828008500100480360014afffffffffffffc1f0000007fe43c009807c00ffe01fe0001fe000001fffe4043c00c07e01f003ff,0x318c6318c630d0001c00792a000b0b0b0b0b0b0b0b0b0b200d00019d0001e4a80000000000000003e00001ff8007c000e007fff001fe0000000001fffe0001807c000ff8001fffc00,0x20000000000000000000000000000000000000002c2c2c2c2c2c2c2c2c2c3f700000f7b5540000010000000000000000003e0000180000fff800000000000001fffe00000001ff80000fffffe000000,0x4210842108432a92a0000000003030303030303030303019d2a92a00000000000000000000000003ffffc000001fffff0000000001fffffffe000000000001fffffff000000000000]
def v : ℕ := 0x1fffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffffffc000000000000000000000000000000000000000
def bank0 : List ℕ := [0x88888888888888888888840092885266024a94a000001fe000001fe01fe218024f21c998193e73,0x22a2a2a2a2a2a2a2a2a2810c4e3010055138cc600000000001fe0001fe00063138c0601fe6e339c,0x98989898989898989898c008d80c1c784360f800001fe000001fe00000038023f03871e18fc3e0,0x50505050505050505050010a002009006c0029601fe0001fe000001fffe4043c00c07e01f003ff,0x16161616161616161616401a00033a0003c95001fe0000000001fffe0001807c000ff8001fffc00,0x585858585858585858587ee00001ef6aa800000000000001fffe00000001ff80000fffffe000000,0x6060606060606060606033a55254000000000001fffffffe000000000001fffffff000000000000]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem wide0 : Wide 158 9 bank0 := widen (by decide +kernel) B0.cert6
def rr0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157]
def ix0 := rr0 ++ rr0.map (317+·)
def base0 : ℕ := 474
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def pr0 : Weak 317 158 := signedPick base0 rr0 (by decide) (by decide) (by decide)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem images0 : ∀ a∈inputs, pr0.f a=0 ∨ pr0.f a∈bank0 := by decide +kernel
def bank1 : List ℕ := [0x210842108420024a055024a94bfffffffffffff0001f003e0f80093c154193e73,0x2b5ad6b5ad6b3138c466138cc600000000000000000000001f04c4e311986e339c,0x6318c6318c6023601784360f800000000000000003e007c000008fc05e18fc3e0,0x14a5294a5294428009806c00297fffffffffffff07c000001ff90f002601f003ff,0x18c6318c631868000e003c950000000000000000f800007fe001f0003801fffc00,0xf80000600003ffe000000,0x2108421084219549500000000000000000000000fffff0000007ffffc000000000]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem wide1 : Wide 158 9 bank1 := widen (by decide +kernel) B1.cert6
def rr1 : List ℕ := [158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315]
def ix1 := rr1 ++ rr1.map (317+·)
def base1 : ℕ := 632
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
def pr1 : Weak 317 158 := signedPick base1 rr1 (by decide) (by decide) (by decide)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem images1 : ∀ a∈inputs, pr1.f a=0 ∨ pr1.f a∈bank1 := by decide +kernel
def posBits : ℕ := 0x48191919191919191919191919191919191919191919191919191919191919191919191919191919191919191919191919191919191919a8a8a8a8a898989898988c8c8c8c8c898989898948484848482c2c2c2c2c29292929291a1a1a1a1a1919191919cac8b8aaaaa8a89c9a98988f8e8e8d8c8c8b8b8989786a685c584f4e4d4c4b4a49483c3c3a3a392f2e2e2d2c2c2b2b29291f1e1e1d1d1b1a1a191911a0a0a0a0a0a0a0a0909090909090909084848484848484848181818181818181505050505050505042424242424242422424242424242424212121212121212112121212121212121111111111111111e0e0d0c5c4c4c2c2c1c1b0a2a2a0a09492909087868685848483838181707065646462626161555454515050474746464343424234343232312726262524242323212117161615151312121111
def negBits : ℕ := 0x400808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808088a382a1c0f8a382a1c0f8a382a1c0f8a382a1c0f8a382a1c0f8a382a1c0f8a382a1c0f8a382a1c0f8a382a1c0f8a88382a8a28881c8a18880f0e8a0d0c880b8a0988382a281c180f0e0d0c0b0a09081c382a38380f0e2a0d0c280b2a09280f0e1c0d1c0b0a18091800c082604530221407c082604530221407c082604530221407c082604530221407c082604530221407c082604530221407c082604530221407c082604530221407c082604530221407c08260453022140760c0c04544c082c041c030228220801482108007068205048003820180306045446022604160451444411040074506440341024014302230300706220504200322012007061405140302100110
def sample (bank : ℕ) (i : Fin 317) (j : Fin 8) := bank.testBit (8*i.val+j.val)

def seeds : List Wire := inputs.map (fun a => (false,a))
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem listed : ∀ i : Fin 317, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (317+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem labels : ∀ i : Fin 317, target (sample posBits i)=true ∧ target (sample negBits i)=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem essential : ∀ a∈inputs, ∃ i : Fin 317, ∀ b∈inputs, b.testBit i.val≠b.testBit (317+i.val) → b=a := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem initial {k S} (live : Live 317 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 8 C=target) :
    ∃ k≤C.gates.countP counted, Live 317 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 8 → Bool) : C.eval (List.ofFn x)=target x := congrFun eq x
  have good : Good 317 out.2 := by
    intro i hi same
    let j : Fin 317 := ⟨i,hi⟩
    have diff : read i out=read (317+i) out := by simp [read,same]
    have p := ev i;have n := ev (317+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩


def pr : Bool → Weak 317 158 | false => pr0 | true => pr1
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem killed (d a b : ℕ) (hd : d<4) (hit : v=a ∨ v=b) :
    ∃ t, (pr t).f (combine d a b)=0 := by
  rcases hit with rfl|rfl
  · obtain ⟨s,c,h⟩ := forced d hd true
    cases s with
    | false => exact ⟨false,forcedLeft (is:=ix0) (s:=false) (c:=c) hd (by decide) (by decide) (by simpa using h)⟩
    | true => exact ⟨true,forcedLeft (is:=ix1) (s:=true) (c:=c) hd (by decide) (by decide) (by simpa using h)⟩
  · obtain ⟨s,c,h⟩ := forced d hd false
    cases s with
    | false => exact ⟨false,forcedRight (is:=ix0) (s:=false) (c:=c) hd (by decide) (by decide) (by simpa using h)⟩
    | true => exact ⟨true,forcedRight (is:=ix1) (s:=true) (c:=c) hd (by decide) (by decide) (by simpa using h)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem eleven {k : ℕ} (live : Live 317 k inputs.toFinset) : 12≤k := by
  obtain ⟨t,j,T,lim,ok,sub⟩ := doubleElim pr v killed (by decide +kernel) live (by decide)
  by_contra! small
  have project {w : List ℕ} (im : ∀ a∈inputs, (pr t).f a=0 ∨ (pr t).f a∈w) : Possible 158 9 w := by
    refine ⟨j,T,by omega,ok,?_⟩
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (sub x hx)
    exact (im _ (List.mem_toFinset.mp ha)).resolve_left (liveNonzero ok _ hx)
  cases t
  · exact wide0 (project images0)
  · exact wide1 (project images1)

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
theorem noSaving (s : ℕ) (h : HasCircuitSize 8 target s) :
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
end PEqualNP.Outside.L_meta_14342

theorem PEqualNP.Outside.L_meta_14342 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fan _ ev
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates,o⟩
  obtain ⟨D, shaped, cost, valid⟩ := PEqualNP.Outside.L_meta_14342.noSaving gates.length ⟨C,fan,le_rfl,ev⟩
  exact ⟨D.gates,D.output,shaped,cost,valid⟩
