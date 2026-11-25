import PEqualNP.Defs

-- The signed live-wire calculus follows L-meta-10532 and L-meta-12325.

namespace PEqualNP.Outside.L_meta_15765

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

end PEqualNP.Outside.L_meta_15765

namespace PEqualNP.Outside.L_meta_15765

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

end PEqualNP.Outside.L_meta_15765

namespace PEqualNP.Outside.L_meta_15765
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







end PEqualNP.Outside.L_meta_15765

namespace PEqualNP.Outside.L_meta_15765

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
end PEqualNP.Outside.L_meta_15765

namespace PEqualNP.Outside.L_meta_15765

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
end PEqualNP.Outside.L_meta_15765

namespace PEqualNP.Outside.L_meta_15765
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

end PEqualNP.Outside.L_meta_15765

namespace PEqualNP.Outside.L_meta_15765

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
end PEqualNP.Outside.L_meta_15765

namespace PEqualNP.Outside.L_meta_15765.B0
def bank : List ℕ := [0x2f0c2b3f8e3f,0x976598cff3cc,0x140b2d5f0ffff,0x1fa0760ff03f0,0x1fdd800fffc00]
def f0 : ℕ := 0x38847c46
def f1 : ℕ := 0x3d0d1f878
def f2 : ℕ := 0x3ed01ff80
def f3 : ℕ := 0x3fdd67800
def s0 : List ℕ := [f0,f1,f2,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w0 : Wide 17 4 s0 := viaSearch (by decide +kernel)
def p0 : Weak 25 17 := signedPick 0 [0,2,3,4,6,7,9,10,12,13,15,16,17,18,19,20,22] (by decide) (by decide) (by decide)
def r0 : Rule 25 5 := cutRule 5 p0 w0
def f4 : ℕ := 0xc6e86c
def f5 : ℕ := 0xd18f1c
def f6 : ℕ := 0xec0fe0
def f7 : ℕ := 0xfd9700
def s1 : List ℕ := [f4,f5,f6,f7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w1 : Wide 12 3 s1 := viaSearch (by decide +kernel)
def p1 : Weak 25 12 := signedPick 2 [2,3,6,7,9,12,13,15,16,17,19,22] (by decide) (by decide) (by decide)
def r1 : Rule 25 5 := cutRule 5 p1 w1
def f8 : ℕ := 0x1614
def f9 : ℕ := 0x48cc
def f10 : ℕ := 0xa0f0
def f11 : ℕ := 0xe9c0
def s2 : List ℕ := [f8,f9,f10,f11]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w2 : Wide 8 3 s2 := viaSearch (by decide +kernel)
def p2 : Weak 25 8 := signedPick 2 [2,3,6,9,12,15,16,17] (by decide) (by decide) (by decide)
def r2 : Rule 25 5 := cutRule 5 p2 w2
def f12 : ℕ := 0x2d0c
def f13 : ℕ := 0x3070
def f14 : ℕ := 0xe8fc
def f15 : ℕ := 0xfa70
def s3 : List ℕ := [f12,f13,f14,f15]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w3 : Wide 8 3 s3 := viaSearch (by decide +kernel)
def p3 : Weak 25 8 := signedPick 6 [6,7,12,13,16,17,19,22] (by decide) (by decide) (by decide)
def r3 : Rule 25 5 := cutRule 5 p3 w3
def f16 : ℕ := 0x704080f820c
def f17 : ℕ := 0x2f0c2b3f8e3f
def f18 : ℕ := 0x976598cff3cc
def f19 : ℕ := 0x140b2d5f0ffff
def f20 : ℕ := 0x1fa0760ff03f0
def f21 : ℕ := 0x1fdd800fffc00
def s4 : List ℕ := [f16,f17,f18,f19,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b1 : Ban 25 6 s4 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1377571113,r0),(1606777486,r1),(391193597,r2),(555939522,r3)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w4 : Wide 12 4 s1 := viaSearch (by decide +kernel)
def r4 : Rule 25 6 := cutRule 6 p1 w4
def f22 : ℕ := 0x186761dc
def f23 : ℕ := 0x20ab63ff
def f24 : ℕ := 0x3a1c7c3c
def f25 : ℕ := 0x3dc07fc0
def s5 : List ℕ := [f22,f23,f24,f25]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w5 : Wide 15 4 s5 := viaSearch (by decide +kernel)
def p4 : Weak 25 15 := relaxed (pick [2,3,6,7,8,9,12,13,14,15,16,17,19,22,23] (by decide) (by decide) (by decide))
def r5 : Rule 25 5 := cutRule 5 p4 w5
def f26 : ℕ := 0x906190c071c0
def s6 : List ℕ := [f17,f26,f18,f19,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b2 : Ban 25 6 s6 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(966152932,r1),(435355014,r1),(185756412,r5),(414962785,r1),(2062798615,r3),(285191022,r3),(569241400,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w6 : Wide 8 4 s3 := viaSearch (by decide +kernel)
def r6 : Rule 25 6 := cutRule 6 p3 w6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w7 : Wide 8 4 s2 := viaSearch (by decide +kernel)
def r7 : Rule 25 6 := cutRule 6 p2 w7
def f27 : ℕ := 0x140b2d4c071c0
def s7 : List ℕ := [f17,f18,f27,f19,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b3 : Ban 25 6 s7 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(592716151,r2),(894936545,r1),(1532000697,r3)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f28 : ℕ := 0x2f0c2a0f0000
def s8 : List ℕ := [f28,f17,f18,f19,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b4 : Ban 25 6 s8 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1532000697,r3),(253122955,r1),(1616868842,r1),(592716151,r2)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f29 : ℕ := 0x10a61ef6
def f30 : ℕ := 0x3c7bee0e70
def f31 : ℕ := 0x3d0747e0f8
def f32 : ℕ := 0x3ee807ff00
def s9 : List ℕ := [f29,f30,f31,f32]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w8 : Wide 19 4 s9 := viaSearch (by decide +kernel)
def p5 : Weak 25 19 := signedPick 1 [1,2,3,5,6,7,8,9,11,12,13,14,15,16,17,19,21,22,23] (by decide) (by decide) (by decide)
def r8 : Rule 25 5 := cutRule 5 p5 w8
def f33 : ℕ := 0x2d0fc
def f34 : ℕ := 0x7d4e0
def f35 : ℕ := 0xa380c
def f36 : ℕ := 0xf03e0
def s10 : List ℕ := [f33,f34,f35,f36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w9 : Wide 10 3 s10 := viaSearch (by decide +kernel)
def p6 : Weak 25 10 := signedPick 10 [10,11,13,14,15,17,18,19,20,21] (by decide) (by decide) (by decide)
def r9 : Rule 25 5 := cutRule 5 p6 w9
def p7 : Weak 25 10 := signedPick 4 [4,5,7,8,9,16,18,19,20,21] (by decide) (by decide) (by decide)
def r10 : Rule 25 5 := cutRule 5 p7 w9
def f37 : ℕ := 0x2090c0f3cc
def s11 : List ℕ := [f37,f17,f18,f19,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b5 : Ban 25 6 s11 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1878923411,r2),(524566979,r1),(318050999,r1),(1325484717,r3),(8604720,r8),(237811093,r1),(1381683105,r9),(324886248,r10)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f38 : ℕ := 0xf22f93
def f39 : ℕ := 0x37b2f00
def f40 : ℕ := 0x3a31f1c
def f41 : ℕ := 0x3d81fe0
def s12 : List ℕ := [f38,f39,f40,f41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w10 : Wide 13 4 s12 := viaSearch (by decide +kernel)
def p8 : Weak 25 13 := relaxed (pick [2,3,6,7,9,12,13,15,16,17,18,19,22] (by decide) (by decide) (by decide))
def r11 : Rule 25 5 := cutRule 5 p8 w10
def f42 : ℕ := 0x9745080f0000
def s13 : List ℕ := [f17,f42,f18,f19,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b6 : Ban 25 6 s13 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(569241400,r2),(444327073,r1),(1199786813,r1),(1050820346,r11),(1280026719,r1)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f43 : ℕ := 0x313c
def f44 : ℕ := 0xf230
def f45 : ℕ := 0x30d04
def f46 : ℕ := 0x3c1f0
def s14 : List ℕ := [f43,f44,f45,f46]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w11 : Wide 9 3 s14 := viaSearch (by decide +kernel)
def p9 : Weak 25 9 := signedPick 4 [4,5,8,9,16,18,20,21,23] (by decide) (by decide) (by decide)
def r12 : Rule 25 5 := cutRule 5 p9 w11
def f47 : ℕ := 0x507c
def f48 : ℕ := 0x12d9e
def f49 : ℕ := 0x17e1c
def s15 : List ℕ := [f47,f48,f49]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w12 : Wide 9 3 s15 := viaSearch (by decide +kernel)
def p10 : Weak 25 9 := signedPick 10 [10,15,17,18,19,20,21,22,23] (by decide) (by decide) (by decide)
def r13 : Rule 25 5 := cutRule 5 p10 w12
def f50 : ℕ := 0x110710
def s16 : List ℕ := [f50,f4,f5,f6,f7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w13 : Wide 12 4 s16 := viaSearch (by decide +kernel)
def r14 : Rule 25 5 := cutRule 5 p1 w13
def f51 : ℕ := 0x2a04203f0230
def s17 : List ℕ := [f51,f17,f18,f19,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b7 : Ban 25 6 s17 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1236277897,r1),(1341635049,r12),(984157433,r13),(237564611,r14),(284703356,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f52 : ℕ := 0xa3c
def f53 : ℕ := 0xb4c
def f54 : ℕ := 0xeb0
def s18 : List ℕ := [f52,f53,f54]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w14 : Wide 6 3 s18 := viaSearch (by decide +kernel)
def p11 : Weak 25 6 := signedPick 18 [18,19,20,21,22,23] (by decide) (by decide) (by decide)
def r15 : Rule 25 6 := cutRule 6 p11 w14
def f55 : ℕ := 0xa3a0c
def f56 : ℕ := 0xad2fc
def f57 : ℕ := 0xfd4e0
def s19 : List ℕ := [f55,f56,f36,f57]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w15 : Wide 10 3 s19 := viaSearch (by decide +kernel)
def p12 : Weak 25 10 := signedPick 10 [10,11,13,14,15,17,18,19,20,22] (by decide) (by decide) (by decide)
def r16 : Rule 25 5 := cutRule 5 p12 w15
def f58 : ℕ := 0x4e
def f59 : ℕ := 0xd8
def s20 : List ℕ := [f58,f59]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w16 : Wide 4 2 s20 := viaSearch (by decide +kernel)
def p13 : Weak 25 4 := signedPick 9 [9,12,13,16] (by decide) (by decide) (by decide)
def r17 : Rule 25 5 := cutRule 5 p13 w16
def f60 : ℕ := 0x66
def s21 : List ℕ := [f58,f60,f59]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w17 : Wide 4 2 s21 := viaSearch (by decide +kernel)
def r18 : Rule 25 5 := cutRule 5 p13 w17
def f61 : ℕ := 0x1a18
def f62 : ℕ := 0x44c4
def f63 : ℕ := 0xb0f8
def f64 : ℕ := 0xf5c0
def s22 : List ℕ := [f61,f62,f63,f64]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w18 : Wide 8 3 s22 := viaSearch (by decide +kernel)
def p14 : Weak 25 8 := signedPick 2 [2,3,9,12,13,15,16,17] (by decide) (by decide) (by decide)
def r19 : Rule 25 5 := cutRule 5 p14 w18
def f65 : ℕ := 0xc0f0
def f66 : ℕ := 0xc486
def f67 : ℕ := 0xd796
def f68 : ℕ := 0xec60
def s23 : List ℕ := [f65,f66,f67,f68]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w19 : Wide 8 3 s23 := viaSearch (by decide +kernel)
def p15 : Weak 25 8 := signedPick 3 [3,6,7,9,12,16,19,22] (by decide) (by decide) (by decide)
def r20 : Rule 25 5 := cutRule 5 p15 w19
def f69 : ℕ := 0x143c
def f70 : ℕ := 0x5d0c
def f71 : ℕ := 0xb630
def s24 : List ℕ := [f69,f70,f71]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w20 : Wide 8 3 s24 := viaSearch (by decide +kernel)
def p16 : Weak 25 8 := signedPick 7 [7,8,18,19,20,21,22,23] (by decide) (by decide) (by decide)
def r21 : Rule 25 5 := cutRule 5 p16 w20
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w21 : Wide 6 2 s18 := viaSearch (by decide +kernel)
def r22 : Rule 25 5 := cutRule 5 p11 w21
def f72 : ℕ := 0x2c07e0
def s25 : List ℕ := [f72,f4,f5,f7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w22 : Wide 12 4 s25 := viaSearch (by decide +kernel)
def r23 : Rule 25 5 := cutRule 5 p1 w22
def f73 : ℕ := 0x1d00340c001c0
def s26 : List ℕ := [f17,f18,f19,f73,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b8 : Ban 25 6 s26 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(101501363,r16),(1944772225,r17),(1183101283,r18),(137283204,r19),(160641358,r20),(184421949,r19),(1788695581,r21),(958418990,r22),(2091928167,r21),(1126682173,r23)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f74 : ℕ := 0x66060
def s27 : List ℕ := [f74,f4,f5,f6,f7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w23 : Wide 12 4 s27 := viaSearch (by decide +kernel)
def r24 : Rule 25 5 := cutRule 5 p1 w23
def f75 : ℕ := 0x1918
def f76 : ℕ := 0x2464
def f77 : ℕ := 0xd0f8
def f78 : ℕ := 0xf660
def s28 : List ℕ := [f75,f76,f77,f78]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w24 : Wide 8 3 s28 := viaSearch (by decide +kernel)
def p17 : Weak 25 8 := signedPick 6 [6,7,9,12,13,16,19,22] (by decide) (by decide) (by decide)
def r25 : Rule 25 5 := cutRule 5 p17 w24
def f79 : ℕ := 0x286690330
def f80 : ℕ := 0x290c17870
def s29 : List ℕ := [f79,f80,f2,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w25 : Wide 17 4 s29 := viaSearch (by decide +kernel)
def r26 : Rule 25 5 := cutRule 5 p0 w25
def f81 : ℕ := 0xeac0
def s30 : List ℕ := [f9,f70,f81]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w26 : Wide 8 3 s30 := viaSearch (by decide +kernel)
def p18 : Weak 25 8 := signedPick 10 [10,11,18,19,20,21,22,23] (by decide) (by decide) (by decide)
def r27 : Rule 25 5 := cutRule 5 p18 w26
def f82 : ℕ := 0x8e0c
def f83 : ℕ := 0xa0e0
def f84 : ℕ := 0xd8fc
def f85 : ℕ := 0xf9e0
def s31 : List ℕ := [f82,f83,f84,f85]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w27 : Wide 8 3 s31 := viaSearch (by decide +kernel)
def p19 : Weak 25 8 := signedPick 2 [2,3,12,13,15,16,17,19] (by decide) (by decide) (by decide)
def r28 : Rule 25 5 := cutRule 5 p19 w27
def f86 : ℕ := 0xecee
def s32 : List ℕ := [f65,f67,f68,f86]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w28 : Wide 8 3 s32 := viaSearch (by decide +kernel)
def r29 : Rule 25 5 := cutRule 5 p15 w28
def f87 : ℕ := 0xfd9f1c
def s33 : List ℕ := [f4,f5,f6,f7,f87]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w29 : Wide 12 4 s33 := viaSearch (by decide +kernel)
def r30 : Rule 25 5 := cutRule 5 p1 w29
def f88 : ℕ := 0xd18700
def s34 : List ℕ := [f4,f88,f5,f6,f7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w30 : Wide 12 4 s34 := viaSearch (by decide +kernel)
def r31 : Rule 25 5 := cutRule 5 p1 w30
def f89 : ℕ := 0x4d0ff
def f90 : ℕ := 0x3231f1c
def s35 : List ℕ := [f89,f38,f90,f41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w31 : Wide 13 4 s35 := viaSearch (by decide +kernel)
def r32 : Rule 25 5 := cutRule 5 p8 w31
def f91 : ℕ := 0x280780
def s36 : List ℕ := [f91,f4,f5,f6,f7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w32 : Wide 12 4 s36 := viaSearch (by decide +kernel)
def r33 : Rule 25 5 := cutRule 5 p1 w32
def f92 : ℕ := 0xe0c
def f93 : ℕ := 0x58dc
def f94 : ℕ := 0xf9c0
def s37 : List ℕ := [f92,f93,f83,f94]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w33 : Wide 8 3 s37 := viaSearch (by decide +kernel)
def p20 : Weak 25 8 := signedPick 2 [2,3,6,7,9,15,16,17] (by decide) (by decide) (by decide)
def r34 : Rule 25 5 := cutRule 5 p20 w33
def f95 : ℕ := 0x480ce0
def f96 : ℕ := 0x4b4cfc
def f97 : ℕ := 0x5f50e0
def f98 : ℕ := 0xe8ec0c
def s38 : List ℕ := [f95,f96,f97,f98]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w34 : Wide 12 3 s38 := viaSearch (by decide +kernel)
def p21 : Weak 25 12 := signedPick 10 [10,11,13,14,15,17,18,19,20,21,22,23] (by decide) (by decide) (by decide)
def r35 : Rule 25 5 := cutRule 5 p21 w34
def f99 : ℕ := 0x920500cf03c0
def f100 : ℕ := 0x954000cff000
def s39 : List ℕ := [f17,f99,f100,f19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b10 : Ban 25 5 s39 := viaRules (ws := []) (nilBan _ _)
  (dictionary [])
  (by decide) (by decide +kernel) (by decide +kernel)
def r36 : Rule 25 5 := cutRule 5 p1 w4
def f101 : ℕ := 0x15ab1fff
def f102 : ℕ := 0x1c856f23f
def f103 : ℕ := 0x68a01e3c0
def f104 : ℕ := 0x76001fc00
def s40 : List ℕ := [f101,f102,f103,f104]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w35 : Wide 18 4 s40 := viaSearch (by decide +kernel)
def p22 : Weak 25 18 := relaxed (pick [0,1,2,3,4,5,6,7,8,9,12,13,15,16,17,19,22,24] (by decide) (by decide) (by decide))
def r37 : Rule 25 5 := cutRule 5 p22 w35
def f105 : ℕ := 0xb8fc
def f106 : ℕ := 0xc0e0
def s41 : List ℕ := [f82,f105,f106,f85]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w36 : Wide 8 3 s41 := viaSearch (by decide +kernel)
def p23 : Weak 25 8 := signedPick 2 [2,3,6,7,9,16,17,19] (by decide) (by decide) (by decide)
def r38 : Rule 25 5 := cutRule 5 p23 w36
def f107 : ℕ := 0xec0700
def s42 : List ℕ := [f4,f5,f107,f6,f7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w37 : Wide 12 4 s42 := viaSearch (by decide +kernel)
def r39 : Rule 25 5 := cutRule 5 p1 w37
def s43 : List ℕ := [f17,f99,f18,f19,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b9 : Ban 25 6 s43 := viaRules (ws := [s39]) (consBan b10 (nilBan _ _))
  (dictionary [(201089102,r14),(353440403,r24),(2119058153,r19),(1879013543,r25),(1570375765,r26),(1799582138,r1),(1248391991,r1),(2087295127,r27),(748744174,r3),(1956943275,r2),(598426582,r28),(1691479286,r29),(97375947,r30),(752761122,r31),(1808554197,r1),(1659587730,r32),(1888794103,r1),(742595376,r33),(185877849,r34),(1632291853,r35),(639250349,r35),(368321032,r35),(1245416487,r36),(387798553,r37),(925888326,r36),(640838618,r38),(1562303859,r35),(1174553874,r39)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r40 : Rule 25 5 := cutRule 5 p11 w14
def f108 : ℕ := 0x5c7e
def f109 : ℕ := 0x1219c
def s44 : List ℕ := [f108,f109,f49]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w38 : Wide 9 3 s44 := viaSearch (by decide +kernel)
def p24 : Weak 25 9 := signedPick 13 [13,15,17,18,19,20,21,22,23] (by decide) (by decide) (by decide)
def r41 : Rule 25 5 := cutRule 5 p24 w38
def s45 : List ℕ := [f17,f99,f18,f19,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b11 : Ban 25 6 s45 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1381683105,r9),(327252162,r29),(237564611,r14),(137283204,r19),(157938982,r25),(2062443265,r40),(1279186742,r1),(863482130,r41),(1092688503,r1),(2087295127,r27),(1048703566,r28),(1282962704,r29),(343545738,r31),(1422506872,r22),(247260331,r40),(1281812538,r40),(802137264,r35),(633256961,r40),(1055249878,r35)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w39 : Wide 8 2 s30 := viaSearch (by decide +kernel)
def r42 : Rule 25 5 := cutRule 5 p18 w39
def f110 : ℕ := 0x5609800f00c
def s46 : List ℕ := [f110,f17,f18,f19,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b12 : Ban 25 6 s46 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(527461681,r27),(1981534265,r36),(2087295127,r27),(708995441,r1),(1115021078,r27),(754814163,r42),(1805641124,r3),(866356578,r2),(717967500,r1),(798207406,r1),(1990929028,r42),(154829790,r36),(471717162,r42)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w40 : Wide 8 4 s31 := viaSearch (by decide +kernel)
def r43 : Rule 25 6 := cutRule 6 p19 w40
def f111 : ℕ := 0x28f8
def f112 : ℕ := 0x2d18
def f113 : ℕ := 0x3a60
def s47 : List ℕ := [f111,f112,f113]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w41 : Wide 7 3 s47 := viaSearch (by decide +kernel)
def p25 : Weak 25 7 := signedPick 17 [17,18,19,20,21,22,23] (by decide) (by decide) (by decide)
def r44 : Rule 25 5 := cutRule 5 p25 w41
def f114 : ℕ := 0xba05200f0000
def s48 : List ℕ := [f17,f18,f114,f19,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b13 : Ban 25 6 s48 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1198716687,r1),(2066219227,r22),(343545738,r31),(2115124425,r44),(390684483,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p26 : Weak 25 9 := signedPick 10 [10,11,14,15,17,18,20,21,23] (by decide) (by decide) (by decide)
def r45 : Rule 25 5 := cutRule 5 p26 w11
def p27 : Weak 25 9 := signedPick 4 [4,9,16,18,19,20,21,22,23] (by decide) (by decide) (by decide)
def r46 : Rule 25 5 := cutRule 5 p27 w12
def f115 : ℕ := 0x2d08003f8c00
def s49 : List ℕ := [f115,f17,f18,f19,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b14 : Ban 25 6 s49 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(136920972,r1),(746101483,r45),(742595376,r33),(397312169,r46),(789734121,r33)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p28 : Weak 25 10 := signedPick 4 [4,5,7,8,9,16,18,19,20,22] (by decide) (by decide) (by decide)
def r47 : Rule 25 5 := cutRule 5 p28 w15
def p29 : Weak 25 8 := signedPick 13 [13,14,18,19,20,21,22,23] (by decide) (by decide) (by decide)
def r48 : Rule 25 5 := cutRule 5 p29 w20
def f116 : ℕ := 0x11871c
def s50 : List ℕ := [f116,f4,f6,f7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w42 : Wide 12 4 s50 := viaSearch (by decide +kernel)
def r49 : Rule 25 5 := cutRule 5 p1 w42
def f117 : ℕ := 0xd4
def f118 : ℕ := 0xe8
def s51 : List ℕ := [f117,f118]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w43 : Wide 4 2 s51 := viaSearch (by decide +kernel)
def p30 : Weak 25 4 := signedPick 6 [6,7,15,17] (by decide) (by decide) (by decide)
def r50 : Rule 25 5 := cutRule 5 p30 w43
def f119 : ℕ := 0xcc
def s52 : List ℕ := [f119,f117,f118]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w44 : Wide 4 2 s52 := viaSearch (by decide +kernel)
def r51 : Rule 25 5 := cutRule 5 p30 w44
def f120 : ℕ := 0xc0e2
def f121 : ℕ := 0xc88c
def f122 : ℕ := 0xcf8e
def f123 : ℕ := 0xf860
def s53 : List ℕ := [f120,f121,f122,f123]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w45 : Wide 8 3 s53 := viaSearch (by decide +kernel)
def p31 : Weak 25 8 := signedPick 3 [3,6,12,13,15,17,19,22] (by decide) (by decide) (by decide)
def r52 : Rule 25 5 := cutRule 5 p31 w45
def f124 : ℕ := 0x1d0d000c07000
def s54 : List ℕ := [f17,f18,f19,f124,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b15 : Ban 25 6 s54 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(913203133,r47),(185877849,r34),(796136334,r48),(857463142,r22),(1147963565,r48),(664656109,r49),(64355846,r50),(1450168551,r51),(233016594,r34),(1380180557,r52)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f125 : ℕ := 0x2e00c
def s55 : List ℕ := [f125,f4,f5,f6,f7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w46 : Wide 12 4 s55 := viaSearch (by decide +kernel)
def r53 : Rule 25 5 := cutRule 5 p1 w46
def f126 : ℕ := 0x3d1c
def f127 : ℕ := 0xf8fc
def f128 : ℕ := 0xfa60
def s56 : List ℕ := [f13,f126,f127,f128]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w47 : Wide 8 3 s56 := viaSearch (by decide +kernel)
def p32 : Weak 25 8 := signedPick 6 [6,7,12,13,15,17,19,22] (by decide) (by decide) (by decide)
def r54 : Rule 25 5 := cutRule 5 p32 w47
def f129 : ℕ := 0x2ac017f00
def s57 : List ℕ := [f79,f129,f1,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w48 : Wide 17 4 s57 := viaSearch (by decide +kernel)
def r55 : Rule 25 5 := cutRule 5 p0 w48
def p33 : Weak 25 8 := signedPick 4 [4,5,18,19,20,21,22,23] (by decide) (by decide) (by decide)
def r56 : Rule 25 5 := cutRule 5 p33 w26
def s58 : List ℕ := [f120,f122,f123,f127]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w49 : Wide 8 3 s58 := viaSearch (by decide +kernel)
def r57 : Rule 25 5 := cutRule 5 p31 w49
def f130 : ℕ := 0xfd9fe0
def s59 : List ℕ := [f4,f5,f6,f7,f130]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w50 : Wide 12 4 s59 := viaSearch (by decide +kernel)
def r58 : Rule 25 5 := cutRule 5 p1 w50
def f131 : ℕ := 0x3581fe0
def s60 : List ℕ := [f89,f38,f131,f40]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w51 : Wide 13 4 s60 := viaSearch (by decide +kernel)
def r59 : Rule 25 5 := cutRule 5 p8 w51
def p34 : Weak 25 12 := signedPick 4 [4,5,7,8,9,16,18,19,20,21,22,23] (by decide) (by decide) (by decide)
def r60 : Rule 25 5 := cutRule 5 p34 w34
def f132 : ℕ := 0x2c6b1fff
def f133 : ℕ := 0x1c316f1cf
def f134 : ℕ := 0x68181e070
def f135 : ℕ := 0x75001fe00
def s61 : List ℕ := [f132,f133,f134,f135]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w52 : Wide 18 4 s61 := viaSearch (by decide +kernel)
def p35 : Weak 25 18 := relaxed (pick [0,1,2,3,6,7,9,10,11,12,13,14,15,16,17,19,22,24] (by decide) (by decide) (by decide))
def r61 : Rule 25 5 := cutRule 5 p35 w52
def s62 : List ℕ := [f17,f100,f18,f19,f20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b16 : Ban 25 6 s62 := viaRules (ws := [s39]) (consBan b10 (nilBan _ _))
  (dictionary [(195904159,r33),(1511267628,r53),(612555265,r34),(1011867942,r54),(1617514510,r55),(1846720883,r1),(1295530736,r1),(2061027754,r56),(795882919,r3),(2004082020,r2),(1736252117,r38),(1862554299,r57),(2103332464,r58),(533385130,r39),(1855692942,r1),(1706726475,r59),(1935932848,r1),(284703356,r14),(184421949,r19),(205077727,r60),(356514609,r60),(981170823,r60),(1245416487,r36),(1097119114,r61),(154829790,r36),(1095842311,r28),(1330101449,r60),(390684483,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p36 : Weak 25 9 := signedPick 7 [7,9,16,18,19,20,21,22,23] (by decide) (by decide) (by decide)
def r62 : Rule 25 5 := cutRule 5 p36 w38
def s63 : List ℕ := [f17,f100,f18,f19,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b17 : Ban 25 6 s63 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(324886248,r10),(451188430,r57),(1092632387,r22),(247260331,r40),(789734121,r33),(233016594,r34),(1679430598,r54),(1400261449,r40),(664143671,r1),(63473886,r62),(292680259,r1),(2061027754,r56),(687977363,r38),(1609442604,r57),(1221692619,r39),(1328951283,r40),(849276009,r60),(680395706,r60),(1102388623,r40)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r63 : Rule 25 5 := cutRule 5 p33 w39
def f136 : ℕ := 0x225980003cc
def s64 : List ℕ := [f136,f17,f18,f19,f20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b18 : Ban 25 6 s64 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(819176644,r56),(2028673010,r36),(2061027754,r56),(1527192722,r1),(2078608838,r56),(520462579,r63),(476354758,r3),(1684553859,r2),(1536164781,r1),(1616404687,r1),(95931616,r63),(925888326,r36),(1010573288,r63)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w53 : Wide 8 4 s41 := viaSearch (by decide +kernel)
def r64 : Rule 25 6 := cutRule 6 p23 w53
def p37 : Weak 25 7 := signedPick 16 [16,18,19,20,21,22,23] (by decide) (by decide) (by decide)
def r65 : Rule 25 5 := cutRule 5 p37 w41
def f137 : ℕ := 0xbd48000f0000
def s65 : List ℕ := [f17,f18,f137,f19,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b19 : Ban 25 6 s65 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2017835899,r1),(198076735,r22),(1174553874,r39),(1221692619,r39),(1215660508,r65)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s66 : List ℕ := [f17,f18,f19,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b0 : Ban 25 7 s66 := viaRules (ws := [s4,s6,s7,s8,s11,s13,s17,s26,s43,s45,s46,s48,s49,s54,s62,s63,s64,s65]) (consBan b1 (consBan b2 (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (consBan b19 (nilBan _ _)))))))))))))))))))
  (dictionary [(435355014,r4),(2031648514,r4),(1532000697,r6),(592716151,r7),(444327073,r4),(524566979,r4),(2027782953,r15),(941195505,r15),(1875945026,r15),(2062443265,r4),(952274376,r15),(1831960089,r43),(2066219227,r15),(1438193959,r15),(44303525,r15),(268064729,r15),(1028798037,r15),(1400261449,r4),(878868258,r15),(1424095141,r64),(198076735,r15),(963602154,r15),(2065069061,r15),(1585393787,r15),(1416513484,r15),(1838506401,r15)])
  (by decide) (by decide +kernel) (by decide +kernel)
theorem cert6 : Ban 25 7 bank := b0
end PEqualNP.Outside.L_meta_15765.B0

namespace PEqualNP.Outside.L_meta_15765
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def target (x : Fin 6 → Bool) := Nat.testBit (4008242912 * 2 ^ 32 + 4007717600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[⟨.or,[2,5]⟩,⟨.or,[4,6]⟩,⟨.and,[1,7]⟩,⟨.or,[0,8]⟩,⟨.and,[5,8]⟩,⟨.and,[0,10]⟩,⟨.and,[4,11]⟩,⟨.or,[3,12]⟩,⟨.or,[2,13]⟩,⟨.and,[9,14]⟩],15⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem shaped : Monotone2 witness := by simp [witness,Monotone2]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem cost : witness.size=10 := rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem valid : ∀ x,witness.eval (List.ofFn x)=target x := by decide +kernel
def inputs : List ℕ := [0x85e18573f8e3f,0x12ecb30cff3cc,0x2000000,0x28165a9f0ffff,0x3f40ec0ff03f0,0x3fbb000fffc00]
def v : ℕ := 0x2000000
def bank0 : List ℕ := [0x2f0c2b3f8e3f,0x976598cff3cc,0x140b2d5f0ffff,0x1fa0760ff03f0,0x1fdd800fffc00]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem wide0 : Wide 25 7 bank0 := widen (by decide +kernel) B0.cert6
def rr0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]
def ix0 := rr0 ++ rr0.map (26+·)
def base0 : ℕ := 50
def pr0 : Weak 26 25 := signedPick base0 rr0 (by decide) (by decide) (by decide)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem images0 : ∀ a∈inputs, pr0.f a=0 ∨ pr0.f a∈bank0 := by decide +kernel
def posBits : ℕ := 0x149ebae79cf3cf3aeaaaaa696da69a6592cb249
def negBits : ℕ := 0x40e32e31cb18d38e888aa214d848a611283201
def sample (bank : ℕ) (i : Fin 26) (j : Fin 6) := bank.testBit (6*i.val+j.val)

def seeds : List Wire := inputs.map (fun a => (false,a))
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem listed : ∀ i : Fin 26, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (26+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem labels : ∀ i : Fin 26, target (sample posBits i)=true ∧ target (sample negBits i)=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem essential : ∀ a∈inputs, ∃ i : Fin 26, ∀ b∈inputs, b.testBit i.val≠b.testBit (26+i.val) → b=a := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem initial {k S} (live : Live 26 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 6 C=target) :
    ∃ k≤C.gates.countP counted, Live 26 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 6 → Bool) : C.eval (List.ofFn x)=target x := congrFun eq x
  have good : Good 26 out.2 := by
    intro i hi same
    let j : Fin 26 := ⟨i,hi⟩
    have diff : read i out=read (26+i) out := by simp [read,same]
    have p := ev i;have n := ev (26+i)
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
theorem noCheap : Ban 26 8 inputs :=
  viaWeakCut pr0 wide0 (by decide) images0 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem eleven {k : ℕ} (run : Live 26 k inputs.toFinset) : 9≤k := by
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
end PEqualNP.Outside.L_meta_15765

theorem PEqualNP.Outside.L_meta_15765 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008242912 * 2 ^ 32 + 4007717600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008242912 * 2 ^ 32 + 4007717600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_15765.noSaving
