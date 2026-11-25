import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12250.Support

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

def t0 := 0xc61bb98c7ff
def t1 := 0x16b6877fff0f
def t2 := 0x2b5b707ffff0
def t3 := 0x306c5de0f8ff
def t4 := 0x3d806eff00ff
def v0 := [t0,t1,t2,t3,t4]
def t5 := 0x601980c0ff
def v1 := [t5,t0,t1,t2,t3,t4]
def t6 := 0xc01a2180700
def v2 := [t5,t6,t1,t2,t3,t4]
def v3 := [t6,t0,t1,t2,t3,t4]
def t7 := 0x300c44603800
def v4 := [t5,t0,t1,t2,t7,t4]
def v5 := [t0,t1,t2,t7,t3,t4]
def t8 := 0x88000ff
def v6 := [t8,t0,t1,t2,t3,t4]
def t9 := 0x3de07fffc0ff
def v7 := [t0,t1,t2,t3,t4,t9]
def t10 := 0x601100c000
def v8 := [t10,t0,t1,t2,t3,t4]
def t11 := 0x3d80667f0000
def v9 := [t0,t1,t2,t3,t11,t4]
def t12 := 0x200100c00f
def v10 := [t12,t0,t1,t2,t3,t4]
def t13 := 0x16f69fffffff
def v11 := [t0,t1,t13,t2,t3,t4]
def t14 := 0x40188000f0
def v12 := [t14,t0,t1,t2,t3,t4]
def t15 := 0x1696867f3f00
def v13 := [t0,t15,t1,t2,t3,t4]
def t16 := 0x401000c0f0
def v14 := [t16,t0,t1,t2,t3,t4]
def t17 := 0x2b7b79ffffff
def v15 := [t0,t1,t2,t17,t3,t4]
def t18 := 0x200980000f
def v16 := [t18,t0,t1,t2,t3,t4]
def t19 := 0x2b1b607f3f00
def v17 := [t0,t1,t19,t2,t3,t4]
def t20 := 0x3c6dfff8ffff
def v18 := [t5,t1,t2,t20,t4]
def v19 := [t5,t0,t1,t2,t20,t4]
def v20 := [t5,t1,t2,t3,t20,t4]
def t21 := 0x3de1ffffc7ff
def v21 := [t5,t1,t2,t3,t4,t21]
def t22 := 0x619100c700
def v22 := [t5,t22,t1,t2,t3,t4]
def t23 := 0x4208318c70f
def v23 := [t5,t23,t1,t2,t3,t4]
def t24 := 0x129604673800
def v24 := [t5,t24,t1,t2,t3,t4]
def t25 := 0x8413018c7f0
def v25 := [t5,t25,t1,t2,t3,t4]
def t26 := 0x231a40673800
def v26 := [t5,t1,t26,t2,t3,t4]
def t27 := 0x3dec7ffff8ff
def v27 := [t5,t0,t1,t2,t4,t27]
def t28 := 0x6c1100f800
def v28 := [t5,t28,t0,t1,t2,t4]
def t29 := 0x10240560f80f
def v29 := [t5,t0,t29,t1,t2,t4]
def t30 := 0x692821f0700
def v30 := [t5,t30,t0,t1,t2,t4]
def t31 := 0x20485060f8f0
def v31 := [t5,t0,t1,t31,t2,t4]
def t32 := 0xb13201f0700
def v32 := [t5,t32,t0,t1,t2,t4]
def v33 := [t0,t1,t2,t3,t20,t4]
def v34 := [t6,t0,t1,t2,t20,t4]
def v35 := [t1,t2,t7,t3,t20,t4]
def t33 := 0xc002a9800ff
def v36 := [t33,t1,t2,t3,t20,t4]
def t34 := 0x318044670000
def v37 := [t1,t2,t3,t34,t20,t4]
def t35 := 0x30004ce000ff
def v38 := [t0,t1,t2,t35,t20,t4]
def t36 := 0xd80221f0000
def v39 := [t0,t36,t1,t2,t20,t4]
def t37 := 0x3c006ef800ff
def v40 := [t0,t1,t2,t3,t37,t4]
def t38 := 0x3dedffffffff
def v41 := [t0,t1,t2,t3,t4,t38]
def t39 := 0x6d9100ff00
def v42 := [t39,t0,t1,t2,t3,t4]
def t40 := 0x18000070000
def v43 := [t40,t0,t1,t2,t3,t4]
def t41 := 0x14248778ff0f
def v44 := [t0,t41,t1,t2,t3,t4]
def t42 := 0x3effffffffff
def v45 := [t0,t1,t2,t3,t4,t42]
def t43 := 0x2849788000f0
def v46 := [t0,t1,t43,t2,t3,t4]
def t44 := 0x29200070000
def v47 := [t44,t0,t1,t2,t3,t4]
def t45 := 0x28497078fff0
def v48 := [t0,t1,t45,t2,t3,t4]
def t46 := 0x3f7fffffffff
def v49 := [t0,t1,t2,t3,t4,t46]
def t47 := 0x14248f80000f
def v50 := [t0,t47,t1,t2,t3,t4]
def t48 := 0x31200070000
def v51 := [t48,t0,t1,t2,t3,t4]
def v52 := [t22,t0,t1,t2,t3,t4]
def v53 := [t22,t33,t1,t2,t3,t4]
def v54 := [t33,t0,t1,t2,t3,t4]
def t49 := 0x306ddde0ffff
def v55 := [t0,t1,t2,t49,t4]
def v56 := [t22,t0,t1,t2,t49,t4]
def v57 := [t0,t1,t2,t3,t49,t4]
def t50 := 0x180000700
def v58 := [t50,t0,t1,t2,t3,t4]
def t51 := 0x300c4ce038ff
def v59 := [t0,t1,t2,t51,t4]
def v60 := [t22,t0,t1,t2,t51,t4]
def v61 := [t0,t1,t2,t51,t3,t4]
def v62 := [t22,t0,t1,t2,t3,t21]
def v63 := [t0,t1,t2,t3,t4,t21]
def t52 := 0x208100c700
def v64 := [t52,t0,t1,t2,t3,t4]
def t53 := 0x16f7977fff0f
def v65 := [t0,t1,t53,t2,t3,t4]
def t54 := 0x4110000000
def v66 := [t54,t0,t1,t2,t3,t4]
def t55 := 0x1696067f380f
def v67 := [t0,t55,t1,t2,t3,t4]
def t56 := 0x411000c700
def v68 := [t56,t0,t1,t2,t3,t4]
def t57 := 0x2b7bf17ffff0
def v69 := [t0,t1,t2,t57,t3,t4]
def t58 := 0x2081000000
def v70 := [t58,t0,t1,t2,t3,t4]
def t59 := 0x2b1a607f38f0
def v71 := [t0,t1,t59,t2,t3,t4]
def v72 := [t22,t1,t2,t7,t3,t4]
def v73 := [t22,t1,t2,t3,t34]
def v74 := [t22,t0,t1,t2,t3,t34]
def v75 := [t22,t1,t2,t3,t34,t4]
def v76 := [t22,t0,t1,t2,t3,t27]
def v77 := [t22,t0,t36,t1,t2,t3]
def t60 := 0x1480067f000f
def v78 := [t22,t0,t60,t1,t2,t3]
def t61 := 0x2368100ff00
def v79 := [t22,t61,t0,t1,t2,t3]
def t62 := 0x2900607f00f0
def v80 := [t22,t0,t1,t62,t2,t3]
def t63 := 0x25b1000ff00
def v81 := [t22,t63,t0,t1,t2,t3]
def map31_2 : Projection 23 23 := pick [0,2,1,3,4,6,5,7,8,9,10,16,17,18,19,20,11,12,13,14,15,21,22] rfl (by decide +kernel) (by decide)
def map31_6 : Projection 23 23 := pick [0,3,1,2,4,7,5,6,11,12,13,16,17,18,21,22,8,9,10,14,15,19,20] rfl (by decide +kernel) (by decide)
def map31_8 : Projection 23 23 := pick [0,2,3,1,4,6,7,5,16,17,18,8,9,10,19,20,11,12,13,21,22,14,15] rfl (by decide +kernel) (by decide)
def v82 := [t0,t1,t2,t3,t34,t4]
def map31_10 : Projection 23 23 := pick [0,3,2,1,4,7,6,5,16,17,18,11,12,13,21,22,8,9,10,19,20,14,15] rfl (by decide +kernel) (by decide)
def v83 := [t23,t0,t1,t2,t3,t4]
def t64 := 0x841388000f0
def v84 := [t23,t64,t1,t2,t3,t4]
def v85 := [t64,t0,t1,t2,t3,t4]
def t65 := 0x346cdff8ffff
def v86 := [t0,t1,t2,t3,t65,t4]
def t66 := 0x40082180700
def v87 := [t66,t0,t1,t2,t3,t4]
def t67 := 0x304c5ce038f0
def v88 := [t0,t1,t2,t67,t3,t4]
def t68 := 0x4000218000f
def v89 := [t68,t0,t1,t2,t3,t4]
def t69 := 0x3da0efffc7ff
def v90 := [t0,t1,t2,t3,t4,t69]
def t70 := 0x39806ce700f0
def v91 := [t0,t1,t2,t3,t70,t4]
def v92 := [t23,t0,t24,t2,t3,t4]
def v93 := [t0,t24,t1,t2,t3,t4]
def t71 := 0x18c700
def v94 := [t71,t0,t1,t2,t3,t4]
def t72 := 0x2f7bf37fffff
def v95 := [t0,t1,t2,t72,t3,t4]
def t73 := 0x4208300000f
def v96 := [t73,t0,t1,t2,t3,t4]
def t74 := 0x2b5b706738f0
def v97 := [t0,t1,t74,t2,t3,t4]
def v98 := [t23,t1,t2,t7,t3,t4]
def v99 := [t23,t33,t1,t2,t3,t4]
def v100 := [t23,t1,t2,t3,t34,t4]
def t75 := 0x1ef7bfffffff
def v101 := [t23,t75,t2,t3,t4]
def v102 := [t23,t0,t75,t2,t3,t4]
def v103 := [t23,t1,t75,t2,t3,t4]
def v104 := [t23,t25,t1,t2,t3,t4]
def v105 := [t23,t1,t26,t2,t3,t4]
def t76 := 0x212007fff00
def v106 := [t76,t23,t0,t2,t3,t4]
def t77 := 0x2949700000f0
def v107 := [t23,t0,t77,t2,t3,t4]
def v108 := [t0,t1,t75,t2,t3,t4]
def v109 := [t64,t0,t75,t2,t3,t4]
def v110 := [t24,t1,t75,t2,t3,t4]
def t78 := 0x10641de0f8ff
def v111 := [t0,t78,t1,t2,t4]
def v112 := [t0,t78,t1,t2,t3,t4]
def v113 := [t0,t78,t1,t75,t2,t4]
def t79 := 0x200840000000
def v114 := [t0,t1,t79,t2,t3,t4]
def t80 := 0xe93a21f0700
def v115 := [t0,t80,t1,t2,t4]
def v116 := [t0,t80,t1,t2,t3,t4]
def v117 := [t0,t80,t1,t75,t2,t4]
def t81 := 0x1c802eff00ff
def v118 := [t0,t1,t81,t2,t3]
def v119 := [t0,t1,t81,t2,t3,t4]
def v120 := [t0,t1,t81,t75,t2,t3]
def t82 := 0x3ff7ffffffff
def v121 := [t0,t1,t2,t3,t4,t82]
def t83 := 0x210040000000
def v122 := [t0,t1,t83,t2,t3,t4]
def t84 := 0x2779100ff00
def v123 := [t84,t0,t1,t2,t3]
def v124 := [t84,t0,t1,t2,t3,t4]
def v125 := [t84,t0,t1,t75,t2,t3]
def t85 := 0xa53307ffff0
def v126 := [t85,t0,t1,t3,t4]
def v127 := [t85,t0,t1,t75,t3,t4]
def v128 := [t85,t0,t1,t2,t3,t4]
def t86 := 0x3fffffffffff
def v129 := [t0,t1,t2,t3,t4,t86]
def t87 := 0x14a48f80000f
def v130 := [t0,t87,t1,t3,t4]
def v131 := [t0,t87,t1,t75,t3,t4]
def v132 := [t0,t87,t1,t2,t3,t4]
def t88 := 0x210840000000
def v133 := [t0,t1,t88,t2,t3,t4]
def t89 := 0x4208b80000f
def v134 := [t89,t0,t1,t2,t3,t4]
def t90 := 0x250ff8
def t91 := 0x48b49f
def t92 := 0x8a58e7
def t93 := 0xd06f07
def v135 := [t90,t91,t92,t93]
def t94 := 0x81087
def v136 := [t94,t90,t91,t92,t93]
def t95 := 0xcafcff
def v137 := [t90,t91,t92,t95,t93]
def t96 := 0x40a418
def v138 := [t90,t96,t91,t92,t93]
def t97 := 0x824860
def v139 := [t90,t91,t97,t92,t93]
def t98 := 0x402407
def v140 := [t90,t98,t91,t92,t93]
def t99 := 0xd8ff9f
def v141 := [t90,t91,t92,t93,t99]
def t100 := 0x89098
def v142 := [t100,t90,t91,t92,t93]
def t101 := 0x904b00
def v143 := [t90,t91,t92,t101,t93]
def t102 := 0x498
def v144 := [t102,t90,t91,t92,t93]
def t103 := 0x6dbfff
def v145 := [t90,t91,t103,t92,t93]
def t104 := 0x48b007
def v146 := [t90,t104,t91,t92,t93]
def t105 := 0x250b60
def v147 := [t105,t90,t91,t92,t93]
def t106 := 0x804807
def v148 := [t90,t91,t106,t92,t93]
def t107 := 0xda7fe7
def v149 := [t90,t91,t92,t93,t107]
def t108 := 0xa10e0
def v150 := [t108,t90,t91,t92,t93]
def t109 := 0x502700
def v151 := [t90,t91,t109,t92,t93]
def t110 := 0x8e0
def v152 := [t110,t90,t91,t92,t93]
def t111 := 0xaf5fff
def v153 := [t90,t91,t92,t111,t93]
def t112 := 0x8a5007
def v154 := [t90,t91,t112,t92,t93]
def t113 := 0x250718
def v155 := [t113,t90,t91,t92,t93]
def t114 := 0xf00
def v156 := [t114,t90,t91,t92,t93]
def t115 := 0xf56fff
def v157 := [t90,t91,t92,t93,t115]
def t116 := 0xd06007
def v158 := [t90,t91,t92,t116,t93]
def t117 := 0x2500f8
def v159 := [t117,t90,t91,t92,t93]
def t118 := 0xffffff
def v160 := [t90,t91,t92,t93,t118]
def p31_2063 : Projection 23 12 := pick [5,6,7,9,10,12,13,15,17,18,20,22] rfl (by decide +kernel) (by decide)
def map31_1 : Projection 23 23 := pick [4,5,6,7,0,1,2,3,9,8,10,12,11,13,15,14,17,16,18,20,19,22,21] rfl (by decide +kernel) (by decide)
def v161 := [t61,t0,t1,t2,t3,t4]
def v162 := [t61,t33,t0,t1,t2,t3]
def t119 := 0xe77bb98ffff
def v163 := [t0,t119,t1,t2,t3,t4]
def t120 := 0xc413a9800ff
def v164 := [t120,t0,t1,t2,t3,t4]
def t121 := 0x21600003800
def v165 := [t121,t0,t1,t2,t3,t4]
def v166 := [t61,t0,t1,t2,t35,t3]
def v167 := [t28,t61,t0,t1,t2,t3]
def t122 := 0x240100f800
def v168 := [t122,t0,t1,t2,t3,t4]
def t123 := 0x327edde0ffff
def v169 := [t0,t1,t2,t3,t123,t4]
def t124 := 0x30485ce000ff
def v170 := [t0,t1,t2,t124,t3,t4]
def t125 := 0x21280000700
def v171 := [t125,t0,t1,t2,t3,t4]
def t126 := 0x3fb6efffffff
def v172 := [t0,t1,t2,t3,t4,t126]
def v173 := [t61,t0,t1,t2,t3,t126]
def v174 := [t61,t0,t60,t2,t3,t4]
def t127 := 0x2900688000f0
def v175 := [t61,t0,t127,t2,t3]
def v176 := [t61,t0,t127,t2,t3,t4]
def v177 := [t61,t0,t1,t127,t2,t3]
def v178 := [t61,t0,t1,t62,t2,t3]
def v179 := [t61,t63,t0,t1,t2,t3]
def v180 := [t0,t60,t1,t2,t3,t4]
def t128 := 0x2120000ff00
def v181 := [t128,t0,t1,t2,t3,t4]
def t129 := 0x2b7ff17ffff0
def v182 := [t0,t1,t2,t129,t3,t4]
def t130 := 0x2481000000
def v183 := [t130,t0,t1,t2,t3,t4]
def t131 := 0x2949707f00f0
def v184 := [t0,t1,t131,t2,t3,t4]
def v185 := [t25,t0,t1,t2,t3,t4]
def t132 := 0x2f7bfbffffff
def v186 := [t0,t1,t2,t132,t3,t4]
def v187 := [t0,t1,t26,t2,t3,t4]
def map31_7 : Projection 23 23 := pick [4,7,5,6,0,3,1,2,12,11,13,17,16,18,22,21,9,8,10,15,14,20,19] rfl (by decide +kernel) (by decide)
def map31_9 : Projection 23 23 := pick [4,6,7,5,0,2,3,1,17,16,18,9,8,10,20,19,12,11,13,22,21,15,14] rfl (by decide +kernel) (by decide)
def v188 := [t0,t1,t2,t35,t3,t4]
def v189 := [t0,t1,t2,t3,t4,t27]
def v190 := [t28,t0,t1,t2,t3,t4]
def map31_4 : Projection 23 23 := pick [0,1,3,2,4,5,7,6,11,12,13,8,9,10,14,15,16,17,18,21,22,19,20] rfl (by decide +kernel) (by decide)
def v191 := [t0,t36,t1,t2,t3,t4]
def v192 := [t0,t29,t1,t2,t3,t4]
def t133 := 0x36fedfffffff
def v193 := [t0,t1,t2,t3,t133,t4]
def t134 := 0x2048588000f0
def v194 := [t0,t1,t134,t2,t3,t4]
def map31_5 : Projection 23 23 := pick [4,5,7,6,0,1,3,2,12,11,13,9,8,10,15,14,17,16,18,22,21,20,19] rfl (by decide +kernel) (by decide)
def v195 := [t30,t0,t1,t2,t3,t4]
def v196 := [t0,t1,t31,t2,t3,t4]
def t135 := 0x3b7f7dffffff
def v197 := [t0,t1,t2,t3,t135,t4]
def t136 := 0x10240d80000f
def v198 := [t0,t136,t1,t2,t3,t4]
def v199 := [t32,t0,t1,t2,t3,t4]
def map31_3 : Projection 23 23 := pick [4,6,5,7,0,2,1,3,9,8,10,17,16,18,20,19,12,11,13,15,14,22,21] rfl (by decide +kernel) (by decide)
def v200 := [t0,t1,t127,t2,t3,t4]
def v201 := [t0,t1,t62,t2,t3,t4]
def t137 := 0x3fdb7effffff
def v202 := [t0,t1,t2,t3,t4,t137]
def t138 := 0x14800e80000f
def v203 := [t0,t138,t1,t2,t3,t4]
def v204 := [t63,t0,t1,t2,t3,t4]
def v205 := [t76,t0,t1,t2,t3,t4]
def t139 := 0xe73bbffffff
def v206 := [t0,t139,t1,t2,t3,t4]
def t140 := 0xc61bb8000ff
def v207 := [t140,t0,t1,t2,t3,t4]
def t141 := 0x21200673800
def v208 := [t141,t0,t1,t2,t3,t4]
def v209 := [t76,t64,t0,t2,t3,t4]
def v210 := [t76,t25,t0,t1,t3,t4]
def v211 := [t76,t89,t0,t1,t3,t4]
def t142 := 0x60f800
def v212 := [t142,t0,t1,t2,t3,t4]
def t143 := 0x327e5dffffff
def v213 := [t0,t1,t2,t3,t143,t4]
def t144 := 0x306c5d8000ff
def v214 := [t0,t1,t2,t144,t3,t4]
def t145 := 0x212001f0700
def v215 := [t145,t0,t1,t2,t3,t4]
def v216 := [t76,t0,t29,t2,t3,t4]
def v217 := [t76,t0,t134,t2,t3,t4]
def v218 := [t76,t0,t1,t31,t3,t4]
def v219 := [t76,t0,t136,t1,t3,t4]
def t146 := 0x7f0000
def v220 := [t146,t0,t1,t2,t3,t4]
def t147 := 0x3f926effffff
def v221 := [t0,t1,t2,t3,t4,t147]
def t148 := 0x3d806e8000ff
def v222 := [t0,t1,t2,t3,t148,t4]
def v223 := [t76,t0,t60,t2,t3,t4]
def v224 := [t76,t0,t127,t2,t3,t4]
def v225 := [t76,t0,t1,t62,t3,t4]
def v226 := [t76,t0,t138,t1,t3,t4]
def t149 := 0x14a48700000f
def v227 := [t76,t0,t149,t2,t3,t4]
def v228 := [t0,t149,t1,t2,t3,t4]
def v229 := [t76,t0,t1,t77,t3,t4]
def v230 := [t0,t1,t77,t2,t3,t4]
def t150 := 0x3ffff77fffff
def v231 := [t76,t0,t3,t4,t150]
def v232 := [t76,t0,t1,t3,t4,t150]
def v233 := [t76,t0,t2,t3,t4,t150]
def v234 := [t0,t1,t2,t3,t4,t150]
def t151 := 0xc61b318c7ff
def v235 := [t151,t1,t2,t3,t4]
def v236 := [t151,t0,t1,t2,t3,t4]
def v237 := [t151,t1,t2,t3,t4,t150]
def t152 := 0x8800000
def v238 := [t152,t0,t1,t2,t3,t4]
def t153 := 0x339e44673800
def v239 := [t1,t2,t3,t153,t4]
def v240 := [t0,t1,t2,t3,t153,t4]
def v241 := [t1,t2,t3,t153,t4,t150]
def t154 := 0x306c5560f8ff
def v242 := [t0,t1,t2,t154,t4]
def v243 := [t0,t1,t2,t154,t3,t4]
def v244 := [t0,t1,t2,t154,t4,t150]
def t155 := 0xf93a21f0700
def v245 := [t0,t155,t1,t2,t4]
def v246 := [t0,t155,t1,t2,t3,t4]
def v247 := [t0,t155,t1,t2,t4,t150]
def t156 := 0x3d80667f00ff
def v248 := [t0,t1,t2,t3,t156]
def v249 := [t0,t1,t2,t3,t156,t4]
def v250 := [t0,t1,t2,t3,t156,t150]
def t157 := 0x27f9100ff00
def v251 := [t157,t0,t1,t2,t3]
def v252 := [t157,t0,t1,t2,t3,t4]
def v253 := [t157,t0,t1,t2,t3,t150]
def v254 := [t0,t149,t1,t3,t4,t150]
def v255 := [t0,t77,t2,t3,t4,t150]
def p31_1047 : Projection 23 12 := pick [1,2,3,8,10,11,13,14,16,18,19,21] rfl (by decide +kernel) (by decide)
theorem b0 : Ban 23 5 v2 := checkedSmall
theorem b1 : Ban 23 5 v3 := checkedSmall
theorem b2 : Ban 23 5 v4 := checkedSmall
theorem b3 : Ban 23 5 v5 := checkedSmall
theorem b4 : Ban 23 5 v6 := checkedSmall
theorem b5 : Ban 23 5 v7 := checkedSmall
theorem b6 : Ban 23 5 v8 := checkedSmall
theorem b7 : Ban 23 5 v9 := checkedSmall
theorem b8 : Ban 23 5 v10 := checkedSmall
theorem b137 : Ban 12 4 v136 := checkedSmall
theorem b138 : Ban 12 4 v137 := checkedSmall
theorem b139 : Ban 12 4 v138 := checkedSmall
theorem b140 : Ban 12 4 v139 := checkedSmall
theorem b141 : Ban 12 4 v140 := checkedSmall
theorem b142 : Ban 12 4 v141 := checkedSmall
theorem b143 : Ban 12 4 v142 := checkedSmall
theorem b144 : Ban 12 4 v143 := checkedSmall
theorem b145 : Ban 12 4 v144 := checkedSmall
theorem b146 : Ban 12 4 v145 := checkedSmall
theorem b147 : Ban 12 4 v146 := checkedSmall
theorem b148 : Ban 12 4 v147 := checkedSmall
theorem b149 : Ban 12 4 v148 := checkedSmall
theorem b150 : Ban 12 4 v149 := checkedSmall
theorem b151 : Ban 12 4 v150 := checkedSmall
theorem b152 : Ban 12 4 v151 := checkedSmall
theorem b153 : Ban 12 4 v152 := checkedSmall
theorem b154 : Ban 12 4 v153 := checkedSmall
theorem b155 : Ban 12 4 v154 := checkedSmall
theorem b156 : Ban 12 4 v155 := checkedSmall
theorem b157 : Ban 12 4 v156 := checkedSmall
theorem b158 : Ban 12 4 v157 := checkedSmall
theorem b159 : Ban 12 4 v158 := checkedSmall
theorem b160 : Ban 12 4 v159 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b161 : Ban 12 5 v135 := viaBranch (ws := [v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159]) (consBan b137 (consBan b138 (consBan b139 (consBan b140 (consBan b141 (consBan b142 (consBan b143 (consBan b144 (consBan b145 (consBan b146 (consBan b147 (consBan b148 (consBan b149 (consBan b150 (consBan b151 (consBan b152 (consBan b153 (consBan b154 (consBan b155 (consBan b156 (consBan b157 (consBan b158 (consBan b159 (consBan b160 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b162 : Ban 12 5 v160 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w0 : Wide 12 5 v160 := viaSub (ws := [v135,v160]) (consBan b161 (consBan b162 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b9 : Ban 23 5 v11 := smallByCut p31_1047 w0
theorem b10 : Ban 23 5 v12 := smallByCut p31_1047 w0
theorem b11 : Ban 23 5 v13 := checkedSmall
theorem b12 : Ban 23 5 v14 := checkedSmall
theorem b13 : Ban 23 5 v15 := smallByCut p31_2063 w0
theorem b14 : Ban 23 5 v16 := smallByCut p31_2063 w0
theorem b15 : Ban 23 5 v17 := checkedSmall
theorem b16 : Ban 23 5 v18 := checkedSmall
theorem b17 : Ban 23 5 v19 := checkedSmall
theorem b18 : Ban 23 5 v20 := checkedSmall
theorem b19 : Ban 23 5 v21 := checkedSmall
theorem b20 : Ban 23 5 v22 := checkedSmall
theorem b21 : Ban 23 5 v23 := checkedSmall
theorem b22 : Ban 23 5 v24 := checkedSmall
theorem b23 : Ban 23 5 v25 := checkedSmall
theorem b24 : Ban 23 5 v26 := checkedSmall
theorem b25 : Ban 23 5 v27 := checkedSmall
theorem b26 : Ban 23 5 v28 := checkedSmall
theorem b27 : Ban 23 5 v29 := checkedSmall
theorem b28 : Ban 23 5 v30 := checkedSmall
theorem b29 : Ban 23 5 v31 := checkedSmall
theorem b30 : Ban 23 5 v32 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b31 : Ban 23 6 v1 := viaBranch (ws := [v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32]) (consBan b0 (consBan b1 (consBan b2 (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b10 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (consBan b19 (consBan b20 (consBan b21 (consBan b22 (consBan b23 (consBan b24 (consBan b25 (consBan b26 (consBan b27 (consBan b28 (consBan b29 (consBan b30 (nilBan 23 5)))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b32 : Ban 23 5 v34 := checkedSmall
theorem b33 : Ban 23 5 v35 := checkedSmall
theorem b34 : Ban 23 5 v36 := checkedSmall
theorem b35 : Ban 23 5 v37 := checkedSmall
theorem b36 : Ban 23 5 v38 := checkedSmall
theorem b37 : Ban 23 5 v39 := checkedSmall
theorem b38 : Ban 23 5 v40 := checkedSmall
theorem b39 : Ban 23 5 v41 := checkedSmall
theorem b40 : Ban 23 5 v42 := checkedSmall
theorem b41 : Ban 23 5 v43 := checkedSmall
theorem b42 : Ban 23 5 v44 := checkedSmall
theorem b43 : Ban 23 5 v45 := smallByCut p31_1047 w0
theorem b44 : Ban 23 5 v46 := smallByCut p31_1047 w0
theorem b45 : Ban 23 5 v47 := checkedSmall
theorem b46 : Ban 23 5 v48 := checkedSmall
theorem b47 : Ban 23 5 v49 := smallByCut p31_2063 w0
theorem b48 : Ban 23 5 v50 := smallByCut p31_2063 w0
theorem b49 : Ban 23 5 v51 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b50 : Ban 23 6 v33 := viaBranch (ws := [v18,v19,v20,v34,v35,v5,v36,v37,v3,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51]) (consBan b16 (consBan b17 (consBan b18 (consBan b32 (consBan b33 (consBan b3 (consBan b34 (consBan b35 (consBan b1 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (consBan b40 (consBan b41 (consBan b42 (consBan b43 (consBan b44 (consBan b45 (consBan b46 (consBan b47 (consBan b48 (consBan b49 (nilBan 23 5)))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b51 : Ban 23 5 v53 := checkedSmall
theorem b52 : Ban 23 5 v54 := checkedSmall
theorem b53 : Ban 23 5 v55 := checkedSmall
theorem b54 : Ban 23 5 v56 := checkedSmall
theorem b55 : Ban 23 5 v57 := checkedSmall
theorem b56 : Ban 23 5 v58 := checkedSmall
theorem b57 : Ban 23 5 v59 := checkedSmall
theorem b58 : Ban 23 5 v60 := checkedSmall
theorem b59 : Ban 23 5 v61 := checkedSmall
theorem b60 : Ban 23 5 v62 := checkedSmall
theorem b61 : Ban 23 5 v63 := checkedSmall
theorem b62 : Ban 23 5 v64 := checkedSmall
theorem b63 : Ban 23 5 v65 := smallByCut p31_1047 w0
theorem b64 : Ban 23 5 v66 := smallByCut p31_1047 w0
theorem b65 : Ban 23 5 v67 := checkedSmall
theorem b66 : Ban 23 5 v68 := checkedSmall
theorem b67 : Ban 23 5 v69 := smallByCut p31_2063 w0
theorem b68 : Ban 23 5 v70 := smallByCut p31_2063 w0
theorem b69 : Ban 23 5 v71 := checkedSmall
theorem b70 : Ban 23 5 v72 := checkedSmall
theorem b71 : Ban 23 5 v73 := checkedSmall
theorem b72 : Ban 23 5 v74 := checkedSmall
theorem b73 : Ban 23 5 v75 := checkedSmall
theorem b74 : Ban 23 5 v76 := checkedSmall
theorem b75 : Ban 23 5 v77 := checkedSmall
theorem b76 : Ban 23 5 v78 := checkedSmall
theorem b77 : Ban 23 5 v79 := checkedSmall
theorem b78 : Ban 23 5 v80 := checkedSmall
theorem b79 : Ban 23 5 v81 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b80 : Ban 23 6 v52 := viaBranch (ws := [v53,v54,v8,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v22,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81]) (consBan b51 (consBan b52 (consBan b6 (consBan b53 (consBan b54 (consBan b55 (consBan b56 (consBan b57 (consBan b58 (consBan b59 (consBan b60 (consBan b61 (consBan b62 (consBan b63 (consBan b64 (consBan b65 (consBan b66 (consBan b67 (consBan b68 (consBan b69 (consBan b20 (consBan b70 (consBan b71 (consBan b72 (consBan b73 (consBan b74 (consBan b75 (consBan b76 (consBan b77 (consBan b78 (consBan b79 (nilBan 23 5)))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b81 : Ban 23 6 v3 := viaPerm map31_2 map31_2 b80 (by decide +kernel) (by decide +kernel)
theorem b82 : Ban 23 6 v5 := viaPerm map31_6 map31_8 b80 (by decide +kernel) (by decide +kernel)
theorem b83 : Ban 23 6 v54 := viaPerm map31_2 map31_2 b31 (by decide +kernel) (by decide +kernel)
theorem b84 : Ban 23 6 v63 := viaPerm map31_2 map31_2 b50 (by decide +kernel) (by decide +kernel)
theorem b85 : Ban 23 6 v82 := viaPerm map31_10 map31_10 b80 (by decide +kernel) (by decide +kernel)
theorem b86 : Ban 23 5 v84 := smallByCut p31_1047 w0
theorem b87 : Ban 23 5 v85 := smallByCut p31_1047 w0
theorem b88 : Ban 23 5 v86 := checkedSmall
theorem b89 : Ban 23 5 v87 := checkedSmall
theorem b90 : Ban 23 5 v88 := checkedSmall
theorem b91 : Ban 23 5 v89 := checkedSmall
theorem b92 : Ban 23 5 v90 := checkedSmall
theorem b93 : Ban 23 5 v91 := checkedSmall
theorem b94 : Ban 23 5 v92 := checkedSmall
theorem b95 : Ban 23 5 v93 := checkedSmall
theorem b96 : Ban 23 5 v94 := checkedSmall
theorem b97 : Ban 23 5 v95 := smallByCut p31_2063 w0
theorem b98 : Ban 23 5 v96 := smallByCut p31_2063 w0
theorem b99 : Ban 23 5 v97 := checkedSmall
theorem b100 : Ban 23 5 v98 := checkedSmall
theorem b101 : Ban 23 5 v99 := checkedSmall
theorem b102 : Ban 23 5 v100 := checkedSmall
theorem b103 : Ban 23 5 v101 := smallByCut p31_1047 w0
theorem b104 : Ban 23 5 v102 := smallByCut p31_1047 w0
theorem b105 : Ban 23 5 v103 := smallByCut p31_1047 w0
theorem b106 : Ban 23 5 v104 := checkedSmall
theorem b107 : Ban 23 5 v105 := checkedSmall
theorem b108 : Ban 23 5 v106 := smallByCut p31_1047 w0
theorem b109 : Ban 23 5 v107 := smallByCut p31_1047 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b110 : Ban 23 6 v83 := viaBranch (ws := [v84,v85,v10,v86,v87,v88,v89,v90,v64,v91,v92,v93,v94,v95,v96,v97,v23,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107]) (consBan b86 (consBan b87 (consBan b8 (consBan b88 (consBan b89 (consBan b90 (consBan b91 (consBan b92 (consBan b62 (consBan b93 (consBan b94 (consBan b95 (consBan b96 (consBan b97 (consBan b98 (consBan b99 (consBan b21 (consBan b100 (consBan b101 (consBan b102 (consBan b103 (consBan b104 (consBan b105 (consBan b106 (consBan b107 (consBan b108 (consBan b109 (nilBan 23 5)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b111 : Ban 23 5 v109 := smallByCut p31_1047 w0
theorem b112 : Ban 23 5 v110 := checkedSmall
theorem b113 : Ban 23 5 v111 := smallByCut p31_1047 w0
theorem b114 : Ban 23 5 v112 := smallByCut p31_1047 w0
theorem b115 : Ban 23 5 v113 := smallByCut p31_1047 w0
theorem b116 : Ban 23 5 v114 := smallByCut p31_1047 w0
theorem b117 : Ban 23 5 v115 := checkedSmall
theorem b118 : Ban 23 5 v116 := checkedSmall
theorem b119 : Ban 23 5 v117 := checkedSmall
theorem b120 : Ban 23 5 v118 := smallByCut p31_1047 w0
theorem b121 : Ban 23 5 v119 := smallByCut p31_1047 w0
theorem b122 : Ban 23 5 v120 := smallByCut p31_1047 w0
theorem b123 : Ban 23 5 v121 := smallByCut p31_1047 w0
theorem b124 : Ban 23 5 v122 := smallByCut p31_1047 w0
theorem b125 : Ban 23 5 v123 := checkedSmall
theorem b126 : Ban 23 5 v124 := checkedSmall
theorem b127 : Ban 23 5 v125 := checkedSmall
theorem b128 : Ban 23 5 v126 := smallByCut p31_1047 w0
theorem b129 : Ban 23 5 v127 := smallByCut p31_1047 w0
theorem b130 : Ban 23 5 v128 := smallByCut p31_1047 w0
theorem b131 : Ban 23 5 v129 := smallByCut p31_1047 w0
theorem b132 : Ban 23 5 v130 := smallByCut p31_2063 w0
theorem b133 : Ban 23 5 v131 := checkedSmall
theorem b134 : Ban 23 5 v132 := smallByCut p31_2063 w0
theorem b135 : Ban 23 5 v133 := smallByCut p31_1047 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b136 : Ban 23 6 v108 := viaBranch (ws := [v101,v102,v103,v109,v110,v93,v111,v112,v113,v45,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v85,v126,v127,v128,v129,v130,v131,v132,v133]) (consBan b103 (consBan b104 (consBan b105 (consBan b111 (consBan b112 (consBan b95 (consBan b113 (consBan b114 (consBan b115 (consBan b43 (consBan b116 (consBan b117 (consBan b118 (consBan b119 (consBan b120 (consBan b121 (consBan b122 (consBan b123 (consBan b124 (consBan b125 (consBan b126 (consBan b127 (consBan b87 (consBan b128 (consBan b129 (consBan b130 (consBan b131 (consBan b132 (consBan b133 (consBan b134 (consBan b135 (nilBan 23 5)))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b164 : Ban 23 6 v85 := smallByCut p31_1047 w0
theorem b165 : Ban 23 5 v162 := checkedSmall
theorem b166 : Ban 23 5 v163 := checkedSmall
theorem b167 : Ban 23 5 v164 := checkedSmall
theorem b168 : Ban 23 5 v165 := checkedSmall
theorem b169 : Ban 23 5 v166 := checkedSmall
theorem b170 : Ban 23 5 v167 := checkedSmall
theorem b171 : Ban 23 5 v168 := checkedSmall
theorem b172 : Ban 23 5 v169 := checkedSmall
theorem b173 : Ban 23 5 v170 := checkedSmall
theorem b174 : Ban 23 5 v171 := checkedSmall
theorem b175 : Ban 23 5 v172 := smallByCut p31_1047 w0
theorem b176 : Ban 23 5 v173 := checkedSmall
theorem b177 : Ban 23 5 v174 := checkedSmall
theorem b178 : Ban 23 5 v175 := checkedSmall
theorem b179 : Ban 23 5 v176 := checkedSmall
theorem b180 : Ban 23 5 v177 := checkedSmall
theorem b181 : Ban 23 5 v178 := checkedSmall
theorem b182 : Ban 23 5 v179 := checkedSmall
theorem b183 : Ban 23 5 v180 := smallByCut p31_1047 w0
theorem b184 : Ban 23 5 v181 := checkedSmall
theorem b185 : Ban 23 5 v182 := smallByCut p31_2063 w0
theorem b186 : Ban 23 5 v183 := smallByCut p31_2063 w0
theorem b187 : Ban 23 5 v184 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b188 : Ban 23 6 v161 := viaBranch (ws := [v162,v79,v64,v163,v164,v165,v166,v167,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184]) (consBan b165 (consBan b77 (consBan b62 (consBan b166 (consBan b167 (consBan b168 (consBan b169 (consBan b170 (consBan b171 (consBan b172 (consBan b173 (consBan b174 (consBan b175 (consBan b176 (consBan b177 (consBan b178 (consBan b179 (consBan b180 (consBan b181 (consBan b182 (consBan b183 (consBan b184 (consBan b185 (consBan b186 (consBan b187 (nilBan 23 5)))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b189 : Ban 23 6 v93 := viaPerm map31_6 map31_8 b188 (by decide +kernel) (by decide +kernel)
theorem b190 : Ban 23 6 v185 := viaPerm map31_1 map31_1 b110 (by decide +kernel) (by decide +kernel)
theorem b191 : Ban 23 6 v186 := viaPerm map31_1 map31_1 b136 (by decide +kernel) (by decide +kernel)
theorem b163 : Ban 23 6 v134 := smallByCut p31_2063 w0
theorem b192 : Ban 23 6 v187 := viaPerm map31_7 map31_9 b188 (by decide +kernel) (by decide +kernel)
theorem b193 : Ban 23 6 v188 := viaPerm map31_6 map31_8 b31 (by decide +kernel) (by decide +kernel)
theorem b194 : Ban 23 6 v189 := viaPerm map31_6 map31_8 b50 (by decide +kernel) (by decide +kernel)
theorem b195 : Ban 23 6 v190 := viaPerm map31_4 map31_4 b80 (by decide +kernel) (by decide +kernel)
theorem b196 : Ban 23 6 v191 := viaPerm map31_8 map31_6 b80 (by decide +kernel) (by decide +kernel)
theorem b197 : Ban 23 6 v192 := viaPerm map31_4 map31_4 b110 (by decide +kernel) (by decide +kernel)
theorem b198 : Ban 23 6 v193 := viaPerm map31_4 map31_4 b136 (by decide +kernel) (by decide +kernel)
theorem b199 : Ban 23 6 v194 := smallByCut p31_1047 w0
theorem b200 : Ban 23 6 v195 := viaPerm map31_2 map31_2 b188 (by decide +kernel) (by decide +kernel)
theorem b201 : Ban 23 6 v196 := viaPerm map31_5 map31_5 b110 (by decide +kernel) (by decide +kernel)
theorem b202 : Ban 23 6 v197 := viaPerm map31_5 map31_5 b136 (by decide +kernel) (by decide +kernel)
theorem b203 : Ban 23 6 v198 := smallByCut p31_2063 w0
theorem b204 : Ban 23 6 v199 := viaPerm map31_3 map31_3 b188 (by decide +kernel) (by decide +kernel)
theorem b205 : Ban 23 6 v180 := viaPerm map31_8 map31_6 b110 (by decide +kernel) (by decide +kernel)
theorem b206 : Ban 23 6 v172 := viaPerm map31_8 map31_6 b136 (by decide +kernel) (by decide +kernel)
theorem b207 : Ban 23 6 v200 := smallByCut p31_1047 w0
theorem b208 : Ban 23 6 v201 := viaPerm map31_9 map31_7 b110 (by decide +kernel) (by decide +kernel)
theorem b209 : Ban 23 6 v202 := viaPerm map31_9 map31_7 b136 (by decide +kernel) (by decide +kernel)
theorem b210 : Ban 23 6 v203 := smallByCut p31_2063 w0
theorem b211 : Ban 23 6 v204 := viaPerm map31_1 map31_1 b188 (by decide +kernel) (by decide +kernel)
theorem b212 : Ban 23 5 v206 := checkedSmall
theorem b213 : Ban 23 5 v207 := checkedSmall
theorem b214 : Ban 23 5 v208 := checkedSmall
theorem b215 : Ban 23 5 v209 := smallByCut p31_1047 w0
theorem b216 : Ban 23 5 v210 := smallByCut p31_2063 w0
theorem b217 : Ban 23 5 v211 := smallByCut p31_2063 w0
theorem b218 : Ban 23 5 v212 := checkedSmall
theorem b219 : Ban 23 5 v213 := checkedSmall
theorem b220 : Ban 23 5 v214 := checkedSmall
theorem b221 : Ban 23 5 v215 := checkedSmall
theorem b222 : Ban 23 5 v216 := smallByCut p31_1047 w0
theorem b223 : Ban 23 5 v217 := smallByCut p31_1047 w0
theorem b224 : Ban 23 5 v218 := smallByCut p31_2063 w0
theorem b225 : Ban 23 5 v219 := smallByCut p31_2063 w0
theorem b226 : Ban 23 5 v220 := checkedSmall
theorem b227 : Ban 23 5 v221 := checkedSmall
theorem b228 : Ban 23 5 v222 := checkedSmall
theorem b229 : Ban 23 5 v223 := smallByCut p31_1047 w0
theorem b230 : Ban 23 5 v224 := smallByCut p31_1047 w0
theorem b231 : Ban 23 5 v225 := smallByCut p31_2063 w0
theorem b232 : Ban 23 5 v226 := smallByCut p31_2063 w0
theorem b233 : Ban 23 5 v227 := smallByCut p31_2063 w0
theorem b234 : Ban 23 5 v228 := smallByCut p31_2063 w0
theorem b235 : Ban 23 5 v229 := smallByCut p31_1047 w0
theorem b236 : Ban 23 5 v230 := smallByCut p31_1047 w0
theorem b237 : Ban 23 5 v231 := smallByCut p31_1047 w0
theorem b238 : Ban 23 5 v232 := smallByCut p31_1047 w0
theorem b239 : Ban 23 5 v233 := smallByCut p31_1047 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b240 : Ban 23 6 v205 := viaBranch (ws := [v94,v206,v207,v208,v106,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v181,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233]) (consBan b96 (consBan b212 (consBan b213 (consBan b214 (consBan b108 (consBan b215 (consBan b216 (consBan b217 (consBan b218 (consBan b219 (consBan b220 (consBan b221 (consBan b222 (consBan b223 (consBan b224 (consBan b225 (consBan b226 (consBan b227 (consBan b228 (consBan b184 (consBan b229 (consBan b230 (consBan b231 (consBan b232 (consBan b233 (consBan b234 (consBan b235 (consBan b236 (consBan b237 (consBan b238 (consBan b239 (nilBan 23 5)))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b241 : Ban 23 5 v235 := smallByCut p31_1047 w0
theorem b242 : Ban 23 5 v236 := smallByCut p31_1047 w0
theorem b243 : Ban 23 5 v237 := smallByCut p31_1047 w0
theorem b244 : Ban 23 5 v238 := smallByCut p31_1047 w0
theorem b245 : Ban 23 5 v239 := checkedSmall
theorem b246 : Ban 23 5 v240 := checkedSmall
theorem b247 : Ban 23 5 v241 := checkedSmall
theorem b248 : Ban 23 5 v242 := smallByCut p31_1047 w0
theorem b249 : Ban 23 5 v243 := smallByCut p31_1047 w0
theorem b250 : Ban 23 5 v244 := smallByCut p31_1047 w0
theorem b251 : Ban 23 5 v245 := checkedSmall
theorem b252 : Ban 23 5 v246 := checkedSmall
theorem b253 : Ban 23 5 v247 := checkedSmall
theorem b254 : Ban 23 5 v248 := smallByCut p31_1047 w0
theorem b255 : Ban 23 5 v249 := smallByCut p31_1047 w0
theorem b256 : Ban 23 5 v250 := smallByCut p31_1047 w0
theorem b257 : Ban 23 5 v251 := checkedSmall
theorem b258 : Ban 23 5 v252 := checkedSmall
theorem b259 : Ban 23 5 v253 := checkedSmall
theorem b260 : Ban 23 5 v254 := smallByCut p31_2063 w0
theorem b261 : Ban 23 5 v255 := smallByCut p31_1047 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b262 : Ban 23 6 v234 := viaBranch (ws := [v235,v236,v237,v129,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v231,v232,v233,v254,v255,v230,v228]) (consBan b241 (consBan b242 (consBan b243 (consBan b131 (consBan b244 (consBan b245 (consBan b246 (consBan b247 (consBan b248 (consBan b249 (consBan b250 (consBan b251 (consBan b252 (consBan b253 (consBan b254 (consBan b255 (consBan b256 (consBan b257 (consBan b258 (consBan b259 (consBan b237 (consBan b238 (consBan b239 (consBan b260 (consBan b261 (consBan b236 (consBan b234 (nilBan 23 5)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b264 : Ban 23 6 v228 := smallByCut p31_2063 w0
theorem b263 : Ban 23 6 v230 := smallByCut p31_1047 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b265 : Ban 23 7 v0 := viaBranch (ws := [v1,v33,v3,v5,v54,v63,v52,v82,v83,v108,v85,v93,v185,v186,v134,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v180,v172,v200,v161,v201,v202,v203,v204,v205,v234,v228,v230]) (consBan b31 (consBan b50 (consBan b81 (consBan b82 (consBan b83 (consBan b84 (consBan b80 (consBan b85 (consBan b110 (consBan b136 (consBan b164 (consBan b189 (consBan b190 (consBan b191 (consBan b163 (consBan b192 (consBan b193 (consBan b194 (consBan b195 (consBan b196 (consBan b197 (consBan b198 (consBan b199 (consBan b200 (consBan b201 (consBan b202 (consBan b203 (consBan b204 (consBan b205 (consBan b206 (consBan b207 (consBan b188 (consBan b208 (consBan b209 (consBan b210 (consBan b211 (consBan b240 (consBan b262 (consBan b264 (consBan b263 (nilBan 23 6))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem verifiedPin : Wide 23 7 v0 := widen (by decide +kernel) b265
end PEqualNP.Outside.L_meta_12250.Support

namespace PEqualNP.Outside.L_meta_12250.Data
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12250.Support
def target (x : Fin 6 → Bool) := Nat.testBit (4269834240 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def posBits : ℕ := 0xbfefbdf7cf3cefbebaeb9e79df7df7befbef
def negBits : ℕ := 0x3f6bb5b78d2ccebe32ab8c69db5ce7badae7
def sample (bank : ℕ) (i : Fin 24) (j : Fin 6) := bank.testBit (6*i.val+j.val)
def inputs : List ℕ := [0x98c37798c7ff,0xe0d8bbe0f8ff,0xfb00ddff00ff,0xad6d0effff0f,0x56b6e07ffff0,0x800000000000]
def seeds : List Wire := [(false,0x98c37798c7ff),(false,0xe0d8bbe0f8ff),(false,0xfb00ddff00ff),(false,0xad6d0effff0f),(false,0x56b6e07ffff0),(true,0x800000000000)]
set_option maxHeartbeats 10000000 in
theorem listed : ∀ i : Fin 24, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (24+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 24, target (sample posBits i)=true ∧ target (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 24, ∀ b∈inputs, b.testBit i.val≠b.testBit (24+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 24 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 6 C=target) :
    ∃ k≤C.gates.countP counted, Live 24 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 6 → Bool) : C.eval (List.ofFn x)=target x := congrFun eq x
  have good : Good 24 out.2 := by
    intro i hi same
    let j : Fin 24 := ⟨i,hi⟩
    have diff : read i out=read (24+i) out := by
      change (out.1 != out.2.testBit i) = (out.1 != out.2.testBit (24+i))
      rw [same]
    have p := ev i;have n := ev (24+i)
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
def restrictRows : Projection 24 23 := pick (List.range 23) (by decide) (by decide) (by decide)
set_option maxHeartbeats 8000000 in
theorem core_floor : Wide 23 7 restricted := verifiedPin
theorem six_floor : Ban 24 8 inputs := viaCut restrictRows core_floor (by decide) (by decide +kernel) (by decide +kernel)
def witness : Circuit := ⟨[⟨.and,[2,5]⟩, ⟨.and,[1,6]⟩, ⟨.and,[0,7]⟩, ⟨.and,[4,8]⟩, ⟨.or,[1,2]⟩, ⟨.or,[0,10]⟩, ⟨.and,[4,11]⟩, ⟨.or,[8,12]⟩, ⟨.and,[3,13]⟩, ⟨.or,[9,14]⟩],15⟩
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
end PEqualNP.Outside.L_meta_12250.Data

theorem PEqualNP.Outside.L_meta_12250 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269834240 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269834240 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_12250.Data.mono_enough
