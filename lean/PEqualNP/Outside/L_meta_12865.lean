import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12865.Support

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

def t0 := 0x5e1c367f1e3f
def t1 := 0x12ec58b9fe3c7
def t2 := 0x2816adde1ffff
def t3 := 0x3f40761fe03f8
def t4 := 0x3fbb001fffc00
def v0 := [t0,t1,t2,t3,t4]
def t5 := 0xe04021f0207
def v1 := [t5,t0,t1,t2,t3,t4]
def t6 := 0x501834601c38
def v2 := [t5,t6,t1,t2,t3,t4]
def v3 := [t6,t0,t1,t2,t3,t4]
def t7 := 0x120c18980e1c0
def v4 := [t5,t0,t7,t2,t3,t4]
def v5 := [t0,t7,t1,t2,t3,t4]
def t8 := 0x10207
def v6 := [t8,t0,t1,t2,t3,t4]
def t9 := 0x28f6edfffffff
def v7 := [t0,t1,t2,t9,t3,t4]
def t10 := 0xe04021e0000
def v8 := [t10,t0,t1,t2,t3,t4]
def t11 := 0x2816adde0fdf8
def v9 := [t0,t1,t11,t2,t3,t4]
def t12 := 0x404001e0200
def v10 := [t12,t0,t1,t2,t3,t4]
def t13 := 0x3fe0763ff03ff
def v11 := [t0,t1,t2,t3,t4,t13]
def t14 := 0xa0002010007
def v12 := [t14,t0,t1,t2,t3,t4]
def t15 := 0x3f00361e001f8
def v13 := [t0,t1,t2,t15,t3,t4]
def t16 := 0xa00001f0000
def v14 := [t16,t0,t1,t2,t3,t4]
def t17 := 0x3ffb403fffe07
def v15 := [t0,t1,t2,t3,t4,t17]
def t18 := 0x40402000207
def v16 := [t18,t0,t1,t2,t3,t4]
def t19 := 0x3f1b001e0fc00
def v17 := [t0,t1,t2,t19,t3,t4]
def t20 := 0x17eddbfffffff
def v18 := [t5,t20,t2,t3,t4]
def v19 := [t5,t0,t20,t2,t3,t4]
def v20 := [t5,t1,t20,t2,t3,t4]
def t21 := 0x814611e3f
def v21 := [t21,t5,t1,t2,t3,t4]
def t22 := 0x28162c980e1c0
def v22 := [t5,t1,t22,t2,t3,t4]
def t23 := 0x408981e3c7
def v23 := [t23,t5,t0,t2,t3,t4]
def t24 := 0x2812a54601c38
def v24 := [t5,t0,t24,t2,t3,t4]
def v25 := [t0,t1,t20,t2,t3,t4]
def v26 := [t6,t0,t20,t2,t3,t4]
def v27 := [t7,t1,t20,t2,t3,t4]
def t25 := 0x489de1ffff
def v28 := [t25,t0,t1,t3,t4]
def v29 := [t25,t0,t1,t20,t3,t4]
def v30 := [t25,t0,t1,t2,t3,t4]
def t26 := 0x3ffffffffffff
def v31 := [t0,t1,t2,t3,t4,t26]
def t27 := 0x17e95221e0000
def v32 := [t0,t1,t27,t3,t4]
def v33 := [t0,t1,t27,t20,t3,t4]
def v34 := [t0,t1,t27,t2,t3,t4]
def t28 := 0x2812240000000
def v35 := [t0,t1,t28,t2,t3,t4]
def t29 := 0x1740521fe03f8
def v36 := [t0,t1,t29,t2,t4]
def v37 := [t0,t1,t29,t20,t2,t4]
def v38 := [t0,t1,t29,t2,t3,t4]
def t30 := 0x3fedfffffffff
def v39 := [t0,t1,t2,t3,t4,t30]
def t31 := 0xad89e01fc07
def v40 := [t31,t0,t1,t2,t4]
def v41 := [t31,t0,t1,t20,t2,t4]
def v42 := [t31,t0,t1,t2,t3,t4]
def t32 := 0x2800240000000
def v43 := [t0,t1,t32,t2,t3,t4]
def t33 := 0x17a9001fffc00
def v44 := [t0,t1,t33,t2,t3]
def v45 := [t0,t1,t33,t20,t2,t3]
def v46 := [t0,t1,t33,t2,t3,t4]
def t34 := 0x3fffdbfffffff
def v47 := [t0,t1,t2,t3,t4,t34]
def t35 := 0x44dbe0003ff
def v48 := [t35,t0,t1,t2,t3]
def v49 := [t35,t0,t1,t20,t2,t3]
def v50 := [t35,t0,t1,t2,t3,t4]
def t36 := 0x2812000000000
def v51 := [t0,t1,t36,t2,t3,t4]
def v52 := [t21,t0,t1,t2,t3,t4]
def t37 := 0x5e14221e0000
def v53 := [t21,t37,t1,t2,t3,t4]
def v54 := [t37,t0,t1,t2,t3,t4]
def t38 := 0x12ecd9fffffff
def v55 := [t0,t1,t38,t2,t3,t4]
def t39 := 0x814601c38
def v56 := [t39,t0,t1,t2,t3,t4]
def t40 := 0x12ec58b9ee1c0
def v57 := [t0,t40,t1,t2,t3,t4]
def v58 := [t21,t0,t1,t22,t3,t4]
def v59 := [t0,t1,t22,t2,t3,t4]
def t41 := 0x600238
def v60 := [t41,t0,t1,t2,t3,t4]
def t42 := 0x3f40f75ff1fff
def v61 := [t0,t1,t2,t3,t42,t4]
def t43 := 0x814011c07
def v62 := [t43,t0,t1,t2,t3,t4]
def t44 := 0x3f407619e01c0
def v63 := [t0,t1,t2,t44,t3,t4]
def t45 := 0x611c00
def v64 := [t45,t0,t1,t2,t3,t4]
def t46 := 0x3fbb815fffe3f
def v65 := [t0,t1,t2,t3,t4,t46]
def t47 := 0x81400023f
def v66 := [t47,t0,t1,t2,t3,t4]
def t48 := 0x3fbb0019ee000
def v67 := [t0,t1,t2,t3,t48,t4]
def v68 := [t21,t7,t1,t2,t3,t4]
def t49 := 0x2df7effffffff
def v69 := [t21,t1,t49,t3,t4]
def v70 := [t21,t0,t1,t49,t3,t4]
def v71 := [t21,t1,t2,t49,t3,t4]
def t50 := 0x5404207e0238
def v72 := [t21,t50,t1,t2,t3,t4]
def t51 := 0x3a003418001c0
def v73 := [t21,t1,t2,t51,t3,t4]
def t52 := 0x5a10007f1c00
def v74 := [t21,t52,t1,t2,t3,t4]
def t53 := 0x3a1a00180e000
def v75 := [t21,t1,t2,t53,t3,t4]
def v76 := [t21,t23,t0,t1,t3,t4]
def t54 := 0x12e85021e0000
def v77 := [t21,t0,t54,t1,t3,t4]
def v78 := [t0,t1,t2,t49,t3,t4]
def v79 := [t37,t0,t1,t49,t3,t4]
def v80 := [t1,t22,t2,t49,t3,t4]
def t55 := 0xe448b9fe3c7
def v81 := [t55,t0,t2,t3,t4]
def v82 := [t55,t0,t1,t2,t3,t4]
def v83 := [t55,t0,t2,t49,t3,t4]
def t56 := 0x1208100000000
def v84 := [t0,t56,t1,t2,t3,t4]
def t57 := 0x2d13a74601c38
def v85 := [t0,t2,t57,t3,t4]
def v86 := [t0,t1,t2,t57,t3,t4]
def v87 := [t0,t2,t57,t49,t3,t4]
def t58 := 0x2d40661fe03f8
def v88 := [t0,t1,t2,t58,t4]
def v89 := [t0,t1,t2,t58,t49,t4]
def v90 := [t0,t1,t2,t58,t3,t4]
def t59 := 0x3ff7fffffffff
def v91 := [t0,t1,t2,t3,t4,t59]
def t60 := 0xb789e01fc07
def v92 := [t60,t0,t1,t2,t4]
def v93 := [t60,t0,t1,t2,t49,t4]
def v94 := [t60,t0,t1,t2,t3,t4]
def t61 := 0x1200100000000
def v95 := [t0,t61,t1,t2,t3,t4]
def t62 := 0x2db3001fffc00
def v96 := [t0,t1,t2,t62,t3]
def v97 := [t0,t1,t2,t62,t49,t3]
def v98 := [t0,t1,t2,t62,t3,t4]
def t63 := 0x3fffeffffffff
def v99 := [t0,t1,t2,t3,t4,t63]
def t64 := 0x44efe0003ff
def v100 := [t64,t0,t1,t2,t3]
def v101 := [t64,t0,t1,t2,t49,t3]
def v102 := [t64,t0,t1,t2,t3,t4]
def t65 := 0x1208000000000
def v103 := [t0,t65,t1,t2,t3,t4]
def t66 := 0x17ed5ab9fe3c7
def v104 := [t0,t1,t66,t2,t3,t4]
def t67 := 0x501020000000
def v105 := [t67,t0,t1,t2,t3,t4]
def t68 := 0x120c18981e3c7
def v106 := [t0,t68,t1,t2,t3,t4]
def t69 := 0x5404201e0000
def v107 := [t69,t0,t1,t2,t3,t4]
def t70 := 0x3fe1763fe03f8
def v108 := [t0,t1,t2,t3,t4,t70]
def t71 := 0xa1002000000
def v109 := [t71,t0,t1,t2,t3,t4]
def t72 := 0x3a00341e003f8
def v110 := [t0,t1,t2,t72,t3,t4]
def t73 := 0x5a10001e0000
def v111 := [t73,t0,t1,t2,t3,t4]
def t74 := 0x3ffb423fffc00
def v112 := [t0,t1,t2,t3,t4,t74]
def t75 := 0x40422000000
def v113 := [t75,t0,t1,t2,t3,t4]
def t76 := 0x3a1a001e1fc00
def v114 := [t0,t1,t2,t76,t3,t4]
def v115 := [t37,t1,t22,t3,t4]
def v116 := [t37,t0,t1,t22,t3,t4]
def v117 := [t37,t1,t22,t2,t3,t4]
def v118 := [t23,t37,t0,t1,t3,t4]
def v119 := [t37,t0,t54,t1,t3,t4]
def v120 := [t0,t1,t24,t2,t3,t4]
def t77 := 0x268ff
def t78 := 0x391793
def t79 := 0xd18f1c
def t80 := 0xec0fe0
def v121 := [t77,t78,t79,t80]
def t81 := 0x93
def v122 := [t81,t77,t78,t79,t80]
def t82 := 0x3b7fff
def v123 := [t77,t78,t82,t79,t80]
def t83 := 0x2686c
def v124 := [t83,t77,t78,t79,t80]
def t84 := 0x391700
def v125 := [t77,t84,t78,t79,t80]
def t85 := 0x81c
def v126 := [t85,t77,t78,t79,t80]
def t86 := 0xd3efff
def v127 := [t77,t78,t79,t86,t80]
def t87 := 0x260e3
def v128 := [t87,t77,t78,t79,t80]
def t88 := 0xd18700
def v129 := [t77,t78,t88,t79,t80]
def t89 := 0x8e0
def v130 := [t89,t77,t78,t79,t80]
def t90 := 0xee6fff
def v131 := [t77,t78,t79,t80,t90]
def t91 := 0x2601f
def v132 := [t91,t77,t78,t79,t80]
def t92 := 0xec0700
def v133 := [t77,t78,t79,t92,t80]
def t93 := 0x110710
def v134 := [t77,t93,t78,t79,t80]
def t94 := 0xf99f9f
def v135 := [t77,t78,t79,t80,t94]
def t95 := 0x281083
def v136 := [t77,t95,t78,t79,t80]
def t96 := 0xc0880c
def v137 := [t77,t78,t96,t79,t80]
def t97 := 0x280780
def v138 := [t77,t97,t78,t79,t80]
def t98 := 0xfd1ff3
def v139 := [t77,t78,t79,t80,t98]
def t99 := 0x111013
def v140 := [t77,t99,t78,t79,t80]
def t100 := 0xc40860
def v141 := [t77,t78,t100,t79,t80]
def t101 := 0xc00f00
def v142 := [t77,t78,t101,t79,t80]
def t102 := 0xfd8ffc
def v143 := [t77,t78,t79,t80,t102]
def t103 := 0x11801c
def v144 := [t77,t103,t78,t79,t80]
def t104 := 0x2c00e0
def v145 := [t77,t104,t78,t79,t80]
def t105 := 0xffffff
def v146 := [t77,t78,t79,t80,t105]
def p59_313 : Projection 25 12 := pick [0,2,6,7,9,13,14,16,17,18,20,23] rfl (by decide +kernel) (by decide)
def map59_2 : Projection 25 25 := pick [0,2,1,6,7,8,3,4,5,9,13,14,15,10,11,12,16,17,18,20,19,23,24,21,22] rfl (by decide +kernel) (by decide)
def v147 := [t50,t0,t1,t2,t3,t4]
def t106 := 0x5bbff
def t107 := 0x86e3f
def t108 := 0xb17c7
def t109 := 0xec3f8
def v148 := [t106,t107,t108,t109]
def p59_43 : Projection 25 10 := pick [0,1,2,10,11,12,13,14,15,16] rfl (by decide +kernel) (by decide)
def t110 := 0x3fe1f77ff1fff
def v149 := [t0,t1,t2,t3,t4,t110]
def t111 := 0xa1816011c07
def v150 := [t111,t0,t1,t2,t3,t4]
def v151 := [t0,t1,t2,t51,t3,t4]
def v152 := [t52,t0,t1,t2,t3,t4]
def map59_1 : Projection 25 25 := pick [0,1,2,10,11,12,13,14,15,16,3,4,5,6,7,8,9,18,17,19,20,21,22,23,24] rfl (by decide +kernel) (by decide)
def t112 := 0x3ffbc37fffe3f
def v153 := [t0,t1,t2,t3,t4,t112]
def t113 := 0x40c3600023f
def v154 := [t113,t0,t1,t2,t3,t4]
def v155 := [t0,t1,t2,t53,t3,t4]
def v156 := [t23,t0,t1,t2,t3,t4]
def t114 := 0x3afefdfffffff
def v157 := [t0,t1,t2,t114,t3,t4]
def v158 := [t0,t54,t1,t2,t3,t4]
def t115 := 0x12405019e03c0
def v159 := [t0,t115,t1,t2,t3,t4]
def t116 := 0x3fec7ebffe3ff
def v160 := [t0,t1,t2,t3,t4,t116]
def t117 := 0xac08a01e007
def v161 := [t117,t0,t1,t2,t3,t4]
def t118 := 0x2d00260600038
def v162 := [t0,t1,t2,t118,t3,t4]
def t119 := 0x12a80019fe000
def v163 := [t0,t119,t1,t2,t3,t4]
def t120 := 0x3fff58bffffc7
def v164 := [t0,t1,t2,t3,t4,t120]
def t121 := 0x4458a0003c7
def v165 := [t121,t0,t1,t2,t3,t4]
def t122 := 0x2d13000601c00
def v166 := [t0,t1,t2,t122,t3,t4]
def t123 := 0x2800241e003f8
def v167 := [t0,t1,t123,t2,t3,t4]
def t124 := 0x3f56ffdffffff
def v168 := [t0,t1,t2,t3,t124,t4]
def t125 := 0x540c347f1e3f
def v169 := [t125,t1,t2,t3,t4]
def v170 := [t125,t0,t1,t2,t3,t4]
def v171 := [t125,t1,t2,t3,t124,t4]
def t126 := 0x3a163c980e1c0
def v172 := [t1,t2,t126,t3,t4]
def v173 := [t0,t1,t2,t126,t3,t4]
def v174 := [t1,t2,t126,t3,t124,t4]
def t127 := 0x12445899fe3c7
def v175 := [t0,t127,t2,t3,t4]
def v176 := [t0,t127,t1,t2,t3,t4]
def v177 := [t0,t127,t2,t3,t124,t4]
def t128 := 0x3ffefffffffff
def v178 := [t0,t1,t2,t3,t4,t128]
def t129 := 0xa8002000000
def v179 := [t129,t0,t1,t2,t3,t4]
def t130 := 0x2d12a74601c38
def v180 := [t0,t2,t130,t3,t4]
def v181 := [t0,t1,t2,t130,t3,t4]
def v182 := [t0,t2,t130,t3,t124,t4]
def v183 := [t0,t1,t123,t124,t4]
def v184 := [t0,t1,t123,t2,t124,t4]
def v185 := [t0,t1,t123,t3,t124,t4]
def t131 := 0x1689c01fc07
def v186 := [t131,t0,t1,t2,t124,t4]
def t132 := 0x17405201e0000
def v187 := [t0,t1,t132,t3,t124,t4]
def v188 := [t0,t1,t132,t2,t3,t4]
def v189 := [t131,t0,t1,t2,t3,t4]
def t133 := 0x3ffb761fffff8
def v190 := [t0,t1,t2,t124,t4,t133]
def t134 := 0x407600003f8
def v191 := [t134,t0,t1,t2,t124,t4]
def t135 := 0x3f12001fffc00
def v192 := [t0,t1,t2,t135,t3]
def v193 := [t0,t1,t2,t135,t3,t124]
def v194 := [t0,t1,t2,t135,t3,t4]
def t136 := 0x3fffffdffffff
def v195 := [t0,t1,t2,t3,t4,t136]
def t137 := 0x44ffc0003ff
def v196 := [t137,t0,t1,t2,t3]
def v197 := [t137,t0,t1,t2,t3,t124]
def v198 := [t137,t0,t1,t2,t3,t4]
def t138 := 0xa9000000000
def v199 := [t138,t0,t1,t2,t3,t4]
def t139 := 0x4adc0003ff
def v200 := [t139,t0,t1,t2,t3,t4]
def t140 := 0x5e5efe7f1fff
def v201 := [t0,t140,t1,t2,t3,t4]
def t141 := 0x42c80001c0
def v202 := [t141,t0,t1,t2,t3,t4]
def t142 := 0x5e14227f1c00
def v203 := [t142,t0,t1,t2,t3,t4]
def t143 := 0x40880003c7
def v204 := [t143,t0,t1,t2,t3,t4]
def t144 := 0x12ecfdf9fe3ff
def v205 := [t0,t1,t144,t2,t3,t4]
def t145 := 0xa54000038
def v206 := [t145,t0,t1,t2,t3,t4]
def t146 := 0x12e85039fe000
def v207 := [t0,t146,t1,t2,t3,t4]
def t147 := 0x2812001e1fc00
def v208 := [t139,t0,t1,t147,t3,t4]
def v209 := [t0,t1,t147,t2,t3,t4]
def t148 := 0x2400003f8
def v210 := [t148,t0,t1,t2,t3,t4]
def t149 := 0x3f44ffdfe03ff
def v211 := [t0,t1,t2,t3,t149,t4]
def t150 := 0x489c000007
def v212 := [t150,t0,t1,t2,t3,t4]
def t151 := 0x3f40521fe0000
def v213 := [t0,t1,t2,t151,t3,t4]
def t152 := 0x3fbfaddffffff
def v214 := [t139,t0,t1,t2,t3,t152]
def v215 := [t0,t1,t2,t3,t4,t152]
def v216 := [t139,t52,t0,t1,t2,t3]
def v217 := [t139,t113,t0,t1,t2,t3]
def v218 := [t139,t0,t119,t1,t2,t3]
def v219 := [t139,t121,t0,t1,t2,t3]
def t153 := 0x17a90001e0000
def v220 := [t139,t0,t1,t153,t3]
def v221 := [t139,t0,t1,t153,t2,t3]
def v222 := [t139,t0,t1,t153,t3,t4]
def t154 := 0x3f00001fe0000
def v223 := [t139,t0,t1,t2,t154,t3]
def v224 := [t139,t134,t0,t1,t2,t3]
def v225 := [t0,t1,t153,t2,t3,t4]
def v226 := [t0,t1,t2,t154,t3,t4]
def p59_27 : Projection 25 10 := pick [0,1,2,3,4,5,6,7,8,9] rfl (by decide +kernel) (by decide)
def v227 := [t0,t1,t2,t3,t4,t133]
def v228 := [t50,t0,t1,t2,t4,t133]
def v229 := [t111,t0,t1,t2,t4,t133]
def v230 := [t52,t0,t1,t2,t3,t133]
def v231 := [t113,t0,t1,t2,t3,t133]
def t155 := 0x5e14207f1e38
def v232 := [t155,t0,t1,t2,t3,t4]
def t156 := 0x3ffbf77ffffff
def v233 := [t0,t1,t2,t3,t4,t156]
def t157 := 0x816000007
def v234 := [t157,t0,t1,t2,t3,t4]
def t158 := 0x3a1a34180e1c0
def v235 := [t0,t1,t2,t158,t3,t4]
def v236 := [t0,t115,t1,t2,t4,t133]
def v237 := [t117,t0,t1,t2,t4,t133]
def v238 := [t0,t119,t1,t2,t3,t133]
def v239 := [t121,t0,t1,t2,t3,t133]
def t159 := 0x12e85019fe3c0
def v240 := [t0,t159,t1,t2,t3,t4]
def t160 := 0x3fff7ebffffff
def v241 := [t0,t1,t2,t3,t4,t160]
def t161 := 0x408a000007
def v242 := [t161,t0,t1,t2,t3,t4]
def t162 := 0x2d13260601c38
def v243 := [t0,t1,t2,t162,t3,t4]
def v244 := [t0,t1,t132,t2,t4,t133]
def v245 := [t0,t1,t2,t3,t152,t133]
def v246 := [t0,t1,t153,t2,t3,t133]
def t163 := 0x2812241e1fff8
def v247 := [t0,t1,t163,t2,t3,t4]
def t164 := 0x17e95201e0000
def v248 := [t0,t1,t164,t2,t3,t4]
def v249 := [t0,t1,t2,t154,t133]
def v250 := [t0,t1,t2,t154,t3,t133]
def v251 := [t0,t1,t2,t154,t4,t133]
def v252 := [t134,t0,t1,t2,t3,t133]
def t165 := 0xbb00001fc00
def v253 := [t165,t0,t1,t2,t4,t133]
def v254 := [t165,t0,t1,t2,t3,t4]
def v255 := [t134,t0,t1,t2,t3,t4]
theorem b124 : Ban 12 4 v122 := checkedSmall
theorem b125 : Ban 12 4 v123 := checkedSmall
theorem b126 : Ban 12 4 v124 := checkedSmall
theorem b127 : Ban 12 4 v125 := checkedSmall
theorem b128 : Ban 12 4 v126 := checkedSmall
theorem b129 : Ban 12 4 v127 := checkedSmall
theorem b130 : Ban 12 4 v128 := checkedSmall
theorem b131 : Ban 12 4 v129 := checkedSmall
theorem b132 : Ban 12 4 v130 := checkedSmall
theorem b133 : Ban 12 4 v131 := checkedSmall
theorem b134 : Ban 12 4 v132 := checkedSmall
theorem b135 : Ban 12 4 v133 := checkedSmall
theorem b136 : Ban 12 4 v134 := checkedSmall
theorem b137 : Ban 12 4 v135 := checkedSmall
theorem b138 : Ban 12 4 v136 := checkedSmall
theorem b139 : Ban 12 4 v137 := checkedSmall
theorem b140 : Ban 12 4 v138 := checkedSmall
theorem b141 : Ban 12 4 v139 := checkedSmall
theorem b142 : Ban 12 4 v140 := checkedSmall
theorem b143 : Ban 12 4 v141 := checkedSmall
theorem b144 : Ban 12 4 v142 := checkedSmall
theorem b145 : Ban 12 4 v143 := checkedSmall
theorem b146 : Ban 12 4 v144 := checkedSmall
theorem b147 : Ban 12 4 v145 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b148 : Ban 12 5 v121 := viaBranch (ws := [v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145]) (consBan b124 (consBan b125 (consBan b126 (consBan b127 (consBan b128 (consBan b129 (consBan b130 (consBan b131 (consBan b132 (consBan b133 (consBan b134 (consBan b135 (consBan b136 (consBan b137 (consBan b138 (consBan b139 (consBan b140 (consBan b141 (consBan b142 (consBan b143 (consBan b144 (consBan b145 (consBan b146 (consBan b147 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b149 : Ban 12 5 v146 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w0 : Wide 12 5 v146 := viaSub (ws := [v121,v146]) (consBan b148 (consBan b149 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b0 : Ban 25 5 v2 := smallByCut p59_313 w0
theorem b1 : Ban 25 5 v3 := smallByCut p59_313 w0
theorem b2 : Ban 25 5 v4 := checkedSmall
theorem b3 : Ban 25 5 v5 := checkedSmall
theorem b4 : Ban 25 5 v6 := checkedSmall
theorem b5 : Ban 25 5 v7 := checkedSmall
theorem b6 : Ban 25 5 v8 := checkedSmall
theorem b7 : Ban 25 5 v9 := checkedSmall
theorem b152 : Ban 10 4 v148 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w1 : Wide 10 4 v148 := viaSub (ws := [v148]) (consBan b152 (nilBan 10 4)) (by decide) (by decide +kernel)
theorem b8 : Ban 25 5 v10 := smallByCut p59_43 w1
theorem b9 : Ban 25 5 v11 := checkedSmall
theorem b10 : Ban 25 5 v12 := checkedSmall
theorem b11 : Ban 25 5 v13 := smallByCut p59_43 w1
theorem b12 : Ban 25 5 v14 := smallByCut p59_27 w1
theorem b13 : Ban 25 5 v15 := checkedSmall
theorem b14 : Ban 25 5 v16 := checkedSmall
theorem b15 : Ban 25 5 v17 := smallByCut p59_27 w1
theorem b16 : Ban 25 5 v18 := smallByCut p59_313 w0
theorem b17 : Ban 25 5 v19 := smallByCut p59_313 w0
theorem b18 : Ban 25 5 v20 := smallByCut p59_313 w0
theorem b19 : Ban 25 5 v21 := checkedSmall
theorem b20 : Ban 25 5 v22 := checkedSmall
theorem b21 : Ban 25 5 v23 := smallByCut p59_313 w0
theorem b22 : Ban 25 5 v24 := smallByCut p59_313 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b23 : Ban 25 6 v1 := viaBranch (ws := [v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24]) (consBan b0 (consBan b1 (consBan b2 (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b10 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (consBan b19 (consBan b20 (consBan b21 (consBan b22 (nilBan 25 5)))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b24 : Ban 25 5 v26 := smallByCut p59_313 w0
theorem b25 : Ban 25 5 v27 := checkedSmall
theorem b26 : Ban 25 5 v28 := smallByCut p59_313 w0
theorem b27 : Ban 25 5 v29 := smallByCut p59_313 w0
theorem b28 : Ban 25 5 v30 := smallByCut p59_313 w0
theorem b29 : Ban 25 5 v31 := smallByCut p59_313 w0
theorem b30 : Ban 25 5 v32 := checkedSmall
theorem b31 : Ban 25 5 v33 := checkedSmall
theorem b32 : Ban 25 5 v34 := checkedSmall
theorem b33 : Ban 25 5 v35 := smallByCut p59_313 w0
theorem b34 : Ban 25 5 v36 := smallByCut p59_43 w1
theorem b35 : Ban 25 5 v37 := smallByCut p59_313 w0
theorem b36 : Ban 25 5 v38 := smallByCut p59_43 w1
theorem b37 : Ban 25 5 v39 := smallByCut p59_313 w0
theorem b38 : Ban 25 5 v40 := checkedSmall
theorem b39 : Ban 25 5 v41 := checkedSmall
theorem b40 : Ban 25 5 v42 := checkedSmall
theorem b41 : Ban 25 5 v43 := smallByCut p59_43 w1
theorem b42 : Ban 25 5 v44 := smallByCut p59_27 w1
theorem b43 : Ban 25 5 v45 := smallByCut p59_313 w0
theorem b44 : Ban 25 5 v46 := smallByCut p59_27 w1
theorem b45 : Ban 25 5 v47 := smallByCut p59_313 w0
theorem b46 : Ban 25 5 v48 := checkedSmall
theorem b47 : Ban 25 5 v49 := checkedSmall
theorem b48 : Ban 25 5 v50 := checkedSmall
theorem b49 : Ban 25 5 v51 := smallByCut p59_27 w1
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b50 : Ban 25 6 v25 := viaBranch (ws := [v18,v19,v20,v26,v27,v5,v3,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51]) (consBan b16 (consBan b17 (consBan b18 (consBan b24 (consBan b25 (consBan b3 (consBan b1 (consBan b26 (consBan b27 (consBan b28 (consBan b29 (consBan b30 (consBan b31 (consBan b32 (consBan b33 (consBan b34 (consBan b35 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (consBan b40 (consBan b41 (consBan b42 (consBan b43 (consBan b44 (consBan b45 (consBan b46 (consBan b47 (consBan b48 (consBan b49 (nilBan 25 5)))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b51 : Ban 25 6 v3 := smallByCut p59_313 w0
theorem b52 : Ban 25 6 v5 := checkedSmall
theorem b53 : Ban 25 5 v53 := checkedSmall
theorem b54 : Ban 25 5 v54 := checkedSmall
theorem b55 : Ban 25 5 v55 := smallByCut p59_313 w0
theorem b56 : Ban 25 5 v56 := smallByCut p59_313 w0
theorem b57 : Ban 25 5 v57 := checkedSmall
theorem b58 : Ban 25 5 v58 := checkedSmall
theorem b59 : Ban 25 5 v59 := checkedSmall
theorem b60 : Ban 25 5 v60 := smallByCut p59_43 w1
theorem b61 : Ban 25 5 v61 := checkedSmall
theorem b62 : Ban 25 5 v62 := checkedSmall
theorem b63 : Ban 25 5 v63 := smallByCut p59_43 w1
theorem b64 : Ban 25 5 v64 := smallByCut p59_27 w1
theorem b65 : Ban 25 5 v65 := checkedSmall
theorem b66 : Ban 25 5 v66 := checkedSmall
theorem b67 : Ban 25 5 v67 := smallByCut p59_27 w1
theorem b68 : Ban 25 5 v68 := checkedSmall
theorem b69 : Ban 25 5 v69 := checkedSmall
theorem b70 : Ban 25 5 v70 := checkedSmall
theorem b71 : Ban 25 5 v71 := checkedSmall
theorem b72 : Ban 25 5 v72 := checkedSmall
theorem b73 : Ban 25 5 v73 := checkedSmall
theorem b74 : Ban 25 5 v74 := checkedSmall
theorem b75 : Ban 25 5 v75 := checkedSmall
theorem b76 : Ban 25 5 v76 := checkedSmall
theorem b77 : Ban 25 5 v77 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b78 : Ban 25 6 v52 := viaBranch (ws := [v53,v54,v6,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v21,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77]) (consBan b53 (consBan b54 (consBan b4 (consBan b55 (consBan b56 (consBan b57 (consBan b58 (consBan b59 (consBan b60 (consBan b61 (consBan b62 (consBan b63 (consBan b64 (consBan b65 (consBan b66 (consBan b67 (consBan b19 (consBan b68 (consBan b69 (consBan b70 (consBan b71 (consBan b72 (consBan b73 (consBan b74 (consBan b75 (consBan b76 (consBan b77 (nilBan 25 5)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b79 : Ban 25 5 v79 := checkedSmall
theorem b80 : Ban 25 5 v80 := checkedSmall
theorem b81 : Ban 25 5 v81 := checkedSmall
theorem b82 : Ban 25 5 v82 := checkedSmall
theorem b83 : Ban 25 5 v83 := checkedSmall
theorem b84 : Ban 25 5 v84 := checkedSmall
theorem b85 : Ban 25 5 v85 := smallByCut p59_313 w0
theorem b86 : Ban 25 5 v86 := smallByCut p59_313 w0
theorem b87 : Ban 25 5 v87 := checkedSmall
theorem b88 : Ban 25 5 v88 := smallByCut p59_43 w1
theorem b89 : Ban 25 5 v89 := checkedSmall
theorem b90 : Ban 25 5 v90 := smallByCut p59_43 w1
theorem b91 : Ban 25 5 v91 := checkedSmall
theorem b92 : Ban 25 5 v92 := checkedSmall
theorem b93 : Ban 25 5 v93 := checkedSmall
theorem b94 : Ban 25 5 v94 := checkedSmall
theorem b95 : Ban 25 5 v95 := smallByCut p59_43 w1
theorem b96 : Ban 25 5 v96 := smallByCut p59_27 w1
theorem b97 : Ban 25 5 v97 := checkedSmall
theorem b98 : Ban 25 5 v98 := smallByCut p59_27 w1
theorem b99 : Ban 25 5 v99 := checkedSmall
theorem b100 : Ban 25 5 v100 := checkedSmall
theorem b101 : Ban 25 5 v101 := checkedSmall
theorem b102 : Ban 25 5 v102 := checkedSmall
theorem b103 : Ban 25 5 v103 := smallByCut p59_27 w1
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b104 : Ban 25 6 v78 := viaBranch (ws := [v69,v70,v71,v79,v80,v59,v81,v82,v83,v31,v84,v85,v86,v87,v54,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103]) (consBan b69 (consBan b70 (consBan b71 (consBan b79 (consBan b80 (consBan b59 (consBan b81 (consBan b82 (consBan b83 (consBan b29 (consBan b84 (consBan b85 (consBan b86 (consBan b87 (consBan b54 (consBan b88 (consBan b89 (consBan b90 (consBan b91 (consBan b92 (consBan b93 (consBan b94 (consBan b95 (consBan b96 (consBan b97 (consBan b98 (consBan b99 (consBan b100 (consBan b101 (consBan b102 (consBan b103 (nilBan 25 5)))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b105 : Ban 25 5 v52 := checkedSmall
theorem b106 : Ban 25 5 v104 := smallByCut p59_313 w0
theorem b107 : Ban 25 5 v105 := smallByCut p59_313 w0
theorem b108 : Ban 25 5 v106 := checkedSmall
theorem b109 : Ban 25 5 v78 := checkedSmall
theorem b110 : Ban 25 5 v107 := smallByCut p59_43 w1
theorem b111 : Ban 25 5 v108 := checkedSmall
theorem b112 : Ban 25 5 v109 := checkedSmall
theorem b113 : Ban 25 5 v110 := smallByCut p59_43 w1
theorem b114 : Ban 25 5 v111 := smallByCut p59_27 w1
theorem b115 : Ban 25 5 v112 := checkedSmall
theorem b116 : Ban 25 5 v113 := checkedSmall
theorem b117 : Ban 25 5 v114 := smallByCut p59_27 w1
theorem b118 : Ban 25 5 v115 := checkedSmall
theorem b119 : Ban 25 5 v116 := checkedSmall
theorem b120 : Ban 25 5 v117 := checkedSmall
theorem b121 : Ban 25 5 v118 := checkedSmall
theorem b122 : Ban 25 5 v119 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b123 : Ban 25 6 v54 := viaBranch (ws := [v53,v52,v8,v104,v105,v106,v79,v78,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119]) (consBan b53 (consBan b105 (consBan b6 (consBan b106 (consBan b107 (consBan b108 (consBan b79 (consBan b109 (consBan b110 (consBan b111 (consBan b112 (consBan b113 (consBan b114 (consBan b115 (consBan b116 (consBan b117 (consBan b118 (consBan b119 (consBan b120 (consBan b121 (consBan b122 (nilBan 25 5)))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b150 : Ban 25 6 v120 := smallByCut p59_313 w0
theorem b151 : Ban 25 6 v59 := viaPerm map59_2 map59_2 b150 (by decide +kernel) (by decide +kernel)
theorem b153 : Ban 25 6 v147 := smallByCut p59_43 w1
theorem b154 : Ban 25 6 v149 := checkedSmall
theorem b155 : Ban 25 6 v150 := checkedSmall
theorem b156 : Ban 25 6 v151 := smallByCut p59_43 w1
theorem b157 : Ban 25 6 v152 := smallByCut p59_27 w1
theorem b158 : Ban 25 6 v153 := checkedSmall
theorem b159 : Ban 25 6 v154 := checkedSmall
theorem b160 : Ban 25 6 v155 := smallByCut p59_27 w1
theorem b161 : Ban 25 6 v156 := viaPerm map59_2 map59_2 b78 (by decide +kernel) (by decide +kernel)
theorem b162 : Ban 25 6 v157 := viaPerm map59_2 map59_2 b104 (by decide +kernel) (by decide +kernel)
theorem b163 : Ban 25 6 v158 := viaPerm map59_2 map59_2 b123 (by decide +kernel) (by decide +kernel)
theorem b164 : Ban 25 6 v159 := smallByCut p59_43 w1
theorem b165 : Ban 25 6 v160 := checkedSmall
theorem b166 : Ban 25 6 v161 := checkedSmall
theorem b167 : Ban 25 6 v162 := smallByCut p59_43 w1
theorem b168 : Ban 25 6 v163 := smallByCut p59_27 w1
theorem b169 : Ban 25 6 v164 := checkedSmall
theorem b170 : Ban 25 6 v165 := checkedSmall
theorem b171 : Ban 25 6 v166 := smallByCut p59_27 w1
theorem b172 : Ban 25 6 v167 := smallByCut p59_43 w1
theorem b173 : Ban 25 5 v169 := checkedSmall
theorem b174 : Ban 25 5 v170 := checkedSmall
theorem b175 : Ban 25 5 v171 := checkedSmall
theorem b176 : Ban 25 5 v172 := checkedSmall
theorem b177 : Ban 25 5 v173 := checkedSmall
theorem b178 : Ban 25 5 v174 := checkedSmall
theorem b179 : Ban 25 5 v175 := checkedSmall
theorem b180 : Ban 25 5 v176 := checkedSmall
theorem b181 : Ban 25 5 v177 := checkedSmall
theorem b182 : Ban 25 5 v178 := smallByCut p59_313 w0
theorem b183 : Ban 25 5 v179 := checkedSmall
theorem b184 : Ban 25 5 v180 := smallByCut p59_313 w0
theorem b185 : Ban 25 5 v181 := smallByCut p59_313 w0
theorem b186 : Ban 25 5 v182 := checkedSmall
theorem b187 : Ban 25 5 v183 := smallByCut p59_43 w1
theorem b188 : Ban 25 5 v184 := smallByCut p59_43 w1
theorem b189 : Ban 25 5 v185 := smallByCut p59_43 w1
theorem b190 : Ban 25 5 v186 := checkedSmall
theorem b191 : Ban 25 5 v187 := smallByCut p59_43 w1
theorem b192 : Ban 25 5 v188 := smallByCut p59_43 w1
theorem b193 : Ban 25 5 v189 := smallByCut p59_43 w1
theorem b194 : Ban 25 5 v190 := checkedSmall
theorem b195 : Ban 25 5 v191 := smallByCut p59_43 w1
theorem b196 : Ban 25 5 v192 := smallByCut p59_27 w1
theorem b197 : Ban 25 5 v193 := checkedSmall
theorem b198 : Ban 25 5 v194 := smallByCut p59_27 w1
theorem b199 : Ban 25 5 v195 := checkedSmall
theorem b200 : Ban 25 5 v196 := checkedSmall
theorem b201 : Ban 25 5 v197 := checkedSmall
theorem b202 : Ban 25 5 v198 := checkedSmall
theorem b203 : Ban 25 5 v199 := smallByCut p59_27 w1
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b204 : Ban 25 6 v168 := viaBranch (ws := [v169,v170,v171,v91,v109,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199]) (consBan b173 (consBan b174 (consBan b175 (consBan b91 (consBan b112 (consBan b176 (consBan b177 (consBan b178 (consBan b179 (consBan b180 (consBan b181 (consBan b182 (consBan b183 (consBan b184 (consBan b185 (consBan b186 (consBan b187 (consBan b188 (consBan b189 (consBan b190 (consBan b191 (consBan b192 (consBan b193 (consBan b194 (consBan b195 (consBan b196 (consBan b197 (consBan b198 (consBan b199 (consBan b200 (consBan b201 (consBan b202 (consBan b203 (nilBan 25 5)))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b205 : Ban 25 5 v201 := checkedSmall
theorem b206 : Ban 25 5 v202 := checkedSmall
theorem b207 : Ban 25 5 v203 := checkedSmall
theorem b208 : Ban 25 5 v204 := checkedSmall
theorem b209 : Ban 25 5 v205 := smallByCut p59_313 w0
theorem b210 : Ban 25 5 v206 := smallByCut p59_313 w0
theorem b211 : Ban 25 5 v207 := checkedSmall
theorem b212 : Ban 25 5 v208 := smallByCut p59_27 w1
theorem b213 : Ban 25 5 v209 := smallByCut p59_27 w1
theorem b214 : Ban 25 5 v210 := smallByCut p59_43 w1
theorem b215 : Ban 25 5 v211 := checkedSmall
theorem b216 : Ban 25 5 v212 := checkedSmall
theorem b217 : Ban 25 5 v213 := smallByCut p59_43 w1
theorem b218 : Ban 25 5 v214 := checkedSmall
theorem b219 : Ban 25 5 v215 := smallByCut p59_27 w1
theorem b220 : Ban 25 5 v216 := smallByCut p59_27 w1
theorem b221 : Ban 25 5 v217 := checkedSmall
theorem b222 : Ban 25 5 v218 := smallByCut p59_27 w1
theorem b223 : Ban 25 5 v219 := checkedSmall
theorem b224 : Ban 25 5 v220 := smallByCut p59_27 w1
theorem b225 : Ban 25 5 v221 := smallByCut p59_27 w1
theorem b226 : Ban 25 5 v222 := smallByCut p59_27 w1
theorem b227 : Ban 25 5 v223 := smallByCut p59_27 w1
theorem b228 : Ban 25 5 v224 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b229 : Ban 25 6 v200 := viaBranch (ws := [v66,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224]) (consBan b66 (consBan b205 (consBan b206 (consBan b207 (consBan b208 (consBan b209 (consBan b210 (consBan b211 (consBan b212 (consBan b213 (consBan b214 (consBan b215 (consBan b216 (consBan b217 (consBan b218 (consBan b219 (consBan b220 (consBan b221 (consBan b222 (consBan b223 (consBan b224 (consBan b225 (consBan b226 (consBan b227 (consBan b228 (nilBan 25 5)))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b230 : Ban 25 6 v189 := viaPerm map59_1 map59_1 b229 (by decide +kernel) (by decide +kernel)
theorem b231 : Ban 25 6 v188 := smallByCut p59_43 w1
theorem b232 : Ban 25 6 v209 := smallByCut p59_27 w1
theorem b233 : Ban 25 6 v215 := viaPerm map59_1 map59_1 b204 (by decide +kernel) (by decide +kernel)
theorem b234 : Ban 25 6 v225 := smallByCut p59_27 w1
theorem b235 : Ban 25 6 v226 := smallByCut p59_27 w1
theorem b236 : Ban 25 5 v228 := smallByCut p59_43 w1
theorem b237 : Ban 25 5 v229 := checkedSmall
theorem b238 : Ban 25 5 v230 := smallByCut p59_27 w1
theorem b239 : Ban 25 5 v231 := checkedSmall
theorem b240 : Ban 25 5 v232 := checkedSmall
theorem b241 : Ban 25 5 v233 := checkedSmall
theorem b242 : Ban 25 5 v234 := checkedSmall
theorem b243 : Ban 25 5 v235 := checkedSmall
theorem b244 : Ban 25 5 v236 := smallByCut p59_43 w1
theorem b245 : Ban 25 5 v237 := checkedSmall
theorem b246 : Ban 25 5 v238 := smallByCut p59_27 w1
theorem b247 : Ban 25 5 v239 := checkedSmall
theorem b248 : Ban 25 5 v240 := checkedSmall
theorem b249 : Ban 25 5 v241 := smallByCut p59_313 w0
theorem b250 : Ban 25 5 v242 := checkedSmall
theorem b251 : Ban 25 5 v243 := smallByCut p59_313 w0
theorem b252 : Ban 25 5 v244 := smallByCut p59_43 w1
theorem b253 : Ban 25 5 v245 := checkedSmall
theorem b254 : Ban 25 5 v246 := smallByCut p59_27 w1
theorem b255 : Ban 25 5 v247 := checkedSmall
theorem b256 : Ban 25 5 v248 := checkedSmall
theorem b257 : Ban 25 5 v249 := smallByCut p59_27 w1
theorem b258 : Ban 25 5 v250 := smallByCut p59_27 w1
theorem b259 : Ban 25 5 v251 := smallByCut p59_27 w1
theorem b260 : Ban 25 5 v252 := smallByCut p59_43 w1
theorem b261 : Ban 25 5 v253 := smallByCut p59_27 w1
theorem b262 : Ban 25 5 v254 := smallByCut p59_27 w1
theorem b263 : Ban 25 5 v255 := smallByCut p59_27 w1
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b264 : Ban 25 6 v227 := viaBranch (ws := [v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v190,v244,v245,v246,v247,v195,v212,v248,v249,v250,v251,v252,v253,v254,v255]) (consBan b236 (consBan b237 (consBan b238 (consBan b239 (consBan b240 (consBan b241 (consBan b242 (consBan b243 (consBan b244 (consBan b245 (consBan b246 (consBan b247 (consBan b248 (consBan b249 (consBan b250 (consBan b251 (consBan b194 (consBan b252 (consBan b253 (consBan b254 (consBan b255 (consBan b199 (consBan b216 (consBan b256 (consBan b257 (consBan b258 (consBan b259 (consBan b260 (consBan b261 (consBan b262 (consBan b263 (nilBan 25 5)))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b266 : Ban 25 6 v255 := smallByCut p59_43 w1
theorem b265 : Ban 25 6 v254 := smallByCut p59_27 w1
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b267 : Ban 25 7 v0 := viaBranch (ws := [v1,v25,v3,v5,v52,v78,v54,v59,v147,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v120,v159,v160,v161,v162,v163,v164,v165,v166,v167,v168,v189,v188,v209,v215,v200,v225,v226,v227,v255,v254]) (consBan b23 (consBan b50 (consBan b51 (consBan b52 (consBan b78 (consBan b104 (consBan b123 (consBan b151 (consBan b153 (consBan b154 (consBan b155 (consBan b156 (consBan b157 (consBan b158 (consBan b159 (consBan b160 (consBan b161 (consBan b162 (consBan b163 (consBan b150 (consBan b164 (consBan b165 (consBan b166 (consBan b167 (consBan b168 (consBan b169 (consBan b170 (consBan b171 (consBan b172 (consBan b204 (consBan b230 (consBan b231 (consBan b232 (consBan b233 (consBan b229 (consBan b234 (consBan b235 (consBan b264 (consBan b266 (consBan b265 (nilBan 25 6))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem verifiedPin : Wide 25 7 v0 := widen (by decide +kernel) b267
end PEqualNP.Outside.L_meta_12865.Support

namespace PEqualNP.Outside.L_meta_12865.Data
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12865.Support
def target (x : Fin 6 → Bool) := Nat.testBit (4008242912 * 2 ^ 32 + 4007692416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def posBits : ℕ := 0x1faeb9e73cf3cebaaaaa9a696da69a65964b2cb
def negBits : ℕ := 0xf8cb8c72c634e3a222a88494d848a61124a243
def sample (bank : ℕ) (i : Fin 26) (j : Fin 6) := bank.testBit (6*i.val+j.val)
def inputs : List ℕ := [0x8bc386e7f1e3f,0xa5d8b179fe3c7,0x2000000,0x502d5b9e1ffff,0x7e80ec1fe03f8,0x7f76001fffc00]
def seeds : List Wire := [(false,0x8bc386e7f1e3f),(false,0xa5d8b179fe3c7),(false,0x2000000),(false,0x502d5b9e1ffff),(false,0x7e80ec1fe03f8),(false,0x7f76001fffc00)]
set_option maxHeartbeats 10000000 in
theorem listed : ∀ i : Fin 26, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (26+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 26, target (sample posBits i)=true ∧ target (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 26, ∀ b∈inputs, b.testBit i.val≠b.testBit (26+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 26 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
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
    have diff : read i out=read (26+i) out := by
      change (out.1 != out.2.testBit i) = (out.1 != out.2.testBit (26+i))
      rw [same]
    have p := ev i;have n := ev (26+i)
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
def restrictRows : Projection 26 25 := pick (List.range 25) (by decide) (by decide) (by decide)
set_option maxHeartbeats 8000000 in
theorem core_floor : Wide 25 7 restricted := verifiedPin
theorem six_floor : Ban 26 8 inputs := viaCut restrictRows core_floor (by decide) (by decide +kernel) (by decide +kernel)
def witness : Circuit := ⟨[⟨.and,[0,1]⟩, ⟨.or,[0,1]⟩, ⟨.or,[2,3]⟩, ⟨.and,[7,8]⟩, ⟨.and,[6,4]⟩, ⟨.or,[9,10]⟩, ⟨.or,[6,4]⟩, ⟨.and,[11,5]⟩, ⟨.and,[9,12]⟩, ⟨.or,[14,13]⟩],15⟩
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
end PEqualNP.Outside.L_meta_12865.Data

theorem PEqualNP.Outside.L_meta_12865 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008242912 * 2 ^ 32 + 4007692416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008242912 * 2 ^ 32 + 4007692416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_12865.Data.mono_enough
