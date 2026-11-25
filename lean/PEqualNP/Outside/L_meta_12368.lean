import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12368.Support

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

def t0 := 0x10da45863f49f
def t1 := 0x462c5299c78e7
def t2 := 0x10b468361f8f07
def t3 := 0x2a001287e00ff8
def t4 := 0x3fdb0007fff000
def v0 := [t0,t1,t2,t3,t4]
def t5 := 0x8408007087
def v1 := [t5,t0,t1,t2,t3,t4]
def t6 := 0x42010038407
def v2 := [t6,t0,t1,t2,t3,t4]
def t7 := 0x1098448607098
def v3 := [t6,t7,t1,t2,t3,t4]
def v4 := [t7,t0,t1,t2,t3,t4]
def v5 := [t6,t7,t0,t1,t2,t3,t4]
def t8 := 0x7
def v6 := [t8,t0,t1,t2,t3,t4]
def v7 := [t8,t6,t0,t1,t2,t3,t4]
def t9 := 0x466e5399ffce7
def v8 := [t0,t1,t9,t2,t3,t4]
def t10 := 0x250ff8
def t11 := 0x48b49f
def t12 := 0x8a58e7
def t13 := 0xd06f07
def v9 := [t10,t11,t12,t13]
def t14 := 0x81087
def v10 := [t14,t10,t11,t12,t13]
def t15 := 0xcafcff
def v11 := [t10,t11,t12,t15,t13]
def t16 := 0x40a418
def v12 := [t10,t16,t11,t12,t13]
def t17 := 0x824860
def v13 := [t10,t11,t17,t12,t13]
def t18 := 0x402407
def v14 := [t10,t18,t11,t12,t13]
def t19 := 0xd8ff9f
def v15 := [t10,t11,t12,t13,t19]
def t20 := 0x89098
def v16 := [t20,t10,t11,t12,t13]
def t21 := 0x904b00
def v17 := [t10,t11,t12,t21,t13]
def t22 := 0x498
def v18 := [t22,t10,t11,t12,t13]
def t23 := 0x6dbfff
def v19 := [t10,t11,t23,t12,t13]
def t24 := 0x48b007
def v20 := [t10,t24,t11,t12,t13]
def t25 := 0x250b60
def v21 := [t25,t10,t11,t12,t13]
def t26 := 0x804807
def v22 := [t10,t11,t26,t12,t13]
def t27 := 0xda7fe7
def v23 := [t10,t11,t12,t13,t27]
def t28 := 0xa10e0
def v24 := [t28,t10,t11,t12,t13]
def t29 := 0x502700
def v25 := [t10,t11,t29,t12,t13]
def t30 := 0x8e0
def v26 := [t30,t10,t11,t12,t13]
def t31 := 0xaf5fff
def v27 := [t10,t11,t12,t31,t13]
def t32 := 0x8a5007
def v28 := [t10,t11,t32,t12,t13]
def t33 := 0x250718
def v29 := [t33,t10,t11,t12,t13]
def t34 := 0xf00
def v30 := [t34,t10,t11,t12,t13]
def t35 := 0xf56fff
def v31 := [t10,t11,t12,t13,t35]
def t36 := 0xd06007
def v32 := [t10,t11,t12,t36,t13]
def t37 := 0x2500f8
def v33 := [t37,t10,t11,t12,t13]
def t38 := 0xca7ce7
def v34 := [t10,t11,t12,t38,t13]
def p31_15 : Projection 27 12 := pick [0,1,2,3,4,5,6,7,8,9,10,11] rfl (by decide +kernel) (by decide)
def v35 := [t6,t0,t1,t9,t2,t3,t4]
def t39 := 0x42010038400
def v36 := [t39,t0,t1,t2,t3,t4]
def v37 := [t39,t6,t0,t1,t2,t3,t4]
def t40 := 0x462c5299c78e0
def v38 := [t0,t40,t1,t2,t3,t4]
def v39 := [t6,t0,t40,t1,t2,t3,t4]
def t41 := 0x10b048261c0b00
def v40 := [t6,t0,t1,t41,t3,t4]
def v41 := [t0,t1,t41,t2,t3,t4]
def v42 := [t6,t0,t1,t41,t2,t3,t4]
def t42 := 0x400
def v43 := [t42,t0,t1,t2,t3,t4]
def v44 := [t42,t6,t0,t1,t2,t3,t4]
def t43 := 0x2a043297e38fff
def v45 := [t0,t1,t2,t3,t43,t4]
def t44 := 0x2a00968fe07fff
def v46 := [t0,t1,t2,t3,t44,t4]
def t45 := 0xdb1ff
def t46 := 0x62de3f
def t47 := 0xb46fc7
def t48 := 0xdb0ff8
def v47 := [t45,t46,t47,t48]
def t49 := 0x903f
def v48 := [t49,t45,t46,t47,t48]
def t50 := 0x6fffff
def v49 := [t45,t46,t50,t47,t48]
def t51 := 0xd21c0
def v50 := [t51,t45,t46,t47,t48]
def t52 := 0x624e00
def v51 := [t45,t52,t46,t47,t48]
def t53 := 0x421c7
def v52 := [t53,t45,t46,t47,t48]
def t54 := 0xbdffff
def v53 := [t45,t46,t47,t54,t48]
def t55 := 0x99038
def v54 := [t55,t45,t46,t47,t48]
def t56 := 0xb04e00
def v55 := [t45,t46,t56,t47,t48]
def t57 := 0x901f8
def v56 := [t57,t45,t46,t47,t48]
def t58 := 0xdfbfff
def v57 := [t45,t46,t47,t48,t58]
def t59 := 0x4b007
def v58 := [t59,t45,t46,t47,t48]
def t60 := 0xd20e00
def v59 := [t45,t46,t47,t60,t48]
def t61 := 0x204e07
def v60 := [t45,t61,t46,t47,t48]
def t62 := 0xf6ffff
def v61 := [t45,t46,t47,t48,t62]
def t63 := 0x429038
def v62 := [t45,t63,t46,t47,t48]
def t64 := 0x9421c0
def v63 := [t45,t46,t64,t47,t48]
def t65 := 0x420e38
def v64 := [t45,t65,t46,t47,t48]
def t66 := 0xfbdfff
def v65 := [t45,t46,t47,t48,t66]
def t67 := 0x20d007
def v66 := [t45,t67,t46,t47,t48]
def t68 := 0x9901c0
def v67 := [t45,t46,t68,t47,t48]
def t69 := 0x900fc0
def v68 := [t45,t46,t69,t47,t48]
def t70 := 0xff6fff
def v69 := [t45,t46,t47,t48,t70]
def t71 := 0x246007
def v70 := [t45,t71,t46,t47,t48]
def t72 := 0x4b0038
def v71 := [t45,t72,t46,t47,t48]
def v72 := [t53,t55,t46,t47,t48]
def v73 := [t8,t45,t46,t47,t48]
def t73 := 0x66ffff
def v74 := [t45,t46,t73,t47,t48]
def t74 := 0x421c0
def v75 := [t74,t45,t46,t47,t48]
def t75 := 0x62de38
def v76 := [t45,t75,t46,t47,t48]
def v77 := [t53,t45,t46,t56,t48]
def t76 := 0x1c0
def v78 := [t76,t45,t46,t47,t48]
def t77 := 0xdf2fff
def v79 := [t45,t46,t47,t48,t77]
def t78 := 0x42007
def v80 := [t78,t45,t46,t47,t48]
def t79 := 0xdb0e38
def v81 := [t45,t46,t47,t79,t48]
def v82 := [t49,t53,t46,t47,t48]
def v83 := [t53,t52,t46,t47,t48]
def v84 := [t53,t46,t54,t48]
def v85 := [t53,t45,t46,t54,t48]
def v86 := [t53,t46,t47,t54,t48]
def v87 := [t53,t57,t46,t47,t48]
def v88 := [t53,t46,t47,t60,t48]
def v89 := [t53,t45,t61,t46,t48]
def v90 := [t53,t45,t63,t46,t48]
def v91 := [t53,t45,t46,t69,t48]
def v92 := [t53,t45,t72,t46,t48]
def map23_2 : Projection 12 12 := pick [1,0,2,6,7,8,3,4,5,9,11,10] rfl (by decide +kernel) (by decide)
def p31_23 : Projection 27 12 := pick [0,1,2,12,13,14,15,16,17,18,19,20] rfl (by decide +kernel) (by decide)
def map31_1 : Projection 27 27 := pick [1,0,2,3,4,8,9,10,5,6,7,11,15,16,17,12,13,14,18,20,19,21,22,25,26,23,24] rfl (by decide +kernel) (by decide)
def v93 := [t6,t0,t1,t2,t3,t43,t4]
def t80 := 0x42010038007
def v94 := [t80,t0,t1,t2,t3,t4]
def t81 := 0x1713f3
def t82 := 0x4b4cfc
def t83 := 0xa0af1f
def t84 := 0xfc0fe0
def v95 := [t81,t82,t83,t84]
def p31_27 : Projection 27 12 := pick [3,4,5,6,7,12,13,14,21,22,23,24] rfl (by decide +kernel) (by decide)
def v96 := [t80,t6,t0,t1,t2,t3,t4]
def t85 := 0x2a001287e00bf8
def v97 := [t0,t1,t2,t85,t3,t4]
def map31_2 : Projection 27 27 := pick [0,2,1,5,6,3,4,7,8,9,11,10,12,14,13,18,19,20,15,16,17,23,24,21,22,25,26] rfl (by decide +kernel) (by decide)
def v99 := [t6,t0,t1,t2,t85,t3,t4]
def t87 := 0x38000
def v100 := [t87,t0,t1,t2,t3,t4]
def v101 := [t87,t6,t0,t1,t2,t3,t4]
def t88 := 0x3fdf2017fff407
def v102 := [t0,t1,t2,t3,t4,t88]
def v103 := [t6,t0,t1,t2,t3,t4,t88]
def t89 := 0x42010000407
def v104 := [t89,t0,t1,t2,t3,t4]
def v105 := [t89,t6,t0,t1,t2,t3,t4]
def t90 := 0x3fdb0007fc7000
def v106 := [t0,t1,t2,t3,t90,t4]
def v107 := [t6,t0,t1,t2,t3,t90,t4]
def v108 := [t5,t6,t0,t1,t2,t3,t4]
def t91 := 0x56fe579fffcff
def v109 := [t6,t0,t1,t91,t2,t3,t4]
def t92 := 0x10d2050638418
def v110 := [t6,t92,t0,t1,t2,t3,t4]
def t93 := 0x46241219c0860
def v111 := [t6,t0,t93,t1,t2,t3,t4]
def t94 := 0x11bdec7e7fff9f
def v112 := [t6,t1,t94,t3,t4]
def v113 := [t8,t6,t1,t94,t3,t4]
def v114 := [t6,t1,t9,t94,t3,t4]
def v115 := [t39,t6,t1,t94,t3,t4]
def v116 := [t6,t40,t1,t94,t3,t4]
def t95 := 0x11b9cc6e7c7b98
def v117 := [t1,t95,t3,t4]
def t96 := 0xb9de38
def v118 := [t46,t96,t48]
def v119 := [t6,t1,t95,t3,t4]
def v120 := [t1,t95,t94,t3,t4]
def v121 := [t6,t1,t95,t94,t3,t4]
def v122 := [t42,t6,t1,t94,t3,t4]
def v123 := [t1,t94,t3,t43,t4]
def v124 := [t6,t1,t94,t3,t43,t4]
def v125 := [t80,t1,t94,t3,t4]
def v126 := [t80,t6,t1,t94,t3,t4]
def v127 := [t6,t1,t94,t85,t3,t4]
def v128 := [t87,t6,t1,t94,t3,t4]
def v129 := [t6,t1,t94,t3,t4,t88]
def v130 := [t89,t6,t1,t94,t3,t4]
def v131 := [t6,t1,t94,t3,t90,t4]
def t97 := 0x20c4281c7887
def v132 := [t6,t97,t1,t94,t3,t4]
def t98 := 0x15ffed7fffffff
def v133 := [t6,t1,t94,t98,t3,t4]
def t99 := 0x4420101800060
def v134 := [t6,t99,t1,t94,t3,t4]
def t100 := 0x119d2856638718
def v135 := [t6,t1,t100,t94,t3,t4]
def t101 := 0x18008e0
def v136 := [t101,t6,t1,t94,t3,t4]
def t102 := 0x2e62d7affc7fff
def v137 := [t6,t1,t94,t3,t102,t4]
def t103 := 0x462c5281c7007
def v138 := [t6,t103,t1,t94,t3,t4]
def t104 := 0x2a001286600718
def v139 := [t6,t1,t94,t104,t3,t4]
def t105 := 0x44200019c7000
def v140 := [t6,t105,t1,t94,t3,t4]
def t106 := 0x3ffbc52ffff8e7
def v141 := [t6,t1,t94,t3,t4,t106]
def t107 := 0x20c5280008e7
def v142 := [t6,t107,t1,t94,t3,t4]
def t108 := 0x3b990006638000
def v143 := [t6,t1,t94,t3,t108,t4]
def t109 := 0x6600f98
def v144 := [t109,t6,t1,t94,t3,t4]
def t110 := 0x3bbdfeffffffff
def v145 := [t6,t1,t94,t3,t110,t4]
def t111 := 0x11bdec781ff007
def v146 := [t6,t1,t111,t94,t3,t4]
def t112 := 0x2a001281800060
def v147 := [t6,t1,t94,t112,t3,t4]
def t113 := 0x119900067ff000
def v148 := [t6,t1,t113,t94,t3]
def v149 := [t6,t1,t113,t94,t3,t4]
def t114 := 0x3fffec7fffff9f
def v150 := [t6,t1,t94,t3,t4,t114]
def t115 := 0x24ec78000f9f
def v151 := [t6,t115,t1,t94,t3]
def v152 := [t6,t115,t1,t94,t3,t4]
def t116 := 0x2e420001800000
def v153 := [t6,t1,t94,t3,t116,t4]
def t117 := 0x2a000007e00000
def v154 := [t6,t1,t94,t117,t3,t4]
def t118 := 0x3fdb1287fffff8
def v155 := [t6,t1,t94,t3,t118]
def v156 := [t6,t1,t94,t3,t4,t118]
def t119 := 0x1280000ff8
def v157 := [t119,t6,t1,t94,t3,t4]
def t120 := 0x15db00001ff000
def v158 := [t6,t1,t94,t120,t3]
def v159 := [t6,t1,t94,t120,t3,t4]
def v160 := [t6,t0,t1,t94,t3,t4]
def v161 := [t6,t1,t2,t94,t3,t4]
def map31_5 : Projection 27 27 := pick [2,1,0,8,9,5,6,11,3,4,10,7,18,20,19,15,17,16,12,14,13,25,26,23,24,21,22] rfl (by decide +kernel) (by decide)
def v162 := [t6,t0,t1,t2,t94,t3,t4]
def t121 := 0x600498
def v163 := [t121,t6,t0,t1,t2,t3,t4]
def t122 := 0x2b0db6dfe3ffff
def v164 := [t6,t0,t1,t2,t3,t122,t4]
def t123 := 0x10da45803f007
def v165 := [t6,t123,t0,t1,t2,t3,t4]
def t124 := 0x2a001287800b60
def v166 := [t6,t0,t1,t2,t124,t3,t4]
def t125 := 0x109000063f000
def v167 := [t6,t125,t0,t1,t2,t3,t4]
def t126 := 0x3fdfa45ffff49f
def v168 := [t6,t0,t1,t2,t3,t4,t126]
def t127 := 0x4a45800049f
def v169 := [t6,t127,t0,t1,t2,t3,t4]
def t128 := 0x3ed200079c0000
def v170 := [t6,t0,t1,t2,t3,t128,t4]
def t129 := 0x2040201c0807
def v171 := [t6,t129,t0,t1,t2,t3,t4]
def t130 := 0x14f6ed3f9fffe7
def v172 := [t6,t0,t1,t2,t130,t3,t4]
def t131 := 0x44285098070e0
def v173 := [t6,t0,t131,t1,t2,t3,t4]
def t132 := 0x10942816038700
def v174 := [t6,t0,t1,t132,t2,t3,t4]
def v175 := [t101,t6,t0,t1,t2,t3,t4]
def v176 := [t6,t0,t1,t2,t3,t102,t4]
def v177 := [t6,t0,t103,t1,t2,t3,t4]
def v178 := [t6,t0,t1,t2,t104,t3,t4]
def v179 := [t6,t0,t105,t1,t2,t3,t4]
def v180 := [t6,t0,t1,t2,t3,t4,t106]
def v181 := [t6,t107,t0,t1,t2,t3,t4]
def v182 := [t6,t0,t1,t2,t3,t108,t4]
def t133 := 0x6000f00
def v183 := [t133,t6,t0,t1,t2,t3,t4]
def t134 := 0x3ab47ab7ff8fff
def v184 := [t6,t0,t1,t2,t3,t134,t4]
def t135 := 0x10b468301f8007
def v185 := [t6,t0,t1,t135,t2,t3,t4]
def t136 := 0x2a001281e000f8
def v186 := [t6,t0,t1,t2,t136,t3,t4]
def t137 := 0x109000061f8000
def v187 := [t6,t0,t1,t137,t2,t3,t4]
def t138 := 0x3fff6837ffff07
def v188 := [t6,t0,t1,t2,t3,t4,t138]
def t139 := 0x246830000f07
def v189 := [t6,t139,t0,t1,t2,t3,t4]
def t140 := 0x2f4b0001e07000
def v190 := [t6,t0,t1,t2,t3,t140,t4]
def v191 := [t6,t0,t1,t2,t117,t3,t4]
def v192 := [t6,t0,t1,t2,t3,t118]
def t141 := 0xfcafff
def v193 := [t81,t82,t83,t141]
def v194 := [t6,t0,t1,t2,t3,t4,t118]
def v195 := [t119,t6,t0,t1,t2,t3,t4]
def v196 := [t6,t0,t1,t2,t120,t3]
def t142 := 0x5c00e0
def v197 := [t81,t82,t142,t83]
def v198 := [t6,t0,t1,t2,t120,t3,t4]
def v199 := [t0,t1,t91,t2,t3,t4]
def v200 := [t5,t91,t2,t3,t4]
def v201 := [t5,t0,t91,t2,t3,t4]
def map31_3 : Projection 27 27 := pick [2,0,1,5,6,8,9,11,3,4,7,10,18,19,20,12,14,13,15,17,16,23,24,25,26,21,22] rfl (by decide +kernel) (by decide)
def map31_4 : Projection 27 27 := pick [1,2,0,8,9,3,4,10,5,6,11,7,15,17,16,18,20,19,12,13,14,25,26,21,22,23,24] rfl (by decide +kernel) (by decide)
def v202 := [t5,t1,t91,t2,t3,t4]
def v203 := [t5,t0,t1,t91,t2,t3,t4]
def v204 := [t92,t0,t91,t2,t3,t4]
def v205 := [t93,t1,t91,t2,t3,t4]
def p31_29 : Projection 27 12 := pick [3,4,8,9,10,15,16,17,21,22,25,26] rfl (by decide +kernel) (by decide)
def v206 := [t92,t0,t1,t91,t2,t3,t4]
def v207 := [t0,t93,t1,t91,t2,t3,t4]
def v208 := [t0,t93,t1,t2,t3,t4]
def v209 := [t0,t1,t91,t2,t94,t3,t4]
def v210 := [t7,t0,t1,t91,t2,t3,t4]
def v211 := [t0,t1,t91,t41,t2,t3,t4]
def v212 := [t121,t0,t1,t91,t2,t3,t4]
def v213 := [t1,t91,t2,t3,t122,t4]
def v214 := [t49,t50,t47,t48]
def v215 := [t49,t45,t50,t47,t48]
def v216 := [t49,t46,t50,t47,t48]
def v217 := [t51,t45,t50,t47,t48]
def v218 := [t52,t46,t50,t47,t48]
def t143 := 0x246fc7
def v219 := [t45,t143,t46,t48]
def v220 := [t45,t143,t46,t50,t48]
def v221 := [t45,t143,t46,t47,t48]
def t144 := 0xffffff
def v222 := [t45,t46,t47,t48,t144]
def t145 := 0x4b9038
def v223 := [t45,t145,t46,t48]
def v224 := [t45,t145,t46,t50,t48]
def v225 := [t45,t145,t46,t47,t48]
def t146 := 0x900000
def v226 := [t45,t46,t146,t47,t48]
def t147 := 0x4b0ff8
def v227 := [t45,t147,t46,t47]
def v228 := [t45,t147,t46,t50,t47]
def v229 := [t45,t147,t46,t47,t48]
def t148 := 0x24f007
def v230 := [t45,t148,t46,t47]
def v231 := [t45,t148,t46,t50,t47]
def v232 := [t45,t148,t46,t47,t48]
def v233 := [t0,t1,t91,t2,t3,t122,t4]
def v234 := [t123,t1,t91,t2,t3,t4]
def v235 := [t123,t0,t1,t91,t2,t3,t4]
def v236 := [t0,t1,t91,t2,t124,t3,t4]
def v237 := [t125,t0,t1,t91,t2,t3,t4]
def v238 := [t0,t1,t91,t2,t3,t4,t126]
def v239 := [t127,t0,t1,t91,t2,t3,t4]
def v240 := [t0,t1,t91,t2,t3,t128,t4]
def v241 := [t92,t0,t1,t2,t3,t4]
def v242 := [t129,t0,t1,t91,t2,t3,t4]
def v243 := [t0,t1,t91,t2,t130,t3,t4]
def v244 := [t0,t131,t1,t91,t2,t3,t4]
def v245 := [t0,t1,t91,t132,t2,t3,t4]
def v246 := [t101,t0,t1,t91,t2,t3,t4]
def v247 := [t0,t91,t2,t3,t102,t4]
def v248 := [t0,t1,t91,t2,t3,t102,t4]
def v249 := [t0,t103,t91,t2,t3,t4]
def v250 := [t0,t103,t1,t91,t2,t3,t4]
def v251 := [t0,t1,t91,t2,t104,t3,t4]
def v252 := [t0,t105,t1,t91,t2,t3,t4]
def v253 := [t0,t1,t91,t2,t3,t4,t106]
def v254 := [t107,t0,t1,t91,t2,t3,t4]
def v255 := [t0,t1,t91,t2,t3,t108,t4]
def t149 := 0x2460301f8c07
def v256 := [t149,t0,t1,t2,t3,t4]
def v257 := [t149,t0,t1,t91,t2,t3,t4]
def v258 := [t0,t1,t2,t98,t3,t4]
def v259 := [t0,t1,t91,t2,t98,t3,t4]
def t150 := 0x54b8549e070f8
def v260 := [t0,t1,t150,t2,t3,t4]
def v261 := [t0,t1,t150,t91,t2,t3,t4]
def t151 := 0x10900806000300
def v262 := [t0,t1,t151,t2,t3,t4]
def v263 := [t0,t1,t91,t151,t2,t3,t4]
def t152 := 0x1e00cf8
def v264 := [t152,t0,t1,t2,t3,t4]
def v265 := [t152,t0,t1,t91,t2,t3,t4]
def t153 := 0x2f6ff7ffffffff
def v266 := [t0,t1,t2,t3,t153,t4]
def v267 := [t0,t1,t91,t2,t3,t153,t4]
def t154 := 0x56fe5781ff007
def v268 := [t0,t1,t154,t2,t3,t4]
def v269 := [t0,t1,t154,t91,t2,t3,t4]
def t155 := 0x2a001286000300
def v270 := [t0,t1,t2,t155,t3,t4]
def v271 := [t0,t1,t91,t2,t155,t3,t4]
def t156 := 0x54b0001fff000
def v272 := [t0,t1,t156,t2,t3]
def v273 := [t0,t1,t156,t91,t2,t3]
def v274 := [t5,t156,t91,t2,t3]
def v275 := [t5,t0,t156,t91,t2,t3]
def v276 := [t5,t1,t156,t91,t2,t3]
def v277 := [t92,t0,t156,t91,t2,t3]
def v278 := [t93,t1,t156,t91,t2,t3]
def v279 := [t0,t93,t1,t156,t2,t3]
def v280 := [t1,t156,t91,t2,t3,t122]
def v281 := [t123,t1,t156,t91,t2,t3]
def v282 := [t92,t0,t1,t156,t2,t3]
def v283 := [t0,t156,t91,t2,t3,t102]
def v284 := [t0,t103,t156,t91,t2,t3]
def t157 := 0x24e578000cff
def v285 := [t157,t0,t1,t2,t3]
def v286 := [t157,t0,t1,t156,t2,t3]
def v287 := [t157,t0,t1,t91,t2,t3]
def t158 := 0x2f4b1287fffff8
def v288 := [t0,t1,t91,t2,t3,t158]
def t159 := 0x54b00001ff000
def v289 := [t0,t1,t159,t91,t2,t3]
def v290 := [t149,t0,t1,t156,t2,t3]
def v291 := [t0,t1,t156,t2,t98,t3]
def v292 := [t0,t1,t156,t150,t2,t3]
def v293 := [t0,t1,t156,t151,t2,t3]
def v294 := [t152,t0,t1,t156,t2,t3]
def v295 := [t0,t1,t156,t2,t3,t153]
def v296 := [t0,t1,t156,t154,t2,t3]
def v297 := [t0,t1,t156,t2,t155,t3]
def v298 := [t0,t1,t156,t2,t3,t4]
def v299 := [t0,t1,t156,t91,t2,t3,t4]
def t160 := 0x3fffe57ffffcff
def v300 := [t0,t1,t2,t3,t4,t160]
def v301 := [t0,t1,t91,t2,t3,t4,t160]
def v302 := [t59,t45,t148,t46,t47]
def t161 := 0x2df1ff
def v303 := [t45,t148,t161,t46,t47]
def t162 := 0x204000
def v304 := [t45,t162,t148,t46,t47]
def v305 := [t57,t45,t148,t46,t47]
def v306 := [t45,t67,t148,t46,t47]
def t163 := 0x66fe3f
def v307 := [t45,t148,t46,t163,t47]
def t164 := 0x42000
def v308 := [t164,t45,t148,t46,t47]
def v309 := [t45,t148,t65,t46,t47]
def v310 := [t45,t71,t148,t46,t47]
def t165 := 0xb4ffc7
def v311 := [t45,t148,t46,t47,t165]
def t166 := 0x9000
def v312 := [t166,t45,t148,t46,t47]
def v313 := [t45,t148,t46,t69,t47]
def v314 := [t49,t45,t148,t46,t47]
def v315 := [t51,t45,t148,t46,t47]
def v316 := [t45,t148,t52,t46,t47]
def v317 := [t53,t45,t148,t46,t47]
def v318 := [t45,t148,t46,t47,t54]
def v319 := [t55,t45,t148,t46,t47]
def v320 := [t45,t148,t46,t56,t47]
def v321 := [t45,t61,t148,t46,t47]
def v322 := [t45,t148,t46,t47,t62]
def v323 := [t45,t148,t63,t46,t47]
def v324 := [t45,t148,t46,t64,t47]
def v325 := [t45,t148,t147,t46,t47]
def v326 := [t49,t148,t50,t47]
def v327 := [t49,t45,t148,t50,t47]
def v328 := [t49,t148,t46,t50,t47]
def v329 := [t51,t45,t148,t50,t47]
def v330 := [t148,t52,t46,t50,t47]
def v331 := [t45,t143,t148,t46]
def v332 := [t45,t143,t148,t46,t50]
def v333 := [t45,t143,t148,t46,t47]
def v334 := [t45,t148,t46,t47,t144]
def v335 := [t45,t148,t145,t46]
def v336 := [t45,t148,t145,t46,t50]
def v337 := [t45,t148,t145,t46,t47]
def v338 := [t45,t148,t46,t146,t47]
def v339 := [t157,t0,t1,t2,t3,t4]
def t167 := 0x450cf
def t168 := 0x112333
def t169 := 0x428c3c
def t170 := 0xa80fc0
def v340 := [t167,t168,t169,t170]
def t171 := 0x3
def v341 := [t171,t167,t168,t169,t170]
def t172 := 0x1573ff
def v342 := [t167,t168,t172,t169,t170]
def t173 := 0x450cc
def v343 := [t173,t167,t168,t169,t170]
def t174 := 0x112330
def v344 := [t167,t174,t168,t169,t170]
def t175 := 0xc
def v345 := [t175,t167,t168,t169,t170]
def t176 := 0x46dcff
def v346 := [t167,t168,t169,t176,t170]
def t177 := 0x450c3
def v347 := [t177,t167,t168,t169,t170]
def t178 := 0x428c30
def v348 := [t167,t168,t178,t169,t170]
def t179 := 0xc0
def v349 := [t179,t167,t168,t169,t170]
def t180 := 0xac5fcf
def v350 := [t167,t168,t169,t170,t180]
def t181 := 0x4500f
def v351 := [t181,t167,t168,t169,t170]
def t182 := 0xa80f00
def v352 := [t167,t168,t169,t182,t170]
def t183 := 0x30
def v353 := [t183,t167,t168,t169,t170]
def t184 := 0x53af3f
def v354 := [t167,t168,t169,t184,t170]
def t185 := 0x112303
def v355 := [t167,t185,t168,t169,t170]
def t186 := 0x428c0c
def v356 := [t167,t168,t186,t169,t170]
def t187 := 0x300
def v357 := [t187,t167,t168,t169,t170]
def t188 := 0xb92ff3
def v358 := [t167,t168,t169,t170,t188]
def t189 := 0x112033
def v359 := [t167,t189,t168,t169,t170]
def t190 := 0xa80cc0
def v360 := [t167,t168,t169,t190,t170]
def t191 := 0xc00
def v361 := [t191,t167,t168,t169,t170]
def t192 := 0xea8ffc
def v362 := [t167,t168,t169,t170,t192]
def t193 := 0x42803c
def v363 := [t167,t168,t193,t169,t170]
def t194 := 0xa803c0
def v364 := [t167,t168,t169,t194,t170]
def v365 := [t167,t168,t169,t170,t144]
def p31_2063 : Projection 27 12 := pick [13,14,16,17,19,20,21,22,23,24,25,26] rfl (by decide +kernel) (by decide)
def v366 := [t157,t0,t1,t91,t2,t3,t4]
def t195 := 0x3a900006000000
def v367 := [t0,t1,t2,t3,t195,t4]
def v368 := [t0,t1,t91,t2,t3,t195,t4]
def v369 := [t133,t0,t1,t91,t2,t3,t4]
def v371 := [t0,t1,t91,t2,t3,t134,t4]
def v372 := [t0,t1,t91,t135,t2,t3,t4]
def v373 := [t0,t1,t91,t2,t136,t3,t4]
def v374 := [t0,t1,t91,t137,t2,t3,t4]
def v375 := [t0,t1,t91,t2,t3,t4,t138]
def v376 := [t139,t0,t1,t91,t2,t3,t4]
def v377 := [t0,t1,t91,t2,t3,t140,t4]
def v378 := [t0,t1,t91,t2,t117,t3,t4]
def v379 := [t0,t1,t91,t2,t3,t118]
def v380 := [t0,t1,t91,t2,t3,t4,t118]
def v381 := [t119,t0,t1,t91,t2,t3,t4]
def v382 := [t0,t1,t91,t2,t120,t3]
def v383 := [t0,t1,t91,t2,t120,t3,t4]
def v384 := [t59,t57,t46,t47,t48]
def t196 := 0x9007
def v385 := [t196,t45,t46,t47,t48]
def v386 := [t45,t46,t163,t47,t48]
def v387 := [t164,t45,t46,t47,t48]
def t197 := 0x624e38
def v388 := [t45,t197,t46,t47,t48]
def v389 := [t45,t46,t47,t165,t48]
def v390 := [t166,t45,t46,t47,t48]
def t198 := 0xb04fc0
def v391 := [t45,t46,t198,t47,t48]
def v392 := [t59,t45,t46,t47,t58]
def v393 := [t59,t46,t47,t60]
def v394 := [t59,t45,t46,t47,t60]
def v395 := [t59,t46,t47,t60,t48]
def v396 := [t59,t45,t65,t46,t47]
def v397 := [t59,t45,t67,t46,t47]
def v398 := [t59,t45,t46,t69,t47]
def v399 := [t59,t45,t71,t46,t47]
def map23_3 : Projection 12 12 := pick [6,7,8,1,0,2,4,3,5,11,9,10] rfl (by decide +kernel) (by decide)
def map23_4 : Projection 12 12 := pick [4,3,5,7,6,8,0,1,2,10,11,9] rfl (by decide +kernel) (by decide)
def map23_9 : Projection 12 12 := pick [9,10,11,2,0,1,5,3,4,8,6,7] rfl (by decide +kernel) (by decide)
def map23_18 : Projection 12 12 := pick [4,5,3,7,8,6,10,11,9,0,1,2] rfl (by decide +kernel) (by decide)
def map23_1 : Projection 12 12 := pick [3,4,5,0,1,2,7,6,8,10,9,11] rfl (by decide +kernel) (by decide)
def map23_15 : Projection 12 12 := pick [9,11,10,2,1,0,8,6,7,5,3,4] rfl (by decide +kernel) (by decide)
def map23_20 : Projection 12 12 := pick [5,4,3,10,11,9,7,8,6,0,2,1] rfl (by decide +kernel) (by decide)
def map23_21 : Projection 12 12 := pick [10,11,9,5,4,3,8,7,6,2,0,1] rfl (by decide +kernel) (by decide)
def map23_6 : Projection 12 12 := pick [0,2,1,3,5,4,9,10,11,6,7,8] rfl (by decide +kernel) (by decide)
def map23_8 : Projection 12 12 := pick [2,0,1,9,10,11,3,5,4,6,8,7] rfl (by decide +kernel) (by decide)
def map23_12 : Projection 12 12 := pick [1,2,0,6,8,7,9,11,10,3,4,5] rfl (by decide +kernel) (by decide)
def map23_7 : Projection 12 12 := pick [3,5,4,0,2,1,10,9,11,7,6,8] rfl (by decide +kernel) (by decide)
def map23_13 : Projection 12 12 := pick [6,8,7,1,2,0,11,9,10,4,3,5] rfl (by decide +kernel) (by decide)
def map23_10 : Projection 12 12 := pick [5,3,4,10,9,11,0,2,1,7,8,6] rfl (by decide +kernel) (by decide)
def map23_19 : Projection 12 12 := pick [7,8,6,4,5,3,11,10,9,1,0,2] rfl (by decide +kernel) (by decide)
def map23_11 : Projection 12 12 := pick [10,9,11,5,3,4,2,0,1,8,7,6] rfl (by decide +kernel) (by decide)
def map23_16 : Projection 12 12 := pick [8,6,7,11,9,10,1,2,0,4,5,3] rfl (by decide +kernel) (by decide)
def v400 := [t55,t46,t56,t48]
def v401 := [t53,t55,t46,t56,t48]
def v402 := [t55,t46,t56,t47,t48]
def t199 := 0x9038
def v403 := [t199,t53,t46,t47,t48]
def t200 := 0x624e07
def v404 := [t53,t200,t46,t47,t48]
def v405 := [t53,t55,t46,t54,t48]
def t201 := 0x90038
def v406 := [t53,t201,t46,t47,t48]
def t202 := 0xd20fc0
def v407 := [t53,t46,t47,t202,t48]
def v408 := [t53,t55,t61,t46,t48]
def v409 := [t53,t55,t63,t46,t48]
def v410 := [t53,t55,t46,t69,t48]
def v411 := [t53,t55,t72,t46,t48]
def v412 := [t59,t57,t45,t46,t47,t48]
def v413 := [t196,t59,t45,t46,t47,t48]
def v414 := [t45,t161,t46,t47,t48]
def v415 := [t45,t162,t46,t47,t48]
def v416 := [t162,t161,t46,t47,t48]
def v417 := [t49,t161,t46,t47,t48]
def v418 := [t161,t52,t46,t47,t48]
def v419 := [t53,t161,t46,t47,t48]
def v420 := [t161,t46,t56,t47,t48]
def v421 := [t57,t45,t161,t46,t47]
def v422 := [t161,t46,t47,t48,t58]
def v423 := [t59,t161,t46,t47]
def v424 := [t59,t45,t161,t46,t47]
def v425 := [t59,t161,t46,t47,t48]
def t203 := 0x20d03f
def v426 := [t45,t203,t46,t47,t48]
def t204 := 0x420e00
def v427 := [t45,t204,t46,t47,t48]
def t205 := 0x2461c7
def v428 := [t45,t205,t46,t47,t48]
def t206 := 0x900e00
def v429 := [t45,t46,t206,t47,t48]
def v430 := [t59,t45,t46,t163,t47,t48]
def t207 := 0x429e3f
def v431 := [t45,t207,t47,t48]
def v432 := [t45,t162,t207,t47,t48]
def v433 := [t45,t207,t46,t47,t48]
def t208 := 0x942fc7
def v434 := [t45,t46,t208,t48]
def v435 := [t45,t162,t46,t208,t48]
def v436 := [t45,t46,t208,t47,t48]
def t209 := 0xfb4ff8
def v437 := [t45,t162,t46,t47,t209]
def v438 := [t45,t46,t47,t48,t209]
def v439 := [t57,t162,t46,t47]
def v440 := [t57,t45,t162,t46,t47]
def v441 := [t57,t162,t46,t47,t48]
def v442 := [t59,t45,t162,t46,t47]
def v443 := [t162,t46,t47,t60,t48]
def v444 := [t164,t59,t45,t46,t47,t48]
def t210 := 0x4b03f
def v445 := [t210,t45,t46,t47,t48]
def t211 := 0x901c0
def v446 := [t210,t211,t46,t47,t48]
def v447 := [t211,t45,t46,t47,t48]
def t212 := 0xb4ffff
def v448 := [t45,t46,t47,t212,t48]
def v449 := [t199,t45,t46,t47,t48]
def t213 := 0x38
def v450 := [t213,t45,t46,t47,t48]
def t214 := 0xdb0fc0
def v451 := [t45,t46,t47,t214,t48]
def v452 := [t210,t46,t50,t47,t48]
def v453 := [t210,t51,t46,t47,t48]
def v454 := [t53,t210,t46,t47,t48]
def v455 := [t210,t46,t56,t47,t48]
def v456 := [t210,t57,t46,t47,t48]
def v457 := [t210,t46,t47,t60,t48]
def v458 := [t210,t45,t61,t47,t48]
def v459 := [t210,t45,t64,t47,t48]
def v460 := [t210,t45,t65,t46,t47]
def v461 := [t210,t45,t67,t46,t47]
def v462 := [t59,t45,t197,t46,t47,t48]
def v463 := [t78,t59,t45,t46,t47,t48]
def v464 := [t59,t45,t46,t47,t165,t48]
def v465 := [t166,t59,t45,t46,t47,t48]
def map23_17 : Projection 12 12 := pick [11,9,10,8,6,7,2,1,0,5,4,3] rfl (by decide +kernel) (by decide)
def map23_22 : Projection 12 12 := pick [8,7,6,11,10,9,4,5,3,1,2,0] rfl (by decide +kernel) (by decide)
def v466 := [t59,t45,t46,t198,t47,t48]
def v467 := [t57,t46,t47,t58]
def v468 := [t59,t57,t46,t47,t58]
def v469 := [t57,t45,t46,t47,t58]
def v470 := [t59,t46,t47,t60,t58]
def v471 := [t59,t45,t207,t47]
def v472 := [t59,t45,t207,t46,t47]
def v473 := [t59,t45,t207,t47,t58]
def t215 := 0x9d21c0
def v474 := [t59,t45,t215,t47,t58]
def v475 := [t59,t45,t46,t208]
def v476 := [t59,t45,t46,t208,t47]
def v477 := [t59,t45,t46,t208,t58]
def v478 := [t59,t45,t145,t46,t58]
def v479 := [t59,t45,t46,t47,t48,t58]
def v480 := [t49,t59,t45,t46,t47,t48]
def v481 := [t59,t45,t46,t50,t47,t48]
def v482 := [t59,t51,t45,t46,t47,t48]
def v483 := [t59,t45,t52,t46,t47,t48]
def v484 := [t53,t59,t45,t46,t47,t48]
def v485 := [t59,t45,t46,t47,t54,t48]
def v486 := [t59,t55,t45,t46,t47,t48]
def v487 := [t59,t45,t46,t56,t47,t48]
def v488 := [t196,t59,t46,t47,t60]
def v489 := [t59,t46,t163,t47,t60]
def v490 := [t164,t59,t46,t47,t60]
def v491 := [t59,t197,t46,t47,t60]
def v492 := [t78,t59,t46,t47,t60]
def v493 := [t59,t46,t47,t165,t60]
def v494 := [t166,t59,t46,t47,t60]
def v495 := [t59,t46,t198,t47,t60]
def t216 := 0xd6be07
def v496 := [t46,t47,t216]
def v497 := [t59,t46,t47,t216]
def v498 := [t46,t47,t60,t216]
def v499 := [t59,t46,t47,t60,t216]
def v500 := [t59,t61,t46,t47,t60]
def v501 := [t59,t46,t47,t60,t62]
def v502 := [t59,t63,t46,t47,t60]
def v503 := [t59,t46,t64,t47,t60]
def v504 := [t59,t204,t46,t47,t60]
def t217 := 0xf2de3f
def v505 := [t59,t46,t47,t60,t217]
def v506 := [t59,t203,t46,t47,t60]
def v507 := [t59,t46,t146,t47,t60]
def v508 := [t59,t46,t206,t47,t60]
def t218 := 0xf66fc7
def v509 := [t59,t46,t47,t60,t218]
def v510 := [t59,t205,t46,t47,t60]
def t219 := 0x420000
def v511 := [t59,t219,t46,t47,t60]
def v512 := [t59,t57,t46,t47,t60]
def v513 := [t57,t45,t46,t47,t60]
def v514 := [t45,t46,t47,t216]
def v515 := [t59,t45,t46,t47,t216]
def v516 := [t45,t46,t47,t60,t216]
def v517 := [t49,t59,t46,t47,t60]
def v518 := [t59,t46,t50,t47,t60]
def v519 := [t59,t51,t46,t47,t60]
def v520 := [t59,t52,t46,t47,t60]
def v521 := [t53,t59,t46,t47,t60]
def v522 := [t59,t46,t47,t54,t60]
def v523 := [t59,t55,t46,t47,t60]
def v524 := [t59,t46,t56,t47,t60]
def v525 := [t59,t45,t204,t46,t47]
def v526 := [t59,t45,t203,t46,t47]
def v527 := [t59,t45,t46,t206,t47]
def v528 := [t59,t45,t205,t46,t47]
def v529 := [t59,t45,t46,t47,t60,t48]
def v530 := [t59,t45,t61,t46,t47,t48]
def v531 := [t53,t45,t67,t46,t47,t48]
def t220 := 0x24f1c7
def v532 := [t45,t220,t46,t47,t48]
def t221 := 0x20d000
def v533 := [t45,t221,t46,t47,t48]
def v534 := [t45,t67,t73,t47,t48]
def v535 := [t45,t67,t75,t47,t48]
def v536 := [t76,t45,t67,t46,t47]
def v537 := [t78,t45,t67,t46,t47]
def t222 := 0xd21f8
def v538 := [t53,t222,t46,t47,t48]
def v539 := [t53,t45,t46,t165,t48]
def t223 := 0x942fc0
def v540 := [t53,t45,t46,t223,t48]
def v541 := [t53,t67,t46,t54,t48]
def v542 := [t53,t57,t67,t46,t47]
def v543 := [t53,t45,t67,t68,t47]
def v544 := [t53,t45,t67,t46,t69]
def v545 := [t59,t45,t46,t47,t48,t62]
def v546 := [t59,t45,t63,t46,t47,t48]
def v547 := [t59,t45,t46,t64,t47,t48]
def v548 := [t55,t45,t63,t46,t48]
def t224 := 0x46b1ff
def v549 := [t53,t45,t224,t46,t48]
def v550 := [t45,t63,t224,t46,t48]
def v551 := [t45,t63,t46,t73,t48]
def v552 := [t74,t45,t63,t46,t48]
def v553 := [t76,t45,t63,t46,t48]
def v554 := [t45,t63,t46,t79,t48]
def v555 := [t199,t53,t63,t46,t48]
def t225 := 0x4fb1ff
def v556 := [t53,t45,t225,t46,t48]
def v557 := [t53,t219,t46,t48]
def v558 := [t53,t45,t219,t46,t48]
def v559 := [t53,t219,t63,t46,t48]
def v560 := [t49,t53,t63,t46,t48]
def v561 := [t53,t63,t52,t46,t48]
def v562 := [t53,t57,t63,t46,t48]
def v563 := [t53,t63,t46,t60,t48]
def v564 := [t53,t45,t61,t63,t48]
def t226 := 0x420038
def v565 := [t53,t45,t226,t46,t48]
def t227 := 0x990fc0
def v566 := [t53,t45,t46,t227,t48]
def v567 := [t59,t45,t65,t46,t47,t48]
def v568 := [t59,t45,t46,t47,t48,t66]
def v569 := [t45,t163,t47,t48,t66]
def v570 := [t45,t197,t47,t48,t66]
def v571 := [t59,t46,t47,t60,t66]
def t228 := 0x991ff
def v572 := [t59,t228,t46,t47,t48]
def t229 := 0xf24e00
def v573 := [t59,t46,t47,t48,t229]
def v574 := [t59,t45,t65,t47,t66]
def t230 := 0xb04fc7
def v575 := [t59,t45,t46,t230,t48]
def v576 := [t59,t45,t145,t46,t48]
def t231 := 0x14f
def t232 := 0x4b3
def t233 := 0xa3c
def v577 := [t231,t232,t233]
def p23_2055 : Projection 12 6 := pick [4,5,7,8,10,11] rfl (by decide +kernel) (by decide)
def v578 := [t59,t45,t67,t46,t47,t48]
def v579 := [t59,t45,t46,t68,t47,t48]
def v580 := [t59,t45,t46,t69,t47,t48]
def v581 := [t59,t45,t46,t47,t48,t70]
def v582 := [t59,t45,t71,t46,t47,t48]
def v583 := [t59,t45,t72,t46,t47,t48]
def v584 := [t0,t1,t2,t94,t3,t4]
def v585 := [t121,t0,t1,t2,t3,t4]
def v586 := [t101,t0,t1,t2,t3,t4]
def v587 := [t0,t1,t2,t3,t122,t4]
def v588 := [t123,t0,t1,t2,t3,t4]
def v589 := [t0,t1,t2,t124,t3,t4]
def v590 := [t0,t1,t2,t136,t3,t4]
def v591 := [t125,t0,t1,t2,t3,t4]
def v592 := [t0,t1,t2,t3,t4,t126]
def v593 := [t5,t0,t1,t2,t3,t4,t126]
def v594 := [t92,t0,t1,t2,t3,t4,t126]
def v595 := [t0,t93,t1,t2,t3,t4,t126]
def v596 := [t0,t1,t2,t94,t3,t4,t126]
def v597 := [t7,t0,t1,t2,t3,t4,t126]
def v598 := [t0,t1,t41,t2,t3,t4,t126]
def v599 := [t121,t0,t1,t2,t3,t4,t126]
def v600 := [t0,t1,t2,t3,t122,t4,t126]
def v601 := [t123,t0,t1,t2,t3,t4,t126]
def v602 := [t0,t1,t2,t124,t3,t4,t126]
def v603 := [t125,t1,t2,t3,t126]
def v604 := [t125,t0,t1,t2,t3,t126]
def v605 := [t125,t1,t2,t3,t4,t126]
def v606 := [t125,t0,t1,t2,t3,t4,t126]
def v607 := [t127,t0,t1,t2,t3,t126]
def v608 := [t127,t0,t1,t2,t3,t4,t126]
def v609 := [t1,t2,t3,t128,t4,t126]
def v610 := [t0,t1,t2,t3,t128,t4,t126]
def v611 := [t0,t1,t2,t3,t128,t4]
def v612 := [t129,t0,t1,t2,t3,t4,t126]
def v613 := [t0,t1,t2,t130,t3,t4,t126]
def v614 := [t0,t131,t1,t2,t3,t4,t126]
def v615 := [t0,t1,t132,t2,t3,t4,t126]
def v616 := [t101,t0,t1,t2,t3,t4,t126]
def v617 := [t0,t1,t2,t3,t102,t4,t126]
def v618 := [t0,t103,t1,t2,t3,t4,t126]
def v619 := [t0,t1,t2,t104,t3,t4,t126]
def v620 := [t0,t105,t1,t2,t3,t4,t126]
def v621 := [t0,t1,t2,t3,t4,t126,t106]
def v622 := [t107,t0,t1,t2,t3,t4,t126]
def v623 := [t0,t1,t2,t3,t108,t4,t126]
def t234 := 0x44284099c7087
def v624 := [t0,t234,t1,t2,t3,t4]
def p31_30 : Projection 27 12 := pick [5,6,8,9,11,18,19,20,23,24,25,26] rfl (by decide +kernel) (by decide)
def v626 := [t0,t234,t1,t2,t3,t4,t126]
def v627 := [t0,t1,t2,t3,t4,t126,t160]
def t236 := 0x204120000860
def v628 := [t236,t0,t1,t2,t3,t4]
def v629 := [t236,t0,t1,t2,t3,t4,t126]
def t237 := 0x3b9d2056638418
def v630 := [t0,t1,t2,t3,t237,t4]
def v631 := [t0,t1,t2,t3,t237,t4,t126]
def v632 := [t133,t0,t1,t2,t3,t4,t126]
def v633 := [t0,t1,t2,t3,t134,t4,t126]
def v634 := [t0,t1,t135,t2,t3,t4,t126]
def v635 := [t0,t1,t2,t136,t3,t4,t126]
def v636 := [t0,t1,t137,t2,t3,t4,t126]
def v637 := [t0,t1,t2,t3,t4,t126,t138]
def v638 := [t139,t0,t1,t2,t3,t4,t126]
def v639 := [t0,t1,t2,t3,t140,t4,t126]
def t238 := 0x109420161f8407
def v640 := [t0,t1,t238,t2,t3,t4]
def v641 := [t0,t1,t238,t2,t3,t4,t126]
def v642 := [t0,t1,t2,t3,t4,t114]
def v643 := [t0,t1,t2,t3,t4,t126,t114]
def t239 := 0x204820000b00
def v644 := [t239,t0,t1,t2,t3,t4]
def v645 := [t239,t0,t1,t2,t3,t4,t126]
def t240 := 0x2f4b8449e07098
def v646 := [t0,t1,t2,t3,t240,t4]
def v647 := [t0,t1,t2,t3,t240,t4,t126]
def v648 := [t0,t1,t2,t117,t3,t4,t126]
def v649 := [t0,t1,t2,t3,t118,t126]
def v650 := [t0,t1,t2,t3,t4,t118,t126]
def v651 := [t119,t0,t1,t2,t3,t4,t126]
def v652 := [t0,t1,t2,t120,t3,t126]
def v653 := [t0,t1,t2,t120,t3,t4,t126]
def t241 := 0x2a000007e00498
def v654 := [t0,t1,t2,t241,t3,t4]
def v655 := [t0,t1,t2,t241,t3,t4,t126]
def t242 := 0x3fdfb6dfffffff
def v656 := [t0,t1,t2,t3,t4,t242]
def v657 := [t0,t1,t2,t3,t4,t126,t242]
def t243 := 0x1280000b60
def v658 := [t243,t0,t1,t2,t3,t4]
def v659 := [t243,t0,t1,t2,t3,t4,t126]
def t244 := 0x15dfa4581ff007
def v660 := [t0,t1,t2,t244,t3,t4]
def v661 := [t0,t1,t2,t244,t3,t4,t126]
def v662 := [t127,t0,t1,t2,t3,t4]
def v663 := [t0,t1,t2,t3,t140,t4]
def v664 := [t129,t0,t1,t2,t3,t4]
def v665 := [t0,t1,t2,t130,t3,t4]
def v666 := [t0,t131,t1,t2,t3,t4]
def v667 := [t0,t1,t132,t2,t3,t4]
def v668 := [t0,t1,t2,t3,t102,t4]
def v669 := [t0,t103,t1,t2,t3,t4]
def v670 := [t0,t1,t2,t104,t3,t4]
def v671 := [t0,t105,t1,t2,t3,t4]
def v672 := [t0,t1,t2,t3,t4,t106]
def v673 := [t107,t0,t1,t2,t3,t4]
def v674 := [t0,t1,t2,t3,t108,t4]
def v675 := [t133,t0,t1,t2,t3,t4]
def v676 := [t0,t1,t2,t3,t134,t4]
def v677 := [t0,t1,t135,t2,t3,t4]
def v678 := [t0,t1,t137,t2,t3,t4]
def v679 := [t0,t1,t2,t3,t4,t138]
def v680 := [t139,t0,t1,t2,t3,t4]
def v681 := [t0,t1,t2,t117,t3,t4]
def v682 := [t0,t1,t2,t3,t118]
def v683 := [t0,t1,t2,t3,t4,t118]
def v684 := [t119,t0,t1,t2,t3,t4]
def v685 := [t0,t1,t2,t120,t3]
def v686 := [t0,t1,t2,t120,t3,t4]
theorem b93 : Ban 12 4 v95 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w2 : Wide 12 4 v95 := viaSub (ws := [v95]) (consBan b93 (nilBan 12 4)) (by decide) (by decide +kernel)
theorem b0 : Ban 27 6 v3 := smallByCut p31_27 w2
theorem b67 : Ban 12 4 v72 := checkedSmall
theorem b48 : Ban 12 4 v54 := checkedSmall
theorem b68 : Ban 12 4 v73 := checkedSmall
theorem b69 : Ban 12 4 v74 := checkedSmall
theorem b70 : Ban 12 4 v75 := checkedSmall
theorem b71 : Ban 12 4 v76 := checkedSmall
theorem b72 : Ban 12 4 v77 := checkedSmall
theorem b49 : Ban 12 4 v55 := checkedSmall
theorem b73 : Ban 12 4 v78 := checkedSmall
theorem b74 : Ban 12 4 v79 := checkedSmall
theorem b75 : Ban 12 4 v80 := checkedSmall
theorem b76 : Ban 12 4 v81 := checkedSmall
theorem b77 : Ban 12 4 v82 := checkedSmall
theorem b78 : Ban 12 4 v83 := checkedSmall
theorem b79 : Ban 12 4 v84 := checkedSmall
theorem b80 : Ban 12 4 v85 := checkedSmall
theorem b81 : Ban 12 4 v86 := checkedSmall
theorem b82 : Ban 12 4 v87 := checkedSmall
theorem b83 : Ban 12 4 v88 := checkedSmall
theorem b84 : Ban 12 4 v89 := checkedSmall
theorem b85 : Ban 12 4 v90 := checkedSmall
theorem b86 : Ban 12 4 v91 := checkedSmall
theorem b87 : Ban 12 4 v92 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b88 : Ban 12 5 v52 := viaBranch (ws := [v72,v54,v73,v74,v75,v76,v77,v55,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92]) (consBan b67 (consBan b48 (consBan b68 (consBan b69 (consBan b70 (consBan b71 (consBan b72 (consBan b49 (consBan b73 (consBan b74 (consBan b75 (consBan b76 (consBan b77 (consBan b78 (consBan b79 (consBan b80 (consBan b81 (consBan b82 (consBan b83 (consBan b84 (consBan b85 (consBan b86 (consBan b87 (nilBan 12 4)))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b89 : Ban 12 5 v48 := viaPerm map23_2 map23_2 b88 (by decide +kernel) (by decide +kernel)
theorem b214 : Ban 12 4 v214 := checkedSmall
theorem b215 : Ban 12 4 v215 := checkedSmall
theorem b216 : Ban 12 4 v216 := checkedSmall
theorem b217 : Ban 12 4 v217 := checkedSmall
theorem b218 : Ban 12 4 v218 := checkedSmall
theorem b45 : Ban 12 4 v51 := checkedSmall
theorem b44 : Ban 12 4 v50 := checkedSmall
theorem b219 : Ban 12 4 v219 := checkedSmall
theorem b220 : Ban 12 4 v220 := checkedSmall
theorem b221 : Ban 12 4 v221 := checkedSmall
theorem b222 : Ban 12 4 v222 := checkedSmall
theorem b223 : Ban 12 4 v223 := checkedSmall
theorem b224 : Ban 12 4 v224 := checkedSmall
theorem b225 : Ban 12 4 v225 := checkedSmall
theorem b226 : Ban 12 4 v226 := checkedSmall
theorem b227 : Ban 12 4 v227 := checkedSmall
theorem b228 : Ban 12 4 v228 := checkedSmall
theorem b229 : Ban 12 4 v229 := checkedSmall
theorem b626 : Ban 6 3 v577 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w16 : Wide 6 3 v577 := viaSub (ws := [v577]) (consBan b626 (nilBan 6 3)) (by decide) (by decide +kernel)
theorem b230 : Ban 12 4 v230 := smallByCut p23_2055 w16
theorem b231 : Ban 12 4 v231 := checkedSmall
theorem b232 : Ban 12 4 v232 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b233 : Ban 12 5 v49 := viaBranch (ws := [v214,v215,v216,v217,v218,v51,v50,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232]) (consBan b214 (consBan b215 (consBan b216 (consBan b217 (consBan b218 (consBan b45 (consBan b44 (consBan b219 (consBan b220 (consBan b221 (consBan b222 (consBan b223 (consBan b224 (consBan b225 (consBan b226 (consBan b227 (consBan b228 (consBan b229 (consBan b230 (consBan b231 (consBan b232 (nilBan 12 4)))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b393 : Ban 12 4 v384 := checkedSmall
theorem b50 : Ban 12 4 v56 := checkedSmall
theorem b394 : Ban 12 4 v385 := checkedSmall
theorem b395 : Ban 12 4 v386 := checkedSmall
theorem b396 : Ban 12 4 v387 := checkedSmall
theorem b397 : Ban 12 4 v388 := checkedSmall
theorem b398 : Ban 12 4 v389 := checkedSmall
theorem b399 : Ban 12 4 v390 := checkedSmall
theorem b400 : Ban 12 4 v391 := checkedSmall
theorem b401 : Ban 12 4 v392 := checkedSmall
theorem b51 : Ban 12 4 v57 := checkedSmall
theorem b402 : Ban 12 4 v393 := checkedSmall
theorem b403 : Ban 12 4 v394 := checkedSmall
theorem b404 : Ban 12 4 v395 := checkedSmall
theorem b405 : Ban 12 4 v396 := smallByCut p23_2055 w16
theorem b406 : Ban 12 4 v397 := smallByCut p23_2055 w16
theorem b407 : Ban 12 4 v398 := smallByCut p23_2055 w16
theorem b408 : Ban 12 4 v399 := smallByCut p23_2055 w16
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b409 : Ban 12 5 v58 := viaBranch (ws := [v384,v56,v385,v386,v387,v388,v80,v389,v390,v391,v392,v57,v393,v394,v395,v396,v397,v398,v399]) (consBan b393 (consBan b50 (consBan b394 (consBan b395 (consBan b396 (consBan b397 (consBan b75 (consBan b398 (consBan b399 (consBan b400 (consBan b401 (consBan b51 (consBan b402 (consBan b403 (consBan b404 (consBan b405 (consBan b406 (consBan b407 (consBan b408 (nilBan 12 4)))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b410 : Ban 12 5 v50 := viaPerm map23_3 map23_4 b409 (by decide +kernel) (by decide +kernel)
theorem b411 : Ban 12 5 v51 := viaPerm map23_9 map23_18 b409 (by decide +kernel) (by decide +kernel)
theorem b412 : Ban 12 5 v53 := viaPerm map23_2 map23_2 b233 (by decide +kernel) (by decide +kernel)
theorem b413 : Ban 12 5 v54 := viaPerm map23_1 map23_1 b409 (by decide +kernel) (by decide +kernel)
theorem b414 : Ban 12 5 v55 := viaPerm map23_15 map23_20 b409 (by decide +kernel) (by decide +kernel)
theorem b415 : Ban 12 5 v56 := viaPerm map23_1 map23_1 b88 (by decide +kernel) (by decide +kernel)
theorem b416 : Ban 12 5 v57 := viaPerm map23_4 map23_3 b233 (by decide +kernel) (by decide +kernel)
theorem b417 : Ban 12 5 v59 := viaPerm map23_21 map23_21 b409 (by decide +kernel) (by decide +kernel)
theorem b418 : Ban 12 5 v60 := viaPerm map23_6 map23_6 b88 (by decide +kernel) (by decide +kernel)
theorem b419 : Ban 12 5 v61 := viaPerm map23_8 map23_12 b233 (by decide +kernel) (by decide +kernel)
theorem b420 : Ban 12 5 v62 := viaPerm map23_7 map23_7 b409 (by decide +kernel) (by decide +kernel)
theorem b421 : Ban 12 5 v63 := viaPerm map23_13 map23_10 b409 (by decide +kernel) (by decide +kernel)
theorem b422 : Ban 12 5 v64 := viaPerm map23_7 map23_7 b88 (by decide +kernel) (by decide +kernel)
theorem b423 : Ban 12 5 v65 := viaPerm map23_10 map23_13 b233 (by decide +kernel) (by decide +kernel)
theorem b424 : Ban 12 5 v66 := viaPerm map23_6 map23_6 b409 (by decide +kernel) (by decide +kernel)
theorem b425 : Ban 12 5 v67 := viaPerm map23_19 map23_11 b409 (by decide +kernel) (by decide +kernel)
theorem b426 : Ban 12 5 v68 := viaPerm map23_13 map23_10 b88 (by decide +kernel) (by decide +kernel)
theorem b427 : Ban 12 5 v69 := viaPerm map23_16 map23_16 b233 (by decide +kernel) (by decide +kernel)
theorem b428 : Ban 12 5 v70 := viaPerm map23_12 map23_8 b409 (by decide +kernel) (by decide +kernel)
theorem b429 : Ban 12 5 v71 := viaPerm map23_18 map23_9 b409 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b430 : Ban 12 6 v47 := viaBranch (ws := [v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71]) (consBan b89 (consBan b233 (consBan b410 (consBan b411 (consBan b88 (consBan b412 (consBan b413 (consBan b414 (consBan b415 (consBan b416 (consBan b409 (consBan b417 (consBan b418 (consBan b419 (consBan b420 (consBan b421 (consBan b422 (consBan b423 (consBan b424 (consBan b425 (consBan b426 (consBan b427 (consBan b428 (consBan b429 (nilBan 12 5))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b42 : Ban 12 4 v48 := checkedSmall
theorem b43 : Ban 12 4 v49 := checkedSmall
theorem b46 : Ban 12 4 v52 := checkedSmall
theorem b47 : Ban 12 4 v53 := checkedSmall
theorem b52 : Ban 12 4 v58 := checkedSmall
theorem b53 : Ban 12 4 v59 := checkedSmall
theorem b54 : Ban 12 4 v60 := checkedSmall
theorem b55 : Ban 12 4 v61 := checkedSmall
theorem b56 : Ban 12 4 v62 := checkedSmall
theorem b57 : Ban 12 4 v63 := checkedSmall
theorem b58 : Ban 12 4 v64 := checkedSmall
theorem b59 : Ban 12 4 v65 := checkedSmall
theorem b60 : Ban 12 4 v66 := checkedSmall
theorem b61 : Ban 12 4 v67 := checkedSmall
theorem b62 : Ban 12 4 v68 := checkedSmall
theorem b63 : Ban 12 4 v69 := checkedSmall
theorem b64 : Ban 12 4 v70 := checkedSmall
theorem b65 : Ban 12 4 v71 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b66 : Ban 12 5 v47 := viaBranch (ws := [v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71]) (consBan b42 (consBan b43 (consBan b44 (consBan b45 (consBan b46 (consBan b47 (consBan b48 (consBan b49 (consBan b50 (consBan b51 (consBan b52 (consBan b53 (consBan b54 (consBan b55 (consBan b56 (consBan b57 (consBan b58 (consBan b59 (consBan b60 (consBan b61 (consBan b62 (consBan b63 (consBan b64 (consBan b65 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w1 : Wide 12 5 v48 := viaSub (ws := [v47,v48]) (consBan b66 (consBan b89 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b96 : Ban 12 4 v47 := bySubset w1
theorem b431 : Ban 12 4 v400 := checkedSmall
theorem b432 : Ban 12 4 v401 := checkedSmall
theorem b433 : Ban 12 4 v402 := checkedSmall
theorem b434 : Ban 12 4 v403 := checkedSmall
theorem b435 : Ban 12 4 v404 := checkedSmall
theorem b436 : Ban 12 4 v405 := checkedSmall
theorem b437 : Ban 12 4 v406 := checkedSmall
theorem b438 : Ban 12 4 v407 := checkedSmall
theorem b439 : Ban 12 4 v408 := checkedSmall
theorem b440 : Ban 12 4 v409 := checkedSmall
theorem b441 : Ban 12 4 v410 := checkedSmall
theorem b442 : Ban 12 4 v411 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b443 : Ban 12 5 v72 := viaBranch (ws := [v47,v52,v54,v400,v401,v402,v403,v404,v84,v405,v86,v406,v407,v408,v409,v410,v411]) (consBan b96 (consBan b46 (consBan b48 (consBan b431 (consBan b432 (consBan b433 (consBan b434 (consBan b435 (consBan b79 (consBan b436 (consBan b81 (consBan b437 (consBan b438 (consBan b439 (consBan b440 (consBan b441 (consBan b442 (nilBan 12 4)))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b444 : Ban 12 5 v384 := viaPerm map23_1 map23_1 b443 (by decide +kernel) (by decide +kernel)
theorem b445 : Ban 12 5 v412 := checkedSmall
theorem b446 : Ban 12 5 v385 := checkedSmall
theorem b447 : Ban 12 5 v413 := checkedSmall
theorem b448 : Ban 12 4 v415 := checkedSmall
theorem b449 : Ban 12 4 v416 := checkedSmall
theorem b450 : Ban 12 4 v417 := checkedSmall
theorem b451 : Ban 12 4 v418 := checkedSmall
theorem b452 : Ban 12 4 v419 := checkedSmall
theorem b453 : Ban 12 4 v420 := checkedSmall
theorem b454 : Ban 12 4 v421 := checkedSmall
theorem b455 : Ban 12 4 v422 := checkedSmall
theorem b456 : Ban 12 4 v423 := smallByCut p23_2055 w16
theorem b457 : Ban 12 4 v424 := smallByCut p23_2055 w16
theorem b458 : Ban 12 4 v425 := checkedSmall
theorem b459 : Ban 12 4 v426 := checkedSmall
theorem b460 : Ban 12 4 v427 := checkedSmall
theorem b461 : Ban 12 4 v428 := checkedSmall
theorem b462 : Ban 12 4 v429 := checkedSmall
theorem b307 : Ban 12 4 v303 := smallByCut p23_2055 w16
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b463 : Ban 12 5 v414 := viaBranch (ws := [v415,v416,v417,v418,v419,v420,v421,v422,v423,v424,v425,v426,v49,v50,v427,v428,v53,v54,v429,v56,v222,v230,v303,v232,v59]) (consBan b448 (consBan b449 (consBan b450 (consBan b451 (consBan b452 (consBan b453 (consBan b454 (consBan b455 (consBan b456 (consBan b457 (consBan b458 (consBan b459 (consBan b43 (consBan b44 (consBan b460 (consBan b461 (consBan b47 (consBan b48 (consBan b462 (consBan b50 (consBan b222 (consBan b230 (consBan b307 (consBan b232 (consBan b53 (nilBan 12 4)))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b464 : Ban 12 5 v386 := viaPerm map23_6 map23_6 b463 (by decide +kernel) (by decide +kernel)
theorem b465 : Ban 12 5 v430 := checkedSmall
theorem b466 : Ban 12 4 v414 := checkedSmall
theorem b467 : Ban 12 4 v431 := checkedSmall
theorem b468 : Ban 12 4 v432 := checkedSmall
theorem b469 : Ban 12 4 v433 := checkedSmall
theorem b470 : Ban 12 4 v434 := checkedSmall
theorem b471 : Ban 12 4 v435 := checkedSmall
theorem b472 : Ban 12 4 v436 := checkedSmall
theorem b473 : Ban 12 4 v437 := checkedSmall
theorem b474 : Ban 12 4 v438 := checkedSmall
theorem b475 : Ban 12 4 v439 := smallByCut p23_2055 w16
theorem b476 : Ban 12 4 v440 := smallByCut p23_2055 w16
theorem b477 : Ban 12 4 v441 := checkedSmall
theorem b478 : Ban 12 4 v442 := smallByCut p23_2055 w16
theorem b479 : Ban 12 4 v443 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b480 : Ban 12 5 v415 := viaBranch (ws := [v416,v414,v431,v432,v433,v434,v435,v436,v437,v438,v439,v440,v441,v442,v443]) (consBan b449 (consBan b466 (consBan b467 (consBan b468 (consBan b469 (consBan b470 (consBan b471 (consBan b472 (consBan b473 (consBan b474 (consBan b475 (consBan b476 (consBan b477 (consBan b478 (consBan b479 (nilBan 12 4)))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b481 : Ban 12 5 v387 := viaPerm map23_6 map23_6 b480 (by decide +kernel) (by decide +kernel)
theorem b482 : Ban 12 5 v444 := checkedSmall
theorem b483 : Ban 12 4 v446 := checkedSmall
theorem b484 : Ban 12 4 v447 := checkedSmall
theorem b485 : Ban 12 4 v448 := checkedSmall
theorem b486 : Ban 12 4 v449 := checkedSmall
theorem b487 : Ban 12 4 v450 := checkedSmall
theorem b488 : Ban 12 4 v451 := checkedSmall
theorem b489 : Ban 12 4 v452 := checkedSmall
theorem b490 : Ban 12 4 v453 := checkedSmall
theorem b491 : Ban 12 4 v454 := checkedSmall
theorem b492 : Ban 12 4 v455 := checkedSmall
theorem b493 : Ban 12 4 v456 := checkedSmall
theorem b494 : Ban 12 4 v457 := checkedSmall
theorem b495 : Ban 12 4 v458 := checkedSmall
theorem b496 : Ban 12 4 v459 := checkedSmall
theorem b497 : Ban 12 4 v460 := checkedSmall
theorem b498 : Ban 12 4 v461 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b499 : Ban 12 5 v445 := viaBranch (ws := [v446,v447,v48,v386,v387,v51,v80,v448,v449,v391,v450,v57,v58,v451,v452,v453,v454,v455,v456,v457,v458,v459,v460,v461]) (consBan b483 (consBan b484 (consBan b42 (consBan b395 (consBan b396 (consBan b45 (consBan b75 (consBan b485 (consBan b486 (consBan b400 (consBan b487 (consBan b51 (consBan b52 (consBan b488 (consBan b489 (consBan b490 (consBan b491 (consBan b492 (consBan b493 (consBan b494 (consBan b495 (consBan b496 (consBan b497 (consBan b498 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b500 : Ban 12 5 v388 := viaPerm map23_11 map23_19 b499 (by decide +kernel) (by decide +kernel)
theorem b501 : Ban 12 5 v462 := checkedSmall
theorem b502 : Ban 12 5 v80 := checkedSmall
theorem b503 : Ban 12 5 v463 := checkedSmall
theorem b504 : Ban 12 5 v389 := viaPerm map23_12 map23_8 b463 (by decide +kernel) (by decide +kernel)
theorem b505 : Ban 12 5 v464 := checkedSmall
theorem b506 : Ban 12 5 v390 := viaPerm map23_12 map23_8 b480 (by decide +kernel) (by decide +kernel)
theorem b507 : Ban 12 5 v465 := checkedSmall
theorem b508 : Ban 12 5 v391 := viaPerm map23_17 map23_22 b499 (by decide +kernel) (by decide +kernel)
theorem b509 : Ban 12 5 v466 := checkedSmall
theorem b510 : Ban 12 4 v467 := checkedSmall
theorem b511 : Ban 12 4 v468 := checkedSmall
theorem b512 : Ban 12 4 v469 := checkedSmall
theorem b513 : Ban 12 4 v470 := checkedSmall
theorem b514 : Ban 12 4 v471 := smallByCut p23_2055 w16
theorem b515 : Ban 12 4 v472 := smallByCut p23_2055 w16
theorem b516 : Ban 12 4 v473 := checkedSmall
theorem b517 : Ban 12 4 v474 := checkedSmall
theorem b518 : Ban 12 4 v475 := smallByCut p23_2055 w16
theorem b519 : Ban 12 4 v476 := smallByCut p23_2055 w16
theorem b520 : Ban 12 4 v477 := checkedSmall
theorem b521 : Ban 12 4 v478 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b522 : Ban 12 5 v392 := viaBranch (ws := [v467,v468,v469,v47,v58,v57,v393,v394,v470,v471,v472,v473,v442,v474,v475,v476,v477,v478]) (consBan b510 (consBan b511 (consBan b512 (consBan b96 (consBan b52 (consBan b51 (consBan b402 (consBan b403 (consBan b513 (consBan b514 (consBan b515 (consBan b516 (consBan b478 (consBan b517 (consBan b518 (consBan b519 (consBan b520 (consBan b521 (nilBan 12 4))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b523 : Ban 12 5 v479 := checkedSmall
theorem b524 : Ban 12 5 v480 := checkedSmall
theorem b525 : Ban 12 5 v481 := checkedSmall
theorem b526 : Ban 12 5 v482 := checkedSmall
theorem b527 : Ban 12 5 v483 := checkedSmall
theorem b528 : Ban 12 5 v484 := checkedSmall
theorem b529 : Ban 12 5 v485 := checkedSmall
theorem b530 : Ban 12 5 v486 := checkedSmall
theorem b531 : Ban 12 5 v487 := checkedSmall
theorem b532 : Ban 12 4 v488 := checkedSmall
theorem b533 : Ban 12 4 v489 := checkedSmall
theorem b534 : Ban 12 4 v490 := checkedSmall
theorem b535 : Ban 12 4 v491 := checkedSmall
theorem b536 : Ban 12 4 v492 := checkedSmall
theorem b537 : Ban 12 4 v493 := checkedSmall
theorem b538 : Ban 12 4 v494 := checkedSmall
theorem b539 : Ban 12 4 v495 := checkedSmall
theorem b540 : Ban 12 4 v496 := checkedSmall
theorem b541 : Ban 12 4 v497 := checkedSmall
theorem b542 : Ban 12 4 v498 := checkedSmall
theorem b543 : Ban 12 4 v499 := checkedSmall
theorem b544 : Ban 12 4 v500 := checkedSmall
theorem b545 : Ban 12 4 v501 := checkedSmall
theorem b546 : Ban 12 4 v502 := checkedSmall
theorem b547 : Ban 12 4 v503 := checkedSmall
theorem b548 : Ban 12 4 v504 := checkedSmall
theorem b549 : Ban 12 4 v505 := checkedSmall
theorem b550 : Ban 12 4 v506 := checkedSmall
theorem b551 : Ban 12 4 v507 := checkedSmall
theorem b552 : Ban 12 4 v508 := checkedSmall
theorem b553 : Ban 12 4 v509 := checkedSmall
theorem b554 : Ban 12 4 v510 := checkedSmall
theorem b555 : Ban 12 4 v511 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b556 : Ban 12 5 v393 := viaBranch (ws := [v488,v489,v490,v491,v492,v493,v494,v495,v496,v497,v498,v499,v500,v501,v502,v503,v504,v505,v506,v507,v508,v509,v510,v511]) (consBan b532 (consBan b533 (consBan b534 (consBan b535 (consBan b536 (consBan b537 (consBan b538 (consBan b539 (consBan b540 (consBan b541 (consBan b542 (consBan b543 (consBan b544 (consBan b545 (consBan b546 (consBan b547 (consBan b548 (consBan b549 (consBan b550 (consBan b551 (consBan b552 (consBan b553 (consBan b554 (consBan b555 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b557 : Ban 12 4 v512 := checkedSmall
theorem b558 : Ban 12 4 v513 := checkedSmall
theorem b559 : Ban 12 4 v514 := checkedSmall
theorem b560 : Ban 12 4 v515 := checkedSmall
theorem b561 : Ban 12 4 v516 := checkedSmall
theorem b562 : Ban 12 4 v517 := checkedSmall
theorem b563 : Ban 12 4 v518 := checkedSmall
theorem b564 : Ban 12 4 v519 := checkedSmall
theorem b565 : Ban 12 4 v520 := checkedSmall
theorem b566 : Ban 12 4 v521 := checkedSmall
theorem b567 : Ban 12 4 v522 := checkedSmall
theorem b568 : Ban 12 4 v523 := checkedSmall
theorem b569 : Ban 12 4 v524 := checkedSmall
theorem b570 : Ban 12 4 v525 := checkedSmall
theorem b571 : Ban 12 4 v526 := checkedSmall
theorem b572 : Ban 12 4 v527 := checkedSmall
theorem b573 : Ban 12 4 v528 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b574 : Ban 12 5 v394 := viaBranch (ws := [v512,v513,v514,v515,v516,v517,v518,v519,v520,v521,v522,v523,v524,v392,v470,v525,v526,v527,v528]) (consBan b557 (consBan b558 (consBan b559 (consBan b560 (consBan b561 (consBan b562 (consBan b563 (consBan b564 (consBan b565 (consBan b566 (consBan b567 (consBan b568 (consBan b569 (consBan b401 (consBan b513 (consBan b570 (consBan b571 (consBan b572 (consBan b573 (nilBan 12 4)))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b575 : Ban 12 5 v395 := viaPerm map23_21 map23_21 b574 (by decide +kernel) (by decide +kernel)
theorem b576 : Ban 12 5 v529 := checkedSmall
theorem b577 : Ban 12 4 v532 := checkedSmall
theorem b578 : Ban 12 4 v533 := checkedSmall
theorem b579 : Ban 12 4 v534 := checkedSmall
theorem b580 : Ban 12 4 v535 := checkedSmall
theorem b581 : Ban 12 4 v536 := checkedSmall
theorem b582 : Ban 12 4 v537 := smallByCut p23_2055 w16
theorem b583 : Ban 12 4 v538 := checkedSmall
theorem b584 : Ban 12 4 v539 := checkedSmall
theorem b585 : Ban 12 4 v540 := checkedSmall
theorem b586 : Ban 12 4 v541 := checkedSmall
theorem b587 : Ban 12 4 v542 := checkedSmall
theorem b588 : Ban 12 4 v543 := checkedSmall
theorem b589 : Ban 12 4 v544 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b590 : Ban 12 5 v531 := viaBranch (ws := [v73,v532,v75,v533,v534,v535,v536,v537,v419,v538,v539,v540,v541,v542,v543,v544]) (consBan b68 (consBan b577 (consBan b70 (consBan b578 (consBan b579 (consBan b580 (consBan b581 (consBan b582 (consBan b452 (consBan b583 (consBan b584 (consBan b585 (consBan b586 (consBan b587 (consBan b588 (consBan b589 (nilBan 12 4))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b591 : Ban 12 5 v530 := viaPerm map23_6 map23_6 b590 (by decide +kernel) (by decide +kernel)
theorem b592 : Ban 12 5 v545 := checkedSmall
theorem b593 : Ban 12 5 v546 := checkedSmall
theorem b594 : Ban 12 5 v547 := checkedSmall
theorem b595 : Ban 12 4 v548 := checkedSmall
theorem b596 : Ban 12 4 v549 := checkedSmall
theorem b597 : Ban 12 4 v550 := checkedSmall
theorem b598 : Ban 12 4 v551 := checkedSmall
theorem b599 : Ban 12 4 v552 := checkedSmall
theorem b600 : Ban 12 4 v553 := checkedSmall
theorem b601 : Ban 12 4 v554 := checkedSmall
theorem b602 : Ban 12 4 v555 := checkedSmall
theorem b603 : Ban 12 4 v556 := checkedSmall
theorem b604 : Ban 12 4 v557 := checkedSmall
theorem b605 : Ban 12 4 v558 := checkedSmall
theorem b606 : Ban 12 4 v559 := checkedSmall
theorem b607 : Ban 12 4 v560 := checkedSmall
theorem b608 : Ban 12 4 v561 := checkedSmall
theorem b609 : Ban 12 4 v562 := checkedSmall
theorem b610 : Ban 12 4 v563 := checkedSmall
theorem b611 : Ban 12 4 v564 := checkedSmall
theorem b612 : Ban 12 4 v565 := checkedSmall
theorem b613 : Ban 12 4 v566 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b614 : Ban 12 5 v90 := viaBranch (ws := [v409,v548,v549,v550,v551,v552,v553,v554,v555,v556,v557,v558,v559,v560,v561,v562,v563,v564,v89,v565,v566]) (consBan b440 (consBan b595 (consBan b596 (consBan b597 (consBan b598 (consBan b599 (consBan b600 (consBan b601 (consBan b602 (consBan b603 (consBan b604 (consBan b605 (consBan b606 (consBan b607 (consBan b608 (consBan b609 (consBan b610 (consBan b611 (consBan b84 (consBan b612 (consBan b613 (nilBan 12 4)))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b615 : Ban 12 5 v396 := viaPerm map23_7 map23_7 b614 (by decide +kernel) (by decide +kernel)
theorem b616 : Ban 12 5 v567 := checkedSmall
theorem b617 : Ban 12 4 v569 := checkedSmall
theorem b618 : Ban 12 4 v570 := checkedSmall
theorem b619 : Ban 12 4 v571 := checkedSmall
theorem b620 : Ban 12 4 v572 := checkedSmall
theorem b621 : Ban 12 4 v573 := checkedSmall
theorem b622 : Ban 12 4 v574 := checkedSmall
theorem b623 : Ban 12 4 v575 := checkedSmall
theorem b624 : Ban 12 4 v576 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b625 : Ban 12 5 v568 := viaBranch (ws := [v569,v570,v385,v222,v387,v438,v571,v572,v573,v574,v575,v576,v397]) (consBan b617 (consBan b618 (consBan b394 (consBan b222 (consBan b396 (consBan b474 (consBan b619 (consBan b620 (consBan b621 (consBan b622 (consBan b623 (consBan b624 (consBan b406 (nilBan 12 4)))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b627 : Ban 12 5 v397 := smallByCut p23_2055 w16
theorem b628 : Ban 12 5 v578 := checkedSmall
theorem b629 : Ban 12 5 v579 := checkedSmall
theorem b630 : Ban 12 5 v398 := viaPerm map23_13 map23_10 b614 (by decide +kernel) (by decide +kernel)
theorem b631 : Ban 12 5 v580 := checkedSmall
theorem b632 : Ban 12 5 v581 := viaPerm map23_2 map23_2 b625 (by decide +kernel) (by decide +kernel)
theorem b633 : Ban 12 5 v399 := smallByCut p23_2055 w16
theorem b634 : Ban 12 5 v582 := checkedSmall
theorem b635 : Ban 12 5 v583 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b636 : Ban 12 6 v58 := viaBranch (ws := [v384,v56,v412,v385,v413,v386,v430,v387,v444,v388,v462,v80,v463,v389,v464,v390,v465,v391,v466,v392,v57,v479,v480,v481,v482,v483,v484,v485,v486,v487,v393,v394,v395,v529,v530,v545,v546,v547,v396,v567,v568,v397,v578,v579,v398,v580,v581,v399,v582,v583]) (consBan b444 (consBan b415 (consBan b445 (consBan b446 (consBan b447 (consBan b464 (consBan b465 (consBan b481 (consBan b482 (consBan b500 (consBan b501 (consBan b502 (consBan b503 (consBan b504 (consBan b505 (consBan b506 (consBan b507 (consBan b508 (consBan b509 (consBan b522 (consBan b416 (consBan b523 (consBan b524 (consBan b525 (consBan b526 (consBan b527 (consBan b528 (consBan b529 (consBan b530 (consBan b531 (consBan b556 (consBan b574 (consBan b575 (consBan b576 (consBan b591 (consBan b592 (consBan b593 (consBan b594 (consBan b615 (consBan b616 (consBan b625 (consBan b627 (consBan b628 (consBan b629 (consBan b630 (consBan b631 (consBan b632 (consBan b633 (consBan b634 (consBan b635 (nilBan 12 5))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b637 : Ban 12 6 v54 := viaPerm map23_1 map23_1 b636 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w17 : Wide 12 6 v54 := viaSub (ws := [v47,v54]) (consBan b430 (consBan b637 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b1 : Ban 27 6 v4 := smallByCut p31_23 w17
theorem b2 : Ban 27 6 v5 := smallByCut p31_27 w2
theorem b347 : Ban 12 4 v341 := checkedSmall
theorem b348 : Ban 12 4 v342 := checkedSmall
theorem b349 : Ban 12 4 v343 := checkedSmall
theorem b350 : Ban 12 4 v344 := checkedSmall
theorem b351 : Ban 12 4 v345 := checkedSmall
theorem b352 : Ban 12 4 v346 := checkedSmall
theorem b353 : Ban 12 4 v347 := checkedSmall
theorem b354 : Ban 12 4 v348 := checkedSmall
theorem b355 : Ban 12 4 v349 := checkedSmall
theorem b356 : Ban 12 4 v350 := checkedSmall
theorem b357 : Ban 12 4 v351 := checkedSmall
theorem b358 : Ban 12 4 v352 := checkedSmall
theorem b359 : Ban 12 4 v353 := checkedSmall
theorem b360 : Ban 12 4 v354 := checkedSmall
theorem b361 : Ban 12 4 v355 := checkedSmall
theorem b362 : Ban 12 4 v356 := checkedSmall
theorem b363 : Ban 12 4 v357 := checkedSmall
theorem b364 : Ban 12 4 v358 := checkedSmall
theorem b365 : Ban 12 4 v359 := checkedSmall
theorem b366 : Ban 12 4 v360 := checkedSmall
theorem b367 : Ban 12 4 v361 := checkedSmall
theorem b368 : Ban 12 4 v362 := checkedSmall
theorem b369 : Ban 12 4 v363 := checkedSmall
theorem b370 : Ban 12 4 v364 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b371 : Ban 12 5 v340 := viaBranch (ws := [v341,v342,v343,v344,v345,v346,v347,v348,v349,v350,v351,v352,v353,v354,v355,v356,v357,v358,v359,v360,v361,v362,v363,v364]) (consBan b347 (consBan b348 (consBan b349 (consBan b350 (consBan b351 (consBan b352 (consBan b353 (consBan b354 (consBan b355 (consBan b356 (consBan b357 (consBan b358 (consBan b359 (consBan b360 (consBan b361 (consBan b362 (consBan b363 (consBan b364 (consBan b365 (consBan b366 (consBan b367 (consBan b368 (consBan b369 (consBan b370 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b372 : Ban 12 5 v365 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w14 : Wide 12 5 v365 := viaSub (ws := [v340,v365]) (consBan b371 (consBan b372 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b3 : Ban 27 6 v6 := smallByCut p31_2063 w14
theorem b4 : Ban 27 6 v7 := smallByCut p31_27 w2
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
theorem b26 : Ban 12 4 v31 := checkedSmall
theorem b27 : Ban 12 4 v32 := checkedSmall
theorem b28 : Ban 12 4 v33 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b29 : Ban 12 5 v9 := viaBranch (ws := [v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33]) (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b10 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (consBan b19 (consBan b20 (consBan b21 (consBan b22 (consBan b23 (consBan b24 (consBan b25 (consBan b26 (consBan b27 (consBan b28 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b30 : Ban 12 5 v34 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w0 : Wide 12 5 v34 := viaSub (ws := [v9,v34]) (consBan b29 (consBan b30 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b31 : Ban 27 6 v8 := smallByCut p31_15 w0
theorem b32 : Ban 27 6 v35 := smallByCut p31_27 w2
theorem b33 : Ban 27 6 v36 := smallByCut p31_27 w2
theorem b34 : Ban 27 6 v37 := smallByCut p31_27 w2
theorem b35 : Ban 27 6 v38 := smallByCut p31_29 w2
theorem b36 : Ban 27 6 v39 := smallByCut p31_27 w2
theorem b37 : Ban 27 6 v40 := smallByCut p31_27 w2
theorem b38 : Ban 27 6 v41 := smallByCut p31_27 w2
theorem b39 : Ban 27 6 v42 := smallByCut p31_27 w2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w21 : Wide 12 6 v58 := viaSub (ws := [v47,v58]) (consBan b430 (consBan b636 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b40 : Ban 27 6 v43 := smallByCut p31_23 w21
theorem b41 : Ban 27 6 v44 := smallByCut p31_27 w2
theorem b90 : Ban 27 6 v46 := smallByCut p31_23 w1
theorem b91 : Ban 27 6 v45 := viaPerm map31_1 map31_1 b90 (by decide +kernel) (by decide +kernel)
theorem b92 : Ban 27 6 v93 := smallByCut p31_27 w2
theorem b94 : Ban 27 6 v94 := smallByCut p31_27 w2
theorem b95 : Ban 27 6 v96 := smallByCut p31_27 w2
theorem b98 : Ban 27 6 v97 := smallByCut p31_23 w21
theorem b99 : Ban 27 6 v99 := smallByCut p31_27 w2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w10 : Wide 12 5 v9 := viaSub (ws := [v9]) (consBan b29 (nilBan 12 5)) (by decide) (by decide +kernel)
theorem b301 : Ban 12 4 v9 := bySubset w10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w11 : Wide 12 4 v9 := viaSub (ws := [v9]) (consBan b301 (nilBan 12 4)) (by decide) (by decide +kernel)
theorem b100 : Ban 27 6 v100 := smallByCut p31_15 w11
theorem b101 : Ban 27 6 v101 := smallByCut p31_27 w2
theorem b102 : Ban 27 6 v102 := checkedSmall
theorem b103 : Ban 27 6 v103 := smallByCut p31_27 w2
theorem b104 : Ban 27 6 v104 := smallByCut p31_2063 w14
theorem b105 : Ban 27 6 v105 := smallByCut p31_27 w2
theorem b106 : Ban 27 6 v106 := smallByCut p31_15 w11
theorem b107 : Ban 27 6 v107 := smallByCut p31_27 w2
theorem b108 : Ban 27 6 v108 := smallByCut p31_30 w2
theorem b109 : Ban 27 6 v109 := smallByCut p31_30 w2
theorem b110 : Ban 27 6 v110 := smallByCut p31_30 w2
theorem b111 : Ban 27 6 v111 := smallByCut p31_30 w2
theorem b112 : Ban 27 5 v113 := smallByCut p31_27 w2
theorem b113 : Ban 27 5 v114 := smallByCut p31_27 w2
theorem b114 : Ban 27 5 v115 := smallByCut p31_27 w2
theorem b115 : Ban 27 5 v116 := smallByCut p31_27 w2
theorem b116 : Ban 12 4 v118 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w4 : Wide 12 4 v118 := viaSub (ws := [v118]) (consBan b116 (nilBan 12 4)) (by decide) (by decide +kernel)
theorem b117 : Ban 27 5 v117 := smallByCut p31_23 w4
theorem b118 : Ban 27 5 v119 := smallByCut p31_27 w2
theorem b119 : Ban 27 5 v120 := checkedSmall
theorem b120 : Ban 27 5 v121 := smallByCut p31_27 w2
theorem b121 : Ban 27 5 v122 := smallByCut p31_27 w2
theorem solidb79 : Wide 12 4 v84 := solid b79
theorem b122 : Ban 27 5 v123 := smallByCut p31_23 solidb79
theorem b123 : Ban 27 5 v124 := smallByCut p31_27 w2
theorem b124 : Ban 27 5 v125 := smallByCut p31_27 w2
theorem b125 : Ban 27 5 v126 := smallByCut p31_27 w2
theorem b126 : Ban 27 5 v127 := smallByCut p31_27 w2
theorem b127 : Ban 27 5 v128 := smallByCut p31_27 w2
theorem b128 : Ban 27 5 v129 := smallByCut p31_27 w2
theorem b129 : Ban 27 5 v130 := smallByCut p31_27 w2
theorem b130 : Ban 27 5 v131 := smallByCut p31_27 w2
theorem b131 : Ban 27 5 v132 := checkedSmall
theorem b132 : Ban 27 5 v133 := checkedSmall
theorem b133 : Ban 27 5 v134 := checkedSmall
theorem b134 : Ban 27 5 v135 := checkedSmall
theorem b135 : Ban 27 5 v136 := smallByCut p31_23 solidb79
theorem b136 : Ban 27 5 v137 := smallByCut p31_23 solidb79
theorem b137 : Ban 27 5 v138 := smallByCut p31_23 solidb79
theorem b138 : Ban 27 5 v139 := smallByCut p31_23 solidb79
theorem b139 : Ban 27 5 v140 := checkedSmall
theorem b140 : Ban 27 5 v141 := checkedSmall
theorem b141 : Ban 27 5 v142 := checkedSmall
theorem b142 : Ban 27 5 v143 := checkedSmall
theorem b143 : Ban 27 5 v144 := smallByCut p31_23 solidb79
theorem b144 : Ban 27 5 v145 := smallByCut p31_23 solidb79
theorem b145 : Ban 27 5 v146 := smallByCut p31_23 solidb79
theorem b146 : Ban 27 5 v147 := smallByCut p31_23 solidb79
theorem b147 : Ban 27 5 v148 := checkedSmall
theorem b148 : Ban 27 5 v149 := checkedSmall
theorem b149 : Ban 27 5 v150 := checkedSmall
theorem b150 : Ban 27 5 v151 := checkedSmall
theorem b151 : Ban 27 5 v152 := checkedSmall
theorem b152 : Ban 27 5 v153 := checkedSmall
theorem b153 : Ban 27 5 v154 := smallByCut p31_23 solidb79
theorem b192 : Ban 12 4 v193 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w5 : Wide 12 4 v193 := viaSub (ws := [v193]) (consBan b192 (nilBan 12 4)) (by decide) (by decide +kernel)
theorem b154 : Ban 27 5 v155 := smallByCut p31_27 w5
theorem b155 : Ban 27 5 v156 := smallByCut p31_23 solidb79
theorem b156 : Ban 27 5 v157 := smallByCut p31_23 solidb79
theorem b196 : Ban 12 4 v197 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w6 : Wide 12 4 v197 := viaSub (ws := [v197]) (consBan b196 (nilBan 12 4)) (by decide) (by decide +kernel)
theorem b157 : Ban 27 5 v158 := smallByCut p31_27 w6
theorem b158 : Ban 27 5 v159 := smallByCut p31_23 solidb79
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b159 : Ban 27 6 v112 := viaBranch (ws := [v113,v114,v115,v116,v117,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159]) (consBan b112 (consBan b113 (consBan b114 (consBan b115 (consBan b117 (consBan b118 (consBan b119 (consBan b120 (consBan b121 (consBan b122 (consBan b123 (consBan b124 (consBan b125 (consBan b126 (consBan b127 (consBan b128 (consBan b129 (consBan b130 (consBan b131 (consBan b132 (consBan b133 (consBan b134 (consBan b135 (consBan b136 (consBan b137 (consBan b138 (consBan b139 (consBan b140 (consBan b141 (consBan b142 (consBan b143 (consBan b144 (consBan b145 (consBan b146 (consBan b147 (consBan b148 (consBan b149 (consBan b150 (consBan b151 (consBan b152 (consBan b153 (consBan b154 (consBan b155 (consBan b156 (consBan b157 (consBan b158 (nilBan 27 5))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b161 : Ban 27 6 v160 := smallByCut p31_30 w2
theorem b160 : Ban 27 6 v161 := smallByCut p31_27 w2
theorem b162 : Ban 27 6 v162 := smallByCut p31_27 w2
theorem b163 : Ban 27 6 v163 := smallByCut p31_30 w2
theorem b164 : Ban 27 6 v164 := smallByCut p31_30 w2
theorem b165 : Ban 27 6 v165 := smallByCut p31_30 w2
theorem b166 : Ban 27 6 v166 := smallByCut p31_30 w2
theorem b167 : Ban 27 6 v167 := smallByCut p31_30 w2
theorem b168 : Ban 27 6 v168 := smallByCut p31_30 w2
theorem b169 : Ban 27 6 v169 := smallByCut p31_30 w2
theorem b170 : Ban 27 6 v170 := smallByCut p31_30 w2
theorem b171 : Ban 27 6 v171 := smallByCut p31_27 w2
theorem b172 : Ban 27 6 v172 := smallByCut p31_27 w2
theorem b173 : Ban 27 6 v173 := smallByCut p31_27 w2
theorem b174 : Ban 27 6 v174 := smallByCut p31_27 w2
theorem b175 : Ban 27 6 v175 := checkedSmall
theorem b176 : Ban 27 6 v176 := checkedSmall
theorem b177 : Ban 27 6 v177 := checkedSmall
theorem b178 : Ban 27 6 v178 := checkedSmall
theorem b179 : Ban 27 6 v179 := checkedSmall
theorem b180 : Ban 27 6 v180 := checkedSmall
theorem b181 : Ban 27 6 v181 := checkedSmall
theorem b182 : Ban 27 6 v182 := checkedSmall
theorem b183 : Ban 27 6 v183 := smallByCut p31_27 w2
theorem b184 : Ban 27 6 v184 := smallByCut p31_27 w2
theorem b185 : Ban 27 6 v185 := smallByCut p31_27 w2
theorem b186 : Ban 27 6 v186 := smallByCut p31_27 w2
theorem b187 : Ban 27 6 v187 := smallByCut p31_27 w2
theorem b188 : Ban 27 6 v188 := smallByCut p31_27 w2
theorem b189 : Ban 27 6 v189 := smallByCut p31_27 w2
theorem b190 : Ban 27 6 v190 := smallByCut p31_27 w2
theorem b191 : Ban 27 6 v191 := checkedSmall
theorem b193 : Ban 27 6 v192 := smallByCut p31_27 w5
theorem b194 : Ban 27 6 v194 := checkedSmall
theorem b195 : Ban 27 6 v195 := checkedSmall
theorem b197 : Ban 27 6 v196 := smallByCut p31_27 w6
theorem b198 : Ban 27 6 v198 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b199 : Ban 27 7 v2 := viaBranch (ws := [v3,v4,v5,v6,v7,v8,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v93,v94,v96,v97,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v160,v161,v162,v163,v164,v165,v166,v167,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184,v185,v186,v187,v188,v189,v190,v191,v192,v194,v195,v196,v198]) (consBan b0 (consBan b1 (consBan b2 (consBan b3 (consBan b4 (consBan b31 (consBan b32 (consBan b33 (consBan b34 (consBan b35 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (consBan b40 (consBan b41 (consBan b91 (consBan b92 (consBan b94 (consBan b95 (consBan b98 (consBan b99 (consBan b100 (consBan b101 (consBan b102 (consBan b103 (consBan b104 (consBan b105 (consBan b106 (consBan b107 (consBan b108 (consBan b109 (consBan b110 (consBan b111 (consBan b159 (consBan b161 (consBan b160 (consBan b162 (consBan b163 (consBan b164 (consBan b165 (consBan b166 (consBan b167 (consBan b168 (consBan b169 (consBan b170 (consBan b171 (consBan b172 (consBan b173 (consBan b174 (consBan b175 (consBan b176 (consBan b177 (consBan b178 (consBan b179 (consBan b180 (consBan b181 (consBan b182 (consBan b183 (consBan b184 (consBan b185 (consBan b186 (consBan b187 (consBan b188 (consBan b189 (consBan b190 (consBan b191 (consBan b193 (consBan b194 (consBan b195 (consBan b197 (consBan b198 (nilBan 27 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b200 : Ban 27 7 v1 := viaPerm map31_1 map31_1 b199 (by decide +kernel) (by decide +kernel)
theorem b201 : Ban 27 6 v200 := viaPerm map31_1 map31_1 b159 (by decide +kernel) (by decide +kernel)
theorem b202 : Ban 27 6 v201 := smallByCut p31_30 w2
theorem b203 : Ban 27 6 v202 := smallByCut p31_29 w2
theorem b204 : Ban 27 6 v203 := smallByCut p31_29 w2
theorem b206 : Ban 27 6 v204 := smallByCut p31_30 w2
theorem b207 : Ban 27 6 v206 := smallByCut p31_30 w2
theorem b205 : Ban 27 6 v205 := smallByCut p31_29 w2
theorem b208 : Ban 27 6 v207 := smallByCut p31_29 w2
theorem b209 : Ban 27 6 v208 := smallByCut p31_29 w2
theorem b210 : Ban 27 6 v209 := checkedSmall
theorem b211 : Ban 27 6 v210 := smallByCut p31_30 w2
theorem b212 : Ban 27 6 v211 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w9 : Wide 12 4 v49 := viaSub (ws := [v47,v49]) (consBan b96 (consBan b43 (nilBan 12 4))) (by decide) (by decide +kernel)
theorem b213 : Ban 27 6 v212 := smallByCut p31_23 w9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w7 : Wide 12 5 v49 := viaSub (ws := [v47,v49]) (consBan b66 (consBan b233 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b234 : Ban 27 6 v213 := smallByCut p31_23 w7
theorem b235 : Ban 27 6 v233 := smallByCut p31_23 w7
theorem b236 : Ban 27 6 v234 := smallByCut p31_23 w7
theorem b237 : Ban 27 6 v235 := smallByCut p31_23 w7
theorem b238 : Ban 27 6 v236 := smallByCut p31_23 w9
theorem b239 : Ban 27 6 v237 := smallByCut p31_30 w2
theorem b240 : Ban 27 6 v238 := checkedSmall
theorem b241 : Ban 27 6 v239 := smallByCut p31_30 w2
theorem b242 : Ban 27 6 v240 := checkedSmall
theorem b243 : Ban 27 6 v241 := smallByCut p31_30 w2
theorem b244 : Ban 27 6 v242 := smallByCut p31_29 w2
theorem b245 : Ban 27 6 v243 := checkedSmall
theorem b246 : Ban 27 6 v244 := smallByCut p31_29 w2
theorem b247 : Ban 27 6 v245 := checkedSmall
theorem b248 : Ban 27 6 v246 := smallByCut p31_23 w9
theorem b249 : Ban 27 6 v247 := smallByCut p31_23 w7
theorem b250 : Ban 27 6 v248 := smallByCut p31_23 w7
theorem b251 : Ban 27 6 v249 := smallByCut p31_23 w7
theorem b252 : Ban 27 6 v250 := smallByCut p31_23 w7
theorem b253 : Ban 27 6 v251 := smallByCut p31_23 w9
theorem b254 : Ban 27 6 v252 := smallByCut p31_29 w2
theorem b255 : Ban 27 6 v253 := checkedSmall
theorem b256 : Ban 27 6 v254 := smallByCut p31_29 w2
theorem b257 : Ban 27 6 v255 := checkedSmall
theorem b258 : Ban 27 6 v256 := smallByCut p31_27 w2
theorem b259 : Ban 27 6 v257 := checkedSmall
theorem b260 : Ban 12 5 v222 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w8 : Wide 12 5 v222 := viaSub (ws := [v47,v222]) (consBan b66 (consBan b260 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b261 : Ban 27 6 v258 := smallByCut p31_23 w8
theorem b262 : Ban 27 6 v259 := checkedSmall
theorem b263 : Ban 27 6 v260 := checkedSmall
theorem b264 : Ban 27 6 v261 := checkedSmall
theorem b265 : Ban 27 6 v262 := smallByCut p31_27 w2
theorem b266 : Ban 27 6 v263 := checkedSmall
theorem b267 : Ban 27 6 v264 := smallByCut p31_23 w21
theorem b268 : Ban 27 6 v265 := smallByCut p31_23 w9
theorem b269 : Ban 27 6 v266 := smallByCut p31_23 w7
theorem b270 : Ban 27 6 v267 := smallByCut p31_23 w7
theorem b271 : Ban 27 6 v268 := smallByCut p31_23 w7
theorem b272 : Ban 27 6 v269 := smallByCut p31_23 w7
theorem b273 : Ban 27 6 v270 := smallByCut p31_23 w21
theorem b274 : Ban 27 6 v271 := smallByCut p31_23 w9
theorem b275 : Ban 27 6 v272 := smallByCut p31_15 w10
theorem b276 : Ban 27 5 v274 := checkedSmall
theorem b277 : Ban 27 5 v275 := checkedSmall
theorem b278 : Ban 27 5 v276 := checkedSmall
theorem b279 : Ban 27 5 v277 := checkedSmall
theorem b280 : Ban 27 5 v278 := checkedSmall
theorem b281 : Ban 27 5 v279 := checkedSmall
theorem b282 : Ban 27 5 v280 := checkedSmall
theorem b283 : Ban 27 5 v281 := checkedSmall
theorem b284 : Ban 27 5 v282 := checkedSmall
theorem b285 : Ban 27 5 v283 := checkedSmall
theorem b286 : Ban 27 5 v284 := checkedSmall
theorem b287 : Ban 27 5 v285 := smallByCut p31_2063 w14
theorem b288 : Ban 27 5 v286 := checkedSmall
theorem b306 : Ban 12 4 v302 := smallByCut p23_2055 w16
theorem b308 : Ban 12 4 v304 := smallByCut p23_2055 w16
theorem b309 : Ban 12 4 v305 := smallByCut p23_2055 w16
theorem b310 : Ban 12 4 v306 := smallByCut p23_2055 w16
theorem b311 : Ban 12 4 v307 := smallByCut p23_2055 w16
theorem b312 : Ban 12 4 v308 := smallByCut p23_2055 w16
theorem b313 : Ban 12 4 v309 := smallByCut p23_2055 w16
theorem b314 : Ban 12 4 v310 := smallByCut p23_2055 w16
theorem b315 : Ban 12 4 v311 := smallByCut p23_2055 w16
theorem b316 : Ban 12 4 v312 := smallByCut p23_2055 w16
theorem b317 : Ban 12 4 v313 := smallByCut p23_2055 w16
theorem b318 : Ban 12 4 v314 := checkedSmall
theorem b319 : Ban 12 4 v315 := checkedSmall
theorem b320 : Ban 12 4 v316 := checkedSmall
theorem b321 : Ban 12 4 v317 := checkedSmall
theorem b322 : Ban 12 4 v318 := checkedSmall
theorem b323 : Ban 12 4 v319 := checkedSmall
theorem b324 : Ban 12 4 v320 := checkedSmall
theorem b325 : Ban 12 4 v321 := checkedSmall
theorem b326 : Ban 12 4 v322 := checkedSmall
theorem b327 : Ban 12 4 v323 := checkedSmall
theorem b328 : Ban 12 4 v324 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b329 : Ban 12 5 v230 := viaBranch (ws := [v302,v303,v304,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v231,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324]) (consBan b306 (consBan b307 (consBan b308 (consBan b309 (consBan b310 (consBan b311 (consBan b312 (consBan b313 (consBan b314 (consBan b315 (consBan b316 (consBan b317 (consBan b318 (consBan b231 (consBan b319 (consBan b320 (consBan b321 (consBan b322 (consBan b323 (consBan b324 (consBan b325 (consBan b326 (consBan b327 (consBan b328 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b331 : Ban 12 4 v325 := checkedSmall
theorem b332 : Ban 12 4 v326 := checkedSmall
theorem b333 : Ban 12 4 v327 := checkedSmall
theorem b334 : Ban 12 4 v328 := checkedSmall
theorem b335 : Ban 12 4 v329 := checkedSmall
theorem b336 : Ban 12 4 v330 := checkedSmall
theorem b337 : Ban 12 4 v331 := checkedSmall
theorem b338 : Ban 12 4 v332 := checkedSmall
theorem b339 : Ban 12 4 v333 := checkedSmall
theorem b340 : Ban 12 4 v334 := checkedSmall
theorem b341 : Ban 12 4 v335 := checkedSmall
theorem b342 : Ban 12 4 v336 := checkedSmall
theorem b343 : Ban 12 4 v337 := checkedSmall
theorem b344 : Ban 12 4 v338 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b345 : Ban 12 5 v231 := viaBranch (ws := [v227,v325,v228,v326,v327,v328,v329,v330,v316,v315,v331,v332,v333,v334,v335,v336,v337,v338]) (consBan b227 (consBan b331 (consBan b228 (consBan b332 (consBan b333 (consBan b334 (consBan b335 (consBan b336 (consBan b320 (consBan b319 (consBan b337 (consBan b338 (consBan b339 (consBan b340 (consBan b341 (consBan b342 (consBan b343 (consBan b344 (nilBan 12 4))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w13 : Wide 12 5 v231 := viaSub (ws := [v230,v231]) (consBan b329 (consBan b345 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b289 : Ban 27 5 v287 := smallByCut p31_23 w13
theorem b290 : Ban 27 5 v288 := checkedSmall
theorem b291 : Ban 27 5 v289 := checkedSmall
theorem b292 : Ban 27 5 v290 := checkedSmall
theorem b293 : Ban 27 5 v291 := checkedSmall
theorem b294 : Ban 27 5 v292 := checkedSmall
theorem b295 : Ban 27 5 v293 := checkedSmall
theorem solidb227 : Wide 12 4 v227 := solid b227
theorem b296 : Ban 27 5 v294 := smallByCut p31_23 solidb227
theorem b297 : Ban 27 5 v295 := checkedSmall
theorem b298 : Ban 27 5 v296 := checkedSmall
theorem b299 : Ban 27 5 v297 := smallByCut p31_23 solidb227
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b300 : Ban 27 6 v273 := viaBranch (ws := [v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297]) (consBan b276 (consBan b277 (consBan b278 (consBan b279 (consBan b280 (consBan b281 (consBan b282 (consBan b283 (consBan b284 (consBan b285 (consBan b286 (consBan b287 (consBan b288 (consBan b289 (consBan b290 (consBan b291 (consBan b292 (consBan b293 (consBan b294 (consBan b295 (consBan b296 (consBan b297 (consBan b298 (consBan b299 (nilBan 27 5))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b302 : Ban 27 6 v298 := smallByCut p31_15 w11
theorem b303 : Ban 27 6 v299 := checkedSmall
theorem b304 : Ban 27 6 v300 := smallByCut p31_23 w8
theorem b305 : Ban 27 6 v301 := checkedSmall
theorem b330 : Ban 27 6 v285 := smallByCut p31_2063 w14
theorem b346 : Ban 27 6 v287 := smallByCut p31_23 w13
theorem b373 : Ban 27 6 v339 := smallByCut p31_2063 w14
theorem b374 : Ban 27 6 v366 := checkedSmall
theorem b375 : Ban 27 6 v367 := smallByCut p31_15 w11
theorem b376 : Ban 27 6 v368 := checkedSmall
theorem b378 : Ban 27 6 v369 := smallByCut p31_23 w9
theorem b379 : Ban 27 6 v371 := smallByCut p31_23 w7
theorem b380 : Ban 27 6 v372 := smallByCut p31_23 w7
theorem b381 : Ban 27 6 v373 := smallByCut p31_23 w9
theorem b382 : Ban 27 6 v374 := checkedSmall
theorem b383 : Ban 27 6 v375 := checkedSmall
theorem b384 : Ban 27 6 v376 := checkedSmall
theorem b385 : Ban 27 6 v377 := checkedSmall
theorem b386 : Ban 27 6 v378 := smallByCut p31_23 w9
theorem b387 : Ban 27 6 v379 := smallByCut p31_23 w7
theorem b388 : Ban 27 6 v380 := smallByCut p31_23 w7
theorem b389 : Ban 27 6 v381 := smallByCut p31_23 w9
theorem b390 : Ban 27 6 v382 := smallByCut p31_23 w7
theorem b391 : Ban 27 6 v383 := smallByCut p31_23 w7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b392 : Ban 27 7 v199 := viaBranch (ws := [v200,v201,v202,v203,v204,v206,v205,v207,v208,v109,v209,v210,v211,v212,v213,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v298,v299,v300,v301,v285,v287,v339,v366,v367,v368,v369,v371,v372,v373,v374,v375,v376,v377,v378,v379,v380,v381,v382,v383]) (consBan b201 (consBan b202 (consBan b203 (consBan b204 (consBan b206 (consBan b207 (consBan b205 (consBan b208 (consBan b209 (consBan b109 (consBan b210 (consBan b211 (consBan b212 (consBan b213 (consBan b234 (consBan b235 (consBan b236 (consBan b237 (consBan b238 (consBan b239 (consBan b240 (consBan b241 (consBan b242 (consBan b243 (consBan b244 (consBan b245 (consBan b246 (consBan b247 (consBan b248 (consBan b249 (consBan b250 (consBan b251 (consBan b252 (consBan b253 (consBan b254 (consBan b255 (consBan b256 (consBan b257 (consBan b258 (consBan b259 (consBan b261 (consBan b262 (consBan b263 (consBan b264 (consBan b265 (consBan b266 (consBan b267 (consBan b268 (consBan b269 (consBan b270 (consBan b271 (consBan b272 (consBan b273 (consBan b274 (consBan b275 (consBan b300 (consBan b302 (consBan b303 (consBan b304 (consBan b305 (consBan b330 (consBan b346 (consBan b373 (consBan b374 (consBan b375 (consBan b376 (consBan b378 (consBan b379 (consBan b380 (consBan b381 (consBan b382 (consBan b383 (consBan b384 (consBan b385 (consBan b386 (consBan b387 (consBan b388 (consBan b389 (consBan b390 (consBan b391 (nilBan 27 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b638 : Ban 27 7 v4 := smallByCut p31_23 w17
theorem b639 : Ban 27 7 v241 := viaPerm map31_1 map31_1 b638 (by decide +kernel) (by decide +kernel)
theorem b640 : Ban 27 7 v208 := viaPerm map31_3 map31_4 b638 (by decide +kernel) (by decide +kernel)
theorem b641 : Ban 27 7 v584 := viaPerm map31_1 map31_1 b392 (by decide +kernel) (by decide +kernel)
theorem b642 : Ban 27 7 v41 := viaPerm map31_5 map31_5 b638 (by decide +kernel) (by decide +kernel)
theorem b644 : Ban 27 7 v585 := smallByCut p31_23 w21
theorem b645 : Ban 27 7 v587 := smallByCut p31_23 w21
theorem b646 : Ban 27 7 v588 := smallByCut p31_23 w21
theorem b648 : Ban 27 7 v589 := smallByCut p31_23 w21
theorem b649 : Ban 27 7 v591 := smallByCut p31_15 w10
theorem b650 : Ban 27 6 v593 := smallByCut p31_30 w2
theorem b651 : Ban 27 6 v594 := smallByCut p31_30 w2
theorem b652 : Ban 27 6 v595 := checkedSmall
theorem b653 : Ban 27 6 v596 := checkedSmall
theorem b654 : Ban 27 6 v597 := smallByCut p31_30 w2
theorem b655 : Ban 27 6 v598 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w20 : Wide 12 5 v57 := viaSub (ws := [v47,v57]) (consBan b66 (consBan b416 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b656 : Ban 27 6 v599 := smallByCut p31_23 w20
theorem b657 : Ban 27 6 v600 := smallByCut p31_23 w20
theorem b658 : Ban 27 6 v601 := smallByCut p31_23 w20
theorem b659 : Ban 27 6 v602 := smallByCut p31_23 w20
theorem b660 : Ban 27 6 v603 := smallByCut p31_15 w10
theorem b661 : Ban 27 6 v604 := smallByCut p31_15 w10
theorem b662 : Ban 27 6 v605 := smallByCut p31_15 w11
theorem b663 : Ban 27 6 v606 := smallByCut p31_15 w11
theorem b664 : Ban 27 6 v607 := smallByCut p31_2063 w14
theorem b665 : Ban 27 6 v608 := smallByCut p31_2063 w14
theorem b666 : Ban 27 6 v609 := smallByCut p31_15 w11
theorem b667 : Ban 27 6 v610 := smallByCut p31_15 w11
theorem b668 : Ban 27 6 v611 := smallByCut p31_15 w11
theorem b669 : Ban 27 6 v612 := checkedSmall
theorem b670 : Ban 27 6 v613 := checkedSmall
theorem b671 : Ban 27 6 v614 := checkedSmall
theorem b672 : Ban 27 6 v615 := checkedSmall
theorem b673 : Ban 27 6 v616 := smallByCut p31_23 w20
theorem b674 : Ban 27 6 v617 := smallByCut p31_23 w20
theorem b675 : Ban 27 6 v618 := smallByCut p31_23 w20
theorem b676 : Ban 27 6 v619 := smallByCut p31_23 w20
theorem b677 : Ban 27 6 v620 := smallByCut p31_15 w11
theorem b678 : Ban 27 6 v621 := smallByCut p31_15 w10
theorem b679 : Ban 27 6 v622 := smallByCut p31_2063 w14
theorem b680 : Ban 27 6 v623 := smallByCut p31_15 w11
theorem b682 : Ban 27 6 v624 := smallByCut p31_29 w2
theorem b683 : Ban 27 6 v626 := checkedSmall
theorem b684 : Ban 27 6 v627 := checkedSmall
theorem b685 : Ban 27 6 v628 := smallByCut p31_2063 w14
theorem b686 : Ban 27 6 v629 := smallByCut p31_2063 w14
theorem b687 : Ban 27 6 v630 := checkedSmall
theorem b688 : Ban 27 6 v631 := checkedSmall
theorem b689 : Ban 27 6 v632 := smallByCut p31_23 w20
theorem b690 : Ban 27 6 v633 := smallByCut p31_23 w20
theorem b691 : Ban 27 6 v634 := smallByCut p31_23 w20
theorem b692 : Ban 27 6 v635 := smallByCut p31_23 w20
theorem b693 : Ban 27 6 v636 := smallByCut p31_15 w11
theorem b694 : Ban 27 6 v637 := smallByCut p31_15 w10
theorem b695 : Ban 27 6 v638 := smallByCut p31_2063 w14
theorem b696 : Ban 27 6 v639 := smallByCut p31_15 w11
theorem b697 : Ban 27 6 v640 := smallByCut p31_27 w2
theorem b698 : Ban 27 6 v641 := checkedSmall
theorem b699 : Ban 27 6 v642 := smallByCut p31_23 w8
theorem b700 : Ban 27 6 v643 := checkedSmall
theorem b701 : Ban 27 6 v644 := smallByCut p31_2063 w14
theorem b702 : Ban 27 6 v645 := smallByCut p31_2063 w14
theorem b703 : Ban 27 6 v646 := checkedSmall
theorem b704 : Ban 27 6 v647 := checkedSmall
theorem b705 : Ban 27 6 v648 := smallByCut p31_23 w20
theorem b706 : Ban 27 6 v649 := smallByCut p31_23 w20
theorem b707 : Ban 27 6 v650 := smallByCut p31_23 w20
theorem b708 : Ban 27 6 v651 := smallByCut p31_23 w20
theorem b709 : Ban 27 6 v652 := smallByCut p31_23 w20
theorem b710 : Ban 27 6 v653 := smallByCut p31_23 w20
theorem b711 : Ban 27 6 v654 := smallByCut p31_23 w21
theorem b712 : Ban 27 6 v655 := smallByCut p31_23 w20
theorem b713 : Ban 27 6 v656 := smallByCut p31_23 w20
theorem b714 : Ban 27 6 v657 := smallByCut p31_23 w20
theorem b715 : Ban 27 6 v658 := smallByCut p31_23 w21
theorem b716 : Ban 27 6 v659 := smallByCut p31_23 w20
theorem b717 : Ban 27 6 v660 := smallByCut p31_23 w20
theorem b718 : Ban 27 6 v661 := smallByCut p31_23 w20
theorem b719 : Ban 27 6 v662 := smallByCut p31_23 w21
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b720 : Ban 27 7 v592 := viaBranch (ws := [v593,v238,v594,v595,v168,v596,v597,v598,v599,v600,v601,v602,v603,v604,v605,v606,v607,v608,v609,v610,v611,v612,v613,v614,v615,v616,v617,v618,v619,v620,v621,v622,v623,v624,v626,v300,v627,v628,v629,v630,v631,v632,v633,v634,v635,v636,v637,v638,v639,v640,v641,v642,v643,v644,v645,v646,v647,v648,v649,v650,v651,v652,v653,v654,v655,v656,v657,v658,v659,v660,v661,v662]) (consBan b650 (consBan b240 (consBan b651 (consBan b652 (consBan b168 (consBan b653 (consBan b654 (consBan b655 (consBan b656 (consBan b657 (consBan b658 (consBan b659 (consBan b660 (consBan b661 (consBan b662 (consBan b663 (consBan b664 (consBan b665 (consBan b666 (consBan b667 (consBan b668 (consBan b669 (consBan b670 (consBan b671 (consBan b672 (consBan b673 (consBan b674 (consBan b675 (consBan b676 (consBan b677 (consBan b678 (consBan b679 (consBan b680 (consBan b682 (consBan b683 (consBan b304 (consBan b684 (consBan b685 (consBan b686 (consBan b687 (consBan b688 (consBan b689 (consBan b690 (consBan b691 (consBan b692 (consBan b693 (consBan b694 (consBan b695 (consBan b696 (consBan b697 (consBan b698 (consBan b699 (consBan b700 (consBan b701 (consBan b702 (consBan b703 (consBan b704 (consBan b705 (consBan b706 (consBan b707 (consBan b708 (consBan b709 (consBan b710 (consBan b711 (consBan b712 (consBan b713 (consBan b714 (consBan b715 (consBan b716 (consBan b717 (consBan b718 (consBan b719 (nilBan 27 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b721 : Ban 27 7 v662 := smallByCut p31_23 w21
theorem b723 : Ban 27 7 v611 := smallByCut p31_15 w10
theorem b724 : Ban 27 7 v664 := viaPerm map31_2 map31_2 b199 (by decide +kernel) (by decide +kernel)
theorem b725 : Ban 27 7 v665 := viaPerm map31_3 map31_4 b392 (by decide +kernel) (by decide +kernel)
theorem b726 : Ban 27 7 v666 := viaPerm map31_2 map31_2 b638 (by decide +kernel) (by decide +kernel)
theorem b727 : Ban 27 7 v667 := viaPerm map31_4 map31_3 b638 (by decide +kernel) (by decide +kernel)
theorem b643 : Ban 27 7 v586 := smallByCut p31_23 w21
theorem b728 : Ban 27 7 v668 := smallByCut p31_23 w21
theorem b729 : Ban 27 7 v669 := smallByCut p31_23 w21
theorem b730 : Ban 27 7 v670 := smallByCut p31_23 w21
theorem b731 : Ban 27 7 v671 := smallByCut p31_15 w10
theorem b732 : Ban 27 7 v672 := viaPerm map31_2 map31_2 b720 (by decide +kernel) (by decide +kernel)
theorem b733 : Ban 27 7 v673 := viaPerm map31_2 map31_2 b721 (by decide +kernel) (by decide +kernel)
theorem b734 : Ban 27 7 v674 := smallByCut p31_15 w10
theorem b735 : Ban 27 7 v675 := smallByCut p31_23 w21
theorem b736 : Ban 27 7 v676 := smallByCut p31_23 w21
theorem b737 : Ban 27 7 v677 := smallByCut p31_23 w21
theorem b647 : Ban 27 7 v590 := smallByCut p31_23 w21
theorem b738 : Ban 27 7 v678 := smallByCut p31_15 w10
theorem b739 : Ban 27 7 v679 := viaPerm map31_4 map31_3 b720 (by decide +kernel) (by decide +kernel)
theorem b740 : Ban 27 7 v680 := viaPerm map31_4 map31_3 b721 (by decide +kernel) (by decide +kernel)
theorem b722 : Ban 27 7 v663 := smallByCut p31_15 w10
theorem b741 : Ban 27 7 v681 := smallByCut p31_23 w21
theorem b742 : Ban 27 7 v682 := smallByCut p31_23 w21
theorem b743 : Ban 27 7 v683 := smallByCut p31_23 w21
theorem b744 : Ban 27 7 v684 := smallByCut p31_23 w21
theorem b745 : Ban 27 7 v685 := smallByCut p31_23 w21
theorem b746 : Ban 27 7 v686 := smallByCut p31_23 w21
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b747 : Ban 27 8 v0 := viaBranch (ws := [v1,v199,v241,v208,v2,v584,v4,v41,v585,v587,v588,v589,v591,v592,v662,v611,v664,v665,v666,v667,v586,v668,v669,v670,v671,v672,v673,v674,v675,v676,v677,v590,v678,v679,v680,v663,v681,v682,v683,v684,v685,v686]) (consBan b200 (consBan b392 (consBan b639 (consBan b640 (consBan b199 (consBan b641 (consBan b638 (consBan b642 (consBan b644 (consBan b645 (consBan b646 (consBan b648 (consBan b649 (consBan b720 (consBan b721 (consBan b723 (consBan b724 (consBan b725 (consBan b726 (consBan b727 (consBan b643 (consBan b728 (consBan b729 (consBan b730 (consBan b731 (consBan b732 (consBan b733 (consBan b734 (consBan b735 (consBan b736 (consBan b737 (consBan b647 (consBan b738 (consBan b739 (consBan b740 (consBan b722 (consBan b741 (consBan b742 (consBan b743 (consBan b744 (consBan b745 (consBan b746 (nilBan 27 7))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem verifiedPin : Wide 27 8 v0 := widen (by decide +kernel) b747
end PEqualNP.Outside.L_meta_12368.Support

namespace PEqualNP.Outside.L_meta_12368.Data
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12368.Support
def target (x : Fin 6 → Bool) := Nat.testBit (4278124160 * 2 ^ 32 + 4276682368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def posBits : ℕ := 0xc5c71a6996565965555534d338d30c2ca2892471c7
def negBits : ℕ := 0x4585184984544865111524431852040c8088046143
def sample (bank : ℕ) (i : Fin 28) (j : Fin 6) := bank.testBit (6*i.val+j.val)
def inputs : List ℕ := [0x821b48b863f49f,0x8c58a519c78e7,0x2168d0661f8f07,0x54002507e00ff8,0xffb6000ffff000,0x8000000]
def seeds : List Wire := [(false,0x821b48b863f49f),(false,0x8c58a519c78e7),(false,0x2168d0661f8f07),(false,0x54002507e00ff8),(false,0xffb6000ffff000),(false,0x8000000)]
set_option maxHeartbeats 10000000 in
theorem listed : ∀ i : Fin 28, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (28+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 28, target (sample posBits i)=true ∧ target (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 28, ∀ b∈inputs, b.testBit i.val≠b.testBit (28+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 28 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 6 C=target) :
    ∃ k≤C.gates.countP counted, Live 28 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 6 → Bool) : C.eval (List.ofFn x)=target x := congrFun eq x
  have good : Good 28 out.2 := by
    intro i hi same
    let j : Fin 28 := ⟨i,hi⟩
    have diff : read i out=read (28+i) out := by
      change (out.1 != out.2.testBit i) = (out.1 != out.2.testBit (28+i))
      rw [same]
    have p := ev i;have n := ev (28+i)
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
def restrictRows : Projection 28 27 := pick (List.range 27) (by decide) (by decide) (by decide)
set_option maxHeartbeats 8000000 in
theorem core_floor : Wide 27 8 restricted := verifiedPin
theorem six_floor : Ban 28 9 inputs := viaCut restrictRows core_floor (by decide) (by decide +kernel) (by decide +kernel)
def witness : Circuit := ⟨[⟨.and,[0,1]⟩, ⟨.or,[0,1]⟩, ⟨.and,[6,2]⟩, ⟨.or,[6,2]⟩, ⟨.and,[7,9]⟩, ⟨.or,[7,9]⟩, ⟨.or,[8,3]⟩, ⟨.or,[10,5]⟩, ⟨.and,[4,13]⟩, ⟨.or,[12,14]⟩, ⟨.and,[11,15]⟩],16⟩
theorem wmono : Monotone2 witness := by simp [Monotone2,witness]
theorem wcomputes : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by decide +kernel
theorem binary_floor {C : Circuit} (fan : FanInTwo C) (d : ∀ x, C.eval (List.ofFn x) = target x) :
    10 ≤ C.gates.countP counted := by
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
    change 11 ≤ s
    omega
  · refine ⟨C,?_,sz,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := fan g hg
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),len⟩
end PEqualNP.Outside.L_meta_12368.Data

theorem PEqualNP.Outside.L_meta_12368 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124160 * 2 ^ 32 + 4276682368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124160 * 2 ^ 32 + 4276682368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_12368.Data.mono_enough
