import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12098.Support

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

def t0 := 0x2ad06dbffc3ff
def t1 := 0x443786d11fe3f
def t2 := 0x858bb161e3fc7
def t3 := 0xd80dda3e03ff8
def t4 := 0xf76e003fffc00
def v0 := [t0,t1,t2,t3,t4]
def t5 := 0x403804103e07
def v1 := [t5,t0,t1,t2,t3,t4]
def t6 := 0x4005821003e38
def v2 := [t0,t6,t1,t2,t3,t4]
def t7 := 0x43204c11c007
def v3 := [t7,t0,t6,t2,t3,t4]
def v4 := [t7,t0,t1,t2,t3,t4]
def v5 := [t7,t0,t6,t1,t2,t3,t4]
def t8 := 0x1800003e00
def v6 := [t8,t0,t1,t2,t3,t4]
def v7 := [t8,t0,t6,t1,t2,t3,t4]
def t9 := 0xc58fb371e3fff
def v8 := [t0,t1,t2,t9,t3,t4]
def v9 := [t0,t6,t1,t2,t9,t3,t4]
def t10 := 0x4004021000038
def v10 := [t0,t10,t1,t2,t3,t4]
def v11 := [t0,t10,t6,t1,t2,t3,t4]
def t11 := 0x858a3161e01c7
def v12 := [t0,t1,t11,t2,t3,t4]
def v13 := [t0,t6,t1,t11,t2,t3,t4]
def t12 := 0x9808582e001c0
def v14 := [t0,t6,t1,t2,t12,t4]
def v15 := [t0,t1,t2,t12,t3,t4]
def v16 := [t0,t6,t1,t2,t12,t3,t4]
def t13 := 0x1000238
def v17 := [t13,t0,t1,t2,t3,t4]
def v18 := [t13,t0,t6,t1,t2,t3,t4]
def t14 := 0x6ad5efbffffff
def v19 := [t0,t1,t14,t2,t3,t4]
def t16 := 0x450cf
def t17 := 0x112333
def t18 := 0x428c3c
def t19 := 0xa80fc0
def v21 := [t16,t17,t18,t19]
def t20 := 0x3
def v22 := [t20,t16,t17,t18,t19]
def t21 := 0x14f
def t22 := 0x4b3
def t23 := 0xa3c
def v23 := [t21,t22,t23]
def p1047_1045 : Projection 12 6 := pick [2,3,6,7,10,11] rfl (by decide +kernel) (by decide)
def t24 := 0x1573ff
def v24 := [t16,t17,t24,t18,t19]
def v25 := [t20,t24,t18,t19]
def v26 := [t20,t16,t24,t18,t19]
def v27 := [t20,t17,t24,t18,t19]
def t25 := 0x450cc
def v28 := [t25,t16,t24,t18,t19]
def t26 := 0x112330
def v29 := [t26,t17,t24,t18,t19]
def v30 := [t16,t26,t17,t18,t19]
def t27 := 0x46dcff
def v31 := [t17,t24,t18,t27,t19]
def t28 := 0x450c3
def v32 := [t28,t17,t24,t18,t19]
def t29 := 0xac5fcf
def v33 := [t17,t24,t18,t19,t29]
def t30 := 0x4500f
def v34 := [t30,t17,t24,t18,t19]
def v35 := [t25,t16,t17,t18,t19]
def t31 := 0x53af3f
def v36 := [t16,t24,t18,t31,t19]
def t32 := 0x112303
def v37 := [t16,t32,t24,t18,t19]
def t33 := 0xb92ff3
def v38 := [t16,t24,t18,t19,t33]
def t34 := 0x112033
def v39 := [t16,t34,t24,t18,t19]
def t35 := 0x3c
def v40 := [t35,t16,t17,t18,t19]
def t36 := 0x57ffff
def v41 := [t16,t17,t18,t36,t19]
def t37 := 0x1573c3
def v42 := [t16,t17,t37,t18,t19]
def t38 := 0x428c00
def v43 := [t16,t17,t38,t18,t19]
def t39 := 0x3c0
def v44 := [t39,t16,t17,t18,t19]
def t40 := 0xbd7fff
def v45 := [t16,t17,t18,t19,t40]
def t41 := 0x15703f
def v46 := [t16,t17,t41,t18,t19]
def t42 := 0xa80c00
def v47 := [t16,t17,t18,t42,t19]
def v48 := [t30,t16,t17,t18,t19]
def p1047_1046 : Projection 12 6 := pick [4,5,8,9,10,11] rfl (by decide +kernel) (by decide)
def map1047_3 : Projection 12 12 := pick [2,3,6,7,10,11,0,1,5,4,9,8] rfl (by decide +kernel) (by decide)
def map1047_4 : Projection 12 12 := pick [6,7,0,1,9,8,2,3,11,10,4,5] rfl (by decide +kernel) (by decide)
def map1047_9 : Projection 12 12 := pick [4,5,8,9,10,11,1,0,3,2,7,6] rfl (by decide +kernel) (by decide)
def map1047_18 : Projection 12 12 := pick [7,6,9,8,0,1,11,10,2,3,4,5] rfl (by decide +kernel) (by decide)
def t43 := 0xc
def v49 := [t43,t16,t17,t18,t19]
def map1047_2 : Projection 12 12 := pick [2,3,0,1,5,4,6,7,10,11,8,9] rfl (by decide +kernel) (by decide)
def v50 := [t16,t17,t18,t27,t19]
def v51 := [t28,t16,t17,t18,t19]
def map1047_1 : Projection 12 12 := pick [0,1,6,7,8,9,2,3,4,5,11,10] rfl (by decide +kernel) (by decide)
def t44 := 0x428c30
def v52 := [t16,t17,t44,t18,t19]
def map1047_15 : Projection 12 12 := pick [5,4,10,11,8,9,3,2,1,0,7,6] rfl (by decide +kernel) (by decide)
def map1047_20 : Projection 12 12 := pick [9,8,7,6,1,0,11,10,4,5,2,3] rfl (by decide +kernel) (by decide)
def t45 := 0xc0
def v53 := [t45,t16,t17,t18,t19]
def v54 := [t16,t17,t18,t19,t29]
def t46 := 0xa80f00
def v55 := [t16,t17,t18,t46,t19]
def map1047_21 : Projection 12 12 := pick [9,8,11,10,4,5,7,6,1,0,3,2] rfl (by decide +kernel) (by decide)
def t47 := 0x30
def v56 := [t47,t16,t17,t18,t19]
def map1047_8 : Projection 12 12 := pick [4,5,1,0,3,2,8,9,10,11,6,7] rfl (by decide +kernel) (by decide)
def map1047_12 : Projection 12 12 := pick [3,2,5,4,0,1,10,11,6,7,8,9] rfl (by decide +kernel) (by decide)
def v57 := [t16,t17,t18,t31,t19]
def v58 := [t16,t32,t17,t18,t19]
def t48 := 0x428c0c
def v59 := [t16,t17,t48,t18,t19]
def map1047_13 : Projection 12 12 := pick [3,2,10,11,6,7,5,4,0,1,9,8] rfl (by decide +kernel) (by decide)
def map1047_10 : Projection 12 12 := pick [8,9,1,0,7,6,4,5,11,10,2,3] rfl (by decide +kernel) (by decide)
def t49 := 0x300
def v60 := [t49,t16,t17,t18,t19]
def v61 := [t16,t17,t18,t19,t33]
def v62 := [t16,t34,t17,t18,t19]
def t50 := 0xa80cc0
def v63 := [t16,t17,t18,t50,t19]
def map1047_19 : Projection 12 12 := pick [7,6,11,10,2,3,9,8,0,1,5,4] rfl (by decide +kernel) (by decide)
def map1047_11 : Projection 12 12 := pick [8,9,4,5,11,10,1,0,7,6,3,2] rfl (by decide +kernel) (by decide)
def t51 := 0xc00
def v64 := [t51,t16,t17,t18,t19]
def map1047_16 : Projection 12 12 := pick [10,11,3,2,7,6,5,4,9,8,0,1] rfl (by decide +kernel) (by decide)
def t52 := 0xea8ffc
def v65 := [t16,t17,t18,t19,t52]
def t53 := 0x42803c
def v66 := [t16,t17,t53,t18,t19]
def t54 := 0xa803c0
def v67 := [t16,t17,t18,t54,t19]
def t55 := 0xffffff
def v68 := [t16,t17,t18,t19,t55]
def v69 := [t20,t16,t17,t18,t19,t55]
def t56 := 0xfff
def v70 := [t21,t22,t23,t56]
def v71 := [t16,t17,t24,t18,t19,t55]
def v72 := [t25,t16,t17,t18,t19,t55]
def v73 := [t16,t26,t17,t18,t19,t55]
def v74 := [t43,t16,t17,t18,t19,t55]
def v75 := [t16,t17,t18,t27,t19,t55]
def v76 := [t28,t16,t17,t18,t19,t55]
def v77 := [t16,t17,t44,t18,t19,t55]
def v78 := [t45,t16,t17,t18,t19,t55]
def v79 := [t16,t17,t18,t19,t29,t55]
def v80 := [t30,t16,t17,t18,t19,t55]
def v81 := [t16,t17,t18,t46,t19,t55]
def t57 := 0xfbaf30
def v82 := [t17,t18,t19,t57]
def t58 := 0x57f03f
def v83 := [t16,t17,t18,t58]
def v84 := [t20,t16,t17,t18,t58]
def v85 := [t16,t17,t24,t18,t58]
def v86 := [t25,t16,t17,t18,t58]
def v87 := [t16,t26,t17,t18,t58]
def v88 := [t43,t16,t17,t18,t58]
def v89 := [t16,t17,t18,t27,t58]
def v90 := [t28,t16,t17,t18,t58]
def v91 := [t16,t17,t44,t18,t58]
def v92 := [t30,t16,t17,t18,t58]
def t59 := 0x57f0ff
def v93 := [t16,t17,t18,t58,t59]
def v94 := [t45,t16,t17,t18,t58]
def t60 := 0x53a030
def v95 := [t16,t17,t18,t60,t58]
def v96 := [t47,t16,t17,t18,t58]
def v97 := [t16,t17,t18,t31,t58]
def v98 := [t16,t32,t17,t18,t58]
def v99 := [t16,t17,t48,t18,t58]
def v100 := [t16,t34,t17,t18,t58]
def t61 := 0x57f33f
def v101 := [t16,t17,t18,t58,t61]
def v102 := [t49,t16,t17,t18,t58]
def t62 := 0x46d00c
def v103 := [t16,t17,t18,t62,t58]
def v104 := [t16,t17,t53,t18,t58]
def t63 := 0x57fc3f
def v105 := [t16,t17,t18,t58,t63]
def v106 := [t51,t16,t17,t18,t58]
def t64 := 0x157003
def v107 := [t16,t17,t64,t18,t58]
def v108 := [t16,t17,t18,t19,t57]
def v109 := [t16,t17,t18,t58,t19]
def v110 := [t16,t17,t18,t59,t19]
def v111 := [t16,t17,t18,t60,t19]
def v112 := [t16,t17,t18,t58,t29]
def v113 := [t16,t17,t18,t58,t46]
def v114 := [t16,t17,t18,t61,t19]
def v115 := [t16,t17,t18,t62,t19]
def v116 := [t16,t17,t18,t58,t33]
def v117 := [t16,t17,t18,t58,t50]
def v118 := [t16,t17,t18,t63,t19]
def v119 := [t16,t17,t64,t18,t19]
def v120 := [t16,t17,t18,t58,t52]
def v121 := [t16,t17,t18,t58,t54]
def v122 := [t16,t17,t18,t58,t55]
def v123 := [t17,t18,t19,t57,t55]
def v124 := [t16,t17,t18,t19,t57,t55]
def v125 := [t47,t16,t17,t18,t19,t55]
def v126 := [t16,t17,t18,t31,t19,t55]
def v127 := [t16,t32,t17,t18,t19,t55]
def v128 := [t16,t17,t48,t18,t19,t55]
def v129 := [t49,t16,t17,t18,t19,t55]
def v130 := [t16,t17,t18,t19,t33,t55]
def v131 := [t16,t34,t17,t18,t19,t55]
def v132 := [t16,t17,t18,t50,t19,t55]
def t65 := 0xeedccc
def v133 := [t16,t18,t19,t65]
def v134 := [t16,t17,t18,t19,t65]
def v135 := [t16,t18,t19,t65,t55]
def v136 := [t16,t17,t18,t19,t65,t55]
def v137 := [t51,t16,t17,t18,t19,t55]
def v138 := [t16,t17,t18,t19,t52,t55]
def v139 := [t16,t17,t53,t18,t19,t55]
def v140 := [t16,t17,t18,t54,t19,t55]
def t66 := 0xbd73c3
def v141 := [t16,t17,t19,t66]
def v142 := [t16,t17,t18,t19,t66]
def v143 := [t16,t17,t19,t66,t55]
def v144 := [t16,t17,t18,t19,t66,t55]
def v145 := [t16,t17,t18,t58,t19,t55]
def p31_1047 : Projection 26 12 := pick [1,2,4,5,7,8,14,16,17,19,21,23] rfl (by decide +kernel) (by decide)
def map31_2 : Projection 26 26 := pick [3,4,5,0,1,2,6,8,7,9,10,12,11,13,14,15,16,21,22,23,24,17,18,19,20,25] rfl (by decide +kernel) (by decide)
def v146 := [t0,t6,t1,t14,t2,t3,t4]
def t67 := 0x4005820003c00
def v147 := [t0,t67,t1,t2,t3,t4]
def v148 := [t0,t67,t6,t1,t2,t3,t4]
def t68 := 0x2ad06daffc1c7
def v149 := [t68,t0,t1,t2,t3,t4]
def v150 := [t68,t0,t6,t1,t2,t3,t4]
def t69 := 0x4004001003c00
def v151 := [t0,t69,t1,t2,t3,t4]
def v152 := [t0,t69,t6,t1,t2,t3,t4]
def t70 := 0xf76f823fffe38
def v153 := [t0,t1,t2,t3,t4,t70]
def v154 := [t0,t6,t1,t2,t3,t4,t70]
def t71 := 0x1820000238
def v155 := [t71,t0,t1,t2,t3,t4]
def v156 := [t71,t0,t6,t1,t2,t3,t4]
def t72 := 0xb76a002ffc000
def v157 := [t0,t1,t2,t72,t3,t4]
def v158 := [t0,t6,t1,t2,t72,t3,t4]
def v159 := [t5,t0,t6,t1,t2,t3,t4]
def t73 := 0xc5bfb7f1fffff
def v160 := [t0,t6,t1,t2,t73,t3,t4]
def t74 := 0x403406901c038
def v161 := [t0,t6,t74,t1,t2,t3,t4]
def t75 := 0x81883120e01c0
def v162 := [t0,t6,t1,t75,t2,t3,t4]
def t76 := 0xdc3fdeff1ffff
def v163 := [t0,t6,t2,t76,t4]
def v164 := [t8,t0,t6,t2,t76,t4]
def v165 := [t0,t6,t2,t9,t76,t4]
def v166 := [t0,t10,t6,t2,t76,t4]
def v167 := [t0,t6,t11,t2,t76,t4]
def t77 := 0x9c3a5cef1c1c7
def v168 := [t0,t2,t77,t4]
def v169 := [t0,t6,t2,t77,t4]
def v170 := [t0,t2,t77,t76,t4]
def v171 := [t0,t6,t2,t77,t76,t4]
def v172 := [t13,t0,t6,t2,t76,t4]
def v173 := [t0,t6,t14,t2,t76,t4]
def v174 := [t0,t67,t6,t2,t76,t4]
def v175 := [t68,t0,t6,t2,t76,t4]
def v176 := [t0,t69,t6,t2,t76,t4]
def v177 := [t0,t6,t2,t76,t4,t70]
def v178 := [t71,t0,t6,t2,t76,t4]
def v179 := [t0,t6,t2,t72,t76,t4]
def t78 := 0x840b906103fc7
def v180 := [t0,t6,t78,t2,t76,t4]
def t79 := 0xddbffffffffff
def v181 := [t0,t6,t2,t76,t79,t4]
def t80 := 0x1802100e0000
def v182 := [t80,t0,t6,t2,t76,t4]
def t81 := 0x58344e9e1c038
def v183 := [t0,t6,t81,t2,t76,t4]
def t82 := 0x802121e03c7
def v184 := [t82,t0,t6,t2,t76,t4]
def t83 := 0xafdbfdfffffff
def v185 := [t0,t6,t2,t83,t76,t4]
def t84 := 0x850b904003c00
def v186 := [t0,t6,t84,t2,t76,t4]
def t85 := 0x2a504c9e1c038
def v187 := [t85,t0,t6,t2,t76,t4]
def t86 := 0x850a0021e3c00
def v188 := [t0,t6,t86,t2,t76,t4]
def t87 := 0xf7efb17ffffc7
def v189 := [t0,t6,t2,t76,t4,t87]
def t88 := 0x81b140003c7
def v190 := [t88,t0,t6,t2,t76,t4]
def t89 := 0x7264001e1c000
def v191 := [t0,t6,t89,t2,t76,t4]
def t90 := 0x8104cbf1c3ff
def v192 := [t90,t0,t6,t2,t4]
def v193 := [t90,t0,t6,t2,t76,t4]
def t91 := 0xfefffffffffff
def v194 := [t0,t6,t2,t76,t4,t91]
def t92 := 0xd42f924003c00
def v195 := [t0,t6,t2,t92,t76,t4]
def t93 := 0x22c02100e0000
def v196 := [t93,t0,t6,t2,t4]
def v197 := [t93,t0,t6,t2,t76,t4]
def t94 := 0xd42e003f1fc00
def v198 := [t0,t6,t2,t94,t76,t4]
def t95 := 0xff7fdefffffff
def v199 := [t0,t6,t2,t76,t4,t95]
def t96 := 0x811dec0003ff
def v200 := [t96,t0,t6,t2,t76,t4]
def t97 := 0x23400000e0000
def v201 := [t97,t0,t6,t2,t76,t4]
def t98 := 0x2240003ffc000
def v202 := [t98,t0,t6,t2,t76,t4]
def t99 := 0xfffe6dbffffff
def v203 := [t0,t6,t2,t76,t4,t99]
def t100 := 0x8906d80003ff
def v204 := [t100,t0,t6,t2,t76,t4]
def t101 := 0xd52e000003c00
def v205 := [t0,t6,t2,t101,t76,t4]
def v206 := [t0,t6,t1,t2,t76,t4]
def t102 := 0x6dbff
def t103 := 0x86e3f
def t104 := 0xb17c7
def t105 := 0xda3f8
def v207 := [t102,t103,t104,t105]
def p31_30 : Projection 26 10 := pick [6,7,8,18,17,19,22,21,23,25] rfl (by decide +kernel) (by decide)
def v208 := [t0,t6,t2,t3,t76,t4]
def map31_14 : Projection 26 26 := pick [6,8,7,3,5,4,0,2,1,9,10,13,12,11,21,22,23,17,18,19,25,14,15,16,24,20] rfl (by decide +kernel) (by decide)
def v209 := [t0,t6,t1,t2,t3,t76,t4]
def t106 := 0x1004911c23f
def v210 := [t106,t0,t6,t2,t3,t4]
def v211 := [t106,t0,t6,t1,t2,t3,t4]
def t107 := 0x6ef7effffffff
def v212 := [t0,t6,t1,t107,t2,t3,t4]
def t108 := 0x4427824003c00
def v213 := [t0,t6,t108,t1,t2,t3,t4]
def t109 := 0x2ac0692ee01c0
def v214 := [t109,t0,t6,t2,t3,t4]
def v215 := [t109,t0,t6,t1,t2,t3,t4]
def t110 := 0x442600111fc00
def v216 := [t0,t6,t110,t1,t2,t3,t4]
def t111 := 0xf77f86ffffe3f
def v217 := [t0,t6,t1,t2,t3,t4,t111]
def t112 := 0x1186c00023f
def v218 := [t112,t0,t6,t1,t2,t3,t4]
def t113 := 0xb348002ee0000
def v219 := [t0,t6,t1,t2,t113,t3,t4]
def t114 := 0x8009902003fc0
def v220 := [t0,t6,t1,t114,t2,t3,t4]
def t115 := 0xdd8ffb7fe3fff
def v221 := [t0,t6,t1,t2,t3,t115,t4]
def t116 := 0x5822141e0007
def v222 := [t116,t0,t6,t1,t2,t3,t4]
def t117 := 0x58044a1e00038
def v223 := [t0,t6,t1,t117,t2,t3,t4]
def v224 := [t82,t0,t6,t1,t2,t3,t4]
def v225 := [t0,t6,t1,t2,t83,t3,t4]
def v226 := [t0,t6,t1,t84,t2,t3,t4]
def v227 := [t85,t0,t6,t1,t2,t3,t4]
def v228 := [t0,t6,t1,t86,t2,t3,t4]
def v229 := [t0,t6,t1,t2,t3,t4,t87]
def v230 := [t88,t0,t6,t1,t2,t3,t4]
def v231 := [t0,t6,t1,t89,t2,t3,t4]
def t118 := 0x800483e003f8
def v232 := [t118,t0,t6,t1,t2,t4]
def v233 := [t118,t0,t6,t1,t2,t3,t4]
def t119 := 0xfaddffbffffff
def v234 := [t0,t6,t1,t2,t3,t4,t119]
def t120 := 0xd00d920003c00
def v235 := [t0,t6,t1,t2,t120,t3,t4]
def t121 := 0x22d02581fc007
def v236 := [t121,t0,t6,t1,t2,t4]
def v237 := [t121,t0,t6,t1,t2,t3,t4]
def t122 := 0xd00c003e03c00
def v238 := [t0,t6,t1,t2,t122,t3,t4]
def t123 := 0xff6fda3fffff8
def v239 := [t0,t6,t1,t2,t3,t4,t123]
def t124 := 0x801da00003f8
def v240 := [t124,t0,t6,t1,t2,t3,t4]
def t125 := 0x27620001fc000
def v241 := [t125,t0,t6,t1,t2,t3,t4]
def v242 := [t98,t0,t6,t1,t2,t3,t4]
def v243 := [t0,t6,t1,t2,t3,t4,t99]
def v244 := [t100,t0,t6,t1,t2,t3,t4]
def v245 := [t0,t6,t1,t2,t101,t3,t4]
def v246 := [t0,t1,t2,t73,t3,t4]
def v247 := [t5,t0,t73,t3,t4]
def v248 := [t5,t0,t1,t73,t3,t4]
def v249 := [t5,t0,t2,t73,t3,t4]
def map31_8 : Projection 26 26 := pick [6,7,8,0,2,1,3,5,4,9,10,13,11,12,17,18,19,21,22,23,25,14,15,16,20,24] rfl (by decide +kernel) (by decide)
def map31_12 : Projection 26 26 := pick [3,5,4,6,8,7,0,1,2,9,10,12,13,11,21,22,23,14,15,16,24,17,18,19,25,20] rfl (by decide +kernel) (by decide)
def v250 := [t5,t0,t1,t2,t73,t3,t4]
def v251 := [t0,t74,t1,t73,t3,t4]
def v252 := [t0,t74,t1,t2,t73,t3,t4]
def v253 := [t0,t75,t2,t73,t3,t4]
def v254 := [t0,t1,t75,t2,t73,t3,t4]
def v255 := [t0,t1,t75,t2,t3,t4]
def v256 := [t0,t1,t2,t73,t3,t76,t4]
def v257 := [t7,t0,t1,t2,t73,t3,t4]
def v258 := [t0,t1,t2,t12,t73,t3,t4]
def v259 := [t106,t0,t1,t2,t73,t3,t4]
def v260 := [t0,t1,t107,t2,t73,t3,t4]
def v261 := [t0,t108,t1,t2,t73,t3,t4]
def v262 := [t109,t0,t1,t2,t73,t3,t4]
def v263 := [t0,t110,t1,t2,t73,t3,t4]
def v264 := [t0,t1,t2,t73,t3,t4,t111]
def v265 := [t112,t0,t1,t2,t73,t3,t4]
def v266 := [t0,t1,t2,t113,t73,t3,t4]
def v267 := [t0,t74,t1,t2,t3,t4]
def v268 := [t0,t1,t114,t2,t73,t3,t4]
def v269 := [t0,t1,t2,t73,t3,t115,t4]
def v270 := [t116,t0,t1,t2,t73,t3,t4]
def v271 := [t0,t1,t117,t2,t73,t3,t4]
def v272 := [t82,t0,t1,t2,t73,t3,t4]
def v273 := [t0,t1,t2,t83,t73,t3,t4]
def v274 := [t0,t1,t84,t2,t73,t3,t4]
def v275 := [t85,t0,t1,t2,t73,t3,t4]
def v276 := [t0,t1,t86,t2,t73,t3,t4]
def v277 := [t0,t1,t2,t73,t3,t4,t87]
def v278 := [t88,t0,t1,t2,t73,t3,t4]
def v279 := [t0,t1,t89,t2,t73,t3,t4]
def t126 := 0xc00d923003ff8
def v280 := [t0,t1,t2,t126,t3,t4]
def v281 := [t0,t1,t2,t126,t73,t3,t4]
def v282 := [t0,t1,t2,t3,t79,t4]
def v283 := [t0,t1,t2,t73,t3,t79,t4]
def t127 := 0x5b225c1fc007
def v284 := [t127,t0,t1,t2,t3,t4]
def v285 := [t127,t0,t1,t2,t73,t3,t4]
def t128 := 0x1800480e00000
def v286 := [t128,t0,t1,t2,t3,t4]
def v287 := [t128,t0,t1,t2,t73,t3,t4]
def t129 := 0x9025b1fc3ff
def v288 := [t129,t0,t1,t2,t3,t4]
def v289 := [t106,t0,t1,t2,t3,t4]
def t130 := 0x44b7a7f1fffff
def v290 := [t0,t1,t130,t2,t3,t4]
def t131 := 0x802120e01c0
def v291 := [t131,t0,t1,t2,t3,t4]
def v292 := [t0,t108,t1,t2,t3,t4]
def v293 := [t82,t0,t1,t2,t3,t4]
def t132 := 0x859bb5f1fffff
def v294 := [t0,t1,t2,t132,t3,t4]
def t133 := 0x1004901c038
def v295 := [t133,t0,t1,t2,t3,t4]
def v296 := [t0,t1,t84,t2,t3,t4]
def t134 := 0x30003f8
def v297 := [t134,t0,t1,t2,t3,t4]
def t135 := 0xd89dffbffffff
def v298 := [t0,t1,t2,t3,t135,t4]
def t136 := 0x902581fc007
def v299 := [t136,t0,t1,t2,t3,t4]
def t137 := 0xd80dda0e03c00
def v300 := [t0,t1,t2,t137,t3,t4]
def t138 := 0x2a40480e00000
def v301 := [t129,t138,t1,t2,t3,t4]
def v302 := [t138,t0,t1,t2,t3,t4]
def t139 := 0x31fc000
def v303 := [t139,t0,t1,t2,t3,t4]
def t140 := 0xf7fe25bffffff
def v304 := [t0,t1,t2,t3,t4,t140]
def t141 := 0x902580003ff
def v305 := [t141,t0,t1,t2,t3,t4]
def t142 := 0xf76e000e03c00
def v306 := [t0,t1,t2,t3,t142,t4]
def v307 := [t129,t5,t0,t3,t4]
def v308 := [t129,t5,t0,t1,t3,t4]
def v309 := [t129,t5,t0,t2,t3,t4]
def v310 := [t129,t0,t74,t1,t3,t4]
def v311 := [t129,t0,t75,t2,t3,t4]
def v312 := [t129,t1,t107,t2,t3,t4]
def v313 := [t129,t109,t1,t2,t3,t4]
def v314 := [t129,t1,t2,t83,t3,t4]
def v315 := [t129,t85,t1,t2,t3,t4]
def v316 := [t129,t118,t1,t2,t3,t4]
def v317 := [t129,t1,t2,t120,t3,t4]
def v318 := [t129,t98,t1,t2,t3,t4]
def v319 := [t129,t1,t2,t101,t3,t4]
def v320 := [t129,t0,t1,t2,t73,t3,t4]
def t143 := 0xeffffffffffff
def v321 := [t0,t1,t2,t3,t143,t4]
def v322 := [t0,t1,t2,t73,t3,t143,t4]
def t144 := 0xc52f924003c00
def v323 := [t0,t1,t2,t144,t3,t4]
def v324 := [t0,t1,t2,t144,t73,t3,t4]
def v325 := [t138,t0,t1,t2,t73,t3,t4]
def t145 := 0xc52e0031ffc00
def v326 := [t0,t1,t2,t145,t3,t4]
def v327 := [t0,t1,t2,t145,t73,t3,t4]
def t146 := 0xf7ffb7fffffff
def v328 := [t0,t1,t2,t3,t4,t146]
def v329 := [t0,t1,t2,t73,t3,t4,t146]
def t147 := 0x91b7c0003ff
def v330 := [t147,t0,t1,t2,t3,t4]
def v331 := [t147,t0,t1,t2,t73,t3,t4]
def t148 := 0x3240000e00000
def v332 := [t0,t148,t1,t2,t3,t4]
def v333 := [t0,t148,t1,t2,t73,t3,t4]
def v334 := [t118,t0,t1,t2,t73,t3,t4]
def v335 := [t0,t1,t2,t73,t3,t4,t119]
def v336 := [t0,t1,t2,t73,t120,t3,t4]
def v337 := [t121,t0,t1,t2,t73,t3,t4]
def v338 := [t0,t1,t2,t73,t122,t3,t4]
def v339 := [t0,t1,t2,t73,t3,t4,t123]
def v340 := [t124,t0,t1,t2,t73,t3,t4]
def v341 := [t125,t0,t1,t2,t73,t3,t4]
def v342 := [t98,t0,t1,t2,t73,t3,t4]
def v343 := [t0,t1,t2,t73,t3,t4,t99]
def v344 := [t100,t0,t1,t2,t73,t3,t4]
def v345 := [t0,t1,t2,t73,t101,t3,t4]
def v346 := [t112,t0,t1,t2,t3,t4]
def v347 := [t112,t0,t110,t2,t3,t4]
def v348 := [t0,t110,t1,t2,t3,t4]
def v349 := [t112,t0,t110,t1,t2,t3,t4]
def t149 := 0x1804000207
def v350 := [t149,t0,t1,t2,t3,t4]
def v351 := [t149,t112,t0,t1,t2,t3,t4]
def t150 := 0x859bb7e1e3fff
def v352 := [t0,t1,t2,t150,t3,t4]
def v353 := [t112,t0,t1,t2,t150,t3,t4]
def t151 := 0x10068000038
def v354 := [t151,t0,t1,t2,t3,t4]
def v355 := [t151,t112,t0,t1,t2,t3,t4]
def t152 := 0x858a3121e3dc0
def v356 := [t0,t1,t152,t2,t3,t4]
def v357 := [t112,t0,t1,t152,t2,t3,t4]
def v358 := [t71,t112,t0,t1,t2,t3,t4]
def t153 := 0xd81ddefe03fff
def v359 := [t0,t1,t2,t3,t153,t4]
def v360 := [t112,t0,t1,t2,t3,t153,t4]
def t154 := 0x1004c000007
def v361 := [t154,t0,t1,t2,t3,t4]
def v362 := [t154,t112,t0,t1,t2,t3,t4]
def t155 := 0xd80c583e03dc0
def v363 := [t0,t1,t2,t155,t3,t4]
def v364 := [t112,t0,t1,t2,t155,t3,t4]
def t156 := 0x1004800023f
def v365 := [t156,t0,t1,t2,t3,t4]
def v366 := [t156,t112,t0,t1,t2,t3,t4]
def t157 := 0x2ad1effffc3ff
def v367 := [t0,t157,t1,t2,t3,t4]
def v368 := [t112,t0,t157,t1,t2,t3,t4]
def t158 := 0x1824000000
def v369 := [t158,t0,t1,t2,t3,t4]
def v370 := [t158,t112,t0,t1,t2,t3,t4]
def t159 := 0x2ac0693ffc1c0
def v371 := [t159,t0,t1,t2,t3,t4]
def v372 := [t112,t159,t0,t1,t2,t3,t4]
def v373 := [t112,t0,t1,t2,t3,t111]
def v374 := [t0,t1,t2,t3,t4,t111]
def v375 := [t112,t0,t1,t2,t3,t4,t111]
def v376 := [t112,t5,t0,t1,t2,t3,t4]
def v377 := [t112,t0,t74,t1,t2,t3,t4]
def v378 := [t112,t0,t1,t75,t2,t3,t4]
def v379 := [t112,t0,t1,t2,t3,t76,t4]
def v380 := [t112,t7,t0,t1,t2,t3,t4]
def v381 := [t112,t0,t1,t2,t12,t3,t4]
def v382 := [t106,t112,t0,t1,t2,t3,t4]
def v383 := [t112,t0,t1,t107,t2,t3,t4]
def v384 := [t112,t0,t108,t1,t2,t3,t4]
def v385 := [t112,t109,t0,t1,t2,t3,t4]
def v386 := [t112,t0,t2,t113,t3]
def t160 := 0x4c07
def t161 := 0x581c0
def v387 := [t160,t161,t102,t104]
def t162 := 0x407
def v388 := [t162,t160,t161,t102,t104]
def t163 := 0xb5fc7
def v389 := [t160,t161,t102,t104,t163]
def t164 := 0x4800
def v390 := [t164,t160,t161,t102,t104]
def t165 := 0xb13c0
def v391 := [t160,t161,t102,t165,t104]
def t166 := 0x5cdc7
def v392 := [t166,t102,t104]
def t167 := 0x6b43f
def v393 := [t167,t102,t103]
def t168 := 0x243f
def v394 := [t168,t167,t102]
def v395 := [t168,t167,t102,t103]
def t169 := 0xefe3f
def v396 := [t167,t102,t103,t169]
def t170 := 0x84a00
def v397 := [t167,t102,t170,t103]
def t171 := 0x69000
def v398 := [t171,t167,t102]
def v399 := [t171,t167,t102,t103]
def t172 := 0x4a3f
def v400 := [t172,t167,t102]
def v401 := [t172,t167,t102,t103]
def t173 := 0xeffff
def v402 := [t167,t102,t103,t173]
def t174 := 0x82400
def v403 := [t167,t102,t174,t103]
def t175 := 0x691c0
def v404 := [t175,t167,t102]
def v405 := [t175,t167,t102,t103]
def t176 := 0x6903f
def v406 := [t176,t102,t103]
def v407 := [t176,t167,t102,t103]
def t177 := 0x6ffff
def v408 := [t167,t102,t177,t103]
def t178 := 0x2400
def v409 := [t178,t167,t102,t103]
def t179 := 0x4bc0
def v410 := [t179,t102,t103]
def v411 := [t179,t167,t102,t103]
def map15_2 : Projection 10 10 := pick [0,2,1,6,7,8,3,4,5,9] rfl (by decide +kernel) (by decide)
def v412 := [t160,t166,t102,t104]
def v413 := [t161,t166,t102,t104]
def v414 := [t160,t161,t166,t102,t104]
def t180 := 0x4807
def v415 := [t180,t161,t102,t104]
def v416 := [t180,t160,t161,t102,t104]
def t181 := 0x6dfff
def v417 := [t160,t161,t102,t181,t104]
def t182 := 0x400
def v418 := [t182,t160,t161,t102,t104]
def t183 := 0x693f8
def v419 := [t161,t183,t102,t104]
def v420 := [t160,t161,t183,t102,t104]
def t184 := 0x101c0
def v421 := [t160,t184,t161,t102,t104]
def t185 := 0xf97c7
def v422 := [t160,t161,t102,t104,t185]
def t186 := 0xa1607
def v423 := [t160,t161,t102,t186,t104]
def t187 := 0x48000
def v424 := [t160,t187,t161,t102,t104]
def t188 := 0x213c7
def v425 := [t160,t188,t161,t102]
def t189 := 0x21407
def t190 := 0x4a038
def v426 := [t172,t189,t190,t102]
def v427 := [t172,t189,t190,t175]
def v428 := [t189,t190,t175,t102]
def v429 := [t172,t189,t167,t102]
def v430 := [t172,t190,t167,t102]
def t191 := 0x21007
def v431 := [t172,t191,t190,t102]
def v432 := [t172,t189,t190,t181]
def t192 := 0x4cbf8
def v433 := [t172,t190,t192]
def v434 := [t172,t189,t190,t192]
def v435 := [t172,t190,t192,t102]
def t193 := 0x48038
def v436 := [t172,t189,t193,t102]
def t194 := 0x6fbff
def v437 := [t172,t189,t190,t194]
def t195 := 0x25bc7
def v438 := [t172,t189,t195]
def v439 := [t172,t189,t195,t190]
def v440 := [t172,t189,t195,t102]
def v441 := [t160,t188,t161,t102,t104]
def t196 := 0xfdfff
def v442 := [t160,t161,t102,t104,t196]
def t197 := 0x90400
def v443 := [t160,t161,t102,t197,t104]
def t198 := 0x4c838
def v444 := [t160,t198,t161,t102]
def v445 := [t160,t198,t161,t102,t104]
def t199 := 0x481c0
def v446 := [t160,t199,t102,t104]
def v447 := [t160,t199,t161,t102,t104]
def t200 := 0x7dbff
def v448 := [t160,t161,t102,t200,t104]
def t201 := 0x10000
def v449 := [t160,t201,t161,t102,t104]
def t202 := 0x25a3f
def v450 := [t160,t202,t102,t104]
def v451 := [t160,t202,t161,t102,t104]
def p31_27 : Projection 26 10 := pick [0,1,2,15,14,16,18,17,19,20] rfl (by decide +kernel) (by decide)
def v452 := [t112,t0,t1,t2,t113,t3]
def v453 := [t112,t0,t2,t113,t3,t4]
def v454 := [t112,t0,t1,t2,t113,t3,t4]
def v455 := [t112,t0,t1,t114,t2,t3,t4]
def v456 := [t112,t0,t1,t2,t3,t115,t4]
def v457 := [t112,t116,t0,t1,t2,t3,t4]
def v458 := [t112,t0,t1,t117,t2,t3,t4]
def v459 := [t112,t82,t0,t1,t2,t3,t4]
def v460 := [t112,t0,t1,t2,t83,t3,t4]
def v461 := [t112,t0,t1,t84,t2,t3,t4]
def v462 := [t112,t85,t0,t1,t2,t3,t4]
def v463 := [t112,t0,t1,t86,t2,t3,t4]
def v464 := [t112,t0,t1,t2,t3,t4,t87]
def v465 := [t112,t88,t0,t1,t2,t3,t4]
def v466 := [t112,t0,t1,t89,t2,t3,t4]
def v467 := [t112,t118,t0,t1,t2,t3,t4]
def v468 := [t112,t0,t1,t2,t3,t4,t119]
def v469 := [t112,t0,t1,t2,t120,t3,t4]
def v470 := [t112,t121,t0,t1,t2,t3,t4]
def v471 := [t112,t0,t1,t2,t122,t3,t4]
def v472 := [t112,t0,t1,t2,t3,t4,t123]
def v473 := [t112,t124,t0,t1,t2,t3,t4]
def v474 := [t112,t125,t0,t1,t2,t3,t4]
def v475 := [t112,t98,t0,t1,t2,t3]
def v476 := [t112,t98,t0,t1,t2,t3,t4]
def v477 := [t112,t0,t1,t2,t3,t4,t99]
def v478 := [t112,t100,t0,t1,t2,t3]
def v479 := [t112,t100,t0,t1,t2,t3,t4]
def v480 := [t112,t0,t1,t2,t101,t3,t4]
def map31_3 : Projection 26 26 := pick [3,4,5,15,14,16,22,21,23,24,12,10,11,13,1,0,2,8,6,7,9,19,18,17,20,25] rfl (by decide +kernel) (by decide)
def map31_4 : Projection 26 26 := pick [15,14,16,0,1,2,18,19,17,20,11,12,10,13,4,3,5,23,22,21,24,7,6,8,9,25] rfl (by decide +kernel) (by decide)
def map31_9 : Projection 26 26 := pick [6,7,8,18,17,19,22,21,23,25,13,10,11,12,2,0,1,5,3,4,9,16,15,14,20,24] rfl (by decide +kernel) (by decide)
def map31_18 : Projection 26 26 := pick [15,16,14,18,19,17,0,1,2,20,11,12,13,10,23,22,21,4,3,5,24,7,6,8,25,9] rfl (by decide +kernel) (by decide)
def v481 := [t0,t1,t2,t3,t76,t4]
def map31_1 : Projection 26 26 := pick [0,1,2,15,14,16,18,17,19,20,11,10,12,13,4,3,5,7,6,8,9,23,22,21,24,25] rfl (by decide +kernel) (by decide)
def map31_15 : Projection 26 26 := pick [6,8,7,22,21,23,18,17,19,25,13,10,12,11,5,3,4,2,0,1,9,16,15,14,24,20] rfl (by decide +kernel) (by decide)
def map31_20 : Projection 26 26 := pick [18,19,17,15,16,14,0,2,1,20,11,13,12,10,23,22,21,7,6,8,25,4,3,5,24,9] rfl (by decide +kernel) (by decide)
def t203 := 0x100207
def v482 := [t203,t0,t1,t2,t3,t4]
def v483 := [t203,t82,t0,t1,t2,t3,t4]
def v484 := [t131,t0,t130,t2,t3,t4]
def v485 := [t5,t0,t130,t3,t4]
def v486 := [t5,t0,t1,t130,t3,t4]
def v487 := [t5,t0,t130,t2,t3,t4]
def v488 := [t0,t74,t1,t130,t3,t4]
def v489 := [t0,t130,t75,t2,t3,t4]
def v490 := [t0,t130,t2,t3,t76,t4]
def v491 := [t7,t0,t130,t2,t3,t4]
def v492 := [t106,t0,t130,t2,t3,t4]
def v493 := [t109,t0,t130,t2,t3,t4]
def v494 := [t0,t130,t2,t3,t4,t111]
def v495 := [t112,t0,t130,t2,t3,t4]
def t204 := 0x483a161e3fc7
def v496 := [t204,t0,t1,t3,t4]
def v497 := [t204,t0,t1,t130,t3,t4]
def v498 := [t204,t0,t1,t2,t3,t4]
def t205 := 0x8108100000000
def v499 := [t0,t1,t205,t2,t3,t4]
def t206 := 0x4005823003ff8
def v500 := [t0,t206,t1,t2,t3,t4]
def t207 := 0xdcbffffffffff
def v501 := [t0,t1,t2,t3,t207,t4]
def t208 := 0x4b225c1fc007
def v502 := [t208,t0,t1,t2,t3,t4]
def t209 := 0x9808580e00000
def v503 := [t0,t1,t2,t209,t3,t4]
def v504 := [t0,t1,t107,t2,t3,t4]
def t210 := 0x44260031ffc00
def v505 := [t0,t210,t1,t2,t3,t4]
def t211 := 0xf7ffa7fffffff
def v506 := [t0,t1,t2,t3,t4,t211]
def t212 := 0x91a7c0003ff
def v507 := [t212,t0,t1,t2,t3,t4]
def t213 := 0xb348000e00000
def v508 := [t0,t1,t2,t213,t3,t4]
def v509 := [t82,t0,t1,t130,t2,t3,t4]
def v510 := [t131,t82,t0,t1,t2,t3,t4]
def t214 := 0x443786d01fc38
def v511 := [t0,t214,t1,t2,t3,t4]
def v512 := [t82,t0,t214,t1,t2,t3,t4]
def v513 := [t82,t0,t1,t84,t3,t4]
def v514 := [t82,t0,t1,t84,t2,t3,t4]
def t215 := 0x20003c0
def v515 := [t215,t0,t1,t2,t3,t4]
def v516 := [t215,t82,t0,t1,t2,t3,t4]
def t216 := 0xd88dfb3fe3fff
def v517 := [t0,t1,t2,t3,t216,t4]
def v518 := [t82,t0,t1,t2,t3,t216,t4]
def t217 := 0x802101e0007
def v519 := [t217,t0,t1,t2,t3,t4]
def v520 := [t217,t82,t0,t1,t2,t3,t4]
def t218 := 0xd80dda1e03c38
def v521 := [t0,t1,t2,t218,t3,t4]
def v522 := [t82,t0,t1,t2,t218,t3,t4]
def v523 := [t82,t85,t1,t2,t3,t4]
def v524 := [t85,t0,t1,t2,t3,t4]
def v525 := [t121,t0,t1,t2,t3,t4]
def t219 := 0x10af1f
def t220 := 0x4714f3
def t221 := 0x8b48fc
def t222 := 0xec0fe0
def v526 := [t219,t220,t221,t222]
def t223 := 0x413
def v527 := [t223,t219,t220,t221,t222]
def t224 := 0x57bfff
def v528 := [t219,t220,t224,t221,t222]
def t225 := 0x10ab0c
def v529 := [t225,t219,t220,t221,t222]
def t226 := 0x4710e0
def v530 := [t219,t226,t220,t221,t222]
def t227 := 0x81c
def v531 := [t227,t219,t220,t221,t222]
def t228 := 0x9befff
def v532 := [t219,t220,t221,t228,t222]
def t229 := 0x10a703
def v533 := [t229,t219,t220,t221,t222]
def t230 := 0x8b40e0
def v534 := [t219,t220,t230,t221,t222]
def t231 := 0xf00
def v535 := [t231,t219,t220,t221,t222]
def t232 := 0xfcafff
def v536 := [t219,t220,t221,t222,t232]
def t233 := 0x10a01f
def v537 := [t233,t219,t220,t221,t222]
def t234 := 0xec00e0
def v538 := [t219,t220,t221,t234,t222]
def t235 := 0x300f0
def v539 := [t235,t219,t220,t221,t222]
def t236 := 0xcf5cff
def v540 := [t219,t220,t221,t236,t222]
def t237 := 0x441403
def v541 := [t219,t237,t220,t221,t222]
def t238 := 0x88480c
def v542 := [t219,t220,t238,t221,t222]
def t239 := 0x4404e0
def v543 := [t219,t239,t220,t221,t222]
def t240 := 0xef1ff3
def v544 := [t219,t220,t221,t222,t240]
def t241 := 0x31013
def v545 := [t241,t219,t220,t221,t222]
def t242 := 0xa80b00
def v546 := [t219,t220,t221,t242,t222]
def t243 := 0x8808e0
def v547 := [t219,t220,t243,t221,t222]
def t244 := 0xef4ffc
def v548 := [t219,t220,t221,t222,t244]
def t245 := 0x3401c
def v549 := [t245,t219,t220,t221,t222]
def t246 := 0x640700
def v550 := [t219,t220,t246,t221,t222]
def v551 := [t219,t220,t221,t222,t55]
def p31_539 : Projection 26 12 := pick [3,5,6,8,9,10,12,13,21,22,24,25] rfl (by decide +kernel) (by decide)
def v552 := [t82,t85,t0,t1,t2,t3,t4]
def t247 := 0x21e0000
def v553 := [t247,t0,t1,t2,t3,t4]
def v554 := [t247,t82,t0,t1,t2,t3,t4]
def t248 := 0xf7ee213ffffc7
def v555 := [t0,t1,t2,t3,t4,t248]
def v556 := [t82,t0,t1,t2,t3,t4,t248]
def t249 := 0x802100003c7
def v557 := [t249,t0,t1,t2,t3,t4]
def v558 := [t249,t82,t0,t1,t2,t3,t4]
def t250 := 0xf76e001e1fc00
def v559 := [t0,t1,t2,t3,t250,t4]
def v560 := [t82,t0,t1,t2,t3,t250,t4]
def v561 := [t82,t5,t0,t1,t3,t4]
def v562 := [t82,t5,t0,t1,t2,t3,t4]
def v563 := [t82,t0,t74,t1,t3,t4]
def v564 := [t82,t0,t74,t1,t2,t3,t4]
def v565 := [t82,t0,t1,t75,t2,t3,t4]
def v566 := [t82,t0,t1,t2,t3,t76,t4]
def v567 := [t82,t7,t0,t1,t2,t3,t4]
def v568 := [t82,t0,t1,t2,t12,t3,t4]
def v569 := [t106,t82,t0,t1,t2,t3,t4]
def v570 := [t82,t0,t1,t107,t2,t3,t4]
def v571 := [t82,t0,t108,t1,t2,t3,t4]
def v572 := [t82,t109,t0,t1,t2,t3,t4]
def v573 := [t82,t0,t110,t1,t2,t3,t4]
def v574 := [t82,t0,t1,t2,t3,t4,t111]
def v575 := [t82,t0,t1,t2,t113,t3,t4]
def v576 := [t82,t0,t1,t114,t3,t4]
def v577 := [t82,t0,t1,t114,t2,t3,t4]
def v578 := [t82,t0,t1,t2,t3,t115,t4]
def v579 := [t82,t116,t0,t1,t2,t3,t4]
def v580 := [t82,t0,t1,t117,t3,t4]
def v581 := [t82,t0,t1,t117,t2,t3,t4]
def v582 := [t82,t1,t83,t3,t4]
def v583 := [t82,t1,t2,t83,t3,t4]
def p31_29 : Projection 26 10 := pick [3,4,5,15,14,16,22,21,23,24] rfl (by decide +kernel) (by decide)
def v584 := [t82,t0,t1,t83,t3,t4]
def v585 := [t82,t0,t1,t2,t83,t3,t4]
def v586 := [t82,t0,t1,t86,t3,t4]
def v587 := [t82,t0,t1,t86,t2,t3,t4]
def v588 := [t82,t0,t1,t2,t3,t4,t87]
def v589 := [t82,t88,t0,t1,t2,t3,t4]
def v590 := [t82,t0,t1,t89,t3,t4]
def v591 := [t82,t0,t1,t89,t2,t3,t4]
def v592 := [t82,t118,t0,t1,t2,t3,t4]
def v593 := [t82,t0,t1,t2,t3,t4,t119]
def v594 := [t82,t0,t1,t2,t120,t3,t4]
def v595 := [t82,t121,t0,t1,t2,t3,t4]
def v596 := [t82,t0,t1,t2,t122,t3,t4]
def v597 := [t82,t0,t1,t2,t3,t4,t123]
def v598 := [t82,t124,t0,t1,t2,t3,t4]
def v599 := [t82,t125,t0,t1,t2,t3,t4]
def v600 := [t82,t98,t0,t1,t2,t3,t4]
def v601 := [t82,t0,t1,t2,t3,t4,t99]
def v602 := [t82,t100,t0,t1,t2,t3,t4]
def v603 := [t82,t0,t1,t2,t101,t3,t4]
def map31_6 : Projection 26 26 := pick [0,2,1,6,7,8,3,4,5,9,10,11,13,12,17,18,19,14,15,16,20,21,22,23,25,24] rfl (by decide +kernel) (by decide)
def v604 := [t5,t0,t1,t107,t2,t3,t4]
def v605 := [t0,t74,t1,t107,t2,t3,t4]
def v606 := [t0,t1,t107,t75,t2,t3,t4]
def v607 := [t0,t1,t107,t2,t3,t76,t4]
def v608 := [t7,t0,t1,t107,t2,t3,t4]
def v609 := [t0,t1,t107,t2,t12,t3,t4]
def v610 := [t106,t107,t2,t3,t4]
def v611 := [t106,t1,t107,t2,t3,t4]
def v612 := [t106,t0,t107,t2,t3,t4]
def v613 := [t106,t0,t1,t107,t2,t3,t4]
def v614 := [t108,t1,t107,t2,t3,t4]
def v615 := [t0,t108,t1,t107,t2,t3,t4]
def v616 := [t109,t0,t107,t2,t3,t4]
def v617 := [t121,t0,t1,t2,t4,t119]
def v618 := [t109,t0,t1,t107,t2,t3,t4]
def v619 := [t109,t0,t1,t2,t3,t4]
def v620 := [t0,t110,t1,t107,t2,t3,t4]
def v621 := [t0,t1,t107,t2,t3,t4,t111]
def v622 := [t0,t1,t107,t2,t113,t3,t4]
def v623 := [t0,t1,t107,t114,t2,t3,t4]
def v624 := [t0,t1,t107,t2,t3,t115,t4]
def v625 := [t116,t0,t1,t107,t2,t3,t4]
def v626 := [t0,t1,t117,t107,t2,t3,t4]
def v627 := [t0,t1,t107,t2,t83,t3,t4]
def v628 := [t0,t1,t107,t84,t2,t3,t4]
def v629 := [t85,t0,t1,t107,t2,t3,t4]
def v632 := [t204,t0,t1,t107,t3,t4]
def v634 := [t204,t0,t1,t107,t2,t3,t4]
def v635 := [t0,t1,t107,t2,t3,t143,t4]
def v636 := [t0,t1,t107,t205,t2,t3,t4]
def map31_16 : Projection 26 26 := pick [22,21,23,3,5,4,15,16,14,24,12,13,10,11,8,6,7,19,18,17,25,1,0,2,9,20] rfl (by decide +kernel) (by decide)
def t253 := 0x6a744e9e1c038
def v638 := [t0,t1,t253,t3,t4]
def t254 := 0x26f225c1fc007
def v639 := [t254,t0,t1,t2,t4]
def v640 := [t0,t1,t253,t2,t3,t4]
def v641 := [t254,t0,t1,t2,t3,t4]
def v642 := [t0,t1,t253,t107,t3,t4]
def v643 := [t254,t0,t1,t107,t2,t4]
def v644 := [t223,t224,t221,t222]
def v645 := [t223,t219,t224,t221,t222]
def v646 := [t223,t220,t224,t221,t222]
def v647 := [t225,t219,t224,t221,t222]
def v648 := [t226,t220,t224,t221,t222]
def v649 := [t219,t224,t221,t236,t222]
def v650 := [t219,t237,t224,t221,t222]
def v651 := [t219,t224,t221,t222,t240]
def v652 := [t241,t219,t224,t221,t222]
def t255 := 0x308fc
def v653 := [t255,t219,t220,t222]
def v654 := [t255,t219,t220,t224,t222]
def v655 := [t255,t219,t220,t221,t222]
def t256 := 0xdfffff
def v656 := [t219,t220,t221,t256,t222]
def t257 := 0x54b703
def v657 := [t219,t220,t257,t222]
def v658 := [t219,t220,t257,t224,t222]
def v659 := [t219,t220,t257,t221,t222]
def t258 := 0x884000
def v660 := [t219,t220,t258,t221,t222]
def t259 := 0x440fe0
def v661 := [t219,t259,t220,t221]
def v662 := [t219,t259,t220,t224,t221]
def v663 := [t219,t259,t220,t221,t222]
def t260 := 0xffbfff
def v664 := [t219,t220,t221,t222,t260]
def t261 := 0x13b01f
def v665 := [t219,t261,t220,t221]
def v666 := [t219,t261,t220,t224,t221]
def v667 := [t219,t261,t220,t221,t222]
def t262 := 0xa80000
def v668 := [t219,t220,t221,t262,t222]
def v669 := [t0,t1,t253,t107,t2,t3,t4]
def v670 := [t0,t1,t107,t86,t2,t3,t4]
def v671 := [t0,t1,t107,t2,t3,t4,t87]
def v672 := [t88,t0,t1,t107,t2,t3,t4]
def v673 := [t0,t1,t107,t89,t2,t3,t4]
def v674 := [t118,t0,t1,t107,t2,t3,t4]
def v675 := [t0,t1,t107,t2,t3,t4,t119]
def v676 := [t0,t1,t107,t2,t120,t3,t4]
def v677 := [t121,t0,t1,t107,t2,t3,t4]
def t263 := 0x4805ca3e03ff8
def v678 := [t0,t1,t263,t2,t4]
def v679 := [t0,t1,t263,t2,t3,t4]
def v680 := [t0,t1,t263,t107,t2,t4]
def v681 := [t0,t1,t263,t107,t2,t3,t4]
def v682 := [t0,t1,t2,t3,t4,t91]
def v683 := [t0,t1,t107,t2,t3,t4,t91]
def t264 := 0x9008100000000
def v684 := [t0,t1,t2,t264,t3,t4]
def v685 := [t0,t1,t107,t2,t264,t3,t4]
def map31_10 : Projection 26 26 := pick [18,17,19,0,2,1,15,16,14,20,11,13,10,12,7,6,8,23,22,21,25,4,3,5,9,24] rfl (by decide +kernel) (by decide)
def map31_13 : Projection 26 26 := pick [3,5,4,22,21,23,15,14,16,24,12,10,13,11,8,6,7,1,0,2,9,19,18,17,25,20] rfl (by decide +kernel) (by decide)
def v686 := [t254,t0,t1,t107,t2,t3,t4]
def v687 := [t0,t1,t107,t2,t122,t3,t4]
def v688 := [t0,t1,t107,t2,t3,t4,t123]
def v689 := [t124,t0,t1,t107,t2,t3,t4]
def v690 := [t125,t0,t1,t107,t2,t3,t4]
def v691 := [t98,t0,t1,t107,t2,t3,t4]
def v692 := [t0,t1,t107,t2,t3,t4,t99]
def v693 := [t100,t0,t1,t107,t2,t3,t4]
def v694 := [t0,t1,t107,t2,t101,t3,t4]
def t265 := 0x6666003fffc00
def v695 := [t0,t1,t265,t2,t3]
def v696 := [t0,t1,t265,t107,t2,t3]
def v697 := [t0,t1,t265,t2,t3,t4]
def v698 := [t0,t1,t265,t107,t2,t3,t4]
def t266 := 0xffffeffffffff
def v699 := [t0,t1,t2,t3,t4,t266]
def v700 := [t0,t1,t107,t2,t3,t4,t266]
def t267 := 0x891efc0003ff
def v701 := [t267,t0,t1,t2,t3]
def v702 := [t267,t0,t1,t107,t2,t3]
def v703 := [t267,t0,t1,t2,t3,t4]
def v704 := [t267,t0,t1,t107,t2,t3,t4]
def t268 := 0x9108000000000
def v705 := [t0,t1,t2,t268,t3,t4]
def v706 := [t0,t1,t107,t2,t268,t3,t4]
def v707 := [t5,t121,t0,t1,t2,t3,t4]
def v708 := [t121,t0,t74,t1,t2,t3,t4]
def v709 := [t121,t0,t1,t75,t2,t3,t4]
def v710 := [t121,t0,t1,t2,t3,t76,t4]
def v711 := [t7,t121,t0,t1,t2,t4]
def v712 := [t7,t121,t0,t1,t2,t3,t4]
def v713 := [t121,t0,t1,t2,t12,t3,t4]
def t269 := 0x1004811c007
def v714 := [t269,t0,t1,t2,t3,t4]
def v715 := [t269,t121,t0,t1,t2,t3,t4]
def t270 := 0x66f7a7d1ffe3f
def v716 := [t0,t1,t270,t2,t3,t4]
def v717 := [t121,t0,t1,t270,t2,t3,t4]
def t271 := 0x4427825003e38
def v718 := [t0,t271,t1,t2,t3,t4]
def v719 := [t121,t0,t271,t1,t2,t3,t4]
def v720 := [t93,t0,t1,t2,t3,t4]
def v721 := [t93,t121,t0,t1,t2,t3,t4]
def v722 := [t106,t121,t0,t1,t2,t3,t4]
def v723 := [t121,t0,t108,t1,t2,t3,t4]
def v724 := [t121,t109,t0,t1,t2,t3,t4]
def v725 := [t121,t0,t110,t1,t2,t3,t4]
def v726 := [t121,t0,t1,t2,t3,t4,t111]
def v727 := [t121,t0,t1,t2,t113,t3,t4]
def v728 := [t121,t0,t1,t114,t2,t4]
def v729 := [t121,t0,t1,t114,t2,t3,t4]
def v730 := [t121,t0,t1,t2,t3,t115,t4]
def v731 := [t116,t121,t0,t1,t2,t4]
def v732 := [t116,t121,t0,t1,t2,t3,t4]
def v733 := [t121,t0,t1,t117,t2,t3,t4]
def v734 := [t217,t121,t0,t1,t2,t3,t4]
def t272 := 0xa7dbb5e1fffc7
def v735 := [t0,t1,t2,t272,t3,t4]
def v736 := [t121,t0,t1,t2,t272,t3,t4]
def t273 := 0x850b906003fc0
def v737 := [t0,t1,t273,t2,t3,t4]
def v738 := [t121,t0,t1,t273,t2,t3,t4]
def t274 := 0x225004801c000
def v739 := [t274,t0,t1,t2,t3,t4]
def v740 := [t274,t121,t0,t1,t2,t3,t4]
def v741 := [t121,t0,t1,t2,t83,t3,t4]
def v742 := [t121,t0,t1,t84,t2,t3,t4]
def v743 := [t121,t85,t0,t1,t2,t3,t4]
def v744 := [t121,t0,t1,t86,t2,t3,t4]
def v745 := [t121,t0,t1,t2,t3,t4,t87]
def v746 := [t88,t121,t0,t1,t2,t3,t4]
def v747 := [t121,t0,t1,t89,t2,t3,t4]
def v748 := [t0,t1,t2,t3,t4,t119]
def v749 := [t121,t0,t1,t2,t3,t4,t119]
def v750 := [t118,t121,t1,t2,t3,t4]
def v751 := [t118,t121,t0,t1,t2,t3,t4]
def v752 := [t121,t1,t2,t120,t4]
def p31_15 : Projection 26 10 := pick [0,1,2,3,4,5,6,7,8,9] rfl (by decide +kernel) (by decide)
def v783 := [t121,t1,t2,t120,t3,t4]
def v784 := [t121,t0,t1,t2,t120,t4]
def v785 := [t109,t0,t108,t2,t3,t4]
def v786 := [t121,t0,t1,t2,t120,t3,t4]
def v787 := [t121,t0,t1,t2,t122,t4]
def v788 := [t121,t0,t1,t2,t122,t3,t4]
def v789 := [t121,t0,t1,t2,t3,t4,t123]
def v790 := [t124,t121,t0,t1,t2,t3,t4]
def v791 := [t121,t125,t0,t1,t2,t4]
def v792 := [t121,t125,t0,t1,t2,t3,t4]
def v793 := [t118,t0,t1,t2,t3,t4]
def t290 := 0x22400001fc000
def v794 := [t290,t0,t1,t2,t3,t4]
def v795 := [t290,t121,t0,t1,t2,t3,t4]
def t291 := 0xf7fe25bfffc07
def v796 := [t0,t1,t2,t3,t4,t291]
def v797 := [t121,t0,t1,t2,t3,t4,t291]
def t292 := 0x90258000007
def v798 := [t292,t0,t1,t2,t3,t4]
def v799 := [t292,t121,t0,t1,t2,t3,t4]
def t293 := 0xd52e003e03c00
def v800 := [t0,t1,t2,t293,t3,t4]
def v801 := [t121,t0,t1,t2,t293,t3,t4]
def v802 := [t98,t121,t0,t1,t2,t3,t4]
def v803 := [t121,t0,t1,t2,t3,t4,t99]
def v804 := [t100,t121,t0,t1,t2,t3,t4]
def v805 := [t121,t0,t1,t2,t101,t3,t4]
def v806 := [t0,t1,t2,t113,t3,t4]
def map31_21 : Projection 26 26 := pick [18,19,17,22,23,21,6,7,8,25,13,11,12,10,16,15,14,2,0,1,20,5,3,4,24,9] rfl (by decide +kernel) (by decide)
def v807 := [t0,t1,t114,t2,t3,t4]
def v808 := [t0,t1,t2,t3,t115,t4]
def v809 := [t116,t0,t1,t2,t3,t4]
def map31_7 : Projection 26 26 := pick [0,2,1,18,17,19,15,14,16,20,11,10,13,12,7,6,8,4,3,5,9,23,22,21,25,24] rfl (by decide +kernel) (by decide)
def v810 := [t0,t1,t117,t2,t3,t4]
def v811 := [t0,t1,t2,t83,t3,t4]
def v812 := [t0,t1,t86,t2,t3,t4]
def v813 := [t0,t1,t2,t3,t4,t87]
def v814 := [t88,t0,t1,t2,t3,t4]
def v815 := [t0,t1,t89,t2,t3,t4]
def map31_19 : Projection 26 26 := pick [15,16,14,22,23,21,3,4,5,24,12,11,13,10,19,18,17,1,0,2,20,8,6,7,25,9] rfl (by decide +kernel) (by decide)
def map31_11 : Projection 26 26 := pick [18,17,19,6,7,8,22,23,21,25,13,11,10,12,2,0,1,16,15,14,20,5,3,4,9,24] rfl (by decide +kernel) (by decide)
def v816 := [t0,t1,t2,t120,t3,t4]
def v817 := [t0,t1,t2,t122,t3,t4]
def v818 := [t0,t1,t2,t3,t4,t123]
def v819 := [t124,t0,t1,t2,t3,t4]
def v820 := [t125,t0,t1,t2,t3,t4]
def v821 := [t98,t0,t1,t2,t3,t4]
def v822 := [t0,t1,t2,t3,t4,t99]
def v823 := [t100,t0,t1,t2,t3,t4]
def v824 := [t0,t1,t2,t101,t3,t4]
theorem b213 : Ban 10 4 v207 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w3 : Wide 10 4 v207 := viaSub (ws := [v207]) (consBan b213 (nilBan 10 4)) (by decide) (by decide +kernel)
theorem b0 : Ban 26 6 v3 := smallByCut p31_27 w3
theorem b1 : Ban 26 6 v4 := smallByCut p31_30 w3
theorem b2 : Ban 26 6 v5 := smallByCut p31_27 w3
theorem b3 : Ban 26 6 v6 := smallByCut p31_27 w3
theorem b4 : Ban 26 6 v7 := smallByCut p31_27 w3
theorem b5 : Ban 26 6 v8 := checkedSmall
theorem b6 : Ban 26 6 v9 := smallByCut p31_27 w3
theorem b7 : Ban 26 6 v10 := smallByCut p31_27 w3
theorem b8 : Ban 26 6 v11 := smallByCut p31_27 w3
theorem b9 : Ban 26 6 v12 := smallByCut p31_29 w3
theorem b10 : Ban 26 6 v13 := smallByCut p31_27 w3
theorem b11 : Ban 26 6 v14 := smallByCut p31_27 w3
theorem b12 : Ban 26 6 v15 := smallByCut p31_27 w3
theorem b13 : Ban 26 6 v16 := smallByCut p31_27 w3
theorem b14 : Ban 26 6 v17 := smallByCut p31_27 w3
theorem b15 : Ban 26 6 v18 := smallByCut p31_27 w3
theorem b16 : Ban 6 3 v23 := checkedSmall
theorem b65 : Ban 6 3 v70 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w1 : Wide 6 3 v70 := viaSub (ws := [v23,v70]) (consBan b16 (consBan b65 (nilBan 6 3))) (by decide) (by decide +kernel)
theorem b17 : Ban 12 5 v22 := smallByCut p1047_1045 w1
theorem b18 : Ban 12 4 v25 := smallByCut p1047_1045 w1
theorem b19 : Ban 12 4 v26 := smallByCut p1047_1045 w1
theorem b20 : Ban 12 4 v27 := smallByCut p1047_1045 w1
theorem b21 : Ban 12 4 v28 := smallByCut p1047_1046 w1
theorem b22 : Ban 12 4 v29 := smallByCut p1047_1045 w1
theorem b23 : Ban 12 4 v30 := smallByCut p1047_1045 w1
theorem b24 : Ban 12 4 v31 := checkedSmall
theorem b25 : Ban 12 4 v32 := smallByCut p1047_1046 w1
theorem b26 : Ban 12 4 v33 := checkedSmall
theorem b27 : Ban 12 4 v34 := smallByCut p1047_1046 w1
theorem b28 : Ban 12 4 v35 := smallByCut p1047_1045 w1
theorem b29 : Ban 12 4 v36 := checkedSmall
theorem b30 : Ban 12 4 v37 := smallByCut p1047_1045 w1
theorem b31 : Ban 12 4 v38 := checkedSmall
theorem b32 : Ban 12 4 v39 := smallByCut p1047_1045 w1
theorem b33 : Ban 12 4 v40 := checkedSmall
theorem b34 : Ban 12 4 v41 := checkedSmall
theorem b35 : Ban 12 4 v42 := checkedSmall
theorem b36 : Ban 12 4 v43 := checkedSmall
theorem b37 : Ban 12 4 v44 := checkedSmall
theorem b38 : Ban 12 4 v45 := checkedSmall
theorem b39 : Ban 12 4 v46 := checkedSmall
theorem b40 : Ban 12 4 v47 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b41 : Ban 12 5 v24 := viaBranch (ws := [v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47]) (consBan b18 (consBan b19 (consBan b20 (consBan b21 (consBan b22 (consBan b23 (consBan b24 (consBan b25 (consBan b26 (consBan b27 (consBan b28 (consBan b29 (consBan b30 (consBan b31 (consBan b32 (consBan b33 (consBan b34 (consBan b35 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (consBan b40 (nilBan 12 4)))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b43 : Ban 12 5 v35 := smallByCut p1047_1046 w1
theorem b44 : Ban 12 5 v30 := smallByCut p1047_1045 w1
theorem b45 : Ban 12 5 v49 := smallByCut p1047_1046 w1
theorem b46 : Ban 12 5 v50 := viaPerm map1047_2 map1047_2 b41 (by decide +kernel) (by decide +kernel)
theorem b47 : Ban 12 5 v51 := smallByCut p1047_1046 w1
theorem b42 : Ban 12 5 v48 := smallByCut p1047_1046 w1
theorem b48 : Ban 12 5 v52 := viaPerm map1047_15 map1047_20 b42 (by decide +kernel) (by decide +kernel)
theorem b49 : Ban 12 5 v53 := smallByCut p1047_1046 w1
theorem b50 : Ban 12 5 v54 := viaPerm map1047_4 map1047_3 b41 (by decide +kernel) (by decide +kernel)
theorem b51 : Ban 12 5 v55 := viaPerm map1047_21 map1047_21 b42 (by decide +kernel) (by decide +kernel)
theorem b52 : Ban 12 5 v56 := smallByCut p1047_1045 w1
theorem b53 : Ban 12 5 v57 := viaPerm map1047_8 map1047_12 b41 (by decide +kernel) (by decide +kernel)
theorem b54 : Ban 12 5 v58 := smallByCut p1047_1045 w1
theorem b55 : Ban 12 5 v59 := viaPerm map1047_13 map1047_10 b42 (by decide +kernel) (by decide +kernel)
theorem b56 : Ban 12 5 v60 := smallByCut p1047_1045 w1
theorem b57 : Ban 12 5 v61 := viaPerm map1047_10 map1047_13 b41 (by decide +kernel) (by decide +kernel)
theorem b58 : Ban 12 5 v62 := smallByCut p1047_1045 w1
theorem b59 : Ban 12 5 v63 := viaPerm map1047_19 map1047_11 b42 (by decide +kernel) (by decide +kernel)
theorem b60 : Ban 12 5 v64 := viaPerm map1047_16 map1047_16 b17 (by decide +kernel) (by decide +kernel)
theorem b61 : Ban 12 5 v65 := viaPerm map1047_16 map1047_16 b41 (by decide +kernel) (by decide +kernel)
theorem b62 : Ban 12 5 v66 := viaPerm map1047_12 map1047_8 b42 (by decide +kernel) (by decide +kernel)
theorem b63 : Ban 12 5 v67 := viaPerm map1047_18 map1047_9 b42 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b64 : Ban 12 6 v21 := viaBranch (ws := [v22,v24,v35,v30,v49,v50,v51,v52,v53,v54,v48,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67]) (consBan b17 (consBan b41 (consBan b43 (consBan b44 (consBan b45 (consBan b46 (consBan b47 (consBan b48 (consBan b49 (consBan b50 (consBan b42 (consBan b51 (consBan b52 (consBan b53 (consBan b54 (consBan b55 (consBan b56 (consBan b57 (consBan b58 (consBan b59 (consBan b60 (consBan b61 (consBan b62 (consBan b63 (nilBan 12 5))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b66 : Ban 12 5 v69 := smallByCut p1047_1045 w1
theorem b67 : Ban 12 5 v71 := checkedSmall
theorem b68 : Ban 12 5 v72 := smallByCut p1047_1046 w1
theorem b69 : Ban 12 5 v73 := smallByCut p1047_1045 w1
theorem b70 : Ban 12 5 v74 := smallByCut p1047_1046 w1
theorem b71 : Ban 12 5 v75 := checkedSmall
theorem b72 : Ban 12 5 v76 := smallByCut p1047_1046 w1
theorem b73 : Ban 12 5 v77 := checkedSmall
theorem b74 : Ban 12 5 v78 := smallByCut p1047_1046 w1
theorem b75 : Ban 12 5 v79 := checkedSmall
theorem b76 : Ban 12 5 v80 := smallByCut p1047_1046 w1
theorem b77 : Ban 12 5 v81 := checkedSmall
theorem b78 : Ban 12 4 v84 := checkedSmall
theorem b79 : Ban 12 4 v85 := checkedSmall
theorem b80 : Ban 12 4 v86 := checkedSmall
theorem b81 : Ban 12 4 v87 := checkedSmall
theorem b82 : Ban 12 4 v88 := checkedSmall
theorem b83 : Ban 12 4 v89 := checkedSmall
theorem b84 : Ban 12 4 v90 := checkedSmall
theorem b85 : Ban 12 4 v91 := checkedSmall
theorem b86 : Ban 12 4 v92 := checkedSmall
theorem b87 : Ban 12 4 v93 := checkedSmall
theorem b88 : Ban 12 4 v94 := checkedSmall
theorem b89 : Ban 12 4 v95 := checkedSmall
theorem b90 : Ban 12 4 v96 := checkedSmall
theorem b91 : Ban 12 4 v97 := checkedSmall
theorem b92 : Ban 12 4 v98 := checkedSmall
theorem b93 : Ban 12 4 v99 := checkedSmall
theorem b94 : Ban 12 4 v100 := checkedSmall
theorem b95 : Ban 12 4 v101 := checkedSmall
theorem b96 : Ban 12 4 v102 := checkedSmall
theorem b97 : Ban 12 4 v103 := checkedSmall
theorem b98 : Ban 12 4 v104 := checkedSmall
theorem b99 : Ban 12 4 v105 := checkedSmall
theorem b100 : Ban 12 4 v106 := checkedSmall
theorem b101 : Ban 12 4 v107 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b102 : Ban 12 5 v83 := viaBranch (ws := [v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107]) (consBan b78 (consBan b79 (consBan b80 (consBan b81 (consBan b82 (consBan b83 (consBan b84 (consBan b85 (consBan b86 (consBan b87 (consBan b88 (consBan b89 (consBan b90 (consBan b91 (consBan b92 (consBan b93 (consBan b94 (consBan b95 (consBan b96 (consBan b97 (consBan b98 (consBan b99 (consBan b100 (consBan b101 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b103 : Ban 12 5 v82 := viaPerm map1047_9 map1047_18 b102 (by decide +kernel) (by decide +kernel)
theorem b104 : Ban 12 4 v48 := smallByCut p1047_1046 w1
theorem b105 : Ban 12 4 v110 := checkedSmall
theorem b106 : Ban 12 4 v53 := smallByCut p1047_1046 w1
theorem b107 : Ban 12 4 v111 := checkedSmall
theorem b108 : Ban 12 4 v112 := checkedSmall
theorem b109 : Ban 12 4 v113 := checkedSmall
theorem b110 : Ban 12 4 v62 := smallByCut p1047_1045 w1
theorem b111 : Ban 12 4 v114 := checkedSmall
theorem b112 : Ban 12 4 v60 := smallByCut p1047_1045 w1
theorem b113 : Ban 12 4 v115 := checkedSmall
theorem b114 : Ban 12 4 v116 := checkedSmall
theorem b115 : Ban 12 4 v117 := checkedSmall
theorem b116 : Ban 12 4 v66 := checkedSmall
theorem b117 : Ban 12 4 v118 := checkedSmall
theorem b118 : Ban 12 4 v64 := checkedSmall
theorem b119 : Ban 12 4 v119 := checkedSmall
theorem b120 : Ban 12 4 v120 := checkedSmall
theorem b121 : Ban 12 4 v121 := checkedSmall
theorem b122 : Ban 12 4 v122 := checkedSmall
theorem b123 : Ban 12 4 v68 := smallByCut p1047_1045 w1
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b124 : Ban 12 5 v109 := viaBranch (ws := [v48,v110,v53,v111,v94,v112,v92,v113,v62,v114,v60,v115,v102,v116,v100,v117,v66,v118,v64,v119,v106,v120,v104,v121,v122,v68]) (consBan b104 (consBan b105 (consBan b106 (consBan b107 (consBan b88 (consBan b108 (consBan b86 (consBan b109 (consBan b110 (consBan b111 (consBan b112 (consBan b113 (consBan b96 (consBan b114 (consBan b94 (consBan b115 (consBan b116 (consBan b117 (consBan b118 (consBan b119 (consBan b100 (consBan b120 (consBan b98 (consBan b121 (consBan b122 (consBan b123 (nilBan 12 4))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b125 : Ban 12 5 v108 := viaPerm map1047_9 map1047_18 b124 (by decide +kernel) (by decide +kernel)
theorem b126 : Ban 12 5 v123 := checkedSmall
theorem b127 : Ban 12 5 v124 := checkedSmall
theorem b128 : Ban 12 5 v125 := smallByCut p1047_1045 w1
theorem b129 : Ban 12 5 v126 := checkedSmall
theorem b130 : Ban 12 5 v127 := smallByCut p1047_1045 w1
theorem b131 : Ban 12 5 v128 := checkedSmall
theorem b132 : Ban 12 5 v129 := smallByCut p1047_1045 w1
theorem b133 : Ban 12 5 v130 := checkedSmall
theorem b134 : Ban 12 5 v131 := smallByCut p1047_1045 w1
theorem b135 : Ban 12 5 v132 := checkedSmall
theorem b136 : Ban 12 5 v133 := viaPerm map1047_3 map1047_4 b102 (by decide +kernel) (by decide +kernel)
theorem b137 : Ban 12 5 v134 := viaPerm map1047_3 map1047_4 b124 (by decide +kernel) (by decide +kernel)
theorem b138 : Ban 12 5 v135 := checkedSmall
theorem b139 : Ban 12 5 v136 := checkedSmall
theorem b140 : Ban 12 5 v137 := viaPerm map1047_16 map1047_16 b66 (by decide +kernel) (by decide +kernel)
theorem b141 : Ban 12 5 v138 := checkedSmall
theorem b142 : Ban 12 5 v139 := checkedSmall
theorem b143 : Ban 12 5 v140 := checkedSmall
theorem b144 : Ban 12 5 v141 := viaPerm map1047_1 map1047_1 b102 (by decide +kernel) (by decide +kernel)
theorem b145 : Ban 12 5 v142 := viaPerm map1047_1 map1047_1 b124 (by decide +kernel) (by decide +kernel)
theorem b146 : Ban 12 5 v143 := checkedSmall
theorem b147 : Ban 12 5 v144 := checkedSmall
theorem b148 : Ban 12 5 v122 := checkedSmall
theorem b149 : Ban 12 5 v145 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b150 : Ban 12 6 v68 := viaBranch (ws := [v69,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v108,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v83,v109,v122,v145]) (consBan b66 (consBan b67 (consBan b68 (consBan b69 (consBan b70 (consBan b71 (consBan b72 (consBan b73 (consBan b74 (consBan b75 (consBan b76 (consBan b77 (consBan b103 (consBan b125 (consBan b126 (consBan b127 (consBan b128 (consBan b129 (consBan b130 (consBan b131 (consBan b132 (consBan b133 (consBan b134 (consBan b135 (consBan b136 (consBan b137 (consBan b138 (consBan b139 (consBan b140 (consBan b141 (consBan b142 (consBan b143 (consBan b144 (consBan b145 (consBan b146 (consBan b147 (consBan b102 (consBan b124 (consBan b148 (consBan b149 (nilBan 12 5))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w2 : Wide 12 6 v68 := viaSub (ws := [v21,v68]) (consBan b64 (consBan b150 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b152 : Ban 26 6 v19 := smallByCut p31_1047 w2
theorem b153 : Ban 26 6 v146 := smallByCut p31_27 w3
theorem b154 : Ban 26 6 v147 := smallByCut p31_27 w3
theorem b155 : Ban 26 6 v148 := smallByCut p31_27 w3
theorem b156 : Ban 26 6 v149 := checkedSmall
theorem b157 : Ban 26 6 v150 := smallByCut p31_27 w3
theorem b158 : Ban 26 6 v151 := smallByCut p31_15 w3
theorem b159 : Ban 26 6 v152 := smallByCut p31_27 w3
theorem b160 : Ban 26 6 v153 := checkedSmall
theorem b161 : Ban 26 6 v154 := smallByCut p31_27 w3
theorem b162 : Ban 26 6 v155 := smallByCut p31_27 w3
theorem b163 : Ban 26 6 v156 := smallByCut p31_27 w3
theorem b164 : Ban 26 6 v157 := smallByCut p31_15 w3
theorem b165 : Ban 26 6 v158 := smallByCut p31_27 w3
theorem b166 : Ban 26 6 v159 := smallByCut p31_30 w3
theorem b167 : Ban 26 6 v160 := smallByCut p31_30 w3
theorem b168 : Ban 26 6 v161 := smallByCut p31_30 w3
theorem b169 : Ban 26 6 v162 := smallByCut p31_30 w3
theorem b170 : Ban 26 5 v164 := smallByCut p31_27 w3
theorem b171 : Ban 26 5 v165 := smallByCut p31_27 w3
theorem b172 : Ban 26 5 v166 := smallByCut p31_27 w3
theorem b173 : Ban 26 5 v167 := smallByCut p31_27 w3
theorem b417 : Ban 10 3 v394 := checkedSmall
theorem b418 : Ban 10 3 v395 := checkedSmall
theorem b419 : Ban 10 3 v396 := checkedSmall
theorem b420 : Ban 10 3 v397 := checkedSmall
theorem b421 : Ban 10 3 v398 := checkedSmall
theorem b422 : Ban 10 3 v399 := checkedSmall
theorem b423 : Ban 10 3 v400 := checkedSmall
theorem b424 : Ban 10 3 v401 := checkedSmall
theorem b425 : Ban 10 3 v402 := checkedSmall
theorem b426 : Ban 10 3 v403 := checkedSmall
theorem b427 : Ban 10 3 v404 := checkedSmall
theorem b428 : Ban 10 3 v405 := checkedSmall
theorem b429 : Ban 10 3 v406 := checkedSmall
theorem b430 : Ban 10 3 v407 := checkedSmall
theorem b431 : Ban 10 3 v408 := checkedSmall
theorem b432 : Ban 10 3 v409 := checkedSmall
theorem b433 : Ban 10 3 v410 := checkedSmall
theorem b434 : Ban 10 3 v411 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b435 : Ban 10 4 v393 := viaBranch (ws := [v394,v395,v396,v397,v398,v399,v400,v401,v402,v403,v404,v405,v406,v407,v408,v409,v410,v411]) (consBan b417 (consBan b418 (consBan b419 (consBan b420 (consBan b421 (consBan b422 (consBan b423 (consBan b424 (consBan b425 (consBan b426 (consBan b427 (consBan b428 (consBan b429 (consBan b430 (consBan b431 (consBan b432 (consBan b433 (consBan b434 (nilBan 10 3))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b436 : Ban 10 4 v392 := viaPerm map15_2 map15_2 b435 (by decide +kernel) (by decide +kernel)
theorem solidb436 : Wide 10 4 v392 := solid b436
theorem b174 : Ban 26 5 v168 := smallByCut p31_15 solidb436
theorem b175 : Ban 26 5 v169 := smallByCut p31_27 w3
theorem b176 : Ban 26 5 v170 := checkedSmall
theorem b177 : Ban 26 5 v171 := smallByCut p31_27 w3
theorem b178 : Ban 26 5 v172 := smallByCut p31_27 w3
theorem b179 : Ban 26 5 v173 := smallByCut p31_27 w3
theorem b180 : Ban 26 5 v174 := smallByCut p31_27 w3
theorem b181 : Ban 26 5 v175 := smallByCut p31_27 w3
theorem b182 : Ban 26 5 v176 := smallByCut p31_27 w3
theorem b183 : Ban 26 5 v177 := smallByCut p31_27 w3
theorem b184 : Ban 26 5 v178 := smallByCut p31_27 w3
theorem b185 : Ban 26 5 v179 := smallByCut p31_27 w3
theorem b562 : Ban 12 4 v527 := checkedSmall
theorem b563 : Ban 12 4 v528 := checkedSmall
theorem b564 : Ban 12 4 v529 := checkedSmall
theorem b565 : Ban 12 4 v530 := checkedSmall
theorem b566 : Ban 12 4 v531 := checkedSmall
theorem b567 : Ban 12 4 v532 := checkedSmall
theorem b568 : Ban 12 4 v533 := checkedSmall
theorem b569 : Ban 12 4 v534 := checkedSmall
theorem b570 : Ban 12 4 v535 := checkedSmall
theorem b571 : Ban 12 4 v536 := checkedSmall
theorem b572 : Ban 12 4 v537 := checkedSmall
theorem b573 : Ban 12 4 v538 := checkedSmall
theorem b574 : Ban 12 4 v539 := checkedSmall
theorem b575 : Ban 12 4 v540 := checkedSmall
theorem b576 : Ban 12 4 v541 := checkedSmall
theorem b577 : Ban 12 4 v542 := checkedSmall
theorem b578 : Ban 12 4 v543 := checkedSmall
theorem b579 : Ban 12 4 v544 := checkedSmall
theorem b580 : Ban 12 4 v545 := checkedSmall
theorem b581 : Ban 12 4 v546 := checkedSmall
theorem b582 : Ban 12 4 v547 := checkedSmall
theorem b583 : Ban 12 4 v548 := checkedSmall
theorem b584 : Ban 12 4 v549 := checkedSmall
theorem b585 : Ban 12 4 v550 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b586 : Ban 12 5 v526 := viaBranch (ws := [v527,v528,v529,v530,v531,v532,v533,v534,v535,v536,v537,v538,v539,v540,v541,v542,v543,v544,v545,v546,v547,v548,v549,v550]) (consBan b562 (consBan b563 (consBan b564 (consBan b565 (consBan b566 (consBan b567 (consBan b568 (consBan b569 (consBan b570 (consBan b571 (consBan b572 (consBan b573 (consBan b574 (consBan b575 (consBan b576 (consBan b577 (consBan b578 (consBan b579 (consBan b580 (consBan b581 (consBan b582 (consBan b583 (consBan b584 (consBan b585 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b587 : Ban 12 5 v551 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w6 : Wide 12 5 v551 := viaSub (ws := [v526,v551]) (consBan b586 (consBan b587 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b186 : Ban 26 5 v180 := smallByCut p31_539 w6
theorem b187 : Ban 26 5 v181 := smallByCut p31_539 w6
theorem b188 : Ban 26 5 v182 := smallByCut p31_539 w6
theorem b189 : Ban 26 5 v183 := checkedSmall
theorem b190 : Ban 26 5 v184 := checkedSmall
theorem b191 : Ban 26 5 v185 := checkedSmall
theorem b192 : Ban 26 5 v186 := checkedSmall
theorem b193 : Ban 26 5 v187 := checkedSmall
theorem b194 : Ban 26 5 v188 := checkedSmall
theorem b195 : Ban 26 5 v189 := checkedSmall
theorem b196 : Ban 26 5 v190 := checkedSmall
theorem b197 : Ban 26 5 v191 := checkedSmall
theorem b685 : Ban 12 4 v644 := checkedSmall
theorem b686 : Ban 12 4 v645 := checkedSmall
theorem b687 : Ban 12 4 v646 := checkedSmall
theorem b688 : Ban 12 4 v647 := checkedSmall
theorem b689 : Ban 12 4 v648 := checkedSmall
theorem b690 : Ban 12 4 v649 := checkedSmall
theorem b691 : Ban 12 4 v650 := checkedSmall
theorem b692 : Ban 12 4 v651 := checkedSmall
theorem b693 : Ban 12 4 v652 := checkedSmall
theorem b694 : Ban 12 4 v653 := checkedSmall
theorem b695 : Ban 12 4 v654 := checkedSmall
theorem b696 : Ban 12 4 v655 := checkedSmall
theorem b697 : Ban 12 4 v656 := checkedSmall
theorem b698 : Ban 12 4 v657 := checkedSmall
theorem b699 : Ban 12 4 v658 := checkedSmall
theorem b700 : Ban 12 4 v659 := checkedSmall
theorem b701 : Ban 12 4 v660 := checkedSmall
theorem b702 : Ban 12 4 v661 := checkedSmall
theorem b703 : Ban 12 4 v662 := checkedSmall
theorem b704 : Ban 12 4 v663 := checkedSmall
theorem b705 : Ban 12 4 v664 := checkedSmall
theorem b706 : Ban 12 4 v665 := checkedSmall
theorem b707 : Ban 12 4 v666 := checkedSmall
theorem b708 : Ban 12 4 v667 := checkedSmall
theorem b709 : Ban 12 4 v668 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b710 : Ban 12 5 v528 := viaBranch (ws := [v644,v645,v646,v647,v648,v530,v529,v649,v650,v651,v652,v653,v654,v655,v656,v657,v658,v659,v660,v661,v662,v663,v664,v665,v666,v667,v668]) (consBan b685 (consBan b686 (consBan b687 (consBan b688 (consBan b689 (consBan b565 (consBan b564 (consBan b690 (consBan b691 (consBan b692 (consBan b693 (consBan b694 (consBan b695 (consBan b696 (consBan b697 (consBan b698 (consBan b699 (consBan b700 (consBan b701 (consBan b702 (consBan b703 (consBan b704 (consBan b705 (consBan b706 (consBan b707 (consBan b708 (consBan b709 (nilBan 12 4)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w8 : Wide 12 5 v528 := viaSub (ws := [v526,v528]) (consBan b586 (consBan b710 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b198 : Ban 26 5 v192 := smallByCut p31_539 w8
theorem b199 : Ban 26 5 v193 := smallByCut p31_539 w6
theorem b200 : Ban 26 5 v194 := smallByCut p31_539 w6
theorem b201 : Ban 26 5 v195 := checkedSmall
theorem b202 : Ban 26 5 v196 := smallByCut p31_539 w8
theorem b203 : Ban 26 5 v197 := smallByCut p31_539 w6
theorem b204 : Ban 26 5 v198 := smallByCut p31_539 w6
theorem b205 : Ban 26 5 v199 := smallByCut p31_539 w6
theorem b206 : Ban 26 5 v200 := checkedSmall
theorem b207 : Ban 26 5 v201 := smallByCut p31_539 w6
theorem b208 : Ban 26 5 v202 := checkedSmall
theorem b209 : Ban 26 5 v203 := checkedSmall
theorem b210 : Ban 26 5 v204 := checkedSmall
theorem b211 : Ban 26 5 v205 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b212 : Ban 26 6 v163 := viaBranch (ws := [v164,v165,v166,v167,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205]) (consBan b170 (consBan b171 (consBan b172 (consBan b173 (consBan b174 (consBan b175 (consBan b176 (consBan b177 (consBan b178 (consBan b179 (consBan b180 (consBan b181 (consBan b182 (consBan b183 (consBan b184 (consBan b185 (consBan b186 (consBan b187 (consBan b188 (consBan b189 (consBan b190 (consBan b191 (consBan b192 (consBan b193 (consBan b194 (consBan b195 (consBan b196 (consBan b197 (consBan b198 (consBan b199 (consBan b200 (consBan b201 (consBan b202 (consBan b203 (consBan b204 (consBan b205 (consBan b206 (consBan b207 (consBan b208 (consBan b209 (consBan b210 (consBan b211 (nilBan 26 5))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b214 : Ban 26 6 v206 := smallByCut p31_30 w3
theorem b215 : Ban 26 6 v208 := smallByCut p31_27 w3
theorem b216 : Ban 26 6 v209 := smallByCut p31_27 w3
theorem b217 : Ban 26 6 v210 := smallByCut p31_30 w3
theorem b218 : Ban 26 6 v211 := smallByCut p31_30 w3
theorem b219 : Ban 26 6 v212 := smallByCut p31_30 w3
theorem b220 : Ban 26 6 v213 := smallByCut p31_30 w3
theorem b221 : Ban 26 6 v214 := checkedSmall
theorem b222 : Ban 26 6 v215 := smallByCut p31_30 w3
theorem b223 : Ban 26 6 v216 := smallByCut p31_30 w3
theorem b224 : Ban 26 6 v217 := smallByCut p31_30 w3
theorem b225 : Ban 26 6 v218 := smallByCut p31_30 w3
theorem b226 : Ban 26 6 v219 := smallByCut p31_30 w3
theorem b227 : Ban 26 6 v220 := smallByCut p31_27 w3
theorem b228 : Ban 26 6 v221 := smallByCut p31_27 w3
theorem b229 : Ban 26 6 v222 := smallByCut p31_27 w3
theorem b230 : Ban 26 6 v223 := smallByCut p31_27 w3
theorem b231 : Ban 26 6 v224 := checkedSmall
theorem b232 : Ban 26 6 v225 := checkedSmall
theorem b233 : Ban 26 6 v226 := checkedSmall
theorem b234 : Ban 26 6 v227 := checkedSmall
theorem b235 : Ban 26 6 v228 := checkedSmall
theorem b236 : Ban 26 6 v229 := checkedSmall
theorem b237 : Ban 26 6 v230 := checkedSmall
theorem b238 : Ban 26 6 v231 := checkedSmall
theorem b239 : Ban 26 6 v232 := smallByCut p31_27 w3
theorem b240 : Ban 26 6 v233 := smallByCut p31_27 w3
theorem b241 : Ban 26 6 v234 := smallByCut p31_27 w3
theorem b242 : Ban 26 6 v235 := smallByCut p31_27 w3
theorem b243 : Ban 26 6 v236 := smallByCut p31_539 w8
theorem b244 : Ban 26 6 v237 := smallByCut p31_27 w3
theorem b245 : Ban 26 6 v238 := smallByCut p31_27 w3
theorem b246 : Ban 26 6 v239 := smallByCut p31_27 w3
theorem b247 : Ban 26 6 v240 := smallByCut p31_27 w3
theorem b248 : Ban 26 6 v241 := smallByCut p31_27 w3
theorem b249 : Ban 26 6 v242 := checkedSmall
theorem b250 : Ban 26 6 v243 := checkedSmall
theorem b251 : Ban 26 6 v244 := checkedSmall
theorem b252 : Ban 26 6 v245 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b253 : Ban 26 7 v2 := viaBranch (ws := [v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v163,v206,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245]) (consBan b0 (consBan b1 (consBan b2 (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b10 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b152 (consBan b153 (consBan b154 (consBan b155 (consBan b156 (consBan b157 (consBan b158 (consBan b159 (consBan b160 (consBan b161 (consBan b162 (consBan b163 (consBan b164 (consBan b165 (consBan b166 (consBan b167 (consBan b168 (consBan b169 (consBan b212 (consBan b214 (consBan b215 (consBan b216 (consBan b217 (consBan b218 (consBan b219 (consBan b220 (consBan b221 (consBan b222 (consBan b223 (consBan b224 (consBan b225 (consBan b226 (consBan b227 (consBan b228 (consBan b229 (consBan b230 (consBan b231 (consBan b232 (consBan b233 (consBan b234 (consBan b235 (consBan b236 (consBan b237 (consBan b238 (consBan b239 (consBan b240 (consBan b241 (consBan b242 (consBan b243 (consBan b244 (consBan b245 (consBan b246 (consBan b247 (consBan b248 (consBan b249 (consBan b250 (consBan b251 (consBan b252 (nilBan 26 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b254 : Ban 26 7 v1 := viaPerm map31_2 map31_2 b253 (by decide +kernel) (by decide +kernel)
theorem b255 : Ban 26 6 v247 := viaPerm map31_2 map31_2 b212 (by decide +kernel) (by decide +kernel)
theorem b256 : Ban 26 6 v248 := smallByCut p31_30 w3
theorem b257 : Ban 26 6 v249 := smallByCut p31_29 w3
theorem b258 : Ban 26 6 v250 := smallByCut p31_29 w3
theorem b259 : Ban 26 6 v251 := smallByCut p31_30 w3
theorem b260 : Ban 26 6 v252 := smallByCut p31_30 w3
theorem b261 : Ban 26 6 v253 := smallByCut p31_29 w3
theorem b262 : Ban 26 6 v254 := smallByCut p31_29 w3
theorem b263 : Ban 26 6 v255 := smallByCut p31_29 w3
theorem b264 : Ban 26 6 v256 := checkedSmall
theorem b265 : Ban 26 6 v257 := smallByCut p31_30 w3
theorem b266 : Ban 26 6 v258 := checkedSmall
theorem b267 : Ban 26 6 v259 := smallByCut p31_30 w3
theorem b268 : Ban 26 6 v260 := checkedSmall
theorem b269 : Ban 26 6 v261 := smallByCut p31_30 w3
theorem b270 : Ban 26 6 v262 := checkedSmall
theorem b271 : Ban 26 6 v263 := smallByCut p31_30 w3
theorem b272 : Ban 26 6 v264 := checkedSmall
theorem b273 : Ban 26 6 v265 := smallByCut p31_30 w3
theorem b274 : Ban 26 6 v266 := checkedSmall
theorem b275 : Ban 26 6 v267 := smallByCut p31_30 w3
theorem b276 : Ban 26 6 v268 := smallByCut p31_29 w3
theorem b277 : Ban 26 6 v269 := checkedSmall
theorem b278 : Ban 26 6 v270 := smallByCut p31_29 w3
theorem b279 : Ban 26 6 v271 := checkedSmall
theorem b280 : Ban 26 6 v272 := smallByCut p31_29 w3
theorem b281 : Ban 26 6 v273 := checkedSmall
theorem b282 : Ban 26 6 v274 := smallByCut p31_29 w3
theorem b283 : Ban 26 6 v275 := checkedSmall
theorem b284 : Ban 26 6 v276 := smallByCut p31_29 w3
theorem b285 : Ban 26 6 v277 := checkedSmall
theorem b286 : Ban 26 6 v278 := smallByCut p31_29 w3
theorem b287 : Ban 26 6 v279 := checkedSmall
theorem b288 : Ban 26 6 v280 := smallByCut p31_27 w3
theorem b289 : Ban 26 6 v281 := checkedSmall
theorem b290 : Ban 26 6 v282 := checkedSmall
theorem b291 : Ban 26 6 v283 := checkedSmall
theorem b292 : Ban 26 6 v284 := smallByCut p31_539 w6
theorem b293 : Ban 26 6 v285 := checkedSmall
theorem b294 : Ban 26 6 v286 := smallByCut p31_27 w3
theorem b295 : Ban 26 6 v287 := checkedSmall
theorem b296 : Ban 26 5 v289 := smallByCut p31_30 w3
theorem b297 : Ban 26 5 v290 := smallByCut p31_29 w3
theorem b298 : Ban 26 5 v291 := smallByCut p31_29 w3
theorem b299 : Ban 26 5 v292 := smallByCut p31_30 w3
theorem b300 : Ban 26 5 v293 := smallByCut p31_29 w3
theorem b301 : Ban 26 5 v294 := smallByCut p31_30 w3
theorem b302 : Ban 26 5 v295 := smallByCut p31_30 w3
theorem b303 : Ban 26 5 v296 := smallByCut p31_29 w3
theorem b304 : Ban 26 5 v297 := smallByCut p31_27 w3
theorem b305 : Ban 26 5 v298 := smallByCut p31_539 w6
theorem b306 : Ban 26 5 v299 := smallByCut p31_539 w6
theorem b307 : Ban 26 5 v300 := smallByCut p31_27 w3
theorem b308 : Ban 26 5 v301 := checkedSmall
theorem b309 : Ban 26 5 v302 := checkedSmall
theorem b310 : Ban 26 5 v303 := smallByCut p31_15 w3
theorem b311 : Ban 26 5 v304 := checkedSmall
theorem b312 : Ban 26 5 v305 := checkedSmall
theorem b313 : Ban 26 5 v306 := smallByCut p31_15 w3
theorem b314 : Ban 26 5 v307 := checkedSmall
theorem b315 : Ban 26 5 v308 := checkedSmall
theorem b316 : Ban 26 5 v309 := checkedSmall
theorem b317 : Ban 26 5 v310 := checkedSmall
theorem b318 : Ban 26 5 v311 := checkedSmall
theorem b319 : Ban 26 5 v312 := checkedSmall
theorem b320 : Ban 26 5 v313 := checkedSmall
theorem b321 : Ban 26 5 v314 := checkedSmall
theorem b322 : Ban 26 5 v315 := checkedSmall
theorem b323 : Ban 26 5 v316 := checkedSmall
theorem b324 : Ban 26 5 v317 := checkedSmall
theorem b325 : Ban 26 5 v318 := checkedSmall
theorem b326 : Ban 26 5 v319 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b327 : Ban 26 6 v288 := viaBranch (ws := [v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v319]) (consBan b296 (consBan b297 (consBan b298 (consBan b299 (consBan b300 (consBan b301 (consBan b302 (consBan b303 (consBan b304 (consBan b305 (consBan b306 (consBan b307 (consBan b308 (consBan b309 (consBan b310 (consBan b311 (consBan b312 (consBan b313 (consBan b314 (consBan b315 (consBan b316 (consBan b317 (consBan b318 (consBan b319 (consBan b320 (consBan b321 (consBan b322 (consBan b323 (consBan b324 (consBan b325 (consBan b326 (nilBan 26 5)))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b328 : Ban 26 6 v320 := checkedSmall
theorem b329 : Ban 26 6 v321 := smallByCut p31_1047 w2
theorem b330 : Ban 26 6 v322 := checkedSmall
theorem b347 : Ban 12 5 v21 := bySubset w2
theorem b348 : Ban 12 5 v68 := bySubset w2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w4 : Wide 12 5 v68 := viaSub (ws := [v21,v68]) (consBan b347 (consBan b348 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b349 : Ban 26 6 v323 := smallByCut p31_1047 w4
theorem b350 : Ban 26 6 v324 := checkedSmall
theorem b351 : Ban 26 6 v302 := checkedSmall
theorem b352 : Ban 26 6 v325 := checkedSmall
theorem b353 : Ban 26 6 v326 := smallByCut p31_15 w3
theorem b354 : Ban 26 6 v327 := checkedSmall
theorem b355 : Ban 26 6 v328 := checkedSmall
theorem b356 : Ban 26 6 v329 := checkedSmall
theorem b357 : Ban 26 6 v330 := checkedSmall
theorem b358 : Ban 26 6 v331 := checkedSmall
theorem b359 : Ban 26 6 v332 := smallByCut p31_15 w3
theorem b360 : Ban 26 6 v333 := checkedSmall
theorem b361 : Ban 26 6 v334 := checkedSmall
theorem b362 : Ban 26 6 v335 := checkedSmall
theorem b363 : Ban 26 6 v336 := checkedSmall
theorem b364 : Ban 26 6 v337 := checkedSmall
theorem b365 : Ban 26 6 v338 := checkedSmall
theorem b366 : Ban 26 6 v339 := checkedSmall
theorem b367 : Ban 26 6 v340 := checkedSmall
theorem b368 : Ban 26 6 v341 := checkedSmall
theorem b369 : Ban 26 6 v342 := checkedSmall
theorem b370 : Ban 26 6 v343 := checkedSmall
theorem b371 : Ban 26 6 v344 := checkedSmall
theorem b372 : Ban 26 6 v345 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b373 : Ban 26 7 v246 := viaBranch (ws := [v247,v248,v249,v250,v251,v252,v253,v254,v255,v160,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v320,v321,v322,v323,v324,v302,v325,v326,v327,v328,v329,v330,v331,v332,v333,v334,v335,v336,v337,v338,v339,v340,v341,v342,v343,v344,v345]) (consBan b255 (consBan b256 (consBan b257 (consBan b258 (consBan b259 (consBan b260 (consBan b261 (consBan b262 (consBan b263 (consBan b167 (consBan b264 (consBan b265 (consBan b266 (consBan b267 (consBan b268 (consBan b269 (consBan b270 (consBan b271 (consBan b272 (consBan b273 (consBan b274 (consBan b275 (consBan b276 (consBan b277 (consBan b278 (consBan b279 (consBan b280 (consBan b281 (consBan b282 (consBan b283 (consBan b284 (consBan b285 (consBan b286 (consBan b287 (consBan b288 (consBan b289 (consBan b290 (consBan b291 (consBan b292 (consBan b293 (consBan b294 (consBan b295 (consBan b327 (consBan b328 (consBan b329 (consBan b330 (consBan b349 (consBan b350 (consBan b351 (consBan b352 (consBan b353 (consBan b354 (consBan b355 (consBan b356 (consBan b357 (consBan b358 (consBan b359 (consBan b360 (consBan b361 (consBan b362 (consBan b363 (consBan b364 (consBan b365 (consBan b366 (consBan b367 (consBan b368 (consBan b369 (consBan b370 (consBan b371 (consBan b372 (nilBan 26 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b374 : Ban 26 6 v347 := smallByCut p31_15 w3
theorem b375 : Ban 26 6 v348 := smallByCut p31_15 w3
theorem b376 : Ban 26 6 v349 := smallByCut p31_15 w3
theorem b377 : Ban 26 6 v350 := smallByCut p31_29 w3
theorem b378 : Ban 26 6 v351 := smallByCut p31_30 w3
theorem b379 : Ban 26 6 v352 := checkedSmall
theorem b380 : Ban 26 6 v353 := smallByCut p31_30 w3
theorem b381 : Ban 26 6 v354 := smallByCut p31_30 w3
theorem b382 : Ban 26 6 v355 := smallByCut p31_30 w3
theorem b383 : Ban 26 6 v356 := smallByCut p31_29 w3
theorem b384 : Ban 26 6 v357 := smallByCut p31_30 w3
theorem b385 : Ban 26 6 v358 := smallByCut p31_30 w3
theorem b386 : Ban 26 6 v359 := checkedSmall
theorem b387 : Ban 26 6 v360 := smallByCut p31_30 w3
theorem b388 : Ban 26 6 v361 := smallByCut p31_30 w3
theorem b389 : Ban 26 6 v362 := smallByCut p31_30 w3
theorem b390 : Ban 26 6 v363 := smallByCut p31_27 w3
theorem b391 : Ban 26 6 v364 := smallByCut p31_30 w3
theorem b392 : Ban 26 6 v365 := smallByCut p31_30 w3
theorem b393 : Ban 26 6 v366 := smallByCut p31_30 w3
theorem b394 : Ban 26 6 v367 := smallByCut p31_1047 w2
theorem b395 : Ban 26 6 v368 := smallByCut p31_30 w3
theorem b396 : Ban 26 6 v369 := smallByCut p31_30 w3
theorem b397 : Ban 26 6 v370 := smallByCut p31_30 w3
theorem b398 : Ban 26 6 v371 := checkedSmall
theorem b399 : Ban 26 6 v372 := smallByCut p31_30 w3
theorem b400 : Ban 26 6 v373 := smallByCut p31_30 w3
theorem b401 : Ban 26 6 v374 := checkedSmall
theorem b402 : Ban 26 6 v375 := smallByCut p31_30 w3
theorem b403 : Ban 26 6 v376 := smallByCut p31_30 w3
theorem b404 : Ban 26 6 v377 := smallByCut p31_30 w3
theorem b405 : Ban 26 6 v378 := smallByCut p31_30 w3
theorem b406 : Ban 26 6 v379 := smallByCut p31_30 w3
theorem b407 : Ban 26 6 v380 := smallByCut p31_30 w3
theorem b408 : Ban 26 6 v381 := smallByCut p31_30 w3
theorem b409 : Ban 26 6 v382 := smallByCut p31_30 w3
theorem b410 : Ban 26 6 v383 := smallByCut p31_30 w3
theorem b411 : Ban 26 6 v384 := smallByCut p31_30 w3
theorem b412 : Ban 26 6 v385 := smallByCut p31_30 w3
theorem b413 : Ban 10 4 v388 := checkedSmall
theorem b414 : Ban 10 4 v389 := checkedSmall
theorem b415 : Ban 10 4 v390 := checkedSmall
theorem b416 : Ban 10 4 v391 := checkedSmall
theorem b437 : Ban 10 4 v412 := checkedSmall
theorem b438 : Ban 10 4 v413 := checkedSmall
theorem b439 : Ban 10 4 v414 := checkedSmall
theorem b440 : Ban 10 4 v415 := checkedSmall
theorem b441 : Ban 10 4 v416 := checkedSmall
theorem b442 : Ban 10 4 v417 := checkedSmall
theorem b443 : Ban 10 4 v418 := checkedSmall
theorem b444 : Ban 10 4 v419 := checkedSmall
theorem b445 : Ban 10 4 v420 := checkedSmall
theorem b446 : Ban 10 4 v421 := checkedSmall
theorem b447 : Ban 10 4 v422 := checkedSmall
theorem b448 : Ban 10 4 v423 := checkedSmall
theorem b449 : Ban 10 4 v424 := checkedSmall
theorem b450 : Ban 10 3 v427 := checkedSmall
theorem b451 : Ban 10 3 v428 := checkedSmall
theorem b452 : Ban 10 3 v429 := checkedSmall
theorem b453 : Ban 10 3 v430 := checkedSmall
theorem b454 : Ban 10 3 v431 := checkedSmall
theorem b455 : Ban 10 3 v432 := checkedSmall
theorem b456 : Ban 10 3 v433 := checkedSmall
theorem b457 : Ban 10 3 v434 := checkedSmall
theorem b458 : Ban 10 3 v435 := checkedSmall
theorem b459 : Ban 10 3 v436 := checkedSmall
theorem b460 : Ban 10 3 v437 := checkedSmall
theorem b461 : Ban 10 3 v438 := checkedSmall
theorem b462 : Ban 10 3 v439 := checkedSmall
theorem b463 : Ban 10 3 v440 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b464 : Ban 10 4 v426 := viaBranch (ws := [v427,v428,v400,v429,v430,v431,v432,v433,v434,v435,v436,v437,v438,v439,v440]) (consBan b450 (consBan b451 (consBan b423 (consBan b452 (consBan b453 (consBan b454 (consBan b455 (consBan b456 (consBan b457 (consBan b458 (consBan b459 (consBan b460 (consBan b461 (consBan b462 (consBan b463 (nilBan 10 3)))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b465 : Ban 10 4 v425 := viaPerm map15_2 map15_2 b464 (by decide +kernel) (by decide +kernel)
theorem b466 : Ban 10 4 v441 := checkedSmall
theorem b467 : Ban 10 4 v442 := checkedSmall
theorem b468 : Ban 10 4 v443 := checkedSmall
theorem b469 : Ban 10 4 v444 := checkedSmall
theorem b470 : Ban 10 4 v445 := checkedSmall
theorem b471 : Ban 10 4 v446 := checkedSmall
theorem b472 : Ban 10 4 v447 := checkedSmall
theorem b473 : Ban 10 4 v448 := checkedSmall
theorem b474 : Ban 10 4 v449 := checkedSmall
theorem b475 : Ban 10 4 v450 := checkedSmall
theorem b476 : Ban 10 4 v451 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b477 : Ban 10 5 v387 := viaBranch (ws := [v388,v389,v390,v391,v392,v412,v413,v414,v415,v416,v417,v418,v419,v420,v421,v422,v423,v424,v425,v441,v442,v443,v444,v445,v446,v447,v448,v449,v450,v451]) (consBan b413 (consBan b414 (consBan b415 (consBan b416 (consBan b436 (consBan b437 (consBan b438 (consBan b439 (consBan b440 (consBan b441 (consBan b442 (consBan b443 (consBan b444 (consBan b445 (consBan b446 (consBan b447 (consBan b448 (consBan b449 (consBan b465 (consBan b466 (consBan b467 (consBan b468 (consBan b469 (consBan b470 (consBan b471 (consBan b472 (consBan b473 (consBan b474 (consBan b475 (consBan b476 (nilBan 10 4))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w5 : Wide 10 5 v387 := viaSub (ws := [v387]) (consBan b477 (nilBan 10 5)) (by decide) (by decide +kernel)
theorem b478 : Ban 26 6 v386 := smallByCut p31_27 w5
theorem b479 : Ban 26 6 v452 := smallByCut p31_30 w3
theorem b480 : Ban 26 6 v453 := smallByCut p31_15 w3
theorem b481 : Ban 26 6 v454 := smallByCut p31_15 w3
theorem b482 : Ban 26 6 v455 := checkedSmall
theorem b483 : Ban 26 6 v456 := checkedSmall
theorem b484 : Ban 26 6 v457 := checkedSmall
theorem b485 : Ban 26 6 v458 := checkedSmall
theorem b486 : Ban 26 6 v459 := checkedSmall
theorem b487 : Ban 26 6 v460 := checkedSmall
theorem b488 : Ban 26 6 v461 := checkedSmall
theorem b489 : Ban 26 6 v462 := checkedSmall
theorem b490 : Ban 26 6 v463 := smallByCut p31_15 w3
theorem b491 : Ban 26 6 v464 := checkedSmall
theorem b492 : Ban 26 6 v465 := checkedSmall
theorem b493 : Ban 26 6 v466 := smallByCut p31_15 w3
theorem b494 : Ban 26 6 v467 := checkedSmall
theorem b495 : Ban 26 6 v468 := checkedSmall
theorem b496 : Ban 26 6 v469 := checkedSmall
theorem b497 : Ban 26 6 v470 := checkedSmall
theorem b498 : Ban 26 6 v471 := smallByCut p31_15 w3
theorem b499 : Ban 26 6 v472 := checkedSmall
theorem b500 : Ban 26 6 v473 := checkedSmall
theorem b501 : Ban 26 6 v474 := smallByCut p31_15 w3
theorem b502 : Ban 26 6 v475 := checkedSmall
theorem b503 : Ban 26 6 v476 := smallByCut p31_15 w3
theorem b504 : Ban 26 6 v477 := checkedSmall
theorem b505 : Ban 26 6 v478 := checkedSmall
theorem b506 : Ban 26 6 v479 := checkedSmall
theorem b507 : Ban 26 6 v480 := smallByCut p31_15 w3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b508 : Ban 26 7 v346 := viaBranch (ws := [v347,v348,v349,v350,v351,v352,v353,v354,v355,v356,v357,v155,v358,v359,v360,v361,v362,v363,v364,v365,v366,v367,v368,v369,v370,v371,v372,v373,v374,v375,v376,v265,v377,v378,v218,v379,v380,v381,v382,v383,v384,v385,v386,v452,v453,v454,v455,v456,v457,v458,v459,v460,v461,v462,v463,v464,v465,v466,v467,v468,v469,v470,v471,v472,v473,v474,v475,v476,v477,v478,v479,v480]) (consBan b374 (consBan b375 (consBan b376 (consBan b377 (consBan b378 (consBan b379 (consBan b380 (consBan b381 (consBan b382 (consBan b383 (consBan b384 (consBan b162 (consBan b385 (consBan b386 (consBan b387 (consBan b388 (consBan b389 (consBan b390 (consBan b391 (consBan b392 (consBan b393 (consBan b394 (consBan b395 (consBan b396 (consBan b397 (consBan b398 (consBan b399 (consBan b400 (consBan b401 (consBan b402 (consBan b403 (consBan b273 (consBan b404 (consBan b405 (consBan b225 (consBan b406 (consBan b407 (consBan b408 (consBan b409 (consBan b410 (consBan b411 (consBan b412 (consBan b478 (consBan b479 (consBan b480 (consBan b481 (consBan b482 (consBan b483 (consBan b484 (consBan b485 (consBan b486 (consBan b487 (consBan b488 (consBan b489 (consBan b490 (consBan b491 (consBan b492 (consBan b493 (consBan b494 (consBan b495 (consBan b496 (consBan b497 (consBan b498 (consBan b499 (consBan b500 (consBan b501 (consBan b502 (consBan b503 (consBan b504 (consBan b505 (consBan b506 (consBan b507 (nilBan 26 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b509 : Ban 26 7 v267 := viaPerm map31_3 map31_4 b508 (by decide +kernel) (by decide +kernel)
theorem b510 : Ban 26 7 v255 := viaPerm map31_9 map31_18 b508 (by decide +kernel) (by decide +kernel)
theorem b511 : Ban 26 7 v481 := viaPerm map31_2 map31_2 b373 (by decide +kernel) (by decide +kernel)
theorem b512 : Ban 26 7 v4 := viaPerm map31_1 map31_1 b508 (by decide +kernel) (by decide +kernel)
theorem b513 : Ban 26 7 v15 := viaPerm map31_15 map31_20 b508 (by decide +kernel) (by decide +kernel)
theorem b514 : Ban 26 6 v482 := smallByCut p31_29 w3
theorem b515 : Ban 26 6 v483 := smallByCut p31_29 w3
theorem b516 : Ban 26 5 v484 := smallByCut p31_29 w3
theorem b517 : Ban 26 5 v485 := smallByCut p31_29 w3
theorem b518 : Ban 26 5 v486 := smallByCut p31_29 w3
theorem b519 : Ban 26 5 v487 := smallByCut p31_29 w3
theorem b520 : Ban 26 5 v488 := checkedSmall
theorem b521 : Ban 26 5 v489 := smallByCut p31_29 w3
theorem b522 : Ban 26 5 v490 := checkedSmall
theorem b523 : Ban 26 5 v491 := checkedSmall
theorem b524 : Ban 26 5 v492 := checkedSmall
theorem b525 : Ban 26 5 v493 := checkedSmall
theorem b526 : Ban 26 5 v494 := checkedSmall
theorem b527 : Ban 26 5 v495 := checkedSmall
theorem b528 : Ban 26 5 v496 := smallByCut p31_29 w3
theorem b529 : Ban 26 5 v497 := smallByCut p31_29 w3
theorem b530 : Ban 26 5 v498 := smallByCut p31_29 w3
theorem b531 : Ban 26 5 v246 := smallByCut p31_29 w3
theorem b532 : Ban 26 5 v267 := smallByCut p31_29 w3
theorem b533 : Ban 26 5 v499 := smallByCut p31_29 w3
theorem b534 : Ban 26 5 v500 := smallByCut p31_27 w3
theorem b535 : Ban 26 5 v501 := smallByCut p31_539 w6
theorem b536 : Ban 26 5 v502 := smallByCut p31_539 w6
theorem b537 : Ban 26 5 v503 := smallByCut p31_27 w3
theorem b538 : Ban 26 5 v288 := checkedSmall
theorem b539 : Ban 26 5 v504 := smallByCut p31_30 w3
theorem b540 : Ban 26 5 v505 := smallByCut p31_15 w3
theorem b541 : Ban 26 5 v506 := checkedSmall
theorem b542 : Ban 26 5 v507 := checkedSmall
theorem b543 : Ban 26 5 v508 := smallByCut p31_15 w3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b544 : Ban 26 6 v290 := viaBranch (ws := [v291,v484,v485,v486,v487,v488,v489,v490,v491,v492,v493,v494,v495,v496,v497,v498,v246,v267,v499,v500,v501,v502,v503,v288,v504,v292,v302,v505,v506,v507,v508]) (consBan b298 (consBan b516 (consBan b517 (consBan b518 (consBan b519 (consBan b520 (consBan b521 (consBan b522 (consBan b523 (consBan b524 (consBan b525 (consBan b526 (consBan b527 (consBan b528 (consBan b529 (consBan b530 (consBan b531 (consBan b532 (consBan b533 (consBan b534 (consBan b535 (consBan b536 (consBan b537 (consBan b538 (consBan b539 (consBan b299 (consBan b309 (consBan b540 (consBan b541 (consBan b542 (consBan b543 (nilBan 26 5)))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b545 : Ban 26 6 v509 := smallByCut p31_29 w3
theorem b546 : Ban 26 6 v291 := smallByCut p31_29 w3
theorem b547 : Ban 26 6 v510 := smallByCut p31_29 w3
theorem b548 : Ban 26 6 v511 := smallByCut p31_30 w3
theorem b549 : Ban 26 6 v512 := smallByCut p31_29 w3
theorem b550 : Ban 26 6 v513 := smallByCut p31_29 w3
theorem b551 : Ban 26 6 v296 := smallByCut p31_29 w3
theorem b552 : Ban 26 6 v514 := smallByCut p31_29 w3
theorem b553 : Ban 26 6 v515 := smallByCut p31_27 w3
theorem b554 : Ban 26 6 v516 := smallByCut p31_29 w3
theorem b555 : Ban 26 6 v517 := viaPerm map31_14 map31_14 b544 (by decide +kernel) (by decide +kernel)
theorem b556 : Ban 26 6 v518 := smallByCut p31_29 w3
theorem b557 : Ban 26 6 v519 := smallByCut p31_29 w3
theorem b558 : Ban 26 6 v520 := smallByCut p31_29 w3
theorem b559 : Ban 26 6 v521 := smallByCut p31_27 w3
theorem b560 : Ban 26 6 v522 := smallByCut p31_29 w3
theorem b561 : Ban 26 6 v523 := smallByCut p31_29 w3
theorem b588 : Ban 26 6 v525 := smallByCut p31_539 w6
theorem b589 : Ban 26 6 v524 := viaPerm map31_2 map31_2 b588 (by decide +kernel) (by decide +kernel)
theorem b590 : Ban 26 6 v552 := smallByCut p31_29 w3
theorem b591 : Ban 26 6 v553 := smallByCut p31_15 w3
theorem b592 : Ban 26 6 v554 := smallByCut p31_29 w3
theorem b593 : Ban 26 6 v555 := viaPerm map31_20 map31_15 b544 (by decide +kernel) (by decide +kernel)
theorem b594 : Ban 26 6 v556 := smallByCut p31_29 w3
theorem b595 : Ban 26 6 v557 := smallByCut p31_29 w3
theorem b596 : Ban 26 6 v558 := smallByCut p31_29 w3
theorem b597 : Ban 26 6 v559 := smallByCut p31_15 w3
theorem b598 : Ban 26 6 v560 := smallByCut p31_29 w3
theorem b599 : Ban 26 6 v561 := smallByCut p31_29 w3
theorem b600 : Ban 26 6 v562 := smallByCut p31_29 w3
theorem b601 : Ban 26 6 v563 := checkedSmall
theorem b602 : Ban 26 6 v564 := smallByCut p31_29 w3
theorem b603 : Ban 26 6 v565 := smallByCut p31_29 w3
theorem b604 : Ban 26 6 v566 := checkedSmall
theorem b605 : Ban 26 6 v567 := checkedSmall
theorem b606 : Ban 26 6 v568 := checkedSmall
theorem b607 : Ban 26 6 v569 := smallByCut p31_1047 w2
theorem b608 : Ban 26 6 v570 := smallByCut p31_1047 w2
theorem b609 : Ban 26 6 v571 := smallByCut p31_1047 w4
theorem b610 : Ban 26 6 v572 := checkedSmall
theorem b611 : Ban 26 6 v573 := checkedSmall
theorem b612 : Ban 26 6 v574 := checkedSmall
theorem b613 : Ban 26 6 v575 := checkedSmall
theorem b614 : Ban 26 6 v576 := smallByCut p31_29 w3
theorem b615 : Ban 26 6 v577 := smallByCut p31_29 w3
theorem b616 : Ban 26 6 v578 := smallByCut p31_29 w3
theorem b617 : Ban 26 6 v579 := smallByCut p31_29 w3
theorem b618 : Ban 26 6 v580 := checkedSmall
theorem b619 : Ban 26 6 v581 := smallByCut p31_29 w3
theorem b620 : Ban 26 6 v582 := smallByCut p31_1047 w2
theorem b621 : Ban 26 6 v583 := smallByCut p31_29 w3
theorem b622 : Ban 26 6 v584 := smallByCut p31_1047 w2
theorem b623 : Ban 26 6 v585 := smallByCut p31_29 w3
theorem b624 : Ban 26 6 v586 := smallByCut p31_29 w3
theorem b625 : Ban 26 6 v587 := smallByCut p31_29 w3
theorem b626 : Ban 26 6 v588 := smallByCut p31_29 w3
theorem b627 : Ban 26 6 v589 := smallByCut p31_29 w3
theorem b628 : Ban 26 6 v590 := checkedSmall
theorem b629 : Ban 26 6 v591 := smallByCut p31_29 w3
theorem b630 : Ban 26 6 v592 := smallByCut p31_1047 w2
theorem b631 : Ban 26 6 v593 := smallByCut p31_1047 w2
theorem b632 : Ban 26 6 v594 := smallByCut p31_1047 w4
theorem b633 : Ban 26 6 v595 := checkedSmall
theorem b634 : Ban 26 6 v596 := checkedSmall
theorem b635 : Ban 26 6 v597 := checkedSmall
theorem b636 : Ban 26 6 v598 := checkedSmall
theorem b637 : Ban 26 6 v599 := checkedSmall
theorem b638 : Ban 26 6 v600 := smallByCut p31_1047 w2
theorem b639 : Ban 26 6 v601 := smallByCut p31_1047 w2
theorem b640 : Ban 26 6 v602 := checkedSmall
theorem b641 : Ban 26 6 v603 := smallByCut p31_1047 w4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b642 : Ban 26 7 v293 := viaBranch (ws := [v482,v483,v290,v509,v291,v510,v511,v512,v513,v296,v514,v515,v516,v517,v518,v519,v520,v521,v522,v523,v524,v552,v553,v554,v555,v556,v557,v558,v559,v560,v561,v562,v272,v563,v564,v565,v224,v566,v567,v568,v569,v570,v571,v572,v573,v574,v459,v575,v576,v577,v578,v579,v580,v581,v582,v583,v584,v585,v586,v587,v588,v589,v590,v591,v592,v593,v594,v595,v596,v597,v598,v599,v600,v601,v602,v603]) (consBan b514 (consBan b515 (consBan b544 (consBan b545 (consBan b546 (consBan b547 (consBan b548 (consBan b549 (consBan b550 (consBan b551 (consBan b552 (consBan b553 (consBan b554 (consBan b555 (consBan b556 (consBan b557 (consBan b558 (consBan b559 (consBan b560 (consBan b561 (consBan b589 (consBan b590 (consBan b591 (consBan b592 (consBan b593 (consBan b594 (consBan b595 (consBan b596 (consBan b597 (consBan b598 (consBan b599 (consBan b600 (consBan b280 (consBan b601 (consBan b602 (consBan b603 (consBan b231 (consBan b604 (consBan b605 (consBan b606 (consBan b607 (consBan b608 (consBan b609 (consBan b610 (consBan b611 (consBan b612 (consBan b486 (consBan b613 (consBan b614 (consBan b615 (consBan b616 (consBan b617 (consBan b618 (consBan b619 (consBan b620 (consBan b621 (consBan b622 (consBan b623 (consBan b624 (consBan b625 (consBan b626 (consBan b627 (consBan b628 (consBan b629 (consBan b630 (consBan b631 (consBan b632 (consBan b633 (consBan b634 (consBan b635 (consBan b636 (consBan b637 (consBan b638 (consBan b639 (consBan b640 (consBan b641 (nilBan 26 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b643 : Ban 26 7 v289 := viaPerm map31_6 map31_6 b642 (by decide +kernel) (by decide +kernel)
theorem b644 : Ban 26 6 v604 := smallByCut p31_30 w3
theorem b645 : Ban 26 6 v605 := smallByCut p31_30 w3
theorem b646 : Ban 26 6 v606 := checkedSmall
theorem b647 : Ban 26 6 v607 := checkedSmall
theorem b648 : Ban 26 6 v608 := smallByCut p31_30 w3
theorem b649 : Ban 26 6 v609 := checkedSmall
theorem b650 : Ban 26 6 v610 := smallByCut p31_1047 w2
theorem b651 : Ban 26 6 v611 := smallByCut p31_30 w3
theorem b652 : Ban 26 6 v612 := smallByCut p31_1047 w2
theorem b653 : Ban 26 6 v613 := smallByCut p31_30 w3
theorem b654 : Ban 26 6 v614 := smallByCut p31_30 w3
theorem b655 : Ban 26 6 v615 := smallByCut p31_30 w3
theorem b656 : Ban 26 6 v617 := smallByCut p31_539 w6
theorem b657 : Ban 26 6 v616 := viaPerm map31_8 map31_12 b656 (by decide +kernel) (by decide +kernel)
theorem b658 : Ban 26 6 v618 := checkedSmall
theorem b659 : Ban 26 6 v619 := viaPerm map31_8 map31_12 b588 (by decide +kernel) (by decide +kernel)
theorem b660 : Ban 26 6 v620 := smallByCut p31_30 w3
theorem b661 : Ban 26 6 v621 := checkedSmall
theorem b662 : Ban 26 6 v622 := checkedSmall
theorem b663 : Ban 26 6 v623 := checkedSmall
theorem b664 : Ban 26 6 v624 := checkedSmall
theorem b665 : Ban 26 6 v625 := checkedSmall
theorem b666 : Ban 26 6 v626 := checkedSmall
theorem b667 : Ban 26 6 v627 := smallByCut p31_1047 w2
theorem b668 : Ban 26 6 v628 := smallByCut p31_1047 w4
theorem b669 : Ban 26 6 v629 := checkedSmall
theorem b671 : Ban 26 6 v496 := smallByCut p31_1047 w2
theorem b673 : Ban 26 6 v498 := smallByCut p31_29 w3
theorem b675 : Ban 26 6 v632 := smallByCut p31_1047 w2
theorem b676 : Ban 26 6 v634 := smallByCut p31_1047 w2
theorem b677 : Ban 26 6 v635 := smallByCut p31_1047 w2
theorem b678 : Ban 26 6 v499 := smallByCut p31_29 w3
theorem b680 : Ban 26 6 v636 := smallByCut p31_1047 w4
theorem b681 : Ban 26 6 v639 := smallByCut p31_539 w8
theorem b682 : Ban 26 6 v638 := viaPerm map31_2 map31_2 b681 (by decide +kernel) (by decide +kernel)
theorem b683 : Ban 26 6 v641 := smallByCut p31_539 w6
theorem b684 : Ban 26 6 v640 := viaPerm map31_2 map31_2 b683 (by decide +kernel) (by decide +kernel)
theorem b711 : Ban 26 6 v643 := smallByCut p31_539 w8
theorem b712 : Ban 26 6 v642 := viaPerm map31_2 map31_2 b711 (by decide +kernel) (by decide +kernel)
theorem b713 : Ban 26 6 v669 := checkedSmall
theorem b714 : Ban 26 6 v670 := checkedSmall
theorem b715 : Ban 26 6 v671 := checkedSmall
theorem b716 : Ban 26 6 v672 := checkedSmall
theorem b717 : Ban 26 6 v673 := checkedSmall
theorem b718 : Ban 26 6 v674 := smallByCut p31_1047 w2
theorem b719 : Ban 26 6 v675 := smallByCut p31_1047 w2
theorem b720 : Ban 26 6 v676 := smallByCut p31_1047 w4
theorem b721 : Ban 26 6 v677 := checkedSmall
theorem b722 : Ban 26 6 v678 := smallByCut p31_1047 w2
theorem b723 : Ban 26 6 v679 := smallByCut p31_27 w3
theorem b724 : Ban 26 6 v680 := smallByCut p31_1047 w2
theorem b725 : Ban 26 6 v681 := smallByCut p31_1047 w2
theorem b726 : Ban 26 6 v682 := smallByCut p31_1047 w2
theorem b727 : Ban 26 6 v683 := smallByCut p31_1047 w2
theorem b728 : Ban 26 6 v684 := smallByCut p31_27 w3
theorem b729 : Ban 26 6 v685 := smallByCut p31_1047 w4
theorem b730 : Ban 26 6 v686 := checkedSmall
theorem b731 : Ban 26 6 v687 := checkedSmall
theorem b732 : Ban 26 6 v688 := checkedSmall
theorem b733 : Ban 26 6 v689 := checkedSmall
theorem b734 : Ban 26 6 v690 := checkedSmall
theorem b735 : Ban 26 6 v292 := smallByCut p31_30 w3
theorem b736 : Ban 26 6 v691 := smallByCut p31_1047 w2
theorem b737 : Ban 26 6 v692 := smallByCut p31_1047 w2
theorem b738 : Ban 26 6 v693 := checkedSmall
theorem b739 : Ban 26 6 v694 := smallByCut p31_1047 w4
theorem b740 : Ban 26 6 v695 := smallByCut p31_1047 w2
theorem b741 : Ban 26 6 v696 := smallByCut p31_1047 w2
theorem b742 : Ban 26 6 v697 := smallByCut p31_15 w3
theorem b743 : Ban 26 6 v698 := smallByCut p31_1047 w2
theorem b744 : Ban 26 6 v699 := smallByCut p31_1047 w2
theorem b745 : Ban 26 6 v700 := smallByCut p31_1047 w2
theorem b746 : Ban 26 6 v701 := viaPerm map31_1 map31_1 b681 (by decide +kernel) (by decide +kernel)
theorem b747 : Ban 26 6 v702 := viaPerm map31_1 map31_1 b711 (by decide +kernel) (by decide +kernel)
theorem b748 : Ban 26 6 v703 := viaPerm map31_1 map31_1 b683 (by decide +kernel) (by decide +kernel)
theorem b749 : Ban 26 6 v704 := checkedSmall
theorem b750 : Ban 26 6 v705 := smallByCut p31_15 w3
theorem b751 : Ban 26 6 v706 := smallByCut p31_1047 w4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b752 : Ban 26 7 v504 := viaBranch (ws := [v604,v260,v605,v606,v212,v607,v608,v609,v610,v611,v612,v613,v614,v615,v616,v618,v619,v620,v621,v383,v622,v623,v624,v625,v626,v570,v627,v628,v629,v496,v498,v632,v634,v321,v635,v499,v636,v638,v640,v642,v669,v670,v671,v672,v673,v674,v675,v676,v677,v678,v679,v680,v681,v682,v683,v684,v685,v639,v641,v643,v686,v687,v688,v689,v690,v292,v691,v692,v693,v694,v695,v696,v697,v698,v699,v700,v701,v702,v703,v704,v705,v706]) (consBan b644 (consBan b268 (consBan b645 (consBan b646 (consBan b219 (consBan b647 (consBan b648 (consBan b649 (consBan b650 (consBan b651 (consBan b652 (consBan b653 (consBan b654 (consBan b655 (consBan b657 (consBan b658 (consBan b659 (consBan b660 (consBan b661 (consBan b410 (consBan b662 (consBan b663 (consBan b664 (consBan b665 (consBan b666 (consBan b608 (consBan b667 (consBan b668 (consBan b669 (consBan b671 (consBan b673 (consBan b675 (consBan b676 (consBan b329 (consBan b677 (consBan b678 (consBan b680 (consBan b682 (consBan b684 (consBan b712 (consBan b713 (consBan b714 (consBan b715 (consBan b716 (consBan b717 (consBan b718 (consBan b719 (consBan b720 (consBan b721 (consBan b722 (consBan b723 (consBan b724 (consBan b725 (consBan b726 (consBan b727 (consBan b728 (consBan b729 (consBan b681 (consBan b683 (consBan b711 (consBan b730 (consBan b731 (consBan b732 (consBan b733 (consBan b734 (consBan b735 (consBan b736 (consBan b737 (consBan b738 (consBan b739 (consBan b740 (consBan b741 (consBan b742 (consBan b743 (consBan b744 (consBan b745 (consBan b746 (consBan b747 (consBan b748 (consBan b749 (consBan b750 (consBan b751 (nilBan 26 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b753 : Ban 26 7 v292 := smallByCut p31_1047 w2
theorem b754 : Ban 26 6 v707 := checkedSmall
theorem b755 : Ban 26 6 v708 := checkedSmall
theorem b756 : Ban 26 6 v709 := checkedSmall
theorem b757 : Ban 26 6 v710 := smallByCut p31_539 w6
theorem b758 : Ban 26 6 v711 := smallByCut p31_539 w8
theorem b759 : Ban 26 6 v712 := smallByCut p31_539 w6
theorem b760 : Ban 26 6 v713 := smallByCut p31_27 w3
theorem b761 : Ban 26 6 v714 := smallByCut p31_30 w3
theorem b762 : Ban 26 6 v715 := smallByCut p31_539 w6
theorem b763 : Ban 26 6 v716 := checkedSmall
theorem b764 : Ban 26 6 v717 := smallByCut p31_539 w6
theorem b765 : Ban 26 6 v718 := smallByCut p31_30 w3
theorem b766 : Ban 26 6 v719 := smallByCut p31_539 w6
theorem b767 : Ban 26 6 v720 := smallByCut p31_539 w6
theorem b768 : Ban 26 6 v721 := smallByCut p31_539 w6
theorem b769 : Ban 26 6 v722 := checkedSmall
theorem b770 : Ban 26 6 v723 := checkedSmall
theorem b771 : Ban 26 6 v724 := checkedSmall
theorem b772 : Ban 26 6 v725 := checkedSmall
theorem b773 : Ban 26 6 v726 := checkedSmall
theorem b774 : Ban 26 6 v727 := checkedSmall
theorem b775 : Ban 26 6 v728 := smallByCut p31_539 w8
theorem b776 : Ban 26 6 v729 := smallByCut p31_27 w3
theorem b777 : Ban 26 6 v730 := smallByCut p31_539 w6
theorem b778 : Ban 26 6 v731 := smallByCut p31_539 w8
theorem b779 : Ban 26 6 v732 := smallByCut p31_539 w6
theorem b780 : Ban 26 6 v733 := smallByCut p31_27 w3
theorem b781 : Ban 26 6 v734 := smallByCut p31_539 w6
theorem b782 : Ban 26 6 v735 := checkedSmall
theorem b783 : Ban 26 6 v736 := smallByCut p31_539 w6
theorem b784 : Ban 26 6 v737 := smallByCut p31_29 w3
theorem b785 : Ban 26 6 v738 := smallByCut p31_539 w6
theorem b786 : Ban 26 6 v739 := smallByCut p31_539 w6
theorem b787 : Ban 26 6 v740 := smallByCut p31_539 w6
theorem b788 : Ban 26 6 v741 := checkedSmall
theorem b789 : Ban 26 6 v742 := checkedSmall
theorem b790 : Ban 26 6 v743 := checkedSmall
theorem b791 : Ban 26 6 v744 := checkedSmall
theorem b792 : Ban 26 6 v745 := checkedSmall
theorem b793 : Ban 26 6 v746 := checkedSmall
theorem b794 : Ban 26 6 v747 := checkedSmall
theorem b796 : Ban 26 6 v748 := smallByCut p31_1047 w2
theorem b797 : Ban 26 6 v749 := smallByCut p31_539 w6
theorem b798 : Ban 26 6 v750 := smallByCut p31_27 w3
theorem b799 : Ban 26 6 v751 := smallByCut p31_27 w3
theorem solidb144 : Wide 12 5 v141 := solid b144
theorem b830 : Ban 26 6 v752 := smallByCut p31_1047 solidb144
theorem b831 : Ban 26 6 v783 := smallByCut p31_27 w3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w10 : Wide 12 5 v123 := viaSub (ws := [v82,v123]) (consBan b103 (consBan b126 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b832 : Ban 26 6 v785 := smallByCut p31_1047 w10
theorem b833 : Ban 26 6 v784 := viaPerm map31_12 map31_8 b832 (by decide +kernel) (by decide +kernel)
theorem b834 : Ban 26 6 v786 := smallByCut p31_27 w3
theorem b835 : Ban 26 6 v787 := smallByCut p31_539 w8
theorem b836 : Ban 26 6 v788 := smallByCut p31_27 w3
theorem b837 : Ban 26 6 v789 := smallByCut p31_539 w6
theorem b838 : Ban 26 6 v790 := smallByCut p31_27 w3
theorem b839 : Ban 26 6 v791 := smallByCut p31_539 w8
theorem b840 : Ban 26 6 v792 := smallByCut p31_539 w6
theorem b842 : Ban 26 6 v793 := smallByCut p31_27 w3
theorem b843 : Ban 26 6 v794 := smallByCut p31_15 w3
theorem b844 : Ban 26 6 v795 := smallByCut p31_539 w6
theorem b845 : Ban 26 6 v796 := checkedSmall
theorem b846 : Ban 26 6 v797 := smallByCut p31_539 w6
theorem b847 : Ban 26 6 v798 := smallByCut p31_539 w6
theorem b848 : Ban 26 6 v799 := smallByCut p31_539 w6
theorem b849 : Ban 26 6 v800 := smallByCut p31_15 w3
theorem b850 : Ban 26 6 v801 := smallByCut p31_539 w6
theorem b851 : Ban 26 6 v802 := checkedSmall
theorem b852 : Ban 26 6 v803 := checkedSmall
theorem b853 : Ban 26 6 v804 := checkedSmall
theorem b854 : Ban 26 6 v805 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b855 : Ban 26 7 v525 := viaBranch (ws := [v707,v337,v708,v709,v236,v237,v710,v711,v712,v713,v714,v715,v716,v717,v718,v719,v720,v721,v722,v677,v723,v724,v725,v726,v470,v727,v728,v729,v730,v731,v732,v733,v519,v734,v735,v736,v737,v738,v739,v740,v595,v741,v742,v743,v744,v745,v746,v747,v748,v617,v749,v750,v751,v752,v783,v784,v786,v787,v788,v789,v790,v791,v792,v793,v794,v795,v796,v797,v798,v799,v800,v801,v802,v803,v804,v805]) (consBan b754 (consBan b364 (consBan b755 (consBan b756 (consBan b243 (consBan b244 (consBan b757 (consBan b758 (consBan b759 (consBan b760 (consBan b761 (consBan b762 (consBan b763 (consBan b764 (consBan b765 (consBan b766 (consBan b767 (consBan b768 (consBan b769 (consBan b721 (consBan b770 (consBan b771 (consBan b772 (consBan b773 (consBan b497 (consBan b774 (consBan b775 (consBan b776 (consBan b777 (consBan b778 (consBan b779 (consBan b780 (consBan b557 (consBan b781 (consBan b782 (consBan b783 (consBan b784 (consBan b785 (consBan b786 (consBan b787 (consBan b633 (consBan b788 (consBan b789 (consBan b790 (consBan b791 (consBan b792 (consBan b793 (consBan b794 (consBan b796 (consBan b656 (consBan b797 (consBan b798 (consBan b799 (consBan b830 (consBan b831 (consBan b833 (consBan b834 (consBan b835 (consBan b836 (consBan b837 (consBan b838 (consBan b839 (consBan b840 (consBan b842 (consBan b843 (consBan b844 (consBan b845 (consBan b846 (consBan b847 (consBan b848 (consBan b849 (consBan b850 (consBan b851 (consBan b852 (consBan b853 (consBan b854 (nilBan 26 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b856 : Ban 26 7 v619 := viaPerm map31_8 map31_12 b855 (by decide +kernel) (by decide +kernel)
theorem b857 : Ban 26 7 v348 := viaPerm map31_1 map31_1 b253 (by decide +kernel) (by decide +kernel)
theorem b858 : Ban 26 7 v374 := viaPerm map31_4 map31_3 b373 (by decide +kernel) (by decide +kernel)
theorem b859 : Ban 26 7 v806 := viaPerm map31_21 map31_21 b508 (by decide +kernel) (by decide +kernel)
theorem b860 : Ban 26 7 v807 := viaPerm map31_6 map31_6 b253 (by decide +kernel) (by decide +kernel)
theorem b861 : Ban 26 7 v808 := viaPerm map31_8 map31_12 b373 (by decide +kernel) (by decide +kernel)
theorem b862 : Ban 26 7 v809 := viaPerm map31_7 map31_7 b508 (by decide +kernel) (by decide +kernel)
theorem b863 : Ban 26 7 v810 := viaPerm map31_13 map31_10 b508 (by decide +kernel) (by decide +kernel)
theorem b864 : Ban 26 7 v811 := viaPerm map31_6 map31_6 b752 (by decide +kernel) (by decide +kernel)
theorem b865 : Ban 26 7 v296 := smallByCut p31_1047 w2
theorem b866 : Ban 26 7 v524 := viaPerm map31_2 map31_2 b855 (by decide +kernel) (by decide +kernel)
theorem b867 : Ban 26 7 v812 := viaPerm map31_7 map31_7 b253 (by decide +kernel) (by decide +kernel)
theorem b868 : Ban 26 7 v813 := viaPerm map31_10 map31_13 b373 (by decide +kernel) (by decide +kernel)
theorem b869 : Ban 26 7 v814 := viaPerm map31_6 map31_6 b508 (by decide +kernel) (by decide +kernel)
theorem b870 : Ban 26 7 v815 := viaPerm map31_19 map31_11 b508 (by decide +kernel) (by decide +kernel)
theorem b871 : Ban 26 7 v793 := viaPerm map31_2 map31_2 b642 (by decide +kernel) (by decide +kernel)
theorem b872 : Ban 26 7 v748 := viaPerm map31_12 map31_8 b752 (by decide +kernel) (by decide +kernel)
theorem b873 : Ban 26 7 v816 := smallByCut p31_1047 w2
theorem b874 : Ban 26 7 v817 := viaPerm map31_13 map31_10 b253 (by decide +kernel) (by decide +kernel)
theorem b875 : Ban 26 7 v818 := viaPerm map31_16 map31_16 b373 (by decide +kernel) (by decide +kernel)
theorem b876 : Ban 26 7 v819 := viaPerm map31_12 map31_8 b508 (by decide +kernel) (by decide +kernel)
theorem b877 : Ban 26 7 v820 := viaPerm map31_18 map31_9 b508 (by decide +kernel) (by decide +kernel)
theorem b878 : Ban 26 7 v821 := viaPerm map31_4 map31_3 b642 (by decide +kernel) (by decide +kernel)
theorem b879 : Ban 26 7 v822 := viaPerm map31_18 map31_9 b752 (by decide +kernel) (by decide +kernel)
theorem b880 : Ban 26 7 v823 := viaPerm map31_1 map31_1 b855 (by decide +kernel) (by decide +kernel)
theorem b881 : Ban 26 7 v824 := smallByCut p31_1047 w2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b882 : Ban 26 8 v0 := viaBranch (ws := [v1,v246,v267,v255,v2,v481,v4,v15,v289,v504,v292,v619,v348,v374,v346,v806,v807,v808,v809,v810,v293,v811,v296,v524,v812,v813,v814,v815,v793,v748,v816,v525,v817,v818,v819,v820,v821,v822,v823,v824]) (consBan b254 (consBan b373 (consBan b509 (consBan b510 (consBan b253 (consBan b511 (consBan b512 (consBan b513 (consBan b643 (consBan b752 (consBan b753 (consBan b856 (consBan b857 (consBan b858 (consBan b508 (consBan b859 (consBan b860 (consBan b861 (consBan b862 (consBan b863 (consBan b642 (consBan b864 (consBan b865 (consBan b866 (consBan b867 (consBan b868 (consBan b869 (consBan b870 (consBan b871 (consBan b872 (consBan b873 (consBan b855 (consBan b874 (consBan b875 (consBan b876 (consBan b877 (consBan b878 (consBan b879 (consBan b880 (consBan b881 (nilBan 26 7))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem verifiedPin : Wide 26 8 v0 := widen (by decide +kernel) b882
end PEqualNP.Outside.L_meta_12098.Support

namespace PEqualNP.Outside.L_meta_12098.Data
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12098.Support
def target (x : Fin 6 → Bool) := Nat.testBit (4269866496 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def posBits : ℕ := 0x2979d71c71b69a6996595d75d73ce38e34d34b2cb
def negBits : ℕ := 0x95956143136122984495954c71cc28630914a243
def sample (bank : ℕ) (i : Fin 27) (j : Fin 6) := bank.testBit (6*i.val+j.val)
def inputs : List ℕ := [0x2886f0dd11fe3f,0x10b1762a1e3fc7,0x1b01bb43e03ff8,0x255a0db7ffc3ff,0x1eedc003fffc00,0x4000000]
def seeds : List Wire := [(false,0x2886f0dd11fe3f),(false,0x10b1762a1e3fc7),(false,0x1b01bb43e03ff8),(false,0x255a0db7ffc3ff),(false,0x1eedc003fffc00),(false,0x4000000)]
set_option maxHeartbeats 10000000 in
theorem listed : ∀ i : Fin 27, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (27+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 27, target (sample posBits i)=true ∧ target (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 27, ∀ b∈inputs, b.testBit i.val≠b.testBit (27+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 27 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 6 C=target) :
    ∃ k≤C.gates.countP counted, Live 27 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 6 → Bool) : C.eval (List.ofFn x)=target x := congrFun eq x
  have good : Good 27 out.2 := by
    intro i hi same
    let j : Fin 27 := ⟨i,hi⟩
    have diff : read i out=read (27+i) out := by
      change (out.1 != out.2.testBit i) = (out.1 != out.2.testBit (27+i))
      rw [same]
    have p := ev i;have n := ev (27+i)
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
def restrictRows : Projection 27 26 := pick (List.range 26) (by decide) (by decide) (by decide)
set_option maxHeartbeats 8000000 in
theorem core_floor : Wide 26 8 restricted := verifiedPin
theorem six_floor : Ban 27 9 inputs := viaCut restrictRows core_floor (by decide) (by decide +kernel) (by decide +kernel)
def witness : Circuit := ⟨[⟨.and,[0,1]⟩, ⟨.or,[0,1]⟩, ⟨.and,[7,3]⟩, ⟨.and,[3,5]⟩, ⟨.or,[9,4]⟩, ⟨.and,[2,10]⟩, ⟨.or,[8,11]⟩, ⟨.or,[2,10]⟩, ⟨.and,[3,13]⟩, ⟨.or,[6,14]⟩, ⟨.and,[12,15]⟩],16⟩
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
end PEqualNP.Outside.L_meta_12098.Data

theorem PEqualNP.Outside.L_meta_12098 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269866496 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269866496 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_12098.Data.mono_enough
