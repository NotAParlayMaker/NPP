import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16921.Support

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

def t0 := 0x304582702c429c73e1bc1f3
def t1 := 0x1089128816650d624ce64f99c
def t2 := 0x460228218082b1838f1870e1f
def t3 := 0xb80d805c03503e03f01f80fe0
def t4 := 0xef500077e8003ffc001fff000
def t5 := 0xffefff0000003fffffe000000
def v0 := [t0,t1,t2,t3,t4,t5]
def t6 := 0x801024000040e00c190
def v1 := [t6,t0,t1,t2,t3,t4,t5]
def t7 := 0x14f
def t8 := 0x4b3
def t9 := 0xa3c
def v2 := [t7,t8,t9]
def p63_13 : Projection 50 6 := pick [0,1,5,6,9,10] rfl (by decide +kernel) (by decide)
def t10 := 0x10b9578a766d4ffe7fe7ff9ff
def v3 := [t0,t1,t10,t2,t3,t4,t5]
def t11 := 0x62ce4539f793
def t12 := 0x10942d2c679fc
def t13 := 0xc14302b078e1f
def t14 := 0xea03d03f80fe0
def t15 := 0xfdf8003fff000
def v4 := [t11,t12,t13,t14,t15]
def t16 := 0x4240007190
def v5 := [t16,t11,t12,t13,t14,t15]
def t17 := 0x16bced7ffffff
def v6 := [t11,t12,t17,t13,t14,t15]
def t18 := 0x628c05398603
def v7 := [t18,t11,t12,t13,t14,t15]
def t19 := 0x1090092c6086c
def v8 := [t11,t19,t12,t13,t14,t15]
def t20 := 0x1018613
def v9 := [t20,t11,t12,t13,t14,t15]
def t21 := 0xc76fe6f3fff9f
def v10 := [t11,t12,t13,t21,t14,t15]
def t22 := 0x62ce44387180
def v11 := [t22,t11,t12,t13,t14,t15]
def t23 := 0xc14302a06080c
def v12 := [t11,t12,t23,t13,t14,t15]
def t24 := 0x200c01380780
def v13 := [t24,t11,t12,t13,t14,t15]
def t25 := 0xee2ff47f9fff3
def v14 := [t11,t12,t13,t14,t25,t15]
def t26 := 0x42c24401f013
def v15 := [t26,t11,t12,t13,t14,t15]
def t27 := 0xe803102c00860
def v16 := [t11,t12,t13,t27,t14,t15]
def t28 := 0x42800139f000
def v17 := [t28,t11,t12,t13,t14]
def v18 := [t28,t11,t12,t13,t14,t15]
def t29 := 0xfffce47fff793
def v19 := [t11,t12,t13,t14,t15,t29]
def t30 := 0x204e44000793
def v20 := [t30,t11,t12,t13,t14]
def v21 := [t30,t11,t12,t13,t14,t15]
def t31 := 0xf9d0002c60000
def v22 := [t11,t12,t13,t14,t31,t15]
def t32 := 0x206081c
def v23 := [t32,t11,t12,t13,t14,t15]
def t33 := 0xd1d72fbc7ffff
def v24 := [t11,t12,t13,t33,t14,t15]
def t34 := 0x10942d0c071e0
def v25 := [t11,t34,t12,t13,t14,t15]
def t35 := 0xc143029018603
def v26 := [t11,t12,t35,t13,t14,t15]
def t36 := 0x2c009e0
def v27 := [t36,t11,t12,t13,t14,t15]
def t37 := 0xfa97fd3fe7ffc
def v28 := [t11,t12,t13,t14,t37,t15]
def t38 := 0x10942d006701c
def v29 := [t11,t38,t12,t13,t14,t15]
def t39 := 0xea03d01380600
def v30 := [t11,t12,t13,t39,t14,t15]
def t40 := 0x1090002c67000
def v31 := [t11,t40,t12,t13,t14,t15]
def t41 := 0xfdfc2d3fff9fc
def v32 := [t11,t12,t13,t14,t15,t41]
def t42 := 0x42d00009fc
def v33 := [t42,t11,t12,t13,t14,t15]
def t43 := 0xed68001398000
def v34 := [t11,t12,t13,t14,t43,t15]
def t44 := 0xc003003000e00
def v35 := [t11,t12,t44,t13,t14,t15]
def t45 := 0xeb43d2bff8fff
def v36 := [t11,t12,t13,t45,t15]
def v37 := [t11,t12,t13,t14,t45,t15]
def t46 := 0x14002807801f
def v38 := [t46,t11,t12,t13,t14,t15]
def t47 := 0x2a00d00f801e0
def v39 := [t11,t12,t47,t13,t15]
def v40 := [t11,t12,t47,t13,t14,t15]
def t48 := 0xc140003078000
def v41 := [t11,t12,t48,t13,t14,t15]
def t49 := 0xfdfb02bfffe1f
def v42 := [t11,t12,t13,t14,t49]
def v43 := [t11,t12,t13,t14,t15,t49]
def t50 := 0x3028000e1f
def v44 := [t50,t11,t12,t13,t14,t15]
def t51 := 0x3cb8000f87000
def v45 := [t11,t12,t51,t13,t14]
def v46 := [t11,t12,t51,t13,t14,t15]
def t52 := 0xe800003f80000
def v47 := [t11,t12,t13,t52,t14,t15]
def t53 := 0xfffbd03ffffe0
def v48 := [t11,t12,t13,t14,t15,t53]
def t54 := 0x203d00000fe0
def v49 := [t54,t11,t12,t13,t14,t15]
def t55 := 0x15f800007f000
def v50 := [t11,t12,t55,t13,t14,t15]
def v51 := [t16,t17,t13,t14,t15]
def v52 := [t16,t11,t17,t13,t14,t15]
def v53 := [t16,t12,t17,t13,t14,t15]
def v54 := [t18,t11,t17,t13,t14,t15]
def v55 := [t19,t12,t17,t13,t14,t15]
def v56 := [t12,t17,t13,t21,t14,t15]
def v57 := [t22,t12,t17,t13,t14,t15]
def v58 := [t12,t17,t13,t14,t25,t15]
def v59 := [t26,t12,t17,t13,t14,t15]
def v60 := [t28,t12,t17,t13,t14]
def v61 := [t28,t11,t12,t17,t13,t14]
def v62 := [t28,t12,t17,t13,t14,t15]
def v63 := [t30,t11,t12,t17,t13,t14]
def v64 := [t12,t17,t13,t14,t31,t15]
def v65 := [t11,t17,t13,t33,t14,t15]
def v66 := [t11,t34,t17,t13,t14,t15]
def t56 := 0x3078e1f
def v67 := [t56,t11,t12,t14,t15]
def v68 := [t56,t11,t12,t17,t14,t15]
def v69 := [t56,t11,t12,t13,t14,t15]
def t57 := 0xd7ffeffffffff
def v70 := [t11,t12,t13,t57,t14,t15]
def t58 := 0x16bced4f871e0
def v71 := [t11,t12,t58,t14,t15]
def v72 := [t11,t12,t58,t17,t14,t15]
def v73 := [t11,t12,t58,t13,t14,t15]
def t59 := 0xc143028000000
def v74 := [t11,t12,t59,t13,t14,t15]
def t60 := 0x200c03f80fe0
def v75 := [t60,t11,t12,t13,t15]
def v76 := [t60,t11,t12,t17,t13,t15]
def v77 := [t60,t11,t12,t13,t14,t15]
def t61 := 0xfebffd7ffffff
def v78 := [t11,t12,t13,t14,t15,t61]
def t62 := 0x14bc2d407f01f
def v79 := [t11,t12,t62,t13,t15]
def v80 := [t11,t12,t62,t17,t13,t15]
def v81 := [t11,t12,t62,t13,t14,t15]
def t63 := 0xe803100000000
def v82 := [t11,t12,t13,t63,t14,t15]
def t64 := 0x14b8003fff000
def v83 := [t11,t12,t64,t13,t14]
def v84 := [t11,t12,t64,t17,t13,t14]
def v85 := [t11,t12,t64,t13,t14,t15]
def t65 := 0xfffced7ffffff
def v86 := [t11,t12,t13,t14,t15,t65]
def t66 := 0x204ed4000fff
def v87 := [t66,t11,t12,t13,t14]
def v88 := [t66,t11,t12,t17,t13,t14]
def v89 := [t66,t11,t12,t13,t14,t15]
def t67 := 0xe940000000000
def v90 := [t11,t12,t13,t67,t14,t15]
def v91 := [t11,t12,t17,t13,t45,t15]
def v92 := [t11,t12,t17,t47,t13,t15]
def v93 := [t11,t12,t17,t13,t14,t49]
def v94 := [t11,t12,t17,t51,t13,t14]
def p63_55 : Projection 50 26 := pick [0,1,2,3,4,12,13,14,15,16,17,18,25,26,27,28,29,30,31,38,39,40,41,42,43,44] rfl (by decide +kernel) (by decide)
def t68 := 0x3045026008429c3301b0063
def v95 := [t68,t0,t1,t2,t3,t4,t5]
def t69 := 0x1381621bc1f3
def t70 := 0x40b32864f99c
def t71 := 0x10c0415870e1f
def t72 := 0x2e01a81f80fe0
def t73 := 0x3bf4001fff000
def v96 := [t69,t70,t71,t72,t73]
def t74 := 0x812000c190
def v97 := [t74,t69,t70,t71,t72,t73]
def t75 := 0x53b36a7ff9ff
def v98 := [t69,t70,t75,t71,t72,t73]
def t76 := 0x40320864380c
def v99 := [t69,t76,t70,t71,t72,t73]
def t77 := 0x1300421b0063
def v100 := [t77,t69,t70,t71,t72,t73]
def t78 := 0x4081c
def v101 := [t78,t69,t70,t71,t72,t73]
def t79 := 0x14cb73de7ff9f
def v102 := [t69,t70,t71,t79,t72,t73]
def t80 := 0x40b32860f180
def v103 := [t69,t80,t70,t71,t72,t73]
def t81 := 0x10c0415830603
def v104 := [t69,t70,t81,t71,t72,t73]
def t82 := 0x401200600980
def v105 := [t69,t82,t70,t71,t72,t73]
def t83 := 0x2e0bba9fcfffc
def v106 := [t69,t70,t71,t72,t83,t73]
def t84 := 0xa12804f01c
def v107 := [t84,t69,t70,t71,t72,t73]
def t85 := 0x2a00881980660
def v108 := [t69,t70,t71,t85,t72,t73]
def t86 := 0x64f000
def v109 := [t86,t69,t70,t71,t72]
def v110 := [t86,t69,t70,t71,t72,t73]
def t87 := 0x3fff329fff99c
def v111 := [t69,t70,t71,t72,t73,t87]
def t88 := 0x40b32800099c
def v112 := [t69,t88,t70,t71,t72]
def v113 := [t69,t88,t70,t71,t72,t73]
def t89 := 0x3bf40019b0000
def v114 := [t69,t70,t71,t72,t89,t73]
def t90 := 0x30013
def v115 := [t90,t69,t70,t71,t72,t73]
def t91 := 0x11f85779fcfff
def v116 := [t69,t70,t71,t91,t72,t73]
def t92 := 0x13816218c1e0
def v117 := [t92,t69,t70,t71,t72,t73]
def t93 := 0x10c0415840e0c
def v118 := [t69,t70,t93,t71,t72,t73]
def t94 := 0x1801e0
def v119 := [t94,t69,t70,t71,t72,t73]
def t95 := 0x2f39be3fbcff3
def v120 := [t69,t70,t71,t72,t95,t73]
def t96 := 0x13816203c013
def v121 := [t96,t69,t70,t71,t72,t73]
def t97 := 0x2e01a81e00e00
def v122 := [t69,t70,t71,t97,t72,t73]
def t98 := 0x1300001bc000
def v123 := [t98,t69,t70,t71,t72,t73]
def t99 := 0x3bfc163fff1f3
def v124 := [t69,t70,t71,t72,t73,t99]
def t100 := 0x81620001f3
def v125 := [t100,t69,t70,t71,t72,t73]
def t101 := 0x3ac4001e43000
def v126 := [t69,t70,t71,t72,t101,t73]
def t102 := 0x1800e00
def v127 := [t102,t69,t70,t71,t72,t73]
def t103 := 0x3ec1e95ff0fff
def v128 := [t69,t70,t71,t72,t73,t103]
def t104 := 0x10c041407001f
def v129 := [t69,t70,t104,t71,t72,t73]
def t105 := 0x2e01a807801e0
def v130 := [t69,t70,t71,t105,t72,t73]
def t106 := 0x10c0001870000
def v131 := [t69,t70,t106,t71,t72,t73]
def t107 := 0x3bf4415fffe1f
def v132 := [t69,t70,t71,t72,t107]
def v133 := [t69,t70,t71,t72,t73,t107]
def t108 := 0x414000e1f
def v134 := [t108,t69,t70,t71,t72,t73]
def t109 := 0x2b3400078f000
def v135 := [t69,t70,t71,t109,t72]
def v136 := [t69,t70,t71,t109,t72,t73]
def t110 := 0x2a00001f80000
def v137 := [t69,t70,t71,t110,t72,t73]
def t111 := 0x3ff5a81ffffe0
def v138 := [t69,t70,t71,t72,t73,t111]
def t112 := 0x401a80000fe0
def v139 := [t69,t112,t70,t71,t72,t73]
def t113 := 0x11f400007f000
def v140 := [t69,t70,t71,t113,t72,t73]
def v141 := [t77,t69,t75,t71,t72,t73]
def v142 := [t74,t77,t70,t71,t72,t73]
def v143 := [t77,t76,t71,t72,t73]
def v144 := [t77,t76,t70,t71,t72,t73]
def v145 := [t77,t69,t76,t71,t72,t73]
def v146 := [t86,t77,t69,t70,t71,t72]
def v147 := [t77,t69,t88,t70,t71,t72]
def t114 := 0x30003
def v148 := [t114,t69,t70,t71,t72,t73]
def t115 := 0x11f04579f0e7f
def v149 := [t69,t70,t71,t115,t72,t73]
def t116 := 0x130042180060
def v150 := [t116,t69,t70,t71,t72,t73]
def t117 := 0x10c0415840e1c
def v151 := [t69,t70,t117,t71,t72,t73]
def t118 := 0x180060
def v152 := [t118,t69,t70,t71,t72,t73]
def t119 := 0x2f31ac3fb0fe3
def v153 := [t69,t70,t71,t72,t119,t73]
def t120 := 0x130042030003
def v154 := [t120,t69,t70,t71,t72,t73]
def t121 := 0x2e01a81e00f80
def v155 := [t69,t70,t71,t121,t72,t73]
def t122 := 0x1300001b0000
def v156 := [t122,t69,t70,t71,t72,t73]
def t123 := 0x3bf4043fff063
def v157 := [t69,t70,t71,t72,t123]
def v158 := [t77,t69,t70,t71,t72,t123]
def v159 := [t69,t70,t71,t72,t73,t123]
def t124 := 0x42000063
def v160 := [t124,t69,t70,t71,t72,t73]
def t125 := 0x3ac4001e4f000
def v161 := [t69,t70,t71,t72,t125]
def v162 := [t77,t69,t70,t71,t72,t125]
def v163 := [t69,t70,t71,t72,t125,t73]
def v164 := [t77,t70,t71,t91,t72,t73]
def v165 := [t77,t92,t70,t71,t72,t73]
def v166 := [t94,t77,t70,t71,t72,t73]
def v167 := [t77,t70,t71,t97,t72,t73]
def v168 := [t77,t70,t71,t72,t73,t99]
def v169 := [t100,t77,t70,t71,t72,t73]
def v170 := [t77,t69,t70,t71,t72,t107]
def v171 := [t77,t69,t70,t71,t109,t72]
def p63_31 : Projection 50 25 := pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24] rfl (by decide +kernel) (by decide)
def t126 := 0x1089120806410d620c064380c
def v172 := [t0,t126,t1,t2,t3,t4,t5]
def t127 := 0x80030030013
def v173 := [t127,t0,t1,t2,t3,t4,t5]
def t128 := 0x1bc3fc
def t129 := 0x455c7f
def t130 := 0xa8af8f
def t131 := 0xf60ff0
def v174 := [t128,t129,t130,t131]
def p63_51 : Projection 50 12 := pick [12,13,14,15,25,26,27,38,39,40,41,42] rfl (by decide +kernel) (by decide)
def t132 := 0x46326da3f0aef39ffff9fcfff
def v175 := [t0,t1,t2,t132,t3,t4,t5]
def v176 := [t18,t12,t13,t21,t14,t15]
def v177 := [t20,t12,t21,t14,t15]
def v178 := [t20,t11,t12,t21,t14,t15]
def v179 := [t20,t12,t13,t21,t14,t15]
def v180 := [t22,t11,t12,t21,t14,t15]
def v181 := [t12,t23,t13,t21,t14,t15]
def v182 := [t28,t11,t12,t13,t21,t14]
def v183 := [t30,t11,t12,t13,t21,t14]
def t133 := 0x424206799c
def v184 := [t133,t11,t12,t13,t14,t15]
def t134 := 0x1090090c00060
def v185 := [t11,t134,t12,t13,t14,t15]
def t135 := 0xc76bc2d398603
def v186 := [t11,t12,t13,t135,t14,t15]
def v187 := [t11,t12,t13,t21,t45,t15]
def v188 := [t11,t12,t47,t13,t21,t15]
def v189 := [t11,t12,t13,t21,t14,t49]
def v190 := [t11,t12,t51,t13,t21,t14]
def t136 := 0xc203c03380f80
def v191 := [t11,t12,t13,t136,t14,t15]
def t137 := 0xef6ff6fffffff
def v192 := [t11,t12,t13,t14,t137,t15]
def t138 := 0x56c26c07f01f
def v193 := [t138,t11,t12,t13,t14,t15]
def t139 := 0x2800100c00060
def v194 := [t11,t12,t139,t13,t14,t15]
def t140 := 0xc5680033ff000
def v195 := [t11,t12,t13,t140,t14]
def v196 := [t11,t12,t13,t140,t21,t14]
def v197 := [t11,t12,t13,t140,t14,t15]
def t141 := 0xffffe6fffff9f
def v198 := [t11,t12,t13,t14,t15,t141]
def t142 := 0x207e6c000f9f
def v199 := [t142,t11,t12,t13,t14]
def v200 := [t142,t11,t12,t13,t21,t14]
def v201 := [t142,t11,t12,t13,t14,t15]
def t143 := 0x3890000c00000
def v202 := [t11,t12,t143,t13,t14,t15]
def t144 := 0x304582702c421c70e18c1e0
def v203 := [t144,t0,t1,t2,t3,t4,t5]
def t145 := 0x812000c180
def v204 := [t145,t69,t70,t71,t72,t73]
def t146 := 0x53b36a7cf9fc
def v205 := [t69,t70,t146,t71,t72,t73]
def t147 := 0x40320864381c
def v206 := [t69,t147,t70,t71,t72,t73]
def v207 := [t92,t70,t75,t71,t72,t73]
def v208 := [t86,t92,t69,t70,t71,t72]
def v209 := [t92,t69,t88,t70,t71,t72]
def v210 := [t90,t92,t70,t71,t72,t73]
def v211 := [t92,t69,t70,t91,t72,t73]
def t148 := 0x2f39be3f8cfe0
def v212 := [t69,t70,t71,t72,t148,t73]
def t149 := 0x13816200c000
def v213 := [t149,t69,t70,t71,t72,t73]
def t150 := 0x13000018c000
def v214 := [t150,t69,t70,t71,t72,t73]
def t151 := 0x3bfc163fff1e0
def v215 := [t69,t70,t71,t72,t73,t151]
def t152 := 0x81620001e0
def v216 := [t152,t69,t70,t71,t72,t73]
def t153 := 0x3ac4001e73000
def v217 := [t69,t70,t71,t72,t153,t73]
def v218 := [t92,t70,t93,t72,t73]
def v219 := [t92,t69,t70,t93,t72,t73]
def v220 := [t92,t70,t93,t71,t72,t73]
def v221 := [t92,t70,t71,t72,t95,t73]
def v222 := [t96,t92,t70,t71,t72,t73]
def v223 := [t92,t69,t70,t71,t72,t107]
def v224 := [t92,t69,t70,t71,t109,t72]
def t154 := 0x460228218082b1038c1840e0c
def v225 := [t0,t1,t154,t2,t3,t4,t5]
def t155 := 0x2007001801e0
def v226 := [t155,t0,t1,t2,t3,t4,t5]
def t156 := 0xb83dc5de737c7e9ff3ffbcff3
def v227 := [t0,t1,t2,t3,t156,t4,t5]
def t157 := 0x304582702c409c03e03c013
def v228 := [t157,t0,t1,t2,t3,t4,t5]
def t158 := 0xb80d805c03503c03801e00e00
def v229 := [t0,t1,t2,t158,t3,t4,t5]
def t159 := 0x1000026000029c0001bc000
def v230 := [t159,t0,t1,t2,t3,t4,t5]
def t160 := 0xef7045f7f82c7ffc73ffff1f3
def v231 := [t0,t1,t2,t3,t4,t160,t5]
def t161 := 0x11616239f1f3
def t162 := 0x8a0415c78e1f
def t163 := 0x244b32926799c
def t164 := 0x3601a81f80fe0
def t165 := 0x3ffc001fff000
def v232 := [t161,t162,t163,t164,t165]
def t166 := 0x18013
def v233 := [t166,t161,t162,t163,t164,t165]
def t167 := 0x9b6577ffffff
def v234 := [t161,t162,t167,t163,t164,t165]
def t168 := 0x1161623871e0
def v235 := [t168,t161,t162,t163,t164,t165]
def t169 := 0x8a0415c60e0c
def v236 := [t161,t169,t162,t163,t164,t165]
def t170 := 0x2120207190
def v237 := [t170,t161,t162,t163,t164,t165]
def t171 := 0x255f36b3ff9ff
def v238 := [t161,t162,t163,t171,t164,t165]
def t172 := 0x114042198063
def v239 := [t172,t161,t162,t163,t164,t165]
def t173 := 0x244920906080c
def v240 := [t161,t162,t173,t163,t164,t165]
def t174 := 0x3801e0
def v241 := [t174,t161,t162,t163,t164,t165]
def t175 := 0x3717be3f9fff3
def v242 := [t161,t162,t163,t164,t175,t165]
def t176 := 0x11616201f013
def v243 := [t176,t161,t162,t163,t164,t165]
def t177 := 0x3601a81c00e00
def v244 := [t161,t162,t163,t177,t164,t165]
def t178 := 0x11400039f000
def v245 := [t178,t161,t162,t163,t164]
def v246 := [t178,t161,t162,t163,t164,t165]
def t179 := 0x3ffe163fff1f3
def v247 := [t161,t162,t163,t164,t165,t179]
def t180 := 0x21620001f3
def v248 := [t180,t161,t162,t163,t164]
def v249 := [t180,t161,t162,t163,t164,t165]
def t181 := 0x3ee8001c60000
def v250 := [t161,t162,t163,t164,t181,t165]
def t182 := 0x106081c
def v251 := [t182,t161,t162,t163,t164,t165]
def t183 := 0x2ceb73de7ff9f
def v252 := [t161,t162,t163,t183,t164,t165]
def t184 := 0x8a0414c18603
def v253 := [t161,t184,t162,t163,t164,t165]
def t185 := 0x244b328207180
def v254 := [t161,t162,t185,t163,t164,t165]
def t186 := 0x1c00e00
def v255 := [t186,t161,t162,t163,t164,t165]
def t187 := 0x3ea1e95ff8fff
def v256 := [t161,t162,t163,t164,t187,t165]
def t188 := 0x8a041407801f
def v257 := [t161,t188,t162,t163,t164,t165]
def t189 := 0x3601a803801e0
def v258 := [t161,t162,t163,t189,t164,t165]
def t190 := 0x8a0001c78000
def v259 := [t161,t190,t162,t163,t164,t165]
def t191 := 0x3ffc415fffe1f
def v260 := [t161,t162,t163,t164,t191]
def v261 := [t161,t162,t163,t164,t165,t191]
def v262 := [t108,t161,t162,t163,t164,t165]
def t192 := 0x375c000387000
def v263 := [t161,t162,t163,t164,t192]
def v264 := [t161,t162,t163,t164,t192,t165]
def t193 := 0x2401201200980
def v265 := [t161,t162,t193,t163,t164,t165]
def t194 := 0x364bba9fe7ffc
def v266 := [t161,t162,t164,t194,t165]
def v267 := [t161,t162,t163,t164,t194,t165]
def t195 := 0x4a12806701c
def v268 := [t195,t161,t162,t164,t165]
def v269 := [t195,t161,t162,t163,t164,t165]
def t196 := 0x1200880d80660
def v270 := [t161,t162,t196,t163,t164,t165]
def t197 := 0x2448001267000
def v271 := [t161,t162,t197,t163,t164]
def v272 := [t161,t162,t197,t163,t164,t165]
def v273 := [t161,t162,t163,t164,t165,t87]
def t198 := 0x332800099c
def v274 := [t198,t161,t162,t163,t164]
def v275 := [t198,t161,t162,t163,t164,t165]
def t199 := 0x1bb4000d98000
def v276 := [t161,t162,t199,t163,t164,t165]
def t200 := 0x3600001f80000
def v277 := [t161,t162,t163,t200,t164,t165]
def t201 := 0x3ffda81ffffe0
def v278 := [t161,t162,t163,t164,t201]
def v279 := [t161,t162,t163,t164,t165,t201]
def t202 := 0x1a80000fe0
def v280 := [t202,t161,t162,t163,t164,t165]
def t203 := 0x9fc00007f000
def v281 := [t161,t162,t203,t163,t164]
def v282 := [t161,t162,t203,t163,t164,t165]
def p63_47 : Projection 50 25 := pick [0,1,2,3,4,5,6,7,8,9,10,11,25,26,27,28,29,30,31,32,33,34,35,36,37] rfl (by decide +kernel) (by decide)
def t204 := 0x204580102c400073e0001f3
def v283 := [t204,t0,t1,t2,t3,t4,t5]
def t205 := 0xef40007588003d60001e43000
def v284 := [t0,t1,t2,t3,t205,t4,t5]
def t206 := 0x2045000000029c73e000000
def v285 := [t206,t0,t1,t2,t3,t4]
def v286 := [t206,t0,t1,t2,t3,t4,t5]
def t207 := 0xffffff82702c7fffffe1bc1f3
def v287 := [t0,t1,t2,t3,t4,t5,t207]
def t208 := 0x100082702c40000001bc1f3
def v288 := [t208,t0,t1,t2,t3,t4]
def v289 := [t30,t28,t12,t13,t14]
def v290 := [t30,t28,t11,t12,t13,t14]
def t209 := 0x4240000190
def v291 := [t209,t30,t11,t12,t13,t14]
def t210 := 0x1294ed6c67fff
def v292 := [t30,t11,t12,t210,t13,t14]
def t211 := 0x200c04000603
def v293 := [t211,t30,t11,t12,t13,t14]
def t212 := 0x1090092c6786c
def v294 := [t30,t11,t212,t12,t13,t14]
def t213 := 0x613
def v295 := [t213,t30,t11,t12,t13,t14]
def t214 := 0xc347e6f078f9f
def v296 := [t11,t12,t13,t214,t14]
def v297 := [t30,t11,t12,t13,t214,t14]
def t215 := 0x204e44000180
def v298 := [t215,t11,t12,t13,t14]
def v299 := [t215,t30,t11,t12,t13,t14]
def t216 := 0xc14302b07880c
def v300 := [t30,t11,t12,t216,t13,t14]
def t217 := 0x200c00000780
def v301 := [t217,t30,t11,t12,t13,t14]
def t218 := 0xea07f47f80ff3
def v302 := [t30,t11,t12,t13,t14,t218]
def t219 := 0x4244000013
def v303 := [t219,t30,t11,t12,t13,t14]
def t220 := 0xe803103f80860
def v304 := [t30,t11,t12,t13,t220,t14]
def v305 := [t16,t30,t11,t12,t13,t14]
def v306 := [t30,t18,t11,t12,t13,t14]
def v307 := [t30,t11,t19,t12,t13,t14]
def v308 := [t20,t30,t11,t12,t13,t14]
def v309 := [t30,t22,t11,t12,t13,t14]
def v310 := [t30,t11,t12,t23,t13,t14]
def v311 := [t24,t30,t11,t12,t13,t14]
def v312 := [t30,t11,t12,t13,t14,t25]
def v313 := [t30,t26,t11,t12,t13,t14]
def v314 := [t30,t11,t12,t13,t27,t14]
def v315 := [t32,t30,t11,t12,t13,t14]
def v316 := [t30,t11,t12,t13,t33,t14]
def v317 := [t30,t11,t34,t12,t13,t14]
def v318 := [t30,t11,t12,t35,t13,t14]
def v319 := [t36,t30,t11,t12,t13,t14]
def v320 := [t30,t11,t12,t13,t14,t37]
def v321 := [t30,t11,t38,t12,t13,t14]
def v322 := [t30,t11,t12,t13,t39,t14]
def v323 := [t30,t11,t12,t44,t13,t14]
def v324 := [t30,t11,t12,t13,t45]
def v325 := [t30,t11,t12,t13,t14,t45]
def v326 := [t46,t30,t11,t12,t13,t14]
def v327 := [t30,t11,t12,t47,t13]
def v328 := [t30,t11,t12,t47,t13,t14]
def v329 := [t208,t0,t1,t2,t3,t4,t5]
def t221 := 0xffcfba0000003d638c0000000
def v330 := [t0,t1,t2,t3,t4,t221,t5]
def t222 := 0x1020c004081c
def v331 := [t222,t0,t1,t2,t3,t4,t5]
def t223 := 0x568b3aa996e7bde3cffe7ff9f
def v332 := [t0,t1,t2,t223,t3,t4,t5]
def v333 := [t69,t75,t71,t79,t72,t73]
def v334 := [t69,t76,t71,t79,t72,t73]
def v335 := [t78,t69,t79,t72,t73]
def v336 := [t78,t69,t70,t79,t72,t73]
def v337 := [t78,t69,t71,t79,t72,t73]
def v338 := [t69,t80,t70,t79,t72,t73]
def v339 := [t69,t81,t71,t79,t72,t73]
def v340 := [t69,t71,t79,t72,t83,t73]
def v341 := [t84,t69,t71,t79,t72,t73]
def v342 := [t86,t69,t70,t71,t79,t72]
def v343 := [t69,t88,t70,t71,t79,t72]
def t224 := 0x812003c193
def v344 := [t224,t69,t70,t71,t72,t73]
def t225 := 0x15fb77fffffff
def v345 := [t69,t70,t71,t225,t72,t73]
def t226 := 0x14c361de43e0c
def v346 := [t69,t70,t71,t226,t72,t73]
def v347 := [t69,t70,t79,t72,t107]
def v348 := [t69,t70,t71,t79,t72,t107]
def v349 := [t69,t70,t79,t72,t73,t107]
def v350 := [t108,t69,t70,t79,t72,t73]
def v351 := [t69,t70,t71,t79,t109,t72]
def t227 := 0x401201e00f80
def v352 := [t69,t227,t70,t71,t72,t73]
def t228 := 0x3ecbfbdffffff
def v353 := [t69,t70,t71,t72,t73,t228]
def t229 := 0x10ca53c07f01f
def v354 := [t69,t70,t71,t229,t72,t73]
def t230 := 0x2a00880180060
def v355 := [t69,t70,t71,t230,t72,t73]
def t231 := 0x10c0001e7f000
def v356 := [t69,t70,t231,t71,t72]
def v357 := [t69,t70,t231,t71,t79,t72]
def v358 := [t69,t70,t231,t71,t72,t73]
def t232 := 0x3fff73dffff9f
def v359 := [t69,t70,t71,t72,t73,t232]
def t233 := 0x40b73c000f9f
def v360 := [t69,t70,t233,t71,t72]
def v361 := [t69,t70,t233,t71,t79,t72]
def v362 := [t69,t70,t233,t71,t72,t73]
def t234 := 0x2b34000180000
def v363 := [t69,t70,t71,t234,t72,t73]
def t235 := 0x1089128816650c6040e60f180
def v364 := [t0,t235,t1,t2,t3,t4,t5]
def t236 := 0x460228218082b081831830603
def v365 := [t0,t1,t236,t2,t3,t4,t5]
def t237 := 0x1009000802400c02400600980
def v366 := [t0,t237,t1,t2,t3,t4,t5]
def t238 := 0xb88d92dc17753f63fcffcfffc
def v367 := [t0,t1,t2,t3,t238,t4,t5]
def t239 := 0x801280142501600ce04f01c
def v368 := [t0,t239,t1,t2,t3,t4,t5]
def t240 := 0xa804805401103201b01980660
def v369 := [t0,t1,t2,t240,t3,t4,t5]
def t241 := 0xd6000064f000
def v370 := [t241,t0,t1,t2,t3,t4,t5]
def t242 := 0xffd912fffe653ffe4cffff99c
def v371 := [t0,t1,t2,t3,t4,t242,t5]
def t243 := 0x10891288166500024ce00099c
def v372 := [t0,t243,t1,t2,t3,t4,t5]
def t244 := 0xef500077e800329c0019b0000
def v373 := [t0,t1,t2,t3,t244,t4,t5]
def t245 := 0x1089120000000d624ce000000
def v374 := [t0,t245,t1,t2,t3,t4,t5]
def t246 := 0xffefff8816653fffffe64f99c
def v375 := [t0,t1,t2,t3,t4,t5,t246]
def t247 := 0x881665000000064f99c
def v376 := [t247,t0,t1,t2,t3,t4,t5]
def t248 := 0xef66ed000000329db30000000
def v377 := [t0,t1,t2,t3,t4,t248,t5]
def t249 := 0x3003801800e00
def v378 := [t249,t0,t1,t2,t3,t4,t5]
def t250 := 0xfe0fa87d83d2bf83ff1ff0fff
def v379 := [t0,t1,t2,t3,t4,t250,t5]
def t251 := 0x46022821808281800f007001f
def v380 := [t0,t1,t251,t2,t3,t4,t5]
def t252 := 0xb80d805c03500e007007801e0
def v381 := [t0,t1,t2,t252,t3,t4,t5]
def t253 := 0x4600002180003180001870000
def v382 := [t0,t1,t253,t2,t3,t4,t5]
def t254 := 0xef522877e882bfff8f1fffe1f
def v383 := [t0,t1,t2,t3,t254,t5]
def v384 := [t6,t0,t1,t2,t3,t254,t5]
def v385 := [t0,t1,t10,t2,t3,t254,t5]
def v386 := [t68,t0,t1,t2,t3,t254,t5]
def v387 := [t0,t126,t1,t2,t3,t254,t5]
def v388 := [t127,t0,t1,t2,t3,t254,t5]
def v389 := [t0,t1,t2,t132,t3,t254,t5]
def v390 := [t144,t0,t1,t2,t3,t254,t5]
def v391 := [t0,t1,t154,t2,t3,t254,t5]
def v392 := [t155,t0,t1,t2,t3,t254,t5]
def v393 := [t0,t1,t2,t3,t156,t254,t5]
def v394 := [t157,t0,t1,t2,t3,t254,t5]
def v395 := [t0,t1,t2,t158,t3,t254,t5]
def t255 := 0x1000026000029c0301bc013
def v396 := [t255,t0,t1,t2,t3,t254,t5]
def t256 := 0xef726df7f8aefffffffffffff
def v397 := [t0,t1,t2,t3,t254,t256,t5]
def t257 := 0x204580102c400070e0001e0
def v398 := [t257,t0,t1,t2,t3,t254,t5]
def t258 := 0xef4228758882bd638c1e43e0c
def v399 := [t0,t1,t2,t3,t258,t254,t5]
def v400 := [t206,t0,t1,t2,t3,t254]
def v401 := [t206,t0,t1,t2,t3,t254,t5]
def v402 := [t0,t1,t2,t3,t254,t5,t207]
def v403 := [t208,t0,t1,t2,t3,t254]
def v404 := [t208,t0,t1,t2,t3,t254,t5]
def v405 := [t0,t1,t2,t3,t254,t221,t5]
def v406 := [t222,t0,t1,t2,t3,t254,t5]
def v407 := [t0,t1,t223,t3,t254,t5]
def v408 := [t0,t1,t2,t223,t3,t254,t5]
def v409 := [t0,t235,t1,t2,t3,t254,t5]
def v410 := [t0,t1,t236,t3,t254,t5]
def v411 := [t0,t1,t236,t2,t3,t254,t5]
def v412 := [t0,t237,t1,t2,t3,t254,t5]
def v413 := [t0,t1,t2,t3,t238,t254,t5]
def v414 := [t0,t239,t1,t2,t3,t254,t5]
def v415 := [t0,t1,t2,t240,t3,t254,t5]
def t259 := 0xd620c064f81c
def v416 := [t259,t0,t1,t2,t3,t254,t5]
def t260 := 0xffdb3afffee7bfffcffffff9f
def v417 := [t0,t1,t2,t3,t254,t260,t5]
def t261 := 0x108912881665000040e000180
def v418 := [t0,t261,t1,t2,t3,t254,t5]
def t262 := 0xef522877e882b29d8319b0603
def v419 := [t0,t1,t2,t3,t262,t254,t5]
def v420 := [t0,t245,t1,t2,t3,t254,t5]
def v421 := [t0,t1,t2,t3,t254,t5,t246]
def v422 := [t247,t0,t1,t2,t3,t254,t5]
def v423 := [t0,t1,t2,t3,t254,t248,t5]
def v424 := [t249,t0,t1,t2,t3,t254,t5]
def v425 := [t0,t1,t2,t3,t254,t250,t5]
def v426 := [t0,t1,t251,t2,t3,t254,t5]
def v427 := [t0,t1,t2,t252,t3,t254,t5]
def t263 := 0xa950005668000e7c00078f000
def v428 := [t0,t1,t2,t263,t3,t5]
def v429 := [t0,t1,t263,t3,t254,t5]
def v430 := [t0,t1,t2,t263,t3,t254,t5]
def t264 := 0x46022800000031838f0000000
def v431 := [t0,t1,t264,t2,t3,t254,t5]
def t265 := 0xffefff218082bffffff870e1f
def v432 := [t0,t1,t2,t3,t254,t265]
def v433 := [t0,t1,t2,t3,t254,t5,t265]
def t266 := 0x2180828000001870e1f
def v434 := [t266,t0,t1,t2,t3,t254,t5]
def t267 := 0xb9edd70000000e7c70e000000
def v435 := [t0,t1,t2,t3,t267,t254]
def v436 := [t0,t1,t2,t3,t267,t254,t5]
def t268 := 0xa800005400003e03801f80e00
def v437 := [t0,t1,t2,t268,t3,t254,t5]
def t269 := 0xff5fa87febd2bfffff1ffffff
def v438 := [t0,t1,t2,t3,t254,t269,t5]
def t270 := 0x100d8008035000007000001e0
def v439 := [t0,t270,t1,t2,t3,t254,t5]
def t271 := 0x47522823e88281fc0f007f01f
def v440 := [t0,t1,t2,t271,t3,t254,t5]
def t272 := 0xb80d800000003e03f00000000
def v441 := [t0,t1,t2,t272,t3,t254,t5]
def t273 := 0xffefff5c03503fffffff80fe0
def v442 := [t0,t1,t2,t3,t254,t273]
def v443 := [t0,t1,t2,t3,t254,t5,t273]
def t274 := 0x5c03500000001f80fe0
def v444 := [t274,t0,t1,t2,t3,t254,t5]
def t275 := 0x47e27f00000001fc0fe000000
def v445 := [t0,t1,t2,t275,t3,t254]
def v446 := [t0,t1,t2,t275,t3,t254,t5]
def t276 := 0xef42280000003fff8f0000000
def v447 := [t0,t1,t2,t3,t276,t254,t5]
def t277 := 0xffffff77e882bfffffffffe1f
def v448 := [t0,t1,t2,t3,t254,t5,t277]
def t278 := 0x100077e8828000001fffe1f
def v449 := [t278,t0,t1,t2,t3,t254,t5]
def t279 := 0x10add7000000000070e000000
def v450 := [t0,t1,t279,t2,t3,t254,t5]
def v451 := [t0,t1,t2,t3,t4,t254,t5]
def t280 := 0x22800008280038f0000e1f
def v452 := [t280,t0,t1,t2,t3,t4,t5]
def v453 := [t0,t1,t2,t263,t3,t4,t5]
def v454 := [t0,t1,t264,t2,t3,t4,t5]
def v455 := [t0,t1,t2,t3,t4,t265]
def v456 := [t6,t0,t1,t2,t3,t4,t265]
def v457 := [t0,t1,t10,t2,t3,t4,t265]
def v458 := [t68,t0,t1,t2,t3,t4,t265]
def v459 := [t0,t126,t1,t2,t3,t4,t265]
def v460 := [t127,t0,t1,t2,t3,t4,t265]
def v461 := [t0,t1,t2,t132,t3,t4,t265]
def v462 := [t144,t0,t1,t2,t3,t4,t265]
def v463 := [t0,t1,t154,t2,t3,t4,t265]
def v464 := [t155,t0,t1,t2,t3,t4,t265]
def v465 := [t0,t1,t2,t3,t156,t4,t265]
def v466 := [t157,t0,t1,t2,t3,t4,t265]
def v467 := [t0,t1,t2,t158,t3,t4,t265]
def v468 := [t159,t0,t1,t2,t3,t4,t265]
def v469 := [t0,t1,t2,t3,t4,t160,t265]
def v470 := [t204,t0,t1,t2,t3,t4,t265]
def v471 := [t0,t1,t2,t3,t205,t4,t265]
def t281 := 0x2045000000029c73e030013
def v472 := [t281,t0,t1,t2,t3,t4]
def v473 := [t281,t0,t1,t2,t3,t4,t265]
def t282 := 0xffffffa3f0aefffffff9fcfff
def v474 := [t0,t1,t2,t3,t4,t265,t282]
def t283 := 0x100082702c400000018c1e0
def v475 := [t283,t0,t1,t2,t3,t4]
def v476 := [t283,t0,t1,t2,t3,t4,t265]
def t284 := 0xffcfba218082bd638c1840e0c
def v477 := [t0,t1,t2,t3,t4,t284,t265]
def v478 := [t222,t0,t1,t2,t3,t4,t265]
def v479 := [t0,t1,t2,t223,t3,t4,t265]
def v480 := [t0,t235,t1,t2,t3,t4,t265]
def v481 := [t0,t1,t236,t2,t3,t4,t265]
def v482 := [t0,t237,t1,t2,t3,t4,t265]
def v483 := [t0,t1,t2,t3,t238,t4,t265]
def v484 := [t0,t239,t1,t2,t3,t4,t265]
def v485 := [t0,t1,t2,t240,t3,t4,t265]
def v486 := [t241,t0,t1,t2,t3,t4,t265]
def v487 := [t0,t1,t2,t3,t4,t242,t265]
def v488 := [t0,t243,t1,t2,t3,t4,t265]
def v489 := [t0,t1,t2,t3,t244,t4,t265]
def t285 := 0x1089120000000d624ce04081c
def v490 := [t0,t285,t1,t2,t3,t4,t265]
def t286 := 0xffefffa996e7bffffffe7ff9f
def v491 := [t0,t1,t2,t3,t4,t265,t286]
def t287 := 0x881665000000060f180
def v492 := [t287,t0,t1,t2,t3,t4,t265]
def t288 := 0xef66ed218082b29db31830603
def v493 := [t0,t1,t2,t3,t4,t288,t265]
def v494 := [t249,t0,t1,t2,t3,t4,t265]
def v495 := [t0,t1,t2,t3,t4,t250,t265]
def v496 := [t0,t1,t251,t2,t3,t4,t265]
def v497 := [t0,t1,t2,t252,t3,t4,t265]
def v498 := [t0,t1,t253,t2,t3,t4,t265]
def v499 := [t0,t1,t2,t3,t4,t254,t265]
def v500 := [t280,t0,t1,t2,t3,t4,t265]
def v501 := [t0,t1,t2,t263,t3,t265]
def v502 := [t0,t1,t2,t263,t3,t4,t265]
def v503 := [t0,t1,t2,t3,t267,t4]
def v504 := [t0,t1,t3,t267,t4,t265]
def v505 := [t0,t1,t2,t3,t267,t4,t265]
def t289 := 0xa800005400003e00001f80000
def v506 := [t0,t1,t2,t289,t3,t4,t265]
def t290 := 0xff5d807feb503ffff01ffffe0
def v507 := [t0,t1,t2,t3,t4,t290,t265]
def t291 := 0x100d800803500003f00000fe0
def v508 := [t0,t291,t1,t2,t3,t4,t265]
def t292 := 0x47500023e80001fc00007f000
def v509 := [t0,t1,t2,t292,t3,t4,t265]
def t293 := 0xb80d800000003e03f01800e00
def v510 := [t0,t1,t2,t293,t3,t4,t265]
def t294 := 0xffefff7d83d2bffffffff0fff
def v511 := [t0,t1,t2,t3,t4,t294]
def v512 := [t0,t1,t2,t3,t4,t265,t294]
def t295 := 0x5c035000000007801e0
def v513 := [t295,t0,t1,t2,t3,t4,t265]
def t296 := 0x47e27f21808281fc0fe07001f
def v514 := [t0,t1,t2,t296,t3,t4]
def v515 := [t0,t1,t2,t296,t3,t4,t265]
def t297 := 0xef40002180003ffc001870000
def v516 := [t0,t1,t2,t3,t297,t4,t265]
def v517 := [t0,t1,t2,t3,t4,t265,t277]
def t298 := 0x1000566800000000078f000
def v518 := [t298,t0,t1,t2,t3,t4,t265]
def t299 := 0x10afff0000828003ffe000e1f
def v519 := [t0,t1,t299,t2,t3,t4,t265]
def v520 := [t0,t1,t2,t3,t4,t5,t265]
def v521 := [t266,t0,t1,t2,t3,t4,t5]
def v522 := [t0,t1,t2,t3,t267,t4,t5]
def v523 := [t0,t1,t2,t289,t3,t4,t5]
def v524 := [t0,t1,t2,t3,t4,t290,t5]
def v525 := [t0,t291,t1,t2,t3,t4,t5]
def v526 := [t0,t1,t2,t292,t3,t4,t5]
def v527 := [t0,t1,t2,t272,t3,t4,t5]
def v528 := [t0,t1,t2,t3,t4,t273]
def v529 := [t0,t1,t2,t3,t4,t5,t273]
def v530 := [t274,t0,t1,t2,t3,t4,t5]
def v531 := [t0,t1,t2,t275,t3,t4]
def v532 := [t0,t1,t2,t275,t3,t4,t5]
def t300 := 0xef40000000003ffc000000000
def v533 := [t0,t1,t2,t3,t300,t4,t5]
def t301 := 0xffffff77e8003fffffffff000
def v534 := [t0,t1,t2,t3,t4,t5,t301]
def t302 := 0x100077e8000000001fff000
def v535 := [t302,t0,t1,t2,t3,t4,t5]
def t303 := 0x10afff0000000003ffe000000
def v536 := [t0,t1,t303,t2,t3,t4,t5]
theorem b0 : Ban 6 3 v2 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w0 : Wide 6 3 v2 := viaSub (ws := [v2]) (consBan b0 (nilBan 6 3)) (by decide) (by decide +kernel)
theorem b1 : Ban 50 7 v1 := smallByCut p63_13 w0
theorem b2 : Ban 26 5 v5 := checkedSmall
theorem b3 : Ban 26 5 v6 := checkedSmall
theorem b4 : Ban 26 5 v7 := checkedSmall
theorem b5 : Ban 26 5 v8 := checkedSmall
theorem b6 : Ban 26 5 v9 := checkedSmall
theorem b7 : Ban 26 5 v10 := checkedSmall
theorem b8 : Ban 26 5 v11 := checkedSmall
theorem b9 : Ban 26 5 v12 := checkedSmall
theorem b10 : Ban 26 5 v13 := checkedSmall
theorem b11 : Ban 26 5 v14 := checkedSmall
theorem b12 : Ban 26 5 v15 := checkedSmall
theorem b13 : Ban 26 5 v16 := checkedSmall
theorem b14 : Ban 26 5 v17 := checkedSmall
theorem b15 : Ban 26 5 v18 := checkedSmall
theorem b16 : Ban 26 5 v19 := checkedSmall
theorem b17 : Ban 26 5 v20 := checkedSmall
theorem b18 : Ban 26 5 v21 := checkedSmall
theorem b19 : Ban 26 5 v22 := checkedSmall
theorem b20 : Ban 26 5 v23 := checkedSmall
theorem b21 : Ban 26 5 v24 := checkedSmall
theorem b22 : Ban 26 5 v25 := checkedSmall
theorem b23 : Ban 26 5 v26 := checkedSmall
theorem b24 : Ban 26 5 v27 := checkedSmall
theorem b25 : Ban 26 5 v28 := checkedSmall
theorem b26 : Ban 26 5 v29 := checkedSmall
theorem b27 : Ban 26 5 v30 := checkedSmall
theorem b28 : Ban 26 5 v31 := checkedSmall
theorem b29 : Ban 26 5 v32 := checkedSmall
theorem b30 : Ban 26 5 v33 := checkedSmall
theorem b31 : Ban 26 5 v34 := checkedSmall
theorem b32 : Ban 26 5 v35 := checkedSmall
theorem b33 : Ban 26 5 v36 := checkedSmall
theorem b34 : Ban 26 5 v37 := checkedSmall
theorem b35 : Ban 26 5 v38 := checkedSmall
theorem b36 : Ban 26 5 v39 := checkedSmall
theorem b37 : Ban 26 5 v40 := checkedSmall
theorem b38 : Ban 26 5 v41 := checkedSmall
theorem b39 : Ban 26 5 v42 := checkedSmall
theorem b40 : Ban 26 5 v43 := checkedSmall
theorem b41 : Ban 26 5 v44 := checkedSmall
theorem b42 : Ban 26 5 v45 := checkedSmall
theorem b43 : Ban 26 5 v46 := checkedSmall
theorem b44 : Ban 26 5 v47 := checkedSmall
theorem b45 : Ban 26 5 v48 := checkedSmall
theorem b46 : Ban 26 5 v49 := checkedSmall
theorem b47 : Ban 26 5 v50 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b48 : Ban 26 6 v4 := viaBranch (ws := [v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50]) (consBan b2 (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b10 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (consBan b19 (consBan b20 (consBan b21 (consBan b22 (consBan b23 (consBan b24 (consBan b25 (consBan b26 (consBan b27 (consBan b28 (consBan b29 (consBan b30 (consBan b31 (consBan b32 (consBan b33 (consBan b34 (consBan b35 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (consBan b40 (consBan b41 (consBan b42 (consBan b43 (consBan b44 (consBan b45 (consBan b46 (consBan b47 (nilBan 26 5))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b49 : Ban 26 5 v51 := checkedSmall
theorem b50 : Ban 26 5 v52 := checkedSmall
theorem b51 : Ban 26 5 v53 := checkedSmall
theorem b52 : Ban 26 5 v54 := checkedSmall
theorem b53 : Ban 26 5 v55 := checkedSmall
theorem b54 : Ban 26 5 v56 := checkedSmall
theorem b55 : Ban 26 5 v57 := checkedSmall
theorem b56 : Ban 26 5 v58 := checkedSmall
theorem b57 : Ban 26 5 v59 := checkedSmall
theorem b58 : Ban 26 5 v60 := checkedSmall
theorem b59 : Ban 26 5 v61 := checkedSmall
theorem b60 : Ban 26 5 v62 := checkedSmall
theorem b61 : Ban 26 5 v63 := checkedSmall
theorem b62 : Ban 26 5 v64 := checkedSmall
theorem b63 : Ban 26 5 v65 := checkedSmall
theorem b64 : Ban 26 5 v66 := checkedSmall
theorem b65 : Ban 26 5 v67 := checkedSmall
theorem b66 : Ban 26 5 v68 := checkedSmall
theorem b67 : Ban 26 5 v69 := checkedSmall
theorem b68 : Ban 26 5 v70 := checkedSmall
theorem b69 : Ban 26 5 v71 := checkedSmall
theorem b70 : Ban 26 5 v72 := checkedSmall
theorem b71 : Ban 26 5 v73 := checkedSmall
theorem b72 : Ban 26 5 v74 := checkedSmall
theorem b73 : Ban 26 5 v75 := checkedSmall
theorem b74 : Ban 26 5 v76 := checkedSmall
theorem b75 : Ban 26 5 v77 := checkedSmall
theorem b76 : Ban 26 5 v78 := checkedSmall
theorem b77 : Ban 26 5 v79 := checkedSmall
theorem b78 : Ban 26 5 v80 := checkedSmall
theorem b79 : Ban 26 5 v81 := checkedSmall
theorem b80 : Ban 26 5 v82 := checkedSmall
theorem b81 : Ban 26 5 v83 := checkedSmall
theorem b82 : Ban 26 5 v84 := checkedSmall
theorem b83 : Ban 26 5 v85 := checkedSmall
theorem b84 : Ban 26 5 v86 := checkedSmall
theorem b85 : Ban 26 5 v87 := checkedSmall
theorem b86 : Ban 26 5 v88 := checkedSmall
theorem b87 : Ban 26 5 v89 := checkedSmall
theorem b88 : Ban 26 5 v90 := checkedSmall
theorem b89 : Ban 26 5 v91 := checkedSmall
theorem b90 : Ban 26 5 v92 := checkedSmall
theorem b91 : Ban 26 5 v93 := checkedSmall
theorem b92 : Ban 26 5 v94 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b93 : Ban 26 6 v6 := viaBranch (ws := [v51,v52,v53,v54,v55,v8,v56,v57,v58,v59,v60,v61,v62,v63,v64,v7,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94]) (consBan b49 (consBan b50 (consBan b51 (consBan b52 (consBan b53 (consBan b5 (consBan b54 (consBan b55 (consBan b56 (consBan b57 (consBan b58 (consBan b59 (consBan b60 (consBan b61 (consBan b62 (consBan b4 (consBan b63 (consBan b64 (consBan b65 (consBan b66 (consBan b67 (consBan b68 (consBan b69 (consBan b70 (consBan b71 (consBan b72 (consBan b73 (consBan b74 (consBan b75 (consBan b76 (consBan b77 (consBan b78 (consBan b79 (consBan b80 (consBan b81 (consBan b82 (consBan b83 (consBan b84 (consBan b85 (consBan b86 (consBan b87 (consBan b88 (consBan b89 (consBan b90 (consBan b91 (consBan b92 (nilBan 26 5))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w1 : Wide 26 6 v6 := viaSub (ws := [v4,v6]) (consBan b48 (consBan b93 (nilBan 26 6))) (by decide) (by decide +kernel)
theorem b94 : Ban 50 7 v3 := smallByCut p63_55 w1
theorem b95 : Ban 25 5 v97 := checkedSmall
theorem b96 : Ban 25 5 v98 := checkedSmall
theorem b97 : Ban 25 5 v99 := checkedSmall
theorem b98 : Ban 25 5 v100 := checkedSmall
theorem b99 : Ban 25 5 v101 := checkedSmall
theorem b100 : Ban 25 5 v102 := checkedSmall
theorem b101 : Ban 25 5 v103 := checkedSmall
theorem b102 : Ban 25 5 v104 := checkedSmall
theorem b103 : Ban 25 5 v105 := checkedSmall
theorem b104 : Ban 25 5 v106 := checkedSmall
theorem b105 : Ban 25 5 v107 := checkedSmall
theorem b106 : Ban 25 5 v108 := checkedSmall
theorem b107 : Ban 25 5 v109 := checkedSmall
theorem b108 : Ban 25 5 v110 := checkedSmall
theorem b109 : Ban 25 5 v111 := checkedSmall
theorem b110 : Ban 25 5 v112 := checkedSmall
theorem b111 : Ban 25 5 v113 := checkedSmall
theorem b112 : Ban 25 5 v114 := checkedSmall
theorem b113 : Ban 25 5 v115 := checkedSmall
theorem b114 : Ban 25 5 v116 := checkedSmall
theorem b115 : Ban 25 5 v117 := checkedSmall
theorem b116 : Ban 25 5 v118 := checkedSmall
theorem b117 : Ban 25 5 v119 := checkedSmall
theorem b118 : Ban 25 5 v120 := checkedSmall
theorem b119 : Ban 25 5 v121 := checkedSmall
theorem b120 : Ban 25 5 v122 := checkedSmall
theorem b121 : Ban 25 5 v123 := checkedSmall
theorem b122 : Ban 25 5 v124 := checkedSmall
theorem b123 : Ban 25 5 v125 := checkedSmall
theorem b124 : Ban 25 5 v126 := checkedSmall
theorem b125 : Ban 25 5 v127 := checkedSmall
theorem b126 : Ban 25 5 v128 := checkedSmall
theorem b127 : Ban 25 5 v129 := checkedSmall
theorem b128 : Ban 25 5 v130 := checkedSmall
theorem b129 : Ban 25 5 v131 := checkedSmall
theorem b130 : Ban 25 5 v132 := checkedSmall
theorem b131 : Ban 25 5 v133 := checkedSmall
theorem b132 : Ban 25 5 v134 := checkedSmall
theorem b133 : Ban 25 5 v135 := checkedSmall
theorem b134 : Ban 25 5 v136 := checkedSmall
theorem b135 : Ban 25 5 v137 := checkedSmall
theorem b136 : Ban 25 5 v138 := checkedSmall
theorem b137 : Ban 25 5 v139 := checkedSmall
theorem b138 : Ban 25 5 v140 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b139 : Ban 25 6 v96 := viaBranch (ws := [v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140]) (consBan b95 (consBan b96 (consBan b97 (consBan b98 (consBan b99 (consBan b100 (consBan b101 (consBan b102 (consBan b103 (consBan b104 (consBan b105 (consBan b106 (consBan b107 (consBan b108 (consBan b109 (consBan b110 (consBan b111 (consBan b112 (consBan b113 (consBan b114 (consBan b115 (consBan b116 (consBan b117 (consBan b118 (consBan b119 (consBan b120 (consBan b121 (consBan b122 (consBan b123 (consBan b124 (consBan b125 (consBan b126 (consBan b127 (consBan b128 (consBan b129 (consBan b130 (consBan b131 (consBan b132 (consBan b133 (consBan b134 (consBan b135 (consBan b136 (consBan b137 (consBan b138 (nilBan 25 5))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b140 : Ban 25 5 v141 := checkedSmall
theorem b141 : Ban 25 5 v142 := checkedSmall
theorem b142 : Ban 25 5 v143 := checkedSmall
theorem b143 : Ban 25 5 v144 := checkedSmall
theorem b144 : Ban 25 5 v145 := checkedSmall
theorem b145 : Ban 25 5 v146 := checkedSmall
theorem b146 : Ban 25 5 v147 := checkedSmall
theorem b147 : Ban 25 5 v148 := checkedSmall
theorem b148 : Ban 25 5 v149 := checkedSmall
theorem b149 : Ban 25 5 v150 := checkedSmall
theorem b150 : Ban 25 5 v151 := checkedSmall
theorem b151 : Ban 25 5 v152 := checkedSmall
theorem b152 : Ban 25 5 v153 := checkedSmall
theorem b153 : Ban 25 5 v154 := checkedSmall
theorem b154 : Ban 25 5 v155 := checkedSmall
theorem b155 : Ban 25 5 v156 := checkedSmall
theorem b156 : Ban 25 5 v157 := checkedSmall
theorem b157 : Ban 25 5 v158 := checkedSmall
theorem b158 : Ban 25 5 v159 := checkedSmall
theorem b159 : Ban 25 5 v160 := checkedSmall
theorem b160 : Ban 25 5 v161 := checkedSmall
theorem b161 : Ban 25 5 v162 := checkedSmall
theorem b162 : Ban 25 5 v163 := checkedSmall
theorem b163 : Ban 25 5 v164 := checkedSmall
theorem b164 : Ban 25 5 v165 := checkedSmall
theorem b165 : Ban 25 5 v166 := checkedSmall
theorem b166 : Ban 25 5 v167 := checkedSmall
theorem b167 : Ban 25 5 v168 := checkedSmall
theorem b168 : Ban 25 5 v169 := checkedSmall
theorem b169 : Ban 25 5 v170 := checkedSmall
theorem b170 : Ban 25 5 v171 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b171 : Ban 25 6 v100 := viaBranch (ws := [v98,v141,v142,v143,v144,v145,v146,v147,v97,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v163,v164,v165,v166,v167,v168,v169,v170,v171]) (consBan b96 (consBan b140 (consBan b141 (consBan b142 (consBan b143 (consBan b144 (consBan b145 (consBan b146 (consBan b95 (consBan b147 (consBan b148 (consBan b149 (consBan b150 (consBan b151 (consBan b152 (consBan b153 (consBan b154 (consBan b155 (consBan b156 (consBan b157 (consBan b158 (consBan b159 (consBan b160 (consBan b161 (consBan b162 (consBan b163 (consBan b164 (consBan b165 (consBan b166 (consBan b167 (consBan b168 (consBan b169 (consBan b170 (nilBan 25 5)))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w2 : Wide 25 6 v100 := viaSub (ws := [v96,v100]) (consBan b139 (consBan b171 (nilBan 25 6))) (by decide) (by decide +kernel)
theorem b172 : Ban 50 7 v95 := smallByCut p63_31 w2
theorem b173 : Ban 50 7 v172 := smallByCut p63_13 w0
theorem b174 : Ban 12 4 v174 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w3 : Wide 12 4 v174 := viaSub (ws := [v174]) (consBan b174 (nilBan 12 4)) (by decide) (by decide +kernel)
theorem b175 : Ban 50 7 v173 := smallByCut p63_51 w3
theorem b176 : Ban 26 5 v176 := checkedSmall
theorem b177 : Ban 26 5 v177 := checkedSmall
theorem b178 : Ban 26 5 v178 := checkedSmall
theorem b179 : Ban 26 5 v179 := checkedSmall
theorem b180 : Ban 26 5 v180 := checkedSmall
theorem b181 : Ban 26 5 v181 := checkedSmall
theorem b182 : Ban 26 5 v182 := checkedSmall
theorem b183 : Ban 26 5 v183 := checkedSmall
theorem b184 : Ban 26 5 v184 := checkedSmall
theorem b185 : Ban 26 5 v185 := checkedSmall
theorem b186 : Ban 26 5 v186 := checkedSmall
theorem b187 : Ban 26 5 v187 := checkedSmall
theorem b188 : Ban 26 5 v188 := checkedSmall
theorem b189 : Ban 26 5 v189 := checkedSmall
theorem b190 : Ban 26 5 v190 := checkedSmall
theorem b191 : Ban 26 5 v191 := checkedSmall
theorem b192 : Ban 26 5 v192 := checkedSmall
theorem b193 : Ban 26 5 v193 := checkedSmall
theorem b194 : Ban 26 5 v194 := checkedSmall
theorem b195 : Ban 26 5 v195 := checkedSmall
theorem b196 : Ban 26 5 v196 := checkedSmall
theorem b197 : Ban 26 5 v197 := checkedSmall
theorem b198 : Ban 26 5 v198 := checkedSmall
theorem b199 : Ban 26 5 v199 := checkedSmall
theorem b200 : Ban 26 5 v200 := checkedSmall
theorem b201 : Ban 26 5 v201 := checkedSmall
theorem b202 : Ban 26 5 v202 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b203 : Ban 26 6 v10 := viaBranch (ws := [v56,v176,v177,v178,v179,v180,v181,v12,v182,v183,v184,v70,v185,v186,v11,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202]) (consBan b54 (consBan b176 (consBan b177 (consBan b178 (consBan b179 (consBan b180 (consBan b181 (consBan b9 (consBan b182 (consBan b183 (consBan b184 (consBan b68 (consBan b185 (consBan b186 (consBan b8 (consBan b187 (consBan b188 (consBan b189 (consBan b190 (consBan b191 (consBan b192 (consBan b193 (consBan b194 (consBan b195 (consBan b196 (consBan b197 (consBan b198 (consBan b199 (consBan b200 (consBan b201 (consBan b202 (nilBan 26 5)))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w4 : Wide 26 6 v10 := viaSub (ws := [v4,v10]) (consBan b48 (consBan b203 (nilBan 26 6))) (by decide) (by decide +kernel)
theorem b204 : Ban 50 7 v175 := smallByCut p63_55 w4
theorem b205 : Ban 25 5 v204 := checkedSmall
theorem b206 : Ban 25 5 v205 := checkedSmall
theorem b207 : Ban 25 5 v206 := checkedSmall
theorem b208 : Ban 25 5 v207 := checkedSmall
theorem b209 : Ban 25 5 v208 := checkedSmall
theorem b210 : Ban 25 5 v209 := checkedSmall
theorem b211 : Ban 25 5 v210 := checkedSmall
theorem b212 : Ban 25 5 v211 := checkedSmall
theorem b213 : Ban 25 5 v212 := checkedSmall
theorem b214 : Ban 25 5 v213 := checkedSmall
theorem b215 : Ban 25 5 v214 := checkedSmall
theorem b216 : Ban 25 5 v215 := checkedSmall
theorem b217 : Ban 25 5 v216 := checkedSmall
theorem b218 : Ban 25 5 v217 := checkedSmall
theorem b219 : Ban 25 5 v218 := checkedSmall
theorem b220 : Ban 25 5 v219 := checkedSmall
theorem b221 : Ban 25 5 v220 := checkedSmall
theorem b222 : Ban 25 5 v221 := checkedSmall
theorem b223 : Ban 25 5 v222 := checkedSmall
theorem b224 : Ban 25 5 v223 := checkedSmall
theorem b225 : Ban 25 5 v224 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b226 : Ban 25 6 v117 := viaBranch (ws := [v204,v205,v206,v150,v207,v165,v208,v209,v210,v115,v211,v116,v119,v212,v213,v122,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224]) (consBan b205 (consBan b206 (consBan b207 (consBan b149 (consBan b208 (consBan b164 (consBan b209 (consBan b210 (consBan b211 (consBan b113 (consBan b212 (consBan b114 (consBan b117 (consBan b213 (consBan b214 (consBan b120 (consBan b215 (consBan b216 (consBan b217 (consBan b218 (consBan b219 (consBan b220 (consBan b221 (consBan b222 (consBan b223 (consBan b224 (consBan b225 (nilBan 25 5)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w5 : Wide 25 6 v117 := viaSub (ws := [v96,v117]) (consBan b139 (consBan b226 (nilBan 25 6))) (by decide) (by decide +kernel)
theorem b227 : Ban 50 7 v203 := smallByCut p63_31 w5
theorem b228 : Ban 50 7 v225 := smallByCut p63_51 w3
theorem b229 : Ban 50 7 v226 := smallByCut p63_51 w3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w6 : Wide 26 6 v4 := viaSub (ws := [v4]) (consBan b48 (nilBan 26 6)) (by decide) (by decide +kernel)
theorem b230 : Ban 50 7 v227 := smallByCut p63_55 w6
theorem b231 : Ban 50 7 v228 := smallByCut p63_55 w6
theorem b232 : Ban 50 7 v229 := smallByCut p63_51 w3
theorem b233 : Ban 50 7 v230 := smallByCut p63_13 w0
theorem b234 : Ban 25 5 v233 := checkedSmall
theorem b235 : Ban 25 5 v234 := checkedSmall
theorem b236 : Ban 25 5 v235 := checkedSmall
theorem b237 : Ban 25 5 v236 := checkedSmall
theorem b238 : Ban 25 5 v237 := checkedSmall
theorem b239 : Ban 25 5 v238 := checkedSmall
theorem b240 : Ban 25 5 v239 := checkedSmall
theorem b241 : Ban 25 5 v240 := checkedSmall
theorem b242 : Ban 25 5 v241 := checkedSmall
theorem b243 : Ban 25 5 v242 := checkedSmall
theorem b244 : Ban 25 5 v243 := checkedSmall
theorem b245 : Ban 25 5 v244 := checkedSmall
theorem b246 : Ban 25 5 v245 := checkedSmall
theorem b247 : Ban 25 5 v246 := checkedSmall
theorem b248 : Ban 25 5 v247 := checkedSmall
theorem b249 : Ban 25 5 v248 := checkedSmall
theorem b250 : Ban 25 5 v249 := checkedSmall
theorem b251 : Ban 25 5 v250 := checkedSmall
theorem b252 : Ban 25 5 v251 := checkedSmall
theorem b253 : Ban 25 5 v252 := checkedSmall
theorem b254 : Ban 25 5 v253 := checkedSmall
theorem b255 : Ban 25 5 v254 := checkedSmall
theorem b256 : Ban 25 5 v255 := checkedSmall
theorem b257 : Ban 25 5 v256 := checkedSmall
theorem b258 : Ban 25 5 v257 := checkedSmall
theorem b259 : Ban 25 5 v258 := checkedSmall
theorem b260 : Ban 25 5 v259 := checkedSmall
theorem b261 : Ban 25 5 v260 := checkedSmall
theorem b262 : Ban 25 5 v261 := checkedSmall
theorem b263 : Ban 25 5 v262 := checkedSmall
theorem b264 : Ban 25 5 v263 := checkedSmall
theorem b265 : Ban 25 5 v264 := checkedSmall
theorem b266 : Ban 25 5 v265 := checkedSmall
theorem b267 : Ban 25 5 v266 := checkedSmall
theorem b268 : Ban 25 5 v267 := checkedSmall
theorem b269 : Ban 25 5 v268 := checkedSmall
theorem b270 : Ban 25 5 v269 := checkedSmall
theorem b271 : Ban 25 5 v270 := checkedSmall
theorem b272 : Ban 25 5 v271 := checkedSmall
theorem b273 : Ban 25 5 v272 := checkedSmall
theorem b274 : Ban 25 5 v273 := checkedSmall
theorem b275 : Ban 25 5 v274 := checkedSmall
theorem b276 : Ban 25 5 v275 := checkedSmall
theorem b277 : Ban 25 5 v276 := checkedSmall
theorem b278 : Ban 25 5 v277 := checkedSmall
theorem b279 : Ban 25 5 v278 := checkedSmall
theorem b280 : Ban 25 5 v279 := checkedSmall
theorem b281 : Ban 25 5 v280 := checkedSmall
theorem b282 : Ban 25 5 v281 := checkedSmall
theorem b283 : Ban 25 5 v282 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b284 : Ban 25 6 v232 := viaBranch (ws := [v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282]) (consBan b234 (consBan b235 (consBan b236 (consBan b237 (consBan b238 (consBan b239 (consBan b240 (consBan b241 (consBan b242 (consBan b243 (consBan b244 (consBan b245 (consBan b246 (consBan b247 (consBan b248 (consBan b249 (consBan b250 (consBan b251 (consBan b252 (consBan b253 (consBan b254 (consBan b255 (consBan b256 (consBan b257 (consBan b258 (consBan b259 (consBan b260 (consBan b261 (consBan b262 (consBan b263 (consBan b264 (consBan b265 (consBan b266 (consBan b267 (consBan b268 (consBan b269 (consBan b270 (consBan b271 (consBan b272 (consBan b273 (consBan b274 (consBan b275 (consBan b276 (consBan b277 (consBan b278 (consBan b279 (consBan b280 (consBan b281 (consBan b282 (consBan b283 (nilBan 25 5))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w7 : Wide 25 6 v232 := viaSub (ws := [v232]) (consBan b284 (nilBan 25 6)) (by decide) (by decide +kernel)
theorem b285 : Ban 50 7 v231 := smallByCut p63_47 w7
theorem b286 : Ban 50 7 v283 := smallByCut p63_47 w7
theorem b287 : Ban 50 7 v284 := smallByCut p63_13 w0
theorem b336 : Ban 25 5 v333 := checkedSmall
theorem b337 : Ban 25 5 v334 := checkedSmall
theorem b338 : Ban 25 5 v335 := checkedSmall
theorem b339 : Ban 25 5 v336 := checkedSmall
theorem b340 : Ban 25 5 v337 := checkedSmall
theorem b341 : Ban 25 5 v338 := checkedSmall
theorem b342 : Ban 25 5 v339 := checkedSmall
theorem b343 : Ban 25 5 v340 := checkedSmall
theorem b344 : Ban 25 5 v341 := checkedSmall
theorem b345 : Ban 25 5 v342 := checkedSmall
theorem b346 : Ban 25 5 v343 := checkedSmall
theorem b347 : Ban 25 5 v344 := checkedSmall
theorem b348 : Ban 25 5 v345 := checkedSmall
theorem b349 : Ban 25 5 v346 := checkedSmall
theorem b350 : Ban 25 5 v347 := checkedSmall
theorem b351 : Ban 25 5 v348 := checkedSmall
theorem b352 : Ban 25 5 v349 := checkedSmall
theorem b353 : Ban 25 5 v350 := checkedSmall
theorem b354 : Ban 25 5 v351 := checkedSmall
theorem b355 : Ban 25 5 v352 := checkedSmall
theorem b356 : Ban 25 5 v353 := checkedSmall
theorem b357 : Ban 25 5 v354 := checkedSmall
theorem b358 : Ban 25 5 v355 := checkedSmall
theorem b359 : Ban 25 5 v356 := checkedSmall
theorem b360 : Ban 25 5 v357 := checkedSmall
theorem b361 : Ban 25 5 v358 := checkedSmall
theorem b362 : Ban 25 5 v359 := checkedSmall
theorem b363 : Ban 25 5 v360 := checkedSmall
theorem b364 : Ban 25 5 v361 := checkedSmall
theorem b365 : Ban 25 5 v362 := checkedSmall
theorem b366 : Ban 25 5 v363 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b367 : Ban 25 6 v102 := viaBranch (ws := [v333,v334,v335,v336,v337,v338,v339,v104,v340,v341,v342,v343,v344,v345,v150,v346,v103,v347,v348,v349,v350,v351,v352,v353,v354,v355,v356,v357,v358,v359,v360,v361,v362,v363]) (consBan b336 (consBan b337 (consBan b338 (consBan b339 (consBan b340 (consBan b341 (consBan b342 (consBan b102 (consBan b343 (consBan b344 (consBan b345 (consBan b346 (consBan b347 (consBan b348 (consBan b149 (consBan b349 (consBan b101 (consBan b350 (consBan b351 (consBan b352 (consBan b353 (consBan b354 (consBan b355 (consBan b356 (consBan b357 (consBan b358 (consBan b359 (consBan b360 (consBan b361 (consBan b362 (consBan b363 (consBan b364 (consBan b365 (consBan b366 (nilBan 25 5))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w10 : Wide 25 6 v102 := viaSub (ws := [v96,v102]) (consBan b139 (consBan b367 (nilBan 25 6))) (by decide) (by decide +kernel)
theorem b288 : Ban 50 7 v285 := smallByCut p63_31 w10
theorem b289 : Ban 50 7 v286 := smallByCut p63_13 w0
theorem b290 : Ban 50 7 v287 := smallByCut p63_31 w10
theorem b291 : Ban 26 5 v289 := checkedSmall
theorem b292 : Ban 26 5 v290 := checkedSmall
theorem b293 : Ban 26 5 v291 := checkedSmall
theorem b294 : Ban 26 5 v292 := checkedSmall
theorem b295 : Ban 26 5 v293 := checkedSmall
theorem b296 : Ban 26 5 v294 := checkedSmall
theorem b297 : Ban 26 5 v295 := checkedSmall
theorem b298 : Ban 26 5 v296 := checkedSmall
theorem b299 : Ban 26 5 v297 := checkedSmall
theorem b300 : Ban 26 5 v298 := checkedSmall
theorem b301 : Ban 26 5 v299 := checkedSmall
theorem b302 : Ban 26 5 v300 := checkedSmall
theorem b303 : Ban 26 5 v301 := checkedSmall
theorem b304 : Ban 26 5 v302 := checkedSmall
theorem b305 : Ban 26 5 v303 := checkedSmall
theorem b306 : Ban 26 5 v304 := checkedSmall
theorem b307 : Ban 26 5 v305 := checkedSmall
theorem b308 : Ban 26 5 v306 := checkedSmall
theorem b309 : Ban 26 5 v307 := checkedSmall
theorem b310 : Ban 26 5 v308 := checkedSmall
theorem b311 : Ban 26 5 v309 := checkedSmall
theorem b312 : Ban 26 5 v310 := checkedSmall
theorem b313 : Ban 26 5 v311 := checkedSmall
theorem b314 : Ban 26 5 v312 := checkedSmall
theorem b315 : Ban 26 5 v313 := checkedSmall
theorem b316 : Ban 26 5 v314 := checkedSmall
theorem b317 : Ban 26 5 v315 := checkedSmall
theorem b318 : Ban 26 5 v316 := checkedSmall
theorem b319 : Ban 26 5 v317 := checkedSmall
theorem b320 : Ban 26 5 v318 := checkedSmall
theorem b321 : Ban 26 5 v319 := checkedSmall
theorem b322 : Ban 26 5 v320 := checkedSmall
theorem b323 : Ban 26 5 v321 := checkedSmall
theorem b324 : Ban 26 5 v322 := checkedSmall
theorem b325 : Ban 26 5 v323 := checkedSmall
theorem b326 : Ban 26 5 v324 := checkedSmall
theorem b327 : Ban 26 5 v325 := checkedSmall
theorem b328 : Ban 26 5 v326 := checkedSmall
theorem b329 : Ban 26 5 v327 := checkedSmall
theorem b330 : Ban 26 5 v328 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b331 : Ban 26 6 v20 := viaBranch (ws := [v289,v17,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v63,v306,v307,v308,v183,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v325,v326,v327,v328]) (consBan b291 (consBan b14 (consBan b292 (consBan b293 (consBan b294 (consBan b295 (consBan b296 (consBan b297 (consBan b298 (consBan b299 (consBan b300 (consBan b301 (consBan b302 (consBan b303 (consBan b304 (consBan b305 (consBan b306 (consBan b307 (consBan b61 (consBan b308 (consBan b309 (consBan b310 (consBan b183 (consBan b311 (consBan b312 (consBan b313 (consBan b314 (consBan b315 (consBan b316 (consBan b317 (consBan b318 (consBan b319 (consBan b320 (consBan b321 (consBan b322 (consBan b323 (consBan b324 (consBan b325 (consBan b326 (consBan b327 (consBan b328 (consBan b329 (consBan b330 (nilBan 26 5)))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w9 : Wide 26 6 v20 := viaSub (ws := [v20]) (consBan b331 (nilBan 26 6)) (by decide) (by decide +kernel)
theorem b332 : Ban 50 7 v288 := smallByCut p63_55 w9
theorem b333 : Ban 50 7 v329 := smallByCut p63_31 w10
theorem b334 : Ban 50 7 v330 := smallByCut p63_13 w0
theorem b335 : Ban 50 7 v331 := smallByCut p63_13 w0
theorem b368 : Ban 50 7 v332 := smallByCut p63_31 w10
theorem b369 : Ban 50 7 v364 := smallByCut p63_13 w0
theorem b370 : Ban 50 7 v365 := smallByCut p63_51 w3
theorem b371 : Ban 50 7 v366 := smallByCut p63_13 w0
theorem b372 : Ban 50 7 v367 := smallByCut p63_55 w6
theorem b373 : Ban 50 7 v368 := smallByCut p63_13 w0
theorem b374 : Ban 50 7 v369 := smallByCut p63_51 w3
theorem b375 : Ban 50 7 v370 := smallByCut p63_13 w0
theorem b376 : Ban 50 7 v371 := smallByCut p63_13 w0
theorem b377 : Ban 50 7 v372 := smallByCut p63_13 w0
theorem b378 : Ban 50 7 v373 := smallByCut p63_13 w0
theorem b379 : Ban 50 7 v374 := smallByCut p63_13 w0
theorem b380 : Ban 50 7 v375 := smallByCut p63_13 w0
theorem b381 : Ban 50 7 v376 := smallByCut p63_13 w0
theorem b382 : Ban 50 7 v377 := smallByCut p63_13 w0
theorem b383 : Ban 50 7 v378 := smallByCut p63_51 w3
theorem b384 : Ban 50 7 v379 := smallByCut p63_51 w3
theorem b385 : Ban 50 7 v380 := smallByCut p63_51 w3
theorem b386 : Ban 50 7 v381 := smallByCut p63_51 w3
theorem b387 : Ban 50 7 v382 := smallByCut p63_13 w0
theorem b388 : Ban 50 6 v384 := smallByCut p63_13 w0
theorem b389 : Ban 50 6 v385 := checkedSmall
theorem b390 : Ban 50 6 v386 := checkedSmall
theorem b391 : Ban 50 6 v387 := smallByCut p63_13 w0
theorem b392 : Ban 50 6 v388 := smallByCut p63_51 w3
theorem b393 : Ban 50 6 v389 := smallByCut p63_51 w3
theorem b394 : Ban 50 6 v390 := smallByCut p63_51 w3
theorem b395 : Ban 50 6 v391 := smallByCut p63_51 w3
theorem b396 : Ban 50 6 v392 := smallByCut p63_51 w3
theorem b397 : Ban 50 6 v393 := smallByCut p63_51 w3
theorem b398 : Ban 50 6 v394 := smallByCut p63_51 w3
theorem b399 : Ban 50 6 v395 := smallByCut p63_51 w3
theorem b400 : Ban 50 6 v396 := checkedSmall
theorem b401 : Ban 50 6 v397 := checkedSmall
theorem b402 : Ban 50 6 v398 := checkedSmall
theorem b403 : Ban 50 6 v399 := checkedSmall
theorem solidb130 : Wide 25 5 v132 := solid b130
theorem b404 : Ban 50 6 v400 := smallByCut p63_31 solidb130
theorem b405 : Ban 50 6 v401 := smallByCut p63_13 w0
theorem b406 : Ban 50 6 v402 := smallByCut p63_31 solidb130
theorem solidb326 : Wide 26 5 v324 := solid b326
theorem b407 : Ban 50 6 v403 := smallByCut p63_55 solidb326
theorem b408 : Ban 50 6 v404 := smallByCut p63_31 solidb130
theorem b409 : Ban 50 6 v405 := smallByCut p63_13 w0
theorem b410 : Ban 50 6 v406 := smallByCut p63_13 w0
theorem solidb350 : Wide 25 5 v347 := solid b350
theorem b411 : Ban 50 6 v407 := smallByCut p63_31 solidb350
theorem b412 : Ban 50 6 v408 := smallByCut p63_51 w3
theorem b413 : Ban 50 6 v409 := smallByCut p63_13 w0
theorem b414 : Ban 50 6 v410 := smallByCut p63_51 w3
theorem b415 : Ban 50 6 v411 := smallByCut p63_51 w3
theorem b416 : Ban 50 6 v412 := smallByCut p63_13 w0
theorem b417 : Ban 50 6 v413 := smallByCut p63_51 w3
theorem b418 : Ban 50 6 v414 := smallByCut p63_13 w0
theorem b419 : Ban 50 6 v415 := smallByCut p63_51 w3
theorem b420 : Ban 50 6 v416 := smallByCut p63_13 w0
theorem b421 : Ban 50 6 v417 := checkedSmall
theorem b422 : Ban 50 6 v418 := smallByCut p63_13 w0
theorem b423 : Ban 50 6 v419 := checkedSmall
theorem b424 : Ban 50 6 v420 := smallByCut p63_13 w0
theorem b425 : Ban 50 6 v421 := smallByCut p63_13 w0
theorem b426 : Ban 50 6 v422 := smallByCut p63_13 w0
theorem b427 : Ban 50 6 v423 := smallByCut p63_13 w0
theorem b428 : Ban 50 6 v424 := smallByCut p63_51 w3
theorem b429 : Ban 50 6 v425 := smallByCut p63_51 w3
theorem b430 : Ban 50 6 v426 := smallByCut p63_51 w3
theorem b431 : Ban 50 6 v427 := smallByCut p63_51 w3
theorem b432 : Ban 50 6 v428 := smallByCut p63_13 w0
theorem b433 : Ban 50 6 v429 := smallByCut p63_13 w0
theorem b434 : Ban 50 6 v430 := smallByCut p63_13 w0
theorem b435 : Ban 50 6 v431 := smallByCut p63_13 w0
theorem b436 : Ban 50 6 v432 := smallByCut p63_51 w3
theorem b437 : Ban 50 6 v433 := smallByCut p63_51 w3
theorem b438 : Ban 50 6 v434 := smallByCut p63_51 w3
theorem b439 : Ban 50 6 v435 := smallByCut p63_51 w3
theorem b440 : Ban 50 6 v436 := smallByCut p63_13 w0
theorem b441 : Ban 50 6 v437 := smallByCut p63_51 w3
theorem b442 : Ban 50 6 v438 := smallByCut p63_51 w3
theorem b443 : Ban 50 6 v439 := smallByCut p63_51 w3
theorem b444 : Ban 50 6 v440 := smallByCut p63_51 w3
theorem b445 : Ban 50 6 v441 := smallByCut p63_13 w0
theorem b446 : Ban 50 6 v442 := smallByCut p63_51 w3
theorem b447 : Ban 50 6 v443 := smallByCut p63_51 w3
theorem b448 : Ban 50 6 v444 := smallByCut p63_51 w3
theorem b449 : Ban 50 6 v445 := smallByCut p63_51 w3
theorem b450 : Ban 50 6 v446 := smallByCut p63_13 w0
theorem b451 : Ban 50 6 v447 := smallByCut p63_13 w0
theorem b452 : Ban 50 6 v448 := smallByCut p63_31 solidb130
theorem b453 : Ban 50 6 v449 := smallByCut p63_31 solidb130
theorem b454 : Ban 50 6 v450 := smallByCut p63_13 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b455 : Ban 50 7 v383 := viaBranch (ws := [v384,v385,v386,v387,v388,v389,v390,v391,v392,v393,v394,v395,v396,v397,v398,v399,v400,v401,v402,v403,v404,v405,v406,v407,v408,v409,v410,v411,v412,v413,v414,v415,v416,v417,v418,v419,v420,v421,v422,v423,v424,v425,v426,v427,v428,v429,v430,v431,v432,v433,v434,v435,v436,v437,v438,v439,v440,v441,v442,v443,v444,v445,v446,v447,v448,v449,v450]) (consBan b388 (consBan b389 (consBan b390 (consBan b391 (consBan b392 (consBan b393 (consBan b394 (consBan b395 (consBan b396 (consBan b397 (consBan b398 (consBan b399 (consBan b400 (consBan b401 (consBan b402 (consBan b403 (consBan b404 (consBan b405 (consBan b406 (consBan b407 (consBan b408 (consBan b409 (consBan b410 (consBan b411 (consBan b412 (consBan b413 (consBan b414 (consBan b415 (consBan b416 (consBan b417 (consBan b418 (consBan b419 (consBan b420 (consBan b421 (consBan b422 (consBan b423 (consBan b424 (consBan b425 (consBan b426 (consBan b427 (consBan b428 (consBan b429 (consBan b430 (consBan b431 (consBan b432 (consBan b433 (consBan b434 (consBan b435 (consBan b436 (consBan b437 (consBan b438 (consBan b439 (consBan b440 (consBan b441 (consBan b442 (consBan b443 (consBan b444 (consBan b445 (consBan b446 (consBan b447 (consBan b448 (consBan b449 (consBan b450 (consBan b451 (consBan b452 (consBan b453 (consBan b454 (nilBan 50 6)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b456 : Ban 50 7 v451 := smallByCut p63_47 w7
theorem b457 : Ban 50 7 v452 := smallByCut p63_51 w3
theorem b458 : Ban 50 7 v428 := smallByCut p63_47 w7
theorem b459 : Ban 50 7 v453 := smallByCut p63_13 w0
theorem b460 : Ban 50 7 v454 := smallByCut p63_13 w0
theorem b461 : Ban 50 6 v456 := smallByCut p63_13 w0
theorem b462 : Ban 50 6 v457 := checkedSmall
theorem b463 : Ban 50 6 v458 := smallByCut p63_31 w2
theorem b464 : Ban 50 6 v459 := smallByCut p63_13 w0
theorem b465 : Ban 50 6 v460 := smallByCut p63_51 w3
theorem b466 : Ban 50 6 v461 := smallByCut p63_51 w3
theorem b467 : Ban 50 6 v462 := smallByCut p63_51 w3
theorem b468 : Ban 50 6 v463 := smallByCut p63_51 w3
theorem b469 : Ban 50 6 v464 := smallByCut p63_51 w3
theorem b470 : Ban 50 6 v465 := smallByCut p63_51 w3
theorem b471 : Ban 50 6 v466 := smallByCut p63_51 w3
theorem b472 : Ban 50 6 v467 := smallByCut p63_51 w3
theorem b473 : Ban 50 6 v468 := smallByCut p63_13 w0
theorem solidb261 : Wide 25 5 v260 := solid b261
theorem b474 : Ban 50 6 v469 := smallByCut p63_47 solidb261
theorem b475 : Ban 50 6 v470 := smallByCut p63_47 solidb261
theorem b476 : Ban 50 6 v471 := smallByCut p63_13 w0
theorem b477 : Ban 50 6 v472 := checkedSmall
theorem b478 : Ban 50 6 v473 := checkedSmall
theorem b479 : Ban 50 6 v474 := checkedSmall
theorem b480 : Ban 50 6 v475 := smallByCut p63_31 w5
theorem b481 : Ban 50 6 v476 := smallByCut p63_31 w5
theorem b482 : Ban 50 6 v477 := checkedSmall
theorem b483 : Ban 50 6 v478 := smallByCut p63_13 w0
theorem b484 : Ban 50 6 v479 := smallByCut p63_51 w3
theorem b485 : Ban 50 6 v480 := smallByCut p63_13 w0
theorem b486 : Ban 50 6 v481 := smallByCut p63_51 w3
theorem b487 : Ban 50 6 v482 := smallByCut p63_13 w0
theorem b488 : Ban 50 6 v483 := smallByCut p63_51 w3
theorem b489 : Ban 50 6 v484 := smallByCut p63_13 w0
theorem b490 : Ban 50 6 v485 := smallByCut p63_51 w3
theorem b491 : Ban 50 6 v486 := smallByCut p63_13 w0
theorem b492 : Ban 50 6 v487 := smallByCut p63_13 w0
theorem b493 : Ban 50 6 v488 := smallByCut p63_13 w0
theorem b494 : Ban 50 6 v489 := smallByCut p63_13 w0
theorem b495 : Ban 50 6 v490 := smallByCut p63_13 w0
theorem b496 : Ban 50 6 v491 := smallByCut p63_31 w10
theorem b497 : Ban 50 6 v492 := smallByCut p63_13 w0
theorem b498 : Ban 50 6 v493 := checkedSmall
theorem b499 : Ban 50 6 v494 := smallByCut p63_51 w3
theorem b500 : Ban 50 6 v495 := smallByCut p63_51 w3
theorem b501 : Ban 50 6 v496 := smallByCut p63_51 w3
theorem b502 : Ban 50 6 v497 := smallByCut p63_51 w3
theorem b503 : Ban 50 6 v498 := smallByCut p63_13 w0
theorem b504 : Ban 50 6 v499 := smallByCut p63_51 w3
theorem b505 : Ban 50 6 v500 := smallByCut p63_51 w3
theorem b506 : Ban 50 6 v501 := smallByCut p63_51 w3
theorem b507 : Ban 50 6 v502 := smallByCut p63_13 w0
theorem b508 : Ban 50 6 v503 := smallByCut p63_13 w0
theorem b509 : Ban 50 6 v504 := smallByCut p63_13 w0
theorem b510 : Ban 50 6 v505 := smallByCut p63_13 w0
theorem b511 : Ban 50 6 v506 := smallByCut p63_13 w0
theorem b512 : Ban 50 6 v507 := smallByCut p63_51 w3
theorem b513 : Ban 50 6 v508 := smallByCut p63_51 w3
theorem b514 : Ban 50 6 v509 := smallByCut p63_13 w0
theorem b515 : Ban 50 6 v510 := smallByCut p63_51 w3
theorem b516 : Ban 50 6 v511 := smallByCut p63_51 w3
theorem b517 : Ban 50 6 v512 := smallByCut p63_51 w3
theorem b518 : Ban 50 6 v513 := smallByCut p63_51 w3
theorem b519 : Ban 50 6 v514 := smallByCut p63_51 w3
theorem b520 : Ban 50 6 v515 := smallByCut p63_51 w3
theorem b521 : Ban 50 6 v516 := smallByCut p63_13 w0
theorem b522 : Ban 50 6 v517 := smallByCut p63_47 solidb261
theorem b523 : Ban 50 6 v518 := smallByCut p63_13 w0
theorem b524 : Ban 50 6 v519 := smallByCut p63_47 solidb261
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b525 : Ban 50 7 v455 := viaBranch (ws := [v456,v457,v458,v459,v460,v461,v462,v463,v464,v465,v466,v467,v468,v469,v470,v471,v472,v473,v474,v475,v476,v477,v478,v479,v480,v481,v482,v483,v484,v485,v486,v487,v488,v489,v490,v491,v492,v493,v494,v495,v496,v497,v498,v432,v499,v500,v501,v502,v503,v504,v505,v506,v507,v508,v509,v510,v511,v512,v513,v514,v515,v516,v517,v518,v519]) (consBan b461 (consBan b462 (consBan b463 (consBan b464 (consBan b465 (consBan b466 (consBan b467 (consBan b468 (consBan b469 (consBan b470 (consBan b471 (consBan b472 (consBan b473 (consBan b474 (consBan b475 (consBan b476 (consBan b477 (consBan b478 (consBan b479 (consBan b480 (consBan b481 (consBan b482 (consBan b483 (consBan b484 (consBan b485 (consBan b486 (consBan b487 (consBan b488 (consBan b489 (consBan b490 (consBan b491 (consBan b492 (consBan b493 (consBan b494 (consBan b495 (consBan b496 (consBan b497 (consBan b498 (consBan b499 (consBan b500 (consBan b501 (consBan b502 (consBan b503 (consBan b436 (consBan b504 (consBan b505 (consBan b506 (consBan b507 (consBan b508 (consBan b509 (consBan b510 (consBan b511 (consBan b512 (consBan b513 (consBan b514 (consBan b515 (consBan b516 (consBan b517 (consBan b518 (consBan b519 (consBan b520 (consBan b521 (consBan b522 (consBan b523 (consBan b524 (nilBan 50 6)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b526 : Ban 50 7 v520 := smallByCut p63_31 w10
theorem b527 : Ban 50 7 v521 := smallByCut p63_51 w3
theorem b528 : Ban 50 7 v503 := smallByCut p63_31 w10
theorem b529 : Ban 50 7 v522 := smallByCut p63_13 w0
theorem b530 : Ban 50 7 v523 := smallByCut p63_13 w0
theorem b531 : Ban 50 7 v524 := smallByCut p63_47 w7
theorem b532 : Ban 50 7 v525 := smallByCut p63_51 w3
theorem b533 : Ban 50 7 v526 := smallByCut p63_13 w0
theorem b534 : Ban 50 7 v527 := smallByCut p63_13 w0
theorem b535 : Ban 50 7 v528 := smallByCut p63_55 w6
theorem b536 : Ban 50 7 v529 := smallByCut p63_31 w10
theorem b537 : Ban 50 7 v530 := smallByCut p63_51 w3
theorem b538 : Ban 50 7 v531 := smallByCut p63_31 w10
theorem b539 : Ban 50 7 v532 := smallByCut p63_13 w0
theorem b540 : Ban 50 7 v533 := smallByCut p63_13 w0
theorem b541 : Ban 50 7 v534 := smallByCut p63_13 w0
theorem b542 : Ban 50 7 v535 := smallByCut p63_13 w0
theorem b543 : Ban 50 7 v536 := smallByCut p63_13 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b544 : Ban 50 8 v0 := viaBranch (ws := [v1,v3,v95,v172,v173,v175,v203,v225,v226,v227,v228,v229,v230,v231,v283,v284,v285,v286,v287,v288,v329,v330,v331,v332,v364,v365,v366,v367,v368,v369,v370,v371,v372,v373,v374,v375,v376,v377,v378,v379,v380,v381,v382,v383,v451,v452,v428,v453,v454,v455,v520,v521,v503,v522,v523,v524,v525,v526,v527,v528,v529,v530,v531,v532,v533,v534,v535,v536]) (consBan b1 (consBan b94 (consBan b172 (consBan b173 (consBan b175 (consBan b204 (consBan b227 (consBan b228 (consBan b229 (consBan b230 (consBan b231 (consBan b232 (consBan b233 (consBan b285 (consBan b286 (consBan b287 (consBan b288 (consBan b289 (consBan b290 (consBan b332 (consBan b333 (consBan b334 (consBan b335 (consBan b368 (consBan b369 (consBan b370 (consBan b371 (consBan b372 (consBan b373 (consBan b374 (consBan b375 (consBan b376 (consBan b377 (consBan b378 (consBan b379 (consBan b380 (consBan b381 (consBan b382 (consBan b383 (consBan b384 (consBan b385 (consBan b386 (consBan b387 (consBan b455 (consBan b456 (consBan b457 (consBan b458 (consBan b459 (consBan b460 (consBan b525 (consBan b526 (consBan b527 (consBan b528 (consBan b529 (consBan b530 (consBan b531 (consBan b532 (consBan b533 (consBan b534 (consBan b535 (consBan b536 (consBan b537 (consBan b538 (consBan b539 (consBan b540 (consBan b541 (consBan b542 (consBan b543 (nilBan 50 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem verifiedPin : Wide 50 8 v0 := widen (by decide +kernel) b544
end PEqualNP.Outside.L_meta_16921.Support

namespace PEqualNP.Outside.L_meta_16921.Data
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_16921.Support
def target (x : Fin 6 → Bool) := Nat.testBit (4277074664 * 2 ^ 32 + 4276943584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def posBits : ℕ := 0xf3cebae76d72cb1c71bacb2ba699a69658e38dc71a6996565554d349238c30b2c9247186145
def negBits : ℕ := 0xe34e2ae34d308b0851aa892aa219229218a10d851829845451144340228810a0c8043102101
def sample (bank : ℕ) (i : Fin 50) (j : Fin 6) := bank.testBit (6*i.val+j.val)
def inputs : List ℕ := [0x304582702c429c73e1bc1f3,0x1089128816650d624ce64f99c,0x460228218082b1838f1870e1f,0xb80d805c03503e03f01f80fe0,0xef500077e8003ffc001fff000,0xffefff0000003fffffe000000]
def seeds : List Wire := [(false,0x304582702c429c73e1bc1f3),(false,0x1089128816650d624ce64f99c),(false,0x460228218082b1838f1870e1f),(false,0xb80d805c03503e03f01f80fe0),(false,0xef500077e8003ffc001fff000),(false,0xffefff0000003fffffe000000)]
set_option maxHeartbeats 10000000 in
theorem listed : ∀ i : Fin 50, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (50+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 50, target (sample posBits i)=true ∧ target (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 50, ∀ b∈inputs, b.testBit i.val≠b.testBit (50+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 50 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 6 C=target) :
    ∃ k≤C.gates.countP counted, Live 50 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 6 → Bool) : C.eval (List.ofFn x)=target x := congrFun eq x
  have good : Good 50 out.2 := by
    intro i hi same
    let j : Fin 50 := ⟨i,hi⟩
    have diff : read i out=read (50+i) out := by
      change (out.1 != out.2.testBit i) = (out.1 != out.2.testBit (50+i))
      rw [same]
    have p := ev i;have n := ev (50+i)
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
def restrictRows : Projection 50 50 := pick (List.range 50) (by decide) (by decide) (by decide)
set_option maxHeartbeats 8000000 in
theorem core_floor : Wide 50 8 restricted := verifiedPin
theorem six_floor : Ban 50 8 inputs := viaCut restrictRows core_floor (by decide) (by decide +kernel) (by decide +kernel)
def witness : Circuit := ⟨[⟨.or,[0,1]⟩, ⟨.or,[0,2]⟩, ⟨.and,[1,4]⟩, ⟨.or,[1,4]⟩, ⟨.and,[9,5]⟩, ⟨.or,[2,10]⟩, ⟨.and,[6,11]⟩, ⟨.or,[12,3]⟩, ⟨.and,[7,13]⟩, ⟨.or,[8,14]⟩],15⟩
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
end PEqualNP.Outside.L_meta_16921.Data

theorem PEqualNP.Outside.L_meta_16921 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4276943584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4276943584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_16921.Data.mono_enough
