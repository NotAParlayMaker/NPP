import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12889.Support

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

def t0 := 0x244c409f3f3
def t1 := 0xc91218764c9f
def t2 := 0x6162c63878f1c
def t3 := 0xb603b03f80fe0
def t4 := 0xdbd8003fff000
def v0 := [t0,t1,t2,t3,t4]
def t5 := 0x4093
def v1 := [t5,t0,t1,t2,t3,t4]
def t6 := 0xd51ff
def t7 := 0x62ae3f
def t8 := 0xb4cfcc
def t9 := 0xdb0ff0
def v2 := [t6,t7,t8,t9]
def p47_46 : Projection 26 12 := pick [2,3,10,11,17,18,20,21,22,23,24,25] rfl (by decide +kernel) (by decide)
def t10 := 0xcb56dc7fffff
def v3 := [t0,t1,t10,t2,t3,t4]
def t11 := 0x251ff
def t12 := 0x692e93
def t13 := 0xb18f1c
def t14 := 0xdc0fe0
def v4 := [t11,t12,t13,t14]
def t15 := 0x93
def v5 := [t15,t11,t12,t13,t14]
def t16 := 0x6b7fff
def v6 := [t11,t12,t16,t13,t14]
def t17 := 0x2516c
def v7 := [t17,t11,t12,t13,t14]
def t18 := 0x692e00
def v8 := [t11,t18,t12,t13,t14]
def t19 := 0x11c
def v9 := [t19,t11,t12,t13,t14]
def t20 := 0xb3dfff
def v10 := [t11,t12,t13,t20,t14]
def t21 := 0x250e3
def v11 := [t21,t11,t12,t13,t14]
def t22 := 0xb18e00
def v12 := [t11,t12,t22,t13,t14]
def t23 := 0x1e0
def v13 := [t23,t11,t12,t13,t14]
def t24 := 0xde5fff
def v14 := [t11,t12,t13,t14,t24]
def t25 := 0x2501f
def v15 := [t25,t11,t12,t13,t14]
def t26 := 0xdc0e00
def v16 := [t11,t12,t13,t26,t14]
def t27 := 0x210e10
def v17 := [t11,t27,t12,t13,t14]
def t28 := 0xf9af9f
def v18 := [t11,t12,t13,t14,t28]
def t29 := 0x482083
def v19 := [t11,t29,t12,t13,t14]
def t30 := 0x90810c
def v20 := [t11,t12,t30,t13,t14]
def t31 := 0x480e80
def v21 := [t11,t31,t12,t13,t14]
def t32 := 0xfd2ff3
def v22 := [t11,t12,t13,t14,t32]
def t33 := 0x212013
def v23 := [t11,t33,t12,t13,t14]
def t34 := 0x940160
def v24 := [t11,t12,t34,t13,t14]
def t35 := 0x900f00
def v25 := [t11,t12,t35,t13,t14]
def t36 := 0xfd8ffc
def v26 := [t11,t12,t13,t14,t36]
def t37 := 0x21801c
def v27 := [t11,t37,t12,t13,t14]
def t38 := 0x4c00e0
def v28 := [t11,t38,t12,t13,t14]
def v29 := [t15,t16,t13,t14]
def v30 := [t15,t11,t16,t13,t14]
def v31 := [t15,t12,t16,t13,t14]
def v32 := [t17,t11,t16,t13,t14]
def v33 := [t18,t12,t16,t13,t14]
def v34 := [t11,t16,t13,t14,t28]
def v35 := [t11,t29,t16,t13,t14]
def v36 := [t11,t16,t13,t14,t32]
def v37 := [t11,t33,t16,t13,t14]
def t39 := 0x210f1c
def v38 := [t11,t39,t12,t14]
def v39 := [t11,t39,t12,t16,t14]
def v40 := [t11,t39,t12,t13,t14]
def t40 := 0xfbffff
def v41 := [t11,t12,t13,t14,t40]
def t41 := 0x4a70e3
def v42 := [t11,t41,t12,t14]
def v43 := [t11,t41,t12,t16,t14]
def v44 := [t11,t41,t12,t13,t14]
def t42 := 0x908000
def v45 := [t11,t12,t42,t13,t14]
def t43 := 0x480fe0
def v46 := [t11,t43,t12,t13]
def v47 := [t11,t43,t12,t16,t13]
def v48 := [t11,t43,t12,t13,t14]
def t44 := 0xff7fff
def v49 := [t11,t12,t13,t14,t44]
def t45 := 0x23701f
def v50 := [t11,t45,t12,t13]
def v51 := [t11,t45,t12,t16,t13]
def v52 := [t11,t45,t12,t13,t14]
def t46 := 0x940000
def v53 := [t11,t12,t46,t13,t14]
def p47_43 : Projection 26 12 := pick [0,1,5,6,7,12,13,14,19,20,21,22] rfl (by decide +kernel) (by decide)
def t47 := 0x244c409b360
def v54 := [t47,t0,t1,t2,t3,t4]
def t48 := 0xc91218760c0c
def v55 := [t0,t48,t1,t2,t3,t4]
def t49 := 0x551ff
def t50 := 0x6ccecc
def t51 := 0xb0af0f
def t52 := 0xda0ff0
def v56 := [t49,t50,t51,t52]
def p47_45 : Projection 26 12 := pick [5,6,8,9,12,13,15,16,19,23,24,25] rfl (by decide +kernel) (by decide)
def t53 := 0x20440018310
def v57 := [t53,t0,t1,t2,t3,t4]
def t54 := 0x6166ce78fffff
def v58 := [t0,t1,t54,t3,t4]
def v59 := [t5,t0,t1,t54,t3,t4]
def v60 := [t1,t10,t54,t3,t4]
def v61 := [t0,t1,t10,t54,t3,t4]
def v62 := [t47,t1,t54,t3,t4]
def v63 := [t47,t0,t1,t54,t3,t4]
def v64 := [t0,t48,t1,t54,t3,t4]
def t55 := 0x6142823860c0c
def v65 := [t0,t1,t55,t3,t4]
def v66 := [t1,t55,t54,t3,t4]
def v67 := [t0,t1,t55,t54,t3,t4]
def t56 := 0x803e0
def v68 := [t56,t0,t1,t54,t3,t4]
def t57 := 0xb627fc7f9fff3
def v69 := [t0,t1,t54,t3,t57,t4]
def t58 := 0x244c401f013
def v70 := [t58,t0,t1,t54,t3,t4]
def t59 := 0xb603b03f00c00
def v71 := [t0,t1,t54,t59,t3,t4]
def t60 := 0x9f000
def v72 := [t60,t0,t1,t54,t3,t4]
def t61 := 0xdbfc4c7fff3f3
def v73 := [t0,t1,t54,t3,t4,t61]
def t62 := 0x244c40003f3
def v74 := [t62,t0,t1,t54,t3,t4]
def t63 := 0xdbd8003f60000
def v75 := [t0,t1,t54,t3,t63,t4]
def t64 := 0x64c9f
def v76 := [t64,t0,t1,t54,t3,t4]
def t65 := 0x6df7effffffff
def v77 := [t0,t1,t54,t65,t3,t4]
def t66 := 0xc91218700000
def v78 := [t0,t66,t1,t54,t3,t4]
def t67 := 0x6166ce789b360
def v79 := [t0,t1,t67,t54,t3,t4]
def t68 := 0x401200700c80
def v80 := [t0,t68,t1,t54,t3,t4]
def t69 := 0xbe93b1bfe4fff
def v81 := [t0,t1,t54,t3,t69,t4]
def t70 := 0x89001806401f
def v82 := [t0,t70,t1,t54,t3,t4]
def t71 := 0xb202903880360
def v83 := [t0,t1,t54,t71,t3,t4]
def t72 := 0x890000764000
def v84 := [t0,t72,t1,t54,t3,t4]
def t73 := 0xdfd921bfffc9f
def v85 := [t0,t1,t54,t3,t4,t73]
def t74 := 0x401218000c9f
def v86 := [t0,t74,t1,t54,t3,t4]
def t75 := 0xd34800389b000
def v87 := [t0,t1,t54,t3,t75,t4]
def t76 := 0x2002803880fe0
def v88 := [t0,t1,t76,t54,t3,t4]
def t77 := 0xf767fe7ffffff
def v89 := [t0,t1,t54,t3,t4,t77]
def t78 := 0x41644e407f01f
def v90 := [t0,t1,t78,t54,t3,t4]
def t79 := 0x9601300700000
def v91 := [t0,t1,t54,t79,t3,t4]
def t80 := 0x41400038ff000
def v92 := [t0,t1,t80,t54,t3,t4]
def t81 := 0xfbfece7ffffff
def v93 := [t0,t1,t54,t3,t4,t81]
def t82 := 0x2026ce4000fff
def v94 := [t0,t1,t82,t54,t3,t4]
def t83 := 0x9a98000700000
def v95 := [t0,t1,t54,t83,t3,t4]
def t84 := 0x9200003f80000
def v96 := [t0,t1,t54,t84,t3,t4]
def t85 := 0xffdbb03ffffe0
def v97 := [t0,t1,t54,t3,t4,t85]
def t86 := 0x2403b00000fe0
def v98 := [t0,t1,t86,t54,t3,t4]
def t87 := 0x49d800007f000
def v99 := [t0,t1,t87,t54,t3,t4]
def v100 := [t0,t1,t2,t54,t3,t4]
def t88 := 0x40840870e3
def v101 := [t88,t0,t1,t2,t3,t4]
def v102 := [t0,t1,t55,t2,t3,t4]
def v103 := [t56,t0,t1,t2,t3,t4]
def v104 := [t0,t1,t2,t3,t57,t4]
def map43_2 : Projection 12 12 := pick [2,3,0,1,4,5,6,8,7,9,11,10] rfl (by decide +kernel) (by decide)
def v105 := [t58,t0,t1,t2,t3,t4]
def v106 := [t62,t0,t1,t2,t3,t4]
def map47_1 : Projection 26 26 := pick [0,1,2,3,4,12,13,14,15,16,17,18,5,6,7,8,9,10,11,19,21,20,22,24,23,25] rfl (by decide +kernel) (by decide)
def v107 := [t0,t1,t2,t59,t3,t4]
def v108 := [t15,t11,t18,t13,t14]
def v109 := [t17,t18,t13,t14]
def v110 := [t17,t11,t18,t13,t14]
def v111 := [t17,t18,t12,t13,t14]
def t89 := 0x210e00
def v112 := [t11,t89,t12,t13,t14]
def t90 := 0xf9af1c
def v113 := [t11,t12,t13,t14,t90]
def t91 := 0x482000
def v114 := [t11,t91,t12,t13,t14]
def t92 := 0x90811c
def v115 := [t11,t12,t92,t13,t14]
def t93 := 0x480e00
def v116 := [t11,t93,t12,t13,t14]
def t94 := 0xfd2fe0
def v117 := [t11,t12,t13,t14,t94]
def t95 := 0x212000
def v118 := [t11,t95,t12,t13,t14]
def t96 := 0x9401e0
def v119 := [t11,t12,t96,t13,t14]
def v120 := [t11,t18,t13,t14,t28]
def v121 := [t11,t29,t18,t13,t14]
def v122 := [t11,t18,t13,t14,t32]
def v123 := [t11,t33,t18,t13,t14]
def v124 := [t60,t0,t1,t2,t3,t4]
def v125 := [t0,t1,t2,t3,t4,t61]
def v126 := [t0,t1,t2,t3,t63,t4]
def t97 := 0x60c1c
def v127 := [t97,t0,t1,t2,t3,t4]
def t98 := 0x6df3e7bf7cf9f
def v128 := [t0,t1,t2,t98,t3,t4]
def t99 := 0xc91218704083
def v129 := [t0,t99,t1,t2,t3,t4]
def t100 := 0x6162c63818300
def v130 := [t0,t1,t100,t2,t3,t4]
def v131 := [t0,t68,t1,t2,t3,t4]
def v132 := [t0,t72,t1,t2,t3,t4]
def v133 := [t0,t1,t2,t3,t69,t4]
def v134 := [t0,t10,t2,t3,t69,t4]
def v135 := [t0,t48,t2,t3,t69,t4]
def v136 := [t0,t1,t55,t3,t69,t4]
def v137 := [t0,t1,t2,t57,t69,t4]
def v138 := [t0,t1,t2,t59,t69,t4]
def t101 := 0x843f3
def v139 := [t101,t0,t1,t2,t3,t4]
def t102 := 0xbeb7fdfffffff
def v140 := [t0,t1,t2,t3,t102,t4]
def t103 := 0x244c401b000
def v141 := [t103,t0,t1,t2,t3,t4]
def t104 := 0xbe93b1bf60c0c
def v142 := [t0,t1,t2,t3,t104,t4]
def v143 := [t0,t68,t2,t69,t4]
def v144 := [t0,t68,t1,t2,t69,t4]
def v145 := [t0,t68,t2,t3,t69,t4]
def v146 := [t0,t70,t1,t2,t69,t4]
def v147 := [t0,t2,t71,t3,t69,t4]
def v148 := [t0,t1,t2,t71,t3,t4]
def t105 := 0xf763f63ff8ffc
def v149 := [t0,t1,t2,t69,t4,t105]
def t106 := 0x96013007800e0
def v150 := [t0,t1,t2,t106,t69,t4]
def t107 := 0x2002803860f1c
def v151 := [t0,t1,t107,t3,t4]
def v152 := [t0,t1,t107,t2,t3,t4]
def v153 := [t0,t1,t107,t3,t69,t4]
def t108 := 0xfff3f7bffcfff
def v154 := [t0,t1,t2,t3,t4,t108]
def t109 := 0x4160460018000
def v155 := [t0,t1,t109,t2,t3,t4]
def t110 := 0x9e913187840e3
def v156 := [t0,t1,t110,t3,t4]
def v157 := [t0,t1,t2,t110,t3,t4]
def v158 := [t0,t1,t110,t3,t69,t4]
def v159 := [t0,t70,t1,t2,t3,t4]
def v160 := [t0,t1,t2,t84,t69,t4]
def v161 := [t0,t1,t87,t2,t69,t4]
def t111 := 0x9a90003fe4000
def v162 := [t0,t1,t2,t111,t3,t4]
def t112 := 0xffdbb1bffffff
def v163 := [t0,t1,t2,t3,t4,t112]
def t113 := 0x2403b18000fff
def v164 := [t0,t1,t113,t2,t3,t4]
def t114 := 0x414800001b000
def v165 := [t0,t1,t114,t2,t3,t4]
def t115 := 0x1c
def v166 := [t115,t11,t12,t13,t14]
def t116 := 0x23d1ff
def v167 := [t11,t116,t12,t13,t14]
def t117 := 0x251e3
def v168 := [t117,t11,t12,t13,t14]
def t118 := 0x218000
def v169 := [t11,t118,t12,t13,t14]
def v170 := [t11,t37,t12,t20,t14]
def v171 := [t11,t37,t12,t22,t14]
def v172 := [t23,t11,t37,t12,t13]
def v173 := [t25,t11,t37,t12,t13]
def t119 := 0x210010
def v174 := [t11,t119,t12,t13,t14]
def t120 := 0x69ae9f
def v175 := [t11,t120,t13,t14]
def v176 := [t11,t37,t120,t13,t14]
def v177 := [t11,t12,t120,t13,t14]
def t121 := 0x800c
def v178 := [t121,t11,t12,t13,t14]
def t122 := 0x482e83
def v179 := [t11,t122,t13,t14]
def v180 := [t11,t37,t122,t13,t14]
def v181 := [t11,t122,t12,t13,t14]
def v182 := [t11,t37,t12,t35,t14]
def v183 := [t11,t37,t12,t13,t36]
def v184 := [t11,t27,t37,t12,t14]
def v185 := [t11,t37,t29,t12,t14]
def v186 := [t11,t37,t12,t13,t32]
def v187 := [t11,t37,t12,t34,t13]
def v188 := [t11,t37,t38,t12]
def v189 := [t11,t37,t38,t12,t13]
def v190 := [t11,t37,t38,t12,t14]
def map43_5 : Projection 12 12 := pick [5,6,2,3,8,0,1,7,4,11,10,9] rfl (by decide +kernel) (by decide)
def v191 := [t0,t1,t2,t3,t4,t73]
def v192 := [t0,t74,t1,t2,t3,t4]
def v193 := [t0,t1,t2,t3,t75,t4]
def t123 := 0x2002803800f00
def v194 := [t0,t1,t123,t2,t3,t4]
def v195 := [t0,t1,t2,t3,t4,t105]
def t124 := 0x416046007801c
def v196 := [t0,t1,t124,t2,t3,t4]
def v197 := [t0,t1,t2,t106,t3,t4]
def t125 := 0x4140003878000
def v198 := [t0,t1,t125,t2,t3,t4]
def t126 := 0xfbfac63ffff1c
def v199 := [t0,t1,t2,t3,t4,t126]
def t127 := 0x2022c60000f1c
def v200 := [t0,t1,t127,t2,t3,t4]
def t128 := 0x9a98000787000
def v201 := [t0,t1,t2,t128,t3,t4]
def v202 := [t0,t1,t2,t84,t3,t4]
def v203 := [t0,t1,t55,t84,t3,t4]
def t129 := 0x80000
def v204 := [t129,t0,t1,t2,t3,t4]
def t130 := 0x92244c7f9f3f3
def v205 := [t0,t1,t2,t130,t3,t4]
def t131 := 0x244c401f3f3
def v206 := [t131,t0,t1,t2,t3,t4]
def t132 := 0x9200003f00000
def v207 := [t0,t1,t2,t132,t3,t4]
def v208 := [t56,t0,t1,t2,t84,t4]
def v209 := [t58,t0,t1,t2,t84,t4]
def v210 := [t60,t0,t1,t2,t84,t3]
def v211 := [t62,t0,t1,t2,t84,t3]
def t133 := 0x700000
def v212 := [t133,t0,t1,t2,t3,t4]
def t134 := 0x9e9121bfe4c9f
def v213 := [t0,t1,t2,t134,t3,t4]
def t135 := 0xc91218064c9f
def v214 := [t0,t135,t1,t2,t3,t4]
def t136 := 0x9200003880000
def v215 := [t0,t1,t2,t136,t3,t4]
def v216 := [t0,t1,t2,t84,t71,t4]
def v217 := [t0,t1,t2,t84,t3,t73]
def v218 := [t0,t1,t2,t84,t3,t75]
def t137 := 0x3800000
def v219 := [t137,t0,t1,t2,t3,t4]
def t138 := 0xf362c63ff8f1c
def v220 := [t0,t1,t2,t3,t4,t138]
def t139 := 0x6162c60078f1c
def v221 := [t0,t1,t139,t2,t3,t4]
def t140 := 0x9200000780000
def v222 := [t0,t1,t2,t140,t3,t4]
def v223 := [t0,t1,t86,t2,t84,t4]
def v224 := [t0,t1,t86,t2,t3,t4]
def v225 := [t0,t1,t87,t2,t84,t3]
def v226 := [t0,t1,t87,t2,t3,t4]
def v227 := [t0,t1,t2,t84,t85]
def v228 := [t0,t1,t2,t84,t3,t85]
def v229 := [t0,t1,t2,t84,t4,t85]
def v230 := [t0,t1,t2,t3,t4,t85]
def v231 := [t0,t1,t55,t3,t4,t85]
def v232 := [t0,t1,t2,t57,t4,t85]
def v233 := [t0,t1,t2,t59,t4,t85]
def v234 := [t0,t1,t2,t3,t61,t85]
def v235 := [t0,t1,t2,t3,t63,t85]
def t141 := 0x9f3e0
def v236 := [t141,t0,t1,t2,t3,t4]
def t142 := 0xfffffc7fffff3
def v237 := [t0,t1,t2,t3,t4,t142]
def t143 := 0x244c4000013
def v238 := [t143,t0,t1,t2,t3,t4]
def t144 := 0xffdbb03f60c00
def v239 := [t0,t1,t2,t3,t4,t144]
def t145 := 0xc91200764c80
def v240 := [t0,t145,t1,t2,t3,t4]
def t146 := 0x1800001f
def v241 := [t146,t0,t1,t2,t3,t4]
def t147 := 0xf34a90389b360
def v242 := [t0,t1,t2,t3,t4,t147]
def t148 := 0x6142803878f00
def v243 := [t0,t1,t148,t2,t3,t4]
def t149 := 0xfffbf63fffffc
def v244 := [t0,t1,t2,t3,t4,t149]
def t150 := 0x2046000001c
def v245 := [t150,t0,t1,t2,t3,t4]
def t151 := 0x9e993007870e0
def v246 := [t0,t1,t2,t151,t3,t4]
def v247 := [t0,t1,t86,t2,t3,t85]
def v248 := [t0,t1,t87,t2,t4,t85]
theorem b55 : Ban 12 4 v56 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w2 : Wide 12 4 v56 := viaSub (ws := [v56]) (consBan b55 (nilBan 12 4)) (by decide) (by decide +kernel)
theorem b1 : Ban 26 6 v1 := smallByCut p47_45 w2
theorem b2 : Ban 12 4 v5 := checkedSmall
theorem b3 : Ban 12 4 v6 := checkedSmall
theorem b4 : Ban 12 4 v7 := checkedSmall
theorem b5 : Ban 12 4 v8 := checkedSmall
theorem b6 : Ban 12 4 v9 := checkedSmall
theorem b7 : Ban 12 4 v10 := checkedSmall
theorem b8 : Ban 12 4 v11 := checkedSmall
theorem b9 : Ban 12 4 v12 := checkedSmall
theorem b10 : Ban 12 4 v13 := checkedSmall
theorem b11 : Ban 12 4 v14 := checkedSmall
theorem b12 : Ban 12 4 v15 := checkedSmall
theorem b13 : Ban 12 4 v16 := checkedSmall
theorem b14 : Ban 12 4 v17 := checkedSmall
theorem b15 : Ban 12 4 v18 := checkedSmall
theorem b16 : Ban 12 4 v19 := checkedSmall
theorem b17 : Ban 12 4 v20 := checkedSmall
theorem b18 : Ban 12 4 v21 := checkedSmall
theorem b19 : Ban 12 4 v22 := checkedSmall
theorem b20 : Ban 12 4 v23 := checkedSmall
theorem b21 : Ban 12 4 v24 := checkedSmall
theorem b22 : Ban 12 4 v25 := checkedSmall
theorem b23 : Ban 12 4 v26 := checkedSmall
theorem b24 : Ban 12 4 v27 := checkedSmall
theorem b25 : Ban 12 4 v28 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b26 : Ban 12 5 v4 := viaBranch (ws := [v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28]) (consBan b2 (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b10 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (consBan b19 (consBan b20 (consBan b21 (consBan b22 (consBan b23 (consBan b24 (consBan b25 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b27 : Ban 12 4 v29 := checkedSmall
theorem b28 : Ban 12 4 v30 := checkedSmall
theorem b29 : Ban 12 4 v31 := checkedSmall
theorem b30 : Ban 12 4 v32 := checkedSmall
theorem b31 : Ban 12 4 v33 := checkedSmall
theorem b32 : Ban 12 4 v34 := checkedSmall
theorem b33 : Ban 12 4 v35 := checkedSmall
theorem b34 : Ban 12 4 v36 := checkedSmall
theorem b35 : Ban 12 4 v37 := checkedSmall
theorem b36 : Ban 12 4 v38 := checkedSmall
theorem b37 : Ban 12 4 v39 := checkedSmall
theorem b38 : Ban 12 4 v40 := checkedSmall
theorem b39 : Ban 12 4 v41 := checkedSmall
theorem b40 : Ban 12 4 v42 := checkedSmall
theorem b41 : Ban 12 4 v43 := checkedSmall
theorem b42 : Ban 12 4 v44 := checkedSmall
theorem b43 : Ban 12 4 v45 := checkedSmall
theorem b44 : Ban 12 4 v46 := checkedSmall
theorem b45 : Ban 12 4 v47 := checkedSmall
theorem b46 : Ban 12 4 v48 := checkedSmall
theorem b47 : Ban 12 4 v49 := checkedSmall
theorem b48 : Ban 12 4 v50 := checkedSmall
theorem b49 : Ban 12 4 v51 := checkedSmall
theorem b50 : Ban 12 4 v52 := checkedSmall
theorem b51 : Ban 12 4 v53 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b52 : Ban 12 5 v6 := viaBranch (ws := [v29,v30,v31,v32,v33,v8,v7,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53]) (consBan b27 (consBan b28 (consBan b29 (consBan b30 (consBan b31 (consBan b5 (consBan b4 (consBan b32 (consBan b33 (consBan b34 (consBan b35 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (consBan b40 (consBan b41 (consBan b42 (consBan b43 (consBan b44 (consBan b45 (consBan b46 (consBan b47 (consBan b48 (consBan b49 (consBan b50 (consBan b51 (nilBan 12 4)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w1 : Wide 12 5 v6 := viaSub (ws := [v4,v6]) (consBan b26 (consBan b52 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b53 : Ban 26 6 v3 := smallByCut p47_43 w1
theorem b0 : Ban 12 4 v2 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w0 : Wide 12 4 v2 := viaSub (ws := [v2]) (consBan b0 (nilBan 12 4)) (by decide) (by decide +kernel)
theorem b54 : Ban 26 6 v54 := smallByCut p47_46 w0
theorem b56 : Ban 26 6 v55 := smallByCut p47_45 w2
theorem b172 : Ban 12 4 v166 := checkedSmall
theorem b173 : Ban 12 4 v167 := checkedSmall
theorem b174 : Ban 12 4 v168 := checkedSmall
theorem b175 : Ban 12 4 v169 := checkedSmall
theorem b176 : Ban 12 4 v170 := checkedSmall
theorem b177 : Ban 12 4 v171 := checkedSmall
theorem b178 : Ban 12 4 v172 := checkedSmall
theorem b179 : Ban 12 4 v173 := checkedSmall
theorem b180 : Ban 12 4 v174 := checkedSmall
theorem b181 : Ban 12 4 v175 := checkedSmall
theorem b182 : Ban 12 4 v176 := checkedSmall
theorem b183 : Ban 12 4 v177 := checkedSmall
theorem b184 : Ban 12 4 v178 := checkedSmall
theorem b185 : Ban 12 4 v179 := checkedSmall
theorem b186 : Ban 12 4 v180 := checkedSmall
theorem b187 : Ban 12 4 v181 := checkedSmall
theorem b188 : Ban 12 4 v182 := checkedSmall
theorem b189 : Ban 12 4 v183 := checkedSmall
theorem b190 : Ban 12 4 v184 := checkedSmall
theorem b191 : Ban 12 4 v185 := checkedSmall
theorem b192 : Ban 12 4 v186 := checkedSmall
theorem b193 : Ban 12 4 v187 := checkedSmall
theorem b194 : Ban 12 4 v188 := checkedSmall
theorem b195 : Ban 12 4 v189 := checkedSmall
theorem b196 : Ban 12 4 v190 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b197 : Ban 12 5 v27 := viaBranch (ws := [v166,v167,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v25,v183,v26,v184,v185,v186,v187,v188,v189,v190]) (consBan b172 (consBan b173 (consBan b174 (consBan b175 (consBan b176 (consBan b177 (consBan b178 (consBan b179 (consBan b180 (consBan b181 (consBan b182 (consBan b183 (consBan b184 (consBan b185 (consBan b186 (consBan b187 (consBan b188 (consBan b22 (consBan b189 (consBan b23 (consBan b190 (consBan b191 (consBan b192 (consBan b193 (consBan b194 (consBan b195 (consBan b196 (nilBan 12 4)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w8 : Wide 12 5 v27 := viaSub (ws := [v4,v27]) (consBan b26 (consBan b197 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b57 : Ban 26 6 v57 := smallByCut p47_43 w8
theorem b58 : Ban 26 5 v59 := smallByCut p47_46 w0
theorem b59 : Ban 26 5 v60 := smallByCut p47_43 w1
theorem b60 : Ban 26 5 v61 := smallByCut p47_43 w1
theorem b61 : Ban 26 5 v62 := smallByCut p47_46 w0
theorem b62 : Ban 26 5 v63 := smallByCut p47_46 w0
theorem b63 : Ban 26 5 v64 := smallByCut p47_46 w0
theorem b64 : Ban 26 5 v65 := smallByCut p47_43 w8
theorem b65 : Ban 26 5 v66 := smallByCut p47_43 w8
theorem b66 : Ban 26 5 v67 := smallByCut p47_43 w8
theorem b67 : Ban 26 5 v68 := smallByCut p47_46 w0
theorem b106 : Ban 12 5 v10 := viaPerm map43_2 map43_2 b52 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w5 : Wide 12 5 v10 := viaSub (ws := [v4,v10]) (consBan b26 (consBan b106 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b68 : Ban 26 5 v69 := smallByCut p47_43 w5
theorem b69 : Ban 26 5 v70 := smallByCut p47_46 w0
theorem b110 : Ban 12 4 v108 := checkedSmall
theorem b111 : Ban 12 4 v109 := checkedSmall
theorem b112 : Ban 12 4 v110 := checkedSmall
theorem b113 : Ban 12 4 v111 := checkedSmall
theorem b114 : Ban 12 4 v112 := checkedSmall
theorem b115 : Ban 12 4 v113 := checkedSmall
theorem b116 : Ban 12 4 v114 := checkedSmall
theorem b117 : Ban 12 4 v115 := checkedSmall
theorem b118 : Ban 12 4 v116 := checkedSmall
theorem b119 : Ban 12 4 v117 := checkedSmall
theorem b120 : Ban 12 4 v118 := checkedSmall
theorem b121 : Ban 12 4 v119 := checkedSmall
theorem b122 : Ban 12 4 v120 := checkedSmall
theorem b123 : Ban 12 4 v121 := checkedSmall
theorem b124 : Ban 12 4 v122 := checkedSmall
theorem b125 : Ban 12 4 v123 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b126 : Ban 12 5 v8 := viaBranch (ws := [v6,v33,v108,v109,v110,v111,v5,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123]) (consBan b3 (consBan b31 (consBan b110 (consBan b111 (consBan b112 (consBan b113 (consBan b2 (consBan b114 (consBan b115 (consBan b116 (consBan b117 (consBan b118 (consBan b119 (consBan b120 (consBan b121 (consBan b122 (consBan b123 (consBan b124 (consBan b125 (nilBan 12 4)))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b127 : Ban 12 5 v12 := viaPerm map43_2 map43_2 b126 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w6 : Wide 12 5 v12 := viaSub (ws := [v4,v12]) (consBan b26 (consBan b127 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b70 : Ban 26 5 v71 := smallByCut p47_43 w6
theorem b71 : Ban 26 5 v72 := smallByCut p47_46 w0
theorem b72 : Ban 26 5 v73 := smallByCut p47_46 w0
theorem b73 : Ban 26 5 v74 := smallByCut p47_46 w0
theorem b74 : Ban 26 5 v75 := smallByCut p47_46 w0
theorem b75 : Ban 26 5 v76 := checkedSmall
theorem b76 : Ban 26 5 v77 := smallByCut p47_43 w1
theorem b77 : Ban 26 5 v78 := checkedSmall
theorem b78 : Ban 26 5 v79 := checkedSmall
theorem b79 : Ban 26 5 v80 := checkedSmall
theorem b80 : Ban 26 5 v81 := checkedSmall
theorem b81 : Ban 26 5 v82 := checkedSmall
theorem b198 : Ban 12 5 v20 := viaPerm map43_5 map43_5 b197 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w7 : Wide 12 5 v20 := viaSub (ws := [v4,v20]) (consBan b26 (consBan b198 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b82 : Ban 26 5 v83 := smallByCut p47_43 w7
theorem b83 : Ban 26 5 v84 := checkedSmall
theorem b84 : Ban 26 5 v85 := checkedSmall
theorem b85 : Ban 26 5 v86 := checkedSmall
theorem b86 : Ban 26 5 v87 := checkedSmall
theorem b87 : Ban 26 5 v88 := checkedSmall
theorem b88 : Ban 26 5 v89 := smallByCut p47_43 w5
theorem b89 : Ban 26 5 v90 := checkedSmall
theorem b90 : Ban 26 5 v91 := smallByCut p47_43 w6
theorem b91 : Ban 26 5 v92 := checkedSmall
theorem b92 : Ban 26 5 v93 := checkedSmall
theorem b93 : Ban 26 5 v94 := checkedSmall
theorem b94 : Ban 26 5 v95 := checkedSmall
theorem b95 : Ban 26 5 v96 := checkedSmall
theorem b96 : Ban 26 5 v97 := checkedSmall
theorem b97 : Ban 26 5 v98 := smallByCut p47_43 w8
theorem b98 : Ban 26 5 v99 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b99 : Ban 26 6 v58 := viaBranch (ws := [v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99]) (consBan b58 (consBan b59 (consBan b60 (consBan b61 (consBan b62 (consBan b63 (consBan b64 (consBan b65 (consBan b66 (consBan b67 (consBan b68 (consBan b69 (consBan b70 (consBan b71 (consBan b72 (consBan b73 (consBan b74 (consBan b75 (consBan b76 (consBan b77 (consBan b78 (consBan b79 (consBan b80 (consBan b81 (consBan b82 (consBan b83 (consBan b84 (consBan b85 (consBan b86 (consBan b87 (consBan b88 (consBan b89 (consBan b90 (consBan b91 (consBan b92 (consBan b93 (consBan b94 (consBan b95 (consBan b96 (consBan b97 (consBan b98 (nilBan 26 5)))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b100 : Ban 26 6 v100 := smallByCut p47_43 w8
theorem b101 : Ban 26 6 v101 := smallByCut p47_43 w8
theorem b102 : Ban 26 6 v65 := smallByCut p47_43 w8
theorem b104 : Ban 26 6 v102 := smallByCut p47_43 w8
theorem b105 : Ban 26 6 v103 := smallByCut p47_46 w0
theorem b107 : Ban 26 6 v104 := smallByCut p47_43 w5
theorem b109 : Ban 26 6 v105 := smallByCut p47_46 w0
theorem b128 : Ban 26 6 v107 := smallByCut p47_43 w6
theorem b129 : Ban 26 6 v124 := smallByCut p47_46 w0
theorem b130 : Ban 26 6 v125 := viaPerm map47_1 map47_1 b107 (by decide +kernel) (by decide +kernel)
theorem b108 : Ban 26 6 v106 := smallByCut p47_46 w0
theorem b131 : Ban 26 6 v126 := viaPerm map47_1 map47_1 b128 (by decide +kernel) (by decide +kernel)
theorem b132 : Ban 26 6 v127 := smallByCut p47_43 w8
theorem b133 : Ban 26 6 v128 := smallByCut p47_43 w8
theorem b134 : Ban 26 6 v129 := smallByCut p47_43 w8
theorem b135 : Ban 26 6 v130 := smallByCut p47_43 w8
theorem b137 : Ban 26 6 v131 := smallByCut p47_45 w2
theorem solidb32 : Wide 12 4 v34 := solid b32
theorem b138 : Ban 26 5 v134 := smallByCut p47_43 solidb32
theorem b139 : Ban 26 5 v135 := smallByCut p47_45 w2
theorem b140 : Ban 26 5 v136 := checkedSmall
theorem b141 : Ban 26 5 v137 := checkedSmall
theorem b142 : Ban 26 5 v138 := checkedSmall
theorem b143 : Ban 26 5 v139 := smallByCut p47_46 w0
theorem b144 : Ban 26 5 v140 := checkedSmall
theorem b145 : Ban 26 5 v141 := smallByCut p47_46 w0
theorem b146 : Ban 26 5 v142 := checkedSmall
theorem b147 : Ban 26 5 v143 := smallByCut p47_45 w2
theorem b148 : Ban 26 5 v144 := smallByCut p47_45 w2
theorem b149 : Ban 26 5 v145 := smallByCut p47_45 w2
theorem b150 : Ban 26 5 v146 := smallByCut p47_45 w2
theorem b151 : Ban 26 5 v147 := checkedSmall
theorem b152 : Ban 26 5 v148 := smallByCut p47_43 w7
theorem b153 : Ban 26 5 v149 := checkedSmall
theorem b154 : Ban 26 5 v150 := checkedSmall
theorem b155 : Ban 26 5 v151 := smallByCut p47_43 w8
theorem b156 : Ban 26 5 v152 := smallByCut p47_43 w8
theorem b157 : Ban 26 5 v153 := checkedSmall
theorem b158 : Ban 26 5 v154 := checkedSmall
theorem b159 : Ban 26 5 v155 := smallByCut p47_43 w8
theorem b160 : Ban 26 5 v156 := checkedSmall
theorem b161 : Ban 26 5 v157 := checkedSmall
theorem b162 : Ban 26 5 v158 := checkedSmall
theorem b163 : Ban 26 5 v159 := smallByCut p47_45 w2
theorem b164 : Ban 26 5 v160 := checkedSmall
theorem b165 : Ban 26 5 v161 := checkedSmall
theorem b166 : Ban 26 5 v162 := checkedSmall
theorem b167 : Ban 26 5 v163 := checkedSmall
theorem b168 : Ban 26 5 v164 := checkedSmall
theorem b169 : Ban 26 5 v165 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b170 : Ban 26 6 v133 := viaBranch (ws := [v134,v135,v81,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v163,v164,v165]) (consBan b138 (consBan b139 (consBan b80 (consBan b140 (consBan b141 (consBan b142 (consBan b143 (consBan b144 (consBan b145 (consBan b146 (consBan b147 (consBan b148 (consBan b149 (consBan b150 (consBan b151 (consBan b152 (consBan b153 (consBan b154 (consBan b155 (consBan b156 (consBan b157 (consBan b158 (consBan b159 (consBan b160 (consBan b161 (consBan b162 (consBan b163 (consBan b164 (consBan b165 (consBan b166 (consBan b167 (consBan b168 (consBan b169 (nilBan 26 5)))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b171 : Ban 26 6 v159 := smallByCut p47_45 w2
theorem b199 : Ban 26 6 v148 := smallByCut p47_43 w7
theorem b136 : Ban 26 6 v132 := smallByCut p47_45 w2
theorem b200 : Ban 26 6 v191 := viaPerm map47_1 map47_1 b170 (by decide +kernel) (by decide +kernel)
theorem b201 : Ban 26 6 v192 := smallByCut p47_45 w2
theorem b202 : Ban 26 6 v193 := viaPerm map47_1 map47_1 b199 (by decide +kernel) (by decide +kernel)
theorem b203 : Ban 26 6 v194 := smallByCut p47_43 w8
theorem b204 : Ban 26 6 v195 := smallByCut p47_43 w8
theorem b205 : Ban 26 6 v196 := smallByCut p47_43 w8
theorem b206 : Ban 26 6 v197 := smallByCut p47_43 w8
theorem b207 : Ban 26 6 v198 := smallByCut p47_43 w8
theorem b208 : Ban 26 6 v199 := smallByCut p47_43 w8
theorem b209 : Ban 26 6 v200 := smallByCut p47_43 w8
theorem b210 : Ban 26 6 v201 := smallByCut p47_43 w8
theorem b211 : Ban 26 5 v203 := checkedSmall
theorem b212 : Ban 26 5 v204 := smallByCut p47_46 w0
theorem b213 : Ban 26 5 v205 := checkedSmall
theorem b214 : Ban 26 5 v206 := smallByCut p47_46 w0
theorem b215 : Ban 26 5 v207 := checkedSmall
theorem b216 : Ban 26 5 v208 := checkedSmall
theorem b217 : Ban 26 5 v209 := checkedSmall
theorem b218 : Ban 26 5 v210 := checkedSmall
theorem b219 : Ban 26 5 v211 := checkedSmall
theorem b220 : Ban 26 5 v212 := smallByCut p47_45 w2
theorem b221 : Ban 26 5 v213 := checkedSmall
theorem b222 : Ban 26 5 v214 := smallByCut p47_45 w2
theorem b223 : Ban 26 5 v215 := checkedSmall
theorem b224 : Ban 26 5 v216 := checkedSmall
theorem b225 : Ban 26 5 v217 := checkedSmall
theorem b226 : Ban 26 5 v218 := checkedSmall
theorem b227 : Ban 26 5 v219 := smallByCut p47_43 w8
theorem b228 : Ban 26 5 v220 := checkedSmall
theorem b229 : Ban 26 5 v221 := smallByCut p47_43 w8
theorem b230 : Ban 26 5 v222 := checkedSmall
theorem solidb188 : Wide 12 4 v182 := solid b188
theorem b231 : Ban 26 5 v223 := smallByCut p47_43 solidb188
theorem b232 : Ban 26 5 v224 := smallByCut p47_43 w8
theorem b233 : Ban 26 5 v225 := checkedSmall
theorem b234 : Ban 26 5 v226 := checkedSmall
theorem b235 : Ban 26 5 v227 := checkedSmall
theorem b236 : Ban 26 5 v228 := checkedSmall
theorem b237 : Ban 26 5 v229 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b238 : Ban 26 6 v202 := viaBranch (ws := [v96,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v160,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229]) (consBan b95 (consBan b211 (consBan b212 (consBan b213 (consBan b214 (consBan b215 (consBan b216 (consBan b217 (consBan b218 (consBan b219 (consBan b220 (consBan b221 (consBan b222 (consBan b223 (consBan b164 (consBan b224 (consBan b225 (consBan b226 (consBan b227 (consBan b228 (consBan b229 (consBan b230 (consBan b231 (consBan b232 (consBan b233 (consBan b234 (consBan b235 (consBan b236 (consBan b237 (nilBan 26 5)))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b239 : Ban 26 5 v231 := checkedSmall
theorem b240 : Ban 26 5 v232 := checkedSmall
theorem b241 : Ban 26 5 v233 := checkedSmall
theorem b242 : Ban 26 5 v234 := checkedSmall
theorem b243 : Ban 26 5 v235 := checkedSmall
theorem b244 : Ban 26 5 v236 := smallByCut p47_46 w0
theorem b245 : Ban 26 5 v237 := checkedSmall
theorem b246 : Ban 26 5 v238 := smallByCut p47_46 w0
theorem b247 : Ban 26 5 v239 := checkedSmall
theorem b248 : Ban 26 5 v240 := smallByCut p47_45 w2
theorem b249 : Ban 26 5 v241 := smallByCut p47_45 w2
theorem b250 : Ban 26 5 v242 := checkedSmall
theorem b251 : Ban 26 5 v243 := smallByCut p47_43 w8
theorem b252 : Ban 26 5 v244 := checkedSmall
theorem b253 : Ban 26 5 v245 := smallByCut p47_43 w8
theorem b254 : Ban 26 5 v246 := checkedSmall
theorem solidb189 : Wide 12 4 v183 := solid b189
theorem b255 : Ban 26 5 v247 := smallByCut p47_43 solidb189
theorem b256 : Ban 26 5 v248 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b257 : Ban 26 6 v230 := viaBranch (ws := [v97,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v163,v241,v242,v243,v244,v245,v246,v227,v228,v229,v247,v248,v226,v224]) (consBan b96 (consBan b239 (consBan b240 (consBan b241 (consBan b242 (consBan b243 (consBan b244 (consBan b245 (consBan b246 (consBan b247 (consBan b248 (consBan b167 (consBan b249 (consBan b250 (consBan b251 (consBan b252 (consBan b253 (consBan b254 (consBan b235 (consBan b236 (consBan b237 (consBan b255 (consBan b256 (consBan b234 (consBan b232 (nilBan 26 5)))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b258 : Ban 26 6 v224 := smallByCut p47_43 w8
theorem b259 : Ban 26 6 v226 := viaPerm map47_1 map47_1 b258 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b260 : Ban 26 7 v0 := viaBranch (ws := [v1,v3,v54,v55,v57,v58,v100,v101,v65,v102,v103,v104,v105,v107,v124,v125,v106,v126,v127,v128,v129,v130,v131,v133,v159,v148,v132,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v230,v224,v226]) (consBan b1 (consBan b53 (consBan b54 (consBan b56 (consBan b57 (consBan b99 (consBan b100 (consBan b101 (consBan b102 (consBan b104 (consBan b105 (consBan b107 (consBan b109 (consBan b128 (consBan b129 (consBan b130 (consBan b108 (consBan b131 (consBan b132 (consBan b133 (consBan b134 (consBan b135 (consBan b137 (consBan b170 (consBan b171 (consBan b199 (consBan b136 (consBan b200 (consBan b201 (consBan b202 (consBan b203 (consBan b204 (consBan b205 (consBan b206 (consBan b207 (consBan b208 (consBan b209 (consBan b210 (consBan b238 (consBan b257 (consBan b258 (consBan b259 (nilBan 26 6))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem verifiedPin : Wide 26 7 v0 := widen (by decide +kernel) b260
end PEqualNP.Outside.L_meta_12889.Support

namespace PEqualNP.Outside.L_meta_12889.Data
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12889.Support
def target (x : Fin 6 → Bool) := Nat.testBit (4276808392 * 2 ^ 32 + 3939035848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def posBits : ℕ := 0x31f3cf3aebae76db5d73c7179e75d6d96575964d3
def negBits : ℕ := 0x21e34738c9ae34cb4572c1171a715698455512491
def sample (bank : ℕ) (i : Fin 27) (j : Fin 6) := bank.testBit (6*i.val+j.val)
def inputs : List ℕ := [0x2004898c09f3f3,0x1922430764c9f,0xc2c58c3878f1c,0x16c07603f80fe0,0x20000000000000,0x3b7b0007fff000]
def seeds : List Wire := [(false,0x2004898c09f3f3),(false,0x1922430764c9f),(false,0xc2c58c3878f1c),(false,0x16c07603f80fe0),(true,0x20000000000000),(false,0x3b7b0007fff000)]
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
theorem core_floor : Wide 26 7 restricted := verifiedPin
theorem six_floor : Ban 27 8 inputs := viaCut restrictRows core_floor (by decide) (by decide +kernel) (by decide +kernel)
def witness : Circuit := ⟨[⟨.and,[4,5]⟩, ⟨.and,[3,6]⟩, ⟨.and,[2,7]⟩, ⟨.or,[2,7]⟩, ⟨.and,[1,9]⟩, ⟨.or,[8,10]⟩, ⟨.or,[3,6]⟩, ⟨.or,[1,12]⟩, ⟨.and,[0,13]⟩, ⟨.or,[11,14]⟩],15⟩
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
end PEqualNP.Outside.L_meta_12889.Data

theorem PEqualNP.Outside.L_meta_12889 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 3939035848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 3939035848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_12889.Data.mono_enough
