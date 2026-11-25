import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16907.Support

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

def t0 := 0x102503f0ff
def t1 := 0x560ac0fe0fe0
def t2 := 0x8d4c929d4c93
def t3 := 0xa18518e18f1c
def t4 := 0xfbe000fff000
def v0 := [t0,t1,t2,t3,t4]
def t5 := 0x14093
def v1 := [t5,t0,t1,t2,t3,t4]
def t6 := 0x14f
def t7 := 0x4b3
def t8 := 0xa3c
def v2 := [t6,t7,t8]
def p31_13 : Projection 24 6 := pick [2,3,5,6,8,9] rfl (by decide +kernel) (by decide)
def t9 := 0x8d5cb79ffcff
def v3 := [t0,t1,t2,t9,t3,t4]
def t10 := 0x251ff
def t11 := 0x692e93
def t12 := 0xb18f1c
def t13 := 0xdc0fe0
def v4 := [t10,t11,t12,t13]
def t14 := 0x93
def v5 := [t14,t10,t11,t12,t13]
def t15 := 0x6b7fff
def v6 := [t10,t11,t15,t12,t13]
def t16 := 0x2516c
def v7 := [t16,t10,t11,t12,t13]
def t17 := 0x692e00
def v8 := [t10,t17,t11,t12,t13]
def t18 := 0x11c
def v9 := [t18,t10,t11,t12,t13]
def t19 := 0xb3dfff
def v10 := [t10,t11,t12,t19,t13]
def t20 := 0x250e3
def v11 := [t20,t10,t11,t12,t13]
def t21 := 0xb18e00
def v12 := [t10,t11,t21,t12,t13]
def t22 := 0x1e0
def v13 := [t22,t10,t11,t12,t13]
def t23 := 0xde5fff
def v14 := [t10,t11,t12,t13,t23]
def t24 := 0x2501f
def v15 := [t24,t10,t11,t12,t13]
def t25 := 0xdc0e00
def v16 := [t10,t11,t12,t25,t13]
def t26 := 0x210e10
def v17 := [t10,t26,t11,t12,t13]
def t27 := 0xf9af9f
def v18 := [t10,t11,t12,t13,t27]
def t28 := 0x482083
def v19 := [t10,t28,t11,t12,t13]
def t29 := 0x90810c
def v20 := [t10,t11,t29,t12,t13]
def t30 := 0x480e80
def v21 := [t10,t30,t11,t12,t13]
def t31 := 0xfd2ff3
def v22 := [t10,t11,t12,t13,t31]
def t32 := 0x212013
def v23 := [t10,t32,t11,t12,t13]
def t33 := 0x940160
def v24 := [t10,t11,t33,t12,t13]
def t34 := 0x900f00
def v25 := [t10,t11,t34,t12,t13]
def t35 := 0xfd8ffc
def v26 := [t10,t11,t12,t13,t35]
def t36 := 0x21801c
def v27 := [t10,t36,t11,t12,t13]
def t37 := 0x4c00e0
def v28 := [t10,t37,t11,t12,t13]
def v29 := [t14,t15,t12,t13]
def v30 := [t14,t10,t15,t12,t13]
def v31 := [t14,t11,t15,t12,t13]
def v32 := [t16,t10,t15,t12,t13]
def v33 := [t17,t11,t15,t12,t13]
def v34 := [t10,t15,t12,t13,t27]
def v35 := [t10,t28,t15,t12,t13]
def v36 := [t10,t15,t12,t13,t31]
def v37 := [t10,t32,t15,t12,t13]
def t38 := 0x210f1c
def v38 := [t10,t38,t11,t13]
def v39 := [t10,t38,t11,t15,t13]
def v40 := [t10,t38,t11,t12,t13]
def t39 := 0xfbffff
def v41 := [t10,t11,t12,t13,t39]
def t40 := 0x4a70e3
def v42 := [t10,t40,t11,t13]
def v43 := [t10,t40,t11,t15,t13]
def v44 := [t10,t40,t11,t12,t13]
def t41 := 0x908000
def v45 := [t10,t11,t41,t12,t13]
def t42 := 0x480fe0
def v46 := [t10,t42,t11,t12]
def v47 := [t10,t42,t11,t15,t12]
def v48 := [t10,t42,t11,t12,t13]
def t43 := 0xff7fff
def v49 := [t10,t11,t12,t13,t43]
def t44 := 0x23701f
def v50 := [t10,t44,t11,t12]
def v51 := [t10,t44,t11,t15,t12]
def v52 := [t10,t44,t11,t12,t13]
def t45 := 0x940000
def v53 := [t10,t11,t45,t12,t13]
def p31_27 : Projection 24 12 := pick [0,1,5,6,7,12,13,14,17,18,19,20] rfl (by decide +kernel) (by decide)
def t46 := 0x102502b06c
def v54 := [t46,t0,t1,t2,t3,t4]
def t47 := 0x10250000ff
def v55 := [t47,t0,t1,t2,t3,t4]
def v56 := [t22,t24,t11,t12,t13]
def t48 := 0x13
def v57 := [t48,t10,t11,t12,t13]
def t49 := 0x6b7e9f
def v58 := [t10,t11,t49,t12,t13]
def t50 := 0x2500c
def v59 := [t50,t10,t11,t12,t13]
def t51 := 0x692e80
def v60 := [t10,t51,t11,t12,t13]
def t52 := 0x1c
def v61 := [t52,t10,t11,t12,t13]
def t53 := 0xb3df1f
def v62 := [t10,t11,t12,t53,t13]
def t54 := 0x25003
def v63 := [t54,t10,t11,t12,t13]
def t55 := 0xb18f00
def v64 := [t10,t11,t55,t12,t13]
def v65 := [t24,t10,t11,t12,t23]
def v66 := [t24,t11,t12,t25]
def v67 := [t24,t10,t11,t12,t25]
def v68 := [t24,t11,t12,t25,t13]
def v69 := [t24,t10,t30,t11,t12]
def v70 := [t24,t10,t32,t11,t12]
def v71 := [t24,t10,t11,t34,t12]
def v72 := [t24,t10,t36,t11,t12]
def map31_1 : Projection 24 24 := pick [12,13,2,3,15,5,6,17,8,9,21,22,0,1,14,4,16,7,20,19,18,10,11,23] rfl (by decide +kernel) (by decide)
def t56 := 0x8d4c929c0c00
def v73 := [t0,t1,t56,t2,t3,t4]
def t57 := 0x1801c
def v74 := [t57,t0,t1,t2,t3,t4]
def t58 := 0xa1953de3ffff
def v75 := [t0,t1,t2,t3,t58,t4]
def t59 := 0x10250270e3
def v76 := [t59,t0,t1,t2,t3,t4]
def t60 := 0xa18518e00f00
def v77 := [t0,t1,t2,t60,t3,t4]
def t61 := 0x200e0
def v78 := [t61,t0,t1,t2,t3,t4]
def v79 := [t18,t20,t11,t12,t13]
def t62 := 0x10
def v80 := [t62,t10,t11,t12,t13]
def t63 := 0x692f9f
def v81 := [t10,t63,t12,t13]
def v82 := [t18,t10,t63,t12,t13]
def v83 := [t10,t11,t63,t12,t13]
def t64 := 0x10c
def v84 := [t64,t10,t11,t12,t13]
def t65 := 0x692e83
def v85 := [t10,t65,t12,t13]
def v86 := [t18,t10,t65,t12,t13]
def v87 := [t10,t65,t11,t12,t13]
def v88 := [t18,t10,t11,t21,t13]
def t66 := 0x100
def v89 := [t66,t10,t11,t12,t13]
def t67 := 0xdc0ffc
def v90 := [t10,t11,t12,t67]
def v91 := [t18,t10,t11,t12,t67]
def v92 := [t10,t11,t12,t13,t67]
def t68 := 0xdc0ee0
def v93 := [t10,t11,t12,t68]
def v94 := [t18,t10,t11,t12,t68]
def v95 := [t10,t11,t12,t68,t13]
def v96 := [t18,t11,t19,t13]
def v97 := [t18,t10,t11,t19,t13]
def v98 := [t18,t11,t12,t19,t13]
def v99 := [t18,t10,t26,t11,t13]
def v100 := [t18,t10,t28,t11,t13]
def v101 := [t18,t10,t11,t34,t13]
def v102 := [t18,t10,t37,t11,t13]
def t69 := 0x561ae5ffffff
def v103 := [t0,t1,t69,t2,t3,t4]
def map27_2 : Projection 12 12 := pick [2,3,0,1,4,5,6,8,7,9,11,10] rfl (by decide +kernel) (by decide)
def t70 := 0x102501f01f
def v104 := [t70,t0,t1,t2,t3,t4]
def map27_1 : Projection 12 12 := pick [0,1,5,6,7,2,3,4,8,10,9,11] rfl (by decide +kernel) (by decide)
def t71 := 0x560ac0fc0f00
def v105 := [t0,t71,t1,t2,t3,t4]
def v106 := [t14,t10,t17,t12,t13]
def v107 := [t16,t17,t12,t13]
def v108 := [t16,t10,t17,t12,t13]
def v109 := [t16,t17,t11,t12,t13]
def t72 := 0x210e00
def v110 := [t10,t72,t11,t12,t13]
def t73 := 0xf9af1c
def v111 := [t10,t11,t12,t13,t73]
def t74 := 0x482000
def v112 := [t10,t74,t11,t12,t13]
def t75 := 0x90811c
def v113 := [t10,t11,t75,t12,t13]
def t76 := 0x480e00
def v114 := [t10,t76,t11,t12,t13]
def t77 := 0xfd2fe0
def v115 := [t10,t11,t12,t13,t77]
def t78 := 0x212000
def v116 := [t10,t78,t11,t12,t13]
def t79 := 0x9401e0
def v117 := [t10,t11,t79,t12,t13]
def v118 := [t10,t17,t12,t13,t27]
def v119 := [t10,t28,t17,t12,t13]
def v120 := [t10,t17,t12,t13,t31]
def v121 := [t10,t32,t17,t12,t13]
def t80 := 0x3f000
def v122 := [t80,t0,t1,t2,t3,t4]
def t81 := 0xfbf025fff0ff
def v123 := [t0,t1,t2,t3,t4,t81]
def t82 := 0xfbe000fc0000
def v124 := [t0,t1,t2,t3,t82,t4]
def t83 := 0x810410810c10
def v125 := [t0,t1,t83,t2,t3,t4]
def t84 := 0xadcd9afdcf9f
def v126 := [t0,t1,t3,t84,t4]
def t85 := 0xfbe518ffff1c
def v127 := [t0,t1,t2,t3,t85]
def v128 := [t0,t1,t2,t3,t84,t4]
def t86 := 0xc48821c4083
def v129 := [t0,t86,t1,t3,t4]
def v130 := [t0,t86,t1,t2,t3,t4]
def t87 := 0x20810860830c
def v131 := [t0,t87,t1,t2,t3,t4]
def t88 := 0x408809c0c80
def v132 := [t0,t88,t1,t2,t3,t4]
def t89 := 0x520000fe0000
def v133 := [t0,t89,t1,t2,t3,t4]
def t90 := 0xdf4ed2ff4ff3
def v134 := [t0,t1,t2,t3,t90,t4]
def t91 := 0xffeac0ffffe0
def v135 := [t0,t1,t2,t3,t4,t91]
def v136 := [t0,t69,t2,t3,t4,t91]
def v137 := [t0,t71,t2,t3,t4,t91]
def v138 := [t0,t1,t2,t3,t81,t91]
def v139 := [t0,t1,t2,t3,t82,t91]
def t92 := 0x3f0e0
def v140 := [t92,t0,t1,t2,t3,t4]
def t93 := 0xfffae5ffffff
def v141 := [t0,t1,t2,t3,t4,t93]
def t94 := 0x102500001f
def v142 := [t94,t0,t1,t2,t3,t4]
def t95 := 0xffeac0fc0f00
def v143 := [t0,t1,t2,t3,t4,t95]
def v144 := [t0,t1,t3,t84,t4,t91]
def v145 := [t0,t86,t1,t3,t4,t91]
def t96 := 0x8940009d4000
def v146 := [t0,t1,t96,t2,t3,t91]
def t97 := 0x40c92000c93
def v147 := [t0,t97,t1,t2,t3,t91]
def t98 := 0x8d48809d4c80
def v148 := [t0,t1,t98,t2,t3,t4]
def t99 := 0xffeed2fffff3
def v149 := [t0,t1,t2,t3,t4,t99]
def t100 := 0x412000013
def v150 := [t100,t0,t1,t2,t3,t4]
def t101 := 0x72a24062b360
def v151 := [t0,t1,t101,t2,t3,t4]
def v152 := [t0,t1,t2,t3,t85,t91]
def t102 := 0x5a60001e7000
def v153 := [t0,t1,t102,t2,t3,t91]
def t103 := 0xa18000e18f00
def v154 := [t0,t1,t2,t103,t3,t4]
def t104 := 0xffefd8fffffc
def v155 := [t0,t1,t2,t3,t4,t104]
def t105 := 0x51800001c
def v156 := [t105,t0,t1,t2,t3,t4]
def t106 := 0x5e6ac01e70e0
def v157 := [t0,t1,t106,t2,t3,t4]
def v158 := [t0,t89,t2,t3,t91]
def v159 := [t0,t89,t1,t2,t3,t91]
def v160 := [t0,t89,t2,t3,t4,t91]
def t107 := 0x40ac0000fe0
def v161 := [t0,t107,t1,t2,t3,t91]
def t108 := 0xa9e00001f000
def v162 := [t0,t2,t3,t108,t4,t91]
def v163 := [t0,t1,t2,t3,t108,t4]
def v164 := [t0,t107,t1,t2,t3,t4]
def t109 := 0x894412014013
def v165 := [t0,t1,t109,t2,t3,t4]
def t110 := 0x520240620360
def v166 := [t0,t110,t1,t2,t3,t4]
def t111 := 0x23d1ff
def v167 := [t10,t111,t11,t12,t13]
def t112 := 0x251e3
def v168 := [t112,t10,t11,t12,t13]
def t113 := 0x218000
def v169 := [t10,t113,t11,t12,t13]
def v170 := [t10,t36,t11,t19,t13]
def v171 := [t10,t36,t11,t21,t13]
def v172 := [t22,t10,t36,t11,t12]
def t114 := 0x210010
def v173 := [t10,t114,t11,t12,t13]
def t115 := 0x69ae9f
def v174 := [t10,t115,t12,t13]
def v175 := [t10,t36,t115,t12,t13]
def v176 := [t10,t11,t115,t12,t13]
def t116 := 0x800c
def v177 := [t116,t10,t11,t12,t13]
def t117 := 0x482e83
def v178 := [t10,t117,t12,t13]
def v179 := [t10,t36,t117,t12,t13]
def v180 := [t10,t117,t11,t12,t13]
def v181 := [t10,t36,t11,t34,t13]
def v182 := [t10,t36,t11,t12,t35]
def v183 := [t10,t26,t36,t11,t13]
def v184 := [t10,t36,t28,t11,t13]
def v185 := [t10,t36,t11,t12,t31]
def v186 := [t10,t36,t11,t33,t12]
def v187 := [t10,t36,t37,t11]
def v188 := [t10,t36,t37,t11,t12]
def v189 := [t10,t36,t37,t11,t13]
def map27_5 : Projection 12 12 := pick [5,6,2,3,8,0,1,7,4,11,10,9] rfl (by decide +kernel) (by decide)
def v190 := [t0,t1,t96,t2,t3,t4]
def t118 := 0xffec92fffc93
def v191 := [t0,t1,t2,t3,t4,t118]
def v192 := [t0,t97,t1,t2,t3,t4]
def t119 := 0x72a00062b000
def v193 := [t0,t1,t119,t2,t3,t4]
def t120 := 0xe00f00
def v194 := [t120,t0,t1,t2,t3,t4]
def t121 := 0xf78fd8ff8ffc
def v195 := [t0,t1,t2,t3,t121,t4]
def t122 := 0xa1851801801c
def v196 := [t0,t1,t2,t122,t3,t4]
def t123 := 0x560ac01e00e0
def v197 := [t0,t123,t1,t2,t3,t4]
def t124 := 0xa18000e18000
def v198 := [t0,t1,t2,t124,t3,t4]
def v199 := [t0,t1,t2,t3,t4,t85]
def t125 := 0x518000f1c
def v200 := [t125,t0,t1,t2,t3,t4]
def v201 := [t0,t1,t102,t2,t3]
def v202 := [t0,t1,t102,t2,t3,t4]
theorem b0 : Ban 6 3 v2 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w0 : Wide 6 3 v2 := viaSub (ws := [v2]) (consBan b0 (nilBan 6 3)) (by decide) (by decide +kernel)
theorem b1 : Ban 24 6 v1 := smallByCut p31_13 w0
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
theorem b53 : Ban 24 6 v3 := smallByCut p31_27 w1
theorem b54 : Ban 12 4 v56 := checkedSmall
theorem b55 : Ban 12 4 v57 := checkedSmall
theorem b56 : Ban 12 4 v58 := checkedSmall
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b71 : Ban 12 5 v15 := viaBranch (ws := [v56,v13,v57,v58,v59,v60,v61,v62,v63,v64,v65,v14,v66,v67,v68,v69,v70,v71,v72]) (consBan b54 (consBan b10 (consBan b55 (consBan b56 (consBan b57 (consBan b58 (consBan b59 (consBan b60 (consBan b61 (consBan b62 (consBan b63 (consBan b11 (consBan b64 (consBan b65 (consBan b66 (consBan b67 (consBan b68 (consBan b69 (consBan b70 (nilBan 12 4)))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w2 : Wide 12 5 v15 := viaSub (ws := [v4,v15]) (consBan b26 (consBan b71 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b72 : Ban 24 6 v55 := smallByCut p31_27 w2
theorem b73 : Ban 24 6 v54 := viaPerm map31_1 map31_1 b72 (by decide +kernel) (by decide +kernel)
theorem b74 : Ban 24 6 v73 := smallByCut p31_13 w0
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b196 : Ban 12 5 v27 := viaBranch (ws := [v61,v167,v168,v169,v170,v171,v172,v72,v173,v174,v175,v176,v177,v178,v179,v180,v181,v25,v182,v26,v183,v184,v185,v186,v187,v188,v189]) (consBan b59 (consBan b173 (consBan b174 (consBan b175 (consBan b176 (consBan b177 (consBan b178 (consBan b70 (consBan b179 (consBan b180 (consBan b181 (consBan b182 (consBan b183 (consBan b184 (consBan b185 (consBan b186 (consBan b187 (consBan b22 (consBan b188 (consBan b23 (consBan b189 (consBan b190 (consBan b191 (consBan b192 (consBan b193 (consBan b194 (consBan b195 (nilBan 12 4)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b197 : Ban 12 5 v20 := viaPerm map27_5 map27_5 b196 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w9 : Wide 12 5 v20 := viaSub (ws := [v4,v20]) (consBan b26 (consBan b197 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b76 : Ban 24 6 v74 := smallByCut p31_27 w9
theorem b77 : Ban 24 6 v75 := smallByCut p31_27 w9
theorem b78 : Ban 24 6 v76 := smallByCut p31_27 w9
theorem b79 : Ban 24 6 v77 := smallByCut p31_27 w9
theorem b80 : Ban 12 4 v79 := checkedSmall
theorem b81 : Ban 12 4 v80 := checkedSmall
theorem b82 : Ban 12 4 v81 := checkedSmall
theorem b83 : Ban 12 4 v82 := checkedSmall
theorem b84 : Ban 12 4 v83 := checkedSmall
theorem b85 : Ban 12 4 v84 := checkedSmall
theorem b86 : Ban 12 4 v85 := checkedSmall
theorem b87 : Ban 12 4 v86 := checkedSmall
theorem b88 : Ban 12 4 v87 := checkedSmall
theorem b89 : Ban 12 4 v88 := checkedSmall
theorem b90 : Ban 12 4 v89 := checkedSmall
theorem b91 : Ban 12 4 v90 := checkedSmall
theorem b92 : Ban 12 4 v91 := checkedSmall
theorem b93 : Ban 12 4 v92 := checkedSmall
theorem b94 : Ban 12 4 v93 := checkedSmall
theorem b95 : Ban 12 4 v94 := checkedSmall
theorem b96 : Ban 12 4 v95 := checkedSmall
theorem b97 : Ban 12 4 v96 := checkedSmall
theorem b98 : Ban 12 4 v97 := checkedSmall
theorem b99 : Ban 12 4 v98 := checkedSmall
theorem b100 : Ban 12 4 v99 := checkedSmall
theorem b101 : Ban 12 4 v100 := checkedSmall
theorem b102 : Ban 12 4 v101 := checkedSmall
theorem b103 : Ban 12 4 v102 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b104 : Ban 12 5 v9 := viaBranch (ws := [v79,v11,v80,v81,v82,v83,v84,v85,v86,v87,v88,v12,v89,v90,v91,v92,v61,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102]) (consBan b80 (consBan b8 (consBan b81 (consBan b82 (consBan b83 (consBan b84 (consBan b85 (consBan b86 (consBan b87 (consBan b88 (consBan b89 (consBan b9 (consBan b90 (consBan b91 (consBan b92 (consBan b93 (consBan b59 (consBan b94 (consBan b95 (consBan b96 (consBan b97 (consBan b98 (consBan b99 (consBan b100 (consBan b101 (consBan b102 (consBan b103 (nilBan 12 4)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w5 : Wide 12 5 v9 := viaSub (ws := [v4,v9]) (consBan b26 (consBan b104 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b105 : Ban 24 6 v78 := smallByCut p31_27 w5
theorem b106 : Ban 12 5 v10 := viaPerm map27_2 map27_2 b52 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w6 : Wide 12 5 v10 := viaSub (ws := [v4,v10]) (consBan b26 (consBan b106 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b107 : Ban 24 6 v103 := smallByCut p31_27 w6
theorem b108 : Ban 12 5 v11 := viaPerm map27_1 map27_1 b71 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w7 : Wide 12 5 v11 := viaSub (ws := [v4,v11]) (consBan b26 (consBan b108 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b109 : Ban 24 6 v104 := smallByCut p31_27 w7
theorem b110 : Ban 12 4 v106 := checkedSmall
theorem b111 : Ban 12 4 v107 := checkedSmall
theorem b112 : Ban 12 4 v108 := checkedSmall
theorem b113 : Ban 12 4 v109 := checkedSmall
theorem b114 : Ban 12 4 v110 := checkedSmall
theorem b115 : Ban 12 4 v111 := checkedSmall
theorem b116 : Ban 12 4 v112 := checkedSmall
theorem b117 : Ban 12 4 v113 := checkedSmall
theorem b118 : Ban 12 4 v114 := checkedSmall
theorem b119 : Ban 12 4 v115 := checkedSmall
theorem b120 : Ban 12 4 v116 := checkedSmall
theorem b121 : Ban 12 4 v117 := checkedSmall
theorem b122 : Ban 12 4 v118 := checkedSmall
theorem b123 : Ban 12 4 v119 := checkedSmall
theorem b124 : Ban 12 4 v120 := checkedSmall
theorem b125 : Ban 12 4 v121 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b126 : Ban 12 5 v8 := viaBranch (ws := [v6,v33,v106,v107,v108,v109,v5,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121]) (consBan b3 (consBan b31 (consBan b110 (consBan b111 (consBan b112 (consBan b113 (consBan b2 (consBan b114 (consBan b115 (consBan b116 (consBan b117 (consBan b118 (consBan b119 (consBan b120 (consBan b121 (consBan b122 (consBan b123 (consBan b124 (consBan b125 (nilBan 12 4)))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b127 : Ban 12 5 v12 := viaPerm map27_2 map27_2 b126 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w8 : Wide 12 5 v12 := viaSub (ws := [v4,v12]) (consBan b26 (consBan b127 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b128 : Ban 24 6 v105 := smallByCut p31_27 w8
theorem b129 : Ban 24 6 v122 := smallByCut p31_13 w0
theorem b130 : Ban 24 6 v123 := viaPerm map31_1 map31_1 b53 (by decide +kernel) (by decide +kernel)
theorem b131 : Ban 24 6 v124 := smallByCut p31_13 w0
theorem b132 : Ban 24 6 v125 := smallByCut p31_13 w0
theorem b134 : Ban 24 6 v126 := smallByCut p31_27 w9
theorem b135 : Ban 24 6 v128 := smallByCut p31_27 w9
theorem b136 : Ban 24 6 v129 := smallByCut p31_27 w9
theorem b137 : Ban 24 6 v130 := smallByCut p31_13 w0
theorem b138 : Ban 24 6 v131 := smallByCut p31_27 w9
theorem b140 : Ban 24 6 v132 := smallByCut p31_13 w0
theorem b141 : Ban 24 5 v136 := checkedSmall
theorem b142 : Ban 24 5 v137 := checkedSmall
theorem b143 : Ban 24 5 v138 := checkedSmall
theorem b144 : Ban 24 5 v139 := smallByCut p31_13 w0
theorem b145 : Ban 24 5 v140 := checkedSmall
theorem b146 : Ban 24 5 v141 := checkedSmall
theorem b147 : Ban 24 5 v142 := checkedSmall
theorem b148 : Ban 24 5 v143 := checkedSmall
theorem b149 : Ban 24 5 v144 := checkedSmall
theorem b150 : Ban 24 5 v145 := smallByCut p31_13 w0
theorem b151 : Ban 24 5 v146 := smallByCut p31_13 w0
theorem b152 : Ban 24 5 v147 := smallByCut p31_13 w0
theorem b153 : Ban 24 5 v148 := smallByCut p31_13 w0
theorem b154 : Ban 24 5 v149 := smallByCut p31_13 w0
theorem b155 : Ban 24 5 v150 := smallByCut p31_13 w0
theorem b156 : Ban 24 5 v151 := smallByCut p31_13 w0
theorem b157 : Ban 24 5 v152 := checkedSmall
theorem b158 : Ban 24 5 v153 := smallByCut p31_13 w0
theorem b159 : Ban 24 5 v154 := smallByCut p31_27 w9
theorem b160 : Ban 24 5 v155 := checkedSmall
theorem b161 : Ban 24 5 v156 := smallByCut p31_27 w9
theorem b162 : Ban 24 5 v157 := checkedSmall
theorem b163 : Ban 24 5 v158 := smallByCut p31_13 w0
theorem b164 : Ban 24 5 v159 := smallByCut p31_13 w0
theorem b165 : Ban 24 5 v160 := smallByCut p31_13 w0
theorem solidb188 : Wide 12 4 v182 := solid b188
theorem b166 : Ban 24 5 v161 := smallByCut p31_27 solidb188
theorem b167 : Ban 24 5 v162 := smallByCut p31_13 w0
theorem b168 : Ban 24 5 v163 := smallByCut p31_13 w0
theorem b169 : Ban 24 5 v164 := smallByCut p31_13 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b170 : Ban 24 6 v135 := viaBranch (ws := [v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v163,v164]) (consBan b141 (consBan b142 (consBan b143 (consBan b144 (consBan b145 (consBan b146 (consBan b147 (consBan b148 (consBan b149 (consBan b150 (consBan b151 (consBan b152 (consBan b153 (consBan b154 (consBan b155 (consBan b156 (consBan b157 (consBan b158 (consBan b159 (consBan b160 (consBan b161 (consBan b162 (consBan b163 (consBan b164 (consBan b165 (consBan b166 (consBan b167 (consBan b168 (consBan b169 (nilBan 24 5)))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b171 : Ban 24 6 v134 := viaPerm map31_1 map31_1 b170 (by decide +kernel) (by decide +kernel)
theorem b172 : Ban 24 6 v165 := smallByCut p31_13 w0
theorem b198 : Ban 24 6 v166 := smallByCut p31_27 w9
theorem b199 : Ban 24 6 v190 := smallByCut p31_13 w0
theorem b200 : Ban 24 6 v191 := smallByCut p31_13 w0
theorem b202 : Ban 24 6 v192 := smallByCut p31_13 w0
theorem b201 : Ban 24 6 v193 := smallByCut p31_13 w0
theorem b203 : Ban 24 6 v194 := smallByCut p31_27 w9
theorem b204 : Ban 24 6 v195 := smallByCut p31_27 w9
theorem b205 : Ban 24 6 v196 := smallByCut p31_27 w9
theorem b206 : Ban 24 6 v197 := smallByCut p31_27 w9
theorem b207 : Ban 24 6 v198 := smallByCut p31_13 w0
theorem b133 : Ban 24 6 v127 := smallByCut p31_27 w9
theorem b208 : Ban 24 6 v199 := smallByCut p31_27 w9
theorem b209 : Ban 24 6 v200 := smallByCut p31_27 w9
theorem b210 : Ban 24 6 v201 := smallByCut p31_27 w9
theorem b211 : Ban 24 6 v202 := smallByCut p31_13 w0
theorem b139 : Ban 24 6 v133 := smallByCut p31_13 w0
theorem b212 : Ban 24 6 v164 := viaPerm map31_1 map31_1 b198 (by decide +kernel) (by decide +kernel)
theorem b213 : Ban 24 6 v163 := smallByCut p31_13 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b214 : Ban 24 7 v0 := viaBranch (ws := [v1,v3,v54,v73,v74,v75,v76,v77,v78,v103,v104,v105,v122,v123,v55,v124,v125,v126,v128,v129,v130,v131,v132,v134,v165,v166,v190,v191,v192,v193,v194,v195,v196,v197,v198,v127,v199,v200,v201,v202,v133,v135,v164,v163]) (consBan b1 (consBan b53 (consBan b73 (consBan b74 (consBan b76 (consBan b77 (consBan b78 (consBan b79 (consBan b105 (consBan b107 (consBan b109 (consBan b128 (consBan b129 (consBan b130 (consBan b72 (consBan b131 (consBan b132 (consBan b134 (consBan b135 (consBan b136 (consBan b137 (consBan b138 (consBan b140 (consBan b171 (consBan b172 (consBan b198 (consBan b199 (consBan b200 (consBan b202 (consBan b201 (consBan b203 (consBan b204 (consBan b205 (consBan b206 (consBan b207 (consBan b133 (consBan b208 (consBan b209 (consBan b210 (consBan b211 (consBan b139 (consBan b170 (consBan b212 (consBan b213 (nilBan 24 6))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem verifiedPin : Wide 24 7 v0 := widen (by decide +kernel) b214
end PEqualNP.Outside.L_meta_16907.Support

namespace PEqualNP.Outside.L_meta_16907.Data
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_16907.Support
def target (x : Fin 6 → Bool) := Nat.testBit (4277074664 * 2 ^ 32 + 4272618152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def posBits : ℕ := 0x2679c71a69a65755345138e30c2c92471450c3
def negBits : ℕ := 0x659851848a616512401286204288046101081
def sample (bank : ℕ) (i : Fin 25) (j : Fin 6) := bank.testBit (6*i.val+j.val)
def inputs : List ℕ := [0x204a03f0ff,0x31a99259d4c93,0x3430a31e18f1c,0xac1580fe0fe0,0x1f7c000fff000,0x1000000]
def seeds : List Wire := [(false,0x204a03f0ff),(false,0x31a99259d4c93),(false,0x3430a31e18f1c),(false,0xac1580fe0fe0),(false,0x1f7c000fff000),(false,0x1000000)]
set_option maxHeartbeats 10000000 in
theorem listed : ∀ i : Fin 25, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (25+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 25, target (sample posBits i)=true ∧ target (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 25, ∀ b∈inputs, b.testBit i.val≠b.testBit (25+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 25 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 6 C=target) :
    ∃ k≤C.gates.countP counted, Live 25 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 6 → Bool) : C.eval (List.ofFn x)=target x := congrFun eq x
  have good : Good 25 out.2 := by
    intro i hi same
    let j : Fin 25 := ⟨i,hi⟩
    have diff : read i out=read (25+i) out := by
      change (out.1 != out.2.testBit i) = (out.1 != out.2.testBit (25+i))
      rw [same]
    have p := ev i;have n := ev (25+i)
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
def restrictRows : Projection 25 24 := pick (List.range 24) (by decide) (by decide) (by decide)
set_option maxHeartbeats 8000000 in
theorem core_floor : Wide 24 7 restricted := verifiedPin
theorem six_floor : Ban 25 8 inputs := viaCut restrictRows core_floor (by decide) (by decide +kernel) (by decide +kernel)
def witness : Circuit := ⟨[⟨.or,[2,4]⟩, ⟨.and,[1,6]⟩, ⟨.and,[5,7]⟩, ⟨.or,[2,7]⟩, ⟨.and,[3,9]⟩, ⟨.or,[8,10]⟩, ⟨.or,[1,6]⟩, ⟨.or,[3,12]⟩, ⟨.and,[0,13]⟩, ⟨.or,[11,14]⟩],15⟩
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
end PEqualNP.Outside.L_meta_16907.Data

theorem PEqualNP.Outside.L_meta_16907 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4272618152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4272618152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_16907.Data.mono_enough
