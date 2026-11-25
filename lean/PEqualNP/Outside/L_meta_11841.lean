import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11841.Ground

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

end PEqualNP.Outside.L_meta_11841.Ground

namespace PEqualNP.Outside.L_meta_11841.Frame
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List ℕ := [0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6]
def target (x : Fin 7 → Bool) := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

def witness : List Gate := [
  ⟨.or, [0,1]⟩,
  ⟨.or, [1,2]⟩,
  ⟨.or, [3,4]⟩,
  ⟨.or, [0,6]⟩,
  ⟨.or, [4,6]⟩,
  ⟨.or, [3,7]⟩,
  ⟨.and, [9,10]⟩,
  ⟨.and, [8,11]⟩,
  ⟨.and, [5,12]⟩,
  ⟨.or, [13,14]⟩,
  ⟨.or, [15,16]⟩]

theorem good : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

theorem correct : ∀ x : Fin 7 → Bool, Circuit.eval ⟨witness,17⟩ (List.ofFn x) = target x := by
  decide +kernel

theorem finish (lower : ∀ (gs : List Gate) (o : ℕ), FanInTwo ⟨gs,o⟩ →
    (∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) →
    (∃ g ∈ gs, g.op = .not) → 11 ≤ gs.length) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o fan _ computes
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · exact ⟨witness, 17, good, lower gs o fan computes hn, correct⟩
  · refine ⟨gs, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨op, len⟩ := fan g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),len⟩

end PEqualNP.Outside.L_meta_11841.Frame

namespace PEqualNP.Outside.L_meta_11841.Cert
open PEqualNP.Outside.L_meta_11841.Ground
def t0 : ℕ := 0xacc00acc00acc00acc00acc00acc00acc00acc00acc00acc00acc000000000000000fffff00000fffff0000000000fffff0000000000
def t1 : ℕ := 0x2f0002f0002f0002f0002f0002f0002f0002f0002f0002f0002f0000000fffff0000000000fffff0000000000000000000000000fffff
def t2 : ℕ := 0x8cf008cf008cf008cf008cf008cf008cf008cf008cf008cf008cf00000000000fffff00000000000000000000fffff000000000000000
def t3 : ℕ := 0x1300013000130001300013000130001300013000130001300013000fffff000000000000000000000000000000fffffffffffffff00000
def t4 : ℕ := 0x400aa400aa400aa400aa400aa400aa400aa400aa400aa400aa400aa000000000000000000000000000000fffff0000000000ffffffffff
def t5 : ℕ := 0x9c0009c0009c0009c0009c0009c0009c0009c0009c0009c0009c00000000000000000000000fffffffffffffff00000000000000000000
def t6 : ℕ := 0xe0000e0000e0000e0000e0000e0000e0000e0000e0000e0000e0000ffffffffffffffffffff00000000000000000000000000000000000
def v0 : List ℕ := [t0,t1,t2,t3,t4,t5,t6]
def t7 : ℕ := 0xa0000a0000a0000a0000a0000a0000a0000a0000a0000a0000a000000000000000000000000000000000000000000000000000000000
def v1 : List ℕ := [t7,t0,t1,t2,t3,t4,t5,t6]
def t8 : ℕ := 0x40810201fffff
def t9 : ℕ := 0x2850a14fe0007f
def t10 : ℕ := 0xb162c580003f80
def t11 : ℕ := 0xc183060fffc000
def v2 : List ℕ := [t8,t9,t10,t11]
theorem b0 : Ban 28 4 v2 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w0 : Wide 28 4 v2 := viaSub (ws := [v2]) (consBan b0 (nilBan 28 4)) (by decide) (by decide +kernel)
def p127_114 : Projection 220 28 := pick [40,42,52,54,56,57,59,100,102,112,114,116,117,119,140,142,152,154,156,157,159,200,202,212,214,216,217,219] rfl (by decide +kernel) (by decide)
theorem b1 : Ban 220 8 v1 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t12 : ℕ := 0x2fcc02fcc02fcc02fcc02fcc02fcc02fcc02fcc02fcc02fcc02fcc00000fffff00000fffffffffffffff0000000000fffff00000fffff
def v3 : List ℕ := [t0,t12,t2,t3,t4,t5,t6]
def t13 : ℕ := 0x280a0280a0280a00000ffc00fffff
def t14 : ℕ := 0xb02c0b02c0b02c003ff003ff00000
def t15 : ℕ := 0x2f0bc2f0bc2f0bcfffff003ff003ff
def t16 : ℕ := 0xb02c0b02c0b02c000000003ffffc00
def t17 : ℕ := 0xc0300c0300c0300fffffffc0000000
def v4 : List ℕ := [t13,t14,t15,t16,t17]
def t18 : ℕ := 0x20080200802008000000000000000
def v5 : List ℕ := [t18,t13,t14,t15,t16,t17]
theorem b2 : Ban 60 5 v5 := viaSmall (by decide +kernel) (by decide)
def t19 : ℕ := 0xb82e0b82e0b82e003ffffffffffff
def v6 : List ℕ := [t14,t19,t15,t16,t17]
theorem b3 : Ban 60 5 v6 := viaSmall (by decide +kernel) (by decide)
def v7 : List ℕ := [t13,t14,t19,t15,t16,t17]
theorem b4 : Ban 60 5 v7 := viaSmall (by decide +kernel) (by decide)
def t20 : ℕ := 0x802008020080200000ffc00fffff
def v8 : List ℕ := [t20,t14,t15,t16,t17]
theorem b5 : Ban 60 5 v8 := viaSmall (by decide +kernel) (by decide)
def v9 : List ℕ := [t20,t13,t14,t15,t16,t17]
theorem b6 : Ban 60 5 v9 := viaSmall (by decide +kernel) (by decide)
def t21 : ℕ := 0x90240902409024003ff003ff00000
def v10 : List ℕ := [t13,t21,t14,t15,t16,t17]
theorem b7 : Ban 60 5 v10 := viaSmall (by decide +kernel) (by decide)
def t22 : ℕ := 0x200802008020080000000000003ff
def v11 : List ℕ := [t22,t13,t14,t15,t16,t17]
theorem b8 : Ban 60 5 v11 := viaSmall (by decide +kernel) (by decide)
def t23 : ℕ := 0x2f8be2f8be2f8befffffffffffffff
def v12 : List ℕ := [t13,t14,t15,t23,t16,t17]
theorem b9 : Ban 60 5 v12 := viaSmall (by decide +kernel) (by decide)
def t24 : ℕ := 0x802008020080200000ffc00ffc00
def v13 : List ℕ := [t24,t13,t14,t15,t16,t17]
theorem b10 : Ban 60 5 v13 := viaSmall (by decide +kernel) (by decide)
def t25 : ℕ := 0x2d0b42d0b42d0b4fffff003ff00000
def v14 : List ℕ := [t13,t14,t25,t15,t16,t17]
theorem b11 : Ban 60 5 v14 := viaSmall (by decide +kernel) (by decide)
def t26 : ℕ := 0xffc00
def v15 : List ℕ := [t26,t13,t14,t15,t16,t17]
theorem b12 : Ban 60 5 v15 := viaSmall (by decide +kernel) (by decide)
def t27 : ℕ := 0xb2acab2acab2aca00000ffffffffff
def v16 : List ℕ := [t13,t14,t15,t16,t27,t17]
theorem b13 : Ban 60 5 v16 := viaSmall (by decide +kernel) (by decide)
def t28 : ℕ := 0x280a0280a0280a00000ffc00003ff
def v17 : List ℕ := [t28,t13,t14,t15,t16,t17]
theorem b14 : Ban 60 5 v17 := viaSmall (by decide +kernel) (by decide)
def t29 : ℕ := 0xb02c0b02c0b02c000000003ff00000
def v18 : List ℕ := [t13,t14,t15,t29,t16,t17]
theorem b15 : Ban 60 5 v18 := viaSmall (by decide +kernel) (by decide)
def t30 : ℕ := 0xffc0000000
def v19 : List ℕ := [t30,t13,t14,t15,t16,t17]
theorem b16 : Ban 60 5 v19 := viaSmall (by decide +kernel) (by decide)
def t31 : ℕ := 0xc2b0ac2b0ac2b0afffffffc00fffff
def v20 : List ℕ := [t13,t14,t15,t16,t17,t31]
theorem b17 : Ban 60 5 v20 := viaSmall (by decide +kernel) (by decide)
def t32 : ℕ := 0x280a0280a0280a0000000000fffff
def v21 : List ℕ := [t32,t13,t14,t15,t16,t17]
theorem b18 : Ban 60 5 v21 := viaSmall (by decide +kernel) (by decide)
def t33 : ℕ := 0xc0300c0300c0300fffff0000000000
def v22 : List ℕ := [t13,t14,t15,t16,t33,t17]
theorem b19 : Ban 60 5 v22 := viaSmall (by decide +kernel) (by decide)
def t34 : ℕ := 0x240902409024090ffc0000000003ff
def v23 : List ℕ := [t13,t14,t34,t16,t17]
theorem b20 : Ban 60 5 v23 := viaSmall (by decide +kernel) (by decide)
def v24 : List ℕ := [t13,t34,t15,t16,t17]
theorem b21 : Ban 60 5 v24 := viaSmall (by decide +kernel) (by decide)
def v25 : List ℕ := [t13,t14,t34,t15,t16,t17]
theorem b22 : Ban 60 5 v25 := viaSmall (by decide +kernel) (by decide)
def t35 : ℕ := 0x3ff00000
def v26 : List ℕ := [t35,t13,t14,t15,t16,t17]
theorem b23 : Ban 60 5 v26 := viaSmall (by decide +kernel) (by decide)
def t36 : ℕ := 0xbb2ecbb2ecbb2ec003ff003ffffc00
def v27 : List ℕ := [t13,t14,t15,t16,t36,t17]
theorem b24 : Ban 60 5 v27 := viaSmall (by decide +kernel) (by decide)
def t37 : ℕ := 0xb02c0b02c0b02c003ff0000000000
def v28 : List ℕ := [t13,t37,t14,t15,t16,t17]
theorem b25 : Ban 60 5 v28 := viaSmall (by decide +kernel) (by decide)
def t38 : ℕ := 0xb02c0b02c0b02c00000000000ffc00
def v29 : List ℕ := [t13,t14,t15,t38,t16,t17]
theorem b26 : Ban 60 5 v29 := viaSmall (by decide +kernel) (by decide)
def t39 : ℕ := 0x3ff0000000000
def v30 : List ℕ := [t39,t13,t14,t15,t16,t17]
theorem b27 : Ban 60 5 v30 := viaSmall (by decide +kernel) (by decide)
def t40 : ℕ := 0xcb32ccb32ccb32cffffffffff00000
def v31 : List ℕ := [t13,t15,t16,t17,t40]
theorem b28 : Ban 60 5 v31 := viaSmall (by decide +kernel) (by decide)
def v32 : List ℕ := [t13,t14,t15,t16,t17,t40]
theorem b29 : Ban 60 5 v32 := viaSmall (by decide +kernel) (by decide)
def t41 : ℕ := 0xb02c0b02c0b02c00000003ff00000
def v33 : List ℕ := [t13,t41,t15,t16,t17]
theorem b30 : Ban 60 5 v33 := viaSmall (by decide +kernel) (by decide)
def v34 : List ℕ := [t13,t41,t14,t15,t16,t17]
theorem b31 : Ban 60 5 v34 := viaSmall (by decide +kernel) (by decide)
def t42 : ℕ := 0xc0300c0300c0300ffc00ffc0000000
def v35 : List ℕ := [t13,t14,t15,t16,t42,t17]
theorem b32 : Ban 60 5 v35 := viaSmall (by decide +kernel) (by decide)
def t43 : ℕ := 0x20080200802008000000003ff00000
def v36 : List ℕ := [t13,t14,t43,t15,t16,t17]
theorem b33 : Ban 60 5 v36 := viaSmall (by decide +kernel) (by decide)
def t44 : ℕ := 0xbf2fcbf2fcbf2fcfffff003fffffff
def v37 : List ℕ := [t13,t14,t16,t44,t17]
theorem b34 : Ban 60 5 v37 := viaSmall (by decide +kernel) (by decide)
def v38 : List ℕ := [t13,t14,t15,t16,t44,t17]
theorem b35 : Ban 60 5 v38 := viaSmall (by decide +kernel) (by decide)
def t45 : ℕ := 0xf03c0f03c0f03cfffff00000003ff
def v39 : List ℕ := [t13,t14,t45,t16,t17]
theorem b36 : Ban 60 5 v39 := viaSmall (by decide +kernel) (by decide)
def v40 : List ℕ := [t13,t14,t45,t15,t16,t17]
theorem b37 : Ban 60 5 v40 := viaSmall (by decide +kernel) (by decide)
def t46 : ℕ := 0x9024090240902400000000000ffc00
def v41 : List ℕ := [t13,t14,t15,t46,t16,t17]
theorem b38 : Ban 60 5 v41 := viaSmall (by decide +kernel) (by decide)
def t47 : ℕ := 0xfffff0000000000
def v42 : List ℕ := [t47,t13,t14,t15,t16,t17]
theorem b39 : Ban 60 5 v42 := viaSmall (by decide +kernel) (by decide)
def t48 : ℕ := 0xef3bcef3bcef3bcffffffffff003ff
def v43 : List ℕ := [t13,t14,t15,t16,t17,t48]
theorem b40 : Ban 60 5 v43 := viaSmall (by decide +kernel) (by decide)
def t49 : ℕ := 0x2f0bc2f0bc2f0bc00000003ff003ff
def v44 : List ℕ := [t13,t14,t49,t15,t16,t17]
theorem b41 : Ban 60 5 v44 := viaSmall (by decide +kernel) (by decide)
def t50 : ℕ := 0xc0300c0300c030000000ffc0000000
def v45 : List ℕ := [t13,t14,t15,t16,t50,t17]
theorem b42 : Ban 60 5 v45 := viaSmall (by decide +kernel) (by decide)
def t51 : ℕ := 0x802008020080200000000000000000
def v46 : List ℕ := [t13,t14,t15,t51,t16,t17]
theorem b43 : Ban 60 5 v46 := viaSmall (by decide +kernel) (by decide)
def t52 : ℕ := 0xf03c0f03c0f03c0ffffffffffffc00
def v47 : List ℕ := [t13,t14,t15,t16,t52]
theorem b44 : Ban 60 5 v47 := viaSmall (by decide +kernel) (by decide)
def v48 : List ℕ := [t13,t14,t15,t17,t52]
theorem b45 : Ban 60 5 v48 := viaSmall (by decide +kernel) (by decide)
def v49 : List ℕ := [t13,t14,t15,t16,t17,t52]
theorem b46 : Ban 60 5 v49 := viaSmall (by decide +kernel) (by decide)
def t53 : ℕ := 0x300c0300c0300c000000003ffffc00
def v50 : List ℕ := [t13,t14,t15,t53,t17]
theorem b47 : Ban 60 5 v50 := viaSmall (by decide +kernel) (by decide)
def v51 : List ℕ := [t13,t14,t15,t53,t16,t17]
theorem b48 : Ban 60 5 v51 := viaSmall (by decide +kernel) (by decide)
def t54 : ℕ := 0x401004010040100fffffffc0000000
def v52 : List ℕ := [t13,t14,t15,t54,t16]
theorem b49 : Ban 60 5 v52 := viaSmall (by decide +kernel) (by decide)
def v53 : List ℕ := [t13,t14,t15,t54,t16,t17]
theorem b50 : Ban 60 5 v53 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b51 : Ban 60 6 v4 := viaBranch (ws := [v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53]) (consBan b2 (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b10 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (consBan b19 (consBan b20 (consBan b21 (consBan b22 (consBan b23 (consBan b24 (consBan b25 (consBan b26 (consBan b27 (consBan b28 (consBan b29 (consBan b30 (consBan b31 (consBan b32 (consBan b33 (consBan b34 (consBan b35 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (consBan b40 (consBan b41 (consBan b42 (consBan b43 (consBan b44 (consBan b45 (consBan b46 (consBan b47 (consBan b48 (consBan b49 (consBan b50 (nilBan 60 5)))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w1 : Wide 60 6 v4 := viaSub (ws := [v4]) (consBan b51 (nilBan 60 6)) (by decide) (by decide +kernel)
def p127_59 : Projection 220 60 := pick [0,1,2,3,8,9,12,13,14,16,20,21,22,23,28,29,32,33,34,36,40,41,42,43,48,49,52,53,54,56,80,81,82,83,88,89,92,93,94,96,100,101,102,103,108,109,112,113,114,116,120,121,122,123,128,129,132,133,134,136] rfl (by decide +kernel) (by decide)
theorem b52 : Ban 220 8 v3 := viaCut p127_59 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v54 : List ℕ := [t1,t12,t2,t3,t4,t5,t6]
def t55 : ℕ := 0x2c0b02c0b02c0b0003ff00000003ff
def t56 : ℕ := 0x2f0bc2f0bc2f0bc003fffffff003ff
def t57 : ℕ := 0x300c0300c0300c0ffc00003ffffc00
def t58 : ℕ := 0x82a0a82a0a82a0a0000000000fffff
def v55 : List ℕ := [t55,t56,t57,t58,t17]
def t59 : ℕ := 0x300c0300c0300c00000fffff00000
def v56 : List ℕ := [t59,t55,t57,t58,t17]
theorem b53 : Ban 60 5 v56 := viaSmall (by decide +kernel) (by decide)
def v57 : List ℕ := [t59,t56,t57,t58,t17]
theorem b54 : Ban 60 5 v57 := viaSmall (by decide +kernel) (by decide)
def v58 : List ℕ := [t59,t55,t56,t57,t58,t17]
theorem b55 : Ban 60 5 v58 := viaSmall (by decide +kernel) (by decide)
def t60 : ℕ := 0x200802008020080000000000000000
def v59 : List ℕ := [t60,t55,t56,t57,t58,t17]
theorem b56 : Ban 60 5 v59 := viaSmall (by decide +kernel) (by decide)
def t61 : ℕ := 0x3c0f03c0f03c0f0fffff003fffffff
def v60 : List ℕ := [t55,t56,t61,t58,t17]
theorem b57 : Ban 60 5 v60 := viaSmall (by decide +kernel) (by decide)
def v61 : List ℕ := [t55,t56,t57,t61,t58,t17]
theorem b58 : Ban 60 5 v61 := viaSmall (by decide +kernel) (by decide)
def t62 : ℕ := 0xc0300c0300c030003ff00000003ff
def v62 : List ℕ := [t62,t55,t56,t57,t58,t17]
theorem b59 : Ban 60 5 v62 := viaSmall (by decide +kernel) (by decide)
def t63 : ℕ := 0x100401004010040ffc00003ffffc00
def v63 : List ℕ := [t63,t55,t56,t58,t17]
theorem b60 : Ban 60 5 v63 := viaSmall (by decide +kernel) (by decide)
def v64 : List ℕ := [t63,t55,t56,t57,t58,t17]
theorem b61 : Ban 60 5 v64 := viaSmall (by decide +kernel) (by decide)
def t64 : ℕ := 0x3ff
def v65 : List ℕ := [t64,t55,t56,t57,t58,t17]
theorem b62 : Ban 60 5 v65 := viaSmall (by decide +kernel) (by decide)
def t65 : ℕ := 0xaeabaaeabaaeaba003ff00000fffff
def v66 : List ℕ := [t55,t56,t57,t58,t65,t17]
theorem b63 : Ban 60 5 v66 := viaSmall (by decide +kernel) (by decide)
def t66 : ℕ := 0x2c0b02c0b02c0b0003ff0000000000
def v67 : List ℕ := [t66,t55,t56,t57,t58,t17]
theorem b64 : Ban 60 5 v67 := viaSmall (by decide +kernel) (by decide)
def t67 : ℕ := 0x82a0a82a0a82a0a0000000000ffc00
def v68 : List ℕ := [t55,t56,t57,t67,t58,t17]
theorem b65 : Ban 60 5 v68 := viaSmall (by decide +kernel) (by decide)
def v69 : List ℕ := [t39,t55,t56,t57,t58,t17]
theorem b66 : Ban 60 5 v69 := viaSmall (by decide +kernel) (by decide)
def t68 : ℕ := 0xec3b0ec3b0ec3b0fffffffc00003ff
def v70 : List ℕ := [t56,t57,t58,t17,t68]
theorem b67 : Ban 60 5 v70 := viaSmall (by decide +kernel) (by decide)
def v71 : List ℕ := [t55,t56,t57,t58,t17,t68]
theorem b68 : Ban 60 5 v71 := viaSmall (by decide +kernel) (by decide)
def t69 : ℕ := 0x2c0b02c0b02c0b00000000000003ff
def v72 : List ℕ := [t69,t56,t57,t58,t17]
theorem b69 : Ban 60 5 v72 := viaSmall (by decide +kernel) (by decide)
def v73 : List ℕ := [t69,t55,t56,t57,t58,t17]
theorem b70 : Ban 60 5 v73 := viaSmall (by decide +kernel) (by decide)
def v74 : List ℕ := [t55,t56,t57,t58,t42,t17]
theorem b71 : Ban 60 5 v74 := viaSmall (by decide +kernel) (by decide)
def v75 : List ℕ := [t43,t55,t56,t57,t58,t17]
theorem b72 : Ban 60 5 v75 := viaSmall (by decide +kernel) (by decide)
def t70 : ℕ := 0x3f0fc3f0fc3f0fcfffffffffffffff
def v76 : List ℕ := [t55,t56,t57,t70,t58,t17]
theorem b73 : Ban 60 5 v76 := viaSmall (by decide +kernel) (by decide)
def t71 : ℕ := 0xf03c0f03c0f03c003ffffc00003ff
def v77 : List ℕ := [t71,t55,t56,t57,t58,t17]
theorem b74 : Ban 60 5 v77 := viaSmall (by decide +kernel) (by decide)
def t72 : ℕ := 0x100401004010040ffc0000000ffc00
def v78 : List ℕ := [t72,t55,t56,t57,t58,t17]
theorem b75 : Ban 60 5 v78 := viaSmall (by decide +kernel) (by decide)
def v79 : List ℕ := [t22,t55,t56,t57,t58,t17]
theorem b76 : Ban 60 5 v79 := viaSmall (by decide +kernel) (by decide)
def t73 : ℕ := 0xafabeafabeafabe003ffffffffffff
def v80 : List ℕ := [t55,t57,t58,t73,t17]
theorem b77 : Ban 60 5 v80 := viaSmall (by decide +kernel) (by decide)
def v81 : List ℕ := [t55,t56,t57,t58,t73,t17]
theorem b78 : Ban 60 5 v81 := viaSmall (by decide +kernel) (by decide)
def t74 : ℕ := 0x2d0b42d0b42d0b4003fffffff00000
def v82 : List ℕ := [t55,t74,t57,t58,t17]
theorem b79 : Ban 60 5 v82 := viaSmall (by decide +kernel) (by decide)
def v83 : List ℕ := [t55,t74,t56,t57,t58,t17]
theorem b80 : Ban 60 5 v83 := viaSmall (by decide +kernel) (by decide)
def t75 : ℕ := 0x80a0280a0280a020000000000ffc00
def v84 : List ℕ := [t55,t56,t57,t75,t58,t17]
theorem b81 : Ban 60 5 v84 := viaSmall (by decide +kernel) (by decide)
def t76 : ℕ := 0x3ffffc0000000
def v85 : List ℕ := [t76,t55,t56,t57,t58,t17]
theorem b82 : Ban 60 5 v85 := viaSmall (by decide +kernel) (by decide)
def v86 : List ℕ := [t55,t56,t57,t58,t17,t48]
theorem b83 : Ban 60 5 v86 := viaSmall (by decide +kernel) (by decide)
def v87 : List ℕ := [t55,t49,t56,t57,t58,t17]
theorem b84 : Ban 60 5 v87 := viaSmall (by decide +kernel) (by decide)
def t77 : ℕ := 0xc0300c0300c0300ffc000000000000
def v88 : List ℕ := [t55,t56,t57,t58,t77,t17]
theorem b85 : Ban 60 5 v88 := viaSmall (by decide +kernel) (by decide)
def v89 : List ℕ := [t26,t55,t56,t57,t58,t17]
theorem b86 : Ban 60 5 v89 := viaSmall (by decide +kernel) (by decide)
def t78 : ℕ := 0xb2acab2acab2acaffc00003fffffff
def v90 : List ℕ := [t55,t56,t57,t58,t78,t17]
theorem b87 : Ban 60 5 v90 := viaSmall (by decide +kernel) (by decide)
def t79 : ℕ := 0x300c0300c0300c0ffc00003ff00000
def v91 : List ℕ := [t55,t56,t79,t57,t58,t17]
theorem b88 : Ban 60 5 v91 := viaSmall (by decide +kernel) (by decide)
def t80 : ℕ := 0x82a0a82a0a82a0a0000000000003ff
def v92 : List ℕ := [t55,t56,t57,t80,t58,t17]
theorem b89 : Ban 60 5 v92 := viaSmall (by decide +kernel) (by decide)
def t81 : ℕ := 0xffc000000000000
def v93 : List ℕ := [t81,t55,t56,t57,t58,t17]
theorem b90 : Ban 60 5 v93 := viaSmall (by decide +kernel) (by decide)
def v94 : List ℕ := [t55,t56,t57,t58,t17,t52]
theorem b91 : Ban 60 5 v94 := viaSmall (by decide +kernel) (by decide)
def v95 : List ℕ := [t55,t56,t53,t57,t58,t17]
theorem b92 : Ban 60 5 v95 := viaSmall (by decide +kernel) (by decide)
def t82 : ℕ := 0xc0300c0300c0300003ffffc0000000
def v96 : List ℕ := [t55,t56,t57,t58,t82,t17]
theorem b93 : Ban 60 5 v96 := viaSmall (by decide +kernel) (by decide)
def v97 : List ℕ := [t55,t56,t57,t51,t58,t17]
theorem b94 : Ban 60 5 v97 := viaSmall (by decide +kernel) (by decide)
def v98 : List ℕ := [t55,t56,t57,t58,t31]
theorem b95 : Ban 60 5 v98 := viaSmall (by decide +kernel) (by decide)
def v99 : List ℕ := [t55,t56,t57,t17,t31]
theorem b96 : Ban 60 5 v99 := viaSmall (by decide +kernel) (by decide)
def v100 : List ℕ := [t55,t56,t57,t58,t17,t31]
theorem b97 : Ban 60 5 v100 := viaSmall (by decide +kernel) (by decide)
def v101 : List ℕ := [t32,t55,t56,t57,t17]
theorem b98 : Ban 60 5 v101 := viaSmall (by decide +kernel) (by decide)
def v102 : List ℕ := [t32,t55,t56,t57,t58,t17]
theorem b99 : Ban 60 5 v102 := viaSmall (by decide +kernel) (by decide)
def v103 : List ℕ := [t55,t56,t57,t54,t58]
theorem b100 : Ban 60 5 v103 := viaSmall (by decide +kernel) (by decide)
def v104 : List ℕ := [t55,t56,t57,t54,t58,t17]
theorem b101 : Ban 60 5 v104 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b102 : Ban 60 6 v55 := viaBranch (ws := [v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104]) (consBan b53 (consBan b54 (consBan b55 (consBan b56 (consBan b57 (consBan b58 (consBan b59 (consBan b60 (consBan b61 (consBan b62 (consBan b63 (consBan b64 (consBan b65 (consBan b66 (consBan b67 (consBan b68 (consBan b69 (consBan b70 (consBan b71 (consBan b72 (consBan b73 (consBan b74 (consBan b75 (consBan b76 (consBan b77 (consBan b78 (consBan b79 (consBan b80 (consBan b81 (consBan b82 (consBan b83 (consBan b84 (consBan b85 (consBan b86 (consBan b87 (consBan b88 (consBan b89 (consBan b90 (consBan b91 (consBan b92 (consBan b93 (consBan b94 (consBan b95 (consBan b96 (consBan b97 (consBan b98 (consBan b99 (consBan b100 (consBan b101 (nilBan 60 5)))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w2 : Wide 60 6 v55 := viaSub (ws := [v55]) (consBan b102 (nilBan 60 6)) (by decide) (by decide +kernel)
def p127_91 : Projection 220 60 := pick [0,1,2,3,8,9,12,13,17,18,20,21,22,23,28,29,32,33,37,38,40,41,42,43,48,49,52,53,57,58,140,141,142,143,148,149,152,153,157,158,180,181,182,183,188,189,192,193,197,198,200,201,202,203,208,209,212,213,217,218] rfl (by decide +kernel) (by decide)
theorem b103 : Ban 220 8 v54 := viaCut p127_91 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v105 : List ℕ := [t0,t1,t12,t2,t3,t4,t5,t6]
def t83 : ℕ := 0x2220ff
def t84 : ℕ := 0x444f0f
def t85 : ℕ := 0x888ff0
def v106 : List ℕ := [t83,t84,t85]
theorem b104 : Ban 12 3 v106 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w3 : Wide 12 3 v106 := viaSub (ws := [v106]) (consBan b104 (nilBan 12 3)) (by decide) (by decide +kernel)
def p127_84 : Projection 220 12 := pick [60,64,72,77,160,164,172,177,200,204,212,217] rfl (by decide +kernel) (by decide)
theorem b105 : Ban 220 8 v105 := viaCut p127_84 w3 (by decide) (by decide +kernel) (by decide +kernel)
def t86 : ℕ := 0xcc000cc000cc000cc000cc000cc000cc000cc000cc000cc000cc000000000000000fffff00000fffff0000000000fffff0000000000
def v107 : List ℕ := [t86,t1,t2,t3,t4,t5,t6]
def t87 : ℕ := 0x500a01402805000ffe003fffff
def t88 : ℕ := 0x580b01602c0587ff000000007ff
def t89 : ℕ := 0x11622c4588b116000001ffc00000
def t90 : ℕ := 0x2604c098130260000001fffff800
def t91 : ℕ := 0x380700e01c03807ffffe00000000
def v108 : List ℕ := [t87,t88,t89,t90,t91]
def t92 : ℕ := 0x7ff
def v109 : List ℕ := [t92,t87,t88,t89,t90,t91]
theorem b106 : Ban 55 5 v109 := viaSmall (by decide +kernel) (by decide)
def t93 : ℕ := 0x5d0ba1742e85d7ffffe003fffff
def v110 : List ℕ := [t87,t88,t93,t89,t90,t91]
theorem b107 : Ban 55 5 v110 := viaSmall (by decide +kernel) (by decide)
def t94 : ℕ := 0x500a01402805000ffe003ff800
def v111 : List ℕ := [t94,t87,t88,t89,t90,t91]
theorem b108 : Ban 55 5 v111 := viaSmall (by decide +kernel) (by decide)
def t95 : ℕ := 0x580b01602c0587ff00000000000
def v112 : List ℕ := [t87,t95,t88,t89,t90,t91]
theorem b109 : Ban 55 5 v112 := viaSmall (by decide +kernel) (by decide)
def t96 : ℕ := 0x40080100200400000000000000
def v113 : List ℕ := [t96,t87,t88,t89,t90,t91]
theorem b110 : Ban 55 5 v113 := viaSmall (by decide +kernel) (by decide)
def t97 : ℕ := 0x11722e45c8b917000fffffffffff
def v114 : List ℕ := [t87,t88,t97,t90,t91]
theorem b111 : Ban 55 5 v114 := viaSmall (by decide +kernel) (by decide)
def v115 : List ℕ := [t88,t89,t97,t90,t91]
theorem b112 : Ban 55 5 v115 := viaSmall (by decide +kernel) (by decide)
def v116 : List ℕ := [t87,t88,t89,t97,t90,t91]
theorem b113 : Ban 55 5 v116 := viaSmall (by decide +kernel) (by decide)
def t98 : ℕ := 0x100200400801000ffe003fffff
def v117 : List ℕ := [t98,t88,t89,t90,t91]
theorem b114 : Ban 55 5 v117 := viaSmall (by decide +kernel) (by decide)
def v118 : List ℕ := [t98,t87,t88,t89,t90,t91]
theorem b115 : Ban 55 5 v118 := viaSmall (by decide +kernel) (by decide)
def t99 : ℕ := 0x11222444889112000001ffc00000
def v119 : List ℕ := [t87,t88,t99,t90,t91]
theorem b116 : Ban 55 5 v119 := viaSmall (by decide +kernel) (by decide)
def v120 : List ℕ := [t87,t88,t99,t89,t90,t91]
theorem b117 : Ban 55 5 v120 := viaSmall (by decide +kernel) (by decide)
def t100 : ℕ := 0x3ff800
def v121 : List ℕ := [t100,t87,t88,t89,t90,t91]
theorem b118 : Ban 55 5 v121 := viaSmall (by decide +kernel) (by decide)
def t101 : ℕ := 0x2654ca99532a65000fffffffffff
def v122 : List ℕ := [t87,t88,t89,t90,t101,t91]
theorem b119 : Ban 55 5 v122 := viaSmall (by decide +kernel) (by decide)
def t102 : ℕ := 0x500a01402805000ffe000007ff
def v123 : List ℕ := [t102,t87,t88,t89,t90,t91]
theorem b120 : Ban 55 5 v123 := viaSmall (by decide +kernel) (by decide)
def t103 : ℕ := 0x2604c098130260000001ffc00000
def v124 : List ℕ := [t87,t88,t89,t103,t90,t91]
theorem b121 : Ban 55 5 v124 := viaSmall (by decide +kernel) (by decide)
def t104 : ℕ := 0xffe00000000
def v125 : List ℕ := [t104,t87,t88,t89,t90,t91]
theorem b122 : Ban 55 5 v125 := viaSmall (by decide +kernel) (by decide)
def t105 : ℕ := 0x38570ae15c2b857ffffe003fffff
def v126 : List ℕ := [t87,t88,t89,t90,t91,t105]
theorem b123 : Ban 55 5 v126 := viaSmall (by decide +kernel) (by decide)
def t106 : ℕ := 0x500a01402805000000003fffff
def v127 : List ℕ := [t106,t87,t88,t89,t90,t91]
theorem b124 : Ban 55 5 v127 := viaSmall (by decide +kernel) (by decide)
def t107 : ℕ := 0x380700e01c03807ff00000000000
def v128 : List ℕ := [t87,t88,t89,t90,t107,t91]
theorem b125 : Ban 55 5 v128 := viaSmall (by decide +kernel) (by decide)
def t108 : ℕ := 0x100200400801000000000000000
def v129 : List ℕ := [t87,t108,t88,t89,t90,t91]
theorem b126 : Ban 55 5 v129 := viaSmall (by decide +kernel) (by decide)
def t109 : ℕ := 0x15e2bc578af15e7ff001ffc007ff
def v130 : List ℕ := [t87,t88,t109,t90,t91]
theorem b127 : Ban 55 5 v130 := viaSmall (by decide +kernel) (by decide)
def v131 : List ℕ := [t87,t89,t109,t90,t91]
theorem b128 : Ban 55 5 v131 := viaSmall (by decide +kernel) (by decide)
def v132 : List ℕ := [t87,t88,t89,t109,t90,t91]
theorem b129 : Ban 55 5 v132 := viaSmall (by decide +kernel) (by decide)
def t110 : ℕ := 0x48090120240487ff000000007ff
def v133 : List ℕ := [t87,t110,t89,t90,t91]
theorem b130 : Ban 55 5 v133 := viaSmall (by decide +kernel) (by decide)
def v134 : List ℕ := [t87,t110,t88,t89,t90,t91]
theorem b131 : Ban 55 5 v134 := viaSmall (by decide +kernel) (by decide)
def t111 : ℕ := 0x10620c41883106000001ffc00000
def v135 : List ℕ := [t87,t88,t111,t90,t91]
theorem b132 : Ban 55 5 v135 := viaSmall (by decide +kernel) (by decide)
def v136 : List ℕ := [t87,t88,t111,t89,t90,t91]
theorem b133 : Ban 55 5 v136 := viaSmall (by decide +kernel) (by decide)
def t112 : ℕ := 0x400801002004000000000000000
def v137 : List ℕ := [t87,t112,t88,t89,t90,t91]
theorem b134 : Ban 55 5 v137 := viaSmall (by decide +kernel) (by decide)
def t113 : ℕ := 0x2784f09e13c2787ff001ffffffff
def v138 : List ℕ := [t87,t88,t89,t113,t91]
theorem b135 : Ban 55 5 v138 := viaSmall (by decide +kernel) (by decide)
def v139 : List ℕ := [t87,t89,t90,t113,t91]
theorem b136 : Ban 55 5 v139 := viaSmall (by decide +kernel) (by decide)
def v140 : List ℕ := [t87,t88,t89,t90,t113,t91]
theorem b137 : Ban 55 5 v140 := viaSmall (by decide +kernel) (by decide)
def t114 : ℕ := 0x180300600c0187ff000000007ff
def v141 : List ℕ := [t87,t114,t89,t90,t91]
theorem b138 : Ban 55 5 v141 := viaSmall (by decide +kernel) (by decide)
def v142 : List ℕ := [t87,t114,t88,t89,t90,t91]
theorem b139 : Ban 55 5 v142 := viaSmall (by decide +kernel) (by decide)
def t115 : ℕ := 0x22044088110220000001fffff800
def v143 : List ℕ := [t87,t88,t89,t115,t91]
theorem b140 : Ban 55 5 v143 := viaSmall (by decide +kernel) (by decide)
def v144 : List ℕ := [t87,t88,t89,t115,t90,t91]
theorem b141 : Ban 55 5 v144 := viaSmall (by decide +kernel) (by decide)
def t116 : ℕ := 0x7ff00000000000
def v145 : List ℕ := [t116,t87,t88,t89,t90,t91]
theorem b142 : Ban 55 5 v145 := viaSmall (by decide +kernel) (by decide)
def t117 : ℕ := 0x3d87b0f61ec3d87ffffe000007ff
def v146 : List ℕ := [t87,t88,t89,t90,t91,t117]
theorem b143 : Ban 55 5 v146 := viaSmall (by decide +kernel) (by decide)
def t118 : ℕ := 0x580b01602c058000000000007ff
def v147 : List ℕ := [t87,t118,t88,t89,t90,t91]
theorem b144 : Ban 55 5 v147 := viaSmall (by decide +kernel) (by decide)
def t119 : ℕ := 0x380700e01c0380000ffe00000000
def v148 : List ℕ := [t87,t88,t89,t90,t119,t91]
theorem b145 : Ban 55 5 v148 := viaSmall (by decide +kernel) (by decide)
def t120 : ℕ := 0x1ffc00000
def v149 : List ℕ := [t120,t87,t88,t90,t91]
theorem b146 : Ban 55 5 v149 := viaSmall (by decide +kernel) (by decide)
def v150 : List ℕ := [t120,t87,t88,t89,t90,t91]
theorem b147 : Ban 55 5 v150 := viaSmall (by decide +kernel) (by decide)
def t121 : ℕ := 0x3766ecdd9bb376000001fffff800
def v151 : List ℕ := [t87,t88,t89,t90,t121,t91]
theorem b148 : Ban 55 5 v151 := viaSmall (by decide +kernel) (by decide)
def t122 : ℕ := 0x11622c4588b11600000000000000
def v152 : List ℕ := [t87,t88,t122,t89,t90,t91]
theorem b149 : Ban 55 5 v152 := viaSmall (by decide +kernel) (by decide)
def t123 : ℕ := 0x2604c098130260000000003ff800
def v153 : List ℕ := [t87,t88,t123,t90,t91]
theorem b150 : Ban 55 5 v153 := viaSmall (by decide +kernel) (by decide)
def v154 : List ℕ := [t87,t88,t89,t123,t90,t91]
theorem b151 : Ban 55 5 v154 := viaSmall (by decide +kernel) (by decide)
def t124 : ℕ := 0x1002004008010000000000000000
def v155 : List ℕ := [t87,t88,t124,t89,t90,t91]
theorem b152 : Ban 55 5 v155 := viaSmall (by decide +kernel) (by decide)
def t125 : ℕ := 0x39672ce59cb3967fffffffc00000
def v156 : List ℕ := [t87,t88,t89,t90,t125]
theorem b153 : Ban 55 5 v156 := viaSmall (by decide +kernel) (by decide)
def v157 : List ℕ := [t87,t88,t90,t91,t125]
theorem b154 : Ban 55 5 v157 := viaSmall (by decide +kernel) (by decide)
def v158 : List ℕ := [t87,t88,t89,t90,t91,t125]
theorem b155 : Ban 55 5 v158 := viaSmall (by decide +kernel) (by decide)
def t126 : ℕ := 0x1602c0580b016000001ffc00000
def v159 : List ℕ := [t87,t126,t88,t90,t91]
theorem b156 : Ban 55 5 v159 := viaSmall (by decide +kernel) (by decide)
def v160 : List ℕ := [t87,t126,t88,t89,t90,t91]
theorem b157 : Ban 55 5 v160 := viaSmall (by decide +kernel) (by decide)
def t127 : ℕ := 0x280500a01402807ffffe00000000
def v161 : List ℕ := [t87,t88,t89,t90,t127]
theorem b158 : Ban 55 5 v161 := viaSmall (by decide +kernel) (by decide)
def v162 : List ℕ := [t87,t88,t89,t90,t127,t91]
theorem b159 : Ban 55 5 v162 := viaSmall (by decide +kernel) (by decide)
def t128 : ℕ := 0x2004008010020000000000000000
def v163 : List ℕ := [t87,t88,t89,t128,t90,t91]
theorem b160 : Ban 55 5 v163 := viaSmall (by decide +kernel) (by decide)
def t129 : ℕ := 0x3e07c0f81f03e07ffffffffff800
def v164 : List ℕ := [t87,t88,t89,t90,t129]
theorem b161 : Ban 55 5 v164 := viaSmall (by decide +kernel) (by decide)
def v165 : List ℕ := [t87,t88,t89,t91,t129]
theorem b162 : Ban 55 5 v165 := viaSmall (by decide +kernel) (by decide)
def v166 : List ℕ := [t87,t88,t89,t90,t91,t129]
theorem b163 : Ban 55 5 v166 := viaSmall (by decide +kernel) (by decide)
def t130 : ℕ := 0x600c018030060000001fffff800
def v167 : List ℕ := [t87,t88,t130,t89,t91]
theorem b164 : Ban 55 5 v167 := viaSmall (by decide +kernel) (by decide)
def v168 : List ℕ := [t87,t88,t130,t89,t90,t91]
theorem b165 : Ban 55 5 v168 := viaSmall (by decide +kernel) (by decide)
def t131 : ℕ := 0x180300600c01807ffffe00000000
def v169 : List ℕ := [t87,t88,t89,t131,t90]
theorem b166 : Ban 55 5 v169 := viaSmall (by decide +kernel) (by decide)
def v170 : List ℕ := [t87,t88,t89,t131,t90,t91]
theorem b167 : Ban 55 5 v170 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b168 : Ban 55 6 v108 := viaBranch (ws := [v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v163,v164,v165,v166,v167,v168,v169,v170]) (consBan b106 (consBan b107 (consBan b108 (consBan b109 (consBan b110 (consBan b111 (consBan b112 (consBan b113 (consBan b114 (consBan b115 (consBan b116 (consBan b117 (consBan b118 (consBan b119 (consBan b120 (consBan b121 (consBan b122 (consBan b123 (consBan b124 (consBan b125 (consBan b126 (consBan b127 (consBan b128 (consBan b129 (consBan b130 (consBan b131 (consBan b132 (consBan b133 (consBan b134 (consBan b135 (consBan b136 (consBan b137 (consBan b138 (consBan b139 (consBan b140 (consBan b141 (consBan b142 (consBan b143 (consBan b144 (consBan b145 (consBan b146 (consBan b147 (consBan b148 (consBan b149 (consBan b150 (consBan b151 (consBan b152 (consBan b153 (consBan b154 (consBan b155 (consBan b156 (consBan b157 (consBan b158 (consBan b159 (consBan b160 (consBan b161 (consBan b162 (consBan b163 (consBan b164 (consBan b165 (consBan b166 (consBan b167 (nilBan 55 5))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w4 : Wide 55 6 v108 := viaSub (ws := [v108]) (consBan b168 (nilBan 55 6)) (by decide) (by decide +kernel)
def p127_61 : Projection 220 55 := pick [0,1,4,5,8,10,12,13,14,15,16,20,21,24,25,28,30,32,33,34,35,36,60,61,64,65,68,70,72,73,74,75,76,80,81,84,85,88,90,92,93,94,95,96,120,121,124,125,128,130,132,133,134,135,136] rfl (by decide +kernel) (by decide)
theorem b169 : Ban 220 8 v107 := viaCut p127_61 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v171 : List ℕ := [t86,t0,t1,t2,t3,t4,t5,t6]
theorem b170 : Ban 12 3 v106 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w5 : Wide 12 3 v106 := viaSub (ws := [v106]) (consBan b170 (nilBan 12 3)) (by decide) (by decide +kernel)
def p127_41 : Projection 220 12 := pick [0,1,8,14,80,81,88,94,120,121,128,134] rfl (by decide +kernel) (by decide)
theorem b171 : Ban 220 8 v171 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def t132 : ℕ := 0x25000250002500025000250002500025000250002500025000250000000fffff0000000000fffff0000000000000000000000000fffff
def v172 : List ℕ := [t0,t132,t2,t3,t4,t5,t6]
theorem b172 : Ban 220 8 v172 := viaCut p127_61 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v173 : List ℕ := [t0,t132,t1,t2,t3,t4,t5,t6]
theorem b173 : Ban 220 8 v173 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t133 : ℕ := 0x8c0008c0008c0008c0008c0008c0008c0008c0008c0008c0008c00000000000000000000000000000000000000000000000000000000
def v174 : List ℕ := [t133,t0,t1,t2,t3,t4,t5,t6]
theorem b174 : Ban 220 8 v174 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t134 : ℕ := 0x8efc08efc08efc08efc08efc08efc08efc08efc08efc08efc08efc0000000000ffffffffff00000fffff00000ffffffffff0000000000
def v175 : List ℕ := [t0,t1,t134,t3,t4,t5,t6]
theorem b175 : Ban 220 8 v175 := viaCut p127_61 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v176 : List ℕ := [t1,t2,t134,t3,t4,t5,t6]
def t135 : ℕ := 0xc0000c0000c0000c0000c0000c0000c0000c0000c0000c0000c000000000000000000000000000000000000000000000000000000000
def v177 : List ℕ := [t135,t1,t2,t134,t3,t4,t5,t6]
theorem b176 : Ban 28 3 v2 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w6 : Wide 28 3 v2 := viaSub (ws := [v2]) (consBan b176 (nilBan 28 3)) (by decide) (by decide +kernel)
theorem b177 : Ban 220 7 v177 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t136 : ℕ := 0xaff00aff00aff00aff00aff00aff00aff00aff00aff00aff00aff000000ffffffffff00000fffff0000000000fffff0000000000fffff
def v178 : List ℕ := [t134,t136,t3,t4,t5,t6]
def t137 : ℕ := 0x2a80aa02a80aa0000000fffffff
def t138 : ℕ := 0xbbf2efcbbf2efc0003fff0000000
def t139 : ℕ := 0xbfc2ff0bfc2ff0fffc0000003fff
def t140 : ℕ := 0xc003000c003000ffffffffffc000
def v179 : List ℕ := [t137,t138,t139,t140]
theorem b178 : Ban 56 5 v179 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w7 : Wide 56 5 v179 := viaSub (ws := [v179]) (consBan b178 (nilBan 56 5)) (by decide) (by decide +kernel)
def p127_47 : Projection 220 56 := pick [0,1,2,3,4,5,6,7,8,9,10,11,14,15,80,81,82,83,84,85,86,87,88,89,90,91,94,95,100,101,102,103,104,105,106,107,108,109,110,111,114,115,120,121,122,123,124,125,126,127,128,129,130,131,134,135] rfl (by decide +kernel) (by decide)
theorem b179 : Ban 220 7 v178 := viaCut p127_47 w7 (by decide) (by decide +kernel) (by decide +kernel)
def v180 : List ℕ := [t1,t134,t136,t3,t4,t5,t6]
theorem b180 : Ban 220 7 v180 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v181 : List ℕ := [t2,t134,t136,t3,t4,t5,t6]
theorem b181 : Ban 220 7 v181 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v182 : List ℕ := [t1,t2,t134,t136,t3,t4,t5,t6]
theorem b182 : Ban 220 7 v182 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t141 : ℕ := 0x23000230002300023000230002300023000230002300023000230000000fffff0000000000fffff0000000000000000000000000fffff
def v183 : List ℕ := [t141,t2,t134,t3,t4,t5,t6]
theorem b183 : Ban 220 7 v183 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v184 : List ℕ := [t141,t1,t2,t134,t3,t4,t5,t6]
theorem b184 : Ban 220 7 v184 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t142 : ℕ := 0x80f0080f0080f0080f0080f0080f0080f0080f0080f0080f0080f00000000000fffff00000000000000000000fffff000000000000000
def v185 : List ℕ := [t1,t142,t134,t3,t4,t5,t6]
theorem b185 : Ban 220 7 v185 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v186 : List ℕ := [t1,t142,t2,t134,t3,t4,t5,t6]
theorem b186 : Ban 220 7 v186 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t143 : ℕ := 0xe0000e0000e0000e0000e0000e0000e0000e0000e0000e0000e000000000000000000000000000000000000000000000000000000000
def v187 : List ℕ := [t143,t1,t2,t134,t3,t4,t5,t6]
theorem b187 : Ban 220 7 v187 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t144 : ℕ := 0xaffc0affc0affc0affc0affc0affc0affc0affc0affc0affc0affc00000fffffffffffffffffffffffff00000ffffffffff00000fffff
def v188 : List ℕ := [t1,t2,t144,t3,t4,t5,t6]
theorem b188 : Ban 220 7 v188 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v189 : List ℕ := [t2,t134,t144,t3,t4,t5,t6]
theorem b189 : Ban 220 7 v189 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v190 : List ℕ := [t1,t2,t134,t144,t3,t4,t5,t6]
theorem b190 : Ban 220 7 v190 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t145 : ℕ := 0x21000210002100021000210002100021000210002100021000210000000fffff0000000000fffff0000000000000000000000000fffff
def v191 : List ℕ := [t145,t2,t134,t3,t4,t5,t6]
theorem b191 : Ban 220 7 v191 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v192 : List ℕ := [t145,t1,t2,t134,t3,t4,t5,t6]
theorem b192 : Ban 220 7 v192 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t146 : ℕ := 0x80fc080fc080fc080fc080fc080fc080fc080fc080fc080fc080fc0000000000ffffffffff00000fffff00000ffffffffff0000000000
def v193 : List ℕ := [t1,t146,t2,t3,t4,t5,t6]
theorem b193 : Ban 220 7 v193 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v194 : List ℕ := [t1,t146,t2,t134,t3,t4,t5,t6]
theorem b194 : Ban 220 7 v194 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t147 : ℕ := 0x2000020000200002000020000200002000020000200002000020000000000000000000000000000000000000000000000000000000000
def v195 : List ℕ := [t147,t1,t2,t134,t3,t4,t5,t6]
theorem b195 : Ban 220 7 v195 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t148 : ℕ := 0x13f0013f0013f0013f0013f0013f0013f0013f0013f0013f0013f00ffffffffff0000000000fffff0000000000ffffffffffffffffffff
def v196 : List ℕ := [t1,t2,t134,t148,t4,t5,t6]
theorem b196 : Ban 220 7 v196 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v197 : List ℕ := [t2,t134,t3,t148,t4,t5,t6]
theorem b197 : Ban 220 7 v197 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v198 : List ℕ := [t1,t2,t134,t3,t148,t4,t5,t6]
theorem b198 : Ban 220 7 v198 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t149 : ℕ := 0xf0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000000fffff0000000000fffff0000000000000000000000000fffff
def v199 : List ℕ := [t149,t2,t134,t3,t4,t5,t6]
theorem b199 : Ban 220 7 v199 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v200 : List ℕ := [t149,t1,t2,t134,t3,t4,t5,t6]
theorem b200 : Ban 220 7 v200 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t150 : ℕ := 0x1100011000110001100011000110001100011000110001100011000fffff000000000000000000000000000000fffffffffffffff00000
def v201 : List ℕ := [t1,t2,t134,t150,t4,t5,t6]
theorem b201 : Ban 220 7 v201 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v202 : List ℕ := [t1,t2,t134,t150,t3,t4,t5,t6]
theorem b202 : Ban 220 7 v202 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t151 : ℕ := 0xfffff
def v203 : List ℕ := [t151,t1,t2,t134,t3,t4,t5,t6]
theorem b203 : Ban 220 7 v203 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t152 : ℕ := 0x42faa42faa42faa42faa42faa42faa42faa42faa42faa42faa42faa00000fffff0000000000fffff00000fffff0000000000ffffffffff
def v204 : List ℕ := [t1,t2,t134,t3,t4,t152,t5,t6]
theorem b204 : Ban 220 7 v204 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t153 : ℕ := 0x2f0002f0002f0002f0002f0002f0002f0002f0002f0002f0002f0000000fffff0000000000fffff000000000000000000000000000000
def v205 : List ℕ := [t153,t1,t2,t134,t3,t4,t5,t6]
theorem b205 : Ban 220 7 v205 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t154 : ℕ := 0x400aa400aa400aa400aa400aa400aa400aa400aa400aa400aa400aa000000000000000000000000000000fffff0000000000fffff00000
def v206 : List ℕ := [t1,t2,t134,t3,t154,t4,t5,t6]
theorem b206 : Ban 220 7 v206 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t155 : ℕ := 0xfffff000000000000000000000000000000
def v207 : List ℕ := [t155,t1,t2,t134,t3,t4,t5,t6]
theorem b207 : Ban 220 7 v207 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t156 : ℕ := 0x9ef009ef009ef009ef009ef009ef009ef009ef009ef009ef009ef0000000fffff0000000000fffffffffffffff000000000000000fffff
def v208 : List ℕ := [t1,t2,t134,t3,t4,t5,t156,t6]
theorem b208 : Ban 220 7 v208 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t157 : ℕ := 0x2f0002f0002f0002f0002f0002f0002f0002f0002f0002f0002f0000000fffff0000000000000000000000000000000000000000fffff
def v209 : List ℕ := [t157,t1,t2,t134,t3,t4,t5,t6]
theorem b209 : Ban 220 7 v209 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t158 : ℕ := 0x9c0009c0009c0009c0009c0009c0009c0009c0009c0009c0009c0000000000000000000000000000ffffffffff00000000000000000000
def v210 : List ℕ := [t1,t2,t134,t3,t4,t158,t5,t6]
theorem b210 : Ban 220 7 v210 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t159 : ℕ := 0xfffff000000000000000000000000000000000000000000000
def v211 : List ℕ := [t159,t1,t2,t134,t3,t4,t5,t6]
theorem b211 : Ban 220 7 v211 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t160 : ℕ := 0xe2f00e2f00e2f00e2f00e2f00e2f00e2f00e2f00e2f00e2f00e2f00fffffffffffffffffffffffff0000000000000000000000000fffff
def v212 : List ℕ := [t1,t2,t134,t3,t4,t5,t6,t160]
theorem b212 : Ban 220 7 v212 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t161 : ℕ := 0x2f0002f0002f0002f0002f0002f0002f0002f0002f0002f0002f0000000000000000000000fffff0000000000000000000000000fffff
def v213 : List ℕ := [t161,t1,t2,t134,t3,t4,t5,t6]
theorem b213 : Ban 220 7 v213 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t162 : ℕ := 0xe0000e0000e0000e0000e0000e0000e0000e0000e0000e0000e0000fffff00000ffffffffff00000000000000000000000000000000000
def v214 : List ℕ := [t1,t2,t134,t3,t4,t5,t162,t6]
theorem b214 : Ban 220 7 v214 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t163 : ℕ := 0x20c0020c0020c0020c0020c0020c0020c0020c0020c0020c0020c000000000000000fffff00000fffff0000000000fffff0000000000
def v215 : List ℕ := [t163,t1,t2,t3,t4,t5,t6]
theorem b215 : Ban 220 7 v215 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v216 : List ℕ := [t163,t1,t134,t3,t4,t5,t6]
theorem b216 : Ban 220 7 v216 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v217 : List ℕ := [t163,t1,t2,t134,t3,t4,t5,t6]
theorem b217 : Ban 220 7 v217 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t164 : ℕ := 0xfffff000000000000000
def v218 : List ℕ := [t164,t1,t2,t134,t3,t4,t5,t6]
theorem b218 : Ban 220 7 v218 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t165 : ℕ := 0x1bcf01bcf01bcf01bcf01bcf01bcf01bcf01bcf01bcf01bcf01bcf0fffff00000fffff00000000000000000000fffffffffffffff00000
def v219 : List ℕ := [t1,t134,t3,t165,t4,t5,t6]
theorem b219 : Ban 220 7 v219 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v220 : List ℕ := [t1,t2,t134,t3,t165,t4,t5,t6]
theorem b220 : Ban 220 7 v220 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t166 : ℕ := 0x8cf008cf008cf008cf008cf008cf008cf008cf008cf008cf008cf00000000000fffff0000000000000000000000000000000000000000
def v221 : List ℕ := [t1,t166,t134,t3,t4,t5,t6]
theorem b221 : Ban 220 7 v221 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v222 : List ℕ := [t1,t166,t2,t134,t3,t4,t5,t6]
theorem b222 : Ban 220 7 v222 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t167 : ℕ := 0x1300013000130001300013000130001300013000130001300013000fffff00000000000000000000000000000000000ffffffffff00000
def v223 : List ℕ := [t1,t2,t134,t167,t3,t4,t5,t6]
theorem b223 : Ban 220 7 v223 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t168 : ℕ := 0xa0000a0000a0000a0000a0000a0000a0000a0000a0000a0000a00000000000000000000000000000000000000000000000000000000
def v224 : List ℕ := [t168,t1,t2,t134,t3,t4,t5,t6]
theorem b224 : Ban 220 7 v224 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t169 : ℕ := 0x48cfa48cfa48cfa48cfa48cfa48cfa48cfa48cfa48cfa48cfa48cfa0000000000fffff000000000000000ffffffffff00000ffffffffff
def v225 : List ℕ := [t1,t134,t3,t169,t5,t6]
def t170 : ℕ := 0x3c00f003c00f00fffc0000003fff
def t171 : ℕ := 0xb3eacfab3eacfa0000000fffffff
def v226 : List ℕ := [t170,t171,t138,t140]
theorem b225 : Ban 56 5 v226 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w8 : Wide 56 5 v226 := viaSub (ws := [v226]) (consBan b225 (nilBan 56 5)) (by decide) (by decide +kernel)
theorem b226 : Ban 220 7 v225 := viaCut p127_47 w8 (by decide) (by decide +kernel) (by decide +kernel)
def v227 : List ℕ := [t1,t2,t134,t3,t169,t5,t6]
theorem b227 : Ban 220 7 v227 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v228 : List ℕ := [t1,t134,t3,t4,t169,t5,t6]
theorem b228 : Ban 220 7 v228 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v229 : List ℕ := [t1,t2,t134,t3,t4,t169,t5,t6]
theorem b229 : Ban 220 7 v229 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t172 : ℕ := 0x8c5008c5008c5008c5008c5008c5008c5008c5008c5008c5008c500000000000fffff00000000000000000000fffff000000000000000
def v230 : List ℕ := [t1,t172,t134,t3,t4,t5,t6]
theorem b230 : Ban 220 7 v230 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v231 : List ℕ := [t1,t172,t2,t134,t3,t4,t5,t6]
theorem b231 : Ban 220 7 v231 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t173 : ℕ := 0x4000a4000a4000a4000a4000a4000a4000a4000a4000a4000a4000a000000000000000000000000000000fffff0000000000ffffffffff
def v232 : List ℕ := [t1,t2,t134,t3,t173,t5,t6]
theorem b232 : Ban 220 7 v232 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v233 : List ℕ := [t1,t2,t134,t3,t173,t4,t5,t6]
theorem b233 : Ban 220 7 v233 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t174 : ℕ := 0x8000080000800008000080000800008000080000800008000080000000000000000000000000000000000000000000000000000000000
def v234 : List ℕ := [t1,t174,t134,t3,t4,t5,t6]
theorem b234 : Ban 220 7 v234 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v235 : List ℕ := [t1,t174,t2,t134,t3,t4,t5,t6]
theorem b235 : Ban 220 7 v235 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t175 : ℕ := 0x9ccf09ccf09ccf09ccf09ccf09ccf09ccf09ccf09ccf09ccf09ccf00000000000fffff00000ffffffffffffffffffff000000000000000
def v236 : List ℕ := [t1,t2,t134,t3,t4,t175,t6]
theorem b236 : Ban 220 7 v236 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v237 : List ℕ := [t1,t2,t134,t3,t4,t5,t175,t6]
theorem b237 : Ban 220 7 v237 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t176 : ℕ := 0xcf000cf000cf000cf000cf000cf000cf000cf000cf000cf000cf00000000000fffff00000000000000000000fffff000000000000000
def v238 : List ℕ := [t176,t1,t2,t134,t3,t4,t5,t6]
theorem b238 : Ban 220 7 v238 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t177 : ℕ := 0x940009400094000940009400094000940009400094000940009400000000000000000000000fffffffffffffff00000000000000000000
def v239 : List ℕ := [t1,t134,t3,t4,t177,t6]
def v240 : List ℕ := [t143,t1,t134,t3,t4,t177,t6]
theorem b239 : Ban 220 6 v240 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v241 : List ℕ := [t1,t144,t3,t4,t177,t6]
theorem b240 : Ban 220 6 v241 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v242 : List ℕ := [t134,t144,t3,t4,t177,t6]
theorem b241 : Ban 220 6 v242 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v243 : List ℕ := [t1,t134,t144,t3,t4,t177,t6]
theorem b242 : Ban 220 6 v243 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v244 : List ℕ := [t145,t134,t3,t4,t177,t6]
theorem b243 : Ban 220 6 v244 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v245 : List ℕ := [t145,t1,t134,t3,t4,t177,t6]
theorem b244 : Ban 220 6 v245 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v246 : List ℕ := [t1,t146,t3,t4,t177,t6]
theorem b245 : Ban 220 6 v246 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v247 : List ℕ := [t1,t146,t134,t3,t4,t177,t6]
theorem b246 : Ban 220 6 v247 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v248 : List ℕ := [t147,t1,t134,t3,t4,t177,t6]
theorem b247 : Ban 220 6 v248 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v249 : List ℕ := [t1,t134,t148,t4,t177,t6]
theorem b248 : Ban 220 6 v249 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v250 : List ℕ := [t134,t3,t148,t4,t177,t6]
theorem b249 : Ban 220 6 v250 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v251 : List ℕ := [t1,t134,t3,t148,t4,t177,t6]
theorem b250 : Ban 220 6 v251 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v252 : List ℕ := [t149,t134,t3,t4,t177,t6]
theorem b251 : Ban 220 6 v252 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v253 : List ℕ := [t149,t1,t134,t3,t4,t177,t6]
theorem b252 : Ban 220 6 v253 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v254 : List ℕ := [t1,t134,t150,t4,t177,t6]
theorem b253 : Ban 220 6 v254 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v255 : List ℕ := [t1,t134,t150,t3,t4,t177,t6]
theorem b254 : Ban 220 6 v255 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v256 : List ℕ := [t151,t1,t134,t3,t4,t177,t6]
theorem b255 : Ban 220 6 v256 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v257 : List ℕ := [t1,t134,t3,t4,t152,t177,t6]
theorem b256 : Ban 220 6 v257 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v258 : List ℕ := [t153,t1,t134,t3,t4,t177,t6]
theorem b257 : Ban 220 6 v258 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v259 : List ℕ := [t1,t134,t3,t154,t4,t177,t6]
theorem b258 : Ban 220 6 v259 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v260 : List ℕ := [t155,t1,t134,t3,t4,t177,t6]
theorem b259 : Ban 220 6 v260 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t178 : ℕ := 0x96f0096f0096f0096f0096f0096f0096f0096f0096f0096f0096f0000000fffff0000000000fffffffffffffff000000000000000fffff
def v261 : List ℕ := [t1,t134,t3,t4,t177,t178,t6]
theorem b260 : Ban 220 6 v261 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v262 : List ℕ := [t157,t1,t134,t3,t4,t177,t6]
theorem b261 : Ban 220 6 v262 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t179 : ℕ := 0x94000940009400094000940009400094000940009400094000940000000000000000000000000000ffffffffff00000000000000000000
def v263 : List ℕ := [t1,t134,t3,t4,t179,t177,t6]
theorem b262 : Ban 220 6 v263 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v264 : List ℕ := [t159,t1,t134,t3,t4,t177,t6]
theorem b263 : Ban 220 6 v264 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v265 : List ℕ := [t1,t134,t3,t4,t177,t6,t160]
theorem b264 : Ban 220 6 v265 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v266 : List ℕ := [t161,t1,t134,t3,t4,t177,t6]
theorem b265 : Ban 220 6 v266 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v267 : List ℕ := [t1,t134,t3,t4,t177,t162,t6]
theorem b266 : Ban 220 6 v267 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t180 : ℕ := 0xffffffffff0000000000
def v268 : List ℕ := [t180,t1,t134,t3,t4,t177,t6]
def t181 : ℕ := 0x7f
def v269 : List ℕ := [t181,t8,t9,t10,t11]
theorem b267 : Ban 28 4 v269 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w9 : Wide 28 4 v269 := viaSub (ws := [v2,v269]) (consBan b0 (consBan b267 (nilBan 28 4))) (by decide) (by decide +kernel)
theorem b268 : Ban 220 6 v268 := viaCut p127_114 w9 (by decide) (by decide +kernel) (by decide +kernel)
def t182 : ℕ := 0x1befc1befc1befc1befc1befc1befc1befc1befc1befc1befc1befcfffff00000ffffffffff00000fffff00000fffffffffffffff00000
def v270 : List ℕ := [t1,t134,t3,t182,t4,t177,t6]
theorem b269 : Ban 12 2 v106 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w10 : Wide 12 2 v106 := viaSub (ws := [v106]) (consBan b269 (nilBan 12 2)) (by decide) (by decide +kernel)
theorem b270 : Ban 220 6 v270 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def t183 : ℕ := 0x8efc08efc08efc08efc08efc08efc08efc08efc08efc08efc08efc0000000000ffffffffff00000fffff0000000000000000000000000
def v271 : List ℕ := [t1,t183,t134,t3,t4,t177,t6]
def t184 : ℕ := 0x40810201fff80
def v272 : List ℕ := [t184,t8,t9,t10,t11]
theorem b271 : Ban 28 4 v272 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w11 : Wide 28 4 v272 := viaSub (ws := [v2,v272]) (consBan b0 (consBan b271 (nilBan 28 4))) (by decide) (by decide +kernel)
theorem b272 : Ban 220 6 v271 := viaCut p127_114 w11 (by decide) (by decide +kernel) (by decide +kernel)
def t185 : ℕ := 0x1300013000130001300013000130001300013000130001300013000fffff0000000000000000000000000000000000000000fffff00000
def v273 : List ℕ := [t1,t134,t185,t3,t4,t177,t6]
def t186 : ℕ := 0x2850a14fe00000
def v274 : List ℕ := [t8,t186,t9,t10,t11]
theorem b273 : Ban 28 4 v274 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w12 : Wide 28 4 v274 := viaSub (ws := [v2,v274]) (consBan b0 (consBan b273 (nilBan 28 4))) (by decide) (by decide +kernel)
theorem b274 : Ban 220 6 v273 := viaCut p127_114 w12 (by decide) (by decide +kernel) (by decide +kernel)
def t187 : ℕ := 0xa8000a8000a8000a8000a8000a8000a8000a8000a8000a8000a80000000000000000000000000000000000000000000000000000000
def v275 : List ℕ := [t187,t1,t134,t3,t4,t177,t6]
theorem b275 : Ban 220 6 v275 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t188 : ℕ := 0x48efe48efe48efe48efe48efe48efe48efe48efe48efe48efe48efe0000000000ffffffffff00000ffffffffffffffffffffffffffffff
def v276 : List ℕ := [t1,t134,t3,t188,t177,t6]
theorem b276 : Ban 220 6 v276 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v277 : List ℕ := [t1,t3,t4,t188,t177,t6]
theorem b277 : Ban 220 6 v277 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v278 : List ℕ := [t1,t134,t3,t4,t188,t177,t6]
theorem b278 : Ban 220 6 v278 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t189 : ℕ := 0x8e5408e5408e5408e5408e5408e5408e5408e5408e5408e5408e540000000000ffffffffff00000fffff00000ffffffffff0000000000
def v279 : List ℕ := [t1,t189,t3,t4,t177,t6]
theorem b279 : Ban 220 6 v279 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v280 : List ℕ := [t1,t189,t134,t3,t4,t177,t6]
theorem b280 : Ban 220 6 v280 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t190 : ℕ := 0x4000240002400024000240002400024000240002400024000240002000000000000000000000000000000fffff0000000000ffffffffff
def v281 : List ℕ := [t1,t134,t3,t190,t177,t6]
theorem b281 : Ban 220 6 v281 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v282 : List ℕ := [t1,t134,t3,t190,t4,t177,t6]
theorem b282 : Ban 220 6 v282 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t191 : ℕ := 0xfffff0000000000000000000000000
def v283 : List ℕ := [t191,t1,t134,t3,t4,t177,t6]
def t192 : ℕ := 0x3f80
def v284 : List ℕ := [t192,t8,t9,t11]
theorem b283 : Ban 28 4 v284 := viaSmall (by decide +kernel) (by decide)
def v285 : List ℕ := [t192,t8,t9,t10,t11]
theorem b284 : Ban 28 4 v285 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w13 : Wide 28 4 v285 := viaSub (ws := [v284,v2,v285]) (consBan b283 (consBan b0 (consBan b284 (nilBan 28 4)))) (by decide) (by decide +kernel)
theorem b285 : Ban 220 6 v283 := viaCut p127_114 w13 (by decide) (by decide +kernel) (by decide +kernel)
def t193 : ℕ := 0x9cefc9cefc9cefc9cefc9cefc9cefc9cefc9cefc9cefc9cefc9cefc0000000000fffffffffffffffffffffffffffffffffff0000000000
def v286 : List ℕ := [t1,t134,t3,t4,t177,t193,t6]
def t194 : ℕ := 0xb56ad5a01fffff
def v287 : List ℕ := [t8,t9,t10,t194,t11]
theorem b286 : Ban 28 4 v287 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w14 : Wide 28 4 v287 := viaSub (ws := [v2,v287]) (consBan b0 (consBan b286 (nilBan 28 4))) (by decide) (by decide +kernel)
theorem b287 : Ban 220 6 v286 := viaCut p127_114 w14 (by decide) (by decide +kernel) (by decide +kernel)
def t195 : ℕ := 0x8efc08efc08efc08efc08efc08efc08efc08efc08efc08efc08efc0000000000ffffffffff000000000000000ffffffffff0000000000
def v288 : List ℕ := [t1,t195,t134,t3,t4,t177,t6]
def t196 : ℕ := 0x40810201fc07f
def v289 : List ℕ := [t196,t8,t9,t11]
theorem b288 : Ban 28 4 v289 := viaSmall (by decide +kernel) (by decide)
def v290 : List ℕ := [t196,t8,t9,t10,t11]
theorem b289 : Ban 28 4 v290 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w15 : Wide 28 4 v290 := viaSub (ws := [v289,v2,v290]) (consBan b288 (consBan b0 (consBan b289 (nilBan 28 4)))) (by decide) (by decide +kernel)
theorem b290 : Ban 220 6 v288 := viaCut p127_114 w15 (by decide) (by decide +kernel) (by decide +kernel)
def t197 : ℕ := 0x940009400094000940009400094000940009400094000940009400000000000000000000000fffff00000fffff00000000000000000000
def v291 : List ℕ := [t1,t134,t3,t4,t197,t177,t6]
def t198 : ℕ := 0xb162c580000000
def v292 : List ℕ := [t8,t9,t198,t10,t11]
theorem b291 : Ban 28 4 v292 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w16 : Wide 28 4 v292 := viaSub (ws := [v2,v292]) (consBan b0 (consBan b291 (nilBan 28 4))) (by decide) (by decide +kernel)
theorem b292 : Ban 220 6 v291 := viaCut p127_114 w16 (by decide) (by decide +kernel) (by decide +kernel)
def t199 : ℕ := 0xffffffffff00000000000000000000000000000000000
def v293 : List ℕ := [t199,t1,t134,t3,t4,t177,t6]
def t200 : ℕ := 0x1fc000
def v294 : List ℕ := [t200,t8,t9,t10,t11]
theorem b293 : Ban 28 4 v294 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w17 : Wide 28 4 v294 := viaSub (ws := [v2,v294]) (consBan b0 (consBan b293 (nilBan 28 4))) (by decide) (by decide +kernel)
theorem b294 : Ban 220 6 v293 := viaCut p127_114 w17 (by decide) (by decide +kernel) (by decide +kernel)
def t201 : ℕ := 0xe8efce8efce8efce8efce8efce8efce8efce8efce8efce8efce8efcffffffffffffffffffff00000fffff00000ffffffffff0000000000
def v295 : List ℕ := [t1,t134,t3,t4,t177,t6,t201]
theorem b295 : Ban 220 6 v295 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def t202 : ℕ := 0x8efc08efc08efc08efc08efc08efc08efc08efc08efc08efc08efc0000000000000000000000000fffff00000ffffffffff0000000000
def v296 : List ℕ := [t1,t202,t134,t3,t4,t177,t6]
def t203 : ℕ := 0x4081020003fff
def v297 : List ℕ := [t203,t8,t9,t10,t11]
theorem b296 : Ban 28 4 v297 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w18 : Wide 28 4 v297 := viaSub (ws := [v2,v297]) (consBan b0 (consBan b296 (nilBan 28 4))) (by decide) (by decide +kernel)
theorem b297 : Ban 220 6 v296 := viaCut p127_114 w18 (by decide) (by decide +kernel) (by decide +kernel)
def t204 : ℕ := 0xe0000e0000e0000e0000e0000e0000e0000e0000e0000e0000e0000ffffffffff000000000000000000000000000000000000000000000
def v298 : List ℕ := [t1,t134,t3,t4,t177,t204,t6]
def t205 : ℕ := 0xc183060fe00000
def v299 : List ℕ := [t8,t9,t10,t205,t11]
theorem b298 : Ban 28 4 v299 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w19 : Wide 28 4 v299 := viaSub (ws := [v2,v299]) (consBan b0 (consBan b298 (nilBan 28 4))) (by decide) (by decide +kernel)
theorem b299 : Ban 220 6 v298 := viaCut p127_114 w19 (by decide) (by decide +kernel) (by decide +kernel)
def t206 : ℕ := 0xfffff00000
def v300 : List ℕ := [t206,t1,t134,t3,t4,t177,t6]
theorem b300 : Ban 220 6 v300 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t207 : ℕ := 0x530aa530aa530aa530aa530aa530aa530aa530aa530aa530aa530aafffff0000000000000000000000000fffffffffffffffffffffffff
def v301 : List ℕ := [t1,t134,t3,t4,t207,t177,t6]
theorem b301 : Ban 220 6 v301 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t208 : ℕ := 0x1300013000130001300013000130001300013000130001300013000fffff000000000000000000000000000000ffffffffff0000000000
def v302 : List ℕ := [t1,t134,t208,t3,t4,t177,t6]
theorem b302 : Ban 220 6 v302 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t209 : ℕ := 0x400aa400aa400aa400aa400aa400aa400aa400aa400aa400aa400aa000000000000000000000000000000fffff000000000000000fffff
def v303 : List ℕ := [t1,t134,t3,t209,t4,t177,t6]
theorem b303 : Ban 220 6 v303 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t210 : ℕ := 0x10000100001000010000100001000010000100001000010000100000000000000000000000000000000000000000000000000000000000
def v304 : List ℕ := [t1,t134,t210,t3,t4,t177,t6]
def t211 : ℕ := 0x20408100000000
def v305 : List ℕ := [t8,t211,t9,t10,t11]
theorem b304 : Ban 28 4 v305 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w20 : Wide 28 4 v305 := viaSub (ws := [v2,v305]) (consBan b0 (consBan b304 (nilBan 28 4))) (by decide) (by decide +kernel)
theorem b305 : Ban 220 6 v304 := viaCut p127_114 w20 (by decide) (by decide +kernel) (by decide +kernel)
def t212 : ℕ := 0x9700097000970009700097000970009700097000970009700097000fffff000000000000000ffffffffffffffffffffffffffffff00000
def v306 : List ℕ := [t1,t134,t3,t4,t212,t6]
theorem b306 : Ban 220 6 v306 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v307 : List ℕ := [t1,t134,t4,t177,t212,t6]
def t213 : ℕ := 0xb972e5cfe03fff
def v308 : List ℕ := [t8,t10,t213,t11]
theorem b307 : Ban 28 4 v308 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w21 : Wide 28 4 v308 := viaSub (ws := [v308]) (consBan b307 (nilBan 28 4)) (by decide) (by decide +kernel)
theorem b308 : Ban 220 6 v307 := viaCut p127_114 w21 (by decide) (by decide +kernel) (by decide +kernel)
def v309 : List ℕ := [t1,t134,t3,t4,t177,t212,t6]
theorem b309 : Ban 220 6 v309 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def t214 : ℕ := 0x300003000030000300003000030000300003000030000300003000fffff000000000000000000000000000000fffffffffffffff00000
def v310 : List ℕ := [t1,t214,t134,t4,t177,t6]
def t215 : ℕ := 0x810204fe0007f
def v311 : List ℕ := [t8,t215,t10,t11]
theorem b310 : Ban 28 4 v311 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w22 : Wide 28 4 v311 := viaSub (ws := [v311]) (consBan b310 (nilBan 28 4)) (by decide) (by decide +kernel)
theorem b311 : Ban 220 6 v310 := viaCut p127_114 w22 (by decide) (by decide +kernel) (by decide +kernel)
def v312 : List ℕ := [t1,t214,t134,t3,t4,t177,t6]
def v313 : List ℕ := [t8,t215,t9,t10,t11]
theorem b312 : Ban 28 4 v313 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w23 : Wide 28 4 v313 := viaSub (ws := [v311,v2,v313]) (consBan b310 (consBan b0 (consBan b312 (nilBan 28 4)))) (by decide) (by decide +kernel)
theorem b313 : Ban 220 6 v312 := viaCut p127_114 w23 (by decide) (by decide +kernel) (by decide +kernel)
def t216 : ℕ := 0x840008400084000840008400084000840008400084000840008400000000000000000000000fffffffffffffff00000000000000000000
def v314 : List ℕ := [t1,t134,t3,t4,t216,t6]
def t217 : ℕ := 0x91224480003f80
def v315 : List ℕ := [t8,t9,t217,t11]
theorem b314 : Ban 28 4 v315 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w24 : Wide 28 4 v315 := viaSub (ws := [v315]) (consBan b314 (nilBan 28 4)) (by decide) (by decide +kernel)
theorem b315 : Ban 220 6 v314 := viaCut p127_114 w24 (by decide) (by decide +kernel) (by decide +kernel)
def v316 : List ℕ := [t1,t134,t3,t4,t216,t177,t6]
def v317 : List ℕ := [t8,t9,t217,t10,t11]
theorem b316 : Ban 28 4 v317 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w25 : Wide 28 4 v317 := viaSub (ws := [v315,v2,v317]) (consBan b314 (consBan b0 (consBan b316 (nilBan 28 4)))) (by decide) (by decide +kernel)
theorem b317 : Ban 220 6 v316 := viaCut p127_114 w25 (by decide) (by decide +kernel) (by decide +kernel)
def t218 : ℕ := 0xfffff00000000000000000000000000000000000000000000000000
def v318 : List ℕ := [t218,t1,t134,t3,t4,t177,t6]
theorem b318 : Ban 220 6 v318 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def t219 : ℕ := 0xf3000f3000f3000f3000f3000f3000f3000f3000f3000f3000f3000ffffffffffffffffffff000000000000000fffffffffffffff00000
def v319 : List ℕ := [t1,t134,t3,t4,t177,t6,t219]
theorem b319 : Ban 220 6 v319 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def t220 : ℕ := 0x130001300013000130001300013000130001300013000130001300000000000000000000000000000000000000fffffffffffffff00000
def v320 : List ℕ := [t1,t134,t220,t3,t4,t177,t6]
def t221 : ℕ := 0x2850a14000007f
def v321 : List ℕ := [t8,t221,t9,t10,t11]
theorem b320 : Ban 28 4 v321 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w26 : Wide 28 4 v321 := viaSub (ws := [v2,v321]) (consBan b0 (consBan b320 (nilBan 28 4))) (by decide) (by decide +kernel)
theorem b321 : Ban 220 6 v320 := viaCut p127_114 w26 (by decide) (by decide +kernel) (by decide +kernel)
def t222 : ℕ := 0xe0000e0000e0000e0000e0000e0000e0000e0000e0000e0000e000000000fffffffffffffff00000000000000000000000000000000000
def v322 : List ℕ := [t1,t134,t3,t4,t177,t222,t6]
def t223 : ℕ := 0xc18306001fc000
def v323 : List ℕ := [t8,t9,t10,t223,t11]
theorem b322 : Ban 28 4 v323 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w27 : Wide 28 4 v323 := viaSub (ws := [v2,v323]) (consBan b0 (consBan b322 (nilBan 28 4))) (by decide) (by decide +kernel)
theorem b323 : Ban 220 6 v322 := viaCut p127_114 w27 (by decide) (by decide +kernel) (by decide +kernel)
def t224 : ℕ := 0xfffff00000000000000000000
def v324 : List ℕ := [t224,t1,t134,t3,t4,t177,t6]
theorem b324 : Ban 220 6 v324 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t225 : ℕ := 0xd40aad40aad40aad40aad40aad40aad40aad40aad40aad40aad40aa00000000000000000000fffffffffffffff0000000000ffffffffff
def v325 : List ℕ := [t1,t134,t3,t4,t177,t225,t6]
theorem b325 : Ban 220 6 v325 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t226 : ℕ := 0x400aa400aa400aa400aa400aa400aa400aa400aa400aa400aa400aa000000000000000000000000000000000000000000000ffffffffff
def v326 : List ℕ := [t1,t134,t3,t226,t4,t177,t6]
theorem b326 : Ban 220 6 v326 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t227 : ℕ := 0x940009400094000940009400094000940009400094000940009400000000000000000000000ffffffffff0000000000000000000000000
def v327 : List ℕ := [t1,t134,t3,t4,t227,t177,t6]
theorem b327 : Ban 220 6 v327 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t228 : ℕ := 0x40000400004000040000400004000040000400004000040000400000000000000000000000000000000000000000000000000000000000
def v328 : List ℕ := [t1,t134,t3,t228,t4,t177,t6]
theorem b328 : Ban 220 6 v328 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t229 : ℕ := 0xe00aae00aae00aae00aae00aae00aae00aae00aae00aae00aae00aaffffffffffffffffffff0000000000fffff0000000000ffffffffff
def v329 : List ℕ := [t1,t134,t3,t4,t177,t229]
theorem b329 : Ban 220 6 v329 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v330 : List ℕ := [t1,t134,t3,t177,t6,t229]
theorem b330 : Ban 220 6 v330 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v331 : List ℕ := [t1,t134,t3,t4,t177,t6,t229]
theorem b331 : Ban 220 6 v331 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t230 : ℕ := 0xaa000aa000aa000aa000aa000aa000aa000aa000aa000aa000aa000000000000000000000000000000fffff0000000000ffffffffff
def v332 : List ℕ := [t230,t1,t134,t3,t177,t6]
theorem b332 : Ban 220 6 v332 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v333 : List ℕ := [t230,t1,t134,t3,t4,t177,t6]
theorem b333 : Ban 220 6 v333 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t231 : ℕ := 0xa0000a0000a0000a0000a0000a0000a0000a0000a0000a0000a0000ffffffffffffffffffff00000000000000000000000000000000000
def v334 : List ℕ := [t1,t134,t3,t4,t177,t231]
theorem b334 : Ban 220 6 v334 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v335 : List ℕ := [t1,t134,t3,t4,t177,t231,t6]
theorem b335 : Ban 220 6 v335 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t232 : ℕ := 0x80000800008000080000800008000080000800008000080000800000000000000000000000000000000000000000000000000000000000
def v336 : List ℕ := [t1,t134,t3,t4,t232,t177,t6]
def t233 : ℕ := 0x81020400000000
def v337 : List ℕ := [t8,t9,t233,t10,t11]
theorem b336 : Ban 28 4 v337 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w28 : Wide 28 4 v337 := viaSub (ws := [v2,v337]) (consBan b0 (consBan b336 (nilBan 28 4))) (by decide) (by decide +kernel)
theorem b337 : Ban 220 6 v336 := viaCut p127_114 w28 (by decide) (by decide +kernel) (by decide +kernel)
def t234 : ℕ := 0xf4000f4000f4000f4000f4000f4000f4000f4000f4000f4000f4000fffffffffffffffffffffffffffffffffff00000000000000000000
def v338 : List ℕ := [t1,t134,t3,t4,t177,t234]
def t235 : ℕ := 0xf1e3c78fffff80
def v339 : List ℕ := [t8,t9,t10,t235]
theorem b338 : Ban 28 4 v339 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w29 : Wide 28 4 v339 := viaSub (ws := [v339]) (consBan b338 (nilBan 28 4)) (by decide) (by decide +kernel)
theorem b339 : Ban 220 6 v338 := viaCut p127_114 w29 (by decide) (by decide +kernel) (by decide +kernel)
def v340 : List ℕ := [t1,t134,t3,t4,t6,t234]
theorem b340 : Ban 220 6 v340 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v341 : List ℕ := [t1,t134,t3,t4,t177,t6,t234]
theorem b341 : Ban 220 6 v341 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def t236 : ℕ := 0x140001400014000140001400014000140001400014000140001400000000000000000000000fffffffffffffff00000000000000000000
def v342 : List ℕ := [t1,t134,t3,t236,t4,t6]
def t237 : ℕ := 0x3060c180003f80
def v343 : List ℕ := [t8,t9,t237,t11]
theorem b342 : Ban 28 4 v343 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w30 : Wide 28 4 v343 := viaSub (ws := [v343]) (consBan b342 (nilBan 28 4)) (by decide) (by decide +kernel)
theorem b343 : Ban 220 6 v342 := viaCut p127_114 w30 (by decide) (by decide +kernel) (by decide +kernel)
def v344 : List ℕ := [t1,t134,t3,t236,t4,t177,t6]
def v345 : List ℕ := [t8,t9,t237,t10,t11]
theorem b344 : Ban 28 4 v345 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w31 : Wide 28 4 v345 := viaSub (ws := [v343,v2,v345]) (consBan b342 (consBan b0 (consBan b344 (nilBan 28 4)))) (by decide) (by decide +kernel)
theorem b345 : Ban 220 6 v344 := viaCut p127_114 w31 (by decide) (by decide +kernel) (by decide +kernel)
def t238 : ℕ := 0x6000060000600006000060000600006000060000600006000060000ffffffffffffffffffff00000000000000000000000000000000000
def v346 : List ℕ := [t1,t134,t3,t4,t238,t177]
def t239 : ℕ := 0x4081020fffc000
def v347 : List ℕ := [t8,t9,t239,t10]
theorem b346 : Ban 28 4 v347 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w32 : Wide 28 4 v347 := viaSub (ws := [v347]) (consBan b346 (nilBan 28 4)) (by decide) (by decide +kernel)
theorem b347 : Ban 220 6 v346 := viaCut p127_114 w32 (by decide) (by decide +kernel) (by decide +kernel)
def v348 : List ℕ := [t1,t134,t3,t4,t238,t177,t6]
def v349 : List ℕ := [t8,t9,t239,t10,t11]
theorem b348 : Ban 28 4 v349 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w33 : Wide 28 4 v349 := viaSub (ws := [v347,v2,v349]) (consBan b346 (consBan b0 (consBan b348 (nilBan 28 4)))) (by decide) (by decide +kernel)
theorem b349 : Ban 220 6 v348 := viaCut p127_114 w33 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b350 : Ban 220 7 v239 := viaBranch (ws := [v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v270,v271,v273,v275,v276,v277,v278,v279,v280,v281,v282,v283,v286,v288,v291,v293,v295,v296,v298,v300,v301,v302,v303,v304,v306,v307,v309,v310,v312,v314,v316,v318,v319,v320,v322,v324,v325,v326,v327,v328,v329,v330,v331,v332,v333,v334,v335,v336,v338,v340,v341,v342,v344,v346,v348]) (consBan b239 (consBan b240 (consBan b241 (consBan b242 (consBan b243 (consBan b244 (consBan b245 (consBan b246 (consBan b247 (consBan b248 (consBan b249 (consBan b250 (consBan b251 (consBan b252 (consBan b253 (consBan b254 (consBan b255 (consBan b256 (consBan b257 (consBan b258 (consBan b259 (consBan b260 (consBan b261 (consBan b262 (consBan b263 (consBan b264 (consBan b265 (consBan b266 (consBan b268 (consBan b270 (consBan b272 (consBan b274 (consBan b275 (consBan b276 (consBan b277 (consBan b278 (consBan b279 (consBan b280 (consBan b281 (consBan b282 (consBan b285 (consBan b287 (consBan b290 (consBan b292 (consBan b294 (consBan b295 (consBan b297 (consBan b299 (consBan b300 (consBan b301 (consBan b302 (consBan b303 (consBan b305 (consBan b306 (consBan b308 (consBan b309 (consBan b311 (consBan b313 (consBan b315 (consBan b317 (consBan b318 (consBan b319 (consBan b321 (consBan b323 (consBan b324 (consBan b325 (consBan b326 (consBan b327 (consBan b328 (consBan b329 (consBan b330 (consBan b331 (consBan b332 (consBan b333 (consBan b334 (consBan b335 (consBan b337 (consBan b339 (consBan b340 (consBan b341 (consBan b343 (consBan b345 (consBan b347 (consBan b349 (nilBan 220 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
def v350 : List ℕ := [t1,t2,t134,t3,t4,t177,t6]
theorem b351 : Ban 220 7 v350 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v351 : List ℕ := [t1,t134,t3,t4,t177,t5,t6]
theorem b352 : Ban 12 3 v106 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w34 : Wide 12 3 v106 := viaSub (ws := [v106]) (consBan b352 (nilBan 12 3)) (by decide) (by decide +kernel)
def p127_82 : Projection 220 12 := pick [40,42,52,57,140,142,152,157,200,202,212,217] rfl (by decide +kernel) (by decide)
theorem b353 : Ban 220 7 v351 := viaCut p127_82 w34 (by decide) (by decide +kernel) (by decide +kernel)
def v352 : List ℕ := [t1,t2,t134,t3,t4,t177,t5,t6]
theorem b354 : Ban 220 7 v352 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t240 : ℕ := 0xfffff0000000000000000000000000000000000000000
def v353 : List ℕ := [t240,t1,t2,t134,t3,t4,t5,t6]
theorem b355 : Ban 220 7 v353 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t241 : ℕ := 0xe8cf0e8cf0e8cf0e8cf0e8cf0e8cf0e8cf0e8cf0e8cf0e8cf0e8cf0ffffffffffffffffffff000000000000000fffff000000000000000
def v354 : List ℕ := [t1,t134,t3,t4,t5,t6,t241]
theorem b356 : Ban 220 7 v354 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v355 : List ℕ := [t1,t2,t134,t3,t4,t5,t6,t241]
theorem b357 : Ban 220 7 v355 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t242 : ℕ := 0x8cf008cf008cf008cf008cf008cf008cf008cf008cf008cf008cf000000000000000000000000000000000000fffff000000000000000
def v356 : List ℕ := [t1,t242,t134,t3,t4,t5,t6]
theorem b358 : Ban 220 7 v356 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v357 : List ℕ := [t1,t242,t2,t134,t3,t4,t5,t6]
theorem b359 : Ban 220 7 v357 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t243 : ℕ := 0xe0000e0000e0000e0000e0000e0000e0000e0000e0000e0000e0000ffffffffff00000fffff00000000000000000000000000000000000
def v358 : List ℕ := [t1,t2,t134,t3,t4,t5,t243,t6]
theorem b360 : Ban 220 7 v358 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v359 : List ℕ := [t180,t1,t2,t134,t3,t4,t5,t6]
theorem b361 : Ban 220 7 v359 := viaCut p127_114 w9 (by decide) (by decide +kernel) (by decide +kernel)
def v360 : List ℕ := [t1,t2,t134,t3,t182,t4,t5,t6]
theorem b362 : Ban 220 7 v360 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v361 : List ℕ := [t1,t2,t183,t134,t3,t4,t5,t6]
theorem b363 : Ban 220 7 v361 := viaCut p127_114 w11 (by decide) (by decide +kernel) (by decide +kernel)
def v362 : List ℕ := [t1,t2,t134,t185,t3,t4,t5,t6]
theorem b364 : Ban 220 7 v362 := viaCut p127_114 w12 (by decide) (by decide +kernel) (by decide +kernel)
def v363 : List ℕ := [t187,t1,t2,t134,t3,t4,t5,t6]
theorem b365 : Ban 220 7 v363 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v364 : List ℕ := [t1,t2,t134,t3,t188,t5,t6]
theorem b366 : Ban 220 7 v364 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v365 : List ℕ := [t1,t2,t3,t4,t188,t5,t6]
theorem b367 : Ban 220 7 v365 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v366 : List ℕ := [t1,t2,t134,t3,t4,t188,t5,t6]
theorem b368 : Ban 220 7 v366 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v367 : List ℕ := [t1,t2,t189,t3,t4,t5,t6]
theorem b369 : Ban 220 7 v367 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v368 : List ℕ := [t1,t2,t189,t134,t3,t4,t5,t6]
theorem b370 : Ban 220 7 v368 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v369 : List ℕ := [t1,t2,t134,t3,t190,t5,t6]
theorem b371 : Ban 220 7 v369 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v370 : List ℕ := [t1,t2,t134,t3,t190,t4,t5,t6]
theorem b372 : Ban 220 7 v370 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t244 : ℕ := 0x8000080000800008000080000800008000080000800008000080000000000000000000000000000fffff0000000000000000000000000
def v371 : List ℕ := [t1,t244,t2,t134,t3,t4,t5,t6]
theorem b373 : Ban 220 7 v371 := viaCut p127_114 w13 (by decide) (by decide +kernel) (by decide +kernel)
def v372 : List ℕ := [t1,t2,t134,t3,t4,t5,t193,t6]
theorem b374 : Ban 220 7 v372 := viaCut p127_114 w14 (by decide) (by decide +kernel) (by decide +kernel)
def t245 : ℕ := 0xefc00efc00efc00efc00efc00efc00efc00efc00efc00efc00efc0000000000ffffffffff000000000000000ffffffffff0000000000
def v373 : List ℕ := [t245,t1,t2,t134,t3,t4,t5,t6]
theorem b375 : Ban 220 7 v373 := viaCut p127_114 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v374 : List ℕ := [t1,t2,t134,t3,t4,t197,t5,t6]
theorem b376 : Ban 220 7 v374 := viaCut p127_114 w16 (by decide) (by decide +kernel) (by decide +kernel)
def v375 : List ℕ := [t199,t1,t2,t134,t3,t4,t5,t6]
theorem b377 : Ban 220 7 v375 := viaCut p127_114 w17 (by decide) (by decide +kernel) (by decide +kernel)
def v376 : List ℕ := [t1,t2,t134,t3,t4,t5,t6,t201]
theorem b378 : Ban 220 7 v376 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v377 : List ℕ := [t1,t2,t202,t134,t3,t4,t5,t6]
theorem b379 : Ban 220 7 v377 := viaCut p127_114 w18 (by decide) (by decide +kernel) (by decide +kernel)
def v378 : List ℕ := [t1,t2,t134,t3,t4,t5,t204,t6]
theorem b380 : Ban 220 7 v378 := viaCut p127_114 w19 (by decide) (by decide +kernel) (by decide +kernel)
def v379 : List ℕ := [t206,t1,t2,t134,t3,t4,t5,t6]
theorem b381 : Ban 220 7 v379 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v380 : List ℕ := [t1,t2,t134,t3,t4,t207,t5,t6]
theorem b382 : Ban 220 7 v380 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v381 : List ℕ := [t1,t2,t134,t208,t3,t4,t5,t6]
theorem b383 : Ban 220 7 v381 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v382 : List ℕ := [t1,t2,t134,t3,t209,t4,t5,t6]
theorem b384 : Ban 220 7 v382 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v383 : List ℕ := [t1,t2,t134,t210,t3,t4,t5,t6]
theorem b385 : Ban 220 7 v383 := viaCut p127_114 w20 (by decide) (by decide +kernel) (by decide +kernel)
def t246 : ℕ := 0x9f0009f0009f0009f0009f0009f0009f0009f0009f0009f0009f000fffff000000000000000ffffffffffffffffffffffffffffff00000
def v384 : List ℕ := [t1,t2,t134,t3,t4,t246,t6]
theorem b386 : Ban 220 7 v384 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v385 : List ℕ := [t1,t2,t134,t4,t5,t246,t6]
theorem b387 : Ban 220 7 v385 := viaCut p127_114 w21 (by decide) (by decide +kernel) (by decide +kernel)
def v386 : List ℕ := [t1,t2,t134,t3,t4,t5,t246,t6]
theorem b388 : Ban 220 7 v386 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v387 : List ℕ := [t1,t214,t2,t134,t4,t5,t6]
theorem b389 : Ban 220 7 v387 := viaCut p127_114 w22 (by decide) (by decide +kernel) (by decide +kernel)
def v388 : List ℕ := [t1,t214,t2,t134,t3,t4,t5,t6]
theorem b390 : Ban 220 7 v388 := viaCut p127_114 w23 (by decide) (by decide +kernel) (by decide +kernel)
def t247 : ℕ := 0x8c0008c0008c0008c0008c0008c0008c0008c0008c0008c0008c00000000000000000000000fffffffffffffff00000000000000000000
def v389 : List ℕ := [t1,t2,t134,t3,t4,t247,t6]
theorem b391 : Ban 220 7 v389 := viaCut p127_114 w24 (by decide) (by decide +kernel) (by decide +kernel)
def v390 : List ℕ := [t1,t2,t134,t3,t4,t247,t5,t6]
theorem b392 : Ban 220 7 v390 := viaCut p127_114 w25 (by decide) (by decide +kernel) (by decide +kernel)
def v391 : List ℕ := [t218,t1,t2,t134,t3,t4,t5,t6]
theorem b393 : Ban 220 7 v391 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v392 : List ℕ := [t1,t2,t134,t3,t4,t5,t6,t219]
theorem b394 : Ban 220 7 v392 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v393 : List ℕ := [t1,t2,t134,t220,t3,t4,t5,t6]
theorem b395 : Ban 220 7 v393 := viaCut p127_114 w26 (by decide) (by decide +kernel) (by decide +kernel)
def v394 : List ℕ := [t1,t2,t134,t3,t4,t5,t222,t6]
theorem b396 : Ban 220 7 v394 := viaCut p127_114 w27 (by decide) (by decide +kernel) (by decide +kernel)
def v395 : List ℕ := [t224,t1,t2,t134,t3,t4,t5,t6]
theorem b397 : Ban 220 7 v395 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t248 : ℕ := 0xdc0aadc0aadc0aadc0aadc0aadc0aadc0aadc0aadc0aadc0aadc0aa00000000000000000000fffffffffffffff0000000000ffffffffff
def v396 : List ℕ := [t1,t2,t134,t3,t4,t5,t248,t6]
theorem b398 : Ban 220 7 v396 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v397 : List ℕ := [t1,t2,t134,t3,t226,t4,t5,t6]
theorem b399 : Ban 220 7 v397 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t249 : ℕ := 0x9c0009c0009c0009c0009c0009c0009c0009c0009c0009c0009c00000000000000000000000ffffffffff0000000000000000000000000
def v398 : List ℕ := [t1,t2,t134,t3,t4,t249,t5,t6]
theorem b400 : Ban 220 7 v398 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v399 : List ℕ := [t1,t2,t134,t3,t228,t4,t5,t6]
theorem b401 : Ban 220 7 v399 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v400 : List ℕ := [t1,t2,t134,t3,t4,t5,t229]
theorem b402 : Ban 220 7 v400 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v401 : List ℕ := [t1,t2,t134,t3,t5,t6,t229]
theorem b403 : Ban 220 7 v401 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v402 : List ℕ := [t1,t2,t134,t3,t4,t5,t6,t229]
theorem b404 : Ban 220 7 v402 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v403 : List ℕ := [t230,t1,t2,t134,t3,t5,t6]
theorem b405 : Ban 220 7 v403 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v404 : List ℕ := [t230,t1,t2,t134,t3,t4,t5,t6]
theorem b406 : Ban 220 7 v404 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v405 : List ℕ := [t1,t2,t134,t3,t4,t5,t231]
theorem b407 : Ban 220 7 v405 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v406 : List ℕ := [t1,t2,t134,t3,t4,t5,t231,t6]
theorem b408 : Ban 220 7 v406 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v407 : List ℕ := [t1,t2,t134,t3,t4,t232,t5,t6]
theorem b409 : Ban 220 7 v407 := viaCut p127_114 w28 (by decide) (by decide +kernel) (by decide +kernel)
def t250 : ℕ := 0xfc000fc000fc000fc000fc000fc000fc000fc000fc000fc000fc000fffffffffffffffffffffffffffffffffff00000000000000000000
def v408 : List ℕ := [t1,t2,t134,t3,t4,t5,t250]
theorem b410 : Ban 220 7 v408 := viaCut p127_114 w29 (by decide) (by decide +kernel) (by decide +kernel)
def v409 : List ℕ := [t1,t2,t134,t3,t4,t6,t250]
theorem b411 : Ban 220 7 v409 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v410 : List ℕ := [t1,t2,t134,t3,t4,t5,t6,t250]
theorem b412 : Ban 220 7 v410 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def t251 : ℕ := 0x1c0001c0001c0001c0001c0001c0001c0001c0001c0001c0001c00000000000000000000000fffffffffffffff00000000000000000000
def v411 : List ℕ := [t1,t2,t134,t3,t251,t4,t6]
theorem b413 : Ban 220 7 v411 := viaCut p127_114 w30 (by decide) (by decide +kernel) (by decide +kernel)
def v412 : List ℕ := [t1,t2,t134,t3,t251,t4,t5,t6]
theorem b414 : Ban 220 7 v412 := viaCut p127_114 w31 (by decide) (by decide +kernel) (by decide +kernel)
def v413 : List ℕ := [t1,t2,t134,t3,t4,t238,t5]
theorem b415 : Ban 220 7 v413 := viaCut p127_114 w32 (by decide) (by decide +kernel) (by decide +kernel)
def v414 : List ℕ := [t1,t2,t134,t3,t4,t238,t5,t6]
theorem b416 : Ban 220 7 v414 := viaCut p127_114 w33 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b417 : Ban 220 8 v176 := viaBranch (ws := [v177,v178,v180,v181,v182,v183,v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v350,v351,v352,v353,v354,v355,v356,v357,v358,v359,v360,v361,v362,v363,v364,v365,v366,v367,v368,v369,v370,v371,v372,v373,v374,v375,v376,v377,v378,v379,v380,v381,v382,v383,v384,v385,v386,v387,v388,v389,v390,v391,v392,v393,v394,v395,v396,v397,v398,v399,v400,v401,v402,v403,v404,v405,v406,v407,v408,v409,v410,v411,v412,v413,v414]) (consBan b177 (consBan b179 (consBan b180 (consBan b181 (consBan b182 (consBan b183 (consBan b184 (consBan b185 (consBan b186 (consBan b187 (consBan b188 (consBan b189 (consBan b190 (consBan b191 (consBan b192 (consBan b193 (consBan b194 (consBan b195 (consBan b196 (consBan b197 (consBan b198 (consBan b199 (consBan b200 (consBan b201 (consBan b202 (consBan b203 (consBan b204 (consBan b205 (consBan b206 (consBan b207 (consBan b208 (consBan b209 (consBan b210 (consBan b211 (consBan b212 (consBan b213 (consBan b214 (consBan b215 (consBan b216 (consBan b217 (consBan b218 (consBan b219 (consBan b220 (consBan b221 (consBan b222 (consBan b223 (consBan b224 (consBan b226 (consBan b227 (consBan b228 (consBan b229 (consBan b230 (consBan b231 (consBan b232 (consBan b233 (consBan b234 (consBan b235 (consBan b236 (consBan b237 (consBan b238 (consBan b350 (consBan b351 (consBan b353 (consBan b354 (consBan b355 (consBan b356 (consBan b357 (consBan b358 (consBan b359 (consBan b360 (consBan b361 (consBan b362 (consBan b363 (consBan b364 (consBan b365 (consBan b366 (consBan b367 (consBan b368 (consBan b369 (consBan b370 (consBan b371 (consBan b372 (consBan b373 (consBan b374 (consBan b375 (consBan b376 (consBan b377 (consBan b378 (consBan b379 (consBan b380 (consBan b381 (consBan b382 (consBan b383 (consBan b384 (consBan b385 (consBan b386 (consBan b387 (consBan b388 (consBan b389 (consBan b390 (consBan b391 (consBan b392 (consBan b393 (consBan b394 (consBan b395 (consBan b396 (consBan b397 (consBan b398 (consBan b399 (consBan b400 (consBan b401 (consBan b402 (consBan b403 (consBan b404 (consBan b405 (consBan b406 (consBan b407 (consBan b408 (consBan b409 (consBan b410 (consBan b411 (consBan b412 (consBan b413 (consBan b414 (consBan b415 (consBan b416 (nilBan 220 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
def v415 : List ℕ := [t0,t1,t2,t134,t3,t4,t5,t6]
theorem b418 : Ban 220 8 v415 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
theorem b419 : Ban 220 8 v215 := viaCut p127_61 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v416 : List ℕ := [t163,t0,t1,t2,t3,t4,t5,t6]
theorem b420 : Ban 220 8 v416 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def t252 : ℕ := 0x8430084300843008430084300843008430084300843008430084300000000000fffff00000000000000000000fffff000000000000000
def v417 : List ℕ := [t0,t1,t252,t3,t4,t5,t6]
theorem b421 : Ban 220 8 v417 := viaCut p127_61 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v418 : List ℕ := [t0,t1,t252,t2,t3,t4,t5,t6]
theorem b422 : Ban 220 8 v418 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v419 : List ℕ := [t47,t0,t1,t2,t3,t4,t5,t6]
theorem b423 : Ban 220 8 v419 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def t253 : ℕ := 0x13acc13acc13acc13acc13acc13acc13acc13acc13acc13acc13accfffff0000000000fffff00000fffff00000fffffffffffffff00000
def v420 : List ℕ := [t0,t1,t2,t3,t253,t4,t5,t6]
theorem b424 : Ban 220 8 v420 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def t254 : ℕ := 0xacc00acc00acc00acc00acc00acc00acc00acc00acc00acc00acc000000000000000fffff00000fffff0000000000000000000000000
def v421 : List ℕ := [t254,t0,t1,t2,t3,t4,t5,t6]
theorem b425 : Ban 220 8 v421 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def t255 : ℕ := 0x1300013000130001300013000130001300013000130001300013000fffff000000000000000000000000000000fffff00000fffff00000
def v422 : List ℕ := [t0,t1,t2,t255,t3,t4,t5,t6]
theorem b426 : Ban 220 8 v422 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def t256 : ℕ := 0x88000880008800088000880008800088000880008800088000880000000000000000000000000000000000000000000000000000000
def v423 : List ℕ := [t256,t0,t1,t2,t3,t4,t5,t6]
theorem b427 : Ban 220 8 v423 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t257 : ℕ := 0x40aee40aee40aee40aee40aee40aee40aee40aee40aee40aee40aee000000000000000fffff00000ffffffffff00000fffffffffffffff
def v424 : List ℕ := [t0,t1,t2,t3,t257,t5,t6]
theorem b428 : Ban 220 8 v424 := viaCut p127_61 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v425 : List ℕ := [t1,t2,t3,t4,t257,t5,t6]
def t258 : ℕ := 0x8ba2e8ba2e8ba2e00000ffffffffff
def v426 : List ℕ := [t55,t57,t58,t258,t17]
def v427 : List ℕ := [t60,t55,t57,t58,t258,t17]
theorem b429 : Ban 60 5 v427 := viaSmall (by decide +kernel) (by decide)
def v428 : List ℕ := [t55,t61,t58,t258,t17]
theorem b430 : Ban 60 5 v428 := viaSmall (by decide +kernel) (by decide)
def v429 : List ℕ := [t57,t61,t58,t258,t17]
theorem b431 : Ban 60 5 v429 := viaSmall (by decide +kernel) (by decide)
def v430 : List ℕ := [t55,t57,t61,t58,t258,t17]
theorem b432 : Ban 60 5 v430 := viaSmall (by decide +kernel) (by decide)
def v431 : List ℕ := [t62,t57,t58,t258,t17]
theorem b433 : Ban 60 5 v431 := viaSmall (by decide +kernel) (by decide)
def v432 : List ℕ := [t62,t55,t57,t58,t258,t17]
theorem b434 : Ban 60 5 v432 := viaSmall (by decide +kernel) (by decide)
def v433 : List ℕ := [t63,t55,t58,t258,t17]
theorem b435 : Ban 60 5 v433 := viaSmall (by decide +kernel) (by decide)
def v434 : List ℕ := [t63,t55,t57,t58,t258,t17]
theorem b436 : Ban 60 5 v434 := viaSmall (by decide +kernel) (by decide)
def v435 : List ℕ := [t64,t55,t57,t58,t258,t17]
theorem b437 : Ban 60 5 v435 := viaSmall (by decide +kernel) (by decide)
def v436 : List ℕ := [t55,t57,t58,t258,t65,t17]
theorem b438 : Ban 60 5 v436 := viaSmall (by decide +kernel) (by decide)
def v437 : List ℕ := [t66,t55,t57,t58,t258,t17]
theorem b439 : Ban 60 5 v437 := viaSmall (by decide +kernel) (by decide)
def v438 : List ℕ := [t55,t57,t67,t58,t258,t17]
theorem b440 : Ban 60 5 v438 := viaSmall (by decide +kernel) (by decide)
def t259 : ℕ := 0x802008020080200000000000003ff
def v439 : List ℕ := [t259,t55,t57,t58,t258,t17]
theorem b441 : Ban 60 5 v439 := viaSmall (by decide +kernel) (by decide)
def v440 : List ℕ := [t55,t57,t58,t258,t73,t17]
theorem b442 : Ban 60 5 v440 := viaSmall (by decide +kernel) (by decide)
def t260 : ℕ := 0x240902409024090003ff0000000000
def v441 : List ℕ := [t260,t55,t57,t58,t258,t17]
theorem b443 : Ban 60 5 v441 := viaSmall (by decide +kernel) (by decide)
def t261 : ℕ := 0x83a0e83a0e83a0e00000fffffffc00
def v442 : List ℕ := [t55,t57,t58,t261,t17]
theorem b444 : Ban 60 5 v442 := viaSmall (by decide +kernel) (by decide)
def v443 : List ℕ := [t55,t57,t58,t261,t258,t17]
theorem b445 : Ban 60 5 v443 := viaSmall (by decide +kernel) (by decide)
def v444 : List ℕ := [t39,t55,t57,t58,t258,t17]
theorem b446 : Ban 60 5 v444 := viaSmall (by decide +kernel) (by decide)
def v445 : List ℕ := [t55,t57,t58,t258,t17,t68]
theorem b447 : Ban 60 5 v445 := viaSmall (by decide +kernel) (by decide)
def v446 : List ℕ := [t69,t55,t57,t58,t258,t17]
theorem b448 : Ban 60 5 v446 := viaSmall (by decide +kernel) (by decide)
def v447 : List ℕ := [t55,t57,t58,t258,t42,t17]
theorem b449 : Ban 60 5 v447 := viaSmall (by decide +kernel) (by decide)
def v448 : List ℕ := [t26,t55,t57,t58,t258,t17]
theorem b450 : Ban 60 5 v448 := viaSmall (by decide +kernel) (by decide)
def v449 : List ℕ := [t55,t57,t258,t78,t17]
theorem b451 : Ban 60 5 v449 := viaSmall (by decide +kernel) (by decide)
def v450 : List ℕ := [t55,t57,t58,t258,t78,t17]
theorem b452 : Ban 60 5 v450 := viaSmall (by decide +kernel) (by decide)
def v451 : List ℕ := [t55,t79,t57,t58,t258,t17]
theorem b453 : Ban 60 5 v451 := viaSmall (by decide +kernel) (by decide)
def v452 : List ℕ := [t55,t57,t80,t258,t17]
theorem b454 : Ban 60 5 v452 := viaSmall (by decide +kernel) (by decide)
def v453 : List ℕ := [t55,t57,t80,t58,t258,t17]
theorem b455 : Ban 60 5 v453 := viaSmall (by decide +kernel) (by decide)
def t262 : ℕ := 0x3ffffc00
def v454 : List ℕ := [t262,t55,t57,t58,t258,t17]
theorem b456 : Ban 60 5 v454 := viaSmall (by decide +kernel) (by decide)
def t263 : ℕ := 0xbbaeebbaeebbaeeffc00ffffffffff
def v455 : List ℕ := [t55,t57,t58,t258,t263,t17]
theorem b457 : Ban 60 5 v455 := viaSmall (by decide +kernel) (by decide)
def t264 : ℕ := 0x300c0300c0300c0ffc000000000000
def v456 : List ℕ := [t55,t264,t57,t58,t258,t17]
theorem b458 : Ban 60 5 v456 := viaSmall (by decide +kernel) (by decide)
def t265 : ℕ := 0x8ba2e8ba2e8ba2e00000ffc00003ff
def v457 : List ℕ := [t55,t57,t58,t265,t258,t17]
theorem b459 : Ban 60 5 v457 := viaSmall (by decide +kernel) (by decide)
def v458 : List ℕ := [t81,t55,t57,t58,t258,t17]
theorem b460 : Ban 60 5 v458 := viaSmall (by decide +kernel) (by decide)
def v459 : List ℕ := [t55,t57,t58,t258,t17,t52]
theorem b461 : Ban 60 5 v459 := viaSmall (by decide +kernel) (by decide)
def v460 : List ℕ := [t55,t53,t57,t58,t258,t17]
theorem b462 : Ban 60 5 v460 := viaSmall (by decide +kernel) (by decide)
def v461 : List ℕ := [t55,t57,t58,t258,t82,t17]
theorem b463 : Ban 60 5 v461 := viaSmall (by decide +kernel) (by decide)
def t266 : ℕ := 0x9024090240902400000fffff00000
def v462 : List ℕ := [t266,t55,t57,t58,t17]
theorem b464 : Ban 60 5 v462 := viaSmall (by decide +kernel) (by decide)
def v463 : List ℕ := [t266,t55,t57,t258,t17]
theorem b465 : Ban 60 5 v463 := viaSmall (by decide +kernel) (by decide)
def v464 : List ℕ := [t266,t55,t57,t58,t258,t17]
theorem b466 : Ban 60 5 v464 := viaSmall (by decide +kernel) (by decide)
def v465 : List ℕ := [t55,t57,t51,t58,t258,t17]
theorem b467 : Ban 60 5 v465 := viaSmall (by decide +kernel) (by decide)
def v466 : List ℕ := [t55,t57,t58,t258,t31]
theorem b468 : Ban 60 5 v466 := viaSmall (by decide +kernel) (by decide)
def v467 : List ℕ := [t55,t57,t58,t258,t17,t31]
theorem b469 : Ban 60 5 v467 := viaSmall (by decide +kernel) (by decide)
def v468 : List ℕ := [t32,t55,t57,t58,t258,t17]
theorem b470 : Ban 60 5 v468 := viaSmall (by decide +kernel) (by decide)
def v469 : List ℕ := [t55,t57,t54,t58,t258]
theorem b471 : Ban 60 5 v469 := viaSmall (by decide +kernel) (by decide)
def v470 : List ℕ := [t55,t57,t54,t58,t258,t17]
theorem b472 : Ban 60 5 v470 := viaSmall (by decide +kernel) (by decide)
def t267 : ℕ := 0x80200802008020000000ffc0000000
def v471 : List ℕ := [t55,t57,t267,t58,t258,t17]
theorem b473 : Ban 60 5 v471 := viaSmall (by decide +kernel) (by decide)
def t268 : ℕ := 0xcbb2ecbb2ecbb2efffffffffffffff
def v472 : List ℕ := [t55,t57,t58,t258,t17,t268]
theorem b474 : Ban 60 5 v472 := viaSmall (by decide +kernel) (by decide)
def t269 : ℕ := 0xb82e0b82e0b82e00000003fffffff
def v473 : List ℕ := [t269,t55,t57,t58,t258,t17]
theorem b475 : Ban 60 5 v473 := viaSmall (by decide +kernel) (by decide)
def t270 : ℕ := 0x401004010040100fffff0000000000
def v474 : List ℕ := [t55,t57,t270,t58,t258,t17]
theorem b476 : Ban 60 5 v474 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b477 : Ban 60 6 v426 := viaBranch (ws := [v427,v428,v429,v430,v431,v432,v433,v434,v435,v436,v437,v438,v439,v80,v440,v441,v442,v443,v444,v445,v446,v447,v448,v449,v450,v451,v452,v453,v454,v455,v456,v457,v458,v459,v460,v461,v462,v463,v464,v465,v466,v467,v468,v469,v470,v471,v472,v473,v474]) (consBan b429 (consBan b430 (consBan b431 (consBan b432 (consBan b433 (consBan b434 (consBan b435 (consBan b436 (consBan b437 (consBan b438 (consBan b439 (consBan b440 (consBan b441 (consBan b77 (consBan b442 (consBan b443 (consBan b444 (consBan b445 (consBan b446 (consBan b447 (consBan b448 (consBan b449 (consBan b450 (consBan b451 (consBan b452 (consBan b453 (consBan b454 (consBan b455 (consBan b456 (consBan b457 (consBan b458 (consBan b459 (consBan b460 (consBan b461 (consBan b462 (consBan b463 (consBan b464 (consBan b465 (consBan b466 (consBan b467 (consBan b468 (consBan b469 (consBan b470 (consBan b471 (consBan b472 (consBan b473 (consBan b474 (consBan b475 (consBan b476 (nilBan 60 5)))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w35 : Wide 60 6 v426 := viaSub (ws := [v426]) (consBan b477 (nilBan 60 6)) (by decide) (by decide +kernel)
theorem b478 : Ban 220 8 v425 := viaCut p127_91 w35 (by decide) (by decide +kernel) (by decide +kernel)
def v475 : List ℕ := [t0,t1,t2,t3,t4,t257,t5,t6]
theorem b479 : Ban 220 8 v475 := viaCut p127_84 w3 (by decide) (by decide +kernel) (by decide +kernel)
def t271 : ℕ := 0xa4400a4400a4400a4400a4400a4400a4400a4400a4400a4400a44000000000000000fffff00000fffff0000000000fffff0000000000
def v476 : List ℕ := [t271,t1,t2,t3,t4,t5,t6]
theorem b480 : Ban 220 8 v476 := viaCut p127_61 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v477 : List ℕ := [t271,t0,t1,t2,t3,t4,t5,t6]
theorem b481 : Ban 220 8 v477 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def t272 : ℕ := 0x4002240022400224002240022400224002240022400224002240022000000000000000000000000000000fffff0000000000ffffffffff
def v478 : List ℕ := [t0,t1,t2,t3,t272,t5,t6]
theorem b482 : Ban 220 8 v478 := viaCut p127_61 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v479 : List ℕ := [t0,t1,t2,t3,t272,t4,t5,t6]
theorem b483 : Ban 220 8 v479 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v480 : List ℕ := [t191,t0,t1,t2,t3,t4,t5,t6]
theorem b484 : Ban 220 8 v480 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def t273 : ℕ := 0x9cacc9cacc9cacc9cacc9cacc9cacc9cacc9cacc9cacc9cacc9cacc000000000000000ffffffffffffffffffff00000fffff0000000000
def v481 : List ℕ := [t0,t1,t2,t3,t4,t5,t273,t6]
theorem b485 : Ban 220 8 v481 := viaCut p127_84 w3 (by decide) (by decide +kernel) (by decide +kernel)
def t274 : ℕ := 0xacc00acc00acc00acc00acc00acc00acc00acc00acc00acc00acc000000000000000fffff00000000000000000000fffff0000000000
def v482 : List ℕ := [t274,t0,t1,t2,t3,t4,t5,t6]
theorem b486 : Ban 220 8 v482 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def t275 : ℕ := 0x9c0009c0009c0009c0009c0009c0009c0009c0009c0009c0009c00000000000000000000000fffff00000fffff00000000000000000000
def v483 : List ℕ := [t0,t1,t2,t3,t4,t275,t5,t6]
theorem b487 : Ban 220 8 v483 := viaCut p127_82 w34 (by decide) (by decide +kernel) (by decide +kernel)
def t276 : ℕ := 0xfffff00000000000000000000000000000000000
def v484 : List ℕ := [t276,t0,t1,t2,t3,t4,t5,t6]
theorem b488 : Ban 220 8 v484 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def t277 : ℕ := 0xe0acce0acce0acce0acce0acce0acce0acce0acce0acce0acce0accffffffffffffffffffff00000fffff0000000000fffff0000000000
def v485 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t277]
theorem b489 : Ban 220 8 v485 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def t278 : ℕ := 0xacc00acc00acc00acc00acc00acc00acc00acc00acc00acc00acc0000000000000000000000000fffff0000000000fffff0000000000
def v486 : List ℕ := [t278,t0,t1,t2,t3,t4,t5,t6]
theorem b490 : Ban 220 8 v486 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def t279 : ℕ := 0xe0000e0000e0000e0000e0000e0000e0000e0000e0000e0000e0000fffffffffffffff0000000000000000000000000000000000000000
def v487 : List ℕ := [t0,t1,t2,t3,t4,t5,t279,t6]
theorem b491 : Ban 220 8 v487 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v488 : List ℕ := [t0,t135,t1,t2,t3,t4,t5,t6]
theorem b492 : Ban 220 8 v488 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v489 : List ℕ := [t0,t1,t136,t3,t4,t5,t6]
def v490 : List ℕ := [t92,t87,t88,t109,t90,t91]
theorem b493 : Ban 55 5 v490 := viaSmall (by decide +kernel) (by decide)
def v491 : List ℕ := [t87,t88,t93,t109,t90,t91]
theorem b494 : Ban 55 5 v491 := viaSmall (by decide +kernel) (by decide)
def v492 : List ℕ := [t94,t87,t88,t109,t90,t91]
theorem b495 : Ban 55 5 v492 := viaSmall (by decide +kernel) (by decide)
def v493 : List ℕ := [t87,t95,t88,t109,t90,t91]
theorem b496 : Ban 55 5 v493 := viaSmall (by decide +kernel) (by decide)
def t280 : ℕ := 0x400801002004000000000007ff
def v494 : List ℕ := [t280,t87,t88,t109,t90,t91]
theorem b497 : Ban 55 5 v494 := viaSmall (by decide +kernel) (by decide)
def t281 : ℕ := 0x15f2be57caf95f7fffffffffffff
def v495 : List ℕ := [t87,t88,t281,t90,t91]
theorem b498 : Ban 55 5 v495 := viaSmall (by decide +kernel) (by decide)
def v496 : List ℕ := [t87,t88,t109,t281,t90,t91]
theorem b499 : Ban 55 5 v496 := viaSmall (by decide +kernel) (by decide)
def t282 : ℕ := 0x100200400801000ffe003ff800
def v497 : List ℕ := [t282,t87,t88,t109,t90,t91]
theorem b500 : Ban 55 5 v497 := viaSmall (by decide +kernel) (by decide)
def t283 : ℕ := 0x15a2b4568ad15a7ff001ffc00000
def v498 : List ℕ := [t87,t88,t283,t90,t91]
theorem b501 : Ban 55 5 v498 := viaSmall (by decide +kernel) (by decide)
def v499 : List ℕ := [t87,t88,t283,t109,t90,t91]
theorem b502 : Ban 55 5 v499 := viaSmall (by decide +kernel) (by decide)
def v500 : List ℕ := [t100,t87,t88,t109,t90,t91]
theorem b503 : Ban 55 5 v500 := viaSmall (by decide +kernel) (by decide)
def v501 : List ℕ := [t87,t88,t109,t90,t101,t91]
theorem b504 : Ban 55 5 v501 := viaSmall (by decide +kernel) (by decide)
def v502 : List ℕ := [t102,t87,t88,t109,t90,t91]
theorem b505 : Ban 55 5 v502 := viaSmall (by decide +kernel) (by decide)
def v503 : List ℕ := [t87,t88,t109,t103,t90,t91]
theorem b506 : Ban 55 5 v503 := viaSmall (by decide +kernel) (by decide)
def v504 : List ℕ := [t104,t87,t88,t109,t90,t91]
theorem b507 : Ban 55 5 v504 := viaSmall (by decide +kernel) (by decide)
def v505 : List ℕ := [t87,t88,t109,t90,t91,t105]
theorem b508 : Ban 55 5 v505 := viaSmall (by decide +kernel) (by decide)
def v506 : List ℕ := [t106,t87,t88,t109,t90,t91]
theorem b509 : Ban 55 5 v506 := viaSmall (by decide +kernel) (by decide)
def v507 : List ℕ := [t87,t88,t109,t90,t107,t91]
theorem b510 : Ban 55 5 v507 := viaSmall (by decide +kernel) (by decide)
def v508 : List ℕ := [t87,t111,t109,t90,t91]
theorem b511 : Ban 55 5 v508 := viaSmall (by decide +kernel) (by decide)
def v509 : List ℕ := [t87,t88,t111,t109,t90,t91]
theorem b512 : Ban 55 5 v509 := viaSmall (by decide +kernel) (by decide)
def v510 : List ℕ := [t87,t112,t88,t109,t90,t91]
theorem b513 : Ban 55 5 v510 := viaSmall (by decide +kernel) (by decide)
def v511 : List ℕ := [t87,t88,t109,t113,t91]
theorem b514 : Ban 55 5 v511 := viaSmall (by decide +kernel) (by decide)
def v512 : List ℕ := [t87,t88,t109,t90,t113,t91]
theorem b515 : Ban 55 5 v512 := viaSmall (by decide +kernel) (by decide)
def v513 : List ℕ := [t87,t114,t88,t109,t90,t91]
theorem b516 : Ban 55 5 v513 := viaSmall (by decide +kernel) (by decide)
def v514 : List ℕ := [t87,t88,t109,t115,t91]
theorem b517 : Ban 55 5 v514 := viaSmall (by decide +kernel) (by decide)
def v515 : List ℕ := [t87,t88,t109,t115,t90,t91]
theorem b518 : Ban 55 5 v515 := viaSmall (by decide +kernel) (by decide)
def v516 : List ℕ := [t116,t87,t88,t109,t90,t91]
theorem b519 : Ban 55 5 v516 := viaSmall (by decide +kernel) (by decide)
def v517 : List ℕ := [t87,t88,t109,t90,t91,t117]
theorem b520 : Ban 55 5 v517 := viaSmall (by decide +kernel) (by decide)
def v518 : List ℕ := [t87,t118,t88,t109,t90,t91]
theorem b521 : Ban 55 5 v518 := viaSmall (by decide +kernel) (by decide)
def v519 : List ℕ := [t87,t88,t109,t90,t119,t91]
theorem b522 : Ban 55 5 v519 := viaSmall (by decide +kernel) (by decide)
def t284 : ℕ := 0x4008010020040000001ffc00000
def v520 : List ℕ := [t87,t284,t88,t90,t91]
theorem b523 : Ban 55 5 v520 := viaSmall (by decide +kernel) (by decide)
def v521 : List ℕ := [t87,t284,t88,t109,t90,t91]
theorem b524 : Ban 55 5 v521 := viaSmall (by decide +kernel) (by decide)
def t285 : ℕ := 0x37e6fcdf9bf37e7ff001ffffffff
def v522 : List ℕ := [t87,t88,t109,t90,t285,t91]
theorem b525 : Ban 55 5 v522 := viaSmall (by decide +kernel) (by decide)
def t286 : ℕ := 0x11e23c4788f11e7ff000000007ff
def v523 : List ℕ := [t87,t88,t286,t109,t90,t91]
theorem b526 : Ban 55 5 v523 := viaSmall (by decide +kernel) (by decide)
def t287 : ℕ := 0x22044088110220000000003ff800
def v524 : List ℕ := [t87,t88,t287,t90,t91]
theorem b527 : Ban 55 5 v524 := viaSmall (by decide +kernel) (by decide)
def v525 : List ℕ := [t87,t88,t109,t287,t90,t91]
theorem b528 : Ban 55 5 v525 := viaSmall (by decide +kernel) (by decide)
def t288 : ℕ := 0x100200400801007ff00000000000
def v526 : List ℕ := [t87,t88,t288,t109,t90,t91]
theorem b529 : Ban 55 5 v526 := viaSmall (by decide +kernel) (by decide)
def t289 : ℕ := 0x3de7bcf79ef3de7fffffffc007ff
def v527 : List ℕ := [t87,t88,t90,t91,t289]
theorem b530 : Ban 55 5 v527 := viaSmall (by decide +kernel) (by decide)
def v528 : List ℕ := [t87,t88,t109,t90,t91,t289]
theorem b531 : Ban 55 5 v528 := viaSmall (by decide +kernel) (by decide)
def t290 : ℕ := 0x5e0bc1782f05e000001ffc007ff
def v529 : List ℕ := [t87,t88,t290,t90,t91]
theorem b532 : Ban 55 5 v529 := viaSmall (by decide +kernel) (by decide)
def v530 : List ℕ := [t87,t88,t290,t109,t90,t91]
theorem b533 : Ban 55 5 v530 := viaSmall (by decide +kernel) (by decide)
def t291 : ℕ := 0x280500a0140280000ffe00000000
def v531 : List ℕ := [t87,t88,t109,t90,t291,t91]
theorem b534 : Ban 55 5 v531 := viaSmall (by decide +kernel) (by decide)
def v532 : List ℕ := [t87,t88,t109,t128,t90,t91]
theorem b535 : Ban 55 5 v532 := viaSmall (by decide +kernel) (by decide)
def v533 : List ℕ := [t87,t88,t109,t90,t129]
theorem b536 : Ban 55 5 v533 := viaSmall (by decide +kernel) (by decide)
def v534 : List ℕ := [t87,t88,t109,t91,t129]
theorem b537 : Ban 55 5 v534 := viaSmall (by decide +kernel) (by decide)
def v535 : List ℕ := [t87,t88,t109,t90,t91,t129]
theorem b538 : Ban 55 5 v535 := viaSmall (by decide +kernel) (by decide)
def v536 : List ℕ := [t87,t88,t130,t109,t91]
theorem b539 : Ban 55 5 v536 := viaSmall (by decide +kernel) (by decide)
def v537 : List ℕ := [t87,t88,t130,t109,t90,t91]
theorem b540 : Ban 55 5 v537 := viaSmall (by decide +kernel) (by decide)
def v538 : List ℕ := [t87,t88,t109,t131,t90]
theorem b541 : Ban 55 5 v538 := viaSmall (by decide +kernel) (by decide)
def v539 : List ℕ := [t87,t88,t109,t131,t90,t91]
theorem b542 : Ban 55 5 v539 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b543 : Ban 55 6 v130 := viaBranch (ws := [v490,v491,v492,v493,v494,v495,v496,v497,v498,v499,v500,v501,v502,v503,v504,v505,v506,v507,v135,v508,v509,v510,v511,v512,v513,v514,v515,v516,v517,v518,v519,v520,v521,v522,v523,v524,v525,v526,v527,v528,v529,v530,v531,v532,v533,v534,v535,v536,v537,v538,v539]) (consBan b493 (consBan b494 (consBan b495 (consBan b496 (consBan b497 (consBan b498 (consBan b499 (consBan b500 (consBan b501 (consBan b502 (consBan b503 (consBan b504 (consBan b505 (consBan b506 (consBan b507 (consBan b508 (consBan b509 (consBan b510 (consBan b132 (consBan b511 (consBan b512 (consBan b513 (consBan b514 (consBan b515 (consBan b516 (consBan b517 (consBan b518 (consBan b519 (consBan b520 (consBan b521 (consBan b522 (consBan b523 (consBan b524 (consBan b525 (consBan b526 (consBan b527 (consBan b528 (consBan b529 (consBan b530 (consBan b531 (consBan b532 (consBan b533 (consBan b534 (consBan b535 (consBan b536 (consBan b537 (consBan b538 (consBan b539 (consBan b540 (consBan b541 (consBan b542 (nilBan 55 5)))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w36 : Wide 55 6 v130 := viaSub (ws := [v130]) (consBan b543 (nilBan 55 6)) (by decide) (by decide +kernel)
theorem b544 : Ban 220 8 v489 := viaCut p127_61 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v540 : List ℕ := [t0,t2,t136,t3,t4,t5,t6]
def v541 : List ℕ := [t96,t87,t89,t109,t90,t91]
theorem b545 : Ban 55 5 v541 := viaSmall (by decide +kernel) (by decide)
def v542 : List ℕ := [t89,t97,t109,t90,t91]
theorem b546 : Ban 55 5 v542 := viaSmall (by decide +kernel) (by decide)
def v543 : List ℕ := [t87,t89,t97,t109,t90,t91]
theorem b547 : Ban 55 5 v543 := viaSmall (by decide +kernel) (by decide)
def v544 : List ℕ := [t98,t89,t109,t90,t91]
theorem b548 : Ban 55 5 v544 := viaSmall (by decide +kernel) (by decide)
def v545 : List ℕ := [t98,t87,t89,t109,t90,t91]
theorem b549 : Ban 55 5 v545 := viaSmall (by decide +kernel) (by decide)
def v546 : List ℕ := [t87,t99,t89,t109,t90,t91]
theorem b550 : Ban 55 5 v546 := viaSmall (by decide +kernel) (by decide)
def v547 : List ℕ := [t280,t87,t89,t109,t90,t91]
theorem b551 : Ban 55 5 v547 := viaSmall (by decide +kernel) (by decide)
def v548 : List ℕ := [t87,t89,t109,t281,t90,t91]
theorem b552 : Ban 55 5 v548 := viaSmall (by decide +kernel) (by decide)
def v549 : List ℕ := [t282,t87,t89,t109,t90,t91]
theorem b553 : Ban 55 5 v549 := viaSmall (by decide +kernel) (by decide)
def v550 : List ℕ := [t87,t89,t283,t109,t90,t91]
theorem b554 : Ban 55 5 v550 := viaSmall (by decide +kernel) (by decide)
def v551 : List ℕ := [t100,t87,t89,t109,t90,t91]
theorem b555 : Ban 55 5 v551 := viaSmall (by decide +kernel) (by decide)
def v552 : List ℕ := [t87,t89,t109,t90,t101,t91]
theorem b556 : Ban 55 5 v552 := viaSmall (by decide +kernel) (by decide)
def v553 : List ℕ := [t102,t87,t89,t109,t90,t91]
theorem b557 : Ban 55 5 v553 := viaSmall (by decide +kernel) (by decide)
def v554 : List ℕ := [t87,t89,t109,t103,t90,t91]
theorem b558 : Ban 55 5 v554 := viaSmall (by decide +kernel) (by decide)
def v555 : List ℕ := [t104,t87,t89,t109,t90,t91]
theorem b559 : Ban 55 5 v555 := viaSmall (by decide +kernel) (by decide)
def v556 : List ℕ := [t87,t89,t109,t90,t91,t105]
theorem b560 : Ban 55 5 v556 := viaSmall (by decide +kernel) (by decide)
def v557 : List ℕ := [t106,t87,t89,t109,t90,t91]
theorem b561 : Ban 55 5 v557 := viaSmall (by decide +kernel) (by decide)
def v558 : List ℕ := [t87,t89,t109,t90,t107,t91]
theorem b562 : Ban 55 5 v558 := viaSmall (by decide +kernel) (by decide)
def v559 : List ℕ := [t87,t110,t109,t90,t91]
theorem b563 : Ban 55 5 v559 := viaSmall (by decide +kernel) (by decide)
def v560 : List ℕ := [t87,t110,t89,t109,t90,t91]
theorem b564 : Ban 55 5 v560 := viaSmall (by decide +kernel) (by decide)
def v561 : List ℕ := [t120,t87,t89,t109,t90,t91]
theorem b565 : Ban 55 5 v561 := viaSmall (by decide +kernel) (by decide)
def v562 : List ℕ := [t87,t89,t109,t90,t121,t91]
theorem b566 : Ban 55 5 v562 := viaSmall (by decide +kernel) (by decide)
def v563 : List ℕ := [t87,t122,t89,t109,t90,t91]
theorem b567 : Ban 55 5 v563 := viaSmall (by decide +kernel) (by decide)
def v564 : List ℕ := [t87,t89,t109,t123,t90,t91]
theorem b568 : Ban 55 5 v564 := viaSmall (by decide +kernel) (by decide)
def v565 : List ℕ := [t87,t124,t89,t109,t90,t91]
theorem b569 : Ban 55 5 v565 := viaSmall (by decide +kernel) (by decide)
def v566 : List ℕ := [t87,t89,t109,t90,t125]
theorem b570 : Ban 55 5 v566 := viaSmall (by decide +kernel) (by decide)
def v567 : List ℕ := [t87,t89,t109,t90,t91,t125]
theorem b571 : Ban 55 5 v567 := viaSmall (by decide +kernel) (by decide)
def v568 : List ℕ := [t87,t126,t89,t109,t90,t91]
theorem b572 : Ban 55 5 v568 := viaSmall (by decide +kernel) (by decide)
def v569 : List ℕ := [t87,t89,t109,t90,t127]
theorem b573 : Ban 55 5 v569 := viaSmall (by decide +kernel) (by decide)
def v570 : List ℕ := [t87,t89,t109,t90,t127,t91]
theorem b574 : Ban 55 5 v570 := viaSmall (by decide +kernel) (by decide)
def v571 : List ℕ := [t87,t284,t89,t109,t90,t91]
theorem b575 : Ban 55 5 v571 := viaSmall (by decide +kernel) (by decide)
def v572 : List ℕ := [t87,t89,t90,t285,t91]
theorem b576 : Ban 55 5 v572 := viaSmall (by decide +kernel) (by decide)
def v573 : List ℕ := [t87,t89,t109,t90,t285,t91]
theorem b577 : Ban 55 5 v573 := viaSmall (by decide +kernel) (by decide)
def v574 : List ℕ := [t87,t89,t286,t90,t91]
theorem b578 : Ban 55 5 v574 := viaSmall (by decide +kernel) (by decide)
def v575 : List ℕ := [t87,t89,t286,t109,t90,t91]
theorem b579 : Ban 55 5 v575 := viaSmall (by decide +kernel) (by decide)
def v576 : List ℕ := [t87,t89,t109,t287,t90,t91]
theorem b580 : Ban 55 5 v576 := viaSmall (by decide +kernel) (by decide)
def v577 : List ℕ := [t87,t288,t89,t109,t90,t91]
theorem b581 : Ban 55 5 v577 := viaSmall (by decide +kernel) (by decide)
def v578 : List ℕ := [t87,t89,t109,t90,t91,t289]
theorem b582 : Ban 55 5 v578 := viaSmall (by decide +kernel) (by decide)
def v579 : List ℕ := [t87,t290,t89,t109,t90,t91]
theorem b583 : Ban 55 5 v579 := viaSmall (by decide +kernel) (by decide)
def v580 : List ℕ := [t87,t89,t109,t90,t291,t91]
theorem b584 : Ban 55 5 v580 := viaSmall (by decide +kernel) (by decide)
def v581 : List ℕ := [t87,t89,t109,t128,t90,t91]
theorem b585 : Ban 55 5 v581 := viaSmall (by decide +kernel) (by decide)
def v582 : List ℕ := [t87,t89,t109,t90,t129]
theorem b586 : Ban 55 5 v582 := viaSmall (by decide +kernel) (by decide)
def v583 : List ℕ := [t87,t89,t109,t91,t129]
theorem b587 : Ban 55 5 v583 := viaSmall (by decide +kernel) (by decide)
def v584 : List ℕ := [t87,t89,t109,t90,t91,t129]
theorem b588 : Ban 55 5 v584 := viaSmall (by decide +kernel) (by decide)
def v585 : List ℕ := [t87,t130,t89,t109,t91]
theorem b589 : Ban 55 5 v585 := viaSmall (by decide +kernel) (by decide)
def v586 : List ℕ := [t87,t130,t89,t109,t90,t91]
theorem b590 : Ban 55 5 v586 := viaSmall (by decide +kernel) (by decide)
def v587 : List ℕ := [t87,t89,t109,t131,t90]
theorem b591 : Ban 55 5 v587 := viaSmall (by decide +kernel) (by decide)
def v588 : List ℕ := [t87,t89,t109,t131,t90,t91]
theorem b592 : Ban 55 5 v588 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b593 : Ban 55 6 v131 := viaBranch (ws := [v541,v542,v543,v544,v545,v546,v547,v548,v549,v550,v551,v552,v553,v554,v555,v556,v557,v558,v133,v559,v560,v561,v562,v563,v564,v565,v566,v567,v568,v569,v570,v571,v572,v573,v574,v575,v576,v577,v578,v579,v580,v581,v582,v583,v584,v585,v586,v587,v588]) (consBan b545 (consBan b546 (consBan b547 (consBan b548 (consBan b549 (consBan b550 (consBan b551 (consBan b552 (consBan b553 (consBan b554 (consBan b555 (consBan b556 (consBan b557 (consBan b558 (consBan b559 (consBan b560 (consBan b561 (consBan b562 (consBan b130 (consBan b563 (consBan b564 (consBan b565 (consBan b566 (consBan b567 (consBan b568 (consBan b569 (consBan b570 (consBan b571 (consBan b572 (consBan b573 (consBan b574 (consBan b575 (consBan b576 (consBan b577 (consBan b578 (consBan b579 (consBan b580 (consBan b581 (consBan b582 (consBan b583 (consBan b584 (consBan b585 (consBan b586 (consBan b587 (consBan b588 (consBan b589 (consBan b590 (consBan b591 (consBan b592 (nilBan 55 5)))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w37 : Wide 55 6 v131 := viaSub (ws := [v131]) (consBan b593 (nilBan 55 6)) (by decide) (by decide +kernel)
theorem b594 : Ban 220 8 v540 := viaCut p127_61 w37 (by decide) (by decide +kernel) (by decide +kernel)
def v589 : List ℕ := [t0,t1,t2,t136,t3,t4,t5,t6]
theorem b595 : Ban 220 8 v589 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v590 : List ℕ := [t0,t141,t2,t3,t4,t5,t6]
def t292 : ℕ := 0x8010020040087ff001ffc007ff
def t293 : ℕ := 0x560ac1582b056000ffe00000000
def t294 : ℕ := 0x10520a41482905000000003fffff
def v591 : List ℕ := [t292,t293,t294,t90,t91]
def t295 : ℕ := 0x5e0bc1782f05e7fffffffc007ff
def v592 : List ℕ := [t292,t295,t294,t90,t91]
theorem b596 : Ban 55 5 v592 := viaSmall (by decide +kernel) (by decide)
def v593 : List ℕ := [t293,t295,t294,t90,t91]
theorem b597 : Ban 55 5 v593 := viaSmall (by decide +kernel) (by decide)
def v594 : List ℕ := [t292,t293,t295,t294,t90,t91]
theorem b598 : Ban 55 5 v594 := viaSmall (by decide +kernel) (by decide)
def v595 : List ℕ := [t92,t292,t293,t294,t90,t91]
theorem b599 : Ban 55 5 v595 := viaSmall (by decide +kernel) (by decide)
def t296 : ℕ := 0x10d21a4348690d7ff001ffffffff
def v596 : List ℕ := [t292,t293,t294,t296,t90,t91]
theorem b600 : Ban 55 5 v596 := viaSmall (by decide +kernel) (by decide)
def t297 : ℕ := 0x8010020040087ff001ffc00000
def v597 : List ℕ := [t297,t292,t293,t294,t90,t91]
theorem b601 : Ban 55 5 v597 := viaSmall (by decide +kernel) (by decide)
def t298 : ℕ := 0x10520a41482905000000003ff800
def v598 : List ℕ := [t292,t293,t298,t294,t90,t91]
theorem b602 : Ban 55 5 v598 := viaSmall (by decide +kernel) (by decide)
def v599 : List ℕ := [t120,t292,t293,t294,t90,t91]
theorem b603 : Ban 55 5 v599 := viaSmall (by decide +kernel) (by decide)
def t299 : ℕ := 0x2684d09a1342687ff001ffffffff
def v600 : List ℕ := [t292,t293,t294,t90,t299,t91]
theorem b604 : Ban 55 5 v600 := viaSmall (by decide +kernel) (by decide)
def t300 : ℕ := 0x8010020040087ff000000007ff
def v601 : List ℕ := [t300,t292,t293,t294,t90,t91]
theorem b605 : Ban 55 5 v601 := viaSmall (by decide +kernel) (by decide)
def v602 : List ℕ := [t292,t293,t294,t123,t90,t91]
theorem b606 : Ban 55 5 v602 := viaSmall (by decide +kernel) (by decide)
def v603 : List ℕ := [t116,t292,t293,t294,t90,t91]
theorem b607 : Ban 55 5 v603 := viaSmall (by decide +kernel) (by decide)
def t301 : ℕ := 0x388710e21c43887fffffffc007ff
def v604 : List ℕ := [t292,t293,t294,t90,t91,t301]
theorem b608 : Ban 55 5 v604 := viaSmall (by decide +kernel) (by decide)
def t302 : ℕ := 0x801002004008000001ffc007ff
def v605 : List ℕ := [t302,t292,t293,t294,t90,t91]
theorem b609 : Ban 55 5 v605 := viaSmall (by decide +kernel) (by decide)
def v606 : List ℕ := [t292,t293,t294,t90,t119,t91]
theorem b610 : Ban 55 5 v606 := viaSmall (by decide +kernel) (by decide)
def v607 : List ℕ := [t96,t292,t293,t294,t90,t91]
theorem b611 : Ban 55 5 v607 := viaSmall (by decide +kernel) (by decide)
def t303 : ℕ := 0x1572ae55cab957000ffe003fffff
def v608 : List ℕ := [t292,t293,t303,t90,t91]
theorem b612 : Ban 55 5 v608 := viaSmall (by decide +kernel) (by decide)
def v609 : List ℕ := [t292,t294,t303,t90,t91]
theorem b613 : Ban 55 5 v609 := viaSmall (by decide +kernel) (by decide)
def v610 : List ℕ := [t292,t293,t294,t303,t90,t91]
theorem b614 : Ban 55 5 v610 := viaSmall (by decide +kernel) (by decide)
def t304 : ℕ := 0x520a414829052000ffe00000000
def v611 : List ℕ := [t292,t304,t294,t90,t91]
theorem b615 : Ban 55 5 v611 := viaSmall (by decide +kernel) (by decide)
def v612 : List ℕ := [t292,t304,t293,t294,t90,t91]
theorem b616 : Ban 55 5 v612 := viaSmall (by decide +kernel) (by decide)
def t305 : ℕ := 0x10120240480901000000003fffff
def v613 : List ℕ := [t292,t293,t305,t90,t91]
theorem b617 : Ban 55 5 v613 := viaSmall (by decide +kernel) (by decide)
def v614 : List ℕ := [t292,t293,t305,t294,t90,t91]
theorem b618 : Ban 55 5 v614 := viaSmall (by decide +kernel) (by decide)
def v615 : List ℕ := [t292,t112,t293,t294,t90,t91]
theorem b619 : Ban 55 5 v615 := viaSmall (by decide +kernel) (by decide)
def t306 : ℕ := 0x2764ec9d93b276000ffffffff800
def v616 : List ℕ := [t292,t293,t294,t306,t91]
theorem b620 : Ban 55 5 v616 := viaSmall (by decide +kernel) (by decide)
def v617 : List ℕ := [t292,t294,t90,t306,t91]
theorem b621 : Ban 55 5 v617 := viaSmall (by decide +kernel) (by decide)
def v618 : List ℕ := [t292,t293,t294,t90,t306,t91]
theorem b622 : Ban 55 5 v618 := viaSmall (by decide +kernel) (by decide)
def t307 : ℕ := 0x1602c0580b016000ffe00000000
def v619 : List ℕ := [t292,t307,t294,t90,t91]
theorem b623 : Ban 55 5 v619 := viaSmall (by decide +kernel) (by decide)
def v620 : List ℕ := [t292,t307,t293,t294,t90,t91]
theorem b624 : Ban 55 5 v620 := viaSmall (by decide +kernel) (by decide)
def v621 : List ℕ := [t292,t293,t294,t115,t91]
theorem b625 : Ban 55 5 v621 := viaSmall (by decide +kernel) (by decide)
def v622 : List ℕ := [t292,t293,t294,t115,t90,t91]
theorem b626 : Ban 55 5 v622 := viaSmall (by decide +kernel) (by decide)
def v623 : List ℕ := [t104,t292,t294,t90,t91]
theorem b627 : Ban 55 5 v623 := viaSmall (by decide +kernel) (by decide)
def v624 : List ℕ := [t104,t292,t293,t294,t90,t91]
theorem b628 : Ban 55 5 v624 := viaSmall (by decide +kernel) (by decide)
def t308 : ℕ := 0x3d67acf59eb3d67ffffe00000000
def v625 : List ℕ := [t292,t293,t294,t90,t91,t308]
theorem b629 : Ban 55 5 v625 := viaSmall (by decide +kernel) (by decide)
def t309 : ℕ := 0x560ac1582b05600000000000000
def v626 : List ℕ := [t292,t309,t293,t294,t90,t91]
theorem b630 : Ban 55 5 v626 := viaSmall (by decide +kernel) (by decide)
def v627 : List ℕ := [t292,t294,t90,t107,t91]
theorem b631 : Ban 55 5 v627 := viaSmall (by decide +kernel) (by decide)
def v628 : List ℕ := [t292,t293,t294,t90,t107,t91]
theorem b632 : Ban 55 5 v628 := viaSmall (by decide +kernel) (by decide)
def v629 : List ℕ := [t100,t292,t293,t294,t90,t91]
theorem b633 : Ban 55 5 v629 := viaSmall (by decide +kernel) (by decide)
def t310 : ℕ := 0x3656cad95b2b65000001ffffffff
def v630 : List ℕ := [t292,t293,t294,t90,t310,t91]
theorem b634 : Ban 55 5 v630 := viaSmall (by decide +kernel) (by decide)
def t311 : ℕ := 0x10520a41482905000000000007ff
def v631 : List ℕ := [t292,t293,t311,t294,t90,t91]
theorem b635 : Ban 55 5 v631 := viaSmall (by decide +kernel) (by decide)
def v632 : List ℕ := [t292,t293,t294,t103,t90,t91]
theorem b636 : Ban 55 5 v632 := viaSmall (by decide +kernel) (by decide)
def v633 : List ℕ := [t292,t293,t124,t294,t90,t91]
theorem b637 : Ban 55 5 v633 := viaSmall (by decide +kernel) (by decide)
def v634 : List ℕ := [t292,t293,t294,t90,t105]
theorem b638 : Ban 55 5 v634 := viaSmall (by decide +kernel) (by decide)
def v635 : List ℕ := [t292,t293,t90,t91,t105]
theorem b639 : Ban 55 5 v635 := viaSmall (by decide +kernel) (by decide)
def v636 : List ℕ := [t292,t293,t294,t90,t91,t105]
theorem b640 : Ban 55 5 v636 := viaSmall (by decide +kernel) (by decide)
def v637 : List ℕ := [t106,t292,t293,t90,t91]
theorem b641 : Ban 55 5 v637 := viaSmall (by decide +kernel) (by decide)
def v638 : List ℕ := [t106,t292,t293,t294,t90,t91]
theorem b642 : Ban 55 5 v638 := viaSmall (by decide +kernel) (by decide)
def v639 : List ℕ := [t292,t293,t294,t90,t127]
theorem b643 : Ban 55 5 v639 := viaSmall (by decide +kernel) (by decide)
def v640 : List ℕ := [t292,t293,t294,t90,t127,t91]
theorem b644 : Ban 55 5 v640 := viaSmall (by decide +kernel) (by decide)
def v641 : List ℕ := [t292,t293,t294,t128,t90,t91]
theorem b645 : Ban 55 5 v641 := viaSmall (by decide +kernel) (by decide)
def v642 : List ℕ := [t292,t293,t294,t90,t129]
theorem b646 : Ban 55 5 v642 := viaSmall (by decide +kernel) (by decide)
def v643 : List ℕ := [t292,t293,t294,t91,t129]
theorem b647 : Ban 55 5 v643 := viaSmall (by decide +kernel) (by decide)
def v644 : List ℕ := [t292,t293,t294,t90,t91,t129]
theorem b648 : Ban 55 5 v644 := viaSmall (by decide +kernel) (by decide)
def v645 : List ℕ := [t292,t293,t130,t294,t91]
theorem b649 : Ban 55 5 v645 := viaSmall (by decide +kernel) (by decide)
def v646 : List ℕ := [t292,t293,t130,t294,t90,t91]
theorem b650 : Ban 55 5 v646 := viaSmall (by decide +kernel) (by decide)
def v647 : List ℕ := [t292,t293,t294,t131,t90]
theorem b651 : Ban 55 5 v647 := viaSmall (by decide +kernel) (by decide)
def v648 : List ℕ := [t292,t293,t294,t131,t90,t91]
theorem b652 : Ban 55 5 v648 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b653 : Ban 55 6 v591 := viaBranch (ws := [v592,v593,v594,v595,v596,v597,v598,v599,v600,v601,v602,v603,v604,v605,v606,v607,v608,v609,v610,v611,v612,v613,v614,v615,v616,v617,v618,v619,v620,v621,v622,v623,v624,v625,v626,v627,v628,v629,v630,v631,v632,v633,v634,v635,v636,v637,v638,v639,v640,v641,v642,v643,v644,v645,v646,v647,v648]) (consBan b596 (consBan b597 (consBan b598 (consBan b599 (consBan b600 (consBan b601 (consBan b602 (consBan b603 (consBan b604 (consBan b605 (consBan b606 (consBan b607 (consBan b608 (consBan b609 (consBan b610 (consBan b611 (consBan b612 (consBan b613 (consBan b614 (consBan b615 (consBan b616 (consBan b617 (consBan b618 (consBan b619 (consBan b620 (consBan b621 (consBan b622 (consBan b623 (consBan b624 (consBan b625 (consBan b626 (consBan b627 (consBan b628 (consBan b629 (consBan b630 (consBan b631 (consBan b632 (consBan b633 (consBan b634 (consBan b635 (consBan b636 (consBan b637 (consBan b638 (consBan b639 (consBan b640 (consBan b641 (consBan b642 (consBan b643 (consBan b644 (consBan b645 (consBan b646 (consBan b647 (consBan b648 (consBan b649 (consBan b650 (consBan b651 (consBan b652 (nilBan 55 5)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w38 : Wide 55 6 v591 := viaSub (ws := [v591]) (consBan b653 (nilBan 55 6)) (by decide) (by decide +kernel)
def p127_109 : Projection 220 55 := pick [0,1,4,5,8,10,14,15,17,18,19,80,81,84,85,88,90,94,95,97,98,99,120,121,124,125,128,130,134,135,137,138,139,160,161,164,165,168,170,174,175,177,178,179,180,181,184,185,188,190,194,195,197,198,199] rfl (by decide +kernel) (by decide)
theorem b654 : Ban 220 8 v590 := viaCut p127_109 w38 (by decide) (by decide +kernel) (by decide +kernel)
def v649 : List ℕ := [t0,t141,t1,t2,t3,t4,t5,t6]
theorem b655 : Ban 220 8 v649 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v650 : List ℕ := [t0,t1,t142,t3,t4,t5,t6]
def t312 : ℕ := 0x180300600c0187ff001ffc007ff
def t313 : ℕ := 0x4608c11823046000ffe00000000
def v651 : List ℕ := [t312,t313,t294,t90,t91]
def v652 : List ℕ := [t312,t295,t294,t90,t91]
theorem b656 : Ban 55 5 v652 := viaSmall (by decide +kernel) (by decide)
def v653 : List ℕ := [t313,t295,t294,t90,t91]
theorem b657 : Ban 55 5 v653 := viaSmall (by decide +kernel) (by decide)
def v654 : List ℕ := [t312,t313,t295,t294,t90,t91]
theorem b658 : Ban 55 5 v654 := viaSmall (by decide +kernel) (by decide)
def v655 : List ℕ := [t92,t312,t313,t294,t90,t91]
theorem b659 : Ban 55 5 v655 := viaSmall (by decide +kernel) (by decide)
def t314 : ℕ := 0x11d23a4748e91d7ff001ffffffff
def v656 : List ℕ := [t312,t313,t294,t314,t90,t91]
theorem b660 : Ban 55 5 v656 := viaSmall (by decide +kernel) (by decide)
def t315 : ℕ := 0x180300600c0187ff001ffc00000
def v657 : List ℕ := [t315,t312,t313,t294,t90,t91]
theorem b661 : Ban 55 5 v657 := viaSmall (by decide +kernel) (by decide)
def v658 : List ℕ := [t312,t313,t298,t294,t90,t91]
theorem b662 : Ban 55 5 v658 := viaSmall (by decide +kernel) (by decide)
def v659 : List ℕ := [t120,t312,t313,t294,t90,t91]
theorem b663 : Ban 55 5 v659 := viaSmall (by decide +kernel) (by decide)
def v660 : List ℕ := [t312,t313,t294,t90,t113,t91]
theorem b664 : Ban 55 5 v660 := viaSmall (by decide +kernel) (by decide)
def v661 : List ℕ := [t114,t312,t313,t294,t90,t91]
theorem b665 : Ban 55 5 v661 := viaSmall (by decide +kernel) (by decide)
def v662 : List ℕ := [t312,t313,t294,t123,t90,t91]
theorem b666 : Ban 55 5 v662 := viaSmall (by decide +kernel) (by decide)
def v663 : List ℕ := [t116,t312,t313,t294,t90,t91]
theorem b667 : Ban 55 5 v663 := viaSmall (by decide +kernel) (by decide)
def t316 : ℕ := 0x398730e61cc3987fffffffc007ff
def v664 : List ℕ := [t312,t313,t294,t90,t91,t316]
theorem b668 : Ban 55 5 v664 := viaSmall (by decide +kernel) (by decide)
def t317 : ℕ := 0x180300600c018000001ffc007ff
def v665 : List ℕ := [t317,t312,t313,t294,t90,t91]
theorem b669 : Ban 55 5 v665 := viaSmall (by decide +kernel) (by decide)
def v666 : List ℕ := [t312,t313,t294,t90,t119,t91]
theorem b670 : Ban 55 5 v666 := viaSmall (by decide +kernel) (by decide)
def v667 : List ℕ := [t96,t312,t313,t294,t90,t91]
theorem b671 : Ban 55 5 v667 := viaSmall (by decide +kernel) (by decide)
def t318 : ℕ := 0x14728e51ca3947000ffe003fffff
def v668 : List ℕ := [t312,t313,t318,t90,t91]
theorem b672 : Ban 55 5 v668 := viaSmall (by decide +kernel) (by decide)
def v669 : List ℕ := [t312,t294,t318,t90,t91]
theorem b673 : Ban 55 5 v669 := viaSmall (by decide +kernel) (by decide)
def v670 : List ℕ := [t312,t313,t294,t318,t90,t91]
theorem b674 : Ban 55 5 v670 := viaSmall (by decide +kernel) (by decide)
def t319 : ℕ := 0x4208410821042000ffe00000000
def v671 : List ℕ := [t312,t319,t294,t90,t91]
theorem b675 : Ban 55 5 v671 := viaSmall (by decide +kernel) (by decide)
def v672 : List ℕ := [t312,t319,t313,t294,t90,t91]
theorem b676 : Ban 55 5 v672 := viaSmall (by decide +kernel) (by decide)
def v673 : List ℕ := [t312,t313,t305,t90,t91]
theorem b677 : Ban 55 5 v673 := viaSmall (by decide +kernel) (by decide)
def v674 : List ℕ := [t312,t313,t305,t294,t90,t91]
theorem b678 : Ban 55 5 v674 := viaSmall (by decide +kernel) (by decide)
def v675 : List ℕ := [t312,t112,t313,t294,t90,t91]
theorem b679 : Ban 55 5 v675 := viaSmall (by decide +kernel) (by decide)
def t320 : ℕ := 0x2664cc99933266000ffffffff800
def v676 : List ℕ := [t312,t313,t294,t320,t91]
theorem b680 : Ban 55 5 v676 := viaSmall (by decide +kernel) (by decide)
def v677 : List ℕ := [t312,t294,t90,t320,t91]
theorem b681 : Ban 55 5 v677 := viaSmall (by decide +kernel) (by decide)
def v678 : List ℕ := [t312,t313,t294,t90,t320,t91]
theorem b682 : Ban 55 5 v678 := viaSmall (by decide +kernel) (by decide)
def t321 : ℕ := 0x600c01803006000ffe00000000
def v679 : List ℕ := [t321,t312,t294,t90,t91]
theorem b683 : Ban 55 5 v679 := viaSmall (by decide +kernel) (by decide)
def v680 : List ℕ := [t321,t312,t313,t294,t90,t91]
theorem b684 : Ban 55 5 v680 := viaSmall (by decide +kernel) (by decide)
def v681 : List ℕ := [t312,t313,t294,t115,t91]
theorem b685 : Ban 55 5 v681 := viaSmall (by decide +kernel) (by decide)
def v682 : List ℕ := [t312,t313,t294,t115,t90,t91]
theorem b686 : Ban 55 5 v682 := viaSmall (by decide +kernel) (by decide)
def v683 : List ℕ := [t104,t312,t294,t90,t91]
theorem b687 : Ban 55 5 v683 := viaSmall (by decide +kernel) (by decide)
def v684 : List ℕ := [t104,t312,t313,t294,t90,t91]
theorem b688 : Ban 55 5 v684 := viaSmall (by decide +kernel) (by decide)
def t322 : ℕ := 0x3c678cf19e33c67ffffe00000000
def v685 : List ℕ := [t312,t313,t294,t90,t91,t322]
theorem b689 : Ban 55 5 v685 := viaSmall (by decide +kernel) (by decide)
def t323 : ℕ := 0x4608c1182304600000000000000
def v686 : List ℕ := [t312,t323,t313,t294,t90,t91]
theorem b690 : Ban 55 5 v686 := viaSmall (by decide +kernel) (by decide)
def v687 : List ℕ := [t312,t294,t90,t107,t91]
theorem b691 : Ban 55 5 v687 := viaSmall (by decide +kernel) (by decide)
def v688 : List ℕ := [t312,t313,t294,t90,t107,t91]
theorem b692 : Ban 55 5 v688 := viaSmall (by decide +kernel) (by decide)
def v689 : List ℕ := [t100,t312,t313,t294,t90,t91]
theorem b693 : Ban 55 5 v689 := viaSmall (by decide +kernel) (by decide)
def v690 : List ℕ := [t312,t313,t294,t90,t310,t91]
theorem b694 : Ban 55 5 v690 := viaSmall (by decide +kernel) (by decide)
def v691 : List ℕ := [t312,t313,t311,t294,t90,t91]
theorem b695 : Ban 55 5 v691 := viaSmall (by decide +kernel) (by decide)
def v692 : List ℕ := [t312,t313,t294,t103,t90,t91]
theorem b696 : Ban 55 5 v692 := viaSmall (by decide +kernel) (by decide)
def v693 : List ℕ := [t312,t313,t124,t294,t90,t91]
theorem b697 : Ban 55 5 v693 := viaSmall (by decide +kernel) (by decide)
def v694 : List ℕ := [t312,t313,t294,t90,t105]
theorem b698 : Ban 55 5 v694 := viaSmall (by decide +kernel) (by decide)
def v695 : List ℕ := [t312,t313,t90,t91,t105]
theorem b699 : Ban 55 5 v695 := viaSmall (by decide +kernel) (by decide)
def v696 : List ℕ := [t312,t313,t294,t90,t91,t105]
theorem b700 : Ban 55 5 v696 := viaSmall (by decide +kernel) (by decide)
def v697 : List ℕ := [t106,t312,t313,t90,t91]
theorem b701 : Ban 55 5 v697 := viaSmall (by decide +kernel) (by decide)
def v698 : List ℕ := [t106,t312,t313,t294,t90,t91]
theorem b702 : Ban 55 5 v698 := viaSmall (by decide +kernel) (by decide)
def v699 : List ℕ := [t312,t313,t294,t90,t127]
theorem b703 : Ban 55 5 v699 := viaSmall (by decide +kernel) (by decide)
def v700 : List ℕ := [t312,t313,t294,t90,t127,t91]
theorem b704 : Ban 55 5 v700 := viaSmall (by decide +kernel) (by decide)
def v701 : List ℕ := [t312,t313,t294,t128,t90,t91]
theorem b705 : Ban 55 5 v701 := viaSmall (by decide +kernel) (by decide)
def v702 : List ℕ := [t312,t313,t294,t90,t129]
theorem b706 : Ban 55 5 v702 := viaSmall (by decide +kernel) (by decide)
def v703 : List ℕ := [t312,t313,t294,t91,t129]
theorem b707 : Ban 55 5 v703 := viaSmall (by decide +kernel) (by decide)
def v704 : List ℕ := [t312,t313,t294,t90,t91,t129]
theorem b708 : Ban 55 5 v704 := viaSmall (by decide +kernel) (by decide)
def v705 : List ℕ := [t312,t313,t130,t294,t91]
theorem b709 : Ban 55 5 v705 := viaSmall (by decide +kernel) (by decide)
def v706 : List ℕ := [t312,t313,t130,t294,t90,t91]
theorem b710 : Ban 55 5 v706 := viaSmall (by decide +kernel) (by decide)
def v707 : List ℕ := [t312,t313,t294,t131,t90]
theorem b711 : Ban 55 5 v707 := viaSmall (by decide +kernel) (by decide)
def v708 : List ℕ := [t312,t313,t294,t131,t90,t91]
theorem b712 : Ban 55 5 v708 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b713 : Ban 55 6 v651 := viaBranch (ws := [v652,v653,v654,v655,v656,v657,v658,v659,v660,v661,v662,v663,v664,v665,v666,v667,v668,v669,v670,v671,v672,v673,v674,v675,v676,v677,v678,v679,v680,v681,v682,v683,v684,v685,v686,v687,v688,v689,v690,v691,v692,v693,v694,v695,v696,v697,v698,v699,v700,v701,v702,v703,v704,v705,v706,v707,v708]) (consBan b656 (consBan b657 (consBan b658 (consBan b659 (consBan b660 (consBan b661 (consBan b662 (consBan b663 (consBan b664 (consBan b665 (consBan b666 (consBan b667 (consBan b668 (consBan b669 (consBan b670 (consBan b671 (consBan b672 (consBan b673 (consBan b674 (consBan b675 (consBan b676 (consBan b677 (consBan b678 (consBan b679 (consBan b680 (consBan b681 (consBan b682 (consBan b683 (consBan b684 (consBan b685 (consBan b686 (consBan b687 (consBan b688 (consBan b689 (consBan b690 (consBan b691 (consBan b692 (consBan b693 (consBan b694 (consBan b695 (consBan b696 (consBan b697 (consBan b698 (consBan b699 (consBan b700 (consBan b701 (consBan b702 (consBan b703 (consBan b704 (consBan b705 (consBan b706 (consBan b707 (consBan b708 (consBan b709 (consBan b710 (consBan b711 (consBan b712 (nilBan 55 5)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w39 : Wide 55 6 v651 := viaSub (ws := [v651]) (consBan b713 (nilBan 55 6)) (by decide) (by decide +kernel)
theorem b714 : Ban 220 8 v650 := viaCut p127_109 w39 (by decide) (by decide +kernel) (by decide +kernel)
def v709 : List ℕ := [t0,t1,t142,t2,t3,t4,t5,t6]
theorem b715 : Ban 220 8 v709 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v710 : List ℕ := [t0,t147,t1,t2,t3,t4,t5,t6]
theorem b716 : Ban 220 8 v710 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v711 : List ℕ := [t0,t1,t2,t148,t4,t5,t6]
def t324 : ℕ := 0x2604c09813026000ffe003ff800
def t325 : ℕ := 0x48090120240487ff000003fffff
def t326 : ℕ := 0x10520a41482905000001ffc007ff
def t327 : ℕ := 0x2704e09c138270000001ffc00000
def v712 : List ℕ := [t324,t325,t326,t327,t91]
def v713 : List ℕ := [t100,t324,t325,t326,t327,t91]
theorem b717 : Ban 55 5 v713 := viaSmall (by decide +kernel) (by decide)
def t328 : ℕ := 0x6e0dc1b83706e7ffffe003fffff
def v714 : List ℕ := [t324,t325,t328,t326,t327,t91]
theorem b718 : Ban 55 5 v714 := viaSmall (by decide +kernel) (by decide)
def t329 : ℕ := 0x2604c09813026000ffe00000000
def v715 : List ℕ := [t329,t324,t325,t326,t327,t91]
theorem b719 : Ban 55 5 v715 := viaSmall (by decide +kernel) (by decide)
def v716 : List ℕ := [t324,t110,t325,t326,t327,t91]
theorem b720 : Ban 55 5 v716 := viaSmall (by decide +kernel) (by decide)
def v717 : List ℕ := [t96,t324,t325,t326,t327,t91]
theorem b721 : Ban 55 5 v717 := viaSmall (by decide +kernel) (by decide)
def t330 : ℕ := 0x12724e49c93927000fffffffffff
def v718 : List ℕ := [t324,t325,t330,t327,t91]
theorem b722 : Ban 55 5 v718 := viaSmall (by decide +kernel) (by decide)
def v719 : List ℕ := [t325,t326,t330,t327,t91]
theorem b723 : Ban 55 5 v719 := viaSmall (by decide +kernel) (by decide)
def v720 : List ℕ := [t324,t325,t326,t330,t327,t91]
theorem b724 : Ban 55 5 v720 := viaSmall (by decide +kernel) (by decide)
def t331 : ℕ := 0x2204408811022000ffe003ff800
def v721 : List ℕ := [t331,t325,t326,t327,t91]
theorem b725 : Ban 55 5 v721 := viaSmall (by decide +kernel) (by decide)
def v722 : List ℕ := [t331,t324,t325,t326,t327,t91]
theorem b726 : Ban 55 5 v722 := viaSmall (by decide +kernel) (by decide)
def t332 : ℕ := 0x10120240480901000001ffc007ff
def v723 : List ℕ := [t324,t325,t332,t327,t91]
theorem b727 : Ban 55 5 v723 := viaSmall (by decide +kernel) (by decide)
def v724 : List ℕ := [t324,t325,t332,t326,t327,t91]
theorem b728 : Ban 55 5 v724 := viaSmall (by decide +kernel) (by decide)
def t333 : ℕ := 0x200400801002000000000000000
def v725 : List ℕ := [t333,t324,t325,t326,t327,t91]
theorem b729 : Ban 55 5 v725 := viaSmall (by decide +kernel) (by decide)
def v726 : List ℕ := [t324,t325,t326,t306,t91]
theorem b730 : Ban 55 5 v726 := viaSmall (by decide +kernel) (by decide)
def v727 : List ℕ := [t325,t326,t327,t306,t91]
theorem b731 : Ban 55 5 v727 := viaSmall (by decide +kernel) (by decide)
def v728 : List ℕ := [t324,t325,t326,t327,t306,t91]
theorem b732 : Ban 55 5 v728 := viaSmall (by decide +kernel) (by decide)
def t334 : ℕ := 0x600c01803006000ffe003ff800
def v729 : List ℕ := [t334,t325,t326,t327,t91]
theorem b733 : Ban 55 5 v729 := viaSmall (by decide +kernel) (by decide)
def v730 : List ℕ := [t334,t324,t325,t326,t327,t91]
theorem b734 : Ban 55 5 v730 := viaSmall (by decide +kernel) (by decide)
def t335 : ℕ := 0x2504a094128250000001ffc00000
def v731 : List ℕ := [t324,t325,t326,t335,t91]
theorem b735 : Ban 55 5 v731 := viaSmall (by decide +kernel) (by decide)
def v732 : List ℕ := [t324,t325,t326,t335,t327,t91]
theorem b736 : Ban 55 5 v732 := viaSmall (by decide +kernel) (by decide)
def v733 : List ℕ := [t104,t324,t325,t326,t327,t91]
theorem b737 : Ban 55 5 v733 := viaSmall (by decide +kernel) (by decide)
def t336 : ℕ := 0x3a674ce99d33a67ffffe003ff800
def v734 : List ℕ := [t324,t325,t326,t327,t91,t336]
theorem b738 : Ban 55 5 v734 := viaSmall (by decide +kernel) (by decide)
def t337 : ℕ := 0x2604c09813026000000003ff800
def v735 : List ℕ := [t337,t324,t325,t326,t327,t91]
theorem b739 : Ban 55 5 v735 := viaSmall (by decide +kernel) (by decide)
def v736 : List ℕ := [t324,t325,t326,t327,t107,t91]
theorem b740 : Ban 55 5 v736 := viaSmall (by decide +kernel) (by decide)
def v737 : List ℕ := [t92,t324,t325,t326,t327,t91]
theorem b741 : Ban 55 5 v737 := viaSmall (by decide +kernel) (by decide)
def t338 : ℕ := 0x14d29a534a694d7ff001ffffffff
def v738 : List ℕ := [t324,t325,t326,t338,t327,t91]
theorem b742 : Ban 55 5 v738 := viaSmall (by decide +kernel) (by decide)
def t339 : ℕ := 0x48090120240487ff000003ff800
def v739 : List ℕ := [t324,t339,t325,t326,t327,t91]
theorem b743 : Ban 55 5 v739 := viaSmall (by decide +kernel) (by decide)
def t340 : ℕ := 0x10520a41482905000001ffc00000
def v740 : List ℕ := [t324,t325,t340,t326,t327,t91]
theorem b744 : Ban 55 5 v740 := viaSmall (by decide +kernel) (by decide)
def v741 : List ℕ := [t324,t112,t325,t326,t327,t91]
theorem b745 : Ban 55 5 v741 := viaSmall (by decide +kernel) (by decide)
def v742 : List ℕ := [t324,t325,t326,t113,t91]
theorem b746 : Ban 55 5 v742 := viaSmall (by decide +kernel) (by decide)
def v743 : List ℕ := [t324,t326,t327,t113,t91]
theorem b747 : Ban 55 5 v743 := viaSmall (by decide +kernel) (by decide)
def v744 : List ℕ := [t324,t325,t326,t327,t113,t91]
theorem b748 : Ban 55 5 v744 := viaSmall (by decide +kernel) (by decide)
def t341 : ℕ := 0x8010020040087ff000003fffff
def v745 : List ℕ := [t341,t324,t326,t327,t91]
theorem b749 : Ban 55 5 v745 := viaSmall (by decide +kernel) (by decide)
def v746 : List ℕ := [t341,t324,t325,t326,t327,t91]
theorem b750 : Ban 55 5 v746 := viaSmall (by decide +kernel) (by decide)
def t342 : ℕ := 0x2304608c118230000001ffc00000
def v747 : List ℕ := [t324,t325,t326,t342,t91]
theorem b751 : Ban 55 5 v747 := viaSmall (by decide +kernel) (by decide)
def v748 : List ℕ := [t324,t325,t326,t342,t327,t91]
theorem b752 : Ban 55 5 v748 := viaSmall (by decide +kernel) (by decide)
def v749 : List ℕ := [t116,t324,t325,t326,t327,t91]
theorem b753 : Ban 55 5 v749 := viaSmall (by decide +kernel) (by decide)
def t343 : ℕ := 0x3c8790f21e43c87ffffe003fffff
def v750 : List ℕ := [t324,t325,t326,t327,t91,t343]
theorem b754 : Ban 55 5 v750 := viaSmall (by decide +kernel) (by decide)
def t344 : ℕ := 0x4809012024048000000003fffff
def v751 : List ℕ := [t324,t344,t325,t326,t327,t91]
theorem b755 : Ban 55 5 v751 := viaSmall (by decide +kernel) (by decide)
def v752 : List ℕ := [t324,t325,t326,t327,t119,t91]
theorem b756 : Ban 55 5 v752 := viaSmall (by decide +kernel) (by decide)
def v753 : List ℕ := [t120,t324,t325,t326,t91]
theorem b757 : Ban 55 5 v753 := viaSmall (by decide +kernel) (by decide)
def v754 : List ℕ := [t120,t324,t325,t326,t327,t91]
theorem b758 : Ban 55 5 v754 := viaSmall (by decide +kernel) (by decide)
def t345 : ℕ := 0x3756eadd5bab75000001ffc007ff
def v755 : List ℕ := [t324,t325,t326,t327,t345,t91]
theorem b759 : Ban 55 5 v755 := viaSmall (by decide +kernel) (by decide)
def v756 : List ℕ := [t324,t325,t311,t326,t91]
theorem b760 : Ban 55 5 v756 := viaSmall (by decide +kernel) (by decide)
def v757 : List ℕ := [t324,t325,t311,t326,t327,t91]
theorem b761 : Ban 55 5 v757 := viaSmall (by decide +kernel) (by decide)
def t346 : ℕ := 0x2704e09c13827000000000000000
def v758 : List ℕ := [t324,t325,t326,t346,t327,t91]
theorem b762 : Ban 55 5 v758 := viaSmall (by decide +kernel) (by decide)
def v759 : List ℕ := [t324,t325,t124,t326,t327,t91]
theorem b763 : Ban 55 5 v759 := viaSmall (by decide +kernel) (by decide)
def t347 : ℕ := 0x38570ae15c2b857fffffffc007ff
def v760 : List ℕ := [t324,t325,t326,t327,t347]
theorem b764 : Ban 55 5 v760 := viaSmall (by decide +kernel) (by decide)
def v761 : List ℕ := [t324,t325,t327,t91,t347]
theorem b765 : Ban 55 5 v761 := viaSmall (by decide +kernel) (by decide)
def v762 : List ℕ := [t324,t325,t326,t327,t91,t347]
theorem b766 : Ban 55 5 v762 := viaSmall (by decide +kernel) (by decide)
def t348 : ℕ := 0x500a01402805000001ffc007ff
def v763 : List ℕ := [t348,t324,t325,t327,t91]
theorem b767 : Ban 55 5 v763 := viaSmall (by decide +kernel) (by decide)
def v764 : List ℕ := [t348,t324,t325,t326,t327,t91]
theorem b768 : Ban 55 5 v764 := viaSmall (by decide +kernel) (by decide)
def v765 : List ℕ := [t324,t325,t326,t327,t127]
theorem b769 : Ban 55 5 v765 := viaSmall (by decide +kernel) (by decide)
def v766 : List ℕ := [t324,t325,t326,t327,t127,t91]
theorem b770 : Ban 55 5 v766 := viaSmall (by decide +kernel) (by decide)
def v767 : List ℕ := [t324,t325,t326,t128,t327,t91]
theorem b771 : Ban 55 5 v767 := viaSmall (by decide +kernel) (by decide)
def t349 : ℕ := 0x3f07e0fc1f83f07fffffffc00000
def v768 : List ℕ := [t324,t325,t326,t327,t349]
theorem b772 : Ban 55 5 v768 := viaSmall (by decide +kernel) (by decide)
def v769 : List ℕ := [t324,t325,t326,t91,t349]
theorem b773 : Ban 55 5 v769 := viaSmall (by decide +kernel) (by decide)
def v770 : List ℕ := [t324,t325,t326,t327,t91,t349]
theorem b774 : Ban 55 5 v770 := viaSmall (by decide +kernel) (by decide)
def t350 : ℕ := 0x700e01c038070000001ffc00000
def v771 : List ℕ := [t324,t325,t350,t326,t91]
theorem b775 : Ban 55 5 v771 := viaSmall (by decide +kernel) (by decide)
def v772 : List ℕ := [t324,t325,t350,t326,t327,t91]
theorem b776 : Ban 55 5 v772 := viaSmall (by decide +kernel) (by decide)
def v773 : List ℕ := [t324,t325,t326,t131,t327]
theorem b777 : Ban 55 5 v773 := viaSmall (by decide +kernel) (by decide)
def v774 : List ℕ := [t324,t325,t326,t131,t327,t91]
theorem b778 : Ban 55 5 v774 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b779 : Ban 55 6 v712 := viaBranch (ws := [v713,v714,v715,v716,v717,v718,v719,v720,v721,v722,v723,v724,v725,v726,v727,v728,v729,v730,v731,v732,v733,v734,v735,v736,v737,v738,v739,v740,v741,v742,v743,v744,v745,v746,v747,v748,v749,v750,v751,v752,v753,v754,v755,v756,v757,v758,v759,v760,v761,v762,v763,v764,v765,v766,v767,v768,v769,v770,v771,v772,v773,v774]) (consBan b717 (consBan b718 (consBan b719 (consBan b720 (consBan b721 (consBan b722 (consBan b723 (consBan b724 (consBan b725 (consBan b726 (consBan b727 (consBan b728 (consBan b729 (consBan b730 (consBan b731 (consBan b732 (consBan b733 (consBan b734 (consBan b735 (consBan b736 (consBan b737 (consBan b738 (consBan b739 (consBan b740 (consBan b741 (consBan b742 (consBan b743 (consBan b744 (consBan b745 (consBan b746 (consBan b747 (consBan b748 (consBan b749 (consBan b750 (consBan b751 (consBan b752 (consBan b753 (consBan b754 (consBan b755 (consBan b756 (consBan b757 (consBan b758 (consBan b759 (consBan b760 (consBan b761 (consBan b762 (consBan b763 (consBan b764 (consBan b765 (consBan b766 (consBan b767 (consBan b768 (consBan b769 (consBan b770 (consBan b771 (consBan b772 (consBan b773 (consBan b774 (consBan b775 (consBan b776 (consBan b777 (consBan b778 (nilBan 55 5))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w40 : Wide 55 6 v712 := viaSub (ws := [v712]) (consBan b779 (nilBan 55 6)) (by decide) (by decide +kernel)
def p127_117 : Projection 220 55 := pick [20,21,24,25,32,34,35,36,37,38,39,60,61,64,65,72,74,75,76,77,78,79,80,81,84,85,92,94,95,96,97,98,99,160,161,164,165,172,174,175,176,177,178,179,200,201,204,205,212,214,215,216,217,218,219] rfl (by decide +kernel) (by decide)
theorem b780 : Ban 220 8 v711 := viaCut p127_117 w40 (by decide) (by decide +kernel) (by decide +kernel)
def v775 : List ℕ := [t0,t2,t3,t148,t4,t5,t6]
def t351 : ℕ := 0xbc2f0bc2f0bc2f0ffc00003fffffff
def v776 : List ℕ := [t13,t14,t16,t351,t17]
def v777 : List ℕ := [t18,t13,t14,t16,t351,t17]
theorem b781 : Ban 60 5 v777 := viaSmall (by decide +kernel) (by decide)
def v778 : List ℕ := [t13,t19,t16,t351,t17]
theorem b782 : Ban 60 5 v778 := viaSmall (by decide +kernel) (by decide)
def v779 : List ℕ := [t14,t19,t16,t351,t17]
theorem b783 : Ban 60 5 v779 := viaSmall (by decide +kernel) (by decide)
def v780 : List ℕ := [t13,t14,t19,t16,t351,t17]
theorem b784 : Ban 60 5 v780 := viaSmall (by decide +kernel) (by decide)
def v781 : List ℕ := [t20,t14,t16,t351,t17]
theorem b785 : Ban 60 5 v781 := viaSmall (by decide +kernel) (by decide)
def v782 : List ℕ := [t20,t13,t14,t16,t351,t17]
theorem b786 : Ban 60 5 v782 := viaSmall (by decide +kernel) (by decide)
def v783 : List ℕ := [t13,t21,t16,t351,t17]
theorem b787 : Ban 60 5 v783 := viaSmall (by decide +kernel) (by decide)
def v784 : List ℕ := [t13,t21,t14,t16,t351,t17]
theorem b788 : Ban 60 5 v784 := viaSmall (by decide +kernel) (by decide)
def v785 : List ℕ := [t26,t13,t14,t16,t351,t17]
theorem b789 : Ban 60 5 v785 := viaSmall (by decide +kernel) (by decide)
def v786 : List ℕ := [t13,t14,t27,t351,t17]
theorem b790 : Ban 60 5 v786 := viaSmall (by decide +kernel) (by decide)
def v787 : List ℕ := [t13,t14,t16,t27,t351,t17]
theorem b791 : Ban 60 5 v787 := viaSmall (by decide +kernel) (by decide)
def v788 : List ℕ := [t28,t13,t14,t16,t351,t17]
theorem b792 : Ban 60 5 v788 := viaSmall (by decide +kernel) (by decide)
def v789 : List ℕ := [t13,t14,t29,t351,t17]
theorem b793 : Ban 60 5 v789 := viaSmall (by decide +kernel) (by decide)
def v790 : List ℕ := [t13,t14,t29,t16,t351,t17]
theorem b794 : Ban 60 5 v790 := viaSmall (by decide +kernel) (by decide)
def v791 : List ℕ := [t151,t13,t14,t16,t351,t17]
theorem b795 : Ban 60 5 v791 := viaSmall (by decide +kernel) (by decide)
def t352 : ℕ := 0xbeafabeafabeafaffc00ffffffffff
def v792 : List ℕ := [t13,t14,t16,t351,t352,t17]
theorem b796 : Ban 60 5 v792 := viaSmall (by decide +kernel) (by decide)
def t353 : ℕ := 0x280a0280a0280a00000ffc0000000
def v793 : List ℕ := [t353,t13,t14,t16,t351,t17]
theorem b797 : Ban 60 5 v793 := viaSmall (by decide +kernel) (by decide)
def t354 : ℕ := 0xbc2f0bc2f0bc2f0ffc00003ff00000
def v794 : List ℕ := [t13,t14,t16,t354,t351,t17]
theorem b798 : Ban 60 5 v794 := viaSmall (by decide +kernel) (by decide)
def v795 : List ℕ := [t30,t13,t14,t16,t351,t17]
theorem b799 : Ban 60 5 v795 := viaSmall (by decide +kernel) (by decide)
def v796 : List ℕ := [t13,t14,t16,t351,t17,t31]
theorem b800 : Ban 60 5 v796 := viaSmall (by decide +kernel) (by decide)
def v797 : List ℕ := [t32,t13,t14,t16,t351,t17]
theorem b801 : Ban 60 5 v797 := viaSmall (by decide +kernel) (by decide)
def v798 : List ℕ := [t13,t14,t16,t351,t33,t17]
theorem b802 : Ban 60 5 v798 := viaSmall (by decide +kernel) (by decide)
def v799 : List ℕ := [t35,t13,t14,t16,t351,t17]
theorem b803 : Ban 60 5 v799 := viaSmall (by decide +kernel) (by decide)
def v800 : List ℕ := [t13,t14,t16,t36,t351,t17]
theorem b804 : Ban 60 5 v800 := viaSmall (by decide +kernel) (by decide)
def v801 : List ℕ := [t13,t37,t14,t16,t351,t17]
theorem b805 : Ban 60 5 v801 := viaSmall (by decide +kernel) (by decide)
def v802 : List ℕ := [t13,t14,t38,t16,t351,t17]
theorem b806 : Ban 60 5 v802 := viaSmall (by decide +kernel) (by decide)
def t355 : ℕ := 0x8020080200802000000003ff00000
def v803 : List ℕ := [t13,t355,t14,t16,t351,t17]
theorem b807 : Ban 60 5 v803 := viaSmall (by decide +kernel) (by decide)
def v804 : List ℕ := [t13,t14,t16,t351,t44,t17]
theorem b808 : Ban 60 5 v804 := viaSmall (by decide +kernel) (by decide)
def t356 : ℕ := 0x300c0300c0300c003ff0000000000
def v805 : List ℕ := [t13,t356,t14,t16,t351,t17]
theorem b809 : Ban 60 5 v805 := viaSmall (by decide +kernel) (by decide)
def t357 : ℕ := 0xb42d0b42d0b42d0ffc0000000fffff
def v806 : List ℕ := [t13,t14,t16,t357,t17]
theorem b810 : Ban 60 5 v806 := viaSmall (by decide +kernel) (by decide)
def v807 : List ℕ := [t13,t14,t16,t357,t351,t17]
theorem b811 : Ban 60 5 v807 := viaSmall (by decide +kernel) (by decide)
def v808 : List ℕ := [t39,t13,t14,t16,t351,t17]
theorem b812 : Ban 60 5 v808 := viaSmall (by decide +kernel) (by decide)
def v809 : List ℕ := [t13,t14,t16,t351,t17,t40]
theorem b813 : Ban 60 5 v809 := viaSmall (by decide +kernel) (by decide)
def v810 : List ℕ := [t13,t41,t14,t16,t351,t17]
theorem b814 : Ban 60 5 v810 := viaSmall (by decide +kernel) (by decide)
def v811 : List ℕ := [t13,t14,t16,t351,t42,t17]
theorem b815 : Ban 60 5 v811 := viaSmall (by decide +kernel) (by decide)
def t358 : ℕ := 0xc0300c0300c030ffc0000000003ff
def v812 : List ℕ := [t13,t14,t358,t16,t17]
theorem b816 : Ban 60 5 v812 := viaSmall (by decide +kernel) (by decide)
def v813 : List ℕ := [t13,t14,t358,t351,t17]
theorem b817 : Ban 60 5 v813 := viaSmall (by decide +kernel) (by decide)
def v814 : List ℕ := [t13,t14,t358,t16,t351,t17]
theorem b818 : Ban 60 5 v814 := viaSmall (by decide +kernel) (by decide)
def v815 : List ℕ := [t13,t14,t51,t16,t351,t17]
theorem b819 : Ban 60 5 v815 := viaSmall (by decide +kernel) (by decide)
def v816 : List ℕ := [t13,t14,t16,t351,t52]
theorem b820 : Ban 60 5 v816 := viaSmall (by decide +kernel) (by decide)
def v817 : List ℕ := [t13,t14,t16,t351,t17,t52]
theorem b821 : Ban 60 5 v817 := viaSmall (by decide +kernel) (by decide)
def v818 : List ℕ := [t13,t14,t53,t16,t351,t17]
theorem b822 : Ban 60 5 v818 := viaSmall (by decide +kernel) (by decide)
def v819 : List ℕ := [t13,t14,t54,t16,t351]
theorem b823 : Ban 60 5 v819 := viaSmall (by decide +kernel) (by decide)
def v820 : List ℕ := [t13,t14,t54,t16,t351,t17]
theorem b824 : Ban 60 5 v820 := viaSmall (by decide +kernel) (by decide)
def t359 : ℕ := 0x802008020080200ffc000000000000
def v821 : List ℕ := [t13,t14,t359,t16,t351,t17]
theorem b825 : Ban 60 5 v821 := viaSmall (by decide +kernel) (by decide)
def t360 : ℕ := 0xfc3f0fc3f0fc3f0fffffffffffffff
def v822 : List ℕ := [t13,t14,t16,t351,t17,t360]
theorem b826 : Ban 60 5 v822 := viaSmall (by decide +kernel) (by decide)
def t361 : ℕ := 0x3c0f03c0f03c0f000000003fffffff
def v823 : List ℕ := [t13,t14,t361,t16,t351,t17]
theorem b827 : Ban 60 5 v823 := viaSmall (by decide +kernel) (by decide)
def t362 : ℕ := 0x401004010040100003ffffc0000000
def v824 : List ℕ := [t13,t14,t362,t16,t351,t17]
theorem b828 : Ban 60 5 v824 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b829 : Ban 60 6 v776 := viaBranch (ws := [v777,v778,v779,v780,v781,v782,v783,v784,v785,v786,v787,v788,v789,v790,v791,v792,v793,v794,v795,v796,v797,v798,v799,v800,v801,v802,v803,v37,v804,v805,v806,v807,v808,v809,v810,v811,v812,v813,v814,v815,v816,v817,v818,v819,v820,v821,v822,v823,v824]) (consBan b781 (consBan b782 (consBan b783 (consBan b784 (consBan b785 (consBan b786 (consBan b787 (consBan b788 (consBan b789 (consBan b790 (consBan b791 (consBan b792 (consBan b793 (consBan b794 (consBan b795 (consBan b796 (consBan b797 (consBan b798 (consBan b799 (consBan b800 (consBan b801 (consBan b802 (consBan b803 (consBan b804 (consBan b805 (consBan b806 (consBan b807 (consBan b34 (consBan b808 (consBan b809 (consBan b810 (consBan b811 (consBan b812 (consBan b813 (consBan b814 (consBan b815 (consBan b816 (consBan b817 (consBan b818 (consBan b819 (consBan b820 (consBan b821 (consBan b822 (consBan b823 (consBan b824 (consBan b825 (consBan b826 (consBan b827 (consBan b828 (nilBan 60 5)))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w41 : Wide 60 6 v776 := viaSub (ws := [v776]) (consBan b829 (nilBan 60 6)) (by decide) (by decide +kernel)
theorem b830 : Ban 220 8 v775 := viaCut p127_59 w41 (by decide) (by decide +kernel) (by decide +kernel)
def v825 : List ℕ := [t0,t1,t2,t3,t148,t4,t5,t6]
def v826 : List ℕ := [t312,t293,t294,t90,t91]
def v827 : List ℕ := [t108,t312,t293,t294,t90,t91]
theorem b831 : Ban 55 5 v827 := viaSmall (by decide +kernel) (by decide)
def v828 : List ℕ := [t312,t293,t295,t294,t90,t91]
theorem b832 : Ban 55 5 v828 := viaSmall (by decide +kernel) (by decide)
theorem b833 : Ban 55 5 v591 := viaSmall (by decide +kernel) (by decide)
def v829 : List ℕ := [t292,t312,t293,t294,t90,t91]
theorem b834 : Ban 55 5 v829 := viaSmall (by decide +kernel) (by decide)
theorem b835 : Ban 55 5 v651 := viaSmall (by decide +kernel) (by decide)
def v830 : List ℕ := [t312,t313,t293,t294,t90,t91]
theorem b836 : Ban 55 5 v830 := viaSmall (by decide +kernel) (by decide)
def v831 : List ℕ := [t92,t312,t293,t294,t90,t91]
theorem b837 : Ban 55 5 v831 := viaSmall (by decide +kernel) (by decide)
def v832 : List ℕ := [t312,t293,t294,t314,t90,t91]
theorem b838 : Ban 55 5 v832 := viaSmall (by decide +kernel) (by decide)
def v833 : List ℕ := [t315,t312,t293,t294,t90,t91]
theorem b839 : Ban 55 5 v833 := viaSmall (by decide +kernel) (by decide)
def v834 : List ℕ := [t312,t293,t298,t294,t90,t91]
theorem b840 : Ban 55 5 v834 := viaSmall (by decide +kernel) (by decide)
def v835 : List ℕ := [t120,t312,t293,t294,t90,t91]
theorem b841 : Ban 55 5 v835 := viaSmall (by decide +kernel) (by decide)
def v836 : List ℕ := [t312,t293,t294,t90,t113,t91]
theorem b842 : Ban 55 5 v836 := viaSmall (by decide +kernel) (by decide)
def v837 : List ℕ := [t114,t312,t293,t294,t90,t91]
theorem b843 : Ban 55 5 v837 := viaSmall (by decide +kernel) (by decide)
def v838 : List ℕ := [t312,t293,t294,t123,t90,t91]
theorem b844 : Ban 55 5 v838 := viaSmall (by decide +kernel) (by decide)
def v839 : List ℕ := [t116,t312,t293,t294,t90,t91]
theorem b845 : Ban 55 5 v839 := viaSmall (by decide +kernel) (by decide)
def v840 : List ℕ := [t312,t293,t294,t90,t91,t316]
theorem b846 : Ban 55 5 v840 := viaSmall (by decide +kernel) (by decide)
def v841 : List ℕ := [t317,t312,t293,t294,t90,t91]
theorem b847 : Ban 55 5 v841 := viaSmall (by decide +kernel) (by decide)
def v842 : List ℕ := [t312,t293,t294,t90,t119,t91]
theorem b848 : Ban 55 5 v842 := viaSmall (by decide +kernel) (by decide)
def v843 : List ℕ := [t96,t312,t293,t294,t90,t91]
theorem b849 : Ban 55 5 v843 := viaSmall (by decide +kernel) (by decide)
def v844 : List ℕ := [t312,t293,t303,t90,t91]
theorem b850 : Ban 55 5 v844 := viaSmall (by decide +kernel) (by decide)
def v845 : List ℕ := [t312,t294,t303,t90,t91]
theorem b851 : Ban 55 5 v845 := viaSmall (by decide +kernel) (by decide)
def v846 : List ℕ := [t312,t293,t294,t303,t90,t91]
theorem b852 : Ban 55 5 v846 := viaSmall (by decide +kernel) (by decide)
def v847 : List ℕ := [t312,t304,t294,t90,t91]
theorem b853 : Ban 55 5 v847 := viaSmall (by decide +kernel) (by decide)
def v848 : List ℕ := [t312,t304,t293,t294,t90,t91]
theorem b854 : Ban 55 5 v848 := viaSmall (by decide +kernel) (by decide)
def v849 : List ℕ := [t312,t293,t305,t90,t91]
theorem b855 : Ban 55 5 v849 := viaSmall (by decide +kernel) (by decide)
def v850 : List ℕ := [t312,t293,t305,t294,t90,t91]
theorem b856 : Ban 55 5 v850 := viaSmall (by decide +kernel) (by decide)
def v851 : List ℕ := [t312,t112,t293,t294,t90,t91]
theorem b857 : Ban 55 5 v851 := viaSmall (by decide +kernel) (by decide)
def v852 : List ℕ := [t312,t293,t294,t306,t91]
theorem b858 : Ban 55 5 v852 := viaSmall (by decide +kernel) (by decide)
def v853 : List ℕ := [t312,t294,t90,t306,t91]
theorem b859 : Ban 55 5 v853 := viaSmall (by decide +kernel) (by decide)
def v854 : List ℕ := [t312,t293,t294,t90,t306,t91]
theorem b860 : Ban 55 5 v854 := viaSmall (by decide +kernel) (by decide)
def v855 : List ℕ := [t307,t312,t294,t90,t91]
theorem b861 : Ban 55 5 v855 := viaSmall (by decide +kernel) (by decide)
def v856 : List ℕ := [t307,t312,t293,t294,t90,t91]
theorem b862 : Ban 55 5 v856 := viaSmall (by decide +kernel) (by decide)
def v857 : List ℕ := [t312,t293,t294,t115,t91]
theorem b863 : Ban 55 5 v857 := viaSmall (by decide +kernel) (by decide)
def v858 : List ℕ := [t312,t293,t294,t115,t90,t91]
theorem b864 : Ban 55 5 v858 := viaSmall (by decide +kernel) (by decide)
def v859 : List ℕ := [t104,t312,t293,t294,t90,t91]
theorem b865 : Ban 55 5 v859 := viaSmall (by decide +kernel) (by decide)
def v860 : List ℕ := [t312,t293,t294,t90,t91,t308]
theorem b866 : Ban 55 5 v860 := viaSmall (by decide +kernel) (by decide)
def v861 : List ℕ := [t312,t309,t293,t294,t90,t91]
theorem b867 : Ban 55 5 v861 := viaSmall (by decide +kernel) (by decide)
def v862 : List ℕ := [t312,t293,t294,t90,t107,t91]
theorem b868 : Ban 55 5 v862 := viaSmall (by decide +kernel) (by decide)
def v863 : List ℕ := [t100,t312,t293,t294,t90,t91]
theorem b869 : Ban 55 5 v863 := viaSmall (by decide +kernel) (by decide)
def v864 : List ℕ := [t312,t293,t294,t90,t310,t91]
theorem b870 : Ban 55 5 v864 := viaSmall (by decide +kernel) (by decide)
def v865 : List ℕ := [t312,t293,t311,t294,t90,t91]
theorem b871 : Ban 55 5 v865 := viaSmall (by decide +kernel) (by decide)
def v866 : List ℕ := [t312,t293,t294,t103,t90,t91]
theorem b872 : Ban 55 5 v866 := viaSmall (by decide +kernel) (by decide)
def v867 : List ℕ := [t312,t293,t124,t294,t90,t91]
theorem b873 : Ban 55 5 v867 := viaSmall (by decide +kernel) (by decide)
def v868 : List ℕ := [t312,t293,t294,t90,t105]
theorem b874 : Ban 55 5 v868 := viaSmall (by decide +kernel) (by decide)
def v869 : List ℕ := [t312,t293,t90,t91,t105]
theorem b875 : Ban 55 5 v869 := viaSmall (by decide +kernel) (by decide)
def v870 : List ℕ := [t312,t293,t294,t90,t91,t105]
theorem b876 : Ban 55 5 v870 := viaSmall (by decide +kernel) (by decide)
def v871 : List ℕ := [t106,t312,t293,t90,t91]
theorem b877 : Ban 55 5 v871 := viaSmall (by decide +kernel) (by decide)
def v872 : List ℕ := [t106,t312,t293,t294,t90,t91]
theorem b878 : Ban 55 5 v872 := viaSmall (by decide +kernel) (by decide)
def v873 : List ℕ := [t312,t293,t294,t90,t127]
theorem b879 : Ban 55 5 v873 := viaSmall (by decide +kernel) (by decide)
def v874 : List ℕ := [t312,t293,t294,t90,t127,t91]
theorem b880 : Ban 55 5 v874 := viaSmall (by decide +kernel) (by decide)
def v875 : List ℕ := [t312,t293,t294,t128,t90,t91]
theorem b881 : Ban 55 5 v875 := viaSmall (by decide +kernel) (by decide)
def v876 : List ℕ := [t312,t293,t294,t90,t129]
theorem b882 : Ban 55 5 v876 := viaSmall (by decide +kernel) (by decide)
def v877 : List ℕ := [t312,t293,t294,t91,t129]
theorem b883 : Ban 55 5 v877 := viaSmall (by decide +kernel) (by decide)
def v878 : List ℕ := [t312,t293,t294,t90,t91,t129]
theorem b884 : Ban 55 5 v878 := viaSmall (by decide +kernel) (by decide)
def v879 : List ℕ := [t312,t293,t130,t294,t91]
theorem b885 : Ban 55 5 v879 := viaSmall (by decide +kernel) (by decide)
def v880 : List ℕ := [t312,t293,t130,t294,t90,t91]
theorem b886 : Ban 55 5 v880 := viaSmall (by decide +kernel) (by decide)
def v881 : List ℕ := [t312,t293,t294,t131,t90]
theorem b887 : Ban 55 5 v881 := viaSmall (by decide +kernel) (by decide)
def v882 : List ℕ := [t312,t293,t294,t131,t90,t91]
theorem b888 : Ban 55 5 v882 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b889 : Ban 55 6 v826 := viaBranch (ws := [v827,v652,v593,v828,v591,v829,v651,v830,v831,v832,v833,v834,v835,v836,v837,v838,v839,v840,v841,v842,v843,v844,v845,v846,v847,v848,v849,v850,v851,v852,v853,v854,v855,v856,v857,v858,v683,v859,v860,v861,v687,v862,v863,v864,v865,v866,v867,v868,v869,v870,v871,v872,v873,v874,v875,v876,v877,v878,v879,v880,v881,v882]) (consBan b831 (consBan b656 (consBan b597 (consBan b832 (consBan b833 (consBan b834 (consBan b835 (consBan b836 (consBan b837 (consBan b838 (consBan b839 (consBan b840 (consBan b841 (consBan b842 (consBan b843 (consBan b844 (consBan b845 (consBan b846 (consBan b847 (consBan b848 (consBan b849 (consBan b850 (consBan b851 (consBan b852 (consBan b853 (consBan b854 (consBan b855 (consBan b856 (consBan b857 (consBan b858 (consBan b859 (consBan b860 (consBan b861 (consBan b862 (consBan b863 (consBan b864 (consBan b687 (consBan b865 (consBan b866 (consBan b867 (consBan b691 (consBan b868 (consBan b869 (consBan b870 (consBan b871 (consBan b872 (consBan b873 (consBan b874 (consBan b875 (consBan b876 (consBan b877 (consBan b878 (consBan b879 (consBan b880 (consBan b881 (consBan b882 (consBan b883 (consBan b884 (consBan b885 (consBan b886 (consBan b887 (consBan b888 (nilBan 55 5))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w42 : Wide 55 6 v826 := viaSub (ws := [v826]) (consBan b889 (nilBan 55 6)) (by decide) (by decide +kernel)
theorem b890 : Ban 220 8 v825 := viaCut p127_109 w42 (by decide) (by decide +kernel) (by decide +kernel)
def v883 : List ℕ := [t0,t149,t2,t3,t4,t5,t6]
def v884 : List ℕ := [t92,t87,t114,t89,t90,t91]
theorem b891 : Ban 55 5 v884 := viaSmall (by decide +kernel) (by decide)
def t363 : ℕ := 0x1d03a0740e81d7ffffe003fffff
def v885 : List ℕ := [t87,t114,t363,t89,t90,t91]
theorem b892 : Ban 55 5 v885 := viaSmall (by decide +kernel) (by decide)
def v886 : List ℕ := [t94,t87,t114,t89,t90,t91]
theorem b893 : Ban 55 5 v886 := viaSmall (by decide +kernel) (by decide)
def t364 : ℕ := 0x180300600c0187ff00000000000
def v887 : List ℕ := [t87,t364,t114,t89,t90,t91]
theorem b894 : Ban 55 5 v887 := viaSmall (by decide +kernel) (by decide)
def v888 : List ℕ := [t96,t87,t114,t89,t90,t91]
theorem b895 : Ban 55 5 v888 := viaSmall (by decide +kernel) (by decide)
def v889 : List ℕ := [t87,t114,t97,t90,t91]
theorem b896 : Ban 55 5 v889 := viaSmall (by decide +kernel) (by decide)
def v890 : List ℕ := [t114,t89,t97,t90,t91]
theorem b897 : Ban 55 5 v890 := viaSmall (by decide +kernel) (by decide)
def v891 : List ℕ := [t87,t114,t89,t97,t90,t91]
theorem b898 : Ban 55 5 v891 := viaSmall (by decide +kernel) (by decide)
def v892 : List ℕ := [t98,t114,t89,t90,t91]
theorem b899 : Ban 55 5 v892 := viaSmall (by decide +kernel) (by decide)
def v893 : List ℕ := [t98,t87,t114,t89,t90,t91]
theorem b900 : Ban 55 5 v893 := viaSmall (by decide +kernel) (by decide)
def v894 : List ℕ := [t87,t114,t99,t90,t91]
theorem b901 : Ban 55 5 v894 := viaSmall (by decide +kernel) (by decide)
def v895 : List ℕ := [t87,t114,t99,t89,t90,t91]
theorem b902 : Ban 55 5 v895 := viaSmall (by decide +kernel) (by decide)
def v896 : List ℕ := [t100,t87,t114,t89,t90,t91]
theorem b903 : Ban 55 5 v896 := viaSmall (by decide +kernel) (by decide)
def v897 : List ℕ := [t87,t114,t89,t90,t101,t91]
theorem b904 : Ban 55 5 v897 := viaSmall (by decide +kernel) (by decide)
def v898 : List ℕ := [t102,t87,t114,t89,t90,t91]
theorem b905 : Ban 55 5 v898 := viaSmall (by decide +kernel) (by decide)
def v899 : List ℕ := [t87,t114,t89,t103,t90,t91]
theorem b906 : Ban 55 5 v899 := viaSmall (by decide +kernel) (by decide)
def v900 : List ℕ := [t104,t87,t114,t89,t90,t91]
theorem b907 : Ban 55 5 v900 := viaSmall (by decide +kernel) (by decide)
def v901 : List ℕ := [t87,t114,t89,t90,t91,t105]
theorem b908 : Ban 55 5 v901 := viaSmall (by decide +kernel) (by decide)
def v902 : List ℕ := [t106,t87,t114,t89,t90,t91]
theorem b909 : Ban 55 5 v902 := viaSmall (by decide +kernel) (by decide)
def v903 : List ℕ := [t87,t114,t89,t90,t107,t91]
theorem b910 : Ban 55 5 v903 := viaSmall (by decide +kernel) (by decide)
def v904 : List ℕ := [t87,t108,t114,t89,t90,t91]
theorem b911 : Ban 55 5 v904 := viaSmall (by decide +kernel) (by decide)
def t365 : ℕ := 0x11e23c4788f11e7ff001ffc007ff
def v905 : List ℕ := [t87,t114,t365,t90,t91]
theorem b912 : Ban 55 5 v905 := viaSmall (by decide +kernel) (by decide)
def v906 : List ℕ := [t87,t89,t365,t90,t91]
theorem b913 : Ban 55 5 v906 := viaSmall (by decide +kernel) (by decide)
def v907 : List ℕ := [t87,t114,t89,t365,t90,t91]
theorem b914 : Ban 55 5 v907 := viaSmall (by decide +kernel) (by decide)
def v908 : List ℕ := [t87,t300,t89,t90,t91]
theorem b915 : Ban 55 5 v908 := viaSmall (by decide +kernel) (by decide)
def v909 : List ℕ := [t87,t300,t114,t89,t90,t91]
theorem b916 : Ban 55 5 v909 := viaSmall (by decide +kernel) (by decide)
def v910 : List ℕ := [t87,t114,t111,t90,t91]
theorem b917 : Ban 55 5 v910 := viaSmall (by decide +kernel) (by decide)
def v911 : List ℕ := [t87,t114,t111,t89,t90,t91]
theorem b918 : Ban 55 5 v911 := viaSmall (by decide +kernel) (by decide)
def v912 : List ℕ := [t87,t114,t89,t113,t91]
theorem b919 : Ban 55 5 v912 := viaSmall (by decide +kernel) (by decide)
def v913 : List ℕ := [t87,t114,t89,t90,t113,t91]
theorem b920 : Ban 55 5 v913 := viaSmall (by decide +kernel) (by decide)
def v914 : List ℕ := [t116,t87,t114,t89,t90,t91]
theorem b921 : Ban 55 5 v914 := viaSmall (by decide +kernel) (by decide)
def t366 : ℕ := 0x398730e61cc3987ffffe000007ff
def v915 : List ℕ := [t87,t114,t89,t90,t91,t366]
theorem b922 : Ban 55 5 v915 := viaSmall (by decide +kernel) (by decide)
def t367 : ℕ := 0x180300600c018000000000007ff
def v916 : List ℕ := [t87,t367,t114,t89,t90,t91]
theorem b923 : Ban 55 5 v916 := viaSmall (by decide +kernel) (by decide)
def v917 : List ℕ := [t87,t114,t89,t90,t119,t91]
theorem b924 : Ban 55 5 v917 := viaSmall (by decide +kernel) (by decide)
def v918 : List ℕ := [t120,t87,t114,t90,t91]
def p61_41 : Projection 55 12 := pick [0,1,4,8,33,34,37,41,44,45,48,52] rfl (by decide +kernel) (by decide)
theorem b925 : Ban 55 5 v918 := viaCut p61_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v919 : List ℕ := [t120,t87,t114,t89,t90,t91]
theorem b926 : Ban 55 5 v919 := viaSmall (by decide +kernel) (by decide)
def v920 : List ℕ := [t87,t114,t89,t90,t121,t91]
theorem b927 : Ban 55 5 v920 := viaSmall (by decide +kernel) (by decide)
def v921 : List ℕ := [t87,t114,t122,t89,t90,t91]
theorem b928 : Ban 55 5 v921 := viaSmall (by decide +kernel) (by decide)
def v922 : List ℕ := [t87,t114,t123,t90,t91]
theorem b929 : Ban 55 5 v922 := viaSmall (by decide +kernel) (by decide)
def v923 : List ℕ := [t87,t114,t89,t123,t90,t91]
theorem b930 : Ban 55 5 v923 := viaSmall (by decide +kernel) (by decide)
def v924 : List ℕ := [t87,t114,t124,t89,t90,t91]
theorem b931 : Ban 55 5 v924 := viaSmall (by decide +kernel) (by decide)
def v925 : List ℕ := [t87,t114,t89,t90,t125]
theorem b932 : Ban 55 5 v925 := viaSmall (by decide +kernel) (by decide)
def v926 : List ℕ := [t87,t114,t90,t91,t125]
theorem b933 : Ban 55 5 v926 := viaSmall (by decide +kernel) (by decide)
def v927 : List ℕ := [t87,t114,t89,t90,t91,t125]
theorem b934 : Ban 55 5 v927 := viaSmall (by decide +kernel) (by decide)
def v928 : List ℕ := [t87,t126,t114,t90,t91]
theorem b935 : Ban 55 5 v928 := viaSmall (by decide +kernel) (by decide)
def v929 : List ℕ := [t87,t126,t114,t89,t90,t91]
theorem b936 : Ban 55 5 v929 := viaSmall (by decide +kernel) (by decide)
def v930 : List ℕ := [t87,t114,t89,t90,t127]
theorem b937 : Ban 55 5 v930 := viaSmall (by decide +kernel) (by decide)
def v931 : List ℕ := [t87,t114,t89,t90,t127,t91]
theorem b938 : Ban 55 5 v931 := viaSmall (by decide +kernel) (by decide)
def v932 : List ℕ := [t87,t114,t89,t128,t90,t91]
theorem b939 : Ban 55 5 v932 := viaSmall (by decide +kernel) (by decide)
def v933 : List ℕ := [t87,t114,t89,t90,t129]
theorem b940 : Ban 55 5 v933 := viaCut p61_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v934 : List ℕ := [t87,t114,t89,t91,t129]
theorem b941 : Ban 55 5 v934 := viaSmall (by decide +kernel) (by decide)
def v935 : List ℕ := [t87,t114,t89,t90,t91,t129]
theorem b942 : Ban 55 5 v935 := viaSmall (by decide +kernel) (by decide)
def v936 : List ℕ := [t87,t114,t130,t89,t91]
theorem b943 : Ban 55 5 v936 := viaSmall (by decide +kernel) (by decide)
def v937 : List ℕ := [t87,t114,t130,t89,t90,t91]
theorem b944 : Ban 55 5 v937 := viaSmall (by decide +kernel) (by decide)
def v938 : List ℕ := [t87,t114,t89,t131,t90]
theorem b945 : Ban 55 5 v938 := viaSmall (by decide +kernel) (by decide)
def v939 : List ℕ := [t87,t114,t89,t131,t90,t91]
theorem b946 : Ban 55 5 v939 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b947 : Ban 55 6 v141 := viaBranch (ws := [v884,v885,v886,v887,v888,v889,v890,v891,v892,v893,v894,v895,v896,v897,v898,v899,v900,v901,v902,v903,v904,v905,v906,v907,v908,v909,v910,v911,v912,v139,v913,v914,v915,v916,v917,v918,v919,v920,v921,v922,v923,v924,v925,v926,v927,v928,v929,v930,v931,v932,v933,v934,v935,v936,v937,v938,v939]) (consBan b891 (consBan b892 (consBan b893 (consBan b894 (consBan b895 (consBan b896 (consBan b897 (consBan b898 (consBan b899 (consBan b900 (consBan b901 (consBan b902 (consBan b903 (consBan b904 (consBan b905 (consBan b906 (consBan b907 (consBan b908 (consBan b909 (consBan b910 (consBan b911 (consBan b912 (consBan b913 (consBan b914 (consBan b915 (consBan b916 (consBan b917 (consBan b918 (consBan b919 (consBan b136 (consBan b920 (consBan b921 (consBan b922 (consBan b923 (consBan b924 (consBan b925 (consBan b926 (consBan b927 (consBan b928 (consBan b929 (consBan b930 (consBan b931 (consBan b932 (consBan b933 (consBan b934 (consBan b935 (consBan b936 (consBan b937 (consBan b938 (consBan b939 (consBan b940 (consBan b941 (consBan b942 (consBan b943 (consBan b944 (consBan b945 (consBan b946 (nilBan 55 5)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w43 : Wide 55 6 v141 := viaSub (ws := [v141]) (consBan b947 (nilBan 55 6)) (by decide) (by decide +kernel)
theorem b948 : Ban 220 8 v883 := viaCut p127_61 w43 (by decide) (by decide +kernel) (by decide +kernel)
def v940 : List ℕ := [t0,t149,t1,t2,t3,t4,t5,t6]
theorem b949 : Ban 220 8 v940 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v941 : List ℕ := [t0,t1,t2,t150,t4,t5,t6]
def v942 : List ℕ := [t92,t87,t88,t89,t115,t91]
theorem b950 : Ban 55 5 v942 := viaSmall (by decide +kernel) (by decide)
def v943 : List ℕ := [t87,t88,t93,t89,t115,t91]
theorem b951 : Ban 55 5 v943 := viaSmall (by decide +kernel) (by decide)
def v944 : List ℕ := [t94,t87,t88,t89,t115,t91]
theorem b952 : Ban 55 5 v944 := viaSmall (by decide +kernel) (by decide)
def v945 : List ℕ := [t87,t95,t88,t89,t115,t91]
theorem b953 : Ban 55 5 v945 := viaSmall (by decide +kernel) (by decide)
def v946 : List ℕ := [t96,t87,t88,t89,t115,t91]
theorem b954 : Ban 55 5 v946 := viaSmall (by decide +kernel) (by decide)
def v947 : List ℕ := [t87,t88,t97,t115,t91]
theorem b955 : Ban 55 5 v947 := viaSmall (by decide +kernel) (by decide)
def v948 : List ℕ := [t88,t89,t97,t115,t91]
theorem b956 : Ban 55 5 v948 := viaSmall (by decide +kernel) (by decide)
def v949 : List ℕ := [t87,t88,t89,t97,t115,t91]
theorem b957 : Ban 55 5 v949 := viaSmall (by decide +kernel) (by decide)
def v950 : List ℕ := [t98,t88,t89,t115,t91]
theorem b958 : Ban 55 5 v950 := viaSmall (by decide +kernel) (by decide)
def v951 : List ℕ := [t98,t87,t88,t89,t115,t91]
theorem b959 : Ban 55 5 v951 := viaSmall (by decide +kernel) (by decide)
def v952 : List ℕ := [t87,t88,t99,t115,t91]
theorem b960 : Ban 55 5 v952 := viaSmall (by decide +kernel) (by decide)
def v953 : List ℕ := [t87,t88,t99,t89,t115,t91]
theorem b961 : Ban 55 5 v953 := viaSmall (by decide +kernel) (by decide)
def v954 : List ℕ := [t100,t87,t88,t89,t115,t91]
theorem b962 : Ban 55 5 v954 := viaSmall (by decide +kernel) (by decide)
def t368 : ℕ := 0x22544a89512a25000fffffffffff
def v955 : List ℕ := [t87,t88,t89,t115,t368,t91]
theorem b963 : Ban 55 5 v955 := viaSmall (by decide +kernel) (by decide)
def v956 : List ℕ := [t102,t87,t88,t89,t115,t91]
theorem b964 : Ban 55 5 v956 := viaSmall (by decide +kernel) (by decide)
def t369 : ℕ := 0x22044088110220000001ffc00000
def v957 : List ℕ := [t87,t88,t89,t369,t115,t91]
theorem b965 : Ban 55 5 v957 := viaSmall (by decide +kernel) (by decide)
def v958 : List ℕ := [t104,t87,t88,t89,t115,t91]
theorem b966 : Ban 55 5 v958 := viaSmall (by decide +kernel) (by decide)
def v959 : List ℕ := [t87,t88,t89,t115,t91,t105]
theorem b967 : Ban 55 5 v959 := viaSmall (by decide +kernel) (by decide)
def v960 : List ℕ := [t106,t87,t88,t89,t115,t91]
theorem b968 : Ban 55 5 v960 := viaSmall (by decide +kernel) (by decide)
def v961 : List ℕ := [t87,t88,t89,t115,t107,t91]
theorem b969 : Ban 55 5 v961 := viaSmall (by decide +kernel) (by decide)
def v962 : List ℕ := [t87,t108,t88,t89,t115,t91]
theorem b970 : Ban 55 5 v962 := viaSmall (by decide +kernel) (by decide)
def v963 : List ℕ := [t87,t89,t109,t115,t91]
theorem b971 : Ban 55 5 v963 := viaSmall (by decide +kernel) (by decide)
def v964 : List ℕ := [t87,t88,t89,t109,t115,t91]
theorem b972 : Ban 55 5 v964 := viaSmall (by decide +kernel) (by decide)
def v965 : List ℕ := [t87,t110,t89,t115,t91]
theorem b973 : Ban 55 5 v965 := viaSmall (by decide +kernel) (by decide)
def v966 : List ℕ := [t87,t110,t88,t89,t115,t91]
theorem b974 : Ban 55 5 v966 := viaSmall (by decide +kernel) (by decide)
def v967 : List ℕ := [t87,t88,t111,t115,t91]
theorem b975 : Ban 55 5 v967 := viaSmall (by decide +kernel) (by decide)
def v968 : List ℕ := [t87,t88,t111,t89,t115,t91]
theorem b976 : Ban 55 5 v968 := viaSmall (by decide +kernel) (by decide)
def v969 : List ℕ := [t87,t89,t115,t113,t91]
theorem b977 : Ban 55 5 v969 := viaSmall (by decide +kernel) (by decide)
def v970 : List ℕ := [t87,t88,t89,t115,t113,t91]
theorem b978 : Ban 55 5 v970 := viaSmall (by decide +kernel) (by decide)
def v971 : List ℕ := [t116,t87,t88,t89,t115,t91]
theorem b979 : Ban 55 5 v971 := viaSmall (by decide +kernel) (by decide)
def v972 : List ℕ := [t87,t88,t89,t115,t91,t117]
theorem b980 : Ban 55 5 v972 := viaSmall (by decide +kernel) (by decide)
def v973 : List ℕ := [t87,t118,t88,t89,t115,t91]
theorem b981 : Ban 55 5 v973 := viaSmall (by decide +kernel) (by decide)
def v974 : List ℕ := [t87,t88,t89,t115,t119,t91]
theorem b982 : Ban 55 5 v974 := viaSmall (by decide +kernel) (by decide)
def v975 : List ℕ := [t120,t87,t88,t115,t91]
theorem b983 : Ban 55 5 v975 := viaCut p61_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v976 : List ℕ := [t120,t87,t88,t89,t115,t91]
theorem b984 : Ban 55 5 v976 := viaSmall (by decide +kernel) (by decide)
def t370 : ℕ := 0x33666ccd99b336000001fffff800
def v977 : List ℕ := [t87,t88,t89,t115,t370,t91]
theorem b985 : Ban 55 5 v977 := viaSmall (by decide +kernel) (by decide)
def v978 : List ℕ := [t87,t88,t122,t89,t115,t91]
theorem b986 : Ban 55 5 v978 := viaSmall (by decide +kernel) (by decide)
def v979 : List ℕ := [t87,t88,t287,t115,t91]
theorem b987 : Ban 55 5 v979 := viaSmall (by decide +kernel) (by decide)
def v980 : List ℕ := [t87,t88,t89,t287,t115,t91]
theorem b988 : Ban 55 5 v980 := viaSmall (by decide +kernel) (by decide)
def v981 : List ℕ := [t87,t88,t124,t89,t115,t91]
theorem b989 : Ban 55 5 v981 := viaSmall (by decide +kernel) (by decide)
def v982 : List ℕ := [t87,t88,t89,t115,t125]
theorem b990 : Ban 55 5 v982 := viaSmall (by decide +kernel) (by decide)
def v983 : List ℕ := [t87,t88,t115,t91,t125]
theorem b991 : Ban 55 5 v983 := viaSmall (by decide +kernel) (by decide)
def v984 : List ℕ := [t87,t88,t89,t115,t91,t125]
theorem b992 : Ban 55 5 v984 := viaSmall (by decide +kernel) (by decide)
def v985 : List ℕ := [t87,t126,t88,t115,t91]
theorem b993 : Ban 55 5 v985 := viaSmall (by decide +kernel) (by decide)
def v986 : List ℕ := [t87,t126,t88,t89,t115,t91]
theorem b994 : Ban 55 5 v986 := viaSmall (by decide +kernel) (by decide)
def v987 : List ℕ := [t87,t88,t89,t115,t127]
theorem b995 : Ban 55 5 v987 := viaSmall (by decide +kernel) (by decide)
def v988 : List ℕ := [t87,t88,t89,t115,t127,t91]
theorem b996 : Ban 55 5 v988 := viaSmall (by decide +kernel) (by decide)
def v989 : List ℕ := [t87,t88,t89,t128,t115,t91]
theorem b997 : Ban 55 5 v989 := viaSmall (by decide +kernel) (by decide)
def t371 : ℕ := 0x3a0740e81d03a07ffffffffff800
def v990 : List ℕ := [t87,t88,t89,t115,t371]
theorem b998 : Ban 55 5 v990 := viaCut p61_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v991 : List ℕ := [t87,t88,t89,t91,t371]
theorem b999 : Ban 55 5 v991 := viaSmall (by decide +kernel) (by decide)
def v992 : List ℕ := [t87,t88,t89,t115,t91,t371]
theorem b1000 : Ban 55 5 v992 := viaSmall (by decide +kernel) (by decide)
def t372 : ℕ := 0x2004008010020000001fffff800
def v993 : List ℕ := [t87,t372,t88,t89,t91]
theorem b1001 : Ban 55 5 v993 := viaSmall (by decide +kernel) (by decide)
def v994 : List ℕ := [t87,t372,t88,t89,t115,t91]
theorem b1002 : Ban 55 5 v994 := viaSmall (by decide +kernel) (by decide)
def v995 : List ℕ := [t87,t88,t89,t131,t115]
theorem b1003 : Ban 55 5 v995 := viaSmall (by decide +kernel) (by decide)
def v996 : List ℕ := [t87,t88,t89,t131,t115,t91]
theorem b1004 : Ban 55 5 v996 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1005 : Ban 55 6 v143 := viaBranch (ws := [v942,v943,v944,v945,v946,v947,v948,v949,v950,v951,v952,v953,v954,v955,v956,v957,v958,v959,v960,v961,v962,v514,v963,v964,v965,v966,v967,v968,v138,v969,v970,v971,v972,v973,v974,v975,v976,v977,v978,v979,v980,v981,v982,v983,v984,v985,v986,v987,v988,v989,v990,v991,v992,v993,v994,v995,v996]) (consBan b950 (consBan b951 (consBan b952 (consBan b953 (consBan b954 (consBan b955 (consBan b956 (consBan b957 (consBan b958 (consBan b959 (consBan b960 (consBan b961 (consBan b962 (consBan b963 (consBan b964 (consBan b965 (consBan b966 (consBan b967 (consBan b968 (consBan b969 (consBan b970 (consBan b517 (consBan b971 (consBan b972 (consBan b973 (consBan b974 (consBan b975 (consBan b976 (consBan b135 (consBan b977 (consBan b978 (consBan b979 (consBan b980 (consBan b981 (consBan b982 (consBan b983 (consBan b984 (consBan b985 (consBan b986 (consBan b987 (consBan b988 (consBan b989 (consBan b990 (consBan b991 (consBan b992 (consBan b993 (consBan b994 (consBan b995 (consBan b996 (consBan b997 (consBan b998 (consBan b999 (consBan b1000 (consBan b1001 (consBan b1002 (consBan b1003 (consBan b1004 (nilBan 55 5)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w44 : Wide 55 6 v143 := viaSub (ws := [v143]) (consBan b1005 (nilBan 55 6)) (by decide) (by decide +kernel)
theorem b1006 : Ban 220 8 v941 := viaCut p127_61 w44 (by decide) (by decide +kernel) (by decide +kernel)
def v997 : List ℕ := [t0,t1,t2,t150,t3,t4,t5,t6]
theorem b1007 : Ban 220 8 v997 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v998 : List ℕ := [t151,t0,t1,t2,t3,t4,t5,t6]
theorem b1008 : Ban 220 8 v998 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v999 : List ℕ := [t0,t1,t2,t3,t4,t152,t5,t6]
theorem b1009 : Ban 220 8 v999 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1000 : List ℕ := [t0,t153,t1,t2,t3,t4,t5,t6]
theorem b1010 : Ban 220 8 v1000 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1001 : List ℕ := [t0,t1,t2,t3,t154,t4,t5,t6]
theorem b1011 : Ban 220 8 v1001 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1002 : List ℕ := [t155,t0,t1,t2,t3,t4,t5,t6]
theorem b1012 : Ban 220 8 v1002 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1003 : List ℕ := [t0,t1,t2,t3,t4,t5,t156,t6]
theorem b1013 : Ban 220 8 v1003 := viaCut p127_82 w34 (by decide) (by decide +kernel) (by decide +kernel)
def v1004 : List ℕ := [t0,t157,t1,t2,t3,t4,t5,t6]
theorem b1014 : Ban 220 8 v1004 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1005 : List ℕ := [t0,t1,t2,t3,t4,t158,t5,t6]
theorem b1015 : Ban 220 8 v1005 := viaCut p127_82 w34 (by decide) (by decide +kernel) (by decide +kernel)
def v1006 : List ℕ := [t159,t0,t1,t2,t3,t4,t5,t6]
theorem b1016 : Ban 220 8 v1006 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1007 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t160]
theorem b1017 : Ban 220 8 v1007 := viaCut p127_61 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v1008 : List ℕ := [t0,t161,t1,t2,t3,t4,t5,t6]
theorem b1018 : Ban 220 8 v1008 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1009 : List ℕ := [t0,t1,t2,t3,t4,t5,t162,t6]
theorem b1019 : Ban 220 8 v1009 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1010 : List ℕ := [t164,t0,t1,t2,t3,t4,t5,t6]
theorem b1020 : Ban 220 8 v1010 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1011 : List ℕ := [t0,t1,t2,t3,t165,t4,t5,t6]
theorem b1021 : Ban 220 8 v1011 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1012 : List ℕ := [t0,t1,t166,t2,t3,t4,t5,t6]
theorem b1022 : Ban 220 8 v1012 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1013 : List ℕ := [t0,t1,t2,t167,t3,t4,t5,t6]
theorem b1023 : Ban 220 8 v1013 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1014 : List ℕ := [t168,t0,t1,t2,t3,t4,t5,t6]
theorem b1024 : Ban 220 8 v1014 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1015 : List ℕ := [t0,t1,t2,t3,t169,t5,t6]
def v1016 : List ℕ := [t108,t312,t293,t303,t90,t91]
theorem b1025 : Ban 55 5 v1016 := viaSmall (by decide +kernel) (by decide)
def v1017 : List ℕ := [t293,t295,t303,t90,t91]
theorem b1026 : Ban 55 5 v1017 := viaSmall (by decide +kernel) (by decide)
def v1018 : List ℕ := [t312,t293,t295,t303,t90,t91]
theorem b1027 : Ban 55 5 v1018 := viaSmall (by decide +kernel) (by decide)
def v1019 : List ℕ := [t292,t312,t293,t303,t90,t91]
theorem b1028 : Ban 55 5 v1019 := viaSmall (by decide +kernel) (by decide)
def v1020 : List ℕ := [t312,t313,t293,t303,t90,t91]
theorem b1029 : Ban 55 5 v1020 := viaSmall (by decide +kernel) (by decide)
def t373 : ℕ := 0x1002004008010000000000007ff
def v1021 : List ℕ := [t373,t312,t293,t303,t90,t91]
theorem b1030 : Ban 55 5 v1021 := viaSmall (by decide +kernel) (by decide)
def v1022 : List ℕ := [t312,t293,t303,t281,t90,t91]
theorem b1031 : Ban 55 5 v1022 := viaSmall (by decide +kernel) (by decide)
def v1023 : List ℕ := [t297,t312,t293,t303,t90,t91]
theorem b1032 : Ban 55 5 v1023 := viaSmall (by decide +kernel) (by decide)
def t374 : ℕ := 0x14728e51ca3947000ffe003ff800
def v1024 : List ℕ := [t312,t293,t374,t303,t90,t91]
theorem b1033 : Ban 55 5 v1024 := viaSmall (by decide +kernel) (by decide)
def v1025 : List ℕ := [t120,t312,t293,t303,t90,t91]
theorem b1034 : Ban 55 5 v1025 := viaSmall (by decide +kernel) (by decide)
def v1026 : List ℕ := [t312,t293,t303,t90,t113,t91]
theorem b1035 : Ban 55 5 v1026 := viaSmall (by decide +kernel) (by decide)
def v1027 : List ℕ := [t114,t312,t293,t303,t90,t91]
theorem b1036 : Ban 55 5 v1027 := viaSmall (by decide +kernel) (by decide)
def v1028 : List ℕ := [t312,t293,t303,t123,t90,t91]
theorem b1037 : Ban 55 5 v1028 := viaSmall (by decide +kernel) (by decide)
def v1029 : List ℕ := [t116,t312,t293,t303,t90,t91]
theorem b1038 : Ban 55 5 v1029 := viaSmall (by decide +kernel) (by decide)
def v1030 : List ℕ := [t312,t293,t303,t90,t91,t316]
theorem b1039 : Ban 55 5 v1030 := viaSmall (by decide +kernel) (by decide)
def v1031 : List ℕ := [t317,t312,t293,t303,t90,t91]
theorem b1040 : Ban 55 5 v1031 := viaSmall (by decide +kernel) (by decide)
def v1032 : List ℕ := [t312,t293,t303,t90,t119,t91]
theorem b1041 : Ban 55 5 v1032 := viaSmall (by decide +kernel) (by decide)
def v1033 : List ℕ := [t312,t305,t303,t90,t91]
theorem b1042 : Ban 55 5 v1033 := viaSmall (by decide +kernel) (by decide)
def v1034 : List ℕ := [t312,t293,t305,t303,t90,t91]
theorem b1043 : Ban 55 5 v1034 := viaSmall (by decide +kernel) (by decide)
def v1035 : List ℕ := [t312,t112,t293,t303,t90,t91]
theorem b1044 : Ban 55 5 v1035 := viaSmall (by decide +kernel) (by decide)
def v1036 : List ℕ := [t312,t293,t303,t306,t91]
theorem b1045 : Ban 55 5 v1036 := viaSmall (by decide +kernel) (by decide)
def v1037 : List ℕ := [t312,t293,t303,t90,t306,t91]
theorem b1046 : Ban 55 5 v1037 := viaSmall (by decide +kernel) (by decide)
def v1038 : List ℕ := [t307,t312,t293,t303,t90,t91]
theorem b1047 : Ban 55 5 v1038 := viaSmall (by decide +kernel) (by decide)
def v1039 : List ℕ := [t312,t293,t303,t115,t91]
theorem b1048 : Ban 55 5 v1039 := viaSmall (by decide +kernel) (by decide)
def v1040 : List ℕ := [t312,t293,t303,t115,t90,t91]
theorem b1049 : Ban 55 5 v1040 := viaSmall (by decide +kernel) (by decide)
def v1041 : List ℕ := [t104,t312,t293,t303,t90,t91]
theorem b1050 : Ban 55 5 v1041 := viaSmall (by decide +kernel) (by decide)
def v1042 : List ℕ := [t312,t293,t303,t90,t91,t308]
theorem b1051 : Ban 55 5 v1042 := viaSmall (by decide +kernel) (by decide)
def v1043 : List ℕ := [t312,t309,t293,t303,t90,t91]
theorem b1052 : Ban 55 5 v1043 := viaSmall (by decide +kernel) (by decide)
def v1044 : List ℕ := [t312,t293,t303,t90,t107,t91]
theorem b1053 : Ban 55 5 v1044 := viaSmall (by decide +kernel) (by decide)
def t375 : ℕ := 0x4008010020040000000003ff800
def v1045 : List ℕ := [t312,t375,t293,t303,t90,t91]
theorem b1054 : Ban 55 5 v1045 := viaSmall (by decide +kernel) (by decide)
def t376 : ℕ := 0x3776eedddbbb77000fffffffffff
def v1046 : List ℕ := [t312,t293,t303,t90,t376,t91]
theorem b1055 : Ban 55 5 v1046 := viaSmall (by decide +kernel) (by decide)
def t377 : ℕ := 0x11722e45c8b917000ffe000007ff
def v1047 : List ℕ := [t312,t293,t377,t303,t90,t91]
theorem b1056 : Ban 55 5 v1047 := viaSmall (by decide +kernel) (by decide)
def v1048 : List ℕ := [t312,t293,t303,t369,t90,t91]
theorem b1057 : Ban 55 5 v1048 := viaSmall (by decide +kernel) (by decide)
def t378 : ℕ := 0x10020040080100000ffe00000000
def v1049 : List ℕ := [t312,t293,t378,t303,t90,t91]
theorem b1058 : Ban 55 5 v1049 := viaSmall (by decide +kernel) (by decide)
def t379 : ℕ := 0x3d77aef5debbd77ffffe003fffff
def v1050 : List ℕ := [t312,t293,t90,t91,t379]
theorem b1059 : Ban 55 5 v1050 := viaSmall (by decide +kernel) (by decide)
def v1051 : List ℕ := [t312,t293,t303,t90,t91,t379]
theorem b1060 : Ban 55 5 v1051 := viaSmall (by decide +kernel) (by decide)
def t380 : ℕ := 0x570ae15c2b857000000003fffff
def v1052 : List ℕ := [t312,t293,t380,t90,t91]
theorem b1061 : Ban 55 5 v1052 := viaSmall (by decide +kernel) (by decide)
def v1053 : List ℕ := [t312,t293,t380,t303,t90,t91]
theorem b1062 : Ban 55 5 v1053 := viaSmall (by decide +kernel) (by decide)
def t381 : ℕ := 0x280500a01402807ff00000000000
def v1054 : List ℕ := [t312,t293,t303,t90,t381,t91]
theorem b1063 : Ban 55 5 v1054 := viaSmall (by decide +kernel) (by decide)
def v1055 : List ℕ := [t312,t293,t303,t128,t90,t91]
theorem b1064 : Ban 55 5 v1055 := viaSmall (by decide +kernel) (by decide)
def v1056 : List ℕ := [t312,t293,t303,t90,t129]
theorem b1065 : Ban 55 5 v1056 := viaSmall (by decide +kernel) (by decide)
def v1057 : List ℕ := [t312,t293,t303,t91,t129]
theorem b1066 : Ban 55 5 v1057 := viaSmall (by decide +kernel) (by decide)
def v1058 : List ℕ := [t312,t293,t303,t90,t91,t129]
theorem b1067 : Ban 55 5 v1058 := viaSmall (by decide +kernel) (by decide)
def v1059 : List ℕ := [t312,t293,t130,t303,t91]
theorem b1068 : Ban 55 5 v1059 := viaSmall (by decide +kernel) (by decide)
def v1060 : List ℕ := [t312,t293,t130,t303,t90,t91]
theorem b1069 : Ban 55 5 v1060 := viaSmall (by decide +kernel) (by decide)
def v1061 : List ℕ := [t312,t293,t303,t131,t90]
theorem b1070 : Ban 55 5 v1061 := viaSmall (by decide +kernel) (by decide)
def v1062 : List ℕ := [t312,t293,t303,t131,t90,t91]
theorem b1071 : Ban 55 5 v1062 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1072 : Ban 55 6 v844 := viaBranch (ws := [v1016,v1017,v1018,v608,v1019,v1020,v1021,v1022,v1023,v1024,v1025,v1026,v1027,v1028,v1029,v1030,v1031,v1032,v849,v1033,v1034,v1035,v1036,v1037,v1038,v1039,v1040,v1041,v1042,v1043,v1044,v1045,v1046,v1047,v1048,v1049,v1050,v1051,v1052,v1053,v1054,v1055,v1056,v1057,v1058,v1059,v1060,v1061,v1062]) (consBan b1025 (consBan b1026 (consBan b1027 (consBan b612 (consBan b1028 (consBan b1029 (consBan b1030 (consBan b1031 (consBan b1032 (consBan b1033 (consBan b1034 (consBan b1035 (consBan b1036 (consBan b1037 (consBan b1038 (consBan b1039 (consBan b1040 (consBan b1041 (consBan b855 (consBan b1042 (consBan b1043 (consBan b1044 (consBan b1045 (consBan b1046 (consBan b1047 (consBan b1048 (consBan b1049 (consBan b1050 (consBan b1051 (consBan b1052 (consBan b1053 (consBan b1054 (consBan b1055 (consBan b1056 (consBan b1057 (consBan b1058 (consBan b1059 (consBan b1060 (consBan b1061 (consBan b1062 (consBan b1063 (consBan b1064 (consBan b1065 (consBan b1066 (consBan b1067 (consBan b1068 (consBan b1069 (consBan b1070 (consBan b1071 (nilBan 55 5)))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w45 : Wide 55 6 v844 := viaSub (ws := [v844]) (consBan b1072 (nilBan 55 6)) (by decide) (by decide +kernel)
theorem b1073 : Ban 220 8 v1015 := viaCut p127_109 w45 (by decide) (by decide +kernel) (by decide +kernel)
def v1063 : List ℕ := [t0,t1,t3,t4,t169,t5,t6]
theorem b1074 : Ban 60 5 v427 := viaSmall (by decide +kernel) (by decide)
theorem b1075 : Ban 60 5 v428 := viaSmall (by decide +kernel) (by decide)
theorem b1076 : Ban 60 5 v429 := viaSmall (by decide +kernel) (by decide)
theorem b1077 : Ban 60 5 v430 := viaSmall (by decide +kernel) (by decide)
theorem b1078 : Ban 60 5 v431 := viaSmall (by decide +kernel) (by decide)
theorem b1079 : Ban 60 5 v432 := viaSmall (by decide +kernel) (by decide)
theorem b1080 : Ban 60 5 v433 := viaSmall (by decide +kernel) (by decide)
theorem b1081 : Ban 60 5 v434 := viaSmall (by decide +kernel) (by decide)
theorem b1082 : Ban 60 5 v435 := viaSmall (by decide +kernel) (by decide)
theorem b1083 : Ban 60 5 v436 := viaSmall (by decide +kernel) (by decide)
theorem b1084 : Ban 60 5 v437 := viaSmall (by decide +kernel) (by decide)
theorem b1085 : Ban 60 5 v438 := viaSmall (by decide +kernel) (by decide)
theorem b1086 : Ban 60 5 v439 := viaSmall (by decide +kernel) (by decide)
theorem b1087 : Ban 60 5 v80 := viaSmall (by decide +kernel) (by decide)
theorem b1088 : Ban 60 5 v440 := viaSmall (by decide +kernel) (by decide)
theorem b1089 : Ban 60 5 v441 := viaSmall (by decide +kernel) (by decide)
theorem b1090 : Ban 60 5 v442 := viaSmall (by decide +kernel) (by decide)
theorem b1091 : Ban 60 5 v443 := viaSmall (by decide +kernel) (by decide)
theorem b1092 : Ban 60 5 v444 := viaSmall (by decide +kernel) (by decide)
theorem b1093 : Ban 60 5 v445 := viaSmall (by decide +kernel) (by decide)
theorem b1094 : Ban 60 5 v446 := viaSmall (by decide +kernel) (by decide)
theorem b1095 : Ban 60 5 v447 := viaSmall (by decide +kernel) (by decide)
theorem b1096 : Ban 60 5 v448 := viaSmall (by decide +kernel) (by decide)
theorem b1097 : Ban 60 5 v449 := viaSmall (by decide +kernel) (by decide)
theorem b1098 : Ban 60 5 v450 := viaSmall (by decide +kernel) (by decide)
theorem b1099 : Ban 60 5 v451 := viaSmall (by decide +kernel) (by decide)
theorem b1100 : Ban 60 5 v452 := viaSmall (by decide +kernel) (by decide)
theorem b1101 : Ban 60 5 v453 := viaSmall (by decide +kernel) (by decide)
theorem b1102 : Ban 60 5 v454 := viaSmall (by decide +kernel) (by decide)
theorem b1103 : Ban 60 5 v455 := viaSmall (by decide +kernel) (by decide)
theorem b1104 : Ban 60 5 v456 := viaSmall (by decide +kernel) (by decide)
theorem b1105 : Ban 60 5 v457 := viaSmall (by decide +kernel) (by decide)
theorem b1106 : Ban 60 5 v458 := viaSmall (by decide +kernel) (by decide)
theorem b1107 : Ban 60 5 v459 := viaSmall (by decide +kernel) (by decide)
theorem b1108 : Ban 60 5 v460 := viaSmall (by decide +kernel) (by decide)
theorem b1109 : Ban 60 5 v461 := viaSmall (by decide +kernel) (by decide)
theorem b1110 : Ban 60 5 v462 := viaSmall (by decide +kernel) (by decide)
theorem b1111 : Ban 60 5 v463 := viaSmall (by decide +kernel) (by decide)
theorem b1112 : Ban 60 5 v464 := viaSmall (by decide +kernel) (by decide)
theorem b1113 : Ban 60 5 v465 := viaSmall (by decide +kernel) (by decide)
theorem b1114 : Ban 60 5 v466 := viaSmall (by decide +kernel) (by decide)
theorem b1115 : Ban 60 5 v467 := viaSmall (by decide +kernel) (by decide)
theorem b1116 : Ban 60 5 v468 := viaSmall (by decide +kernel) (by decide)
theorem b1117 : Ban 60 5 v469 := viaSmall (by decide +kernel) (by decide)
theorem b1118 : Ban 60 5 v470 := viaSmall (by decide +kernel) (by decide)
theorem b1119 : Ban 60 5 v471 := viaSmall (by decide +kernel) (by decide)
theorem b1120 : Ban 60 5 v472 := viaSmall (by decide +kernel) (by decide)
theorem b1121 : Ban 60 5 v473 := viaSmall (by decide +kernel) (by decide)
theorem b1122 : Ban 60 5 v474 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1123 : Ban 60 6 v426 := viaBranch (ws := [v427,v428,v429,v430,v431,v432,v433,v434,v435,v436,v437,v438,v439,v80,v440,v441,v442,v443,v444,v445,v446,v447,v448,v449,v450,v451,v452,v453,v454,v455,v456,v457,v458,v459,v460,v461,v462,v463,v464,v465,v466,v467,v468,v469,v470,v471,v472,v473,v474]) (consBan b1074 (consBan b1075 (consBan b1076 (consBan b1077 (consBan b1078 (consBan b1079 (consBan b1080 (consBan b1081 (consBan b1082 (consBan b1083 (consBan b1084 (consBan b1085 (consBan b1086 (consBan b1087 (consBan b1088 (consBan b1089 (consBan b1090 (consBan b1091 (consBan b1092 (consBan b1093 (consBan b1094 (consBan b1095 (consBan b1096 (consBan b1097 (consBan b1098 (consBan b1099 (consBan b1100 (consBan b1101 (consBan b1102 (consBan b1103 (consBan b1104 (consBan b1105 (consBan b1106 (consBan b1107 (consBan b1108 (consBan b1109 (consBan b1110 (consBan b1111 (consBan b1112 (consBan b1113 (consBan b1114 (consBan b1115 (consBan b1116 (consBan b1117 (consBan b1118 (consBan b1119 (consBan b1120 (consBan b1121 (consBan b1122 (nilBan 60 5)))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w46 : Wide 60 6 v426 := viaSub (ws := [v426]) (consBan b1123 (nilBan 60 6)) (by decide) (by decide +kernel)
def p127_93 : Projection 220 60 := pick [0,1,4,5,8,10,12,13,17,18,20,21,24,25,28,30,32,33,37,38,60,61,64,65,68,70,72,73,77,78,160,161,164,165,168,170,172,173,177,178,180,181,184,185,188,190,192,193,197,198,200,201,204,205,208,210,212,213,217,218] rfl (by decide +kernel) (by decide)
theorem b1124 : Ban 220 8 v1063 := viaCut p127_93 w46 (by decide) (by decide +kernel) (by decide +kernel)
def v1064 : List ℕ := [t0,t1,t2,t3,t4,t169,t5,t6]
theorem b1125 : Ban 220 8 v1064 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1065 : List ℕ := [t0,t1,t172,t3,t4,t5,t6]
def v1066 : List ℕ := [t92,t87,t88,t99,t90,t91]
theorem b1126 : Ban 55 5 v1066 := viaSmall (by decide +kernel) (by decide)
def v1067 : List ℕ := [t87,t88,t93,t99,t90,t91]
theorem b1127 : Ban 55 5 v1067 := viaSmall (by decide +kernel) (by decide)
def v1068 : List ℕ := [t94,t87,t88,t99,t90,t91]
theorem b1128 : Ban 55 5 v1068 := viaSmall (by decide +kernel) (by decide)
def v1069 : List ℕ := [t87,t95,t88,t99,t90,t91]
theorem b1129 : Ban 55 5 v1069 := viaSmall (by decide +kernel) (by decide)
def v1070 : List ℕ := [t88,t99,t97,t90,t91]
theorem b1130 : Ban 55 5 v1070 := viaSmall (by decide +kernel) (by decide)
def v1071 : List ℕ := [t87,t88,t99,t97,t90,t91]
theorem b1131 : Ban 55 5 v1071 := viaSmall (by decide +kernel) (by decide)
def v1072 : List ℕ := [t100,t87,t88,t99,t90,t91]
theorem b1132 : Ban 55 5 v1072 := viaSmall (by decide +kernel) (by decide)
def v1073 : List ℕ := [t87,t88,t99,t90,t101,t91]
theorem b1133 : Ban 55 5 v1073 := viaSmall (by decide +kernel) (by decide)
def v1074 : List ℕ := [t102,t87,t88,t99,t90,t91]
theorem b1134 : Ban 55 5 v1074 := viaSmall (by decide +kernel) (by decide)
def v1075 : List ℕ := [t87,t88,t99,t103,t90,t91]
theorem b1135 : Ban 55 5 v1075 := viaSmall (by decide +kernel) (by decide)
def v1076 : List ℕ := [t104,t87,t88,t99,t90,t91]
theorem b1136 : Ban 55 5 v1076 := viaSmall (by decide +kernel) (by decide)
def v1077 : List ℕ := [t87,t88,t99,t90,t91,t105]
theorem b1137 : Ban 55 5 v1077 := viaSmall (by decide +kernel) (by decide)
def v1078 : List ℕ := [t106,t87,t88,t99,t90,t91]
theorem b1138 : Ban 55 5 v1078 := viaSmall (by decide +kernel) (by decide)
def v1079 : List ℕ := [t87,t88,t99,t90,t107,t91]
theorem b1139 : Ban 55 5 v1079 := viaSmall (by decide +kernel) (by decide)
def v1080 : List ℕ := [t87,t108,t88,t99,t90,t91]
theorem b1140 : Ban 55 5 v1080 := viaSmall (by decide +kernel) (by decide)
def t382 : ℕ := 0x15a2b4568ad15a7ff001ffc007ff
def v1081 : List ℕ := [t87,t88,t382,t90,t91]
theorem b1141 : Ban 55 5 v1081 := viaSmall (by decide +kernel) (by decide)
def v1082 : List ℕ := [t87,t99,t382,t90,t91]
theorem b1142 : Ban 55 5 v1082 := viaSmall (by decide +kernel) (by decide)
def v1083 : List ℕ := [t87,t88,t99,t382,t90,t91]
theorem b1143 : Ban 55 5 v1083 := viaSmall (by decide +kernel) (by decide)
def v1084 : List ℕ := [t87,t110,t99,t90,t91]
theorem b1144 : Ban 55 5 v1084 := viaSmall (by decide +kernel) (by decide)
def v1085 : List ℕ := [t87,t110,t88,t99,t90,t91]
theorem b1145 : Ban 55 5 v1085 := viaSmall (by decide +kernel) (by decide)
def t383 : ℕ := 0x10220440881102000001ffc00000
def v1086 : List ℕ := [t87,t88,t383,t90,t91]
theorem b1146 : Ban 55 5 v1086 := viaSmall (by decide +kernel) (by decide)
def v1087 : List ℕ := [t87,t88,t383,t99,t90,t91]
theorem b1147 : Ban 55 5 v1087 := viaSmall (by decide +kernel) (by decide)
def v1088 : List ℕ := [t87,t112,t88,t99,t90,t91]
theorem b1148 : Ban 55 5 v1088 := viaSmall (by decide +kernel) (by decide)
def v1089 : List ℕ := [t87,t88,t99,t113,t91]
theorem b1149 : Ban 55 5 v1089 := viaSmall (by decide +kernel) (by decide)
def v1090 : List ℕ := [t87,t99,t90,t113,t91]
theorem b1150 : Ban 55 5 v1090 := viaSmall (by decide +kernel) (by decide)
def v1091 : List ℕ := [t87,t88,t99,t90,t113,t91]
theorem b1151 : Ban 55 5 v1091 := viaSmall (by decide +kernel) (by decide)
def v1092 : List ℕ := [t87,t114,t88,t99,t90,t91]
theorem b1152 : Ban 55 5 v1092 := viaSmall (by decide +kernel) (by decide)
def v1093 : List ℕ := [t87,t88,t99,t115,t90,t91]
theorem b1153 : Ban 55 5 v1093 := viaSmall (by decide +kernel) (by decide)
def v1094 : List ℕ := [t116,t87,t88,t99,t90,t91]
theorem b1154 : Ban 55 5 v1094 := viaSmall (by decide +kernel) (by decide)
def v1095 : List ℕ := [t87,t88,t99,t90,t91,t117]
theorem b1155 : Ban 55 5 v1095 := viaSmall (by decide +kernel) (by decide)
def v1096 : List ℕ := [t87,t118,t88,t99,t90,t91]
theorem b1156 : Ban 55 5 v1096 := viaSmall (by decide +kernel) (by decide)
def v1097 : List ℕ := [t87,t88,t99,t90,t119,t91]
theorem b1157 : Ban 55 5 v1097 := viaSmall (by decide +kernel) (by decide)
def v1098 : List ℕ := [t120,t87,t88,t99,t90,t91]
theorem b1158 : Ban 55 5 v1098 := viaSmall (by decide +kernel) (by decide)
def t384 : ℕ := 0x3726e4dc9b9372000001fffff800
def v1099 : List ℕ := [t87,t88,t99,t90,t384,t91]
theorem b1159 : Ban 55 5 v1099 := viaSmall (by decide +kernel) (by decide)
def t385 : ℕ := 0x1122244488911200000000000000
def v1100 : List ℕ := [t87,t88,t385,t99,t90,t91]
theorem b1160 : Ban 55 5 v1100 := viaSmall (by decide +kernel) (by decide)
def v1101 : List ℕ := [t87,t88,t99,t123,t90,t91]
theorem b1161 : Ban 55 5 v1101 := viaSmall (by decide +kernel) (by decide)
def v1102 : List ℕ := [t87,t88,t124,t99,t90,t91]
theorem b1162 : Ban 55 5 v1102 := viaSmall (by decide +kernel) (by decide)
def t386 : ℕ := 0x392724e49c93927fffffffc00000
def v1103 : List ℕ := [t87,t88,t99,t90,t386]
theorem b1163 : Ban 55 5 v1103 := viaSmall (by decide +kernel) (by decide)
def v1104 : List ℕ := [t87,t88,t90,t91,t386]
theorem b1164 : Ban 55 5 v1104 := viaSmall (by decide +kernel) (by decide)
def v1105 : List ℕ := [t87,t88,t99,t90,t91,t386]
theorem b1165 : Ban 55 5 v1105 := viaSmall (by decide +kernel) (by decide)
def t387 : ℕ := 0x1202404809012000001ffc00000
def v1106 : List ℕ := [t87,t387,t88,t90,t91]
theorem b1166 : Ban 55 5 v1106 := viaSmall (by decide +kernel) (by decide)
def v1107 : List ℕ := [t87,t387,t88,t99,t90,t91]
theorem b1167 : Ban 55 5 v1107 := viaSmall (by decide +kernel) (by decide)
def v1108 : List ℕ := [t87,t88,t99,t90,t127]
theorem b1168 : Ban 55 5 v1108 := viaSmall (by decide +kernel) (by decide)
def v1109 : List ℕ := [t87,t88,t99,t90,t127,t91]
theorem b1169 : Ban 55 5 v1109 := viaSmall (by decide +kernel) (by decide)
def v1110 : List ℕ := [t87,t88,t99,t128,t90,t91]
theorem b1170 : Ban 55 5 v1110 := viaSmall (by decide +kernel) (by decide)
def v1111 : List ℕ := [t87,t88,t99,t90,t129]
theorem b1171 : Ban 55 5 v1111 := viaSmall (by decide +kernel) (by decide)
def v1112 : List ℕ := [t87,t88,t99,t91,t129]
theorem b1172 : Ban 55 5 v1112 := viaSmall (by decide +kernel) (by decide)
def v1113 : List ℕ := [t87,t88,t99,t90,t91,t129]
theorem b1173 : Ban 55 5 v1113 := viaSmall (by decide +kernel) (by decide)
def v1114 : List ℕ := [t87,t88,t130,t99,t91]
theorem b1174 : Ban 55 5 v1114 := viaSmall (by decide +kernel) (by decide)
def v1115 : List ℕ := [t87,t88,t130,t99,t90,t91]
theorem b1175 : Ban 55 5 v1115 := viaSmall (by decide +kernel) (by decide)
def v1116 : List ℕ := [t87,t88,t99,t131,t90]
theorem b1176 : Ban 55 5 v1116 := viaSmall (by decide +kernel) (by decide)
def v1117 : List ℕ := [t87,t88,t99,t131,t90,t91]
theorem b1177 : Ban 55 5 v1117 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1178 : Ban 55 6 v119 := viaBranch (ws := [v1066,v1067,v1068,v1069,v114,v1070,v1071,v1072,v1073,v1074,v1075,v1076,v1077,v1078,v1079,v1080,v1081,v1082,v1083,v1084,v1085,v1086,v1087,v1088,v1089,v1090,v1091,v894,v1092,v952,v1093,v1094,v1095,v1096,v1097,v149,v1098,v1099,v1100,v153,v1101,v1102,v1103,v1104,v1105,v1106,v1107,v1108,v1109,v1110,v1111,v1112,v1113,v1114,v1115,v1116,v1117]) (consBan b1126 (consBan b1127 (consBan b1128 (consBan b1129 (consBan b111 (consBan b1130 (consBan b1131 (consBan b1132 (consBan b1133 (consBan b1134 (consBan b1135 (consBan b1136 (consBan b1137 (consBan b1138 (consBan b1139 (consBan b1140 (consBan b1141 (consBan b1142 (consBan b1143 (consBan b1144 (consBan b1145 (consBan b1146 (consBan b1147 (consBan b1148 (consBan b1149 (consBan b1150 (consBan b1151 (consBan b901 (consBan b1152 (consBan b960 (consBan b1153 (consBan b1154 (consBan b1155 (consBan b1156 (consBan b1157 (consBan b146 (consBan b1158 (consBan b1159 (consBan b1160 (consBan b150 (consBan b1161 (consBan b1162 (consBan b1163 (consBan b1164 (consBan b1165 (consBan b1166 (consBan b1167 (consBan b1168 (consBan b1169 (consBan b1170 (consBan b1171 (consBan b1172 (consBan b1173 (consBan b1174 (consBan b1175 (consBan b1176 (consBan b1177 (nilBan 55 5)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w47 : Wide 55 6 v119 := viaSub (ws := [v119]) (consBan b1178 (nilBan 55 6)) (by decide) (by decide +kernel)
theorem b1179 : Ban 220 8 v1065 := viaCut p127_61 w47 (by decide) (by decide +kernel) (by decide +kernel)
def v1118 : List ℕ := [t0,t1,t172,t2,t3,t4,t5,t6]
theorem b1180 : Ban 220 8 v1118 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1119 : List ℕ := [t0,t1,t2,t3,t173,t5,t6]
def v1120 : List ℕ := [t92,t98,t88,t89,t90,t91]
theorem b1181 : Ban 55 5 v1120 := viaSmall (by decide +kernel) (by decide)
def t388 : ℕ := 0x590b21642c8597ffffe003fffff
def v1121 : List ℕ := [t98,t88,t388,t89,t90,t91]
theorem b1182 : Ban 55 5 v1121 := viaSmall (by decide +kernel) (by decide)
def v1122 : List ℕ := [t282,t98,t88,t89,t90,t91]
theorem b1183 : Ban 55 5 v1122 := viaSmall (by decide +kernel) (by decide)
def v1123 : List ℕ := [t98,t95,t88,t89,t90,t91]
theorem b1184 : Ban 55 5 v1123 := viaSmall (by decide +kernel) (by decide)
def v1124 : List ℕ := [t98,t88,t97,t90,t91]
theorem b1185 : Ban 55 5 v1124 := viaSmall (by decide +kernel) (by decide)
def v1125 : List ℕ := [t98,t88,t89,t97,t90,t91]
theorem b1186 : Ban 55 5 v1125 := viaSmall (by decide +kernel) (by decide)
def v1126 : List ℕ := [t100,t98,t88,t89,t90,t91]
theorem b1187 : Ban 55 5 v1126 := viaSmall (by decide +kernel) (by decide)
def t389 : ℕ := 0x2614c298530a61000fffffffffff
def v1127 : List ℕ := [t98,t88,t89,t90,t389,t91]
theorem b1188 : Ban 55 5 v1127 := viaSmall (by decide +kernel) (by decide)
def t390 : ℕ := 0x100200400801000ffe000007ff
def v1128 : List ℕ := [t390,t98,t88,t89,t90,t91]
theorem b1189 : Ban 55 5 v1128 := viaSmall (by decide +kernel) (by decide)
def v1129 : List ℕ := [t98,t88,t89,t103,t90,t91]
theorem b1190 : Ban 55 5 v1129 := viaSmall (by decide +kernel) (by decide)
def v1130 : List ℕ := [t104,t98,t88,t89,t90,t91]
theorem b1191 : Ban 55 5 v1130 := viaSmall (by decide +kernel) (by decide)
def t391 : ℕ := 0x381702e05c0b817ffffe003fffff
def v1131 : List ℕ := [t98,t88,t89,t90,t91,t391]
theorem b1192 : Ban 55 5 v1131 := viaSmall (by decide +kernel) (by decide)
def t392 : ℕ := 0x100200400801000000003fffff
def v1132 : List ℕ := [t392,t98,t88,t89,t90,t91]
theorem b1193 : Ban 55 5 v1132 := viaSmall (by decide +kernel) (by decide)
def v1133 : List ℕ := [t98,t88,t89,t90,t107,t91]
theorem b1194 : Ban 55 5 v1133 := viaSmall (by decide +kernel) (by decide)
def v1134 : List ℕ := [t98,t108,t88,t89,t90,t91]
theorem b1195 : Ban 55 5 v1134 := viaSmall (by decide +kernel) (by decide)
def v1135 : List ℕ := [t98,t88,t109,t90,t91]
theorem b1196 : Ban 55 5 v1135 := viaSmall (by decide +kernel) (by decide)
def v1136 : List ℕ := [t98,t88,t89,t109,t90,t91]
theorem b1197 : Ban 55 5 v1136 := viaSmall (by decide +kernel) (by decide)
def v1137 : List ℕ := [t98,t110,t89,t90,t91]
theorem b1198 : Ban 55 5 v1137 := viaSmall (by decide +kernel) (by decide)
def v1138 : List ℕ := [t98,t110,t88,t89,t90,t91]
theorem b1199 : Ban 55 5 v1138 := viaSmall (by decide +kernel) (by decide)
def v1139 : List ℕ := [t98,t88,t111,t90,t91]
theorem b1200 : Ban 55 5 v1139 := viaSmall (by decide +kernel) (by decide)
def v1140 : List ℕ := [t98,t88,t111,t89,t90,t91]
theorem b1201 : Ban 55 5 v1140 := viaSmall (by decide +kernel) (by decide)
def v1141 : List ℕ := [t98,t112,t88,t89,t90,t91]
theorem b1202 : Ban 55 5 v1141 := viaSmall (by decide +kernel) (by decide)
def v1142 : List ℕ := [t98,t88,t89,t113,t91]
theorem b1203 : Ban 55 5 v1142 := viaSmall (by decide +kernel) (by decide)
def v1143 : List ℕ := [t98,t89,t90,t113,t91]
theorem b1204 : Ban 55 5 v1143 := viaSmall (by decide +kernel) (by decide)
def v1144 : List ℕ := [t98,t88,t89,t90,t113,t91]
theorem b1205 : Ban 55 5 v1144 := viaSmall (by decide +kernel) (by decide)
def v1145 : List ℕ := [t98,t114,t88,t89,t90,t91]
theorem b1206 : Ban 55 5 v1145 := viaSmall (by decide +kernel) (by decide)
def v1146 : List ℕ := [t98,t88,t89,t115,t90,t91]
theorem b1207 : Ban 55 5 v1146 := viaSmall (by decide +kernel) (by decide)
def v1147 : List ℕ := [t116,t98,t88,t89,t90,t91]
theorem b1208 : Ban 55 5 v1147 := viaSmall (by decide +kernel) (by decide)
def v1148 : List ℕ := [t98,t88,t89,t90,t91,t117]
theorem b1209 : Ban 55 5 v1148 := viaSmall (by decide +kernel) (by decide)
def v1149 : List ℕ := [t98,t118,t88,t89,t90,t91]
theorem b1210 : Ban 55 5 v1149 := viaSmall (by decide +kernel) (by decide)
def v1150 : List ℕ := [t98,t88,t89,t90,t119,t91]
theorem b1211 : Ban 55 5 v1150 := viaSmall (by decide +kernel) (by decide)
def v1151 : List ℕ := [t120,t98,t88,t90,t91]
theorem b1212 : Ban 55 5 v1151 := viaSmall (by decide +kernel) (by decide)
def v1152 : List ℕ := [t120,t98,t88,t89,t90,t91]
theorem b1213 : Ban 55 5 v1152 := viaSmall (by decide +kernel) (by decide)
def v1153 : List ℕ := [t98,t88,t89,t90,t121,t91]
theorem b1214 : Ban 55 5 v1153 := viaSmall (by decide +kernel) (by decide)
def v1154 : List ℕ := [t98,t88,t122,t89,t90,t91]
theorem b1215 : Ban 55 5 v1154 := viaSmall (by decide +kernel) (by decide)
def v1155 : List ℕ := [t98,t88,t123,t90,t91]
theorem b1216 : Ban 55 5 v1155 := viaSmall (by decide +kernel) (by decide)
def v1156 : List ℕ := [t98,t88,t89,t123,t90,t91]
theorem b1217 : Ban 55 5 v1156 := viaSmall (by decide +kernel) (by decide)
def v1157 : List ℕ := [t98,t88,t124,t89,t90,t91]
theorem b1218 : Ban 55 5 v1157 := viaSmall (by decide +kernel) (by decide)
def v1158 : List ℕ := [t98,t88,t89,t90,t125]
theorem b1219 : Ban 55 5 v1158 := viaSmall (by decide +kernel) (by decide)
def v1159 : List ℕ := [t98,t88,t90,t91,t125]
theorem b1220 : Ban 55 5 v1159 := viaSmall (by decide +kernel) (by decide)
def v1160 : List ℕ := [t98,t88,t89,t90,t91,t125]
theorem b1221 : Ban 55 5 v1160 := viaSmall (by decide +kernel) (by decide)
def v1161 : List ℕ := [t98,t126,t88,t90,t91]
theorem b1222 : Ban 55 5 v1161 := viaSmall (by decide +kernel) (by decide)
def v1162 : List ℕ := [t98,t126,t88,t89,t90,t91]
theorem b1223 : Ban 55 5 v1162 := viaSmall (by decide +kernel) (by decide)
def v1163 : List ℕ := [t98,t88,t89,t90,t127]
theorem b1224 : Ban 55 5 v1163 := viaSmall (by decide +kernel) (by decide)
def v1164 : List ℕ := [t98,t88,t89,t90,t127,t91]
theorem b1225 : Ban 55 5 v1164 := viaSmall (by decide +kernel) (by decide)
def v1165 : List ℕ := [t98,t88,t89,t128,t90,t91]
theorem b1226 : Ban 55 5 v1165 := viaSmall (by decide +kernel) (by decide)
def v1166 : List ℕ := [t98,t88,t89,t90,t129]
theorem b1227 : Ban 55 5 v1166 := viaSmall (by decide +kernel) (by decide)
def v1167 : List ℕ := [t98,t88,t89,t91,t129]
theorem b1228 : Ban 55 5 v1167 := viaSmall (by decide +kernel) (by decide)
def v1168 : List ℕ := [t98,t88,t89,t90,t91,t129]
theorem b1229 : Ban 55 5 v1168 := viaSmall (by decide +kernel) (by decide)
def v1169 : List ℕ := [t98,t88,t130,t89,t91]
theorem b1230 : Ban 55 5 v1169 := viaSmall (by decide +kernel) (by decide)
def v1170 : List ℕ := [t98,t88,t130,t89,t90,t91]
theorem b1231 : Ban 55 5 v1170 := viaSmall (by decide +kernel) (by decide)
def v1171 : List ℕ := [t98,t88,t89,t131,t90]
theorem b1232 : Ban 55 5 v1171 := viaSmall (by decide +kernel) (by decide)
def v1172 : List ℕ := [t98,t88,t89,t131,t90,t91]
theorem b1233 : Ban 55 5 v1172 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1234 : Ban 55 6 v117 := viaBranch (ws := [v1120,v1121,v1122,v1123,v1124,v115,v1125,v1126,v1127,v1128,v1129,v1130,v1131,v1132,v1133,v1134,v1135,v544,v1136,v1137,v1138,v1139,v1140,v1141,v1142,v1143,v1144,v892,v1145,v950,v1146,v1147,v1148,v1149,v1150,v1151,v1152,v1153,v1154,v1155,v1156,v1157,v1158,v1159,v1160,v1161,v1162,v1163,v1164,v1165,v1166,v1167,v1168,v1169,v1170,v1171,v1172]) (consBan b1181 (consBan b1182 (consBan b1183 (consBan b1184 (consBan b1185 (consBan b112 (consBan b1186 (consBan b1187 (consBan b1188 (consBan b1189 (consBan b1190 (consBan b1191 (consBan b1192 (consBan b1193 (consBan b1194 (consBan b1195 (consBan b1196 (consBan b548 (consBan b1197 (consBan b1198 (consBan b1199 (consBan b1200 (consBan b1201 (consBan b1202 (consBan b1203 (consBan b1204 (consBan b1205 (consBan b899 (consBan b1206 (consBan b958 (consBan b1207 (consBan b1208 (consBan b1209 (consBan b1210 (consBan b1211 (consBan b1212 (consBan b1213 (consBan b1214 (consBan b1215 (consBan b1216 (consBan b1217 (consBan b1218 (consBan b1219 (consBan b1220 (consBan b1221 (consBan b1222 (consBan b1223 (consBan b1224 (consBan b1225 (consBan b1226 (consBan b1227 (consBan b1228 (consBan b1229 (consBan b1230 (consBan b1231 (consBan b1232 (consBan b1233 (nilBan 55 5)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w48 : Wide 55 6 v117 := viaSub (ws := [v117]) (consBan b1234 (nilBan 55 6)) (by decide) (by decide +kernel)
theorem b1235 : Ban 220 8 v1119 := viaCut p127_61 w48 (by decide) (by decide +kernel) (by decide +kernel)
def v1173 : List ℕ := [t0,t1,t2,t3,t173,t4,t5,t6]
theorem b1236 : Ban 220 8 v1173 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1174 : List ℕ := [t0,t1,t174,t2,t3,t4,t5,t6]
theorem b1237 : Ban 220 8 v1174 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1175 : List ℕ := [t0,t1,t2,t3,t4,t175,t6]
def v1176 : List ℕ := [t92,t87,t88,t89,t90,t125]
theorem b1238 : Ban 55 5 v1176 := viaSmall (by decide +kernel) (by decide)
def v1177 : List ℕ := [t87,t88,t93,t89,t90,t125]
theorem b1239 : Ban 55 5 v1177 := viaSmall (by decide +kernel) (by decide)
def v1178 : List ℕ := [t94,t87,t88,t89,t90,t125]
theorem b1240 : Ban 55 5 v1178 := viaSmall (by decide +kernel) (by decide)
def v1179 : List ℕ := [t87,t95,t88,t89,t90,t125]
theorem b1241 : Ban 55 5 v1179 := viaSmall (by decide +kernel) (by decide)
def v1180 : List ℕ := [t96,t87,t88,t89,t90,t125]
theorem b1242 : Ban 55 5 v1180 := viaSmall (by decide +kernel) (by decide)
def v1181 : List ℕ := [t88,t89,t97,t90,t125]
theorem b1243 : Ban 55 5 v1181 := viaSmall (by decide +kernel) (by decide)
def v1182 : List ℕ := [t87,t88,t89,t97,t90,t125]
theorem b1244 : Ban 55 5 v1182 := viaSmall (by decide +kernel) (by decide)
def v1183 : List ℕ := [t98,t87,t88,t89,t90,t125]
theorem b1245 : Ban 55 5 v1183 := viaSmall (by decide +kernel) (by decide)
def v1184 : List ℕ := [t87,t88,t99,t89,t90,t125]
theorem b1246 : Ban 55 5 v1184 := viaSmall (by decide +kernel) (by decide)
def v1185 : List ℕ := [t100,t87,t88,t89,t90,t125]
theorem b1247 : Ban 55 5 v1185 := viaSmall (by decide +kernel) (by decide)
def v1186 : List ℕ := [t87,t88,t89,t90,t101,t125]
theorem b1248 : Ban 55 5 v1186 := viaSmall (by decide +kernel) (by decide)
def v1187 : List ℕ := [t102,t87,t88,t89,t90,t125]
theorem b1249 : Ban 55 5 v1187 := viaSmall (by decide +kernel) (by decide)
def v1188 : List ℕ := [t87,t88,t89,t103,t90,t125]
theorem b1250 : Ban 55 5 v1188 := viaSmall (by decide +kernel) (by decide)
def t393 : ℕ := 0x400801002004000ffe00000000
def v1189 : List ℕ := [t393,t87,t88,t89,t90,t125]
theorem b1251 : Ban 55 5 v1189 := viaSmall (by decide +kernel) (by decide)
def t394 : ℕ := 0x39772ee5dcbb977fffffffffffff
def v1190 : List ℕ := [t87,t88,t89,t90,t125,t394]
theorem b1252 : Ban 55 5 v1190 := viaSmall (by decide +kernel) (by decide)
def v1191 : List ℕ := [t392,t87,t88,t89,t90,t125]
theorem b1253 : Ban 55 5 v1191 := viaSmall (by decide +kernel) (by decide)
def t395 : ℕ := 0x392724e49c93927ff001ffc00000
def v1192 : List ℕ := [t87,t88,t89,t90,t395,t125]
theorem b1254 : Ban 55 5 v1192 := viaSmall (by decide +kernel) (by decide)
def v1193 : List ℕ := [t87,t108,t88,t89,t90,t125]
theorem b1255 : Ban 55 5 v1193 := viaSmall (by decide +kernel) (by decide)
def v1194 : List ℕ := [t87,t88,t89,t109,t90,t125]
theorem b1256 : Ban 55 5 v1194 := viaSmall (by decide +kernel) (by decide)
def v1195 : List ℕ := [t87,t110,t89,t90,t125]
theorem b1257 : Ban 55 5 v1195 := viaSmall (by decide +kernel) (by decide)
def v1196 : List ℕ := [t87,t110,t88,t89,t90,t125]
theorem b1258 : Ban 55 5 v1196 := viaSmall (by decide +kernel) (by decide)
def v1197 : List ℕ := [t87,t88,t111,t89,t90,t125]
theorem b1259 : Ban 55 5 v1197 := viaSmall (by decide +kernel) (by decide)
def v1198 : List ℕ := [t87,t112,t88,t89,t90,t125]
theorem b1260 : Ban 55 5 v1198 := viaSmall (by decide +kernel) (by decide)
def v1199 : List ℕ := [t87,t88,t89,t113,t125]
theorem b1261 : Ban 55 5 v1199 := viaSmall (by decide +kernel) (by decide)
def v1200 : List ℕ := [t87,t89,t90,t113,t125]
theorem b1262 : Ban 55 5 v1200 := viaSmall (by decide +kernel) (by decide)
def v1201 : List ℕ := [t87,t88,t89,t90,t113,t125]
theorem b1263 : Ban 55 5 v1201 := viaSmall (by decide +kernel) (by decide)
def v1202 : List ℕ := [t87,t114,t88,t89,t90,t125]
theorem b1264 : Ban 55 5 v1202 := viaSmall (by decide +kernel) (by decide)
def v1203 : List ℕ := [t87,t88,t89,t115,t90,t125]
theorem b1265 : Ban 55 5 v1203 := viaSmall (by decide +kernel) (by decide)
def t396 : ℕ := 0x10020040080107ff00000000000
def v1204 : List ℕ := [t87,t396,t88,t89,t90,t125]
theorem b1266 : Ban 55 5 v1204 := viaSmall (by decide +kernel) (by decide)
def v1205 : List ℕ := [t87,t88,t89,t90,t125,t289]
theorem b1267 : Ban 55 5 v1205 := viaSmall (by decide +kernel) (by decide)
def t397 : ℕ := 0x4809012024048000000000007ff
def v1206 : List ℕ := [t87,t397,t88,t89,t90,t125]
theorem b1268 : Ban 55 5 v1206 := viaSmall (by decide +kernel) (by decide)
def t398 : ℕ := 0x38670ce19c3386000fffffc00000
def v1207 : List ℕ := [t87,t88,t89,t90,t398,t125]
theorem b1269 : Ban 55 5 v1207 := viaSmall (by decide +kernel) (by decide)
def v1208 : List ℕ := [t120,t87,t88,t89,t90,t125]
theorem b1270 : Ban 55 5 v1208 := viaSmall (by decide +kernel) (by decide)
def v1209 : List ℕ := [t87,t88,t89,t90,t121,t125]
theorem b1271 : Ban 55 5 v1209 := viaSmall (by decide +kernel) (by decide)
def v1210 : List ℕ := [t87,t88,t122,t89,t90,t125]
theorem b1272 : Ban 55 5 v1210 := viaSmall (by decide +kernel) (by decide)
def v1211 : List ℕ := [t87,t88,t89,t123,t90,t125]
theorem b1273 : Ban 55 5 v1211 := viaSmall (by decide +kernel) (by decide)
def v1212 : List ℕ := [t87,t88,t90,t127,t125]
theorem b1274 : Ban 55 5 v1212 := viaSmall (by decide +kernel) (by decide)
def v1213 : List ℕ := [t87,t88,t89,t90,t127,t125]
theorem b1275 : Ban 55 5 v1213 := viaSmall (by decide +kernel) (by decide)
def t399 : ℕ := 0x20040080100200000001ffc00000
def v1214 : List ℕ := [t87,t88,t89,t399,t90,t125]
theorem b1276 : Ban 55 5 v1214 := viaSmall (by decide +kernel) (by decide)
def t400 : ℕ := 0x3f67ecfd9fb3f67ffffffffff800
def v1215 : List ℕ := [t87,t88,t89,t90,t400]
theorem b1277 : Ban 55 5 v1215 := viaSmall (by decide +kernel) (by decide)
def v1216 : List ℕ := [t87,t88,t89,t90,t125,t400]
theorem b1278 : Ban 55 5 v1216 := viaSmall (by decide +kernel) (by decide)
def t401 : ℕ := 0x600c018030060000000003ff800
def v1217 : List ℕ := [t87,t88,t401,t89,t90,t125]
theorem b1279 : Ban 55 5 v1217 := viaSmall (by decide +kernel) (by decide)
def t402 : ℕ := 0x19632c658cb1967ffffe00000000
def v1218 : List ℕ := [t87,t88,t89,t402,t90]
theorem b1280 : Ban 55 5 v1218 := viaSmall (by decide +kernel) (by decide)
def v1219 : List ℕ := [t87,t88,t89,t402,t90,t125]
theorem b1281 : Ban 55 5 v1219 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1282 : Ban 55 6 v156 := viaBranch (ws := [v1176,v1177,v1178,v1179,v1180,v1181,v1182,v1158,v1183,v1184,v1185,v1186,v1187,v1188,v1189,v1190,v1191,v1192,v1193,v566,v1194,v1195,v1196,v1197,v1198,v1199,v1200,v1201,v925,v1202,v982,v1203,v1204,v1205,v1206,v1207,v1208,v1209,v1210,v1211,v161,v1212,v1213,v1214,v1215,v1216,v1217,v1218,v1219]) (consBan b1238 (consBan b1239 (consBan b1240 (consBan b1241 (consBan b1242 (consBan b1243 (consBan b1244 (consBan b1219 (consBan b1245 (consBan b1246 (consBan b1247 (consBan b1248 (consBan b1249 (consBan b1250 (consBan b1251 (consBan b1252 (consBan b1253 (consBan b1254 (consBan b1255 (consBan b570 (consBan b1256 (consBan b1257 (consBan b1258 (consBan b1259 (consBan b1260 (consBan b1261 (consBan b1262 (consBan b1263 (consBan b932 (consBan b1264 (consBan b990 (consBan b1265 (consBan b1266 (consBan b1267 (consBan b1268 (consBan b1269 (consBan b1270 (consBan b1271 (consBan b1272 (consBan b1273 (consBan b158 (consBan b1274 (consBan b1275 (consBan b1276 (consBan b1277 (consBan b1278 (consBan b1279 (consBan b1280 (consBan b1281 (nilBan 55 5)))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w49 : Wide 55 6 v156 := viaSub (ws := [v156]) (consBan b1282 (nilBan 55 6)) (by decide) (by decide +kernel)
theorem b1283 : Ban 220 8 v1175 := viaCut p127_61 w49 (by decide) (by decide +kernel) (by decide +kernel)
def v1220 : List ℕ := [t0,t1,t3,t4,t5,t175,t6]
def v1221 : List ℕ := [t92,t87,t88,t90,t91,t125]
theorem b1284 : Ban 55 5 v1221 := viaSmall (by decide +kernel) (by decide)
def v1222 : List ℕ := [t87,t88,t93,t90,t91,t125]
theorem b1285 : Ban 55 5 v1222 := viaSmall (by decide +kernel) (by decide)
def v1223 : List ℕ := [t94,t87,t88,t90,t91,t125]
theorem b1286 : Ban 55 5 v1223 := viaSmall (by decide +kernel) (by decide)
def v1224 : List ℕ := [t87,t95,t88,t90,t91,t125]
theorem b1287 : Ban 55 5 v1224 := viaSmall (by decide +kernel) (by decide)
def v1225 : List ℕ := [t100,t87,t88,t90,t91,t125]
theorem b1288 : Ban 55 5 v1225 := viaSmall (by decide +kernel) (by decide)
def v1226 : List ℕ := [t87,t88,t90,t101,t91,t125]
theorem b1289 : Ban 55 5 v1226 := viaSmall (by decide +kernel) (by decide)
def v1227 : List ℕ := [t102,t87,t88,t90,t91,t125]
theorem b1290 : Ban 55 5 v1227 := viaSmall (by decide +kernel) (by decide)
def v1228 : List ℕ := [t87,t88,t103,t90,t91,t125]
theorem b1291 : Ban 55 5 v1228 := viaSmall (by decide +kernel) (by decide)
def v1229 : List ℕ := [t104,t87,t88,t90,t91,t125]
theorem b1292 : Ban 55 5 v1229 := viaSmall (by decide +kernel) (by decide)
def v1230 : List ℕ := [t87,t88,t90,t91,t105,t125]
theorem b1293 : Ban 55 5 v1230 := viaSmall (by decide +kernel) (by decide)
def v1231 : List ℕ := [t106,t87,t88,t90,t91,t125]
theorem b1294 : Ban 55 5 v1231 := viaSmall (by decide +kernel) (by decide)
def v1232 : List ℕ := [t87,t88,t90,t107,t91,t125]
theorem b1295 : Ban 55 5 v1232 := viaSmall (by decide +kernel) (by decide)
def v1233 : List ℕ := [t393,t87,t88,t90,t91,t125]
theorem b1296 : Ban 55 5 v1233 := viaSmall (by decide +kernel) (by decide)
def v1234 : List ℕ := [t87,t88,t90,t91,t394]
theorem b1297 : Ban 55 5 v1234 := viaSmall (by decide +kernel) (by decide)
def v1235 : List ℕ := [t87,t88,t90,t91,t125,t394]
theorem b1298 : Ban 55 5 v1235 := viaSmall (by decide +kernel) (by decide)
def v1236 : List ℕ := [t392,t87,t88,t90,t91,t125]
theorem b1299 : Ban 55 5 v1236 := viaSmall (by decide +kernel) (by decide)
def v1237 : List ℕ := [t87,t88,t90,t91,t395]
theorem b1300 : Ban 55 5 v1237 := viaSmall (by decide +kernel) (by decide)
def v1238 : List ℕ := [t87,t88,t90,t91,t395,t125]
theorem b1301 : Ban 55 5 v1238 := viaSmall (by decide +kernel) (by decide)
def v1239 : List ℕ := [t87,t112,t88,t90,t91,t125]
theorem b1302 : Ban 55 5 v1239 := viaSmall (by decide +kernel) (by decide)
def v1240 : List ℕ := [t87,t88,t113,t91,t125]
theorem b1303 : Ban 55 5 v1240 := viaSmall (by decide +kernel) (by decide)
def v1241 : List ℕ := [t87,t90,t113,t91,t125]
theorem b1304 : Ban 55 5 v1241 := viaSmall (by decide +kernel) (by decide)
def v1242 : List ℕ := [t87,t88,t90,t113,t91,t125]
theorem b1305 : Ban 55 5 v1242 := viaSmall (by decide +kernel) (by decide)
def v1243 : List ℕ := [t87,t114,t88,t90,t91,t125]
theorem b1306 : Ban 55 5 v1243 := viaSmall (by decide +kernel) (by decide)
def v1244 : List ℕ := [t87,t88,t115,t90,t91,t125]
theorem b1307 : Ban 55 5 v1244 := viaSmall (by decide +kernel) (by decide)
def v1245 : List ℕ := [t116,t87,t88,t90,t91,t125]
theorem b1308 : Ban 55 5 v1245 := viaSmall (by decide +kernel) (by decide)
def v1246 : List ℕ := [t87,t88,t90,t91,t125,t117]
theorem b1309 : Ban 55 5 v1246 := viaSmall (by decide +kernel) (by decide)
def v1247 : List ℕ := [t87,t118,t88,t90,t91,t125]
theorem b1310 : Ban 55 5 v1247 := viaSmall (by decide +kernel) (by decide)
def v1248 : List ℕ := [t87,t88,t90,t119,t91,t125]
theorem b1311 : Ban 55 5 v1248 := viaSmall (by decide +kernel) (by decide)
def v1249 : List ℕ := [t87,t396,t88,t90,t91,t125]
theorem b1312 : Ban 55 5 v1249 := viaSmall (by decide +kernel) (by decide)
def v1250 : List ℕ := [t87,t88,t90,t91,t125,t289]
theorem b1313 : Ban 55 5 v1250 := viaSmall (by decide +kernel) (by decide)
def v1251 : List ℕ := [t87,t397,t88,t90,t91,t125]
theorem b1314 : Ban 55 5 v1251 := viaSmall (by decide +kernel) (by decide)
def v1252 : List ℕ := [t87,t88,t90,t91,t398]
theorem b1315 : Ban 55 5 v1252 := viaSmall (by decide +kernel) (by decide)
def v1253 : List ℕ := [t87,t88,t90,t91,t398,t125]
theorem b1316 : Ban 55 5 v1253 := viaSmall (by decide +kernel) (by decide)
def v1254 : List ℕ := [t87,t88,t128,t90,t91,t125]
theorem b1317 : Ban 55 5 v1254 := viaSmall (by decide +kernel) (by decide)
def v1255 : List ℕ := [t87,t88,t91,t125,t129]
theorem b1318 : Ban 55 5 v1255 := viaSmall (by decide +kernel) (by decide)
def v1256 : List ℕ := [t87,t88,t90,t91,t125,t129]
theorem b1319 : Ban 55 5 v1256 := viaSmall (by decide +kernel) (by decide)
def v1257 : List ℕ := [t87,t88,t130,t91,t125]
theorem b1320 : Ban 55 5 v1257 := viaSmall (by decide +kernel) (by decide)
def v1258 : List ℕ := [t87,t88,t130,t90,t91,t125]
theorem b1321 : Ban 55 5 v1258 := viaSmall (by decide +kernel) (by decide)
def v1259 : List ℕ := [t87,t88,t131,t90,t91,t125]
theorem b1322 : Ban 55 5 v1259 := viaSmall (by decide +kernel) (by decide)
def v1260 : List ℕ := [t87,t88,t399,t90,t91]
theorem b1323 : Ban 55 5 v1260 := viaSmall (by decide +kernel) (by decide)
def v1261 : List ℕ := [t87,t88,t399,t90,t91,t125]
theorem b1324 : Ban 55 5 v1261 := viaSmall (by decide +kernel) (by decide)
def v1262 : List ℕ := [t87,t88,t90,t91,t125,t400]
theorem b1325 : Ban 55 5 v1262 := viaSmall (by decide +kernel) (by decide)
def v1263 : List ℕ := [t87,t88,t401,t90,t91]
theorem b1326 : Ban 55 5 v1263 := viaSmall (by decide +kernel) (by decide)
def v1264 : List ℕ := [t87,t88,t401,t90,t91,t125]
theorem b1327 : Ban 55 5 v1264 := viaSmall (by decide +kernel) (by decide)
def v1265 : List ℕ := [t87,t88,t402,t90,t91,t125]
theorem b1328 : Ban 55 5 v1265 := viaSmall (by decide +kernel) (by decide)
def v1266 : List ℕ := [t87,t126,t88,t90,t125]
theorem b1329 : Ban 55 5 v1266 := viaSmall (by decide +kernel) (by decide)
def v1267 : List ℕ := [t87,t126,t88,t90,t91,t125]
theorem b1330 : Ban 55 5 v1267 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1331 : Ban 55 6 v157 := viaBranch (ws := [v1221,v1222,v1223,v1224,v1225,v1226,v1227,v1228,v1229,v1230,v1231,v1232,v1233,v1234,v1235,v1236,v1237,v1238,v1239,v1240,v1241,v1242,v926,v1243,v983,v1244,v1245,v1246,v1247,v1248,v1249,v527,v1250,v1251,v1252,v1253,v1254,v1255,v1256,v1257,v1258,v1259,v1260,v1261,v1262,v1263,v1264,v1265,v159,v1266,v1267]) (consBan b1284 (consBan b1285 (consBan b1286 (consBan b1287 (consBan b1288 (consBan b1289 (consBan b1290 (consBan b1291 (consBan b1292 (consBan b1293 (consBan b1294 (consBan b1295 (consBan b1296 (consBan b1297 (consBan b1298 (consBan b1299 (consBan b1300 (consBan b1301 (consBan b1302 (consBan b1303 (consBan b1304 (consBan b1305 (consBan b933 (consBan b1306 (consBan b991 (consBan b1307 (consBan b1308 (consBan b1309 (consBan b1310 (consBan b1311 (consBan b1312 (consBan b530 (consBan b1313 (consBan b1314 (consBan b1315 (consBan b1316 (consBan b1317 (consBan b1318 (consBan b1319 (consBan b1320 (consBan b1321 (consBan b1322 (consBan b1323 (consBan b1324 (consBan b1325 (consBan b1326 (consBan b1327 (consBan b1328 (consBan b156 (consBan b1329 (consBan b1330 (nilBan 55 5)))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w50 : Wide 55 6 v157 := viaSub (ws := [v157]) (consBan b1331 (nilBan 55 6)) (by decide) (by decide +kernel)
theorem b1332 : Ban 220 8 v1220 := viaCut p127_61 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v1268 : List ℕ := [t0,t1,t2,t3,t4,t5,t175,t6]
theorem b1333 : Ban 220 8 v1268 := viaCut p127_82 w34 (by decide) (by decide +kernel) (by decide +kernel)
def v1269 : List ℕ := [t0,t176,t1,t3,t4,t5,t6]
def v1270 : List ℕ := [t133,t0,t176,t1,t3,t4,t5,t6]
theorem b1334 : Ban 220 7 v1270 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t403 : ℕ := 0xefc00efc00efc00efc00efc00efc00efc00efc00efc00efc00efc0000000000ffffffffff00000fffff00000ffffffffff0000000000
def v1271 : List ℕ := [t403,t1,t3,t4,t5,t6]
def v1272 : List ℕ := [t143,t403,t1,t3,t4,t5,t6]
theorem b1335 : Ban 220 6 v1272 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t404 : ℕ := 0x2ffc02ffc02ffc02ffc02ffc02ffc02ffc02ffc02ffc02ffc02ffc00000fffffffffffffffffffffffff00000ffffffffff00000fffff
def v1273 : List ℕ := [t403,t404,t3,t4,t5,t6]
theorem b1336 : Ban 220 6 v1273 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1274 : List ℕ := [t1,t404,t3,t4,t5,t6]
theorem b1337 : Ban 220 6 v1274 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1275 : List ℕ := [t403,t1,t404,t3,t4,t5,t6]
theorem b1338 : Ban 220 6 v1275 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t405 : ℕ := 0xfc000fc000fc000fc000fc000fc000fc000fc000fc000fc000fc0000000000ffffffffff00000fffff00000ffffffffff0000000000
def v1276 : List ℕ := [t405,t1,t3,t4,t5,t6]
theorem b1339 : Ban 220 6 v1276 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1277 : List ℕ := [t405,t403,t1,t3,t4,t5,t6]
theorem b1340 : Ban 220 6 v1277 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1278 : List ℕ := [t403,t145,t3,t4,t5,t6]
theorem b1341 : Ban 220 6 v1278 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1279 : List ℕ := [t403,t145,t1,t3,t4,t5,t6]
theorem b1342 : Ban 220 6 v1279 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1280 : List ℕ := [t180,t403,t1,t3,t4,t5,t6]
theorem b1343 : Ban 220 6 v1280 := viaCut p127_114 w9 (by decide) (by decide +kernel) (by decide +kernel)
def t406 : ℕ := 0x13efc13efc13efc13efc13efc13efc13efc13efc13efc13efc13efcfffff00000ffffffffff00000fffff00000fffffffffffffff00000
def v1281 : List ℕ := [t403,t1,t3,t406,t4,t5,t6]
theorem b1344 : Ban 220 6 v1281 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def t407 : ℕ := 0xefc00efc00efc00efc00efc00efc00efc00efc00efc00efc00efc0000000000ffffffffff00000fffff0000000000000000000000000
def v1282 : List ℕ := [t407,t403,t1,t3,t4,t5,t6]
theorem b1345 : Ban 220 6 v1282 := viaCut p127_114 w11 (by decide) (by decide +kernel) (by decide +kernel)
def v1283 : List ℕ := [t403,t1,t185,t3,t4,t5,t6]
theorem b1346 : Ban 220 6 v1283 := viaCut p127_114 w12 (by decide) (by decide +kernel) (by decide +kernel)
def v1284 : List ℕ := [t187,t403,t1,t3,t4,t5,t6]
theorem b1347 : Ban 220 6 v1284 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t408 : ℕ := 0x40efe40efe40efe40efe40efe40efe40efe40efe40efe40efe40efe0000000000ffffffffff00000ffffffffffffffffffffffffffffff
def v1285 : List ℕ := [t403,t1,t3,t408,t5,t6]
theorem b1348 : Ban 220 6 v1285 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1286 : List ℕ := [t1,t3,t4,t408,t5,t6]
theorem b1349 : Ban 220 6 v1286 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1287 : List ℕ := [t403,t1,t3,t4,t408,t5,t6]
theorem b1350 : Ban 220 6 v1287 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t409 : ℕ := 0xe5400e5400e5400e5400e5400e5400e5400e5400e5400e5400e540000000000ffffffffff00000fffff00000ffffffffff0000000000
def v1288 : List ℕ := [t409,t1,t3,t4,t5,t6]
theorem b1351 : Ban 220 6 v1288 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1289 : List ℕ := [t409,t403,t1,t3,t4,t5,t6]
theorem b1352 : Ban 220 6 v1289 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1290 : List ℕ := [t403,t1,t3,t190,t5,t6]
theorem b1353 : Ban 220 6 v1290 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1291 : List ℕ := [t403,t1,t3,t190,t4,t5,t6]
theorem b1354 : Ban 220 6 v1291 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1292 : List ℕ := [t191,t403,t1,t3,t4,t5,t6]
theorem b1355 : Ban 220 6 v1292 := viaCut p127_114 w13 (by decide) (by decide +kernel) (by decide +kernel)
def v1293 : List ℕ := [t403,t1,t3,t4,t5,t193,t6]
theorem b1356 : Ban 220 6 v1293 := viaCut p127_114 w14 (by decide) (by decide +kernel) (by decide +kernel)
def v1294 : List ℕ := [t245,t403,t1,t3,t4,t5,t6]
theorem b1357 : Ban 220 6 v1294 := viaCut p127_114 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v1295 : List ℕ := [t403,t1,t3,t4,t275,t5,t6]
theorem b1358 : Ban 220 6 v1295 := viaCut p127_114 w16 (by decide) (by decide +kernel) (by decide +kernel)
def v1296 : List ℕ := [t199,t403,t1,t3,t4,t5,t6]
theorem b1359 : Ban 220 6 v1296 := viaCut p127_114 w17 (by decide) (by decide +kernel) (by decide +kernel)
def t410 : ℕ := 0xe0efce0efce0efce0efce0efce0efce0efce0efce0efce0efce0efcffffffffffffffffffff00000fffff00000ffffffffff0000000000
def v1297 : List ℕ := [t403,t1,t3,t4,t5,t6,t410]
theorem b1360 : Ban 220 6 v1297 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def t411 : ℕ := 0xefc00efc00efc00efc00efc00efc00efc00efc00efc00efc00efc0000000000000000000000000fffff00000ffffffffff0000000000
def v1298 : List ℕ := [t411,t403,t1,t3,t4,t5,t6]
theorem b1361 : Ban 220 6 v1298 := viaCut p127_114 w18 (by decide) (by decide +kernel) (by decide +kernel)
def v1299 : List ℕ := [t403,t1,t3,t4,t5,t204,t6]
theorem b1362 : Ban 220 6 v1299 := viaCut p127_114 w19 (by decide) (by decide +kernel) (by decide +kernel)
def v1300 : List ℕ := [t403,t147,t1,t3,t4,t5,t6]
theorem b1363 : Ban 220 6 v1300 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1301 : List ℕ := [t403,t1,t148,t4,t5,t6]
theorem b1364 : Ban 220 6 v1301 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1302 : List ℕ := [t403,t3,t148,t4,t5,t6]
theorem b1365 : Ban 220 6 v1302 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1303 : List ℕ := [t403,t1,t3,t148,t4,t5,t6]
theorem b1366 : Ban 220 6 v1303 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1304 : List ℕ := [t403,t149,t3,t4,t5,t6]
theorem b1367 : Ban 220 6 v1304 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1305 : List ℕ := [t403,t149,t1,t3,t4,t5,t6]
theorem b1368 : Ban 220 6 v1305 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1306 : List ℕ := [t403,t1,t150,t4,t5,t6]
theorem b1369 : Ban 220 6 v1306 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1307 : List ℕ := [t403,t1,t150,t3,t4,t5,t6]
theorem b1370 : Ban 220 6 v1307 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1308 : List ℕ := [t151,t403,t1,t3,t4,t5,t6]
theorem b1371 : Ban 220 6 v1308 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1309 : List ℕ := [t403,t1,t3,t4,t152,t5,t6]
theorem b1372 : Ban 220 6 v1309 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1310 : List ℕ := [t403,t153,t1,t3,t4,t5,t6]
theorem b1373 : Ban 220 6 v1310 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1311 : List ℕ := [t403,t1,t3,t154,t4,t5,t6]
theorem b1374 : Ban 220 6 v1311 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1312 : List ℕ := [t155,t403,t1,t3,t4,t5,t6]
theorem b1375 : Ban 220 6 v1312 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1313 : List ℕ := [t403,t1,t3,t4,t5,t156,t6]
theorem b1376 : Ban 220 6 v1313 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1314 : List ℕ := [t403,t157,t1,t3,t4,t5,t6]
theorem b1377 : Ban 220 6 v1314 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1315 : List ℕ := [t403,t1,t3,t4,t158,t5,t6]
theorem b1378 : Ban 220 6 v1315 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1316 : List ℕ := [t159,t403,t1,t3,t4,t5,t6]
theorem b1379 : Ban 220 6 v1316 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1317 : List ℕ := [t403,t1,t3,t4,t5,t6,t160]
theorem b1380 : Ban 220 6 v1317 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1318 : List ℕ := [t403,t161,t1,t3,t4,t5,t6]
theorem b1381 : Ban 220 6 v1318 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1319 : List ℕ := [t403,t1,t3,t4,t5,t162,t6]
theorem b1382 : Ban 220 6 v1319 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1320 : List ℕ := [t206,t403,t1,t3,t4,t5,t6]
theorem b1383 : Ban 220 6 v1320 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1321 : List ℕ := [t403,t1,t3,t4,t207,t5,t6]
theorem b1384 : Ban 220 6 v1321 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1322 : List ℕ := [t403,t1,t208,t3,t4,t5,t6]
theorem b1385 : Ban 220 6 v1322 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1323 : List ℕ := [t403,t1,t3,t209,t4,t5,t6]
theorem b1386 : Ban 220 6 v1323 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1324 : List ℕ := [t403,t1,t210,t3,t4,t5,t6]
theorem b1387 : Ban 220 6 v1324 := viaCut p127_114 w20 (by decide) (by decide +kernel) (by decide +kernel)
def v1325 : List ℕ := [t403,t1,t3,t4,t246,t6]
theorem b1388 : Ban 220 6 v1325 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1326 : List ℕ := [t403,t1,t4,t5,t246,t6]
theorem b1389 : Ban 220 6 v1326 := viaCut p127_114 w21 (by decide) (by decide +kernel) (by decide +kernel)
def v1327 : List ℕ := [t403,t1,t3,t4,t5,t246,t6]
theorem b1390 : Ban 220 6 v1327 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1328 : List ℕ := [t403,t1,t214,t4,t5,t6]
theorem b1391 : Ban 220 6 v1328 := viaCut p127_114 w22 (by decide) (by decide +kernel) (by decide +kernel)
def v1329 : List ℕ := [t403,t1,t214,t3,t4,t5,t6]
theorem b1392 : Ban 220 6 v1329 := viaCut p127_114 w23 (by decide) (by decide +kernel) (by decide +kernel)
def v1330 : List ℕ := [t403,t1,t3,t4,t247,t6]
theorem b1393 : Ban 220 6 v1330 := viaCut p127_114 w24 (by decide) (by decide +kernel) (by decide +kernel)
def v1331 : List ℕ := [t403,t1,t3,t4,t247,t5,t6]
theorem b1394 : Ban 220 6 v1331 := viaCut p127_114 w25 (by decide) (by decide +kernel) (by decide +kernel)
def v1332 : List ℕ := [t218,t403,t1,t3,t4,t5,t6]
theorem b1395 : Ban 220 6 v1332 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1333 : List ℕ := [t403,t1,t3,t4,t5,t6,t219]
theorem b1396 : Ban 220 6 v1333 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1334 : List ℕ := [t403,t1,t220,t3,t4,t5,t6]
theorem b1397 : Ban 220 6 v1334 := viaCut p127_114 w26 (by decide) (by decide +kernel) (by decide +kernel)
def v1335 : List ℕ := [t403,t1,t3,t4,t5,t222,t6]
theorem b1398 : Ban 220 6 v1335 := viaCut p127_114 w27 (by decide) (by decide +kernel) (by decide +kernel)
def v1336 : List ℕ := [t224,t403,t1,t3,t4,t5,t6]
theorem b1399 : Ban 220 6 v1336 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1337 : List ℕ := [t403,t1,t3,t4,t5,t248,t6]
theorem b1400 : Ban 220 6 v1337 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1338 : List ℕ := [t403,t1,t3,t226,t4,t5,t6]
theorem b1401 : Ban 220 6 v1338 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1339 : List ℕ := [t403,t1,t3,t4,t249,t5,t6]
theorem b1402 : Ban 220 6 v1339 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1340 : List ℕ := [t403,t1,t3,t228,t4,t5,t6]
theorem b1403 : Ban 220 6 v1340 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1341 : List ℕ := [t403,t1,t3,t4,t5,t229]
theorem b1404 : Ban 220 6 v1341 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1342 : List ℕ := [t403,t1,t3,t5,t6,t229]
theorem b1405 : Ban 220 6 v1342 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1343 : List ℕ := [t403,t1,t3,t4,t5,t6,t229]
theorem b1406 : Ban 220 6 v1343 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1344 : List ℕ := [t230,t403,t1,t3,t5,t6]
theorem b1407 : Ban 220 6 v1344 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1345 : List ℕ := [t230,t403,t1,t3,t4,t5,t6]
theorem b1408 : Ban 220 6 v1345 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1346 : List ℕ := [t403,t1,t3,t4,t5,t231]
theorem b1409 : Ban 220 6 v1346 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1347 : List ℕ := [t403,t1,t3,t4,t5,t231,t6]
theorem b1410 : Ban 220 6 v1347 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1348 : List ℕ := [t403,t1,t3,t4,t232,t5,t6]
theorem b1411 : Ban 220 6 v1348 := viaCut p127_114 w28 (by decide) (by decide +kernel) (by decide +kernel)
def v1349 : List ℕ := [t403,t1,t3,t4,t5,t250]
theorem b1412 : Ban 220 6 v1349 := viaCut p127_114 w29 (by decide) (by decide +kernel) (by decide +kernel)
def v1350 : List ℕ := [t403,t1,t3,t4,t6,t250]
theorem b1413 : Ban 220 6 v1350 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1351 : List ℕ := [t403,t1,t3,t4,t5,t6,t250]
theorem b1414 : Ban 220 6 v1351 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1352 : List ℕ := [t403,t1,t3,t251,t4,t6]
theorem b1415 : Ban 220 6 v1352 := viaCut p127_114 w30 (by decide) (by decide +kernel) (by decide +kernel)
def v1353 : List ℕ := [t403,t1,t3,t251,t4,t5,t6]
theorem b1416 : Ban 220 6 v1353 := viaCut p127_114 w31 (by decide) (by decide +kernel) (by decide +kernel)
def v1354 : List ℕ := [t403,t1,t3,t4,t238,t5]
theorem b1417 : Ban 220 6 v1354 := viaCut p127_114 w32 (by decide) (by decide +kernel) (by decide +kernel)
def v1355 : List ℕ := [t403,t1,t3,t4,t238,t5,t6]
theorem b1418 : Ban 220 6 v1355 := viaCut p127_114 w33 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1419 : Ban 220 7 v1271 := viaBranch (ws := [v1272,v1273,v1274,v1275,v1276,v1277,v1278,v1279,v1280,v1281,v1282,v1283,v1284,v1285,v1286,v1287,v1288,v1289,v1290,v1291,v1292,v1293,v1294,v1295,v1296,v1297,v1298,v1299,v1300,v1301,v1302,v1303,v1304,v1305,v1306,v1307,v1308,v1309,v1310,v1311,v1312,v1313,v1314,v1315,v1316,v1317,v1318,v1319,v1320,v1321,v1322,v1323,v1324,v1325,v1326,v1327,v1328,v1329,v1330,v1331,v1332,v1333,v1334,v1335,v1336,v1337,v1338,v1339,v1340,v1341,v1342,v1343,v1344,v1345,v1346,v1347,v1348,v1349,v1350,v1351,v1352,v1353,v1354,v1355]) (consBan b1335 (consBan b1336 (consBan b1337 (consBan b1338 (consBan b1339 (consBan b1340 (consBan b1341 (consBan b1342 (consBan b1343 (consBan b1344 (consBan b1345 (consBan b1346 (consBan b1347 (consBan b1348 (consBan b1349 (consBan b1350 (consBan b1351 (consBan b1352 (consBan b1353 (consBan b1354 (consBan b1355 (consBan b1356 (consBan b1357 (consBan b1358 (consBan b1359 (consBan b1360 (consBan b1361 (consBan b1362 (consBan b1363 (consBan b1364 (consBan b1365 (consBan b1366 (consBan b1367 (consBan b1368 (consBan b1369 (consBan b1370 (consBan b1371 (consBan b1372 (consBan b1373 (consBan b1374 (consBan b1375 (consBan b1376 (consBan b1377 (consBan b1378 (consBan b1379 (consBan b1380 (consBan b1381 (consBan b1382 (consBan b1383 (consBan b1384 (consBan b1385 (consBan b1386 (consBan b1387 (consBan b1388 (consBan b1389 (consBan b1390 (consBan b1391 (consBan b1392 (consBan b1393 (consBan b1394 (consBan b1395 (consBan b1396 (consBan b1397 (consBan b1398 (consBan b1399 (consBan b1400 (consBan b1401 (consBan b1402 (consBan b1403 (consBan b1404 (consBan b1405 (consBan b1406 (consBan b1407 (consBan b1408 (consBan b1409 (consBan b1410 (consBan b1411 (consBan b1412 (consBan b1413 (consBan b1414 (consBan b1415 (consBan b1416 (consBan b1417 (consBan b1418 (nilBan 220 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
def v1356 : List ℕ := [t0,t403,t1,t3,t4,t5,t6]
theorem b1420 : Ban 220 7 v1356 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1357 : List ℕ := [t176,t403,t1,t3,t4,t5,t6]
theorem b1421 : Ban 220 7 v1357 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1358 : List ℕ := [t0,t176,t403,t1,t3,t4,t5,t6]
theorem b1422 : Ban 220 7 v1358 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1359 : List ℕ := [t163,t176,t1,t3,t4,t5,t6]
theorem b1423 : Ban 220 7 v1359 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1360 : List ℕ := [t163,t0,t176,t1,t3,t4,t5,t6]
theorem b1424 : Ban 220 7 v1360 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t412 : ℕ := 0x430004300043000430004300043000430004300043000430004300000000000fffff00000000000000000000fffff000000000000000
def v1361 : List ℕ := [t412,t0,t1,t3,t4,t5,t6]
theorem b1425 : Ban 220 7 v1361 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1362 : List ℕ := [t412,t0,t176,t1,t3,t4,t5,t6]
theorem b1426 : Ban 220 7 v1362 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1363 : List ℕ := [t7,t0,t176,t1,t3,t4,t5,t6]
theorem b1427 : Ban 220 7 v1363 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1364 : List ℕ := [t0,t176,t12,t3,t4,t5,t6]
theorem b1428 : Ban 220 7 v1364 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1365 : List ℕ := [t176,t1,t12,t3,t4,t5,t6]
theorem b1429 : Ban 220 7 v1365 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1366 : List ℕ := [t0,t176,t1,t12,t3,t4,t5,t6]
theorem b1430 : Ban 220 7 v1366 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1367 : List ℕ := [t86,t176,t1,t3,t4,t5,t6]
theorem b1431 : Ban 220 7 v1367 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1368 : List ℕ := [t86,t0,t176,t1,t3,t4,t5,t6]
theorem b1432 : Ban 220 7 v1368 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1369 : List ℕ := [t0,t176,t132,t3,t4,t5,t6]
theorem b1433 : Ban 220 7 v1369 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1370 : List ℕ := [t0,t176,t132,t1,t3,t4,t5,t6]
theorem b1434 : Ban 220 7 v1370 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1371 : List ℕ := [t47,t0,t176,t1,t3,t4,t5,t6]
theorem b1435 : Ban 220 7 v1371 := viaCut p127_114 w9 (by decide) (by decide +kernel) (by decide +kernel)
def v1372 : List ℕ := [t0,t176,t1,t3,t253,t4,t5,t6]
theorem b1436 : Ban 220 7 v1372 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1373 : List ℕ := [t254,t0,t176,t1,t3,t4,t5,t6]
theorem b1437 : Ban 220 7 v1373 := viaCut p127_114 w11 (by decide) (by decide +kernel) (by decide +kernel)
def v1374 : List ℕ := [t0,t176,t1,t255,t3,t4,t5,t6]
theorem b1438 : Ban 220 7 v1374 := viaCut p127_114 w12 (by decide) (by decide +kernel) (by decide +kernel)
def v1375 : List ℕ := [t256,t0,t176,t1,t3,t4,t5,t6]
theorem b1439 : Ban 220 7 v1375 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1376 : List ℕ := [t0,t176,t1,t3,t257,t5,t6]
theorem b1440 : Ban 220 7 v1376 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1377 : List ℕ := [t176,t1,t3,t4,t257,t5,t6]
theorem b1441 : Ban 220 7 v1377 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1378 : List ℕ := [t0,t176,t1,t3,t4,t257,t5,t6]
theorem b1442 : Ban 220 7 v1378 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1379 : List ℕ := [t271,t176,t1,t3,t4,t5,t6]
theorem b1443 : Ban 220 7 v1379 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1380 : List ℕ := [t271,t0,t176,t1,t3,t4,t5,t6]
theorem b1444 : Ban 220 7 v1380 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1381 : List ℕ := [t0,t176,t1,t3,t272,t5,t6]
theorem b1445 : Ban 220 7 v1381 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1382 : List ℕ := [t0,t176,t1,t3,t272,t4,t5,t6]
theorem b1446 : Ban 220 7 v1382 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1383 : List ℕ := [t191,t0,t176,t1,t3,t4,t5,t6]
theorem b1447 : Ban 220 7 v1383 := viaCut p127_114 w13 (by decide) (by decide +kernel) (by decide +kernel)
def v1384 : List ℕ := [t0,t176,t1,t3,t4,t5,t273,t6]
theorem b1448 : Ban 220 7 v1384 := viaCut p127_114 w14 (by decide) (by decide +kernel) (by decide +kernel)
def v1385 : List ℕ := [t274,t0,t176,t1,t3,t4,t5,t6]
theorem b1449 : Ban 220 7 v1385 := viaCut p127_114 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v1386 : List ℕ := [t0,t176,t1,t3,t4,t275,t5,t6]
theorem b1450 : Ban 220 7 v1386 := viaCut p127_114 w16 (by decide) (by decide +kernel) (by decide +kernel)
def v1387 : List ℕ := [t276,t0,t176,t1,t3,t4,t5,t6]
theorem b1451 : Ban 220 7 v1387 := viaCut p127_114 w17 (by decide) (by decide +kernel) (by decide +kernel)
def v1388 : List ℕ := [t0,t176,t1,t3,t4,t5,t6,t277]
theorem b1452 : Ban 220 7 v1388 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1389 : List ℕ := [t278,t0,t176,t1,t3,t4,t5,t6]
theorem b1453 : Ban 220 7 v1389 := viaCut p127_114 w18 (by decide) (by decide +kernel) (by decide +kernel)
def v1390 : List ℕ := [t0,t176,t1,t3,t4,t5,t279,t6]
theorem b1454 : Ban 220 7 v1390 := viaCut p127_114 w19 (by decide) (by decide +kernel) (by decide +kernel)
def v1391 : List ℕ := [t0,t135,t176,t1,t3,t4,t5,t6]
theorem b1455 : Ban 220 7 v1391 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t413 : ℕ := 0x2ff002ff002ff002ff002ff002ff002ff002ff002ff002ff002ff000000ffffffffff00000fffff0000000000fffff0000000000fffff
def v1392 : List ℕ := [t0,t176,t413,t3,t4,t5,t6]
theorem b1456 : Ban 220 7 v1392 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1393 : List ℕ := [t0,t1,t413,t3,t4,t5,t6]
theorem b1457 : Ban 220 7 v1393 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1394 : List ℕ := [t0,t176,t1,t413,t3,t4,t5,t6]
theorem b1458 : Ban 220 7 v1394 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t414 : ℕ := 0xf0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f00000000000fffff00000000000000000000fffff000000000000000
def v1395 : List ℕ := [t414,t0,t1,t3,t4,t5,t6]
theorem b1459 : Ban 220 7 v1395 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1396 : List ℕ := [t414,t0,t176,t1,t3,t4,t5,t6]
theorem b1460 : Ban 220 7 v1396 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1397 : List ℕ := [t0,t176,t141,t3,t4,t5,t6]
theorem b1461 : Ban 220 7 v1397 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1398 : List ℕ := [t0,t176,t141,t1,t3,t4,t5,t6]
theorem b1462 : Ban 220 7 v1398 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1399 : List ℕ := [t164,t0,t176,t1,t3,t4,t5,t6]
theorem b1463 : Ban 220 7 v1399 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t415 : ℕ := 0x13cf013cf013cf013cf013cf013cf013cf013cf013cf013cf013cf0fffff00000fffff00000000000000000000fffffffffffffff00000
def v1400 : List ℕ := [t0,t176,t1,t3,t415,t4,t5,t6]
theorem b1464 : Ban 220 7 v1400 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t416 : ℕ := 0xcf000cf000cf000cf000cf000cf000cf000cf000cf000cf000cf00000000000fffff0000000000000000000000000000000000000000
def v1401 : List ℕ := [t0,t416,t176,t1,t3,t4,t5,t6]
theorem b1465 : Ban 220 7 v1401 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1402 : List ℕ := [t0,t176,t1,t167,t3,t4,t5,t6]
theorem b1466 : Ban 220 7 v1402 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1403 : List ℕ := [t168,t0,t176,t1,t3,t4,t5,t6]
theorem b1467 : Ban 220 7 v1403 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t417 : ℕ := 0x40cfa40cfa40cfa40cfa40cfa40cfa40cfa40cfa40cfa40cfa40cfa0000000000fffff000000000000000ffffffffff00000ffffffffff
def v1404 : List ℕ := [t0,t176,t1,t3,t417,t5,t6]
theorem b1468 : Ban 220 7 v1404 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1405 : List ℕ := [t0,t1,t3,t4,t417,t5,t6]
theorem b1469 : Ban 220 7 v1405 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1406 : List ℕ := [t0,t176,t1,t3,t4,t417,t5,t6]
theorem b1470 : Ban 220 7 v1406 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t418 : ℕ := 0xc5000c5000c5000c5000c5000c5000c5000c5000c5000c5000c500000000000fffff00000000000000000000fffff000000000000000
def v1407 : List ℕ := [t0,t418,t1,t3,t4,t5,t6]
theorem b1471 : Ban 220 7 v1407 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1408 : List ℕ := [t0,t418,t176,t1,t3,t4,t5,t6]
theorem b1472 : Ban 220 7 v1408 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1409 : List ℕ := [t0,t176,t1,t3,t173,t5,t6]
theorem b1473 : Ban 220 7 v1409 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1410 : List ℕ := [t0,t176,t1,t3,t173,t4,t5,t6]
theorem b1474 : Ban 220 7 v1410 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1411 : List ℕ := [t0,t176,t1,t3,t4,t175,t6]
theorem b1475 : Ban 220 7 v1411 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1476 : Ban 220 7 v1220 := viaCut p127_82 w34 (by decide) (by decide +kernel) (by decide +kernel)
def v1412 : List ℕ := [t0,t176,t1,t3,t4,t5,t175,t6]
theorem b1477 : Ban 220 7 v1412 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1413 : List ℕ := [t240,t0,t176,t1,t3,t4,t5,t6]
theorem b1478 : Ban 220 7 v1413 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def t419 : ℕ := 0xe0cf0e0cf0e0cf0e0cf0e0cf0e0cf0e0cf0e0cf0e0cf0e0cf0e0cf0ffffffffffffffffffff000000000000000fffff000000000000000
def v1414 : List ℕ := [t0,t176,t1,t3,t4,t5,t6,t419]
theorem b1479 : Ban 220 7 v1414 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def t420 : ℕ := 0xcf000cf000cf000cf000cf000cf000cf000cf000cf000cf000cf000000000000000000000000000000000000fffff000000000000000
def v1415 : List ℕ := [t0,t420,t176,t1,t3,t4,t5,t6]
theorem b1480 : Ban 220 7 v1415 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1416 : List ℕ := [t0,t176,t1,t3,t4,t5,t243,t6]
theorem b1481 : Ban 220 7 v1416 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1417 : List ℕ := [t0,t176,t147,t1,t3,t4,t5,t6]
theorem b1482 : Ban 220 7 v1417 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1418 : List ℕ := [t0,t176,t1,t148,t4,t5,t6]
theorem b1483 : Ban 220 7 v1418 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1419 : List ℕ := [t0,t176,t3,t148,t4,t5,t6]
theorem b1484 : Ban 220 7 v1419 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1420 : List ℕ := [t0,t176,t1,t3,t148,t4,t5,t6]
theorem b1485 : Ban 220 7 v1420 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1421 : List ℕ := [t0,t176,t149,t3,t4,t5,t6]
theorem b1486 : Ban 220 7 v1421 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1422 : List ℕ := [t0,t176,t149,t1,t3,t4,t5,t6]
theorem b1487 : Ban 220 7 v1422 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1423 : List ℕ := [t0,t176,t1,t150,t4,t5,t6]
theorem b1488 : Ban 220 7 v1423 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1424 : List ℕ := [t0,t176,t1,t150,t3,t4,t5,t6]
theorem b1489 : Ban 220 7 v1424 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1425 : List ℕ := [t151,t0,t176,t1,t3,t4,t5,t6]
theorem b1490 : Ban 220 7 v1425 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1426 : List ℕ := [t0,t176,t1,t3,t4,t152,t5,t6]
theorem b1491 : Ban 220 7 v1426 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1427 : List ℕ := [t0,t176,t153,t1,t3,t4,t5,t6]
theorem b1492 : Ban 220 7 v1427 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1428 : List ℕ := [t0,t176,t1,t3,t154,t4,t5,t6]
theorem b1493 : Ban 220 7 v1428 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1429 : List ℕ := [t155,t0,t176,t1,t3,t4,t5,t6]
theorem b1494 : Ban 220 7 v1429 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1430 : List ℕ := [t0,t176,t1,t3,t4,t5,t156,t6]
theorem b1495 : Ban 220 7 v1430 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1431 : List ℕ := [t0,t176,t157,t1,t3,t4,t5,t6]
theorem b1496 : Ban 220 7 v1431 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1432 : List ℕ := [t0,t176,t1,t3,t4,t158,t5,t6]
theorem b1497 : Ban 220 7 v1432 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1433 : List ℕ := [t159,t0,t176,t1,t3,t4,t5,t6]
theorem b1498 : Ban 220 7 v1433 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1434 : List ℕ := [t0,t176,t1,t3,t4,t5,t6,t160]
theorem b1499 : Ban 220 7 v1434 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1435 : List ℕ := [t0,t176,t161,t1,t3,t4,t5,t6]
theorem b1500 : Ban 220 7 v1435 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1436 : List ℕ := [t0,t176,t1,t3,t4,t5,t162,t6]
theorem b1501 : Ban 220 7 v1436 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1437 : List ℕ := [t206,t0,t176,t1,t3,t4,t5,t6]
theorem b1502 : Ban 220 7 v1437 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1438 : List ℕ := [t0,t176,t1,t3,t4,t207,t5,t6]
theorem b1503 : Ban 220 7 v1438 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1439 : List ℕ := [t0,t176,t1,t208,t3,t4,t5,t6]
theorem b1504 : Ban 220 7 v1439 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1440 : List ℕ := [t0,t176,t1,t3,t209,t4,t5,t6]
theorem b1505 : Ban 220 7 v1440 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1441 : List ℕ := [t0,t176,t1,t210,t3,t4,t5,t6]
theorem b1506 : Ban 220 7 v1441 := viaCut p127_114 w20 (by decide) (by decide +kernel) (by decide +kernel)
def v1442 : List ℕ := [t0,t176,t1,t3,t4,t246,t6]
theorem b1507 : Ban 220 7 v1442 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1443 : List ℕ := [t0,t176,t1,t4,t5,t246,t6]
theorem b1508 : Ban 220 7 v1443 := viaCut p127_114 w21 (by decide) (by decide +kernel) (by decide +kernel)
def v1444 : List ℕ := [t0,t176,t1,t3,t4,t5,t246,t6]
theorem b1509 : Ban 220 7 v1444 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1445 : List ℕ := [t0,t176,t1,t214,t4,t5,t6]
theorem b1510 : Ban 220 7 v1445 := viaCut p127_114 w22 (by decide) (by decide +kernel) (by decide +kernel)
def v1446 : List ℕ := [t0,t176,t1,t214,t3,t4,t5,t6]
theorem b1511 : Ban 220 7 v1446 := viaCut p127_114 w23 (by decide) (by decide +kernel) (by decide +kernel)
def v1447 : List ℕ := [t0,t176,t1,t3,t4,t247,t6]
theorem b1512 : Ban 220 7 v1447 := viaCut p127_114 w24 (by decide) (by decide +kernel) (by decide +kernel)
def v1448 : List ℕ := [t0,t176,t1,t3,t4,t247,t5,t6]
theorem b1513 : Ban 220 7 v1448 := viaCut p127_114 w25 (by decide) (by decide +kernel) (by decide +kernel)
def v1449 : List ℕ := [t218,t0,t176,t1,t3,t4,t5,t6]
theorem b1514 : Ban 220 7 v1449 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1450 : List ℕ := [t0,t176,t1,t3,t4,t5,t6,t219]
theorem b1515 : Ban 220 7 v1450 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1451 : List ℕ := [t0,t176,t1,t220,t3,t4,t5,t6]
theorem b1516 : Ban 220 7 v1451 := viaCut p127_114 w26 (by decide) (by decide +kernel) (by decide +kernel)
def v1452 : List ℕ := [t0,t176,t1,t3,t4,t5,t222,t6]
theorem b1517 : Ban 220 7 v1452 := viaCut p127_114 w27 (by decide) (by decide +kernel) (by decide +kernel)
def v1453 : List ℕ := [t224,t0,t176,t1,t3,t4,t5,t6]
theorem b1518 : Ban 220 7 v1453 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1454 : List ℕ := [t0,t176,t1,t3,t4,t5,t248,t6]
theorem b1519 : Ban 220 7 v1454 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1455 : List ℕ := [t0,t176,t1,t3,t226,t4,t5,t6]
theorem b1520 : Ban 220 7 v1455 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1456 : List ℕ := [t0,t176,t1,t3,t4,t249,t5,t6]
theorem b1521 : Ban 220 7 v1456 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1457 : List ℕ := [t0,t176,t1,t3,t228,t4,t5,t6]
theorem b1522 : Ban 220 7 v1457 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1458 : List ℕ := [t0,t176,t1,t3,t4,t5,t229]
theorem b1523 : Ban 220 7 v1458 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1459 : List ℕ := [t0,t176,t1,t3,t5,t6,t229]
theorem b1524 : Ban 220 7 v1459 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1460 : List ℕ := [t0,t176,t1,t3,t4,t5,t6,t229]
theorem b1525 : Ban 220 7 v1460 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1461 : List ℕ := [t230,t0,t176,t1,t3,t5,t6]
theorem b1526 : Ban 220 7 v1461 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1462 : List ℕ := [t230,t0,t176,t1,t3,t4,t5,t6]
theorem b1527 : Ban 220 7 v1462 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1463 : List ℕ := [t0,t176,t1,t3,t4,t5,t231]
theorem b1528 : Ban 220 7 v1463 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1464 : List ℕ := [t0,t176,t1,t3,t4,t5,t231,t6]
theorem b1529 : Ban 220 7 v1464 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1465 : List ℕ := [t0,t176,t1,t3,t4,t232,t5,t6]
theorem b1530 : Ban 220 7 v1465 := viaCut p127_114 w28 (by decide) (by decide +kernel) (by decide +kernel)
def v1466 : List ℕ := [t0,t176,t1,t3,t4,t5,t250]
theorem b1531 : Ban 220 7 v1466 := viaCut p127_114 w29 (by decide) (by decide +kernel) (by decide +kernel)
def v1467 : List ℕ := [t0,t176,t1,t3,t4,t6,t250]
theorem b1532 : Ban 220 7 v1467 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1468 : List ℕ := [t0,t176,t1,t3,t4,t5,t6,t250]
theorem b1533 : Ban 220 7 v1468 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1469 : List ℕ := [t0,t176,t1,t3,t251,t4,t6]
theorem b1534 : Ban 220 7 v1469 := viaCut p127_114 w30 (by decide) (by decide +kernel) (by decide +kernel)
def v1470 : List ℕ := [t0,t176,t1,t3,t251,t4,t5,t6]
theorem b1535 : Ban 220 7 v1470 := viaCut p127_114 w31 (by decide) (by decide +kernel) (by decide +kernel)
def v1471 : List ℕ := [t0,t176,t1,t3,t4,t238,t5]
theorem b1536 : Ban 220 7 v1471 := viaCut p127_114 w32 (by decide) (by decide +kernel) (by decide +kernel)
def v1472 : List ℕ := [t0,t176,t1,t3,t4,t238,t5,t6]
theorem b1537 : Ban 220 7 v1472 := viaCut p127_114 w33 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1538 : Ban 220 8 v1269 := viaBranch (ws := [v1270,v1271,v1356,v1357,v1358,v1359,v1360,v1361,v1362,v1363,v1364,v1365,v1366,v1367,v1368,v1369,v1370,v1371,v1372,v1373,v1374,v1375,v1376,v1377,v1378,v1379,v1380,v1381,v1382,v1383,v1384,v1385,v1386,v1387,v1388,v1389,v1390,v1391,v1392,v1393,v1394,v1395,v1396,v1397,v1398,v1399,v1400,v1401,v1402,v1403,v1404,v1405,v1406,v1407,v1408,v1409,v1410,v1411,v1220,v1412,v1413,v1414,v1415,v1416,v1417,v1418,v1419,v1420,v1421,v1422,v1423,v1424,v1425,v1426,v1427,v1428,v1429,v1430,v1431,v1432,v1433,v1434,v1435,v1436,v1437,v1438,v1439,v1440,v1441,v1442,v1443,v1444,v1445,v1446,v1447,v1448,v1449,v1450,v1451,v1452,v1453,v1454,v1455,v1456,v1457,v1458,v1459,v1460,v1461,v1462,v1463,v1464,v1465,v1466,v1467,v1468,v1469,v1470,v1471,v1472]) (consBan b1334 (consBan b1419 (consBan b1420 (consBan b1421 (consBan b1422 (consBan b1423 (consBan b1424 (consBan b1425 (consBan b1426 (consBan b1427 (consBan b1428 (consBan b1429 (consBan b1430 (consBan b1431 (consBan b1432 (consBan b1433 (consBan b1434 (consBan b1435 (consBan b1436 (consBan b1437 (consBan b1438 (consBan b1439 (consBan b1440 (consBan b1441 (consBan b1442 (consBan b1443 (consBan b1444 (consBan b1445 (consBan b1446 (consBan b1447 (consBan b1448 (consBan b1449 (consBan b1450 (consBan b1451 (consBan b1452 (consBan b1453 (consBan b1454 (consBan b1455 (consBan b1456 (consBan b1457 (consBan b1458 (consBan b1459 (consBan b1460 (consBan b1461 (consBan b1462 (consBan b1463 (consBan b1464 (consBan b1465 (consBan b1466 (consBan b1467 (consBan b1468 (consBan b1469 (consBan b1470 (consBan b1471 (consBan b1472 (consBan b1473 (consBan b1474 (consBan b1475 (consBan b1476 (consBan b1477 (consBan b1478 (consBan b1479 (consBan b1480 (consBan b1481 (consBan b1482 (consBan b1483 (consBan b1484 (consBan b1485 (consBan b1486 (consBan b1487 (consBan b1488 (consBan b1489 (consBan b1490 (consBan b1491 (consBan b1492 (consBan b1493 (consBan b1494 (consBan b1495 (consBan b1496 (consBan b1497 (consBan b1498 (consBan b1499 (consBan b1500 (consBan b1501 (consBan b1502 (consBan b1503 (consBan b1504 (consBan b1505 (consBan b1506 (consBan b1507 (consBan b1508 (consBan b1509 (consBan b1510 (consBan b1511 (consBan b1512 (consBan b1513 (consBan b1514 (consBan b1515 (consBan b1516 (consBan b1517 (consBan b1518 (consBan b1519 (consBan b1520 (consBan b1521 (consBan b1522 (consBan b1523 (consBan b1524 (consBan b1525 (consBan b1526 (consBan b1527 (consBan b1528 (consBan b1529 (consBan b1530 (consBan b1531 (consBan b1532 (consBan b1533 (consBan b1534 (consBan b1535 (consBan b1536 (consBan b1537 (nilBan 220 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
def v1473 : List ℕ := [t0,t176,t1,t2,t3,t4,t5,t6]
theorem b1539 : Ban 220 8 v1473 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1474 : List ℕ := [t0,t1,t2,t3,t4,t177,t6]
def v1475 : List ℕ := [t7,t0,t1,t2,t3,t4,t177,t6]
theorem b1540 : Ban 220 7 v1475 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1476 : List ℕ := [t0,t12,t2,t3,t4,t177,t6]
theorem b1541 : Ban 220 7 v1476 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1477 : List ℕ := [t1,t12,t2,t3,t4,t177,t6]
theorem b1542 : Ban 220 7 v1477 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1478 : List ℕ := [t0,t1,t12,t2,t3,t4,t177,t6]
theorem b1543 : Ban 220 7 v1478 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1479 : List ℕ := [t86,t1,t2,t3,t4,t177,t6]
theorem b1544 : Ban 220 7 v1479 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1480 : List ℕ := [t86,t0,t1,t2,t3,t4,t177,t6]
theorem b1545 : Ban 220 7 v1480 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1481 : List ℕ := [t0,t132,t2,t3,t4,t177,t6]
theorem b1546 : Ban 220 7 v1481 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1482 : List ℕ := [t0,t132,t1,t2,t3,t4,t177,t6]
theorem b1547 : Ban 220 7 v1482 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1483 : List ℕ := [t133,t0,t1,t2,t3,t4,t177,t6]
theorem b1548 : Ban 220 7 v1483 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1484 : List ℕ := [t0,t1,t134,t3,t4,t177,t6]
theorem b1549 : Ban 220 7 v1484 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1485 : List ℕ := [t0,t1,t2,t134,t3,t4,t177,t6]
theorem b1550 : Ban 220 7 v1485 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1486 : List ℕ := [t163,t1,t2,t3,t4,t177,t6]
theorem b1551 : Ban 220 7 v1486 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1487 : List ℕ := [t163,t0,t1,t2,t3,t4,t177,t6]
theorem b1552 : Ban 220 7 v1487 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1488 : List ℕ := [t0,t1,t252,t3,t4,t177,t6]
theorem b1553 : Ban 220 7 v1488 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1489 : List ℕ := [t0,t1,t252,t2,t3,t4,t177,t6]
theorem b1554 : Ban 220 7 v1489 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1490 : List ℕ := [t47,t0,t1,t2,t3,t4,t177,t6]
theorem b1555 : Ban 220 7 v1490 := viaCut p127_114 w9 (by decide) (by decide +kernel) (by decide +kernel)
def v1491 : List ℕ := [t0,t1,t2,t3,t253,t4,t177,t6]
theorem b1556 : Ban 220 7 v1491 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1492 : List ℕ := [t254,t0,t1,t2,t3,t4,t177,t6]
theorem b1557 : Ban 220 7 v1492 := viaCut p127_114 w11 (by decide) (by decide +kernel) (by decide +kernel)
def v1493 : List ℕ := [t0,t1,t2,t255,t3,t4,t177,t6]
theorem b1558 : Ban 220 7 v1493 := viaCut p127_114 w12 (by decide) (by decide +kernel) (by decide +kernel)
def v1494 : List ℕ := [t256,t0,t1,t2,t3,t4,t177,t6]
theorem b1559 : Ban 220 7 v1494 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1495 : List ℕ := [t0,t1,t2,t3,t257,t177,t6]
theorem b1560 : Ban 220 7 v1495 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1496 : List ℕ := [t1,t2,t3,t4,t257,t177,t6]
theorem b1561 : Ban 220 7 v1496 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1497 : List ℕ := [t0,t1,t2,t3,t4,t257,t177,t6]
theorem b1562 : Ban 220 7 v1497 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1498 : List ℕ := [t271,t1,t2,t3,t4,t177,t6]
theorem b1563 : Ban 220 7 v1498 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1499 : List ℕ := [t271,t0,t1,t2,t3,t4,t177,t6]
theorem b1564 : Ban 220 7 v1499 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1500 : List ℕ := [t0,t1,t2,t3,t272,t177,t6]
theorem b1565 : Ban 220 7 v1500 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1501 : List ℕ := [t0,t1,t2,t3,t272,t4,t177,t6]
theorem b1566 : Ban 220 7 v1501 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1502 : List ℕ := [t191,t0,t1,t2,t3,t4,t177,t6]
theorem b1567 : Ban 220 7 v1502 := viaCut p127_114 w13 (by decide) (by decide +kernel) (by decide +kernel)
def t421 : ℕ := 0x94acc94acc94acc94acc94acc94acc94acc94acc94acc94acc94acc000000000000000ffffffffffffffffffff00000fffff0000000000
def v1503 : List ℕ := [t0,t1,t2,t3,t4,t177,t421,t6]
theorem b1568 : Ban 220 7 v1503 := viaCut p127_114 w14 (by decide) (by decide +kernel) (by decide +kernel)
def v1504 : List ℕ := [t274,t0,t1,t2,t3,t4,t177,t6]
theorem b1569 : Ban 220 7 v1504 := viaCut p127_114 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v1505 : List ℕ := [t0,t1,t2,t3,t4,t197,t177,t6]
theorem b1570 : Ban 220 7 v1505 := viaCut p127_114 w16 (by decide) (by decide +kernel) (by decide +kernel)
def v1506 : List ℕ := [t276,t0,t1,t2,t3,t4,t177,t6]
theorem b1571 : Ban 220 7 v1506 := viaCut p127_114 w17 (by decide) (by decide +kernel) (by decide +kernel)
def v1507 : List ℕ := [t0,t1,t2,t3,t4,t177,t6,t277]
theorem b1572 : Ban 220 7 v1507 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1508 : List ℕ := [t278,t0,t1,t2,t3,t4,t177,t6]
theorem b1573 : Ban 220 7 v1508 := viaCut p127_114 w18 (by decide) (by decide +kernel) (by decide +kernel)
def v1509 : List ℕ := [t0,t1,t2,t3,t4,t177,t279,t6]
theorem b1574 : Ban 220 7 v1509 := viaCut p127_114 w19 (by decide) (by decide +kernel) (by decide +kernel)
def v1510 : List ℕ := [t0,t135,t1,t2,t3,t4,t177,t6]
theorem b1575 : Ban 220 7 v1510 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1511 : List ℕ := [t0,t1,t136,t3,t4,t177,t6]
theorem b1576 : Ban 220 7 v1511 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1512 : List ℕ := [t0,t2,t136,t3,t4,t177,t6]
theorem b1577 : Ban 220 7 v1512 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1513 : List ℕ := [t0,t1,t2,t136,t3,t4,t177,t6]
theorem b1578 : Ban 220 7 v1513 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1514 : List ℕ := [t0,t141,t2,t3,t4,t177,t6]
theorem b1579 : Ban 220 7 v1514 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1515 : List ℕ := [t0,t141,t1,t2,t3,t4,t177,t6]
theorem b1580 : Ban 220 7 v1515 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1516 : List ℕ := [t0,t1,t142,t3,t4,t177,t6]
theorem b1581 : Ban 220 7 v1516 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1517 : List ℕ := [t0,t1,t142,t2,t3,t4,t177,t6]
theorem b1582 : Ban 220 7 v1517 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1518 : List ℕ := [t0,t147,t1,t2,t3,t4,t177,t6]
theorem b1583 : Ban 220 7 v1518 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1519 : List ℕ := [t0,t1,t2,t148,t4,t177,t6]
theorem b1584 : Ban 220 7 v1519 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1520 : List ℕ := [t0,t2,t3,t148,t4,t177,t6]
theorem b1585 : Ban 220 7 v1520 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1521 : List ℕ := [t0,t1,t2,t3,t148,t4,t177,t6]
theorem b1586 : Ban 220 7 v1521 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1522 : List ℕ := [t0,t149,t2,t3,t4,t177,t6]
theorem b1587 : Ban 220 7 v1522 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1523 : List ℕ := [t0,t149,t1,t2,t3,t4,t177,t6]
theorem b1588 : Ban 220 7 v1523 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1524 : List ℕ := [t0,t1,t2,t150,t4,t177,t6]
theorem b1589 : Ban 220 7 v1524 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1525 : List ℕ := [t0,t1,t2,t150,t3,t4,t177,t6]
theorem b1590 : Ban 220 7 v1525 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1526 : List ℕ := [t151,t0,t1,t2,t3,t4,t177,t6]
theorem b1591 : Ban 220 7 v1526 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1527 : List ℕ := [t0,t1,t2,t3,t4,t152,t177,t6]
theorem b1592 : Ban 220 7 v1527 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1528 : List ℕ := [t0,t153,t1,t2,t3,t4,t177,t6]
theorem b1593 : Ban 220 7 v1528 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1529 : List ℕ := [t0,t1,t2,t3,t154,t4,t177,t6]
theorem b1594 : Ban 220 7 v1529 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1530 : List ℕ := [t155,t0,t1,t2,t3,t4,t177,t6]
theorem b1595 : Ban 220 7 v1530 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1531 : List ℕ := [t0,t1,t2,t3,t4,t177,t178,t6]
theorem b1596 : Ban 220 7 v1531 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1532 : List ℕ := [t0,t157,t1,t2,t3,t4,t177,t6]
theorem b1597 : Ban 220 7 v1532 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1533 : List ℕ := [t0,t1,t2,t3,t4,t179,t177,t6]
theorem b1598 : Ban 220 7 v1533 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1534 : List ℕ := [t159,t0,t1,t2,t3,t4,t177,t6]
theorem b1599 : Ban 220 7 v1534 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1535 : List ℕ := [t0,t1,t2,t3,t4,t177,t6,t160]
theorem b1600 : Ban 220 7 v1535 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1536 : List ℕ := [t0,t161,t1,t2,t3,t4,t177,t6]
theorem b1601 : Ban 220 7 v1536 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1537 : List ℕ := [t0,t1,t2,t3,t4,t177,t162,t6]
theorem b1602 : Ban 220 7 v1537 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1538 : List ℕ := [t164,t0,t1,t2,t3,t4,t177,t6]
theorem b1603 : Ban 220 7 v1538 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1539 : List ℕ := [t0,t1,t2,t3,t165,t4,t177,t6]
theorem b1604 : Ban 220 7 v1539 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1540 : List ℕ := [t0,t1,t166,t2,t3,t4,t177,t6]
theorem b1605 : Ban 220 7 v1540 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1541 : List ℕ := [t0,t1,t2,t167,t3,t4,t177,t6]
theorem b1606 : Ban 220 7 v1541 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1542 : List ℕ := [t168,t0,t1,t2,t3,t4,t177,t6]
theorem b1607 : Ban 220 7 v1542 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1543 : List ℕ := [t0,t1,t2,t3,t169,t177,t6]
theorem b1608 : Ban 220 7 v1543 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1544 : List ℕ := [t0,t1,t3,t4,t169,t177,t6]
theorem b1609 : Ban 220 7 v1544 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1545 : List ℕ := [t0,t1,t2,t3,t4,t169,t177,t6]
theorem b1610 : Ban 220 7 v1545 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1546 : List ℕ := [t0,t1,t172,t3,t4,t177,t6]
theorem b1611 : Ban 220 7 v1546 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1547 : List ℕ := [t0,t1,t172,t2,t3,t4,t177,t6]
theorem b1612 : Ban 220 7 v1547 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1548 : List ℕ := [t0,t1,t2,t3,t173,t177,t6]
theorem b1613 : Ban 220 7 v1548 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1549 : List ℕ := [t0,t1,t2,t3,t173,t4,t177,t6]
theorem b1614 : Ban 220 7 v1549 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1615 : Ban 220 7 v1175 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1550 : List ℕ := [t0,t1,t3,t4,t177,t175,t6]
theorem b1616 : Ban 220 7 v1550 := viaCut p127_82 w34 (by decide) (by decide +kernel) (by decide +kernel)
def v1551 : List ℕ := [t0,t1,t2,t3,t4,t177,t175,t6]
theorem b1617 : Ban 220 7 v1551 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1552 : List ℕ := [t240,t0,t1,t2,t3,t4,t177,t6]
theorem b1618 : Ban 220 7 v1552 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1553 : List ℕ := [t0,t1,t2,t3,t4,t177,t6,t241]
theorem b1619 : Ban 220 7 v1553 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1554 : List ℕ := [t0,t1,t242,t2,t3,t4,t177,t6]
theorem b1620 : Ban 220 7 v1554 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1555 : List ℕ := [t0,t1,t2,t3,t4,t177,t243,t6]
theorem b1621 : Ban 220 7 v1555 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1556 : List ℕ := [t206,t0,t1,t2,t3,t4,t177,t6]
theorem b1622 : Ban 220 7 v1556 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1557 : List ℕ := [t0,t1,t2,t3,t4,t207,t177,t6]
theorem b1623 : Ban 220 7 v1557 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1558 : List ℕ := [t0,t1,t2,t208,t3,t4,t177,t6]
theorem b1624 : Ban 220 7 v1558 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1559 : List ℕ := [t0,t1,t2,t3,t209,t4,t177,t6]
theorem b1625 : Ban 220 7 v1559 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1560 : List ℕ := [t0,t1,t2,t210,t3,t4,t177,t6]
theorem b1626 : Ban 220 7 v1560 := viaCut p127_114 w20 (by decide) (by decide +kernel) (by decide +kernel)
def v1561 : List ℕ := [t0,t1,t2,t3,t4,t212,t6]
theorem b1627 : Ban 220 7 v1561 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1562 : List ℕ := [t0,t1,t2,t4,t177,t212,t6]
theorem b1628 : Ban 220 7 v1562 := viaCut p127_114 w21 (by decide) (by decide +kernel) (by decide +kernel)
def v1563 : List ℕ := [t0,t1,t2,t3,t4,t177,t212,t6]
theorem b1629 : Ban 220 7 v1563 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1564 : List ℕ := [t0,t1,t214,t2,t4,t177,t6]
theorem b1630 : Ban 220 7 v1564 := viaCut p127_114 w22 (by decide) (by decide +kernel) (by decide +kernel)
def v1565 : List ℕ := [t0,t1,t214,t2,t3,t4,t177,t6]
theorem b1631 : Ban 220 7 v1565 := viaCut p127_114 w23 (by decide) (by decide +kernel) (by decide +kernel)
def v1566 : List ℕ := [t0,t1,t2,t3,t4,t216,t6]
theorem b1632 : Ban 220 7 v1566 := viaCut p127_114 w24 (by decide) (by decide +kernel) (by decide +kernel)
def v1567 : List ℕ := [t0,t1,t2,t3,t4,t216,t177,t6]
theorem b1633 : Ban 220 7 v1567 := viaCut p127_114 w25 (by decide) (by decide +kernel) (by decide +kernel)
def v1568 : List ℕ := [t218,t0,t1,t2,t3,t4,t177,t6]
theorem b1634 : Ban 220 7 v1568 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1569 : List ℕ := [t0,t1,t2,t3,t4,t177,t6,t219]
theorem b1635 : Ban 220 7 v1569 := viaCut p127_41 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1570 : List ℕ := [t0,t1,t2,t220,t3,t4,t177,t6]
theorem b1636 : Ban 220 7 v1570 := viaCut p127_114 w26 (by decide) (by decide +kernel) (by decide +kernel)
def v1571 : List ℕ := [t0,t1,t2,t3,t4,t177,t222,t6]
theorem b1637 : Ban 220 7 v1571 := viaCut p127_114 w27 (by decide) (by decide +kernel) (by decide +kernel)
def v1572 : List ℕ := [t224,t0,t1,t2,t3,t4,t177,t6]
theorem b1638 : Ban 220 7 v1572 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1573 : List ℕ := [t0,t1,t2,t3,t4,t177,t225,t6]
theorem b1639 : Ban 220 7 v1573 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1574 : List ℕ := [t0,t1,t2,t3,t226,t4,t177,t6]
theorem b1640 : Ban 220 7 v1574 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1575 : List ℕ := [t0,t1,t2,t3,t4,t227,t177,t6]
theorem b1641 : Ban 220 7 v1575 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1576 : List ℕ := [t0,t1,t2,t3,t228,t4,t177,t6]
theorem b1642 : Ban 220 7 v1576 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1577 : List ℕ := [t0,t1,t2,t3,t4,t177,t229]
theorem b1643 : Ban 220 7 v1577 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1578 : List ℕ := [t0,t1,t2,t3,t177,t6,t229]
theorem b1644 : Ban 220 7 v1578 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1579 : List ℕ := [t0,t1,t2,t3,t4,t177,t6,t229]
theorem b1645 : Ban 220 7 v1579 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1580 : List ℕ := [t230,t0,t1,t2,t3,t177,t6]
theorem b1646 : Ban 220 7 v1580 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1581 : List ℕ := [t230,t0,t1,t2,t3,t4,t177,t6]
theorem b1647 : Ban 220 7 v1581 := viaCut p127_114 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v1582 : List ℕ := [t0,t1,t2,t3,t4,t177,t231]
theorem b1648 : Ban 220 7 v1582 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1583 : List ℕ := [t0,t1,t2,t3,t4,t177,t231,t6]
theorem b1649 : Ban 220 7 v1583 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1584 : List ℕ := [t0,t1,t2,t3,t4,t232,t177,t6]
theorem b1650 : Ban 220 7 v1584 := viaCut p127_114 w28 (by decide) (by decide +kernel) (by decide +kernel)
def v1585 : List ℕ := [t0,t1,t2,t3,t4,t177,t234]
theorem b1651 : Ban 220 7 v1585 := viaCut p127_114 w29 (by decide) (by decide +kernel) (by decide +kernel)
def v1586 : List ℕ := [t0,t1,t2,t3,t4,t6,t234]
theorem b1652 : Ban 220 7 v1586 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1587 : List ℕ := [t0,t1,t2,t3,t4,t177,t6,t234]
theorem b1653 : Ban 220 7 v1587 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1588 : List ℕ := [t0,t1,t2,t3,t236,t4,t6]
theorem b1654 : Ban 220 7 v1588 := viaCut p127_114 w30 (by decide) (by decide +kernel) (by decide +kernel)
def v1589 : List ℕ := [t0,t1,t2,t3,t236,t4,t177,t6]
theorem b1655 : Ban 220 7 v1589 := viaCut p127_114 w31 (by decide) (by decide +kernel) (by decide +kernel)
def v1590 : List ℕ := [t0,t1,t2,t3,t4,t238,t177]
theorem b1656 : Ban 220 7 v1590 := viaCut p127_114 w32 (by decide) (by decide +kernel) (by decide +kernel)
def v1591 : List ℕ := [t0,t1,t2,t3,t4,t238,t177,t6]
theorem b1657 : Ban 220 7 v1591 := viaCut p127_114 w33 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1658 : Ban 220 8 v1474 := viaBranch (ws := [v1475,v1476,v1477,v1478,v1479,v1480,v1481,v1482,v1483,v239,v1484,v350,v1485,v1486,v1487,v1488,v1489,v1490,v1491,v1492,v1493,v1494,v1495,v1496,v1497,v1498,v1499,v1500,v1501,v1502,v1503,v1504,v1505,v1506,v1507,v1508,v1509,v1510,v1511,v1512,v1513,v1514,v1515,v1516,v1517,v1518,v1519,v1520,v1521,v1522,v1523,v1524,v1525,v1526,v1527,v1528,v1529,v1530,v1531,v1532,v1533,v1534,v1535,v1536,v1537,v1538,v1539,v1540,v1541,v1542,v1543,v1544,v1545,v1546,v1547,v1548,v1549,v1175,v1550,v1551,v1552,v1553,v1554,v1555,v1556,v1557,v1558,v1559,v1560,v1561,v1562,v1563,v1564,v1565,v1566,v1567,v1568,v1569,v1570,v1571,v1572,v1573,v1574,v1575,v1576,v1577,v1578,v1579,v1580,v1581,v1582,v1583,v1584,v1585,v1586,v1587,v1588,v1589,v1590,v1591]) (consBan b1540 (consBan b1541 (consBan b1542 (consBan b1543 (consBan b1544 (consBan b1545 (consBan b1546 (consBan b1547 (consBan b1548 (consBan b350 (consBan b1549 (consBan b351 (consBan b1550 (consBan b1551 (consBan b1552 (consBan b1553 (consBan b1554 (consBan b1555 (consBan b1556 (consBan b1557 (consBan b1558 (consBan b1559 (consBan b1560 (consBan b1561 (consBan b1562 (consBan b1563 (consBan b1564 (consBan b1565 (consBan b1566 (consBan b1567 (consBan b1568 (consBan b1569 (consBan b1570 (consBan b1571 (consBan b1572 (consBan b1573 (consBan b1574 (consBan b1575 (consBan b1576 (consBan b1577 (consBan b1578 (consBan b1579 (consBan b1580 (consBan b1581 (consBan b1582 (consBan b1583 (consBan b1584 (consBan b1585 (consBan b1586 (consBan b1587 (consBan b1588 (consBan b1589 (consBan b1590 (consBan b1591 (consBan b1592 (consBan b1593 (consBan b1594 (consBan b1595 (consBan b1596 (consBan b1597 (consBan b1598 (consBan b1599 (consBan b1600 (consBan b1601 (consBan b1602 (consBan b1603 (consBan b1604 (consBan b1605 (consBan b1606 (consBan b1607 (consBan b1608 (consBan b1609 (consBan b1610 (consBan b1611 (consBan b1612 (consBan b1613 (consBan b1614 (consBan b1615 (consBan b1616 (consBan b1617 (consBan b1618 (consBan b1619 (consBan b1620 (consBan b1621 (consBan b1622 (consBan b1623 (consBan b1624 (consBan b1625 (consBan b1626 (consBan b1627 (consBan b1628 (consBan b1629 (consBan b1630 (consBan b1631 (consBan b1632 (consBan b1633 (consBan b1634 (consBan b1635 (consBan b1636 (consBan b1637 (consBan b1638 (consBan b1639 (consBan b1640 (consBan b1641 (consBan b1642 (consBan b1643 (consBan b1644 (consBan b1645 (consBan b1646 (consBan b1647 (consBan b1648 (consBan b1649 (consBan b1650 (consBan b1651 (consBan b1652 (consBan b1653 (consBan b1654 (consBan b1655 (consBan b1656 (consBan b1657 (nilBan 220 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
def v1592 : List ℕ := [t0,t1,t2,t3,t4,t177,t5,t6]
theorem b1659 : Ban 220 8 v1592 := viaCut p127_82 w34 (by decide) (by decide +kernel) (by decide +kernel)
def v1593 : List ℕ := [t240,t0,t1,t2,t3,t4,t5,t6]
theorem b1660 : Ban 220 8 v1593 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1594 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t241]
theorem b1661 : Ban 220 8 v1594 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1595 : List ℕ := [t0,t1,t242,t2,t3,t4,t5,t6]
theorem b1662 : Ban 220 8 v1595 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1596 : List ℕ := [t0,t1,t2,t3,t4,t5,t243,t6]
theorem b1663 : Ban 220 8 v1596 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1597 : List ℕ := [t206,t0,t1,t2,t3,t4,t5,t6]
theorem b1664 : Ban 220 8 v1597 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1598 : List ℕ := [t0,t1,t2,t3,t4,t207,t5,t6]
def v1599 : List ℕ := [t88,t93,t89,t90,t101,t91]
theorem b1665 : Ban 55 5 v1599 := viaSmall (by decide +kernel) (by decide)
def v1600 : List ℕ := [t94,t88,t89,t90,t101,t91]
theorem b1666 : Ban 55 5 v1600 := viaSmall (by decide +kernel) (by decide)
def v1601 : List ℕ := [t88,t97,t90,t101,t91]
def v1602 : List ℕ := [t88,t281,t90,t101,t91]
theorem b1667 : Ban 55 4 v1602 := viaSmall (by decide +kernel) (by decide)
def t422 : ℕ := 0x10720e41c83907000ffffffff800
def v1603 : List ℕ := [t88,t422,t90,t101,t91]
theorem b1668 : Ban 55 4 v1603 := viaSmall (by decide +kernel) (by decide)
def v1604 : List ℕ := [t97,t101,t113,t91]
theorem b1669 : Ban 55 4 v1604 := viaSmall (by decide +kernel) (by decide)
def v1605 : List ℕ := [t88,t97,t101,t113,t91]
theorem b1670 : Ban 55 4 v1605 := viaSmall (by decide +kernel) (by decide)
def v1606 : List ℕ := [t97,t90,t101,t113,t91]
theorem b1671 : Ban 55 4 v1606 := viaSmall (by decide +kernel) (by decide)
def v1607 : List ℕ := [t114,t97,t90,t101,t91]
theorem b1672 : Ban 55 4 v1607 := viaSmall (by decide +kernel) (by decide)
def v1608 : List ℕ := [t88,t97,t115,t101,t91]
theorem b1673 : Ban 55 4 v1608 := viaSmall (by decide +kernel) (by decide)
def t423 : ℕ := 0x1fffff800
def v1609 : List ℕ := [t423,t88,t97,t101,t91]
theorem b1674 : Ban 55 4 v1609 := viaSmall (by decide +kernel) (by decide)
def v1610 : List ℕ := [t423,t88,t90,t101,t91]
theorem b1675 : Ban 55 4 v1610 := viaSmall (by decide +kernel) (by decide)
def v1611 : List ℕ := [t88,t377,t97,t101,t91]
theorem b1676 : Ban 55 4 v1611 := viaSmall (by decide +kernel) (by decide)
def t424 : ℕ := 0x2604c09813026000000000000000
def v1612 : List ℕ := [t88,t424,t90,t101,t91]
theorem b1677 : Ban 55 4 v1612 := viaSmall (by decide +kernel) (by decide)
def t425 : ℕ := 0x500a01402805000fffffffffff
def v1613 : List ℕ := [t425,t88,t90,t91]
theorem b1678 : Ban 55 4 v1613 := viaSmall (by decide +kernel) (by decide)
def v1614 : List ℕ := [t425,t88,t97,t90,t91]
theorem b1679 : Ban 55 4 v1614 := viaSmall (by decide +kernel) (by decide)
def v1615 : List ℕ := [t425,t88,t90,t101,t91]
theorem b1680 : Ban 55 4 v1615 := viaSmall (by decide +kernel) (by decide)
def v1616 : List ℕ := [t88,t385,t97,t90,t91]
theorem b1681 : Ban 55 4 v1616 := viaSmall (by decide +kernel) (by decide)
def v1617 : List ℕ := [t88,t90,t101,t91,t394]
theorem b1682 : Ban 55 4 v1617 := viaSmall (by decide +kernel) (by decide)
def t426 : ℕ := 0x1702e05c0b817000001ffffffff
def v1618 : List ℕ := [t426,t88,t90,t101,t91]
theorem b1683 : Ban 55 4 v1618 := viaSmall (by decide +kernel) (by decide)
def v1619 : List ℕ := [t102,t88,t97,t90,t91]
theorem b1684 : Ban 55 4 v1619 := viaSmall (by decide +kernel) (by decide)
def v1620 : List ℕ := [t102,t88,t97,t101,t91]
theorem b1685 : Ban 55 4 v1620 := viaSmall (by decide +kernel) (by decide)
def v1621 : List ℕ := [t88,t97,t101,t129]
theorem b1686 : Ban 55 4 v1621 := viaSmall (by decide +kernel) (by decide)
def v1622 : List ℕ := [t88,t97,t90,t101,t129]
theorem b1687 : Ban 55 4 v1622 := viaSmall (by decide +kernel) (by decide)
def v1623 : List ℕ := [t88,t97,t101,t91,t129]
theorem b1688 : Ban 55 4 v1623 := viaSmall (by decide +kernel) (by decide)
def v1624 : List ℕ := [t88,t130,t97,t101,t91]
theorem b1689 : Ban 55 4 v1624 := viaSmall (by decide +kernel) (by decide)
def v1625 : List ℕ := [t88,t97,t131,t90,t101]
theorem b1690 : Ban 55 4 v1625 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1691 : Ban 55 5 v1601 := viaBranch (ws := [v1602,v1603,v1604,v1605,v1606,v1607,v1608,v1609,v1610,v1611,v1612,v1613,v1614,v1615,v1616,v1617,v1618,v1619,v1620,v1621,v1622,v1623,v1624,v1625]) (consBan b1667 (consBan b1668 (consBan b1669 (consBan b1670 (consBan b1671 (consBan b1672 (consBan b1673 (consBan b1674 (consBan b1675 (consBan b1676 (consBan b1677 (consBan b1678 (consBan b1679 (consBan b1680 (consBan b1681 (consBan b1682 (consBan b1683 (consBan b1684 (consBan b1685 (consBan b1686 (consBan b1687 (consBan b1688 (consBan b1689 (consBan b1690 (nilBan 55 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
def v1626 : List ℕ := [t87,t88,t97,t90,t101,t91]
theorem b1692 : Ban 55 5 v1626 := viaSmall (by decide +kernel) (by decide)
def v1627 : List ℕ := [t88,t89,t97,t90,t101,t91]
theorem b1693 : Ban 55 5 v1627 := viaSmall (by decide +kernel) (by decide)
def v1628 : List ℕ := [t98,t88,t89,t90,t101,t91]
theorem b1694 : Ban 55 5 v1628 := viaSmall (by decide +kernel) (by decide)
def v1629 : List ℕ := [t100,t87,t88,t89,t101,t91]
theorem b1695 : Ban 55 5 v1629 := viaSmall (by decide +kernel) (by decide)
def v1630 : List ℕ := [t100,t88,t89,t90,t101,t91]
theorem b1696 : Ban 55 5 v1630 := viaSmall (by decide +kernel) (by decide)
def v1631 : List ℕ := [t102,t87,t88,t89,t101,t91]
theorem b1697 : Ban 55 5 v1631 := viaSmall (by decide +kernel) (by decide)
def v1632 : List ℕ := [t88,t89,t103,t90,t101,t91]
theorem b1698 : Ban 55 5 v1632 := viaSmall (by decide +kernel) (by decide)
def v1633 : List ℕ := [t88,t89,t90,t101,t91,t105]
theorem b1699 : Ban 55 5 v1633 := viaSmall (by decide +kernel) (by decide)
def v1634 : List ℕ := [t106,t88,t89,t90,t101,t91]
theorem b1700 : Ban 55 5 v1634 := viaSmall (by decide +kernel) (by decide)
def v1635 : List ℕ := [t87,t110,t89,t90,t101,t91]
theorem b1701 : Ban 55 5 v1635 := viaSmall (by decide +kernel) (by decide)
def v1636 : List ℕ := [t87,t88,t111,t90,t101,t91]
theorem b1702 : Ban 55 5 v1636 := viaSmall (by decide +kernel) (by decide)
def v1637 : List ℕ := [t87,t89,t101,t113,t91]
theorem b1703 : Ban 55 5 v1637 := viaSmall (by decide +kernel) (by decide)
def v1638 : List ℕ := [t87,t88,t89,t101,t113,t91]
theorem b1704 : Ban 55 5 v1638 := viaSmall (by decide +kernel) (by decide)
def v1639 : List ℕ := [t87,t89,t90,t101,t113,t91]
theorem b1705 : Ban 55 5 v1639 := viaSmall (by decide +kernel) (by decide)
def v1640 : List ℕ := [t87,t88,t89,t115,t101,t91]
theorem b1706 : Ban 55 5 v1640 := viaSmall (by decide +kernel) (by decide)
def t427 : ℕ := 0x4008010020040000000000007ff
def v1641 : List ℕ := [t87,t427,t88,t89,t90,t91]
theorem b1707 : Ban 55 5 v1641 := viaSmall (by decide +kernel) (by decide)
def t428 : ℕ := 0x27d4fa9f53ea7d7fffffffffffff
def v1642 : List ℕ := [t87,t88,t89,t90,t428,t91]
theorem b1708 : Ban 55 5 v1642 := viaSmall (by decide +kernel) (by decide)
def v1643 : List ℕ := [t87,t364,t88,t89,t90,t91]
theorem b1709 : Ban 55 5 v1643 := viaSmall (by decide +kernel) (by decide)
def t429 : ℕ := 0x22544a89512a25000ffffffff800
def v1644 : List ℕ := [t87,t88,t89,t429,t90,t91]
theorem b1710 : Ban 55 5 v1644 := viaSmall (by decide +kernel) (by decide)
def v1645 : List ℕ := [t120,t87,t88,t90,t101,t91]
theorem b1711 : Ban 55 5 v1645 := viaSmall (by decide +kernel) (by decide)
def v1646 : List ℕ := [t87,t88,t89,t101,t121,t91]
theorem b1712 : Ban 55 5 v1646 := viaSmall (by decide +kernel) (by decide)
def v1647 : List ℕ := [t87,t88,t123,t101,t91]
theorem b1713 : Ban 55 5 v1647 := viaSmall (by decide +kernel) (by decide)
def v1648 : List ℕ := [t87,t88,t89,t123,t101,t91]
theorem b1714 : Ban 55 5 v1648 := viaSmall (by decide +kernel) (by decide)
def v1649 : List ℕ := [t87,t88,t123,t90,t101,t91]
theorem b1715 : Ban 55 5 v1649 := viaSmall (by decide +kernel) (by decide)
def t430 : ℕ := 0x400801002004000001ffc00000
def v1650 : List ℕ := [t430,t87,t88,t90,t91]
theorem b1716 : Ban 55 5 v1650 := viaSmall (by decide +kernel) (by decide)
def v1651 : List ℕ := [t430,t87,t88,t89,t90,t91]
theorem b1717 : Ban 55 5 v1651 := viaSmall (by decide +kernel) (by decide)
def v1652 : List ℕ := [t430,t87,t88,t90,t101,t91]
theorem b1718 : Ban 55 5 v1652 := viaSmall (by decide +kernel) (by decide)
def v1653 : List ℕ := [t87,t88,t89,t90,t376,t91]
theorem b1719 : Ban 55 5 v1653 := viaSmall (by decide +kernel) (by decide)
def v1654 : List ℕ := [t87,t88,t385,t89,t90,t91]
theorem b1720 : Ban 55 5 v1654 := viaSmall (by decide +kernel) (by decide)
def t431 : ℕ := 0x2614c298530a61000ffe003fffff
def v1655 : List ℕ := [t87,t88,t90,t431,t91]
theorem b1721 : Ban 55 5 v1655 := viaSmall (by decide +kernel) (by decide)
def v1656 : List ℕ := [t87,t88,t89,t90,t431,t91]
theorem b1722 : Ban 55 5 v1656 := viaSmall (by decide +kernel) (by decide)
def v1657 : List ℕ := [t87,t88,t90,t431,t101,t91]
theorem b1723 : Ban 55 5 v1657 := viaSmall (by decide +kernel) (by decide)
def v1658 : List ℕ := [t87,t126,t88,t90,t101,t91]
theorem b1724 : Ban 55 5 v1658 := viaSmall (by decide +kernel) (by decide)
def v1659 : List ℕ := [t87,t88,t89,t90,t101,t127]
theorem b1725 : Ban 55 5 v1659 := viaSmall (by decide +kernel) (by decide)
def v1660 : List ℕ := [t87,t88,t89,t101,t129]
theorem b1726 : Ban 55 5 v1660 := viaSmall (by decide +kernel) (by decide)
def v1661 : List ℕ := [t87,t88,t89,t90,t101,t129]
theorem b1727 : Ban 55 5 v1661 := viaSmall (by decide +kernel) (by decide)
def v1662 : List ℕ := [t87,t88,t89,t101,t91,t129]
theorem b1728 : Ban 55 5 v1662 := viaSmall (by decide +kernel) (by decide)
def v1663 : List ℕ := [t87,t88,t130,t89,t101,t91]
theorem b1729 : Ban 55 5 v1663 := viaSmall (by decide +kernel) (by decide)
def v1664 : List ℕ := [t87,t88,t89,t131,t90,t101]
theorem b1730 : Ban 55 5 v1664 := viaSmall (by decide +kernel) (by decide)
def t432 : ℕ := 0x20040080100200000ffe00000000
def v1665 : List ℕ := [t87,t88,t89,t432,t90,t91]
theorem b1731 : Ban 55 5 v1665 := viaSmall (by decide +kernel) (by decide)
def t433 : ℕ := 0x3e57caf95f2be57fffffffffffff
def v1666 : List ℕ := [t87,t88,t89,t90,t91,t433]
theorem b1732 : Ban 55 5 v1666 := viaSmall (by decide +kernel) (by decide)
def t434 : ℕ := 0x650ca19432865000001ffffffff
def v1667 : List ℕ := [t87,t88,t434,t89,t90,t91]
theorem b1733 : Ban 55 5 v1667 := viaSmall (by decide +kernel) (by decide)
def t435 : ℕ := 0x180300600c01807ff00000000000
def v1668 : List ℕ := [t87,t88,t89,t435,t90,t91]
theorem b1734 : Ban 55 5 v1668 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1735 : Ban 55 6 v122 := viaBranch (ws := [v1599,v1600,v1601,v1626,v1627,v1628,v1073,v1629,v1630,v1631,v1632,v124,v1633,v1634,v501,v552,v1635,v1636,v1637,v1638,v1639,v897,v1640,v1641,v1642,v1643,v1644,v1645,v1646,v1647,v1648,v1649,v1650,v1651,v1652,v1653,v1654,v1655,v1656,v1657,v1186,v1226,v1658,v1659,v123,v1660,v1661,v1662,v1663,v1664,v1665,v1666,v1667,v1668]) (consBan b1665 (consBan b1666 (consBan b1691 (consBan b1692 (consBan b1693 (consBan b1694 (consBan b1133 (consBan b1695 (consBan b1696 (consBan b1697 (consBan b1698 (consBan b121 (consBan b1699 (consBan b1700 (consBan b504 (consBan b556 (consBan b1701 (consBan b1702 (consBan b1703 (consBan b1704 (consBan b1705 (consBan b904 (consBan b1706 (consBan b1707 (consBan b1708 (consBan b1709 (consBan b1710 (consBan b1711 (consBan b1712 (consBan b1713 (consBan b1714 (consBan b1715 (consBan b1716 (consBan b1717 (consBan b1718 (consBan b1719 (consBan b1720 (consBan b1721 (consBan b1722 (consBan b1723 (consBan b1248 (consBan b1289 (consBan b1724 (consBan b1725 (consBan b120 (consBan b1726 (consBan b1727 (consBan b1728 (consBan b1729 (consBan b1730 (consBan b1731 (consBan b1732 (consBan b1733 (consBan b1734 (nilBan 55 5))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w51 : Wide 55 6 v122 := viaSub (ws := [v108,v122]) (consBan b168 (consBan b1735 (nilBan 55 6))) (by decide) (by decide +kernel)
theorem b1736 : Ban 220 8 v1598 := viaCut p127_61 w51 (by decide) (by decide +kernel) (by decide +kernel)
def v1669 : List ℕ := [t0,t1,t2,t208,t3,t4,t5,t6]
theorem b1737 : Ban 220 8 v1669 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1670 : List ℕ := [t0,t1,t2,t3,t209,t4,t5,t6]
theorem b1738 : Ban 220 8 v1670 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1671 : List ℕ := [t0,t1,t2,t210,t3,t4,t5,t6]
theorem b1739 : Ban 220 8 v1671 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1672 : List ℕ := [t0,t1,t2,t3,t4,t246,t6]
def v1673 : List ℕ := [t92,t87,t88,t89,t90,t129]
theorem b1740 : Ban 55 5 v1673 := viaSmall (by decide +kernel) (by decide)
def v1674 : List ℕ := [t87,t88,t93,t89,t90,t129]
theorem b1741 : Ban 55 5 v1674 := viaSmall (by decide +kernel) (by decide)
def v1675 : List ℕ := [t94,t87,t88,t89,t90,t129]
theorem b1742 : Ban 55 5 v1675 := viaSmall (by decide +kernel) (by decide)
def v1676 : List ℕ := [t87,t95,t88,t89,t90,t129]
theorem b1743 : Ban 55 5 v1676 := viaSmall (by decide +kernel) (by decide)
def v1677 : List ℕ := [t96,t87,t88,t89,t90,t129]
theorem b1744 : Ban 55 5 v1677 := viaSmall (by decide +kernel) (by decide)
def v1678 : List ℕ := [t87,t88,t97,t90,t129]
theorem b1745 : Ban 55 5 v1678 := viaSmall (by decide +kernel) (by decide)
def v1679 : List ℕ := [t88,t89,t97,t90,t129]
theorem b1746 : Ban 55 5 v1679 := viaSmall (by decide +kernel) (by decide)
def v1680 : List ℕ := [t87,t88,t89,t97,t90,t129]
theorem b1747 : Ban 55 5 v1680 := viaSmall (by decide +kernel) (by decide)
def v1681 : List ℕ := [t98,t87,t88,t89,t90,t129]
theorem b1748 : Ban 55 5 v1681 := viaSmall (by decide +kernel) (by decide)
def v1682 : List ℕ := [t87,t88,t99,t89,t90,t129]
theorem b1749 : Ban 55 5 v1682 := viaSmall (by decide +kernel) (by decide)
def v1683 : List ℕ := [t100,t87,t88,t89,t90,t129]
theorem b1750 : Ban 55 5 v1683 := viaSmall (by decide +kernel) (by decide)
def v1684 : List ℕ := [t102,t87,t88,t89,t90,t129]
theorem b1751 : Ban 55 5 v1684 := viaSmall (by decide +kernel) (by decide)
def v1685 : List ℕ := [t87,t88,t89,t103,t129]
theorem b1752 : Ban 55 5 v1685 := viaSmall (by decide +kernel) (by decide)
def v1686 : List ℕ := [t87,t88,t89,t103,t90,t129]
theorem b1753 : Ban 55 5 v1686 := viaSmall (by decide +kernel) (by decide)
def t436 : ℕ := 0xffe003ff800
def v1687 : List ℕ := [t436,t87,t88,t89,t90,t129]
theorem b1754 : Ban 55 5 v1687 := viaSmall (by decide +kernel) (by decide)
def v1688 : List ℕ := [t87,t88,t89,t90,t129,t433]
theorem b1755 : Ban 55 5 v1688 := viaSmall (by decide +kernel) (by decide)
def t437 : ℕ := 0x500a01402805000000000007ff
def v1689 : List ℕ := [t437,t87,t88,t89,t90,t129]
theorem b1756 : Ban 55 5 v1689 := viaSmall (by decide +kernel) (by decide)
def t438 : ℕ := 0x3e07c0f81f03e07ff001ffc00000
def v1690 : List ℕ := [t87,t88,t89,t90,t438,t129]
theorem b1757 : Ban 55 5 v1690 := viaSmall (by decide +kernel) (by decide)
def v1691 : List ℕ := [t87,t108,t88,t89,t90,t129]
theorem b1758 : Ban 55 5 v1691 := viaSmall (by decide +kernel) (by decide)
def v1692 : List ℕ := [t87,t88,t89,t109,t90,t129]
theorem b1759 : Ban 55 5 v1692 := viaSmall (by decide +kernel) (by decide)
def v1693 : List ℕ := [t87,t110,t89,t90,t129]
theorem b1760 : Ban 55 5 v1693 := viaSmall (by decide +kernel) (by decide)
def v1694 : List ℕ := [t87,t110,t88,t89,t90,t129]
theorem b1761 : Ban 55 5 v1694 := viaSmall (by decide +kernel) (by decide)
def v1695 : List ℕ := [t87,t88,t111,t90,t129]
theorem b1762 : Ban 55 5 v1695 := viaSmall (by decide +kernel) (by decide)
def v1696 : List ℕ := [t87,t88,t111,t89,t90,t129]
theorem b1763 : Ban 55 5 v1696 := viaSmall (by decide +kernel) (by decide)
def v1697 : List ℕ := [t87,t112,t88,t89,t90,t129]
theorem b1764 : Ban 55 5 v1697 := viaSmall (by decide +kernel) (by decide)
def v1698 : List ℕ := [t87,t89,t90,t113,t129]
theorem b1765 : Ban 55 5 v1698 := viaCut p61_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1699 : List ℕ := [t87,t88,t89,t90,t113,t129]
theorem b1766 : Ban 55 5 v1699 := viaSmall (by decide +kernel) (by decide)
def v1700 : List ℕ := [t87,t114,t88,t89,t90,t129]
theorem b1767 : Ban 55 5 v1700 := viaSmall (by decide +kernel) (by decide)
def v1701 : List ℕ := [t87,t88,t89,t115,t90,t129]
theorem b1768 : Ban 55 5 v1701 := viaSmall (by decide +kernel) (by decide)
def t439 : ℕ := 0x40080100200407ff00000000000
def v1702 : List ℕ := [t87,t439,t88,t89,t90,t129]
theorem b1769 : Ban 55 5 v1702 := viaSmall (by decide +kernel) (by decide)
def t440 : ℕ := 0x3f87f0fe1fc3f87fffffffffffff
def v1703 : List ℕ := [t87,t88,t89,t90,t129,t440]
theorem b1770 : Ban 55 5 v1703 := viaSmall (by decide +kernel) (by decide)
def v1704 : List ℕ := [t87,t367,t88,t89,t90,t129]
theorem b1771 : Ban 55 5 v1704 := viaSmall (by decide +kernel) (by decide)
def t441 : ℕ := 0x3a0740e81d03a0000ffffffff800
def v1705 : List ℕ := [t87,t88,t89,t90,t441,t129]
theorem b1772 : Ban 55 5 v1705 := viaSmall (by decide +kernel) (by decide)
def v1706 : List ℕ := [t120,t87,t88,t90,t129]
theorem b1773 : Ban 55 5 v1706 := viaCut p61_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1707 : List ℕ := [t120,t87,t88,t89,t90,t129]
theorem b1774 : Ban 55 5 v1707 := viaSmall (by decide +kernel) (by decide)
def v1708 : List ℕ := [t87,t88,t89,t90,t121,t129]
theorem b1775 : Ban 55 5 v1708 := viaSmall (by decide +kernel) (by decide)
def v1709 : List ℕ := [t87,t88,t122,t89,t90,t129]
theorem b1776 : Ban 55 5 v1709 := viaSmall (by decide +kernel) (by decide)
def v1710 : List ℕ := [t87,t88,t123,t90,t129]
theorem b1777 : Ban 55 5 v1710 := viaCut p61_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1711 : List ℕ := [t87,t88,t89,t123,t90,t129]
theorem b1778 : Ban 55 5 v1711 := viaSmall (by decide +kernel) (by decide)
def t442 : ℕ := 0x10020040080100000001ffc00000
def v1712 : List ℕ := [t87,t88,t442,t90,t129]
theorem b1779 : Ban 55 5 v1712 := viaSmall (by decide +kernel) (by decide)
def v1713 : List ℕ := [t87,t88,t442,t89,t90,t129]
theorem b1780 : Ban 55 5 v1713 := viaSmall (by decide +kernel) (by decide)
def v1714 : List ℕ := [t87,t88,t89,t90,t129,t400]
theorem b1781 : Ban 55 5 v1714 := viaSmall (by decide +kernel) (by decide)
def t443 : ℕ := 0x1602c0580b01600000000000000
def v1715 : List ℕ := [t87,t443,t88,t89,t90,t129]
theorem b1782 : Ban 55 5 v1715 := viaSmall (by decide +kernel) (by decide)
def t444 : ℕ := 0x2e05c0b81702e07ffffe003ff800
def v1716 : List ℕ := [t87,t88,t90,t444]
theorem b1783 : Ban 55 5 v1716 := viaSmall (by decide +kernel) (by decide)
def v1717 : List ℕ := [t87,t88,t89,t90,t444]
theorem b1784 : Ban 55 5 v1717 := viaSmall (by decide +kernel) (by decide)
def v1718 : List ℕ := [t87,t88,t90,t444,t129]
theorem b1785 : Ban 55 5 v1718 := viaSmall (by decide +kernel) (by decide)
def v1719 : List ℕ := [t87,t88,t89,t90,t444,t129]
theorem b1786 : Ban 55 5 v1719 := viaSmall (by decide +kernel) (by decide)
def v1720 : List ℕ := [t87,t88,t89,t131,t129]
theorem b1787 : Ban 55 5 v1720 := viaSmall (by decide +kernel) (by decide)
def v1721 : List ℕ := [t87,t88,t89,t131,t90,t129]
theorem b1788 : Ban 55 5 v1721 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1789 : Ban 55 6 v164 := viaBranch (ws := [v1673,v1674,v1675,v1676,v1677,v1678,v1679,v1680,v1166,v1681,v1111,v1682,v1683,v1660,v1661,v1684,v1685,v1686,v1687,v1688,v1689,v1690,v1691,v533,v582,v1692,v1693,v1694,v1695,v1696,v1697,v1698,v1699,v933,v1700,v1701,v1702,v1703,v1704,v1705,v1706,v1707,v1708,v1709,v1710,v1711,v1712,v1713,v1215,v1714,v1715,v1716,v1717,v1718,v1719,v169,v1720,v1721]) (consBan b1740 (consBan b1741 (consBan b1742 (consBan b1743 (consBan b1744 (consBan b1745 (consBan b1746 (consBan b1747 (consBan b1227 (consBan b1748 (consBan b1171 (consBan b1749 (consBan b1750 (consBan b1726 (consBan b1727 (consBan b1751 (consBan b1752 (consBan b1753 (consBan b1754 (consBan b1755 (consBan b1756 (consBan b1757 (consBan b1758 (consBan b536 (consBan b586 (consBan b1759 (consBan b1760 (consBan b1761 (consBan b1762 (consBan b1763 (consBan b1764 (consBan b1765 (consBan b1766 (consBan b940 (consBan b1767 (consBan b1768 (consBan b1769 (consBan b1770 (consBan b1771 (consBan b1772 (consBan b1773 (consBan b1774 (consBan b1775 (consBan b1776 (consBan b1777 (consBan b1778 (consBan b1779 (consBan b1780 (consBan b1277 (consBan b1781 (consBan b1782 (consBan b1783 (consBan b1784 (consBan b1785 (consBan b1786 (consBan b166 (consBan b1787 (consBan b1788 (nilBan 55 5))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w52 : Wide 55 6 v164 := viaSub (ws := [v164]) (consBan b1789 (nilBan 55 6)) (by decide) (by decide +kernel)
theorem b1790 : Ban 220 8 v1672 := viaCut p127_61 w52 (by decide) (by decide +kernel) (by decide +kernel)
def v1722 : List ℕ := [t0,t1,t2,t4,t5,t246,t6]
theorem b1791 : Ban 60 5 v777 := viaSmall (by decide +kernel) (by decide)
theorem b1792 : Ban 60 5 v778 := viaSmall (by decide +kernel) (by decide)
theorem b1793 : Ban 60 5 v779 := viaSmall (by decide +kernel) (by decide)
theorem b1794 : Ban 60 5 v780 := viaSmall (by decide +kernel) (by decide)
theorem b1795 : Ban 60 5 v781 := viaSmall (by decide +kernel) (by decide)
theorem b1796 : Ban 60 5 v782 := viaSmall (by decide +kernel) (by decide)
theorem b1797 : Ban 60 5 v783 := viaSmall (by decide +kernel) (by decide)
theorem b1798 : Ban 60 5 v784 := viaSmall (by decide +kernel) (by decide)
theorem b1799 : Ban 60 5 v785 := viaSmall (by decide +kernel) (by decide)
theorem b1800 : Ban 60 5 v786 := viaSmall (by decide +kernel) (by decide)
theorem b1801 : Ban 60 5 v787 := viaSmall (by decide +kernel) (by decide)
theorem b1802 : Ban 60 5 v788 := viaSmall (by decide +kernel) (by decide)
theorem b1803 : Ban 60 5 v789 := viaSmall (by decide +kernel) (by decide)
theorem b1804 : Ban 60 5 v790 := viaSmall (by decide +kernel) (by decide)
theorem b1805 : Ban 60 5 v791 := viaSmall (by decide +kernel) (by decide)
theorem b1806 : Ban 60 5 v792 := viaSmall (by decide +kernel) (by decide)
theorem b1807 : Ban 60 5 v793 := viaSmall (by decide +kernel) (by decide)
theorem b1808 : Ban 60 5 v794 := viaSmall (by decide +kernel) (by decide)
theorem b1809 : Ban 60 5 v795 := viaSmall (by decide +kernel) (by decide)
theorem b1810 : Ban 60 5 v796 := viaSmall (by decide +kernel) (by decide)
theorem b1811 : Ban 60 5 v797 := viaSmall (by decide +kernel) (by decide)
theorem b1812 : Ban 60 5 v798 := viaSmall (by decide +kernel) (by decide)
theorem b1813 : Ban 60 5 v799 := viaSmall (by decide +kernel) (by decide)
theorem b1814 : Ban 60 5 v800 := viaSmall (by decide +kernel) (by decide)
theorem b1815 : Ban 60 5 v801 := viaSmall (by decide +kernel) (by decide)
theorem b1816 : Ban 60 5 v802 := viaSmall (by decide +kernel) (by decide)
theorem b1817 : Ban 60 5 v803 := viaSmall (by decide +kernel) (by decide)
theorem b1818 : Ban 60 5 v37 := viaSmall (by decide +kernel) (by decide)
theorem b1819 : Ban 60 5 v804 := viaSmall (by decide +kernel) (by decide)
theorem b1820 : Ban 60 5 v805 := viaSmall (by decide +kernel) (by decide)
theorem b1821 : Ban 60 5 v806 := viaSmall (by decide +kernel) (by decide)
theorem b1822 : Ban 60 5 v807 := viaSmall (by decide +kernel) (by decide)
theorem b1823 : Ban 60 5 v808 := viaSmall (by decide +kernel) (by decide)
theorem b1824 : Ban 60 5 v809 := viaSmall (by decide +kernel) (by decide)
theorem b1825 : Ban 60 5 v810 := viaSmall (by decide +kernel) (by decide)
theorem b1826 : Ban 60 5 v811 := viaSmall (by decide +kernel) (by decide)
theorem b1827 : Ban 60 5 v812 := viaSmall (by decide +kernel) (by decide)
theorem b1828 : Ban 60 5 v813 := viaSmall (by decide +kernel) (by decide)
theorem b1829 : Ban 60 5 v814 := viaSmall (by decide +kernel) (by decide)
theorem b1830 : Ban 60 5 v815 := viaSmall (by decide +kernel) (by decide)
theorem b1831 : Ban 60 5 v816 := viaSmall (by decide +kernel) (by decide)
theorem b1832 : Ban 60 5 v817 := viaSmall (by decide +kernel) (by decide)
theorem b1833 : Ban 60 5 v818 := viaSmall (by decide +kernel) (by decide)
theorem b1834 : Ban 60 5 v819 := viaSmall (by decide +kernel) (by decide)
theorem b1835 : Ban 60 5 v820 := viaSmall (by decide +kernel) (by decide)
theorem b1836 : Ban 60 5 v821 := viaSmall (by decide +kernel) (by decide)
theorem b1837 : Ban 60 5 v822 := viaSmall (by decide +kernel) (by decide)
theorem b1838 : Ban 60 5 v823 := viaSmall (by decide +kernel) (by decide)
theorem b1839 : Ban 60 5 v824 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1840 : Ban 60 6 v776 := viaBranch (ws := [v777,v778,v779,v780,v781,v782,v783,v784,v785,v786,v787,v788,v789,v790,v791,v792,v793,v794,v795,v796,v797,v798,v799,v800,v801,v802,v803,v37,v804,v805,v806,v807,v808,v809,v810,v811,v812,v813,v814,v815,v816,v817,v818,v819,v820,v821,v822,v823,v824]) (consBan b1791 (consBan b1792 (consBan b1793 (consBan b1794 (consBan b1795 (consBan b1796 (consBan b1797 (consBan b1798 (consBan b1799 (consBan b1800 (consBan b1801 (consBan b1802 (consBan b1803 (consBan b1804 (consBan b1805 (consBan b1806 (consBan b1807 (consBan b1808 (consBan b1809 (consBan b1810 (consBan b1811 (consBan b1812 (consBan b1813 (consBan b1814 (consBan b1815 (consBan b1816 (consBan b1817 (consBan b1818 (consBan b1819 (consBan b1820 (consBan b1821 (consBan b1822 (consBan b1823 (consBan b1824 (consBan b1825 (consBan b1826 (consBan b1827 (consBan b1828 (consBan b1829 (consBan b1830 (consBan b1831 (consBan b1832 (consBan b1833 (consBan b1834 (consBan b1835 (consBan b1836 (consBan b1837 (consBan b1838 (consBan b1839 (nilBan 60 5)))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w53 : Wide 60 6 v776 := viaSub (ws := [v776]) (consBan b1840 (nilBan 60 6)) (by decide) (by decide +kernel)
def p127_122 : Projection 220 60 := pick [40,42,48,49,52,53,54,56,57,59,100,102,108,109,112,113,114,116,117,119,120,122,128,129,132,133,134,136,137,139,140,142,148,149,152,153,154,156,157,159,180,182,188,189,192,193,194,196,197,199,200,202,208,209,212,213,214,216,217,219] rfl (by decide +kernel) (by decide)
theorem b1841 : Ban 220 8 v1722 := viaCut p127_122 w53 (by decide) (by decide +kernel) (by decide +kernel)
def v1723 : List ℕ := [t0,t1,t2,t3,t4,t5,t246,t6]
theorem b1842 : Ban 220 8 v1723 := viaCut p127_109 w42 (by decide) (by decide +kernel) (by decide +kernel)
def v1724 : List ℕ := [t0,t1,t214,t2,t4,t5,t6]
def v1725 : List ℕ := [t92,t87,t88,t130,t89,t91]
theorem b1843 : Ban 55 5 v1725 := viaSmall (by decide +kernel) (by decide)
def v1726 : List ℕ := [t87,t88,t93,t130,t89,t91]
theorem b1844 : Ban 55 5 v1726 := viaSmall (by decide +kernel) (by decide)
def v1727 : List ℕ := [t94,t87,t88,t130,t89,t91]
theorem b1845 : Ban 55 5 v1727 := viaSmall (by decide +kernel) (by decide)
def v1728 : List ℕ := [t87,t95,t88,t130,t89,t91]
theorem b1846 : Ban 55 5 v1728 := viaSmall (by decide +kernel) (by decide)
def v1729 : List ℕ := [t100,t87,t88,t130,t89,t91]
theorem b1847 : Ban 55 5 v1729 := viaSmall (by decide +kernel) (by decide)
def t445 : ℕ := 0x650ca19432865000fffffffffff
def v1730 : List ℕ := [t87,t88,t130,t445,t89,t91]
theorem b1848 : Ban 55 5 v1730 := viaSmall (by decide +kernel) (by decide)
def v1731 : List ℕ := [t102,t87,t88,t130,t89,t91]
theorem b1849 : Ban 55 5 v1731 := viaSmall (by decide +kernel) (by decide)
def t446 : ℕ := 0x600c018030060000001ffc00000
def v1732 : List ℕ := [t87,t88,t446,t130,t89,t91]
theorem b1850 : Ban 55 5 v1732 := viaSmall (by decide +kernel) (by decide)
def v1733 : List ℕ := [t96,t87,t88,t130,t89,t91]
theorem b1851 : Ban 55 5 v1733 := viaSmall (by decide +kernel) (by decide)
def v1734 : List ℕ := [t87,t88,t130,t97,t91]
theorem b1852 : Ban 55 5 v1734 := viaSmall (by decide +kernel) (by decide)
def v1735 : List ℕ := [t88,t130,t89,t97,t91]
theorem b1853 : Ban 55 5 v1735 := viaSmall (by decide +kernel) (by decide)
def v1736 : List ℕ := [t87,t88,t130,t89,t97,t91]
theorem b1854 : Ban 55 5 v1736 := viaSmall (by decide +kernel) (by decide)
def v1737 : List ℕ := [t98,t87,t88,t130,t89,t91]
theorem b1855 : Ban 55 5 v1737 := viaSmall (by decide +kernel) (by decide)
def v1738 : List ℕ := [t87,t88,t130,t99,t89,t91]
theorem b1856 : Ban 55 5 v1738 := viaSmall (by decide +kernel) (by decide)
def v1739 : List ℕ := [t104,t87,t88,t130,t89,t91]
theorem b1857 : Ban 55 5 v1739 := viaSmall (by decide +kernel) (by decide)
def v1740 : List ℕ := [t87,t88,t130,t89,t91,t105]
theorem b1858 : Ban 55 5 v1740 := viaSmall (by decide +kernel) (by decide)
def v1741 : List ℕ := [t106,t87,t88,t130,t89,t91]
theorem b1859 : Ban 55 5 v1741 := viaSmall (by decide +kernel) (by decide)
def v1742 : List ℕ := [t87,t88,t130,t89,t107,t91]
theorem b1860 : Ban 55 5 v1742 := viaSmall (by decide +kernel) (by decide)
def v1743 : List ℕ := [t87,t112,t88,t130,t89,t91]
theorem b1861 : Ban 55 5 v1743 := viaSmall (by decide +kernel) (by decide)
def t447 : ℕ := 0x780f01e03c0787ff001ffffffff
def v1744 : List ℕ := [t87,t88,t447,t89,t91]
theorem b1862 : Ban 55 5 v1744 := viaSmall (by decide +kernel) (by decide)
def v1745 : List ℕ := [t87,t130,t447,t89,t91]
theorem b1863 : Ban 55 5 v1745 := viaCut p61_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1746 : List ℕ := [t87,t88,t130,t447,t89,t91]
theorem b1864 : Ban 55 5 v1746 := viaSmall (by decide +kernel) (by decide)
def v1747 : List ℕ := [t87,t114,t88,t130,t89,t91]
theorem b1865 : Ban 55 5 v1747 := viaSmall (by decide +kernel) (by decide)
def v1748 : List ℕ := [t87,t372,t88,t130,t89,t91]
theorem b1866 : Ban 55 5 v1748 := viaSmall (by decide +kernel) (by decide)
def v1749 : List ℕ := [t87,t108,t88,t130,t89,t91]
theorem b1867 : Ban 55 5 v1749 := viaSmall (by decide +kernel) (by decide)
def v1750 : List ℕ := [t87,t88,t130,t89,t109,t91]
theorem b1868 : Ban 55 5 v1750 := viaSmall (by decide +kernel) (by decide)
def v1751 : List ℕ := [t87,t110,t130,t89,t91]
theorem b1869 : Ban 55 5 v1751 := viaSmall (by decide +kernel) (by decide)
def v1752 : List ℕ := [t87,t110,t88,t130,t89,t91]
theorem b1870 : Ban 55 5 v1752 := viaSmall (by decide +kernel) (by decide)
def v1753 : List ℕ := [t87,t88,t130,t111,t91]
theorem b1871 : Ban 55 5 v1753 := viaSmall (by decide +kernel) (by decide)
def v1754 : List ℕ := [t87,t88,t130,t111,t89,t91]
theorem b1872 : Ban 55 5 v1754 := viaSmall (by decide +kernel) (by decide)
def v1755 : List ℕ := [t116,t87,t88,t130,t89,t91]
theorem b1873 : Ban 55 5 v1755 := viaSmall (by decide +kernel) (by decide)
def v1756 : List ℕ := [t87,t88,t130,t89,t91,t117]
theorem b1874 : Ban 55 5 v1756 := viaSmall (by decide +kernel) (by decide)
def v1757 : List ℕ := [t87,t118,t88,t130,t89,t91]
theorem b1875 : Ban 55 5 v1757 := viaSmall (by decide +kernel) (by decide)
def v1758 : List ℕ := [t87,t88,t130,t89,t119,t91]
theorem b1876 : Ban 55 5 v1758 := viaSmall (by decide +kernel) (by decide)
def v1759 : List ℕ := [t120,t87,t88,t130,t91]
theorem b1877 : Ban 55 5 v1759 := viaCut p61_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1760 : List ℕ := [t120,t87,t88,t130,t89,t91]
theorem b1878 : Ban 55 5 v1760 := viaSmall (by decide +kernel) (by decide)
def t448 : ℕ := 0x1762ec5d8bb176000001fffff800
def v1761 : List ℕ := [t87,t88,t130,t89,t448,t91]
theorem b1879 : Ban 55 5 v1761 := viaSmall (by decide +kernel) (by decide)
def v1762 : List ℕ := [t87,t88,t401,t130,t91]
theorem b1880 : Ban 55 5 v1762 := viaSmall (by decide +kernel) (by decide)
def v1763 : List ℕ := [t87,t88,t401,t130,t89,t91]
theorem b1881 : Ban 55 5 v1763 := viaSmall (by decide +kernel) (by decide)
def v1764 : List ℕ := [t87,t88,t130,t122,t89,t91]
theorem b1882 : Ban 55 5 v1764 := viaSmall (by decide +kernel) (by decide)
def v1765 : List ℕ := [t87,t88,t130,t89,t129]
theorem b1883 : Ban 55 5 v1765 := viaSmall (by decide +kernel) (by decide)
def v1766 : List ℕ := [t87,t88,t130,t89,t91,t129]
theorem b1884 : Ban 55 5 v1766 := viaSmall (by decide +kernel) (by decide)
def v1767 : List ℕ := [t87,t88,t130,t124,t89,t91]
theorem b1885 : Ban 55 5 v1767 := viaSmall (by decide +kernel) (by decide)
def v1768 : List ℕ := [t87,t88,t130,t89,t125]
theorem b1886 : Ban 55 5 v1768 := viaSmall (by decide +kernel) (by decide)
def v1769 : List ℕ := [t87,t88,t130,t89,t91,t125]
theorem b1887 : Ban 55 5 v1769 := viaSmall (by decide +kernel) (by decide)
def v1770 : List ℕ := [t87,t126,t88,t130,t91]
theorem b1888 : Ban 55 5 v1770 := viaSmall (by decide +kernel) (by decide)
def v1771 : List ℕ := [t87,t126,t88,t130,t89,t91]
theorem b1889 : Ban 55 5 v1771 := viaSmall (by decide +kernel) (by decide)
def v1772 : List ℕ := [t87,t88,t130,t89,t127]
theorem b1890 : Ban 55 5 v1772 := viaSmall (by decide +kernel) (by decide)
def v1773 : List ℕ := [t87,t88,t130,t89,t127,t91]
theorem b1891 : Ban 55 5 v1773 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1892 : Ban 55 6 v167 := viaBranch (ws := [v1725,v1726,v1727,v1728,v1729,v1730,v1731,v1732,v1733,v1734,v1735,v1736,v1169,v1737,v1114,v1738,v1739,v1740,v1741,v1742,v1743,v1744,v1745,v1746,v936,v1747,v993,v1748,v1749,v536,v585,v1750,v1751,v1752,v1753,v1754,v1755,v1756,v1757,v1758,v1759,v1760,v1761,v1762,v1763,v1764,v1765,v165,v1766,v1767,v1768,v1257,v1769,v1770,v1771,v1772,v1773]) (consBan b1843 (consBan b1844 (consBan b1845 (consBan b1846 (consBan b1847 (consBan b1848 (consBan b1849 (consBan b1850 (consBan b1851 (consBan b1852 (consBan b1853 (consBan b1854 (consBan b1230 (consBan b1855 (consBan b1174 (consBan b1856 (consBan b1857 (consBan b1858 (consBan b1859 (consBan b1860 (consBan b1861 (consBan b1862 (consBan b1863 (consBan b1864 (consBan b943 (consBan b1865 (consBan b1001 (consBan b1866 (consBan b1867 (consBan b539 (consBan b589 (consBan b1868 (consBan b1869 (consBan b1870 (consBan b1871 (consBan b1872 (consBan b1873 (consBan b1874 (consBan b1875 (consBan b1876 (consBan b1877 (consBan b1878 (consBan b1879 (consBan b1880 (consBan b1881 (consBan b1882 (consBan b1883 (consBan b162 (consBan b1884 (consBan b1885 (consBan b1886 (consBan b1320 (consBan b1887 (consBan b1888 (consBan b1889 (consBan b1890 (consBan b1891 (nilBan 55 5)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w54 : Wide 55 6 v167 := viaSub (ws := [v167]) (consBan b1892 (nilBan 55 6)) (by decide) (by decide +kernel)
theorem b1893 : Ban 220 8 v1724 := viaCut p127_61 w54 (by decide) (by decide +kernel) (by decide +kernel)
def v1774 : List ℕ := [t0,t1,t214,t2,t3,t4,t5,t6]
theorem b1894 : Ban 220 8 v1774 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1775 : List ℕ := [t0,t1,t2,t3,t4,t247,t6]
def v1776 : List ℕ := [t92,t87,t88,t89,t131,t90]
theorem b1895 : Ban 55 5 v1776 := viaSmall (by decide +kernel) (by decide)
def v1777 : List ℕ := [t87,t88,t93,t89,t131,t90]
theorem b1896 : Ban 55 5 v1777 := viaSmall (by decide +kernel) (by decide)
def v1778 : List ℕ := [t94,t87,t88,t89,t131,t90]
theorem b1897 : Ban 55 5 v1778 := viaSmall (by decide +kernel) (by decide)
def v1779 : List ℕ := [t87,t95,t88,t89,t131,t90]
theorem b1898 : Ban 55 5 v1779 := viaSmall (by decide +kernel) (by decide)
def v1780 : List ℕ := [t96,t87,t88,t89,t131,t90]
theorem b1899 : Ban 55 5 v1780 := viaSmall (by decide +kernel) (by decide)
def v1781 : List ℕ := [t87,t88,t97,t131,t90]
theorem b1900 : Ban 55 5 v1781 := viaSmall (by decide +kernel) (by decide)
def v1782 : List ℕ := [t88,t89,t97,t131,t90]
theorem b1901 : Ban 55 5 v1782 := viaSmall (by decide +kernel) (by decide)
def v1783 : List ℕ := [t87,t88,t89,t97,t131,t90]
theorem b1902 : Ban 55 5 v1783 := viaSmall (by decide +kernel) (by decide)
def v1784 : List ℕ := [t98,t87,t88,t89,t131,t90]
theorem b1903 : Ban 55 5 v1784 := viaSmall (by decide +kernel) (by decide)
def v1785 : List ℕ := [t87,t88,t99,t89,t131,t90]
theorem b1904 : Ban 55 5 v1785 := viaSmall (by decide +kernel) (by decide)
def v1786 : List ℕ := [t104,t87,t88,t89,t131,t90]
theorem b1905 : Ban 55 5 v1786 := viaSmall (by decide +kernel) (by decide)
def t449 : ℕ := 0x18530a614c29857ffffe003fffff
def v1787 : List ℕ := [t87,t88,t89,t131,t449,t90]
theorem b1906 : Ban 55 5 v1787 := viaSmall (by decide +kernel) (by decide)
def v1788 : List ℕ := [t106,t87,t88,t89,t131,t90]
theorem b1907 : Ban 55 5 v1788 := viaSmall (by decide +kernel) (by decide)
def v1789 : List ℕ := [t87,t88,t89,t435,t131,t90]
theorem b1908 : Ban 55 5 v1789 := viaSmall (by decide +kernel) (by decide)
def v1790 : List ℕ := [t100,t87,t88,t89,t131,t90]
theorem b1909 : Ban 55 5 v1790 := viaSmall (by decide +kernel) (by decide)
def v1791 : List ℕ := [t102,t87,t88,t89,t131,t90]
theorem b1910 : Ban 55 5 v1791 := viaSmall (by decide +kernel) (by decide)
def v1792 : List ℕ := [t87,t88,t89,t131,t103,t90]
theorem b1911 : Ban 55 5 v1792 := viaSmall (by decide +kernel) (by decide)
def v1793 : List ℕ := [t87,t108,t88,t89,t131,t90]
theorem b1912 : Ban 55 5 v1793 := viaSmall (by decide +kernel) (by decide)
def v1794 : List ℕ := [t87,t88,t89,t109,t131,t90]
theorem b1913 : Ban 55 5 v1794 := viaSmall (by decide +kernel) (by decide)
def v1795 : List ℕ := [t87,t110,t89,t131,t90]
theorem b1914 : Ban 55 5 v1795 := viaSmall (by decide +kernel) (by decide)
def v1796 : List ℕ := [t87,t110,t88,t89,t131,t90]
theorem b1915 : Ban 55 5 v1796 := viaSmall (by decide +kernel) (by decide)
def v1797 : List ℕ := [t87,t88,t111,t131,t90]
theorem b1916 : Ban 55 5 v1797 := viaSmall (by decide +kernel) (by decide)
def v1798 : List ℕ := [t87,t88,t111,t89,t131,t90]
theorem b1917 : Ban 55 5 v1798 := viaSmall (by decide +kernel) (by decide)
def v1799 : List ℕ := [t116,t87,t88,t89,t131,t90]
theorem b1918 : Ban 55 5 v1799 := viaSmall (by decide +kernel) (by decide)
def t450 : ℕ := 0x1d83b0760ec1d87ffffe000007ff
def v1800 : List ℕ := [t87,t88,t89,t131,t450,t90]
theorem b1919 : Ban 55 5 v1800 := viaSmall (by decide +kernel) (by decide)
def v1801 : List ℕ := [t87,t118,t88,t89,t131,t90]
theorem b1920 : Ban 55 5 v1801 := viaSmall (by decide +kernel) (by decide)
def t451 : ℕ := 0x180300600c0180000ffe00000000
def v1802 : List ℕ := [t87,t88,t89,t451,t131,t90]
theorem b1921 : Ban 55 5 v1802 := viaSmall (by decide +kernel) (by decide)
def v1803 : List ℕ := [t87,t112,t88,t89,t131,t90]
theorem b1922 : Ban 55 5 v1803 := viaSmall (by decide +kernel) (by decide)
def v1804 : List ℕ := [t87,t88,t89,t131,t113]
theorem b1923 : Ban 55 5 v1804 := viaSmall (by decide +kernel) (by decide)
def v1805 : List ℕ := [t87,t89,t131,t90,t113]
theorem b1924 : Ban 55 5 v1805 := viaCut p61_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1806 : List ℕ := [t87,t88,t89,t131,t90,t113]
theorem b1925 : Ban 55 5 v1806 := viaSmall (by decide +kernel) (by decide)
def v1807 : List ℕ := [t87,t114,t88,t89,t131,t90]
theorem b1926 : Ban 55 5 v1807 := viaSmall (by decide +kernel) (by decide)
def v1808 : List ℕ := [t87,t88,t89,t131,t115,t90]
theorem b1927 : Ban 55 5 v1808 := viaSmall (by decide +kernel) (by decide)
def v1809 : List ℕ := [t87,t88,t124,t89,t131,t90]
theorem b1928 : Ban 55 5 v1809 := viaSmall (by decide +kernel) (by decide)
def t452 : ℕ := 0x19632c658cb1967fffffffc00000
def v1810 : List ℕ := [t87,t88,t89,t452,t90]
theorem b1929 : Ban 55 5 v1810 := viaSmall (by decide +kernel) (by decide)
def v1811 : List ℕ := [t87,t88,t131,t452,t90]
theorem b1930 : Ban 55 5 v1811 := viaSmall (by decide +kernel) (by decide)
def v1812 : List ℕ := [t87,t88,t89,t131,t452,t90]
theorem b1931 : Ban 55 5 v1812 := viaSmall (by decide +kernel) (by decide)
def v1813 : List ℕ := [t87,t126,t88,t131,t90]
theorem b1932 : Ban 55 5 v1813 := viaSmall (by decide +kernel) (by decide)
def v1814 : List ℕ := [t87,t126,t88,t89,t131,t90]
theorem b1933 : Ban 55 5 v1814 := viaSmall (by decide +kernel) (by decide)
def t453 : ℕ := 0x80100200400807ffffe00000000
def v1815 : List ℕ := [t87,t88,t453,t89,t90]
theorem b1934 : Ban 55 5 v1815 := viaSmall (by decide +kernel) (by decide)
def v1816 : List ℕ := [t87,t88,t453,t89,t131,t90]
theorem b1935 : Ban 55 5 v1816 := viaSmall (by decide +kernel) (by decide)
def v1817 : List ℕ := [t120,t87,t88,t131,t90]
theorem b1936 : Ban 55 5 v1817 := viaCut p61_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1818 : List ℕ := [t120,t87,t88,t89,t131,t90]
theorem b1937 : Ban 55 5 v1818 := viaSmall (by decide +kernel) (by decide)
def v1819 : List ℕ := [t87,t88,t89,t131,t90,t121]
theorem b1938 : Ban 55 5 v1819 := viaSmall (by decide +kernel) (by decide)
def v1820 : List ℕ := [t87,t88,t122,t89,t131,t90]
theorem b1939 : Ban 55 5 v1820 := viaSmall (by decide +kernel) (by decide)
def v1821 : List ℕ := [t87,t88,t131,t123,t90]
theorem b1940 : Ban 55 5 v1821 := viaSmall (by decide +kernel) (by decide)
def v1822 : List ℕ := [t87,t88,t89,t131,t123,t90]
theorem b1941 : Ban 55 5 v1822 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1942 : Ban 55 6 v169 := viaBranch (ws := [v1776,v1777,v1778,v1779,v1780,v1781,v1782,v1783,v1171,v1784,v1116,v1785,v1786,v1787,v1788,v1789,v1790,v1664,v1791,v1792,v1793,v538,v587,v1794,v1795,v1796,v1797,v1798,v1799,v1800,v1801,v1802,v1803,v1804,v1805,v1806,v938,v1807,v995,v1808,v1809,v1810,v1811,v1812,v1813,v1814,v1815,v1816,v1817,v1818,v1819,v1820,v1821,v1822,v1720,v164,v1721]) (consBan b1895 (consBan b1896 (consBan b1897 (consBan b1898 (consBan b1899 (consBan b1900 (consBan b1901 (consBan b1902 (consBan b1232 (consBan b1903 (consBan b1176 (consBan b1904 (consBan b1905 (consBan b1906 (consBan b1907 (consBan b1908 (consBan b1909 (consBan b1730 (consBan b1910 (consBan b1911 (consBan b1912 (consBan b541 (consBan b591 (consBan b1913 (consBan b1914 (consBan b1915 (consBan b1916 (consBan b1917 (consBan b1918 (consBan b1919 (consBan b1920 (consBan b1921 (consBan b1922 (consBan b1923 (consBan b1924 (consBan b1925 (consBan b945 (consBan b1926 (consBan b1003 (consBan b1927 (consBan b1928 (consBan b1929 (consBan b1930 (consBan b1931 (consBan b1932 (consBan b1933 (consBan b1934 (consBan b1935 (consBan b1936 (consBan b1937 (consBan b1938 (consBan b1939 (consBan b1940 (consBan b1941 (consBan b1787 (consBan b161 (consBan b1788 (nilBan 55 5)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w55 : Wide 55 6 v169 := viaSub (ws := [v169]) (consBan b1942 (nilBan 55 6)) (by decide) (by decide +kernel)
theorem b1943 : Ban 220 8 v1775 := viaCut p127_61 w55 (by decide) (by decide +kernel) (by decide +kernel)
def v1823 : List ℕ := [t0,t1,t2,t3,t4,t247,t5,t6]
theorem b1944 : Ban 220 8 v1823 := viaCut p127_82 w34 (by decide) (by decide +kernel) (by decide +kernel)
def v1824 : List ℕ := [t218,t0,t1,t2,t3,t4,t5,t6]
theorem b1945 : Ban 220 8 v1824 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1825 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t219]
theorem b1946 : Ban 220 8 v1825 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1826 : List ℕ := [t0,t1,t2,t220,t3,t4,t5,t6]
theorem b1947 : Ban 220 8 v1826 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1827 : List ℕ := [t0,t1,t2,t3,t4,t5,t222,t6]
theorem b1948 : Ban 220 8 v1827 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1828 : List ℕ := [t224,t0,t1,t2,t3,t4,t5,t6]
theorem b1949 : Ban 220 8 v1828 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1829 : List ℕ := [t0,t1,t2,t3,t4,t5,t248,t6]
theorem b1950 : Ban 220 8 v1829 := viaCut p127_82 w34 (by decide) (by decide +kernel) (by decide +kernel)
def v1830 : List ℕ := [t0,t1,t2,t3,t226,t4,t5,t6]
theorem b1951 : Ban 220 8 v1830 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1831 : List ℕ := [t0,t1,t2,t3,t4,t249,t5,t6]
theorem b1952 : Ban 220 8 v1831 := viaCut p127_82 w34 (by decide) (by decide +kernel) (by decide +kernel)
def v1832 : List ℕ := [t0,t1,t2,t3,t228,t4,t5,t6]
theorem b1953 : Ban 220 8 v1832 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1833 : List ℕ := [t0,t1,t2,t3,t4,t5,t229]
def t454 : ℕ := 0x300c0300c0300c003ffffc00ffc00
def t455 : ℕ := 0x140501405014050ffc0000000fffff
def t456 : ℕ := 0x4290a4290a4290a00000003ff003ff
def t457 : ℕ := 0x98260982609826000000fffff00000
def t458 : ℕ := 0xe2b8ae2b8ae2b8afffff003ff003ff
def v1834 : List ℕ := [t454,t455,t456,t457,t458]
def v1835 : List ℕ := [t26,t454,t455,t456,t457,t458]
theorem b1954 : Ban 60 5 v1835 := viaSmall (by decide +kernel) (by decide)
def t459 : ℕ := 0x1705c1705c1705cfffffffc00fffff
def v1836 : List ℕ := [t454,t455,t459,t456,t457,t458]
theorem b1955 : Ban 60 5 v1836 := viaSmall (by decide +kernel) (by decide)
def t460 : ℕ := 0x300c0300c0300c003ffffc0000000
def v1837 : List ℕ := [t460,t454,t455,t456,t457,t458]
theorem b1956 : Ban 60 5 v1837 := viaSmall (by decide +kernel) (by decide)
def t461 : ℕ := 0x140501405014050ffc0000000003ff
def v1838 : List ℕ := [t454,t461,t455,t456,t457,t458]
theorem b1957 : Ban 60 5 v1838 := viaSmall (by decide +kernel) (by decide)
def v1839 : List ℕ := [t18,t454,t455,t456,t457,t458]
theorem b1958 : Ban 60 5 v1839 := viaSmall (by decide +kernel) (by decide)
def t462 : ℕ := 0x4390e4390e4390e003ffffffffffff
def v1840 : List ℕ := [t455,t456,t462,t457,t458]
theorem b1959 : Ban 60 5 v1840 := viaSmall (by decide +kernel) (by decide)
def v1841 : List ℕ := [t454,t455,t456,t462,t457,t458]
theorem b1960 : Ban 60 5 v1841 := viaSmall (by decide +kernel) (by decide)
def t463 : ℕ := 0x10040100401004003ffffc00ffc00
def v1842 : List ℕ := [t463,t455,t456,t457,t458]
theorem b1961 : Ban 60 5 v1842 := viaSmall (by decide +kernel) (by decide)
def v1843 : List ℕ := [t463,t454,t455,t456,t457,t458]
theorem b1962 : Ban 60 5 v1843 := viaSmall (by decide +kernel) (by decide)
def t464 : ℕ := 0x40902409024090200000003ff003ff
def v1844 : List ℕ := [t454,t455,t464,t456,t457,t458]
theorem b1963 : Ban 60 5 v1844 := viaSmall (by decide +kernel) (by decide)
def v1845 : List ℕ := [t30,t454,t455,t456,t457,t458]
theorem b1964 : Ban 60 5 v1845 := viaSmall (by decide +kernel) (by decide)
def t465 : ℕ := 0x9b26c9b26c9b26c003fffffffffc00
def v1846 : List ℕ := [t454,t455,t456,t457,t465,t458]
theorem b1965 : Ban 60 5 v1846 := viaSmall (by decide +kernel) (by decide)
def t466 : ℕ := 0x300c0300c0300c003ff00000ffc00
def v1847 : List ℕ := [t466,t454,t455,t456,t457,t458]
theorem b1966 : Ban 60 5 v1847 := viaSmall (by decide +kernel) (by decide)
def t467 : ℕ := 0x98260982609826000000003ff00000
def v1848 : List ℕ := [t454,t455,t456,t467,t457,t458]
theorem b1967 : Ban 60 5 v1848 := viaSmall (by decide +kernel) (by decide)
def t468 : ℕ := 0x20080200802008003ff0000000000
def v1849 : List ℕ := [t468,t454,t455,t456,t457,t458]
theorem b1968 : Ban 60 5 v1849 := viaSmall (by decide +kernel) (by decide)
def t469 : ℕ := 0xe3b8ee3b8ee3b8efffffffffffffff
def v1850 : List ℕ := [t454,t455,t456,t457,t458,t469]
theorem b1969 : Ban 60 5 v1850 := viaSmall (by decide +kernel) (by decide)
def t470 : ℕ := 0x1004010040100400000ffc00ffc00
def v1851 : List ℕ := [t470,t454,t455,t456,t457,t458]
theorem b1970 : Ban 60 5 v1851 := viaSmall (by decide +kernel) (by decide)
def t471 : ℕ := 0xe0b82e0b82e0b82ffc00003ff003ff
def v1852 : List ℕ := [t454,t455,t456,t457,t471,t458]
theorem b1971 : Ban 60 5 v1852 := viaSmall (by decide +kernel) (by decide)
def v1853 : List ℕ := [t64,t454,t455,t456,t457,t458]
theorem b1972 : Ban 60 5 v1853 := viaSmall (by decide +kernel) (by decide)
def t472 : ℕ := 0x5695a5695a5695affc00003fffffff
def v1854 : List ℕ := [t454,t455,t472,t457,t458]
theorem b1973 : Ban 60 5 v1854 := viaSmall (by decide +kernel) (by decide)
def v1855 : List ℕ := [t454,t455,t456,t472,t457,t458]
theorem b1974 : Ban 60 5 v1855 := viaSmall (by decide +kernel) (by decide)
def t473 : ℕ := 0x140501405014050ffc0000000ffc00
def v1856 : List ℕ := [t454,t473,t455,t456,t457,t458]
theorem b1975 : Ban 60 5 v1856 := viaSmall (by decide +kernel) (by decide)
def t474 : ℕ := 0x4290a4290a4290a00000003ff00000
def v1857 : List ℕ := [t454,t455,t474,t457,t458]
theorem b1976 : Ban 60 5 v1857 := viaSmall (by decide +kernel) (by decide)
def v1858 : List ℕ := [t454,t455,t474,t456,t457,t458]
theorem b1977 : Ban 60 5 v1858 := viaSmall (by decide +kernel) (by decide)
def t475 : ℕ := 0x100401004010040000000000000000
def v1859 : List ℕ := [t454,t475,t455,t456,t457,t458]
theorem b1978 : Ban 60 5 v1859 := viaSmall (by decide +kernel) (by decide)
def t476 : ℕ := 0x9c2709c2709c270ffc00ffffffffff
def v1860 : List ℕ := [t454,t455,t456,t476,t458]
theorem b1979 : Ban 60 5 v1860 := viaSmall (by decide +kernel) (by decide)
def v1861 : List ℕ := [t454,t456,t457,t476,t458]
theorem b1980 : Ban 60 5 v1861 := viaSmall (by decide +kernel) (by decide)
def v1862 : List ℕ := [t454,t455,t456,t457,t476,t458]
theorem b1981 : Ban 60 5 v1862 := viaSmall (by decide +kernel) (by decide)
def t477 : ℕ := 0x40100401004010ffc0000000fffff
def v1863 : List ℕ := [t454,t477,t456,t457,t458]
theorem b1982 : Ban 60 5 v1863 := viaSmall (by decide +kernel) (by decide)
def v1864 : List ℕ := [t454,t477,t455,t456,t457,t458]
theorem b1983 : Ban 60 5 v1864 := viaSmall (by decide +kernel) (by decide)
def t478 : ℕ := 0x88220882208822000000fffff00000
def v1865 : List ℕ := [t454,t455,t456,t478,t458]
theorem b1984 : Ban 60 5 v1865 := viaSmall (by decide +kernel) (by decide)
def v1866 : List ℕ := [t454,t455,t456,t478,t457,t458]
theorem b1985 : Ban 60 5 v1866 := viaSmall (by decide +kernel) (by decide)
def t479 : ℕ := 0xffc0000000003ff
def v1867 : List ℕ := [t479,t454,t455,t456,t457,t458]
theorem b1986 : Ban 60 5 v1867 := viaSmall (by decide +kernel) (by decide)
def t480 : ℕ := 0xf6bdaf6bdaf6bdafffff003fffffff
def v1868 : List ℕ := [t454,t455,t456,t457,t458,t480]
theorem b1987 : Ban 60 5 v1868 := viaSmall (by decide +kernel) (by decide)
def t481 : ℕ := 0x1405014050140500000000000ffc00
def v1869 : List ℕ := [t454,t481,t455,t456,t457,t458]
theorem b1988 : Ban 60 5 v1869 := viaSmall (by decide +kernel) (by decide)
def t482 : ℕ := 0xe2b8ae2b8ae2b8a003ff003ff00000
def v1870 : List ℕ := [t454,t455,t456,t457,t482,t458]
theorem b1989 : Ban 60 5 v1870 := viaSmall (by decide +kernel) (by decide)
def v1871 : List ℕ := [t35,t454,t455,t456,t457,t458]
theorem b1990 : Ban 60 5 v1871 := viaSmall (by decide +kernel) (by decide)
def t483 : ℕ := 0xdab6adab6adab6a00000fffff003ff
def v1872 : List ℕ := [t454,t455,t456,t457,t483,t458]
theorem b1991 : Ban 60 5 v1872 := viaSmall (by decide +kernel) (by decide)
def t484 : ℕ := 0x4290a4290a4290a0000000000003ff
def v1873 : List ℕ := [t454,t455,t484,t456,t457,t458]
theorem b1992 : Ban 60 5 v1873 := viaSmall (by decide +kernel) (by decide)
def t485 : ℕ := 0x98260982609826000000ffc0000000
def v1874 : List ℕ := [t454,t455,t456,t485,t457,t458]
theorem b1993 : Ban 60 5 v1874 := viaSmall (by decide +kernel) (by decide)
def t486 : ℕ := 0xa0280a0280a0280fffff0000000000
def v1875 : List ℕ := [t454,t455,t456,t457,t486]
theorem b1994 : Ban 60 5 v1875 := viaSmall (by decide +kernel) (by decide)
def v1876 : List ℕ := [t454,t455,t457,t486,t458]
theorem b1995 : Ban 60 5 v1876 := viaSmall (by decide +kernel) (by decide)
def v1877 : List ℕ := [t454,t455,t456,t457,t486,t458]
theorem b1996 : Ban 60 5 v1877 := viaSmall (by decide +kernel) (by decide)
def t487 : ℕ := 0x80200802008020000000003ff00000
def v1878 : List ℕ := [t454,t455,t456,t487,t457,t458]
theorem b1997 : Ban 60 5 v1878 := viaSmall (by decide +kernel) (by decide)
def t488 : ℕ := 0xfabeafabeafabeaffffffffff003ff
def v1879 : List ℕ := [t454,t455,t456,t457,t488]
theorem b1998 : Ban 60 5 v1879 := viaSmall (by decide +kernel) (by decide)
def v1880 : List ℕ := [t454,t455,t456,t457,t458,t488]
theorem b1999 : Ban 60 5 v1880 := viaSmall (by decide +kernel) (by decide)
def t489 : ℕ := 0x18060180601806000000ffc0000000
def v1881 : List ℕ := [t454,t455,t489,t456,t457,t458]
theorem b2000 : Ban 60 5 v1881 := viaSmall (by decide +kernel) (by decide)
def t490 : ℕ := 0x6298a6298a6298afffff00000003ff
def v1882 : List ℕ := [t454,t455,t456,t490,t457]
theorem b2001 : Ban 60 5 v1882 := viaSmall (by decide +kernel) (by decide)
def v1883 : List ℕ := [t454,t455,t456,t490,t457,t458]
theorem b2002 : Ban 60 5 v1883 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b2003 : Ban 60 6 v1834 := viaBranch (ws := [v1835,v1836,v1837,v1838,v1839,v1840,v1841,v1842,v1843,v1844,v1845,v1846,v1847,v1848,v1849,v1850,v1851,v1852,v1853,v1854,v1855,v1856,v1857,v1858,v1859,v1860,v1861,v1862,v1863,v1864,v1865,v1866,v1867,v1868,v1869,v1870,v1871,v1872,v1873,v1874,v1875,v1876,v1877,v1878,v1879,v1880,v1881,v1882,v1883]) (consBan b1954 (consBan b1955 (consBan b1956 (consBan b1957 (consBan b1958 (consBan b1959 (consBan b1960 (consBan b1961 (consBan b1962 (consBan b1963 (consBan b1964 (consBan b1965 (consBan b1966 (consBan b1967 (consBan b1968 (consBan b1969 (consBan b1970 (consBan b1971 (consBan b1972 (consBan b1973 (consBan b1974 (consBan b1975 (consBan b1976 (consBan b1977 (consBan b1978 (consBan b1979 (consBan b1980 (consBan b1981 (consBan b1982 (consBan b1983 (consBan b1984 (consBan b1985 (consBan b1986 (consBan b1987 (consBan b1988 (consBan b1989 (consBan b1990 (consBan b1991 (consBan b1992 (consBan b1993 (consBan b1994 (consBan b1995 (consBan b1996 (consBan b1997 (consBan b1998 (consBan b1999 (consBan b2000 (consBan b2001 (consBan b2002 (nilBan 60 5)))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w56 : Wide 60 6 v1834 := viaSub (ws := [v1834]) (consBan b2003 (nilBan 60 6)) (by decide) (by decide +kernel)
def p127_115 : Projection 220 60 := pick [20,21,22,23,32,34,36,37,38,39,40,41,42,43,52,54,56,57,58,59,80,81,82,83,92,94,96,97,98,99,100,101,102,103,112,114,116,117,118,119,140,141,142,143,152,154,156,157,158,159,200,201,202,203,212,214,216,217,218,219] rfl (by decide +kernel) (by decide)
theorem b2004 : Ban 220 8 v1833 := viaCut p127_115 w56 (by decide) (by decide +kernel) (by decide +kernel)
def v1884 : List ℕ := [t0,t1,t2,t3,t5,t6,t229]
theorem b2005 : Ban 220 8 v1884 := viaCut p127_61 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v1885 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t229]
theorem b2006 : Ban 220 8 v1885 := viaCut p127_61 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v1886 : List ℕ := [t230,t0,t1,t2,t3,t5,t6]
theorem b2007 : Ban 220 8 v1886 := viaCut p127_61 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v1887 : List ℕ := [t230,t0,t1,t2,t3,t4,t5,t6]
theorem b2008 : Ban 220 8 v1887 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1888 : List ℕ := [t0,t1,t2,t3,t4,t5,t231]
theorem b2009 : Ban 220 8 v1888 := viaCut p127_61 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v1889 : List ℕ := [t0,t1,t2,t3,t4,t5,t231,t6]
theorem b2010 : Ban 220 8 v1889 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1890 : List ℕ := [t0,t1,t2,t3,t4,t232,t5,t6]
theorem b2011 : Ban 220 8 v1890 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v1891 : List ℕ := [t0,t1,t2,t3,t4,t5,t250]
def t491 : ℕ := 0xf83e0f83e0f83e0ffffffffff00000
def v1892 : List ℕ := [t454,t455,t456,t457,t491]
def v1893 : List ℕ := [t26,t454,t455,t456,t457,t491]
theorem b2012 : Ban 60 5 v1893 := viaSmall (by decide +kernel) (by decide)
def v1894 : List ℕ := [t454,t455,t459,t456,t457,t491]
theorem b2013 : Ban 60 5 v1894 := viaSmall (by decide +kernel) (by decide)
def v1895 : List ℕ := [t460,t454,t455,t456,t457,t491]
theorem b2014 : Ban 60 5 v1895 := viaSmall (by decide +kernel) (by decide)
def v1896 : List ℕ := [t454,t461,t455,t456,t457,t491]
theorem b2015 : Ban 60 5 v1896 := viaSmall (by decide +kernel) (by decide)
def v1897 : List ℕ := [t18,t454,t455,t456,t457,t491]
theorem b2016 : Ban 60 5 v1897 := viaSmall (by decide +kernel) (by decide)
def v1898 : List ℕ := [t454,t455,t462,t457,t491]
theorem b2017 : Ban 60 5 v1898 := viaSmall (by decide +kernel) (by decide)
def v1899 : List ℕ := [t455,t456,t462,t457,t491]
theorem b2018 : Ban 60 5 v1899 := viaSmall (by decide +kernel) (by decide)
def v1900 : List ℕ := [t454,t455,t456,t462,t457,t491]
theorem b2019 : Ban 60 5 v1900 := viaSmall (by decide +kernel) (by decide)
def v1901 : List ℕ := [t463,t455,t456,t457,t491]
theorem b2020 : Ban 60 5 v1901 := viaSmall (by decide +kernel) (by decide)
def v1902 : List ℕ := [t463,t454,t455,t456,t457,t491]
theorem b2021 : Ban 60 5 v1902 := viaSmall (by decide +kernel) (by decide)
def v1903 : List ℕ := [t454,t455,t464,t457,t491]
theorem b2022 : Ban 60 5 v1903 := viaSmall (by decide +kernel) (by decide)
def v1904 : List ℕ := [t454,t455,t464,t456,t457,t491]
theorem b2023 : Ban 60 5 v1904 := viaSmall (by decide +kernel) (by decide)
def v1905 : List ℕ := [t30,t454,t455,t456,t457,t491]
theorem b2024 : Ban 60 5 v1905 := viaSmall (by decide +kernel) (by decide)
def v1906 : List ℕ := [t454,t455,t456,t465,t491]
theorem b2025 : Ban 60 5 v1906 := viaSmall (by decide +kernel) (by decide)
def v1907 : List ℕ := [t454,t455,t456,t457,t465,t491]
theorem b2026 : Ban 60 5 v1907 := viaSmall (by decide +kernel) (by decide)
def v1908 : List ℕ := [t466,t454,t455,t456,t457,t491]
theorem b2027 : Ban 60 5 v1908 := viaSmall (by decide +kernel) (by decide)
def v1909 : List ℕ := [t454,t455,t456,t467,t491]
theorem b2028 : Ban 60 5 v1909 := viaSmall (by decide +kernel) (by decide)
def v1910 : List ℕ := [t454,t455,t456,t467,t457,t491]
theorem b2029 : Ban 60 5 v1910 := viaSmall (by decide +kernel) (by decide)
def v1911 : List ℕ := [t76,t454,t455,t456,t457,t491]
theorem b2030 : Ban 60 5 v1911 := viaSmall (by decide +kernel) (by decide)
def t492 : ℕ := 0xfb3ecfb3ecfb3ecffffffffffffc00
def v1912 : List ℕ := [t454,t455,t456,t457,t491,t492]
theorem b2031 : Ban 60 5 v1912 := viaSmall (by decide +kernel) (by decide)
def t493 : ℕ := 0x300c0300c0300c0000000000ffc00
def v1913 : List ℕ := [t493,t454,t455,t456,t457,t491]
theorem b2032 : Ban 60 5 v1913 := viaSmall (by decide +kernel) (by decide)
def t494 : ℕ := 0xf83e0f83e0f83e0ffc00003ff00000
def v1914 : List ℕ := [t454,t455,t456,t457,t494,t491]
theorem b2033 : Ban 60 5 v1914 := viaSmall (by decide +kernel) (by decide)
def v1915 : List ℕ := [t64,t454,t455,t456,t457,t491]
theorem b2034 : Ban 60 5 v1915 := viaSmall (by decide +kernel) (by decide)
def v1916 : List ℕ := [t454,t455,t456,t472,t457,t491]
theorem b2035 : Ban 60 5 v1916 := viaSmall (by decide +kernel) (by decide)
def v1917 : List ℕ := [t454,t473,t455,t456,t457,t491]
theorem b2036 : Ban 60 5 v1917 := viaSmall (by decide +kernel) (by decide)
def v1918 : List ℕ := [t454,t455,t474,t456,t457,t491]
theorem b2037 : Ban 60 5 v1918 := viaSmall (by decide +kernel) (by decide)
def v1919 : List ℕ := [t454,t475,t455,t456,t457,t491]
theorem b2038 : Ban 60 5 v1919 := viaSmall (by decide +kernel) (by decide)
def v1920 : List ℕ := [t454,t456,t457,t476,t491]
theorem b2039 : Ban 60 5 v1920 := viaSmall (by decide +kernel) (by decide)
def v1921 : List ℕ := [t454,t455,t456,t457,t476,t491]
theorem b2040 : Ban 60 5 v1921 := viaSmall (by decide +kernel) (by decide)
def v1922 : List ℕ := [t454,t477,t456,t457,t491]
theorem b2041 : Ban 60 5 v1922 := viaSmall (by decide +kernel) (by decide)
def v1923 : List ℕ := [t454,t477,t455,t456,t457,t491]
theorem b2042 : Ban 60 5 v1923 := viaSmall (by decide +kernel) (by decide)
def v1924 : List ℕ := [t454,t455,t456,t478,t457,t491]
theorem b2043 : Ban 60 5 v1924 := viaSmall (by decide +kernel) (by decide)
def t495 : ℕ := 0x100401004010040ffc000000000000
def v1925 : List ℕ := [t454,t495,t455,t456,t457,t491]
theorem b2044 : Ban 60 5 v1925 := viaSmall (by decide +kernel) (by decide)
def v1926 : List ℕ := [t454,t455,t456,t457,t491,t360]
theorem b2045 : Ban 60 5 v1926 := viaSmall (by decide +kernel) (by decide)
def t496 : ℕ := 0x401004010040100000000000fffff
def v1927 : List ℕ := [t454,t496,t455,t456,t457,t491]
theorem b2046 : Ban 60 5 v1927 := viaSmall (by decide +kernel) (by decide)
def t497 : ℕ := 0xe83a0e83a0e83a0003fffffff00000
def v1928 : List ℕ := [t454,t455,t456,t457,t497,t491]
theorem b2047 : Ban 60 5 v1928 := viaSmall (by decide +kernel) (by decide)
def v1929 : List ℕ := [t35,t454,t455,t456,t457,t491]
theorem b2048 : Ban 60 5 v1929 := viaSmall (by decide +kernel) (by decide)
def v1930 : List ℕ := [t454,t455,t456,t457,t483,t491]
theorem b2049 : Ban 60 5 v1930 := viaSmall (by decide +kernel) (by decide)
def v1931 : List ℕ := [t454,t455,t484,t456,t457,t491]
theorem b2050 : Ban 60 5 v1931 := viaSmall (by decide +kernel) (by decide)
def v1932 : List ℕ := [t454,t455,t456,t485,t457,t491]
theorem b2051 : Ban 60 5 v1932 := viaSmall (by decide +kernel) (by decide)
def t498 : ℕ := 0x40100401004010000000003ff00000
def v1933 : List ℕ := [t454,t455,t498,t456,t457,t491]
theorem b2052 : Ban 60 5 v1933 := viaSmall (by decide +kernel) (by decide)
def v1934 : List ℕ := [t454,t455,t456,t457,t491,t488]
theorem b2053 : Ban 60 5 v1934 := viaSmall (by decide +kernel) (by decide)
def t499 : ℕ := 0x280a0280a0280a0000000000003ff
def v1935 : List ℕ := [t499,t454,t455,t456,t457,t491]
theorem b2054 : Ban 60 5 v1935 := viaSmall (by decide +kernel) (by decide)
def t500 : ℕ := 0xb82e0b82e0b82e0fffffffc0000000
def v1936 : List ℕ := [t454,t455,t456,t457,t500]
theorem b2055 : Ban 60 5 v1936 := viaSmall (by decide +kernel) (by decide)
def v1937 : List ℕ := [t454,t455,t456,t457,t500,t491]
theorem b2056 : Ban 60 5 v1937 := viaSmall (by decide +kernel) (by decide)
def t501 : ℕ := 0x601806018060180fffff0000000000
def v1938 : List ℕ := [t454,t455,t456,t501,t457]
theorem b2057 : Ban 60 5 v1938 := viaSmall (by decide +kernel) (by decide)
def v1939 : List ℕ := [t454,t455,t456,t501,t491]
theorem b2058 : Ban 60 5 v1939 := viaSmall (by decide +kernel) (by decide)
def v1940 : List ℕ := [t454,t455,t456,t501,t457,t491]
theorem b2059 : Ban 60 5 v1940 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b2060 : Ban 60 6 v1892 := viaBranch (ws := [v1893,v1894,v1895,v1896,v1897,v1898,v1899,v1900,v1901,v1902,v1903,v1904,v1905,v1906,v1907,v1908,v1909,v1910,v1911,v1912,v1913,v1914,v1915,v1916,v1917,v1918,v1919,v1920,v1921,v1922,v1923,v1924,v1925,v1926,v1927,v1928,v1929,v1930,v1931,v1932,v1933,v1879,v1934,v1935,v1936,v1937,v1938,v1939,v1940]) (consBan b2012 (consBan b2013 (consBan b2014 (consBan b2015 (consBan b2016 (consBan b2017 (consBan b2018 (consBan b2019 (consBan b2020 (consBan b2021 (consBan b2022 (consBan b2023 (consBan b2024 (consBan b2025 (consBan b2026 (consBan b2027 (consBan b2028 (consBan b2029 (consBan b2030 (consBan b2031 (consBan b2032 (consBan b2033 (consBan b2034 (consBan b2035 (consBan b2036 (consBan b2037 (consBan b2038 (consBan b2039 (consBan b2040 (consBan b2041 (consBan b2042 (consBan b2043 (consBan b2044 (consBan b2045 (consBan b2046 (consBan b2047 (consBan b2048 (consBan b2049 (consBan b2050 (consBan b2051 (consBan b2052 (consBan b1998 (consBan b2053 (consBan b2054 (consBan b2055 (consBan b2056 (consBan b2057 (consBan b2058 (consBan b2059 (nilBan 60 5)))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w57 : Wide 60 6 v1892 := viaSub (ws := [v1892]) (consBan b2060 (nilBan 60 6)) (by decide) (by decide +kernel)
theorem b2061 : Ban 220 8 v1891 := viaCut p127_115 w57 (by decide) (by decide +kernel) (by decide +kernel)
def v1941 : List ℕ := [t0,t1,t2,t3,t4,t6,t250]
theorem b2062 : Ban 220 8 v1941 := viaCut p127_61 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v1942 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t250]
theorem b2063 : Ban 220 8 v1942 := viaCut p127_61 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v1943 : List ℕ := [t0,t1,t2,t3,t251,t4,t6]
theorem b2064 : Ban 220 8 v1943 := viaCut p127_61 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v1944 : List ℕ := [t0,t1,t2,t3,t251,t4,t5,t6]
theorem b2065 : Ban 220 8 v1944 := viaCut p127_82 w34 (by decide) (by decide +kernel) (by decide +kernel)
def v1945 : List ℕ := [t0,t1,t2,t3,t4,t238,t5]
theorem b2066 : Ban 220 8 v1945 := viaCut p127_61 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v1946 : List ℕ := [t0,t1,t2,t3,t4,t238,t5,t6]
theorem b2067 : Ban 220 8 v1946 := viaCut p127_41 w5 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b2068 : Ban 220 9 v0 := viaBranch (ws := [v1,v3,v54,v105,v107,v171,v172,v173,v174,v175,v176,v415,v215,v416,v417,v418,v419,v420,v421,v422,v423,v424,v425,v475,v476,v477,v478,v479,v480,v481,v482,v483,v484,v485,v486,v487,v488,v489,v540,v589,v590,v649,v650,v709,v710,v711,v775,v825,v883,v940,v941,v997,v998,v999,v1000,v1001,v1002,v1003,v1004,v1005,v1006,v1007,v1008,v1009,v1010,v1011,v1012,v1013,v1014,v1015,v1063,v1064,v1065,v1118,v1119,v1173,v1174,v1175,v1220,v1268,v1269,v1473,v1474,v1592,v1593,v1594,v1595,v1596,v1597,v1598,v1669,v1670,v1671,v1672,v1722,v1723,v1724,v1774,v1775,v1823,v1824,v1825,v1826,v1827,v1828,v1829,v1830,v1831,v1832,v1833,v1884,v1885,v1886,v1887,v1888,v1889,v1890,v1891,v1941,v1942,v1943,v1944,v1945,v1946]) (consBan b1 (consBan b52 (consBan b103 (consBan b105 (consBan b169 (consBan b171 (consBan b172 (consBan b173 (consBan b174 (consBan b175 (consBan b417 (consBan b418 (consBan b419 (consBan b420 (consBan b421 (consBan b422 (consBan b423 (consBan b424 (consBan b425 (consBan b426 (consBan b427 (consBan b428 (consBan b478 (consBan b479 (consBan b480 (consBan b481 (consBan b482 (consBan b483 (consBan b484 (consBan b485 (consBan b486 (consBan b487 (consBan b488 (consBan b489 (consBan b490 (consBan b491 (consBan b492 (consBan b544 (consBan b594 (consBan b595 (consBan b654 (consBan b655 (consBan b714 (consBan b715 (consBan b716 (consBan b780 (consBan b830 (consBan b890 (consBan b948 (consBan b949 (consBan b1006 (consBan b1007 (consBan b1008 (consBan b1009 (consBan b1010 (consBan b1011 (consBan b1012 (consBan b1013 (consBan b1014 (consBan b1015 (consBan b1016 (consBan b1017 (consBan b1018 (consBan b1019 (consBan b1020 (consBan b1021 (consBan b1022 (consBan b1023 (consBan b1024 (consBan b1073 (consBan b1124 (consBan b1125 (consBan b1179 (consBan b1180 (consBan b1235 (consBan b1236 (consBan b1237 (consBan b1283 (consBan b1332 (consBan b1333 (consBan b1538 (consBan b1539 (consBan b1658 (consBan b1659 (consBan b1660 (consBan b1661 (consBan b1662 (consBan b1663 (consBan b1664 (consBan b1736 (consBan b1737 (consBan b1738 (consBan b1739 (consBan b1790 (consBan b1841 (consBan b1842 (consBan b1893 (consBan b1894 (consBan b1943 (consBan b1944 (consBan b1945 (consBan b1946 (consBan b1947 (consBan b1948 (consBan b1949 (consBan b1950 (consBan b1951 (consBan b1952 (consBan b1953 (consBan b2004 (consBan b2005 (consBan b2006 (consBan b2007 (consBan b2008 (consBan b2009 (consBan b2010 (consBan b2011 (consBan b2061 (consBan b2062 (consBan b2063 (consBan b2064 (consBan b2065 (consBan b2066 (consBan b2067 (nilBan 220 8))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem cap10 : Ban 220 9 v0 := b2068
end PEqualNP.Outside.L_meta_11841.Cert

namespace PEqualNP.Outside.L_meta_11841.Complete
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_11841.Ground

def posBits : ℕ := 0xa142850a142850a142850a142850a1428509122448912244891224489122448912244889122448912244891224489122448912244850a142850a142850a142850a142850a14250a142850a142850a142850a142850a14284489122448912244891224489122448912242850a142850a142850a142850a142850a12850a142850a142850a142850a142850a14244891224489122448912244891224489122244891224489122448912244891224489112244891224489122448912244891224489
def negBits : ℕ := 0xc1060304880c101c305080e182840608080c1060304880c101c305080e182840608080c1060304880c101c305080e182840608080c1060304880c101c305080e182840608080c1060304880c101c305080e182840608080c1060304880c101c305080e182840608080c1060304880c101c305080e182840608080c1060304880c101c305080e182840608080c1060304880c101c305080e182840608080c1060304880c101c305080e182840608080c1060304880c101c305080e182840608080
def sample (bank : ℕ) (i : Fin 220) (j : Fin 7) := bank.testBit (7*i.val+j.val)
def inputs : List ℕ := [0x400aa400aa400aa400aa400aa400aa400aa400aa400aa400aa400aa000000000000000000000000000000fffff0000000000ffffffffff,0xacc00acc00acc00acc00acc00acc00acc00acc00acc00acc00acc000000000000000fffff00000fffff0000000000fffff0000000000,0x8cf008cf008cf008cf008cf008cf008cf008cf008cf008cf008cf00000000000fffff00000000000000000000fffff000000000000000,0x2f0002f0002f0002f0002f0002f0002f0002f0002f0002f0002f0000000fffff0000000000fffff0000000000000000000000000fffff,0x1300013000130001300013000130001300013000130001300013000fffff000000000000000000000000000000fffffffffffffff00000,0x9c0009c0009c0009c0009c0009c0009c0009c0009c0009c0009c00000000000000000000000fffffffffffffff00000000000000000000,0xe0000e0000e0000e0000e0000e0000e0000e0000e0000e0000e0000ffffffffffffffffffff00000000000000000000000000000000000]

def seeds : List Wire := inputs.map (fun a => (false,a))
set_option maxHeartbeats 10000000 in
theorem listed : ∀ i : Fin 220, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (220+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 220, Frame.target (sample posBits i)=true ∧ Frame.target (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 220, ∀ b∈inputs, b.testBit i.val≠b.testBit (220+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 220 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 7 C=Frame.target) :
    ∃ k≤C.gates.countP counted, Live 220 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 7 → Bool) : C.eval (List.ofFn x)=Frame.target x := congrFun eq x
  have good : Good 220 out.2 := by
    intro i hi same
    let j : Fin 220 := ⟨i,hi⟩
    have diff : read i out=read (220+i) out := by
      change (out.1 != out.2.testBit i) = (out.1 != out.2.testBit (220+i))
      rw [same]
    have p := ev i;have n := ev (220+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩

theorem signed_floor (gs : List Gate) (o : ℕ) (fan : FanInTwo ⟨gs,o⟩)
    (correct : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Frame.target x)
    (hasNot : ∃ g ∈ gs, g.op = .not) : 11 ≤ gs.length := by
  obtain ⟨k,hk,live⟩ := trace ⟨gs,o⟩ fan (funext correct)
  have same : inputs.toFinset = Cert.v0.toFinset := by decide +kernel
  rw [same] at live
  have lo : 10 ≤ k := by
    by_contra! small
    exact Cert.cap10 k (by omega) live
  have less : gs.countP counted < gs.length := by
    apply Nat.lt_of_le_of_ne List.countP_le_length
    intro eq
    obtain ⟨g,hg,hop⟩ := hasNot
    have bad := List.countP_eq_length.mp eq g hg
    simp [counted,hop] at bad
  change k ≤ gs.countP counted at hk
  omega

end PEqualNP.Outside.L_meta_11841.Complete
theorem PEqualNP.Outside.L_meta_11841 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_11841.Frame.finish PEqualNP.Outside.L_meta_11841.Complete.signed_floor
