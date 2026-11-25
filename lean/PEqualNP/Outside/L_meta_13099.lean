import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13099.Support

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

def t0 := 0x10250930ff
def t1 := 0x124c9236cc93
def t2 := 0x470518c70f1c
def t3 := 0xb80ac0f80fe0
def t4 := 0xeda000fff000
def v0 := [t0,t1,t2,t3,t4]
def t5 := 0x93
def v1 := [t5,t0,t1,t2,t3,t4]
def t6 := 0x800e0
def v2 := [t6,t0,t1,t2,t3,t4]
def t7 := 0x14f
def t8 := 0x4b3
def t9 := 0xa3c
def v3 := [t7,t8,t9]
def p31_19 : Projection 24 6 := pick [0,1,12,13,14,15] rfl (by decide +kernel) (by decide)
def map31_3 : Projection 24 24 := pick [2,3,12,13,16,0,1,4,15,14,18,17,5,6,8,9,19,22,23,7,10,11,21,20] rfl (by decide +kernel) (by decide)
def map31_4 : Projection 24 24 := pick [5,6,0,1,7,12,13,19,14,15,20,21,2,3,9,8,4,11,10,16,23,22,17,18] rfl (by decide +kernel) (by decide)
def t10 := 0x125cb73ffcff
def v4 := [t0,t1,t10,t2,t3,t4]
def t11 := 0x47153dcf3fff
def v5 := [t0,t1,t2,t11,t3,t4]
def t12 := 0x1001c
def v6 := [t12,t1,t11,t3,t4]
def v7 := [t12,t0,t1,t11,t3,t4]
def v8 := [t12,t1,t2,t11,t3,t4]
def t13 := 0x10250830e3
def v9 := [t13,t0,t1,t11,t3,t4]
def t14 := 0x470518c60f00
def v10 := [t1,t14,t2,t11,t3,t4]
def v11 := [t0,t1,t14,t2,t3,t4]
def t15 := 0xb81ae5f93fff
def v12 := [t1,t2,t11,t3,t15,t4]
def t16 := 0x102501301f
def v13 := [t16,t1,t2,t11,t3,t4]
def t17 := 0x574d9af7cf9f
def v14 := [t0,t1,t11,t17,t3,t4]
def t18 := 0x450108c1030c
def v15 := [t0,t1,t18,t11,t3,t4]
def t19 := 0x20410060c93
def v16 := [t0,t19,t1,t2,t3,t4]
def t20 := 0x575dbfffffff
def v17 := [t0,t1,t2,t20,t3,t4]
def t21 := 0x10488230c000
def v18 := [t0,t21,t1,t2,t3,t4]
def t22 := 0x45112dc9336c
def v19 := [t0,t1,t22,t2,t3,t4]
def v20 := [t13,t0,t1,t2,t3,t4]
def t23 := 0xff0fd8ff0ffc
def v21 := [t0,t1,t11,t3,t4,t23]
def t24 := 0x47051807001c
def v22 := [t0,t1,t24,t11,t3,t4]
def t25 := 0xefa518ffff1c
def v23 := [t0,t1,t11,t3,t4,t25]
def t26 := 0x20518000f1c
def v24 := [t0,t26,t1,t11,t3,t4]
def t27 := 0xc80fe0
def v25 := [t27,t0,t1,t2,t4]
def v26 := [t27,t0,t1,t2,t11,t4]
def v27 := [t27,t0,t1,t2,t3,t4]
def t28 := 0xff1ffdff3fff
def v28 := [t0,t1,t2,t3,t4,t28]
def t29 := 0x47153d07301f
def v29 := [t0,t1,t2,t29,t4]
def v30 := [t0,t1,t2,t29,t11,t4]
def v31 := [t0,t1,t2,t29,t3,t4]
def t30 := 0xb80ac0300000
def v32 := [t0,t1,t2,t30,t3,t4]
def t31 := 0x450000cf3000
def v33 := [t0,t1,t31,t2,t3,t4]
def t32 := 0xefb53dffffff
def v34 := [t0,t1,t2,t3,t4,t32]
def t33 := 0x2153d000fff
def v35 := [t0,t33,t1,t2,t3,t4]
def t34 := 0xa8a00030c000
def v36 := [t0,t1,t2,t34,t3,t4]
def map31_2 : Projection 24 24 := pick [2,3,0,1,4,12,13,16,14,15,17,18,5,6,8,9,7,10,11,19,22,23,20,21] rfl (by decide +kernel) (by decide)
def t35 := 0x102509306c
def v37 := [t35,t0,t1,t2,t3,t4]
def t36 := 0x10250000ff
def v38 := [t36,t0,t1,t2,t3,t4]
def t37 := 0x93000
def v39 := [t37,t36,t1,t2,t3,t4]
def v40 := [t37,t0,t1,t2,t3,t4]
def t38 := 0x125cb736ccff
def v41 := [t0,t1,t38,t2,t3,t4]
def t39 := 0x102500006c
def v42 := [t39,t0,t1,t2,t3,t4]
def t40 := 0x124c9236cc00
def v43 := [t0,t40,t1,t2,t3,t4]
def t41 := 0x1c
def v44 := [t41,t0,t1,t2,t3,t4]
def t42 := 0x47153dc70fff
def v45 := [t0,t1,t2,t42,t3,t4]
def t43 := 0x10250000e3
def v46 := [t43,t0,t1,t2,t3,t4]
def t44 := 0x470518c70f00
def v47 := [t0,t1,t44,t2,t3,t4]
def t45 := 0xe0
def v48 := [t45,t0,t1,t2,t3,t4]
def t46 := 0xb81ae5f80fff
def v49 := [t0,t1,t2,t3,t46,t4]
def t47 := 0x102500001f
def v50 := [t47,t0,t1,t2,t3,t4]
def t48 := 0xb80ac0f80f00
def v51 := [t0,t1,t2,t48,t3,t4]
def t49 := 0xedb025fff0ff
def v52 := [t36,t0,t1,t2,t3,t49]
def v53 := [t0,t1,t2,t3,t4,t49]
def v54 := [t36,t1,t10,t2,t3,t4]
def v55 := [t36,t35,t1,t2,t3,t4]
def t50 := 0xeda000f6c000
def v56 := [t36,t1,t2,t3,t50]
def v57 := [t36,t0,t1,t2,t3,t50]
def v58 := [t36,t1,t2,t3,t50,t4]
def t51 := 0x36c000
def v59 := [t51,t36,t0,t1,t2,t3]
def t52 := 0x124c92000c93
def v60 := [t36,t0,t52,t1,t2,t3]
def map31_6 : Projection 24 24 := pick [12,13,2,3,16,5,6,19,8,9,22,23,0,1,15,14,4,18,17,7,21,20,10,11] rfl (by decide +kernel) (by decide)
def p31_13 : Projection 24 6 := pick [2,3,5,6,8,9] rfl (by decide +kernel) (by decide)
def v61 := [t12,t0,t1,t2,t3,t4]
def map31_1 : Projection 24 24 := pick [0,1,5,6,7,2,3,4,9,8,11,10,12,13,14,15,19,20,21,16,17,18,23,22] rfl (by decide +kernel) (by decide)
def v62 := [t0,t1,t2,t3,t15,t4]
def v63 := [t16,t0,t1,t2,t3,t4]
def t53 := 0xb80ac0f00f00
def v64 := [t0,t1,t2,t53,t3,t4]
def v65 := [t0,t1,t2,t3,t50,t4]
def t54 := 0x20410060c10
def v66 := [t0,t54,t1,t2,t3,t4]
def v67 := [t0,t1,t2,t17,t3,t4]
def v68 := [t0,t10,t2,t17,t3,t4]
def v69 := [t0,t40,t2,t17,t3,t4]
def v70 := [t0,t1,t14,t17,t3,t4]
def t55 := 0x1009f
def v71 := [t55,t0,t1,t2,t3,t4]
def t56 := 0x1025083060
def v72 := [t56,t0,t1,t2,t3,t4]
def t57 := 0x574d9af6cf00
def v73 := [t0,t1,t2,t57,t3,t4]
def v74 := [t0,t54,t17,t3,t4]
def v75 := [t0,t54,t1,t17,t3,t4]
def v76 := [t0,t54,t2,t17,t3,t4]
def t58 := 0x10488230c083
def v77 := [t0,t58,t1,t17,t3,t4]
def v78 := [t0,t18,t2,t17,t3,t4]
def v79 := [t0,t1,t18,t2,t3,t4]
def t59 := 0xba4ed2fecff3
def v80 := [t0,t2,t17,t3,t59,t4]
def t60 := 0x2441206c013
def v81 := [t0,t60,t2,t17,t3,t4]
def v82 := [t51,t0,t2,t17,t3,t4]
def t61 := 0xeda000c93000
def v83 := [t0,t2,t17,t3,t61,t4]
def v84 := [t0,t58,t1,t2,t3,t4]
def t62 := 0xc00f00
def v85 := [t62,t0,t1,t17,t3,t4]
def t63 := 0xb80ac03800e0
def v86 := [t0,t1,t17,t63,t3,t4]
def v87 := [t0,t1,t17,t3,t4,t25]
def v88 := [t0,t26,t1,t17,t3,t4]
def t64 := 0x100880f00f80
def v89 := [t0,t64,t1,t2,t3,t4]
def t65 := 0xff4fdaffcfff
def v90 := [t0,t1,t2,t3,t4,t65]
def t66 := 0x47451a07c01f
def v91 := [t0,t1,t2,t66,t3,t4]
def t67 := 0xa80240080060
def v92 := [t0,t1,t2,t67,t3,t4]
def t68 := 0x450000f7c000
def v93 := [t0,t1,t68,t2,t3,t4]
def t69 := 0xffed9affff9f
def v94 := [t0,t1,t2,t3,t4,t69]
def t70 := 0x124d9a000f9f
def v95 := [t0,t1,t70,t2,t3,t4]
def t71 := 0xa8a000083000
def v96 := [t0,t1,t2,t71,t3,t4]
def v97 := [t0,t60,t1,t2,t3,t4]
def t72 := 0x100880300c80
def v98 := [t0,t72,t1,t2,t3,t4]
def v99 := [t0,t1,t2,t3,t59,t4]
def t73 := 0xa80240c80360
def v100 := [t0,t1,t2,t73,t3,t4]
def map31_5 : Projection 24 24 := pick [5,6,12,13,19,0,1,7,15,14,21,20,2,3,9,8,16,23,22,4,11,10,18,17] rfl (by decide +kernel) (by decide)
def v101 := [t51,t0,t1,t2,t3,t4]
def t74 := 0xffec92fffc93
def v102 := [t0,t1,t2,t3,t4,t74]
def v103 := [t0,t1,t2,t3,t4,t23]
def v104 := [t0,t52,t1,t2,t3,t4]
def v105 := [t0,t1,t2,t3,t61,t4]
def v106 := [t62,t0,t1,t2,t3,t4]
def v107 := [t0,t1,t24,t2,t3,t4]
def v108 := [t0,t1,t2,t63,t3,t4]
def t75 := 0x450000c70000
def v109 := [t0,t1,t75,t2,t3,t4]
def v110 := [t0,t1,t2,t3,t4,t25]
def v111 := [t0,t26,t1,t2,t3,t4]
def t76 := 0xa8a00038f000
def v112 := [t0,t1,t2,t76,t3,t4]
def t77 := 0xa80000f80000
def v113 := [t0,t1,t2,t77,t3,t4]
def t78 := 0xfdaac0ffffe0
def v114 := [t0,t1,t2,t3,t4,t78]
def t79 := 0x100ac0000fe0
def v115 := [t0,t79,t1,t2,t3,t4]
def t80 := 0x45a00007f000
def v116 := [t0,t1,t80,t2,t3,t4]
theorem b0 : Ban 6 3 v3 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w0 : Wide 6 3 v3 := viaSub (ws := [v3]) (consBan b0 (nilBan 6 3)) (by decide) (by decide +kernel)
theorem b2 : Ban 24 6 v1 := smallByCut p31_13 w0
theorem b3 : Ban 24 5 v6 := smallByCut p31_19 w0
theorem b4 : Ban 24 5 v7 := smallByCut p31_19 w0
theorem b5 : Ban 24 5 v8 := smallByCut p31_19 w0
theorem b6 : Ban 24 5 v9 := checkedSmall
theorem b7 : Ban 24 5 v10 := smallByCut p31_19 w0
theorem b8 : Ban 24 5 v11 := smallByCut p31_19 w0
theorem b9 : Ban 24 5 v12 := smallByCut p31_19 w0
theorem b10 : Ban 24 5 v13 := smallByCut p31_19 w0
theorem b11 : Ban 24 5 v14 := checkedSmall
theorem b12 : Ban 24 5 v15 := smallByCut p31_19 w0
theorem b13 : Ban 24 5 v16 := smallByCut p31_13 w0
theorem b14 : Ban 24 5 v17 := checkedSmall
theorem b15 : Ban 24 5 v18 := smallByCut p31_13 w0
theorem b16 : Ban 24 5 v19 := checkedSmall
theorem b17 : Ban 24 5 v20 := smallByCut p31_19 w0
theorem b18 : Ban 24 5 v21 := smallByCut p31_19 w0
theorem b19 : Ban 24 5 v22 := smallByCut p31_19 w0
theorem b20 : Ban 24 5 v23 := checkedSmall
theorem b21 : Ban 24 5 v24 := smallByCut p31_19 w0
theorem b22 : Ban 24 5 v25 := smallByCut p31_19 w0
theorem b23 : Ban 24 5 v26 := smallByCut p31_19 w0
theorem b24 : Ban 24 5 v27 := smallByCut p31_19 w0
theorem b25 : Ban 24 5 v28 := smallByCut p31_19 w0
theorem b26 : Ban 24 5 v29 := checkedSmall
theorem b27 : Ban 24 5 v30 := checkedSmall
theorem b28 : Ban 24 5 v31 := smallByCut p31_19 w0
theorem b29 : Ban 24 5 v32 := smallByCut p31_19 w0
theorem b30 : Ban 24 5 v33 := smallByCut p31_13 w0
theorem b31 : Ban 24 5 v34 := checkedSmall
theorem b32 : Ban 24 5 v35 := checkedSmall
theorem b33 : Ban 24 5 v36 := smallByCut p31_13 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b34 : Ban 24 6 v5 := viaBranch (ws := [v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36]) (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b10 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (consBan b19 (consBan b20 (consBan b21 (consBan b22 (consBan b23 (consBan b24 (consBan b25 (consBan b26 (consBan b27 (consBan b28 (consBan b29 (consBan b30 (consBan b31 (consBan b32 (consBan b33 (nilBan 24 5)))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b35 : Ban 24 6 v4 := viaPerm map31_2 map31_2 b34 (by decide +kernel) (by decide +kernel)
theorem b36 : Ban 24 5 v39 := smallByCut p31_13 w0
theorem b37 : Ban 24 5 v40 := smallByCut p31_13 w0
theorem b38 : Ban 24 5 v1 := smallByCut p31_13 w0
theorem b39 : Ban 24 5 v41 := smallByCut p31_13 w0
theorem b40 : Ban 24 5 v42 := smallByCut p31_13 w0
theorem b41 : Ban 24 5 v43 := smallByCut p31_13 w0
theorem b42 : Ban 24 5 v44 := smallByCut p31_19 w0
theorem b43 : Ban 24 5 v45 := checkedSmall
theorem b44 : Ban 24 5 v46 := checkedSmall
theorem b45 : Ban 24 5 v47 := smallByCut p31_19 w0
theorem b46 : Ban 24 5 v48 := smallByCut p31_19 w0
theorem b47 : Ban 24 5 v49 := checkedSmall
theorem b48 : Ban 24 5 v50 := checkedSmall
theorem b49 : Ban 24 5 v51 := smallByCut p31_19 w0
theorem b50 : Ban 24 5 v52 := checkedSmall
theorem b51 : Ban 24 5 v53 := smallByCut p31_13 w0
theorem b52 : Ban 24 5 v54 := smallByCut p31_13 w0
theorem b53 : Ban 24 5 v55 := smallByCut p31_13 w0
theorem b54 : Ban 24 5 v56 := smallByCut p31_13 w0
theorem b55 : Ban 24 5 v57 := smallByCut p31_13 w0
theorem b56 : Ban 24 5 v58 := smallByCut p31_13 w0
theorem b57 : Ban 24 5 v59 := smallByCut p31_13 w0
theorem b58 : Ban 24 5 v60 := smallByCut p31_13 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b59 : Ban 24 6 v38 := viaBranch (ws := [v39,v40,v1,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60]) (consBan b36 (consBan b37 (consBan b38 (consBan b39 (consBan b40 (consBan b41 (consBan b42 (consBan b43 (consBan b44 (consBan b45 (consBan b46 (consBan b47 (consBan b48 (consBan b49 (consBan b50 (consBan b51 (consBan b52 (consBan b53 (consBan b54 (consBan b55 (consBan b56 (consBan b57 (consBan b58 (nilBan 24 5)))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b60 : Ban 24 6 v37 := viaPerm map31_6 map31_6 b59 (by decide +kernel) (by decide +kernel)
theorem b61 : Ban 24 6 v43 := smallByCut p31_13 w0
theorem b62 : Ban 24 6 v61 := smallByCut p31_19 w0
theorem b63 : Ban 24 6 v20 := viaPerm map31_4 map31_3 b59 (by decide +kernel) (by decide +kernel)
theorem b64 : Ban 24 6 v11 := smallByCut p31_19 w0
theorem b1 : Ban 24 6 v2 := smallByCut p31_19 w0
theorem b65 : Ban 24 6 v62 := viaPerm map31_1 map31_1 b34 (by decide +kernel) (by decide +kernel)
theorem b66 : Ban 24 6 v63 := viaPerm map31_2 map31_2 b59 (by decide +kernel) (by decide +kernel)
theorem b67 : Ban 24 6 v64 := smallByCut p31_19 w0
theorem b68 : Ban 24 6 v40 := smallByCut p31_13 w0
theorem b69 : Ban 24 6 v53 := viaPerm map31_3 map31_4 b34 (by decide +kernel) (by decide +kernel)
theorem b70 : Ban 24 6 v65 := smallByCut p31_13 w0
theorem b71 : Ban 24 6 v66 := smallByCut p31_13 w0
theorem b72 : Ban 24 5 v68 := checkedSmall
theorem b73 : Ban 24 5 v69 := smallByCut p31_13 w0
theorem b74 : Ban 24 5 v70 := smallByCut p31_19 w0
theorem b75 : Ban 24 5 v71 := checkedSmall
theorem b76 : Ban 24 5 v72 := checkedSmall
theorem b77 : Ban 24 5 v73 := checkedSmall
theorem b78 : Ban 24 5 v74 := smallByCut p31_13 w0
theorem b79 : Ban 24 5 v75 := smallByCut p31_13 w0
theorem b80 : Ban 24 5 v76 := smallByCut p31_13 w0
theorem b81 : Ban 24 5 v77 := smallByCut p31_13 w0
theorem b82 : Ban 24 5 v78 := smallByCut p31_19 w0
theorem b83 : Ban 24 5 v79 := smallByCut p31_13 w0
theorem b84 : Ban 24 5 v80 := smallByCut p31_19 w0
theorem b85 : Ban 24 5 v81 := smallByCut p31_13 w0
theorem b86 : Ban 24 5 v82 := smallByCut p31_13 w0
theorem b87 : Ban 24 5 v83 := smallByCut p31_13 w0
theorem b88 : Ban 24 5 v84 := smallByCut p31_13 w0
theorem b89 : Ban 24 5 v85 := smallByCut p31_19 w0
theorem b90 : Ban 24 5 v86 := smallByCut p31_19 w0
theorem b91 : Ban 24 5 v87 := smallByCut p31_13 w0
theorem b92 : Ban 24 5 v88 := smallByCut p31_13 w0
theorem b93 : Ban 24 5 v89 := smallByCut p31_19 w0
theorem b94 : Ban 24 5 v90 := smallByCut p31_19 w0
theorem b95 : Ban 24 5 v91 := smallByCut p31_19 w0
theorem b96 : Ban 24 5 v92 := smallByCut p31_19 w0
theorem b97 : Ban 24 5 v93 := smallByCut p31_13 w0
theorem b98 : Ban 24 5 v94 := smallByCut p31_13 w0
theorem b99 : Ban 24 5 v95 := smallByCut p31_13 w0
theorem b100 : Ban 24 5 v96 := smallByCut p31_13 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b101 : Ban 24 6 v67 := viaBranch (ws := [v68,v69,v14,v70,v71,v17,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96]) (consBan b72 (consBan b73 (consBan b11 (consBan b74 (consBan b75 (consBan b14 (consBan b76 (consBan b77 (consBan b78 (consBan b79 (consBan b80 (consBan b81 (consBan b82 (consBan b83 (consBan b84 (consBan b85 (consBan b86 (consBan b87 (consBan b88 (consBan b89 (consBan b90 (consBan b91 (consBan b92 (consBan b93 (consBan b94 (consBan b95 (consBan b96 (consBan b97 (consBan b98 (consBan b99 (consBan b100 (nilBan 24 5)))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b103 : Ban 24 6 v84 := smallByCut p31_13 w0
theorem b104 : Ban 24 6 v79 := smallByCut p31_19 w0
theorem b105 : Ban 24 6 v98 := smallByCut p31_13 w0
theorem b106 : Ban 24 6 v99 := viaPerm map31_1 map31_1 b101 (by decide +kernel) (by decide +kernel)
theorem b102 : Ban 24 6 v97 := smallByCut p31_13 w0
theorem b107 : Ban 24 6 v100 := smallByCut p31_19 w0
theorem b108 : Ban 24 6 v101 := smallByCut p31_13 w0
theorem b110 : Ban 24 6 v102 := smallByCut p31_13 w0
theorem b111 : Ban 24 6 v104 := smallByCut p31_13 w0
theorem b112 : Ban 24 6 v105 := smallByCut p31_13 w0
theorem b113 : Ban 24 6 v106 := smallByCut p31_19 w0
theorem b109 : Ban 24 6 v103 := smallByCut p31_19 w0
theorem b114 : Ban 24 6 v107 := smallByCut p31_19 w0
theorem b115 : Ban 24 6 v108 := smallByCut p31_19 w0
theorem b116 : Ban 24 6 v109 := smallByCut p31_13 w0
theorem b117 : Ban 24 6 v110 := viaPerm map31_3 map31_4 b101 (by decide +kernel) (by decide +kernel)
theorem b118 : Ban 24 6 v111 := smallByCut p31_19 w0
theorem b119 : Ban 24 6 v112 := smallByCut p31_13 w0
theorem b120 : Ban 24 6 v113 := smallByCut p31_13 w0
theorem b121 : Ban 24 6 v114 := viaPerm map31_5 map31_5 b101 (by decide +kernel) (by decide +kernel)
theorem b122 : Ban 24 6 v115 := smallByCut p31_19 w0
theorem b123 : Ban 24 6 v116 := smallByCut p31_13 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b124 : Ban 24 7 v0 := viaBranch (ws := [v1,v4,v37,v43,v61,v5,v20,v11,v2,v62,v63,v64,v40,v53,v38,v65,v66,v67,v84,v79,v98,v99,v97,v100,v101,v102,v104,v105,v106,v103,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116]) (consBan b2 (consBan b35 (consBan b60 (consBan b61 (consBan b62 (consBan b34 (consBan b63 (consBan b64 (consBan b1 (consBan b65 (consBan b66 (consBan b67 (consBan b68 (consBan b69 (consBan b59 (consBan b70 (consBan b71 (consBan b101 (consBan b103 (consBan b104 (consBan b105 (consBan b106 (consBan b102 (consBan b107 (consBan b108 (consBan b110 (consBan b111 (consBan b112 (consBan b113 (consBan b109 (consBan b114 (consBan b115 (consBan b116 (consBan b117 (consBan b118 (consBan b119 (consBan b120 (consBan b121 (consBan b122 (consBan b123 (nilBan 24 6))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem verifiedPin : Wide 24 7 v0 := widen (by decide +kernel) b124
end PEqualNP.Outside.L_meta_13099.Support

namespace PEqualNP.Outside.L_meta_13099.Data
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_13099.Support
def target (x : Fin 6 → Bool) := Nat.testBit (4277074664 * 2 ^ 32 + 4277074600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def posBits : ℕ := 0x2671c69a65659549245138e30c2c92471450c3
def negBits : ℕ := 0x661460a614194402401286204288046101081
def sample (bank : ℕ) (i : Fin 25) (j : Fin 6) := bank.testBit (6*i.val+j.val)
def inputs : List ℕ := [0x204a0930ff,0x224992536cc93,0x28e0a31c70f1c,0x1701580f80fe0,0x1db4000fff000,0x1000000]
def seeds : List Wire := [(false,0x204a0930ff),(false,0x224992536cc93),(false,0x28e0a31c70f1c),(false,0x1701580f80fe0),(false,0x1db4000fff000),(false,0x1000000)]
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
def witness : Circuit := ⟨[⟨.and,[0,1]⟩, ⟨.or,[0,1]⟩, ⟨.or,[6,2]⟩, ⟨.or,[0,8]⟩, ⟨.and,[9,3]⟩, ⟨.or,[0,5]⟩, ⟨.and,[8,11]⟩, ⟨.or,[12,4]⟩, ⟨.and,[7,13]⟩, ⟨.or,[10,14]⟩],15⟩
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
end PEqualNP.Outside.L_meta_13099.Data

theorem PEqualNP.Outside.L_meta_13099 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4277074600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4277074600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_13099.Data.mono_enough
