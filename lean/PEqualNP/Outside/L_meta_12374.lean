import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12374.Support

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

def t0 := 0x70dc36078fe3f
def t1 := 0x3162d8a38f1fc7
def t2 := 0x181b46d1c0fe3f8
def t3 := 0x2da0036dff003ff
def t4 := 0x36cdb001ffffc00
def v0 := [t0,t1,t2,t3,t4]
def t5 := 0x100c020081e07
def v1 := [t5,t0,t1,t2,t3,t4]
def t6 := 0xdb1ff
def t7 := 0x62de3f
def t8 := 0xb46fc7
def t9 := 0xdb0ff8
def v2 := [t6,t7,t8,t9]
def t10 := 0x903f
def v3 := [t10,t6,t7,t8,t9]
def t11 := 0x6fffff
def v4 := [t6,t7,t11,t8,t9]
def t12 := 0xd21c0
def v5 := [t12,t6,t7,t8,t9]
def t13 := 0x624e00
def v6 := [t6,t13,t7,t8,t9]
def t14 := 0x421c7
def v7 := [t14,t6,t7,t8,t9]
def t15 := 0xbdffff
def v8 := [t6,t7,t8,t15,t9]
def t16 := 0x99038
def v9 := [t16,t6,t7,t8,t9]
def t17 := 0xb04e00
def v10 := [t6,t7,t17,t8,t9]
def t18 := 0x901f8
def v11 := [t18,t6,t7,t8,t9]
def t19 := 0xdfbfff
def v12 := [t6,t7,t8,t9,t19]
def t20 := 0x4b007
def v13 := [t20,t6,t7,t8,t9]
def t21 := 0xd20e00
def v14 := [t6,t7,t8,t21,t9]
def t22 := 0x204e07
def v15 := [t6,t22,t7,t8,t9]
def t23 := 0xf6ffff
def v16 := [t6,t7,t8,t9,t23]
def t24 := 0x429038
def v17 := [t6,t24,t7,t8,t9]
def t25 := 0x9421c0
def v18 := [t6,t7,t25,t8,t9]
def t26 := 0x420e38
def v19 := [t6,t26,t7,t8,t9]
def t27 := 0xfbdfff
def v20 := [t6,t7,t8,t9,t27]
def t28 := 0x20d007
def v21 := [t6,t28,t7,t8,t9]
def t29 := 0x9901c0
def v22 := [t6,t7,t29,t8,t9]
def t30 := 0x900fc0
def v23 := [t6,t7,t30,t8,t9]
def t31 := 0xff6fff
def v24 := [t6,t7,t8,t9,t31]
def t32 := 0x246007
def v25 := [t6,t32,t7,t8,t9]
def t33 := 0x4b0038
def v26 := [t6,t33,t7,t8,t9]
def p55_53 : Projection 29 12 := pick [3,4,5,13,14,15,20,21,22,26,27,28] rfl (by decide +kernel) (by decide)
def t34 := 0x376fdbe3ffffff
def v27 := [t0,t1,t34,t2,t3,t4]
def v28 := [t14,t16,t7,t8,t9]
def t35 := 0x7
def v29 := [t35,t6,t7,t8,t9]
def t36 := 0x66ffff
def v30 := [t6,t7,t36,t8,t9]
def t37 := 0x421c0
def v31 := [t37,t6,t7,t8,t9]
def t38 := 0x62de38
def v32 := [t6,t38,t7,t8,t9]
def v33 := [t14,t6,t7,t17,t9]
def t39 := 0x1c0
def v34 := [t39,t6,t7,t8,t9]
def t40 := 0xdf2fff
def v35 := [t6,t7,t8,t9,t40]
def t41 := 0x42007
def v36 := [t41,t6,t7,t8,t9]
def t42 := 0xdb0e38
def v37 := [t6,t7,t8,t42,t9]
def v38 := [t10,t14,t7,t8,t9]
def v39 := [t14,t13,t7,t8,t9]
def v40 := [t14,t7,t15,t9]
def v41 := [t14,t6,t7,t15,t9]
def v42 := [t14,t7,t8,t15,t9]
def v43 := [t14,t18,t7,t8,t9]
def v44 := [t14,t7,t8,t21,t9]
def v45 := [t14,t6,t22,t7,t9]
def v46 := [t14,t6,t24,t7,t9]
def v47 := [t14,t6,t7,t30,t9]
def v48 := [t14,t6,t33,t7,t9]
def map51_2 : Projection 12 12 := pick [1,0,2,6,7,8,3,4,5,9,11,10] rfl (by decide +kernel) (by decide)
def v49 := [t10,t11,t8,t9]
def v50 := [t10,t6,t11,t8,t9]
def v51 := [t10,t7,t11,t8,t9]
def v52 := [t12,t6,t11,t8,t9]
def v53 := [t13,t7,t11,t8,t9]
def t43 := 0x246fc7
def v54 := [t6,t43,t7,t9]
def v55 := [t6,t43,t7,t11,t9]
def v56 := [t6,t43,t7,t8,t9]
def t44 := 0xffffff
def v57 := [t6,t7,t8,t9,t44]
def t45 := 0x4b9038
def v58 := [t6,t45,t7,t9]
def v59 := [t6,t45,t7,t11,t9]
def v60 := [t6,t45,t7,t8,t9]
def t46 := 0x900000
def v61 := [t6,t7,t46,t8,t9]
def t47 := 0x4b0ff8
def v62 := [t6,t47,t7,t8]
def v63 := [t6,t47,t7,t11,t8]
def v64 := [t6,t47,t7,t8,t9]
def t48 := 0x24f007
def v65 := [t6,t48,t7,t8]
def v66 := [t6,t48,t7,t11,t8]
def v67 := [t6,t48,t7,t8,t9]
def v68 := [t20,t18,t7,t8,t9]
def t49 := 0x9007
def v69 := [t49,t6,t7,t8,t9]
def t50 := 0x66fe3f
def v70 := [t6,t7,t50,t8,t9]
def t51 := 0x42000
def v71 := [t51,t6,t7,t8,t9]
def t52 := 0x624e38
def v72 := [t6,t52,t7,t8,t9]
def t53 := 0xb4ffc7
def v73 := [t6,t7,t8,t53,t9]
def t54 := 0x9000
def v74 := [t54,t6,t7,t8,t9]
def t55 := 0xb04fc0
def v75 := [t6,t7,t55,t8,t9]
def v76 := [t20,t6,t7,t8,t19]
def v77 := [t20,t7,t8,t21]
def v78 := [t20,t6,t7,t8,t21]
def v79 := [t20,t7,t8,t21,t9]
def v80 := [t20,t6,t26,t7,t8]
def v81 := [t20,t6,t28,t7,t8]
def v82 := [t20,t6,t7,t30,t8]
def v83 := [t20,t6,t32,t7,t8]
def map51_3 : Projection 12 12 := pick [6,7,8,1,0,2,4,3,5,11,9,10] rfl (by decide +kernel) (by decide)
def map51_4 : Projection 12 12 := pick [4,3,5,7,6,8,0,1,2,10,11,9] rfl (by decide +kernel) (by decide)
def map51_9 : Projection 12 12 := pick [9,10,11,2,0,1,5,3,4,8,6,7] rfl (by decide +kernel) (by decide)
def map51_18 : Projection 12 12 := pick [4,5,3,7,8,6,10,11,9,0,1,2] rfl (by decide +kernel) (by decide)
def map51_1 : Projection 12 12 := pick [3,4,5,0,1,2,7,6,8,10,9,11] rfl (by decide +kernel) (by decide)
def map51_15 : Projection 12 12 := pick [9,11,10,2,1,0,8,6,7,5,3,4] rfl (by decide +kernel) (by decide)
def map51_20 : Projection 12 12 := pick [5,4,3,10,11,9,7,8,6,0,2,1] rfl (by decide +kernel) (by decide)
def map51_21 : Projection 12 12 := pick [10,11,9,5,4,3,8,7,6,2,0,1] rfl (by decide +kernel) (by decide)
def map51_6 : Projection 12 12 := pick [0,2,1,3,5,4,9,10,11,6,7,8] rfl (by decide +kernel) (by decide)
def map51_8 : Projection 12 12 := pick [2,0,1,9,10,11,3,5,4,6,8,7] rfl (by decide +kernel) (by decide)
def map51_12 : Projection 12 12 := pick [1,2,0,6,8,7,9,11,10,3,4,5] rfl (by decide +kernel) (by decide)
def map51_7 : Projection 12 12 := pick [3,5,4,0,2,1,10,9,11,7,6,8] rfl (by decide +kernel) (by decide)
def map51_13 : Projection 12 12 := pick [6,8,7,1,2,0,11,9,10,4,3,5] rfl (by decide +kernel) (by decide)
def map51_10 : Projection 12 12 := pick [5,3,4,10,9,11,0,2,1,7,8,6] rfl (by decide +kernel) (by decide)
def map51_19 : Projection 12 12 := pick [7,8,6,4,5,3,11,10,9,1,0,2] rfl (by decide +kernel) (by decide)
def map51_11 : Projection 12 12 := pick [10,9,11,5,3,4,2,0,1,8,7,6] rfl (by decide +kernel) (by decide)
def map51_16 : Projection 12 12 := pick [8,6,7,11,9,10,1,2,0,4,5,3] rfl (by decide +kernel) (by decide)
def t56 := 0x60d034070e038
def v84 := [t56,t0,t1,t2,t3,t4]
def t57 := 0x6098260701c07
def v85 := [t57,t0,t1,t2,t3,t4]
def p55_51 : Projection 29 12 := pick [0,1,2,10,11,12,20,21,22,23,24,25] rfl (by decide +kernel) (by decide)
def t58 := 0x306218838701c0
def v86 := [t0,t58,t1,t2,t3,t4]
def map55_6 : Projection 29 29 := pick [6,7,8,0,2,1,3,5,4,9,16,17,18,10,12,11,13,15,14,19,23,24,25,26,27,28,20,21,22] rfl (by decide +kernel) (by decide)
def map55_8 : Projection 29 29 := pick [3,5,4,6,8,7,0,1,2,9,13,15,14,16,18,17,10,11,12,19,26,27,28,20,21,22,23,24,25] rfl (by decide +kernel) (by decide)
def t59 := 0x104410008e238
def v87 := [t59,t0,t1,t2,t3,t4]
def t60 := 0x187bdef7c7fffff
def v88 := [t0,t1,t2,t60,t3,t4]
def t61 := 0x180b02c1c0701c0
def v89 := [t0,t1,t61,t2,t3,t4]
def t62 := 0x200024070023f
def v90 := [t62,t0,t1,t2,t3,t4]
def t63 := 0x100010838003c7
def v91 := [t0,t63,t1,t2,t3,t4]
def t64 := 0x2df0df7fff8ffff
def v92 := [t0,t1,t2,t3,t64,t4]
def p55_54 : Projection 29 12 := pick [6,7,8,16,17,18,23,24,25,26,27,28] rfl (by decide +kernel) (by decide)
def t65 := 0x50dc12008fc00
def v93 := [t65,t0,t1,t2,t3,t4]
def t66 := 0x304c36000023f
def v94 := [t66,t0,t1,t2,t3,t4]
def map55_1 : Projection 29 29 := pick [10,11,12,13,14,15,16,17,18,19,0,1,2,3,4,5,6,7,8,9,21,20,22,24,23,25,27,26,28] rfl (by decide +kernel) (by decide)
def t67 := 0x2d800349f8001c0
def v95 := [t0,t1,t2,t67,t3,t4]
def t68 := 0x25a0012c3f00007
def v96 := [t0,t1,t2,t68,t3,t4]
def t69 := 0x409000078fc00
def v97 := [t69,t0,t1,t2,t3,t4]
def t70 := 0x36fdfc37ffffe3f
def v98 := [t0,t1,t2,t3,t4,t70]
def t71 := 0x368d2001f870000
def v99 := [t0,t1,t2,t3,t71,t4]
def t72 := 0x12048000f03c0
def v100 := [t72,t0,t1,t2,t3,t4]
def t73 := 0x1b1f6fdbf8fffff
def v101 := [t0,t1,t2,t73,t3,t4]
def t74 := 0x304290a3801c07
def v102 := [t0,t74,t1,t2,t3,t4]
def t75 := 0x18094251c00e038
def v103 := [t0,t1,t75,t2,t3,t4]
def t76 := 0x2fb62feffff1fff
def v104 := [t0,t1,t2,t3,t76,t4]
def t77 := 0x2162c8200f1c00
def v105 := [t0,t77,t1,t2,t3,t4]
def t78 := 0x2ca00265c700038
def v106 := [t0,t1,t2,t78,t3,t4]
def t79 := 0x204200038f1c00
def v107 := [t0,t79,t1,t2,t3,t4]
def t80 := 0x37dfbd8bfffffc7
def v108 := [t0,t1,t2,t3,t4,t80]
def t81 := 0x1120d8a00003c7
def v109 := [t0,t81,t1,t2,t3,t4]
def t82 := 0x34c99001c70e000
def v110 := [t0,t1,t2,t3,t82,t4]
def t83 := 0x8000241c0003f8
def v111 := [t0,t1,t83,t2,t3,t4]
def t84 := 0x3dbb47fdfffe3ff
def v112 := [t0,t1,t2,t3,t4,t84]
def t85 := 0x101b449000fe000
def v113 := [t0,t1,t85,t2,t3,t4]
def t86 := 0x10090001c0fe000
def v114 := [t0,t1,t86,t2,t3,t4]
def t87 := 0x3edff6d1ffffff8
def v115 := [t0,t1,t2,t3,t4,t87]
def t88 := 0x81246d000003f8
def v116 := [t0,t1,t88,t2,t3,t4]
def t89 := 0x26c4b0003f01c00
def v117 := [t0,t1,t2,t89,t3,t4]
def t90 := 0x24800001ff00000
def v118 := [t0,t1,t2,t90,t3,t4]
def v119 := [t5,t0,t1,t2,t90,t3,t4]
def v120 := [t0,t1,t34,t2,t90,t3,t4]
def v121 := [t56,t0,t1,t2,t90,t3,t4]
def v122 := [t0,t58,t1,t2,t90,t3,t4]
def v123 := [t59,t0,t1,t2,t90,t3,t4]
def v124 := [t0,t1,t2,t60,t90,t3,t4]
def v125 := [t57,t0,t1,t2,t90,t3,t4]
def v126 := [t0,t1,t61,t2,t90,t3,t4]
def t91 := 0x700000
def v127 := [t91,t0,t1,t2,t3,t4]
def v128 := [t91,t0,t1,t2,t90,t3,t4]
def t92 := 0x24f0dc37ff8fe3f
def v129 := [t0,t1,t2,t92,t3,t4]
def v130 := [t0,t1,t2,t90,t92,t3,t4]
def t93 := 0x70dc36008fe3f
def v131 := [t93,t0,t1,t2,t3,t4]
def v132 := [t93,t0,t1,t2,t90,t3,t4]
def t94 := 0x24800001f800000
def v133 := [t0,t1,t2,t94,t3,t4]
def v134 := [t0,t1,t2,t94,t90,t3,t4]
def v135 := [t62,t0,t1,t2,t90,t3,t4]
def v136 := [t0,t1,t2,t90,t3,t64,t4]
def v137 := [t65,t0,t1,t2,t90,t3,t4]
def v138 := [t0,t1,t2,t90,t67,t3,t4]
def v139 := [t69,t0,t1,t2,t90,t3,t4]
def v140 := [t0,t1,t2,t90,t3,t4,t70]
def v141 := [t66,t0,t1,t2,t90,t3,t4]
def v142 := [t0,t1,t2,t90,t3,t71,t4]
def v143 := [t72,t0,t1,t2,t90,t3,t4]
def v144 := [t0,t1,t2,t73,t90,t3,t4]
def v145 := [t0,t74,t1,t2,t90,t3,t4]
def v146 := [t0,t1,t75,t2,t90,t3,t4]
def t95 := 0x3800000
def v147 := [t95,t0,t1,t2,t3,t4]
def v148 := [t95,t0,t1,t2,t90,t3,t4]
def t96 := 0x27962d8bfff1fc7
def v149 := [t0,t1,t2,t96,t3,t4]
def v150 := [t0,t1,t2,t90,t96,t3,t4]
def t97 := 0x3162d8a00f1fc7
def v151 := [t0,t97,t1,t2,t3,t4]
def v152 := [t0,t97,t1,t2,t90,t3,t4]
def t98 := 0x24800001c700000
def v153 := [t0,t1,t2,t98,t3,t4]
def v154 := [t0,t1,t2,t98,t90,t3,t4]
def v155 := [t0,t63,t1,t2,t90,t3,t4]
def v156 := [t0,t1,t2,t90,t3,t76,t4]
def v157 := [t0,t77,t1,t2,t90,t3,t4]
def v158 := [t0,t1,t2,t90,t78,t3,t4]
def v159 := [t0,t79,t1,t2,t90,t3,t4]
def v160 := [t0,t1,t2,t90,t3,t4,t80]
def v161 := [t0,t81,t1,t2,t90,t3,t4]
def v162 := [t0,t1,t2,t90,t3,t82,t4]
def t99 := 0x1c000000
def v163 := [t99,t0,t1,t2,t3,t4]
def v164 := [t99,t0,t1,t2,t90,t3,t4]
def t100 := 0x3c9b46d1fffe3f8
def v165 := [t0,t1,t2,t3,t4,t100]
def v166 := [t0,t1,t2,t90,t3,t4,t100]
def t101 := 0x181b46d000fe3f8
def v167 := [t0,t1,t101,t2,t3,t4]
def v168 := [t0,t1,t101,t2,t90,t3,t4]
def t102 := 0x248000003f00000
def v169 := [t0,t1,t2,t102,t3,t4]
def v170 := [t0,t1,t2,t102,t90,t3,t4]
def v171 := [t0,t1,t83,t2,t90,t3,t4]
def v172 := [t0,t1,t2,t90,t3,t4,t84]
def v173 := [t0,t1,t85,t2,t90,t3,t4]
def v174 := [t0,t1,t2,t90,t68,t3,t4]
def v175 := [t0,t1,t86,t2,t90,t3,t4]
def v176 := [t0,t1,t2,t90,t3,t4,t87]
def v177 := [t0,t1,t88,t2,t90,t3,t4]
def v178 := [t0,t1,t2,t90,t89,t3,t4]
def t103 := 0x920036c00003ff
def v179 := [t0,t1,t103,t2,t90,t4]
def v180 := [t0,t1,t103,t2,t3,t4]
def v181 := [t0,t1,t103,t2,t90,t3,t4]
def t104 := 0x124db00000ffc00
def v182 := [t0,t1,t104,t2,t90,t3]
def v183 := [t0,t1,t104,t2,t3,t4]
def v184 := [t0,t1,t104,t2,t90,t3,t4]
def t105 := 0x3fedb36dfffffff
def v185 := [t0,t1,t2,t90,t105]
def t106 := 0x450cf
def t107 := 0x112333
def t108 := 0x428c3c
def t109 := 0xa80fc0
def v186 := [t106,t107,t108,t109]
def t110 := 0x3
def v187 := [t110,t106,t107,t108,t109]
def t111 := 0x14f
def t112 := 0x4b3
def t113 := 0xa3c
def v188 := [t111,t112,t113]
def p2087_2085 : Projection 12 6 := pick [2,3,6,7,10,11] rfl (by decide +kernel) (by decide)
def t114 := 0x1573ff
def v189 := [t106,t107,t114,t108,t109]
def v190 := [t110,t114,t108,t109]
def v191 := [t110,t106,t114,t108,t109]
def v192 := [t110,t107,t114,t108,t109]
def t115 := 0x450cc
def v193 := [t115,t106,t114,t108,t109]
def t116 := 0x112330
def v194 := [t116,t107,t114,t108,t109]
def v195 := [t106,t116,t107,t108,t109]
def t117 := 0x46dcff
def v196 := [t107,t114,t108,t117,t109]
def t118 := 0x450c3
def v197 := [t118,t107,t114,t108,t109]
def t119 := 0xac5fcf
def v198 := [t107,t114,t108,t109,t119]
def t120 := 0x4500f
def v199 := [t120,t107,t114,t108,t109]
def v200 := [t115,t106,t107,t108,t109]
def t121 := 0x53af3f
def v201 := [t106,t114,t108,t121,t109]
def t122 := 0x112303
def v202 := [t106,t122,t114,t108,t109]
def t123 := 0xb92ff3
def v203 := [t106,t114,t108,t109,t123]
def t124 := 0x112033
def v204 := [t106,t124,t114,t108,t109]
def t125 := 0x3c
def v205 := [t125,t106,t107,t108,t109]
def t126 := 0x57ffff
def v206 := [t106,t107,t108,t126,t109]
def t127 := 0x1573c3
def v207 := [t106,t107,t127,t108,t109]
def t128 := 0x428c00
def v208 := [t106,t107,t128,t108,t109]
def t129 := 0x3c0
def v209 := [t129,t106,t107,t108,t109]
def t130 := 0xbd7fff
def v210 := [t106,t107,t108,t109,t130]
def t131 := 0x15703f
def v211 := [t106,t107,t131,t108,t109]
def t132 := 0xa80c00
def v212 := [t106,t107,t108,t132,t109]
def v213 := [t120,t106,t107,t108,t109]
def p2087_2086 : Projection 12 6 := pick [4,5,8,9,10,11] rfl (by decide +kernel) (by decide)
def map2087_3 : Projection 12 12 := pick [2,3,6,7,10,11,0,1,5,4,9,8] rfl (by decide +kernel) (by decide)
def map2087_4 : Projection 12 12 := pick [6,7,0,1,9,8,2,3,11,10,4,5] rfl (by decide +kernel) (by decide)
def map2087_9 : Projection 12 12 := pick [4,5,8,9,10,11,1,0,3,2,7,6] rfl (by decide +kernel) (by decide)
def map2087_18 : Projection 12 12 := pick [7,6,9,8,0,1,11,10,2,3,4,5] rfl (by decide +kernel) (by decide)
def t133 := 0xc
def v214 := [t133,t106,t107,t108,t109]
def map2087_2 : Projection 12 12 := pick [2,3,0,1,5,4,6,7,10,11,8,9] rfl (by decide +kernel) (by decide)
def v215 := [t106,t107,t108,t117,t109]
def v216 := [t118,t106,t107,t108,t109]
def map2087_1 : Projection 12 12 := pick [0,1,6,7,8,9,2,3,4,5,11,10] rfl (by decide +kernel) (by decide)
def t134 := 0x428c30
def v217 := [t106,t107,t134,t108,t109]
def map2087_15 : Projection 12 12 := pick [5,4,10,11,8,9,3,2,1,0,7,6] rfl (by decide +kernel) (by decide)
def map2087_20 : Projection 12 12 := pick [9,8,7,6,1,0,11,10,4,5,2,3] rfl (by decide +kernel) (by decide)
def t135 := 0xc0
def v218 := [t135,t106,t107,t108,t109]
def v219 := [t106,t107,t108,t109,t119]
def t136 := 0xa80f00
def v220 := [t106,t107,t108,t136,t109]
def map2087_21 : Projection 12 12 := pick [9,8,11,10,4,5,7,6,1,0,3,2] rfl (by decide +kernel) (by decide)
def t137 := 0x30
def v221 := [t137,t106,t107,t108,t109]
def map2087_8 : Projection 12 12 := pick [4,5,1,0,3,2,8,9,10,11,6,7] rfl (by decide +kernel) (by decide)
def map2087_12 : Projection 12 12 := pick [3,2,5,4,0,1,10,11,6,7,8,9] rfl (by decide +kernel) (by decide)
def v222 := [t106,t107,t108,t121,t109]
def v223 := [t106,t122,t107,t108,t109]
def t138 := 0x428c0c
def v224 := [t106,t107,t138,t108,t109]
def map2087_13 : Projection 12 12 := pick [3,2,10,11,6,7,5,4,0,1,9,8] rfl (by decide +kernel) (by decide)
def map2087_10 : Projection 12 12 := pick [8,9,1,0,7,6,4,5,11,10,2,3] rfl (by decide +kernel) (by decide)
def t139 := 0x300
def v225 := [t139,t106,t107,t108,t109]
def v226 := [t106,t107,t108,t109,t123]
def v227 := [t106,t124,t107,t108,t109]
def t140 := 0xa80cc0
def v228 := [t106,t107,t108,t140,t109]
def map2087_19 : Projection 12 12 := pick [7,6,11,10,2,3,9,8,0,1,5,4] rfl (by decide +kernel) (by decide)
def map2087_11 : Projection 12 12 := pick [8,9,4,5,11,10,1,0,7,6,3,2] rfl (by decide +kernel) (by decide)
def t141 := 0xc00
def v229 := [t141,t106,t107,t108,t109]
def map2087_16 : Projection 12 12 := pick [10,11,3,2,7,6,5,4,9,8,0,1] rfl (by decide +kernel) (by decide)
def t142 := 0xea8ffc
def v230 := [t106,t107,t108,t109,t142]
def t143 := 0x42803c
def v231 := [t106,t107,t143,t108,t109]
def t144 := 0xa803c0
def v232 := [t106,t107,t108,t144,t109]
def v233 := [t106,t107,t108,t109,t44]
def v234 := [t110,t106,t107,t108,t109,t44]
def t145 := 0xfff
def v235 := [t111,t112,t113,t145]
def v236 := [t106,t107,t114,t108,t109,t44]
def v237 := [t115,t106,t107,t108,t109,t44]
def v238 := [t106,t116,t107,t108,t109,t44]
def v239 := [t133,t106,t107,t108,t109,t44]
def v240 := [t106,t107,t108,t117,t109,t44]
def v241 := [t118,t106,t107,t108,t109,t44]
def v242 := [t106,t107,t134,t108,t109,t44]
def v243 := [t135,t106,t107,t108,t109,t44]
def v244 := [t106,t107,t108,t109,t119,t44]
def v245 := [t120,t106,t107,t108,t109,t44]
def v246 := [t106,t107,t108,t136,t109,t44]
def t146 := 0xfbaf30
def v247 := [t107,t108,t109,t146]
def t147 := 0x57f03f
def v248 := [t106,t107,t108,t147]
def v249 := [t110,t106,t107,t108,t147]
def v250 := [t106,t107,t114,t108,t147]
def v251 := [t115,t106,t107,t108,t147]
def v252 := [t106,t116,t107,t108,t147]
def v253 := [t133,t106,t107,t108,t147]
def v254 := [t106,t107,t108,t117,t147]
def v255 := [t118,t106,t107,t108,t147]
def v256 := [t106,t107,t134,t108,t147]
def v257 := [t120,t106,t107,t108,t147]
def t148 := 0x57f0ff
def v258 := [t106,t107,t108,t147,t148]
def v259 := [t135,t106,t107,t108,t147]
def t149 := 0x53a030
def v260 := [t106,t107,t108,t149,t147]
def v261 := [t137,t106,t107,t108,t147]
def v262 := [t106,t107,t108,t121,t147]
def v263 := [t106,t122,t107,t108,t147]
def v264 := [t106,t107,t138,t108,t147]
def v265 := [t106,t124,t107,t108,t147]
def t150 := 0x57f33f
def v266 := [t106,t107,t108,t147,t150]
def v267 := [t139,t106,t107,t108,t147]
def t151 := 0x46d00c
def v268 := [t106,t107,t108,t151,t147]
def v269 := [t106,t107,t143,t108,t147]
def t152 := 0x57fc3f
def v270 := [t106,t107,t108,t147,t152]
def v271 := [t141,t106,t107,t108,t147]
def t153 := 0x157003
def v272 := [t106,t107,t153,t108,t147]
def v273 := [t106,t107,t108,t109,t146]
def v274 := [t106,t107,t108,t147,t109]
def v275 := [t106,t107,t108,t148,t109]
def v276 := [t106,t107,t108,t149,t109]
def v277 := [t106,t107,t108,t147,t119]
def v278 := [t106,t107,t108,t147,t136]
def v279 := [t106,t107,t108,t150,t109]
def v280 := [t106,t107,t108,t151,t109]
def v281 := [t106,t107,t108,t147,t123]
def v282 := [t106,t107,t108,t147,t140]
def v283 := [t106,t107,t108,t152,t109]
def v284 := [t106,t107,t153,t108,t109]
def v285 := [t106,t107,t108,t147,t142]
def v286 := [t106,t107,t108,t147,t144]
def v287 := [t106,t107,t108,t147,t44]
def v288 := [t107,t108,t109,t146,t44]
def v289 := [t106,t107,t108,t109,t146,t44]
def v290 := [t137,t106,t107,t108,t109,t44]
def v291 := [t106,t107,t108,t121,t109,t44]
def v292 := [t106,t122,t107,t108,t109,t44]
def v293 := [t106,t107,t138,t108,t109,t44]
def v294 := [t139,t106,t107,t108,t109,t44]
def v295 := [t106,t107,t108,t109,t123,t44]
def v296 := [t106,t124,t107,t108,t109,t44]
def v297 := [t106,t107,t108,t140,t109,t44]
def t154 := 0xeedccc
def v298 := [t106,t108,t109,t154]
def v299 := [t106,t107,t108,t109,t154]
def v300 := [t106,t108,t109,t154,t44]
def v301 := [t106,t107,t108,t109,t154,t44]
def v302 := [t141,t106,t107,t108,t109,t44]
def v303 := [t106,t107,t108,t109,t142,t44]
def v304 := [t106,t107,t143,t108,t109,t44]
def v305 := [t106,t107,t108,t144,t109,t44]
def t155 := 0xbd73c3
def v306 := [t106,t107,t109,t155]
def v307 := [t106,t107,t108,t109,t155]
def v308 := [t106,t107,t109,t155,t44]
def v309 := [t106,t107,t108,t109,t155,t44]
def v310 := [t106,t107,t108,t147,t109,t44]
def p55_4119 : Projection 29 12 := pick [11,12,14,15,17,18,21,22,24,25,27,28] rfl (by decide +kernel) (by decide)
def v311 := [t0,t1,t2,t90,t3,t105]
def v312 := [t0,t1,t2,t90,t4,t105]
def v313 := [t0,t1,t2,t90,t3,t4,t105]
def v314 := [t0,t1,t2,t3,t4,t105]
def v315 := [t5,t0,t1,t2,t3,t4,t105]
def v316 := [t0,t1,t34,t2,t3,t4,t105]
def v317 := [t56,t0,t1,t2,t3,t4,t105]
def v318 := [t0,t58,t1,t2,t3,t4,t105]
def v319 := [t59,t0,t1,t2,t3,t4,t105]
def v320 := [t0,t1,t2,t60,t3,t4,t105]
def v321 := [t57,t0,t1,t2,t3,t4,t105]
def v322 := [t0,t1,t61,t2,t3,t4,t105]
def v323 := [t62,t0,t1,t2,t3,t4,t105]
def v324 := [t0,t1,t2,t3,t64,t4,t105]
def v325 := [t65,t0,t1,t2,t3,t4,t105]
def v326 := [t0,t1,t2,t67,t3,t4,t105]
def v327 := [t69,t0,t1,t2,t3,t4,t105]
def v328 := [t0,t1,t2,t3,t4,t70,t105]
def v329 := [t66,t0,t1,t2,t3,t4,t105]
def v330 := [t0,t1,t2,t3,t71,t4,t105]
def t156 := 0x609024078fe3f
def v331 := [t156,t1,t2,t3,t4]
def v332 := [t156,t0,t1,t2,t3,t4]
def v333 := [t156,t1,t2,t3,t4,t105]
def v334 := [t156,t0,t1,t2,t3,t4,t105]
def t157 := 0x3ffdff7ffffffff
def v335 := [t0,t1,t2,t3,t4,t157]
def v336 := [t0,t1,t2,t3,t4,t105,t157]
def t158 := 0x104c120000000
def v337 := [t158,t0,t1,t2,t3,t4]
def v338 := [t158,t0,t1,t2,t3,t4,t105]
def t159 := 0x3f8d2349f8701c0
def v339 := [t1,t2,t3,t4,t159]
def t160 := 0x27e4b12c3f01c07
def v340 := [t0,t1,t160,t3,t4]
def t161 := 0x9d21c0
def v341 := [t6,t161,t8,t9]
def v342 := [t20,t6,t48,t7,t8]
def t162 := 0x2df1ff
def v343 := [t6,t48,t162,t7,t8]
def t163 := 0x204000
def v344 := [t6,t163,t48,t7,t8]
def v345 := [t18,t6,t48,t7,t8]
def v346 := [t6,t28,t48,t7,t8]
def v347 := [t6,t48,t7,t50,t8]
def v348 := [t51,t6,t48,t7,t8]
def v349 := [t6,t48,t26,t7,t8]
def v350 := [t6,t32,t48,t7,t8]
def v351 := [t6,t48,t7,t8,t53]
def v352 := [t54,t6,t48,t7,t8]
def v353 := [t6,t48,t7,t30,t8]
def v354 := [t10,t6,t48,t7,t8]
def v355 := [t12,t6,t48,t7,t8]
def v356 := [t6,t48,t13,t7,t8]
def v357 := [t14,t6,t48,t7,t8]
def v358 := [t6,t48,t7,t8,t15]
def v359 := [t16,t6,t48,t7,t8]
def v360 := [t6,t48,t7,t17,t8]
def v361 := [t6,t22,t48,t7,t8]
def v362 := [t6,t48,t7,t8,t23]
def v363 := [t6,t48,t24,t7,t8]
def v364 := [t6,t48,t7,t25,t8]
def v365 := [t0,t1,t2,t3,t4,t159]
def v366 := [t0,t1,t2,t160,t3,t4]
def v367 := [t1,t2,t3,t4,t159,t105]
def v368 := [t0,t1,t160,t3,t4,t105]
def v369 := [t6,t161,t8,t9,t31]
def v370 := [t6,t48,t47,t7,t8]
def v371 := [t10,t48,t11,t8]
def v372 := [t10,t6,t48,t11,t8]
def v373 := [t10,t48,t7,t11,t8]
def v374 := [t12,t6,t48,t11,t8]
def v375 := [t48,t13,t7,t11,t8]
def v376 := [t6,t43,t48,t7]
def v377 := [t6,t43,t48,t7,t11]
def v378 := [t6,t43,t48,t7,t8]
def v379 := [t6,t48,t7,t8,t44]
def v380 := [t6,t48,t45,t7]
def v381 := [t6,t48,t45,t7,t11]
def v382 := [t6,t48,t45,t7,t8]
def v383 := [t6,t48,t7,t46,t8]
def v384 := [t0,t1,t2,t3,t4,t159,t105]
def v385 := [t72,t0,t1,t2,t3,t4,t105]
def v386 := [t0,t1,t2,t73,t3,t4,t105]
def v387 := [t0,t74,t1,t2,t3,t4,t105]
def v388 := [t0,t1,t75,t2,t3,t4,t105]
def v389 := [t0,t63,t1,t2,t3,t4,t105]
def v390 := [t0,t1,t2,t3,t76,t4,t105]
def v391 := [t0,t77,t1,t2,t3,t4,t105]
def v392 := [t0,t1,t2,t78,t3,t4,t105]
def v393 := [t0,t79,t1,t2,t3,t4,t105]
def v394 := [t0,t1,t2,t3,t4,t80,t105]
def v395 := [t0,t81,t1,t2,t3,t4,t105]
def v396 := [t0,t1,t2,t3,t82,t4,t105]
def t164 := 0x304210838f1fc7
def v397 := [t0,t164,t2,t3,t4]
def v398 := [t0,t164,t1,t2,t3,t4]
def v399 := [t0,t164,t2,t3,t4,t105]
def v400 := [t0,t164,t1,t2,t3,t4,t105]
def t165 := 0x3fffbfeffffffff
def v401 := [t0,t1,t2,t3,t4,t165]
def v402 := [t0,t1,t2,t3,t4,t105,t165]
def t166 := 0x120c820000000
def v403 := [t166,t0,t1,t2,t3,t4]
def v404 := [t166,t0,t1,t2,t3,t4,t105]
def t167 := 0x3ce99265c70e038
def v405 := [t0,t2,t3,t4,t167]
def v406 := [t0,t1,t2,t3,t4,t167]
def v407 := [t0,t2,t3,t4,t167,t105]
def v408 := [t0,t1,t2,t3,t4,t167,t105]
def v409 := [t0,t1,t83,t2,t3,t4,t105]
def v410 := [t0,t1,t2,t3,t4,t84,t105]
def v411 := [t0,t1,t85,t2,t3,t4,t105]
def v412 := [t0,t1,t2,t68,t3,t4,t105]
def v413 := [t0,t1,t86,t2,t3,t4,t105]
def v414 := [t0,t1,t2,t3,t4,t87,t105]
def v415 := [t0,t1,t88,t2,t3,t4,t105]
def v416 := [t0,t1,t2,t89,t3,t4,t105]
def t168 := 0x18090241c0fe3f8
def v417 := [t0,t1,t168,t3,t4]
def v418 := [t0,t1,t168,t2,t3,t4]
def v419 := [t0,t1,t168,t3,t4,t105]
def v420 := [t0,t1,t168,t2,t3,t4,t105]
def t169 := 0x3ffff7fdfffffff
def v421 := [t0,t1,t2,t3,t4,t169]
def v422 := [t0,t1,t2,t3,t4,t105,t169]
def t170 := 0x1244900000000
def v423 := [t170,t0,t1,t2,t3,t4]
def v424 := [t170,t0,t1,t2,t3,t4,t105]
def v425 := [t0,t1,t2,t160,t3,t4,t105]
def v426 := [t0,t1,t103,t2,t3,t105]
def t171 := 0x6dbff
def t172 := 0x86e3f
def t173 := 0xb17c7
def t174 := 0xda3f8
def v427 := [t171,t172,t173,t174]
def p55_39 : Projection 29 10 := pick [10,11,12,13,14,15,16,17,18,19] rfl (by decide +kernel) (by decide)
def v428 := [t0,t1,t103,t2,t3,t4,t105]
def v429 := [t0,t1,t104,t2,t4,t105]
def v430 := [t0,t1,t104,t2,t3,t4,t105]
theorem b0 : Ban 12 4 v3 := checkedSmall
theorem b1 : Ban 12 4 v4 := checkedSmall
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b24 : Ban 12 5 v2 := viaBranch (ws := [v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26]) (consBan b0 (consBan b1 (consBan b2 (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b10 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (consBan b19 (consBan b20 (consBan b21 (consBan b22 (consBan b23 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b49 : Ban 12 4 v49 := checkedSmall
theorem b50 : Ban 12 4 v50 := checkedSmall
theorem b51 : Ban 12 4 v51 := checkedSmall
theorem b52 : Ban 12 4 v52 := checkedSmall
theorem b53 : Ban 12 4 v53 := checkedSmall
theorem b54 : Ban 12 4 v54 := checkedSmall
theorem b55 : Ban 12 4 v55 := checkedSmall
theorem b56 : Ban 12 4 v56 := checkedSmall
theorem b57 : Ban 12 4 v57 := checkedSmall
theorem b58 : Ban 12 4 v58 := checkedSmall
theorem b59 : Ban 12 4 v59 := checkedSmall
theorem b60 : Ban 12 4 v60 := checkedSmall
theorem b61 : Ban 12 4 v61 := checkedSmall
theorem b62 : Ban 12 4 v62 := checkedSmall
theorem b63 : Ban 12 4 v63 := checkedSmall
theorem b64 : Ban 12 4 v64 := checkedSmall
theorem b65 : Ban 12 4 v65 := checkedSmall
theorem b66 : Ban 12 4 v66 := checkedSmall
theorem b67 : Ban 12 4 v67 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b68 : Ban 12 5 v4 := viaBranch (ws := [v49,v50,v51,v52,v53,v6,v5,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67]) (consBan b49 (consBan b50 (consBan b51 (consBan b52 (consBan b53 (consBan b3 (consBan b2 (consBan b54 (consBan b55 (consBan b56 (consBan b57 (consBan b58 (consBan b59 (consBan b60 (consBan b61 (consBan b62 (consBan b63 (consBan b64 (consBan b65 (consBan b66 (consBan b67 (nilBan 12 4)))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b103 : Ban 12 5 v24 := viaPerm map51_16 map51_16 b68 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w7 : Wide 12 5 v24 := viaSub (ws := [v2,v24]) (consBan b24 (consBan b103 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b25 : Ban 29 7 v1 := smallByCut p55_53 w7
theorem b26 : Ban 12 4 v28 := checkedSmall
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b47 : Ban 12 5 v7 := viaBranch (ws := [v28,v9,v29,v30,v31,v32,v33,v10,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48]) (consBan b26 (consBan b6 (consBan b27 (consBan b28 (consBan b29 (consBan b30 (consBan b31 (consBan b7 (consBan b32 (consBan b33 (consBan b34 (consBan b35 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (consBan b40 (consBan b41 (consBan b42 (consBan b43 (consBan b44 (consBan b45 (consBan b46 (nilBan 12 4)))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b48 : Ban 12 5 v3 := viaPerm map51_2 map51_2 b47 (by decide +kernel) (by decide +kernel)
theorem b69 : Ban 12 4 v68 := checkedSmall
theorem b70 : Ban 12 4 v69 := checkedSmall
theorem b71 : Ban 12 4 v70 := checkedSmall
theorem b72 : Ban 12 4 v71 := checkedSmall
theorem b73 : Ban 12 4 v72 := checkedSmall
theorem b74 : Ban 12 4 v73 := checkedSmall
theorem b75 : Ban 12 4 v74 := checkedSmall
theorem b76 : Ban 12 4 v75 := checkedSmall
theorem b77 : Ban 12 4 v76 := checkedSmall
theorem b78 : Ban 12 4 v77 := checkedSmall
theorem b79 : Ban 12 4 v78 := checkedSmall
theorem b80 : Ban 12 4 v79 := checkedSmall
theorem b81 : Ban 12 4 v80 := checkedSmall
theorem b82 : Ban 12 4 v81 := checkedSmall
theorem b83 : Ban 12 4 v82 := checkedSmall
theorem b84 : Ban 12 4 v83 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b85 : Ban 12 5 v13 := viaBranch (ws := [v68,v11,v69,v70,v71,v72,v36,v73,v74,v75,v76,v12,v77,v78,v79,v80,v81,v82,v83]) (consBan b69 (consBan b8 (consBan b70 (consBan b71 (consBan b72 (consBan b73 (consBan b34 (consBan b74 (consBan b75 (consBan b76 (consBan b77 (consBan b9 (consBan b78 (consBan b79 (consBan b80 (consBan b81 (consBan b82 (consBan b83 (consBan b84 (nilBan 12 4)))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b86 : Ban 12 5 v5 := viaPerm map51_3 map51_4 b85 (by decide +kernel) (by decide +kernel)
theorem b87 : Ban 12 5 v6 := viaPerm map51_9 map51_18 b85 (by decide +kernel) (by decide +kernel)
theorem b88 : Ban 12 5 v8 := viaPerm map51_2 map51_2 b68 (by decide +kernel) (by decide +kernel)
theorem b89 : Ban 12 5 v9 := viaPerm map51_1 map51_1 b85 (by decide +kernel) (by decide +kernel)
theorem b90 : Ban 12 5 v10 := viaPerm map51_15 map51_20 b85 (by decide +kernel) (by decide +kernel)
theorem b91 : Ban 12 5 v11 := viaPerm map51_1 map51_1 b47 (by decide +kernel) (by decide +kernel)
theorem b92 : Ban 12 5 v12 := viaPerm map51_4 map51_3 b68 (by decide +kernel) (by decide +kernel)
theorem b93 : Ban 12 5 v14 := viaPerm map51_21 map51_21 b85 (by decide +kernel) (by decide +kernel)
theorem b94 : Ban 12 5 v15 := viaPerm map51_6 map51_6 b47 (by decide +kernel) (by decide +kernel)
theorem b95 : Ban 12 5 v16 := viaPerm map51_8 map51_12 b68 (by decide +kernel) (by decide +kernel)
theorem b96 : Ban 12 5 v17 := viaPerm map51_7 map51_7 b85 (by decide +kernel) (by decide +kernel)
theorem b97 : Ban 12 5 v18 := viaPerm map51_13 map51_10 b85 (by decide +kernel) (by decide +kernel)
theorem b98 : Ban 12 5 v19 := viaPerm map51_7 map51_7 b47 (by decide +kernel) (by decide +kernel)
theorem b99 : Ban 12 5 v20 := viaPerm map51_10 map51_13 b68 (by decide +kernel) (by decide +kernel)
theorem b100 : Ban 12 5 v21 := viaPerm map51_6 map51_6 b85 (by decide +kernel) (by decide +kernel)
theorem b101 : Ban 12 5 v22 := viaPerm map51_19 map51_11 b85 (by decide +kernel) (by decide +kernel)
theorem b102 : Ban 12 5 v23 := viaPerm map51_13 map51_10 b47 (by decide +kernel) (by decide +kernel)
theorem b104 : Ban 12 5 v25 := viaPerm map51_12 map51_8 b85 (by decide +kernel) (by decide +kernel)
theorem b105 : Ban 12 5 v26 := viaPerm map51_18 map51_9 b85 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b106 : Ban 12 6 v2 := viaBranch (ws := [v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26]) (consBan b48 (consBan b68 (consBan b86 (consBan b87 (consBan b47 (consBan b88 (consBan b89 (consBan b90 (consBan b91 (consBan b92 (consBan b85 (consBan b93 (consBan b94 (consBan b95 (consBan b96 (consBan b97 (consBan b98 (consBan b99 (consBan b100 (consBan b101 (consBan b102 (consBan b103 (consBan b104 (consBan b105 (nilBan 12 5))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w1 : Wide 12 6 v2 := viaSub (ws := [v2]) (consBan b106 (nilBan 12 6)) (by decide) (by decide +kernel)
theorem b107 : Ban 29 7 v27 := smallByCut p55_53 w1
theorem b109 : Ban 29 7 v84 := smallByCut p55_54 w7
theorem b110 : Ban 29 7 v86 := smallByCut p55_53 w7
theorem b111 : Ban 29 7 v87 := smallByCut p55_51 w7
theorem b112 : Ban 29 7 v88 := smallByCut p55_51 w1
theorem b108 : Ban 29 7 v85 := smallByCut p55_54 w7
theorem b113 : Ban 29 7 v89 := smallByCut p55_51 w7
theorem b115 : Ban 29 7 v90 := smallByCut p55_54 w7
theorem b116 : Ban 29 7 v92 := smallByCut p55_54 w1
theorem b118 : Ban 29 7 v93 := smallByCut p55_54 w7
theorem b120 : Ban 29 7 v95 := smallByCut p55_54 w1
theorem b121 : Ban 29 7 v97 := smallByCut p55_54 w7
theorem b122 : Ban 29 7 v98 := smallByCut p55_54 w1
theorem b117 : Ban 29 7 v94 := smallByCut p55_54 w7
theorem b123 : Ban 29 7 v99 := smallByCut p55_54 w1
theorem b124 : Ban 29 7 v100 := smallByCut p55_51 w7
theorem b125 : Ban 29 7 v101 := smallByCut p55_51 w1
theorem b126 : Ban 29 7 v102 := smallByCut p55_53 w7
theorem b127 : Ban 29 7 v103 := smallByCut p55_51 w7
theorem b114 : Ban 29 7 v91 := smallByCut p55_53 w7
theorem b128 : Ban 29 7 v104 := smallByCut p55_53 w1
theorem b129 : Ban 29 7 v105 := smallByCut p55_53 w7
theorem b130 : Ban 29 7 v106 := smallByCut p55_53 w1
theorem b131 : Ban 29 7 v107 := smallByCut p55_53 w7
theorem b132 : Ban 29 7 v108 := smallByCut p55_53 w1
theorem b133 : Ban 29 7 v109 := smallByCut p55_53 w7
theorem b134 : Ban 29 7 v110 := smallByCut p55_53 w1
theorem b135 : Ban 29 7 v111 := smallByCut p55_51 w7
theorem b136 : Ban 29 7 v112 := smallByCut p55_51 w1
theorem b137 : Ban 29 7 v113 := smallByCut p55_51 w7
theorem b119 : Ban 29 7 v96 := smallByCut p55_51 w1
theorem b138 : Ban 29 7 v114 := smallByCut p55_51 w7
theorem b139 : Ban 29 7 v115 := smallByCut p55_51 w1
theorem b140 : Ban 29 7 v116 := smallByCut p55_51 w7
theorem b141 : Ban 29 7 v117 := smallByCut p55_51 w1
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w2 : Wide 12 5 v23 := viaSub (ws := [v2,v23]) (consBan b24 (consBan b102 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b142 : Ban 29 6 v119 := smallByCut p55_53 w2
theorem b143 : Ban 29 6 v120 := smallByCut p55_53 w2
theorem b144 : Ban 29 6 v121 := smallByCut p55_53 w2
theorem b145 : Ban 29 6 v122 := smallByCut p55_53 w2
theorem b146 : Ban 29 6 v123 := smallByCut p55_51 w2
theorem b147 : Ban 29 6 v124 := smallByCut p55_51 w2
theorem b148 : Ban 29 6 v125 := smallByCut p55_51 w2
theorem b149 : Ban 29 6 v126 := smallByCut p55_51 w2
theorem b462 : Ban 10 4 v427 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w10 : Wide 10 4 v427 := viaSub (ws := [v427]) (consBan b462 (nilBan 10 4)) (by decide) (by decide +kernel)
theorem b150 : Ban 29 6 v127 := smallByCut p55_39 w10
theorem b151 : Ban 29 6 v128 := smallByCut p55_39 w10
theorem b152 : Ban 29 6 v129 := smallByCut p55_54 w2
theorem b153 : Ban 29 6 v130 := smallByCut p55_39 w10
theorem b154 : Ban 29 6 v131 := smallByCut p55_54 w7
theorem b155 : Ban 29 6 v132 := smallByCut p55_39 w10
theorem b156 : Ban 29 6 v133 := smallByCut p55_39 w10
theorem b157 : Ban 29 6 v134 := smallByCut p55_39 w10
theorem b158 : Ban 29 6 v135 := smallByCut p55_39 w10
theorem b159 : Ban 29 6 v136 := smallByCut p55_39 w10
theorem b160 : Ban 29 6 v137 := smallByCut p55_39 w10
theorem b161 : Ban 29 6 v138 := smallByCut p55_39 w10
theorem b208 : Ban 6 3 v188 := checkedSmall
theorem b257 : Ban 6 3 v235 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w4 : Wide 6 3 v235 := viaSub (ws := [v188,v235]) (consBan b208 (consBan b257 (nilBan 6 3))) (by decide) (by decide +kernel)
theorem b209 : Ban 12 5 v187 := smallByCut p2087_2085 w4
theorem b210 : Ban 12 4 v190 := smallByCut p2087_2085 w4
theorem b211 : Ban 12 4 v191 := smallByCut p2087_2085 w4
theorem b212 : Ban 12 4 v192 := smallByCut p2087_2085 w4
theorem b213 : Ban 12 4 v193 := smallByCut p2087_2086 w4
theorem b214 : Ban 12 4 v194 := smallByCut p2087_2085 w4
theorem b215 : Ban 12 4 v195 := smallByCut p2087_2085 w4
theorem b216 : Ban 12 4 v196 := checkedSmall
theorem b217 : Ban 12 4 v197 := smallByCut p2087_2086 w4
theorem b218 : Ban 12 4 v198 := checkedSmall
theorem b219 : Ban 12 4 v199 := smallByCut p2087_2086 w4
theorem b220 : Ban 12 4 v200 := smallByCut p2087_2085 w4
theorem b221 : Ban 12 4 v201 := checkedSmall
theorem b222 : Ban 12 4 v202 := smallByCut p2087_2085 w4
theorem b223 : Ban 12 4 v203 := checkedSmall
theorem b224 : Ban 12 4 v204 := smallByCut p2087_2085 w4
theorem b225 : Ban 12 4 v205 := checkedSmall
theorem b226 : Ban 12 4 v206 := checkedSmall
theorem b227 : Ban 12 4 v207 := checkedSmall
theorem b228 : Ban 12 4 v208 := checkedSmall
theorem b229 : Ban 12 4 v209 := checkedSmall
theorem b230 : Ban 12 4 v210 := checkedSmall
theorem b231 : Ban 12 4 v211 := checkedSmall
theorem b232 : Ban 12 4 v212 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b233 : Ban 12 5 v189 := viaBranch (ws := [v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212]) (consBan b210 (consBan b211 (consBan b212 (consBan b213 (consBan b214 (consBan b215 (consBan b216 (consBan b217 (consBan b218 (consBan b219 (consBan b220 (consBan b221 (consBan b222 (consBan b223 (consBan b224 (consBan b225 (consBan b226 (consBan b227 (consBan b228 (consBan b229 (consBan b230 (consBan b231 (consBan b232 (nilBan 12 4)))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b235 : Ban 12 5 v200 := smallByCut p2087_2086 w4
theorem b236 : Ban 12 5 v195 := smallByCut p2087_2085 w4
theorem b237 : Ban 12 5 v214 := smallByCut p2087_2086 w4
theorem b238 : Ban 12 5 v215 := viaPerm map2087_2 map2087_2 b233 (by decide +kernel) (by decide +kernel)
theorem b239 : Ban 12 5 v216 := smallByCut p2087_2086 w4
theorem b234 : Ban 12 5 v213 := smallByCut p2087_2086 w4
theorem b240 : Ban 12 5 v217 := viaPerm map2087_15 map2087_20 b234 (by decide +kernel) (by decide +kernel)
theorem b241 : Ban 12 5 v218 := smallByCut p2087_2086 w4
theorem b242 : Ban 12 5 v219 := viaPerm map2087_4 map2087_3 b233 (by decide +kernel) (by decide +kernel)
theorem b243 : Ban 12 5 v220 := viaPerm map2087_21 map2087_21 b234 (by decide +kernel) (by decide +kernel)
theorem b244 : Ban 12 5 v221 := smallByCut p2087_2085 w4
theorem b245 : Ban 12 5 v222 := viaPerm map2087_8 map2087_12 b233 (by decide +kernel) (by decide +kernel)
theorem b246 : Ban 12 5 v223 := smallByCut p2087_2085 w4
theorem b247 : Ban 12 5 v224 := viaPerm map2087_13 map2087_10 b234 (by decide +kernel) (by decide +kernel)
theorem b248 : Ban 12 5 v225 := smallByCut p2087_2085 w4
theorem b249 : Ban 12 5 v226 := viaPerm map2087_10 map2087_13 b233 (by decide +kernel) (by decide +kernel)
theorem b250 : Ban 12 5 v227 := smallByCut p2087_2085 w4
theorem b251 : Ban 12 5 v228 := viaPerm map2087_19 map2087_11 b234 (by decide +kernel) (by decide +kernel)
theorem b252 : Ban 12 5 v229 := viaPerm map2087_16 map2087_16 b209 (by decide +kernel) (by decide +kernel)
theorem b253 : Ban 12 5 v230 := viaPerm map2087_16 map2087_16 b233 (by decide +kernel) (by decide +kernel)
theorem b254 : Ban 12 5 v231 := viaPerm map2087_12 map2087_8 b234 (by decide +kernel) (by decide +kernel)
theorem b255 : Ban 12 5 v232 := viaPerm map2087_18 map2087_9 b234 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b256 : Ban 12 6 v186 := viaBranch (ws := [v187,v189,v200,v195,v214,v215,v216,v217,v218,v219,v213,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232]) (consBan b209 (consBan b233 (consBan b235 (consBan b236 (consBan b237 (consBan b238 (consBan b239 (consBan b240 (consBan b241 (consBan b242 (consBan b234 (consBan b243 (consBan b244 (consBan b245 (consBan b246 (consBan b247 (consBan b248 (consBan b249 (consBan b250 (consBan b251 (consBan b252 (consBan b253 (consBan b254 (consBan b255 (nilBan 12 5))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b258 : Ban 12 5 v234 := smallByCut p2087_2085 w4
theorem b259 : Ban 12 5 v236 := checkedSmall
theorem b260 : Ban 12 5 v237 := smallByCut p2087_2086 w4
theorem b261 : Ban 12 5 v238 := smallByCut p2087_2085 w4
theorem b262 : Ban 12 5 v239 := smallByCut p2087_2086 w4
theorem b263 : Ban 12 5 v240 := checkedSmall
theorem b264 : Ban 12 5 v241 := smallByCut p2087_2086 w4
theorem b265 : Ban 12 5 v242 := checkedSmall
theorem b266 : Ban 12 5 v243 := smallByCut p2087_2086 w4
theorem b267 : Ban 12 5 v244 := checkedSmall
theorem b268 : Ban 12 5 v245 := smallByCut p2087_2086 w4
theorem b269 : Ban 12 5 v246 := checkedSmall
theorem b270 : Ban 12 4 v249 := checkedSmall
theorem b271 : Ban 12 4 v250 := checkedSmall
theorem b272 : Ban 12 4 v251 := checkedSmall
theorem b273 : Ban 12 4 v252 := checkedSmall
theorem b274 : Ban 12 4 v253 := checkedSmall
theorem b275 : Ban 12 4 v254 := checkedSmall
theorem b276 : Ban 12 4 v255 := checkedSmall
theorem b277 : Ban 12 4 v256 := checkedSmall
theorem b278 : Ban 12 4 v257 := checkedSmall
theorem b279 : Ban 12 4 v258 := checkedSmall
theorem b280 : Ban 12 4 v259 := checkedSmall
theorem b281 : Ban 12 4 v260 := checkedSmall
theorem b282 : Ban 12 4 v261 := checkedSmall
theorem b283 : Ban 12 4 v262 := checkedSmall
theorem b284 : Ban 12 4 v263 := checkedSmall
theorem b285 : Ban 12 4 v264 := checkedSmall
theorem b286 : Ban 12 4 v265 := checkedSmall
theorem b287 : Ban 12 4 v266 := checkedSmall
theorem b288 : Ban 12 4 v267 := checkedSmall
theorem b289 : Ban 12 4 v268 := checkedSmall
theorem b290 : Ban 12 4 v269 := checkedSmall
theorem b291 : Ban 12 4 v270 := checkedSmall
theorem b292 : Ban 12 4 v271 := checkedSmall
theorem b293 : Ban 12 4 v272 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b294 : Ban 12 5 v248 := viaBranch (ws := [v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272]) (consBan b270 (consBan b271 (consBan b272 (consBan b273 (consBan b274 (consBan b275 (consBan b276 (consBan b277 (consBan b278 (consBan b279 (consBan b280 (consBan b281 (consBan b282 (consBan b283 (consBan b284 (consBan b285 (consBan b286 (consBan b287 (consBan b288 (consBan b289 (consBan b290 (consBan b291 (consBan b292 (consBan b293 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b295 : Ban 12 5 v247 := viaPerm map2087_9 map2087_18 b294 (by decide +kernel) (by decide +kernel)
theorem b296 : Ban 12 4 v213 := smallByCut p2087_2086 w4
theorem b297 : Ban 12 4 v275 := checkedSmall
theorem b298 : Ban 12 4 v218 := smallByCut p2087_2086 w4
theorem b299 : Ban 12 4 v276 := checkedSmall
theorem b300 : Ban 12 4 v277 := checkedSmall
theorem b301 : Ban 12 4 v278 := checkedSmall
theorem b302 : Ban 12 4 v227 := smallByCut p2087_2085 w4
theorem b303 : Ban 12 4 v279 := checkedSmall
theorem b304 : Ban 12 4 v225 := smallByCut p2087_2085 w4
theorem b305 : Ban 12 4 v280 := checkedSmall
theorem b306 : Ban 12 4 v281 := checkedSmall
theorem b307 : Ban 12 4 v282 := checkedSmall
theorem b308 : Ban 12 4 v231 := checkedSmall
theorem b309 : Ban 12 4 v283 := checkedSmall
theorem b310 : Ban 12 4 v229 := checkedSmall
theorem b311 : Ban 12 4 v284 := checkedSmall
theorem b312 : Ban 12 4 v285 := checkedSmall
theorem b313 : Ban 12 4 v286 := checkedSmall
theorem b314 : Ban 12 4 v287 := checkedSmall
theorem b315 : Ban 12 4 v233 := smallByCut p2087_2085 w4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b316 : Ban 12 5 v274 := viaBranch (ws := [v213,v275,v218,v276,v259,v277,v257,v278,v227,v279,v225,v280,v267,v281,v265,v282,v231,v283,v229,v284,v271,v285,v269,v286,v287,v233]) (consBan b296 (consBan b297 (consBan b298 (consBan b299 (consBan b280 (consBan b300 (consBan b278 (consBan b301 (consBan b302 (consBan b303 (consBan b304 (consBan b305 (consBan b288 (consBan b306 (consBan b286 (consBan b307 (consBan b308 (consBan b309 (consBan b310 (consBan b311 (consBan b292 (consBan b312 (consBan b290 (consBan b313 (consBan b314 (consBan b315 (nilBan 12 4))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b317 : Ban 12 5 v273 := viaPerm map2087_9 map2087_18 b316 (by decide +kernel) (by decide +kernel)
theorem b318 : Ban 12 5 v288 := checkedSmall
theorem b319 : Ban 12 5 v289 := checkedSmall
theorem b320 : Ban 12 5 v290 := smallByCut p2087_2085 w4
theorem b321 : Ban 12 5 v291 := checkedSmall
theorem b322 : Ban 12 5 v292 := smallByCut p2087_2085 w4
theorem b323 : Ban 12 5 v293 := checkedSmall
theorem b324 : Ban 12 5 v294 := smallByCut p2087_2085 w4
theorem b325 : Ban 12 5 v295 := checkedSmall
theorem b326 : Ban 12 5 v296 := smallByCut p2087_2085 w4
theorem b327 : Ban 12 5 v297 := checkedSmall
theorem b328 : Ban 12 5 v298 := viaPerm map2087_3 map2087_4 b294 (by decide +kernel) (by decide +kernel)
theorem b329 : Ban 12 5 v299 := viaPerm map2087_3 map2087_4 b316 (by decide +kernel) (by decide +kernel)
theorem b330 : Ban 12 5 v300 := checkedSmall
theorem b331 : Ban 12 5 v301 := checkedSmall
theorem b332 : Ban 12 5 v302 := viaPerm map2087_16 map2087_16 b258 (by decide +kernel) (by decide +kernel)
theorem b333 : Ban 12 5 v303 := checkedSmall
theorem b334 : Ban 12 5 v304 := checkedSmall
theorem b335 : Ban 12 5 v305 := checkedSmall
theorem b336 : Ban 12 5 v306 := viaPerm map2087_1 map2087_1 b294 (by decide +kernel) (by decide +kernel)
theorem b337 : Ban 12 5 v307 := viaPerm map2087_1 map2087_1 b316 (by decide +kernel) (by decide +kernel)
theorem b338 : Ban 12 5 v308 := checkedSmall
theorem b339 : Ban 12 5 v309 := checkedSmall
theorem b340 : Ban 12 5 v287 := checkedSmall
theorem b341 : Ban 12 5 v310 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b342 : Ban 12 6 v233 := viaBranch (ws := [v234,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v273,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v248,v274,v287,v310]) (consBan b258 (consBan b259 (consBan b260 (consBan b261 (consBan b262 (consBan b263 (consBan b264 (consBan b265 (consBan b266 (consBan b267 (consBan b268 (consBan b269 (consBan b295 (consBan b317 (consBan b318 (consBan b319 (consBan b320 (consBan b321 (consBan b322 (consBan b323 (consBan b324 (consBan b325 (consBan b326 (consBan b327 (consBan b328 (consBan b329 (consBan b330 (consBan b331 (consBan b332 (consBan b333 (consBan b334 (consBan b335 (consBan b336 (consBan b337 (consBan b338 (consBan b339 (consBan b294 (consBan b316 (consBan b340 (consBan b341 (nilBan 12 5))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w5 : Wide 12 6 v233 := viaSub (ws := [v186,v233]) (consBan b256 (consBan b342 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b162 : Ban 29 6 v139 := smallByCut p55_4119 w5
theorem b163 : Ban 29 6 v140 := smallByCut p55_4119 w5
theorem b164 : Ban 29 6 v141 := smallByCut p55_4119 w5
theorem b165 : Ban 29 6 v142 := smallByCut p55_54 w2
theorem b166 : Ban 29 6 v143 := smallByCut p55_51 w2
theorem b167 : Ban 29 6 v144 := smallByCut p55_51 w2
theorem b168 : Ban 29 6 v145 := smallByCut p55_51 w2
theorem b169 : Ban 29 6 v146 := smallByCut p55_51 w2
theorem b170 : Ban 29 6 v147 := smallByCut p55_39 w10
theorem b171 : Ban 29 6 v148 := smallByCut p55_39 w10
theorem b172 : Ban 29 6 v149 := smallByCut p55_53 w2
theorem b173 : Ban 29 6 v150 := smallByCut p55_39 w10
theorem b174 : Ban 29 6 v151 := smallByCut p55_53 w7
theorem b175 : Ban 29 6 v152 := smallByCut p55_39 w10
theorem b176 : Ban 29 6 v153 := smallByCut p55_39 w10
theorem b177 : Ban 29 6 v154 := smallByCut p55_39 w10
theorem b178 : Ban 29 6 v155 := smallByCut p55_39 w10
theorem b179 : Ban 29 6 v156 := smallByCut p55_39 w10
theorem b180 : Ban 29 6 v157 := smallByCut p55_39 w10
theorem b181 : Ban 29 6 v158 := smallByCut p55_39 w10
theorem b182 : Ban 29 6 v159 := smallByCut p55_4119 w5
theorem b183 : Ban 29 6 v160 := smallByCut p55_4119 w5
theorem b184 : Ban 29 6 v161 := smallByCut p55_4119 w5
theorem b185 : Ban 29 6 v162 := smallByCut p55_53 w2
theorem b186 : Ban 29 6 v163 := smallByCut p55_39 w10
theorem b187 : Ban 29 6 v164 := smallByCut p55_39 w10
theorem b188 : Ban 29 6 v165 := smallByCut p55_51 w2
theorem b189 : Ban 29 6 v166 := smallByCut p55_39 w10
theorem b190 : Ban 29 6 v167 := smallByCut p55_51 w7
theorem b191 : Ban 29 6 v168 := smallByCut p55_39 w10
theorem b192 : Ban 29 6 v169 := smallByCut p55_39 w10
theorem b193 : Ban 29 6 v170 := smallByCut p55_39 w10
theorem b194 : Ban 29 6 v171 := smallByCut p55_39 w10
theorem b195 : Ban 29 6 v172 := smallByCut p55_39 w10
theorem b196 : Ban 29 6 v173 := smallByCut p55_39 w10
theorem b197 : Ban 29 6 v174 := smallByCut p55_39 w10
theorem b198 : Ban 29 6 v175 := smallByCut p55_4119 w5
theorem b199 : Ban 29 6 v176 := smallByCut p55_4119 w5
theorem b200 : Ban 29 6 v177 := smallByCut p55_4119 w5
theorem b201 : Ban 29 6 v178 := smallByCut p55_51 w2
theorem b202 : Ban 29 6 v179 := smallByCut p55_39 w10
theorem b203 : Ban 29 6 v180 := smallByCut p55_39 w10
theorem b204 : Ban 29 6 v181 := smallByCut p55_39 w10
theorem b205 : Ban 29 6 v182 := smallByCut p55_39 w10
theorem b206 : Ban 29 6 v183 := checkedSmall
theorem b207 : Ban 29 6 v184 := smallByCut p55_39 w10
theorem b343 : Ban 29 6 v185 := smallByCut p55_4119 w5
theorem b344 : Ban 29 6 v311 := smallByCut p55_39 w10
theorem b345 : Ban 29 6 v312 := smallByCut p55_4119 w5
theorem b346 : Ban 29 6 v313 := smallByCut p55_39 w10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b347 : Ban 29 7 v118 := viaBranch (ws := [v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v163,v164,v165,v166,v167,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184,v185,v311,v312,v313]) (consBan b142 (consBan b143 (consBan b144 (consBan b145 (consBan b146 (consBan b147 (consBan b148 (consBan b149 (consBan b150 (consBan b151 (consBan b152 (consBan b153 (consBan b154 (consBan b155 (consBan b156 (consBan b157 (consBan b158 (consBan b159 (consBan b160 (consBan b161 (consBan b162 (consBan b163 (consBan b164 (consBan b165 (consBan b166 (consBan b167 (consBan b168 (consBan b169 (consBan b170 (consBan b171 (consBan b172 (consBan b173 (consBan b174 (consBan b175 (consBan b176 (consBan b177 (consBan b178 (consBan b179 (consBan b180 (consBan b181 (consBan b182 (consBan b183 (consBan b184 (consBan b185 (consBan b186 (consBan b187 (consBan b188 (consBan b189 (consBan b190 (consBan b191 (consBan b192 (consBan b193 (consBan b194 (consBan b195 (consBan b196 (consBan b197 (consBan b198 (consBan b199 (consBan b200 (consBan b201 (consBan b202 (consBan b203 (consBan b204 (consBan b205 (consBan b206 (consBan b207 (consBan b343 (consBan b344 (consBan b345 (consBan b346 (nilBan 29 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b349 : Ban 29 6 v315 := smallByCut p55_53 w7
theorem b350 : Ban 29 6 v316 := smallByCut p55_53 w7
theorem b351 : Ban 29 6 v317 := smallByCut p55_53 w7
theorem b352 : Ban 29 6 v318 := smallByCut p55_53 w7
theorem b353 : Ban 29 6 v319 := smallByCut p55_51 w7
theorem b354 : Ban 29 6 v320 := smallByCut p55_51 w7
theorem b355 : Ban 29 6 v321 := smallByCut p55_51 w7
theorem b356 : Ban 29 6 v322 := smallByCut p55_51 w7
theorem b357 : Ban 29 6 v323 := smallByCut p55_39 w10
theorem b358 : Ban 29 6 v324 := smallByCut p55_54 w7
theorem b359 : Ban 29 6 v325 := smallByCut p55_54 w7
theorem b360 : Ban 29 6 v326 := smallByCut p55_39 w10
theorem b361 : Ban 29 6 v327 := smallByCut p55_54 w7
theorem b362 : Ban 29 6 v328 := smallByCut p55_54 w7
theorem b363 : Ban 29 6 v329 := smallByCut p55_54 w7
theorem b364 : Ban 29 6 v330 := smallByCut p55_54 w7
theorem b365 : Ban 29 6 v331 := smallByCut p55_54 w7
theorem b366 : Ban 29 6 v332 := smallByCut p55_54 w7
theorem b367 : Ban 29 6 v333 := smallByCut p55_54 w7
theorem b368 : Ban 29 6 v334 := smallByCut p55_54 w7
theorem b369 : Ban 29 6 v335 := smallByCut p55_54 w7
theorem b370 : Ban 29 6 v336 := smallByCut p55_54 w7
theorem b371 : Ban 29 6 v337 := smallByCut p55_54 w7
theorem b372 : Ban 29 6 v338 := smallByCut p55_54 w7
theorem b373 : Ban 12 4 v342 := checkedSmall
theorem b374 : Ban 12 4 v343 := checkedSmall
theorem b375 : Ban 12 4 v344 := checkedSmall
theorem b376 : Ban 12 4 v345 := checkedSmall
theorem b377 : Ban 12 4 v346 := checkedSmall
theorem b378 : Ban 12 4 v347 := checkedSmall
theorem b379 : Ban 12 4 v348 := checkedSmall
theorem b380 : Ban 12 4 v349 := checkedSmall
theorem b381 : Ban 12 4 v350 := checkedSmall
theorem b382 : Ban 12 4 v351 := checkedSmall
theorem b383 : Ban 12 4 v352 := checkedSmall
theorem b384 : Ban 12 4 v353 := checkedSmall
theorem b385 : Ban 12 4 v354 := checkedSmall
theorem b386 : Ban 12 4 v355 := checkedSmall
theorem b387 : Ban 12 4 v356 := checkedSmall
theorem b388 : Ban 12 4 v357 := checkedSmall
theorem b389 : Ban 12 4 v358 := checkedSmall
theorem b390 : Ban 12 4 v359 := checkedSmall
theorem b391 : Ban 12 4 v360 := checkedSmall
theorem b392 : Ban 12 4 v361 := checkedSmall
theorem b393 : Ban 12 4 v362 := checkedSmall
theorem b394 : Ban 12 4 v363 := checkedSmall
theorem b395 : Ban 12 4 v364 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b396 : Ban 12 5 v65 := viaBranch (ws := [v342,v343,v344,v345,v346,v347,v348,v349,v350,v351,v352,v353,v354,v66,v355,v356,v357,v358,v359,v360,v361,v362,v363,v364]) (consBan b373 (consBan b374 (consBan b375 (consBan b376 (consBan b377 (consBan b378 (consBan b379 (consBan b380 (consBan b381 (consBan b382 (consBan b383 (consBan b384 (consBan b385 (consBan b66 (consBan b386 (consBan b387 (consBan b388 (consBan b389 (consBan b390 (consBan b391 (consBan b392 (consBan b393 (consBan b394 (consBan b395 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b397 : Ban 12 5 v341 := viaPerm map51_3 map51_4 b396 (by decide +kernel) (by decide +kernel)
theorem b402 : Ban 12 4 v370 := checkedSmall
theorem b403 : Ban 12 4 v371 := checkedSmall
theorem b404 : Ban 12 4 v372 := checkedSmall
theorem b405 : Ban 12 4 v373 := checkedSmall
theorem b406 : Ban 12 4 v374 := checkedSmall
theorem b407 : Ban 12 4 v375 := checkedSmall
theorem b408 : Ban 12 4 v376 := checkedSmall
theorem b409 : Ban 12 4 v377 := checkedSmall
theorem b410 : Ban 12 4 v378 := checkedSmall
theorem b411 : Ban 12 4 v379 := checkedSmall
theorem b412 : Ban 12 4 v380 := checkedSmall
theorem b413 : Ban 12 4 v381 := checkedSmall
theorem b414 : Ban 12 4 v382 := checkedSmall
theorem b415 : Ban 12 4 v383 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b416 : Ban 12 5 v66 := viaBranch (ws := [v62,v370,v63,v371,v372,v373,v374,v375,v356,v355,v376,v377,v378,v379,v380,v381,v382,v383]) (consBan b62 (consBan b402 (consBan b63 (consBan b403 (consBan b404 (consBan b405 (consBan b406 (consBan b407 (consBan b387 (consBan b386 (consBan b408 (consBan b409 (consBan b410 (consBan b411 (consBan b412 (consBan b413 (consBan b414 (consBan b415 (nilBan 12 4))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b417 : Ban 12 5 v369 := viaPerm map51_16 map51_16 b416 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w9 : Wide 12 5 v369 := viaSub (ws := [v341,v369]) (consBan b397 (consBan b417 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b398 : Ban 29 6 v340 := smallByCut p55_53 w9
theorem b399 : Ban 29 6 v339 := viaPerm map55_6 map55_8 b398 (by decide +kernel) (by decide +kernel)
theorem b401 : Ban 29 6 v365 := smallByCut p55_54 w7
theorem b418 : Ban 29 6 v368 := smallByCut p55_53 w9
theorem b419 : Ban 29 6 v367 := viaPerm map55_6 map55_8 b418 (by decide +kernel) (by decide +kernel)
theorem b420 : Ban 29 6 v384 := smallByCut p55_54 w7
theorem b421 : Ban 29 6 v385 := smallByCut p55_51 w7
theorem b422 : Ban 29 6 v386 := smallByCut p55_51 w7
theorem b423 : Ban 29 6 v387 := smallByCut p55_51 w7
theorem b424 : Ban 29 6 v388 := smallByCut p55_51 w7
theorem b425 : Ban 29 6 v389 := smallByCut p55_39 w10
theorem b426 : Ban 29 6 v390 := smallByCut p55_53 w7
theorem b427 : Ban 29 6 v391 := smallByCut p55_53 w7
theorem b428 : Ban 29 6 v392 := smallByCut p55_39 w10
theorem b429 : Ban 29 6 v393 := smallByCut p55_53 w7
theorem b430 : Ban 29 6 v394 := smallByCut p55_53 w7
theorem b431 : Ban 29 6 v395 := smallByCut p55_53 w7
theorem b432 : Ban 29 6 v396 := smallByCut p55_53 w7
theorem b433 : Ban 29 6 v397 := smallByCut p55_53 w7
theorem b434 : Ban 29 6 v398 := smallByCut p55_53 w7
theorem b435 : Ban 29 6 v399 := smallByCut p55_53 w7
theorem b436 : Ban 29 6 v400 := smallByCut p55_53 w7
theorem b437 : Ban 29 6 v401 := smallByCut p55_53 w7
theorem b438 : Ban 29 6 v402 := smallByCut p55_53 w7
theorem b439 : Ban 29 6 v403 := smallByCut p55_53 w7
theorem b440 : Ban 29 6 v404 := smallByCut p55_53 w7
theorem b441 : Ban 29 6 v405 := smallByCut p55_51 w9
theorem b442 : Ban 29 6 v406 := smallByCut p55_53 w7
theorem b443 : Ban 29 6 v407 := smallByCut p55_51 w9
theorem b444 : Ban 29 6 v408 := smallByCut p55_53 w7
theorem b445 : Ban 29 6 v409 := smallByCut p55_39 w10
theorem b446 : Ban 29 6 v410 := smallByCut p55_51 w7
theorem b447 : Ban 29 6 v411 := smallByCut p55_51 w7
theorem b448 : Ban 29 6 v412 := smallByCut p55_39 w10
theorem b449 : Ban 29 6 v413 := smallByCut p55_51 w7
theorem b450 : Ban 29 6 v414 := smallByCut p55_51 w7
theorem b451 : Ban 29 6 v415 := smallByCut p55_51 w7
theorem b452 : Ban 29 6 v416 := smallByCut p55_51 w7
theorem b453 : Ban 29 6 v417 := smallByCut p55_51 w7
theorem b454 : Ban 29 6 v418 := smallByCut p55_51 w7
theorem b455 : Ban 29 6 v419 := smallByCut p55_51 w7
theorem b456 : Ban 29 6 v420 := smallByCut p55_51 w7
theorem b457 : Ban 29 6 v421 := smallByCut p55_51 w7
theorem b458 : Ban 29 6 v422 := smallByCut p55_51 w7
theorem b459 : Ban 29 6 v423 := smallByCut p55_51 w7
theorem b460 : Ban 29 6 v424 := smallByCut p55_51 w7
theorem b400 : Ban 29 6 v366 := smallByCut p55_51 w7
theorem b461 : Ban 29 6 v425 := smallByCut p55_51 w7
theorem b463 : Ban 29 6 v426 := smallByCut p55_39 w10
theorem b464 : Ban 29 6 v428 := smallByCut p55_39 w10
theorem b465 : Ban 29 6 v429 := viaPerm map55_1 map55_1 b463 (by decide +kernel) (by decide +kernel)
theorem b466 : Ban 29 6 v430 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b467 : Ban 29 7 v314 := viaBranch (ws := [v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v325,v326,v327,v328,v329,v330,v331,v332,v333,v334,v335,v336,v337,v338,v339,v365,v367,v384,v385,v386,v387,v388,v389,v390,v391,v392,v393,v394,v395,v396,v397,v398,v399,v400,v401,v402,v403,v404,v405,v406,v407,v408,v409,v410,v411,v412,v413,v414,v415,v416,v417,v418,v419,v420,v421,v422,v423,v424,v340,v366,v368,v425,v185,v311,v312,v313,v426,v428,v429,v430,v183,v180]) (consBan b349 (consBan b350 (consBan b351 (consBan b352 (consBan b353 (consBan b354 (consBan b355 (consBan b356 (consBan b357 (consBan b358 (consBan b359 (consBan b360 (consBan b361 (consBan b362 (consBan b363 (consBan b364 (consBan b365 (consBan b366 (consBan b367 (consBan b368 (consBan b369 (consBan b370 (consBan b371 (consBan b372 (consBan b399 (consBan b401 (consBan b419 (consBan b420 (consBan b421 (consBan b422 (consBan b423 (consBan b424 (consBan b425 (consBan b426 (consBan b427 (consBan b428 (consBan b429 (consBan b430 (consBan b431 (consBan b432 (consBan b433 (consBan b434 (consBan b435 (consBan b436 (consBan b437 (consBan b438 (consBan b439 (consBan b440 (consBan b441 (consBan b442 (consBan b443 (consBan b444 (consBan b445 (consBan b446 (consBan b447 (consBan b448 (consBan b449 (consBan b450 (consBan b451 (consBan b452 (consBan b453 (consBan b454 (consBan b455 (consBan b456 (consBan b457 (consBan b458 (consBan b459 (consBan b460 (consBan b398 (consBan b400 (consBan b418 (consBan b461 (consBan b343 (consBan b344 (consBan b345 (consBan b346 (consBan b463 (consBan b464 (consBan b465 (consBan b466 (consBan b206 (consBan b203 (nilBan 29 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b468 : Ban 29 7 v180 := smallByCut p55_4119 w5
theorem b469 : Ban 29 7 v183 := viaPerm map55_1 map55_1 b468 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b470 : Ban 29 8 v0 := viaBranch (ws := [v1,v27,v84,v86,v87,v88,v85,v89,v90,v92,v93,v95,v97,v98,v94,v99,v100,v101,v102,v103,v91,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v96,v114,v115,v116,v117,v118,v314,v180,v183]) (consBan b25 (consBan b107 (consBan b109 (consBan b110 (consBan b111 (consBan b112 (consBan b108 (consBan b113 (consBan b115 (consBan b116 (consBan b118 (consBan b120 (consBan b121 (consBan b122 (consBan b117 (consBan b123 (consBan b124 (consBan b125 (consBan b126 (consBan b127 (consBan b114 (consBan b128 (consBan b129 (consBan b130 (consBan b131 (consBan b132 (consBan b133 (consBan b134 (consBan b135 (consBan b136 (consBan b137 (consBan b119 (consBan b138 (consBan b139 (consBan b140 (consBan b141 (consBan b347 (consBan b467 (consBan b468 (consBan b469 (nilBan 29 7))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem verifiedPin : Wide 29 8 v0 := widen (by decide +kernel) b470
end PEqualNP.Outside.L_meta_12374.Support

namespace PEqualNP.Outside.L_meta_12374.Data
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12374.Support
def target (x : Fin 6 → Bool) := Nat.testBit (4278124264 * 2 ^ 32 + 4276682240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def posBits : ℕ := 0x274d34cb2cb1c719e69a69659638e35d65965555534d3
def negBits : ℕ := 0x70914c224b08511e48869211628431d4486511152443
def sample (bank : ℕ) (i : Fin 30) (j : Fin 6) := bank.testBit (6*i.val+j.val)
def inputs : List ℕ := [0x80e1b86e078fe3f,0x62c5b1438f1fc7,0x30368da1c0fe3f8,0x20000000,0x5b4006d9ff003ff,0x6d9b6001ffffc00]
def seeds : List Wire := [(false,0x80e1b86e078fe3f),(false,0x62c5b1438f1fc7),(false,0x30368da1c0fe3f8),(false,0x20000000),(false,0x5b4006d9ff003ff),(false,0x6d9b6001ffffc00)]
set_option maxHeartbeats 10000000 in
theorem listed : ∀ i : Fin 30, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (30+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 30, target (sample posBits i)=true ∧ target (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 30, ∀ b∈inputs, b.testBit i.val≠b.testBit (30+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 30 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 6 C=target) :
    ∃ k≤C.gates.countP counted, Live 30 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 6 → Bool) : C.eval (List.ofFn x)=target x := congrFun eq x
  have good : Good 30 out.2 := by
    intro i hi same
    let j : Fin 30 := ⟨i,hi⟩
    have diff : read i out=read (30+i) out := by
      change (out.1 != out.2.testBit i) = (out.1 != out.2.testBit (30+i))
      rw [same]
    have p := ev i;have n := ev (30+i)
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
def restrictRows : Projection 30 29 := pick (List.range 29) (by decide) (by decide) (by decide)
set_option maxHeartbeats 8000000 in
theorem core_floor : Wide 29 8 restricted := verifiedPin
theorem six_floor : Ban 30 9 inputs := viaCut restrictRows core_floor (by decide) (by decide +kernel) (by decide +kernel)
def witness : Circuit := ⟨[⟨.and,[0,1]⟩, ⟨.or,[0,1]⟩, ⟨.or,[6,2]⟩, ⟨.and,[7,8]⟩, ⟨.or,[7,8]⟩, ⟨.and,[9,4]⟩, ⟨.or,[11,3]⟩, ⟨.or,[9,4]⟩, ⟨.and,[13,5]⟩, ⟨.or,[12,14]⟩, ⟨.and,[10,15]⟩],16⟩
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
end PEqualNP.Outside.L_meta_12374.Data

theorem PEqualNP.Outside.L_meta_12374 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124264 * 2 ^ 32 + 4276682240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124264 * 2 ^ 32 + 4276682240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_12374.Data.mono_enough
