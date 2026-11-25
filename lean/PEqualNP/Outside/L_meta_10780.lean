import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10780.Free

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

end PEqualNP.Outside.L_meta_10780.Free

namespace PEqualNP.Outside.L_meta_10780.Frame
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List ℕ := [0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6]
def target (x : Fin 7 → Bool) := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

def witness : List Gate := [
  ⟨.or, [0,1]⟩,
  ⟨.or, [1,2]⟩,
  ⟨.or, [3,5]⟩,
  ⟨.or, [4,5]⟩,
  ⟨.or, [0,6]⟩,
  ⟨.or, [5,6]⟩,
  ⟨.or, [4,7]⟩,
  ⟨.and, [8,10]⟩,
  ⟨.and, [9,11]⟩,
  ⟨.and, [12,13]⟩,
  ⟨.or, [14,15]⟩,
  ⟨.or, [16,17]⟩]

theorem good : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

theorem correct : ∀ x : Fin 7 → Bool, Circuit.eval ⟨witness,18⟩ (List.ofFn x) = target x := by
  decide +kernel

theorem finish (lower : ∀ (gs : List Gate) (o : ℕ), FanInTwo ⟨gs,o⟩ →
    (∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) →
    (∃ g ∈ gs, g.op = .not) → 12 ≤ gs.length) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o fan _ computes
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · exact ⟨witness, 18, good, lower gs o fan computes hn, correct⟩
  · refine ⟨gs, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨op, len⟩ := fan g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),len⟩

end PEqualNP.Outside.L_meta_10780.Frame

namespace PEqualNP.Outside.L_meta_10780.Cert
open PEqualNP.Outside.L_meta_10780.Free
inductive LookupTree
  | empty
  | fork (idx value : ℕ) (lo hi : LookupTree)
def LookupTree.run (f : ℕ → ℕ) : LookupTree → ℕ → ℕ
  | .empty, x => f x
  | .fork k v l r, x => if x < k then l.run f x else if x = k then v else r.run f x
def LookupTree.valid (f : ℕ → ℕ) : LookupTree → Bool
  | .empty => true
  | .fork k v l r => (f k == v) && l.valid f && r.valid f
set_option maxHeartbeats 0 in
theorem LookupTree.correct (f : ℕ → ℕ) (t : LookupTree) (h : t.valid f = true) (x : ℕ) :
    t.run f x = f x := by
  induction t with
  | empty => rfl
  | fork k v l r il ir =>
    simp only [LookupTree.valid, Bool.and_eq_true, beq_iff_eq] at h
    simp only [LookupTree.run]
    split
    · exact il h.1.2
    · split
      next e => subst x; exact h.1.1.symm
      next => exact ir h.2
def cached {m h : ℕ} (p : Projection m h) (t : LookupTree) (ok : t.valid p.toFun = true) :
    Projection m h := by
  refine ⟨t.run p.toFun, ?_⟩
  have same : t.run p.toFun = p.toFun := funext (t.correct _ ok)
  rw [same]
  exact p.property
def t0 : ℕ := 0x159802b30056600acc0159802b30056600acc0159802b30056600acc000000000000007ffff000000000000007ffff0000000003ffff80000
def t1 : ℕ := 0x4154082a81055020aa04154082a81055020aa04154082a81055020aa0000000000000000000ffffe00000000000000ffffe0000000007ffff
def t2 : ℕ := 0xe0001c0003800070000e0001c0003800070000e0001c00038000700000001ffffc00000000000001ffffc00000000000001fffffffff80000
def t3 : ℕ := 0x29e0053c00a78014f0029e0053c00a78014f0029e0053c00a78014f000000000003ffff800000000000000000000000000000000000007ffff
def t4 : ℕ := 0x3000060000c000180003000060000c000180003000060000c00018000ffffe0000000000000000001ffffffffffffffffffe00000000000000
def t5 : ℕ := 0x819e1033c2067840cf0819e1033c2067840cf0819e1033c2067840cf000000000000000000000000000003ffff8000000001ffffc000000000
def t6 : ℕ := 0xc000180003000060000c000180003000060000c000180003000060000fffffffffffffffffffffffe000000000000000000000000000000000
def t7 : ℕ := 0x1100022000440008800110002200044000880011000220004400088000000000000000000000000000000000000000000000000000000000
def t8 : ℕ := 0x1084210800f83ff
def t9 : ℕ := 0x210842101f07c1f
def t10 : ℕ := 0x42108423e007fe0
def t11 : ℕ := 0x84210843fff8000
def t12 : ℕ := 0x55dc0abb8157702aee055dc0abb8157702aee055dc0abb8157702aee000000000000007ffffffffe0000000007ffffffffe00003fffffffff
def t13 : ℕ := 0x404408088101102022040440808810110202204044080881011020220000000000000000000ffffe00000000000000ffffe0000000007ffff
def t14 : ℕ := 0x3ffff80000
def t15 : ℕ := 0x2220ff
def t16 : ℕ := 0x444f0f
def t17 : ℕ := 0x888ff0
def t18 : ℕ := 0xf5981eb303d6607acc0f5981eb303d6607acc0f5981eb303d6607acc00001ffffc00007ffff00001ffffc00007ffff00001fffffffff80000
def t19 : ℕ := 0x159802b30056600acc0159802b30056600acc0159802b30056600acc000000000000007ffff000000000000007ffff0000000000000000000
def t20 : ℕ := 0xe0001c0003800070000e0001c0003800070000e0001c00038000700000001ffffc00000000000001ffffc00000000000001ffffc000000000
def t21 : ℕ := 0x140002800050000a000140002800050000a000140002800050000a00000000000000000000000000000000000000000000000000000000000
def t22 : ℕ := 0x29f9853f30a7e614fcc29f9853f30a7e614fcc29f9853f30a7e614fcc0000000003fffffffff000000000000007ffff0000000003fffffffff
def t23 : ℕ := 0x1602c0580b016000ffe003ff800
def t24 : ℕ := 0x4508a11422845000001ffc007ff
def t25 : ℕ := 0xe01c0380700e07ff000003ff800
def t26 : ℕ := 0x298530a614c298000000000007ff
def t27 : ℕ := 0x300600c01803007fffffffc00000
def t28 : ℕ := 0x198003300066000cc00198003300066000cc00198003300066000cc000000000000007ffff000000000000007ffff0000000003ffff80000
def t29 : ℕ := 0x28a0051400a2801450028a0051400a2801450028a0051400a280145000000000003ffff800000000000000000000000000000000000007ffff
def t30 : ℕ := 0x7ffff0000000000000000000
def t31 : ℕ := 0x3159862b30c56618acc3159862b30c56618acc3159862b30c56618accffffe0000000007ffff00001ffffffffffffffffffe00003ffff80000
def t32 : ℕ := 0xb02c0b02c0b02c00000ffc00ffc00
def t33 : ℕ := 0x2b8ae2b8ae2b8ae00000ffffffffff
def t34 : ℕ := 0x4c1304c1304c130003ff00000003ff
def t35 : ℕ := 0x701c0701c0701c0ffc0000000ffc00
def t36 : ℕ := 0x802008020080200ffffffffff00000
def t37 : ℕ := 0x159802b30056600acc0159802b30056600acc0159802b30056600acc000000000000007ffff00000000000000000000000000003ffff80000
def t38 : ℕ := 0x3000060000c000180003000060000c000180003000060000c00018000ffffe0000000000000000001fffffffff80000ffffe00000000000000
def t39 : ℕ := 0x1180023000460008c001180023000460008c001180023000460008c0000000000000000000000000000000000000000000000000000000000
def t40 : ℕ := 0x81df903bf2077e40efc81df903bf2077e40efc81df903bf2077e40efc000000000000007ffff0000000003fffffffff00001fffffffff80000
def t41 : ℕ := 0x40000800010000200004000080001000020000400008000100002000000000000000000000000000000000000000000000000003ffff80000
def t42 : ℕ := 0xf5dc1ebb83d7707aee0f5dc1ebb83d7707aee0f5dc1ebb83d7707aee00001ffffc00007fffffffffffffc00007fffffffffffffffffffffff
def t43 : ℕ := 0x7b9ee7b9ee7b9eeffc00ffffffffff
def t44 : ℕ := 0x15dc02bb8057700aee015dc02bb8057700aee015dc02bb8057700aee000000000000007ffffffffe0000000007ffffffffe0000000007ffff
def t45 : ℕ := 0x1f
def t46 : ℕ := 0x318c63181ffffff
def t47 : ℕ := 0x1084210800f83e0
def t48 : ℕ := 0x210842101f07c00
def t49 : ℕ := 0x3e0
def t50 : ℕ := 0x5294a52be0fffff
def t51 : ℕ := 0x1084210800f801f
def t52 : ℕ := 0x42108423e007c00
def t53 : ℕ := 0xf8000
def t54 : ℕ := 0x94a5294bfff83ff
def t55 : ℕ := 0x1084210800003ff
def t56 : ℕ := 0x84210843ff00000
def t57 : ℕ := 0x7c00
def t58 : ℕ := 0x6318c633ff07fff
def t59 : ℕ := 0x210842101f0001f
def t60 : ℕ := 0x42108423e0003e0
def t61 : ℕ := 0x1f00000
def t62 : ℕ := 0xa5294a53ffffc1f
def t63 : ℕ := 0x210842100007c1f
def t64 : ℕ := 0x84210843e0f8000
def t65 : ℕ := 0x3e000000
def t66 : ℕ := 0xc6318c63fffffe0
def t67 : ℕ := 0x421084200007fe0
def t68 : ℕ := 0x842108401ff8000
def t69 : ℕ := 0x5294a52be0fffe0
def t70 : ℕ := 0x1084210800f8000
def t71 : ℕ := 0x94a5294bfff83e0
def t72 : ℕ := 0x1084210800003e0
def t73 : ℕ := 0x2220f0
def t74 : ℕ := 0xa000140002800050000a000140002800050000a0001400028000500000001ffffc00000000000001ffffc00000000000001ffffc000000000
def t75 : ℕ := 0x140002800050000a000140002800050000a000140002800050000a0000000000000000000000000000000000000000000000000000007ffff
def t76 : ℕ := 0x2dfdc5bfb8b7f716fee2dfdc5bfb8b7f716fee2dfdc5bfb8b7f716fee0000000003fffffffffffffe0000000007ffffffffe00003fffffffff
def t77 : ℕ := 0x41dc083b81077020ee041dc083b81077020ee041dc083b81077020ee000000000000007ffffffffe0000000007ffffffffe00003ffff80000
def t78 : ℕ := 0x28a0051400a2801450028a0051400a2801450028a0051400a280145000000000003ffff8000000000000000000000000000000000000000000
def t79 : ℕ := 0x7ffffffffe00000000000000
def t80 : ℕ := 0x355dc6abb8d5771aaee355dc6abb8d5771aaee355dc6abb8d5771aaeeffffe0000000007fffffffffffffffffffffffffffe00003fffffffff
def t81 : ℕ := 0x55dc0abb8157702aee055dc0abb8157702aee055dc0abb8157702aee000000000000007ffffffffe000000000000000000000003fffffffff
def t82 : ℕ := 0x3000060000c000180003000060000c000180003000060000c00018000ffffe0000000000000000001fffffffff800000000000000000000000
def t83 : ℕ := 0x15d802bb0057600aec015d802bb0057600aec015d802bb0057600aec000000000000007ffff000000000000007ffff0000000003ffff80000
def t84 : ℕ := 0x85dfd0bbfa177f42efe85dfd0bbfa177f42efe85dfd0bbfa177f42efe000000000000007ffffffffe00003ffffffffffffffffffffffffffff
def t85 : ℕ := 0x400408008100102002040040800810010200204004080081001020020000000000000000000ffffe00000000000000ffffe0000000007ffff
def t86 : ℕ := 0x80821010420208404108082101042020840410808210104202084041000000000000000000000000000003ffff8000000001ffffc000000000
def t87 : ℕ := 0x7ffffffffe000000000000000000000000000000000
def t88 : ℕ := 0xc55dd8abbb157762aeec55dd8abbb157762aeec55dd8abbb157762aeefffffffffffffffffffffffe0000000007ffffffffe00003fffffffff
def t89 : ℕ := 0x55dc0abb8157702aee055dc0abb8157702aee055dc0abb8157702aee0000000000000000000000000000000007ffffffffe00003fffffffff
def t90 : ℕ := 0xc000180003000060000c000180003000060000c000180003000060000ffffffffffffff8000000000000000000000000000000000000000000
def t91 : ℕ := 0x80001000020000400008000100002000040000800010000200004000000000000000000000000000000000000000000000000000000000000
def t92 : ℕ := 0x2fe005fc00bf8017f002fe005fc00bf8017f002fe005fc00bf8017f0000001fffffffff8000000001ffffc00000000000001ffffffffffffff
def t93 : ℕ := 0x570ae15c2b857000fffffffffff
def t94 : ℕ := 0x2f85f0be17c2f87ff000003fffff
def t95 : ℕ := 0x4108210420841000001ffc007ff
def t96 : ℕ := 0x4120801ff
def t97 : ℕ := 0x572bbffff
def t98 : ℕ := 0xe0703fe00
def t99 : ℕ := 0xf87c3ffff
def t100 : ℕ := 0x3ff800
def t101 : ℕ := 0x12121200ffff
def t102 : ℕ := 0x383838ff0000
def t103 : ℕ := 0xbcbcbcff00ff
def t104 : ℕ := 0xc0c0c0ffff00
def t105 : ℕ := 0xf61ec3d87b0f67ffffe003ff800
def t106 : ℕ := 0x1602c0580b016000ffe00000000
def t107 : ℕ := 0xe01c0380700e07ff00000000000
def t108 : ℕ := 0x1002004008010000000003ff800
def t109 : ℕ := 0x10083fe00
def t110 : ℕ := 0x2fe5fcbf97f2fe7ffffe003fffff
def t111 : ℕ := 0x160b3fe00
def t112 : ℕ := 0xfe7f3ffff
def t113 : ℕ := 0x600c01803006000ffe00000000
def t114 : ℕ := 0x2e85d0ba1742e87ff000000007ff
def t115 : ℕ := 0xffe00000000
def t116 : ℕ := 0x31662cc598b3167ffffffffff800
def t117 : ℕ := 0x1602c0580b016000000003ff800
def t118 : ℕ := 0x300600c01803007ff001ffc00000
def t119 : ℕ := 0x4008010020040000000003ff800
def t120 : ℕ := 0x40203fe00
def t121 : ℕ := 0xf71ee3dc7b8f77fffffffffffff
def t122 : ℕ := 0xf77bbffff
def t123 : ℕ := 0x1702e05c0b817000fffffc007ff
def t124 : ℕ := 0xa0140280500a07ff00000000000
def t125 : ℕ := 0xa05000000
def t126 : ℕ := 0x500a014028050000000003fffff
def t127 : ℕ := 0x2ff5febfd7faff7fffffffffffff
def t128 : ℕ := 0xff7fbffff
def t129 : ℕ := 0x700e01c03807000fffffc00000
def t130 : ℕ := 0x70380000
def t131 : ℕ := 0x2a8550aa1542a87ff00000000000
def t132 : ℕ := 0xa85400000
def t133 : ℕ := 0xfffffc00000
def t134 : ℕ := 0x3576aed5dabb577fffffffffffff
def t135 : ℕ := 0x570ae15c2b857000000003fffff
def t136 : ℕ := 0x300600c01803007ff00000000000
def t137 : ℕ := 0x2184308610c218000000000007ff
def t138 : ℕ := 0x180c001ff
def t139 : ℕ := 0x7ff00000000000
def t140 : ℕ := 0x3e07c0f81f03e07ffffffffff800
def t141 : ℕ := 0xe01c0380700e0000000003ff800
def t142 : ℕ := 0x300600c0180300000fffffc00000
def t143 : ℕ := 0x200400801002007ff00000000000
def t144 : ℕ := 0x3f87f0fe1fc3f87fffffffffffff
def t145 : ℕ := 0xf81f03e07c0f8000000003fffff
def t146 : ℕ := 0x10020040080100000fffffc00000
def t147 : ℕ := 0x60000c000180003000060000c000180003000060000c00018000300000001ffffc00000000000001ffffc00000000000001fffffffff80000
def t148 : ℕ := 0x21e0043c00878010f0021e0043c00878010f0021e0043c00878010f000000000003ffff800000000000000000000000000000000000007ffff
def t149 : ℕ := 0x1ffffc0000000000000000000000000000
def t150 : ℕ := 0x3e0007c000f8001f0003e0007c000f8001f0003e0007c000f8001f000fffffffffc00000000000001ffffffffffffffffffffffffffff80000
def t151 : ℕ := 0xe0001c0003800070000e0001c0003800070000e0001c00038000700000001ffffc000000000000000000000000000000001fffffffff80000
def t152 : ℕ := 0x3000060000c000180003000060000c000180003000060000c00018000ffffe000000000000000000000003fffffffffffffe00000000000000
def t153 : ℕ := 0x1fffffffff80000
def t154 : ℕ := 0x8fdf91fbf23f7e47efc8fdf91fbf23f7e47efc8fdf91fbf23f7e47efc00001ffffc00007ffff00001ffffffffffffff00001fffffffff80000
def t155 : ℕ := 0xe0001c0003800070000e0001c0003800070000e0001c00038000700000001ffffc00000000000001ffffc0000000000000000000000000000
def t156 : ℕ := 0x81df903bf2077e40efc81df903bf2077e40efc81df903bf2077e40efc000000000000007ffff0000000003fffffffff0000000000000000000
def t157 : ℕ := 0x1ffffc00000000000000000000000000000000000000000000000
def t158 : ℕ := 0xce0019c003380067000ce0019c003380067000ce0019c003380067000ffffffffffffffffffffffffffffc00000000000001fffffffff80000
def t159 : ℕ := 0xe0001c0003800070000e0001c0003800070000e0001c000380007000000000000000000000000001ffffc00000000000001fffffffff80000
def t160 : ℕ := 0xc000180003000060000c000180003000060000c000180003000060000ffffe00003fffffffffffffe000000000000000000000000000000000
def t161 : ℕ := 0x200004000080001000020000400008000100002000040000800010000000000000000000000000000000000000000000000000000000000000
def t162 : ℕ := 0x39e0073c00e7801cf0039e0073c00e7801cf0039e0073c00e7801cf00ffffe00003ffff8000000001ffffffffffffffffffe0000000007ffff
def t163 : ℕ := 0x9e0013c00278004f0009e0013c00278004f0009e0013c00278004f000000000003ffff800000000000000000000000000000000000007ffff
def t164 : ℕ := 0x100002000040000800010000200004000080001000020000400008000ffffe0000000000000000001ffffffffffffffffffe00000000000000
def t165 : ℕ := 0x1c0003800070000e0001c0003800070000e0001c0003800070000e00000000000000000000000000000000000000000000000000000000000
def t166 : ℕ := 0xa9ff953ff2a7fe54ffca9ff953ff2a7fe54ffca9ff953ff2a7fe54ffc0000000003fffffffff0000000003fffffffff00001ffffffffffffff
def t167 : ℕ := 0x29e53ca794f29e000ffe003fffff
def t168 : ℕ := 0x2820050400a080141002820050400a080141002820050400a080141000000000003ffff800000000000000000000000000000000000007ffff
def t169 : ℕ := 0x801f9003f2007e400fc801f9003f2007e400fc801f9003f2007e400fc000000000000007ffff0000000003fffffffff00001fffffffff80000
def t170 : ℕ := 0x3ffff8000000000000000000000000000000000000000000
def t171 : ℕ := 0xe9e01d3c03a78074f00e9e01d3c03a78074f00e9e01d3c03a78074f00fffffffffffffffffffffffe00000000000000000000000000007ffff
def t172 : ℕ := 0x29e0053c00a78014f0029e0053c00a78014f0029e0053c00a78014f0000000000000000000000000000000000000000000000000000007ffff
def t173 : ℕ := 0xc000180003000060000c000180003000060000c000180003000060000fffffffffc00007ffffffffe000000000000000000000000000000000
def t174 : ℕ := 0x3fffffffff0000000000000000000
def t175 : ℕ := 0xb1df963bf2c77e58efcb1df963bf2c77e58efcb1df963bf2c77e58efcffffe0000000007ffff00001ffffffffffffffffffffffffffff80000
def t176 : ℕ := 0x3000060000c000180003000060000c000180003000060000c00018000ffffe0000000000000000001ffffc000000000ffffe00000000000000
def t177 : ℕ := 0x81df903bf2077e40efc81df903bf2077e40efc81df903bf2077e40efc000000000000007ffff000000000000000000000001fffffffff80000
def t178 : ℕ := 0xffffe0000000000000000000000000000000000000000000000000000
def t179 : ℕ := 0xf0001e0003c00078000f0001e0003c00078000f0001e0003c00078000ffffffffffffffffffffffffffffffffffffffffffe00000000000000
def t180 : ℕ := 0x3000060000c000180003000060000c000180003000060000c00018000000000000000000000000001ffffffffffffffffffe00000000000000
def t181 : ℕ := 0xc000180003000060000c000180003000060000c00018000300006000000001ffffffffffffffffffe000000000000000000000000000000000
def t182 : ℕ := 0x800010000200004000080001000020000400008000100002000040000000000000000007ffff00000000000000000000000000000000000000
def t183 : ℕ := 0xc1df983bf3077e60efcc1df983bf3077e60efcc1df983bf3077e60efcfffffffffffffffffffffffe00003fffffffff00001fffffffff80000
def t184 : ℕ := 0x1df803bf0077e00efc01df803bf0077e00efc01df803bf0077e00efc00000000000000000000000000003fffffffff00001fffffffff80000
def t185 : ℕ := 0x400008000100002000040000800010000200004000080001000020000ffffffffffffff80000ffffe000000000000000000000000000000000
def t186 : ℕ := 0x4180083001060020c004180083001060020c004180083001060020c000000000000007ffff000000000000007ffff0000000003ffff80000
def t187 : ℕ := 0x80861010c202184043080861010c202184043080861010c202184043000000000000000000000000000003ffff8000000001ffffc000000000
def t188 : ℕ := 0x7ffff00000000000000000000000000000000000000
def t189 : ℕ := 0xc159982b33056660accc159982b33056660accc159982b33056660accfffffffffffffffffffffffe0000000007ffff0000000003ffff80000
def t190 : ℕ := 0x159802b30056600acc0159802b30056600acc0159802b30056600acc0000000000000000000000000000000007ffff0000000003ffff80000
def t191 : ℕ := 0xc000180003000060000c000180003000060000c000180003000060000ffffffffffffff80000ffffe000000000000000000000000000000000
def t192 : ℕ := 0x11c0023800470008e0011c0023800470008e0011c0023800470008e0000000000000000000000000000000000000000000000000000000000
def t193 : ℕ := 0x1202404809012000ffe003ff800
def t194 : ℕ := 0x400801002004000000000000000
def t195 : ℕ := 0xe51ca394728e57ff001ffffffff
def t196 : ℕ := 0x500a01402805000001ffc007ff
def t197 : ℕ := 0xa0140280500a07ff000003ff800
def t198 : ℕ := 0x7ff
def t199 : ℕ := 0x2dd5bab756eadd000001ffc007ff
def t200 : ℕ := 0x4508a11422845000001ffc00000
def t201 : ℕ := 0x298530a614c29800000000000000
def t202 : ℕ := 0x1ffc00000
def t203 : ℕ := 0x34568ad15a2b457fffffffc007ff
def t204 : ℕ := 0x5cb972e01fffff
def t205 : ℕ := 0x60c1830fe0007f
def t206 : ℕ := 0x8102040fffff80
def t207 : ℕ := 0xd5ab56afffff80
def t208 : ℕ := 0x4508a11422845000000000007ff
def t209 : ℕ := 0x300600c01803007ffffe00000000
def t210 : ℕ := 0x444f00
def t211 : ℕ := 0x1002004008010000000000007ff
def t212 : ℕ := 0x2df5beb7d6fadf000fffffffffff
def t213 : ℕ := 0x4708e11c23847000ffffffff800
def t214 : ℕ := 0x288510a214428800000000000000
def t215 : ℕ := 0x4522801ff
def t216 : ℕ := 0x984c001ff
def t217 : ℕ := 0x22200f
def t218 : ℕ := 0x801002004008000000000000000
def t219 : ℕ := 0x600c0180300607ff000003ff800
def t220 : ℕ := 0x54a952a0003f80
def t221 : ℕ := 0xe1c3870fffffff
def t222 : ℕ := 0x44400f
def t223 : ℕ := 0x2004008010020000000000000000
def t224 : ℕ := 0x398730e61cc3987fffffffc007ff
def t225 : ℕ := 0x981302604c098000000000007ff
def t226 : ℕ := 0x100200400801007fffffffc00000
def t227 : ℕ := 0x441c0883811070220e0441c0883811070220e0441c0883811070220e000000000000007ffffffffe0000000007ffffffffe00003fffffffff
def t228 : ℕ := 0x1ffffc000000000
def t229 : ℕ := 0x8f9e11f3c23e7847cf08f9e11f3c23e7847cf08f9e11f3c23e7847cf000001ffffc00000000000001fffffffff8000000001fffffffff80000
def t230 : ℕ := 0xe0001c0003800070000e0001c0003800070000e0001c00038000700000001ffffc00000000000001ffffc0000000000000000003ffff80000
def t231 : ℕ := 0x819e1033c2067840cf0819e1033c2067840cf0819e1033c2067840cf000000000000000000000000000003ffff800000000000000000000000
def t232 : ℕ := 0x180003000060000c000180003000060000c000180003000060000c00000000000000000000000000000000000000000000000000000000000
def t233 : ℕ := 0xa9fe153fc2a7f854ff0a9fe153fc2a7f854ff0a9fe153fc2a7f854ff00000000003ffff800000000000003ffff8000000001ffffc00007ffff
def t234 : ℕ := 0x2860050c00a180143002860050c00a180143002860050c00a180143000000000003ffff800000000000000000000000000000000000007ffff
def t235 : ℕ := 0x801e1003c20078400f0801e1003c20078400f0801e1003c20078400f000000000000000000000000000003ffff8000000001ffffc000000000
def t236 : ℕ := 0x3ffff800000000000000000000000
def t237 : ℕ := 0xb19e1633c2c67858cf0b19e1633c2c67858cf0b19e1633c2c67858cf0ffffe0000000000000000001fffffffffffffffffffffffc000000000
def t238 : ℕ := 0x3000060000c000180003000060000c000180003000060000c00018000ffffe0000000000000000001ffffc00007ffffffffe00000000000000
def t239 : ℕ := 0x819e1033c2067840cf0819e1033c2067840cf0819e1033c2067840cf00000000000000000000000000000000000000000001ffffc000000000
def t240 : ℕ := 0x800010000200004000080001000020000400008000100002000040000000000000000000000000000000000000000000000000000000000000
def t241 : ℕ := 0xc19e1833c3067860cf0c19e1833c3067860cf0c19e1833c3067860cf0fffffffffffffffffffffffe00003ffff8000000001ffffc000000000
def t242 : ℕ := 0x19e0033c0067800cf0019e0033c0067800cf0019e0033c0067800cf000000000000000000000000000003ffff8000000001ffffc000000000
def t243 : ℕ := 0x400008000100002000040000800010000200004000080001000020000fffffffffffffffffffffffe000000000000000000000000000000000
def t244 : ℕ := 0x148802910052200a440148802910052200a440148802910052200a44000000000000007ffff000000000000007ffff0000000003ffff80000
def t245 : ℕ := 0x280a0280a0280a00000ffc00fffff
def t246 : ℕ := 0x2c0b02c0b02c0b0003ff00000003ff
def t247 : ℕ := 0x300c0300c0300c0ffc00003ffffc00
def t248 : ℕ := 0x8b22c8b22c8b22c00000003ff00000
def t249 : ℕ := 0xc0300c0300c0300fffffffc0000000
def t250 : ℕ := 0x40000800010000200004000080001000020000400008000100002000000000000000000000000000000000000000000000000000000000000
def t251 : ℕ := 0xe1541c2a83855070aa0e1541c2a83855070aa0e1541c2a83855070aa00001ffffc000000000fffffffffc000000000fffffffffffffffffff
def t252 : ℕ := 0x154002a80055000aa00154002a80055000aa00154002a80055000aa0000000000000000000ffffe00000000000000ffffe0000000007ffff
def t253 : ℕ := 0xa000140002800050000a000140002800050000a0001400028000500000001ffffc00000000000001ffffc00000000000001fffffffff80000
def t254 : ℕ := 0x110002200044000880011000220004400088001100022000440008800000000000000000000000000000000000000000000000000007ffff
def t255 : ℕ := 0x404408088101102022040440808810110202204044080881011020220000000000000000000ffffe00000000000000ffffe00000000000000
def t256 : ℕ := 0x29e8853d10a7a214f4429e8853d10a7a214f4429e8853d10a7a214f440000000003fffffffff000000000000007ffff0000000003ffff80000
def t257 : ℕ := 0xffffe00000000000000
def t258 : ℕ := 0x34154682a8d0551a0aa34154682a8d0551a0aa34154682a8d0551a0aaffffe00000000000000fffffffffffffffffffffffe0000000007ffff
def t259 : ℕ := 0x4154082a81055020aa04154082a81055020aa04154082a81055020aa0000000000000000000ffffe00000000000000000000000000007ffff
def t260 : ℕ := 0x3000060000c000180003000060000c000180003000060000c00018000ffffe0000000000000000001ffffffffffffff0000000000000000000
def t261 : ℕ := 0x150002a00054000a800150002a00054000a800150002a00054000a8000000000000000000000000000000000000000000000000000000000
def t262 : ℕ := 0x4f13c4f13c4f13c003ffffc00fffff
def t263 : ℕ := 0x81ca903952072a40e5481ca903952072a40e5481ca903952072a40e54000000000000007ffff0000000003fffffffff00001fffffffff80000
def t264 : ℕ := 0xffffe000000000000000000000000000000000
def t265 : ℕ := 0xc4155882ab1055620aac4155882ab1055620aac4155882ab1055620aafffffffffffffffffffffffe00000000000000ffffe0000000007ffff
def t266 : ℕ := 0x4154082a81055020aa04154082a81055020aa04154082a81055020aa00000000000000000000000000000000000000ffffe0000000007ffff
def t267 : ℕ := 0xc000180003000060000c000180003000060000c000180003000060000fffffffffffffffffff00000000000000000000000000000000000000
def t268 : ℕ := 0x80001000020000400008000100002000040000800010000200004000000000000000000000000000000000000000000000000003ffff80000
def t269 : ℕ := 0x2ff985ff30bfe617fcc2ff985ff30bfe617fcc2ff985ff30bfe617fcc00001ffffffffffffff00001ffffc00007ffff00001ffffffffffffff
def t270 : ℕ := 0x60000c000180003000060000c000180003000060000c00018000300000001ffffc00000000000001ffffc00000000000001ffffc000000000
def t271 : ℕ := 0x21f9843f3087e610fcc21f9843f3087e610fcc21f9843f3087e610fcc0000000003fffffffff000000000000007ffff000000000000007ffff
def t272 : ℕ := 0x2000040000800010000200004000080001000020000400008000100000000000000000000000000000000000007ffff0000000000000000000
def t273 : ℕ := 0x39f9873f30e7e61cfcc39f9873f30e7e61cfcc39f9873f30e7e61cfccffffe00003fffffffff00001ffffffffffffffffffe00003fffffffff
def t274 : ℕ := 0x39e73ce79cf39e7fffffffffffff
def t275 : ℕ := 0x40080100200400000000000000
def t276 : ℕ := 0xa0a0a00ffff
def t277 : ℕ := 0x303030ff00ff
def t278 : ℕ := 0xeeeeeeffffff
def t279 : ℕ := 0x2c2c2cff0000
def t280 : ℕ := 0xfcfcfcffffff
def t281 : ℕ := 0x9e4f3ffff
def t282 : ℕ := 0x388710e21c43887ff001ffc007ff
def t283 : ℕ := 0xe4e4e4ff0000
def t284 : ℕ := 0xe572bffff
def t285 : ℕ := 0x5281f
def t286 : ℕ := 0x633e0
def t287 : ℕ := 0xd6bff
def t288 : ℕ := 0xe73ff
def t289 : ℕ := 0x400801002004000001ffc007ff
def t290 : ℕ := 0x3df7bef7defbdf7fffffffffffff
def t291 : ℕ := 0x410821042084100000000000000
def t292 : ℕ := 0x39a734e69cd39a7ffffe003ff800
def t293 : ℕ := 0x80100200400807ff000003ff800
def t294 : ℕ := 0x3fe7fcff9ff3fe7fffffffffffff
def t295 : ℕ := 0x600c01803006000000000000000
def t296 : ℕ := 0x31e63cc798f31e000fffffc007ff
def t297 : ℕ := 0x9e13c2784f09e000000003fffff
def t298 : ℕ := 0x2e2e2e0000ff
def t299 : ℕ := 0x9f9813f3027e604fcc09f9813f3027e604fcc09f9813f3027e604fcc0000000003fffffffff00000000000000000000000000003fffffffff
def t300 : ℕ := 0x100002000040000800010000200004000080001000020000400008000ffffe0000000000000000001fffffffff80000ffffe00000000000000
def t301 : ℕ := 0x1d9803b30076600ecc01d9803b30076600ecc01d9803b30076600ecc000000000000007ffff000000000000007ffff0000000003ffff80000
def t302 : ℕ := 0x80061000c200184003080061000c200184003080061000c200184003000000000000000000000000000003ffff8000000001ffffc000000000
def t303 : ℕ := 0x3fffffffff00000000000000000000000000000000000000
def t304 : ℕ := 0xe9f99d3f33a7e674fcce9f99d3f33a7e674fcce9f99d3f33a7e674fccfffffffffffffffffffffffe0000000007ffff0000000003fffffffff
def t305 : ℕ := 0x29f9853f30a7e614fcc29f9853f30a7e614fcc29f9853f30a7e614fcc0000000000000000000000000000000007ffff0000000003fffffffff
def t306 : ℕ := 0xc000180003000060000c000180003000060000c000180003000060000fffffffffc000000000ffffe000000000000000000000000000000000
def t307 : ℕ := 0x140002800050000a000140002800050000a000140002800050000a0000000000000000000000000000000000000000000000000000000000
def t308 : ℕ := 0x859f50b3ea167d42cfa859f50b3ea167d42cfa859f50b3ea167d42cfa0000000000000000000ffffe00003ffff80000fffffffffc00007ffff
def t309 : ℕ := 0x40140802810050200a040140802810050200a040140802810050200a0000000000000000000ffffe00000000000000ffffe0000000007ffff
def t310 : ℕ := 0x818a103142062840c50818a103142062840c50818a103142062840c5000000000000000000000000000003ffff8000000001ffffc000000000
def t311 : ℕ := 0x198003300066000cc00198003300066000cc00198003300066000cc0000000000000000000000000000000000000000000000000000000000
def t312 : ℕ := 0x2861850c30a1861430c2861850c30a1861430c2861850c30a1861430c0000000003fffffffff000000000000007ffff0000000003fffffffff
def t313 : ℕ := 0x2288a2288a2288a00000003ff003ff
def t314 : ℕ := 0x20080200802008000000000000000
def t315 : ℕ := 0x9024090240902400000ffc00ffc00
def t316 : ℕ := 0x20882208822088200000003ff003ff
def t317 : ℕ := 0x80200802008020000000000000000
def t318 : ℕ := 0x300c0300c0300c00000ffc00ffc00
def t319 : ℕ := 0x441104411044110003ff00000003ff
def t320 : ℕ := 0xffc00
def t321 : ℕ := 0x7b1ec7b1ec7b1ecffc00ffc00ffc00
def t322 : ℕ := 0xb02c0b02c0b02c00000ffc0000000
def t323 : ℕ := 0x701c0701c0701c0ffc000000000000
def t324 : ℕ := 0xffc0000000
def t325 : ℕ := 0x8b22c8b22c8b22cffffffffffffc00
def t326 : ℕ := 0xb02c0b02c0b02c0000000000ffc00
def t327 : ℕ := 0x802008020080200fffff003ff00000
def t328 : ℕ := 0x3ff
def t329 : ℕ := 0x6e9ba6e9ba6e9ba003ff003ff003ff
def t330 : ℕ := 0x2288a2288a2288a00000003ff00000
def t331 : ℕ := 0x4c1304c1304c130003ff0000000000
def t332 : ℕ := 0x200802008020080000000000000000
def t333 : ℕ := 0x729ca729ca729caffc00003fffffff
def t334 : ℕ := 0x280a0280a0280a00000003ff003ff
def t335 : ℕ := 0x501405014050140ffc0000000ffc00
def t336 : ℕ := 0x3ff00000
def t337 : ℕ := 0xa2a8aa2a8aa2a8affffffffff003ff
def t338 : ℕ := 0x2288a2288a2288a0000000000003ff
def t339 : ℕ := 0x802008020080200fffffffc0000000
def t340 : ℕ := 0x401004010040100000000000000000
def t341 : ℕ := 0x7c1f07c1f07c1f0fffff00000fffff
def t342 : ℕ := 0xc0300c0300c030003ff00000003ff
def t343 : ℕ := 0x300c0300c0300c0ffc0000000ffc00
def t344 : ℕ := 0x3ff0000000000
def t345 : ℕ := 0xcc330cc330cc330ffffffffff003ff
def t346 : ℕ := 0x4c1304c1304c1300000000000003ff
def t347 : ℕ := 0x802008020080200ffc00fffff00000
def t348 : ℕ := 0xffc000000000000
def t349 : ℕ := 0xf03c0f03c0f03c0ffffffffffffc00
def t350 : ℕ := 0x701c0701c0701c00000000000ffc00
def t351 : ℕ := 0x802008020080200003fffffff00000
def t352 : ℕ := 0x7ffff
def t353 : ℕ := 0x2df545bea8b7d516faa2df545bea8b7d516faa2df545bea8b7d516faa0000000003ffff80000ffffe00000000000000ffffe0000000007ffff
def t354 : ℕ := 0x4154082a81055020aa04154082a81055020aa04154082a81055020aa0000000000000000000ffffe00000000000000ffffe00000000000000
def t355 : ℕ := 0x29e0053c00a78014f0029e0053c00a78014f0029e0053c00a78014f000000000003ffff8000000000000000000000000000000000000000000
def t356 : ℕ := 0x981302604c098000ffe000007ff
def t357 : ℕ := 0x21642c8590b216000000003ff800
def t358 : ℕ := 0x2574ae95d2ba57000001ffffffff
def t359 : ℕ := 0x1100022000440008800110002200044000880011000220004400088000000000000000000000000000000000000000000000003ffff80000
def t360 : ℕ := 0x148802910052200a440148802910052200a440148802910052200a44000000000000007ffff000000000000007ffff0000000000000000000
def t361 : ℕ := 0xe0441c0883811070220e0441c0883811070220e0441c08838110702200001ffffc000000000fffffffffc000000000fffffffffc00007ffff
def t362 : ℕ := 0x489122401fc07f
def t363 : ℕ := 0x74e9d3afe03fff
def t364 : ℕ := 0xf1e3c78fffff80
def t365 : ℕ := 0x200802008020080000000000ffc00
def t366 : ℕ := 0x9024090240902400000ffc0000000
def t367 : ℕ := 0x709c2709c2709c2ffc00003ff003ff
def t368 : ℕ := 0xffc00ffc00
def t369 : ℕ := 0xfb3ecfb3ecfb3ecffffffffffffc00
def t370 : ℕ := 0xb02c0b02c0b02c000000000000000
def t371 : ℕ := 0xf03c0f03c0f03c0fffff003ff00000
def t372 : ℕ := 0x4010040100401000000000000003ff
def t373 : ℕ := 0x7e9fa7e9fa7e9fafffff003fffffff
def t374 : ℕ := 0xc0300c0300c030003ff0000000000
def t375 : ℕ := 0x81020401fc000
def t376 : ℕ := 0x328ca328ca328caffc00003ffffc00
def t377 : ℕ := 0x3468d1afe03f80
def t378 : ℕ := 0xc993264fffffff
def t379 : ℕ := 0x4891224000007f
def t380 : ℕ := 0x8102040fe03f80
def t381 : ℕ := 0x401004010040100003ff0000000000
def t382 : ℕ := 0xfc3f0fc3f0fc3f0fffffffffffffff
def t383 : ℕ := 0xf9f3e7cfffffff
def t384 : ℕ := 0xc0300c0300c0300000000000003ff
def t385 : ℕ := 0xb02c0b02c0b02c0ffc00fffffffc00
def t386 : ℕ := 0xb162c58fe03f80
def t387 : ℕ := 0xffc00003ff00000
def t388 : ℕ := 0xfe03f80
def t389 : ℕ := 0xf2bcaf2bcaf2bcafffffffffffffff
def t390 : ℕ := 0xf5ebd7afffffff
def t391 : ℕ := 0x729ca729ca729ca0000000000fffff
def t392 : ℕ := 0x74e9d3a000007f
def t393 : ℕ := 0x802008020080200003ffffc0000000
def t394 : ℕ := 0x701c0701c0701c0ffc00003ffffc00
def t395 : ℕ := 0x280a0280a0280a0000000000003ff
def t396 : ℕ := 0x8000100002000040000800010000200004000080001000020000400000000000000000000000000000000000000000000000000000007ffff
def t397 : ℕ := 0x2ff545fea8bfd517faa2ff545fea8bfd517faa2ff545fea8bfd517faa00001fffffffff80000fffffffffc000000000fffffffffffffffffff
def t398 : ℕ := 0x61540c2a81855030aa061540c2a81855030aa061540c2a81855030aa00001ffffc000000000fffffffffc000000000ffffffffffffff80000
def t399 : ℕ := 0x21e0043c00878010f0021e0043c00878010f0021e0043c00878010f000000000003ffff8000000000000000000000000000000000000000000
def t400 : ℕ := 0x1ffffc000000000ffffe00000000000000
def t401 : ℕ := 0x3e1547c2a8f8551f0aa3e1547c2a8f8551f0aa3e1547c2a8f8551f0aafffffffffc000000000ffffffffffffffffffffffffffffffffffffff
def t402 : ℕ := 0xe1541c2a83855070aa0e1541c2a83855070aa0e1541c2a83855070aa00001ffffc000000000ffffe0000000000000000001ffffffffffffff
def t403 : ℕ := 0x3000060000c000180003000060000c000180003000060000c00018000ffffe000000000000000000000003fffffffff0000000000000000000
def t404 : ℕ := 0x140002800050000a000140002800050000a000140002800050000a00000000000000000000000000000000000000000001ffffc000000000
def t405 : ℕ := 0x8f9f51f3ea3e7d47cfa8f9f51f3ea3e7d47cfa8f9f51f3ea3e7d47cfa00001ffffc000000000ffffffffffffff80000fffffffffffffffffff
def t406 : ℕ := 0xe0141c02838050700a0e0141c02838050700a0e0141c02838050700a00001ffffc000000000fffffffffc000000000ffffe00003fffffffff
def t407 : ℕ := 0x818a103142062840c50818a103142062840c50818a103142062840c5000000000000000000000000000003ffff800000000000000000000000
def t408 : ℕ := 0x1ffffc000000000ffffe000000000000000000000000000000000
def t409 : ℕ := 0xce1559c2ab3855670aace1559c2ab3855670aace1559c2ab3855670aaffffffffffffffffffffffffffffc000000000fffffffffffffffffff
def t410 : ℕ := 0xe1541c2a83855070aa0e1541c2a83855070aa0e1541c2a83855070aa000000000000000000000001ffffc000000000fffffffffffffffffff
def t411 : ℕ := 0xc000180003000060000c000180003000060000c000180003000060000ffffe00003fffffffff00000000000000000000000000000000000000
def t412 : ℕ := 0xf81f03e07c0f87ffffe003fffff
def t413 : ℕ := 0x180300600c018000ffe000007ff
def t414 : ℕ := 0x8010020040080000000000007ff
def t415 : ℕ := 0xfd1fa3f47e8fd7fffffffffffff
def t416 : ℕ := 0x180300600c018000ffe00000000
def t417 : ℕ := 0x650ca194328657ff001fffff800
def t418 : ℕ := 0x1002004008010000ffe00000000
def t419 : ℕ := 0x8811022044088000000000007ff
def t420 : ℕ := 0x30660cc19833067ff001fffff800
def t421 : ℕ := 0x7ff000003ff800
def t422 : ℕ := 0x3f67ecfd9fb3f67ffffffffff800
def t423 : ℕ := 0xe01c0380700e000000000000000
def t424 : ℕ := 0x31662cc598b316000fffffc00000
def t425 : ℕ := 0x7ff001ffc00000
def t426 : ℕ := 0x3e57caf95f2be57fffffffffffff
def t427 : ℕ := 0xe51ca394728e5000000003fffff
def t428 : ℕ := 0x300600c0180300000ffe00000000
def t429 : ℕ := 0x4008010020047ff001fffff800
def t430 : ℕ := 0x3f77eefddfbbf77fffffffffffff
def t431 : ℕ := 0xe11c2384708e1000000000007ff
def t432 : ℕ := 0x312624c4989312000ffe00000000
def t433 : ℕ := 0x140002800050000a000140002800050000a000140002800050000a00000000000000000000000000000000000000000000000003ffff80000
def t434 : ℕ := 0x198003300066000cc00198003300066000cc00198003300066000cc000000000000007ffff000000000000007ffff0000000000000000000
def t435 : ℕ := 0x2ea005d400ba80175002ea005d400ba80175002ea005d400ba801750000001fffffffff8000000001ffffc00000000000001ffffc00007ffff
def t436 : ℕ := 0x4000080001000020000400008000100002000040000800010000200000000000000000000000000000000000000000000000000000007ffff
def t437 : ℕ := 0x154002a80055000aa00154002a80055000aa00154002a80055000aa0000000000000000000ffffe00000000000000ffffe00000000000000
def t438 : ℕ := 0x2be0057c00af8015f002be0057c00af8015f002be0057c00af8015f0000001fffffffff8000000001ffffc00000000000001fffffffff80000
def t439 : ℕ := 0x200004000080001000020000400008000100002000040000800010000000000000000000000000001ffffc0000000000000000000000000000
def t440 : ℕ := 0x3fe007fc00ff801ff003fe007fc00ff801ff003fe007fc00ff801ff00ffffffffffffff8000000001fffffffffffffffffffffffffffffffff
def t441 : ℕ := 0xfe001fc003f8007f000fe001fc003f8007f000fe001fc003f8007f0000001fffffffff80000000000000000000000000001ffffffffffffff
def t442 : ℕ := 0x100002000040000800010000200004000080001000020000400008000ffffe000000000000000000000003fffffffffffffe00000000000000
def t443 : ℕ := 0x180003000060000c000180003000060000c000180003000060000c000000000000000000000000000000000000000000001ffffc000000000
def t444 : ℕ := 0xaffe15ffc2bff857ff0affe15ffc2bff857ff0affe15ffc2bff857ff000001fffffffff8000000001fffffffff8000000001ffffffffffffff
def t445 : ℕ := 0x2e6005cc00b980173002e6005cc00b980173002e6005cc00b9801730000001fffffffff8000000001ffffc0000000000000000003fffffffff
def t446 : ℕ := 0x801e1003c20078400f0801e1003c20078400f0801e1003c20078400f000000000000000000000000000003ffff800000000000000000000000
def t447 : ℕ := 0x1fffffffff8000000000000000000000000000000000000000000
def t448 : ℕ := 0xefe01dfc03bf8077f00efe01dfc03bf8077f00efe01dfc03bf8077f00ffffffffffffffffffffffffffffc00000000000001ffffffffffffff
def t449 : ℕ := 0x2fe005fc00bf8017f002fe005fc00bf8017f002fe005fc00bf8017f00000000000000000000000001ffffc00000000000001ffffffffffffff
def t450 : ℕ := 0xc000180003000060000c000180003000060000c000180003000060000ffffe0000000007ffffffffe000000000000000000000000000000000
def t451 : ℕ := 0x7ffff00000000000000000000000000003ffff80000
def t452 : ℕ := 0xcf5999eb333d6667acccf5999eb333d6667acccf5999eb333d6667accffffffffffffffffffffffffffffc00007ffff00001fffffffff80000
def t453 : ℕ := 0x159802b30056600acc0159802b30056600acc0159802b30056600acc0000000000000000000000000000000007ffff0000000000000000000
def t454 : ℕ := 0xce0019c003380067000ce0019c003380067000ce0019c003380067000ffffffffffffff80000fffffffffc00000000000001ffffc000000000
def t455 : ℕ := 0x400008000100002000040000800010000200004000080001000020000000000000000000000ffffe000000000000000000000000000000000
def t456 : ℕ := 0x154002a80055000aa00154002a80055000aa00154002a80055000aa00000000000000000000000000000000000000ffffe0000000007ffff
def t457 : ℕ := 0xca00194003280065000ca00194003280065000ca00194003280065000fffffffffffffffffff00001ffffc00000000000001fffffffff80000
def t458 : ℕ := 0x800010000200004000080001000020000400008000100002000040000000000003ffff8000000000000000000000000000000000000000000
def t459 : ℕ := 0x21e0043c00878010f0021e0043c00878010f0021e0043c00878010f0000000000000000000000000000000000000000000000000000007ffff
def t460 : ℕ := 0xc60018c003180063000c60018c003180063000c60018c003180063000fffffffffc00007fffffffffffffc00000000000001fffffffff80000
def t461 : ℕ := 0xffffe0000000000000000001ffffc0000000000000000000000000000
def t462 : ℕ := 0xfe001fc003f8007f000fe001fc003f8007f000fe001fc003f8007f000ffffffffffffffffffffffffffffffffffffffffffffffffffff80000
def t463 : ℕ := 0x3000060000c000180003000060000c000180003000060000c0001800000000000000000000000000000003fffffffffffffe00000000000000
def t464 : ℕ := 0xce0019c003380067000ce0019c003380067000ce0019c00338006700000001ffffffffffffffffffe0000000000000000001fffffffff80000
def t465 : ℕ := 0xcb32ccb32ccb32cffffffffff00000
def t466 : ℕ := 0x8000100002000040000800010000200004000080001000020000400000000000000000000000000000000000000000000001ffffc000000000
def t467 : ℕ := 0xcf9e19f3c33e7867cf0cf9e19f3c33e7867cf0cf9e19f3c33e7867cf0fffffffffffffffffffffffffffffffff8000000001fffffffff80000
def t468 : ℕ := 0x19e0033c0067800cf0019e0033c0067800cf0019e0033c0067800cf000000000000000000000000000003ffff800000000000000000000000
def t469 : ℕ := 0x4e0009c0013800270004e0009c0013800270004e0009c001380027000ffffffffffffffffffffffffffffc0000000000000000003ffff80000
def t470 : ℕ := 0x1180023000460008c001180023000460008c001180023000460008c0000000000000007ffff00000000000000000000000000000000000000
def t471 : ℕ := 0x4180083001060020c004180083001060020c004180083001060020c0000000000000000000000000000000007ffff0000000003ffff80000
def t472 : ℕ := 0xc0861810c3021860430c0861810c3021860430c0861810c3021860430ffffffffffffff80000ffffe00003ffff8000000001ffffc000000000
def t473 : ℕ := 0x140002800050000a000140002800050000a000140002800050000a00000000000000000000ffffe000000000000000000000000000000000
def t474 : ℕ := 0xc59f58b3eb167d62cfac59f58b3eb167d62cfac59f58b3eb167d62cfafffffffffffffffffffffffe00003ffff80000fffffffffc00007ffff
def t475 : ℕ := 0x40140802810050200a040140802810050200a040140802810050200a00000000000000000000000000000000000000ffffe0000000007ffff
def t476 : ℕ := 0xc18a183143062860c50c18a183143062860c50c18a183143062860c50fffffffffffffffffff0000000003ffff8000000001ffffc000000000
def t477 : ℕ := 0x1ffffc000000000000000000000000000000001ffffc000000000
def t478 : ℕ := 0xe0001c0003800070000e0001c0003800070000e0001c000380007000000000000000000000000001ffffc0000000000000000003ffff80000
def t479 : ℕ := 0xc19e1833c3067860cf0c19e1833c3067860cf0c19e1833c3067860cf0ffffe00003fffffffffffffe00003ffff800000000000000000000000
def t480 : ℕ := 0x180003000060000c000180003000060000c000180003000060000c000000000003ffff8000000000000000000000000000000000000000000
def t481 : ℕ := 0xe9fe1d3fc3a7f874ff0e9fe1d3fc3a7f874ff0e9fe1d3fc3a7f874ff0fffffffffffffffffffffffe00003ffff8000000001ffffc00007ffff
def t482 : ℕ := 0x2860050c00a180143002860050c00a180143002860050c00a1801430000000000000000000000000000000000000000000000000000007ffff
def t483 : ℕ := 0xc01e1803c30078600f0c01e1803c30078600f0c01e1803c30078600f0fffffffffc00007ffffffffe00003ffff8000000001ffffc000000000
def t484 : ℕ := 0xffffe000000000000000000000003ffff800000000000000000000000
def t485 : ℕ := 0xf19e1e33c3c67878cf0f19e1e33c3c67878cf0f19e1e33c3c67878cf0fffffffffffffffffffffffffffffffffffffffffffffffc000000000
def t486 : ℕ := 0x3000060000c000180003000060000c000180003000060000c00018000000000000000000000000001ffffc00007ffffffffe00000000000000
def t487 : ℕ := 0xc19e1833c3067860cf0c19e1833c3067860cf0c19e1833c3067860cf000001ffffffffffffffffffe0000000000000000001ffffc000000000
def t488 : ℕ := 0x0
def v0 : List ℕ := [t0,t1,t2,t3,t4,t5,t6]
def v1 : List ℕ := [t7,t0,t1,t2,t3,t4,t5,t6]
def v2 : List ℕ := [t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b0 : Ban 30 5 v2 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w0 : Wide 30 5 v2 := viaSub (ws := [v2]) (consBan b0 (nilBan 30 5)) (by decide) (by decide +kernel)
def p127_114Slow : Projection 228 30 := pick [19,21,31,34,36,76,78,88,91,93,114,116,126,129,131,152,154,164,167,169,190,192,202,205,207,209,211,221,224,226] rfl (by decide +kernel) (by decide)
def p127_114T : LookupTree := (.fork t148 t488 (.fork t165 t488 (.fork t186 t8 (.fork t307 t488 (.fork t264 t488 (.fork t257 t488 (.fork t228 t488 (.fork t352 t488 .empty .empty) .empty) (.fork t236 t488 .empty .empty)) (.fork t7 t488 (.fork t170 t488 .empty .empty) (.fork t254 t488 .empty .empty))) (.fork t437 t488 (.fork t261 t488 (.fork t473 t488 (.fork t404 t488 .empty .empty) .empty) (.fork t456 t488 .empty .empty)) (.fork t434 t47 (.fork t252 t488 .empty .empty) (.fork t28 t8 .empty .empty)))) (.fork t0 t8 (.fork t360 t47 (.fork t21 t488 (.fork t192 t488 (.fork t39 t488 .empty .empty) .empty) (.fork t75 t488 .empty .empty)) (.fork t37 t51 (.fork t244 t8 .empty .empty) (.fork t19 t47 .empty .empty))) (.fork t480 t488 (.fork t232 t488 (.fork t44 t47 (.fork t83 t8 .empty .empty) .empty) (.fork t443 t488 .empty .empty)) (.fork t468 t488 (.fork t311 t488 .empty .empty) (.fork t242 t488 .empty .empty))))) (.fork t398 t9 (.fork t13 t488 (.fork t85 t488 (.fork t436 t488 (.fork t250 t488 (.fork t301 t8 .empty .empty) .empty) (.fork t455 t488 .empty .empty)) (.fork t309 t488 (.fork t475 t488 .empty .empty) (.fork t255 t488 .empty .empty))) (.fork t77 t8 (.fork t354 t488 (.fork t259 t488 (.fork t266 t488 .empty .empty) .empty) (.fork t1 t488 .empty .empty)) (.fork t12 t8 (.fork t227 t8 .empty .empty) (.fork t147 t9 .empty .empty)))) (.fork t2 t9 (.fork t299 t51 (.fork t458 t488 (.fork t396 t488 (.fork t91 t488 .empty .empty) .empty) (.fork t163 t488 .empty .empty)) (.fork t151 t59 (.fork t253 t9 .empty .empty) (.fork t230 t9 .empty .empty))) (.fork t164 t10 (.fork t251 t9 (.fork t406 t9 .empty .empty) (.fork t441 t59 .empty .empty)) (.fork t459 t488 (.fork t161 t488 .empty .empty) (.fork t399 t488 .empty .empty)))))) (.fork t239 t488 (.fork t397 t9 (.fork t355 t488 (.fork t312 t8 (.fork t482 t488 (.fork t168 t488 (.fork t271 t47 .empty .empty) .empty) (.fork t234 t488 .empty .empty)) (.fork t29 t488 (.fork t78 t488 .empty .empty) (.fork t172 t488 .empty .empty))) (.fork t353 t488 (.fork t22 t8 (.fork t256 t8 (.fork t3 t488 .empty .empty) .empty) (.fork t438 t9 .empty .empty)) (.fork t445 t9 (.fork t76 t8 .empty .empty) (.fork t92 t9 .empty .empty)))) (.fork t466 t488 (.fork t162 t10 (.fork t4 t10 (.fork t260 t10 (.fork t238 t10 .empty .empty) .empty) (.fork t258 t10 .empty .empty)) (.fork t469 t62 (.fork t243 t11 .empty .empty) (.fork t240 t488 .empty .empty))) (.fork t86 t488 (.fork t235 t488 (.fork t446 t488 (.fork t302 t488 .empty .empty) .empty) (.fork t169 t8 .empty .empty)) (.fork t407 t488 (.fork t187 t488 .empty .empty) (.fork t310 t488 .empty .empty))))) (.fork t173 t11 (.fork t229 t9 (.fork t156 t47 (.fork t263 t8 (.fork t5 t488 (.fork t231 t488 .empty .empty) .empty) (.fork t177 t51 .empty .empty)) (.fork t308 t488 (.fork t40 t8 .empty .empty) (.fork t84 t8 .empty .empty))) (.fork t237 t10 (.fork t166 t8 (.fork t233 t488 (.fork t405 t9 .empty .empty) .empty) (.fork t444 t9 .empty .empty)) (.fork t411 t64 (.fork t450 t64 .empty .empty) (.fork t160 t64 .empty .empty)))) (.fork t460 t62 (.fork t479 t64 (.fork t483 t11 (.fork t6 t11 (.fork t267 t11 .empty .empty) .empty) (.fork t476 t11 .empty .empty)) (.fork t265 t11 (.fork t241 t11 .empty .empty) (.fork t474 t11 .empty .empty))) (.fork t467 t62 (.fork t158 t62 (.fork t457 t62 .empty .empty) (.fork t409 t62 .empty .empty)) (.fork t481 t11 (.fork t171 t11 .empty .empty) (.fork t448 t62 .empty .empty)))))))
set_option maxHeartbeats 0 in
def p127_114 : Projection 228 30 := cached p127_114Slow p127_114T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1 : Ban 228 9 v1 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v3 : List ℕ := [t0,t12,t2,t3,t4,t5,t6]
def v4 : List ℕ := [t0,t13,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b2 : Ban 228 8 v4 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v5 : List ℕ := [t13,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b3 : Ban 228 8 v5 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v6 : List ℕ := [t0,t13,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b4 : Ban 228 8 v6 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v7 : List ℕ := [t14,t0,t12,t2,t3,t4,t5,t6]
def v8 : List ℕ := [t15,t16,t17]
set_option maxHeartbeats 0 in
theorem b5 : Ban 12 3 v8 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w1 : Wide 12 3 v8 := viaSub (ws := [v8]) (consBan b5 (nilBan 12 3)) (by decide) (by decide +kernel)
def p127_52Slow : Projection 228 12 := pick [38,42,50,53,95,99,107,110,114,118,126,129] rfl (by decide +kernel) (by decide)
def p127_52T : LookupTree := (.fork t12 t488 (.fork t471 t488 (.fork t87 t488 (.fork t79 t488 (.fork t30 t488 (.fork t14 t488 .empty .empty) .empty) (.fork t451 t488 (.fork t188 t488 .empty .empty) .empty)) (.fork t178 t488 (.fork t157 t488 (.fork t303 t488 .empty .empty) .empty) (.fork t28 t488 (.fork t7 t488 .empty .empty) .empty))) (.fork t0 t488 (.fork t190 t488 (.fork t453 t488 (.fork t470 t488 .empty .empty) .empty) (.fork t19 t488 (.fork t37 t488 .empty .empty) .empty)) (.fork t89 t488 (.fork t1 t488 (.fork t41 t488 .empty .empty) .empty) (.fork t81 t488 .empty .empty)))) (.fork t181 t488 (.fork t22 t488 (.fork t272 t488 (.fork t2 t16 (.fork t268 t488 .empty .empty) .empty) (.fork t305 t488 (.fork t3 t488 .empty .empty) .empty)) (.fork t182 t488 (.fork t185 t488 (.fork t4 t17 .empty .empty) .empty) (.fork t40 t15 (.fork t5 t15 .empty .empty) .empty))) (.fork t189 t488 (.fork t90 t488 (.fork t306 t488 (.fork t160 t488 .empty .empty) .empty) (.fork t6 t488 (.fork t191 t488 .empty .empty) .empty)) (.fork t158 t16 (.fork t88 t488 (.fork t241 t15 .empty .empty) .empty) (.fork t304 t488 .empty .empty)))))
set_option maxHeartbeats 0 in
def p127_52 : Projection 228 12 := cached p127_52Slow p127_52T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b6 : Ban 228 8 v7 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v9 : List ℕ := [t0,t12,t2,t18,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b7 : Ban 12 3 v8 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w2 : Wide 12 3 v8 := viaSub (ws := [v8]) (consBan b7 (nilBan 12 3)) (by decide) (by decide +kernel)
def p127_73Slow : Projection 228 12 := pick [0,1,8,17,133,134,141,150,171,172,179,188] rfl (by decide +kernel) (by decide)
def p127_73T : LookupTree := (.fork t251 t15 (.fork t190 t488 (.fork t188 t488 (.fork t174 t488 (.fork t153 t488 (.fork t14 t488 .empty .empty) (.fork t30 t488 .empty .empty)) (.fork t400 t488 (.fork t149 t488 .empty .empty) .empty)) (.fork t461 t488 (.fork t178 t488 (.fork t157 t488 .empty .empty) .empty) (.fork t433 t488 (.fork t359 t488 .empty .empty) .empty))) (.fork t74 t488 (.fork t1 t15 (.fork t184 t488 (.fork t0 t488 .empty .empty) .empty) (.fork t270 t488 (.fork t12 t15 .empty .empty) .empty)) (.fork t155 t488 (.fork t151 t488 (.fork t159 t488 .empty .empty) .empty) (.fork t2 t488 (.fork t20 t488 .empty .empty) .empty)))) (.fork t82 t488 (.fork t92 t16 (.fork t439 t488 (.fork t442 t488 (.fork t18 t488 .empty .empty) (.fork t300 t488 .empty .empty)) (.fork t22 t16 (.fork t3 t16 .empty .empty) .empty)) (.fork t403 t488 (.fork t180 t488 (.fork t463 t488 .empty .empty) .empty) (.fork t176 t488 (.fork t152 t488 .empty .empty) .empty))) (.fork t177 t488 (.fork t31 t488 (.fork t4 t488 (.fork t38 t488 .empty .empty) .empty) (.fork t5 t488 (.fork t150 t488 .empty .empty) .empty)) (.fork t175 t488 (.fork t154 t488 (.fork t40 t488 .empty .empty) .empty) (.fork t158 t17 (.fork t6 t17 .empty .empty) .empty)))))
set_option maxHeartbeats 0 in
def p127_73 : Projection 228 12 := cached p127_73Slow p127_73T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b8 : Ban 228 8 v9 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v10 : List ℕ := [t19,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b9 : Ban 228 8 v10 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v11 : List ℕ := [t0,t12,t20,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b10 : Ban 228 8 v11 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v12 : List ℕ := [t21,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b11 : Ban 228 8 v12 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v13 : List ℕ := [t0,t12,t2,t22,t4,t5,t6]
def v14 : List ℕ := [t23,t24,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b12 : Ban 55 6 v14 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w3 : Wide 55 6 v14 := viaSub (ws := [v14]) (consBan b12 (nilBan 55 6)) (by decide) (by decide +kernel)
def p127_61Slow : Projection 228 55 := pick [0,1,4,5,8,10,12,13,14,15,16,38,39,42,43,46,48,50,51,52,53,54,57,58,61,62,65,67,69,70,71,72,73,95,96,99,100,103,105,107,108,109,110,111,114,115,118,119,122,124,126,127,128,129,130] rfl (by decide +kernel) (by decide)
def p127_61T : LookupTree := (.fork t180 t27 (.fork t1 t24 (.fork t178 t488 (.fork t188 t488 (.fork t30 t488 (.fork t14 t488 .empty .empty) .empty) (.fork t157 t488 .empty .empty)) (.fork t0 t488 (.fork t37 t488 (.fork t190 t488 .empty .empty) .empty) (.fork t184 t23 .empty .empty))) (.fork t18 t25 (.fork t20 t25 (.fork t159 t25 (.fork t12 t24 .empty .empty) .empty) (.fork t2 t25 .empty .empty)) (.fork t3 t26 (.fork t29 t26 .empty .empty) (.fork t22 t26 .empty .empty)))) (.fork t6 t488 (.fork t40 t23 (.fork t31 t27 (.fork t4 t27 (.fork t38 t27 .empty .empty) .empty) (.fork t5 t23 .empty .empty)) (.fork t181 t488 (.fork t166 t167 (.fork t84 t93 .empty .empty) .empty) (.fork t191 t488 .empty .empty))) (.fork t454 t25 (.fork t241 t23 (.fork t189 t488 (.fork t472 t23 .empty .empty) .empty) (.fork t183 t23 .empty .empty)) (.fork t452 t25 (.fork t158 t25 .empty .empty) (.fork t179 t27 .empty .empty)))))
set_option maxHeartbeats 0 in
def p127_61 : Projection 228 55 := cached p127_61Slow p127_61T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b13 : Ban 228 8 v13 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v15 : List ℕ := [t0,t12,t2,t3,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b14 : Ban 228 8 v15 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v16 : List ℕ := [t28,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b15 : Ban 228 8 v16 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v17 : List ℕ := [t0,t12,t2,t29,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b16 : Ban 228 8 v17 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v18 : List ℕ := [t0,t12,t2,t29,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b17 : Ban 228 8 v18 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v19 : List ℕ := [t30,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b18 : Ban 228 8 v19 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v20 : List ℕ := [t12,t2,t3,t4,t31,t5,t6]
def v21 : List ℕ := [t32,t33,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b19 : Ban 60 6 v21 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w4 : Wide 60 6 v21 := viaSub (ws := [v21]) (consBan b19 (nilBan 60 6)) (by decide) (by decide +kernel)
def p127_91Slow : Projection 228 60 := pick [0,1,2,3,8,9,12,13,14,17,19,20,21,22,27,28,31,32,33,36,133,134,135,136,141,142,145,146,147,150,152,153,154,155,160,161,164,165,166,169,171,172,173,174,179,180,183,184,185,188,190,191,192,193,198,199,202,203,204,207] rfl (by decide +kernel) (by decide)
def p127_91T : LookupTree := (.fork t80 t33 (.fork t42 t43 (.fork t12 t33 (.fork t0 t32 (.fork t484 t488 (.fork t149 t488 .empty .empty) .empty) (.fork t1 t313 .empty .empty)) (.fork t2 t35 (.fork t151 t35 .empty .empty) (.fork t251 t333 .empty .empty))) (.fork t152 t488 (.fork t486 t488 (.fork t22 t262 (.fork t3 t34 .empty .empty) .empty) (.fork t180 t488 .empty .empty)) (.fork t4 t488 (.fork t38 t488 .empty .empty) (.fork t31 t32 .empty .empty)))) (.fork t487 t36 (.fork t40 t32 (.fork t401 t333 (.fork t150 t35 (.fork t162 t34 .empty .empty) .empty) (.fork t5 t488 .empty .empty)) (.fork t181 t36 (.fork t84 t33 .empty .empty) (.fork t6 t36 .empty .empty))) (.fork t409 t389 (.fork t464 t349 (.fork t241 t36 .empty .empty) (.fork t158 t349 .empty .empty)) (.fork t485 t36 (.fork t179 t36 .empty .empty) (.fork t462 t349 .empty .empty)))))
set_option maxHeartbeats 0 in
def p127_91 : Projection 228 60 := cached p127_91Slow p127_91T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b20 : Ban 228 8 v20 := viaCut p127_91 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v22 : List ℕ := [t0,t12,t2,t3,t4,t31,t5,t6]
set_option maxHeartbeats 0 in
theorem b21 : Ban 228 8 v22 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v23 : List ℕ := [t37,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b22 : Ban 228 8 v23 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v24 : List ℕ := [t37,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b23 : Ban 228 8 v24 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v25 : List ℕ := [t0,t12,t2,t3,t38,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b24 : Ban 228 8 v25 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v26 : List ℕ := [t39,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b25 : Ban 228 8 v26 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v27 : List ℕ := [t12,t2,t3,t4,t40,t6]
def v28 : List ℕ := [t41,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b26 : Ban 228 7 v28 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v29 : List ℕ := [t2,t42,t3,t4,t40,t6]
def v30 : List ℕ := [t32,t34,t35,t43,t36]
set_option maxHeartbeats 0 in
theorem b27 : Ban 60 6 v30 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w5 : Wide 60 6 v30 := viaSub (ws := [v30]) (consBan b27 (nilBan 60 6)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b28 : Ban 228 7 v29 := viaCut p127_91 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v31 : List ℕ := [t12,t2,t42,t3,t4,t40,t6]
def v32 : List ℕ := [t32,t33,t34,t35,t43,t36]
set_option maxHeartbeats 0 in
theorem b29 : Ban 60 6 v32 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w6 : Wide 60 6 v32 := viaSub (ws := [v21,v30,v32]) (consBan b19 (consBan b27 (consBan b29 (nilBan 60 6)))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b30 : Ban 228 7 v31 := viaCut p127_91 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v33 : List ℕ := [t44,t2,t3,t4,t40,t6]
def v34 : List ℕ := [t45,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b31 : Ban 12 3 v8 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w7 : Wide 12 3 v8 := viaSub (ws := [v8]) (consBan b31 (nilBan 12 3)) (by decide) (by decide +kernel)
def p114_98Slow : Projection 30 12 := pick [5,6,8,9,15,16,18,19,25,26,28,29] rfl (by decide +kernel) (by decide)
def p114_98T : LookupTree := (.fork t48 t488 (.fork t47 t15 (.fork t57 t488 (.fork t45 t488 .empty .empty) .empty) (.fork t8 t15 .empty .empty)) (.fork t10 t16 (.fork t9 t488 .empty .empty) (.fork t11 t17 .empty .empty)))
set_option maxHeartbeats 0 in
def p114_98 : Projection 30 12 := cached p114_98Slow p114_98T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b32 : Ban 30 5 v34 := viaCut p114_98 w7 (by decide) (by decide +kernel) (by decide +kernel)
def v35 : List ℕ := [t8,t9,t46,t10,t11]
set_option maxHeartbeats 0 in
theorem b33 : Ban 30 5 v35 := viaSmall (by decide +kernel) (by decide)
def v36 : List ℕ := [t47,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b34 : Ban 12 3 v8 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w8 : Wide 12 3 v8 := viaSub (ws := [v8]) (consBan b34 (nilBan 12 3)) (by decide) (by decide +kernel)
def p114_112Slow : Projection 30 12 := pick [10,12,13,14,20,22,23,24,25,27,28,29] rfl (by decide +kernel) (by decide)
def p114_112T : LookupTree := (.fork t9 t15 (.fork t47 t488 (.fork t70 t488 (.fork t49 t488 .empty .empty) (.fork t51 t488 .empty .empty)) (.fork t48 t15 (.fork t8 t488 .empty .empty) .empty)) (.fork t69 t16 (.fork t52 t16 (.fork t46 t15 .empty .empty) (.fork t10 t16 .empty .empty)) (.fork t11 t17 (.fork t50 t16 .empty .empty) .empty)))
set_option maxHeartbeats 0 in
def p114_112 : Projection 30 12 := cached p114_112Slow p114_112T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b35 : Ban 30 5 v36 := viaCut p114_112 w8 (by decide) (by decide +kernel) (by decide +kernel)
def v37 : List ℕ := [t8,t48,t9,t10,t11]
def a114_4156Slow : Projection 30 30 := pick [0,2,1,3,4,10,12,11,13,14,5,7,6,8,9,20,22,21,23,24,15,17,16,18,19,25,27,26,28,29] rfl (by decide +kernel) (by decide)
def a114_4156T : LookupTree := (.fork t48 t47 (.fork t47 t48 (.fork t57 t49 (.fork t49 t57 .empty .empty) (.fork t51 t59 .empty .empty)) (.fork t59 t51 (.fork t8 t9 .empty .empty) .empty)) (.fork t50 t58 (.fork t10 t10 (.fork t9 t8 .empty .empty) .empty) (.fork t11 t11 (.fork t58 t50 .empty .empty) .empty)))
set_option maxHeartbeats 0 in
def a114_4156 : Projection 30 30 := cached a114_4156Slow a114_4156T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b36 : Ban 30 5 v37 := viaPerm a114_4156 a114_4156 b35 (by decide +kernel) (by decide +kernel)
def v38 : List ℕ := [t49,t8,t9,t10,t11]
def a114_1546Slow : Projection 30 30 := pick [5,6,8,7,9,0,1,3,2,4,10,11,13,12,14,15,16,18,17,19,25,26,28,27,29,20,21,23,22,24] rfl (by decide +kernel) (by decide)
def a114_1546T : LookupTree := (.fork t9 t10 (.fork t47 t51 (.fork t61 t65 (.fork t49 t45 (.fork t45 t49 .empty .empty) .empty) (.fork t51 t47 (.fork t65 t61 .empty .empty) .empty)) (.fork t59 t60 (.fork t63 t67 (.fork t8 t8 .empty .empty) .empty) (.fork t48 t52 .empty .empty))) (.fork t10 t9 (.fork t60 t59 (.fork t67 t63 (.fork t46 t50 .empty .empty) .empty) (.fork t52 t48 .empty .empty)) (.fork t62 t66 (.fork t11 t11 (.fork t50 t46 .empty .empty) .empty) (.fork t66 t62 .empty .empty))))
set_option maxHeartbeats 0 in
def a114_1546 : Projection 30 30 := cached a114_1546Slow a114_1546T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b37 : Ban 30 5 v38 := viaPerm a114_1546 a114_1546 b32 (by decide +kernel) (by decide +kernel)
def v39 : List ℕ := [t8,t9,t10,t50,t11]
set_option maxHeartbeats 0 in
theorem b38 : Ban 30 5 v39 := viaPerm a114_1546 a114_1546 b33 (by decide +kernel) (by decide +kernel)
def v40 : List ℕ := [t51,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b39 : Ban 30 5 v40 := viaPerm a114_1546 a114_1546 b35 (by decide +kernel) (by decide +kernel)
def v41 : List ℕ := [t8,t9,t52,t10,t11]
set_option maxHeartbeats 0 in
theorem b40 : Ban 30 5 v41 := viaPerm a114_1546 a114_1546 b36 (by decide +kernel) (by decide +kernel)
def v42 : List ℕ := [t53,t8,t9,t10,t11]
def a114_1465Slow : Projection 30 30 := pick [0,1,2,4,3,15,16,17,19,18,20,21,22,24,23,5,6,7,9,8,10,11,12,14,13,25,26,27,29,28] rfl (by decide +kernel) (by decide)
def a114_1465T : LookupTree := (.fork t67 t68 (.fork t70 t72 (.fork t61 t57 (.fork t57 t61 (.fork t49 t53 .empty .empty) (.fork t53 t49 .empty .empty)) (.fork t55 t51 (.fork t72 t70 .empty .empty) .empty)) (.fork t63 t59 (.fork t47 t47 (.fork t51 t55 .empty .empty) (.fork t8 t8 .empty .empty)) (.fork t9 t9 (.fork t59 t63 .empty .empty) .empty))) (.fork t68 t67 (.fork t69 t71 (.fork t52 t56 (.fork t60 t64 .empty .empty) (.fork t10 t11 .empty .empty)) (.fork t58 t62 (.fork t50 t54 .empty .empty) .empty)) (.fork t71 t69 (.fork t56 t52 (.fork t64 t60 .empty .empty) (.fork t11 t10 .empty .empty)) (.fork t62 t58 (.fork t54 t50 .empty .empty) .empty))))
set_option maxHeartbeats 0 in
def a114_1465 : Projection 30 30 := cached a114_1465Slow a114_1465T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b41 : Ban 30 5 v42 := viaPerm a114_1465 a114_1465 b37 (by decide +kernel) (by decide +kernel)
def v43 : List ℕ := [t8,t9,t10,t11,t54]
set_option maxHeartbeats 0 in
theorem b42 : Ban 30 5 v43 := viaPerm a114_1465 a114_1465 b38 (by decide +kernel) (by decide +kernel)
def v44 : List ℕ := [t55,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b43 : Ban 30 5 v44 := viaPerm a114_1465 a114_1465 b39 (by decide +kernel) (by decide +kernel)
def v45 : List ℕ := [t8,t9,t10,t56,t11]
set_option maxHeartbeats 0 in
theorem b44 : Ban 30 5 v45 := viaPerm a114_1465 a114_1465 b40 (by decide +kernel) (by decide +kernel)
def v46 : List ℕ := [t57,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b45 : Ban 30 5 v46 := viaPerm a114_4156 a114_4156 b37 (by decide +kernel) (by decide +kernel)
def v47 : List ℕ := [t8,t9,t10,t58,t11]
set_option maxHeartbeats 0 in
theorem b46 : Ban 30 5 v47 := viaPerm a114_4156 a114_4156 b38 (by decide +kernel) (by decide +kernel)
def v48 : List ℕ := [t8,t59,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b47 : Ban 30 5 v48 := viaPerm a114_4156 a114_4156 b39 (by decide +kernel) (by decide +kernel)
def v49 : List ℕ := [t8,t9,t60,t10,t11]
set_option maxHeartbeats 0 in
theorem b48 : Ban 30 5 v49 := viaPerm a114_1546 a114_1546 b47 (by decide +kernel) (by decide +kernel)
def v50 : List ℕ := [t61,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b49 : Ban 30 5 v50 := viaPerm a114_1465 a114_1465 b45 (by decide +kernel) (by decide +kernel)
def v51 : List ℕ := [t8,t9,t10,t11,t62]
set_option maxHeartbeats 0 in
theorem b50 : Ban 30 5 v51 := viaPerm a114_1465 a114_1465 b46 (by decide +kernel) (by decide +kernel)
def v52 : List ℕ := [t8,t63,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b51 : Ban 30 5 v52 := viaPerm a114_1465 a114_1465 b47 (by decide +kernel) (by decide +kernel)
def v53 : List ℕ := [t8,t9,t10,t64,t11]
set_option maxHeartbeats 0 in
theorem b52 : Ban 30 5 v53 := viaPerm a114_1465 a114_1465 b48 (by decide +kernel) (by decide +kernel)
def v54 : List ℕ := [t65,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b53 : Ban 30 5 v54 := viaPerm a114_1546 a114_1546 b49 (by decide +kernel) (by decide +kernel)
def v55 : List ℕ := [t8,t9,t10,t11,t66]
set_option maxHeartbeats 0 in
theorem b54 : Ban 30 5 v55 := viaPerm a114_1546 a114_1546 b50 (by decide +kernel) (by decide +kernel)
def v56 : List ℕ := [t8,t9,t67,t10,t11]
set_option maxHeartbeats 0 in
theorem b55 : Ban 30 5 v56 := viaPerm a114_1546 a114_1546 b51 (by decide +kernel) (by decide +kernel)
def v57 : List ℕ := [t8,t9,t10,t68,t11]
set_option maxHeartbeats 0 in
theorem b56 : Ban 30 5 v57 := viaPerm a114_1465 a114_1465 b55 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b57 : Ban 30 6 v2 := viaBranch (ws := [v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57]) (consBan b32 (consBan b33 (consBan b35 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (consBan b40 (consBan b41 (consBan b42 (consBan b43 (consBan b44 (consBan b45 (consBan b46 (consBan b47 (consBan b48 (consBan b49 (consBan b50 (consBan b51 (consBan b52 (consBan b53 (consBan b54 (consBan b55 (consBan b56 (nilBan 30 5))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
def v58 : List ℕ := [t45,t47,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b58 : Ban 30 5 v58 := viaCut p114_98 w7 (by decide) (by decide +kernel) (by decide +kernel)
def v59 : List ℕ := [t45,t47,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b59 : Ban 30 5 v59 := viaCut p114_98 w7 (by decide) (by decide +kernel) (by decide +kernel)
def v60 : List ℕ := [t47,t8,t46,t10,t11]
set_option maxHeartbeats 0 in
theorem b60 : Ban 30 5 v60 := viaCut p114_112 w8 (by decide) (by decide +kernel) (by decide +kernel)
def v61 : List ℕ := [t47,t8,t9,t46,t10,t11]
set_option maxHeartbeats 0 in
theorem b61 : Ban 30 5 v61 := viaCut p114_112 w8 (by decide) (by decide +kernel) (by decide +kernel)
def v62 : List ℕ := [t49,t47,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b62 : Ban 30 5 v62 := viaCut p114_112 w8 (by decide) (by decide +kernel) (by decide +kernel)
def v63 : List ℕ := [t8,t9,t10,t69,t11]
set_option maxHeartbeats 0 in
theorem b63 : Ban 30 5 v63 := viaSmall (by decide +kernel) (by decide)
def v64 : List ℕ := [t47,t8,t9,t10,t69,t11]
set_option maxHeartbeats 0 in
theorem b64 : Ban 30 5 v64 := viaCut p114_112 w8 (by decide) (by decide +kernel) (by decide +kernel)
def v65 : List ℕ := [t70,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b65 : Ban 30 5 v65 := viaCut p114_112 w8 (by decide) (by decide +kernel) (by decide +kernel)
def v66 : List ℕ := [t70,t47,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b66 : Ban 30 5 v66 := viaCut p114_112 w8 (by decide) (by decide +kernel) (by decide +kernel)
def v67 : List ℕ := [t47,t8,t9,t52,t10,t11]
set_option maxHeartbeats 0 in
theorem b67 : Ban 30 5 v67 := viaCut p114_112 w8 (by decide) (by decide +kernel) (by decide +kernel)
def v68 : List ℕ := [t53,t47,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b68 : Ban 30 5 v68 := viaPerm a114_1465 a114_1465 b62 (by decide +kernel) (by decide +kernel)
def v69 : List ℕ := [t8,t9,t10,t11,t71]
set_option maxHeartbeats 0 in
theorem b69 : Ban 30 5 v69 := viaPerm a114_1465 a114_1465 b63 (by decide +kernel) (by decide +kernel)
def v70 : List ℕ := [t47,t8,t9,t10,t11,t71]
set_option maxHeartbeats 0 in
theorem b70 : Ban 30 5 v70 := viaPerm a114_1465 a114_1465 b64 (by decide +kernel) (by decide +kernel)
def v71 : List ℕ := [t72,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b71 : Ban 30 5 v71 := viaPerm a114_1465 a114_1465 b65 (by decide +kernel) (by decide +kernel)
def v72 : List ℕ := [t72,t47,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b72 : Ban 30 5 v72 := viaPerm a114_1465 a114_1465 b66 (by decide +kernel) (by decide +kernel)
def v73 : List ℕ := [t47,t8,t9,t10,t56,t11]
set_option maxHeartbeats 0 in
theorem b73 : Ban 30 5 v73 := viaPerm a114_1465 a114_1465 b67 (by decide +kernel) (by decide +kernel)
def v74 : List ℕ := [t47,t8,t48,t10,t11]
set_option maxHeartbeats 0 in
theorem b74 : Ban 30 5 v74 := viaCut p114_112 w8 (by decide) (by decide +kernel) (by decide +kernel)
def v75 : List ℕ := [t47,t48,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b75 : Ban 30 5 v75 := viaPerm a114_4156 a114_4156 b74 (by decide +kernel) (by decide +kernel)
def v76 : List ℕ := [t47,t8,t48,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b76 : Ban 30 5 v76 := viaCut p114_98 w7 (by decide) (by decide +kernel) (by decide +kernel)
def v77 : List ℕ := [t47,t9,t10,t50,t11]
set_option maxHeartbeats 0 in
theorem b77 : Ban 30 5 v77 := viaSmall (by decide +kernel) (by decide)
def v78 : List ℕ := [t47,t8,t9,t10,t50,t11]
set_option maxHeartbeats 0 in
theorem b78 : Ban 30 5 v78 := viaCut p114_112 w8 (by decide) (by decide +kernel) (by decide +kernel)
def v79 : List ℕ := [t51,t47,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b79 : Ban 30 5 v79 := viaCut p114_112 w8 (by decide) (by decide +kernel) (by decide +kernel)
def v80 : List ℕ := [t51,t47,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b80 : Ban 30 5 v80 := viaCut p114_112 w8 (by decide) (by decide +kernel) (by decide +kernel)
def v81 : List ℕ := [t47,t9,t10,t11,t54]
set_option maxHeartbeats 0 in
theorem b81 : Ban 30 5 v81 := viaPerm a114_1465 a114_1465 b77 (by decide +kernel) (by decide +kernel)
def v82 : List ℕ := [t47,t8,t9,t10,t11,t54]
set_option maxHeartbeats 0 in
theorem b82 : Ban 30 5 v82 := viaPerm a114_1465 a114_1465 b78 (by decide +kernel) (by decide +kernel)
def v83 : List ℕ := [t55,t47,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b83 : Ban 30 5 v83 := viaPerm a114_1465 a114_1465 b79 (by decide +kernel) (by decide +kernel)
def v84 : List ℕ := [t55,t47,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b84 : Ban 30 5 v84 := viaPerm a114_1465 a114_1465 b80 (by decide +kernel) (by decide +kernel)
def v85 : List ℕ := [t57,t47,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b85 : Ban 30 5 v85 := viaCut p114_98 w7 (by decide) (by decide +kernel) (by decide +kernel)
def v86 : List ℕ := [t47,t8,t9,t10,t58,t11]
set_option maxHeartbeats 0 in
theorem b86 : Ban 30 5 v86 := viaSmall (by decide +kernel) (by decide)
def v87 : List ℕ := [t47,t8,t59,t9,t10,t11]
def a114_4516Slow : Projection 30 30 := pick [10,12,13,11,14,0,2,3,1,4,5,7,8,6,9,20,22,23,21,24,25,27,28,26,29,15,17,18,16,19] rfl (by decide +kernel) (by decide)
def a114_4516T : LookupTree := (.fork t9 t8 (.fork t8 t10 (.fork t47 t52 .empty .empty) (.fork t59 t47 .empty .empty)) (.fork t11 t11 (.fork t10 t9 .empty .empty) .empty))
set_option maxHeartbeats 0 in
def a114_4516 : Projection 30 30 := cached a114_4516Slow a114_4516T (by decide +kernel)
def a114_5146Slow : Projection 30 30 := pick [5,8,6,7,9,10,13,11,12,14,0,3,1,2,4,25,28,26,27,29,15,18,16,17,19,20,23,21,22,24] rfl (by decide +kernel) (by decide)
def a114_5146T : LookupTree := (.fork t52 t47 (.fork t8 t9 (.fork t47 t59 .empty .empty) (.fork t9 t10 .empty .empty)) (.fork t11 t11 (.fork t10 t8 .empty .empty) .empty))
set_option maxHeartbeats 0 in
def a114_5146 : Projection 30 30 := cached a114_5146Slow a114_5146T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b87 : Ban 30 5 v87 := viaPerm a114_4516 a114_5146 b67 (by decide +kernel) (by decide +kernel)
def v88 : List ℕ := [t47,t8,t9,t60,t10,t11]
set_option maxHeartbeats 0 in
theorem b88 : Ban 12 3 v8 := viaSmall (by decide +kernel) (by decide)
def v89 : List ℕ := [t73,t15,t16,t17]
set_option maxHeartbeats 0 in
theorem b89 : Ban 12 3 v89 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w9 : Wide 12 3 v89 := viaSub (ws := [v8,v89]) (consBan b88 (consBan b89 (nilBan 12 3))) (by decide) (by decide +kernel)
def p114_82Slow : Projection 30 12 := pick [0,1,2,4,15,16,17,19,20,21,22,24] rfl (by decide +kernel) (by decide)
def p114_82T : LookupTree := (.fork t67 t488 (.fork t8 t15 (.fork t47 t73 (.fork t65 t488 .empty .empty) .empty) (.fork t9 t16 .empty .empty)) (.fork t10 t488 (.fork t60 t488 .empty .empty) (.fork t11 t17 .empty .empty)))
set_option maxHeartbeats 0 in
def p114_82 : Projection 30 12 := cached p114_82Slow p114_82T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b90 : Ban 30 5 v88 := viaCut p114_82 w9 (by decide) (by decide +kernel) (by decide +kernel)
def v90 : List ℕ := [t61,t47,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b91 : Ban 30 5 v90 := viaPerm a114_1465 a114_1465 b85 (by decide +kernel) (by decide +kernel)
def v91 : List ℕ := [t47,t8,t9,t10,t11,t62]
set_option maxHeartbeats 0 in
theorem b92 : Ban 30 5 v91 := viaPerm a114_1465 a114_1465 b86 (by decide +kernel) (by decide +kernel)
def v92 : List ℕ := [t47,t8,t63,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b93 : Ban 30 5 v92 := viaPerm a114_1465 a114_1465 b87 (by decide +kernel) (by decide +kernel)
def v93 : List ℕ := [t47,t8,t9,t10,t64,t11]
set_option maxHeartbeats 0 in
theorem b94 : Ban 30 5 v93 := viaPerm a114_1465 a114_1465 b90 (by decide +kernel) (by decide +kernel)
def v94 : List ℕ := [t65,t47,t8,t9,t10,t11]
set_option maxHeartbeats 0 in
theorem b95 : Ban 30 5 v94 := viaCut p114_82 w9 (by decide) (by decide +kernel) (by decide +kernel)
def v95 : List ℕ := [t47,t8,t9,t10,t11,t66]
set_option maxHeartbeats 0 in
theorem b96 : Ban 30 5 v95 := viaSmall (by decide +kernel) (by decide)
def v96 : List ℕ := [t47,t8,t9,t67,t10,t11]
set_option maxHeartbeats 0 in
theorem b97 : Ban 30 5 v96 := viaCut p114_82 w9 (by decide) (by decide +kernel) (by decide +kernel)
def v97 : List ℕ := [t47,t8,t9,t10,t68,t11]
set_option maxHeartbeats 0 in
theorem b98 : Ban 30 5 v97 := viaPerm a114_1465 a114_1465 b97 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b99 : Ban 30 6 v36 := viaBranch (ws := [v58,v34,v59,v60,v35,v61,v38,v62,v63,v64,v65,v66,v41,v67,v42,v68,v69,v70,v71,v72,v45,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v90,v91,v92,v93,v94,v95,v96,v97]) (consBan b58 (consBan b32 (consBan b59 (consBan b60 (consBan b33 (consBan b61 (consBan b37 (consBan b62 (consBan b63 (consBan b64 (consBan b65 (consBan b66 (consBan b40 (consBan b67 (consBan b41 (consBan b68 (consBan b69 (consBan b70 (consBan b71 (consBan b72 (consBan b44 (consBan b73 (consBan b74 (consBan b75 (consBan b76 (consBan b77 (consBan b78 (consBan b79 (consBan b80 (consBan b81 (consBan b82 (consBan b83 (consBan b84 (consBan b85 (consBan b86 (consBan b87 (consBan b90 (consBan b91 (consBan b92 (consBan b93 (consBan b94 (consBan b95 (consBan b96 (consBan b97 (consBan b98 (nilBan 30 5)))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w10 : Wide 30 6 v36 := viaSub (ws := [v2,v36]) (consBan b57 (consBan b99 (nilBan 30 6))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b100 : Ban 228 7 v33 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v98 : List ℕ := [t44,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b101 : Ban 228 7 v98 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v99 : List ℕ := [t12,t74,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b102 : Ban 228 7 v99 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v100 : List ℕ := [t75,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b103 : Ban 228 7 v100 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v101 : List ℕ := [t12,t2,t3,t76,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b104 : Ban 228 7 v101 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v102 : List ℕ := [t77,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b105 : Ban 228 7 v102 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v103 : List ℕ := [t12,t2,t78,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b106 : Ban 228 7 v103 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v104 : List ℕ := [t79,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b107 : Ban 228 7 v104 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v105 : List ℕ := [t12,t2,t3,t4,t80,t40,t6]
set_option maxHeartbeats 0 in
theorem b108 : Ban 228 7 v105 := viaCut p127_91 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v106 : List ℕ := [t81,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b109 : Ban 228 7 v106 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v107 : List ℕ := [t12,t2,t3,t82,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b110 : Ban 228 7 v107 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v108 : List ℕ := [t83,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b111 : Ban 228 7 v108 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v109 : List ℕ := [t12,t2,t3,t4,t40,t84,t6]
set_option maxHeartbeats 0 in
theorem b112 : Ban 228 7 v109 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v110 : List ℕ := [t85,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b113 : Ban 228 7 v110 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v111 : List ℕ := [t12,t2,t3,t4,t86,t40,t6]
set_option maxHeartbeats 0 in
theorem b114 : Ban 228 7 v111 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v112 : List ℕ := [t87,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b115 : Ban 228 7 v112 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v113 : List ℕ := [t12,t2,t3,t4,t40,t6,t88]
set_option maxHeartbeats 0 in
theorem b116 : Ban 228 7 v113 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v114 : List ℕ := [t89,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b117 : Ban 228 7 v114 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v115 : List ℕ := [t12,t2,t3,t4,t40,t90,t6]
set_option maxHeartbeats 0 in
theorem b118 : Ban 228 7 v115 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v116 : List ℕ := [t12,t91,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b119 : Ban 228 7 v116 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v117 : List ℕ := [t12,t2,t92,t4,t40,t6]
def v118 : List ℕ := [t23,t93,t25,t94,t27]
def v119 : List ℕ := [t23,t95,t25,t94,t27]
set_option maxHeartbeats 0 in
theorem b120 : Ban 55 5 v119 := viaSmall (by decide +kernel) (by decide)
def v120 : List ℕ := [t95,t93,t25,t94,t27]
def v121 : List ℕ := [t96,t97,t98,t99]
set_option maxHeartbeats 0 in
theorem b121 : Ban 18 4 v121 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w11 : Wide 18 4 v121 := viaSub (ws := [v121]) (consBan b121 (nilBan 18 4)) (by decide) (by decide +kernel)
def p59_27Slow : Projection 55 18 := pick [0,1,2,3,4,5,6,7,8,11,12,13,14,15,16,17,18,19] rfl (by decide +kernel) (by decide)
def p59_27T : LookupTree := (.fork t145 t99 (.fork t95 t96 (.fork t129 t130 (.fork t133 t488 (.fork t115 t488 (.fork t202 t488 .empty .empty) .empty) (.fork t139 t488 .empty .empty)) (.fork t23 t111 (.fork t117 t111 (.fork t108 t109 .empty .empty) .empty) (.fork t119 t120 .empty .empty))) (.fork t141 t98 (.fork t93 t97 (.fork t135 t97 (.fork t24 t215 .empty .empty) .empty) (.fork t124 t125 .empty .empty)) (.fork t195 t284 (.fork t25 t98 .empty .empty) (.fork t121 t122 .empty .empty)))) (.fork t118 t488 (.fork t94 t99 (.fork t137 t138 (.fork t143 t488 (.fork t146 t488 .empty .empty) .empty) (.fork t131 t132 .empty .empty)) (.fork t142 t488 (.fork t127 t128 (.fork t110 t112 .empty .empty) .empty) (.fork t136 t488 .empty .empty))) (.fork t274 t281 (.fork t116 t111 (.fork t27 t488 (.fork t209 t488 .empty .empty) .empty) (.fork t134 t97 .empty .empty)) (.fork t144 t99 (.fork t140 t98 .empty .empty) (.fork t294 t112 .empty .empty)))))
set_option maxHeartbeats 0 in
def p59_27 : Projection 55 18 := cached p59_27Slow p59_27T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b122 : Ban 55 5 v120 := viaCut p59_27 w11 (by decide) (by decide +kernel) (by decide +kernel)
def v122 : List ℕ := [t23,t95,t93,t25,t94,t27]
set_option maxHeartbeats 0 in
theorem b123 : Ban 55 5 v122 := viaSmall (by decide +kernel) (by decide)
def v123 : List ℕ := [t100,t23,t93,t25,t94,t27]
def v124 : List ℕ := [t101,t102,t103,t104]
set_option maxHeartbeats 0 in
theorem b124 : Ban 24 3 v124 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w12 : Wide 24 3 v124 := viaSub (ws := [v124]) (consBan b124 (nilBan 24 3)) (by decide) (by decide +kernel)
def p59_57Slow : Projection 55 24 := pick [0,1,4,6,7,8,9,10,22,23,26,28,29,30,31,32,44,45,48,50,51,52,53,54] rfl (by decide +kernel) (by decide)
def p59_57T : LookupTree := (.fork t23 t488 (.fork t113 t488 (.fork t115 t488 (.fork t100 t488 .empty .empty) .empty) (.fork t106 t488 (.fork t108 t488 .empty .empty) .empty)) (.fork t94 t103 (.fork t25 t102 (.fork t93 t101 .empty .empty) .empty) (.fork t27 t104 .empty .empty)))
set_option maxHeartbeats 0 in
def p59_57 : Projection 55 24 := cached p59_57Slow p59_57T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b125 : Ban 55 5 v123 := viaCut p59_57 w12 (by decide) (by decide +kernel) (by decide +kernel)
def v125 : List ℕ := [t23,t93,t25,t105,t94,t27]
set_option maxHeartbeats 0 in
theorem b126 : Ban 55 5 v125 := viaSmall (by decide +kernel) (by decide)
def v126 : List ℕ := [t106,t23,t93,t25,t94,t27]
set_option maxHeartbeats 0 in
theorem b127 : Ban 55 5 v126 := viaCut p59_57 w12 (by decide) (by decide +kernel) (by decide +kernel)
def v127 : List ℕ := [t23,t93,t107,t25,t94,t27]
set_option maxHeartbeats 0 in
theorem b128 : Ban 55 5 v127 := viaSmall (by decide +kernel) (by decide)
def v128 : List ℕ := [t108,t93,t25,t94,t27]
def v129 : List ℕ := [t109,t97,t98,t99]
set_option maxHeartbeats 0 in
theorem b129 : Ban 18 4 v129 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w13 : Wide 18 4 v129 := viaSub (ws := [v129]) (consBan b129 (nilBan 18 4)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b130 : Ban 55 5 v128 := viaCut p59_27 w13 (by decide) (by decide +kernel) (by decide +kernel)
def v130 : List ℕ := [t108,t23,t93,t25,t94,t27]
set_option maxHeartbeats 0 in
theorem b131 : Ban 55 5 v130 := viaCut p59_57 w12 (by decide) (by decide +kernel) (by decide +kernel)
def v131 : List ℕ := [t23,t93,t25,t110,t27]
def v132 : List ℕ := [t111,t97,t98,t112]
set_option maxHeartbeats 0 in
theorem b132 : Ban 18 4 v132 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w14 : Wide 18 4 v132 := viaSub (ws := [v132]) (consBan b132 (nilBan 18 4)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b133 : Ban 55 5 v131 := viaCut p59_27 w14 (by decide) (by decide +kernel) (by decide +kernel)
def v133 : List ℕ := [t23,t93,t25,t94,t110,t27]
set_option maxHeartbeats 0 in
theorem b134 : Ban 55 5 v133 := viaSmall (by decide +kernel) (by decide)
def v134 : List ℕ := [t113,t23,t93,t25,t94,t27]
set_option maxHeartbeats 0 in
theorem b135 : Ban 55 5 v134 := viaCut p59_57 w12 (by decide) (by decide +kernel) (by decide +kernel)
def v135 : List ℕ := [t93,t25,t114,t27]
set_option maxHeartbeats 0 in
theorem b136 : Ban 55 5 v135 := viaSmall (by decide +kernel) (by decide)
def v136 : List ℕ := [t23,t93,t25,t114,t27]
set_option maxHeartbeats 0 in
theorem b137 : Ban 55 5 v136 := viaSmall (by decide +kernel) (by decide)
def v137 : List ℕ := [t93,t25,t114,t94,t27]
set_option maxHeartbeats 0 in
theorem b138 : Ban 55 5 v137 := viaSmall (by decide +kernel) (by decide)
def v138 : List ℕ := [t23,t93,t25,t114,t94,t27]
set_option maxHeartbeats 0 in
theorem b139 : Ban 55 5 v138 := viaSmall (by decide +kernel) (by decide)
def v139 : List ℕ := [t115,t23,t93,t25,t94,t27]
set_option maxHeartbeats 0 in
theorem b140 : Ban 55 5 v139 := viaCut p59_57 w12 (by decide) (by decide +kernel) (by decide +kernel)
def v140 : List ℕ := [t93,t25,t94,t27,t116]
def v141 : List ℕ := [t111,t97,t98,t99]
set_option maxHeartbeats 0 in
theorem b141 : Ban 18 4 v141 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w15 : Wide 18 4 v141 := viaSub (ws := [v141]) (consBan b141 (nilBan 18 4)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b142 : Ban 55 5 v140 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v142 : List ℕ := [t23,t93,t25,t94,t27,t116]
set_option maxHeartbeats 0 in
theorem b143 : Ban 55 5 v142 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v143 : List ℕ := [t117,t93,t25,t94,t27]
set_option maxHeartbeats 0 in
theorem b144 : Ban 55 5 v143 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v144 : List ℕ := [t117,t23,t93,t25,t94,t27]
set_option maxHeartbeats 0 in
theorem b145 : Ban 55 5 v144 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v145 : List ℕ := [t23,t93,t25,t94,t118,t27]
set_option maxHeartbeats 0 in
theorem b146 : Ban 55 5 v145 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v146 : List ℕ := [t23,t119,t93,t25,t94,t27]
def v147 : List ℕ := [t111,t120,t97,t99]
def a27_3401Slow : Projection 18 18 := pick [0,4,6,8,1,7,2,5,3,9,13,15,17,10,16,11,14,12] rfl (by decide +kernel) (by decide)
def a27_3401T : LookupTree := (.fork t216 t215 (.fork t120 t109 (.fork t111 t98 (.fork t109 t120 (.fork t130 t132 .empty .empty) .empty) (.fork t138 t96 .empty .empty)) (.fork t215 t216 (.fork t96 t138 .empty .empty) (.fork t97 t99 .empty .empty))) (.fork t284 t281 (.fork t132 t130 (.fork t281 t284 .empty .empty) (.fork t98 t111 .empty .empty)) (.fork t99 t97 (.fork t122 t112 .empty .empty) (.fork t112 t122 .empty .empty))))
set_option maxHeartbeats 0 in
def a27_3401 : Projection 18 18 := cached a27_3401Slow a27_3401T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b147 : Ban 18 4 v147 := viaPerm a27_3401 a27_3401 b129 (by decide +kernel) (by decide +kernel)
def v148 : List ℕ := [t111,t120,t97,t98,t99]
set_option maxHeartbeats 0 in
theorem b148 : Ban 18 4 v148 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w16 : Wide 18 4 v148 := viaSub (ws := [v147,v141,v148]) (consBan b147 (consBan b141 (consBan b148 (nilBan 18 4)))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b149 : Ban 55 5 v146 := viaCut p59_27 w16 (by decide) (by decide +kernel) (by decide +kernel)
def v149 : List ℕ := [t23,t25,t121,t94,t27]
def v150 : List ℕ := [t111,t98,t122,t99]
set_option maxHeartbeats 0 in
theorem b150 : Ban 18 4 v150 := viaPerm a27_3401 a27_3401 b132 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w17 : Wide 18 4 v150 := viaSub (ws := [v150]) (consBan b150 (nilBan 18 4)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b151 : Ban 55 5 v149 := viaCut p59_27 w17 (by decide) (by decide +kernel) (by decide +kernel)
def v151 : List ℕ := [t23,t93,t25,t121,t94,t27]
def v152 : List ℕ := [t111,t97,t98,t122,t99]
set_option maxHeartbeats 0 in
theorem b152 : Ban 18 4 v152 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w18 : Wide 18 4 v152 := viaSub (ws := [v141,v150,v152]) (consBan b141 (consBan b150 (consBan b152 (nilBan 18 4)))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b153 : Ban 55 5 v151 := viaCut p59_27 w18 (by decide) (by decide +kernel) (by decide +kernel)
def v153 : List ℕ := [t23,t123,t25,t94,t27]
set_option maxHeartbeats 0 in
theorem b154 : Ban 55 5 v153 := viaSmall (by decide +kernel) (by decide)
def v154 : List ℕ := [t23,t123,t93,t25,t94,t27]
set_option maxHeartbeats 0 in
theorem b155 : Ban 55 5 v154 := viaSmall (by decide +kernel) (by decide)
def v155 : List ℕ := [t23,t93,t124,t25,t94,t27]
def v156 : List ℕ := [t111,t97,t125,t98,t99]
set_option maxHeartbeats 0 in
theorem b156 : Ban 18 4 v156 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w19 : Wide 18 4 v156 := viaSub (ws := [v141,v156]) (consBan b141 (consBan b156 (nilBan 18 4))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b157 : Ban 55 5 v155 := viaCut p59_27 w19 (by decide) (by decide +kernel) (by decide +kernel)
def v157 : List ℕ := [t23,t126,t93,t25,t27]
set_option maxHeartbeats 0 in
theorem b158 : Ban 55 5 v157 := viaSmall (by decide +kernel) (by decide)
def v158 : List ℕ := [t23,t126,t93,t25,t94,t27]
set_option maxHeartbeats 0 in
theorem b159 : Ban 55 5 v158 := viaSmall (by decide +kernel) (by decide)
def v159 : List ℕ := [t23,t93,t25,t94,t127,t27]
def v160 : List ℕ := [t111,t97,t98,t99,t128]
set_option maxHeartbeats 0 in
theorem b160 : Ban 18 4 v160 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w20 : Wide 18 4 v160 := viaSub (ws := [v141,v160]) (consBan b141 (consBan b160 (nilBan 18 4))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b161 : Ban 55 5 v159 := viaCut p59_27 w20 (by decide) (by decide +kernel) (by decide +kernel)
def v161 : List ℕ := [t129,t23,t93,t25,t27]
def v162 : List ℕ := [t130,t111,t97,t98]
set_option maxHeartbeats 0 in
theorem b162 : Ban 18 4 v162 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w21 : Wide 18 4 v162 := viaSub (ws := [v162]) (consBan b162 (nilBan 18 4)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b163 : Ban 55 5 v161 := viaCut p59_27 w21 (by decide) (by decide +kernel) (by decide +kernel)
def v163 : List ℕ := [t129,t23,t93,t25,t94,t27]
def v164 : List ℕ := [t130,t111,t97,t98,t99]
set_option maxHeartbeats 0 in
theorem b164 : Ban 18 4 v164 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w22 : Wide 18 4 v164 := viaSub (ws := [v162,v141,v164]) (consBan b162 (consBan b141 (consBan b164 (nilBan 18 4)))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b165 : Ban 55 5 v163 := viaCut p59_27 w22 (by decide) (by decide +kernel) (by decide +kernel)
def v165 : List ℕ := [t23,t93,t25,t131,t94,t27]
def v166 : List ℕ := [t111,t132,t98,t99]
set_option maxHeartbeats 0 in
theorem b166 : Ban 18 4 v166 := viaPerm a27_3401 a27_3401 b162 (by decide +kernel) (by decide +kernel)
def v167 : List ℕ := [t111,t97,t132,t98,t99]
set_option maxHeartbeats 0 in
theorem b167 : Ban 18 4 v167 := viaPerm a27_3401 a27_3401 b164 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w23 : Wide 18 4 v167 := viaSub (ws := [v141,v166,v167]) (consBan b141 (consBan b166 (consBan b167 (nilBan 18 4)))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b168 : Ban 55 5 v165 := viaCut p59_27 w23 (by decide) (by decide +kernel) (by decide +kernel)
def v168 : List ℕ := [t133,t23,t93,t25,t94,t27]
set_option maxHeartbeats 0 in
theorem b169 : Ban 55 5 v168 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v169 : List ℕ := [t23,t93,t25,t94,t27,t134]
set_option maxHeartbeats 0 in
theorem b170 : Ban 55 5 v169 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v170 : List ℕ := [t23,t135,t93,t25,t94,t27]
set_option maxHeartbeats 0 in
theorem b171 : Ban 55 5 v170 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v171 : List ℕ := [t23,t93,t25,t94,t136,t27]
set_option maxHeartbeats 0 in
theorem b172 : Ban 55 5 v171 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v172 : List ℕ := [t23,t93,t25,t137,t27]
set_option maxHeartbeats 0 in
theorem b173 : Ban 55 5 v172 := viaSmall (by decide +kernel) (by decide)
def v173 : List ℕ := [t23,t93,t137,t94,t27]
def v174 : List ℕ := [t111,t138,t97,t99]
set_option maxHeartbeats 0 in
theorem b174 : Ban 18 4 v174 := viaPerm a27_3401 a27_3401 b121 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w24 : Wide 18 4 v174 := viaSub (ws := [v174]) (consBan b174 (nilBan 18 4)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b175 : Ban 55 5 v173 := viaCut p59_27 w24 (by decide) (by decide +kernel) (by decide +kernel)
def v175 : List ℕ := [t23,t93,t25,t137,t94,t27]
set_option maxHeartbeats 0 in
theorem b176 : Ban 55 5 v175 := viaSmall (by decide +kernel) (by decide)
def v176 : List ℕ := [t139,t23,t93,t25,t94,t27]
set_option maxHeartbeats 0 in
theorem b177 : Ban 55 5 v176 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v177 : List ℕ := [t23,t93,t25,t94,t27,t140]
set_option maxHeartbeats 0 in
theorem b178 : Ban 55 5 v177 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v178 : List ℕ := [t23,t93,t141,t25,t94,t27]
set_option maxHeartbeats 0 in
theorem b179 : Ban 55 5 v178 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v179 : List ℕ := [t23,t93,t25,t94,t142,t27]
set_option maxHeartbeats 0 in
theorem b180 : Ban 55 5 v179 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v180 : List ℕ := [t23,t93,t25,t143,t94,t27]
set_option maxHeartbeats 0 in
theorem b181 : Ban 55 5 v180 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v181 : List ℕ := [t23,t93,t25,t27,t144]
set_option maxHeartbeats 0 in
theorem b182 : Ban 55 5 v181 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v182 : List ℕ := [t23,t93,t25,t94,t27,t144]
set_option maxHeartbeats 0 in
theorem b183 : Ban 55 5 v182 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v183 : List ℕ := [t23,t93,t25,t145,t27]
set_option maxHeartbeats 0 in
theorem b184 : Ban 55 5 v183 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v184 : List ℕ := [t23,t93,t25,t145,t94,t27]
set_option maxHeartbeats 0 in
theorem b185 : Ban 55 5 v184 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
def v185 : List ℕ := [t23,t93,t25,t146,t94,t27]
set_option maxHeartbeats 0 in
theorem b186 : Ban 55 5 v185 := viaCut p59_27 w15 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b187 : Ban 55 6 v118 := viaBranch (ws := [v119,v120,v122,v123,v125,v126,v127,v128,v130,v131,v133,v134,v135,v136,v137,v138,v139,v140,v142,v143,v144,v145,v146,v149,v151,v153,v154,v155,v157,v158,v159,v161,v163,v165,v168,v169,v170,v171,v172,v173,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184,v185]) (consBan b120 (consBan b122 (consBan b123 (consBan b125 (consBan b126 (consBan b127 (consBan b128 (consBan b130 (consBan b131 (consBan b133 (consBan b134 (consBan b135 (consBan b136 (consBan b137 (consBan b138 (consBan b139 (consBan b140 (consBan b142 (consBan b143 (consBan b144 (consBan b145 (consBan b146 (consBan b149 (consBan b151 (consBan b153 (consBan b154 (consBan b155 (consBan b157 (consBan b158 (consBan b159 (consBan b161 (consBan b163 (consBan b165 (consBan b168 (consBan b169 (consBan b170 (consBan b171 (consBan b172 (consBan b173 (consBan b175 (consBan b176 (consBan b177 (consBan b178 (consBan b179 (consBan b180 (consBan b181 (consBan b182 (consBan b183 (consBan b184 (consBan b185 (consBan b186 (nilBan 55 5)))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w25 : Wide 55 6 v118 := viaSub (ws := [v118]) (consBan b187 (nilBan 55 6)) (by decide) (by decide +kernel)
def p127_59Slow : Projection 228 55 := pick [0,1,2,3,8,9,12,13,14,15,16,19,20,21,22,27,28,31,32,33,34,35,57,58,59,60,65,66,69,70,71,72,73,76,77,78,79,84,85,88,89,90,91,92,114,115,116,117,122,123,126,127,128,129,130] rfl (by decide +kernel) (by decide)
def p127_59T : LookupTree := (.fork t440 t144 (.fork t159 t25 (.fork t184 t23 (.fork t0 t23 (.fork t190 t23 .empty .empty) .empty) (.fork t12 t93 (.fork t1 t24 .empty .empty) .empty)) (.fork t92 t94 (.fork t22 t167 (.fork t2 t25 .empty .empty) .empty) (.fork t273 t274 (.fork t4 t27 .empty .empty) .empty))) (.fork t241 t488 (.fork t181 t488 (.fork t40 t23 (.fork t5 t488 .empty .empty) .empty) (.fork t189 t23 (.fork t6 t488 .empty .empty) .empty)) (.fork t448 t94 (.fork t158 t25 (.fork t183 t23 .empty .empty) .empty) (.fork t179 t27 .empty .empty))))
set_option maxHeartbeats 0 in
def p127_59 : Projection 228 55 := cached p127_59Slow p127_59T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b188 : Ban 228 7 v117 := viaCut p127_59 w25 (by decide) (by decide +kernel) (by decide +kernel)
def v186 : List ℕ := [t12,t3,t92,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b189 : Ban 228 7 v186 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v187 : List ℕ := [t12,t2,t3,t92,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b190 : Ban 228 7 v187 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v188 : List ℕ := [t12,t147,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b191 : Ban 228 7 v188 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v189 : List ℕ := [t12,t147,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b192 : Ban 228 7 v189 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v190 : List ℕ := [t12,t2,t148,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b193 : Ban 228 7 v190 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v191 : List ℕ := [t12,t2,t148,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b194 : Ban 228 7 v191 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v192 : List ℕ := [t149,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b195 : Ban 228 7 v192 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v193 : List ℕ := [t12,t2,t3,t4,t150,t40,t6]
set_option maxHeartbeats 0 in
theorem b196 : Ban 228 7 v193 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v194 : List ℕ := [t12,t151,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b197 : Ban 228 7 v194 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v195 : List ℕ := [t12,t2,t3,t152,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b198 : Ban 228 7 v195 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v196 : List ℕ := [t153,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b199 : Ban 228 7 v196 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v197 : List ℕ := [t12,t2,t3,t4,t40,t154,t6]
set_option maxHeartbeats 0 in
theorem b200 : Ban 228 7 v197 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v198 : List ℕ := [t12,t155,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b201 : Ban 228 7 v198 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v199 : List ℕ := [t12,t2,t3,t4,t156,t40,t6]
set_option maxHeartbeats 0 in
theorem b202 : Ban 228 7 v199 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v200 : List ℕ := [t157,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b203 : Ban 228 7 v200 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v201 : List ℕ := [t12,t2,t3,t4,t40,t6,t158]
set_option maxHeartbeats 0 in
theorem b204 : Ban 228 7 v201 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v202 : List ℕ := [t12,t159,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b205 : Ban 228 7 v202 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v203 : List ℕ := [t12,t2,t3,t4,t40,t160,t6]
set_option maxHeartbeats 0 in
theorem b206 : Ban 228 7 v203 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v204 : List ℕ := [t12,t2,t161,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b207 : Ban 228 7 v204 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v205 : List ℕ := [t12,t2,t3,t162,t40,t6]
set_option maxHeartbeats 0 in
theorem b208 : Ban 228 7 v205 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v206 : List ℕ := [t12,t2,t4,t162,t40,t6]
set_option maxHeartbeats 0 in
theorem b209 : Ban 228 7 v206 := viaCut p127_91 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v207 : List ℕ := [t12,t2,t3,t4,t162,t40,t6]
set_option maxHeartbeats 0 in
theorem b210 : Ban 228 7 v207 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v208 : List ℕ := [t12,t163,t2,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b211 : Ban 228 7 v208 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v209 : List ℕ := [t12,t163,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b212 : Ban 228 7 v209 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v210 : List ℕ := [t12,t2,t164,t3,t40,t6]
set_option maxHeartbeats 0 in
theorem b213 : Ban 228 7 v210 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v211 : List ℕ := [t12,t2,t164,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b214 : Ban 228 7 v211 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v212 : List ℕ := [t165,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b215 : Ban 228 7 v212 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v213 : List ℕ := [t12,t2,t4,t40,t166,t6]
def v214 : List ℕ := [t23,t24,t25,t167,t27]
set_option maxHeartbeats 0 in
theorem b216 : Ban 55 6 v214 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w26 : Wide 55 6 v214 := viaSub (ws := [v214]) (consBan b216 (nilBan 55 6)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b217 : Ban 228 7 v213 := viaCut p127_61 w26 (by decide) (by decide +kernel) (by decide +kernel)
def v215 : List ℕ := [t12,t2,t3,t4,t40,t166,t6]
set_option maxHeartbeats 0 in
theorem b218 : Ban 228 7 v215 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v216 : List ℕ := [t12,t2,t168,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b219 : Ban 228 7 v216 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v217 : List ℕ := [t12,t2,t168,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b220 : Ban 228 7 v217 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v218 : List ℕ := [t12,t2,t3,t4,t169,t40,t6]
set_option maxHeartbeats 0 in
theorem b221 : Ban 228 7 v218 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v219 : List ℕ := [t170,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b222 : Ban 228 7 v219 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v220 : List ℕ := [t12,t2,t3,t4,t40,t6,t171]
set_option maxHeartbeats 0 in
theorem b223 : Ban 228 7 v220 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v221 : List ℕ := [t12,t2,t172,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b224 : Ban 228 7 v221 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v222 : List ℕ := [t12,t2,t3,t4,t40,t173,t6]
set_option maxHeartbeats 0 in
theorem b225 : Ban 228 7 v222 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v223 : List ℕ := [t174,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b226 : Ban 228 7 v223 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v224 : List ℕ := [t12,t2,t3,t4,t40,t175,t6]
set_option maxHeartbeats 0 in
theorem b227 : Ban 228 7 v224 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v225 : List ℕ := [t12,t2,t3,t176,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b228 : Ban 228 7 v225 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v226 : List ℕ := [t12,t2,t3,t4,t177,t40,t6]
set_option maxHeartbeats 0 in
theorem b229 : Ban 228 7 v226 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v227 : List ℕ := [t178,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b230 : Ban 228 7 v227 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v228 : List ℕ := [t12,t2,t3,t4,t40,t6,t179]
set_option maxHeartbeats 0 in
theorem b231 : Ban 228 7 v228 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v229 : List ℕ := [t12,t2,t3,t180,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b232 : Ban 228 7 v229 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v230 : List ℕ := [t12,t2,t3,t4,t40,t181,t6]
set_option maxHeartbeats 0 in
theorem b233 : Ban 228 7 v230 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v231 : List ℕ := [t12,t2,t3,t4,t182,t40,t6]
set_option maxHeartbeats 0 in
theorem b234 : Ban 228 7 v231 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v232 : List ℕ := [t12,t2,t3,t4,t6,t183]
set_option maxHeartbeats 0 in
theorem b235 : Ban 228 7 v232 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v233 : List ℕ := [t12,t2,t3,t4,t40,t6,t183]
set_option maxHeartbeats 0 in
theorem b236 : Ban 228 7 v233 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v234 : List ℕ := [t184,t12,t2,t3,t4,t6]
set_option maxHeartbeats 0 in
theorem b237 : Ban 228 7 v234 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v235 : List ℕ := [t184,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b238 : Ban 228 7 v235 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v236 : List ℕ := [t12,t2,t3,t4,t185,t40,t6]
set_option maxHeartbeats 0 in
theorem b239 : Ban 228 7 v236 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b240 : Ban 228 8 v27 := viaBranch (ws := [v28,v29,v31,v33,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236]) (consBan b26 (consBan b28 (consBan b30 (consBan b100 (consBan b101 (consBan b102 (consBan b103 (consBan b104 (consBan b105 (consBan b106 (consBan b107 (consBan b108 (consBan b109 (consBan b110 (consBan b111 (consBan b112 (consBan b113 (consBan b114 (consBan b115 (consBan b116 (consBan b117 (consBan b118 (consBan b119 (consBan b188 (consBan b189 (consBan b190 (consBan b191 (consBan b192 (consBan b193 (consBan b194 (consBan b195 (consBan b196 (consBan b197 (consBan b198 (consBan b199 (consBan b200 (consBan b201 (consBan b202 (consBan b203 (consBan b204 (consBan b205 (consBan b206 (consBan b207 (consBan b208 (consBan b209 (consBan b210 (consBan b211 (consBan b212 (consBan b213 (consBan b214 (consBan b215 (consBan b217 (consBan b218 (consBan b219 (consBan b220 (consBan b221 (consBan b222 (consBan b223 (consBan b224 (consBan b225 (consBan b226 (consBan b227 (consBan b228 (consBan b229 (consBan b230 (consBan b231 (consBan b232 (consBan b233 (consBan b234 (consBan b235 (consBan b236 (consBan b237 (consBan b238 (consBan b239 (nilBan 228 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
def v237 : List ℕ := [t0,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b241 : Ban 228 8 v237 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v238 : List ℕ := [t12,t2,t3,t4,t5,t40,t6]
set_option maxHeartbeats 0 in
theorem b242 : Ban 228 8 v238 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v239 : List ℕ := [t0,t12,t2,t3,t4,t5,t40,t6]
set_option maxHeartbeats 0 in
theorem b243 : Ban 228 8 v239 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v240 : List ℕ := [t186,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b244 : Ban 228 8 v240 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v241 : List ℕ := [t186,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b245 : Ban 228 8 v241 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v242 : List ℕ := [t0,t12,t2,t3,t4,t187,t6]
set_option maxHeartbeats 0 in
theorem b246 : Ban 228 8 v242 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v243 : List ℕ := [t0,t12,t2,t3,t4,t187,t5,t6]
set_option maxHeartbeats 0 in
theorem b247 : Ban 228 8 v243 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v244 : List ℕ := [t188,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b248 : Ban 228 8 v244 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v245 : List ℕ := [t12,t2,t3,t4,t5,t6,t189]
set_option maxHeartbeats 0 in
theorem b249 : Ban 228 8 v245 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v246 : List ℕ := [t0,t12,t2,t3,t4,t5,t6,t189]
set_option maxHeartbeats 0 in
theorem b250 : Ban 228 8 v246 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v247 : List ℕ := [t190,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b251 : Ban 228 8 v247 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v248 : List ℕ := [t190,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b252 : Ban 228 8 v248 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v249 : List ℕ := [t0,t12,t2,t3,t4,t5,t191,t6]
set_option maxHeartbeats 0 in
theorem b253 : Ban 228 8 v249 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v250 : List ℕ := [t0,t41,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b254 : Ban 228 8 v250 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v251 : List ℕ := [t0,t2,t42,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b255 : Ban 228 8 v251 := viaCut p127_91 w5 (by decide) (by decide +kernel) (by decide +kernel)
def v252 : List ℕ := [t0,t12,t2,t42,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b256 : Ban 228 8 v252 := viaCut p127_91 w6 (by decide) (by decide +kernel) (by decide +kernel)
def v253 : List ℕ := [t0,t44,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b257 : Ban 228 8 v253 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v254 : List ℕ := [t0,t44,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b258 : Ban 228 8 v254 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v255 : List ℕ := [t0,t12,t74,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b259 : Ban 228 8 v255 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v256 : List ℕ := [t75,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b260 : Ban 228 8 v256 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v257 : List ℕ := [t0,t12,t2,t3,t76,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b261 : Ban 228 8 v257 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v258 : List ℕ := [t0,t77,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b262 : Ban 228 8 v258 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v259 : List ℕ := [t0,t12,t2,t78,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b263 : Ban 228 8 v259 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v260 : List ℕ := [t79,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b264 : Ban 228 8 v260 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v261 : List ℕ := [t0,t12,t2,t3,t4,t80,t5,t6]
set_option maxHeartbeats 0 in
theorem b265 : Ban 228 8 v261 := viaCut p127_91 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v262 : List ℕ := [t0,t81,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b266 : Ban 228 8 v262 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v263 : List ℕ := [t0,t12,t2,t3,t82,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b267 : Ban 228 8 v263 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v264 : List ℕ := [t192,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b268 : Ban 228 8 v264 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v265 : List ℕ := [t0,t12,t2,t3,t4,t84,t6]
def v266 : List ℕ := [t24,t93,t25,t26,t27]
def v267 : List ℕ := [t193,t24,t25,t26,t27]
def p61_52Slow : Projection 55 12 := pick [11,13,17,20,33,35,39,42,44,46,50,53] rfl (by decide +kernel) (by decide)
def p61_52T : LookupTree := (.fork t197 t16 (.fork t200 t488 (.fork t193 t15 (.fork t196 t488 (.fork t202 t488 (.fork t198 t488 .empty .empty) .empty) (.fork t211 t488 .empty .empty)) (.fork t194 t488 (.fork t123 t73 .empty .empty) (.fork t208 t488 .empty .empty))) (.fork t219 t16 (.fork t135 t217 (.fork t213 t15 (.fork t24 t488 .empty .empty) .empty) (.fork t93 t15 .empty .empty)) (.fork t225 t488 (.fork t218 t488 .empty .empty) (.fork t124 t210 .empty .empty)))) (.fork t26 t488 (.fork t223 t488 (.fork t195 t16 (.fork t25 t16 (.fork t141 t222 .empty .empty) .empty) (.fork t226 t17 .empty .empty)) (.fork t214 t488 (.fork t137 t488 .empty .empty) (.fork t201 t488 .empty .empty))) (.fork t209 t17 (.fork t212 t15 (.fork t199 t488 .empty .empty) (.fork t94 t16 .empty .empty)) (.fork t203 t17 (.fork t27 t17 .empty .empty) (.fork t224 t17 .empty .empty)))))
set_option maxHeartbeats 0 in
def p61_52 : Projection 55 12 := cached p61_52Slow p61_52T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b269 : Ban 55 5 v267 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v268 : List ℕ := [t193,t93,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b270 : Ban 55 5 v268 := viaSmall (by decide +kernel) (by decide)
def v269 : List ℕ := [t193,t24,t93,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b271 : Ban 55 5 v269 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v270 : List ℕ := [t194,t24,t93,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b272 : Ban 55 5 v270 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v271 : List ℕ := [t24,t93,t195,t26,t27]
set_option maxHeartbeats 0 in
theorem b273 : Ban 55 5 v271 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v272 : List ℕ := [t24,t93,t25,t195,t26,t27]
set_option maxHeartbeats 0 in
theorem b274 : Ban 55 5 v272 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v273 : List ℕ := [t196,t24,t93,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b275 : Ban 55 5 v273 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v274 : List ℕ := [t24,t93,t197,t26,t27]
set_option maxHeartbeats 0 in
theorem b276 : Ban 55 5 v274 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v275 : List ℕ := [t24,t93,t197,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b277 : Ban 55 5 v275 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v276 : List ℕ := [t198,t24,t93,t25,t27]
set_option maxHeartbeats 0 in
theorem b278 : Ban 55 5 v276 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v277 : List ℕ := [t198,t24,t93,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b279 : Ban 55 5 v277 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v278 : List ℕ := [t24,t93,t25,t26,t199,t27]
set_option maxHeartbeats 0 in
theorem b280 : Ban 55 5 v278 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v279 : List ℕ := [t200,t24,t93,t25,t27]
set_option maxHeartbeats 0 in
theorem b281 : Ban 55 5 v279 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v280 : List ℕ := [t200,t24,t93,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b282 : Ban 55 5 v280 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v281 : List ℕ := [t24,t93,t25,t201,t26,t27]
set_option maxHeartbeats 0 in
theorem b283 : Ban 55 5 v281 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v282 : List ℕ := [t202,t24,t93,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b284 : Ban 55 5 v282 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v283 : List ℕ := [t93,t25,t26,t27,t203]
def v284 : List ℕ := [t204,t205,t206,t207]
set_option maxHeartbeats 0 in
theorem b285 : Ban 28 4 v284 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w27 : Wide 28 4 v284 := viaSub (ws := [v284]) (consBan b285 (nilBan 28 4)) (by decide) (by decide +kernel)
def p61_53Slow : Projection 55 28 := pick [11,12,13,14,17,18,20,22,23,24,25,28,29,31,33,34,35,36,39,40,42,44,45,46,47,50,51,53] rfl (by decide +kernel) (by decide)
def p61_53T : LookupTree := (.fork t26 t488 (.fork t93 t204 (.fork t24 t220 .empty .empty) (.fork t25 t205 .empty .empty)) (.fork t203 t207 (.fork t27 t206 .empty .empty) (.fork t140 t221 .empty .empty)))
set_option maxHeartbeats 0 in
def p61_53 : Projection 55 28 := cached p61_53Slow p61_53T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b286 : Ban 55 5 v283 := viaCut p61_53 w27 (by decide) (by decide +kernel) (by decide +kernel)
def v285 : List ℕ := [t24,t93,t25,t26,t27,t203]
set_option maxHeartbeats 0 in
theorem b287 : Ban 55 5 v285 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v286 : List ℕ := [t208,t93,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b288 : Ban 55 5 v286 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v287 : List ℕ := [t208,t24,t93,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b289 : Ban 55 5 v287 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v288 : List ℕ := [t24,t93,t25,t26,t209,t27]
set_option maxHeartbeats 0 in
theorem b290 : Ban 55 5 v288 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v289 : List ℕ := [t119,t24,t93,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b291 : Ban 55 5 v289 := viaSmall (by decide +kernel) (by decide)
def v290 : List ℕ := [t24,t93,t25,t121,t26,t27]
set_option maxHeartbeats 0 in
theorem b292 : Ban 55 5 v290 := viaSmall (by decide +kernel) (by decide)
def v291 : List ℕ := [t123,t24,t93,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b293 : Ban 12 3 v89 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w28 : Wide 12 3 v89 := viaSub (ws := [v8,v89]) (consBan b5 (consBan b293 (nilBan 12 3))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b294 : Ban 55 5 v291 := viaCut p61_52 w28 (by decide) (by decide +kernel) (by decide +kernel)
def v292 : List ℕ := [t24,t93,t124,t25,t26,t27]
def v293 : List ℕ := [t15,t210,t16,t17]
set_option maxHeartbeats 0 in
theorem b295 : Ban 12 3 v293 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w29 : Wide 12 3 v293 := viaSub (ws := [v8,v293]) (consBan b5 (consBan b295 (nilBan 12 3))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b296 : Ban 55 5 v292 := viaCut p61_52 w29 (by decide) (by decide +kernel) (by decide +kernel)
def v294 : List ℕ := [t211,t24,t93,t25,t27]
set_option maxHeartbeats 0 in
theorem b297 : Ban 55 5 v294 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v295 : List ℕ := [t211,t24,t93,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b298 : Ban 55 5 v295 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v296 : List ℕ := [t24,t25,t26,t212,t27]
set_option maxHeartbeats 0 in
theorem b299 : Ban 55 5 v296 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v297 : List ℕ := [t24,t93,t25,t26,t212,t27]
set_option maxHeartbeats 0 in
theorem b300 : Ban 55 5 v297 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v298 : List ℕ := [t24,t213,t25,t27]
set_option maxHeartbeats 0 in
theorem b301 : Ban 55 5 v298 := viaSmall (by decide +kernel) (by decide)
def v299 : List ℕ := [t24,t213,t93,t25,t27]
set_option maxHeartbeats 0 in
theorem b302 : Ban 55 5 v299 := viaSmall (by decide +kernel) (by decide)
def v300 : List ℕ := [t24,t213,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b303 : Ban 55 5 v300 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v301 : List ℕ := [t24,t213,t93,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b304 : Ban 55 5 v301 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v302 : List ℕ := [t24,t93,t25,t214,t26,t27]
set_option maxHeartbeats 0 in
theorem b305 : Ban 55 5 v302 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v303 : List ℕ := [t133,t24,t93,t25,t26,t27]
def v304 : List ℕ := [t215,t97,t216,t98]
set_option maxHeartbeats 0 in
theorem b306 : Ban 18 3 v304 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w30 : Wide 18 3 v304 := viaSub (ws := [v304]) (consBan b306 (nilBan 18 3)) (by decide) (by decide +kernel)
def p61_29Slow : Projection 55 18 := pick [0,1,2,3,4,5,6,7,8,11,12,13,14,15,16,17,18,19] rfl (by decide +kernel) (by decide)
def p61_29T : LookupTree := (.fork t26 t216 (.fork t24 t215 (.fork t139 t488 (.fork t133 t488 .empty .empty) .empty) (.fork t25 t98 (.fork t93 t97 .empty .empty) .empty)) (.fork t136 t488 (.fork t142 t488 (.fork t94 t99 .empty .empty) .empty) (.fork t27 t488 .empty .empty)))
set_option maxHeartbeats 0 in
def p61_29 : Projection 55 18 := cached p61_29Slow p61_29T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b307 : Ban 55 5 v303 := viaCut p61_29 w30 (by decide) (by decide +kernel) (by decide +kernel)
def v305 : List ℕ := [t24,t93,t25,t26,t27,t134]
set_option maxHeartbeats 0 in
theorem b308 : Ban 55 5 v305 := viaSmall (by decide +kernel) (by decide)
def v306 : List ℕ := [t24,t135,t93,t25,t26,t27]
def v307 : List ℕ := [t217,t15,t16,t17]
set_option maxHeartbeats 0 in
theorem b309 : Ban 12 3 v307 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w31 : Wide 12 3 v307 := viaSub (ws := [v8,v307]) (consBan b5 (consBan b309 (nilBan 12 3))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b310 : Ban 55 5 v306 := viaCut p61_52 w31 (by decide) (by decide +kernel) (by decide +kernel)
def v308 : List ℕ := [t24,t93,t25,t26,t136,t27]
set_option maxHeartbeats 0 in
theorem b311 : Ban 55 5 v308 := viaCut p61_29 w30 (by decide) (by decide +kernel) (by decide +kernel)
def v309 : List ℕ := [t24,t93,t218,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b312 : Ban 55 5 v309 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v310 : List ℕ := [t24,t93,t25,t94,t27]
def v311 : List ℕ := [t215,t97,t98,t99]
set_option maxHeartbeats 0 in
theorem b313 : Ban 18 4 v311 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w32 : Wide 18 4 v311 := viaSub (ws := [v311]) (consBan b313 (nilBan 18 4)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b314 : Ban 55 5 v310 := viaCut p61_29 w32 (by decide) (by decide +kernel) (by decide +kernel)
def v312 : List ℕ := [t24,t93,t26,t94,t27]
set_option maxHeartbeats 0 in
theorem b315 : Ban 55 5 v312 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v313 : List ℕ := [t24,t93,t25,t26,t94,t27]
set_option maxHeartbeats 0 in
theorem b316 : Ban 55 5 v313 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v314 : List ℕ := [t24,t93,t219,t26,t27]
set_option maxHeartbeats 0 in
theorem b317 : Ban 55 5 v314 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v315 : List ℕ := [t24,t93,t219,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b318 : Ban 55 5 v315 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v316 : List ℕ := [t24,t93,t25,t137,t27]
set_option maxHeartbeats 0 in
theorem b319 : Ban 55 5 v316 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v317 : List ℕ := [t24,t93,t25,t137,t26,t27]
set_option maxHeartbeats 0 in
theorem b320 : Ban 55 5 v317 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v318 : List ℕ := [t139,t24,t93,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b321 : Ban 55 5 v318 := viaCut p61_29 w30 (by decide) (by decide +kernel) (by decide +kernel)
def v319 : List ℕ := [t24,t93,t25,t26,t27,t140]
def v320 : List ℕ := [t220,t204,t205,t206]
def p53_52Slow : Projection 28 12 := pick [0,2,4,6,14,16,18,20,21,23,25,27] rfl (by decide +kernel) (by decide)
def p53_52T : LookupTree := (.fork t205 t16 (.fork t204 t15 (.fork t220 t488 .empty .empty) .empty) (.fork t206 t17 .empty .empty))
set_option maxHeartbeats 0 in
def p53_52 : Projection 28 12 := cached p53_52Slow p53_52T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b322 : Ban 28 4 v320 := viaCut p53_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v321 : List ℕ := [t220,t204,t205,t206,t221]
set_option maxHeartbeats 0 in
theorem b323 : Ban 28 4 v321 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w33 : Wide 28 4 v321 := viaSub (ws := [v320,v321]) (consBan b322 (consBan b323 (nilBan 28 4))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b324 : Ban 55 5 v319 := viaCut p61_53 w33 (by decide) (by decide +kernel) (by decide +kernel)
def v322 : List ℕ := [t24,t93,t141,t25,t26,t27]
def v323 : List ℕ := [t15,t222,t16,t17]
set_option maxHeartbeats 0 in
theorem b325 : Ban 12 3 v323 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w34 : Wide 12 3 v323 := viaSub (ws := [v8,v323]) (consBan b5 (consBan b325 (nilBan 12 3))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b326 : Ban 55 5 v322 := viaCut p61_52 w34 (by decide) (by decide +kernel) (by decide +kernel)
def v324 : List ℕ := [t24,t93,t25,t26,t142,t27]
set_option maxHeartbeats 0 in
theorem b327 : Ban 55 5 v324 := viaCut p61_29 w30 (by decide) (by decide +kernel) (by decide +kernel)
def v325 : List ℕ := [t24,t93,t25,t223,t26,t27]
set_option maxHeartbeats 0 in
theorem b328 : Ban 55 5 v325 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v326 : List ℕ := [t24,t93,t25,t26,t224]
set_option maxHeartbeats 0 in
theorem b329 : Ban 55 5 v326 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v327 : List ℕ := [t24,t93,t25,t27,t224]
set_option maxHeartbeats 0 in
theorem b330 : Ban 55 5 v327 := viaSmall (by decide +kernel) (by decide)
def v328 : List ℕ := [t24,t93,t25,t26,t27,t224]
set_option maxHeartbeats 0 in
theorem b331 : Ban 55 5 v328 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v329 : List ℕ := [t24,t93,t225,t25,t27]
set_option maxHeartbeats 0 in
theorem b332 : Ban 55 5 v329 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v330 : List ℕ := [t24,t93,t225,t25,t26,t27]
set_option maxHeartbeats 0 in
theorem b333 : Ban 55 5 v330 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v331 : List ℕ := [t24,t93,t25,t226,t26]
set_option maxHeartbeats 0 in
theorem b334 : Ban 55 5 v331 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v332 : List ℕ := [t24,t93,t25,t226,t26,t27]
set_option maxHeartbeats 0 in
theorem b335 : Ban 55 5 v332 := viaCut p61_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b336 : Ban 55 6 v266 := viaBranch (ws := [v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v285,v286,v287,v288,v289,v290,v291,v292,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v305,v306,v308,v309,v310,v312,v313,v314,v315,v316,v317,v318,v319,v322,v324,v325,v326,v327,v328,v329,v330,v331,v332]) (consBan b269 (consBan b270 (consBan b271 (consBan b272 (consBan b273 (consBan b274 (consBan b275 (consBan b276 (consBan b277 (consBan b278 (consBan b279 (consBan b280 (consBan b281 (consBan b282 (consBan b283 (consBan b284 (consBan b286 (consBan b287 (consBan b288 (consBan b289 (consBan b290 (consBan b291 (consBan b292 (consBan b294 (consBan b296 (consBan b297 (consBan b298 (consBan b299 (consBan b300 (consBan b301 (consBan b302 (consBan b303 (consBan b304 (consBan b305 (consBan b307 (consBan b308 (consBan b310 (consBan b311 (consBan b312 (consBan b314 (consBan b315 (consBan b316 (consBan b317 (consBan b318 (consBan b319 (consBan b320 (consBan b321 (consBan b324 (consBan b326 (consBan b327 (consBan b328 (consBan b329 (consBan b330 (consBan b331 (consBan b332 (consBan b333 (consBan b334 (consBan b335 (nilBan 55 5))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w35 : Wide 55 6 v266 := viaSub (ws := [v266]) (consBan b336 (nilBan 55 6)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b337 : Ban 228 8 v265 := viaCut p127_61 w35 (by decide) (by decide +kernel) (by decide +kernel)
def v333 : List ℕ := [t0,t2,t3,t4,t5,t84,t6]
set_option maxHeartbeats 0 in
theorem b338 : Ban 228 8 v333 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v334 : List ℕ := [t0,t12,t2,t3,t4,t5,t84,t6]
set_option maxHeartbeats 0 in
theorem b339 : Ban 228 8 v334 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v335 : List ℕ := [t0,t227,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b340 : Ban 228 8 v335 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v336 : List ℕ := [t0,t227,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b341 : Ban 228 8 v336 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v337 : List ℕ := [t0,t12,t2,t3,t4,t86,t6]
set_option maxHeartbeats 0 in
theorem b342 : Ban 228 8 v337 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v338 : List ℕ := [t0,t12,t2,t3,t4,t86,t5,t6]
set_option maxHeartbeats 0 in
theorem b343 : Ban 228 8 v338 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v339 : List ℕ := [t87,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b344 : Ban 228 8 v339 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v340 : List ℕ := [t0,t12,t2,t3,t4,t5,t6,t88]
set_option maxHeartbeats 0 in
theorem b345 : Ban 228 8 v340 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v341 : List ℕ := [t0,t89,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b346 : Ban 228 8 v341 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v342 : List ℕ := [t0,t12,t2,t3,t4,t5,t90,t6]
set_option maxHeartbeats 0 in
theorem b347 : Ban 228 8 v342 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v343 : List ℕ := [t0,t12,t91,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b348 : Ban 228 8 v343 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v344 : List ℕ := [t0,t12,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b349 : Ban 228 8 v344 := viaCut p127_59 w25 (by decide) (by decide +kernel) (by decide +kernel)
def v345 : List ℕ := [t0,t12,t3,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b350 : Ban 228 8 v345 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v346 : List ℕ := [t0,t12,t2,t3,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b351 : Ban 228 8 v346 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v347 : List ℕ := [t0,t12,t147,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b352 : Ban 228 8 v347 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v348 : List ℕ := [t0,t12,t147,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b353 : Ban 228 8 v348 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v349 : List ℕ := [t0,t12,t2,t148,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b354 : Ban 228 8 v349 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v350 : List ℕ := [t0,t12,t2,t148,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b355 : Ban 228 8 v350 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v351 : List ℕ := [t149,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b356 : Ban 228 8 v351 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v352 : List ℕ := [t0,t12,t2,t3,t4,t150,t5,t6]
set_option maxHeartbeats 0 in
theorem b357 : Ban 228 8 v352 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v353 : List ℕ := [t0,t12,t151,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b358 : Ban 228 8 v353 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v354 : List ℕ := [t0,t12,t2,t3,t152,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b359 : Ban 228 8 v354 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v355 : List ℕ := [t228,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b360 : Ban 228 8 v355 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v356 : List ℕ := [t0,t12,t2,t3,t4,t5,t229,t6]
set_option maxHeartbeats 0 in
theorem b361 : Ban 228 8 v356 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v357 : List ℕ := [t0,t12,t230,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b362 : Ban 228 8 v357 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v358 : List ℕ := [t0,t12,t2,t3,t4,t231,t5,t6]
set_option maxHeartbeats 0 in
theorem b363 : Ban 228 8 v358 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v359 : List ℕ := [t157,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b364 : Ban 228 8 v359 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v360 : List ℕ := [t0,t12,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b365 : Ban 228 8 v360 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v361 : List ℕ := [t0,t12,t159,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b366 : Ban 228 8 v361 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v362 : List ℕ := [t0,t12,t2,t3,t4,t5,t160,t6]
set_option maxHeartbeats 0 in
theorem b367 : Ban 228 8 v362 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v363 : List ℕ := [t0,t12,t2,t161,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b368 : Ban 228 8 v363 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v364 : List ℕ := [t0,t12,t2,t3,t162,t5,t6]
set_option maxHeartbeats 0 in
theorem b369 : Ban 228 8 v364 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v365 : List ℕ := [t0,t12,t2,t4,t162,t5,t6]
set_option maxHeartbeats 0 in
theorem b370 : Ban 228 8 v365 := viaCut p127_91 w4 (by decide) (by decide +kernel) (by decide +kernel)
def v366 : List ℕ := [t0,t12,t2,t3,t4,t162,t5,t6]
set_option maxHeartbeats 0 in
theorem b371 : Ban 228 8 v366 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v367 : List ℕ := [t0,t12,t163,t2,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b372 : Ban 228 8 v367 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v368 : List ℕ := [t0,t12,t163,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b373 : Ban 228 8 v368 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v369 : List ℕ := [t0,t12,t2,t164,t3,t5,t6]
set_option maxHeartbeats 0 in
theorem b374 : Ban 228 8 v369 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v370 : List ℕ := [t0,t12,t2,t164,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b375 : Ban 228 8 v370 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v371 : List ℕ := [t0,t232,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b376 : Ban 228 8 v371 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v372 : List ℕ := [t0,t12,t2,t3,t4,t233,t6]
set_option maxHeartbeats 0 in
theorem b377 : Ban 228 8 v372 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v373 : List ℕ := [t0,t12,t2,t4,t5,t233,t6]
set_option maxHeartbeats 0 in
theorem b378 : Ban 228 8 v373 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v374 : List ℕ := [t0,t12,t2,t3,t4,t5,t233,t6]
set_option maxHeartbeats 0 in
theorem b379 : Ban 228 8 v374 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v375 : List ℕ := [t0,t12,t2,t234,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b380 : Ban 228 8 v375 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v376 : List ℕ := [t0,t12,t2,t234,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b381 : Ban 228 8 v376 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v377 : List ℕ := [t0,t12,t2,t3,t4,t235,t6]
set_option maxHeartbeats 0 in
theorem b382 : Ban 228 8 v377 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v378 : List ℕ := [t0,t12,t2,t3,t4,t235,t5,t6]
set_option maxHeartbeats 0 in
theorem b383 : Ban 228 8 v378 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v379 : List ℕ := [t170,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b384 : Ban 228 8 v379 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v380 : List ℕ := [t0,t12,t2,t3,t4,t5,t6,t171]
set_option maxHeartbeats 0 in
theorem b385 : Ban 228 8 v380 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v381 : List ℕ := [t0,t12,t2,t172,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b386 : Ban 228 8 v381 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v382 : List ℕ := [t0,t12,t2,t3,t4,t5,t173,t6]
set_option maxHeartbeats 0 in
theorem b387 : Ban 228 8 v382 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v383 : List ℕ := [t236,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b388 : Ban 228 8 v383 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v384 : List ℕ := [t0,t12,t2,t3,t4,t5,t237,t6]
set_option maxHeartbeats 0 in
theorem b389 : Ban 228 8 v384 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v385 : List ℕ := [t0,t12,t2,t3,t238,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b390 : Ban 228 8 v385 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v386 : List ℕ := [t0,t12,t2,t3,t4,t239,t5,t6]
set_option maxHeartbeats 0 in
theorem b391 : Ban 228 8 v386 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v387 : List ℕ := [t178,t0,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b392 : Ban 228 8 v387 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v388 : List ℕ := [t0,t12,t2,t3,t4,t5,t6,t179]
set_option maxHeartbeats 0 in
theorem b393 : Ban 228 8 v388 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v389 : List ℕ := [t0,t12,t2,t3,t180,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b394 : Ban 228 8 v389 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v390 : List ℕ := [t0,t12,t2,t3,t4,t5,t181,t6]
set_option maxHeartbeats 0 in
theorem b395 : Ban 228 8 v390 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v391 : List ℕ := [t0,t12,t2,t3,t4,t240,t5,t6]
set_option maxHeartbeats 0 in
theorem b396 : Ban 228 8 v391 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v392 : List ℕ := [t0,t12,t2,t3,t4,t5,t241]
set_option maxHeartbeats 0 in
theorem b397 : Ban 228 8 v392 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v393 : List ℕ := [t0,t12,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b398 : Ban 228 8 v393 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v394 : List ℕ := [t0,t12,t2,t3,t4,t5,t6,t241]
set_option maxHeartbeats 0 in
theorem b399 : Ban 228 8 v394 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v395 : List ℕ := [t0,t242,t12,t2,t3,t4,t6]
set_option maxHeartbeats 0 in
theorem b400 : Ban 228 8 v395 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v396 : List ℕ := [t0,t242,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b401 : Ban 228 8 v396 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v397 : List ℕ := [t0,t12,t2,t3,t4,t243,t5]
set_option maxHeartbeats 0 in
theorem b402 : Ban 228 8 v397 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v398 : List ℕ := [t0,t12,t2,t3,t4,t243,t5,t6]
set_option maxHeartbeats 0 in
theorem b403 : Ban 228 8 v398 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b404 : Ban 228 9 v3 := viaBranch (ws := [v4,v5,v6,v7,v9,v10,v11,v12,v13,v15,v16,v17,v18,v19,v20,v22,v23,v24,v25,v26,v27,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v333,v334,v335,v336,v337,v338,v339,v340,v341,v342,v343,v344,v345,v346,v347,v348,v349,v350,v351,v352,v353,v354,v355,v356,v357,v358,v359,v360,v361,v362,v363,v364,v365,v366,v367,v368,v369,v370,v371,v372,v373,v374,v375,v376,v377,v378,v379,v380,v381,v382,v383,v384,v385,v386,v387,v388,v389,v390,v391,v392,v393,v394,v395,v396,v397,v398]) (consBan b2 (consBan b3 (consBan b4 (consBan b6 (consBan b8 (consBan b9 (consBan b10 (consBan b11 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (consBan b20 (consBan b21 (consBan b22 (consBan b23 (consBan b24 (consBan b25 (consBan b240 (consBan b241 (consBan b242 (consBan b243 (consBan b244 (consBan b245 (consBan b246 (consBan b247 (consBan b248 (consBan b249 (consBan b250 (consBan b251 (consBan b252 (consBan b253 (consBan b254 (consBan b255 (consBan b256 (consBan b257 (consBan b258 (consBan b259 (consBan b260 (consBan b261 (consBan b262 (consBan b263 (consBan b264 (consBan b265 (consBan b266 (consBan b267 (consBan b268 (consBan b337 (consBan b338 (consBan b339 (consBan b340 (consBan b341 (consBan b342 (consBan b343 (consBan b344 (consBan b345 (consBan b346 (consBan b347 (consBan b348 (consBan b349 (consBan b350 (consBan b351 (consBan b352 (consBan b353 (consBan b354 (consBan b355 (consBan b356 (consBan b357 (consBan b358 (consBan b359 (consBan b360 (consBan b361 (consBan b362 (consBan b363 (consBan b364 (consBan b365 (consBan b366 (consBan b367 (consBan b368 (consBan b369 (consBan b370 (consBan b371 (consBan b372 (consBan b373 (consBan b374 (consBan b375 (consBan b376 (consBan b377 (consBan b378 (consBan b379 (consBan b380 (consBan b381 (consBan b382 (consBan b383 (consBan b384 (consBan b385 (consBan b386 (consBan b387 (consBan b388 (consBan b389 (consBan b390 (consBan b391 (consBan b392 (consBan b393 (consBan b394 (consBan b395 (consBan b396 (consBan b397 (consBan b398 (consBan b399 (consBan b400 (consBan b401 (consBan b402 (consBan b403 (nilBan 228 8))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
def v399 : List ℕ := [t1,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b405 : Ban 228 9 v399 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v400 : List ℕ := [t0,t1,t12,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b406 : Ban 228 9 v400 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v401 : List ℕ := [t244,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b407 : Ban 228 9 v401 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v402 : List ℕ := [t244,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b408 : Ban 228 9 v402 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b409 : Ban 228 9 v4 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v403 : List ℕ := [t0,t13,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b410 : Ban 228 9 v403 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v404 : List ℕ := [t14,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b411 : Ban 228 9 v404 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v405 : List ℕ := [t0,t1,t2,t18,t3,t4,t5,t6]
def v406 : List ℕ := [t245,t246,t247,t248,t249]
set_option maxHeartbeats 0 in
theorem b412 : Ban 60 6 v406 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w36 : Wide 60 6 v406 := viaSub (ws := [v406]) (consBan b412 (nilBan 60 6)) (by decide) (by decide +kernel)
def p127_109Slow : Projection 228 60 := pick [0,1,4,5,8,10,15,16,17,18,57,58,61,62,65,67,72,73,74,75,95,96,99,100,103,105,110,111,112,113,133,134,137,138,141,143,148,149,150,151,171,172,175,176,179,181,186,187,188,189,209,210,213,214,217,219,224,225,226,227] rfl (by decide +kernel) (by decide)
def p127_109T : LookupTree := (.fork t435 t246 (.fork t2 t488 (.fork t478 t488 (.fork t0 t488 (.fork t477 t488 .empty .empty) (.fork t1 t245 .empty .empty)) (.fork t20 t488 (.fork t159 t488 .empty .empty) .empty)) (.fork t42 t245 (.fork t251 t245 (.fork t361 t245 .empty .empty) (.fork t18 t488 .empty .empty)) (.fork t22 t246 (.fork t3 t246 .empty .empty) .empty))) (.fork t191 t249 (.fork t5 t248 (.fork t269 t246 (.fork t92 t246 .empty .empty) (.fork t4 t247 .empty .empty)) (.fork t160 t249 (.fork t40 t248 .empty .empty) .empty)) (.fork t241 t465 (.fork t189 t249 (.fork t6 t249 .empty .empty) .empty) (.fork t467 t465 (.fork t158 t249 .empty .empty) .empty))))
set_option maxHeartbeats 0 in
def p127_109 : Projection 228 60 := cached p127_109Slow p127_109T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b413 : Ban 228 9 v405 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v407 : List ℕ := [t19,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b414 : Ban 228 9 v407 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v408 : List ℕ := [t0,t1,t20,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b415 : Ban 228 9 v408 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v409 : List ℕ := [t21,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b416 : Ban 228 9 v409 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v410 : List ℕ := [t0,t1,t2,t22,t4,t5,t6]
def v411 : List ℕ := [t7,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b417 : Ban 228 8 v411 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v412 : List ℕ := [t0,t1,t12,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b418 : Ban 228 8 v412 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v413 : List ℕ := [t244,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b419 : Ban 228 8 v413 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v414 : List ℕ := [t0,t13,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b420 : Ban 228 8 v414 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v415 : List ℕ := [t0,t13,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b421 : Ban 228 8 v415 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v416 : List ℕ := [t14,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b422 : Ban 228 8 v416 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v417 : List ℕ := [t0,t1,t2,t18,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b423 : Ban 228 8 v417 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v418 : List ℕ := [t19,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b424 : Ban 228 8 v418 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v419 : List ℕ := [t0,t1,t20,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b425 : Ban 228 8 v419 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v420 : List ℕ := [t0,t1,t2,t29,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b426 : Ban 228 8 v420 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v421 : List ℕ := [t1,t2,t29,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b427 : Ban 228 8 v421 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v422 : List ℕ := [t0,t1,t2,t29,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b428 : Ban 228 8 v422 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v423 : List ℕ := [t30,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b429 : Ban 228 8 v423 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v424 : List ℕ := [t0,t1,t2,t22,t4,t31,t5,t6]
set_option maxHeartbeats 0 in
theorem b430 : Ban 228 8 v424 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v425 : List ℕ := [t37,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b431 : Ban 228 8 v425 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v426 : List ℕ := [t0,t1,t2,t22,t38,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b432 : Ban 228 8 v426 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v427 : List ℕ := [t39,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b433 : Ban 228 8 v427 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v428 : List ℕ := [t1,t2,t22,t4,t40,t6]
def v429 : List ℕ := [t250,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b434 : Ban 228 7 v429 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v430 : List ℕ := [t1,t251,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b435 : Ban 228 7 v430 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v431 : List ℕ := [t2,t251,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b436 : Ban 228 7 v431 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v432 : List ℕ := [t1,t2,t251,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b437 : Ban 228 7 v432 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v433 : List ℕ := [t252,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b438 : Ban 228 7 v433 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v434 : List ℕ := [t252,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b439 : Ban 228 7 v434 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v435 : List ℕ := [t1,t253,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b440 : Ban 228 7 v435 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v436 : List ℕ := [t1,t253,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b441 : Ban 228 7 v436 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v437 : List ℕ := [t254,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b442 : Ban 228 7 v437 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v438 : List ℕ := [t1,t2,t22,t76,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b443 : Ban 228 7 v438 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v439 : List ℕ := [t255,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b444 : Ban 228 7 v439 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v440 : List ℕ := [t1,t2,t256,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b445 : Ban 228 7 v440 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v441 : List ℕ := [t257,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b446 : Ban 228 7 v441 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v442 : List ℕ := [t1,t2,t22,t4,t258,t40,t6]
set_option maxHeartbeats 0 in
theorem b447 : Ban 228 7 v442 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v443 : List ℕ := [t259,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b448 : Ban 228 7 v443 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v444 : List ℕ := [t1,t2,t22,t260,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b449 : Ban 228 7 v444 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v445 : List ℕ := [t261,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b450 : Ban 228 7 v445 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v446 : List ℕ := [t2,t22,t4,t40,t84,t6]
def v447 : List ℕ := [t32,t33,t262,t35,t36]
set_option maxHeartbeats 0 in
theorem b451 : Ban 60 6 v447 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w37 : Wide 60 6 v447 := viaSub (ws := [v447]) (consBan b451 (nilBan 60 6)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b452 : Ban 228 7 v446 := viaCut p127_91 w37 (by decide) (by decide +kernel) (by decide +kernel)
def v448 : List ℕ := [t1,t2,t22,t4,t40,t84,t6]
set_option maxHeartbeats 0 in
theorem b453 : Ban 228 7 v448 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v449 : List ℕ := [t85,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b454 : Ban 228 7 v449 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v450 : List ℕ := [t85,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b455 : Ban 228 7 v450 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v451 : List ℕ := [t1,t2,t22,t4,t263,t40,t6]
set_option maxHeartbeats 0 in
theorem b456 : Ban 228 7 v451 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v452 : List ℕ := [t264,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b457 : Ban 228 7 v452 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v453 : List ℕ := [t1,t2,t22,t4,t40,t6,t265]
set_option maxHeartbeats 0 in
theorem b458 : Ban 228 7 v453 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v454 : List ℕ := [t266,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b459 : Ban 228 7 v454 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v455 : List ℕ := [t1,t2,t22,t4,t40,t267,t6]
set_option maxHeartbeats 0 in
theorem b460 : Ban 228 7 v455 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v456 : List ℕ := [t1,t268,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b461 : Ban 228 7 v456 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v457 : List ℕ := [t1,t2,t269,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b462 : Ban 228 7 v457 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v458 : List ℕ := [t1,t2,t22,t269,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b463 : Ban 228 7 v458 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v459 : List ℕ := [t1,t270,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b464 : Ban 228 7 v459 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v460 : List ℕ := [t1,t2,t271,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b465 : Ban 228 7 v460 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v461 : List ℕ := [t1,t2,t271,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b466 : Ban 228 7 v461 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v462 : List ℕ := [t149,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b467 : Ban 228 7 v462 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v463 : List ℕ := [t1,t2,t22,t4,t150,t40,t6]
set_option maxHeartbeats 0 in
theorem b468 : Ban 228 7 v463 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v464 : List ℕ := [t1,t151,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b469 : Ban 228 7 v464 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v465 : List ℕ := [t1,t2,t22,t152,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b470 : Ban 228 7 v465 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v466 : List ℕ := [t153,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b471 : Ban 228 7 v466 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v467 : List ℕ := [t1,t2,t22,t4,t40,t154,t6]
set_option maxHeartbeats 0 in
theorem b472 : Ban 228 7 v467 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v468 : List ℕ := [t1,t155,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b473 : Ban 228 7 v468 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v469 : List ℕ := [t1,t2,t22,t4,t156,t40,t6]
set_option maxHeartbeats 0 in
theorem b474 : Ban 228 7 v469 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v470 : List ℕ := [t157,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b475 : Ban 228 7 v470 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v471 : List ℕ := [t1,t2,t22,t4,t40,t6,t158]
set_option maxHeartbeats 0 in
theorem b476 : Ban 228 7 v471 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v472 : List ℕ := [t1,t159,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b477 : Ban 228 7 v472 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v473 : List ℕ := [t1,t2,t22,t4,t40,t160,t6]
set_option maxHeartbeats 0 in
theorem b478 : Ban 228 7 v473 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v474 : List ℕ := [t1,t2,t272,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b479 : Ban 228 7 v474 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v475 : List ℕ := [t1,t2,t4,t273,t40,t6]
def v476 : List ℕ := [t23,t24,t25,t27,t274]
def v477 : List ℕ := [t275,t23,t24,t25,t27,t274]
def v478 : List ℕ := [t276,t277,t104]
set_option maxHeartbeats 0 in
theorem b480 : Ban 24 3 v478 := viaSmall (by decide +kernel) (by decide)
def v479 : List ℕ := [t276,t277,t104,t278]
set_option maxHeartbeats 0 in
theorem b481 : Ban 24 3 v479 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w38 : Wide 24 3 v479 := viaSub (ws := [v478,v479]) (consBan b480 (consBan b481 (nilBan 24 3))) (by decide) (by decide +kernel)
def p59_58Slow : Projection 55 24 := pick [11,13,15,16,17,19,20,21,33,35,37,38,39,41,42,43,44,46,48,49,50,52,53,54] rfl (by decide +kernel) (by decide)
def p59_58T : LookupTree := (.fork t208 t488 (.fork t23 t276 (.fork t289 t488 (.fork t275 t488 .empty .empty) (.fork t196 t488 .empty .empty)) (.fork t95 t488 (.fork t291 t488 .empty .empty) .empty)) (.fork t27 t104 (.fork t297 t298 (.fork t24 t488 .empty .empty) (.fork t25 t277 .empty .empty)) (.fork t274 t278 (.fork t282 t283 .empty .empty) .empty)))
set_option maxHeartbeats 0 in
def p59_58 : Projection 55 24 := cached p59_58Slow p59_58T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b482 : Ban 55 5 v477 := viaCut p59_58 w38 (by decide) (by decide +kernel) (by decide +kernel)
def v480 : List ℕ := [t23,t93,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b483 : Ban 55 5 v480 := viaSmall (by decide +kernel) (by decide)
def v481 : List ℕ := [t23,t24,t93,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b484 : Ban 55 5 v481 := viaSmall (by decide +kernel) (by decide)
def v482 : List ℕ := [t193,t23,t24,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b485 : Ban 55 5 v482 := viaSmall (by decide +kernel) (by decide)
def v483 : List ℕ := [t23,t95,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b486 : Ban 55 5 v483 := viaSmall (by decide +kernel) (by decide)
def v484 : List ℕ := [t23,t95,t24,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b487 : Ban 55 5 v484 := viaCut p59_58 w38 (by decide) (by decide +kernel) (by decide +kernel)
def v485 : List ℕ := [t100,t23,t24,t25,t27,t274]
def v486 : List ℕ := [t276,t279,t104,t280]
set_option maxHeartbeats 0 in
theorem b488 : Ban 24 3 v486 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w39 : Wide 24 3 v486 := viaSub (ws := [v486]) (consBan b488 (nilBan 24 3)) (by decide) (by decide +kernel)
def p59_43Slow : Projection 55 24 := pick [0,1,2,3,4,5,9,10,22,23,24,25,26,27,31,32,33,34,35,36,37,38,42,43] rfl (by decide +kernel) (by decide)
def p59_43T : LookupTree := (.fork t197 t488 (.fork t24 t276 (.fork t23 t279 (.fork t100 t488 .empty .empty) (.fork t194 t488 .empty .empty)) (.fork t293 t488 (.fork t295 t488 .empty .empty) .empty)) (.fork t25 t488 (.fork t107 t488 (.fork t141 t488 .empty .empty) .empty) (.fork t274 t280 (.fork t27 t104 .empty .empty) .empty)))
set_option maxHeartbeats 0 in
def p59_43 : Projection 55 24 := cached p59_43Slow p59_43T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b489 : Ban 55 5 v485 := viaCut p59_43 w39 (by decide) (by decide +kernel) (by decide +kernel)
def v487 : List ℕ := [t23,t24,t25,t105,t27,t274]
set_option maxHeartbeats 0 in
theorem b490 : Ban 55 5 v487 := viaSmall (by decide +kernel) (by decide)
def v488 : List ℕ := [t106,t23,t24,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b491 : Ban 55 5 v488 := viaSmall (by decide +kernel) (by decide)
def v489 : List ℕ := [t23,t24,t107,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b492 : Ban 55 5 v489 := viaCut p59_43 w39 (by decide) (by decide +kernel) (by decide +kernel)
def v490 : List ℕ := [t115,t23,t24,t25,t27,t274]
def v491 : List ℕ := [t111,t215,t281,t98]
set_option maxHeartbeats 0 in
theorem b493 : Ban 18 3 v491 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w40 : Wide 18 3 v491 := viaSub (ws := [v491]) (consBan b493 (nilBan 18 3)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b494 : Ban 55 5 v490 := viaCut p59_27 w40 (by decide) (by decide +kernel) (by decide +kernel)
def v492 : List ℕ := [t23,t24,t25,t27,t116,t274]
set_option maxHeartbeats 0 in
theorem b495 : Ban 55 5 v492 := viaSmall (by decide +kernel) (by decide)
def v493 : List ℕ := [t117,t23,t24,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b496 : Ban 55 5 v493 := viaSmall (by decide +kernel) (by decide)
def v494 : List ℕ := [t23,t24,t25,t118,t27,t274]
set_option maxHeartbeats 0 in
theorem b497 : Ban 55 5 v494 := viaCut p59_27 w40 (by decide) (by decide +kernel) (by decide +kernel)
def v495 : List ℕ := [t23,t24,t25,t27,t282]
set_option maxHeartbeats 0 in
theorem b498 : Ban 55 5 v495 := viaSmall (by decide +kernel) (by decide)
def v496 : List ℕ := [t24,t25,t27,t282,t274]
def v497 : List ℕ := [t277,t104,t283,t278]
set_option maxHeartbeats 0 in
theorem b499 : Ban 24 4 v497 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w41 : Wide 24 4 v497 := viaSub (ws := [v497]) (consBan b499 (nilBan 24 4)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b500 : Ban 55 5 v496 := viaCut p59_58 w41 (by decide) (by decide +kernel) (by decide +kernel)
def v498 : List ℕ := [t23,t24,t25,t27,t282,t274]
set_option maxHeartbeats 0 in
theorem b501 : Ban 55 5 v498 := viaSmall (by decide +kernel) (by decide)
def v499 : List ℕ := [t23,t194,t24,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b502 : Ban 55 5 v499 := viaCut p59_43 w39 (by decide) (by decide +kernel) (by decide +kernel)
def v500 : List ℕ := [t23,t24,t195,t27,t274]
def v501 : List ℕ := [t111,t215,t281,t284]
set_option maxHeartbeats 0 in
theorem b503 : Ban 18 4 v501 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w42 : Wide 18 4 v501 := viaSub (ws := [v501]) (consBan b503 (nilBan 18 4)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b504 : Ban 55 5 v500 := viaCut p59_27 w42 (by decide) (by decide +kernel) (by decide +kernel)
def v502 : List ℕ := [t23,t25,t195,t27,t274]
def a59_04315Slow : Projection 55 55 := pick [0,1,6,7,4,8,2,3,5,9,10,11,12,17,18,15,19,13,14,16,20,21,22,23,28,29,26,30,24,25,27,31,32,44,45,50,51,48,52,46,47,49,53,54,33,34,39,40,37,41,35,36,38,42,43] rfl (by decide +kernel) (by decide)
def a59_04315T : LookupTree := (.fork t167 t94 (.fork t93 t195 (.fork t24 t24 (.fork t23 t25 .empty .empty) .empty) (.fork t195 t93 (.fork t25 t23 .empty .empty) .empty)) (.fork t274 t144 (.fork t27 t27 (.fork t94 t167 .empty .empty) .empty) (.fork t144 t274 .empty .empty)))
set_option maxHeartbeats 0 in
def a59_04315 : Projection 55 55 := cached a59_04315Slow a59_04315T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b505 : Ban 55 5 v502 := viaPerm a59_04315 a59_04315 b182 (by decide +kernel) (by decide +kernel)
def v503 : List ℕ := [t23,t24,t25,t195,t27,t274]
set_option maxHeartbeats 0 in
theorem b506 : Ban 55 5 v503 := viaSmall (by decide +kernel) (by decide)
def v504 : List ℕ := [t196,t23,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b507 : Ban 55 5 v504 := viaSmall (by decide +kernel) (by decide)
def v505 : List ℕ := [t196,t23,t24,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b508 : Ban 55 5 v505 := viaCut p59_58 w38 (by decide) (by decide +kernel) (by decide +kernel)
def v506 : List ℕ := [t23,t24,t197,t27,t274]
set_option maxHeartbeats 0 in
theorem b509 : Ban 55 5 v506 := viaSmall (by decide +kernel) (by decide)
def v507 : List ℕ := [t23,t24,t197,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b510 : Ban 55 5 v507 := viaCut p59_43 w39 (by decide) (by decide +kernel) (by decide +kernel)
def v508 : List ℕ := [t202,t23,t24,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b511 : Ban 55 5 v508 := viaCut p59_27 w40 (by decide) (by decide +kernel) (by decide +kernel)
def v509 : List ℕ := [t23,t24,t25,t203,t274]
def v510 : List ℕ := [t285,t286,t287,t288]
set_option maxHeartbeats 0 in
theorem b512 : Ban 10 4 v510 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w43 : Wide 10 4 v510 := viaSub (ws := [v510]) (consBan b512 (nilBan 10 4)) (by decide) (by decide +kernel)
def p59_35Slow : Projection 55 10 := pick [22,23,24,25,31,33,34,35,36,42] rfl (by decide +kernel) (by decide)
def p59_35T : LookupTree := (.fork t25 t488 (.fork t24 t285 (.fork t23 t286 .empty .empty) .empty) (.fork t274 t288 (.fork t203 t287 .empty .empty) .empty))
set_option maxHeartbeats 0 in
def p59_35 : Projection 55 10 := cached p59_35Slow p59_35T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b513 : Ban 55 5 v509 := viaCut p59_35 w43 (by decide) (by decide +kernel) (by decide +kernel)
def v511 : List ℕ := [t23,t24,t25,t27,t203,t274]
set_option maxHeartbeats 0 in
theorem b514 : Ban 55 5 v511 := viaSmall (by decide +kernel) (by decide)
def v512 : List ℕ := [t23,t208,t24,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b515 : Ban 55 5 v512 := viaCut p59_58 w38 (by decide) (by decide +kernel) (by decide +kernel)
def v513 : List ℕ := [t23,t24,t25,t209,t274]
set_option maxHeartbeats 0 in
theorem b516 : Ban 55 5 v513 := viaSmall (by decide +kernel) (by decide)
def v514 : List ℕ := [t23,t24,t25,t209,t27,t274]
set_option maxHeartbeats 0 in
theorem b517 : Ban 55 5 v514 := viaCut p59_27 w40 (by decide) (by decide +kernel) (by decide +kernel)
def v515 : List ℕ := [t289,t23,t25,t27]
set_option maxHeartbeats 0 in
theorem b518 : Ban 55 5 v515 := viaSmall (by decide +kernel) (by decide)
def v516 : List ℕ := [t289,t23,t24,t25,t27]
set_option maxHeartbeats 0 in
theorem b519 : Ban 55 5 v516 := viaCut p59_58 w38 (by decide) (by decide +kernel) (by decide +kernel)
def v517 : List ℕ := [t289,t23,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b520 : Ban 55 5 v517 := viaSmall (by decide +kernel) (by decide)
def v518 : List ℕ := [t289,t23,t24,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b521 : Ban 55 5 v518 := viaCut p59_58 w38 (by decide) (by decide +kernel) (by decide +kernel)
def v519 : List ℕ := [t23,t24,t25,t27,t274,t290]
set_option maxHeartbeats 0 in
theorem b522 : Ban 55 5 v519 := viaSmall (by decide +kernel) (by decide)
def v520 : List ℕ := [t23,t291,t24,t25,t27]
set_option maxHeartbeats 0 in
theorem b523 : Ban 55 5 v520 := viaCut p59_58 w38 (by decide) (by decide +kernel) (by decide +kernel)
def v521 : List ℕ := [t23,t291,t24,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b524 : Ban 55 5 v521 := viaCut p59_58 w38 (by decide) (by decide +kernel) (by decide +kernel)
def v522 : List ℕ := [t23,t25,t27,t292,t274]
set_option maxHeartbeats 0 in
theorem b525 : Ban 55 5 v522 := viaSmall (by decide +kernel) (by decide)
def v523 : List ℕ := [t23,t24,t25,t27,t292,t274]
set_option maxHeartbeats 0 in
theorem b526 : Ban 55 5 v523 := viaSmall (by decide +kernel) (by decide)
def v524 : List ℕ := [t139,t23,t24,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b527 : Ban 55 5 v524 := viaCut p59_27 w40 (by decide) (by decide +kernel) (by decide +kernel)
def v525 : List ℕ := [t23,t24,t25,t27,t274,t140]
set_option maxHeartbeats 0 in
theorem b528 : Ban 55 5 v525 := viaSmall (by decide +kernel) (by decide)
def v526 : List ℕ := [t23,t24,t141,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b529 : Ban 55 5 v526 := viaCut p59_43 w39 (by decide) (by decide +kernel) (by decide +kernel)
def v527 : List ℕ := [t23,t24,t25,t142,t27,t274]
set_option maxHeartbeats 0 in
theorem b530 : Ban 55 5 v527 := viaCut p59_27 w40 (by decide) (by decide +kernel) (by decide +kernel)
def v528 : List ℕ := [t23,t24,t293,t27,t274]
set_option maxHeartbeats 0 in
theorem b531 : Ban 55 5 v528 := viaSmall (by decide +kernel) (by decide)
def v529 : List ℕ := [t23,t24,t293,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b532 : Ban 55 5 v529 := viaCut p59_43 w39 (by decide) (by decide +kernel) (by decide +kernel)
def v530 : List ℕ := [t23,t24,t25,t27,t294]
def v531 : List ℕ := [t111,t215,t98,t112]
set_option maxHeartbeats 0 in
theorem b533 : Ban 18 4 v531 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w44 : Wide 18 4 v531 := viaSub (ws := [v531]) (consBan b533 (nilBan 18 4)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b534 : Ban 55 5 v530 := viaCut p59_27 w44 (by decide) (by decide +kernel) (by decide +kernel)
def v532 : List ℕ := [t23,t24,t25,t27,t274,t294]
set_option maxHeartbeats 0 in
theorem b535 : Ban 55 5 v532 := viaSmall (by decide +kernel) (by decide)
def v533 : List ℕ := [t23,t24,t295,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b536 : Ban 55 5 v533 := viaCut p59_43 w39 (by decide) (by decide +kernel) (by decide +kernel)
def v534 : List ℕ := [t23,t24,t27,t296]
set_option maxHeartbeats 0 in
theorem b537 : Ban 55 5 v534 := viaSmall (by decide +kernel) (by decide)
def v535 : List ℕ := [t23,t24,t25,t27,t296]
set_option maxHeartbeats 0 in
theorem b538 : Ban 55 5 v535 := viaSmall (by decide +kernel) (by decide)
def v536 : List ℕ := [t23,t24,t27,t296,t274]
set_option maxHeartbeats 0 in
theorem b539 : Ban 55 5 v536 := viaSmall (by decide +kernel) (by decide)
def v537 : List ℕ := [t23,t24,t25,t27,t296,t274]
set_option maxHeartbeats 0 in
theorem b540 : Ban 55 5 v537 := viaSmall (by decide +kernel) (by decide)
def v538 : List ℕ := [t23,t24,t297,t25,t27]
set_option maxHeartbeats 0 in
theorem b541 : Ban 55 5 v538 := viaSmall (by decide +kernel) (by decide)
def v539 : List ℕ := [t23,t24,t297,t25,t274]
def v540 : List ℕ := [t276,t298,t277,t278]
def a58_5341Slow : Projection 24 24 := pick [16,22,18,23,20,21,17,19,8,14,10,15,12,13,9,11,0,6,2,7,4,5,1,3] rfl (by decide +kernel) (by decide)
def a58_5341T : LookupTree := (.fork t104 t276 (.fork t298 t283 (.fork t276 t104 .empty .empty) (.fork t277 t277 .empty .empty)) (.fork t278 t278 (.fork t283 t298 .empty .empty) .empty))
set_option maxHeartbeats 0 in
def a58_5341 : Projection 24 24 := cached a58_5341Slow a58_5341T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b542 : Ban 24 4 v540 := viaPerm a58_5341 a58_5341 b499 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w45 : Wide 24 4 v540 := viaSub (ws := [v540]) (consBan b542 (nilBan 24 4)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b543 : Ban 55 5 v539 := viaCut p59_58 w45 (by decide) (by decide +kernel) (by decide +kernel)
def v541 : List ℕ := [t23,t24,t297,t25,t27,t274]
set_option maxHeartbeats 0 in
theorem b544 : Ban 55 5 v541 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b545 : Ban 55 6 v476 := viaBranch (ws := [v477,v480,v481,v482,v483,v484,v485,v487,v488,v489,v490,v492,v493,v494,v495,v496,v498,v499,v500,v502,v503,v504,v505,v506,v507,v508,v509,v511,v512,v513,v514,v515,v516,v517,v518,v519,v520,v521,v522,v523,v524,v525,v526,v527,v528,v529,v530,v532,v533,v534,v535,v536,v537,v538,v539,v541]) (consBan b482 (consBan b483 (consBan b484 (consBan b485 (consBan b486 (consBan b487 (consBan b489 (consBan b490 (consBan b491 (consBan b492 (consBan b494 (consBan b495 (consBan b496 (consBan b497 (consBan b498 (consBan b500 (consBan b501 (consBan b502 (consBan b504 (consBan b505 (consBan b506 (consBan b507 (consBan b508 (consBan b509 (consBan b510 (consBan b511 (consBan b513 (consBan b514 (consBan b515 (consBan b516 (consBan b517 (consBan b518 (consBan b519 (consBan b520 (consBan b521 (consBan b522 (consBan b523 (consBan b524 (consBan b525 (consBan b526 (consBan b527 (consBan b528 (consBan b529 (consBan b530 (consBan b531 (consBan b532 (consBan b534 (consBan b535 (consBan b536 (consBan b537 (consBan b538 (consBan b539 (consBan b540 (consBan b541 (consBan b543 (consBan b544 (nilBan 55 5))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w46 : Wide 55 6 v476 := viaSub (ws := [v476]) (consBan b545 (nilBan 55 6)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b546 : Ban 228 7 v475 := viaCut p127_59 w46 (by decide) (by decide +kernel) (by decide +kernel)
def v542 : List ℕ := [t1,t2,t22,t4,t273,t40,t6]
set_option maxHeartbeats 0 in
theorem b547 : Ban 55 6 v214 := viaSmall (by decide +kernel) (by decide)
def v543 : List ℕ := [t23,t24,t25,t167,t27,t274]
set_option maxHeartbeats 0 in
theorem b548 : Ban 55 6 v543 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w47 : Wide 55 6 v543 := viaSub (ws := [v214,v476,v543]) (consBan b547 (consBan b545 (consBan b548 (nilBan 55 6)))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b549 : Ban 228 7 v542 := viaCut p127_59 w47 (by decide) (by decide +kernel) (by decide +kernel)
def v544 : List ℕ := [t1,t299,t2,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b550 : Ban 30 6 v40 := viaPerm a114_1546 a114_1546 b99 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w48 : Wide 30 6 v40 := viaSub (ws := [v2,v40]) (consBan b57 (consBan b550 (nilBan 30 6))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b551 : Ban 228 7 v544 := viaCut p127_114 w48 (by decide) (by decide +kernel) (by decide +kernel)
def v545 : List ℕ := [t1,t299,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b552 : Ban 228 7 v545 := viaCut p127_114 w48 (by decide) (by decide +kernel) (by decide +kernel)
def v546 : List ℕ := [t1,t2,t300,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b553 : Ban 228 7 v546 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v547 : List ℕ := [t301,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b554 : Ban 228 7 v547 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v548 : List ℕ := [t1,t2,t22,t4,t40,t166,t6]
set_option maxHeartbeats 0 in
theorem b555 : Ban 228 7 v548 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v549 : List ℕ := [t1,t2,t168,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b556 : Ban 228 7 v549 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v550 : List ℕ := [t1,t2,t22,t4,t302,t40,t6]
set_option maxHeartbeats 0 in
theorem b557 : Ban 228 7 v550 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v551 : List ℕ := [t303,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b558 : Ban 228 7 v551 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v552 : List ℕ := [t1,t2,t22,t4,t40,t6,t304]
set_option maxHeartbeats 0 in
theorem b559 : Ban 228 7 v552 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v553 : List ℕ := [t1,t2,t305,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b560 : Ban 228 7 v553 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v554 : List ℕ := [t1,t2,t22,t4,t40,t306,t6]
set_option maxHeartbeats 0 in
theorem b561 : Ban 228 7 v554 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v555 : List ℕ := [t174,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b562 : Ban 228 7 v555 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v556 : List ℕ := [t1,t2,t22,t4,t40,t175,t6]
set_option maxHeartbeats 0 in
theorem b563 : Ban 228 7 v556 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v557 : List ℕ := [t1,t2,t22,t176,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b564 : Ban 228 7 v557 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v558 : List ℕ := [t1,t2,t22,t4,t177,t40,t6]
set_option maxHeartbeats 0 in
theorem b565 : Ban 228 7 v558 := viaCut p127_114 w48 (by decide) (by decide +kernel) (by decide +kernel)
def v559 : List ℕ := [t178,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b566 : Ban 228 7 v559 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v560 : List ℕ := [t1,t2,t22,t4,t40,t6,t179]
set_option maxHeartbeats 0 in
theorem b567 : Ban 228 7 v560 := viaCut p127_59 w47 (by decide) (by decide +kernel) (by decide +kernel)
def v561 : List ℕ := [t1,t2,t22,t180,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b568 : Ban 228 7 v561 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v562 : List ℕ := [t1,t2,t22,t4,t40,t181,t6]
set_option maxHeartbeats 0 in
theorem b569 : Ban 228 7 v562 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v563 : List ℕ := [t1,t2,t22,t4,t182,t40,t6]
set_option maxHeartbeats 0 in
theorem b570 : Ban 228 7 v563 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v564 : List ℕ := [t1,t2,t22,t4,t6,t183]
set_option maxHeartbeats 0 in
theorem b571 : Ban 228 7 v564 := viaCut p127_59 w47 (by decide) (by decide +kernel) (by decide +kernel)
def v565 : List ℕ := [t1,t2,t22,t4,t40,t6,t183]
set_option maxHeartbeats 0 in
theorem b572 : Ban 228 7 v565 := viaCut p127_59 w47 (by decide) (by decide +kernel) (by decide +kernel)
def v566 : List ℕ := [t184,t1,t2,t22,t4,t6]
set_option maxHeartbeats 0 in
theorem b573 : Ban 228 7 v566 := viaCut p127_59 w47 (by decide) (by decide +kernel) (by decide +kernel)
def v567 : List ℕ := [t184,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b574 : Ban 228 7 v567 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v568 : List ℕ := [t1,t2,t22,t4,t185,t40,t6]
set_option maxHeartbeats 0 in
theorem b575 : Ban 228 7 v568 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b576 : Ban 228 8 v428 := viaBranch (ws := [v429,v430,v431,v432,v433,v434,v435,v436,v437,v438,v439,v440,v441,v442,v443,v444,v445,v446,v448,v449,v450,v451,v452,v453,v454,v455,v456,v457,v458,v459,v460,v461,v462,v463,v464,v465,v466,v467,v468,v469,v470,v471,v472,v473,v474,v475,v542,v544,v545,v546,v547,v548,v549,v550,v551,v552,v553,v554,v555,v556,v557,v558,v559,v560,v561,v562,v563,v564,v565,v566,v567,v568]) (consBan b434 (consBan b435 (consBan b436 (consBan b437 (consBan b438 (consBan b439 (consBan b440 (consBan b441 (consBan b442 (consBan b443 (consBan b444 (consBan b445 (consBan b446 (consBan b447 (consBan b448 (consBan b449 (consBan b450 (consBan b452 (consBan b453 (consBan b454 (consBan b455 (consBan b456 (consBan b457 (consBan b458 (consBan b459 (consBan b460 (consBan b461 (consBan b462 (consBan b463 (consBan b464 (consBan b465 (consBan b466 (consBan b467 (consBan b468 (consBan b469 (consBan b470 (consBan b471 (consBan b472 (consBan b473 (consBan b474 (consBan b475 (consBan b476 (consBan b477 (consBan b478 (consBan b479 (consBan b546 (consBan b549 (consBan b551 (consBan b552 (consBan b553 (consBan b554 (consBan b555 (consBan b556 (consBan b557 (consBan b558 (consBan b559 (consBan b560 (consBan b561 (consBan b562 (consBan b563 (consBan b564 (consBan b565 (consBan b566 (consBan b567 (consBan b568 (consBan b569 (consBan b570 (consBan b571 (consBan b572 (consBan b573 (consBan b574 (consBan b575 (nilBan 228 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
def v569 : List ℕ := [t0,t1,t2,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b577 : Ban 228 8 v569 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v570 : List ℕ := [t1,t2,t22,t4,t5,t40,t6]
set_option maxHeartbeats 0 in
theorem b578 : Ban 228 8 v570 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v571 : List ℕ := [t0,t1,t2,t22,t4,t5,t40,t6]
set_option maxHeartbeats 0 in
theorem b579 : Ban 228 8 v571 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v572 : List ℕ := [t186,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b580 : Ban 228 8 v572 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v573 : List ℕ := [t186,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b581 : Ban 228 8 v573 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v574 : List ℕ := [t0,t1,t2,t22,t4,t187,t6]
set_option maxHeartbeats 0 in
theorem b582 : Ban 228 8 v574 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v575 : List ℕ := [t0,t1,t2,t22,t4,t187,t5,t6]
set_option maxHeartbeats 0 in
theorem b583 : Ban 228 8 v575 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v576 : List ℕ := [t188,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b584 : Ban 228 8 v576 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v577 : List ℕ := [t1,t2,t22,t4,t5,t6,t189]
set_option maxHeartbeats 0 in
theorem b585 : Ban 228 8 v577 := viaCut p127_59 w47 (by decide) (by decide +kernel) (by decide +kernel)
def v578 : List ℕ := [t0,t1,t2,t22,t4,t5,t6,t189]
set_option maxHeartbeats 0 in
theorem b586 : Ban 228 8 v578 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v579 : List ℕ := [t190,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b587 : Ban 228 8 v579 := viaCut p127_59 w47 (by decide) (by decide +kernel) (by decide +kernel)
def v580 : List ℕ := [t190,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b588 : Ban 228 8 v580 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v581 : List ℕ := [t0,t1,t2,t22,t4,t5,t191,t6]
set_option maxHeartbeats 0 in
theorem b589 : Ban 228 8 v581 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v582 : List ℕ := [t0,t250,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b590 : Ban 228 8 v582 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v583 : List ℕ := [t0,t1,t251,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b591 : Ban 228 8 v583 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v584 : List ℕ := [t0,t2,t251,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b592 : Ban 228 8 v584 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v585 : List ℕ := [t0,t1,t2,t251,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b593 : Ban 228 8 v585 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v586 : List ℕ := [t252,t0,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b594 : Ban 228 8 v586 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v587 : List ℕ := [t252,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b595 : Ban 228 8 v587 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v588 : List ℕ := [t0,t1,t253,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b596 : Ban 228 8 v588 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v589 : List ℕ := [t0,t1,t253,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b597 : Ban 228 8 v589 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v590 : List ℕ := [t254,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b598 : Ban 228 8 v590 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v591 : List ℕ := [t0,t1,t2,t22,t76,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b599 : Ban 228 8 v591 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v592 : List ℕ := [t0,t255,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b600 : Ban 228 8 v592 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v593 : List ℕ := [t0,t1,t2,t256,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b601 : Ban 228 8 v593 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v594 : List ℕ := [t257,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b602 : Ban 228 8 v594 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v595 : List ℕ := [t0,t1,t2,t22,t4,t258,t5,t6]
set_option maxHeartbeats 0 in
theorem b603 : Ban 228 8 v595 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v596 : List ℕ := [t0,t259,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b604 : Ban 228 8 v596 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v597 : List ℕ := [t0,t1,t2,t22,t260,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b605 : Ban 228 8 v597 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v598 : List ℕ := [t307,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b606 : Ban 228 8 v598 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v599 : List ℕ := [t0,t1,t2,t22,t4,t308,t6]
set_option maxHeartbeats 0 in
theorem b607 : Ban 228 8 v599 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v600 : List ℕ := [t0,t2,t22,t4,t5,t308,t6]
set_option maxHeartbeats 0 in
theorem b608 : Ban 228 8 v600 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v601 : List ℕ := [t0,t1,t2,t22,t4,t5,t308,t6]
set_option maxHeartbeats 0 in
theorem b609 : Ban 228 8 v601 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v602 : List ℕ := [t0,t309,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b610 : Ban 228 8 v602 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v603 : List ℕ := [t0,t309,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b611 : Ban 228 8 v603 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v604 : List ℕ := [t0,t1,t2,t22,t4,t310,t6]
set_option maxHeartbeats 0 in
theorem b612 : Ban 228 8 v604 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v605 : List ℕ := [t0,t1,t2,t22,t4,t310,t5,t6]
set_option maxHeartbeats 0 in
theorem b613 : Ban 228 8 v605 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v606 : List ℕ := [t264,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b614 : Ban 228 8 v606 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v607 : List ℕ := [t0,t1,t2,t22,t4,t5,t6,t265]
set_option maxHeartbeats 0 in
theorem b615 : Ban 228 8 v607 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v608 : List ℕ := [t0,t266,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b616 : Ban 228 8 v608 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v609 : List ℕ := [t0,t1,t2,t22,t4,t5,t267,t6]
set_option maxHeartbeats 0 in
theorem b617 : Ban 228 8 v609 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v610 : List ℕ := [t0,t1,t268,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b618 : Ban 228 8 v610 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v611 : List ℕ := [t0,t1,t2,t269,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b619 : Ban 228 8 v611 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v612 : List ℕ := [t0,t1,t2,t22,t269,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b620 : Ban 228 8 v612 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v613 : List ℕ := [t0,t1,t270,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b621 : Ban 228 8 v613 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v614 : List ℕ := [t0,t1,t2,t271,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b622 : Ban 228 8 v614 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v615 : List ℕ := [t0,t1,t2,t271,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b623 : Ban 228 8 v615 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v616 : List ℕ := [t149,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b624 : Ban 228 8 v616 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v617 : List ℕ := [t0,t1,t2,t22,t4,t150,t5,t6]
set_option maxHeartbeats 0 in
theorem b625 : Ban 228 8 v617 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v618 : List ℕ := [t0,t1,t151,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b626 : Ban 228 8 v618 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v619 : List ℕ := [t0,t1,t2,t22,t152,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b627 : Ban 228 8 v619 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v620 : List ℕ := [t228,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b628 : Ban 228 8 v620 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v621 : List ℕ := [t0,t1,t2,t22,t4,t5,t229,t6]
set_option maxHeartbeats 0 in
theorem b629 : Ban 228 8 v621 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v622 : List ℕ := [t0,t1,t230,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b630 : Ban 228 8 v622 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v623 : List ℕ := [t0,t1,t2,t22,t4,t231,t5,t6]
set_option maxHeartbeats 0 in
theorem b631 : Ban 228 8 v623 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v624 : List ℕ := [t157,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b632 : Ban 228 8 v624 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v625 : List ℕ := [t0,t1,t2,t22,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b633 : Ban 228 8 v625 := viaCut p127_59 w47 (by decide) (by decide +kernel) (by decide +kernel)
def v626 : List ℕ := [t0,t1,t159,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b634 : Ban 228 8 v626 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v627 : List ℕ := [t0,t1,t2,t22,t4,t5,t160,t6]
set_option maxHeartbeats 0 in
theorem b635 : Ban 228 8 v627 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v628 : List ℕ := [t0,t1,t2,t272,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b636 : Ban 228 8 v628 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v629 : List ℕ := [t0,t1,t2,t4,t273,t5,t6]
set_option maxHeartbeats 0 in
theorem b637 : Ban 228 8 v629 := viaCut p127_59 w46 (by decide) (by decide +kernel) (by decide +kernel)
def v630 : List ℕ := [t0,t1,t2,t22,t4,t273,t5,t6]
set_option maxHeartbeats 0 in
theorem b638 : Ban 228 8 v630 := viaCut p127_59 w47 (by decide) (by decide +kernel) (by decide +kernel)
def v631 : List ℕ := [t0,t1,t299,t2,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b639 : Ban 228 8 v631 := viaCut p127_114 w48 (by decide) (by decide +kernel) (by decide +kernel)
def v632 : List ℕ := [t0,t1,t299,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b640 : Ban 228 8 v632 := viaCut p127_114 w48 (by decide) (by decide +kernel) (by decide +kernel)
def v633 : List ℕ := [t0,t1,t2,t300,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b641 : Ban 228 8 v633 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v634 : List ℕ := [t0,t311,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b642 : Ban 228 8 v634 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v635 : List ℕ := [t0,t1,t2,t22,t4,t166,t6]
def v636 : List ℕ := [t24,t25,t26,t167,t27]
set_option maxHeartbeats 0 in
theorem b643 : Ban 55 6 v636 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w49 : Wide 55 6 v636 := viaSub (ws := [v636]) (consBan b643 (nilBan 55 6)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b644 : Ban 228 8 v635 := viaCut p127_61 w49 (by decide) (by decide +kernel) (by decide +kernel)
def v637 : List ℕ := [t0,t1,t2,t4,t5,t166,t6]
set_option maxHeartbeats 0 in
theorem b645 : Ban 228 8 v637 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v638 : List ℕ := [t0,t1,t2,t22,t4,t5,t166,t6]
set_option maxHeartbeats 0 in
theorem b646 : Ban 228 8 v638 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v639 : List ℕ := [t0,t1,t2,t312,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b647 : Ban 228 8 v639 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v640 : List ℕ := [t0,t1,t2,t312,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b648 : Ban 228 8 v640 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v641 : List ℕ := [t0,t1,t2,t22,t4,t302,t6]
set_option maxHeartbeats 0 in
theorem b649 : Ban 228 8 v641 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v642 : List ℕ := [t0,t1,t2,t22,t4,t302,t5,t6]
set_option maxHeartbeats 0 in
theorem b650 : Ban 228 8 v642 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v643 : List ℕ := [t303,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b651 : Ban 228 8 v643 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v644 : List ℕ := [t0,t1,t2,t22,t4,t5,t6,t304]
set_option maxHeartbeats 0 in
theorem b652 : Ban 228 8 v644 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v645 : List ℕ := [t0,t1,t2,t305,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b653 : Ban 228 8 v645 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v646 : List ℕ := [t0,t1,t2,t22,t4,t5,t306,t6]
set_option maxHeartbeats 0 in
theorem b654 : Ban 228 8 v646 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v647 : List ℕ := [t236,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b655 : Ban 228 8 v647 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v648 : List ℕ := [t0,t1,t2,t22,t4,t5,t237,t6]
set_option maxHeartbeats 0 in
theorem b656 : Ban 228 8 v648 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v649 : List ℕ := [t0,t1,t2,t22,t238,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b657 : Ban 228 8 v649 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v650 : List ℕ := [t0,t1,t2,t22,t4,t239,t5,t6]
set_option maxHeartbeats 0 in
theorem b658 : Ban 228 8 v650 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v651 : List ℕ := [t178,t0,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b659 : Ban 228 8 v651 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v652 : List ℕ := [t0,t1,t2,t22,t4,t5,t6,t179]
set_option maxHeartbeats 0 in
theorem b660 : Ban 228 8 v652 := viaCut p127_59 w47 (by decide) (by decide +kernel) (by decide +kernel)
def v653 : List ℕ := [t0,t1,t2,t22,t180,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b661 : Ban 228 8 v653 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v654 : List ℕ := [t0,t1,t2,t22,t4,t5,t181,t6]
set_option maxHeartbeats 0 in
theorem b662 : Ban 228 8 v654 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v655 : List ℕ := [t0,t1,t2,t22,t4,t240,t5,t6]
set_option maxHeartbeats 0 in
theorem b663 : Ban 228 8 v655 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v656 : List ℕ := [t0,t1,t2,t22,t4,t5,t241]
set_option maxHeartbeats 0 in
theorem b664 : Ban 228 8 v656 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v657 : List ℕ := [t0,t1,t2,t22,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b665 : Ban 228 8 v657 := viaCut p127_59 w47 (by decide) (by decide +kernel) (by decide +kernel)
def v658 : List ℕ := [t0,t1,t2,t22,t4,t5,t6,t241]
set_option maxHeartbeats 0 in
theorem b666 : Ban 228 8 v658 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v659 : List ℕ := [t0,t242,t1,t2,t22,t4,t6]
set_option maxHeartbeats 0 in
theorem b667 : Ban 228 8 v659 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v660 : List ℕ := [t0,t242,t1,t2,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b668 : Ban 228 8 v660 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v661 : List ℕ := [t0,t1,t2,t22,t4,t243,t5]
set_option maxHeartbeats 0 in
theorem b669 : Ban 228 8 v661 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v662 : List ℕ := [t0,t1,t2,t22,t4,t243,t5,t6]
set_option maxHeartbeats 0 in
theorem b670 : Ban 228 8 v662 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b671 : Ban 228 9 v410 := viaBranch (ws := [v411,v13,v412,v413,v414,v415,v416,v417,v418,v419,v420,v421,v422,v423,v424,v425,v426,v427,v428,v569,v570,v571,v572,v573,v574,v575,v576,v577,v578,v579,v580,v581,v582,v583,v584,v585,v586,v587,v588,v589,v590,v591,v592,v593,v594,v595,v596,v597,v598,v599,v600,v601,v602,v603,v604,v605,v606,v607,v608,v609,v610,v611,v612,v613,v614,v615,v616,v617,v618,v619,v620,v621,v622,v623,v624,v625,v626,v627,v628,v629,v630,v631,v632,v633,v634,v635,v637,v638,v639,v640,v641,v642,v643,v644,v645,v646,v647,v648,v649,v650,v651,v652,v653,v654,v655,v656,v657,v658,v659,v660,v661,v662]) (consBan b417 (consBan b13 (consBan b418 (consBan b419 (consBan b420 (consBan b421 (consBan b422 (consBan b423 (consBan b424 (consBan b425 (consBan b426 (consBan b427 (consBan b428 (consBan b429 (consBan b430 (consBan b431 (consBan b432 (consBan b433 (consBan b576 (consBan b577 (consBan b578 (consBan b579 (consBan b580 (consBan b581 (consBan b582 (consBan b583 (consBan b584 (consBan b585 (consBan b586 (consBan b587 (consBan b588 (consBan b589 (consBan b590 (consBan b591 (consBan b592 (consBan b593 (consBan b594 (consBan b595 (consBan b596 (consBan b597 (consBan b598 (consBan b599 (consBan b600 (consBan b601 (consBan b602 (consBan b603 (consBan b604 (consBan b605 (consBan b606 (consBan b607 (consBan b608 (consBan b609 (consBan b610 (consBan b611 (consBan b612 (consBan b613 (consBan b614 (consBan b615 (consBan b616 (consBan b617 (consBan b618 (consBan b619 (consBan b620 (consBan b621 (consBan b622 (consBan b623 (consBan b624 (consBan b625 (consBan b626 (consBan b627 (consBan b628 (consBan b629 (consBan b630 (consBan b631 (consBan b632 (consBan b633 (consBan b634 (consBan b635 (consBan b636 (consBan b637 (consBan b638 (consBan b639 (consBan b640 (consBan b641 (consBan b642 (consBan b644 (consBan b645 (consBan b646 (consBan b647 (consBan b648 (consBan b649 (consBan b650 (consBan b651 (consBan b652 (consBan b653 (consBan b654 (consBan b655 (consBan b656 (consBan b657 (consBan b658 (consBan b659 (consBan b660 (consBan b661 (consBan b662 (consBan b663 (consBan b664 (consBan b665 (consBan b666 (consBan b667 (consBan b668 (consBan b669 (consBan b670 (nilBan 228 8))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
def v663 : List ℕ := [t1,t2,t3,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b672 : Ban 228 9 v663 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v664 : List ℕ := [t0,t1,t2,t3,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b673 : Ban 228 9 v664 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v665 : List ℕ := [t28,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b674 : Ban 228 9 v665 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v666 : List ℕ := [t28,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b675 : Ban 228 9 v666 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b676 : Ban 228 9 v420 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v667 : List ℕ := [t0,t1,t2,t29,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b677 : Ban 228 9 v667 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v668 : List ℕ := [t30,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b678 : Ban 228 9 v668 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v669 : List ℕ := [t0,t1,t2,t3,t4,t31,t5,t6]
def v670 : List ℕ := [t32,t313,t34,t35,t36]
def v671 : List ℕ := [t314,t32,t313,t34,t35,t36]
def p91_73Slow : Projection 60 12 := pick [0,1,4,9,20,21,24,29,40,41,44,49] rfl (by decide +kernel) (by decide)
def p91_73T : LookupTree := (.fork t326 t488 (.fork t318 t488 (.fork t368 t488 (.fork t324 t488 (.fork t320 t488 .empty .empty) .empty) (.fork t365 t488 (.fork t314 t488 .empty .empty) .empty)) (.fork t315 t488 (.fork t366 t488 (.fork t317 t488 .empty .empty) .empty) (.fork t370 t488 .empty .empty))) (.fork t35 t488 (.fork t313 t15 (.fork t32 t488 (.fork t322 t488 .empty .empty) .empty) (.fork t350 t488 (.fork t34 t16 .empty .empty) .empty)) (.fork t36 t17 (.fork t321 t488 (.fork t333 t15 .empty .empty) .empty) (.fork t349 t17 .empty .empty))))
set_option maxHeartbeats 0 in
def p91_73 : Projection 60 12 := cached p91_73Slow p91_73T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b679 : Ban 60 6 v671 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v672 : List ℕ := [t313,t33,t34,t35,t36]
def a91_10436Slow : Projection 60 60 := pick [10,12,11,13,16,17,14,15,18,19,0,2,1,3,6,7,4,5,8,9,30,32,31,33,36,37,34,35,38,39,20,22,21,23,26,27,24,25,28,29,50,52,51,53,56,57,54,55,58,59,40,42,41,43,46,47,44,45,48,49] rfl (by decide +kernel) (by decide)
def a91_10436T : LookupTree := (.fork t33 t33 (.fork t322 t330 (.fork t324 t336 (.fork t320 t328 (.fork t328 t320 .empty .empty) (.fork t336 t324 .empty .empty)) (.fork t326 t338 (.fork t315 t316 .empty .empty) .empty)) (.fork t338 t326 (.fork t316 t315 (.fork t32 t313 .empty .empty) .empty) (.fork t313 t32 (.fork t330 t322 .empty .empty) .empty))) (.fork t321 t329 (.fork t329 t321 (.fork t34 t35 (.fork t331 t323 .empty .empty) .empty) (.fork t35 t34 (.fork t323 t331 .empty .empty) .empty)) (.fork t36 t36 (.fork t339 t327 (.fork t327 t339 .empty .empty) .empty) (.fork t337 t325 (.fork t325 t337 .empty .empty) .empty))))
set_option maxHeartbeats 0 in
def a91_10436 : Projection 60 60 := cached a91_10436Slow a91_10436T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b680 : Ban 60 6 v672 := viaPerm a91_10436 a91_10436 b19 (by decide +kernel) (by decide +kernel)
def v673 : List ℕ := [t32,t313,t33,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b681 : Ban 60 6 v673 := viaSmall (by decide +kernel) (by decide)
def v674 : List ℕ := [t315,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b682 : Ban 60 6 v674 := viaSmall (by decide +kernel) (by decide)
def v675 : List ℕ := [t315,t32,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b683 : Ban 60 6 v675 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v676 : List ℕ := [t32,t316,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b684 : Ban 60 6 v676 := viaPerm a91_10436 a91_10436 b682 (by decide +kernel) (by decide +kernel)
def v677 : List ℕ := [t32,t316,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b685 : Ban 60 6 v677 := viaPerm a91_10436 a91_10436 b683 (by decide +kernel) (by decide +kernel)
def v678 : List ℕ := [t317,t32,t313,t34,t35,t36]
def a91_13406Slow : Projection 60 60 := pick [10,12,14,15,16,18,11,13,17,19,0,2,4,5,6,8,1,3,7,9,30,32,34,35,36,38,31,33,37,39,40,42,44,45,46,48,41,43,47,49,50,52,54,55,56,58,51,53,57,59,20,22,24,25,26,28,21,23,27,29] rfl (by decide +kernel) (by decide)
def a91_13406T : LookupTree := (.fork t346 t326 (.fork t32 t313 (.fork t318 t316 (.fork t344 t324 .empty .empty) (.fork t317 t314 .empty .empty)) (.fork t319 t315 (.fork t313 t35 .empty .empty) .empty)) (.fork t347 t327 (.fork t262 t33 (.fork t34 t32 .empty .empty) (.fork t35 t34 .empty .empty)) (.fork t345 t325 (.fork t36 t36 .empty .empty) .empty)))
set_option maxHeartbeats 0 in
def a91_13406 : Projection 60 60 := cached a91_13406Slow a91_13406T (by decide +kernel)
def a91_40136Slow : Projection 60 60 := pick [10,16,11,17,12,13,14,18,15,19,0,6,1,7,2,3,4,8,5,9,50,56,51,57,52,53,54,58,55,59,20,26,21,27,22,23,24,28,25,29,30,36,31,37,32,33,34,38,35,39,40,46,41,47,42,43,44,48,45,49] rfl (by decide +kernel) (by decide)
def a91_40136T : LookupTree := (.fork t313 t32 (.fork t326 t346 (.fork t314 t317 (.fork t324 t344 .empty .empty) (.fork t315 t319 .empty .empty)) (.fork t316 t318 (.fork t32 t34 .empty .empty) .empty)) (.fork t327 t347 (.fork t34 t35 (.fork t33 t262 .empty .empty) (.fork t35 t313 .empty .empty)) (.fork t325 t345 (.fork t36 t36 .empty .empty) .empty)))
set_option maxHeartbeats 0 in
def a91_40136 : Projection 60 60 := cached a91_40136Slow a91_40136T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b686 : Ban 60 6 v678 := viaPerm a91_13406 a91_40136 b679 (by decide +kernel) (by decide +kernel)
def v679 : List ℕ := [t32,t313,t262,t35,t36]
set_option maxHeartbeats 0 in
theorem b687 : Ban 60 6 v679 := viaPerm a91_13406 a91_40136 b680 (by decide +kernel) (by decide +kernel)
def v680 : List ℕ := [t313,t34,t262,t35,t36]
set_option maxHeartbeats 0 in
theorem b688 : Ban 60 6 v680 := viaPerm a91_13406 a91_40136 b19 (by decide +kernel) (by decide +kernel)
def v681 : List ℕ := [t32,t313,t34,t262,t35,t36]
set_option maxHeartbeats 0 in
theorem b689 : Ban 60 6 v681 := viaPerm a91_13406 a91_40136 b681 (by decide +kernel) (by decide +kernel)
def v682 : List ℕ := [t318,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b690 : Ban 60 6 v682 := viaPerm a91_13406 a91_40136 b684 (by decide +kernel) (by decide +kernel)
def v683 : List ℕ := [t318,t32,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b691 : Ban 60 6 v683 := viaPerm a91_13406 a91_40136 b685 (by decide +kernel) (by decide +kernel)
def v684 : List ℕ := [t32,t313,t319,t35,t36]
set_option maxHeartbeats 0 in
theorem b692 : Ban 60 6 v684 := viaPerm a91_13406 a91_40136 b682 (by decide +kernel) (by decide +kernel)
def v685 : List ℕ := [t32,t313,t319,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b693 : Ban 60 6 v685 := viaPerm a91_13406 a91_40136 b683 (by decide +kernel) (by decide +kernel)
def v686 : List ℕ := [t320,t32,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b694 : Ban 60 6 v686 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v687 : List ℕ := [t32,t313,t34,t35,t321,t36]
set_option maxHeartbeats 0 in
theorem b695 : Ban 60 6 v687 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v688 : List ℕ := [t322,t32,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b696 : Ban 60 6 v688 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v689 : List ℕ := [t32,t313,t34,t323,t35,t36]
def a91_04316Slow : Projection 60 60 := pick [0,1,6,7,4,8,2,3,5,9,10,11,16,17,14,18,12,13,15,19,20,21,26,27,24,28,22,23,25,29,50,51,56,57,54,58,52,53,55,59,40,41,46,47,44,48,42,43,45,49,30,31,36,37,34,38,32,33,35,39] rfl (by decide +kernel) (by decide)
def a91_04316T : LookupTree := (.fork t343 t318 (.fork t326 t350 (.fork t334 t316 (.fork t348 t324 (.fork t324 t348 .empty .empty) (.fork t314 t332 .empty .empty)) (.fork t317 t340 (.fork t318 t343 .empty .empty) (.fork t315 t335 .empty .empty))) (.fork t332 t314 (.fork t32 t35 (.fork t322 t323 .empty .empty) (.fork t342 t319 .empty .empty)) (.fork t313 t313 (.fork t316 t334 .empty .empty) (.fork t33 t333 .empty .empty)))) (.fork t35 t32 (.fork t262 t341 (.fork t319 t342 (.fork t340 t317 .empty .empty) (.fork t34 t34 .empty .empty)) (.fork t350 t326 (.fork t335 t315 .empty .empty) (.fork t323 t322 .empty .empty))) (.fork t327 t351 (.fork t341 t262 (.fork t333 t33 .empty .empty) (.fork t351 t327 .empty .empty)) (.fork t325 t349 (.fork t36 t36 .empty .empty) (.fork t349 t325 .empty .empty)))))
set_option maxHeartbeats 0 in
def a91_04316 : Projection 60 60 := cached a91_04316Slow a91_04316T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b697 : Ban 60 6 v689 := viaPerm a91_04316 a91_04316 b696 (by decide +kernel) (by decide +kernel)
def v690 : List ℕ := [t324,t32,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b698 : Ban 60 6 v690 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v691 : List ℕ := [t32,t313,t34,t35,t36,t325]
set_option maxHeartbeats 0 in
theorem b699 : Ban 60 6 v691 := viaSmall (by decide +kernel) (by decide)
def v692 : List ℕ := [t326,t32,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b700 : Ban 60 6 v692 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v693 : List ℕ := [t32,t313,t34,t35,t327,t36]
set_option maxHeartbeats 0 in
theorem b701 : Ban 60 6 v693 := viaSmall (by decide +kernel) (by decide)
def v694 : List ℕ := [t328,t32,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b702 : Ban 60 6 v694 := viaPerm a91_10436 a91_10436 b694 (by decide +kernel) (by decide +kernel)
def v695 : List ℕ := [t32,t313,t34,t329,t35,t36]
set_option maxHeartbeats 0 in
theorem b703 : Ban 60 6 v695 := viaPerm a91_10436 a91_10436 b695 (by decide +kernel) (by decide +kernel)
def v696 : List ℕ := [t32,t330,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b704 : Ban 60 6 v696 := viaPerm a91_10436 a91_10436 b696 (by decide +kernel) (by decide +kernel)
def v697 : List ℕ := [t32,t313,t331,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b705 : Ban 60 6 v697 := viaPerm a91_10436 a91_10436 b697 (by decide +kernel) (by decide +kernel)
def v698 : List ℕ := [t32,t332,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b706 : Ban 60 6 v698 := viaPerm a91_04316 a91_04316 b679 (by decide +kernel) (by decide +kernel)
def v699 : List ℕ := [t32,t313,t34,t333,t36]
set_option maxHeartbeats 0 in
theorem b707 : Ban 60 6 v699 := viaPerm a91_04316 a91_04316 b680 (by decide +kernel) (by decide +kernel)
def v700 : List ℕ := [t32,t34,t35,t333,t36]
set_option maxHeartbeats 0 in
theorem b708 : Ban 60 6 v700 := viaPerm a91_04316 a91_04316 b19 (by decide +kernel) (by decide +kernel)
def v701 : List ℕ := [t32,t313,t34,t35,t333,t36]
set_option maxHeartbeats 0 in
theorem b709 : Ban 60 6 v701 := viaPerm a91_04316 a91_04316 b681 (by decide +kernel) (by decide +kernel)
def v702 : List ℕ := [t334,t32,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b710 : Ban 60 6 v702 := viaPerm a91_04316 a91_04316 b684 (by decide +kernel) (by decide +kernel)
def v703 : List ℕ := [t334,t32,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b711 : Ban 60 6 v703 := viaPerm a91_04316 a91_04316 b685 (by decide +kernel) (by decide +kernel)
def v704 : List ℕ := [t32,t313,t34,t335,t36]
set_option maxHeartbeats 0 in
theorem b712 : Ban 60 6 v704 := viaPerm a91_04316 a91_04316 b682 (by decide +kernel) (by decide +kernel)
def v705 : List ℕ := [t32,t313,t34,t335,t35,t36]
set_option maxHeartbeats 0 in
theorem b713 : Ban 60 6 v705 := viaPerm a91_04316 a91_04316 b683 (by decide +kernel) (by decide +kernel)
def v706 : List ℕ := [t336,t32,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b714 : Ban 60 6 v706 := viaPerm a91_10436 a91_10436 b698 (by decide +kernel) (by decide +kernel)
def v707 : List ℕ := [t32,t313,t34,t35,t36,t337]
set_option maxHeartbeats 0 in
theorem b715 : Ban 60 6 v707 := viaPerm a91_10436 a91_10436 b699 (by decide +kernel) (by decide +kernel)
def v708 : List ℕ := [t32,t338,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b716 : Ban 60 6 v708 := viaPerm a91_10436 a91_10436 b700 (by decide +kernel) (by decide +kernel)
def v709 : List ℕ := [t32,t313,t34,t35,t339,t36]
set_option maxHeartbeats 0 in
theorem b717 : Ban 60 6 v709 := viaPerm a91_10436 a91_10436 b701 (by decide +kernel) (by decide +kernel)
def v710 : List ℕ := [t32,t313,t340,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b718 : Ban 60 6 v710 := viaPerm a91_04316 a91_04316 b686 (by decide +kernel) (by decide +kernel)
def v711 : List ℕ := [t32,t313,t34,t341,t36]
set_option maxHeartbeats 0 in
theorem b719 : Ban 60 6 v711 := viaPerm a91_04316 a91_04316 b688 (by decide +kernel) (by decide +kernel)
def v712 : List ℕ := [t32,t313,t35,t341,t36]
set_option maxHeartbeats 0 in
theorem b720 : Ban 60 6 v712 := viaPerm a91_04316 a91_04316 b687 (by decide +kernel) (by decide +kernel)
def v713 : List ℕ := [t32,t313,t34,t35,t341,t36]
set_option maxHeartbeats 0 in
theorem b721 : Ban 60 6 v713 := viaPerm a91_04316 a91_04316 b689 (by decide +kernel) (by decide +kernel)
def v714 : List ℕ := [t32,t342,t313,t35,t36]
set_option maxHeartbeats 0 in
theorem b722 : Ban 60 6 v714 := viaPerm a91_04316 a91_04316 b692 (by decide +kernel) (by decide +kernel)
def v715 : List ℕ := [t32,t342,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b723 : Ban 60 6 v715 := viaPerm a91_04316 a91_04316 b693 (by decide +kernel) (by decide +kernel)
def v716 : List ℕ := [t32,t313,t343,t34,t36]
set_option maxHeartbeats 0 in
theorem b724 : Ban 60 6 v716 := viaPerm a91_04316 a91_04316 b690 (by decide +kernel) (by decide +kernel)
def v717 : List ℕ := [t32,t313,t343,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b725 : Ban 60 6 v717 := viaPerm a91_04316 a91_04316 b691 (by decide +kernel) (by decide +kernel)
def v718 : List ℕ := [t344,t32,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b726 : Ban 60 6 v718 := viaPerm a91_13406 a91_40136 b698 (by decide +kernel) (by decide +kernel)
def v719 : List ℕ := [t32,t313,t34,t35,t36,t345]
set_option maxHeartbeats 0 in
theorem b727 : Ban 60 6 v719 := viaPerm a91_13406 a91_40136 b699 (by decide +kernel) (by decide +kernel)
def v720 : List ℕ := [t32,t313,t346,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b728 : Ban 60 6 v720 := viaPerm a91_13406 a91_40136 b700 (by decide +kernel) (by decide +kernel)
def v721 : List ℕ := [t32,t313,t34,t35,t347,t36]
set_option maxHeartbeats 0 in
theorem b729 : Ban 60 6 v721 := viaPerm a91_13406 a91_40136 b701 (by decide +kernel) (by decide +kernel)
def v722 : List ℕ := [t348,t32,t313,t34,t35,t36]
set_option maxHeartbeats 0 in
theorem b730 : Ban 60 6 v722 := viaPerm a91_04316 a91_04316 b698 (by decide +kernel) (by decide +kernel)
def v723 : List ℕ := [t32,t313,t34,t35,t36,t349]
set_option maxHeartbeats 0 in
theorem b731 : Ban 60 6 v723 := viaPerm a91_04316 a91_04316 b699 (by decide +kernel) (by decide +kernel)
def v724 : List ℕ := [t32,t313,t34,t350,t35,t36]
set_option maxHeartbeats 0 in
theorem b732 : Ban 60 6 v724 := viaPerm a91_04316 a91_04316 b700 (by decide +kernel) (by decide +kernel)
def v725 : List ℕ := [t32,t313,t34,t35,t351,t36]
set_option maxHeartbeats 0 in
theorem b733 : Ban 60 6 v725 := viaPerm a91_04316 a91_04316 b701 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b734 : Ban 60 7 v670 := viaBranch (ws := [v671,v21,v672,v673,v674,v675,v676,v677,v678,v679,v680,v681,v682,v683,v684,v685,v686,v687,v688,v689,v690,v691,v692,v693,v694,v695,v696,v697,v698,v699,v700,v701,v702,v703,v704,v705,v706,v707,v708,v709,v710,v711,v712,v713,v714,v715,v716,v717,v718,v719,v720,v721,v722,v723,v724,v725]) (consBan b679 (consBan b19 (consBan b680 (consBan b681 (consBan b682 (consBan b683 (consBan b684 (consBan b685 (consBan b686 (consBan b687 (consBan b688 (consBan b689 (consBan b690 (consBan b691 (consBan b692 (consBan b693 (consBan b694 (consBan b695 (consBan b696 (consBan b697 (consBan b698 (consBan b699 (consBan b700 (consBan b701 (consBan b702 (consBan b703 (consBan b704 (consBan b705 (consBan b706 (consBan b707 (consBan b708 (consBan b709 (consBan b710 (consBan b711 (consBan b712 (consBan b713 (consBan b714 (consBan b715 (consBan b716 (consBan b717 (consBan b718 (consBan b719 (consBan b720 (consBan b721 (consBan b722 (consBan b723 (consBan b724 (consBan b725 (consBan b726 (consBan b727 (consBan b728 (consBan b729 (consBan b730 (consBan b731 (consBan b732 (consBan b733 (nilBan 60 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w50 : Wide 60 7 v670 := viaSub (ws := [v670]) (consBan b734 (nilBan 60 7)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b735 : Ban 228 9 v669 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v726 : List ℕ := [t37,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b736 : Ban 228 9 v726 := viaCut p127_114 w48 (by decide) (by decide +kernel) (by decide +kernel)
def v727 : List ℕ := [t0,t1,t2,t3,t38,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b737 : Ban 228 9 v727 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v728 : List ℕ := [t39,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b738 : Ban 228 9 v728 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v729 : List ℕ := [t0,t1,t2,t3,t4,t40,t6]
def v730 : List ℕ := [t7,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b739 : Ban 228 8 v730 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v731 : List ℕ := [t1,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b740 : Ban 228 8 v731 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v732 : List ℕ := [t0,t1,t12,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b741 : Ban 228 8 v732 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v733 : List ℕ := [t244,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b742 : Ban 228 8 v733 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v734 : List ℕ := [t244,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b743 : Ban 228 8 v734 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v735 : List ℕ := [t0,t13,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b744 : Ban 228 8 v735 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v736 : List ℕ := [t0,t13,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b745 : Ban 228 8 v736 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v737 : List ℕ := [t14,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b746 : Ban 228 8 v737 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v738 : List ℕ := [t1,t2,t18,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b747 : Ban 228 8 v738 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v739 : List ℕ := [t0,t1,t2,t18,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b748 : Ban 228 8 v739 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v740 : List ℕ := [t19,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b749 : Ban 228 8 v740 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v741 : List ℕ := [t19,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b750 : Ban 228 8 v741 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v742 : List ℕ := [t0,t1,t20,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b751 : Ban 228 8 v742 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v743 : List ℕ := [t21,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b752 : Ban 228 8 v743 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v744 : List ℕ := [t1,t2,t3,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b753 : Ban 228 8 v744 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v745 : List ℕ := [t0,t1,t2,t3,t22,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b754 : Ban 228 8 v745 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v746 : List ℕ := [t28,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b755 : Ban 228 8 v746 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v747 : List ℕ := [t28,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b756 : Ban 228 8 v747 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v748 : List ℕ := [t0,t1,t2,t29,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b757 : Ban 228 8 v748 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v749 : List ℕ := [t0,t1,t2,t29,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b758 : Ban 228 8 v749 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v750 : List ℕ := [t30,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b759 : Ban 228 8 v750 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v751 : List ℕ := [t1,t2,t3,t4,t31,t40,t6]
set_option maxHeartbeats 0 in
theorem b760 : Ban 228 8 v751 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v752 : List ℕ := [t0,t1,t2,t3,t4,t31,t40,t6]
set_option maxHeartbeats 0 in
theorem b761 : Ban 228 8 v752 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v753 : List ℕ := [t37,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b762 : Ban 228 8 v753 := viaCut p127_114 w48 (by decide) (by decide +kernel) (by decide +kernel)
def v754 : List ℕ := [t37,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b763 : Ban 228 8 v754 := viaCut p127_114 w48 (by decide) (by decide +kernel) (by decide +kernel)
def v755 : List ℕ := [t0,t1,t2,t3,t38,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b764 : Ban 228 8 v755 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v756 : List ℕ := [t0,t1,t2,t3,t4,t187,t6]
set_option maxHeartbeats 0 in
theorem b765 : Ban 228 8 v756 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v757 : List ℕ := [t1,t2,t3,t4,t187,t40,t6]
set_option maxHeartbeats 0 in
theorem b766 : Ban 228 8 v757 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v758 : List ℕ := [t0,t1,t2,t3,t4,t187,t40,t6]
set_option maxHeartbeats 0 in
theorem b767 : Ban 228 8 v758 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v759 : List ℕ := [t188,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b768 : Ban 228 8 v759 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v760 : List ℕ := [t188,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b769 : Ban 228 8 v760 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v761 : List ℕ := [t0,t1,t2,t3,t4,t40,t6,t189]
set_option maxHeartbeats 0 in
theorem b770 : Ban 228 8 v761 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v762 : List ℕ := [t190,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b771 : Ban 228 8 v762 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v763 : List ℕ := [t1,t2,t3,t4,t40,t191,t6]
set_option maxHeartbeats 0 in
theorem b772 : Ban 228 8 v763 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v764 : List ℕ := [t0,t1,t2,t3,t4,t40,t191,t6]
set_option maxHeartbeats 0 in
theorem b773 : Ban 228 8 v764 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v765 : List ℕ := [t0,t250,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b774 : Ban 228 8 v765 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v766 : List ℕ := [t0,t1,t251,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b775 : Ban 228 8 v766 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v767 : List ℕ := [t0,t2,t251,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b776 : Ban 228 8 v767 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v768 : List ℕ := [t0,t1,t2,t251,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b777 : Ban 228 8 v768 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v769 : List ℕ := [t252,t0,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b778 : Ban 228 8 v769 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v770 : List ℕ := [t252,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b779 : Ban 228 8 v770 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v771 : List ℕ := [t0,t1,t253,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b780 : Ban 228 8 v771 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v772 : List ℕ := [t0,t1,t253,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b781 : Ban 228 8 v772 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v773 : List ℕ := [t352,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b782 : Ban 228 8 v773 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v774 : List ℕ := [t0,t1,t2,t3,t353,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b783 : Ban 228 8 v774 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v775 : List ℕ := [t0,t354,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b784 : Ban 228 8 v775 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v776 : List ℕ := [t0,t1,t2,t355,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b785 : Ban 228 8 v776 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v777 : List ℕ := [t257,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b786 : Ban 228 8 v777 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v778 : List ℕ := [t0,t1,t2,t3,t4,t258,t40,t6]
set_option maxHeartbeats 0 in
theorem b787 : Ban 228 8 v778 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v779 : List ℕ := [t0,t259,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b788 : Ban 228 8 v779 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v780 : List ℕ := [t0,t1,t2,t3,t260,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b789 : Ban 228 8 v780 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v781 : List ℕ := [t261,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b790 : Ban 228 8 v781 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v782 : List ℕ := [t0,t1,t2,t3,t4,t84,t6]
set_option maxHeartbeats 0 in
theorem b791 : Ban 228 8 v782 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v783 : List ℕ := [t0,t2,t3,t4,t40,t84,t6]
def v784 : List ℕ := [t356,t25,t357,t358,t27]
set_option maxHeartbeats 0 in
theorem b792 : Ban 55 6 v784 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w51 : Wide 55 6 v784 := viaSub (ws := [v784]) (consBan b792 (nilBan 55 6)) (by decide) (by decide +kernel)
def p127_93Slow : Projection 228 55 := pick [0,1,4,5,8,10,12,13,14,17,18,38,39,42,43,46,48,50,51,52,55,56,133,134,137,138,141,143,145,146,147,150,151,171,172,175,176,179,181,183,184,185,188,189,190,191,194,195,198,200,202,203,204,207,208] rfl (by decide +kernel) (by decide)
def p127_93T : LookupTree := (.fork t4 t488 (.fork t251 t195 (.fork t2 t25 (.fork t0 t488 .empty .empty) .empty) (.fork t3 t356 .empty .empty)) (.fork t6 t27 (.fork t84 t358 (.fork t40 t357 .empty .empty) .empty) (.fork t241 t116 .empty .empty)))
set_option maxHeartbeats 0 in
def p127_93 : Projection 228 55 := cached p127_93Slow p127_93T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b793 : Ban 228 8 v783 := viaCut p127_93 w51 (by decide) (by decide +kernel) (by decide +kernel)
def v785 : List ℕ := [t0,t1,t2,t3,t4,t40,t84,t6]
set_option maxHeartbeats 0 in
theorem b794 : Ban 228 8 v785 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v786 : List ℕ := [t0,t85,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b795 : Ban 228 8 v786 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v787 : List ℕ := [t0,t85,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b796 : Ban 228 8 v787 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v788 : List ℕ := [t0,t1,t2,t3,t4,t263,t6]
set_option maxHeartbeats 0 in
theorem b797 : Ban 228 8 v788 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v789 : List ℕ := [t0,t1,t2,t3,t4,t263,t40,t6]
set_option maxHeartbeats 0 in
theorem b798 : Ban 228 8 v789 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v790 : List ℕ := [t264,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b799 : Ban 228 8 v790 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v791 : List ℕ := [t0,t1,t2,t3,t4,t40,t6,t265]
set_option maxHeartbeats 0 in
theorem b800 : Ban 228 8 v791 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v792 : List ℕ := [t0,t266,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b801 : Ban 228 8 v792 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v793 : List ℕ := [t0,t1,t2,t3,t4,t40,t267,t6]
set_option maxHeartbeats 0 in
theorem b802 : Ban 228 8 v793 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v794 : List ℕ := [t0,t1,t91,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b803 : Ban 228 8 v794 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v795 : List ℕ := [t0,t1,t2,t92,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b804 : Ban 228 8 v795 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v796 : List ℕ := [t0,t1,t3,t92,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b805 : Ban 228 8 v796 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v797 : List ℕ := [t0,t1,t2,t3,t92,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b806 : Ban 228 8 v797 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v798 : List ℕ := [t0,t1,t147,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b807 : Ban 228 8 v798 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v799 : List ℕ := [t0,t1,t147,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b808 : Ban 228 8 v799 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v800 : List ℕ := [t0,t1,t2,t148,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b809 : Ban 228 8 v800 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v801 : List ℕ := [t0,t1,t2,t148,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b810 : Ban 228 8 v801 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v802 : List ℕ := [t149,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b811 : Ban 228 8 v802 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v803 : List ℕ := [t0,t1,t2,t3,t4,t150,t40,t6]
set_option maxHeartbeats 0 in
theorem b812 : Ban 228 8 v803 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v804 : List ℕ := [t0,t1,t151,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b813 : Ban 228 8 v804 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v805 : List ℕ := [t0,t1,t2,t3,t152,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b814 : Ban 228 8 v805 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v806 : List ℕ := [t153,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b815 : Ban 228 8 v806 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v807 : List ℕ := [t0,t1,t2,t3,t4,t40,t154,t6]
set_option maxHeartbeats 0 in
theorem b816 : Ban 228 8 v807 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v808 : List ℕ := [t0,t1,t155,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b817 : Ban 228 8 v808 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v809 : List ℕ := [t0,t1,t2,t3,t4,t156,t40,t6]
set_option maxHeartbeats 0 in
theorem b818 : Ban 228 8 v809 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v810 : List ℕ := [t157,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b819 : Ban 228 8 v810 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v811 : List ℕ := [t0,t1,t2,t3,t4,t40,t6,t158]
set_option maxHeartbeats 0 in
theorem b820 : Ban 228 8 v811 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v812 : List ℕ := [t0,t1,t159,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b821 : Ban 228 8 v812 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v813 : List ℕ := [t0,t1,t2,t3,t4,t40,t160,t6]
set_option maxHeartbeats 0 in
theorem b822 : Ban 228 8 v813 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v814 : List ℕ := [t0,t1,t2,t161,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b823 : Ban 228 8 v814 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v815 : List ℕ := [t0,t1,t2,t3,t162,t40,t6]
set_option maxHeartbeats 0 in
theorem b824 : Ban 228 8 v815 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v816 : List ℕ := [t0,t1,t2,t4,t162,t40,t6]
set_option maxHeartbeats 0 in
theorem b825 : Ban 228 8 v816 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v817 : List ℕ := [t0,t1,t2,t3,t4,t162,t40,t6]
set_option maxHeartbeats 0 in
theorem b826 : Ban 228 8 v817 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v818 : List ℕ := [t0,t1,t163,t2,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b827 : Ban 228 8 v818 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v819 : List ℕ := [t0,t1,t163,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b828 : Ban 228 8 v819 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v820 : List ℕ := [t0,t1,t2,t164,t3,t40,t6]
set_option maxHeartbeats 0 in
theorem b829 : Ban 228 8 v820 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v821 : List ℕ := [t0,t1,t2,t164,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b830 : Ban 228 8 v821 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v822 : List ℕ := [t0,t165,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b831 : Ban 228 8 v822 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v823 : List ℕ := [t0,t1,t2,t3,t4,t166,t6]
set_option maxHeartbeats 0 in
theorem b832 : Ban 228 8 v823 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v824 : List ℕ := [t0,t1,t2,t4,t40,t166,t6]
set_option maxHeartbeats 0 in
theorem b833 : Ban 228 8 v824 := viaCut p127_61 w26 (by decide) (by decide +kernel) (by decide +kernel)
def v825 : List ℕ := [t0,t1,t2,t3,t4,t40,t166,t6]
set_option maxHeartbeats 0 in
theorem b834 : Ban 228 8 v825 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v826 : List ℕ := [t0,t1,t2,t168,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b835 : Ban 228 8 v826 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v827 : List ℕ := [t0,t1,t2,t168,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b836 : Ban 228 8 v827 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v828 : List ℕ := [t0,t1,t2,t3,t4,t169,t6]
set_option maxHeartbeats 0 in
theorem b837 : Ban 228 8 v828 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v829 : List ℕ := [t0,t1,t2,t3,t4,t169,t40,t6]
set_option maxHeartbeats 0 in
theorem b838 : Ban 228 8 v829 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v830 : List ℕ := [t170,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b839 : Ban 228 8 v830 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v831 : List ℕ := [t0,t1,t2,t3,t4,t40,t6,t171]
set_option maxHeartbeats 0 in
theorem b840 : Ban 228 8 v831 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v832 : List ℕ := [t0,t1,t2,t172,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b841 : Ban 228 8 v832 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v833 : List ℕ := [t0,t1,t2,t3,t4,t40,t173,t6]
set_option maxHeartbeats 0 in
theorem b842 : Ban 228 8 v833 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v834 : List ℕ := [t174,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b843 : Ban 228 8 v834 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v835 : List ℕ := [t0,t1,t2,t3,t4,t40,t175,t6]
set_option maxHeartbeats 0 in
theorem b844 : Ban 228 8 v835 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v836 : List ℕ := [t0,t1,t2,t3,t176,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b845 : Ban 228 8 v836 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v837 : List ℕ := [t0,t1,t2,t3,t4,t177,t40,t6]
set_option maxHeartbeats 0 in
theorem b846 : Ban 228 8 v837 := viaCut p127_114 w48 (by decide) (by decide +kernel) (by decide +kernel)
def v838 : List ℕ := [t178,t0,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b847 : Ban 228 8 v838 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v839 : List ℕ := [t0,t1,t2,t3,t4,t40,t6,t179]
set_option maxHeartbeats 0 in
theorem b848 : Ban 228 8 v839 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v840 : List ℕ := [t0,t1,t2,t3,t180,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b849 : Ban 228 8 v840 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v841 : List ℕ := [t0,t1,t2,t3,t4,t40,t181,t6]
set_option maxHeartbeats 0 in
theorem b850 : Ban 228 8 v841 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v842 : List ℕ := [t0,t1,t2,t3,t4,t182,t40,t6]
set_option maxHeartbeats 0 in
theorem b851 : Ban 228 8 v842 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v843 : List ℕ := [t0,t1,t2,t3,t4,t6,t183]
set_option maxHeartbeats 0 in
theorem b852 : Ban 228 8 v843 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v844 : List ℕ := [t0,t1,t2,t3,t4,t40,t6,t183]
set_option maxHeartbeats 0 in
theorem b853 : Ban 228 8 v844 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v845 : List ℕ := [t0,t184,t1,t2,t3,t4,t6]
set_option maxHeartbeats 0 in
theorem b854 : Ban 228 8 v845 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v846 : List ℕ := [t0,t184,t1,t2,t3,t4,t40,t6]
set_option maxHeartbeats 0 in
theorem b855 : Ban 228 8 v846 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v847 : List ℕ := [t0,t1,t2,t3,t4,t185,t40,t6]
set_option maxHeartbeats 0 in
theorem b856 : Ban 228 8 v847 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b857 : Ban 228 9 v729 := viaBranch (ws := [v730,v27,v237,v731,v732,v733,v734,v735,v736,v737,v738,v739,v740,v741,v742,v743,v428,v569,v744,v745,v746,v747,v748,v749,v750,v751,v752,v753,v754,v755,v756,v757,v758,v759,v760,v761,v762,v763,v764,v765,v766,v767,v768,v769,v770,v771,v772,v773,v774,v775,v776,v777,v778,v779,v780,v781,v782,v783,v785,v786,v787,v788,v789,v790,v791,v792,v793,v794,v795,v796,v797,v798,v799,v800,v801,v802,v803,v804,v805,v806,v807,v808,v809,v810,v811,v812,v813,v814,v815,v816,v817,v818,v819,v820,v821,v822,v823,v824,v825,v826,v827,v828,v829,v830,v831,v832,v833,v834,v835,v836,v837,v838,v839,v840,v841,v842,v843,v844,v845,v846,v847]) (consBan b739 (consBan b240 (consBan b241 (consBan b740 (consBan b741 (consBan b742 (consBan b743 (consBan b744 (consBan b745 (consBan b746 (consBan b747 (consBan b748 (consBan b749 (consBan b750 (consBan b751 (consBan b752 (consBan b576 (consBan b577 (consBan b753 (consBan b754 (consBan b755 (consBan b756 (consBan b757 (consBan b758 (consBan b759 (consBan b760 (consBan b761 (consBan b762 (consBan b763 (consBan b764 (consBan b765 (consBan b766 (consBan b767 (consBan b768 (consBan b769 (consBan b770 (consBan b771 (consBan b772 (consBan b773 (consBan b774 (consBan b775 (consBan b776 (consBan b777 (consBan b778 (consBan b779 (consBan b780 (consBan b781 (consBan b782 (consBan b783 (consBan b784 (consBan b785 (consBan b786 (consBan b787 (consBan b788 (consBan b789 (consBan b790 (consBan b791 (consBan b793 (consBan b794 (consBan b795 (consBan b796 (consBan b797 (consBan b798 (consBan b799 (consBan b800 (consBan b801 (consBan b802 (consBan b803 (consBan b804 (consBan b805 (consBan b806 (consBan b807 (consBan b808 (consBan b809 (consBan b810 (consBan b811 (consBan b812 (consBan b813 (consBan b814 (consBan b815 (consBan b816 (consBan b817 (consBan b818 (consBan b819 (consBan b820 (consBan b821 (consBan b822 (consBan b823 (consBan b824 (consBan b825 (consBan b826 (consBan b827 (consBan b828 (consBan b829 (consBan b830 (consBan b831 (consBan b832 (consBan b833 (consBan b834 (consBan b835 (consBan b836 (consBan b837 (consBan b838 (consBan b839 (consBan b840 (consBan b841 (consBan b842 (consBan b843 (consBan b844 (consBan b845 (consBan b846 (consBan b847 (consBan b848 (consBan b849 (consBan b850 (consBan b851 (consBan b852 (consBan b853 (consBan b854 (consBan b855 (consBan b856 (nilBan 228 8)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
def v848 : List ℕ := [t1,t2,t3,t4,t5,t40,t6]
set_option maxHeartbeats 0 in
theorem b858 : Ban 228 9 v848 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v849 : List ℕ := [t0,t1,t2,t3,t4,t5,t40,t6]
set_option maxHeartbeats 0 in
theorem b859 : Ban 228 9 v849 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v850 : List ℕ := [t186,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b860 : Ban 228 9 v850 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v851 : List ℕ := [t186,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b861 : Ban 228 9 v851 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b862 : Ban 228 9 v756 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v852 : List ℕ := [t0,t1,t2,t3,t4,t187,t5,t6]
set_option maxHeartbeats 0 in
theorem b863 : Ban 228 9 v852 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v853 : List ℕ := [t188,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b864 : Ban 228 9 v853 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v854 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t189]
set_option maxHeartbeats 0 in
theorem b865 : Ban 228 9 v854 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v855 : List ℕ := [t190,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b866 : Ban 228 9 v855 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v856 : List ℕ := [t0,t1,t2,t3,t4,t5,t191,t6]
set_option maxHeartbeats 0 in
theorem b867 : Ban 228 9 v856 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v857 : List ℕ := [t0,t250,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b868 : Ban 228 9 v857 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v858 : List ℕ := [t0,t1,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b869 : Ban 228 9 v858 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v859 : List ℕ := [t0,t2,t251,t3,t4,t5,t6]
def v860 : List ℕ := [t14,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b870 : Ban 228 8 v860 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v861 : List ℕ := [t0,t2,t251,t18,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b871 : Ban 228 8 v861 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v862 : List ℕ := [t19,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b872 : Ban 228 8 v862 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v863 : List ℕ := [t0,t20,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b873 : Ban 228 8 v863 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v864 : List ℕ := [t359,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b874 : Ban 228 8 v864 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v865 : List ℕ := [t0,t2,t251,t42,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b875 : Ban 228 8 v865 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v866 : List ℕ := [t360,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b876 : Ban 228 8 v866 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v867 : List ℕ := [t0,t2,t361,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b877 : Ban 228 8 v867 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v868 : List ℕ := [t0,t2,t361,t251,t3,t4,t5,t6]
def p127_98Slow : Projection 228 12 := pick [76,78,91,93,152,154,167,169,209,211,224,226] rfl (by decide +kernel) (by decide)
def p127_98T : LookupTree := (.fork t251 t488 (.fork t2 t488 (.fork t0 t15 (.fork t447 t488 (.fork t408 t488 .empty .empty) .empty) (.fork t1 t488 .empty .empty)) (.fork t410 t488 (.fork t361 t488 .empty .empty) (.fork t402 t488 .empty .empty))) (.fork t92 t488 (.fork t435 t488 (.fork t3 t488 .empty .empty) (.fork t449 t488 .empty .empty)) (.fork t5 t488 (.fork t4 t16 .empty .empty) (.fork t6 t17 .empty .empty))))
set_option maxHeartbeats 0 in
def p127_98 : Projection 228 12 := cached p127_98Slow p127_98T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b878 : Ban 228 8 v868 := viaCut p127_98 w7 (by decide) (by decide +kernel) (by decide +kernel)
def v869 : List ℕ := [t21,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b879 : Ban 228 8 v869 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v870 : List ℕ := [t2,t251,t3,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b880 : Ban 228 8 v870 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v871 : List ℕ := [t0,t2,t251,t3,t22,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b881 : Ban 228 8 v871 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v872 : List ℕ := [t28,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b882 : Ban 228 8 v872 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v873 : List ℕ := [t28,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b883 : Ban 228 8 v873 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v874 : List ℕ := [t0,t2,t251,t29,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b884 : Ban 228 8 v874 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v875 : List ℕ := [t0,t2,t251,t29,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b885 : Ban 228 8 v875 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v876 : List ℕ := [t30,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b886 : Ban 228 8 v876 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v877 : List ℕ := [t0,t2,t251,t3,t4,t31,t5,t6]
set_option maxHeartbeats 0 in
theorem b887 : Ban 228 8 v877 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v878 : List ℕ := [t37,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b888 : Ban 228 8 v878 := viaCut p127_114 w48 (by decide) (by decide +kernel) (by decide +kernel)
def v879 : List ℕ := [t0,t2,t251,t3,t38,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b889 : Ban 228 8 v879 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v880 : List ℕ := [t39,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b890 : Ban 228 8 v880 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v881 : List ℕ := [t2,t251,t3,t4,t5,t40,t6]
set_option maxHeartbeats 0 in
theorem b891 : Ban 228 8 v881 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v882 : List ℕ := [t0,t2,t251,t3,t4,t5,t40,t6]
set_option maxHeartbeats 0 in
theorem b892 : Ban 228 8 v882 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v883 : List ℕ := [t186,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b893 : Ban 228 8 v883 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v884 : List ℕ := [t186,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b894 : Ban 228 8 v884 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v885 : List ℕ := [t0,t2,t251,t3,t4,t187,t6]
set_option maxHeartbeats 0 in
theorem b895 : Ban 228 8 v885 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v886 : List ℕ := [t0,t2,t251,t3,t4,t187,t5,t6]
set_option maxHeartbeats 0 in
theorem b896 : Ban 228 8 v886 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v887 : List ℕ := [t188,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b897 : Ban 228 8 v887 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v888 : List ℕ := [t0,t2,t251,t3,t4,t5,t6,t189]
set_option maxHeartbeats 0 in
theorem b898 : Ban 228 8 v888 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v889 : List ℕ := [t190,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b899 : Ban 228 8 v889 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v890 : List ℕ := [t0,t2,t251,t3,t4,t5,t191,t6]
set_option maxHeartbeats 0 in
theorem b900 : Ban 228 8 v890 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v891 : List ℕ := [t252,t0,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b901 : Ban 228 8 v891 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v892 : List ℕ := [t252,t0,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b902 : Ban 228 8 v892 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v893 : List ℕ := [t252,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b903 : Ban 228 8 v893 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v894 : List ℕ := [t0,t91,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b904 : Ban 228 8 v894 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v895 : List ℕ := [t0,t2,t251,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b905 : Ban 228 8 v895 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v896 : List ℕ := [t0,t2,t251,t3,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b906 : Ban 228 8 v896 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v897 : List ℕ := [t0,t147,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b907 : Ban 228 8 v897 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v898 : List ℕ := [t0,t2,t251,t148,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b908 : Ban 228 8 v898 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v899 : List ℕ := [t0,t2,t251,t148,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b909 : Ban 228 8 v899 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v900 : List ℕ := [t149,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b910 : Ban 228 8 v900 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v901 : List ℕ := [t0,t251,t3,t4,t150,t5,t6]
set_option maxHeartbeats 0 in
theorem w52 : Wide 60 6 v700 := viaSub (ws := [v700]) (consBan b708 (nilBan 60 6)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b911 : Ban 228 8 v901 := viaCut p127_91 w52 (by decide) (by decide +kernel) (by decide +kernel)
def v902 : List ℕ := [t0,t2,t251,t3,t4,t150,t5,t6]
set_option maxHeartbeats 0 in
theorem b912 : Ban 228 8 v902 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v903 : List ℕ := [t0,t151,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b913 : Ban 228 8 v903 := viaCut p127_91 w52 (by decide) (by decide +kernel) (by decide +kernel)
def v904 : List ℕ := [t0,t151,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b914 : Ban 228 8 v904 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v905 : List ℕ := [t0,t2,t251,t3,t152,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b915 : Ban 228 8 v905 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v906 : List ℕ := [t228,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b916 : Ban 228 8 v906 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v907 : List ℕ := [t0,t2,t251,t3,t4,t5,t229,t6]
set_option maxHeartbeats 0 in
theorem b917 : Ban 228 8 v907 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v908 : List ℕ := [t0,t230,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b918 : Ban 228 8 v908 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v909 : List ℕ := [t0,t2,t251,t3,t4,t231,t5,t6]
set_option maxHeartbeats 0 in
theorem b919 : Ban 228 8 v909 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v910 : List ℕ := [t157,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b920 : Ban 228 8 v910 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v911 : List ℕ := [t0,t251,t3,t4,t5,t6,t158]
def v912 : List ℕ := [t32,t34,t333,t36,t349]
def v913 : List ℕ := [t317,t32,t34,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b921 : Ban 60 5 v913 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v914 : List ℕ := [t32,t262,t333,t36,t349]
def v915 : List ℕ := [t111,t281,t98,t284]
def a27_0431Slow : Projection 18 18 := pick [0,1,6,7,4,8,2,3,5,9,10,15,16,13,17,11,12,14] rfl (by decide +kernel) (by decide)
def a27_0431T : LookupTree := (.fork t98 t111 (.fork t97 t284 (.fork t111 t98 .empty .empty) (.fork t281 t99 .empty .empty)) (.fork t99 t281 (.fork t284 t97 .empty .empty) .empty))
set_option maxHeartbeats 0 in
def a27_0431 : Projection 18 18 := cached a27_0431Slow a27_0431T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b922 : Ban 18 4 v915 := viaPerm a27_0431 a27_0431 b141 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w53 : Wide 18 4 v915 := viaSub (ws := [v915]) (consBan b922 (nilBan 18 4)) (by decide) (by decide +kernel)
def p91_27Slow : Projection 60 18 := pick [0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,16,17,18] rfl (by decide +kernel) (by decide)
def p91_27T : LookupTree := (.fork t333 t284 (.fork t34 t216 (.fork t32 t111 (.fork t387 t488 .empty .empty) .empty) (.fork t262 t281 .empty .empty)) (.fork t36 t488 (.fork t393 t488 .empty .empty) (.fork t349 t98 .empty .empty)))
set_option maxHeartbeats 0 in
def p91_27 : Projection 60 18 := cached p91_27Slow p91_27T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b923 : Ban 60 5 v914 := viaCut p91_27 w53 (by decide) (by decide +kernel) (by decide +kernel)
def v916 : List ℕ := [t34,t262,t333,t36,t349]
def v917 : List ℕ := [t216,t281,t98,t284]
set_option maxHeartbeats 0 in
theorem b924 : Ban 18 4 v917 := viaPerm a27_3401 a27_3401 b503 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w54 : Wide 18 4 v917 := viaSub (ws := [v917]) (consBan b924 (nilBan 18 4)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b925 : Ban 60 5 v916 := viaCut p91_27 w54 (by decide) (by decide +kernel) (by decide +kernel)
def v918 : List ℕ := [t32,t34,t262,t333,t36,t349]
def v919 : List ℕ := [t362,t363,t206,t364]
set_option maxHeartbeats 0 in
theorem b926 : Ban 28 4 v919 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w55 : Wide 28 4 v919 := viaSub (ws := [v919]) (consBan b926 (nilBan 28 4)) (by decide) (by decide +kernel)
def p91_89Slow : Projection 60 28 := pick [0,1,4,6,7,8,9,20,21,24,26,27,28,29,40,41,44,46,47,48,49,50,51,54,56,57,58,59] rfl (by decide +kernel) (by decide)
def p91_89T : LookupTree := (.fork t333 t363 (.fork t319 t362 (.fork t32 t488 (.fork t387 t388 (.fork t368 t488 .empty .empty) (.fork t318 t488 .empty .empty)) (.fork t376 t377 (.fork t374 t375 .empty .empty) .empty)) (.fork t262 t362 (.fork t34 t362 (.fork t346 t379 .empty .empty) .empty) (.fork t391 t392 (.fork t367 t363 .empty .empty) .empty))) (.fork t345 t378 (.fork t36 t206 (.fork t347 t380 (.fork t43 t363 .empty .empty) (.fork t327 t206 .empty .empty)) (.fork t385 t386 (.fork t325 t206 .empty .empty) .empty)) (.fork t389 t390 (.fork t349 t364 (.fork t371 t364 .empty .empty) .empty) (.fork t382 t383 (.fork t369 t364 .empty .empty) .empty))))
set_option maxHeartbeats 0 in
def p91_89 : Projection 60 28 := cached p91_89Slow p91_89T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b927 : Ban 60 5 v918 := viaCut p91_89 w55 (by decide) (by decide +kernel) (by decide +kernel)
def v920 : List ℕ := [t318,t34,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b928 : Ban 60 5 v920 := viaCut p91_89 w55 (by decide) (by decide +kernel) (by decide +kernel)
def v921 : List ℕ := [t318,t32,t34,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b929 : Ban 60 5 v921 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v922 : List ℕ := [t32,t319,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b930 : Ban 60 5 v922 := viaCut p91_89 w55 (by decide) (by decide +kernel) (by decide +kernel)
def v923 : List ℕ := [t32,t319,t34,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b931 : Ban 60 5 v923 := viaCut p91_89 w55 (by decide) (by decide +kernel) (by decide +kernel)
def v924 : List ℕ := [t365,t32,t34,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b932 : Ban 60 5 v924 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v925 : List ℕ := [t32,t34,t43,t36,t349]
set_option maxHeartbeats 0 in
theorem b933 : Ban 60 5 v925 := viaCut p91_89 w55 (by decide) (by decide +kernel) (by decide +kernel)
def v926 : List ℕ := [t32,t34,t333,t43,t36,t349]
set_option maxHeartbeats 0 in
theorem b934 : Ban 60 5 v926 := viaCut p91_89 w55 (by decide) (by decide +kernel) (by decide +kernel)
def v927 : List ℕ := [t366,t32,t34,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b935 : Ban 60 5 v927 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v928 : List ℕ := [t32,t34,t367,t36,t349]
set_option maxHeartbeats 0 in
theorem b936 : Ban 60 5 v928 := viaCut p91_89 w55 (by decide) (by decide +kernel) (by decide +kernel)
def v929 : List ℕ := [t32,t34,t367,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b937 : Ban 60 5 v929 := viaCut p91_89 w55 (by decide) (by decide +kernel) (by decide +kernel)
def v930 : List ℕ := [t324,t32,t34,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b938 : Ban 60 5 v930 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v931 : List ℕ := [t32,t34,t333,t325,t349]
set_option maxHeartbeats 0 in
theorem b939 : Ban 60 5 v931 := viaCut p91_89 w55 (by decide) (by decide +kernel) (by decide +kernel)
def v932 : List ℕ := [t32,t34,t333,t36,t325,t349]
set_option maxHeartbeats 0 in
theorem b940 : Ban 60 5 v932 := viaCut p91_89 w55 (by decide) (by decide +kernel) (by decide +kernel)
def v933 : List ℕ := [t326,t32,t34,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b941 : Ban 60 5 v933 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v934 : List ℕ := [t32,t34,t333,t327,t349]
set_option maxHeartbeats 0 in
theorem b942 : Ban 60 5 v934 := viaCut p91_89 w55 (by decide) (by decide +kernel) (by decide +kernel)
def v935 : List ℕ := [t32,t34,t333,t327,t36,t349]
set_option maxHeartbeats 0 in
theorem b943 : Ban 60 5 v935 := viaCut p91_89 w55 (by decide) (by decide +kernel) (by decide +kernel)
def v936 : List ℕ := [t368,t34,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b944 : Ban 60 5 v936 := viaCut p91_89 w55 (by decide) (by decide +kernel) (by decide +kernel)
def v937 : List ℕ := [t368,t32,t34,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b945 : Ban 60 5 v937 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v938 : List ℕ := [t32,t34,t333,t36,t349,t369]
set_option maxHeartbeats 0 in
theorem b946 : Ban 60 5 v938 := viaCut p91_89 w55 (by decide) (by decide +kernel) (by decide +kernel)
def v939 : List ℕ := [t370,t32,t34,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b947 : Ban 60 5 v939 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v940 : List ℕ := [t34,t333,t36,t371,t349]
set_option maxHeartbeats 0 in
theorem b948 : Ban 60 5 v940 := viaSmall (by decide +kernel) (by decide)
def v941 : List ℕ := [t32,t34,t333,t36,t371,t349]
set_option maxHeartbeats 0 in
theorem b949 : Ban 60 5 v941 := viaCut p91_89 w55 (by decide) (by decide +kernel) (by decide +kernel)
def v942 : List ℕ := [t32,t372,t34,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b950 : Ban 60 5 v942 := viaSmall (by decide +kernel) (by decide)
def v943 : List ℕ := [t32,t34,t333,t373,t36,t349]
set_option maxHeartbeats 0 in
theorem b951 : Ban 60 5 v943 := viaSmall (by decide +kernel) (by decide)
def v944 : List ℕ := [t32,t374,t34,t333,t36,t349]
def v945 : List ℕ := [t375,t362,t363,t206,t364]
set_option maxHeartbeats 0 in
theorem b952 : Ban 28 4 v945 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w56 : Wide 28 4 v945 := viaSub (ws := [v919,v945]) (consBan b926 (consBan b952 (nilBan 28 4))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b953 : Ban 60 5 v944 := viaCut p91_89 w56 (by decide) (by decide +kernel) (by decide +kernel)
def v946 : List ℕ := [t32,t376,t34,t333,t36,t349]
def v947 : List ℕ := [t377,t362,t363,t206,t364]
set_option maxHeartbeats 0 in
theorem b954 : Ban 28 4 v947 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w57 : Wide 28 4 v947 := viaSub (ws := [v919,v947]) (consBan b926 (consBan b954 (nilBan 28 4))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b955 : Ban 60 5 v946 := viaCut p91_89 w57 (by decide) (by decide +kernel) (by decide +kernel)
def v948 : List ℕ := [t344,t32,t34,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b956 : Ban 60 5 v948 := viaSmall (by decide +kernel) (by decide)
def v949 : List ℕ := [t32,t34,t333,t345,t349]
set_option maxHeartbeats 0 in
theorem b957 : Ban 10 4 v510 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w58 : Wide 10 4 v510 := viaSub (ws := [v510]) (consBan b957 (nilBan 10 4)) (by decide) (by decide +kernel)
def p91_88Slow : Projection 60 10 := pick [40,44,46,48,49,50,54,56,58,59] rfl (by decide +kernel) (by decide)
def p91_88T : LookupTree := (.fork t333 t286 (.fork t34 t285 (.fork t32 t488 .empty .empty) .empty) (.fork t349 t288 (.fork t345 t287 .empty .empty) .empty))
set_option maxHeartbeats 0 in
def p91_88 : Projection 60 10 := cached p91_88Slow p91_88T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b958 : Ban 60 5 v949 := viaCut p91_88 w58 (by decide) (by decide +kernel) (by decide +kernel)
def v950 : List ℕ := [t32,t34,t333,t36,t345,t349]
def v951 : List ℕ := [t362,t363,t378,t364]
def p89_88Slow : Projection 28 10 := pick [14,16,17,19,20,21,23,24,26,27] rfl (by decide +kernel) (by decide)
def p89_88T : LookupTree := (.fork t378 t287 (.fork t363 t286 (.fork t362 t285 .empty .empty) .empty) (.fork t364 t288 .empty .empty))
set_option maxHeartbeats 0 in
def p89_88 : Projection 28 10 := cached p89_88Slow p89_88T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b959 : Ban 28 4 v951 := viaCut p89_88 w58 (by decide) (by decide +kernel) (by decide +kernel)
def v952 : List ℕ := [t362,t363,t206,t378,t364]
set_option maxHeartbeats 0 in
theorem b960 : Ban 28 4 v952 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w59 : Wide 28 4 v952 := viaSub (ws := [v919,v951,v952]) (consBan b926 (consBan b959 (consBan b960 (nilBan 28 4)))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b961 : Ban 60 5 v950 := viaCut p91_89 w59 (by decide) (by decide +kernel) (by decide +kernel)
def v953 : List ℕ := [t32,t346,t34,t333,t36,t349]
def v954 : List ℕ := [t379,t362,t363,t206,t364]
set_option maxHeartbeats 0 in
theorem b962 : Ban 28 4 v954 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w60 : Wide 28 4 v954 := viaSub (ws := [v919,v954]) (consBan b926 (consBan b962 (nilBan 28 4))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b963 : Ban 60 5 v953 := viaCut p91_89 w60 (by decide) (by decide +kernel) (by decide +kernel)
def v955 : List ℕ := [t32,t34,t333,t347,t349]
def v956 : List ℕ := [t362,t363,t380,t364]
set_option maxHeartbeats 0 in
theorem b964 : Ban 28 4 v956 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w61 : Wide 28 4 v956 := viaSub (ws := [v956]) (consBan b964 (nilBan 28 4)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b965 : Ban 60 5 v955 := viaCut p91_89 w61 (by decide) (by decide +kernel) (by decide +kernel)
def v957 : List ℕ := [t32,t34,t333,t347,t36,t349]
set_option maxHeartbeats 0 in
theorem b966 : Ban 60 5 v957 := viaSmall (by decide +kernel) (by decide)
def v958 : List ℕ := [t32,t381,t34,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b967 : Ban 60 5 v958 := viaSmall (by decide +kernel) (by decide)
def v959 : List ℕ := [t32,t34,t333,t36,t349,t382]
def v960 : List ℕ := [t362,t363,t206,t364,t383]
set_option maxHeartbeats 0 in
theorem b968 : Ban 28 4 v960 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w62 : Wide 28 4 v960 := viaSub (ws := [v919,v960]) (consBan b926 (consBan b968 (nilBan 28 4))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b969 : Ban 60 5 v959 := viaCut p91_89 w62 (by decide) (by decide +kernel) (by decide +kernel)
def v961 : List ℕ := [t32,t384,t34,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b970 : Ban 60 5 v961 := viaSmall (by decide +kernel) (by decide)
def v962 : List ℕ := [t32,t34,t333,t36,t385,t349]
def v963 : List ℕ := [t362,t363,t206,t386,t364]
set_option maxHeartbeats 0 in
theorem b971 : Ban 28 4 v963 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w63 : Wide 28 4 v963 := viaSub (ws := [v919,v963]) (consBan b926 (consBan b971 (nilBan 28 4))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b972 : Ban 60 5 v962 := viaCut p91_89 w63 (by decide) (by decide +kernel) (by decide +kernel)
def v964 : List ℕ := [t387,t32,t34,t333,t349]
def v965 : List ℕ := [t388,t362,t363,t364]
set_option maxHeartbeats 0 in
theorem b973 : Ban 28 4 v965 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w64 : Wide 28 4 v965 := viaSub (ws := [v965]) (consBan b973 (nilBan 28 4)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b974 : Ban 60 5 v964 := viaCut p91_89 w64 (by decide) (by decide +kernel) (by decide +kernel)
def v966 : List ℕ := [t387,t32,t34,t333,t36,t349]
def v967 : List ℕ := [t111,t216,t98,t284]
set_option maxHeartbeats 0 in
theorem b975 : Ban 18 3 v967 := viaPerm a27_3401 a27_3401 b493 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w65 : Wide 18 3 v967 := viaSub (ws := [v967]) (consBan b975 (nilBan 18 3)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b976 : Ban 60 5 v966 := viaCut p91_27 w65 (by decide) (by decide +kernel) (by decide +kernel)
def v968 : List ℕ := [t32,t34,t333,t36,t349,t389]
def v969 : List ℕ := [t362,t363,t206,t364,t390]
set_option maxHeartbeats 0 in
theorem b977 : Ban 28 4 v969 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w66 : Wide 28 4 v969 := viaSub (ws := [v919,v969]) (consBan b926 (consBan b977 (nilBan 28 4))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b978 : Ban 60 5 v968 := viaCut p91_89 w66 (by decide) (by decide +kernel) (by decide +kernel)
def v970 : List ℕ := [t32,t34,t391,t333,t349]
def v971 : List ℕ := [t362,t392,t363,t364]
set_option maxHeartbeats 0 in
theorem b979 : Ban 28 4 v971 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w67 : Wide 28 4 v971 := viaSub (ws := [v971]) (consBan b979 (nilBan 28 4)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b980 : Ban 60 5 v970 := viaCut p91_89 w67 (by decide) (by decide +kernel) (by decide +kernel)
def v972 : List ℕ := [t32,t34,t391,t333,t36,t349]
def v973 : List ℕ := [t362,t392,t363,t206,t364]
set_option maxHeartbeats 0 in
theorem b981 : Ban 28 4 v973 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w68 : Wide 28 4 v973 := viaSub (ws := [v971,v919,v973]) (consBan b979 (consBan b926 (consBan b981 (nilBan 28 4)))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b982 : Ban 60 5 v972 := viaCut p91_89 w68 (by decide) (by decide +kernel) (by decide +kernel)
def v974 : List ℕ := [t32,t34,t333,t393,t36,t349]
set_option maxHeartbeats 0 in
theorem b983 : Ban 60 5 v974 := viaCut p91_27 w65 (by decide) (by decide +kernel) (by decide +kernel)
def v975 : List ℕ := [t32,t34,t394,t333,t36]
set_option maxHeartbeats 0 in
theorem b984 : Ban 60 5 v975 := viaSmall (by decide +kernel) (by decide)
def v976 : List ℕ := [t32,t34,t394,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b985 : Ban 60 5 v976 := viaSmall (by decide +kernel) (by decide)
def v977 : List ℕ := [t395,t32,t34,t333,t36]
def p91_82Slow : Projection 60 12 := pick [10,12,16,19,30,32,36,39,50,52,56,59] rfl (by decide +kernel) (by decide)
def p91_82T : LookupTree := (.fork t34 t488 (.fork t32 t15 (.fork t395 t488 .empty .empty) .empty) (.fork t36 t17 (.fork t333 t16 .empty .empty) .empty))
set_option maxHeartbeats 0 in
def p91_82 : Projection 60 12 := cached p91_82Slow p91_82T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b986 : Ban 60 5 v977 := viaCut p91_82 w9 (by decide) (by decide +kernel) (by decide +kernel)
def v978 : List ℕ := [t395,t32,t34,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b987 : Ban 60 5 v978 := viaSmall (by decide +kernel) (by decide)
def v979 : List ℕ := [t32,t34,t350,t333,t36]
set_option maxHeartbeats 0 in
theorem b988 : Ban 60 5 v979 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v980 : List ℕ := [t32,t34,t350,t333,t349]
set_option maxHeartbeats 0 in
theorem b989 : Ban 60 5 v980 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v981 : List ℕ := [t32,t34,t350,t333,t36,t349]
set_option maxHeartbeats 0 in
theorem b990 : Ban 60 5 v981 := viaCut p91_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b991 : Ban 60 6 v912 := viaBranch (ws := [v913,v914,v916,v918,v920,v921,v922,v923,v924,v925,v926,v927,v928,v929,v930,v931,v932,v933,v934,v935,v936,v937,v938,v939,v940,v941,v942,v943,v944,v946,v948,v949,v950,v953,v955,v957,v958,v959,v961,v962,v964,v966,v968,v970,v972,v974,v975,v976,v977,v978,v979,v980,v981]) (consBan b921 (consBan b923 (consBan b925 (consBan b927 (consBan b928 (consBan b929 (consBan b930 (consBan b931 (consBan b932 (consBan b933 (consBan b934 (consBan b935 (consBan b936 (consBan b937 (consBan b938 (consBan b939 (consBan b940 (consBan b941 (consBan b942 (consBan b943 (consBan b944 (consBan b945 (consBan b946 (consBan b947 (consBan b948 (consBan b949 (consBan b950 (consBan b951 (consBan b953 (consBan b955 (consBan b956 (consBan b958 (consBan b961 (consBan b963 (consBan b965 (consBan b966 (consBan b967 (consBan b969 (consBan b970 (consBan b972 (consBan b974 (consBan b976 (consBan b978 (consBan b980 (consBan b982 (consBan b983 (consBan b984 (consBan b985 (consBan b986 (consBan b987 (consBan b988 (consBan b989 (consBan b990 (nilBan 60 5)))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w69 : Wide 60 6 v912 := viaSub (ws := [v912]) (consBan b991 (nilBan 60 6)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b992 : Ban 228 8 v911 := viaCut p127_91 w69 (by decide) (by decide +kernel) (by decide +kernel)
def v982 : List ℕ := [t0,t2,t251,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b993 : Ban 228 8 v982 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v983 : List ℕ := [t0,t159,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b994 : Ban 228 8 v983 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v984 : List ℕ := [t0,t159,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b995 : Ban 228 8 v984 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v985 : List ℕ := [t0,t2,t251,t3,t4,t5,t160,t6]
set_option maxHeartbeats 0 in
theorem b996 : Ban 228 8 v985 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v986 : List ℕ := [t0,t396,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b997 : Ban 228 8 v986 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v987 : List ℕ := [t0,t2,t251,t3,t397,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b998 : Ban 228 8 v987 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v988 : List ℕ := [t0,t398,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b999 : Ban 228 8 v988 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v989 : List ℕ := [t0,t2,t251,t399,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1000 : Ban 228 8 v989 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v990 : List ℕ := [t400,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1001 : Ban 228 8 v990 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v991 : List ℕ := [t0,t2,t251,t3,t4,t401,t5,t6]
set_option maxHeartbeats 0 in
theorem b1002 : Ban 228 8 v991 := viaCut p127_91 w52 (by decide) (by decide +kernel) (by decide +kernel)
def v992 : List ℕ := [t0,t2,t402,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1003 : Ban 228 8 v992 := viaCut p127_98 w7 (by decide) (by decide +kernel) (by decide +kernel)
def v993 : List ℕ := [t0,t2,t251,t3,t403,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1004 : Ban 228 8 v993 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v994 : List ℕ := [t404,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1005 : Ban 228 8 v994 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v995 : List ℕ := [t0,t2,t3,t4,t5,t405,t6]
set_option maxHeartbeats 0 in
theorem b1006 : Ban 228 8 v995 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v996 : List ℕ := [t0,t2,t251,t3,t4,t5,t405,t6]
set_option maxHeartbeats 0 in
theorem b1007 : Ban 228 8 v996 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v997 : List ℕ := [t0,t2,t406,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1008 : Ban 228 8 v997 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v998 : List ℕ := [t0,t2,t406,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1009 : Ban 228 8 v998 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v999 : List ℕ := [t0,t2,t251,t3,t4,t407,t5,t6]
set_option maxHeartbeats 0 in
theorem b1010 : Ban 228 8 v999 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1000 : List ℕ := [t408,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1011 : Ban 228 8 v1000 := viaCut p127_98 w7 (by decide) (by decide +kernel) (by decide +kernel)
def v1001 : List ℕ := [t0,t2,t251,t3,t4,t5,t6,t409]
def v1002 : List ℕ := [t32,t34,t35,t333,t36,t389]
set_option maxHeartbeats 0 in
theorem b1012 : Ban 60 6 v1002 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w70 : Wide 60 6 v1002 := viaSub (ws := [v700,v1002]) (consBan b708 (consBan b1012 (nilBan 60 6))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1013 : Ban 228 8 v1001 := viaCut p127_91 w70 (by decide) (by decide +kernel) (by decide +kernel)
def v1003 : List ℕ := [t0,t2,t410,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1014 : Ban 228 8 v1003 := viaCut p127_98 w7 (by decide) (by decide +kernel) (by decide +kernel)
def v1004 : List ℕ := [t0,t2,t251,t3,t4,t5,t411,t6]
def a114_6145Slow : Projection 30 30 := pick [15,19,16,17,18,20,24,21,22,23,0,4,1,2,3,25,29,26,27,28,5,9,6,7,8,10,14,11,12,13] rfl (by decide +kernel) (by decide)
def a114_6145T : LookupTree := (.fork t10 t11 (.fork t9 t10 (.fork t8 t9 .empty .empty) .empty) (.fork t11 t8 (.fork t64 t51 .empty .empty) .empty))
set_option maxHeartbeats 0 in
def a114_6145 : Projection 30 30 := cached a114_6145Slow a114_6145T (by decide +kernel)
def a114_4561Slow : Projection 30 30 := pick [10,12,13,14,11,20,22,23,24,21,25,27,28,29,26,0,2,3,4,1,5,7,8,9,6,15,17,18,19,16] rfl (by decide +kernel) (by decide)
def a114_4561T : LookupTree := (.fork t9 t8 (.fork t8 t11 (.fork t51 t64 .empty .empty) .empty) (.fork t11 t10 (.fork t10 t9 .empty .empty) .empty))
set_option maxHeartbeats 0 in
def a114_4561 : Projection 30 30 := cached a114_4561Slow a114_4561T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1015 : Ban 30 6 v53 := viaPerm a114_6145 a114_4561 b550 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w71 : Wide 30 6 v53 := viaSub (ws := [v2,v53]) (consBan b57 (consBan b1015 (nilBan 30 6))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1016 : Ban 228 8 v1004 := viaCut p127_114 w71 (by decide) (by decide +kernel) (by decide +kernel)
def v1005 : List ℕ := [t0,t2,t251,t161,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1017 : Ban 228 8 v1005 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1006 : List ℕ := [t0,t2,t251,t3,t162,t5,t6]
set_option maxHeartbeats 0 in
theorem b1018 : Ban 228 8 v1006 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1007 : List ℕ := [t0,t2,t251,t4,t162,t5,t6]
set_option maxHeartbeats 0 in
theorem b1019 : Ban 228 8 v1007 := viaCut p127_91 w52 (by decide) (by decide +kernel) (by decide +kernel)
def v1008 : List ℕ := [t0,t2,t251,t3,t4,t162,t5,t6]
set_option maxHeartbeats 0 in
theorem b1020 : Ban 228 8 v1008 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1009 : List ℕ := [t0,t163,t2,t251,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1021 : Ban 228 8 v1009 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1010 : List ℕ := [t0,t163,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1022 : Ban 228 8 v1010 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1011 : List ℕ := [t0,t2,t251,t164,t3,t5,t6]
set_option maxHeartbeats 0 in
theorem b1023 : Ban 228 8 v1011 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1012 : List ℕ := [t0,t2,t251,t164,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1024 : Ban 228 8 v1012 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1013 : List ℕ := [t0,t232,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1025 : Ban 228 8 v1013 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1014 : List ℕ := [t0,t2,t251,t3,t4,t233,t6]
set_option maxHeartbeats 0 in
theorem b1026 : Ban 228 8 v1014 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1015 : List ℕ := [t0,t2,t251,t4,t5,t233,t6]
set_option maxHeartbeats 0 in
theorem b1027 : Ban 228 8 v1015 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1016 : List ℕ := [t0,t2,t251,t3,t4,t5,t233,t6]
set_option maxHeartbeats 0 in
theorem b1028 : Ban 228 8 v1016 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1017 : List ℕ := [t0,t2,t251,t234,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1029 : Ban 228 8 v1017 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1018 : List ℕ := [t0,t2,t251,t234,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1030 : Ban 228 8 v1018 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1019 : List ℕ := [t0,t2,t251,t3,t4,t235,t6]
set_option maxHeartbeats 0 in
theorem b1031 : Ban 228 8 v1019 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1020 : List ℕ := [t0,t2,t251,t3,t4,t235,t5,t6]
set_option maxHeartbeats 0 in
theorem b1032 : Ban 228 8 v1020 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1021 : List ℕ := [t170,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1033 : Ban 228 8 v1021 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1022 : List ℕ := [t0,t2,t251,t3,t4,t5,t6,t171]
set_option maxHeartbeats 0 in
theorem b1034 : Ban 228 8 v1022 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1023 : List ℕ := [t0,t2,t251,t172,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1035 : Ban 228 8 v1023 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1024 : List ℕ := [t0,t2,t251,t3,t4,t5,t173,t6]
set_option maxHeartbeats 0 in
theorem b1036 : Ban 228 8 v1024 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1025 : List ℕ := [t236,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1037 : Ban 228 8 v1025 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1026 : List ℕ := [t0,t2,t251,t3,t4,t5,t237,t6]
set_option maxHeartbeats 0 in
theorem b1038 : Ban 228 8 v1026 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1027 : List ℕ := [t0,t2,t251,t3,t238,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1039 : Ban 228 8 v1027 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1028 : List ℕ := [t0,t2,t251,t3,t4,t239,t5,t6]
set_option maxHeartbeats 0 in
theorem b1040 : Ban 228 8 v1028 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1029 : List ℕ := [t178,t0,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1041 : Ban 228 8 v1029 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1030 : List ℕ := [t0,t2,t251,t3,t4,t5,t6,t179]
set_option maxHeartbeats 0 in
theorem b1042 : Ban 228 8 v1030 := viaCut p127_91 w52 (by decide) (by decide +kernel) (by decide +kernel)
def v1031 : List ℕ := [t0,t2,t251,t3,t180,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1043 : Ban 228 8 v1031 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1032 : List ℕ := [t0,t2,t251,t3,t4,t5,t181,t6]
set_option maxHeartbeats 0 in
theorem b1044 : Ban 228 8 v1032 := viaCut p127_91 w52 (by decide) (by decide +kernel) (by decide +kernel)
def v1033 : List ℕ := [t0,t2,t251,t3,t4,t240,t5,t6]
set_option maxHeartbeats 0 in
theorem b1045 : Ban 228 8 v1033 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1034 : List ℕ := [t0,t2,t251,t3,t4,t5,t241]
set_option maxHeartbeats 0 in
theorem b1046 : Ban 228 8 v1034 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1035 : List ℕ := [t0,t2,t251,t3,t4,t6,t241]
def v1036 : List ℕ := [t356,t25,t195,t27,t116]
def v1037 : List ℕ := [t218,t356,t25,t195,t27,t116]
def p93_73Slow : Projection 55 12 := pick [0,1,4,9,22,23,26,31,33,34,37,42] rfl (by decide +kernel) (by decide)
def p93_73T : LookupTree := (.fork t423 t488 (.fork t219 t488 (.fork t421 t488 (.fork t139 t488 .empty .empty) (.fork t117 t488 .empty .empty)) (.fork t356 t16 (.fork t218 t488 .empty .empty) .empty)) (.fork t195 t15 (.fork t25 t488 (.fork t141 t488 .empty .empty) .empty) (.fork t116 t17 (.fork t27 t17 .empty .empty) .empty)))
set_option maxHeartbeats 0 in
def p93_73 : Projection 55 12 := cached p93_73Slow p93_73T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1047 : Ban 55 5 v1037 := viaCut p93_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1038 : List ℕ := [t25,t195,t412,t27,t116]
set_option maxHeartbeats 0 in
theorem b1048 : Ban 55 5 v1038 := viaSmall (by decide +kernel) (by decide)
def v1039 : List ℕ := [t356,t25,t195,t412,t27,t116]
set_option maxHeartbeats 0 in
theorem b1049 : Ban 55 5 v1039 := viaSmall (by decide +kernel) (by decide)
def v1040 : List ℕ := [t413,t25,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1050 : Ban 55 5 v1040 := viaSmall (by decide +kernel) (by decide)
def v1041 : List ℕ := [t413,t356,t25,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1051 : Ban 55 5 v1041 := viaSmall (by decide +kernel) (by decide)
def v1042 : List ℕ := [t219,t356,t25,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1052 : Ban 55 5 v1042 := viaCut p93_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1043 : List ℕ := [t414,t356,t25,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1053 : Ban 55 5 v1043 := viaSmall (by decide +kernel) (by decide)
def v1044 : List ℕ := [t356,t25,t195,t415,t27,t116]
set_option maxHeartbeats 0 in
theorem b1054 : Ban 55 5 v1044 := viaSmall (by decide +kernel) (by decide)
def v1045 : List ℕ := [t416,t356,t25,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1055 : Ban 55 5 v1045 := viaSmall (by decide +kernel) (by decide)
def v1046 : List ℕ := [t417,t356,t25,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1056 : Ban 55 5 v1046 := viaSmall (by decide +kernel) (by decide)
def v1047 : List ℕ := [t115,t356,t25,t195,t27,t116]
def a29_4023Slow : Projection 18 18 := pick [9,15,10,16,11,12,13,17,14,0,6,1,7,2,3,4,8,5] rfl (by decide +kernel) (by decide)
def a29_4023T : LookupTree := (.fork t98 t215 (.fork t216 t98 (.fork t111 t216 .empty .empty) .empty) (.fork t284 t97 .empty .empty))
set_option maxHeartbeats 0 in
def a29_4023 : Projection 18 18 := cached a29_4023Slow a29_4023T (by decide +kernel)
def a29_2340Slow : Projection 18 18 := pick [9,11,13,14,15,17,10,12,16,0,2,4,5,6,8,1,3,7] rfl (by decide +kernel) (by decide)
def a29_2340T : LookupTree := (.fork t216 t111 (.fork t97 t284 (.fork t215 t98 .empty .empty) .empty) (.fork t98 t216 .empty .empty))
set_option maxHeartbeats 0 in
def a29_2340 : Projection 18 18 := cached a29_2340Slow a29_2340T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1057 : Ban 18 3 v967 := viaPerm a29_4023 a29_2340 b306 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w72 : Wide 18 3 v967 := viaSub (ws := [v967]) (consBan b1057 (nilBan 18 3)) (by decide) (by decide +kernel)
def p93_29Slow : Projection 55 18 := pick [0,1,2,3,4,5,6,7,8,11,12,13,14,15,16,17,18,19] rfl (by decide +kernel) (by decide)
def p93_29T : LookupTree := (.fork t428 t488 (.fork t356 t216 (.fork t425 t488 (.fork t115 t488 .empty .empty) .empty) (.fork t195 t284 (.fork t25 t98 .empty .empty) .empty)) (.fork t27 t488 (.fork t118 t488 (.fork t142 t488 .empty .empty) .empty) (.fork t274 t281 (.fork t116 t111 .empty .empty) .empty)))
set_option maxHeartbeats 0 in
def p93_29 : Projection 55 18 := cached p93_29Slow p93_29T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1058 : Ban 55 5 v1047 := viaCut p93_29 w72 (by decide) (by decide +kernel) (by decide +kernel)
def v1048 : List ℕ := [t356,t25,t195,t27,t116,t224]
set_option maxHeartbeats 0 in
theorem b1059 : Ban 55 5 v1048 := viaSmall (by decide +kernel) (by decide)
def v1049 : List ℕ := [t225,t356,t25,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1060 : Ban 55 5 v1049 := viaSmall (by decide +kernel) (by decide)
def v1050 : List ℕ := [t356,t25,t195,t118,t27,t116]
set_option maxHeartbeats 0 in
theorem b1061 : Ban 55 5 v1050 := viaCut p93_29 w72 (by decide) (by decide +kernel) (by decide +kernel)
def v1051 : List ℕ := [t418,t356,t25,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1062 : Ban 55 5 v1051 := viaSmall (by decide +kernel) (by decide)
def v1052 : List ℕ := [t356,t25,t195,t27,t274]
def a29_3204Slow : Projection 18 18 := pick [0,4,2,5,1,3,6,8,7,9,13,11,14,10,12,15,17,16] rfl (by decide +kernel) (by decide)
def a29_3204T : LookupTree := (.fork t281 t97 (.fork t97 t281 (.fork t215 t216 .empty .empty) (.fork t216 t215 .empty .empty)) (.fork t284 t99 (.fork t98 t98 .empty .empty) (.fork t99 t284 .empty .empty)))
set_option maxHeartbeats 0 in
def a29_3204 : Projection 18 18 := cached a29_3204Slow a29_3204T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1063 : Ban 18 4 v917 := viaPerm a29_3204 a29_3204 b313 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w73 : Wide 18 4 v917 := viaSub (ws := [v917]) (consBan b1063 (nilBan 18 4)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1064 : Ban 55 5 v1052 := viaCut p93_29 w73 (by decide) (by decide +kernel) (by decide +kernel)
def v1053 : List ℕ := [t356,t25,t195,t27,t116,t274]
set_option maxHeartbeats 0 in
theorem b1065 : Ban 55 5 v1053 := viaSmall (by decide +kernel) (by decide)
def v1054 : List ℕ := [t419,t356,t25,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1066 : Ban 55 5 v1054 := viaSmall (by decide +kernel) (by decide)
def v1055 : List ℕ := [t356,t25,t195,t27,t420]
set_option maxHeartbeats 0 in
theorem b1067 : Ban 55 5 v1055 := viaSmall (by decide +kernel) (by decide)
def v1056 : List ℕ := [t356,t25,t195,t27,t420,t116]
set_option maxHeartbeats 0 in
theorem b1068 : Ban 55 5 v1056 := viaSmall (by decide +kernel) (by decide)
def v1057 : List ℕ := [t196,t356,t25,t27,t116]
set_option maxHeartbeats 0 in
theorem b1069 : Ban 55 5 v1057 := viaSmall (by decide +kernel) (by decide)
def v1058 : List ℕ := [t196,t356,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1070 : Ban 55 5 v1058 := viaSmall (by decide +kernel) (by decide)
def v1059 : List ℕ := [t196,t356,t25,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1071 : Ban 55 5 v1059 := viaSmall (by decide +kernel) (by decide)
def v1060 : List ℕ := [t139,t356,t25,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1072 : Ban 55 5 v1060 := viaCut p93_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1061 : List ℕ := [t356,t195,t116,t140]
set_option maxHeartbeats 0 in
theorem b1073 : Ban 55 5 v1061 := viaSmall (by decide +kernel) (by decide)
def v1062 : List ℕ := [t356,t25,t195,t116,t140]
set_option maxHeartbeats 0 in
theorem b1074 : Ban 55 5 v1062 := viaSmall (by decide +kernel) (by decide)
def v1063 : List ℕ := [t356,t195,t27,t116,t140]
set_option maxHeartbeats 0 in
theorem b1075 : Ban 55 5 v1063 := viaSmall (by decide +kernel) (by decide)
def v1064 : List ℕ := [t356,t25,t195,t27,t116,t140]
set_option maxHeartbeats 0 in
theorem b1076 : Ban 55 5 v1064 := viaSmall (by decide +kernel) (by decide)
def v1065 : List ℕ := [t356,t141,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1077 : Ban 55 5 v1065 := viaSmall (by decide +kernel) (by decide)
def v1066 : List ℕ := [t356,t141,t25,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1078 : Ban 55 5 v1066 := viaCut p93_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1067 : List ℕ := [t356,t25,t195,t142,t116]
set_option maxHeartbeats 0 in
theorem b1079 : Ban 55 5 v1067 := viaSmall (by decide +kernel) (by decide)
def v1068 : List ℕ := [t356,t25,t195,t142,t27,t116]
set_option maxHeartbeats 0 in
theorem b1080 : Ban 55 5 v1068 := viaCut p93_29 w72 (by decide) (by decide +kernel) (by decide +kernel)
def v1069 : List ℕ := [t421,t356,t25,t195,t27]
set_option maxHeartbeats 0 in
theorem b1081 : Ban 55 5 v1069 := viaCut p93_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1070 : List ℕ := [t421,t356,t25,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1082 : Ban 55 5 v1070 := viaCut p93_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1071 : List ℕ := [t356,t25,t195,t27,t116,t422]
set_option maxHeartbeats 0 in
theorem b1083 : Ban 55 5 v1071 := viaSmall (by decide +kernel) (by decide)
def v1072 : List ℕ := [t356,t423,t25,t195,t27]
set_option maxHeartbeats 0 in
theorem b1084 : Ban 55 5 v1072 := viaCut p93_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1073 : List ℕ := [t356,t423,t25,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1085 : Ban 55 5 v1073 := viaCut p93_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1074 : List ℕ := [t356,t25,t195,t27,t424,t116]
set_option maxHeartbeats 0 in
theorem b1086 : Ban 55 5 v1074 := viaSmall (by decide +kernel) (by decide)
def v1075 : List ℕ := [t425,t356,t25,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1087 : Ban 55 5 v1075 := viaCut p93_29 w72 (by decide) (by decide +kernel) (by decide +kernel)
def v1076 : List ℕ := [t356,t25,t195,t27,t116,t426]
set_option maxHeartbeats 0 in
theorem b1088 : Ban 55 5 v1076 := viaSmall (by decide +kernel) (by decide)
def v1077 : List ℕ := [t356,t25,t427,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1089 : Ban 55 5 v1077 := viaSmall (by decide +kernel) (by decide)
def v1078 : List ℕ := [t356,t25,t195,t428,t27,t116]
set_option maxHeartbeats 0 in
theorem b1090 : Ban 55 5 v1078 := viaCut p93_29 w72 (by decide) (by decide +kernel) (by decide +kernel)
def v1079 : List ℕ := [t429,t356,t25,t195,t27]
set_option maxHeartbeats 0 in
theorem b1091 : Ban 55 5 v1079 := viaSmall (by decide +kernel) (by decide)
def v1080 : List ℕ := [t429,t356,t25,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1092 : Ban 55 5 v1080 := viaSmall (by decide +kernel) (by decide)
def v1081 : List ℕ := [t356,t25,t195,t27,t116,t430]
set_option maxHeartbeats 0 in
theorem b1093 : Ban 55 5 v1081 := viaSmall (by decide +kernel) (by decide)
def v1082 : List ℕ := [t356,t25,t431,t195,t27]
set_option maxHeartbeats 0 in
theorem b1094 : Ban 55 5 v1082 := viaSmall (by decide +kernel) (by decide)
def v1083 : List ℕ := [t356,t25,t431,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1095 : Ban 55 5 v1083 := viaSmall (by decide +kernel) (by decide)
def v1084 : List ℕ := [t356,t25,t195,t27,t432,t116]
set_option maxHeartbeats 0 in
theorem b1096 : Ban 55 5 v1084 := viaSmall (by decide +kernel) (by decide)
def v1085 : List ℕ := [t117,t356,t25,t195,t27]
set_option maxHeartbeats 0 in
theorem b1097 : Ban 55 5 v1085 := viaCut p93_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1086 : List ℕ := [t117,t356,t25,t195,t116]
set_option maxHeartbeats 0 in
theorem b1098 : Ban 55 5 v1086 := viaCut p93_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1087 : List ℕ := [t117,t356,t25,t195,t27,t116]
set_option maxHeartbeats 0 in
theorem b1099 : Ban 55 5 v1087 := viaCut p93_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1100 : Ban 55 6 v1036 := viaBranch (ws := [v1037,v1038,v1039,v1040,v1041,v1042,v1043,v1044,v1045,v1046,v1047,v1048,v1049,v1050,v1051,v1052,v1053,v1054,v1055,v1056,v1057,v1058,v1059,v1060,v1061,v1062,v1063,v1064,v1065,v1066,v1067,v1068,v1069,v1070,v1071,v1072,v1073,v1074,v1075,v1076,v1077,v1078,v1079,v1080,v1081,v1082,v1083,v1084,v1085,v1086,v1087]) (consBan b1047 (consBan b1048 (consBan b1049 (consBan b1050 (consBan b1051 (consBan b1052 (consBan b1053 (consBan b1054 (consBan b1055 (consBan b1056 (consBan b1058 (consBan b1059 (consBan b1060 (consBan b1061 (consBan b1062 (consBan b1064 (consBan b1065 (consBan b1066 (consBan b1067 (consBan b1068 (consBan b1069 (consBan b1070 (consBan b1071 (consBan b1072 (consBan b1073 (consBan b1074 (consBan b1075 (consBan b1076 (consBan b1077 (consBan b1078 (consBan b1079 (consBan b1080 (consBan b1081 (consBan b1082 (consBan b1083 (consBan b1084 (consBan b1085 (consBan b1086 (consBan b1087 (consBan b1088 (consBan b1089 (consBan b1090 (consBan b1091 (consBan b1092 (consBan b1093 (consBan b1094 (consBan b1095 (consBan b1096 (consBan b1097 (consBan b1098 (consBan b1099 (nilBan 55 5)))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w74 : Wide 55 6 v1036 := viaSub (ws := [v1036]) (consBan b1100 (nilBan 55 6)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1101 : Ban 228 8 v1035 := viaCut p127_93 w74 (by decide) (by decide +kernel) (by decide +kernel)
def v1088 : List ℕ := [t0,t2,t251,t3,t4,t5,t6,t241]
set_option maxHeartbeats 0 in
theorem b1102 : Ban 228 8 v1088 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1089 : List ℕ := [t0,t242,t2,t251,t3,t4,t6]
set_option maxHeartbeats 0 in
theorem b1103 : Ban 228 8 v1089 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1090 : List ℕ := [t0,t242,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1104 : Ban 228 8 v1090 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1091 : List ℕ := [t0,t2,t251,t3,t4,t243,t5]
set_option maxHeartbeats 0 in
theorem b1105 : Ban 228 8 v1091 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1092 : List ℕ := [t0,t2,t251,t3,t4,t243,t5,t6]
set_option maxHeartbeats 0 in
theorem b1106 : Ban 228 8 v1092 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1107 : Ban 228 9 v859 := viaBranch (ws := [v860,v861,v862,v863,v864,v251,v865,v866,v867,v868,v869,v584,v870,v871,v872,v873,v874,v875,v876,v877,v878,v879,v880,v767,v881,v882,v883,v884,v885,v886,v887,v888,v889,v890,v891,v892,v893,v894,v895,v896,v897,v898,v899,v900,v901,v902,v903,v904,v905,v906,v907,v908,v909,v910,v911,v982,v983,v984,v985,v986,v987,v988,v989,v990,v991,v992,v993,v994,v995,v996,v997,v998,v999,v1000,v1001,v1003,v1004,v1005,v1006,v1007,v1008,v1009,v1010,v1011,v1012,v1013,v1014,v1015,v1016,v1017,v1018,v1019,v1020,v1021,v1022,v1023,v1024,v1025,v1026,v1027,v1028,v1029,v1030,v1031,v1032,v1033,v1034,v1035,v1088,v1089,v1090,v1091,v1092]) (consBan b870 (consBan b871 (consBan b872 (consBan b873 (consBan b874 (consBan b255 (consBan b875 (consBan b876 (consBan b877 (consBan b878 (consBan b879 (consBan b592 (consBan b880 (consBan b881 (consBan b882 (consBan b883 (consBan b884 (consBan b885 (consBan b886 (consBan b887 (consBan b888 (consBan b889 (consBan b890 (consBan b776 (consBan b891 (consBan b892 (consBan b893 (consBan b894 (consBan b895 (consBan b896 (consBan b897 (consBan b898 (consBan b899 (consBan b900 (consBan b901 (consBan b902 (consBan b903 (consBan b904 (consBan b905 (consBan b906 (consBan b907 (consBan b908 (consBan b909 (consBan b910 (consBan b911 (consBan b912 (consBan b913 (consBan b914 (consBan b915 (consBan b916 (consBan b917 (consBan b918 (consBan b919 (consBan b920 (consBan b992 (consBan b993 (consBan b994 (consBan b995 (consBan b996 (consBan b997 (consBan b998 (consBan b999 (consBan b1000 (consBan b1001 (consBan b1002 (consBan b1003 (consBan b1004 (consBan b1005 (consBan b1006 (consBan b1007 (consBan b1008 (consBan b1009 (consBan b1010 (consBan b1011 (consBan b1013 (consBan b1014 (consBan b1016 (consBan b1017 (consBan b1018 (consBan b1019 (consBan b1020 (consBan b1021 (consBan b1022 (consBan b1023 (consBan b1024 (consBan b1025 (consBan b1026 (consBan b1027 (consBan b1028 (consBan b1029 (consBan b1030 (consBan b1031 (consBan b1032 (consBan b1033 (consBan b1034 (consBan b1035 (consBan b1036 (consBan b1037 (consBan b1038 (consBan b1039 (consBan b1040 (consBan b1041 (consBan b1042 (consBan b1043 (consBan b1044 (consBan b1045 (consBan b1046 (consBan b1101 (consBan b1102 (consBan b1103 (consBan b1104 (consBan b1105 (consBan b1106 (nilBan 228 8)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
def v1093 : List ℕ := [t0,t1,t2,t251,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1108 : Ban 228 9 v1093 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1109 : Ban 228 9 v891 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1094 : List ℕ := [t252,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1110 : Ban 228 9 v1094 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1095 : List ℕ := [t0,t1,t253,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1111 : Ban 228 9 v1095 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1096 : List ℕ := [t0,t1,t253,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1112 : Ban 228 9 v1096 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1097 : List ℕ := [t352,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1113 : Ban 228 9 v1097 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1098 : List ℕ := [t0,t1,t2,t3,t353,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1114 : Ban 228 9 v1098 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1099 : List ℕ := [t0,t354,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1115 : Ban 228 9 v1099 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1100 : List ℕ := [t0,t1,t2,t355,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1116 : Ban 228 9 v1100 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1101 : List ℕ := [t257,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1117 : Ban 228 9 v1101 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1102 : List ℕ := [t0,t1,t2,t3,t4,t258,t5,t6]
set_option maxHeartbeats 0 in
theorem b1118 : Ban 228 9 v1102 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1103 : List ℕ := [t0,t259,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1119 : Ban 228 9 v1103 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1104 : List ℕ := [t0,t1,t2,t3,t260,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1120 : Ban 228 9 v1104 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1105 : List ℕ := [t307,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1121 : Ban 228 9 v1105 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1106 : List ℕ := [t0,t1,t2,t3,t4,t308,t6]
set_option maxHeartbeats 0 in
theorem b1122 : Ban 228 9 v1106 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1107 : List ℕ := [t0,t2,t3,t4,t5,t308,t6]
set_option maxHeartbeats 0 in
theorem b1123 : Ban 228 9 v1107 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1108 : List ℕ := [t0,t1,t2,t3,t4,t5,t308,t6]
set_option maxHeartbeats 0 in
theorem b1124 : Ban 228 9 v1108 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1109 : List ℕ := [t0,t309,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1125 : Ban 228 9 v1109 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1110 : List ℕ := [t0,t309,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1126 : Ban 228 9 v1110 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1111 : List ℕ := [t0,t1,t2,t3,t4,t310,t6]
set_option maxHeartbeats 0 in
theorem b1127 : Ban 228 9 v1111 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1112 : List ℕ := [t0,t1,t2,t3,t4,t310,t5,t6]
set_option maxHeartbeats 0 in
theorem b1128 : Ban 228 9 v1112 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1113 : List ℕ := [t264,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1129 : Ban 228 9 v1113 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1114 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t265]
set_option maxHeartbeats 0 in
theorem b1130 : Ban 228 9 v1114 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1115 : List ℕ := [t0,t266,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1131 : Ban 228 9 v1115 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1116 : List ℕ := [t0,t1,t2,t3,t4,t5,t267,t6]
set_option maxHeartbeats 0 in
theorem b1132 : Ban 228 9 v1116 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1117 : List ℕ := [t0,t1,t91,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1133 : Ban 228 9 v1117 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1118 : List ℕ := [t0,t1,t2,t92,t4,t5,t6]
def v1119 : List ℕ := [t7,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1134 : Ban 228 8 v1119 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1120 : List ℕ := [t1,t12,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1135 : Ban 228 8 v1120 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1121 : List ℕ := [t0,t1,t12,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1136 : Ban 228 8 v1121 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1122 : List ℕ := [t244,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1137 : Ban 228 8 v1122 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1123 : List ℕ := [t244,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1138 : Ban 228 8 v1123 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1124 : List ℕ := [t0,t13,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1139 : Ban 228 8 v1124 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1125 : List ℕ := [t0,t13,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1140 : Ban 228 8 v1125 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1126 : List ℕ := [t14,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1141 : Ban 228 8 v1126 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1127 : List ℕ := [t0,t1,t2,t18,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1142 : Ban 228 8 v1127 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1128 : List ℕ := [t19,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1143 : Ban 228 8 v1128 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1129 : List ℕ := [t0,t1,t20,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1144 : Ban 228 8 v1129 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1130 : List ℕ := [t433,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1145 : Ban 228 8 v1130 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1131 : List ℕ := [t0,t1,t2,t92,t269,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1146 : Ban 228 8 v1131 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v1132 : List ℕ := [t434,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1147 : Ban 228 8 v1132 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1133 : List ℕ := [t0,t1,t2,t435,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1148 : Ban 228 8 v1133 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v1134 : List ℕ := [t0,t1,t2,t435,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1149 : Ban 228 8 v1134 := viaCut p127_98 w7 (by decide) (by decide +kernel) (by decide +kernel)
def v1135 : List ℕ := [t30,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1150 : Ban 228 8 v1135 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1136 : List ℕ := [t0,t1,t2,t92,t4,t31,t5,t6]
set_option maxHeartbeats 0 in
theorem b1151 : Ban 228 8 v1136 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1137 : List ℕ := [t37,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1152 : Ban 228 8 v1137 := viaCut p127_114 w48 (by decide) (by decide +kernel) (by decide +kernel)
def v1138 : List ℕ := [t0,t1,t2,t92,t38,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1153 : Ban 228 8 v1138 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1139 : List ℕ := [t39,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1154 : Ban 228 8 v1139 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1140 : List ℕ := [t1,t2,t92,t4,t5,t40,t6]
set_option maxHeartbeats 0 in
theorem b1155 : Ban 228 8 v1140 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1141 : List ℕ := [t0,t1,t2,t92,t4,t5,t40,t6]
set_option maxHeartbeats 0 in
theorem b1156 : Ban 228 8 v1141 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1142 : List ℕ := [t186,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1157 : Ban 228 8 v1142 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1143 : List ℕ := [t186,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1158 : Ban 228 8 v1143 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1144 : List ℕ := [t0,t1,t2,t92,t4,t187,t6]
set_option maxHeartbeats 0 in
theorem b1159 : Ban 228 8 v1144 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1145 : List ℕ := [t0,t1,t2,t92,t4,t187,t5,t6]
set_option maxHeartbeats 0 in
theorem b1160 : Ban 228 8 v1145 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1146 : List ℕ := [t188,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1161 : Ban 228 8 v1146 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1147 : List ℕ := [t0,t1,t2,t92,t4,t5,t6,t189]
set_option maxHeartbeats 0 in
theorem b1162 : Ban 228 8 v1147 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v1148 : List ℕ := [t190,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1163 : Ban 228 8 v1148 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1149 : List ℕ := [t0,t1,t2,t92,t4,t5,t191,t6]
set_option maxHeartbeats 0 in
theorem b1164 : Ban 228 8 v1149 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
def v1150 : List ℕ := [t0,t250,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1165 : Ban 228 8 v1150 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1151 : List ℕ := [t0,t1,t2,t251,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1166 : Ban 228 8 v1151 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1152 : List ℕ := [t252,t0,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1167 : Ban 228 8 v1152 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1153 : List ℕ := [t252,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1168 : Ban 228 8 v1153 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1154 : List ℕ := [t0,t1,t253,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1169 : Ban 228 8 v1154 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1155 : List ℕ := [t0,t436,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1170 : Ban 228 8 v1155 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1156 : List ℕ := [t0,t1,t2,t92,t397,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1171 : Ban 228 8 v1156 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1157 : List ℕ := [t437,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1172 : Ban 228 8 v1157 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1158 : List ℕ := [t0,t1,t2,t438,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1173 : Ban 228 8 v1158 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1159 : List ℕ := [t257,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1174 : Ban 228 8 v1159 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1160 : List ℕ := [t0,t1,t2,t92,t4,t258,t5,t6]
set_option maxHeartbeats 0 in
theorem b1175 : Ban 228 8 v1160 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1161 : List ℕ := [t0,t259,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1176 : Ban 228 8 v1161 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1162 : List ℕ := [t0,t1,t2,t92,t260,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1177 : Ban 228 8 v1162 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1163 : List ℕ := [t307,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1178 : Ban 228 8 v1163 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1164 : List ℕ := [t0,t1,t2,t92,t4,t308,t6]
set_option maxHeartbeats 0 in
theorem b1179 : Ban 228 8 v1164 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1165 : List ℕ := [t0,t2,t92,t4,t5,t308,t6]
set_option maxHeartbeats 0 in
theorem b1180 : Ban 228 8 v1165 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1166 : List ℕ := [t0,t1,t2,t92,t4,t5,t308,t6]
set_option maxHeartbeats 0 in
theorem b1181 : Ban 228 8 v1166 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1167 : List ℕ := [t0,t309,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1182 : Ban 228 8 v1167 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1168 : List ℕ := [t0,t309,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1183 : Ban 228 8 v1168 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1169 : List ℕ := [t0,t1,t2,t92,t4,t310,t6]
set_option maxHeartbeats 0 in
theorem b1184 : Ban 228 8 v1169 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1170 : List ℕ := [t0,t1,t2,t92,t4,t310,t5,t6]
set_option maxHeartbeats 0 in
theorem b1185 : Ban 228 8 v1170 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1171 : List ℕ := [t264,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1186 : Ban 228 8 v1171 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1172 : List ℕ := [t0,t1,t2,t92,t4,t5,t6,t265]
set_option maxHeartbeats 0 in
theorem b1187 : Ban 228 8 v1172 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1173 : List ℕ := [t0,t266,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1188 : Ban 228 8 v1173 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1174 : List ℕ := [t0,t1,t2,t92,t4,t5,t267,t6]
set_option maxHeartbeats 0 in
theorem b1189 : Ban 228 8 v1174 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1175 : List ℕ := [t0,t1,t2,t148,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1190 : Ban 228 8 v1175 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1176 : List ℕ := [t0,t1,t148,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1191 : Ban 228 8 v1176 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1177 : List ℕ := [t0,t1,t2,t148,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1192 : Ban 228 8 v1177 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1178 : List ℕ := [t149,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1193 : Ban 228 8 v1178 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1179 : List ℕ := [t0,t1,t2,t92,t4,t150,t5,t6]
set_option maxHeartbeats 0 in
theorem b1194 : Ban 228 8 v1179 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1180 : List ℕ := [t0,t1,t151,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1195 : Ban 228 8 v1180 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1181 : List ℕ := [t0,t1,t2,t92,t152,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1196 : Ban 228 8 v1181 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1182 : List ℕ := [t228,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1197 : Ban 228 8 v1182 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1183 : List ℕ := [t0,t1,t2,t92,t4,t5,t229,t6]
set_option maxHeartbeats 0 in
theorem b1198 : Ban 228 8 v1183 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1184 : List ℕ := [t0,t1,t230,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1199 : Ban 228 8 v1184 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1185 : List ℕ := [t0,t1,t2,t92,t4,t231,t5,t6]
set_option maxHeartbeats 0 in
theorem b1200 : Ban 228 8 v1185 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1186 : List ℕ := [t157,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1201 : Ban 228 8 v1186 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1187 : List ℕ := [t0,t1,t92,t4,t5,t6,t158]
def v1188 : List ℕ := [t23,t24,t25,t94,t27]
set_option maxHeartbeats 0 in
theorem b1202 : Ban 55 6 v1188 := viaPerm a59_04315 a59_04315 b547 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w75 : Wide 55 6 v1188 := viaSub (ws := [v1188]) (consBan b1202 (nilBan 55 6)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1203 : Ban 228 8 v1187 := viaCut p127_59 w75 (by decide) (by decide +kernel) (by decide +kernel)
def v1189 : List ℕ := [t0,t1,t2,t92,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1204 : Ban 228 8 v1189 := viaCut p127_59 w75 (by decide) (by decide +kernel) (by decide +kernel)
def v1190 : List ℕ := [t0,t1,t159,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1205 : Ban 228 8 v1190 := viaCut p127_59 w75 (by decide) (by decide +kernel) (by decide +kernel)
def v1191 : List ℕ := [t0,t1,t159,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1206 : Ban 228 8 v1191 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1192 : List ℕ := [t0,t1,t2,t92,t4,t5,t160,t6]
set_option maxHeartbeats 0 in
theorem b1207 : Ban 228 8 v1192 := viaCut p127_114 w71 (by decide) (by decide +kernel) (by decide +kernel)
def v1193 : List ℕ := [t0,t1,t2,t439,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1208 : Ban 228 8 v1193 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1194 : List ℕ := [t0,t1,t2,t4,t440,t5,t6]
def v1195 : List ℕ := [t23,t24,t25,t27,t144]
set_option maxHeartbeats 0 in
theorem b1209 : Ban 55 6 v1195 := viaPerm a59_04315 a59_04315 b545 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w76 : Wide 55 6 v1195 := viaSub (ws := [v1195]) (consBan b1209 (nilBan 55 6)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1210 : Ban 228 8 v1194 := viaCut p127_59 w76 (by decide) (by decide +kernel) (by decide +kernel)
def v1196 : List ℕ := [t0,t1,t2,t92,t4,t440,t5,t6]
def v1197 : List ℕ := [t23,t24,t25,t94,t27,t144]
set_option maxHeartbeats 0 in
theorem b1211 : Ban 55 6 v1197 := viaPerm a59_04315 a59_04315 b548 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w77 : Wide 55 6 v1197 := viaSub (ws := [v1188,v1195,v1197]) (consBan b1202 (consBan b1209 (consBan b1211 (nilBan 55 6)))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1212 : Ban 228 8 v1196 := viaCut p127_59 w77 (by decide) (by decide +kernel) (by decide +kernel)
def v1198 : List ℕ := [t0,t1,t2,t441,t4,t5,t6]
def a114_1564Slow : Projection 30 30 := pick [5,6,8,9,7,15,16,18,19,17,25,26,28,29,27,0,1,3,4,2,10,11,13,14,12,20,21,23,24,22] rfl (by decide +kernel) (by decide)
def a114_1564T : LookupTree := (.fork t9 t11 (.fork t59 t64 (.fork t8 t8 .empty .empty) .empty) (.fork t11 t10 (.fork t10 t9 .empty .empty) .empty))
set_option maxHeartbeats 0 in
def a114_1564 : Projection 30 30 := cached a114_1564Slow a114_1564T (by decide +kernel)
def a114_1645Slow : Projection 30 30 := pick [15,16,19,17,18,0,1,4,2,3,20,21,24,22,23,5,6,9,7,8,25,26,29,27,28,10,11,14,12,13] rfl (by decide +kernel) (by decide)
def a114_1645T : LookupTree := (.fork t10 t11 (.fork t9 t10 (.fork t8 t8 .empty .empty) .empty) (.fork t11 t9 (.fork t64 t59 .empty .empty) .empty))
set_option maxHeartbeats 0 in
def a114_1645 : Projection 30 30 := cached a114_1645Slow a114_1645T (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1213 : Ban 30 6 v48 := viaPerm a114_1564 a114_1645 b1015 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem w78 : Wide 30 6 v48 := viaSub (ws := [v2,v48]) (consBan b57 (consBan b1213 (nilBan 30 6))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1214 : Ban 228 8 v1198 := viaCut p127_114 w78 (by decide) (by decide +kernel) (by decide +kernel)
def v1199 : List ℕ := [t0,t1,t2,t441,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1215 : Ban 228 8 v1199 := viaCut p127_114 w78 (by decide) (by decide +kernel) (by decide +kernel)
def v1200 : List ℕ := [t0,t1,t2,t442,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1216 : Ban 228 8 v1200 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1201 : List ℕ := [t0,t443,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1217 : Ban 228 8 v1201 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1202 : List ℕ := [t0,t1,t2,t4,t5,t444,t6]
set_option maxHeartbeats 0 in
theorem b1218 : Ban 228 8 v1202 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1203 : List ℕ := [t0,t1,t2,t92,t4,t5,t444,t6]
set_option maxHeartbeats 0 in
theorem b1219 : Ban 228 8 v1203 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1204 : List ℕ := [t0,t1,t2,t445,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1220 : Ban 228 8 v1204 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1205 : List ℕ := [t0,t1,t2,t445,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1221 : Ban 228 8 v1205 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1206 : List ℕ := [t0,t1,t2,t92,t4,t446,t5,t6]
set_option maxHeartbeats 0 in
theorem b1222 : Ban 228 8 v1206 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1207 : List ℕ := [t447,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1223 : Ban 228 8 v1207 := viaCut p127_98 w7 (by decide) (by decide +kernel) (by decide +kernel)
def v1208 : List ℕ := [t0,t1,t2,t92,t4,t5,t6,t448]
set_option maxHeartbeats 0 in
theorem b1224 : Ban 228 8 v1208 := viaCut p127_59 w75 (by decide) (by decide +kernel) (by decide +kernel)
def v1209 : List ℕ := [t0,t1,t2,t449,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1225 : Ban 228 8 v1209 := viaCut p127_98 w7 (by decide) (by decide +kernel) (by decide +kernel)
def v1210 : List ℕ := [t0,t1,t2,t92,t4,t5,t450,t6]
set_option maxHeartbeats 0 in
theorem b1226 : Ban 228 8 v1210 := viaCut p127_114 w71 (by decide) (by decide +kernel) (by decide +kernel)
def v1211 : List ℕ := [t236,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1227 : Ban 228 8 v1211 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1212 : List ℕ := [t0,t1,t2,t92,t4,t5,t237,t6]
set_option maxHeartbeats 0 in
theorem b1228 : Ban 228 8 v1212 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1213 : List ℕ := [t0,t1,t2,t92,t238,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1229 : Ban 228 8 v1213 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1214 : List ℕ := [t0,t1,t2,t92,t4,t239,t5,t6]
set_option maxHeartbeats 0 in
theorem b1230 : Ban 228 8 v1214 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1215 : List ℕ := [t178,t0,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1231 : Ban 228 8 v1215 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1216 : List ℕ := [t0,t1,t2,t92,t4,t5,t6,t179]
set_option maxHeartbeats 0 in
theorem b1232 : Ban 228 8 v1216 := viaCut p127_59 w75 (by decide) (by decide +kernel) (by decide +kernel)
def v1217 : List ℕ := [t0,t1,t2,t92,t180,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1233 : Ban 228 8 v1217 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1218 : List ℕ := [t0,t1,t2,t92,t4,t5,t181,t6]
set_option maxHeartbeats 0 in
theorem b1234 : Ban 228 8 v1218 := viaCut p127_59 w75 (by decide) (by decide +kernel) (by decide +kernel)
def v1219 : List ℕ := [t0,t1,t2,t92,t4,t240,t5,t6]
set_option maxHeartbeats 0 in
theorem b1235 : Ban 228 8 v1219 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1220 : List ℕ := [t0,t1,t2,t92,t4,t5,t241]
set_option maxHeartbeats 0 in
theorem b1236 : Ban 228 8 v1220 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1221 : List ℕ := [t0,t1,t2,t92,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1237 : Ban 228 8 v1221 := viaCut p127_59 w75 (by decide) (by decide +kernel) (by decide +kernel)
def v1222 : List ℕ := [t0,t1,t2,t92,t4,t5,t6,t241]
set_option maxHeartbeats 0 in
theorem b1238 : Ban 228 8 v1222 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1223 : List ℕ := [t0,t242,t1,t2,t92,t4,t6]
set_option maxHeartbeats 0 in
theorem b1239 : Ban 228 8 v1223 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1224 : List ℕ := [t0,t242,t1,t2,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1240 : Ban 228 8 v1224 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1225 : List ℕ := [t0,t1,t2,t92,t4,t243,t5]
set_option maxHeartbeats 0 in
theorem b1241 : Ban 228 8 v1225 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1226 : List ℕ := [t0,t1,t2,t92,t4,t243,t5,t6]
set_option maxHeartbeats 0 in
theorem b1242 : Ban 228 8 v1226 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1243 : Ban 228 9 v1118 := viaBranch (ws := [v1119,v344,v1120,v1121,v1122,v1123,v1124,v1125,v1126,v1127,v1128,v1129,v1130,v611,v1131,v1132,v1133,v1134,v1135,v1136,v1137,v1138,v1139,v795,v1140,v1141,v1142,v1143,v1144,v1145,v1146,v1147,v1148,v1149,v1150,v895,v1151,v1152,v1153,v1154,v1155,v1156,v1157,v1158,v1159,v1160,v1161,v1162,v1163,v1164,v1165,v1166,v1167,v1168,v1169,v1170,v1171,v1172,v1173,v1174,v1175,v1176,v1177,v1178,v1179,v1180,v1181,v1182,v1183,v1184,v1185,v1186,v1187,v1189,v1190,v1191,v1192,v1193,v1194,v1196,v1198,v1199,v1200,v1201,v1202,v1203,v1204,v1205,v1206,v1207,v1208,v1209,v1210,v1211,v1212,v1213,v1214,v1215,v1216,v1217,v1218,v1219,v1220,v1221,v1222,v1223,v1224,v1225,v1226]) (consBan b1134 (consBan b349 (consBan b1135 (consBan b1136 (consBan b1137 (consBan b1138 (consBan b1139 (consBan b1140 (consBan b1141 (consBan b1142 (consBan b1143 (consBan b1144 (consBan b1145 (consBan b619 (consBan b1146 (consBan b1147 (consBan b1148 (consBan b1149 (consBan b1150 (consBan b1151 (consBan b1152 (consBan b1153 (consBan b1154 (consBan b804 (consBan b1155 (consBan b1156 (consBan b1157 (consBan b1158 (consBan b1159 (consBan b1160 (consBan b1161 (consBan b1162 (consBan b1163 (consBan b1164 (consBan b1165 (consBan b905 (consBan b1166 (consBan b1167 (consBan b1168 (consBan b1169 (consBan b1170 (consBan b1171 (consBan b1172 (consBan b1173 (consBan b1174 (consBan b1175 (consBan b1176 (consBan b1177 (consBan b1178 (consBan b1179 (consBan b1180 (consBan b1181 (consBan b1182 (consBan b1183 (consBan b1184 (consBan b1185 (consBan b1186 (consBan b1187 (consBan b1188 (consBan b1189 (consBan b1190 (consBan b1191 (consBan b1192 (consBan b1193 (consBan b1194 (consBan b1195 (consBan b1196 (consBan b1197 (consBan b1198 (consBan b1199 (consBan b1200 (consBan b1201 (consBan b1203 (consBan b1204 (consBan b1205 (consBan b1206 (consBan b1207 (consBan b1208 (consBan b1210 (consBan b1212 (consBan b1214 (consBan b1215 (consBan b1216 (consBan b1217 (consBan b1218 (consBan b1219 (consBan b1220 (consBan b1221 (consBan b1222 (consBan b1223 (consBan b1224 (consBan b1225 (consBan b1226 (consBan b1227 (consBan b1228 (consBan b1229 (consBan b1230 (consBan b1231 (consBan b1232 (consBan b1233 (consBan b1234 (consBan b1235 (consBan b1236 (consBan b1237 (consBan b1238 (consBan b1239 (consBan b1240 (consBan b1241 (consBan b1242 (nilBan 228 8)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
def v1227 : List ℕ := [t0,t1,t3,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1244 : Ban 228 9 v1227 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1228 : List ℕ := [t0,t1,t2,t3,t92,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1245 : Ban 228 9 v1228 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1229 : List ℕ := [t0,t1,t147,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1246 : Ban 228 9 v1229 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1230 : List ℕ := [t0,t1,t147,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1247 : Ban 228 9 v1230 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1248 : Ban 228 9 v1175 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1231 : List ℕ := [t0,t1,t2,t148,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1249 : Ban 228 9 v1231 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1232 : List ℕ := [t149,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1250 : Ban 228 9 v1232 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v1233 : List ℕ := [t0,t1,t2,t3,t4,t150,t5,t6]
set_option maxHeartbeats 0 in
theorem b1251 : Ban 228 9 v1233 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v1234 : List ℕ := [t0,t1,t151,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1252 : Ban 228 9 v1234 := viaCut p127_114 w78 (by decide) (by decide +kernel) (by decide +kernel)
def v1235 : List ℕ := [t0,t1,t2,t3,t152,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1253 : Ban 228 9 v1235 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v1236 : List ℕ := [t228,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1254 : Ban 228 9 v1236 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1237 : List ℕ := [t0,t1,t2,t3,t4,t5,t229,t6]
set_option maxHeartbeats 0 in
theorem b1255 : Ban 228 9 v1237 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1238 : List ℕ := [t0,t1,t230,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1256 : Ban 228 9 v1238 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1239 : List ℕ := [t0,t1,t2,t3,t4,t231,t5,t6]
set_option maxHeartbeats 0 in
theorem b1257 : Ban 228 9 v1239 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1240 : List ℕ := [t157,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1258 : Ban 228 9 v1240 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1241 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t158]
def v1242 : List ℕ := [t7,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1259 : Ban 228 8 v1242 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1243 : List ℕ := [t1,t12,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem w79 : Wide 30 5 v51 := viaSub (ws := [v2,v51]) (consBan b0 (consBan b50 (nilBan 30 5))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1260 : Ban 228 8 v1243 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1244 : List ℕ := [t0,t1,t12,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1261 : Ban 228 8 v1244 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1245 : List ℕ := [t244,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1262 : Ban 228 8 v1245 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1246 : List ℕ := [t244,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1263 : Ban 228 8 v1246 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1247 : List ℕ := [t0,t13,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1264 : Ban 228 8 v1247 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1248 : List ℕ := [t0,t13,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1265 : Ban 228 8 v1248 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1249 : List ℕ := [t14,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1266 : Ban 228 8 v1249 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1250 : List ℕ := [t0,t1,t18,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1267 : Ban 228 8 v1250 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1251 : List ℕ := [t0,t1,t2,t18,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1268 : Ban 228 8 v1251 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1252 : List ℕ := [t19,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1269 : Ban 228 8 v1252 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1253 : List ℕ := [t0,t1,t20,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1270 : Ban 228 8 v1253 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1254 : List ℕ := [t0,t1,t20,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1271 : Ban 228 8 v1254 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1255 : List ℕ := [t21,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1272 : Ban 228 8 v1255 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1256 : List ℕ := [t1,t2,t3,t22,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1273 : Ban 228 8 v1256 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1257 : List ℕ := [t0,t1,t2,t3,t22,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1274 : Ban 228 8 v1257 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1258 : List ℕ := [t28,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1275 : Ban 228 8 v1258 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1259 : List ℕ := [t28,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1276 : Ban 228 8 v1259 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1260 : List ℕ := [t0,t1,t2,t29,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1277 : Ban 228 8 v1260 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1261 : List ℕ := [t0,t1,t2,t29,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1278 : Ban 228 8 v1261 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1262 : List ℕ := [t30,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1279 : Ban 228 8 v1262 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1263 : List ℕ := [t0,t1,t2,t3,t4,t31,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1280 : Ban 228 8 v1263 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1264 : List ℕ := [t37,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1281 : Ban 228 8 v1264 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1265 : List ℕ := [t0,t1,t2,t3,t38,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1282 : Ban 228 8 v1265 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1266 : List ℕ := [t39,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1283 : Ban 228 8 v1266 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1267 : List ℕ := [t1,t2,t3,t4,t5,t40,t6,t158]
set_option maxHeartbeats 0 in
theorem b1284 : Ban 228 8 v1267 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1268 : List ℕ := [t0,t1,t2,t3,t4,t5,t40,t6,t158]
set_option maxHeartbeats 0 in
theorem b1285 : Ban 228 8 v1268 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1269 : List ℕ := [t186,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1286 : Ban 228 8 v1269 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1270 : List ℕ := [t186,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1287 : Ban 228 8 v1270 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1271 : List ℕ := [t0,t1,t2,t3,t4,t187,t6,t158]
set_option maxHeartbeats 0 in
theorem b1288 : Ban 228 8 v1271 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1272 : List ℕ := [t0,t1,t2,t3,t4,t187,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1289 : Ban 228 8 v1272 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1273 : List ℕ := [t188,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1290 : Ban 228 8 v1273 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1274 : List ℕ := [t0,t1,t2,t3,t4,t5,t189,t158]
set_option maxHeartbeats 0 in
theorem b1291 : Ban 228 8 v1274 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1275 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t189,t158]
set_option maxHeartbeats 0 in
theorem b1292 : Ban 228 8 v1275 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1276 : List ℕ := [t190,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1293 : Ban 228 8 v1276 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1277 : List ℕ := [t0,t1,t2,t3,t4,t5,t191,t158]
set_option maxHeartbeats 0 in
theorem b1294 : Ban 228 8 v1277 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1278 : List ℕ := [t0,t1,t2,t3,t4,t5,t191,t6,t158]
set_option maxHeartbeats 0 in
theorem b1295 : Ban 228 8 v1278 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1279 : List ℕ := [t451,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1296 : Ban 228 8 v1279 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1280 : List ℕ := [t451,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1297 : Ban 228 8 v1280 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1281 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t452]
set_option maxHeartbeats 0 in
theorem b1298 : Ban 228 8 v1281 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1282 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t158,t452]
set_option maxHeartbeats 0 in
theorem b1299 : Ban 228 8 v1282 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1283 : List ℕ := [t453,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1300 : Ban 228 8 v1283 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1284 : List ℕ := [t453,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1301 : Ban 228 8 v1284 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1285 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t454]
set_option maxHeartbeats 0 in
theorem b1302 : Ban 228 8 v1285 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1286 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t454,t158]
set_option maxHeartbeats 0 in
theorem b1303 : Ban 228 8 v1286 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1287 : List ℕ := [t0,t250,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1304 : Ban 228 8 v1287 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1288 : List ℕ := [t0,t1,t251,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1305 : Ban 228 8 v1288 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1289 : List ℕ := [t0,t1,t2,t251,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1306 : Ban 228 8 v1289 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1290 : List ℕ := [t252,t0,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1307 : Ban 228 8 v1290 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1291 : List ℕ := [t252,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1308 : Ban 228 8 v1291 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1292 : List ℕ := [t0,t1,t253,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1309 : Ban 228 8 v1292 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1293 : List ℕ := [t0,t1,t253,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1310 : Ban 228 8 v1293 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1294 : List ℕ := [t352,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1311 : Ban 228 8 v1294 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1295 : List ℕ := [t0,t1,t2,t3,t353,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1312 : Ban 228 8 v1295 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1296 : List ℕ := [t0,t354,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1313 : Ban 228 8 v1296 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1297 : List ℕ := [t0,t1,t2,t355,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1314 : Ban 228 8 v1297 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1298 : List ℕ := [t257,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1315 : Ban 228 8 v1298 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1299 : List ℕ := [t0,t1,t2,t3,t4,t258,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1316 : Ban 228 8 v1299 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1300 : List ℕ := [t0,t259,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1317 : Ban 228 8 v1300 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1301 : List ℕ := [t0,t1,t2,t3,t260,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1318 : Ban 228 8 v1301 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1302 : List ℕ := [t307,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1319 : Ban 228 8 v1302 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1303 : List ℕ := [t0,t1,t2,t3,t4,t308,t6,t158]
set_option maxHeartbeats 0 in
theorem b1320 : Ban 228 8 v1303 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1304 : List ℕ := [t0,t2,t3,t4,t5,t308,t6,t158]
set_option maxHeartbeats 0 in
theorem b1321 : Ban 228 8 v1304 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1305 : List ℕ := [t0,t1,t2,t3,t4,t5,t308,t6,t158]
set_option maxHeartbeats 0 in
theorem b1322 : Ban 228 8 v1305 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1306 : List ℕ := [t0,t309,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1323 : Ban 228 8 v1306 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1307 : List ℕ := [t0,t309,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1324 : Ban 228 8 v1307 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1308 : List ℕ := [t0,t1,t2,t3,t4,t310,t6,t158]
set_option maxHeartbeats 0 in
theorem b1325 : Ban 228 8 v1308 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1309 : List ℕ := [t0,t1,t2,t3,t4,t310,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1326 : Ban 228 8 v1309 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1310 : List ℕ := [t264,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1327 : Ban 228 8 v1310 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1311 : List ℕ := [t0,t1,t2,t3,t4,t5,t265,t158]
set_option maxHeartbeats 0 in
theorem b1328 : Ban 228 8 v1311 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1312 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t265,t158]
set_option maxHeartbeats 0 in
theorem b1329 : Ban 228 8 v1312 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1313 : List ℕ := [t0,t266,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1330 : Ban 228 8 v1313 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1314 : List ℕ := [t0,t1,t2,t3,t4,t5,t267,t158]
set_option maxHeartbeats 0 in
theorem b1331 : Ban 228 8 v1314 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1315 : List ℕ := [t0,t1,t2,t3,t4,t5,t267,t6,t158]
set_option maxHeartbeats 0 in
theorem b1332 : Ban 228 8 v1315 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1316 : List ℕ := [t0,t455,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1333 : Ban 228 8 v1316 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1317 : List ℕ := [t0,t455,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1334 : Ban 228 8 v1317 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1318 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t409]
set_option maxHeartbeats 0 in
theorem b1335 : Ban 228 8 v1318 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1319 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t158,t409]
set_option maxHeartbeats 0 in
theorem b1336 : Ban 228 8 v1319 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1320 : List ℕ := [t456,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1337 : Ban 228 8 v1320 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1321 : List ℕ := [t456,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1338 : Ban 228 8 v1321 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1322 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t457]
set_option maxHeartbeats 0 in
theorem b1339 : Ban 228 8 v1322 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1323 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t457,t158]
set_option maxHeartbeats 0 in
theorem b1340 : Ban 228 8 v1323 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1324 : List ℕ := [t0,t1,t91,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1341 : Ban 228 8 v1324 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1325 : List ℕ := [t0,t1,t3,t92,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1342 : Ban 228 8 v1325 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1326 : List ℕ := [t0,t1,t2,t3,t92,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1343 : Ban 228 8 v1326 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1327 : List ℕ := [t0,t1,t147,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1344 : Ban 228 8 v1327 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1328 : List ℕ := [t0,t1,t147,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1345 : Ban 228 8 v1328 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1329 : List ℕ := [t0,t1,t2,t148,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1346 : Ban 228 8 v1329 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1330 : List ℕ := [t0,t1,t2,t148,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1347 : Ban 228 8 v1330 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1331 : List ℕ := [t149,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1348 : Ban 228 8 v1331 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1332 : List ℕ := [t0,t1,t3,t4,t150,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1349 : Ban 60 6 v670 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w80 : Wide 60 6 v723 := viaSub (ws := [v670,v723]) (consBan b1349 (consBan b731 (nilBan 60 6))) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1350 : Ban 228 8 v1332 := viaCut p127_91 w80 (by decide) (by decide +kernel) (by decide +kernel)
def v1333 : List ℕ := [t0,t1,t2,t3,t4,t150,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1351 : Ban 228 8 v1333 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1334 : List ℕ := [t0,t1,t151,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1352 : Ban 228 8 v1334 := viaCut p127_91 w80 (by decide) (by decide +kernel) (by decide +kernel)
def v1335 : List ℕ := [t0,t1,t151,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1353 : Ban 228 8 v1335 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1336 : List ℕ := [t0,t1,t2,t3,t152,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1354 : Ban 228 8 v1336 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1337 : List ℕ := [t228,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1355 : Ban 228 8 v1337 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1338 : List ℕ := [t0,t1,t3,t4,t5,t229,t6,t158]
set_option maxHeartbeats 0 in
theorem b1356 : Ban 228 8 v1338 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1339 : List ℕ := [t0,t1,t2,t3,t4,t5,t229,t6,t158]
set_option maxHeartbeats 0 in
theorem b1357 : Ban 228 8 v1339 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1340 : List ℕ := [t0,t1,t230,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1358 : Ban 228 8 v1340 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1341 : List ℕ := [t0,t1,t230,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1359 : Ban 228 8 v1341 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1342 : List ℕ := [t0,t1,t2,t3,t4,t231,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1360 : Ban 228 8 v1342 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1343 : List ℕ := [t157,t0,t1,t2,t3,t4,t5,t158]
set_option maxHeartbeats 0 in
theorem b1361 : Ban 228 8 v1343 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1344 : List ℕ := [t157,t0,t1,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1362 : Ban 228 8 v1344 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1345 : List ℕ := [t157,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1363 : Ban 228 8 v1345 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1346 : List ℕ := [t0,t1,t159,t2,t3,t4,t5,t158]
set_option maxHeartbeats 0 in
theorem b1364 : Ban 228 8 v1346 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1347 : List ℕ := [t0,t1,t159,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1365 : Ban 228 8 v1347 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1348 : List ℕ := [t0,t1,t3,t4,t5,t160,t6,t158]
set_option maxHeartbeats 0 in
theorem b1366 : Ban 228 8 v1348 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1349 : List ℕ := [t0,t1,t2,t3,t4,t5,t160,t6,t158]
set_option maxHeartbeats 0 in
theorem b1367 : Ban 228 8 v1349 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1350 : List ℕ := [t0,t1,t2,t3,t4,t5,t160,t6]
set_option maxHeartbeats 0 in
theorem b1368 : Ban 228 8 v1350 := viaCut p127_114 w71 (by decide) (by decide +kernel) (by decide +kernel)
def v1351 : List ℕ := [t0,t1,t2,t161,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1369 : Ban 228 8 v1351 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1352 : List ℕ := [t0,t1,t2,t3,t162,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1370 : Ban 228 8 v1352 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1353 : List ℕ := [t0,t1,t2,t4,t162,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1371 : Ban 228 8 v1353 := viaCut p127_91 w80 (by decide) (by decide +kernel) (by decide +kernel)
def v1354 : List ℕ := [t0,t1,t2,t3,t4,t162,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1372 : Ban 228 8 v1354 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1355 : List ℕ := [t0,t1,t163,t2,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1373 : Ban 228 8 v1355 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1356 : List ℕ := [t0,t1,t163,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1374 : Ban 228 8 v1356 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1357 : List ℕ := [t0,t1,t2,t164,t3,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1375 : Ban 228 8 v1357 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1358 : List ℕ := [t0,t1,t2,t164,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1376 : Ban 228 8 v1358 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1359 : List ℕ := [t0,t232,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1377 : Ban 228 8 v1359 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1360 : List ℕ := [t0,t1,t2,t3,t4,t233,t6,t158]
set_option maxHeartbeats 0 in
theorem b1378 : Ban 228 8 v1360 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1361 : List ℕ := [t0,t1,t2,t4,t5,t233,t6,t158]
set_option maxHeartbeats 0 in
theorem b1379 : Ban 228 8 v1361 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1362 : List ℕ := [t0,t1,t2,t3,t4,t5,t233,t6,t158]
set_option maxHeartbeats 0 in
theorem b1380 : Ban 228 8 v1362 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1363 : List ℕ := [t0,t1,t2,t234,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1381 : Ban 228 8 v1363 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1364 : List ℕ := [t0,t1,t2,t234,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1382 : Ban 228 8 v1364 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1365 : List ℕ := [t0,t1,t2,t3,t4,t235,t6,t158]
set_option maxHeartbeats 0 in
theorem b1383 : Ban 228 8 v1365 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1366 : List ℕ := [t0,t1,t2,t3,t4,t235,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1384 : Ban 228 8 v1366 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1367 : List ℕ := [t170,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1385 : Ban 228 8 v1367 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1368 : List ℕ := [t0,t1,t2,t3,t4,t5,t158,t171]
set_option maxHeartbeats 0 in
theorem b1386 : Ban 228 8 v1368 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1369 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t158,t171]
set_option maxHeartbeats 0 in
theorem b1387 : Ban 228 8 v1369 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1370 : List ℕ := [t0,t1,t2,t172,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1388 : Ban 228 8 v1370 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1371 : List ℕ := [t0,t1,t2,t3,t4,t5,t173,t158]
set_option maxHeartbeats 0 in
theorem b1389 : Ban 228 8 v1371 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1372 : List ℕ := [t0,t1,t2,t3,t4,t5,t173,t6,t158]
set_option maxHeartbeats 0 in
theorem b1390 : Ban 228 8 v1372 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1373 : List ℕ := [t0,t1,t458,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1391 : Ban 228 8 v1373 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1374 : List ℕ := [t0,t1,t458,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1392 : Ban 228 8 v1374 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1375 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t448]
set_option maxHeartbeats 0 in
theorem b1393 : Ban 228 8 v1375 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1376 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t158,t448]
set_option maxHeartbeats 0 in
theorem b1394 : Ban 228 8 v1376 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1377 : List ℕ := [t0,t1,t2,t459,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1395 : Ban 228 8 v1377 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1378 : List ℕ := [t0,t1,t2,t459,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1396 : Ban 228 8 v1378 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1379 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t460]
set_option maxHeartbeats 0 in
theorem b1397 : Ban 228 8 v1379 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1380 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t460,t158]
set_option maxHeartbeats 0 in
theorem b1398 : Ban 228 8 v1380 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1381 : List ℕ := [t236,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1399 : Ban 228 8 v1381 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1382 : List ℕ := [t0,t1,t2,t3,t4,t5,t237,t6,t158]
set_option maxHeartbeats 0 in
theorem b1400 : Ban 228 8 v1382 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1383 : List ℕ := [t0,t1,t2,t3,t238,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1401 : Ban 228 8 v1383 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1384 : List ℕ := [t0,t1,t2,t3,t4,t239,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1402 : Ban 228 8 v1384 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1385 : List ℕ := [t178,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1403 : Ban 228 8 v1385 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1386 : List ℕ := [t0,t1,t2,t3,t4,t5,t158,t179]
set_option maxHeartbeats 0 in
theorem b1404 : Ban 228 8 v1386 := viaCut p127_91 w80 (by decide) (by decide +kernel) (by decide +kernel)
def v1387 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t158,t179]
set_option maxHeartbeats 0 in
theorem b1405 : Ban 228 8 v1387 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1388 : List ℕ := [t0,t1,t2,t3,t180,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1406 : Ban 228 8 v1388 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1389 : List ℕ := [t0,t1,t2,t3,t4,t5,t181,t158]
set_option maxHeartbeats 0 in
theorem b1407 : Ban 228 8 v1389 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1390 : List ℕ := [t0,t1,t2,t3,t4,t5,t181,t6,t158]
set_option maxHeartbeats 0 in
theorem b1408 : Ban 228 8 v1390 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1391 : List ℕ := [t461,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1409 : Ban 228 8 v1391 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1392 : List ℕ := [t461,t0,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1410 : Ban 228 8 v1392 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1393 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t462]
set_option maxHeartbeats 0 in
theorem b1411 : Ban 228 8 v1393 := viaCut p127_91 w80 (by decide) (by decide +kernel) (by decide +kernel)
def v1394 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t158,t462]
set_option maxHeartbeats 0 in
theorem b1412 : Ban 228 8 v1394 := viaCut p127_91 w80 (by decide) (by decide +kernel) (by decide +kernel)
def v1395 : List ℕ := [t0,t1,t2,t3,t463,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1413 : Ban 228 8 v1395 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1396 : List ℕ := [t0,t1,t2,t3,t463,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1414 : Ban 228 8 v1396 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
def v1397 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t464]
set_option maxHeartbeats 0 in
theorem b1415 : Ban 228 8 v1397 := viaCut p127_91 w80 (by decide) (by decide +kernel) (by decide +kernel)
def v1398 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t464,t158]
set_option maxHeartbeats 0 in
theorem b1416 : Ban 228 8 v1398 := viaCut p127_91 w80 (by decide) (by decide +kernel) (by decide +kernel)
def v1399 : List ℕ := [t0,t1,t2,t3,t4,t240,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1417 : Ban 228 8 v1399 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1400 : List ℕ := [t0,t1,t2,t3,t4,t241,t158]
def v1401 : List ℕ := [t245,t246,t247,t249,t465]
set_option maxHeartbeats 0 in
theorem b1418 : Ban 60 6 v1401 := viaSmall (by decide +kernel) (by decide)
set_option maxHeartbeats 0 in
theorem w81 : Wide 60 6 v1401 := viaSub (ws := [v1401]) (consBan b1418 (nilBan 60 6)) (by decide) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1419 : Ban 228 8 v1400 := viaCut p127_109 w81 (by decide) (by decide +kernel) (by decide +kernel)
def v1402 : List ℕ := [t0,t1,t2,t3,t4,t5,t241,t158]
set_option maxHeartbeats 0 in
theorem b1420 : Ban 228 8 v1402 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1403 : List ℕ := [t0,t1,t2,t3,t4,t6,t241,t158]
set_option maxHeartbeats 0 in
theorem b1421 : Ban 228 8 v1403 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1404 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t241,t158]
set_option maxHeartbeats 0 in
theorem b1422 : Ban 228 8 v1404 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1405 : List ℕ := [t0,t242,t1,t2,t3,t4,t6,t158]
set_option maxHeartbeats 0 in
theorem b1423 : Ban 228 8 v1405 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1406 : List ℕ := [t0,t242,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1424 : Ban 228 8 v1406 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1407 : List ℕ := [t0,t1,t2,t3,t4,t243,t5,t158]
set_option maxHeartbeats 0 in
theorem b1425 : Ban 228 8 v1407 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1408 : List ℕ := [t0,t1,t2,t3,t4,t243,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1426 : Ban 228 8 v1408 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1409 : List ℕ := [t0,t1,t2,t3,t4,t466,t5,t6]
set_option maxHeartbeats 0 in
theorem b1427 : Ban 228 8 v1409 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1410 : List ℕ := [t0,t1,t2,t3,t4,t466,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1428 : Ban 228 8 v1410 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1411 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t467]
set_option maxHeartbeats 0 in
theorem b1429 : Ban 228 8 v1411 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1412 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t158,t467]
set_option maxHeartbeats 0 in
theorem b1430 : Ban 228 8 v1412 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1413 : List ℕ := [t0,t468,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1431 : Ban 228 8 v1413 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1414 : List ℕ := [t0,t468,t1,t2,t3,t4,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1432 : Ban 228 8 v1414 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1415 : List ℕ := [t0,t1,t2,t3,t4,t469,t5,t6]
set_option maxHeartbeats 0 in
theorem b1433 : Ban 228 8 v1415 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1416 : List ℕ := [t0,t1,t2,t3,t4,t469,t5,t6,t158]
set_option maxHeartbeats 0 in
theorem b1434 : Ban 228 8 v1416 := viaCut p127_114 w79 (by decide) (by decide +kernel) (by decide +kernel)
def v1417 : List ℕ := [t0,t1,t159,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1435 : Ban 228 8 v1417 := viaCut p127_73 w2 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1436 : Ban 228 9 v1241 := viaBranch (ws := [v1242,v360,v1243,v1244,v1245,v1246,v1247,v1248,v1249,v1250,v1251,v1252,v1253,v1254,v1255,v625,v1256,v1257,v1258,v1259,v1260,v1261,v1262,v1263,v1264,v1265,v1266,v811,v1267,v1268,v1269,v1270,v1271,v1272,v1273,v1274,v1275,v1276,v1277,v1278,v1279,v1280,v1281,v1282,v1283,v1284,v1285,v1286,v1287,v911,v1288,v982,v1289,v1290,v1291,v1292,v1293,v1294,v1295,v1296,v1297,v1298,v1299,v1300,v1301,v1302,v1303,v1304,v1305,v1306,v1307,v1308,v1309,v1310,v1311,v1312,v1313,v1314,v1315,v1316,v1317,v1318,v1319,v1320,v1321,v1322,v1323,v1324,v1187,v1189,v1325,v1326,v1327,v1328,v1329,v1330,v1331,v1332,v1333,v1334,v1335,v1336,v1337,v1338,v1339,v1340,v1341,v1342,v1343,v1344,v1345,v1346,v1347,v1348,v1349,v1350,v1351,v1352,v1353,v1354,v1355,v1356,v1357,v1358,v1359,v1360,v1361,v1362,v1363,v1364,v1365,v1366,v1367,v1368,v1369,v1370,v1371,v1372,v1373,v1374,v1375,v1376,v1377,v1378,v1379,v1380,v1381,v1382,v1383,v1384,v1385,v1386,v1387,v1388,v1389,v1390,v1391,v1392,v1393,v1394,v1395,v1396,v1397,v1398,v1399,v1400,v1402,v1403,v1404,v1405,v1406,v1407,v1408,v1409,v1410,v1411,v1412,v1413,v1414,v1415,v1416,v1417]) (consBan b1259 (consBan b365 (consBan b1260 (consBan b1261 (consBan b1262 (consBan b1263 (consBan b1264 (consBan b1265 (consBan b1266 (consBan b1267 (consBan b1268 (consBan b1269 (consBan b1270 (consBan b1271 (consBan b1272 (consBan b633 (consBan b1273 (consBan b1274 (consBan b1275 (consBan b1276 (consBan b1277 (consBan b1278 (consBan b1279 (consBan b1280 (consBan b1281 (consBan b1282 (consBan b1283 (consBan b820 (consBan b1284 (consBan b1285 (consBan b1286 (consBan b1287 (consBan b1288 (consBan b1289 (consBan b1290 (consBan b1291 (consBan b1292 (consBan b1293 (consBan b1294 (consBan b1295 (consBan b1296 (consBan b1297 (consBan b1298 (consBan b1299 (consBan b1300 (consBan b1301 (consBan b1302 (consBan b1303 (consBan b1304 (consBan b992 (consBan b1305 (consBan b993 (consBan b1306 (consBan b1307 (consBan b1308 (consBan b1309 (consBan b1310 (consBan b1311 (consBan b1312 (consBan b1313 (consBan b1314 (consBan b1315 (consBan b1316 (consBan b1317 (consBan b1318 (consBan b1319 (consBan b1320 (consBan b1321 (consBan b1322 (consBan b1323 (consBan b1324 (consBan b1325 (consBan b1326 (consBan b1327 (consBan b1328 (consBan b1329 (consBan b1330 (consBan b1331 (consBan b1332 (consBan b1333 (consBan b1334 (consBan b1335 (consBan b1336 (consBan b1337 (consBan b1338 (consBan b1339 (consBan b1340 (consBan b1341 (consBan b1203 (consBan b1204 (consBan b1342 (consBan b1343 (consBan b1344 (consBan b1345 (consBan b1346 (consBan b1347 (consBan b1348 (consBan b1350 (consBan b1351 (consBan b1352 (consBan b1353 (consBan b1354 (consBan b1355 (consBan b1356 (consBan b1357 (consBan b1358 (consBan b1359 (consBan b1360 (consBan b1361 (consBan b1362 (consBan b1363 (consBan b1364 (consBan b1365 (consBan b1366 (consBan b1367 (consBan b1368 (consBan b1369 (consBan b1370 (consBan b1371 (consBan b1372 (consBan b1373 (consBan b1374 (consBan b1375 (consBan b1376 (consBan b1377 (consBan b1378 (consBan b1379 (consBan b1380 (consBan b1381 (consBan b1382 (consBan b1383 (consBan b1384 (consBan b1385 (consBan b1386 (consBan b1387 (consBan b1388 (consBan b1389 (consBan b1390 (consBan b1391 (consBan b1392 (consBan b1393 (consBan b1394 (consBan b1395 (consBan b1396 (consBan b1397 (consBan b1398 (consBan b1399 (consBan b1400 (consBan b1401 (consBan b1402 (consBan b1403 (consBan b1404 (consBan b1405 (consBan b1406 (consBan b1407 (consBan b1408 (consBan b1409 (consBan b1410 (consBan b1411 (consBan b1412 (consBan b1413 (consBan b1414 (consBan b1415 (consBan b1416 (consBan b1417 (consBan b1419 (consBan b1420 (consBan b1421 (consBan b1422 (consBan b1423 (consBan b1424 (consBan b1425 (consBan b1426 (consBan b1427 (consBan b1428 (consBan b1429 (consBan b1430 (consBan b1431 (consBan b1432 (consBan b1433 (consBan b1434 (consBan b1435 (nilBan 228 8))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1437 : Ban 228 9 v1417 := viaCut p127_109 w36 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1438 : Ban 228 9 v1350 := viaCut p127_114 w71 (by decide) (by decide +kernel) (by decide +kernel)
def v1418 : List ℕ := [t0,t1,t2,t161,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1439 : Ban 228 9 v1418 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1419 : List ℕ := [t0,t1,t2,t3,t162,t5,t6]
set_option maxHeartbeats 0 in
theorem b1440 : Ban 228 9 v1419 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1420 : List ℕ := [t0,t1,t2,t4,t162,t5,t6]
set_option maxHeartbeats 0 in
theorem b1441 : Ban 228 9 v1420 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v1421 : List ℕ := [t0,t1,t2,t3,t4,t162,t5,t6]
set_option maxHeartbeats 0 in
theorem b1442 : Ban 228 9 v1421 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1422 : List ℕ := [t0,t1,t163,t2,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1443 : Ban 228 9 v1422 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1423 : List ℕ := [t0,t1,t163,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1444 : Ban 228 9 v1423 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1424 : List ℕ := [t0,t1,t2,t164,t3,t5,t6]
set_option maxHeartbeats 0 in
theorem b1445 : Ban 228 9 v1424 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1425 : List ℕ := [t0,t1,t2,t164,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1446 : Ban 228 9 v1425 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1426 : List ℕ := [t0,t232,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1447 : Ban 228 9 v1426 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1427 : List ℕ := [t0,t1,t2,t3,t4,t233,t6]
set_option maxHeartbeats 0 in
theorem b1448 : Ban 228 9 v1427 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1428 : List ℕ := [t0,t1,t2,t4,t5,t233,t6]
set_option maxHeartbeats 0 in
theorem b1449 : Ban 228 9 v1428 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1429 : List ℕ := [t0,t1,t2,t3,t4,t5,t233,t6]
set_option maxHeartbeats 0 in
theorem b1450 : Ban 228 9 v1429 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1430 : List ℕ := [t0,t1,t2,t234,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1451 : Ban 228 9 v1430 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1431 : List ℕ := [t0,t1,t2,t234,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1452 : Ban 228 9 v1431 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1432 : List ℕ := [t0,t1,t2,t3,t4,t235,t6]
set_option maxHeartbeats 0 in
theorem b1453 : Ban 228 9 v1432 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1433 : List ℕ := [t0,t1,t2,t3,t4,t235,t5,t6]
set_option maxHeartbeats 0 in
theorem b1454 : Ban 228 9 v1433 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1434 : List ℕ := [t170,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1455 : Ban 228 9 v1434 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1435 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t171]
set_option maxHeartbeats 0 in
theorem b1456 : Ban 228 9 v1435 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1436 : List ℕ := [t0,t1,t2,t172,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1457 : Ban 228 9 v1436 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1437 : List ℕ := [t0,t1,t2,t3,t4,t5,t173,t6]
set_option maxHeartbeats 0 in
theorem b1458 : Ban 228 9 v1437 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1438 : List ℕ := [t236,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1459 : Ban 228 9 v1438 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1439 : List ℕ := [t0,t1,t2,t3,t4,t5,t237,t6]
set_option maxHeartbeats 0 in
theorem b1460 : Ban 228 9 v1439 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1440 : List ℕ := [t0,t1,t2,t3,t238,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1461 : Ban 228 9 v1440 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1441 : List ℕ := [t0,t1,t2,t3,t4,t239,t5,t6]
set_option maxHeartbeats 0 in
theorem b1462 : Ban 228 9 v1441 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1442 : List ℕ := [t178,t0,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1463 : Ban 228 9 v1442 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1443 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t179]
set_option maxHeartbeats 0 in
theorem b1464 : Ban 228 9 v1443 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v1444 : List ℕ := [t0,t1,t2,t3,t180,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1465 : Ban 228 9 v1444 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v1445 : List ℕ := [t0,t1,t2,t3,t4,t5,t181,t6]
set_option maxHeartbeats 0 in
theorem b1466 : Ban 228 9 v1445 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1446 : List ℕ := [t0,t1,t2,t3,t4,t240,t5,t6]
set_option maxHeartbeats 0 in
theorem b1467 : Ban 228 9 v1446 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1447 : List ℕ := [t0,t1,t2,t3,t4,t5,t241]
set_option maxHeartbeats 0 in
theorem b1468 : Ban 228 9 v1447 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1448 : List ℕ := [t0,t1,t2,t3,t4,t6,t241]
def v1449 : List ℕ := [t7,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1469 : Ban 228 8 v1449 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1450 : List ℕ := [t1,t12,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1470 : Ban 228 8 v1450 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1451 : List ℕ := [t0,t1,t12,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1471 : Ban 228 8 v1451 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1452 : List ℕ := [t244,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1472 : Ban 228 8 v1452 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1453 : List ℕ := [t244,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1473 : Ban 228 8 v1453 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1454 : List ℕ := [t0,t13,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1474 : Ban 228 8 v1454 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1455 : List ℕ := [t0,t13,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1475 : Ban 228 8 v1455 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1456 : List ℕ := [t14,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1476 : Ban 228 8 v1456 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1457 : List ℕ := [t0,t1,t2,t18,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1477 : Ban 228 8 v1457 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1458 : List ℕ := [t19,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1478 : Ban 228 8 v1458 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1459 : List ℕ := [t0,t1,t20,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1479 : Ban 228 8 v1459 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1460 : List ℕ := [t21,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1480 : Ban 228 8 v1460 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1461 : List ℕ := [t1,t2,t3,t22,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1481 : Ban 228 8 v1461 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1462 : List ℕ := [t0,t1,t2,t3,t22,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1482 : Ban 228 8 v1462 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1463 : List ℕ := [t28,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1483 : Ban 228 8 v1463 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1464 : List ℕ := [t28,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1484 : Ban 228 8 v1464 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1465 : List ℕ := [t0,t1,t2,t29,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1485 : Ban 228 8 v1465 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1466 : List ℕ := [t0,t1,t2,t29,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1486 : Ban 228 8 v1466 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1467 : List ℕ := [t30,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1487 : Ban 228 8 v1467 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1468 : List ℕ := [t0,t1,t2,t3,t4,t31,t6,t241]
set_option maxHeartbeats 0 in
theorem b1488 : Ban 228 8 v1468 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1469 : List ℕ := [t37,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1489 : Ban 228 8 v1469 := viaCut p127_114 w48 (by decide) (by decide +kernel) (by decide +kernel)
def v1470 : List ℕ := [t0,t1,t2,t3,t38,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1490 : Ban 228 8 v1470 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1471 : List ℕ := [t188,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1491 : Ban 228 8 v1471 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1472 : List ℕ := [t0,t1,t2,t3,t4,t6,t189,t241]
set_option maxHeartbeats 0 in
theorem b1492 : Ban 228 8 v1472 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1473 : List ℕ := [t190,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1493 : Ban 228 8 v1473 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1474 : List ℕ := [t0,t1,t2,t3,t4,t191,t6,t241]
set_option maxHeartbeats 0 in
theorem b1494 : Ban 228 8 v1474 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1475 : List ℕ := [t470,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1495 : Ban 228 8 v1475 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1476 : List ℕ := [t0,t1,t2,t3,t4,t6,t241,t183]
set_option maxHeartbeats 0 in
theorem b1496 : Ban 228 8 v1476 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1477 : List ℕ := [t471,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1497 : Ban 228 8 v1477 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1478 : List ℕ := [t0,t1,t2,t3,t4,t6,t472]
set_option maxHeartbeats 0 in
theorem b1498 : Ban 228 8 v1478 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1479 : List ℕ := [t0,t1,t2,t3,t4,t6,t472,t241]
set_option maxHeartbeats 0 in
theorem b1499 : Ban 228 8 v1479 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1480 : List ℕ := [t0,t250,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1500 : Ban 228 8 v1480 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1481 : List ℕ := [t0,t1,t251,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1501 : Ban 228 8 v1481 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1482 : List ℕ := [t0,t1,t2,t251,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1502 : Ban 228 8 v1482 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1483 : List ℕ := [t252,t0,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1503 : Ban 228 8 v1483 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1484 : List ℕ := [t252,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1504 : Ban 228 8 v1484 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1485 : List ℕ := [t0,t1,t253,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1505 : Ban 228 8 v1485 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1486 : List ℕ := [t0,t1,t253,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1506 : Ban 228 8 v1486 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1487 : List ℕ := [t352,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1507 : Ban 228 8 v1487 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1488 : List ℕ := [t0,t1,t2,t3,t353,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1508 : Ban 228 8 v1488 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1489 : List ℕ := [t0,t354,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1509 : Ban 228 8 v1489 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1490 : List ℕ := [t0,t1,t2,t355,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1510 : Ban 228 8 v1490 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1491 : List ℕ := [t257,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1511 : Ban 228 8 v1491 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1492 : List ℕ := [t0,t1,t2,t3,t4,t258,t6,t241]
set_option maxHeartbeats 0 in
theorem b1512 : Ban 228 8 v1492 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1493 : List ℕ := [t0,t259,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1513 : Ban 228 8 v1493 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1494 : List ℕ := [t0,t1,t2,t3,t260,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1514 : Ban 228 8 v1494 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1495 : List ℕ := [t264,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1515 : Ban 228 8 v1495 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1496 : List ℕ := [t0,t1,t2,t3,t4,t6,t241,t265]
set_option maxHeartbeats 0 in
theorem b1516 : Ban 228 8 v1496 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1497 : List ℕ := [t0,t266,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1517 : Ban 228 8 v1497 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1498 : List ℕ := [t0,t1,t2,t3,t4,t267,t6,t241]
set_option maxHeartbeats 0 in
theorem b1518 : Ban 228 8 v1498 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1499 : List ℕ := [t473,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1519 : Ban 228 8 v1499 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1500 : List ℕ := [t0,t1,t2,t3,t4,t6,t474]
set_option maxHeartbeats 0 in
theorem b1520 : Ban 228 8 v1500 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1501 : List ℕ := [t0,t1,t2,t3,t4,t6,t241,t474]
set_option maxHeartbeats 0 in
theorem b1521 : Ban 228 8 v1501 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1502 : List ℕ := [t0,t475,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1522 : Ban 228 8 v1502 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1503 : List ℕ := [t0,t1,t2,t3,t4,t6,t476]
set_option maxHeartbeats 0 in
theorem b1523 : Ban 228 8 v1503 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1504 : List ℕ := [t0,t1,t2,t3,t4,t6,t476,t241]
set_option maxHeartbeats 0 in
theorem b1524 : Ban 228 8 v1504 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1505 : List ℕ := [t0,t1,t91,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1525 : Ban 228 8 v1505 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1506 : List ℕ := [t0,t1,t3,t92,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1526 : Ban 228 8 v1506 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1507 : List ℕ := [t0,t1,t2,t3,t92,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1527 : Ban 228 8 v1507 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1508 : List ℕ := [t0,t1,t147,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1528 : Ban 228 8 v1508 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1509 : List ℕ := [t0,t1,t147,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1529 : Ban 228 8 v1509 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1510 : List ℕ := [t0,t1,t2,t148,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1530 : Ban 228 8 v1510 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1511 : List ℕ := [t0,t1,t2,t148,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1531 : Ban 228 8 v1511 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1512 : List ℕ := [t149,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1532 : Ban 228 8 v1512 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v1513 : List ℕ := [t0,t1,t2,t3,t4,t150,t6,t241]
set_option maxHeartbeats 0 in
theorem b1533 : Ban 228 8 v1513 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v1514 : List ℕ := [t0,t1,t151,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1534 : Ban 228 8 v1514 := viaCut p127_114 w78 (by decide) (by decide +kernel) (by decide +kernel)
def v1515 : List ℕ := [t0,t1,t2,t3,t152,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1535 : Ban 228 8 v1515 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v1516 : List ℕ := [t157,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1536 : Ban 228 8 v1516 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1517 : List ℕ := [t0,t1,t159,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1537 : Ban 228 8 v1517 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1518 : List ℕ := [t0,t1,t2,t3,t4,t160,t241]
set_option maxHeartbeats 0 in
theorem b1538 : Ban 228 8 v1518 := viaCut p127_114 w71 (by decide) (by decide +kernel) (by decide +kernel)
def v1519 : List ℕ := [t0,t1,t2,t3,t4,t160,t6,t241]
set_option maxHeartbeats 0 in
theorem b1539 : Ban 228 8 v1519 := viaCut p127_114 w71 (by decide) (by decide +kernel) (by decide +kernel)
def v1520 : List ℕ := [t477,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1540 : Ban 228 8 v1520 := viaCut p127_109 w81 (by decide) (by decide +kernel) (by decide +kernel)
def v1521 : List ℕ := [t0,t1,t2,t3,t4,t6,t241,t467]
set_option maxHeartbeats 0 in
theorem b1541 : Ban 228 8 v1521 := viaCut p127_109 w81 (by decide) (by decide +kernel) (by decide +kernel)
def v1522 : List ℕ := [t0,t1,t478,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1542 : Ban 228 8 v1522 := viaCut p127_109 w81 (by decide) (by decide +kernel) (by decide +kernel)
def v1523 : List ℕ := [t0,t1,t2,t3,t4,t6,t479,t241]
set_option maxHeartbeats 0 in
theorem b1543 : Ban 228 8 v1523 := viaCut p127_114 w71 (by decide) (by decide +kernel) (by decide +kernel)
def v1524 : List ℕ := [t0,t1,t2,t161,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1544 : Ban 228 8 v1524 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1525 : List ℕ := [t0,t1,t2,t3,t162,t6,t241]
set_option maxHeartbeats 0 in
theorem b1545 : Ban 228 8 v1525 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1526 : List ℕ := [t0,t1,t2,t4,t162,t6,t241]
set_option maxHeartbeats 0 in
theorem b1546 : Ban 228 8 v1526 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v1527 : List ℕ := [t0,t1,t2,t3,t4,t162,t6,t241]
set_option maxHeartbeats 0 in
theorem b1547 : Ban 228 8 v1527 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1528 : List ℕ := [t0,t1,t163,t2,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1548 : Ban 228 8 v1528 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1529 : List ℕ := [t0,t1,t163,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1549 : Ban 228 8 v1529 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1530 : List ℕ := [t0,t1,t2,t164,t3,t6,t241]
set_option maxHeartbeats 0 in
theorem b1550 : Ban 228 8 v1530 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1531 : List ℕ := [t0,t1,t2,t164,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1551 : Ban 228 8 v1531 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1532 : List ℕ := [t170,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1552 : Ban 228 8 v1532 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1533 : List ℕ := [t0,t1,t2,t3,t4,t6,t241,t171]
set_option maxHeartbeats 0 in
theorem b1553 : Ban 228 8 v1533 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1534 : List ℕ := [t0,t1,t2,t172,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1554 : Ban 228 8 v1534 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1535 : List ℕ := [t0,t1,t2,t3,t4,t173,t6,t241]
set_option maxHeartbeats 0 in
theorem b1555 : Ban 228 8 v1535 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1536 : List ℕ := [t0,t480,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1556 : Ban 228 8 v1536 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1537 : List ℕ := [t0,t1,t2,t3,t4,t6,t481]
set_option maxHeartbeats 0 in
theorem b1557 : Ban 228 8 v1537 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1538 : List ℕ := [t0,t1,t2,t3,t4,t6,t241,t481]
set_option maxHeartbeats 0 in
theorem b1558 : Ban 228 8 v1538 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1539 : List ℕ := [t0,t1,t2,t482,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1559 : Ban 228 8 v1539 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1540 : List ℕ := [t0,t1,t2,t3,t4,t6,t483]
set_option maxHeartbeats 0 in
theorem b1560 : Ban 228 8 v1540 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1541 : List ℕ := [t0,t1,t2,t3,t4,t6,t483,t241]
set_option maxHeartbeats 0 in
theorem b1561 : Ban 228 8 v1541 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1542 : List ℕ := [t178,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1562 : Ban 228 8 v1542 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1543 : List ℕ := [t0,t1,t2,t3,t4,t241,t179]
set_option maxHeartbeats 0 in
theorem b1563 : Ban 228 8 v1543 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v1544 : List ℕ := [t0,t1,t2,t3,t4,t6,t241,t179]
set_option maxHeartbeats 0 in
theorem b1564 : Ban 228 8 v1544 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1545 : List ℕ := [t0,t1,t2,t3,t180,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1565 : Ban 228 8 v1545 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1546 : List ℕ := [t0,t1,t2,t3,t4,t181,t241]
set_option maxHeartbeats 0 in
theorem b1566 : Ban 228 8 v1546 := viaCut p127_61 w3 (by decide) (by decide +kernel) (by decide +kernel)
def v1547 : List ℕ := [t0,t1,t2,t3,t4,t181,t6,t241]
set_option maxHeartbeats 0 in
theorem b1567 : Ban 228 8 v1547 := viaCut p127_52 w1 (by decide) (by decide +kernel) (by decide +kernel)
def v1548 : List ℕ := [t484,t0,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1568 : Ban 228 8 v1548 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v1549 : List ℕ := [t0,t1,t2,t3,t4,t6,t241,t485]
set_option maxHeartbeats 0 in
theorem b1569 : Ban 228 8 v1549 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v1550 : List ℕ := [t0,t1,t2,t3,t486,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1570 : Ban 228 8 v1550 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v1551 : List ℕ := [t0,t1,t2,t3,t4,t6,t487,t241]
set_option maxHeartbeats 0 in
theorem b1571 : Ban 228 8 v1551 := viaCut p127_91 w50 (by decide) (by decide +kernel) (by decide +kernel)
def v1552 : List ℕ := [t0,t242,t1,t2,t3,t4,t6]
set_option maxHeartbeats 0 in
theorem b1572 : Ban 228 8 v1552 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1553 : List ℕ := [t0,t242,t1,t2,t3,t4,t241]
set_option maxHeartbeats 0 in
theorem b1573 : Ban 228 8 v1553 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1554 : List ℕ := [t0,t242,t1,t2,t3,t4,t6,t241]
set_option maxHeartbeats 0 in
theorem b1574 : Ban 228 8 v1554 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1575 : Ban 228 9 v1448 := viaBranch (ws := [v1449,v393,v1450,v1451,v1452,v1453,v1454,v1455,v1456,v1457,v1458,v1459,v1460,v657,v1461,v1462,v1463,v1464,v1465,v1466,v1467,v1468,v1469,v1470,v1471,v1472,v1473,v1474,v1475,v843,v1476,v1477,v1478,v1479,v1480,v1481,v1035,v1482,v1483,v1484,v1485,v1486,v1487,v1488,v1489,v1490,v1491,v1492,v1493,v1494,v1495,v1496,v1497,v1498,v1499,v1500,v1501,v1502,v1503,v1504,v1505,v1221,v1506,v1507,v1508,v1509,v1510,v1511,v1512,v1513,v1514,v1515,v1516,v1400,v1403,v1517,v1518,v1519,v1520,v1521,v1522,v1523,v1524,v1525,v1526,v1527,v1528,v1529,v1530,v1531,v1532,v1533,v1534,v1535,v1536,v1537,v1538,v1539,v1540,v1541,v1542,v1543,v1544,v1545,v1546,v1547,v1548,v1549,v1550,v1551,v1552,v1553,v1554]) (consBan b1469 (consBan b398 (consBan b1470 (consBan b1471 (consBan b1472 (consBan b1473 (consBan b1474 (consBan b1475 (consBan b1476 (consBan b1477 (consBan b1478 (consBan b1479 (consBan b1480 (consBan b665 (consBan b1481 (consBan b1482 (consBan b1483 (consBan b1484 (consBan b1485 (consBan b1486 (consBan b1487 (consBan b1488 (consBan b1489 (consBan b1490 (consBan b1491 (consBan b1492 (consBan b1493 (consBan b1494 (consBan b1495 (consBan b852 (consBan b1496 (consBan b1497 (consBan b1498 (consBan b1499 (consBan b1500 (consBan b1501 (consBan b1101 (consBan b1502 (consBan b1503 (consBan b1504 (consBan b1505 (consBan b1506 (consBan b1507 (consBan b1508 (consBan b1509 (consBan b1510 (consBan b1511 (consBan b1512 (consBan b1513 (consBan b1514 (consBan b1515 (consBan b1516 (consBan b1517 (consBan b1518 (consBan b1519 (consBan b1520 (consBan b1521 (consBan b1522 (consBan b1523 (consBan b1524 (consBan b1525 (consBan b1237 (consBan b1526 (consBan b1527 (consBan b1528 (consBan b1529 (consBan b1530 (consBan b1531 (consBan b1532 (consBan b1533 (consBan b1534 (consBan b1535 (consBan b1536 (consBan b1419 (consBan b1421 (consBan b1537 (consBan b1538 (consBan b1539 (consBan b1540 (consBan b1541 (consBan b1542 (consBan b1543 (consBan b1544 (consBan b1545 (consBan b1546 (consBan b1547 (consBan b1548 (consBan b1549 (consBan b1550 (consBan b1551 (consBan b1552 (consBan b1553 (consBan b1554 (consBan b1555 (consBan b1556 (consBan b1557 (consBan b1558 (consBan b1559 (consBan b1560 (consBan b1561 (consBan b1562 (consBan b1563 (consBan b1564 (consBan b1565 (consBan b1566 (consBan b1567 (consBan b1568 (consBan b1569 (consBan b1570 (consBan b1571 (consBan b1572 (consBan b1573 (consBan b1574 (nilBan 228 8)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
def v1555 : List ℕ := [t0,t1,t2,t3,t4,t5,t6,t241]
set_option maxHeartbeats 0 in
theorem b1576 : Ban 228 9 v1555 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem b1577 : Ban 228 9 v1552 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1556 : List ℕ := [t0,t242,t1,t2,t3,t4,t5,t6]
set_option maxHeartbeats 0 in
theorem b1578 : Ban 228 9 v1556 := viaCut p127_114 w0 (by decide) (by decide +kernel) (by decide +kernel)
def v1557 : List ℕ := [t0,t1,t2,t3,t4,t243,t5]
set_option maxHeartbeats 0 in
theorem b1579 : Ban 228 9 v1557 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
def v1558 : List ℕ := [t0,t1,t2,t3,t4,t243,t5,t6]
set_option maxHeartbeats 0 in
theorem b1580 : Ban 228 9 v1558 := viaCut p127_114 w10 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1581 : Ban 228 10 v0 := viaBranch (ws := [v1,v3,v399,v400,v401,v402,v4,v403,v404,v405,v407,v408,v409,v410,v663,v664,v665,v666,v420,v667,v668,v669,v726,v727,v728,v729,v848,v849,v850,v851,v756,v852,v853,v854,v855,v856,v857,v858,v859,v1093,v891,v1094,v1095,v1096,v1097,v1098,v1099,v1100,v1101,v1102,v1103,v1104,v1105,v1106,v1107,v1108,v1109,v1110,v1111,v1112,v1113,v1114,v1115,v1116,v1117,v1118,v1227,v1228,v1229,v1230,v1175,v1231,v1232,v1233,v1234,v1235,v1236,v1237,v1238,v1239,v1240,v1241,v1417,v1350,v1418,v1419,v1420,v1421,v1422,v1423,v1424,v1425,v1426,v1427,v1428,v1429,v1430,v1431,v1432,v1433,v1434,v1435,v1436,v1437,v1438,v1439,v1440,v1441,v1442,v1443,v1444,v1445,v1446,v1447,v1448,v1555,v1552,v1556,v1557,v1558]) (consBan b1 (consBan b404 (consBan b405 (consBan b406 (consBan b407 (consBan b408 (consBan b409 (consBan b410 (consBan b411 (consBan b413 (consBan b414 (consBan b415 (consBan b416 (consBan b671 (consBan b672 (consBan b673 (consBan b674 (consBan b675 (consBan b676 (consBan b677 (consBan b678 (consBan b735 (consBan b736 (consBan b737 (consBan b738 (consBan b857 (consBan b858 (consBan b859 (consBan b860 (consBan b861 (consBan b862 (consBan b863 (consBan b864 (consBan b865 (consBan b866 (consBan b867 (consBan b868 (consBan b869 (consBan b1107 (consBan b1108 (consBan b1109 (consBan b1110 (consBan b1111 (consBan b1112 (consBan b1113 (consBan b1114 (consBan b1115 (consBan b1116 (consBan b1117 (consBan b1118 (consBan b1119 (consBan b1120 (consBan b1121 (consBan b1122 (consBan b1123 (consBan b1124 (consBan b1125 (consBan b1126 (consBan b1127 (consBan b1128 (consBan b1129 (consBan b1130 (consBan b1131 (consBan b1132 (consBan b1133 (consBan b1243 (consBan b1244 (consBan b1245 (consBan b1246 (consBan b1247 (consBan b1248 (consBan b1249 (consBan b1250 (consBan b1251 (consBan b1252 (consBan b1253 (consBan b1254 (consBan b1255 (consBan b1256 (consBan b1257 (consBan b1258 (consBan b1436 (consBan b1437 (consBan b1438 (consBan b1439 (consBan b1440 (consBan b1441 (consBan b1442 (consBan b1443 (consBan b1444 (consBan b1445 (consBan b1446 (consBan b1447 (consBan b1448 (consBan b1449 (consBan b1450 (consBan b1451 (consBan b1452 (consBan b1453 (consBan b1454 (consBan b1455 (consBan b1456 (consBan b1457 (consBan b1458 (consBan b1459 (consBan b1460 (consBan b1461 (consBan b1462 (consBan b1463 (consBan b1464 (consBan b1465 (consBan b1466 (consBan b1467 (consBan b1468 (consBan b1575 (consBan b1576 (consBan b1577 (consBan b1578 (consBan b1579 (consBan b1580 (nilBan 228 9))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem cap10 : Ban 228 10 v0 := b1581
end PEqualNP.Outside.L_meta_10780.Cert

namespace PEqualNP.Outside.L_meta_10780.Complete
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_10780.Free

def posBits : ℕ := 0xc183060c183060c183060c183060c183050a142850a142850a142850a142850a1424489122448912244891224489122448910a142850a142850a142850a142850a14283060c183060c183060c183060c183060b060c183060c183060c183060c183060c122448912244891224489122448912244889122448912244891224489122448912242850a142850a142850a142850a142850942850a142850a142850a142850a142850912244891224489122448912244891224244891224489122448912244891224489
def negBits : ℕ := 0x8901420304480e18284070c14203040404480a1018224070c14203860a1018202022405080c11203860a101c305080c101011202840608901c305080e1828406080808901420304480e18284070c14203040404480a1018224070c14203860a1018202022405080c11203860a101c305080c101011202840608901c305080e1828406080808901420304480e18284070c14203040404480a1018224070c14203860a1018202022405080c11203860a101c305080c101011202840608901c305080e182840608080
def sample (bank : ℕ) (i : Fin 228) (j : Fin 7) := bank.testBit (7*i.val+j.val)
def inputs : List ℕ := [0x4154082a81055020aa04154082a81055020aa04154082a81055020aa0000000000000000000ffffe00000000000000ffffe0000000007ffff,0x159802b30056600acc0159802b30056600acc0159802b30056600acc000000000000007ffff000000000000007ffff0000000003ffff80000,0x819e1033c2067840cf0819e1033c2067840cf0819e1033c2067840cf000000000000000000000000000003ffff8000000001ffffc000000000,0x29e0053c00a78014f0029e0053c00a78014f0029e0053c00a78014f000000000003ffff800000000000000000000000000000000000007ffff,0xe0001c0003800070000e0001c0003800070000e0001c00038000700000001ffffc00000000000001ffffc00000000000001fffffffff80000,0x3000060000c000180003000060000c000180003000060000c00018000ffffe0000000000000000001ffffffffffffffffffe00000000000000,0xc000180003000060000c000180003000060000c000180003000060000fffffffffffffffffffffffe000000000000000000000000000000000]

def seeds : List Wire := inputs.map (fun a => (false,a))
set_option maxHeartbeats 10000000 in
theorem listed : ∀ i : Fin 228, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (228+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 228, Frame.target (sample posBits i)=true ∧ Frame.target (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 228, ∀ b∈inputs, b.testBit i.val≠b.testBit (228+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 228 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 7 C=Frame.target) :
    ∃ k≤C.gates.countP counted, Live 228 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 7 → Bool) : C.eval (List.ofFn x)=Frame.target x := congrFun eq x
  have good : Good 228 out.2 := by
    intro i hi same
    let j : Fin 228 := ⟨i,hi⟩
    have diff : read i out=read (228+i) out := by
      change (out.1 != out.2.testBit i) = (out.1 != out.2.testBit (228+i))
      rw [same]
    have p := ev i;have n := ev (228+i)
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
    (hasNot : ∃ g ∈ gs, g.op = .not) : 12 ≤ gs.length := by
  obtain ⟨k,hk,live⟩ := trace ⟨gs,o⟩ fan (funext correct)
  have same : inputs.toFinset = Cert.v0.toFinset := by decide +kernel
  rw [same] at live
  have lo : 11 ≤ k := by
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

end PEqualNP.Outside.L_meta_10780.Complete
theorem PEqualNP.Outside.L_meta_10780 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_10780.Frame.finish PEqualNP.Outside.L_meta_10780.Complete.signed_floor
