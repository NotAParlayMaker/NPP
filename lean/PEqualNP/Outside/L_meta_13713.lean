import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13713

-- Compression des fils et restriction adaptées de L-meta-4425 et L-meta-2960.
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



-- The paired-wire restriction and circuit trace are adapted from L-meta-12238.
def restrictedInputs : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
def splitV0 : List ℕ := [0x18000003f,0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB0 : Ban 36 5 splitV0 := viaSmall (by decide +kernel) (by decide)

def splitV1 : List ℕ := [0x18000003f,0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB1 : Ban 36 5 splitV1 := viaSmall (by decide +kernel) (by decide)

def splitV2 : List ℕ := [0x240000fc0,0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB2 : Ban 36 5 splitV2 := viaSmall (by decide +kernel) (by decide)

def splitV3 : List ℕ := [0x240000fc0,0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB3 : Ban 36 5 splitV3 := viaSmall (by decide +kernel) (by decide)

def splitV4 : List ℕ := [0x800fc0000,0x37df7df740003f000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB4 : Ban 36 5 splitV4 := viaSmall (by decide +kernel) (by decide)

def splitV5 : List ℕ := [0x71c71c740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB5 : Ban 36 5 splitV5 := viaSmall (by decide +kernel) (by decide)

def splitV6 : List ℕ := [0x820820883ffc0000,0x37df7df740003f000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB6 : Ban 36 5 splitV6 := viaSmall (by decide +kernel) (by decide)

def splitV7 : List ℕ := [0x1041041083ffc0000,0x37df7df740003f000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB7 : Ban 36 5 splitV7 := viaSmall (by decide +kernel) (by decide)

def splitV8 : List ℕ := [0x1249249240003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB8 : Ban 36 5 splitV8 := viaSmall (by decide +kernel) (by decide)

def splitV9 : List ℕ := [0x2082082083ffc0000,0x37df7df740003f000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB9 : Ban 36 5 splitV9 := viaSmall (by decide +kernel) (by decide)

def splitV10 : List ℕ := [0x2492492440003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB10 : Ban 36 5 splitV10 := viaSmall (by decide +kernel) (by decide)

def splitV11 : List ℕ := [0x32cb2cb240003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB11 : Ban 36 5 splitV11 := viaSmall (by decide +kernel) (by decide)

def splitV12 : List ℕ := [0x34d34d3440003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB12 : Ban 36 5 splitV12 := viaSmall (by decide +kernel) (by decide)

def splitV13 : List ℕ := [0x37df7df740003f000,0x38e38e38800fc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB13 : Ban 36 5 splitV13 := viaSmall (by decide +kernel) (by decide)

def splitV14 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x64924924240000fc0,0x1051451451bf00003f,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB14 : Ban 36 5 splitV14 := viaSmall (by decide +kernel) (by decide)

def splitV15 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x9249249218000003f,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB15 : Ban 36 5 splitV15 := viaSmall (by decide +kernel) (by decide)

def splitV16 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1000000001bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB16 : Ban 36 5 splitV16 := viaSmall (by decide +kernel) (by decide)

def splitV17 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1010410411bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB17 : Ban 36 5 splitV17 := viaSmall (by decide +kernel) (by decide)

def splitV18 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1041041041bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB18 : Ban 36 5 splitV18 := viaSmall (by decide +kernel) (by decide)

def splitV19 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x10514514503f000000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB19 : Ban 36 5 splitV19 := viaSmall (by decide +kernel) (by decide)

def splitV20 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x10514514518000003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB20 : Ban 36 5 splitV20 := viaSmall (by decide +kernel) (by decide)

def splitV21 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x44410410464003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB21 : Ban 36 5 splitV21 := viaSmall (by decide +kernel) (by decide)

def splitV22 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x448208208240000fc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB22 : Ban 36 5 splitV22 := viaSmall (by decide +kernel) (by decide)

def splitV23 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x468a28a2864003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB23 : Ban 36 5 splitV23 := viaSmall (by decide +kernel) (by decide)

def splitV24 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c40003f000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB24 : Ban 36 5 splitV24 := viaSmall (by decide +kernel) (by decide)

def splitV25 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x48208208258003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB25 : Ban 36 5 splitV25 := viaSmall (by decide +kernel) (by decide)

def splitV26 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x48820820818000003f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB26 : Ban 36 5 splitV26 := viaSmall (by decide +kernel) (by decide)

def splitV27 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49861861858003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB27 : Ban 36 5 splitV27 := viaSmall (by decide +kernel) (by decide)

def splitV28 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa00000000a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB28 : Ban 36 5 splitV28 := viaSmall (by decide +kernel) (by decide)

def splitV29 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa01041041a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB29 : Ban 36 5 splitV29 := viaSmall (by decide +kernel) (by decide)

def splitV30 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa02082082a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB30 : Ban 36 5 splitV30 := viaSmall (by decide +kernel) (by decide)

def splitV31 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3240000fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB31 : Ban 36 5 splitV31 := viaSmall (by decide +kernel) (by decide)

def splitV32 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa37df7df7e40ffffc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB32 : Ban 36 5 splitV32 := viaSmall (by decide +kernel) (by decide)

def splitV33 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa3befbefba7ffc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB33 : Ban 36 5 splitV33 := viaSmall (by decide +kernel) (by decide)

def splitV34 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB34 : Ban 36 5 splitV34 := viaSmall (by decide +kernel) (by decide)

def splitV35 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB35 : Ban 36 5 splitV35 := viaSmall (by decide +kernel) (by decide)

def splitV36 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x4baebaebadbffff03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB36 : Ban 36 5 splitV36 := viaSmall (by decide +kernel) (by decide)

def splitV37 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x4bfffffff58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB37 : Ban 36 5 splitV37 := viaSmall (by decide +kernel) (by decide)

def splitV38 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x4fefbefbe7c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB38 : Ban 36 5 splitV38 := viaSmall (by decide +kernel) (by decide)

def splitV39 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xa030c30c3a40fc0fc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB39 : Ban 36 5 splitV39 := viaSmall (by decide +kernel) (by decide)

def splitV40 : List ℕ := [0x104104118000003f,0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB40 : Ban 36 4 splitV40 := viaSmall (by decide +kernel) (by decide)

def splitV41 : List ℕ := [0x820820883ffc0000,0x37df7df740003f000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB41 : Ban 36 4 splitV41 := viaSmall (by decide +kernel) (by decide)

def splitV42 : List ℕ := [0x134d34d340003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB42 : Ban 36 4 splitV42 := viaSmall (by decide +kernel) (by decide)

def splitV43 : List ℕ := [0x18618618800fc0000,0x37df7df740003f000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB43 : Ban 36 4 splitV43 := viaSmall (by decide +kernel) (by decide)

def splitV44 : List ℕ := [0x37df7df740003f000,0x38e38e38800fc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB44 : Ban 36 4 splitV44 := viaSmall (by decide +kernel) (by decide)

def splitV45 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1000000001bf00003f,0x46cb2cb2c64003ffc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB45 : Ban 36 4 splitV45 := viaSmall (by decide +kernel) (by decide)

def splitV46 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1010410411bf00003f,0x46cb2cb2c64003ffc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB46 : Ban 36 4 splitV46 := viaSmall (by decide +kernel) (by decide)

def splitV47 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x10514514518000003f,0x46cb2cb2c64003ffc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB47 : Ban 36 4 splitV47 := viaSmall (by decide +kernel) (by decide)

def splitV48 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x40820820864003ffc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB48 : Ban 36 4 splitV48 := viaSmall (by decide +kernel) (by decide)

def splitV49 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x468a28a2864003ffc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB49 : Ban 36 4 splitV49 := viaSmall (by decide +kernel) (by decide)

def splitV50 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xe830c30c37c003ffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB50 : Ban 36 4 splitV50 := viaSmall (by decide +kernel) (by decide)

def splitV51 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xe88208208bc0fc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB51 : Ban 36 4 splitV51 := viaSmall (by decide +kernel) (by decide)

def splitV52 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xebbefbefbfffffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB52 : Ban 36 4 splitV52 := viaSmall (by decide +kernel) (by decide)

def splitV53 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xebffffffffc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB53 : Ban 36 4 splitV53 := viaSmall (by decide +kernel) (by decide)

def splitV54 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x56db6db6d7ff03ffff,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB54 : Ban 36 4 splitV54 := viaSmall (by decide +kernel) (by decide)

def splitV55 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0xa934d34d3980fc003f,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB55 : Ban 36 4 splitV55 := viaSmall (by decide +kernel) (by decide)

def splitV56 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x137df7df75bf03f03f,0x46cb2cb2c64003ffc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB56 : Ban 36 4 splitV56 := viaSmall (by decide +kernel) (by decide)

def splitV57 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x13df7df7d9bffc003f,0x46cb2cb2c64003ffc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB57 : Ban 36 4 splitV57 := viaSmall (by decide +kernel) (by decide)

def splitV58 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0x56db6db6d7ff03ffff,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB58 : Ban 36 4 splitV58 := viaSmall (by decide +kernel) (by decide)

def splitV59 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0xe9a69a69ae40ffffc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB59 : Ban 36 4 splitV59 := viaSmall (by decide +kernel) (by decide)

def splitV60 : List ℕ := [0x37df7df740003f000,0x3fffffffc3ffff000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB60 : Ban 36 4 splitV60 := viaSmall (by decide +kernel) (by decide)

def splitV61 : List ℕ := [0x37df7df740003f000,0x1051451451bf00003f,0x13df7df7d9bffc003f,0x46cb2cb2c64003ffc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB61 : Ban 36 4 splitV61 := viaSmall (by decide +kernel) (by decide)

def splitV62 : List ℕ := [0x37df7df740003f000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xe830c30c37c003ffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB62 : Ban 36 4 splitV62 := viaSmall (by decide +kernel) (by decide)

def splitV63 : List ℕ := [0x37df7df740003f000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xe830c30c37c003ffff,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB63 : Ban 36 4 splitV63 := viaSmall (by decide +kernel) (by decide)

def splitV64 : List ℕ := [0x37df7df740003f000,0x13df7df7d9bffc003f,0x46cb2cb2c64003ffc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB64 : Ban 36 4 splitV64 := viaSmall (by decide +kernel) (by decide)

def splitV65 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xe88208208bc0fc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB65 : Ban 36 4 splitV65 := viaSmall (by decide +kernel) (by decide)

def splitV66 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xe88208208bc0fc0fff,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB66 : Ban 36 4 splitV66 := viaSmall (by decide +kernel) (by decide)

def splitV67 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB67 : Ban 36 5 splitV67 := viaBranch (ws := [splitV40,splitV41,splitV42,splitV43,splitV44,splitV45,splitV46,splitV47,splitV48,splitV49,splitV50,splitV51,splitV52,splitV53,splitV54,splitV55,splitV56,splitV57,splitV58,splitV59,splitV60,splitV61,splitV62,splitV63,splitV64,splitV65,splitV66])
 (consBan splitB40 (consBan splitB41 (consBan splitB42 (consBan splitB43 (consBan splitB44 (consBan splitB45 (consBan splitB46 (consBan splitB47 (consBan splitB48 (consBan splitB49 (consBan splitB50 (consBan splitB51 (consBan splitB52 (consBan splitB53 (consBan splitB54 (consBan splitB55 (consBan splitB56 (consBan splitB57 (consBan splitB58 (consBan splitB59 (consBan splitB60 (consBan splitB61 (consBan splitB62 (consBan splitB63 (consBan splitB64 (consBan splitB65 (consBan splitB66 (nilBan 36 4))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV68 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x47cf3cf3ce7fffffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB68 : Ban 36 5 splitV68 := viaSmall (by decide +kernel) (by decide)

def splitV69 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x47fffffff64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB69 : Ban 36 5 splitV69 := viaSmall (by decide +kernel) (by decide)

def splitV70 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x49a69a69a58003f03f,0x4fefbefbe7c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB70 : Ban 36 5 splitV70 := viaSmall (by decide +kernel) (by decide)

def splitV71 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x49a69a69a58003f03f,0x56db6db6d7ff03ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB71 : Ban 36 5 splitV71 := viaSmall (by decide +kernel) (by decide)

def splitV72 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x49a69a69a58003f03f,0xa030c30c3800fc0000,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB72 : Ban 36 5 splitV72 := viaSmall (by decide +kernel) (by decide)

def splitV73 : List ℕ := [0x2082082240000fc0,0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x4fefbefbe7c003ffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB73 : Ban 36 4 splitV73 := viaSmall (by decide +kernel) (by decide)

def splitV74 : List ℕ := [0x410410418000003f,0x37df7df740003f000,0x38e38e3883ffc0000,0x4fefbefbe7c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB74 : Ban 36 4 splitV74 := viaSmall (by decide +kernel) (by decide)

def splitV75 : List ℕ := [0x71c71c740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x4fefbefbe7c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB75 : Ban 36 4 splitV75 := viaSmall (by decide +kernel) (by decide)

def splitV76 : List ℕ := [0x36db6db640003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x4fefbefbe7c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB76 : Ban 36 4 splitV76 := viaSmall (by decide +kernel) (by decide)

def splitV77 : List ℕ := [0x37df7df740003f000,0x38e38e38800fc0000,0x1051451451bf00003f,0x4fefbefbe7c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB77 : Ban 36 4 splitV77 := viaSmall (by decide +kernel) (by decide)

def splitV78 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1041041041bf00003f,0x4fefbefbe7c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB78 : Ban 36 4 splitV78 := viaSmall (by decide +kernel) (by decide)

def splitV79 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x10514514518000003f,0x4fefbefbe7c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB79 : Ban 36 4 splitV79 := viaSmall (by decide +kernel) (by decide)

def splitV80 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x4c61861867c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB80 : Ban 36 4 splitV80 := viaSmall (by decide +kernel) (by decide)

def splitV81 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x4c82082083c0000fff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB81 : Ban 36 4 splitV81 := viaSmall (by decide +kernel) (by decide)

def splitV82 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x4fcf3cf3c58003f03f,0x4fefbefbe7c003ffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB82 : Ban 36 4 splitV82 := viaSmall (by decide +kernel) (by decide)

def splitV83 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x4fefbefbe7c003ffff,0xa02082082a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB83 : Ban 36 4 splitV83 := viaSmall (by decide +kernel) (by decide)

def splitV84 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x4fefbefbe7c003ffff,0xa030c30c3240000fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB84 : Ban 36 4 splitV84 := viaSmall (by decide +kernel) (by decide)

def splitV85 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x4fefbefbe7c003ffff,0xa3befbefba7ffc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB85 : Ban 36 4 splitV85 := viaSmall (by decide +kernel) (by decide)

def splitV86 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x4fefbefbe7c003ffff,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB86 : Ban 36 4 splitV86 := viaSmall (by decide +kernel) (by decide)

def splitV87 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x4fefbefbefffffffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB87 : Ban 36 4 splitV87 := viaSmall (by decide +kernel) (by decide)

def splitV88 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x4ffffffff7c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB88 : Ban 36 4 splitV88 := viaSmall (by decide +kernel) (by decide)

def splitV89 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x13df7df7d9bffc003f,0x4fefbefbe7c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB89 : Ban 36 4 splitV89 := viaSmall (by decide +kernel) (by decide)

def splitV90 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x4faebaeba64003ffc0,0x4fefbefbe7c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB90 : Ban 36 4 splitV90 := viaSmall (by decide +kernel) (by decide)

def splitV91 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x4fefbefbe7c003ffff,0xa030c30c3a40fc0fc0,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB91 : Ban 36 4 splitV91 := viaSmall (by decide +kernel) (by decide)

def splitV92 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x4fefbefbe7c003ffff,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB92 : Ban 36 4 splitV92 := viaSmall (by decide +kernel) (by decide)

def splitV93 : List ℕ := [0x37df7df740003f000,0x1051451451bf00003f,0x13df7df7d9bffc003f,0x4fefbefbe7c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB93 : Ban 36 4 splitV93 := viaSmall (by decide +kernel) (by decide)

def splitV94 : List ℕ := [0x38e38e3883ffc0000,0x3fffffffc3ffff000,0x1051451451bf00003f,0x4fefbefbe7c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB94 : Ban 36 4 splitV94 := viaSmall (by decide +kernel) (by decide)

def splitV95 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x4c82082083c0000fff,0x4fefbefbe7c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB95 : Ban 36 4 splitV95 := viaSmall (by decide +kernel) (by decide)

def splitV96 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x4c82082083c0000fff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB96 : Ban 36 4 splitV96 := viaSmall (by decide +kernel) (by decide)

def splitV97 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x4fefbefbe7c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB97 : Ban 36 5 splitV97 := viaBranch (ws := [splitV73,splitV74,splitV75,splitV76,splitV77,splitV78,splitV79,splitV80,splitV81,splitV82,splitV83,splitV84,splitV85,splitV86,splitV87,splitV88,splitV89,splitV90,splitV91,splitV92,splitV93,splitV94,splitV95,splitV96])
 (consBan splitB73 (consBan splitB74 (consBan splitB75 (consBan splitB76 (consBan splitB77 (consBan splitB78 (consBan splitB79 (consBan splitB80 (consBan splitB81 (consBan splitB82 (consBan splitB83 (consBan splitB84 (consBan splitB85 (consBan splitB86 (consBan splitB87 (consBan splitB88 (consBan splitB89 (consBan splitB90 (consBan splitB91 (consBan splitB92 (consBan splitB93 (consBan splitB94 (consBan splitB95 (consBan splitB96 (nilBan 36 4)))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV98 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x137df7df75bf03f03f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB98 : Ban 36 5 splitV98 := viaSmall (by decide +kernel) (by decide)

def splitV99 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x13df7df7d9bffc003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB99 : Ban 36 5 splitV99 := viaSmall (by decide +kernel) (by decide)

def splitV100 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0x49a69a69a40003f000,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB100 : Ban 36 5 splitV100 := viaSmall (by decide +kernel) (by decide)

def splitV101 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0x56db6db6d7ff03ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB101 : Ban 36 5 splitV101 := viaSmall (by decide +kernel) (by decide)

def splitV102 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB102 : Ban 36 5 splitV102 := viaSmall (by decide +kernel) (by decide)

def splitV103 : List ℕ := [0x83ffc0000,0x37df7df740003f000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB103 : Ban 36 4 splitV103 := viaSmall (by decide +kernel) (by decide)

def splitV104 : List ℕ := [0x208208218000003f,0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB104 : Ban 36 4 splitV104 := viaSmall (by decide +kernel) (by decide)

def splitV105 : List ℕ := [0x4104104240000fc0,0x37df7df740003f000,0x38e38e3883ffc0000,0x49a69a69a58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB105 : Ban 36 4 splitV105 := viaSmall (by decide +kernel) (by decide)

def splitV106 : List ℕ := [0x71c71c740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB106 : Ban 36 4 splitV106 := viaSmall (by decide +kernel) (by decide)

def splitV107 : List ℕ := [0x820820883ffc0000,0x37df7df740003f000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB107 : Ban 36 4 splitV107 := viaSmall (by decide +kernel) (by decide)

def splitV108 : List ℕ := [0x1041041083ffc0000,0x37df7df740003f000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB108 : Ban 36 4 splitV108 := viaSmall (by decide +kernel) (by decide)

def splitV109 : List ℕ := [0x2082082083ffc0000,0x37df7df740003f000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB109 : Ban 36 4 splitV109 := viaSmall (by decide +kernel) (by decide)

def splitV110 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x64924924240000fc0,0x49a69a69a58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB110 : Ban 36 4 splitV110 := viaSmall (by decide +kernel) (by decide)

def splitV111 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x9249249218000003f,0x46cb2cb2c64003ffc0,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB111 : Ban 36 4 splitV111 := viaSmall (by decide +kernel) (by decide)

def splitV112 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x44410410464003ffc0,0x49a69a69a58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB112 : Ban 36 4 splitV112 := viaSmall (by decide +kernel) (by decide)

def splitV113 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x448208208240000fc0,0x49a69a69a58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB113 : Ban 36 4 splitV113 := viaSmall (by decide +kernel) (by decide)

def splitV114 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0x48208208258003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB114 : Ban 36 4 splitV114 := viaSmall (by decide +kernel) (by decide)

def splitV115 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0x48820820818000003f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB115 : Ban 36 4 splitV115 := viaSmall (by decide +kernel) (by decide)

def splitV116 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xb00000000bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB116 : Ban 36 4 splitV116 := viaSmall (by decide +kernel) (by decide)

def splitV117 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xb071c71c73c0000fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB117 : Ban 36 4 splitV117 := viaSmall (by decide +kernel) (by decide)

def splitV118 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xb37df7df7fffffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB118 : Ban 36 4 splitV118 := viaSmall (by decide +kernel) (by decide)

def splitV119 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xb3fffffffbfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB119 : Ban 36 4 splitV119 := viaSmall (by decide +kernel) (by decide)

def splitV120 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0x4baebaebadbffff03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB120 : Ban 36 4 splitV120 := viaSmall (by decide +kernel) (by decide)

def splitV121 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0x4bfffffff58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB121 : Ban 36 4 splitV121 := viaSmall (by decide +kernel) (by decide)

def splitV122 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0x4fefbefbe7c003ffff,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB122 : Ban 36 4 splitV122 := viaSmall (by decide +kernel) (by decide)

def splitV123 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0xb05145145a7ffc0fc0,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB123 : Ban 36 4 splitV123 := viaSmall (by decide +kernel) (by decide)

def splitV124 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x47cf3cf3ce7fffffc0,0x49a69a69a58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB124 : Ban 36 4 splitV124 := viaSmall (by decide +kernel) (by decide)

def splitV125 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x47fffffff64003ffc0,0x49a69a69a58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB125 : Ban 36 4 splitV125 := viaSmall (by decide +kernel) (by decide)

def splitV126 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x49a69a69a58003f03f,0x4fefbefbe7c003ffff,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB126 : Ban 36 4 splitV126 := viaSmall (by decide +kernel) (by decide)

def splitV127 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x49a69a69a58003f03f,0xb030c30c39bffc003f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB127 : Ban 36 4 splitV127 := viaSmall (by decide +kernel) (by decide)

def splitV128 : List ℕ := [0x37df7df740003f000,0x3fffffffc3ffff000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB128 : Ban 36 4 splitV128 := viaSmall (by decide +kernel) (by decide)

def splitV129 : List ℕ := [0x37df7df740003f000,0x46cb2cb2c64003ffc0,0x47cf3cf3ce7fffffc0,0x49a69a69a58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB129 : Ban 36 4 splitV129 := viaSmall (by decide +kernel) (by decide)

def splitV130 : List ℕ := [0x37df7df740003f000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0x4baebaebadbffff03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB130 : Ban 36 4 splitV130 := viaSmall (by decide +kernel) (by decide)

def splitV131 : List ℕ := [0x37df7df740003f000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xb071c71c73c0000fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB131 : Ban 36 4 splitV131 := viaSmall (by decide +kernel) (by decide)

def splitV132 : List ℕ := [0x37df7df740003f000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xb071c71c73c0000fff,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB132 : Ban 36 4 splitV132 := viaSmall (by decide +kernel) (by decide)

def splitV133 : List ℕ := [0x38e38e3883ffc0000,0x3fffffffc3ffff000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB133 : Ban 36 4 splitV133 := viaSmall (by decide +kernel) (by decide)

def splitV134 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB134 : Ban 36 5 splitV134 := viaBranch (ws := [splitV103,splitV104,splitV105,splitV106,splitV107,splitV108,splitV109,splitV110,splitV111,splitV112,splitV113,splitV114,splitV115,splitV116,splitV117,splitV118,splitV119,splitV120,splitV121,splitV122,splitV123,splitV124,splitV125,splitV126,splitV127,splitV92,splitV128,splitV129,splitV130,splitV131,splitV132,splitV133])
 (consBan splitB103 (consBan splitB104 (consBan splitB105 (consBan splitB106 (consBan splitB107 (consBan splitB108 (consBan splitB109 (consBan splitB110 (consBan splitB111 (consBan splitB112 (consBan splitB113 (consBan splitB114 (consBan splitB115 (consBan splitB116 (consBan splitB117 (consBan splitB118 (consBan splitB119 (consBan splitB120 (consBan splitB121 (consBan splitB122 (consBan splitB123 (consBan splitB124 (consBan splitB125 (consBan splitB126 (consBan splitB127 (consBan splitB92 (consBan splitB128 (consBan splitB129 (consBan splitB130 (consBan splitB131 (consBan splitB132 (consBan splitB133 (nilBan 36 4)))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV135 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x49a69a69a58003f03f,0x56db6db6d7ff03ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB135 : Ban 36 5 splitV135 := viaSmall (by decide +kernel) (by decide)

def splitV136 : List ℕ := [0x37df7df740003f000,0x3fffffffc3ffff000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB136 : Ban 36 5 splitV136 := viaSmall (by decide +kernel) (by decide)

def splitV137 : List ℕ := [0x37df7df740003f000,0x1051451451bf00003f,0x13df7df7d9bffc003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB137 : Ban 36 5 splitV137 := viaSmall (by decide +kernel) (by decide)

def splitV138 : List ℕ := [0x37df7df740003f000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x47cf3cf3ce7fffffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB138 : Ban 36 5 splitV138 := viaSmall (by decide +kernel) (by decide)

def splitV139 : List ℕ := [0x37df7df740003f000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0x4baebaebadbffff03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB139 : Ban 36 5 splitV139 := viaSmall (by decide +kernel) (by decide)

def splitV140 : List ℕ := [0x37df7df740003f000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3240000fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB140 : Ban 36 5 splitV140 := viaSmall (by decide +kernel) (by decide)

def splitV141 : List ℕ := [0x37df7df740003f000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3240000fc0,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB141 : Ban 36 5 splitV141 := viaSmall (by decide +kernel) (by decide)

def splitV142 : List ℕ := [0x37df7df740003f000,0x13df7df7d9bffc003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB142 : Ban 36 5 splitV142 := viaSmall (by decide +kernel) (by decide)

def splitV143 : List ℕ := [0x38e38e3883ffc0000,0x3fffffffc3ffff000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB143 : Ban 36 5 splitV143 := viaSmall (by decide +kernel) (by decide)

def splitV144 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x137df7df75bf03f03f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB144 : Ban 36 5 splitV144 := viaSmall (by decide +kernel) (by decide)

def splitV145 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x448208208240000fc0,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB145 : Ban 36 5 splitV145 := viaSmall (by decide +kernel) (by decide)

def splitV146 : List ℕ := [0x18000003f,0x38e38e3883ffc0000,0x1051451451bf00003f,0x448208208240000fc0,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB146 : Ban 36 4 splitV146 := viaSmall (by decide +kernel) (by decide)

def splitV147 : List ℕ := [0x30c30c3083ffc0000,0x1051451451bf00003f,0x448208208240000fc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB147 : Ban 36 4 splitV147 := viaSmall (by decide +kernel) (by decide)

def splitV148 : List ℕ := [0x38e38e3883ffc0000,0x9249249258003f03f,0x1051451451bf00003f,0x448208208240000fc0,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB148 : Ban 36 4 splitV148 := viaSmall (by decide +kernel) (by decide)

def splitV149 : List ℕ := [0x38e38e3883ffc0000,0x1041041041bf00003f,0x448208208240000fc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB149 : Ban 36 4 splitV149 := viaSmall (by decide +kernel) (by decide)

def splitV150 : List ℕ := [0x38e38e3883ffc0000,0x10514514503f000000,0x1051451451bf00003f,0x448208208240000fc0,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB150 : Ban 36 4 splitV150 := viaSmall (by decide +kernel) (by decide)

def splitV151 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x440000000240000fc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB151 : Ban 36 4 splitV151 := viaSmall (by decide +kernel) (by decide)

def splitV152 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x448208208240000fc0,0x48208208258003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB152 : Ban 36 4 splitV152 := viaSmall (by decide +kernel) (by decide)

def splitV153 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x448208208240000fc0,0x49861861858003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB153 : Ban 36 4 splitV153 := viaSmall (by decide +kernel) (by decide)

def splitV154 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x448208208240000fc0,0x49a69a69a58003f03f,0xa02082082a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB154 : Ban 36 4 splitV154 := viaSmall (by decide +kernel) (by decide)

def splitV155 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x448208208240000fc0,0x49a69a69a58003f03f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB155 : Ban 36 4 splitV155 := viaSmall (by decide +kernel) (by decide)

def splitV156 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x448208208240000fc0,0x4baebaebadbffff03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB156 : Ban 36 4 splitV156 := viaSmall (by decide +kernel) (by decide)

def splitV157 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x448208208240000fc0,0x4da69a69a7c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB157 : Ban 36 4 splitV157 := viaSmall (by decide +kernel) (by decide)

def splitV158 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x448208208240000fc0,0xa030c30c3a40fc0fc0,0xe9b6db6dbfc0ffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB158 : Ban 36 4 splitV158 := viaSmall (by decide +kernel) (by decide)

def splitV159 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x478e38e38a7ffc0fc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB159 : Ban 36 4 splitV159 := viaSmall (by decide +kernel) (by decide)

def splitV160 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x49a69a69a58003f03f,0x54d34d34d3ff000fff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB160 : Ban 36 4 splitV160 := viaSmall (by decide +kernel) (by decide)

def splitV161 : List ℕ := [0x38e38e3883ffc0000,0x448208208240000fc0,0x49a69a69a58003f03f,0x54d34d34d3ff000fff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB161 : Ban 36 4 splitV161 := viaSmall (by decide +kernel) (by decide)

def splitV162 : List ℕ := [0x38e38e3883ffc0000,0x448208208240000fc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB162 : Ban 36 4 splitV162 := viaSmall (by decide +kernel) (by decide)

def splitV163 : List ℕ := [0x1051451451bf00003f,0x448208208240000fc0,0x478e38e38a7ffc0fc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB163 : Ban 36 4 splitV163 := viaSmall (by decide +kernel) (by decide)

def splitV164 : List ℕ := [0x1051451451bf00003f,0x478e38e38a7ffc0fc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB164 : Ban 36 4 splitV164 := viaSmall (by decide +kernel) (by decide)

def splitV165 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x448208208240000fc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB165 : Ban 36 5 splitV165 := viaBranch (ws := [splitV146,splitV147,splitV148,splitV149,splitV150,splitV151,splitV152,splitV153,splitV154,splitV155,splitV156,splitV157,splitV158,splitV159,splitV160,splitV161,splitV162,splitV163,splitV164])
 (consBan splitB146 (consBan splitB147 (consBan splitB148 (consBan splitB149 (consBan splitB150 (consBan splitB151 (consBan splitB152 (consBan splitB153 (consBan splitB154 (consBan splitB155 (consBan splitB156 (consBan splitB157 (consBan splitB158 (consBan splitB159 (consBan splitB160 (consBan splitB161 (consBan splitB162 (consBan splitB163 (consBan splitB164 (nilBan 36 4))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV166 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x48820820818000003f,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB166 : Ban 36 5 splitV166 := viaSmall (by decide +kernel) (by decide)

def splitV167 : List ℕ := [0x240000fc0,0x38e38e3883ffc0000,0x1051451451bf00003f,0x48820820818000003f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB167 : Ban 36 4 splitV167 := viaSmall (by decide +kernel) (by decide)

def splitV168 : List ℕ := [0x30c30c3083ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x48820820818000003f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB168 : Ban 36 4 splitV168 := viaSmall (by decide +kernel) (by decide)

def splitV169 : List ℕ := [0x38e38e38800fc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x48820820818000003f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB169 : Ban 36 4 splitV169 := viaSmall (by decide +kernel) (by decide)

def splitV170 : List ℕ := [0x38e38e3883ffc0000,0x6492492464003ffc0,0x1051451451bf00003f,0x48820820818000003f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB170 : Ban 36 4 splitV170 := viaSmall (by decide +kernel) (by decide)

def splitV171 : List ℕ := [0x38e38e3883ffc0000,0x1041041041bf00003f,0x46cb2cb2c64003ffc0,0x48820820818000003f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB171 : Ban 36 4 splitV171 := viaSmall (by decide +kernel) (by decide)

def splitV172 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x44410410464003ffc0,0x48820820818000003f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB172 : Ban 36 4 splitV172 := viaSmall (by decide +kernel) (by decide)

def splitV173 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x468a28a2864003ffc0,0x48820820818000003f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB173 : Ban 36 4 splitV173 := viaSmall (by decide +kernel) (by decide)

def splitV174 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x48000000018000003f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB174 : Ban 36 4 splitV174 := viaSmall (by decide +kernel) (by decide)

def splitV175 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x48820820818000003f,0xa02082082a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB175 : Ban 36 4 splitV175 := viaSmall (by decide +kernel) (by decide)

def splitV176 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x48820820818000003f,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB176 : Ban 36 4 splitV176 := viaSmall (by decide +kernel) (by decide)

def splitV177 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x48820820818000003f,0xe8b2cb2cbbc0fc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB177 : Ban 36 4 splitV177 := viaSmall (by decide +kernel) (by decide)

def splitV178 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x4b8e38e389bffc003f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB178 : Ban 36 4 splitV178 := viaSmall (by decide +kernel) (by decide)

def splitV179 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0xa030c30c3a40fc0fc0,0xe8b2cb2cbbc0fc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB179 : Ban 36 4 splitV179 := viaSmall (by decide +kernel) (by decide)

def splitV180 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x47cf3cf3ce7fffffc0,0x48820820818000003f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB180 : Ban 36 4 splitV180 := viaSmall (by decide +kernel) (by decide)

def splitV181 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x48820820818000003f,0x4ecb2cb2c7c003ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB181 : Ban 36 4 splitV181 := viaSmall (by decide +kernel) (by decide)

def splitV182 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x48820820818000003f,0x56db6db6d7ff03ffff,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB182 : Ban 36 4 splitV182 := viaSmall (by decide +kernel) (by decide)

def splitV183 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x48820820818000003f,0xa030c30c3800fc0000,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB183 : Ban 36 4 splitV183 := viaSmall (by decide +kernel) (by decide)

def splitV184 : List ℕ := [0x38e38e3883ffc0000,0x46cb2cb2c64003ffc0,0x48820820818000003f,0xa030c30c3a40fc0fc0,0xb071c71c7bfffc0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB184 : Ban 36 4 splitV184 := viaSmall (by decide +kernel) (by decide)

def splitV185 : List ℕ := [0x1051451451bf00003f,0x13df7df7d9bffc003f,0x46cb2cb2c64003ffc0,0x48820820818000003f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB185 : Ban 36 4 splitV185 := viaSmall (by decide +kernel) (by decide)

def splitV186 : List ℕ := [0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x48820820818000003f,0x4b8e38e389bffc003f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB186 : Ban 36 4 splitV186 := viaSmall (by decide +kernel) (by decide)

def splitV187 : List ℕ := [0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x4b8e38e389bffc003f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB187 : Ban 36 4 splitV187 := viaSmall (by decide +kernel) (by decide)

def splitV188 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x48820820818000003f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB188 : Ban 36 5 splitV188 := viaBranch (ws := [splitV167,splitV168,splitV169,splitV170,splitV171,splitV172,splitV173,splitV174,splitV175,splitV176,splitV177,splitV178,splitV179,splitV180,splitV181,splitV182,splitV183,splitV184,splitV185,splitV186,splitV187])
 (consBan splitB167 (consBan splitB168 (consBan splitB169 (consBan splitB170 (consBan splitB171 (consBan splitB172 (consBan splitB173 (consBan splitB174 (consBan splitB175 (consBan splitB176 (consBan splitB177 (consBan splitB178 (consBan splitB179 (consBan splitB180 (consBan splitB181 (consBan splitB182 (consBan splitB183 (consBan splitB184 (consBan splitB185 (consBan splitB186 (consBan splitB187 (nilBan 36 4))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV189 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0,0xa37df7df7e40ffffc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB189 : Ban 36 5 splitV189 := viaSmall (by decide +kernel) (by decide)

def splitV190 : List ℕ := [0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa37df7df7e40ffffc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB190 : Ban 36 5 splitV190 := viaSmall (by decide +kernel) (by decide)

def splitV191 : List ℕ := [0x38e38e3883ffc0000,0x137df7df75bf03f03f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB191 : Ban 36 5 splitV191 := viaSmall (by decide +kernel) (by decide)

def splitV192 : List ℕ := [0x37df7df740003f000,0x38e38e3883ffc0000,0x1051451451bf00003f,0x46cb2cb2c64003ffc0,0x49a69a69a58003f03f,0xa030c30c3a40fc0fc0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB192 : Ban 36 6 splitV192 := viaBranch (ws := [splitV0,splitV1,splitV2,splitV3,splitV4,splitV5,splitV6,splitV7,splitV8,splitV9,splitV10,splitV11,splitV12,splitV13,splitV14,splitV15,splitV16,splitV17,splitV18,splitV19,splitV20,splitV21,splitV22,splitV23,splitV24,splitV25,splitV26,splitV27,splitV28,splitV29,splitV30,splitV31,splitV32,splitV33,splitV34,splitV35,splitV36,splitV37,splitV38,splitV39,splitV67,splitV68,splitV69,splitV70,splitV71,splitV72,splitV97,splitV98,splitV99,splitV100,splitV101,splitV102,splitV134,splitV135,splitV136,splitV137,splitV138,splitV139,splitV140,splitV141,splitV142,splitV143,splitV144,splitV145,splitV165,splitV166,splitV188,splitV189,splitV190,splitV191])
 (consBan splitB0 (consBan splitB1 (consBan splitB2 (consBan splitB3 (consBan splitB4 (consBan splitB5 (consBan splitB6 (consBan splitB7 (consBan splitB8 (consBan splitB9 (consBan splitB10 (consBan splitB11 (consBan splitB12 (consBan splitB13 (consBan splitB14 (consBan splitB15 (consBan splitB16 (consBan splitB17 (consBan splitB18 (consBan splitB19 (consBan splitB20 (consBan splitB21 (consBan splitB22 (consBan splitB23 (consBan splitB24 (consBan splitB25 (consBan splitB26 (consBan splitB27 (consBan splitB28 (consBan splitB29 (consBan splitB30 (consBan splitB31 (consBan splitB32 (consBan splitB33 (consBan splitB34 (consBan splitB35 (consBan splitB36 (consBan splitB37 (consBan splitB38 (consBan splitB39 (consBan splitB67 (consBan splitB68 (consBan splitB69 (consBan splitB70 (consBan splitB71 (consBan splitB72 (consBan splitB97 (consBan splitB98 (consBan splitB99 (consBan splitB100 (consBan splitB101 (consBan splitB102 (consBan splitB134 (consBan splitB135 (consBan splitB136 (consBan splitB137 (consBan splitB138 (consBan splitB139 (consBan splitB140 (consBan splitB141 (consBan splitB142 (consBan splitB143 (consBan splitB144 (consBan splitB145 (consBan splitB165 (consBan splitB166 (consBan splitB188 (consBan splitB189 (consBan splitB190 (consBan splitB191 (nilBan 36 5)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

theorem restrictedBound : Wide 36 6 restrictedInputs := by
  have ess : ∀ a∈splitV192, ∃ i : Fin 36, ∀ b∈splitV192, b.testBit i.val≠b.testBit (36+i.val) → b=a := by decide +kernel
  have w := widen ess splitB192
  exact w

def caseInputs : List ℕ := [12278377730058152027361216, 1228190076536882460622911, 5527117698108865772777535, 5221513124287825813176256, 4122700895020468400128, 4197659094209210875904]
def projectRows : Projection 42 36 := pick [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35] rfl (by decide +kernel) (by decide)
theorem caseBound : Ban 42 6 caseInputs := viaCut projectRows restrictedBound (by decide) (by decide +kernel) (by decide +kernel)
def graph (x : Fin 6 → Bool) := Nat.testBit (4277071598 * 2 ^ 32 + 4206947008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def posBits : ℕ := 0x85c24618985c2461898a28a28a286186186171c71c71c249249249186186186
def negBits : ℕ := 0x4c04210804c042108e34b1a553e34b1a553e34b1a553e34b1a553e34b1a553
def sample (bank : ℕ) (i : Fin 42) (j : Fin 6) := bank.testBit (6*i.val+j.val)
def inputs : List ℕ := caseInputs
def seeds : List Wire := [(false,12278377730058152027361216),(false,1228190076536882460622911),(false,5527117698108865772777535),(false,5221513124287825813176256),(false,4122700895020468400128),(false,4197659094209210875904)]
set_option maxHeartbeats 1000000 in
theorem listed : ∀ i : Fin 42, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (42+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 42, graph (sample posBits i)=true ∧ graph (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 42, ∀ b∈inputs, b.testBit i.val≠b.testBit (42+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 42 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 6 C=graph) :
    ∃ k≤C.gates.countP counted, Live 42 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 6 → Bool) : C.eval (List.ofFn x)=graph x := congrFun eq x
  have good : Good 42 out.2 := by
    intro i hi same
    let j : Fin 42 := ⟨i,hi⟩
    have diff : read i out=read (42+i) out := by simp [read,same]
    have p := ev i;have n := ev (42+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa only [show reps seeds = inputs from rfl] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩


def witness : List Gate := [⟨.or,[3,5]⟩, ⟨.or,[2,5]⟩, ⟨.and,[0,6]⟩, ⟨.and,[1,7]⟩, ⟨.or,[8,9]⟩, ⟨.and,[2,3]⟩, ⟨.and,[4,11]⟩, ⟨.or,[10,12]⟩]
theorem upperMono : Monotone2 ⟨witness,13⟩ := by simp [Monotone2,witness]
theorem upperEq : ∀ x : Fin 6 → Bool, Circuit.eval ⟨witness,13⟩ (List.ofFn x)=graph x := by decide +kernel
end PEqualNP.Outside.L_meta_13713
open PEqualNP.Outside.L_meta_13713 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_13713 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071598 * 2 ^ 32 + 4206947008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071598 * 2 ^ 32 + 4206947008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨C,fan,size,eq⟩
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨k,small,live⟩ := trace C fan (funext eq)
    have lower : 7 ≤ k := by
      by_contra! h
      exact caseBound k (by omega) live
    have strict : C.gates.countP counted < C.gates.length := by
      apply List.countP_lt_length_iff.mpr
      obtain ⟨g,mem,op⟩ := hn
      exact ⟨g,mem,by simp [counted,op]⟩
    change C.gates.length ≤ s at size
    exact ⟨⟨witness,13⟩,upperMono,by change 8 ≤ s; omega,upperEq⟩
  · refine ⟨C, ?_, size, eq⟩
    intro g mem
    obtain ⟨op,cap⟩ := fan g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun e => (hn ⟨g,mem,e⟩).elim)), cap⟩
