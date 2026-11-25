import PEqualNP.Defs

-- The signed live-wire calculus follows L-meta-10532. Pinning input 5 in either
-- direction leaves a five-input restriction that needs nine binary gates.
-- The two certificates below cover both restrictions.


namespace PEqualNP.Outside.L_meta_12092

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

end PEqualNP.Outside.L_meta_12092

namespace PEqualNP.Outside.L_meta_12092

def opB (d : ℕ) (a b : Bool) : Bool :=
  match d with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => b && !a
theorem combineBit (d a b i : ℕ) (hd : d<4) :
    (combine d a b).testBit i = opB d (a.testBit i) (b.testBit i) := by
  interval_cases d <;> cases ha : a.testBit i <;> cases hb : b.testBit i <;>
    simp [combine,opB,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,ha,hb]
def remap (d : ℕ) (s t : Bool) : ℕ :=
  let f := fun x y => opB d s t != opB d (s != x) (t != y)
  if f true false then (if f false true then 1 else 2) else (if f false true then 3 else 0)
theorem remapRule (d : ℕ) (hd : d<4) (s t x y : Bool) :
    remap d s t < 4 ∧
    (opB d s t != opB d x y) = opB (remap d s t) (s != x) (t != y) := by
  interval_cases d <;> cases s <;> cases t <;> cases x <;> cases y <;> decide

def signedBits (origin : ℕ) (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | i::is => Nat.bit (w.testBit origin != w.testBit i) (signedBits origin w is)
theorem signedBit (origin w : ℕ) (is : List ℕ) (k : ℕ) :
    (signedBits origin w is).testBit k =
      (is[k]?.map (fun i => w.testBit origin != w.testBit i)).getD false := by
  induction is generalizing k with
  | nil => simp [signedBits]
  | cons i is ih =>
    cases k with
    | zero => cases ha : w.testBit origin <;> cases hb : w.testBit i <;> simp [signedBits,ha,hb]
    | succ k => simp [signedBits,Nat.testBit_bit_succ,ih]

structure Weak (m h : ℕ) where
  f : ℕ → ℕ
  good : ∀ w, Good m w → Good h (f w)
  pos : 0<h
  maps : ∀ d a b, d<4 → ∃ e, e<4 ∧ f (combine d a b)=combine e (f a) (f b)

def signedPick {m h : ℕ} (origin : ℕ) (r : List ℕ) (len : r.length=h)
    (small : ∀ i∈r,i<m) (pos : 0<h) : Weak m h := by
  let is := r ++ r.map (m+·)
  refine ⟨fun w => signedBits origin w is, ?_, pos, ?_⟩
  · intro a ha i hi
    have ir : i<r.length := by omega
    have diff := ha r[i] (small _ (List.getElem_mem ir))
    have H₁ : is[i]? = some r[i] := by simp [is,List.getElem?_append,ir]
    have H₂ : is[h+i]? = some (m+r[i]) := by
      have ne : ¬h+i<r.length := by omega
      have sub : h+i-r.length=i := by omega
      simp [is,List.getElem?_append,ne,sub,ir]
    simp only [signedBit,H₁,H₂,Option.map_some,Option.getD_some]
    cases a.testBit origin <;> simpa using diff
  · intro d a b hd
    let e := remap d (a.testBit origin) (b.testBit origin)
    have he : e<4 := (remapRule d hd _ _ false false).1
    refine ⟨e,he,Nat.eq_of_testBit_eq ?_⟩
    intro i
    rw [combineBit _ _ _ _ he]
    simp only [signedBit]
    cases hi : is[i]? with
    | none => interval_cases e <;> rfl
    | some j =>
      simp only [Option.map_some,Option.getD_some,combineBit _ _ _ _ hd]
      exact (remapRule d hd _ _ _ _).2

end PEqualNP.Outside.L_meta_12092

namespace PEqualNP.Outside.L_meta_12092
lemma weakCharge {m h d a b : ℕ} (p : Weak m h) (hd : d<4) (U : Finset ℕ)
    (fz : combine d a b∉insert a (insert b U)) (av : List ℕ) (ma : p.f a∈av) (mb : p.f b∈av) :
    (charge av (p.f (combine d a b))).toNat + dead p.f (insert a (insert b U)) ≤
      1+dead p.f (insert (combine d a b) U) := by
  obtain ⟨e,he,eq⟩ := p.maps d a b hd
  have up := deadMono p.f (combine d a b) U
  have la := deadLimit p.f a (insert b U)
  have lb := deadLimit p.f b U
  have free (bad : p.f a=0 ∨ p.f b=0) : charge av (p.f (combine d a b))=false := by
    rw [eq]
    rcases combine_eq_cases _ _ _ he (bad.imp_right Or.inl) with e|e|e <;> simp [charge,e,ma,mb]
  by_cases az : p.f a=0
  · rw [free (Or.inl az)];simp only [Bool.toNat_false,Nat.zero_add]
    by_cases bz : p.f b=0
    · have zz : p.f (combine d a b)=0 := by
        rw [eq,az,bz];interval_cases e <;> decide
      have fresh : combine d a b∉U := fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
      rw [deadGrow zz fresh];omega
    · rw [deadStay bz] at la;omega
  · rw [deadStay az]
    by_cases bz : p.f b=0
    · rw [free (Or.inr bz)];simp only [Bool.toNat_false,Nat.zero_add];omega
    · rw [deadStay bz];cases charge av (p.f (combine d a b)) <;> simp [Bool.toNat] <;> omega

theorem weakLive {m h k S} (p : Weak m h) (live : Live m k S) :
    ∃ j T,j+dead p.f S≤k ∧ Live h j T ∧ ∀ x∈T,x∈S.image p.f := by
  induction k generalizing S with
  | zero =>
    rw [Live] at live
    obtain ⟨a, rfl, hg, _⟩ := live
    have gp := p.good a hg
    have nz : p.f a≠0 := by intro e;have x := gp 0 p.pos;simp [e] at x
    exact ⟨0,{p.f a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | succ k ih =>
    rw [Live] at live
    obtain ⟨U, a, b, d, rfl, hd, ha, hb, ab, fz, tail⟩ := live
    obtain ⟨j,T,cost,ok,raw⟩ := ih tail
    obtain ⟨e,he,eq⟩ := p.maps d a b hd
    let av := ((insert a (insert b U)).image p.f).toList
    have ma : p.f a∈av := by simp [av]
    have mb : p.f b∈av := by simp [av]
    have later : Possible h j (av++[combine e (p.f a) (p.f b)]) := by
      refine ⟨j,T,le_rfl,ok,?_⟩
      intro z hz
      have has := raw _ hz
      simp only [Finset.image_insert,Finset.mem_insert] at has
      rcases has with rfl|old
      · simp [eq]
      · have inav : z∈av := by simpa [av] using (Or.inr (Or.inr old) : z=p.f a ∨ z=p.f b ∨ z∈U.image p.f)
        simp [inav]
    obtain ⟨l,V,lim,good,sub⟩ := pullPaid he ma mb later
    rw [←eq] at lim
    have bound := weakCharge p hd U fz av ma mb
    exact ⟨l,V,by omega,good,by simpa [av] using sub⟩







end PEqualNP.Outside.L_meta_12092

namespace PEqualNP.Outside.L_meta_12092

theorem forced (d : ℕ) (hd : d<4) (left : Bool) :
    ∃ s c : Bool, ∀ y : Bool, (if left then opB d s y else opB d y s)=c := by
  interval_cases d <;> cases left <;> decide

theorem signedZero {o w : ℕ} {is : List ℕ} (same : ∀ i∈is, w.testBit i = w.testBit o) :
    signedBits o w is=0 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    have hi := same i (by simp)
    have ht := ih (fun j hj => same j (by simp [hj]))
    simp [signedBits,hi,ht]

theorem forcedLeft {o v b d : ℕ} {is : List ℕ} {s c : Bool} (hd : d<4)
    (base : v.testBit o=s) (constant : ∀ i∈is, v.testBit i=s)
    (force : ∀ y, opB d s y=c) : signedBits o (combine d v b) is=0 := by
  apply signedZero
  intro i hi
  simp [combineBit _ _ _ _ hd,base,constant i hi,force]

theorem forcedRight {o v a d : ℕ} {is : List ℕ} {s c : Bool} (hd : d<4)
    (base : v.testBit o=s) (constant : ∀ i∈is, v.testBit i=s)
    (force : ∀ y, opB d y s=c) : signedBits o (combine d a v) is=0 := by
  apply signedZero
  intro i hi
  simp [combineBit _ _ _ _ hd,base,constant i hi,force]
end PEqualNP.Outside.L_meta_12092

namespace PEqualNP.Outside.L_meta_12092

theorem doubleElim {m h k S} (p : Bool → Weak m h) (v : ℕ)
    (killed : ∀ d a b, d<4 → (v=a ∨ v=b) → ∃ t, (p t).f (combine d a b)=0)
    (fixed : ∀ t, (p t).f v=0)
    (live : Live m k S) (hv : v∈S) :
    ∃ t j T, j+2≤k ∧ Live h j T ∧ ∀ x∈T,x∈S.image (p t).f := by
  induction k generalizing S with
  | zero =>
    rw [Live] at live
    obtain ⟨a,rfl,good,_⟩ := live
    have ev : v=a := by simpa using hv
    have bad := (p false).good a good 0 (p false).pos
    rw [←ev,fixed] at bad
    simp at bad
  | succ k ih =>
    rw [Live] at live
    obtain ⟨U,a,b,d,rfl,hd,_,_,_,_,tail⟩ := live
    by_cases hit : v=a ∨ v=b
    · obtain ⟨t,van⟩ := killed d a b hd hit
      obtain ⟨j,T,cost,ok,sub⟩ := weakLive (p t) tail
      have one : 0<dead (p t).f (insert (combine d a b) U) :=
        Finset.card_pos.mpr ⟨combine d a b,Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _,van⟩⟩
      refine ⟨t,j,T,by omega,ok,?_⟩
      intro x hx
      have mem := sub x hx
      rw [Finset.image_insert] at mem
      rcases Finset.mem_insert.mp mem with eq|mem
      · exact False.elim (liveNonzero ok x hx (eq.trans van))
      · simp [mem]
    · have vu : v∈U := by simpa [Finset.mem_insert,not_or.mp hit |>.1,not_or.mp hit |>.2] using hv
      obtain ⟨t,j,T,cost,ok,sub⟩ := ih tail (Finset.mem_insert_of_mem vu)
      let q := p t
      obtain ⟨e,he,eq⟩ := q.maps d a b hd
      let av := ((insert a (insert b U)).image q.f).toList
      have ma : q.f a∈av := by simp [av]
      have mb : q.f b∈av := by simp [av]
      have later : Possible h j (av++[combine e (q.f a) (q.f b)]) := by
        refine ⟨j,T,le_rfl,ok,?_⟩
        intro z hz
        have mem := sub z hz
        change z ∈ (insert (combine d a b) U).image q.f at mem
        rw [Finset.image_insert] at mem
        rcases Finset.mem_insert.mp mem with rfl|mem
        · simp [eq]
        · have inav : z∈av := by simp [av,mem]
          simp [inav]
      obtain ⟨l,V,lim,ok',sub'⟩ := pullPaid he ma mb later
      have cap : (charge av (combine e (q.f a) (q.f b))).toNat≤1 := by cases charge av _ <;> decide
      exact ⟨t,l,V,by omega,ok',by simpa [av,q] using sub'⟩
end PEqualNP.Outside.L_meta_12092

namespace PEqualNP.Outside.L_meta_12092
theorem viaWeakCut {m h f t : ℕ} {v w : List ℕ} (p : Weak m h)
    (bound : Wide h t w) (nd : v.Nodup)
    (mem : ∀ a∈v, p.f a=0 ∨ p.f a∈w)
    (cost : f≤t+(v.map p.f).count 0) : Ban m f v := by
  intro k lim run
  obtain ⟨j,T,c,ok,incl⟩ := weakLive p run
  have fixed : dead p.f v.toFinset=(v.map p.f).count 0 := by
    dsimp [dead]
    have E : v.toFinset.filter (fun x => p.f x=0) = (v.filter (fun x => decide (p.f x=0))).toFinset := by ext x;simp
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

end PEqualNP.Outside.L_meta_12092

namespace PEqualNP.Outside.L_meta_12092

abbrev Rule (m k : ℕ) := { test : List ℕ → Bool // ∀ v, v.Nodup → test v=true → Ban m k v }

def relaxed {m h} (p : Projection m h) : Weak m h :=
  ⟨p.val,p.property.2.2.1,p.property.2.2.2,fun d a b hd => ⟨d,hd,p.property.2.1 d a b hd⟩⟩

def cutRule {m h bound : ℕ} (k : ℕ) (p : Weak m h) {w : List ℕ} (lo : Wide h bound w) : Rule m k :=
  ⟨fun v => decide (k ≤ bound+(v.map p.f).count 0) && v.all (fun x => p.f x == 0 || w.contains (p.f x)), by
    intro v nd ok
    simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at ok
    exact viaWeakCut p lo nd ok.2 ok.1⟩

def fingerprint (v : List ℕ) : ℕ :=
  (v.map (fun x => ((x ^^^ (x >>> 23)) * (x+17)) % 2147483647)).sum % 2147483647

def dictionary {m k} (entries : List (ℕ × Rule m k)) : Rule m k :=
  ⟨fun v => entries.any (fun e => e.1 == fingerprint v && e.2.val v), by
    intro v nd yes
    obtain ⟨e,_,ok⟩ := List.any_eq_true.mp yes
    simp only [Bool.and_eq_true] at ok
    exact e.2.property v nd ok.2⟩

theorem viaRules {m f : ℕ} {v : List ℕ} {ws : List (List ℕ)} (closed : banList m f ws)
    (cuts : Rule m f) (nd : v.Nodup) (no : terminal m v=false)
    (test : anyGate m f (fun u => (!ws.contains (ordered u)) && (!cuts.val u) && search m f u) v=false) :
    Ban m (f+1) v := by
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
    have yes := @transition m f n U a b d v (fun u => (!ws.contains (ordered u)) && (!cuts.val u) && search m f u)
      hd ab fr rep nd (by omega) tail (by
      intro u hu nu
      simp only [Bool.and_eq_true]
      refine ⟨⟨?_,?_⟩,complete m f tail (by omega) u hu nu⟩
      · simp
        intro found
        have hv := closed _ found n (by omega)
        rw [ord_eq,hu] at hv
        exact hv tail
      · cases eq : cuts.val u with
        | false => rfl
        | true =>
          have bad := cuts.property u nu eq n (by omega)
          rw [hu] at bad
          exact False.elim (bad tail))
    simp_all
end PEqualNP.Outside.L_meta_12092

namespace PEqualNP.Outside.L_meta_12092.B0
def f0 : ℕ := 0xa3c
def f1 : ℕ := 0xb4c
def f2 : ℕ := 0xeb0
def s0 : List ℕ := [f0,f1,f2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w0 : Wide 6 3 s0 := viaSearch (by decide +kernel)
def p0 : Weak 28 6 := signedPick 0 [0,1,4,5,14,15] (by decide) (by decide) (by decide)
def r0 : Rule 28 6 := cutRule 6 p0 w0
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w1 : Wide 6 2 s0 := viaSearch (by decide +kernel)
def r1 : Rule 28 6 := cutRule 6 p0 w1
def f3 : ℕ := 0xa87f8
def f4 : ℕ := 0xbc878
def f5 : ℕ := 0x1ed398
def f6 : ℕ := 0x2fa5e0
def s1 : List ℕ := [f3,f4,f5,f6]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w2 : Wide 11 4 s1 := viaSearch (by decide +kernel)
def p1 : Weak 28 11 := signedPick 5 [5,6,7,9,10,12,13,17,18,20,22] (by decide) (by decide) (by decide)
def r2 : Rule 28 6 := cutRule 6 p1 w2
def f7 : ℕ := 0x250ff8
def f8 : ℕ := 0x2f90f8
def f9 : ℕ := 0x75a718
def f10 : ℕ := 0xb74b60
def s2 : List ℕ := [f7,f8,f9,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w3 : Wide 12 4 s2 := viaSearch (by decide +kernel)
def p2 : Weak 28 12 := signedPick 1 [1,2,3,8,10,11,13,14,16,18,19,21] (by decide) (by decide) (by decide)
def r3 : Rule 28 6 := cutRule 6 p2 w3
def f11 : ℕ := 0x121f8
def f12 : ℕ := 0x1e4e0
def f13 : ℕ := 0x37b38
def s3 : List ℕ := [f11,f12,f13]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w4 : Wide 9 3 s3 := viaSearch (by decide +kernel)
def p3 : Weak 28 9 := signedPick 0 [0,1,3,4,5,11,14,15,21] (by decide) (by decide) (by decide)
def r4 : Rule 28 5 := cutRule 5 p3 w4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w5 : Wide 12 3 s2 := viaSearch (by decide +kernel)
def r5 : Rule 28 5 := cutRule 5 p2 w5
def f14 : ℕ := 0x50f8
def f15 : ℕ := 0x5918
def f16 : ℕ := 0x7260
def f17 : ℕ := 0xfef8
def s4 : List ℕ := [f14,f15,f16,f17]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w6 : Wide 8 3 s4 := viaSearch (by decide +kernel)
def p4 : Weak 28 8 := signedPick 5 [5,6,7,12,13,17,18,22] (by decide) (by decide) (by decide)
def r6 : Rule 28 5 := cutRule 5 p4 w6
def r7 : Rule 28 5 := cutRule 5 p0 w0
def p5 : Weak 28 6 := signedPick 0 [0,3,4,7,21,22] (by decide) (by decide) (by decide)
def r8 : Rule 28 5 := cutRule 5 p5 w1
def f18 : ℕ := 0xc033f80c0ff
def f19 : ℕ := 0x84106f98c70f
def f20 : ℕ := 0x2d6d0efffff0f
def f21 : ℕ := 0x56b6e007ffff0
def f22 : ℕ := 0x60d8bbfe0f8ff
def f23 : ℕ := 0x7b00ddfff00ff
def s5 : List ℕ := [f18,f19,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b2 : Ban 28 6 s5 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1272664622,r4),(736059706,r5),(1889561442,r6),(2146827602,r7),(1136900608,r8),(91049472,r7)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p6 : Weak 28 11 := signedPick 1 [1,2,3,8,10,11,13,16,18,19,21] (by decide) (by decide) (by decide)
def r9 : Rule 28 6 := cutRule 6 p6 w2
def p7 : Weak 28 12 := signedPick 5 [5,6,7,9,10,12,13,15,17,18,20,22] (by decide) (by decide) (by decide)
def r10 : Rule 28 6 := cutRule 6 p7 w3
def f24 : ℕ := 0x110dc
def f25 : ℕ := 0x1d4e0
def f26 : ℕ := 0x37a1c
def s6 : List ℕ := [f24,f25,f26]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w7 : Wide 9 3 s6 := viaSearch (by decide +kernel)
def p8 : Weak 28 9 := signedPick 0 [0,1,4,5,7,12,14,15,22] (by decide) (by decide) (by decide)
def r11 : Rule 28 5 := cutRule 5 p8 w7
def r12 : Rule 28 5 := cutRule 5 p7 w5
def p9 : Weak 28 8 := signedPick 1 [1,2,3,11,13,16,18,21] (by decide) (by decide) (by decide)
def r13 : Rule 28 5 := cutRule 5 p9 w6
def f27 : ℕ := 0x108260018c7f0
def s7 : List ℕ := [f18,f27,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b3 : Ban 28 6 s7 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1762088895,r11),(1276181981,r12),(1616930924,r13),(329608094,r7),(745401332,r8),(2016600603,r7)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r14 : Rule 28 5 := cutRule 5 p0 w1
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w8 : Wide 11 3 s1 := viaSearch (by decide +kernel)
def r15 : Rule 28 5 := cutRule 5 p1 w8
def r16 : Rule 28 5 := cutRule 5 p6 w8
def f28 : ℕ := 0x21201fffc0
def f29 : ℕ := 0x27f9203fc0
def f30 : ℕ := 0xf93a47c1c0
def f31 : ℕ := 0x339e499ce00
def f32 : ℕ := 0x3f9fedfcfc0
def s8 : List ℕ := [f28,f29,f30,f31,f32]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w9 : Wide 21 4 s8 := viaSearch (by decide +kernel)
def p10 : Weak 28 21 := signedPick 1 [1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22] (by decide) (by decide) (by decide)
def r17 : Rule 28 5 := cutRule 5 p10 w9
def f33 : ℕ := 0x7460
def s9 : List ℕ := [f14,f15,f33,f17]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w10 : Wide 8 3 s9 := viaSearch (by decide +kernel)
def p11 : Weak 28 8 := signedPick 5 [5,6,7,9,10,17,18,20] (by decide) (by decide) (by decide)
def r18 : Rule 28 5 := cutRule 5 p11 w10
def p12 : Weak 28 8 := signedPick 1 [1,2,3,8,10,16,18,19] (by decide) (by decide) (by decide)
def r19 : Rule 28 5 := cutRule 5 p12 w10
def f34 : ℕ := 0x4240007fff00
def f35 : ℕ := 0x18c377f98c7ff
def s10 : List ℕ := [f18,f34,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b4 : Ban 28 6 s10 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(655182505,r14),(17523384,r15),(1889561442,r6),(83464670,r16),(1616930924,r13),(1439710484,r17),(752918791,r18),(603749484,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f36 : ℕ := 0xf7ef78
def s11 : List ℕ := [f7,f8,f9,f10,f36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w11 : Wide 12 4 s11 := viaSearch (by decide +kernel)
def r20 : Rule 28 6 := cutRule 6 p2 w11
def f37 : ℕ := 0xa0c
def s12 : List ℕ := [f37,f0,f1,f2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w12 : Wide 6 3 s12 := viaSearch (by decide +kernel)
def r21 : Rule 28 6 := cutRule 6 p0 w12
def f38 : ℕ := 0xb7c
def s13 : List ℕ := [f0,f1,f38,f2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w13 : Wide 6 3 s13 := viaSearch (by decide +kernel)
def r22 : Rule 28 6 := cutRule 6 p0 w13
def f39 : ℕ := 0x350300
def s14 : List ℕ := [f7,f8,f39,f36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w14 : Wide 12 3 s14 := viaSearch (by decide +kernel)
def r23 : Rule 28 5 := cutRule 5 p2 w14
def r24 : Rule 28 5 := cutRule 5 p7 w14
def f40 : ℕ := 0x317fcf
def f41 : ℕ := 0x54bff3
def f42 : ℕ := 0x6a01fc
def s15 : List ℕ := [f40,f41,f42]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w15 : Wide 14 4 s15 := viaSearch (by decide +kernel)
def p13 : Weak 28 14 := relaxed (pick [0,1,4,5,14,15,16,17,18,23,24,25,26,27] (by decide) (by decide) (by decide))
def r25 : Rule 28 5 := cutRule 5 p13 w15
def f43 : ℕ := 0xac3f8
def f44 : ℕ := 0xae438
def f45 : ℕ := 0xfdbc0
def s16 : List ℕ := [f43,f44,f45]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w16 : Wide 10 3 s16 := viaSearch (by decide +kernel)
def p14 : Weak 28 10 := signedPick 0 [0,2,3,4,6,7,19,20,21,22] (by decide) (by decide) (by decide)
def r26 : Rule 28 5 := cutRule 5 p14 w16
def f46 : ℕ := 0xaa3fc
def f47 : ℕ := 0xab40c
def f48 : ℕ := 0xfebf0
def s17 : List ℕ := [f46,f47,f48]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w17 : Wide 10 3 s17 := viaSearch (by decide +kernel)
def p15 : Weak 28 10 := signedPick 0 [0,1,4,5,8,9,11,12,14,15] (by decide) (by decide) (by decide)
def r27 : Rule 28 5 := cutRule 5 p15 w17
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w18 : Wide 10 2 s16 := viaSearch (by decide +kernel)
def r28 : Rule 28 5 := cutRule 5 p14 w18
def f49 : ℕ := 0xab0ff8
def f50 : ℕ := 0xab9038
def f51 : ℕ := 0xff6fc0
def s18 : List ℕ := [f49,f50,f51]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w19 : Wide 12 3 s18 := viaSearch (by decide +kernel)
def p16 : Weak 28 12 := signedPick 0 [0,2,3,4,6,7,16,17,19,20,21,22] (by decide) (by decide) (by decide)
def r29 : Rule 28 5 := cutRule 5 p16 w19
def f52 : ℕ := 0x78dbffff8ffff
def s19 : List ℕ := [f18,f20,f21,f52,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b5 : Ban 28 6 s19 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(587753380,r7),(1944135699,r14),(1118192158,r14),(704392668,r7),(558706843,r14),(1185931039,r14),(1921445977,r23),(356972950,r23),(926257575,r24),(2057705909,r25),(1971527073,r7),(1660293498,r7),(1232184107,r7),(13034187,r14),(1959428957,r7),(1873250121,r14),(905123723,r7),(1925765866,r14),(67937658,r7),(2129242469,r14),(557862349,r26),(160449938,r7),(1433498070,r14),(1233353770,r27),(835941359,r14),(263630801,r7),(477905814,r26),(1494844756,r28),(8124409,r28),(837063297,r26),(106889148,r28),(830138702,r26),(52719343,r28),(727746539,r7),(444721029,r7),(358542193,r14),(1453995761,r14),(751968904,r29),(665790068,r7)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p17 : Weak 28 9 := signedPick 0 [0,1,2,4,5,8,14,15,19] (by decide) (by decide) (by decide)
def r30 : Rule 28 5 := cutRule 5 p17 w4
def p18 : Weak 28 6 := signedPick 0 [0,2,4,6,19,20] (by decide) (by decide) (by decide)
def r31 : Rule 28 5 := cutRule 5 p18 w1
def f53 : ℕ := 0x20480afe0f80f
def s20 : List ℕ := [f18,f35,f53,f20,f21,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b6 : Ban 28 6 s20 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(500200359,r7),(136021971,r30),(1746900702,r5),(752918791,r18),(53401985,r7),(706711957,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p19 : Weak 28 9 := signedPick 0 [0,1,4,5,6,9,14,15,20] (by decide) (by decide) (by decide)
def r32 : Rule 28 5 := cutRule 5 p19 w7
def f54 : ℕ := 0x4090a0060f8f0
def s21 : List ℕ := [f18,f35,f20,f54,f21,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b7 : Ban 28 6 s21 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1366307874,r7),(748907455,r32),(263000541,r12),(603749484,r19),(2102414327,r7),(1494512504,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f55 : ℕ := 0x2c7c
def f56 : ℕ := 0x2e9c
def f57 : ℕ := 0x3560
def f58 : ℕ := 0x3d60
def s22 : List ℕ := [f55,f56,f57,f58]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w20 : Wide 7 3 s22 := viaSearch (by decide +kernel)
def p20 : Weak 28 7 := signedPick 0 [0,1,4,5,7,14,15] (by decide) (by decide) (by decide)
def r33 : Rule 28 5 := cutRule 5 p20 w20
def f59 : ℕ := 0x2878
def f60 : ℕ := 0x2c98
def f61 : ℕ := 0x3960
def f62 : ℕ := 0x3b60
def s23 : List ℕ := [f59,f60,f61,f62]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w21 : Wide 7 3 s23 := viaSearch (by decide +kernel)
def p21 : Weak 28 7 := signedPick 0 [0,1,3,4,5,14,15] (by decide) (by decide) (by decide)
def r34 : Rule 28 5 := cutRule 5 p21 w21
def p22 : Weak 28 7 := signedPick 0 [0,1,4,5,6,14,15] (by decide) (by decide) (by decide)
def r35 : Rule 28 5 := cutRule 5 p22 w20
def p23 : Weak 28 7 := signedPick 0 [0,1,2,4,5,14,15] (by decide) (by decide) (by decide)
def r36 : Rule 28 5 := cutRule 5 p23 w21
def p24 : Weak 28 10 := signedPick 0 [0,1,3,4,5,7,14,15,21,22] (by decide) (by decide) (by decide)
def r37 : Rule 28 5 := cutRule 5 p24 w16
def s24 : List ℕ := [f55,f56,f61,f58]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w22 : Wide 7 3 s24 := viaSearch (by decide +kernel)
def p25 : Weak 28 7 := signedPick 0 [0,2,4,5,6,19,20] (by decide) (by decide) (by decide)
def r38 : Rule 28 5 := cutRule 5 p25 w22
def f63 : ℕ := 0x3a60
def s25 : List ℕ := [f59,f60,f63,f62]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w23 : Wide 7 3 s25 := viaSearch (by decide +kernel)
def p26 : Weak 28 7 := signedPick 0 [0,1,2,4,6,19,20] (by decide) (by decide) (by decide)
def r39 : Rule 28 5 := cutRule 5 p26 w23
def p27 : Weak 28 10 := signedPick 0 [0,1,2,4,5,6,14,15,19,20] (by decide) (by decide) (by decide)
def r40 : Rule 28 5 := cutRule 5 p27 w16
def f64 : ℕ := 0x11f8000ff
def s26 : List ℕ := [f64,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b8 : Ban 28 6 s26 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(16769760,r7),(1626179447,r8),(434683305,r5),(460345518,r33),(149578571,r12),(1116865734,r34),(1368580809,r7),(1350670866,r31),(557862349,r26),(1075120921,r8),(1595284938,r31),(1096508076,r31),(743647102,r8),(1860405647,r35),(1591523418,r36),(726730120,r14),(58874363,r14),(2018466044,r37),(1038186783,r8),(908404986,r14),(1831140819,r14),(67111955,r8),(1378541060,r38),(1423135994,r39),(919470880,r40),(2086675266,r31),(1436729452,r14),(1078870503,r14),(999053637,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r41 : Rule 28 6 := cutRule 6 p18 w0
def r42 : Rule 28 6 := cutRule 6 p5 w0
def f65 : ℕ := 0x16
def f66 : ℕ := 0x18
def s27 : List ℕ := [f65,f66]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w24 : Wide 3 1 s27 := viaSearch (by decide +kernel)
def p28 : Weak 28 3 := signedPick 8 [8,19,20] (by decide) (by decide) (by decide)
def r43 : Rule 28 5 := cutRule 5 p28 w24
def f67 : ℕ := 0x29000cfff000f
def s28 : List ℕ := [f18,f35,f67,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b9 : Ban 28 6 s28 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(440688038,r14),(477905814,r26),(1935652039,r14),(1174426141,r43)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f68 : ℕ := 0x14c
def s29 : List ℕ := [f68,f0,f1,f2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w25 : Wide 6 3 s29 := viaSearch (by decide +kernel)
def r44 : Rule 28 6 := cutRule 6 p0 w25
def f69 : ℕ := 0x26
def f70 : ℕ := 0x28
def s30 : List ℕ := [f69,f70]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w26 : Wide 3 1 s30 := viaSearch (by decide +kernel)
def p29 : Weak 28 3 := signedPick 9 [9,19,20] (by decide) (by decide) (by decide)
def r45 : Rule 28 5 := cutRule 5 p29 w26
def f71 : ℕ := 0x5200c007f00f0
def s31 : List ℕ := [f18,f35,f20,f71,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b10 : Ban 28 6 s31 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1651455185,r14),(837063297,r26),(505165274,r14),(94930014,r45)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f72 : ℕ := 0xebc
def s32 : List ℕ := [f0,f1,f2,f72]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w27 : Wide 6 3 s32 := viaSearch (by decide +kernel)
def r46 : Rule 28 6 := cutRule 6 p0 w27
def s33 : List ℕ := [f18,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b1 : Ban 28 7 s33 := viaRules (ws := [s5,s7,s10,s19,s20,s21,s26,s28,s31]) (consBan b2 (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b10 (nilBan _ _))))))))))
  (dictionary [(1281721062,r0),(1994369709,r0),(884308651,r1),(478542141,r2),(81129730,r0),(1834924460,r0),(1437512049,r1),(1008980919,r0),(611568508,r1),(1229012333,r3),(831599922,r0),(1240519141,r0),(906101489,r1),(1711068125,r0),(601007067,r1),(974473531,r0),(595181429,r9),(197769018,r0),(449495604,r0),(52083193,r1),(1076719800,r0),(679307389,r1),(2083772145,r10),(1686359734,r0),(1018586625,r0),(1397654155,r1),(220104694,r0),(1257527283,r1),(1450028066,r0),(1414822327,r20),(1997832947,r21),(419633925,r22),(1114418019,r0),(199747036,r0),(717005608,r1),(178359881,r0),(698523898,r0),(1215782470,r1),(1731196120,r0),(917057922,r1),(322036572,r0),(963644607,r0),(1480903179,r1),(1632724815,r0),(127773547,r1),(1026290409,r0),(694762378,r0),(1212020950,r1),(1801309935,r0),(1324286831,r0),(926874420,r1),(726730120,r0),(329317709,r1),(154419562,r41),(1904490798,r0),(1180493324,r0),(141425743,r0),(1178848332,r1),(2101584165,r1),(1317834562,r42),(207773504,r0),(988221106,r41),(620151188,r44),(1648984406,r41),(1747749145,r41),(323515052,r46),(1693579340,r41),(1265683314,r0),(1189914226,r0),(1707172798,r1),(1349313849,r1),(102292597,r41),(619551169,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f73 : ℕ := 0x392001c000
def s34 : List ℕ := [f28,f29,f73,f30,f31]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w28 : Wide 21 4 s34 := viaSearch (by decide +kernel)
def r47 : Rule 28 5 := cutRule 5 p10 w28
def f74 : ℕ := 0xb0f8
def f75 : ℕ := 0xb938
def f76 : ℕ := 0xd2c0
def f77 : ℕ := 0xe4c0
def s35 : List ℕ := [f74,f75,f76,f77]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w29 : Wide 8 3 s35 := viaSearch (by decide +kernel)
def p30 : Weak 28 8 := signedPick 0 [0,2,3,4,6,7,16,17] (by decide) (by decide) (by decide)
def r48 : Rule 28 5 := cutRule 5 p30 w29
def s36 : List ℕ := [f34,f35,f20,f21,f22,f52,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b12 : Ban 28 6 s36 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(677601683,r14),(1750944059,r47),(1078513567,r14),(2069152757,r48)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s37 : List ℕ := [f7,f8,f39,f9,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w30 : Wide 12 4 s37 := viaSearch (by decide +kernel)
def r49 : Rule 28 6 := cutRule 6 p2 w30
def f78 : ℕ := 0xfc8f8
def f79 : ℕ := 0x1ad318
def f80 : ℕ := 0x2ba560
def s38 : List ℕ := [f3,f78,f79,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w31 : Wide 11 3 s38 := viaSearch (by decide +kernel)
def p31 : Weak 28 11 := signedPick 1 [1,2,3,8,10,11,13,14,18,19,21] (by decide) (by decide) (by decide)
def r50 : Rule 28 5 := cutRule 5 p31 w31
def r51 : Rule 28 5 := cutRule 5 p18 w0
def f81 : ℕ := 0x28490eff8ff0f
def s39 : List ℕ := [f35,f81,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b13 : Ban 28 6 s39 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1263717967,r14),(1724242949,r14),(2069152757,r48),(1903890914,r50),(1274674400,r14),(2111565944,r51),(632263486,r31),(328898642,r51),(569436304,r51)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p32 : Weak 28 11 := signedPick 5 [5,6,7,9,10,12,13,15,18,20,22] (by decide) (by decide) (by decide)
def r52 : Rule 28 5 := cutRule 5 p32 w31
def f82 : ℕ := 0x5092e0078fff0
def s40 : List ℕ := [f35,f20,f82,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b14 : Ban 28 6 s40 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2069152757,r48),(2129764802,r52),(1377512247,r14),(1602476911,r14),(107631639,r14),(1784505560,r51),(1065405432,r31),(310297739,r51),(242375920,r51)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r53 : Rule 28 6 := cutRule 6 p18 w1
def s41 : List ℕ := [f35,f20,f21,f22,f52,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b11 : Ban 28 7 s41 := viaRules (ws := [s36,s19,s39,s40]) (consBan b12 (consBan b5 (consBan b13 (consBan b14 (nilBan _ _)))))
  (dictionary [(1551752716,r0),(1217335064,r1),(912240642,r1),(1285707106,r0),(1329820200,r0),(1708887730,r1),(1568760858,r1),(1761261641,r0),(1726055902,r49),(161582875,r21),(730867500,r22),(178359881,r0),(698523898,r0),(1215782470,r1),(2138300241,r0),(1028239183,r1),(678283654,r0),(1195542226,r1),(2042429695,r0),(1228291497,r1),(633270147,r0),(1792136754,r1),(1943958390,r0),(439007122,r1),(1337523984,r0),(1523254525,r1),(1114418019,r0),(1036794032,r0),(2051306595,r0),(1965127759,r1),(22046970,r3),(2083351781,r0),(1764038882,r0),(1677860046,r1),(709733648,r0),(1816554627,r0),(1730375791,r1),(1242385121,r10),(1156206285,r0),(2020031230,r0),(1933852394,r1),(1281721062,r0),(454304310,r41),(1491726899,r0),(1490081907,r1),(1375395151,r41),(265334093,r1),(519007079,r0),(282515739,r41),(1299454681,r53),(931384763,r41),(1960217981,r53),(641673222,r41),(2058982720,r53),(634748627,r41),(2004812915,r53),(1059658317,r41),(1576916889,r0),(2018406373,r1),(1143288852,r41),(1660547424,r1),(930784744,r0),(618535300,r41),(532356464,r0),(249330954,r0),(163152118,r1),(1344784522,r0),(1258605686,r1),(556578829,r41),(470399993,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f83 : ℕ := 0xc37f063f
def f84 : ℕ := 0x848dfc7c7
def f85 : ℕ := 0xd68dfffc7
def f86 : ℕ := 0x16b600fff8
def f87 : ℕ := 0x1b05bff83f
def s42 : List ℕ := [f83,f84,f85,f86,f87]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w32 : Wide 21 5 s42 := viaSearch (by decide +kernel)
def p33 : Weak 28 21 := relaxed (pick [0,1,2,4,5,6,8,9,10,14,15,16,17,18,19,20,23,24,25,26,27] (by decide) (by decide) (by decide))
def r54 : Rule 28 6 := cutRule 6 p33 w32
def f88 : ℕ := 0x109600c7f8
def s43 : List ℕ := [f83,f85,f88,f86,f87]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w33 : Wide 21 5 s43 := viaSearch (by decide +kernel)
def r55 : Rule 28 6 := cutRule 6 p33 w33
def f89 : ℕ := 0x42000ffc0
def f90 : ℕ := 0x18dfffc7ff
def s44 : List ℕ := [f83,f89,f85,f86,f90,f87]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w34 : Wide 21 5 s44 := viaSearch (by decide +kernel)
def r56 : Rule 28 6 := cutRule 6 p33 w34
def f91 : ℕ := 0x48fc
def f92 : ℕ := 0x5d1c
def f93 : ℕ := 0x6860
def f94 : ℕ := 0xeeec
def s45 : List ℕ := [f91,f92,f93,f94]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w35 : Wide 8 3 s45 := viaSearch (by decide +kernel)
def p34 : Weak 28 8 := signedPick 1 [1,2,8,10,14,16,18,19] (by decide) (by decide) (by decide)
def r57 : Rule 28 6 := cutRule 6 p34 w35
def p35 : Weak 28 8 := signedPick 5 [5,6,9,10,15,17,18,20] (by decide) (by decide) (by decide)
def r58 : Rule 28 6 := cutRule 6 p35 w35
def f95 : ℕ := 0x131fc
def f96 : ℕ := 0x17a3c
def f97 : ℕ := 0x1b0d0
def f98 : ℕ := 0x3bdcc
def s46 : List ℕ := [f95,f96,f97,f98]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w36 : Wide 9 3 s46 := viaSearch (by decide +kernel)
def p36 : Weak 28 9 := signedPick 1 [1,2,8,10,13,14,16,18,19] (by decide) (by decide) (by decide)
def r59 : Rule 28 5 := cutRule 5 p36 w36
def f99 : ℕ := 0xd6506f9fc70f
def s47 : List ℕ := [f99,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b16 : Ban 28 6 s47 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(943237703,r14),(969482808,r59),(1314470333,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p37 : Weak 28 9 := signedPick 5 [5,6,9,10,13,15,17,18,20] (by decide) (by decide) (by decide)
def r60 : Rule 28 5 := cutRule 5 p37 w36
def f100 : ℕ := 0x16a66001fc7f0
def s48 : List ℕ := [f100,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b17 : Ban 28 6 s48 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(612590969,r60),(347942228,r14),(525185958,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r61 : Rule 28 6 := cutRule 6 p13 w15
def f101 : ℕ := 0x2d9098
def s49 : List ℕ := [f7,f101,f9,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w37 : Wide 12 4 s49 := viaSearch (by decide +kernel)
def r62 : Rule 28 5 := cutRule 5 p2 w37
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w38 : Wide 12 3 s49 := viaSearch (by decide +kernel)
def r63 : Rule 28 5 := cutRule 5 p2 w38
def f102 : ℕ := 0x7b18ddfff38ff
def s50 : List ℕ := [f35,f20,f21,f22,f102]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b18 : Ban 28 6 s50 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1347603014,r14),(1839155680,r14),(745839158,r62),(1856323852,r63),(828791848,r7),(808551604,r7),(1358559447,r14),(569275072,r14),(1621994849,r7),(293420068,r14),(1922690158,r14),(649275029,r7),(1508042120,r31),(865902511,r31),(1312814831,r51),(1273556802,r51)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f103 : ℕ := 0xa8fc
def f104 : ℕ := 0xad0c
def f105 : ℕ := 0xfaf0
def s51 : List ℕ := [f103,f104,f105]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w39 : Wide 8 3 s51 := viaSearch (by decide +kernel)
def p38 : Weak 28 8 := signedPick 0 [0,2,4,6,16,17,19,20] (by decide) (by decide) (by decide)
def r64 : Rule 28 5 := cutRule 5 p38 w39
def f106 : ℕ := 0xdd98
def s52 : List ℕ := [f14,f16,f106]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w40 : Wide 8 3 s52 := viaSearch (by decide +kernel)
def r65 : Rule 28 5 := cutRule 5 p4 w40
def r66 : Rule 28 5 := cutRule 5 p9 w40
def f107 : ℕ := 0xafd8f8
def s53 : List ℕ := [f7,f9,f107,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w41 : Wide 12 4 s53 := viaSearch (by decide +kernel)
def r67 : Rule 28 5 := cutRule 5 p2 w41
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w42 : Wide 12 3 s53 := viaSearch (by decide +kernel)
def r68 : Rule 28 5 := cutRule 5 p2 w42
def p39 : Weak 28 12 := signedPick 0 [0,1,3,4,5,7,11,12,14,15,21,22] (by decide) (by decide) (by decide)
def r69 : Rule 28 5 := cutRule 5 p39 w19
def f108 : ℕ := 0x1b0055f9f00ff
def s54 : List ℕ := [f35,f108,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b19 : Ban 28 6 s54 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1483317799,r7),(2072057183,r64),(957319173,r65),(1660324110,r14),(317807099,r51),(1213651340,r31),(735386657,r66),(4393129,r14),(974327315,r51),(1941556855,r31),(1058560254,r67),(21561301,r68),(932582502,r51),(601108683,r69),(408048909,r7),(313911772,r14),(1725391019,r7),(2103536470,r14),(1671280543,r14),(881996168,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f109 : ℕ := 0x6018880603800
def s55 : List ℕ := [f35,f20,f21,f109,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b15 : Ban 28 7 s55 := viaRules (ws := [s47,s48,s50,s54]) (consBan b16 (consBan b17 (consBan b18 (consBan b19 (nilBan _ _)))))
  (dictionary [(15553265,r54),(1052975854,r0),(718558202,r1),(1523524838,r0),(413463780,r1),(786930244,r0),(1941104396,r55),(831043338,r0),(1210110868,r1),(32561407,r0),(1069983996,r1),(1262484779,r0),(116794346,r56),(1227279040,r57),(1810289660,r57),(232090638,r58),(2138300241,r0),(1613194881,r0),(1028239183,r1),(1723474098,r0),(1138518400,r1),(1236048508,r3),(651092810,r0),(322656105,r0),(1885184054,r1),(217536906,r0),(520636602,r0),(2083164551,r1),(1918924586,r10),(1333968888,r0),(984262616,r0),(399306918,r1),(1328870414,r0),(199747036,r0),(717005608,r1),(1289567850,r61),(1806826422,r0),(179506792,r0),(696765364,r1),(1543652833,r0),(729514635,r1),(134493285,r0),(1293359892,r1),(1445181528,r0),(2087713907,r1),(838747122,r0),(1024477663,r1),(1301961306,r0),(992950037,r0),(2101366103,r0),(991305045,r1),(1914040878,r1),(1130291275,r42),(20230217,r0),(1931222524,r41),(800677819,r53),(432607901,r41),(1461441119,r53),(142896360,r41),(1560205858,r53),(135971765,r41),(1506036053,r53),(1054548489,r0),(469592791,r1),(763183570,r41),(1158507133,r0),(178227872,r0),(1075904666,r41),(1471228229,r0),(490948968,r0),(605703575,r0),(20747877,r1),(560881455,r41),(1078140027,r0),(1519629511,r1),(644511990,r41),(1161770562,r1),(432007882,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f110 : ℕ := 0x129fc
def f111 : ℕ := 0x1a8c4
def f112 : ℕ := 0x3bdd8
def s56 : List ℕ := [f110,f96,f111,f112]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w43 : Wide 9 3 s56 := viaSearch (by decide +kernel)
def p40 : Weak 28 9 := signedPick 1 [1,3,10,11,13,14,16,18,21] (by decide) (by decide) (by decide)
def r70 : Rule 28 5 := cutRule 5 p40 w43
def f113 : ℕ := 0x256c0afe7f80f
def s57 : List ℕ := [f35,f113,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b21 : Ban 28 6 s57 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1303513900,r14),(1927766014,r70),(1728342877,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p41 : Weak 28 9 := signedPick 5 [5,7,10,12,13,15,17,18,22] (by decide) (by decide) (by decide)
def r71 : Rule 28 5 := cutRule 5 p41 w43
def f114 : ℕ := 0x46b4a0067f8f0
def s58 : List ℕ := [f35,f20,f114,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b22 : Ban 28 6 s58 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1795066566,r14),(1534892156,r71),(1997325950,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p42 : Weak 28 21 := relaxed (pick [0,1,3,4,5,7,11,12,13,14,15,16,17,18,21,22,23,24,25,26,27] (by decide) (by decide) (by decide))
def r72 : Rule 28 6 := cutRule 6 p42 w34
def p43 : Weak 28 8 := signedPick 1 [1,3,11,13,14,16,18,21] (by decide) (by decide) (by decide)
def r73 : Rule 28 6 := cutRule 6 p43 w35
def p44 : Weak 28 8 := signedPick 5 [5,7,12,13,15,17,18,22] (by decide) (by decide) (by decide)
def r74 : Rule 28 6 := cutRule 6 p44 w35
def r75 : Rule 28 6 := cutRule 6 p42 w32
def r76 : Rule 28 6 := cutRule 6 p42 w33
def f115 : ℕ := 0x2f10e0
def s59 : List ℕ := [f7,f115,f9,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w44 : Wide 12 4 s59 := viaSearch (by decide +kernel)
def r77 : Rule 28 5 := cutRule 5 p2 w44
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w45 : Wide 12 3 s59 := viaSearch (by decide +kernel)
def r78 : Rule 28 5 := cutRule 5 p2 w45
def r79 : Rule 28 5 := cutRule 5 p5 w0
def f116 : ℕ := 0x7b03ddfff07ff
def s60 : List ℕ := [f35,f20,f21,f22,f116]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b23 : Ban 28 6 s60 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1334048549,r14),(1825601215,r14),(732284693,r77),(1842769387,r78),(295073366,r7),(107530079,r7),(1345004982,r14),(555720607,r14),(1742706514,r79),(1492108636,r79),(1701704918,r8),(133057334,r8),(1693630374,r7),(279865603,r14),(809138301,r14),(1047498229,r7)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f117 : ℕ := 0x6fb4f8
def s61 : List ℕ := [f7,f117,f9,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w46 : Wide 12 4 s61 := viaSearch (by decide +kernel)
def r80 : Rule 28 5 := cutRule 5 p2 w46
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w47 : Wide 12 3 s61 := viaSearch (by decide +kernel)
def r81 : Rule 28 5 := cutRule 5 p2 w47
def p45 : Weak 28 12 := signedPick 0 [0,1,2,4,5,6,8,9,14,15,19,20] (by decide) (by decide) (by decide)
def r82 : Rule 28 5 := cutRule 5 p45 w19
def f118 : ℕ := 0xdb98
def s62 : List ℕ := [f14,f33,f118]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w48 : Wide 8 3 s62 := viaSearch (by decide +kernel)
def r83 : Rule 28 5 := cutRule 5 p11 w48
def r84 : Rule 28 5 := cutRule 5 p12 w48
def p46 : Weak 28 8 := signedPick 0 [0,2,4,6,8,9,19,20] (by decide) (by decide) (by decide)
def r85 : Rule 28 5 := cutRule 5 p46 w39
def f119 : ℕ := 0x630099fe700ff
def s63 : List ℕ := [f35,f20,f21,f22,f119]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b24 : Ban 28 6 s63 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(391619257,r14),(883171923,r14),(1937339048,r80),(900340095,r81),(184041666,r79),(1832748451,r82),(699455316,r83),(402575690,r14),(449162375,r79),(600984011,r84),(1760774962,r14),(180280146,r79),(1286827703,r7),(664366100,r14),(1587101933,r14),(1252358764,r7),(1395280242,r8),(2048579351,r8),(234025506,r7),(1735294012,r85)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f120 : ℕ := 0x1803440180700
def s64 : List ℕ := [f120,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b20 : Ban 28 7 s64 := viaRules (ws := [s57,s58,s60,s63]) (consBan b21 (consBan b22 (consBan b23 (consBan b24 (nilBan _ _)))))
  (dictionary [(1301961306,r0),(1994369709,r0),(884308651,r1),(174696088,r0),(1904527080,r1),(1724325938,r3),(1306673283,r0),(1158988690,r0),(681937832,r0),(264285177,r1),(1220278897,r0),(885861245,r1),(580766823,r1),(954233287,r0),(1709922324,r0),(1292269669,r1),(611166741,r10),(193514086,r0),(120470493,r0),(396538785,r0),(2126369777,r1),(998346381,r0),(1377413911,r1),(1237287039,r1),(1429787822,r0),(284097389,r72),(1394582083,r73),(1977592703,r73),(399393681,r74),(1613194881,r0),(678283654,r0),(1195542226,r1),(1289567850,r61),(1806826422,r0),(179506792,r0),(696765364,r1),(1193697304,r75),(1710955876,r0),(896817678,r1),(301796328,r0),(943404363,r0),(1460662935,r1),(1095225999,r76),(1612484571,r0),(107533303,r1),(1006050165,r0),(674522134,r0),(1191780706,r1),(2061624290,r0),(1643971635,r1),(749629105,r41),(1312255711,r0),(331976450,r0),(1954683460,r42),(369826419,r0),(1537030805,r0),(1749787637,r0),(1332134982,r1),(122830491,r42),(1160253080,r0),(1158608088,r1),(1043921332,r42),(2081343921,r1),(187533260,r0),(2098525567,r42),(967980862,r41),(599910944,r42),(1628744162,r41),(310199403,r42),(1727508901,r41),(303274808,r42),(1673339096,r41),(1245443070,r0),(1169673982,r0),(1686932554,r1),(1329073605,r1),(82052353,r41),(599310925,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f121 : ℕ := 0x1287f8
def f122 : ℕ := 0x17c8f8
def f123 : ℕ := 0x3ba760
def s65 : List ℕ := [f121,f122,f79,f123]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w49 : Wide 11 4 s65 := viaSearch (by decide +kernel)
def p47 : Weak 28 11 := signedPick 5 [5,6,7,9,10,12,13,15,17,18,22] (by decide) (by decide) (by decide)
def r86 : Rule 28 6 := cutRule 6 p47 w49
def p48 : Weak 28 9 := signedPick 0 [0,2,3,4,6,16,19,20,21] (by decide) (by decide) (by decide)
def r87 : Rule 28 5 := cutRule 5 p48 w4
def f124 : ℕ := 0xfdf8
def s66 : List ℕ := [f14,f15,f16,f124]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w50 : Wide 8 3 s66 := viaSearch (by decide +kernel)
def r88 : Rule 28 5 := cutRule 5 p4 w50
def f125 : ℕ := 0x180055f9800ff
def s67 : List ℕ := [f19,f125,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b26 : Ban 28 6 s67 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(78969842,r87),(1689848573,r5),(18022224,r88),(792546956,r8),(245640651,r51),(1864531734,r51)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p49 : Weak 28 11 := signedPick 1 [1,2,3,8,10,11,13,14,16,18,21] (by decide) (by decide) (by decide)
def r89 : Rule 28 6 := cutRule 6 p49 w49
def p50 : Weak 28 9 := signedPick 0 [0,2,4,6,7,17,19,20,22] (by decide) (by decide) (by decide)
def r90 : Rule 28 5 := cutRule 5 p50 w7
def r91 : Rule 28 5 := cutRule 5 p9 w50
def s68 : List ℕ := [f27,f125,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b27 : Ban 28 6 s68 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1822964750,r90),(1337057836,r12),(1892875353,r91),(1122811095,r8),(2001625022,r51),(1642599218,r51)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w51 : Wide 11 3 s65 := viaSearch (by decide +kernel)
def r92 : Rule 28 5 := cutRule 5 p47 w51
def r93 : Rule 28 5 := cutRule 5 p49 w51
def f126 : ℕ := 0x33ffdb9ffc0
def s69 : List ℕ := [f28,f29,f30,f31,f126]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w52 : Wide 21 4 s69 := viaSearch (by decide +kernel)
def r94 : Rule 28 5 := cutRule 5 p10 w52
def f127 : ℕ := 0x5a18
def s70 : List ℕ := [f14,f127,f33,f124]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w53 : Wide 8 3 s70 := viaSearch (by decide +kernel)
def p51 : Weak 28 8 := signedPick 5 [5,6,7,9,10,12,13,15] (by decide) (by decide) (by decide)
def r95 : Rule 28 5 := cutRule 5 p51 w53
def p52 : Weak 28 8 := signedPick 1 [1,2,3,8,10,11,13,14] (by decide) (by decide) (by decide)
def r96 : Rule 28 5 := cutRule 5 p52 w53
def s71 : List ℕ := [f34,f125,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b28 : Ban 28 6 s71 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1966642237,r31),(333463392,r92),(18022224,r88),(1559096068,r93),(1892875353,r91),(1715654913,r94),(766487097,r95),(1074946578,r96)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f128 : ℕ := 0xbfdbf8
def s72 : List ℕ := [f7,f8,f9,f10,f128]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w54 : Wide 12 4 s72 := viaSearch (by decide +kernel)
def r97 : Rule 28 6 := cutRule 6 p2 w54
def r98 : Rule 28 6 := cutRule 6 p18 w12
def r99 : Rule 28 6 := cutRule 6 p18 w13
def p53 : Weak 28 3 := signedPick 8 [8,14,15] (by decide) (by decide) (by decide)
def r100 : Rule 28 5 := cutRule 5 p53 w24
def s73 : List ℕ := [f125,f35,f53,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b29 : Ban 28 6 s73 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1293403360,r31),(1641583509,r100),(1826884247,r37),(332710572,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r101 : Rule 28 6 := cutRule 6 p18 w25
def p54 : Weak 28 3 := signedPick 9 [9,14,15] (by decide) (by decide) (by decide)
def r102 : Rule 28 5 := cutRule 5 p54 w26
def s74 : List ℕ := [f125,f35,f20,f54,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b30 : Ban 28 6 s74 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(12027228,r31),(703129827,r102),(1728412942,r37),(1120511119,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r103 : Rule 28 6 := cutRule 6 p18 w27
def f129 : ℕ := 0x270060
def s75 : List ℕ := [f7,f129,f9,f128]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w55 : Wide 12 3 s75 := viaSearch (by decide +kernel)
def r104 : Rule 28 5 := cutRule 5 p2 w55
def r105 : Rule 28 5 := cutRule 5 p7 w55
def r106 : Rule 28 5 := cutRule 5 p24 w18
def f130 : ℕ := 0xd7e7f
def f131 : ℕ := 0x34bff3
def f132 : ℕ := 0x5a01fc
def s76 : List ℕ := [f130,f131,f132]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w56 : Wide 14 4 s76 := viaSearch (by decide +kernel)
def p55 : Weak 28 14 := relaxed (pick [0,2,4,6,11,12,13,19,20,23,24,25,26,27] (by decide) (by decide) (by decide))
def r107 : Rule 28 5 := cutRule 5 p55 w56
def f133 : ℕ := 0x7bc3fffffc7ff
def s77 : List ℕ := [f125,f20,f21,f22,f133]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b31 : Ban 28 6 s77 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(492757865,r51),(339505396,r31),(863953375,r31),(1769088543,r51),(208647175,r31),(838805524,r31),(1510510454,r104),(2093521074,r104),(515322052,r105),(2018466044,r37),(1896998062,r51),(235430634,r31),(1188324507,r37),(1066856525,r31),(1759900006,r51),(1826884247,r37),(1012746049,r106),(1576591306,r106),(1728412942,r37),(223461674,r106),(1121978536,r37),(1307709077,r106),(1689944275,r107),(1566831301,r51),(1568476293,r51),(1605092869,r51),(275796631,r31),(1108694126,r51),(985581152,r31),(1501786138,r51),(861758039,r31),(128083313,r51),(4970339,r31),(290758241,r51),(70719644,r51),(2095090317,r31),(599992342,r69),(476879368,r51),(303979291,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f134 : ℕ := 0x221f8
def f135 : ℕ := 0x2f678
def f136 : ℕ := 0x369a0
def s78 : List ℕ := [f134,f135,f136]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w57 : Wide 9 3 s78 := viaSearch (by decide +kernel)
def p56 : Weak 28 9 := signedPick 0 [0,1,2,4,6,8,14,19,20] (by decide) (by decide) (by decide)
def r108 : Rule 28 5 := cutRule 5 p56 w57
def s79 : List ℕ := [f125,f35,f67,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b32 : Ban 28 6 s79 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1696911728,r51),(827434715,r108),(290829799,r5),(766487097,r95),(103904429,r51),(1561650654,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f137 : ℕ := 0x2219c
def f138 : ℕ := 0x2fa1c
def f139 : ℕ := 0x365a0
def s80 : List ℕ := [f137,f138,f139]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w58 : Wide 9 3 s80 := viaSearch (by decide +kernel)
def p57 : Weak 28 9 := signedPick 0 [0,2,4,5,6,9,15,19,20] (by decide) (by decide) (by decide)
def r109 : Rule 28 5 := cutRule 5 p57 w58
def s81 : List ℕ := [f125,f35,f20,f71,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b33 : Ban 28 6 s81 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(760195228,r51),(1005035975,r109),(519129061,r12),(1074946578,r96),(463061912,r51),(131163889,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s82 : List ℕ := [f125,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b25 : Ban 28 7 s82 := viaRules (ws := [s67,s68,s71,s26,s73,s74,s77,s79,s81]) (consBan b26 (consBan b27 (consBan b28 (consBan b8 (consBan b29 (consBan b30 (consBan b31 (consBan b32 (consBan b33 (nilBan _ _))))))))))
  (dictionary [(605185915,r41),(1593778991,r41),(483717933,r53),(794482149,r86),(673014167,r41),(641229680,r41),(519761698,r53),(1165677659,r41),(1044209677,r53),(1700806012,r3),(1579338030,r41),(1516463570,r41),(1182045918,r0),(1987012554,r41),(876951496,r0),(1250417960,r41),(2070812827,r89),(1949344845,r41),(510371459,r41),(388903477,r53),(1140529808,r41),(1019061826,r53),(581024856,r10),(459556874,r41),(1294531054,r41),(1673598584,r0),(496049123,r41),(1533471712,r0),(1725972495,r41),(1690766756,r97),(126293729,r98),(695578354,r99),(2077254364,r41),(537154918,r0),(415686936,r0),(1368580809,r41),(1247112827,r53),(2061624290,r0),(1940156308,r0),(1180493324,r0),(454304310,r41),(1491726899,r0),(992950037,r0),(122830491,r42),(1160253080,r0),(1193002351,r0),(597981001,r101),(1756847608,r0),(403717976,r0),(1302234838,r103),(1487965379,r0),(351512929,r0),(1210324208,r0),(230044947,r0),(417370172,r41),(287588375,r0),(1454792761,r0),(247226593,r41),(1264165535,r53),(896095617,r41),(757724449,r41),(1924928835,r53),(606384076,r41),(2023693574,r53),(599459481,r41),(802319383,r41),(1969523769,r53),(1541627743,r41),(815912841,r0),(1983117227,r0),(458053892,r0),(1625258278,r0),(895495598,r53)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f140 : ℕ := 0x21e0000e00
def s83 : List ℕ := [f28,f140,f29,f30,f31]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w59 : Wide 21 4 s83 := viaSearch (by decide +kernel)
def r110 : Rule 28 5 := cutRule 5 p10 w59
def p58 : Weak 28 8 := signedPick 0 [0,1,3,4,5,7,11,12] (by decide) (by decide) (by decide)
def r111 : Rule 28 5 := cutRule 5 p58 w29
def s84 : List ℕ := [f34,f35,f20,f21,f22,f23,f133]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b35 : Ban 28 6 s84 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(640667545,r14),(1714009921,r110),(1395512733,r31),(2054691107,r111)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s85 : List ℕ := [f7,f129,f8,f9,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w60 : Wide 12 4 s85 := viaSearch (by decide +kernel)
def r112 : Rule 28 6 := cutRule 6 p2 w60
def f141 : ℕ := 0x987f8
def f142 : ℕ := 0x1dd398
def f143 : ℕ := 0x2da5a0
def s86 : List ℕ := [f141,f4,f142,f143]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w61 : Wide 11 3 s86 := viaSearch (by decide +kernel)
def p59 : Weak 28 11 := signedPick 1 [1,2,3,8,10,13,14,16,18,19,21] (by decide) (by decide) (by decide)
def r113 : Rule 28 5 := cutRule 5 p59 w61
def f144 : ℕ := 0x29410efffc70f
def s87 : List ℕ := [f35,f144,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b36 : Ban 28 6 s87 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2047562252,r14),(2031353788,r14),(2054691107,r111),(1259419250,r113),(471982153,r7),(1089459599,r14),(725173236,r7),(2129681869,r31),(703334775,r7)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p60 : Weak 28 11 := signedPick 5 [5,6,7,9,10,13,15,17,18,20,22] (by decide) (by decide) (by decide)
def r114 : Rule 28 5 := cutRule 5 p60 w61
def f145 : ℕ := 0x5282e007fc7f0
def s88 : List ℕ := [f35,f20,f145,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b37 : Ban 28 6 s88 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2054691107,r111),(673180402,r114),(237626538,r14),(896738242,r14),(368675422,r7),(813624906,r14),(472697198,r7),(587721528,r31),(600028044,r7)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s89 : List ℕ := [f35,f20,f21,f22,f23,f133]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b34 : Ban 28 7 s89 := viaRules (ws := [s84,s77,s87,s88]) (consBan b35 (consBan b31 (consBan b36 (consBan b37 (nilBan _ _)))))
  (dictionary [(1514818578,r0),(1180400926,r1),(875306504,r1),(1248772968,r0),(1292886062,r0),(1671953592,r1),(1531826720,r1),(1724327503,r0),(1689121764,r112),(124648737,r21),(693933362,r22),(141425743,r0),(1178848332,r1),(1490081907,r1),(2101366103,r0),(991305045,r1),(1158608088,r1),(2005495557,r0),(1191357359,r1),(596336009,r0),(1755202616,r1),(1907024252,r0),(402072984,r1),(1300589846,r0),(1486320387,r1),(417370172,r41),(287588375,r0),(1454792761,r0),(1338461013,r0),(228399955,r1),(1462352202,r0),(482072941,r0),(245581601,r41),(1262520543,r53),(894450625,r41),(1923283843,r53),(604739084,r41),(2022048582,r53),(597814489,r41),(1967878777,r53),(372778365,r0),(1539982751,r0),(1981472235,r1),(1623613286,r1),(1874129867,r0),(893850606,r0),(351512929,r0),(1783704179,r0),(577520915,r0),(454407941,r1),(427321444,r3),(304208470,r0),(1287305436,r0),(1164192462,r1),(1680397448,r0),(1163482323,r0),(1040369349,r1),(27186098,r10),(2051556771,r0),(306694623,r0),(183581649,r1),(592482525,r0),(469369551,r1),(249330954,r0),(126217980,r1),(778603652,r0),(655490678,r1),(605703575,r0),(482590601,r1),(605185915,r41)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f146 : ℕ := 0x6c37f3e3f
def f147 : ℕ := 0xa08dff1c7
def f148 : ℕ := 0xb68dfffc7
def f149 : ℕ := 0x15b600fff8
def f150 : ℕ := 0x1805bfc03f
def s90 : List ℕ := [f146,f147,f148,f149,f150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w62 : Wide 21 5 s90 := viaSearch (by decide +kernel)
def p61 : Weak 28 21 := relaxed (pick [0,1,2,4,5,6,8,9,10,11,12,13,14,15,19,20,23,24,25,26,27] (by decide) (by decide) (by decide))
def r115 : Rule 28 6 := cutRule 6 p61 w62
def f151 : ℕ := 0x141600f1f8
def s91 : List ℕ := [f146,f148,f151,f149,f150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w63 : Wide 21 5 s91 := viaSearch (by decide +kernel)
def r116 : Rule 28 6 := cutRule 6 p61 w63
def f152 : ℕ := 0x12000ffc0
def f153 : ℕ := 0x1e1ffff1ff
def s92 : List ℕ := [f152,f146,f148,f149,f150,f153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w64 : Wide 21 5 s92 := viaSearch (by decide +kernel)
def r117 : Rule 28 6 := cutRule 6 p61 w64
def f154 : ℕ := 0x28fc
def f155 : ℕ := 0x3830
def f156 : ℕ := 0x7d7c
def f157 : ℕ := 0xae8c
def s93 : List ℕ := [f154,f155,f156,f157]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w65 : Wide 8 3 s93 := viaSearch (by decide +kernel)
def p62 : Weak 28 8 := signedPick 1 [1,2,8,10,11,13,14,19] (by decide) (by decide) (by decide)
def r118 : Rule 28 6 := cutRule 6 p62 w65
def p63 : Weak 28 8 := signedPick 5 [5,6,9,10,12,13,15,20] (by decide) (by decide) (by decide)
def r119 : Rule 28 6 := cutRule 6 p63 w65
def f158 : ℕ := 0x151fc
def f159 : ℕ := 0x170b0
def f160 : ℕ := 0x1fa7c
def f161 : ℕ := 0x35d8c
def s94 : List ℕ := [f158,f159,f160,f161]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w66 : Wide 9 3 s94 := viaSearch (by decide +kernel)
def p64 : Weak 28 9 := signedPick 1 [1,2,8,10,11,13,14,18,19] (by decide) (by decide) (by decide)
def r120 : Rule 28 5 := cutRule 5 p64 w66
def f162 : ℕ := 0xc6d06f98ff0f
def s95 : List ℕ := [f162,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b39 : Ban 28 6 s95 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1310072492,r14),(1475688890,r120),(1385633517,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p65 : Weak 28 9 := signedPick 5 [5,6,9,10,12,13,15,18,20] (by decide) (by decide) (by decide)
def r121 : Rule 28 5 := cutRule 5 p65 w66
def f163 : ℕ := 0x14b660018fff0
def s96 : List ℕ := [f163,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b40 : Ban 28 6 s96 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1402786961,r121),(1317401285,r14),(2145161556,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f164 : ℕ := 0x65a418
def s97 : List ℕ := [f7,f8,f164,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w67 : Wide 12 4 s97 := viaSearch (by decide +kernel)
def r122 : Rule 28 5 := cutRule 5 p2 w67
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w68 : Wide 12 3 s97 := viaSearch (by decide +kernel)
def r123 : Rule 28 5 := cutRule 5 p2 w68
def f165 : ℕ := 0x63d8bbfe7f8ff
def s98 : List ℕ := [f35,f20,f21,f165,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b41 : Ban 28 6 s98 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(750060332,r14),(1241612998,r14),(148296476,r122),(1258781170,r123),(748507738,r14),(1843361033,r14),(1325147476,r14),(728267494,r14),(1027351531,r14),(1080722485,r14),(2004731428,r7),(1032011608,r7),(832179949,r31),(1591707988,r31),(234025506,r7),(1443789273,r7)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p66 : Weak 28 8 := signedPick 0 [0,1,4,5,11,12,14,15] (by decide) (by decide) (by decide)
def r124 : Rule 28 5 := cutRule 5 p66 w39
def f166 : ℕ := 0xf6e0
def s99 : List ℕ := [f14,f15,f166]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w69 : Wide 8 3 s99 := viaSearch (by decide +kernel)
def r125 : Rule 28 5 := cutRule 5 p4 w69
def r126 : Rule 28 5 := cutRule 5 p9 w69
def f167 : ℕ := 0xf5ef18
def s100 : List ℕ := [f7,f8,f10,f167]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w70 : Wide 12 4 s100 := viaSearch (by decide +kernel)
def r127 : Rule 28 5 := cutRule 5 p2 w70
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w71 : Wide 12 3 s100 := viaSearch (by decide +kernel)
def r128 : Rule 28 5 := cutRule 5 p2 w71
def f168 : ℕ := 0xd833f80f8ff
def s101 : List ℕ := [f168,f35,f20,f21,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b42 : Ban 28 6 s101 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1203990216,r51),(255367422,r124),(172122004,r14),(611577912,r125),(1314582849,r14),(2119549485,r7),(1919251741,r14),(389645396,r126),(1806135515,r14),(628586054,r7),(712818993,r127),(1823303687,r128),(62307648,r7),(2115654158,r14),(737799069,r14),(1028032529,r7),(549907103,r7),(1726315922,r29),(1396702466,r31),(8746858,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r129 : Rule 28 6 := cutRule 6 p55 w56
def f169 : ℕ := 0x6300880670000
def s102 : List ℕ := [f35,f20,f21,f22,f169,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b38 : Ban 28 7 s102 := viaRules (ws := [s95,s96,s98,s101]) (consBan b39 (consBan b40 (consBan b41 (consBan b42 (nilBan _ _)))))
  (dictionary [(1400131822,r115),(290070764,r0),(2103136759,r1),(760619748,r0),(1798042337,r1),(24025154,r0),(1178199306,r116),(68138248,r0),(447205778,r1),(1417139964,r0),(307078906,r1),(499579689,r0),(1501372903,r117),(464373950,r118),(1047384570,r118),(1616669195,r119),(2101584165,r1),(1375395151,r41),(265334093,r1),(1914040878,r1),(1043921332,r42),(2081343921,r1),(780747743,r0),(2114093192,r1),(1519071842,r0),(530454802,r1),(682276438,r0),(1324808817,r1),(75842032,r0),(261572573,r1),(1338461013,r0),(1576260743,r0),(228399955,r1),(1646357640,r0),(298496852,r1),(299275690,r3),(1098898549,r0),(186727761,r0),(986350620,r1),(1968950252,r0),(2120143302,r0),(772282514,r1),(96603454,r10),(896226313,r0),(939062994,r0),(1738685853,r1),(1535424381,r0),(1054548489,r0),(1854171348,r1),(1945543008,r0),(1663178721,r0),(315317933,r1),(1344784522,r0),(2144407381,r1),(362581878,r0),(80217591,r0),(879840450,r1),(1210324208,r0),(230044947,r0),(1347665446,r129),(367386185,r41),(237604388,r0),(1404808774,r0),(1168317434,r41),(37772729,r53),(1817186458,r41),(698536029,r53),(1527474917,r41),(797300768,r53),(1520550322,r41),(743130963,r53),(1295514198,r0),(315234937,r0),(756724421,r1),(398865472,r1),(649382053,r0),(1816586439,r0),(1577905735,r41)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f170 : ℕ := 0xa9fc
def f171 : ℕ := 0xb81c
def f172 : ℕ := 0x1eae4
def f173 : ℕ := 0x2fd78
def s103 : List ℕ := [f170,f171,f172,f173]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w72 : Wide 9 3 s103 := viaSearch (by decide +kernel)
def p67 : Weak 28 9 := signedPick 2 [2,3,10,11,13,16,18,19,21] (by decide) (by decide) (by decide)
def r130 : Rule 28 5 := cutRule 5 p67 w72
def f174 : ℕ := 0x2d2c0cfff380f
def s104 : List ℕ := [f35,f174,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b44 : Ban 28 6 s104 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1303513900,r14),(1049991021,r130),(1711508936,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p68 : Weak 28 9 := signedPick 6 [6,7,10,12,13,17,18,20,22] (by decide) (by decide) (by decide)
def r131 : Rule 28 5 := cutRule 5 p68 w72
def f175 : ℕ := 0x5634c007f38f0
def s105 : List ℕ := [f35,f20,f175,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b45 : Ban 28 6 s105 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1795066566,r14),(1555654638,r131),(388554550,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f176 : ℕ := 0x6037f303f
def f177 : ℕ := 0x181dbfc1ff
def f178 : ℕ := 0x1ec7fffe3f
def s106 : List ℕ := [f152,f176,f148,f149,f177,f178]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w73 : Wide 21 5 s106 := viaSearch (by decide +kernel)
def p69 : Weak 28 21 := relaxed (pick [0,2,3,4,6,7,11,12,13,16,17,18,19,20,21,22,23,24,25,26,27] (by decide) (by decide) (by decide))
def r132 : Rule 28 6 := cutRule 6 p69 w73
def f179 : ℕ := 0x2c0c
def f180 : ℕ := 0x7970
def f181 : ℕ := 0xbebc
def s107 : List ℕ := [f154,f179,f180,f181]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w74 : Wide 8 3 s107 := viaSearch (by decide +kernel)
def p70 : Weak 28 8 := signedPick 2 [2,3,11,13,16,18,19,21] (by decide) (by decide) (by decide)
def r133 : Rule 28 6 := cutRule 6 p70 w74
def p71 : Weak 28 8 := signedPick 6 [6,7,12,13,17,18,20,22] (by decide) (by decide) (by decide)
def r134 : Rule 28 6 := cutRule 6 p71 w74
def f182 : ℕ := 0x752700
def s108 : List ℕ := [f7,f8,f182,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w75 : Wide 12 4 s108 := viaSearch (by decide +kernel)
def r135 : Rule 28 5 := cutRule 5 p2 w75
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w76 : Wide 12 3 s108 := viaSearch (by decide +kernel)
def r136 : Rule 28 5 := cutRule 5 p2 w76
def f183 : ℕ := 0x60dbbbfe0ffff
def s109 : List ℕ := [f35,f20,f21,f183,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b46 : Ban 28 6 s109 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(467072555,r31),(958625221,r31),(2012792346,r135),(975793393,r136),(355836250,r79),(1388037732,r79),(1131287726,r8),(959233149,r8),(1851525448,r51),(625132642,r51),(549192172,r31),(1308720211,r31),(826654380,r51),(1560373256,r31),(910284915,r51),(1867621131,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f184 : ℕ := 0x7db798
def s110 : List ℕ := [f7,f8,f184,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w77 : Wide 12 4 s110 := viaSearch (by decide +kernel)
def r137 : Rule 28 5 := cutRule 5 p2 w77
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w78 : Wide 12 3 s110 := viaSearch (by decide +kernel)
def r138 : Rule 28 5 := cutRule 5 p2 w78
def r139 : Rule 28 5 := cutRule 5 p51 w48
def r140 : Rule 28 5 := cutRule 5 p52 w48
def p72 : Weak 28 8 := signedPick 0 [0,1,4,5,8,9,14,15] (by decide) (by decide) (by decide)
def r141 : Rule 28 5 := cutRule 5 p72 w39
def f185 : ℕ := 0x601899fe038ff
def s111 : List ℕ := [f35,f20,f21,f185,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b47 : Ban 28 6 s111 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(872865900,r31),(1364418566,r31),(271102044,r137),(1381586738,r138),(1768074346,r51),(1182546881,r31),(683770019,r31),(1733605407,r51),(1657177208,r8),(96508540,r8),(2125892004,r79),(901144190,r82),(918325836,r139),(954985517,r31),(448544431,r79),(1277483319,r140),(1714513556,r31),(493139365,r79),(1312814831,r51),(148873874,r141)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f186 : ℕ := 0xa40dffe07
def s112 : List ℕ := [f176,f186,f148,f149,f177]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w79 : Wide 21 5 s112 := viaSearch (by decide +kernel)
def r142 : Rule 28 6 := cutRule 6 p69 w79
def f187 : ℕ := 0x148600fe38
def s113 : List ℕ := [f176,f148,f187,f149,f177]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w80 : Wide 21 5 s113 := viaSearch (by decide +kernel)
def r143 : Rule 28 6 := cutRule 6 p69 w80
def f188 : ℕ := 0xc322000c700
def s114 : List ℕ := [f188,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b43 : Ban 28 7 s114 := viaRules (ws := [s104,s105,s109,s111]) (consBan b44 (consBan b45 (consBan b46 (consBan b47 (nilBan _ _)))))
  (dictionary [(1577905735,r41),(1593778991,r41),(483717933,r53),(1217479592,r41),(123291790,r53),(1278992510,r3),(184804708,r41),(394456418,r41),(1878695211,r41),(784507409,r53),(543743750,r41),(209326098,r0),(2051715323,r0),(277698140,r41),(1450796101,r41),(356608299,r53),(1531695843,r10),(437508041,r41),(510155642,r41),(1344219418,r41),(250031616,r53),(321811234,r41),(700878764,r0),(560751892,r0),(753252675,r41),(1755045889,r132),(718046936,r133),(1301057556,r133),(1870342181,r134),(154419562,r41),(1207715407,r53),(1380190944,r0),(1916228217,r41),(286003142,r0),(1785984289,r42),(174537915,r41),(691796487,r41),(1749787637,r0),(655599835,r0),(1317834562,r42),(207773504,r0),(519007079,r0),(1130291275,r42),(20230217,r0),(187533260,r0),(1034420729,r42),(220282531,r0),(1772744828,r42),(784127788,r0),(935949424,r42),(1578481803,r0),(329515018,r42),(515245559,r0),(1576260743,r0),(1462352202,r0),(482072941,r0),(1347665446,r129),(367386185,r41),(237604388,r0),(1404808774,r0),(254786034,r142),(1421990420,r41),(291445715,r53),(2070859444,r41),(1932488276,r41),(952209015,r53),(613943517,r143),(1781147903,r41),(1050973754,r53),(1774223308,r41),(1977083210,r41),(996803949,r53),(568907923,r41),(1990676668,r0),(1010397407,r0),(1632817719,r0),(652538458,r0),(2070259425,r53)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p73 : Weak 28 3 := signedPick 11 [11,14,15] (by decide) (by decide) (by decide)
def r144 : Rule 28 5 := cutRule 5 p73 w24
def f189 : ℕ := 0x600099fe000ff
def s115 : List ℕ := [f19,f35,f20,f21,f189,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b49 : Ban 28 6 s115 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(704976070,r144),(1397900963,r8),(1368253230,r8),(322402094,r40)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r145 : Rule 28 6 := cutRule 6 p5 w25
def p74 : Weak 28 3 := signedPick 12 [12,14,15] (by decide) (by decide) (by decide)
def r146 : Rule 28 5 := cutRule 5 p74 w26
def s116 : List ℕ := [f27,f35,f20,f21,f189,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b50 : Ban 28 6 s116 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(923898218,r146),(1728165102,r8),(976753954,r8),(100469578,r40)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r147 : Rule 28 6 := cutRule 6 p5 w27
def f190 : ℕ := 0xfffb67ffc0
def s117 : List ℕ := [f28,f29,f30,f190,f31]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w81 : Wide 21 4 s117 := viaSearch (by decide +kernel)
def r148 : Rule 28 5 := cutRule 5 p10 w81
def f191 : ℕ := 0x1ba360
def f192 : ℕ := 0x3ad718
def s118 : List ℕ := [f121,f122,f191,f192]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w82 : Wide 11 3 s118 := viaSearch (by decide +kernel)
def p75 : Weak 28 11 := signedPick 5 [5,6,7,9,10,12,13,15,17,18,20] (by decide) (by decide) (by decide)
def r149 : Rule 28 5 := cutRule 5 p75 w82
def p76 : Weak 28 11 := signedPick 1 [1,2,3,8,10,11,13,14,16,18,19] (by decide) (by decide) (by decide)
def r150 : Rule 28 5 := cutRule 5 p76 w82
def f193 : ℕ := 0xfbf8
def s119 : List ℕ := [f14,f15,f33,f193]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w83 : Wide 8 3 s119 := viaSearch (by decide +kernel)
def r151 : Rule 28 5 := cutRule 5 p11 w83
def r152 : Rule 28 5 := cutRule 5 p12 w83
def s120 : List ℕ := [f14,f127,f33,f193]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w84 : Wide 8 3 s120 := viaSearch (by decide +kernel)
def r153 : Rule 28 5 := cutRule 5 p51 w84
def r154 : Rule 28 5 := cutRule 5 p52 w84
def s121 : List ℕ := [f34,f35,f20,f21,f189,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b51 : Ban 28 6 s121 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1800844903,r148),(571456447,r8),(1171379590,r149),(634071710,r150),(1114053210,r151),(964883903,r152),(851677087,r153),(1160136568,r154)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f194 : ℕ := 0x7fb7f8
def s122 : List ℕ := [f7,f8,f9,f194,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w85 : Wide 12 4 s122 := viaSearch (by decide +kernel)
def r155 : Rule 28 6 := cutRule 6 p2 w85
def r156 : Rule 28 6 := cutRule 6 p5 w12
def r157 : Rule 28 6 := cutRule 6 p5 w13
def r158 : Rule 28 6 := cutRule 6 p5 w1
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w86 : Wide 11 4 s118 := viaSearch (by decide +kernel)
def r159 : Rule 28 6 := cutRule 6 p75 w86
def r160 : Rule 28 6 := cutRule 6 p76 w86
def p77 : Weak 28 9 := signedPick 0 [0,2,3,4,7,16,19,21,22] (by decide) (by decide) (by decide)
def r161 : Rule 28 5 := cutRule 5 p77 w57
def s123 : List ℕ := [f35,f53,f20,f21,f189,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b52 : Ban 28 6 s123 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1898757367,r31),(1114053210,r151),(459509196,r161),(2070387927,r5),(284754607,r79),(2048125637,r79)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p78 : Weak 28 9 := signedPick 0 [0,3,4,6,7,17,20,21,22] (by decide) (by decide) (by decide)
def r162 : Rule 28 5 := cutRule 5 p78 w58
def s124 : List ℕ := [f35,f20,f54,f21,f189,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b53 : Ban 28 6 s124 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(617381235,r31),(964883903,r152),(1113858178,r162),(627951264,r12),(186283302,r79),(688442537,r79)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p79 : Weak 28 9 := signedPick 0 [0,1,3,4,7,11,14,21,22] (by decide) (by decide) (by decide)
def r163 : Rule 28 5 := cutRule 5 p79 w57
def s125 : List ℕ := [f35,f67,f20,f21,f189,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b54 : Ban 28 6 s125 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(672040660,r14),(851677087,r153),(197133073,r163),(1808011804,r5),(709258436,r79),(1129582072,r79)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p80 : Weak 28 9 := signedPick 0 [0,3,4,5,7,12,15,21,22] (by decide) (by decide) (by decide)
def r164 : Rule 28 5 := cutRule 5 p80 w58
def s126 : List ℕ := [f35,f20,f71,f21,f189,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b55 : Ban 28 6 s126 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1882807807,r14),(1160136568,r154),(1309110843,r164),(823203929,r12),(1068415919,r79),(1846578954,r79)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r165 : Rule 28 5 := cutRule 5 p27 w18
def f195 : ℕ := 0x258018
def s127 : List ℕ := [f7,f195,f194,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w87 : Wide 12 3 s127 := viaSearch (by decide +kernel)
def r166 : Rule 28 5 := cutRule 5 p2 w87
def r167 : Rule 28 5 := cutRule 5 p7 w87
def p81 : Weak 28 14 := relaxed (pick [0,3,4,7,8,9,10,21,22,23,24,25,26,27] (by decide) (by decide) (by decide))
def r168 : Rule 28 5 := cutRule 5 p81 w56
def f196 : ℕ := 0x7bd8ffffff8ff
def s128 : List ℕ := [f35,f20,f21,f189,f196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b56 : Ban 28 6 s128 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(322402094,r40),(2135468089,r165),(1830373667,r165),(100469578,r40),(479537108,r165),(339410236,r165),(531911019,r40),(496705280,r166),(1079715900,r166),(1649000525,r167),(919470880,r40),(883192888,r79),(666196563,r8),(1886502678,r79),(885001941,r40),(848723949,r8),(316868889,r79),(842882227,r8),(538672456,r8),(1977742658,r79),(1646400516,r8),(306508702,r8),(888425591,r79),(676073651,r79),(1081285143,r8),(157860094,r82),(563071586,r79),(434258179,r8),(962090061,r79),(265489841,r8),(696057968,r79),(1101269460,r8),(1675807385,r79),(333251497,r8),(1269698192,r79),(1674909684,r8),(1098821393,r168),(1504032885,r79),(1062543401,r79)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s129 : List ℕ := [f35,f20,f21,f189,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b48 : Ban 28 7 s129 := viaRules (ws := [s115,s116,s121,s26,s123,s124,s125,s126,s128]) (consBan b49 (consBan b50 (consBan b51 (consBan b8 (consBan b52 (consBan b53 (consBan b54 (consBan b55 (consBan b56 (nilBan _ _))))))))))
  (dictionary [(1267235908,r0),(962141486,r0),(1335607950,r145),(1758788574,r0),(1618661702,r0),(1811162485,r147),(1775956746,r155),(211483719,r156),(780768344,r157),(14960707,r42),(1981726021,r0),(1945448029,r0),(1054548489,r0),(1018270497,r0),(16769760,r42),(2127975415,r158),(1632398347,r159),(1596120355,r42),(10928038,r42),(2122133693,r158),(1879649900,r3),(1843371908,r42),(1854201914,r42),(1817923922,r158),(1145788469,r160),(1109510477,r42),(814446327,r42),(778168335,r158),(40446848,r10),(4168856,r42),(1622038160,r42),(1585760168,r158),(1265683314,r0),(1059658317,r41),(1576916889,r0),(560881455,r41),(1078140027,r0),(1245443070,r0),(2092330539,r42),(1278192341,r0),(683170991,r42),(1324779026,r42),(1842037598,r0),(1993859234,r42),(488907966,r0),(1387424828,r42),(1055896797,r42),(1573155369,r0),(1016963580,r41),(463427016,r41),(980685588,r41),(1541627743,r41),(372778365,r0),(1539982751,r0),(1295514198,r0),(315234937,r0),(568907923,r41),(332416583,r42),(1349355525,r41),(981285607,r42),(842914439,r42),(2010118825,r41),(691574066,r42),(2108883564,r41),(684649471,r42),(887509373,r42),(2054713759,r41),(1746726260,r0),(543243882,r0),(1710448268,r0),(1551048645,r41),(901102831,r0),(2068307217,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f197 : ℕ := 0x21380001c0
def s130 : List ℕ := [f28,f197,f29,f30,f31]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w88 : Wide 21 4 s130 := viaSearch (by decide +kernel)
def r169 : Rule 28 5 := cutRule 5 p10 w88
def p82 : Weak 28 8 := signedPick 0 [0,1,2,4,5,6,8,9] (by decide) (by decide) (by decide)
def r170 : Rule 28 5 := cutRule 5 p82 w29
def s131 : List ℕ := [f34,f35,f20,f21,f22,f23,f196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b58 : Ban 28 6 s131 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(94850740,r169),(1569903895,r14),(1923837199,r31),(1846172293,r170)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s132 : List ℕ := [f7,f195,f8,f9,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w89 : Wide 12 4 s132 := viaSearch (by decide +kernel)
def r171 : Rule 28 6 := cutRule 6 p2 w89
def f198 : ℕ := 0x947f8
def f199 : ℕ := 0x1d5388
def f200 : ℕ := 0x2de5b0
def s133 : List ℕ := [f198,f4,f199,f200]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w90 : Wide 11 3 s133 := viaSearch (by decide +kernel)
def p83 : Weak 28 11 := signedPick 1 [1,2,3,10,11,13,14,16,18,19,21] (by decide) (by decide) (by decide)
def r172 : Rule 28 5 := cutRule 5 p83 w90
def f201 : ℕ := 0x29480effff80f
def s134 : List ℕ := [f35,f201,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b59 : Ban 28 6 s134 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(538485403,r14),(605298623,r7),(1384165989,r14),(1846172293,r170),(1744960642,r172),(1362948536,r7),(281837404,r14),(988947151,r7),(353000588,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p84 : Weak 28 11 := signedPick 5 [5,6,7,10,12,13,15,17,18,20,22] (by decide) (by decide) (by decide)
def r173 : Rule 28 5 := cutRule 5 p84 w90
def f202 : ℕ := 0x5290e007ff8f0
def s135 : List ℕ := [f35,f20,f202,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b60 : Ban 28 6 s135 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(800302009,r14),(1846172293,r170),(1677164306,r173),(1046385429,r7),(473341888,r14),(2076665860,r7),(155572351,r14),(1702664475,r7),(1775547949,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s136 : List ℕ := [f35,f20,f21,f22,f23,f196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b57 : Ban 28 7 s136 := viaRules (ws := [s131,s128,s134,s135]) (consBan b58 (consBan b56 (consBan b59 (consBan b60 (nilBan _ _)))))
  (dictionary [(2043143044,r0),(1708725392,r1),(1403630970,r1),(1777097434,r0),(1821210528,r0),(52794411,r1),(2060151186,r1),(105168322,r0),(69962583,r171),(652973203,r21),(1222257828,r22),(1189914226,r0),(1707172798,r1),(2018406373,r1),(1519629511,r1),(1169673982,r0),(1686932554,r1),(386336376,r0),(1719681825,r1),(1124660475,r0),(136043435,r1),(287865071,r0),(930397450,r1),(1828914312,r0),(2014644853,r1),(815912841,r0),(1983117227,r0),(1981472235,r1),(756724421,r1),(1990676668,r0),(1010397407,r0),(773906067,r41),(1790845009,r53),(1422775091,r41),(304124662,r53),(1133063550,r41),(402889401,r53),(1126138955,r41),(348719596,r53),(1551048645,r41),(901102831,r0),(2068307217,r0),(1634679180,r0),(4454105,r1),(254970686,r0),(1422175072,r0),(56471402,r0),(461682894,r1),(249330954,r0),(654542446,r1),(1878601044,r0),(136328889,r1),(1749787637,r0),(7515482,r1),(535347364,r0),(1581019299,r0),(1986230791,r1),(1538451420,r3),(1943662912,r0),(269315271,r0),(674526763,r1),(1249064688,r0),(1648780955,r0),(2053992447,r1),(1908728784,r10),(166456629,r0),(842955495,r0),(1248166987,r1),(1746726260,r0),(1016963580,r41)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f203 : ℕ := 0xa74860
def s137 : List ℕ := [f7,f8,f9,f203]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w91 : Wide 12 4 s137 := viaSearch (by decide +kernel)
def r174 : Rule 28 5 := cutRule 5 p2 w91
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w92 : Wide 12 3 s137 := viaSearch (by decide +kernel)
def r175 : Rule 28 5 := cutRule 5 p2 w92
def f204 : ℕ := 0x1bc377f9fc7ff
def s138 : List ℕ := [f204,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b62 : Ban 28 6 s138 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(512279814,r14),(47908485,r14),(128883916,r174),(1239368610,r175),(729095178,r14),(1823948473,r14),(541551891,r14),(205737524,r14),(741604205,r14),(2099803477,r14),(1483317799,r7),(1012599048,r7),(812767389,r8),(1572295428,r8),(2070508858,r7),(1424376713,r7)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f205 : ℕ := 0xf76f60
def s139 : List ℕ := [f7,f8,f9,f205]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w93 : Wide 12 4 s139 := viaSearch (by decide +kernel)
def r176 : Rule 28 5 := cutRule 5 p2 w93
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w94 : Wide 12 3 s139 := viaSearch (by decide +kernel)
def r177 : Rule 28 5 := cutRule 5 p2 w94
def r178 : Rule 28 5 := cutRule 5 p11 w69
def r179 : Rule 28 5 := cutRule 5 p12 w69
def f206 : ℕ := 0xc333f80c7ff
def s140 : List ℕ := [f206,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b63 : Ban 28 6 s140 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1931212140,r14),(1200305044,r14),(194653922,r176),(1305138616,r177),(355836250,r79),(90063325,r141),(1104253837,r178),(807374211,r14),(853960896,r7),(1005782532,r179),(18089836,r14),(585078667,r7),(1691626224,r7),(1069164621,r14),(219633998,r14),(98089793,r7),(878537395,r8),(1638065434,r8),(1080230515,r7),(2140092533,r29)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f207 : ℕ := 0x1588c
def f208 : ℕ := 0x375b0
def s141 : List ℕ := [f158,f207,f160,f208]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w95 : Wide 9 3 s141 := viaSearch (by decide +kernel)
def p85 : Weak 28 9 := signedPick 1 [1,3,8,10,11,13,14,18,21] (by decide) (by decide) (by decide)
def r180 : Rule 28 5 := cutRule 5 p85 w95
def f209 : ℕ := 0x246d0afe0ff0f
def s142 : List ℕ := [f35,f209,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b64 : Ban 28 6 s142 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2080421055,r180),(1511429531,r14),(1385633517,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p86 : Weak 28 9 := signedPick 5 [5,7,9,10,12,13,15,18,22] (by decide) (by decide) (by decide)
def r181 : Rule 28 5 := cutRule 5 p86 w95
def f210 : ℕ := 0x44b6a0060fff0
def s143 : List ℕ := [f35,f20,f210,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b65 : Ban 28 6 s143 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1904129328,r181),(1623612977,r14),(2145161556,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f211 : ℕ := 0x61b7f31ff
def s144 : List ℕ := [f152,f211,f148,f149,f150,f178]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w96 : Wide 21 5 s144 := viaSearch (by decide +kernel)
def p87 : Weak 28 21 := relaxed (pick [0,1,3,4,5,7,8,9,10,11,12,13,14,15,21,22,23,24,25,26,27] (by decide) (by decide) (by decide))
def r182 : Rule 28 6 := cutRule 6 p87 w96
def f212 : ℕ := 0xbab0
def s145 : List ℕ := [f154,f179,f156,f212]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w97 : Wide 8 3 s145 := viaSearch (by decide +kernel)
def p88 : Weak 28 8 := signedPick 1 [1,3,8,10,11,13,14,21] (by decide) (by decide) (by decide)
def r183 : Rule 28 6 := cutRule 6 p88 w97
def p89 : Weak 28 8 := signedPick 5 [5,7,9,10,12,13,15,22] (by decide) (by decide) (by decide)
def r184 : Rule 28 6 := cutRule 6 p89 w97
def s146 : List ℕ := [f211,f186,f148,f149,f150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w98 : Wide 21 5 s146 := viaSearch (by decide +kernel)
def r185 : Rule 28 6 := cutRule 6 p87 w98
def s147 : List ℕ := [f211,f148,f187,f149,f150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w99 : Wide 21 5 s147 := viaSearch (by decide +kernel)
def r186 : Rule 28 6 := cutRule 6 p87 w99
def r187 : Rule 28 6 := cutRule 6 p81 w56
def f213 : ℕ := 0x1b004401f0000
def s148 : List ℕ := [f35,f213,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b61 : Ban 28 7 s148 := viaRules (ws := [s138,s140,s142,s143]) (consBan b62 (consBan b63 (consBan b64 (consBan b65 (nilBan _ _)))))
  (dictionary [(2061624290,r0),(2108976833,r1),(1173860132,r0),(16446531,r0),(63799074,r1),(1344784522,r0),(1392137065,r1),(1239630138,r0),(82216537,r0),(129569080,r1),(1685284095,r0),(1350866443,r1),(1045772021,r1),(1419238485,r0),(1867316150,r0),(1914668693,r1),(58072965,r3),(105425508,r0),(1407080542,r0),(1070953864,r0),(1118306407,r1),(1463351579,r0),(1842419109,r1),(1702292237,r1),(1894793020,r0),(1003817379,r0),(1051169922,r1),(1504203015,r10),(1551555558,r0),(211762718,r0),(496938473,r0),(544291016,r1),(749102587,r182),(1859587281,r183),(295114254,r183),(864398879,r184),(1349313849,r1),(1143288852,r41),(1660547424,r1),(644511990,r41),(1161770562,r1),(1329073605,r1),(2104585209,r0),(1634679180,r0),(4454105,r1),(1658702502,r185),(28477427,r0),(1361822876,r1),(766801526,r0),(1408409561,r0),(1925668133,r1),(1560231197,r186),(2077489769,r0),(572538501,r1),(1471055363,r0),(1139527332,r0),(1656785904,r1),(458053892,r0),(1625258278,r0),(1623613286,r1),(398865472,r1),(1632817719,r0),(652538458,r0),(1663095725,r42),(543243882,r0),(1710448268,r0),(416047118,r42),(1432986060,r41),(1064916142,r42),(2093749360,r41),(775204601,r42),(45030452,r41),(768280006,r42),(2138344294,r41),(1527336812,r187),(547057551,r41),(2044595384,r0),(1064316123,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f214 : ℕ := 0xb54b00
def s149 : List ℕ := [f7,f8,f9,f214]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w100 : Wide 12 4 s149 := viaSearch (by decide +kernel)
def r188 : Rule 28 5 := cutRule 5 p2 w100
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w101 : Wide 12 3 s149 := viaSearch (by decide +kernel)
def r189 : Rule 28 5 := cutRule 5 p2 w101
def f215 : ℕ := 0x18db77f98ffff
def s150 : List ℕ := [f215,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b67 : Ban 28 6 s150 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1386090764,r31),(629128885,r31),(195297594,r188),(1305782288,r189),(1203990216,r51),(258010040,r51),(808017883,r8),(18733508,r8),(1071453285,r31),(1890362151,r31),(1992544126,r31),(50126379,r31),(879181067,r31),(1638709106,r31),(639384703,r51),(723015238,r51)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f216 : ℕ := 0xbf5be0
def s151 : List ℕ := [f7,f8,f9,f216]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w102 : Wide 12 4 s151 := viaSearch (by decide +kernel)
def r190 : Rule 28 5 := cutRule 5 p2 w102
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w103 : Wide 12 3 s151 := viaSearch (by decide +kernel)
def r191 : Rule 28 5 := cutRule 5 p2 w103
def f217 : ℕ := 0xf5e0
def s152 : List ℕ := [f14,f127,f217]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w104 : Wide 8 3 s152 := viaSearch (by decide +kernel)
def r192 : Rule 28 5 := cutRule 5 p51 w104
def r193 : Rule 28 5 := cutRule 5 p52 w104
def f218 : ℕ := 0x180355f9807ff
def s153 : List ℕ := [f218,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b68 : Ban 28 6 s153 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1407751724,r31),(744946929,r31),(714548192,r190),(1825032886,r191),(64036847,r51),(1625993029,r31),(1381378957,r31),(1294519210,r51),(1327268481,r8),(537984106,r8),(1742706514,r79),(1344590338,r124),(1361771984,r192),(1398431665,r31),(891990579,r51),(1720929467,r193),(10476057,r31),(936585513,r51),(950178971,r51),(592320022,r69)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f219 : ℕ := 0xb1fc
def f220 : ℕ := 0x1faec
def f221 : ℕ := 0x2f570
def s154 : List ℕ := [f219,f171,f220,f221]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w105 : Wide 9 3 s154 := viaSearch (by decide +kernel)
def p90 : Weak 28 9 := signedPick 2 [2,3,8,10,13,16,18,19,21] (by decide) (by decide) (by decide)
def r194 : Rule 28 5 := cutRule 5 p90 w105
def f222 : ℕ := 0x2d250cfff070f
def s155 : List ℕ := [f35,f222,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b69 : Ban 28 6 s155 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(330457549,r194),(1314470333,r14),(778696874,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p91 : Weak 28 9 := signedPick 6 [6,7,9,10,13,17,18,20,22] (by decide) (by decide) (by decide)
def r195 : Rule 28 5 := cutRule 5 p91 w105
def f223 : ℕ := 0x5626c007f07f0
def s156 : List ℕ := [f35,f20,f223,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b70 : Ban 28 6 s156 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1762386381,r195),(525185958,r14),(966234778,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p92 : Weak 28 21 := relaxed (pick [0,2,3,4,6,7,8,9,10,16,17,18,19,20,21,22,23,24,25,26,27] (by decide) (by decide) (by decide))
def r196 : Rule 28 6 := cutRule 6 p92 w96
def p93 : Weak 28 8 := signedPick 2 [2,3,8,10,16,18,19,21] (by decide) (by decide) (by decide)
def r197 : Rule 28 6 := cutRule 6 p93 w97
def p94 : Weak 28 8 := signedPick 6 [6,7,9,10,17,18,20,22] (by decide) (by decide) (by decide)
def r198 : Rule 28 6 := cutRule 6 p94 w97
def r199 : Rule 28 6 := cutRule 6 p92 w98
def r200 : Rule 28 6 := cutRule 6 p92 w99
def f224 : ℕ := 0xd822000f800
def s157 : List ℕ := [f224,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b66 : Ban 28 7 s157 := viaRules (ws := [s150,s153,s155,s156]) (consBan b67 (consBan b68 (consBan b69 (consBan b70 (nilBan _ _)))))
  (dictionary [(154419562,r41),(1619493072,r53),(82860209,r0),(510511130,r41),(1547933719,r0),(602110807,r41),(1029761728,r41),(2067184317,r53),(605703575,r0),(2070777085,r0),(423131262,r41),(1888204772,r53),(1177202918,r3),(494792781,r41),(2020905668,r41),(743602412,r41),(61192275,r53),(955521415,r41),(621103763,r0),(316009341,r0),(689475805,r41),(862630161,r41),(180220024,r53),(659845716,r10),(2124919226,r41),(1499613535,r41),(1597604970,r41),(915194833,r53),(733588899,r41),(1112656429,r0),(972529557,r0),(1165030340,r41),(19339907,r196),(1129824601,r197),(1712835221,r197),(134636199,r198),(1663095725,r42),(463427016,r41),(980685588,r41),(102292597,r41),(619551169,r0),(930784744,r0),(432007882,r0),(82052353,r41),(599310925,r0),(1446198394,r42),(632060196,r0),(37038846,r42),(1195905453,r0),(1347727089,r42),(1990259468,r0),(741292683,r42),(927023224,r0),(2104585209,r0),(254970686,r0),(1422175072,r0),(895495598,r53),(1874129867,r0),(893850606,r0),(649382053,r0),(1816586439,r0),(2070259425,r53),(666563699,r199),(1833768085,r41),(703223380,r53),(335153462,r41),(196782294,r41),(1363986680,r53),(1025721182,r200),(45441921,r41),(1462751419,r53),(38517326,r41),(241377228,r41),(1408581614,r53),(1527336812,r187),(547057551,r41),(2044595384,r0),(1064316123,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w106 : Wide 9 4 s3 := viaSearch (by decide +kernel)
def r201 : Rule 28 6 := cutRule 6 p3 w106
def f225 : ℕ := 0xfcf8
def s158 : List ℕ := [f14,f15,f16,f225]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w107 : Wide 8 3 s158 := viaSearch (by decide +kernel)
def r202 : Rule 28 6 := cutRule 6 p4 w107
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w108 : Wide 8 4 s158 := viaSearch (by decide +kernel)
def r203 : Rule 28 6 := cutRule 6 p4 w108
def r204 : Rule 28 6 := cutRule 6 p9 w108
def f226 : ℕ := 0x6098b906038f0
def s159 : List ℕ := [f35,f20,f21,f226,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b72 : Ban 28 6 s159 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1314470333,r14),(1035999529,r59)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f227 : ℕ := 0xfaf8
def s160 : List ℕ := [f14,f15,f33,f227]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w109 : Wide 8 4 s160 := viaSearch (by decide +kernel)
def r205 : Rule 28 6 := cutRule 6 p12 w109
def f228 : ℕ := 0x7300d906700f0
def s161 : List ℕ := [f35,f20,f21,f22,f228,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b73 : Ban 28 6 s161 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1385633517,r31),(999468003,r120)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f229 : ℕ := 0xf9f8
def s162 : List ℕ := [f14,f127,f33,f229]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w110 : Wide 8 4 s162 := viaSearch (by decide +kernel)
def r206 : Rule 28 6 := cutRule 6 p52 w110
def s163 : List ℕ := [f19,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b71 : Ban 28 7 s163 := viaRules (ws := [s159,s5,s161,s67,s115]) (consBan b72 (consBan b2 (consBan b73 (consBan b26 (consBan b49 (nilBan _ _))))))
  (dictionary [(1371885942,r3),(273021188,r3),(1310443777,r3),(998419478,r0),(1473582229,r0),(936977313,r0),(741254062,r201),(204649146,r3),(1778676651,r0),(1242071735,r0),(1369480801,r42),(1308038636,r202),(2134896681,r10),(2073454516,r202),(1511720733,r203),(1450278568,r202),(1645641073,r10),(1584198908,r202),(317134282,r204),(1354556871,r204),(1733624401,r0),(556074940,r203),(1593497529,r0),(1785998312,r202),(1176912795,r203),(640307879,r203),(1750792573,r3),(722924462,r203),(186319546,r3),(755604171,r202),(478542141,r2),(417099976,r202),(1951437527,r0),(1889995362,r0),(42449015,r203),(174696088,r0),(113253923,r0),(1240519141,r0),(1551752716,r0),(15553265,r54),(1052975854,r0),(1220278897,r0),(1253028168,r0),(658006818,r3),(1816873425,r0),(1968695061,r205),(463743793,r0),(1362260655,r202),(1547991196,r0),(794482149,r86),(733039984,r202),(424251961,r41),(362809796,r41),(640923848,r203),(1217479592,r41),(1156037427,r41),(1516463570,r41),(1514818578,r0),(1400131822,r115),(290070764,r0),(543743750,r41),(1324191352,r41),(956121434,r3),(1984954652,r41),(666409893,r206),(2083719391,r41),(659485298,r202),(2029549586,r41),(2043143044,r0),(1685284095,r0),(955521415,r41)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r207 : Rule 28 6 := cutRule 6 p2 w5
def f230 : ℕ := 0x210ff8
def f231 : ℕ := 0x3d23c0
def f232 : ℕ := 0xefdcf8
def s164 : List ℕ := [f230,f231,f232]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w111 : Wide 12 4 s164 := viaSearch (by decide +kernel)
def r208 : Rule 28 5 := cutRule 5 p39 w111
def r209 : Rule 28 5 := cutRule 5 p2 w3
def f233 : ℕ := 0x14a66007ffff0
def s165 : List ℕ := [f233,f35,f20,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b75 : Ban 28 6 s165 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1212412666,r14),(224412325,r5),(548323437,r208),(11718521,r209),(1585746026,r7),(1049141110,r7),(714723458,r14),(642798179,r7),(268552109,r14),(232632278,r7),(1051554849,r14),(1024404439,r14),(525627577,r14),(692930620,r14),(725679891,r14),(130658541,r7),(1589573299,r51),(1955313705,r31),(808987540,r51),(18125781,r31),(987470301,r14),(1910206134,r14),(16395473,r7),(796843075,r31),(428773157,r51),(1074305283,r7),(1515794767,r14),(1157935818,r14),(428173138,r7)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f234 : ℕ := 0x5850
def f235 : ℕ := 0x58fc
def f236 : ℕ := 0x7d3c
def f237 : ℕ := 0xdecc
def s166 : List ℕ := [f234,f235,f236,f237]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w112 : Wide 8 4 s166 := viaSearch (by decide +kernel)
def p95 : Weak 28 8 := signedPick 5 [5,6,9,10,13,15,18,20] (by decide) (by decide) (by decide)
def r210 : Rule 28 6 := cutRule 6 p95 w112
def f238 : ℕ := 0x48b49f
def f239 : ℕ := 0x8a58e7
def f240 : ℕ := 0xd06f07
def s167 : List ℕ := [f7,f238,f239,f240]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w113 : Wide 12 3 s167 := viaSearch (by decide +kernel)
def p96 : Weak 28 12 := relaxed (pick [5,6,7,9,10,12,13,15,17,18,20,22] (by decide) (by decide) (by decide))
def r211 : Rule 28 5 := cutRule 5 p96 w113
def f241 : ℕ := 0x29491ff80000f
def s168 : List ℕ := [f35,f241,f20,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b76 : Ban 28 6 s168 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(374418400,r14),(1656106281,r14),(1280224607,r211),(2062620198,r14),(1667062714,r14),(1988500631,r31),(1738225898,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f242 : ℕ := 0x20c83bfe0f8ff
def s169 : List ℕ := [f35,f242,f20,f21,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b77 : Ban 28 6 s169 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(238644253,r209),(941649190,r14),(1473059750,r14),(1433201856,r14),(163321248,r14),(1450370028,r5),(1023768807,r31),(1783296846,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f243 : ℕ := 0x1d274401f0700
def s170 : List ℕ := [f35,f243,f20,f21,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b78 : Ban 28 6 s170 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1679311653,r14),(23380672,r14),(2085825570,r14),(40548844,r5),(1761431270,r31),(373475662,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f244 : ℕ := 0x39005dfff00ff
def s171 : List ℕ := [f35,f20,f244,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b79 : Ban 28 6 s171 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1351026730,r209),(2054031667,r14),(1391747447,r31),(398100686,r14),(415268858,r5),(748195676,r31),(2064988100,r14),(1275703725,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f245 : ℕ := 0x4ef22000ff00
def s172 : List ℕ := [f245,f35,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b80 : Ban 28 6 s172 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(489677313,r14),(822071663,r31),(981229979,r14),(998398151,r5),(500633746,r14),(1858833018,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f246 : ℕ := 0x3def7ffffffff
def s173 : List ℕ := [f35,f20,f246,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b74 : Ban 28 7 s173 := viaRules (ws := [s165,s168,s169,s170,s171,s172]) (consBan b75 (consBan b76 (consBan b77 (consBan b78 (consBan b79 (consBan b80 (nilBan _ _)))))))
  (dictionary [(741254062,r201),(204649146,r3),(1778676651,r0),(1242071735,r0),(1712620719,r0),(602559661,r1),(1512631041,r0),(976026125,r0),(998419478,r0),(1371885942,r3),(1020139219,r0),(1399206749,r1),(1259079877,r1),(1451580660,r0),(305890227,r3),(1416374921,r207),(1999385541,r207),(421186519,r3),(624676361,r210),(714723458,r0),(228816544,r0),(1716020371,r0),(1320160554,r1),(814194579,r0),(418334762,r1),(1566059184,r10),(1656106281,r0),(1170199367,r0),(906101489,r1),(1217335064,r1),(718558202,r1),(885861245,r1),(1732748714,r0),(918610516,r1),(323589166,r0),(1482455773,r1),(1854767579,r0),(941649190,r0),(1458907762,r1),(2051306595,r0),(1655446778,r1),(322656105,r0),(2074279935,r1),(444946395,r0),(1679311653,r0),(49086578,r1),(1634277409,r0),(129326141,r1),(1027843003,r0),(1213573544,r1),(1182045918,r0),(1180400926,r1),(2103136759,r1),(209326098,r0),(2120318405,r41),(989773700,r53),(621703782,r41),(1650537000,r53),(1469612223,r41),(2054031667,r0),(1073752406,r0),(577520915,r0),(181661098,r1),(186727761,r0),(1938351591,r1),(2052741516,r41),(489677313,r0),(1656881699,r0),(331992241,r41),(1749301739,r53),(325067646,r41),(1695131934,r53),(1267235908,r0),(1708725392,r1),(1350866443,r1),(621103763,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f247 : ℕ := 0x269c
def s174 : List ℕ := [f247,f55,f57]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w114 : Wide 7 4 s174 := viaSearch (by decide +kernel)
def r212 : Rule 28 6 := cutRule 6 p20 w114
def r213 : Rule 28 5 := cutRule 5 p4 w107
def r214 : Rule 28 5 := cutRule 5 p9 w107
def f248 : ℕ := 0x252c080673800
def s175 : List ℕ := [f34,f35,f248,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b82 : Ban 28 6 s175 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(62826280,r14),(21826019,r14),(1176912795,r213),(1313389096,r214)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s176 : List ℕ := [f35,f248,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b81 : Ban 28 7 s176 := viaRules (ws := [s175]) (consBan b82 (nilBan _ _))
  (dictionary [(1712620719,r0),(1303513900,r0),(602559661,r1),(1473582229,r0),(936977313,r0),(170114030,r212),(1780992761,r3),(1207536619,r0),(670931703,r0),(1637931552,r203),(1825105855,r204),(715044797,r0),(1094112327,r1),(2064046513,r0),(953985455,r1),(1146486238,r0),(1518297102,r0),(817342863,r1),(888518462,r10),(187564223,r0),(1522499979,r204),(821545740,r0),(21826019,r0),(1468355427,r1),(1111280499,r3),(1694291119,r3),(116092097,r22),(1711068125,r0),(601007067,r1),(912240642,r1),(1523524838,r0),(413463780,r1),(580766823,r1),(1723474098,r0),(1022519859,r1),(1254011594,r0),(553057355,r1),(1620580772,r0),(919626533,r1),(1764038882,r0),(1063084643,r1),(1427654292,r0),(613516094,r1),(18494744,r0),(1177361351,r1),(1329182987,r0),(1971715366,r1),(722748581,r0),(908479122,r1),(1987012554,r41),(876951496,r0),(875306504,r1),(760619748,r0),(1798042337,r1),(2051715323,r0),(1646357640,r0),(945403401,r1),(1320932788,r41),(619978549,r0),(960696613,r41),(259742374,r0),(1287305436,r0),(586351197,r1),(1815223983,r41),(684679278,r53),(316609360,r41),(1345442578,r53),(26897819,r41),(1444207317,r53),(19973224,r41),(1390037512,r53),(962141486,r0),(1403630970,r1),(1045772021,r1),(316009341,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f249 : ℕ := 0x46348007fff00
def s177 : List ℕ := [f35,f20,f249,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b84 : Ban 28 6 s177 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1795066566,r14),(814194579,r14),(1927264067,r5),(1951415372,r14),(1226707535,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r215 : Rule 28 6 := cutRule 6 p9 w107
def f250 : ℕ := 0xb74ff8
def s178 : List ℕ := [f7,f8,f9,f10,f250]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w115 : Wide 12 4 s178 := viaSearch (by decide +kernel)
def r216 : Rule 28 6 := cutRule 6 p2 w115
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w116 : Wide 8 3 s166 := viaSearch (by decide +kernel)
def r217 : Rule 28 5 := cutRule 5 p95 w116
def f251 : ℕ := 0x4a00ff8
def f252 : ℕ := 0x917f49f
def f253 : ℕ := 0x114bf8e7
def f254 : ℕ := 0x1a0dff07
def s179 : List ℕ := [f251,f252,f253,f254]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w117 : Wide 17 3 s179 := viaSearch (by decide +kernel)
def p97 : Weak 28 17 := relaxed (pick [1,2,3,8,10,11,13,14,16,18,19,21,23,24,25,26,27] (by decide) (by decide) (by decide))
def r218 : Rule 28 5 := cutRule 5 p97 w117
def f255 : ℕ := 0x89007ff8
def f256 : ℕ := 0x110bf911f
def f257 : ℕ := 0x6165fe1e7
def f258 : ℕ := 0x7606ffe07
def s180 : List ℕ := [f255,f256,f257,f258]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w118 : Wide 20 3 s180 := viaSearch (by decide +kernel)
def p98 : Weak 28 20 := relaxed (pick [1,2,3,8,10,11,12,13,14,16,17,18,19,21,22,23,24,25,26,27] (by decide) (by decide) (by decide))
def r219 : Rule 28 5 := cutRule 5 p98 w118
def f259 : ℕ := 0x424001fffc0
def f260 : ℕ := 0x18c36fe631ff
def f261 : ℕ := 0x60d8b7f83e3f
def f262 : ℕ := 0x7b00dbffc03f
def s181 : List ℕ := [f259,f260,f261,f262]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w119 : Wide 26 4 s181 := viaSearch (by decide +kernel)
def p99 : Weak 28 26 := relaxed (pick [1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] (by decide) (by decide) (by decide))
def r220 : Rule 28 5 := cutRule 5 p99 w119
def f263 : ℕ := 0x3f807
def f264 : ℕ := 0x12007f8
def f265 : ℕ := 0x61dfe3f
def f266 : ℕ := 0x6c6ffc7
def s182 : List ℕ := [f263,f264,f265,f266]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w120 : Wide 16 3 s182 := viaSearch (by decide +kernel)
def p100 : Weak 28 16 := relaxed (pick [1,2,3,11,12,13,16,17,18,21,22,23,24,25,26,27] (by decide) (by decide) (by decide))
def r221 : Rule 28 5 := cutRule 5 p100 w120
def f267 : ℕ := 0x4487ff8
def f268 : ℕ := 0x8858007
def f269 : ℕ := 0x885911f
def f270 : ℕ := 0x30b2e1e7
def f271 : ℕ := 0x3b037e07
def s183 : List ℕ := [f267,f268,f269,f270,f271]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w121 : Wide 15 4 s183 := viaSearch (by decide +kernel)
def p101 : Weak 28 15 := relaxed (pick [5,6,7,9,10,11,12,13,15,16,17,18,20,21,22] (by decide) (by decide) (by decide))
def r222 : Rule 28 5 := cutRule 5 p101 w121
def f272 : ℕ := 0x17e07
def f273 : ℕ := 0x2401f8
def f274 : ℕ := 0x42ff1f
def f275 : ℕ := 0x59bfe7
def s184 : List ℕ := [f272,f273,f274,f275]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w122 : Wide 14 3 s184 := viaSearch (by decide +kernel)
def p102 : Weak 28 14 := relaxed (pick [1,2,3,8,10,16,17,18,19,23,24,25,26,27] (by decide) (by decide) (by decide))
def r223 : Rule 28 5 := cutRule 5 p102 w122
def f276 : ℕ := 0x1be07
def f277 : ℕ := 0x597fe7
def s185 : List ℕ := [f276,f273,f274,f277]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w123 : Wide 14 3 s185 := viaSearch (by decide +kernel)
def p103 : Weak 28 14 := relaxed (pick [1,2,3,8,10,11,12,13,14,23,24,25,26,27] (by decide) (by decide) (by decide))
def r224 : Rule 28 5 := cutRule 5 p103 w123
def f278 : ℕ := 0x10827100000f0
def s186 : List ℕ := [f34,f278,f35,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b85 : Ban 28 6 s186 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1301530149,r217),(2010320249,r14),(1176912795,r213),(2092645740,r218),(1701848176,r219),(1874220435,r12),(952520383,r220),(1113399418,r221),(1544840859,r222),(1727537608,r223),(425252440,r224)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w124 : Wide 17 4 s179 := viaSearch (by decide +kernel)
def r225 : Rule 28 6 := cutRule 6 p97 w124
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w125 : Wide 8 3 s160 := viaSearch (by decide +kernel)
def r226 : Rule 28 5 := cutRule 5 p12 w125
def f279 : ℕ := 0x60588afe0f80f
def s187 : List ℕ := [f35,f20,f21,f279,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b86 : Ban 28 6 s187 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(809897839,r12),(337382334,r5),(1053049227,r226)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r227 : Rule 28 6 := cutRule 6 p12 w125
def f280 : ℕ := 0x75aff8
def s188 : List ℕ := [f7,f8,f9,f280,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w126 : Wide 12 4 s188 := viaSearch (by decide +kernel)
def r228 : Rule 28 6 := cutRule 6 p2 w126
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w127 : Wide 8 3 s162 := viaSearch (by decide +kernel)
def r229 : Rule 28 5 := cutRule 5 p52 w127
def f281 : ℕ := 0x6b008cfff000f
def s189 : List ℕ := [f35,f20,f21,f22,f281,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b87 : Ban 28 6 s189 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(225578093,r12),(1205948390,r5),(548166931,r229)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r230 : Rule 28 6 := cutRule 6 p52 w127
def f282 : ℕ := 0x2f9ff8
def s190 : List ℕ := [f7,f8,f282,f9,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w128 : Wide 12 4 s190 := viaSearch (by decide +kernel)
def r231 : Rule 28 6 := cutRule 6 p2 w128
def s191 : List ℕ := [f278,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b83 : Ban 28 7 s191 := viaRules (ws := [s177,s186,s187,s189]) (consBan b84 (consBan b85 (consBan b86 (consBan b87 (nilBan _ _)))))
  (dictionary [(1637931552,r203),(273021188,r3),(1310443777,r3),(1303513900,r0),(1512631041,r0),(976026125,r0),(170114030,r212),(1780992761,r3),(1207536619,r0),(670931703,r0),(2004447794,r3),(1676960019,r207),(187755545,r10),(2007751417,r3),(1001008357,r3),(927632226,r3),(600144451,r207),(1088511261,r215),(1467578791,r0),(1327451919,r0),(1519952702,r216),(374262269,r3),(1484746963,r207),(456878852,r225),(2067757583,r207),(489558561,r3),(1229012333,r3),(901524558,r207),(1122931047,r0),(795443272,r0),(912056515,r3),(681937832,r0),(354450057,r0),(974473531,r0),(1285707106,r0),(786930244,r0),(954233287,r0),(1801120756,r3),(986982558,r0),(391961208,r207),(1550827815,r0),(1702649451,r227),(197698183,r0),(1096215045,r228),(1281945586,r0),(1700806012,r3),(1373318237,r207),(721275919,r41),(393788144,r41),(211921554,r3),(1878695211,r41),(1551207436,r41),(1250417960,r41),(1248772968,r0),(24025154,r0),(277698140,r41),(41206800,r3),(1058145742,r41),(690075824,r207),(1718909042,r41),(400364283,r230),(1817673781,r41),(393439688,r231),(1763503976,r41),(1335607950,r145),(1777097434,r0),(1419238485,r0),(689475805,r41)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r232 : Rule 28 6 := cutRule 6 p11 w125
def f283 : ℕ := 0x18837501807f0
def s192 : List ℕ := [f283,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b89 : Ban 28 6 s192 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1303513900,r14),(2112333591,r70)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r233 : Rule 28 6 := cutRule 6 p11 w109
def r234 : Rule 28 6 := cutRule 6 p17 w106
def f284 : ℕ := 0x5b00d501f00f0
def s193 : List ℕ := [f35,f20,f21,f284,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b90 : Ban 28 6 s193 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1385633517,r31),(74162392,r180)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s194 : List ℕ := [f35,f53,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b88 : Ban 28 7 s194 := viaRules (ws := [s192,s20,s73,s193,s123]) (consBan b89 (consBan b6 (consBan b29 (consBan b90 (consBan b52 (nilBan _ _))))))
  (dictionary [(478542141,r2),(907776955,r232),(304810284,r0),(734045098,r0),(1723474098,r0),(5225265,r0),(2135316178,r233),(1732748714,r0),(1427654292,r0),(1801120756,r3),(1878315590,r0),(696671673,r0),(160066757,r0),(1845233850,r204),(76817733,r0),(2084174508,r0),(129191644,r232),(1543185419,r41),(1972420233,r232),(809897839,r10),(1239132653,r232),(1420111790,r233),(1849346604,r232),(952387166,r10),(1381621980,r232),(1667589774,r233),(1130984858,r233),(93985905,r3),(1213601441,r233),(676996525,r3),(1246281150,r232),(1731196120,r0),(2042429695,r0),(1543652833,r0),(1193697304,r75),(1710955876,r0),(719448983,r3),(631425225,r3),(1148683797,r3),(1763051491,r234),(132826416,r0),(1226446575,r3),(1743705147,r0),(1942113468,r205),(311888393,r205),(954420772,r0),(1852937634,r232),(1521409603,r233),(2038668175,r0),(2005495557,r0),(780747743,r0),(1034420729,r42),(1632398347,r159),(2061633161,r232),(1621382940,r41),(2050617754,r42),(227928999,r233),(423131262,r41),(852366076,r42),(1814868331,r42),(1446798413,r3),(328147984,r42),(1157086872,r206),(426912723,r42),(1150162277,r232),(372742918,r42),(2092330539,r42),(386336376,r0),(1658702502,r185),(28477427,r0),(1446198394,r42)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f285 : ℕ := 0x8c137f98c7ff
def s195 : List ℕ := [f285,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b92 : Ban 28 6 s195 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1489486300,r14),(1449628406,r14),(1466796578,r5),(1265911799,r209),(969032173,r14),(179747798,r14),(1040195357,r8),(1799723396,r8)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f286 : ℕ := 0x653c880673800
def s196 : List ℕ := [f20,f21,f22,f286,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b93 : Ban 28 6 s196 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1383633803,r5),(885869398,r14),(96585023,r14),(1740708731,r14),(957032582,r31),(1716560621,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r235 : Rule 28 5 := cutRule 5 p45 w111
def f287 : ℕ := 0x44b4a007ffff0
def s197 : List ℕ := [f35,f20,f287,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b94 : Ban 28 6 s197 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1126612875,r14),(1194984917,r7),(748756079,r7),(74435289,r14),(1963788255,r14),(44429556,r7),(1073900205,r5),(1436293856,r14),(937516994,r14),(1104820037,r14),(1971053850,r235),(340828775,r7),(1434448934,r209),(1951707506,r7),(1137569308,r14),(1505049950,r14),(1401004710,r7),(1399359718,r14),(174611904,r14),(428284890,r7),(1208732492,r8),(840662574,r79),(1775318650,r79),(1757004259,r8),(150673458,r79),(828513959,r8),(1927684184,r14),(1569825235,r14),(840062555,r7)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f288 : ℕ := 0x5444
def f289 : ℕ := 0x54fc
def f290 : ℕ := 0xded8
def s198 : List ℕ := [f288,f289,f236,f290]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w129 : Wide 8 4 s198 := viaSearch (by decide +kernel)
def p104 : Weak 28 8 := signedPick 5 [5,7,10,12,13,15,18,22] (by decide) (by decide) (by decide)
def r236 : Rule 28 6 := cutRule 6 p104 w129
def f291 : ℕ := 0x69009dfff00ff
def s199 : List ℕ := [f35,f20,f21,f22,f291]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b95 : Ban 28 6 s199 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(388342910,r14),(879895576,r14),(897063748,r5),(696178969,r209),(399299343,r14),(1757498615,r14),(1243240695,r8),(1229990566,r8)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f292 : ℕ := 0x4fd22000ff00
def s200 : List ℕ := [f292,f35,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b96 : Ban 28 6 s200 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1495363242,r14),(1827757592,r31),(1986915908,r14),(2004084080,r5),(1506319675,r14),(717035300,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f293 : ℕ := 0x6dfdbffffffff
def s201 : List ℕ := [f35,f20,f21,f22,f293,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b91 : Ban 28 7 s201 := viaRules (ws := [s195,s196,s197,s168,s199,s200]) (consBan b92 (consBan b93 (consBan b94 (consBan b76 (consBan b95 (consBan b96 (nilBan _ _)))))))
  (dictionary [(1253028168,r0),(918610516,r1),(613516094,r1),(986982558,r0),(1031095652,r0),(1410163182,r1),(1270036310,r1),(1462537093,r0),(316846660,r3),(1427331354,r207),(2010341974,r207),(432142952,r3),(917057922,r1),(1228291497,r1),(729514635,r1),(896817678,r1),(1763051491,r234),(132826416,r0),(1226446575,r3),(1743705147,r0),(871150515,r0),(334545599,r0),(976153634,r0),(1493412206,r1),(1645233842,r0),(140282574,r1),(1038799436,r0),(1224529977,r1),(969032173,r0),(243874499,r0),(2006454762,r1),(2051306595,r0),(1666403211,r1),(885869398,r0),(160711724,r0),(1923291987,r1),(681937832,r0),(297034448,r1),(719448983,r3),(1137569308,r0),(1036565778,r236),(651662394,r0),(1716020371,r0),(1331116987,r1),(1667062714,r0),(1566059184,r10),(1181155800,r0),(1628294602,r0),(1243391218,r1),(1878315590,r0),(1193002351,r0),(1191357359,r1),(2114093192,r1),(220282531,r0),(2131274838,r42),(1000730133,r158),(632660215,r42),(1661493433,r158),(342948674,r42),(1760258172,r158),(336024079,r42),(1706088367,r158),(1278192341,r0),(1719681825,r1),(1361822876,r1),(632060196,r0),(1951407113,r42),(399299343,r0),(1566503729,r0),(1581019299,r0),(1196115915,r1),(1070953864,r0),(686050480,r1),(910943798,r41),(1506319675,r0),(526040414,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r237 : Rule 28 5 := cutRule 5 p11 w125
def f294 : ℕ := 0xd250401f0700
def s202 : List ℕ := [f34,f294,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b98 : Ban 28 6 s202 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1710027817,r14),(1667589774,r237),(1343634276,r14),(1180103768,r226)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r238 : Rule 28 6 := cutRule 6 p22 w114
def s203 : List ℕ := [f294,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b97 : Ban 28 7 s203 := viaRules (ws := [s202]) (consBan b98 (nilBan _ _))
  (dictionary [(174696088,r0),(353637961,r1),(382234468,r0),(561176341,r1),(547706882,r0),(726648755,r1),(1764038882,r0),(1942980755,r1),(2128608531,r233),(696671673,r0),(160066757,r0),(1816873425,r0),(1482455773,r1),(1177361351,r1),(1550827815,r0),(1550552202,r0),(1729494075,r1),(1592445479,r10),(1771387352,r0),(1454379567,r205),(1633321440,r0),(1710027817,r0),(1888969690,r1),(1594940909,r0),(1974008439,r1),(1833881567,r1),(2026382350,r0),(1991176611,r3),(426703584,r3),(995988209,r22),(1314470333,r0),(976153634,r0),(1493412206,r1),(963644607,r0),(1480903179,r1),(1792136754,r1),(1293359892,r1),(943404363,r0),(1460662935,r1),(917737200,r238),(1434995772,r0),(381132284,r3),(898390856,r0),(1691820527,r205),(61595452,r0),(704127831,r1),(1602644693,r0),(1271116662,r0),(1788375234,r1),(1867316150,r0),(2046258023,r1),(1512996720,r41),(1691938593,r0),(300519121,r42),(479460994,r0),(269315271,r0),(448257144,r1),(1756847608,r0),(1755202616,r1),(530454802,r1),(784127788,r0),(547636448,r42),(1564575390,r158),(1196505472,r42),(77855043,r158),(906793931,r42),(176619782,r158),(899869336,r42),(122449977,r158),(1324779026,r42),(1842037598,r0),(136043435,r1),(1408409561,r0),(1925668133,r1),(1195905453,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f295 : ℕ := 0x184346f98c70f
def s204 : List ℕ := [f295,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b100 : Ban 28 6 s204 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1625269659,r5),(2134896681,r12),(1737754795,r214)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w130 : Wide 8 3 s198 := viaSearch (by decide +kernel)
def r239 : Rule 28 5 := cutRule 5 p104 w130
def f296 : ℕ := 0xfe07
def f297 : ℕ := 0x437f1f
def s205 : List ℕ := [f296,f273,f297,f275]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w131 : Wide 14 3 s205 := viaSearch (by decide +kernel)
def p105 : Weak 28 14 := relaxed (pick [1,2,3,11,13,16,17,18,21,23,24,25,26,27] (by decide) (by decide) (by decide))
def r240 : Rule 28 5 := cutRule 5 p105 w131
def f298 : ℕ := 0x8a007ff8
def f299 : ℕ := 0x311bfb13f
def f300 : ℕ := 0x4145fc1c7
def s206 : List ℕ := [f298,f299,f300,f258]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w132 : Wide 20 3 s206 := viaSearch (by decide +kernel)
def p106 : Weak 28 20 := relaxed (pick [1,2,3,8,9,10,11,13,14,16,17,18,19,20,21,23,24,25,26,27] (by decide) (by decide) (by decide))
def r241 : Rule 28 5 := cutRule 5 p106 w132
def f301 : ℕ := 0x5f807
def f302 : ℕ := 0x61bfe3f
def s207 : List ℕ := [f301,f264,f302,f266]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w133 : Wide 16 3 s207 := viaSearch (by decide +kernel)
def p107 : Weak 28 16 := relaxed (pick [1,2,3,8,9,10,16,17,18,19,20,23,24,25,26,27] (by decide) (by decide) (by decide))
def r242 : Rule 28 5 := cutRule 5 p107 w133
def f303 : ℕ := 0x4507ff8
def f304 : ℕ := 0x188db13f
def f305 : ℕ := 0x20a28007
def f306 : ℕ := 0x20a2c1c7
def s208 : List ℕ := [f303,f304,f305,f306,f271]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w134 : Wide 15 4 s208 := viaSearch (by decide +kernel)
def p108 : Weak 28 15 := relaxed (pick [5,6,7,8,9,10,12,13,15,16,17,18,19,20,22] (by decide) (by decide) (by decide))
def r243 : Rule 28 5 := cutRule 5 p108 w134
def f307 : ℕ := 0x2801f8
def f308 : ℕ := 0x46ff3f
def f309 : ℕ := 0x517fc7
def s209 : List ℕ := [f276,f307,f308,f309]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w135 : Wide 14 3 s209 := viaSearch (by decide +kernel)
def p109 : Weak 28 14 := relaxed (pick [1,2,3,8,9,10,11,13,14,23,24,25,26,27] (by decide) (by decide) (by decide))
def r244 : Rule 28 5 := cutRule 5 p109 w135
def f310 : ℕ := 0x4090b100000f0
def s210 : List ℕ := [f34,f35,f310,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b101 : Ban 28 6 s210 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1714596544,r239),(1440208781,r218),(460962459,r240),(2139664671,r241),(1874220435,r12),(952520383,r220),(1238631157,r14),(1667589774,r237),(1075100649,r242),(468666243,r243),(1920299128,r244)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f311 : ℕ := 0x16264007fff00
def s211 : List ℕ := [f311,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b102 : Ban 28 6 s211 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1314367979,r14),(1628294602,r14),(1851878786,r5),(525185958,r14),(900138398,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f312 : ℕ := 0x3b004cfff000f
def s212 : List ℕ := [f35,f20,f312,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b103 : Ban 28 6 s212 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(225578093,r12),(239526061,r5),(1729228249,r229)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s213 : List ℕ := [f35,f20,f310,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b99 : Ban 28 7 s213 := viaRules (ws := [s204,s210,s211,s212]) (consBan b100 (consBan b101 (consBan b102 (consBan b103 (nilBan _ _)))))
  (dictionary [(658006818,r3),(323589166,r0),(18494744,r0),(391961208,r207),(1229012333,r3),(249087599,r207),(1612636472,r0),(632711738,r0),(322656105,r0),(1490215018,r0),(2078627331,r3),(871150515,r0),(1314470333,r0),(334545599,r0),(436074302,r215),(815141832,r0),(675014960,r0),(867515743,r216),(1869308957,r3),(832310004,r207),(1951925540,r225),(1415320624,r207),(1984605249,r3),(947217601,r3),(2114776514,r207),(187755545,r10),(1355314458,r3),(273186117,r3),(927632226,r3),(2095191139,r207),(322036572,r0),(633270147,r0),(134493285,r0),(301796328,r0),(631425225,r3),(1148683797,r3),(917737200,r238),(1434995772,r0),(381132284,r3),(898390856,r0),(2128608531,r233),(1050212492,r227),(1692744871,r0),(443778086,r228),(629508627,r0),(597981001,r101),(596336009,r0),(1519071842,r0),(1772744828,r42),(1536253488,r3),(405708783,r42),(37638865,r207),(1066472083,r42),(1879649900,r3),(899725166,r207),(1460094648,r41),(480169914,r42),(740545913,r3),(743602412,r41),(1911161325,r42),(1895410971,r230),(1165236822,r42),(1888486376,r231),(1111067017,r42),(683170991,r42),(1124660475,r0),(766801526,r0),(37038846,r42)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r245 : Rule 28 6 := cutRule 6 p51 w127
def f313 : ℕ := 0x10c373000c7f0
def s214 : List ℕ := [f313,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b105 : Ban 28 6 s214 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1303513900,r14),(708967808,r130)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r246 : Rule 28 6 := cutRule 6 p51 w110
def f314 : ℕ := 0x40d8b3000f8f0
def s215 : List ℕ := [f35,f20,f314,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b106 : Ban 28 6 s215 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1314470333,r14),(962598024,r194)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w136 : Wide 9 4 s78 := viaSearch (by decide +kernel)
def r247 : Rule 28 6 := cutRule 6 p56 w136
def s216 : List ℕ := [f35,f67,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b104 : Ban 28 7 s216 := viaRules (ws := [s214,s28,s215,s79,s125]) (consBan b105 (consBan b9 (consBan b106 (consBan b32 (consBan b54 (nilBan _ _))))))
  (dictionary [(794482149,r86),(1611286654,r245),(1875523038,r0),(544843896,r41),(1646357640,r0),(315678498,r41),(1880709973,r246),(2120318405,r41),(1815223983,r41),(41206800,r3),(2046396817,r41),(1252322591,r41),(715717675,r41),(85319894,r204),(464387424,r41),(324260552,r41),(516761335,r245),(1840898199,r0),(510219057,r245),(225578093,r10),(1042382598,r245),(569273930,r246),(1386078435,r245),(108684112,r10),(925488617,r245),(2055159465,r246),(1518554549,r246),(481555596,r3),(1601171132,r246),(1064566216,r3),(1633850841,r245),(282515739,r41),(1931222524,r41),(2098525567,r42),(1632398347,r159),(301719205,r245),(702839375,r0),(1519643880,r42),(2111777295,r246),(1867316150,r0),(536637008,r42),(2131274838,r42),(1536253488,r3),(547636448,r42),(699458084,r205),(1341990463,r42),(93023678,r245),(278754219,r42),(247226593,r41),(245581601,r41),(1168317434,r41),(254786034,r142),(1421990420,r41),(1017563599,r3),(667163718,r3),(1834368104,r3),(1571838552,r247),(591559291,r41),(1035233636,r3),(54954375,r41),(377452177,r206),(1544656563,r206),(814482414,r41),(1537731968,r245),(1740591870,r246),(760312609,r41),(332416583,r42),(773906067,r41),(416047118,r42),(666563699,r199),(1833768085,r41)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f315 : ℕ := 0x184157f98c7ff
def s217 : List ℕ := [f315,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b108 : Ban 28 6 s217 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(465220107,r31),(1619056993,r31),(1636225165,r5),(1138460760,r8),(349176385,r8),(1172964263,r209),(1209623944,r31),(1969151983,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f316 : ℕ := 0x672c880673800
def s218 : List ℕ := [f20,f21,f22,f316,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b109 : Ban 28 6 s218 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2112666552,r5),(1614902147,r14),(825617772,r14),(322257833,r14),(1686065331,r31),(298109723,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f317 : ℕ := 0x820ff8
def f318 : ℕ := 0xbfb3f8
def f319 : ℕ := 0xce4cc0
def s219 : List ℕ := [f317,f318,f319]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w137 : Wide 12 4 s219 := viaSearch (by decide +kernel)
def r248 : Rule 28 5 := cutRule 5 p45 w137
def f320 : ℕ := 0x5624c007ffff0
def s220 : List ℕ := [f35,f20,f320,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b110 : Ban 28 6 s220 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(378327179,r31),(446699221,r51),(1388357736,r51),(2088580227,r31),(1877656872,r31),(685759044,r51),(551593548,r5),(376774585,r51),(688008160,r31),(189231298,r31),(356534341,r51),(389283612,r8),(1941745909,r79),(1875150478,r79),(1352422739,r8),(938987725,r79),(1976217117,r8),(651074022,r31),(1573809855,r31),(1827482841,r31),(960392031,r248),(2127596417,r51),(423787115,r209),(1590991501,r51),(460446796,r31),(1760643372,r31),(1179398488,r31),(821539539,r51),(91776859,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f321 : ℕ := 0x2cfc
def f322 : ℕ := 0x7d74
def f323 : ℕ := 0xbeb8
def s221 : List ℕ := [f179,f321,f322,f323]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w138 : Wide 8 4 s221 := viaSearch (by decide +kernel)
def p110 : Weak 28 8 := signedPick 6 [6,7,10,13,17,18,20,22] (by decide) (by decide) (by decide)
def r249 : Rule 28 6 := cutRule 6 p110 w138
def f324 : ℕ := 0x60489bfe0f8ff
def s222 : List ℕ := [f35,f20,f21,f324,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b111 : Ban 28 6 s222 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1752246430,r31),(96315449,r31),(113483621,r5),(459660568,r8),(973918488,r8),(1797706366,r209),(1834366047,r31),(446410439,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f325 : ℕ := 0x1f254401f0700
def s223 : List ℕ := [f35,f325,f20,f21,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b112 : Ban 28 6 s223 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1056075257,r14),(1547627923,r14),(1462589174,r14),(1564796095,r5),(1138194874,r31),(1897722913,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f326 : ℕ := 0x7f6ddffffffff
def s224 : List ℕ := [f35,f20,f21,f22,f23,f326]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b107 : Ban 28 7 s224 := viaRules (ws := [s217,s218,s220,s168,s222,s223]) (consBan b108 (consBan b109 (consBan b110 (consBan b76 (consBan b111 (consBan b112 (nilBan _ _)))))))
  (dictionary [(1324191352,r41),(989773700,r53),(684679278,r53),(1058145742,r41),(1102258836,r41),(1481326366,r53),(1341199494,r53),(1533700277,r41),(388009844,r3),(1498494538,r207),(2081505158,r207),(503306136,r3),(988221106,r41),(1299454681,r53),(800677819,r53),(967980862,r41),(1814868331,r42),(1000730133,r158),(405708783,r42),(1564575390,r158),(1716397026,r42),(211445758,r158),(1109962620,r42),(1295693161,r158),(1264165535,r53),(1262520543,r53),(37772729,r53),(291445715,r53),(1571838552,r247),(591559291,r41),(1035233636,r3),(54954375,r41),(1240428315,r41),(703823399,r41),(565452231,r41),(1732656617,r53),(414111858,r41),(1831421356,r53),(407187263,r41),(1777251551,r53),(1349355525,r41),(1790845009,r53),(1432986060,r41),(703223380,r53),(1209623944,r41),(413303086,r41),(99562886,r53),(577520915,r0),(263780715,r53),(1686065331,r41),(889744473,r0),(576004273,r53),(1878695211,r41),(1564955011,r53),(1017563599,r3),(460446796,r41),(288280082,r249),(2122023529,r41),(1716020371,r0),(1402280171,r53),(1738225898,r41),(1566059184,r10),(1252318984,r41),(896651052,r41),(582910852,r53),(1834366047,r41),(517881172,r42),(204140972,r41),(1581019299,r0),(1267279099,r53),(1138194874,r41),(1969193646,r0),(1655453446,r41),(743602412,r41),(429862212,r53),(2046396817,r41)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r250 : Rule 28 5 := cutRule 5 p51 w127
def f327 : ℕ := 0x46d02000ff00
def s225 : List ℕ := [f34,f327,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b114 : Ban 28 6 s225 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1635908250,r31),(2055159465,r250),(1865648807,r31),(1543437660,r229)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f328 : ℕ := 0x2a9c
def s226 : List ℕ := [f328,f55,f61]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w139 : Wide 7 4 s226 := viaSearch (by decide +kernel)
def r251 : Rule 28 6 := cutRule 6 p25 w139
def s227 : List ℕ := [f327,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b113 : Ban 28 7 s227 := viaRules (ws := [s225]) (consBan b114 (nilBan _ _))
  (dictionary [(1217479592,r41),(1564502692,r53),(1876969976,r0),(76509429,r53),(1490556474,r41),(1837579574,r53),(1287305436,r0),(1634328536,r53),(368694575,r246),(1252322591,r41),(715717675,r41),(1984954652,r41),(1650537000,r53),(1345442578,r53),(1718909042,r41),(1156308904,r41),(1503332004,r53),(839990116,r10),(1187013216,r41),(2031201138,r206),(230740591,r41),(1635908250,r41),(1982931350,r53),(1763022136,r41),(2142089666,r53),(2001962794,r53),(46979930,r41),(11774191,r3),(594784811,r3),(1164069436,r99),(423131262,r41),(770154362,r53),(2045746181,r0),(245285634,r41),(1850615059,r42),(50154512,r41),(269315271,r0),(616338371,r53),(1648984406,r41),(1960217981,r53),(1461441119,r53),(1628744162,r41),(328147984,r42),(1661493433,r158),(1066472083,r42),(77855043,r158),(229676679,r42),(872209058,r158),(1770725920,r42),(1956456461,r158),(1385633517,r41),(565452231,r41),(1732656617,r53),(757724449,r41),(1924928835,r53),(1923283843,r53),(698536029,r53),(1932488276,r41),(952209015,r53),(733987229,r251),(1901191615,r41),(197382313,r3),(1364586699,r41),(2055154419,r206),(1074875158,r41),(344701009,r53),(1067950563,r41),(1270810465,r41),(290531204,r53),(842914439,r42),(2010118825,r41),(304124662,r53),(2093749360,r41),(196782294,r41),(1363986680,r53)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f329 : ℕ := 0x8c326f98c70f
def s228 : List ℕ := [f329,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b116 : Ban 28 6 s228 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1965026111,r5),(2134896681,r12),(2077511247,r214)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w140 : Wide 8 3 s221 := viaSearch (by decide +kernel)
def r252 : Rule 28 5 := cutRule 5 p110 w140
def f330 : ℕ := 0x477f3f
def f331 : ℕ := 0x51bfc7
def s229 : List ℕ := [f296,f307,f330,f331]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w141 : Wide 14 3 s229 := viaSearch (by decide +kernel)
def p111 : Weak 28 14 := relaxed (pick [1,2,3,11,12,13,16,18,21,23,24,25,26,27] (by decide) (by decide) (by decide))
def r253 : Rule 28 5 := cutRule 5 p111 w141
def f332 : ℕ := 0x112007ff8
def f333 : ℕ := 0x261bfa63f
def f334 : ℕ := 0x46c5fc7c7
def f335 : ℕ := 0x6806ff807
def s230 : List ℕ := [f332,f333,f334,f335]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w142 : Wide 20 3 s230 := viaSearch (by decide +kernel)
def p112 : Weak 28 20 := relaxed (pick [1,2,3,8,9,10,11,12,13,14,15,16,18,19,21,23,24,25,26,27] (by decide) (by decide) (by decide))
def r254 : Rule 28 5 := cutRule 5 p112 w142
def s231 : List ℕ := [f272,f307,f308,f331]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w143 : Wide 14 3 s231 := viaSearch (by decide +kernel)
def p113 : Weak 28 14 := relaxed (pick [1,2,3,8,9,10,16,18,19,23,24,25,26,27] (by decide) (by decide) (by decide))
def r255 : Rule 28 5 := cutRule 5 p113 w143
def f336 : ℕ := 0x6f807
def f337 : ℕ := 0x6c5ffc7
def s232 : List ℕ := [f336,f264,f302,f337]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w144 : Wide 16 3 s232 := viaSearch (by decide +kernel)
def p114 : Weak 28 16 := relaxed (pick [1,2,3,8,9,10,11,12,13,14,15,23,24,25,26,27] (by decide) (by decide) (by decide))
def r256 : Rule 28 5 := cutRule 5 p114 w144
def f338 : ℕ := 0x8907ff8
def f339 : ℕ := 0x130da63f
def f340 : ℕ := 0x2362c7c7
def f341 : ℕ := 0x34030007
def f342 : ℕ := 0x34037807
def s233 : List ℕ := [f338,f339,f340,f341,f342]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w145 : Wide 15 4 s233 := viaSearch (by decide +kernel)
def p115 : Weak 28 15 := relaxed (pick [5,6,7,8,9,10,11,12,13,14,15,17,18,20,22] (by decide) (by decide) (by decide))
def r257 : Rule 28 5 := cutRule 5 p115 w145
def f343 : ℕ := 0x5200d100000f0
def s234 : List ℕ := [f34,f35,f343,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b117 : Ban 28 6 s234 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(954101329,r252),(1738323397,r218),(759077075,r253),(441522687,r254),(1874220435,r12),(952520383,r220),(1373215265,r255),(393141244,r31),(2055159465,r250),(70930097,r256),(64005502,r257)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f344 : ℕ := 0x4b62007fff00
def s235 : List ℕ := [f344,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b118 : Ban 28 6 s235 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(33032584,r14),(896651052,r31),(1151230668,r5),(447785139,r14),(2145161556,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f345 : ℕ := 0x20d82afe0f80f
def s236 : List ℕ := [f35,f345,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b119 : Ban 28 6 s236 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(809897839,r12),(2094405481,r5),(662588727,r226)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s237 : List ℕ := [f35,f20,f343,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b115 : Ban 28 7 s237 := viaRules (ws := [s228,s234,s235,s236]) (consBan b116 (consBan b117 (consBan b118 (consBan b119 (nilBan _ _)))))
  (dictionary [(956121434,r3),(621703782,r41),(316609360,r41),(690075824,r207),(1700806012,r3),(1018995894,r207),(1541149440,r0),(859339322,r41),(186727761,r0),(1652401290,r41),(569014752,r3),(1240428315,r41),(1385633517,r41),(703823399,r41),(734188918,r215),(1113256448,r41),(973129576,r41),(1165630359,r216),(19939926,r3),(1130424620,r207),(102556509,r225),(1713435240,r207),(135236218,r3),(1098444648,r3),(416634530,r207),(187755545,r10),(1653429074,r3),(2018136262,r3),(927632226,r3),(245822108,r207),(620151188,r44),(931384763,r41),(432607901,r41),(599910944,r42),(1446798413,r3),(632660215,r42),(37638865,r207),(1196505472,r42),(1879649900,r3),(1197839782,r207),(1402498808,r0),(720688690,r42),(167273672,r3),(1070953864,r0),(389143746,r42),(1348327108,r227),(1990859487,r42),(741892702,r228),(927623243,r42),(896095617,r41),(894450625,r41),(1817186458,r41),(2070859444,r41),(667163718,r3),(1834368104,r3),(733987229,r251),(1901191615,r41),(197382313,r3),(1364586699,r41),(368694575,r246),(46041940,r230),(1463351438,r41),(39117345,r231),(1409181633,r41),(981285607,r42),(1422775091,r41),(1064916142,r42),(335153462,r41)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w146 : Wide 9 4 s6 := viaSearch (by decide +kernel)
def r258 : Rule 28 6 := cutRule 6 p8 w146
def f346 : ℕ := 0x60589bfe0380f
def s238 : List ℕ := [f35,f20,f21,f346,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b121 : Ban 28 6 s238 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(124144890,r60),(525185958,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f347 : ℕ := 0x6b009dfe7000f
def s239 : List ℕ := [f35,f20,f21,f22,f347,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b122 : Ban 28 6 s239 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(5552738,r121),(2145161556,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s240 : List ℕ := [f27,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b120 : Ban 28 7 s240 := viaRules (ws := [s238,s7,s239,s68,s116]) (consBan b121 (consBan b3 (consBan b122 (consBan b27 (consBan b50 (nilBan _ _))))))
  (dictionary [(1847440477,r10),(526643207,r10),(1564065796,r10),(1369480801,r42),(1086106120,r215),(813202767,r3),(529828086,r215),(333100179,r204),(49725498,r215),(2004447794,r3),(1721073113,r215),(317134282,r204),(1354556871,r204),(1020139219,r0),(1825105855,r204),(715044797,r0),(1088511261,r215),(1654939694,r0),(1857471927,r0),(1371565013,r0),(960176210,r258),(474269296,r10),(1997598799,r0),(1511691885,r0),(904282277,r204),(418375363,r204),(1528860057,r10),(2111870677,r215),(1019578569,r204),(533671655,r10),(595181429,r9),(311806748,r215),(134218019,r0),(1998326985,r0),(2040671038,r204),(1709922324,r0),(1426547643,r0),(1018586625,r0),(1329820200,r0),(1941104396,r55),(831043338,r0),(998346381,r0),(1845233850,r204),(1031095652,r0),(436074302,r215),(1594940909,r0),(241811277,r0),(1140328139,r10),(1326058680,r0),(2070812827,r89),(1787438146,r215),(32752685,r41),(1896861651,r41),(1680241933,r204),(1450796101,r41),(1167421420,r41),(1294531054,r41),(1292886062,r0),(1178199306,r116),(68138248,r0),(321811234,r41),(85319894,r204),(1102258836,r41),(734188918,r215),(1763022136,r41),(1861786875,r41),(437552782,r10),(1807617070,r41),(1821210528,r0),(1463351579,r0),(733588899,r41)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r259 : Rule 28 6 := cutRule 6 p7 w5
def f348 : ℕ := 0x210338
def f349 : ℕ := 0xefd038
def s241 : List ℕ := [f348,f231,f349]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w147 : Wide 12 4 s241 := viaSearch (by decide +kernel)
def r260 : Rule 28 5 := cutRule 5 p39 w147
def r261 : Rule 28 5 := cutRule 5 p7 w3
def f350 : ℕ := 0xc6506fffff0f
def s242 : List ℕ := [f350,f35,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b124 : Ban 28 6 s242 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(746710782,r14),(1080404355,r12),(1957474682,r260),(1471567768,r261),(847413624,r7),(361506710,r7),(740574240,r14),(734784427,r7),(328137192,r14),(789625418,r7),(2146452229,r14),(558702555,r14),(59925693,r14),(227228736,r14),(1618177279,r14),(369210494,r7),(936390237,r51),(1315588230,r31),(1378152268,r51),(536179047,r31),(521768417,r14),(1444504250,r14),(1698177236,r7),(1090669230,r31),(1813918784,r51),(608603399,r7),(1050092883,r14),(692233934,r14),(2109954901,r7)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p116 : Weak 28 8 := signedPick 1 [1,2,8,10,13,14,18,19] (by decide) (by decide) (by decide)
def r262 : Rule 28 6 := cutRule 6 p116 w112
def f351 : ℕ := 0x5292f100000f0
def s243 : List ℕ := [f35,f351,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b125 : Ban 28 6 s243 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1970598184,r14),(803986524,r14),(2084035831,r12),(637214560,r14),(1681589563,r14),(2053054657,r31),(1154081514,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f352 : ℕ := 0xf7e718
def s244 : List ℕ := [f7,f8,f10,f352]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w148 : Wide 12 3 s244 := viaSearch (by decide +kernel)
def r263 : Rule 28 5 := cutRule 5 p2 w148
def f353 : ℕ := 0x40d0b3fe0f8ff
def s245 : List ℕ := [f35,f20,f353,f21,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b126 : Ban 28 6 s245 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(259076677,r14),(270033110,r14),(1481622871,r261),(750629343,r14),(767797515,r263),(1552542028,r14),(341196294,r31),(1100724333,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f354 : ℕ := 0x65a718
def s246 : List ℕ := [f7,f8,f354,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w149 : Wide 12 3 s246 := viaSearch (by decide +kernel)
def r264 : Rule 28 5 := cutRule 5 p2 w149
def f355 : ℕ := 0x1e274401f0700
def s247 : List ℕ := [f35,f355,f20,f21,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b127 : Ban 28 6 s247 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(794070225,r14),(1118850927,r14),(1285622891,r14),(1302791063,r264),(876189842,r31),(1635717881,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f356 : ℕ := 0xbfd0f8
def s248 : List ℕ := [f7,f9,f10,f356]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w150 : Wide 12 3 s248 := viaSearch (by decide +kernel)
def r265 : Rule 28 5 := cutRule 5 p2 w150
def f357 : ℕ := 0x5a00d5fff00ff
def s249 : List ℕ := [f35,f20,f21,f357,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b128 : Ban 28 6 s249 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1499866763,r14),(574929310,r261),(1991419429,r14),(2008587601,r265),(1581986380,r31),(706724322,r31),(1510823196,r14),(721538821,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f358 : ℕ := 0x2d90f8
def s250 : List ℕ := [f7,f358,f9,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w151 : Wide 12 3 s250 := viaSearch (by decide +kernel)
def r266 : Rule 28 5 := cutRule 5 p2 w151
def f359 : ℕ := 0x4f722000ff00
def s251 : List ℕ := [f359,f35,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b129 : Ban 28 6 s251 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1111228293,r31),(1518091141,r14),(2009643807,r14),(2026811979,r266),(1529047574,r14),(739763199,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f360 : ℕ := 0x5ef7f7fffffff
def s252 : List ℕ := [f35,f20,f21,f360,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b123 : Ban 28 7 s252 := viaRules (ws := [s242,s243,s245,s247,s249,s251]) (consBan b124 (consBan b125 (consBan b126 (consBan b127 (consBan b128 (consBan b129 (nilBan _ _)))))))
  (dictionary [(1733624401,r0),(1399206749,r1),(1094112327,r1),(1467578791,r0),(960176210,r258),(474269296,r10),(1997598799,r0),(1511691885,r0),(713209954,r0),(1750632543,r1),(281556593,r0),(1943133326,r0),(797442893,r10),(1907927587,r259),(343454560,r10),(912739185,r259),(1654939694,r0),(740574240,r0),(108276475,r262),(203969324,r0),(1716020371,r0),(1811713220,r1),(803986524,r0),(171688759,r3),(267381608,r0),(21826019,r0),(117518868,r1),(1847440477,r10),(1397654155,r1),(1708887730,r1),(1210110868,r1),(1377413911,r1),(76817733,r0),(1410163182,r1),(815141832,r0),(1974008439,r1),(2125830075,r0),(620878807,r1),(1519395669,r0),(1705126210,r1),(1172195066,r0),(750629343,r0),(1267887915,r1),(1816554627,r0),(1912247476,r1),(984262616,r0),(1079955465,r1),(1707188614,r0),(1285622891,r0),(1802881463,r1),(1673598584,r0),(1671953592,r1),(447205778,r1),(700878764,r0),(464387424,r41),(1481326366,r53),(1113256448,r41),(2142089666,r53),(823544907,r41),(93370758,r53),(816620312,r41),(39200953,r53),(915447319,r41),(1991419429,r0),(1011140168,r0),(1163482323,r0),(1259175172,r1),(939062994,r0),(1034755843,r1),(933671697,r41),(2009643807,r0),(1029364546,r0),(1758788574,r0),(52794411,r1),(1842419109,r1),(1112656429,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f361 : ℕ := 0x2a78
def s253 : List ℕ := [f361,f60,f61]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w152 : Wide 7 4 s253 := viaSearch (by decide +kernel)
def r267 : Rule 28 6 := cutRule 6 p21 w152
def f362 : ℕ := 0x4634800673800
def s254 : List ℕ := [f34,f35,f20,f362,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b131 : Ban 28 6 s254 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(719346496,r14),(95056183,r213),(814194579,r14),(904282277,r214)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s255 : List ℕ := [f35,f20,f362,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b130 : Ban 28 7 s255 := viaRules (ws := [s254]) (consBan b131 (nilBan _ _))
  (dictionary [(556074940,r203),(1593497529,r0),(1259079877,r1),(2064046513,r0),(953985455,r1),(1327451919,r0),(713209954,r0),(1795066566,r0),(1750632543,r1),(1518297102,r0),(1473863079,r1),(277445819,r3),(233011796,r0),(814194579,r0),(769760556,r1),(1066584945,r203),(1022150922,r0),(1857471927,r0),(1371565013,r0),(1251490779,r267),(765583865,r10),(141429721,r0),(1803006454,r0),(1767800715,r10),(203327688,r21),(772612313,r10),(1415999036,r204),(220104694,r0),(1257527283,r1),(1568760858,r1),(32561407,r0),(1069983996,r1),(1237287039,r1),(2084174508,r0),(1270036310,r1),(675014960,r0),(1833881567,r1),(520636602,r0),(476202579,r1),(1992725098,r0),(1948291075,r1),(1306401180,r0),(1261967157,r1),(2020031230,r0),(1975597207,r1),(1985703203,r0),(480751935,r1),(1379268797,r0),(1564999338,r1),(496049123,r41),(1533471712,r0),(1531826720,r1),(1417139964,r0),(307078906,r1),(560751892,r0),(324260552,r41),(1341199494,r53),(973129576,r41),(2001962794,r53),(2120143302,r0),(2075709279,r1),(1756929270,r41),(1712495247,r0),(1625937164,r41),(1581503141,r0),(306694623,r0),(262260600,r1),(683418035,r41),(2100727533,r53),(676493440,r41),(2046557728,r53),(1618661702,r0),(2060151186,r1),(1702292237,r1),(972529557,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f363 : ℕ := 0x252c0807fff00
def s256 : List ℕ := [f35,f363,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b133 : Ban 28 6 s256 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1303513900,r14),(21826019,r14),(344613593,r12),(675832494,r14),(1972980494,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r268 : Rule 28 5 := cutRule 5 p116 w116
def s257 : List ℕ := [f267,f269,f270,f271]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w153 : Wide 15 3 s257 := viaSearch (by decide +kernel)
def r269 : Rule 28 5 := cutRule 5 p101 w153
def f364 : ℕ := 0x1807
def f365 : ℕ := 0x907f8
def f366 : ℕ := 0x30ee3f
def f367 : ℕ := 0x3637c7
def s258 : List ℕ := [f364,f365,f366,f367]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w154 : Wide 11 3 s258 := viaSearch (by decide +kernel)
def p117 : Weak 28 11 := relaxed (pick [5,6,7,11,12,13,16,17,18,21,22] (by decide) (by decide) (by decide))
def r270 : Rule 28 5 := cutRule 5 p117 w154
def f368 : ℕ := 0xa07
def f369 : ℕ := 0x2171f
def f370 : ℕ := 0x2cde7
def s259 : List ℕ := [f368,f11,f369,f370]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w155 : Wide 9 3 s259 := viaSearch (by decide +kernel)
def p118 : Weak 28 9 := relaxed (pick [5,6,7,9,10,16,17,18,20] (by decide) (by decide) (by decide))
def r271 : Rule 28 5 := cutRule 5 p118 w155
def f371 : ℕ := 0xc07
def f372 : ℕ := 0x2cbe7
def s260 : List ℕ := [f371,f11,f369,f372]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w156 : Wide 9 3 s260 := viaSearch (by decide +kernel)
def p119 : Weak 28 9 := relaxed (pick [5,6,7,9,10,11,12,13,15] (by decide) (by decide) (by decide))
def r272 : Rule 28 5 := cutRule 5 p119 w156
def f373 : ℕ := 0x84117f80000f
def s261 : List ℕ := [f34,f373,f35,f20,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b134 : Ban 28 6 s261 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2143924017,r268),(287693135,r14),(904282277,r214),(990001253,r211),(1818595990,r269),(1311866396,r5),(952520383,r220),(1810886469,r270),(1544840859,r222),(154079801,r271),(541649492,r272)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w157 : Wide 12 4 s167 := viaSearch (by decide +kernel)
def r273 : Rule 28 6 := cutRule 6 p96 w157
def f374 : ℕ := 0x6098a8060f8f0
def s262 : List ℕ := [f35,f20,f21,f374,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b135 : Ban 28 6 s262 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1250801230,r5),(1648572516,r237),(45149943,r12)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f375 : ℕ := 0x7300c807f00f0
def s263 : List ℕ := [f35,f20,f21,f22,f375,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b136 : Ban 28 6 s263 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1476780269,r5),(860367824,r250),(489351158,r12)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s264 : List ℕ := [f373,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b132 : Ban 28 7 s264 := viaRules (ws := [s256,s261,s262,s263]) (consBan b133 (consBan b134 (consBan b135 (consBan b136 (nilBan _ _)))))
  (dictionary [(1415999036,r204),(526643207,r10),(1564065796,r10),(1645641073,r10),(1793707833,r259),(1823583155,r3),(1971649915,r10),(1990698063,r10),(927632226,r3),(1075698986,r259),(1785998312,r202),(1451580660,r0),(1146486238,r0),(1519952702,r216),(1795066566,r0),(281556593,r0),(1943133326,r0),(1251490779,r267),(765583865,r10),(141429721,r0),(1803006454,r0),(849816804,r10),(1960301498,r259),(395828471,r10),(1451020010,r273),(965113096,r259),(2083772145,r10),(84355258,r259),(2049602310,r0),(50185423,r0),(1884663034,r10),(396538785,r0),(544605545,r0),(1450028066,r0),(1761261641,r0),(1262484779,r0),(1429787822,r0),(129191644,r232),(1462537093,r0),(867515743,r216),(2026382350,r0),(30720339,r10),(673252718,r0),(1571769580,r259),(1757500121,r0),(581024856,r10),(729091616,r259),(486324735,r41),(634391495,r41),(1358834465,r10),(1344219418,r41),(1492286178,r41),(1725972495,r41),(1724327503,r0),(499579689,r0),(753252675,r41),(516761335,r245),(1533700277,r41),(1165630359,r216),(46979930,r41),(875918818,r10),(145744669,r41),(868994223,r259),(91574864,r41),(1811162485,r147),(105168322,r0),(1894793020,r0),(1165030340,r41)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f376 : ℕ := 0x184357f98070f
def s265 : List ℕ := [f376,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b138 : Ban 28 6 s265 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(53438375,r71),(1795066566,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r274 : Rule 28 6 := cutRule 6 p19 w146
def f377 : ℕ := 0x3b005df9f000f
def s266 : List ℕ := [f35,f20,f377,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b139 : Ban 28 6 s266 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(460279927,r181),(2145161556,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s267 : List ℕ := [f35,f20,f54,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b137 : Ban 28 7 s267 := viaRules (ws := [s265,s21,s74,s266,s124]) (consBan b138 (consBan b7 (consBan b30 (consBan b139 (consBan b53 (nilBan _ _))))))
  (dictionary [(1968695061,r205),(1634277409,r0),(1329182987,r0),(1702649451,r227),(595181429,r9),(925944938,r227),(1170917799,r0),(1501681308,r0),(520636602,r0),(851400111,r0),(253606702,r205),(1543185419,r41),(1873948928,r227),(1250801230,r3),(1581564739,r227),(947217601,r3),(1277981110,r227),(153814829,r205),(484578338,r227),(2125830075,r0),(1985703203,r0),(30720339,r10),(1518420467,r205),(1032513553,r205),(2142998247,r10),(578525220,r227),(1633716759,r205),(1147809845,r10),(1609433361,r0),(278620137,r0),(1940196870,r0),(1632724815,r0),(1943958390,r0),(1445181528,r0),(1095225999,r76),(1612484571,r0),(1942113468,r205),(311888393,r205),(1645233842,r0),(1050212492,r227),(1691820527,r205),(61595452,r0),(1423702820,r10),(1237207757,r10),(1754466329,r10),(824597809,r274),(1341856381,r0),(338690895,r10),(855949467,r0),(1907024252,r0),(682276438,r0),(935949424,r42),(699458084,r205),(1716397026,r42),(1348327108,r227),(229676679,r42),(1145788469,r160),(1476551978,r227),(261699840,r41),(592463349,r42),(1480860447,r205),(862630161,r41),(1193393670,r42),(328441418,r42),(1051690972,r10),(274271613,r42),(1993859234,r42),(287865071,r0),(1560231197,r186),(2077489769,r0),(1347727089,r42)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f378 : ℕ := 0xf7eb60
def s268 : List ℕ := [f7,f8,f9,f378]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w158 : Wide 12 3 s268 := viaSearch (by decide +kernel)
def r275 : Rule 28 5 := cutRule 5 p2 w158
def f379 : ℕ := 0x10c273f98c7ff
def s269 : List ℕ := [f379,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b141 : Ban 28 6 s269 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(434412915,r14),(1727878266,r14),(943133753,r275),(445369348,r14),(643777669,r261),(1803568620,r14),(516532532,r8),(1276060571,r8)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f380 : ℕ := 0xa74b60
def s270 : List ℕ := [f7,f8,f9,f380]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w159 : Wide 12 3 s270 := viaSearch (by decide +kernel)
def r276 : Rule 28 5 := cutRule 5 p2 w159
def f381 : ℕ := 0x663c880673800
def s271 : List ℕ := [f20,f21,f22,f381,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b142 : Ban 28 6 s271 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(138336732,r276),(1788055974,r14),(998771599,r14),(1287780220,r14),(1859219158,r31),(471263550,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r277 : Rule 28 5 := cutRule 5 p45 w147
def f382 : ℕ := 0x246c0afffff0f
def s272 : List ℕ := [f35,f382,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b143 : Ban 28 6 s272 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1209584880,r7),(1612114508,r14),(170082566,r14),(1177812289,r7),(1793156627,r14),(1845530538,r7),(807987900,r12),(1611284942,r14),(1112508080,r14),(1279811123,r14),(1680041036,r14),(1996875629,r277),(366650554,r7),(1510968715,r261),(2028227287,r7),(523276019,r14),(1575995796,r7),(1574350804,r14),(349602990,r14),(603275976,r7),(105122123,r79),(1240171842,r8),(1587453482,r79),(427777711,r8),(2143251617,r8),(719017524,r79),(2102675270,r14),(1744816321,r14),(1015053641,r7)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p120 : Weak 28 8 := signedPick 1 [1,3,10,11,13,14,18,21] (by decide) (by decide) (by decide)
def r278 : Rule 28 6 := cutRule 6 p120 w129
def f383 : ℕ := 0x7fb0f8
def s273 : List ℕ := [f7,f9,f383,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w160 : Wide 12 3 s273 := viaSearch (by decide +kernel)
def r279 : Rule 28 5 := cutRule 5 p2 w160
def f384 : ℕ := 0x7200d9fff00ff
def s274 : List ℕ := [f35,f20,f21,f22,f384]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b144 : Ban 28 6 s274 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(948249269,r14),(1439801935,r14),(1456970107,r279),(959205702,r14),(1157614023,r261),(169921327,r14),(1030368886,r8),(459181696,r8)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f385 : ℕ := 0x2f10f8
def s275 : List ℕ := [f7,f385,f9,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w161 : Wide 12 3 s275 := viaSearch (by decide +kernel)
def r280 : Rule 28 5 := cutRule 5 p2 w161
def f386 : ℕ := 0x4fe22000ff00
def s276 : List ℕ := [f386,f35,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b145 : Ban 28 6 s276 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(557433306,r31),(964296154,r14),(1455848820,r14),(1473016992,r280),(975252587,r14),(185968212,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f387 : ℕ := 0x76fefbfffffff
def s277 : List ℕ := [f35,f20,f21,f22,f387,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b140 : Ban 28 7 s277 := viaRules (ws := [s269,s271,s272,s243,s274,s276]) (consBan b141 (consBan b142 (consBan b143 (consBan b125 (consBan b144 (consBan b145 (nilBan _ _)))))))
  (dictionary [(463743793,r0),(129326141,r1),(1971715366,r1),(197698183,r0),(241811277,r0),(620878807,r1),(480751935,r1),(673252718,r0),(1675045932,r10),(638046979,r259),(1221057599,r10),(1790342224,r259),(127773547,r1),(439007122,r1),(2087713907,r1),(107533303,r1),(954420772,r0),(140282574,r1),(1692744871,r0),(704127831,r1),(824597809,r274),(1341856381,r0),(338690895,r10),(855949467,r0),(735421975,r0),(249515061,r0),(2065470677,r0),(435245602,r1),(1803568620,r0),(1867695321,r0),(693507562,r1),(1816554627,r0),(642366868,r1),(998771599,r0),(1062898300,r0),(2036194188,r1),(396538785,r0),(1369834673,r1),(523276019,r0),(1160858862,r278),(2134154750,r0),(1716020371,r0),(541832612,r1),(1681589563,r0),(171688759,r3),(1144984647,r0),(1710027817,r0),(535840058,r1),(1423702820,r10),(1609433361,r0),(403717976,r0),(402072984,r1),(1324808817,r1),(1578481803,r0),(1341990463,r42),(211445758,r158),(1990859487,r42),(872209058,r158),(1701147946,r42),(970973797,r158),(1694223351,r42),(916803992,r158),(488907966,r0),(930397450,r1),(572538501,r1),(1990259468,r0),(363829825,r42),(169921327,r0),(1337125713,r0),(1648780955,r0),(474593196,r1),(496938473,r0),(1470234361,r1),(379876710,r41),(185968212,r0),(1353172598,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f388 : ℕ := 0x16264001f0700
def s278 : List ℕ := [f34,f388,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b147 : Ban 28 6 s278 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1628294602,r14),(1518420467,r226),(1074752047,r14),(1060390846,r237)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r281 : Rule 28 6 := cutRule 6 p23 w152
def s279 : List ℕ := [f388,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b146 : Ban 28 7 s279 := viaRules (ws := [s278]) (consBan b147 (nilBan _ _))
  (dictionary [(1709922324,r0),(1619981968,r1),(134616896,r0),(44676540,r1),(192376013,r0),(102435657,r1),(2020031230,r0),(1930090874,r1),(1550552202,r0),(1460611846,r1),(281020525,r3),(191080169,r0),(874561293,r233),(784620937,r0),(1628294602,r0),(1538354246,r1),(1547991196,r0),(1213573544,r1),(908479122,r1),(1281945586,r0),(2030137226,r205),(278620137,r0),(1940196870,r0),(1326058680,r0),(1705126210,r1),(1564999338,r1),(1757500121,r0),(1722294382,r10),(157821355,r21),(727105980,r10),(525185958,r0),(2065470677,r0),(435245602,r1),(694762378,r0),(1212020950,r1),(1523254525,r1),(1024477663,r1),(674522134,r0),(1191780706,r1),(1521409603,r233),(2038668175,r0),(1224529977,r1),(629508627,r0),(1271116662,r0),(1788375234,r1),(1302410806,r281),(1819669378,r0),(816503892,r10),(1333762464,r0),(1003817379,r0),(913877023,r1),(1058911328,r41),(968970972,r0),(970640231,r42),(880699875,r0),(842955495,r0),(753015139,r1),(1487965379,r0),(1486320387,r1),(261572573,r1),(515245559,r0),(278754219,r42),(1295693161,r158),(927623243,r42),(1956456461,r158),(637911702,r42),(2055221200,r158),(630987107,r42),(2001051395,r158),(1055896797,r42),(1573155369,r0),(2014644853,r1),(1139527332,r0),(1656785904,r1),(927023224,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f389 : ℕ := 0x188364018c7f0
def s280 : List ℕ := [f389,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b149 : Ban 28 6 s280 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(813202767,r5),(135535252,r213),(292670266,r12)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f390 : ℕ := 0xd250407fff00
def s281 : List ℕ := [f390,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b150 : Ban 28 6 s281 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(416934864,r14),(1710027817,r14),(79815696,r12),(1314470333,r14),(719503542,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r282 : Rule 28 5 := cutRule 5 p120 w130
def f391 : ℕ := 0x607
def f392 : ℕ := 0x21b1f
def s282 : List ℕ := [f391,f11,f392,f370]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w162 : Wide 9 3 s282 := viaSearch (by decide +kernel)
def p121 : Weak 28 9 := relaxed (pick [5,6,7,12,13,16,17,18,22] (by decide) (by decide) (by decide))
def r283 : Rule 28 5 := cutRule 5 p121 w162
def s283 : List ℕ := [f303,f304,f306,f271]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w163 : Wide 15 3 s283 := viaSearch (by decide +kernel)
def r284 : Rule 28 5 := cutRule 5 p108 w163
def f393 : ℕ := 0x2807
def f394 : ℕ := 0x30de3f
def s284 : List ℕ := [f393,f365,f394,f367]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w164 : Wide 11 3 s284 := viaSearch (by decide +kernel)
def p122 : Weak 28 11 := relaxed (pick [5,6,7,8,9,10,16,17,18,19,20] (by decide) (by decide) (by decide))
def r285 : Rule 28 5 := cutRule 5 p122 w164
def f395 : ℕ := 0x141f8
def f396 : ℕ := 0x2373f
def f397 : ℕ := 0x28bc7
def s285 : List ℕ := [f371,f395,f396,f397]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w165 : Wide 9 3 s285 := viaSearch (by decide +kernel)
def p123 : Weak 28 9 := relaxed (pick [5,6,7,8,9,10,12,13,15] (by decide) (by decide) (by decide))
def r286 : Rule 28 5 := cutRule 5 p123 w165
def f398 : ℕ := 0x20481bf80000f
def s286 : List ℕ := [f34,f35,f398,f20,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b151 : Ban 28 6 s286 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1116737727,r282),(566263596,r211),(1387148812,r283),(701604426,r284),(1311866396,r5),(952520383,r220),(1892186992,r14),(1518420467,r226),(1877825791,r285),(468666243,r243),(117911835,r286)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f399 : ℕ := 0x5b00c407f00f0
def s287 : List ℕ := [f35,f20,f21,f399,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b152 : Ban 28 6 s287 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1476780269,r5),(1584365927,r250),(1213349261,r12)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s288 : List ℕ := [f35,f398,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b148 : Ban 28 7 s288 := viaRules (ws := [s280,s281,s286,s287]) (consBan b149 (consBan b150 (consBan b151 (consBan b152 (nilBan _ _)))))
  (dictionary [(2083772145,r10),(1808101248,r259),(272901580,r0),(2144714330,r0),(984262616,r0),(708591719,r0),(958729109,r10),(1362260655,r202),(1027843003,r0),(722748581,r0),(1096215045,r228),(952387166,r10),(676716269,r259),(1823583155,r3),(1547912258,r10),(1302162509,r10),(927632226,r3),(651961329,r259),(1140328139,r10),(1519395669,r0),(1379268797,r0),(1571769580,r259),(525185958,r0),(735421975,r0),(249515061,r0),(426079147,r10),(1536563841,r259),(2119574461,r10),(1027282353,r273),(541375439,r259),(1026290409,r0),(1337523984,r0),(838747122,r0),(1006050165,r0),(2030137226,r205),(1237207757,r10),(1754466329,r10),(1852937634,r232),(1038799436,r0),(443778086,r228),(1602644693,r0),(1302410806,r281),(1819669378,r0),(816503892,r10),(1333762464,r0),(1302234838,r103),(1300589846,r0),(75842032,r0),(329515018,r42),(40446848,r10),(1912259598,r259),(66516164,r41),(1938328914,r42),(1659094911,r10),(1597604970,r41),(1321934073,r42),(93023678,r245),(1109962620,r42),(741892702,r228),(1770725920,r42),(452181161,r10),(1869490659,r42),(445256566,r259),(1815320854,r42),(1387424828,r42),(1828914312,r0),(1471055363,r0),(741292683,r42)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f400 : ℕ := 0x8c337f80c70f
def s289 : List ℕ := [f400,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b154 : Ban 28 6 s289 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1111501849,r131),(1795066566,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f401 : ℕ := 0x20d83bf80f80f
def s290 : List ℕ := [f35,f401,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b155 : Ban 28 6 s290 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2124382025,r195),(525185958,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w166 : Wide 9 4 s80 := viaSearch (by decide +kernel)
def r287 : Rule 28 6 := cutRule 6 p57 w166
def s291 : List ℕ := [f35,f20,f71,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b153 : Ban 28 7 s291 := viaRules (ws := [s289,s31,s290,s81,s126]) (consBan b154 (consBan b10 (consBan b155 (consBan b33 (consBan b55 (nilBan _ _))))))
  (dictionary [(666409893,r206),(331992241,r41),(26897819,r41),(400364283,r230),(2070812827,r89),(1099291168,r230),(938806538,r0),(2114768526,r41),(2120143302,r0),(1148621643,r41),(1721602562,r206),(1840898199,r0),(869376540,r230),(1476780269,r3),(505258610,r230),(1098444648,r3),(126922989,r230),(550547799,r206),(1726509787,r230),(823544907,r41),(683418035,r41),(875918818,r10),(216135299,r206),(1877712032,r206),(840713079,r10),(1423723699,r230),(331431591,r206),(1993008324,r10),(2090991751,r41),(1605377006,r41),(1119470092,r41),(641673222,r41),(142896360,r41),(310199403,r42),(1157086872,r206),(342948674,r42),(1895410971,r230),(906793931,r42),(1145788469,r160),(174266810,r230),(1419836257,r0),(448314598,r42),(1227279241,r206),(1003817379,r0),(32295720,r42),(1701147946,r42),(452181161,r10),(637911702,r42),(606384076,r41),(604739084,r41),(1527474917,r41),(613943517,r143),(1781147903,r41),(377452177,r206),(1544656563,r206),(414111858,r41),(46041940,r230),(2055154419,r206),(1074875158,r41),(720927463,r10),(729685065,r10),(1896889451,r10),(492342425,r287),(1659546811,r41),(6435511,r10),(1173639897,r41),(691574066,r42),(1133063550,r41),(775204601,r42),(1025721182,r200),(45441921,r41)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f402 : ℕ := 0xbfdb60
def s292 : List ℕ := [f7,f8,f9,f402]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w167 : Wide 12 3 s292 := viaSearch (by decide +kernel)
def r288 : Rule 28 5 := cutRule 5 p2 w167
def f403 : ℕ := 0x188275f98c7ff
def s293 : List ℕ := [f403,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b157 : Ban 28 6 s293 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1154004678,r31),(360862237,r31),(1662725516,r288),(1164961111,r8),(375676736,r8),(1236124295,r31),(1558622097,r261),(1995652334,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f404 : ℕ := 0xb54b60
def s294 : List ℕ := [f7,f8,f9,f404]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w168 : Wide 12 3 s294 := viaSearch (by decide +kernel)
def r289 : Rule 28 5 := cutRule 5 p2 w168
def f405 : ℕ := 0x6734880673800
def s295 : List ℕ := [f20,f21,f22,f405,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b158 : Ban 28 6 s295 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1660415466,r289),(1162651061,r14),(373366686,r14),(662375307,r14),(1233814245,r31),(1993342284,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f406 : ℕ := 0x820c38
def f407 : ℕ := 0xbfb038
def s296 : List ℕ := [f406,f407,f319]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w169 : Wide 12 4 s296 := viaSearch (by decide +kernel)
def r290 : Rule 28 5 := cutRule 5 p45 w169
def f408 : ℕ := 0x2d240cfffff0f
def s297 : List ℕ := [f35,f408,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b159 : Ban 28 6 s297 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(382822985,r51),(660793788,r31),(1393911892,r31),(1694256166,r51),(1496996151,r31),(1549370062,r51),(2074991325,r12),(1003890891,r51),(1315124466,r31),(816347604,r31),(983650647,r51),(15786066,r79),(688987189,r8),(2053017619,r79),(218069615,r8),(227115543,r8),(1125632405,r79),(1278190328,r31),(53442514,r31),(307115500,r31),(240276031,r31),(1895967818,r290),(915688557,r51),(1410060904,r261),(429781643,r51),(1847091141,r31),(1806514794,r31),(1448655845,r51),(718893165,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p124 : Weak 28 8 := signedPick 2 [2,3,10,13,16,18,19,21] (by decide) (by decide) (by decide)
def r291 : Rule 28 6 := cutRule 6 p124 w138
def f409 : ℕ := 0x7fb718
def s298 : List ℕ := [f7,f8,f409,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w170 : Wide 12 3 s298 := viaSearch (by decide +kernel)
def r292 : Rule 28 5 := cutRule 5 p2 w170
def f410 : ℕ := 0x6090b9fe0f8ff
def s299 : List ℕ := [f35,f20,f21,f410,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b160 : Ban 28 6 s299 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1909628154,r31),(253697173,r31),(270865345,r292),(1920584587,r8),(1420560581,r8),(1991747771,r31),(166761926,r261),(603792163,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f411 : ℕ := 0x752718
def s300 : List ℕ := [f7,f8,f411,f10]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w171 : Wide 12 3 s300 := viaSearch (by decide +kernel)
def r293 : Rule 28 5 := cutRule 5 p2 w171
def f412 : ℕ := 0x1f264401f0700
def s301 : List ℕ := [f35,f412,f20,f21,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b161 : Ban 28 6 s301 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(549297731,r14),(874078433,r14),(1040850397,r14),(1058018569,r293),(631417348,r31),(1390945387,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f413 : ℕ := 0x7fb6fdfffffff
def s302 : List ℕ := [f35,f20,f21,f22,f23,f413]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b156 : Ban 28 7 s302 := viaRules (ws := [s293,s295,s297,s243,s299,s301]) (consBan b157 (consBan b158 (consBan b159 (consBan b125 (consBan b160 (consBan b161 (nilBan _ _)))))))
  (dictionary [(2083719391,r41),(1749301739,r53),(1444207317,r53),(1817673781,r41),(1861786875,r41),(93370758,r53),(2100727533,r53),(145744669,r41),(1147537883,r10),(110538930,r259),(693549550,r10),(1262834175,r259),(1747749145,r41),(2058982720,r53),(1560205858,r53),(1727508901,r41),(426912723,r42),(1760258172,r158),(1165236822,r42),(176619782,r158),(328441418,r42),(970973797,r158),(1869490659,r42),(2055221200,r158),(2023693574,r53),(2022048582,r53),(797300768,r53),(1050973754,r53),(814482414,r41),(1831421356,r53),(1463351438,r41),(344701009,r53),(492342425,r287),(1659546811,r41),(6435511,r10),(1173639897,r41),(1652622216,r41),(1166715302,r41),(1369575204,r41),(389295943,r53),(2108883564,r41),(402889401,r53),(45030452,r41),(1462751419,r53),(1995652334,r41),(439803437,r41),(885591276,r53),(1163482323,r0),(1609270162,r53),(1993342284,r41),(437493387,r0),(883281226,r53),(1344219418,r41),(1790007257,r53),(1847091141,r41),(864698386,r291),(1310486225,r41),(1716020371,r0),(14324563,r53),(1154081514,r41),(171688759,r3),(617476598,r41),(1635908250,r41),(2081696089,r53),(720927463,r10),(603792163,r41),(675262896,r42),(1121050735,r41),(1648780955,r0),(2094568794,r53),(1390945387,r41),(1462416120,r0),(1908203959,r41),(1597604970,r41),(2043392809,r53),(2090991751,r41)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f414 : ℕ := 0x4b620000ff00
def s303 : List ℕ := [f34,f414,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b163 : Ban 28 6 s303 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(896651052,r31),(216135299,r229),(1910243741,r31),(1279573113,r250)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f415 : ℕ := 0x2978
def s304 : List ℕ := [f415,f60,f63]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w172 : Wide 7 4 s304 := viaSearch (by decide +kernel)
def r294 : Rule 28 6 := cutRule 6 p26 w172
def s305 : List ℕ := [f414,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b162 : Ban 28 7 s305 := viaRules (ws := [s303]) (consBan b163 (nilBan _ _))
  (dictionary [(1450796101,r41),(1842414135,r53),(875378473,r0),(1266996507,r53),(2097555737,r41),(341690124,r53),(306694623,r0),(698312657,r53),(1156308904,r41),(1547926938,r53),(1767872464,r3),(12006851,r41),(524311973,r246),(915930007,r41),(896651052,r41),(1288269086,r53),(2029549586,r41),(1695131934,r53),(1390037512,r53),(1763503976,r41),(727852058,r206),(1605377006,r41),(1119470092,r41),(1807617070,r41),(39200953,r53),(2046557728,r53),(91574864,r41),(56369125,r10),(639379745,r98),(1208664370,r10),(862630161,r41),(1254248195,r53),(891531239,r0),(1283149273,r41),(828472521,r42),(1220090555,r41),(842955495,r0),(1234573529,r53),(1693579340,r41),(2004812915,r53),(1506036053,r53),(1673339096,r41),(372742918,r42),(1706088367,r158),(1111067017,r42),(122449977,r158),(274271613,r42),(916803992,r158),(1815320854,r42),(2001051395,r158),(2145161556,r41),(1369575204,r41),(389295943,r53),(802319383,r41),(1969523769,r53),(1967878777,r53),(743130963,r53),(1977083210,r41),(996803949,r53),(1740591870,r246),(760312609,r41),(1777251551,r53),(1409181633,r41),(1270810465,r41),(290531204,r53),(431248025,r294),(1598452411,r41),(2092824758,r10),(1112545497,r41),(887509373,r42),(2054713759,r41),(348719596,r53),(2138344294,r41),(241377228,r41),(1408581614,r53)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f416 : ℕ := 0x10c362018c7f0
def s306 : List ℕ := [f416,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b165 : Ban 28 6 s306 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(813202767,r5),(2112937799,r213),(122589166,r12)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f417 : ℕ := 0x46d0207fff00
def s307 : List ℕ := [f417,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b166 : Ban 28 6 s307 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(933829526,r14),(1635908250,r31),(635341859,r12),(1065129177,r14),(1385633517,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r295 : Rule 28 5 := cutRule 5 p124 w140
def f418 : ℕ := 0x23b3f
def f419 : ℕ := 0x28dc7
def s308 : List ℕ := [f391,f395,f418,f419]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w173 : Wide 9 3 s308 := viaSearch (by decide +kernel)
def p125 : Weak 28 9 := relaxed (pick [5,6,7,11,12,13,17,18,22] (by decide) (by decide) (by decide))
def r296 : Rule 28 5 := cutRule 5 p125 w173
def s309 : List ℕ := [f338,f339,f340,f342]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w174 : Wide 15 3 s309 := viaSearch (by decide +kernel)
def r297 : Rule 28 5 := cutRule 5 p115 w174
def s310 : List ℕ := [f368,f395,f396,f419]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w175 : Wide 9 3 s310 := viaSearch (by decide +kernel)
def p126 : Weak 28 9 := relaxed (pick [5,6,7,8,9,10,17,18,20] (by decide) (by decide) (by decide))
def r298 : Rule 28 5 := cutRule 5 p126 w175
def f420 : ℕ := 0x3007
def f421 : ℕ := 0x362fc7
def s311 : List ℕ := [f420,f365,f394,f421]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w176 : Wide 11 3 s311 := viaSearch (by decide +kernel)
def p127 : Weak 28 11 := relaxed (pick [5,6,7,8,9,10,11,12,13,14,15] (by decide) (by decide) (by decide))
def r299 : Rule 28 5 := cutRule 5 p127 w176
def f422 : ℕ := 0x29001df80000f
def s312 : List ℕ := [f34,f35,f422,f20,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b167 : Ban 28 6 s312 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(881960372,r295),(2010971886,r211),(684373455,r296),(1302609662,r297),(1311866396,r5),(952520383,r220),(1175050434,r298),(45807106,r31),(216135299,r229),(1562620125,r299),(64005502,r257)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f423 : ℕ := 0x40d8a2060f8f0
def s313 : List ℕ := [f35,f20,f423,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b168 : Ban 28 6 s313 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1250801230,r5),(1025603446,r237),(1569664520,r12)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s314 : List ℕ := [f35,f422,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b164 : Ban 28 7 s314 := viaRules (ws := [s306,s307,s312,s313]) (consBan b165 (consBan b166 (consBan b167 (consBan b168 (nilBan _ _)))))
  (dictionary [(581024856,r10),(1750062249,r259),(255859878,r0),(1424897271,r41),(939062994,r0),(2108100387,r41),(85872652,r10),(659485298,r202),(325067646,r41),(19973224,r41),(393439688,r231),(108684112,r10),(1277721505,r259),(1823583155,r3),(845136901,r10),(1154913315,r10),(927632226,r3),(2096669619,r259),(437552782,r10),(816620312,r41),(676493440,r41),(868994223,r259),(2145161556,r41),(1652622216,r41),(1166715302,r41),(1870787437,r10),(833788484,r259),(1416799104,r10),(324506996,r273),(1986083729,r259),(323515052,r46),(634748627,r41),(135971765,r41),(303274808,r42),(40446848,r10),(1209484241,r259),(1083680822,r0),(105234568,r42),(135180950,r10),(496938473,r0),(1665975866,r42),(1150162277,r232),(336024079,r42),(1888486376,r231),(899869336,r42),(1051690972,r10),(1694223351,r42),(445256566,r259),(630987107,r42),(599459481,r41),(597814489,r41),(1520550322,r41),(1774223308,r41),(727852058,r206),(729685065,r10),(1896889451,r10),(1537731968,r245),(407187263,r41),(39117345,r231),(1067950563,r41),(431248025,r294),(1598452411,r41),(2092824758,r10),(1112545497,r41),(684649471,r42),(1126138955,r41),(768280006,r42),(38517326,r41)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f424 : ℕ := 0x18c377f8000ff
def s315 : List ℕ := [f424,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b170 : Ban 28 6 s315 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1303513900,r14),(1795066566,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f425 : ℕ := 0x24c0
def s316 : List ℕ := [f425,f74,f75,f76]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w177 : Wide 8 3 s316 := viaSearch (by decide +kernel)
def p128 : Weak 28 8 := signedPick 0 [0,1,3,4,5,7,14,15] (by decide) (by decide) (by decide)
def r300 : Rule 28 5 := cutRule 5 p128 w177
def f426 : ℕ := 0x339e49fffc0
def s317 : List ℕ := [f28,f29,f30,f31,f426]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w178 : Wide 21 4 s317 := viaSearch (by decide +kernel)
def r301 : Rule 28 5 := cutRule 5 p10 w178
def s318 : List ℕ := [f34,f424,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b171 : Ban 28 6 s318 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1801203108,r14),(2042783635,r300),(1184622316,r12),(1492731035,r5),(1251548370,r301)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f427 : ℕ := 0x2403fc0
def f428 : ℕ := 0x27241c0
def f429 : ℕ := 0x3c48e00
def f430 : ℕ := 0xff93fc0
def s319 : List ℕ := [f427,f428,f429,f430]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w179 : Wide 14 3 s319 := viaSearch (by decide +kernel)
def p129 : Weak 28 14 := signedPick 1 [1,2,3,5,6,7,11,12,13,16,17,18,21,22] (by decide) (by decide) (by decide)
def r302 : Rule 28 5 := cutRule 5 p129 w179
def f431 : ℕ := 0x980480
def f432 : ℕ := 0x981ff0
def f433 : ℕ := 0xfea3f0
def f434 : ℕ := 0x39f5c70
def s320 : List ℕ := [f431,f432,f433,f434]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w180 : Wide 13 3 s320 := viaSearch (by decide +kernel)
def p130 : Weak 28 13 := signedPick 1 [1,2,5,6,8,9,10,13,14,15,18,19,20] (by decide) (by decide) (by decide)
def r303 : Rule 28 5 := cutRule 5 p130 w180
def f435 : ℕ := 0x212019ce00
def s321 : List ℕ := [f435,f28,f29,f30,f31]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w181 : Wide 21 4 s321 := viaSearch (by decide +kernel)
def r304 : Rule 28 5 := cutRule 5 p10 w181
def f436 : ℕ := 0x3c90e00
def f437 : ℕ := 0xff4bfc0
def s322 : List ℕ := [f427,f428,f436,f437]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w182 : Wide 14 3 s322 := viaSearch (by decide +kernel)
def p131 : Weak 28 14 := signedPick 1 [1,2,3,5,6,7,8,9,10,16,17,18,19,20] (by decide) (by decide) (by decide)
def r305 : Rule 28 5 := cutRule 5 p131 w182
def f438 : ℕ := 0x920410
def f439 : ℕ := 0x921ff0
def f440 : ℕ := 0x39f5ce0
def s323 : List ℕ := [f438,f439,f433,f440]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w183 : Wide 13 3 s323 := viaSearch (by decide +kernel)
def p132 : Weak 28 13 := signedPick 1 [1,3,5,7,10,11,12,13,14,15,18,21,22] (by decide) (by decide) (by decide)
def r306 : Rule 28 5 := cutRule 5 p132 w183
def f441 : ℕ := 0xf93a5fffc0
def s324 : List ℕ := [f28,f29,f30,f441,f31]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w184 : Wide 21 4 s324 := viaSearch (by decide +kernel)
def r307 : Rule 28 5 := cutRule 5 p10 w184
def f442 : ℕ := 0x212007c1c0
def s325 : List ℕ := [f442,f28,f29,f30,f31]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w185 : Wide 21 4 s325 := viaSearch (by decide +kernel)
def r308 : Rule 28 5 := cutRule 5 p10 w185
def f443 : ℕ := 0x2103ff0
def f444 : ℕ := 0x27d41f0
def f445 : ℕ := 0x3900e00
def f446 : ℕ := 0xf9ebe70
def s326 : List ℕ := [f443,f444,f445,f446]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w186 : Wide 14 3 s326 := viaSearch (by decide +kernel)
def p133 : Weak 28 14 := signedPick 1 [1,2,5,6,8,9,10,14,15,16,17,18,19,20] (by decide) (by decide) (by decide)
def r309 : Rule 28 5 := cutRule 5 p133 w186
def p134 : Weak 28 14 := signedPick 1 [1,3,5,7,11,12,13,14,15,16,17,18,21,22] (by decide) (by decide) (by decide)
def r310 : Rule 28 5 := cutRule 5 p134 w186
def f447 : ℕ := 0x27481c0
def f448 : ℕ := 0xff27fc0
def s327 : List ℕ := [f427,f447,f436,f448]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w187 : Wide 14 3 s327 := viaSearch (by decide +kernel)
def p135 : Weak 28 14 := signedPick 1 [1,2,3,5,6,7,8,9,10,11,12,13,14,15] (by decide) (by decide) (by decide)
def r311 : Rule 28 5 := cutRule 5 p135 w187
def f449 : ℕ := 0x260030
def f450 : ℕ := 0x261ff0
def f451 : ℕ := 0xfea7d0
def f452 : ℕ := 0x33f59e0
def s328 : List ℕ := [f449,f450,f451,f452]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w188 : Wide 13 3 s328 := viaSearch (by decide +kernel)
def p136 : Weak 28 13 := signedPick 2 [2,3,6,7,10,13,16,17,18,19,20,21,22] (by decide) (by decide) (by decide)
def r312 : Rule 28 5 := cutRule 5 p136 w188
def f453 : ℕ := 0x27f93fffc0
def s329 : List ℕ := [f28,f29,f453,f30,f31]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w189 : Wide 21 4 s329 := viaSearch (by decide +kernel)
def r313 : Rule 28 5 := cutRule 5 p10 w189
def f454 : ℕ := 0x2120003fc0
def s330 : List ℕ := [f454,f28,f29,f30,f31]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w190 : Wide 21 4 s330 := viaSearch (by decide +kernel)
def r314 : Rule 28 5 := cutRule 5 p10 w190
def f455 : ℕ := 0x903ff0
def f456 : ℕ := 0xf00380
def f457 : ℕ := 0x3fd4ff0
def f458 : ℕ := 0xc9eb070
def s331 : List ℕ := [f455,f456,f457,f458]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w191 : Wide 14 3 s331 := viaSearch (by decide +kernel)
def p137 : Weak 28 14 := signedPick 1 [1,2,5,6,8,9,10,11,12,13,14,15,19,20] (by decide) (by decide) (by decide)
def r315 : Rule 28 5 := cutRule 5 p137 w191
def f459 : ℕ := 0x9c0070
def f460 : ℕ := 0x3f14f80
def f461 : ℕ := 0xcfeb3f0
def s332 : List ℕ := [f455,f459,f460,f461]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w192 : Wide 14 3 s332 := viaSearch (by decide +kernel)
def p138 : Weak 28 14 := signedPick 2 [2,3,6,7,11,12,13,16,17,18,19,20,21,22] (by decide) (by decide) (by decide)
def r316 : Rule 28 5 := cutRule 5 p138 w192
def f462 : ℕ := 0xcf2b380
def s333 : List ℕ := [f455,f459,f457,f462]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w193 : Wide 14 3 s333 := viaSearch (by decide +kernel)
def p139 : Weak 28 14 := signedPick 1 [1,3,5,7,8,9,10,11,12,13,14,15,21,22] (by decide) (by decide) (by decide)
def r317 : Rule 28 5 := cutRule 5 p139 w193
def p140 : Weak 28 14 := signedPick 2 [2,3,6,7,8,9,10,16,17,18,19,20,21,22] (by decide) (by decide) (by decide)
def r318 : Rule 28 5 := cutRule 5 p140 w193
def f463 : ℕ := 0x7bdbeef8000ff
def s334 : List ℕ := [f35,f22,f23,f463]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b173 : Ban 28 5 s334 := viaRules (ws := []) (nilBan _ _)
  (dictionary [])
  (by decide) (by decide +kernel) (by decide +kernel)
def s335 : List ℕ := [f28,f29,f30,f31]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w194 : Wide 21 4 s335 := viaSearch (by decide +kernel)
def r319 : Rule 28 5 := cutRule 5 p10 w194
def s336 : List ℕ := [f34,f35,f22,f23,f463]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b174 : Ban 28 5 s336 := viaRules (ws := []) (nilBan _ _)
  (dictionary [])
  (by decide) (by decide +kernel) (by decide +kernel)
def f464 : ℕ := 0x18c366f98c7ff
def s337 : List ℕ := [f34,f464,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b175 : Ban 28 5 s337 := viaRules (ws := []) (nilBan _ _)
  (dictionary [])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w195 : Wide 21 3 s335 := viaSearch (by decide +kernel)
def r320 : Rule 28 5 := cutRule 5 p10 w195
def f465 : ℕ := 0x60d8aafe0f8ff
def s338 : List ℕ := [f34,f35,f465,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b176 : Ban 28 5 s338 := viaRules (ws := []) (nilBan _ _)
  (dictionary [])
  (by decide) (by decide +kernel) (by decide +kernel)
def f466 : ℕ := 0x7b00ccfff00ff
def s339 : List ℕ := [f34,f35,f22,f466]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b177 : Ban 28 5 s339 := viaRules (ws := []) (nilBan _ _)
  (dictionary [])
  (by decide) (by decide +kernel) (by decide +kernel)
def f467 : ℕ := 0x7fffeefffffff
def s340 : List ℕ := [f34,f35,f22,f23,f467]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b172 : Ban 28 6 s340 := viaRules (ws := [s334,s336,s337,s338,s339]) (consBan b173 (consBan b174 (consBan b175 (consBan b176 (consBan b177 (nilBan _ _))))))
  (dictionary [(1507229979,r302),(1938952286,r303),(1251548370,r301),(1656046280,r304),(1680934597,r305),(1819700153,r306),(45765491,r307),(1688301380,r308),(1439710484,r17),(1750944059,r47),(1252167197,r309),(1419470240,r310),(1978647377,r311),(676095624,r312),(750313251,r313),(1294058082,r314),(1715654913,r94),(1714009921,r110),(489262107,r315),(742935093,r316),(1800844903,r148),(94850740,r169),(1884475438,r317),(1154712758,r318),(867505034,r319),(49944213,r319),(1087366802,r319),(1853769549,r320),(1199629177,r319),(89568119,r319),(952520383,r220),(1065381404,r320),(2089917930,r319),(459692855,r319),(576655536,r319),(1093914108,r319),(1022935720,r319),(42656459,r319),(966315821,r319),(2133520207,r319)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f468 : ℕ := 0x60d8bbf8000ff
def s341 : List ℕ := [f35,f20,f21,f468,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b178 : Ban 28 6 s341 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1314470333,r14),(525185958,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p141 : Weak 28 8 := signedPick 0 [0,1,2,4,5,6,14,15] (by decide) (by decide) (by decide)
def r321 : Rule 28 5 := cutRule 5 p141 w177
def s342 : List ℕ := [f34,f35,f20,f21,f468,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b179 : Ban 28 6 s342 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(45765491,r307),(1681950975,r14),(491368409,r12),(435500842,r5),(1389419873,r321)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f469 : ℕ := 0x7b00ddf8000ff
def s343 : List ℕ := [f35,f20,f21,f22,f469,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b180 : Ban 28 6 s343 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1385633517,r31),(2145161556,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f470 : ℕ := 0x12c0
def s344 : List ℕ := [f470,f74,f75,f77]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w196 : Wide 8 3 s344 := viaSearch (by decide +kernel)
def p142 : Weak 28 8 := signedPick 0 [0,1,2,4,5,6,19,20] (by decide) (by decide) (by decide)
def r322 : Rule 28 5 := cutRule 5 p142 w196
def s345 : List ℕ := [f34,f35,f20,f21,f22,f469,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b181 : Ban 28 6 s345 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(750313251,r313),(538346446,r31),(1795149002,r12),(586727889,r5),(1049778521,r322)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s346 : List ℕ := [f34,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b169 : Ban 28 7 s346 := viaRules (ws := [s315,s318,s175,s186,s254,s261,s340,s341,s342,s10,s36,s210,s202,s286,s278,s343,s345,s71,s84,s234,s225,s312,s303,s121,s131]) (consBan b170 (consBan b171 (consBan b82 (consBan b85 (consBan b131 (consBan b134 (consBan b172 (consBan b178 (consBan b179 (consBan b4 (consBan b12 (consBan b101 (consBan b98 (consBan b151 (consBan b147 (consBan b180 (consBan b181 (consBan b28 (consBan b35 (consBan b117 (consBan b114 (consBan b167 (consBan b163 (consBan b51 (consBan b58 (nilBan _ _))))))))))))))))))))))))))
  (dictionary [(1369480801,r42),(371857128,r204),(1801203108,r0),(803579435,r262),(1518297102,r0),(817046336,r10),(356027579,r10),(1966906310,r10),(1176912795,r203),(640307879,r203),(305890227,r3),(374262269,r3),(247761711,r3),(1883528599,r3),(1397621685,r3),(904282277,r204),(418375363,r204),(797442893,r10),(849816804,r10),(1351215981,r10),(1300517979,r3),(814611065,r3),(1543185419,r41),(545561746,r205),(1681950975,r0),(684327302,r278),(1550552202,r0),(116794346,r56),(284097389,r72),(1667589774,r233),(1130984858,r233),(316846660,r3),(1869308957,r3),(1518420467,r205),(1032513553,r205),(1675045932,r10),(426079147,r10),(1840898199,r0),(843274526,r206),(538346446,r41),(1688206420,r291),(1156308904,r41),(1501372903,r117),(1755045889,r132),(2055159465,r246),(1518554549,r246),(388009844,r3),(19939926,r3),(216135299,r206),(1877712032,r206),(1147537883,r10),(1870787437,r10),(749102587,r182),(19339907,r196)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r323 : Rule 28 5 := cutRule 5 p2 w11
def r324 : Rule 28 5 := cutRule 5 p2 w30
def r325 : Rule 28 5 := cutRule 5 p34 w35
def r326 : Rule 28 5 := cutRule 5 p43 w35
def r327 : Rule 28 5 := cutRule 5 p2 w54
def r328 : Rule 28 5 := cutRule 5 p2 w60
def r329 : Rule 28 5 := cutRule 5 p62 w65
def r330 : Rule 28 5 := cutRule 5 p70 w74
def r331 : Rule 28 5 := cutRule 5 p2 w85
def r332 : Rule 28 5 := cutRule 5 p2 w89
def r333 : Rule 28 5 := cutRule 5 p88 w97
def r334 : Rule 28 5 := cutRule 5 p93 w97
def s347 : List ℕ := [f464,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b183 : Ban 28 6 s347 := viaRules (ws := [s337]) (consBan b175 (nilBan _ _))
  (dictionary [(1173507732,r5),(347717999,r12),(1598659925,r261),(1547961923,r209),(1062055009,r209),(25056056,r5),(1164345156,r323),(1973499846,r324),(1261855935,r325),(1642026027,r326),(1674775298,r5),(1079753948,r5),(885490923,r12),(1784007785,r12),(586275119,r327),(1936565708,r328),(741884925,r329),(965490880,r330),(1745938482,r5),(1377868564,r5),(357982874,r12),(1081232428,r12),(2023400690,r331),(317406527,r332),(2107031225,r333),(1377268545,r334)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s348 : List ℕ := [f464,f35,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b184 : Ban 28 6 s348 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(927632226,r5),(1287937191,r5),(813202767,r5),(1663818865,r5),(1732190907,r5),(2134896681,r12),(7887884,r12),(60261795,r12),(488598867,r261),(437900865,r209),(804040191,r323),(901550970,r325),(1973499846,r324),(1474722984,r325),(1642026027,r326),(225970154,r327),(381579960,r329),(1936565708,r328),(711817894,r329),(965490880,r330)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f471 : ℕ := 0x673c880673800
def s349 : List ℕ := [f20,f21,f22,f471,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b185 : Ban 28 6 s349 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1174741020,r5),(676976615,r14),(2035175887,r14),(176700861,r14),(1531815948,r14),(748139799,r31),(1507667838,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s350 : List ℕ := [f35,f20,f21,f465,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b186 : Ban 28 6 s350 := viaRules (ws := [s338]) (consBan b176 (nilBan _ _))
  (dictionary [(1556308935,r5),(1624680977,r5),(2047861601,r12),(2100235512,r12),(1491149995,r261),(1440451993,r209),(954545079,r209),(2065029773,r5),(1056835226,r323),(1865989916,r324),(1367213054,r325),(295473514,r326),(1503596265,r5),(1062692874,r12),(1830700770,r327),(1829055778,r328),(604307964,r329),(857980950,r330),(1638428552,r5),(1270358634,r5),(250472944,r12),(973722498,r12),(193257894,r331),(209896597,r332),(704162593,r333),(1269758615,r334)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s351 : List ℕ := [f35,f20,f21,f465,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b187 : Ban 28 6 s351 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2008408567,r261),(1957710565,r209),(804040191,r323),(42678479,r326),(1250801230,r5),(809897839,r12),(1865989916,r324),(1367213054,r325),(1534516097,r326),(1567265368,r5),(972244018,r5),(777980993,r12),(1676497855,r12),(927632226,r5),(1180427261,r5),(2087946506,r331),(451367558,r333),(209896597,r332),(1999521295,r333),(1269758615,r334)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f472 : ℕ := 0x1f274401f0700
def s352 : List ℕ := [f35,f472,f20,f21,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b188 : Ban 28 6 s352 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(43046541,r14),(367827243,r14),(534599207,r14),(449560458,r14),(551767379,r5),(125166158,r31),(884694197,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s353 : List ℕ := [f35,f20,f21,f22,f466]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b189 : Ban 28 6 s353 := viaRules (ws := [s339]) (consBan b177 (nilBan _ _))
  (dictionary [(489326725,r5),(557698767,r5),(980879391,r12),(1033253302,r12),(424167785,r261),(373469783,r209),(2035046516,r209),(998047563,r5),(487774131,r323),(799007706,r324),(300230844,r325),(467533887,r326),(500283158,r5),(2052745455,r5),(1858482430,r12),(609515645,r12),(1559266626,r327),(762073568,r328),(1684809401,r329),(1277054618,r330),(662593094,r5),(1558874565,r12),(1273759331,r331),(1290398034,r332),(932539085,r333),(1755097859,r334)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s354 : List ℕ := [f35,f20,f21,f22,f466,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b190 : Ban 28 6 s354 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1591372171,r261),(1540674169,r209),(225970154,r327),(2091241793,r330),(1476780269,r5),(225578093,r12),(2087946506,r331),(421801387,r334),(762073568,r328),(1684809401,r329),(1938482387,r330),(571446342,r5),(203376424,r5),(1330974381,r12),(2054223935,r12),(1290398034,r332),(932539085,r333),(202776405,r334),(927632226,r5),(113445051,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f473 : ℕ := 0x4ff22000ff00
def s355 : List ℕ := [f473,f35,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b191 : Ban 28 6 s355 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(25843978,r31),(432706826,r14),(765101176,r31),(924259492,r14),(941427664,r5),(443663259,r14),(1801862531,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s356 : List ℕ := [f35,f20,f21,f22,f23,f467]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b182 : Ban 28 7 s356 := viaRules (ws := [s340,s347,s348,s349,s350,s351,s352,s353,s354,s355]) (consBan b172 (consBan b183 (consBan b184 (consBan b185 (consBan b186 (consBan b187 (consBan b188 (consBan b189 (consBan b190 (consBan b191 (nilBan _ _)))))))))))
  (dictionary [(1750792573,r3),(1416374921,r207),(1111280499,r3),(1484746963,r207),(1528860057,r10),(1907927587,r259),(1767800715,r10),(1960301498,r259),(1351215981,r10),(1300517979,r3),(814611065,r3),(897227648,r3),(360622732,r207),(1415814271,r3),(929907357,r3),(1414822327,r20),(1726055902,r49),(1227279040,r57),(1394582083,r73),(93985905,r3),(1427331354,r207),(832310004,r207),(1991176611,r3),(2142998247,r10),(638046979,r259),(1536563841,r259),(1722294382,r10),(1690766756,r97),(1689121764,r112),(464373950,r118),(718046936,r133),(481555596,r3),(1498494538,r207),(1130424620,r207),(11774191,r3),(840713079,r10),(110538930,r259),(833788484,r259),(56369125,r10),(1775956746,r155),(69962583,r171),(1859587281,r183),(1129824601,r197),(25056056,r3),(1062478645,r3),(1716020371,r0),(1828881392,r207),(1174741020,r3),(2099302588,r0),(64679962,r3),(927632226,r3),(1040493247,r207),(247761711,r3),(817046336,r10),(2065029773,r3),(434804698,r3),(551767379,r3),(956164930,r0),(1069025951,r3),(998047563,r3),(17768302,r3),(941427664,r3),(1995771029,r41),(2108632050,r3)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f474 : ℕ := 0xc
def f475 : ℕ := 0x34
def s357 : List ℕ := [f474,f475]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w197 : Wide 3 1 s357 := viaSearch (by decide +kernel)
def p143 : Weak 28 3 := signedPick 0 [0,1,14] (by decide) (by decide) (by decide)
def r335 : Rule 28 5 := cutRule 5 p143 w197
def f476 : ℕ := 0x245fe93f
def f477 : ℕ := 0x452ff1cf
def f478 : ℕ := 0x6837fe0f
def f479 : ℕ := 0x6d7be00f
def s358 : List ℕ := [f476,f477,f478,f479]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w198 : Wide 18 4 s358 := viaSearch (by decide +kernel)
def p144 : Weak 28 18 := relaxed (pick [0,1,2,3,8,10,11,13,14,16,18,19,21,23,24,25,26,27] (by decide) (by decide) (by decide))
def r336 : Rule 28 5 := cutRule 5 p144 w198
def f480 : ℕ := 0x122e93f
def f481 : ℕ := 0x22971cf
def f482 : ℕ := 0x341be0f
def f483 : ℕ := 0x36bc00f
def s359 : List ℕ := [f480,f481,f482,f483]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w199 : Wide 13 4 s359 := viaSearch (by decide +kernel)
def p145 : Weak 28 13 := relaxed (pick [4,5,6,7,9,10,12,13,15,17,18,20,22] (by decide) (by decide) (by decide))
def r337 : Rule 28 5 := cutRule 5 p145 w199
def p146 : Weak 28 3 := signedPick 0 [0,2,19] (by decide) (by decide) (by decide)
def r338 : Rule 28 5 := cutRule 5 p146 w197
def p147 : Weak 28 3 := signedPick 0 [0,3,21] (by decide) (by decide) (by decide)
def r339 : Rule 28 5 := cutRule 5 p147 w197
def f484 : ℕ := 0x29490ef80000f
def f485 : ℕ := 0x5292e000000f0
def s360 : List ℕ := [f35,f484,f485,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b193 : Ban 28 6 s360 := viaRules (ws := [s334]) (consBan b173 (nilBan _ _))
  (dictionary [(857882109,r335),(1650250669,r335),(1450515654,r336),(2019800279,r337),(2138017396,r335),(301767324,r335),(1950474109,r335),(2117777152,r335),(398600260,r335),(316867045,r335),(266478178,r338),(264833186,r335),(1187569019,r335),(1441242005,r338),(324480693,r338),(1732707142,r335),(351668168,r339),(793157652,r335),(435298703,r335),(1853019670,r338)])
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b194 : Ban 28 6 s346 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1801203108,r14),(356027579,r12),(1176912795,r213),(1883528599,r5),(904282277,r214),(1837122895,r319),(1681950975,r14),(1667589774,r237),(1518420467,r226),(538346446,r31),(2055159465,r250),(216135299,r229)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s361 : List ℕ := [f35,f20,f485,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b192 : Ban 28 7 s361 := viaRules (ws := [s360,s346]) (consBan b193 (consBan b194 (nilBan _ _)))
  (dictionary [(722924462,r203),(186319546,r3),(1999385541,r207),(1694291119,r3),(456878852,r225),(2067757583,r207),(2004447794,r3),(552835788,r207),(23211363,r0),(719083004,r3),(814194579,r0),(1510066220,r207),(995701456,r203),(1691573097,r3),(897227648,r3),(1812234738,r3),(360622732,r207),(2111870677,r215),(343454560,r10),(203327688,r21),(395828471,r10),(1883528599,r3),(1397621685,r3),(2049522893,r10),(1998824891,r3),(1512917977,r3),(1997832947,r21),(161582875,r21),(1810289660,r57),(1977592703,r73),(1213601441,r233),(676996525,r3),(2010341974,r207),(1951925540,r225),(1415320624,r207),(426703584,r3),(947217601,r3),(1643089242,r207),(1826771641,r0),(375159635,r3),(1789054939,r233),(337442933,r3),(1628294602,r0),(176682596,r207),(578525220,r227),(1221057599,r10),(2119574461,r10),(157821355,r21),(126293729,r98),(124648737,r21),(1047384570,r118),(1301057556,r133),(1601171132,r246),(1064566216,r3),(2081505158,r207),(102556509,r225),(1713435240,r207),(594784811,r3),(1098444648,r3),(1794316289,r207),(514091672,r41),(1209963313,r3),(1240181960,r246),(1936053601,r3),(896651052,r41),(1592522693,r207),(1423723699,r230),(693549550,r10),(1416799104,r10),(639379745,r98),(211483719,r156),(652973203,r21),(295114254,r183),(1712835221,r197)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s362 : List ℕ := [f35,f484,f20,f21,f22,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b195 : Ban 28 7 s362 := viaRules (ws := [s346,s360]) (consBan b194 (consBan b193 (nilBan _ _)))
  (dictionary [(1645641073,r10),(763313692,r259),(1487014870,r0),(604687489,r10),(21826019,r0),(1286982285,r259),(1911184831,r204),(1028857450,r10),(755604171,r202),(421186519,r3),(116092097,r22),(489558561,r3),(356027579,r10),(1966906310,r10),(1019578569,r204),(533671655,r10),(912739185,r259),(772612313,r10),(1451020010,r273),(965113096,r259),(1812234738,r3),(1415814271,r3),(929907357,r3),(2049522893,r10),(1998824891,r3),(1512917977,r3),(419633925,r22),(730867500,r22),(232090638,r58),(399393681,r74),(952387166,r10),(70059785,r259),(1425699895,r0),(543372514,r10),(584765538,r205),(1849921804,r10),(1710027817,r0),(827700436,r259),(1246281150,r232),(432142952,r3),(1984605249,r3),(995988209,r22),(1633716759,r205),(1147809845,r10),(1790342224,r259),(1027282353,r273),(541375439,r259),(727105980,r10),(695578354,r99),(693933362,r22),(1616669195,r119),(1870342181,r134),(108684112,r10),(1373840378,r259),(1740521923,r41),(858194542,r10),(364625539,r206),(1629781805,r10),(1635908250,r41),(753580869,r259),(1633850841,r245),(503306136,r3),(135236218,r3),(1164069436,r99),(331431591,r206),(1993008324,r10),(1262834175,r259),(324506996,r273),(1986083729,r259),(1208664370,r10),(780768344,r157),(1222257828,r22),(864398879,r184),(134636199,r198)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s363 : List ℕ := [f35,f22,f23,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b0 : Ban 28 8 s363 := viaRules (ws := [s33,s41,s55,s64,s82,s89,s102,s114,s129,s136,s148,s157,s163,s173,s176,s191,s194,s201,s203,s213,s216,s224,s227,s237,s240,s252,s255,s264,s267,s277,s279,s288,s291,s302,s305,s314,s346,s356,s361,s362]) (consBan b1 (consBan b11 (consBan b15 (consBan b20 (consBan b25 (consBan b34 (consBan b38 (consBan b43 (consBan b48 (consBan b57 (consBan b61 (consBan b66 (consBan b71 (consBan b74 (consBan b81 (consBan b83 (consBan b88 (consBan b91 (consBan b97 (consBan b99 (consBan b104 (consBan b107 (consBan b113 (consBan b115 (consBan b120 (consBan b123 (consBan b130 (consBan b132 (consBan b137 (consBan b140 (consBan b146 (consBan b148 (consBan b153 (consBan b156 (consBan b162 (consBan b164 (consBan b169 (consBan b182 (consBan b192 (consBan b195 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))
  (dictionary [])
  (by decide) (by decide +kernel) (by decide +kernel)
theorem cert6 : Ban 28 8 s363 := b0
end PEqualNP.Outside.L_meta_12092.B0

namespace PEqualNP.Outside.L_meta_12092.B1
def f0 : ℕ := 0xa3c
def f1 : ℕ := 0xb4c
def f2 : ℕ := 0xeb0
def s0 : List ℕ := [f0,f1,f2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w0 : Wide 6 3 s0 := viaSearch (by decide +kernel)
def p0 : Weak 28 6 := signedPick 1 [1,2,6,8,9,11] (by decide) (by decide) (by decide)
def r0 : Rule 28 6 := cutRule 6 p0 w0
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w1 : Wide 6 2 s0 := viaSearch (by decide +kernel)
def p1 : Weak 28 6 := signedPick 7 [7,8,15,17,22,24] (by decide) (by decide) (by decide)
def r1 : Rule 28 6 := cutRule 6 p1 w1
def p2 : Weak 28 6 := signedPick 4 [4,5,7,8,10,11] (by decide) (by decide) (by decide)
def r2 : Rule 28 6 := cutRule 6 p2 w0
def r3 : Rule 28 6 := cutRule 6 p1 w0
def p3 : Weak 28 6 := signedPick 0 [0,2,3,5,9,10] (by decide) (by decide) (by decide)
def r4 : Rule 28 6 := cutRule 6 p3 w0
def p4 : Weak 28 6 := signedPick 0 [0,1,3,4,6,7] (by decide) (by decide) (by decide)
def r5 : Rule 28 6 := cutRule 6 p4 w0
def f3 : ℕ := 0xa83f0
def f4 : ℕ := 0xbd4f0
def f5 : ℕ := 0xeab00
def s1 : List ℕ := [f3,f4,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w2 : Wide 10 2 s1 := viaSearch (by decide +kernel)
def p5 : Weak 28 10 := signedPick 7 [7,8,10,11,15,17,18,20,22,24] (by decide) (by decide) (by decide)
def r6 : Rule 28 5 := cutRule 5 p5 w2
def f6 : ℕ := 0x1573fc
def f7 : ℕ := 0x428c3c
def f8 : ℕ := 0xa80fc0
def s2 : List ℕ := [f6,f7,f8]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w3 : Wide 12 4 s2 := viaSearch (by decide +kernel)
def p6 : Weak 28 12 := signedPick 4 [4,5,7,8,10,11,15,17,18,20,22,24] (by decide) (by decide) (by decide)
def r7 : Rule 28 5 := cutRule 5 p6 w3
def f9 : ℕ := 0xac3f8
def f10 : ℕ := 0xae438
def f11 : ℕ := 0xfdbc0
def s3 : List ℕ := [f9,f10,f11]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w4 : Wide 10 3 s3 := viaSearch (by decide +kernel)
def p7 : Weak 28 10 := signedPick 0 [0,1,2,3,4,5,6,7,9,10] (by decide) (by decide) (by decide)
def r8 : Rule 28 5 := cutRule 5 p7 w4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w5 : Wide 10 3 s1 := viaSearch (by decide +kernel)
def r9 : Rule 28 5 := cutRule 5 p5 w5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w6 : Wide 10 2 s3 := viaSearch (by decide +kernel)
def r10 : Rule 28 5 := cutRule 5 p7 w6
def f12 : ℕ := 0x201009820703f
def f13 : ℕ := 0x1568db07ff8ff8
def f14 : ℕ := 0x62df6ffe3fffff
def f15 : ℕ := 0x6c06b46fc07fc7
def f16 : ℕ := 0x7bb70007fff000
def s4 : List ℕ := [f12,f13,f14,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b2 : Ban 28 6 s4 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2028083290,r6),(1758858088,r6),(2101195815,r6),(383016868,r6),(876154748,r7),(1225008989,r8),(1865404691,r9),(1328982463,r9),(1677836704,r8),(1979826756,r10),(390216003,r8),(554935682,r9),(903789923,r10),(307667086,r6),(164856589,r6),(484814466,r9),(798863376,r6),(1164378557,r6),(1752260017,r9),(581110893,r8),(689919569,r10),(1444200677,r10),(1044135047,r9),(61184918,r9),(88233653,r8),(890567417,r9),(2032278125,r10),(1446072357,r8),(1374202032,r10),(1994152515,r9),(988379576,r8),(1194497819,r10),(1714146082,r10),(966107524,r8),(1681442322,r10),(890388882,r8)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p8 : Weak 28 6 := signedPick 4 [4,5,15,17,18,20] (by decide) (by decide) (by decide)
def r11 : Rule 28 6 := cutRule 6 p8 w0
def p9 : Weak 28 6 := signedPick 10 [10,11,18,20,22,24] (by decide) (by decide) (by decide)
def r12 : Rule 28 6 := cutRule 6 p9 w1
def r13 : Rule 28 5 := cutRule 5 p1 w1
def f17 : ℕ := 0x128f3c
def f18 : ℕ := 0x13f03c
def f19 : ℕ := 0x76d70c
def f20 : ℕ := 0xbbab30
def s5 : List ℕ := [f17,f18,f19,f20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w7 : Wide 12 3 s5 := viaSearch (by decide +kernel)
def p10 : Weak 28 12 := signedPick 1 [1,2,6,8,9,11,13,14,22,23,25,26] (by decide) (by decide) (by decide)
def r14 : Rule 28 5 := cutRule 5 p10 w7
def f21 : ℕ := 0x221b0dba23f1ff
def f22 : ℕ := 0x42c562dc3c7e3f
def f23 : ℕ := 0x7bb7009ffff03f
def s6 : List ℕ := [f13,f21,f22,f15,f23]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b3 : Ban 28 6 s6 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1345550921,r13),(427920980,r13),(474982842,r13),(191228490,r13),(1762247651,r14)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f24 : ℕ := 0x250ff8
def f25 : ℕ := 0x2f90f8
def f26 : ℕ := 0x75a718
def f27 : ℕ := 0xb74b60
def s7 : List ℕ := [f24,f25,f26,f27]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w8 : Wide 12 4 s7 := viaSearch (by decide +kernel)
def p11 : Weak 28 12 := signedPick 12 [12,13,14,16,17,19,20,21,23,24,25,26] (by decide) (by decide) (by decide)
def r15 : Rule 28 6 := cutRule 6 p11 w8
def f28 : ℕ := 0xeedccc
def f29 : ℕ := 0xfbaf30
def s8 : List ℕ := [f7,f8,f28,f29]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w9 : Wide 12 5 s8 := viaSearch (by decide +kernel)
def r16 : Rule 28 6 := cutRule 6 p6 w9
def f30 : ℕ := 0xf7ef78
def s9 : List ℕ := [f24,f25,f26,f27,f30]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w10 : Wide 12 4 s9 := viaSearch (by decide +kernel)
def r17 : Rule 28 6 := cutRule 6 p11 w10
def f31 : ℕ := 0xb7c
def s10 : List ℕ := [f0,f1,f31,f2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w11 : Wide 6 3 s10 := viaSearch (by decide +kernel)
def r18 : Rule 28 6 := cutRule 6 p1 w11
def s11 : List ℕ := [f12,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b1 : Ban 28 7 s11 := viaRules (ws := [s4,s6]) (consBan b2 (consBan b3 (nilBan _ _)))
  (dictionary [(270128608,r0),(1259378551,r1),(903406,r2),(990153349,r1),(343241133,r3),(1332491076,r1),(772545833,r2),(1761795776,r1),(108393409,r4),(1511498185,r4),(1097643352,r4),(210837661,r3),(1944466475,r3),(900726716,r5),(1389715289,r1),(1932916950,r3),(1519062117,r5),(354898227,r5),(1350143835,r5),(1344148170,r5),(888507504,r3),(882511839,r1),(2130580422,r4),(1414993882,r1),(174670051,r3),(168674386,r4),(1751548881,r4),(1343689713,r5),(1337694048,r5),(697196051,r2),(1686445994,r1),(2068110612,r0),(909876908,r3),(1058375294,r11),(2047625237,r3),(554385554,r0),(1543635497,r1),(1863593374,r3),(30158637,r1),(395673818,r1),(983555278,r3),(2082093937,r12),(1674417047,r5),(448455820,r5),(1374762039,r12),(2090852142,r1),(1772168766,r4),(1104315155,r4),(204275347,r1),(1833729642,r5),(675495938,r5),(427891073,r15),(275430308,r3),(1417141016,r3),(450713883,r16),(1592424591,r5),(1439963826,r3),(434190887,r5),(477762618,r3),(1467012561,r1),(121862678,r3),(1263573386,r5),(677367618,r1),(605497293,r5),(1225447776,r3),(219674837,r3),(1051893355,r5),(1106849365,r5),(2088296557,r5),(288274605,r5),(1432706621,r5),(2072266359,r4),(854767900,r5),(1409807820,r4),(945441343,r5),(197402785,r17),(912737583,r5),(121684143,r18)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r19 : Rule 28 6 := cutRule 6 p4 w1
def r20 : Rule 28 6 := cutRule 6 p3 w1
def r21 : Rule 28 5 := cutRule 5 p4 w1
def r22 : Rule 28 5 := cutRule 5 p3 w1
def f32 : ℕ := 0x283c
def f33 : ℕ := 0x6d0c
def f34 : ℕ := 0xba30
def s12 : List ℕ := [f32,f33,f34]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w12 : Wide 8 3 s12 := viaSearch (by decide +kernel)
def p12 : Weak 28 8 := signedPick 0 [0,1,3,4,6,7,12,13] (by decide) (by decide) (by decide)
def r23 : Rule 28 5 := cutRule 5 p12 w12
def f35 : ℕ := 0x484b063f8ff8
def s13 : List ℕ := [f35,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b5 : Ban 28 6 s13 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(232138684,r21),(1461992390,r22),(1328982463,r9),(1600758293,r23)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f36 : ℕ := 0x91cc
def f37 : ℕ := 0x1d4c0
def f38 : ℕ := 0x361f0
def f39 : ℕ := 0x3bbcc
def s14 : List ℕ := [f36,f37,f38,f39]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w13 : Wide 9 3 s14 := viaSearch (by decide +kernel)
def p13 : Weak 28 9 := signedPick 0 [0,1,3,4,12,13,15,16,21] (by decide) (by decide) (by decide)
def r24 : Rule 28 6 := cutRule 6 p13 w13
def f40 : ℕ := 0xa0c
def s15 : List ℕ := [f40,f0,f1,f2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w14 : Wide 6 3 s15 := viaSearch (by decide +kernel)
def r25 : Rule 28 6 := cutRule 6 p4 w14
def r26 : Rule 28 6 := cutRule 6 p12 w12
def f41 : ℕ := 0x12803c
def s16 : List ℕ := [f41,f17,f19,f20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w15 : Wide 12 4 s16 := viaSearch (by decide +kernel)
def p14 : Weak 28 12 := signedPick 0 [0,1,3,4,6,7,12,13,15,16,21,25] (by decide) (by decide) (by decide)
def r27 : Rule 28 6 := cutRule 6 p14 w15
def s17 : List ℕ := [f13,f21,f22,f14,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b4 : Ban 28 7 s17 := viaRules (ws := [s4,s13]) (consBan b2 (consBan b5 (nilBan _ _)))
  (dictionary [(260331014,r19),(749319587,r5),(878666415,r19),(1490184720,r20),(774598180,r4),(1675762331,r20),(1751548881,r4),(1343689713,r5),(1337694048,r5),(1117607301,r5),(703752468,r19),(463243315,r5),(457247650,r5),(268736263,r5),(221872074,r5),(570726315,r19),(779744968,r2),(1128599209,r5),(1293318888,r5),(1642173129,r19),(354898227,r5),(108393409,r4),(1223197672,r24),(1537246582,r3),(1902761763,r3),(343159576,r25),(1441698235,r5),(1034021345,r19),(1955543765,r19),(1450456440,r4),(1131773064,r20),(463919453,r20),(970639858,r11),(1319494099,r5),(1079448534,r5),(1428302775,r19),(1687259522,r5),(2036113763,r19),(1521969137,r0),(1870823378,r5),(1628950623,r26),(623177684,r19),(36971916,r5),(2112585238,r19),(585052074,r27),(1726762782,r5),(466453663,r19),(1447900855,r19),(1431870657,r5),(214372198,r19),(734117056,r5),(1082971297,r19),(1584026784,r5),(1932881025,r19),(91224444,r5),(440078685,r19),(1834016400,r5),(35386994,r19),(305045641,r19),(1704490730,r5),(272341881,r19),(1628772088,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f42 : ℕ := 0x59e
def f43 : ℕ := 0x1266
def f44 : ℕ := 0x2878
def s18 : List ℕ := [f42,f43,f44]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w16 : Wide 7 4 s18 := viaSearch (by decide +kernel)
def p15 : Weak 28 7 := signedPick 4 [4,7,8,15,17,22,24] (by decide) (by decide) (by decide)
def r28 : Rule 28 6 := cutRule 6 p15 w16
def f45 : ℕ := 0x40c462441c0e00
def s19 : List ℕ := [f13,f21,f45,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b6 : Ban 28 7 s19 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1724379728,r3),(1310524895,r5),(266785136,r19),(755773709,r5),(1298975370,r3),(885120537,r19),(581990710,r5),(937299073,r19),(301269121,r2),(656577484,r5),(284655607,r5),(639963970,r19),(1510064356,r3),(1865372719,r5),(1117607301,r5),(348444105,r5),(703752468,r19),(248570259,r1),(1496638842,r4),(781052302,r1),(1682216453,r4),(1350143835,r5),(1344148170,r5),(883552270,r28),(877556605,r4),(469697437,r5),(463701772,r5),(988839807,r3),(1229651794,r3),(1543700704,r1),(1909215885,r1),(349613698,r3),(1448152357,r5),(1040475467,r19),(1961997887,r19),(1405058021,r5),(1760366384,r19),(1204714210,r0),(1560022573,r5),(1346473964,r11),(1701782327,r5),(1982381608,r5),(190206324,r19),(1456910562,r1),(1717817414,r1),(1635404745,r3),(629631806,r19),(43426038,r5),(2119039360,r19),(591506196,r3),(1733216904,r5),(472907785,r19),(1454354977,r19),(416813031,r5),(772121394,r19),(1521660531,r5),(1876968894,r19),(2031810000,r5),(239634716,r19),(59638553,r5),(414946916,r19),(798765041,r19),(1438324779,r5),(220826320,r19),(775866240,r5),(311499763,r19),(1710944852,r5),(278796003,r19),(1635226210,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r29 : Rule 28 6 := cutRule 6 p9 w0
def f46 : ℕ := 0x201a0d220381c0
def s20 : List ℕ := [f13,f46,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b7 : Ban 28 7 s20 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(247109645,r4),(355913190,r20),(1249002792,r2),(1357806337,r4),(709200199,r4),(818003744,r20),(1628025347,r29),(1736828892,r4),(1064020077,r12),(20280318,r5),(509268891,r3),(638615719,r5),(988839807,r3),(1511498185,r4),(1097643352,r4),(8061106,r29),(2065441,r4),(1250134024,r20),(534547484,r4),(1441707300,r29),(1435711635,r20),(348444105,r5),(463243315,r5),(457247650,r5),(883552270,r28),(877556605,r4),(469697437,r5),(463701772,r5),(983146976,r29),(1297195886,r3),(1662711067,r3),(103108880,r29),(892874673,r4),(1001678218,r20),(1958110006,r0),(2066913551,r4),(1131534869,r11),(1240338414,r4),(1655678939,r4),(1764482484,r20),(1201647539,r12),(494315641,r12),(1210405744,r4),(891722368,r20),(223868757,r20),(1388899927,r29),(383126988,r5),(1944404867,r4),(1872534542,r5),(345001378,r29),(1486712086,r4),(1143400473,r5),(1252204018,r5),(207086466,r4),(315890011,r20),(75836321,r5),(184639866,r5),(1236995497,r4),(1345799042,r20),(171446957,r5),(226402967,r5),(1207850159,r5),(1555311854,r5),(1191819961,r20),(2121805149,r5),(64994945,r5),(1464440034,r4),(32291185,r5),(1388721392,r4)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r30 : Rule 28 6 := cutRule 6 p8 w1
def f47 : ℕ := 0xb98c0
def f48 : ℕ := 0xee730
def s21 : List ℕ := [f3,f47,f48]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w17 : Wide 10 2 s21 := viaSearch (by decide +kernel)
def p16 : Weak 28 10 := signedPick 4 [4,5,10,11,15,17,18,20,22,24] (by decide) (by decide) (by decide)
def r31 : Rule 28 5 := cutRule 5 p16 w17
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w18 : Wide 10 3 s21 := viaSearch (by decide +kernel)
def r32 : Rule 28 5 := cutRule 5 p16 w18
def f49 : ℕ := 0xb43f8
def f50 : ℕ := 0xbc8e0
def f51 : ℕ := 0xf7718
def s22 : List ℕ := [f49,f50,f51]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w19 : Wide 10 3 s22 := viaSearch (by decide +kernel)
def p17 : Weak 28 10 := signedPick 0 [0,1,2,3,4,6,7,8,9,11] (by decide) (by decide) (by decide)
def r33 : Rule 28 5 := cutRule 5 p17 w19
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w20 : Wide 10 2 s22 := viaSearch (by decide +kernel)
def r34 : Rule 28 5 := cutRule 5 p17 w20
def f52 : ℕ := 0xb9230c
def s23 : List ℕ := [f8,f52,f28]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w21 : Wide 12 4 s23 := viaSearch (by decide +kernel)
def r35 : Rule 28 5 := cutRule 5 p6 w21
def f53 : ℕ := 0x2002042a0071c7
def f54 : ℕ := 0x6e1fbdffe3ffff
def s24 : List ℕ := [f13,f53,f22,f54,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b9 : Ban 28 6 s24 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1072070567,r31),(126044846,r31),(927975977,r31),(1656453596,r31),(260365045,r32),(1508433628,r31),(792847088,r31),(1694011239,r32),(1064299200,r31),(1259977822,r31),(582279133,r32),(1267856373,r33),(869352567,r34),(650424797,r33),(1459437469,r32),(2145014709,r34),(226189102,r35),(911766342,r33),(1319443232,r32),(1869614911,r33),(1446551683,r34),(1647199531,r32),(641426592,r34),(55220824,r33),(2130834146,r34),(603300982,r32),(1745011690,r33),(186859258,r34),(1981098003,r32),(923899921,r32),(2053986380,r33),(810559827,r34),(1450119565,r33),(232621106,r34),(787661026,r33),(1612690898,r34)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r36 : Rule 28 5 := cutRule 5 p8 w1
def p18 : Weak 28 12 := signedPick 0 [0,2,3,5,9,10,12,14,18,19,21,26] (by decide) (by decide) (by decide)
def r37 : Rule 28 5 := cutRule 5 p18 w7
def f55 : ℕ := 0x7bb7042ffff1c7
def s25 : List ℕ := [f13,f21,f22,f15,f55]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b10 : Ban 28 6 s25 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1525881763,r36),(608251822,r36),(655313684,r36),(1546186687,r36),(1468085448,r37)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f56 : ℕ := 0xbfdbf8
def s26 : List ℕ := [f24,f25,f26,f27,f56]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w22 : Wide 12 4 s26 := viaSearch (by decide +kernel)
def r38 : Rule 28 6 := cutRule 6 p11 w22
def r39 : Rule 28 6 := cutRule 6 p8 w11
def s27 : List ℕ := [f13,f53,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b8 : Ban 28 7 s27 := viaRules (ws := [s24,s25]) (consBan b9 (consBan b10 (nilBan _ _)))
  (dictionary [(704967418,r4),(1798221548,r30),(1906425344,r2),(852195827,r30),(560872828,r2),(1654126958,r30),(1289350447,r11),(235120930,r30),(314841848,r11),(2048470662,r11),(1004730903,r5),(1493719476,r30),(2036921137,r11),(1623066304,r5),(385512096,r0),(1892621059,r0),(1478766226,r0),(986516026,r11),(87100962,r30),(1518998069,r30),(272678573,r11),(697196051,r2),(1790450181,r30),(905137103,r4),(1998391233,r11),(1789305974,r3),(735076457,r11),(892874673,r4),(1986128803,r30),(2082093937,r12),(1441698235,r5),(1448152357,r5),(1201647539,r12),(142014507,r11),(1967597561,r30),(134162824,r0),(499678005,r30),(1409460058,r11),(1087559465,r0),(1606689524,r5),(874360600,r5),(552460007,r5),(44792420,r0),(2100321827,r5),(1778421234,r5),(47372682,r30),(1876172953,r0),(1208319342,r30),(308279534,r0),(225866865,r11),(1367577573,r5),(781371805,r30),(709501480,r5),(1329451963,r11),(323679024,r11),(1967239756,r5),(913010239,r5),(608221915,r15),(559765337,r11),(1701476045,r11),(556796772,r16),(1698507480,r5),(1650050902,r11),(644277963,r5),(1686883231,r11),(632653714,r30),(1155897542,r5),(1210853552,r5),(44817097,r5),(392278792,r5),(1536710808,r5),(28786899,r38),(958772087,r5),(1513812007,r39),(1049445530,r5),(301406972,r0),(1016741770,r5),(225688330,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f57 : ℕ := 0x1b2c0
def f58 : ℕ := 0x3ddcc
def s28 : List ℕ := [f36,f57,f38,f58]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w23 : Wide 9 3 s28 := viaSearch (by decide +kernel)
def p19 : Weak 28 9 := signedPick 0 [0,1,6,7,12,13,15,16,25] (by decide) (by decide) (by decide)
def r40 : Rule 28 6 := cutRule 6 p19 w23
def f59 : ℕ := 0xa30
def s29 : List ℕ := [f59,f0,f1,f2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w24 : Wide 6 3 s29 := viaSearch (by decide +kernel)
def r41 : Rule 28 6 := cutRule 6 p4 w24
def r42 : Rule 28 6 := cutRule 6 p0 w1
def r43 : Rule 28 5 := cutRule 5 p0 w1
def f60 : ℕ := 0x4089907e38ff8
def s30 : List ℕ := [f60,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b12 : Ban 28 6 s30 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1213009886,r21),(342441807,r43),(582279133,r32),(434145848,r23)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s31 : List ℕ := [f13,f21,f22,f15,f54,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b11 : Ban 28 7 s31 := viaRules (ws := [s24,s30]) (consBan b9 (consBan b12 (nilBan _ _)))
  (dictionary [(597054013,r19),(1086042586,r5),(1215389414,r19),(578839136,r40),(1826907719,r11),(1111321179,r11),(2012485330,r41),(1674417047,r5),(1034021345,r19),(1040475467,r19),(1873969581,r42),(92001115,r0),(679882575,r42),(44792420,r0),(2100321827,r5),(1778421234,r5),(558637950,r5),(144783117,r19),(1392989929,r5),(1071089336,r5),(1787179439,r0),(1468496063,r42),(2048086291,r42),(1586330464,r5),(502249418,r5),(1187826658,r19),(283321648,r2),(968898888,r5),(1777911560,r5),(316005153,r19),(1606689524,r5),(1502511762,r3),(40605355,r5),(1079448534,r5),(1765025774,r19),(1894001491,r4),(432095084,r5),(1982381608,r5),(520475201,r19),(385512096,r0),(1965673622,r26),(959900683,r19),(373694915,r5),(301824590,r19),(921775073,r27),(2063485781,r5),(803176662,r19),(1784623854,r19),(1129033918,r19),(1768593656,r5),(551095197,r19),(1106135117,r5),(2041213729,r5),(609064880,r19),(1065843653,r5),(1751420893,r19),(1245587749,r5),(1931164989,r19),(1803454541,r5),(341548134,r19),(1836783104,r5),(374876697,r19)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f61 : ℕ := 0x2e9c
def f62 : ℕ := 0x3964
def s32 : List ℕ := [f44,f61,f62]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w25 : Wide 7 4 s32 := viaSearch (by decide +kernel)
def p20 : Weak 28 7 := signedPick 4 [4,5,7,15,17,18,20] (by decide) (by decide) (by decide)
def r44 : Rule 28 6 := cutRule 6 p20 w25
def f63 : ℕ := 0x4c04b045c00e00
def s33 : List ℕ := [f13,f21,f22,f63,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b13 : Ban 28 7 s33 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(828687378,r11),(414832545,r5),(1518576433,r19),(2007565006,r5),(403283020,r11),(2136911834,r19),(1500361556,r11),(600946492,r30),(2032843599,r30),(786524103,r11),(448455820,r5),(1955543765,r19),(1961997887,r19),(511095287,r5),(2118194947,r19),(605423891,r2),(65039904,r5),(396730344,r5),(2003830004,r19),(1931060038,r11),(1390676051,r5),(558637950,r5),(685167104,r5),(144783117,r19),(1405058021,r5),(864674034,r19),(1636749828,r4),(1096365841,r5),(1687259522,r5),(1146875535,r19),(1068716213,r3),(528332226,r5),(333959444,r30),(648008354,r0),(1013523535,r30),(1601404995,r0),(874360600,r5),(552460007,r5),(580883535,r44),(258982942,r0),(167028702,r5),(1992611756,r5),(561218212,r30),(1722164872,r30),(1092843994,r11),(739712395,r11),(1881423103,r19),(1295217335,r5),(1223347010,r19),(1843297493,r11),(837524554,r5),(1724699082,r19),(558662627,r19),(2050556338,r19),(542632429,r5),(1472617617,r19),(2027657537,r5),(149733250,r5),(1756832910,r19),(1097005794,r5),(556621807,r19),(1533925421,r5),(993541434,r19),(2092663039,r5),(1552279052,r19),(1563291060,r19),(815252502,r5),(1530587300,r19),(739533860,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f64 : ℕ := 0x2190990238038
def s34 : List ℕ := [f64,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b14 : Ban 28 7 s34 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1304173710,r0),(1690095942,r42),(276543215,r2),(662465447,r0),(2130155212,r29),(368593797,r0),(442237740,r0),(828159972,r42),(1092843994,r11),(1892621059,r0),(1478766226,r0),(1341138764,r12),(297399005,r5),(786387578,r11),(915734406,r5),(554385554,r0),(940307786,r42),(2138941496,r4),(377380081,r0),(388341638,r3),(774263870,r0),(1655678939,r4),(2041601171,r42),(279184128,r29),(1527252711,r11),(811666171,r11),(1712830322,r29),(1374762039,r12),(494315641,r12),(685167104,r5),(1392989929,r5),(1071089336,r5),(1582166256,r29),(1260265663,r0),(1574314573,r42),(1939829754,r0),(702128160,r29),(380227567,r42),(580883535,r44),(258982942,r0),(167028702,r5),(1992611756,r5),(1487524431,r0),(1168841055,r42),(1748431283,r42),(48152247,r5),(434074479,r5),(1491760415,r0),(1877682647,r42),(618393196,r5),(1004315428,r5),(2046498766,r0),(284937351,r42),(1666018614,r29),(660245675,r5),(74039907,r0),(2169582,r5),(622120065,r29),(1763830773,r0),(448565644,r5),(503521654,r5),(1484968846,r5),(1832430541,r5),(829378910,r5),(1468938648,r0),(251440189,r5),(806480109,r0),(1741558721,r42),(309409872,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f65 : ℕ := 0xad430
def f66 : ℕ := 0xfabc0
def s35 : List ℕ := [f3,f65,f66]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w26 : Wide 10 3 s35 := viaSearch (by decide +kernel)
def p21 : Weak 28 10 := signedPick 4 [4,5,7,8,15,17,18,20,22,24] (by decide) (by decide) (by decide)
def r45 : Rule 28 5 := cutRule 5 p21 w26
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w27 : Wide 10 2 s35 := viaSearch (by decide +kernel)
def r46 : Rule 28 5 := cutRule 5 p21 w27
def f67 : ℕ := 0xd43f8
def f68 : ℕ := 0xdec78
def f69 : ℕ := 0xf5380
def s36 : List ℕ := [f67,f68,f69]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w28 : Wide 10 3 s36 := viaSearch (by decide +kernel)
def p22 : Weak 28 10 := signedPick 0 [0,1,2,3,5,6,8,9,10,11] (by decide) (by decide) (by decide)
def r47 : Rule 28 5 := cutRule 5 p22 w28
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w29 : Wide 10 2 s36 := viaSearch (by decide +kernel)
def r48 : Rule 28 5 := cutRule 5 p22 w29
def f70 : ℕ := 0xac50f0
def s37 : List ℕ := [f8,f70,f29]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w30 : Wide 12 4 s37 := viaSearch (by decide +kernel)
def r49 : Rule 28 5 := cutRule 5 p6 w30
def f71 : ℕ := 0x4004204c007e07
def f72 : ℕ := 0x6ec7f6fffc7fff
def s38 : List ℕ := [f13,f21,f71,f72,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b16 : Ban 28 6 s38 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1020970437,r45),(2124714325,r46),(466219251,r46),(595566079,r45),(1758097537,r46),(810741780,r46),(577980349,r46),(679703222,r46),(762949956,r46),(1470811926,r46),(1645934542,r45),(281779854,r47),(400920689,r48),(340725816,r47),(2141528299,r45),(777373611,r48),(2065451191,r47),(1145202439,r48),(1789832249,r49),(425677561,r47),(744360937,r45),(1345850287,r45),(340077348,r48),(1901355227,r47),(1829484902,r48),(301951738,r45),(1443662446,r47),(128397317,r48),(183353327,r47),(1164800519,r48),(1512262214,r47),(1910641194,r48),(531553196,r45),(1542506313,r45),(1758470507,r47),(1839754530,r48)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f73 : ℕ := 0x7fb7f8
def s39 : List ℕ := [f24,f25,f26,f73,f27]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w31 : Wide 12 4 s39 := viaSearch (by decide +kernel)
def r50 : Rule 28 6 := cutRule 6 p11 w31
def f74 : ℕ := 0xebc
def s40 : List ℕ := [f0,f1,f2,f74]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w32 : Wide 6 3 s40 := viaSearch (by decide +kernel)
def r51 : Rule 28 6 := cutRule 6 p8 w32
def r52 : Rule 28 5 := cutRule 5 p14 w7
def f75 : ℕ := 0x7bb7204ffffe07
def s41 : List ℕ := [f13,f21,f22,f15,f75]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b17 : Ban 28 6 s41 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(377686200,r36),(1607539906,r36),(1654601768,r36),(1741014640,r36),(1588503438,r52)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s42 : List ℕ := [f13,f21,f71,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b15 : Ban 28 7 s42 := viaRules (ws := [s38,s41]) (consBan b16 (consBan b17 (nilBan _ _)))
  (dictionary [(2057228867,r11),(1013489108,r30),(1502477681,r30),(1631824509,r11),(1692343632,r5),(646872320,r30),(744987875,r2),(1847000210,r30),(512226444,r2),(1614238779,r30),(613949317,r11),(1715961652,r30),(697196051,r2),(1799208386,r30),(1977553339,r5),(932082027,r11),(1405058021,r5),(359586709,r30),(416979892,r29),(1518992227,r11),(1001269896,r11),(995274231,r11),(95859167,r4),(1527756274,r30),(287432443,r11),(281436778,r4),(2090852142,r1),(1450456440,r4),(1456910562,r1),(1210405744,r4),(1362509051,r0),(323033404,r0),(317037739,r0),(150772712,r11),(1976355766,r30),(142921029,r0),(508436210,r30),(1418218263,r11),(1096317670,r0),(47372682,r30),(1787179439,r0),(561218212,r30),(1487524431,r0),(115065212,r4),(1538978140,r4),(1217077547,r4),(1890926823,r0),(59348104,r4),(1884931158,r4),(234625070,r11),(1376335778,r4),(790130010,r30),(718259685,r4),(1338210168,r11),(332437229,r11),(1164655747,r4),(1219611757,r50),(53575302,r4),(401036997,r51),(1844887289,r5),(799415977,r4),(1607509999,r15),(1567811626,r11),(562038687,r11),(1476752408,r16),(470979469,r5),(431281096,r11),(1572991804,r4),(1692716602,r11),(647245290,r30),(1545469013,r4),(37545104,r4),(967530292,r4),(1522570212,r4),(1058203735,r4),(310165177,r0),(1025499975,r4),(234446535,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p23 : Weak 28 9 := signedPick 0 [0,2,9,10,12,14,18,19,26] (by decide) (by decide) (by decide)
def r53 : Rule 28 6 := cutRule 6 p23 w23
def r54 : Rule 28 6 := cutRule 6 p3 w24
def p24 : Weak 28 8 := signedPick 0 [0,2,3,5,9,10,12,14] (by decide) (by decide) (by decide)
def r55 : Rule 28 5 := cutRule 5 p24 w12
def f76 : ℕ := 0x440d207fc0ff8
def s43 : List ℕ := [f76,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b19 : Ban 28 6 s43 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1758136317,r22),(1805198179,r43),(1645934542,r45),(1896902220,r55)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r56 : Rule 28 6 := cutRule 6 p24 w12
def r57 : Rule 28 6 := cutRule 6 p18 w15
def s44 : List ℕ := [f13,f21,f22,f15,f72,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b18 : Ban 28 7 s44 := viaRules (ws := [s38,s43]) (consBan b16 (consBan b19 (nilBan _ _)))
  (dictionary [(1738545491,r53),(694805732,r11),(1183794305,r11),(1313141133,r54),(1924659438,r20),(1209072898,r4),(2110237049,r20),(1772168766,r4),(1131773064,r20),(891722368,r20),(1971721300,r42),(189752834,r0),(777634294,r42),(1876172953,r0),(1468496063,r42),(1168841055,r42),(1890926823,r0),(59348104,r4),(1884931158,r4),(904389836,r4),(898394171,r20),(320254956,r4),(2145838010,r4),(999354908,r4),(335166784,r5),(1118495743,r20),(274971911,r2),(1058300870,r4),(711619706,r4),(1494948665,r20),(1999697286,r29),(635542598,r4),(1079448534,r5),(1862777493,r20),(959091194,r5),(1742420153,r4),(1655678939,r4),(291524251,r20),(115065212,r4),(1362509051,r0),(2063425341,r56),(1057652402,r20),(471446634,r4),(399576309,r20),(1019526792,r57),(13753853,r4),(845972371,r20),(900928381,r4),(1882375573,r20),(82353621,r4),(1866345375,r20),(648846916,r20),(2138965448,r4),(706816599,r20),(823825176,r5),(1607154135,r20),(1774000625,r4),(409845937,r20),(1323816201,r5),(2107145160,r20),(1154060466,r4),(1937389425,r20)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f77 : ℕ := 0x2c9c
def f78 : ℕ := 0x3b64
def s45 : List ℕ := [f44,f77,f78]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w33 : Wide 7 4 s45 := viaSearch (by decide +kernel)
def p25 : Weak 28 7 := signedPick 4 [4,5,10,15,17,18,20] (by decide) (by decide) (by decide)
def r58 : Rule 28 6 := cutRule 6 p25 w33
def f79 : ℕ := 0x2c029423c001c0
def s46 : List ℕ := [f13,f21,f79,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b20 : Ban 28 7 s46 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1070691880,r11),(26952121,r30),(515940694,r30),(645287522,r11),(610961596,r4),(726436944,r20),(1519571184,r2),(1635046532,r4),(993741858,r4),(1109217206,r20),(1362021459,r11),(1477496807,r4),(892874673,r4),(1008350021,r20),(896053242,r5),(1011528590,r4),(1687259522,r5),(1802734870,r20),(1307533430,r29),(1423008778,r4),(14732909,r11),(8737244,r4),(1256805827,r20),(541219287,r4),(1448379103,r11),(1442383438,r20),(1104315155,r4),(463919453,r20),(223868757,r20),(782918823,r4),(904389836,r4),(898394171,r20),(989818779,r30),(1303867689,r0),(1669382870,r30),(109780683,r0),(1208319342,r30),(1722164872,r30),(1101602199,r11),(1538978140,r4),(1217077547,r4),(1805880657,r58),(1483980064,r0),(1799884992,r4),(1477984399,r4),(1395571730,r11),(389798791,r20),(1951076670,r4),(1879206345,r20),(351673181,r11),(1493383889,r4),(178118760,r20),(233074770,r4),(1214521962,r20),(1561983657,r4),(1148797867,r5),(1264273215,r20),(76366053,r4),(191841401,r20),(1492376028,r5),(1607851376,r20),(1652447098,r4),(1767922446,r20),(1198491764,r20),(2128476952,r20),(71666748,r20),(1471111837,r4),(38962988,r20),(1395393195,r4)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f80 : ℕ := 0x2c142903c0038
def s47 : List ℕ := [f80,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b21 : Ban 28 7 s47 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(902095308,r0),(117530848,r42),(110506619,r2),(1473425806,r0),(555950898,r3),(1918870085,r0),(717548347,r0),(2080467534,r42),(554385554,r0),(1917304741,r42),(1547241504,r5),(762677044,r0),(1899481655,r29),(1114917195,r0),(1982381608,r5),(1197817148,r42),(170652072,r3),(1274395960,r11),(1763384533,r11),(1892731361,r3),(1101602199,r11),(323033404,r0),(317037739,r0),(1256181083,r1),(356766019,r4),(1788663126,r11),(542343630,r4),(204275347,r1),(1717817414,r1),(782918823,r4),(320254956,r4),(2145838010,r4),(411679564,r3),(89778971,r0),(403827881,r42),(769343062,r0),(1679125115,r3),(1357224522,r42),(308279534,r0),(2048086291,r42),(1748431283,r42),(1805880657,r58),(1483980064,r0),(1799884992,r4),(1477984399,r4),(1634962436,r5),(850397976,r4),(1868757589,r0),(1084193129,r42),(894092520,r5),(109528060,r4),(480965517,r0),(1843884704,r42),(495531922,r3),(1637242630,r4),(1051036862,r0),(979166537,r4),(1599117020,r3),(593344081,r0),(1425562599,r4),(1480518609,r0),(314482154,r4),(661943849,r0),(1806375865,r4),(298451956,r4),(1228437144,r4),(1783477064,r4),(571072029,r42),(1286406827,r4)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f81 : ℕ := 0xac3f0
def f82 : ℕ := 0xb54c0
def s48 : List ℕ := [f81,f82,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w34 : Wide 10 4 s48 := viaSearch (by decide +kernel)
def p26 : Weak 28 10 := signedPick 0 [0,1,10,11,12,13,18,20,22,24] (by decide) (by decide) (by decide)
def r59 : Rule 28 6 := cutRule 6 p26 w34
def f83 : ℕ := 0x50f8
def f84 : ℕ := 0x5918
def f85 : ℕ := 0x7260
def f86 : ℕ := 0xfcf8
def s49 : List ℕ := [f83,f84,f85,f86]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w35 : Wide 8 3 s49 := viaSearch (by decide +kernel)
def p27 : Weak 28 8 := signedPick 12 [12,13,14,19,20,23,24,26] (by decide) (by decide) (by decide)
def r60 : Rule 28 6 := cutRule 6 p27 w35
def f87 : ℕ := 0x809022381f8
def s50 : List ℕ := [f87,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b22 : Ban 28 7 s50 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(529812174,r5),(1885808595,r5),(1485438842,r5),(400465346,r2),(1769946847,r2),(1356092014,r2),(1681328027,r59),(1267473194,r5),(1280958274,r2),(867103441,r5),(270128608,r0),(1225755276,r3),(2020049943,r4),(828192964,r29),(548608436,r3),(1504235104,r3),(247109645,r4),(1202736313,r12),(848888564,r3),(2096957147,r2),(1381370607,r2),(135051111,r3),(210837661,r3),(1944466475,r3),(1724379728,r3),(1310524895,r5),(1064020077,r12),(704967418,r4),(1660594086,r11),(1610369818,r0),(418512839,r29),(1533829692,r11),(341972713,r11),(1304173710,r0),(112316731,r12),(1829970099,r11),(2144019009,r2),(362050543,r2),(949932003,r11),(314841848,r11),(2048470662,r11),(828687378,r11),(414832545,r5),(1341138764,r12),(2057228867,r11),(1738545491,r53),(1070691880,r11),(170652072,r3),(1827431428,r5),(635574449,r5),(38037172,r15),(993663840,r29),(1323257290,r5),(131400311,r5),(607534840,r29),(1563161508,r12),(88239403,r29),(1229950111,r5),(643744343,r2),(571874018,r5),(1191824501,r29),(186051562,r2),(1018270080,r5),(1073226090,r5),(2054673282,r5),(254651330,r5),(1399083346,r5),(2038643084,r60),(821144625,r5),(1376184545,r3),(911818068,r5),(163779510,r60),(879114308,r5),(88060868,r11)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r61 : Rule 28 7 := cutRule 7 p6 w9
def f88 : ℕ := 0x1973
def f89 : ℕ := 0x2c7c
def f90 : ℕ := 0x3570
def s51 : List ℕ := [f88,f89,f90]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w36 : Wide 7 4 s51 := viaSearch (by decide +kernel)
def p28 : Weak 28 7 := relaxed (pick [4,5,7,8,9,10,11] (by decide) (by decide) (by decide))
def r62 : Rule 28 6 := cutRule 6 p28 w36
def f91 : ℕ := 0x1560d205dc0e00
def s52 : List ℕ := [f91,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b23 : Ban 28 7 s52 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(955216532,r29),(1885808595,r5),(1485438842,r5),(2058960420,r5),(855553916,r5),(441699083,r19),(1744912242,r62),(1331057409,r5),(1344542489,r2),(930687656,r5),(581990710,r5),(1112213020,r19),(748867569,r4),(1279089879,r5),(134732510,r3),(664954820,r5),(1293318888,r5),(1823541198,r19),(423484206,r3),(1671552789,r2),(955966249,r2),(1857130400,r3),(1932916950,r3),(1519062117,r5),(878666415,r19),(1298975370,r3),(885120537,r19),(638615719,r5),(511095287,r5),(1041317597,r19),(1497723344,r0),(2027945654,r5),(1770257096,r11),(152995759,r5),(1777911560,r5),(160650223,r19),(1404565741,r11),(1718614651,r2),(2084129832,r2),(524527645,r11),(2036921137,r11),(1623066304,r5),(1215389414,r19),(403283020,r11),(2136911834,r19),(915734406,r5),(1631824509,r11),(1313141133,r54),(645287522,r11),(1892731361,r3),(2003115662,r5),(385854325,r19),(1065914893,r5),(1596137203,r19),(846916394,r5),(1377138704,r19),(355190549,r5),(885412859,r19),(1810318692,r29),(804545753,r19),(218339985,r5),(146469660,r19),(766420143,r29),(1908130851,r5),(592865722,r19),(647821732,r19),(1629268924,r19),(1976730619,r19),(973678988,r19),(1613238726,r5),(395740267,r19),(950780187,r5),(486413710,r19),(1885858799,r5),(453709950,r19),(1810140157,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p29 : Weak 28 10 := signedPick 0 [0,2,7,8,12,14,15,17,22,24] (by decide) (by decide) (by decide)
def r63 : Rule 28 6 := cutRule 6 p29 w34
def f92 : ℕ := 0x7460
def f93 : ℕ := 0xfaf8
def s53 : List ℕ := [f83,f84,f92,f93]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w37 : Wide 8 3 s53 := viaSearch (by decide +kernel)
def p30 : Weak 28 8 := signedPick 12 [12,13,14,16,17,23,24,25] (by decide) (by decide) (by decide)
def r64 : Rule 28 6 := cutRule 6 p30 w37
def f94 : ℕ := 0x4042043c0e38
def s54 : List ℕ := [f94,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b24 : Ban 28 7 s54 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1326908090,r4),(1620949875,r4),(1220580122,r4),(270128608,r0),(163800640,r1),(1557192999,r5),(1450865031,r3),(1215096443,r29),(1108768475,r3),(581990710,r5),(475662742,r1),(848888564,r3),(1952632452,r2),(294137378,r2),(423484206,r3),(425743939,r2),(325411636,r2),(319415971,r2),(1441367929,r63),(1435372264,r4),(1040998176,r2),(1035002511,r4),(888507504,r3),(882511839,r1),(248570259,r1),(8061106,r29),(2065441,r4),(1692343632,r5),(1586015664,r11),(235896353,r0),(129568385,r3),(668693522,r11),(562365554,r11),(902095308,r0),(795767340,r1),(768015463,r11),(1082064373,r2),(1447579554,r2),(2035461014,r11),(986516026,r11),(578839136,r40),(1500361556,r11),(279184128,r29),(1001269896,r11),(995274231,r11),(14732909,r11),(8737244,r4),(1256181083,r1),(1777965712,r5),(1671637744,r4),(643789894,r15),(537461926,r3),(1554861420,r5),(1448533452,r4),(2068029187,r3),(1961701219,r1),(1173768414,r3),(167995475,r4),(1729273354,r2),(1657403029,r4),(129869865,r3),(1271580573,r2),(2103799091,r4),(11271454,r64),(992718646,r4),(1340180341,r29),(337128710,r4),(976688448,r4),(1906673636,r4),(314229909,r4),(1997347079,r4),(1249308521,r64),(1964643319,r4),(1173589879,r11)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f95 : ℕ := 0x69f
def f96 : ℕ := 0x2a7c
def s55 : List ℕ := [f95,f96,f77]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w38 : Wide 7 4 s55 := viaSearch (by decide +kernel)
def p31 : Weak 28 7 := relaxed (pick [4,5,6,7,8,10,11] (by decide) (by decide) (by decide))
def r65 : Rule 28 6 := cutRule 6 p31 w38
def f97 : ℕ := 0x15289903c381c0
def s56 : List ℕ := [f97,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b25 : Ban 28 7 s56 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2040745543,r3),(1620949875,r4),(1220580122,r4),(247109645,r4),(1574427871,r20),(1978000563,r5),(1157835142,r4),(610993537,r3),(1938311763,r4),(1293318888,r5),(473153467,r20),(135051111,r3),(1238794999,r2),(1727783572,r2),(1857130400,r3),(1141330479,r4),(327160723,r4),(321165058,r20),(11943936,r65),(5948271,r4),(1759057830,r2),(1753062165,r4),(174670051,r3),(168674386,r4),(1675762331,r20),(1682216453,r4),(1441707300,r29),(1435711635,r20),(610961596,r4),(1938279822,r20),(1413683624,r0),(593518203,r4),(855866698,r11),(35701277,r4),(711619706,r4),(2038937932,r20),(54178010,r11),(368226920,r2),(733742101,r2),(1321623561,r11),(272678573,r11),(2012485330,r41),(786524103,r11),(1712830322,r29),(287432443,r11),(281436778,r4),(2110237049,r20),(1448379103,r11),(1442383438,r20),(542343630,r4),(1749681637,r5),(929516216,r20),(1637279209,r4),(817113788,r20),(314317973,r5),(1641636199,r20),(536085894,r4),(1863404120,r20),(459930961,r3),(1601641669,r20),(1015435901,r4),(943565576,r20),(1563516059,r3),(557743120,r4),(1389961638,r20),(1444917648,r4),(278881193,r20),(626342888,r4),(1770774904,r20),(262850995,r20),(1192836183,r20),(1747876103,r20),(1283509626,r20),(535471068,r4),(1250805866,r20),(459752426,r4)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p32 : Weak 28 10 := signedPick 1 [1,2,4,5,13,14,15,17,18,20] (by decide) (by decide) (by decide)
def r66 : Rule 28 6 := cutRule 6 p32 w34
def f98 : ℕ := 0x5a18
def f99 : ℕ := 0xf9f8
def s57 : List ℕ := [f83,f98,f92,f99]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w39 : Wide 8 3 s57 := viaSearch (by decide +kernel)
def p33 : Weak 28 8 := signedPick 12 [12,13,14,16,17,19,20,21] (by decide) (by decide) (by decide)
def r67 : Rule 28 6 := cutRule 6 p33 w39
def f100 : ℕ := 0x4009007c00fc0
def s58 : List ℕ := [f100,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b26 : Ban 28 7 s58 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2141788982,r0),(1269428655,r0),(869058902,r0),(704967418,r4),(1579720985,r30),(1225058071,r5),(2099811638,r11),(1417154146,r29),(144424066,r11),(511095287,r5),(1385848854,r30),(1829970099,r11),(786230340,r2),(1275218913,r2),(1404565741,r11),(1692343632,r5),(419613552,r30),(2056269893,r4),(783539813,r11),(367501731,r3),(1242255298,r11),(610961596,r4),(1485715163,r30),(768015463,r11),(2016084046,r2),(1300497506,r2),(54178010,r11),(1863593374,r3),(1223197672,r24),(1229651794,r3),(983146976,r29),(1553907522,r2),(603078035,r2),(281177442,r2),(637932607,r66),(316032014,r0),(237562854,r2),(2063145908,r0),(142014507,r11),(1967597561,r30),(333959444,r30),(1582166256,r29),(1260265663,r0),(150772712,r11),(1976355766,r30),(989818779,r30),(411679564,r3),(89778971,r0),(2020728552,r5),(747998472,r0),(475711905,r15),(1350465472,r11),(565769377,r5),(1440522944,r0),(716128875,r11),(1590882442,r30),(7366302,r11),(1149077010,r0),(562871242,r2),(491000917,r0),(1110951400,r11),(105178461,r2),(937396979,r0),(992352989,r67),(1973800181,r0),(173778229,r29),(1318210245,r0),(1957769983,r67),(740271524,r0),(1295311444,r3),(830944967,r0),(82906409,r0),(798241207,r0),(7187767,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f101 : ℕ := 0x59f
def f102 : ℕ := 0x12e7
def f103 : ℕ := 0x1707
def s59 : List ℕ := [f101,f102,f103]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w40 : Wide 7 4 s59 := viaSearch (by decide +kernel)
def p34 : Weak 28 7 := relaxed (pick [3,4,5,7,8,10,11] (by decide) (by decide) (by decide))
def r68 : Rule 28 6 := cutRule 6 p34 w40
def f104 : ℕ := 0x11684b003f8038
def s60 : List ℕ := [f104,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b27 : Ban 28 7 s60 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(874343431,r11),(1269428655,r0),(869058902,r0),(1304173710,r0),(1298889181,r42),(1470916511,r5),(1465631982,r0),(2060202933,r11),(2054918404,r0),(1777911560,r5),(1772627031,r42),(949932003,r11),(2053675891,r2),(395180817,r2),(524527645,r11),(902095308,r0),(896810779,r42),(947532289,r4),(942247760,r0),(407984904,r11),(402700375,r0),(711619706,r4),(706335177,r42),(2035461014,r11),(1136045950,r2),(420459410,r2),(1321623561,r11),(983555278,r3),(343159576,r25),(349613698,r3),(103108880,r29),(1188392341,r0),(1505008405,r0),(1183107812,r42),(123409692,r68),(1948992746,r0),(1870523586,r2),(1548622993,r0),(1409460058,r11),(1087559465,r0),(679882575,r42),(1601404995,r0),(702128160,r29),(380227567,r42),(1418218263,r11),(1096317670,r0),(777634294,r42),(109780683,r0),(1679125115,r3),(1357224522,r42),(1557262450,r5),(1551977921,r42),(2140961723,r0),(2135677194,r42),(1349730303,r5),(1344445774,r42),(608070654,r0),(602786125,r42),(1274811853,r11),(269038914,r42),(1830316793,r0),(1758446468,r42),(230913304,r11),(1372624012,r0),(57358883,r42),(112314893,r0),(1093762085,r42),(1441223780,r0),(438172149,r42),(1077731887,r0),(2007717075,r42),(415273348,r0),(2098390518,r42),(1350351960,r42),(2065686758,r42),(1274633318,r42)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f105 : ℕ := 0x1b71ff
def f106 : ℕ := 0xc5be3f
def f107 : ℕ := 0x168dfc7
def f108 : ℕ := 0x1b60ff8
def s61 : List ℕ := [f105,f106,f107,f108]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w41 : Wide 13 5 s61 := viaSearch (by decide +kernel)
def p35 : Weak 28 13 := relaxed (pick [0,1,2,3,4,5,6,7,8,9,10,11,27] (by decide) (by decide) (by decide))
def r69 : Rule 28 7 := cutRule 7 p35 w41
def f109 : ℕ := 0x2503fe0
def f110 : ℕ := 0x2f943e0
def f111 : ℕ := 0x75a9c60
def f112 : ℕ := 0xb742d80
def s62 : List ℕ := [f109,f110,f111,f112]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w42 : Wide 14 4 s62 := viaSearch (by decide +kernel)
def p36 : Weak 28 14 := signedPick 0 [0,1,12,13,14,16,17,19,20,21,23,24,25,26] (by decide) (by decide) (by decide)
def r70 : Rule 28 6 := cutRule 6 p36 w42
def f113 : ℕ := 0xd1fc
def f114 : ℕ := 0xf430
def f115 : ℕ := 0x1dacc
def s63 : List ℕ := [f113,f114,f115]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w43 : Wide 9 4 s63 := viaSearch (by decide +kernel)
def p37 : Weak 28 9 := signedPick 0 [0,2,3,5,9,10,18,19,26] (by decide) (by decide) (by decide)
def r71 : Rule 28 6 := cutRule 6 p37 w43
def f116 : ℕ := 0x2503fe2
def f117 : ℕ := 0x2f9c3e2
def f118 : ℕ := 0x75a1c60
def s64 : List ℕ := [f116,f117,f118,f112]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w44 : Wide 14 4 s64 := viaSearch (by decide +kernel)
def p38 : Weak 28 14 := signedPick 0 [0,3,12,13,14,16,17,19,20,21,23,24,25,26] (by decide) (by decide) (by decide)
def r72 : Rule 28 6 := cutRule 6 p38 w44
def f119 : ℕ := 0x28bc
def f120 : ℕ := 0x3a30
def f121 : ℕ := 0xed8c
def s65 : List ℕ := [f119,f120,f121]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w45 : Wide 8 3 s65 := viaSearch (by decide +kernel)
def p39 : Weak 28 8 := signedPick 0 [0,1,3,4,6,7,12,21] (by decide) (by decide) (by decide)
def r73 : Rule 28 6 := cutRule 6 p39 w45
def f122 : ℕ := 0x2f903e0
def f123 : ℕ := 0x75adc62
def s66 : List ℕ := [f116,f122,f123,f112]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w46 : Wide 14 4 s66 := viaSearch (by decide +kernel)
def p40 : Weak 28 14 := signedPick 1 [1,6,12,13,14,16,17,19,20,21,23,24,25,26] (by decide) (by decide) (by decide)
def r74 : Rule 28 6 := cutRule 6 p40 w46
def f124 : ℕ := 0x2d0c
def f125 : ℕ := 0xfab0
def s67 : List ℕ := [f119,f124,f125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w47 : Wide 8 3 s67 := viaSearch (by decide +kernel)
def p41 : Weak 28 8 := signedPick 0 [0,1,3,4,6,7,13,25] (by decide) (by decide) (by decide)
def r75 : Rule 28 6 := cutRule 6 p41 w47
def f126 : ℕ := 0x11280907ff81f8
def s68 : List ℕ := [f126,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b29 : Ban 28 6 s68 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1817768418,r21)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f127 : ℕ := 0x7bbf0dbffff1ff
def s69 : List ℕ := [f13,f21,f22,f15,f16,f127]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b28 : Ban 28 7 s69 := viaRules (ws := [s68]) (consBan b29 (nilBan _ _))
  (dictionary [(1073226090,r5),(29486331,r19),(518474904,r5),(647821732,r19),(11271454,r64),(1259340037,r4),(543753497,r2),(1444917648,r4),(1106849365,r5),(466453663,r19),(472907785,r19),(226402967,r5),(992352989,r67),(1306401899,r0),(1671917080,r2),(112314893,r0),(1210853552,r5),(803176662,r19),(1724699082,r19),(503521654,r5),(1219611757,r50),(900928381,r4),(233074770,r4),(1480518609,r0),(1398105940,r26),(392333001,r19),(1953610880,r5),(1881740555,r19),(354207391,r70),(1495918099,r5),(1600280742,r71),(594507803,r5),(1186425909,r5),(180652970,r19),(1630911005,r5),(1217056172,r19),(422807159,r5),(1564517867,r19),(59315266,r72),(1201025974,r5),(989300454,r73),(2131011162,r19),(538567435,r5),(331935339,r74),(1473646047,r5),(1047270137,r75),(41497198,r19),(1397927405,r5),(1623521314,r5),(1844417168,r5),(1962426726,r19),(1163324044,r2),(1281333602,r5),(355190549,r5),(473200107,r19),(1099046614,r5),(117172559,r3),(235182117,r5),(1584026784,r5),(1702036342,r19),(622764894,r4),(740774452,r5),(59638553,r5),(177648111,r19),(25831541,r11),(143841099,r5),(1245587749,r5),(1363597307,r19),(1395096130,r0),(1513105688,r5),(2092663039,r5),(63188950,r19),(1446508309,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f128 : ℕ := 0xfaf0
def s70 : List ℕ := [f119,f121,f128]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w48 : Wide 8 4 s70 := viaSearch (by decide +kernel)
def p42 : Weak 28 8 := signedPick 0 [0,2,3,5,9,10,12,21] (by decide) (by decide) (by decide)
def r76 : Rule 28 6 := cutRule 6 p42 w48
def f129 : ℕ := 0x80db80001ff
def s71 : List ℕ := [f129,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b30 : Ban 28 7 s71 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(607534840,r29),(2054453285,r5),(634781821,r5),(2081700266,r19),(1109930470,r5),(409365268,r19),(1350237086,r2),(649671884,r5),(62643412,r5),(1923416690,r5),(1509561857,r19),(254651330,r5),(1358395218,r19),(1847383791,r5),(1976730619,r19),(477762618,r3),(1924681063,r5),(299768192,r5),(1746686637,r19),(439892917,r5),(1886811362,r19),(1236995497,r4),(536430295,r5),(1340180341,r29),(440765277,r4),(1872662384,r2),(626342888,r4),(288274605,r5),(1555311854,r5),(1686883231,r11),(986318029,r5),(959473618,r5),(258908416,r19),(1086407491,r5),(385842289,r19),(2046498766,r0),(1345933564,r5),(173778229,r29),(487827139,r0),(853342320,r2),(1441223780,r0),(392278792,r5),(1832430541,r5),(401036997,r51),(82353621,r4),(1561983657,r4),(661943849,r0),(117599422,r5),(422807159,r5),(1564517867,r19),(579531180,r5),(1721241888,r19),(1135036120,r5),(1063165795,r19),(1683116278,r29),(677343339,r5),(1818109184,r76),(812336245,r5),(1404254351,r5),(398481412,r19),(1890375123,r19),(382451214,r5),(1867476322,r5),(1403109845,r19),(655071287,r5),(579352645,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f130 : ℕ := 0xb74ad80
def s72 : List ℕ := [f109,f110,f118,f130]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w49 : Wide 14 4 s72 := viaSearch (by decide +kernel)
def p43 : Weak 28 14 := signedPick 0 [0,2,12,13,14,16,17,19,20,21,23,24,25,26] (by decide) (by decide) (by decide)
def r77 : Rule 28 6 := cutRule 6 p43 w49
def r78 : Rule 28 6 := cutRule 6 p42 w45
def p44 : Weak 28 9 := signedPick 0 [0,1,3,4,6,7,15,16,25] (by decide) (by decide) (by decide)
def r79 : Rule 28 6 := cutRule 6 p44 w43
def f131 : ℕ := 0xb74ed82
def s73 : List ℕ := [f116,f122,f118,f131]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w50 : Wide 14 4 s73 := viaSearch (by decide +kernel)
def p45 : Weak 28 14 := signedPick 2 [2,9,12,13,14,16,17,19,20,21,23,24,25,26] (by decide) (by decide) (by decide)
def r80 : Rule 28 6 := cutRule 6 p45 w50
def p46 : Weak 28 8 := signedPick 0 [0,2,3,5,9,10,14,26] (by decide) (by decide) (by decide)
def r81 : Rule 28 6 := cutRule 6 p46 w47
def f132 : ℕ := 0x11604207ff8e38
def s74 : List ℕ := [f132,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b32 : Ban 28 6 s74 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1580133872,r22)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f133 : ℕ := 0x7bf762dffffe3f
def s75 : List ℕ := [f13,f21,f22,f15,f16,f133]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b31 : Ban 28 7 s75 := viaRules (ws := [s74]) (consBan b32 (nilBan _ _))
  (dictionary [(2038643084,r60),(994903325,r5),(1483891898,r2),(1613238726,r5),(976688448,r4),(77273384,r20),(1509170491,r4),(262850995,r20),(2072266359,r4),(1431870657,r5),(1438324779,r5),(1191819961,r20),(1957769983,r67),(124335246,r0),(489850427,r2),(1077731887,r0),(28786899,r38),(1768593656,r5),(542632429,r5),(1468938648,r0),(37545104,r4),(1866345375,r20),(1198491764,r20),(298451956,r4),(216039287,r56),(1357749995,r5),(771544227,r4),(699673902,r5),(1319624385,r77),(313851446,r4),(59315266,r72),(1201025974,r5),(1040762458,r78),(34989519,r5),(382451214,r5),(391168187,r79),(1532878895,r5),(385172522,r4),(1526883230,r5),(954940174,r5),(948944509,r5),(362273721,r4),(1503984429,r20),(1297352333,r80),(291579394,r4),(2012687131,r81),(1006914192,r5),(215860752,r4),(1121450056,r4),(1979448732,r4),(915391637,r20),(1050493364,r2),(2133919916,r4),(536085894,r4),(1619512446,r20),(1538902533,r29),(474845438,r4),(1584026784,r5),(519969689,r5),(1798069113,r5),(734012018,r5),(1236995497,r4),(172938402,r20),(2013001604,r5),(1956836442,r11),(892779347,r4),(1774000625,r4),(709943530,r20),(2079265889,r0),(1015208794,r4),(1652447098,r4),(588390003,r20),(420557877,r4)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r82 : Rule 28 6 := cutRule 6 p39 w48
def f134 : ℕ := 0x4062d8000e3f
def s76 : List ℕ := [f134,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b33 : Ban 28 7 s76 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(2068029187,r3),(341513553,r4),(151234110,r4),(572202123,r20),(1085942611,r4),(1506910624,r20),(345037496,r2),(766005509,r4),(477762618,r3),(898730631,r4),(458148359,r5),(879116372,r5),(1871242758,r4),(144727124,r20),(59638553,r5),(480606566,r5),(1376184545,r3),(332444786,r5),(821433359,r2),(950780187,r5),(443456678,r5),(870420356,r5),(864424691,r5),(314229909,r4),(1562298492,r20),(846711952,r4),(1747876103,r20),(1409807820,r4),(775866240,r5),(1692716602,r11),(2113684615,r4),(1504208901,r4),(1925176914,r20),(1870015232,r4),(143499598,r20),(480965517,r0),(901933530,r4),(1295311444,r3),(1609360354,r0),(1974875535,r2),(415273348,r0),(1513812007,r39),(1106135117,r5),(2027657537,r5),(806480109,r0),(1522570212,r4),(1783477064,r4),(1083016416,r4),(362273721,r4),(1503984429,r20),(1701064395,r4),(695291456,r5),(109085688,r4),(37215363,r5),(657165846,r3),(1798876554,r4),(483611425,r5),(538567435,r5),(1867476322,r5),(1298254574,r82),(292481635,r5),(1292258909,r4),(286485970,r5),(377159413,r5),(1776604502,r4),(1700885860,r4)])
  (by decide) (by decide +kernel) (by decide +kernel)
def p47 : Weak 28 8 := signedPick 1 [1,2,6,8,9,11,13,14] (by decide) (by decide) (by decide)
def r83 : Rule 28 6 := cutRule 6 p47 w12
def f135 : ℕ := 0x75a5c60
def s77 : List ℕ := [f109,f122,f135,f130]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w51 : Wide 14 4 s77 := viaSearch (by decide +kernel)
def p48 : Weak 28 14 := signedPick 1 [1,2,12,13,14,16,17,19,20,21,23,24,25,26] (by decide) (by decide) (by decide)
def r84 : Rule 28 6 := cutRule 6 p48 w51
def p49 : Weak 28 8 := signedPick 1 [1,2,6,8,9,11,13,25] (by decide) (by decide) (by decide)
def r85 : Rule 28 6 := cutRule 6 p49 w45
def p50 : Weak 28 8 := signedPick 1 [1,2,6,8,9,11,14,26] (by decide) (by decide) (by decide)
def r86 : Rule 28 6 := cutRule 6 p50 w47
def f136 : ℕ := 0xda0c
def f137 : ℕ := 0x1f4f0
def s78 : List ℕ := [f113,f136,f137]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w52 : Wide 9 4 s78 := viaSearch (by decide +kernel)
def p51 : Weak 28 9 := signedPick 0 [0,1,3,4,6,7,15,16,21] (by decide) (by decide) (by decide)
def r87 : Rule 28 6 := cutRule 6 p51 w52
def f138 : ℕ := 0x15209007ff8fc0
def s79 : List ℕ := [f138,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b35 : Ban 28 6 s79 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1811162506,r43)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f139 : ℕ := 0x7fb7b46fffffc7
def s80 : List ℕ := [f13,f21,f22,f15,f16,f139]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b34 : Ban 28 7 s80 := viaRules (ws := [s79]) (consBan b35 (nilBan _ _))
  (dictionary [(163779510,r60),(1267523398,r5),(1756511971,r2),(1885858799,r5),(1249308521,r64),(349893457,r4),(1781790564,r2),(535471068,r4),(197402785,r17),(1704490730,r5),(1710944852,r5),(1464440034,r4),(82906409,r0),(396955319,r42),(762470500,r0),(1350351960,r42),(301406972,r0),(2041213729,r5),(815252502,r5),(1741558721,r42),(310165177,r0),(2138965448,r4),(1471111837,r4),(571072029,r42),(488659360,r83),(1630370068,r5),(1044164300,r0),(972293975,r5),(1592244458,r84),(586471519,r0),(331935339,r74),(1473646047,r5),(1313382531,r85),(307609592,r5),(655071287,r5),(1297352333,r80),(291579394,r4),(79853874,r86),(1221564582,r5),(1776604502,r4),(492427910,r87),(1634138618,r5),(170527317,r0),(1312238025,r5),(1601434858,r5),(1279534265,r5),(1494253764,r0),(488480825,r42),(1578036901,r0),(737922713,r0),(2093969338,r42),(1531997206,r2),(740560184,r0),(608070654,r0),(1964117279,r42),(321803699,r29),(1677850324,r0),(1245587749,r5),(454150727,r5),(1803996635,r5),(1012559613,r5),(2046498766,r0),(1255061744,r42),(1948809498,r3),(1157372476,r0),(1774000625,r4),(982563603,r4),(311042724,r4),(1667089349,r4),(480965517,r0),(1837012142,r42),(2070971287,r5),(1279917847,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f140 : ℕ := 0xedcc
def s81 : List ℕ := [f119,f140,f125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w53 : Wide 8 4 s81 := viaSearch (by decide +kernel)
def r88 : Rule 28 6 := cutRule 6 p41 w53
def f141 : ℕ := 0x400b468000fc7
def s82 : List ℕ := [f141,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b36 : Ban 28 7 s82 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(716128875,r11),(1996456858,r0),(1446901424,r0),(579745760,r42),(738916925,r0),(2019244908,r42),(1821730111,r2),(954574447,r0),(1686883231,r11),(819727567,r0),(1768765602,r5),(901609938,r5),(2107290475,r0),(1240134811,r42),(2092663039,r5),(1225507375,r5),(88060868,r11),(1191804756,r5),(1680793329,r2),(1810140157,r5),(1692716602,r11),(825560938,r0),(733420762,r4),(2013748745,r4),(46663139,r0),(1326991122,r42),(1652447098,r4),(785291434,r4),(1173589879,r11),(274174815,r4),(1706071922,r2),(459752426,r4),(121684143,r18),(1628772088,r5),(1635226210,r5),(1388721392,r4),(2103675047,r5),(1558419976,r5),(1236519383,r5),(7187767,r0),(321236677,r42),(686751858,r0),(1274633318,r42),(225688330,r0),(739533860,r5),(234446535,r0),(1395393195,r4),(1355636489,r0),(1494253764,r0),(488480825,r42),(412940718,r0),(1554651426,r5),(968445658,r0),(896575333,r5),(1516525816,r11),(510752877,r0),(1342971395,r5),(1397927405,r5),(579352645,r5),(1723784661,r5),(215860752,r4),(1700885860,r4),(384005508,r88),(1525716216,r5),(62104915,r0),(1203815623,r5)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f142 : ℕ := 0xdb00ff8
def f143 : ℕ := 0x30dbf1ff
def f144 : ℕ := 0x562dfe3f
def f145 : ℕ := 0x6b46ffc7
def s83 : List ℕ := [f142,f143,f144,f145]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w54 : Wide 16 5 s83 := viaSearch (by decide +kernel)
def p52 : Weak 28 16 := relaxed (pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,27] (by decide) (by decide) (by decide))
def r89 : Rule 28 6 := cutRule 6 p52 w54
def f146 : ℕ := 0x11200007ff8000
def s84 : List ℕ := [f146,f13,f21,f22,f15]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b37 : Ban 28 7 s84 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(236197833,r16),(911301165,r89),(510931412,r2),(960454299,r2),(2045644691,r26),(1110814727,r29),(1136138533,r2),(88239403,r29),(1191983291,r2),(1680971864,r2),(1810318692,r29),(910988583,r2),(838456067,r56),(781916253,r3),(882704508,r2),(1173768414,r3),(274353350,r2),(1706250457,r2),(459930961,r3),(121862678,r3),(1628950623,r26),(1635404745,r3),(1388899927,r29),(1153751423,r2),(574506253,r83),(784154313,r11),(690285321,r2),(7366302,r11),(321415212,r2),(686930393,r2),(1274811853,r11),(225866865,r11),(1965673622,r26),(739712395,r11),(1666018614,r29),(234625070,r11),(2063425341,r56),(1395571730,r11),(495531922,r3)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f147 : ℕ := 0x12807fc0
def f148 : ℕ := 0x245ba4ff
def f149 : ℕ := 0x452dc73f
def f150 : ℕ := 0x6836f83f
def s85 : List ℕ := [f147,f148,f149,f150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w55 : Wide 16 4 s85 := viaSearch (by decide +kernel)
def p53 : Weak 28 16 := relaxed (pick [0,1,2,12,13,14,16,17,19,20,21,23,24,25,26,27] (by decide) (by decide) (by decide))
def r90 : Rule 28 6 := cutRule 6 p53 w55
def f151 : ℕ := 0x448db00000ff8
def s86 : List ℕ := [f151,f13,f21,f22,f15]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b38 : Ban 28 7 s86 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1280096382,r16),(911301165,r89),(510931412,r2),(844142809,r29),(438329776,r2),(1347884824,r2),(591798518,r90),(1191824501,r29),(148084742,r2),(637073315,r2),(766420143,r29),(157153509,r3),(1564000605,r2),(453553829,r2),(772693863,r90),(129869865,r3),(1377938448,r2),(662351908,r2),(1563516059,r3),(1225447776,r3),(585052074,r27),(591506196,r3),(345001378,r29),(952736844,r11),(1403586202,r2),(93039420,r2),(844678623,r90),(1110951400,r11),(1425000310,r2),(1790515491,r2),(230913304,r11),(1329451963,r11),(921775073,r27),(1843297493,r11),(622120065,r29),(1338210168,r11),(1019526792,r57),(351673181,r11),(1599117020,r3)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r91 : Rule 28 6 := cutRule 6 p2 w1
def p54 : Weak 28 7 := relaxed (pick [3,4,5,15,17,18,20] (by decide) (by decide) (by decide))
def r92 : Rule 28 6 := cutRule 6 p54 w40
def s87 : List ℕ := [f151,f13,f21,f22,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b39 : Ban 28 7 s87 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(274323443,r5),(2053011873,r5),(1652642120,r5),(607534840,r29),(1985853517,r2),(201721807,r5),(1580040484,r5),(1111276855,r2),(342111885,r91),(355190549,r5),(1733509226,r5),(186051562,r2),(1289795450,r5),(1778784023,r91),(1908130851,r5),(2068029187,r3),(1298864217,r2),(1327392636,r4),(558227666,r4),(216945860,r2),(1595264537,r91),(536085894,r4),(1914404571,r4),(1271580573,r2),(372165509,r4),(1804062616,r91),(557743120,r4),(219674837,r3),(1726762782,r5),(1733216904,r5),(1486712086,r4),(716128875,r11),(2094447552,r2),(1166978233,r0),(397813263,r0),(2003915098,r2),(1234750128,r91),(608070654,r0),(1986389331,r0),(105178461,r2),(419227371,r0),(784742552,r91),(1372624012,r0),(323679024,r11),(2063485781,r5),(837524554,r5),(1763830773,r0),(332437229,r11),(13753853,r4),(1493383889,r4),(593344081,r0),(1835601322,r2),(2072209291,r2),(1066436352,r91),(911301165,r89),(510931412,r2),(253225072,r92),(1394935780,r5),(2000338966,r2),(994566027,r5),(299251381,r2),(1440962089,r5),(354207391,r70),(1495918099,r5),(1335654583,r2),(329881644,r5),(1683116278,r29),(677343339,r5),(680064647,r2),(1821775355,r5),(1319624385,r77),(313851446,r4),(102125926,r2),(1243836634,r5),(657165846,r3),(1798876554,r4),(192799369,r2),(1334510077,r5),(1592244458,r84),(586471519,r0),(160095609,r2),(1301806317,r5),(1516525816,r11),(510752877,r0)])
  (by decide) (by decide +kernel) (by decide +kernel)
def s88 : List ℕ := [f21,f22,f15,f13,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b0 : Ban 28 8 s88 := viaRules (ws := [s11,s17,s19,s20,s27,s31,s33,s34,s42,s44,s46,s47,s50,s52,s54,s56,s58,s60,s69,s71,s75,s76,s80,s82,s84,s86,s87]) (consBan b1 (consBan b4 (consBan b6 (consBan b7 (consBan b8 (consBan b11 (consBan b13 (consBan b14 (consBan b15 (consBan b18 (consBan b20 (consBan b21 (consBan b22 (consBan b23 (consBan b24 (consBan b25 (consBan b26 (consBan b27 (consBan b28 (consBan b30 (consBan b31 (consBan b33 (consBan b34 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (nilBan _ _))))))))))))))))))))))))))))
  (dictionary [(2058960420,r61),(400465346,r61),(1141330479,r61),(425743939,r61),(1188392341,r61),(1553907522,r61),(62643412,r69),(1099046614,r69),(443456678,r69),(2013001604,r69),(2103675047,r69),(2070971287,r69),(274323443,r69),(1835601322,r61),(1763730997,r61)])
  (by decide) (by decide +kernel) (by decide +kernel)
theorem cert6 : Ban 28 8 s88 := b0
end PEqualNP.Outside.L_meta_12092.B1

namespace PEqualNP.Outside.L_meta_12092
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def target (x : Fin 6 → Bool) := Nat.testBit (4269860992 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[⟨.or,[0,2]⟩,⟨.and,[0,2]⟩,⟨.or,[4,5]⟩,⟨.and,[6,8]⟩,⟨.or,[1,9]⟩,⟨.and,[1,9]⟩,⟨.or,[4,11]⟩,⟨.and,[3,12]⟩,⟨.or,[7,13]⟩,⟨.or,[3,11]⟩,⟨.and,[14,15]⟩,⟨.and,[10,16]⟩],17⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem shaped : Monotone2 witness := by simp [witness,Monotone2]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem cost : witness.size=12 := rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem valid : ∀ x, witness.eval (List.ofFn x)=target x := by decide +kernel
def bank0 : List ℕ := [0x18c377f98c7ff,0x60d8bbfe0f8ff,0x7b00ddfff00ff,0x2d6d0efffff0f,0x56b6e007ffff0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem wide0 : Wide 28 8 bank0 := widen (by decide +kernel) B0.cert6
def bank1 : List ℕ := [0x221b0dba23f1ff,0x42c562dc3c7e3f,0x6c06b46fc07fc7,0x1568db07ff8ff8,0x7bb70007fff000]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem wide1 : Wide 28 8 bank1 := widen (by decide +kernel) B1.cert6
def inputs : List ℕ := [0x244361b603186efa23f1fff98c7ff,0x2858ac5a0c1b177c3c7e3ffe0f8ff,0x2d80d68c0f601bbfc07fc7fff00ff,0x2ad1b6005ada1c7ff8ff8fffff0f,0xf76e0000ad6dc07fff00007ffff0,0x1ffffffe0000001fffffff0000000]
def v : ℕ := 0x1ffffffe0000001fffffff0000000
def rr0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27]
def ix0 := rr0 ++ rr0.map (57+·)
def base0 : ℕ := 84
def pr0 : Weak 57 28 := signedPick base0 rr0 (by decide) (by decide) (by decide)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem images0 : ∀ a∈inputs, pr0.f a=0 ∨ pr0.f a∈bank0 := by decide +kernel
def rr1 : List ℕ := [28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55]
def ix1 := rr1 ++ rr1.map (57+·)
def base1 : ℕ := 112
def pr1 : Weak 57 28 := signedPick base1 rr1 (by decide) (by decide) (by decide)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem images1 : ∀ a∈inputs, pr1.f a=0 ∨ pr1.f a∈bank1 := by decide +kernel
def pr : Bool → Weak 57 28 | false => pr0 | true => pr1
def posBits : ℕ := 0x279fef7cf3cefaebae79e77df7baebadb6daebae79e73cf3cf3de79d75c71c6db69a6996595d75d73cf3cf
def negBits : ℕ := 0x7836d78d2ccf8caae31a76d73b2a9aca65aa98e696300000001639535850c4cb6122984495954c738d2c7
def sample (bank : ℕ) (i : Fin 57) (j : Fin 6) := bank.testBit (6*i.val+j.val)

def seeds : List Wire := inputs.map (fun a => (false,a))
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem listed : ∀ i : Fin 57, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (57+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem labels : ∀ i : Fin 57, target (sample posBits i)=true ∧ target (sample negBits i)=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem essential : ∀ a∈inputs, ∃ i : Fin 57, ∀ b∈inputs, b.testBit i.val≠b.testBit (57+i.val) → b=a := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem initial {k S} (live : Live 57 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 6 C=target) :
    ∃ k≤C.gates.countP counted, Live 57 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 6 → Bool) : C.eval (List.ofFn x)=target x := congrFun eq x
  have good : Good 57 out.2 := by
    intro i hi same
    let j : Fin 57 := ⟨i,hi⟩
    have diff : read i out=read (57+i) out := by simp [read,same]
    have p := ev i;have n := ev (57+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩


set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem killed (d a b : ℕ) (hd : d<4) (hit : v=a ∨ v=b) :
    ∃ t, (pr t).f (combine d a b)=0 := by
  rcases hit with rfl|rfl
  · obtain ⟨s,c,h⟩ := forced d hd true
    cases s with
    | false => exact ⟨false,forcedLeft (is:=ix0) (s:=false) (c:=c) hd (by decide) (by decide) (by simpa using h)⟩
    | true => exact ⟨true,forcedLeft (is:=ix1) (s:=true) (c:=c) hd (by decide) (by decide) (by simpa using h)⟩
  · obtain ⟨s,c,h⟩ := forced d hd false
    cases s with
    | false => exact ⟨false,forcedRight (is:=ix0) (s:=false) (c:=c) hd (by decide) (by decide) (by simpa using h)⟩
    | true => exact ⟨true,forcedRight (is:=ix1) (s:=true) (c:=c) hd (by decide) (by decide) (by simpa using h)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem eleven {k : ℕ} (live : Live 57 k inputs.toFinset) : 11≤k := by
  obtain ⟨t,j,T,lim,ok,sub⟩ := doubleElim pr v killed (by decide +kernel) live (by decide)
  by_contra! small
  have project {w : List ℕ} (im : ∀ a∈inputs, (pr t).f a=0 ∨ (pr t).f a∈w) : Possible 28 8 w := by
    refine ⟨j,T,by omega,ok,?_⟩
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (sub x hx)
    exact (im _ (List.mem_toFinset.mp ha)).resolve_left (liveNonzero ok _ hx)
  cases t
  · exact wide0 (project images0)
  · exact wide1 (project images1)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem counted_lt {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) : gs.countP counted < gs.length := by
  apply Nat.lt_of_le_of_ne List.countP_le_length
  intro eq
  obtain ⟨g,hg,hop⟩ := h
  have bad := List.countP_eq_length.mp eq g hg
  simp [counted,hop] at bad

set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem noSaving (s : ℕ) (h : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x,C.eval (List.ofFn x)=target x := by
  obtain ⟨C,fan,hsize,ev⟩ := h
  by_cases used : ∃ g∈C.gates, g.op=.not
  · obtain ⟨k,lim,ok⟩ := trace C fan (funext ev)
    have lb := eleven ok
    have strict := counted_lt used
    change C.gates.length ≤ s at hsize
    refine ⟨witness,shaped,?_,valid⟩
    rw [cost]; omega
  · refine ⟨C,?_,hsize,ev⟩
    intro g hg
    rcases (fan g hg).1 with a|b|n
    · exact ⟨Or.inl a,(fan g hg).2⟩
    · exact ⟨Or.inr b,(fan g hg).2⟩
    · exact False.elim (used ⟨g,hg,n⟩)
end PEqualNP.Outside.L_meta_12092

theorem PEqualNP.Outside.L_meta_12092 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860992 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860992 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_12092.noSaving
