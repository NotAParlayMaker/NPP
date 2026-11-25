import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_15863

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
def restrictedInputs : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
def splitV0 : List ℕ := [0x600001f,0x2108428007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB0 : Ban 28 4 splitV0 := viaSmall (by decide +kernel) (by decide)

def splitV1 : List ℕ := [0x600001f,0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB1 : Ban 28 4 splitV1 := viaSmall (by decide +kernel) (by decide)

def splitV2 : List ℕ := [0x600001f,0x8421088007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB2 : Ban 28 4 splitV2 := viaSmall (by decide +kernel) (by decide)

def splitV3 : List ℕ := [0x600001f,0xc6318c1f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB3 : Ban 28 4 splitV3 := viaSmall (by decide +kernel) (by decide)

def splitV4 : List ℕ := [0x600001f,0x108421000f8000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB4 : Ban 28 4 splitV4 := viaSmall (by decide +kernel) (by decide)

def splitV5 : List ℕ := [0x600001f,0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB5 : Ban 28 4 splitV5 := viaSmall (by decide +kernel) (by decide)

def splitV6 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63100ffc00,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB6 : Ban 28 4 splitV6 := viaSmall (by decide +kernel) (by decide)

def splitV7 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8c6318c80003e0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB7 : Ban 28 4 splitV7 := viaSmall (by decide +kernel) (by decide)

def splitV8 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ade0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB8 : Ban 28 4 splitV8 := viaSmall (by decide +kernel) (by decide)

def splitV9 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xbdef7bde0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB9 : Ban 28 4 splitV9 := viaSmall (by decide +kernel) (by decide)

def splitV10 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c7ff801f,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB10 : Ban 28 4 splitV10 := viaSmall (by decide +kernel) (by decide)

def splitV11 : List ℕ := [0x600001f,0x1ad6b5aff07fff,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB11 : Ban 28 4 splitV11 := viaSmall (by decide +kernel) (by decide)

def splitV12 : List ℕ := [0x600001f,0x1ce739c1ff8000,0x1ef7bde9ffffe0,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB12 : Ban 28 4 splitV12 := viaSmall (by decide +kernel) (by decide)

def splitV13 : List ℕ := [0x600001f,0x1ce739c1ff8000,0x318c63160ffc1f,0x85294a500f8000,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB13 : Ban 28 4 splitV13 := viaSmall (by decide +kernel) (by decide)

def splitV14 : List ℕ := [0x1ad6b5a9f07fe0,0x1ad6b5aff07fff,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB14 : Ban 28 4 splitV14 := viaSmall (by decide +kernel) (by decide)

def splitV15 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x1ce739c7ff801f,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB15 : Ban 28 4 splitV15 := viaSmall (by decide +kernel) (by decide)

def splitV16 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63100ffc00,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB16 : Ban 28 4 splitV16 := viaSmall (by decide +kernel) (by decide)

def splitV17 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0x8d6b5ade0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB17 : Ban 28 4 splitV17 := viaSmall (by decide +kernel) (by decide)

def splitV18 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c7ff801f,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB18 : Ban 28 4 splitV18 := viaSmall (by decide +kernel) (by decide)

def splitV19 : List ℕ := [0x1ad6b5aff07fff,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB19 : Ban 28 4 splitV19 := viaSmall (by decide +kernel) (by decide)

def splitV20 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB20 : Ban 28 5 splitV20 := viaBranch (ws := [splitV0,splitV1,splitV2,splitV3,splitV4,splitV5,splitV6,splitV7,splitV8,splitV9,splitV10,splitV11,splitV12,splitV13,splitV14,splitV15,splitV16,splitV17,splitV18,splitV19])
 (consBan splitB0 (consBan splitB1 (consBan splitB2 (consBan splitB3 (consBan splitB4 (consBan splitB5 (consBan splitB6 (consBan splitB7 (consBan splitB8 (consBan splitB9 (consBan splitB10 (consBan splitB11 (consBan splitB12 (consBan splitB13 (consBan splitB14 (consBan splitB15 (consBan splitB16 (consBan splitB17 (consBan splitB18 (consBan splitB19 (nilBan 28 4)))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV21 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB21 : Ban 28 5 splitV21 := viaSmall (by decide +kernel) (by decide)

def splitV22 : List ℕ := [0x600001f,0x4210841f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB22 : Ban 28 4 splitV22 := viaSmall (by decide +kernel) (by decide)

def splitV23 : List ℕ := [0x600001f,0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB23 : Ban 28 4 splitV23 := viaSmall (by decide +kernel) (by decide)

def splitV24 : List ℕ := [0x600001f,0x8421088007fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB24 : Ban 28 4 splitV24 := viaSmall (by decide +kernel) (by decide)

def splitV25 : List ℕ := [0x600001f,0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB25 : Ban 28 4 splitV25 := viaSmall (by decide +kernel) (by decide)

def splitV26 : List ℕ := [0x600001f,0x18c631800f8000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB26 : Ban 28 4 splitV26 := viaSmall (by decide +kernel) (by decide)

def splitV27 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x42108427f0001f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB27 : Ban 28 4 splitV27 := viaSmall (by decide +kernel) (by decide)

def splitV28 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x81084218007fe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB28 : Ban 28 4 splitV28 := viaSmall (by decide +kernel) (by decide)

def splitV29 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x842108480003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB29 : Ban 28 4 splitV29 := viaSmall (by decide +kernel) (by decide)

def splitV30 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc6318c69f003e0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB30 : Ban 28 4 splitV30 := viaSmall (by decide +kernel) (by decide)

def splitV31 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ade0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB31 : Ban 28 4 splitV31 := viaSmall (by decide +kernel) (by decide)

def splitV32 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x9def7bd9ffffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB32 : Ban 28 4 splitV32 := viaSmall (by decide +kernel) (by decide)

def splitV33 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c7ff801f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB33 : Ban 28 4 splitV33 := viaSmall (by decide +kernel) (by decide)

def splitV34 : List ℕ := [0x600001f,0x1ad6b5aff07fff,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB34 : Ban 28 4 splitV34 := viaSmall (by decide +kernel) (by decide)

def splitV35 : List ℕ := [0x600001f,0x1ce739c1ff8000,0x85294a500f8000,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB35 : Ban 28 4 splitV35 := viaSmall (by decide +kernel) (by decide)

def splitV36 : List ℕ := [0x1ad6b5a9f07fe0,0x1ad6b5aff07fff,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB36 : Ban 28 4 splitV36 := viaSmall (by decide +kernel) (by decide)

def splitV37 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x1ce739c7ff801f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB37 : Ban 28 4 splitV37 := viaSmall (by decide +kernel) (by decide)

def splitV38 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0x8d6b5ade0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB38 : Ban 28 4 splitV38 := viaSmall (by decide +kernel) (by decide)

def splitV39 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc6318c69f003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB39 : Ban 28 4 splitV39 := viaSmall (by decide +kernel) (by decide)

def splitV40 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ade0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB40 : Ban 28 4 splitV40 := viaSmall (by decide +kernel) (by decide)

def splitV41 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c7ff801f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB41 : Ban 28 4 splitV41 := viaSmall (by decide +kernel) (by decide)

def splitV42 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB42 : Ban 28 5 splitV42 := viaBranch (ws := [splitV22,splitV23,splitV24,splitV25,splitV26,splitV27,splitV28,splitV29,splitV30,splitV31,splitV32,splitV33,splitV34,splitV35,splitV36,splitV37,splitV38,splitV39,splitV40,splitV41])
 (consBan splitB22 (consBan splitB23 (consBan splitB24 (consBan splitB25 (consBan splitB26 (consBan splitB27 (consBan splitB28 (consBan splitB29 (consBan splitB30 (consBan splitB31 (consBan splitB32 (consBan splitB33 (consBan splitB34 (consBan splitB35 (consBan splitB36 (consBan splitB37 (consBan splitB38 (consBan splitB39 (consBan splitB40 (consBan splitB41 (nilBan 28 4)))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV43 : List ℕ := [0x10842100ffc00,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB43 : Ban 28 5 splitV43 := viaSmall (by decide +kernel) (by decide)

def splitV44 : List ℕ := [0x2108428007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB44 : Ban 28 5 splitV44 := viaSmall (by decide +kernel) (by decide)

def splitV45 : List ℕ := [0x2108428007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB45 : Ban 28 5 splitV45 := viaSmall (by decide +kernel) (by decide)

def splitV46 : List ℕ := [0x2108429f003e0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB46 : Ban 28 5 splitV46 := viaSmall (by decide +kernel) (by decide)

def splitV47 : List ℕ := [0x42108400f8000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB47 : Ban 28 5 splitV47 := viaSmall (by decide +kernel) (by decide)

def splitV48 : List ℕ := [0x4210841f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB48 : Ban 28 5 splitV48 := viaSmall (by decide +kernel) (by decide)

def splitV49 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB49 : Ban 28 5 splitV49 := viaSmall (by decide +kernel) (by decide)

def splitV50 : List ℕ := [0x80003e0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB50 : Ban 28 4 splitV50 := viaSmall (by decide +kernel) (by decide)

def splitV51 : List ℕ := [0x8007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB51 : Ban 28 4 splitV51 := viaSmall (by decide +kernel) (by decide)

def splitV52 : List ℕ := [0x42108400f8000,0x8421088007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB52 : Ban 28 4 splitV52 := viaSmall (by decide +kernel) (by decide)

def splitV53 : List ℕ := [0x84210880003e0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB53 : Ban 28 4 splitV53 := viaSmall (by decide +kernel) (by decide)

def splitV54 : List ℕ := [0x8421088007fe0,0x1294a521f00000,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB54 : Ban 28 4 splitV54 := viaSmall (by decide +kernel) (by decide)

def splitV55 : List ℕ := [0x8421088007fe0,0x14a52941ff8000,0x1ad6b5a9f07fe0,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB55 : Ban 28 4 splitV55 := viaSmall (by decide +kernel) (by decide)

def splitV56 : List ℕ := [0x8421088007fe0,0x18c63181f00000,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB56 : Ban 28 4 splitV56 := viaSmall (by decide +kernel) (by decide)

def splitV57 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x21084216007c1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB57 : Ban 28 4 splitV57 := viaSmall (by decide +kernel) (by decide)

def splitV58 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x210842160f801f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB58 : Ban 28 4 splitV58 := viaSmall (by decide +kernel) (by decide)

def splitV59 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63100ffc00,0x318c63160ffc1f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB59 : Ban 28 4 splitV59 := viaSmall (by decide +kernel) (by decide)

def splitV60 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160f801f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB60 : Ban 28 4 splitV60 := viaSmall (by decide +kernel) (by decide)

def splitV61 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc210842e0003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB61 : Ban 28 4 splitV61 := viaSmall (by decide +kernel) (by decide)

def splitV62 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB62 : Ban 28 4 splitV62 := viaSmall (by decide +kernel) (by decide)

def splitV63 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c67f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB63 : Ban 28 4 splitV63 := viaSmall (by decide +kernel) (by decide)

def splitV64 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xce739ceff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB64 : Ban 28 4 splitV64 := viaSmall (by decide +kernel) (by decide)

def splitV65 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB65 : Ban 28 4 splitV65 := viaSmall (by decide +kernel) (by decide)

def splitV66 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB66 : Ban 28 4 splitV66 := viaSmall (by decide +kernel) (by decide)

def splitV67 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x39ce739e0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB67 : Ban 28 4 splitV67 := viaSmall (by decide +kernel) (by decide)

def splitV68 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3bdef7bfffffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB68 : Ban 28 4 splitV68 := viaSmall (by decide +kernel) (by decide)

def splitV69 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3def7bd7fffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB69 : Ban 28 4 splitV69 := viaSmall (by decide +kernel) (by decide)

def splitV70 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xc6318c69f003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB70 : Ban 28 4 splitV70 := viaSmall (by decide +kernel) (by decide)

def splitV71 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c9ffffe0,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB71 : Ban 28 4 splitV71 := viaSmall (by decide +kernel) (by decide)

def splitV72 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB72 : Ban 28 4 splitV72 := viaSmall (by decide +kernel) (by decide)

def splitV73 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x1ce739c9ffffe0,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB73 : Ban 28 4 splitV73 := viaSmall (by decide +kernel) (by decide)

def splitV74 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x39ce739e0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB74 : Ban 28 4 splitV74 := viaSmall (by decide +kernel) (by decide)

def splitV75 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c67f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB75 : Ban 28 4 splitV75 := viaSmall (by decide +kernel) (by decide)

def splitV76 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c67f0001f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB76 : Ban 28 4 splitV76 := viaSmall (by decide +kernel) (by decide)

def splitV77 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x39ce739e0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB77 : Ban 28 4 splitV77 := viaSmall (by decide +kernel) (by decide)

def splitV78 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB78 : Ban 28 5 splitV78 := viaBranch (ws := [splitV1,splitV23,splitV50,splitV51,splitV52,splitV53,splitV54,splitV55,splitV56,splitV57,splitV58,splitV59,splitV60,splitV61,splitV62,splitV63,splitV64,splitV65,splitV66,splitV67,splitV68,splitV69,splitV70,splitV71,splitV72,splitV73,splitV74,splitV75,splitV76,splitV77])
 (consBan splitB1 (consBan splitB23 (consBan splitB50 (consBan splitB51 (consBan splitB52 (consBan splitB53 (consBan splitB54 (consBan splitB55 (consBan splitB56 (consBan splitB57 (consBan splitB58 (consBan splitB59 (consBan splitB60 (consBan splitB61 (consBan splitB62 (consBan splitB63 (consBan splitB64 (consBan splitB65 (consBan splitB66 (consBan splitB67 (consBan splitB68 (consBan splitB69 (consBan splitB70 (consBan splitB71 (consBan splitB72 (consBan splitB73 (consBan splitB74 (consBan splitB75 (consBan splitB76 (consBan splitB77 (nilBan 28 4)))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV79 : List ℕ := [0x8421088007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB79 : Ban 28 5 splitV79 := viaSmall (by decide +kernel) (by decide)

def splitV80 : List ℕ := [0x94a52900ffc00,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB80 : Ban 28 5 splitV80 := viaSmall (by decide +kernel) (by decide)

def splitV81 : List ℕ := [0xa5294a9f003e0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB81 : Ban 28 5 splitV81 := viaSmall (by decide +kernel) (by decide)

def splitV82 : List ℕ := [0xc6318c00f8000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB82 : Ban 28 5 splitV82 := viaSmall (by decide +kernel) (by decide)

def splitV83 : List ℕ := [0xc6318c1f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB83 : Ban 28 5 splitV83 := viaSmall (by decide +kernel) (by decide)

def splitV84 : List ℕ := [0x10842100007c00,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB84 : Ban 28 5 splitV84 := viaSmall (by decide +kernel) (by decide)

def splitV85 : List ℕ := [0x108421000f8000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB85 : Ban 28 5 splitV85 := viaSmall (by decide +kernel) (by decide)

def splitV86 : List ℕ := [0x10842101f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB86 : Ban 28 5 splitV86 := viaSmall (by decide +kernel) (by decide)

def splitV87 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB87 : Ban 28 5 splitV87 := viaSmall (by decide +kernel) (by decide)

def splitV88 : List ℕ := [0x2108420000000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB88 : Ban 28 4 splitV88 := viaSmall (by decide +kernel) (by decide)

def splitV89 : List ℕ := [0x2108421f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB89 : Ban 28 4 splitV89 := viaSmall (by decide +kernel) (by decide)

def splitV90 : List ℕ := [0x2108428007fe0,0x1294a521f00000,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB90 : Ban 28 4 splitV90 := viaSmall (by decide +kernel) (by decide)

def splitV91 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB91 : Ban 28 4 splitV91 := viaSmall (by decide +kernel) (by decide)

def splitV92 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x21084216007c1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB92 : Ban 28 4 splitV92 := viaSmall (by decide +kernel) (by decide)

def splitV93 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x210842160f801f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB93 : Ban 28 4 splitV93 := viaSmall (by decide +kernel) (by decide)

def splitV94 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x210842160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB94 : Ban 28 4 splitV94 := viaSmall (by decide +kernel) (by decide)

def splitV95 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63100ffc00,0x318c63160ffc1f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB95 : Ban 28 4 splitV95 := viaSmall (by decide +kernel) (by decide)

def splitV96 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc210842e0003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB96 : Ban 28 4 splitV96 := viaSmall (by decide +kernel) (by decide)

def splitV97 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB97 : Ban 28 4 splitV97 := viaSmall (by decide +kernel) (by decide)

def splitV98 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc421084e0003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB98 : Ban 28 4 splitV98 := viaSmall (by decide +kernel) (by decide)

def splitV99 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xd6b5ad6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB99 : Ban 28 4 splitV99 := viaSmall (by decide +kernel) (by decide)

def splitV100 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB100 : Ban 28 4 splitV100 := viaSmall (by decide +kernel) (by decide)

def splitV101 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB101 : Ban 28 4 splitV101 := viaSmall (by decide +kernel) (by decide)

def splitV102 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x339ce737fffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB102 : Ban 28 4 splitV102 := viaSmall (by decide +kernel) (by decide)

def splitV103 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3bdef7bfffffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB103 : Ban 28 4 splitV103 := viaSmall (by decide +kernel) (by decide)

def splitV104 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3def7bd7fffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB104 : Ban 28 4 splitV104 := viaSmall (by decide +kernel) (by decide)

def splitV105 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xc6318c69f003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB105 : Ban 28 4 splitV105 := viaSmall (by decide +kernel) (by decide)

def splitV106 : List ℕ := [0x1294a521f00000,0x1ce739c1ff8000,0x1ef7bde9ffffe0,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB106 : Ban 28 4 splitV106 := viaSmall (by decide +kernel) (by decide)

def splitV107 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x1ef7bde1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB107 : Ban 28 4 splitV107 := viaSmall (by decide +kernel) (by decide)

def splitV108 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x339ce737fffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB108 : Ban 28 4 splitV108 := viaSmall (by decide +kernel) (by decide)

def splitV109 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc421084e0003ff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB109 : Ban 28 4 splitV109 := viaSmall (by decide +kernel) (by decide)

def splitV110 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x339ce737fffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB110 : Ban 28 4 splitV110 := viaSmall (by decide +kernel) (by decide)

def splitV111 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB111 : Ban 28 5 splitV111 := viaBranch (ws := [splitV5,splitV25,splitV88,splitV89,splitV90,splitV54,splitV91,splitV92,splitV93,splitV94,splitV95,splitV96,splitV97,splitV98,splitV99,splitV100,splitV101,splitV102,splitV103,splitV104,splitV105,splitV106,splitV107,splitV108,splitV109,splitV110])
 (consBan splitB5 (consBan splitB25 (consBan splitB88 (consBan splitB89 (consBan splitB90 (consBan splitB54 (consBan splitB91 (consBan splitB92 (consBan splitB93 (consBan splitB94 (consBan splitB95 (consBan splitB96 (consBan splitB97 (consBan splitB98 (consBan splitB99 (consBan splitB100 (consBan splitB101 (consBan splitB102 (consBan splitB103 (consBan splitB104 (consBan splitB105 (consBan splitB106 (consBan splitB107 (consBan splitB108 (consBan splitB109 (consBan splitB110 (nilBan 28 4)))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV112 : List ℕ := [0x18c63180007c00,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB112 : Ban 28 5 splitV112 := viaSmall (by decide +kernel) (by decide)

def splitV113 : List ℕ := [0x18c631800f8000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB113 : Ban 28 5 splitV113 := viaSmall (by decide +kernel) (by decide)

def splitV114 : List ℕ := [0x18c63181f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB114 : Ban 28 5 splitV114 := viaSmall (by decide +kernel) (by decide)

def splitV115 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x1ef7bde9ffffe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB115 : Ban 28 5 splitV115 := viaSmall (by decide +kernel) (by decide)

def splitV116 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x21084216007c1f,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB116 : Ban 28 5 splitV116 := viaSmall (by decide +kernel) (by decide)

def splitV117 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB117 : Ban 28 4 splitV117 := viaSmall (by decide +kernel) (by decide)

def splitV118 : List ℕ := [0x2108428007fe0,0x1ad6b5a9f07fe0,0x21084216007c1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB118 : Ban 28 4 splitV118 := viaSmall (by decide +kernel) (by decide)

def splitV119 : List ℕ := [0x4210841f00000,0x1ad6b5a9f07fe0,0x21084216007c1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB119 : Ban 28 4 splitV119 := viaSmall (by decide +kernel) (by decide)

def splitV120 : List ℕ := [0x8421088007fe0,0x1ce739c1ff8000,0x21084216007c1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB120 : Ban 28 4 splitV120 := viaSmall (by decide +kernel) (by decide)

def splitV121 : List ℕ := [0x10842101f00000,0x1ad6b5a9f07fe0,0x21084216007c1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB121 : Ban 28 4 splitV121 := viaSmall (by decide +kernel) (by decide)

def splitV122 : List ℕ := [0x18c63181f00000,0x1ad6b5a9f07fe0,0x21084216007c1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB122 : Ban 28 4 splitV122 := viaSmall (by decide +kernel) (by decide)

def splitV123 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x2000000600001f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB123 : Ban 28 4 splitV123 := viaSmall (by decide +kernel) (by decide)

def splitV124 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x2108421600001f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB124 : Ban 28 4 splitV124 := viaSmall (by decide +kernel) (by decide)

def splitV125 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x21084216007c1f,0x42108427f0001f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB125 : Ban 28 4 splitV125 := viaSmall (by decide +kernel) (by decide)

def splitV126 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x21084216007c1f,0x81084218007fe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB126 : Ban 28 4 splitV126 := viaSmall (by decide +kernel) (by decide)

def splitV127 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x21084216007c1f,0x842108480003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB127 : Ban 28 4 splitV127 := viaSmall (by decide +kernel) (by decide)

def splitV128 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x21084216007c1f,0x8c6318c80f83e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB128 : Ban 28 4 splitV128 := viaSmall (by decide +kernel) (by decide)

def splitV129 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x21084216007c1f,0x9def7bd9ffffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB129 : Ban 28 4 splitV129 := viaSmall (by decide +kernel) (by decide)

def splitV130 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x21084216007c1f,0xad6b5ade0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB130 : Ban 28 4 splitV130 := viaSmall (by decide +kernel) (by decide)

def splitV131 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3bdef7bff07fff,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB131 : Ban 28 4 splitV131 := viaSmall (by decide +kernel) (by decide)

def splitV132 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3def7bd7fffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB132 : Ban 28 4 splitV132 := viaSmall (by decide +kernel) (by decide)

def splitV133 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xad6b5ade0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB133 : Ban 28 4 splitV133 := viaSmall (by decide +kernel) (by decide)

def splitV134 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xad6b5ade0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB134 : Ban 28 4 splitV134 := viaSmall (by decide +kernel) (by decide)

def splitV135 : List ℕ := [0x1ad6b5a9f07fe0,0x21084216007c1f,0x3def7bd7fffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB135 : Ban 28 4 splitV135 := viaSmall (by decide +kernel) (by decide)

def splitV136 : List ℕ := [0x1ad6b5a9f07fe0,0x21084216007c1f,0x8d6b5ad80fffe0,0x9def7bd9ffffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB136 : Ban 28 4 splitV136 := viaSmall (by decide +kernel) (by decide)

def splitV137 : List ℕ := [0x1ad6b5a9f07fe0,0x21084216007c1f,0x8d6b5ad80fffe0,0xc210842e0003ff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB137 : Ban 28 4 splitV137 := viaSmall (by decide +kernel) (by decide)

def splitV138 : List ℕ := [0x1ad6b5a9f07fe0,0x21084216007c1f,0x9def7bd9ffffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB138 : Ban 28 4 splitV138 := viaSmall (by decide +kernel) (by decide)

def splitV139 : List ℕ := [0x1ce739c1ff8000,0x21084216007c1f,0x85294a500f8000,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB139 : Ban 28 4 splitV139 := viaSmall (by decide +kernel) (by decide)

def splitV140 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x21084216007c1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB140 : Ban 28 5 splitV140 := viaBranch (ws := [splitV117,splitV118,splitV119,splitV57,splitV120,splitV121,splitV92,splitV122,splitV123,splitV124,splitV125,splitV126,splitV127,splitV128,splitV129,splitV130,splitV131,splitV132,splitV133,splitV39,splitV134,splitV135,splitV136,splitV137,splitV138,splitV139])
 (consBan splitB117 (consBan splitB118 (consBan splitB119 (consBan splitB57 (consBan splitB120 (consBan splitB121 (consBan splitB92 (consBan splitB122 (consBan splitB123 (consBan splitB124 (consBan splitB125 (consBan splitB126 (consBan splitB127 (consBan splitB128 (consBan splitB129 (consBan splitB130 (consBan splitB131 (consBan splitB132 (consBan splitB133 (consBan splitB39 (consBan splitB134 (consBan splitB135 (consBan splitB136 (consBan splitB137 (consBan splitB138 (consBan splitB139 (nilBan 28 4)))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV141 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x210842160f801f,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB141 : Ban 28 5 splitV141 := viaSmall (by decide +kernel) (by decide)

def splitV142 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x210842160f801f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB142 : Ban 28 5 splitV142 := viaSmall (by decide +kernel) (by decide)

def splitV143 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3084210600001f,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB143 : Ban 28 5 splitV143 := viaSmall (by decide +kernel) (by decide)

def splitV144 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3084210600001f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB144 : Ban 28 5 splitV144 := viaSmall (by decide +kernel) (by decide)

def splitV145 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB145 : Ban 28 4 splitV145 := viaSmall (by decide +kernel) (by decide)

def splitV146 : List ℕ := [0x2108428007fe0,0x1ce739c1ff8000,0x318c63100ffc00,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB146 : Ban 28 4 splitV146 := viaSmall (by decide +kernel) (by decide)

def splitV147 : List ℕ := [0x8421088007fe0,0x1ce739c1ff8000,0x318c63100ffc00,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB147 : Ban 28 4 splitV147 := viaSmall (by decide +kernel) (by decide)

def splitV148 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x21084210007c00,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB148 : Ban 28 4 splitV148 := viaSmall (by decide +kernel) (by decide)

def splitV149 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x210842100f8000,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB149 : Ban 28 4 splitV149 := viaSmall (by decide +kernel) (by decide)

def splitV150 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x21084216007c1f,0x318c63100ffc00,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB150 : Ban 28 4 splitV150 := viaSmall (by decide +kernel) (by decide)

def splitV151 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x210842160f801f,0x318c63100ffc00,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB151 : Ban 28 4 splitV151 := viaSmall (by decide +kernel) (by decide)

def splitV152 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x30842100000000,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB152 : Ban 28 4 splitV152 := viaSmall (by decide +kernel) (by decide)

def splitV153 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3084210600001f,0x318c63100ffc00,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB153 : Ban 28 4 splitV153 := viaSmall (by decide +kernel) (by decide)

def splitV154 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63100ffc00,0x318c63160ffc1f,0x8c6318c80003e0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB154 : Ban 28 4 splitV154 := viaSmall (by decide +kernel) (by decide)

def splitV155 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63100ffc00,0x318c63160ffc1f,0xbdef7bd80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB155 : Ban 28 4 splitV155 := viaSmall (by decide +kernel) (by decide)

def splitV156 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63100ffc00,0x318c63160ffc1f,0xbdef7bde0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB156 : Ban 28 4 splitV156 := viaSmall (by decide +kernel) (by decide)

def splitV157 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63100ffc00,0x3bdef7bfffffff,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB157 : Ban 28 4 splitV157 := viaSmall (by decide +kernel) (by decide)

def splitV158 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63100ffc00,0x3def7bd7fffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB158 : Ban 28 4 splitV158 := viaSmall (by decide +kernel) (by decide)

def splitV159 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63100ffc00,0x8d6b5ad80fffe0,0xbdef7bde0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB159 : Ban 28 4 splitV159 := viaSmall (by decide +kernel) (by decide)

def splitV160 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63100ffc00,0xbdef7bde0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB160 : Ban 28 4 splitV160 := viaSmall (by decide +kernel) (by decide)

def splitV161 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x3bdef7b9ffffe0,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB161 : Ban 28 4 splitV161 := viaSmall (by decide +kernel) (by decide)

def splitV162 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x3def7bd1fffc00,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB162 : Ban 28 4 splitV162 := viaSmall (by decide +kernel) (by decide)

def splitV163 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xbdef7bd80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB163 : Ban 28 4 splitV163 := viaSmall (by decide +kernel) (by decide)

def splitV164 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xbdef7bd80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB164 : Ban 28 4 splitV164 := viaSmall (by decide +kernel) (by decide)

def splitV165 : List ℕ := [0x1ce739c1ff8000,0x1ef7bde9ffffe0,0x318c63100ffc00,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB165 : Ban 28 4 splitV165 := viaSmall (by decide +kernel) (by decide)

def splitV166 : List ℕ := [0x1ce739c1ff8000,0x318c63100ffc00,0x318c63160ffc1f,0x85294a500f8000,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB166 : Ban 28 4 splitV166 := viaSmall (by decide +kernel) (by decide)

def splitV167 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63100ffc00,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB167 : Ban 28 5 splitV167 := viaBranch (ws := [splitV6,splitV145,splitV146,splitV59,splitV147,splitV95,splitV148,splitV149,splitV150,splitV151,splitV152,splitV153,splitV154,splitV155,splitV156,splitV157,splitV158,splitV159,splitV160,splitV161,splitV162,splitV163,splitV164,splitV165,splitV166])
 (consBan splitB6 (consBan splitB145 (consBan splitB146 (consBan splitB59 (consBan splitB147 (consBan splitB95 (consBan splitB148 (consBan splitB149 (consBan splitB150 (consBan splitB151 (consBan splitB152 (consBan splitB153 (consBan splitB154 (consBan splitB155 (consBan splitB156 (consBan splitB157 (consBan splitB158 (consBan splitB159 (consBan splitB160 (consBan splitB161 (consBan splitB162 (consBan splitB163 (consBan splitB164 (consBan splitB165 (consBan splitB166 (nilBan 28 4))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV168 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63100ffc00,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB168 : Ban 28 5 splitV168 := viaSmall (by decide +kernel) (by decide)

def splitV169 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x3bdef7bfffffff,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB169 : Ban 28 5 splitV169 := viaSmall (by decide +kernel) (by decide)

def splitV170 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x3def7bd7fffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB170 : Ban 28 5 splitV170 := viaSmall (by decide +kernel) (by decide)

def splitV171 : List ℕ := [0x1f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB171 : Ban 28 4 splitV171 := viaSmall (by decide +kernel) (by decide)

def splitV172 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB172 : Ban 28 4 splitV172 := viaSmall (by decide +kernel) (by decide)

def splitV173 : List ℕ := [0x2108421f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB173 : Ban 28 4 splitV173 := viaSmall (by decide +kernel) (by decide)

def splitV174 : List ℕ := [0x2108428007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB174 : Ban 28 4 splitV174 := viaSmall (by decide +kernel) (by decide)

def splitV175 : List ℕ := [0x42108400f8000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB175 : Ban 28 4 splitV175 := viaSmall (by decide +kernel) (by decide)

def splitV176 : List ℕ := [0xa5294a9f003e0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB176 : Ban 28 4 splitV176 := viaSmall (by decide +kernel) (by decide)

def splitV177 : List ℕ := [0xc6318c1f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB177 : Ban 28 4 splitV177 := viaSmall (by decide +kernel) (by decide)

def splitV178 : List ℕ := [0x10842100007c00,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB178 : Ban 28 4 splitV178 := viaSmall (by decide +kernel) (by decide)

def splitV179 : List ℕ := [0x108421000f8000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB179 : Ban 28 4 splitV179 := viaSmall (by decide +kernel) (by decide)

def splitV180 : List ℕ := [0x18c63181f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB180 : Ban 28 4 splitV180 := viaSmall (by decide +kernel) (by decide)

def splitV181 : List ℕ := [0x18c63188007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB181 : Ban 28 4 splitV181 := viaSmall (by decide +kernel) (by decide)

def splitV182 : List ℕ := [0x18c63188007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB182 : Ban 28 4 splitV182 := viaSmall (by decide +kernel) (by decide)

def splitV183 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c00f8000,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB183 : Ban 28 4 splitV183 := viaSmall (by decide +kernel) (by decide)

def splitV184 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x1ef7bde9ffffe0,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB184 : Ban 28 4 splitV184 := viaSmall (by decide +kernel) (by decide)

def splitV185 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x21084216007c1f,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB185 : Ban 28 4 splitV185 := viaSmall (by decide +kernel) (by decide)

def splitV186 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x210842160f801f,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB186 : Ban 28 4 splitV186 := viaSmall (by decide +kernel) (by decide)

def splitV187 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x210842160f801f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB187 : Ban 28 4 splitV187 := viaSmall (by decide +kernel) (by decide)

def splitV188 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63100ffc00,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB188 : Ban 28 4 splitV188 := viaSmall (by decide +kernel) (by decide)

def splitV189 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x3bdef7bfffffff,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB189 : Ban 28 4 splitV189 := viaSmall (by decide +kernel) (by decide)

def splitV190 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x3def7bd7fffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB190 : Ban 28 4 splitV190 := viaSmall (by decide +kernel) (by decide)

def splitV191 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x4000000600001f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB191 : Ban 28 4 splitV191 := viaSmall (by decide +kernel) (by decide)

def splitV192 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108421f00000,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB192 : Ban 28 4 splitV192 := viaSmall (by decide +kernel) (by decide)

def splitV193 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x4210842600001f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB193 : Ban 28 4 splitV193 := viaSmall (by decide +kernel) (by decide)

def splitV194 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x5ad6b5aff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB194 : Ban 28 4 splitV194 := viaSmall (by decide +kernel) (by decide)

def splitV195 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x5ef7bde7ff801f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB195 : Ban 28 4 splitV195 := viaSmall (by decide +kernel) (by decide)

def splitV196 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x739ce737fffc1f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB196 : Ban 28 4 splitV196 := viaSmall (by decide +kernel) (by decide)

def splitV197 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3bdef7bfffffff,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB197 : Ban 28 4 splitV197 := viaSmall (by decide +kernel) (by decide)

def splitV198 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x5ad6b5aff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB198 : Ban 28 4 splitV198 := viaSmall (by decide +kernel) (by decide)

def splitV199 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB199 : Ban 28 5 splitV199 := viaBranch (ws := [splitV171,splitV172,splitV173,splitV174,splitV175,splitV176,splitV177,splitV178,splitV179,splitV180,splitV181,splitV182,splitV183,splitV184,splitV185,splitV186,splitV187,splitV188,splitV189,splitV190,splitV191,splitV192,splitV193,splitV194,splitV195,splitV196,splitV197,splitV198])
 (consBan splitB171 (consBan splitB172 (consBan splitB173 (consBan splitB174 (consBan splitB175 (consBan splitB176 (consBan splitB177 (consBan splitB178 (consBan splitB179 (consBan splitB180 (consBan splitB181 (consBan splitB182 (consBan splitB183 (consBan splitB184 (consBan splitB185 (consBan splitB186 (consBan splitB187 (consBan splitB188 (consBan splitB189 (consBan splitB190 (consBan splitB191 (consBan splitB192 (consBan splitB193 (consBan splitB194 (consBan splitB195 (consBan splitB196 (consBan splitB197 (consBan splitB198 (nilBan 28 4)))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV200 : List ℕ := [0x10842100ffc00,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB200 : Ban 28 4 splitV200 := viaSmall (by decide +kernel) (by decide)

def splitV201 : List ℕ := [0x2108428007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB201 : Ban 28 4 splitV201 := viaSmall (by decide +kernel) (by decide)

def splitV202 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB202 : Ban 28 4 splitV202 := viaSmall (by decide +kernel) (by decide)

def splitV203 : List ℕ := [0x8421088007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB203 : Ban 28 4 splitV203 := viaSmall (by decide +kernel) (by decide)

def splitV204 : List ℕ := [0xc6318c00f8000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB204 : Ban 28 4 splitV204 := viaSmall (by decide +kernel) (by decide)

def splitV205 : List ℕ := [0x10842101f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB205 : Ban 28 4 splitV205 := viaSmall (by decide +kernel) (by decide)

def splitV206 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB206 : Ban 28 4 splitV206 := viaSmall (by decide +kernel) (by decide)

def splitV207 : List ℕ := [0x18c63188007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB207 : Ban 28 4 splitV207 := viaSmall (by decide +kernel) (by decide)

def splitV208 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x210842160f801f,0x42108427f0001f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB208 : Ban 28 4 splitV208 := viaSmall (by decide +kernel) (by decide)

def splitV209 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3084210600001f,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB209 : Ban 28 4 splitV209 := viaSmall (by decide +kernel) (by decide)

def splitV210 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x4000000600001f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB210 : Ban 28 4 splitV210 := viaSmall (by decide +kernel) (by decide)

def splitV211 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x4210842600001f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB211 : Ban 28 4 splitV211 := viaSmall (by decide +kernel) (by decide)

def splitV212 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x81084218007fe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB212 : Ban 28 4 splitV212 := viaSmall (by decide +kernel) (by decide)

def splitV213 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x85294a500f8000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB213 : Ban 28 4 splitV213 := viaSmall (by decide +kernel) (by decide)

def splitV214 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x8c6318c80003e0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB214 : Ban 28 4 splitV214 := viaSmall (by decide +kernel) (by decide)

def splitV215 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x9def7bd9ffffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB215 : Ban 28 4 splitV215 := viaSmall (by decide +kernel) (by decide)

def splitV216 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x9ffffff9ffffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB216 : Ban 28 4 splitV216 := viaSmall (by decide +kernel) (by decide)

def splitV217 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0xbdef7bde0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB217 : Ban 28 4 splitV217 := viaSmall (by decide +kernel) (by decide)

def splitV218 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0xcf7bdeffffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB218 : Ban 28 4 splitV218 := viaSmall (by decide +kernel) (by decide)

def splitV219 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x5ad6b5aff07fff,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB219 : Ban 28 4 splitV219 := viaSmall (by decide +kernel) (by decide)

def splitV220 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x5ef7bde7ff801f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB220 : Ban 28 4 splitV220 := viaSmall (by decide +kernel) (by decide)

def splitV221 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xcf7bdeffffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB221 : Ban 28 4 splitV221 := viaSmall (by decide +kernel) (by decide)

def splitV222 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3bdef7bfffffff,0x42108427f0001f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB222 : Ban 28 4 splitV222 := viaSmall (by decide +kernel) (by decide)

def splitV223 : List ℕ := [0x1ce739c1ff8000,0x1ef7bde9ffffe0,0x318c63160ffc1f,0x42108427f0001f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB223 : Ban 28 4 splitV223 := viaSmall (by decide +kernel) (by decide)

def splitV224 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x5ad6b5aff07fff,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB224 : Ban 28 4 splitV224 := viaSmall (by decide +kernel) (by decide)

def splitV225 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x85294a500f8000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB225 : Ban 28 4 splitV225 := viaSmall (by decide +kernel) (by decide)

def splitV226 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x85294a500f8000,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB226 : Ban 28 4 splitV226 := viaSmall (by decide +kernel) (by decide)

def splitV227 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x5ad6b5aff07fff,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB227 : Ban 28 4 splitV227 := viaSmall (by decide +kernel) (by decide)

def splitV228 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB228 : Ban 28 5 splitV228 := viaBranch (ws := [splitV145,splitV200,splitV201,splitV202,splitV203,splitV204,splitV205,splitV206,splitV207,splitV208,splitV209,splitV16,splitV210,splitV211,splitV212,splitV213,splitV214,splitV215,splitV216,splitV217,splitV218,splitV219,splitV220,splitV221,splitV222,splitV223,splitV224,splitV225,splitV226,splitV227])
 (consBan splitB145 (consBan splitB200 (consBan splitB201 (consBan splitB202 (consBan splitB203 (consBan splitB204 (consBan splitB205 (consBan splitB206 (consBan splitB207 (consBan splitB208 (consBan splitB209 (consBan splitB16 (consBan splitB210 (consBan splitB211 (consBan splitB212 (consBan splitB213 (consBan splitB214 (consBan splitB215 (consBan splitB216 (consBan splitB217 (consBan splitB218 (consBan splitB219 (consBan splitB220 (consBan splitB221 (consBan splitB222 (consBan splitB223 (consBan splitB224 (consBan splitB225 (consBan splitB226 (consBan splitB227 (nilBan 28 4)))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV229 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB229 : Ban 28 5 splitV229 := viaSmall (by decide +kernel) (by decide)

def splitV230 : List ℕ := [0x2108429f003e0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB230 : Ban 28 4 splitV230 := viaSmall (by decide +kernel) (by decide)

def splitV231 : List ℕ := [0x4210841f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB231 : Ban 28 4 splitV231 := viaSmall (by decide +kernel) (by decide)

def splitV232 : List ℕ := [0x18c63180007c00,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB232 : Ban 28 4 splitV232 := viaSmall (by decide +kernel) (by decide)

def splitV233 : List ℕ := [0x18c631800f8000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB233 : Ban 28 4 splitV233 := viaSmall (by decide +kernel) (by decide)

def splitV234 : List ℕ := [0x18c63188007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB234 : Ban 28 4 splitV234 := viaSmall (by decide +kernel) (by decide)

def splitV235 : List ℕ := [0x18c63188007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB235 : Ban 28 4 splitV235 := viaSmall (by decide +kernel) (by decide)

def splitV236 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x210842160f801f,0x42108427f0001f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB236 : Ban 28 4 splitV236 := viaSmall (by decide +kernel) (by decide)

def splitV237 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108421f00000,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB237 : Ban 28 4 splitV237 := viaSmall (by decide +kernel) (by decide)

def splitV238 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x4210842600001f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB238 : Ban 28 4 splitV238 := viaSmall (by decide +kernel) (by decide)

def splitV239 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x842108480003e0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB239 : Ban 28 4 splitV239 := viaSmall (by decide +kernel) (by decide)

def splitV240 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0xc210842e0003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB240 : Ban 28 4 splitV240 := viaSmall (by decide +kernel) (by decide)

def splitV241 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB241 : Ban 28 4 splitV241 := viaSmall (by decide +kernel) (by decide)

def splitV242 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0xc6318c69f003e0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB242 : Ban 28 4 splitV242 := viaSmall (by decide +kernel) (by decide)

def splitV243 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB243 : Ban 28 4 splitV243 := viaSmall (by decide +kernel) (by decide)

def splitV244 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB244 : Ban 28 4 splitV244 := viaSmall (by decide +kernel) (by decide)

def splitV245 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0xf7bdef7fffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB245 : Ban 28 4 splitV245 := viaSmall (by decide +kernel) (by decide)

def splitV246 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x5ef7bde7ff801f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB246 : Ban 28 4 splitV246 := viaSmall (by decide +kernel) (by decide)

def splitV247 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x739ce737fffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB247 : Ban 28 4 splitV247 := viaSmall (by decide +kernel) (by decide)

def splitV248 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x842108480003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB248 : Ban 28 4 splitV248 := viaSmall (by decide +kernel) (by decide)

def splitV249 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3bdef7bfffffff,0x42108427f0001f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB249 : Ban 28 4 splitV249 := viaSmall (by decide +kernel) (by decide)

def splitV250 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3def7bd7fffc1f,0x42108427f0001f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB250 : Ban 28 4 splitV250 := viaSmall (by decide +kernel) (by decide)

def splitV251 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x42108421f00000,0x42108427f0001f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB251 : Ban 28 4 splitV251 := viaSmall (by decide +kernel) (by decide)

def splitV252 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x42108421f00000,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB252 : Ban 28 4 splitV252 := viaSmall (by decide +kernel) (by decide)

def splitV253 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x42108427f0001f,0xc6318c69f003e0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB253 : Ban 28 4 splitV253 := viaSmall (by decide +kernel) (by decide)

def splitV254 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x42108427f0001f,0xc6318c69f003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB254 : Ban 28 4 splitV254 := viaSmall (by decide +kernel) (by decide)

def splitV255 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x5ad6b5aff07fff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB255 : Ban 28 4 splitV255 := viaSmall (by decide +kernel) (by decide)

def splitV256 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB256 : Ban 28 5 splitV256 := viaBranch (ws := [splitV172,splitV27,splitV89,splitV230,splitV231,splitV232,splitV233,splitV234,splitV235,splitV125,splitV236,splitV188,splitV237,splitV238,splitV239,splitV240,splitV241,splitV242,splitV243,splitV244,splitV245,splitV246,splitV247,splitV248,splitV249,splitV250,splitV251,splitV252,splitV253,splitV254,splitV255])
 (consBan splitB172 (consBan splitB27 (consBan splitB89 (consBan splitB230 (consBan splitB231 (consBan splitB232 (consBan splitB233 (consBan splitB234 (consBan splitB235 (consBan splitB125 (consBan splitB236 (consBan splitB188 (consBan splitB237 (consBan splitB238 (consBan splitB239 (consBan splitB240 (consBan splitB241 (consBan splitB242 (consBan splitB243 (consBan splitB244 (consBan splitB245 (consBan splitB246 (consBan splitB247 (consBan splitB248 (consBan splitB249 (consBan splitB250 (consBan splitB251 (consBan splitB252 (consBan splitB253 (consBan splitB254 (consBan splitB255 (nilBan 28 4))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV257 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x81084218007fe0,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB257 : Ban 28 5 splitV257 := viaSmall (by decide +kernel) (by decide)

def splitV258 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x81084218007fe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB258 : Ban 28 5 splitV258 := viaSmall (by decide +kernel) (by decide)

def splitV259 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x842108480003e0,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB259 : Ban 28 5 splitV259 := viaSmall (by decide +kernel) (by decide)

def splitV260 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x842108480003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB260 : Ban 28 5 splitV260 := viaSmall (by decide +kernel) (by decide)

def splitV261 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x85294a500f8000,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB261 : Ban 28 5 splitV261 := viaSmall (by decide +kernel) (by decide)

def splitV262 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8c6318c80003e0,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB262 : Ban 28 5 splitV262 := viaSmall (by decide +kernel) (by decide)

def splitV263 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8c6318c80003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB263 : Ban 28 4 splitV263 := viaSmall (by decide +kernel) (by decide)

def splitV264 : List ℕ := [0x10842101ff8000,0x1ad6b5a9f07fe0,0x318c63160ffc1f,0x8c6318c80003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB264 : Ban 28 4 splitV264 := viaSmall (by decide +kernel) (by decide)

def splitV265 : List ℕ := [0x1294a521f07c00,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB265 : Ban 28 4 splitV265 := viaSmall (by decide +kernel) (by decide)

def splitV266 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x21084216007c1f,0x8c6318c80003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB266 : Ban 28 4 splitV266 := viaSmall (by decide +kernel) (by decide)

def splitV267 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x210842160f801f,0x8c6318c80003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB267 : Ban 28 4 splitV267 := viaSmall (by decide +kernel) (by decide)

def splitV268 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB268 : Ban 28 4 splitV268 := viaSmall (by decide +kernel) (by decide)

def splitV269 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB269 : Ban 28 4 splitV269 := viaSmall (by decide +kernel) (by decide)

def splitV270 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x800000080003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB270 : Ban 28 4 splitV270 := viaSmall (by decide +kernel) (by decide)

def splitV271 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8c6318c80003e0,0xc210842e0003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB271 : Ban 28 4 splitV271 := viaSmall (by decide +kernel) (by decide)

def splitV272 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8c6318c80003e0,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB272 : Ban 28 4 splitV272 := viaSmall (by decide +kernel) (by decide)

def splitV273 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8c6318c80003e0,0xce739ceff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB273 : Ban 28 4 splitV273 := viaSmall (by decide +kernel) (by decide)

def splitV274 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8c6318c80003e0,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB274 : Ban 28 4 splitV274 := viaSmall (by decide +kernel) (by decide)

def splitV275 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8c6318c80003e0,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB275 : Ban 28 4 splitV275 := viaSmall (by decide +kernel) (by decide)

def splitV276 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x9ce739c9ff83e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB276 : Ban 28 4 splitV276 := viaSmall (by decide +kernel) (by decide)

def splitV277 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB277 : Ban 28 4 splitV277 := viaSmall (by decide +kernel) (by decide)

def splitV278 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3bdef7bfffffff,0x8c6318c80003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB278 : Ban 28 4 splitV278 := viaSmall (by decide +kernel) (by decide)

def splitV279 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3def7bd7fffc1f,0x8c6318c80003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB279 : Ban 28 4 splitV279 := viaSmall (by decide +kernel) (by decide)

def splitV280 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8c6318c80003e0,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB280 : Ban 28 4 splitV280 := viaSmall (by decide +kernel) (by decide)

def splitV281 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8c6318c80003e0,0xc6318c69f003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB281 : Ban 28 4 splitV281 := viaSmall (by decide +kernel) (by decide)

def splitV282 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB282 : Ban 28 4 splitV282 := viaSmall (by decide +kernel) (by decide)

def splitV283 : List ℕ := [0x1ad6b5a9f07fe0,0x318c63160ffc1f,0x8c6318c80003e0,0x9ce739c9ff83e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB283 : Ban 28 4 splitV283 := viaSmall (by decide +kernel) (by decide)

def splitV284 : List ℕ := [0x1ad6b5a9f07fe0,0x318c63160ffc1f,0x9ce739c9ff83e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB284 : Ban 28 4 splitV284 := viaSmall (by decide +kernel) (by decide)

def splitV285 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8c6318c80003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB285 : Ban 28 5 splitV285 := viaBranch (ws := [splitV7,splitV263,splitV53,splitV264,splitV265,splitV266,splitV267,splitV154,splitV268,splitV214,splitV269,splitV270,splitV248,splitV271,splitV272,splitV273,splitV274,splitV275,splitV276,splitV277,splitV278,splitV279,splitV280,splitV281,splitV282,splitV283,splitV284])
 (consBan splitB7 (consBan splitB263 (consBan splitB53 (consBan splitB264 (consBan splitB265 (consBan splitB266 (consBan splitB267 (consBan splitB154 (consBan splitB268 (consBan splitB214 (consBan splitB269 (consBan splitB270 (consBan splitB248 (consBan splitB271 (consBan splitB272 (consBan splitB273 (consBan splitB274 (consBan splitB275 (consBan splitB276 (consBan splitB277 (consBan splitB278 (consBan splitB279 (consBan splitB280 (consBan splitB281 (consBan splitB282 (consBan splitB283 (consBan splitB284 (nilBan 28 4))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV286 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0x9def7bd9ffffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB286 : Ban 28 5 splitV286 := viaSmall (by decide +kernel) (by decide)

def splitV287 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0x9ffffff9ffffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB287 : Ban 28 5 splitV287 := viaSmall (by decide +kernel) (by decide)

def splitV288 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB288 : Ban 28 5 splitV288 := viaSmall (by decide +kernel) (by decide)

def splitV289 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc210842e0003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB289 : Ban 28 5 splitV289 := viaSmall (by decide +kernel) (by decide)

def splitV290 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc210842e0003ff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB290 : Ban 28 5 splitV290 := viaSmall (by decide +kernel) (by decide)

def splitV291 : List ℕ := [0x2108428007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB291 : Ban 28 4 splitV291 := viaSmall (by decide +kernel) (by decide)

def splitV292 : List ℕ := [0x8421088007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB292 : Ban 28 4 splitV292 := viaSmall (by decide +kernel) (by decide)

def splitV293 : List ℕ := [0x94a52980fffe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB293 : Ban 28 4 splitV293 := viaSmall (by decide +kernel) (by decide)

def splitV294 : List ℕ := [0x10842100007c00,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB294 : Ban 28 4 splitV294 := viaSmall (by decide +kernel) (by decide)

def splitV295 : List ℕ := [0x18c63181ff8000,0x1ad6b5a9f07fe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB295 : Ban 28 4 splitV295 := viaSmall (by decide +kernel) (by decide)

def splitV296 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3084210600001f,0x8d6b5ad80fffe0,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB296 : Ban 28 4 splitV296 := viaSmall (by decide +kernel) (by decide)

def splitV297 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc000000600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB297 : Ban 28 4 splitV297 := viaSmall (by decide +kernel) (by decide)

def splitV298 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xcd6b5ade0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB298 : Ban 28 4 splitV298 := viaSmall (by decide +kernel) (by decide)

def splitV299 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdce739c7ff801f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB299 : Ban 28 4 splitV299 := viaSmall (by decide +kernel) (by decide)

def splitV300 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB300 : Ban 28 4 splitV300 := viaSmall (by decide +kernel) (by decide)

def splitV301 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xbdef7bde0fffff,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB301 : Ban 28 4 splitV301 := viaSmall (by decide +kernel) (by decide)

def splitV302 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc421084600001f,0xcd6b5ade0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB302 : Ban 28 4 splitV302 := viaSmall (by decide +kernel) (by decide)

def splitV303 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xbdef7bde0fffff,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB303 : Ban 28 4 splitV303 := viaSmall (by decide +kernel) (by decide)

def splitV304 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB304 : Ban 28 4 splitV304 := viaSmall (by decide +kernel) (by decide)

def splitV305 : List ℕ := [0x1ad6b5a9f07fe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc421084600001f,0xdce739c7ff801f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB305 : Ban 28 4 splitV305 := viaSmall (by decide +kernel) (by decide)

def splitV306 : List ℕ := [0x1ad6b5a9f07fe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdce739c7ff801f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB306 : Ban 28 4 splitV306 := viaSmall (by decide +kernel) (by decide)

def splitV307 : List ℕ := [0x1ce739c1ff8000,0x1ef7bde9ffffe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB307 : Ban 28 4 splitV307 := viaSmall (by decide +kernel) (by decide)

def splitV308 : List ℕ := [0x1ce739c1ff8000,0x210842160f801f,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB308 : Ban 28 4 splitV308 := viaSmall (by decide +kernel) (by decide)

def splitV309 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x85294a500f8000,0x8d6b5ad80fffe0,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB309 : Ban 28 4 splitV309 := viaSmall (by decide +kernel) (by decide)

def splitV310 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc421084600001f,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB310 : Ban 28 4 splitV310 := viaSmall (by decide +kernel) (by decide)

def splitV311 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB311 : Ban 28 5 splitV311 := viaBranch (ws := [splitV145,splitV291,splitV62,splitV292,splitV293,splitV294,splitV97,splitV295,splitV296,splitV16,splitV210,splitV272,splitV297,splitV298,splitV299,splitV300,splitV301,splitV302,splitV303,splitV304,splitV305,splitV306,splitV307,splitV308,splitV309,splitV310])
 (consBan splitB145 (consBan splitB291 (consBan splitB62 (consBan splitB292 (consBan splitB293 (consBan splitB294 (consBan splitB97 (consBan splitB295 (consBan splitB296 (consBan splitB16 (consBan splitB210 (consBan splitB272 (consBan splitB297 (consBan splitB298 (consBan splitB299 (consBan splitB300 (consBan splitB301 (consBan splitB302 (consBan splitB303 (consBan splitB304 (consBan splitB305 (consBan splitB306 (consBan splitB307 (consBan splitB308 (consBan splitB309 (consBan splitB310 (nilBan 28 4)))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV312 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc421084600001f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB312 : Ban 28 5 splitV312 := viaSmall (by decide +kernel) (by decide)

def splitV313 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c69f003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB313 : Ban 28 5 splitV313 := viaSmall (by decide +kernel) (by decide)

def splitV314 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff,0xcf7bdeffffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB314 : Ban 28 5 splitV314 := viaSmall (by decide +kernel) (by decide)

def splitV315 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB315 : Ban 28 5 splitV315 := viaSmall (by decide +kernel) (by decide)

def splitV316 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB316 : Ban 28 5 splitV316 := viaSmall (by decide +kernel) (by decide)

def splitV317 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff,0xf7bdef7fffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB317 : Ban 28 5 splitV317 := viaSmall (by decide +kernel) (by decide)

def splitV318 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xcf7bdeffffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB318 : Ban 28 5 splitV318 := viaSmall (by decide +kernel) (by decide)

def splitV319 : List ℕ := [0x2108428007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB319 : Ban 28 4 splitV319 := viaSmall (by decide +kernel) (by decide)

def splitV320 : List ℕ := [0x8421088007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB320 : Ban 28 4 splitV320 := viaSmall (by decide +kernel) (by decide)

def splitV321 : List ℕ := [0xa5294a9f003e0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB321 : Ban 28 4 splitV321 := viaSmall (by decide +kernel) (by decide)

def splitV322 : List ℕ := [0x10842106007c1f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB322 : Ban 28 4 splitV322 := viaSmall (by decide +kernel) (by decide)

def splitV323 : List ℕ := [0x10842106007c1f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB323 : Ban 28 4 splitV323 := viaSmall (by decide +kernel) (by decide)

def splitV324 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3084210600001f,0x8d6b5ad80fffe0,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB324 : Ban 28 4 splitV324 := viaSmall (by decide +kernel) (by decide)

def splitV325 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x5294a527f0001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB325 : Ban 28 4 splitV325 := viaSmall (by decide +kernel) (by decide)

def splitV326 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x5294a527f0001f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB326 : Ban 28 4 splitV326 := viaSmall (by decide +kernel) (by decide)

def splitV327 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x5294a527f0001f,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB327 : Ban 28 4 splitV327 := viaSmall (by decide +kernel) (by decide)

def splitV328 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8c6318c8007fe0,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB328 : Ban 28 4 splitV328 := viaSmall (by decide +kernel) (by decide)

def splitV329 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc210842e007fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB329 : Ban 28 4 splitV329 := viaSmall (by decide +kernel) (by decide)

def splitV330 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc421084600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB330 : Ban 28 4 splitV330 := viaSmall (by decide +kernel) (by decide)

def splitV331 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdef7bdefffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB331 : Ban 28 4 splitV331 := viaSmall (by decide +kernel) (by decide)

def splitV332 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdfffffffffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB332 : Ban 28 4 splitV332 := viaSmall (by decide +kernel) (by decide)

def splitV333 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xbdef7bde0fffff,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB333 : Ban 28 4 splitV333 := viaSmall (by decide +kernel) (by decide)

def splitV334 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xbdef7bde0fffff,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB334 : Ban 28 4 splitV334 := viaSmall (by decide +kernel) (by decide)

def splitV335 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xce739ce9f003e0,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB335 : Ban 28 4 splitV335 := viaSmall (by decide +kernel) (by decide)

def splitV336 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB336 : Ban 28 4 splitV336 := viaSmall (by decide +kernel) (by decide)

def splitV337 : List ℕ := [0x1ce739c1ff8000,0x1ef7bde9ffffe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB337 : Ban 28 4 splitV337 := viaSmall (by decide +kernel) (by decide)

def splitV338 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x3bdef7bfffffff,0x8d6b5ad80fffe0,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB338 : Ban 28 4 splitV338 := viaSmall (by decide +kernel) (by decide)

def splitV339 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x85294a500f8000,0x8d6b5ad80fffe0,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB339 : Ban 28 4 splitV339 := viaSmall (by decide +kernel) (by decide)

def splitV340 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB340 : Ban 28 5 splitV340 := viaBranch (ws := [splitV319,splitV65,splitV320,splitV321,splitV322,splitV323,splitV100,splitV149,splitV324,splitV325,splitV326,splitV327,splitV274,splitV328,splitV329,splitV330,splitV331,splitV332,splitV333,splitV334,splitV335,splitV336,splitV337,splitV338,splitV339,splitV310])
 (consBan splitB319 (consBan splitB65 (consBan splitB320 (consBan splitB321 (consBan splitB322 (consBan splitB323 (consBan splitB100 (consBan splitB149 (consBan splitB324 (consBan splitB325 (consBan splitB326 (consBan splitB327 (consBan splitB274 (consBan splitB328 (consBan splitB329 (consBan splitB330 (consBan splitB331 (consBan splitB332 (consBan splitB333 (consBan splitB334 (consBan splitB335 (consBan splitB336 (consBan splitB337 (consBan splitB338 (consBan splitB339 (consBan splitB310 (nilBan 28 4)))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV341 : List ℕ := [0x2108428007fe0,0x1ad6b5a9f07fe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB341 : Ban 28 4 splitV341 := viaSmall (by decide +kernel) (by decide)

def splitV342 : List ℕ := [0x2108428007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB342 : Ban 28 4 splitV342 := viaSmall (by decide +kernel) (by decide)

def splitV343 : List ℕ := [0x8421088007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB343 : Ban 28 4 splitV343 := viaSmall (by decide +kernel) (by decide)

def splitV344 : List ℕ := [0xc6318c1f00000,0x1ad6b5a9f07fe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB344 : Ban 28 4 splitV344 := viaSmall (by decide +kernel) (by decide)

def splitV345 : List ℕ := [0x108421060f801f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB345 : Ban 28 4 splitV345 := viaSmall (by decide +kernel) (by decide)

def splitV346 : List ℕ := [0x108421060f801f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB346 : Ban 28 4 splitV346 := viaSmall (by decide +kernel) (by decide)

def splitV347 : List ℕ := [0x108421060f801f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB347 : Ban 28 4 splitV347 := viaSmall (by decide +kernel) (by decide)

def splitV348 : List ℕ := [0x18c63181f00000,0x1ad6b5a9f07fe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB348 : Ban 28 4 splitV348 := viaSmall (by decide +kernel) (by decide)

def splitV349 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x5294a527f0001f,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB349 : Ban 28 4 splitV349 := viaSmall (by decide +kernel) (by decide)

def splitV350 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8c6318c80f83e0,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB350 : Ban 28 4 splitV350 := viaSmall (by decide +kernel) (by decide)

def splitV351 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc210842e0003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB351 : Ban 28 4 splitV351 := viaSmall (by decide +kernel) (by decide)

def splitV352 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc42108460f801f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB352 : Ban 28 4 splitV352 := viaSmall (by decide +kernel) (by decide)

def splitV353 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xbdef7bde0fffff,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB353 : Ban 28 4 splitV353 := viaSmall (by decide +kernel) (by decide)

def splitV354 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xce739ce9f003e0,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB354 : Ban 28 4 splitV354 := viaSmall (by decide +kernel) (by decide)

def splitV355 : List ℕ := [0x1ad6b5a9f07fe0,0x318c63160ffc1f,0x3def7bd7fffc1f,0x8d6b5ad80fffe0,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB355 : Ban 28 4 splitV355 := viaSmall (by decide +kernel) (by decide)

def splitV356 : List ℕ := [0x1ad6b5a9f07fe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc210842e0003ff,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB356 : Ban 28 4 splitV356 := viaSmall (by decide +kernel) (by decide)

def splitV357 : List ℕ := [0x1ce739c1ff8000,0x1ef7bde9ffffe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB357 : Ban 28 4 splitV357 := viaSmall (by decide +kernel) (by decide)

def splitV358 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x85294a500f8000,0x8d6b5ad80fffe0,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB358 : Ban 28 4 splitV358 := viaSmall (by decide +kernel) (by decide)

def splitV359 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB359 : Ban 28 5 splitV359 := viaBranch (ws := [splitV341,splitV342,splitV66,splitV343,splitV344,splitV345,splitV346,splitV347,splitV101,splitV348,splitV148,splitV325,splitV326,splitV349,splitV275,splitV350,splitV351,splitV352,splitV331,splitV332,splitV353,splitV354,splitV355,splitV356,splitV357,splitV358])
 (consBan splitB341 (consBan splitB342 (consBan splitB66 (consBan splitB343 (consBan splitB344 (consBan splitB345 (consBan splitB346 (consBan splitB347 (consBan splitB101 (consBan splitB348 (consBan splitB148 (consBan splitB325 (consBan splitB326 (consBan splitB349 (consBan splitB275 (consBan splitB350 (consBan splitB351 (consBan splitB352 (consBan splitB331 (consBan splitB332 (consBan splitB353 (consBan splitB354 (consBan splitB355 (consBan splitB356 (consBan splitB357 (consBan splitB358 (nilBan 28 4)))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV360 : List ℕ := [0x108421000f8000,0x1ad6b5a9f07fe0,0x318c63160ffc1f,0x9def7bd9ffffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB360 : Ban 28 4 splitV360 := viaSmall (by decide +kernel) (by decide)

def splitV361 : List ℕ := [0x18c631800f8000,0x1ad6b5a9f07fe0,0x318c63160ffc1f,0x9def7bd9ffffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB361 : Ban 28 4 splitV361 := viaSmall (by decide +kernel) (by decide)

def splitV362 : List ℕ := [0x18c63189f07fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB362 : Ban 28 4 splitV362 := viaSmall (by decide +kernel) (by decide)

def splitV363 : List ℕ := [0x18c63189f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x9def7bd9ffffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB363 : Ban 28 4 splitV363 := viaSmall (by decide +kernel) (by decide)

def splitV364 : List ℕ := [0x18c63189f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB364 : Ban 28 4 splitV364 := viaSmall (by decide +kernel) (by decide)

def splitV365 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x2000000600001f,0x9def7bd9ffffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB365 : Ban 28 4 splitV365 := viaSmall (by decide +kernel) (by decide)

def splitV366 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x210842160f801f,0x9def7bd9ffffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB366 : Ban 28 4 splitV366 := viaSmall (by decide +kernel) (by decide)

def splitV367 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x81084218007fe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB367 : Ban 28 4 splitV367 := viaSmall (by decide +kernel) (by decide)

def splitV368 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x84210849f003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB368 : Ban 28 4 splitV368 := viaSmall (by decide +kernel) (by decide)

def splitV369 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8c6318c9f003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB369 : Ban 28 4 splitV369 := viaSmall (by decide +kernel) (by decide)

def splitV370 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xbdef7bdfffffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB370 : Ban 28 4 splitV370 := viaSmall (by decide +kernel) (by decide)

def splitV371 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3bdef7bfffffff,0x9def7bd9ffffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB371 : Ban 28 4 splitV371 := viaSmall (by decide +kernel) (by decide)

def splitV372 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3def7bd7fffc1f,0x9def7bd9ffffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB372 : Ban 28 4 splitV372 := viaSmall (by decide +kernel) (by decide)

def splitV373 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x9def7bd9ffffe0,0xbdef7bdfffffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB373 : Ban 28 4 splitV373 := viaSmall (by decide +kernel) (by decide)

def splitV374 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x9def7bd9ffffe0,0xc6318c69f003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB374 : Ban 28 4 splitV374 := viaSmall (by decide +kernel) (by decide)

def splitV375 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bdfffffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB375 : Ban 28 4 splitV375 := viaSmall (by decide +kernel) (by decide)

def splitV376 : List ℕ := [0x1ad6b5a9f07fe0,0x21084216007c1f,0x318c63160ffc1f,0x9def7bd9ffffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB376 : Ban 28 4 splitV376 := viaSmall (by decide +kernel) (by decide)

def splitV377 : List ℕ := [0x1ad6b5a9f07fe0,0x318c63160ffc1f,0x81084218007fe0,0x9def7bd9ffffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB377 : Ban 28 4 splitV377 := viaSmall (by decide +kernel) (by decide)

def splitV378 : List ℕ := [0x1ad6b5a9f07fe0,0x318c63160ffc1f,0x9def7bd9ffffe0,0xc6318c6ff003ff,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB378 : Ban 28 4 splitV378 := viaSmall (by decide +kernel) (by decide)

def splitV379 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x85294a500f8000,0x9def7bd9ffffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB379 : Ban 28 4 splitV379 := viaSmall (by decide +kernel) (by decide)

def splitV380 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x9def7bd9ffffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB380 : Ban 28 5 splitV380 := viaBranch (ws := [splitV32,splitV88,splitV360,splitV361,splitV362,splitV363,splitV364,splitV365,splitV129,splitV366,splitV238,splitV367,splitV368,splitV369,splitV370,splitV371,splitV372,splitV373,splitV374,splitV375,splitV376,splitV138,splitV377,splitV378,splitV379])
 (consBan splitB32 (consBan splitB88 (consBan splitB360 (consBan splitB361 (consBan splitB362 (consBan splitB363 (consBan splitB364 (consBan splitB365 (consBan splitB129 (consBan splitB366 (consBan splitB238 (consBan splitB367 (consBan splitB368 (consBan splitB369 (consBan splitB370 (consBan splitB371 (consBan splitB372 (consBan splitB373 (consBan splitB374 (consBan splitB375 (consBan splitB376 (consBan splitB138 (consBan splitB377 (consBan splitB378 (consBan splitB379 (nilBan 28 4))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV381 : List ℕ := [0x600001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB381 : Ban 28 4 splitV381 := viaSmall (by decide +kernel) (by decide)

def splitV382 : List ℕ := [0xa5294a9f003e0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB382 : Ban 28 4 splitV382 := viaSmall (by decide +kernel) (by decide)

def splitV383 : List ℕ := [0xc6318c1f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB383 : Ban 28 4 splitV383 := viaSmall (by decide +kernel) (by decide)

def splitV384 : List ℕ := [0x10842100007c00,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB384 : Ban 28 4 splitV384 := viaSmall (by decide +kernel) (by decide)

def splitV385 : List ℕ := [0x108421000f8000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB385 : Ban 28 4 splitV385 := viaSmall (by decide +kernel) (by decide)

def splitV386 : List ℕ := [0x18c63188007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB386 : Ban 28 4 splitV386 := viaSmall (by decide +kernel) (by decide)

def splitV387 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x21084216007c1f,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB387 : Ban 28 4 splitV387 := viaSmall (by decide +kernel) (by decide)

def splitV388 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x210842160f801f,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB388 : Ban 28 4 splitV388 := viaSmall (by decide +kernel) (by decide)

def splitV389 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63100ffc00,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB389 : Ban 28 4 splitV389 := viaSmall (by decide +kernel) (by decide)

def splitV390 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x39ce73900ffc00,0xbdef7bde0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB390 : Ban 28 4 splitV390 := viaSmall (by decide +kernel) (by decide)

def splitV391 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8421084e0003ff,0xbdef7bde0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB391 : Ban 28 4 splitV391 := viaSmall (by decide +kernel) (by decide)

def splitV392 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8421084e0003ff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB392 : Ban 28 4 splitV392 := viaSmall (by decide +kernel) (by decide)

def splitV393 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8c6318c80003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB393 : Ban 28 4 splitV393 := viaSmall (by decide +kernel) (by decide)

def splitV394 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xa108421e007fff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB394 : Ban 28 4 splitV394 := viaSmall (by decide +kernel) (by decide)

def splitV395 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xbdef7bde0fffff,0xc210842e0003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB395 : Ban 28 4 splitV395 := viaSmall (by decide +kernel) (by decide)

def splitV396 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3bdef7bfffffff,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB396 : Ban 28 4 splitV396 := viaSmall (by decide +kernel) (by decide)

def splitV397 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3def7bd7fffc1f,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB397 : Ban 28 4 splitV397 := viaSmall (by decide +kernel) (by decide)

def splitV398 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c69f003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB398 : Ban 28 4 splitV398 := viaSmall (by decide +kernel) (by decide)

def splitV399 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff,0xf7bdef7fffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB399 : Ban 28 4 splitV399 := viaSmall (by decide +kernel) (by decide)

def splitV400 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0xa5294a560f801f,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB400 : Ban 28 4 splitV400 := viaSmall (by decide +kernel) (by decide)

def splitV401 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB401 : Ban 28 5 splitV401 := viaBranch (ws := [splitV9,splitV381,splitV89,splitV382,splitV383,splitV384,splitV385,splitV234,splitV386,splitV387,splitV388,splitV156,splitV160,splitV389,splitV390,splitV237,splitV391,splitV392,splitV393,splitV394,splitV395,splitV301,splitV333,splitV353,splitV370,splitV396,splitV397,splitV280,splitV398,splitV399,splitV400])
 (consBan splitB9 (consBan splitB381 (consBan splitB89 (consBan splitB382 (consBan splitB383 (consBan splitB384 (consBan splitB385 (consBan splitB234 (consBan splitB386 (consBan splitB387 (consBan splitB388 (consBan splitB156 (consBan splitB160 (consBan splitB389 (consBan splitB390 (consBan splitB237 (consBan splitB391 (consBan splitB392 (consBan splitB393 (consBan splitB394 (consBan splitB395 (consBan splitB301 (consBan splitB333 (consBan splitB353 (consBan splitB370 (consBan splitB396 (consBan splitB397 (consBan splitB280 (consBan splitB398 (consBan splitB399 (consBan splitB400 (nilBan 28 4))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV402 : List ℕ := [0x210842ff003ff,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3bdef7bfffffff,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB402 : Ban 28 4 splitV402 := viaSmall (by decide +kernel) (by decide)

def splitV403 : List ℕ := [0x210842ff003ff,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB403 : Ban 28 4 splitV403 := viaSmall (by decide +kernel) (by decide)

def splitV404 : List ℕ := [0x94a52980fffe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3bdef7bfffffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB404 : Ban 28 4 splitV404 := viaSmall (by decide +kernel) (by decide)

def splitV405 : List ℕ := [0x18c63181ff8000,0x1ad6b5a9f07fe0,0x3bdef7bfffffff,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB405 : Ban 28 4 splitV405 := viaSmall (by decide +kernel) (by decide)

def splitV406 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x210842160f801f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB406 : Ban 28 4 splitV406 := viaSmall (by decide +kernel) (by decide)

def splitV407 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x2318c63e007fff,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB407 : Ban 28 4 splitV407 := viaSmall (by decide +kernel) (by decide)

def splitV408 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3294a527f0001f,0x3bdef7bfffffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB408 : Ban 28 4 splitV408 := viaSmall (by decide +kernel) (by decide)

def splitV409 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3294a527f0001f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB409 : Ban 28 4 splitV409 := viaSmall (by decide +kernel) (by decide)

def splitV410 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3294a527f0001f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB410 : Ban 28 4 splitV410 := viaSmall (by decide +kernel) (by decide)

def splitV411 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x39ce73900ffc00,0x3bdef7bfffffff,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB411 : Ban 28 4 splitV411 := viaSmall (by decide +kernel) (by decide)

def splitV412 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3bdef7bfffffff,0x81084218007fe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB412 : Ban 28 4 splitV412 := viaSmall (by decide +kernel) (by decide)

def splitV413 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3bdef7bfffffff,0x842108480003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB413 : Ban 28 4 splitV413 := viaSmall (by decide +kernel) (by decide)

def splitV414 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3bdef7bfffffff,0x8d6b5ad80fffe0,0xcf7bdeffffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB414 : Ban 28 4 splitV414 := viaSmall (by decide +kernel) (by decide)

def splitV415 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3fffffffffffff,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB415 : Ban 28 4 splitV415 := viaSmall (by decide +kernel) (by decide)

def splitV416 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xbfffffffffffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB416 : Ban 28 4 splitV416 := viaSmall (by decide +kernel) (by decide)

def splitV417 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc4210840000000,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB417 : Ban 28 4 splitV417 := viaSmall (by decide +kernel) (by decide)

def splitV418 : List ℕ := [0x1ad6b5a9f07fe0,0x2318c63e007fff,0x3bdef7bfffffff,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB418 : Ban 28 4 splitV418 := viaSmall (by decide +kernel) (by decide)

def splitV419 : List ℕ := [0x1ad6b5a9f07fe0,0x2318c63e007fff,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB419 : Ban 28 4 splitV419 := viaSmall (by decide +kernel) (by decide)

def splitV420 : List ℕ := [0x1ce739c1ff8000,0x210842160f801f,0x3bdef7bfffffff,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB420 : Ban 28 4 splitV420 := viaSmall (by decide +kernel) (by decide)

def splitV421 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3bdef7bfffffff,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB421 : Ban 28 5 splitV421 := viaBranch (ws := [splitV402,splitV403,splitV68,splitV404,splitV103,splitV405,splitV406,splitV407,splitV408,splitV409,splitV410,splitV411,splitV197,splitV222,splitV249,splitV412,splitV413,splitV414,splitV371,splitV415,splitV416,splitV417,splitV418,splitV419,splitV420])
 (consBan splitB402 (consBan splitB403 (consBan splitB68 (consBan splitB404 (consBan splitB103 (consBan splitB405 (consBan splitB406 (consBan splitB407 (consBan splitB408 (consBan splitB409 (consBan splitB410 (consBan splitB411 (consBan splitB197 (consBan splitB222 (consBan splitB249 (consBan splitB412 (consBan splitB413 (consBan splitB414 (consBan splitB371 (consBan splitB415 (consBan splitB416 (consBan splitB417 (consBan splitB418 (consBan splitB419 (consBan splitB420 (nilBan 28 4))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV422 : List ℕ := [0x4210847f0001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3def7bd7fffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB422 : Ban 28 4 splitV422 := viaSmall (by decide +kernel) (by decide)

def splitV423 : List ℕ := [0x4210847f0001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB423 : Ban 28 4 splitV423 := viaSmall (by decide +kernel) (by decide)

def splitV424 : List ℕ := [0x4210847f0001f,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB424 : Ban 28 4 splitV424 := viaSmall (by decide +kernel) (by decide)

def splitV425 : List ℕ := [0x8421088007fe0,0x1ce739c1ff8000,0x3def7bd7fffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB425 : Ban 28 4 splitV425 := viaSmall (by decide +kernel) (by decide)

def splitV426 : List ℕ := [0xc6318c00f8000,0x1ad6b5a9f07fe0,0x3def7bd7fffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB426 : Ban 28 4 splitV426 := viaSmall (by decide +kernel) (by decide)

def splitV427 : List ℕ := [0x18c631800f8000,0x1ad6b5a9f07fe0,0x3def7bd7fffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB427 : Ban 28 4 splitV427 := viaSmall (by decide +kernel) (by decide)

def splitV428 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x21084216007c1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB428 : Ban 28 4 splitV428 := viaSmall (by decide +kernel) (by decide)

def splitV429 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x25294a560f801f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB429 : Ban 28 4 splitV429 := viaSmall (by decide +kernel) (by decide)

def splitV430 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x30842107f0001f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB430 : Ban 28 4 splitV430 := viaSmall (by decide +kernel) (by decide)

def splitV431 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x39ce73900ffc00,0x3def7bd7fffc1f,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB431 : Ban 28 4 splitV431 := viaSmall (by decide +kernel) (by decide)

def splitV432 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3def7bd7fffc1f,0x800000080003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB432 : Ban 28 4 splitV432 := viaSmall (by decide +kernel) (by decide)

def splitV433 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3def7bd7fffc1f,0x81084218007fe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB433 : Ban 28 4 splitV433 := viaSmall (by decide +kernel) (by decide)

def splitV434 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3def7bd7fffc1f,0x842108480003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB434 : Ban 28 4 splitV434 := viaSmall (by decide +kernel) (by decide)

def splitV435 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3def7bd7fffc1f,0xbdef7bdfffffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB435 : Ban 28 4 splitV435 := viaSmall (by decide +kernel) (by decide)

def splitV436 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xbdef7bdfffffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB436 : Ban 28 4 splitV436 := viaSmall (by decide +kernel) (by decide)

def splitV437 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc21084280003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB437 : Ban 28 4 splitV437 := viaSmall (by decide +kernel) (by decide)

def splitV438 : List ℕ := [0x1ad6b5a9f07fe0,0x3def7bd7fffc1f,0x81084218007fe0,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB438 : Ban 28 4 splitV438 := viaSmall (by decide +kernel) (by decide)

def splitV439 : List ℕ := [0x1ad6b5a9f07fe0,0x3def7bd7fffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB439 : Ban 28 4 splitV439 := viaSmall (by decide +kernel) (by decide)

def splitV440 : List ℕ := [0x1ce739c1ff8000,0x3def7bd7fffc1f,0x85294a500f8000,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB440 : Ban 28 4 splitV440 := viaSmall (by decide +kernel) (by decide)

def splitV441 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3def7bd7fffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB441 : Ban 28 5 splitV441 := viaBranch (ws := [splitV422,splitV423,splitV424,splitV69,splitV425,splitV426,splitV104,splitV427,splitV428,splitV429,splitV430,splitV431,splitV250,splitV432,splitV433,splitV434,splitV372,splitV435,splitV415,splitV436,splitV437,splitV375,splitV135,splitV438,splitV439,splitV440])
 (consBan splitB422 (consBan splitB423 (consBan splitB424 (consBan splitB69 (consBan splitB425 (consBan splitB426 (consBan splitB104 (consBan splitB427 (consBan splitB428 (consBan splitB429 (consBan splitB430 (consBan splitB431 (consBan splitB250 (consBan splitB432 (consBan splitB433 (consBan splitB434 (consBan splitB372 (consBan splitB435 (consBan splitB415 (consBan splitB436 (consBan splitB437 (consBan splitB375 (consBan splitB135 (consBan splitB438 (consBan splitB439 (consBan splitB440 (nilBan 28 4)))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV442 : List ℕ := [0x8421088007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB442 : Ban 28 4 splitV442 := viaSmall (by decide +kernel) (by decide)

def splitV443 : List ℕ := [0x8421088007fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB443 : Ban 28 4 splitV443 := viaSmall (by decide +kernel) (by decide)

def splitV444 : List ℕ := [0x94a52900ffc00,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB444 : Ban 28 4 splitV444 := viaSmall (by decide +kernel) (by decide)

def splitV445 : List ℕ := [0xc6318c00f8000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB445 : Ban 28 4 splitV445 := viaSmall (by decide +kernel) (by decide)

def splitV446 : List ℕ := [0x10842101f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB446 : Ban 28 4 splitV446 := viaSmall (by decide +kernel) (by decide)

def splitV447 : List ℕ := [0x1294a521f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB447 : Ban 28 4 splitV447 := viaSmall (by decide +kernel) (by decide)

def splitV448 : List ℕ := [0x18c63188007fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB448 : Ban 28 4 splitV448 := viaSmall (by decide +kernel) (by decide)

def splitV449 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3084210600001f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB449 : Ban 28 4 splitV449 := viaSmall (by decide +kernel) (by decide)

def splitV450 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x3084210600001f,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB450 : Ban 28 4 splitV450 := viaSmall (by decide +kernel) (by decide)

def splitV451 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x39ce73900ffc00,0x8d6b5ad80fffe0,0xbdef7bde0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB451 : Ban 28 4 splitV451 := viaSmall (by decide +kernel) (by decide)

def splitV452 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x42108421f00000,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB452 : Ban 28 4 splitV452 := viaSmall (by decide +kernel) (by decide)

def splitV453 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x42108427f0001f,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB453 : Ban 28 4 splitV453 := viaSmall (by decide +kernel) (by decide)

def splitV454 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x81084218007fe0,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB454 : Ban 28 4 splitV454 := viaSmall (by decide +kernel) (by decide)

def splitV455 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x842108480003e0,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB455 : Ban 28 4 splitV455 := viaSmall (by decide +kernel) (by decide)

def splitV456 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8421084e0003ff,0x8d6b5ad80fffe0,0xbdef7bde0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB456 : Ban 28 4 splitV456 := viaSmall (by decide +kernel) (by decide)

def splitV457 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8421084e0003ff,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB457 : Ban 28 4 splitV457 := viaSmall (by decide +kernel) (by decide)

def splitV458 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x85294a500f8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB458 : Ban 28 4 splitV458 := viaSmall (by decide +kernel) (by decide)

def splitV459 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xa108421e007fff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB459 : Ban 28 4 splitV459 := viaSmall (by decide +kernel) (by decide)

def splitV460 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xa5294a560f801f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB460 : Ban 28 4 splitV460 := viaSmall (by decide +kernel) (by decide)

def splitV461 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x9def7bd9ffffe0,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB461 : Ban 28 4 splitV461 := viaSmall (by decide +kernel) (by decide)

def splitV462 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x9ffffff9ffffe0,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB462 : Ban 28 4 splitV462 := viaSmall (by decide +kernel) (by decide)

def splitV463 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff,0xcf7bdeffffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB463 : Ban 28 4 splitV463 := viaSmall (by decide +kernel) (by decide)

def splitV464 : List ℕ := [0x1ce739c1ff8000,0x85294a500f8000,0x8d6b5ad80fffe0,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB464 : Ban 28 4 splitV464 := viaSmall (by decide +kernel) (by decide)

def splitV465 : List ℕ := [0x1ce739c1ff8000,0x85294a500f8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB465 : Ban 28 4 splitV465 := viaSmall (by decide +kernel) (by decide)

def splitV466 : List ℕ := [0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xa5294a560f801f,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB466 : Ban 28 4 splitV466 := viaSmall (by decide +kernel) (by decide)

def splitV467 : List ℕ := [0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xa5294a560f801f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB467 : Ban 28 4 splitV467 := viaSmall (by decide +kernel) (by decide)

def splitV468 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB468 : Ban 28 5 splitV468 := viaBranch (ws := [splitV442,splitV443,splitV444,splitV445,splitV446,splitV447,splitV448,splitV449,splitV450,splitV451,splitV452,splitV453,splitV454,splitV455,splitV456,splitV457,splitV458,splitV459,splitV460,splitV303,splitV334,splitV436,splitV416,splitV461,splitV462,splitV463,splitV464,splitV465,splitV466,splitV467])
 (consBan splitB442 (consBan splitB443 (consBan splitB444 (consBan splitB445 (consBan splitB446 (consBan splitB447 (consBan splitB448 (consBan splitB449 (consBan splitB450 (consBan splitB451 (consBan splitB452 (consBan splitB453 (consBan splitB454 (consBan splitB455 (consBan splitB456 (consBan splitB457 (consBan splitB458 (consBan splitB459 (consBan splitB460 (consBan splitB303 (consBan splitB334 (consBan splitB436 (consBan splitB416 (consBan splitB461 (consBan splitB462 (consBan splitB463 (consBan splitB464 (consBan splitB465 (consBan splitB466 (consBan splitB467 (nilBan 28 4)))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV469 : List ℕ := [0x8421088007fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc6318c69f003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB469 : Ban 28 4 splitV469 := viaSmall (by decide +kernel) (by decide)

def splitV470 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x42108421f00000,0xc6318c69f003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB470 : Ban 28 4 splitV470 := viaSmall (by decide +kernel) (by decide)

def splitV471 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x42108427f0001f,0x8d6b5ad80fffe0,0xc6318c69f003e0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB471 : Ban 28 4 splitV471 := viaSmall (by decide +kernel) (by decide)

def splitV472 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x81084218007fe0,0xc6318c69f003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB472 : Ban 28 4 splitV472 := viaSmall (by decide +kernel) (by decide)

def splitV473 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x842108480003e0,0xc6318c69f003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB473 : Ban 28 4 splitV473 := viaSmall (by decide +kernel) (by decide)

def splitV474 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc210842e0003ff,0xc6318c69f003e0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB474 : Ban 28 4 splitV474 := viaSmall (by decide +kernel) (by decide)

def splitV475 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc421084600001f,0xc6318c69f003e0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB475 : Ban 28 4 splitV475 := viaSmall (by decide +kernel) (by decide)

def splitV476 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc6318c69f003e0,0xcf7bdeffffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB476 : Ban 28 4 splitV476 := viaSmall (by decide +kernel) (by decide)

def splitV477 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc6318c69f003e0,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB477 : Ban 28 4 splitV477 := viaSmall (by decide +kernel) (by decide)

def splitV478 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc6318c69f003e0,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB478 : Ban 28 4 splitV478 := viaSmall (by decide +kernel) (by decide)

def splitV479 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc6318c6ff003ff,0xcf7bdef9ffffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB479 : Ban 28 4 splitV479 := viaSmall (by decide +kernel) (by decide)

def splitV480 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc6318c6ff003ff,0xdef7bde9f07fe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB480 : Ban 28 4 splitV480 := viaSmall (by decide +kernel) (by decide)

def splitV481 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc6318c6ff003ff,0xdef7bde9ff83e0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB481 : Ban 28 4 splitV481 := viaSmall (by decide +kernel) (by decide)

def splitV482 : List ℕ := [0x1ce739c1ff8000,0x85294a500f8000,0x8d6b5ad80fffe0,0xc6318c69f003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB482 : Ban 28 4 splitV482 := viaSmall (by decide +kernel) (by decide)

def splitV483 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8d6b5ad80fffe0,0xc6318c69f003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB483 : Ban 28 5 splitV483 := viaBranch (ws := [splitV30,splitV117,splitV70,splitV469,splitV105,splitV452,splitV470,splitV252,splitV471,splitV253,splitV254,splitV472,splitV473,splitV437,splitV474,splitV417,splitV475,splitV476,splitV477,splitV478,splitV479,splitV480,splitV481,splitV374,splitV482])
 (consBan splitB30 (consBan splitB117 (consBan splitB70 (consBan splitB469 (consBan splitB105 (consBan splitB452 (consBan splitB470 (consBan splitB252 (consBan splitB471 (consBan splitB253 (consBan splitB254 (consBan splitB472 (consBan splitB473 (consBan splitB437 (consBan splitB474 (consBan splitB417 (consBan splitB475 (consBan splitB476 (consBan splitB477 (consBan splitB478 (consBan splitB479 (consBan splitB480 (consBan splitB481 (consBan splitB374 (consBan splitB482 (nilBan 28 4))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV484 : List ℕ := [0x1f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB484 : Ban 28 4 splitV484 := viaSmall (by decide +kernel) (by decide)

def splitV485 : List ℕ := [0x2108421f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB485 : Ban 28 4 splitV485 := viaSmall (by decide +kernel) (by decide)

def splitV486 : List ℕ := [0x2108428007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB486 : Ban 28 4 splitV486 := viaSmall (by decide +kernel) (by decide)

def splitV487 : List ℕ := [0x2108429f003e0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB487 : Ban 28 4 splitV487 := viaSmall (by decide +kernel) (by decide)

def splitV488 : List ℕ := [0x42108400f8000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB488 : Ban 28 4 splitV488 := viaSmall (by decide +kernel) (by decide)

def splitV489 : List ℕ := [0x4210841f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB489 : Ban 28 4 splitV489 := viaSmall (by decide +kernel) (by decide)

def splitV490 : List ℕ := [0x18c63180007c00,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB490 : Ban 28 4 splitV490 := viaSmall (by decide +kernel) (by decide)

def splitV491 : List ℕ := [0x18c631800f8000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB491 : Ban 28 4 splitV491 := viaSmall (by decide +kernel) (by decide)

def splitV492 : List ℕ := [0x18c63181f00000,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB492 : Ban 28 4 splitV492 := viaSmall (by decide +kernel) (by decide)

def splitV493 : List ℕ := [0x18c63188007fe0,0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB493 : Ban 28 4 splitV493 := viaSmall (by decide +kernel) (by decide)

def splitV494 : List ℕ := [0x18c63188007fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB494 : Ban 28 4 splitV494 := viaSmall (by decide +kernel) (by decide)

def splitV495 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c00f8000,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB495 : Ban 28 4 splitV495 := viaSmall (by decide +kernel) (by decide)

def splitV496 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x1ef7bde9ffffe0,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB496 : Ban 28 4 splitV496 := viaSmall (by decide +kernel) (by decide)

def splitV497 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x39ce73900ffc00,0xbdef7bde0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB497 : Ban 28 4 splitV497 := viaSmall (by decide +kernel) (by decide)

def splitV498 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x39ce73900ffc00,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB498 : Ban 28 4 splitV498 := viaSmall (by decide +kernel) (by decide)

def splitV499 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x42108421f00000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB499 : Ban 28 4 splitV499 := viaSmall (by decide +kernel) (by decide)

def splitV500 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8421084e0003ff,0xbdef7bde0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB500 : Ban 28 4 splitV500 := viaSmall (by decide +kernel) (by decide)

def splitV501 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8421084e0003ff,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB501 : Ban 28 4 splitV501 := viaSmall (by decide +kernel) (by decide)

def splitV502 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x8421084e0003ff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB502 : Ban 28 4 splitV502 := viaSmall (by decide +kernel) (by decide)

def splitV503 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xa108421e007fff,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB503 : Ban 28 4 splitV503 := viaSmall (by decide +kernel) (by decide)

def splitV504 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xa108421e007fff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB504 : Ban 28 4 splitV504 := viaSmall (by decide +kernel) (by decide)

def splitV505 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xa5294a560f801f,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB505 : Ban 28 4 splitV505 := viaSmall (by decide +kernel) (by decide)

def splitV506 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xbdef7bdfffffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB506 : Ban 28 4 splitV506 := viaSmall (by decide +kernel) (by decide)

def splitV507 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xbfffffffffffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB507 : Ban 28 4 splitV507 := viaSmall (by decide +kernel) (by decide)

def splitV508 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc210842e0003ff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB508 : Ban 28 4 splitV508 := viaSmall (by decide +kernel) (by decide)

def splitV509 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc421084600001f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB509 : Ban 28 4 splitV509 := viaSmall (by decide +kernel) (by decide)

def splitV510 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff,0xdef7bdeff07fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB510 : Ban 28 4 splitV510 := viaSmall (by decide +kernel) (by decide)

def splitV511 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff,0xdef7bdefff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB511 : Ban 28 4 splitV511 := viaSmall (by decide +kernel) (by decide)

def splitV512 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff,0xffffffffffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB512 : Ban 28 4 splitV512 := viaSmall (by decide +kernel) (by decide)

def splitV513 : List ℕ := [0x1ce739c1ff8000,0xa5294a560f801f,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB513 : Ban 28 4 splitV513 := viaSmall (by decide +kernel) (by decide)

def splitV514 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB514 : Ban 28 5 splitV514 := viaBranch (ws := [splitV484,splitV485,splitV486,splitV487,splitV488,splitV489,splitV490,splitV491,splitV492,splitV493,splitV494,splitV495,splitV496,splitV497,splitV498,splitV499,splitV252,splitV500,splitV501,splitV502,splitV503,splitV504,splitV505,splitV506,splitV507,splitV508,splitV304,splitV509,splitV510,splitV511,splitV512,splitV336,splitV375,splitV513])
 (consBan splitB484 (consBan splitB485 (consBan splitB486 (consBan splitB487 (consBan splitB488 (consBan splitB489 (consBan splitB490 (consBan splitB491 (consBan splitB492 (consBan splitB493 (consBan splitB494 (consBan splitB495 (consBan splitB496 (consBan splitB497 (consBan splitB498 (consBan splitB499 (consBan splitB252 (consBan splitB500 (consBan splitB501 (consBan splitB502 (consBan splitB503 (consBan splitB504 (consBan splitB505 (consBan splitB506 (consBan splitB507 (consBan splitB508 (consBan splitB304 (consBan splitB509 (consBan splitB510 (consBan splitB511 (consBan splitB512 (consBan splitB336 (consBan splitB375 (consBan splitB513 (nilBan 28 4)))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV515 : List ℕ := [0x2108428007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB515 : Ban 28 4 splitV515 := viaSmall (by decide +kernel) (by decide)

def splitV516 : List ℕ := [0x2108428007fe0,0x1ef7bde9ffffe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB516 : Ban 28 4 splitV516 := viaSmall (by decide +kernel) (by decide)

def splitV517 : List ℕ := [0x4210841f00000,0x1ef7bde9ffffe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB517 : Ban 28 4 splitV517 := viaSmall (by decide +kernel) (by decide)

def splitV518 : List ℕ := [0xc6318c1f00000,0x1ef7bde9ffffe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB518 : Ban 28 4 splitV518 := viaSmall (by decide +kernel) (by decide)

def splitV519 : List ℕ := [0xc6318c80fffe0,0x1ce739c1ff8000,0x1ef7bde9ffffe0,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB519 : Ban 28 4 splitV519 := viaSmall (by decide +kernel) (by decide)

def splitV520 : List ℕ := [0xc6318c80fffe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB520 : Ban 28 4 splitV520 := viaSmall (by decide +kernel) (by decide)

def splitV521 : List ℕ := [0xc6318c80fffe0,0x1ce739c1ff8000,0x318c63160ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB521 : Ban 28 4 splitV521 := viaSmall (by decide +kernel) (by decide)

def splitV522 : List ℕ := [0x1ce739c1ff8000,0x1ef7bde9ffffe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc000000600001f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB522 : Ban 28 4 splitV522 := viaSmall (by decide +kernel) (by decide)

def splitV523 : List ℕ := [0x1ce739c1ff8000,0x1ef7bde9ffffe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc210842e0003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB523 : Ban 28 4 splitV523 := viaSmall (by decide +kernel) (by decide)

def splitV524 : List ℕ := [0x1ce739c1ff8000,0x1ef7bde9ffffe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xcf7bdeffffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB524 : Ban 28 4 splitV524 := viaSmall (by decide +kernel) (by decide)

def splitV525 : List ℕ := [0x1ce739c1ff8000,0x1ef7bde9ffffe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xdef7bdefffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB525 : Ban 28 4 splitV525 := viaSmall (by decide +kernel) (by decide)

def splitV526 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x81084210000000,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB526 : Ban 28 4 splitV526 := viaSmall (by decide +kernel) (by decide)

def splitV527 : List ℕ := [0x1ef7bde9ffffe0,0x318c63160ffc1f,0x3def7bd7fffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB527 : Ban 28 4 splitV527 := viaSmall (by decide +kernel) (by decide)

def splitV528 : List ℕ := [0x1ef7bde9ffffe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc210842e0003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB528 : Ban 28 4 splitV528 := viaSmall (by decide +kernel) (by decide)

def splitV529 : List ℕ := [0x1ef7bde9ffffe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc210842e0003ff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB529 : Ban 28 4 splitV529 := viaSmall (by decide +kernel) (by decide)

def splitV530 : List ℕ := [0x1ce739c1ff8000,0x1ef7bde9ffffe0,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB530 : Ban 28 5 splitV530 := viaBranch (ws := [splitV12,splitV515,splitV516,splitV517,splitV518,splitV519,splitV520,splitV521,splitV106,splitV165,splitV223,splitV522,splitV523,splitV524,splitV357,splitV525,splitV526,splitV527,splitV528,splitV529])
 (consBan splitB12 (consBan splitB515 (consBan splitB516 (consBan splitB517 (consBan splitB518 (consBan splitB519 (consBan splitB520 (consBan splitB521 (consBan splitB106 (consBan splitB165 (consBan splitB223 (consBan splitB522 (consBan splitB523 (consBan splitB524 (consBan splitB357 (consBan splitB525 (consBan splitB526 (consBan splitB527 (consBan splitB528 (consBan splitB529 (nilBan 28 4)))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV531 : List ℕ := [0x8421088007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x85294a500f8000,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB531 : Ban 28 4 splitV531 := viaSmall (by decide +kernel) (by decide)

def splitV532 : List ℕ := [0x8421088007fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB532 : Ban 28 4 splitV532 := viaSmall (by decide +kernel) (by decide)

def splitV533 : List ℕ := [0x1ce739c1ff8000,0x3084210600001f,0x85294a500f8000,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB533 : Ban 28 4 splitV533 := viaSmall (by decide +kernel) (by decide)

def splitV534 : List ℕ := [0x1ce739c1ff8000,0x30842106007c1f,0x85294a500f8000,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB534 : Ban 28 4 splitV534 := viaSmall (by decide +kernel) (by decide)

def splitV535 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x42108427f0001f,0x85294a500f8000,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB535 : Ban 28 4 splitV535 := viaSmall (by decide +kernel) (by decide)

def splitV536 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x4210842ff003ff,0x85294a500f8000,0x8d6b5ad80fffe0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB536 : Ban 28 4 splitV536 := viaSmall (by decide +kernel) (by decide)

def splitV537 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x81084218007fe0,0x85294a500f8000,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB537 : Ban 28 4 splitV537 := viaSmall (by decide +kernel) (by decide)

def splitV538 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x842108480003e0,0x85294a500f8000,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB538 : Ban 28 4 splitV538 := viaSmall (by decide +kernel) (by decide)

def splitV539 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x85294a500f8000,0x8c6318c80003e0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB539 : Ban 28 4 splitV539 := viaSmall (by decide +kernel) (by decide)

def splitV540 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x85294a500f8000,0x8d6b5ad80fffe0,0xc210842e0003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB540 : Ban 28 4 splitV540 := viaSmall (by decide +kernel) (by decide)

def splitV541 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x85294a500f8000,0x8d6b5ad80fffe0,0xc739ce7fff83ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB541 : Ban 28 4 splitV541 := viaSmall (by decide +kernel) (by decide)

def splitV542 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x85294a500f8000,0x8d6b5ad80fffe0,0xcf7bdeffffffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB542 : Ban 28 4 splitV542 := viaSmall (by decide +kernel) (by decide)

def splitV543 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x85294a500f8000,0xbdef7bde0fffff,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB543 : Ban 28 4 splitV543 := viaSmall (by decide +kernel) (by decide)

def splitV544 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0x9def7bd1ff8000,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB544 : Ban 28 4 splitV544 := viaSmall (by decide +kernel) (by decide)

def splitV545 : List ℕ := [0x1ce739c1ff8000,0x85294a500f8000,0x8d6b5ad80fffe0,0xb5ad6b560ffc1f,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB545 : Ban 28 4 splitV545 := viaSmall (by decide +kernel) (by decide)

def splitV546 : List ℕ := [0x1ce739c1ff8000,0x318c63160ffc1f,0x85294a500f8000,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB546 : Ban 28 5 splitV546 := viaBranch (ws := [splitV13,splitV35,splitV531,splitV532,splitV139,splitV533,splitV534,splitV166,splitV225,splitV226,splitV535,splitV536,splitV526,splitV537,splitV538,splitV539,splitV540,splitV541,splitV542,splitV358,splitV379,splitV543,splitV544,splitV440,splitV545,splitV464,splitV482,splitV465])
 (consBan splitB13 (consBan splitB35 (consBan splitB531 (consBan splitB532 (consBan splitB139 (consBan splitB533 (consBan splitB534 (consBan splitB166 (consBan splitB225 (consBan splitB226 (consBan splitB535 (consBan splitB536 (consBan splitB526 (consBan splitB537 (consBan splitB538 (consBan splitB539 (consBan splitB540 (consBan splitB541 (consBan splitB542 (consBan splitB358 (consBan splitB379 (consBan splitB543 (consBan splitB544 (consBan splitB440 (consBan splitB545 (consBan splitB464 (consBan splitB482 (consBan splitB465 (nilBan 28 4)))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV547 : List ℕ := [0x1ad6b5a9f07fe0,0x1ce739c1ff8000,0x318c63160ffc1f,0x8d6b5ad80fffe0,0xc6318c6ff003ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB547 : Ban 28 6 splitV547 := viaBranch (ws := [splitV20,splitV21,splitV42,splitV43,splitV44,splitV45,splitV46,splitV47,splitV48,splitV49,splitV78,splitV79,splitV80,splitV81,splitV82,splitV83,splitV84,splitV85,splitV86,splitV87,splitV111,splitV112,splitV113,splitV114,splitV115,splitV116,splitV140,splitV141,splitV142,splitV143,splitV144,splitV167,splitV168,splitV169,splitV170,splitV199,splitV228,splitV229,splitV256,splitV257,splitV258,splitV259,splitV260,splitV261,splitV262,splitV285,splitV286,splitV287,splitV288,splitV289,splitV290,splitV311,splitV312,splitV313,splitV314,splitV315,splitV316,splitV317,splitV318,splitV340,splitV359,splitV380,splitV401,splitV421,splitV441,splitV468,splitV483,splitV514,splitV530,splitV546])
 (consBan splitB20 (consBan splitB21 (consBan splitB42 (consBan splitB43 (consBan splitB44 (consBan splitB45 (consBan splitB46 (consBan splitB47 (consBan splitB48 (consBan splitB49 (consBan splitB78 (consBan splitB79 (consBan splitB80 (consBan splitB81 (consBan splitB82 (consBan splitB83 (consBan splitB84 (consBan splitB85 (consBan splitB86 (consBan splitB87 (consBan splitB111 (consBan splitB112 (consBan splitB113 (consBan splitB114 (consBan splitB115 (consBan splitB116 (consBan splitB140 (consBan splitB141 (consBan splitB142 (consBan splitB143 (consBan splitB144 (consBan splitB167 (consBan splitB168 (consBan splitB169 (consBan splitB170 (consBan splitB199 (consBan splitB228 (consBan splitB229 (consBan splitB256 (consBan splitB257 (consBan splitB258 (consBan splitB259 (consBan splitB260 (consBan splitB261 (consBan splitB262 (consBan splitB285 (consBan splitB286 (consBan splitB287 (consBan splitB288 (consBan splitB289 (consBan splitB290 (consBan splitB311 (consBan splitB312 (consBan splitB313 (consBan splitB314 (consBan splitB315 (consBan splitB316 (consBan splitB317 (consBan splitB318 (consBan splitB340 (consBan splitB359 (consBan splitB380 (consBan splitB401 (consBan splitB421 (consBan splitB441 (consBan splitB468 (consBan splitB483 (consBan splitB514 (consBan splitB530 (consBan splitB546 (nilBan 28 5)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

theorem restrictedBound : Wide 28 6 restrictedInputs := by
  have ess : ∀ a∈splitV547, ∃ i : Fin 28, ∀ b∈splitV547, b.testBit i.val≠b.testBit (28+i.val) → b=a := by decide +kernel
  have w := widen ess splitB547
  exact w

def caseInputs : List ℕ := [260802001655183704032, 63522255803178288127, 83902932718942419999, 5095169218210463712, 520674216698150912, 8589934592]
def projectRows : Projection 34 28 := pick [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] rfl (by decide +kernel) (by decide)
theorem caseBound : Ban 34 7 caseInputs := viaCut projectRows restrictedBound (by decide) (by decide +kernel) (by decide +kernel)
def graph (x : Fin 6 → Bool) := Nat.testBit (4008372970 * 2 ^ 32 + 3974162624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def posBits : ℕ := 0x8552c618b2c619a69a69a55555554d34d34d2cb2cb2c6186186
def negBits : ℕ := 0x450c210a0c211c6532857194ca15c6532857194ca15c653285
def sample (bank : ℕ) (i : Fin 34) (j : Fin 6) := bank.testBit (6*i.val+j.val)
def inputs : List ℕ := caseInputs
def seeds : List Wire := [(false,260802001655183704032),(false,63522255803178288127),(false,83902932718942419999),(false,5095169218210463712),(false,520674216698150912),(false,8589934592)]
set_option maxHeartbeats 1000000 in
theorem listed : ∀ i : Fin 34, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (34+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 34, graph (sample posBits i)=true ∧ graph (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 34, ∀ b∈inputs, b.testBit i.val≠b.testBit (34+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 34 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 6 C=graph) :
    ∃ k≤C.gates.countP counted, Live 34 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 6 → Bool) : C.eval (List.ofFn x)=graph x := congrFun eq x
  have good : Good 34 out.2 := by
    intro i hi same
    let j : Fin 34 := ⟨i,hi⟩
    have diff : read i out=read (34+i) out := by simp [read,same]
    have p := ev i;have n := ev (34+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa only [show reps seeds = inputs from rfl] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩


def witness : List Gate := [⟨.or,[3,4]⟩, ⟨.and,[2,6]⟩, ⟨.or,[0,4]⟩, ⟨.or,[5,7]⟩, ⟨.and,[0,9]⟩, ⟨.and,[3,8]⟩, ⟨.or,[2,11]⟩, ⟨.and,[1,12]⟩, ⟨.or,[10,13]⟩]
theorem upperMono : Monotone2 ⟨witness,14⟩ := by simp [Monotone2,witness]
theorem upperEq : ∀ x : Fin 6 → Bool, Circuit.eval ⟨witness,14⟩ (List.ofFn x)=graph x := by decide +kernel
end PEqualNP.Outside.L_meta_15863
open PEqualNP.Outside.L_meta_15863 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_15863 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 3974162624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 3974162624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨C,fan,size,eq⟩
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨k,small,live⟩ := trace C fan (funext eq)
    have lower : 8 ≤ k := by
      by_contra! h
      exact caseBound k (by omega) live
    have strict : C.gates.countP counted < C.gates.length := by
      apply List.countP_lt_length_iff.mpr
      obtain ⟨g,mem,op⟩ := hn
      exact ⟨g,mem,by simp [counted,op]⟩
    change C.gates.length ≤ s at size
    exact ⟨⟨witness,14⟩,upperMono,by change 9 ≤ s; omega,upperEq⟩
  · refine ⟨C, ?_, size, eq⟩
    intro g mem
    obtain ⟨op,cap⟩ := fan g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun e => (hn ⟨g,mem,e⟩).elim)), cap⟩
