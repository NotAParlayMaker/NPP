import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_15877

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
def restrictedInputs : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
def splitV0 : List ℕ := [0xf0,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB0 : Ban 29 5 splitV0 := viaSmall (by decide +kernel) (by decide)

def splitV1 : List ℕ := [0xf0,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB1 : Ban 29 5 splitV1 := viaSmall (by decide +kernel) (by decide)

def splitV2 : List ℕ := [0xf00,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB2 : Ban 29 5 splitV2 := viaSmall (by decide +kernel) (by decide)

def splitV3 : List ℕ := [0xf000,0x1000000f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB3 : Ban 29 4 splitV3 := viaSmall (by decide +kernel) (by decide)

def splitV4 : List ℕ := [0xf000,0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB4 : Ban 29 4 splitV4 := viaSmall (by decide +kernel) (by decide)

def splitV5 : List ℕ := [0xf000,0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB5 : Ban 29 4 splitV5 := viaSmall (by decide +kernel) (by decide)

def splitV6 : List ℕ := [0xf000,0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB6 : Ban 29 4 splitV6 := viaSmall (by decide +kernel) (by decide)

def splitV7 : List ℕ := [0xf000,0x22222230f0f0ff,0x88888880000ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB7 : Ban 29 4 splitV7 := viaSmall (by decide +kernel) (by decide)

def splitV8 : List ℕ := [0xf000,0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB8 : Ban 29 4 splitV8 := viaSmall (by decide +kernel) (by decide)

def splitV9 : List ℕ := [0xf000,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB9 : Ban 29 4 splitV9 := viaSmall (by decide +kernel) (by decide)

def splitV10 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB10 : Ban 29 4 splitV10 := viaSmall (by decide +kernel) (by decide)

def splitV11 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f00ff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB11 : Ban 29 4 splitV11 := viaSmall (by decide +kernel) (by decide)

def splitV12 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff0f000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB12 : Ban 29 4 splitV12 := viaSmall (by decide +kernel) (by decide)

def splitV13 : List ℕ := [0x22222230f0f0ff,0x888888800ffff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB13 : Ban 29 4 splitV13 := viaSmall (by decide +kernel) (by decide)

def splitV14 : List ℕ := [0xf000,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB14 : Ban 29 5 splitV14 := viaBranch (ws := [splitV3,splitV4,splitV5,splitV6,splitV7,splitV8,splitV9,splitV10,splitV11,splitV12,splitV13])
 (consBan splitB3 (consBan splitB4 (consBan splitB5 (consBan splitB6 (consBan splitB7 (consBan splitB8 (consBan splitB9 (consBan splitB10 (consBan splitB11 (consBan splitB12 (consBan splitB13 (nilBan 29 4))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV15 : List ℕ := [0xf000,0xf0ff0,0x22222230f0f0ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB15 : Ban 29 4 splitV15 := viaSmall (by decide +kernel) (by decide)

def splitV16 : List ℕ := [0xf000,0x22222230f0f00f,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB16 : Ban 29 4 splitV16 := viaSmall (by decide +kernel) (by decide)

def splitV17 : List ℕ := [0xf000,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB17 : Ban 29 4 splitV17 := viaSmall (by decide +kernel) (by decide)

def splitV18 : List ℕ := [0xf000,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f00ff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB18 : Ban 29 4 splitV18 := viaSmall (by decide +kernel) (by decide)

def splitV19 : List ℕ := [0xf000,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB19 : Ban 29 4 splitV19 := viaSmall (by decide +kernel) (by decide)

def splitV20 : List ℕ := [0xf000,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff0f000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB20 : Ban 29 4 splitV20 := viaSmall (by decide +kernel) (by decide)

def splitV21 : List ℕ := [0xf000,0x22222230f0f0ff,0x888888800ffff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB21 : Ban 29 4 splitV21 := viaSmall (by decide +kernel) (by decide)

def splitV22 : List ℕ := [0xf000,0x22222230f0f0ff,0x19999998ff00000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB22 : Ban 29 4 splitV22 := viaSmall (by decide +kernel) (by decide)

def splitV23 : List ℕ := [0xf000,0x888888800f0ff0,0xaaaaaab0ffffff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB23 : Ban 29 4 splitV23 := viaSmall (by decide +kernel) (by decide)

def splitV24 : List ℕ := [0x22222230f000ff,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB24 : Ban 29 4 splitV24 := viaSmall (by decide +kernel) (by decide)

def splitV25 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB25 : Ban 29 4 splitV25 := viaSmall (by decide +kernel) (by decide)

def splitV26 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x888888800ffff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB26 : Ban 29 4 splitV26 := viaSmall (by decide +kernel) (by decide)

def splitV27 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x19999998ff0f000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB27 : Ban 29 4 splitV27 := viaSmall (by decide +kernel) (by decide)

def splitV28 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x24444445f00ff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB28 : Ban 29 4 splitV28 := viaSmall (by decide +kernel) (by decide)

def splitV29 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f00ff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB29 : Ban 29 4 splitV29 := viaSmall (by decide +kernel) (by decide)

def splitV30 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff0f000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB30 : Ban 29 4 splitV30 := viaSmall (by decide +kernel) (by decide)

def splitV31 : List ℕ := [0x22222230f0f0ff,0x888888800ffff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB31 : Ban 29 4 splitV31 := viaSmall (by decide +kernel) (by decide)

def splitV32 : List ℕ := [0xf000,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB32 : Ban 29 5 splitV32 := viaBranch (ws := [splitV15,splitV5,splitV16,splitV17,splitV18,splitV19,splitV20,splitV21,splitV22,splitV23,splitV24,splitV25,splitV26,splitV27,splitV28,splitV29,splitV30,splitV31])
 (consBan splitB15 (consBan splitB5 (consBan splitB16 (consBan splitB17 (consBan splitB18 (consBan splitB19 (consBan splitB20 (consBan splitB21 (consBan splitB22 (consBan splitB23 (consBan splitB24 (consBan splitB25 (consBan splitB26 (consBan splitB27 (consBan splitB28 (consBan splitB29 (consBan splitB30 (consBan splitB31 (nilBan 29 4)))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV33 : List ℕ := [0xf0000,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB33 : Ban 29 5 splitV33 := viaSmall (by decide +kernel) (by decide)

def splitV34 : List ℕ := [0xf0ff0,0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB34 : Ban 29 4 splitV34 := viaSmall (by decide +kernel) (by decide)

def splitV35 : List ℕ := [0xf0ff0,0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB35 : Ban 29 4 splitV35 := viaSmall (by decide +kernel) (by decide)

def splitV36 : List ℕ := [0xf0ff0,0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB36 : Ban 29 4 splitV36 := viaSmall (by decide +kernel) (by decide)

def splitV37 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB37 : Ban 29 4 splitV37 := viaSmall (by decide +kernel) (by decide)

def splitV38 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x11111110ff00000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB38 : Ban 29 4 splitV38 := viaSmall (by decide +kernel) (by decide)

def splitV39 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x15555554000f000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB39 : Ban 29 4 splitV39 := viaSmall (by decide +kernel) (by decide)

def splitV40 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB40 : Ban 29 4 splitV40 := viaSmall (by decide +kernel) (by decide)

def splitV41 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x1555555400ff000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB41 : Ban 29 4 splitV41 := viaSmall (by decide +kernel) (by decide)

def splitV42 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB42 : Ban 29 4 splitV42 := viaSmall (by decide +kernel) (by decide)

def splitV43 : List ℕ := [0x22222230f0f00f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB43 : Ban 29 4 splitV43 := viaSmall (by decide +kernel) (by decide)

def splitV44 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x15555554000f000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB44 : Ban 29 4 splitV44 := viaSmall (by decide +kernel) (by decide)

def splitV45 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB45 : Ban 29 4 splitV45 := viaSmall (by decide +kernel) (by decide)

def splitV46 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB46 : Ban 29 4 splitV46 := viaSmall (by decide +kernel) (by decide)

def splitV47 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB47 : Ban 29 4 splitV47 := viaSmall (by decide +kernel) (by decide)

def splitV48 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ffff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB48 : Ban 29 4 splitV48 := viaSmall (by decide +kernel) (by decide)

def splitV49 : List ℕ := [0x22222230ffffff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB49 : Ban 29 4 splitV49 := viaSmall (by decide +kernel) (by decide)

def splitV50 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB50 : Ban 29 5 splitV50 := viaBranch (ws := [splitV34,splitV35,splitV36,splitV37,splitV38,splitV39,splitV40,splitV41,splitV42,splitV43,splitV44,splitV45,splitV46,splitV47,splitV48,splitV49])
 (consBan splitB34 (consBan splitB35 (consBan splitB36 (consBan splitB37 (consBan splitB38 (consBan splitB39 (consBan splitB40 (consBan splitB41 (consBan splitB42 (consBan splitB43 (consBan splitB44 (consBan splitB45 (consBan splitB46 (consBan splitB47 (consBan splitB48 (consBan splitB49 (nilBan 29 4)))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV51 : List ℕ := [0xf0,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB51 : Ban 29 4 splitV51 := viaSmall (by decide +kernel) (by decide)

def splitV52 : List ℕ := [0xff0,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB52 : Ban 29 4 splitV52 := viaSmall (by decide +kernel) (by decide)

def splitV53 : List ℕ := [0xf00f0,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB53 : Ban 29 4 splitV53 := viaSmall (by decide +kernel) (by decide)

def splitV54 : List ℕ := [0xf0ff0,0xf00000,0x22222230f0f0ff,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB54 : Ban 29 4 splitV54 := viaSmall (by decide +kernel) (by decide)

def splitV55 : List ℕ := [0xf0ff0,0x2222223000f0ff,0x22222230f0f0ff,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB55 : Ban 29 4 splitV55 := viaSmall (by decide +kernel) (by decide)

def splitV56 : List ℕ := [0xf0ff0,0x22222230f000ff,0x22222230f0f0ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB56 : Ban 29 4 splitV56 := viaSmall (by decide +kernel) (by decide)

def splitV57 : List ℕ := [0xf0ff0,0x22222230f000ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB57 : Ban 29 4 splitV57 := viaSmall (by decide +kernel) (by decide)

def splitV58 : List ℕ := [0xf0ff0,0x22222230f000ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB58 : Ban 29 4 splitV58 := viaSmall (by decide +kernel) (by decide)

def splitV59 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x444444400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB59 : Ban 29 4 splitV59 := viaSmall (by decide +kernel) (by decide)

def splitV60 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x8888888ff00000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB60 : Ban 29 4 splitV60 := viaSmall (by decide +kernel) (by decide)

def splitV61 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x1111111000ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB61 : Ban 29 4 splitV61 := viaSmall (by decide +kernel) (by decide)

def splitV62 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x1555555400ff000,0x199999980f00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB62 : Ban 29 4 splitV62 := viaSmall (by decide +kernel) (by decide)

def splitV63 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB63 : Ban 29 4 splitV63 := viaSmall (by decide +kernel) (by decide)

def splitV64 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB64 : Ban 29 4 splitV64 := viaSmall (by decide +kernel) (by decide)

def splitV65 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB65 : Ban 29 4 splitV65 := viaSmall (by decide +kernel) (by decide)

def splitV66 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x1555555400ff000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB66 : Ban 29 4 splitV66 := viaSmall (by decide +kernel) (by decide)

def splitV67 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x1555555400ff000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB67 : Ban 29 4 splitV67 := viaSmall (by decide +kernel) (by decide)

def splitV68 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x1555555400ffff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB68 : Ban 29 4 splitV68 := viaSmall (by decide +kernel) (by decide)

def splitV69 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x19999998ff00000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB69 : Ban 29 4 splitV69 := viaSmall (by decide +kernel) (by decide)

def splitV70 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x19999998ff00000,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB70 : Ban 29 4 splitV70 := viaSmall (by decide +kernel) (by decide)

def splitV71 : List ℕ := [0xf0ff0,0x22222230ffffff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB71 : Ban 29 4 splitV71 := viaSmall (by decide +kernel) (by decide)

def splitV72 : List ℕ := [0xf0ff0,0x1555555400ff000,0x177777770fff0ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB72 : Ban 29 4 splitV72 := viaSmall (by decide +kernel) (by decide)

def splitV73 : List ℕ := [0x22222230f0f00f,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB73 : Ban 29 4 splitV73 := viaSmall (by decide +kernel) (by decide)

def splitV74 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB74 : Ban 29 4 splitV74 := viaSmall (by decide +kernel) (by decide)

def splitV75 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x1555555400ffff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB75 : Ban 29 4 splitV75 := viaSmall (by decide +kernel) (by decide)

def splitV76 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB76 : Ban 29 4 splitV76 := viaSmall (by decide +kernel) (by decide)

def splitV77 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x24444445f0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB77 : Ban 29 4 splitV77 := viaSmall (by decide +kernel) (by decide)

def splitV78 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB78 : Ban 29 5 splitV78 := viaBranch (ws := [splitV51,splitV52,splitV15,splitV53,splitV54,splitV55,splitV56,splitV57,splitV58,splitV36,splitV59,splitV60,splitV61,splitV39,splitV62,splitV63,splitV40,splitV64,splitV65,splitV41,splitV66,splitV67,splitV68,splitV69,splitV70,splitV71,splitV72,splitV73,splitV74,splitV75,splitV76,splitV77])
 (consBan splitB51 (consBan splitB52 (consBan splitB15 (consBan splitB53 (consBan splitB54 (consBan splitB55 (consBan splitB56 (consBan splitB57 (consBan splitB58 (consBan splitB36 (consBan splitB59 (consBan splitB60 (consBan splitB61 (consBan splitB39 (consBan splitB62 (consBan splitB63 (consBan splitB40 (consBan splitB64 (consBan splitB65 (consBan splitB41 (consBan splitB66 (consBan splitB67 (consBan splitB68 (consBan splitB69 (consBan splitB70 (consBan splitB71 (consBan splitB72 (consBan splitB73 (consBan splitB74 (consBan splitB75 (consBan splitB76 (consBan splitB77 (nilBan 29 4)))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV79 : List ℕ := [0xf00000,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB79 : Ban 29 5 splitV79 := viaSmall (by decide +kernel) (by decide)

def splitV80 : List ℕ := [0xf00000,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB80 : Ban 29 5 splitV80 := viaSmall (by decide +kernel) (by decide)

def splitV81 : List ℕ := [0xf000000,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB81 : Ban 29 5 splitV81 := viaSmall (by decide +kernel) (by decide)

def splitV82 : List ℕ := [0x1000000f,0x22222220f0f0f0,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB82 : Ban 29 4 splitV82 := viaSmall (by decide +kernel) (by decide)

def splitV83 : List ℕ := [0x1000000f,0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB83 : Ban 29 4 splitV83 := viaSmall (by decide +kernel) (by decide)

def splitV84 : List ℕ := [0x1000000f,0x22222230f0f00f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB84 : Ban 29 4 splitV84 := viaSmall (by decide +kernel) (by decide)

def splitV85 : List ℕ := [0x1000000f,0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x1555555400ff000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB85 : Ban 29 4 splitV85 := viaSmall (by decide +kernel) (by decide)

def splitV86 : List ℕ := [0x1000000f,0x22222230f0f0ff,0x888888800f0ff0,0x15555554000f000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB86 : Ban 29 4 splitV86 := viaSmall (by decide +kernel) (by decide)

def splitV87 : List ℕ := [0x1000000f,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999999ff0000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB87 : Ban 29 4 splitV87 := viaSmall (by decide +kernel) (by decide)

def splitV88 : List ℕ := [0x1000000f,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcffff000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB88 : Ban 29 4 splitV88 := viaSmall (by decide +kernel) (by decide)

def splitV89 : List ℕ := [0x1000000f,0x22222230f0f0ff,0x888888800f0ff0,0x1555555500ff00f,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB89 : Ban 29 4 splitV89 := viaSmall (by decide +kernel) (by decide)

def splitV90 : List ℕ := [0x1000000f,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB90 : Ban 29 4 splitV90 := viaSmall (by decide +kernel) (by decide)

def splitV91 : List ℕ := [0x1000000f,0x22222230f0f0ff,0x888888900f0fff,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB91 : Ban 29 4 splitV91 := viaSmall (by decide +kernel) (by decide)

def splitV92 : List ℕ := [0x1000000f,0x888888800f0ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB92 : Ban 29 4 splitV92 := viaSmall (by decide +kernel) (by decide)

def splitV93 : List ℕ := [0x1000000f,0x888888800f0ff0,0x1555555400f0000,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB93 : Ban 29 4 splitV93 := viaSmall (by decide +kernel) (by decide)

def splitV94 : List ℕ := [0x1000000f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB94 : Ban 29 4 splitV94 := viaSmall (by decide +kernel) (by decide)

def splitV95 : List ℕ := [0x22222220f0f0f0,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB95 : Ban 29 4 splitV95 := viaSmall (by decide +kernel) (by decide)

def splitV96 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x888888900f0fff,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB96 : Ban 29 4 splitV96 := viaSmall (by decide +kernel) (by decide)

def splitV97 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1555555500ff00f,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB97 : Ban 29 4 splitV97 := viaSmall (by decide +kernel) (by decide)

def splitV98 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x19999999ff0000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB98 : Ban 29 4 splitV98 := viaSmall (by decide +kernel) (by decide)

def splitV99 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999999ff0000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB99 : Ban 29 4 splitV99 := viaSmall (by decide +kernel) (by decide)

def splitV100 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555500ff00f,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB100 : Ban 29 4 splitV100 := viaSmall (by decide +kernel) (by decide)

def splitV101 : List ℕ := [0x22222230f0f0ff,0x888888900f0fff,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB101 : Ban 29 4 splitV101 := viaSmall (by decide +kernel) (by decide)

def splitV102 : List ℕ := [0x1000000f,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB102 : Ban 29 5 splitV102 := viaBranch (ws := [splitV3,splitV82,splitV83,splitV84,splitV85,splitV86,splitV87,splitV88,splitV89,splitV90,splitV91,splitV92,splitV93,splitV94,splitV95,splitV96,splitV97,splitV98,splitV99,splitV100,splitV101])
 (consBan splitB3 (consBan splitB82 (consBan splitB83 (consBan splitB84 (consBan splitB85 (consBan splitB86 (consBan splitB87 (consBan splitB88 (consBan splitB89 (consBan splitB90 (consBan splitB91 (consBan splitB92 (consBan splitB93 (consBan splitB94 (consBan splitB95 (consBan splitB96 (consBan splitB97 (consBan splitB98 (consBan splitB99 (consBan splitB100 (consBan splitB101 (nilBan 29 4))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV103 : List ℕ := [0x1000000f,0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB103 : Ban 29 4 splitV103 := viaSmall (by decide +kernel) (by decide)

def splitV104 : List ℕ := [0x1000000f,0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB104 : Ban 29 4 splitV104 := viaSmall (by decide +kernel) (by decide)

def splitV105 : List ℕ := [0x1000000f,0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB105 : Ban 29 4 splitV105 := viaSmall (by decide +kernel) (by decide)

def splitV106 : List ℕ := [0x1000000f,0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB106 : Ban 29 4 splitV106 := viaSmall (by decide +kernel) (by decide)

def splitV107 : List ℕ := [0x1000000f,0x22222230f0f0ff,0x888888800f0ff0,0x1111111000ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB107 : Ban 29 4 splitV107 := viaSmall (by decide +kernel) (by decide)

def splitV108 : List ℕ := [0x1000000f,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x199999980f00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB108 : Ban 29 4 splitV108 := viaSmall (by decide +kernel) (by decide)

def splitV109 : List ℕ := [0x1000000f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444444f000f00]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB109 : Ban 29 4 splitV109 := viaSmall (by decide +kernel) (by decide)

def splitV110 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999999ff0000f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB110 : Ban 29 4 splitV110 := viaSmall (by decide +kernel) (by decide)

def splitV111 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555500ff00f,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB111 : Ban 29 4 splitV111 := viaSmall (by decide +kernel) (by decide)

def splitV112 : List ℕ := [0x22222230f0f0ff,0x888888900f0fff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB112 : Ban 29 4 splitV112 := viaSmall (by decide +kernel) (by decide)

def splitV113 : List ℕ := [0x1000000f,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB113 : Ban 29 5 splitV113 := viaBranch (ws := [splitV82,splitV103,splitV104,splitV105,splitV106,splitV107,splitV108,splitV109,splitV110,splitV111,splitV112])
 (consBan splitB82 (consBan splitB103 (consBan splitB104 (consBan splitB105 (consBan splitB106 (consBan splitB107 (consBan splitB108 (consBan splitB109 (consBan splitB110 (consBan splitB111 (consBan splitB112 (nilBan 29 4))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV114 : List ℕ := [0x1000000f,0x44444440000000,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB114 : Ban 29 4 splitV114 := viaSmall (by decide +kernel) (by decide)

def splitV115 : List ℕ := [0x1000000f,0x88888880000ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB115 : Ban 29 4 splitV115 := viaSmall (by decide +kernel) (by decide)

def splitV116 : List ℕ := [0x1000000f,0x888888800f00f0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB116 : Ban 29 4 splitV116 := viaSmall (by decide +kernel) (by decide)

def splitV117 : List ℕ := [0x1000000f,0x888888800f0ff0,0x1111111000ff000,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB117 : Ban 29 4 splitV117 := viaSmall (by decide +kernel) (by decide)

def splitV118 : List ℕ := [0x1000000f,0x888888800f0ff0,0x1111111000ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB118 : Ban 29 4 splitV118 := viaSmall (by decide +kernel) (by decide)

def splitV119 : List ℕ := [0x1000000f,0x888888800f0ff0,0x1111111000ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB119 : Ban 29 4 splitV119 := viaSmall (by decide +kernel) (by decide)

def splitV120 : List ℕ := [0x1000000f,0x888888800f0ff0,0x15555554000f000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB120 : Ban 29 4 splitV120 := viaSmall (by decide +kernel) (by decide)

def splitV121 : List ℕ := [0x1000000f,0x888888800f0ff0,0x1555555400ff000,0x199999980f00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB121 : Ban 29 4 splitV121 := viaSmall (by decide +kernel) (by decide)

def splitV122 : List ℕ := [0x1000000f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB122 : Ban 29 4 splitV122 := viaSmall (by decide +kernel) (by decide)

def splitV123 : List ℕ := [0x1000000f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB123 : Ban 29 4 splitV123 := viaSmall (by decide +kernel) (by decide)

def splitV124 : List ℕ := [0x1000000f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB124 : Ban 29 4 splitV124 := viaSmall (by decide +kernel) (by decide)

def splitV125 : List ℕ := [0x1000000f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB125 : Ban 29 4 splitV125 := viaSmall (by decide +kernel) (by decide)

def splitV126 : List ℕ := [0x1000000f,0x888888800f0ff0,0x1555555400ff000,0x19999999ff0000f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB126 : Ban 29 4 splitV126 := viaSmall (by decide +kernel) (by decide)

def splitV127 : List ℕ := [0x1000000f,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB127 : Ban 29 4 splitV127 := viaSmall (by decide +kernel) (by decide)

def splitV128 : List ℕ := [0x1000000f,0x888888800f0ff0,0x1555555500ff00f,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB128 : Ban 29 4 splitV128 := viaSmall (by decide +kernel) (by decide)

def splitV129 : List ℕ := [0x1000000f,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB129 : Ban 29 4 splitV129 := viaSmall (by decide +kernel) (by decide)

def splitV130 : List ℕ := [0x1000000f,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB130 : Ban 29 4 splitV130 := viaSmall (by decide +kernel) (by decide)

def splitV131 : List ℕ := [0x1000000f,0x888888900f0fff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB131 : Ban 29 4 splitV131 := viaSmall (by decide +kernel) (by decide)

def splitV132 : List ℕ := [0x1000000f,0x1555555400ff000,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB132 : Ban 29 4 splitV132 := viaSmall (by decide +kernel) (by decide)

def splitV133 : List ℕ := [0x1000000f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB133 : Ban 29 4 splitV133 := viaSmall (by decide +kernel) (by decide)

def splitV134 : List ℕ := [0x888888800f0ff0,0x888888900f0fff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB134 : Ban 29 4 splitV134 := viaSmall (by decide +kernel) (by decide)

def splitV135 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x1555555500ff00f,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB135 : Ban 29 4 splitV135 := viaSmall (by decide +kernel) (by decide)

def splitV136 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x19999999ff0000f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB136 : Ban 29 4 splitV136 := viaSmall (by decide +kernel) (by decide)

def splitV137 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444444f000f00,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB137 : Ban 29 4 splitV137 := viaSmall (by decide +kernel) (by decide)

def splitV138 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999999ff0000f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB138 : Ban 29 4 splitV138 := viaSmall (by decide +kernel) (by decide)

def splitV139 : List ℕ := [0x888888900f0fff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB139 : Ban 29 4 splitV139 := viaSmall (by decide +kernel) (by decide)

def splitV140 : List ℕ := [0x1000000f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB140 : Ban 29 5 splitV140 := viaBranch (ws := [splitV114,splitV115,splitV116,splitV117,splitV118,splitV119,splitV120,splitV121,splitV109,splitV122,splitV123,splitV124,splitV125,splitV126,splitV127,splitV128,splitV129,splitV130,splitV131,splitV132,splitV133,splitV134,splitV135,splitV136,splitV137,splitV138,splitV139])
 (consBan splitB114 (consBan splitB115 (consBan splitB116 (consBan splitB117 (consBan splitB118 (consBan splitB119 (consBan splitB120 (consBan splitB121 (consBan splitB109 (consBan splitB122 (consBan splitB123 (consBan splitB124 (consBan splitB125 (consBan splitB126 (consBan splitB127 (consBan splitB128 (consBan splitB129 (consBan splitB130 (consBan splitB131 (consBan splitB132 (consBan splitB133 (consBan splitB134 (consBan splitB135 (consBan splitB136 (consBan splitB137 (consBan splitB138 (consBan splitB139 (nilBan 29 4))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV141 : List ℕ := [0x22222220f0f0f0,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB141 : Ban 29 5 splitV141 := viaSmall (by decide +kernel) (by decide)

def splitV142 : List ℕ := [0x22222220f0f0f0,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB142 : Ban 29 5 splitV142 := viaSmall (by decide +kernel) (by decide)

def splitV143 : List ℕ := [0x2222223000f0ff,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB143 : Ban 29 5 splitV143 := viaSmall (by decide +kernel) (by decide)

def splitV144 : List ℕ := [0x2222223000f0ff,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB144 : Ban 29 5 splitV144 := viaSmall (by decide +kernel) (by decide)

def splitV145 : List ℕ := [0xf000000,0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB145 : Ban 29 4 splitV145 := viaSmall (by decide +kernel) (by decide)

def splitV146 : List ℕ := [0x1000000f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB146 : Ban 29 4 splitV146 := viaSmall (by decide +kernel) (by decide)

def splitV147 : List ℕ := [0x2222222000f0f0,0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB147 : Ban 29 4 splitV147 := viaSmall (by decide +kernel) (by decide)

def splitV148 : List ℕ := [0x222222300000ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB148 : Ban 29 4 splitV148 := viaSmall (by decide +kernel) (by decide)

def splitV149 : List ℕ := [0x2222223000f00f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB149 : Ban 29 4 splitV149 := viaSmall (by decide +kernel) (by decide)

def splitV150 : List ℕ := [0x2222223000f0ff,0x444444400ff000,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB150 : Ban 29 4 splitV150 := viaSmall (by decide +kernel) (by decide)

def splitV151 : List ℕ := [0x2222223000f0ff,0x88888880000000,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB151 : Ban 29 4 splitV151 := viaSmall (by decide +kernel) (by decide)

def splitV152 : List ℕ := [0x2222223000f0ff,0x88888880000ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB152 : Ban 29 4 splitV152 := viaSmall (by decide +kernel) (by decide)

def splitV153 : List ℕ := [0x2222223000f0ff,0x888888800f00f0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB153 : Ban 29 4 splitV153 := viaSmall (by decide +kernel) (by decide)

def splitV154 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x8888888ff00000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB154 : Ban 29 4 splitV154 := viaSmall (by decide +kernel) (by decide)

def splitV155 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x111111100000000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB155 : Ban 29 4 splitV155 := viaSmall (by decide +kernel) (by decide)

def splitV156 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1111111000ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB156 : Ban 29 4 splitV156 := viaSmall (by decide +kernel) (by decide)

def splitV157 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x11111110ff00000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB157 : Ban 29 4 splitV157 := viaSmall (by decide +kernel) (by decide)

def splitV158 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x15555554000f000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB158 : Ban 29 4 splitV158 := viaSmall (by decide +kernel) (by decide)

def splitV159 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x199999980f00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB159 : Ban 29 4 splitV159 := viaSmall (by decide +kernel) (by decide)

def splitV160 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB160 : Ban 29 4 splitV160 := viaSmall (by decide +kernel) (by decide)

def splitV161 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB161 : Ban 29 4 splitV161 := viaSmall (by decide +kernel) (by decide)

def splitV162 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB162 : Ban 29 4 splitV162 := viaSmall (by decide +kernel) (by decide)

def splitV163 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB163 : Ban 29 4 splitV163 := viaSmall (by decide +kernel) (by decide)

def splitV164 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB164 : Ban 29 4 splitV164 := viaSmall (by decide +kernel) (by decide)

def splitV165 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB165 : Ban 29 4 splitV165 := viaSmall (by decide +kernel) (by decide)

def splitV166 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB166 : Ban 29 4 splitV166 := viaSmall (by decide +kernel) (by decide)

def splitV167 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x1bbbbbbbff0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB167 : Ban 29 4 splitV167 := viaSmall (by decide +kernel) (by decide)

def splitV168 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB168 : Ban 29 4 splitV168 := viaSmall (by decide +kernel) (by decide)

def splitV169 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB169 : Ban 29 4 splitV169 := viaSmall (by decide +kernel) (by decide)

def splitV170 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x244444450000f0f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB170 : Ban 29 4 splitV170 := viaSmall (by decide +kernel) (by decide)

def splitV171 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB171 : Ban 29 4 splitV171 := viaSmall (by decide +kernel) (by decide)

def splitV172 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB172 : Ban 29 4 splitV172 := viaSmall (by decide +kernel) (by decide)

def splitV173 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB173 : Ban 29 4 splitV173 := viaSmall (by decide +kernel) (by decide)

def splitV174 : List ℕ := [0x2222223000f0ff,0x1555555400ff000,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB174 : Ban 29 4 splitV174 := viaSmall (by decide +kernel) (by decide)

def splitV175 : List ℕ := [0x2222223000f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB175 : Ban 29 4 splitV175 := viaSmall (by decide +kernel) (by decide)

def splitV176 : List ℕ := [0x888888800f0ff0,0xaaaaaab00fffff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB176 : Ban 29 4 splitV176 := viaSmall (by decide +kernel) (by decide)

def splitV177 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x1777777700ff0ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB177 : Ban 29 4 splitV177 := viaSmall (by decide +kernel) (by decide)

def splitV178 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB178 : Ban 29 4 splitV178 := viaSmall (by decide +kernel) (by decide)

def splitV179 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB179 : Ban 29 5 splitV179 := viaBranch (ws := [splitV34,splitV145,splitV83,splitV146,splitV147,splitV148,splitV149,splitV150,splitV151,splitV152,splitV153,splitV154,splitV155,splitV156,splitV157,splitV158,splitV159,splitV160,splitV161,splitV162,splitV163,splitV164,splitV165,splitV166,splitV167,splitV168,splitV169,splitV170,splitV171,splitV172,splitV173,splitV174,splitV175,splitV176,splitV177,splitV178,splitV137])
 (consBan splitB34 (consBan splitB145 (consBan splitB83 (consBan splitB146 (consBan splitB147 (consBan splitB148 (consBan splitB149 (consBan splitB150 (consBan splitB151 (consBan splitB152 (consBan splitB153 (consBan splitB154 (consBan splitB155 (consBan splitB156 (consBan splitB157 (consBan splitB158 (consBan splitB159 (consBan splitB160 (consBan splitB161 (consBan splitB162 (consBan splitB163 (consBan splitB164 (consBan splitB165 (consBan splitB166 (consBan splitB167 (consBan splitB168 (consBan splitB169 (consBan splitB170 (consBan splitB171 (consBan splitB172 (consBan splitB173 (consBan splitB174 (consBan splitB175 (consBan splitB176 (consBan splitB177 (consBan splitB178 (consBan splitB137 (nilBan 29 4))))))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV180 : List ℕ := [0xf0,0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB180 : Ban 29 4 splitV180 := viaSmall (by decide +kernel) (by decide)

def splitV181 : List ℕ := [0xf00,0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB181 : Ban 29 4 splitV181 := viaSmall (by decide +kernel) (by decide)

def splitV182 : List ℕ := [0xf0000,0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB182 : Ban 29 4 splitV182 := viaSmall (by decide +kernel) (by decide)

def splitV183 : List ℕ := [0x2222222000f0f0,0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB183 : Ban 29 4 splitV183 := viaSmall (by decide +kernel) (by decide)

def splitV184 : List ℕ := [0x222222300000ff,0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB184 : Ban 29 4 splitV184 := viaSmall (by decide +kernel) (by decide)

def splitV185 : List ℕ := [0x2222223000f00f,0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB185 : Ban 29 4 splitV185 := viaSmall (by decide +kernel) (by decide)

def splitV186 : List ℕ := [0x2222223000f0ff,0x44444440000000,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB186 : Ban 29 4 splitV186 := viaSmall (by decide +kernel) (by decide)

def splitV187 : List ℕ := [0x2222223000f0ff,0x88888880000ff0,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB187 : Ban 29 4 splitV187 := viaSmall (by decide +kernel) (by decide)

def splitV188 : List ℕ := [0x2222223000f0ff,0x888888800f00f0,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB188 : Ban 29 4 splitV188 := viaSmall (by decide +kernel) (by decide)

def splitV189 : List ℕ := [0x2222223000f0ff,0x888888800f00f0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB189 : Ban 29 4 splitV189 := viaSmall (by decide +kernel) (by decide)

def splitV190 : List ℕ := [0x2222223000f0ff,0x888888800f0f00,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB190 : Ban 29 4 splitV190 := viaSmall (by decide +kernel) (by decide)

def splitV191 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0xaaaaaab00fffff,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB191 : Ban 29 4 splitV191 := viaSmall (by decide +kernel) (by decide)

def splitV192 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1111111000ff000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB192 : Ban 29 4 splitV192 := viaSmall (by decide +kernel) (by decide)

def splitV193 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x15555554000f000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB193 : Ban 29 4 splitV193 := viaSmall (by decide +kernel) (by decide)

def splitV194 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400f0000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB194 : Ban 29 4 splitV194 := viaSmall (by decide +kernel) (by decide)

def splitV195 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x1777777700ff0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB195 : Ban 29 4 splitV195 := viaSmall (by decide +kernel) (by decide)

def splitV196 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB196 : Ban 29 4 splitV196 := viaSmall (by decide +kernel) (by decide)

def splitV197 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB197 : Ban 29 4 splitV197 := viaSmall (by decide +kernel) (by decide)

def splitV198 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x20000001f000f0f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB198 : Ban 29 4 splitV198 := viaSmall (by decide +kernel) (by decide)

def splitV199 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444444f000f00,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB199 : Ban 29 4 splitV199 := viaSmall (by decide +kernel) (by decide)

def splitV200 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f00000f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB200 : Ban 29 4 splitV200 := viaSmall (by decide +kernel) (by decide)

def splitV201 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x26666667f00ffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB201 : Ban 29 4 splitV201 := viaSmall (by decide +kernel) (by decide)

def splitV202 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB202 : Ban 29 4 splitV202 := viaSmall (by decide +kernel) (by decide)

def splitV203 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB203 : Ban 29 4 splitV203 := viaSmall (by decide +kernel) (by decide)

def splitV204 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB204 : Ban 29 4 splitV204 := viaSmall (by decide +kernel) (by decide)

def splitV205 : List ℕ := [0x2222223000f0ff,0x1555555400ff000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB205 : Ban 29 4 splitV205 := viaSmall (by decide +kernel) (by decide)

def splitV206 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB206 : Ban 29 5 splitV206 := viaBranch (ws := [splitV180,splitV181,splitV4,splitV182,splitV103,splitV183,splitV184,splitV185,splitV186,splitV187,splitV188,splitV189,splitV190,splitV191,splitV192,splitV193,splitV194,splitV195,splitV196,splitV197,splitV198,splitV199,splitV200,splitV201,splitV202,splitV203,splitV204,splitV205])
 (consBan splitB180 (consBan splitB181 (consBan splitB4 (consBan splitB182 (consBan splitB103 (consBan splitB183 (consBan splitB184 (consBan splitB185 (consBan splitB186 (consBan splitB187 (consBan splitB188 (consBan splitB189 (consBan splitB190 (consBan splitB191 (consBan splitB192 (consBan splitB193 (consBan splitB194 (consBan splitB195 (consBan splitB196 (consBan splitB197 (consBan splitB198 (consBan splitB199 (consBan splitB200 (consBan splitB201 (consBan splitB202 (consBan splitB203 (consBan splitB204 (consBan splitB205 (nilBan 29 4)))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV207 : List ℕ := [0x22222230f000ff,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB207 : Ban 29 5 splitV207 := viaSmall (by decide +kernel) (by decide)

def splitV208 : List ℕ := [0xf0,0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB208 : Ban 29 4 splitV208 := viaSmall (by decide +kernel) (by decide)

def splitV209 : List ℕ := [0xf000,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB209 : Ban 29 4 splitV209 := viaSmall (by decide +kernel) (by decide)

def splitV210 : List ℕ := [0xf00000,0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB210 : Ban 29 4 splitV210 := viaSmall (by decide +kernel) (by decide)

def splitV211 : List ℕ := [0x22222220f000f0,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB211 : Ban 29 4 splitV211 := viaSmall (by decide +kernel) (by decide)

def splitV212 : List ℕ := [0x22222220f0f0f0,0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB212 : Ban 29 4 splitV212 := viaSmall (by decide +kernel) (by decide)

def splitV213 : List ℕ := [0x222222300000ff,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB213 : Ban 29 4 splitV213 := viaSmall (by decide +kernel) (by decide)

def splitV214 : List ℕ := [0x2222223000f0ff,0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB214 : Ban 29 4 splitV214 := viaSmall (by decide +kernel) (by decide)

def splitV215 : List ℕ := [0x22222230f0000f,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB215 : Ban 29 4 splitV215 := viaSmall (by decide +kernel) (by decide)

def splitV216 : List ℕ := [0x22222230f000ff,0x22222230f0f00f,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB216 : Ban 29 4 splitV216 := viaSmall (by decide +kernel) (by decide)

def splitV217 : List ℕ := [0x22222230f000ff,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB217 : Ban 29 4 splitV217 := viaSmall (by decide +kernel) (by decide)

def splitV218 : List ℕ := [0x22222230f000ff,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB218 : Ban 29 4 splitV218 := viaSmall (by decide +kernel) (by decide)

def splitV219 : List ℕ := [0x22222230f000ff,0x22222230f0f0ff,0x19999998ff00000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB219 : Ban 29 4 splitV219 := viaSmall (by decide +kernel) (by decide)

def splitV220 : List ℕ := [0x22222230f000ff,0x888888800f0f00,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB220 : Ban 29 4 splitV220 := viaSmall (by decide +kernel) (by decide)

def splitV221 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0xaaaaaab0ffffff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB221 : Ban 29 4 splitV221 := viaSmall (by decide +kernel) (by decide)

def splitV222 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998f000000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB222 : Ban 29 4 splitV222 := viaSmall (by decide +kernel) (by decide)

def splitV223 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB223 : Ban 29 4 splitV223 := viaSmall (by decide +kernel) (by decide)

def splitV224 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444444f000f00,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB224 : Ban 29 4 splitV224 := viaSmall (by decide +kernel) (by decide)

def splitV225 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x26666667ff0ffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB225 : Ban 29 4 splitV225 := viaSmall (by decide +kernel) (by decide)

def splitV226 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0xaaaaaab0ff0fff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB226 : Ban 29 4 splitV226 := viaSmall (by decide +kernel) (by decide)

def splitV227 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1bbbbbbbff000ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB227 : Ban 29 4 splitV227 := viaSmall (by decide +kernel) (by decide)

def splitV228 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x26666667ff00fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB228 : Ban 29 4 splitV228 := viaSmall (by decide +kernel) (by decide)

def splitV229 : List ℕ := [0x22222230f000ff,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB229 : Ban 29 5 splitV229 := viaBranch (ws := [splitV208,splitV5,splitV209,splitV56,splitV210,splitV104,splitV211,splitV212,splitV213,splitV214,splitV215,splitV216,splitV217,splitV218,splitV219,splitV220,splitV221,splitV222,splitV223,splitV224,splitV225,splitV226,splitV227,splitV228])
 (consBan splitB208 (consBan splitB5 (consBan splitB209 (consBan splitB56 (consBan splitB210 (consBan splitB104 (consBan splitB211 (consBan splitB212 (consBan splitB213 (consBan splitB214 (consBan splitB215 (consBan splitB216 (consBan splitB217 (consBan splitB218 (consBan splitB219 (consBan splitB220 (consBan splitB221 (consBan splitB222 (consBan splitB223 (consBan splitB224 (consBan splitB225 (consBan splitB226 (consBan splitB227 (consBan splitB228 (nilBan 29 4)))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV230 : List ℕ := [0xf0,0x22222230f000ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB230 : Ban 29 4 splitV230 := viaSmall (by decide +kernel) (by decide)

def splitV231 : List ℕ := [0xf0000,0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB231 : Ban 29 4 splitV231 := viaSmall (by decide +kernel) (by decide)

def splitV232 : List ℕ := [0x22222230f0000f,0x22222230f000ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB232 : Ban 29 4 splitV232 := viaSmall (by decide +kernel) (by decide)

def splitV233 : List ℕ := [0x22222230f0000f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB233 : Ban 29 4 splitV233 := viaSmall (by decide +kernel) (by decide)

def splitV234 : List ℕ := [0x22222230f0000f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB234 : Ban 29 4 splitV234 := viaSmall (by decide +kernel) (by decide)

def splitV235 : List ℕ := [0x22222230f000ff,0x44444440000000,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB235 : Ban 29 4 splitV235 := viaSmall (by decide +kernel) (by decide)

def splitV236 : List ℕ := [0x22222230f000ff,0x444444400ff000,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB236 : Ban 29 4 splitV236 := viaSmall (by decide +kernel) (by decide)

def splitV237 : List ℕ := [0x22222230f000ff,0x88888880000ff0,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB237 : Ban 29 4 splitV237 := viaSmall (by decide +kernel) (by decide)

def splitV238 : List ℕ := [0x22222230f000ff,0x88888880000ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB238 : Ban 29 4 splitV238 := viaSmall (by decide +kernel) (by decide)

def splitV239 : List ℕ := [0x22222230f000ff,0x88888880000ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB239 : Ban 29 4 splitV239 := viaSmall (by decide +kernel) (by decide)

def splitV240 : List ℕ := [0x22222230f000ff,0x888888800f00f0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB240 : Ban 29 4 splitV240 := viaSmall (by decide +kernel) (by decide)

def splitV241 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x8888888ff00000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB241 : Ban 29 4 splitV241 := viaSmall (by decide +kernel) (by decide)

def splitV242 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x111111100000000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB242 : Ban 29 4 splitV242 := viaSmall (by decide +kernel) (by decide)

def splitV243 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x1111111000ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB243 : Ban 29 4 splitV243 := viaSmall (by decide +kernel) (by decide)

def splitV244 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x11111110ff00000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB244 : Ban 29 4 splitV244 := viaSmall (by decide +kernel) (by decide)

def splitV245 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x15555554000f000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB245 : Ban 29 4 splitV245 := viaSmall (by decide +kernel) (by decide)

def splitV246 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x1555555400ff000,0x199999980f00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB246 : Ban 29 4 splitV246 := viaSmall (by decide +kernel) (by decide)

def splitV247 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB247 : Ban 29 4 splitV247 := viaSmall (by decide +kernel) (by decide)

def splitV248 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB248 : Ban 29 4 splitV248 := viaSmall (by decide +kernel) (by decide)

def splitV249 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB249 : Ban 29 4 splitV249 := viaSmall (by decide +kernel) (by decide)

def splitV250 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB250 : Ban 29 4 splitV250 := viaSmall (by decide +kernel) (by decide)

def splitV251 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x1555555400ff000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB251 : Ban 29 4 splitV251 := viaSmall (by decide +kernel) (by decide)

def splitV252 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB252 : Ban 29 4 splitV252 := viaSmall (by decide +kernel) (by decide)

def splitV253 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x177777770fff0ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB253 : Ban 29 4 splitV253 := viaSmall (by decide +kernel) (by decide)

def splitV254 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB254 : Ban 29 4 splitV254 := viaSmall (by decide +kernel) (by decide)

def splitV255 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB255 : Ban 29 4 splitV255 := viaSmall (by decide +kernel) (by decide)

def splitV256 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x20000001f000f0f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB256 : Ban 29 4 splitV256 := viaSmall (by decide +kernel) (by decide)

def splitV257 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB257 : Ban 29 4 splitV257 := viaSmall (by decide +kernel) (by decide)

def splitV258 : List ℕ := [0x22222230f000ff,0x1555555400ff000,0x19999998ff00000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB258 : Ban 29 4 splitV258 := viaSmall (by decide +kernel) (by decide)

def splitV259 : List ℕ := [0x22222230f000ff,0x1555555400ff000,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB259 : Ban 29 4 splitV259 := viaSmall (by decide +kernel) (by decide)

def splitV260 : List ℕ := [0x22222230f000ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB260 : Ban 29 4 splitV260 := viaSmall (by decide +kernel) (by decide)

def splitV261 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ff0fff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB261 : Ban 29 4 splitV261 := viaSmall (by decide +kernel) (by decide)

def splitV262 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x177777770fff0ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB262 : Ban 29 4 splitV262 := viaSmall (by decide +kernel) (by decide)

def splitV263 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff000ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB263 : Ban 29 4 splitV263 := viaSmall (by decide +kernel) (by decide)

def splitV264 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB264 : Ban 29 5 splitV264 := viaBranch (ws := [splitV230,splitV231,splitV57,splitV146,splitV148,splitV232,splitV233,splitV234,splitV235,splitV236,splitV237,splitV238,splitV239,splitV240,splitV241,splitV242,splitV243,splitV244,splitV245,splitV246,splitV247,splitV248,splitV249,splitV250,splitV251,splitV252,splitV253,splitV254,splitV255,splitV256,splitV257,splitV258,splitV259,splitV260,splitV261,splitV262,splitV263,splitV137])
 (consBan splitB230 (consBan splitB231 (consBan splitB57 (consBan splitB146 (consBan splitB148 (consBan splitB232 (consBan splitB233 (consBan splitB234 (consBan splitB235 (consBan splitB236 (consBan splitB237 (consBan splitB238 (consBan splitB239 (consBan splitB240 (consBan splitB241 (consBan splitB242 (consBan splitB243 (consBan splitB244 (consBan splitB245 (consBan splitB246 (consBan splitB247 (consBan splitB248 (consBan splitB249 (consBan splitB250 (consBan splitB251 (consBan splitB252 (consBan splitB253 (consBan splitB254 (consBan splitB255 (consBan splitB256 (consBan splitB257 (consBan splitB258 (consBan splitB259 (consBan splitB260 (consBan splitB261 (consBan splitB262 (consBan splitB263 (consBan splitB137 (nilBan 29 4)))))))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV265 : List ℕ := [0xf00,0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB265 : Ban 29 4 splitV265 := viaSmall (by decide +kernel) (by decide)

def splitV266 : List ℕ := [0xf000000,0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB266 : Ban 29 4 splitV266 := viaSmall (by decide +kernel) (by decide)

def splitV267 : List ℕ := [0x22222220f000f0,0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB267 : Ban 29 4 splitV267 := viaSmall (by decide +kernel) (by decide)

def splitV268 : List ℕ := [0x222222300000ff,0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB268 : Ban 29 4 splitV268 := viaSmall (by decide +kernel) (by decide)

def splitV269 : List ℕ := [0x22222230f0000f,0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB269 : Ban 29 4 splitV269 := viaSmall (by decide +kernel) (by decide)

def splitV270 : List ℕ := [0x22222230f0000f,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB270 : Ban 29 4 splitV270 := viaSmall (by decide +kernel) (by decide)

def splitV271 : List ℕ := [0x22222230f000ff,0x88888880000000,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB271 : Ban 29 4 splitV271 := viaSmall (by decide +kernel) (by decide)

def splitV272 : List ℕ := [0x22222230f000ff,0x888888800f00f0,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB272 : Ban 29 4 splitV272 := viaSmall (by decide +kernel) (by decide)

def splitV273 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0xaaaaaab0ff0fff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB273 : Ban 29 4 splitV273 := viaSmall (by decide +kernel) (by decide)

def splitV274 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x11111110ff00000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB274 : Ban 29 4 splitV274 := viaSmall (by decide +kernel) (by decide)

def splitV275 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x199999980f00000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB275 : Ban 29 4 splitV275 := viaSmall (by decide +kernel) (by decide)

def splitV276 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB276 : Ban 29 4 splitV276 := viaSmall (by decide +kernel) (by decide)

def splitV277 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x1bbbbbbbff000ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB277 : Ban 29 4 splitV277 := viaSmall (by decide +kernel) (by decide)

def splitV278 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x244444450000f0f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB278 : Ban 29 4 splitV278 := viaSmall (by decide +kernel) (by decide)

def splitV279 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB279 : Ban 29 4 splitV279 := viaSmall (by decide +kernel) (by decide)

def splitV280 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f00000f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB280 : Ban 29 4 splitV280 := viaSmall (by decide +kernel) (by decide)

def splitV281 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x26666667ff00fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB281 : Ban 29 4 splitV281 := viaSmall (by decide +kernel) (by decide)

def splitV282 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB282 : Ban 29 4 splitV282 := viaSmall (by decide +kernel) (by decide)

def splitV283 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB283 : Ban 29 4 splitV283 := viaSmall (by decide +kernel) (by decide)

def splitV284 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB284 : Ban 29 4 splitV284 := viaSmall (by decide +kernel) (by decide)

def splitV285 : List ℕ := [0x22222230f000ff,0x19999998ff00000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB285 : Ban 29 4 splitV285 := viaSmall (by decide +kernel) (by decide)

def splitV286 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ff0fff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB286 : Ban 29 4 splitV286 := viaSmall (by decide +kernel) (by decide)

def splitV287 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB287 : Ban 29 5 splitV287 := viaBranch (ws := [splitV208,splitV265,splitV35,splitV58,splitV210,splitV266,splitV104,splitV267,splitV268,splitV269,splitV270,splitV271,splitV272,splitV220,splitV273,splitV274,splitV275,splitV222,splitV276,splitV277,splitV224,splitV278,splitV279,splitV280,splitV281,splitV282,splitV283,splitV284,splitV285,splitV286])
 (consBan splitB208 (consBan splitB265 (consBan splitB35 (consBan splitB58 (consBan splitB210 (consBan splitB266 (consBan splitB104 (consBan splitB267 (consBan splitB268 (consBan splitB269 (consBan splitB270 (consBan splitB271 (consBan splitB272 (consBan splitB220 (consBan splitB273 (consBan splitB274 (consBan splitB275 (consBan splitB222 (consBan splitB276 (consBan splitB277 (consBan splitB224 (consBan splitB278 (consBan splitB279 (consBan splitB280 (consBan splitB281 (consBan splitB282 (consBan splitB283 (consBan splitB284 (consBan splitB285 (consBan splitB286 (nilBan 29 4)))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV288 : List ℕ := [0x22222230f0f00f,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB288 : Ban 29 5 splitV288 := viaSmall (by decide +kernel) (by decide)

def splitV289 : List ℕ := [0x22222230f0f00f,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB289 : Ban 29 5 splitV289 := viaSmall (by decide +kernel) (by decide)

def splitV290 : List ℕ := [0xf00,0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB290 : Ban 29 4 splitV290 := viaSmall (by decide +kernel) (by decide)

def splitV291 : List ℕ := [0xf0000,0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB291 : Ban 29 4 splitV291 := viaSmall (by decide +kernel) (by decide)

def splitV292 : List ℕ := [0x22222220f0f000,0x22222230f0f00f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB292 : Ban 29 4 splitV292 := viaSmall (by decide +kernel) (by decide)

def splitV293 : List ℕ := [0x22222230f0000f,0x22222230f0f00f,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB293 : Ban 29 4 splitV293 := viaSmall (by decide +kernel) (by decide)

def splitV294 : List ℕ := [0x22222230f0f00f,0x444444400ff000,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB294 : Ban 29 4 splitV294 := viaSmall (by decide +kernel) (by decide)

def splitV295 : List ℕ := [0x22222230f0f00f,0x88888880000000,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB295 : Ban 29 4 splitV295 := viaSmall (by decide +kernel) (by decide)

def splitV296 : List ℕ := [0x22222230f0f00f,0x88888880000ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB296 : Ban 29 4 splitV296 := viaSmall (by decide +kernel) (by decide)

def splitV297 : List ℕ := [0x22222230f0f00f,0x888888800f00f0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB297 : Ban 29 4 splitV297 := viaSmall (by decide +kernel) (by decide)

def splitV298 : List ℕ := [0x22222230f0f00f,0x888888800f0ff0,0x8888888ff00000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB298 : Ban 29 4 splitV298 := viaSmall (by decide +kernel) (by decide)

def splitV299 : List ℕ := [0x22222230f0f00f,0x888888800f0ff0,0x1111111000ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB299 : Ban 29 4 splitV299 := viaSmall (by decide +kernel) (by decide)

def splitV300 : List ℕ := [0x22222230f0f00f,0x888888800f0ff0,0x15555554000f000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB300 : Ban 29 4 splitV300 := viaSmall (by decide +kernel) (by decide)

def splitV301 : List ℕ := [0x22222230f0f00f,0x888888800f0ff0,0x1555555400ff000,0x199999980f00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB301 : Ban 29 4 splitV301 := viaSmall (by decide +kernel) (by decide)

def splitV302 : List ℕ := [0x22222230f0f00f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB302 : Ban 29 4 splitV302 := viaSmall (by decide +kernel) (by decide)

def splitV303 : List ℕ := [0x22222230f0f00f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB303 : Ban 29 4 splitV303 := viaSmall (by decide +kernel) (by decide)

def splitV304 : List ℕ := [0x22222230f0f00f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB304 : Ban 29 4 splitV304 := viaSmall (by decide +kernel) (by decide)

def splitV305 : List ℕ := [0x22222230f0f00f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB305 : Ban 29 4 splitV305 := viaSmall (by decide +kernel) (by decide)

def splitV306 : List ℕ := [0x22222230f0f00f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB306 : Ban 29 4 splitV306 := viaSmall (by decide +kernel) (by decide)

def splitV307 : List ℕ := [0x22222230f0f00f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB307 : Ban 29 4 splitV307 := viaSmall (by decide +kernel) (by decide)

def splitV308 : List ℕ := [0x22222230f0f00f,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB308 : Ban 29 4 splitV308 := viaSmall (by decide +kernel) (by decide)

def splitV309 : List ℕ := [0x22222230f0f00f,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB309 : Ban 29 4 splitV309 := viaSmall (by decide +kernel) (by decide)

def splitV310 : List ℕ := [0x22222230f0f00f,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB310 : Ban 29 4 splitV310 := viaSmall (by decide +kernel) (by decide)

def splitV311 : List ℕ := [0x22222230f0f00f,0x888888800f0ff0,0x19999998ff00000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB311 : Ban 29 4 splitV311 := viaSmall (by decide +kernel) (by decide)

def splitV312 : List ℕ := [0x22222230f0f00f,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB312 : Ban 29 4 splitV312 := viaSmall (by decide +kernel) (by decide)

def splitV313 : List ℕ := [0x22222230f0f00f,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB313 : Ban 29 4 splitV313 := viaSmall (by decide +kernel) (by decide)

def splitV314 : List ℕ := [0x22222230f0f00f,0x11111110ff00000,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB314 : Ban 29 4 splitV314 := viaSmall (by decide +kernel) (by decide)

def splitV315 : List ℕ := [0x22222230f0f00f,0x15555554000f000,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB315 : Ban 29 4 splitV315 := viaSmall (by decide +kernel) (by decide)

def splitV316 : List ℕ := [0x22222230f0f00f,0x15555554000f000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB316 : Ban 29 4 splitV316 := viaSmall (by decide +kernel) (by decide)

def splitV317 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB317 : Ban 29 4 splitV317 := viaSmall (by decide +kernel) (by decide)

def splitV318 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB318 : Ban 29 4 splitV318 := viaSmall (by decide +kernel) (by decide)

def splitV319 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB319 : Ban 29 4 splitV319 := viaSmall (by decide +kernel) (by decide)

def splitV320 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f00000f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB320 : Ban 29 4 splitV320 := viaSmall (by decide +kernel) (by decide)

def splitV321 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB321 : Ban 29 4 splitV321 := viaSmall (by decide +kernel) (by decide)

def splitV322 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB322 : Ban 29 4 splitV322 := viaSmall (by decide +kernel) (by decide)

def splitV323 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x177777770fff00f,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB323 : Ban 29 4 splitV323 := viaSmall (by decide +kernel) (by decide)

def splitV324 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f00f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB324 : Ban 29 4 splitV324 := viaSmall (by decide +kernel) (by decide)

def splitV325 : List ℕ := [0x22222230f0f00f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB325 : Ban 29 5 splitV325 := viaBranch (ws := [splitV290,splitV16,splitV291,splitV36,splitV84,splitV146,splitV292,splitV149,splitV293,splitV233,splitV270,splitV294,splitV295,splitV296,splitV297,splitV298,splitV299,splitV300,splitV301,splitV302,splitV303,splitV304,splitV305,splitV306,splitV307,splitV308,splitV309,splitV310,splitV311,splitV312,splitV313,splitV314,splitV315,splitV316,splitV317,splitV318,splitV319,splitV320,splitV321,splitV322,splitV323,splitV324,splitV137])
 (consBan splitB290 (consBan splitB16 (consBan splitB291 (consBan splitB36 (consBan splitB84 (consBan splitB146 (consBan splitB292 (consBan splitB149 (consBan splitB293 (consBan splitB233 (consBan splitB270 (consBan splitB294 (consBan splitB295 (consBan splitB296 (consBan splitB297 (consBan splitB298 (consBan splitB299 (consBan splitB300 (consBan splitB301 (consBan splitB302 (consBan splitB303 (consBan splitB304 (consBan splitB305 (consBan splitB306 (consBan splitB307 (consBan splitB308 (consBan splitB309 (consBan splitB310 (consBan splitB311 (consBan splitB312 (consBan splitB313 (consBan splitB314 (consBan splitB315 (consBan splitB316 (consBan splitB317 (consBan splitB318 (consBan splitB319 (consBan splitB320 (consBan splitB321 (consBan splitB322 (consBan splitB323 (consBan splitB324 (consBan splitB137 (nilBan 29 4))))))))))))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV326 : List ℕ := [0xf00000,0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB326 : Ban 29 4 splitV326 := viaSmall (by decide +kernel) (by decide)

def splitV327 : List ℕ := [0xf000000,0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB327 : Ban 29 4 splitV327 := viaSmall (by decide +kernel) (by decide)

def splitV328 : List ℕ := [0x22222220f0f000,0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB328 : Ban 29 4 splitV328 := viaSmall (by decide +kernel) (by decide)

def splitV329 : List ℕ := [0x2222223000f00f,0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB329 : Ban 29 4 splitV329 := viaSmall (by decide +kernel) (by decide)

def splitV330 : List ℕ := [0x22222230f0000f,0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB330 : Ban 29 4 splitV330 := viaSmall (by decide +kernel) (by decide)

def splitV331 : List ℕ := [0x22222230f0f00f,0x44444440000000,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB331 : Ban 29 4 splitV331 := viaSmall (by decide +kernel) (by decide)

def splitV332 : List ℕ := [0x22222230f0f00f,0x444444400ff000,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB332 : Ban 29 4 splitV332 := viaSmall (by decide +kernel) (by decide)

def splitV333 : List ℕ := [0x22222230f0f00f,0x444444400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB333 : Ban 29 4 splitV333 := viaSmall (by decide +kernel) (by decide)

def splitV334 : List ℕ := [0x22222230f0f00f,0x8888888ff00000,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB334 : Ban 29 4 splitV334 := viaSmall (by decide +kernel) (by decide)

def splitV335 : List ℕ := [0x22222230f0f00f,0x111111100000000,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB335 : Ban 29 4 splitV335 := viaSmall (by decide +kernel) (by decide)

def splitV336 : List ℕ := [0x22222230f0f00f,0x1111111000ff000,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB336 : Ban 29 4 splitV336 := viaSmall (by decide +kernel) (by decide)

def splitV337 : List ℕ := [0x22222230f0f00f,0x1555555400f0000,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB337 : Ban 29 4 splitV337 := viaSmall (by decide +kernel) (by decide)

def splitV338 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x177777770fff00f,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB338 : Ban 29 4 splitV338 := viaSmall (by decide +kernel) (by decide)

def splitV339 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x199999980f00000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB339 : Ban 29 4 splitV339 := viaSmall (by decide +kernel) (by decide)

def splitV340 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x199999980f00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB340 : Ban 29 4 splitV340 := viaSmall (by decide +kernel) (by decide)

def splitV341 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x19999998f000000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB341 : Ban 29 4 splitV341 := viaSmall (by decide +kernel) (by decide)

def splitV342 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f00f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB342 : Ban 29 4 splitV342 := viaSmall (by decide +kernel) (by decide)

def splitV343 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB343 : Ban 29 4 splitV343 := viaSmall (by decide +kernel) (by decide)

def splitV344 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x20000001f000f0f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB344 : Ban 29 4 splitV344 := viaSmall (by decide +kernel) (by decide)

def splitV345 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444444f000f00,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB345 : Ban 29 4 splitV345 := viaSmall (by decide +kernel) (by decide)

def splitV346 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x244444450000f0f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB346 : Ban 29 4 splitV346 := viaSmall (by decide +kernel) (by decide)

def splitV347 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x26666667ff0ff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB347 : Ban 29 4 splitV347 := viaSmall (by decide +kernel) (by decide)

def splitV348 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB348 : Ban 29 4 splitV348 := viaSmall (by decide +kernel) (by decide)

def splitV349 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB349 : Ban 29 4 splitV349 := viaSmall (by decide +kernel) (by decide)

def splitV350 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB350 : Ban 29 4 splitV350 := viaSmall (by decide +kernel) (by decide)

def splitV351 : List ℕ := [0x22222230f0f00f,0x19999998ff00000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB351 : Ban 29 4 splitV351 := viaSmall (by decide +kernel) (by decide)

def splitV352 : List ℕ := [0x1555555400ff000,0x177777770fff00f,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB352 : Ban 29 4 splitV352 := viaSmall (by decide +kernel) (by decide)

def splitV353 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB353 : Ban 29 5 splitV353 := viaBranch (ws := [splitV6,splitV326,splitV327,splitV105,splitV328,splitV329,splitV330,splitV234,splitV331,splitV332,splitV333,splitV334,splitV335,splitV336,splitV337,splitV338,splitV339,splitV340,splitV341,splitV342,splitV343,splitV344,splitV345,splitV346,splitV347,splitV348,splitV349,splitV350,splitV351,splitV352])
 (consBan splitB6 (consBan splitB326 (consBan splitB327 (consBan splitB105 (consBan splitB328 (consBan splitB329 (consBan splitB330 (consBan splitB234 (consBan splitB331 (consBan splitB332 (consBan splitB333 (consBan splitB334 (consBan splitB335 (consBan splitB336 (consBan splitB337 (consBan splitB338 (consBan splitB339 (consBan splitB340 (consBan splitB341 (consBan splitB342 (consBan splitB343 (consBan splitB344 (consBan splitB345 (consBan splitB346 (consBan splitB347 (consBan splitB348 (consBan splitB349 (consBan splitB350 (consBan splitB351 (consBan splitB352 (nilBan 29 4)))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV354 : List ℕ := [0x22222230f0f0ff,0x44444440000000,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB354 : Ban 29 4 splitV354 := viaSmall (by decide +kernel) (by decide)

def splitV355 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1111111000ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB355 : Ban 29 4 splitV355 := viaSmall (by decide +kernel) (by decide)

def splitV356 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB356 : Ban 29 4 splitV356 := viaSmall (by decide +kernel) (by decide)

def splitV357 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB357 : Ban 29 4 splitV357 := viaSmall (by decide +kernel) (by decide)

def splitV358 : List ℕ := [0x22222230f0f0ff,0xccccccc00f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB358 : Ban 29 4 splitV358 := viaSmall (by decide +kernel) (by decide)

def splitV359 : List ℕ := [0x66666670f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB359 : Ban 29 4 splitV359 := viaSmall (by decide +kernel) (by decide)

def splitV360 : List ℕ := [0x22222230f0f0ff,0x44444440000000,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB360 : Ban 29 5 splitV360 := viaBranch (ws := [splitV114,splitV186,splitV235,splitV331,splitV354,splitV355,splitV356,splitV357,splitV358,splitV359])
 (consBan splitB114 (consBan splitB186 (consBan splitB235 (consBan splitB331 (consBan splitB354 (consBan splitB355 (consBan splitB356 (consBan splitB357 (consBan splitB358 (consBan splitB359 (nilBan 29 4)))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV361 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x88888880000ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB361 : Ban 29 4 splitV361 := viaSmall (by decide +kernel) (by decide)

def splitV362 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x888888800f0ff0,0x8888888ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB362 : Ban 29 4 splitV362 := viaSmall (by decide +kernel) (by decide)

def splitV363 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x888888800f0ff0,0x19999998ff00000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB363 : Ban 29 4 splitV363 := viaSmall (by decide +kernel) (by decide)

def splitV364 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x888888800f0ff0,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB364 : Ban 29 4 splitV364 := viaSmall (by decide +kernel) (by decide)

def splitV365 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x1555555400ff000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB365 : Ban 29 4 splitV365 := viaSmall (by decide +kernel) (by decide)

def splitV366 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB366 : Ban 29 4 splitV366 := viaSmall (by decide +kernel) (by decide)

def splitV367 : List ℕ := [0x22222230f0f0ff,0x88888880000ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB367 : Ban 29 4 splitV367 := viaSmall (by decide +kernel) (by decide)

def splitV368 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB368 : Ban 29 4 splitV368 := viaSmall (by decide +kernel) (by decide)

def splitV369 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB369 : Ban 29 4 splitV369 := viaSmall (by decide +kernel) (by decide)

def splitV370 : List ℕ := [0x22222230f0f0ff,0xccccccc00ffff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB370 : Ban 29 4 splitV370 := viaSmall (by decide +kernel) (by decide)

def splitV371 : List ℕ := [0x66666670fff0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB371 : Ban 29 4 splitV371 := viaSmall (by decide +kernel) (by decide)

def splitV372 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB372 : Ban 29 5 splitV372 := viaBranch (ws := [splitV150,splitV236,splitV10,splitV332,splitV361,splitV362,splitV363,splitV364,splitV365,splitV366,splitV367,splitV356,splitV368,splitV369,splitV370,splitV371])
 (consBan splitB150 (consBan splitB236 (consBan splitB10 (consBan splitB332 (consBan splitB361 (consBan splitB362 (consBan splitB363 (consBan splitB364 (consBan splitB365 (consBan splitB366 (consBan splitB367 (consBan splitB356 (consBan splitB368 (consBan splitB369 (consBan splitB370 (consBan splitB371 (nilBan 29 4)))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV373 : List ℕ := [0xf0,0x22222230f0f0ff,0x444444400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB373 : Ban 29 4 splitV373 := viaSmall (by decide +kernel) (by decide)

def splitV374 : List ℕ := [0xff000,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB374 : Ban 29 4 splitV374 := viaSmall (by decide +kernel) (by decide)

def splitV375 : List ℕ := [0xf00000,0x22222230f0f0ff,0x444444400ff000,0x888888800f0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB375 : Ban 29 4 splitV375 := viaSmall (by decide +kernel) (by decide)

def splitV376 : List ℕ := [0x2222223000f0ff,0x22222230f0f0ff,0x444444400ff000,0x888888800f0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB376 : Ban 29 4 splitV376 := viaSmall (by decide +kernel) (by decide)

def splitV377 : List ℕ := [0x22222230f0f00f,0x22222230f0f0ff,0x444444400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB377 : Ban 29 4 splitV377 := viaSmall (by decide +kernel) (by decide)

def splitV378 : List ℕ := [0x22222230f0f0ff,0x4444444000f000,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB378 : Ban 29 4 splitV378 := viaSmall (by decide +kernel) (by decide)

def splitV379 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x888888800f00f0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB379 : Ban 29 4 splitV379 := viaSmall (by decide +kernel) (by decide)

def splitV380 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x888888800f0ff0,0x11111110ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB380 : Ban 29 4 splitV380 := viaSmall (by decide +kernel) (by decide)

def splitV381 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x888888800f0ff0,0x199999980f00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB381 : Ban 29 4 splitV381 := viaSmall (by decide +kernel) (by decide)

def splitV382 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x888888800f0ff0,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB382 : Ban 29 4 splitV382 := viaSmall (by decide +kernel) (by decide)

def splitV383 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x888888800f0ff0,0x19999998ff00000,0x24444445f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB383 : Ban 29 4 splitV383 := viaSmall (by decide +kernel) (by decide)

def splitV384 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x888888800f0ff0,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB384 : Ban 29 4 splitV384 := viaSmall (by decide +kernel) (by decide)

def splitV385 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x888888800f0ff0,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB385 : Ban 29 4 splitV385 := viaSmall (by decide +kernel) (by decide)

def splitV386 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x888888800f0ff0,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB386 : Ban 29 4 splitV386 := viaSmall (by decide +kernel) (by decide)

def splitV387 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0xccccccc00ffff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB387 : Ban 29 4 splitV387 := viaSmall (by decide +kernel) (by decide)

def splitV388 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x19999998ff00000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB388 : Ban 29 4 splitV388 := viaSmall (by decide +kernel) (by decide)

def splitV389 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x19999998ff00000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB389 : Ban 29 4 splitV389 := viaSmall (by decide +kernel) (by decide)

def splitV390 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB390 : Ban 29 4 splitV390 := viaSmall (by decide +kernel) (by decide)

def splitV391 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0xccccccc00ffff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB391 : Ban 29 4 splitV391 := viaSmall (by decide +kernel) (by decide)

def splitV392 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB392 : Ban 29 4 splitV392 := viaSmall (by decide +kernel) (by decide)

def splitV393 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x24444445f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB393 : Ban 29 4 splitV393 := viaSmall (by decide +kernel) (by decide)

def splitV394 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB394 : Ban 29 4 splitV394 := viaSmall (by decide +kernel) (by decide)

def splitV395 : List ℕ := [0x444444400ff000,0x66666670fff0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB395 : Ban 29 4 splitV395 := viaSmall (by decide +kernel) (by decide)

def splitV396 : List ℕ := [0x444444400ff000,0x888888800f0ff0,0xaaaaaab0ffffff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB396 : Ban 29 4 splitV396 := viaSmall (by decide +kernel) (by decide)

def splitV397 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB397 : Ban 29 5 splitV397 := viaBranch (ws := [splitV373,splitV209,splitV59,splitV374,splitV375,splitV376,splitV24,splitV236,splitV25,splitV377,splitV294,splitV333,splitV378,splitV361,splitV379,splitV380,splitV381,splitV363,splitV382,splitV383,splitV384,splitV385,splitV364,splitV386,splitV387,splitV388,splitV389,splitV390,splitV391,splitV392,splitV393,splitV394,splitV395,splitV396])
 (consBan splitB373 (consBan splitB209 (consBan splitB59 (consBan splitB374 (consBan splitB375 (consBan splitB376 (consBan splitB24 (consBan splitB236 (consBan splitB25 (consBan splitB377 (consBan splitB294 (consBan splitB333 (consBan splitB378 (consBan splitB361 (consBan splitB379 (consBan splitB380 (consBan splitB381 (consBan splitB363 (consBan splitB382 (consBan splitB383 (consBan splitB384 (consBan splitB385 (consBan splitB364 (consBan splitB386 (consBan splitB387 (consBan splitB388 (consBan splitB389 (consBan splitB390 (consBan splitB391 (consBan splitB392 (consBan splitB393 (consBan splitB394 (consBan splitB395 (consBan splitB396 (nilBan 29 4)))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV398 : List ℕ := [0x22222230f0f0ff,0x88888880000000,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB398 : Ban 29 5 splitV398 := viaSmall (by decide +kernel) (by decide)

def splitV399 : List ℕ := [0x22222230f0f0ff,0x88888880000ff0,0x11111110ff00000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB399 : Ban 29 4 splitV399 := viaSmall (by decide +kernel) (by decide)

def splitV400 : List ℕ := [0x22222230f0f0ff,0x88888880000ff0,0x15555554000f000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB400 : Ban 29 4 splitV400 := viaSmall (by decide +kernel) (by decide)

def splitV401 : List ℕ := [0x22222230f0f0ff,0x88888880000ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB401 : Ban 29 4 splitV401 := viaSmall (by decide +kernel) (by decide)

def splitV402 : List ℕ := [0x22222230f0f0ff,0x88888880000ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB402 : Ban 29 4 splitV402 := viaSmall (by decide +kernel) (by decide)

def splitV403 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x11111110ff00000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB403 : Ban 29 4 splitV403 := viaSmall (by decide +kernel) (by decide)

def splitV404 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x2ccccccdf000fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB404 : Ban 29 4 splitV404 := viaSmall (by decide +kernel) (by decide)

def splitV405 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB405 : Ban 29 4 splitV405 := viaSmall (by decide +kernel) (by decide)

def splitV406 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB406 : Ban 29 4 splitV406 := viaSmall (by decide +kernel) (by decide)

def splitV407 : List ℕ := [0x88888880000ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB407 : Ban 29 4 splitV407 := viaSmall (by decide +kernel) (by decide)

def splitV408 : List ℕ := [0x888888800f0ff0,0xaaaaaab0f0ffff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB408 : Ban 29 4 splitV408 := viaSmall (by decide +kernel) (by decide)

def splitV409 : List ℕ := [0x22222230f0f0ff,0x88888880000ff0,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB409 : Ban 29 5 splitV409 := viaBranch (ws := [splitV187,splitV237,splitV296,splitV43,splitV399,splitV400,splitV401,splitV402,splitV403,splitV45,splitV404,splitV405,splitV406,splitV407,splitV408])
 (consBan splitB187 (consBan splitB237 (consBan splitB296 (consBan splitB43 (consBan splitB399 (consBan splitB400 (consBan splitB401 (consBan splitB402 (consBan splitB403 (consBan splitB45 (consBan splitB404 (consBan splitB405 (consBan splitB406 (consBan splitB407 (consBan splitB408 (nilBan 29 4))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV410 : List ℕ := [0x22222230f000ff,0x22222230f0f0ff,0x88888880000ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB410 : Ban 29 4 splitV410 := viaSmall (by decide +kernel) (by decide)

def splitV411 : List ℕ := [0x22222230f0f0ff,0x888888800000f0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB411 : Ban 29 4 splitV411 := viaSmall (by decide +kernel) (by decide)

def splitV412 : List ℕ := [0x22222230f0f0ff,0x88888880000ff0,0x1111111000ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB412 : Ban 29 4 splitV412 := viaSmall (by decide +kernel) (by decide)

def splitV413 : List ℕ := [0x22222230f0f0ff,0x88888880000ff0,0x1555555400ff000,0x199999980f00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB413 : Ban 29 4 splitV413 := viaSmall (by decide +kernel) (by decide)

def splitV414 : List ℕ := [0x22222230f0f0ff,0x88888880000ff0,0x1555555400ff000,0x19999998ff00000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB414 : Ban 29 4 splitV414 := viaSmall (by decide +kernel) (by decide)

def splitV415 : List ℕ := [0x22222230f0f0ff,0x88888880000ff0,0x1555555400ff000,0x19999998ff00000,0x2ccccccdf000fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB415 : Ban 29 4 splitV415 := viaSmall (by decide +kernel) (by decide)

def splitV416 : List ℕ := [0x22222230f0f0ff,0x88888880000ff0,0x1555555400ff000,0x19999998ff00000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB416 : Ban 29 4 splitV416 := viaSmall (by decide +kernel) (by decide)

def splitV417 : List ℕ := [0x22222230f0f0ff,0x88888880000ff0,0x1555555400ff000,0x19999998ff00ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB417 : Ban 29 4 splitV417 := viaSmall (by decide +kernel) (by decide)

def splitV418 : List ℕ := [0x22222230f0f0ff,0x88888880000ff0,0x1555555400ff000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB418 : Ban 29 4 splitV418 := viaSmall (by decide +kernel) (by decide)

def splitV419 : List ℕ := [0x22222230f0f0ff,0x88888880000ff0,0x19999998ff00000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB419 : Ban 29 4 splitV419 := viaSmall (by decide +kernel) (by decide)

def splitV420 : List ℕ := [0x22222230f0f0ff,0x88888880000ff0,0x19999998ff00000,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB420 : Ban 29 4 splitV420 := viaSmall (by decide +kernel) (by decide)

def splitV421 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x19999998ff00ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB421 : Ban 29 4 splitV421 := viaSmall (by decide +kernel) (by decide)

def splitV422 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB422 : Ban 29 4 splitV422 := viaSmall (by decide +kernel) (by decide)

def splitV423 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x2ccccccdf000fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB423 : Ban 29 4 splitV423 := viaSmall (by decide +kernel) (by decide)

def splitV424 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB424 : Ban 29 4 splitV424 := viaSmall (by decide +kernel) (by decide)

def splitV425 : List ℕ := [0x88888880000ff0,0xaaaaaab0f0ffff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB425 : Ban 29 4 splitV425 := viaSmall (by decide +kernel) (by decide)

def splitV426 : List ℕ := [0x88888880000ff0,0x1555555400ff000,0x177777770fff0ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB426 : Ban 29 4 splitV426 := viaSmall (by decide +kernel) (by decide)

def splitV427 : List ℕ := [0x88888880000ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB427 : Ban 29 4 splitV427 := viaSmall (by decide +kernel) (by decide)

def splitV428 : List ℕ := [0x88888880000ff0,0x1555555400ff000,0x19999998ff00000,0x24444444f000f00,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB428 : Ban 29 4 splitV428 := viaSmall (by decide +kernel) (by decide)

def splitV429 : List ℕ := [0x22222230f0f0ff,0x88888880000ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB429 : Ban 29 5 splitV429 := viaBranch (ws := [splitV51,splitV52,splitV7,splitV115,splitV152,splitV410,splitV238,splitV239,splitV73,splitV296,splitV74,splitV361,splitV411,splitV412,splitV399,splitV413,splitV414,splitV401,splitV415,splitV416,splitV417,splitV418,splitV402,splitV419,splitV420,splitV421,splitV422,splitV423,splitV424,splitV425,splitV426,splitV427,splitV428])
 (consBan splitB51 (consBan splitB52 (consBan splitB7 (consBan splitB115 (consBan splitB152 (consBan splitB410 (consBan splitB238 (consBan splitB239 (consBan splitB73 (consBan splitB296 (consBan splitB74 (consBan splitB361 (consBan splitB411 (consBan splitB412 (consBan splitB399 (consBan splitB413 (consBan splitB414 (consBan splitB401 (consBan splitB415 (consBan splitB416 (consBan splitB417 (consBan splitB418 (consBan splitB402 (consBan splitB419 (consBan splitB420 (consBan splitB421 (consBan splitB422 (consBan splitB423 (consBan splitB424 (consBan splitB425 (consBan splitB426 (consBan splitB427 (consBan splitB428 (nilBan 29 4))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV430 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x888888800f0ff0,0x1555555400ff000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB430 : Ban 29 4 splitV430 := viaSmall (by decide +kernel) (by decide)

def splitV431 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x11111110ff00000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB431 : Ban 29 4 splitV431 := viaSmall (by decide +kernel) (by decide)

def splitV432 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x15555554000f000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB432 : Ban 29 4 splitV432 := viaSmall (by decide +kernel) (by decide)

def splitV433 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB433 : Ban 29 4 splitV433 := viaSmall (by decide +kernel) (by decide)

def splitV434 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB434 : Ban 29 4 splitV434 := viaSmall (by decide +kernel) (by decide)

def splitV435 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB435 : Ban 29 4 splitV435 := viaSmall (by decide +kernel) (by decide)

def splitV436 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB436 : Ban 29 4 splitV436 := viaSmall (by decide +kernel) (by decide)

def splitV437 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998fff00f0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB437 : Ban 29 4 splitV437 := viaSmall (by decide +kernel) (by decide)

def splitV438 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ff0f0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB438 : Ban 29 4 splitV438 := viaSmall (by decide +kernel) (by decide)

def splitV439 : List ℕ := [0x888888800f00f0,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB439 : Ban 29 4 splitV439 := viaSmall (by decide +kernel) (by decide)

def splitV440 : List ℕ := [0x888888800f0ff0,0xaaaaaab0fff0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB440 : Ban 29 4 splitV440 := viaSmall (by decide +kernel) (by decide)

def splitV441 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB441 : Ban 29 5 splitV441 := viaBranch (ws := [splitV188,splitV272,splitV297,splitV43,splitV430,splitV431,splitV432,splitV433,splitV434,splitV435,splitV403,splitV44,splitV436,splitV437,splitV438,splitV439,splitV440])
 (consBan splitB188 (consBan splitB272 (consBan splitB297 (consBan splitB43 (consBan splitB430 (consBan splitB431 (consBan splitB432 (consBan splitB433 (consBan splitB434 (consBan splitB435 (consBan splitB403 (consBan splitB44 (consBan splitB436 (consBan splitB437 (consBan splitB438 (consBan splitB439 (consBan splitB440 (nilBan 29 4))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV442 : List ℕ := [0xf00000,0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB442 : Ban 29 4 splitV442 := viaSmall (by decide +kernel) (by decide)

def splitV443 : List ℕ := [0x22222220f0f0f0,0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB443 : Ban 29 4 splitV443 := viaSmall (by decide +kernel) (by decide)

def splitV444 : List ℕ := [0x2222223000f0ff,0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB444 : Ban 29 4 splitV444 := viaSmall (by decide +kernel) (by decide)

def splitV445 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x8888888ff00000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB445 : Ban 29 4 splitV445 := viaSmall (by decide +kernel) (by decide)

def splitV446 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x199999980f00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB446 : Ban 29 4 splitV446 := viaSmall (by decide +kernel) (by decide)

def splitV447 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x19999998ff00000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB447 : Ban 29 4 splitV447 := viaSmall (by decide +kernel) (by decide)

def splitV448 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x19999998ff00000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB448 : Ban 29 4 splitV448 := viaSmall (by decide +kernel) (by decide)

def splitV449 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x19999998ff00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB449 : Ban 29 4 splitV449 := viaSmall (by decide +kernel) (by decide)

def splitV450 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x19999998ff00000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB450 : Ban 29 4 splitV450 := viaSmall (by decide +kernel) (by decide)

def splitV451 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x19999998fff00f0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB451 : Ban 29 4 splitV451 := viaSmall (by decide +kernel) (by decide)

def splitV452 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB452 : Ban 29 4 splitV452 := viaSmall (by decide +kernel) (by decide)

def splitV453 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB453 : Ban 29 4 splitV453 := viaSmall (by decide +kernel) (by decide)

def splitV454 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB454 : Ban 29 4 splitV454 := viaSmall (by decide +kernel) (by decide)

def splitV455 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x19999998ff00000,0x1ddddddc00ff0f0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB455 : Ban 29 4 splitV455 := viaSmall (by decide +kernel) (by decide)

def splitV456 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x19999998ff00000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB456 : Ban 29 4 splitV456 := viaSmall (by decide +kernel) (by decide)

def splitV457 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x19999998fff00f0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB457 : Ban 29 4 splitV457 := viaSmall (by decide +kernel) (by decide)

def splitV458 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x1ddddddc00ff0f0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB458 : Ban 29 4 splitV458 := viaSmall (by decide +kernel) (by decide)

def splitV459 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB459 : Ban 29 4 splitV459 := viaSmall (by decide +kernel) (by decide)

def splitV460 : List ℕ := [0x22222230f0f0ff,0x19999998ff00000,0x1ddddddc00ff0f0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB460 : Ban 29 4 splitV460 := viaSmall (by decide +kernel) (by decide)

def splitV461 : List ℕ := [0x888888800f00f0,0xaaaaaab0fff0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB461 : Ban 29 4 splitV461 := viaSmall (by decide +kernel) (by decide)

def splitV462 : List ℕ := [0x888888800f00f0,0x1555555400ff000,0x177777770fff0ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB462 : Ban 29 4 splitV462 := viaSmall (by decide +kernel) (by decide)

def splitV463 : List ℕ := [0x888888800f00f0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB463 : Ban 29 4 splitV463 := viaSmall (by decide +kernel) (by decide)

def splitV464 : List ℕ := [0x888888800f00f0,0x1555555400ff000,0x19999998ff00000,0x24444444f000f00,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB464 : Ban 29 4 splitV464 := viaSmall (by decide +kernel) (by decide)

def splitV465 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB465 : Ban 29 5 splitV465 := viaBranch (ws := [splitV51,splitV53,splitV442,splitV106,splitV116,splitV443,splitV444,splitV153,splitV189,splitV240,splitV73,splitV297,splitV74,splitV379,splitV411,splitV445,splitV431,splitV432,splitV446,splitV447,splitV448,splitV434,splitV449,splitV450,splitV451,splitV452,splitV453,splitV454,splitV455,splitV456,splitV457,splitV458,splitV459,splitV460,splitV461,splitV462,splitV463,splitV464])
 (consBan splitB51 (consBan splitB53 (consBan splitB442 (consBan splitB106 (consBan splitB116 (consBan splitB443 (consBan splitB444 (consBan splitB153 (consBan splitB189 (consBan splitB240 (consBan splitB73 (consBan splitB297 (consBan splitB74 (consBan splitB379 (consBan splitB411 (consBan splitB445 (consBan splitB431 (consBan splitB432 (consBan splitB446 (consBan splitB447 (consBan splitB448 (consBan splitB434 (consBan splitB449 (consBan splitB450 (consBan splitB451 (consBan splitB452 (consBan splitB453 (consBan splitB454 (consBan splitB455 (consBan splitB456 (consBan splitB457 (consBan splitB458 (consBan splitB459 (consBan splitB460 (consBan splitB461 (consBan splitB462 (consBan splitB463 (consBan splitB464 (nilBan 29 4)))))))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV466 : List ℕ := [0x22222230f0f0ff,0x888888800f0f00,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB466 : Ban 29 5 splitV466 := viaSmall (by decide +kernel) (by decide)

def splitV467 : List ℕ := [0xf0ff0,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB467 : Ban 29 4 splitV467 := viaSmall (by decide +kernel) (by decide)

def splitV468 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB468 : Ban 29 4 splitV468 := viaSmall (by decide +kernel) (by decide)

def splitV469 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x1555555400ff000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB469 : Ban 29 4 splitV469 := viaSmall (by decide +kernel) (by decide)

def splitV470 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x1555555400ff000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB470 : Ban 29 4 splitV470 := viaSmall (by decide +kernel) (by decide)

def splitV471 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x19999998ff00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB471 : Ban 29 4 splitV471 := viaSmall (by decide +kernel) (by decide)

def splitV472 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB472 : Ban 29 4 splitV472 := viaSmall (by decide +kernel) (by decide)

def splitV473 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB473 : Ban 29 4 splitV473 := viaSmall (by decide +kernel) (by decide)

def splitV474 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x2ccccccdff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB474 : Ban 29 4 splitV474 := viaSmall (by decide +kernel) (by decide)

def splitV475 : List ℕ := [0x22222230f0f0ff,0x8888888fff0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB475 : Ban 29 4 splitV475 := viaSmall (by decide +kernel) (by decide)

def splitV476 : List ℕ := [0x888888800f0ff0,0xaaaaaabff0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB476 : Ban 29 4 splitV476 := viaSmall (by decide +kernel) (by decide)

def splitV477 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB477 : Ban 29 5 splitV477 := viaBranch (ws := [splitV60,splitV467,splitV154,splitV468,splitV241,splitV334,splitV362,splitV469,splitV470,splitV471,splitV472,splitV473,splitV474,splitV392,splitV475,splitV476])
 (consBan splitB60 (consBan splitB467 (consBan splitB154 (consBan splitB468 (consBan splitB241 (consBan splitB334 (consBan splitB362 (consBan splitB469 (consBan splitB470 (consBan splitB471 (consBan splitB472 (consBan splitB473 (consBan splitB474 (consBan splitB392 (consBan splitB475 (consBan splitB476 (nilBan 29 4)))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV478 : List ℕ := [0xf00000,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB478 : Ban 29 4 splitV478 := viaSmall (by decide +kernel) (by decide)

def splitV479 : List ℕ := [0xff00000,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB479 : Ban 29 4 splitV479 := viaSmall (by decide +kernel) (by decide)

def splitV480 : List ℕ := [0x22222220f0f0f0,0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x1555555400ff000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB480 : Ban 29 4 splitV480 := viaSmall (by decide +kernel) (by decide)

def splitV481 : List ℕ := [0x2222223000f0ff,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB481 : Ban 29 4 splitV481 := viaSmall (by decide +kernel) (by decide)

def splitV482 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB482 : Ban 29 4 splitV482 := viaSmall (by decide +kernel) (by decide)

def splitV483 : List ℕ := [0x22222230f000ff,0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB483 : Ban 29 4 splitV483 := viaSmall (by decide +kernel) (by decide)

def splitV484 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x88888880f00000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB484 : Ban 29 4 splitV484 := viaSmall (by decide +kernel) (by decide)

def splitV485 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x1111111000ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB485 : Ban 29 4 splitV485 := viaSmall (by decide +kernel) (by decide)

def splitV486 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x15555554000f000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB486 : Ban 29 4 splitV486 := viaSmall (by decide +kernel) (by decide)

def splitV487 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x1555555400ff000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB487 : Ban 29 4 splitV487 := viaSmall (by decide +kernel) (by decide)

def splitV488 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x1555555400ff000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB488 : Ban 29 4 splitV488 := viaSmall (by decide +kernel) (by decide)

def splitV489 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x1555555400ff000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB489 : Ban 29 4 splitV489 := viaSmall (by decide +kernel) (by decide)

def splitV490 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x1555555400ff000,0x2ccccccdff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB490 : Ban 29 4 splitV490 := viaSmall (by decide +kernel) (by decide)

def splitV491 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x1555555400ff000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB491 : Ban 29 4 splitV491 := viaSmall (by decide +kernel) (by decide)

def splitV492 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB492 : Ban 29 4 splitV492 := viaSmall (by decide +kernel) (by decide)

def splitV493 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB493 : Ban 29 4 splitV493 := viaSmall (by decide +kernel) (by decide)

def splitV494 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB494 : Ban 29 4 splitV494 := viaSmall (by decide +kernel) (by decide)

def splitV495 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888fff0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB495 : Ban 29 4 splitV495 := viaSmall (by decide +kernel) (by decide)

def splitV496 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x2ccccccdff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB496 : Ban 29 4 splitV496 := viaSmall (by decide +kernel) (by decide)

def splitV497 : List ℕ := [0x22222230f0f0ff,0x8888888ff00000,0x8888888fff0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB497 : Ban 29 4 splitV497 := viaSmall (by decide +kernel) (by decide)

def splitV498 : List ℕ := [0x22222230f0f0ff,0x8888888ff00000,0x1555555400ff000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB498 : Ban 29 4 splitV498 := viaSmall (by decide +kernel) (by decide)

def splitV499 : List ℕ := [0x22222230f0f0ff,0x8888888fff0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB499 : Ban 29 4 splitV499 := viaSmall (by decide +kernel) (by decide)

def splitV500 : List ℕ := [0x888888800f0ff0,0x8888888ff00000,0xaaaaaab0ffffff,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB500 : Ban 29 4 splitV500 := viaSmall (by decide +kernel) (by decide)

def splitV501 : List ℕ := [0x888888800f0ff0,0x8888888ff00000,0xaaaaaabff0f0ff,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB501 : Ban 29 4 splitV501 := viaSmall (by decide +kernel) (by decide)

def splitV502 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB502 : Ban 29 5 splitV502 := viaBranch (ws := [splitV8,splitV60,splitV478,splitV479,splitV85,splitV480,splitV481,splitV154,splitV482,splitV483,splitV298,splitV445,splitV484,splitV485,splitV486,splitV487,splitV469,splitV488,splitV489,splitV490,splitV491,splitV492,splitV472,splitV493,splitV494,splitV495,splitV369,splitV496,splitV497,splitV498,splitV499,splitV500,splitV501])
 (consBan splitB8 (consBan splitB60 (consBan splitB478 (consBan splitB479 (consBan splitB85 (consBan splitB480 (consBan splitB481 (consBan splitB154 (consBan splitB482 (consBan splitB483 (consBan splitB298 (consBan splitB445 (consBan splitB484 (consBan splitB485 (consBan splitB486 (consBan splitB487 (consBan splitB469 (consBan splitB488 (consBan splitB489 (consBan splitB490 (consBan splitB491 (consBan splitB492 (consBan splitB472 (consBan splitB493 (consBan splitB494 (consBan splitB495 (consBan splitB369 (consBan splitB496 (consBan splitB497 (consBan splitB498 (consBan splitB499 (consBan splitB500 (consBan splitB501 (nilBan 29 4))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV503 : List ℕ := [0x10000f0f,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB503 : Ban 29 4 splitV503 := viaSmall (by decide +kernel) (by decide)

def splitV504 : List ℕ := [0x22222220f0f0f0,0x888888800f0ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB504 : Ban 29 4 splitV504 := viaSmall (by decide +kernel) (by decide)

def splitV505 : List ℕ := [0x2222223000f0ff,0x888888800f0ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB505 : Ban 29 4 splitV505 := viaSmall (by decide +kernel) (by decide)

def splitV506 : List ℕ := [0x222222300fffff,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB506 : Ban 29 4 splitV506 := viaSmall (by decide +kernel) (by decide)

def splitV507 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0xaaaaaaa0fff0f0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB507 : Ban 29 4 splitV507 := viaSmall (by decide +kernel) (by decide)

def splitV508 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0xaaaaaab0f00fff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB508 : Ban 29 4 splitV508 := viaSmall (by decide +kernel) (by decide)

def splitV509 : List ℕ := [0x22222230f0f0ff,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB509 : Ban 29 4 splitV509 := viaSmall (by decide +kernel) (by decide)

def splitV510 : List ℕ := [0x22222230f0f0ff,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB510 : Ban 29 4 splitV510 := viaSmall (by decide +kernel) (by decide)

def splitV511 : List ℕ := [0x22222230f0f0ff,0xaaaaaab0ffffff,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB511 : Ban 29 4 splitV511 := viaSmall (by decide +kernel) (by decide)

def splitV512 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB512 : Ban 29 5 splitV512 := viaBranch (ws := [splitV23,splitV374,splitV92,splitV503,splitV504,splitV505,splitV506,splitV221,splitV73,splitV313,splitV484,splitV507,splitV508,splitV509,splitV510,splitV511])
 (consBan splitB23 (consBan splitB374 (consBan splitB92 (consBan splitB503 (consBan splitB504 (consBan splitB505 (consBan splitB506 (consBan splitB221 (consBan splitB73 (consBan splitB313 (consBan splitB484 (consBan splitB507 (consBan splitB508 (consBan splitB509 (consBan splitB510 (consBan splitB511 (nilBan 29 4)))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV513 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x111111100000000,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB513 : Ban 29 5 splitV513 := viaSmall (by decide +kernel) (by decide)

def splitV514 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x8888888ff00000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB514 : Ban 29 4 splitV514 := viaSmall (by decide +kernel) (by decide)

def splitV515 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1111111000ff000,0x19999998ff00000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB515 : Ban 29 4 splitV515 := viaSmall (by decide +kernel) (by decide)

def splitV516 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1111111000ff000,0x19999998ff00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB516 : Ban 29 4 splitV516 := viaSmall (by decide +kernel) (by decide)

def splitV517 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB517 : Ban 29 4 splitV517 := viaSmall (by decide +kernel) (by decide)

def splitV518 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB518 : Ban 29 4 splitV518 := viaSmall (by decide +kernel) (by decide)

def splitV519 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x1999999800ffff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB519 : Ban 29 4 splitV519 := viaSmall (by decide +kernel) (by decide)

def splitV520 : List ℕ := [0x888888800f0ff0,0x133333330fff0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB520 : Ban 29 4 splitV520 := viaSmall (by decide +kernel) (by decide)

def splitV521 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1111111000ff000,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB521 : Ban 29 5 splitV521 := viaBranch (ws := [splitV117,splitV192,splitV243,splitV10,splitV336,splitV412,splitV367,splitV485,splitV514,splitV515,splitV516,splitV517,splitV518,splitV519,splitV520])
 (consBan splitB117 (consBan splitB192 (consBan splitB243 (consBan splitB10 (consBan splitB336 (consBan splitB412 (consBan splitB367 (consBan splitB485 (consBan splitB514 (consBan splitB515 (consBan splitB516 (consBan splitB517 (consBan splitB518 (consBan splitB519 (consBan splitB520 (nilBan 29 4))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV522 : List ℕ := [0x22222220f0f0f0,0x22222230f0f0ff,0x888888800f0ff0,0x1111111000ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB522 : Ban 29 4 splitV522 := viaSmall (by decide +kernel) (by decide)

def splitV523 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x11111110000f000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB523 : Ban 29 4 splitV523 := viaSmall (by decide +kernel) (by decide)

def splitV524 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1111111000ff000,0x11111110ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB524 : Ban 29 4 splitV524 := viaSmall (by decide +kernel) (by decide)

def splitV525 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1111111000ff000,0x19999998ff00000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB525 : Ban 29 4 splitV525 := viaSmall (by decide +kernel) (by decide)

def splitV526 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1111111000ff000,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB526 : Ban 29 4 splitV526 := viaSmall (by decide +kernel) (by decide)

def splitV527 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1111111000ff000,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB527 : Ban 29 4 splitV527 := viaSmall (by decide +kernel) (by decide)

def splitV528 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1111111000ff000,0x19999998ff00000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB528 : Ban 29 4 splitV528 := viaSmall (by decide +kernel) (by decide)

def splitV529 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1111111000ff000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB529 : Ban 29 4 splitV529 := viaSmall (by decide +kernel) (by decide)

def splitV530 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1111111000ff000,0x19999998ffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB530 : Ban 29 4 splitV530 := viaSmall (by decide +kernel) (by decide)

def splitV531 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1999999800ffff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB531 : Ban 29 4 splitV531 := viaSmall (by decide +kernel) (by decide)

def splitV532 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x19999998ffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB532 : Ban 29 4 splitV532 := viaSmall (by decide +kernel) (by decide)

def splitV533 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB533 : Ban 29 4 splitV533 := viaSmall (by decide +kernel) (by decide)

def splitV534 : List ℕ := [0x22222230f0f0ff,0x1111111000ff000,0x1999999800ffff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB534 : Ban 29 4 splitV534 := viaSmall (by decide +kernel) (by decide)

def splitV535 : List ℕ := [0x22222230f0f0ff,0x1111111000ff000,0x19999998ff00000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB535 : Ban 29 4 splitV535 := viaSmall (by decide +kernel) (by decide)

def splitV536 : List ℕ := [0x22222230f0f0ff,0x1999999800ffff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB536 : Ban 29 4 splitV536 := viaSmall (by decide +kernel) (by decide)

def splitV537 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ffffff,0x1111111000ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB537 : Ban 29 4 splitV537 := viaSmall (by decide +kernel) (by decide)

def splitV538 : List ℕ := [0x888888800f0ff0,0x1111111000ff000,0x133333330fff0ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB538 : Ban 29 4 splitV538 := viaSmall (by decide +kernel) (by decide)

def splitV539 : List ℕ := [0x888888800f0ff0,0x1111111000ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB539 : Ban 29 4 splitV539 := viaSmall (by decide +kernel) (by decide)

def splitV540 : List ℕ := [0x888888800f0ff0,0x1111111000ff000,0x19999998ff00000,0x24444444f000f00,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB540 : Ban 29 4 splitV540 := viaSmall (by decide +kernel) (by decide)

def splitV541 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1111111000ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB541 : Ban 29 5 splitV541 := viaBranch (ws := [splitV209,splitV61,splitV374,splitV107,splitV118,splitV119,splitV522,splitV156,splitV24,splitV243,splitV25,splitV299,splitV412,splitV485,splitV523,splitV524,splitV525,splitV526,splitV527,splitV516,splitV528,splitV529,splitV530,splitV531,splitV532,splitV533,splitV534,splitV535,splitV536,splitV537,splitV538,splitV539,splitV540])
 (consBan splitB209 (consBan splitB61 (consBan splitB374 (consBan splitB107 (consBan splitB118 (consBan splitB119 (consBan splitB522 (consBan splitB156 (consBan splitB24 (consBan splitB243 (consBan splitB25 (consBan splitB299 (consBan splitB412 (consBan splitB485 (consBan splitB523 (consBan splitB524 (consBan splitB525 (consBan splitB526 (consBan splitB527 (consBan splitB516 (consBan splitB528 (consBan splitB529 (consBan splitB530 (consBan splitB531 (consBan splitB532 (consBan splitB533 (consBan splitB534 (consBan splitB535 (consBan splitB536 (consBan splitB537 (consBan splitB538 (consBan splitB539 (consBan splitB540 (nilBan 29 4))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV542 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x11111110ff00000,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB542 : Ban 29 5 splitV542 := viaSmall (by decide +kernel) (by decide)

def splitV543 : List ℕ := [0xf0,0x22222230f0f0ff,0x11111110ff00000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB543 : Ban 29 4 splitV543 := viaSmall (by decide +kernel) (by decide)

def splitV544 : List ℕ := [0x22222230f0f00f,0x22222230f0f0ff,0x11111110ff00000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB544 : Ban 29 4 splitV544 := viaSmall (by decide +kernel) (by decide)

def splitV545 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x111111100f00000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB545 : Ban 29 4 splitV545 := viaSmall (by decide +kernel) (by decide)

def splitV546 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x11111110ff00000,0x1555555400ff000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB546 : Ban 29 4 splitV546 := viaSmall (by decide +kernel) (by decide)

def splitV547 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x11111110ff00000,0x1555555400ff000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB547 : Ban 29 4 splitV547 := viaSmall (by decide +kernel) (by decide)

def splitV548 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x11111110ff00000,0x1555555400ff000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB548 : Ban 29 4 splitV548 := viaSmall (by decide +kernel) (by decide)

def splitV549 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x11111110ff00000,0x1555555400ff000,0x35555555ff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB549 : Ban 29 4 splitV549 := viaSmall (by decide +kernel) (by decide)

def splitV550 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x11111110ff00000,0x15555554ffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB550 : Ban 29 4 splitV550 := viaSmall (by decide +kernel) (by decide)

def splitV551 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x11111110ff00000,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB551 : Ban 29 4 splitV551 := viaSmall (by decide +kernel) (by decide)

def splitV552 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x15555554ffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB552 : Ban 29 4 splitV552 := viaSmall (by decide +kernel) (by decide)

def splitV553 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x35555555ff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB553 : Ban 29 4 splitV553 := viaSmall (by decide +kernel) (by decide)

def splitV554 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x35555555ff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB554 : Ban 29 4 splitV554 := viaSmall (by decide +kernel) (by decide)

def splitV555 : List ℕ := [0x22222230f0f0ff,0x11111110ff00000,0x1555555400ff000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB555 : Ban 29 4 splitV555 := viaSmall (by decide +kernel) (by decide)

def splitV556 : List ℕ := [0x22222230f0f0ff,0x11111110ff00000,0x1555555400ff000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB556 : Ban 29 4 splitV556 := viaSmall (by decide +kernel) (by decide)

def splitV557 : List ℕ := [0x22222230f0f0ff,0x11111110ff00000,0x1555555400ff000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB557 : Ban 29 4 splitV557 := viaSmall (by decide +kernel) (by decide)

def splitV558 : List ℕ := [0x888888800f0ff0,0x11111110ff00000,0x13333333ff0f0ff,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB558 : Ban 29 4 splitV558 := viaSmall (by decide +kernel) (by decide)

def splitV559 : List ℕ := [0x888888800f0ff0,0x11111110ff00000,0x1555555400ff000,0x177777770fff0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB559 : Ban 29 4 splitV559 := viaSmall (by decide +kernel) (by decide)

def splitV560 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x11111110ff00000,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB560 : Ban 29 5 splitV560 := viaBranch (ws := [splitV543,splitV478,splitV479,splitV481,splitV157,splitV482,splitV244,splitV544,splitV380,splitV399,splitV431,splitV524,splitV545,splitV546,splitV547,splitV548,splitV549,splitV550,splitV551,splitV552,splitV47,splitV553,splitV554,splitV555,splitV556,splitV557,splitV558,splitV559])
 (consBan splitB543 (consBan splitB478 (consBan splitB479 (consBan splitB481 (consBan splitB157 (consBan splitB482 (consBan splitB244 (consBan splitB544 (consBan splitB380 (consBan splitB399 (consBan splitB431 (consBan splitB524 (consBan splitB545 (consBan splitB546 (consBan splitB547 (consBan splitB548 (consBan splitB549 (consBan splitB550 (consBan splitB551 (consBan splitB552 (consBan splitB47 (consBan splitB553 (consBan splitB554 (consBan splitB555 (consBan splitB556 (consBan splitB557 (consBan splitB558 (consBan splitB559 (nilBan 29 4)))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV561 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x15555554000f000,0x19999998ff00000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB561 : Ban 29 4 splitV561 := viaSmall (by decide +kernel) (by decide)

def splitV562 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x15555554000f000,0x19999998ff00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB562 : Ban 29 4 splitV562 := viaSmall (by decide +kernel) (by decide)

def splitV563 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x35555555f00ff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB563 : Ban 29 4 splitV563 := viaSmall (by decide +kernel) (by decide)

def splitV564 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcff0f000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB564 : Ban 29 4 splitV564 := viaSmall (by decide +kernel) (by decide)

def splitV565 : List ℕ := [0x22222230f0f0ff,0x15555554000f000,0x1555555400ff000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB565 : Ban 29 4 splitV565 := viaSmall (by decide +kernel) (by decide)

def splitV566 : List ℕ := [0x22222230f0f0ff,0x15555554000f000,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB566 : Ban 29 4 splitV566 := viaSmall (by decide +kernel) (by decide)

def splitV567 : List ℕ := [0x888888800f0ff0,0x15555554000f000,0x177777770fff0ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB567 : Ban 29 4 splitV567 := viaSmall (by decide +kernel) (by decide)

def splitV568 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x177777770f0f0ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB568 : Ban 29 4 splitV568 := viaSmall (by decide +kernel) (by decide)

def splitV569 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x15555554000f000,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB569 : Ban 29 5 splitV569 := viaBranch (ws := [splitV193,splitV245,splitV10,splitV315,splitV400,splitV486,splitV514,splitV561,splitV562,splitV356,splitV563,splitV564,splitV565,splitV566,splitV422,splitV567,splitV568])
 (consBan splitB193 (consBan splitB245 (consBan splitB10 (consBan splitB315 (consBan splitB400 (consBan splitB486 (consBan splitB514 (consBan splitB561 (consBan splitB562 (consBan splitB356 (consBan splitB563 (consBan splitB564 (consBan splitB565 (consBan splitB566 (consBan splitB422 (consBan splitB567 (consBan splitB568 (nilBan 29 4))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV570 : List ℕ := [0xf0,0x22222230f0f0ff,0x15555554000f000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB570 : Ban 29 4 splitV570 := viaSmall (by decide +kernel) (by decide)

def splitV571 : List ℕ := [0x22222220f0f0f0,0x22222230f0f0ff,0x888888800f0ff0,0x15555554000f000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB571 : Ban 29 4 splitV571 := viaSmall (by decide +kernel) (by decide)

def splitV572 : List ℕ := [0x22222230f0f00f,0x22222230f0f0ff,0x15555554000f000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB572 : Ban 29 4 splitV572 := viaSmall (by decide +kernel) (by decide)

def splitV573 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x15555554000f000,0x199999980f00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB573 : Ban 29 4 splitV573 := viaSmall (by decide +kernel) (by decide)

def splitV574 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x15555554000f000,0x19999998ff00000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB574 : Ban 29 4 splitV574 := viaSmall (by decide +kernel) (by decide)

def splitV575 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x15555554000f000,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB575 : Ban 29 4 splitV575 := viaSmall (by decide +kernel) (by decide)

def splitV576 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x15555554000f000,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB576 : Ban 29 4 splitV576 := viaSmall (by decide +kernel) (by decide)

def splitV577 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x15555554000f000,0x19999998ff00000,0x35555555f00ff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB577 : Ban 29 4 splitV577 := viaSmall (by decide +kernel) (by decide)

def splitV578 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x15555554000f000,0x19999998ff00000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB578 : Ban 29 4 splitV578 := viaSmall (by decide +kernel) (by decide)

def splitV579 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x15555554000f000,0x1ddddddcff0f000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB579 : Ban 29 4 splitV579 := viaSmall (by decide +kernel) (by decide)

def splitV580 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x15555554000f000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB580 : Ban 29 4 splitV580 := viaSmall (by decide +kernel) (by decide)

def splitV581 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddcff0f000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB581 : Ban 29 4 splitV581 := viaSmall (by decide +kernel) (by decide)

def splitV582 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x35555555f00ff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB582 : Ban 29 4 splitV582 := viaSmall (by decide +kernel) (by decide)

def splitV583 : List ℕ := [0x22222230f0f0ff,0x15555554000f000,0x19999998ff00000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB583 : Ban 29 4 splitV583 := viaSmall (by decide +kernel) (by decide)

def splitV584 : List ℕ := [0x22222230f0f0ff,0x15555554000f000,0x19999998ff00000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB584 : Ban 29 4 splitV584 := viaSmall (by decide +kernel) (by decide)

def splitV585 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ffffff,0x15555554000f000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB585 : Ban 29 4 splitV585 := viaSmall (by decide +kernel) (by decide)

def splitV586 : List ℕ := [0x888888800f0ff0,0x15555554000f000,0x177777770f0f0ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB586 : Ban 29 4 splitV586 := viaSmall (by decide +kernel) (by decide)

def splitV587 : List ℕ := [0x888888800f0ff0,0x15555554000f000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB587 : Ban 29 4 splitV587 := viaSmall (by decide +kernel) (by decide)

def splitV588 : List ℕ := [0x888888800f0ff0,0x15555554000f000,0x19999998ff00000,0x24444444f000f00,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB588 : Ban 29 4 splitV588 := viaSmall (by decide +kernel) (by decide)

def splitV589 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x15555554000f000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB589 : Ban 29 5 splitV589 := viaBranch (ws := [splitV570,splitV209,splitV39,splitV86,splitV120,splitV571,splitV158,splitV24,splitV245,splitV25,splitV572,splitV300,splitV316,splitV378,splitV432,splitV486,splitV523,splitV573,splitV561,splitV574,splitV575,splitV576,splitV577,splitV578,splitV579,splitV580,splitV406,splitV581,splitV582,splitV583,splitV566,splitV584,splitV585,splitV586,splitV587,splitV588])
 (consBan splitB570 (consBan splitB209 (consBan splitB39 (consBan splitB86 (consBan splitB120 (consBan splitB571 (consBan splitB158 (consBan splitB24 (consBan splitB245 (consBan splitB25 (consBan splitB572 (consBan splitB300 (consBan splitB316 (consBan splitB378 (consBan splitB432 (consBan splitB486 (consBan splitB523 (consBan splitB573 (consBan splitB561 (consBan splitB574 (consBan splitB575 (consBan splitB576 (consBan splitB577 (consBan splitB578 (consBan splitB579 (consBan splitB580 (consBan splitB406 (consBan splitB581 (consBan splitB582 (consBan splitB583 (consBan splitB566 (consBan splitB584 (consBan splitB585 (consBan splitB586 (consBan splitB587 (consBan splitB588 (nilBan 29 4)))))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV590 : List ℕ := [0x22222230f000ff,0x888888800f0ff0,0x1555555400f0000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB590 : Ban 29 4 splitV590 := viaSmall (by decide +kernel) (by decide)

def splitV591 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400f0000,0x19999998ff00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB591 : Ban 29 4 splitV591 := viaSmall (by decide +kernel) (by decide)

def splitV592 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400f0000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB592 : Ban 29 4 splitV592 := viaSmall (by decide +kernel) (by decide)

def splitV593 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x35555555f0f0f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB593 : Ban 29 4 splitV593 := viaSmall (by decide +kernel) (by decide)

def splitV594 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcfff0000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB594 : Ban 29 4 splitV594 := viaSmall (by decide +kernel) (by decide)

def splitV595 : List ℕ := [0x22222230f0f0ff,0x1555555400f0000,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB595 : Ban 29 4 splitV595 := viaSmall (by decide +kernel) (by decide)

def splitV596 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x1ddddddc00f0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB596 : Ban 29 4 splitV596 := viaSmall (by decide +kernel) (by decide)

def splitV597 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400f0000,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB597 : Ban 29 5 splitV597 := viaBranch (ws := [splitV209,splitV93,splitV194,splitV590,splitV337,splitV367,splitV514,splitV591,splitV592,splitV356,splitV593,splitV594,splitV595,splitV596,splitV262])
 (consBan splitB209 (consBan splitB93 (consBan splitB194 (consBan splitB590 (consBan splitB337 (consBan splitB367 (consBan splitB514 (consBan splitB591 (consBan splitB592 (consBan splitB356 (consBan splitB593 (consBan splitB594 (consBan splitB595 (consBan splitB596 (consBan splitB262 (nilBan 29 4))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV598 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x177777770fff0ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB598 : Ban 29 5 splitV598 := viaSmall (by decide +kernel) (by decide)

def splitV599 : List ℕ := [0x22222230f0f0ff,0x444444400ff000,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB599 : Ban 29 4 splitV599 := viaSmall (by decide +kernel) (by decide)

def splitV600 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x199999980f00000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB600 : Ban 29 4 splitV600 := viaSmall (by decide +kernel) (by decide)

def splitV601 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x199999980f00000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB601 : Ban 29 4 splitV601 := viaSmall (by decide +kernel) (by decide)

def splitV602 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB602 : Ban 29 4 splitV602 := viaSmall (by decide +kernel) (by decide)

def splitV603 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x199999980f00000,0x19999998ff00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB603 : Ban 29 4 splitV603 := viaSmall (by decide +kernel) (by decide)

def splitV604 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc0fff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB604 : Ban 29 4 splitV604 := viaSmall (by decide +kernel) (by decide)

def splitV605 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x199999980f00000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB605 : Ban 29 4 splitV605 := viaSmall (by decide +kernel) (by decide)

def splitV606 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x199999980ff0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB606 : Ban 29 4 splitV606 := viaSmall (by decide +kernel) (by decide)

def splitV607 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x199999980f00000,0x1bbbbbbbff0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB607 : Ban 29 4 splitV607 := viaSmall (by decide +kernel) (by decide)

def splitV608 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbb0f0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB608 : Ban 29 4 splitV608 := viaSmall (by decide +kernel) (by decide)

def splitV609 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x199999980f00000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB609 : Ban 29 5 splitV609 := viaBranch (ws := [splitV62,splitV467,splitV159,splitV468,splitV275,splitV339,splitV381,splitV599,splitV600,splitV601,splitV602,splitV603,splitV604,splitV605,splitV606,splitV607,splitV608])
 (consBan splitB62 (consBan splitB467 (consBan splitB159 (consBan splitB468 (consBan splitB275 (consBan splitB339 (consBan splitB381 (consBan splitB599 (consBan splitB600 (consBan splitB601 (consBan splitB602 (consBan splitB603 (consBan splitB604 (consBan splitB605 (consBan splitB606 (consBan splitB607 (consBan splitB608 (nilBan 29 4))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV610 : List ℕ := [0xf0,0x22222230f0f0ff,0x1555555400ff000,0x199999980f00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB610 : Ban 29 4 splitV610 := viaSmall (by decide +kernel) (by decide)

def splitV611 : List ℕ := [0x22222220f0f0f0,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x199999980f00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB611 : Ban 29 4 splitV611 := viaSmall (by decide +kernel) (by decide)

def splitV612 : List ℕ := [0x22222230f0f00f,0x22222230f0f0ff,0x1555555400ff000,0x199999980f00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB612 : Ban 29 4 splitV612 := viaSmall (by decide +kernel) (by decide)

def splitV613 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x199999980f00000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB613 : Ban 29 4 splitV613 := viaSmall (by decide +kernel) (by decide)

def splitV614 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x199999980f00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB614 : Ban 29 4 splitV614 := viaSmall (by decide +kernel) (by decide)

def splitV615 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x199999980f00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB615 : Ban 29 4 splitV615 := viaSmall (by decide +kernel) (by decide)

def splitV616 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x199999980f00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB616 : Ban 29 4 splitV616 := viaSmall (by decide +kernel) (by decide)

def splitV617 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x199999980ff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB617 : Ban 29 4 splitV617 := viaSmall (by decide +kernel) (by decide)

def splitV618 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddc0fff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB618 : Ban 29 4 splitV618 := viaSmall (by decide +kernel) (by decide)

def splitV619 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB619 : Ban 29 4 splitV619 := viaSmall (by decide +kernel) (by decide)

def splitV620 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x199999980f00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB620 : Ban 29 4 splitV620 := viaSmall (by decide +kernel) (by decide)

def splitV621 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x199999980f00000,0x1ddddddc0fff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB621 : Ban 29 4 splitV621 := viaSmall (by decide +kernel) (by decide)

def splitV622 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x199999980f00000,0x199999980ff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB622 : Ban 29 4 splitV622 := viaSmall (by decide +kernel) (by decide)

def splitV623 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x199999980f00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB623 : Ban 29 4 splitV623 := viaSmall (by decide +kernel) (by decide)

def splitV624 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x199999980f00000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB624 : Ban 29 4 splitV624 := viaSmall (by decide +kernel) (by decide)

def splitV625 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x199999980f00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB625 : Ban 29 4 splitV625 := viaSmall (by decide +kernel) (by decide)

def splitV626 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x177777770fff0ff,0x199999980f00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB626 : Ban 29 4 splitV626 := viaSmall (by decide +kernel) (by decide)

def splitV627 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x199999980f00000,0x1bbbbbbb0f0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB627 : Ban 29 4 splitV627 := viaSmall (by decide +kernel) (by decide)

def splitV628 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x199999980f00000,0x24444444f000f00,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB628 : Ban 29 4 splitV628 := viaSmall (by decide +kernel) (by decide)

def splitV629 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x199999980f00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB629 : Ban 29 5 splitV629 := viaBranch (ws := [splitV610,splitV62,splitV478,splitV108,splitV121,splitV611,splitV481,splitV159,splitV482,splitV246,splitV612,splitV301,splitV340,splitV381,splitV413,splitV446,splitV484,splitV545,splitV573,splitV613,splitV614,splitV615,splitV616,splitV601,splitV617,splitV618,splitV619,splitV620,splitV621,splitV622,splitV623,splitV624,splitV625,splitV626,splitV627,splitV628])
 (consBan splitB610 (consBan splitB62 (consBan splitB478 (consBan splitB108 (consBan splitB121 (consBan splitB611 (consBan splitB481 (consBan splitB159 (consBan splitB482 (consBan splitB246 (consBan splitB612 (consBan splitB301 (consBan splitB340 (consBan splitB381 (consBan splitB413 (consBan splitB446 (consBan splitB484 (consBan splitB545 (consBan splitB573 (consBan splitB613 (consBan splitB614 (consBan splitB615 (consBan splitB616 (consBan splitB601 (consBan splitB617 (consBan splitB618 (consBan splitB619 (consBan splitB620 (consBan splitB621 (consBan splitB622 (consBan splitB623 (consBan splitB624 (consBan splitB625 (consBan splitB626 (consBan splitB627 (consBan splitB628 (nilBan 29 4)))))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV630 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998f000000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB630 : Ban 29 5 splitV630 := viaSmall (by decide +kernel) (by decide)

def splitV631 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB631 : Ban 29 5 splitV631 := viaSmall (by decide +kernel) (by decide)

def splitV632 : List ℕ := [0x1f00000f,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB632 : Ban 29 4 splitV632 := viaSmall (by decide +kernel) (by decide)

def splitV633 : List ℕ := [0x22222220f0f0f0,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB633 : Ban 29 4 splitV633 := viaSmall (by decide +kernel) (by decide)

def splitV634 : List ℕ := [0x22222230f0f00f,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB634 : Ban 29 4 splitV634 := viaSmall (by decide +kernel) (by decide)

def splitV635 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0xaaaaaabff000ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB635 : Ban 29 4 splitV635 := viaSmall (by decide +kernel) (by decide)

def splitV636 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbba0f0f0f0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB636 : Ban 29 4 splitV636 := viaSmall (by decide +kernel) (by decide)

def splitV637 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1bbbbbbbff0f0ff,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB637 : Ban 29 4 splitV637 := viaSmall (by decide +kernel) (by decide)

def splitV638 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1bbbbbbbff0f0ff,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB638 : Ban 29 4 splitV638 := viaSmall (by decide +kernel) (by decide)

def splitV639 : List ℕ := [0x22222230f0f0ff,0x13333333ff0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB639 : Ban 29 4 splitV639 := viaSmall (by decide +kernel) (by decide)

def splitV640 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998fff0ff0,0x1bbbbbbbff0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB640 : Ban 29 4 splitV640 := viaSmall (by decide +kernel) (by decide)

def splitV641 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB641 : Ban 29 5 splitV641 := viaBranch (ws := [splitV94,splitV632,splitV633,splitV481,splitV167,splitV223,splitV634,splitV411,splitV635,splitV523,splitV636,splitV637,splitV638,splitV639,splitV640])
 (consBan splitB94 (consBan splitB632 (consBan splitB633 (consBan splitB481 (consBan splitB167 (consBan splitB223 (consBan splitB634 (consBan splitB411 (consBan splitB635 (consBan splitB523 (consBan splitB636 (consBan splitB637 (consBan splitB638 (consBan splitB639 (consBan splitB640 (nilBan 29 4))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV642 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x20000001f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB642 : Ban 29 4 splitV642 := viaSmall (by decide +kernel) (by decide)

def splitV643 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x3dddddddf0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB643 : Ban 29 4 splitV643 := viaSmall (by decide +kernel) (by decide)

def splitV644 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcffffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB644 : Ban 29 4 splitV644 := viaSmall (by decide +kernel) (by decide)

def splitV645 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB645 : Ban 29 4 splitV645 := viaSmall (by decide +kernel) (by decide)

def splitV646 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB646 : Ban 29 4 splitV646 := viaSmall (by decide +kernel) (by decide)

def splitV647 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB647 : Ban 29 4 splitV647 := viaSmall (by decide +kernel) (by decide)

def splitV648 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1fffffff0ffffff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB648 : Ban 29 4 splitV648 := viaSmall (by decide +kernel) (by decide)

def splitV649 : List ℕ := [0x888888800f0ff0,0x177777770fff0ff,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB649 : Ban 29 4 splitV649 := viaSmall (by decide +kernel) (by decide)

def splitV650 : List ℕ := [0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB650 : Ban 29 4 splitV650 := viaSmall (by decide +kernel) (by decide)

def splitV651 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB651 : Ban 29 5 splitV651 := viaBranch (ws := [splitV479,splitV196,splitV233,splitV254,splitV318,splitV402,splitV492,splitV642,splitV643,splitV644,splitV645,splitV646,splitV556,splitV566,splitV647,splitV648,splitV649,splitV650])
 (consBan splitB479 (consBan splitB196 (consBan splitB233 (consBan splitB254 (consBan splitB318 (consBan splitB402 (consBan splitB492 (consBan splitB642 (consBan splitB643 (consBan splitB644 (consBan splitB645 (consBan splitB646 (consBan splitB556 (consBan splitB566 (consBan splitB647 (consBan splitB648 (consBan splitB649 (consBan splitB650 (nilBan 29 4)))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV652 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x200000010000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB652 : Ban 29 4 splitV652 := viaSmall (by decide +kernel) (by decide)

def splitV653 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x3dddddddfffff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB653 : Ban 29 4 splitV653 := viaSmall (by decide +kernel) (by decide)

def splitV654 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcffff000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB654 : Ban 29 4 splitV654 := viaSmall (by decide +kernel) (by decide)

def splitV655 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcffff000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB655 : Ban 29 4 splitV655 := viaSmall (by decide +kernel) (by decide)

def splitV656 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddcffff000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB656 : Ban 29 4 splitV656 := viaSmall (by decide +kernel) (by decide)

def splitV657 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x1ddddddcffffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB657 : Ban 29 4 splitV657 := viaSmall (by decide +kernel) (by decide)

def splitV658 : List ℕ := [0x22222230f0f0ff,0x19999998ff00000,0x1ddddddc00ffff0,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB658 : Ban 29 4 splitV658 := viaSmall (by decide +kernel) (by decide)

def splitV659 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1fffffffffff0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB659 : Ban 29 4 splitV659 := viaSmall (by decide +kernel) (by decide)

def splitV660 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB660 : Ban 29 5 splitV660 := viaBranch (ws := [splitV52,splitV66,splitV148,splitV168,splitV255,splitV343,splitV364,splitV419,splitV472,splitV652,splitV653,splitV654,splitV655,splitV656,splitV657,splitV658,splitV659])
 (consBan splitB52 (consBan splitB66 (consBan splitB148 (consBan splitB168 (consBan splitB255 (consBan splitB343 (consBan splitB364 (consBan splitB419 (consBan splitB472 (consBan splitB652 (consBan splitB653 (consBan splitB654 (consBan splitB655 (consBan splitB656 (consBan splitB657 (consBan splitB658 (consBan splitB659 (nilBan 29 4))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV661 : List ℕ := [0xf00000,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB661 : Ban 29 4 splitV661 := viaSmall (by decide +kernel) (by decide)

def splitV662 : List ℕ := [0x1000000f,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB662 : Ban 29 4 splitV662 := viaSmall (by decide +kernel) (by decide)

def splitV663 : List ℕ := [0x2222223000f0ff,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB663 : Ban 29 4 splitV663 := viaSmall (by decide +kernel) (by decide)

def splitV664 : List ℕ := [0x22222230f000ff,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB664 : Ban 29 4 splitV664 := viaSmall (by decide +kernel) (by decide)

def splitV665 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x28888889f0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB665 : Ban 29 4 splitV665 := viaSmall (by decide +kernel) (by decide)

def splitV666 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x39999999ff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB666 : Ban 29 4 splitV666 := viaSmall (by decide +kernel) (by decide)

def splitV667 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998fff0ff0,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB667 : Ban 29 4 splitV667 := viaSmall (by decide +kernel) (by decide)

def splitV668 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcffff000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB668 : Ban 29 4 splitV668 := viaSmall (by decide +kernel) (by decide)

def splitV669 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x20000001f000f0f,0x39999999ff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB669 : Ban 29 4 splitV669 := viaSmall (by decide +kernel) (by decide)

def splitV670 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x20000001f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB670 : Ban 29 4 splitV670 := viaSmall (by decide +kernel) (by decide)

def splitV671 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x19999998fff0ff0,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB671 : Ban 29 4 splitV671 := viaSmall (by decide +kernel) (by decide)

def splitV672 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x20000001f000f0f,0x28888889f0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB672 : Ban 29 4 splitV672 := viaSmall (by decide +kernel) (by decide)

def splitV673 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB673 : Ban 29 4 splitV673 := viaSmall (by decide +kernel) (by decide)

def splitV674 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB674 : Ban 29 4 splitV674 := viaSmall (by decide +kernel) (by decide)

def splitV675 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x20000001f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB675 : Ban 29 5 splitV675 := viaBranch (ws := [splitV9,splitV63,splitV661,splitV662,splitV95,splitV663,splitV160,splitV197,splitV664,splitV302,splitV363,splitV447,splitV487,splitV546,splitV561,splitV613,splitV652,splitV642,splitV665,splitV517,splitV666,splitV667,splitV668,splitV669,splitV645,splitV656,splitV670,splitV671,splitV672,splitV673,splitV674])
 (consBan splitB9 (consBan splitB63 (consBan splitB661 (consBan splitB662 (consBan splitB95 (consBan splitB663 (consBan splitB160 (consBan splitB197 (consBan splitB664 (consBan splitB302 (consBan splitB363 (consBan splitB447 (consBan splitB487 (consBan splitB546 (consBan splitB561 (consBan splitB613 (consBan splitB652 (consBan splitB642 (consBan splitB665 (consBan splitB517 (consBan splitB666 (consBan splitB667 (consBan splitB668 (consBan splitB669 (consBan splitB645 (consBan splitB656 (consBan splitB670 (consBan splitB671 (consBan splitB672 (consBan splitB673 (consBan splitB674 (nilBan 29 4))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV676 : List ℕ := [0x22222230f0f0ff,0x888888800f00f0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB676 : Ban 29 4 splitV676 := viaSmall (by decide +kernel) (by decide)

def splitV677 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x199999980f00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB677 : Ban 29 4 splitV677 := viaSmall (by decide +kernel) (by decide)

def splitV678 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x20000001f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB678 : Ban 29 4 splitV678 := viaSmall (by decide +kernel) (by decide)

def splitV679 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x39999999ff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB679 : Ban 29 4 splitV679 := viaSmall (by decide +kernel) (by decide)

def splitV680 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x28888889f0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB680 : Ban 29 4 splitV680 := viaSmall (by decide +kernel) (by decide)

def splitV681 : List ℕ := [0x22222230f0f0ff,0x19999998ff00000,0x1ddddddc00ffff0,0x20000001f000f0f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB681 : Ban 29 4 splitV681 := viaSmall (by decide +kernel) (by decide)

def splitV682 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x20000000f000f00,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB682 : Ban 29 4 splitV682 := viaSmall (by decide +kernel) (by decide)

def splitV683 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x20000001f000f0f,0x24444444f000f00]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB683 : Ban 29 4 splitV683 := viaSmall (by decide +kernel) (by decide)

def splitV684 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x20000001f000f0f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB684 : Ban 29 5 splitV684 := viaBranch (ws := [splitV146,splitV198,splitV256,splitV344,splitV447,splitV676,splitV515,splitV613,splitV677,splitV678,splitV679,splitV670,splitV533,splitV680,splitV681,splitV682,splitV683])
 (consBan splitB146 (consBan splitB198 (consBan splitB256 (consBan splitB344 (consBan splitB447 (consBan splitB676 (consBan splitB515 (consBan splitB613 (consBan splitB677 (consBan splitB678 (consBan splitB679 (consBan splitB670 (consBan splitB533 (consBan splitB680 (consBan splitB681 (consBan splitB682 (consBan splitB683 (nilBan 29 4))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV685 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444444f000f00,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB685 : Ban 29 5 splitV685 := viaSmall (by decide +kernel) (by decide)

def splitV686 : List ℕ := [0xf00000,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB686 : Ban 29 4 splitV686 := viaSmall (by decide +kernel) (by decide)

def splitV687 : List ℕ := [0x2222223000f0ff,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB687 : Ban 29 4 splitV687 := viaSmall (by decide +kernel) (by decide)

def splitV688 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445000000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB688 : Ban 29 4 splitV688 := viaSmall (by decide +kernel) (by decide)

def splitV689 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x2ccccccd00f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB689 : Ban 29 4 splitV689 := viaSmall (by decide +kernel) (by decide)

def splitV690 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x3555555500fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB690 : Ban 29 4 splitV690 := viaSmall (by decide +kernel) (by decide)

def splitV691 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998fff0ff0,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB691 : Ban 29 4 splitV691 := viaSmall (by decide +kernel) (by decide)

def splitV692 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x244444450000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB692 : Ban 29 4 splitV692 := viaSmall (by decide +kernel) (by decide)

def splitV693 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB693 : Ban 29 4 splitV693 := viaSmall (by decide +kernel) (by decide)

def splitV694 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x244444450000f0f,0x3555555500fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB694 : Ban 29 4 splitV694 := viaSmall (by decide +kernel) (by decide)

def splitV695 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x3555555500fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB695 : Ban 29 4 splitV695 := viaSmall (by decide +kernel) (by decide)

def splitV696 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x1ddddddc00ffff0,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB696 : Ban 29 4 splitV696 := viaSmall (by decide +kernel) (by decide)

def splitV697 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x244444450000f0f,0x2ccccccd00f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB697 : Ban 29 4 splitV697 := viaSmall (by decide +kernel) (by decide)

def splitV698 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB698 : Ban 29 4 splitV698 := viaSmall (by decide +kernel) (by decide)

def splitV699 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x177777770fff0ff,0x19999998ff00000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB699 : Ban 29 4 splitV699 := viaSmall (by decide +kernel) (by decide)

def splitV700 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB700 : Ban 29 4 splitV700 := viaSmall (by decide +kernel) (by decide)

def splitV701 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x244444440000f00,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB701 : Ban 29 4 splitV701 := viaSmall (by decide +kernel) (by decide)

def splitV702 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB702 : Ban 29 5 splitV702 := viaBranch (ws := [splitV686,splitV662,splitV122,splitV95,splitV687,splitV161,splitV169,splitV247,splitV303,splitV414,splitV448,splitV469,splitV525,splitV547,splitV574,splitV652,splitV688,splitV689,splitV690,splitV602,splitV691,splitV654,splitV692,splitV693,splitV694,splitV695,splitV696,splitV697,splitV698,splitV699,splitV700,splitV701])
 (consBan splitB686 (consBan splitB662 (consBan splitB122 (consBan splitB95 (consBan splitB687 (consBan splitB161 (consBan splitB169 (consBan splitB247 (consBan splitB303 (consBan splitB414 (consBan splitB448 (consBan splitB469 (consBan splitB525 (consBan splitB547 (consBan splitB574 (consBan splitB652 (consBan splitB688 (consBan splitB689 (consBan splitB690 (consBan splitB602 (consBan splitB691 (consBan splitB654 (consBan splitB692 (consBan splitB693 (consBan splitB694 (consBan splitB695 (consBan splitB696 (consBan splitB697 (consBan splitB698 (consBan splitB699 (consBan splitB700 (consBan splitB701 (nilBan 29 4)))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV703 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x3555555500fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB703 : Ban 29 4 splitV703 := viaSmall (by decide +kernel) (by decide)

def splitV704 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x2ccccccd00f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB704 : Ban 29 4 splitV704 := viaSmall (by decide +kernel) (by decide)

def splitV705 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x244444440000f00,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB705 : Ban 29 4 splitV705 := viaSmall (by decide +kernel) (by decide)

def splitV706 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444444f000f00,0x244444450000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB706 : Ban 29 4 splitV706 := viaSmall (by decide +kernel) (by decide)

def splitV707 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x244444450000f0f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB707 : Ban 29 5 splitV707 := viaBranch (ws := [splitV122,splitV146,splitV170,splitV278,splitV346,splitV448,splitV676,splitV525,splitV355,splitV600,splitV692,splitV619,splitV703,splitV704,splitV705,splitV706])
 (consBan splitB122 (consBan splitB146 (consBan splitB170 (consBan splitB278 (consBan splitB346 (consBan splitB448 (consBan splitB676 (consBan splitB525 (consBan splitB355 (consBan splitB600 (consBan splitB692 (consBan splitB619 (consBan splitB703 (consBan splitB704 (consBan splitB705 (consBan splitB706 (nilBan 29 4)))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV708 : List ℕ := [0xf0,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB708 : Ban 29 4 splitV708 := viaSmall (by decide +kernel) (by decide)

def splitV709 : List ℕ := [0x22222230f0f00f,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB709 : Ban 29 4 splitV709 := viaSmall (by decide +kernel) (by decide)

def splitV710 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x35555555f0ff00f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB710 : Ban 29 4 splitV710 := viaSmall (by decide +kernel) (by decide)

def splitV711 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x3dddddddff0000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB711 : Ban 29 4 splitV711 := viaSmall (by decide +kernel) (by decide)

def splitV712 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcffff000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB712 : Ban 29 4 splitV712 := viaSmall (by decide +kernel) (by decide)

def splitV713 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f00000f,0x3dddddddff0000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB713 : Ban 29 4 splitV713 := viaSmall (by decide +kernel) (by decide)

def splitV714 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x3dddddddff0000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB714 : Ban 29 4 splitV714 := viaSmall (by decide +kernel) (by decide)

def splitV715 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB715 : Ban 29 4 splitV715 := viaSmall (by decide +kernel) (by decide)

def splitV716 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddcffff000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB716 : Ban 29 4 splitV716 := viaSmall (by decide +kernel) (by decide)

def splitV717 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f00000f,0x35555555f0ff00f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB717 : Ban 29 4 splitV717 := viaSmall (by decide +kernel) (by decide)

def splitV718 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x19999998fff0ff0,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB718 : Ban 29 4 splitV718 := viaSmall (by decide +kernel) (by decide)

def splitV719 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f00000f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB719 : Ban 29 4 splitV719 := viaSmall (by decide +kernel) (by decide)

def splitV720 : List ℕ := [0x22222230f0f0ff,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB720 : Ban 29 4 splitV720 := viaSmall (by decide +kernel) (by decide)

def splitV721 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB721 : Ban 29 4 splitV721 := viaSmall (by decide +kernel) (by decide)

def splitV722 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x177777770fff0ff,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB722 : Ban 29 4 splitV722 := viaSmall (by decide +kernel) (by decide)

def splitV723 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB723 : Ban 29 4 splitV723 := viaSmall (by decide +kernel) (by decide)

def splitV724 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444444f000000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB724 : Ban 29 4 splitV724 := viaSmall (by decide +kernel) (by decide)

def splitV725 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB725 : Ban 29 5 splitV725 := viaBranch (ws := [splitV708,splitV17,splitV40,splitV662,splitV123,splitV95,splitV162,splitV217,splitV248,splitV279,splitV709,splitV304,splitV319,splitV382,splitV401,splitV488,splitV526,splitV575,splitV614,splitV642,splitV688,splitV436,splitV710,splitV711,splitV712,splitV713,splitV714,splitV715,splitV716,splitV717,splitV718,splitV647,splitV719,splitV720,splitV721,splitV722,splitV723,splitV724])
 (consBan splitB708 (consBan splitB17 (consBan splitB40 (consBan splitB662 (consBan splitB123 (consBan splitB95 (consBan splitB162 (consBan splitB217 (consBan splitB248 (consBan splitB279 (consBan splitB709 (consBan splitB304 (consBan splitB319 (consBan splitB382 (consBan splitB401 (consBan splitB488 (consBan splitB526 (consBan splitB575 (consBan splitB614 (consBan splitB642 (consBan splitB688 (consBan splitB436 (consBan splitB710 (consBan splitB711 (consBan splitB712 (consBan splitB713 (consBan splitB714 (consBan splitB715 (consBan splitB716 (consBan splitB717 (consBan splitB718 (consBan splitB647 (consBan splitB719 (consBan splitB720 (consBan splitB721 (consBan splitB722 (consBan splitB723 (consBan splitB724 (nilBan 29 4)))))))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV726 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x3dddddddff0000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB726 : Ban 29 4 splitV726 := viaSmall (by decide +kernel) (by decide)

def splitV727 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f00000f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB727 : Ban 29 4 splitV727 := viaSmall (by decide +kernel) (by decide)

def splitV728 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x35555555f0ff00f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB728 : Ban 29 4 splitV728 := viaSmall (by decide +kernel) (by decide)

def splitV729 : List ℕ := [0x22222230f0f0ff,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f00000f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB729 : Ban 29 4 splitV729 := viaSmall (by decide +kernel) (by decide)

def splitV730 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444444f000000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB730 : Ban 29 4 splitV730 := viaSmall (by decide +kernel) (by decide)

def splitV731 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444444f000f00,0x24444445f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB731 : Ban 29 4 splitV731 := viaSmall (by decide +kernel) (by decide)

def splitV732 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f00000f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB732 : Ban 29 5 splitV732 := viaBranch (ws := [splitV123,splitV146,splitV200,splitV280,splitV320,splitV433,splitV526,splitV355,splitV614,splitV677,splitV726,splitV727,splitV728,splitV719,splitV459,splitV729,splitV730,splitV731])
 (consBan splitB123 (consBan splitB146 (consBan splitB200 (consBan splitB280 (consBan splitB320 (consBan splitB433 (consBan splitB526 (consBan splitB355 (consBan splitB614 (consBan splitB677 (consBan splitB726 (consBan splitB727 (consBan splitB728 (consBan splitB719 (consBan splitB459 (consBan splitB729 (consBan splitB730 (consBan splitB731 (nilBan 29 4)))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV733 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x26666667ff0ffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB733 : Ban 29 5 splitV733 := viaSmall (by decide +kernel) (by decide)

def splitV734 : List ℕ := [0x100000ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB734 : Ban 29 4 splitV734 := viaSmall (by decide +kernel) (by decide)

def splitV735 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x3dddddddfff0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB735 : Ban 29 4 splitV735 := viaSmall (by decide +kernel) (by decide)

def splitV736 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x3dddddddf0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB736 : Ban 29 4 splitV736 := viaSmall (by decide +kernel) (by decide)

def splitV737 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x2ccccccdf0f0fff,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB737 : Ban 29 4 splitV737 := viaSmall (by decide +kernel) (by decide)

def splitV738 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998fff0ff0,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB738 : Ban 29 4 splitV738 := viaSmall (by decide +kernel) (by decide)

def splitV739 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444444f000f00,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB739 : Ban 29 4 splitV739 := viaSmall (by decide +kernel) (by decide)

def splitV740 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x2cccccccf0f0f00]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB740 : Ban 29 4 splitV740 := viaSmall (by decide +kernel) (by decide)

def splitV741 : List ℕ := [0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB741 : Ban 29 4 splitV741 := viaSmall (by decide +kernel) (by decide)

def splitV742 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB742 : Ban 29 5 splitV742 := viaBranch (ws := [splitV124,splitV734,splitV202,splitV282,splitV321,splitV434,splitV523,splitV527,splitV545,splitV615,splitV735,splitV736,splitV737,splitV557,splitV584,splitV719,splitV738,splitV739,splitV740,splitV741])
 (consBan splitB124 (consBan splitB734 (consBan splitB202 (consBan splitB282 (consBan splitB321 (consBan splitB434 (consBan splitB523 (consBan splitB527 (consBan splitB545 (consBan splitB615 (consBan splitB735 (consBan splitB736 (consBan splitB737 (consBan splitB557 (consBan splitB584 (consBan splitB719 (consBan splitB738 (consBan splitB739 (consBan splitB740 (consBan splitB741 (nilBan 29 4)))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV743 : List ℕ := [0x1000f00f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB743 : Ban 29 4 splitV743 := viaSmall (by decide +kernel) (by decide)

def splitV744 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x3dddddddfffff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB744 : Ban 29 4 splitV744 := viaSmall (by decide +kernel) (by decide)

def splitV745 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x35555555f0fff0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB745 : Ban 29 4 splitV745 := viaSmall (by decide +kernel) (by decide)

def splitV746 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x3dddddddf0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB746 : Ban 29 4 splitV746 := viaSmall (by decide +kernel) (by decide)

def splitV747 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444444f000f00,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB747 : Ban 29 4 splitV747 := viaSmall (by decide +kernel) (by decide)

def splitV748 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x35555554f0f0f00]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB748 : Ban 29 4 splitV748 := viaSmall (by decide +kernel) (by decide)

def splitV749 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB749 : Ban 29 5 splitV749 := viaBranch (ws := [splitV743,splitV203,splitV257,splitV348,splitV411,splitV420,splitV449,splitV484,splitV493,splitV516,splitV616,splitV744,splitV745,splitV670,splitV746,splitV747,splitV748])
 (consBan splitB743 (consBan splitB203 (consBan splitB257 (consBan splitB348 (consBan splitB411 (consBan splitB420 (consBan splitB449 (consBan splitB484 (consBan splitB493 (consBan splitB516 (consBan splitB616 (consBan splitB744 (consBan splitB745 (consBan splitB670 (consBan splitB746 (consBan splitB747 (consBan splitB748 (nilBan 29 4))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV750 : List ℕ := [0x10f0000f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB750 : Ban 29 4 splitV750 := viaSmall (by decide +kernel) (by decide)

def splitV751 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x3dddddddfffff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB751 : Ban 29 4 splitV751 := viaSmall (by decide +kernel) (by decide)

def splitV752 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x3dddddddfff0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB752 : Ban 29 4 splitV752 := viaSmall (by decide +kernel) (by decide)

def splitV753 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998fff0ff0,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB753 : Ban 29 4 splitV753 := viaSmall (by decide +kernel) (by decide)

def splitV754 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444444f000f00,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB754 : Ban 29 4 splitV754 := viaSmall (by decide +kernel) (by decide)

def splitV755 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x3ddddddcf000f00]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB755 : Ban 29 4 splitV755 := viaSmall (by decide +kernel) (by decide)

def splitV756 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x1bbbbbbbff0f0ff,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB756 : Ban 29 4 splitV756 := viaSmall (by decide +kernel) (by decide)

def splitV757 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB757 : Ban 29 5 splitV757 := viaBranch (ws := [splitV53,splitV67,splitV374,splitV125,splitV750,splitV171,splitV283,splitV349,splitV386,splitV450,splitV528,splitV601,splitV692,splitV751,splitV752,splitV753,splitV754,splitV755,splitV756])
 (consBan splitB53 (consBan splitB67 (consBan splitB374 (consBan splitB125 (consBan splitB750 (consBan splitB171 (consBan splitB283 (consBan splitB349 (consBan splitB386 (consBan splitB450 (consBan splitB528 (consBan splitB601 (consBan splitB692 (consBan splitB751 (consBan splitB752 (consBan splitB753 (consBan splitB754 (consBan splitB755 (consBan splitB756 (nilBan 29 4))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV758 : List ℕ := [0x100000ff,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB758 : Ban 29 4 splitV758 := viaSmall (by decide +kernel) (by decide)

def splitV759 : List ℕ := [0x100000ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB759 : Ban 29 4 splitV759 := viaSmall (by decide +kernel) (by decide)

def splitV760 : List ℕ := [0x22222220f0f000,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB760 : Ban 29 4 splitV760 := viaSmall (by decide +kernel) (by decide)

def splitV761 : List ℕ := [0x22222230f0f0ff,0x888888800f0f00,0x1555555400ff000,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB761 : Ban 29 4 splitV761 := viaSmall (by decide +kernel) (by decide)

def splitV762 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x11111110000f000,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB762 : Ban 29 4 splitV762 := viaSmall (by decide +kernel) (by decide)

def splitV763 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x2444444500f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB763 : Ban 29 4 splitV763 := viaSmall (by decide +kernel) (by decide)

def splitV764 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x28888889f000fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB764 : Ban 29 4 splitV764 := viaSmall (by decide +kernel) (by decide)

def splitV765 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x3dddddddfff0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB765 : Ban 29 4 splitV765 := viaSmall (by decide +kernel) (by decide)

def splitV766 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcffff000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB766 : Ban 29 4 splitV766 := viaSmall (by decide +kernel) (by decide)

def splitV767 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB767 : Ban 29 4 splitV767 := viaSmall (by decide +kernel) (by decide)

def splitV768 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddcffff000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB768 : Ban 29 4 splitV768 := viaSmall (by decide +kernel) (by decide)

def splitV769 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x2ccccccdf0f0fff,0x3dddddddf0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB769 : Ban 29 4 splitV769 := viaSmall (by decide +kernel) (by decide)

def splitV770 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB770 : Ban 29 4 splitV770 := viaSmall (by decide +kernel) (by decide)

def splitV771 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x177777770fff0ff,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB771 : Ban 29 4 splitV771 := viaSmall (by decide +kernel) (by decide)

def splitV772 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB772 : Ban 29 4 splitV772 := viaSmall (by decide +kernel) (by decide)

def splitV773 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x2cccccccf0f0f00,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB773 : Ban 29 4 splitV773 := viaSmall (by decide +kernel) (by decide)

def splitV774 : List ℕ := [0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB774 : Ban 29 4 splitV774 := viaSmall (by decide +kernel) (by decide)

def splitV775 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB775 : Ban 29 5 splitV775 := viaBranch (ws := [splitV19,splitV758,splitV759,splitV760,splitV163,splitV218,splitV249,splitV284,splitV305,splitV384,splitV761,splitV489,splitV762,splitV576,splitV763,splitV45,splitV764,splitV643,splitV765,splitV766,splitV767,splitV768,splitV769,splitV509,splitV719,splitV770,splitV771,splitV772,splitV773,splitV774])
 (consBan splitB19 (consBan splitB758 (consBan splitB759 (consBan splitB760 (consBan splitB163 (consBan splitB218 (consBan splitB249 (consBan splitB284 (consBan splitB305 (consBan splitB384 (consBan splitB761 (consBan splitB489 (consBan splitB762 (consBan splitB576 (consBan splitB763 (consBan splitB45 (consBan splitB764 (consBan splitB643 (consBan splitB765 (consBan splitB766 (consBan splitB767 (consBan splitB768 (consBan splitB769 (consBan splitB509 (consBan splitB719 (consBan splitB770 (consBan splitB771 (consBan splitB772 (consBan splitB773 (consBan splitB774 (nilBan 29 4)))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV776 : List ℕ := [0xf00000,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB776 : Ban 29 4 splitV776 := viaSmall (by decide +kernel) (by decide)

def splitV777 : List ℕ := [0x1000f00f,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB777 : Ban 29 4 splitV777 := viaSmall (by decide +kernel) (by decide)

def splitV778 : List ℕ := [0x1000f00f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB778 : Ban 29 4 splitV778 := viaSmall (by decide +kernel) (by decide)

def splitV779 : List ℕ := [0x1000f00f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB779 : Ban 29 4 splitV779 := viaSmall (by decide +kernel) (by decide)

def splitV780 : List ℕ := [0x22222220f000f0,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB780 : Ban 29 4 splitV780 := viaSmall (by decide +kernel) (by decide)

def splitV781 : List ℕ := [0x2222223000f0ff,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB781 : Ban 29 4 splitV781 := viaSmall (by decide +kernel) (by decide)

def splitV782 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x88888880f00000,0x1555555400ff000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB782 : Ban 29 4 splitV782 := viaSmall (by decide +kernel) (by decide)

def splitV783 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x111111100000000,0x19999998ff00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB783 : Ban 29 4 splitV783 := viaSmall (by decide +kernel) (by decide)

def splitV784 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x2444444500fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB784 : Ban 29 4 splitV784 := viaSmall (by decide +kernel) (by decide)

def splitV785 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x35555555f00f00f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB785 : Ban 29 4 splitV785 := viaSmall (by decide +kernel) (by decide)

def splitV786 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998fff0ff0,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB786 : Ban 29 4 splitV786 := viaSmall (by decide +kernel) (by decide)

def splitV787 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcffff000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB787 : Ban 29 4 splitV787 := viaSmall (by decide +kernel) (by decide)

def splitV788 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x35555555f0fff0f,0x3dddddddfffff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB788 : Ban 29 4 splitV788 := viaSmall (by decide +kernel) (by decide)

def splitV789 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x177777770fff0ff,0x19999998ff00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB789 : Ban 29 4 splitV789 := viaSmall (by decide +kernel) (by decide)

def splitV790 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x19999998fff0ff0,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB790 : Ban 29 4 splitV790 := viaSmall (by decide +kernel) (by decide)

def splitV791 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB791 : Ban 29 4 splitV791 := viaSmall (by decide +kernel) (by decide)

def splitV792 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB792 : Ban 29 4 splitV792 := viaSmall (by decide +kernel) (by decide)

def splitV793 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x35555554f0f0f00,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB793 : Ban 29 4 splitV793 := viaSmall (by decide +kernel) (by decide)

def splitV794 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB794 : Ban 29 5 splitV794 := viaBranch (ws := [splitV65,splitV776,splitV777,splitV778,splitV779,splitV780,splitV781,splitV164,splitV204,splitV306,splitV782,splitV491,splitV471,splitV494,splitV783,splitV548,splitV562,splitV591,splitV356,splitV784,splitV785,splitV643,splitV653,splitV786,splitV787,splitV788,splitV789,splitV646,splitV670,splitV790,splitV791,splitV792,splitV793])
 (consBan splitB65 (consBan splitB776 (consBan splitB777 (consBan splitB778 (consBan splitB779 (consBan splitB780 (consBan splitB781 (consBan splitB164 (consBan splitB204 (consBan splitB306 (consBan splitB782 (consBan splitB491 (consBan splitB471 (consBan splitB494 (consBan splitB783 (consBan splitB548 (consBan splitB562 (consBan splitB591 (consBan splitB356 (consBan splitB784 (consBan splitB785 (consBan splitB643 (consBan splitB653 (consBan splitB786 (consBan splitB787 (consBan splitB788 (consBan splitB789 (consBan splitB646 (consBan splitB670 (consBan splitB790 (consBan splitB791 (consBan splitB792 (consBan splitB793 (nilBan 29 4))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV795 : List ℕ := [0x10f0000f,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB795 : Ban 29 4 splitV795 := viaSmall (by decide +kernel) (by decide)

def splitV796 : List ℕ := [0x10f0000f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB796 : Ban 29 4 splitV796 := viaSmall (by decide +kernel) (by decide)

def splitV797 : List ℕ := [0x2222222000f0f0,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB797 : Ban 29 4 splitV797 := viaSmall (by decide +kernel) (by decide)

def splitV798 : List ℕ := [0x22222230f0f0ff,0x88888880000000,0x888888800f0ff0,0x1555555400ff000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB798 : Ban 29 4 splitV798 := viaSmall (by decide +kernel) (by decide)

def splitV799 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998f000000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB799 : Ban 29 4 splitV799 := viaSmall (by decide +kernel) (by decide)

def splitV800 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x28888889ff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB800 : Ban 29 4 splitV800 := viaSmall (by decide +kernel) (by decide)

def splitV801 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x35555555ff0000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB801 : Ban 29 4 splitV801 := viaSmall (by decide +kernel) (by decide)

def splitV802 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB802 : Ban 29 4 splitV802 := viaSmall (by decide +kernel) (by decide)

def splitV803 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x1ddddddc00ffff0,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB803 : Ban 29 4 splitV803 := viaSmall (by decide +kernel) (by decide)

def splitV804 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB804 : Ban 29 4 splitV804 := viaSmall (by decide +kernel) (by decide)

def splitV805 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x177777770fff0ff,0x19999998ff00000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB805 : Ban 29 4 splitV805 := viaSmall (by decide +kernel) (by decide)

def splitV806 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB806 : Ban 29 4 splitV806 := viaSmall (by decide +kernel) (by decide)

def splitV807 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x3ddddddcf000f00,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB807 : Ban 29 4 splitV807 := viaSmall (by decide +kernel) (by decide)

def splitV808 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x1bbbbbbbff0f0ff,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB808 : Ban 29 4 splitV808 := viaSmall (by decide +kernel) (by decide)

def splitV809 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB809 : Ban 29 5 splitV809 := viaBranch (ws := [splitV37,splitV795,splitV796,splitV797,splitV165,splitV250,splitV307,splitV798,splitV416,splitV470,splitV578,splitV799,splitV473,splitV800,splitV801,splitV765,splitV653,splitV637,splitV655,splitV692,splitV802,splitV803,splitV804,splitV805,splitV806,splitV807,splitV808])
 (consBan splitB37 (consBan splitB795 (consBan splitB796 (consBan splitB797 (consBan splitB165 (consBan splitB250 (consBan splitB307 (consBan splitB798 (consBan splitB416 (consBan splitB470 (consBan splitB578 (consBan splitB799 (consBan splitB473 (consBan splitB800 (consBan splitB801 (consBan splitB765 (consBan splitB653 (consBan splitB637 (consBan splitB655 (consBan splitB692 (consBan splitB802 (consBan splitB803 (consBan splitB804 (consBan splitB805 (consBan splitB806 (consBan splitB807 (consBan splitB808 (nilBan 29 4))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV810 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB810 : Ban 29 5 splitV810 := viaSmall (by decide +kernel) (by decide)

def splitV811 : List ℕ := [0xf0f000,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB811 : Ban 29 4 splitV811 := viaSmall (by decide +kernel) (by decide)

def splitV812 : List ℕ := [0x22222220f0f0f0,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcffff000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB812 : Ban 29 4 splitV812 := viaSmall (by decide +kernel) (by decide)

def splitV813 : List ℕ := [0x222222300000ff,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB813 : Ban 29 4 splitV813 := viaSmall (by decide +kernel) (by decide)

def splitV814 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x15555554ff0f000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB814 : Ban 29 4 splitV814 := viaSmall (by decide +kernel) (by decide)

def splitV815 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x199999980fff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB815 : Ban 29 4 splitV815 := viaSmall (by decide +kernel) (by decide)

def splitV816 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcffff000,0x200000010000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB816 : Ban 29 4 splitV816 := viaSmall (by decide +kernel) (by decide)

def splitV817 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcffff000,0x3dddddddfffff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB817 : Ban 29 4 splitV817 := viaSmall (by decide +kernel) (by decide)

def splitV818 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x177777770fff0ff,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB818 : Ban 29 4 splitV818 := viaSmall (by decide +kernel) (by decide)

def splitV819 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x1ddddddcffff000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB819 : Ban 29 4 splitV819 := viaSmall (by decide +kernel) (by decide)

def splitV820 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB820 : Ban 29 4 splitV820 := viaSmall (by decide +kernel) (by decide)

def splitV821 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB821 : Ban 29 5 splitV821 := viaBranch (ws := [splitV811,splitV88,splitV812,splitV813,splitV308,splitV452,splitV514,splitV472,splitV592,splitV814,splitV815,splitV816,splitV668,splitV712,splitV766,splitV787,splitV817,splitV644,splitV744,splitV818,splitV819,splitV820])
 (consBan splitB811 (consBan splitB88 (consBan splitB812 (consBan splitB813 (consBan splitB308 (consBan splitB452 (consBan splitB514 (consBan splitB472 (consBan splitB592 (consBan splitB814 (consBan splitB815 (consBan splitB816 (consBan splitB668 (consBan splitB712 (consBan splitB766 (consBan splitB787 (consBan splitB817 (consBan splitB644 (consBan splitB744 (consBan splitB818 (consBan splitB819 (consBan splitB820 (nilBan 29 4)))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV822 : List ℕ := [0xf0,0x22222230f0f0ff,0x1555555400ff000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB822 : Ban 29 4 splitV822 := viaSmall (by decide +kernel) (by decide)

def splitV823 : List ℕ := [0xf00,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB823 : Ban 29 4 splitV823 := viaSmall (by decide +kernel) (by decide)

def splitV824 : List ℕ := [0xf00f0,0x22222230f0f0ff,0x1555555400ff000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB824 : Ban 29 4 splitV824 := viaSmall (by decide +kernel) (by decide)

def splitV825 : List ℕ := [0x10f0000f,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB825 : Ban 29 4 splitV825 := viaSmall (by decide +kernel) (by decide)

def splitV826 : List ℕ := [0x10f0000f,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB826 : Ban 29 4 splitV826 := viaSmall (by decide +kernel) (by decide)

def splitV827 : List ℕ := [0x2222222000f0f0,0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB827 : Ban 29 4 splitV827 := viaSmall (by decide +kernel) (by decide)

def splitV828 : List ℕ := [0x22222230f0f00f,0x22222230f0f0ff,0x1555555400ff000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB828 : Ban 29 4 splitV828 := viaSmall (by decide +kernel) (by decide)

def splitV829 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444444f000f00,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB829 : Ban 29 4 splitV829 := viaSmall (by decide +kernel) (by decide)

def splitV830 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x28888889ff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB830 : Ban 29 4 splitV830 := viaSmall (by decide +kernel) (by decide)

def splitV831 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x35555555ff0000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB831 : Ban 29 4 splitV831 := viaSmall (by decide +kernel) (by decide)

def splitV832 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x26666667ff0ffff,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB832 : Ban 29 4 splitV832 := viaSmall (by decide +kernel) (by decide)

def splitV833 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1ddddddc00ffff0,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB833 : Ban 29 4 splitV833 := viaSmall (by decide +kernel) (by decide)

def splitV834 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x1ddddddc00ffff0,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB834 : Ban 29 4 splitV834 := viaSmall (by decide +kernel) (by decide)

def splitV835 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x24444445f000f0f,0x2ccccccdf0f0fff,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB835 : Ban 29 4 splitV835 := viaSmall (by decide +kernel) (by decide)

def splitV836 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x24444445f000f0f,0x3dddddddff00f0f,0x3dddddddfff0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB836 : Ban 29 4 splitV836 := viaSmall (by decide +kernel) (by decide)

def splitV837 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB837 : Ban 29 4 splitV837 := viaSmall (by decide +kernel) (by decide)

def splitV838 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x177777770fff0ff,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB838 : Ban 29 4 splitV838 := viaSmall (by decide +kernel) (by decide)

def splitV839 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x24444444f000f00,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB839 : Ban 29 4 splitV839 := viaSmall (by decide +kernel) (by decide)

def splitV840 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x24444444f000f00,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB840 : Ban 29 4 splitV840 := viaSmall (by decide +kernel) (by decide)

def splitV841 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x3ddddddcf000f00,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB841 : Ban 29 4 splitV841 := viaSmall (by decide +kernel) (by decide)

def splitV842 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x3dddddddff00f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB842 : Ban 29 5 splitV842 := viaBranch (ws := [splitV822,splitV823,splitV824,splitV127,splitV825,splitV826,splitV827,splitV252,splitV828,splitV309,splitV350,splitV418,splitV430,splitV453,splitV454,splitV580,splitV677,splitV601,splitV678,splitV829,splitV830,splitV831,splitV735,splitV744,splitV832,splitV745,splitV833,splitV834,splitV835,splitV836,splitV837,splitV838,splitV839,splitV840,splitV841])
 (consBan splitB822 (consBan splitB823 (consBan splitB824 (consBan splitB127 (consBan splitB825 (consBan splitB826 (consBan splitB827 (consBan splitB252 (consBan splitB828 (consBan splitB309 (consBan splitB350 (consBan splitB418 (consBan splitB430 (consBan splitB453 (consBan splitB454 (consBan splitB580 (consBan splitB677 (consBan splitB601 (consBan splitB678 (consBan splitB829 (consBan splitB830 (consBan splitB831 (consBan splitB735 (consBan splitB744 (consBan splitB832 (consBan splitB745 (consBan splitB833 (consBan splitB834 (consBan splitB835 (consBan splitB836 (consBan splitB837 (consBan splitB838 (consBan splitB839 (consBan splitB840 (consBan splitB841 (nilBan 29 4))))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV843 : List ℕ := [0xf00,0x22222230f0f0ff,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB843 : Ban 29 4 splitV843 := viaSmall (by decide +kernel) (by decide)

def splitV844 : List ℕ := [0xf0f0,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB844 : Ban 29 4 splitV844 := viaSmall (by decide +kernel) (by decide)

def splitV845 : List ℕ := [0x22222220f0f0f0,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB845 : Ban 29 4 splitV845 := viaSmall (by decide +kernel) (by decide)

def splitV846 : List ℕ := [0x22222230f0000f,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB846 : Ban 29 4 splitV846 := viaSmall (by decide +kernel) (by decide)

def splitV847 : List ℕ := [0x22222230f0f0ff,0x444444400ffff0,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB847 : Ban 29 4 splitV847 := viaSmall (by decide +kernel) (by decide)

def splitV848 : List ℕ := [0x22222230f0f0ff,0x888888800f0f00,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB848 : Ban 29 4 splitV848 := viaSmall (by decide +kernel) (by decide)

def splitV849 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1999999800ff0f0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB849 : Ban 29 4 splitV849 := viaSmall (by decide +kernel) (by decide)

def splitV850 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x20000001f00000f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB850 : Ban 29 4 splitV850 := viaSmall (by decide +kernel) (by decide)

def splitV851 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x3dddddddf0fffff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB851 : Ban 29 4 splitV851 := viaSmall (by decide +kernel) (by decide)

def splitV852 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddcffffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB852 : Ban 29 4 splitV852 := viaSmall (by decide +kernel) (by decide)

def splitV853 : List ℕ := [0x22222230f0f0ff,0x19999998ff00000,0x19999998fff0ff0,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB853 : Ban 29 4 splitV853 := viaSmall (by decide +kernel) (by decide)

def splitV854 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ffffff,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB854 : Ban 29 4 splitV854 := viaSmall (by decide +kernel) (by decide)

def splitV855 : List ℕ := [0x888888800f0ff0,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB855 : Ban 29 4 splitV855 := viaSmall (by decide +kernel) (by decide)

def splitV856 : List ℕ := [0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x1fffffff0ffffff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB856 : Ban 29 4 splitV856 := viaSmall (by decide +kernel) (by decide)

def splitV857 : List ℕ := [0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x24444444f000f00,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB857 : Ban 29 4 splitV857 := viaSmall (by decide +kernel) (by decide)

def splitV858 : List ℕ := [0xaaaaaab0ffffff,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB858 : Ban 29 4 splitV858 := viaSmall (by decide +kernel) (by decide)

def splitV859 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB859 : Ban 29 5 splitV859 := viaBranch (ws := [splitV843,splitV844,splitV42,splitV90,splitV129,splitV845,splitV172,splitV215,splitV846,splitV270,splitV310,splitV847,splitV848,splitV44,splitV849,splitV620,splitV850,splitV693,splitV715,splitV767,splitV851,splitV802,splitV852,splitV736,splitV833,splitV511,splitV566,splitV853,splitV720,splitV729,splitV854,splitV855,splitV856,splitV857,splitV858])
 (consBan splitB843 (consBan splitB844 (consBan splitB42 (consBan splitB90 (consBan splitB129 (consBan splitB845 (consBan splitB172 (consBan splitB215 (consBan splitB846 (consBan splitB270 (consBan splitB310 (consBan splitB847 (consBan splitB848 (consBan splitB44 (consBan splitB849 (consBan splitB620 (consBan splitB850 (consBan splitB693 (consBan splitB715 (consBan splitB767 (consBan splitB851 (consBan splitB802 (consBan splitB852 (consBan splitB736 (consBan splitB833 (consBan splitB511 (consBan splitB566 (consBan splitB853 (consBan splitB720 (consBan splitB729 (consBan splitB854 (consBan splitB855 (consBan splitB856 (consBan splitB857 (consBan splitB858 (nilBan 29 4))))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV860 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB860 : Ban 29 5 splitV860 := viaSmall (by decide +kernel) (by decide)

def splitV861 : List ℕ := [0xf000000,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB861 : Ban 29 4 splitV861 := viaSmall (by decide +kernel) (by decide)

def splitV862 : List ℕ := [0x1000f00f,0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB862 : Ban 29 4 splitV862 := viaSmall (by decide +kernel) (by decide)

def splitV863 : List ℕ := [0x1000f00f,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB863 : Ban 29 4 splitV863 := viaSmall (by decide +kernel) (by decide)

def splitV864 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444444f000f00,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB864 : Ban 29 4 splitV864 := viaSmall (by decide +kernel) (by decide)

def splitV865 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x2444444500fff0f,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB865 : Ban 29 4 splitV865 := viaSmall (by decide +kernel) (by decide)

def splitV866 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x35555555f00f00f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB866 : Ban 29 4 splitV866 := viaSmall (by decide +kernel) (by decide)

def splitV867 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x26666667ff0ffff,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB867 : Ban 29 4 splitV867 := viaSmall (by decide +kernel) (by decide)

def splitV868 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998fff0ff0,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB868 : Ban 29 4 splitV868 := viaSmall (by decide +kernel) (by decide)

def splitV869 : List ℕ := [0x22222230f0f0ff,0x19999998ff00000,0x19999998fff0ff0,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB869 : Ban 29 4 splitV869 := viaSmall (by decide +kernel) (by decide)

def splitV870 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ffffff,0x19999998ff00000,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB870 : Ban 29 4 splitV870 := viaSmall (by decide +kernel) (by decide)

def splitV871 : List ℕ := [0x888888800f0ff0,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB871 : Ban 29 4 splitV871 := viaSmall (by decide +kernel) (by decide)

def splitV872 : List ℕ := [0x888888800f0ff0,0x19999998ff00000,0x24444444f000f00,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB872 : Ban 29 4 splitV872 := viaSmall (by decide +kernel) (by decide)

def splitV873 : List ℕ := [0x888888800f0ff0,0x19999998ff00000,0x24444444f000f00,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB873 : Ban 29 4 splitV873 := viaSmall (by decide +kernel) (by decide)

def splitV874 : List ℕ := [0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x35555554f0f0f00,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB874 : Ban 29 4 splitV874 := viaSmall (by decide +kernel) (by decide)

def splitV875 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x35555555f0fff0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB875 : Ban 29 5 splitV875 := viaBranch (ws := [splitV70,splitV861,splitV130,splitV862,splitV863,splitV211,splitV173,splitV312,splitV355,splitV516,splitV551,splitV603,splitV864,splitV865,splitV727,splitV866,splitV736,splitV751,splitV867,splitV737,splitV868,splitV869,splitV870,splitV871,splitV872,splitV873,splitV874])
 (consBan splitB70 (consBan splitB861 (consBan splitB130 (consBan splitB862 (consBan splitB863 (consBan splitB211 (consBan splitB173 (consBan splitB312 (consBan splitB355 (consBan splitB516 (consBan splitB551 (consBan splitB603 (consBan splitB864 (consBan splitB865 (consBan splitB727 (consBan splitB866 (consBan splitB736 (consBan splitB751 (consBan splitB867 (consBan splitB737 (consBan splitB868 (consBan splitB869 (consBan splitB870 (consBan splitB871 (consBan splitB872 (consBan splitB873 (consBan splitB874 (nilBan 29 4))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV876 : List ℕ := [0xf000f0,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB876 : Ban 29 4 splitV876 := viaSmall (by decide +kernel) (by decide)

def splitV877 : List ℕ := [0x2222223000f00f,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB877 : Ban 29 4 splitV877 := viaSmall (by decide +kernel) (by decide)

def splitV878 : List ℕ := [0x22222230f0f0ff,0x4444444000f000,0x19999998ff00000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB878 : Ban 29 4 splitV878 := viaSmall (by decide +kernel) (by decide)

def splitV879 : List ℕ := [0x22222230f0f0ff,0x8888888ff00ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB879 : Ban 29 4 splitV879 := viaSmall (by decide +kernel) (by decide)

def splitV880 : List ℕ := [0x22222230f0f0ff,0x111111100000000,0x1555555400ff000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB880 : Ban 29 4 splitV880 := viaSmall (by decide +kernel) (by decide)

def splitV881 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x199999980ff00f0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB881 : Ban 29 4 splitV881 := viaSmall (by decide +kernel) (by decide)

def splitV882 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998f000000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB882 : Ban 29 4 splitV882 := viaSmall (by decide +kernel) (by decide)

def splitV883 : List ℕ := [0x22222230f0f0ff,0x19999998ff00000,0x19999998fff0ff0,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB883 : Ban 29 4 splitV883 := viaSmall (by decide +kernel) (by decide)

def splitV884 : List ℕ := [0x22222230f0f0ff,0x19999998ff00000,0x19999998fff0ff0,0x1ddddddcffffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB884 : Ban 29 4 splitV884 := viaSmall (by decide +kernel) (by decide)

def splitV885 : List ℕ := [0x1555555400ff000,0x177777770fff0ff,0x19999998ff00000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB885 : Ban 29 4 splitV885 := viaSmall (by decide +kernel) (by decide)

def splitV886 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB886 : Ban 29 5 splitV886 := viaBranch (ws := [splitV22,splitV467,splitV41,splitV876,splitV877,splitV219,splitV258,splitV285,splitV878,splitV365,splitV388,splitV390,splitV879,splitV880,splitV535,splitV605,splitV881,splitV882,splitV671,splitV790,splitV657,splitV752,splitV640,splitV753,splitV883,splitV884,splitV869,splitV885])
 (consBan splitB22 (consBan splitB467 (consBan splitB41 (consBan splitB876 (consBan splitB877 (consBan splitB219 (consBan splitB258 (consBan splitB285 (consBan splitB878 (consBan splitB365 (consBan splitB388 (consBan splitB390 (consBan splitB879 (consBan splitB880 (consBan splitB535 (consBan splitB605 (consBan splitB881 (consBan splitB882 (consBan splitB671 (consBan splitB790 (consBan splitB657 (consBan splitB752 (consBan splitB640 (consBan splitB753 (consBan splitB883 (consBan splitB884 (consBan splitB869 (consBan splitB885 (nilBan 29 4)))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV887 : List ℕ := [0xf0f0,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB887 : Ban 29 4 splitV887 := viaSmall (by decide +kernel) (by decide)

def splitV888 : List ℕ := [0x22222230f0000f,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB888 : Ban 29 4 splitV888 := viaSmall (by decide +kernel) (by decide)

def splitV889 : List ℕ := [0x22222230f0000f,0x1555555400ff000,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB889 : Ban 29 4 splitV889 := viaSmall (by decide +kernel) (by decide)

def splitV890 : List ℕ := [0x22222230f0f0ff,0x444444400ffff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB890 : Ban 29 4 splitV890 := viaSmall (by decide +kernel) (by decide)

def splitV891 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x1999999800ff0f0,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB891 : Ban 29 4 splitV891 := viaSmall (by decide +kernel) (by decide)

def splitV892 : List ℕ := [0x22222230f0f0ff,0x177777770fff0ff,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB892 : Ban 29 4 splitV892 := viaSmall (by decide +kernel) (by decide)

def splitV893 : List ℕ := [0x1555555400ff000,0x177777770fff0ff,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB893 : Ban 29 4 splitV893 := viaSmall (by decide +kernel) (by decide)

def splitV894 : List ℕ := [0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB894 : Ban 29 4 splitV894 := viaSmall (by decide +kernel) (by decide)

def splitV895 : List ℕ := [0x1555555400ff000,0x19999998ff00000,0x1ddddddc00ffff0,0x1fffffff0ffffff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB895 : Ban 29 4 splitV895 := viaSmall (by decide +kernel) (by decide)

def splitV896 : List ℕ := [0x1555555400ff000,0x19999998ff00000,0x1ddddddc00ffff0,0x24444444f000f00,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB896 : Ban 29 4 splitV896 := viaSmall (by decide +kernel) (by decide)

def splitV897 : List ℕ := [0x177777770fff0ff,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB897 : Ban 29 4 splitV897 := viaSmall (by decide +kernel) (by decide)

def splitV898 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x1ddddddc00ffff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB898 : Ban 29 5 splitV898 := viaBranch (ws := [splitV887,splitV132,splitV174,splitV888,splitV889,splitV234,splitV259,splitV354,splitV366,splitV890,splitV367,splitV402,splitV595,splitV891,splitV623,splitV696,splitV803,splitV657,splitV746,splitV834,splitV892,splitV658,splitV681,splitV893,splitV894,splitV895,splitV896,splitV897])
 (consBan splitB887 (consBan splitB132 (consBan splitB174 (consBan splitB888 (consBan splitB889 (consBan splitB234 (consBan splitB259 (consBan splitB354 (consBan splitB366 (consBan splitB890 (consBan splitB367 (consBan splitB402 (consBan splitB595 (consBan splitB891 (consBan splitB623 (consBan splitB696 (consBan splitB803 (consBan splitB657 (consBan splitB746 (consBan splitB834 (consBan splitB892 (consBan splitB658 (consBan splitB681 (consBan splitB893 (consBan splitB894 (consBan splitB895 (consBan splitB896 (consBan splitB897 (nilBan 29 4)))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV899 : List ℕ := [0xf00000,0x22222230f0f0ff,0x1555555400ff000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB899 : Ban 29 4 splitV899 := viaSmall (by decide +kernel) (by decide)

def splitV900 : List ℕ := [0x100000ff,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB900 : Ban 29 4 splitV900 := viaSmall (by decide +kernel) (by decide)

def splitV901 : List ℕ := [0x100000ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB901 : Ban 29 4 splitV901 := viaSmall (by decide +kernel) (by decide)

def splitV902 : List ℕ := [0x22222220f0f000,0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB902 : Ban 29 4 splitV902 := viaSmall (by decide +kernel) (by decide)

def splitV903 : List ℕ := [0x2222223000f0ff,0x22222230f0f0ff,0x1555555400ff000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB903 : Ban 29 4 splitV903 := viaSmall (by decide +kernel) (by decide)

def splitV904 : List ℕ := [0x22222230f0f0ff,0x111111100f00000,0x1555555400ff000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB904 : Ban 29 4 splitV904 := viaSmall (by decide +kernel) (by decide)

def splitV905 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444444f000f00,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB905 : Ban 29 4 splitV905 := viaSmall (by decide +kernel) (by decide)

def splitV906 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x2444444500f0fff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB906 : Ban 29 4 splitV906 := viaSmall (by decide +kernel) (by decide)

def splitV907 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x28888889f000fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB907 : Ban 29 4 splitV907 := viaSmall (by decide +kernel) (by decide)

def splitV908 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x26666667ff0ffff,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB908 : Ban 29 4 splitV908 := viaSmall (by decide +kernel) (by decide)

def splitV909 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x24444445f000f0f,0x2ccccccdf0f0fff,0x3dddddddfff0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB909 : Ban 29 4 splitV909 := viaSmall (by decide +kernel) (by decide)

def splitV910 : List ℕ := [0x22222230f0f0ff,0x19999998ff00000,0x1ddddddcffff000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB910 : Ban 29 4 splitV910 := viaSmall (by decide +kernel) (by decide)

def splitV911 : List ℕ := [0x1555555400ff000,0x177777770fff0ff,0x19999998ff00000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB911 : Ban 29 4 splitV911 := viaSmall (by decide +kernel) (by decide)

def splitV912 : List ℕ := [0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB912 : Ban 29 4 splitV912 := viaSmall (by decide +kernel) (by decide)

def splitV913 : List ℕ := [0x1555555400ff000,0x19999998ff00000,0x24444444f000f00,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB913 : Ban 29 4 splitV913 := viaSmall (by decide +kernel) (by decide)

def splitV914 : List ℕ := [0x1555555400ff000,0x19999998ff00000,0x24444444f000f00,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB914 : Ban 29 4 splitV914 := viaSmall (by decide +kernel) (by decide)

def splitV915 : List ℕ := [0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x2cccccccf0f0f00,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB915 : Ban 29 4 splitV915 := viaSmall (by decide +kernel) (by decide)

def splitV916 : List ℕ := [0x22222230f0f0ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x2ccccccdf0f0fff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB916 : Ban 29 5 splitV916 := viaBranch (ws := [splitV899,splitV133,splitV900,splitV901,splitV902,splitV903,splitV175,splitV205,splitV260,splitV389,splitV676,splitV434,splitV498,splitV904,splitV624,splitV905,splitV906,splitV907,splitV746,splitV752,splitV908,splitV819,splitV835,splitV909,splitV910,splitV911,splitV912,splitV913,splitV914,splitV915])
 (consBan splitB899 (consBan splitB133 (consBan splitB900 (consBan splitB901 (consBan splitB902 (consBan splitB903 (consBan splitB175 (consBan splitB205 (consBan splitB260 (consBan splitB389 (consBan splitB676 (consBan splitB434 (consBan splitB498 (consBan splitB904 (consBan splitB624 (consBan splitB905 (consBan splitB906 (consBan splitB907 (consBan splitB746 (consBan splitB752 (consBan splitB908 (consBan splitB819 (consBan splitB835 (consBan splitB909 (consBan splitB910 (consBan splitB911 (consBan splitB912 (consBan splitB913 (consBan splitB914 (consBan splitB915 (nilBan 29 4)))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV917 : List ℕ := [0xff000,0x888888800f0ff0,0xaaaaaab0ffffff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB917 : Ban 29 4 splitV917 := viaSmall (by decide +kernel) (by decide)

def splitV918 : List ℕ := [0x10000f0f,0x888888800f0ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB918 : Ban 29 4 splitV918 := viaSmall (by decide +kernel) (by decide)

def splitV919 : List ℕ := [0x10000f0f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB919 : Ban 29 4 splitV919 := viaSmall (by decide +kernel) (by decide)

def splitV920 : List ℕ := [0x222222300fffff,0x888888800f0ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB920 : Ban 29 4 splitV920 := viaSmall (by decide +kernel) (by decide)

def splitV921 : List ℕ := [0x222222300fffff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB921 : Ban 29 4 splitV921 := viaSmall (by decide +kernel) (by decide)

def splitV922 : List ℕ := [0x222222300fffff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB922 : Ban 29 4 splitV922 := viaSmall (by decide +kernel) (by decide)

def splitV923 : List ℕ := [0x888888800f0ff0,0x88888880f00000,0xaaaaaab0ffffff,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB923 : Ban 29 4 splitV923 := viaSmall (by decide +kernel) (by decide)

def splitV924 : List ℕ := [0x888888800f0ff0,0xaaaaaaa0fff0f0,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB924 : Ban 29 4 splitV924 := viaSmall (by decide +kernel) (by decide)

def splitV925 : List ℕ := [0x888888800f0ff0,0xaaaaaab0f00fff,0xaaaaaab0ffffff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB925 : Ban 29 4 splitV925 := viaSmall (by decide +kernel) (by decide)

def splitV926 : List ℕ := [0x888888800f0ff0,0xaaaaaab0f00fff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB926 : Ban 29 4 splitV926 := viaSmall (by decide +kernel) (by decide)

def splitV927 : List ℕ := [0x888888800f0ff0,0xaaaaaab0f00fff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB927 : Ban 29 4 splitV927 := viaSmall (by decide +kernel) (by decide)

def splitV928 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ffffff,0x19999998ff00000,0x1ddddddcffff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB928 : Ban 29 4 splitV928 := viaSmall (by decide +kernel) (by decide)

def splitV929 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbfffffff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB929 : Ban 29 4 splitV929 := viaSmall (by decide +kernel) (by decide)

def splitV930 : List ℕ := [0x888888800f0ff0,0xaaaaaab0ffffff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB930 : Ban 29 5 splitV930 := viaBranch (ws := [splitV917,splitV918,splitV919,splitV920,splitV921,splitV922,splitV43,splitV313,splitV74,splitV396,splitV407,splitV439,splitV923,splitV500,splitV924,splitV925,splitV926,splitV927,splitV537,splitV585,splitV625,splitV673,splitV698,splitV721,splitV770,splitV791,splitV804,splitV820,splitV837,splitV854,splitV928,splitV870,splitV929,splitV648,splitV730,splitV650,splitV741,splitV774,splitV858])
 (consBan splitB917 (consBan splitB918 (consBan splitB919 (consBan splitB920 (consBan splitB921 (consBan splitB922 (consBan splitB43 (consBan splitB313 (consBan splitB74 (consBan splitB396 (consBan splitB407 (consBan splitB439 (consBan splitB923 (consBan splitB500 (consBan splitB924 (consBan splitB925 (consBan splitB926 (consBan splitB927 (consBan splitB537 (consBan splitB585 (consBan splitB625 (consBan splitB673 (consBan splitB698 (consBan splitB721 (consBan splitB770 (consBan splitB791 (consBan splitB804 (consBan splitB820 (consBan splitB837 (consBan splitB854 (consBan splitB928 (consBan splitB870 (consBan splitB929 (consBan splitB648 (consBan splitB730 (consBan splitB650 (consBan splitB741 (consBan splitB774 (consBan splitB858 (nilBan 29 4))))))))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV931 : List ℕ := [0xf00f0,0x1555555400ff000,0x177777770fff0ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB931 : Ban 29 4 splitV931 := viaSmall (by decide +kernel) (by decide)

def splitV932 : List ℕ := [0x4444445000000f,0x888888800f0ff0,0x1555555400ff000,0x177777770fff0ff,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB932 : Ban 29 4 splitV932 := viaSmall (by decide +kernel) (by decide)

def splitV933 : List ℕ := [0x4444445000000f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB933 : Ban 29 4 splitV933 := viaSmall (by decide +kernel) (by decide)

def splitV934 : List ℕ := [0x4444445000000f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB934 : Ban 29 4 splitV934 := viaSmall (by decide +kernel) (by decide)

def splitV935 : List ℕ := [0x666666700ff0ff,0x888888800f0ff0,0x1555555400ff000,0x177777770fff0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB935 : Ban 29 4 splitV935 := viaSmall (by decide +kernel) (by decide)

def splitV936 : List ℕ := [0x666666700ff0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB936 : Ban 29 4 splitV936 := viaSmall (by decide +kernel) (by decide)

def splitV937 : List ℕ := [0x666666700ff0ff,0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB937 : Ban 29 4 splitV937 := viaSmall (by decide +kernel) (by decide)

def splitV938 : List ℕ := [0x888888800f0ff0,0x111111100f00000,0x1555555400ff000,0x177777770fff0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB938 : Ban 29 4 splitV938 := viaSmall (by decide +kernel) (by decide)

def splitV939 : List ℕ := [0x888888800f0ff0,0x133333320fff0f0,0x1555555400ff000,0x177777770fff0ff,0x19999998ff00000]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB939 : Ban 29 4 splitV939 := viaSmall (by decide +kernel) (by decide)

def splitV940 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x177777770f0f00f,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB940 : Ban 29 4 splitV940 := viaSmall (by decide +kernel) (by decide)

def splitV941 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x177777770fff0ff,0x19999998fff0ff0,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB941 : Ban 29 4 splitV941 := viaSmall (by decide +kernel) (by decide)

def splitV942 : List ℕ := [0x1555555400ff000,0x177777770f0f00f,0x177777770fff0ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB942 : Ban 29 4 splitV942 := viaSmall (by decide +kernel) (by decide)

def splitV943 : List ℕ := [0x1555555400ff000,0x177777770f0f00f,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB943 : Ban 29 4 splitV943 := viaSmall (by decide +kernel) (by decide)

def splitV944 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x177777770fff0ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB944 : Ban 29 5 splitV944 := viaBranch (ws := [splitV931,splitV72,splitV10,splitV253,splitV25,splitV932,splitV933,splitV934,splitV935,splitV936,splitV937,splitV426,splitV462,splitV938,splitV559,splitV939,splitV567,splitV940,splitV626,splitV699,splitV722,splitV771,splitV805,splitV941,splitV838,splitV648,splitV659,splitV682,splitV649,splitV942,splitV943,splitV885,splitV893,splitV911,splitV897])
 (consBan splitB931 (consBan splitB72 (consBan splitB10 (consBan splitB253 (consBan splitB25 (consBan splitB932 (consBan splitB933 (consBan splitB934 (consBan splitB935 (consBan splitB936 (consBan splitB937 (consBan splitB426 (consBan splitB462 (consBan splitB938 (consBan splitB559 (consBan splitB939 (consBan splitB567 (consBan splitB940 (consBan splitB626 (consBan splitB699 (consBan splitB722 (consBan splitB771 (consBan splitB805 (consBan splitB941 (consBan splitB838 (consBan splitB648 (consBan splitB659 (consBan splitB682 (consBan splitB649 (consBan splitB942 (consBan splitB943 (consBan splitB885 (consBan splitB893 (consBan splitB911 (consBan splitB897 (nilBan 29 4))))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV945 : List ℕ := [0x1f00000f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB945 : Ban 29 4 splitV945 := viaSmall (by decide +kernel) (by decide)

def splitV946 : List ℕ := [0x1f00000f,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB946 : Ban 29 4 splitV946 := viaSmall (by decide +kernel) (by decide)

def splitV947 : List ℕ := [0x888888800000f0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB947 : Ban 29 4 splitV947 := viaSmall (by decide +kernel) (by decide)

def splitV948 : List ℕ := [0x888888800f0ff0,0xaaaaaabff000ff,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB948 : Ban 29 4 splitV948 := viaSmall (by decide +kernel) (by decide)

def splitV949 : List ℕ := [0x888888800f0ff0,0xaaaaaabff000ff,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB949 : Ban 29 4 splitV949 := viaSmall (by decide +kernel) (by decide)

def splitV950 : List ℕ := [0x888888800f0ff0,0xaaaaaabff000ff,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB950 : Ban 29 4 splitV950 := viaSmall (by decide +kernel) (by decide)

def splitV951 : List ℕ := [0x888888800f0ff0,0x11111110000f000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB951 : Ban 29 4 splitV951 := viaSmall (by decide +kernel) (by decide)

def splitV952 : List ℕ := [0x888888800f0ff0,0x13333333ff0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB952 : Ban 29 4 splitV952 := viaSmall (by decide +kernel) (by decide)

def splitV953 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbba0f0f0f0,0x1bbbbbbbff0f0ff]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB953 : Ban 29 4 splitV953 := viaSmall (by decide +kernel) (by decide)

def splitV954 : List ℕ := [0x13333333ff0f00f,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB954 : Ban 29 4 splitV954 := viaSmall (by decide +kernel) (by decide)

def splitV955 : List ℕ := [0x13333333ff0f00f,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB955 : Ban 29 4 splitV955 := viaSmall (by decide +kernel) (by decide)

def splitV956 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x1bbbbbbbff0f0ff,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB956 : Ban 29 5 splitV956 := viaBranch (ws := [splitV945,splitV946,splitV468,splitV167,splitV482,splitV947,splitV427,splitV463,splitV948,splitV949,splitV950,splitV951,splitV539,splitV952,splitV587,splitV607,splitV953,splitV674,splitV700,splitV723,splitV772,splitV792,splitV806,splitV929,splitV659,splitV705,splitV756,splitV808,splitV855,splitV871,splitV954,splitV955,splitV894,splitV912])
 (consBan splitB945 (consBan splitB946 (consBan splitB468 (consBan splitB167 (consBan splitB482 (consBan splitB947 (consBan splitB427 (consBan splitB463 (consBan splitB948 (consBan splitB949 (consBan splitB950 (consBan splitB951 (consBan splitB539 (consBan splitB952 (consBan splitB587 (consBan splitB607 (consBan splitB953 (consBan splitB674 (consBan splitB700 (consBan splitB723 (consBan splitB772 (consBan splitB792 (consBan splitB806 (consBan splitB929 (consBan splitB659 (consBan splitB705 (consBan splitB756 (consBan splitB808 (consBan splitB855 (consBan splitB871 (consBan splitB954 (consBan splitB955 (consBan splitB894 (consBan splitB912 (nilBan 29 4)))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV957 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x2cccccccf0f0ff0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB957 : Ban 29 4 splitV957 := viaSmall (by decide +kernel) (by decide)

def splitV958 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x35555554f0fff00]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB958 : Ban 29 4 splitV958 := viaSmall (by decide +kernel) (by decide)

def splitV959 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x3ddddddcff00f00]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB959 : Ban 29 4 splitV959 := viaSmall (by decide +kernel) (by decide)

def splitV960 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x24444444f000f00,0x24444445f000f0f,0x3ddddddcff00f00]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB960 : Ban 29 4 splitV960 := viaSmall (by decide +kernel) (by decide)

def splitV961 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x24444445f000f0f,0x3ddddddcff00f00]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB961 : Ban 29 4 splitV961 := viaSmall (by decide +kernel) (by decide)

def splitV962 : List ℕ := [0x888888800f0ff0,0x19999998ff00000,0x24444444f000f00,0x24444445f000f0f,0x35555554f0fff00]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB962 : Ban 29 4 splitV962 := viaSmall (by decide +kernel) (by decide)

def splitV963 : List ℕ := [0x888888800f0ff0,0x19999998ff00000,0x24444445f000f0f,0x35555554f0fff00]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB963 : Ban 29 4 splitV963 := viaSmall (by decide +kernel) (by decide)

def splitV964 : List ℕ := [0x1555555400ff000,0x19999998ff00000,0x24444444f000f00,0x24444445f000f0f,0x2cccccccf0f0ff0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB964 : Ban 29 4 splitV964 := viaSmall (by decide +kernel) (by decide)

def splitV965 : List ℕ := [0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f,0x2cccccccf0f0ff0]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB965 : Ban 29 4 splitV965 := viaSmall (by decide +kernel) (by decide)

def splitV966 : List ℕ := [0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444444f000f00,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB966 : Ban 29 5 splitV966 := viaBranch (ws := [splitV109,splitV146,splitV428,splitV464,splitV540,splitV588,splitV628,splitV682,splitV683,splitV705,splitV730,splitV706,splitV731,splitV739,splitV747,splitV754,splitV957,splitV958,splitV959,splitV960,splitV839,splitV840,splitV961,splitV857,splitV962,splitV872,splitV873,splitV963,splitV896,splitV964,splitV913,splitV914,splitV965])
 (consBan splitB109 (consBan splitB146 (consBan splitB428 (consBan splitB464 (consBan splitB540 (consBan splitB588 (consBan splitB628 (consBan splitB682 (consBan splitB683 (consBan splitB705 (consBan splitB730 (consBan splitB706 (consBan splitB731 (consBan splitB739 (consBan splitB747 (consBan splitB754 (consBan splitB957 (consBan splitB958 (consBan splitB959 (consBan splitB960 (consBan splitB839 (consBan splitB840 (consBan splitB961 (consBan splitB857 (consBan splitB962 (consBan splitB872 (consBan splitB873 (consBan splitB963 (consBan splitB896 (consBan splitB964 (consBan splitB913 (consBan splitB914 (consBan splitB965 (nilBan 29 4))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

def splitV967 : List ℕ := [0x22222230f0f0ff,0x888888800f0ff0,0x1555555400ff000,0x19999998ff00000,0x24444445f000f0f]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem splitB967 : Ban 29 6 splitV967 := viaBranch (ws := [splitV0,splitV1,splitV2,splitV14,splitV32,splitV33,splitV50,splitV78,splitV79,splitV80,splitV81,splitV102,splitV113,splitV140,splitV141,splitV142,splitV143,splitV144,splitV179,splitV206,splitV207,splitV229,splitV264,splitV287,splitV288,splitV289,splitV325,splitV353,splitV360,splitV372,splitV397,splitV398,splitV409,splitV429,splitV441,splitV465,splitV466,splitV477,splitV502,splitV512,splitV513,splitV521,splitV541,splitV542,splitV560,splitV569,splitV589,splitV597,splitV598,splitV609,splitV629,splitV630,splitV631,splitV641,splitV651,splitV660,splitV675,splitV684,splitV685,splitV702,splitV707,splitV725,splitV732,splitV733,splitV742,splitV749,splitV757,splitV775,splitV794,splitV809,splitV810,splitV821,splitV842,splitV859,splitV860,splitV875,splitV886,splitV898,splitV916,splitV930,splitV944,splitV956,splitV966])
 (consBan splitB0 (consBan splitB1 (consBan splitB2 (consBan splitB14 (consBan splitB32 (consBan splitB33 (consBan splitB50 (consBan splitB78 (consBan splitB79 (consBan splitB80 (consBan splitB81 (consBan splitB102 (consBan splitB113 (consBan splitB140 (consBan splitB141 (consBan splitB142 (consBan splitB143 (consBan splitB144 (consBan splitB179 (consBan splitB206 (consBan splitB207 (consBan splitB229 (consBan splitB264 (consBan splitB287 (consBan splitB288 (consBan splitB289 (consBan splitB325 (consBan splitB353 (consBan splitB360 (consBan splitB372 (consBan splitB397 (consBan splitB398 (consBan splitB409 (consBan splitB429 (consBan splitB441 (consBan splitB465 (consBan splitB466 (consBan splitB477 (consBan splitB502 (consBan splitB512 (consBan splitB513 (consBan splitB521 (consBan splitB541 (consBan splitB542 (consBan splitB560 (consBan splitB569 (consBan splitB589 (consBan splitB597 (consBan splitB598 (consBan splitB609 (consBan splitB629 (consBan splitB630 (consBan splitB631 (consBan splitB641 (consBan splitB651 (consBan splitB660 (consBan splitB675 (consBan splitB684 (consBan splitB685 (consBan splitB702 (consBan splitB707 (consBan splitB725 (consBan splitB732 (consBan splitB733 (consBan splitB742 (consBan splitB749 (consBan splitB757 (consBan splitB775 (consBan splitB794 (consBan splitB809 (consBan splitB810 (consBan splitB821 (consBan splitB842 (consBan splitB859 (consBan splitB860 (consBan splitB875 (consBan splitB886 (consBan splitB898 (consBan splitB916 (consBan splitB930 (consBan splitB944 (consBan splitB956 (consBan splitB966 (nilBan 29 5))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (by decide) (by decide +kernel) (by decide +kernel)

theorem restrictedBound : Wide 29 6 restrictedInputs := by
  have ess : ∀ a∈splitV967, ∃ i : Fin 29, ∀ b∈splitV967, b.testBit i.val≠b.testBit (29+i.val) → b=a := by decide +kernel
  have w := widen ess splitB967
  exact w

def caseInputs : List ℕ := [1107419535922439450879, 1162144876676450877440, 65793387195927629583, 39353054020120809456, 6148914676921004032, 7378697619443286016]
def projectRows : Projection 35 29 := pick [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28] rfl (by decide +kernel) (by decide)
theorem caseBound : Ban 35 7 caseInputs := viaCut projectRows restrictedBound (by decide) (by decide +kernel) (by decide +kernel)
def graph (x : Fin 6 → Bool) := Nat.testBit (4008372970 * 2 ^ 32 + 4004178592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def posBits : ℕ := 0x2144914e1479a69a68e38e369a69a4d34d338e38e2cb2cb1c71c7
def negBits : ℕ := 0x104104c106caa583caa583caa583caa583caa583caa583caa583
def sample (bank : ℕ) (i : Fin 35) (j : Fin 6) := bank.testBit (6*i.val+j.val)
def inputs : List ℕ := caseInputs
def seeds : List Wire := [(false,1107419535922439450879),(true,1162144876676450877440),(false,65793387195927629583),(false,39353054020120809456),(false,6148914676921004032),(false,7378697619443286016)]
set_option maxHeartbeats 1000000 in
theorem listed : ∀ i : Fin 35, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (35+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 35, graph (sample posBits i)=true ∧ graph (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 35, ∀ b∈inputs, b.testBit i.val≠b.testBit (35+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 35 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 6 C=graph) :
    ∃ k≤C.gates.countP counted, Live 35 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 6 → Bool) : C.eval (List.ofFn x)=graph x := congrFun eq x
  have good : Good 35 out.2 := by
    intro i hi same
    let j : Fin 35 := ⟨i,hi⟩
    have diff : read i out=read (35+i) out := by simp [read,same]
    have p := ev i;have n := ev (35+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa only [show reps seeds = inputs from rfl] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩


def witness : List Gate := [⟨.or,[3,5]⟩, ⟨.or,[2,4]⟩, ⟨.and,[1,7]⟩, ⟨.or,[6,7]⟩, ⟨.or,[2,3]⟩, ⟨.and,[8,10]⟩, ⟨.and,[0,9]⟩, ⟨.and,[6,11]⟩, ⟨.or,[12,13]⟩]
theorem upperMono : Monotone2 ⟨witness,14⟩ := by simp [Monotone2,witness]
theorem upperEq : ∀ x : Fin 6 → Bool, Circuit.eval ⟨witness,14⟩ (List.ofFn x)=graph x := by decide +kernel
end PEqualNP.Outside.L_meta_15877
open PEqualNP.Outside.L_meta_15877 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_15877 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4004178592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4004178592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
