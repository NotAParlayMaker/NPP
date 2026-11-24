import PEqualNP.Defs
-- Subgraph bounds and verification lemmas adapted from L_meta_2936.
namespace PEqualNP.Outside.L_meta_3563
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

def Live (target : Sig) (k t : Nat) (S : Finset Sig) : Prop :=
  ∀ M : Nat → Nat → Finset Sig → Prop,
  (∀ (hp : proper target), M 0 0 {target}) →
  (∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a) (hf : neg a ∉ insert a U) (tail : M k t (insert (neg a) U)), M (k+1) (t+1) (insert a U)) →
  (∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (ha : proper a) (hb : proper b) (hab : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (tail : M k t (insert (bin d a b) U)), M (k+1) t (insert a (insert b U))) → M k t S
theorem Live.stop {target : Sig} : ∀ (hp : proper target), Live target 0 0 {target} := by
  intro hp
  intro M stopStep unaryStep binaryStep
  exact stopStep hp
theorem Live.unary {target : Sig} : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a) (hf : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)), Live target (k+1) (t+1) (insert a U) := by
  intro k t  U  a  ha hf tail
  intro M stopStep unaryStep binaryStep
  exact unaryStep ha hf (tail M stopStep unaryStep binaryStep)
theorem Live.binary {target : Sig} : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (ha : proper a) (hb : proper b) (hab : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)), Live target (k+1) t (insert a (insert b U)) := by
  intro k t  U  a b  d  ha hb hab hf tail
  intro M stopStep unaryStep binaryStep
  exact binaryStep ha hb hab hf (tail M stopStep unaryStep binaryStep)
theorem Live.weakInduct {target : Sig} {M : Nat → Nat → Finset Sig → Prop} {k t : Nat} {S : Finset Sig} (h : Live target k t S)
    (stop : ∀ (hp : proper target), M 0 0 {target})
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a) (hf : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) (ih : M k t (insert (neg a) U)), M (k+1) (t+1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (ha : proper a) (hb : proper b) (hab : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) (ih : M k t (insert (bin d a b) U)), M (k+1) t (insert a (insert b U)))
    : M k t S := by
  apply And.right (a := Live target k t S)
  apply h (fun k t S => Live target k t S ∧ M k t S)
  · intro hp
    exact ⟨Live.stop hp, stop hp ⟩
  · intro k t  U  a  ha hf tail
    exact ⟨Live.unary ha hf tail.1, unary ha hf tail.1 tail.2⟩
  · intro k t  U  a b  d  ha hb hab hf tail
    exact ⟨Live.binary ha hb hab hf tail.1, binary ha hb hab hf tail.1 tail.2⟩
theorem Live.induct {target : Sig} {M : ∀ (k t : Nat) (S : Finset Sig), Live target k t S → Prop} {k t : Nat} {S : Finset Sig} (h : Live target k t S)
    (stop : ∀ (hp : proper target), M 0 0 {target} (Live.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a) (hf : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) (ih : M k t (insert (neg a) U) tail), M (k+1) (t+1) (insert a U) (Live.unary ha hf tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (ha : proper a) (hb : proper b) (hab : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) (ih : M k t (insert (bin d a b) U) tail), M (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hf tail))
    : M k t S h := by
  apply Live.weakInduct (M := fun k t S => ∀ z, M k t S z) h _ _ _ h
  · intro hp z
    exact stop hp 
  · intro k t  U  a  ha hf tail ih z
    exact unary ha hf tail (ih tail)
  · intro k t  U  a b  d  ha hb hab hf tail ih z
    exact binary ha hb hab hf tail (ih tail)


lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.induct with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using Live.induct with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)



lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]




abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

def Reach {R : Type} (roots : List (Wire R)) (p : Nat) (bank : List (Wire R)) : Prop :=
  ∀ M : Nat → List (Wire R) → Prop,
  (M 0 roots) →
  (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (tail : M p bank) (ha : Available bank a), M (p+1) (inv a :: bank)) →
  (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (tail : M p bank) (ha : Available bank a) (hb : Available bank b), M (p+1) (combine op a b :: bank)) → M p bank
theorem Reach.start {R : Type} {roots : List (Wire R)} : Reach roots 0 roots := by
  intro M startStep oneStep twoStep
  exact startStep 
theorem Reach.one {R : Type} {roots : List (Wire R)} : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (tail : Reach roots p bank) (ha : Available bank a), Reach roots (p+1) (inv a :: bank) := by
  intro p  bank  a  tail ha
  intro M startStep oneStep twoStep
  exact oneStep (tail M startStep oneStep twoStep) ha
theorem Reach.two {R : Type} {roots : List (Wire R)} : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (tail : Reach roots p bank) (ha : Available bank a) (hb : Available bank b), Reach roots (p+1) (combine op a b :: bank) := by
  intro p  bank  a b  op tail ha hb
  intro M startStep oneStep twoStep
  exact twoStep op (tail M startStep oneStep twoStep) ha hb
theorem Reach.weakInduct {R : Type} {roots : List (Wire R)} {M : Nat → List (Wire R) → Prop} {p : Nat} {bank : List (Wire R)} (h : Reach roots p bank)
    (start : M 0 roots)
    (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (tail : Reach roots p bank) (ha : Available bank a) (ih : M p bank), M (p+1) (inv a :: bank))
    (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (tail : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) (ih : M p bank), M (p+1) (combine op a b :: bank))
    : M p bank := by
  apply And.right (a := Reach roots p bank)
  apply h (fun p bank => Reach roots p bank ∧ M p bank)
  · exact ⟨Reach.start , start  ⟩
  · intro p  bank  a  tail ha
    exact ⟨Reach.one tail.1 ha, one tail.1 ha tail.2⟩
  · intro p  bank  a b  op tail ha hb
    exact ⟨Reach.two op tail.1 ha hb, two op tail.1 ha hb tail.2⟩
theorem Reach.induct {R : Type} {roots : List (Wire R)} {M : ∀ (p : Nat) (bank : List (Wire R)), Reach roots p bank → Prop} {p : Nat} {bank : List (Wire R)} (h : Reach roots p bank)
    (start : M 0 roots (Reach.start ))
    (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (tail : Reach roots p bank) (ha : Available bank a) (ih : M p bank tail), M (p+1) (inv a :: bank) (Reach.one tail ha))
    (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (tail : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) (ih : M p bank tail), M (p+1) (combine op a b :: bank) (Reach.two op tail ha hb))
    : M p bank h := by
  apply Reach.weakInduct (M := fun p bank => ∀ z, M p bank z) h _ _ _ h
  · intro z
    exact start  
  · intro p  bank  a  tail ha ih z
    exact one tail ha (ih tail)
  · intro p  bank  a b  op tail ha hb ih z
    exact two op tail ha hb (ih tail)


def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R : Type} (goal : Wire R) (s : Nat) (ws : List (Wire R)) : Prop :=
  ∀ M : Nat → List (Wire R) → Prop,
  (M 0 [goal]) →
  (∀ {s : Nat} {xs zs : List (Wire R)} (eq : xs.Perm zs) (tail : M s xs), M s zs) →
  (∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (tail : M s (inv a :: kept save a rest)), M (s+1) (a :: rest)) →
  (∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Bool) (ka : Bool) (kb : Bool) (tail : M s (combine op a b :: kept ka a (kept kb b rest))), M (s+1) (a :: b :: rest)) → M s ws
theorem Run.stop {R : Type} {goal : Wire R} : Run goal 0 [goal] := by
  intro M stopStep permStep oneStep twoStep
  exact stopStep 
theorem Run.perm {R : Type} {goal : Wire R} : ∀ {s : Nat} {xs zs : List (Wire R)} (eq : xs.Perm zs) (tail : Run goal s xs), Run goal s zs := by
  intro s  xs zs  eq tail
  intro M stopStep permStep oneStep twoStep
  exact permStep eq (tail M stopStep permStep oneStep twoStep)
theorem Run.one {R : Type} {goal : Wire R} : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (tail : Run goal s (inv a :: kept save a rest)), Run goal (s+1) (a :: rest) := by
  intro s  a  rest  save tail
  intro M stopStep permStep oneStep twoStep
  exact oneStep save (tail M stopStep permStep oneStep twoStep)
theorem Run.two {R : Type} {goal : Wire R} : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Bool) (ka : Bool) (kb : Bool) (tail : Run goal s (combine op a b :: kept ka a (kept kb b rest))), Run goal (s+1) (a :: b :: rest) := by
  intro s  a b  rest  op ka kb tail
  intro M stopStep permStep oneStep twoStep
  exact twoStep op ka kb (tail M stopStep permStep oneStep twoStep)
theorem Run.weakInduct {R : Type} {goal : Wire R} {M : Nat → List (Wire R) → Prop} {s : Nat} {ws : List (Wire R)} (h : Run goal s ws)
    (stop : M 0 [goal])
    (perm : ∀ {s : Nat} {xs zs : List (Wire R)} (eq : xs.Perm zs) (tail : Run goal s xs) (ih : M s xs), M s zs)
    (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (tail : Run goal s (inv a :: kept save a rest)) (ih : M s (inv a :: kept save a rest)), M (s+1) (a :: rest))
    (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Bool) (ka : Bool) (kb : Bool) (tail : Run goal s (combine op a b :: kept ka a (kept kb b rest))) (ih : M s (combine op a b :: kept ka a (kept kb b rest))), M (s+1) (a :: b :: rest))
    : M s ws := by
  apply And.right (a := Run goal s ws)
  apply h (fun s ws => Run goal s ws ∧ M s ws)
  · exact ⟨Run.stop , stop  ⟩
  · intro s  xs zs  eq tail
    exact ⟨Run.perm eq tail.1, perm eq tail.1 tail.2⟩
  · intro s  a  rest  save tail
    exact ⟨Run.one save tail.1, one save tail.1 tail.2⟩
  · intro s  a b  rest  op ka kb tail
    exact ⟨Run.two op ka kb tail.1, two op ka kb tail.1 tail.2⟩
theorem Run.induct {R : Type} {goal : Wire R} {M : ∀ (s : Nat) (ws : List (Wire R)), Run goal s ws → Prop} {s : Nat} {ws : List (Wire R)} (h : Run goal s ws)
    (stop : M 0 [goal] (Run.stop ))
    (perm : ∀ {s : Nat} {xs zs : List (Wire R)} (eq : xs.Perm zs) (tail : Run goal s xs) (ih : M s xs tail), M s zs (Run.perm eq tail))
    (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (tail : Run goal s (inv a :: kept save a rest)) (ih : M s (inv a :: kept save a rest) tail), M (s+1) (a :: rest) (Run.one save tail))
    (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Bool) (ka : Bool) (kb : Bool) (tail : Run goal s (combine op a b :: kept ka a (kept kb b rest))) (ih : M s (combine op a b :: kept ka a (kept kb b rest)) tail), M (s+1) (a :: b :: rest) (Run.two op ka kb tail))
    : M s ws h := by
  apply Run.weakInduct (M := fun s ws => ∀ z, M s ws z) h _ _ _ _ h
  · intro z
    exact stop  
  · intro s  xs zs  eq tail ih z
    exact perm eq tail (ih tail)
  · intro s  a  rest  save tail ih z
    exact one save tail (ih tail)
  · intro s  a b  rest  op ka kb tail ih z
    exact two op ka kb tail (ih tail)


theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.induct generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.induct with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h using Live.induct generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h using Reach.induct generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.induct with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 1) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[seed]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = seed := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seed at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩ := extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)


def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.induct with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.induct with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.induct with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~seed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev BoundPool := (Sig) × (Nat) × (Nat) × (List Sig)
def BoundPool.domain (v : BoundPool) : Sig := v.1
def BoundPool.bound (v : BoundPool) : Nat := v.2.1
def BoundPool.paid (v : BoundPool) : Nat := v.2.2.1
def BoundPool.wires (v : BoundPool) : List Sig := v.2.2.2

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h


def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl) (fun _ _ _ hn => by contradiction) (fun _ _ _ _ _ hn => by contradiction) rfl
    exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev IndexTree (α : Type) := List α
def IndexTree.leaf {α} (xs : List α) : IndexTree α := xs
def IndexTree.fork {α} (_ : Nat) (a b : IndexTree α) : IndexTree α := a ++ b
def IndexTree.read {α} (xs : IndexTree α) (i : Nat) := xs[i]?
def IndexTree.values {α} (xs : IndexTree α) := xs
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := List.mem_of_getElem? e
abbrev Forest := (Nat) × (Nat) × (Nat → Bits × Bits) × (IndexTree ColumnInfo) × (Array (List Nat)) × (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (v : Forest) : Nat := v.1
def Forest.cap (v : Forest) : Nat := v.2.1
def Forest.samples (v : Forest) : Nat → Bits × Bits := v.2.2.1
def Forest.cols (v : Forest) : IndexTree ColumnInfo := v.2.2.2.1
def Forest.autos (v : Forest) : Array (List Nat) := v.2.2.2.2.1
def Forest.levels (v : Forest) : Nat → Packing := v.2.2.2.2.2.1
def Forest.index (v : Forest) : Nat → Nat → Option (Nat × Nat) := v.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl) (fun _ _ _ hn => by contradiction) (fun _ _ _ _ _ hn => by contradiction) rfl
    exact hT (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)


def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (IndexTree.leaf [])
def g15autos : Array (List Nat) := Array.mk [[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (IndexTree.fork 2 (IndexTree.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (IndexTree.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := Array.mk [[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (IndexTree.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := Array.mk [[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := Array.mk [(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (IndexTree.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := Array.mk [[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := Array.mk [(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (IndexTree.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := Array.mk [[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := Array.mk [(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (IndexTree.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := Array.mk [[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := Array.mk [(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (IndexTree.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := Array.mk [[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := Array.mk [(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (IndexTree.fork 4 (IndexTree.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (IndexTree.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := Array.mk [[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := Array.mk [(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (IndexTree.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := Array.mk [[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := Array.mk [(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (IndexTree.fork 19 (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (IndexTree.fork 2 (IndexTree.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (IndexTree.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (IndexTree.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (IndexTree.fork 2 (IndexTree.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (IndexTree.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (IndexTree.fork 2 (IndexTree.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (IndexTree.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (IndexTree.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (IndexTree.fork 2 (IndexTree.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (IndexTree.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := Array.mk [[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := Array.mk [(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (IndexTree.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := Array.mk [[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := Array.mk [(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (IndexTree.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := Array.mk [[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := Array.mk [(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (IndexTree.fork 29 (IndexTree.fork 14 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (IndexTree.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (IndexTree.fork 3 (IndexTree.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (IndexTree.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (IndexTree.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (IndexTree.fork 4 (IndexTree.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (IndexTree.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (IndexTree.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (IndexTree.fork 4 (IndexTree.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (IndexTree.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (IndexTree.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (IndexTree.fork 4 (IndexTree.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (IndexTree.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := Array.mk [[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat := 0x202e0
def deadd8 (i : Nat) : Nat := 0xa24b7baf6624ad253281df927589c4d52540d02
def deadl8 : Packing := (2,6,7,0,4,3,0,deadd8)
def deadd9 (i : Nat) : Nat := 0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600
def deadl9 : Packing := (25,5,7,1,4,9,0,deadd9)
def deadd10 (i : Nat) : Nat := (if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)
def deadl10 : Packing := (156,4,7,5,4,12,0,deadd10)
def deadd11 (i : Nat) : Nat := (if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))
def deadl11 : Packing := (183,3,7,8,4,14,0,deadd11)
def deadd12 (i : Nat) : Nat := 0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600
def deadl12 : Packing := (32,2,7,8,4,12,0,deadd12)
def deadd13 (i : Nat) : Nat := 0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00
def deadl13 : Packing := (4,1,7,5,4,8,0,deadd13)
def deadd14 (i : Nat) : Nat := 0x17e2b6526070604013ff
def deadl14 : Packing := (1,0,7,2,4,0,0,deadd14)
def deadsamples : Array (Bits × Bits) := Array.mk [(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (IndexTree.fork 63 (IndexTree.fork 31 (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (IndexTree.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (IndexTree.fork 4 (IndexTree.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (IndexTree.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (IndexTree.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (IndexTree.fork 4 (IndexTree.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (IndexTree.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (IndexTree.fork 16 (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (IndexTree.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (IndexTree.fork 4 (IndexTree.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (IndexTree.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (IndexTree.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (IndexTree.fork 4 (IndexTree.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (IndexTree.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (IndexTree.fork 31 (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (IndexTree.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (IndexTree.fork 4 (IndexTree.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (IndexTree.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (IndexTree.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (IndexTree.fork 4 (IndexTree.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (IndexTree.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (IndexTree.fork 16 (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (IndexTree.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (IndexTree.fork 4 (IndexTree.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (IndexTree.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (IndexTree.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (IndexTree.fork 4 (IndexTree.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (IndexTree.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := Array.mk [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def deadlevels : Nat → Packing
  | 8 => deadl8
  | 9 => deadl9
  | 10 => deadl10
  | 11 => deadl11
  | 12 => deadl12
  | 13 => deadl13
  | 14 => deadl14
  | _ => emptyPacking
def deadindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 0 9 1 4 (hashdeadl9)
  | 10 => lookupWord 17 61 5 13 5 4 (hashdeadl10)
  | 11 => lookupWord 124 434 7 16 8 4 (hashdeadl11)
  | 12 => lookupWord 137 475 8 16 8 4 (hashdeadl12)
  | 13 => lookupWord 26 148 3 13 5 4 (hashdeadl13)
  | 14 => lookupWord 7 47 1 10 2 4 (hashdeadl14)
  | _ => fun _ => none
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead8_0 : block dead 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8 : block dead 8 0 2=true := sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead14 : block dead 14 0 1=true := sdead14_0
theorem tablesdead : checkedTables dead 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block dead 0 0 0 = true)
  · exact (rfl : block dead 1 0 0 = true)
  · exact (rfl : block dead 2 0 0 = true)
  · exact (rfl : block dead 3 0 0 = true)
  · exact (rfl : block dead 4 0 0 = true)
  · exact (rfl : block dead 5 0 0 = true)
  · exact (rfl : block dead 6 0 0 = true)
  · exact (rfl : block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14
theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun


def idxBits8 (i : Nat) : Nat := 0x500e81
def dataBits8 (i : Nat) : Nat := 0x294285bde7aedc4aa95264d40a1af79abb712aa60593502a794ea745c32154164940
def lev8 : Packing := (3,7,7,0,0,4,0,dataBits8)
def idxBits9 (i : Nat) : Nat := 0x7bfabe80003f526da400021ee03cc5318198db600070ff87fc99cac8692f4a0d51db91b2000597e2e5bce9f701ea53aeb34daa29c5c580044e91000000008b800746504e0a52cb4330868291d51b2c1f95e89ebe02c388c29c955263249938a97472b16c0a44d2014bf3af4dfb5f8cc0661400041779b904630eab4238001cd30f2d10001c8785800794ca22c380011161269c8387213b503318e5c163d000000027047e4680211dd0168d7cf19a7b76b05bc000332a2af076259c254c3908000006ba5807c43b699280041321635000032d5adc190000c934e6b181aa051830000d0b0eebb9b7e8b533aa7a19d119b8896e094b9e1e4ca2afc21f4c934480ccf928b405cb0a37a800052bbd213dc3b70ac1ff22d42c0c70d848b7002c08128045a400cc181b62908b01429c90204108007c48d08041120a056166c000312400000
def dataBits9 (i : Nat) : Nat := (if i < 1 then 0x26a058ef752aa6198164d40a37eeb576d2b02c9a8163bdd4aa982605935022dfbad66370b8b26a051ef752aa6e17164d40c37e6518cdc2e2c9a8165bdd4aa9875c593502cb7ba9552ecb8b26a041ff371b86957164d4092fe6e30ed2ae2c9a8165bdd4aa9725c5935028f7ba955370b0b26a051ef752aa6dd6164d40b35eea554b12c2c9a8167b5d4aa98158593503e5cb04b1302b0b26a045bf75acc6e15164d40a3deea554dc2a2c9a8186fcca319b854593502ce7ba9552a4a8b26a059ed752aa6055164d40f93ac32cac0aa2c9a81f365825498154593503e8eaecb2ae2a8b26a07d595c9525c55164d408b7eeb598dc242c9a8147bdd4aa9b8485935030df9946337090b26a051ef752aa6dd2164d40a3deea554db242c9a8115fdd7b31b5485935028f7ba95536a90b26a041ff371a86d52164d4083fe6e370d2a42c9a8167add4aa96248593502cf6ba9552e290b26a07d395d9625c52164d408b7eeb19744422c9a8147dcda705b32159250227fbb16636ca9b24a060ff328c86d953649408b7eeb196a9b04c9281f62d6555162549925028dfbad5db4ec0b24a051bf75abb6958164940ab5eeb576aa302c928146fdd6aeda36059250387e974c3302a8b24a07c9d619656055164940dbcae8b8642a82c928107fddc2e8854c5925030bf974e390a98b24a061bf2e9c62153164940c3ee5d38642a62c928187f8ba700854c592503e5ab0cb1b0298b24a07cd661d8554d30649409b7ceb598c0a60c9281a7f0ca605514c192503e7a30cc0a6298324a041ff36dc85d9a564540f8aec3b0ab9aa6c8a8107fcdb72176689915020ff9b6e42ead1322a041ff36dc8595a264540a2feebd77552a4c8a8115fdd7b31b8549915030bf99463b70a9322a0517f75ebb6a15264540a2feebd76d32a4c8a8145fdd7aeda354991502aeb9b6b9aa6a9322a07c5b61d7560952645409bb66e2a6c12a4c8a81f34d8354d8254991503ea9ae6a9ae4a9322a0457f75ecc6d53264540f8e6c3ae6c1264c8a8115fdd732e55889915024bf9b8c3b4ab8b22a0586f752aaa227764d40b15eea555444ccc9a8164bdd4aaa77999935028b7ba95536e42b26a051af752aa6d88564d40a3ceea554d990ac9a8147add4aa9b2215935028f6ba95536242b26a051ee752aa6c08564d40b19eea555444aac9a81653dd4aaa7795593502cc7ba9554cd2ab26a051af752aa6d85264d40b1d6ea55544444c9a8165add4aaa7788993502cd5ba9554cd11326a059cb752aa9562264d40a2deea554db902c9a8143bdd4aa9b8085935028b7ba95536e10b26a051af752aa6d82164d40a39eea554da842c9a81479dd4aa9b3085935028f73a95536010b26a058ed752aaa221164d40b2daea5553bc22c9a8166b5d4aaa6684593502ce6ba9554ab08b26a059e9752aa88a1164d40 else 0x341c1000000000007008200033ba1066a420cd48400cd4873521cdb0400cc30730c100000ce2840000019c508000cc3073521066a42000000cc104198208336c1066083982080198208019820e6d820066d820cc107352100000066d82000019c508019820e618200000c0e0e8382006914200d0800001706842161085842121085842101f0701c1e0704000000000000d1b0400000000000000000000000000000000000000000000000002b856bacd586ae54aa8b5029dd36a634b293d22a3b42e835019f93aa72cd399d2f25bcb294123a3e4778e5182274498890fe1d42884707a0cc1481eff5fc3f37dcf71e53c5766eb9d4ba473ee69c43836e2db1ad355686cc59632762ac4185af95ceb896eacb58cad15129d530a4d472894ee9c936a684c69452624746a88d0f21942883cfe9eb3cc784e79bd3706ccd719c3145e0b31542844c08f10c20e4087e8f81e63b8748e41be368640c317c2e45a0af1542945009b12c244460871041f43c0730dc1a43205f0b41542804b08c1041e0370640b41402303c0640a00f014014007c5761d855cd5365940a2feebd77552a4cb28115fdd7b31b8549965030bf99463b70a932ca0517f75ebb6a15265940aa7eebd76b1aa4cb281575cdb5cd5354996503e2db0ebab04a932ca04ddb371536095265940f9a6c1aa6c12a4cb281f54d7354d72549965022bfbaf6636a9932ca07c7361d7360932659408afeeb9972ac44cb281f5657254971545965026b7baf662a4a0b2ca045fb74acc6dd31659408afeebd98daa42cb28147bdd4aa9b85d993502cb7ba95530ebb326a041ff36dc85d9a564d40b1deea554c3b0ac9a8147bdd4aa9b85d593502cb7ba95530ebab26a051ef752aa6e16564d40a3deea554dbacac9a8166bdd4aa98659593502cd7ba9552ecb2b26a059cf752aa6156564d40f83ec3aecc2acac9a8147bdd4aa9b758993502cd7ba9552ecb1326a059af752aa5956264d40f876c3aecc12c4c9a8145fdd7aeeaa549935030f7d76e2554a9326a0457f75ecc6e15264d40a3deea554dc2a4c9a8185fcca31db8549935028bfbaf5db50a9326a051ef752aa6dd5264d40b2deea5545baa4c9a8115fdd7b31b6549935028f7ba95536ca9326a041ff371a86d95264d40c2fe6518edb2a4c9a8145fdd7aeda654993502ce7ba9552eaa9326a059eb752aa6095264d40f8b6c3aeac12a4c9a8167add4aa972549935022bfbae65cab11326a051bf75abbaa98164d40c3df5db8955302c9a8146fdd6aeda760593502cd7ba95516cc0b)
def lev9 : Packing := (165,6,7,0,0,11,0,dataBits9)
def idxBits10 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x33d1f449e51fa0414c400054797169487ce9779b0b3b00274eb94cd3bbefc576e06742fdc76915a924800092d800007400000a524326e41b5da46543c090e11f09a296dc8aff2140ce0d3ca7d4000028df16e00025218000c8fdb74cd85d488ab21c8b0d74a85d272193a6ed9b332c39b3866b318b500000000121100000001447cce529b400c6a45aa2129f0000000030990658b7b941f554489f600716e62a55b09c00140001cff0563a8ab75702038aa0157ae72518789b2072b0e7a2094a64604c000000055e16209e96ae4f80dc0b04b80a9a78000019e7adf6da5b0c68735a9c294751796c80001af7b42cda31b1dc058951a62f20000c90bbfd000119b741634db56e641f909c2c1dada80000a799c19d3e687400007d8b666e40f98f70000562e572000061b1bbab35eb2d30e272330e2e2a7bbbff95a167b171272dc720253940004d540000043c86539990346acc7119984397f6000196f00000000000181d10b93536343b15ad57921a3204ad6fe98140c55638dca28e4b6e83842e7b26ad423ce5d5f5d01edb4de54313515b23960f038c00035b80b06eaa7dbe0000cbed11c04b474540001a46c525fb8e5b22d83aef48000807a6c2515bb9b7e9f5a4960069b857516583dcd5e134649a15ee2abc3e2b7aab070e0801c1866babc130af16e0445abd111c6ae500011528f005c2b8198411cc178271b3b749a4000000036586834000241f000000008620058340021050005e150681c1a150583836051a03814030904406198485028051818c60010a800881b1b8183e010382814426801c1400010088420090080a03028fc020c3a00c5a110000020020784d920055070000801028283e031380a012b8dc0800258180e21119bc28182d90400230c824581a00840b22f068608002120bc02030404c2e0105310420209034dc060608804110683c0a00048041005000103e000d15008180201852401387402162884c080a05808120d090580c0d030040a0d0001400000101c06030b03c0e3a0981836010501c0c0e0101458292991410021803800000d0282c03010000a000284012193a0080200010000e04000101e170204802000005450000c8040201098dc2c1400004040200014040902034000214808040f02810080115000001306824360004044201900840300501814025002174040004800060b0184c1c000112414060000000070101018000282c02040509c560000030000210800000d0180016010f800080c0081022040503c0001000085c00071e40a000403014050281c56030508832000900000080000036050800022020b820540c0284402000000010021200806030080000001980c000a110040c040280408030902c020a068040001040004801058a042180283036010c8440e01078082c080201c0001018440408 else 0xc30600018b07095a687c2cb50c92450ce31bbc163c4a0fc4ec215ea28e33f67bc319ae1aa511144f0782c660329536e069621bb3909035081a348dee8978499776b49082aeb000117ee9819ce8b939864c0aa6dc94a40d486746837000010042a94e950981d445334a9443a367f6fdad4f9e0421793bfee118bac12949d7eb5125387e2ad630f8cb66656c81ea0369659144277c170684065abb48488eece3a4609d4c90c6ce3df992a05ac4bf0f3ea0ef781a8b62a43d2c0f9034a1541a1bed8104642d3500004e979cda8cddb4fc8df54e5d7d515e6000840b234e2c200440002cff0c6a019800052cf0001d8595b2c92fcd10000389bc9c778d4dabd441c268474c8fe1965650300000000f33a5e655640002e8c8000c87400019fa8000e473218702d8bbb511711a44f96aa5bc3d9844ee004c000000002e7f7d8ce4b00002e665b9c000000035a47cb711d98a7b9ed0dd4e570000000068b0ad4c186835b2d43c508c3b4da4c301e7a1ae740000000d10821381e39dfea1ecd66c0006817c36bb5ffe23464d00015345d765d60015000000007c5e26ed574567743382abc00015db3e2a61feb14d8b7ca300cbc000112e80a956bf2ed65da7d48731d36e900c1028000067782cd0000955ecf99a0c00000000000187e90066b2cc7fc0001a350000000000075490000a010f2900000001b3b18cb6854d16c0000000422ebd40000000000000000cd4764d0587c40f6611c729371a8fb446b61e00003d8cec5b4190000e755d176f238a0c00000003e35dbb800013b3c574107000018f30b38962d436df3ed4bfcc49188367beddcdb990001b92199e8000b474891810bf846450a000000033b204f60003c470b210001e0213688000c91a78140000000cab400030d4e856f067e9dc64b0cf0fa0c683aec2fa053c278d9f31a220a703cb0561d4f9a8486d3112c33e8050001644e35504bb05b79230c7c0924a75a53ad2b2b28013bef0fd06ce9353705e50f4e7cc0346f5c291f51e5b90ca9f8cc00039c466b2c32e271000078b200009ade01b00017aa61bc63149975967923131762bfb318ef224578a2d400007147c4561836b5320980000000c0840006552fa24000146a2a4c59ea64c1961ca7280e955dd5c6612c3a12ea8b6f2fc57a23b658b50c19c8bbac1b1f849fb1b16dc4dacf29e372c73f312c56344eae74ee7732f1618a2d369238e7e5cafc38b3b4b18511360cc9e9b5856422402e2a7891b4642867a8e130a56000054dc396b6000000b67cf3800001d3f0001026ea3373a0e044c34e686fab107011a38000715300000001965f80117bf728605712908af980abf671598f0bda456e3062ba151820d797ea986e5c0d9e896b51e6a7ae4acd1338add87678263c3d9cb1899db4e10970952c476871b1ef7266e80af988859ab8f0001) else (if i < 3 then 0x62cfd01cf0ee0001638400000005d7a000000043e7103916d73628d44d622215d8ba10faf37b3b4c0002d9300000001e6158c6fa7dcbba8e1827eb4ab43f3d3620b58835fb57b2fbccf0b3fd31e74b8000e2b3ba624fd14010335f8ae6e1be085c46c7a32a15d97b1cf6c579f6e25443f0a0ddb2605dc4a8ace2476411429c1317c8691c90993168a76f49606cb089628c0000000ed9ba2ec61052783cd2726699a20bdb041651a6c6fa01217876eeb3b95a1114e631c000425931c400006af8481b779eb340006c91814560654324d6db9a400039816e17777b317c0004cf2a4290aaae5945531d920000e4c0000e3d38cf08070000c04ec59db2ee46e13c60001825566c0000949c000000000006ac00c9725eb82dc12cca384893bf92a7f320cc6ff5ce94dfd7c0d58990fb2169411245c32f527b348981a367756f148c0000346270c2703bba8f90c0001052bace55fe37055f1b357faaa48f971100002104000398471bf0000d275760a6370beb7620ae876ac0000000090a927947d2e2840007b6c5d380001dfb0e3f0000ec140000000d810d2415938000b680f4b00000000094cebe5461000057f44670000000009be000000015e70001c86c000242d51ad097f26b5e3e00000000743414c4bf0000000059940000000235a6e790000946eea5800079c94b240002ad90000b5440c1f1a00000caf80006a410000d23f531488a457e6620000031051d60001a6bf96965b0e5b4d31800070dc00005a3b6550a3883435fa54d8489bb80cdd59995e9278eff5cd000009faad0400038fe69f20000000280900018fdf6b845dd66551407225064a9506f13272016a8000015596ccc61441180001dec8000c625aa63a41e4d97c65ba16912b51ee3540bf12923dc45047d59b2b482000b6d62fa059289920079b4156a8000f0de24340004eb800000001c93a3dbba67d0cc00060ad00005981aa30000d79a86000006c7cb5daf029147469d69b54420f1c4bfec0b8496c0007e2f71400002d536ad70000168c0006db0d082cfa0c01490c5ac4000000000009600b92400079bb0000af8323245dadd03a6841148e4569e26b1d4c4b00fc9a0dafc9aac612d96baefa5f5eb61d10bb120c4f085f0000ce5d2e56b2bdb6fe4a0d9153ea6244973b046850870f3891c000380b6d89e36044f80000000ae0511000001639589bc066aefd2d6000000029708551456bb65918f0001f8b1c96de4f0001b6f9b066d302694624a5f2f95bc8ea51c4ab3de25d7a5142cef61163845470e0414ed7572b9cf39c2284219a786055c1d8000e0d17009455bc78ad26eeb8d22000052520000da1be82bd33f77c1d880005aa1d99be39ba3d7546000197d05050181b5cc23a227433c83211047eda011d170f80003de360c027a8ccdf6b5ad140a5ba7c440facff37a2de2 else (if i < 4 then 0x39fcaa00000197965682bc80001ac0cab901b699c341f8c1100000003d352ec0595bb44424af17e7b4b03146ce79870000a8bcd07fb4bc4c0655c52504a76791322edd1bc92cac800000000000000192a9f39868c000000039e481a6743337cf700aaaea84b03e66ebce56d640e9f1a70a44787acc941b14a4cab2e6afb0cfe81d9033f069fb4d05ed0001c759003ce76ac4280b8affba8f09290382ad8f67c8305371b87d92ab0001ebcf2f5dd9500b2ebf8ae963770001ae1ecac00000001e825b0300000000044800000005579f32019cc2c0065e4376d3e9e200405e923864a07f0d988ff3cfcda99d6eb11480405eab0829f0eca1e866e59db1aef530f45bb481ea445beda0428f73714a9500008d64444035e5b1aead6000003911a421df4f1b0a4bebe425413181c8ad4cc8ca0e2d30e4c513709929400078e667f20001439f5f996c61acf6f512cc2359f9f708c9842576f437a19402f602f646e0082ae74ec30e84e6e5ba76405a888c00018aa14ca4f129a1052513a60003d71ae468b5f39a1cdcc63c9cae000261a80005406000321a3b24a2a38d81250000089600000df08000f03f469526e00002ad88cb80003ad3097f3b5a888bbf2000000034a5c190532200000005dee0001773400001fb0000c0c3c536e6a000000036d706369d20cd899a280000000e14e874bae1e8b8f2cc000035d2627d50311f8000e5027600f25800010d40003df83bac3a20a68b06a8000563d956f2979d1432fa000390ea069429d4c7f12e000000000000da6c33078b051d80005cdd00002a4dde1fa7000000000d751eb94b58a86800072270ca00002104135e0000ad4ca5f693d0001f73fd62d44f0001c0c54e151cb21d5d2906fa54610000a5010787424f84e0001a40754fa12aa3d00004631c69c8558000266525856154443ca87f99aa76b8440000643c0001939e2970001af459c1b24e249e0003b3c617270e384004f08000fb9800000004ba4084d15b8000015fc35e00021b6ae30697b2d124620b540000a908ec51c1e2272849800000008cfce75084b6bc267a686e8d5de0f17d17853c000000023a26b45ad5000047de00018df00004ade4cda4a2c2d20001b1a000000000bb3a24000000004c160001c9e000000002a21df99091000018740006504e0560f2af657b9262cc000163d0000000000000004251000052baac200000000835c0001b9628360002f1742b4c8e5b305cf28000d54fa8a38a53058c5f734ac0001b7f8796b0361a653ee0000182ae96dc17c8b5ef3fe548559000134561d8553a05c8f2f128ec9d5842200026ce9cde161b720b287800000000003321fa9a075f7ac354aad8646fced680006ae68247058319d44040000ae36ab88000474493175a978bf17820003503742efd84ef63f30838a8464482c00038f2181 else 0x1a7d27272906403a000091b297c309385eb91e00780001187cf2d965c4a8ff3576a71a56f6de8472d0e1379c61c77e8c35e497e1eaa7df08bf534fac31a840007da8000064ed8cec6a50000b1fc21505ab0000c9fc25400002cd66140ede8000296921200003da2bafc0003994eb56135a0000e280000ab25d6c9c26894d46f6a4f80000e84f04b14280004b1d5381ecb534ffd3b0001576c0003b880000000000000000000528ec290ac8000166f25ae736a244cb47e83ad07c9be3e615d4a29330112a73896243469bb1404d50b093f874275d80000000000011b5618aa7a0000a79d4b209d7fd62e482427bc37ad1f5a90599f6838559730e69124b9ec36036957b80c310b4ca18ae3f252e5e231b00005574fa7b26ba29c8000b4d6ab68000415500000002f37fd9462040001a738000b97005dc00010761726405362000000000000158c2907d27513534e9632600016da5898cd26000090a40001148639800000001d4d2c7296243618000a77501de92bfaf51813a8b40006e7579cdaab407be95e021dec94000085195c5d3138f5c5130001067800043c000003ab800)))
def dataBits10 (i : Nat) : Nat := (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0xf1de889de3364540f2de8899a3364540f4de7799a3364540b5ddc72163364540b6ddc62163364540b7cdc22163364540b7d5c12163364540b7d9c02163364540e75cca9563364540f35e889563364540f55e779563364540f65e669563364540c3fccba21a26454087fccba21a26454087fccb61da264540e1fe889dda264540e2fe88999a264540e4fe77999a264540a5fdc7215a264540a6fdc6215a264540a7ddc3215a264540a7edc2215a264540a7f5c1215a264540a7f9c0215a264540c77ccb955a264540e37e88955a264540e57e77955a264540e67e66955a26454087fccb955a26454095fdc7aed5264540c5fdba2dd526454095fccb9dd526454096fecc6d85264540c6feaa6d85264540c6fda86d85264540d2fe886d85264540c6fdb668c5264540d6ddb68cc5264540a7edc82ea2264540a7edc52ea2264540a7edc32ea2264540b5edc72e22264540a7eccb6a22264540e3eccaa222264540e3ecbaa222264540e3eeaaa222264540e3eda8a222264540e5eeaa9de2264540e5eda89de2264540f1ee889de2264540e5ee7769a2264540e6eda899a2264540f2ee8899a2264540f4ee7799a2264540a7eccb6962264540e3ee886962264540e5ee776962264540e6ee666962264540b5edc72162264540b6edc62162264540b7cdc32162264540b7e5c12162264540b7e9c02162264540e76cca9562264540e76cba9562264540e76eaa9562264540e76da89562264540f36e889562264540f56e779562264540e76da69562264540f66e669562264540e76da59562264540a7eccb68e2264540e3ee8868e2264540e5ee7768e2264540e6ee6668e2264540e76e5568e2264540e7ccba8ce2264540f3ce888ce2264540f5ce778ce2264540f6ce668ce2264540f74e558ce226454087fccb6a2226454087fccb696226454087fccb68e2264540e3ee8868a2264540e6ee6668a2264540e76e5568a226454096fdc6aed8164540e3f5a8a221164540e3f68869e1164540e5f5a89de1164540f1f6889de1164540e3f6886961164540e5f6776961164540b5f5c72161164540b6f5c62161164540b7d5c32161164540b7e5c22161164540b7f1c02161164540e775a89561164540f376889561164540f576779561164540e775a59561164540e3f68868e1164540e5f67768e1164540e7765568e1164540f3d6888ce1164540f5d6778ce1164540f756558ce1164540e3f68868a1164540e5f67768a1164540e7765568a1164540b6f5c614a1164540e7e5a888a1164540f3e68888a1164540f5e67788a1164540e7e5a588a1164540f7665588a1164540e7e5a388a1164540f7c63388a1164540e7e5a288a1164540a3bdc4aaa8864d40a5bdc4aaa7764d40a6bdc4aaa6664d40a73dc4aaa5564d40a7adc4aaa2264d40a7b5c4aaa1164d40 else 0xf7c63388a116494087fdc82ea116494087fdc52ea116494087fdc32ea1164940a7f5c1aaa116494087fccb6a21164940c3fcbaa22116494087fccb69e1164940c5fcba9de116494087fccb6961164940c77cba956116494087fccb68e1164940c7dcba8ce1164940c7f4ba6061164940f3b6885061164940f5b6775061164940f736555061164940f7a6225061164940e3f8caa213064940a7f8caa213064940f1fa889dd3064940f2fa889993064940f4fa77999306494097f9cb2153064940b5f9c72153064940b6f9c62153064940b7d9c32153064940b7e9c22153064940b7f1c12153064940f37a889553064940f57a779553064940f67a669553064940b7dacc54d3064940f3da8854d3064940f5da7754d3064940f6da6654d3064940f7598554d3064940f75a5554d3064940f759535493064940f3ea888893064940f6ea668893064940f76a558893064940f7c9538893064940b5f9c72053064940b7d9c32053064940a7f8ca5453064940b7d9c31453064940b7dacc4c53064940f3da884c53064940f5da774c53064940f6da664c53064940b7d9c54c53064940f75a554c53064940f7ca224c53064940f7d1814c53064940f7d1314853064940f3f2888453064940f5f2778453064940f6f2668453064940f772558453064940f7d1538453064940f7e2228453064940f7d1318453064940a3fdc52ea8864540a3fdc32ea8864540a3fdc22ea8864540b2fdc62ca8864540c3fccba21a76454087fccba21a764540e1fccaa227764540e1feaaa227764540e1fda8a227764540e2fe8869e6664540e4fda89de6664540f0fe889de6664540c3fccba21a56454087fccba21a56454087fccb61da564540e1fe889dda564540e2fe88999a564540e4fe77999a564540c5feaa6dc8564540c6feaa6d8856454097decc6cc8564540c7ddca6cc8564540c7deaa6cc856454097eecc6c88564540c7edca6c88564540c7eeaa6c8856454097f6cc6c48564540c7f6aa6c48564540c7faaa6c08564540a77dc82ea5564540a77dc32ea5564540a77dc22ea5564540a77ccb6a25564540e37ccaa225564540e37cbaa225564540e37eaaa225564540e37da8a225564540e57eaa9de5564540e57da89de5564540f17e889de5564540e57e7769a5564540e67da899a5564540f27e8899a5564540f47e7799a556454087fccb6a25564540e37e886965564540e67e666965564540c3fccba21a36454087fccba21a36454087fccb61da364540e1fe889dda364540e2fe88999a364540e4fe77999a364540a5fdc7215a364540a6fdc6215a364540a7ddc3215a364540a7edc2215a364540a7f5c1215a364540a7f9c0215a364540c77ccb955a364540e37e88955a364540e57e77955a364540e67e66955a36454087fccb955a364540e3dccaa223364540) else (if i < 3 then 0xb7e5c12162264940b7e9c02162264940e76cca9562264940e76da89562264940f36e889562264940e76da69562264940f66e669562264940e76da59562264940f3ae885522264940f6ae665522264940f72e555522264940e3ee8868e2264940e6ee6668e2264940e76e5568e2264940f3ce888ce2264940f6ce668ce2264940f74e558ce226494096fdc6aed8164940a7f5c1aa98164940c6fdba2d9816494096fccb999816494095fecc6dc8164940c5feaa6dc8164940c5fdb76948164940d57db79548164940d5bdb75508164940c5fdb768c8164940d5ddb78cc8164940d5edb7888816494087fdc82e9516494087fdc32e95164940c3fcbaa215164940c5fcba9dd5164940c6fcba9995164940c7dcba8cd5164940c7f4ba6055164940e3bccaa214164940a7bccaa214164940f1be889dd4164940f2be889994164940f4be779994164940b5bdc72154164940b6bdc62154164940b79dc32154164940b7adc22154164940b7b5c12154164940b7b9c02154164940d73ccb9554164940f33e889554164940f53e779554164940f63e669554164940f3ae888894164940f6ae668894164940f72e55889416494087fdc82e9316494087fdc52e93164940c3fcbaa213164940c5fcba9dd3164940c77cba9553164940c7f4ba6053164940f7c5324c52164940a7f5c82ea1164940a7f5c52ea1164940a7f5c32ea1164940a7f5c8aaa1164940a7f5c5aaa1164940a7f4cb6a21164940e3f4caa221164940e3f4baa221164940e3f6aaa221164940a7f4caa221164940e3f5a8a221164940a7f4cb69e1164940e3f68869e1164940a7f4ca61e1164940e5f4ba9de1164940e5f6aa9de1164940e5f5a89de1164940f1f6889de1164940e6f6aa99a1164940e6f5a899a1164940f2f68899a1164940e6f5a799a1164940f4f67799a1164940b6f5c62d61164940b7e5c22d61164940a7f4cb6961164940e3f6886961164940e5f6776961164940e6f6666961164940b5f5c72161164940b6f5c62161164940b7d5c32161164940b7e5c22161164940b7f1c02161164940e774ca9561164940e774ba9561164940e776aa9561164940e775a89561164940f376889561164940f576779561164940f676669561164940a7f4ca9561164940e775a59561164940b7b4cb5521164940f3b6885521164940f5b6775521164940f6b6665521164940f736555521164940a7f4cb68e1164940e3f68868e1164940e5f67768e1164940e6f66668e1164940e7765568e1164940a7f4ca54e1164940e7d4ba8ce1164940f3d6888ce1164940f5d6778ce1164940f6d6668ce1164940f756558ce1164940e7e4ba88a1164940e7e5a888a1164940f3e68888a1164940f6e66688a1164940e7e5a588a1164940f7665588a1164940f7a55488a1164940e7e5a388a1164940 else (if i < 4 then 0x87fdc12e98764940c3fcbaa218764940a5fdc8aaa7764940a5fdc5aaa7764940a5fdc1aaa7764940e1fccaa227764940e1feaaa227764940a5fccaa227764940e1fda8a227764940a6fdc8aaa6664940a6fdc5aaa6664940a6fdc1aaa6664940e2feaaa226664940e2fe8869e6664940a6fcca61e6664940e4feaa9de6664940e4fda89de6664940f0fe889de6664940c3fccba21a56494087fccba21a56494087fccb61da564940e1fe889dda564940e2fe88999a564940e4fe77999a564940c5feaa6dc8564940c6feaa6d8856494097decc6cc8564940c7ddca6cc8564940c7deaa6cc8564940d7d9c06cc856494097eecc6c88564940c7eeaa6c8856494097f6cc6c48564940c7f5ca6c48564940c7f6aa6c48564940d7b5c46c48564940c7faaa6c08564940a77dc82ea5564940a77dc32ea5564940a77dc12ea5564940a77dc8aaa5564940a77dc1aaa5564940a77ccb6a25564940e37ccaa225564940e37cbaa225564940e37eaaa225564940a77ccaa225564940e37da8a225564940a77cca61e5564940e57eaa9de5564940e57da89de5564940f17e889de5564940a77ccb69a5564940e57e7769a5564940e67cba99a5564940e67eaa99a5564940e67da899a5564940f27e8899a5564940f47e7799a5564940b57dc72c6556494087fdc82ea556494087fdc32ea556494087fdc12ea5564940a77dc5aaa556494087fccb6a25564940c3fcbaa22556494087fccb69a5564940c6fcba99a5564940e37e886965564940e67e666965564940e3bccaa215464940a7bccaa215464940f1be889dd5464940f2be889995464940f4be779995464940f33e889555464940f63e669555464940c3fccba21a36494087fccba21a36494087fccb61da364940e1fe889dda364940e2fe88999a364940e4fe77999a364940a5fdc7215a364940a6fdc6215a364940a7ddc3215a364940a7edc2215a364940a7f5c1215a364940a7f9c0215a364940c77ccb955a364940e37e88955a364940e57e77955a364940e67e66955a36494087fccb955a36494087fdc82e9636494087fdc52e96364940c3fcbaa216364940c5fcba9dd6364940c77cba955636494087fdc12e95364940c5fcba9dd5364940c6fcba9995364940e3dccaa223364940a7dccaa223364940a7dcca61e3364940f1de889de3364940f2de8899a3364940f4de7799a3364940b5ddc72163364940b6ddc62163364940b7cdc22163364940b7d5c12163364940b7d9c02163364940e75cca9563364940f35e889563364940f55e779563364940f65e669563364940a7dcca956336494095fdc7aed5264940e3eccaa222264940e3eda8a222264940e6eda899a2264940f2ee8899a2264940e3ee886962264940e6ee666962264940b5edc72162264940b6edc62162264940b7cdc32162264940 else 0xb7e5c12162264d40b7e9c02162264d40e76cca9562264d40e76cba9562264d40e76eaa9562264d40e76da89562264d40f36e889562264d40f56e779562264d40e76da69562264d40f66e669562264d40e76da59562264d40a7bdc4aaa2264d4087fccb6a22264d4087fccb69a2264d4087fccb6962264d4096fdc6aed8164d40a7bdc4aa98164d40c6fdba2d98164d4096fccb9998164d40a7bdc4aa88164d4095fecc6dc8164d40c5feaa6dc8164d40c5fdb76948164d40d57db79548164d40d5edb78888164d40a7bdc4aa97164d40a7bdc4aa96164d40a7bdc4aa95164d40a7bdc4aa85164d40a7bdc4aa92164d40a7bdc4aa82164d4093fecc6e02164d40c3fdca6e02164d40c3feaa6e02164d40c3fdb86a02164d40c5feaa6dc2164d40c5fda86dc2164d40d1fe886dc2164d40c6feaa6d82164d40c6fda86d82164d40d2fe886d82164d40977ecc6d42164d40c77dca6d42164d40c77eaa6d42164d40c77da86d42164d40d37e886d42164d40c3fdb86942164d40c5fdb76942164d40c6fdb66942164d40c77db56942164d40d37db89542164d40d57db79542164d40d67db69542164d4097decc6cc2164d40c7deaa6cc2164d40c7dda86cc2164d40d3de886cc2164d40c7dda56cc2164d40d75e556cc2164d40c7faaa6c02164d40c7f9a86c02164d40d3fa886c02164d40c7f9a56c02164d40d77a556c02164d40a7f5c82ea1164d40a7f5c52ea1164d40a7f5c22ea1164d40a7f4cb6a21164d40e3f4caa221164d40e3f4baa221164d40e3f6aaa221164d40e3f5a8a221164d40a7f4cb69e1164d40e3f68869e1164d40e5f4ba9de1164d40e5f6aa9de1164d40e5f5a89de1164d40f1f6889de1164d40e6f6aa99a1164d40e6f5a899a1164d40f2f68899a1164d40e6f5a799a1164d40f4f67799a1164d40b6f5c62d61164d40a7f4cb6961164d40e3f6886961164d40e5f6776961164d40e6f6666961164d40b5f5c72161164d40b6f5c62161164d40b7d5c32161164d40b7e5c22161164d40b7f1c02161164d40e774ca9561164d40e774ba9561164d40e776aa9561164d40e775a89561164d40f376889561164d40f576779561164d40f676669561164d40e775a59561164d40b6f5c614a1164d40e7e4ca88a1164d40e7e4ba88a1164d40e7e6aa88a1164d40e7e5a888a1164d40f3e68888a1164d40f5e67788a1164d40f6e66688a1164d40e7e5a588a1164d40f7665588a1164d40a7bdc4aaa1164d4087fccb6a21164d4087fccb69e1164d4087fccb6961164d40a3fdc52ea8864940a3fdc32ea8864940a3fdc12ea8864940a3fdc5aaa8864940a3fdc1aaa886494087fdc52ea886494087fdc32ea886494087fdc12ea8864940a3fdc8aaa8864940c3fccba21a76494087fccba21a76494087fdc52e9876494087fdc32e98764940))) else (if i < 8 then (if i < 6 then 0xa7eccb6962265940e5ee776962265940e76cca9562265940e76cba9562265940e76eaa9562265940e76da89562265940f36e889562265940f56e779562265940e76da59562265940e6ecba58e2265940f4ee7758e2265940f66e5558e2265940e7ccba8ce2265940f3ce888ce2265940f5ce778ce2265940f74e558ce226594087fccb6a2226594087fccb6962265940f53e779554165940f5ae778894165940f72e558894165940f576779561165940f5d6778ce1165940f756558ce1165940f5e67788a1165940f7665588a1165940f7c63388a1165940a3fdc52ea8864d40a3fdc22ea8864d40a3fdc12ea8864d40b2fdc62ca8864d40a7bdc4aaa8864d40c3fccba21a764d4087fccba21a764d40a7bdc4aa98764d40e1fccaa227764d40e1feaaa227764d40e1fda8a227764d40a7bdc4aa98664d40a7bdc4aa97664d40e2feaaa226664d40e2fe8869e6664d40e4feaa9de6664d40e4fda89de6664d40f0fe889de6664d40c3fccba21a564d4087fccba21a564d4087fccb61da564d40e1fe889dda564d40e2fe88999a564d40e4fe77999a564d40a7bdc4aa98564d40a7bdc4aa88564d40c5feaa6dc8564d40c6feaa6d88564d40c7deaa6cc8564d4097eecc6c88564d40c7edca6c88564d40c7eeaa6c88564d4097f6cc6c48564d40c7f5ca6c48564d40c7f6aa6c48564d40c7faaa6c08564d40a7bdc4aa97564d40a7bdc4aa96564d40a77dc82ea5564d40a77dc22ea5564d40a77dc12ea5564d40a77ccb6a25564d40e37ccaa225564d40e37cbaa225564d40e37eaaa225564d40e37da8a225564d40e57eaa9de5564d40e57da89de5564d40f17e889de5564d40a77ccb69a5564d40e57e7769a5564d40e67cba99a5564d40e67eaa99a5564d40e67da899a5564d40f27e8899a5564d40f47e7799a5564d40b57dc72c65564d40a7bdc4aaa5564d4087fccb6a25564d4087fccb69a5564d40e37e886965564d40e67e666965564d40a7bdc4aa98264d40a7bdc4aa88264d40a7bdc4aa97264d40a7bdc4aa96264d4095fdc7aed5264d40a7bdc4aa95264d40c5fdba2dd5264d4095fccb9dd5264d40a7bdc4aa85264d4096fecc6d85264d40c6feaa6d85264d40c6fda86d85264d40d2fe886d85264d40a7edc82ea2264d40a7edc52ea2264d40a7edc12ea2264d40b5edc72e22264d40a7eccb6a22264d40e3eccaa222264d40e3ecbaa222264d40e3eeaaa222264d40e3eda8a222264d40e5eeaa9de2264d40e5eda89de2264d40f1ee889de2264d40a7eccb69a2264d40e5ee7769a2264d40e6ecba99a2264d40e6eeaa99a2264d40e6eda899a2264d40f2ee8899a2264d40f4ee7799a2264d40a7eccb6962264d40e3ee886962264d40e5ee776962264d40e6ee666962264d40b5edc72162264d40b6edc62162264d40b7cdc32162264d40 else (if i < 7 then 0xc7febb6995264540c7fdb76995264540e5fcb76995264540e77eaa5d55264540e77da85d55264540f57d875d55264540e77da65d55264540d5fcb76cd5264540c7febb68d5264540c7fdb868d5264540c7fdb768d5264540e5fcb768d5264540c7fdb668d5264540e77d7568d526454097fccb5cd526454097fccb58d5264540d77db854d5264540b77dc754d5264540f57cb754d5264540f75d8354d5264540f75d7354d5264540f76cc254d5264540e7eeaa6095264540f5ecb76095264540f3ed876095264540f76cc56095264540f76d756095264540e7eda36095264540f3ed836095264540f76d53609526454097fdcb6095264540e7eeaa5c95264540b7edc85c95264540e7eda85c95264540e7eda65c95264540e7eda35c95264540f5ed735c95264540f76d535c9526454097fecc6cc526454097fdcb60c5264540d3fdb860c5264540d6fdb660c5264540d7ddb360c526454097fdc8aed326454097fdc7aed326454097fdc5aed326454097fecc6e1326454097fccba21326454097fecc6dd326454097fdcb61d326454097fccb61d326454097fecc6d53264540d5fcc76d5326454097fdcb615326454097fdcb2153264540b5fdc72153264540b6fdc62153264540b7ddc32153264540b7edc22153264540b7f5c12153264540b7f9c0215326454097fdcb5d5326454097fccb9553264540f5dd875cd3264540d7ddb55cd3264540f3ed876093264540d7edb56093264540f7cd73609326454097fccba222264540b5fdc72162264540b6fdc62162264540b7ddc32162264540b7edc22162264540b7f9c0216226454097fccb956226454097fccb58e226454097fccb54e2264540f3ed825498164540f3ed824c98164540e5fda861d7164540e5fd876957164540f1fd876157164540e5fd8768d7164540e5fd876897164540f1fd876097164540b5fdc85c97164540f5ed725497164540d5fdb761d5164540f76d825495164540f5f5875c55164540d5fdb761d3164540b5fdc72153164540b6fdc62153164540b7ddc32153164540b7edc22153164540b7f9c02153164540f7cd824c93164540b5fdc72152164540b6fdc62152164540b7ddc32152164540b7edc22152164540b7f9c02152164540f5f5875c52164540a77dc82ea5565940a77dc32ea5565940a77dc22ea5565940a77ccb6a25565940e37cbaa225565940e57eaa9de5565940e57da89de5565940f17e889de556594087fccb6a25565940f47e779556365940f1de889de3365940e75cca9563365940f35e889563365940f55e77956336594095fdc7aed5265940c5fdba2dd526594095fccb9dd5265940a7edc82ea2265940a7edc52ea2265940a7edc32ea2265940a7eccb6a22265940e3ecbaa222265940e5eeaa9de2265940e5eda89de2265940f1ee889de2265940 else 0xd7ddc26cc8564540d7ddc16cc8564540d7eecc6c88564540d7edc36c88564540d7edc16c8856454097fecc6c88564540c7feaa6c8856454097fecc6e17564540c7fcca6e17564540c7feaa6e17564540e5fcca61d7564540e5feaa61d7564540f37d876156564540a7fdc85d9a364540e5fd875d9a364540e3fd87615a364540a7fdc85d5a364540e5fd875d5a364540a7fdc8595a364540a7fdc7595a364540e6fd86595a364540e6fd76595a364540e77d85595a36454097fdc8aed736454097fdc5aed736454097fdc2aed736454097fecc6e17364540c7fcca6e1736454097fccba217364540f1fd87615736454097fdc7aed636454097fdc5aed636454097fdc2aed636454097fccb61d636454097fccb955636454097fdc8aed536454097fdc7aed536454097fdc2aed536454097fecc6e15364540b5fdc72e15364540b6fdc62e15364540b7edc22e15364540b7f5c12e15364540b7f9c02e1536454097fccba21536454097fecc6dd536454097fdcb61d536454097fccb61d5364540d5fdb761d5364540b3fcc86d95364540f37d876155364540f75d8560d5364540b7ddc85cd5364540f5dd875cd5364540f75d855cd5364540b6fdc62c95364540a7fecc61da264540a7fdc85d9a264540e5fd875d9a264540e3fd87615a264540a7fdc85d5a264540e5fd875d5a264540a7fdc8595a264540a7fdc7595a264540e6fd86595a264540e6fd76595a264540e77d85595a26454097fdc7aed826454097fdc5aed826454097fdc3aed8264540c7febbaa98264540e3feaa61d8264540f1fd875d98264540b6fdc62d58264540c7febb6958264540e3fd876958264540f1fd875d5826454097fccb955826454097fccb5cd8264540b3fdc85cd8264540f1fd875cd826454097fccb58d8264540f3dd8358d826454097fccb54d8264540f3dd8354d826454097fdcb54c8264540d77db554c8264540d7ddb354c826454097fecc6e17264540c7feaa6e17264540c7fdb86957264540d5fdb85cd7264540f5dd7354d7264540c7fdb86956264540c7fdb76956264540e6fd766956264540e6fda55956264540c7fdb768d6264540e6fd7668d6264540e6fd6568d6264540e6fd656896264540f3ed876096264540e7eda56096264540f3ed83609626454097fdc8aed5264540d5fdc7aed526454097fdc7aed526454097fdc3aed5264540b5fdc7aed5264540c7febbaa9526454097fecc6e15264540c7fcca6e15264540c7feaa6e15264540d5fcc76e15264540c7febb6a1526454097fccba21526454097fecc6dd5264540c7feaa6dd5264540c7fda86dd5264540d5febb2dd5264540e5feaa2dd5264540d5fdb82dd5264540d5fcb82dd5264540e5fda82dd526454097fdcb61d526454097fccb61d5264540d3fdb861d5264540d5fcb76d95264540)) else (if i < 9 then 0xe5feaa5d97164940e5fda85d97164940c7fdb868d7164940e5fd8768d7164940e5fd7668d7164940c7fda86dd6164940c7fdb869d6164940c7fdb86956164940d7bdb85516164940c7fdb868d6164940c7fdb768d6164940f6bd545896164940e7f5a76056164940e7f5a56056164940f7b5546056164940e7f5a36056164940c7fcbaa215164940c7fcba61d5164940c7fcba6195164940c7fcba5d95164940d77db85955164940f67d865955164940f67d765955164940d7bdb85515164940c7fdb868d5164940c7fcba60d5164940c7fcba5cd5164940c7fcba58d5164940f67d655895164940f73d545495164940f3f5866055164940f775656055164940f7b5546055164940e7f5a36055164940f775655c5516494097fdcb60c5164940d7ddb360c5164940b7becc61d4164940b7bdc85d94164940f5bd875d94164940f3bd876154164940b7bdc85d54164940f5bd875d54164940b7bdc85954164940b7bdc75954164940f6bd865954164940f6bd765954164940f73d855954164940f6bd655894164940f5bd875c54164940c7fcbaa213164940c7fcba61d3164940c7fcba6153164940c7fcba2153164940b5fdc72153164940b6fdc62153164940b7ddc32153164940b7f9c02153164940c7fcba5d53164940c7fcba9553164940d7ddb858d3164940f6dd8658d3164940f3f5866053164940f7d5636053164940b5fdc72152164940b6fdc62152164940b7ddc32152164940b7f9c02152164940d7bebb5512164940d7bdb85512164940d7bdb65512164940d7bdb55512164940f6ed655892164940f7ad545892164940c7fcbaa221164940c7fcba61e1164940c7fcba6161164940c7fcba60e1164940c7fcba54e1164940b7facc61d3064940b7f9c85d93064940f5f9875d93064940b7facc6153064940f3f9876153064940b7f9c85d53064940f5f9875d53064940b7f9c85953064940b7f9c75953064940f6f9865953064940f6f9765953064940f779855953064940f7d98754d3064940f7d98654d3064940f7d97654d3064940f7d98554d3064940f6f9655893064940f7d9535893064940f7d9535493064940b7facc6053064940f6f8c66053064940f3f9866053064940f7d9536053064940b7f9c85c53064940f5f9875c53064940f5f9765c53064940b7f9c85853064940b7f9c75853064940f7f1815853064940b7f9c85453064940f7f1815453064940b7f9c81453064940f7d9874c53064940f7d9864c53064940f7d9764c53064940f7d9854c53064940f7d953485306494097fdc5aed876454097fdc3aed876454097fdc2aed8764540a7fdc52e98764540c7febbaa98764540c7fcba6d58764540a7fecc61da564540a7fdc85d9a564540e5fd875d9a564540e3fcca61d8564540e3feaa61d8564540f1fd875d98564540 else (if i < 10 then 0xc7feaa6e17564940e5feaa61d756494097fecc6e16564940c7fcca6e16564940c7feaa6e16564940a7fcca6e16564940c7feaa6dd6564940a7fcca61d6564940e6feaa6196564940e6feaa5d96564940e77eaa6156564940f37d876156564940f67d766156564940a7fcca6cd6564940b7bdc85955464940f6bd865955464940f73d855955464940a7fdc85d9a364940e5fd875d9a364940e3fd87615a364940a7fdc85d5a364940e5fd875d5a364940a7fdc8595a364940a7fdc7595a364940e6fd86595a364940e6fd76595a364940e77d85595a364940a7fcca6dd8364940a7fcca6d98364940a7fcca9558364940a7fcca6c5836494097fecc6e16364940c7fcca6e16364940a7fcca6e16364940a7fcca6dd6364940c7fcba61d6364940a7fcca6d56364940c7fcba6156364940c7fcba5d56364940a7fcca9556364940c7fcba955636494097fdc8aed536494097fdc6aed536494097fecc6e15364940b5fdc72e15364940b6fdc62e15364940b7edc22e15364940b7f5c12e15364940b7f9c02e1536494097fccba21536494097fccb61d536494097fecc6d95364940c7fcca6d95364940d3fcc86d95364940a7fcca6d95364940b3fcc86d9536494097fdcb6195364940d6fdb66195364940c7fcba5d95364940f37d876155364940d77db66155364940d7ddb660d5364940f75d8560d5364940f75d855cd5364940a7fcca6c5536494097fdc5aed8264940b6fdc62d5826494097fccb9558264940d7bebb551826494097fccb54d8264940f3dd8354d8264940e6feaa5956264940d6fdb85956264940e6fda85956264940e6fda55956264940f67d855956264940d7bebb5516264940d7bdb85516264940f6bd655516264940e6fd6568d6264940f6dd8358d6264940b6fdc654d6264940f6ed656096264940f7ad546096264940d7bdb85515264940d7bdb65515264940f73d655515264940f75d8354d5264940f7ad546095264940f6ed655895264940f7ad545895264940b5fdc72153264940b6fdc62153264940b7ddc32153264940b7f5c12153264940b7f9c0215326494097fecc6e0a164940d3fdb861ca16494097fdcb614a16494097fdc6aed816494097fdc5aed816494097fdc3aed8164940c7febb69d8164940e6fda72d98164940e3feaa6198164940e3fda76198164940c7febb6958164940e6fcb66958164940e3fd866958164940f2fd86595816494097fccb9558164940d7bebb5518164940f6bcb65518164940f3bd865518164940c7febb68d8164940e6fcb668d8164940e3fd8668d8164940f2fd8658d816494097fccb54d8164940f3bd546098164940b7f5c5285816494097fdcb54c8164940d5fdb754c8164940d77db554c8164940d7ddb354c8164940d7bd546c88164940e5feaa61d7164940e5fda861d7164940 else 0x97fdcb61d5164d40d5fdb761d5164d4097fdcb6195164d4097fdcb5d95164d40d77db85955164d40f67d865955164d40f67d765955164d4097fdcb2095164d40b77dc52095164d40b7f5c12095164d40d6fdb65895164d40f67d655895164d40e77eaa5495164d40e77da85495164d40f57cc75495164d40d77db75495164d40b77dc65495164d40f76d825495164d40f76d725495164d40e7f6aa6055164d40f6f4c66055164d40d7f5b66055164d40f3f5866055164d40f775656055164d40f3f5826055164d40f775526055164d4097fdcb6055164d40b7f5c85c55164d40f5f5875c55164d40f5f5765c55164d40f775655c55164d40f5f5725c55164d40f775525c55164d4097fecc6c85164d40c7feaa6c85164d40c7fda86c85164d4097fdcb6085164d40d3fdb86085164d40d7edb26085164d4097fdc8aed2164d4097fdc7aed2164d4097fdc6aed2164d4097fdc5aed2164d40c7febbaa92164d4097fecc6e12164d40c7fcca6e12164d40c7feaa6e12164d40d6fcc66e12164d40c7febb6a12164d4097fccba212164d4097fecc6dd2164d40c7feaa6dd2164d40c7fda86dd2164d4097fdcb61d2164d4097fecc6d92164d40c7feaa6d92164d40c7fda86d92164d4097fdcb6192164d4097fdcb5d92164d4097fecc6d52164d40c7fcca6d52164d40c7feaa6d52164d40c7fda86d52164d40d5fcc76d52164d40c7febb6952164d40c7fdb86952164d40c7fdb76952164d40c7fdb66952164d4097fdcb6152164d4097fdcb2152164d40b5fdc72152164d40b6fdc62152164d40b7ddc32152164d40b7edc22152164d40b7f5c12152164d40b7f9c02152164d4097fdcb5d52164d4097fdcb5952164d4097fccb9552164d40e7eeaa5892164d40d7edb85892164d40e7eda85892164d40f6ed765892164d40e7eda55892164d40f6ed655892164d4097fdcb6052164d40e7f6aa5c52164d40e7f5a85c52164d40f5f5875c52164d40f5f5765c52164d40d7f5b55c52164d40e7f5a55c52164d40f7e5625c52164d4097fdcb5452164d40d3fdc56e02164d40d77dc86d42164d4097fdcb6142164d40d3fdb86142164d40d5fdb76142164d40d6fdb66142164d40d77db56142164d40d7dd856cc2164d40d7f9856c02164d4097fccba221164d4097fccb54a1164d4097fccb88a1164d40a7fdc1aaa886494097fdc6aed876494097fdc3aed8764940a7fdc12e98764940c7febbaa98764940a7fdc5aa98764940a7fdc1aa98764940a7fdc1aa98664940a7fdc5aa97664940a7fdc1aa97664940c7feaa6e17664940e5feaa61d766494097fdcb618a564940d6fdb6618a564940a7fdc1aa98564940a7fcca6dd8564940e3feaa61d8564940a7fcca61d8564940a7fcca6d98564940a7fcca6c58564940d7ddc26cc8564940d7ddc16cc8564940)))) else (if i < 16 then (if i < 13 then (if i < 12 then 0xc7fcca6e15264d40c7feaa6e15264d40d5fcc76e15264d40c7febb6a15264d4097fccba215264d4097fecc6dd5264d40c7feaa6dd5264d40c7fda86dd5264d40d5febb2dd5264d40e5feaa2dd5264d40d5fdb82dd5264d40e5fda82dd5264d4097fdcb61d5264d40d3fdb861d5264d4097fecc6d95264d40c7fcca6d95264d40c7feaa6d95264d40c7fda86d95264d40d5fcc76d95264d40d5fcb76d95264d40c7febb6995264d40c7fdb76995264d40e5fcb76995264d4097fdcb6195264d4097fdcb5d95264d40d6fdb65d95264d40e77eaa5d55264d40e77da85d55264d40f57d875d55264d40e77da65d55264d40e7eeaa6095264d40f5ecb76095264d40f3ed876095264d40d7edb66095264d40f76d756095264d4097fdcb6095264d40e7eeaa5c95264d40b7edc85c95264d40e7eda85c95264d40e7eda65c95264d40d5fcb76c55264d4097fccb9562264d4097fdc7aed8164d40d6fdc6aed8164d4097fdc6aed8164d4097fdc5aed8164d4097fdc2aed8164d40b6fdc6aed8164d40c7febbaa98164d40c7febb69d8164d40d6febb2d98164d40e6feaa2d98164d40d6fdb72d98164d40e6fda72d98164d40e3feaa6198164d40e3fda76198164d40d6fcb66d58164d40c7febb6958164d40e6fcb66958164d40e3fd866958164d40f2fd865958164d4097fccb9558164d40d6fcb66c98164d40e3feaa6098164d40f2fcb66098164d40e3fda56098164d40b3fdc85898164d40f3ed825898164d4097fccb5498164d40f3ed825498164d4097fdcb1498164d40b3fdc81498164d40b6fdc61498164d40b7f5c11498164d4097fccb8898164d4097fdcb5488164d40d5fdb75488164d40d77db55488164d40d7edb25488164d4097fecc6e17164d40c7fcca6e17164d40c7feaa6e17164d40d6fcc66e17164d40e5fcca61d7164d40e5feaa61d7164d40e5fda861d7164d40e5feaa5d97164d40b5fdc85d97164d40d5fdb85d97164d40e5fda85d97164d40c7fdb86957164d40e5fd876957164d40e5fd766957164d40f1fd876157164d40f4fd765957164d40d3fdb86097164d40f1fd876097164d40e5feaa5c97164d40b5fdc85c97164d40e5fda85c97164d40e5fda55c97164d40b5fdc75897164d40f4fd765897164d40f5ed725497164d4097fecc6e16164d40c7feaa6e16164d4097fecc6dd6164d40c7feaa6dd6164d40c7fda86dd6164d40c7fdb869d6164d4097fdcb61d6164d40d5fdb761d6164d40c7fdb86956164d40c7fdb76956164d40e6feaa5896164d40e6fda85896164d40d6fdb75896164d40e6fda55896164d40f6ed825896164d40e7f6aa6056164d40e7f5a76056164d40e7f5a56056164d40f3f5826056164d40f6f5626056164d4097fecc6e15164d40c7fcca6e15164d40c7feaa6e15164d40d6fcc66e15164d40 else 0xf5ed735c95265940f6ed635c95265940f76d535c95265940d5fcb76c5526594097fecc6cc5265940d6fdc66cc526594097fdcb60c5265940d3fdb860c5265940d7ddb360c526594097fdc8aed326594097fdc7aed326594097fdc5aed326594097fdc1aed326594097fecc6e1326594097fecc6dd326594097fdcb61d326594097fccb61d326594097fecc6d53265940d5fcc76d5326594097fdcb615326594097fdcb5d5326594097fccb9553265940f5dd875cd3265940d7ddb55cd3265940f3ed876093265940d7edb56093265940f7cd73609326594097fccb956226594097fccb54e2265940f5ed725497165940f57cc75495165940d77db75495165940f76d725495165940f5f5725c55165940f775525c55165940b7becc5494165940b7bdc75494165940f5bcc75494165940f73d755494165940f7ad72549416594097fecc6dd3165940d7ecc26dd3165940b7ecc26dd316594097fecc6d5316594097fdcb5d53165940d5fdb75c93165940d77db5549316594097fdcb1493165940b7ddc31493165940b7f5c11493165940d7ddb74c9316594097fecc6d52165940d5fcc76d5216594097fdcb5d5216594097fecc6cd216594097fdcb5cd216594097fdcb54d2165940d7f5b55c52165940b7f5c74c52165940f7d5324c52165940a7fdc52e98764d40a7fdc12e98764d40c7fcba6d98764d40c7fcba6d58764d40c7fcba6c58764d4097fecc6e17664d40c7fcca6e17664d40c7feaa6e17664d40e5fcca61d7664d40e5feaa61d7664d40a7fdc85d9a564d40e5fd875d9a564d40e3fcca61d8564d40e3feaa61d8564d40f1fd875d98564d40d7edc16c88564d40d7f5c26c48564d4097fecc6e17564d40c7fcca6e17564d40c7feaa6e17564d40e5fcca61d7564d40e5feaa61d7564d4097fecc6e16564d40c7fcca6e16564d40c7feaa6e16564d4097fecc6dd6564d40c7feaa6dd6564d4097fdcb61d6564d40d5fdb761d6564d40e6feaa6196564d40e6feaa5d96564d40b6fdc85d96564d40f4fd875d96564d40e77eaa6156564d40f37d876156564d40f67d766156564d40f1fd875d98264d40f1fd875d58264d4097fecc6c48264d40c7feaa6c48264d40c7fda56c48264d4097fecc6dd6264d40c7feaa6dd6264d40c7fda86dd6264d4097fdcb61d6264d40e6feaa5d96264d40e6fda85d96264d40f4fd875d96264d40c7fdb76956264d40e6fd766956264d40e6feaa5956264d40d6fdb85956264d40e6fda85956264d40b6fdc75956264d40d6fdb75956264d40e6fda55956264d40f67d855956264d40f3ed876096264d40f6ed766096264d40f6ed656096264d4097fdc8aed5264d40d5fdc7aed5264d4097fdc7aed5264d4097fdc6aed5264d4097fdc1aed5264d40b5fdc7aed5264d40c7febbaa95264d4097fecc6e15264d40) else (if i < 14 then 0x95f094209310920091b09160911090008fb08ea08e508e008cf08ca08c508a808a3089e088d0870083b08360831082c080f07f207d507b8078f076607550750074b074607290724071f071a0715070406f306e206c506a806a3069e069906940683066606250620061b061605ed05c4059b057205490520050f050a0505050004e304ba049d04980487046a044d043c041f040e03f103e003cf03be03ad03a803a3039e038d038803770372036d035c035703520341033c033703320321031002ff02e202c502c002bb02b602a502a0029b02960291028c027b02760271026c02670262025d02580253024e0231021401f701f201ed01e801cb01ba01b501a4019f019a019501840173016201510140012f012a01250120011b01160111010c0107010200fd00f800f300e200d100cc00c700c200bd00b800b300ae009100740057003a001d000097fdc5aed876594097fdc3aed876594097fdc2aed8765940a7fdc52e98765940c7fcba6d58765940e3fcca61d856594097fecc6e17565940c7fcca6e17565940e5fcca61d756594097fdc8aed736594097fdc5aed736594097fdc2aed736594097fdc1aed736594097fecc6e17365940c7fcca6e17365940f1fd87615736594097fdc8aed536594097fdc7aed536594097fdc2aed536594097fdc1aed536594097fecc6e1536594097fecc6dd536594097fdcb61d536594097fccb61d5365940d5fdb761d5365940f37d876155365940b7ddc85cd5365940f5dd875cd5365940f75d855cd536594097fdc7aed826594097fdc5aed826594097fdc3aed8265940f1fd875d5826594097fccb955826594097fccb5cd8265940b3fdc85cd8265940f1fd875cd826594097fccb54d8265940f3dd8354d826594097fecc6e17265940d5fdb85cd7265940f5dd7354d726594097fdc8aed5265940d5fdc7aed526594097fdc7aed526594097fdc3aed526594097fdc1aed5265940b5fdc7aed5265940c7febbaa9526594097fecc6e15265940c7fcca6e15265940d5fcc76e15265940c7febb6a1526594097fecc6dd5265940c7feaa6dd5265940c7fda86dd5265940d5febb2dd5265940e5feaa2dd5265940d5fdb82dd5265940e5fda82dd526594097fdcb61d526594097fccb61d5265940d3fdb861d5265940e77eaa5d55265940e77da85d55265940f57d875d55265940d5fcb76cd526594097fccb5cd5265940d6febb58d5265940d6fdb758d5265940f4fcb758d5265940f67d7558d5265940d77db854d5265940b77dc754d5265940f57cb754d5265940f75d8354d5265940f75d7354d5265940f76cc254d5265940f5ecb76095265940f3ed876095265940f76cc56095265940f76d756095265940f3ed836095265940f76d536095265940e7eeaa5c95265940b7edc85c95265940e7eda85c95265940 else (if i < 15 then 0x3153312a30f530d830d3309e308d30703053304230313020300f2ffe2fed2fe82fe32fde2fd92fd42fcf2fca2fb92fb42faf2faa2fa52fa02f9b2f8a2f852f802f7b2f6a2f592f3c2f2b2f0e2f092f042eff2efa2ef52ef02eeb2ee62ee12eb82e9b2e7e2e612e382e032de62de12dac2d9b2d7e2d612d502d3f2d162ced2cb82c832c722c3d2c2c2c0f2bf22bd52bb82b9b2b8a2b6d2b502b3f2b2e2b112af42ad72ac62aa92a8c2a6f2a462a352a242a132a0229e529c829ab298e297129542937291a28f128d428c328b228a12890288b28862881287c286b28662861285c28572852284d28482843283e2839282828172812280d280827f727e627c927b8279b27962791278c27872782277d277827732762275d27582753274e27492744273f273a2735270c26ef26d226b526a426932682267126602643262625fd25ec25db25be25952578254f253e252d251c250b2506250124f024df24ce24bd24ac24a724a22491248c247b247624652448240723f623e523d4239323522341232422e322c622b52280226f22462229220c21cb21ba219d218c217b216a21592154214f214a2139212821172112210120fc20eb20da20d520d020bf20ba20b520a42087205e2035202420071ff61fd91fc81fb71fa61f951f6c1f5b1f4a1f391f281f171f061ee91ea81ea31e9e1e991e7c1e5f1e361e0d1df01dc71db61db11dac1da71d8a1d611d2c1d0f1cf21cd51cac1c9b1c8a1c851c741c631c5e1c591c541c431c321c151c041be71be21bdd1bd81bd31bc21b991b941b831b721b6d1b5c1b4b1b3a1b291b181b071aea1ae51ad41acf1abe1ab91aa81a971a861a751a701a6b1a661a611a5c1a571a2e1a0519e819d719c6199119681957193a191d190c18fb18d218b51898187b185e18411818180717de17cd17bc17ab178e17711748172b170e16e516d416c316b216a11690167f166e1645161c15ff15e215c51590156715561539151c150b14fa14e914e414df14da14c914b814a714a21491148c148714761471146c145b14561451144c143b141e140d13fc13eb13da13c913b813a7138a136d13681363135e134d13481343133e132d131c130b12fa12e912d812c712b612b112ac12a712a21291128c12871282127d127812731262125d1258124712421231122c122711fe11d511ac119b117e116d1150113f1122111110f410e310c610b510a4109310821071105410431032102110040fe70fca0fad0f900f730f620f510f400f170eee0ec50e9c0e730e560e2d0e1c0e0b0dfa0dd10db40da30d6e0d510d340d170cfa0cdd0cc00ca30c860c690c4c0c3b0c2a0c190c080bdf0bce0bbd0bac0b9b0b8a0b790b680b4b0b460b410b300b2b0b1a0b150b040ae70aa60aa10a9c0a970a7a0a5d0a4c0a2f0a120a0109d809bb09aa098d0970 else 0x60af60866069604c602f60125ff55fd85fbb5f9e5f815f645f475f2a5f0d5ee45ec75eb65e995e885e775e5a5e3d5e205e035de65dc95dac5d9b5d7e5d555d2c5d0f5cf25cd55cac5c9b5c7e5c615c445c335c0a5bed5bd05bbf5ba25b855b685b4b5b2e5b115af45ad75aa25a795a505a3f5a3a5a295a0c59ef59c6599d5974596359465941593c591f590258f158d458b758a658955878585b584a582d581c580b57ee57d157b45797577a5751572856ff56ca56ad569056735656562d560455db55b255a155845567554a552d551054ff54e254d154b45497547a545d54405423540653e953d853c753aa5399537c536b534e533d532c530f52f252d552b8529b527e52615244521b51f251e151d051b3517e5161514451275116510550e850bf50a250915080506f505e504d503050134ff64fd94fbc4f9f4f9a4f7d4f6c4f5b4f4a4f394f1c4eff4ee24ec54ea84e8b4e6e4e514e344e2f4e124e014df04dd34db64da54d944d774d664d494d2c4d0f4cf24cd54cb84c9b4c7e4c614c5c4c3f4c2e4c114bf44bd74bba4b9d4b804b634b464b294b0c4aef4ad24ab54a984a7b4a5e4a414a244a1349f649f149ec49db49d649d149b4499749864969494c493b491e490d48f048d348b64899487c485f48424825481447f747da47bd47ac47a7478a476d475c4757472e471146e846e346c646b546a44687466a464d463c4637461a45fd45ec45cf45b245a145844567455645454534451744fa44dd44c04497447a445d4458443b442a440d43f043d343b64399437c435f43424325430842eb42ce42bd42a04283426642494238420f41fe41ed41d041b341964179415c413f4122410540e840d740c640a940a4409f408e407d4060405b405640514034402f402a400d3ffc3feb3fce3fbd3fa03f8f3f8a3f6d3f503f3f3f223f113ef43ed73eba3e9d3e803e633e463e293e0c3def3dd23db53d983d7b3d5e3d413d243d073cea3ccd3cbc3cab3ca63c953c903c733c563c393c1c3bff3be23bc53ba83b8b3b7a3b693b4c3b3b3b2a3b193afc3aeb3ada3ac93ab83aa73a8a3a6d3a503a333a1639f939dc39cb39ae399139743957393a391d390c38ef38de38cd38c838c338be38b9389c388b38863881387c3877384e38253820380337f237e137d037cb37c637c137bc37ab37a637a1379c37973792378d37883783377237613750374b37463741373c371336ea36d936c836b736b236ad36a836a3369e36993688367736663655362c361b35fe35d535d035cb35c6359d3574356f356a35653560355b354a352d34ec34e734e234dd34c0348b346e345134343423340633e933d833bb339e33813358332f331e330d32fc32eb32e632e132dc32d732d232cd32c832b732b232ad32a832a3329e329932883253323632193214320f31da31a5317c))) else (if i < 19 then (if i < 17 then 0x908f907290559038901b8ffe8fe18fc48fa78f8a8f6d8f5c8f4b8f2e8f1d8f008ecb8eba8ea98e988e7b8e6a8e598e3c8e378e328e218e108e0b8e068e018df08deb8dda8dc98dac8d9b8d7e8d798d5c8d3f8d2e8d118cf48ce38cc68ca98c8c8c6f8c528c358c188bfb8bde8bc18ba48b878b6a8b598b488b438b328b2d8b108af38ad68ac58ab48aaf8a9e8a998a888a778a668a498a2c8a0f89f289c989ac8983896689558938890f88e688c988ac888f887288558838881b87fe87e187c487a7878a87858780876f8752874d8730871f870e86fd86ec86db86ca86b9869c867f8662865d8640862f861e860185fc85df85c285a585888577856685558544853f852e852985248513850e84f184c884ab848e8471845484378426840983f883db83ca83b983a8838b837a8369834c833b833683318320830382e682c982ac828f82668249822c8227820a81f981dc81bf81a281858168814b812e811180f480d780c680a980a48087807680658048802b800e7ff17fd47fb77fa67f957f787f677f567f457f347f2f7f1e7f197efc7eeb7eda7ebd7eac7e8f7e727e557e387e1b7dfe7de17db87d9b7d7e7d617d447d277d0a7cf97ce87ccb7cae7c917c747c637c467c297c187c077bea7bd97bd47bb77bb27b957b847b677b567b397b1c7aff7aee7add7ac07abb7a9e7a8d7a7c7a6b7a4e7a3d7a2c7a1b7a0a79f979e879cb79ba79a979987987797679657954793779267921791078f378d678b9789c787f786278457834781777fa77e977cc77bb77aa77a5779477837766776177507733772e7711770076e376d276b5769876877682767d7660764f763e762d761c760b75ee75dd75cc75bb75b675b175a0758f757e75797574756f756a754d753c752b751a75157510750b74ee74c574a8748b747a7469744c742f741273f573cc73af73aa738d737c735f73427325730872eb72ce72b172947277725a723d7220720f71f271e171c471a771967179715c7133711670f970dc70b3709670797050703370166ff96fe86fd76fba6fb56fa46f936f766f656f546f436f3e6f2d6f106f0b6eee6ed16eb46e976e7a6e5d6e406e236dfa6dd16db46d976d7a6d5d6d406d236d066ce96ccc6caf6c926c756c586c3b6c1e6c016bf06bd36bb66b996b7c6b5f6b426b256b146af76ada6abd6ab86a9b6a7e6a616a446a336a226a1169f469e369d269c169a46987696a694d6930691368f668d968bc68ab689a6889686c684f6832681567f867f367d667b96790677367566739671c66ff66e266c566a8667f6656662d660465db65be6589656c655b653e651564ec64cf64b264956478645b643e642163f863c363a663956378636763326315630462f362ca62ad629c628b627a625d624c621761ee61c561a8618b616e61516134611760fa60e960cc else (if i < 18 then 0xe80b403e3b000d80041a001d0008000d000e800486b4005a001229500100000680071a82bc0fc6060e0b0704148a1a450e80074003a001d00080f280080c1c10301040c8a1a290d14848a42000000003201b80f8f6d80640f46c1c0fa201f0b800677c15c0fc09480be09607e3b000806511881ec11056001b00081682f0398c09c1a448336002419b00120cd8009066c0040c607203e3d180a1083880f8f00838041c020e016118b00b08c44638040683c02c2312016118b0088070847a301c020e010700838041c020e01040680541f4601c0bc0e43421b001210d8009086c0040d684207c03e42210150521cc10491660853040042d000e8005608200034002c1c1582083400200307040060e08000982090d4c109608348a12490d22874003a001d00090d680088a540040001838200034002c8a15820d14868a4345212290ac1040000340020000000307040064508003020001b02c0128c17c178094600404e0683d00080280f8ac00200a03e2b00080280f8ac00200a03e2b000ddb0018a008300418020c0107c6028420d22c0e0e0707038203c0682c0e034160701a090380d0581c0682c0e034160707038381c182180e5001c10c072800e086039400704301ca00380e8210691c07280090381a40a0781c1c0e0e070508503a400781c0682034083210c80b01a110380d05042a0028215001410a800a08540050420d228215001410a800a08407c48460502c0e0e0707038381c142140e9001e07064003e30100f0803846183e3010710731000c6c1021b841e301064072101b801ceaf0d03d9400030e01a098700d04e001055079130e01a09c0020be0aa07e361c03413800487007c44380682f18090c0078801c3e3010000c6c1031b040023708000540682003c6020c6048203702a07b02420000055079102a83c881541e440aa0f2205f05503d182f82c0218fc60200000ac090400001a001d000e800486b4004438a00200000f180838839880dc0a800f8681eca000017c16810c60bf89c086305f05a043182f82a81f8f114188110788a0c40863f180800002a034102903d02d0d9d0148407000b0e00f880f01f04e0010550791580048da618530c19860cc305618200018d820636080046e1001618200034003a001d00090d68008871400400018d82000000586080000000000001c07c400e03e200701f10000c1c03d131b040c6c10001a001d000e8007400205a16360800000000000000680058d820000000034008405a004202d0021016801080b4008405a004202951e950194e494c794c294b19494948f947e946194449427940a93ed93e893d793ba939d9380936393469329930c92e392d292cd92bc92b792b292959278925b92569239921091ff91fa91d191cc91af919e9199917c915f91429125910890df90c290a590a0 else 0x530c11c508077c20007001160e6030b073018583980c2007406120e0178801c004400e002200700110050402831040ba248209d485208208a9042986084104130205a100a0ad4e0d08091618583381c2c19c0e12070158b0670384002062200a0e0ce030b067018583380c240602b10008178a61b0185e30121800f100387c602000000540682c0e0800000358290180d97d8081486098600614c3066182b0c100000586080000000002c306838341c10000002a5c802818322e40140f00838041c02080000001e3010070801846183baa8820d23f180832034880400041ec600000400041e46020421bba300000078c041901a4406e007c353aa0f6500004200e22dd5010079034231101a098880d044440682700083d822098880d04e001055079131101a088880d0402001e0ae301000f0441f8c0401c20061f180800000000f180800000003041dc5c8e079034201501a080a80d040000800083d83c937d01c772005c80200020f63010001079182903d0180f7d371405c8408ce80a4206e400803c80b91c00202804e2048044138006618330c10030cc3056182000000001618200000002c304000680074002435a002d00091028008000000000000f608602e3014028100a014080500a040140c00fa3dd5db6017210230303e8800ae02008802e470008028120812c1e456001b00080800782b8c04003c110602001e0ae0884071dd5db8017200b840401ec11005c8e0010480441002812080241f4400a0482048044138004014090409008827000b800412c1e4400a048204804413800412c1e440960f2204b079152f8240220ec0036001b000b800401409040900882802700102583c8a009c004002048204804414011800997c1200ec700460029820cc1066082b0410000058208000000000001304158208000d000e800486b4005a0012205001000000000068004000000000000f608602e300501f100280f8801407c5e30100f0801874003a00106c0721013834881540f807c7a001f180838839880381781c8604e0d2204202101f1d80074003a001d000801a00160e0e80074003a0010034002060e083c6020c80e420370190030d907b2c24871142892104762161a9f40342b24b10b0d4fa01a15c0020f6088264961a00f9f4034281881a09c0033be4920860504700082fb270218d86407c405ac46204662121a9f40342f8c0486003c40061d000e8007c60200034002c1c1d0008183820f180d01040060e0800304106b034100c01381a0c0d819416c7a00102a0341580040a80d056001a450d2287460241c0e28463c290e14870a4305218290f8c0418c09c406e05400683204e500000f6088207b044102f82a8220c17c1540fc60f6088205f0550441f8c04000015813881280f81cc603c01c0bc0e4440eb0012075800903ac0040)) else (if i < 20 then 0x96c1d30439820b074c10809c0ec4096b042582082f3070008c1d800440ec098200d08138008809c004401930420389b614db02f0a6d8034407136c207102d103220c823816900dc079064606e03c83231b60803642b6c01a202703b100f20c8320c07906411c603c83206e398208064c108001a900d1016cd488364203c002226218216010700838047ba23a9c02160104ea700858041c0209d4e0108ea7008476d8042c0202e10c14010817d084044684202208e302a4210111a1080f90c80b100bb084405d842242102e1610834880a9084044605284203c31b682141e181f41080b0c0f8207c8422c19c02160ce010b067008400205a200c0adb006080302b8a018201e04110064c10801400c400a0f6200500310028018801400c581c1c0e0e071ee8b038275381c2c0e09d4e070b038381c13a9c0e11d4e0708edb038504301c282180e1410c070a086038581c50c242101340e1a10a075640f038203e1c0e38215db21080fa0710edb038581c7042c0e382160707038276d81c23b601ec0e19d480f8b038304218210c1086084284281c2001059100e000880700044452432201c00110011c004400213dd0ce2866a421ee3ba261c00f130d0078986401c4c3800e261a0071003800880ac01c40380022000e0008a754335210f7c36101200088f742752102400111d484090004404800220743a9102e9d488eda0d84038002201c001100080a0803c0044001c00111d48407000440380022014001103881f080040f84038002201c001100a0008803c00440638422031c211018e108800c0c44002062201c00110078008807000440380e221df0c1883c88001a908000620142047001100084174f74488a7522001082a9d48800420fa00220743a9102e9d488eda0d84038002201c001100080988070004530c10f71dd10308158801c0044b0c1000e00088090028430c100ef81f0108c3de8d840381ee0423000e00088618230c10070011003800881ec004431c1003c000881780044b0c103c9861012000896182078b0c2186042107b866d821ee101c00110178038814811c402600221c502f007180e0008801c004400070461003840040fc403800220070011003800881600fc4c3200e2619007130e00389870158407e05e201c001100e02b08714343800e20070011020800880bc01c530c10556369861cc306618343800e2007001101202308090004400e05e202404612c3403080701304038002218e08c3040bec80400018866a4205f352200000c33522000070118535211a90cd4a210a6a4209135229a908003c004403800221860d0e005086182038002201c001100e0008801c00440240022007001100e00088048004400e002205a007100e0230807000458338242c19c121209015890480ac40060b4200105a100e00088048004 else (if i < 21 then 0x10018008800c18040e8b04258208110008a88800c530419820830cc108608200220011000880ec43041c2204310c30401c004404408c2a2205710c10460820060022000181d8800c204819820825cc10a608230411b60cc1040ec2b04105d58211d4840b8230c19860cc1046083304104898210c1040752100300110018008800c0044006002205e001103b0008808800443be1076001102f0008a608207130421860cc104136c19b6092fcdb08036c100300110000c0ec4006102203b101704088004404400221b60800044002218208c304618330419820816cc10a618230c118208013521043082184000000880ec435215a90817040000038008805c01c0046012002202200110c10460820440022022001101100088088004402e012002300300110000c0ec4006100300110048008800c0044006002204b001101101d8800c0044006002203c0011011000880880044006002203008018230811820600062003001101d8412c004407800221c502203b18110008b0670245833812221a00fc091a04815890240ac44418120023022001101102308024004530411b6091b4c10813041982081101d8a618330c1986080714248b30c20011023098880144c4400a202200115110028a888014544400a2a220051111002c010c88a0080046006002200300110018008800c014403c0022001064110110c88078004408e0562005047101e802880ac078400600a201e001120f4ee88078004403c1005003101510c889266a4448b38a202a219110c9010803c0c4405c101e00114d4a0f080780044001e001101510c88078004403c06e29a90cd4866d821b2c8a20d90910860a4235305223b6029101380088174f74488a7522027001102a9d48809c004404e00223a909d484ed8243201e221900f100f00788864808401e0022010c83108864138403c81c08e32190311037015080a8168403c06e203101e100f00088078004401e0022069031c211834818e108c1a70840c460d2063842302bc21031180f000883270841680ac801e002240e0807e07081a508486460d3063842301e00110efe07080780dc41b289c203fc0e14310218818a08441b309d0423069421219011200f0008b868203c002206c083480c8188099088404c403c11a908213074430e218174436c1a290d14848a5218404e141ec190130bc21efd0700f0cf7c07a868736cc5225c582912e2c14880a5774483c02624291a9160d00f086a4383381c2c19c0e1007a0700f0f06703840020622003001120f00f08078004406e03e201e001100080f8800c00440060c0203d98214c12010800413040c0007096358284b102084078004401a100d0d14ac10800c00440060c0258280212c101f080c41c44019304221e080f017080b81ba884605d41c042301102510064c10907a60840 else 0x82c88104004408200222292191027142054002204ea841040044082002201400110208008803c004403a90800831881040044028002204103b10078008803c0044082002203107502b18ef8403521000104004408200220010131000a8004408230c04231860800c41d40846000700110c7040082002202f00710290238804c004400201621c502f00718178008801c0044000708038008801c004400e0022058001130c8038986401c4c8200e200702f1020800880bc158438a1986082acc30a618348200e203702f186046250706838341c1a0e58610c704618205f64020000c43352100004ea104d4846a4335285229a90cd4b0708006000e200f03b10090410400444ea30c2075082081d881040044082002200100b10038008801c0044082002201200110038008816801c408208c204100110090008a618238a100ef84000e002200700111d4e010a618230c104208418041c020e0104e1b0084753804200300116208238b0e70860446006002204118600118c360108618202a0022421c020391a1c8048108c61b0084006002203000310208008800c0044082002204104610e28208a024618401280e2229219110c9010800bb6081100088004400229dd0cee8400427ba19c50cd4847742c4400e2622003101100088004400229d50cd48408800440022001101100088088004404400221df0cd4866a42352104db04001dd08000c004402e006002300900110038008801c00440bc002202200114c30417661843ba105e00112c3066182352104298610c3046a4207930c21b608007be102200110178038814811c4044002200b00110e28178038c088004400e002200038230801c200e002202200110038008801c00440b00022619007130c8038988801c400e05e202200110e28401c0044000704610230401c344400e2007001102c000880bc01c404408c202200110e28661820ab30c29860cc3066a433521002184004408c29a908d4866a50a453521a2200710038008808800440c0006203d03710110008802800440c036c006302200110018008986400c4c32006262200310300018a60833041a22003)))))
def lev10 : Packing := (1751,5,7,0,0,16,0,dataBits10)
def idxBits11 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xd306925720816f2d4000000003a9369b556b835a1020000618b382bf030d3132fc080aaf00001df18000c24e0458000296036740001a408ce882d44b6800045e03b7e000021334fd468904f4000403f0001ba7514e43672d60000380356e10000a07422b6e82a7a6290849c357577ce00022f3000016d2f627df122d79b76c2700003f8800000000a218db80001a3f6441690d00017a33134df8e17e39d35fb6b467a6b200000003a9a33460000000199d58423bce00801ad91ff3d42e34fa117c9c00008db5ad249c222e9b016991d84541680002e1383edb9eaf8d167958f20001f06f6fd1355298d1cc19b09f04000000062662dd5e537e864629bc000001201c0972ae0000008f39c17b3c0000ce816fce8c371eb782ef2f2bac84d12dbf29953e2865885a0d6b0000538daa8fda8e5df5a7b123ed0b0000035a65a227489bf01ac65f9320a56a0001d37b597a74081540000302dc8c000268e08209c44606272e0000bc9e562a1e7327196c864a1657c0fe0001e995fbacbb5c6c784ca7348000e9eb1a5fe255a95f91751d8e67431f000163ac0001cabf12850f297c11a8f1c73d526a6531d03ade4fd3a18e890b58fcdb7923bc4519f9bdc52b5272ea9275a543700006781336fb5cf341425cea2217bb6275010516fceb80003bda0001b10cc080000a494441f946f07b2180f9ae5d0b80f8c2169a3dc766da000121779fd0000b33444c73710001a664000000062560000773938b010f001510071f06670d01300240100c5f021a0004640005170511031640490a07052a04020e09116f0015311d000b0c260104050a010b4a080123010500010121020f001c000e000001030104051f26c51e8c3d4323000103021e0c00080318004f000a022200630f060f910c280320197c045a060965042d082300033908101d660502000a07021b0102070d1b1a04090a020c06000e0017010004060303042800024e022d3849110f320002041d0005001019080100212600005802520300010718040d060a051f03042603020601071e021d22014f0f19440122020005011c001204105d01010b01040101000301263c01023731080008030f31010f0c16061700081101020e010b050b09014c0505120a0208280903010a1909041108001a0b0011140d2100075a0109010b0111071e0305003e1c020a053104620106051a0013033a02060907010906203a1d010103022d0e0a1b00020544052c1f040108020909170104051a221e00290c0000003a015c021b134316020a00000001000001000d020800000409070500043a0705130310060004020e0c010c090b1901070c001a03001601070700110004110601030a050200170c04090903021003530a19010a01020624152007280212071f05030301222304010102080100030c0003081105050e10 else 0xcd4c5b18a9c6e13d915a8883d020b61e1e5d8cc35a7152a70ff81c00004e6398fbd74ecd780007bf6326d0f083c60001a3207a5f8ec0001b84320bd8faf8494fdc0005c71000075665839d2700018e34000524e513617440007b3e5e6fcb1ae3d80009442562cf5246a90000904fc242a1cf9c0000000035f600000003900541c7874c74e0803c9137af87a179c7c377a151c22b3b0b8f471928f202e7822c3ead44c0001ea2e1ae0000058c0bf1034b67f726ea6ab7fc0001c7b00001c0a6fe6d640270000000000001a189a30c2fb3245434000149f400051a7dbb338040001281375f6a242213d4d9b921074000000000000002a3bc8f03ee56e1706ae24ab6247df5a4254ccd7d3666bc3f11830b6600023cb231b0000421242ca30abc7288d25650c6b8052db28006add50a49fe24e9acda22016b4ba8705f255cacc34dc730d32fec3e350bb30ec9d3b286215f67c864e00ebbb2d79057cc80cc31b5771853c58fa16d3b7dcf14a36975e44c61ad7a17b939141caed0a8e3011bec50165550aaee9e0beabc961e17c270000a5514f4699c0e5271df5416394a4f700012b99e600000a215409e9cbb356bc757aac0003a59ec8e985e141ea520631fbbcc8250c5b2e58728cf00000cb43c5410004f93172409efc60c39359a28ca89ef8000dc70118c0000ad88038af7a6b2beff0ce5573b8c8132e0000c3d7d262d67a304c66e90ce5447af4e82a83b0ef00001e5720238000000039894f79bb1b01c000000000000001e7478a880007e1798ada316ed1fb575dff54fb9bf12e122c23146dc4c7820adb018d63c00013d65a37124b000000008aec984e52e9d119a8af7a000068af247de330001e218e96c4b6b15a00019ac221f0001879411680009c6b88589ad827a0001f45400022cde06f0378000000000011c640000000000000034d98000000177224bb80002e4c00000003a2590869b080005b6a571000000a7b76ba38d935a901000083620002cc061ce00000000a50a56621b352760f77b059e098bb40000000ec882a5919180008b9800000007f3bd7fe03940003a8714118ed28df00003d760bb3449bbda5d6da55fe6280000000fd240006f100000637cb4300006aa8414c0000000177765e18291cb01e74000000000000001e2e0f5194d59992125c00053aa409979e397200000000d507f967b557e13a805e25e8f3c2860000000250dca531c4ddf908db03f60000447ef3982e38ab0000000000016770000773300005b5debf28380001d2e84d080008b8b70bd0315c993bf42b8bb0880000963823555740e700017ca0e72786ceeb7065fe22384be596228ecfc987565991deeec01f57db7c00011a380002bc42d680007f84000058c7499c926964e7ad316ab7628299c90d6f3ea6c00012dd0f0cb58f33f40befd2a571f20cf20) else (if i < 3 then 0x20f000000000003870b1a40000b06800068916bea000172f5ec76927640c00019c063e53da702200000065d08191667809bee92580005f680000cf2465f11d5451f7556cc6fe1800000002651698a000074e40000000d59d5d4605b8d170000e0b800000000bc7776c05dcd4b0000c0ec00072385ac600009f000000000d07c26e000039de27c3f8b00005831e7d00007d96168a000111f62be5d1000019cdaac70e81f06e1eddde4000102a8db00000a9074a6161f071d94c1dc71958356a677e7966b5693fa8ed8c5f9c2f7e420001caf27a511a04d076e5800000000000000000003460000c29b61d8c9270291833e7a3503bb828a9d616910928332c24359818f0e8bf0275ea80000000dcc85b90ea77d34000076f56dc2d28e0d80003aa507c88e107209d58b7a8c0780000000cb69f2a9261bdb5295808cd84606ed3c40dba4796b2ba582030018c724660001ca1068f54a84d1f360c000207af081d914d9dc8129b852e6bc7a7df46c0ffbfbc17c2239133996062e380cbddc0d37c37c10868c83c3deb161d25eb94ee406d36810001cc0c8cc253700015a826d392a624bf87f05eefeb2360d3154198a23bf262a468b4380007cfc2c2e98e25992679459a4a715dc00014526a6c3c11e76495a00006334e51b62840615244994ca5babc55e93d914a4ec00068ccc9cb48275be4d90286bf5b122880009ab6b0cceb064b200011718d7e1f645b246e98000000000005de40002dee89fdeda3494fafe95b2cfd8000437e7ce891640007cf1dc9996940004be11779fbdbdb0fa24b9a7982226a166c57905d1c102391d00002d70b46feb7000037a40007bbd87d60001024a3149e696ccf988e651b88aeba933dbdaecc7dcfa1cb7c448061e7c0f92345bd11b00000000000019e717f7913393955a16adc44949f8478ec76bb0ad80408fece8d159ceeb3e9e6e0c0006802ebbf244c0004878bd6331c1f11ca79035d11270e42a13089be8cafa346cb4e0c4963a8cda73e15edb1b59164fa2a77e1740000e0616a40001811c6d800001d75589c01bdb7400001dd6df93ccf1b9a2a90000fa100003f1ead0609d825061405e6e282957374651cd7b7dd4472548650f52ca2afdd110000198e00000001a9b2cba00008d5f95a00007e48000469b000013783353ed26ea72a861338e343948c61e2518000fbd40001767dc230001ec78cb200001e90eb4c7aa9d8729b4cde99ce82dd9d8bc46000079c7000054406ee8000375200010edd1021d3204f316f2f4ecdc5d7cedc33005a0f20db000030e80001dd600000d84eec00000000742b5b0cc64c0007521000000030a58000e473d74904f842720efe69400011592ea5cb58dc542dc36ed23ef730bafd56cbf1421298000613bd52bcf22332118d8291d688000e31220a1157d6f54285e4536c8f8 else (if i < 4 then 0x711f8be954c4ff85ff72c755ecb1b1195608c1c3b1f2d6655c61c89da64146f00017df9145d9236c2804334e79475d152127bd0bc3cdcd9cac4359c84c14daa9cc6d5cb8aed2434bd1b9578b2000053b960774a5b75de44bd8b80006edfee9f2328e0e9b520001e4400000001eeac0000301000161ef88300000000e297a848d110001818c0000000f5f59e5158ccd43432523f211500005b1defce66e8f7c23167c347909c6a469f18bc000000073d35893438c97da9888256836a1a600019af24348291120b760837c40eecee1af588b40db97825246c8a4176e211d18fd1fd83406c4c000317b359572606b1512ae29452be00c197449b969b267b00005c15699fcba75ba8000617876214de2944d6a8a503028102a6b3885d7b37800000008147442cd46000134cc6b7000051f200029868000a80d60260e4ff8c2d90c4903af7061000050d86a87cfbfb0a0000000490b0000879dc440000f117ae3ac2100005e0ed03c77d8000546f35df2bf800067f0c45c0004e16a7660002f904d815be17dddde6322f744006d2cadf11030ccdc6f59ec76381502cb057cdb357b1b04461d14b2d82d3cbac0000000eba8000043a416d00000002ba12235feb41b512d07c90175a609000000004b2775d8a500000000190062be80004302000000021e22700000161844ade5fe00021620000fb37b3cb1322bf400018c380005b7916e6720b391c579a562f1780000000796f9b8c476800041f0901400074ed00015d30000000014626bc00000000adf56a4c000521b0000000227c000000011cac00036a800002dc00004856a53c0f2f3c191eb1d6a000000021bb00000fd4f3bcb267ae97b7cd24e34b19a04028daf023d0001fa9b1201a106a561c4904b6cc600009a3882f84f01a1dcde2135deecc9d68868707dc9800000002eafff8f542921f6bc6cf91523230f7324e83ecaac92ec0001986e59ea9bb6201248d90bc4f9cda80005c3617c57194547d2c2d9f799780005e4585b11b7fce9b3d40003b12a17c9e82d26ab3302c96d74801d1493778f2e82d0f92f000038f1a7992f7cdcad56578ec541722eadb574f7229613a66bac1a99820087fb30000229c208a811200031db373cd374000161480002006632e8a2f83a7cc0a00400014572a4d5bd000054eadd164b8e5514de17c6e000007bfaa90001195cd798000f26ed13ea9f03c5a72a00000004e7c77cce6b34788c9f936459ad6ff0571d03e00005940000b7220000000761c6a0f740800000005b492dac75ea826720f4986161086423b1829dea7d99f9805f031f49794a90ca0e2634f917373fdc54ae3445ad0001bb6440b00136e4e0001df8070102b1db0c000402da62d90fd9e95787b47e000334800008cc934bd8161e2eee1809b45f6a33f1548d47585a89cb63baac91e299e73bbd80 else 0x1c7df336e6b8000047b5cb3f2b408e96e048914236241800010de83b0be15d5703020c0dfa8530113707e125167ed7c0002e0ae3841b4db421aa0d97a493d5e1c2750079dd7ffc34e70fde4000148fd28e91739760419fcb33134b57762eea4532ec57f12f5e428000000004bcee989ee9c77996d85f20aaf62d8b3f8b7b0997eea16a700000000f4480004af11399138aa27178b8546987f34e06a1f1e40003a230000b74aed24000096281d3a673f554c5a449b8688623c6be908b3da8e300120039ab7a2851418cba469b0400036db58db40ac40ae377f74949fbbbb51c5d460403c0000000577c01600004e03000042f7f218000b40b9c5e42550ac27b842797b3dd311586254df0ee15e0899acdcaf29696b1878b87ed880007120b0e07ca96ac01c5a7cf4ab00007d5e00016eb8000b51400000003d250af80000000038700010e7cc7525160b79b29d903dca9dd88a34532a000025e4d65346480000bf152f0505e47e060185eb2a40000941b496ed20a1b7a79e00003407cca89cc127057380003a44239321566cdfa59f2000b58336fb64d2e1e3e16cc2e7b5163d431abdd04209de0344278f98591502c65a68721df2388bfc68a5694fc7b6944c957e7f48e96b24366743c2bd72694d1f3c94c16c9ce4540709e995506ee4418eca00001a99ae5622a66a4f607819f3c7b2e6a8a000000006b805dc28d01b612dff1909206602f4fbe426c92aa4b83585b29ac8720f9cb7e6e1983900016653f2dbd0040e490b000049c4b50b8f0ae19027f5ab4b703ad535362386f1b3adb50a06c177b97a7cbf026202000319593d8f634dbc55a82ab84ee3f5cc00076a5f75881ce67ff5a3c4b402adf8c0473c2aabb74e9d2936de60e940ab78000a73d925320b2520941c796b994fe09a918b4fd53e56d044073578000799e1ee79c5000003b7402228a40003b4272f7298a90e800000010ff1a82000000014854000339400005468000734878720000a46b6e800000001863b40a0000284873896504a377778000169547219afc0004025e19c00000006b5784ae172f79f2935b7fa0001b7cb56dbb34a4b0000710f953b5a459b12cf681894b0154645da5dad46e3b3ad9df39cecb041b71b997b3a5c571e51b15a8e584bffab0e68084b2c97896f54552a8e51e15dd53019f8fe401d0c)))
def dataBits11 (i : Nat) : Nat := (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0xaa9925023fedad54c92811ff6c6aa64940c7f97544324a063feaaa21925023fe5d510c92818ff6a28864940c7fd10d3b24a047fcba61d925032ff554eec928197f6a27764940e3fd113bb24a065fe776999250337f554ccc92819bf6a26664940e5fd1133324a066fda799992503a7f3bcccc92818ffa21a564940cbfceed2b24a066fe6669592502afedb90ac92815bf6d88564940afbb6642b24a057edb221592502bfad890ac92815fe6c08564940cef9752ab24a0677eaa955925033bed44aac9281cdfa225564940eafcef2ab24a0677da695592503b3f334aac92811ff2ea5564940cefb4b2ab24a073be8855192503adf3baa8c9281daf9995464940ee7caaaa324a063fe8868d925032ff3bb46c92819bf999a364940cefcaad1b24a047fcba58d925023fe5d2a6c9281cf7a223364940ebbcef19b24a076de668cd92503baf2ac66c92819fb6a22264940e7dd1111324a067eda688992503b7733444c92819fb6962264940eedcab11324a077ad54889925033f6d1c44c9281df38ce2264940abfb6e40b24a047fcba545925039df44282c9281d6f9dd4164940ed7ccca0b24a0773e5550592503bd711282c92811ff2e93164940cfe97508b24a067f6aa845925033fad4422c9281cfda221164940cfeb4f08b24a075f67784592503b7b33422c92819fd6961164940eeecab08b24a077b554845925033fad1c22c9281df58ce1164940efcc4508b24a047fcba84592503bdaa0c22c9281cfea213064940ebf4ee98324a076fa664c192503bbd2aa60c9281df654d3064940efd44498324a077d9314c192503bf908a60c92818ff2ea8864540c7fd5544322a063fda8a21915031ff4434ec8a8197faaa7764540cbfb513bb22a071fe889dd915032ff3bb4cc8a819bf6a26664540e5fd1133322a066fda799991503a7f3bcccc8a818ffa21a564540cbfceed2b22a066fe6669591502afedb90ac8a815bf6d88564540afbb6642b22a057edb221591502bfad890ac8a815fe6c08564540cef9752ab22a0677eaa955915033bed44aac8a81cdfa225564540eafcef2ab22a0677da695591503b3f334aac8a819df6965564540c7fd10d1b22a065fe7768d9150337f33346c8a819df955a364540e7bd1119b22a075de778cd91503b6f33466c8a81dd79563364540c7fd10d1322a065fe776899150337f33344c8a819df955a264540adfb6c29322a067ecba889915033f755444c8a819fb6a22264540e7dd1111322a075ee77889915033f6d3444c8a81dbb99a2264540cfdb4b11322a0776e55889915033f6d1c44c8a81df38ce2264540cfdb4511322a067f5a8845915039fb44422c8a819fd69e1164540ebecef08b22a067f5a584591503bbb2ac22c8a819fd68e1164540efac6708b22a067f5a284591503bf311422c8a811ef6d2aa64d40 else (if i < 2 then 0x819ff6a17164540e7fd10b8b22a075fd875c5915033fed2ae2c8a81ddf9557164540cffb46b8b22a077de335c5915033fed12e2c8a81d7f5c97164540efdc44b8b22a057febb54591502bfedc2a2c8a819ff6a15164540e7fd10a8b22a057fdb754591503aff3baa2c8a81ddf9555164540cffb46a8b22a077de33545915033fed12a2c8a81ddf5495164540efdc44a8b22a077f58154591503bfab8aa2c8a815ffaed3164540affb7098b22a073fe884c591502bfedba62c8a81d7f9dd3164540affb6a98b22a0777e554c591503bee99262c8a81dfb8893164540efeb0298b22a077f5514c591502bff5da42c8a815ff6e12164540cffb5090b22a073fe8848591502bfedba42c8a81d7f9dd2164540affb6a90b22a067fda548591503bbf2aa42c8a815ff6cd2164540cffb4690b22a077de3348591503bf711242c8a81dfd5c52164540efea6290b22a077f68884591503bfac3c22c8a81dfd6161164540efe90b08b22a077f57584591503bfb2ac22c8a81dfd60e1164540efeae708b22a077f55384591503bfac1422c8a81dfd20a1164540efeae508b22a077f55284591503bfa29422c8a81dfd4ca1164540efec4508b22a065feaa9dd965032fed44eecb281c7fa227765940cbfceed2b2ca0677cba955965033bf554aacb2819df6a25565940e6fd112ab2ca0757e77955965033bed2caacb281d3f9dd6365940ecfcaab1b2ca073de888cd96503aef3bc66cb281dd79563365940cfd9751132ca067eeaa889965033f6d4444cb281cfba222265940ebdcef1132ca067eda588996503bb72ac44cb281dbb58e2265940ef9c671132ca075be7750596503b9f2aa82cb281deb8894165940ebecef08b2ca077765584596503beb19c22cb281df988a1165940c7f97544326a063feaaa21935031fed4510c9a818ffa21a764d40cbfd553bb26a065fda89dd935038ff444eec9a8197f9dda664d40cdfd5533326a066fda89999350397f444ccc9a819bf69e6664d40e9fcef33326a063fe88695935032ff3bb4ac9a819bf999a564d40abfb6e42b26a056fdb621593502beed990ac9a815fb6c88564d40afeb6242b26a057f9b0215935033be5d4aac9a819dfaaa5564d40cefb512ab26a0737e8895593503abf3bcaac9a819df69a5564d40ecfccd2ab26a0677da595593502b7edb0a4c9a819fb2ea2264d40cfdd5511326a067eda8889935039f744444c9a81d7b9de2264d40cfdb4d11326a076ee66889935033f6d2c44c9a81ddb9562264d40abfb6e40b26a053fdb808593502afedb842c9a815bf6d82164d40aefb6a10b26a057ddb308593502bfcd8042c9a819fd2ea1164d40cfed5508b26a067f5a8845935039fb44422c9a819fd69e1164d40ebecef08b26a076f666845935033fad2c22c9a81ddd9561164d40efcc4508b26a047fdb8 else 0xcca9b22a0777d8554d91503bbf2aaa6c8a81df760d5364540efbae6a9b22a077de888cd91503beec3c66c8a81df761a3364540efbaed19b22a077dd858cd91503bee42c66c8a81df75d63364540efbacb19b22a077de558cd915033ff44344c8a819ff61da264540cffb0cd1322a067fd76689915033fec2b44c8a819ff215a264540cffaead1322a067fd65689915033ff2ab44c8a815ffaed8264540cffb74c1322a067feaa609915033fed4304c8a81cffa218264540e7fb0ec1322a075fe7760991503b7f33304c8a819ff6958264540eefcaac1322a067fda3609915039fec1b04c8a81df78cd8264540cffb44c1322a067feaa20991502bfeda904c8a819ff6948264540eefcaa41322a057fdb3209915033fed1904c8a81df78cc8264540affb6241322a067feaa5c991502bfedc2e4c8a819ff6a17264540e7fd10b9322a067fda65c991503b7f332e4c8a819ff6957264540eefcaab9322a067fda35c991503afeb9ae4c8a81df78cd7264540affd76b1322a057fdb8589915033fed42c4c8a81cffa216264540affb6eb1322a075fe7758991503b7ebb2c4c8a819ff6956264540edfacab1322a0777e55589915033fed1ac4c8a81dbf58d6264540efbc66b1322a067fda258991503bf6c12c4c8a815ffaed5264540cffb74a9322a067feaa54991502bfedc2a4c8a819ff6a15264540e7fd10a9322a057fdb754991503afe5baa4c8a81d7f9dd5264540affb6ca9322a067fda654991503b7f332a4c8a819ff6955264540eefaeaa9322a0777e55549915033fed1aa4c8a81ddf54d5264540efbc66a9322a067fda254991503bf6c12a4c8a81dfb5c95264540cffd5429322a057fdb8149915033fed40a4c8a81cffa205264540affb6c29322a067fda614991503b7f330a4c8a815ff6cc5264540cffb4629322a077de3314991502bfed88a4c8a815ffaed3264540affb7099322a073fe884c991502bfedba64c8a81d7f9dd3264540affb6c99322a076fe664c991502bfedaa64c8a81ddf9553264540efbae699322a077ed824c991503bf65c444c8a81dfba222264540efdb0f11322a077ed8688991503bf6bb444c8a81dfb2d62264540efdb0b11322a077ec8588991503bf6bac44c8a81dfb5962264540efdcab11322a077ed8388991503bf6b9c44c8a81dfb58e2264540efdaa711322a067feaa889915033fed4444c8a81cffa222264540cffb4d11322a076fe66889915033fed2c44c8a81ddf9562264540cffb4711322a077de3388991503bf6c1444c8a81dfb58a2264540efdaa511322a077ed3288991502bff5db02c8a81cffa218164540cffb4ec0b22a075fe77605915033fed2b02c8a81ddf9558164540cffb46c0b22a077de33605915033fed1302c8a81cff6098164540efdc44c0b22a057febb5c591502bfedc2e2c8a)) else (if i < 5 then (if i < 4 then 0x2503bfa54422c9281dfda221164940efeb0f08b24a077f58684592503bfabb422c9281dfd2d61164940efe94b08b24a077f58584592503bfa42c22c9281dfd5d61164940efeacb08b24a077f65584592503bfac1c22c9281dfd5ce1164940efeac708b24a077f55384592503bfac1422c9281dfd58a1164940efeaa508b24a077f532845925033ff55422c92819ff6a21164940e7fd1108b24a067fda784592503aff3bc22c92819ff6961164940eefcab08b24a077bd54845925033fed1c22c9281df78ce1164940efdc4508b24a077f58184592503bfab8c22c9281dfd5461164940efea6308b24a077f52184592503bfd44260c9281dfe61d3064940eff30c98324a077f9764c192503bfcc2a60c9281dfe2153064940eff2ea98324a077f9654c192503bfd2aa60c9281dfe6093064940eff2c498324a077f9524c192503bfcc0a60c9281dfe2053064940eff2e298324a077f9614c192503bfca8a60c9281dfe1453064940eff24298324a077fa114c1925039fe5ad10c8a81cff2ca8864540cffd5544322a067fe8869d91502bff5db0ec8a819ff2e98764540cffd54c3b22a067fda861d915039ff4430ec8a81d7fa227764540cffb4ec3322a075fe7761991502bfedc2ecc8a819ff6a17664540e7fd10bb322a075fd875d991503b7ec3cccc8a819ffa21a564540cffb0ed2b22a067fd86695915033febb34ac8a815ffaed8564540cffb74c2b22a067feaa615915033fed430ac8a81cffa218564540e7fb0ec2b22a075fe7761591503b7f3330ac8a819ff6958564540cffd5442b22a057fdb321591502bfed910ac8a815ff6c48564540cffd54bab22a057fdb85d5915033fed42eac8a81cffa217564540ebfb0ebab22a067fda65d591503b7f332eac8a815ffaed6564540affb70b2b22a067fda8595915039ff442cac8a815ff6dd6564540ebfceeb2b22a076fd8659591503b7ebb2cac8a819ff6956564540eefb0ab2b22a0777cb895591503bbf444aac8a81ddf61e5564540eefb0d2ab22a0777d7695591503bbe594aac8a819ffaaa5564540cffb512ab22a073fe88955915033fed34aac8a81dbf99a5564540eefb0b2ab22a0777d65955915033ff44346c8a819ff61da364540cffb0cd1b22a067fd7668d915033fec2b46c8a819ff215a364540cffaead1b22a067fd6568d915033ff2ab46c8a815ffaed8364540e7fd10c1b22a075fe7760d91503b7f33306c8a81ddf9558364540affd76b9b22a057fdb85cd915039ff442e6c8a81d7f61d7364540edfcccb9b22a0777e555cd91502bff5dac6c8a815ff6e16364540e7fd10b1b22a057fdb758d91503aff3bac6c8a81dbf6196364540eefcaab1b22a077dd8358d91502bff5daa6c8a815ff6e15364540e7fd10a9b22a057fdb754d91503aff3baa6c8a815ff6d95364540edfc else 0xf9553264940efdb0499324a077ed524c992503bf744444c9281dfb61a2264940efdb0b11324a077ec8588992503bf6b2c44c9281dfb9562264940efdb0711324a077ed6388992503bf6a9c44c92815ff6e0a164940e7fd1050b24a057fdb728592503aff3b942c92815ff6d4a164940eefcaa50b24a057febb605925033fedd302c92819ffaa98164940cffb50c0b24a073fe88605925033fed3b02c9281d7f9dd8164940edf96cc0b24a073fd8660592503b7f33302c92819ff6958164940eefcaac0b24a077bd54605925033fed1b02c9281df78cd8164940e7fb04c0b24a077ee2260592503bfa50b02c92819ffaa88164940affb6e40b24a067fda720592503aff3b902c92815ff6d48164940cffb4a40b24a0777e5520592503bdeaa102c92815ff6cc8164940cffb4640b24a077de3320592502bfed9102c9281dfb8888164940affd76b8b24a067feaa5c592502bfedc2e2c92819ff6a17164940e7fd10b8b24a075fd875c592503afebb2e2c9281dbf9997164940cffb4ab8b24a0777e555c592503bdeaa2e2c92819ff68d7164940efbc66b8b24a067feaa58592502bfedc2c2c92819ff6a16164940e7fd10b0b24a057fdb7585925033fed3ac2c9281d7f9dd6164940cffb4ab0b24a0777e5558592503bdeaa2c2c92819ff68d6164940efbc66b0b24a076fd6258592503bf7112c2c9281dfd6056164940affd76a8b24a067fdba545925033ff552a2c92815ff6e15164940cffb50a8b24a073fe8854592502bfedbaa2c9281d7f9dd5164940affb6ca8b24a076fe66545925033fed2aa2c9281ddf5955164940eefcaaa8b24a077bdb454592503bdeaa2a2c92819ff68d5164940efbc66a8b24a0777d5254592503bf7112a2c9281dfd6055164940efeae2a8b24a067feaa14592502bfedc0a2c92819ff6a05164940e7fd1028b24a057fdb3145925033fed18a2c9281df78cc5164940affb6428b24a077ee2214592503bdf44282c9281def61d4164940ef7b0ca0b24a077bd7650592503bdec2a82c9281def2154164940ef7aeaa0b24a077bd6550592503bdf2aa82c9281def6094164940ef7ac4a0b24a077bd5250592503bdec0a82c9281def5c54164940ef7aa2a0b24a057febb4c592502bfedc262c9281cffa213164940affb6e98b24a075fe774c592502bfedb262c9281dbf9993164940affb6a98b24a0777e554c592503beeb1a62c9281df74c93164940efdc4498b24a077f5814c592502bff5da42c92819ffaa92164940affb7090b24a067fda8485925039ff44242c92815ff6d92164940edfccc90b24a057fdb5485925033fed2a42c9281ddf9552164940ef7aa890b24a057fdb3485925033fed1a42c9281df78cd2164940efdac490b24a077ed3248592503bdea0a42c9281dfd4c52164940efe97508b24a077f4b88459) else (if i < 6 then 0x324a076fd87999925033ff4434ac92819ff61da564940cffb0cd2b24a067fd7669592502bfedc14ac9281cffa20a564940affb6c52b24a076fe6629592502bfed894ac92815ffaed8564940cffb74c2b24a067feaa615925033fed430ac9281cffa218564940e7fb0ec2b24a075fe7761592503b7f3330ac92819ff6958564940cffd5442b24a057fdb321592502bfed910ac92815ff6c48564940cffd54bab24a057fdb85d5925033fed42eac9281cffa217564940ebfb0ebab24a067fda65d592503b7f332eac92815ffaed6564940cffd54b2b24a057fdb8595925033fed42cac9281cffa216564940affb6eb2b24a075fe7759592503b7ec32cac9281dbf5d96564940cffb4ab2b24a0777d8559592503bbe5d4aac9281ddf2e25564940eef9512ab24a0777e8895592503bbec3caac9281ddf61a5564940eefaed2ab24a0777cb1955925033ff554aac92819ff6a25564940e7fd112ab24a067fda695592503b7f334aac9281ddf6165564940eefacb2ab24a077be8855192503bdec3aa8c9281def6195464940ef7aecaa324a077bd8555192503bdeb2aa8c92819ffa21a364940cffb0ed1b24a067fd8668d925033febb346c92819ff615a364940cff90ad1b24a067fd7568d925033feb2b46c92819ff955a364940affd76c1b24a073fe8860d92503aff3bb06c9281dbf9998364940eefcaac1b24a057febb5cd92502bfedc2e6c9281cffa217364940ebfb0eb9b24a076fe665cd92503bbf2aae6c92815ffaed6364940affb70b1b24a073fe8858d92502bfedbac6c9281d7f9dd6364940edfb0cb1b24a0777e5558d92503beec1ac6c92815ffaed5364940affb70a9b24a073fe8854d92502bfedbaa6c9281d7f9dd5364940affb6ca9b24a076fe6654d92503bbec2aa6c9281ddf9555364940efbb06a9b24a077dd7354d92503bef44466c9281df761e3364940efbb0d19b24a077dd768cd92503beec2c66c9281df72163364940efbaeb19b24a077dd658cd92503bef2ac66c92815ffaed8264940cffd54c1324a073fe8860992503b7f33304c92819ff6958264940eefcaac1324a077bd54609925033fed1b04c9281cff60d8264940efbc66c1324a057febb589925033ff552c4c92815ff6e16264940cffb50b1324a073fe88589925033fed2ac4c9281dbf5956264940eefcaab1324a077bd54589925033fed1ac4c9281dbf58d6264940efbc66b1324a077ed8258992502bff5daa4c92819ffaa95264940affb70a9324a067fda8549925039ff442a4c92815ff6d95264940cffb4ca9324a076fe6654992503bbf2aaa4c9281def5515264940cffb46a9324a0777d5354992503bef19aa4c9281dfb6095264940efdac4a9324a057febb4c992502bfedc264c9281cffa213264940affb6c99324a076fe664c992502bfedaa64c9281dd else 0x9ff44444c9a819ff69a2264d40edfccd11326a067fda588993503bbf2ac44c9a81dfb60a2264d40efdac511326a077ed5288993502bff5db02c9a819ff6e98164d40cffd54c0b26a067fda8605935039ff44302c9a819ff69d8164d40ebfceec0b26a076fcb6605935039fec3302c9a81dbf9998164d40cffb4ac0b26a0777e55605935039fec1302c9a81dfb8898164d40cffd5440b26a057fdb7205935033fed3902c9a81d7f9dc8164d40affb6a40b26a067fda520593503bbf2a902c9a815ff6c88164d40efdc4440b26a057febb5c5935033ff552e2c9a815ff6e17164d40cffb50b8b26a073fe885c593503afec3ae2c9a81d7f5d97164d40edfcccb8b26a067fda55c593503bbf2aae2c9a81d7f5c97164d40efdc44b8b26a067feaa58593502bfedc2c2c9a819ff6a16164d40e7fd10b0b26a057fdb7585935033fed3ac2c9a81d7f9dd6164d40cffb4ab0b26a0777e5558593503b7eb12c2c9a81dfb8896164d40efeb02b0b26a057febb545935033fedd2a2c9a819ffaa95164d40affb70a8b26a067fda8545935039ff442a2c9a815ff6dd5164d40ebfceea8b26a057fdb654593503b7f332a2c9a819ff6955164d40eefacaa8b26a0777e5554593503bbea92a2c9a81dfb8895164d40efeb02a8b26a077f571545935033ff550a2c9a815ff6e05164d40cffb5028b26a073fe8814593502bfed90a2c9a81dfb8885164d40affd7690b26a067fdba485935033ff55242c9a815ff6e12164d40cffb5090b26a073fe8848593502bfedba42c9a81d7f9dd2164d40affb6c90b26a076fe6648593502bfedaa42c9a819ff6952164d40eefcaa90b26a077ed6248593503bf711242c9a81dfd5c52164d40cffd5410b26a057fdb8085935033fed4042c9a81cffa202164d40affb6a10b26a067fda508593503bbf2a842c9a81dfd2e21164d40efed1108b26a077f58784593503bfac3422c9a81dfd5da1164d40efe96b08b26a077f58584593503bfa42c22c9a81dfd5d61164d40efeacb08b26a077f65584593503bfa59422c9a81dfd60a1164d40efe90508b26a077f57284593503bfab1422c9a81dfd54a1164d40efe8a508b26a077f622845935033ff55422c9a819ff6a21164d40e7fd1108b26a067fda784593503aff3bc22c9a819ff6961164d40eefcab08b26a077ee2284593503bfac0c22c9a81dfd5c61164d40efeaa308b26a077f52184593502bfedb950c92815ff6d4a864940affb6254324a073fcbaa21925039fe5ad10c9281cff2c68864940cffd5544324a067fe8869d92502bff5db0ec92819ff2e98764940cffd54c3b24a067fda861d925039ff4430ec9281d7f2a27764940ebfd113bb24a067feaa619925033fed3b0cc9281d7f9dd8664940cffd54bb324a057fdb85d9925033fed42ecc9281cffa217664940ebfb0ebb))) else (if i < 11 then (if i < 9 then (if i < 8 then 0x2165940efdc4490b2ca077f57148596503bfa98a42cb281dfd5d61165940efecab08b2ca077f57384596503bfaa9c22cb281dfd5ca1165940efeaa508b2ca077f45284596503bfa99422cb281dfd88a1165940e7f96b44326a073fcb2a21935039fe58d10c9a819ffaaa8864d40cffd10d3b26a057febb61d935033fe5d30ec9a819ffaa98764d40cffb50c3b26a073fe8861d93503aff444eec9a819ffaa98664d40cffb4ec3326a075fe77619935033ff552ecc9a815ff6e17664d40cffb50bb326a073fe885d993503afec3aecc9a81dbf61e6664d40cffd10d2b26a067fd87695935033fec334ac9a819ff5d9a564d40affd76c2b26a067fdba615935033ff5530ac9a819ff6a18564d40e7fd10c2b26a073fd8761593503aff3bb0ac9a81dbf9998564d40cffb4ac2b26a067feaa21593502bfed910ac9a815ff6c48564d40cffd54bab26a057fdb85d5935033fed42eac9a81cffa217564d40ebfb0ebab26a067fda65d593503b7f332eac9a815ffaed6564d40cffd54b2b26a057fdb8595935033fed42cac9a81cffa216564d40affb6eb2b26a075fe7759593503b7ec32cac9a81dbf5d96564d40cffb4ab2b26a0777d8559593503bbe5c4aac9a81ddfa225564d40eefb0f2ab26a0777d8695593503bbebb4aac9a81ddf2ca5564d40eef9632ab26a067feaa955935033fed44aac9a81cffa225564d40cffb4d2ab26a076fe6695593503bbec2caac9a81ddf5965564d40affd76c1326a067fdba609935033ff55304c9a819ff6a18264d40e7fd10c1326a073fd8760993503aff3bb04c9a81dbf9998264d40cffb4ac1326a0777e55609935033ff55104c9a815ff6d48264d40cffb4a41326a0777e5520993502bfed8904c9a819ffaa97264d40affb70b9326a067fda85c9935039ff442e4c9a819ff6997264d40edfcccb9326a067fda55c993503bbf2aae4c9a815ffaed6264d40cffd54b1326a057fdb8589935033fed42c4c9a81cffa216264d40affb6eb1326a075fe7758993503b7ebb2c4c9a819ff6956264d40edfacab1326a0777e5558993503bf6c12c4c9a815ffaed5264d40cffb74a9326a067feaa54993502bfedc2a4c9a819ff6a15264d40e7fd10a9326a057fdb754993503afe5baa4c9a81d7f9dd5264d40affb6ca9326a067fda654993503b7f332a4c9a819ff6955264d40eefaeaa9326a0777e5554993503bf6c12a4c9a81dfb5c95264d40cffd5429326a057fdb8149935033fed40a4c9a81cffa205264d40affb6c29326a067fda614993503b7f330a4c9a815ff6c45264d40efd97111326a077ee8888993503bf6c3c44c9a81dfb61a2264d40efdaed11326a077ecb588993503bf6c2c44c9a81dfb2162264d40efdaeb11326a077ed6588993503bf72ac44c9a81dfb2c62264d40cffd5511326a067fda888993503 else 0x77fd754c591503bff2aa62c8a81dff6093164540effaa498b22a077fe8848591503bfec3a42c8a81dff6152164540eff90a90b22a077fd7548591503bff2aa42c8a81dff60d2164540effae690b22a077fd5348591503bfec1242c8a81dff5492164540effa6490b22a057febb61d965033fe5d30ecb2815ffaed8565940e7fb0ec2b2ca075fe77615965033ff552eacb2815ff6e17565940cffb50bab2ca073fe885d596503afec3aeacb281ddf61e5565940eef9652ab2ca067feaa955965033fed44aacb281cffa225565940eefb0b2ab2ca057febb60d96503aff3bb06cb281ddf9558365940affd76b9b2ca057fdb85cd965039ff442e6cb281d7f61d7365940eefcaab9b2ca076fd7558d96503b7f2aac6cb2815ffaed5365940affb70a9b2ca073fe8854d96502bfedbaa6cb281d7f9dd5365940eefb0aa9b2ca0777e5554d96503beec1aa6cb281df75cd5365940efbb0f19b2ca077dd858cd96503beebac66cb281df79563365940affd76c132ca073fd8760996503aff3bb04cb281ddf9558265940e7fb06c132ca077de33609965033ff552e4cb2815ff6e17265940cffb50b932ca073fe885c9965033fed2ae4cb281ddf9557265940ebfae6b932ca076fd635c996503bef19ae4cb2815ffaed5265940cffb74a932ca067feaa54996502bfedc2a4cb2819ff6a15265940e7fd10a932ca057fdb754996503afe5baa4cb281d7f9dd5265940cffb4aa932ca0777d7554996503bbf2aaa4cb281dbf58d5265940eefaa6a932ca077de3354996503bf6c12a4cb281dfb5c95265940cffd542932ca057fdb8149965033fed40a4cb281cffa205265940affb662932ca076fd6314996503bef198a4cb2815ff6c45265940affd769932ca057fdb84c9965039ff44264cb2815ff6dd3265940ebfcee9932ca057fdb54c996503bbf2aa64cb281df75cd3265940efdb049932ca077ed8788996503bf65ac44cb281dfb6162265940efdaeb1132ca077ee5588996503bf6c1c44cb281dfb5ce2265940efdaa71132ca067feaa889965033fed4444cb281cffa222265940cffb4b1132ca0777e5588996503b7eb1c44cb281df78ce2265940efdb051132ca077ed5288996503bf699444cb2815ffaed7165940eefcaab8b2ca077de335c596503afeb92e2cb281dfb8897165940affd76a8b2ca057fdb754596503aff3baa2cb281ddf9555165940efbc66a8b2ca0777d5254596503bf7112a2cb281dfd5c55165940ef7aeaa0b2ca077be5550596503bdeb9282cb281def5494165940ef78a4a0b2ca077be2250596502bff5da62cb2815ff6dd3165940ebfcee98b2ca057fdb54c596503bbf2aa62cb281df74c93165940efdc4498b2ca057febb48596502bfedba42cb281d7f9dd2165940affb6a90b2ca0777e5548596502bfed9a42cb281df78cd) else (if i < 10 then 0x3b06c8a81dff6d98364540effaecc1b22a077fdb560d91503bfec2b06c8a81dff5d58364540effacac1b22a077fe5560d91503bfed9306c8a81dff6c58364540effd76b9b22a077fdb85cd91503bfe5c2e6c8a81dffa217364540effb6cb9b22a077fd865cd91503bfedaae6c8a81dff6157364540effacab9b22a077fdb25cd91503bfed8ae6c8a81dff61d6364540eff96ab1b22a077fd8558d91503bfebaac6c8a81dff9556364540eff964b1b22a077febb54d91503bfedc2a6c8a81dff2e15364540effd10a9b22a077fdb754d91503bfec3aa6c8a81dff6d95364540effb0ca9b22a077fd7654d91503bfec2aa6c8a81dff5955364540effb64a9b22a077fcb254d91503bfed8aa6c8a81dffaed8264540effb6ec1322a077fd8760991503bfedb304c8a81dff5d98264540effb6ac1322a077fcb560991503bfec2b04c8a81dff5d58264540effacac1322a077fe5560991503bfed9b04c8a81dff60d8264540effae6c1322a077fd6360991503bfea9b04c8a81dff6c58264540effaa641322a077fe885c991503bfec32e4c8a81dff6157264540effacab9322a077fd835c991503bfeb1ae4c8a81dff54d7264540effb0eb1322a077fd8558991503bfebaac4c8a81dff9556264540effb06b1322a077fd7358991503bfea9ac4c8a81dff6096264540effd76a9322a077fdb854991503bfe5c2a4c8a81dffa215264540effb6ea9322a077fd8754991503bfedb2a4c8a81dff6195264540effaeca9322a077fd8554991503bfeb2aa4c8a81dff6cd5264540effb06a9322a077fd7354991503bfeb1aa4c8a81dff54d5264540effb04a9322a077fd6254991503bfed8aa4c8a81dff6185264540effb0629322a077fd6314991503bff5da64c8a81dff6e13264540eff97099322a077fe884c991503bfedba64c8a81dff61d3264540effb6c99322a077fd864c991503bfebb264c8a81dff6d53264540eff96a99322a077fd854c991503bfe42a64c8a81dff5d53264540effaca99322a077fe554c991503bfec1264c8a81dff5893264540effaa499322a077fdb14c991503bff44444c8a81dff61a2264540effb0b11322a077fc8588991503bfeb2c44c8a81dff9562264540effb0711322a077fd6388991503bfea9c44c8a81dff61d8164540effb0ac0b22a077fd7560591503bff2ab02c8a81dff60d8164540effae6c0b22a077fd5360591503bfec1302c8a81dff5498164540effa64c0b22a077fe885c591503bfec2ae2c8a81dff60d7164540effaa6b8b22a077fd825c591503bfea92e2c8a81dff4c97164540effd10a8b22a077fd8754591503bfec2aa2c8a81dff60d5164540effae6a8b22a077fd5354591503bfec12a2c8a81dff5495164540effa64a8b22a077fe884c591503bfec3a62c8a81dff6153164540eff90a98b22a else 0x940effd10bab24a077fd865d592503bfedc2cac9281dff6dd6564940effb0eb2b24a077fd8559592503bfed9acac9281dff6c96564940effb0d2ab24a077fdb760d92503bfec3b06c9281dff6d98364940effaecc1b24a077fdb560d92503bfec2b06c9281dff5d58364940effacac1b24a077fe5560d92503bfed9306c9281dff6c58364940effd10b9b24a077fd865cd92503bfec2ae6c9281dff5957364940effb70b1b24a077fdb758d92503bfec3ac6c9281dff6d56364940effb0ab1b24a077fd7558d92503bff2aac6c9281dffaed5364940effb70a9b24a077fcb854d92503bff442a6c9281dff6dd5364940effb0ea9b24a077fdb654d92503bfec32a6c9281dff5d95364940effb0aa9b24a077fd6554d92503bfed92a6c9281dff6c55364940eff962a9b24a077fcb560992503bfec2b04c9281dff5958264940effcaac1324a077fd8360992503bfea9b04c9281dff6156264940effcaab1324a077fd8358992503bfea9ac4c9281dffa215264940effb0ca9324a077fd8554992503bfeb2aa4c9281dff60d5264940effaa6a9324a077fe884c992503bfec3264c9281dff6153264940eff90a99324a077fd654c992503bff2aa64c9281dffa20a164940effb0e50b24a077fd8528592503bfec3b02c9281dff5d98164940eff96ac0b24a077fd8560592503bfebab02c9281dff5958164940effcaac0b24a077fd8360592503bfeb9b02c9281dff58d8164940effaa6c0b24a077fd8260592503bfeb1302c9281dff5498164940effa64c0b24a077fd5320592503bff442e2c9281dff6197164940effb0ab8b24a077fd655c592503bfec1ae2c9281dff58d7164940effaa6b8b24a077fd8758592503bfec2ac2c9281dff5d56164940effb06b0b24a077fd7358592503bfea9ac2c9281dffa215164940effb0ea8b24a077fd8654592503bfebb2a2c9281dff6155164940effb06a8b24a077fd7354592503bfeb1aa2c9281dff54d5164940effb04a8b24a077fd6254592503bfea92a2c9281dff4c95164940effb0628b24a077fe884c592503bfec3a62c9281dff6193164940effaec98b24a077fd854c592503bfe42a62c9281dff5d53164940effaca98b24a077fe554c592503bff44242c9281dff6192164940effb0a90b24a077fc8548592503bfeb2a42c9281dff9552164940effb0690b24a077fd5348592503bff44422c9281dff61e1164940effb0b08b24a077fd8384592503bfea9c22c9281dffaed8764540effb6cc3b22a077fdb561d91503bfed9b0ec8a81dff6c98764540effb62c3b22a077fdb761591503bfec3b0ac8a81dff6d98564540effaecc2b22a077fdb361591503bfed930ac8a81dff6c58564540effd10bab22a077fd865d591503bfec3acac8a81dff6156564540effb0d2ab22a077fdb760d91503bfec)) else (if i < 13 then (if i < 12 then 0xd7548596503bff2aa42cb281dff6cd2165940effae690b2ca077fd5348596503bfea9242cb281dff4c92165940effb6cc3b26a077fdb561d93503bfed8b0ec9a81dff6dd8564d40effb0ec2b26a077fdb661593503bfebb30ac9a81dff6c98564d40effb62c2b26a077fe885d593503bfec32eac9a81dff6e16564d40effb6eb2b26a077fd8759593503bfec2acac9a81dff6c96564d40effb0d2ab26a077fd7660993503bfedab04c9a81dff6158264d40effaeac1326a077fd6560993503bff2ab04c9a81dff6c58264d40effb0cb9326a077fd855c993503bfeb2ae4c9a81dff6dd6264d40effb0eb1326a077fdb558993503bfec2ac4c9a81dff5d56264d40effcaab1326a077fdb158993503bff5daa4c9a81dff6e15264d40eff970a9326a077fe8854993503bfedbaa4c9a81dff61d5264d40effb6ca9326a077fd8654993503bfebb2a4c9a81dff6155264d40effacaa9326a077fd8254993503bfeb12a4c9a81dff6c55264d40eff962a9326a077fd8588993503bfeb2c44c9a81dff9562264d40effd76c0b26a077fdb760593503bfec3b02c9a81dff6d98164d40effaecc0b26a077fdb560593503bfe5ab02c9a81dff6158164d40effaeac0b26a077fd6560593503bff2ab02c9a81dff6c98164d40eff964c0b26a077fd8260593503bfeb9302c9a81dff5898164d40effaa4c0b26a077fc5260593503bff11302c9a81dff5488164d40effb70b8b26a077fe885c593503bfedb2e2c9a81dff6197164d40effb0ab8b26a077fd655c593503bfed92e2c9a81dff6097164d40effac4b8b26a077fd525c593503bfec0ae2c9a81dff61d6164d40effb0ab0b26a077fd7558593503bfec12c2c9a81dff5c96164d40effaa4b0b26a077fe2258593503bfedc2a2c9a81dffa215164d40effb0ea8b26a077fd8654593503bfebb2a2c9a81dff6155164d40effb64a8b26a077fd8254593503bfe412a2c9a81dff5c95164d40effac4a8b26a077fd5254593503bff112a2c9a81dff6055164d40effb0428b26a077fe2214593503bff5da42c9a81dff6e12164d40eff97090b26a077fe8848593503bfedba42c9a81dff61d2164d40effb6c90b26a077fd8648593503bfebb242c9a81dff6d52164d40eff96a90b26a077fd8548593503bfe42a42c9a81dff5d52164d40effaca90b26a077fe5548593503bfec1242c9a81dff5892164d40effaa490b26a077fd8148593503bfeb8a42c9a81dff5452164d40effb0a10b26a077fe8884593503bfec3c22c9a81dff6161164d40effb0508b26a077fc8284593503bfeb9422c9a81dff54a1164d40effc4508b26a077fcba61d92503bfe58b0ec9281dff618a564940effb6ec2b24a077fd8761592503bfedb30ac9281dff5d98564940effb66c2b24a077fdb261592503bfed8b0ac9281dff2a17564 else 0x623230c7184b0c1c0607e300317e90be2c5eca2f3417818ba985c7c2de116c20b49c59942ca4163f0b16057f62bbf15c70acf056162ab915498a9b4547829ea14d18a5c8524028ef144e8a158500827b213b009c384d8e26751327898a44bf025a612ba8948c49ce24b6123209048476a2358117288aa444c4222610f5086e442a2212010720821c4096200f0fe987e303eb61f090f6c07a703cd61e030ecd874cc39c21c790e0886f54371c1b520d7a86a8c34ce1a150ce18664832d8193b0c8a863bc317c188d0c2e060ac2fc817870bab05c682dd216a20b33058242b9a15700a9f853b4298e14960a2d050202756138509af84d10263c12f8095e04a2c248811fd08d5845e8223a10ec085d841a42086100707e583db81e640f17077883b2c1d4a0e740711037f01b540d7906a9834b419f80ccb0652831d018440bf105da82e3c16bc0b38058902b8415600a4804f00260c124c08d4043b82170106c080503d401db00e760715037201acc0d0406510310017900b66059802b3814d80a0a04d40251811180856040501ea00e08068c0315017780af804d8023000ff8070c033a017700a30048001de00c9004c001f400980026000077febb61d96503bfedab0ecb281dff6cd8765940effb64c3b2ca077fdb761596503bfed9b0acb281dff6c98565940effb6ec1b2ca077fdb560d96503bfebab06cb281dff9558365940effb64c1b2ca077febb5cd96503bfedc2e6cb281dff6d57365940effb0ab9b2ca077fdb25cd96503bfed8ae6cb281dffaed5365940effb70a9b2ca077fdb754d96503bfec3aa6cb281dff6155365940effb64a9b2ca077fcb254d96503bfed8aa6cb281dffaed8265940effb6ec132ca077fdb560996503bfe5ab04cb281dff5d58265940effcaac132ca077fdb360996503bfeb9b04cb281dff54d8265940effb0ab932ca077fd835c996503bfea9ae4cb281dffaed5265940effb70a932ca077fdb754996503bfec3aa4cb281dff6155265940effb66a932ca077fd8354996503bfeb9aa4cb281dff54d5265940effb04a932ca077fdb154996503bfec18a4cb281dffaed3265940effb709932ca077fdb74c996503bfec3a64cb281dff6d53265940eff96a9932ca077fd854c996503bfebaa64cb281dff9553265940effb049932ca077fd524c996503bfed8a64cb281dff6162265940effcab1132ca077fd8388996503bfea9c44cb281dff6cd7165940effaa6b8b2ca077fd525c596503bfe992e2cb281dff6cd5165940effae6a8b2ca077fd5354596503bfed92a2cb281dff5c95165940effaa4a8b2ca077fd3254596503bff112a2cb281dff6dd3165940effb6a98b2ca077fd754c596503bff2aa62cb281dff6c93165940effae498b2ca077fd524c596503bfe29262cb281dff8893165940effb6a90b2ca077f) else (if i < 14 then 0xcee266ad332099544c86a639d3182987a4c14260352fce97c14bbd25d252e0496b04b3a259392c2495d64ad8255fd2ac895284a70a529528e8943849f324ea926f29327496aa4a9124ba921648f2a46d122f09131488b24369217e9083482ea40591ff68fb447c1a3d751e6e8f06476523a0d1c4c8e0046e2236d11ada8d264680232e518ce8c2045fd22f2517308b7245a0a2cc516168af0456aa2abd15128a63451ea288913f889cb44d2a25fd12b289334486a239d1182889b4445a2169106887ed43d321e010e7287134360a1a6d0ca8861842f92175d0b62858b42b2a14fd0a4884e84256211c1086883f841d8a0e01069e83084160a09bd045081cb40c7a0579025a80db404fa0134fff67fd53fd79fda0fe427ea33f441f8d8fbde7dc93ed19f570fa6c7ce43e541f208f8a27c2b3df21ee48f6967af93d539e980f44879d23cd61e594f27e79193c691e22cf046779a3bb49dcb4ed8a76733b269d818eb7e75993aae9d42ce99e74a93a2b9d0c4e7d473b939be9ccd8e62072ea39621ca78e4f0725239001c6e4e3267141388d9c3d4e19e708838261c040df926f8237a89bc28dd866e7c37151b810dbbc6db836c91b4a8d99a6ca736251b090d7fc6bc235b81acfcd5da6abc35459a968d43c69c134b21a4f8d1d868c634349a10ccff867d633c219d4cce5a6707337099aeccd2a666f33249988ccbfa65b632ac9941cc9966479321918facc73263473159989dcc47661ff30ec98648c2d86146307a18338c0f86035300797f20beec5f0e2f6397a84bc725dfd2eeb97698bad45cf72e52971fcb8705c122de596e94b6d25b222d7e16b00b4c65a1c2cfb166e8b32859632c8e16380b174587e2c269609cafec57af2b9895c00ad7256302ae995688aa7454dd2a5b95168a81053d729c814d50a65c52d1294a94990a42451aa28ac14418a15250782829140589f884f9e27a093c409dd44eb9272e138289bc84d8726b09346899e84c972638930d497dc4bc825d112df096ac4b30258512b9095664a8d253392904943649f524e212678929848fa246a1223490ce481523f791ecc8f1a476723a091c6c8dea46c4234f1195c8c6245ea22e2115f48aae4505226f912e488fa443621fd10f50871a4351219b10be885a8429821391095c844c41ea20d71062082984131208b10394817e4083202e900dc80223feb1fdd0fdf87eb03f061f700fa647ce63e4d1f138f8047bb63daa1eb18f44479d63caf1e4a0f134780c3be01dcc8ed4876583b061d700eae875283a6e1d240e88873f839e11cdd8e65472de39491c970e42071ae38bc1c4b0e1ec709438191bee8deb06f2237601b978dbcc6d58367b1b250d8646bd035ac1ab28d5286a3234e81a560d168685233cc19cd8cd50664632f2195b0ca4064d43244190f0c7e063a431a118b80c528 else 0xdd706c5834fc19e60ca7062d8303c17860b35055e829c413f209ad04b08245410e2082503d681d2c0dfe069d0328818140ac20515024380f3406aa0309011c8075c029200d100427ffdbff55ff32ff737f963fbedfd68fe787f293f7d5fb9efd887ea63f3e9f9a8fca37e1dbf029f770fb457d743eaddf4b4f9f27ce63e565f224f8e17c4d3e14df05af7c57bb9bdcddede0f6bf7b4cbd949ec2cf5e57ac9bd5b5ea8ef5217a7dbd355e95ef4897a2c3d0c9e818f3e679e03cde5e664f30c7962bca7de4c6f23d790bbc7c5e396f16378993c381e132f07378163bfeddf3cef62779e3bb7ddd5cee3b77053b739db24ed567692bb379d95aec8776203b069d7bcebad759d3abf9d5b0ea91752aba8bdd3e6e9cd74bdba555d248e8c77445ba195d026e7cc73d339da9ce88e708737139a99ccbee63972feb9629ca70e5127265b9295c8bce4387203b8f59c760e348719138ae9c512e24270f8386fdc332e13c708b3828dc0e4e02b6fdc37dc5be96dee36f5eb7981bc74ddc76ec037569ba26dced6e4db717db830dbe76ddb36dbdb67cdb0d6d73b6b05b536da756d27b68a5b406d9d26cd636619b2c0d93a6c8a363b9b190d8a26c38b612db04ad7de6bd135df1ae6ad70f6b6435a89acf8d6566b1835829abc8d59d6aa5b5411a9e8d4ce6a5435101a808d39169b034c0da562d28b693834955a3dad1a668c0344b9a1b8d0956837b40cda01acfc667ba33c899dccce9f6742339219c5acdfc66dab35b99a0cccb46647330f1982ccbf065cf32d05959cca9d6536328699390c97664a8324259158c8866414b1f318ec8c712637631a3d8cd2c60c62e8316258a6ec5276280b13998996c4a5623fb11658866c3d661c7b0da58644c2fc616b30ac184d2c22260f3306d58308c1486080b031580fcc0375ff82fefd7ef0bf265f6fafa097cb8be365f082f7a97b5cbd675ea0af3bd7992bca35e232ef797770bb665da02eb8d757aba765cfc2e64172d4b90d5c73ae1797070b7f15be5adde56e64b7175b78adb2d6d4ab67f5b2cad8cd6c1ab5e75ad02d5bd6a92b52e5a73ad305690ab4545a06acf9d6756b36f599f2cbdd65b8b295591c2c8496396b19a589eac45d61ccb0aa58372c09d5f94af9957a92bc2d5db4aeb45741ab8c55bbeadae56beab5315a20acc95651ab1455856abc355ceaad595634aaf455672aaa15504aa5c551b2a84153bea9ae54b3aa5315236a90054622a2a550c4a82653efa9e094eb8a715537229a494cc2a63b52e9a96894ab6a4fe5266a927148d6a43a51f9a8edd46e0a33f517c28af1452ca25a510f287b5438ea18b50b8284fd421ca0b15035281113fce9fab4fc2a7d253e469ef24f5b27a413cbe9e234eee276d93af49d3e4e8c2734539569c6f4e19a703537ce9bc14dcda6da936729b084d55a6939346699f74)))) else (if i < 22 then (if i < 18 then (if i < 16 then 0x855ab66d5676a77b5235a82ad39d697cb4a05a412d1a768a2b4335a0aad00967d3b3d6d9df2ce976725b37fd9b0ecd3b6661b312d97d2cb71657cb2ab5946ac9bd64a2b238d90aac7f363bdb1b5d8cbec5fd62cdb148d8956c43361e8b0d658596c25360f8b063d825ac0cb6029b001d7f1ebf435f70af9fd7c66bdd15eacaf38578d2bbdb5dbcaec05756aba535cf8ae63d725ab8e15c34ae01d6f1eb72d5b65ad9a56c0eb58f5a96ad2d5687ab3af59a6acbad6512b22758d7ac535622eb0e1584aac17d6052afdd57bdabd155dc6aead5725ab8555b92ad675677ab28d5856abc955a8aac6d5546aa6d5510aa6fd528ea8cf544caa18d5002a7b553b4a9c1d4da2a66f531ca975d4a92a5135263a90e547daa35f5168a89bd4446a1c150c5a84a5418ea091502da80953f869f354f74a7a753ca29e054ee7a75b53a6e9ceb4e5aa70f537b69b794d8ba6ad5344e99af4cbca64b531ee98ab4c3aa60fd2fe697914b8ca5add2c7e95dd4abda54bd2942942949d8a4d3d25ae927548fea466d227290d7483aa3f9d1f368f394776a397d1bce8d6f4686a330518668be745b7a2bdd14fe8a1d44dda2565121a88954419a1ff50f6287394381a1a850cd685f342b2a1465099a846b420fa0f4d06b6830f4156a092d03d281b340a8a03bd011a80153fd99fd44fdde7e8d3f159f724fafa7d1b3e519f15cf7ea7b933da39eb3cf4ae79df3cbe9e414f11a78153bd99dd44edde76773b159d724eaa275053a469d0ace766735139779ca34e42a71b338a89c3bce0ee6fff37c39bc94dd866e7736ff9b674da766cc336309affcd73a6ae335569a824d3226945345b99ff4cf0a673933559997ccc266585328699304c8ea63d131c298ce4c4fe61c530bc982a4c0ba5fcf2fa097a1cbbc65d972e6e97244b8065bb72d9f96b1cb4f65a2f2cf19665cb1e658912c2295fe4af0257352b53957b4aa9254fd2a2c95034a6fe52f12952947aca31250e5281593e749e764e8126e3935ec99da4c75261492e6c96464ac12524926ec9202485d23f291e0c8d92462522e19152c892243ed21d090b9c853641e120ca90474811e40431ffb8feac7ebe3f131f638f9ec7c5e3da11e7e8f2c478463bd71da48ebf475623a651d0c8e57c722638c71c328e0646eea36fd1b588d9946c3235cd1ac08d47c694e341919d08cc4c64de31cb18888c1045f922f3b17618b92c5bd22d4516668b20457e62ba7158c8ab3455022a1f14de8a5c4524a28d914468a1044fbe277d139889b944d32264d1300895cc49f6246d121088efc46ba231111628898c43aa218910888815c3fea1fa90f9887b943cae1ddf0eb387364386a1bd30db886b8c352e19f30cd38656c319a18550be385ce42dae16070ac78550c296a142709ed84d3425d6123108d18455c213a105107cb83c241d220 else (if i < 17 then 0xa411d0046c16511913ae36c34c01355538a078eac0220c2321f406e9625c2232a5f601104697d108414b2448ac02208d8045e84638bf0f0eac23245f890ae211902ae36c38197901d50ae7d0192722842c38197901d50ae7d019270e65d2d0194ea8573e80c918732e865e407542b9f40648cba194eaf200987d0191d0e65d0cbc80ea8573e80c90755208a80221482340d4012ea2322758b38d9805004c586a2c232fc42c34940ea953ad0048288c94022ca411a5f4bc75511921b3008b108c8c023a05984648bf1615c423245f60117a11931b6296019221195806744b308c9085208980674c9108c91158044284648bf108e4423245f8aaae211922fb008bb08c80f03a83d0a18847b9c80648390904540110a411a29a0097511913ab00a009d22ce1a8a07c539d30d05039054eb40120a232500892904697e8025d4464cbf1258050048586a281d2fa45a00909119680674caa88c897d22a4239088ca96020a231a5f601104697d108414b2448ac02208d2fa4808288c8c012cc411a5f4b0105119110c41125f4aa1051191802498823f8bed8080f3ed39f4ecf9467c373dcf9ecccf4de797f3c739dfdcedb676433abf9d39ce8f673b739a59cacce3de7183388b9c2ace0266f7b375b9b92cdb0e6d1b362b9ae4cd59e69df34b99a41cd13667d733739988ccabe649b320198cfcc446618b303797f5cbdce5dcb2e999705cb6a65ae72d3d966dcb23e58872be195cacad2655cf2a859527ca75e52eb28e79437ca08e4f8327759389c9b1e4c9f25ed92c5c94fe49bb247b9201c8ede46ab22c79111c875e42bf20bb9021c7f2e3ed31f078f47c79663bef1d7f8e8ec72ee390b1c4f8e01c6ede36ab1b098d5ec696e33f319ad8cb0c645631bf187d8c0dc5ee62edb17218b5fc59762bf715af8aa6c53ae2913142789e2c4e3e265b12cb8934c481e234b116f8886c42ae20930fd187c2c3ce61daf0e5f86fec36161a1b0cab8619c2f4616b30af7854ac28ce13a3096f847bc22ae10bf07fd83cdc1c8e0d57065f82f3c16160a1b04ab8219c0f9e06b302f7813fc0876037701598091c030600befffd7fe3bfdedfe5efee37f2abf7cdfb22fd2f7e66bf205f812fbbd7dadbebe5f52efa4b7cf4be61df24af8c37c3bbe0adefbef77d7b8dbdae5ecaef60b7ad4bd51de9f6f4997a31bd005e796f3697983bca95e4b2f1f778cabc4cde1a2f06f7806bbf05de92eed17742bb88ddb82ed5f767ebb26dd872ebed75d0baca5d5baeaa77522ba7e5d386e97774a0ba37dd152e85d7408b9f15cef2e7177370b9aadcc92e5e772c2b94e5c982e47571feb8f1dc69ee3197166b8955c3e6e1a770b8b8495c186e04b6fe9b7d6dbe4adeef6f30b7855bb92dd516e6cb7185b82adb9d6d87b6b0db4c2da156cd9b6495b1b2d8616bffb5ecdaea2d6ef6b46b5 else 0x5110e802194443a00979118d3ac59c40c028061a4ed16118823561a4bc754b401242234ee4cbf8830d5008b2d012f1d2f9d54bc88c98803a85e0887203c8323a3739088874010ca221a29a00179119310300a009d62ce1a8bc7cbf8a71061a0bc720d4012aa234ee4cbf8830d5008b2d002f1d2fd000bc88c997f10300a001670d45e384b0b215c3407b08260c18802c02e3901ec209f2fe200b00b8e407b0827cbf8802c02e3901ec209f2fe200b00b8e407b0827cbe160171c80f6104d97f100580567203d8413a4937088874010ca221a36a0096111921ce206014013561a8bc7a009d111a592629c4186a804776a6178f97f14e20c90104a97e8005e4464c40c02804774b386a2f1f10300a011dd2ce1a0bc77be0a42f01f0fa0843e01e405ff8a07c2f07a0421100f202f845089ed80184204215c1f81e525949c7d120e1a2a4946f86a80067446609207c3e1f403c5452838fa25e44656010e22cc23204506fc82e2df403e3643d81e484546f321119114a0e47132111953acc8c53869802628bd54d10a6012c88471dca9270d50008288ca8a50724b3e888cb8a70d1f44c517aa01a800774b288c997f14e1ac1c179645403c026011761190ea8498ecb2211962fbb60bd08c8157071d5e401d8648573e80c93917076860edc80ea8573e80c9391418e860ec5a0ea8573e80c93917070763aa7d01f8323e45e418383b1d503e15cfa0324e45c1da183b7203aa15cfa0324a374c47552f0322a4946f4001961a4466e3083a8025e44654eb16722b00a018e03761a42c8c3583a351d54bcd4ce915015004469dcb97f0d60ea011652f3403837e4007c3d0443aa078e9d92e9d544646010a6118ceac2959108c8c0214c2319d506508c70a58045e84648531d96442323008aa1de11922fb008bd08c8126fa021f8a0f80f1824837043f17db01f0dc0790c032ae388464cbf8a71c2c884656019553bc23265fc8bc618063884664528382f4c844654eb8a60d3004c517a6461a422909732111a772e5fc5306b073b60bd3230d212fcc80bc88c906b073004d517a6461a3a2999088c69a82f4c84464cbf8a62f4c84465096124370573be148209c24837033f17db72003c0b50c02014231ac880508c61061189804028463804b22118c24821f8a0f80f152fa5949c10489251bd00039869119922f1841d401212233439c52c02802628bd868f4013a25944645918a70d60ea011dc2f353465fc1d95420912fd004ba88c9839805008ee9662f61a3d0045288c697d22d0048488cbc6280674caa88cb8a50d60ea011dc2f2c8c34809215c291b803c508288c5038804231c0e59108c7038804231f1881c40211936403101c15c34844046781cb22118c3484402207c2b83f0467e31038804232249e30904740110a411a363e896111921b300847164940110)) else (if i < 20 then (if i < 19 then 0xa04708d106609300180ace8168e402328f7c6d954328218426438864c30d0e5004be3438866800d0e219a003438866800d0e21930c3438866800d0e186a0086488710cd001a19a009086872802291a1c43340068710cd001a3643886680110e219a003bbf7142182100c8700f9d1b2294325a02d85007a7838c02030d0c8710421052084d341c601018697eefa19b1c16c2803d3c1c60101876a50c82f09a1e4b07110c061a1c43340068710cd001a1c43272068640950018671ed0701e900e41a3e83b6c8a41085b0c40f4d065804411a45b6c0842d86207a6832c02208d22db604216c3503d341960110476dad48194aa1503103d381c8380f4706580441181a0330702b83d29b63520641141c07a646c0642705707a5832c020e0cefba9b0c11c0e441325f0321382b83d29d583824be0642285707a5832c020e0d2f8190aa1481e940e44109a3391070406a0e02d07a40327741141c07a50328382105707a5832c020e0c0d01983815c1e94eac1c101c06420321a82b83d241960107060650706a0ae0f4a0722084d1c1960107066a40e03d19d50380f460680882407a40327741941c07a5832c02070cefbc50326181941c07a7832c02070cef9c503206a0e03d341960103860720e03d1c1960103866380e03d198e0380f4606a0e00c07a436c064ea8228380f4c77d1b22904216c2803d3c1960101860680c8cb8380f4a7220308ef81938a08a0e03d325fbbe0842d85007a6832c02030cef9c50320ca0e03d325fbbe0842d85807a6832c02030c0e00630c33900701e8cc301c07a30388660e0c0e219a003038866800e8001c4323038866800c0e02d101c43340060710cd00181c43340060710cd001a190182038866800de281c433400886406090ca12a00303803049d6802214824a001653ba232629c35142a9a772c063ab08e3b90eaa411275a008852092802484ee88c983a80648c349dcbadb0746ac3492cea99241d54469dc9039804238ee481cc0211c772629c909de11932fe025ba96611972feb6c04c032442331c848224eb40110a4125004aa9dd119314d008a18693b972feb6c5383b0d04b390748b40111a77265fd6d839805000b386a25a1075004469dc997f5b629a0112d119a013008ef08c90098047784648ef0098044184656011063b8d804418ee38ee886208d804418ee34927d1110e8021944434527d12f223230087108e2c928021944434537151e2232275c418698026aaa7178ec002cc238ee4a00865110d149f449688c98813561a3e9178b4003ba234b24cbf8a71061a0bc774cc022f4231c5f3ab0f211922fbb689708c87d02c6380881a0ea87906483e810b0d0390b01e4ea8440d09c347d31c0580f27542206841f40b18e0220683aa1e419203b1f4c90110341d50f20c907d3246380761a0ea879064846e75 else 0xc0061edd4d860f83dc3c8218468839065800e0e41960030380fa10c411ee53520700c84d173086209e1b41c832c0086a40e019019106108f73c3683906580105c9f484210490da0e419600436d0d87b821882503800c7bc550f237811c2341c5c6d9205c8190dc0f611a20e41960030399d00c8f70b40f6119e0e41960033be8d80e01909a906108f7441c832c0063df1b6480dc086119a0e41960031ee77f1b6483521b8119f3a05a3aa08c88712fc211a1c43340068710cd001a1c43340068710cd001a1ca0008468710cd001a19a00908687114c21185f8bb084118de0e260f600c3a05508872011c2340198aa01c3a0417e908cf1a80c85d846378a1a80c807007176118713c2100e1583101908860ab1d0e442103215cd17e228070850840c8443bdf88b064c30540dc110f1d433449172638038016001c42607d0ca105a8d90706c482148b75410841442904a7d00c8410781f0b0720cb001875c6c0283787b3906839065800e0e419600348a1ac2b83d0f008d119e0e41960030c28a4008190141ec3c9f1b00a0cb16010a21341c832c0068dad48190d4104291838dc84420700324103e7c6c0700c8013e8028281c80e29b908840c8710a00f4d066033001e360327d0351c801414111968481900c1443883d2c1980cc0066190e00c07a403806510a4109a54ea1905c8030560fc1087b0b210543dc322290321791084d3c1c832c0069d420819442904269a0e41960034be178ea819442134d0720cb0018484840642687b2f180159d02d1c84466839065800c0e0198822e41e943cc493aa0840381c8823dd08a40ca0e0bc3dc1e9a0e4196003038066208de1ee5839065800cc30de0823dc897c1505e0328841e9a2498606e1047b960e41960030780652a8410f2531c105108f7241c832c0069a85e0410a440f2124db0071ef104d1245c98e002c00358710980fc2c0415a45e301e82912efdc504210510a4132758922e415007006004e28780421f020b2e2a360143dc3e8230b088d17160e41960040060047b86b0b00fc108590829e41838266410f40bf0d1c8441c832c007124151c504201c0e2411ee8bbe9d6e2821082905119ee2c1c832c00875641021aa61403d180561a0f4168e4160e4193aa3bbf2093a5c507a08c2c223400ace80842d2232dc583906580112fddfb8a064210410a471ee9d4309dfc34164d487a0f89cbe7542661a07e168e41c38dc84420700ca4103e71720643c61a014140e4071403c0320f43e120330083230780dd208b907a50e20dd10806032904269d800418323cbe1087b9c807a14011a23400603215c3c9203300832330c8701683d20b90e3954260410f208e11a05c84c0fa110328238467833049800f148031ef9d02205004708d10660930018193aa07120c211ee6833049800c018f7ce87142085) else (if i < 21 then 0xdf38a8840c83203e0fce8a40cdf48641d8291a0cb008043cbf8a420852222130405429100680c05034420780f83f21820a5f4326086866800a8025f124543340069d10cd001a5d43340068a4c12191d0043224d4866800d14982a0086489550cd001a424334006c62802291a62433400693a802211d0007c884683a802211a19a0097c61042f150cd004524433401070c0ca19a300080281f31dfa30864088520886a30c02010eefa19190180220253518601008697eefdc54320c82583f3d1860100860c90c80cbe8360129aefa190c014822168c402442303c03041810c9b8184b43340060b6802191a1902340060780e09e2c0e08908434960704359009611978c40e026fd211978c40e0a4f761196072c807e0961195ea84381c1a50c834340e5914802b9009c0ea401109086073f45904801a196442181c0843482833a904508434ac881c0a0e08a10bf481cb201419db3a903f0396402307f08d014a0721907e0d0b03b8c0520ae481c05a9004425204330382b84402c0d0e866073d507e094af7c1142159010e070283bdf78b0860703f2400d0e8710cf181a1930c8186866e4021082870389a1b4194441946f07134751738d801dc5056720378210f610569043d8ad4d86b8a08420a2148273e8066c305e0821f0d0720cb001a1ca0097c77d03a2210b21052c9a0e4196003352638c30490383de209c0ca0e0bc3dc3e960e419600308e7747bc41221c4334007115e40258321943d1a1b28207a1ec119d584670e8066240418421e8d17ceaab8032179eec233e36c1c723240210821c4e8d81500a40c9043e180e0194429043894fa01940d618210410f87839065800c3a86ac349783e1d5341c832c0070720cb0019d503217d280710f46baa8840e0194820d0d9140c9f408400cea8652d088d3c800e61c0061ec109d507e1942b9f4064c0328701683d2221038065208572a7517263b0d07c0f40282c84148f70aa0640185ec341f0f0720cb0018f7c349d42f07c3aa60828840ca7548215cd0720cb00181c0851045c8442c593900a81081c1ef104e064212121ee1f4b06580442182a31c6182481c8823dcf06580442186b8b26a41b8f7082606e754208f721d54a010c2087a285936d0d8150f788264388678c0d0e5004be3438866800d0e219a003438866800d0c98640c3bbf7141e8290428701a1d0ca06b0c1082087c341c6010a4777d0cd86042105208573c1c6010a468710cd001a19a0010871160cbd50d40703c98018018840643d943a0198aa1043c96352b803217a11bdd306a03200e2f4230e260520642b879245f0aa03e1e0190ae68be108078190bc110d17e0cbc82d01602218d49c80fa19420c212d07839065800e0e4196003839065800e0e4196003cbe2e4018718ba2f02c82384691726a53a01c0331601ec23441c832 else 0x1038677e10c0e0ea908190523c19601038677f2f9c58420660724208214930658040e1e36c53084c70620a4684286a070320a4503d4012f8c0f219a00303c866800e8001e432303c866800e8022903c303c866800c0f20ea0088480790750044241920842b9b8842078cc020c880c81e1b21488c020c8864c210320782215804191064192078c107703e646dc610703d0f8503d756db02143207cd7140ca1941c078fa05e0e688327d0300edb0590461d92ca2335b6832c023b1032060f8a10f9004103e70161d83e04120768321046366db06b48a3601f8230ec88d36da0cb008ec41b28a6db0d804688cd6dad4a559900fc118764468b6d06580476240203c07c1f92db4196011d88064dc22103e4bbe0780c85707e094c1882485e19215ca0640385f0921101298e2c0260106486a42b80b0dc06422182f84b03215c1f960130083230ae0302201904a50a40843702507e50040643d8442402601064617cc16550180fcb06406080f01903e15c80780c85203e40c97161c81e36c0846c81f406441c1780c8520ae6897065800e1ce2983c988ef85e08e365197f07059082364b12e0cb001a5f0321786c8522c4b832c0068a5108d90ae44be1780c8520ae5897065800c0f01907607c8078fa1d504207ca914fa03e0320fc221a1c419600303c0646c8de03e578a1d80c84407e5871065800c6c82a0ea17b0d03f3438832c00636514819442110a97c2f01907e110b0e20cb00181e03e0fc607a0cb0019f408207c60640f01f088448a9882b83d201e0321100f90324598720a80f0213ba07d00b51086c41c02c2b819088860106443240f01903e15cac020c880f01908807c8c020c880ca0e09615c3d172fe45c1c02cc1044302d60106460b42201f1b183aa11016a2106864be0b40781901615c221d80419101e03e148607980419186c0d71641c9a903e63523640f857201e0e2066ea83f04a6c8a064371d5016104389c038190221f412960130083230321b82903207e50e20643005b07e5804c020c8f3a0321b20a09064060a010221bd08c3895d4c0207ab2012c233019016105fa4232c0203308c6f100680b80508c3895ea8440170080cc21068701b009644210ae50161061084423df038e3a010de8420d0eeda0cc025900ca0d0283ac80820f41411efc0227508d64028306075214a1084103e60961042901f251805a1100f921081e02207c1294d481e0327761081f330084220323640f01f0a4560108450840f01907e07ca0f98042119df03c064eec2103e6601084597c1f182caa08c1f981081e03e148805580421198e84207c60680f80c07e4bbe0082181e0a85033008ee83203e0fcc77d148194320fe190150a48832c02010c5e01906407c29142084ef9c50321040f852325f0337d02f0320a46832c02010eef80c08732011a2331))) else (if i < 26 then (if i < 24 then (if i < 23 then 0xc3541960030ea1a922e380de7546c9e3541960038d5065800cea819404914310710f4703c86803dd5442066fa034464503e064fa63800e75437168446a0be0c86c83f202d03207c22103e23703c066642210ae74ea1913b03f0b20786c9c2aa0e0fb3200c87c0ae78ab065800d3a8554ec1bcea8d9305576c80a642210329d42ba22ac1960033bf97ce2e45c1c0840f044407d4920790d00703288422222c8c903e1eb0d07c0ee1480f242122100e0650707d0887885065800cefbc5c1c0583e81e0ee365110a0cb0018d98b210b0d6020f81e8fa230707d0ee7746c94ea81941c1742207a30590841ba2f61a0f47d0e6a4297d0cf181a19a002a0097c49150cd001a7443340069750cd001982404864686838dd50860851081e0688a3121818a190f8110d461804291d8e0e22f016a210ae6a30c02148c35219a003084866800ddb4295900961187134293aaee011c231b261b30a40cbf48465852f76118d9206a3ab08c3890211d506508422160cbd58aa1810e07934290020642f07b2874852006258190f268d4b200c85e846f74c1a80c8078bd08c3898148190f6110815407c745900642b9a2fc4508403c03819088778b0643885504e110d914d4e3803c1b86f16884680c5065800e3141960038c5065800e3141960030339d02c8d90a4503c1653b13a842364d1398042119df09d8a53b021842364f139804211c4e601084677f2f9d5caa0fa1081e07e803e07803a6a1b317865823846981cc02108cef81e0b24123b4211b2781cc02108cfa03e81d9540b07604308d103980421183fcaa1881f1f404663be3240f81e00e13f1c06e1bc08e11ac64e4503e01f1c06e1bc08e11a58006e84233bf97c0f059c704e864c23440e6010846325db01f03d03803c6a3be97865823846c81cc02108f22813c700843742334196000c4677c6ce45c706a437023384ec701b8ea8d904664bf08449150cd001a7443340069750cd001a6a43340068a6800211a5543340069090cd001b1845308478a40081e0c21501f980c84303c148906a0c81e19f48be248b6d80c874064148d0658045f1a2999011011a2328190d41e4291314a210c4148c703f341960117c78a43a85e1780fcb6d80c87103c148a1d6210320a44432838fa432084148c7d21b092fddfb6c1741905233df03f140170420ef3200f220cb0086c3b6c8a438cc804a88cc064210790a44cbf32314a2103c1401083f44196010d878a4fa0740a44cbe068178d907e5b8a066fa01e0a454be7140cc42082148d7140ca1941c7d0214320a48b8b0658042921df38a1d42101a0a46b8a8083a86a082148d7160cb008524b8a078190ee2832446360897eefdc5033104210523e36c348383701e90c148f7160cb008524c6c1a81905223b68340c829121081a02409c1f96108194d41481903f341960 else 0x9240260106461ef148190960703c9a013008323cbe1e42f0220ae504406511057206436dc6001a7502817821859044a0c803c0c85e0ae5845065800cc12750bc15c3d859365f7521782c8412c22832c00697c078190bc15cb08a0cb001e290280163b80a0bc720f08a0cb00182203288822103b1a9c0c1d41107c0a2105003cfa0190bc110b08a0cb001e5f352178110660b2104ef1407876032924221a1141960034be03c0c85e0885845065800c0a0784b21482096114196003c418183007d0825cbe0672407b044110c97c2b83d182203215d110442c5936c0a80c80a0ee1442207d044a05a03d0306c03215c221e114196003cbe08807c3c03215cd08a0cb001e5f04403f240190886845065800c0c8090ae1e8997cc16480884845065800c1681430d1dc2c982c341481ea611419600305b8830d0773bf1643582e0fa9cbe6a41e0572071baa0880103b0486044064079d5c90104389c0c80904a1f49066013001e5f04418c038210b075420a20cc026003e3001d804778b200c3d84404417941c53503d0a840121ec21822432888d1240c8073ba0283be200861f41128efa290fa08c2f2233419812c006088038038ee1e42c833046179306604b0019a900f164110750f617820a20cc09600338b0e4358590321ec2904407a089497cea87a046179119a0cc096003cbe1641e6200a4104d06404b001e290281df0d0030bc720e0883d819088090b8a40c8600f60703c98010190f6110877e013008324cbe0642c1c8c40110c0080c8570f24353009804192222432608688a8025f1a2243340068890cd001a2243340068890c9821a224334006888c15004324444866800d11219a003445401148d0ca063043444866800d0ca06a003444866800d11219a00378a8890cd002206a00864688a802061a220320083d84404864337203404b0885844c02010d2fddf432340048443422601008697d0cdc88d012c221a113008043844c02010d112193703444866800d11219a003432026800de29b804207a108d930c903e064fa42103c1c4e7142181e0430840f990c8514f184323304865010d24dc546e8680c83f44607838a5114210ec37838943dc7588a07c320468ec0642c8d9504546e3643d903223703e1242202399088d07d10ca0e99017a2087c3c45832c006866800a8025f107a49207c0f21a00e066fa2234bc50329643b5f444668e9065800c3e81f03c066645dd4467b8b0d80b06f03c1dc6c9d0705e9900651187d345d832c0069882f07d3ba364a9150cd001a8688a180294210f460bef15dc05e0470846c9c3a0d900e0642f4210f470ea179eec211b2503e064eac2103c1c4cc020c880c9d5842078221580419101e03207c2b900f07cc7008c6f07132450548391c0710f864928dc0f81e43406403a230e293e8065072020841c43e1) else (if i < 25 then 0x19d503217d258710f460457540c8790685033808ea8580641e4c0670302d0ae1a022181101944415c89d4327180d60522f03b0b2089203c2c0190fa15cb08a0cb001e20c358193b87d3aa676c03c2c0194ea15cd08a0cb001e5f0339203d822088604406511044202ae311640287d0a21dc11202100f40c0642207d3422832c0060ab8c0050ee1f4330590448845065800e2c842c4186b014580f47d107570d6060ee1f4ee98ea8190bc1103d14350590858830d06b8bc7d108890cf181a22a0097c68890cd001a2243340068890cd001a1930c8186864c12021dc50520843ca220686433720340580885844c02148ec32758d00bc2b96113008523444866800d11219a003c520880c9d58960703c9d148790a430440643da220f250320243307d2422832c0078a4c36380f64845065800e1141960030c28080086b0321ec3c9e114196003be81c4110060a209cc0880c8013e8050e405e0e28b900643904b0f25833019800f1481904400cfa0430bc7203424110194441ec98a411001c700643d99148010321783d9611419600376c0042c0194721ecd08a0cb0018013aa0642f07b2c22832c0078a4111d50bc0703c98110194441e498a4110018960643c99148010321783c9611419600304401c3a8630b20d01185e4422832c00797f148140a4178ee98150010321783c96249860841e43a8440bc7845065800cdb6290961e491278c3000d61ec1f85808808929178c07a0a44bbe066e2db8044865111c1501900f124e2a77c400ec3e82251dfb8b6091c07d04616111a2e2c22832c00877c35858c400fc1d85904480afedb016220f61e817e1a3909845065800cefc4938a0a81fe200b015c3b82255c50ee16011a234ee6b8b08a0cb0021d5b04086a984b0f4602980b0d07a0b0720d08a0c9d51861c418693b8593521ac3307d4e5f3ab86b1003f0b0720e0883d81908809ca1e411019c700c83d98030190f611090198041919c806fc602f07908860320181b8690ae536d01980419265f088064c103cc4015ce8890c9861a22a0097c68890cd001a2243340068890cd001a2243261868890cd001a2230d4010c9111219a003444866800d115004523432609010d1101900c15c3c82732294337560e04b0f26844c02030d14da94320242087b34226010186864eac1c0961e4b089804061a2243340068890cd001a2243272070e78c3000d81ec2607608808928db8c07c07a4b52066e45b6044865111edb0190cc0880487d34228327d076d82c87604688d2c9adb422832c009f1421e06c441803e0790828c0c1db1007c0825845065800edb1a94917203d0230ec88d16da1141960040c29240598600a028c1077c401f556da1141960040441ec0c84404850961242087b0ae503200824869088538b0098041920570440672406808860040642b87 else 0x230f816c3bc77386f0f67203b9220c196003883065800f2a98e6401943b9620c1960034ea1040cdc8442904c1ec20eb6c521401a0234ee8d6c8a53b819097721119e20c196003d6c755118190a17213b9e20c196003cbfc630105a39088cc0dd074194477213b9a20c1960030ea1ac109860ac1642904146b60961c82912efa75b8a08420a214827083ada149c58a00d011a7745c50ee08d3b8584466b8b1060cb00265f0021d4ea85804214820a39006bc8205b3b82fc3472111060cb001a0e970084ea84b0e46c058683585a390505f064ea8d07075b8a09511a77365fc040842d2232dc588306580130d0650ea1613b972f9d5c3402c2d1c83071b901041ba210329041a2020837c34140e42770e270320181b8730ae586f01980419265f16c154e407702a08d11a2e43208328381ba77864786f0198041920410329dd208572e29c041d4ea8410f608e11a0e2eb6caa08c328344ee7833049800f2fe29c04308118500ef08d1066093001e5fe31808e28410b41de11a20cc126003cbf8082d1c804650c38a43a850a409dcc9050cd001a2943261869050cd001a414334006906802291a41a009d469050cd001a4143340061c410dc80828852098efa2908609425dc844678829d6030ec7071838142e4277344160101876a4b420e0837213b9a20a2180c3482866800c17a19390343204a800cefc3930d00810c4108215d10658044b1c1960112c7008e44418ee4832c00258cefc3930c086208410ae70820663bc410ae5883065800c16c196003883065800cc14778823883065800cd487708215c900a3bc4184215caf7dc74021bd0841a1a3bc0203308c6f160127578b1dc12c233071790066012378420d0ef7c20b8e804f561083d3841873084388111bd10412a1e284103261a0107103d1063ba620c39804c021094e28410ea07a20c77344187300980421282180460a3bc412c396010840a90208090e208a20c771bc70820646f4418ee5833025800c2087538a08a3bc413419812c0067140a8750651063b9a0cc096003832025800cc30771bc1048638c30770824082866800c20c394523082866800c20a19a003082866800de284143340088dd03500432443284a800c20c3940c34448678c0d0c98640c3432609010c0c85fbab1051106933a90c11650e07929a90321671c0410f6646f8683d8c110194441ec80642587b0fa4845065800d115004be30440651107923c50021d80ca590f26845065800c11019bba86511143225fa800502f02e0b2089088c0c85e0fa4845065800d2fe208781f4ee9511219a00388b064ea8604381e4c0061c0193aa1eca1d2258190f41e4b17cea8190bd08dee980c9c8c906e31c0220e27c408243887d20220328883893100194041603887d3422832c0061d43561a4978803e9d53c22832c00708a0cb0)) else (if i < 28 then (if i < 27 then 0x86544230cc14841981f8f7186f0cc200e90450642d00a1a1c8381c426105ca1c83906426150e41c83213090710c8434842e4a8720e41909841730702603f24190b413067150e41c8323dc1e990e41c8323dc1e950e41c8320f45c950e41c0560f488720e4191ee0f4b070290b907a44390720c83d172543801e2083d21a930c0bc0391e282f43801c81acd4a1905e43bf7150e41c30c1accf142c00719c54390642c91e2a4100e33e97145cc1c4321e8c8720c9dd0b22e4b7150e41c30c0a8b7142087a482478a169108cb45c54390710cc1931c50b214877145cc1c4320fcb714c305a442084b7150e02f35201cb7152084100e4098f150e0072078173064051032c1901434386185cc190f2531c61809007206500e2842084090cefa1c82461831942800711c54330483d912080711f41728660907929dd1728710cc19824678a168038e10a19024343886609071205a05686468642d05618b943304821a422a1c0b40ac7480c706500e443804a1082123c50b5084109009007121c8390180510fa41c0f002888720e07101444390710c82b014583890805043221c83901805120e1680ca02886da0300a07e43530702d00a201c0c83da20903201c882303815801c4120f683207001c41286403910463d83e00388241ec1be20803201c0c910463d80e419882130a3da0ca12882028a32c0e41a832130a0720d07109841960720d41900651960720d41909851960720d1c801451970642c04c20cb83214005100e4190ce0b880720d41905a00ca0c80e003182d8321b801901681c83475401941901c006305a0720d41901450390642602d202d8350650900a2c1981c00c12120cc0e04800c906607024006483286607024006583303812003241981c00c12120cc0e048028906607186048130a0720c88980c00ca07044c0639000ca0720307100644320bc1580320580ac00c60720c88980c00cb06444865006483222428003201c83222603003281c30c00c06100e1860980308048c300c014435263a2761a03c1643bc7742410f62c1d1dce4648042104389f0d06a4a07543b9620c1960030828840ca7548215cc1075b42930d1401a0234ee8d6c1600c87c0ae5883065800f5b61ac1c160eaa7732414334006864c32061cf4b900a410a410686b0c8dc178730ae58829d6148d20a19a0033521b8e44500825a23b9e20b008ea3882c023a8f2feb60e312c5e05904708d01075b62930c140118344ee8883065800c3dba9c5263ac361a0a01d53ba620c19600306f0390cc237ab1dccf7de402581d1dd191820c29c041d43d8de04708d1ad8e46480681b811a773c41832c00797f8c186c041042d0778468883065800f5b06ec900853bc233031832c0061b83ac58c349dcb97f0105a3aa08ca9050cd001a4143340069050cd001a41453084610603 else 0xcc0e84260421ba108c218420620861095e2c210d20c4908418869182e84286418900f219c3401c906a0c81e00e43be07a0d04300e58350640f01d20210c404c61a510c190dc04ca07838c3607e403d0661b0bc03a517807a0cc3607e51788840f41941d0d8099c6c5c50e207835146c5c50f50a40396e280706407897140381e06441b17160c86e026510d3201083144252d0188138e0c82781c01c81c4370071a190560c403920c82781c01c80ac18827181e0e2014607a0f0c9832014a078028711bc50c007cee87c28c98327740f877281f0868643012db1820c81800f96db2198ec1580f943b84303e38ec6082182d03e5b6c07c300214425b6d1d82922103e541c0fc0f87721dfb6d1d837a2103e64326083003f20bc03e0782083f28d878a8660101e07e07ce07d0c82702a0fca0ba0c86e04a48970640f852244b1930642901f28d98970640f85228d98968640f8442c4b8321480f9225c1941c07c291625a218328380f85730c98321781d81f2c388320ec0f921c41907607c90e20c83b03e48710640f83f22218320f80f844281f0e20b869140fc1905c364a0b80fc1918d905c07e0c9016a1903e1c480b80fc191c1944207c29120ca0e44207c1f941702d06208510940f41905c07c05941701f03d0642080b341905a02c2b910cc1904e83805943741900a30d30840f81624211920583d901f42103e05880fa1081f02c484207c0b0c1721984207c0b161081603e15c80fa1081603e110a0ba1081603e48322240f860241911207c1c900f07100f008807d0c82b05a01ca07844807082403d06444c0203a503d06444807804544207a0c88900e054d4620101f00a42a612c0f805251880407c02928c40203e01480ba8c01f022094a77ce287b08e408e904487023883da1c44230f611c586920883521c05434381a8321d5224105428381f47b871206e44220d4f150e02a261a48220f81c42b0c5cc1c0f4158810d0e4190fa3dca1062087a19f44390642082b286278a8700790e2a1c83808610952080f11dd1730710c87d286e01e20dc086108d0e41c432158810e0e2191ee1f4a5a10e41c056084a194078807a41104e38a08407902721c01e3842138108cef9c50f818c89040788fa0b90f81e481680788e2a1c0f81c487145cc1c43210d21182800f11c843803c677e1b41c4321ec7b9a10a1907c386c8720e2191ee1c4c2e61b21c8388642b190e41c0840ac80281083e183135208407903700f11a98420c41090d48710de084816807883d86f12410f223e81e4378b921dd1728720e21983260421ba108d208410f4378a168078c18814042343803c477cc306100e40f601c41ec321c81a4100e23bb0710c87d1ee50c2f150e00721df0561850c910e41c30c19088720e2190ac43be10e0e2190fa3dcc8720e21930c0aca19403881) else (if i < 29 then 0xc2122205430fa0a8488a1141908644447d02102a23c508488815103d02b0f238441f4330c30bc544401c888a111860c844450890c85624220fa198688a1102b0cc40c2ed9110072222845064289111422832144888a1121908640bc01c488a114190f2478a0f11100722228450643c9111422432158888a1102b0f2407801c46a4c302f00e478a0bd1100721a94321ec1791114224326183d95e285800e34441643d8de282f44401c9715114224321e4a88a0c9dd0b24b8a88a11186054576c888ee82f05454440bc0387b23b6444774178072bc505e88803902b8244326180595114220e2050888a11014086444508a0301421df3041800190303b644400c88883206078a774aed83b003187d0ee7746181db22200643be8643004325b6445088c10642db64450890c8562a220ee10c688a1121930410ca181db22200640f209d0c98201454441e43006421c8b6d0890c84c2a220ee1e46f16db2228448660c9a1120643210c877d1142240c1e4a88a014190ae4096ed911003222284418c2b902f00312228450642b911142283215c888a11219088409600c48882906618570a40f470882c8571dc538a88a11041006644508a0c83b22228450641d91114228320ec888a1141907648441301d8de2a228450641d941f814076376c0b511003222284418c1711114228320b890883d02e1a228450641711114223040a88f1416a22006444508a0c82e221904e02870882602e1c2207a0b868882b82d05444450880a02e222205a00c22111141980401480500580519863040240191db22201200c818d0c8091a2243302431902580312224330243d901e00312224330243c90eea198321788f15110090064056864048d112198121c4888a0482b43244448660485622224330242191112198120ac8888048070cc43700f0038de2a220126080395db2220126180194259c80063444024c3003222200b008389111422804014888a110050f6444508838805222284401433101380900a3098014288cd4a228450082b940500b00a343c864432402a190f640330640f0c3502a106a0f875461a8150a3507d0e236481b91089e286ac34376c07c150c0c8c903c30f81c42b0e2a8c90f4158810815083e82a10438321f46c90351f40840a887d02120e442478a10b0d0cfa4190f45001594313c501e30c4716900210f650c403c5188ee8c94321f4a1b807883702184238c495464a190ac58c49090c843206e0565a061880789db01f01e31921f210852227489c324294212a6a89c366108522c4e19290a10852283e06e207c0dc477e10c0e1920fc3d98fa03e06e30dc0fe108d2a8c981c0fe10941f9a96300c61094d4c2131c1a418961086e0d230d26a61083104253be6a61098e0de1a4d0843485a187b8421f06c92108310d233e89d21086f21dd4ba325 else 0xf67143a847224108e20f6905108c3d847106a4820a861b91088353c54820a891d4313c548203cb1d43700f1c754831050c8562c752d09062082b04268ea194078c271c504203c81392080f185a01e238a9043e071205001e2390904238c189a904203c81b807882d00f107b0de20421ba108de285a01e346e0c40a021224101e23be61830807207b00e20c2f1520807202b4321843a9120c41432158890620a1930c0aca194038833052106f0cc24831050c87122753909060c85129c84830642890d498605e01c8f152082f00e478a160038ce2a418321648bd2e2a4105e6181519e285a44232d171520c418329d4c7142c8521dc530c169108212af4b8a904179a900e678a904038d3aa4186e61a0c814318e30c048039032807105000e238a8660907b23c50b401c70851b8121a4143304838910c85a0ac3482168158e9018e0ca01c8f142d421042402a01c490620a1930c1c4a90620a1905644ea906209862d0050c906209a930c050a72029047184183312c2b902c8570a430af06509052204105a00c671420c418320b8a0c416821442478a1041680324410980b86f1420c4105448830650902e2041882028c302e2c390a40f461061c81107a40831061cc0204b084c10620c3935300812c213c3907a05461061c825842058af1420c3904a61a108163c3946f084128152c3930d0840b0252bc5082024019020a1981215881045e2198120aca05401885e21981214881045e219833024af1420c4100e46406080a807222208e244411c4ed911047186a4440a86888350643aa40d4888150e1107d0e230d4f151102a206a76c88815103e0630ac38441e82b)))))
def lev11 : Packing := (1943,4,7,0,0,17,0,dataBits11)
def idxBits12 (i : Nat) : Nat := 0xe27058000000084d50d87974c77279b03c7ed92a45000000185000f70e6f982635160246000f0e66500000065ff4aa94e7bf4450923aa6a295918d89e6947359140cc19816a9074d11035765a36803b91c66316634e04f58fd1f000b81014953378c39a7f852a8c276731000a9302df4852a23715d520f3d886000000451c13c4c00000000085cd36711a42000141d5b000a0a904000d72271a7dc8eb8a000f15759583000000001e56726c1eb2b000464000b7a805d4908b12200008db3453c00063e32ee5e56701de2f53fb6b60f43307ce4b402000c5472111b76d46274300046e80d000000000b17000b88d1ab25d47e40d8062c755a0ba29d06030532075f23f0866c000407038f00000000000961212324028000000292419e8e0c10d0a682061c489a51e2840f24240100088b80081020b0c00301081c107
def dataBits12 (i : Nat) : Nat := (if i < 1 then 0xf39acd672bec8b71bac4f70a2c10efd0bcd6ea4b826daab4deca6afdeba2ac6ea76a8ae99aa4c6896a1067ba9d966e89a9e62a966653a92f647c8f863788c1626a878e17a83f60808035f867bd5e787815dd87545d0671fdc206e15b3a6b45a4a673593c62d587e60cd7a25d0d6e459c55f45605518530d4644f753744c2d2ac48951c6459d0ea42550363f5cf8c3cb4f003b4ce883994de836ecd3e3444cbc3124c122f94bb82e04b042b5ca6428dc9c4263491a22c48481ff47b21d4c7261af4686189c5dc15a452813c44b0111c41a0f143980dd432a0adc28a08ac1fe074419004c40fa02e4078008c000dff61d965037fd8565940dff5d5965037fe5565940dff60d965037fd7365940dff54d965037fd8265940dff5c9965037fd5265940dff149965037fd3265940dff889965037fd7165940dff545965037fd3165940dff485965037fe8864d40dff61d935037fd8664d40dff5d9935037fd8564d40dff215935037fd7564d40dff595935037fe5564d40dff609935037fc8264d40dff5c9935037fd6264d40dff549935037fc5264d40dff889935037fd8164d40dff205935037fd7164d40dff585935037fd5164d40dff145935037fd2164d40dff085935037fe1164d40dff2a1925037fe8864940dff61d925037fd8664940dff5d9925037fca564940dff615925037fc8564940dff5d5925037fd6564940dff955925037fd8364940dff5cd925037fd6364940dff54d925037fd8264940dff589925037fd5264940dff4c9925037fca164940dff605925037fc8164940dff5c5925037fd6164940dff545925037fc5164940dff4c5925037fd2164940dff845925037fe8864540dff61d915037fd8664540dff5d9915037fd8564540dff215915037fd7564540dff595915037fe5564540dff60d915037fd7364540dff58d915037fd5364540dff609915037fc8264540dff5c9915037fd6264540dff549915037fc5264540dff4c9915037fe2264540dff605915037fd7164540dff545915037fd3164540dff485915027feaa659409ff6a1965033fe88659409ff69d965035fe77659409ff6959650377e5565940dbf58d965037de3365940dfb889965037bd4165940dfd845965027feaa64d409ff6a1935033fe8864d409ff69d935035fe7764d409ff699935036fe6664d409ff6959350377e5564d40dfb889935037f61164d409ffaa9925027fda864940cffa21925027fda764940d7f9dd925027fda664940dbf999925027fda564940ddf955925037bd54649409ff68d925037de3364940dfb889925037bd4164940dfd845925037f930649409ffaa9915027fda864540cffa21915027fda764540d7f9dd915027fda664540dbf999915027fda564540ddf955915027fda364540df78cd915027fda264540dfb889915037f61164540 else (if i < 2 then 0x4178c886940149cefcbec741cdc4706c0aa0f1910d07ec77e5f6a6296e238248500fcc808d62b842dc03c46da0e75655078217d077b221a88c4107db228dc0c8aeef8a4209ddf07a0e1dc597544b0841f104c8868526cbf073e92a832225901f882977c59b2245838770b72007821754418681f111f228e2370320b3aa209e5f6a5f4954c8f143e07c3f08d4d4c52c741c3bbe80f9122f03c644341fb5df97e19839d59552007c1e15c5210591b35314b1c38b912478a310390d43911be8e1d4747d04e08459755c81061a88d53905a0cf8b903e82095f4065d5723207744138ea2cc6cc33e924640108dcea8830d0e320ba1c97465c8019754577d0324c1d3a3900c8b110c3520baa977c5910c370d986087203ddd51056efc6cc730c388dd2408310bab20864c7d2366a65572065f14415a2b808d6efc533a170ea8a0e438b5c046a77c366a586774f70844143bf1b30c370b020bab5c04691d4498d9a9954217d0651061a72223905b1b0d40c8e2050a110c34fa390a8a67475419130508861a905c853be2486eea843901ee6f082977dd57167416450084410ca1a72223905a38ce9900a00cc381eb901925df6a6299d0b8141c8ae0234bbed4c52c74e8054342808311c82e431a9639c8c821a3d84c1050efb1cc364001baae299620a5df1658e7232086857130414bbed4b901209810882777c49639d5c821a00ccb1053e28ea108824163c51dc23245307491e2e410d0ee708c7716472fbab5b4530739025e410d4eea9c82c121d508c7724be2cd6d07404800b10d4eeeac4720b00ef14231dc92fd6d14c05245bb3b846897eb6839001644b86a777222390560178a3b8422097c5c80771049e2f6c0c84440a45ef15f408ca3ac52804911c78b0cf6d1044434434c1dbb608c5924bf14baa2f391db43310435112a6b163c508c7724bf14c91113e9e2c350cb6d10082b17c5eed9d508cb2f8b2804702c445db433103ab0d2e5f4005917a22eda19881c8869514a003bc9111435e2c3310082a1243706a1aedac808ce14c34070bcfa590119c7583900954767d2c88861a48eddb0b211925f8a60e179d5eda1a3222354d4010ab640463b965f83a557d21a502c888c414c343b0bbdb3ab64046797c599160e40238ed832b22218696ea853db0656404661a85eedac808cb2fcab1c76d64046697e2906a0e1781eeda213221a50056408211920e400779561ab222310500776d640464f142110461b4342c78afa082119c758da2940062923c5869df88e4158be208462c92299d1d5141c886a2354e414f8a3a8422091f4f172010482fc34243aa2084661660e402741621a7562390522f8b1e28821196299d248f16b808cc2fc342ab902084664027416450869c888e41478b900823e8979bce4ff8b8e1677f0de1f71eda875fcd64f520d267430cfb else 0x418a422c8050755537221a1dd50730c388d42c045903ab0d0eea97dc8ada0e80b200dc589de1a905d563bf20b1cc3404374915b083903ab3b864d6a629189c892168f14231dd32fc53010eeea8a0e44ee6e846a77d868086e16041ad9d59dc2350c220b53148a011640e44343baa5f756b68a60ec803712e7786a4172192f892e2d6cc741d013aa3a8b020b910d4ef11c83097e45ad819c80150de777203253bf2fb5314c045c0a15b3913b846b77eb66a629638658684b1067788e41721a6f3539031c01390e28ae3b882a639c8c80571dc41335201391e284a108ee20a18e7572037877104cd4c5311432c139124470388443dbe90d0f2343e2206586608751785975422881f454e1a1edd14c45240323a78b0d0f220c40fa2e5f8a5f4065d5179c8864418821a77583a8d42cb0cc14440c8ec2c044fa3ab1043438be488e02e065f41a1d51e4324cbf114700cb91db0b02bc410d3aab16422889861d64810821869f47544150220111eefcbf11432c3490dc47038845103aa22064e1d5df6a47b184596e2220645e08a207221a1e5f14c440c8bc38c34fa39034265f8a622065d5ed85e1ee1a881c85bbed4845110ea2c8422f440db39020c343cb9df97dd5125c5089b88e22208458eda190ca207221a8cbf100322f088e40f21921df97da98a6196e2228802217a1a1e5c86be8db35314844e44900c8ef1178a344350cc4020c22992057064681ec413bbed4845110ee2c8430d096e438a20c402bba5f8a622920197d3c5112201054ef8b216b0c3b8ae114442c0430d3aa20c40223e5f8881916071881d51050efb52110ee2cc44108970d432e444020b65f0b858880197207b1050efcbed4c530cb9124444114402b882c1c7c507c217d01e331d07304eacaa3883c3b59110c34fa3075125a907a0e0707615423365f48861a321d074aa0c8e820d9110c34fa265f8a60e7d019175d5106213221a77583883e22042ea83c61d4599160e60a3875421c806a079f4b221a1c5f22c1d430ed90032ea8aefa064a97e0e8e01915c55eda213221a75562cc8b070eaeae400f08410c34fa08364280223ddf916861b9b88e12007871885d5110326b52c14aa64470b40c4fa59011a9df97da98a5828e1dd138d9148c808d92fb52073052a990fa07cdb5901f846c77e45038866e2381bbb6756c808d63ab5314b1d07304258e8fa03c644341fb65f2f1a98a41e63a0e071f))
def lev12 : Packing := (150,3,7,0,0,14,0,dataBits12)
def idxBits13 (i : Nat) : Nat := 0x1fca9d8
def dataBits13 (i : Nat) : Nat := 0x5f5b0a41c022471434771190565f149207022e2ed832200d28be0e2a8e36cc810869029071d091c50d08c828f99a4d00bfecb2817fd93502ffb24a05ff64540
def lev13 : Packing := (4,2,7,0,0,8,0,dataBits13)
def mixedLevels : Nat → Packing
  | 8 => lev8
  | 9 => lev9
  | 10 => lev10
  | 11 => lev11
  | 12 => lev12
  | 13 => lev13
  | _ => emptyPacking
def mixedIndex : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 4 0 6 2 0 idxBits8
  | 10 => lookupWord 45 188 7 12 8 0 idxBits9
  | 11 => lookupWord 442 2141 9 15 11 0 idxBits10
  | 12 => lookupWord 487 2375 8 15 11 0 idxBits11
  | 13 => lookupWord 40 187 7 12 8 0 idxBits12
  | 14 => lookupWord 2 5 2 6 2 0 idxBits13
  | _ => fun _ => none
def mixedForest : Forest :=
  ⟨511,13,dead.samples,(IndexTree.fork 126 deadcolumns (IndexTree.leaf [(0,0,511,0,15)])),(Array.mk [[]]),mixedLevels,mixedIndex⟩

def fullKnown := (511,15) :: known383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem fullKnown_ok : Known fullKnown := by
  intro e he
  rcases List.mem_cons.mp he with h | h
  · subst e
    exact lower_forest (g:=dead) (i:=0) (hints:=13438755108) (before_sound known383 valid383)
      geomdead tablesdead (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact valid383 e h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mixedGeometry : graphValid mixedForest (boundsBefore fullKnown) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk8_0 : block mixedForest 8 0 3 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layer8 : block mixedForest 8 0 3 = true := chunk8_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk9_0 : block mixedForest 9 0 29 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk9_29 : block mixedForest 9 29 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk9_77 : block mixedForest 9 77 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk9_125 : block mixedForest 9 125 40 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layer9 : block mixedForest 9 0 165 = true := (@block_merge mixedForest 9 0 77 88 (@block_merge mixedForest 9 0 29 48 chunk9_0 chunk9_29) (@block_merge mixedForest 9 77 48 40 chunk9_77 chunk9_125))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_0 : block mixedForest 10 0 6 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_6 : block mixedForest 10 6 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_54 : block mixedForest 10 54 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_102 : block mixedForest 10 102 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_150 : block mixedForest 10 150 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_198 : block mixedForest 10 198 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_246 : block mixedForest 10 246 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_294 : block mixedForest 10 294 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_342 : block mixedForest 10 342 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_390 : block mixedForest 10 390 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_438 : block mixedForest 10 438 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_486 : block mixedForest 10 486 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_534 : block mixedForest 10 534 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_582 : block mixedForest 10 582 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_630 : block mixedForest 10 630 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_678 : block mixedForest 10 678 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_726 : block mixedForest 10 726 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_774 : block mixedForest 10 774 19 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_793 : block mixedForest 10 793 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_841 : block mixedForest 10 841 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_889 : block mixedForest 10 889 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_937 : block mixedForest 10 937 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_985 : block mixedForest 10 985 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_1033 : block mixedForest 10 1033 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_1081 : block mixedForest 10 1081 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_1129 : block mixedForest 10 1129 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_1177 : block mixedForest 10 1177 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_1225 : block mixedForest 10 1225 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_1273 : block mixedForest 10 1273 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_1321 : block mixedForest 10 1321 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_1369 : block mixedForest 10 1369 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_1417 : block mixedForest 10 1417 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_1465 : block mixedForest 10 1465 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_1513 : block mixedForest 10 1513 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_1561 : block mixedForest 10 1561 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_1609 : block mixedForest 10 1609 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_1657 : block mixedForest 10 1657 48 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk10_1705 : block mixedForest 10 1705 46 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layer10 : block mixedForest 10 0 1751 = true := (@block_merge mixedForest 10 0 841 910 (@block_merge mixedForest 10 0 390 451 (@block_merge mixedForest 10 0 150 240 (@block_merge mixedForest 10 0 54 96 (@block_merge mixedForest 10 0 6 48 chunk10_0 chunk10_6) (@block_merge mixedForest 10 54 48 48 chunk10_54 chunk10_102)) (@block_merge mixedForest 10 150 96 144 (@block_merge mixedForest 10 150 48 48 chunk10_150 chunk10_198) (@block_merge mixedForest 10 246 48 96 chunk10_246 (@block_merge mixedForest 10 294 48 48 chunk10_294 chunk10_342)))) (@block_merge mixedForest 10 390 240 211 (@block_merge mixedForest 10 390 96 144 (@block_merge mixedForest 10 390 48 48 chunk10_390 chunk10_438) (@block_merge mixedForest 10 486 48 96 chunk10_486 (@block_merge mixedForest 10 534 48 48 chunk10_534 chunk10_582))) (@block_merge mixedForest 10 630 96 115 (@block_merge mixedForest 10 630 48 48 chunk10_630 chunk10_678) (@block_merge mixedForest 10 726 48 67 chunk10_726 (@block_merge mixedForest 10 774 19 48 chunk10_774 chunk10_793))))) (@block_merge mixedForest 10 841 432 478 (@block_merge mixedForest 10 841 192 240 (@block_merge mixedForest 10 841 96 96 (@block_merge mixedForest 10 841 48 48 chunk10_841 chunk10_889) (@block_merge mixedForest 10 937 48 48 chunk10_937 chunk10_985)) (@block_merge mixedForest 10 1033 96 144 (@block_merge mixedForest 10 1033 48 48 chunk10_1033 chunk10_1081) (@block_merge mixedForest 10 1129 48 96 chunk10_1129 (@block_merge mixedForest 10 1177 48 48 chunk10_1177 chunk10_1225)))) (@block_merge mixedForest 10 1273 240 238 (@block_merge mixedForest 10 1273 96 144 (@block_merge mixedForest 10 1273 48 48 chunk10_1273 chunk10_1321) (@block_merge mixedForest 10 1369 48 96 chunk10_1369 (@block_merge mixedForest 10 1417 48 48 chunk10_1417 chunk10_1465))) (@block_merge mixedForest 10 1513 96 142 (@block_merge mixedForest 10 1513 48 48 chunk10_1513 chunk10_1561) (@block_merge mixedForest 10 1609 48 94 chunk10_1609 (@block_merge mixedForest 10 1657 48 46 chunk10_1657 chunk10_1705))))))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_0 : block mixedForest 11 0 1 = true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1 : block mixedForest 11 1 48 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_49 : block mixedForest 11 49 48 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_97 : block mixedForest 11 97 48 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_145 : block mixedForest 11 145 48 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_193 : block mixedForest 11 193 48 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_241 : block mixedForest 11 241 2 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_243 : block mixedForest 11 243 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_291 : block mixedForest 11 291 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_339 : block mixedForest 11 339 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_387 : block mixedForest 11 387 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_435 : block mixedForest 11 435 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_483 : block mixedForest 11 483 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_531 : block mixedForest 11 531 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_579 : block mixedForest 11 579 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_627 : block mixedForest 11 627 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_675 : block mixedForest 11 675 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_723 : block mixedForest 11 723 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_771 : block mixedForest 11 771 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_819 : block mixedForest 11 819 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_867 : block mixedForest 11 867 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_915 : block mixedForest 11 915 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_963 : block mixedForest 11 963 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1011 : block mixedForest 11 1011 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1059 : block mixedForest 11 1059 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1107 : block mixedForest 11 1107 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1155 : block mixedForest 11 1155 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1203 : block mixedForest 11 1203 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1251 : block mixedForest 11 1251 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1299 : block mixedForest 11 1299 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1347 : block mixedForest 11 1347 28 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1375 : block mixedForest 11 1375 48 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1423 : block mixedForest 11 1423 48 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1471 : block mixedForest 11 1471 48 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1519 : block mixedForest 11 1519 48 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1567 : block mixedForest 11 1567 48 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1615 : block mixedForest 11 1615 48 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1663 : block mixedForest 11 1663 48 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1711 : block mixedForest 11 1711 48 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1759 : block mixedForest 11 1759 48 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1807 : block mixedForest 11 1807 48 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1855 : block mixedForest 11 1855 48 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk11_1903 : block mixedForest 11 1903 40 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layer11 : block mixedForest 11 0 1943 = true := (@block_merge mixedForest 11 0 915 1028 (@block_merge mixedForest 11 0 387 528 (@block_merge mixedForest 11 0 193 194 (@block_merge mixedForest 11 0 49 144 (@block_merge mixedForest 11 0 1 48 chunk11_0 chunk11_1) (@block_merge mixedForest 11 49 48 96 chunk11_49 (@block_merge mixedForest 11 97 48 48 chunk11_97 chunk11_145))) (@block_merge mixedForest 11 193 50 144 (@block_merge mixedForest 11 193 48 2 chunk11_193 chunk11_241) (@block_merge mixedForest 11 243 48 96 chunk11_243 (@block_merge mixedForest 11 291 48 48 chunk11_291 chunk11_339)))) (@block_merge mixedForest 11 387 240 288 (@block_merge mixedForest 11 387 96 144 (@block_merge mixedForest 11 387 48 48 chunk11_387 chunk11_435) (@block_merge mixedForest 11 483 48 96 chunk11_483 (@block_merge mixedForest 11 531 48 48 chunk11_531 chunk11_579))) (@block_merge mixedForest 11 627 144 144 (@block_merge mixedForest 11 627 48 96 chunk11_627 (@block_merge mixedForest 11 675 48 48 chunk11_675 chunk11_723)) (@block_merge mixedForest 11 771 48 96 chunk11_771 (@block_merge mixedForest 11 819 48 48 chunk11_819 chunk11_867))))) (@block_merge mixedForest 11 915 508 520 (@block_merge mixedForest 11 915 240 268 (@block_merge mixedForest 11 915 96 144 (@block_merge mixedForest 11 915 48 48 chunk11_915 chunk11_963) (@block_merge mixedForest 11 1011 48 96 chunk11_1011 (@block_merge mixedForest 11 1059 48 48 chunk11_1059 chunk11_1107))) (@block_merge mixedForest 11 1155 144 124 (@block_merge mixedForest 11 1155 48 96 chunk11_1155 (@block_merge mixedForest 11 1203 48 48 chunk11_1203 chunk11_1251)) (@block_merge mixedForest 11 1299 48 76 chunk11_1299 (@block_merge mixedForest 11 1347 28 48 chunk11_1347 chunk11_1375)))) (@block_merge mixedForest 11 1423 240 280 (@block_merge mixedForest 11 1423 96 144 (@block_merge mixedForest 11 1423 48 48 chunk11_1423 chunk11_1471) (@block_merge mixedForest 11 1519 48 96 chunk11_1519 (@block_merge mixedForest 11 1567 48 48 chunk11_1567 chunk11_1615))) (@block_merge mixedForest 11 1663 144 136 (@block_merge mixedForest 11 1663 48 96 chunk11_1663 (@block_merge mixedForest 11 1711 48 48 chunk11_1711 chunk11_1759)) (@block_merge mixedForest 11 1807 48 88 chunk11_1807 (@block_merge mixedForest 11 1855 48 40 chunk11_1855 chunk11_1903))))))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk12_0 : block mixedForest 12 0 48 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk12_48 : block mixedForest 12 48 5 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk12_53 : block mixedForest 12 53 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk12_101 : block mixedForest 12 101 48 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk12_149 : block mixedForest 12 149 1 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layer12 : block mixedForest 12 0 150 = true := (@block_merge mixedForest 12 0 53 97 (@block_merge mixedForest 12 0 48 5 chunk12_0 chunk12_48) (@block_merge mixedForest 12 53 48 49 chunk12_53 (@block_merge mixedForest 12 101 48 1 chunk12_101 chunk12_149)))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem chunk13_0 : block mixedForest 13 0 4 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layer13 : block mixedForest 13 0 4 = true := chunk13_0
theorem mixedTables : checkedTables mixedForest 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mixedForest 0 0 0 = true)
  · exact (rfl : block mixedForest 1 0 0 = true)
  · exact (rfl : block mixedForest 2 0 0 = true)
  · exact (rfl : block mixedForest 3 0 0 = true)
  · exact (rfl : block mixedForest 4 0 0 = true)
  · exact (rfl : block mixedForest 5 0 0 = true)
  · exact (rfl : block mixedForest 6 0 0 = true)
  · exact (rfl : block mixedForest 7 0 0 = true)
  · exact layer8
  · exact layer9
  · exact layer10
  · exact layer11
  · exact layer12
  · exact layer13
def tripleWire (i : Fin 9) : Sig :=
  bin true (bin true (inputs.getD 0 zero) (inputs.getD 4 zero)) (inputs.getD i.val zero)

def tripleFront (i : Fin 9) := inputs ++ [tripleWire i]

def rowWitnesses (offsets : List (Row × Row)) := inputs.zip offsets

lemma triple_lower (tabs : checkedTables mixedForest 13) (i : Fin 9) (idx : Nat) (rows : List (Row × Row))
    (indexOK : indexedRoot mixedForest 13 idx (tripleFront i) = true)
    (diffs : checkEssential graph (tripleFront i) (rowWitnesses rows) = true)
    (allInputs : (rowWitnesses rows).map Prod.fst = inputs)
    (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C) (size : C.size ≤ 13)
    (eval : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [false, x 0 || x 4 || x i]) = edge x) : False := by
  let ws := inputs ++ [zero, tripleWire i]
  have equality : (execute C.gates ws).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates ws).getD C.output zero) = bit r graph
    rw [← b_read, execute_bits _ _ _ (fun g hg => (fan g hg).1)]
    change C.eval (ws.map (bit r)) = bit r graph
    have bits : ws.map (bit r) =
        List.ofFn (sample r) ++ [false, sample r 0 || sample r 4 || sample r i] := by
      rw [sampled]
      simp [ws,tripleWire,bit_zero,bit_bin,sample]
    rw [bits,edge_table,eval]
  have hit := get_rep (execute C.gates ws) C.output
  rw [equality] at hit
  obtain ⟨k,t,S,len,run,hs⟩ := extract C.gates ws fan graph_proper
    (hit.resolve_right (fun hp => hp graph_proper))
  have bound : k ≤ 13 := len.trans size
  have front : ∀ a ∈ S, a ∈ tripleFront i := by
    intro a ha
    have inWs := hs a ha
    rcases (show a ∈ inputs ∨ a = zero ∨ a = tripleWire i by simpa [ws] using inWs) with hm | eq | eq
    · exact List.mem_append_left _ hm
    · exact False.elim ((live_proper run a ha).1 eq)
    · exact List.mem_append_right _ (List.mem_singleton.mpr eq)
  have required : ∀ a ∈ inputs, a ∈ S := by
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok diffs a (List.mem_toFinset.mpr (allInputs ▸ ha))
    exact raw_required run (tripleFront i) a front r s hd iso
  by_cases htr : tripleWire i ∈ S
  · have all : S = (tripleFront i).toFinset := by
      ext a
      rw [List.mem_toFinset]
      refine ⟨front a,?_⟩
      intro ha
      rcases List.mem_append.mp ha with hm | hm
      · exact required a hm
      · exact List.mem_singleton.mp hm ▸ htr
    have cut := root_index (before_sound fullKnown fullKnown_ok) mixedGeometry tabs
      (k:=13) (by decide) indexOK
    have target : targetOf mixedForest = graph := by decide +kernel
    rw [target] at cut
    exact cut k t bound (all ▸ run)
  · have all : S = inputs.toFinset := by
      ext a
      rw [List.mem_toFinset]
      refine ⟨?_,required a⟩
      intro ha
      apply (List.mem_append.mp (front a ha)).resolve_right
      exact fun hm => htr (List.mem_singleton.mp hm ▸ ha)
    exact dead_start (before_sound known383 valid383) geomdead tablesdead k t
      (by omega) (all ▸ run)

end PEqualNP.Outside.L_meta_3563

theorem PEqualNP.Outside.L_meta_3563 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : Fin (9 : ℕ)), x2 = (1 : Fin (9 : ℕ)) ∨ x2 = (2 : Fin (9 : ℕ)) ∨ x2 = (3 : Fin (9 : ℕ)) ∨ x2 = (6 : Fin (9 : ℕ)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x7 ++ [Bool.false, x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) || x7 x2]) = x1 x7) → False := by
  intro f i hi C fan size computes
  rcases hi with rfl | rfl | rfl | rfl
  · exact PEqualNP.Outside.L_meta_3563.triple_lower PEqualNP.Outside.L_meta_3563.mixedTables 1 0 [(2,3),(1,3),(2,6),(4,12),(1,17),(1,33),(2,66),(4,132),(8,264)]
      (by decide +kernel) (by decide +kernel) (by decide +kernel) C fan size computes
  · exact PEqualNP.Outside.L_meta_3563.triple_lower PEqualNP.Outside.L_meta_3563.mixedTables 2 1 [(16,17),(1,3),(9,13),(4,12),(1,17),(1,33),(2,66),(4,132),(8,264)]
      (by decide +kernel) (by decide +kernel) (by decide +kernel) C fan size computes
  · exact PEqualNP.Outside.L_meta_3563.triple_lower PEqualNP.Outside.L_meta_3563.mixedTables 3 2 [(10,11),(1,3),(2,6),(5,13),(1,17),(1,33),(2,66),(4,132),(8,264)]
      (by decide +kernel) (by decide +kernel) (by decide +kernel) C fan size computes
  · exact PEqualNP.Outside.L_meta_3563.triple_lower PEqualNP.Outside.L_meta_3563.mixedTables 6 3 [(16,17),(1,3),(2,6),(4,12),(1,17),(1,33),(18,82),(4,132),(8,264)]
      (by decide +kernel) (by decide +kernel) (by decide +kernel) C fan size computes
