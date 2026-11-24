import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3634

-- The live-wire argument and the lower bounds on induced subgraphs follow L_meta_1667.
-- Each of the 512 bits records the value on one assignment to the nine vertices.
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
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

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
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (IndexTree.leaf [])
def g15autos : Array (List Nat) := #[[],[33,48]]
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
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (IndexTree.fork 2 (IndexTree.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (IndexTree.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (IndexTree.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (IndexTree.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (IndexTree.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (IndexTree.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (IndexTree.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
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
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (IndexTree.fork 4 (IndexTree.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (IndexTree.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (IndexTree.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
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
def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (IndexTree.fork 19 (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (IndexTree.fork 2 (IndexTree.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (IndexTree.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (IndexTree.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (IndexTree.fork 2 (IndexTree.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (IndexTree.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (IndexTree.fork 2 (IndexTree.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (IndexTree.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (IndexTree.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (IndexTree.fork 2 (IndexTree.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (IndexTree.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
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
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (IndexTree.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (IndexTree.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
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
def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (IndexTree.fork 29 (IndexTree.fork 14 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (IndexTree.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (IndexTree.fork 3 (IndexTree.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (IndexTree.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (IndexTree.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (IndexTree.fork 4 (IndexTree.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (IndexTree.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (IndexTree.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (IndexTree.fork 4 (IndexTree.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (IndexTree.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (IndexTree.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (IndexTree.fork 4 (IndexTree.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (IndexTree.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
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
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (IndexTree.fork 63 (IndexTree.fork 31 (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (IndexTree.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (IndexTree.fork 4 (IndexTree.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (IndexTree.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (IndexTree.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (IndexTree.fork 4 (IndexTree.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (IndexTree.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (IndexTree.fork 16 (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (IndexTree.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (IndexTree.fork 4 (IndexTree.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (IndexTree.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (IndexTree.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (IndexTree.fork 4 (IndexTree.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (IndexTree.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (IndexTree.fork 31 (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (IndexTree.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (IndexTree.fork 4 (IndexTree.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (IndexTree.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (IndexTree.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (IndexTree.fork 4 (IndexTree.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (IndexTree.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (IndexTree.fork 16 (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (IndexTree.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (IndexTree.fork 4 (IndexTree.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (IndexTree.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (IndexTree.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (IndexTree.fork 4 (IndexTree.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (IndexTree.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
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

-- Each record gives either the initial pair of OR gates or one transition from its parent.
-- A restriction to an induced subgraph rules out a child when too few gates remain.
-- Otherwise the checker verifies the actual wires against a child at the next level.
def collectCertFields (readField : Nat → Nat) (width : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,i =>
    let a := readField i
    if a = 0 then [] else
      (((a-1) &&& ((1 <<< width)-1)), (a-1) >>> width) :: collectCertFields readField width n (i+1)
def step13D (i : Nat) : Nat := 0xffeb0a81ffd76503ffb04a07ff5c940ffe99281ffd51503ffae2a07ff58940ffe90a81ffd81503ffa62a07ff58d40
def step13 (i : Nat) := packedAt step13D (i*31) 31
def ruleOff13D (i : Nat) : Nat := 0xb34654478d56233848500
def ruleOff13 (i : Nat) := packedAt ruleOff13D (i*7) 7
def ruleEntry13D (i : Nat) : Nat := 0x3d5541092146c003d4de358c91092146c003d4c90cd210751b000d6325414851b000f5325410cc210751b000f5358424851b21c003d4d61504a324424851b000f5324421043a0cd2146c003d4c9108334851b000783d554108410cd2146c87000f5550420cc2146c87000f5550421043a0cc2146c87
def ruleEntry13 (i : Nat) := packedAt ruleEntry13D (i*10) 10
def rules13 (i : Nat) := collectCertFields ruleEntry13 7 9 (ruleOff13 (i/1))
def disp13D (i : Nat) : Nat := 0x1705850e0560b1c5c21e04044162a0825d241038c4e1c48c001d68d193419e06348820e0000464540050070a038804003200013a00cc000000012e0044006201031934a00003a009030a04c0100340050a183810081307040078614001a10481e0b2a04002142c08a0236a800e155a2147c0080088100000828410044000e88021101838302080030c01a8500043061024300
def disp13 (i : Nat) := packedAt disp13D (i*7) 7
def slot13D (i : Nat) : Nat := 0xbf00003244320e7002815c00000009f825024004d06c829022a0eb92b0ae84a027505b0c7002c31804402a49e604c14f804c13a0c9019040c01400008809401644da10d85884660e00a182e81341190b5800000004404182dc2a240002b200814653802c09f855c13403a04982ba16705405780a80ff04383201b60030b902ac0e6048063819c0f40ee1b9853c62407e0a382d41ba0d303104b817604b15613a81020ce03905704b001207d85a802a0d114880581ca07901a0af40ec1020890aeda9f0680a2d10411402a08d80e028621008784a42e80e9078022891a0600b802a82b610e02a84e40d608909d81181d60c50ae051c4b60b20a30db820805547d02cd6560d50a1043882e07700480d81c424009a82002162f1079034029c23101c82904000b3151c0d4120155099026852610106d8c2c2500ac13503e44e005e088032809211919602980c21500a7923c9222e6000012525a0000a081e01c829e00585405942fd02285381d82d60ac8000076000006837440011100003604722e40198ad44000a821b856829003c060318d4ca0b809883806a6085086015812c0a202d8dd8172017134837805216303680b416e4df100000006c8dc0a480ac018037100000000000000004940dc000000000027400009e880024e04700003b404011e0138ac01b401e0ab02298ba24e0a203d01c23000a2ac841ca2d414202382d815409e00002660a613d80002960eb3708590130157000054858205a00782784522b401f007000016603882b0000160067838c0c804b09e80000000b30110000000049104050004600104304341840a002780c01150f517b041400011d0218000260026074000012e1090a300bc1a62c402e03d413615805c10000001751000000006c00000035c28a200000000000000008d04286a400003e03480de0fc08980cd10414d09503bc5860ee00e80b80000f9000003822e1220228d1044200009b000015a03d0a5007c09800007c0a8462800006a034428a0df03f80a02460be02503dc000000073a29c15e0140a008fc2c20fe058814c12a06c0318cdc0c605f06305a420a266073da940580250bb82a400c13c1b1000022c0e20b68060008000065830024816f0a600000000ec32e85945ac2e31578af02a200004e026402212f00003e00000000b4001c02622409f03d860c00004582841ae31f000059421003b42c83ac6b224a166853c2ea08f0b883b00840cd14900e82be00005288680000d805b05115180ef06603dc4001421000428146099129000000000001a014400000000000002a620008381f402a2270
def slot13 (i : Nat) := packedAt slot13D (i*13) 13
def lookup13 (h : Nat) : Option (Nat × Nat) :=
  let v := slot13 ((h/167+disp13 (h % 167))%582)
  some (v >>> 4,v &&& 15)
def step12D (i : Nat) : Nat := 0x4da14da72d762d620da12d630da74da54da80eaa0da50da80da24da32ca55e883e888e886da27e881e882d834eaa3d624ca53ca53ca83d765d629d765d525ca85eaa7da70e22bc526ca2bd52bd72bd83bd739ca17c817c519c518c818e117e119e116d623d865d861d863d656d761d765d651d621d656d635d633d637c851c853c852e554e553e557e550e551e550c520ca57ca87ca57eaa7ca11ca81ca52ca22da62eaa6c821c826da35da25da63d713da73da63eaa5da85da35da56d712c521c523da51da51da72e226e221e226da66eaabe222da22da53d516d815d812da73da83d811d511da61da81d811d713d311ca21eaa2da33da31da22d524d822d822d879d639da67da87da57da17da63d855d837d764d873d751d759eaa8d860ca21d722d723d873d823d527d827d874d733d735d325d826d829da11d877d621d521d822d732d323d533d833d326d329da3259829a995969930a930a222a592a59345973597759755955598559259305593595439a94592693065936592b277b222b233959195411963258615a63596559665961596226665a64591454135a6b5623962a211a591a541b5972597557642113266621152115266554165416591559125412591359135411541221162663211b9302595459535983595b5930541059115911211126602113593259328a6459899a99592359269a469a919a9759675981598059805971597059515951954759579540954759279a90592159275417591493039302930259245a875a602aa456322aa32884982428892660288228835a515a545a735a752aa42aa32aaa23349764277027705a7598755a815a775a7225532555255697152885233227772aa92aa82888266821175a88233222262223277922255723971797385735222322242227277722262aa42550222423392117288798212881255725512771222025572667211198112aa2233923332336233393135a869812582153215a835a3295439544954a1a901a9019641a951a9b1a981a991a961a961a421a911a931a911411130
def step12 (i : Nat) := packedAt step12D (i*16) 16
def ruleOff12D (i : Nat) : Nat := 0xcd4ccfccbcc6cbdcb6cafca7c9ec97c90c88c81c7ac75c6bc63c5ac51c44c38c2fc28c24c1ec1bc16c11c0cc02bfbbf4bedbe8bddbd8bd2bc8bc5bbdbb2ba9ba2b9bb95b8fb87b7bb71b66b5fb55b4cb41b38b30b24b17b0cb02af5ae9ae1ad8ad2ac7abdab5aabaa0a95a8aa7fa79a74a6ca66a60a5ba56a51a4ca45a3da36a31a2ca27a22a1da18a10a08a029fb9f29eb9e19d89cf9c49bb9b19ac9a599d99398a98197997196795e95694d94593b93192891c91590f9058fd8f48e78dc8d28c98bd8b38a989d89388987f87186985c85484c84183d83282981f8138087fd7f17e57d67c77ba7ae7a479978b78077176375474773c7317247197107036f66ed6e36da6d56cb6c16b86af6a569668867a67066265864d64163662761861461060b5ff5f65f15eb5e15db5d15cb5c25bc5b35aa5a259a59559058c58457c57356756155b55655054854053652e52551c51450c5034fb4f24ec4e74e14da4cd4c04b34a649b49248948147b47546e46145244b43d43142541840f4043f93ef3e63db3d03c73bc3b23a83a039638e38637936d36235735034733e33632c31e31530b2fe2f62eb2e32dd2d62d02c82c12b62ac2a129728b28027627126a26125824d24223522a21f21620e2071ff1f61ed1e31d91d01cc1c81c41bc1b71ae1a61a019919218b18417c17516e16515e15714b14213913012812211d1161101091020fc0f30ec0e60df0d30c90c10b90b10ab0a009608d08607a07106805f05505104c04704103c03703202a02301e01601000a005000
def ruleOff12 (i : Nat) := packedAt ruleOff12D (i*12) 12
def ruleEntry12D (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xf55928cd90a1d6360007c0f56a8c858d8000f03d56b32143ac6c000f55acc850eb1b0001e07aac94668850eb1b0003d564a336428758d8000e61a02d05459290812321040c6c000730d0d51210244420800fb1b0003e17a8df3ac32521241048c858d8001ea37c6d1d619209190820636000340df1b4b592a2c9484091908206360007c2f51beb252124106609190b1b0001a06fac94840cc12321040c6c002de0484858d8001f03786d0c9642c6c002f51bc3251d2336428758d8005ea378e4a3a4668850eb1b0003e17a8de1b4758e4a420488858d8000f07d4700da1ac3252132163620c000783ea3696b254592908210246420818d8000d0368eb1544840911082063621c000681b4758688c968209110b1b00a0013c2e03ac90920b21636a1c002f50b475921321636a1c002f50b435964b216360006d0581ac109908206360003c1f54a892964a33642c6c002f54a892964a330484858d8004f0b80aa1c948490519b21636000340d1592d0419824442c6c028005ea18964833048c858d8050007d564b1b000b24a0b1b000b24dcb1b0007d5648330488858d805000b24121216360013c2e039290920a33642c6c002f50b472521233642c6c002f51928cd90b1b000bd464a336428758d8001be36864b21040c6c000df1b4325908206360006d0d1094325a0b1b0003686884a192d0490b1b000bd42d0c9466c858d8005ea32521233642c6c002f51929051d2336428758d8005ea32521233442c6c002f519290919a21636000398685ac1152102e048c841001f6360017a85a3ac9051d32143ac6c002f53929051d2334428758d8005eab5920a3a0484850eb1b0001e1702c93728cd90b1b0007d56b22143ac6c001f56a88858d8000f07d564a33442c6c002f53ac8858da87000bd42d1d64848858d8005ea550e4a33442c6c002f53928cd10b1b000bd4eb2414748850eb1b50e000faad62828850eb1b000bd56b1b9442c6c000783ead5110820636000343544840cc128244420800fb1b0240013c06959290920a330484858d8000d2b25212330484858d8000d2b25212330484858d8000d2b5921024242c6d43800592108908206360003c1f5592108198246420810eb1b0001e0fa8731c0b5855321040c6c000783929099082063621c418003929081031b10e20c000783ead50210330488841001f43ac6c00068592908198242420818d8005ea758212b72664908da87000bd42d1d6592108999242360017a85a3acb24212b72664908d8000f0168120000f0165aa0240001e1aa0242360003c2c9054090018000c6168210240001e1aa0420480003b85a682090002f55920a81211b01e00c000635ac1081211b00e0016b04204846c002f50b2d502103704846c0006b0b2d50210240001ad6484204846c003c60840908d8006a8ae41191b else 0x20000f0161648422480003c3540842e419826048a1c000f559210919b210007d439ad60840e99082003e0007c2f51beb5825042248090000f85ea37d6b042074490000f83ea37c6b042048c84000f81be109908001f037c21321000b782103a0003e06fade5ac108920240003e06fade5ac1089211b000bd46f95a3ac550210246420003c2f52b4758aa1c9084904123212360007c0de1b4109908005eab582103a642000faad6084c84002f55ac10990a87000bd52a24a59210919b210007d52a24a59210919b21000bd42c2d609cb256304224846c002f50b01396484224846c002f50b4160272c90844908d8005ea1616b25409cb24211240003dc272c90840cc9211b0003dc272c90840cc9211b000bd56b04e0941089211b01a0017aad609c1089211b01a0017a84e5921081982504846c002f559210919b210007d5648426420017aac90848cd908005ead5022842246484000785ea7582124126649012321236029438005ea758252c90849041e83a2664919091b0007d43405a5921081d0332480919091b0140003c2f53ac1296484226649012321236028002f56a81142112a248090919210140007c2f55bc10819824236a1c000f85ead50210b9066091438005ea13964842066094120005eab2421233442000faac90848cd108005eab242103a466884000780d2169648420664901212324246c050000f0bd5aa0424820cc9512404848c9091b014a1c000f51c2d50213210400007c0f50d0169648424820f419924048c848d8000fc1f43c2f50b414d6484064246c878000f0bd43a8c90800cc9532103e0748d8000f0bd46484017a0cc9532104007c8d8030001ec2c2d609c1081f1242360003d8780b41616b04e0840f99091b0001f03d1756a81382112a04a090838002f07d42cac92826e419824026000fa8595920cc1201d02c04c001f56a81081992a04c0911081650e0007c0f56a81081f83d0664a812287000bd46f15a3ac7242103f0480003baf52b4758aa1c908409812012000bd4eb0424820fc1e833048a1c000775ea7582103304c0900b287000bd4eb04204c0908da87000bd4331d6592d041982403a058002f53acb25db82403a46c002f53ac1095b824236a1c002f50c6325a08400664a81222103a24c818000f81e8ba85f0a6b25a08402540a0120005ea724212410800fc1992a048884000775ea724210400664a8120200240017aac93720cc1211b000bd4330595926e4198240260017aac90849041992424246c000695921081992424246c002f56a8109208332484848da870001e17a9c90849041992a2480919082003e46c000f81eab2521033048c858d8001f07d5649422820cc122216360007c2f55bc9092083f0740cc1222103ec6c000f81eab242103a242c6c000f85ead5121033048c841001f6360003c1) else (if i < 3 then 0x7aac92844cd90b1b018000fa86a5924cc1222123ac6c060000e61a83485a3ac550a1341048c6c060000d41a5649422660901031b018000fa86a592508a0933048c6c060000f01cc390df5bc169908206360003c0691be3692a24a592909198242420818d8001f077864a330488858d8001f01e07a8df1bc368250c9266c850eb1b000bd4eb04a19288c1031b000bd4eb1c90488841031b000bd4350650c4b2499b2123ac6c060003eab258d8005ea364e483a56e09110820636034002f509c725198244420818d8004f03e0271c94828cd118206360003c0681b412864a42266c841031b01a0003c0f5192109199336420818d80c0007d4398c948410819b21040c6c060003ea3d464a3326609110a1d23ac6c060000f87d46d0c92660a01222143a4758d8001f01a46f8de1b4344250c94744cc1212143ac6c001f50d2368298d1094325211330484841031b01a000fa8690b014c250c94848cc14121040c6c000780d01602984a19290919b21040c6c000783ea1cc2d1c908ac841031b0001e032ac928450499b21040c6c060000f81e0340da2a85292113304a09110820636000fa8c9284505199330488858d80c0001cc3495a1b4364aa24204a0911082063605c438000f01a8341c94848cc998250488841031b02e0003ea781f03dc6d0d1294719209330484841031b0009e07c0f73929051993305009090820636000fa8731beb782d0360484841031b0001e0348df5ac908998242420818d8003ea1a464a424664cc121210400758d80c000bd43985a392114140242420818d8000cab24a13412664858d80c0001f47b8f50d0d501992a64246c052870060003e8f85ead502704207c4dc9532123641c000780c416564842066c848d8005ea1a9648332460889091b5060017aade5acb242112424246c002de0b407d8d8005eab786d0c9084490123212360017aade5acb24211240484848d8005ea37c2d0424820f59091b0001dd7a8df0b41099091b0140017a8660b4345a082403a04c818000f0bd46d0581ac950262c90844cc9202464246c001f50d01682c2d64a8131648420744919091b0001e17a85a0b0b58260c90844919082003e46c000690b0b592a2c90844909091b0001e03485a0b0b592a04c5921089212324246c002f51b41606b2c90844cc9211b0001e06f85a0aab242104064246c070005ea14c648424822f41992a64207c8d8000d21616b04557248c11121236a1c000780d21682c2d608a1081702424608c9091b50e0003c2f50b4b58e48450840b8920246420800f91b0005512131b0009081e81f000908121216360003b2f50cc169649420664901201d2360003c2f55925081992404846c000f86a81081d0001f03d5aa0426420007c1f56a8108198244420800f8000f037d6b0422480003c0df0b0b592a2c90842e49 else (if i < 4 then 0x30000f73ac50812221018000381d628488c060000f81ccf00cc284000fa8cc592508999236360007b8695925091993305009110b1b0180007aac92848cc99b21636030c18001f01cc6f85a0b01081f03a642080001f55ac1081d223040000faa54494b242103a46688c100000f47d564842466091108200007d4398df0b4b2422842074c84100001f07786d0d60840e9118200003e0ef0da084091108200003e0fa8da0b41606b2c908a1081d3210003e0348df3ac1081f23304a0911082002e000398693ac1142103a04a884102870003e0398585921081d024242080000f83ea3786d058494b242103a466090908001f07d46fad60841001d133048484100003ea1a8eb1330488850e8003ea1a8eb133048884102870007d4eb133446080002781ee1c0eb0424824cd9082050e0017a9d60849045ea3a266c850e8005ea7d4eb042266c84068000e61a4eb2422844cc142216360017a9d64848e95b933442c6d439870001cc349d64844cc12a21040c6d438000e41a8e48ba56e4cc12221040874000721b27582003a56e4cc17024442000fa8731a20a0120003ac0a0120930001a4689422660a01181f000344a102804821c001f50e60981231b000758130246360007b9c9040074000f81ee108100001ee1a01001d0007d4399c94460818d8003ea725198244420818d8000e6d5121121040c6c000df1b4324100001be3682102000037c250c90400006f84a38c080000df0840e8100001be0800f81d0001e0fa8da084c841031b0007d46d0c94844841031b0001606b0ca040c6c0005a0b0358210201060013c0f80e075920a23040c6c002f53ac09110820636000fa8730b4758aa2426420818d8000e61a4eb2420488841031b0001a4eb154484091108206360013c2f51ea72520a33266c841031b000bd4399c94840cd908206360017a869392109199334420818d80008a1081d0200001151982e0408758d8001ee37d211332460800f8001f01e0329c948410899b210400007c0780ca75921042642080001f50e61686b0c9084c84100001ea359aa042642080418001eab592a042642080418001f01e0329d62a8908213210400003c1f559210899b21040c6c000f55ac32421133642080000730d275821033048884100003ead5021133048884100000f07d5aa042266091108206360007ab540848cc99824442080418005ea1a4eb154084091108200007d434ac90848cc9982424208043883000724130240400758d80004c0901021d6360007c0780cad5121042266484100003eab25211332420818d8000d2725211330488841031b0009e07c0f70e65686d0d92a8905908206360003d0781ea32521233266c858d80c0003d4329d61928cd9082003ac6c000f50ca758e49c66420758d8001f01e07aac9284101199330484858d8000f41e else 0x3e06f8420003e06f8c96360007c1de0840007c1d608448c000f86a872421040266884100001f072421133048484000f81bc758e4a216360007c05a3ac55190b1b0180003d0f81eab2499b21636030000f85bc100122216360007c0f53ac8858d9870003e07ab543924cd10b1b0003e0e48402668858d8001f0b2499921636030000f71c0758998003ea1cc2c254494b2519b21636000fa8735ac33099b216360003e1f50e6b249992323ac6c000730b4550e4a426420818d8003ea1cc350695928cc9982843a4758d8870007d43986a0d2b24e4a332660940eb1b0003d4348655928cc121216360003d0f61be9080fb1b00037c2103a0001e86f83a26621c000df266000399e01bec6c000df3bc0e98d8001be1281d31b0001f83c0f53bc32519a2343ac6c002f51b432511820636000f00df0b01280eb1b000160660ca18c8758d8002a83441231b000bd4351c9484add199334420818d8001be114998200001602282003ac6c000f70e65686d15448410091b1b00037d210001ea37d211330484858d8001ee528651c64844cc12121040c6c0006a1c0160a1025636030438000e61a42c142048)))
def ruleEntry12 (i : Nat) := packedAt ruleEntry12D (i*11) 11
def rules12 (i : Nat) := collectCertFields ruleEntry12 7 14 (ruleOff12 (i/1))
def disp12D (i : Nat) : Nat := (if i < 1 then 0x16012805570009046a210c020c0c0117080200010400000105030d050300190c0e2f020006000a11000309212b22022e07010000000b05560b04082a0a000000040602091201040720030106000d0301030a000800110003012d000213010201000101000e06380300100028010811000400340012150011270000090a010307000603003f232904013a270103011101070a5e0e0a010101071f034401000e030001031d020009000009021805000c4501041f0000010107090423472f0b1e47040a0e011f1e010b0605050000070a0000160b330d0c0a0024042e011f26001d00042000001812010501000c010d081800030d0b0000002418050200080011022907000125300a0503071c01081328000107300100010204010f01001c0101140d000015030b0b006d172f070600020b0c100900010004150d0003020f0201030014050500050e00000f0705051f070f0d0502170a01121104010200161c1103002e1c07023110061801025100030026000210001f0a0800010b050c0000010022010102010d4900030a001c05001d010003350200030b1503000f070500000402130914060b0a01005d00010b2e0421040400001200200f000006000106061d131201010e170d0400011456081b090d1f01020208000504010004010f0a080601041500160109000a0002160d060e3b01000d0408082e0803003800001105060000270a0000040a080308100102000c021a0000030207050010000a03000901550006020101002200000204110b0604190000093a010701001102080504320102081a23010023041d0700000100050f00170206030f0004000711070202000000060202000201180000100012000230010435022601060106080000170c020007030200010d050201031d00000408110301010d040202000100020311010c031000130102010613010d010a01031301000003224f030100000d0102021300260708002c010d05000702040100000e230211240c000300010607042c020001000307060402181111040003071f01231905050c1400000005100a090006030d000400010e030900130004010302052f020005030004001106060804000100430700010700040535010c0002000000020001020101020702020009090206010b0903010400010300120a0201060104000d010605000403130a0000010500000a020a0b00020e0022040803000010000401280000000901010e0803020b03000107010014000e0502000f0200071a00000100000800220d000004050422040101071603001f080113000001130000001e0c03000106000200030b00040b02030005373c0411020500001d08020406040202000e3803000200040c020306010309080300001d030c030b05010a0616030302000a00112e010105080500070515190f else 0xa1847520e0100000e04c60a0e044102000007021019010b11710102461900033211122900020b2201011c26090f1500191a1f0a140321020500000214210203010054081f150103042e0304130345300c0605143e060100020c030101010000010c08303505010433220907021211020050130f0008013330940c150581000801840d41080d2500140001051f085003150a0a100000000201001017100a31030000000101130129777e0011020422160f000100030466070009000a020511390c062600461a10241202090522002669092206076e0111073e0f04176414141643000004160203521b2d03330f0a0b0a2b0a01001500030f0461092a00032c00010206071b0c2505021502390a1c0304010300003d090002041320000900000003070b15021a0054012b160802000b0d00010401020f01008217080f071c03061d0c213424120102001a0a007a040022510600000700040103100b01003019001208000e000563480201040f2204030011080103000a013806140711047700140d090703033f0200120e040b0f0a0601240513021b2405000d001806000500014503020100010c100b0c0007810714031428590016100d030022042410001428010725050c353600053c4107090000240e000d0b070009030331020310131905110500120200152a05000502112e090e5b06000f003805270801020721000d4434)
def disp12 (i : Nat) := packedAt disp12D (i*8) 8
def slot12D (i : Nat) : Nat := (if i < 5 then (if i < 2 then (if i < 1 then 0x64139608d0486f88a911c8221107d5018203e000131554021119f5150808bf0c8f0439055506d108b9200007760bc211280874000009220c9101ef131b000004c605a90150066b1188060108cd0bc20a8b02a40ac607dc0aeb52ca070b1a8207df088e4c0c1b7d07b40adb0a5c01b82111060b083a18150a54057702a105a7283d08a40449049407bb033462b916c815b01a42027609d0055014180247026e000000000918000000a7054f08ad0bf6121c0c9208bb05c01c7a043b061eb0a800000000094603855924002f0087040b0aa8078b083100000a4f000000bf0ad7089a06d2111c04fe000000000132000006f56000083e17f9022411d504e4700004c11814000007630000057e018b061e46250b250ae10c0c019908451b940b35081e0000043e0a2907ee011008fc0000050007a419bf02b406a017c30000010f1000093200dc11830764154b043a0a7c84bb02b7037e001503f307d71c93092d195a00000593085f0b14189605bb10000931039c18d31a151c00188403780b9b000000000a83a25d062f800000dd0b7c546b15a6178c00000000028c074b0c1a09730ad326fb62790b563000000000000ab10c62007701ef02cb068508620119020c2524043c0b26040e0cb801c80a7a041710ca00930688175b08c60c35120a4ab90adf04ad0b69088007c404a91b7c0561033a0608451e016940b00a7e095006d71b0e06a508ba370c07ba04e5727c04560cc41be64086183f02a825870cb71638a1e002f905da073a0b6001d902a225f4004a751a094c144105b004250c6903d20c3d040f0b6f032502bb0ca4028219ce057713bd074801f700780b33077202a48a3b1cab01a600d3006718fb1a5205df054d103b03f00c6d16900bb20b2307770688051316fc7b7b0a490318036e0b3404b4074d1a5b04d90acc026c045908b1316e0bab049a007f0776140d27041766108e2424155107160a89b58f07b1049f06f87299177f70c90a1805b21407134404af0b103b6e0301002a1bdf4b2012161b56063f068d059e056a052d1238001f058200cd01c1136b0307075003310276b5eb6c0d1893118e00e109ca00176b400495089e184400f30258000009d7186b00000c6308df164d047403c204d40b18013b08ea036300f406211a80399c055c758c1c77120e0bc70a14094d084208e20460662200380c310a360536045f8a0d11f00000003c01b515c700000b73992e00000a7c040301670b2a0b3e10c4043409c8137a0b2745060aefb894a35a0699065d000001f111e116ae0640029205567b61100003c400b504e5000005fa0a3700000000000001ac0000036f029c03f71ba710000000000002d3062d0abe005008a105920bb800000435018f01e6478d0a7a1737161305491c3318870575000004b217a3116b1ab9152c14b90 else 0xc900a845ab4167b03c80b601b9f169d062b1263187703cc00000335608d00000000000000ac0cbc167f0c1c000004d6231609c40c640b980000052507bd0bda06ae19e801f417006248107c035c08c3045709a406390782011512a3025b03931107056208e910300398124718d111f20a1d0a721000051c1b1ab9a2069c1897a79b055c654608261409085b086507b800000000001c10631bd8000007020000022902cb10000828047e0bfc026706d006080000000000000000096e07c7000000fa024100f100000bd515e50a990b5d08ae571a170804b100a60895002c0329013d0458000004bc056505d810000a1f12181b9164b700000138143d064607d1aa1a000007f30a2b0804082746141b9c026013210c2104110085019912fd01de18e30395053001d306e508e1bbe912b303820432064a09a70ab00625100004290b4e00000000025710000bdf00000bcf30000b4d13f7063a5cae19f6190805fd004205d9028a06ef0152000006720c060b02072700000000045a040010000314086a0bca3154000006810a90010a0270134b07f511111b13016a14a407701ba2190c0614025e02cc0bca193e11d400f515940000076b12ab00ae00000a68031502fa0aaf048a041f109e153e18e15a9e155005ec03db02d00ba0126007980b4809f7194301ed000001fd00fc03880a1e681d1478000005470c6f000005a70000069c0a1d10000b54b91f00ee096114fb40920b4c01d70276413e220d06a306fc50000879100008970ac0097b0b6b1210116f08091c1915bc0000000006a108f61385a000000000b30aae06d508ab031100000ac6160511b314820000081b0cb81000000001dc04670b372271100008ae1000080f099f12010a0f000004ee06da086406040bd700240b8b076f1297000007f2900000000837122e03b3037b1bd0052d08cb0ba004080b3b00d80afb0c800153065e000009950741042c01c92405106500af1a74005f09b20499060a05691b7118bf9bc81a246a100a6c01b004050771097a03a700290b3363b908240a7c20000c8c000003341972046e0bcb05851a340b5e04195a0e05781aad0cb503c7054c03cf0b530764012309b5072f00000b571bd40c47092106df0000000008c003190ca7036401e612aa0a300b2c0b96000004fa000003ef0a881ba20cb40bbe0b1404e41b721449493c0a210b310a2a14c206cd001e6000062006cb09be00000bcc09b3033b60000298045e8cc2034f04e80b68abe5005200000898177001380516100001ab03eb07620000000004cf00400000000000000204098808b539690b46027208060657086f15cb06391399012c076b0a8308b4037611150add8a7c6a0d0be8011a05aa079d00000cbb040c081100000000000006e009e10c8418830105195405ed08e51000007409351a550) else (if i < 3 then 0x3760ca609830ba4050b09fb1000000000f905b62c9d0580087d02fe000006a2125a0bf9000009ff0407031f032d00000000049600000000048812e2093689480607069e18df000000000bdd08fb06230c1f00000000000005ae09f3000008d40446002106e21c680000000001390c8802a780c51207100009764c8106be08810000000001c60aba09c0b8963b8c07490000092703a2032401aa0906000003260000092a19490abd000000d10357000000000aa000000b74100001770c8d8a31000005f517830000055812ea0000000008370b63685e0599024b05c608f001e7024e07e300000000006200000a74724b10000000028800000000000008e211f90aec04a60510005500000aef4136000000000bb3000007ce023f086d094d10000bc9017e0000083601ed561907510882022a00000000063780000b2e0391000008e10000064f0c1700000000000000000341026802f00377098a08ed0250000002a88000005b0c481000025b2000000006590b670b760cb70c761075000000000763100000000000064210000000029f00000aff050206e4206e0bef113c07d3008e0886018003a40b5449890b71b1f40728095b01a40533042f0a4919d509ef0000065a4b3a060e1000000004161000044e000006ad00000687300000ad07fc18bb93c3084301141628160f10480999100007cc07e1059f027b4c0406f863e600700100058c05611000014c09570b4502c805b30c901c7e04c909850aef0901000009c90abf099201ec40270974096d0ac4092006b0045108760c340a14171504e464ab07d0a5130b3610b2024d19970c960c27145d27f705070c360a6a0a6005260a580b8201e413a309f60c780b41061111fc100005c516ea04aa6b3f060d0338067e089e07060099000004a560000a8602c307e008a70c5c0b9a09990bec1c740b3d058600000a5701ff037b06f66c710216057d06260000023a07370977047c01250157059b02d40c8407a5001208e90b3916d70759077801cc03850a3305d6134d017607dd09d400000bb2103d010e6000050c0731064307ad0c3010000000000000c61c890049000005c2076e05d716385b12136d1090056e1a560b7900000b9d0a5d005100000ae00101182e000008771461082f02070000080d0a8d0724088c171a00000000000007550b5f15c50b3203034952022004a418db06b207a902a200f7049300000528080c01f305f0074508ae2a65023e12b007ef0890002200350c450561297f1cba038608cf0b5313fe080206ca09251765171905430a4cb6302340009b0c8f161815b317930291092f14540b5d40000b2b03701c540632000002c207d202c60a8e069b19ac09371c0006b608c1b63d0aff8287017d0874a63113000af00bf1126509600c98015a000f1bda100004fb0000010e00000 else (if i < 4 then 0x87db5340803069709bc06301a67026402fb0768149009ec0a6f0ab704d80415077301fb11ad02ef0303121d10d40c440cc50a2711c31000026f03ab0af69af400000c970000057f02f20a4a06d209840a470000082309620c8915fb0000074e0121000003d4154f22220236165c056c00000b1c05d607a2125507fb01700add08b907ff009023d30a76017406f6000009b7097f071e06a00a2202330568045d64cb0c15090b10000c2118de0000000006a317a3079b100004ae039a0734090d000001a10ac108b041cf15a20cc0068717cf08f104c40000016d000003810a1c16261000000009ee089949af07c8060008e80c9f1a7b200001b706e40b3602981161060f0bc63be6ba50082507ac1bc00000076a074200000aa70000082006f8000005b2049d0bb117a805370acf08b5091001dd489301f71000000000000c391b751000030d0a080c3503b7050e052b05f5086219e201eb04e0204d097103c604b003a500000bcf95760885271c017b0a1f0c8e000000000000045003ff096c0a64078800000775168a01c1084e060c198519ed01120223014b022d08220933000006eb0afa08b30a78068f18471bee0cb3045d82d90c801011146f085408be0a8a01ef541b03790c110a9a04f02945029a01bf38a21aa601ba1b8a089b09930be4108a03a1024a80a406e0571b03831af809cd02e10205039cb7950b10244a06f7012d030c07030000093606ba070904c102180baa02090740073c0650042319d909c10488000004961afc172e27e20a796afc00ff0c161979006910b10b2e130d14a7069a125a18520119172d0725000006e80b11100002d70466091200000c99000007cf1569875d06bf04ef20b909f709f1083000dd18c0501a083913e1010f001609511632151b07016630800002da07a4081602581b881ade847201510bfe0799000008c900c800980a1e1bf7163304f25c750c0d0b43000001c61ad91959084746a8021204ed6b9b1cb3147d0b900bd2138915ce07b50b841bbc086c000000a906de07c1033d0c2202f8019602bf19c4b1be0b3e087d3bc1040101c635f9042016cc07f899db18b31419083904f65be600c002d812e8093a000008251a3e000005c118f51000070d0c16044401ab428007f23000000004981259092b1aa10a8258d30381b304079e1000056f07f10a280c3b03b20ad904e0034706f102ce00000644161e009d133702b90a3d159215490bd56746044f2a97004706750000000002100000000000000c9f000005560a3d06e3001b02e70cc077aa063314ec68dc0ad10bcd062804ca1515026d0718066e028208610c6b007d086807731a7981b111b80c7811c507a20c24100000000c5b0262085a0a0a0000000004c30cae000000100000000006340b3814210b1e17961b45100000eb00ef0ae200000 else 0x66914f6043804ad655f0369027c17000801000000b124640c0f077c6894172b033661a8248d0caf04ce07cb00000479022a10000221091608c402d615911a3a0ad218e1420d2c5e0cac07650ca5147c1b80136d093f01b909a30743090405230753047004a302de014d007016d300a00a7a257009e50b08095601310c7907580b791be3054d05a40b2f16980817153f03a018a2040d01940587b443005d02340adc09ae023e0423024a0656041f0460087b989f0a3b01d6033812be13f60068463d700e09fa0a850b3f1524145e091b02dc14fc04c007a7038d0000043f02520515167a092f035816890545138b07100a35066207940342016c019e0c18019f097505b8025f06eb117c012608e50a191bdd1127000002df0b0b088c095f018d0000000004db000003ee019c050901e400000ac7050d0a4009bd05b5051806480be8103406b7096f174c033a6208200000000bf0075f123b1bfb06fca2630c8b06f405e8018a01f10898008b0a0e137d196f038c07c6084601ca00cb000002e114b50ba614c50000002e0c4b06e2080700000bc60bd30913000000000c08168b0000000000fe0251054e1af30b3808b210000b270000018600000b1931480000093500806000000000f8060613df000003b402ac0bd207d90961000003ed096d1a2b1bea06fc03f9083fa8c10068094f00000b6408f7162709291c421bc7371c13530ca300000b6c18b0b17d4b974808029001160b6c05751ae700a505170bbd010300000c56000006e6000000000000000000000c7007cd038f17f7412902e4484319f5498e055e0a880bd0199410570cba1000041e0be513d606fa00c2108405fe0b510bcd19c808a3163a1b4f073907eb0af107970b5808330569600005ef000009fe042a0b840be20000065b0a010a070a7f029e001404a000c60a7f11f6066c063f75040b5b039f00000000000003d900310000071d100000000000028d0000000007570b57000006104591083f582d006c1bf501730bf708671ab800f5038b104a000005e702d502f5083830000655023501ca1b0028d010c2092902cf099515e0007613021c7700d20283228505980a7a88e60ae9008f206d0ad418c2050505dd05690000091315be16050b9930b802360ab602c21c82a8db4b010412055626a701ba04b80ac714be08c802400641116305310b281558000006a41be1096a05030462072a1000000009eb00050940000004a71a4c491d0bad017a06e90a7b165f0aef19bf170e020b00090affb32c0000081d00ec0c2508ce00000bd9051c02f10000039530000000000003360a9e002600df0000061a10000000030b038c2487000004d500ea097e000000000a7104ec2abc09cf02860a4f1000015f027f05190b3c02cd03971b2a1b651000089b104b051219780c9a00de08590c230))) else (if i < 8 then (if i < 6 then 0x1330374076f045779ad01080c2404ea01bb0c0e111d05b101180ac805cd010d1b06000007a11cc8059414e5638903e404a502c003ec083500670c9e18890c37023006bb03376be01a060ae807b2083b0cc707c5045200000768066d095c0bba07200806100002b8006c0c8d2a7b8b2612d809ba08ba050106f00b09a73d1665000000000000054b175a071c7000033f04f008bd044b0970518e22430942014001970c361c270b1003011c2a08170ab504e1032f01e600dc00c312ee0bc4040606ce09b905eb0c280af016ce1a2c087b05e90b7617c2188d0b83087007e906a90b65000303d8039c4b9e04d603f508ca0499175c063f1b29153b09f9068c0acd070f18af1bb6057304ca07f81610a00006e0a63607e50c7aa2750000056f1000000001da008716874000007b04b6017804a809280256000008ab17a00000000000000000024d0447002a08a90c2b000004a21b2d031d0b5699cb169a02bc07866a4818ac110c10bc0ad000e706540c58023918ff02e3073f0a6d1185021b1000001e0b7ca000045506ab03e904ed29e00415153808aa0604b64b015606dd019c17b9000001c208a002ec09370bc8000004c701c010000c811c1b04310000081c140005d103230aa9085d15b70a011ada062b068b1c05182b11f440b400000abb0ae2174b10cf000009c318d4159608bc055a034019a508b8073601e100000cb016e70694031703c900000000045f29391c2c00ce08a5000005a00c3004e52096037c06310c9c026b0269080e077a06d805410248079e09fa1cc1033209b100000000016b0c600000000000000a7d0cc51392000007ab02a7127809340cc71294007e06dc09d3029b0000013e0000098610101bd6020f056b0000000003830c9b000000000000000000000c2210000b4818ef0375056600f2083e0023000009c600000ae91b2a8b0309531888000006a40760000000000642037008ee0448056d16a5121a100000000a0c077b03d00c2909230af6113a0b7319940a0506bd0a110c9402e40c43119b12b20142001822d10497029508b113b0096801e509de023c09c702660be4000004330000000004860bbf1cc6141752f7089f30f60442087d4ad5017e1c460ca616920aeeb89e81e71c4c0b4e148f0000000001490000023d0756015a1370690e07ca03cd00000ab40a480c420a3f00000a7202810b41136202ae089209a6006300000bf30c120a6600000b4f102c6162095308f50aac0c1068e0110e15f103450061045d05561b5e181a087c0000000006d90c51053d0a59033504d10a120b3701fe003e0000071103fb005e09751215053816d6051f100004770000037d08ba21f017f20682094a0c60156700000b8a812002a6000000000000063d18d1000001a80a4102a2147719a3100000000bd810000000017508530 else (if i < 7 then 0x8e118b0000007e801e307320bca009e063d6c01055d0617187109e4091a08af0000004600000aee000005ba0c760322092d0c7016a60c520b0f0000000000000000000007f6abf018c5064908580ade0419132800000000048e049e000004ac01920000089905140000000000e507910000088213a8003707fa0c7d0bcb319f40000000000006ef4bb10661028303a1ab190a8c041a032b032006fd010b0bea100001b40000000001b30000000000000896900003ac00b701e44000000003ba0b7102a9000001af05110c3908bf10fc15b608d808742000048c0a2410000bd8868708d0058d4b4b04a100c1042007ff127130e80761504300fd090f038e0790000003080b9504d70309068a100008bf301f6b02225f1a94088e028900af0000098c1079000000000225000000000c83a0bd100003540b1601a3040a000001fa000005d5137e147107d7020b104c00bb0246027e0bcc1c2f0c1e1c4003120b6a0bae029304f10b3c648914d01717053c161d10000bc1101c0c2607b303b507f431c7011e0516010d039c020c09db08b334e601bf0000000005d8097e161f0696064e089d03460cc8128e0bb005590892143600170422021903d4098c04e0a1cb1190097d0361000000000ba9061100000a8614ae71350485083c0aeb100000d90b02839210ed0000000003be0000019a19d705a105bf08400c7c0cb1104e00000b8514c7153a05a30c45100000540cb600000a250872079c0c8204da0b54000001f75b8d05f816440a840afe00de1c6e01de09c507057af31809083119b40c73097c0bcf02114b30035e12bd0ac308d5098d0110b416017f058e07816b7f055c095809e70af631e80a3906ec042d01ae039d116a0a1c03900c0e00a302450a510ca808ae08e001cd08fe0398073806fe02a00ae401220713060540e40612b201147b0a530b590c3f040406c002b218bd18e3147a0a5e02c704cc014a07bf07d60769057406410a6ea6c90cbd019a0b032a9b015d0779087807f83bc833842b07076c000008f90a6908f807d00adc185811370ad3039d046c055208c811c904f2029414ea1185181815a44bd82b2f0b4206e925021bf2007306760aa206c8035607ec002914dd05a507960bff147613600b704ba113e8096703510a2003f2033306f3018107810a4b1a43082d1b551c200b9f03fc031c057b02c90b97b6090a29104108ac0069080515e1026a01450ae506c308b20b1503ae090703dd0c1d0080092a035207ae0bb408d6128a8324478f021e05220c01128546d4043003930b461b930686084c068d133403660b0a038408630b0c0c7f18e8172304dc08480ae61813083406cf000a094100000c0500da02710771135b037f1615170c13bc005c0911146025231711176d076d128a214f069b0000009705f803ea06c71585041c0 else 0x30a02a7205807e40a7b02dc09b600d0057801f804f3a37201dd1c8b12b10410015b10fe18b9967010c303af0766046b002365f30313042055830602181e13b1069f009d06150b9909e603bb06991b2902d2011f04a907520059058a4a7900f615cc093d0397072c0b0400070b55093211ff1aef5b890a1e09f4190908842890189d11a50b54177f0a91021d06790a980b870244052c0343086a15b90939055215d704ef08dd08b1060c0c72025c0c320c2e09df08bb37b007e6035501fc06fb0aaa0a4b0025013a13e203241012137f07f000b60c100879003f01b1027409170c08055b07e5186604d20be115bd0be00af505d30b730c130952150f0ae115840bb81a950afd028b031a0c86077c78fe1b09060717f50b5a092c022706700b2808190166081c00a205320210493e0af7041301c40954153c003905e56a9c0bd0677509ea01050a8416a20c6c05f910c500000c071a4507f91aab00000c2d000001a00c49091e0a920c3e0c066b63058908f0129d04e3084813984ad6078001c232d60000000000000aa400000bdc1000012f000009051a3c004f000c087e0c0707da000000000ca508a60b4d0900100006640b021000071f011b021f034e0b94600001600ad80996061b0365073a1be709d80a5a0c0908f6078c1c3307031af5166a1a770439799e036c04df033e024f0bd911fe13a155f60323159002b50a8d692b0cab1343135f061240db10000b240b8e000004502426035f1b7e01240a620bb61c14085003c00b6a109108f308e1a67300000b220a1b04ef1270018c000001001358000f000003cb01c91855119b021b000008e28a8a1492000008ca1a930873088b05290a320730072108c11b50002d0acb068005441b850980000d0551209c0b050aa5066601ec008903e707be04ab625705b9134114f503e30b8f0c6d0ad1123b00ba000009a5157108c70085127701db0a8003db1c1a175f0ca20893aa2f05536ba601460b610a6e08955ab3170406db0b0b14240653000001f512840cb208fa054e08d7074401d800000668090500000a240714088f0000000007b70000015b08c910810440072600000645099f08971b2712ba062a01d208b414cd062e0b780000030600000184073d033000000aefab11017c4adb16c604e907c00c6c10000000006a0a451350040219761b700bde03a907af05061bc413e50875057a0608bb9707610ad20249000000000000000000000bd761f502a91b74a000000009c5100007841034162c09d2084f022c0902066f02f405db00820c190000022f041700000000062900cc03b60605b45e2b20008c0094070500be0231084d05810620582a0a4a151112e605f20076051f04c807906832044d094708d200000000053e000008f2056d05e404511ba80000042518ab56f0100000000bf510000)) else (if i < 9 then 0xbd094406580b1f098f07ac0a751b3019c33066063e08850c6105a605ff07a1054643ce06b10810060308e417de0b8608270c8d102b0cc3052701430c43045c0ad456aa05d8367d00130647409a096216930117034214f7037301a201580c17160914730261029902dd055c16ac05cf05ac009f000b08690ae6045f087f0bc995f532af02c401e90a4c06100349050f14f90c7b020609b117047553048006c619f40224054005f7078a1b5f019d03680be2146308e3899a032341ce007207d809a0006003a604e919b91a2e073e064010190542060a1701037e65bb07a326520b62051412e4b1a70000058b468304750a4d02e0034411fb027d079d1be314e705b40621015e072c120a062f2851058db96b0beb09e90604416d112e01b20871ba2319c44ca10926025300000c37148b0478100005ec10000c1e025211b6000005e3094810000000000000000bbc18b930000000038a0aa301650b1b178504a967d81000000009b802b6075400000b1702bf00000a7814b3033c00000a6b05692b181000000009c0489408f9130e05c309a808e71bce120806710986000804ff09c39c9e0b733b5c08e7026b1c590465060607691bff0bf40aca04aa0a020caa0c66146d0189000006c709151c8301c2146802cd1b1d05f616e105d409d603387ba3044f0bed0bd50a810c8d04fd0a19057208f4000005c91b7d1000099b0000058b09fc038480a914f303bf053900a7198d152a051d098e11090ba41c4d05a801bc03f8039e0371096faa380481090a0a8f08cc105a047f0b2a200000a10c030134080000360a00000008d608bb178700000a7f408606f507c901690c4807a60a9602f302000a792000083a0c0208fd052e000002eb00000000000008cc0b6d02231390184a000004ed0ac9001108f70a7c1b770b1a00000a4407f400000000000000c4182412c01000042804ec070b07b60cb610880cad0305001d0000000006b400000af901020c6605d00aff400000000bdb00000774044c063b0695049b050a06201517110c005619dd0b62b38009f2074d0597031006da14f2a091280a03661b2980ab09b002020af91000052f05c10065127b178a03da04eb00530095061910000000000005450000095d00000a1a6b75056406161000029b261c00f0000002741000011300000000000004f12000007106f208e32a89077c062f00e000000c5f022805b68ab300440702189c1000046906af0bce0b740b1c9a8112320970000005ab09640000031e01c95b1b968e040f1982032700d60729068f0a2a091c033b093005c80624096e13c10535027b042e074a05c008550c6504f809f8098a184506370c6a03d50520061801cf0a7306f903a007f2148115570ace077d0a1d61040c7f006f1b7a045b0911090009a904f6a4d009f318a0a75e042b082b0 else (if i < 10 then 0xb781735138f0cad145301440a6300000bdb12c507ef1c670b1e0c4e09760a9f09030000084a10776159028319d10b3a1aed08d90bc301f551d00339682717fe000000000712093b00000816102804270bec0c0a000006910b81060e02838b00027307aa1b3317cd38ef11bd0b1c1be9000003dc049100000000086e08d514871a04079200000000057906510ad4000000000b7203f10cc609140860000000000bef01ca2afa10000722000006e7168b8c0b04ba062718e4052104a20c41007a03811938078407d100000402048906b3011400000c870b011b0d03d7063002db067406ed03fa09d740000000028117ab16b904e409f009a10cb916c4000004d309c2069e00000b1d1b660588baea17470000000009dc04450000000007f802e905fc0164027d16170cbc0919000003870a16097c43de0a5f0302028f0219114705ee00000c381c03198912170cb1012a0081684908b601c4100005ea062d15880339063aaaf20000000000000bfa068413f409fd000000000000000000000ba50c711000061a00c70696189c00000c835623b0560ac2085604cb141d0ad25cb906e11645163f659a02be086f0483000003940a1b148400020bba10000c5706c205e2057a103208825bf81000019500000805095e0ab20b2921680a2d003302e50ae30597165a0000000100830a6106d0113f00fd173504b207831000094e06ff08ec10e601dd06160000022e1cbe074f0ba703ad0a6319c000000c6117ea000006bc0234100000fb000000000000000006c10b49056e0b624137149803590646134800000000000009b01000085c18b70818097112a800000c380638085c03b80bac000009810a26017206470c5d0b3e71ea02ff000002f60476000003221ba1072e0000032a0a030bc93a7505e60a2305de0b52034c079f0857080b081f106b01c303c5058f625408951aea0000030c18dc10000cbf06ee0106000005ad02751548096307d40cc171e2017907cd198707a38a0b091910aa0bf100000a6d0c71982901550c3a10040579170a0237066704bd090c159d0aeb01930b47066b07e615120c3a00d706b509c30a17024a273b0064081f094c030300e9049c09550b01264c04de00d508eb02fc00ff1006098b071d04e205b51add182108470595021407121b800bf80c950867028a458d0c5a05af0b521bbf31ee0484122608410998035e0a13081208b9195105c713aa0bb71caf108f0bbb0bfd02ed017107bc0242063c0bed134a00e3099d07c20ca002952bb70141093f884419701733027a07db0bf913da16690cb00018029608260bca69da09cb04f40b88020922ad01d1004501980bb905c408a41c5007670cc4030f01c71990084b079a0b12051e18a30229155b66630c3c03cf1bbf0ca21bf210e20a1504bf05d5046a0623415c09150a4e1 else 0x87a0ba517860a4e00000414077e070f056000000398badd2a700c530647bc8a01a901cb0c7a1203094b0000016c18910aba1c3b17e41b910707012b0bdc09cc0baf0965006f035d060209e301c0000006372000002163ca0c7515eb1a090000023908071172232e00000a9d0ca90678000002c11000036a07f609f50ac5057c0bd10b4a06770b31178e090b022b06b809aa000001bf124c0b6b0b4405c9068b27e70b501c3c1000087b354a0bb505d20b2d163617ed0b39056306ac159c0be71a87082c04a31460839b0660085d07fd08ec018705601b210c85096606840b920b1b05be0101092508a80c4a01b5067c014e021a0000063a000000db01df061d0bdfb612043703d1019109bb0af60b680000088a00000a2700000000058a02a7066a0991000009fb0c5503670bf6000008e220a61020072a02a506c50000000001cb25dc0a460418170e14e512c101a94b3d13351c4f0b9d1bc50000054403fd0613103a083805ca013009ab021307890000063508da07fc0))))
def slot12 (i : Nat) := packedAt slot12D (i*16) 16
def lookup12 (h : Nat) : Option (Nat × Nat) :=
  let v := slot12 ((h/1537+disp12 (h % 1537))%5308)
  some (v >>> 4,v &&& 15)
def step11D (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x94c510a625553111280a21404eea02555011106c998765103b2661d92a8a8a20544ee2a2550e13310ca20864cc432555b9442dc9dc345101a2770d13306895594466a62331b9198a48cc7a46630233501198c88cd3a466b823318919a408cc424ee2b2771592a96c9dc6e51037266149440a49dc524cc29255149110f8a207a5103d2661613b8c09545e510202881013b890a20484ee24266171440b89985c4aa1f2880f93b87c9983e4aa1f2225693b920998744cc9c2884e9442e09dd704aa912771c9440e49dc724cc9e2884f13ba789553c44423288429442149dc4a5102527712933088a20444ee222661112aa18a210c4ee86255431110e0a213e5109f2772394411c9dc8e4cc31288189330c495520510902774812aa4088820b500f2aa08955040aa979302665a532955198aa801b0e665a73f119a0d694cd2a6b52aa4b94425c9dd2e4aa972334b9110449dd82b50892774492aa24889784ccbc2225e1088035496a510b52775a9332d4888fa5107d2553e919a90a2148466a4222371441b89dcdc4aa0f2880793b9bca20de4ee6f2663792a9a4a20d24ee692663492a9a4888224ccbf2885f93326ca21364aa9b2334d9111f0999345109a2774d119a68888e251071277389331c495526510932774992aa4c888205101027708133250a21284ee942554a119a5088852b241c9541d4aa27a5513d3482995414acc05655084b30485980e2cc0e96614d2a82b954424aa0aa550612a8a0954174aa07e5529028243954194aa276551712a8199a41ccd208a5510d2a81a95418caa242551744eeba2661cacc2796613cb25121921cc5d2d4aecca4ee652553291132c88996422672883393b99c954ce4446721132933304a21824ccc1255609113048451e5108f2774792aa3c888cc5106627733133198954cc444662111bcd496e6a4533528b2884593ba2c999064cc83255b38cc0e16613eb304759818acc0c565520b3090595482c98dd6612a44418222898c143858a22264152550a919850a20284aa9e595482c92496093b30e9d5724f2a92194c88d30e43987194c3d1c5065e34ae81a2a70d0d7c6944f1512e1a8968d2cac6842b145691a5940d11322c6b0350168b5a98d14a86a25234aff1a20c4595746a2bc34a0c277270d48ac6a49e352301a9108cb0ac6585835200981330989d82e8ee1749d1a94e0d49106a400b4a811a95685d001504032c600211001331d42e9741740526600955004a20024ee012660092a804888b2352251a9240d48dc6a472352471a91d0d48f86a47a3523f1a9118d49086a50a352ad1a9130d48886a4bc352291a91c0d48c46a572352b81a9430d4a486a53e352901a9488d4a786a53c3485b1a91c8d2001660012a80059200a99000aec005546a0ba3585d17c6d800510002770012a800888e817400141 else 0x7422cc21165d08b248559842acb8ad65508b2a225951eab98e48cd3c46622596112cc08965e223256419817acc08166048b30245960facc07d6545cb302e596172caa1965d0cb2a86592b18cc55464846b302559812acb13966042b302159715acc0ad65c4ab2e3b9546111990d66036b2c2a5970e2cb87165454b2ab62330d2cc06965c34b2ab5233301552e88cc29144148b1432cc07d6483f3046d288369331b49544e4ee272661392aa1ca210e4ee87255439110789dc3c4cc1e2550f11130661cccb50cc26666111330844c0576602883013b980954cab04182880c13b860998304aa30563502b185a69246348535b18c0db1856c4c8555130ba2fad925caaa8c34d451ba9e8dd2c8aee7c34d3a1ba0b45b05969a70375381b19b8d8c906ce483741e8b60f2d30595482cb05251b12c45bc946ea823741e5a52b95d960aec2cb2400c82920d88794ca4c36c5f9b65495dd706e8aa5769b2aa4dac926d5c928b4ef01baa00dd1156e1ba350355a50a2d392e2d984b50da1ba728dd12caec945764a8b20c2dbb7c6e88aaa5191a4006b8b08aed34b4e459a48c0dc45c6da6e375181b1858dd4606ea2e375171b18b8d98614ca281649a5925d4d22e8aee4a37200d513e2d32f268ea6373531b4aa0da25169528b50935a749ad44186e82f16c138b6a385d1016c5353029b9813245324e6061434897592698dd1a9699285549a5524dad425d608cca6200d817f8db3fc6e1fe36eff1b57f8d81a969403b4c01da849ad2c94692243481e5923215da516d528b466a5a8940dcc606d230372132bb0f2c135c6a030b50122bb0b95da64a2132466992224a9442549552a466b62885b13bad888a8e3234819118cd4bd82e84f2e7550ba2c14416099834b4a905a530ad909d61c78576d5182202d9852608ac51049288311441889dd64510b22772b933154a2152510a92772c13b848a20244ee122660912a8862e856b4e2b8ba422d396caa836554372aa149550a62e8b85544f2aa27ad40b0aa858b502c5a71645d0a8aa854b502a5a7182d4280aa940b50a05a7141550a22e85e554202aa102d408169c48554245a7122d30922e85cb502e5a60f95507d6a03eb4e1f5a60fc5d164aa884554482aa2445d070aa8745543a8ba49155110aa8891749c2aa4e2d4118aa886554322aa5bad42dd69d70b50b85a74895524569c32554195a61c9550e569c72b4c9e2aa4f2d3898aa84d174232aa429552156a04a554255a612c5d088aa844b4e225a6112d288a2e90cb4a5e2aa2f45d0e0aa93e5549f5a84fad391caa88eb4e475a623c5d068aa834b4e1a5a6189550c569862b46902aa482d3a4168df43044a28842ad389569d0cb4e608b2244530722987514c158b14093b87a2a09e5102c288181442e0a208c510462664e92ab28a2064510322661912aa7488) else (if i < 3 then 0x880390401c5200ed2a4e545272e201d62848d4c186a614353461a9890d4c4c6a64a353461a4830dcc00506163721e9b90c4d4c8c6a52c554875a74aad1a5569d30554992aa4aad2a1d6952cb04875328c8c8c806461432302191800c8a525c403b4f031a9b28d4c1464556444315965a155210a21084ee8425542111210aa9685768a2775bacbae165d70b26929a9492cc24965d24b2492595492c9aa8a21544eeaa25555119aa88893930ea82885413baa08ccc84cc4659621acb0549986c4cc142663e933138aa8425542b2aa0895d994aec9eb302c598152cc0c166140b308e2771d2caa089dc74b26882884413ba20955104441c2880e13b8709547446642288241441209dc745103a2771d12aa8164941304bd2885e92aaf48ccba4ee5d2552e919ad09dd684aab32775094429ca214e4eea72555391988a58c90b0c1c5861d2c31195d886aec32576214d49226a4393523a9a95e2c90032951f37400db2006dc0036d99937400e555e2a09966e934b30bc2aa3e155268aa8cf375531a45e4d22f26e983374cb9ba334dd234a211a4ee8e26614aca8c165540b2b381b29c0dbce06da70367381b09c8d8ce46ce72365391b79c8db4e46ea72361371b39b8dbcdc6da6e361371b29b0ca8072166432b35195998cacc46566832a7c2bb4f4d48588cc2c444112550792a84095599352cc592552c919d6496ab24665925acd4a5164882b6cd50bab205d1056d482b6e415b820ad8b842ea901754b1a900e544c42e8e4555491a9a50d49c4aa9b017401ca53a1552b8aaa7c1741d5b600e51007aa8d45541d5b28885d4a86dec6174da0ba0eada8756e03ab6ed70ba3b95524caa8f25546f2aa341551d8aa912554732aa3a955007a2003b0c685a83c1551c0aa8e4b50795a7382d30175d803aec6f5a7382d39b8aa803aea692aa3a2d400759403b0401d8700ea9007954d3304715a638ad41bd698d2b501e5976e0d4ac96628a352b2597252cc07965492b31411a97d0d4b606a5ca352dc1a413caa07a55020b308c2bb332cc350552d2368802bb07acc19d66148b24d41b9302ca86165596b24c92bb0c2cb98165dcc372115975115d8ce550c92a8bd95433caa19a550cb2a87d9545aacc331505445548c2aa45955238aa830b2ccb54133aa0a51660cca8265592a58da22caee6e373371b44695da38aecc9162bc2bb094aa062550c12a812598092ca86166198576345961a2cc1a25ccd32e68b5a80a4aa05165428b308226660144300999804aabb266192c9a7564c72b269e59341955320aed04554822bb4195db016a05d352869a9344c11a8998e651073277391441c89dce44cc3328819933064998f251079277381441c09dce04cc682883413b9a0954d04446b2883593b9ac9555c4ee752883a1441a8a20d44ee6a2551345888a2c44eb2a2759 else 0x7635ad39c969ce2b4e345951a4aa39c69c6cb70ed1ba1a4c3b7461c6b30e4598730adbb6869eb22e4105a75fcc3afd6a01eb4e369541acaa17565df4175301a9ac0dcd642e988554c29542a2daafcaa9792e2dd1b960ac92bcaa95eb4eb02aa619554ec2eab6174545b622acb26d66182a824559822ac9b10aedbc175351a96195db00aed80554bf59860caa304aa982b3045592611554482e8a8b64545b3b405d1516e1ba17400d754c93b8589de6834a179b92c4dcc1c6a506b748b5ba462dd2f8aee3c3527d2bb7e0d4c586a4cf2ec669712ecdc9fe2cdb6352f919213cd4b8864ab23726a5a71a4d4ad96eac0324e41a9718d4a9e6a5f2372f11a9b00d49f5699c63726d5a6720dc89e6e428b247d5a53f15daf4aecfe576bd5a8798d4b4864892577541a9870d4c406a60835201d72611445a066138b30465984eac924165c64b309d5981a15531ca218a510c62882dacb88165c3eb2e295971d2cb8ccaec685764c8a81aac98d56606cb30315a51b1440d89546c46600d7260ab92549dc2a4ee142776214431099886b2a325954eacaa60a21304aa982334c1110d0a20684cc50288229441149988a466452221a9440d49986a4aa352330fcb98b25d8552eca09766885d5786a69e372a32bba305d4f02ea7e175420ba9e85d5a429978b4c00d65968d4cac6a6523533d1a9988d4cd06a66e353421a96e0dcaed699765768a2bb5d95551c6a51f2a8ba5a6aa0dcae8aa82d151531b616ad92b0aec5ab6c2d5b36e05d2c569d5cb4eb45a853ad45c82eae8370812aaba05d2856a27417498987441552488cd02b4e9b9874b13ba589552c46696222559442ac9dd564aaab2335893bab4aa93ab50865a8482d424d4c924510922774912aa4888824b2c585962bacb05165828b6c5f5b6232d40c96a25014d521a9860534342982b14cfd0a621ad408d6a04ab50225a81c2d411d6a034b50315a80cacb0e56588eb2c1a596342d35346de9a3754d1b3a68d92d8aaa9c36f4c1baa58dd52c6ca983672b1b05b15dd2c6e69c3694e1b9a50dcad8998d04cc1f596474531916182314c828a6006c32cd65c20b4c665a647ad380358906b4ca859345ad30035d982aec4596540acbaa255114b4ec057653caa29d65514b508f5a84bacc19550568b2ab45975a4aa196298312c465586334b123d588312c69295432908a34aa8ce5546798247cc0b406a4fe554bd2aaa70d49f8aaaac3526d2aa0aacac7c6a4fa554be2aa361551acaa8dab506a9635eab185564830b247d5a33ead43d06a51cb74825ba860d4a066a6e8352ab2aa5515505a6a43d352a25ba6715dc086a648353281a9800dcaed6ea0a3530b1a95d2dd4246e602353191a9850dcd4c6a5352e27b2aa0b4dcc206a640352952aa1acd48626e48b352875a84aad42616a0f6576872aa00ed10078)) else (if i < 6 then (if i < 5 then 0x6cd6bb46b5da65aed3b726a5ab35298d3243ec126760933a64e42aa6915544d6611795083ca54675522faa907d54b6da513ed8b49696aab2b13595922cac9564c21d5499d874ceb9c5966107b4b0d59586ac9c3165e0cb2b06593476d3a0b69d17b507bd879bcd4a6760d2bae6d49a9784d4b4e6a68eb2b47597a715552caa929aa494d324d6a94a2551c92a893d874a6c1391654fbb0a7dd8371cc134a60821b0c10ca84a6c283f6a01fb4e10da7086d35de55053170288b2244588ea2e07316a909a90dcd48a26a45f352209a9124d487e6a523352199a91ccd489a6a447352859a912cd488a6a4bd352389a94fcd491e6a435352cb2bb2815503caecba5765d2aa3395d89caec4e554b32aa0a95d854aa8985764c2aa509552fcaec6c554c12bb5415da3caec2c576162aa2295d914aa828576142aa0f15d878aa820576a72bb539550d4aec6a554182bb0c155198aeeea352165931e4dc9dd6a2b4352fd1a909cdcda46a64e352ce2aa6795509d661ee331361a97a8d4bdc6a567352f81a9462d44346a59d16d181a9322dd0566a6aa352da1a90b2caa2d69670353171a98a0d484a6e4af373431a99f0d4cb86a4f4554d71a9950d4d8c6a622352ff1a98a8d4bc86a5f6352cd2aa1b2cb4c865aaa32d301963cad409d65952b30802aa50acc14261e7e2eca85a7ad8bb1816dca0b30aa5a8554c12ae60ae83041e96353cbb29d5954eb30ab976b90c329d58d68511301ba980db22169cd2b4c895a7312cc29166154b30ab563552b1ad1660c0b30605a82ecbb1016da7c2c6632bb13ad31856e0c45765d563554bb224a215b352642773212a9908ce26324d60bab48dc97d6dcbeb66ad5971bacb138a20425102b2882d155175654b33525d95451144258a211c51065288089441f899898b31681a8b18d459c6a02c4ccf81b90f2cc0596619e576f819861ad40566e5ee3721159832acc5886626c1745f5b59a85d4d02e8a6b6a525b52c2cc1856d420b4b330baa10dd59469264174d41ba760dd3c02eaba352f01a9b40d4d986a6ce352149a90a4dc803214018a400da500711330aa801d1000da8006d32d26a401b6a00db700654003aa80194400d82006d100369d5a9746428813944130a202c5101e2881aacb31caa98c554562bb53acbac4aa9a81755c1a9ae8dcd7c6e6be3695e1b9af0da5286d0a6b70525b67685d59c2e8a6b6e525b7292dc3942e9c0174df0ba29ad99496cc6b2c4c2266502cb8c96593eb2ec09872aacc3248cd4a510a5233529113296614cb30a6595532c9a9964a803525d5876295531d6a18cb51441a954acba7965cc4b2e125970b2cba4565c2ab2f4f197542cb92165dac372a28ba6b0cb85165c9a576c2987624c3a365d81f2ecc22551b2ca8d5654684aaa15b8ad8dba2d69d88b50c25761aabb3115d88aaecbf5 else 0x5b1a9adc4616ce5cb62ff5b89c1554956cc3190a65c527ea5284b214cdaa214c855e64135629a7cb4b372aa7215dcfa5da7cacad82aa6b955197688cdb50dc592752d8b496a0cdd54d55820a6c119728937b0666da7336d33762e927d1095d5280cc3a67a212ba6495d820aeda8536e02bb6e14e880af2ad1d6629cb314d954a44aa1a76868e974db5a7a5ad95356ca98b64e35b8336d91976c9a4b70e45986b15db5a299c2576da2bb69ad32a761e8ab4ed42bb6a2dc4b96d6bab6af02aa2af444a56e2bcb712d5b8a62dc540aedde576d32bb7115db40aa9aeb5049e880974404b2e1f89504ae881e75d9036d881b6240cb1b21555a0aaac6555672aa772d4568aa9a8b4f442aa68ad3cecaedbcb70ef2aa096babb1699d6b4cee2aa6f15db9a299d8554df5b86a2dbb94aedd8b70e75a673ad2d456a1cc554fa2aa2c6c30536d5a6b4aed8ba70c5d3962e825b0f422bb98ad44d16a274577452aaa92dbd3caee9eb71522bb9e1553796da7cb6ed85b6a02dc4f56de76b713a5b8a12dc54a2ddd0b6af52aa6a95db556de82554d12aa6e155370aec25cab322aa9a9554cd69a62b4d345a6999554d56a26c555312aa9a15550caa9b0b6f402aa75955368aa9b0577585b36dad1d756cebcb674f5a86a155354aa9a6b4ed62aa6a2d334caa825b0c57d76096bb3766ddc4b4cf35a871ad1d596a04fb4af25a5792d3b91695a3374db5a57aad3bc569da0b4c3cdb1722d1bc96a2b4b74f65ba6dc5b52d6e879b6ce15ba772dd3ce2de72b754d5baa62dd37a6e9c9163552aaa1ad3d1caaa90555485a8a42d3b7a609c8b06e35536a4c1a3b69529d1073da538ec32f38892bd1010e8834ebb1c75d8dfaec95d75a44b9a37694e1b4a8bda537ed29a7694d3b0ec3da8466d41c76a135d1071e8843ec399b6c579aecf2982a4ab9af368929b0694d5334e529e36a0d1b4272da54d6c1a6b5cd35b049ad874d6991bfa20d3d1095d854aec1a5754cddb506eda737ed41bf69cdfb4c69da834ed39c769ce3b4c71da55f65c2fb2d44fcaa1ee5577caa34e5508bb0645d321aec1c4e551ab2a95595482caa05b4c829caad79549f4aa4925504faec1ed750f6b906361831b0a18d750c6b28535d431cab6a95468cd24ae552d72a973954794aa3ee551f92a8dc8ba4665aadb2956b94b0b59841e42cb56c6bcb30a2cba4665d1976dccbb6a66db5336dc19b6dccdb6ccbdb265ed899f6d4cbb7466dba33edb99f6c583b0c66d86336bb307588cdaea67da733ed0b0769983b4466d85792cc3c9659e4b2afb5977daca9f754df8b30fc5977e2cb3f1654d3d54f956395adc053aec8396214cb8711553d0aa9e2554d92aa79155348aec839712b5b513f551a329656b2aef9b969cdcb526e537b0494c856e4d21f361d27b04b5eaaa92b10535496bb4b4659268ac9057) else (if i < 7 then 0xd6551194a88ca2396d341165e83352b4cb29f15dc5e58cf9aec88e22af2d458159429ac460ca57c955364aede2577605630c6b15d1608bb94a8deaabbacad7d662c0b31605958f2cc22f69907b4d3b2aa9d15538d6586dac7595b68badb3516d9feb6d185869f2dc56d6e274b6f425b71b6b291758c6bac752593a82cbd426e61cb2697d8784acc41966214b31095935572aa5f60d2fcaa97d82556c11f7618fbaca69d625aed0d552ea649752d596741551876dcc3b6a61db27c95dd08aaa7a5556e5b7b72daba1695d0b516e5b231e5ad7d6a0d7b4a73da839ed39d76a0d7b506bda7b6acbb565cdf4b2665d522eedb9776cd0197465d722eedacf565684b2b3c9a99ecd4bc56a1b2b51429a986caa4b56d983b5010da807f553ccaee14b2b185b871aca9bb69527caa87e5544f2a9f79552bcaa69e5534e42a4f21529caa7dc859cad94dd6c90f90a95c8585acab8d6a1c6b30dc593a3caa34565a24b2d465939e2cb9ab95662b31535b3892cc44964e16b26d19a98ccc3a0f955b0b2b3459699acb4d26a5a92a90b95436f2acce6a5a337274e883974435d655aeb2f3e5955a755333145feb6b2a5b588caa44565663352f22bb94ad93a26184fb6e65db197cc31a3214d1b046ad76396bb1c35d95db4f2b5a5356c398361e9ab4e79d87346c3ca56a0d1ac488c52981551cb6a0e9b5075eaa39f5522714a5e555392aa3065a9af954d590b2f5a896ad44f16dda25773c2bb68adc4b569a52b4d2b5a868cc12272891394a69d8219f444ae608e1b4c70ca8346541e3aa8f3d5470eaa34755534aaa985554c5a8a64c107b2d660b30d8598992cc389659c4b2ae759675acb40566202b2ae75986d2cc04f2d622b2d31596814aa55566280b312f598742cc3a16562eb2cd9598812cbc096560ab2a27cb50f652d21662d694b734a53165aacb2d5e4950f24a57da543ed2947996301954714aa445661f6b2d175986c2cb1072d44f94ad959595acc3c5661c4b312d5988aacb4096620ab31055978aacb89f2c69ab2b4c598a42ca9935cda8b30d15980c65c34d654c9b075b563b52cbaeb5cda6b2ed2596a32b1aeb58ed4b2b6a4a5b12cbd89655aab2ae65737eacabf565e76b313a5950c65ad295cd85b0612cb57e252bda69a9cb473b9869d4c353e61ec52a8d2954804aa19b295a4b30d2595802cc40165e00b2a18ca533e52d365cda32e6b4cb597cc18532956994a14ca8377551bf2a0d3950e89540a65ad226084fb6c27db5666d0bbd661a6b3065e5533f2a99b955a8b2acce1132edc3335d8c1caaccda633ed45a56cebeb66d99543272aca16d650b6615ca56bad307b54a48b6a65e228badc197aa82bd769bd324a6b9aa35cdf514cd88a2336d2af36061a94a65da57d2c9518aed2fae697d327b95dbe0aedb655466d8132ed39976982b96b39 else (if i < 8 then 0x6eaa3ef443e1648c994aa2eaa4775520baaa50b2b679a913f5d99729423d5427d870f6c3b7661e8130e64d76ba2cbd0a5d98db513e5a78dacb2ab5ceb2b2d1659655eb9b7d65a74b2ede5960c6bb4f965e42b30c0da646ed3a0f5da80b50ee598774d4d026a676b2a82d76476bb2ef5d823aecdc9baae4c3bcd699dd30f3d9766d2d41a3954d1b4af359879acb1bfaaa14b2e16d736b4aa1c361eb330445d62adacaa2f5d8b1aec10d766ecaa56e550dfb0e10d876f2cab7d655c0b2add5956fad2b9d65517b0f46976396c3917608b1b0f5b56573caa37a551bf2a8bad76704aa3616a1c6576d85a66074456d64eb2b26c4e886f2cc117a22cab2d6559375acc374aee7e5554e5a549ebaa0f5d5d8b30ec59675cd4bb26a57fd1016d8784caa04761ce3b0e11da7764c383f69421b4ae395460f4430754983b0265d87336c3b8166185d10c2d638dacc37d6616bae627da70a6dbbccaa883aa479da7386d39a369eacb3072da74dea925f54927aa4fa9a96c4d4a635492daa487d5277acac6d2a129b0ee32aa692daa6fa2129aeb20987732cc42565644b3122593902cc48165640b271f59845ed3b176a18bd10e02aa6f95537d6998dd114e597832cbd2165db6b2ed4973792cbbc565e9ab2ef85976aacbc3565c2bae6c2d866e955378aa9c0576df2bba6adbd6d6a1aeb4f5c5b8a32d3bb4aa9ceb714a5b37095512b2e1ca5554e5a76bac3b7e61dbd30e35d860c6c385361cbbae6a7d73606d439caa9bab3034e886ead437560c6dd1120954a72db99b5c431aa498d824aec3b625d5f0b0ed89727d2c126360d31d10e559872ad40d75946bb0a34da81a6d30d36946bd1035d5372cd499361d1db0ef2973952dbbcd69ccdaa467da538eb2c2964d85acac0d6560eb29ab5967ab313d2bbaa2d9cf565c2f96b1859341eb2a239554fb0f3a98353ec2a9f60d2db0eb3da74b6c12a361d1faa53d5a8a12d3cf569d13c44b4da85a6d3ad369557cab3a5a55a72acee60d69b0eb4d759e2d3ce969d4faeaa7d539dc5d4ea2e92dcab462aa53f2aa5b5cd2db06a8d759e45d4f8aa92da64a7da5b02d2aaf60ac0b71605a853ed458168d4fb476098247f112a360d1fb0e8fd7547eb9431619fab0cd45a89b4533bd6a1af3750d5860ae5d3b16a1beb51295b6096b2c4658df72c6d89631b6c339e58dd0b62d15b69b2c335165a46b2cff9630a6bb053595bcb51305b197ad8b4e6e9df37414db60aedb391699c6b4ce396271adb3566e9bb3745ddb1722d43496d9a52c513586874aa399619deaecde57634ed31a35d8d1b4cb6da16dad32db699e4b4d3b9545e6b14f2691fb2a867dba834aa04769ae52a9749549d4aa5825526ab3067d875ef2a977954cfb0467eaa33edc19f6c8cbb6c65d76336b299b588cbac52f5b2ba2c95ad656d6b2ed5592b9acbdc else 0xe15986b2cab3769d6db4e10d6508ed2b566e650b271359363ed42376a02dac53b987adacc571662b8b5016d760aebb5096627d3055b982a12d44e96a157b0f3e5a89dad451a609baaecd79635b6bb2db58e74b30b5d639f2cc51966155b0e15d630f6b156e61c2dac61ed760f6b2ad75dae8b2b72597b92ca99358e1330f695b2b11553dcaa9f0554db2bb93acba3b69905b4cf62aa66f554c16e165b0ef62bb2ee5aba260dd4b6d2f5b87b2dbbda2e9d0b705debba2acbd166a5f2b2af99546b4c3b5660abeb70d998213ed350a619ea57616d82acacc362551b116f4e5b599acc4d1661d730ed8982a6adaa0f6142db06f89546e4dca2fa203db0514598822cc35caee28950d78ba33642af360983b0466d82a72d9b5d69431b052a5b20a65d36a69c81b6666e880c74419b2a296b67385b2357443ed661d4b66d79b13bed4455660319506de8843f441b72166eb66ef9877b25d2032d4c5b0eda8ba5b6b9bd965cd1d1070e883ced41c36a0d1b50d05965b6d1be1654cbb04f858369ad43596e1aab70d55986bacc3d0aeda0576b))))
def step11 (i : Nat) := packedAt step11D (i*21) 21
def ruleOff11D (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x879a1e547911e2c7861e0477d1de47751dc076a1d9075c1d587501d287471d0073a1ccc72d1ca47231c747121c347071c086fa1bc06ed1ba86e71b906e11b786da1b586d21b3c6cc1b286c01ae06af1aac6a71a8c69f1a5468f1a0867919b8665198865f19706591958653194064d1928647191064118f863b18e063518c862f18b06291898623188061d18686171850611183860b182060518085ff17f05f917d85f317c05ed17a85e717905e117785db17605d517485cf17305c917185c317005bd16e85b716d05b116b85ab16a05a5168859f16705991658593164058d1628587161058115f857b15e057515c856f15b05691598563158055d15685571550551153854b1520545150853f14f053914d853314c052d14a85271490521147851b1460515144850f143050913f44f913d44f113b44eb13a44e713944e313844df13704d913584d313404cd13284c713104c112f84bb12e04b512c84af12b04a912984a3128049d12684971250491123848b1220485120847f11f047911d847311c046d11a84671190461117845b1160455114844f113444b11244471114443110443f10f443b10e443710d443310c442f10b442b10a44271094423108441f107441b10644171054413104440f103440b1024407101440310043ff0ff43fb0fe43f70fd43f30fc43ef0fb43eb0fa43e70f943e30f843df0f743db0f643d70f543d30f443cf0f343cb0f243c70f143c30f043bf0ed43ac0e8c39a0e4c38b0e0c37b0dd436e0dac35f0d5c34f0d303490d183430d0033d0cd43320cbc32c0ca43260c8c31a0c5c3140c4430e0c2c3080c143030c042ff0bf42fb0be42f70bd42f30bc42ef0bb42eb0ba42e70b942e30b842df0b742db0b642d70b542d30b442cf0b342cb0b242c70b142c30b042bf0af42bb0ae42b70ad42b30ac42af0ab42ab0aa02a50a8829f0a702990a5828e0a282860a0827e09f027a09e027609d027209c026e09b026a09a02660990262098025e097025a0960256094c2500934249091424108f823c08e423608cc23108bc22d08ac229089c225088c221087c21d086c219085c215084c211083c20d082c209081c20508041fe07ec1f707cc1ef07ac1e7078c1df076c1d7074c1cf072c1c7070c1c006f41bb06e41b706d41b206bc1ac06a41a6068c1a1067c19d066c1990658193064018d063018b06281890620187061818506101830608181060017f05f817d05f017b05e817905e017405c016c05981600570158054c14b050c13b04cc12e04a41250478116044810c041810204000f803bc0ec03a40e6038c0e003740da03580d203380c803100c002f00b802d00b002b00a8028c09d0264095024408b021808101f407901d007001ac066018405c01640530140048010803a00d003100b0026007c0180054012003c00c0014000 else (if i < 2 then 0x449c126c499926049652564941249490d23d48dd23048ad226487d219484920d482120347fd1f847c91ed47a51e5477d1d947591d3473d1cb471d1c346fd1bb46d11ac46911a0467519a465d194464518e462d1884619183460117d45e917745d117045b11684591161457915b4561155454d151453d14d4525145450513f44f513b44e513544c512d44a9127448d11f446d117444d10e442510443fd0fb43dd0f343bd0eb439d0e3437d0dc43650d6434d0d043350cb43250c743150c343050bf42f50ba42dd0b542cd0b142bd0ad42ad0a842990a442890a0427909c4265096424d090422508441fd07841c906c419d0614171057414504b411904140ed03440b9029408d01f4069016404900e40290064008ffb3fd4fef3fa4fe33f70fd53f38fc83f08fb93eccfae3ea4fa43e7cf993e54f8f3e30f893e18f833e00f7c3de8f773dd0f713dbcf6d3d9cf613d70f553d3cf483d04f3d3ce0f323cacf263c84f1b3c54f0d3c1cf013bf4ef63bb8ee83b8cedd3b58ed33b2cec33af0eb73ac0eab3a98ea13a70e963a3ce873a00e7a39d4e6c398ce5f395ce513924e433900e3938c4e2a3894e1e3854e0d3810dfd37d4df037acde63778dd8374cdcd3718dc036e8db336b0da53684d9b3650d8e3620d8235ecd7335b4d663568d54352cd4534f4d3534b4d27348cd1f3468d113430d063408cf933cccee33acce53378cd8334cccc3318cbf32e8cb532b8cab3294c9e3264c943238c883208c7d31d0c663164c4f312cc473108c3c30dcc2f30acc263084c1c3058c113034c0a3010c002fe8bf22facbe52f8cbdd2f58bd02f2cbbf2ee4bb12ea4ba52e84b9d2e64b952e44b8d2e24b852decb772db8b682d8cb582d58b542d38b4b2d20b452d08b3f2cf0b392cd8b332cc0b2d2ca8b272c90b212c78b1b2c60b152c48b0f2c28b082c18b042c08b002bf4afa2bd0aef2bb0ae92b98ae32b80add2b68ad72b50ad12b38aca2b1cac42b04abe2aecab82ad4ab22abcaac2aa4aa62a8caa02a74a9a2a58a922a3ca8c2a1ca852a0ca8129fca7d29eca7829d4a7229bca6c29a0a642984a5e296ca582954a522940a4e292ca492914a432904a3f28f4a3b28e4a3728d4a3328c4a2f28b4a2b28a4a272894a202860a152848a0f2830a092818a0327f49fb27e49f727d49f227bc9ea27909df276c9d6273c9ca27189c326f89b926c89ab26989a02670998264498a261097f25e097325bc96a259095f2560951252c94524f493524b8928248c91e2468916244890d242490524048fd23e88f223b08e623808dc235c8d123248c122e88b222b08a6228489b2260894224088b221c88121ec87421b8869218c85c2154850212c847210083b20dc83220b4827208c81f2068815204080a20107fc1fd87ef1fa07e11f687d31f387c81f007b91ed07ae1e987a11e7 else 0x99de27771dd87751dcf7731dc77709dbc76dddb276adda77689d9e7669d93763dd8a7615d7e75e1d6f75a5d617565d547541d4d752dd467505d3d74e1d3274b5d28748dd1f7471d197459d137441d0a741dd0173f5cfa73d9cf373c1cee7399ce27379cda7361cd07321cc472f5cb872c5cab728dc9c7259c90722dc867205c7d71e1c7471adc637179c587145c4b7109c3a70d1c2f70a9c237079c19704dc0e7025c046ffdbf96fd1bef6fadbe66f89bde6f61bd36f39bc96f0dbbf6ee5bb36ec5bad6eadba96e9dba56e81b996e49b8d6e1db816dedb776dc5b6d6da5b656d85b5b6d59b516d29b446cf9b396cd1b2d6c95b1d6c61b136c41b0d6c29b076c11afd6bc9aef6bb1ae96b99ae36b81add6b69ad76b45acb6b11abe6addab26ab1aa96a91a9d6a59a946a3da8b6a19a8269f5a7869cda6e69a1a606965a53693da4c6915a3e68eda3768cda2b6889a1d6865a136839a0a68119fb67d59ef67a99e567819db67559cf67299c466f99b766c99ac669d99f6665994664198b661998065ed97465b996a65959616579957654d94d652594364f193764c992d64a1923647d9196451910642990463f18f863c98ed63a58e463818db63598d163318c763058bc62d58b162bd8ad62a58a3627d898624d88d621988061ed87561b5865618585d61618546135849611183e60e583460b9828608d81c605180f60218025ff57f85fc57ea5f897dd5f617d25f357c85f097bc5ed97b25eb97a95e9179f5e657965e4978e5e297865e0d7805df17785dd57725dbd76c5da57665d8d7615d7575b5d657575d3d7485cfd73b5ce57375cd572f5cad7295c9d7255c8571d5c657155c4570f5c3570b5c257065c0d7015bfd6fd5bed6f95bdd6f55bcd6f15bb96ec5ba96e85b8d6de5b656d45b396c95b116bf5ae96b55ac56ad5aa16a35a796985a4568b5a1567e59d966f59a9666597d658595164f5929645590563d58e163358b9628588561d5859612583960558055fd57d95f257b15e657855de575d5d157395cb57215c557095bf56f15b956d95b356c15ad56a95a5568d5a1567d59d5665594564158b561958055f557a55d156f55a1562557955855515505531548551154054f153854d553254bd52c549d5205461512543550053e54f253b14e753894df536d4d753494ce53214c553094bf52d94b152a94a15275498524548a521547f51d946f51914605175458514544d511543f50f143650b5426508941d5061411503940750053fe4fed3f74fc53ef4fb53e14f6d3d64f493cd4f213c34ef53b64ec53ab4e8539c4e5d3914e353854dfd3784dc136b4d9935f4d613514d313474d0133c4cd93314cb53284c8d31d4c5930f4c253024bed2f74bc92ed4ba12e24b752d84b4d2cd4b212c24af12b64ac52ad4a9d2a14a712974a4928d4a1528049e927)) else (if i < 4 then 0x849e0277a9dda7719db27679d8a75e9d667549d3e74b9d1a7429cf27379cc672e9cae7269c8671d9c667139c3a7099c167019bf66f99bd66f39bc66eb9b9a6e29b7e6db9b5e6d49b3e6cb9b1e6c29af66ba9ada6b39abe6ab9aa26a29a7e69c9a666949a4268a9a1668099ea67599c666c99a26629972656994264b991a64298f663898ce62e98aa625988261b985e6139836608981260097f25f697c25ec97a65e6978a5dd97625d397365c7970e5be96ea5b596c25ab969a5a19672597964a58d962258395fa57995d656f95a6564957e559954a54c951a54194f253794c652c949e5229476518945250f942a50694024fb93de4f293ba4ea93964e093724d793464cb93124bd92e24b392ba4aa92964a0926e496924648c921e48191f247791ca46d91a6464918245a915a451912e447910e43e90e643490be42a9096420906a414903a40a901a4008fea3f68fc23ea8f9a3e08f723d58f463cd8f263c58f023bb8ee23b58eca3af8eb23a98e9a3a38e8239d8e6a3978e5238f8e223838dfa3798dd23708db23688d9235f8d6e3578d5234f8d2a3478d0e33f8cee3378cca32e8caa3268c8e3208c763198c563128c3a30a8c1a3038bfe2fa8bd62f18bb62e98b9a2e38b822dd8b662d48b422cc8b222c48b022bb8ada2b18abe2ad8aae2a98a9e2a58a8e2a18a7e29d8a6e2998a562918a3628a8a1a28289fe27a89de27389be26c89a2265898a25f896e257894e24f892e247890e23f88ee23888d223088ba22c88aa228889a222887e21a8856210882e206880a20087fa1fa87d21f087b61ea879e1e3877a1da87521d187361c887161c286fe1bc86e61b786d61b386c61af86b21a9869a1a3868219b8662195864a18f862e185860217d85e617585c216b859a1618572157854e14e852a147850e13f84ee13784ca12e84a6124848211c84621138442109841210083f60fa83e20f483ba0e983960e0836e0d683460ca831a0c282f60b882ce0ae82a60a4827e098825208f822e086820607d81e207381ba06a819205e8166054813e04b811a04180f203880d203080aa026808201c8066015804600d80260048005ffc7fddff27fb5fe87f95fe27f79fdc7f69fd87f59fd47f49fd07f39fcc7f29fc77f15fc37f05fbf7ef5fbb7ee5fb77ed5fb37ec5faf7eb5fab7ea5fa77e95fa37e85f9f7e75f9b7e65f977e55f937e45f8f7e35f8b7e25f877e15f837e05f7f7df5f7b7de5f777dd5f737dc5f6f7db5f6b7da5f677d95f637d85f5f7d75f5b7d59f4c7d21f417cedf357cc5f2b7c99f217c71f167c45f0a7c11efd7be5ef37bb5ee77b8dede7b61ed37b35ec87b11ebf7ae9eb57ac1eab7a9dea17a6de957a45e8a7a15e7f79e5e7379b9e677981e587951e4f7921e4378f1e3678c1e277885e1c785de127839e087809dfc77e1df277b9dea77 else (if i < 5 then 0x4c312cc49f122c47b119c457111c433107c40b0fdc3e30f3c3bb0e9c3970e2c3770dac35b0d1c3330c9c3130c0c2f30b7c2cb0aec2a70a4c28309bc25b091c23708ac21b080c1eb075c1bf06bc19f064c18305bc157050c137048c10b03ec0e7034c0c702cc09f023c07f01bc063015c04300dc02b006c00efffbfeaff3bfbefebbf9efe3bf7efd9bf56fd1bf36fc9bf0efbdbee6fb6becafaebeaafa5be8af9dbe6af96be4af8dbe22f84be02f7cbde6f76bdcef70bdb6f6abd9ef65bd8ef61bd7ef5bbd5ef52bd36f48bd12f41bcfaf38bccaf2ebca6f25bc86f1cbc62f14bc42f0bbc22f04bc06efbbbe2ef5bbc2eeabb9aee2bb76edabb5eed3bb3eecbbb1eec3bafeebcbae6eb6baceeafbab2eaabaa2ea6ba8ee9eba6ee98ba56e92ba3ee8bba1ee83ba02e7db9eae78b9dae74b9cae70b9aee68b98ee5eb966e56b94ee51b93ae4bb922e45b90ee3db8dee33b8c2e2ab89ee24b886e1eb86ee18b856e10b82ee05b806dfdb7e6df6b7c6dedb7a2de3b77addab75edd2b73edcab71edc3b6fedbbb6e2db5b6cadacb69ada2b67ed9ab656d8fb62ed88b60ed7eb5e6d75b5c2d6cb5a2d62b57ad5bb55ad53b53ad49b512d3eb4e6d35b4c2d2db4a6d25b482d1bb462d13b43ed0bb41ed03b3fecfbb3d6cf0b3aece6b386cdcb362cd3b342ccdb326cc5b306cbeb2eecb8b2cecadb29aca2b27ac9ab25ec93b23ac89b212c7fb1eec77b1cec6eb1aec66b18ec60b172c56b14ac4eb12ac46b10ac3fb0eec36b0cac2fb0b2c27b08ec1db06ac17b04ec0fb032c06b002bfbafdabf2afb6be9af92bdfaf6abd6af4abcdaf22bc4af02bbbaed6bb0aeaeba8ae8eba0ae72b99ae5ab93ae3ab8aae1ab82adfab79add6b70adb2b67ad92b5ead6ab56ad4ab4dad26b45ad0ab3dace2b33acbeb29ac92b1eac62b13ac3ab0aac1eb02abf6af8abd2aefabaaae5ab7ead9ab56ad0ab2eac7ab0eabeaae6ab4aabeaabaa9eaa2aa7aa9aaa5ea94aa3ea8baa1ea84aa06a7ca9dea72a9b6a67a986a5ca962a54a942a48a90ea40a8f6a38a8caa2ea8aea26a882a1ca85aa0fa832a07a80a9ffa7f29f9a7d29f0a7ae9e6a78e9dea76a9d5a7469cda7269c5a7069bda6e69b5a6c69ada6aa9a4a68299ca652990a636989a616982a5fe97ca5de973a5ba96aa59e962a57a95aa55694fa52e947a50e93ea4e6934a4c692da4a2925a48291ba45e913a43a909a4128ffa3ea8f6a3be8eaa39a8e1a3728d8a3528d0a32e8c6a3068bca2e28b5a2ca8afa2b28a9a29a8a3a28289da266894a23e88ba21a882a1fa87aa1da873a1c286da1aa865a18685ca15e852a136849a116842a0f6839a0ce82fa0aa827a09681fa066816a04280ca022805a0067fc9fde7f19fb27e89f8e7e09f767d99f527d09f327c79f0e7c09ee67b49ec27ac9e9679e9e5e7939e4278d9e267 else 0x371edc63715dc4b70edc2b705dc036fadbdf6f4dbc76eddba36e3db7b6dadb5b6d1db376c9db176c1daf36b7dacf6b0dab36a8da8f69fda6b697da4768cda1f684da0767ed9ef678d9d7671d9b7668d98f65ed96f657d94b64dd923642d8fb63ad8db630d8af625d88361cd863613d83b609d813600d7ef5f5d7c75eed7ab5e6d7875ddd7635d3d73f5ccd71b5c2d6fb5bad6d75b0d6af5a6d68f5a0d66f596d64f58fd627584d5ff57bd5df572d5b7568d59355ed56b556d54b54cd51f542d4ff53bd4df534d4c352cd4a3523d47b51ad457511d433508d413501d3fb4fad3d34f2d3b74e9d38f4ded36f4d8d34f4ced32f4c8d3174c2d2ff4b9d2d34add2a34a2d273496d24348bd217480d1ef476d1c746cd19f462d17745ad157450d133448d113440d0f3437d0cf42fd0b3428d09341fd06f417d04b40ed027405d00b3fecfef3f8cfd73f0cfaf3e6cf8f3e0cf673d5cf433cbcf1f3c3ceff3bacedf3b4cebf3abce9f3a3ce7f39bce57391ce33387ce13380cdf3377cdcb36fcdaf368cd93361cd73358cd4f34dcd23343ccf7338cccb32dcca3324cc8331ccc67315cc4730acc172fecbe72f5cbc72eccb9f2e3cb7f2dacb532cfcb2f2c7cb0b2bdcae32b4cac72aecaa72a5ca8729dca63295ca4b290ca3b28cca1f284ca0327cc9eb273c9bb268c99325fc97725ac95f252c93724ac91f244c90723ec8ef237c8c722bc89f222c877218c84b20dc827204c7ff1fbc7e31f5c7bf1e9c79b1e3c77f1dbc75f1d4c7471cec7271c4c6ff1b9c6d31b0c6b31a7c68f19ec66f198c64f18ec623184c60317ac5d7170c5af166c58715cc55f153c53f149c51313fc4eb136c)))
def ruleOff11 (i : Nat) := packedAt ruleOff11D (i*14) 14
def ruleEntry11D (i : Nat) : Nat := (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0x26031b0006b731b0006b731b00023331b00003331b00031b21a00031b20700007015a0da31b00e4874830006b731b2030006b731b2030006b731b2030006b731b20300031b00031b00031b00031b00031b00031b00031b00031b00031b00031b00031b00031b00031b00031b00031b00031b00031b00031b00031b00031b0003ff41a0003ff41a0005ff21a0005ff02e21a0005ff02e21a0005ff01f21a00071b21a00011a0006b77190006b77190006b77190007190007190007190007190007190007190007190007190007190007190007190007190007190007190007190007190007190007190007190007190007190007190007190005ff06830f0005ff30f0005ff30f0003ff41a40a0003ff41a40a0003ff41a40a0003ff41a40a0003ff41a40a0005ff21a20a0005ff21a20a0005ff21a20a0005ff21a20a0005ff21a00a0005ff21a00a0005ff21a00a0005ff21a00a0005ff21a00a00006848700041d2870002870001870001870001870003ff4830003ff4830003ff4830003ff48300023348300001f4830004830004830004830004830004830005ff2830005ff2830005ff28300021a18300000000000000000000000000000000000000000000000000000000000000000047842451b00027805a2240002782562240002784c922a2242030002784c922a22420300027822431b00027822431b00027824c2242030003f506a75442342102051b00006a6c974112312102051b00007306875404a04003f02400007306805304a03f02401600026325a04222400007925a04222400025a23d22400007306a05804502051b00007d4f504e34904232a7210000f50420ba00005804e0420250240000f83de04203e0240000424244210000420006f515a55404003f02451b00005a05844203a02e12402401f00004242400042441d00042451b00042451b00042451b00042451b00042451b0004f525922400027525f22400025f23722400005f4c922a22420f00026325e22400026325e22400025e22a22400007825a22400027525a22400025a23922400027505a22400005f05a2240000792590422240004f525904203822400025923d22400027525622400025624322400025603f22431b20f0002634c92432240002634c924322400027824222400027824222400026b2590422240002590422240002632560422240002632560422240000792490422240002632490422240000422240004f525603a22420f00022431b0003f506a05804502442101200005804502602411b00006a05804504002402001200004e03e02451b08300002451b00042442151b01200005304a03f02401f0006f504a5c903f02401f0000e17541b772102071b00042451b00042451b00042451b00042451b00015a55403f02451b0160007c67b702411b else 0xb21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a0002780f80730700e015a0da02071b00c08700071b41a48700071b21a28700071b21a28700071b21a28700071b00071b00071b00071b00071b00071b00071b00027661b00027661b00027661b00027661b00045a61b00045a61b00025a61b00044a61b00044a61b00044a61b00044a61b00024a61b00043a61b00043a61b00043a61b00043a61b00043a61b00043a61b00043a61b00042261b00042261b00042261b00042261b00042261b00042261b00042261b00042261b00042261b00042261b00042261b00042261b00042261b00042261b00042261b00042261b00042261b00022261b00022261b00022261b00022261b00022261b00022261b00022261b00022261b00022261b00022261b00022261b00022261b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00061b00007b07005c45a0da04202351b00e00007b45a0da0d903e03502351b00007b0700da2c903502351b00e00007b45a0da2c903502351b00e0000730702e002f52151b00007306a2de02051b0140110002f506a06505c02502051b00006a2c904502502051b01400006a04502502051b00006a2c904402051b01100046051b00007a06c05f05a25443a02402351b00c00400007305c64103612402051b0004780f805803e02551b00c0004b951b0004b951b0004b951b0004b951b0004b951b0006b751b00006a06504424102802051b00042251b00042251b00042251b00042251b00042251b00042251b00007306935403c02502051b01700051b41a00051b41a00051b41a00051b41a00051b40300051b40300051b40300051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b00051b0) else (if i < 3 then 0x42402051b28700005844242402051b0001f50572c94420240200001f50df0442427210200001f50df04424262102000007306a0ca14202402000027806a0570420240200002e004202051b0000f86c604202051b0002f50610df0450425240200000f83d604242402051b00005804222402000006105804212402000047806505704202452102000004042202001f0000bd02000004e4b90200004b90330230200004b902000c00006a6d62b91230200003d62b94230200000ba02602071b00002602071b00002602071b00002602071b00002602001d31b0000680df42402001f0003e03d60424240200000693d604203e42402051b0000680df42402051b00007b04e22402031b00007b05822402031b00022402000005804564112402001f00006e05804212402000006804e04512402051b0002de03342202001f0000f71220200001d66b712202031b0000df6411331220200004780f80730650ca02502462102001b0000786210200170000786210200170870000780655210200000730da0b802452102001b0004780f80730650da02402001b00d00041d51b00041d51b00041d51b00041d51b00041d51b00041d51b0003ff41d41a0003ff41d41a0003ff41d41a00011d21a00011d21a00001d0004f50730580ca04002452102071b00007d0da05a35405322171b00007306a1c923a02e02402071b0004c671b41a0004c671b41a0002c671b21a0002c671b21a0000f80730da1c902462102071b00c0000530ca3c662171b0000730660650e30da0d10450ba62102071b00c0002780f806552102071b00c0870000730650620df0da0ba32102071b01700007a2780f842102071b00c08700071b41a00071b41a00071b41a00071b41a00071b41a00071b41a00071b41a00071b41a00071b41a00071b41a00071b41a00071b41a00071b41a00071b41a00071b41a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071b21a00071 else (if i < 4 then 0x2201300022201300022201300022201200022201200022201200006822220f00022201f20f00022220f00022220f00024223a22220300022200022200022200022200022200022200025a12200044c12200024c12200024212200023d1220002776b71220006b723312200023312200012241d00012220a00012220a00012220a00012250100012200012200002271b00002200062121a0120006210006210006210006210006210006210006210006210006210006210006210006210006210006210006210006210002e005852168700006505c04202352102001400042252100042252100042252100042252100042252100042252100042252100006a52102001728300052100052100052100052100022232100022232100007b4aa02031b00007b04e12402031b00007a0f80df0200000f81d60200000f80246210200000780650ca02001f2050000f71c90240200000f702001b0000f70200000f645a0200870000f60570230200000f607306804b6210200000f60730ca0246210200000f66210200870000f604b03352102000007b1f50200001f50730200001f51d602462102071b0001f51d662102071b11a0001f51d662302071b0001f50691c90200001f51c90330246210200001f562102071b0001f562102000047807325a02000007807307025a0200001f50731c90200000733c664272102071b0001f50731c90240230200000730ca0b80230200004780730e06210200000730ca0b802462102001b00007345a0da0b802402001b00007006c25a03a4aa0200003f506a3c90220200001f50691c90200004780f80670200000e12420200000e102071b0000f60df0200000f60df0da0200000df0da0200000df0580200000df1240200000df02041d0000df0200004780730de45a0240230200000f60da62102001f0000780700da4d60200000780da0534c90200000da4c90200000da0531c90200000650da2427210200000650da04243a02302001f0004780650da04262102001f0004780650da0420200110004780650da0580b80240200000da0b80246210200000da64262102071b0000da2c95210200000680da0425210200000da0200000580420200000582b902000005812402001f00005802051b0000585c603e02031b0002780651d60ba0200000f81d604562102071b0001f51d60240230200002780701d60200000731d64420240200002780651d60420240200000681d60420246210200001d662102011a0001d60ba0200150002c90200150005d61c964262102071b00004502e02011b00004502e02000004512402001f00004512402001f00004502242102001d00004502051b00004502051b00004512402031b00004512402031b00004512202031b0000692de44202051b00005844202302051b00007204e442 else 0x40160000f807407306805f05b0452240000795de4d604222400007e0f805955403d22400e00006706205955404e24222400007c06f4c924213322400e00006e05803e22431b00006e22431b00006e22431b00007e06e05a12400007e07306804a03a12402000c00007d2f512452100007b6de03612431b0000f71d61240004f507305804a03e03a12400c0002f506e05a0581240002f50581245210000df12400007b06105f0581240004f505f0da03f12468300006605f0da1240160006de05312452100007e6de4c912402001f00006625a03d1240160000795e025a03f4b912400007715a64112400015a1d66b712400006515a64103a1240040000da1240000da0d96b712a1240000720da05a0582411240000690582411240006f52d61241210006c90446b712412100007205a4c90451240000f807805804512400005804512412100007807006805704a44212400b0000f807306806545a05705344243a12401f00a00400047806e0da05344a6c944203312451b00a00400007806e0650da04d0474420331240000780421240006de0421240000690580421240000680580421240160000696d60421240002c96410400331245210200001d61b912400007b0581331240001f51d61331240001f51d613312400006e0586411331240006c964113312400004212402000012441b00007b0da05712431b0000da12431b0005e00da12431b68300007e0f607305f25912401600007b2770da3d612401600006525903d12401600012400006605b4c902430300007d0590514c933902400007a05b2c902400b0002c902451b00e0000780652de0da04d44a04003302d02451b0000da02431b4874830002770da04c0240164874830000f805f1590240164874830003ff42341a0003ff42341a0003ff42341a0003ff42341a0003ff42341a0005ff22321a0005ff22321a0005ff22321a0005ff22321a00007c47805f45a04512351b00c0040006de12412300007c07706d04d04543a12351b00007c04564112412300007c04512412300007706d05a04d04404243a02351b01500002300002300007d0f806604042200003f42200043342200043342200043342200043342200043342200042252100042252100042261b00042241300042241300042241300042241300042241300042241300042241300042241300042201300042240f00042240f00042240f00044243a4224030004220004220004220004220004220007ff2220007ff22200017706c06605122200017706605a22200003f22200003f22200003f22200003f22200003f22200023322200023322200023322200022232100022261b00022261b00023a2220160002220160002220160002220160002222130002222130002222130002222130002222130002222130002222130002))) else (if i < 7 then (if i < 6 then 0x6a0d91d61330170001f506a1d61336870001f506a1d61336870001f506a1d61336870001f506a1d61336870001f506a1d613302e0200001f506a1d613302061d0001f506a1d613361d00c0001f506a1d613361d0001f506a1d613361d0001f506a1d613302402000c0050001f506a1d61336830001f50691d61330001f51d61336230001f51d61336230001f51d61337210001f51d613362300c0006b713321a0003f53d613342400e00013321a00013321a00013321a00013321a00013321a00003301d51b0000330003ff4aa0003ff4aa0006b71aa0001aa0001aa00006a05302912252100006a05302912252100005304203e02900006a05302f02912452100007805304502912400006a05304502912452100007805304502912430f00002900e00d0000f80d10330280000f70730d10280240001f50730d10280240200000730d10420280000680da0420280000650d10420330280000f70d10330280200000730d14c90ba0280240200000730d114202802400007e0262220170120003f50264240000731d60ba02602471b00007b47745f0d90330260240000720610df25a0260005f525a02602400007b0d902642251b0000d90ba02602502401f0003d602600047706805a5c944252a0260004780574424b902642401f0000730df44202602401f0000f60d924202600004e03e02642401d51b00003e02601200500002642202001f00002602402001b00002602402001b0001f50730ca02671b0001f50730ca02602471b0000730680c90ba02602471b0000680df0d602602471b0000df03302602471b0000f70da02671b0000730680ca0ba02602401f71b00007e06845f52a02642201f01600002601200e00007c07845905704242450300007b0da05842451b00007a0f845904e0420334240000f807345f52a4240000f842400007806e45f0da05842400007806805804a43d52a4240003f504e13302542451b0003f542451b00e00007e06604e0450ba42400007e0f807306a06845f45942400007b06745f0da05803342400006145f0da0d904203302d4240000780660df3d605142400017706e05f0da0580334240003de2d60424240003de42451b00e0000680da0424240000680660da23b53903342400006e0da05842451b0003d642451b00e0000f804e04542451b00006f05a5c944204242400006904e0420254240003d603e02542451b0003c603e13302542451b0000693c603e02542451b00006904e03e1330254240000f842451b00006e0da0d942451b0000da0d904202d42451b00006e0da05842451b00004e0450ba42451b00007a07706f22401600007906e05804903e2240000f806805724c32a22401f00007d5f504222400c0005f50df05a3d603f22400007e0f607306805f15955405322462148700007706c05f22 else 0x534c903e32a00006725924903e1240003751515c603e00005744203e51b00005744203e02400044203e03302400006e04d03e03543312441d00003e02502341d0003f53d603e42451b0000693d603e42451b00004e03e42400004e03e4240003f504e03e42451b00006904e03e42451b00006904e03e13342451b00003e42400006b05804203e22400006b04e04203e02f2240000636d604203e22400006205f03e02d2240000720625c903e2240000725c903e03d03022400006c5c903e22400004203e02d22400006805905804203e1240000696d603e12431b00006e06205804903e12400007d03e33762100007c03e32a52100006e04e03e5210000f703e41d00007204e03e41d51b28700006805703e41d51b0000cc03e41d51b0000cc03e41d00003e02e41d00006825403e02441d00006804e03e41d51b00003e41d00003e41d00055403e01d0004c903e01d00003e4aa01d00003e22401d00003e12401d0002c903e51b0003f504e03e13342451b00007c17504203e13332a31b00006e55404e03e72131b10700003e22431b0000bd41a0000bd21a0003ff43a00043a61b00043a61b00043a61b00043a61b0000ba21a0000ba0006b941a0006b921a0006b921a0006b921a0000684b90000684b90000614b921a0000614b921a0004b923321a0004b922321a0004b941a0004b941a0004b941a0004b941a0004b941a0004b90004b90004b90004b90000772b941a00024c2b921a00024c2b921a0002b90002b90002b90002b900023871b21a00023871b21a00023871b21a0003ff6b70003ff6b700023d6b721a00023d6b721a00023d6b721a00003d6b721a00003d6b721a0003ff6b743341a0005ff6b723321a0003ff6b742341a0005ff6b722321a0006b741d41a0006b741d41a0006b741d41a0006b741d41a0006b742261b0006b742261b0006b742261b0006b722261b0006b761b0006b761b0006b761b0006b761b0006b761b0006b761b0006b70006b70006b70006b70006b70006b70006b70006b700043a5b700043a5b70005b70005b70005b70005b70005b70005b700023a3b70003b70003b70003b70003b70003b70003b70005ff3370005ff3370005ff3370005ff33700005804503512252101700005804503502200006a05804203500006a05804203502471900006a05804203502400006a05804203502400005804203571900006a3c90420350250000580420351210002c924103571900005804203502e1240002f52c903502252100003502e02051b00003502e02051b00006a05803501d71900004e03e03502401d31b00005804503512211b00006a2de03571900006a03c03571928700006a03571900006a2de0357190003ff43341a0003ff43341a0003ff43341a0005ff23321a0005ff23321a0005ff23321a0001f5) else (if i < 8 then 0xb21a00024271b21a00024271b21a00024271b21a00024271b21a00024271b21a00024271b21a00024271b21a00024221a00024221a00024221a00024221a0000f80571424240000730690da05814200c0000730690da05714202400c0000730690ca14200c00007306914200c00007e47607206706604e44a1420ba02351b00800006a0da05814202500c00006a0681d614202400c0000651d614202400c0000701d614200c0001d614201500c0000d11420000571421240001d614212400005814212231b0000571421220001f50736c914212200014241a00014241a00014221a00007d07b06175404253352440a00007d07704200c00007b2f55d604253352400007d07a06175404504252340a0003f506a04200007707004220a00006e05c45a0da04202300006a0cf04203601401100006a04203602800006a05804202501700007c07805f45a04203302300c00007805f15a04232100c00007706e05f0da44a04704203302401700006a3de0420002de0420001de04203e0ba0000700610df35a04232400015a0da04200007706705f05a04203302300007705f05a04202f00005a04200007705304a04203d00007d07705204203302402340a0002f506a0d10420360280000f70421240006c90426aa12400007c04203f02400007704203f32a0240160000420240002f575404404252352100004203e0ba52102000004252100004252100004252101700004204003a12101500004200004200007a06e05f0da05844a64103e03302301700006a0586410250140002f56415210140002f564152100007d04012452100007d04051b50f0000780df04052a00005804002401248700007006605504051b00900006405a0d10400000d104002842201b0000780620da04d14a04031b48748300037505a0cc0400000cc04002001b0005750cc04052a11b00004002811b00007806805755604042462100006f05304003342400007755604204003f02400006a05304052a12232101f0000771c904002000004012402001600006805304003312202000005704204002051b40300007c17504013332a31b00007d03e03d51b00007d03e03d51b00007d04203e33712a31b00007d03e31b0000f805f03e0302240000f844203e0240000f803e51b00007d17503e4aa00017535603e22400007404e03e03d12a00007406804e03e03a41d00006b04e04203e02f2240000724695c903e0240000f705b5c903e01d31b00006706205905803e12400006e05803e00006b05803e22400006b05803e22400016315e05803e00005805104203e12400026b0585c603e0002630585c603e00005804303e12400006605803e02401d0000583c603e51b00006c05803e11b50f0000704e025603e33700007005f55404203e00026b0cc03e2240000cc03e41d0003750 else (if i < 9 then 0x530bd0240000530bd02051b00007b0770534c90331240003f505303352a42462100006805304503902e12401600007005304062100005302402001f0000682de05302051b00005304402401f00007205364101f00007e06805301f51b00007707005303351b00007a55405312a31b0000531220160000da0d171b00027804e24222400007204e24222400006e04e04272100006404e04213332a00004e4240003ff44c41a0005ff24c21a0005ff24c21a0005ff24c21a0000cc21a0000cc21a0005ff04c21a0005ff04c21a0003ff44a00044a43d00044a41300044a40a00007924a00024a21300024a21300024a00027714a6b70000ca0000ca0000ca00007805f05a4c932131b00b00005f05a0534c903a31b0000f805f0594c923a31b01600b0004c921b21a0004c90004c90004c900004e3c902051b0060002c95210200002c90001c90001c900044c6c641a00044c6c641a00024c6c621a00004c6c621a00004c6c621a0006c60006c60006c60006c600044a5c600044a5c60005c60005c60005c60005c60005c60005c60005c60005c60005c600024a3c60003c60003c60003c60000d10450280240000720cc04572100007714a04512400014a04503a12400005804544202401f0000580454420240000cc0454420240000cc0454420240000ca0454420240002f55d604524200006a0450420000450420200000725d60450280000d10450284870000725d604502500007905f0450432240000725d604522400e2070000725d604522400d0005e05d604522400c0002630df04504322400c00006d05804502e12410f00c00007744c04502402301500005804512412300004512412300007c47744c04502402300006805304522211b01200004504212200004502402001f00004513312202000004502402001f00004502071b00004502071b00004502402001b00004502402001b0000f60d104571b00006804b04502471b00006805804502401f71b0004780df4420004783544424b90332870000f844203e0000f844203e0000f80730680ca4420400245210000f844200c0000e144202000007a0f80730df4420240000f80da4420000730cc4420245210000f804a44202f6870000f84424b94240004422220004f51de4423333230200003f544202f51b68700044251b00044251b00044251b00044251b00044241a00044241a00044241a00044241a00044241a00044221a00044221a00044221a00044221a00044202400e4830004420004420004420004420002780572420002784542420230002784c92420002782422b90240000f824203e00c0000f60d12423b70330000da2420000ca24200007a0e15c924202000027855424222400007b2f55c92425230200002f55d62425230200002420400200002f55d624252102000024271 else 0x5a02e0005f525a14222400027706825a24212401600007725a02f02e31b30f00025a00007706615a31b00015a24212400007915a04201600027715a6b700007715a64112400006115a44212400015a64112431b00027715a31b0160000f80da02462171b0000772e00da04c43a41f50f0000772e00da05143a1330000782de0da05303d0002de0da51b0000da44c0002770da4c923a01600b0000780da0534c903d31b0000da4c60000f80da4420000f80da4420004780680da4420337210040000780650da4420420337210040000770da04203f0000df0da0420000772de0da04203f0001de0da04203e0000da0420350006f50da44242401f0004770680da04c4420334242870000680da0424242870000660da5543390240000da4c902431b0000da1c96210200002780da71b0830000f80da71b0110000670da1540d171b0000780da0530c971b0000780da0c971b0000780da0d602f71b0000f80da03b62171b0004780e00da62171b2870000da0d602071b00007b0da03651b00e0002e00da13351b0000700da04203302351b00e0000680da03302651b0000da4c931b00e0000da4c931b0004f506605a03d0000f70d902471b00006a05803a0245870001f50df0581220000df0da0584c902471b00047705f0da0580530000da0581220000da05802471b0000da05851b00005835400006505f05805312210f00005805352100047805844202301f0004780584420004780df0584420230000680580536c94420240000580cc44202400005844202401f0000f60582420280000781de05804200005804c04212400005804212100006d0584d615103d00026b0585c603d0000581331240000df05802802401f00027805802e22401f00006806505805303a12451b00005812412300007a47705f0580230000700584d612200005812212100006a2de0585210000650585210000da0581c90200000580ca02402000005802402001b00005802402001b0000680df05871b0000df05802402071b0000df05871b0110000df0584c902471b0050000580207190002d60002d60001d621b21a00007e05533730f70100007b35e05500017507005504213331b00007216b05503e00007216305505103e00007205503e13712a10f00007205503e01f41d0000760550bd32a00007205504512401f00007216305524232a52131b00007216b05555403e12a31b00006a3542c90003542c952100007e0536b730f00007e05351b00007e05354131b30f1030004f505332a00017505332a22200006f06305304022200006105f0da0530000da05302001f00007a55405332a31b00006d05314213710f00007705304232a00006b0532420421330240000722630534c904304222400017505304232a00007205364112a12410f00006405354113332a00026b)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0xb0170000f82c951b0000f841b0000f80003ff4776b741a0003ff4776b741a0004776b71220005ff2776b721a0000f70730d102471b0000f71d61331240000f70da71b0110000f70d932171b0005ff07721a00027606200027661b00027661b00027661b0000f621a00007a4f506c05304a0004f501d00007e4f506e05a31b0002f506141a0002f54420002f543341a0002f55190002f55010002f50001f507305a05104c02f6870001f524221a0001f524221a0001f524221a0001f500007e4f507412401f10f0030001f507406834962131b01600007407306800007e4f507406812468700007e07405f01d00007e07405f04201f51b00007404c04030f48700007e4f507415a03d12a12400007e2f507412a1246870002f50746c912452100007e0741225212030000f70731d60240000f70730d101b00007a0730df0240000730df02400007a0730df0230000730df0230000730684de24a23a02400c00400007305804003a02462101f0000731d60450230000730d10ba02402000007345a0544420240200000735c603e12331b0000731d60406b702462102071b0000730de45a02452102001b0000730ca03b0230200000720df02471b0000720df72131b00007e07206f22400e00c0000790720df2240000770720df2240005f50720df6c922400006a05f15948300006a05f32a48700006a05804502200006a3c904502200006a3d644202051b00006a05804202000006a05804271900006a05804200006a3d604202000006a3d604200006a35604200006a05804202471900006a04202f0240003f506a02602200006a02602251b00006a3c902602228300006a02202000006a3d634102051b00006a35404502051b0000e10002f506141a0001e00001e00001e00001e00000780df1de0420000780680df45a0230170004770680df45a0230160000f60df0da71b0000770df05a0420160004780df4420330230000700df03602471b00026b0df2240001f50730df02e1240000df1331240000df1331240000df1331240000df1331240001f50730df12431b00007a0f60df71b0000f60df03671b00007a4f50730df02471b0000731e00df02471b00007a0e30df0da71b0000e30df0da71b0000650df03671b00007c0730df4c902471b00007d0730df02452101f71b00007d0730df02452101f71b0000720df32171b0000720df32171b0000df71b0000df41a0000df21a0000df21a0000df21a00007c0782e005f05a0580000f607306505f05a04423a0240170040006de41a0006de41a0006de41a0006de41a0006de21a0006de21a0006de21a0006de21a0006de21a0000795de0590422240000df2de05a05371b00006806645a0d104253900007945a44272151b00006645a44204202351b0005f525a0422240000770df25a31b0160002 else 0x13300a00848300007202000840300012202008a4030004331aa0082830004231220082830002f550100011a50100000e08a5010005010005010005010005010003010007ff0007ff0007ff0007ff0007ff0005ff01f0005ff0005ff0005ff0005ff0005ff0005ff0005ff0005ff0005ff0005ff0005ff0005ff0005ff0005ff0005ff0005ff0005ff0005ff0005ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff0003ff00007e0f805f22400007e07806c4e025a02f02e32131b00007e02970100007e04242462101f40a00007e05f05322420f00007e04233752100e00007e33702000007d0f74e031b30700007d0f731b00e00007d0f711b00b00007d0f701b40a00007d1f522201601300007e07d55404c00007d04324203022400e00007d14254101730f00007e07d05f04202400e00007d04203e00007e07d04203d02400007e07d04203d51b00007d04203e03d31b00007d04200e00007d03e03d02400007d03e13751b10f00007d03e03d48300007c24213303022400007c24322400e00007b2d623300007b1d613302400007a0585aa02400007a05802458700007a5d655431b00007a04e03432a00007a04e31b00007a5f525904202400007a05904203d02400007a0720d102802300007a02511b00007c07a06203022400e00007c07a07222400007a5e025905822400007a04e13303022400007a5c902522401d00007a15605031b00007a05313332a31b10300007a15904e13331b10700007d47805704202351b40a0002780df2420002785c91332230002785c904213322431b0002785c922431b0001780664596c903342400017806f06605122200007d0f806825a05300007a0f807305f45a03c51b0170000f84de05a04c03f0000f80de0da71b0000f80da0d60420000f80da1c90420000f80da0420000f80da2c952171b0000f84de0590534c90000f805844202300c0000f844201700007a0f805a4420140000f844200c0000f80670420000f80df0420000f805a0420000f805a05304200a0000f82c90420000f80425210000f80423210170000f84b70000f81c91336210000f81c91336210000f844203342400d0000f80581424240000f803342400d0000f80682596c90332240000f86de1240000f80580421240000f80421240000f80421240000f824c04203f32a0240000f82591220000f852171b0170000f82de05371b0000f806a0d104003371b0000f803e02571b01700007a0f80f70730da02471b00c0000f81f562171b00c0000f80730ca04002462171b0000f80730da02462171b00c0000f832171) else (if i < 13 then 0x51b00051b00051b00051b00051b00051b00051b00051b00051b00007332a31b00007332a31b0000690da31b00006931b0000584c631b0000584c631b0004c631b0004e06b731b4870006b731b0004b701f31b00013302f31b0004aa31b00032a31b48300002631b00002631b00002631b00022231b48f00022231b48f00022231b48f00012231b48700012231b48700012231b48700012231b48700002231b48300032a52131b00012131b00002e02031b00031b11a48700031b00031b00031b00031b00031b00002f71b21a00006811a0000622e002c11a0002e002f11a50100007302f02e11a00002c3aa11a40a00002f02071b11a00002c11a00a00011a00011a00006a6b771900006a0696b712471900006a12471900006a71900006a71900006a7190002de7190020002de12471900200012471900200034103c1230207190000207190007192870020000251247190020002f55190002f55190002de5190000585190002d651900051900051900051900051900051900022201600022201600022201600022201600022201600012202001608a00012201600012201600012201600012201600001628f2870000f671b01428f4870001e002811a09300002309300022271b09300002202009300006842271b0930000e042271b09300014242271b09300004242271b09300042211d71b09300042201d71b09300022271b09300013302f11a09300031b0930870004220130002220134870000e324c0100000e301020a00003601020a0000530cc00e28700013311a00e00006e02f00e30100006e02e00e50100002651b00e0002e000c2870001c951b00c0000d91c931b00c0003c600c0004b902f02001f21a00c00002852121a00c00021d00c48700051b00c00000c18300000c00006c02e00b0000f706533711300b0000cc6c641d00b00002551b00b00002e41d51b00b00002e41d51b00b00002071b08a00800002071b08a0080000f72f506831b00a48700006c11a00a00002c11a00a00000a28700428300000a28700428300000a2870042830000623c611d0080004e03b72230080000d152171b0080000404b721a5870004e06b723313321a58700023322258700002f0280155870002872835010002d602e41d0040002d602e41d0040005c600a0040003c612300a0040000615b71330040000615b71230040000615b70040005b713300a4870040005b712300a4870040000613b71330040000613b71230040003b713300a00400006c02e0040005aa11a00800400026941d51b0040000cc41d51b00400010f08a00400016b08a00400016308a0040004e02331330065830004e000658300002001d48700658300071b21a5830002c948300012202048300005851b48300011a48330100011a48330100002541d00e48300000c483000 else (if i < 14 then 0xa02071b41a0003c602221d71b4870000e32c602071b21a00004a0c671b21a00004a0c671b21a00004a0c671b21a0000c612202071b41a00007304471b11a00007304452a71b00007304452a71b0000400ba02071b0005f50bd43a71b00007303c71b00003c42202071b00003c42202071b00003c02071b00043a0b802071b21a0000df0ba42271b0000df0ba71b0001c60ba02571b0000ba02571b0000ba02571b0000580ba42271b0000ba42271b08a0000ba71b08a0000730406b971b0000730d943871b11a0000794761420b871b0000f76b702842271b11a0000d16b742202071b11a0005de02f71b21a00002f02871b21a00002f02071b21a00002f02071b00007302c32a71b0000735aa71b21a0000735aa71b21a0000735aa71b21a0000735aa71b21a0000735aa71b21a00007305b5aa71b00007306d4415aa71b0005aa02071b21a0005aa02071b21a0005aa02071b21a0005f502671b21a00007302671b0005de02671b21a00005702671b0000c602602071b21a00002602071b0000cc44a12271b0005b712202071b00800012271b08a00012271b08a00007d0cf02071b00007302071b21a0000f702071b21a0000e302071b21a0000ca02071b21a0000bd02071b21a00002071b21a08a0003f512202071b41a0003de22202071b41a0003de12202071b41a00071b00c2830001f571b0080000735c613371b0080005c603302071b0080005c671b0080000731e03c671b0080000733c613371b0080003c671b0080000682c602071b0080002c671b0080000733c65b713371b0080005b771b0080005b771b0080003b771b0080003b771b00800006802071b00800002011d71b00800071b00800071b00800071b00800071b00800071b00800071b00800071b00800071b00800071b00800071b00800071b00800071b00800071b0080000400b871b58700007a5f542202071b28700002071b21a58300002071b01658300002071b00c58300002071b00c58300042261b18f00022261b08700022261b0870001aa02261b00007b3b713351b0000f751b08a0002f513351b0002f551b00006a02f42251b0003e041d51b08a0002e051b0000df0ba51b0002de0da51b0002de0da51b0003d651b0040000cc24a02051b0003c613351b0003c651b0130003c651b00a0003c651b0003c651b0002c651b00004c3b751b0003b751b00a0003b751b00006802e51b00006802651b00002551b00400012451b0002de42251b0001e042251b28f00022202051b0170003c602051b00002051b08a00002051b08a00051b11a00051b01300051b01300051b01200006951b00e0002c602e51b00e00002f51b00e00002e51b00e00002e51b00e00006851b28700006851b28700007241d51b00400041d51b08a00400041d51b08a00400051b00051b00051b0 else 0x733c622202000007307202011a00006a2e06b702051b00006a02602061b0002e00202830000620e00204870000cc0200000cc02000014a1c90200000e15c602071b0005c602071b0003c602051b0000450424220200000444420200000420200002770d91c904002031b00003e0ba02061b0000f74b90200000f74b90200000656b702001d61b11a0000656b702001d61b11a0000625b702011d51b0080003b70202870003b70200003b70200000e002f02000002f02071b11a00002e02011a0006b702822202011a00002802011a00006a02602071b00002602071b21a00002822202011a00006a16912202000004412202000004444212202000003312202041a00012202051b28700002202048300042212202001f0000e102071b00003e0bd42202071b00002071b21a08a00002001d61b11a00800002061b00002061b0000735c60200170000680250200170003b702018f0003b702018f00002f02001f21a00c00006202000c08a00024202302000800002028728300002000c18700002000c1870001220202830000cc02050100002000002000005301f71b21a2830003e002541d48300004d2c941d0001c641d00007202f41d00041d00b28700041d0080003c621d00c48700002221d48700021d00c48700036021d18748300032a21d18748300006811d00011d11a48700011d11a00013311d48f00011d00e18300011d00c0005b702011d51b00800011d00800011d00800011d0080000730cc01d00800006a52101d00006a6b702801d71900002001d61b00800006501d00a48700007d0ca6b702071b00007d0e102071b00007c0ca71b00007c02502071b0000f60e371b0000f60df24a0c671b0005f543a02071b21a00007342202071b11a00007342271b11a08a00007307271b11a00007307271b11a00007307271b0000723600cc71b00007202071b11a00007202071b11a0000721e071b11a00007271b11a0001696b942271b00016905842271b00016942271b08a0000670e371b00006712371b0000652b702001f71b0000680640d171b00006806471b00006412271b00006412271b0000680641c671b4870000660e371b0930080000623b771b00006271b00006271b0000665e071b0005e002071b21a0005e002071b21a0005e002071b21a00007e5de0b842271b0005de44a0b871b21a0000da0cc71b0005f505871b21a0000580ca71b00005842202071b00005842202071b00005802071b21a00007305712271b00005744a02071b00005742202071b0005de0d142271b0000580d142271b00004d5c902071b0005d60cc44a71b0000ca42271b08a0000ca42271b08a0000ca02071b11a0000ca71b08a00004d5c942202071b00004d5c942202071b00004d5c902071b0000ca5c971b21a0000735c602071b21a0003f54c623))) else (if i < 18 then (if i < 16 then 0x42222271b00042271b00c48700042261b18f00003e42251b00042251b00042251b0003604c942231b00042209308700013342201300042201300042201300042201300828700042201300828700042201300828700042201300828700002842271b01658300002842271b01658300042271b00c58300042228f5030000f72220200000f62225870000731595c602622220f4870000730702225190000662220000662220000df23a2220160005d624223a2222030000580532220000532220000514c922201600006806504f02622200004422271b0002420bd23a02622200024223a4aa0262222030000422220000404b72224870000f65de03f22200003f22200003f22200003f2220000bd23a22201600003d2220130000614b92220120000614b92220120001332220004e01e032a22200032a22248f00022242121348300003822271b00003822271b00003822271b00003822271b00042222271b00042222271b00042222271b00042222271b00022271b00600005822231b00022231b00006a02622201748700023a22201600002f2220160005c624223a02622201648700022271b09300022209300007a22201300022201348700022201300022201300022201300024223a2220120004b922201200002f02e22201200002e2220120002220120004e02220873030002222135830002222135830001332222134830004770536b712202000007307012200007302f12200006a16912200046916312220a0002690616b71220000df0ba2221220000df1220000d11220200001630cc12220a0002421220000420ba22212200004003f12202000003d1331220000b812271b0004690616b71220004696b72331220006b72331221130006b722212261b0000615b71331220000615b71220000f805824c03f4b71220000404b712220a00032a12248f0000ca22212201700044c0cc12202000002c12271b00002c12271b00012271b01400012271b00c4870000f542212261b0000f542212261b0000ca42212261b0006b712231b00012231b00012231b00012251900012201600012201600012201600012201600012201600012208a0001225192870000cc24a0ca02200014a3c602261b0004421380220004382b752a02200032a02248300032a0260220000230224830002b702251b00002251b00002251b00002231b0000220930000694234226210002232226210003c622362100800006a3b752101400016906524c52100016906552101600004452128300024113352100013352100003613302b52100006a02652100006a6b71235212830002de42252100032a42252131b00052101400052100007006932171b11a00007a4380b832171b00022131b00047704402e0202830000f702011a0000f702011a0000f70200000f6040020000 else (if i < 17 then 0xf74b90001f506504c4b90001f50654b900a00006d0684b921a00006104c6c64b90040004420bd4b902f0004b912241d0000f70454b901d0004b911a0002f54b900c0003f52b90080000bd2b902000800014203e1b90220001b900c00004223871b01500023871b11a00013822201300003f0b842200003f0b871b00003f0b871b00003f0b871b0000794760420b871b00004443a0b871b0000440b842271b0000c603f0b871b00003f0b813371b0002f50b842271b0000b842271b0000b802271b0930000b871b0000b871b0002f503f03800003f03813300003f03813300003f03800003f03800003f0380004f503f03812a00014a1c66b702261b0005c66b722312321a11a0003c66b751900004a2426b70002426b70080006b711a0002c96b75190002de2426b700800007b0445b713300007b0445b713300003f5b702f0040005b70250040005b771b0080005b771b0080000441435b70040005b73010000441383b771b0003b75190003b75010002b728750100005b0d903671b0080000452330040000656b71330004c913302b0002f51331aa00013302f02500013302500044213342200013301f08a40300013341d08a00013311d00013311a00013302f02600e00013301d08a00013302011a00840300013300800013300800013311a00400013311a0040001330040005c62b70330200080000735c603000848300006702f2231230004e013302f30100024202f21a00024202f21a48700003e02f22300003f4b702f21a00002f02942202000007302f22262100002f12371b00007302f21a00002f02812301500002f12300a00400002f1130040000d602e71b00002c3aa12340a0000d95c613302b0260002420bd02c5aa00014202c5aa2130005aa08a00003613302d1aa0001aa31b00013302840f0005aa02800002800800007202600006c43313302600006723302600006702601600003e23302600003e02602200006a02612252100002602071b00007307202671b00002601f31b0000262220174870005aa02500002571b01608a0080000250200170004234222220004e022322200004212412351b00007042222200006602c4220000664220003de0ca03f4220003de0da4334220003de0da42241300005343a4220000580d142271b48700007c0ca4220170001e00ca42212231b0000ca42271b00c58300007c2c642241300007c2c642241300006d2424220001424220000bd0ba42241d0000b842271b21a0003b71334220120003b742201200003f0382b742200003f0382b742200003e0ba1334220000730b802c5aa4220000665aa02842271b00004042212200004002c42262100002f42202001700006d42271b00006d42271b0000ba02f42271b00002f02842271b00002f42202071b00002f42202071b00042222271b0 else 0x44200004444243a0200001de04444242202028700044203e43a00044203e43a00044203e43a00044203e43a00044203e02c0000de44204043a02000044243a32a00044243a02200044243a02200044243a02200005844243a02021a0000df44204043a02000004a4420ba0004420ba00044213821a00044213821a0000f74421330004420bd02f21a00044232a0000f744212200400044212200014a44202000044213821a0004420bd0250170000f744251b00b0003c64420080002c64420080004420bd0080004420080004420080004420080004420080004420080004420080004422870004420004420004420004420000f80652420000f806524200007024203602000006d0e124202000016906524202000006724200800006524200006524200007d5d644a2420200000530cf44a24202000004524202600007304424212200024203e23a00024203e23a0005c624223a02200024223a0ba00024223a02200024243811a00024202f42202000024252a0002420bd12200024212200024203e23a0ba02200024202200024202200024202802021a00024223a02f02011a00024243811a00024271b01000024271b01028700024201000024200c0000e02420080005c62420080005c62420080001c624200800024271b00800024271b0080002420080002420080002420080002420080002f52425070002424870002420002420002420001421b90002de1420ba42200014242200014251b0001420080001420080001420080000da05804200004202f42200004202e02000004231b00004271900004248700004200004200004200004200004200007364102c5aa0002de6410006410bd01f01e00007364132a31b0002f564101418f00064128700064100200064100006a3410002de3410000443410003410140003410000d904043871b1870000770400bd4b902000004003813300004003800027704052102009300003f03800003f03800003f42200003f42200003f42200003f2220005de03e00003e0bd0ba02200003e0ba02061b00003e0bd23a0ba0220003de03e50100007a4420bd0000442420bd0000420bd00024203e0bd0220000bd0b81220000f60bd71b0080000bd02371b0080000bd71b11a0080000420bd0140000bd0140004420bd02000c0000bd08700003d0382b728700003d0380000f603d11a00003d5b700800003d5b700800003d00400003d00400003d00400043a0b802071b21a00043a0b802071b21a0000df04223a00024223a0000df0da0ba71b00004503e0ba71b0001e02420ba42208a00024203e0ba0000bd0ba00007a0ba02571b0000df44a0ba71b0000df0ba42271b0000df0ba71b0004c923a0ba31b0004c603a31b0004c603a31b0005c603c6b912321a0001636b91220006b90100000406b901558700)) else (if i < 19 then 0xd651b00006d2d62330002d65b700e00006d1d66b70000da1d602641b0001d63b70001d661b0001d60001d60001d600016905865451b0000586540006543b70200000653546b700035400007d07a0f605312248700007205344c02000005344c0ca04003f0000534c912200007d0531220160000530000d12220000d10220000d113342271b0000d103371b00800005142200005142200005142200005122200005305000004e0cc0000f704e4b900004e02541d2874830000f706d15904d33700015904d02500004d0cc6c641d0000f704d44251b00004d02551b2870001630da05824c21a0000cc0ca12251b0000cc2c600e0000cc02071b0080000730cc71b00800004e0cc51b0000cc00e0000cc48700006504c4c96b731b0000614de04d04c6c600004c04a00004c04a00004c4c900400004c4c900400004c4c900400004c00400004c00400006644a0000720d144a4130000df44a0b871b0000cc44a02071b0000df05344a02071b0000720cc44a40a00006224a11a0000610df24a0000d124a21348300006224a5b700024a1c602261b00024a01600024a01300024a11a2135830004f506206114a0002770d114a6b711300006114a5b700014a0204830003f50df0530ca41a0000580530ca0200000580530ca0200000530d10ca61b0000530ca02061b0000530cc0ca71b0000f80ca4420bd0000ca42202001f0000df0ca71b0000580ca71b0000f644a0ca71b21a00007c0ca02671b0000520ca02671b0000ca42271b21a0000ca22271b00044a0ca02071b21a0000ca71b00c00007c0ca02061b0000ca42212261b0000ca51b2830000ca4c603a31b0000ca12231b0000ca02231b0000f604a4b731b00004a4420bd0ba00004c04a3b71230005c902571b01700006505804c4c900036044a4c931b0000654c92b771b0000ca4c922261b0003604c931b0004c900e0000530ca2c971b0002c90200002c912231b0000cc2c941d00b0000cc2c941d0040000731c90000651c96b771b0000da1c961b0001c902000c0000586c641d00400004d0cc6c641d00007d04c5c60000655c624251b0000da5c603a31b0000da5c631b00044a5c602231b00044a5c602271b00044a5c671b0100003605c631b0005c631b0000cc5c600400007d0613c66b70200000653c66b743313300024a3c602251b00007c14a0ca3c671b0003c671b0080003c65192830003c651900007304504200006104502e0040000df0da05804502000005804514342300004534100004503f4220200000f604514303f22200004502671b00004522202071b00004414303f02600004471b00004402811a58700004414311a40a00004344202c0000f804a4420000f84420220000f84420000f84420002f52de04d44200006544200006544200014a0ca4420003c64420000f8044 else (if i < 20 then 0x6a32101700007306a42202071b00006a12202008700006a02502001700006a21d00006a1e071b00006a32171b00006a51b00006a16931b00006a12251900006a02501700006a0d902001700006a42202001700006a22201600006a0e301408700006a01428f00006a3b742201200006a22201200006a12208a00026902800026902500026911a00800016922202071b11a00016900006904012271b0000f616811a0000f60680c622271b00006814a71b21a00006705300006704000007206611d28700006c0661332870000664220000664220000664220000661220000661220004f506506206148300006a0656b718f0000690656b702061b4830001690652420200000656b702001d71b0000656b702001d71b0000f70656b731b01600006a0650262220160000660e371b0080000660e371b0930080000622e000828700007206102008a0004f50610404830000612e004411a0000612e00042830000612e00042830000612e000428300006111a00b4830005e008a0004e022231b0870002e00441225190002e02835010000651e071b0000651e031b0001e00c971b0001e00ca61b0000780df0ca41a0000780df21a0000df0de0da0000df44a0000df0530ca0000df0530480000df4420ba41a0000df24223a0000df24223a0000df4420ba1220000df2421220000df0404b71220000df1220160000df1220000df21a01700005f04a00005f04a00005f03800005f2de41a11a00007e0f85de0420000f65de2222130005de0080005de0040004de0da05824c13321a0000783de41a0000783de0da41a0003de02f42341a0002de0da0420002de71b0080000f80df1de0000731de71b0080001de61b0001de61b0000650de5c671b00005b02c11d00005b3c642200005b5c622200005b5c622200005b28f28700006125a0454b902e00025a4aa31b00015a0da6b711b00007c0da2c64130000730da0000df0da05800005f0da05800005f2de0da41a0003de0da41b41a0002de0da0000da0584870000da0580000da1d641b0000da1d60000da0580530510000da05304c00005f0da0534870000da0580531334870000da0530cf71b0000da5c921a0170000da2c613341a40a0000da0ba02061b00007c0da4330264220000da0584c60200000da0c671b41a0000da05861b0000da02631b0000da05811b0000da11b0003de0da41a0000da11b4870000d95c624242202021a0000730d971b0080000d95c642202071b21a00006405842312300007a05f05800005a05822300006c05844c13300005804c21a1130000585c631b00005824223a00005802e1230040000730585d622220f00005844a02071b00005804471b00005871b48700005841d00e4830000573d611a40a0000730575d611a0000df5d623a0005d60040005d60040002e00584 else 0x7d0515c600007d0da6b723312200007c47600007c00800007b0c304200007b3b750100007a27709300c00007a06111a48300007a4e00281235870000790380000790380000f80730000f81e051b0000f805f05803e00007e0f85de20a00007e0f85de0420000f80da31b0000f80ca31b0000f807304414300007a0f84420000f804a4420000f80444420000f84420400000f82de44203e0000f844203e0bd0000f844221a0000f84420000f80ca2420000f82420220000f82de14241a0000790f80400000f80404b720a0000f80400000f803f03d0262220000f803e02f21a0000f82de0bd4b90000f80200000f80200000f851b0000f831b0000f831b0000f831b0000f80df41a00007803e4b700007803f4b721a0000784b713321a00007804003f0200000f74b90000f702011a0000f746906571b0000f706502071b0000f706502071b0000f771b11a08a0080000775b70040000773b70040000773b70040004760670420b851b0004760620082870002760720b871b11a0000f606822271b0000f604061b0000f66b732a0000f62b70230220000f60f504071b0000f607271b11a0000f60ca42271b0000f602271b0000f62f571b11a0000f60626b731b0870005f50df24a0005f50040000794f50080004f511a3010000f72f506561b0002f506571b0002f543871b11a0001f542271b0080001f571b0080001f561b0000790f50bd71b00800007306d1e000007305a0580000730d91d60000730b071b01700007302f71b11a00007302c5aa51900007302c5aa5190000731aa0000731aa00007302f71b11a00007216b11a40a00006d16900006d6b748300006d02f21a30f00c00006c3e013340a00006a0651e002000006a05322200006a03f22200006a02502061b00006a0ca22251b00006a22201708700006a12251900006a42212252141b00006a12252100006a12252100)))))
def ruleEntry11 (i : Nat) := packedAt ruleEntry11D (i*12) 12
def rules11 (i : Nat) := collectCertFields ruleEntry11 7 13 (ruleOff11 (i/1))
def disp11D (i : Nat) : Nat := 0x202040200000887240a334626aa02022b000154080037000100c30009030c17120d01000805030d15020104071b110140105f3101040b0923120004150512000320000e40041a02002509020002010000040302000e0006041c0d070706002203041ba71c7203183e3b060a0109040c2209000e16033b05000301058001320a77001701000108000500041e074101221c020015180400130800351c03000671402b050103040004011bb03501010f0120010205030d0401140100050207050011031834223300040b0148260f092002001534050f3100190304030000260000001321270e2c0106083b0002030b321f020200020004024c340305030500020e01092003010012152700070f014b210b0400001a07103a01010d001a1f000107000000000100420135030103000c015517510007000c04132903060006360f0001121903491e100004110b030800020200120013320d021601000210031505031d040200001d02020f040100150062242708061e000704770513070a0a07280a020104010c080020520a0403000002112a05392200020b1c0100030e003500150c0303000105040007090c00090b040007001f07011305040002320134003d001003140010013d0616551d010a0e00340600000a000000053a0122000c01364103040325001013220c0001020405010002000706001e05210503050104000503300e13041e000f010607060c482115000218060a13020007140101121300080027290314001b001104050904421b060200282612000601010e0041030201000100000200230001200d000800260406000a01140a0f000b010d10061f40030a00020001010e0300040500030a0202010200050001012826250e01002c02012a020011040e002d080013050a0800040e0000020000020509040c36200102090002041d0000020004270115000300002b02060008000a130504310200012e000111000001050004020100090100020004091b0306000c0d02031d00200601070e0200000505000003004a020b052a12020403031a0c000005150400011e160f000d0613090a0a0023110400032501140001060001050206010000290103010400
def disp11 (i : Nat) := packedAt disp11D (i*8) 8
def slot11D (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x9e8193097808a86e589eeb39004742e7060806cb69301ad815a04a60ff8536129a065a168c32286730d220ef018b35d905a0156c2ff04e93cde19041c95800040001905ac044a00000be0438846d067e0b981c98dd208fc1c5020a80170c5cc35c2ec003f0770884a6e3884b16580dc424683750df00adc23703a601900a512c401f6bae008b8577947c059c17a017e84b4034e19881f385d10bcc111806304b700f80fe40ca84f432ac0bd4379025e0bda0ab1000056d0000000017c8000000003642dc833349b420001430c990276115471706f6597414b40000000000010b4301045e10001bb00588447002012c822d8bf4061e14a0290037205c433384dd820211e81b101768d4d01d814f436d01010bec1464119ad27120e164c2df80c905461bc4043023a1baa95682d30695428c092811482661a4e034c5258cce0cf8380cc68841f00741a7c64a8033005a159830e880000001ac037a04970000188594903200c00000000901190cb16cac000051104e40b5c23e800009821a962f18434057c03544ec03e103d011bc21e86d900000000297859912b009a02b40af200e8168407504e0047e20002e480000a46192000002640c603994400005a00000c2c2f7022006ce2ca46d700000b562a8436509ee1ce21961a5b01b902800fe0049016c05e0c09010d1ada06d04c6877d058616aa100424d858b024e1084347b4310c3606ac31e8473006016602bf02380588081eab6081e0c3819985d202652d16dab00a706ef079c16ac2d88d450a1c05481c6039a1940082431edefc0a341a606a385a903f21a10249053b197e0814578028101ec031c0000501569600000f481776b8c17e828b05b405f418c46210255184816d838783a008dc228414f822600a600001af803b00021a2c00000bb00000184000000000000ac000001de100009e426b05776cd760003168000098a2a7401903fe0af0179c03f838d15120ac42a2900000000109afd83ee02e2000000001431c16374004b043003f57b6c1040ca20db0074809880970a9603c413e863a09040b0c34d853c095c109c19f0331072601600c704994678008422e8c8e02c81a98a19a4402b9c22080bd84b8009804f01148edd0a1438f807c021b183d0fa0367862b128028b824308000afa2be840004f92000000019ad5390d44000015b58000d10c8bc33f0e8d0000131c00005f3b00015043210655000006fc00000a703f074a82cb000005ac0cb4800000008aa0000081800003dc008c00005300baa77e40b805b802cc0cbac060000038c0734000000006361a50000000004660f880000000031400000c100000000085852d01766000058c13c0000000014700f1813e087846980be845c12f20d000000568095000003108120045ad7b0000055704ce04fc16605790988157c2e005400 else (if i < 2 then 0xddc0254000057509083a384cd00000d1814982618228669c15e80a4061e08c60da80ee0000012805e5a3c018900000a542ab071000000c682ea266702a612100fe86011c1418342e102a809d40304000000001f40119ad906a60c0829f02a98104000012301d916a507d60c9000002b945d626701bf12750b6a5c580bb860842e2cb8c2fe81dd283410c8388853e06760ee822682b11c22036c0000685030613e19ea024a13c40c9875c0c0d0186103c27080000146112422603b502300000072000000000d58400071a0be413480000043624416885c0855c00001ab438080000556c45c0d105b705e8022421e000000000000275866609650000147842a078616b410a8019044a06e8054837e09482bc06b506040c0a06a402203b320001024252000005f8038816e852e076611581ee805c0000075415d8000095611c01c105b5668202d02c7055500000198400002b0000186c6d4896d03480ca07768562059000000380ab802b2189056e880003301672ac540d6a000127c2da80470e081b9020c041400001a90279064f05cc25400000211183c0af42c02e3060001c54190800003a6197002e811f0580d9f400000c000920000307bacb1d141b0467a82190c7211002f783120e2417340e502b4089a3aa5f27000000000db80fb829604721ae01d904e5a4e0000000000000488178800005aa600000001da0c568000090c21b020202de1b5024e0cd5039615dde5980b600381948281090a093c1c60349049c0ba62c8c000058901f200000000000001207641d30b011d4838b862c824504820870775005704021470aed04640d8a14508000474056c00002d80395084a166c07f00000ace20002c286930d6c0a568d9800009e8c00000003640888062c21701da00000df290701750a00033c00000b900000000000056300001c3800000000c3e14d416a018d08cc04c811180990000000000003d0000000000000000070c092c15980000dd6000000002c6063007e26b309fe0d5e35ca8968d440596165419a919e121a0fbc0418135055c1a3449712650602084c18c85dc0dc60ba800002a0b00004540f602d103f038bda3d81210a3e0a64002017e0baa18c018002842c2e096429906120d100e7c02700d009ea8e7827fd62c0d9c0658301887b0a88c6d005303620c4607e87340cb9096a1a7032203f604e80d1835309f40000143868c006306b800f4252803d68ca09ac8a7818609621a1820d81e1025603f00640d6b090606c806604a91c4a000032980000a3a00001da000000001a2c55a8b2014b6000021400000000000038600880d6e059c31a82da1ab20e6c89a01c209f805c8052010506ba0000328000009b415ec46d070d131001bc20302afb55a3bd81830a7106c840f1a760ea0242c033833400fd0a5acd8c06f868209de0948 else 0x101d3714000191c118809e03ba17ac33f024d0c1e1c4c0ca012c0b1cadf0000040a0000019400003280bae018029b8cfa07e2180062589dc1c1a3b300fb2542077e180415f85c50b400d9c8d0050a0b5402b805806821134164423f84c005080121b85869e07aa08142af007115800c306ac000809c8101c2c106b904be5b4403383be0c32286eb6102e7685811ac1570eec177202601eb865a009c337c2eb03de07820ab002106720b0a334413683f20234196c7518477086e19302ce8ae108081ae805902f6075a1b541a104d407580c5db64801105bc1504422b46a013a1b8832c020c0c94105c08905ed1bc00bf9f3686a70afe1aac06e808d0e1625ac37382e90d5e170c00005720c82987400a006c0a84359001b05cb0ac23b2812e000008da2c382ef800008e4000029a0bb80a6215742b50818036e13b4000024700a41a0c1cc800000001b7c0000000000000001b7868f1500000031130000ae4a3c81bf820f0548087016681090292000000003fa068e18f060886093874092035982c1600007d807a860e000000e425b580005203c5c0000000069a0cbc000007a0d20089c00000de00000f1c2d98000000014dc2e2028c198c17c01c4800005ca295437f05bb04be12f810ba5ac03e60e508000399124c15e04a104e808ba15800000365004e02ac0f881feb37a0e5c0000000075609a41c88371b5ce531430485154a4832141b484ec0e14143c51b04890af8138c000000000000000317800005c820000000000095a00c430c841305360d980eb0208026e05a43668525005417d2ae405670194107077983730352398c16c058eaaf423ac29104de07b208f4680d6a10c30164832005bd05e20dd2cc205f2160801b41de8249025e039c01a804b0e1a0da160106320a8c10cc6928cfd03600cc81da91e00914010592c88ed08b8169010885c51d520ea20fb8b7a1b3a199ac0006800a9e0f483018299764e0f4404702b2056a161019286fb070817a832c841004061720671068f733a0eec00000e107240ed1cfc05340c4a39e01e283df0a642c882c5b02205c81408179800001dc0bec4f2858c074a1c64005803f600005d837485bc0c1cca556868294123c00001b0800007af07ac00003880742165000002fd16e007102f985e40b7c064407804f9060c104801305d2274d416c2c004e61cba0e1c0a585d9143a018817601360d020ae04aa80000004191801e051118900cb814300e601261446900584c1d64000000001b10b5820000000000092c06bc00001c706c160001fe8000000008400be033701c60bd06cad4910a26e00000000760116027c110867c021c055000006e606c22ebc16f834f01e6139c2a1823a0c76000023386bf0000049004e00000d84800004781a500001aec00000000b743b7810a000d066815cc05c03a9)) else (if i < 4 then 0x800001b481a1800000000e9eb0389db1ae620bc1db02340638167c36e02910ba8064825802b71000086c1528554015e000018186b105161a593408b78001e10ec10f02f177b4117c1c5039d0b1a00b823083140e100ca8194848803da2a6010c01b8054c1b1c10301450be20d9c1e5824004d409ec292050d117e01dc19986801dac0f002260e021414132802f86f022c213e024800000ac20ec02f2822206d8120008305a71d5412bc2280288087c0e3822b84410da027141a900000000000030981ed264c0a280da83790ad2068c21585090b8355058000178043e0fa814b893804328000236065e00ac07b0410048f0cdc09e829f8068000008f4161064b04d6a8a002305b106a61544324802c03d400001ff841c0c20339413f8481099e077ad70033d03ea13080ff806b02d419e81d401fb079210880ee8cdb0dfa44c02640e176beb414406a051a1378081c174020536d618581ba01d407cc056c1d8865709461934201845207d8115845e850509cc168145000480000006c17f800004a80790000000009b3600011580000b8e0c7c0a70ca1016a19ac1a80533100010cc000008106ae27ec41db4f300000a6c51c895e01540c24274cbf70482333055b261816f84e6c583851c8a0812caad456740b14007409700000626045028b86991c1610a40c801c00a2435c46d10290093409dc6ce06fd0dc210e00df0426066762b031504f44000188024c080004c03324217853a0d820f3033f86a52cac0e96296000005040bcc783851304cc1bd848106f9048415242ab0d7f1000189000003cd0d1c03a40e8800000001af426983f3000000001091800000004302a5026000001b2004380ba003e0c78000007d066c093818a824f0a560470000018000001aa4589362800fc0af034b084a0706140c3130a3e0b1e000009d35ba01b808b01bb0000000000000950338054e0d5c00000000c0c17e01c9923006f4000037b5217327200000bc36770a0168f000006cd18ea231028602fb6a2819441731698017812b00800287089c18be02a84870aee3c28400000000fa392461f800009b218dc00002ca0bb61bd4154840b00b2002827dbb560c7807ad951061a00001a6800001aa0a26291805b8599045a000012883a305de05101fd842305560bd858682fe0c983ad400004d003ae3188365808c093e2b1c0c786c6097a0a341aa0187000010381840622033e0bb41f480000516233429d85b515f614040eb800709a76c1400004ad1220000033280000660053034ade9f000000001568000043405c198b80c50424134d19c84fb000005fc31ea50b041a0b70054026b01f601d40380000099a000017335f707f80570280be6907ca161c1eb048b0afa09b03100b7b0c20128c6879cf41000141c04f0a2810a80b882f4845e00d400000d604e90000010 else (if i < 5 then 0x432d0866024615d020600000d2e15203198453000015ac51501430ca021401a883b9b1000528157860c0a2465d0023b536074eb44821e547609ae0f7011204f70088cf08290847502741728048000003ce12a82d50bb46a30ee54434808a0cec08c81f682350a7004a413102924c68174c2538498059200000d0801300001440439065819e96b9c1c681680d0e19f46a803e3074cb43aa2a059a032e19fc5f0037d02c019e42998469002a010c092843c57540e4020c8576095200e01e5051b0136094022184dc091638981d8b3c607340ae8253046002ca143c1ad03722ae214918e080e500e613c41a4034a025a097407785dd05821a6c988810805c22d780318ea11bc20c00715b41d0d780b640e483350d80000025d800000000000315869e1614000005f05af00001624b10baaa0da6181c35005c100000000361580003f80ae434482580b945a5422285de00000a0c00006a0771e14400a08577070010d432f80910de02da00303b160dca0800456801600000000301581a0c4ac8f8422828c3b2e0758cc0815f000008605bf56150c6a20001508dfc035c17d0243027e0800108005986f009eed8c41b006924996054401485d81dfe174441a03c803fa23601e782970dee1c182c590d60658ba6c5be92d30ba967401c584fe0cea1320293be9907c81594146069d0c520630139811306e313b8363431d069818fc029123b0e3220002840000058a082c33d81c3098031c4000022b628067fececd14d00000000122880005e6db802cf04f660001b400d4000001aa00002fd8e430b4e11e400000000a2a00dc14f00250d8600001c286640c3c200000006b4068a000034b04dd053800001f8010b0d7c000000002930a3c0a140203000092804ed00001f0000000000000000000000000000000010800001e201570b12c8dc35704de11a40588101ad860c0c2000266021705aa18e01370006033c18bc5ec04804e120e6027cb6f31250153028c0f030cc00fd400000e00af60000000060f6adc04440f904050dae198419d06701d58e5741bb82760c9026ac57c062709e8136022583ae054006b400001cc05df16a0204054588f223083500e5400f200a02a9058a23b6043c17582ee073811e802685290d0a200c1678715174e13a870a029400bc1a3c06585881d7c29005ca026b8660280107f81850a0c19b06710b490ade1604000017a0cd63538382803e68b60ea097b823f0b20051c37889de00000000000058307b600002e6069a15297c0822783b701a437d421c8515b0c81aa00e785ff072c169400280a202dc0a380428636009e19a8052856c0000046c22c003e068807e8037000000000038099866b439c0e6c20b007802e6127417284ff08b407980ef82db0620025c67b053115a4173c0f6865b033600002708800000016e0581046 else 0x14d878001ef096c89dc1b680f706b2098c130857514ac13f9c6980e80cd811442c109b60c182000186025700000e8813786700000000010201160e1c2cb280003d3092613c00cc80000dd001)))
def slot11 (i : Nat) := packedAt slot11D (i*15) 15
def lookup11 (h : Nat) : Option (Nat × Nat) :=
  let v := slot11 ((h/799+disp11 (h % 799))%2771)
  some (v >>> 4,v &&& 15)
def step10D (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0xc36731c76711c86711c76711c66711c5000ca200c5a5000d82000da6000da767a1c366e0c22901c135d1c63321c46390cb4e817621d18703a9715e61c4000d755ad1c32551b92661922541b9000d722a01a954c1a947d1c635a1c61b50cb2070cb29f1a93750a65621b951d1b92af0ca5551c45541c4000d653e81a93e71a93e51a93e61a923f1a94e71ca00b5c64d91630448c60439620445863e41a95051a903c2cc4911c34951c02971b94f71ba46d0c23b71c7000d622371c13b71c04901c31431a91421a91411a903b9c91cf0cb1ba0cb1ac0cb4590cb4301a942f1a942e1a942d1a942c1a942b1a95291a95281a95271a95261a95421c067e1c25e91c0000e553b91c05e80cb7100cb55a0cb000c85000c523ff0cb2b20a867e1c167d1ca40f0ca4001b63e21c30095c50365c20425c204359263b0cb7050cb3c31c74080ca3ac1c7000ca548c0ca3b71c83b71c63b71c56c50ba3c21c7000ca86700ca000eaa7040cb6f60cb55b0cb3e21ca4901c63e21c73e21c63e21c2000d86000d87000d76000d520399860449543930cb0092bb0052bb0042bb0372bb0032bb0022bb6350cb10d1540435980439543e21c000b98200e2aa0392cc0392aa03928803927703925500c2aa00c28800c27700c26600c2550058c10028c16791980045980375980035980025983120ba3110ba3100ba02e96367b1922d60ba2ea0ca2e90ca2e70ca3180ba3170ba3160ba03859835d0cb3671ca4b31c122b1c62921c729a1820445a5000da50435a82aa1c66650cb27a1c62791c203a5a503a95125e1a403a98124514128e1822380ca2ad1c62910ca67d1c13bb0cb000c820445922301c60445824860cb4870cb6f50cb5520cb3c00cb44d0ca64d1761171c600b8a20a90ba0a80ba0a70ca7530cb1131c60970ca32f1c43301c404727704627715f19615e1a915d1a915c1a915b1a915a1a91591a91581a91571a96bd0ba1531a91521a90e50ca03427700f28800f27700f2660112880112770112551351a41601a915f1a91561a91551a91541a91430ba6b40ba1420ca1770ca1410ca3f80ca33c0ca1401a913f1a913e1a913d1a913c1a913b1a913a1a91391a91381a91371a91361a91351a91341a91331a91321a91311a91301a912f1a912e1a912d1a912c1a912b1a912a1a91291a91281a91271a92d51c80322aa0312aa0312880302aa03028803027702f2aa02f28802f27702f26602e2aa02e28802e27702e26602e2550052aa0042aa0042880372aa0372880372770032aa0032880032770032660022aa0022880022770022660022550382bb0382880382770382550382220448a81261a91251a91241a91231a91221a91211a91201a911f1a911e1a911d1a911c1a911b1a911a1a904f1c604f1c00438c20002880002770002660002550002220002aa else (if i < 2 then 0xc1c79181c79181c69181c27a81c2a301c7a301c6a301c36272bb6282bb5875986482bb501598508595507595a1b1a95215978ff1a929e5955f79873f49c3c1f1b858d5b833e5b62855989211a903ad872739875005989181cb81c1a7341987c251c63965c2bed0ca38a2cc3892cc38b2cc38c2ccbec0ca3965c13a55c73a55c5a370ca1185c83a85c63a85c13945c73945c5a340ca8310ca38d58738d9731179c61175c61175c24f52aa1165c81165c683c0ca1192cc1198c64f12cc7611ca7a81c77a81c67a81c337a8b637b5a637a5a6a270ba4005b834b2bb34a5a87fc1a87fb1a68f30ba8020babf70baa430a68010ba4849766c595428f95429e9546c09546dd9542149542129546dc95422f95428e9544d59544d99547a81c0c8b1c49251c48c81b17e61529490cb6c05976c05959631c36354cb39b8cbc271c36ea5877f918721d59632b58732b9735009549cb1b89cb1b335d4cb6dd5976dd5952145954e78ca26c58632e8cbc220babd61768461a829959329a5937fe1825eb9652755982755962755933938cb39d8cb21259721259595c1c26dc5976dc59522f59722f59528e59728e5953902cc3995c83925c75a45c838f2cc38f5c738f8c700be5500bd8700bd7600bd7500bd6500bcc500bca53c35c73c35c53bc5c83bc5c23b75c54915c51112cc4ea5c803dd765605c700dda700dd8600dd7666f9545885a55889544ee5c74ee5a54ee9540fe2cc0fe5c7044d76044d75044d65044d72044d626735c740e5c840e5c26398cb3408cb3762aa3765a73765a684315458f57664d98764d56564d59364d5634d55974d55954d95974d99764d95954d956526659510d2aa10d5a710d5a6b41153355953043d87043d86043d76043d85043d75043d6596a1c33e79a93e69a93e89a904a4cb0464cb01c4cb0244cb0254cb0454cb02b4cb0274cb03e4cb0294cb01f4cb02c4cb1b71c701e4cb0038ca01d4cb0284cb2e80ca2e60ca5940ca1da1c61d91c61d81c61971a91d61c61961a91d51c61951a91d31c66320ca2ed0ca2ec0ca2e50ca3140ba1931a93130ba4921320025a50029540385a503895403859200b2cc00b2aa00b28800b27700b26600b25503d2cc03d2bb03d26600d2aa00d28800d27700d26600d2550442cc0442bb0442aa04428804427704426604425504422203a2aa03a28803a27703a25503a2220432cc0432bb0432aa0432880432770432660432550432223311c64f41ba0085c824f1ba7131c67141c62af1a92651a937d0cb0425c53f31a93f21a93f11a93f01a92421a92411a92431a92401a926e1a93f41a93b21a96c718748c1636c90cb6820cb6830cb6810cb0355c80365c80015c80075c80445980415c50075c50365c50085c50015c5000e88000e22000da8000da267e1cb67e1ca67e1c767e1c667d1c60355 else 0x3e42aa8261a4a321c0a331c000bdc800bdc700dda600dda56895c29ef1cb2535c3c8c1cac900cb21e2cc76e1cb5032cc6935c36575c36515c88c70cb3c55c88e51ca6c15c2c450cb3ea2cc5092cc5042cc9cc1cb6955c36955c26015c327a5c35e95c856b5c83b15c23c25c22795c88cc0cb3b05c25635c293f0cb3bd5c86565c36925c36525c32925c36865c35645c322c5c88cf0cb8a50cbb200cb6615c8268963035d8600bc854f72bb4f42bb51b59751859751a59700bca8bdc0ba9880ba9830ba6735c54e72cc2909547820cb35d2bb6472cc61e2bb6e82bb5ea5a64e12bb4e52bb6e92cc4eb2bb4ed2bb4d22bb35a2bb3312bb5062bb35c2bb35b2bb6579543a35c5c831bab741a98931a9c151ba7d90caab70ca7d30ca7d60ca7de0ca7dd0ca7db0ca7da0ca7dc0ca1155a65f95765f95c894f0caabc0ca1142ccc611a84d65a7ac71a65875c84d15c84d15c74d15c14d05874d09761135c71139c61135c61135c51135c29500caab1182a50182a500ca4da2aa4da5a71052cc1058c67ce1764e02cc4ef2ccb011ca5f99655f95521125c81125c71125c61125c594e0ca1102ccbb70ca4f02cc7cf1ca7c80ca4d79765c85765c89623632aa5005a83612aa3618a65515a85515a73622aa3625a73625a6044e55043e552b99545879549181c03332bbb811ba9901ba9b51ba3945c83a65c23a35c26f05c35065c36e85c335c5c3a97163043d629fe1c79fe1c69911b73ef9c99161a9a170ba9ae0ba98f0ba9f40cac400cabf60cac410cabfe0ca9f30ca97d0bac730cb9ae0cbb860cb99b1b87ad1b5a100bac530baa210cba100cb9d61b83722aa62b2aa3542aa6305a83772aa612598cad1b9277598c221b98e61971105984f059836a5a836b5a836e5a8bb10caba618292c18224898252a9821185c139f5c13a95c13a55c235f2aa7e51527e815254755279a0cb35d5c2ba1182b0d1824749827e31c07e31c63e89c9c6a0cabe50caa1a0caca90ba9780bac720cb3785c5b890cb98d0cb3562aa2665c62129c15425c25665c298c0ca9ba0ba7890baaa00ca4fe2aa6eb2cc3a02cc7880bacc00ba51c2bb3872bb37e2bb9251c97bc0cbc6118746e5987a918746e987b581879111a927f59826c5932985932a559728f59582b1a73559717681a760e8baca20bab690ba4ec5a7a241a6a0d1a8a0e1a8b6a0ba48c5654ee565a031a9bf50bac5f1c8b650cbcb40ba8460bac701a84d95b735d9c635a9c63319c65ce5c85ce5c54f72aa4f42aa4e72aa7700ba7710ba62d2aa3692aa3932cc5232bb39d2cc6392cc5242bb3402cc8dc1b93482bb6342bb5252bb3472bb10e2cc3702aa3512aa7700cb7700ca62c2cc3408c64c78a66232cc2485984be9546045984c72cc5195979401c99401c2a78198a7019858d2cc5385982879872865984ec2cc95)) else (if i < 4 then 0xcb91a1c391a1c23a45c26575954d25c339e5c839e5c639e5c19911ba35a5c335a5c27871ba35b5c835b5c635b5c39781ba10e8c710e8cb8921a9c751a99e51c79e51c69e51c35475c35675c35e398726e5989a01ba2685987e51c69251c6a230caa1f0caca60ca2749870fe954abf0ba9341a99fe1c37e31c13a85c89110ba007d85036d859430ca71c2cc60c9a960c598c701a93732aa3642aa3682aa3652aa3658a63792aa3602aa3605a6006cc55f99872709875eb987a160cb4f55976085984f15985eb5b839598739298638f9825d898756098600dd879421a9a091a910d9543e59a9ae81b8ae81b7ae81b56715c503ad826c55956709548971a95885c84ee5c877f0a64f45a73315c73315c2a510bac061ca7861ba3335c63335c5c0e1cabca1ca7e31ca3b75c83e25c29fe1c29f90c23938c639d8c600bd52039e55039d87039d75039ca500bd8200cd8700cd8600cd762654a80fe598111598212598044cc538f9632445982449549e50ba4ea5985885984ee598a550cba540cba590cb9ed0cb5a4963044ca59c90cac4e0cb26759821d9b72665983d0953245598266596266954b8415426698226696210d598245954043cc5043ca5268596c430ca00bcc800becc9e60bac4a1c7c4a1c6c4a1c150098221e9c97c81cabb71caa0a1ca9870cb97a0cb7d01ca9411a9a201a98761a98751a93625a891c1c891c1c11155929171c1c631c11158c64079810fe8a2044d523555a591c1c62b98a691c1c35ed5a893a1c691c1ca1159a42c18c64de5825ed5724075529341c79341c8a331c19300a69341c03ef9c4c631c390e0a63555a89281ca19d8c54fc2aa19d8a62148a693c0ca3548a64de2aa11558211555293e18200be882905c53552aa3555a7c631ca34d5c521c5c8a220ba2ad5c55d95c35ed98748d98700bcca8f60baa0a1c250895450795403ae8853b5c753b5c553b5c25065c75065c53a75c83a75c73a75c59fe1ca5015a867b95400de88c641c77b11c784d1c7c941c6a3e1c76c04cb8cb1c3bd91c78d31c389c1c78791c7c961c6c971c6c951c600bdc5ab31ca9191cab250caa321c7a321c6a321c28811c64a19879a71c710c5c710c5c510c5c31185c34d15c58190caa331caa331c7a331c61175c38701c68ad1c68721c68291ca9171ca38b8c680e0c283f1caa2d1c7a2d1c6a2d1c21165c3a2c1c7a2c1c6a2c1c31148c77cd1ca91a1c791a1c63e92aa4fd2aa3f02aa3e52aa3502aa4fd5a79711b78000ba9581b53532aa65d5a87ee1b58f41ba8f41b7ac50a637c2bb7fa1bab470cbabf1ba7740cb35e2aac980a69420a69410a65052aaa201a491a1c08c81c98c81c4505598b6c1b9a5b1c9a5b1c4a5a1b93ec2aa3eb2aa3ee2aa3ed2aa3ef2aa50a2aa3f32aa3f22aa3f12aa3f42aa3f49ca3e72aa3e62aa3e82aa3e89ca else (if i < 5 then 0x88cbc211a96c35979400a62a259729b597294597c280cb28e98230d5a671c5a63999874ea9877bb1a99231a9b011a79f60cb6c35879cb1bab7b1c26095969c41a76c55975225a748c5c73595b736c5c1c001a9c031a9c1e1a95ed9815eb576c6e1ca5c9987b3c17636c5c564d59521d595bdd0babdb0ba6ae9766ac97630d58737b58721d9545e0965275982c700ca4e29764e397664d9549351a95f15c35fe5c35db5c3bcc1b74fd5a5a530cb62559877e0cb9930cb6035986075986095984f55a74739873605a55c85a5bba1723639763579765c89875c89542785985005a5ba80c23a65c739f5c7cc70ba03ad529351b9b981a98c11b9c991986398c6b8d0cbc1d0cb507597b850cbb820cb5079732145972149732784b8cb41a8b750cb2125a76c0587cb41878461872125876222cc9f70ba9860ba3812bb39c2cc32e2cc3832bb5452cc6472bb37d2bb50859732e8c6be90babea0baaad0cbb7e0cbc221984729875458c25fe5c8aea1ba8981a9b331caa1d1babe10cbbcc1b910e2bb9101c28ac1c6cc80bab500bab4d1c9b481c96e12cc58e2cc58f2cc8031c9b4815438f8a21145985c95985c859825a5986262bb5c8953be41a99121a960d9a928059660d598280598044d87043d5234498758f98758f5a538f5c639297639158748c97638f97538f9725609766705874ee9760fe5c60fe9750fe9723429873922cc3bc5c6b341b69460a65655c35e35a8b351c4b230c25248b7ac00baab10caab11c84e95c87ce1c74db5a84e35a8ac31ba9311c99060a6cae1a400bdc676a0a623f963a9f1b90c28a633f5b63b95c83a95c853f5c35655c85f25c85f15c85665c85675c85635c85645c853d5c8caf0cbcb20cb6f05c76f05c53a95c73a95c5bc81bac161ba8061ba4d69544e35656d6954ab50ca4e95a84d75a83579824d09544cf562b3b1765e35764d75654d795437f2bb4d9598b320caaa51654f62bb3572aaaa1165af20cb4ee2cc6715c6c981a9a9e1a9a951c423258665b5a8abd0cb86f1b961d2bb32e2bbc9d0ba98a1ba77d1bab341bab351c9c290a63402bb9851baafc1b9bf416548c5c82755c64d25c13a35c13a45c1c991b95ee5a83565a8ad21b92505982675965bd565c9a1865685c8c8a1b84c05a8aa41c1238963039cc54d59864d58ca6d92cc3745c59c70cb9e60cb9820ba63a2cc6352bb39b2cc4e52cc3842bb4ed2ccc8b1c999a0cbb2f1c95c49544e35985bd9546ae2cca951c94f22cc6e72cc4e22ccb1815461a2bb6185984e95984d7598a841b94e42bb61c2bb4d79536da9a9cae1a96d75976da5956d65976d659562c5c600dda810d5a83605a85f75a85f75763765a84dc5a84dd5a86635a84e25a84ee9824e45a8b791c297b0a67800a64f75a7a331c3a321c3a331c2a2d1c3a2d1c0a2c1c2a2c1c04ca5c57780 else 0xa991c260f598c9b0baac10baca80ca6195985058c24d559848c98264d598391963cbd0cb6de5876df587cbd182cac1a8cb51a822f963ca318261b5984d55a84d95a82515989311c49401c435d5c635a5c63315c62ad5c68741b9c870ca3a35c83a45c84d25c8caa0caa560cbc7a1a9c9c0ba2509873625a581a0ca0fe8c7b361ba35d5c5c6b0ca3965c8299595001d85c5d0cb9e51c091d1c06c45c3c5a0c222b5c33909a73912cc3c35c24905c8c5e0cbc580ca2c12ccc631c7c631c6c631c23e89c0c631cb26559898b1c73f49c191d1c791d1c691d1c33e89c191d1c20fe982c570cac420ba60a598c4a1c3c4a1c02c2598c261c3c461c2b6f0cbc8d0cb6e85c735c5c77e71cabb21ba6a52cc9fe1c19fe1c021d987007d876505c835d5c32ad5c328e5987e61c6a301c08e61b98b61b9c2c1c6c2b1c6c2a1c63828b629c5979b01c69921c79921c371c8b62a359764)))
def step10 (i : Nat) := packedAt step10D (i*24) 24
def ruleOff10D (i : Nat) : Nat := (if i < 1 then 0xcb525a72d2968cb4259f2ce966cb325972ca964cb2258f2c61624b0c5832c015f4af45772ba15c8ae056e2b615a8ace5642b09578ab855a2ac1558aa85522a81538a9854a2a39510a865422a09500a7e53e29e94f0a7653a29c94e0a6e53629a94d0a6653229894c0a5e52e29694b0a5652a29494a0a4e5262929490a465222909480a3e51e28e9470a3651a28c9460a2e51628a9450a265122889440a1e50e2869430a1650a2849420a0e5062829410a0650228094009fe4fe27e93f09f64fa27c93e09ee4f627a93d09e64f227893c09de4ee27693b09d64ea27493a09ce4e627293909c64e227093809be4de26e93709b64da26c93609ae4d626a93509a64d2268934099e4ce26693309964c926393149864c125f92f49764b925b92d49664b125792b49564a925392949464a124f927493649924b92549264912479234916489243921490648123f91f48f647923b91d48e647123791b48d646923391948c646122f91748b645922b91548a64512279134896449223911488644121f90f487643921b90d486643121690a884c42320f906c830414207102880e4042008ff87f63f81fa8fc87de3ec1f48f8c7c03dc1ec8f587a63cf1e58f1c7863c01de0edc7663af1d58e9874239d1cc8e587263901c68e2870e3841c08df86f63781b90dbc6d83681b18d806b835a1ab0d4c69a3471a10cfc67833919b0cc865c32b1940c9064031d18c0c586283101868c2860c30317f8bf05f22f51788bb45d22e61710b785b42d51690b405982c81620b0457c2ba15b8ac855c2ab1538a8853c29c14d0a6052c2941490a4051a28b1448a1c50a28314089fc4fa27b13c89d84e6270135899c4c826112f09604a424d124091048223c11c08cc46222d114089444021d10d085c42620f105881c4082010fe87e83ea1f00f6079c3c81e10ef076c3ae1d30e7872c38c1c20de06dc3681ae0d606a83501a60d206883381960c906403181870c2060830017e0be05e82f01760ba05c82e016d0b5059c2c81610af056c2b21570aa854c2a214f0a6852c2921470a2850c28213d09c84d826612f094849824211d08d045022010c08484142020fc07b03c41d80e807203801ba0d806a834419c0cb06403141840bf05e82e01680b205782b01520a7051828413e09a04c0258128092048023811808a044021810808204001f80f807a03c01d80e807203801b80d806b03501a40d006703301940c806303101840c005f02f01740b805b02d01640b005702b01540a805302901440a004f027013409804b02501240900470230114088043021010408003f01f00f407803b01d00e407003701b00d406803301900c406002f01700b405802b01500a40500270130094048023011008404001f00f007403801b00d006403001700b0054028013009004401c00b0040014004000 else (if i < 2 then 0x3608b03d81ac0b604b01d80ac035ffafe97ecbf35f82fb57d2be65f12f7d7b8bd95ebaf557a6bd15e7af35792bc65e12f0177abba5dbaed1762baf5d6aead752ba75d2ae8d73eb9b5cc2e59724b905c72e31714b875c1ae016fcb7c5bd2de16eab735b8adbd6d8b695b32d8d6c0b5d5ad2d596a6b505a62d2568cb435a02cf5674b36599acc165ab2a5932c8d640b1d58cac59626b105862c2160ab03580abfd5faafb57cabdd5eaaf3578abbd5daaeb574ab9d5c8ae056eab695b0ad6569ab4559eacd565ab2158aac255faaf1572ab6559aac155aaab554aa9d548aa154f2a6d530a9654a2a4551ea8d545aa2150aa8253fa9f14f2a76539a9c14daa6a533a9914c4a6052f29714b4a5852b29514a4a505272931494a485232911484a4051f28f1474a3851b28d1464a3051728ad450a25511287d438a1950b284d422a0f506a82d412a07502a80d4029ff4fea7ed3f29f64f9a7c13da9ea4f3a7913c49e04ef27713b49d84eb274d3a09cd4e5271d3889c14df26ed3709b54d926bd3589a94d3268d34099e4ce26693309964c9a64131a98a4c3a61130297e4bda5e12ea9724b7a5b12d29664b1a5812ba95a4aba5512a294e4a5a52128a94249fa4f1272936499a4c125a92a493a49124291e48da46122a912487a43121090548123fd1fa8fb47ca3dd1e68f1477a3b11d28e747223851bc8db46c23551a48cf466232518c8c346022f51748b745a22c515e8ad455a2a514e8a4451228113c89c44d226112c894448a239116888442a2090fe87c43ca1d90e887243821b90d886a43421990c886243021790b885a42c21590a8852428213909884a424211908884242020f907883a41c20d906883241820b905882a4142099048822410207903881a40ba05502480f406202100a8023ff9ff4ff47f73fa1fc4fdc7eb3f41f98fc67e03ee9f68fae7d43e89f38f967c83e29f08f7e7bc3dc9ed8f667b03d71eb0f527a53d11e7cf3a79b3cc9e5cf2a7933c81e34f147863c21e08f0077e3be1de8eec7733b81db4ed47683b29d88ec075e3ae1d68eb07553a91d40e9c74c3a41d14e8473f39e1ce4e6c7333981cb4e547273929c8ce4271e38d9c5ce287113871c2ce107053811bfcdf86f937b1bd0de46ef3761ba4dcc6e43709b78db86da36c1b58da66d03661b28d906c63621b08d806be35e1ae8d706b53591ac0d5c6ac3551aa0d4c6a33501a74d3469734a1a44d1c68b3441a14d0467f33e19e4cec67333819b4cd46673321984cbc65b32c1954ca4650327192cc9064532118fcc7a63b31c98dcc6a63331898bcc5a62b314989cc4a623310987cc3861930b184cc2060d3059820c0c6043011800bfc5fc2fc97dcbea5f32f897bcbd85e92f39794bc65e02ee9768bae5d42e89738b965c82e2970cb825bf2de96ecb725b72da96ccb625af2d696a else 0x47923c11dd8ecc75a3a71d08e6c72a38f1c48e0c6fe37b1bb8dcc6de36b1b38d8c6be35b1aa8d4469a34519e8cd465a32718e8c5c62230b1818bfc5f62f31768b9c5c22dd16c8b4c5922c51608aec56a2af1548a8c53a2971478a2450627d13a89bc4d226312e895c4a224b12188f446e231115889443e21910a88444122010fe87e43ea1ed0f4878c3ba1d70e8872c38a1c10dd86d435e1a70d0866c32a18f0c4860c2fa1770b7859c2be1590a9853c2961470a184fc27613709984bc256127091847c232115088843421210307e83dc1e60ef075839c1c60df06d835c1a60cf06483141820bd05b82cc1560a5050826c12a08f044821410207d03c81d40e206d03481940c205d02c814c09604301e80dc06202d014809404201d00b804c01e00b003800bffdffaffb7fcbfddfe8ff17f73fadfd0fe57f13f79fb8fd97ebbf55fa2fcf7e63f29f90fc67e23f09f7cfbb7dbbed1f64fb07d73eb1f52fa57d0be79f36f987cabe49f1ef8c7c53e21f08f807bf3df1ef2f777ba3dc5edcf6b7b43d95ec4f5f7ae3d65eacf547a93d41e9cf4b7a4bd1de8af437a03cf1e72f367993cc1e5cf2c7953ca1e4af23790bc79e38f1a78c3c59e26f11787bc35e16f09783bc15e06f0177fbbf5df6ef977bbbd1de0eed7753b9ddc6ee076ebb69db0ed676a3b49da0ece765bb21d8cec4760baf5d74eb875b3ac9d5eeac754ba99d46ea074eba69d2ee947483a31d12e86741ba01cfae7a73bb9d5ce6e7173739b1cd4e687333991cc2e5f72eb96dcb0e55729393dc98e49722b90dc82e3f71e38e5c6ee35719b8c1c5ae2a713b891c42e1e70db861c2ae127083839c16e08703380dc00dfd6fd37e1becdf46f8b7b5bd4de76f23789bbcddc6ecb75dbaadd36e83735b94dc76e1b701b7adba6dbb6d1b62daf6d6b6adb50da56d13681b3cd9c6cd3661b2cd936c83635b14d886c33611b04d7f6beb5edaf2d776bab5cdae2d6e6b5b5a1acad636b0b57dabad5b6acb55daaad526a7b531a92d466a23509a80d3e69e34e5a6ad32697b4b1a52d26691b481a3ad1a68bb451a22d0e685b421a0ad0268033f59f4cf767a33c59dcceb67433919c2cdd66d33619aacd1666332598ccc366032f5974cb765ab2c995ecac65532a194cca3650b27d93ac9b64cb25d92ac93648b239916c89643b215906c8163fb1f58f6c7963bb1d58e6c70636b1a98d0c6463031758b4c5762ab14d8a0c4e626312588cc4362030f5874c3761a30c585cc2b6143091842c1e60d306182cc1))
def ruleOff10 (i : Nat) := packedAt ruleOff10D (i*13) 13
def ruleEntry10D (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x400006a01a80001980350001fd4f92035012800017a035012800006a02b00000d405600001a80ac00006a02c011406a82200001a8f9203e01aa08800005802280d524200002280d4040b1b00000d404031a00000d404000003280d424401f00000d563600e0000fd40d2133212000075400003b056805200002b80e005282400000a424800003d00b4052d1b00000a402a0001fa809800007301300001b402601280000b0045013000108403e013000007c02668d800007c02600000f804c00007c009804a00001300940007f5035009904400003981a804c022000009802400e00001f007402d01280000c802500000b004a00001f309000003e61200007eac2468d80007eac2468d80007eac2468d8000fea82400700000d4045012a0900007de412003800006a3e300f804a8240000fd417482468d80000dc42400001ec0b405301d1090000424000109000042400010900004240001090000078032896844800e00001eddbc036092146c00006a09224840001240000fd4266c2200003e1044d1b007000104480f000208800082200020880008220002088000822000208800082200020880008220003ffc8440007ff9088000422207800084440f000108881e000211103c0004222078000844000211000084400021100008440000910001c420007108001c420007108001c42000710800184200003e81e004000003e80ec04000007c00800000f801000000e604801000008f007312d008002e000039808000006a3ef01080400000352484040000070808000006506f80b404001400003e01b40200000369c42020000016004000002281080400000228080a360003eb01090480200003bd5dac042092008000047807c010004000003600fc4480200000194074020000019007402000000bc04031a00000980400003e480f9048020000108804000007c3884040000010005c000020004000004000800000800100000100018000020003000004000007c03680a6f1b00001c1a3600e000346c000bff20d00017fe41a00037fc43400008d00000ca02078c8001a3200000c00000f804575b8444000a0f000283c00060f000183c00060f000183c00060f000183c00060f000183c00060f0000010000603000180c000d010003004000a010002804000a010002804000a01000280400060100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000412246c00082448d800104891b0002091236000412246c000824 else 0x1ffe0007ff8001ffe0007ff8001ffe0007ff8001ffe0007ff8001ffe0007ff8001ffe0007ff8001ffe0007ff8001ffe0007ff8001ffe0006ff8001bfe0006ff8001bfe0006ff8001bfe0006ff8001bfe0006ff8001bfe0006ff8001bfe0006ff8001bfe0006ff8001bfe0005ff80017fe0005ff80017fe0005ff80017fe0005ff80017fe0005ff8000ffe0003ff8000ffe0003ff8000ffe0003ff8000ffe0003ff8000ffe0003ff8000ffe0003ff8000ffe0003ff8000ffe0003ff8000ffe0003ff8000ffe0003ff8000ffe0003ff8000ffe0003ff8000ffe0003ff8000ffe0003ff8000ffe0003ff8000ffe0003ff8000ffe0003ff8000ffe00003f018401600003f00f800007e412002400007e28780000fa0e160500000fa04201f00000fa03d00001f007c72a00001f007402d00fac6c00007b02880e800007a02c80000f405900001e80b200003d016400007a02c80000f405900001e80b200003d016400007a02c80000f405600001e804a00007c0b781b405378d80001f003e00003e009412400001d00e400003a01c800007403900000e805f01700000e805f00080000e805f00080000e804c41200000e8c2100001cc0be82400001cc0be01f00880000e605f00880000e605f00880000e615a01d80000d47d6021208800006a3eb01090440000351f580840000351f5808400003500bc00006a01780000d402f00001a805e00003500bc00006a01400000d402600001a804c000035009800006a01300000d402600001a8f9203e15ca08800006a41100000d482200001a8fac91b00001a809c04548d80000d4f1900001a96a800e00001a800007003080f8000ede08880008b403f01d346c02a00007c036807c02f78d80001b40531e33c6c00005801f00000b0111000016001c000033814c0000530221c3c000053092005800006d029000009c82400001e409a030000019809a03d000013583a000032818589803e00003280000ca000018cc9e045000011448400002294cc00004555c808000004501000000b0045088800008a111000011401c0000378158088000031816c088000031993c088000031993c08800002200940000441950c4c0000f822120900000f802100f80003f502130900400000351d0400074100001bcc9e040000016008001200001f80e803e00001a407c00002c00f800006c02980f800055101f000009c03e612346c00003e612346c00003e412000007ceb7092000007cc2200e946c00003e212346c00043800008e000023800002e00000b800002e00000b80003adc23400031b8000c6e00031b8000c6e00031b8000c6e00031b8000c6e00031b8000c6e00007b80d) else (if i < 3 then 0x3000000c000003000000c000003000000c0002c6c01600000d002c00000b000002c00000b00004a9834c0a000306981400030d182800001a005000003400a000006801400000d002800001a00500000140040000028008000005001000000a00200000140001040000210000021002000001b00400004340130040000034008000006801000000d002000001a0040000034008000006801000000d002000001a0040000034008000006801000000d0020000c87000301c000d19543800150e0030002a1da02000543b404000a8700000f530e000209a21c000887000221c000887000221c0002e034380012326870000b80d0ed01000121c000487000121c000487000121c000487000121c0004870000e1c000387000261c60e00006d021c000087000021c000087000021c000087000021c00006100200000c20040000184008000030001000002a0020000a34004000146800800018d001000001a0020000034004000006800800000d001000001a0020000034004000006800800000d001000001a0020000034004000006800800000d001000001a0020000034004000006800800000d001000001a00200000340040000020008000002000c00000400000100000616418000094c8300000b9906000195320c00032a641800190600064180019060006418001906000641800190600064180019060006418001906000641800190600064180019060006418001a36c03000346d80600068db00c00004a5418000094a83000143d5060005418000426883000220c000883000220c000883000220c000883000243cd060003418000906000241800090600020180013063030000038506000141800020600004180005c0d010000b19a0200015bb40400001a6808000034d010000069a0200000d340400001a6808000034d010000069a020006808001a020006808001a020006808001a020006808001a020006808001a020006808001a020006808001a020006808001a020006808001a020006808001a020006808001a020006808001a020006808001a0200068080019c0b0100013816020002702c0400001a5808000034b010000069602000247ac04000487580800090eb010002c04000b010002c04000b010002c040005c6500800004c701000221ce020004419c040007010001c040007010001c040007010001c040007010001c040007010001404000eb7180800190e301000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x1b0001c6c00061b30d0000c3661a000186cc3400030d986800061b30d0000c3661a000186cc3400030d986800061b30d0000c3661a000186cc3400030d986800061b30d0000c3661a000186cc3400030d9868000bc628d8000a36006000146c00051b000146c00011b000046c00001b00d000003601a000006c03400000d806800001b00d000003601a000006c03400000d806800001b00d000003601a000006c03400000d806800001b00d000003601a000006c03400000d806800001b00d000003601a000006c03400000d806800001b00d000003601a000006c03400000d806800001b00d000003601a000006c03400000d806800001b00d000003601a000006c03400000d806800001b00d000003601a000006c03400000d806800001b00d000003601a000006c03400000d806800001b00d000003601a000006c03400000d806800001b00d000047491a00001d407081a000146801c00028d001000051a0020000a3400028d0000a3400028d00000bc03820d000083400020d000075431a0000c6800800018d000025411a0000184034000025006800004a00d000007a01a00000e003400001c006800003800d000007001a00000e003400001c006800003300d000006601a000008c03400000e806800001a005000003400a0000068e0200000d000003400000d000003400000d00000d4f190003c64000f190003c64000f190003c64000f190003c64000f190000b81a3200016f34640002aa68c8000434d190000869a3200010d3464000d191438001a32287000346450e00068c8a0c000d190003464000d190003464000d190003464000d190003464000d190003464000d190003464000d190003464000d190003464000d190003464000d190003464000d190003464000d190003464000d190003464000d190003464000d190003464000d190003464000d190003464000d190003464000d190002464000919000246400091900024640009190002464000919000246400007338c8000e3200028caa0c0005195418000632c83000006803000a000006802c00000d005800001a00b000002c00000d005400001a00a80000cc014000019802800000d005000001600a0000028a070000050000c1a6098001834c13000286942600030d184c00051a2898000034013000006802600000d004c00001a0098000034013000006802600000d004c00001a0098000034013000006802600000980200000130040000026008000004c000013000018002400003010880240000090010000012002000151e000487800121e000487800121e0004878000c1e8870002adca1e000287a21c00004c287aa0c00050f000143c00050f000123c00048f000123c000022007340400000e680800001cd010000039a02000007340400000e000006801800000b00)) else (if i < 6 then (if i < 5 then 0x94000025000248d234000291946800002300d000004601a000008c034000011806800002300d000004601a000008c034000011806800002300d000004601a00001a9844d1b00001a9844000611104c000c3a6112048000c2200030880007c6411000104400041100010440004110001044000411000104400041100000d40ca31100000d4bc6211103c000065211103c00006521100007c04220002f188440005db908881e0005db9088000422010005c000422207800084440f000108881e00021100008440002110000844000211000084400007b08880260000350888000222009a20c0002220000488026000091043c000122087800024400a0000488e02000091000024400009100002440000910000244000091000017a23a011000004a0221438000044d1b0000088000032710807c000e210003884000e210003884000cf569080005bc023690800056ed210003484000d210003484000d210001cdd64200059080016420005908000d6e92100001a8040000035008000006a01000000d402000001a804000057000800006e0010206c000bc60100000f8c0200001b1804091b00001100400002210080000eb70100000d6e0200000adc04000015b808000002f010146c000d21010000004081d000008103a00001020740005c60103c6c00002078d8000040d1b0000081a360000160080e360000101c6c00002068c800004098f0001adc04048f0000adc04008f0000080018000010000004000001000000400000100000040000010000004000001000000400000100000040000010000004000008f800007801f00000a884401f000007c03400000f806800081d000207400006a20e800023a00008e800023a00008e8000fc001d000007403400000e806800001d00d000003a01a000007403400000e806800001d00d000003a01a000007403400000e800003a00000e8001e360170003c6d02600078da020000f1b0040001e360080003c6c000f1b000386c01000070d8001c3600070d80000cad1b0000195a36000032b46c0007c668d800058cd1b0000b19a3600001f346c00002f68d800005ed1b00000bda36000695346c0006aa68d8001844d1b000346c000d1b000346c000d1b000346c000d1b000346c000d1b000346c000d1b000346c000d1b000346c000d1b000346c000d1b000346c000d1b000346c000d1b000346c000d1b000346c000d1b000346c000d1b000346c000c1b60d0001836c1a00001996360000312c6c000b1b30d000163661a0002c6c03400058d8030000b1b003000163600058d800163600058d800163600058d800163600058d800163600058d800163600058d8001636000035246c00091b48d000123691a000246d2340000311c6c00002f38d8000e36c1a0001c6c00071b0001c6c00071b0001c6c0007 else 0x442000011448400012100f8c7400012100f000024200009080000f802100f000004201e000008403c000010807800002100f000004201e000008403c000010807800002100f000004201e000008403c000010807843a000010807843a0000108034000021006800004200d000008401a00001080340000210068000042580800008400002100000840000352d04000b410002d04000a41000190400064100019506820001a080006820001a0800008001a00003e007e00001f806800015e01f000007cab700000f92320001ef00f9a0200001f000007c00001f000008023d000010c17a00005e800017a00005e800008003d00000f403400002500f000004a01e000007803300000f006600001e00cc00003c011800007871b00000f120e00001e001000003c00000f000005805d000017402600002e800003d01d000007401a00000e803400002f32e4000cb900032e4000ab90002b7917200035c84e04440000a192e400003f15c800007203800030e000093815b907c00093800000fc67000019c000067000019c0000270cb700000f407000001c00ac000038015800007001f20d000007001a00000e003400001c006800003800d000007001a00000e003400075b8001b6e0006db800196e32a00032dc65400065b8ca8000cb700032dc000cb700032dc000cb700032dc00013855b800156e52a0002adca1e00055b943c000ab70002adc000ab70002adc0001434db800136e00045b800116e00045b800116e0003db8000f6e00035b80d80006b74950000d6e90f0001add21e00035b800096e00025b800096e00025b800076e00015b800016e000499a46800093348d0000a6651a00004cc01c000099801800013300004cc00013300004cc00013300001800660000360528066000019b06800003360d000006601a00000cc034000019806800003300d000006601a00000cc034000019806800003300d000006601a00000cc034000019806800003300d000006601a00000cc034000018801000003100000c0c34000018186800002f611000005ec2200000bc844000017806c00002f00d800005e91900000bcc4401600000bc02c0000178468c1e000017b40400002f00000e005c000017086800e00001c00b843400800000b94020005e300b400002d5808001b8c02c00000b0826000016102800002c680800005800003780ac00006b015800005601a00032a8000aaa0002aa80000624d500012540004950001254000495000125400049500012540004950000e5400035534640006aa5808000d540002d50000a540002950000a5400025500007540001d500007540001d500007540001d500000f632a0000ca8c440000168aa800012a000290807c026000290807c02600000f804c0000130080000026007000004c000013000004a01a0000) else (if i < 7 then 0x6800006a68c80000d4d1900001a9a32000035346400006a68c80000d471900001a82320000351888824000035323c00006a34780000d4c8700001a990e000035321c00006a34380000d448700001a800006a00001c88d206200011a40d0a8700009a400026900005a4000069022346400016800001c80d000003901a000006800d00000d001a00001a00340000340068000068000019983400003330680000652b000000ca04a00f80000ca01b0000194034000032806800006510980000c402c0000184a36000030946800006128d00000c22b700200000c22b700200000c22b700200000c2ce000001859c000067000019c000067000019c000067000015c00004f000011c000047000011c000047000011c00002f000000ca56000013800004e00000f800003e000027806c00004f00d800002e068c80003c000007000001c000007000001be00006f80001be00006f80001be00006f8001dbc03800027780009de00027780006de02100009bc00016f00f004600016f34640002de000017807000006d15180000da1a300001b401a00003680000da00003680000da00003680000da00003680000da00003680000da00003680000da000156409a00002c007ce1e00002c007ce1e00002c3c6c00005858d80000b0b1b00027580009d600027580009d600027580008d601780011ac0002eb00009ac0001eb00016a800032a00006a80001aa00006a80001aa00000a66220000345636000029814000005000d00000a001a000013c0340000270a0c00006102691300000cc00001300340000260001894000225004c0100002250000494883000092800024a000092800014a000052800076006518880000ca05e800019402600f800019408700003280000ca00003280000ca000012998c00002510880240000278128834000025006800004a00d000009401a0000128034000025006800004a00d000009401a000012800004a000013d99201a000013d99201a00027240009c9000013119200026480000a604800001cc08e0000238108000047012800008e023000011c046000023808000004718d800008e00400037181540006e3346c000dc60003718000dc60003718000cc601c000198c000663000198c000663000178cd1b00001a158c50f0002b18a1e000563143c000068563100c000ac60002b180009c600027180009c60002318084000463000118c0000329f180007c600013180004c600013180003c6012800078c0001e3000078c0001e3000078c0001e3000078c0001e3000078c0001e3000078c000163000008a0000228000088a230002380088f1b0000111e3600002224640000c3180800188403e61d0001484a3a000011108400042100f000084200021080008420002108000842000210800044201e000088403c0001108000 else 0xff00001f538c41300001ec06600003da10805800007c01c80000f846f00001f00c900003e007e00007c0edc0000f819b80001f042200003e010600007c00001f000007c00001f000007c00001f000007c00001f000007c00001f000007b81a00000f700003dc00007701f00e000007701f00e000007701f00e000007701c008000007700d00001ec0ca00d806800007600d00000ec01a00001d803400057a80fc04400057a80013ea00027a81840940001faa2e400007336300000e6d0100001cc00007200001b4034000036ac6c43400c00001b400006c00001ac056000035032800006a61100000d4d2100001a9e360000353c6c00006a78d80000d43e068d80000d411b00001a82340000350468000073035)))
def ruleEntry10 (i : Nat) := packedAt ruleEntry10D (i*13) 13
def rules10 (i : Nat) := collectCertFields ruleEntry10 7 5 (ruleOff10 (i/1))
def disp10D (i : Nat) : Nat := 0x49880600302380c04c042cc0c00040060e0052500059994200f04512ca0d360c30054088801a00103000058328108040408c8100089012400001283c689040488a0004480060058706041800000488
def disp10 (i : Nat) := packedAt disp10D (i*7) 7
def slot10D (i : Nat) : Nat := 0xaea3e0780af10906e6820170c51730b91b979309d0501230bc4af3c80696620450c609800b08c6431750010b00424700c00a803c04d06d06c07404aabd06e19009601801505605b17c09f07e09c0bf08b04706400001e0b71860ca0a60220110a202f08d15104d57109e08a05f1320ae10000a0a30aba1d04200000007d03800007906b0040b27000490720000881520444480000000000340000c61b96bb08308d0970100b501602a0251400000310af0be00f04e03b0c209402705d0550b811a0a112b09205a0000ad1bd30e0b616e7760030000120140630cb18c20004da0000000809902900005f65c0350b105f0c76610481411463070aa0ae0000b300004e10000005800001f0b90000454000000390c11b804b02f64f05908f04308702526f03a0c30961c7047a2d0cc06e0910c01a70190a104a09b22e0801000ad0570a00c40770421020ab07b04613308800009b00003060003604108400003d0000000ba0670c1026bb214403f0240a504c09bab206000c01b0810b608003005e0260c562800007f1130be10d00005b0210b706e21c0a90000a406f24606d1540c902509a06a0060cb08e0000000000950000000000370261b417a06808c0530890000200b40660c502c0000690000ac08503025007f0050bc0c41650
def slot10 (i : Nat) := packedAt slot10D (i*12) 12
def lookup10 (h : Nat) : Option (Nat × Nat) :=
  let v := slot10 ((h/91+disp10 (h % 91))%317)
  some (v >>> 4,v &&& 15)
def step9D (i : Nat) : Nat := 0x6e40d21a930e5b17578a0eaf141d3c443a8ff836f158ea6191541a714525c6a496cbb14d5872312ec34d75869cba8d39729a23b76cc752bb8ea575154b8a3ae3216a08c4c149c0db5c419549c752908eb5201d628130e4b661869cc15260dc230bb136c772a005d53f0badd21754f82ea528ebc871d690a305294762520c161f1d7c3e3b187c741c68c3b811d66fc3acdec5db6f0eb3961d76da2ed07074ee00e8b6a1d666e3accd875891acc0c65a8c9017591c2e88c2b2aab1d453e3a9bd0660a14c3a7618750a3ac9b8758494aa125954a363a8ea436c6496ea3e18747830f46c764a395da381d678a1b64dcaede206dbae1d4306576f18751670eb3c30dba6c1b4b3475b200eb63a0cb76a3a8ed07517e8eb88f58613eb26a6c371158bb4aa0dac7e3a4b307586816ecee0cbc7c3a4b2875a76865ef00dc5f63af2586a4492cb8925954303ae31161de10ebbc21d27903b8f2075de40eb3c81d27903a035e74d020691fb1d7da01b427961868ac30d18c61132a87d4760fa8c10d52dd1a8bb04b575c9daec1185d71a65ba34d75c69c6b8e15d71c2baa3a1760742e914f5d5118baa522551648eb1452ddcac196ea0371d386e2c81d758e3acaec32dd306e3b11d45823af6ac371d286e5aa0dc3d02ec49565c92acacc50dc19055432169c642d31235a82472ec48d59491caa14b0d229e3ae39c740b68650e11d71f43b43e875c7d0eb0fa1d229e3b053c758a78ea8f91d61f43b647c76c4a86d8801d800a554010aa8021440032aa00651000c9dc011550022880044ee008998009550012880024ee0049980092a8061d6
def step9 (i : Nat) := packedAt step9D (i*23) 23
def ruleOff9D (i : Nat) : Nat := 0x12a9449a49229047637198bc56271187c36170983c1607017fbf5f6f87b3d1e4f0773b1d4e873391c4e06f371b2d76ab4da2ce6632990c66230980be5e2e970b65a2c960ae562a950a652289409e4e26930964a24d24914823d1c8d4622d14894421d0c854220d0481401fcfc7d3e1ecf4793c1dcec753a1cce471381bcdc6d361acd4693419ccc653218cc4613017cbc5d2e16cb4592c15cac552a14ca4512813c9c4d2612c94492411c8c452210c8441200fc7c3d1e0ec74391c0dc6c351a0cc642f168a84e25118843e1d0d8642e15098482210078381a0c058281208038180a04018080200
def ruleOff9 (i : Nat) := packedAt ruleOff9D (i*9) 9
def ruleEntry9D (i : Nat) : Nat := 0x1a9d1b00007e0000016000000c900000c90001cc60001bc6743c0006b180006b180005f1800057180001f180001f180001f180001f180001f180001f1800000e00006adc0006adc0006adc00068dc0003adc0001edc00000bdd0f000022c0001caa000192a000192a00007aa00007aa00007aa000022a000002500014220000c220000c220000c2200004220000bc6008000000800000080000008000000800002f19d1b0001d1b0000d1b0001d190001d190001d190001d190001d190001d190001d19000191900019190001919000190f000190f000090f000088f0000887000088700007870001c830001a83000080300002830001d010001d010001d010000f010000f0100007010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006a5f1800001a80000911c22000002600940006090000609000060900006090000609000060900006090000609000060900000018000000000000000000000000000000000000000000000000000000000000000000
def ruleEntry9 (i : Nat) := packedAt ruleEntry9D (i*14) 14
def rules9 (i : Nat) := collectCertFields ruleEntry9 7 2 (ruleOff9 (i/1))
def disp9D (i : Nat) : Nat := 0
def disp9 (i : Nat) := packedAt disp9D (i*1) 1
def slot9D (i : Nat) : Nat := 0x11400c20
def slot9 (i : Nat) := packedAt slot9D (i*6) 6
def lookup9 (h : Nat) : Option (Nat × Nat) :=
  let v := slot9 ((h/2+disp9 (h % 2))%8)
  some (v >>> 4,v &&& 15)
def step8D (i : Nat) : Nat := 0xc31e7771e4431e7c31e8
def step8 (i : Nat) := packedAt step8D (i*20) 20
def ruleOff8D (i : Nat) : Nat := 0x688
def ruleOff8 (i : Nat) := packedAt ruleOff8D (i*3) 3
def ruleEntry8D (i : Nat) : Nat := 0x2f8c00000000000
def ruleEntry8 (i : Nat) := packedAt ruleEntry8D (i*15) 15
def rules8 (i : Nat) := collectCertFields ruleEntry8 7 1 (ruleOff8 (i/1))
def certStep : Nat → Nat → Nat
  | 8 => step8
  | 9 => step9
  | 10 => step10
  | 11 => step11
  | 12 => step12
  | 13 => step13
  | _ => fun _ => 0
def certRules : Nat → Nat → List (Nat × Nat)
  | 8 => rules8
  | 9 => rules9
  | 10 => rules10
  | 11 => rules11
  | 12 => rules12
  | 13 => rules13
  | _ => fun _ => []
def certIndex : Nat → Nat → Option (Nat × Nat)
  | 9 => lookup9
  | 10 => lookup10
  | 11 => lookup11
  | 12 => lookup12
  | 13 => lookup13
  | _ => fun _ => none
def certCount : Nat → Nat
  | 13 => 12
  | 12 => 376
  | 11 => 3273
  | 10 => 1819
  | 9 => 205
  | 8 => 4
  | _ => 0

def certRecipe : Nat → Nat → Nat × Nat
  | 0,i => let r := certStep 13 i; (r &&& 1048575,r >>> 20)
  | d+1,i =>
    let w := certStep (12-d) i
    let (ops, mask) := certRecipe d (w >>> 12)
    let o := w &&& 1023
    let a := o &&& 15
    let b := (o >>> 4) &&& 15
    let del := (if w.testBit 10 then 0 else 1 <<< a) ||| (if w.testBit 11 then 0 else 1 <<< b)
    (ops ||| (o <<< (10*(2+d))), (mask ^^^ (mask &&& del)) ||| (1 <<< (11+d)))

def certRead (k i : Nat) :=
  let d := 15-k
  let (ops,mask) := certRecipe (13-k) i
  let bank := decodeBank d ops (wiresOf dead)
  (ops,bank,selectLive mask bank)
def certState (k i : Nat) := (certRead k i).2.2.map Prod.fst
def certCols := deadcolumns ++ [(0,0,511,0,15)]
def certGraph : Forest := (511,13,dead.samples,certCols,deadautos,deadlevels,deadindex)
def certLink (k : Nat) (p : Nat × Nat) : Option (List Sig) :=
  if p.1 < certCount k then (deadautos[p.2]?).map (fun s => (certState k p.1).map (movedWord (s.map swapRows).reverse)) else none
def certContext (k i : Nat) : NodeContext :=
  let (ops,bank,ws) := certRead k i
  let rules := (certRules k i).filterMap (fun (j,paid) => buildRule certGraph ops (15-k) bank j paid)
  (k,ws.length,ws,preCov ws,rules,fun tag => ((certIndex k tag).bind (certLink (k-1))).toList)

set_option maxRecDepth 16384 in
theorem certLow511 : Lower (vars 511) (graphGoal 511) 15 := by
  rw [show graphGoal 511 = graph by decide +kernel, show vars 511 = inputs by decide +kernel]
  apply lower_impossible graph_proper
  · intro a ha
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp (input_list.symm ▸ ha : a ∈ List.ofFn (fun j : Fin 9 => inputs.getD j.val zero))
    subst a
    obtain ⟨hd,hs⟩ := Bool.and_eq_true_iff.mp (seed_witness i)
    refine ⟨absentRow i,presentRow i,bne_iff_ne.mp hd,?_⟩
    intro v hv ne
    have test := List.all_eq_true.mp hs v (List.mem_append_left _ hv)
    exact beq_iff_eq.mp ((Bool.or_eq_true_iff.mp test).resolve_left (fun h => ne (beq_iff_eq.mp h)))
  · exact dead_start (before_sound _ valid383) geomdead tablesdead

def certPrior (q : Nat) := if q=511 then 15 else boundsBefore known383 q
theorem certPrior_ok (q : Nat) : Lower (vars q) (graphGoal q) (certPrior q) := by
  by_cases h : q=511
  · subst q; exact certLow511
  · simpa [certPrior,h] using before_sound known383 valid383 q
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem certGeom : graphValid certGraph certPrior = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem certSlices : ∀ ci ∈ certCols, Slice (vars 511) graph (subcube ci.1 ci.2.1) ci.2.2.2.2 := by
  have h := certGeom
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true] at h
  rw [← show chartGoal 511 = graph by decide +kernel]
  exact fun ci hc => col_sound ci certPrior certPrior_ok (h.1.2 ci hc)
def certCheck (k i : Nat) :=
  let c := certContext k i
  prelim graph c && testAll c c.2.2.1
set_option maxRecDepth 16384 in
theorem certStepSound {k i : Nat}
    (prior : ∀ j < certCount (k-1), Impossible graph (k-1) (certState (k-1) j).toFinset)
    (ok : certCheck k i = true) : Impossible graph k (certState k i).toFinset := by
  have g := certGeom
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at g
  simp only [certCheck,prelim,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at ok
  have tg : chartGoal 511 = graph := by decide +kernel
  have pairs := chart_pairs (m:=511) (p:=fun j => (dead.samples j).1) (q:=fun j => (dead.samples j).2) g.1.1.1 g.1.1.2
  rw [tg] at pairs
  apply node_sound (raw:=vars 511) (r:=asRow fun j => (dead.samples j).1) (s:=asRow fun j => (dead.samples j).2)
      (ws:=(certRead k i).2.2) pairs _ ok.1.1 (by change graph ∉ (certContext k i).2.2.1.map Prod.fst; simpa only [List.contains_eq_mem,decide_eq_false_iff_not] using ok.1.2) _ _ ok.2
  · intro w hw
    apply decode_faithful _ _ _ _ _ (wires_faithful dead)
    exact (selectLive_sub _ _).subset hw
  · intro p hp
    obtain ⟨⟨a,b⟩,_,hh⟩ := List.mem_filterMap.mp hp
    rw [← tg]
    apply buildRule_sound certGraph _ hh
    change ∀ ci ∈ certCols, Slice (vars 511) (chartGoal 511) _ _
    rw [tg]
    exact certSlices
  · intro tag xs hx
    have hh : ((certIndex k tag).bind (certLink (k-1))) = some xs := by simpa using hx
    obtain ⟨⟨j,p⟩,_,hh⟩ := Option.bind_eq_some_iff.mp hh
    unfold certLink at hh
    split at hh
    next hj =>
      cases ep : deadautos[p]? with
      | none => simp [ep] at hh
      | some perm =>
        simp [ep] at hh
        subst xs
        have hm : perm ∈ certGraph.autos.toList := by change perm ∈ deadautos.toList; simpa using Array.mem_of_getElem? ep
        have auto := g.2 perm hm
        change autoOK (chartGoal 511) _ = true at auto
        rw [tg] at auto
        exact rotate_excluded (prior _ hj) _ auto
    next => contradiction

def certBlock (k i n ar : Nat) :=
  let xs := (List.range n).map (fun j => certContext k (i+j))
  xs.all (fun c => c.2.1==ar && prelim graph c) && runBatch k ar xs
theorem certBlock_ok {k i n ar j : Nat} (h : certBlock k i n ar=true) (hj : j<n) :
    certCheck k (i+j)=true := by
  let xs := (List.range n).map (fun z => certContext k (i+z))
  have hlen : j<xs.length := by simpa [xs] using hj
  have hx : xs[j] = certContext k (i+j) := by simp [xs]
  have mem := List.getElem_mem (l:=xs) hlen
  change (xs.all _ && runBatch k ar xs) = true at h
  have b := Bool.and_eq_true_iff.mp h
  have left := Bool.and_eq_true_iff.mp (List.all_eq_true.mp b.1 _ mem)
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hx ▸ left.2,?_⟩
  have arity := beq_iff_eq.mp left.1
  have q := runBatch_at (q:=j) (xs:=xs) hlen (by rw [hx]; rfl) arity (by rw [hx] at arity ⊢; exact arity) b.2
  exact hx ▸ q
def segment (k ar : Nat) : Nat → Nat → Nat → Prop
  | 0,i,n => certBlock k i n ar = true
  | d+1,i,n => segment k ar d i (n/2) ∧ segment k ar d (i+n/2) (n-n/2)
theorem segment_elim {k ar d i n j : Nat} (h : segment k ar d i n) (lo : i ≤ j) (hi : j < i + n) :
    certCheck k j=true := by
  induction d generalizing i n with
  | zero =>
    have e := certBlock_ok (j:=j-i) h (by omega)
    simpa [Nat.add_sub_of_le lo] using e
  | succ d ih =>
    by_cases hj : j < i + n/2
    · exact ih h.1 lo hj
    · exact ih h.2 (by omega) (by omega)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v8_0 : segment 8 9 0 0 4 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v9_0 : segment 9 9 1 0 33 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v9_33 : segment 9 10 3 33 172 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v10_0 : segment 10 9 0 0 6 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v10_6 : segment 10 10 5 6 459 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v10_465 : segment 10 11 5 465 512 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v10_977 : segment 10 11 5 977 512 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v10_1489 : segment 10 11 4 1489 330 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v11_0 : segment 11 9 0 0 1 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v11_1 : segment 11 10 2 1 76 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v11_77 : segment 11 11 5 77 512 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v11_589 : segment 11 11 5 589 512 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v11_1101 : segment 11 11 5 1101 512 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v11_1613 : segment 11 11 4 1613 269 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v11_1882 : segment 11 12 5 1882 512 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v11_2394 : segment 11 12 5 2394 512 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v11_2906 : segment 11 12 4 2906 367 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v12_0 : segment 12 10 0 0 15 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v12_15 : segment 12 11 3 15 193 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v12_208 : segment 12 12 3 208 168 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v13_0 : segment 13 11 0 0 12 := by
  simp only [segment, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
lemma valid8 (i : Nat) (hi : i < 4) : certCheck 8 i = true := by
  exact segment_elim v8_0 (by omega) (by omega)
lemma valid9 (i : Nat) (hi : i < 205) : certCheck 9 i = true := by
  by_cases h2 : i < 33
  · exact segment_elim v9_0 (by omega) (by omega)
  · exact segment_elim v9_33 (by omega) (by omega)
lemma valid10 (i : Nat) (hi : i < 1819) : certCheck 10 i = true := by
  by_cases h2 : i < 465
  · by_cases h4 : i < 6
    · exact segment_elim v10_0 (by omega) (by omega)
    · exact segment_elim v10_6 (by omega) (by omega)
  · by_cases h4 : i < 977
    · exact segment_elim v10_465 (by omega) (by omega)
    · by_cases h6 : i < 1489
      · exact segment_elim v10_977 (by omega) (by omega)
      · exact segment_elim v10_1489 (by omega) (by omega)
lemma valid11 (i : Nat) (hi : i < 3273) : certCheck 11 i = true := by
  by_cases h2 : i < 1101
  · by_cases h4 : i < 77
    · by_cases h6 : i < 1
      · exact segment_elim v11_0 (by omega) (by omega)
      · exact segment_elim v11_1 (by omega) (by omega)
    · by_cases h6 : i < 589
      · exact segment_elim v11_77 (by omega) (by omega)
      · exact segment_elim v11_589 (by omega) (by omega)
  · by_cases h4 : i < 1882
    · by_cases h6 : i < 1613
      · exact segment_elim v11_1101 (by omega) (by omega)
      · exact segment_elim v11_1613 (by omega) (by omega)
    · by_cases h6 : i < 2394
      · exact segment_elim v11_1882 (by omega) (by omega)
      · by_cases h8 : i < 2906
        · exact segment_elim v11_2394 (by omega) (by omega)
        · exact segment_elim v11_2906 (by omega) (by omega)
lemma valid12 (i : Nat) (hi : i < 376) : certCheck 12 i = true := by
  by_cases h2 : i < 15
  · exact segment_elim v12_0 (by omega) (by omega)
  · by_cases h4 : i < 208
    · exact segment_elim v12_15 (by omega) (by omega)
    · exact segment_elim v12_208 (by omega) (by omega)
lemma valid13 (i : Nat) (hi : i < 12) : certCheck 13 i = true := by
  exact segment_elim v13_0 (by omega) (by omega)
lemma checkedStates (k : Nat) (hk : k ≤ 13) (i : Nat) (hi : i < certCount k) :
    certCheck k i = true := by
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact valid8 _ hi
  · exact valid9 _ hi
  · exact valid10 _ hi
  · exact valid11 _ hi
  · exact valid12 _ hi
  · exact valid13 _ hi
lemma closedStates (k : Nat) (hk : k ≤ 13) : ∀ i < certCount k, Impossible graph k (certState k i).toFinset := by
  induction k with
  | zero => exact fun i hi => False.elim (Nat.not_lt_zero i hi)
  | succ k ih =>
    intro i hi
    apply certStepSound _ (checkedStates _ hk _ hi)
    exact ih (by omega)
-- For each disjoint pair, two assignments witness the need for each original input,
-- even when both additional OR values are available. Only their two membership bits vary.
def pairAt (p : Fin 21) : Fin 9 × Fin 9 :=
  ([(1,2),(1,3),(1,5),(1,6),(1,7),(1,8),(2,3),(2,5),(2,6),(2,7),(2,8),(3,5),(3,6),(3,7),(3,8),(5,6),(5,7),(5,8),(6,7),(6,8),(7,8)] : List (Fin 9 × Fin 9)).getD p.val (1,2)
def rootHelp (p m : Nat) := (0x101321fa11fa01fa102321fa11fa01fa002b21fa11fa01fa100f21fa11fa01fa102f21fa11fa01fa101721fa11fa01fa101f21fa11fa01fa100321fa11fa01fa000321fa11fa01fa100721fa11fa01fa002721fa11fa01fa002321fa11fa01fa001321fa11fa01fa100b21fa11fa01fa001f21fa11fa01fa000b21fa11fa01fa001721fa11fa01fa002f21fa11fa01fa001b21fa11fa01fa000721fa11fa01fa000f21fa11fa01fa >>> (16*(4*p+m))) &&& 65535
def witnessRow (p : Fin 21) (j : Fin 9) : Row :=
  Fin.ofNat 512 ((0x88820080201020080210200120001008100401080208882008040802008404004014000204010042008100090001020080210040104441008100401080200802008060002008401028010040290010042008020280201220080210040100409008900401080900802008040902008401004010040204400042008024100201021200210040100405008104401080200802008040808008401404010040204014042008110080201020090210040100401008100440080200802410040802120401004010040212010242008020080201020080810 >>> (9*(9*p.val+j.val))) &&& 511)
def toggleRow (p : Fin 21) (j : Fin 9) : Row :=
  Fin.ofNat 512 ((witnessRow p j).val ||| (1 <<< j.val))
def firstOr := bin true (inputs.getD 0 zero) (inputs.getD 4 zero)
def secondOr (p : Fin 21) :=
  bin true (inputs.getD (pairAt p).1.val zero) (inputs.getD (pairAt p).2.val zero)
def avail1 (p : Fin 21) := inputs ++ [firstOr,secondOr p]
def rootList (p : Fin 21) (m : Fin 4) :=
  (inputs ++ (if m.val.testBit 0 then [firstOr] else [])) ++
    (if m.val.testBit 1 then [secondOr p] else [])
set_option maxRecDepth 16384 in
theorem proofRows : ∀ (p : Fin 21) (j : Fin 9),
    witnessB graph (avail1 p) (inputs.getD j.val zero) (witnessRow p j,toggleRow p j) = true := by
  decide +kernel
theorem rootForm {p : Fin 21} {k t S} (h : Live graph k t S) (sub : ∀ a ∈ S, a ∈ avail1 p) :
    ∃ m : Fin 4, (rootList p m).toFinset = S := by
  classical
  have needed (w : Sig) (hw : w ∈ inputs) : w ∈ S := by
    rw [←input_list, List.mem_ofFn] at hw
    obtain ⟨j,rfl⟩ := hw
    obtain ⟨r,s,hd,iso⟩ := witnessB_sound (proofRows p j)
    exact raw_required h _ _ sub r s hd iso
  have pick (a b : Bool) : ∃ m : Fin 4, m.val.testBit 0=a ∧ m.val.testBit 1=b := by
    revert a b
    decide
  obtain ⟨m,e0,e1⟩ := pick (decide (firstOr∈S)) (decide (secondOr p∈S))
  refine ⟨m,?_⟩
  ext w
  have hs (hw : w ∈ S) : w ∈ inputs ∨ w = firstOr ∨ w = secondOr p := by simpa [avail1] using sub w hw
  by_cases h0 : firstOr∈S <;> by_cases h1 : secondOr p∈S <;>
    simp [rootList,e0,e1,h0,h1] <;> grind
def rootChoices (p : Fin 21) : List Choice :=
  [(1,inputs.getD 0 zero,inputs.getD 4 zero),
   (1,inputs.getD (pairAt p).1.val zero,inputs.getD (pairAt p).2.val zero)]
def rootGuard (p : Fin 21) (m : Fin 4) :=
  let w := rootList p m
  let h := rootHelp p.val m.val
  let a := (h >>> 2) &&& 1023
  let b := h >>> 12
  match h &&& 3 with
  | 0 => w.contains one
  | 1 => let r := Fin.ofNat 512 a; let s := Fin.ofNat 512 b
         (bit r graph != bit s graph) && w.all (fun x => bit r x == bit s x)
  | 2 => match certCols[a]? with
         | none => false
         | some ci =>
           let d := subcube ci.1 ci.2.1
           let cs := selectLive b (rootChoices p)
           match makePool d (vars 511) cs with
           | none => false
           | some bank => poolCut d ci.2.2.2.2 13 cs.length bank w && decide w.Nodup
  | _ => match certLink 13 (a,b) with
         | none => false
         | some v => sameWords w v
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem guardOK : ∀ (p : Fin 21) (m : Fin 4), rootGuard p m=true := by decide +kernel
theorem finishRoot (all : ∀ j<certCount 13, Impossible graph 13 (certState 13 j).toFinset)
    (p : Fin 21) (m : Fin 4) : Impossible graph 13 (rootList p m).toFinset := by
  let w := rootList p m
  have ok := guardOK p m
  unfold rootGuard at ok
  dsimp only at ok
  split at ok
  · intro k t hk h
    have mem := List.mem_toFinset.mpr (List.contains_iff_mem.mp ok)
    exact (live_proper h one mem).2 rfl
  · intro k t hk h
    obtain ⟨hd,ha⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨v,hv,ne⟩ := live_row_difference h (bne_iff_ne.mp hd)
    exact ne (beq_iff_eq.mp (List.all_eq_true.mp ha _ (List.mem_toFinset.mp hv)))
  · split at ok
    next => contradiction
    next ci hh =>
      split at ok
      next => contradiction
      next bank hb =>
        have cut := Bool.and_eq_true_iff.mp ok
        exact poolCut_sound (certSlices _ (List.mem_of_getElem? hh)) _ hb (of_decide_eq_true cut.2) cut.1
  · split at ok
    next => contradiction
    next v hh =>
      rw [sameWords_sound ok]
      unfold certLink at hh
      split at hh
      next hj =>
        cases ep : deadautos[rootHelp p.val m.val >>> 12]? with
        | none => simp [ep] at hh
        | some perm =>
          simp [ep] at hh
          subst v
          apply rotate_excluded (all _ hj)
          have g := certGeom
          simp only [graphValid,Bool.and_eq_true,List.all_eq_true] at g
          have hm : perm ∈ certGraph.autos.toList := by change perm ∈ deadautos.toList; simpa using Array.mem_of_getElem? ep
          have ha := g.2 perm hm
          rwa [show targetOf certGraph = graph by decide +kernel] at ha
      next => contradiction

set_option maxRecDepth 16384 in
lemma listedPair : ∀ a b : Fin 9, a ≠ b → Disjoint ({a,b} : Finset (Fin 9)) {0,4} →
    ∃ p : Fin 21, ({a,b} : Finset (Fin 9)) = {(pairAt p).1,(pairAt p).2} := by decide +kernel

theorem conclude (closed : ∀ i < certCount 13, Impossible graph 13 (certState 13 i).toFinset)
    (p : Fin 21) (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C) (small : C.size ≤ 13)
    (correct : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [x 0 || x 4,x (pairAt p).1 || x (pairAt p).2]) = edge x) : False := by
  have aligned (r : Row) : (avail1 p).map (bit r) = List.ofFn (sample r) ++
      [sample r 0 || sample r 4, sample r (pairAt p).1 || sample r (pairAt p).2] := by
    simp only [avail1,List.map_append,List.map_cons,List.map_nil,firstOr,secondOr,bit_bin,sampled]
    rfl
  have goal : (execute C.gates (avail1 p)).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r _ = bit r graph
    rw [←b_read,execute_bits _ _ _ (fun g hg => (fan g hg).1),edge_table,aligned]
    exact correct (sample r)
  have out := get_rep (execute C.gates (avail1 p)) C.output
  rw [goal] at out
  obtain ⟨k,t,S,hk,run,sub⟩ := extract C.gates _ fan graph_proper (out.resolve_right fun h => h graph_proper)
  obtain ⟨m,hm⟩ := rootForm run sub
  exact finishRoot closed p m k t (hk.trans small) (hm.symm ▸ run)
end PEqualNP.Outside.L_meta_3634

theorem PEqualNP.Outside.L_meta_3634 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card = (2 : ℕ) → x2 ≠ {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → Disjoint x2 {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → x1.size = (13 : ℕ) → (∀ (x8 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x9 ∈ x2, x8 x9 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x9.1 && x8 x9.2) → False := by
  intro C S fan hc _ hd hs he
  obtain ⟨a,b,hab,eq⟩ := Finset.card_eq_two.mp hc
  obtain ⟨p,hp⟩ := PEqualNP.Outside.L_meta_3634.listedPair a b hab (eq ▸ hd)
  rw [eq,hp] at he
  apply PEqualNP.Outside.L_meta_3634.conclude (PEqualNP.Outside.L_meta_3634.closedStates 13 (by decide)) p C fan hs.le
  intro x
  simpa [PEqualNP.Outside.L_meta_3634.edge,Bool.or_assoc] using he x
