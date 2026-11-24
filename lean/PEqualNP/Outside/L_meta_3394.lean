import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3394
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
def keySet (xs : List Sig) :=
  let h := xs.foldl (fun v x => v+keyWord x) 0
  if h == 4441884182832514441 && xs.contains 0xfffffffffffffffffa00fa00fa00fa00fffffffffffffffffa00fa00fa00fa00fffffffffffffffffa00fa00fa00fa00fffffffffffffffffa00fa00fa00fa00 then h + 2^85 else h

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
def g15samples : Nat → Bits × Bits
  | 0 => (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919)
  | 1 => (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4)
  | 2 => (0xefbdbf97f9f6bf6a,0x102a401415600a0a)
  | 3 => (0xf3a9d7437375f5ba,0xfc028ab620235b0)
  | 4 => (0,0)
  | 5 => (0,0)
  | 6 => (0,0)
  | 7 => (0,0)
  | 8 => (0,0)
  | _ => (0,0)
def g15columns : IndexTree ColumnInfo := (IndexTree.leaf [])
def g15autos : Array (List Nat) := #[[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,g15samples,g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Nat → Bits × Bits
  | 0 => (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44)
  | 1 => (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b)
  | 2 => (0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4)
  | 3 => (0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002)
  | 4 => (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239)
  | 5 => (0,0)
  | 6 => (0,0)
  | 7 => (0,0)
  | 8 => (0,0)
  | _ => (0,0)
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
def g31 : Forest := ⟨31,6,g31samples,g31columns,g31autos,g31levels,g31index⟩
def g47samples : Nat → Bits × Bits
  | 0 => (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444)
  | 1 => (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919)
  | 2 => (0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4)
  | 3 => (0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812)
  | 4 => (0,0)
  | 5 => (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b)
  | 6 => (0,0)
  | 7 => (0,0)
  | 8 => (0,0)
  | _ => (0,0)
def g47columns : IndexTree ColumnInfo := (IndexTree.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,g47samples,g47columns,g47autos,g47levels,g47index⟩
def g55samples : Nat → Bits × Bits
  | 0 => (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888)
  | 1 => (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231)
  | 2 => (0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e)
  | 3 => (0,0)
  | 4 => (0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126)
  | 5 => (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471)
  | 6 => (0,0)
  | 7 => (0,0)
  | 8 => (0,0)
  | _ => (0,0)
def g55columns : IndexTree ColumnInfo := (IndexTree.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,g55samples,g55columns,g55autos,g55levels,g55index⟩
def g63samples : Nat → Bits × Bits
  | 0 => (0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208)
  | 1 => (0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5)
  | 2 => (0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212)
  | 3 => (0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4)
  | 4 => (0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51)
  | 5 => (0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2)
  | 6 => (0,0)
  | 7 => (0,0)
  | 8 => (0,0)
  | _ => (0,0)
def g63columns : IndexTree ColumnInfo := (IndexTree.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,g63samples,g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Nat → Bits × Bits
  | 0 => (0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444)
  | 1 => (0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909)
  | 2 => (0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452)
  | 3 => (0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac)
  | 4 => (0,0)
  | 5 => (0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9)
  | 6 => (0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6)
  | 7 => (0,0)
  | 8 => (0,0)
  | _ => (0,0)
def g111columns : IndexTree ColumnInfo := (IndexTree.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,g111samples,g111columns,g111autos,g111levels,g111index⟩
def g119samples : Nat → Bits × Bits
  | 0 => (0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888)
  | 1 => (0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421)
  | 2 => (0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996)
  | 3 => (0,0)
  | 4 => (0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374)
  | 5 => (0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261)
  | 6 => (0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca)
  | 7 => (0,0)
  | 8 => (0,0)
  | _ => (0,0)
def g119columns : IndexTree ColumnInfo := (IndexTree.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,g119samples,g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Nat → Bits × Bits
  | 0 => (0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264)
  | 1 => (0,0)
  | 2 => (0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9)
  | 3 => (0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32)
  | 4 => (0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108)
  | 5 => (0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519)
  | 6 => (0,0)
  | 7 => (0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826)
  | 8 => (0,0)
  | _ => (0,0)
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
def g189 : Forest := ⟨189,7,g189samples,g189columns,g189autos,g189levels,g189index⟩
def g127samples : Nat → Bits × Bits
  | 0 => (0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060)
  | 1 => (0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11)
  | 2 => (0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222)
  | 3 => (0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494)
  | 4 => (0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309)
  | 5 => (0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602)
  | 6 => (0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac)
  | 7 => (0,0)
  | 8 => (0,0)
  | _ => (0,0)
def g127columns : IndexTree ColumnInfo := (IndexTree.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,g127samples,g127columns,g127autos,g127levels,g127index⟩
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
def g191samples : Nat → Bits × Bits
  | 0 => (0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200)
  | 1 => (0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161)
  | 2 => (0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882)
  | 3 => (0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544)
  | 4 => (0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891)
  | 5 => (0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a)
  | 6 => (0,0)
  | 7 => (0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474)
  | 8 => (0,0)
  | _ => (0,0)
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
def g191 : Forest := ⟨191,10,g191samples,g191columns,g191autos,g191levels,g191index⟩
def g251samples : Nat → Bits × Bits
  | 0 => (0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140)
  | 1 => (0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9)
  | 2 => (0,0)
  | 3 => (0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2)
  | 4 => (0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c)
  | 5 => (0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09)
  | 6 => (0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142)
  | 7 => (0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474)
  | 8 => (0,0)
  | _ => (0,0)
def g251columns : IndexTree ColumnInfo := (IndexTree.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,g251samples,g251columns,g251autos,g251levels,g251index⟩
def g255samples : Nat → Bits × Bits
  | 0 => (0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0)
  | 1 => (0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101)
  | 2 => (0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02)
  | 3 => (0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184)
  | 4 => (0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819)
  | 5 => (0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802)
  | 6 => (0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214)
  | 7 => (0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8)
  | 8 => (0,0)
  | _ => (0,0)
def g255columns : IndexTree ColumnInfo := (IndexTree.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,g255samples,g255columns,g255autos,g255levels,g255index⟩
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
def g383samples : Nat → Bits × Bits
  | 0 => (0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80)
  | 1 => (0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201)
  | 2 => (0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512)
  | 3 => (0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204)
  | 4 => (0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039)
  | 5 => (0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002)
  | 6 => (0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464)
  | 7 => (0,0)
  | 8 => (0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)
  | _ => (0,0)
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
def g383 : Forest := ⟨383,12,g383samples,g383columns,g383autos,g383levels,g383index⟩
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
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=1) ?_⟩
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
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=1) ?_⟩
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
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=1) ?_⟩
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
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
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
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
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
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
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
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
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
def signed12Data (_ : Nat) : Nat := 0x4868888b547248409010325aa320d0000a11301ff803fd003fe00
def signed12Level : Packing := (3,1,6,0,0,7,0,signed12Data)
def signed11Data (_ : Nat) : Nat := 0x6448c8e4064e203b2246d689d8c10726450299120d680ec608161ec5d4c890b4761dc99040864a44822e4185820432524d24646d0c1072502c0bb190236b44d060a4839122817b5a276305240c89140d2a34640e0829e44820432289491720c242c1025926b68a46390812281614c890520ed24061364111648e429140b205324d146d68e40b241490725005b5926a8120536858a481a4796029ac935b5a23052409140d250b649a9148e4c8dad10629692028a00a7d21287048b83101c3b90a42c182480ec8905250144062b0c29e4c8203520c72641014ac20a7932080d81c8363042b0c26e4482034d6d688c14f2245020e03b932080b8040523e4c8201c03228a406726410239138806c81013c89040680644803e4c8203b490099123932080bc9904036448e4c8202e0322472102c1a0301912083936b472130180c89040f6b07806448e45ac8203c032247228902c1e030193452320839369614c9c890404806420e4dad1483c0106d68b224349e01916b912080d00c9c8a29040b07806420e4da48583b2247264101701912081a4b00c891c990a240780c0644820e4dad1c84c06032246d102c34a20190836b4521a4f0180c891c99041b5a2d2a8051e4c8202a04060726d68e41e03936b4520a810181c9b5a3907e87e32dddd98d53ceec91c3cbf7baab55b20acba5e9f19949178da89d8688338067d17ac7777327056e86cb6866696345f75e25b559856b5364e94ac46f4323dd3b837b33e3092cc28f2622351f81ab1661290d40a706a03d000ffc83803ff5ce00ffc73803ff54e00ffd43803ff8ce00ffd72803ff58a00ffd52803ff50a00ffd32803ff20600ffd41803ff4c600ffc31803ff48600ffe11803ff4c200ffd20803ff44200bfd84803ef91200bfd83802ff20e00bfd82803fb88a00bfd81802ff20600ff940803fe4c200ff830803fe48200ff910803fe04200ff984803fe55200ff983803fe20e00ff973803fe1ce00ff953803fe50e00ffa33803fe60a00ff972803fe58a00ff952803fe50a00ff932803fe60600ff881803fe50600ff931803fe0c600ff921803fe84600fba44803f68ce00fea22803fc84600
def signed11Level : Packing := (60,2,6,0,0,12,0,signed11Data)
def signed10Data (i : Nat) : Nat := if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0xccbaa5005fe25d52802ff126a9401f795354a00ff4b92a5005fe24552802ff532a14017f89850a00bfccba85005fe25d42802ff32ca14017f99550a00fdcc2285007ee55142802ff126a1401fb94350a00ff4b1285005fe24542802ff532994017f8984ca00bfccba65005fe25d32802ff32c994017f9954ca00bfcca265007f68cd32803fd2e499401fe9424ca00bfc48a65005fe24d81802ff53240c017f99420600bfcc9903005fe648818037f30240c017fa9950600bfc4c283005fe25d41802ff32aa0c01fb97450600fdcb2283005fe24d41803f7284a0c01ff08150600bfd4ca63005fe26131802ff32e98c017f8974c600bfccaa63005fe65131803fb10698c01fd9634c600fed19a63007fa24931803fb26498c01ff1714c600ff8a0a63005fea6431802ff13018c017f9970c600bfc4b863005fe65831802ff32a18c01f79950c600bfcca063007f68cc31802ff32418c01fd9310c600ff898863005fea6521802ff13090c017f99748600bfc4ba43005fe65921802ff32a90c017f99448600bfcc9a43005fe24d21803fd2c490c01ff13148600bfc4c423005fe65211802ff32708c017f89384600bfcc9423007fc60611803fe10308c01ff14184600ff898c23007fc0c611803fe24308c01fb88791200fdd3bc89007ee5da44803f72eb22401fb96591200fdc41c89007ee5ce44803f70e722401fb96391200fdca9c89007ee8ce44803f72e522401fb96291200fdca9489007ee4ca44803f710322401fb97191200fdc38c89007ee58644803f72a322401fb93191200fdc18c89007ee48644803f742322401fd9988ce00fec4c467007f661a33803fb30919c01fd9648ce00fecc9467007f660a33803fb2c519c01fd9528ce00feca1467007f664633803fb12319c01fd9818ce00fec40c67007f65c633803fb0e319c01fd9618ce00feca8c67007f650633803fb24319c01fda118ce00ff4c3c45007fa21e22803fd4ef11401fe98688a00ff4bb445007fa61622803fd2eb11401fe96588a00ff4c2445007fa5d222803fd2c911401fe95488a00ff4c1c45007fa20e22803fd2e711401fe87388a00ff4b1c45007fa54e22803fd28711401fea3388a00ff4c0c45007fa20622803fd2e311401fe87188a00ff4b0c45007fa54622803fd28311401fe93188a00ff418c45007fa84622803fe33108c01ff09884600ff8c1c23007fc20e11803fe2e708c01ff07384600ff919c23007fc64a11803fe30508c01ff17284600ff8b1423007fc54a11803fe28508c01ff132846009beca907005be65830802f7328084017d99304200bf4c9021005de654838027f33039c017b9941ce00bf4c90e7005fc64473802ef32a18c01f3a5591200fcd224670077a9de22803dd4cd11401f6a5588a00fd522445007f28ce22803fa46708c01fe22284600 else (if i < 2 then 0x9a43007fe60521803ff2e290c01ff95148600ffca0a43007fe4c521803ff13108c01ff98484600ffcaa423007fe24e11803ff30708c01ff88384600ffcb9c23007fe1ce11803ff2a708c01ff94384600ffd19c23007fe60a11803ff2e508c01ff95284600ffca1423007fe4ca11803ff30308c01ff94184600ffc98c23005df65483802ff32041c013fc985ce00bdeca0e7005fb64873802feb2239c017f9901ce009fe4c2a7004ff262338027f930b94013fc9854a00bfcc8103004ff261418027f93098c0177d950c600bfcc8063004ff2621180377ae8c2401bbd42612009fecb907004ff658838027fb2a41c01b7e5520e00deea9907004ff644838037ba6241c013fd9020e00df6c3c45006fb21e228037db0d11401eee6688a00df6c2c45007db956228037db0911401fae4488a00df6c1c45006fb889818027fb2840c01bbe44206009fec9903006fd504818027fb2040c01efa6650200ff511281007ee50540802ff130984017f9974c200bfc4ba61006fe61d30803df4cc984017f9954c200fbd2aa61005fe65130803f712898401bf9844c200fdd22261007f654d30803fb28698401fda334c200dfcc1261007fa88930802ff12298401fd9314c200bfccb861005fe65830803df4cc18401fda330c200bfcc9061007fa88830802ff322184017f99748200bfc4ba41005fe65920803df4cc904017f99548200fbd2aa41005fe65120803f7488904017f99348200bfc49a41006fe60d20803fd2e490401fe95248200ff4a1241005fe245208037f30290401fe92148200bfc4c221005fe65110803f7488884017f99344200bfc49a21005fe649108037f30488401fea2244200ff8a0a21007fc84510802ff326084017f99204200ff511021007fc84410802ff12ec24017f89361200bfc48b09005fe25d83802ff122c1c017fa9920e00bfccb907005fe65883802ff32a41c01f799520e00bfcca107006fe60c83802ff32441c017f99120e00bfd4cae7005fe26173802ff122b9c017fa991ce00dfccc0e7005fe26073802ff32839c01fb9941ce00fecb98e7005fe64873803fd32439c017f9911ce00ff8c88e7005fea6553802ff130a9c017f89754e00fbcc2aa7007de55153803fb106a9c01fd97354e00bfc48aa7005fea6543802ff130a1c017f99750e00bfc4ba87005fe65543803f72e8a1c01fd88350e00bfc48a87005fe26233802ff32f19c017f8978ce00bfccb467005fe65633802ff32919c01fd9838ce00fec41c67007f65ce33803fb0e719c01fd9538ce00feca1c67005fe64a33802ff32319c017f8918ce00bfc4bb05005fe24d82802ff122c14017fa995ca00bfc4c2e50077e9dd72802ff126b9401df9735ca00bfc48ae5005fea6562802ff130b14017f89358a00ff4b92c5005fe24562802ff532a94017f89854a00bf else 0xe5007fe66162803ff328b1401ff98458a00ffcaa2c5007fe64d62803ff306b1401ff88358a00ffcb9ac5007fe1cd62803ff2a6b1401ff94358a00ffd19ac5007fea6552803ff130a9401ff99754a00ffc4baa5007fe21d52803ff4eea9401ff99654a00ffcca2a5007fe5d152803ff2c8a9401ff99354a00ffc49aa5007fe20d52803ff2e6a9401ff87354a00ffcb1aa5007fe50d52803ff466a9401ff99154a00ffc48aa5007fe65d42803ff10ea1401ffa7750a00ffccb285007fe65542803ff2eaa1401ff96550a00ffcb9a85007fe58d42803ff2a6a1401ff99150a00ffccc265007fe65d32803ff30e99401ff8874ca00ffd3ba65007fe65932803ff30c99401ff9764ca00ffccaa65007fe61532803ff2ea99401ff9654ca00ffcc2265007fe5d132803ff2c899401ff9544ca00ffcc1a65007fe5cd32803ff2c699401ff9534ca00ffcc8a65007fe5cd81803ff0e6c0c01ffa3360600ffcb9303007fe58981803ff264c0c01ff99420600ffcc9903007fe20c81803ff2e640c01ff87320600ffca9903007fe50c81803ff46640c01ff97220600ffca9103007fe50881803ff26440c01ffa9950600ffc4c283007fe65d41803ff12ea0c01ff88750600ffd3ba83007fe65941803ff2eca0c01ff99550600ffcbaa83007fe59541803ff326a0c01ff89350600ffc41a83007fe5cd41803ff0e6a0c01ff96350600ffca9a83007fe8cd41803ff324a0c01ff97250600ffcb1283007fe54941803ff264a0c01ff88150600ffca8a83007fea6531803ff33098c01ff8984c600ffccba63007fe25d31803ff30e98c01ff8874c600ffd3ba63007fe65931803ff30c98c01ff9764c600ffccaa63007fe61531803ff2ea98c01ff9654c600ffcca263007fe61131803ff2e898c01ff9644c600ffcaa263007fe60d31803ff10698c01ff9734c600ffc39a63007fe58d31803ff2a698c01ff9434c600ffd19a63007fe64931803ff30498c01ff9724c600ffcb1263007fe54931803ff28498c01ff9324c600ffcc0a63007fe20531803ff2e298c01ff9514c600ffca0a63007fe66031803ff32e18c01ff9870c600ffc43863007fe9dc31803ff30c18c01ff9760c600ffcca863007fe61431803ff2ea18c01ff9650c600ffcc2063007fe5d031803ff2c818c01ff9540c600ffcc1863007fe5cc31803ff2c618c01ff9530c600ffcc1063007fe5c831803ff2a418c01ff9810c600ffcb8863007fe54431803ff28218c01ff9310c600ffccc243007fe65d21803ff30e90c01ff88748600ffd3ba43007fe61921803ff2ec90c01ff99548600ffcc2a43007fe5d521803ff2ca90c01ff99448600ffcc2243007fe5d121803ff2c890c01ff95448600ffcc9a43007fe60d21803ff10690c01ff97348600ffc39a43007fe58d21803ff2a690c01ff94348600ffd1)) else (if i < 5 then (if i < 4 then 0x7fe4c540803ff062a0401ff92150200ffd08a81007fea6530803ff32e98401ff8974c200ffc43a61007fe9dd30803ff32c98401ff9764c200ffccaa61007fe5d530803ff2ca98401ff9944c200ffcba261007fe59130803ff10698401ff9734c200ffc39a61007fe58d30803ff2a698401ff9434c200ffd19a61007fe64930803ff2e498401ff9624c200ffca9261007fe50930803ff26498401ff9914c200ffc48a61007fe20530803ff2e298401ff8714c200ffcb0a61007fe54530803ff28298401ff9314c200ffc18a61007fe48530803ff42298401ffa770c200ffcbb061007fe5cc30803ff2c618401ff9720c200ffcb1061007fe5c430803ff0e218401ff9610c200ffc98861007fe48430803ff42218401ff99748200ffc43a41007fe9dd20803ff32c90401ff97648200ffccaa41007fe5d520803ff2ca90401ff99448200ffcba241007fe59120803ff32690401ff88348200ffcb9a41007fe1cd20803ff2c690401ff95348200ffca1a41007fe8cd20803ff32290401ff88148200ffcb8a41007fe1c520803ff2c290401ff95148200ffca0a41007fe4c520803ff06290401ffa1148200ffd4ca21007fe65110803ff32688401ff89344200ffc41a21007fe5cd10803ff0e688401ff95344200ffca1a21007fe8cd10803ff32488401ff97244200ffcb1221007fe54910803ff28488401ff93244200ffc40a21007fe50510803ff26288401ff83144200ffc90a21007fe84510803ff2e608401ff87304200ffd19821007fe5c810803ff26408401ff93104200ffccb907007fe21c83803ff32c41c01ff99520e00ffcc8907007fea6573803ff330b9c01ff8985ce00ffcca2e7007fe61173803ff2a8b9c01ff9835ce00ffc41ae7007fe64973803ff322b9c01ff8915ce00ffccc0e7007fe61073803ff2a839c01ff9831ce00ffcb98e7007fe64473803ff532a9c01ff89854e00ffccbaa7007fe25d53803ff10ea9c01ff99654e00ffcca2a7007fe5d153803ff106a9c01ff97354e00ffc39aa7007fe64953803ff322a9c01ff89154e00ffccba87007fe21d43803ff32ca1c01ff99550e00ffcbaa87007fe5cd43803ff2a6a1c01ff99150e00ffc4c467007fe25e33803ff30f19c01ff8878ce00ffd3bc67007fe61633803ff2eb19c01ff9848ce00ffcba467007fe55233803ff30719c01ff9738ce00ffca9c67007fe24633803ff4eec1401ff97360a00ffc39b05007fe8cd82803ff532b9401ff9985ca00ffc4c2e5007fe61d72803ff10eb9401ffa775ca00ffccb2e5007fe61972803ff32ab9401ff9855ca00ffcbaae5007fe65172803ff308b9401ff9745ca00ffcaa2e5007fe64d72803ff126b9401ff9835ca00ffc41ae5007fe5cd72803ff0e6b9401ff9635ca00ffca9ae5007fe50d72803ff466b9401ff9915ca00ffc48a else 0x5ff64c818037f90640c017fd9220600dfe4c2a3005ffa6541802ff92ea0c01fbd7450600fdeb2283005ff24d41803f7a84a0c01ff99050600bff4ca63006ff66131802ff93098c01bfc984c600bfecba63005ff25d31802ffb2a98c017fd944c600fee41a63007f758d31803fd92498c01fdd324c600ffab8a63007fd50531803ff32098c01ff8904c600bff4c863006ff66031802ff93018c017fd970c600bfe4b863005ff65831802ffb2a18c01f7d950c600bfeca063005ff64831803fba6218c01ff5310c600bfec8063007fe64031802ffd3290c01bfd9848600bfe4c243005ff65d21802ff92e90c017fd9648600bfecaa43005ff65121802ffb2690c017fc9348600ff6b1243007fd4c521803ff32090c01ff89084600bff4ca61005ff65d30802ff92e984017fc914c200fee98a61007fe5c130802ffb2e904017fd9648200bfec9a41007fb5c920803fda4290401ff97048200ffcb0241007fe4c120802ffd32884017fd9344200bfe49a21005ff64910803ff26088401ff92044200dff3bb09006ff5d9848037fae6c2401bfc7361200dfeb1b09006ff8cd848037fae4c2401bfd6261200dfe99309006ff5c5848037f8e2c2401bfd6161200dfe98b09006ff0c5848037fa42c2401bfe1161200fdebb489007ef5ce44803f78e722401fbd6391200fdf19c89007ef5ca44803f7ac522401fbd3291200fdeb8c89007ef1c644803f7ac322401fbd3191200fde18c89007ef486448037fceec1c01bfd7660e00dfeb9b07006ff1cd838037fac6c1c01bfe3360e00dfeb9307006ff589838037fa64c1c01bfd7160e00dfe38b07006ff585838037fa62c1c01bfc3160e00dfe90b07006ff845838037fcee41c01bfd7620e00dfeba907006ff594838037fae241c01bfc7120e00dfeb0907006ff544838037fc2241c01bfd7020e00dfeb0107006ff440838037fceec1401bfd7660a00dfeb9b05006ff1cd828037fac6c1401bfe3360a00dfeb8b05006ff1c5828037fac2c1401bfd3160a00dfe18b05006ff84582803fd90f11401fee7788a00ff6bb445007fb5d622803fdacb11401fed7488a00ff6b2445007fb20e22803fdae711401fec7388a00ff6b1c45007fb54e22803fda8711401fee3388a00ff640c45007fb5c622803fd8e311401fed6188a00ff6a8c45007fb50622803fda6311401fec3188a00ff708c45007fb5c222803fdac111401fed3088a00ff688445006ff5cd818037f8e6c0c01bfe3360600dfeb9303006ff589818037fa64c0c01bfd3160600dfe18b03006ff485818037fc22c0c01bfd7320600dfe39903006ff54c818037fa8640c01bfe3320600dfe98103007fe9dd40803ff2eca0401ff97350200ffc39a81007fe58d40803ff466a0401ff97250200ffcb1281007fe4c940803ff2e2a0401ff87150200ffcb0a81) else (if i < 6 then 0xf64d52803ff926a9401ffd7354a00ffe39aa5007ff58d52803ffc66a9401ffd9154a00ffe48aa5007ff9dd42803ffae6a1401ffd6350a00ffecba65007ff21d32803ffb2c99401ffd764ca00ffecaa65007ff5d532803ffaca99401ffd744ca00ffeb2265007ff5cd32803ffac699401ffd534ca00ffec8a65007ff64132803ffae640c01ffc7320600fff19903007ff5c881803ffa6440c01ffe7750600ffebb283007ff5cd41803ff8e6a0c01ffd6350600fff19a83007ff5c941803ffac4a0c01ffd3250600ffe4ba63007ff21d31803ffcee98c01ffd764c600ffebaa63007ff59531803ffae898c01ffd644c600ffe41a63007ff5cd31803ff8e698c01ffd634c600ffea9a63007ff50d31803ffae498c01ffd624c600ffea9263007ff50931803ffa6498c01ffd970c600fff3b863007ff5d831803ffaea18c01ffd650c600ffeba063007ff59031803ffae618c01ffd630c600ffea9863007ff5c831803ffaa418c01ffd710c600ffe98863007ff21d21803ffcee90c01ffd7648600ffebaa43007ff59521803ffae890c01ffd6448600ffe41a43007ff5cd21803ff8e690c01ffd6348600ffea9a43007ff50d21803ffc6690c01ffd7384600ffe39c23007ff8ce11803ffae508c01ffd5284600ffea1423007ff4ca11803ffcee98401ffd764c200ffeb9a61007ff58d30803ffae498401ffd624c200ffe99261007ff5c530803ffac298401ffd314c200ffe90a61007ff9dd20803ffaec90401ffd7348200ffe39a41007ff58d20803ffc6690401ffd7344200ffe39a21007ff8cd10803ffae488401ffd6244200ffe99221005ff65c838037f90e41c017fd9620e00fbeca907005ff64883802ffb2241c017fe995ce00dfecc2e7005ff261738037f930b9c017fc915ce00ffcc82e7007fe24173802ffd3239c01bfd981ce00bfe4c0e7005ff65073803f7b2839c01fdd731ce00bfec90e7007fb64873802ffb2239c01ff5911ce00bfec80e7007fe64073802ffd32a9c01bfc9854e00bfe4baa7007f75cd53802ff922a9c01ff99054e00bff4ca87005ff65d43802ff92ea1c01fbd7450e00bfe48a87007fe64143803ff12119c017fe995ca00dfecc2e5005ff261728037f930b94017fc935ca00efeb9ae5005ff24572803ff320b9401ff8905ca00bff4cac5006ff66162802ff930b14017fc9358a00ff6b92c5005ff24562803ff320b14017fe9954a00dfe4c2a5005ff65d52802ff92ea94017fc9354a00fbea9aa5007fb5c952802ff922a9401ff99054a00bff4ca85005ff65d42802ff92ea14017fd9650a00bfe49a85007ef50d42803fdac4a14017fc9150a00ffcc8285005ffa65328037fb30994017fc984ca00bfecba65005ff25d32802ffb2c994017fd954ca00bfeca265007fb5c932803fda84994017fc914ca00ffcc826500 else 0x23ace3a8a3a733a4139fd39c2397e3955393538fa38ad387b3849381737ee37c5379c377c3765372a370a36cf36af368f367836613638361835f835b43594356b35423519350234d934c234ab34703447340c33ec33ba339a337a335a3343332c331532f532c332a33268322d31fb31d231973165312a311330f330c130a130813061304a301830012fd82faf2f7d2f5d2f2b2f022ed02eb92e902e702e592e392e222e0b2df42ddd2dc62daf2d742d4b2d192cf92cd92cc22cab2c8b2c592c152bf52bd52b912b712b512b312b112afa2ad12ab12a7f2a5f2a2d2a0d29ed29d629c829ba29912968293f292828ff28d628b6288d2876284d281227e927c0278e275c2733270a26f326b82698265d263d261425eb25c225a2258b25742539250724d524ac2483245a2431241a23e823b623842340230e22d322aa22782246221d21eb21c221a22167213e20f120bf2096207f2056202d1ffb1fc91fa01f891f601f371efc1ec11ea11e811e581e381e061def1dbd1d9d1d6b1d4b1d341d021ce21cb91c991c701c471c271bec1bde1b9a1b711b3f1b1f1aed1abb1a9b1a721a2e19f319c11998196f193d191d18eb18b91890185e183e181e17fe17d517be17a7177e17671735170c16ec16b11676164d161b15fb15c9158e155c1533150a14e114c114aa1478143d141d13fd13dd1390135e133e131e130712d512b512831263123111f611bb119211721152112010ee10bc109c1061104110060fb90f990f700f470f1e0ee30eba0e910e560e120df20dc90d970d6e0d3c0d0a0cd80ca60c6b0c300bf50b9f0b6d0b440af70ac50a8a0a610a2609e209b9097e093a091a08f108d1089f08760844081207f207c907a0078007450725070506ca068f065d0634060b05d005b00587055e0535050c04bf049f04760444042403e903ae037c03530333031c030502ee02c502a5027c0253022a020101e101a6016b013000fe00c30088003b0000ffec9aeb007ff64975803ffb22bac01ffd9359600ffec92cb007ff64565803ffb2e41c01ffd9620e00fff4cae7007ff26173803ffb28b9c01ffc835ce00ffec92e7007ff64573803ff922b9c01ffd905ce00ffeb98e7007ff64473803ffd32a9c01ffd9754e00ffe4baa7007ff65953803ffae6a9c01ffc7354e00ffec92a7007ff64553803ff922a9c01ffd7350e00ffe48c67007ffa6572803ff930b9401ffc875ca00ffecb2e5007ff65572803ffaeab9401ffd945ca00ffeba2e5007ff64d72803ff926b9401ffc835ca00ffeb9ae5007ff1cd72803ffac6b9401ffd535ca00ffea1ae5007ff64572803ff922b9401ffd905ca00ffeca2c5007ff64d62803ff906b1401ffd7358a00ffe39ac5007ff54d62803ffa86b1401ffd9058a00fff4caa5007ff65d52803ff92ea9401ffe7754a00ffecb2a5007f))) else (if i < 11 then (if i < 9 then (if i < 8 then 0xc7471742d73d77393734672e77291724d721271d7719371587114710670e670c670a6707d705d703d702f70186ff86fd86faf6f8f6f6f6f616f416f216f016ed86eaf6e8f6e6f6e4f6e2f6e186df86de16da66d6b6d306cda6c9f6c5b6c176bf76bc56b9c6b616b386afd6ac26a7e6a436a236a0c69f569de69c769a76990697969626942692b691468f468dd68c668a66886686f685868416821680167e167d367bc67a5678e67806772675b673b671b66f266db66c466a46684666466446636661f65ff65df65c865b1659165686548653a652c650364ec64cc64ac648c647e6470646264546446642f6418640a63f363e563c563ae63a06380636963526344632d631662ff62e862d162b162a3628c6275625e62476230620761f061e261c261ab6194617d6166614f6138611860f860e160c160b3609c608e606e606060496032601b60045fe45fd65fbf5fa85f915f7a5f5a5f4c5f2c5f155efe5ee75ec75eb95eab5e945e7d5e665e585e4a5e335e135df35de55dce5db75da05d805d725d5b5d3b5d2d5d1f5d085cf15cda5ccc5cb55c955c875c795c625c4b5c345c265c185c0a5bea5bd35bbc5ba55b975b805b695b525b445b2d5b0d5aff5ae85ad15aba5a9a5a7a5a5a5a3a5a1a5a0359e359c359b559955975595e594759305919590258e258cb58b45894587d585d5846582f581857f857d857c157aa5781576a575c5745572e571756f756e956db56cd56b65696567f5668565a5643562c561555fe55e755d055b955a2558b5574554b552b551d550f54f854e154c154aa549c548e54805472545b544454365416540853f153d153c353ac5395537e535e534753395322530b52f452dd52c652af52a1528a526a52535233521c520551ee51d751c051a95192517b5164514d5136511f50ff50df50bf50a850915071505a5043502c501550074ff04fd94fc24fa24f8b4f744f544f344f1d4f064eef4ecf4ec14eaa4e9c4e854e654e4e4e374e294e124dfb4de44dcd4db64d9f4d7f4d5f4d514d314d1a4d034cec4cde4cbe4cb04ca24c824c624c544c344c264c064be64bc64ba64b8f4b6f4b4f4b384b184af84ad84ab84aa14a8a4a6a4a4a4a334a1c4a0549dc49b349934973495c4945492e4917490048e948c948b2489b487b48524829481b480447e447cd47ad4796477f476847484731471a470346ec46d546be46b046a2468b467d4666464f4638462a4613460545ee45d745c945b2459b45844564454d4536451f450844f144da44c344ac4495447e4467445044394422440b43f443d443bd43a64386436f434f432f430f42ef42d842c142a1428a42734253423c421c41fc41dc41bc41a541854165413c411c410e40ee40ce409c407340143fd03f8c3f363ee03e933e193dc33d763d4d3d243cce3c8a3c463be73bac3b5f3b1 else 0x909d48501a4c81c01a4681c01a4681c039290586d1b00e4a426c9cd1360136692c520a81c0160d24c0368b0692391b4d164280d26e0280d23a039190a0250380a034928180501a4940c0280d24a0603c9dae8f214069460140691d01c8c8501281803328190540e00d23a0600ccda49320d40c019936d1641a818033281905e0792021820949c2019a440234880469100b81e48096087827080780e01ecb04c0700f6582603807b2c1301c02c1a49e4e4080740c0347c8a02c198180f276ba3483601c948ed744d26c036bc948501700d1a4791405833030148f2768b066050301c0f276ba3c8450300c8ed744d26bae8bac8baa8ba88ba71ba51ba31ba1ab9f1b9e3b9ccb9acb995b975b955b935b915b8f5b8ccb8b5b895b87eb85eb83eb827b810b7f0b7c7b7a7b77eb767b750b739b722b6f9b6e2b6b9b6a2b682b662b639b619b5f9b5e2b5b9b599b579b550b539b522b50bb4e2b4b9b487b455b435b40cb3ecb3ccb3acb38cb36cb34cb32cb30cb2ecb2ccb2acb28cb263b23ab208b1f1b1dab1c3b191b17ab151b11fb0edb0bbb092b060b037b020b009afe9afc9afa9af80af60af37af05aed3aea1ae6fae3dae0badd0ad9ead7ead5ead3ead0cace3acb1ac7fac4dac2dac04abdbaba0ab6eab45ab1caae1aac1aa98aa78aa61aa41aa21aa01a9d8a9b8a998a978a94fa92fa90fa8e6a8c6a8a6a886a866a834a80ba7d9a7b9a799a779a750a730a707a6d5a6aca68ca66ca64ca62ca60ca5eca5cca5aca583a55aa531a4ffa4d6a4a4a484a449a420a3f7a3c5a39ca373a34aa321a2f8a2cfa2a6a27da254a22ba202a1d9a19ea16ca116a0f6a0a9a089a0219fdd9fbd9f949f599f399f229ed59e9a9e719e369e049dff9db29d899d4e9d1c9cfc9cca9c749c4b9bfe9bc39b889b7a9b369b049ab79a8e9a5c9a4e9a4099c6998b9974994b990798ba987f9868985a980d97e497c49792974e971396fc969d9686963095e3959f9552952094ee94e094ae9458941493c79371933692e0929c928e92419218920191ab9167910890bb9080904e90138fe18fca8f7d8f4b8f108ef08ec78e958e638e288ded8dbb8dad8d608d1c8d058cdc8c988c4b8c108bd58bac8b7a8b368afb8ad28a978a778a608a2e8a0589e5898f895d891988de88b5888c883f8831882c880c87fe87ba87918771872d86f286b78673863885fd85b08575853a852c851e84f584cc84888456842d841683e483a0836e832a82f882d882c18298826f823d820281e281d481a28155810880cd8092803c7fdd7f877f1f7edb7e8e7e537e0f7dc27d877d437d117cf17cda7cba7c9a7c717c517c317c117bf17bd17bb17b887b687b487afb7aae7a737a417a0679cb7999793a790878bb78807845780177cf77947759771576da769f7652760e75dc758f755d751074d574a) else (if i < 10 then 0x198b05c010cf6582501c8c850138058150300e435a6cb0640e00b0340e01c85a6d160c81c0160780219ecb04c0190f658200701c0349290123d8c36581080d2260600982034d20c482d158d3482e02247b24520b8000920b04c0130914820070048349300742b1a49c03488038024158d25c01acd264b217004832004d25c01ac995a101a690735932906610140380ad158cd48360037483d90038024568b0580e009848a417006b2d568801c0122b4692e00867b2c1090202c0f01512606ccd483007007b2c13006b7254498430dd2106b26520cc202921365804929020160090122c109081c016098032146a2e42807004833160b80219ecb04e0160580a419840400e00f6582600d6e421882906c01adb412a4198c01c0160701c0160780e01ac9c428e00b0300e0090662c143658170202742b1a4a782708066b247004069280780691880d22c01e09c20a894f04e100f0012a89ec878270807803590c244c010cc8e426002458192203802196190610058001c0700867b2c1cd7c034880980e019090202807007b1e00f0da09120a01c0120f6d1280487c01e00866472118180b252236432c1c1380ed1a4b0c83123004327320b80e01ac984c0130a2d12600d65a2b1a4bc02b1a4780e006cac692e0002742b1a4a01c0190d24c01acd2206d170056348f00122c0e03802c0c03802c1a4980348b00581600e856349380691600986410520a01c01d0d2400e00d23c01adb4252b520c01c0344987ba41b0078a4080801c0120ac69299300691e00986924520a6b26204d3c0101b00d1261d0d25c01ac4069200701c02c1300742b1a494034a807c0348b009b289a5a25a0601904c501a4c81c01a4681c01a46e42c08078072793909b90162a28c054536e42c15c858100cb0e4100c40581601c89ba8960b80091607806454440e42b9190201e01c8da89160b807215aa220641b0056a8b9040c83390acc8101103802c0dc858100f01517226cb05c0390b151101701514d961c8572160403c0391909ba8960c81c01607807215aa220641b00e4f272137202c5450e44d9606e4e026cb04a0321c8a02501c8c85012818068a6c9ce43601c8da2c1280e46428084ca060190a072189940c0391b492641d03802c0f00da721609c0c039136582d01c8c8501281c072139405a0601c89b2c1681807226cb05a0601365872168081c0390b0da350300e44d939a262650300e450320d40c0393c9dae8f2136584b909d4834a80a4ea4280d24c0793b5d127280d34843909d4834a80b8027521c8a034989d4834a8098027521b4a0349903806d1a69058721c9d4834a809802752136d1349b00d1275213669721c9140500c9c69a42809c040960780275214069292103802c13014834a81c85c052124696d1503802c0f00da3496084e34d21404e0204d23c03 else 0x8620090f80321e00443c0080256110f00221e00443c0089c1c007004c160020127088780110f002e00700e41600380218b00c811a43803488126911a780234e00d63009a4469c00b00da1024d2234e005803d8b00d11024d2234e00469c00841801600d22049a444ce008d380113300234e00c8334e00456c00b004c348c0269152300691d2300691d2300691d2300691a048624090c420c010c78021890269170098431e0086226600863c01688632b600863c013086321a045806410c7802d10c78064160864c01388632184a380218c9980348c1de42707a24535f00d220279007c01928076180f0c02aa1a8ec30222c1ec2e71ae8076182c1ec2e71a8a02e3b0c680b07b05a4861e008ec30a02c1ec2a915833c829030d83e20405fc8330080c3dc01d860b0a018855a1a0b7903c2950520621548ac19e41301a901f1020f04ee00809e4e40802641583381e414880202105a42816149a43c58051f806b260300620349c560c40f004069148a0420a50ac6a22f27223660502045e405c6cb009400f802d1df9236360c20071b1d8e9c82a0c1c57e4130d83c0e101c371817903c3607080be400f0076280f060e1000f003c280c185603170940c0e101d194814a80808a42ec6ab722310748501bb5d134aee3029725210ab465214ca02ad21d29a4280aab465214ca02c3a5348501157485328090c644e2404098a4403104a442be0082403314982629100c560c0101452203300c9201b009120184c4020d960580e01a4404c0004f6335830403c01e2a2e486480d27359a4403a41ee18202058d6691013c9c886080816100ac9488608080c10082c201592a31b00830b06243201c20213aa2c890038d26c0004d2306603804300949869100cc820128d8064900e3658106cb02274804782708078026520cc202804127b18a5c8742b1a69063c390cd2084520c6b26520cc2029ee11481010306b26520cc203590ad08a4080a4e35838cc20a4181258102040091804d64804024a48040806480c080780009a462004880248149a4125101a44133c138404b216206202603807824080b800096066914959907b2921902910109cc834c805250988040101c80d24359a4403101a444834c807203488247b106cb02101a44123d8840691700b501219ecb06e006ccc5821acc86910390a6b348807c0809606202c083658100780581807c9c03d960ac0c0700986b101a4fc034880601c01a47803212086203d960e0c3d9607c03d960780091607802c1ec7803d880380241609802c1ec601c0700f6582e00f6581e00d66910568a6b348807800d9ec64c49084011007006b2d5689800dd68d24c010cf6582080b02c006ea2692007007b2c10d669100f006b091588202c0803803316086b262078069101b005a33160801c0700f64c039086742c17006b6d)) else (if i < 13 then (if i < 12 then 0x4041210070151180701511b93015132101820105824200d4418368b201c300e02a23c0544d231004b012103990581e01a2c81e000220910c5807254464300e02a2433602a23100424100d45900c2602a2234e02a23c0544863358060231287001c004121048700251007002128700c8102424300c046da0488121c01ac12314824409c00812104e004090d883009102424204e0040e688246090e00122c002458004883609160012204e02904c20a412204841380720f0009102700204e00409c00b00091600122c002486321e000230984858068b207800f00982c0049801c00c3612b60058026099029160090234807003c0070058113b0020100441309080380640f001640a49030080c401c00b00011130030118242090e01902e013044ce009c816d07804c1600986b1f01c8c81f00380688b8012160040200f01903e00700c81601c8c81e0024c0804ac2c0080401270b001c01305802616861b0e003800d88d7c01601c821007001e007005aad0c37801601902c03205800e00ac22b7005802b084012b600551c01586200e00b02409305802609c84c408cd7c0260f006b260cb481260f0074260c98921600a24c193040a0193826bc013065ac0130780260a026b10078020093844c808b0048358f80e4170090272520903e0120448c01ac780720890091601b42e0120363a4600e83c0344448048a918028920980100b001c0120448048b804c160091481e003800e00256c00b0048260f00e41600902348700d111a412210600580348812691133802c01a444cc00b00691600d22c0520d24c2600905a186c3800e00b4235f00580241ac7807208401c007001c00700481133802c004981bc00f0012b6005802d1307800e00902c0160458e008b180358f00581080258c008b18011630022c600458c00b0058113838027089ce4048c9dc01600d64e1e009c22702444ec00b004e11381222760044ec008b012113b002276005801008024e1523004e1d23004e1d23004e1e009c200f0044ce00047012608900911a4122270244d10f00d2221f00443e0088601e00c87c0110f80221f0098321f0090321f005c02c0887c0160086511848380720b00135f00580289ac7807208f1801080274c00b007b1601902c014444c090b0051113025801e00c8511880380a8930780640b004811a7002c0049d80288c24110070043260f80c8048f801c0391903c00780e4048cd7c0a40f0148358f00e4640f800911e301481e01b4c81f001223a602903c0520f63c0345903e0144123c0520580a40b0148100f80c8048f81481602902c05204e4c0520c84c0520b4da2601a258190f004e1e01902e0024580240b00691600902c01604c8c01387c0048b80691601c9481b6b01482d11a380a41448430e00862e0004cc321f00443c01ac601330887801600 else 0x664264216918100a0e0111460f63b051802298c2ecd20b31ac99085a460242839af344c0d860506358bb3418100a0c2dd2668ac6904860148320a576690c0a0c4818e6a90181418521018499010b85482034c0442400e200e393d8ec2e73480c021e0b9418010302c8200a88c85a2b4043c5149adc84c0e0242a707144f7010a9556170702c5320049c100a00818165a4368123a4024548100242a421c04040a2144907805884a2d1380640160518520a108c241640040c091094570c094484e58948d50382b43814281c8824081402a4c3010480c01038e020581a986b2b063901428148824091acadc80c2c07641290485d4e46d158280b180a640094cadc8568602c6a14140a64009583a701205840b1203b90ad0ca88a0403b05a00203138d42a0a30044d0ca88ec4e0b38d656c806480502005a0020313c6c2a0a3004532b9003814283c0406070a828b405c204740408a808c090e80a4408d185640c489404420474054a04740472047407220474041848740532047400b321024a020d023a02a5023808ae102719ca4123541300a281c0c45220902206270706c7619301cb018948d4b1a0e8b852250c9a350893130621730041629900c4b2b263200a0b140c44029902a344e1482466572444990814080760b40044f1b148cc14600cae40291382cce46d46812291982cf2b138a6400a280453340c02850695c22361314028c2b060e85d0e1b0c8ee40300431181b1818e487040403630a8182d1b39020208c21c83a0389431181b1c062a0f0c02a5178b5c801038783118403054368c078a2d720aa1c030f0382a87236a1c0e1b054d0e0d8942a416b921c0607084d018185e2c38348d4e3827432900a140e44120481e9126169a441203806360ca401e063b0ba06b2b72032900a14098412050d5c9010640c3b3b0485d2e4a406e2c342c0a0e018dc30d23b0a1802268b0ec4e0b30d691341005812283806360c34cec28695c30071b008a0287048680ab408e80b8408e80b4408e80da5da0494068a04740522046090d01022a0230123a0291023a0039b48125012c811a31024e18243407220474041a04740532047404d0a5024a0244528125001c811d0106811a0d02691aadb4091a901224634412341824524021a460209018031b84010761734046b3b071a42e6723682e290a02c612004a6570c008a4d32030d6706605838412038d4173410024302839a43c1718066818348a0a4302054144160081a2014ca4c03010e42041c8d81a29104a4c39068a652200998722f930981820081c72d106ca4522131ac2512184b002096005800908258011302512184b0020960044ec0082580720c8780104b00209601903c0048412c00b0012218c9980008f0020100700235848580a89ac78072344678c054462009d04023d8804160908241090) else (if i < 14 then 0xa8081e5240b8400e3050945228202a032903838b290385c3040b8401438081c0c38081c0c303818203030a41638082c3c38082c2a3218401638600a241724302e028910040c00c4880206292a2252c481c1701102f0ca8808125078381230bc32a22503818d0c0bc480c4064480c092432a21703818a02840d412404c200425242202020492110105808901010a4124014202e09240e0205011206070b808802818142e40280852092016060901100b03010249e4039a460209018183a0d8c02a535f20400a1d0a1c92012a49d010a8c61e40846c16182c025001030a06c02669044363c02c5a060c88168841a044e3b0d864e064088460d010c8604019983a010a828d806d344601c008c8480f82872781005d04e038d1527b0b98f04e4d8548011c15830220b98f039270606a506040e100102476182c20207b1d85c816008ecac7b05989c103d8ec2e50605c2a3271ec203b0b94d7a48601eb431348824090607c403620ac0f201c9ee301b1aa06da4ad1686320300ccd5a0d85414610045da42b00430220b9d710e330244450096310071c9ec761742e2021811100203348782e50b04181116449831a44200f291b1ec601504b7c8180a0a4123632483c2040b00430201c21489d838121738c016481b4a46218a42006660e8242a0a3601b420484046b264ee3029101a508c501a474434a6c2a304cec52690b947428322d03164149c0648129a43c1431a452235cd0990e8401ccd29104814200f89564c874200e669484a409159e240078c4a4363545200f34074a412173d20620b2407e520e1021560e2d0a6405019981215051700100ca430581115564c21d22a21894894449009e00f290c1606a735ae0990e21804522240b490070903a53202c05d23194960120e1118a2b80a0a2a218720a6409019983a58048541470c045d9a3c01a521b0c1610bb081386644d854422a40d851291801832204804f00794860b03539ad4822a401c5c18030a840a358b80e1f334a424a040045c1894960446270a46c310c14a23314860b0a0300cd2090f050ad10708d62e0812240281002d003178a8202128042120641a45060d8a81630084c2a0b2004267b0a850aab0b406522229917016140a4446064809c120a850c18058245222284c22ecd08886288b004168f226bb429048cc1670102c40c14040164321216916140801673c08b22071c00420354144f1165d824166358b8302804888c280081816452191761814145d9ad00243028059c5da4cd120300b32d22c280590a233500a02c0b3601a2c81e001223c1303615051536660a8288660508463a2608830281b0e412154804067b0a828a22132ecd2181289ce9a6d280361e0e9806660a82881300854444008c3499a34860b00a400c20018142a30187350834c600228051d6896348a080710828 else 0xb0682440b0683720b06833d8a8763150ec4811d8a0601808087017208986b068b4881083464200809023068c04e464034681028b462d01280681808b46070b84064c2d0343e4068d851b0d87c6a40688b51b1b0d02170f8c1a1f13201a2408143e3a89441a3220141a171920d62c181290811026902840b05084d8a109b0d8d0908490857084904882c18082e09180d02300b8e9048160c0881808c0701520c46361888ac31110608e4840b0605048c06300142136414a4842915080409120603293491028c9485c86980ca41c09288a52174b024a81348a471b241683e440c6e1038d86c3e3840d412340c6e10340c6c3e30b8243e340c061034085c3e340c045232d05c3e34081e103028243e32c2046b182088b1010c90445880a90325068c040204881c0d113902b880c38a0d0f89030e1aad084e40c061cbb28889c81870cca4e40c3948222d20900d18129048072901a5a41201a1f20342020724850103808701038086010105c6c80102c124808081630ac446a14240622260a888a070ac0622142c04451103854b11128982a282856031111050b110a82452222c044511140a428680c44521505945c07080c1206038c0f48170cf0b880d20505a401c6ab421ee90255d8a0a220b52066072c054816a40a0a0240824607065201a480d200e10201d480ca41901a603968194806940e0d0b16080e240c4164348a4160e048a0c090702c6580486016405840123408b44061a8b4701030a870117878701818784e4178544431505444340c045a34081a022624042e1f1c040a301a0603030f1202271c8e020a080c0207030c1435948c14b88081c525038d5692920297625140a4a0a114a460a110a46010301c60)))) else 0
def signed10Level : Packing := (1260,3,6,0,0,16,0,signed10Data)
def signed9Data (i : Nat) : Nat := if i < 33 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x3384600ff45ca3384600ff458a3384600ff454a3384600ff450a3384600ff82622284600ff825e2284600ff861e2284600ff821e2284600ff89de2284600ff861a2284600ff85da2284600ff86162284600ff85d62284600ff85962284600ff86122284600ff85d22284600ff85922284600ff85522284600ff824e2284600ff860e2284600ff820e2284600ff85ce2284600ff81ce2284600ff858e2284600ff854e2284600ff850e2284600ff88ce22846008ef690988ce008ef690985ca009fa688974c2009ee2a6444c2009de694914c2009fc28596482009be698934820097e69c91482009be69891482009de69491482009ee69091482009f668c91482009de69493612009ee6909760e008fe2a2991ce009fc286991ce009ee690981ce009fa688981ce009fc684981ce00cee661941ce00dce655941ce00cfa661921ce00dba659921ce00dda655921ce00dea651921ce00cfc661911ce00dec651911ce00df8649911ce009be6989754e009ee6909754e009fa6889754e009fc6849754e009de2a58554e009ee2a57450e009ee690988ce009de6949360a009ee690985ca009be698935ca009de694935ca009ee690935ca009fc684935ca009ee690915ca009ee6909158a009f668c9158a009f628d9750a0097e69c9350a009be6989350a009de6949350a009fc6849350a009fa2a5724ca009de694914ca009de69493606008fe2a195506009ee2a574506009de69493506009fa68a994c6009ee690974c6009fc2a5714c6009de694980c6009ee690970c6009fa688970c6009de6949348600be6690988ce009fa2a58388a009fa2a53188a00bf428d98846008dfaa99520e00c5f9dd9520e00c9f9999520e00cdd8459520e009beaa9960c200db68cd960c200dba889960c200dae9999404200dea88994042009f6aa99304200db69999304200df28899304200df484593042009faaa99204200dba9999204200df884592042009deaa99520e00d5e9dd9520e00d9e9999520e00dce9119520e00dd68cd9520e00dda8899520e00ddc8459520e00cf68cd981ce00cfa889981ce00cfc845981ce009eeaa9941ce00d6e9dd941ce00dae999941ce00dce955941ce00d6e5cd941ce00de68cd941ce00dea889941ce009faaa9921ce00d7a9dd921ce00dba999921ce00dda955921ce00dea911921ce00d7a5cd921ce00df28cd921ce00df8845921ce009fcaa9911ce00dec911911ce00df48cd911ce00df8889911ce009deaa9950c600d5e9dd950c600d9e999950c600dce911950c600dd68cd950c600dda889950c600ddc845950c600f5a9de5588a00faa99a4488a00fca9564488a00fb299a3388a00fd29563388a00fe29123388a00f749de3384600f789de2284600fb899a2284600fd89562284600fe89122284600ff08ce2284600 else 0xdfc5cd911ce00dfc54d911ce00dfc689911ce00dfc609911ce00dfc5c9911ce00dfc589911ce00dfc549911ce00ddeaa9950c600dde6a1950c600dde2a1950c600dde69d950c600dde29d950c600dde61d950c600dde21d950c600dde9dd950c600dde699950c600dde619950c600dde5d9950c600dde691950c600dde611950c600dde5d1950c600dde591950c600dde68d950c600dde60d950c600dde5cd950c600dde58d950c600dde689950c600dde609950c600dde5c9950c600dde685950c600dde605950c600dde5c5950c600dde505950c600dde4c5950c600fce5ce5591200fce1ce5591200fce8ce5591200fce5ca5591200fce58a5591200fce4ca5591200fce4c65591200fce0c65591200fce4865591200fce8465591200fe6262448ce00fe658a448ce00fe654a448ce00fe6246448ce00fe6206448ce00fe65c6448ce00fe61c6448ce00fe6586448ce00fe6546448ce00fe6486448ce00fe6846448ce00f7a6a27788a00f7a2a27788a00f7a6167788a00f7a6927788a00f7a6127788a00f7a5927788a00f7a5527788a00f7a6867788a00f7a2867788a00f7a6067788a00f7a2067788a00f7a5867788a00f7a5467788a00f7a5067788a00f7a4c67788a00f7a0c67788a00f7a8467788a00fba6126688a00fba5526688a00fba60e6688a00fba20e6688a00fba5ce6688a00fba1ce6688a00fba54e6688a00fba50e6688a00fba8ce6688a00fba6066688a00fba5066688a00fba4c66688a00fda21e5588a00fda9de5588a00fda5da5588a00fda5d25588a00fda5925588a00fda20e5588a00fda5ce5588a00fda1ce5588a00fda58e5588a00fda50e5588a00fda8ce5588a00fda2065588a00fda5c65588a00fda1c65588a00fda5865588a00fda5065588a00fda4c65588a00fda0c65588a00fda8465588a00fea21e4488a00fea9de4488a00fea5da4488a00fea5d64488a00fea5964488a00fea5ce4488a00fea58e4488a00fea54e4488a00fea2064488a00fea5c64488a00fea1c64488a00fea5864488a00fea5464488a00fea4c64488a00fea8464488a00ff22a23388a00ff229e3388a00ff261e3388a00ff221e3388a00ff29de3388a00ff261a3388a00ff25da3388a00ff26163388a00ff25d63388a00ff25963388a00ff26123388a00ff25d23388a00ff25923388a00ff25523388a00ff22863388a00ff26063388a00ff22063388a00ff25c63388a00ff21c63388a00ff25863388a00ff25463388a00ff25063388a00ff28463388a00ff46a23384600ff42a23384600ff46623384600ff42623384600ff469e3384600ff429e3384600ff461e3384600ff421e3384600ff49de3384600ff46963384600ff46563384600ff46163384600ff45d63384600ff45963384600ff468a3384600ff464a3384600ff460a) else (if i < 3 then 0x53284600bfc2a13284600bfc69d3284600bfc29d3284600bfc6993284600bfc6953284600bfc6913284600ff424d3284600ff48cd3284600ff85c93284600ff85093284600cdfaa99520e00cdf69d9520e00cdf29d9520e00cdf9dd9520e00cdf6999520e00cdf5d99520e00cdf6859520e00cdf2859520e00cdf5c59520e00cdf1c59520e00cdf5859520e00cdf8459520e00cdf6819520e00cdf5c19520e00cdf5819520e00cdf4419520e00dbe69d960c200dbe9dd960c200dbe68d960c200dbe5cd960c200dbe689960c200dbe5c9960c200dbe685960c200dbe5c5960c200dbe1c5960c200dbe4c5960c200dbe485960c200dbe845960c200dee9dd9404200dee5d99404200dee5cd9404200dee1cd9404200dee58d9404200dee8cd9404200dee5c99404200dee4c99404200dee5c59404200dee4c59404200df6aa99304200df669d9304200df629d9304200df69dd9304200df66999304200df65d99304200df66899304200df65c99304200df66859304200df65c59304200dfa69d9204200dfa9dd9204200dfa5d99204200dfa68d9204200dfa5cd9204200dfa1cd9204200dfa58d9204200dfa8cd9204200dfa5c59204200dfa4c59204200ddeaa99520e00dde2a19520e00dde69d9520e00dde29d9520e00dde21d9520e00dde9dd9520e00dde6999520e00dde5d99520e00dde6919520e00dde5d19520e00dde5919520e00dde68d9520e00dde5cd9520e00dde58d9520e00dde6899520e00dde5c99520e00dde5899520e00dde6859520e00dde2859520e00dde2059520e00dde5c59520e00dde1c59520e00dde5859520e00dde5059520e00dde4c59520e00dde4859520e00dde8459520e00cfe5cd981ce00cfe5c9981ce00cfe589981ce00cfe4c5981ce00cfe485981ce00cfe845981ce00dee6a1941ce00dee69d941ce00dee61d941ce00dee699941ce00dee619941ce00dee695941ce00dee615941ce00dee60d941ce00dee5cd941ce00dee58d941ce00dee54d941ce00dee609941ce00dee5c9941ce00dee589941ce00dee549941ce00dee685941ce00dee605941ce00dee205941ce00dee5c5941ce00dee585941ce00dee545941ce00dee4c5941ce00dee485941ce00dee845941ce00dfa6a1921ce00dfa69d921ce00dfa61d921ce00dfa699921ce00dfa619921ce00dfa695921ce00dfa615921ce00dfa611921ce00dfa5d1921ce00dfa591921ce00dfa551921ce00dfa60d921ce00dfa5cd921ce00dfa58d921ce00dfa54d921ce00dfa685921ce00dfa605921ce00dfa205921ce00dfa5c5921ce00dfa585921ce00dfa545921ce00dfa505921ce00dfa4c5921ce00dfa845921ce00dfcaa9911ce00dfc6a1911ce00dfc2a1911ce00dfc691911ce00dfc611911ce00dfc551911ce00dfc68d911ce00dfc60d911ce0 else 0xbfa6848388a00bfaaa97388a00bfa2a17388a00f7a9dd7388a00f7a5d17388a00f7a9dc7388a00bfa6987388a00bfa6947388a00ff25cc7388a00bfa6847388a00bfaaa96388a00bfa2a16388a00bfa69d6388a00bfa29d6388a00fba5d96388a00fba5916388a00ff25cd6388a00bfaaa95388a00bfa2a15388a00bfa69d5388a00bfa29d5388a00bfa6995388a00fda6155388a00fda5d55388a00fda5515388a00ff220d5388a00ff25cd5388a00bfa69d4388a00bfa6994388a00bfa6954388a00fea5d14388a00bfa2a23388a00bfa29e3388a00ff260e3388a00ff25ce3388a00ff258e3388a00ff254e3388a00bfa29d8188a00bfa69c8188a00bfa6948188a00bfa6908188a00bfa68c8188a00bfaaa97188a00bfa2a17188a00f7a21d7188a00f7a9dd7188a00fba2997188a00f7a5d97188a00f7a9dc7188a00bfa6947188a00bfa6907188a00bfa68c7188a00ff85c47188a00bfa69d6188a00ff85c56188a00bfaaa95188a00bfa2a15188a00bfa69d5188a00bfa29d5188a00bfa6995188a00fda5955188a00fda54d5188a00ff82055188a00ff85c55188a00bfaaa94188a00bfa2a14188a00bfa69d4188a00bfa29d4188a00bfa6994188a00bfa6954188a00fea5d14188a00fea5914188a00ff82054188a00bfaaa93188a00dfa2a53188a00bfa2a13188a00bfa69d3188a00bfa29d3188a00bfa6993188a00bfa6953188a00bfa6913188a00ff220d3188a00ff258d3188a00ff28cd3188a00ff85c53188a00ff85053188a00bfa69c3188a00bfa6943188a00bfa2a21188a00bfa29e1188a00ff86061188a00ff85c61188a00ff85461188a00ff85061188a00ff84c61188a00bfc28d9884600bfcaa89884600bfc68c9884600bfc6889884600bfc2a58384600bfc29d8384600bfcaa88384600bfc2a48384600bfc69c8384600bfc6988384600bfc6948384600fdc6948384600bfc6908384600ff424c8384600efc60c8384600bfc6888384600bfcaa97384600bfc2a17384600bfcaa87384600efc6a07384600bfc2a07384600ff45cc7384600bfc6887384600ff86887384600bfc2a23384600bfc69e3384600bfc29e3384600bfc6963384600ff460e3384600ff420e3384600ff45ce3384600ff41ce3384600bfc68a3384600bfc2a19284600bfc29d9284600bfc28d9284600bfc2a58284600efc2618284600bfc29d8284600bfc28d8284600bfcaa97284600bfc2a57284600bfc2a17284600f7c25d7284600f7c9dd7284600bfc28d7284600f7c5cd7284600ff86497284600ff85c96284600bfcaa95284600bfc2a15284600bfc28d5284600ff85c95284600bfcaa94284600bfc2a14284600bfc69d4284600bfc29d4284600bfc6954284600bfc28d4284600ff86494284600ff85894284600bfcaa93284600bfc2a)) else (if i < 6 then (if i < 5 then 0x9d828ce00bf6285828ce00bf6aa9628ce00bf62a5628ce00bf62a1628ce00bf629d628ce00fb6595628ce00ff2649628ce00bf6285628ce00bf6aa9528ce00bf62a1528ce00bf6699528ce00bf6285528ce00bf6699428ce00bf6695428ce00fe6611428ce00fe6551428ce00ff2589428ce00bf62a1918ce00df6261918ce00bf629d918ce00bf6aa8918ce00bf669c918ce00bf6698918ce00bf6694918ce00bf6690918ce00fe6690918ce00bf6688918ce00df6644918ce00bf62a5818ce00bf629d818ce00bf6aa8818ce00bf62a4818ce00bf669c818ce00bf6698818ce00bf6694818ce00bf6690818ce00bf6688818ce00ef6604818ce00bf6aa9718ce00bf62a1718ce00fb6299718ce00ff4245718ce00bf6aa8718ce00bf62a0718ce00bf6698718ce00bf6690718ce00fe6690718ce00bf6688718ce00ff45c4718ce00bf6aa9618ce00bf62a5618ce00bf62a1618ce00bf669d618ce00bf629d618ce00fb6589618ce00ff45c5618ce00bf6aa9518ce00bf62a5518ce00bf62a1518ce00bf629d518ce00bf6699518ce00fd6595518ce00fd6549518ce00ff4205518ce00ff45c5518ce00bf6aa9418ce00bf62a5418ce00bf62a1418ce00bf669d418ce00bf629d418ce00bf6699418ce00bf6695418ce00fe6651418ce00fe65d1418ce00fe6591418ce00fe6509418ce00ff4245418ce00ff4205418ce00bf6aa9218ce00bf62a5218ce00bf62a1218ce00bf669d218ce00bf629d218ce00bf6699218ce00bf6695218ce00bf6691218ce00ff2589218ce00ff4245218ce00bf62a6118ce00bf62a2118ce00bf669e118ce00bf629e118ce00bf669a118ce00bf6696118ce00bf6692118ce00bf668a118ce00ff4646118ce00ff4246118ce00ff4606118ce00ff4206118ce00ff45c6118ce00ff41c6118ce00ff4586118ce00ff4546118ce00ff4506118ce00ff4486118ce00bfaaa88788a00efa61c8788a00bfa6988788a00bfa6948788a00bfa6908788a00fea6908788a00bfa68c8788a00bfa6848788a00bfa2a27788a00f7a61e7788a00f7a21e7788a00bfa69a7788a00bfa6967788a00bfa6927788a00bfa68e7788a00bfa6867788a00bfa29d8688a00bfaaa97688a00bfa2a17688a00f7a9dd7688a00bfa29d8588a00bfaaa97588a00bfa2a17588a00f7a21d7588a00f7a9dd7588a00bfaaa96588a00bfa2a16588a00bfa69d6588a00bfa29d6588a00fba5d96588a00fda6156588a00fda5d56588a00bfa29d8488a00bfaaa97488a00bfa2a17488a00f7a21d7488a00f7a9dd7488a00fea6117488a00bfaaa96488a00bfa2a16488a00bfa69d6488a00bfa29d6488a00fea5d16488a00bfa69d5488a00bfa6995488a00fda5955488a00fea5d15488a00bfa29d8388a00bfa69c8388a00bfa6988388a00bfa6948388a else 0x200fae5d96591200fce5d56591200bee2856591200bee69c8391200bee6988391200bee6848391200beeaa97391200bee2a17391200f6e9dd7391200bee2857391200f6e9dc7391200bee6987391200bee6947391200fe65cc7391200bee6847391200beeaa96391200bee2a16391200bee69d6391200bee29d6391200fae5d96391200fe65cd6391200bee2856391200beeaa95391200bee69d5391200bee29d5391200bee6995391200fce5d55391200fe65cd5391200bee2855391200bee2a23391200bee29e3391200fe65ce3391200fe658e3391200fe654e3391200bee2863391200beeaa97291200bee2a17291200f6e9dd7291200f6e5cd7291200bee2857291200beeaa96291200bee2a16291200bee69d6291200bee29d6291200fae5956291200fae58d6291200fea5c96291200bee2856291200beeaa95291200bee69d5291200bee29d5291200bee6995291200fce54d5291200fea5c95291200bee2855291200bee69d3291200bee6993291200bee6953291200fea5c93291200beeaa88191200bee69c8191200bee6988191200bee68c8191200bee6888191200beeaa97191200bee2a17191200f6e21d7191200f6e9dd7191200fae2997191200f6e5d97191200f6e5c97191200beeaa87191200bee2a07191200f6e9dc7191200bee6987191200bee6947191200bee68c7191200bee6887191200f6e5c47191200fec5c47191200beeaa96191200bee2a16191200bee69d6191200bee29d6191200fae5896191200fec5c56191200beeaa95191200bee69d5191200bee29d5191200bee6995191200fce5955191200fce54d5191200fce5495191200fec5c55191200beeaa93191200bee2a13191200bee69d3191200bee29d3191200bee6993191200bee6953191200fe620d3191200fe658d3191200fe68cd3191200fea2893191200fe64c93191200fec5c53191200bee69c3191200bee6983191200bee6943191200fe64c43191200beeaa92191200bee2a12191200bee69d2191200bee29d2191200bee6992191200bee6952191200bee68d2191200fea5892191200fec4c52191200bee2a21191200bee69e1191200bee29e1191200bee69a1191200bee6961191200bee68e1191200bee68a1191200fec2061191200fec5c61191200fec1c61191200fec5861191200fec5461191200fec4c61191200fec0c61191200fec4861191200bf6285988ce00bf6aa8988ce00bf6698988ce00bf6690988ce00fe6690988ce00bf6688988ce00bf6684988ce00bf62a5868ce00bf629d868ce00bf6285868ce00bf62a5848ce00ef6261848ce00bf629d848ce00fe6651848ce00bf6285848ce00bf6aa9648ce00bf62a1648ce00bf6285648ce00bf62a1928ce00bf629d928ce00bf6285928ce00bf62a5828ce00ef6261828ce00bf62) else (if i < 7 then 0x58d414c600ff48cd414c600ff8249414c600fec509414c600ff44c9414c6009fe2a2990c6009fe69c980c6009fe694980c6009feaa9970c6009fe2a1970c600d7e21d970c600d7e9dd970c600d7e5d9970c600d7e5d1970c6009fe68d970c600d7e5c9970c6009fe69d960c600dbe5d9960c600dbe591960c6009feaa9950c6009fe2a1950c6009fe69d950c6009fe699950c600dde615950c600dde5d5950c600dde595950c600dde551950c600dde549950c600bdeaa9950c600dde661950c600dde65d950c6009fe69d940c6009fe699940c6009fe695940c600dee5d1940c600dee591940c600df665e330c600df665a330c600df6656330c6009fe69d920c6009fe695920c600dfa5c9920c600bf6aa9310c600bfcaa9310c600dfc65d310c6009fe2a299486009fe69c98486009fe69498486009fe69098486009fe68c98486009feaa997486009fe2a19748600d7e9dd9748600dbe29997486009fe69097486009fe68c97486009feaa995486009fe2a195486009fe69d9548600dde54d95486009feaa994486009fe2a194486009fe69d94486009fe69994486009fe69594486009feaa993486009fe2a193486009fe69d93486009fe69993486009fe69593486009fe6919348600df68cd93486009fe69c93486009fe6949348600dfa65d6248600fba5956248600dfa6516248600fba58d6248600bfcaa93148600dfca653148600dfc65d3148600dfc6513148600ff420d3148600ff458d3148600ff48cd3148600ff858931486009fe69098846009fe68c98846009fe6889884600cfe60898846009fe2a194846009fe2a193846009fe69c93846009fe69893846009fe6949384600df658c93846009fe68493846009fe2a19284600dfa5c99284600dfa5099284600bfc2a58184600bfc28d8184600bfc6908184600bfc68c8184600bfc2a14184600dfc2614184600bfc29d4184600bfc6954184600fec5d14184600fec5914184600bfc28d4184600dfc64d4184600fec5094184600bfc2a53184600bfc2a13184600bfc69d3184600bfc29d3184600dfc65d3184600bfc6953184600bfc6913184600dfc6513184600ff420d3184600ff458d3184600ff48cd3184600ff82893184600dfc6493184600ff44c93184600bfc69c3184600bfc6943184600bfc6903184600ff48cc3184600bfc69d2184600bfc6952184600bfc6912184600bfc68d2184600beeaa88791200bee6988791200bee68c8791200bee6888791200bee6848791200bee2a27791200f6e21e7791200bee69a7791200bee6967791200bee68e7791200bee68a7791200bee6867791200bee2867791200beeaa97691200bee2a17691200f6e9dd7691200bee2857691200beeaa97591200f6e9dd7591200bee2857591200beeaa96591200bee69d6591200bee29d6591 else 0x6009fe6919320600df620d9320600df658d9320600df68cd9320600dfa2899320600df64c993206009fe69d92206009fe69592206009fe69192206009fe68d92206009fe2a299506009fe69e99506009fe69a99506009fe6969950600dee69299506009fe68e99506009fe68a99506009feaa898506009fe69c98506009fe69898506009fe68c98506009fe68898506009fe68c97506009fe6889750600d7e5c497506009feaa99550600cfe2a19550600beeaa97450600deea657450600bee2a17450600f6e25d7450600f6e21d7450600f6e9dd7450600dee6557450600bee28d7450600f6e5cd7450600fec2857450600beeaa96450600deea656450600bee2a16450600bee69d6450600bee28d6450600fae58d6450600fec28564506009fe69c93506009fe69893506009fe6949350600df64c49350600beeaa94250600deea654250600bee2a14250600bee69d4250600bee6994250600dee6554250600bee28d4250600fea5894250600fea4c94250600bfcaa88150600dfca648150600fec5d08150600fec5908150600bfc68c8150600fec50881506009fe2a2994c6009fe69e994c6009fe69a994c6009fe696994c6009fe692994c600df668e994c6009fe68a994c600dfa68a994c600dfc686994c6009feaa8984c6009fe69c984c6009fe698984c6009fe694984c6009fe690984c6009fe68c984c600cfe60c984c6009fe688984c6009fe684984c600cfe604984c6009feaa9974c6009fe2a1974c600dfa289974c6009fe690974c6009fe68c974c600d7e5cc974c6009fe688974c6009fe684974c600d7e5c4974c6009feaa9954c6009fe2a1954c600dfa289954c600dde549954c6009feaa9944c6009fe2a1944c6009fe69d944c6009fe695944c600dee5d1944c600dfa289944c600dee509944c600bf6aa8834c600df6a64834c600bf6698834c600fd6694834c600df6654834c600df6650834c600bf6688834c600bf6aa9634c600df6a65634c600bf62a1634c600df665d634c600fb65d9634c600fb6591634c600fb6589634c600ff4285634c600df62a6334c600bf62a2334c600df6262334c600df665e334c600df625e334c600bf669a334c600df6656334c600df6652334c600bf668a334c600dfaa64924c600dfa260924c600dfa65c924c600dfa25c924c600dfa658924c600dfa654924c600dfa650924c600ff220c924c600ff258c924c600ff28cc924c600bf6aa9324c600df6a65324c600bf62a1324c600bf6699324c600ff25c9324c600ff2509324c600dfca65714c600ff428d714c600ff420d714c600ff48cd714c600ff8249714c600f7c5c9714c600ff44c9714c600bfcaa9414c600dfca65414c600dfc261414c600bfc69d414c600fec5d1414c600fec591414c600ff428d414c600ff420d414c600ff4))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x68cd735ca00d7e9dc915ca009fe694915ca009fe690915ca009fe68c915ca00dfc5c4915ca009fe2a29958a009fe6909858a009fe68c9858a009fe69c9358a009fe6949358a00bfaaa97258a00dfaa657258a00dfa2617258a00f7a9dd7258a00bfa28d7258a00f7a5cd7258a00fba58d7258a009fe6909158a009fe68c9158a00dfa5c89158a00dfc6049158a00dfc5049158a009fe2a29954a009fe69e9954a009fe69a9954a009fe6929954a009fe68e9954a009fe6869954a009feaa89854a009fe69c9854a009fe6989854a009fe68c9854a009fe6849854a009feaa99754a009fe2a19754a00d7e9dd9754a009fe6909754a009fe68c9754a009fe6849754a009fe69c9354a009fe6989354a009fe6849354a00bdeaa95354a00ddea655354a00dde65d5354a00fd624d5354a00fd620d5354a00fd65cd5354a00fd68cd5354a00bfaaa97254a00dfaa657254a00bfa2a17254a00dfa2617254a00f7a25d7254a00f7a9dd7254a00f7a5cd7254a00fda54d7254a009fe69c9154a009fe6909154a009fe68c9154a00dfa5c89154a009fe2a29950a009fe69c9850a009fe6989850a009fe6849850a009feaa99750a009fe2a19750a00d7e9dd9750a00df628d9750a00d7e5cd9750a009fe6849750a009feaa99650a009fe2a19650a00dbe58d9650a009feaa99550a009fe69d9550a009fe6999550a00dde54d9550a00deea658450a00dee65d8450a00deea655450a00dee65d5450a00fce5955450a00fce54d5450a009fe69c9350a009fe6989350a009fe6949350a00dee6109350a00dee5509350a00df658c9350a00df654c9350a009fe6849350a00dee65d4350a00bee6954350a00bfaaa96250a00dfaa656250a00bfa2a16250a00dfa65d6250a00fba5956250a00fea6116250a00fea5516250a00dfa24d6250a00fba58d6250a00fea50d6250a00bfa2856250a009fe69c9150a009fe6949150a009fe2a2994ca009fe69c984ca009fe698984ca009fe694984ca009fe684984ca009feaa9974ca009fe2a1974ca00d7e9dd974ca009fe684974ca009feaa9964ca009fe2a1964ca009fe69d964ca009feaa9954ca009fe2a1954ca009fe69d954ca009fe699954ca009fe69d944ca009fe699944ca009fe695944ca00df665e334ca00df665a334ca00df6656334ca00bfaaa9724ca00dfaa65724ca00dfa261724ca00f7a9dd724ca00dfa659724ca00dfa655724ca00ff228d724ca00f7a5cd724ca00ff28cd724ca00bfa69d424ca00dfa659424ca00fea611424ca00fea551424ca009fe69c914ca009fe694914ca00dfa5c8914ca009fe69c93606009fe6989360600df64c493606009fe2a299206009feaa99420600dee5d19420600dee5919420600dee50994206009feaa993206009fe2a193206009fe69d93206009fe695932 else 0x1ce00dfc845911ce00bfcaa9911ce00dfc661911ce009fe2a29954e009fe69e9954e009fe69a9954e00dde6969954e009fe6929954e009fe68a9954e009fe6869954e009feaa89854e009fe69c9854e009fe6989854e009fe6889854e009fe6849854e009fe6909754e00d7e5cc9754e009fe6889754e009fe6849754e00d7e5c49754e00ddea658554e00ede2618554e00dde25d8554e00ddea655454e00dde25d5454e00fce5d15454e00bf6aa88354e00df6a648354e00bf669c8354e00fd66948354e00bf6aa97354e00df6a657354e00bf62a17354e00f7625d7354e00fd66157354e00f765d17354e00fd65517354e009fe69c9154e009fe6909154e00dfc4c49154e009fe2a29950e009fe69c9850e009fe6989850e009fe6849850e009feaa99750e009fe2a19750e009fe6849750e009feaa99550e009fe69d9550e00beeaa97450e00deea657450e00f6e21d7450e00dee6557450e00fe628d7450e00f6e5cd7450e00fe65d08350e009fe69c9150e009fe6949150e009fe69c988ce00cfe61c988ce009fe698988ce009fe694988ce009fe690988ce00dee690988ce00cfe610988ce009fe688988ce00cfe608988ce009fe684988ce009fe2a1978ce009fe690978ce00d7e5d0978ce009fe688978ce00d7e5c8978ce009fe684978ce009fe2a1968ce009fe2a1958ce009fe2a1948ce00dee611948ce00dee551948ce00dee505948ce00bf62a5838ce00bf629d838ce00bf6285838ce00bf669c838ce00bf6698838ce00bf6694838ce00bf6684838ce00bf62a5738ce00bf62a1738ce00f769dd738ce00df6659738ce00df6655738ce00f765d1738ce00bf6285738ce00f769dc738ce00bf6698738ce00bf6694738ce00bf6684738ce00bf62a1538ce00df6261538ce00bf669d538ce00bf629d538ce00df665d538ce00fd6615538ce00fd65d5538ce00fd6551538ce00bf6285538ce00df6261438ce00bf669d438ce00bf6695438ce00fe65d1438ce009fe2a1928ce00dfa589928ce009fe2a1918ce009fe69c918ce009fe694918ce009fe690918ce00dfc5c4918ce00dfc504918ce009fe68c9760a009fe6849760a00d7e5c49760a009fe69c9360a009fe6989360a00df658c9360a009fe6849360a00df64c49360a009fe69c9160a009fe68c9160a009fe2a2995ca009fe69a995ca009fe696995ca009fe692995ca009fe68e995ca00dfa68a995ca009fe686995ca009feaa8985ca00cfe61c985ca009fe698985ca009fe694985ca009fe690985ca00dee690985ca009fe68c985ca009fe684985ca00d7e262775ca00b7e68e775ca00b7e686775ca00d7e9dc935ca009fe698935ca009fe694935ca00df65cc935ca009fe684935ca00b7eaa9735ca00d7ea65735ca00f7624d735ca00f7658d735ca00f7654d735ca00f7) else (if i < 11 then 0xfe2a19544200cfe2a193442009fe69d93442009fe6959344200dde95593442009fe6919344200dee2919344200dee9119344200df68cd9344200dfa28993442009fe69c93442009fe69893442009fe6949344200dde9549344200df64c493442009fe69d92442009fe69992442009fe6959244200dde95592442009fe6919244200dee91192442009fe68d9244200cfe64d8244200dfa65e2244200dfa25e2244200dfa65a2244200efa61a2244200fba99a2244200dfa6562244200fda9562244200dfa6522244200fea9122244200dfa64e2244200efc2a15144200bfcaa94144200fbc9994144200fec5d14144200fec5914144200dfc64d4144200fec5094144200ff88894144200dfc64e1144200dfc24e1144200dfc64a1144200efc60a1144200ff888a11442009feaa993042009fe69d9304200df65cd9304200df61cd9304200df658d9304200df68cd9304200df64c993042009fe69d92042009fe68d9204200dfa5c99204200dfa4c99204200dfa65e2204200dfa64e2204200dfc64e11042009fe68c97612009fe68897612009fe6849761200d7e5c497612009fe69c93612009fe69893612009fe6849361200df64c493612009fe69c91612009fe68c9161200d7e5cc9760e009fe6889760e009fe6849760e00d7e5c49760e009fe69c9160e00dfc4c49160e009fe2a29920e009feaa99720e009fe2a19720e00d7e21d9720e00d7e9dd9720e00d7e5d19720e00d7e5c99720e009feaa99620e009fe69d9620e00dbe5d99620e00dbe5919620e00dbe5899620e009feaa99520e009fe69d9520e009fe6999520e00dde5d59520e00dde5959520e00dde5499520e00dde5459520e00bdeaa99520e00dde65d9520e00dde6599520e00dde6459520e009fe69d9420e009fe6999420e00dee5d19420e00cfe65d8320e009fe69d9220e009fe6999220e009fe6959220e00dfa5c99220e009feaa99120e009fe69d9120e009fe6999120e009fe6959120e009fe6919120e009fe6899120e00dfc2059120e00dfc5c59120e00dfc5059120e00dfc4859120e00dfc8459120e009fe2a2995ce009fe692995ce00df668e995ce009fe68a995ce009fe686995ce009feaa8985ce009fe690985ce009fe68c985ce00cfe60c985ce009fe688985ce009fe684985ce009fe690915ce00dfc4c4915ce009fe2a2991ce00cfe645981ce009fe684981ce009fe695941ce00dee611941ce00dee591941ce00dee551941ce00dee505941ce00dee661941ce00dee645941ce00bf6aa9731ce009fe699921ce009fe695921ce00dfa609921ce00dfa589921ce00dfa549921ce00dfa485921ce00dfa661921ce00dfa645921ce009feaa9911ce009fe2a1911ce009fe691911ce009fe689911ce00dfc605911ce00dfc205911ce00dfc505911ce00dfc48591 else 0x24c200fea252224c200efa612224c200fea912224c200ff254e224c200ff250e224c200ff28ce224c2009fe69c914c2009fe694914c200dde954914c2009fe690914c200dee910914c200df68cc914c200dfc4c4914c200bf6aa9314c200ef62a1314c200df6261314c200ef661d314c200fb6999314c200bf6695314c200fd6955314c200bf6691314c200fe6251314c200ef6611314c200fe6911314c200ff2289314c200ef6609314c200ff2889314c200ff4245314c200ff45c5314c200ff4505314c200ff4485314c200ff4845314c2009feaa9970c200d7e9dd970c200d7e5c9970c200d7e5c5970c2009fe69d960c200dbe5d9960c200dbe589960c200dbe585960c200dbe65e660c200df665a330c200fb699a330c2009fe69d920c2009fe699920c200dbe999920c200dfa5c9920c200dfa485920c200dfa65e220c200dfa65a220c200fba99a220c2009feaa9910c2009fe69d910c2009fe699910c200dbe999910c200df68cd910c2009fe689910c200dfa889910c200dfc5c5910c200dfc485910c200dfc845910c2009fe2a19748200cfe2a19748200d7e9dd9748200dde2959748200d7e5c597482009fe69097482009fe68c97482009fe6849748200dfc2859648200dbe65e6648200cfe2a195482009fe69d9548200dbe9999548200dde5459548200dde65e5548200f9e99a55482009fe69d94482009fe6999448200dbe9999448200dee5059448200dee65e4448200dee25e4448200dee65a4448200fae99a44482009fe69d93482009fe6999348200dbe99993482009fe6959348200dde95593482009fe6919348200dee2919348200dee9119348200df68cd9348200df64c593482009fe69c93482009fe6989348200dbe99893482009fe6949348200dde95493482009fe6849348200cfe65d8348200ebe9998348200bfaaa97248200efa2a17248200f7a9dd7248200dfa6597248200fba9997248200dfa6557248200fda9557248200fea9117248200bfa28d7248200dfa64d7248200efa60d7248200f7a5cd7248200f7a5c57248200bfaaa95248200efa2a15248200bfa69d5248200dfa65d5248200fba9995248200bfa28d5248200fda54d5248200fda5455248200bfaaa94248200bfa69d4248200dfa6594248200fba9994248200bfa28d4248200dfa64d4248200fea50d4248200fea50542482009fe69c91482009fe6949148200dde95491482009fe6909148200dee91091482009fe68c9148200dfa5c89148200dfa5089148200dfc5c49148200cfe6598148200ebe9998148200efa5c98148200bfaaa92148200bfa69d2148200dfa6592148200fba9992148200bfa6952148200fda9552148200bfa6912148200fea9112148200bfa28d2148200efa60d2148200efa6052148200ff84c52148200ff88452148200c)) else (if i < 14 then (if i < 13 then 0xdde481950c600dde441950c6009fe69d900c600cfe61d900c6009fe699900c600cfe619900c600dbe999900c6009fe695900c600dde955900c6009fe691900c600cfe611900c600dee911900c6009fe689900c600cfe609900c600dfa889900c600df64c5900c6008ff68c9884600cf78cc98846008ff6889884600cfb8889884600cfe4809884600aefaa97461200e6f9dd7461200aef28d7461200e6f5cd7461200aefaa94261200aef69d4261200aef28d4261200eeb5894261200eeb4c942612008ffaa99720e00c7f9dd9720e00c7f5c19720e008ffaa99620e008ff69d9620e00cbf5d99620e00cbf5819620e008ffaa99520e008ff69d9520e008ff6999520e00cdf5d59520e00cdf5959520e00cdf5459520e00cdf65e5520e00cdf65a5520e00af7aa95320e00cf765d5320e00ed75d55320e00ed75455320e008ffaa99120e008ff69d9120e008ff6999120e008ff6959120e00cdf9559120e00cfd5c59120e00cfd8459120e00cfd4419120e00af7aa93120e00cf76593120e00af76953120e00ed79553120e00ef55c53120e00ef58453120e008ffaa99020e008ff6999020e00cfe5c19020e00afb6908788a00e7b5d08788a00afb68c8788a00afb6848788a00e7b5c48788a00afb6808788a00edb5958588a00edb54d8588a00ebb9998488a00eeb5d18488a00eeb21e4488a00fab99a4488a00ebb9998388a00ebb99a22606008ffaa99520600cef5d194206008ffaa993206008ff69d93206008ff6959320600cdf95593206008ff6919320600cef9119320600cf78cd9320600cf74c19320600afdaa95120600eed5d14120600cfd64d41206008ffaa990206008ff68d9020600ede2a15154200fba99a2250200beeaa94150200fae9994150200fea8894150200fec4c541502009fe698984c200cfe2a1974c200dee291974c2009fe690974c200d7e5cc974c2009fe688974c2009fe684974c200afe2a5874c200dbe262664c200ebe61e664c200cfe2a1954c200dbe999954c200dde545954c200f9e99a554c2009fe69d944c200dbe999944c200deea64944c200dee65c944c200dee25c944c200dee658944c200fae998944c200dee648944c200dee644944c200dee244944c200ebe999844c200eee5d1844c200eee509844c200bee2a6444c200dee65e444c200dee25e444c200fae99a444c200bf6aa9534c200ef62a1534c200df665d534c200fb6999534c200fd65d5534c200fd6549534c200fd6545534c200bf6aa9434c200fb6999434c200fe65d1434c200fe6509434c200fb699a334c200df6652334c200fe6252334c200ef6612334c200fe6912334c200bf6686334c200ebe999824c200ef68cd824c200dfa65e224c200dfa25e224c200efa61e224c200fba99a224c200dfa656224c200fda956224c200dfa6522 else 0x941ce00cef605941ce00cef205941ce00dee681941ce00dee5c1941ce00dee581941ce00dee541941ce00dee4c1941ce00dee481941ce00dee441941ce00dee041941ce009fbaa9921ce00cfb6a1921ce00cfb61d921ce00cfb619921ce00dbb999921ce00cfb615921ce00ddb955921ce00cfb611921ce00deb911921ce00cfb60d921ce00d7b5cd921ce00cfb605921ce00cfb205921ce00dfa681921ce00dfa5c1921ce00dfa581921ce00dfa541921ce00dfa501921ce00dfa4c1921ce00dfa441921ce00dfa041921ce009fdaa9911ce00cfd6a1911ce00cfd2a1911ce00cfd611911ce00ded911911ce00cfd60d911ce00cfd609911ce00df9889911ce00dfc681911ce00dfc281911ce00dfc501911ce00dfc4c1911ce00dfc481911ce009fe691901ce00cfe611901ce00dee911901ce00cfe60d901ce009fe689901ce00cfe609901ce00dfa889901ce009fe685901ce00cfe605901ce00cfe205901ce008ffaa89854e008ff69c9854e00c7f9dc9854e008ff6989854e00cbf9989854e00cdf6949854e00cf78cc9854e008ff6889854e00cfb8889854e008ff6849854e00cdf5449854e00cfd8449854e00cfe4c09854e008ff698988ce00cbf998988ce008ff690988ce00cef690988ce00cef910988ce008ff688988ce00cfb888988ce00cfd844988ce00cfe5c0988ce00cfe500988ce00cfe480988ce008ffaa8985ca00c7f9dc985ca008ff698985ca00cbf998985ca008ff694985ca00cdf954985ca008ff690985ca00cef690985ca00cef910985ca008ff68c985ca00cf78cc985ca00cfb548985ca008ff684985ca00c7f5c4985ca00cfd844985ca00cfe5c0985ca008ffaa89854a008ff69c9854a00c7f9dc9854a008ff6989854a00cbf9989854a008ff68c9854a00cf78cc9854a00cfb5c89854a008ff6849854a00cdf5449854a00cfd8449854a009fe68d9020600df68cd90206009fe6899020600dfa88990206008ffaa89854600cfd8449854600cfe44098546008ff69c9850600c7f9dc98506008ff6989850600cbf99898506008ff68c9850600cf78cc98506008ff6889850600cfb8889850600cfe5c098506008ffaa8984c6008ff69c984c600c7f9dc984c6008ff698984c600cbf998984c6008ff694984c600cdf954984c6008ff690984c600cef910984c600cf78cc984c6008ff688984c600cfb888984c600cfd504984c600cfd844984c600cfe4c0984c600cfe440984c6009dfaa9950c600cdf6a1950c600cdf2a1950c600cdf61d950c600cdf21d950c600cdf619950c600d9f999950c600cdf611950c600dcf911950c600cdf60d950c600cdf609950c600ddb889950c600cdf605950c600dde681950c600dde281950c600dde5c1950c600dde1c1950c600dde581950c600dde501950c600dde4c1950c600) else (if i < 15 then 0x8ff2a57260600afd28562606008ff6a47320600afd6847320600bee6907350200bee6907150200bee6903150200bee692994c200d7e65c974c200bfa688974c200bf668c874c2009fe2a5744c2009fe2a5644c2009fe2a5724c200bf628d724c2009fe2a5524c200bde694914c200dfc644914c200bf668c814c2009fe2a5714c200bf668c714c2009fe2a5514c2009fe2a5414c2009fe6a4710c200afe2a19748200bfa6888748200bfc2859648200afe2a19548200bfa6888348200bfa6887348200bfa6888148200bfa6887148200bfa6883148200df664c9344200bfc68483442009fe2a57344200bfc68473442009fe2a553442009fe2a572442009fe2a552442009fe6a47304200bfc6847304200cfe660985ce009fe2a5845ce00dfc644915ce00d7e65c9754e00bbe6989754e00bee6909754e00bfa6889754e00bfc6849754e00b7e29d9654e009fe2a57454e00dfc6449154e00bee690988ce009fe2a5878ce009fe2a5858ce009fe2a5848ce009fe2a67760a009fe2a57360a009fe2a63360a00bf628d985ca00cfe660985ca00bee690985ca009fe2a5865ca009fe2a5855ca00bf628d945ca009fe2a5845ca00afe6a0935ca00bbe698935ca00bde694935ca00bee690935ca00df664c935ca00bfc684935ca009fe2a5835ca009fe2a5635ca009fe2a5535ca00bee690915ca00dfc644915ca00d7e65c9754a009fe2a57454a009fe2a56454a00df664c9354a009fe2a57354a009fe2a56354a00dfc6449154a009fe2a573606009fe2a633606009fe2a572606009fe6a47320600d7e65c9750600afe2a19550600bde6949350600df664c93506009fe2a573506009fe2a563506009fe2a553506009fe2a572506009fe2a55250600bfa68a994c600cfe660984c600d7e65c974c600bee690974c6009fe2a5874c6009fe2a5864c6009fe2a5854c6009fe2a5844c6009fe2a5744c6009fe2a5644c6009fe2a5824c6009fe2a5724c6009fe2a5524c6009fe6a5714c6009fe6a4870c6009fe2a584846009fe2a583846009fe2a582846009dfaa99520e00cdf21d9520e00d5f9dd9520e00d9f9999520e00dd78cd9520e00ddb8899520e00cdf2059520e00ddd8459520e00dde6819520e00dde5c19520e00dde5819520e00dde4c19520e00dde4819520e00dde4419520e009fe69d9020e00d7e9dd9020e009fe6999020e00dbe9999020e009fe6899020e00dfa8899020e00df64c59020e00dfc8459020e008ff690985ce00cef910985ce00cf754c985ce00cf78cc985ce008ff688985ce00cfb888985ce008ff684985ce00cfd844985ce00cfe4c0985ce009efaa9941ce00cef6a1941ce00cef61d941ce00cef619941ce00daf999941ce00cef615941ce00dcf955941ce00cef60d941ce00d6f5cd941ce00cef609941ce00deb889 else 0x59020e00cff9dd9420600cff5cd9420600cff1cd9420600cff8cd9420600cff5d59320600cff5c19320600efd9dd4120600efd5cd4120600efd1cd4120600efd8cd4120600cff5cd9020600cff1cd9020600cff8cd9020600af768c8720e009fe680915ce008ff2a2991ce009fd286991ce009ef690981ce009fb688981ce009fd684981ce00cef661941ce00dcf655941ce00cfb661921ce00dbb659921ce00ddb655921ce00deb651921ce008ff2a1911ce00cfd661911ce00ded651911ce00df9649911ce00cfe661901ce00dee651901ce00dfa649901ce00dfc645901ce009bf6989754e009ef6909754e009fb6889754e009fd6849754e009fe6809754e009fe6809154e008ff2a29950e008ff2a19750e009fe6809750e009ef2a57450e009fe6809150e008ff2a2995ca009ef690985ca00aef690985ca009bf698935ca009df694935ca009ef690935ca009fd684935ca009fe680935ca009ef690915ca009fe680915ca008ff2a29958a009fe6809858a009fe6809358a009ef6909158a009f768c9158a009fe6809158a008ff2a29954a008ff2a19754a009fe6809754a009fe6809354a009fe6809154a008ff2a29950a008ff2a19750a009f728d9750a009fe6809750a008ff2a19650a0097f69c9350a009bf6989350a009df6949350a009fd6849350a009fe6809350a009fe6809150a008ff2a2994ca008ff2a1974ca009fe680974ca008ff2a1964ca008ff2a1954ca009fb2a5724ca009df694914ca009fe680914ca00cf764c8320600afd68483206009fe68097506009ef2a574506009df69493506009fe68093506008ff2a2994c6009fb68a994c6008ff2a1974c6009ef690974c6009fe680974c6008ff2a1954c6008ff2a1944c600cfb260924c6009fd2a5714c600dfa249904c600bbe698904c6008ff2a2990c6009df694980c6008ff2a1970c6009ef690970c6009fb688970c6009fe680970c6008ff2a1950c600cdf661950c600dde655900c6008ff2a299486008ff2a197486009fe68097486008ff2a195486008ff2a194486008ff2a193486009df69493486009fe68093486009ef692994c2008ff2a1974c2009fb688974c2009df694914c2009fe2a5704c200bf628d704c2008ff2a197482009fd28596482008ff2a193442009fe2a53044200df624d3044200bfc28530442008ff2a677612008ff2a57361200aef69073612008ff2a563612008ff2a63361200aef69233612008ff2a572612008ff2a57161200aef69071612008ff2a531612008ff2a611612008ff2a57260e008ff2a57160e008ff6a47120e00af768c7120e008ff2a67760a008ff2a57360a00afb6887360a008ff2a56360a008ff2a63360a008ff2a57160a008ff2a53160a008ff2a61160a009fb2a53188a008ff2a57360600afd684736060)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0xdfb5c5921ce00dfb585921ce00dfb545921ce00dfb505921ce00dfb4c5921ce00dfb845921ce00dfb681921ce00dfb581921ce00dfb441921ce00dfd5cd911ce00dfd54d911ce00dfd5c9911ce00dfd589911ce00dfd549911ce00dfe5cd901ce00dfe54d901ce00dfe5c9901ce00dfe589901ce00dfe549901ce00dfe4c5901ce00dfe485901ce00cff69c9858e00cff9dc9858e00cff5d49858e00cff5d09858e00cff5cc9858e00cff1cc9858e00cff8cc9858e00cff5c89858e00cff5c49858e00cff6989854e00cff58c9854e00cff5889854e00cff5849854e00cff4c49854e00cff4849854e00cff590988ce00cff588988ce00cff548988ce00cff5c4988ce00cff584988ce00cff484988ce00cff698985ca00cff5d8985ca00cff5d4985ca00cff594985ca00cff5d0985ca00cff590985ca00cff5c4985ca00cff584985ca00cff69c9854a00cff9dc9854a00cff6989854a00cff5d89854a00cff5cc9854a00cff58c9854a00cff5c49854a00cff5849854a00cff4c49854a00cff9dc9850600cff5d89850600cff5cc9850600cff1cc9850600cff58c9850600cff8cc9850600cff5c89850600cff5889850600cff4c89850600cff9dc984c600cff5d8984c600cff5d4984c600cff594984c600cff5d0984c600cff590984c600cff5cc984c600cff58c984c600cff54c984c600cff50c984c600cff5c8984c600cff588984c600cff548984c600cff508984c600ddf69d950c600ddf9dd950c600ddf699950c600ddf5d9950c600ddf691950c600ddf5d1950c600ddf591950c600ddf68d950c600ddf5cd950c600ddf58d950c600ddf689950c600ddf5c9950c600ddf5c5950c600ddf4c5950c600cff5cc9884600cff1cc9884600cff8cc9884600cff5c89884600cff5489884600cff5089884600cff4c89884600cff6919221e00cff6859221e00cff5059221e00cff8459221e00cff6819221e00edf68d6561600edf6896561600edfaa95361600edf69d5361600edf6995361600edf6895361600edf6855361600eef5d97461200eef28d7461200eef5cd7461200eef58d7461200eef8cd7461200eef5c97461200eef5897461200eef4c97461200eef2857461200eef5c57461200eef5857461200eef4c57461200eef0c57461200eef4857461200eef8457461200eef9dd4261200eef5d94261200eef5cd4261200eef58d4261200cff5959720e00cff5859720e00cff5459720e00cff8459720e00cff5819720e00cff4419720e00cff5d59620e00cff5c19620e00cff4419620e00cff6999520e00cff5859520e00ef76995320e00ef76855320e00ef75855320e00cff9dd9120e00cff5d99120e00cff5d59120e00cff5959120e00ef79dd3120e00ef75d93120e00ef75d53120e00ef75953120e00cff5c59020e00cff58 else 0xc9324c600ff3509324c600fed5d1414c600cff65d980c6009ff69c980c6009ffaa9970c600d7f5d9970c600d7f5d1970c600d7f5c9970c6009ff69d960c600dbf5d9960c600dbf591960c6009ff69d950c6009ff699950c600ddf5d5950c600ddf595950c600ddf549950c600ddf65d950c6009ff69d920c6009ff695920c600dfb5c9920c6009ff68c9748600ddf54d95486009ff69c93486009ff6949348600fbb5956248600fbb58d62486009ff688974c2009ff69c914c200efb2a17248200dfb6597248200dfb64d7248200f7b5cd7248200ffa5c930482009ff69c9344200ffa5c92044200affaa96361e00cff2a56361e00ef75cd6361e00efb5c96261e00cff2a56361600affaa97661200affaa97361200aff6987361200affaa96361200cff2a56361200aff69d6361200ebf5d96361200ef75cd6361200affaa97261200eef6917261200e7f5cd7261200affaa96261200aff69d6261200ebf58d6261200efb5c96261200aff69d3261200aff6993261200efb5c93261200aff68c7161200aff69c3161200affaa97660e00aff6987360e00affaa96260e00aff69d6260e00efb5c96260e00aff69c3160e00affaa96520e00edf5d56520e00aff6987120e00affaa96120e00efd5c56120e00aff6995120e00edf5955120e00affaa97660a00affaa97360a00aff6987360a00affaa96360a00cff2a56360a00aff69d6360a00ebf5d96360a00ef75cd6360a00aff68c7160a00aff69c3160a00affaa97360600aff6887360600cff2a56360600affaa97260600e7f5cd7260600efb5c96260600affaa93260600aff69d3260600aff6993260600efb5c93260600aff69c3160600affaa97320600aff6907320600affaa95320600ef75cd5320600affaa94320600aff69d4320600eef5d14320600cff58c989de00cff5d8985d200cff9dc9859200cff1cc9859200ddf69d9520e00ddf9dd9520e00ddf6999520e00ddf5d99520e00ddf5cd9520e00ddf58d9520e00ddf6899520e00ddf5c99520e00ddf5899520e00ddf5c59520e00ddf5859520e00ddf4c59520e00ddf4859520e00cff698985ce00cff5d8985ce00cff5d4985ce00cff58c985ce00cff54c985ce00cff588985ce00cff548985ce00cff508985ce00cff4c4985ce00cff484985ce00ddf691951ce00ddf68d951ce00ddf689951ce00ddf685951ce00def5cd941ce00def58d941ce00def54d941ce00def5c9941ce00def589941ce00def549941ce00def205941ce00def5c5941ce00def585941ce00def545941ce00def4c5941ce00def485941ce00def581941ce00def481941ce00def441941ce00dfb69d921ce00dfb699921ce00dfb695921ce00dfb5d1921ce00dfb591921ce00dfb5cd921ce00dfb58d921ce00dfb54d921ce00dfb685921ce00dfb205921ce) else (if i < 19 then 0xe00dfb645921ce00dfe645901ce00cff6a29958e009ff6969958e00affaa89858e00cffa649858e00aff69c9858e00cff65c9858e00cff25c9858e00edf6949858e00cff2a19758e00ebf2617658e00ef72a17358e00ef72617358e00dfd4c49158e009ff69e9954e009ff69a9954e009ff68a9954e00aff6989854e00cff6589854e00aff6849854e00cff6449854e009ffaa99754e00cff2a19754e009ff6889754e00d7f5c49754e009ffaa99654e00cff2a19654e009ff69d9654e00d7f29d9654e00ddf6597554e00ef72a17354e009ff69c9154e00f6f5cd7450e009ff69c9150e009ff69a995ca009ff696995ca009ff68e995ca009ff698985ca009ff68c985ca00aff698985ca00cff658985ca00aff694985ca00cff654985ca00aff690985ca00cff650985ca00aff684985ca00cff644985ca009ff698935ca009ff694935ca00f7758d735ca00f7754d735ca009ff68c915ca009ff68c9858a009ff69c9358a009ff6949358a00efb6a17258a00efb2a17258a00dfb2617258a00bfb28d7258a00f7b5cd7258a00fbb58d7258a009ff68c9158a00dfb5c89158a00cff2a29954a009ff69e9954a009ff69a9954a009ff68e9954a00aff69c9854a00cff65c9854a00aff6989854a00cff6589854a00aff6849854a00cff6449854a009ffaa99754a00cff2a19754a009ff68c9754a009ffaa99654a00cff2a19654a009ff69d9654a009ff69c9354a009ff6989354a00ddf65d5354a00fd75cd5354a00efb2a17254a00efb2617254a00f7b5cd7254a00fdb54d7254a009ff69c9154a009ff68c9154a00dfb5c89154a00d7f5cd9750a00dbf58d9650a009ff69c9350a009ff6989350a00df758c9350a00dfb65d6250a00dfb24d6250a00fbb58d6250a00feb50d6250a009ff69c9150a009ff69c984ca009ff698984ca009ffaa9974ca009ffaa9964ca00cff2a1964ca009ff69d964ca009ffaa9954ca009ff69d954ca009ff699954ca00dfb261724ca00dfb659724ca00dfb655724ca00f7b5cd724ca00bfb69d424ca00dfb659424ca009ff69c914ca00dfb5c8914ca00aff6888720600aff69c8320600cff21d92206009ff696995c6009ff694935c600ddf54d951c600ddf549951c6009ff695931c6009ff695921c6009ff6949358600edf2a15354600edf2615354600ddf65d5354600bdf6995354600edf2a15254600bdf6995254600bdf68d52546009ff68c97506009ff6889750600bef28d7450600f6f5cd7450600bef28d6450600faf58d64506009ff69c93506009ff6989350600bef28d4250600feb5894250600feb4c942506009ff69e994c6009ff696994c6009ff68c974c6009ff688974c600ef72a1634c600fb75d9634c600fb7591634c600fb7589634c600ff5285634c600dfb25c924c600bf7699324c600ff35 else 0x611c111bc11b711b211ad11a811a3119e118f118a11851180117b11761171116c11671162115d115811491144112b11261121111c11171108110310fe10f910f410e510e010d110cc10c710c210bd10b810b310ae10a9109a108b10861081107c10771072106d105e10591054104f104a10451040103b10361031102c10271022101d1018100910040fff0ffa0ff50ff00fe10fdc0faf0faa0fa50fa00f910f8c0f870f820f7d0f780f730f6e0f690f640f5f0f5a0f550f500f4b0f460f370f280f230f1e0f190f140f0f0f0a0f050f000efb0ef60ef10eec0ee70ee20edd0ece0ec90ec40ebf0eba0e790e380e1f0e100df70dde0dc50dac0d930d7a0d610d480d2f0d160cf30cc60ca30c800c5d0c3a0c170bf40bd10bae0b8b0b680b450b220b090af00ad70abe0aa50a820a690a500a410a280a0f09f609dd09c409ab0992097909600947092e091508f208cf08b6089d087a0861083e0825080207df07b2078507620753073a072b071206ef06cc06b306900677065e0645062c061305fa05e105c805af0596057d0564054b05320523050a04f104d804bf04a6048d0474045b04420429041003f703de03c503ac0393037a03610348032f031602fd02e402cb02b2029902800267024e0235021c01f901e001b30186016d0140011300fa00cd00a00087005a002d0000aff2a1945da00aff2a1935da00aff2a1935d600aff2a1925d600aff2a1915d600aff2a19359600aff2a19259600aff2a19159600aff2a1965ce00aff2a1955ce00aff2a1915ce00aff2a19758e00aff2a19058e00aff2a19754e00bbf6989754e00bef6909754e00bfb6889754e00bfd6849754e00bfe6809754e00aff2a19654e00b7f29d9654e00aff2a19154e00bef690985ca00aff2a1965ca00aff2a1955ca00aff2a1945ca00bf728d945ca00bbf698935ca00bdf694935ca00bef690935ca00bfd684935ca00bfe680935ca009ff2a5635ca009ff2a5535ca00aff2a1915ca00bef690915ca00aff2a19458a00aff2a19358a00aff2a29954a00aff2a19754a00aff2a19654a009ff2a57354a009ff2a56354a00aff2a19154a00aff2a1964ca00bef690974c6009ff2a5744c6009ff2a5644c6009ff2a5724c6009ff2a5524c600cff25c9859200cff24c98592009ffaa99720e00d7f5c99720e00aff6988720e009ffaa99620e009ff69d9620e00dbf5d99620e00dbf5899620e00ddf65d9520e00ddf6599520e009ff69d9220e009ff6999220e00dfb5c99220e009ff696995ce009ff68a995ce009ff688985ce00aff698985ce00cff658985ce00aff694985ce00cff654985ce00aff684985ce00cff644985ce00ddf549951ce00ddf545951ce00def645941ce009ff699921ce009ff695921ce00dfb589921ce00dfb549921ce00dfb485921ce00dfb481921c)) else (if i < 22 then (if i < 21 then 0x4294f294a294529362931292c29272922291d29182913290e290928fa28f528f028eb28e628e128dc28d728d228cd28c828b928aa289b28962891288c287d28782869285a285528462841283c283728282823281e28192814280f280027f127ec27e727e227dd27d827c927c427bf27ba27b527a627a1279c279727882783277e27792774276f2760275b275627512742273d27382733272e2729271a27152710270b2706270126fc26f726f226e326de26d926d426cf26ca26c526b626b126ac26a726982693268e26892684267f2670266b26522643263426252620261b26162611260c2607260225fd25f825e925da25d525d025c125b225a3259e25992594258f258a2585258025712562255d25582553254e25492544253f251c250d24fe24ef24ea24db24d624bd24b824a9249a248b248624772472246d246824592454244f244a24452440243b243624272422241d24182413240e240923fa23f523e623e123dc23d723d223cd23c823b923b423af23a02391238c237d236e2369235a2355235023412332232d23282319230a230522f622f122ec22dd22ce22c922c422bf22ba22ab22a6229722882283227e2279226a226522562251224c22472242223d22382233222e221f2210220b2206220121fc21f721f221e321de21d921d421cf21b621b121a2219d21982193218e21892184217f2170216b21662161215c215721522143213e2139213421252120211b21162111210c20f320e420df20d020cb20c620b720a820a32094208f208a2085206c205d204e20492044203f203a20352030202b20262021201c201720081fdb1fae1f8b1f721f311f0e1eeb1ec81e9b1e781e371e0a1ddd1da61d791d561d471d381d291d1a1d0b1cfc1ced1cd41cc51cac1c9d1c8e1c7f1c701c611c481c391c2a1c1b1c0c1bf31bda1bcb1bbc1ba31b941b851b761b671b581b3f1b261b171b081af91aea1adb1ac21ab31aa41a8b1a721a631a541a451a2c1a1d1a0e19ff19f019e119d219c319b419a51996198719781969195a194b193c19231914190518f618dd18ce18bf18b018a118921879186a185b184c183d182e181f1810180117f217e317d417c517b617a717981789177a176b175c174d17341725171616fd16ee16df16d016c116b216a3169416851676166716581649163a162b161c160d15fe15ef15e015d115b815a9159a158b1572156315541545153615271518150914f014e114d214c314b414a51496148714781469145a144b143c1423140a13fb13ec13dd13ce13bf13b013a113921383137413651356134713381329131a130b12fc12e312d412bb12b612a712a2129d12981293128412751270126b125c125712521243123e122f1220121b12161211120c1207120211fd11f811f311ee11e911e411df11da11d511d011cb11c else 0xa42db42cc42bd42a4428b427242634254423b4222420941fa41e141d241c341aa41914182417341644155413c412d411e4119410a40fb40ec40d340c440ab409c408d407e407940604051404c404740384033402440153ffc3fe33fca3fc53fc03fbb3fac3f933f7a3f573f523f433f343f253f203f1b3f163f073eee3ed53ebc3ea33e943e7b3e763e713e623e533e443e353e263e173e083df93dea3de53dd63dc73dc23db33d9a3d8b3d7c3d6d3d543d4f3d403d313d2c3d1d3d0e3cf53ce63cd73cd23cc33cb43caf3ca03c913c823c693c5a3c4b3c323c193c003bf13bd83bd33bce3bbf3bb03ba13b923b833b7e3b793b6a3b513b423b333b1a3b0b3b063b013afc3ae33ad43acf3ac03ab13aa23a933a843a6b3a523a433a343a253a1639fd39f839f339ee39df39c639ad3994398f398a397b396c3953394439353930392b391c390338f438e538e038d138c238b3389a388b387c386d385e384f384038313822381d380437eb37dc37c337b4379b37823773375a374b373c3723370a36f136d836bf36b036a13692368336743665364c3633362e362936243615360635ed35e835e335de35cf35b635a73598357f3570356135523543353435253516350734ee34d534c634b734943485347634673458343f343034213412340d33fe33ef33d633bd33a4338b338633813368334f334033313322330932fa32eb32dc32d732c832b932aa329b328c327d32643255323c3223321e321932143205320031fb31ec31e731d831c931c431b531a631a1319c318d31883183317431653160315b314c313d31383129311a31153110310b310630f730f230ed30e830e330de30d930d430cf30ca30bb30b630b130ac30a730983093308e30893084306b30663061305c305730523039302a301b300c300730022ffd2ff82ff32fee2fe92fda2fd52fd02fcb2fc62fc12fbc2fb72f942f852f762f672f622f5d2f442f3f2f302f212f122f032efe2ef92ef42eef2ee02edb2ecc2ec72eb82ea92ea42e9f2e9a2e8b2e7c2e6d2e5e2e3b2e362e312e222e1d2e0e2dff2df02deb2de62de12dd22dcd2dbe2db92daa2da52da02d9b2d962d872d822d732d642d5f2d502d412d3c2d372d322d2d2d282d232d1e2d192d142cfb2cec2cdd2cd82cc92cba2cb52ca62c972c882c792c742c6f2c562c472c382c292c242c152c062c012bf22be32bde2bd92bd42bcf2bca2bc52bb62bb12bac2ba72ba22b932b842b7f2b702b6b2b662b612b5c2b572b522b432b342b2f2b2a2b1b2b162b112b0c2afd2af82af32aee2ae92ae42adf2ad02ac12abc2ab72ab22aad2aa82aa32a9e2a8f2a8a2a852a762a712a6c2a672a582a532a442a3f2a302a212a1229ef29ea29e529e029d129cc29c729b829a9299a29952990298b297c29772972296d29682963295e2959295) else (if i < 23 then 0xa61c161b261a3618a617161626149613a61356126610d60f460e560cc60b360a4609f6086606d605e6045602c60135ffa5feb5fdc5fcd5fbe5faf5fa05f915f825f695f505f4b5f3c5f375f1e5f055ef65edd5ece5eb55ea65e8d5e745e655e4c5e3d5e2e5e1f5dfc5de35dca5db15d985d895d7a5d615d525d435d345d2f5d2a5d115d025cf35cee5cdf5cda5cc15ca85c8f5c8a5c855c805c7b5c765c715c6c5c675c585c495c445c355c265c175bfe5bef5be05bc75bc25bbd5bb85bb35ba45b955b7c5b635b545b455b365b275b185b095afa5af55af05aeb5adc5acd5abe5aaf5aa05a915a825a735a5a5a415a3c5a2d5a1e5a0559ec59e759d859c959ba59ab59a6598d597459655956593d5924590b58fc58ed58de58c558ac5893587a586b585c584d583e582f58205807580257e957da57cb57b257a3578a577b576c575d574e573f571c570356ea56e556d656c756c256b356a456955686567756725663565456455640563156225613560455f555dc55c355aa559b558c558755785569555a55415528550f550054f154e254c954ba54ab54925483546a54515442543354245415540653f753f253e353d453bb53ac539d538e537f53705361535c534d533e53255320531b530252fd52e452d552c652c152b252a3529e5299528a5285526c525d52445235522652215212520351f451e551d651c751b851a9519a51955190518151685163514a513b512c511d510e510950fa50eb50dc50cd50c850b950b450a55096508750785069505a504150325023501450054fec4fd34fce4fbf4fba4fb54fb04fab4fa64fa14f9c4f974f924f8d4f7e4f794f744f6f4f6a4f654f564f514f4c4f334f2e4f1f4f104f014ef24eed4ee84ee34ed44ec54eac4e9d4e8e4e7f4e704e614e524e434e344e254e0c4dfd4dee4dd54dc64dad4d944d854d764d674d584d494d444d354d1c4d174d084cf94cea4cdb4cc24cb34cae4ca94c9a4c814c724c634c5e4c454c404c3b4c364c274c184c094c044bf54be64bcd4bc84bb94baa4b914b824b734b6e4b694b5a4b4b4b324b194b0a4afb4ae24ac94aba4aab4a9c4a8d4a7e4a6f4a604a514a424a334a244a0b49fc49ed49de49d949ca49bb49ac499d498e49754970496b4952494d493e492f4920491b4916490748f848f348e448d548c648b748a8488f4876486748584849483a482b481c4817480847ef47e047d147c247a9479a47814772475947544745474047274718470946f046e146d246b946a0469146824669465046374632462d461e460545f645e745d845bf45a6458d457445654556454745384529451a450b44fc44ed44e844d944ca44bb44ac449d448e447f44664457444844394434442f442a442544204411440243e943d043cb43b243a3438a43714358433f43304321430842f942e else 0x68a0789f889f389e489d589b2898f8980897b897689678958895389448935893089218912890388ea88e588d688c788c288b388a4888b88728863884a88458840883188228813880487f587d287c387aa87918778875f8750874187328723871486f186e286d386c486b5869286838674865b864c863d862e861f860685f785de85cf85b685a7858e857f856685578534852584ee84df84c684b784a88499846c84498426841783ea83db83ae83a9837c836d834a8327831882ff82f082e182c882b982aa829b828c825f823c8219820a81dd81ce81a18192816f816a8147812e811f810680f780e880d980c080b180a2809380708057802a801b7fee7fc17fb27fa37f947f857f6c7f5d7f4e7f2b7f1c7ef97eea7ec77eb87ea97e907e6d7e4a7e1d7e047dd77dbe7d9b7d827d4b7d327d197cec7cd37cc47ca17c927c797c607c477c2e7c1f7c107c017bf27be37bc07bb17b8e7b7f7b527b437b2a7b117af87ad57ac67aa37a8a7a677a587a497a2679f979ea79c779b8799579867963794a793179227909790478f578f078d778c878b9789678877864785578327823780077f177d877bf779c778d776a775b77387729770676f776e876cf76c0769d768e767f76707661763e761175ee75c1759e758f75767567753a7517750874ef74e074c774b874a9749a748b747274637454743b742c741d740e740973fa73f573e673d773d273c373b473af73aa73877378735f7350734173327319730072dd72ce72ab72887251721a720171f271cf71a2717f7166714d712a70fd70d07099704e701770086ff96fea6fd16fb86f956f7c6f596f366f096efa6ecd6ebe6e9b6e8c6e736e5a6e4b6e286e196e006ddd6dba6dab6d9c6d8d6d7e6d6f6d566d3d6d246d1f6d066cf76cf26ced6ce86ccf6cac6c936c666c436c2a6bfd6be46bcb6ba86b996b766b536b3a6b176b086b036afe6aef6ae06ad16ac26ab36a9a6a8b6a866a776a686a596a546a4f6a406a316a186a0969f069eb69dc69c369b469a569a069916978695f6950694b693c693769286923691e6919690a68f168e268d368c468b568b068a1689268836874686f686a685b68566851684c68476838682968246815680667f767f267ed67de67d967ca67bb67ac679d678e677f67706761675c67576752674367346725671666fd66ee66d566bc66ad669e6685667666676662665366446635662666176612660365ea65db65cc65bd65ae65a965a4659565866577657265636554654f654a653b652c6513650464ff64fa64eb64e664cd64be64b964aa649b648c647d646464556446643764286419640a63fb63f663dd63d863d363b0639763926379636a635b6356635163386315630662ed62de62cf62c062bb62ac62936284627562666257625262436234622562206211620261e961d))) else (if i < 28 then (if i < 26 then (if i < 25 then 0x8bd6fbd56bd3dbd24bd0bbcfcbcd9bccabcb1bc98bc89bc70bc57bc3ebc25bc16bbfdbbe4bbcbbbb2bba3bb8abb71bb58bb3fbb26bb0dbaf4badbbac2baa9ba86ba6dba54ba3bba22ba09b9f0b9d7b9beb9a5b98cb973b950b937b91eb8fbb8e2b8d3b8c4b8a1b888b86fb856b83db824b815b7fcb7e3b7cab7b1b798b77fb766b74db734b71bb702b6f3b6dab6c1b6a8b68fb676b65db644b62bb612b5f9b5e0b5bdb5a4b58bb572b559b540b527b50eb4f5b4f0b4d7b4beb4a5b48cb473b464b44bb432b419b400b3e7b3ceb3b5b39cb383b36ab351b338b31fb310b2edb2d4b2bbb298b27fb266b24db234b21bb20cb1f3b1dab1c1b1a8b18fb176b15db14eb12bb112b0f9b0e0b0bdb0aeb095b07cb063b04ab031b018afffafe6afcdafb4af9baf82af69af46af2daf1eaf05aeecaed3aebaaea1ae92ae79ae56ae51ae2eae0bade8adc5adacad93ad7aad61ad3ead25ad0cad07aceeacd5acbcaca3ac8aac67ac4eac49ac30ac2bac12abf9abe0abbdaba4ab8bab72ab59ab40ab1daafaaae1aac8aaafaa96aa7daa64aa4baa32aa19aa00a9e7a9cea9b5a99ca983a96aa951a938a91fa906a8eda8d4a8bba8a2a889a870a857a834a81ba802a7e9a7d0a7b7a794a77ba762a749a726a70da708a703a6eaa6d1a6c2a6a9a69aa681a672a663a654a63ba62ca613a5faa5eba5c8a5afa5a0a587a56ea555a546a52da514a505a4f6a4dda4cea4b5a49ca483a46aa451a438a41fa406a3eda3caa3a7a3a2a389a384a375a370a357a33ea325a30ca2fda2e4a2dfa2daa2a3a280a267a24ea22ba212a1efa1c2a1b3a1a4a181a168a14fa12ca113a0f0a0e1a0c8a0afa096a07da064a041a01e9ffb9fd89fb59f929f6f9f4c9f299f069ee39ec09e9d9e7a9e4d9e2a9e079de49dc19db29d999d809d719d4e9d3f9d129cf99cd69cb39c7c9c459c229c099bf09be19baa9b919b829b699b469b239ae29ab59a9c9a8d9a7e9a479a2e99ed99de99c599849957992098f398d098c1989498679858981797ea97c797ae979f977c976d975e9745972c971396e696af969696739664964b9632960f95ec95d395ba95a19588955b95429529951094d994c094b19498947f94709457943e942593ee93df93c69399936c93499330932b92fe92db92c292b392ae92a9929092639236921391fa91eb91be91a59182916991509119910090d390b09097906090338fe88fcf8fb68f898f708f618f348f118ee48ec18e9e8e858e6c8e538e3a8e218e1c8e0d8df48ddb8dc28da98d868d778d688d638d4a8d3b8d228cff8ce68cd78cc88cb98caa8c9b8c8c8c738c648c4b8c328c2d8c148c058bec8bdd8bce8bbf8b9c8b8d8b888b798b748b6f8b608b518b428b338b248b018afc8aed8ade8acf8ac08ab18aa28a938a848a7f8a708a618a528a438a348a258a1 else 0xc81000000000000000000034840000012f93c00c41e03cc0f7c9a40441882a6e007b10401e00691700348b801605c00d22e00691700348b801a45c00d22f005817803d880c1ec581887c00f62c13c01ec581f803d8b03f007b1606060f62c0f801ec5818183d8b03e007b1607c00f62c0f801ec5818183d8b03e007b1607c00f62c0f801ec5c00f62e007b17003d8bc01605c00f62c0c12f005e00b02d203c00b02e005817002c0b801605c00d22e00691700348b801605c00b02e005817002c0b801605c00f62c0f80160691f802c08020805c00e8348f80160464701e00f801ec5c00f62c0fc0158691f003a0ac3493801d0561a49c00ac348fc00802500b8009403489c0f02181b81e04303792181381e043037022014362c0a1b1605100d22880691381100a201a45100d22880691440348a201a45100d22703c01381e009e40f802c0bc01605e00b02703c014362c0a1b1604e04402e005817003d8b801ec5c00f62e005817002c0b801605c00b02e007b17003d8b801ec5c00b02e005817002c09c0e004e07002e005817002c0b801604e07002703801700348b801605c00b02e00581a47c00d22702c0d0380238160681c013402804e0581a07004702c0d038027002c09c0b0340e008e0581a07004e0069138160681c011c0b0340e008e0581a07004d642d629d610d5f7d5ded5c5d5acd593d57ad56bd552d539d52ad511d4f8d4dfd4c6d4add494d47bd462d449d430d417d408d3efd3d6d3bdd3a4d38bd372d359d32cd2ffd2e6d2cdd2bed2a5d28cd273d25ad241d228d20fd1f6d1ddd1bad1a1d17ed165d14cd133d124d10bd0f2d0d9d0c0d0b1d0a2d07fd070d057d03ed025d00ccff3cfdacfc1cfbccfadcfa8cf8fcf76cf5dcf44cf2bcf12cef9cee0cebdce9ace81ce68ce4fce4ace31ce18ce09cdf0cdebcdc8cdb9cdb4cda5cd96cd7dcd6ecd55cd3ccd23cd0accfbcce2ccc9ccb0ccabcc92cc79cc60cc51cc38cc1fcbfccbedcbd4cbbbcba2cb7fcb66cb4dcb34cb1bcb02cafdcaeecadfcac6caadca94ca7bca58ca3fca30ca21ca08c9efc9d6c9bdc99ac98bc986c959c940c931c918c8ffc8fac8e1c8c8c8afc896c887c86ec869c850c841c828c819c800c7e7c7e2c7c9c7b0c78dc774c75bc74cc73dc738c71fc706c6edc6d4c6bbc6acc693c670c657c63ec61bc602c5dfc5c6c5adc594c57bc562c55dc544c52bc512c4f9c4f4c4e5c4d6c4c7c4aec49fc486c46dc454c43bc422c409c3f0c3d7c3c8c3afc396c37dc364c34bc328c305c2f6c2ddc2c4c2abc292c26fc256c23dc210c1f7c1dec1bbc198c16bc152c139c120c107c0eec0d5c0bcc099c080c067c058c035c01cc003bfeabfd1bfb8bfa9bf9abf81bf68bf59bf4abf31bf18beffbee6becdbeb4be9bbe82be69be50be37be1ebe05bdecbdc9bdb0bd97bd8) else (if i < 27 then 0x136822b04510800000a2100a210190116020000e40990132027204813905818006d0406404da0990100002b04072040640400002e4080e40990100a21944200000000000144e41190139020390210040720456099013682001c86408560990132020390364040640456080000000720400000e40990101b4100000001e40aa21001c8080003442000000010212042000000000e408006404000102101c8101c8132027204813904e180003202001901320268840001a2100000000000000720400000000000688400000000000039026404e408000368203902640406d040001c810000001c81320200000039020000072040001b410000003c810000f20400000068840000000001e4080000000408400010210000001c8101363488da09c81390200000000000390272040034426d048108000000001383240400000000102270d2313822704e40804e0804e26c40138227044e080da080001382000000000e408000000172040720400000003902001c81368203902270406d040039023484001a42720402404003902270400000e40804e089c1000024040f20400000000008109b4100000000810800001403488021840000000039010000000043080002042000000204691190101c81000c809b410190100003492423442688400000000000001a210b5e40601e23c80aa121790da8601e185a1b0b010d8304481e860c0aa121b0c368601e185e0a8203745e442436203c0a82030bc2d4041f05618305af203e0a902d7901805481a038f203e0a941c831250548f2060108f800f001e003c007800f001e00212f002e003c03902e003c007800f001e00200f002e003c007800f001e01e41700e40b800f0010078017001e003c007800f001e01c81700f20b800f001e003c007800803c00b800f001e01e41191c00bc00f801f003e01b42f003e007c00f801f003e007c00f801f003e007c00f801f003e007c00f801f01e417801f003e007c07205e007c00c021804300860172050086010f801e0023c078008f01e003e0044e0f001e003c0044e0f001e003c007800f801f003c03c82e003c007807205c00780089c1e0023c078008f01e003e007c00f001e003c0044e0f001e003c007800f801f003c03c82e003c007800991c00b800f001f003e007800f801e003c039021383c007800f0011383c007800f001e003e007c00f001e00da1780f20bc00f001e003e007800f001f003c007800f0011383c007800f001f003c007800f801e01e417001e01c81002008000039013682001a21000d1081e409a2100000000000000000000000000000000069080000000000000368205209b1000003c81000003682034420000000000f204d1080000000f20400000000000000000790200000079020791da745c82000079020000000000000000000c80b else 0x4c08981130226040000981f002327002f003c007800f001e003c007c00f801f003e00022f003e007c01205e007c01905e00902f003c007800f001e0020e003e00a2207801f003e007c00f80008bc008002406011ac5c007800838012040003800f00192020e003c0078012040f003e007c00045c007800801e006640f00240848e005c007800f00240b801205e007800f801e003c007800f001e003e007c00f801f000117801e003e0041c007800f001e003c00780120400099c0081e007800c901003c00f80104b41e003c007800f001e00481700240bc00f801f003e007800f801070011338017001e003e0044ce005c007801305c0044ce0040f002016b8017001e003c00982e003c007c01445c00a22e003c007801204267002123801001e00464e005c007c00f001e004810b1c00848e005c00902e003c007c00f801f003e007c00f001f0020e003c007c00f001e003e007800f00358b800f001e002000000f00235846be00435f002070026084c0899c00851e00428f8021478017001e003c00902f003e007c00f801f00221f80210fc01087e00bc00f801f00691780240bc01205e00443f0052407c00887e00bc01905e007c00f801f003c00b42e003c0041c007800f801f006417801f004817801e003c004000f0020102007801078011ac235f002e005110a3c008000780110f80170028885119380183800f001e0020003c00887c00843e004247002e005117001147801001e007c00f801f003e007800f001e003c0041c00780083c00f80320bc00f801f003e0090207801f0020e003e007801a45c00780083800f00107001f003c00448e005c007c00f00348b80120435f002e002247002003c00f801f003e007c00801e00464e005c0078008d3c00b80080005914810981029015202a407800f801e01e41700270b800f001e003e0078079040003c00887c00848e004247002003c00898113b8017001e0020078011338017001e0020f003c0044c089dc00b800f001f003e007c00f001f003e004021f00210f801700110f801700110f801087c00b800f80218b800f00110fc01087c00843e00421f00210f8010b41f003c007800f001e00221f00210f8010000e003c00443e0040003c00f80320bc00f801f000117001f0033207800f001e003c007c00f0032084ce005c007c00f00320983e003c007800f801e006417001e003c0041c0078008c9c00864e0043270021938010002670021338017801e003240448e005e007c00f80107801f003c007800f001e003c00902f00235f002147801000032020008610086110c2014422184001a420019013202000861b20203202218400000e4080000000000151080000190100000144e410000000e408046d04e409c81000000001090400000000102720ac315827204e408002b040200ac)) else (if i < 30 then (if i < 29 then 0x288301e02c8e0040c7900b0a08e00400008281b8010a82814180589c0085017816370020b82a20d0180546060360a8f400e801d003a007400e804d08a4d0044668020157a00891080000700b10060804430400b10340c8520590380600b1b810408220203b02c8e04102702081000010323700208066110c260cc0b18040508180ec19180c1002010c021e003e004020f00100b80083800f00105c2000041944221f002d443c00b4207001e01da17001e0020e003c03902e010114a2100b0102b41000006845ae0050087800f001e002080420904120ea2100151080000240112020d442a887510800a88408085010ea21e003c0041b0f00180420000060f8014043008401e005008401e00500f0024043008409e004808601083800f001e003008780080090803c00b80084a102421284005903c007800800908121001640f001e0064170010038008001e00404841e004020cb41e00221f002e003c007800f001568201078008043e004007002d0983e004310043e004ad05010801c00402e005110c728878014452887800f00104a2110f8017001e002320780080090c021820200c03008425e00500841be0050086010f0004886be004808448e005c00400e0401e0042d70028043c001221201b170010003c00851e005008780024428f002123801013c00b800f00106c3c0041208121e003c007807905008862040210003c00843e005008401e005008401e0050087800244808522024224700280420104020f003d8b03e005814a3240b801205c00b0292022c07801605c007800f001003801ec5c00780083800838014450089025915a100000000002a2101020804209078008a3c008120c021545481000007001e00200f00200780104a1e0020487800f001024204840007801f003e007c00f801f003e007c00f80320bc012040f003e007c07905e00c8207801f003e007c00804cf004247802f003e0044cf004267802123c017801f003e0044cf004267802123c01087e0085a0f801f003e007c00f801133c0103c00045e007c00899e00bc00f80320bc00f801f003e007c00899e03c83133c01091e0081e00780083800f001f003e007c0083c00f801e002000820387c00f0011582267002133801087c009810f00107001e00227044ce00426700210f8013021e003c007c01305c007800899e00bc00899c00848e005c004430b021f003c00780083800f001e006417801f003e007c00f801e0020e003c007807904007802d081c00b42e0022d041e007c00801e00402d7802e0022d7002e003c0041e007c00f801f003c007c00f001e003c00400f00235f0020700260bc00f001e003e0041e007c00f801f0020f0020f003e007800f001e003c007801905e007c00f801f0022d700210f80100810800000000000026040000002604002044c1 else 0x583b02c61501a8903c4b9320028606020058d0302c400f002007801003c00851e0040e002207802e00511700288b801ac400f01a88f800f0010081e00b800803c00b8010c011f00090b80080410243c00402081210078010121007801003c0080207802e00200f002e003c007800f00260023e0020f002007001e003c007800f001e004c1ac60f003e007c00f801f003e007c00f80107801f003e007800f8012043c007800f001070010243c0098358f801306b1f001003800f00107001e0020f003e007c00f8026080020780083800f001e004c1700218b800891c00800e003e007c00f801f003c00d6260f800f80240b801385c00902e006917801f003e007c00b801070300546e005c00b801700217820108dc00a2411d3c0178014483e007c00f80100a510f80288a510f80288a510803e00a51082a1109c008180f0423700215044020041815c0080c0589c0080417003260700804440eda905c6080680b8dc008563db520b91c00856c435211100cd0181c82e47002c40760b8c39088101f001e01da17001e00268f002e003c007800b8016680c0e41720201d82e30403405c6e0040e1ec3905c8e005a4160100d48e004880e5a01800e0ec171872080b800f00ed0b800f001e003c03a22e003c005c00b101d82e30400b13480b86a0591c00b48c406e0590070303b05c8e007800f001e003c03a22e003c00458054351b801061a90d47c0059a0e4171b801e0020302e20e4100846088720f8c240440a0d88e04182880320242a238106082f07c151b8006082a010368801f2b8106080602c4150341b02a47020c100410d00a05c6e0042205440101e27001110320b89c00b80100420084010876098603700206024150dc00854189400f11c008440a88300784e00222004300646e004080c41e180c05882a0780b1b8010082088720f8c240440a0d88e0040c0483a1b8010041f0c46e0042e0ea1b180c05883a02c4e007c016040f002001c1513801008212046058dc0085611816370021486e058dc008561185037002013b4201c101048100163700215840058dc008500e016370021102a058dc00b80104028138010a01002c6e004020804170021383c0b8c2f0a81f0548d2046050c2a078300548d5846050dc0082a0509c00934dc0300511b807c141b8010181717001e00da17001e003c007800f00e88b800f001e005a11021e00240841c0041c004810838009021000240dc0a1b80102c14138010042e005c00ac42881e20ac518806e004ccb20221e362881e30231b4140b494a28810058b109142c0c04e00400008361858014301510110242a18181508000e841c0300f0c240440a0bc808c400487440e806494180d8a168501b03c0741c101c030a8368601e2d801b002e004180d840d86c28603607860301620902002c615840058c) else (if i < 31 then 0x8440842b0084160042008221004068881008412842c0084012c8140c006804060c028302a1808014183011c8040602020205422102e010817008402004f20c0400840200420410010a0806c40105420082210041108027900b1804058801583e2005401080d0084068042009e402c60200420101f100e010807008403804208807008603805098c07008403860200828100e010807008403804201c021038140802088401050280c021004130a0306c501824202c30100405880b07040a81626041e13020308270784c080c26042313020a898105440b83c26040613020334836041e130218080609c403014201402100a02004301402100a0108050084010140a0c050084000440a880b0184ed06241ec414860c06c506060c081c1831c8105618ac1210a215882e09981a85c37202b1456133a2b120203082b79041d062b42448080c28ac2030458820504045882042c41020a82d100813080407440180820940210040288340e841abb4010c053900218004070407202001006100c14080401841403c20182150502000177921101c0628040bc22301c13100e09882201c15181a080807042081820ed4100110d109a2101c15088601820200805100a020043008051074030423e0020b82a20180a15020a8a8105440101620d1a905c60f8720b8c1f0e417183e1c82e307c3905c60f8720b8c0c0080b18701181630403b05c6080760b8c346a417183e1c82e307c3905c6080760b8f0e1d039c80987072110c1f0e72018701181631691b0547c0041705441102a2e0020f8720b8f800855a406c0a9281054411004180f3404017183f9581d9482e5d233403b2905cb9a030140c170544030142e00216038068d20a97c010c5c004060285a400c0a0c660282118581501206e900a982a0351b0549c00b42e003c0042c0a81c1601528440f0aabc2058ca42205cdc00422054416f49840202c64060b79a04017203e16e119482e50b79a0602820a28903c3e002150381882a40a81c0c015270010b00e0700dd20153058151360a901f0e417180c050b8008500101630a03c0040602840a8282e005110500e06605902ee939ac580b2804058838040221f0010080b10040588280400b1870118163e02d1170004880202840101420a81c0c015200c05080602840101420b02a00c1f054a030142e0020101420080b170010080b100405880202c40f85bd2030051780080407882a010300848877341c82e400c0602870082a2005406a240f12e40840a1804058b8008001a82a20a8040c02121981c02011102c46c15182e18880f085406a360a901502c40182a110c1002c40a81420a80102d200c4a1c81620302a4601e20548c03c30b0351055a40088d8645033030ec17205815e90050501024070341710720588280201002c802014201c2150608d82a4 else (if i < 32 then 0x100201080107c45482e26041f0706c0820030c8800440b820205c1010001008400854200420690220448128043d90200e03b206644904030401008400804200419101a408a0c09064089c88304008042006a0f89e4018400804246c2008042036a410d7409703d6820080c2c04321002030801009a418020108010bc4008042008011148408804d860808444908300884419022790071004d202e305c1f12521c2020300e200801100201080205c5b201c920c30082291208c0a082445220a4203014280c48100010084008042004021436408a080c364088041902201c20080424202008042004021000100840086020040269060bc1c2c070812361968200c40e100203080601c5018902133081098105c301004d202e30a12910c9148a291202818b0148a290380918020308010084008042004021002010800080420040210020108020d4401ac235840e08990708150802030a03120405804201c02100e01080201c40b83e28041e103c10041e10020f080205c403118240c0610981a05e3c040649860f052601851480c20041510020a8b01040151e020a885104043204c1402a40041510020a8b01040151e020a0523c042902c15200201080100840080c20041011480308b80a040a85021a4290a0603548204007100c11200e02c60a8162058331002030801008400804201820a84430c0400804201820a840107840f04e26041e104e0f09810784c080c20043010020f08430c0400804205d0e100218080a07c41403c2190290a060b8602004061202109429102e07084882040b812200402101210040d89068084e4890472052240420082a203422102e1c080d088480841504842b070239224102a090830099104080105440082a23202911c814881504840a82421580e10020a8801054400855840c174a441505220060811c81488010c041d80423903a1004150826008472008201002100c1505030042a100206880c05c3818020689010802113838830672448200410100216880101840b81c240420080c23220811c814880101840080c201805102e070801018403804204022100e0108da080e01080700840804420342f14221c082200841100424041c1202010925070480804240402c04680bc824041c120218090100840324a240406100c848901018408300214180d880203440683620a8021004100822100e1808040084c0846205c1f13020f89810d04c085a2605a4102e0f89810c04c0b5226041f13021605e40e46c0b4c26059a1302e40203604101348c089886044c1b02260430130216041f10641a89816904c085a2605a4102e0f89810404c08581790391b02d309816684c0b222321810406c0840e6044d2302260d81130216881707c4c08602604a913020f888100840b8382204301102010881070440b90030c8101 else 0x49048c204446102222081110640888c204440852220426101a40889b090640880d204440840d20458d83e2c6c1f16360f880707c48d838203481101b520883204540e90229081113610c09215241808170c040b860205c30100e1808170c04010981ac524130220d41f21064088050c0449048c204404836246c81123640880107c40083e220c81101a408822040401044038c01008411020058c10024509044200812105c100830100415080100840080420082010501c04021bc810043010020108020c0400804200419100201080d2044026c2020c8113c8e4081707c4c080c205c1)))))) else 0
def signed9Level : Packing := (3075,4,6,0,0,16,0,signed9Data)
def signed8Data (i : Nat) : Nat := if i < 7 then (if i < 3 then (if i < 1 then 0x333d3334a49a83006772116949350600cbd4eed153298c019ba999a2a65318033b52ab454ca630067aa4468a994c600cf9466d153298c019f8845a2a65318023dd5db484ba630065b973690974c600cf3466d212e98c019ea889a425d318033d908b484ba630047f2bb2a5714c6008ef576d293018c0195e9dda5260318023bd5db4a49a4300657a7769493486009f3576d213119c01ba6999a4262338037c5113484c467006f9211690988ce00cbd4ee54b07114019ba998a960e228033f108952c1c450047eabb2a53188a00cbd4ee54a63114019ba998a94c6228033b52a95298c450067aa442a53188a00cf946654a63114019f8844a94c6228036e93b946cc42300617eaa9dd9520e00c4fd553332a41c01c1f9de66654838031bb55422ca907007176778459520e00e4eccd08b2a41c019b6aaa336583080337555444cb0610066daaa9999304200cf955511326084019f4aaa1164c108032bd554eeca90700667aaa9999520e00e8f4ef3332a41c019ceaaa4465483803a9d3bc88ca90700763a669119520e00ceb55519b2a41c01d569de3365483803b2d33466ca90700676aaa8899520e00ead4ef1132a41c01d9a99a22654838033b955422ca907007572778459520e00ece4cd08b2a41c01dcc9121165483803ba919c22ca907007762228459520e00e3b4ef19b3039c01c7a9de226607380397533444cc0e70073d233845981ce00e7c44508b3039c0196eaaa776507380335d554ccca0e700673aaa955941ce00ab7576b9b2839c01d2e9997365073803a9d2aae6ca0e700759a778cd941ce00ed34cd19b2839c01dc69563365073803ad53bc44ca0e70076aa66889941ce00ee54ab1132839c0197aaaa7764873803375554ccc90e700676aaa955921ce00eb54ef2232439c01daa99a4464873803b952ac88c90e70055eabb5cd921ce00e9d4ccb9b2439c01d5a9557364873803ae53bc66c90e70076ca668cd921ce00ee94ab19b2439c019f8aaa1164873803af13bc22c90e70076e266845921ce00eec4ab08b2439c01de89121164873803af0b9c22c90e70077c233845921ce00cf65552232239c01dcc95644644738033e955466c88e70075d2778cd911ce00eea4ab19b2239c019f8aaa2264473803af13bc44c88e70076e266889911ce00eec4ab1132239c0195eaaa776543180333d554ccca86300673aaa911950c600ea74ef2232a18c01d8e99a44654318033ad55466ca86300765a668cd950c600ced5551132a18c01d5a9de22654318033b955422ca86300757277845950c600ee648908b2a18c01dd48ce1165431803f15334ab22445007e4a669563388a00fd14cd2246711401fc2956448ce22803ed13bc8911423007f22559122284600fb84ef19c4508c01fb099a3388a11803fa12ac6711423007f82448ce2284600 else (if i < 2 then 0xcf5444d212ec1c019ec845a425d838033d908b484c0e70067e211688981ce008fe576d093039c01cec84598650738039f108b30c90e70076e211659921ce00eec422cab2439c01de884594648738031f955330c88e70067b2aa651911ce00cfc554c932239c0199e615a625d5380333caa34c4baa70066ba446989754e00cdb466d312ea9c019ba889a625d5380327cb8b4c4baa7006679516989754e008f7576d212ea9c0196e5cda425d538033cd19b484baa70067aa226909754e008fd576d112ea9c019ea911a225d538032f4b9b444baa70067ca336889754e00cbd2e2d112ea9c019da545a225d538023f95db424baa70067b2446849754e00cfa466d092ea9c019f8889a125d538023bd5d952c2aa700657a772a58554e00ccf4cc54b0aa9c019dc844a96155380335d333484c46700673a55690988ce00cf5444d213119c011deaeda524d828032bd3bb4a49b0500667a666949360a00cee422d2926c14011eeaeda4261728032dd3bb484c2e50066ba66690985ca00ce74aad2130b94019e68cda4261728033d908b484c2e50046fabb698935ca00c9f4eed3126b940199e955a624d7280336cb9b4c49ae50066f211698935ca008ef576d2926b940195e9dda524d7280333d3334a49ae500675973694935ca00cee422d2926b940196e9dda424d7280335d3334849ae500673a55690935ca00cf52c4d2126b94019ec845a424d728023f95db4249ae50065f277684935ca00cde4ccd0926b94019dc955a124d728033f0b134249ae50047babb690915ca00cb74eed2122b94019ce955a4245728023dd5db4848ac500673a556909158a00cd72c6d2122b14011f6aeda3245628033ad2ab4648ac500679a4468c9158a00cf92e4d1922b14019f2509a3245628033e8a0b4648ac50065da7728d9750a00cdb4cc51b2ea14019d6954a365d428033ccc2146cba850067995428d9750a00cf92c451b2ea14019e6504a365d428033e908946cba850045fabb69c9350a00c9f4ccd3926a140195e955a724d428032dcc234e49a850065b95469c9350a00cbb2c6d3926a140197654da724d428032f4b134e49a850065b94169c9350a00cbe422d3926a14011beaeda624d4280327d3bb4c49a8500667a556989350a00cd7282d3126a14011deaeda524d428032bd3bb4a49a8500667a666949350a00cee422d2926a14011fcaeda124d428032f93bb4249a850066f2666849350a00cee4aad0926a14019f458da124d428033f0b134249a850067e2112a5724ca008ef576d2922994019da5c9a5245328023bd5db4a49b0300657a776949360600ccf4ccd2926c0c019dc845a524d818021fd5d950caa830063da332a19550600c7d4445432aa0c018fc844a8655418023dd5d952ba28300679a332a574506008ef576d2926a0c0195e9dda524d4180 else 0x23dcda150cbc670047b9b42a1928ce008ef36a54532b94017366d8935cd72802eacda926b9ae50047f1b12a29958a009dd174b1ae4b1401f325cd635c962803ea4b9aa6b92a50047d9b3aa99750a008f7174cbb08a1401dc65515324d42803f14b2aa8b12850076c89358d6250a008f736854532994017f06c4a35c9328023f4d9554c9903005fa0b158942506008f73685453298c011fa6c8a8a65318023f4d9554cba630047e9b2aa9954c6008fd3655532898c010fe2e1a565131802bd4da12e49263007dc1724c9714c600bf2166ba28298c01fa45916350531803fc0a1264a0a630047d9b9aa9310c6008fe3735526218c011be6daaa65d218021fc5c34aca243007ec16358931486009f3174ca30919c01ce626194612338027ccda150c9467004f99b42a5818ce009f33685490319c011fa2e5a3206228023f45cb4e98c450047e8b96993188a008fd172d2a63114011fa2e5a44c6228027b8da95241c230063f1a96a07384600a4fb6c53b2a41c014cf6d0a7654838029b6d914eca907005375b129d9520e00a6f36053b2a41c014cf6d071654838029aed98e2ca9070056b9b41c5960c2008f737439b28084015ae6d87365010802b9cda8e6ca0210057a9b21cd9404200af636239b28084015b66d8a764c10802bacda94ec9821005799b429d9304200af936453b26084015f46c4a764c108023f4dd0e6c90210056e9b61cd9204200aed36a39b24084015ea6d07364810802bf0d88e6c9021005679b629d9520e00ae736853b2a41c015da6c8a765483802bb8d894eca907005739b421d9520e00aeb36643b2a41c015d66cc71654838029bcdc14eca863005679b629d950c600ae736853b2a18c015da6c8a765431802b9cda10eca8630062be66690988ce00c75c44d213119c010efaeda4261728030df3bb484c2e50062be66690985ca00c67caad2130b94018e78cda4261728031db08b484c2e50047eabb688974c200cf5488d112e9840197a5cda225d308023dd5d953222610066ba662a6444c200cf544454c88984011deaeda52453080339d2234a48a6100675a33694914c200cf648850b2c904019f85c8a1659208033f0a1142cb2410046fabb6989348200ccf4aad31269040117eaeda7245208032bd2ab4e48a410065ba4469c9148200ccf4aad3122904019ae911a624520803374b934c48a410066e9426989148200cde2e2d3122904011deaeda52452080339d2234a48a41006769726949148200cee2e2d2922904011eeaeda42452080339d2ab4848a410047dabb68c9148200ceb4aad1922904019e6911a3245208033e4b934648a410067c94268c9148200cfa2e2d1922904011deaeda524d848032bd3bb4a49b0900667a666949361200cee422d2926c24011eeaeda425d838032dcb9b484bb0700679a336909760e0)) else (if i < 5 then (if i < 4 then 0xc6facad2930b94018ef699a4261728038f6b9ae44c2a50071ed715c89854a00c6fb46a8930a9401cdb5c951261528031bea9b4a4c2e300637d53694984c600e76ae8a093098c01ccf5d184654318031f6b93444c4230071ed326497121e00c6f972d32a6c2c01a5f2dda654d858035ce98946ba30900799d635cd7461200d37ae6d3a84c24012ef6dca3509848035ceb1946a1309006bada75894261200d75946b1284c2401eab58d62509848035d6d3a64a1309005badb64c94261200a6fd76b2b2a41c018df69d65654838029bedb2a2ca90700735d975455320e00e37ae6ba32840c01e6d5cd74504818029bedb14eca90700537ebb6999520e00c6fb4ed332a41c018df699a1654838029bedb142ca90700537db61c59520e00a6fd76b0b2a41c014df6e961654838039bab8ac2ca90700637d63694989de00c6fb6ed2930b1c018df9dda5261638031beba34a4c2c700637db36949858e00c6fae6d2930b1c018df1cda5261638031bf19b4a4c2c700637db26949858e00c6fae4d2930b1c018df5c5a5261638031deb13484c4670063bd52690988ce00c77ae2d213119c018ef585a4262338031de90b484c4670063bd76690985ca00c77aead2130b94018ef595a4261728031deb8b484c2e50063bd61690985ca0086fb6a54532b94010ef6d0a8a65328021f6d91514ca63004f71b5285304420086fb6a54ceec24010df6d4a958d848021deda152b93070043bdb42a5726060097e36050ac4c0c011fa6c8a95d1308027acda946b9261004f99b428d724c2009fa36251ae4984011de6d4a9505308023dcda152c2c670047b9b42a5855ca008f736854b06b94011be6d8a954d728023dcda152a9ae50047b9b42a633606008f736854ae4c0c011de6d4a958d418023dcda152b926300533db421d9520e00a6bb6643b2a41c015ec6d0a064473802bf0d9140c88e7005579b7281950c600acf36c5032a18c015ce6d0a065431802bb4d9140ca863004778ba5c1950c600975b6451ae8c24012ee6c0a35d1848021de5cb4ea1309004b9cb369d4261200937b6e51a84c24012ee6c0a3509848021deda554c81070043edb2aa99320600af53644b928984015ce6d491251308029dc5cae8c22610047b8ba65e444c200d73348c2466984011de2e997955208023dc5d488c9a41004f69b528d72482009f536851ae4904013f86c4a35c9208025f45d306b9241004fc8b369d42482009bd36e51a84904013da6d4a3509208027f0d8946a12410075e1725c491482009ed36a51a42904011ee2ea4464d108023f45d327112210056d9b61cd9304200aeb36a39b26084015e66d07364c10802be4d90e6c98210047b9b42a2995ce008fb373552e639c011ee6d0a8a6553802b9c5cae8aa2a7005d99b425d7354e00bb93644bae6a9c01f465d1545cd538 else 0x802daeda950b9aa7004eecba58d7258a00f99ae6b1ae4b1401f535cd535c952803b6649ac6b12850057adb425c924c600bf2966ba28298c014df6d4a958d878025bedad54b9b0b00537cb9695636160096fb6b552e4c2c014df6d4a958d84802dce59b48b93090043fcb969d6260e0087f972d3ac6c14014df6d4a958d8180297edb0e64c2c90052fcb8691961ce00a6f970b232a39c014df2e1a1654738029f65c34cc90e70053ecb8591921ce00a7e970b232239c014bf6d873261638029beda8e64c2c70053bdb41cc9858e00a7db6439930b1c014fd6c473261638029beda8e64c2a30052fdb61cc9850600a6fb6a39930a0c014fb6c873261418029f6d90e64c42300537cb968d6561600b2f96ed32a6c2c016af6d8a35d184802d9eda946ba309005badb228d7461200b76b6251ae8c24016ee6c0a35d1848025de5d2c6ba309004bbcba4c57461200b37b6e18ae8c24016772dda654c838029beda8e6ca903005b75b51cd512060087fb6454532b2c010ff6c8a8a657480317e5c34c49ae90043fdb22a29959200c6fd32d2930b1c018df65da5261638031be4bb4a4c2c7006a7d766949858e00d6bae6d2930b1c010ff6c8a865d638021fed9150cbaa70064fd716989754e00ccfaa2d312ea9c0197b5c5a225d538033b6a8b444baa70043fdb22a19654e00cafaa253b2ca9c018ef659a4261728031decab484c2e5006bad62690985ca00d75aa4d2130b94018ef645a4261728034deb8b484c2e5006bad20690985ca00c5f970d3126b94019eb589a424d7280335eb1b4848ac50067cd7268c9158a00cfd2e4d0122b14019f3588a365d4280317eb1950cb2850065dd6369c9350a00cbdac4d3926a140196f505a724d4280317e5c34c49a850066bd416989350a00c7dae45432c994018fb5c8a8655328033b6b934a48a650043fdb22a1964c200cfcae450b2c904010ffaeca958d878031beda952b1b0f0043fdb22a56361e0087fb6454ac6c2c010ff6c8a958d848031deba15308b090063ed622a57260e00c7bac654ae6c14010ffaeca958d828021fed9152b1b03006be5722856260600c6faa4d29313bc018fb589a22617480317eb1b444c2c900537db621d9520e00a6fb6c40b2a41c018df595a5261738031bea9b4a4c2e700735d7554c985ce00e6baa4a9930b9c010ff6d5a2261738029bedd102ca8e7007375a1205951ce00a77b6a40b2839c01ced54481650738029f6da902c90e70053edb4205921ce00e7caa240b2439c01cf950481648738029f6d8102c90e700637d756949858e00c6faa6d2930b1c018df549a5261638031bed3b4a4c2c70072bd745909858e0087fd76d1130b1c010ff6d5a2261638031f6b93444c2c70063ed426889858e00c7bb4498930b1c018df699a5261538031bed12a24c2a70063ed62688988ce) else (if i < 6 then 0x728193f19f64f727af3d29e6cf227873b39d1ce4e71d3899c24dd26df36a9b2cd826a134099dccda663321988cc3260f30297ecbe25e72ee974cb925bf2da96acb1656b2a594aca4251728693b499a4c325c92bc91e46f232916c8764312088fc47a23c71d38e1c6ce35d1a98c746262f31698b2457e2b514a89d44aa24b115882c4021e10e086dc35a18d0b6858c2b214f0a284942360fb078839c1ba0d304e824c11207f02f815409602b010805c01a002ffc7f63f9dfc4fdd7ec3f4df9cfc97d73ea5f1cf7e7b73d4de86f33791bc4de06ef3771bb4dd86eb3751ba79d1ce7e7373979c9ce3e7173879c1cdfe6fcb7a5b9cdbe6dcb6d1b48d946c7b629b0ad806bdb5adab6d4b6a334d9a4cd1668333d99ccce166e3331978cac64e323190ec77633b1898bac4d61eb0b583ac18609b00d7e6be35e9af0d766ba35c9ae0d6e6b6e5af2d3967cb2e58f2c395fcaee56f2b3957caae54f2a65528a8453a29914bea5a52aa941496a46520a8f146ea32516a8a141aa084fc27cd3c69de4eca7253729a94cca6252f29694aca52527292948ca4251f28e946ca3251728a944ca2250f286942ca12507282940ca024ff27e93ec9f24f727a93cc9e50f1e78a3bd1dd4ee076b3b31d84eb874c39e1cdce6472d3941c8ce3c7193849be4dbc6d936a1b10d686af3551a94d4069b34599eccd66663309970cae6523269920c8663e31c98d0c5e62a3129880c366163089830c0e5f72f39788bba5d82de96b4b505a32cf1664b2858f2c51614aea5652b0156caac5512a6151ca8453d29c14cca5c529292147ca34515288142ca0c50127e13dc9e44ed274138c9bc4d926a133c9944c526012ec9564a6250927092e49224111f48f047323711a48b2454227912887442a20d105482040b1fd8fac7b63cb1e30f047783b71d38e5c70e3771b38d5c6a434d1a40d0c66632e1948c9063e31a18a8c406162fb1758b985c22d11660b1c5842bd15c0acc55c2a91520a7c5342951480a2c50c28113e09dc4e426d134098c4bc25912a093c49424512008ec46c231116089c44421d10c08204061fe0fc87d03de1ea0f287803b61d60e8873038e1c20de86e03661ae0d4869033e19a0ca86403161860c085f02ee1720b685a02c615e0ac855029e14a0a2850027613609884b024e12208e846022610e08484101fe0fa07a83c01d60e607083701ae0d206683201860be05c82d015e0aa0528280136096048823010e08203e81e00e606e03481900be05a02a814009604602080f006e03201680a004601e00c805001e00a00280023beda952ba2c70046fdb62a5535ca008efb6a54ac6b8c014df6d497261638029deda12e4c2c70053edb225c9858e00a7eb624b930b1c0147f2dd95261638028fe5bb2c4c2a7004b7db56849854e008bfb6f5532ca9c0187f2a0a765953 else 0x31c0418e0226f12081104001c326c383022042063616b418521852104290502c1c100c10002080010400002100000000000004d84000000000080870607158715871587158401040000c100020800000000004894406c81000f205c082a1001c840e055308007c817b417c8100c15021032981820000ca4206521652170204040020100000001b0d0108010800004a10000000410041000000830042000000000000000008300420082a0420000010401040000020802080002c2001610041802100060802080b0800f20030803302330200002c0466042884009020082002010201000f204030400000f2040a04200000a0401080003640800f9020000007c810000000000c2048801a4108bc007c005a8f8017800f800fc00fc00fc00f800f800fc00fc00f800f800828907c007c007c007c007c007c007c00407840f04003c3c6c07880f0400f001f0010000007800f800f80083c007c007c007c007c007c00400f001f001f001f001f80107c00f800801e003f003f003f002007c00f800f800f800f800fc00f800f800f800fc0083e007c007e007e007c007c007c0040107c007c007c007c007c00400f0010041f001000000000000000c2c0784003c100150801e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003f003f003f003f003f003f003f0026043e003e003e003f002f002f002f002f002f002f002f002f0020003c0040000000f001f001000000001e003e002793c00800f001f0010000007800f800f80080000000000000000000000007c00f80080003c9e005e0020000000001e003e00200000000000000000000000000000000000000000078008000003c004000001e0020003c007c007c0040007c00f800f800f800800007c00f800f800f800f800f80080000780080000000007800f800801e0020000000000000000000000000000000000000000000000f0010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000bef5f66f937aebcf5e66f13779bb4dd66ea9744b9a5c92e2970fb7a5b92da96cfb5fdaead556a5b505a42d17686b40d9f2cef672b36d9a2cc765eb275926c8963fb1d58d6c6162bb13585ac0d5f6af3575ab8d5b6ad8d6b2b39597ac3d60aafb578ab9d5baad3564aa4d512a6952fa95546a9ff4faa7553969954c5a6052c2941490a4051c28d7450a25d11a883431a165))) else 0
def signed8Level : Packing := (662,5,6,0,0,13,0,signed8Data)
def signed7Data (_ : Nat) : Nat := 0x3290800000000000079010001f001f800fc007e003f001f800fc007e003f0018fc6a2b1085c1a02fc75b99c2dc6bb499ac861af972a851a7932883b998aa441988822008badc22e9635d18480289f714b8698935d200a33dc425da5261638028db708976949858e00a375c125da52616380391d5c5516989754e00e56571545a225d5380289f714b8698935ca00e4cd63589a724d4280289f714b86989350a00c17cb92dda654d85803aa328d635894261200a27dc61cda5261638028cf710736949858e00a36dc21cda5261638028dd704736949858e00c17cc76d4a958d878030eb589b42a57260e00cbe1726c0a1589818032e34c5b228d7461200cb8d622cda75098480326758db728d4261200c9ad626dca3509848039385c9716989148200e561725c5a5245208039705c97168c9148200e47171545a625d538039585c5516889754e00e78142505a3245628039465515369c9350a00e4c963589a724d428039b058d626849350a00
def signed7Level : Packing := (32,6,6,0,0,9,0,signed7Data)
def signed6Data (_ : Nat) : Nat := 0xa282f3a063b6a54ac6c3c01c88d63589b728d4261200
def signed6Level : Packing := (2,7,6,0,0,3,0,signed6Data)
def signedLevels : Nat → Packing
  | 12 => signed12Level
  | 11 => signed11Level
  | 10 => signed10Level
  | 9 => signed9Level
  | 8 => signed8Level
  | 7 => signed7Level
  | 6 => signed6Level
  | _ => emptyPacking
def signed11Index (_ : Nat) : Nat := 0x129a9c400062300000010bc000000000000000000480000016518e8800000000000020d803726ff17411dc14000d2cb88a0d2a3a0000000068000b26c994001a10831b94a4ea00000030ef06fc08f3610cc00000000000010c80000000003805a0000011b400023290a109ec0a0000000000000000c39195c00000022800000000000000000000000000000081e00053300af8ac23100000034f0000000000083dc130356064831406a0e000306000000039d80000000000000000000c14000000086e0001975806000a2080000000000000001ce6000b128002896677000000000000000050bc44800000000000000000006908000000a88ca12422000e24201d4720007160003003a5ca0a8000000a0e50b80000000000000000001c4f0000002c2c212e1aa115c1a000a3d80000000000000000000000e1550e1c8c00060630b585200032f8000000e20f0f8930001c1a0000000000000000000103a00021368858c4867000510d00800060580040002004040000800200108000000430880000000
def signed11Look := lookupWord 35 227 5 13 6 3 signed11Index
def signed10Index (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0xed85014159ef1cb08483c0e5a113528c1e02a9c2615177641fc887744203000007c22446b9a526a943e0854800019d3f000014205610df20f2802ae0000588f80000003580000622f304b05198165e530096a625383118088101d560e7c14d20000489120000783a2004c800009c29000016072781c0c634314f8113f69579413d8996b4654c202865faf804d219d298d6a4ab501140000104a1e61b4897dc149387a200003169e00001815a65912042f6181681882271a93a8616cb000e8cbc000000000380982235c92aa00007d347c5edc925400000000000007999981d400000009580000000000001a6142891664591130145075a2009300301000080089300c0811208b83047808c004008128843030ea4089300081c0c5fb00005800d0aa48d20214007000c11d040c686722d68408081b61a3018506042000800001280460c046c0020e08291041c003041800606c0126002898416882a01c48081227879d201818a501800e1a0028b0e205080e0ce8606014000800485000820300641830600003144448200002831428c0000000960274011026c500182c007020438a5a1818500015000a0c406160018300100050a0e20e00000000e004940a0000406040ae0450eaf12080800a000824028211042038104142812a056810c0820100002831e8829a06004121c000000c011800604102162c1060620c87061c000383c20100000010a040001229382001849e1460d001a2408300001011818009008c0810a2c0811400102060008a020d1090410b010eb040004280111e000021a047010a3800908081011e04b0504805810a100801404002002408318044090e00412081000000242003204983060050f00002180a241941468000440801e083001d041019d040041c0e00080001c10100281021e0410104002962008703000408b00040042a0c00d042c00214e808d0220102002ca9900081020408104020420e0810c8c060c080141400a020470f001030000142083800386061439b201c0060a0010142013841c0050702202860600216020408104100040680006040058004180040818501080c7010a7c6080000001000008204281880010000040068d020498a0c00002280000b00380070018082000008f000029902541060830084040c010002038016080190004380061c00c100c080001400206146000410107061000034000801000911085c3820a18100000041506084020608483001800102000030c000830018385261018e061808606000800210302021000302341800a0000102582030c0408e00149010624001040848312101841a00d0200004800610002320c204000418c140000304000810000201020808000040091814000140cb04000018300000003000185221800900240800028680140c00600000a10808602 else 0xe5f359954417000000c5f860550e1340000000000000000000103760b2800003d3c0000180e22101e6012d8117422288253a4222815581bcd82e564f9c83264274c71b465086043b6202ef4126200c1435444f9b8ab601c80000000078581665c8d3ffe22b000000423b02d9e42080001a09bf099d0440386e7212400000000019050c491216d9a01c18104a5936887f243db91e3c1f4516ebe00660419ccc25011a000000001c47ec85932153c92fd65d6a12285c28800011267b11db6223486c5253c014008416896a7850e6104c00001922f097ac1022000059326c2268000125f8a073000007032ee596ba2fa00001015c0000000000000596f000003178480d300000c07410845226bd94d0000000000000000000000000001a138000002100800000000282c8047a00001e1d600000000059106c4dd00000223f301340000694f40000293f524c2019aae180800016608312bb61f60000080e2820e0000028853019a291bac5eb091cca45f800000000215ac00006230c00005007740910000105fc8000064e88000000000000081ec00000000010426000000000000000001845d8000000003981a000000000000000000a02cb881ca8c2308d1220b498ec0000003a0000000000000000000e63d71911216d800017d41a441240d8800000000289c1e2330000059b6f90b6009099825601ee971764678093341d3b81f1f6480a2f7c114f075e2082683e304f2189800000583e8262f80000652d53033857e796b701db800008111f8540593fc10b2809c59533e645a820a00007897a45f6a95f52087d98e4c4d52043146286961000000000061a0d094ae5248000024a4813400000484d40000002fac14cb02fce0ec701e82811207460000210580000000000000000000000132f9e581106a0000000000e59600001a4ee00001c22b800000000305d602105f82be439e82cfa26d2b0e6a57680001e5b4c88dd6256000014265c914c0000313caa0dd0000061f3800008493000000000506ca0000687a40000507140000388460000484dbc0856168c7dcb28583c4ec210e1a02e5948d443d00000ac0fe97837c7059694a5459895ae1a7794aba15c7173385d598873a049e4084c63a9115a464f0010e00001964021ee790265249c8924000049178a43ff12d9621d80000c15d418b925589986bf57a71587e63a5021da050d040a0000000006455693ec0000790bdc4b42002701fb905f0000000001411d49342055eb1831a8c4a025b8580d862005aac06dc000010727113dd876ba464f064200003e8a384778861e10c7f11a80000081be0000281e281de2021a408e09166000000000652c810c4860b9f8b20000215ab4559e06b00000507685125800000000165cca5a8c16d4000050034c186911b465e300001a5fe80001a5838000105c1b) else (if i < 3 then 0x491d52516a14b14218503b87c72f0849c5acf01d2013a5089d62015a0e900e1105fe000079127026db01114238d04bca01f29044209780001e80cb899e000000000000000000000000000460de88740000303320000608e00000736adc600a068941839954501719899480fbf061385bca87b75c735f082045af16cfe19ca868f85454859400003180f2503897cb64e9b822e710a71064fd3b80000a175214a3c131912db8029d97a8000031427811bb83c1c51aa06b9a18300000000031827a0b700000a4620000065c2a95b2000059688e1760000024d6313c485cf571c580604a0eac12580001e02381898a507844f1412688635a1eb3998b20d9f168ec1e9998878020c01704150e127c2118910982140894cc7623087be4273698a28472801dce663f607a00003143061180000161470469104d380000f070d9223e1b1800afc022488e5c639918de41bdb16bc0000396352db718752a154b84ee20d6a1559e1f7205fc3c4310144f835f0709dd0a085ec06467147881dc900ea4247880d341a6212fb40f7090ab00f1893fb85f4b94efe666b952e2529394aee26f985f664f5117348a294203460345945104d7a905f60ed90376000061262006c715ea0000000000000000000000612a34239c4003641e0863a263f856fb61e118920221e0000100d2e8825e5fe5897880fc790f20000000000000112bca51be86b34141e94be862499212000000001226c510ce65a60854ce44f000014546f8902e58680000c570508b800006150101ca2029100d9792b5e216e13460510201bae5c0b95d3bc49f2719662a19175c21f78766a266a02a744cb69925254c301f340c7c9453883b80001c0c880000c05439311460a80000c1f938168d027780dd84a7496fd85cfac0a3e44768412a1cb3188f01673f1c6823fb85be2105830292185ea30045e6800d404cd700f90038587da000000000211a00001e15b4909a00000000000000943a00005895f4540a0466c24d415d0dc20180f0c4ba8000000000977b421b8e5e800001102aa58da11c0d8ff80001063e1947061af6866a313f9f0c5a4add83401d83d70850610d945e812e50494a127083ed0563d14e24406087c745b9d14d5816e080d72543401d7223b5856520659048b80da493c0601b88652243229788a00780000e5f3a97ba054e2097e00007936200002937a466100001a531716140000195a4000000001e5c480001407280001c476109d481132883a00000000181c6cd6c3513b6179c054400000e0b5c1800c1478000120f548700000000000000009093423bd82c0000061074408f0940226229065585683148000000000000003082921b4406c8000050046856b80000c491917f6a157e972445f100001e40a481f5c1c8000010614902f2647200000026b216c020f300001e053b95e3 else 0xc4948022c05ac685960000120800000000000000095e48566a9958255319744e43a0154ea405f1822c0c3393de0000330da000000000062dd894720a51101d05ca0000104e52068ca47d0005ec15779156c49db095c209eb801d40a141752203f607c86443902f6622ff80a821c39882f80ff4858ce0898000000000000161cf5e3c7c02510953601400000e1776800960c280692049bf9651416a68627e1f5a843e86455128b80b6a9737a5a0c85a3a2155c58484ffc8398a6330000121d2d98a55d6b3a2ee00003834fe0e6f883c0000616d60000000120000001ac507298182402ad984c2444d846a60be7008c6156a1266a0a4b17b80489c96a40000000000000404c800000000000003100600002173884119879ae23e8089e61ed211d78546319a924a81927478693869e6039588d5a12b1a30e625439233c42520823406db1656649af00e9c4e12091520a0d18c5fd3b1807408bf800000000580d8617eb54d800006048c618d8147f8264e18ac0000684be00000000125db0000101bf00001420e000000000704084088e17200000000000000293fd810b58231c65225737e16d283dba1ada32fb825c786113071e8442000000000000050702c1d83507be4e5b88658499598c0619b5825400000929820f39824b841bf171be110000009d258000104780000000006d0d60000000000000080a1863cf13d960c6513ad25d8886e2000051632f029504a400a751033321f399976126398cf05f5f03126084a12312042689ab64f300268019c49701306c197b004ecd84c0419e31891e55969316a430b144784f1a70580000512970664e0808a2058000045828000000003061c64d76011224942e48b1c7080000e1e8194e8820d100c22409000000000000000000010af40c1f927f20932813c6638d9933440f695ee0000716c800006050b44a228158e1fc00713826900000e1ea7129f809e2188ce98dd02d5c015a08e8a048616dd8112396c2a172a194600ed08957659f39084619241034a557cc500b1bc01199e5ff287fd49d8217306551cb636e5ea98179c0c3a155a25fb0000000005085000000027c808c885df6578498059a23594ca8006b00ee022f511c4000059466605b295994634c001425fa5869000000000064fa800000000682b8000038664624a9831a00007948ba1138000065213136fe1a500000e415b41c4a146118bc048e800000000195800000783200000207e28485b138c6c20192148446c966400000000000004009a9d39396daa4c571570e0d47072525921c094200c71123c56e00001f9bee973a00e1a8078000000000000060044000038032c0db2d5cc24cf2815285aa08206a23a8812f42162163a41057a30505a86974b00ee94058e542f1758006620939206e6860814df00001f0e7d018b9d61000000000)) else (if i < 6 then (if i < 5 then 0x8e14b7dc6c00000865e0000104fc8000120494091885ae6b0eb442e683800000688f40000505e72431906e4c2224128304d5f88d84027b16134144b9009e80ba990d60f7994988212b936185c1406a8a45bc85a7041ac181c2482f8297851cd02a000000000061557086a000000000c0ba00000cc3800000065f8893fe5227902021d598360044db16f600000c0880000094da421b585e9c09721406ecbf403e59c6cf8337826e80001015280000224c285afc436004fb80f9e137e05773121c8240688aae059c1377620f989b3658b80000000000000451a310f025a440298a083c010600ef011f7e56db062825245190424cfe90fa00005077fa0000000000001408000003124301bd3844a000063719c0bd71219c590b045c000000000c5f2711e620478092d011600001015c80001c1d880001245cb9589e1315f09ec266190d000005070601b0794dc2d665887000005816f1d3cb976870700116024dc01622e114605bc00003862d30f9109d6c018f9239e5f56197744e00871d558b4819166403100004edb833da1e1902664cc2b00c8202d9943c258761708607f216c7a50df171e600411773e418811a0e11db18c844da90237e0c5c02b62098da03e21b0f482a04a1d191c24c66058f2625a92de40f64932120ce892cf401a38923e513b853c259ec83c5851580103e22419497a4e1d1414000000001660a00001460200001260e90660c12a80000506e501a284a0000002496f0140e193717dfc53c800001a486140d005d9a6ac00000000000003148f623c7874020963874424a9c01ed24fd80001a5c3f8149f9cd80000215e9108b60e3c912400004912a013f9064025ec80000641a00000853d800000000391c6000000000e5833a31018d181626e1e65196d64219c4f440b7f819a0000000000000191b7c4ce000004130b83d0054b1057c00004b5ea00002999400005144c000029096a05f80001461d8e4ea000000000000060224208ec58a3823db828ca40c3085e0000594ec00007930c0000687ae4c00383eae1e33034204f73c91780b1e0686a8bd00000043700001ec378000000000000000007897201f54936541ff80000463f4465925029c0c5e502008842002903c3259a00000224b8000021cd692cb44464013a911cf14bc80476881f20bba856ba13300000000000001c258b8347661f097dcf06d41303643300000445ef09a0016b000000000205b1c1e43f926000041618a5a161140044a000000000016ee2548d89d024ee8880724c7e192e0000430dc000051412000000000c0219921041cde22f90c0d4924a614c0000105ed000004457114c765b80000040f2000000000000018e29185ba00006875a000000000c1bae8308000009190c451708c20000585f4c4b5282ba000069369c629b055681c280001c1fe8000 else 0x469e20ff08e00000000144d371974022480354011f00000a0c0ed6da20bfc0559a5280000164cb800000000518380c0f0000045a5ac036a1f98000000007858b04a30000000bad031c000000000000000001c6478000120f59194f46624809cc09261767a1731c086005580001c14ab8456a593893bc85ef500de641d8000184c7000013e678000000000875c0000000000000505003159e993b614b5739f044280000000000000000000001280c0000000000000000001884c0000388b20000000000000588b7a4740000000004060aa02fe853f8974882be00000000185e5944f8209c800014249e8716d91a00000000000000c4f8b81f926329c4e5a058183a8a966698c361db08345445f71937a468f094dc24711521acbd012d2c42400001044c1060001d90000000003999dc00f5923c0000207e00000288da008a7b2f6606a89726a5ba00000e0eb8000000004819ee259e90a6425b903bf8199e95b0d02398718a580715a7e4b9884b32549c035604f6f8961e1371042ba11908982e80f77690a20cb19a170861f2fe20d2500fa24e231908fcf93854766273080f24e8211b10652f17118636291a746632192c00004177d80943c670600ab84e400001172ca12da141c410cc94e12158d98340000000000000001cd64e48894264cae003e000000001a427790d40000616280000189a88458a1080212b893e5a4de77500a143800006486800000000704866800000000000000000000000000000280480000000000000394638117996b50493e3300000000000c21380000a152000004573c94e6800b2006d4028876584272b86800000606ec00c100000000031593c243f853581f300000608fb15572271691be00005836b851d000000000401ae0000291c38135c8591025a0000000005644e01a14078f224df1052a579e00cde149c82e1e04a196d0e5efe847aa11fa9934a111406a5821ef9819acbfa20dbbd416905d41a8e166a01def1271e44248064e5708165d9d3ec139000002977521bc0063005a2e16cde454584100000309c2814168578c22ee02e6000000000e1e48134544c929208c5da9872a216809382e838ff4f96615418bb25a1c11d3f5950810cde1f196520404a1443224a68651405cb096425a4d0085a59c584a80000605d000003925600000000000000000000001107d618af804000004939f056f14082000000000a1f280000e60b000000000206ce000000000e019e04060000311cfe44e6983ea445201a4604041780c17b800009026a8517e461510a461ec80001013e2017ca53ee00f4e217584b08225ea2f1a03da775e80657175f2070f85f2e1a9f20e445fd1756701427000784efb8625844089883600ed01c4e41c0000001ab8042201b7c9259c56e818f68158683a4041ff109e0000304e6012eb95fb218) else (if i < 7 then 0x9dc8286000060886658c010edc0dc5093de085a83f7414db075564fbb85f801d34f1b80079b06bb84e39709685b138055824ea95288511618f0a60f41196e04d800000000383f4b0247548a00003004f5043782aaa1348000000007053b85bd5409f849b00001a44b254ea21ad00000000021180000038975c4d980001025a896760000295b4a43000000000020492653030783a413e96fec48d0709045c3294fd064391608e22c141bd2642f8130664fc94c200006990304ab8105564f4a41bfe05d4878be626800000635494c9105760566a5361813e60a68000d210da145800007870c4435907d200000000041ef49146ecc32136c00007174f60de4012bc1989939be58b0137d652a512ee6587d90eb60a7b873a0000282604672c086265cb9079e000069810002f00000c0c0300fe9d3db15c680fed95df225008164acc460060449e894dfe11b7115844fa490058009393f980a20000026720000181fe019c12151000013183f0280000000000a0ff8000064eae71c80000101b3809b3f6b902738864461d0e037c000000000061e80001a206807e8615fe810a0646c15e8000000001e06980000a0b8e1961013f296aca024568ca64af909a2000049647614b80001e14500000a4180187000000979381b3083b22080098752108603250197f03396572c03f200002d46965e8608b4000000000823380001242d000e6016111595e504315f6203cb872e816212663219fe92f8420aa96ca6237f3303c21a495fc000000000c0f480001842ec882701014016bc631b1655642b28907c48dc15eda204384de000000001a058902d241c8b03aae200508980000000018174f8028d16b000000000205aac51f2952b620c389040000000000000684886443692dd998b106aa61e20997ce261891af8166f07ab88bf1167f80844043400004708662307066ea16798080066f8000144e9795d9fc6e813c3802918818e444412c93141a900fe0cf800011cc7d11ec0000685c40000304240000206d360e480001e17091278000019105063e893360000095d40000697e4000000000e15bd16f80000682bce44eb04b400005969c80eb58568852ec894fc447b81de2432981388544800000000117fe00006963f017ac956e4621313d1810e5118a610a5057790249d94c0000716176071b896c0000000000000580b1e58e7f473313ea0908410780000a5aef1990664c6928f6655e0395c521906ac65726883666018f670a1fb409a7649a000008460e05e1e26f584848452113cf9141590a2000000001006a686ff7513d11f8218b8914ea063514ea414a24883a51da82460000708d285424116845257930a25c89f1bd3c6df367fc223810a8262a906e804a10051000006063da005a890ae54f00001e9b7004e2865e800018172780cf40b141945e1f0e81 else (if i < 8 then 0xc132b972a8255380c744987070441df20003e1cf80000c1796981f01204230a82318815e45c70000060317067bc05301429e6372832a811ca81ce40b31124996329005a1a5301939a1ddf177ee1918000164a5308c40000000000488318b5846e313e12837b8821a4237c4ef0107192a4625df81fa207879048e4d2681bc0000012c761f0582400000000000000590726658e91f2000000001e4b12884224d4e07c44487fe37c20acc8043a4bd6c8acc5e8b95060000015f3f06cb17a720e9a064bc196b81e4683b0f916a00b8000099b0800011d2cc806a41866835ce650a847060d78c097658ad90f9e2628764b05479832d8204b03e1a103583f9402b0f0936093974f584cee99ae82468946441fd451a400007039c0000704ce00002934ae53920794040f80001c4bf80000623212302626e7f1bf81afc199e0000000010099082b5c103e9333802d7b0440000000000517000000000000000000100360000632efad74f049fa02eb01b5a560c1714cc0c59986c64880000aa2af02b000000000120813174ca1eeb9790a627c06d7a5d24954821e580000dc26d115e0000000014264311ac255d797f1e001441cc05bb506d400007f094459bd8639a22080001613c0826a0000208cbc4e600000c636a956125f078521c064904a7a599e97a40000000018076d90b1c641c15f0e42800000e649b18b324d400000712c80000061bc94d6a1b86863edc011120e809d514cf70723819da50ce96fbf9957890d040370599614e390d2000000000c076481220000000000000000000000080206512997c2000000000e08300000a4dcea56de13d21624c0e09847800004817bc146c812c4032c80da2219e99c20000091860000704d96436b14548db2b15cd456fa177844b96828bc1dc00000000058092a63b897e7e4bb385cee0863f15d244b895d78038980224613e01f785f4093b40195a20e6e061e8696e1b6216ae645c10329601f8178680dba04ebe22980000c2205918e000000000000000000645b710be00005c502e4acd02ac864480001255ca02ed047ac068ae4836135ba0160805c6193b867ca6105960701b6b475e0178a841aa564792c205470000084ca0000000006873285b9290038052f963c00002858601fd80001a0b4009c88419fa67ec23cf178b6176dd3c6dc27286f8c497808a904cc09920c0cc016792668891b2a26380000c5b79008a25a06827664aa38390e469102a2818c99718260cb107bd06e88039a568f9241e08a811ab441b281eb807f864d9219624005a1975a6caf192b043c049cf11bc0000316217d408000180808c1260000015a9248a8089444bc291e4007b80001a6568000080d4d939da063e06140000000000000211dd213b6037244ae509880000000000463306fa00000000042446157c1c860000101 else 0x123f81a1b22ca07dfa5610050da169316e20046330ed04eb8000181d249505482af82c349d0f994ce41290522c0dea8781a51b188a065d91964b409fb86ef86226169a00005176e00007959c000000001c50bd8607f0bfdf6f101faf102d6229341b60000189480000302f0000000001e128f96be00007079dc4c0315fe0000000000000000000000000000000317efe0a3f18e020c5330e9a1ce00001a8370018404bd80001826300334c0df80000c0300000181c7b845b6571208a2113ca038c00001869ae51ef942385d01b0aa64c68000140a968235a5f620945813c9941602159871044c8f840185e668454c014893f0000000)))) else 0
def signed10Look := lookupWord 893 3403 7 18 11 3 signed10Index
def signed9Index (i : Nat) : Nat := if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0x1201020400090200000101000701160012000101080f010b080c0b1202020100020106140209010b030603020003041a02020a030000050a02010b04000204020f0800110002010002020007020003000c0b0404021f0a030306010006015f001f08030000020a01040800000b010104001c010002000000030409030521000100050e0c000f0104040d07030304020500060e0600140303130100013701060002080221080c0704010200000014131200040209010110000120000d00000b050106060b00000300030709080c090002000d07000005030504110101000300060600170001000006080003010b03020007010210000100000206020113020300010b06140201150a1906020000020000062c03050904050805040002030201000401040608020f0a120c070107030c00000b0303000005011b0004040306010004012520001f030501050c081302080000000500110000050900040a01030000100c11060d05030e10010001032200020034020502001a0504070b06090101000e15020b091a06000b00030000041a00040300030501010100000008270d00000000000200000a00010102010509080e03010000090c010f0000070f021a03110003001800000006020101170009000109120300030b0805000f00030200060000020005030f150103000802010302000a03120200040f0200050005000100000001000000010003020202050000020006020605020000031302081602020303300d200004000205000200000000190600050a0003000407030503020b010113030e01010501000106150102010005000e000009020105000402033a000405150101000404000200001103000115050000010000060d010200020015080200190e030300000118030e030e0001010e08000001050000020001000002030004010102060d090300070b0200050806010619160000010503100c080706140a0801040001000b0003010504050002000100002600040000000e00020025000f00020803020a080103000000030d030016000101000900060003050b0107000708020600000100000006000005001100010200000000001b0201091204101c0200000500000101020700040100000101010707000100100a0002030c0108060204000003040b00070d00040604060206000106000300030002011400160001000b02000600010205000e00010000010008000001020401090109000602010202000601070000050a010f00000006030801000200051007040200250004000601030000010c000005010900050102010000030102070b051100060000000a000000030211020000090000010004080005070303000d01050206080108060100000f030a040106000505010001000101260d0500010507030000000207020000050400 else (if i < 2 then 0x4130105110c030102041b09040a0000250a09010004022600150b0302050002001b08000705121a12002906000b00360005050208000014050201160d002f010b252f0006100108290706061401000c0b04010f01080d000d1f280d1c01000e0a1900050804050004040f02010000080007170100030507160405030b0507040000020101030300000209020000311a0002020502000006020316060104051c010605020100080a180001042f2402120a011700010205000302010000090e0004011701020106380002040e033f040c05000d082603060000342027031303200f210100010608111100070d02010016000607010d0e010c1513270005040502011d02000c0202000003190101070607050f06031a0006020e040007050901003c060600090c09034505280513060004060403010d000609070100180e0f030e05000225180a1904190135031f010d0322020007100000002f100101510c050000020200010204030206031a040d0308070707001625030103140b0c010207010100100704210200070100020101000703010b04010209080b0603033e00000a0200060c000005080a06000d031e0e00001200030401030a0105050300000d01180c021804180001090206000c0403002407000001030000010807050e01023c21082a01093c290530001a060b040103000010001a0901000400030228000201000309050106170016061a05090c4c0a100c0f000503080200110009020a0a0000160002000201000002040011030401000802000100010007011d0000010001080b0604001f020b060604000f05021010110117160c000416000028020207000301070b06120000000f04042205042c000300071402050105000603050101030900000800210c12170903000004010202040000020606210f0109000401001b0103000000080012020015150106050009000002010405010c03060100090600132c00031100000001022400090d0001010500030313021506040f0d0e000007030001180004020d002c0002032d0000080114031101030009200202012202011808020304013d111c051d040f0000041a000516000f04030d0d28010d040c020327010106010c0a002f070102020112210701000a0300000319001617080c0f02013612090100000202000200090801050400043001053104000102070f050901010f0f0e013c030002060903070301160b09080308020000263a0500120400040206060200020a070204000b0119010602000602001600050401010200000109000503020e1a0702300100000000010403000101000c0f0204130e13040201001a055206000304010514050104012301090000160f001c00001701051802000913020202000d0808000b0c01020000000020000020010001000b050c0500 else 0x888900524854447d615ee83cec2ae4e0728c1ea616ad8143240eea83cb112688228b0507288cd80000810d12001d0997b8b4f9817641ff40000002aa000000000000000000052d0200000000000000a01e9a6e2c000061405a87dd4099de40d2b3d82c378027a505874051c00001422500000501e76361000000000000000926f821358050d000007e55780ccd0b2c272fa000000000000000000090d1d025480000499a100000000008d5468905000012499d20838000000001c0bec00000092f8249a614d704686180e000015cca9e161c914400001c137904ca48b9e00000000000000619f000000000018816418d74290c027e5c16c010bc88b9fa54f43ae15853d82043813c81044889a3a137242586504ea993ff371a00002483da94a8235620000188d199a8d000008674c000058010026e022dd5b00e8000002493e9f2339c9e148e000004510483ef5811c3e3f2e5af84241217395255c220ac000000000c412622b7c0000000004085561af000006933000000000029079ef2ffc29de000004ca3e84f600001828480000000005010006109845fa1423404ab28f848b89c890e00001ec7eb83700000000000c8838f52100000000000000300368000000000000028a9ad93a0a225140259fae48000000000fcbcf21896178e0000082142c91930846134d79d422c11d00000814620000000007f2a9c2454c097b033cc050b006c6c5c8fc942b96a2da78442c19cb9b006092116800002027ff171bd8bb79c28d184e0000052a9a68fe14cc680000028090a7d30cfb00000000010538d887b401180000162bfdc1782320d827afa548d48a410981e2c3a022c58cbdd0429b0085e665b04fba21dd60c3142c6cc0a4b03f370967a03e8cbb45188ce139b81e8648713974a00000c51f400000184ea35a0000034804510c7000000000004ba784f5237100000309c0000000207020801052808014411201d1e0e0200040b080024010923050006160200000a030306371010000101021507210977020101000b07000f06020802111a003a0b0002110404070004051e000802060e0307000a03001404070b020f1900110005000002352a020505010c6a07010208000c130701050201111408060001020003033401012f1c0b0300160005161d020003020508530100001f0825000819001300010002190009100114060100000b0b04050106100c02031800080e000f15020700000e0001031401380f09110727000102003107040731001e070e12041406000101120d0907040b0208000f21023b1900821c025d010031030c000600180703140107000601162013162e2200000900070c0e0800041813020a130400083b0704001a000b0706230000000000010608011401000513000e05040d00000105020100052726000101010a0704220010)) else (if i < 4 then 0x2d2235b8518889d680000915fda5f53003f242cb00b47615f0000079645f09e8e5998000000000000000000362daaf210c08c60000001d7800008295ce57ec00000105e00000000000a6000000821e600001c49900000c37ba451b40000222b5f01ea00003cc05df254f2be00026e424d800006f2c0e0357c08380000d0344224c70da3a45e8803f5c0c15f480a70ea7238200002c2387814ab24faa2b09c3045d0fd6062fe10b8057700928043c5e007282d7982d70118200000000000000f0c0000001ca2580aa142716000000000000008282804fa400003894de07f000000000059928a287ae66799259000002141840dc0000038427f13dfa1a18c88220996e16eee2b1b4b5819327d361be14c400004f5de920ae415e54b48140aca291ba40a4811e4835d424b9d83dd41bfe90d06300b42cee199c9989b30b8ae632a80e14a3e9c1393618dd823a1183fd17ae654decb0b3710d743fcd510c8537b912280dcebcc568459e874b731dc468040201e9940717c4a639ac0fa9133102ffa6caeb83edd8512625b9028b7018a220920000162e0383bb0863081622cc7b40544087876239021f14ca19892f82349e000000000305c940a69c0105832b7c1f93a50942551096380000c6112000030811000007ed22008c68cdde8bb900000c613585be314e840d6f22b85c599000000000165f40e4290000060842a0fe68af8b7104203d92115c4a2380000867e0c146dca4455248585fdfd7a7800c505b9204e00000000002147202b0f302ff40dac027a00000c28460c7e689e64e599e67fc4435b8958122aac6d758140f01ac00001449bc00005393e906f364800000000000804c2000023988f73901315de821c0000570a200001011ac418c18524000000000182390000000000666040000285ded0d540000309daf062f32ce4647944029e1abb990a000000e1631c8c283140a5db08ac3312589086ae8ae782d0d100a00001c5d08000009219509dac017c0000711f5828f282ed4000071abc000000000104f9b10360000000f81415058b72d0c1bc62bdb96d80740728320000300e0000005a1e600002035a212bb52c300000398f23b699b2c98000020955000000000000000000069a610000000002094609ac21260d9caee046780000715f2653560b5f80000000018874c205b487975610d2293400000000000000c57f410eba011f2b2a9842a28380dc38e50e689176645da21783e14492504a62f0800006e5dc00000000041234e2d74a0a2000000000000000000004bdd80000b2153dc30c0000000000000002c2c00000000000001e4bc4cacd08aae60f7c0000000005a699e282c0000280c000000f17ad624a931e0e06280000001afc0000493d3f08a8a574c000000000bc1fa000000000469d100001a134819f16894800d47acf3600d else (if i < 5 then 0x8e12520c7975ff2bf303e8c5d88000040ba9b259701bef4dd9e0ab846104e63e1c8c1e0a5bc23322150a4907486daceb95c11d8d9e661a2af2246000000000492b582c1ee40b47aac1f854f2ecd80ca3c047b8896308b18607800000f46ff057e00000000000000000000000041166932ac0a7360110c569e45be52fe6000004ce180453c85958035b7150391367229800000000038beea2937e1fbe43a231845e01a000001058900000004c6000028a3980000a2546487bc0000000006636500f5b4cecd1aaed168266be54840c0a6000000000000000706a272d6a00476010644a352261800001c5e1595341072400da20d8d845e2b23d40000000000c838b3489a4280c9456885900001e6f0f8b31f9897a2072087e6396b945de6161a8669c4acac060f5046d64c756203a45cab8358618c584d1287e7620a0c545601abd43933072df0312c5522d82ba171b4669aca21f09554212070b6b0360c048142d32c66014137f43060000002f6681a480000b2e2c000000000000000000000003cdf0000009019c00000540b3c60c000000000009498811b00afbe10c6694eec5c1f13abd1215cac231590d67c064d714ca541088423b60000000000000000001400c28a1458bb700001a0a0a884f29ab9b01d0e23768a2941750d0da202a4a8803c129eb0d346657958f880b88d2398a56b501924602e430dd21524000070a9060b5064dcb0904c125000001c19334b1db002db0a894450c0000418dc5163021aa0807bf17aa64560a1cb8242980000d214a00001b9781f2f4113e808f2800007073204149e469ccc7ba75ccd236e24d3c000029260604b3e037e02a7001b800000000000000606e64127ed83e610f2674e8837aa40c10496610166000016639c8d07cc00e00000c2e440b74000002e62d018d000002432a565562000ecad5b09be6c78fc591a89532e0fa52766a5cc1687be95b73002c65f19c2d81a1d0083f8a1a98f885e42ff52862224895be43055286424808d4837b995003088aaa08d85fd9824822df38cf4f02470821b7259200003cdc00000072e6845e26cab6516f6de624c04c3ca7df01e4512790118a484b68119fe5ab45add820af927c7043c64daecb376123351153a088f8470f1659000000000080322950721016827fa8057f9b8a7075804e3d0af04f0008107e051fd21c8387f41a48b45a1f04f0784da111e640886cd65a802b1e90b40d6a45dd799d89004d850b400006081352c15d4639c053399130000000000881ff166b00000e68fd05a82988300001e06940000000005008a907e88af18000000000000000000505607203dc6198497b8000000000000000000600130000000001824f24428c26e600003009200000000000000000002126c00000804edcbf8b924ac3101804d40c3ba0a79f35ba25324c3ccb13 else 0xcf9400000000096fd6000038a96561ca0000000000000000000e269a0000100799998472ba4646768480af31cf28ce000000000000000000000003cb44181c4c27640000343ff8115a8d3ae000000541800005f20680518c2ce70a8f915a84a3238075b133561411c1aae8b95386f1020d2000026ceb88750d254e00002f857e8b4e000000000000004a2b809204c2c9400004965d82fbd841e60da0042b90000181cd7c519c030a7031081f25040218217b00b6e5c03c1acf8825763e6c0be800003c5d3726a14169905f480000c36a044610883b307828418a00003452c515f9eebba02d69f079c16a400000608594aa5b1a2c82d5f25c9c0000784a500000c459e422809b41dc770a05224282e8bd200001907f40c8a910ef92aec0000000000896c40bdb20c828bb0f0aa7117c621cde8b8c358b7aebd8000024d40f45e77ebb1dc6b000004097800000a4e24000000000b094f949c8c4b88000000001c5ce8000000000f27ea0000000000000021492c02b08042411aa00ef0a26a00000002b8224dbe0e9aa94e000000000065bbc00000000000001047c80000388975073000001cbf769bf0a611ee56960c520000000001e04b0000000000912120000000000000000000000000000595c28346dc617800000000000000a5be802f5b177043731a119dc9a27108a22fb000000d158bb08eb8ed3e59f6d313509507e72200002023f40b2cd041304f787ada39009f217c00000ca4b980f020785dc2fa0a22615a66289de0ef400000000050edb543ffc455e71d0f152e029a81851513e76010d642de4d22d038a788e7c06fa0250d309400000e2149ac109961e60822605da4a6750b810000125d4a00e9f409e1018244bf50d41c13da50ccb866c719ea285172285f463a440a25017aa2cd3c224809df687932283131190c013f95e2000016cacdc8da8000000000c2228000000000e1256000000000000000000100170990c80000000000000000000000000000c6595c3c180000c03c2269e83983e833a0000000003612ac1a47a214d2050463df000da00001841e10da49876b62e9ee0d72c431f1bc40000121102c8c2cb217106f1a497c0000686ce00000008474c32408f2a2a8ca54580000309ed900cec2fdf09c16016460de71c2dc000000000228c105e840000503d02e028e0e76023dc92d60029888f3c00003f0b200001213dc00005814bd414d41828cb8cb956d6800ce12fba9def148a40cd165ff1e2f2a8575563ba0485bcc4e10254a8132e87ab45dee0af12082c62e6810e8d988b9148d6127483f9933f64861e0000322205eaa872b95409f8612a7c31e00000a1a8422eaa99fb0000141b40056e09097ee559e260e01fe8802fd123f8487f89a1d0250831b2849af0451e9ad30000040cc8000059b7d88ba4a44c385648000012))) else (if i < 9 then (if i < 7 then 0x5b0f1033fe583c826e616ef93900000100177781019597000000000082d9800008110904f510d3b101d033299013500000193cc2150fa2aedfc7250ba0b0a532471e0a5b995f50256e2035179910882c42758a25c82880c838c527b16686000007872d00000e06ac0000797d30000060748006200000000000000342d6f83e3206a600c540000017c2a3024000038a532b3e1000009a7868cbb60a0400000000014ba4b703f413a8842d800002b3cbf0dc3654700c28800004156f0525481d28000022dc6000014c1e788ed5095f812eb81ed80000b14be0000232a2d893321641428070584a865300000000018109f883300000000000000000005143ba1530cacf309dc9172f02c7985bda89156201b027b3c100b12f4da783b0b9d888e68b6f20473e049883e82974e10cdf06d3000002145e514c840b1d44352126ece134857380000200dc4049e000004429a0500a146de065fc94c0000000000046d18bbc51ab600000000013c2908a5000001f2414000021b6f112825d83000007f0b90e56b86390000000000c0ca921bc80000587aa728720000358f7c87e8028dd45958e87cf0a84b0ccc05191714e6011782732687feca944181938bc72515db1dea81323e168217bbc496008da2e16a001b80000109cc46fd9bc29c8a098930f00001c49540000000000000000002c26658803000000000000001b2ad00000983eec0e6b8a272208bc4130c3a900000e279d409e4833a80000c12f87a8c422849977ca301f05aac00007945972de8645a801b6f65cde0f943d1c788015034ba2abc4695358488000000001e57778398a84fb0000000002854ce9afe00001805fc0000632b658b860262ebaeba0344b02218434784ebe8a8c604327c29a2a0d70586935ea20a10cca81f0a492dac000014808b9bea6615800000000000000e01cbbcfea034c0000022b2221d5c8d7ff043bf068fe53b8049b897c9c0e20e07f541e57f5c1532f20000000003156ac88ea00003caed00000c261b41f8708db095cb643e6e20ee0cb4d9aa460a4d8032dca84708655059a9a7cc0000086c8d26fd66c4ec9f1414007612f4ccd00b47a83f10000121b5082c62c1fb00001c60aa8a7ec928270435c61ffc24fb964b61171c45df4b9b89274a02d9e05b4cc91480153054540788c59a419cf22639e44cf81afb8603a14d000000487a00000e2daa054270c46b1357323cc0000000003c5c29147fe484c0000795d800000810b400005c319dc77c0195f217a10622108f881e50045011b765252f2604e43908091042fd0067d5839e670b3826023cc2750002308571497e459201f800000000000000000000180d00917e57e0000000000547b280447c25a8000000001005ec49a5894c400000a61e0000000000204ec8016a11590000000001015d0000028252b27708 else (if i < 8 then 0xf0af7a0f5e85bf9050fc0229409062058fd908b99cec0dc881fc24136b177b41019c43f800000097590fea0000000006152db2eba00002453d8000000001826678a650132c603d4c58af8d3be9903f2d414825b7815c9a4df21c2e606bc83161a85d266f5d6c084dc3f902405fb256593857372bad249c44c96c906901dee0be7601e54c2b79bb0912bc00000000000000b14ba0000000003861f0000142df9c249000000000061b8a8cabcdaa8c24ffc588282771815200001a4fd000007a08590e9e0000000007172500000a5c390b030000000000000028b6f800000000001790000000000000000000000000000000000250ed8b29e725200000254c3049d80000c0b76c546c000000000a01552642e00056e245b22d7022e988a6d195a80486000014a9070b43617be64dd449d481a653904764c2c000000000aa03ba27f63139397847269135410fbae608afa1381653e7c45eb06f9d22aee0c709be0d001998171c62ce026ab629d235d16c5e4117a00000c1295014f29420000009e22c4014243b80b32ff179afa0aec04113143000016cfac00000000031777a54e1cb10e93bd8225fc1d60000000000f1388061400000582b60000041251c0f9c198e013c47aaae08324409d2ebb8a16dfa085e934932d9350feb491c1a08600000000030177b8714f2aba4554f84de20893101c2000020ab0a12a2a34de516f789c38000050cc8417e0000021a53b49e885ec5423771820f43ac461b043bfb831da0c9b60b81057c000004295e62490000069112529d2000000000282384e6956659000002078c2321424c5c4929d2331602876da5c0000018d400000a1f2000004155cb0dbbc1600fbf0d8489be01d45ee2c5ea800001349140638041b000007000d46f8fc845a0413f0ecda0092a18140898c10e7e65340000000002065761e6000000000000000c26100000700e300000c1974000070b0532124647814cb7c9993e13220000110f1b810d0000000003034aac2a9b3180c133dc8e3698b792ac42418e8a6fd23f68810408aa785a4840a7f329786dc44512e9ad8f0645a50c30b6c80000e07df0253f4489d863d90aa000001e17c21377315f8263d6ca5b619a40000185a7649c2332080000108f9dca0708a5ac0970e151acc7b7912a62622054ab0164c09c860c41e1cfc000000000000016530d404a6084700000943d8000030b3e0000000000c5618000010f9a22a177bab185d382964021a749bc000008319c000000cc3112076e59626b9000001d3bc4119585129096c5013d11746c00cd0486683c9914378823c000000000000000000002e69923910e74ea4fbc887703521123a20a50000000000d89d0a19c400000172d000012044ab92b4985fce5f062574c0af80000530a760cb2d8f408988b931445132c42f98bab000012267b else 0xb21050c162b0d4e988b0d67cfa4d798bfb61bd200001c20bc419df9b42807cd04b9c000059795c21fe241f400001086e004140000000006c47100000c4fea44f9000002a55089eb4092f000009120de51a94ce2a0aa536108a5f07c1ab2047ab3103a0be1cc95983d74e5c586a28c4f40b030deb8a04647c2c6d53bed0ede052fd0c0da87b7106e8228cbc24ab889fd0dad61e7f0c51993c260d19c2b1d01eeb9be57107000003842ae78ad00001e26b0408b6006a4307b623d6c88d403210000000000000000000000000000285af714c8000000000303918000000000000018abcb89cb000000000000000000000001068f7c1bb80000928f60c2680000115241133ac63cc000000000000018100a412d0000000000a1fb3089a3148438151a1acf4de749254791c800001c467623e380d72a57bac37d0000000000252a4498f4157e43709c4e68d538286a780bc705888cb588f0b60000000003088cc892680cbd04e06c254d8655feb8d81e4b8b9f1832e81605c8f5603c779908b361c29a61048ce071982f0ae51e389e80834804135023960102f85ae51601a245e4078e828ee32660c412cba0c96fd667be2218510fd80862785c365bc70425f912bb708180721cd27304a84e9fe45b2fc296115495008d0c74740d82902fc06fbe16e34cc869066124b66609c08a88961c7107c51793cb3f8000020878025ee519b213d27367354ed4000000000527ff4ccd5ca4b082b3a031504b7c00004979e0280f0066b720d4104e0000162d034a7b00241a06e305c8304f531289d33a3c0157d9f8cf5c00000000000c3cdf127af304600000c03da9abe028c30022085e8803c5530b96216800005b2ae00000644dc81722048ce251dc433ac88b0000062f91d0c6a694ad9bd40860280cc44dfa2a1fa1178362cf08492a977a4815b7869048d9733ec312d310aca4c0b8003413396c033f83e1408f6c17065472a42fed00228e5fcc40f800003992a71736823ab01532a3d6900c30446ed9eec0ad274147fcb830b09912c4e15ae102af8540a808d10146e0c9ec55500000a317d264170408d73238206a28f40a18e400b7d14f400001412d805caa8bd7f42976061397094ebc4a21dfc430000002241f424d00000615b2000016474c000068774d048a7d784caf300543327114634a4bee28b4dd062c40e4000ed69b6ef046600003cbca598841ef9c000034ab9e8b13f2dd306d500cda80000be5a3a05e4384eb11611e181208c10176d884422d7042b66515a0a330a2d42847528bbed96b2fa3397d6c40c84a82e3f0ec8e1aeec84c714c5d1460846f08210612d3d0b7ae449a0a73c197c60ffc0000000000182c00001a4ea28d1e3888db00c50215c096f0032d90afe727384c90c918cd2983a24f80469b10acc26b200002ca4a0891eb2e586c29059ba)) else (if i < 10 then 0x9c06070000000000000000000179c78000000000055220c0100000b22dca65dd4b35188007289144ae682d9194cdf30008527448ca11427492a02498c0000293680000046d5c053b4b3e892e65655128da7888b990e5680f2309bde8902c037e84b51852bd92ee00000200fac0e371941407ea469d58212272fd541225c060c99d594be30873c4fb1c8ffa106cc00e140fb9792989362cae81402e243d220b1ff8b93009180c7c806ed03060fddb6cc0b00000ac1a40000391f790856b36c9a031e80ff7f2c846400e1b248148c0b2f02df7cc279e8de71adbf03e108208c228d8a0992ac9817494234998f270595e2199c58500000c2bfe45ef6420800000e048e0000000000000072e3a00003c16d4122c00000000000000000001361400003019e807ba00000e6a2c4d3e031d500001825e400001805246571885e400000000000001649664a0ae01cc0443121ef544d20a32c0220ae599d8d66840c3a159e818aecc19ae24870387c2f2ac8e1a08b2a0706a87bb84127061ab87258598a02267129d809f240d5542bde0697e0195c610d88e7396cdc014962115caf7ba21a106f700147ca915863ad232a06848216800000a0857847428841c07b6332fc45f8148e5d233300000c0195615e419fcd2d0dac3140000000000000101ca94bc92f5b70e3f4202fe836e78832405f9256f28b36806f5e023ca2c90880fd4325222c561d74000071153e006c4647e8bf90000000000c48b4fb82111f65642600002704a6090a62e960000000000968a0000082948000000000409c400000000041581a0e10000000000282802104200003c5fd4040f72f304660b499e298fd000000000000001940bc06c4862400000118cc00000a4d7d42d100000000000000000007926900001c82b5c176388a686434000000000000001440ac6b4b6cf9a9087013b2482504c27f159dc0bdf50af98af499319000000000049eef72dce3151e8032c3d8000000000022eb44453f02dd81074628090b1cf94a0830f20000000005c8546318526f1c008110bedf36ea2805e80632875a435ae000024acc61ae790f8f84ee4c97248a9c207ee84713038f7078b5278f21817c9a121a7442fdfe2d964cbc5087fc0dd920286bae8614f802a6480ac8447390bc4c61e6000008cadd86927127142923baf359743d17a000000000069be1a01b30417eca7300000d17e660bda0ad05b2a918b7e24090439c68b6e629734cf738087a82d3616e60000008cc000008541f0222c000000000c3476468838456045c500001a160a0b95e91b900bd4000008beed031900274a1940c8d0210b4000010581343e341837a23be823d0000000000d021c2cf6a03e1b45d4e08c1401c40000096380000120330bade8000000001fcb5000000000012e34807e382850000020f410632400006998 else (if i < 11 then 0xdd34b8f34324220e3c69f4d9f7f858900a1ec46ae84215999890f50e21d489d72140f62ed7256c2e8d8d949ce3019a1f9bbadc18b4a9217eccf7b4a90f07fb4165d3029a00cce12417267362e2fc8cb715d124fd9e2b97baf2b16356172bb16e7cac600477c655582fa8c51c09354322e3c064d4ae829bece098e40febc143f62997063d04dc74be2191e260a13e12b34896c13d9a2a0d05f00ace88a3da1e5c624f0c4bc6e94b8c05b800a2ed04759be9b12cee67bb8c96790a2628a2e5cc44344b0295421d606f357966f098fba996223b20c3f623e4de594e5ec80000213d6d81360cabe851dc7464312c065200382f8000053630000018b028000000000c640a054d00000a21c8618a401818000000000fe08e889200000c2a0941b78cc9ae029d000008594bdc2d800000000000003c4a8e8677a14b36612b033e00000ce55a84b8622db9056e00000000032189b92a940bfea2f4c8cc90901891563415ab0c8e8861b03652e57dc000059af1202b2664a6047f407e9129b0212da401cb82afd211214a82492baa08a5640fa0d8558fa780ee20ec6e1c02a3f0f264f0248e00002d101c40a4525704676e0575c8157c01a464b21c4d549b87000016087119059055f307ff2213dc0958000000001e45510b7680bbc728ed201325841f94652270600003fd284873b000000690ac00fb86109058600001025e788a484d8a00000495a1816be140b605958ad880000c316920f18085ae14686272802147802a1b1e30000000000000000000b2eb6000000000000007105da5bacc05e31740534e4a49864d74b40dc60b9e0000188afb8178f174a40e548522c857771500667f54097a176df139428f5c000010acba06ceb8a400000613e500001e207509e44f321f06d5a1ccf83420000082276000000000784e922a28a2d2c000000000debd7a6ba8000039631917a9010cf5a593017e515b1a1f6b416b00000feba7a2b8a098c00000e13f0d49c000002946b00001c26495109021f00000000002c418a11c9b276000000000020260c014e00000000031a71000000000202df4050d4c777456bd0b77400ad0000005c8b89f7102340286a22ff00000491c5f08c8a627f8129800000000000003010800000000006075c00004080d2166ea0d4000000000000000e194aca4100000b2ce270c81417380000fe58a00003c3dcf75b6e0cc6c0e8fcd4b68530b2071e6c30000009438000004294f411280000d0ff340aec000000000fa008409cfe054800000000145f1c0000000000246a00000084008b6a2308e0000340dec08fc0000000002898200000d26480000285559959f00000044b000003044938bba00000ccef9839b3280c00003d8f7092f2000012270bc2a6e910100000654f84865e983548fdcbcc3800000000010f7e20c9bc3e0d918738b else 0xe6c44c3b8c84280000000000000000000d261cc1ba50cb3040bcc2ce60000141f3b9ae0a94986230c00002932300000c1d5a4d71589d0734e06261c8b858c470f2157c018c0000012082e4448116ac1b608624b370b246fc00000000068182000000000399f250078000039800114d000001c0faa590c196b912943a22d78a08880b4c070f00f85c878075e492b66000020dec3888200001e2a2c00005c0aa80c9e11770485c8000000000203e34be500000010fae1611901830c026289fc4d95c507801c17f04e44ead49128000000000c63228bc9ca697e002800002c03b180e413053c22edcb971079c914cfc843c8aca00000ce56842348c16f81b3ff30506c78bcd7b69138000014212042a0786b6b29346288fbaeaa097743274000034361b0bdb21634a500a850b41445f15ea000000000117bf30ad000002ccb451181109e7e0ff182b08f2ae000000000000002179600000000024a3d118d1e23003e7380000493676e10424d835109c870cd2a86e58eac2ec80000e2035c4ba043e7d16dbf13690878000007024058ab1a46ec000000000212da4230acaf091a6eb24ba661bdc5afd13fe7215b8547bc2ccd86412b20241969cb69a189240b1128cb50995d0a4122671c658c00000000040cb000000000000000000008881f019498a0790c2a00000287d195109143884e3ac1c330ad1601848691a443b242c10000000000000060632a15d20000198fb481e60e555a2e33847cc8066914d3f00a0c374503f4b101f068bf8d93c115d8099102dda5c6380000c3780c5bb2459d6f0c44e5710103b002f616190000000002b85f80000824aca698f8311f061940376e8f2e4a5980306ef314842c580b490690d420800003a3e7000000000000000e179000005233901139cb2380000024ca2294682703081600001a0e2f826dd72f6722224475f08c161b8f60d8584fbd026ce954c20598c10dc0000000004092d8508240c240973c111c40f10883d3175500000a550a413248822a2b0be03140000095baa2344a12e4c91fe14aad22646516dcb28901ce73613e21d063d3d0537b2d5d241090336d022d7258350b1e04572783241603652f40000616ff6333a81720420d000000000100c698cdbe080a12f3625ecccc136948bd357400000000000000a0b82804a50272e02e9000000000144f3d18bf62f5c000004b7388b53c0dece1730000000000710e1c107d42f8e046643437c28f7e2e600000a16d000003457d00000e0e2486f7ec26528741711004011c493dd12d25303e00001012b40942c801000ff9094e295f300001e2dd17c28312924082465d5a4a8d21160c2c2000000000000000617f1a42c9e15d7026e8cb90823fd858258bb0416f14208d215ae8aaf40e1302d1ac49ec98a112fcf220e600809c0a140343c4)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0x93f112a9c00001c9f9000000000060ee0000000000121ba000000000000003145000000c9430000000000c1a0800007818c423c2000000bf2800000000000000fa14b82a9a270b42b9c000000000f0fc08062c0000000006259e00001fae7ac314bef5ba424e41e000000a13d7802449b62800008099c86380ed1881b9f091fe00003c935689490000130bbfc598f9146527f7415b08906397f0303ff0428f4158e42c87153be2ccf85388006c82441e0c7c000008103f1137c6316fa3aa154100001e04c403c8686b828b8180bd4919a289a7ae8e7c03600000091a50000020fad05913804b308860000002c9800005079bc8fdd0bc07078592c9f843810c4c0029c12f1ee1410422dd0092b0be1a25000000496de8066e000030a2a0b1e75090c6563c4050349cbd3314000024817111de128124108984dda8be4f362905a0f11e9114a3b2e8ec521559086007c0820ba1fae4544ff1feb2e6a60aeacc4b119e0410de4181e4c6da06aee26dba48ed4857e8a78814ef7214741806898c0079946808c82b099320000000001c97b4013720b8822dc30a488000042d4c42dc58977d9369420ee86e0800006166f5202e0206144f700000c052da258c000040468d0c3ce1244051300000c47d924b8d8273000002b0780000000000000000000000038463742d9a25ff2430c49cdcf7691103c82413004e823dc0000000002400880a47409ce916cc41c400000727c200000ca6ca33edd0ee4e0b4bb974d484f41004000010452e91e992afea41680000615eba02a820e5f048d492cdf0a23652b00000513cdb0bd105aa1c91f58391867a3a0556b979008c770b8e0000000003122243187a53cc49de4294a4243781e9604b121aa100000000010c2c9846c0000000000000000000134ace049c49a620baceebb5e013b487b80000000014490c000021a6a52a22022250d3c50115c2f86243214910a01b790b400000000007831bde63dbcb1a5197d445a2c4e1451d18a610000000000854bab99000000f12b5c0cc0838dc15e7d35a80000388e178566f920800002f97a8000038a140000000000000063045258260da98000052ee800000000000000d0f7890270037800000eb556000008990800002030ae1e2acde300000b281a00001f85c213408666f055944beb5955a1274c3daf389a72364f01764c1b5d4a7b816e2000011cabfc809d73048220ca4c08ad1d4220b3330ad8a10c3877862a0000170bd400000000030ccefcac000000000062bd962480000000000d04cd61d9f01b320ba2c1484c600f448db6565b7295a5c908859de7be32008611ab850b800004047e48fae02da097fe605a3203fde2dd795d5d0dbeb0abbc4a660455106eae4d4ec345182b0f0752fc3730b7c788c9a2192a0dae8820709e4988522472bcc58731db02eaeb86380 else (if i < 14 then 0x212a7dc2f0c150840ae82c85268fa04eff0598829a8a1c4403cd7e7e0012af20abb8aa7c1190d011dc45f5890d10829a02fa64096c12f88419324220444dc018d85d7f32dbc8cc8000048aa0b0176c1d86d06a01a8e933e2263ac0000000008e630000000000607d40000081468000018441a1705606b6d4b4782990000140df918ec915c582d580000204d7875e7428fc00002c49b58be000001225aec9158000000000b9d00cca1d8490a21800000000001512c00d07e40714975a983958608ac24e0382902d9f2c66c1ed2450af168e00000817454a7539158b06bc0000184fe48bbf000000000000000000072e52a423409b2000001027800000c1a0d1952a02e4000000000104ad410fc00000000000000d273cc885cb1c5a95c96814ae1b03cba8800000000000003cbfd00000eebc600001c134087e300001c03a42a8b39b3db2e4c0000345590129040489c17a6cd36b087900000000000000400c953088e45f8c29fa1bc10000042e1400fd917829e13725d7158f06801d40c84a0f4e6ac43116862a6764a05c9fbcf2bdf08950220fcbe639ae51104f6054e431d972d84273b824634be961a89231574238bc5d08f31fbeb77a0d81a812506814a1f781a7f42ea3041cc2b01482ba4890f11f1511dfe2e9adc2900000c2fc4ae82c4a72d19ec02fbfc1f65ca0ec9086f414ec4d8f0590a8a9e52ce00000044d288645be20a004e58813c942c66572000008271b1551000000000000003039a00001604e00000000000090800002caaa00000caacb240c8000000000000010121cc107d936e00000000020abba9a11b14542155918f531991235662466805c520694a67d3c613344547303c82aaed1710453980000708f0465d583240000072f02a135cc863094da0000000000000020af400000387a80d25d05c08442162e4b4cdf386170000185435837e409a60000000001c4725833cd0a0c282340000000006378aa418209ea981479404d85a504456c75dfc0993a00210297c875192baf10f4dcbc5106ebd016ab5fa5c9a8897796118a0000103d6f9aa20000000000000050309000004607408dea929f80514e5f680000691b010726c126984030000072ad760e90853af0788000010571c0000099dc200ade09318db919ab2000000000000006065f616843171a434b0000000000000028153f177e70980ac7594cf58000040fbf007dc0000280288324de4aacc369938bff091164f2e010ea83cb000004629800000000000000856e4000000000800172456ccb86c11dc0000150bda0886e920b5cfc2c26f6848381af3d0b4e00000000000000a2054c155c811778bf01466ec18fc000020192c1444409d50925f1ab700000c2fc4001ba14bce64146189c4b00f90ca9330702b8d81c0b730b30d4a502cd43204094b0c785a0ec38b61c else 0xbe03b0000018a9870dde045ec61710000000001e1b5400007033f6518ee433d4db0000000000180da6c88810bc70000000000000000000b29fd800ec00003b9687014a657d18822000000000185fb6884e505a5f37e540770c538000004302b652d400003a0901ebc1a0efc03a1fb0a60070446ddc80b741948b32932551ec5bd3f5cea0d8ce8f34fac4b14f0a63b18655085a38529ee232fa6251c554513e6a1755a0725042c4186a115fbe0888d1f91c316a285400002b8cb3924c00000a2a09020200000d260a44dbc00000285bb314524a3d208b18bc5721a5e4e8800002176f22fe9a538004cd3659442c19c600685c24183666562459d7440da92287297600000c076c975eccb2746c0a41dcf8715705f2668e5044f463bf52500441638cd981300403d2c2d64033600000000016655400006f76b7079ee0468c5df113a738180e46378b3c80000c15d9c6f9b834dd1159815b631db60df3f037a2009a000008d289784400b28e213844ff80000e107ae43064503702512308d02cab0d004c5e000000acac308bfc72f9d0a18d02de025b80000d2c00c5d7e4565581cf42e283cc3000000000000000c0af0000000000411b34006c0000000000150c41d4c45fa513e822aadc2ec48124a0bae9097e000028202b92460000021ce68ba66051f8207400000000000000163e000001a2f4c92182e5cfa64618ab3b0a9300001010c8000010bcb320ba00001016a804c40000084947494880000f21b6a22a88507289a978d22c0bc80000295992214200002c8c56800cb2ba8c15650c2b9b21d51650000000000208b670bb4719e30363f88bc0000000002c0d1c444d207aa05e40c38328b2bf04c46527c4b6e772c44083c85a1000002993e00000a089ec44e38baf40a106449680ba3c1f68291e6158e0102088e9e16d761c2c0000480f620519865100000014fae0c3b60bfccc8f51217624f000003a1289f2510000184755403d3794100001e153d00177010a625eae0a8e496061733e030225e1db958f8343623f306d2ecb4fa162880efba514f4cbe894a45363820d6d81da111f3e27b806a5608fde93e458444263ff88d98b1ebc0baad0b3f0258699fa115d422cfe85ab4022070a2aa4a9142f3b077730e1ee4748cc040472a02c6fa5407050f289d35274a20c20b96ff028f330c226c4b898fbc8add0e92e4beacc6c389f020c384665e5b4c70bc92136e00000c2a2c02ab00000e68c00000000004441865ce000006179d8e5f800000e15500000e741e0000309972a3db0000000000d95a390aea259dc01cad046380b6923b521a1fc002602a4a2adde0645489e519ada465c000000000000000000141eac00007909bf87982880ac829f0b8ef05dc64ec4f8835997f7214e446f84aaad10bbe3009bcc1a99e53a20dd1386a5fa9c55629674)) else (if i < 16 then 0x53c5846101b82d3dfcae4000000000485a4000034d3d8000000001f0ab5c3d1ac323e07b101b30019a791c0e25ba46318802400000000000000000000940c1043f01a92c165a0b36103bb88fd08197972c26323420b3ac4c9b13e000000819b8000006367000019162781aa027eb3e5c20000041b2d921e7611a68ab70436e14b49056880e7881dd8000020e8a35548e4ec0000018e09a0654cd657012d6081600003019af405f9ebb6be1468a55919875342f8c254c874499afbc75000002460000000f274326b0ec0a2e8717132080000145f3896239372e00001c9a3796f5711432dc960c449068f9c780000020238f92fea08e600000000000000f2f19c42530cb88904660c4d0293101274882a6b28a00000000000000907b9117430530f0414000018c7c94b55486dba44234659d81f9660f800001a06e800002129a0000000002f97b91231c0945a159f45aa807fa0000128fd5c006c104180a28000004c741929482b11c0f6400003161f82d9ecccb80000602240000084fc2c3035a3ed264379d6f3fa2d5880e0000000000000039266417f306b8e09087816af02469d1bb4df8a10d362d79b1fbf8a4608b9982ff7261018a6b494f2421cf048bc59ea99a88d0132e17775996987ed00001a8750400ba97ab4343d056ee3ad9ca1ec609a6c6bc8014f706be1136305db9c26348748a83f0c649e0d4a306d8a05cbfcf324b81f07f67034dec24a04d948194a4145009288b6431aa6a3649663ee82c8b0b7980c03a427d43e961661a0befe6b7a880580000294a120f6883c8890cc1051ae1982c12e7744d62c058653e0ab067392d094640a6c3976800008e3ede80f308bac86ff20161815a5b9601890d42a560000078142d29fb208e221c590f5b0616c33640000301b900000029028542922e5d93b6f234c016c4000009127f0ed0000030c303c2f0d0b2f80e14000000000000019d70d4d6cee29b1057c8181099f9e31f91e64b061c9806b80000506730420800006899500001c106d78032a2aa014f80000182998000000000383f0000000000e33d40000181b9918cf6a532c4cfe20511b08a0000000001cc087221cbc88188ab8c9e0e044802b9821ea40000180b372997659e2c31e783ab00a75e46bd8df9800e73369585391a16a1a8bf82033c268400001196100001e55ec00006058ff22f86410e00ba80000334f2c1fa943d9691eb0000000003caa85037c7111180801054a7159b8287e62bdbc4c2f0293a0bd8a2ca5827e80000320ea654bc000051a7e18ed78500c4b30013975278dbcadc0000000000815e9a8e90dd000000b86300000000006942220c6c00000000000000000000000359f700000e257ee28dd086291a52b2b7e00003000171310863a8463eb00cc384dd533686440b1845de504c20d401d7f446400000d2db else (if i < 17 then 0xf3115ac00001e879c01360000000001003a842160053b32ff3e62750c1c58a18000008568c0000000000000050aaf09d5000004258c00000000048bf280c7de0e27205928a4ab26bba21ec00000000000001e1b15025030635536f7c248c086f98077a2fcc0000348a80000000001a4186caf23c2fb4015cc28e800006857683228266c1d8faf09d800001210060bf679bd1702e004eebca33092d500001a170e04fde12620000000000c3f13a852c174960670000000000b071e6612ea215114e23ecf0000038b9e8195172eca40aa25be751899b07da000000000794b1704b105a940000117ba72bd400003c447f1a62e279ea68e28527585aab0c6784cd0f989c33c8603dc00000000009320e4287e0db8f3f49814f20e480112fb84f6954a123ba410fccd57e8553f21b0c6e25f07f80000000000000291ef800009367600000000021717c28d200000c11409179000012528bc47e903010000000002406e80000e17b000a15119c80b9cda52122b80000029960a2bbd8cccdc536ff5b942820f16d8000000000e832c2cf6443aa08be50000000000c01a80000a0240c206783d38000000001642564b87e074e42cd1e56860266e0399221d465af64291c143cc0680c59f84b7068a6cc2fb640d3884ed98b7d6088ce5c130105e80e67138dc4fb5cc31a100ee376fc210fc1d8a87d3b162986508c55d797ff32e0400000056d2168c70fdce2bc080908c2eeb0b744571880be49a4ca2474a876f8c5900000c6018000030505d096680f66a675883c480000d2644e2f78d3e7531ec0038ed4db60d7c015a80106ef094f8cae80000e70684592108c7114370000186c570989892e9409e3a4e8e0842590fd7258600001d10c993b40013d0436685317175900000e61eb0ae7d83b3b206822c660938f1a28f862030abc000051ac7d3647c04154911c16ea615c960cabc94ab051312b48a45a40000618bc2244c24de4c2bd121d9c163800003438ec867fd2b1d226fecb7240be6000012c2204cc480000b364c662ed19965a2b6c4009848c0813e9f3140251ad945b410c2010ba03f26172c0000001b900001a5a7088ec000000000000000cdba0000030647229980000503e95d0793a2dd605e902e270f700000291051078f3117d000a4c5e6319531018024f7c000049a6800000000010149003c3ae20ea235c000000000000018081d307b0000000000644e64d1591b8e229aea6e844068d55963310c0000001ca6859a9342d02c76c914b848f0000000001cc71c82bd72be510435021c000005316c808f400000c2c2203540000241d768425f2262e24eba17e71421720a3e273e89ddb81dfaf03486c5c000000000f068540fb1d9e741af40000180ef1d04e00000a33750cbf800002065be211e8651608251096e0c53d8124ec99f3931b42999500 else 0x8ad27a221a720034c91cd524e7217620121202cf8113ad2110000040a8a6325d609f3450a1f84f0148886b18000010376c2fc282886c4c80000000001a46780000010d760c1d06bdd02a418930f08de316c7ca7e4097a3040d60797e0586c018c135c00000433580000f32480000000000000012b2480d14f4ee800003055b1d6f98bdac90aae13a2000024517800000000066a190bd23042f52ccb65e450007a12fba256720d31b98ba18310000000003d97a0000092d0b38091c0ecf1356f2d2f044310dd90820251607600ca4c978959c6159c5cb3d4077c9540a2ade0000231b6a3330513159026b80092946c030aa607c65458c14639370684fac0000691e70000000000281700000121ac000020d78000000000150b6c0000619d2e29bb155140000683c1000010a0d0000000000105cce543c000079b48d666d702eacbda1082d60a4fc1dcec9783173b709df1179819f270bf620ed42290000000000083797819f640c78000012874828ad817a110ec506de0020c72bd80000000015cc6502e73014da2cd800000480780810b082fc0ec94381a1b0ff0410a2fb2c5e301775ca128dc022c20518742792f8a1ff140e5d169b6e5dfa5627c08331a102ab29e621e0349886af48576e64c001757b2aca326c0c2b58ba3009dec0b52466674d112d3c01092f08f4548b9004bb035f8400ab016838461f2217c5cbf05abe077e1061f218b6cb4b49303b3262d4a6c01c2793a4a122c3284e0d52897151613ffcb6b11f8370bb827e7716c86162c8ad602d26802560a52e1329347984280e043d382f342e0b8cf488d5810183512ade6c07617880109d21b4e5b44c8623f3d30331920c4205c980485512be516d2c468d055e000016570344c358982e8b9ba52268a0f4f5b5d37d0000010900800000160e2065b11598876922921e5108ca9ca01d1247a8000028bf4d84cba2c1da1c4c4ce0e084100000e1643a05a489c59272506c89c31719252a11236e7d1e23b10674911e1828d4e18ad83b63129d813e0405cc11d64110a028b24b63ca003e0bc458aa00c2d8000020a7da16480000412770000006f90000000000c060400000000000bda30d65e6209cb0bfd59300001e183048c7901616349228cd68229008f1000000000239f73c2cc0000000001404480000b2e500000004c7708dbc013e000020113610e3c20ce00001cb3d00000c019020853c4fd7963cd6136008ec0000080de000006cfde02c2818d39285c92504a18b8b0a1da6ce05474000000000f2c10056b80000000000000182a540000000000000000000216b10519e2fc9a05cc000000000000000000388c4415596302800000000000000c369c0000000005686430455c11d6c3c20000000001f028cb8562898df0965a1784c4daba3e6c124fb4a68020639bc80000180d28c2))) else (if i < 21 then (if i < 19 then 0x24c8c20f244be8856b0000121aa60b3e00000622b9415740000217630003c404d9c989783c70000065ddeca6e00000bd28be212800000000053508e1ed6000d309ba91766000000000000000000162fa00203800008306920c940000109e3922000000000000000000000645380000305d680e4d224a743ee8000000000cc261385e98a8d60139428018d8fc064402cb8c546145930034f00000e60874473187f882f5386999caf451b5600b8d41170000010beb50f1a0000000000000000000000000000000001443a000000000296cab061800000000000000000000000343a3a83de30bf8c2a880000418c7f213582682c18990760a0c5800002a04f80000e0046a10d1cdbe00000117fb828f0a16e79900a0a02000010356a0890730a5e4370000060480a2abf7840400001111d92bb606797835d6438f52bf4e4ccf0308f15bea10a921f3800006e8c4000017d752c185b178623240246e3c3ec7868000001e651a714a8000008421c07b74ac50c2d1e02c422f218b285895c2413e0000009591c34a0256d4527a29d408a206a1f064b98cc2a00000030ca00001c3e00000000000000000000516c10000181d7a215608814f12e000001a9dff99f8000000000000004c0ea3eba4243f0d9e4a931612a1742f70000000000663fe000014a8709a87f2c6518ed68c3110269000000000188c900000947e6c42768d2aa30a7320dd02db3c1e8d138a00001a2d13a15b00000a290f4025e033f0000040a8f22423cce34819e013e2a668d822f20af252802000018958e891200000fcc00c004a857ed09d95d1da08060000030229c5d9c184ef8503b007546d34031ce138d128b8c88014c5c80a91febd55209c833980000b67aee03f7415bf18dea2927c21934c8ca475c80c2501f5c40f7a890f807c870bcd491ee92a5124e5a2c5ba0824964dc0dfb0110808f850b2d1e16104d544b2d718fef35aa01293082da80a84139c2467e002c006e5d0040c58b28426f1037e09c3a061b02d248729620b9e12a90a14992edb12290cad48474010cd00000048f00000793c526fda64c9800000000000000047f3021d0000000001617f80000711e30000024870000045674b85da000000cf380000000012e84b0a0f800004e5799cb1f398831634f23fa000024141e139182ad20000000005069900001a18e000003c1d00000000000000011925a179de2db5483feb8b101360445b400007174893762000034b1ef61b1d217044b8243238000000001c0d1808b7916bbf14fe806bc000000000e294e000018bad3031140a4ae11e5435ec0085b2d8dcc2407992000000000000002396cb0a7e115d00000000000000000000c5514000020a5400000000000b058000092df800000cc52800008311f04be48b2ba0573612fea067dc48e518d5c3581e5f8c8bc5e8 else (if i < 20 then 0xe5b608040e8736f02d000001087cf08cb417ea4669581fb09ad192ee244a230377611ec00c9226162f97d905fa221cc45c18110dd6674828aad84b0aabdde443130bb053b10a12d072721337c87d6c03a80000e0b1c21eb228f508a43d230d05844bae88074c0156025d4f8968f9552a14faa692800003071f88b78c56db4a2fe0b45a01f8000010c128080962c87b1d58446c4060bb85800000240a800000605b6a1e74b96ea99b80000000003c8850000052de080bdc0000287f202353e5766b92a80000d0d2200002f84f88ab500000a50aca23a59754d2e2400003009a308c0000000000000000000000001e61238385485f2c3426000030b62e9030835b80000000005054152caa66c940000795c4c6119c53190abe58817001f6864b7c55180000b2024000038b796177f000000000149092165452349a251002a5e333120464fd0a8004d0610083334c27848808291200000000001027598b3000000c6026495400000b272c000000000318e1a225ca5c2bcc12000009a1f8267dc0000718325220600000cc836b3d0c30ede00b0504b80000236b9e0fa000007c5c73e143c1e7b301f00b625209fa4cd80be6813660252dc078e0bcb875b2d104c006cd6cf0ac0b1e16b80000151ef4961200000000028aef800000ef4e00000058acc960000000458c80ae000006257400001455b780c30a1816177c000000000000000000000000000000000000014a2e80000f8b76916e3e183916d7000000000000000000090aca660ac584b00000a2a0482fbfc2914027fe2a4e247a2414d407ae128a0e624dc4390000000001ac768000061287809859cad8886a0000000001287cb888a80000a0003a48df438210551b1366e201c00005208b7034800b7b0bdc9053220d9e647ba6aca818b1863a1e2334c8d7683580000100b0a0bd6db0ae32a06447bd41a680000b47a6000028a708742800000000024366f93f6f1300249000000000000000144828081059895a0cc2000010962e139573621e14af4cfcb8acdf07c49e8d50965114db9f3b00000085e7b9085b11a8c2796e8d2718f1f2d23e240ec0f58000000000e2126c3440018d3300d060600000365966041d24c1c0000000000000024d1549fe00000516d20000388b631b1964670223dc0000392a0d0a2c000008170a17eb0000165ef00000093af323f08875401a8d9568d04e8a439741d1017f750eea30c88c5b031615f110c7177c4d640000060962a6b2400000000000001a02c9c2d63816730ae5642e80c8e61769c47dd46d56cc4500000210bb38a6800003c03f1321a82ee0abf0c96e6000000000000000000000000e15280000000000000000e9c40826870d00000061240000388018f3a8c2e6071de48646ce80f4167bc5e180000e0e5ec167d49c62b3e602d6c000000000602c52 else 0x683a5786144128704f10820c642f73351964af1c818d161a132d48e3204274300e28e175a29af8262808df6166a425974a9d823c860ecae3006837c01b388009ee60f982da8830eb20ab20934021b2b338a8001420d042aac8add80c86247444223896c032e7fc0f7e03fbff302a0572b094b0556f8921405919d424b959f157532c2960bc6ca7fe2a1272ee70c832424e580d3c0ab69cb0d058bf88fb00a30cc83ad8e1140205080c6060b882c8000030aa825f454bfc793b7525f922e5102e81a2b72125b45f6400000000058723ce08cc0af08b512335901cf590b9a8a3400001444fa8039b12afaa1a485d924593800000000000001bcff00a74809fd01266834680000c08ca0000000007855882e78000000000000000000000000000000000b04ca0000289713c02b723126207ec091798700000161e8bcdc300000f073fe4ff40000215170000065f570bb93a095e0144021e288eca17a3003b7a1c6acc5638562704f7a4b6400002807d21415e2670c5730000000001c5430000021519108b2406dbc0f933a70d04d640a4090e7f928ba316a482b24c87af72a933aa60b03ccff1f0adc47ca88bfb028f2e0e510adba8caf0310882e850eb980a6100b0202a50817c000000000398c19345a0000382fa607a600000000023858d888700000a2d9f488f31149e102a000000000000000000121a771050800009045fc6e4000000000000000b0b54a15980000326a400000000041bd672f4ce56e18ada00000f29bd842f40000493c0214214238c013c239ec60d89647ea6166e332bc257be130ec3f27f470febd100e39c0929c46fa4fdb85b43a0ff4903cc154cb8e9a02c0b107e40968b9620000039901b011720cfb821ef9923a095dc4ba8c4a3e827230d6b61b4800005861362e232597e8255f23dd92dc2462f53d265151f92afa4206800003987320f9622d8d836561a73f0ae386c69d464a06ea233e600003a1703859d902ee51746cc358000000001a27047c7fe9788000004216d8979800003060e10b4c000000000307ca00000000000000a16b64284c000031571412fc00001504200000212d1051d4ccab00000343d184c5605c7995c1e036826a088bd388043c2bfca51c78b45b18c4a0b2aa544f84200000000001a194400aea96e5626f4846a14a63f9449032680000000005914f000014822000006838d912b2000000000283640000064291741089456d283742b008c1d5139ff8b6121773026c031e68439c0c21ed15658881e2d6600782c26e000006157c000004365a19a803338000000000409d200000e1b6400000000000001b240c0000000000000101a154a1b00000134a00000098adb0ba7483ef26f24484600000e2b53887c7ca0bd8acc00001c04aa85cfd09da000014e3240000596f7fb485a5a080000480fe72092)) else (if i < 22 then 0x1e040da089bc4d6d443e5064ed29eba63400cd4895fc40eaa4452a00c81c47288b90c5636099df8b866656e44e1905598431122d35a140bc0ec41871737d7a4050c325e808cd0a5d25ed88961400bd70de946e07ccf6c989af029c0000000003199470a42940fb427d20297c0b0ee2970044aef0c1c133fd13fc8b46cd100d0e9b486cba17d7820d12fea263694ab32122ec33b5213414a78e0257f4e4b05d3583e8d813ef277f61228400281a1dc455602d900000727c1316bba6cf003eb67301826edd4f1f82b24110822e1000001805f00000711320144000998000080cec0000305ac7165ee09d5a129bcab86886c585fbe117d32a91106511188c5e7c42947074640f03050cb42df891a132664a16f3401fc0abd52ec1c646d0b187a09e128ef454fe0d5af947c0157800000115780000c084701dbb40ad0000000001904294204a97c5e861cc23e24d6d393610b0c990c2400001994e343db622dec532ab3f25053f6435400001903db301480b10615c28b1032c4ee5c300000431cec33baa17818094000006077d117aa08d8a0093b0e4a01d6f0b69042d81203a0000342b7886b080fcb0596c000000000328de0000000006085e00001c14e000de0000088baf82aa4d959589c7f2610852b400000114b2042b9830302ad39b6d0000000001417f00000624280000284eb60a5570558000033ae2780cd50226d0b8c00007115e12c5ee637ec03f982d4d113422ad0446e385db7856fa09c511f8d815192b27a569c495f4198f129a60000005866058b5365102e1e98ff5d8c4f2f6e254c4000038507b353e20ad5c54f80000b36b0000000c538000000000000030b88010fa7ebb3a040000000000040f89e0fedc83a695aa023e8e5022c5c4c95bdb84ac0000000000046d20dfc40e02812e8819d72613ac74e80706953a1145c0000100d3d936c00000007dba1581124f00280911b969dc503aaeeb96000020477000000000001438000000000c376922b570c473171fa0211625a80000119f4000000000000000000000001801ac000000000d605382ffa83c0394260000000002c90ed9006d33bc8678b0adab04082058c219cb00b7f13f9f152c8c05c00001003d604d488f3a7978a99ab000000000022f660ba8311f404e618aeb0000000000e59ec59fa8806ff2f50be0e0cb4498038525420000088d6304fc202ad441498331316a7a0bf600000839000000c310a0000380a12a3e80000002d500034000000000000000000000000000000000202d5c0779a2f9c049f8000050338936f4e6377a2ec00000ac3382075983caa8a6ec158ba6784000019b5ac17ba000024d1b80000336a565e6a8c7611bcafe71d063b6803c092db132e686623c4b7d1ad6f211cc5b39c04c2f2d6d46ea0cf5b8b404e95430d40c686aa186688d5e178042f8 else (if i < 23 then 0x1be42b765561c5bfb15e5bf2a000002833c00000d157fe16d88924680db0000000000000000000901740000288ba0000000001c19ea90fa21ae11cb2be4d0545a41b21cb1039e560b414328b90c0424f4394c01289b5b047932075398024102b32b458870a880ad85206083be1eed4dafd9664b2e88662e82162147a1e47c4c4c518451094cff2bda40a26d9fc41970d2c0e255ea01ce2118bd3083e02ac084ca8728b11c00000188a3ed9dd62eb1c675cd0ed7890b00001825dbcd6f912ecc0f9905c87cde9e89f540cb9a44270418321f6063ae44ca140d46e29f11572e113fc956f83b54f2090876049420f2d0a074282ce7c8e781434f0ae1446e840589076c80af000003446f00000b0cd200002856f00000d106a6180ac5622929942253e47b7badf80000316a4468ba0d1aa0625d0b2c00001049cc8b0f0000000003cc778000040496a62214912000000000006358000000000000016c28d84a280000e441142014000000000415daa4fe2c433a9b0be21bc405c40000079056289abcb4f41d6800000000006d470c4880000000000000000000813f00000e5c1c000000000f1098000024d7d718cd00001c408cc59ec99bf12a0b86d64000000000615de00003cdef0a8a9f141bc45e98268d03a8f176d814b580c391a31613ece41c240109125a000000000180486137de22ca0000000004b3cf00000a49c0891380000961a8000000000242d7903f9c1cc30858502032136ca298f02ae10b9db8601c4c2a4c7a11424d353c60edd8cd720af36097b8820f438e080602313c5d6e80000592d72046fc4cf6c8ab08a4f00000c45c0000058a3900000251634345800001332b06cf800001152558bb595f820d908019bc232600001c52b6022b100e80000081e9419d460a5404f24c02bf9ac40000000000d1ec5381600000c2e58ccb1592367e57d410c20ba2db1cf24575e59dec24c0c2eb947c090ba64c2d70bff0000146a028bb500000000008cfd18ae188087f0bf2843e0000000000b816a606c842e1009dd22077b0418ccd5490f2030da000000000401ae0000046ae00000388d672961e5e7283b10000072814a056c000000000525b5a5119c2135c3216ea1444ac2887d996da0000044000000000000f24ed7932c000028ad0ef0a622b0480c4800000e635e4153052f799a2f0f63c52ea028e800004128c920c8c9c9c12e5d227ee87a5ca0d39a7f10582624bb8aada0a29ee5a444911893a80000f220e4012a835880000410417c2712185989abb27380000084b24c2f92f184a2171616fa04565e8e4000024d5001091e250600002e18f9945a00e44824440000000001666400000000048786da776e22317a3a488eb1131362a6ee3d68000033218e2bedf861184000000082332c4adb0b2362faf22d30007c9812ed248ae1392037 else 0x1a19ee09ac0000000001200388c03d730f42184417da498d1970130741a558d49e5415290315a000000000687dc00000e1c62c8f21059b10e7dc577185640000020c94213c24d904843e00000c43d78024800003287da1dea8079491660eb8ee0165cd8f437ad024f20000000002137fe40526454b50f30047f2856200001c8fb80000f135ac0681c3eaa10284e215029ca42469c2bf000000000003380177611024c075758f4b17cb00000402a4000000000d949a000000000502eb0000000002ca75953a672f9fc65bb02fa80000c3453206a48b4c719ca0000000001104c000005066c00001215a10759126946a7b089ad7169252096667410d2071a3a32d99e4004000078536f0b0621c1f44cc00b3830ef942d99c260e06ac70080000020b79b8158b26d48137c023ea993da23fc0000243f8999724101040c49d8fd8c6bc8038bc6f654186b810c6132fa1796413bb538b8817378011895608702c0cb261a79422e901e863527fc7eee0501066a00001808fb05470000020889a1c594968013473e56400000000000000f0e587e937c51f4877b2126a460ef494d8000000000d1422ccac196))))) else 0
def signed9Look := lookupWord 2385 9091 8 19 12 3 signed9Index
def signed8Index (i : Nat) : Nat := if i < 5 then (if i < 2 then (if i < 1 then 0xa428ed299f7004836a646a00c1d5182893ba5077088b065742916666630dc118a1c5b219b0000207a4043c000082388000000005c637611800000000a0ed0000000038aaee005aa2af042400000000e21f2129230e1043130e80000149d96119ec25c21eb842d625560ae192c08b7d8116aa6ae15d3c254e01fd320599d4d814000062c40000200d8256d403bf962f8826a1a100004812f4259221991243894d83ae823700007021800000000300e000000000000040b280000000000008245b11100001857a62f60087c0000c0525074f9574000044381e94e81740001628df0cc7029ec350c6336102488305049a8c2000041200cc6e0000128e8c1e844ad7c400000005bc01a08169000029706c84561ac0000000000000225b51306e2080001a47b000040186c9440000310e000013870e573000000003891aa5c4420221320a2674120426a493b48326c8d1424c91311112fc55e7083307f40001a52f4331817e4a1b7821720111860710ea000000000000000000000304b706880001316000004410fc9afe0decc1f316a2430be16c8005d11140000c202e06bf03fe419d2902d323f532903114417d249b2378cb1505322137d028988436261d031e81c5625ce1b2925e9331c084e2c8ad28785277c08b857d6422c95c00941866c922e283d6cb910c0256802c34ba84b418c524e490cfc81e21512250f05d84305c1b9ca4ac92150aa5bd2ec2e1520fc0a4aa4e13324390084a0be478c0bf6084340d2c0c89606915be9093201142bc0000344b001f0b105c02e8022424c7728c082d68355c1c54015f00041d60619505021001706b850a1600a03020008030085001f10a12362802414a4d84000c705168409a1c1018826581c5181c70a0030c0702405844e004be00080214a1411300010820630245182c20304000003a1c0040c080000a3400c0c70183000c19100145150010486020cd90021c70b061800900200801404202042c1863004987046c501101cd82262050b000019500084060004008160028a365c0091804180000000102000800e0c80206141002c040823e0811900245020c0008002040056a0c1000a3098c1040f8002b81060c0009840283050c00805000003904140000200000020008100696a30248e0e06100121614100044c0810e007852808bb50408b8204040022e78300021c4a70010084042010116040820a09080001c100001880006041050a3801806247010214a80040000008288810a0408408200083c2c0800008500000c080260c7ad06045810e00a8300000810c00084000c2051000080080018006180810600a000c0428116100030c04d000e0c080002800206001000214080022828706007030004081020038000080090000118001c00000000010400f0004006830038a86000448400040000400000 else 0x28a28a0d041f4b411800014142000000002e33cf80e85cae0396054b0502243f70a8795928a18e1fc6445396b9450480dcc86e800000000000072dbe1326c985c0b30000388aa023de4d3a247141340000e1994836800030269c4bb41045153b832380ee0000000018a5a2528f0e68000388d104ad0000000032818b029028180000cb6c000000005f1354193c47f00002847000001d5f00005135bd04ba27800000000388741419a127e873cc1356078b26f791d80001210c02fb2072a49e9a14f82e98000083d1b43200000951d42c98104b224107ca811362060000000038c9a0000913569516451200005220682628058000000004d42400012420609a816c8036c0000f2f18000304c600000000423f981c484b90000700b4c2744c225090a16b00138d045709680001a97644010e34006ef992e000000000000000012c4400005a565c983c8699c28800024195280242823054c38f578322613504e6599900020000000000000000000000000000000000762ee85240000485b4029e8a21c9520000000000000c8ef8081c0f880000c482000000ed882f80000425a9045c01d40000440b72541d147a1e641570000000000000000000000000049cea636000000000000024bfa25380001817361ee74059901c00000000605d8000241fc014763209713d010acc200000193f400000000b02b771b58457c52442ab287bc413284dd10b46000cc31684169121380f558f6548cd27d8c17d4c08e0cfc0521340502bff843822c5879f7a6681af0000000031a5b9d040c4a806ad811c3c5d00000000000000000502ca082b041d04971c30601d00000e117903eef0a1c01c8285f28d1967b0b4ca8d7c134586c0010524bad0466c724b814e5a100005824ec220a5d0000000003f032000000000b1b34b71058f00007031383cd60e10000000000000549922c6e007444c5e23ea050588ce48fa00000000212cac09f819a930ced04fc92520310000000000000e9a400001231c40c5603e614928a2cc1ce00d4e0c03c617c2dd264f027f5961560bba442322fb80dcc9a54251e272160e000000126a47e694da027965260000000028a022473a2120000243c662270000213e88b520822d0f9b19840000e0909202a1749807e6225d006a5179c98da1ce4c46716ef4a42000000006972400004531011c380800000263c0000704a1015c81ff0000196100000213300000947cd008945372280151a82100623b079112540001014c1e920000061b870380000116f743660000a0aa80001c9c1a00ab01c7b02fcb1de56b40b69839b8363418d908d1530388da000000000871b0aa2215e529ce13c5139280d50000281280001a032d0e2186a44087b8bba051d11240000612ef20cdd0e14852b01b82d9d156c00000000401c800020b9be840229f6b00f886) else (if i < 3 then 0xe6e80000b8f64880e0f6188e941ca20e4d2d382082892040b8201348346c33c00007065d70db8a91824e000030100a0d8e14a701180002b0854425000000000c26da222a28362402815421a5703000002005c000000001b1180001614e82441863983d7e5c7f111c97380001d44218949a006c1e7f18482f8192600000e862de76e86408a1c1c8800d6f173d4392e451e00908248c20e814090a12837f287d3d85f12f1867e4acd60bf7279b88f40000000030a20c74bc9b880d85423482c704cca04de203000000001e4593035410c90010a4a653282a8b782ad84bef61f8a21b0a4fa284f32fa959c43cbc0443082dd1860d0625827edc391b18a7f045be04e984bf706b824d764819184c9a1c27a66340c220c3b4e1f7762280804c8d7a162c017f0a33044dc1ba90a5ba00dd84a5040ec70387f889ec623c5106fc1dd4ba9000ff62d80003ccfac21df2fc0985e047fd848210df96300001014db0a30000080260000042e10a4241c18213f0603d20bfb7a74d9000000002c2d40000e2d5d063e40e62141020540366409c00830000000000001dd840000282520918607ee81b7233043ec64cf00a1800024371a1008062911e800000000b2ea8000000000000a2d5000000000645a0000407716395468460ca003bc4486e06b90e1c858148a8459cb05b0040a433b84ac0000792f0000000000000189d002f31001b26580000000104e200007e3290af60000213e00002496c000000003827c0000046f22bb415120a10d0e17116795c9443580bc32332908d44a484d53a1480000000000000000000000000c519912e80003c2760000a2ff981b78c352220e26180001c0ff215a306df02bc00014c8000007920e412b813ede79c94e2a1c721c1b138289cb018c00000000303d00b5e000000007512c8398a079613b3211e410e0000128b8000340cbc4ea60b9f14e94cd76c499248f571c82e13853f0db80000492c0000e1168000048940000a29d800000001d1bd0028192074b49c51532de0000142f784b471321512309c6e05b00e438648c8af8033f26d800000001040da255a89a40000000062172834b0b7405ad3013f926d8a01c03a7201b881c000005cbf2e029a1802f51c270000189b983f1263af004ff0de095405402a2e60970c4484c24e0109604c60acbdd22058384dc83a800005e30493a6cc76a28700004843d0b6aac690119105f6b837e2150668990c20000606f006081428cc7ec5b9d342b9668c34861d1d056f95414a46427164064077f0168182f52269e96900a344d852c8f075a081ca07062290165c8b408c0c2332e091704dba605b02e495a4cac6660690eec859941ee000012158099f899c000013221f1b3c0920000d0aa68a0e84a08017d28b0000108bcc24600001169508c92554c10a0000000009c112122 else (if i < 4 then 0x47f0b370542e24fa1988000184566217f93ad03b2000088d20000000010c7a5012e84c00a5c000094068a4b4dbfb0a15624d7c0828b02617f00003a085e249f0071e14d803219bcc4b5b44491855cb2a601442b7694a94d29063812b0f10ed436819c74118b9983c24a5208800243122cc5aa1a66a3959717f0b81d61e07c7871e41b40000007b29139837c0000a26cfe1c84ac4f8d93c0e19055c314240cc25b8000101f200003087000038ad441c2c048808c209efa293331f517d3c1873829d0740892f43a7c17c400df127ac50dac40f091d8a47c52b250d722ea142cc1f922540000000015cd20000102c000000000213150ba1c000000171d10000093d6f9b800002a0280001cc5981fad0f2608d950ba654df2aa807840001104f4808e872c00014178c2652a1a3120ee594f0d0494827bab05984c84ad1ac000120fae232b15b34a98a10d087400003dc2be0fd00000000038bf217118318157fbba200000000000038477c47c00004856fa98c2122c2cc80000000000000000595f07821704ebe22a93e1c0cd0068f66130929c480b15fe063a82ac02c38209331aaa1ec0309455a0000793c24a040000803d80002c88c000000002f074000000000000580690a200000823a8000304d80000301dc811e4a23404c92c3f16400000000000005952e603828fd000018298000144cd9089b91a5c2b0000002cef82780000000022c1b928c00016cfe6071e16898068c09bf2ae0091d49dd8041a0ea80000485a062800004965a18080000300a800024a2400000000000000001a02812f5803edc3bde57500003025d8203808f329609745898aa2189117a372444722530104680a3c00010234c0c39613800000000ac2f61098000180cc3a700409cd88f6d07209598042c0ce0000124a4c0df823600000000000004980a175626fb7693c37f84e84424681200001d8992045184e14a3dc20fc245387e70423226b1a1aba02b39d0c5f55040241ec0899842a33230772988a7653d8075346e10a52e4ccf09ed00d400847002412cf80780000841462bbd8a0380310cfd000038059c908a05ac600a10a2f9a485eaa32761566203a202900b3915274869e25f00001f1dc0a260000528a231720aca00002480f14d40001a408000002098c966c6496876951c28055bc20a8302121f81bba0eb7c600000209a2f80c400300000000161150000097c501d9a43db8eaf01ba8c3e00003c58305dc000000000000788d64b8d41a7c20f912bf832fe5a30000000000001a084d2a9c772409de844f303b5123f0380a0a85c12e9049c4eb80ac12c98000000018203a13f614888032264a0000181f000012439d08a000000001251b000031470c0bfc118000002240c9e5a59f663ae84c8c8c000002231890dfccf8000000002153c0000000000000000180ae else 0x2049384faac6232e64056570d64212d08560297800f043c42d890627318d21ae714a601ea8492415d102f095a0824fa4ae0000718f400000000b0de7f1398834254ad239185ac000000f180fdd404383d525bf00000000049620000000000001296000002610a81500be7e0d6a2b8910440001422ed20dc340b10d88592522a88308000001d2129b800000001824c71028950fc94b647020f1309e7086c60cd0000111b84a6945fec01e00000000025e5fe70a05178c8aa19c0000000000001050910fad07b6f9b78cd71012184a4c8cfc5f70000000000000000000000000000005c02023c800000000000040c3000034442210b10defe15400000000527280000c2c7411d0000517cae0516560000074028485800f042730c4100001441d18b0b21d0034764100114800027ac12055000000001c2e400005c6ae865800010265b100409fe4110e0a92295d3691c800e0644139b076139c6e6427a27691fac3c10602ea678912c0000013f51144950789b440bd8334f29a44b60a0d3613d82113006d0664f6acb895cc4ef6103e0181920a888f20b71059750be8970189d90237))) else 0
def signed8Look := lookupWord 502 1917 7 17 10 3 signed8Index
def signed7Index (_ : Nat) : Nat := 0x34740b903c0dc00081201400241f86fcfeca606b86045507b42c086401c5980c4488af49d020864003c70001ca2c8c87fcd0003c3942b4938340000880000020250b00000000034e4001480000000000003c538a9c9749ac43c5c831cebc07c464080b544f01800206c081000e21000c128d87
def signed7Look := lookupWord 18 69 5 12 5 3 signed7Index
def signed6Index (_ : Nat) : Nat := 0xf20100100000
def signed6Look := lookupWord 1 6 0 8 1 3 signed6Index
def signedIndex : Nat → Nat → Option (Nat × Nat)
  | 12 => signed11Look
  | 11 => signed10Look
  | 10 => signed9Look
  | 9 => signed8Look
  | 8 => signed7Look
  | 7 => signed6Look
  | _ => fun _ => none
def signedForest : Forest := ⟨383,1000,g383.samples,IndexTree.fork 1 (IndexTree.leaf [(0,0,383,0,13)]) g383columns,g383autos,signedLevels,signedIndex⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk6p0 : block signedForest 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem checked6 : block signedForest 6 0 2=true := chk6p0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk7p0 : block signedForest 7 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk7p9 : block signedForest 7 9 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem checked7 : block signedForest 7 0 32=true := (@block_merge signedForest 7 0 9 23 chk7p0 chk7p9)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk8p0 : block signedForest 8 0 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk8p48 : block signedForest 8 48 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk8p96 : block signedForest 8 96 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk8p144 : block signedForest 8 144 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk8p192 : block signedForest 8 192 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk8p240 : block signedForest 8 240 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk8p288 : block signedForest 8 288 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk8p336 : block signedForest 8 336 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk8p384 : block signedForest 8 384 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk8p432 : block signedForest 8 432 28=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk8p460 : block signedForest 8 460 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk8p508 : block signedForest 8 508 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk8p556 : block signedForest 8 556 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk8p604 : block signedForest 8 604 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk8p652 : block signedForest 8 652 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem checked8 : block signedForest 8 0 662=true := (@block_merge signedForest 8 0 336 326 (@block_merge signedForest 8 0 144 192 (@block_merge signedForest 8 0 48 96 chk8p0 (@block_merge signedForest 8 48 48 48 chk8p48 chk8p96)) (@block_merge signedForest 8 144 96 96 (@block_merge signedForest 8 144 48 48 chk8p144 chk8p192) (@block_merge signedForest 8 240 48 48 chk8p240 chk8p288))) (@block_merge signedForest 8 336 172 154 (@block_merge signedForest 8 336 96 76 (@block_merge signedForest 8 336 48 48 chk8p336 chk8p384) (@block_merge signedForest 8 432 28 48 chk8p432 chk8p460)) (@block_merge signedForest 8 508 96 58 (@block_merge signedForest 8 508 48 48 chk8p508 chk8p556) (@block_merge signedForest 8 604 48 10 chk8p604 chk8p652))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p0 : block signedForest 9 0 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p48 : block signedForest 9 48 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p96 : block signedForest 9 96 34=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p130 : block signedForest 9 130 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p178 : block signedForest 9 178 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p226 : block signedForest 9 226 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p274 : block signedForest 9 274 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p322 : block signedForest 9 322 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p370 : block signedForest 9 370 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p418 : block signedForest 9 418 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p466 : block signedForest 9 466 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p514 : block signedForest 9 514 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p562 : block signedForest 9 562 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p610 : block signedForest 9 610 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p658 : block signedForest 9 658 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p706 : block signedForest 9 706 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p754 : block signedForest 9 754 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p802 : block signedForest 9 802 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p850 : block signedForest 9 850 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p898 : block signedForest 9 898 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p946 : block signedForest 9 946 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p994 : block signedForest 9 994 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1042 : block signedForest 9 1042 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1090 : block signedForest 9 1090 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1138 : block signedForest 9 1138 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1186 : block signedForest 9 1186 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1234 : block signedForest 9 1234 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1282 : block signedForest 9 1282 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1330 : block signedForest 9 1330 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1378 : block signedForest 9 1378 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1426 : block signedForest 9 1426 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1474 : block signedForest 9 1474 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1522 : block signedForest 9 1522 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1570 : block signedForest 9 1570 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1618 : block signedForest 9 1618 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1666 : block signedForest 9 1666 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1714 : block signedForest 9 1714 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1762 : block signedForest 9 1762 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1810 : block signedForest 9 1810 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1858 : block signedForest 9 1858 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1906 : block signedForest 9 1906 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p1954 : block signedForest 9 1954 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2002 : block signedForest 9 2002 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2050 : block signedForest 9 2050 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2098 : block signedForest 9 2098 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2146 : block signedForest 9 2146 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2194 : block signedForest 9 2194 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2242 : block signedForest 9 2242 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2290 : block signedForest 9 2290 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2338 : block signedForest 9 2338 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2386 : block signedForest 9 2386 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2434 : block signedForest 9 2434 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2482 : block signedForest 9 2482 25=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2507 : block signedForest 9 2507 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2555 : block signedForest 9 2555 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2603 : block signedForest 9 2603 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2651 : block signedForest 9 2651 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2699 : block signedForest 9 2699 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2747 : block signedForest 9 2747 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2795 : block signedForest 9 2795 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2843 : block signedForest 9 2843 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2891 : block signedForest 9 2891 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2939 : block signedForest 9 2939 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p2987 : block signedForest 9 2987 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk9p3035 : block signedForest 9 3035 40=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem checked9 : block signedForest 9 0 3075=true := (@block_merge signedForest 9 0 1522 1553 (@block_merge signedForest 9 0 754 768 (@block_merge signedForest 9 0 370 384 (@block_merge signedForest 9 0 178 192 (@block_merge signedForest 9 0 96 82 (@block_merge signedForest 9 0 48 48 chk9p0 chk9p48) (@block_merge signedForest 9 96 34 48 chk9p96 chk9p130)) (@block_merge signedForest 9 178 96 96 (@block_merge signedForest 9 178 48 48 chk9p178 chk9p226) (@block_merge signedForest 9 274 48 48 chk9p274 chk9p322))) (@block_merge signedForest 9 370 192 192 (@block_merge signedForest 9 370 96 96 (@block_merge signedForest 9 370 48 48 chk9p370 chk9p418) (@block_merge signedForest 9 466 48 48 chk9p466 chk9p514)) (@block_merge signedForest 9 562 96 96 (@block_merge signedForest 9 562 48 48 chk9p562 chk9p610) (@block_merge signedForest 9 658 48 48 chk9p658 chk9p706)))) (@block_merge signedForest 9 754 384 384 (@block_merge signedForest 9 754 192 192 (@block_merge signedForest 9 754 96 96 (@block_merge signedForest 9 754 48 48 chk9p754 chk9p802) (@block_merge signedForest 9 850 48 48 chk9p850 chk9p898)) (@block_merge signedForest 9 946 96 96 (@block_merge signedForest 9 946 48 48 chk9p946 chk9p994) (@block_merge signedForest 9 1042 48 48 chk9p1042 chk9p1090))) (@block_merge signedForest 9 1138 192 192 (@block_merge signedForest 9 1138 96 96 (@block_merge signedForest 9 1138 48 48 chk9p1138 chk9p1186) (@block_merge signedForest 9 1234 48 48 chk9p1234 chk9p1282)) (@block_merge signedForest 9 1330 96 96 (@block_merge signedForest 9 1330 48 48 chk9p1330 chk9p1378) (@block_merge signedForest 9 1426 48 48 chk9p1426 chk9p1474))))) (@block_merge signedForest 9 1522 768 785 (@block_merge signedForest 9 1522 384 384 (@block_merge signedForest 9 1522 192 192 (@block_merge signedForest 9 1522 96 96 (@block_merge signedForest 9 1522 48 48 chk9p1522 chk9p1570) (@block_merge signedForest 9 1618 48 48 chk9p1618 chk9p1666)) (@block_merge signedForest 9 1714 96 96 (@block_merge signedForest 9 1714 48 48 chk9p1714 chk9p1762) (@block_merge signedForest 9 1810 48 48 chk9p1810 chk9p1858))) (@block_merge signedForest 9 1906 192 192 (@block_merge signedForest 9 1906 96 96 (@block_merge signedForest 9 1906 48 48 chk9p1906 chk9p1954) (@block_merge signedForest 9 2002 48 48 chk9p2002 chk9p2050)) (@block_merge signedForest 9 2098 96 96 (@block_merge signedForest 9 2098 48 48 chk9p2098 chk9p2146) (@block_merge signedForest 9 2194 48 48 chk9p2194 chk9p2242)))) (@block_merge signedForest 9 2290 361 424 (@block_merge signedForest 9 2290 192 169 (@block_merge signedForest 9 2290 96 96 (@block_merge signedForest 9 2290 48 48 chk9p2290 chk9p2338) (@block_merge signedForest 9 2386 48 48 chk9p2386 chk9p2434)) (@block_merge signedForest 9 2482 73 96 (@block_merge signedForest 9 2482 25 48 chk9p2482 chk9p2507) (@block_merge signedForest 9 2555 48 48 chk9p2555 chk9p2603))) (@block_merge signedForest 9 2651 192 232 (@block_merge signedForest 9 2651 96 96 (@block_merge signedForest 9 2651 48 48 chk9p2651 chk9p2699) (@block_merge signedForest 9 2747 48 48 chk9p2747 chk9p2795)) (@block_merge signedForest 9 2843 96 136 (@block_merge signedForest 9 2843 48 48 chk9p2843 chk9p2891) (@block_merge signedForest 9 2939 48 88 chk9p2939 (@block_merge signedForest 9 2987 48 40 chk9p2987 chk9p3035)))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p0 : block signedForest 10 0 20=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p20 : block signedForest 10 20 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p68 : block signedForest 10 68 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p116 : block signedForest 10 116 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p164 : block signedForest 10 164 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p212 : block signedForest 10 212 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p260 : block signedForest 10 260 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p308 : block signedForest 10 308 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p356 : block signedForest 10 356 19=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p375 : block signedForest 10 375 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p423 : block signedForest 10 423 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p471 : block signedForest 10 471 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p519 : block signedForest 10 519 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p567 : block signedForest 10 567 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p615 : block signedForest 10 615 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p663 : block signedForest 10 663 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p711 : block signedForest 10 711 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p759 : block signedForest 10 759 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p807 : block signedForest 10 807 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p855 : block signedForest 10 855 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p903 : block signedForest 10 903 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p951 : block signedForest 10 951 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p999 : block signedForest 10 999 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p1047 : block signedForest 10 1047 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p1083 : block signedForest 10 1083 48=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p1131 : block signedForest 10 1131 48=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p1179 : block signedForest 10 1179 48=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk10p1227 : block signedForest 10 1227 33=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem checked10 : block signedForest 10 0 1260=true := (@block_merge signedForest 10 0 615 645 (@block_merge signedForest 10 0 308 307 (@block_merge signedForest 10 0 116 192 (@block_merge signedForest 10 0 20 96 chk10p0 (@block_merge signedForest 10 20 48 48 chk10p20 chk10p68)) (@block_merge signedForest 10 116 96 96 (@block_merge signedForest 10 116 48 48 chk10p116 chk10p164) (@block_merge signedForest 10 212 48 48 chk10p212 chk10p260))) (@block_merge signedForest 10 308 115 192 (@block_merge signedForest 10 308 48 67 chk10p308 (@block_merge signedForest 10 356 19 48 chk10p356 chk10p375)) (@block_merge signedForest 10 423 96 96 (@block_merge signedForest 10 423 48 48 chk10p423 chk10p471) (@block_merge signedForest 10 519 48 48 chk10p519 chk10p567)))) (@block_merge signedForest 10 615 336 309 (@block_merge signedForest 10 615 144 192 (@block_merge signedForest 10 615 48 96 chk10p615 (@block_merge signedForest 10 663 48 48 chk10p663 chk10p711)) (@block_merge signedForest 10 759 96 96 (@block_merge signedForest 10 759 48 48 chk10p759 chk10p807) (@block_merge signedForest 10 855 48 48 chk10p855 chk10p903))) (@block_merge signedForest 10 951 132 177 (@block_merge signedForest 10 951 48 84 chk10p951 (@block_merge signedForest 10 999 48 36 chk10p999 chk10p1047)) (@block_merge signedForest 10 1083 96 81 (@block_merge signedForest 10 1083 48 48 chk10p1083 chk10p1131) (@block_merge signedForest 10 1179 48 33 chk10p1179 chk10p1227)))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk11p0 : block signedForest 11 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk11p4 : block signedForest 11 4 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk11p40 : block signedForest 11 40 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem checked11 : block signedForest 11 0 60=true := (@block_merge signedForest 11 0 4 56 chk11p0 (@block_merge signedForest 11 4 36 20 chk11p4 chk11p40))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk12p0 : block signedForest 12 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem chk12p2 : block signedForest 12 2 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem checked12 : block signedForest 12 0 3=true := (@block_merge signedForest 12 0 2 1 chk12p0 chk12p2)
theorem verified : checkedTables signedForest 12 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact checked6
  · exact checked7
  · exact checked8
  · exact checked9
  · exact checked10
  · exact checked11
  · exact checked12
def rootBank := vars 383 ++ [neg (inputs.getD 0 zero)]

def pairsSmall : List (Row × Row) := [(2,3),(4,6),(8,12),(16,24),(1,17),(1,33),(256,320),(32,288)]

def separatedBad (T : Sig) (ws : List Sig) :=
  pairsSmall.any fun (r,s) => bit r T != bit s T && ws.all (fun a => bit r a == bit s a)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem possibleBanks : rootBank.sublists.all (fun w =>
    separatedBad (graphGoal 383) w || ([0,1,2] : List Nat).any (fun n =>
      sameWords w (stateSet signedForest 12 n))) = true := by decide +kernel

theorem signedBound (done : checkedTables signedForest 12) : Lower rootBank (graphGoal 383) 13 := by
  have geom : graphValid signedForest (boundsBefore known383) = true := by decide +kernel
  have ex := forest_all signedForest 12 (boundsBefore known383) (before_sound _ valid383) geom done
  intro p bank hr hit
  by_contra! hs
  obtain ⟨k,t,S,hk,H,sub⟩ := reach_live (proper_of _ (by decide +kernel : properB (graphGoal 383)=true)) hr hit
  classical
  let w := rootBank.filter (fun x => x ∈ S)
  have eq : w.toFinset = S := by ext a; simp [w,and_iff_right_of_imp (sub a)]
  have he := List.all_eq_true.mp possibleBanks w (List.mem_sublists.mpr List.filter_sublist)
  simp only [Bool.or_eq_true] at he
  rcases he with bad | yes
  · obtain ⟨⟨r,s⟩,_,rs⟩ := List.any_eq_true.mp bad
    simp only [Bool.and_eq_true] at rs
    obtain ⟨diff,agree⟩ := rs
    obtain ⟨a,ha,hh⟩ := live_row_difference H (bne_iff_ne.mp diff)
    exact hh (beq_iff_eq.mp (List.all_eq_true.mp agree a (List.mem_toFinset.mp (eq.symm ▸ ha))))
  · obtain ⟨n,hn,hw⟩ := List.any_eq_true.mp yes
    have cut := ex 12 (by decide) n (by
      simp at hn
      rcases hn with rfl | rfl | rfl <;> decide +kernel)
    have ee := (sameWords_sound hw).symm.trans eq
    exact cut k t (by omega) (ee.symm ▸ H)

def fullBank (j : Fin 9) := (inputs ++ [neg (inputs.getD 0 zero)]) ++
    [bin true (inputs.getD 6 zero) (inputs.getD j.val zero)]

def slicingMoves := ([65,50,131,84,118,135] : List Nat).map swapRows ++ fixRows 64 0

def pinRows (j : Fin 9) : List (Sig × Row × Row) :=
  let r := ([257,2,260,10,18,34,2,130,256] : List Nat).getD j.val 0
  [(inputs.getD 6 zero,Fin.ofNat 512 r,Fin.ofNat 512 (r+64))]

set_option maxHeartbeats 0 in
theorem fullLift : ∀ j : Fin 9,
    checkLift slicingMoves graph (fullBank j) rootBank (graphGoal 383) (pinRows j) = true := by
  decide +kernel

theorem circuitBound (j : Fin 9) (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (correct : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [!x 0] ++ [x 6 || x j]) = edge x)
    (lower : Lower rootBank (graphGoal 383) 13) : 14 ≤ C.size := by
  let w := fullBank j
  have bits (r : Row) : w.map (bit r) =
      List.ofFn (sample r) ++ [!sample r 0] ++ [sample r 6 || sample r j] := by
    simp only [w,fullBank,List.map_append,List.map_singleton,←sampled,bit_neg,bit_bin]
    rfl
  have goal : (execute C.gates w).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Row := ⟨i,hi⟩
    change bit r ((execute C.gates w).getD C.output zero) = bit r graph
    rw [←b_read,execute_bits _ _ _ (fun g hg => (fan g hg).1),edge_table,bits]
    exact correct (sample r)
  have rep := get_rep (execute C.gates w) C.output
  rw [goal] at rep
  obtain ⟨k,t,S,hk,run,sub⟩ := extract C.gates w fan graph_proper (rep.resolve_right fun h => h graph_proper)
  let xs := S.toList
  have rr := list_run run xs (Finset.nodup_toList _) (by simp [xs])
  have hs : supply (w.map observe) (xs.map observe) := by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q,bank,hq,he,hl⟩ := contraction (observe_proper graph_proper) rr _ Reach.start hs
  have bound := lift_ok (fullLift j) graph_proper (proper_of _ (by decide +kernel)) lower q bank hq he
  have card : ((pinRows j).map Prod.fst).toFinset.card = 1 := by simp [pinRows]
  rw [card] at bound
  change 14 ≤ C.gates.length
  omega

end PEqualNP.Outside.L_meta_3394

theorem PEqualNP.Outside.L_meta_3394 : ∀ x1 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++ [x6 (6 : Fin (9 : ℕ)) || x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro j _ C fan small
  by_contra h
  have hh := PEqualNP.Outside.L_meta_3394.circuitBound j C fan (fun x => Classical.not_not.mp (fun ne => h ⟨x,ne⟩))
    (PEqualNP.Outside.L_meta_3394.signedBound PEqualNP.Outside.L_meta_3394.verified)
  omega
