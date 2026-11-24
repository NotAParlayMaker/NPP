import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2046
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
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


private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.induct with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
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

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
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

private lemma gate_rep (w : List Sig) (g : Gate)
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



private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
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

private lemma extract (gs : List Gate) (w : List Sig)
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
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
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

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
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



def isNot2046 (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false

private lemma gate_repT (w : List Sig) (g : Gate)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨
      (if isNot2046 g.op then ∃ a, a∈w ∧ proper a ∧ gv w g = neg a
       else ∃ d a b, a∈w ∧ b∈w ∧ proper a ∧ proper b ∧ a≠b ∧ gv w g = bin d a b) := by
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ ∃ x, x∈w ∧ proper x ∧ neg a = neg x := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
    · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
    · exact Or.inr ⟨a,hm,hp,rfl⟩
  have bn (d : Bool) (a b : Sig) (ha : represented w a) (hb : represented w b) :
      represented w (bin d a b) ∨ ∃ d' x y, x∈w ∧ y∈w ∧ proper x ∧ proper y ∧ x≠y ∧ bin d a b = bin d' x y := by
    have bzero : ∀ v, bin false v zero = zero ∧ bin true v zero = v := fun v => ⟨(bin_laws v).2.2.1, (bin_laws v).2.1⟩
    have bone : ∀ v, bin false v one = v ∧ bin true v one = one := fun v => ⟨(bin_laws v).1, (bin_laws v).2.2.2.1⟩
    rcases operand_cases ha with rfl | rfl | ⟨hma,hpa⟩
    · rw [bin_comm]
      cases d
      · exact Or.inl (Or.inr fun h => h.1 (bzero b).1)
      · rw [(bzero b).2]; exact Or.inl hb
    · rw [bin_comm]
      cases d
      · rw [(bone b).1]; exact Or.inl hb
      · exact Or.inl (Or.inr fun h => h.2 (bone b).2)
    · rcases operand_cases hb with rfl | rfl | ⟨hmb,hpb⟩
      · cases d
        · exact Or.inl (Or.inr fun h => h.1 (bzero a).1)
        · rw [(bzero a).2]; exact Or.inl (Or.inl hma)
      · cases d
        · rw [(bone a).1]; exact Or.inl (Or.inl hma)
        · exact Or.inl (Or.inr fun h => h.2 (bone a).2)
      · by_cases eq : a = b
        · subst b
          cases d
          · rw [(bin_laws a).2.2.2.2.1]; exact Or.inl (Or.inl hma)
          · rw [(bin_laws a).2.2.2.2.2]; exact Or.inl (Or.inl hma)
        · exact Or.inr ⟨d,a,b,hma,hmb,hpa,hpb,eq,rfl⟩
  obtain ⟨ho,hl⟩ := hg
  rcases ho with ho | ho | ho
  · simp only [ho, isNot2046, Bool.false_eq_true, ite_false]
    cases hi : g.inputs with
    | nil => exact Or.inl (Or.inr fun h => h.2 (by simp [gv, ho, hi]))
    | cons i t =>
      cases t with
      | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using get_rep w i)
      | cons j u =>
        cases u with
        | cons _ _ => simp [hi] at hl
        | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bn false _ _ (get_rep w i) (get_rep w j)
  · simp only [ho, isNot2046, Bool.false_eq_true, ite_false]
    cases hi : g.inputs with
    | nil => exact Or.inl (Or.inr fun h => h.1 (by simp [gv, ho, hi]))
    | cons i t =>
      cases t with
      | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using get_rep w i)
      | cons j u =>
        cases u with
        | cons _ _ => simp [hi] at hl
        | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bn true _ _ (get_rep w i) (get_rep w j)
  · rw [Set.mem_singleton_iff] at ho
    simp only [ho, isNot2046, ite_true]
    cases hi : g.inputs with
    | nil =>
      have hgv : gv w g = one := by simp only [gv, ho, hi, List.map_nil, List.headD_nil, neg_laws.1]
      exact Or.inl (Or.inr fun h => h.2 hgv)
    | cons i t =>
      have hgv : gv w g = neg (w.getD i zero) := by simp only [gv, ho, hi, List.map_cons, List.headD_cons]
      rw [hgv]; exact nx _ (get_rep w i)

private lemma pull_gateT {w : List Sig} {z : Sig} {k t S} (isN : Bool) (h : Live target k t S)
    (hz : represented w z ∨
      (if isN then ∃ a, a∈w ∧ proper a ∧ z = neg a
       else ∃ d a b, a∈w ∧ b∈w ∧ proper a ∧ proper b ∧ a≠b ∧ z = bin d a b))
    (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ t' ≤ t + isN.toNat ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,by cases isN <;> simp,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | hwit
      · exact False.elim ((hr.resolve_left hw) hp)
      · cases isN with
        | true =>
          simp only [ite_true] at hwit
          obtain ⟨a,ha,hp',eq⟩ := hwit
          subst z
          let U := S.erase (neg a)
          have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
          have hu : ∀ v ∈ U, v ∈ w := fun v hv => by
            obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
          have hf : neg a ∉ insert a U := fun hh => by
            rcases Finset.mem_insert.mp hh with eq | u
            · exact hw (eq.symm ▸ ha)
            · exact hw (hu _ u)
          exact ⟨k+1,t+1,insert a U,Nat.le_refl _,by simp,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
        | false =>
          simp only [Bool.false_eq_true,ite_false] at hwit
          obtain ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩ := hwit
          subst z
          let U := S.erase (bin d a b)
          have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
          have hu : ∀ v ∈ U, v ∈ w := fun v hv => by
            obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
          have hf : bin d a b ∉ insert a (insert b U) := fun hh => by
            rcases Finset.mem_insert.mp hh with eq | u
            · exact hw (eq.symm ▸ ha)
            rcases Finset.mem_insert.mp u with eq | u
            · exact hw (eq.symm ▸ hb)
            · exact hw (hu _ u)
          exact ⟨k+1,t,insert a (insert b U),Nat.le_refl _,by simp,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,by cases isN <;> simp,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extractT (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ t ≤ gs.countP (fun g => isNot2046 g.op) ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hl,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl',hu',hlu,hT⟩ := pull_gateT (isNot2046 g.op) hl (gate_repT w g (legal g (by simp))) hs
    refine ⟨l,u,T,by simp; omega,?_,hlu,hT⟩
    simp only [List.countP_cons]
    cases h : isNot2046 g.op <;> simp [h] at hu' ⊢ <;> omega

def ImpossibleT (T : Sig) (cap tmax : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → t ≤ tmax → ¬Live T k t S

theorem imp_to_impT {T cap tmax S} (h : Impossible T cap S) : ImpossibleT T cap tmax S :=
  fun k t hk _ => h k t hk

theorem rotate_excludedT {T n tmax} {ws : List Sig} (hi : ImpossibleT T n tmax ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : ImpossibleT T n tmax (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk ht h
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
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩; simpa only [inv] using hw
    · intro ha; exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk ht run

theorem enum_stepT {T : Sig} {cap tmax : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : tmax > 0 → ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      ImpossibleT T (cap-1) (tmax-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      ImpossibleT T (cap-1) (if (childTwo ws a b d ka kb).length = cap then 0 else tmax)
        (childTwo ws a b d ka kb).toFinset) :
    ImpossibleT T cap tmax ws.toFinset := by
  classical
  intro k t hk ht h
  generalize he : ws.toFinset = S at h
  induction h using Live.induct with
  | stop hp =>
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]; by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      refine List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h)),
        kept_nd keep a (ws.erase a) (hn.erase _) na⟩
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by rw [←List.toFinset_card_of_nodup nd,eq]; omega
    exact oneStep (by omega) a am keep fresh hz len k t (by omega) (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin, kept_fin, er, he]
      ext j
      by_cases hja : j = a
      · subst j; by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka, kb, aa, bb, hab]
      · by_cases hjb : j = b
        · subst j; by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka, kb, aa, bb, hja]
        · by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka, kb, aa, bb, hja, hjb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup :=
      List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h))),
        kept_nd ka a _ nk ax⟩
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by rw [←List.toFinset_card_of_nodup nd,eq]; omega
    have ht' : t ≤ if (childTwo ws a b d ka kb).length = cap then 0 else tmax := by
      split_ifs with hlen
      · rw [←List.toFinset_card_of_nodup nd,eq] at hlen; omega
      · exact ht
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) ht' (eq.symm ▸ tail)

theorem closeChildT_sound {raw T pools links k tmax rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → ImpossibleT T k tmax (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    ImpossibleT T k tmax (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]; exact lValid _ _ hx
  · exact imp_to_impT (scalarPoolCut_sound (pValid _ hp) nd ok)

def full768 : Nat := (BitVec.allOnes 768).toNat
abbrev NatCov := Nat × Nat × Nat
abbrev NatSig := Nat × Nat
def toNatCov (c : Cov) : NatCov := (c.1.toNat, c.2.1.toNat, c.2.2.toNat)
def toNatSig (s : Signals) : NatSig := (s.1.toNat, s.2.toNat)
def natCol (d : Bool) (s : NatSig) : Nat := if d then s.1 ^^^ (s.1 &&& s.2) else s.1 ^^^ s.2
def natOp (op : Nat) (a b : NatSig) : NatSig :=
  if op = 2 then (full768 ^^^ a.1, full768 ^^^ a.2)
  else if op = 1 then (a.1 ||| b.1, a.2 ||| b.2)
  else (a.1 &&& b.1, a.2 &&& b.2)
def natRest (c : NatCov) (a b : Nat) (un ka kb : Bool) : Nat :=
  let w1 := fun x => c.1 ^^^ (c.1 &&& (c.2.1 &&& x))
  let w2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else w1 a)
  else if ka then (if kb then c.1 else w1 b)
  else if kb then w1 a else w2

theorem natCol_eq (d : Bool) (s : Signals) : natCol d (toNatSig s) = (column d s).toNat := by
  cases d
  · simp [natCol, toNatSig, column]
  · simp [natCol, toNatSig, column, ← xor_meet]

theorem natOp_eq (op : Nat) (a b : Decor) :
    natOp op (toNatSig a.2) (toNatSig b.2) = toNatSig (movedDecor op a b).2 := by
  by_cases h2 : op = 2
  · simp only [natOp, h2, ite_true, toNatSig, movedDecor, codeDecor, dneg, full768]
    apply Prod.ext
    · change (BitVec.allOnes 768).toNat ^^^ a.2.1.toNat = (~~~a.2.1).toNat
      rw [← BitVec.toNat_xor, top_xor]
    · change (BitVec.allOnes 768).toNat ^^^ a.2.2.toNat = (~~~a.2.2).toNat
      rw [← BitVec.toNat_xor, top_xor]
  · by_cases h1 : op = 1
    · simp [natOp, h2, h1, toNatSig, movedDecor, codeDecor, dbin]
    · have h1b : (op == 1) = false := beq_eq_false_iff_ne.mpr h1
      simp [natOp, h2, h1, h1b, toNatSig, movedDecor, codeDecor, dbin]

theorem natRest_eq (c : Cov) (a b : Bits) (un ka kb : Bool) :
    natRest (toNatCov c) a.toNat b.toNat un ka kb = (restCov c a b un ka kb).toNat := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [natRest, toNatCov, restCov, takeOne, takeTwo, Bool.false_eq_true, ite_false, ite_true,
      ← BitVec.toNat_and, ← BitVec.toNat_or, ← BitVec.toNat_xor, xor_meet]

abbrev FastDecor := Decor × NatSig × Nat × Nat
def mkFast (d : Decor) : FastDecor :=
  let ns := toNatSig d.2
  (d, ns, natCol false ns, natCol true ns)

abbrev NodeContextT := Nat × Nat × Nat × List Decor × NatCov × NatCov × List BoundPool × List QuickPool × (Nat → List (List Sig)) × (Nat → List (List Sig))

def evalMoveT (c : NodeContextT) (op : Nat) (a b : FastDecor) (zns : NatSig) (ka kb : Bool) : Bool :=
  let (cap,tmax,n,ws,cov0,cov1,pools,qpools,links0,links1) := c
  let un := op == 2
  let len := 1 + (n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len > cap then true else
    let ct := if un || len == cap then 0 else tmax
    let d := ct == 0
    let rs := if d then natRest cov1 a.2.2.2 b.2.2.2 un ka kb else natRest cov0 a.2.2.1 b.2.2.1 un ka kb
    if (rs ||| natCol d zns) != full768 then true else
    let z := choiceVal (movedChoice op a.1 b.1)
    if !properB z || ws.any (fun v => v.1 == z) then true else
    if qpools.any (fun qp => fastCost qp (cap-1) a.1 b.1 op ka kb) then true else
      let rest := (opKeep un ka kb a.1 b.1 ws).map Prod.fst
      let links := if ct == 0 then links0 else links1
      closeChild pools links (cap-1) rest (movedChoice op a.1 b.1)

theorem evalMoveT_sound {raw T r s ws pools links0 links1 cap tmax a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op == 2) = false → a ≠ b) (hcap : 0 < cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv0 : ∀ tag xs, xs ∈ links0 tag → ImpossibleT T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs, xs ∈ links1 tag → ImpossibleT T (cap-1) tmax (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMoveT (cap,tmax,ws.length,ws,toNatCov (coverage false ws),toNatCov (coverage true ws),pools,pools.map (summarizePool ws),links0,links1)
      op (mkFast a) (mkFast b) (natOp op (toNatSig a.2) (toNatSig b.2)) ka kb = true) :
    ImpossibleT T (cap-1)
      (if (op == 2) || (moveFront ws op a b ka kb).length == cap then 0 else tmax)
      (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
  have val := moved_full op a b
  have fr : ws.any (fun v => v.1 == choiceVal (movedChoice op a b)) = false := by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (val.trans ((beq_iff_eq.mp he).symm) ▸ List.mem_map_of_mem hx)
  have pp : properB (choiceVal (movedChoice op a b)) = true := by simpa [properB,proper,val] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk ht h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMoveT at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  let ct := if (op == 2) || (child.length == cap) then 0 else tmax
  have ht0 : (ct == 0) = true → t = 0 := by
    intro hct
    have hc0 : ct = 0 := beq_iff_eq.mp hct
    change t ≤ ct at ht
    omega
  have sep := cover_sound h rfl (pair_sep pairs) (ct == 0) ht0
  let d := ct == 0
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have hnat_eq : (if d then natRest (toNatCov (coverage true ws)) (mkFast a).2.2.2 (mkFast b).2.2.2 (op==2) ka kb
                  else natRest (toNatCov (coverage false ws)) (mkFast a).2.2.1 (mkFast b).2.2.1 (op==2) ka kb)
                 ||| natCol d (natOp op (toNatSig a.2) (toNatSig b.2)) = full768 := by
    rw [natOp_eq, natCol_eq]
    cases hd : d with
    | false =>
      simp only [Bool.false_eq_true, ite_false, mkFast, natCol_eq, natRest_eq, ← BitVec.toNat_or]
      rw [hd] at sep
      simpa [full768, getCov, preCov] using congrArg BitVec.toNat sep
    | true =>
      simp only [ite_true, mkFast, natCol_eq, natRest_eq, ← BitVec.toNat_or]
      rw [hd] at sep
      simpa [full768, getCov, preCov] using congrArg BitVec.toNat sep
  have be : (((if d then natRest (toNatCov (coverage true ws)) (mkFast a).2.2.2 (mkFast b).2.2.2 (op==2) ka kb
               else natRest (toNatCov (coverage false ws)) (mkFast a).2.2.1 (mkFast b).2.2.1 (op==2) ka kb)
              ||| natCol d (natOp op (toNatSig a.2) (toNatSig b.2))) != full768) = false := by
    simp [hnat_eq]
  change (if (_ != _) then true else if !properB (choiceVal (movedChoice op a b)) || ws.any (fun v => v.1 == choiceVal (movedChoice op a b)) then true else if _ then true else _) = true at test
  rw [be, pp, fr] at test
  simp only [Bool.false_eq_true, ite_false, Bool.not_true, Bool.false_or] at test
  have nd' : (choiceVal (movedChoice op a b) :: rest.map Prod.fst).Nodup := val ▸ ndc
  have h' : Live T k t (choiceVal (movedChoice op a b) :: rest.map Prod.fst).toFinset := val ▸ h
  by_cases hq : (pools.map (summarizePool ws)).any (fun qp => fastCost qp (cap-1) a b op ka kb) = true
  · obtain ⟨qp,hqp,hfc⟩ := List.any_eq_true.mp hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hqp
    exact scalarPoolCut_sound (pv p hp) nd' (fastCost_good ha hb hfc) k t hk h'
  · have hqf : (pools.map (summarizePool ws)).any (fun qp => fastCost qp (cap-1) a b op ka kb) = false :=
      Bool.eq_false_iff.mpr hq
    change (if ((pools.map (summarizePool ws)).any fun qp => fastCost qp (cap-1) a b op ka kb) = true then true else _) = true at test
    rw [hqf] at test
    simp only [Bool.false_eq_true, ite_false] at test
    by_cases hct0 : ct = 0
    · have hctb : (ct == 0) = true := beq_iff_eq.mpr hct0
      rw [hctb] at test
      simp only [ite_true] at test
      exact closeChildT_sound pv lv0 nd' test k t hk (hct0 ▸ ht) h'
    · have hctb : (ct == 0) = false := beq_eq_false_iff_ne.mpr hct0
      rw [hctb] at test
      simp only [Bool.false_eq_true, ite_false] at test
      have hctm : ct = tmax := by
        dsimp [ct] at hct0 ⊢
        split_ifs at hct0 ⊢ with hc
        · exact False.elim (hct0 rfl)
        · rfl
      exact closeChildT_sound pv lv1 nd' test k t hk (hctm ▸ ht) h'

def testPairT (ctx : NodeContextT) (a b : FastDecor) (d : Bool) :=
  let op := if d then 1 else 0
  let zns := natOp op a.2.1 b.2.1
  let attempt := evalMoveT ctx op a b zns
  attempt false false && attempt true false && attempt false true && attempt true true

def testRowT (ctx : NodeContextT) (a : FastDecor) (bs : List FastDecor) :=
  let unOk := if ctx.2.1 == 0 then true else
    let zns := natOp 2 a.2.1 a.2.1
    evalMoveT ctx 2 a a zns false false && evalMoveT ctx 2 a a zns true true
  unOk && bs.all (fun b => testPairT ctx a b false && testPairT ctx a b true)

def testAllT (ctx : NodeContextT) : List FastDecor → Bool
  | [] => true
  | a::bs => testRowT ctx a bs && testAllT ctx bs

theorem all_unaryT {ctx} {ws : List Decor} (h : testAllT ctx (ws.map mkFast) = true) (ht : ctx.2.1 > 0) {a : Decor} (ha : a ∈ ws) (keep : Bool) :
    evalMoveT ctx 2 (mkFast a) (mkFast a) (natOp 2 (toNatSig a.2) (toNatSig a.2)) keep keep = true := by
  have hne : (ctx.2.1 == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [List.map_cons,testAllT,Bool.and_eq_true,testRowT,hne,Bool.false_eq_true,ite_false] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binaryT {ctx} {ws : List Decor} (h : testAllT ctx (ws.map mkFast) = true) {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (d : Bool) : testPairT ctx (mkFast a) (mkFast b) d = true ∨ testPairT ctx (mkFast b) (mkFast a) d = true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [List.map_cons,testAllT,Bool.and_eq_true,testRowT,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := List.mem_map_of_mem (f := mkFast) ((List.mem_cons.mp hb).resolve_left (Ne.symm ne))
      left; cases d <;> first | exact (h.1.2 _ bm).1 | exact (h.1.2 _ bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · have am := List.mem_map_of_mem (f := mkFast) haTail
        right; cases d <;> first | exact (h.1.2 _ am).1 | exact (h.1.2 _ am).2
      · exact ih h.2 haTail hbTail

theorem testPairT_at {ctx a b d} (h : testPairT ctx (mkFast a) (mkFast b) d = true) (ka kb : Bool) :
    evalMoveT ctx (if d then 1 else 0) (mkFast a) (mkFast b) (natOp (if d then 1 else 0) (toNatSig a.2) (toNatSig b.2)) ka kb = true := by
  simp only [testPairT,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem nodeT_sound {raw T r s ws pools links0 links1 cap tmax}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv0 : ∀ tag xs, xs ∈ links0 tag → ImpossibleT T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs, xs ∈ links1 tag → ImpossibleT T (cap-1) tmax (List.toFinset xs))
    (htmax : tmax ≤ 1)
    (checks : testAllT (cap,tmax,ws.length,ws,toNatCov (coverage false ws),toNatCov (coverage true ws),pools,pools.map (summarizePool ws),links0,links1) (ws.map mkFast) = true) :
    ImpossibleT T cap tmax (ws.map Prod.fst).toFinset := by
  by_cases hc : cap = 0
  · intro k t hk _ h
    have ke : k = 0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  have hc' : 0 < cap := by omega
  apply enum_stepT nd out
  · intro htpos v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    have htm1 : tmax - 1 = 0 := by omega
    rw [←hf, htm1]
    have hev := evalMoveT_sound (op := 2) pairs faith nd ha ha (by simp) hc' pv lv0 lv1 pro fresh (all_unaryT checks htpos ha keep)
    simpa using hev
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a ∈ ws) (bb : b ∈ ws) (ne' : a.1 ≠ b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPairT (cap,tmax,ws.length,ws,toNatCov (coverage false ws),toNatCov (coverage true ws),pools,pools.map (summarizePool ws),links0,links1) (mkFast a) (mkFast b) d = true) :
        ImpossibleT T (cap-1) (if (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length = cap then 0 else tmax)
          (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      have hf := binary_front nd aa bb ne' d ka kb
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      have hev := evalMoveT_sound (op := if d then 1 else 0) pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv0 lv1
        (eq ▸ pr) (eq ▸ fr) (testPairT_at test ka kb)
      have hop : ((if d then 1 else 0) == 2) = false := by cases d <;> rfl
      rw [hop, Bool.false_or] at hev
      have hlenEq : (moveFront ws (if d then 1 else 0) a b ka kb).length =
          (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length := by
        have nd1 : (moveFront ws (if d then 1 else 0) a b ka kb).Nodup := by
          unfold moveFront
          have sub := keep_sub ws a b ((if d then 1 else 0) == 2) ka kb
          exact List.nodup_cons.mpr ⟨fun hm => (eq ▸ fr) ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
        have nd2 : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup := by
          unfold childTwo
          let r0 := ((ws.map Prod.fst).erase a.1).erase b.1
          have rn : r0.Nodup := (nd.erase _).erase _
          have ar : a.1 ∉ r0 := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b.1 ∉ r0 := (nd.erase a.1).not_mem_erase
          have nk := kept_nd kb b.1 r0 rn br
          have ax : a.1 ∉ kept kb b.1 r0 := by cases kb <;> simp [kept,ar,ne']
          refine List.nodup_cons.mpr ⟨fun hm => ?_, kept_nd ka a.1 _ nk ax⟩
          rw [keep_mem] at hm
          rcases hm with ⟨heq,_⟩ | hm
          · exact fr (heq.symm ▸ List.mem_map_of_mem aa)
          · rw [keep_mem] at hm
            rcases hm with ⟨heq,_⟩ | hm
            · exact fr (heq.symm ▸ List.mem_map_of_mem bb)
            · exact fr (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [←List.toFinset_card_of_nodup nd1, ←List.toFinset_card_of_nodup nd2, hf]
      rw [hf, hlenEq] at hev
      by_cases hl : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length = cap
      · simp [hl] at hev ⊢; exact hev
      · simp [hl] at hev ⊢; exact hev
    rcases all_binaryT checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · have hsw := childTwo_swap (ws.map Prod.fst) nd a.1 b.1 d ka kb
      have hlenSw : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length =
          (childTwo (ws.map Prod.fst) b.1 a.1 d kb ka).length := by
        have ndA : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup := by
          unfold childTwo
          let rA := ((ws.map Prod.fst).erase a.1).erase b.1
          have rn : rA.Nodup := (nd.erase a.1).erase b.1
          have ar : a.1 ∉ rA := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b.1 ∉ rA := (nd.erase a.1).not_mem_erase
          have nk := kept_nd kb b.1 rA rn br
          have ax : a.1 ∉ kept kb b.1 rA := by cases kb <;> simp [kept,ar,ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_, kept_nd ka a.1 _ nk ax⟩
          rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
          · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
          · rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
            · exact fresh (heq.symm ▸ List.mem_map_of_mem hbW)
            · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        have ndB : (childTwo (ws.map Prod.fst) b.1 a.1 d kb ka).Nodup := by
          unfold childTwo
          let rB := ((ws.map Prod.fst).erase b.1).erase a.1
          have rn : rB.Nodup := (nd.erase b.1).erase a.1
          have br : b.1 ∉ rB := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have ar : a.1 ∉ rB := (nd.erase b.1).not_mem_erase
          have nk := kept_nd ka a.1 rB rn ar
          have bx : b.1 ∉ kept ka a.1 rB := by cases ka <;> simp [kept,br,Ne.symm ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_, kept_nd kb b.1 _ nk bx⟩
          rw [bin_comm d b.1 a.1] at hm
          rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
          · exact fresh (heq.symm ▸ List.mem_map_of_mem hbW)
          · rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
            · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
            · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [←List.toFinset_card_of_nodup ndA, ←List.toFinset_card_of_nodup ndB, hsw]
      rw [hsw, hlenSw]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro) (bin_comm d a.1 b.1 ▸ fresh) hh

abbrev PackingT := Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPackingT : PackingT := (0, 0, 0, 0, fun _ => 0)

def deadWires : List Decor := wiresOf dead
def readNodeT (levels : Nat → PackingT) (slot i : Nat) : Nat × List Decor × List Decor :=
  let raw := deadWires
  let (_, depth, _, _, data) := levels slot
  let len := 10 * depth
  let width := len + raw.length + depth
  let recp := packedAt data (i * width) width
  let ops := recp &&& ((1 <<< len) - 1)
  let bank := decodeBank depth ops raw
  (ops, bank, selectLive (recp >>> len) bank)

def stateSetT (levels : Nat → PackingT) (slot i : Nat) : List Sig :=
  (readNodeT levels slot i).2.2.map Prod.fst

def linkedSetT (levels : Nat → PackingT) (slot : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (levels slot).1 then none else
    (dead.autos[pair.2]?).map fun perm => (stateSetT levels slot pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSetT_sound (levels : Nat → PackingT) (k tmax : Nat)
    (names : ∀ x ∈ dead.autos.toList, autoOK (targetOf dead) (x.map swapRows) = true)
    (earlier : ∀ i < (levels (2*k+tmax)).1, ImpossibleT (targetOf dead) k tmax (stateSetT levels (2*k+tmax) i).toFinset)
    {pair out} (h : linkedSetT levels (2*k+tmax) pair = some out) :
    ImpossibleT (targetOf dead) k tmax out.toFinset := by
  unfold linkedSetT at h
  split at h
  · cases h
  next valid =>
    cases e : dead.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excludedT (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def nodeVerifiedT (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tmax i : Nat) : Bool :=
  let slot := 2 * k + tmax
  let raw := deadWires
  let (num, depth, cw, offw, data) := levels slot
  let (ops, bank, ws) := readNodeT levels slot i
  let values := ws.map Prod.fst
  let start := num * (10 * depth + raw.length + depth)
  let pos := start + num * offw + packedAt data (start + i * offw) offw
  let nr := packedAt data pos 5
  let st := pos + 5
  let rules := (getPairs data cw depth nr st).filterMap (fun (a, b) => buildRule dead ops depth bank a b)
  let ls0 := fun tag => ((idx0 slot tag).bind (linkedSetT levels (2*(k-1)))).toList
  let ls1 := fun tag => ((idx1 slot tag).bind (linkedSetT levels (2*(k-1)+tmax))).toList
  decide values.Nodup && !(values.contains (targetOf dead)) &&
    (if k = 0 then true else testAllT (k, tmax, ws.length, ws, toNatCov (coverage false ws), toNatCov (coverage true ws), rules, rules.map (summarizePool ws), ls0, ls1) (ws.map mkFast))

theorem nodeVerifiedT_sound (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tmax i : Nat)
    (htmax : tmax ≤ 1)
    (samples : properPairs (targetOf dead) (asRow fun j => (dead.samples j).1) (asRow fun j => (dead.samples j).2))
    (cols : ∀ ci ∈ dead.cols.values, Slice (vars dead.mask) (targetOf dead) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ dead.autos.toList, autoOK (targetOf dead) (x.map swapRows) = true)
    (prior0 : k > 0 → ∀ j < (levels (2*(k-1))).1, ImpossibleT (targetOf dead) (k-1) 0 (stateSetT levels (2*(k-1)) j).toFinset)
    (prior1 : k > 0 → ∀ j < (levels (2*(k-1)+tmax)).1, ImpossibleT (targetOf dead) (k-1) tmax (stateSetT levels (2*(k-1)+tmax) j).toFinset)
    (checked : nodeVerifiedT levels idx0 idx1 k tmax i = true) :
    ImpossibleT (targetOf dead) k tmax (stateSetT levels (2*k+tmax) i).toFinset := by
  simp only [nodeVerifiedT,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf dead ∉ stateSetT levels (2*k+tmax) i := by simpa [stateSetT] using checked.1.2
  by_cases h0 : k = 0
  · subst k
    intro k' t' hk' _ h
    have hk0 : k' = 0 := by omega
    subst k'
    generalize he : (stateSetT levels (2*0+tmax) i).toFinset = S at h
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact hT (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  apply nodeT_sound (raw:=vars dead.mask) samples _ hN hT _ _ _ htmax (by simpa only [h0,ite_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful dead) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound dead cols h
  · intro tag xs hx
    have e : ((idx0 (2*k+tmax) tag).bind (linkedSetT levels (2*(k-1)))) = some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    have h0' : 2*(k-1) = 2*(k-1)+0 := by omega
    rw [h0'] at h
    exact linkedSetT_sound levels (k-1) 0 names (by simpa [←h0'] using prior0 (by omega)) h
  · intro tag xs hx
    have e : ((idx1 (2*k+tmax) tag).bind (linkedSetT levels (2*(k-1)+tmax))) = some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSetT_sound levels (k-1) tmax names (prior1 (by omega)) h

def blockT (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tmax start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerifiedT levels idx0 idx1 k tmax (start + n) && blockT levels idx0 idx1 k tmax start n

theorem blockT_at {levels idx0 idx1 k tmax start n} (h : blockT levels idx0 idx1 k tmax start n = true)
    (j : Nat) (lo : start ≤ j) (hi : j < start + n) :
    nodeVerifiedT levels idx0 idx1 k tmax j = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [blockT,Bool.and_eq_true] at h
    by_cases eq : j = start + n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem blockT_merge {levels idx0 idx1 k tmax start a b}
    (h : blockT levels idx0 idx1 k tmax start a = true)
    (h' : blockT levels idx0 idx1 k tmax (start + a) b = true) :
    blockT levels idx0 idx1 k tmax start (a + b) = true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [blockT,Bool.and_eq_true] at h'
    simp only [blockT,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1, ih h'.2⟩

theorem forestT_all (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (top : Nat)
    (prior : Nat → Nat) (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior = true)
    (rows : ∀ k ≤ top, ∀ tmax ≤ 1, blockT levels idx0 idx1 k tmax 0 (levels (2*k+tmax)).1 = true) :
    ∀ k ≤ top, ∀ tmax ≤ 1, ∀ i < (levels (2*k+tmax)).1,
      ImpossibleT (targetOf dead) k tmax (stateSetT levels (2*k+tmax) i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk tmax ht i hi
    apply nodeVerifiedT_sound levels idx0 idx1 0 tmax i ht
      (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (by omega) (by omega)
    exact blockT_at (rows 0 hk tmax ht) i (by omega) (by omega)
  | succ k ih =>
    intro hk tmax ht i hi
    apply nodeVerifiedT_sound levels idx0 idx1 (k+1) tmax i ht
      (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega) 0 (by omega))
      (fun _ => by simpa using ih (by omega) tmax ht)
    exact blockT_at (rows (k+1) hk tmax ht) i (by omega) (by omega)

def first2046 : Sig := bin false (inputs.getD 0 zero) (inputs.getD 2 zero)
def sup2046 : List Sig := inputs ++ [first2046]

theorem first2046_table : ∀ r : Row, bit r first2046 = (sample r 0 && sample r 2) := by decide +kernel
theorem first2046_nonzero : first2046 ≠ zero := by decide +kernel
theorem first2046_not_neg : inputs.all (fun a => neg a != first2046) = true ∧ neg zero != first2046 ∧ neg one != first2046 := by decide +kernel

def nbr2046 (i : Fin 9) : Nat := [4,2,3,4,3,7,1,5,3].getD i.val 0
def abs2046 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< nbr2046 i)
def prs2046 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< nbr2046 i))

theorem witness2046 : ∀ i : Fin 9,
    (bit (abs2046 i) graph != bit (prs2046 i) graph) &&
    (sup2046.all fun w => w == inputs.getD i.val zero ||
      bit (abs2046 i) w == bit (prs2046 i) w) = true := by decide +kernel

theorem all_roots2046 {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ sup2046) :
    S = inputs.toFinset ∨ S = sup2046.toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := witness2046 i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (abs2046 i) (prs2046 i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hf : first2046 ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [sup2046,List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hf)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [sup2046,List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hf hw)) needed

theorem close2046 (noRaw : Impossible graph 14 inputs.toFinset)
    (noSup : ImpossibleT graph 14 1 sup2046.toFinset)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 2))
    (hsz : C.size = 15)
    (hcnt : List.countP (fun g => GateOp.rec false false true (fun _ => false) false g.op) C.gates = 1)
    (hfun : PEqualNP.MetaComplexity.circuitFun 9 C = fun x : Fin 9 → Bool =>
      x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
      x 6 && x 8 || x 8 && x 5) : False := by
  have headEq : (execute C.gates inputs).getD 9 zero = first2046 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (first2046_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    have hf := congrFun hfun (sample r)
    exact (table_eval C legal C.output r).trans (hf.trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact first2046_nonzero headEq.symm
  | cons g gs =>
    have eq0 : gv inputs g = first2046 := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = first2046 at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    have gNotNot : isNot2046 g.op = false := by
      by_cases hgn : g.op = .not
      · exfalso
        cases hi : g.inputs with
        | nil =>
          have hgv : gv inputs g = neg zero := by simp [gv, hgn, hi]
          rw [hgv] at eq0
          exact (bne_iff_ne.mp first2046_not_neg.2.1) eq0
        | cons i is =>
          have hgv : gv inputs g = neg (inputs.getD i zero) := by simp [gv, hgn, hi]
          rw [hgv] at eq0
          rcases operand_cases (get_rep inputs i) with hz | ho | ⟨hm,_⟩
          · rw [hz] at eq0; exact (bne_iff_ne.mp first2046_not_neg.2.1) eq0
          · rw [ho] at eq0; exact (bne_iff_ne.mp first2046_not_neg.2.2) eq0
          · exact (bne_iff_ne.mp (List.all_eq_true.mp first2046_not_neg.1 _ hm)) eq0
      · cases hop : g.op <;> simp [isNot2046] at *
        exact hgn hop
    have hcntEq : (fun g : Gate => GateOp.rec false false true (fun _ => false) false g.op) =
        (fun g : Gate => isNot2046 g.op) := by
      funext x; cases x.op <;> rfl
    rw [hcntEq, hgs, List.countP_cons, gNotNot] at hcnt
    simp only [Bool.false_eq_true, ite_false] at hcnt
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 :=
      fun gate hg => legal gate (by rw [hgs]; exact List.mem_cons_of_mem _ hg)
    obtain ⟨k,t,S,hk,ht,run,hs⟩ := extractT gs sup2046 tailLegal graph_proper targetIn
    have hlen : gs.length = 14 := by
      have : (g :: gs).length = 15 := by simpa [Circuit.size, hgs] using hsz
      simp at this; omega
    rcases all_roots2046 run hs with rfl | rfl
    · exact noRaw k t (by omega) run
    · exact noSup k t (by omega) (by omega) run

def f2046L18A : Array Nat := #[0x5040097a06e00af40318c070003308e0006310000002600106966dddb58cfb9b727981593108e0b828041ffb75c92e98558c2083ff6eb925d2c6c084143fcdb6959858d810830df99663350caa621041bf770a6aeda960420c97edcb8c5c2a6c0841b2ddc664cb854d8108327f372e0170a9b02106cde655c02e15360420d9ecc9b805c2a6c084186fdc6656bb6a131083e5aac6c0b0ccaa62107cb561993595814c420a37eed94cc9d54c084186fdc96d953aa9810838dbb6cc9aa7553021061bf725b614eaa60420]
def f2046L18 : PackingT := (17,6,7,8,fun i => f2046L18A[i]?.getD 0)
def f2046L19A : Array Nat := #[0x142a5bbac59b62cc306105cd3748a86558354c20]
def f2046L19 : PackingT := (2,6,7,4,fun i => f2046L19A[i]?.getD 0)
def f2046L20A : Array Nat := #[0xa7fdca619954c420f6dd63619954c420f3f581619954c420a7fcca6e5854c420c7fdb9699854c420e3fd98699854c420c7fda96e1654c420d7dd936e1654c420d7f5916e1654c420e6fda9619654c420f6dd93619654c420f6f591619654c420e77da9615654c420f37d98615654c420f75d93615654c420f77591615654c420b7ddc92d5634c420f7d5912d5634c420b7ddc9615634c420f3dd98615634c420f7d591615634c420c7fdba655814c420b7f5c92d5814c420f7d5932d5814c420f7d593615814c420d7f5b9595814c420f3f598595814c420faf586595814c420f7d593595814c420a7fdc8596aa64c20e6fd86596aa64c20e77d85596aa64c20e6fcc6606aa64c20e3fd86606aa64c20a7fdc8586aa64c20e7f581586aa64c20a7fdc8546aa64c20a7fdc6546aa64c20e77d65546aa64c20e7f581546aa64c20a7fdc9546aa60c20e77d95546aa60c20e7f591546aa60c20a7fdc9146aa60c20e7f5c96865520c20a7fdca6465520c20e6fda66465520c20e77da56465520c20e7bda46465520c20e7eda26465520c20e7f5a16465520c20e7f9916825520c20a7fdc9296aa58c20c3fdb8662aa58c20c7fdb8656aa58c20a7fdc9616aa58c20c7fdb9616aa58c20e3fd98616aa58c20c7fdb564eaa58c20c7fd956c6aa58c20c7fd936c6aa58c20c7fdb5646aa58c20a7fdc9546aa58c20e77d95546aa58c20e7f591546aa58c20c7fdb8646aa54c20cbfdb8606aa54c20a7fdc9586aa54c20c7fdb9586aa54c20e6fd96586aa54c20a7fdc854eaa64420e7dd8354eaa64420c6fda96daaa60420d2fd986daaa604208efdcb29aaa60420e2fd9829aaa60420d6fdb664eaa60420e6fca664eaa60420c6fd986daaa60420e6fdb664eaa60420c7fdb664eaa60420c6fdb664eaa60420c7fdb564eaa60420cefdb660eaa60420a7fdc954eaa60420cefdb654eaa60420e7dd9354eaa60420a7fdc914eaa60420cefdb614eaa60420c6fdb6646aa60420a7fdc9616aa4c420c7fdb9616aa4c420e3fd98616aa4c42087fdc92e953a202087fcca6e553a2020a7fcca54d91a202087fdc52e9988cc2087fdc12e9988cc20a7fcca6e1958cc20a7fcca6d9958cc2087fdc92e9858cc2087fcca6e5858cc20c3fcba661858cc2087fdc92e9658cc2087fcca6e5658cc20c6fcba659658cc20f37d98615658cc20a7fcca615918cc20a7fcca595918cc2087fdc92e9818cc2087fcca6e5818cc20c3fcba661818cc20c7fcba655818cc20f3f598605618cc20f77565645518cc20f77595605518cc2087fdc52e9988442087fdc92e953844208ffdc82e953844208efdc62e9538442087fcca6e5538442097fdcb661538442097fccb6615384420d3fdb86615384420c7dcba64d5384420b7ddc960d5384420f3dd9860d5384420f75d9560d5384420,0xc7fdb82c5a954c20d7f5c96c4a854c20c7fcc16e99854c2087fecc6e99854c20c7fccb6a56360420e3fda56616360420d3fcc86e5536042087fecc6e9984c42087fecc6e9954c420c7fccb6a1954c420e6fcc66a1954c420c7fcca6e5854c420f6f4b6655814c42096fdc6aeda16602097fdc5aeda664c2097fdc1aeda664c20c7fd61aeda960c20c7fd51aeda960c20c7fd91aeda520c20e77d91aeda520c20c6fda6aed9520c20c77da5aed9520c20c7bda4aed9520c20c7eda2aed9520c20c7fda1aed9520c20c7f5a1aed9520c20c7f9a0aed9520c20a7fdc92d5a858c2087fdc9aeda858c20c7fd95aeda858c20a7fcca6d59858c20a7fcca6c59858c20c7fdb96a0a558c2097fdcb660a558c20d3fdb8660a558c20d6fdb9618a558c20a7fcca6e19558c2097fdc92e98558c20d3fd982e98558c20a7fcca6e58558c20a7fcca6159358c20b7ddc92958358c20a7fdc9295a158c2087fdc8aeda954c2087fdc1aeda954c20c7fd81aeda954c20c7fd61aeda954c20a7fdc92c5a854c20c7fdb92c5a854c20e3fd982c5a854c20c7fd91aeda854c20c7fda96c4a854c20d7dd936c4a854c2087fdc9aeda654c208bfdc8aeda654c20c7fda96e0a154c20d7dd936e0a154c20c7fdb96a0a154c20d7ddb960ca154c20f75d9560ca154c2096fdc6aeda86442097fdc3aeda864420f75d536158364420a7fdca2d56364420b7f5c12d5636442097fccb6156364420a7fdca2e15364420b6fdc62e15364420b7f5c12e15364420b7f9c02e1536442097fccb6a15364420b3fcc86d9536442097fdcb60d5364420c6fca6aeda960420a6fdc6aeda960420c6fcb6aeda960420c6fdc6aeda96042087fdc3aeda960420c7fd63aeda960420c7fdb9694a360420a7fcca6d99360420e6fca6695936042097fdcb2959360420e6fca62959360420b7ddc32959360420a7fdca6556360420c7fcba6556360420f2fd866556360420e7dda36556360420d7f5b16556360420f7d5316556360420c7fcba64d6360420f2fd8664d6360420b3fdc92e15360420d3fdb92e15360420bafdc62e15360420f3dd932e15360420bbf9c02e15360420d6fdb92995360420f6dd932995360420d3fdb96195360420f3dd936195360420f75d9560d5360420d6fdb92985360420c7fd93aeda858420c7fdb96a15358420e7dd936a1535842097fdcb6615358420d3fdb86615358420b7ddc960d5358420f3dd9860d5358420f75d9560d5358420c7fdb96a0535842097fdcb6605358420d3fdb86605358420b7f5c954d8158420f3f59854d8158420f7d59354d8158420b7f5c914d8158420c7fd85aeda94c420c7fd65aeda94c420a7fdc92d5a84c42087fdc9aeda84c4208efdc6aeda84c420c7fd95aeda84c420a7fdc92d5a64c420c7fd95aeda64c42087fdc9aeda54c420,0xb618018078800c0504028100400311d4848e80e9d15ca5c61c39c1800dc012c0576d16c014e0050e0f48f1a003f0028700055db380280152d818002860c0006223abb67457297180647066027004830001880400dccd8606e07a0c94bf65369163560d404015600b00f01015800320803c00c5600130008300018ac0034095040076004011003100880508028208e08a06e06c02005203203001e01ce0c00c006004e00001004704503703601002901901800f00eb06006003002b000008002001881140a80d8064062a3b41801800c00b400001801c08a06c05203000400c007a00000a68e28e13471470811c0dc064052a39c1801800c009c00001608e06e03201ed1d60c00c006005600000b04701449968e00a000303202380c80a5473830030018013800002c18c11c06403da3ac1801800c00ac00001608e0cc932d1d60c015605600806608018020800d054400808e06e054032028e0c00c006004e00000c00404703702a01900fb06006003002b00000602380a01624cd830050001c0a803c536d17020016841140d80600380ab41801aa0b40000140c808e06e032014e0c00d504e00000a000064101b837fa4416f8d40ad417802019011c0dc066c1800da0ac0000120040062adf04713710e11912900b00300548050411c029266c19a0ac00c2521002d90b5fed32b1e6c74b1bec52b0d6c18b04ebf6afc6b5cad2eb2eac76aa0a88ea1ea836a08a7ae986a5a694ca4be912a3a68c0a13e7f69de67089b7e63e97665c8949e50a93864c492ce49691e6468912e43a90a640c8f8e3d28f063508bae2c28a962948a3e27e898624488ce19284e611c842e0fa83a60e482ee09e826607c81ae0368065ffc7f7dfc27e95f7c7d7deee79f5e00769dd1e7405ce4731dcaa7205c5870bdc066f45bc06ebdb9e6e65b7c6d7db366c95afc6b4dab66a35a7c697da4268c5a1467dd9da67259ac663d97e65e5974655d93a6475900635d8ba62a588c61bd8525ef57645d1d7365c65684599d6625945640588d60657a55d8571d5aa5635570554d53654654fc537d4da53254ac529d47e5185450512d43a507540c501d3ea4f653c84ead39a4df536c4d0d3264c553044b9d2d64b152a84a2d26248e5210479d1be4625160450d0d242a508c418d03a40750003f8cfc63ea4f983e1cf5e3cd4f183beceea3b34ebc392ce0a3724d88357cd423344cb4322cc022f94bc82eacb9a2e24b6c2d6cb262c24aec2b6ca162544934227c82220147e81d7c6d61a2460015dc51214044e4131c4320e743440c9c30a0c142f409dc1fa0774178041c0ea01e4068006c00a0014000c7fda56c4a366020d3fd856c4a366020a77ecc6e5a520c2087fecc6e99520c20c7fccb6a19558c20c7fcca6e58558c2097fecc6e58558c20a7fdc12e1a954c20a7fdc82c5a954c20,0x19c10802820546300b4605600600602d04703702a010019018a8e00ed06001003002d00000780001e054200305a100782d0800620062002d02381b81500c807e83000801801680000336d8240096c2eb6080a82381b81500c807e83001e800002818c11c0dc05406403f41800f4000014000308337c0284f6df8a0d9f300c9c0db05c00801000f10010050800c03c400601e200300408218189821c10c0f817e51403a41a4ca40b402401205401d20c265205a01200702005f94593600e906132902d00900500902fca2c9b0074994816804802404400c40860220bf28b26526d233230d1c01da0d20da01200d01005f94593600e0011329024380040f811fad80a806405003dc1801800c009c00001a05401e202d03e0df1c1d03209c00201e07c21000ea1547040a80b44e0011df0d8001508040b7c03c796c17000822fdb01480c0030010326800002417c1140d806001400f400001001e0c8f6c300300f1380040e00100300410019810802820c808e06205403202801ee0c00c006004e00000d064f4802af1a00f0b9f00380782d09c002e001aa908301000f80060080062000191688800200986c3be006403100310188330800c0c440620cc20040031418d1b00a0c00c0105a900d92320c9a0c006f6da0120097b6036fc506cf98064d06003d00481bea403668d032683001bdb6804802b5201b346819341800f400e01c08a06c05203001fa0c00c004007a00b00303713805db0a44818c5224014205a05f0791c8903cd6f8c1681e4028600607c06c302d02a4b64df2341052d829be1048903189a0818c5d6c0cc2623eb6097a7800330dc03ad818c6e000cc200306045f1805041d2a08550407a2eb60801a890803c00c40060b42500080181c084012e04252100000c040400607021004b8165b0af881e002b2d8660196c2cb6080a8018800e0544e00184201104703702a01900a00f706006003700000601b8327a478d007801f801c0a800c4e00102a003103202381b80880c805007b83003001b800003000c0b44003d0d800400c0f84a001d42003015130005800242b35229a960014d4b000a6d90d8536d96c29b660014db30009c000b440c82098064108000605a96c370005a100504081c100a337119b84002001e23a909db0400c1804704100300f11db0400c03ced8600601e238209d48400c03c4600130008310020800c054400602b30439299049821894c824c10e4a64126087253209304320001500310422948822c10c0a80005691d6c05965293202801e015600902a02d35f1815007880a80500a46600059152301000f1001816880100284006008200300f118004c0020060081043082431b]
def f2046L20 : PackingT := (265,5,7,14,fun i => f2046L20A[i]?.getD 0)
def f2046H0_20A : Array Nat := #[0x82f014011d40e034c0bc03f074808023c064008044022011008980150640c0088044022011d040044023209044b22900f688502521020c1001000]
def f2046H0_20 (h : Nat) : Option (Nat × Nat) := lookupWord 7 33 6 13 5 4 (fun i => f2046H0_20A[i]?.getD 0) h
def f2046L21A : Array Nat := #[0xa7bdc428da166020c7bda56d0a166020d3bd856d0a166020c7f5b5684a166020b2ddc62cd9860c20b3ddc52cd9860c20b35dc52cd9860c20d3dcb36c59860c20c77db96c5a520c20c7f5b96d5a120c20a7f5cb655a120c20e775b5655a120c2087fdc52e99858c2087fdc92e98558c20c3fcba6618558c20f2ddc66618358c20c3fdb82e1a954c20a3fcc86d9a954c20c7f5b12c5a954c20c3fdb96a0a854c20c6fda96d8a854c20c7f5a96c4a854c20c7f9a96c0a854c2087fdc12e99854c2087f5c12e99854c20d75db56cd9854c20c3fda92e1a654c20b2fcc86999654c20e3dda82a19354c20b6ddc62a19354c20b7cdc22a19354c20b7d5c12a19354c20b7d9c02a19354c20b3dcc86999354c2087fdcb6a58354c20c3fdba6618354c20b3ddc92a18354c20e3dda92a18354c20bbcdc22a18354c20f35dc56618354c20e3dd986998354c20f35ca86558354c20d75db96158354c20f35d986158354c20c7f5b9684a154c20e7d593684a154c20c77dca6d48364420d775c16d48364420c6fcb66cda960420c7ddb32cda960420b1fdc72cd9860420b2fdc62cd9860420b37dc52cd9860420b3bdc42cd9860420d3ddb32cd9860420b3f5c12cd9860420b3f5c52c59860420e2fd98299a360420c6fdb9298a360420e2fd98298a360420e3dd9868ca360420c6fdba299936042087fdc92e96360420c3fcba661636042087fdc92e9536042093fccb661536042087fdcb6a45360420c7f5a96c45360420d3f5986c4536042087fdcb6a55320420c7ddb968d5320420a7ddca64d5320420c7ddba64d5320420e75da564d5320420c6fdb92d9a84c420c6fcc66e9984c42087fdc52e9984c420e2fcc66a1984c42087fdcb6a5854c420c3fdba661854c42087fdcb6a4854c420c5fda96dc854c420c6fda96d8854c420c7dda96cc854c420c7eda96c8854c420c7f5a96c4854c420c7f9a96c0854c42097ddcb215934c420a7ddca215934c420b5ddc7215934c420b6ddc6215934c420b7cdc2215934c420b7d5c1215934c420b7d9c0215934c420e3dda8661634c42097f5cb215914c420a7f5ca215914c420b5f5c7215914c420b6f5c6215914c420b7d5c3215914c420b7e5c2215914c420b7f1c0215914c420f6d58658d914c42087fdcb6a5814c420c3fdba661814c420c7f4ca6e5814c420d6f4c66e5814c420d7d4c36e5814c420d6f5b92d9814c420f2f5982d9814c420e3f598699814c420c7f5b9695814c420e3f598695814c420b7d5c92cd814c420d7d5b92cd814c420f3d5982cd814c420f6d4b664d814c420f3d58664d814c420e7d5a564d814c420d7d5b958d814c420f3d59858d814c420fad58658d814c42087fdcb6a5514c420c7ddba64d514c420c7f5ba645514c42087fdcb6a5850c420c77db9695850c420e37d98695850c420,0x5683680141b8bb53b3176ca00014640474807a519003bb670051243a4037b8d38326fddb3806c7200a8aa52a31a0ca0176c0067004047045db603602a02971a00e706003002066700000782383201658d58347a06ff41033580280100dc06400dc00168c26e0f02620bf600504503602901800e006000003400731b001b80108e7ad802a209c19c00c0be08a06c03000c00400001e805f00f71a7067002802007b6fd8d5835801803ec19a0ac008dbf69163560d600574572971800f7067000033fe28217cc683680001981140db77c06003801800b4000a93f8a585f30029a000146045036018006000003325b0050000c17c1140d80a406001800000d0292c6c052c0ce34c000c6704264502960671a600063382fb22b1b014b0338d300007a00bd9158d80a5c6980018ce0bec8ac6c052c30c0cc00006802d64563602960631a06338010079efe8d6836806001c03c02b41b400808f8727527bfa35a0da018008137d483a93dfd1ad06d00c00461c8ac1efe8d680600190e402b41b01b403000c05ba918727527bea35a0c74b6014064b1ab06e82b00380701ee836801000c05341b4009a340cda0da0043dfd483a9d1a0b9d06d0039efe8d00a6836016801b46819b4006a340cda0c30b9015064d1ad06c02d00382281b01480c0030000019d2d8052c180009f8a07c063f3001d60d600006803e003e8eb067b6b0030000d839c1aed9c00a9be015d1ce0d76ce0060dfbb600a7067002818801b83380110e4029c19c008000284802ac19edac00a07b60d600303db06b00181f5db00a83238d3833801c198190cdeed8055c69c19c01066e07be91e35e0de00605f04503601800600000338055800800ec1ac00608a06c03001c00c004000054874802a519a8e70670033a401638d5473801658e94d64d0926e46690363d88f4e3b68da63108b0e28288761b8854e0fa82e60b4828e09e823608880ee0067e85f6c7bede2a7715d7875cdd1a7455d10736dc9a71c5c006d7db126ab5a54693da1a679599865bd9226325894620d87261b58205f4d7c25dd57105c2d7065ab565457ed5f656a552c537d492523544c511d3fa4e553304cad2d2486519c453d10e42a5074409cfc23e04f343bfcebe3994e18369cd5a3434ce431fcc262f34b682c3caaa29449f8270c95e23e48ac217c8061eb47781d0c70e1ad466818fc61616f456414bc4ca11f447810dc3ea0ea43740cfc33a0cd43300bbc2c60a74244077c19204e411c03cc08e0104000d37dc86d4a366020c6fdb6694a366020c77db5694a366020d2fdb6614a366020d37db5614a366020c7bda56d0a366020d3bd856d0a366020c7ddb568ca366020c75db568ca366020d3f5c86c4a366020c7f5a56c4a366020d3f5856c4a366020a5fdc728da166020a6fdc628da166020a77dc528da166020,0x1c90f6c059c0043b6bc5b98a06b82a000643f245db5cc0075035c1700015201e01b41938009c9176c059c0043987c57b6606782e000643bdb036832700101c01dbe27b603d00a004e06e003008be2bdb3cc3037000321f921ed81b786a63b800db6db304b38000c8503edc5da9d98c0606dc000644018ee2edb6cc603036f00032216637176db6a70181b78001910731c90f6cf1cc0c0040da7e489b8823982e00280184200610800a9c6b23b37dd21c00c07a006e0ce00405f34533631800e306300003401e805583580100df52006003b41800badb4000a9205a06ee9002006c05405203203001e01ce0c00c006004e000011b480ea0df499b0600aeb6b004030a5b0333c1032580181f8ba35a0d7707bfa0001e7001c6818dc0016880c6e353bee000b4531a06305a1eeffe2fdb754fcc747683680001a41875200c746800f77ff17edbaa7e63a3b41b401a51c553a91a35a0da00674571a706702db69df70000f409bfe2e8d4dc1efe8000a1c1a35a0c0c7a00405ad1a063d0020056a41efe8d6836801946b41818c7a35a0c01f76c7bfa00604503601800600200000f3a5b00a005000100c4204610032830da458d5835801837c199c69c1aed9c00c04610299df74871a7067003030c47454ba403338d383380200005f63661800ee4860002a3ceff2401670d4c77037001ef16ea6e62419eda40000ce0d1a07815938ed00c00303c6a4098e8d68307a8369c76806002b5234681b41e0e3b400c533a900f00da71da006001ef5b00]
def f2046L21 : PackingT := (143,5,7,14,fun i => f2046L21A[i]?.getD 0)
def f2046H0_21A : Array Nat := #[0x184381f405d05804700fa883020046814009000]
def f2046H0_21 (h : Nat) : Option (Nat × Nat) := lookupWord 3 11 4 13 5 4 (fun i => f2046H0_21A[i]?.getD 0) h
def f2046H1_21A : Array Nat := #[0x100ea1e0004010]
def f2046H1_21 (h : Nat) : Option (Nat × Nat) := lookupWord 1 5 3 10 2 4 (fun i => f2046H1_21A[i]?.getD 0) h
def f2046L22A : Array Nat := #[0xaa9980823fed9d54cc0419ff58eaa66020cffaa7553301047fdb1aa9980833fe58d54cc0419ff606aa66020cffac3553301067fc51aa9980833fe98d54cc0419ff54eaa65820cff8a75532c1067fd86aa9930833fec2d54c98419ff596aa64c20cffb03553261067fd61aa9930833fea8d54c98419ff65aaa60c20cffb2b55306106ffd65aa9830833fec8d54c1841bff586aa60c20dffaa355306106ffc51aa9830833fed4caa41841bbf69a5520c20defb4b2a906106fbda4954830837f6d14aa41841bff6865520c20dfeb432a9061077fd91954830837fcd04aa418417ff6d6aa58c20dff94b552c61077fd95aa9630823fedcd54b18413ff6e2aa58c20cffb31552c6106ffdb5aa9630827fedad54b18419ff656aa58c20dffb0b552c61067fd93aa9630827fed8d54b18419ff646aa58c20dffaa3552c61067fda9aa953083beec9d54a9841dff646aa54c208ffb73552a6104ffdb8aa9530833fecc554a98413ff6daaa54c20cffb2d552a61067fd93aa9530827fed8d54a98419ff646aa54c20dffb03552a6106ffd61aa9530833fec1d54c88419ff54eaa64420cffb53553021073fd98aa981082f7edb554c0841bbf29aaa60420effb27553021067fd98aa98108377edb554c08413ff6daaa604209dfb6d55302104ffdb3aa9810833fec9d54c0841bff60eaa60420dffaa755302106ffc53aa9810833fec8d54c08411ff6e6aa4c420cffb31552621067fd96aa9310833fecad5498841bff616aa4c420dffacb55262104ffcba54e88082bfedcaa744041df764d53a2020effb66c8d101077fd5364688082bfedc8a344041dff64c51a2020affb7298d101077fd954c688083beec9a6344041dff64531a2020efeb2298d101047fcba66233082bfedcb0d19841dff6e1958cc20effb6ccac661077fd8665633083bfed8b2b198413ff2e9858cc20affb72c2c661073fd9861633083bfecb30b19841dff655858cc209ff974b2c661057fdb959633082ffedc2cb19841dff661658cc20edfb2cb2c66107efd8659633083bfecaacb19841fdf615658cc20effb0cc8c661077fd8564633083bfeb2b23198413ff2e9818cc20affb72c0c661073fd9860633083f7e5b30319841eff619818cc20effb2ac0c661057fdb958633082ffedc2c319841dff661618cc20edfb2cb0c661077fd9558633083ffac0ac319841dff6e5518cc20affb72a8c66105ffdb854633083bfecc2a3198417ff6d9518cc20effb2ca8c661077fd9554633083bbecaaa319841fdf595518cc20efeb22a8c66107ff581546330823fe5d33108841dff6cd9884420effb72c1c221057fdb960e11083bfecc30708841cff6618384420effb2ac1c22104ffcba54e11083bfedcaa7088415ff6e55384420bffb70a9c221077fd9854e11083beec9aa708841ff760d5384420,0x41dff6c59560c20effb2ac2b06105ffebb61583083bfecab42c18413ffaeda520c20defd76d29061057febb654830837fe5ab50b18413ffaeda858c20effb6acc2c61077fdb166163082ffedc14ab1841bff6a0a558c20effb3052ac6107efd8629563082ffed894ab1841dff6e99558c20effb70caac61077fda865563083bfed2b2ab1841dff6cd9558c20effb62caac6105ffcba61563083bfedcb0ab1841dff6558558c20eff94ac9ac61077fd8564d63083bfecab06b1841ff72958358c20dff94ad0ac61077fd9568563082bff5db52a98419ffaeda954c208ffd76d4aa6106ffcb16a1530827ff5db50a98417ff6c4a854c209ffd76d32a61077fd9560d53083bfecaac6a98417ff6e0a154c20dffb5050aa6107fdd8328553082bff5db50c8841dff6e98364420effb50c1b221077fdb660d91083bfedab06c8841dff6958364420effb0ac1b221077fdb160d91083bfe5aac6c8841dff6156364420effb06b1b221077fdba54d91083bfedc2a6c8841dff2e15364420effb50a9b221077fdb654d91083bfec32a6c8841dff60d5364420effac6a9b221077fdb154d91082bff5db52c08419ffaeda9604208ffd76d4b02105ffdb528d810837fed2946c0841dff6e99360420effb6cc9b021077fda664d81083bfedab26c0841dff6959360420eff94ac9b021077fda364d81083bfecab06c0841dff6556360420effb26b1b021077fdb954d81082ffedc2a6c0841eff2e15360420fdf94ca9b02107bfd8654d81083bfec9aa6c0841ff760d5360420fdf94c29b021077fd8364581083bfea9b22c08413ffaeda858420effb66cc2c21077fdb864d61083bfedab26b0841dff6e58358420effb2ac1ac21077fd9360d61083bfedcaa6b08417ff6e15358420dffb50a9ac21077fd9854d61083bfec9aa6b0841ff760d5358420bffb7029ac2106ffda814d61083bfecc0a6b0841ffd54d8158420ffe8a6c0ac21047febb6a5310837fe5ab50988413ffaeda84c420effb6acc2621077fdb1661310837fe5ab4c988413ffaeda64c4209ffd76d2a621077fdba65531083bfedc32a98841dff6a1954c420effb6ccaa621077fda665531083bfec332a98841dff695954c420effb66caa621077fdb961531083bfed4b0a98841bff6a1854c420effb30c2a62106ffda661531083bfecab0a98841dff6a5654c420bffb70b2a62106ffda859531083bfecc2ca98841fbf619654c420effb2ab2a62107f7d8559531083bfec2b2698841dff595934c420effb2ac1a621077fd9558d31083fee5aac698841ff7615634c420effb2aa9a621077fd8564531083bfecc30298841dff655814c420ffe96ac0a62107ff58560531083ffab2b0298841dff661514c420cffb4b553301073fd85aa9980833fed0d54cc041cff606aa66020cff96b553301067fd85,0x4dc94ea92324634c68e01cc1903003904c0100440501426e40307600313741c1e2475b85be6171b1754e8ed30c18054822eac01002c9b93241c0b6474b8552736c2e3076002ea50060b440b43215fdbe4dc9b6b69524648c698d1c03801c82690c01004805014201800321b6306541c1b416adf0de60140508060ec004dcc4e81d48e05aad89c998010005ba38549416edf273ad98d698d1c02a41348600b30583b00139202d0dfb7da46c5d6d2a58d698d1cc198030d482dc001bc95215c02d0cb4680ad065054012197410619be40cba08710c32cdf08e5176293726dad894ea96352398310640da08013004013600400308e2d0437cc19423ec5d52c6b4c48ed70c1903682600801a0b501232904195549837f48014ae016f1a02bc194170056820b420b457f6f93726dada54b1a91cd218310640da0801300401110402880602c0050cb20837adf205adbed2023ec5d6d2a58d306d04c010030d4e02c003ce839c9b36a6698cbdd974f2dc6592cad9951b28564efc96791df22363c8c6ed8c3b179e275c48987f70e661a6c2eb853f08f6103c1d1830b04e6060c08b807f0025fc8bf457df2f9adf0fbdd37b3af3e5e35babf753ee5ddc95b82f6f42dc4db63b6916cb6d685ab5b51f69d2d275a28b3ef6746cd5d97ab27d648ec7ed8c1b13761aac1757f2af835e6eb83d673ab7d560aaa8d520a9f55326a46d45ca86d4fea9df538da6b94cae97252bea505491a8fa51c3a3254586887d086a0d7411680fd0049fa73e5e7be4f409e093b4e7464e669c5537ba6decd819aa1321662fcbd697612da65a74ac5947928864fdc9ca934925fa4a6c9329203239a465c884909120323edc7c08f091cf637b46c58d13196230e45e08b5f15a22a1451c89d712be234442187f70f561d2437386010ae6128c220835b04ea04dc0127efcfbd5f51be467af6f345e13bbb47656e9d9cf1394e7148df91b97b6856bf8d6d5a8034b968fad1059c6330e6536c8a18e031846222c32983130265feabf117982ec85c7eb8656c2acaf58e6b02d5cc2ad85538a955501a9d25266a2d540b27b94ddc9af532525694a2e939921e2392463e8ab1132a20843ae85650892094402c7ee4f6c1e9c3cc07890eee9d2838ba6e74d5e1a8b349e67c8ca998d5315e61a0bd4176c2d425968af395ab2a865398a18940b27ca4e209b112ef248a471c8ba9123217640707ea8f831e203b7c7468e5c1bfe36b46b88d14190030345e30b7f1644298850d89d412ac241046408ad0fc41e6c3aa070d0d8c1a2830605db0aa4148425c848808c40e301a282b104d407dc0ee011c01c002bc0130000affd76d0b301077fcb569993082bff5db4cc98415ffaeda564c208ffd76d4b061077fdba65583083bfedc32ac1841dff6d99560c20effb4ccab061077fda565583083bfed9b2ac18,0x80a30000110140518003e800563403c2d582600400c0a44702c63416807b00383191d2a40a100106e0ccd23e2fb6059aa58d798029a398330070310f3edb8d05a029c1805082e0000160c4308df68b317db318930c18033029041bd80386f86fe34168030b9e0000100c41d0799beed9a422991c0b18d20e9520518330207b20980481485a01ec0080c46f86f16c0f78d05a015c000028188040ded7e6fb361732d914c8e41d2a4018826900b18d01460000280280a3008001bddb082380a028c0200103105f08ef1622ba98538680743ac0c00d41600800f062f7e2fc3a76d0d814e1a80803b24606006a0b003da433607a1b18d06460c00d8010050026900f7db06c6341906f80a600a16dd238d0e0015c00dd238d0e001400ddb700a0080c120a6f80a23485e9ed83631a0c8c18032021bec017d238d0e001400f80197a748153c68470b7e0cae005682e00b16e0f76ff48f8bc6bcc00ae0da0b802fa40a9e3403c7b00ae000010180080644bf2091cb3696cca65480f11cd218d30600c80a6f80a6014014c003006402850280298047680051ec0298047680054083d983003600000c17c14866691f141f7b6635e6008e8e01c0298368260100c237da4239f6cca40aca963483a4101460c0190148e014c0240e81ebb665205654a3963483a4101460c0190148e014c0220b5afcdf472cda5b015152d218d20e9040518300640523805300001402a02980400200a07d0020aa392af4e3416b8300a105c000020a2ec526dada54b1a20c81831902dbfa09802007012d8bada54b1a60c18f6fe8260080160540180419045bf01154a8e0cc6691b149beb61524674c063209b7f4730640c60841300401120497d094820c6502a51762936d6c18c94edfd5203e4730640c00e4131a60080244c816cdf02a19a411b62eb60c7aa6416df634c19802005300200054018822804d8badb54b1ad30199833004d480f01b68d01551d41a80203c4df28bb165b129d524634769801cc19031396008021a3816ca91e8e05b2a464dc9928e5e903a192b69528d1c0b6548fa40791d5c694770601420b800005145d8a4db5b4a9231a60832060c840b47682600801fb16db6b6953a6103064d1da09802005a3a91c1e4db2b69525d4ec008020e05b238750a93f4818419b8d28ee0c0290af00495fdbe51762ca9231a3b4c00e60c8189cb00400e11c0509b900c1d800c83836c8e0cc77d6f9373ec59525d74769860c8189cb00400a0cc4df07600230020083816c8e1842a4e19b076002ea426e411472f481d0115b4824064208a3a07404553208e4de0740482b208bd207b02c029c680af00000828bb149b6b6231a60832069041bf47300400dd8b6db5b69840d20837e8e600801402870700c001924118c1139c1d8015b482306426483816c8eb6caa641236f93ad8a,0x3c05003e00001819ba403d02a0ab8d01401e02801f00000c02b40040541682a182d022ed805100a82d054305a044050c9b8158641e494000a8815015028a3880a8750801815100a02a8028006456c66001840a8df0c850143a90050046e56000b40a82a200342a20140549b900c0050143090007d16d0e4c0f8331df0fa4de5b18d4a1526f8008c001681596c0a8a6db004b6872402b4020008e0c65a010020a80f11c505a04641014202db6c05647014904605ac009b8e4130087233520500ac8e2015a010000188229df014056db300904605a046475b6004028c0282d06f1c8e600190602a47300072402219a4700a202978aed9cc064704186c1600800a76c1b432061b05800c009e2bb673018436064c0100121e036064c004f8bedbcc38e0621b5c106105b80140a5e2bb60dae60323820c300b002814802c91f143c7b60da1bf0d79801ee3b03600703707cf1622ba9853869c140276c19b003018bc588aeda1b029c34038333820cb00b003724029f8a1b7db065c35e60308037058019921dc61a0c21b032600380278ae6030af40d81930023243b888a1b5d4c29c34e620c06671c1e2076060060097a6009061c9011ddc437c3506437c0ec0c015c1002c01001e18408bc588aeda1b3a9852198018020c986b03600783a05586807c75c9181a1cc02c00a8eb9221d3a9c35065c760687300b0040060740bf921e2c4506cea614e1a731061c141280580200403505fc90eda1b029c34e620c38282500b0034213df8be0db24029c34e620c41280505700343005fc90f1622bb686cea614e1a73106001412c00f8bf921dc44506cea614e1a73104a0c00f51d81801802c01105af7e2fbb686c0a70d39882506007a8e00600b24600803a68b31594865952c6a4c20e60cc081ec824eac01e0b53ab3696c2a5a431a60419641300000c058051804628009d4c0113ab3696cca432ca941d37c01882690c680a3000010014051804628009d4c0280a3008c5000a388413008c5000a37da45c546f6d90ca12b30419015a9b04a390730020100da8dd6ff48e34a3a835a9b05c02802c157485e9c694750635360b8050050a0433d217a28ea0d6a6c1700a00a024d217a71a51d6a6c1700a00902b4a405182e00502bd217a5a9e34a3b83506e0140144a48220491c164c118087485e8c6947506b5360980245483ee000dc0a141603ea00050803c1f48e96c40be0a433348f8a0fb5c31af3005347306600d07dd201671a0c6053830f7e0090c80f9a43290dac69074b6028c187bb00603ee0005060f836f48d6c0b38d08e029c1805082e00001a0f816b5f9bfad91b48e0542a5a431a41d2d80a30660520980000982c028c02000a928360c6d210931a60cc0807b00483e1efd235b0a9e3420805700000a07c3dc5ceb646d23994ca941d2d801882690c6,0x13247c51ebed83661af3019303061b05801b048078831e48c340ea0900fc00705a16a0900fc0050521f432802dbf523e2fb60d946bcc00fd1d41a803c99014102d0d620ca0b4358c9906202832646a40a0c1500f05aa3a80141686b13002000b45486b288e0d58003201429320c56d80a1018f489e80ab8d48ee0c02841700000b0633d38d05a705c01801ca2859de941899102d1d40200241bf0010660c9d201671a02803f830b9e0000161866f8640fa40c337d5b0640fa198c0507570086e406ec02800c1f0ea06e1f48a381bd00180a2004b61b90992f4102a05a226403c1f0e801325e8305403c16ab651c50544b45c011b9df18ea0542600400168ea0545a01048078e804120c632648cb5b4b691c050d2d83ea371b00a000dc603c1f080802aa340b40785aa0070214681680f0b5400c17c1b8790200b42d0020c7523e2fb6055aa68d79801fa3a835009f00086ee901e41602ae3405007f0601420b80000680a0b5c00619ba402c055c680a00fe0c2e780000582d55205054b0091c605aaa65b014153238c0502d06f1b000de25521bc411c5ce1ac0d01030803c008408ed8400d023b6180f474240803c310c16803008331c810324042600408ed868101ba2d1a048090d87b92db1b602a6380a1502600120406205060c42c823352198a011db0031a040628d80a10fa2378082e43c94d4a048080380a15db1b602a0509801022821804a91f141cfb60d8467cc064a0c18401d006804a91f141efb60d946bcc064a0c18401d00680406e0d81487d01d52037864a35e6283061007a0a80402d0df0de1e805158006476c0288449db0790144224ad8318c8906076c0288168082dfd6c18ca448303b601440d81696f8c893b60f263805141686446520b5b149b82d4652d88c00894b60c640b497f5b063200a10440300064d6c6e01ad8330c707009be1bc05147a2824722e41e95801000b537f5b08e0c67353800366b6258ee00190051001d00809ad880107b500800b7f5b0033876170193a46b6059c680a00a007c0000335c07d12b801e0406ae007810180fd70205a8dd194b823002000425c00f280fd7020142e0806004ea50141691ba00a0050f08dc336b823002000425c00f11c63538013a8c050b82018013a940508e46e8028014870f5d701f4802a5b3003bf1d4a02a5b07d8ea40be1e40a8290c7523e2fb6a35e600200fd1d41808003d054025c00360c218150c9d201e82ce340500780a007c0000300a8610c830c8054053b6505400dc001b881f066e916d81671a028]
def f2046L22 : PackingT := (320,4,7,15,fun i => f2046L22A[i]?.getD 0)
def f2046H0_22A : Array Nat := #[0x8480426403c01090084804240212010900848042641e40109302700427c0da0109a00a80424021201090084b0293c0cc01090084804240213c0cc008480424021200ae008480424021201093419004240212007b0084804240212010900848027fc03801090084b00f80212000d008480424021201090084804244122e0dab078b823b003201090084804240212010900848042701440109c00b58188021201090084804240213a027a0628042402120109004448378021201090084b001802120109008480424021201090084d02aec0722045f019a03340213c0760084804269002c8ab0084d00bcd13ee0410084f0261c0fe0109a02a201ac4139e0b2008480426817a008b0084f028c021260bb008480424021201090084d83600212010910222a27bc1d80109008480426418fe074f02b501cb1004010920460042781c201090084f0170021220c000848042402120109008480424021201090084f80e802120109008480424021201090084800c2811fa002d06b682540212c06f444e004240212e07dd0230042741cc20e9e042e834b414040e50084d0367416001095052902340212010900848042481e00109706a80427118ee09700848a0bb01da01090084b020f813401090084f00380212603f0084b02980213807e801d80427c090010900848042402120109008480425419d60380084e83ba41c40109008480424021208959073a034400e7c0df70750042402120109008480424021201090084804240213e0140084c82a802120109300018370402e010900848042402120109100c00424c02140eb70140a26b4054a0940005500a7c04c804a806ec00c840e10023008480425803a01090084ca24402120109800600424021360d4008480427c0c6a00900848042611746053246100204410c010900848042402120109a060f02f8d0c64082b0700042681960109e0347807e804ae035603a80425806c010900849816c000768920084a801c01946004300580424021201090084804240213a8290084a8284021300c300848042402120109008480424021200bc008480424021201090084e024840f2010900848042402120109602180427c1720109008480424021240a9401bd015dc0d40109a059b012ec1c8200560744808751974084008480424404401090084f806ec1332061804078340813d000f340180426814e0109203b8042402132049202f804240212007cf027d81340099e867f06d920b1016ec09d905b00424021380e3000000000500c01004000440000400004000000200000000000040100000004000040300003010000000000802004000000101801004010300100001010000100000002004000040000c00000020000a0000000001000010180200c00000000000100000004060000000002000030040000000,0x213a0c4008480425d0012052008480424021201090084804240212e058c05a882e002134089d064481640213a08a30348042402120109104800427819348330084a80b95164a82f0084a819f00400109f05f920e002120109c02000425c0e28050200080426515a0109008480424c07b20a8d02e804240212209600848042402120109008480424021201090084a815501ae40121016004240212e0510084804240212803c0084804240212e01ac0040824c01592047e01a004240212088ae02f1026c0213208740088042402120109a0211804e00b401090084880b40213683000848042641a6010900848042402120109008480424006201090084d0318021201090084802d0c1de40ad0084d0180021201090084f009002120109008480424912fe0af0084d830901740109008480425d05a0109c0320042740d8206500848042402120109f05880424021300cfe0158042402120109008480424021300780084804240212010900848042780f5606e0]
def f2046H0_22 (h : Nat) : Option (Nat × Nat) := lookupWord 92 602 10 17 9 4 (fun i => f2046H0_22A[i]?.getD 0) h
def f2046L23A : Array Nat := #[0x58d810839fecc2c6c0841ebf61963604209ff974a9b021057fdb954d810833fed4aa6c0841cff6615360420efbb26a9b021057fdb914d810833fed48a6c08417fd6c453604208ffb74c99021065fda764c810833fed2b26408419f768d93204209ffb74a99021057fdb954c810833fed4aa640841bf768d5320420efbb26a99021067fdba661610833fedd326b08419ff6a19358420affb72c1ac21073fd9860d61082bfedcaa6b08419ff6a55358420edfb2ca9ac21077dd9354d610827fedd0a6b08415ff6e45358420cffb5229ac21076fd9614d61083bfadcb02b0841cfd6618158420efeb26c0ac21067fdb86a5310833fedb352988419ff6d5a94c420cffb52d42621067fdb96a13108377e5b350988419ff6e9984c420affb74cc2621047fdba661310823fe5d33098841cff6a1984c420cffb50cc2621063fda866131083bfad8b30988419ff6a5a64c420cffb30d3262104ffdba619310833fed4b0c988419ff6a5a54c420cffb72d2a621067fd98695310833fecb34a988419ff6e9954c420affb74caa621047fdba655310833fed432a988419ff699954c420eefb4acaa62104ffdba61531082bfedcb0a988419ff6a5854c420e7fb30c2a62104ffdba21531082bfedc90a988419ff6a4854c420bbfb6e42a62105efdb621531082feed990a988417fb6c8854c420bfeb6242a62105ff9b0215310827fedd2ca988419ff6a5654c420cffb50c9a621067fda664d310833fed2b2698841df76e1934c420efbb50c9a621077ddb664d31083beed332698841df7619934c420efbb6ac9a621077dda564d310833eed2b2698841df7615934c420efb90ac9a621077dd6564d31082bfedcb06988419ff6a5834c420e7fb30c1a621077dd9360d310833fed4ac698841df764d634c420efbb52b1a62106fdda858d31083beecc2c698841fb7619634c420efbb2ab1a621057fdb954d310833fed4aa698841ddf655534c420efbb26a9a621067fda8645310833fed2b2298841dfd6e1914c420efeb50c8a621077f5a664531083bfac332298841dfd6d5914c420efeb4ac8a621067f5a564531083bfac2b2298841dfd215914c420efeacac8a621077f58364531083bfab1b2298841df558d914c420efeaa6c8a62104ffdba60531082bfedcb02988419ff6a5814c420e7fb30c0a621077dd9360531083bfac8b0298841dfd6e5814c420afeb72c0a621077f5a960531083bfacc30298841cfd661814c420fde96cc0a62106ff5a660531083dfac330298841bfd695814c420efeb2ac0a62107fd4b360531083bfac9b0298841df564d814c420ffaac6c0a62104ffdba545310833fed4aa298841df764d514c420efeb22a8a621067fd98694310823fedd32a188419ff6a1950c420cefb4aca8621057fdb9614310833fed4b0a18841bdf695850c420,0x419ef655a420c20cfdb2ad11061067fd95684830833fadcb4241841bfd6d5a120c20cfeb2ad09061067f995680830833fedd330b18411ff2e99858c20edfb6ccc2c61057fdb9295630837bed294ab18419ff6e99558c20cffb50caac61076fd86655630827fe5d30ab18415ff6e58558c20e7fb30c2ac61067fda864d63083b7ec3326b18415ff6e58358c20e7fb30c1ac61077dd9360d63083beedcb06b1841cf76618358c20efbb2ac1ac61067fdb86a5530833fe5c352a98419ff6d9a954c20cffb62d4aa61067fcb16a5530833fed4b50a98419ff6e5a854c20affb72542a61067fda92a1530835fed4150a98417bf6d8a854c20bfeb62542a6105ff9b02a1530833fedd330a98415ff6e99854c208ffb74cc2a61047fcba661530839fed4330a98419ff6a19854c20c7fb50cc2a61077ddb3661530833fed4b4ca98416ff2e1a654c20d7f970d32a61067fd9869953082bfedd32ca98419ff6a19654c20edfb4ccb2a6104ffdba61953082bfedcb0ca98419ff6a58654c20ddfb4cc32a61067fda864d530833fed3326a9841df76e19354c20efbb50c9aa61077dca864d53083beedb326a9841df76999354c20efbb0cc9aa61077ddb164d530827fedd306a98415ff6e58354c20cffb52c1aa61073fd9860d53083bbecab06a9841df764d8354c20efbb72c1aa61057ddb960d53083beed4b06a9841ef72a18354c20efbb30c1aa61073dd9860d530837eed3306a9841df76598354c20efbb2ac1aa610775d9560d53083faec2b06a98415ff6e56354c20cffb52b1aa61076fd9658d53083bbecaac6a9841df764d6354c20cffb52d0aa61077dd9368553082bfedc942a98419ff6a4a154c20efbb2650aa6106ff5a1285530833fecc342298419ff659a114c20cffb50d1b221067fda568d910833fedd306c88415ff6e983644208ffb7441b221055fdb720d91082b7edb106c88415ff6d48364420aefb6a41b221057bdb420d91082bf6d9106c88415fd6c48364420aff36041b221057fdb858d91083b7ec32c6c8841df760d6364420cffb74a9b221057fdba54d91082bfedc2a6c88415ff6d95364420efbb06a9b221077f5b154d910823fedd0a6c88415ff6e05364420affb6c29b221057f5b114d91083b7e5b352c08419ff6d9a960420cdf96cd4b021067fdb36a5810833fe59b52c0841cff6d99860420e7fb66cc3021073fcb3661810839fa58b30c08419ff6a5a660420e7fb30d33021076fda92998108337ed494cc0841cbf660a660420e7fb52c33021067fda968d810839fecc346c0841bbf299a360420affb7251b021067fda928d810839fecc146c0841bbf298a360420dfbb4651b021067fdba64d81082bfedd326c0841dbf2999360420e7fb0cc9b021057fdb960d810833fed4b06c0841cff66183604209ff974b1b021067fda9,0x3b46397a3782360e34c6337e31b230122fa62e322be22a6e284a26d6258e244621ca1f221cfe1b5e1a16181e16d6158e136a11460ef60cfe0b06088a076e054a03d60159ff09fd95fb45fa29f889f875f72df459f261f0c1ee45ebf5ea55e965e715e51de37de1dddfb9ddc1dc4ddb5dd9e9d875d785d535d3edd279d105d0f1d001cee5cdf5ccadcb39c891c565c449c1cdbf7dbeb9bcc1bb4db9d9b839b699b525b385b23db0f5af81ae39ac6daaa1a8d5a735a5eda421a281a1399f999e519bd59985976195c1934592818fd98e0d8dcd8cb18a6188c186f58605838982417fc57dcd7b7d79dd783d764574d173b5729970cd70b96f456e556c5d6abd691d67a96585638d616960215dfd5c055a0d581555c5547d5361524550a54f314c5d4abd486d46cd447d430941c13fc93e553ce13a6538c536cd352d33e5324531ad2f312de92c4929cd277d26612411229d215520651ec51d511bb11b9d19fd185d15e113e911c50f750ccd0b01082d0661049503a500a4ff04fd90fb6cf974f7a8f608f3b8f168f04cee28ecb4eae8e8f0e750e52ce3b8e218df18dd78dc30da90d898d750d608d494d34cd1acd00cce98cca0ca7cc908c794c620c454c2b4c114bf74bdd4bb00b858b768b570b2f4b204b090aec4ad24abb0aa10a8c8a6fca588a3bca21c9f489c74997498b09710943c91108e948d208b288988886c872485dc84c0834c823080907e147c487aa878dc76e475707378723070bc6ec46d506b00690866e46518632061285f885d905bc459f85884571055c8548052e050bc4ec44d504b5849e4484446d0455c43bc424841003f603d103b183978378035e03440324830d42f602d942bf42b04299027f025f823d422e421c81f201dac1be01a4018a01624161014f4124c10d80f640dc40ca80b340a4407f4070404e0036c01a000033fed3346cc0419ff695a366020abfb6e51b301056fdb628d98082bfeda946cc0415df6d4a366020cffb4a51b301073fd8528d98082bdeda146cc0419f768ca366020affb6251b301057f5b128d98083b7e5b342cc0419ff699a166020cffb46d0b301067fca368598082bfeda942cc0419ff694a166020e7fb0a50b301057bdb4285980833fad0942cc0419ff6a1a664c20affb74c33261067fda8695930833fed334ac98419ff6a1a164c20cffb4cd0b261067fda5685930833fedb352c18419ff6d5a960c20cffb62d4b061073fdb6661830839fedab30c1841cf72cd9860c20e7fb62cc3061067fda9699830839fecc34cc18419ff6a5a560c20e7fb30d2b061067fdba65583082bfedd32ac18419ff6a58560c20e7fb30c2b061067fda9685830839fecc342c18419ff6e5a520c20cefb72d2906106f7db1694830833fedd32a418411ff6e99520c20cdfb4cca9061067fda5654830833bed2b2a418,0x83180001f2394049e2bb6752a0831d1aa0c4020000f581578aed807ba97314000521e2ba9024a0b41063a3541a8040001eb7bef1407ba9731400051ea407957146a83500800fd10f15db012505a0831d1aa0c4020000f5bdf78aed807b9802b40005203cd4805946805063f8bed9d4f98a0da0a803407815a90eda1c82c014a0a8d506a00b01f521fa439046029efd1aa0d402003a9600f014055efd48058ae28d506a00a28a4d89481500418d8d30620080007aee2db602b6a647306904c690010001ebb6c0564700e0c8c6880200028902b716db5a990418d8d30620080007aedb5c50c6056d4b06d04c698000f55c50256a641063d04c698330001ea0c60541ee82634c198000f474887219b8d706971a0b8021a4137971a098d3000cc726fd20330b8e35c1b801c1f0116be051a44b8634c198024a293602b23801063635a098310040003d9716db0150c72398331ad048008000f581591c0383331ad048000a22e2db602a80a41063634c188020001eb58aaa54c40497141a8000342df58aad94c404a0d40001c824bc5752e614703aa0d40001a1e2bb6752e600a506a0000d0f7de2815752e600a506a0000d200ea4079a3419a835007e8805ae614703aa0d400019defbc576ce600a814a0d40001a43cd4805946801866f8bed9d4f98d1d41a8034018150c9521db02ca34a3833506a00b007521fa023a3419a835007529006055efd480594680a28e76d41a802c0206478aed9d4d1a51c4000a24023c5808199d4d1aa0005147241d015a9146a02066f8aedbcc506a00b008f15db066a34a388001441dfe912e054f1a02802b8020a2929230054074b860cc0001c8255c59716a40ad9891cc19800034815970c00054822812b8b2e2d4d9860002a4122e2da9b30012470b860cc0001a66ffc566c1bfcc20ed1c0f583300006b01cd203331a007f17db06ff31a3983300601507ac198000328610ccc19800643be60c20446f8396901998d00af8bed837f98d1cc19803e6ff48015c683cf0676dc01037c3374846eed80571a0c7c1b80281c83de91c683cbb60cdc1b80246f866e900f435f1a0c7c1b8024300119bf2383203966c1ada431a41c199833007003c863634c010928e30600737d031815690c690900abbff17db79860cc01e0f7a40390ccedb8d706e0080cdd225c1a9e34a3805700402d970056cc48e60d20980003482d97166241300014605b6600ac8e170c19800034348970c683282d2d4857146816865f8bedad4f9851d419415006ab8a914683282d2d4857146815065f8bedbcc28ea0ca0a8031a46b8054c69833000c9a090191a402a570c6acc28e60c419022815064e90ae38d28ee0ca0b8026680665326366616e607e5e5a5c625aee594e58b65742551e53aa51b24f364cba4b7249fe485e460e45a24352420a3fe63d3e,0x1125b4846c3dd8d3060076a580064b1ca0c9d235b03d353c68c7706e009a90ae28d0155bff17db02df3163a83282a00d5701668d04902ab7fdb02df3163a83282a00d5beae2a451a05a054d5215c51a01eb7fe2fb605be6283282a00c5bfd215c02ae34a080a70041450b3ae015023634c1980063d04a008d22e2a37b6c0a98d082600400332c07f485700b56ff1ae0ca0b802407b4808e1675c02cdbe08d8d306601a099f175b06cf3141b415000c885beb1554a9822541b4150001e906e1d8080642bfada1b2a9a5203c47548a3541a0100aa01106ed2094b1a01ec1a7a300d7090c8d218d01460cc035c1c1b95f054c6807b4860cc035c24188296340393ab4860c00e4130046eb634d218300a9049d5801c07b48058c6983300d7071ebd201b9a9e346380570040376906a58d300225ae0e9d5a4029634c1801b0046f6392d218d30640c0293ab004016392d175b329630c398330000680f03da5c348d6cc680507df30c19802c300030713d0afeb665218da431a60cc018f15db3a97300568350000687bef15d4b9802b41a8000343df78aed9cc015a0d40001a2e2db6b52056cc00f60cc008000357c566ded83679801ec19800034bb60c9d206171a02803c057004ac556caa432f98a0da0a80064494526c4a48c01501f41a800034d4806e0d81487da3403c01fc5f6c1b3cc68ea0da0a80402483e03346807061023f17db06df31a3a83682a00f76c0540a5000145a00b155b2a953019803402000190efaea42b60fb4680a00af8bed836798d1d41b4150070610cd41a800642ddfb8b6a40ad9860cc0001a01b83e1bed22db4a96340298006650370c9d22db0a9e3403c0570048376908a65c31a6001e6fa22efdc5b6c056cc00f60cc0001a431fc5f6de618330000670c2d211ccb6058c680530000019940ea6fcc54720b18d01407a85beb155b02df31a3a83682a000a9457ca293623005407d06a0000d217c1b879a900aa8d0030c7f17db5a9f31a3a83682a01005a190afab68734d8150a9a9146a07014a0d00805500803707c0b56fd5f76c4d8150a9a9146a07014a0d00805500881502940005103274816c0f41571a01e02b802408cdf6904dc9b6b60552a4070660060083231a60cc0201a80a8640bed211ba36b6c0a814c8e0c6c1883003904c698048308ea691b16db6b60592a433064014c698330071dfe900f4d4f1a02802b802008b48d8a4df5b0a9006c6894a000ccb6917d011b06006c6980063b5292927d016f1a0cdc00c3089bf4805bc68337003f483e80b4eff1a029c00ed20fa02de3419b8018eff48353c683183d015c011d20fa02d63419980186f866e900dc1571a01e02b80241b8150fa97eefb480540a407c8e60d2e18d30072c556caa54c41291d41a0150001ea58aaa54c412a0d00831d0001e958aad94c412a0d0,0x4094a90c6c698301560003d2d16e2b36b6cc69831020c6c008000f5fc5f6cc69835820c6c0007a0379b86346098005a306fb70c698005ab04601e1bda4047b702398d306601609402723d654b48634c0032815403d634c009c8152bc576cea5cc01531c81a0320080000d60b5cc01531c81a0320080000d29151b2290cb86b03682c0003d2714db1a93300190260000683e99230d0153bff17db79831d81b4160061f4c34054effb60b3e60c7606d0580167d32461a172054effc5f3063b03682c00c3e9edb2402cc358000a9cfa648c34054effc5f6de60c7606d0580187d3241a002a77fe2fb631d81b4160059f44918680a9dff8bedbcc18ed058017920fa61a02a77fe2fb6f3063b0360059f40459210d01002a77fe2fb6f3063b0368268643539230d0141730e8e2e4fa648c341981d1807c361ef9230d43a3063f8bed81561ac0da0b0000f49df38a6d8cc00640980001a0370040c82e4db275c6d0a6070031059201661a029802077d1b0f7c900b30d0141728e9277cd48620621b07ba75c6d0a72406dc35801a81018866f8bed81661ac0005120df2461a02a197e2fb6353e60c7606d05801a2e53ae4835386b0006502a81ef920d4e1a0002e40a9f2461a006197e2fb6353e60c7606c00bf8a1b3cc064a0ceda8000347c576c1b3cc064a0d40001a02103ea901be8d00376df14367980c941b4150077c576ded83679871d41a800034d48f8a3dc1f51af314180186fa001917f17cc506570ed8365008001913ad83287d0d8402000643d480df468050780da37e8038e4ab80ca1846d16e29366536a58c59861d6398310660040001bae2db6b53662c7300014768aca58c30e1c0c1adb3000069652c39a406f63400edb7c50d9e6032306d04c01cd2037b1a97002adb7c50d9e6032306d04c01ad16db06c6301901e99a2dc566d6d994da96316608703d60cc0001b7e2db60d9e62c703d6000291d22d4f1a0f2ed8057003b48634c00890f62b481ecc69834df0dec003258e4b48634c186f8f60dec02c720707480f5c6a6fc1576d63b80240b155b2a953044a83682a0003d3f149b7b60d9e62c7506a0000d3448300648bf4a6c7548a3541a01079014eda80389b87407a18294d48a354183cab8a00b28bb148c69820c818014f40d8401000646245b8a862cc00e9e8818836820d8800800646dc5d8b6634c10e91c419032029043d036100400191fd201c82ce342db830df0cc3db80281f34848b716db0364536a50ca18b31638830662003de0185a44b6b52c6ac71060cc4007ba87b064e902e78d03de0c1985c700571a1be3d82d700285a0c01902f93726dada54b1a91cd21830030041ac31b00883146c3dd8d34860c00d8006f48f7d6cc69a4306014c0037a00785a0d8d2362eb6952c698300a0dac018191a46c526fad98d6980066a580,0x281201fa398312d264902df58a01941132a000a8e0dc168642bfada1b02a1535228d40e02941941502a01007c1aea451a81cbd03350670540a802fa40751bfc6b8300ad6c3ab80241b83e6900aa54b1a01d3d033306205a0b5b30070611d4d23628640592a58d06660da0b5b3006ac5552a620950650540a8000f4d1a70418e804122eb69be517628360c64a754b1a60c0558000f686107db14324b6d52c680ab00029239737c31812634c198101560003d2d1431b29634c19816b660003d21943083e691ad98d0140fbe61836b8600c0c403c1f4f40d6d218d306605ad9802deffc5f6d46a83382a0003d0fd28d063a00168a18fe2bb6a35419dc50001e80c7f17db51aa0ce0a8000f43b8a34e0a8005a295f68b7159b5b6634c1883302b04c008000f6fc5f6de618330260003ce4dc0931a06419818b000b480b37d011b1a95218d8005a4009bf1a0cc16b8014051f4e3477c2d70031f46341982d3002ac556ca6141065a00190e5149b51aa0c40837d0001e806e0083254805546807ddff8bedb54f98d1d41a803c2483701c06414d480f14682f831bbff17db6a9f31a3a83500903176d46837d000286a00b16a2ab6a6d0a54c51800ca0a810000c877dc196a402ca34050327c5f6daa7cc68ea0d401b468365000ca468b7143182a634c1981582b6cc0007afa402ae356e2db1df029c011d201571a1736d833014e0080c237da402c6343dedb3000cc92be18fe282aa3541adc50001e9074b145b2985040003c975413706219be282ca346e2800144864e900ab8d0b9029c00e0c58d34860c4e58006f38376901ad8d2026001e6fa206ff480d7c68330b9e00758aad94c41291d41941502a0003d4b7d6286353104a8350282b40007a9e2bb655218e8d3820254020000f53df78aed81651aa0ce0a8000f48597e808e8d063a00168ef15548120c746a8338220100007a9e286305946a8338276d40007a6a406da341e6804007e8702a04831d067054688040001e9e907d154f1a104053801ca2ec526dad814863634c188168220080007c8e705f48b7151b5b6952c6a473064056098000f6861063b16db6b60c8c6b41100400052473019064b8b6d98d58220005247266fdc5b6c04a54863634c19815826004010000f731a0cac000790148650de1b1a406d63403eeffc5f6daa7cc306600f95257da2b360c6c698330260003d408c21998d06c600194ef981886f6901b58d065029f17db6a9f30c1980346f80fe901af8d7061eeedb802431031690ed914b1a60cc0980175534860c1ad192a928a9be81ac32b486348c80a5dff8bedbcc306600e0c818fa41f4e35c1b801c1b945d8b2d81486363523983102d044010000f75b648b7141b063952c698301560003d64dc189b6d8a1998d48e605a0980100400051a0cae286663523807015600051371,0xed9e2dc536ce62cc18e0d881a03382b04802000647bc5b8aedadb1a9731660c706c40d019c15824010003240c7078c341876ffb60b3e600ae00506f31d9230d0f50c3f1436f9802b80160c81886f02a1b4a63b24078c341b430edff8bedbcc015c00c78a1643c02ac34819c14dfc00192c72c2c8780db868320dfc0163919203c1a00c3f17db06d02b8013800c76df1804c901e036e1ac001840aa03c648c3405430fc5f6c1b7cc18ec0d8019f17cc6063701b1db6000c8878b715db398b3081a031820d9800322de2dc576d6d9cc59831c81a031820d8802000647648b8a3dedb06fb5386acc4060061b56fe000c8e065920dc61a0ca0b4309c2ce48b7186832e060db60901672402cb7186832e06c016093920dc0230381876ffc5f6c0b40ae06305801a6e0328adb1df78b714db3a9b5386b03382b0580007b4e29a93306090960001e73bef16e2bb6b6c6a70d60670560b0000f63b67bf77de2dc536c6a70d20680ce0ac120080003def15db3a902a81a03182c348020000f5bb67bef15d4815c0c60b0d60001ea7bef15db01540d018c161a40100007ade2ba90cb46a833b8a0003d0f15db51a7041968000f3bc576cea68d065a0003cef15cc28e76c1b0833822010003229cc28e0fa1b08338220100032243c06113b67301f43286c2010003221a2dc526cca6d4b1a60c4198158260040007b6e2db6b52c6acc5826000510d16e2b36b6c4a58d3066056098010001ecb8b6d98d598b041958001442c556c01941132a000a8e5149b51a2041968000f3a45b8a0a67a218b301b103106405609001000c8eb8bb1654d98d312387a06c20c81ac1682200800323da2dc566d6d994da9634c188130020003d9716db5a90cac6bcc582600051216be2fb6f300558002a3c8e6913d18d02a9bff17db79802ac0173d38d0159bfd20167003ac556c4cbcc015a000a8ea3aa42f4a340a96ffc5f6d6a7cc015a00c51d52035d1a5e94c96ffc5b53e600ad00650058aad899298a3003803282a04000151a96a8ea90bd28d02a5bff17db79802b4016d227a06b2652826ffc5f6cea40ab00581291c5227a06b634cca6ffc5f6cea7cc015600e6913d035b1a600054cd227a31a02a00e6ffc5f6de6247306600c9bfd203583de352380570044f46901ad8d33202b37fe2fb6753e6247306600e044d227a06b2344c8084dff8bed9d4f9802ad58aaa432f98a0dae280064454801d4683085f07df1436f98d1d41b5c50068619bee08335000c861d4d23e]
def f2046L23 : PackingT := (362,4,7,16,fun i => f2046L23A[i]?.getD 0)
def f2046H0_23A : Array Nat := #[0xa804244132010900848835a80740109b065c210402120109008480424021201090084d2036000c0102008480424021201090084c00a4c20c0103b0334a1c00212010900848042402120109c01a783e8812c010900848042710e4010900848042580f201090084804174122010900848042402120109932a00424812f20a7943d983cc41312025b064781a080e201090084982c4021201090084882b8021201090430f01740212010900848042550ec01090084f215c0212010900848042701438089e453681b4021201090084804240213883f00848042402120109b03b0014802120109c0560042402120109f027f01bc02120109506c80424c0ce0109103d0042601e80109343f8042580a3c8c50084804240212a092743c18013c1394077705d3a2a191dc60ff005f004240213a083a06b8821ec1ce01090084a82780212010900848042402120109507de02d05188680c707480424021320fe0084d0228021201090084b831402138050604a703ac90aa01099051783d8021380c10456004240212010900848042740e72038f05e804240213404e0084f81d3d0b00109008480425c11fc0f8b43300426008c0109b4306819041bf60650084804240212087300848042402120109345680424021280ea00848042440f6010900848042650ef609b1037004271d1c01090084a814f41ee0109207460131418120ccb74680425816e40d5344800426419f207f0084d80000212e0aa0084804240212c02b5071004240212010900848042581fa0109005280425c0bce07e90196a1d40212a095008480426c1f3687d103858220021280e50084c041c02120109008480424021201090084a01c80212209330778042402120109008480427818e0109204700424021201090084c012002138899842c8042402120109003500427800a0109008480427515c600e706200427c13e01090084c812f809a60a4506f0042402120109008480426416cc8690084804240212010900848042402120109706e0042541460109008480427908001090084804240212010900848042402120109000080424c07880cef43a08407413a01090084e83440212010900848042581cd6865d432004240213c104008480424021201098084004241d12407dc045e01e2c10201090084a0298021201098046421c5420001090084903b2d0c5205fc054804240212010990480042410f20109d47980426c18d6028e0540042681f801090084804240213e0ed405c5008f4072885600848042581a4010900848042500b80109905e62168021260cd0084c000ac0d6487a00848040000000100204000000200000080601008100000000000000010040000008080205020000200000080000010080002008000200010000202000040000008100a00018000800008000200000000001,0x4216d814000750084c818c021201090084804240213a06c00848042681600109d04d0042402120109e07]
def f2046H0_23 (h : Nat) : Option (Nat × Nat) := lookupWord 71 464 9 17 9 4 (fun i => f2046H0_23A[i]?.getD 0) h
def f2046H1_23A : Array Nat := #[0x11f20ad60672854011f803d00d9e052e08e011f68b4011e011e011f805d805e011e011e011e603e6022c084a83d6105288540eb800468b620c4011f6044c0aec85e8097609240b1004de075e04e011fa0f560e28073c038285b202120dce0a0011f40de011e011e200c011e4808e0c88040e0cc011e881300ee20e0011e08490054011f4036410fc059e8ab60d2a83960d5211de1124063287060800007685d4057403a8047411a2032c048688ce08a202fc836c8514822011fc086011f405a011e011ee824011ec04a011e011f40a7ae79c08960daa050011ee06b8008408c011ea01a011e011fc01360d720914060011e011f486e011fe042011e011e01192027082a011e011e011f68588856011e011e011f40e6c010011f6078011e011f08a4011fa0b4011e011f80a3a8c668b108bd00ba011e011e4002c06960a8011e011f209a011e011e011ea0b62102011e011e011e011ec0fe011e011e011ea8896111c09cc116806e00abc017000aa09f80c3e845089f801500e920f0011f40f8e07a011e011ea8ae40a4e10ba07ee01e6064e0c740fc00ec011fe0d0011e286ce100a10840bcc0f6884fa835e082e06c011e011e011f8114011ec846011e011e011e20e4011e011fc84048ad801c011e011e011f08c2011e483e011e011e011e011e011e011e011e20ce011f08c1c0006018011e011e011e011e011e011e011f80f2011e011e011e011e011f20b8011ee0246852011e011e011e011e011e007cc8d2011f48b2210dc84b4826800e011f08c4011f2076011e011e011e40be011e2028011f883b002a011f802cc0b22106c0fb2c03e09980ca011e40c028728094e84c6070c030011e0034011e010081c06040000014020080006000000400020080404000101408010481802010000002010103c0004000180007038101400030000200010280600010000003098000006030000610]
def f2046H1_23 (h : Nat) : Option (Nat × Nat) := lookupWord 65 310 9 16 8 4 (fun i => f2046H1_23A[i]?.getD 0) h
def f2046L24A : Array Nat := #[0x1a960a48f1478ed86d1b21ae606519206801c1bde81481c01491e2f6d0d73032c0d00343a1d6f4923c586b980e6b881a0058be148cbdb005244340a8254740d0030622a482196dfd23c5edb1ae6014a3b06c01c2ce917a63583352c151d80400a0f866d208ec68b9ad814c0121f1be549efa45718d7300a51d83600c0c4792382cc68a90505ac012189be3c8b4410cda478bdb05954e35cc0294760d80445f0a42d03a480ea1a05606012828018416918d1ec6f815801c762a48ed23c53dfb6c6b9837c0ac1a82c01c6f8f2548cda478bdb635cc02a0560d41600e04929aa51240a82523c5bd3b646b9818d8e4190086917a15235e34470ccc15bf41600b011044a6a9a3af4196df521b846906609007690dc3538d0cd6fd1d8340cc1601003015d22f46a6a919882b7f1ac1b0059be32a5354bbfdb504322908d02b4720c80383a57d3a4a6a95dd486d91a0568e4190069e86f8c9a436cd4d538d60c8340cc151d416010040324c95fb7fb62a5a9a094846815a3906401c751be32690db56c54e358320d0330547505803cc24dddfb7db6d20a9c6b06a3a828570068096fd5232f6c412900aa354720cc1200d3d8df193486dab65dda9aa71a20815a3b00741cdc5bfa436cd4d538d02b80282d839dfb7db6ad8a9c6815d230058c26fd5216d1ca45708d02a83504803012b7ea9ae02d239480551a63906a090068ca6fe90d4d538d02b5c60d4160100305a77edfae02dc6815d2306a0b005c0d9f5ef3c75fb8b9b8ad66674b2297b6b5e589aa093e294c46ca120f967583639900b3650a2378fa06c22d013387d02ee0f003980037feaa660209ffaa9980827feaa658209ffaa993082ffeaa60c20fff95483083ffeaa58c20bffaa963083ffeaa54c20bffaa9530827feaa64420fffaa981082ffeaa60420bffaa9310837fd93a2020fff54e880837fd91a2020fff14688083ffd31a2020dff662330837fd968cc20fff61a330837fd958cc20fff61633083ffd658cc20dff64633083ffd818cc20fff58633083ffd518cc20dff662110837fd9384420fff60e11083ffd5384420]
def f2046L24 : PackingT := (33,3,7,13,fun i => f2046L24A[i]?.getD 0)
def f2046H0_24A : Array Nat := #[0x140701bba0040280014030078050040620140d00a80502801d801ae043380fa800c406000a0681280281c028004a00501811d4052503bc026bd077c01400a020089400fc02f3048801340281002d20420027bc0fd0070903efa142507d009c044c0050002814024c434c817c0281c035c019300da00970097b42ef802b00d0802cb04cf813d80b3e098d021a024e812a80535008b803340bde041800e481dac0b90044301ed00d200460140c04ef81ee4077602e64292021cd014a01900a00050002800140c02c5026f4030e00db406005005079000400a038184028080731004805000280889900a000501004c200800a00050141104005e01500503d0ae806ec012881380280207f00320050140cc014000a03811f4105a85100a078120802e014000a0601afd0c4014000403815081124046b01e02113c125a06ac01c5200300d9007ae41f80108c0e2207c00a0020248098014004038823680e801400404005000281002190458019c0003808170158018c0280014000a0482408024607900a0400000280014000a05009ec0de0002804188083803d800390465806d812ca0693009c815ac0afa049c01d40059013f201ff00ef210fc081605a1018201e0028120510019d015402816065d01ca01cac0c5c06d8042e82280281c03f10280050040eb2029b047d802c008a0010a4488050380b7805d0402060605040509001903001402070001150017000b000200080002030003041603090113010106030a060100051109050c01030e0c00000b18021000]
def f2046H0_24 (h : Nat) : Option (Nat × Nat) := lookupWord 61 237 8 17 9 4 (fun i => f2046H0_24A[i]?.getD 0) h
def f2046L25A : Array Nat := #[0x410158021482e11a01065f17b60b79823906209006e905c634168cbe2f6cd4f304760c41600dae1484682d197c5ed9a9e628e41a82401a160ca3269016d718d51d83505802e0b9c1008106ff51fa1bebc7ca6f781ea7bcd27896ef39d9ebab674aee7e1ca4b8fe709edfe9bbeb7286d7ed981afbb57069fad1b1a06b3a4668acb4992fb1d862f2c3c9821afc65e7ebb81736add25a82b33962dabd456eaab6952eaa125302a4b143ea8284f1a9b79344a6024b469511259a45447fe8ef91a5a2c4448e86d909ca0b23fca7da0f6b9e143b2e73a0e269b8a362e6b30d2299be32be6450c1e97e82f125b68b2e95cc2a8a5320a2093b026a24b0090d9180221a41f080e8fc81efa3bd87378dde1aea33406068bae1626299050789ba123e21c03e587800dde19782f085960a46129822883ca06ae0c0812e8208030203e80398000dff699980837fda366020dff28d980837fda166020dff285980827fda961820dff6a1930837fda664c20dff619930837fda564c20dff685930837fda960c209ff6a5830837fd9860c20cff66183083ffda660c20dff65983083ffda560c20dff65583083ffd8560c20dff64d83083ffda160c209ff6a483082dfda720c20bbf69883082ffda520c20bdf694830837fd9520c20bef69083082feda220c20bff68483082ff5a120c20bfe680830827fda958c20fff6a163082ffda858c20dff661630836fd9658c20fbf61963083ffda558c20fff295630837fd9558c20fff615630837fd9358c20fff60d63083fdd8358c20fff685630837fda954c209ff6a553083ffda854c20bff6a153083ffca854c20dff66153083ffda654c20bff699530837fd9654c20fff619530837fd9354c20df764d53083ffd8354c20ff760d53083ffd6354c20fff68553083ffca154c209ff6a4530837fd9614c20bff684530837fda864420dff619910837fda364420dff60d910837fc8364420dff58d910837fd5364420dff14d910837fda9604209ff6a5810837fd9860420cff66181083ffda660420fbf29981083bfd8660420fff68d81083ffca360420dff64d81083ffd8360420fff58d81083ffd5360420fff14d810837fd91604209ff6a481082fbda420420bff68c810837fd9320420fff54c810827fda958420bff6a1610837fd9858420dbf659610837fd9358420fff60d61083ffd5358420fff14d61083ff58158420dff6a5310827fda94c420fff6a131082ffda84c420dff66131083ffda64c420bff699310837fd964c420fff61931083ffda54c420bff695310837fd954c420fff61531083ffc854c420fff595310837fd934c420df764d31083ffd834c420fff58d31083fdd634c420fff54d310837fd914c420dfd64531083ffd814c420ffd60531083ffd514c4209ff6a431082ffda50c420dff65431083ffd850c420,0x6023bfe2f6c16f300ac0d41400e0de48869f40e9dff15b6e6206a0a006075244340a809e2f6c16f30c740d41400d0123a1d5f46a629922b8868151960477fc5edb9863a06a0a00a3e9244340abbfe2f6dcc31d035050030376a648868b90e9f4f15b6e618e81a82801c18808efcbf1d4915c05b0d02b0278bdb353cc31d03505004e4886815197c5ed9a9e618e81a8280189b252872907b8de8d5be01f8bdb0d9cc0c8835048044370daf40a40e522b846adff17b6e6106a09007a5354a1d470de30804a41e88d1bfe2f6c367303220d4120130e6b6522b846bc5edb9841a8240161ce90db6347b015801ce03d348c68b86d80ab7fc5e6306a0b0068727b6918d1705c87be2b6dcc60d41600d193486d9a9c698e0f40ac013a4635831bec71ed801c6004839adaf44a6a919548ae11a05512b7fc5edb9863906a0900a8c9a45538d0147a0cb8023482d9a9c698ec18663df0048b46f8de7bb6d5b4ee54e344769183014410da33601102865193483deb69df1a055a963b0062905c234020076ff8bdb05bcc02a831048039482e11a010dff17b60b79805506209006e905c0460e1bfe2f6c1682b83105803348c68b8054dff17b60b79863b0620b006d7011a908d02b6ff8bdb05bcc31c83504803859d22b80b423c6866a0b004852070eaa42345c06f7a78b5b730835048038372a4f6238f4d231a2e00a77fc5adb98c1a82c0201ba52872908d1e83c570eff8b5b73083504803d48468752e0373d3c5e6106a0900586e94a908d2255c5e9e2d6dcc31c83504803b481d5a9c6814c18f4ae3004bbe166340a691835718023486a71ac198eae30038ea7b1707a6918d014eff8b5b73183600d0e4795211a05463f17b6e628e41a82401a2f86e14a915c2340af8bdb7314720d41200e19b486d83d6a415c681402b00516c3bbe854e918d028053bfe2f6dcc51d835058040790e5f44a6a919948ae11a1941577fc5edb98a3906a090098cda4072d482b8d02805600937c372a748c68b802866f15b6e628ec1a82c01e1d25354a903c8ee8d0720abe9e2b6dcc51c835048044150e748aa4b8c6879c010336901e82b8d02805600837c79d202cc680a19bc5ed9a9e628ec1a82c01e192bf6f872a45708d05a0af8bdb353cc51c835048044ea054dfd21b6ad8770b0a92386602882c6b06c021a43e81185b8d0cd801cc2055dfb7c39d202c2a414238b8c6b06c01c1c8f2a40048d02a31f8bdb7304720d41200e0e412522b846815f17b6e6106a090066903b82a32e340a60076db480e5a905466a0b1a0530023961c82ba41718d0cde2b6dcc60d41600cd207905466c6a82053004008a41708d02be2f6c16f314720c41200d0e8045211a057c5edb98a39064017a43538d02a5c01580104837c8e1ddf40574819b1a029dff17b6e628ec1b00869016e340a970,0x6da481ea1a1e478f146ce6064819b8801a3ec910d0cbe2f6c36730c740d002d8e92078868df187c5ed86de60158018db3523eb1c378c3243710d78bdb0d9cc0c9033050046486e06586861b7fc5ed82de601581982801c1481c7a2908d0721bdbfe2f308357080364886865049dff17b6e60158014efb5324434090c7e2b6dcc02b002c378a648868797d21277fc5e628e819b8801cef8f324434090c7e2f6cd4f300ac00c1e6488681504863f17b6e628e81982801a3a8faa423432f8bdb0d9cc51c83200c0def40a4025211a196dff17b6e628e41900701ca41e88d0ca6ff8bdb0d9cc51c83200d5211a197c5edb98a390640123ae90db35232e34dc02980243a2d929aa5481e51a1dc75196dff1798a39066e1008e903ce34c10ca0a60070c875bd102a094846932196dff17b66a798a39064022326918d1e836b0432e008048752394846865b7fc5edb98055006690db0eed4e34328298021483d11a048dff17b6e60154014471e98d1bfdb0b3cc02b80248ed231ac18f437fc5e6015c014476907a635830586ff8bdb353cc02b80348ed20f4c6b0637fc5edb980570058b3472917a0d68d2656ff8bdb353cc02a803b483d306280dff17b6057004a907a634091bfe2f6dcc02b802b483d31a37fc5edb98057004e907a6340a9bfe2f6dcc11d83600b08b483d11a0410037fc5edb980556148eaa42341c86f7a78bcc51c835708034f419b486a71a2e6b605300486e549e9a46340a3bfe2f314760d5c600d1843e0dd29aa4f4522b64686677fc5e628e41ab840223aa908d0721b9e9e2f314720c5c200c0dcf4d231a198b777fc5e628ec18b8c01a7a690d48cd8d1735b0298024ead208e0df1a0528ec192d6a700586e1f064a456c8d2657a78ad4f314720d5c200f3ab481d42c2a71a238f419b0660a82adb0075bf54a908d02431f8b5b7300aa00badb481d4656a6a9c68150530023963a8ca7a6915b6340a3bfe2f31835718037480dda9c68b819982053004abe3ca042d2901523431f8bdb553cc51c83200f17c370094846bc5edaa9e628e4190066903c8598d3040a60077d082d202cc681477fc5edaa9e628ec1b0070b2fa0478d152330b58020610c502a086f5206d4686677fc5edaa9e628e419008e90330598d370db0298020df0dcf7d21b60b31a19bc5aa798a3b066e30078621d06edb2eea40f48d0f2fa78b54f314720cdc20113d3481e86dc6a821e70045be3ca908d02431f8bdb553cc11c0aa00d5211a04bc5edaa9e61064013a40f232e34c15040a6004724a97d065d206dc681477fc5edaa9e6306c01da436c548cd8d11c0a8298027481e42ac698219814c01037b718d3042d60060dd4846812197c5ed8a9e601540161bd1cbba908d26e32f8adb553cc02a803748c6815197c5ed8a9e608ec1982c0181d4910d]
def f2046L25 : PackingT := (134,3,7,15,fun i => f2046L25A[i]?.getD 0)
def f2046H0_25A : Array Nat := #[0x827dc0bb441b00502d0d6612800a0081780280c138f02c0229911f00140f073481e8c26c014040867832c028021011409da07ec15da8c7a47600502d241c0a0d453a83500281411ae05ea00ec0281a07c2021805034043c0de5066805000281691c00a0005000280014000a00050041e80122f045583854149e81df41542232827380a500a0320b1c23ea0b4740800500d05c01408765b03d80280014000a0005000280813500a00050002800140e0229031280d40140e4517834c0248205b00a078437007220c900a00050091d080ba7418ea2b4028168c6e451ea3c640d9aecf041ab843d116ee042446b8a382c1fc014000a0181a002800140f09770498c110c0a95093d2064028020f5c03bb018802800140b074d84500280014000a0383f40281a005d0286a0a1c1dd68eb504c28170019ea0d8a07902072815a014000a0005000280014000a000502819801406028d8440101d082600825a0adc2792106c45c00500117e0140946880503410000d290061a080818a208fc078da294028001404042801f5902a0140903b783ee1112805f807c301c380b4e91fc08c684eb81de014000a00050041b4014000a0681cc0280014030717829e104e0140c098005000280014000a058238028100e500a000502807e014000a04007402800140f049805008117090a3027483218095c100940a0050002800935807c805000281e900540dc818f4014e0a1a05cba2be5067890d900390371c1a0207b603ce84d1826fa0b16057f8375c102a091e446800259022c0b00341005000280014000a000500410e481600a02839d4242014000a0005000280014050874045dd1d20140b022403580280601900a0005000280014000a0381a601b201405094d22e8028001406407805000280014000a0005000281201cc048504240281681e841b805000280014000a0182a002800140b08e0050312340140a030784ec0280812cf085805018007802000a0102740280e823c08a805000280014000a062385422c0140a026c81bd9183c0a600a00050100084047a075005024165c04f00a0005000280014000a0683900281a83200a0005000280200800a0005000280c0c31013e24d10092014000a0005000280014000a00050002800140207e7a0a402800140b025805000280014000a00050281be40ff00a000503427e014000a000501110c409400a07006d81e0014000a000500020180000c070000100400008010080200c0d0180400000000030080000002000040040100000018000080001407000010000000001000000100100410004090000000002000040140901404030000140b0040100405000020000600c04010010040a01800010000080301001000050040c00804008060000000400008020080201800008090040c0000c00806000050201b00000,0xa05700a00050002800140d09ed241c028188b634115828a015461039070081fb1166e8eed032f027101d940b500a073b3402800140048700503116a014000a0000f0028188bb00a02802c0281a11b105b805000280014000a0681580280014000a07a3df01aa014000a000501017c014000a0005000280014000a0005000281081a00a000008c03d40ed00a0602f3423c0140607580502d02ea0b300a058213117ac102405b0050291bc20f300a000501024700dbd41c70467c047812ab095c0344d1488821d0607048002800140e409005000280014000a0004cc0280014000a000500028108a100a01a20c0280014000a0005000280a06e4071b01200281a03e1065682e1d15820c200a0722c4028041087458304140280014000a000428017e014020899a0e500ba014070005825c0280000100a0723400280014000a0784940280a0e800a00050002800140f48200500028100d700a000501105a014040671a4e0904a01404491984c640fe014044182a36c02800140c0113844b81f40140e083a82b2c25ec8b200a0484c80280014000a00050390300140408e904b40280014000a078446c1460140b063a03078156014054576031881ee014000a0200f6]
def f2046H0_25 (h : Nat) : Option (Nat × Nat) := lookupWord 119 623 10 17 9 4 (fun i => f2046H0_25A[i]?.getD 0) h
def f2046H1_25A : Array Nat := #[0x2cd43bf015002d4411980636807e41efa00900b54255b50aa00dcd00bf227a1049401e404c7803441e9202df0281a268c096404ad04f004f002d44081e014805a90073205c5428402ec9d22c00ff07c0049b00fa48182058580c88050016a14a0005a802d4016ab064d057b0216016a00b55b9f7c297e09200b5081a610b3089cf75e805ab80466150a02eca38002d5c12a8447805ab0148012c60a6ca29002d568aa9048a02ff41b4c04700b52811482c088f3b09f805abc240e95a903df02524172010d701bf8545918a016a6496c858e02880124107d88018d1a020645098d219a416c6162c09aca2fe813b212160b3c029f516ac8eaf0b47a022d25760e600b51207741a6a0fe1077005a900ff011ee47b782b251de60340072b04a682464019003c005aa413548415043f00915143490600b54842652924063a408a846942cbe899047308563c004415aa0b4b214ad2d22134501108004425ec02e405c3011a021d201470532a396c28d2089d003a20260220c085c0628814401f9089394adc056c8086016af08da004f82718856105ed855e82adc0af00b51248e902a016a507170081114d2c0094a1005ab40d4a94a075dc0098c1c100a89027a0087022d401680659816ec1dba06e34a3805ab40d00142e039b83aed80588d710462ba4102b84100d800005aa421800405602c027cd1642070046fb01b002d480bad03f501c800a7411200b5684ec02d4016ab03d7223402d4c09cd0657a27c4256016a00b5005aa1062016ac427005ab419140dd00b5584e8d1ee016a80969a49f80ac20277454b018601b128126017d83139036016a202f005a9800ac06fc070da3d0d0d72867505740460502fa02c60470a07cd01f0161b02d381130054c079c4940a15d012ca099548718213816528652414d023e427c80b3c0435042102234884208e48156c29168885459822d9001640d4808ff01f00261a883c041ba369c1dfe018a0a7402dc4286e03e00b51040a425d006630941829491bce882b02f8839202b288ed80a4fa0c84208c0595434805aa81eb8101e031784548272a03d80aaf0041c0e2016aa08ba00d4114ae03630552a319411140a2802c1059280a4016a005a2013b829ec0df9078d21000a0200b0200001c03000000100600c020180c07c010040409005034000440702c0a00406008190082001401004020140102c0a08c5800c0405801088230140009c140180203403008490000b00000004030080b004000002e0080001c1400002000120000c03007000130041f020030200b0182200c01008410040906c110000000800050600680300020000380082100006050070a003000030000405000030020000700c0200c0102c010080800c080080d000050040105c0705001050010000303c0a020090201003007018020000705c02,0xeaa8e400a08054c4009c09b405f7815ec2bb80d9a00d7221ed0ba614540a94824002d520d5142e1052841ac016a00b5005ab10390851100730417803b40f300b5005a8028e016a90b3103eb406280c7540ce80afd0b1a11d941f40451419da03ae4301050380cac03f947d4039f8226686e5004503e481d10154d0019036e426ea0a300b57030e104a016a6008d857c02d4a060d00570533102840d2a46ea03db007040eab4146a39c02d5a84fd4298010402d528f000b5784d9d02628f97474182b601e0016a743848049c1bd889d00b5720b98093c04c600a805a802d5206700b560340c067c84c7411b21fb816b60485091005ab50932097d074ba34c02d4212560831a3ba80d7408a807ff02a402d4406dc093805ab913080fd1085182f38126016ab73e005a8d11c016af018301dd000080b1a046f028441d820c2d0603238c91d3483f204aa83354182213d7012a022e40852924200e1020150d5e13300b520209c15640d79006005a94141010320879a49901e5810720990833e01c620d1903a4a0c011c408a8a00de2282c198a03cf42a4013402d4807600b52200b407608]
def f2046H1_25 (h : Nat) : Option (Nat × Nat) := lookupWord 169 580 10 17 9 4 (fun i => f2046H1_25A[i]?.getD 0) h
def f2046L26A : Array Nat := #[0xa94720a91c57a6da359832c1a00c6faa4cbb64152234154741a00b6faa45a8ea42e234158320a00b681a001ffe88083ffc66107ff84420]
def f2046L26 : PackingT := (3,2,7,9,fun i => f2046L26A[i]?.getD 0)
def f2046H0_26A : Array Nat := #[0x21b04940b6029c090084021b00a8111041007c03680040200213448d0244040041018021003d80c503a403f004021601750e5804300040]
def f2046H0_26 (h : Nat) : Option (Nat × Nat) := lookupWord 8 29 5 14 6 4 (fun i => f2046H0_26A[i]?.getD 0) h
def f2046L27A : Array Nat := #[0x1e82907008901a6ff176d98030018b6148e81c77240686ef4e2e600cb8003a911a7a37f8b98832e20092f8a404480d04b8bb6cc2380c0063d15282a4468cadfe2edb308e83401a8ea43d235066ff176d980ac0163754d216d1a7a717308e832e200c6fa0a911ae2ed953984741a00b47522350632f176ca9cc05600b2f8e8520e242e03404e2edb300641001cb63bbd1528ea42e234dfe2edb310641401f485c469bfc5db0b730158320a00ca446970f4e2adb3106414014df54d21711a0af176d984741905006d21711a32f176c2dcc23a0c8280331bdb4abd3b639c0b734cc965247376528758710017fd98082ffb2c107ff61820bfec9841ffd83083ff906107ff58c20ffea9841ffc53082ffb22107ff60420ffe40841ffd61083ffa62107ff0c420]
def f2046L27 : PackingT := (15,2,7,11,fun i => f2046L27A[i]?.getD 0)
def f2046H0_27A : Array Nat := #[0x10804201080434018040882f01740c6a1201080420108043c080823a8200420108042010ba1660cd00e0109214010804201080420108042010804380080420109a0e0108042010d83c01080420108804010d82ec0eba1001080420108042010a826606e00c010803f80b482a010a8000108043c0dd8280108043886aa0c010804300600420108043e0e0043207600a80d00420108043a090a1801080000008200000000604084]
def f2046H0_27 (h : Nat) : Option (Nat × Nat) := lookupWord 13 89 7 14 6 4 (fun i => f2046H0_27A[i]?.getD 0) h
def f2046H1_27A : Array Nat := #[0x9477c00a2026807cd0446027b00e00868043903eb0060086a0840086a44c103cc01c84292078e076904ad0330086043da43f00860086006cf082e4110086302d2072845b206a00864400607ee0570005d0408021008600860037b002008664083017107f405e3075c05d805f60280086a058904f0086d04d9422242a0086507a801b54793433102c90717045d067008600860086004890309061b4075063c003f029008690858055a0629464106f905ba744d00d24155050873b0032a431e02500860086b0492066c008a0010086603544320086845f0086008660640086540f400cd07da44a40560086008600866070a051403b5013005a00860086f46a0086107910070448e4103478002f94615012907758026060d052a06d00209024301d00866039f02a806b0086b04e9421008664091047244bf4190086b00b008680150086a018041c44759074a03f104cc401a010071f406e045c7042b0810428102ea0389065a6020086a473201aa036042fa4300416646014409069e04600223073a0000086c417d07b00860086702b8068f484c4626412008600806023e601640600860086e041008600866483c009501900860086d7430086043e501e5011103d1031747d9059b00f50530086841a0086a05c0086203a00860086b4054034601600868083008614490086304b0054301fb01410040006000a010002010005000800000310020b000011030000020003000005010405100100000019010003030a040103000101000900030409000400000002020001]
def f2046H1_27 (h : Nat) : Option (Nat × Nat) := lookupWord 65 250 8 16 8 4 (fun i => f2046H1_27A[i]?.getD 0) h
def f2046L29A : Array Nat := #[0x240d62db4c03001c0ffc20]
def f2046L29 : PackingT := (1,1,7,6,fun i => f2046L29A[i]?.getD 0)
def f2046H0_29A : Array Nat := #[0xa0803644039000300c03b040300]
def f2046H0_29 (h : Nat) : Option (Nat × Nat) := lookupWord 2 10 4 10 2 4 (fun i => f2046H0_29A[i]?.getD 0) h
def f2046H1_29A : Array Nat := #[0x40740f03001d43602101403c03dc3910792803c03f82741803c03c03c03f12c03c03e02c03c03c03d40003c03c03c03c03c03c03c03d52403c03c03c03e82803c03c03c03d00850003c03d123c1003c03c03c2002000000]
def f2046H1_29 (h : Nat) : Option (Nat × Nat) := lookupWord 7 55 6 12 4 4 (fun i => f2046H1_29A[i]?.getD 0) h
def f2046Levels : Nat → PackingT
  | 18 => f2046L18
  | 19 => f2046L19
  | 20 => f2046L20
  | 21 => f2046L21
  | 22 => f2046L22
  | 23 => f2046L23
  | 24 => f2046L24
  | 25 => f2046L25
  | 26 => f2046L26
  | 27 => f2046L27
  | 29 => f2046L29
  | _ => emptyPackingT
def f2046Idx0 : Nat → Nat → Option (Nat × Nat)
  | 20 => f2046H0_20
  | 21 => f2046H0_21
  | 22 => f2046H0_22
  | 23 => f2046H0_23
  | 24 => f2046H0_24
  | 25 => f2046H0_25
  | 26 => f2046H0_26
  | 27 => f2046H0_27
  | 29 => f2046H0_29
  | _ => fun _ => none
def f2046Idx1 : Nat → Nat → Option (Nat × Nat)
  | 21 => f2046H1_21
  | 23 => f2046H1_23
  | 25 => f2046H1_25
  | 27 => f2046H1_27
  | 29 => f2046H1_29
  | _ => fun _ => none
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_18_0 : blockT f2046Levels f2046Idx0 f2046Idx1 9 0 0 17 = true := by decide +kernel
set_option maxRecDepth 32768 in
theorem all2046_18 : blockT f2046Levels f2046Idx0 f2046Idx1 9 0 0 17 = true := b2046_18_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_19_0 : blockT f2046Levels f2046Idx0 f2046Idx1 9 1 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
theorem all2046_19 : blockT f2046Levels f2046Idx0 f2046Idx1 9 1 0 2 = true := b2046_19_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_20_0 : blockT f2046Levels f2046Idx0 f2046Idx1 10 0 0 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_20_20 : blockT f2046Levels f2046Idx0 f2046Idx1 10 0 20 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_20_40 : blockT f2046Levels f2046Idx0 f2046Idx1 10 0 40 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_20_60 : blockT f2046Levels f2046Idx0 f2046Idx1 10 0 60 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_20_80 : blockT f2046Levels f2046Idx0 f2046Idx1 10 0 80 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_20_100 : blockT f2046Levels f2046Idx0 f2046Idx1 10 0 100 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_20_120 : blockT f2046Levels f2046Idx0 f2046Idx1 10 0 120 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_20_140 : blockT f2046Levels f2046Idx0 f2046Idx1 10 0 140 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_20_160 : blockT f2046Levels f2046Idx0 f2046Idx1 10 0 160 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_20_180 : blockT f2046Levels f2046Idx0 f2046Idx1 10 0 180 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_20_200 : blockT f2046Levels f2046Idx0 f2046Idx1 10 0 200 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_20_220 : blockT f2046Levels f2046Idx0 f2046Idx1 10 0 220 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_20_240 : blockT f2046Levels f2046Idx0 f2046Idx1 10 0 240 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_20_260 : blockT f2046Levels f2046Idx0 f2046Idx1 10 0 260 5 = true := by decide +kernel
set_option maxRecDepth 32768 in
theorem all2046_20 : blockT f2046Levels f2046Idx0 f2046Idx1 10 0 0 265 = true := (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 0 0 140 125 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 0 0 60 80 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 0 0 20 40 b2046_20_0 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 0 20 20 20 b2046_20_20 b2046_20_40)) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 0 60 40 40 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 0 60 20 20 b2046_20_60 b2046_20_80) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 0 100 20 20 b2046_20_100 b2046_20_120))) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 0 140 60 65 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 0 140 20 40 b2046_20_140 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 0 160 20 20 b2046_20_160 b2046_20_180)) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 0 200 40 25 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 0 200 20 20 b2046_20_200 b2046_20_220) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 0 240 20 5 b2046_20_240 b2046_20_260))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_21_0 : blockT f2046Levels f2046Idx0 f2046Idx1 10 1 0 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_21_20 : blockT f2046Levels f2046Idx0 f2046Idx1 10 1 20 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_21_40 : blockT f2046Levels f2046Idx0 f2046Idx1 10 1 40 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_21_60 : blockT f2046Levels f2046Idx0 f2046Idx1 10 1 60 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_21_80 : blockT f2046Levels f2046Idx0 f2046Idx1 10 1 80 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_21_100 : blockT f2046Levels f2046Idx0 f2046Idx1 10 1 100 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_21_120 : blockT f2046Levels f2046Idx0 f2046Idx1 10 1 120 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_21_140 : blockT f2046Levels f2046Idx0 f2046Idx1 10 1 140 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
theorem all2046_21 : blockT f2046Levels f2046Idx0 f2046Idx1 10 1 0 143 = true := (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 1 0 80 63 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 1 0 40 40 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 1 0 20 20 b2046_21_0 b2046_21_20) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 1 40 20 20 b2046_21_40 b2046_21_60)) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 1 80 40 23 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 1 80 20 20 b2046_21_80 b2046_21_100) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 10 1 120 20 3 b2046_21_120 b2046_21_140)))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_22_0 : blockT f2046Levels f2046Idx0 f2046Idx1 11 0 0 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_22_20 : blockT f2046Levels f2046Idx0 f2046Idx1 11 0 20 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_22_40 : blockT f2046Levels f2046Idx0 f2046Idx1 11 0 40 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_22_60 : blockT f2046Levels f2046Idx0 f2046Idx1 11 0 60 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_22_80 : blockT f2046Levels f2046Idx0 f2046Idx1 11 0 80 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_22_100 : blockT f2046Levels f2046Idx0 f2046Idx1 11 0 100 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_22_120 : blockT f2046Levels f2046Idx0 f2046Idx1 11 0 120 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_22_140 : blockT f2046Levels f2046Idx0 f2046Idx1 11 0 140 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_22_160 : blockT f2046Levels f2046Idx0 f2046Idx1 11 0 160 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_22_180 : blockT f2046Levels f2046Idx0 f2046Idx1 11 0 180 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_22_200 : blockT f2046Levels f2046Idx0 f2046Idx1 11 0 200 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_22_220 : blockT f2046Levels f2046Idx0 f2046Idx1 11 0 220 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_22_240 : blockT f2046Levels f2046Idx0 f2046Idx1 11 0 240 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_22_260 : blockT f2046Levels f2046Idx0 f2046Idx1 11 0 260 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_22_280 : blockT f2046Levels f2046Idx0 f2046Idx1 11 0 280 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_22_300 : blockT f2046Levels f2046Idx0 f2046Idx1 11 0 300 20 = true := by decide +kernel
set_option maxRecDepth 32768 in
theorem all2046_22 : blockT f2046Levels f2046Idx0 f2046Idx1 11 0 0 320 = true := (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 0 0 160 160 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 0 0 80 80 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 0 0 40 40 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 0 0 20 20 b2046_22_0 b2046_22_20) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 0 40 20 20 b2046_22_40 b2046_22_60)) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 0 80 40 40 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 0 80 20 20 b2046_22_80 b2046_22_100) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 0 120 20 20 b2046_22_120 b2046_22_140))) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 0 160 80 80 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 0 160 40 40 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 0 160 20 20 b2046_22_160 b2046_22_180) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 0 200 20 20 b2046_22_200 b2046_22_220)) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 0 240 40 40 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 0 240 20 20 b2046_22_240 b2046_22_260) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 0 280 20 20 b2046_22_280 b2046_22_300))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_0 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 0 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_20 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 20 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_40 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 40 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_60 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 60 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_80 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 80 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_100 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 100 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_120 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 120 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_140 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 140 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_160 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 160 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_180 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 180 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_200 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 200 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_220 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 220 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_240 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 240 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_260 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 260 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_280 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 280 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_300 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 300 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_320 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 320 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_340 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 340 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_23_360 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 360 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
theorem all2046_23 : blockT f2046Levels f2046Idx0 f2046Idx1 11 1 0 362 = true := (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 0 180 182 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 0 80 100 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 0 40 40 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 0 20 20 b2046_23_0 b2046_23_20) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 40 20 20 b2046_23_40 b2046_23_60)) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 80 40 60 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 80 20 20 b2046_23_80 b2046_23_100) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 120 20 40 b2046_23_120 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 140 20 20 b2046_23_140 b2046_23_160)))) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 180 100 82 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 180 40 60 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 180 20 20 b2046_23_180 b2046_23_200) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 220 20 40 b2046_23_220 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 240 20 20 b2046_23_240 b2046_23_260))) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 280 40 42 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 280 20 20 b2046_23_280 b2046_23_300) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 320 20 22 b2046_23_320 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 11 1 340 20 2 b2046_23_340 b2046_23_360)))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_24_0 : blockT f2046Levels f2046Idx0 f2046Idx1 12 0 0 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_24_20 : blockT f2046Levels f2046Idx0 f2046Idx1 12 0 20 13 = true := by decide +kernel
set_option maxRecDepth 32768 in
theorem all2046_24 : blockT f2046Levels f2046Idx0 f2046Idx1 12 0 0 33 = true := (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 12 0 0 20 13 b2046_24_0 b2046_24_20)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_25_0 : blockT f2046Levels f2046Idx0 f2046Idx1 12 1 0 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_25_20 : blockT f2046Levels f2046Idx0 f2046Idx1 12 1 20 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_25_40 : blockT f2046Levels f2046Idx0 f2046Idx1 12 1 40 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_25_60 : blockT f2046Levels f2046Idx0 f2046Idx1 12 1 60 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_25_80 : blockT f2046Levels f2046Idx0 f2046Idx1 12 1 80 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_25_100 : blockT f2046Levels f2046Idx0 f2046Idx1 12 1 100 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_25_120 : blockT f2046Levels f2046Idx0 f2046Idx1 12 1 120 14 = true := by decide +kernel
set_option maxRecDepth 32768 in
theorem all2046_25 : blockT f2046Levels f2046Idx0 f2046Idx1 12 1 0 134 = true := (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 12 1 0 60 74 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 12 1 0 20 40 b2046_25_0 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 12 1 20 20 20 b2046_25_20 b2046_25_40)) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 12 1 60 40 34 (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 12 1 60 20 20 b2046_25_60 b2046_25_80) (@blockT_merge f2046Levels f2046Idx0 f2046Idx1 12 1 100 20 14 b2046_25_100 b2046_25_120)))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_26_0 : blockT f2046Levels f2046Idx0 f2046Idx1 13 0 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
theorem all2046_26 : blockT f2046Levels f2046Idx0 f2046Idx1 13 0 0 3 = true := b2046_26_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_27_0 : blockT f2046Levels f2046Idx0 f2046Idx1 13 1 0 15 = true := by decide +kernel
set_option maxRecDepth 32768 in
theorem all2046_27 : blockT f2046Levels f2046Idx0 f2046Idx1 13 1 0 15 = true := b2046_27_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b2046_29_0 : blockT f2046Levels f2046Idx0 f2046Idx1 14 1 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
theorem all2046_29 : blockT f2046Levels f2046Idx0 f2046Idx1 14 1 0 1 = true := b2046_29_0
theorem tables2046 : ∀ k ≤ 14, ∀ tmax ≤ 1, blockT f2046Levels f2046Idx0 f2046Idx1 k tmax 0 (f2046Levels (2*k+tmax)).1 = true := by
  intro k hk tmax ht
  interval_cases k <;> interval_cases tmax
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 0 0 0 0 = true)
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 0 1 0 0 = true)
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 1 0 0 0 = true)
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 1 1 0 0 = true)
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 2 0 0 0 = true)
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 2 1 0 0 = true)
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 3 0 0 0 = true)
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 3 1 0 0 = true)
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 4 0 0 0 = true)
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 4 1 0 0 = true)
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 5 0 0 0 = true)
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 5 1 0 0 = true)
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 6 0 0 0 = true)
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 6 1 0 0 = true)
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 7 0 0 0 = true)
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 7 1 0 0 = true)
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 8 0 0 0 = true)
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 8 1 0 0 = true)
  · exact all2046_18
  · exact all2046_19
  · exact all2046_20
  · exact all2046_21
  · exact all2046_22
  · exact all2046_23
  · exact all2046_24
  · exact all2046_25
  · exact all2046_26
  · exact all2046_27
  · exact (rfl : blockT f2046Levels f2046Idx0 f2046Idx1 14 0 0 0 = true)
  · exact all2046_29

theorem noSup2046 : ImpossibleT graph 14 1 sup2046.toFinset := by
  have hall := forestT_all f2046Levels f2046Idx0 f2046Idx1 14 (boundsBefore known383)
    (before_sound _ valid383) geomdead tables2046 14 (by decide) 1 (by decide) 0 (by decide)
  have hsame : sameWords (stateSetT f2046Levels 29 0) sup2046 = true := by decide +kernel
  have htgt : targetOf dead = graph := by decide +kernel
  rw [←sameWords_sound hsame, ←htgt]
  exact hall

theorem main2046 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)))) → x1.size = (15 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x6 : ℕ) => Bool.false) Bool.false x5.op) x1.gates = (1 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) := by
  intro C legal first hsz hcnt hfun
  exact close2046 (dead_start (before_sound _ valid383) geomdead tablesdead) noSup2046 C legal first hsz hcnt hfun
end PEqualNP.Outside.L_meta_2046

theorem PEqualNP.Outside.L_meta_2046 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)))) → x1.size = (15 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x6 : ℕ) => Bool.false) Bool.false x5.op) x1.gates = (1 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) :=
  PEqualNP.Outside.L_meta_2046.main2046
