import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10968
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
def signedVertex (m j : Nat) : Sig :=
  if m.testBit (9+j) && m.testBit j then ~~~(vertex m j) else vertex m j
def graphGoal (m : Nat) : Sig :=
  let x := signedVertex m
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 4 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 5 &&& x 8)
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
  (selected mask).map fun (i,a) =>
    let f := (mask >>> 9) &&& 511
    (a,Fin.ofNat 512 f,Fin.ofNat 512 (f ^^^ (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    let f := (m >>> 9) &&& 511
    (a,Fin.ofNat 512 (f ^^^ r),Fin.ofNat 512 (f ^^^ (r ||| (1 <<< i))))

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
def colFree (m z o : Nat) := let free := (m &&& 511) ^^^ (m &&& 511 &&& (z ||| o))
  free ||| ((free &&& (m >>> 9)) <<< 9)
def literalZero (m : Nat) : List Move :=
  let free := m &&& 511
  let ones := free &&& (m >>> 9)
  fixRows (free ^^^ ones) ones
def chartGoal (m : Nat) : Sig :=
  if m.testBit 18 then ((((((((((((inputs.getD 0 zero) &&& (inputs.getD 4 zero)) ||| ((inputs.getD 1 zero) &&& (inputs.getD 5 zero))) ||| ((inputs.getD 2 zero) &&& (inputs.getD 5 zero))) ||| ((inputs.getD 1 zero) &&& (inputs.getD 6 zero))) ||| ((inputs.getD 3 zero) &&& (inputs.getD 6 zero))) ||| ((inputs.getD 0 zero) &&& (inputs.getD 7 zero))) ||| ((inputs.getD 1 zero) &&& (inputs.getD 7 zero))) ||| ((inputs.getD 4 zero) &&& (inputs.getD 7 zero))) ||| ((inputs.getD 2 zero) &&& (inputs.getD 8 zero))) ||| ((inputs.getD 3 zero) &&& (inputs.getD 8 zero))) ||| ((inputs.getD 5 zero) &&& (inputs.getD 8 zero))) else graphGoal m
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
       checkLift (literalZero (colFree free q 0)) G (vars free) (vars q) (graphGoal q) xs &&
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
    let a := ws.getD (bits &&& 31) defaultDecor
    let b := ws.getD ((bits >>> 5) &&& 31) defaultDecor
    decodeBank k (bits >>> 12) (ws++[codeDecor ((bits >>> 10) &&& 3) a b])
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
  let x := fun j =>
    let a := if m.testBit j then v j else 0
    if m.testBit (9+j) && m.testBit j then ~~~a else a
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 4 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 5 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_signed (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    (signedVertex m j.val).getLsbD (asRow v i).val =
    ((if m.testBit (9+j.val) && m.testBit j.val then
      ~~~(if m.testBit j.val then v j.val else 0) else (if m.testBit j.val then v j.val else 0)) : Bits).getLsbD i.val := by
  have h := bit_vertex m v i j
  unfold bit at h
  by_cases e : (m.testBit (9+j.val) && m.testBit j.val) = true <;>
    simp only [signedVertex,e,Bool.false_eq_true,ite_true,ite_false,BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,h]

theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) := bit_signed m v i ⟨j,hj⟩
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
  let n := v.toNat % 76974734310321013718105942979652502807324550410122233000227581439531802351027
  let n := (n ^^^ (n >>> 61))*11400714819323198485
  let n := ((n ^^^ (n >>> 43))*13787848793156543929) % 18446744073709551557
  n ^^^ (n >>> 27)
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
  rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful _ _ _
def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m.testBit 18 then ((((((((((((v 0) &&& (v 4)) ||| ((v 1) &&& (v 5))) ||| ((v 2) &&& (v 5))) ||| ((v 1) &&& (v 6))) ||| ((v 3) &&& (v 6))) ||| ((v 0) &&& (v 7))) ||| ((v 1) &&& (v 7))) ||| ((v 4) &&& (v 7))) ||| ((v 2) &&& (v 8))) ||| ((v 3) &&& (v 8))) ||| ((v 5) &&& (v 8))) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m.testBit 18 = true
  · have coord (j : Nat) (hj : j<9) : (inputs.getD j zero).getLsbD (asRow v i).val = (v j).getLsbD i.val :=
      asRow_bit v i ⟨j,hj⟩
    simp only [chartGoal,chartSamples,e,ite_true,bit,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,
      BitVec.getLsbD_allOnes,BitVec.getLsbD_zero,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,coord 0 (by decide),coord 1 (by decide),coord 2 (by decide),coord 3 (by decide),coord 4 (by decide),coord 5 (by decide),coord 6 (by decide),coord 7 (by decide),coord 8 (by decide)]
  · simpa only [chartGoal,chartSamples,e,Bool.false_eq_true,ite_false] using bit_liftGoal m v i
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
  let len := 12*storedDepth g depth
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
    let more := chosenSteps bank (ops >>> 12) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 10 2,(bank.getD (ops &&& 31) defaultDecor).1,
        (bank.getD (getFieldV ops 5 5) defaultDecor).1) :: more

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
  let start := num*(12*storedDepth g depth+raw.length+depth)
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
  let start := num*(12*storedDepth g depth+raw.length+depth)
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
def knownBase : List (Nat × Nat) := []
theorem validBase : Known knownBase := baseKnown
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low38 : Lower (vars 38) (graphGoal 38) 2 := size_of (hints:=1049936) (by decide +kernel)
def maps38 : List (Nat × List Nat) := [(98,[98,66,50,81]),(38,[]),(328,[130,33,113,98,81,66,49]),(296,[133,117,82,98,66,49]),(290,[130,114,98,66,50]),(74,[101,50]),(194,[33,113,98,66,50,81]),(131,[117,101,32,16]),(162,[114,98,66,50,81]),(146,[117,101,66,50]),(268,[133,117,101,33,49])]
def known38 := extendKnown knownBase 2 maps38
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid38 : Known known38 := extendKnown_ok validBase low38 (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low17 : Lower (vars 17) (graphGoal 17) 1 := size_of (hints:=4) (by decide +kernel)
def maps17 : List (Nat × List Nat) := [(66,[100,84,16]),(36,[84,32,16]),(34,[84,16]),(264,[132,116,100,84,48,32,16]),(72,[100,84,48,32,16]),(288,[132,116,100,80,48,32,16]),(129,[116,100,84]),(130,[116,100,84,16]),(144,[116,100,64,80,48,32,16]),(17,[]),(260,[132,116,100,84,32,16])]
def known17 := extendKnown known38 1 maps17
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid17 : Known known17 := extendKnown_ok valid38 low17 (by decide +kernel)
def g102d3 (i : Nat) : Nat := 0xf
def g102l3 : Packing := (1,0,5,0,0,0,0,g102d3)
def g102samples : Array (Bits × Bits) := #[(0x0,0x0),(0xcfff3fd7f8f9d37bcfff3fd7f8f9d37bcfff3fd7f8f9d37bcfff3fd7f8f9d37bcfff3fd7f8f9d37bcfff3fd7f8f9d37bcfff3fd7f8f9d37bcfff3fd7f8f9d37bcfff3fd7f8f9d37bcfff3fd7f8f9d37bcfff3fd7f8f9d37bcfff3fd7f8f9d37b,0x102449104118214310244910411821431024491041182143102449104118214310244910411821431024491041182143102449104118214310244910411821431024491041182143102449104118214310244910411821431024491041182143),(0xfdfbdefa47062ce6fdfbdefa47062ce6fdfbdefa47062ce6fdfbdefa47062ce6fdfbdefa47062ce6fdfbdefa47062ce6fdfbdefa47062ce6fdfbdefa47062ce6fdfbdefa47062ce6fdfbdefa47062ce6fdfbdefa47062ce6fdfbdefa47062ce6,0x118a2926105abc62118a2926105abc62118a2926105abc62118a2926105abc62118a2926105abc62118a2926105abc62118a2926105abc62118a2926105abc62118a2926105abc62118a2926105abc62118a2926105abc62118a2926105abc62),(0x0,0x0),(0x0,0x0),(0x7bb7fbff9f8eeecd7bb7fbff9f8eeecd7bb7fbff9f8eeecd7bb7fbff9f8eeecd7bb7fbff9f8eeecd7bb7fbff9f8eeecd7bb7fbff9f8eeecd7bb7fbff9f8eeecd7bb7fbff9f8eeecd7bb7fbff9f8eeecd7bb7fbff9f8eeecd7bb7fbff9f8eeecd,0x85014490025428c085014490025428c085014490025428c085014490025428c085014490025428c085014490025428c085014490025428c085014490025428c085014490025428c085014490025428c085014490025428c085014490025428c),(0xf6cffd7de07117b2f6cffd7de07117b2f6cffd7de07117b2f6cffd7de07117b2f6cffd7de07117b2f6cffd7de07117b2f6cffd7de07117b2f6cffd7de07117b2f6cffd7de07117b2f6cffd7de07117b2f6cffd7de07117b2f6cffd7de07117b2,0x6c4220c28a07d6b06c4220c28a07d6b06c4220c28a07d6b06c4220c28a07d6b06c4220c28a07d6b06c4220c28a07d6b06c4220c28a07d6b06c4220c28a07d6b06c4220c28a07d6b06c4220c28a07d6b06c4220c28a07d6b06c4220c28a07d6b0),(0x0,0x0),(0x0,0x0)]
def g102columns : IndexTree ColumnInfo := (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(4,0,98,0,2),(0,4,66,32,2),(64,0,38,0,2),(0,64,36,2,2)]) (IndexTree.leaf [(0,6,0,96,1),(4,2,0,96,1),(66,0,36,0,1),(2,64,36,0,1),(36,0,66,0,1)])) (IndexTree.fork 4 (IndexTree.leaf [(32,4,66,0,1),(68,0,34,0,1),(0,68,0,34,1),(0,96,0,6,1)]) (IndexTree.leaf [(64,32,0,6,1),(2,0,36,0,1),(0,2,0,96,1),(32,0,66,0,1),(0,32,0,6,1)])))
def g102autos : Array (List Nat) := #[[],[98,81]]
def g102levels : Nat → Packing
  | 3 => g102l3
  | _ => emptyPacking
def g102index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g102 : Forest := ⟨102,3,fun j => g102samples[j]?.getD (0,0),g102columns,g102autos,g102levels,g102index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom102 : graphValid g102 (boundsBefore known17) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s102_3_0 : block g102 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all102_3 : block g102 3 0 1=true := s102_3_0
theorem tables102 : checkedTables g102 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g102 0 0 0 = true)
  · exact (rfl : block g102 1 0 0 = true)
  · exact (rfl : block g102 2 0 0 = true)
  · exact all102_3

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low102 : Lower (vars 102) (graphGoal 102) 4 := lower_forest (g:=g102) (i:=0) (hints:=17827152) (before_sound known17 valid17) geom102 tables102 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps102 : List (Nat × List Nat) := [(360,[133,82,114,66,49]),(354,[134,98,114,66,50,81]),(330,[134,101,117,49,33]),(298,[129,113,97,49,33]),(106,[101,50]),(195,[117,32]),(102,[]),(166,[118]),(163,[117,101,32]),(418,[134,114,66,50,81]),(202,[101,117,50]),(178,[117,101,66,50]),(210,[117,66,50]),(332,[133,117,49])]
def known102 := extendKnown known17 4 maps102
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid102 : Known known102 := extendKnown_ok valid17 low102 (by decide +kernel)
def g362d5 (i : Nat) : Nat := 0x184003a683f440fd083e800
def g362l5 : Packing := (3,1,7,0,0,5,0,g362d5)
def g362d6 (i : Nat) : Nat := 0x101820200bf
def g362l6 : Packing := (1,0,7,2,3,0,0,g362d6)
def g362samples : Array (Bits × Bits) := #[(0x0,0x0),(0xa83139914f84407fb4df77cb76957fff75ffef84dfd5ef974d3e5f12df506273229f0880ff69beef96ed2afffeebffdf09bfabdf2e9a7cbe25bea0c4e6453e1101fed37ddf2dda55fffdd7ffbe137f57be5d34f97c4b7d4189cc8a7c2203fda6,0x88a00560592806590cc80044908159068308028c1e6000380a2849808111400ac0b2500cb2199000892102b20d061005183cc0007014509301022280158164a01964332001124205641a0c200a30798000e028a126020445002b02c94032c86),(0x0,0x0),(0xf34ac44cb0330781fa7cf9dafe7edee59ba8eef3bdefddfb9ec9def875e695889960660f03f4f9f3b5fcfdbdcb3751dde77bdfbbf73d93bdf0ebcd2b1132c0cc1e07e9f3e76bf9fb7b966ea3bbcef7bf77ee7b277be1d79a56226581983c0fd3,0x28250015016784017868822c481180184d0a20421a4c1910c00008418c504a002a02cf0802f0d10458902300309a144084349832218000108318a0940054059e1005e1a208b12046006134288108693064430000210631412800a80b3c200bc3),(0x0,0x0),(0x549512a30f48be3065dfbff52beebf14674ebdddd7773fedf5ebf5c7bca92a25461e917c60cbbf7fea57dd7e28ce9d7bbbaeee7fdbebd7eb8f7952544a8c3d22f8c1977effd4afbafc519d3af7775ddcffb7d7afd71ef2a4a895187a45f1832e,0x100a009626d1e1064010828a455680485020f160201d84824140a020402014012c4da3c20c802105148aad0090a041e2c0403b09048281404080402802589b47841900420a29155a01214083c580807612090502808100805004b1368f08320),(0xe9286d1070b66bde5033cdfde17d4dfbbdbff0ef6dfff2e3f297636fafd250da20e16cd7bca0679bfbc2fa9bf77b7fe1dedbffe5c7e52ec6df5fa4a1b441c2d9af7940cf37f785f537eef6ffc3bdb7ffcb8fca5d8dbebf4943688385b35ef281,0x86001028fa086b9a0002215234024a4182454914001082c015117020310c002051f410d734000442a468049483048a9228002105802a22e04062180040a3e821ae6800088548d00929060915245000420b005445c080c430008147d0435cd000),(0x0,0x0),(0x3ec6826e8049bce38b0f7affffa7f39bdb5fd73f266a39dfef76aafd627d8d04dd009379c7161ef5ffff4fe737b6bfae7e4cd473bfdeed55fac4fb1a09ba0126f38e2c3debfffe9fce6f6d7f5cfc99a8e77fbddaabf589f6341374024de71c58,0x900005e29c9060e2830201d01282138310c090a961b02420008195004120000bc53920c1c5060403a02504270621812152c360484001032a00824000178a7241838a0c0807404a084e0c430242a586c09080020654010480002f14e483071418)]
def g362columns : IndexTree ColumnInfo := (IndexTree.fork 37 (IndexTree.fork 18 (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(2,0,360,0,4),(8,0,354,0,4),(32,0,330,0,4),(64,0,298,0,4)]) (IndexTree.leaf [(256,0,106,0,4),(0,2,264,96,3),(0,8,34,320,3),(0,32,72,258,3),(0,64,288,10,3)])) (IndexTree.fork 4 (IndexTree.leaf [(0,256,66,40,3),(0,10,0,352,2),(34,0,328,0,2),(2,32,72,256,2)]) (IndexTree.leaf [(32,2,264,64,2),(66,0,296,0,2),(2,64,288,8,2),(64,2,264,32,2),(0,258,0,104,2)]))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(0,40,0,322,2),(72,0,290,0,2),(8,64,288,2,2),(64,8,34,256,2)]) (IndexTree.leaf [(264,0,98,0,2),(8,256,66,32,2),(256,8,34,64,2),(0,96,0,266,2),(288,0,74,0,2)])) (IndexTree.fork 5 (IndexTree.leaf [(32,256,66,8,2),(256,32,72,2,2),(0,320,0,42,2),(2,40,0,320,1),(32,10,0,320,1)]) (IndexTree.leaf [(34,8,0,320,1),(74,0,288,0,1),(10,64,288,0,1),(64,10,0,288,1),(8,258,0,96,1)])))) (IndexTree.fork 19 (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(256,10,0,96,1),(264,2,0,96,1),(98,0,264,0,1),(2,96,0,264,1)]) (IndexTree.leaf [(96,2,264,0,1),(290,0,72,0,1),(32,258,0,72,1),(258,32,72,0,1),(2,320,0,40,1)])) (IndexTree.fork 5 (IndexTree.leaf [(64,258,0,40,1),(66,256,0,40,1),(8,96,0,258,1),(64,40,0,258,1),(72,32,0,258,1)]) (IndexTree.leaf [(296,0,66,0,1),(40,256,66,0,1),(256,40,0,66,1),(328,0,34,0,1),(8,320,0,34,1)]))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(320,8,34,0,1),(32,320,0,10,1),(256,96,0,10,1),(288,64,0,10,1)]) (IndexTree.leaf [(10,0,288,0,1),(2,8,0,320,1),(8,2,0,96,1),(258,0,72,0,1),(2,256,0,40,1)])) (IndexTree.fork 5 (IndexTree.leaf [(256,2,0,96,1),(40,0,66,0,1),(8,32,0,258,1),(32,8,0,320,1),(96,0,264,0,1)]) (IndexTree.leaf [(32,64,0,10,1),(64,32,0,258,1),(320,0,34,0,1),(64,256,0,40,1),(256,64,0,10,1)])))))
def g362autos : Array (List Nat) := #[[],[101,131],[133,49],[129,97,81,49],[134,81],[49,129,99,81],[83,97],[83,81,131,97],[101,83,49,129],[99,129]]
def g362levels : Nat → Packing
  | 5 => g362l5
  | 6 => g362l6
  | _ => emptyPacking
def hashg362l6 (i : Nat) : Nat := 0x28801da5280400c86a2a9a06c3365400004c8000011001f8c000002034
def g362index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 5 24 3 9 2 3 (hashg362l6)
  | _ => fun _ => none
def g362 : Forest := ⟨362,6,fun j => g362samples[j]?.getD (0,0),g362columns,g362autos,g362levels,g362index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom362 : graphValid g362 (boundsBefore known102) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s362_5_0 : block g362 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s362_5_1 : block g362 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all362_5 : block g362 5 0 3=true := (@block_merge g362 5 0 1 2 s362_5_0 s362_5_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s362_6_0 : block g362 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all362_6 : block g362 6 0 1=true := s362_6_0
theorem tables362 : checkedTables g362 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g362 0 0 0 = true)
  · exact (rfl : block g362 1 0 0 = true)
  · exact (rfl : block g362 2 0 0 = true)
  · exact (rfl : block g362 3 0 0 = true)
  · exact (rfl : block g362 4 0 0 = true)
  · exact all362_5
  · exact all362_6

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low362 : Lower (vars 362) (graphGoal 362) 7 := lower_forest (g:=g362) (i:=0) (hints:=12902752336) (before_sound known102 valid102) geom362 tables362 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps362 : List (Nat × List Nat) := [(362,[])]
def known362 := extendKnown known102 7 maps362
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid362 : Known known362 := extendKnown_ok valid102 low362 (by decide +kernel)
def g490 : Forest := ⟨490,7,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low490 : Lower (vars 490) (graphGoal 490) 8 := lower_discard (g:=g490) (ci:=(128,0,362,0,7)) (hints:=13171187792) (before_sound known362 valid362) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps490 : List (Nat × List Nat) := [(490,[])]
def known490 := extendKnown known362 8 maps490
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid490 : Known known490 := extendKnown_ok valid362 low490 (by decide +kernel)
def g227 : Forest := ⟨227,4,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low227 : Lower (vars 227) (graphGoal 227) 5 := lower_discard (g:=g227) (ci:=(32,0,195,0,4)) (hints:=17825879) (before_sound known490 valid490) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps227 : List (Nat × List Nat) := [(230,[101,117,32]),(227,[]),(482,[101,117,128,64,48,32]),(234,[118,48,32]),(242,[64,48,32])]
def known227 := extendKnown known490 5 maps227
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid227 : Known known227 := extendKnown_ok valid490 low227 (by decide +kernel)
def g110 : Forest := ⟨110,4,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low110 : Lower (vars 110) (graphGoal 110) 5 := lower_discard (g:=g110) (ci:=(4,0,106,0,4)) (hints:=17851728) (before_sound known227 valid227) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps110 : List (Nat × List Nat) := [(167,[117,101,48,32]),(426,[133,81,115,50,66,97]),(419,[83,133,101,115,67,32]),(458,[49,129,114,99,66,81]),(203,[117,32]),(182,[118,67]),(434,[83,133,101,115,66]),(218,[101,117,50,66]),(334,[134,101,117,49,33]),(110,[])]
def known110 := extendKnown known227 5 maps110
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid110 : Known known110 := extendKnown_ok valid227 low110 (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1048660) (by decide +kernel)
def maps51 : List (Nat × List Nat) := [(165,[116,100,33]),(394,[84,132,117,100,49,16,32]),(417,[133,81,116,97,49,33]),(393,[84,132,117,100,49,33]),(201,[84,117,100,49,33]),(51,[]),(180,[117,84,65,97,49,32]),(83,[101]),(53,[33]),(281,[133,117,101,49,33]),(432,[84,132,81,64,113,96,49,32]),(408,[132,117,65,16,96,49,32]),(305,[133,117,81,97,49,33]),(216,[117,65,16,96,49,32]),(404,[132,117,65,97,49,32]),(89,[101,49,33]),(389,[84,132,117,100,33]),(277,[133,117,101,33]),(390,[84,132,117,100,16,32]),(108,[84,100,49,32]),(326,[133,117,100,16,32])]
def known51 := extendKnown known110 3 maps51
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid51 : Known known51 := extendKnown_ok valid110 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low226 : Lower (vars 226) (graphGoal 226) 3 := size_of (hints:=286261328) (by decide +kernel)
def maps226 : List (Nat × List Nat) := [(226,[])]
def known226 := extendKnown known51 3 maps226
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid226 : Known known226 := extendKnown_ok valid51 low226 (by decide +kernel)
def g231d6 (i : Nat) : Nat := 0x204838ff
def g231l6 : Packing := (1,0,8,0,0,0,0,g231d6)
def g231samples : Array (Bits × Bits) := #[(0xe56ffecdcf7faf4c0db71aeb17fdd7affffaf6a983e3eef786db9e7f13abc7dccf7a6676f72b2d8689331ddeaeebfd9017df95ffcda3de3b723d7a0ff3bfa5a16ffbe6371c95b535fbb53a64a100010cd44400024062450209008eee0693a377,0x4e77c2f05e7e10867c31240100a148086d052800a35820a904a368417f6dc0793d0512191a5294aa2c1882a66b923012046c681023087030840b460f8490c98c354106c00805227c226846e86338004091013d1d1b6107fa62708ea60293a147),(0xabbfcbdbbcf1167ea658c4d59cf32ffb6d8e65be7eff7b3f7a7f336ffe7ac80a236b9bdedf9dd7bd6e5ef375f1ff7ee3cdb9ffcb7fd4fff7cf720d9af57ffaff5aed39bcf3bbd5feffe775efbfbffec2028bdd7da69db2f5e62f3b10f33db0c3,0x988610028105260000100102000001282a00004580000006408900864804438c9509c024600424408405aa200010010c00250002032843000298006004082270b00001c068c00424a000002220814004808900840028a0021110083103043),(0x56227ff3ff8f49f3fee37d7ef1c4b7cfc7bffded94f5370fb9e5fb90bfedf6ebdc8ee307ae7b76f9d5ef838a5ea60beefd3b7fdd9bbe2d580dc3faf19eb37082f852b0719b5aebc51e5aff5fca400031293022801900080810d150a50c4f5ddf,0x4c08ecd810f40250161400ef80700095b3c002445d1e403b4068cc5c82605a6838412074924f3a641508280cd9010ae050cf606200483407542db042b0420ea2a163daa42465bd06583e3087ab034c0c1a088782b41146ced36550a00c0f18df),(0x0,0x0),(0x0,0x0),(0x7cdf6f6e4b18ff99da3befaf7a7a1e1fde7babfc75cfe5fce1ff7f9fe4747ffb3e8d071b67fd7a677ff1fbeb3f3fcbaee4d8f0d4d34a05c6a5bdb76fdfee4d4aa0e9efda455fea576f79baf3d7e660312930a3a93b88181896f366572942ed2e,0x31120102ae01c42400034e000d0d9c6a0c0d50918280b4402483120075012583462680010410001108a50301041c50190f00988de601017000420415411521515814215843000098a501840840d0b0a285154001400c01312c9a26572040c520),(0x173242d9b47567c659ef647c6b8f43f3e075efbeaf0febe7ff5f75e39ebcbab45cff99fde0d2919a8c0f276aaf15ec7d570e46a7697776ded7d2bd6f6fccfebfe74599b467f4a9cec1a3558afed9924200880c00041080a540005e79b8f70191,0x6ed023149950a0000c80b04ec68538a8e83d56cdf02677513391002a341169b382022342d5b9e7b400973d81015c0ad0203110a4f617c92bcd4d521ba9f50d415064a90223f143741815c179dd0051c040b6222686a82d75ffdc4e7938e70190),(0x9de3b5a45faebc7977e59323873feed7fdf33ad7ebf89df57f198c165df3559df3ba7ebb3a06cce2beeafeb7e4d79ff9bbff79ee6fadc86f79dde9b71addeff77f76e65bbee6f7e83d4efcbf31800d8cd6475056c0676742290ca5eb6eac5a70,0x2100200601010e2000ce986003029377801856bc58a4dd12a3080526808221000012ac0260080804036708011440820c00031004149701420aa09000606f303188000901422841028815a0121c4021230ea240202010d0059d8c20496c2c4a30),(0x0,0x0)]
def g231columns : IndexTree ColumnInfo := (IndexTree.fork 83 (IndexTree.fork 41 (IndexTree.fork 20 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(1,0,230,0,5),(0,1,102,128,5),(4,0,227,0,5),(0,4,195,32,5),(64,0,167,0,5)]) (IndexTree.leaf [(65,0,166,0,4),(129,0,102,0,4),(128,1,102,0,4),(36,0,195,0,4),(32,4,195,0,4)])) (IndexTree.fork 5 (IndexTree.leaf [(68,0,163,0,4),(32,0,195,0,4),(0,64,165,2,4),(128,0,102,0,4),(5,0,226,0,3)]) (IndexTree.leaf [(0,5,66,160,3),(1,4,194,32,3),(4,1,98,128,3),(0,65,36,130,3),(64,1,38,128,3)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(66,0,165,0,3),(2,64,165,0,3),(0,68,129,34,3),(64,4,131,32,3),(0,96,129,6,3)]) (IndexTree.leaf [(64,32,129,6,3),(0,192,36,3,3),(64,128,36,3,3),(0,7,0,224,2),(1,6,0,224,2)])) (IndexTree.fork 5 (IndexTree.leaf [(4,3,0,224,2),(5,2,0,224,2),(2,65,36,128,2),(66,1,36,128,2),(37,0,194,0,2)]) (IndexTree.leaf [(32,5,66,128,2),(33,4,194,0,2),(36,1,66,128,2),(69,0,162,0,2),(0,69,0,162,2),(65,4,130,32,2)])))) (IndexTree.fork 21 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(68,1,34,128,2),(133,0,98,0,2),(128,5,66,32,2),(129,4,66,32,2),(132,1,98,0,2)]) (IndexTree.leaf [(0,97,0,134,2),(64,33,0,134,2),(193,0,38,0,2),(1,192,36,2,2),(65,128,36,2,2)])) (IndexTree.fork 5 (IndexTree.leaf [(128,65,36,2,2),(129,64,36,2,2),(192,1,38,0,2),(2,68,129,32,2),(66,4,129,32,2)]) (IndexTree.leaf [(2,96,129,4,2),(66,32,129,4,2),(2,192,36,1,2),(66,128,36,1,2),(100,0,131,0,2),(4,96,129,2,2)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(32,68,129,2,2),(36,64,129,2,2),(68,32,129,2,2),(96,4,131,0,2),(0,196,0,35,2)]) (IndexTree.leaf [(64,132,0,35,2),(0,224,0,7,2),(64,160,0,7,2),(2,0,165,0,3),(0,32,129,6,3)])) (IndexTree.fork 5 (IndexTree.leaf [(0,128,36,3,3),(0,3,0,224,2),(1,2,0,224,2),(2,1,36,128,2),(33,0,194,0,2)]) (IndexTree.leaf [(0,33,0,134,2),(32,1,66,128,2),(1,64,36,2,2),(1,128,36,2,2),(0,6,0,224,2),(2,4,129,32,2)]))))) (IndexTree.fork 41 (IndexTree.fork 20 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(4,2,0,224,2),(2,32,129,4,2),(2,128,36,1,2),(4,32,129,2,2),(4,64,129,2,2)]) (IndexTree.leaf [(132,0,98,0,2),(0,132,0,35,2),(128,4,66,32,2),(96,0,131,0,2),(32,64,129,2,2)])) (IndexTree.fork 5 (IndexTree.leaf [(0,160,0,7,2),(192,0,38,0,2),(128,64,36,2,2),(2,5,0,160,1),(2,33,0,132,1)]) (IndexTree.leaf [(32,3,0,192,1),(33,2,0,192,1),(67,0,36,0,1),(3,64,36,0,1),(64,3,0,160,1)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(65,2,0,160,1),(131,0,36,0,1),(3,128,36,0,1),(128,3,0,96,1),(129,2,0,96,1)]) (IndexTree.leaf [(130,1,36,0,1),(4,33,0,130,1),(1,68,0,34,1),(4,65,0,130,1),(64,5,0,160,1)])) (IndexTree.fork 5 (IndexTree.leaf [(1,132,0,34,1),(97,0,130,0,1),(1,96,0,6,1),(32,65,0,130,1),(65,32,0,6,1)]) (IndexTree.leaf [(161,0,66,0,1),(1,160,0,6,1),(128,33,0,6,1),(129,32,0,6,1),(160,1,66,0,1),(38,0,129,0,1)])))) (IndexTree.fork 21 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(6,32,129,0,1),(32,6,0,192,1),(34,4,129,0,1),(36,2,0,192,1),(70,0,129,0,1)]) (IndexTree.leaf [(6,64,129,0,1),(64,6,0,160,1),(68,2,0,160,1),(2,132,0,33,1),(128,6,0,96,1)])) (IndexTree.fork 5 (IndexTree.leaf [(132,2,0,96,1),(98,0,129,0,1),(34,64,129,0,1),(2,160,0,5,1),(194,0,36,0,1)]) (IndexTree.leaf [(130,64,36,0,1),(164,0,66,0,1),(4,160,0,3,1),(32,132,0,3,1),(36,128,0,3,1),(160,4,66,0,1)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(196,0,34,0,1),(4,192,0,3,1),(68,128,0,3,1),(128,68,0,34,1),(32,192,0,3,1)]) (IndexTree.leaf [(96,128,0,3,1),(128,96,0,6,1),(192,32,0,6,1),(0,2,0,224,2),(3,0,36,0,1)])) (IndexTree.fork 5 (IndexTree.leaf [(1,32,0,6,1),(6,0,129,0,1),(34,0,129,0,1),(32,2,0,192,1),(64,2,0,160,1)]) (IndexTree.leaf [(130,0,36,0,1),(128,2,0,96,1),(4,128,0,3,1),(160,0,66,0,1),(32,128,0,3,1),(128,32,0,6,1)]))))))
def g231autos : Array (List Nat) := #[[],[117,32]]
def g231levels : Nat → Packing
  | 6 => g231l6
  | _ => emptyPacking
def g231index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g231 : Forest := ⟨231,6,fun j => g231samples[j]?.getD (0,0),g231columns,g231autos,g231levels,g231index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom231 : graphValid g231 (boundsBefore known226) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s231_6_0 : block g231 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all231_6 : block g231 6 0 1=true := s231_6_0
theorem tables231 : checkedTables g231 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact (rfl : block g231 4 0 0 = true)
  · exact (rfl : block g231 5 0 0 = true)
  · exact all231_6

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low231 : Lower (vars 231) (graphGoal 231) 7 := lower_forest (g:=g231) (i:=0) (hints:=17827159) (before_sound known226 valid226) geom231 tables231 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps231 : List (Nat × List Nat) := [(483,[130,66,50]),(235,[101,50]),(246,[117,66,32,48]),(231,[]),(498,[32,128,66,48]),(250,[117,101,66,48]),(238,[101,117,32,48])]
def known231 := extendKnown known226 7 maps231
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid231 : Known known231 := extendKnown_ok valid226 low231 (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low55 : Lower (vars 55) (graphGoal 55) 4 := size_of (hints:=1049940) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(425,[133,82,116,98,49]),(395,[132,117,100,48,32,16]),(457,[33,129,116,81,98,49]),(115,[98,50,81]),(55,[]),(440,[84,132,82,64,16,114,97,48]),(410,[132,117,66,98,48]),(313,[133,117,82,98,49]),(307,[130,114,98,50]),(472,[66,132,64,80,114,97,48]),(412,[84,132,117,64,32,33,97,48]),(345,[130,33,113,81,98,49]),(397,[84,132,117,100,33,49]),(285,[133,117,101,33,49]),(406,[132,117,66,98,32,48]),(391,[132,117,100,32,16]),(454,[66,33,129,116,98,32,81,48]),(398,[84,132,117,100,33,16,48])]
def known55 := extendKnown known231 4 maps55
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid55 : Known known55 := extendKnown_ok valid231 low55 (by decide +kernel)
def g427d6 (i : Nat) : Nat := 0x180820ff
def g427l6 : Packing := (1,0,8,0,0,0,0,g427d6)
def g427samples : Array (Bits × Bits) := #[(0xcd5b6e4aad16dbaffedbe7f6eb6b925e177d780b3449d7ddde2935c9139fa9afbfb9271ea0db4e2b8dfbb9c1fd16c197e99b1449ccf9b6fd942fe279f7dc4efbfb8492bb878d59f97ff195fecf6e1000601a002105134620c001a8cd4627b45d,0x2aa420a5266108c900055a2d160522e2380162ca80899532a8ae620817a44859444c3839c258325981d105fcaa410101009678108c2c252685a520949034c04055eadc305054c904e815dbce32719220bc4503229a6104fda5d1a8cc4602b44d),(0x95ec3ec3c7d6b76ccf7b7ef9bdf6f6d9ecd9e75eff7cf96feffc56fbbfe75f7efbd797d97eeddb7e46deac5601f53ef63de7a9bea771cc97ebfa51a6bd32713fd39bd7f57ff39264c67afba705d7258a94801b1aa0e4b91e22c6e6b0d6c2c8ab,0x68020092110ba824002022415aa0902090440581628f120a14e00d46400e5438c0d642110400005908a524e62450011025010808004210049a91b481840006018e05009829181181a11c2345b011b8800022405c2086075a452a2a0d6c20021),(0x0,0x0),(0x119feeb78b8ddedcd7973cb93a9fadcaef5f97cff5b9fdb56cc648a56fdc9f8e9364e8e32f4cabd38fd3e51b3b8acbbed13b76bc1bef1beadfd39f551da9fd70bf33c632adfe7697331ef8acead24a1109448440480000801431d4ea0ac99f31,0x5c5ac405302094806ebb54603284082f42005ead89424447131e51465c54cc0ff072018aaa074f203678908810019500accf9a08d10d14a68906a2ee50220108b4dd57610d022a2d21871f03cea6201e602cd60411447d99fd8554c202c19f31),(0x0,0x0),(0x7fcd3770bcf9b593ab7154ccf6efbaa61eeaa42e9a66ffc6fdb7edf3dab0fa79de877fcfde0b54ff7f368e37eff3b644b379ce5ffaaced5fc960b96b3371be1fb7d939dfbbc5af4fdb74e57c7432a4e41621798c9248a94729897f52e130e03d,0x50500402026101480b495002a200e09042003ca58196008f0031cd018258008463700084800f0d124044a1a119081700710f402548018c742252a436c4af6288c108836249403c60a44408438400042087a0804029170d8859855d520120c01c),(0x0,0x0),(0xaa34c30ff92f7cfa1c6fffb3fb9b41bdbad7dffcc5fb5fbbdaf9b33de5abf7fb3e7f7e7b13fea76ffefbf3f88efe8ddb6edf9fa72537f86978dfeeaede174ddb4cef3ecff5cad9bdddf913fff14f110ae09a023325b75638c2465855177f1ad2,0x40020510488241140778a400c800001002fa10056156004856011023085a02a402a081c6288784006c00880105301868a520820000911a5920420422650b2484020500442d0234a3002024000480645403880800000213025a2c5011013d0a92),(0xfbeffdbed76b127f6ca4c5b7b7456d63cbf7fbf7afb7162f3553fa77cddc1c2fe58adfa6e1b97ee473a6d2effe4df9addf7e67f2dcef57d83f452dff76cfbfe477f7e9a772f764e67ae7af5dfabaca750b65e4c45a0800c11d3991aff99a2706,0x21042240889c623280000a0d085a04400845014224210000e0000288202010600c04304040c0a0848103421480e420b1003021900672620900205901235088460a20209c201900824210400c3148898008020122048882660278802df81a2002)]
def g427columns : IndexTree ColumnInfo := (IndexTree.fork 84 (IndexTree.fork 42 (IndexTree.fork 21 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(1,0,426,0,5),(0,1,298,128,5),(8,0,419,0,5),(0,8,163,256,5),(9,0,418,0,4)]) (IndexTree.leaf [(129,0,298,0,4),(128,1,298,0,4),(264,0,163,0,4),(256,8,163,0,4),(2,0,425,0,4)])) (IndexTree.fork 5 (IndexTree.leaf [(32,0,395,0,4),(128,0,298,0,4),(0,128,296,3,4),(256,0,163,0,4),(0,256,131,40,4)]) (IndexTree.leaf [(0,3,264,160,3),(1,2,264,160,3),(2,1,296,128,3),(0,9,34,384,3),(1,8,162,256,3),(8,1,290,128,3)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(33,0,394,0,3),(1,128,296,2,3),(1,256,130,40,3),(10,0,417,0,3),(34,0,393,0,3)]) (IndexTree.leaf [(2,128,296,1,3),(2,256,129,40,3),(0,40,129,258,3),(8,32,129,258,3),(32,8,131,256,3)])) (IndexTree.fork 5 (IndexTree.leaf [(8,128,288,3,3),(8,256,131,32,3),(32,128,264,3,3),(32,256,131,8,3),(0,384,0,43,3)]) (IndexTree.leaf [(0,11,0,416,2),(1,10,0,416,2),(10,1,288,128,2),(32,3,264,128,2),(33,2,264,128,2),(34,1,264,128,2)])))) (IndexTree.fork 21 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(131,0,296,0,2),(3,128,296,0,2),(128,3,264,32,2),(129,2,264,32,2),(130,1,296,0,2)]) (IndexTree.leaf [(0,259,0,168,2),(1,258,0,168,2),(2,257,0,168,2),(0,41,0,386,2),(8,33,0,386,2)])) (IndexTree.fork 5 (IndexTree.leaf [(33,8,130,256,2),(137,0,290,0,2),(9,128,288,2,2),(128,9,34,256,2),(129,8,34,256,2)]) (IndexTree.leaf [(136,1,290,0,2),(265,0,162,0,2),(9,256,130,32,2),(256,9,34,128,2),(257,8,162,0,2),(264,1,34,128,2)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(33,128,264,2,2),(33,256,130,8,2),(1,384,0,42,2),(2,40,129,256,2),(10,32,129,256,2)]) (IndexTree.leaf [(34,8,129,256,2),(10,128,288,1,2),(10,256,129,32,2),(34,128,264,1,2),(34,256,129,8,2)])) (IndexTree.fork 5 (IndexTree.leaf [(2,384,0,41,2),(0,168,0,259,2),(8,160,0,259,2),(32,136,0,259,2),(296,0,131,0,2)]) (IndexTree.leaf [(40,256,131,0,2),(256,40,129,2,2),(264,32,129,2,2),(288,8,131,0,2),(8,384,0,35,2),(32,384,0,11,2)]))))) (IndexTree.fork 42 (IndexTree.fork 21 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(0,2,264,160,3),(0,32,129,258,3),(3,0,296,0,2),(0,33,0,386,2),(32,1,264,128,2)]) (IndexTree.leaf [(257,0,162,0,2),(0,257,0,168,2),(256,1,34,128,2),(0,10,0,416,2),(2,8,129,256,2)])) (IndexTree.fork 5 (IndexTree.leaf [(2,32,129,256,2),(32,2,264,128,2),(130,0,296,0,2),(128,2,264,32,2),(0,258,0,168,2)]) (IndexTree.leaf [(40,0,131,0,2),(136,0,290,0,2),(0,136,0,259,2),(128,8,34,256,2),(0,160,0,259,2),(288,0,131,0,2)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(256,32,129,2,2),(11,0,288,0,1),(2,9,0,384,1),(8,3,0,160,1),(9,2,0,160,1)]) (IndexTree.leaf [(35,0,264,0,1),(2,33,0,384,1),(3,256,0,40,1),(256,3,0,160,1),(257,2,0,160,1)])) (IndexTree.fork 5 (IndexTree.leaf [(41,0,130,0,1),(1,40,0,258,1),(9,32,0,258,1),(32,9,0,384,1),(1,136,0,258,1)]) (IndexTree.leaf [(8,257,0,160,1),(161,0,264,0,1),(1,160,0,258,1),(128,33,0,258,1),(129,32,0,258,1),(160,1,264,0,1)])))) (IndexTree.fork 21 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(289,0,130,0,1),(32,257,0,136,1),(256,33,0,130,1),(385,0,34,0,1),(128,257,0,40,1)]) (IndexTree.leaf [(129,256,0,40,1),(384,1,34,0,1),(42,0,129,0,1),(32,10,0,384,1),(138,0,288,0,1)])) (IndexTree.fork 5 (IndexTree.leaf [(2,136,0,257,1),(128,10,0,288,1),(266,0,129,0,1),(8,258,0,160,1),(256,10,0,160,1)]) (IndexTree.leaf [(258,8,129,0,1),(264,2,0,160,1),(162,0,264,0,1),(2,160,0,257,1),(160,2,264,0,1),(290,0,129,0,1)]))) (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(32,258,0,136,1),(258,32,129,0,1),(128,258,0,40,1),(130,256,0,40,1),(40,128,0,3,1)]) (IndexTree.leaf [(128,40,0,258,1),(136,32,0,258,1),(392,0,34,0,1),(256,136,0,3,1),(264,128,0,3,1),(384,8,34,0,1)])) (IndexTree.fork 5 (IndexTree.leaf [(256,160,0,3,1),(288,128,0,3,1),(1,32,0,258,1),(8,2,0,160,1),(258,0,129,0,1)]) (IndexTree.leaf [(256,2,0,160,1),(160,0,264,0,1),(128,32,0,258,1),(384,0,34,0,1),(128,256,0,40,1),(256,128,0,3,1)]))))))
def g427autos : Array (List Nat) := #[[],[135,81,48]]
def g427levels : Nat → Packing
  | 6 => g427l6
  | _ => emptyPacking
def g427index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g427 : Forest := ⟨427,6,fun j => g427samples[j]?.getD (0,0),g427columns,g427autos,g427levels,g427index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom427 : graphValid g427 (boundsBefore known55) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s427_6_0 : block g427 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all427_6 : block g427 6 0 1=true := s427_6_0
theorem tables427 : checkedTables g427 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g427 0 0 0 = true)
  · exact (rfl : block g427 1 0 0 = true)
  · exact (rfl : block g427 2 0 0 = true)
  · exact (rfl : block g427 3 0 0 = true)
  · exact (rfl : block g427 4 0 0 = true)
  · exact (rfl : block g427 5 0 0 = true)
  · exact all427_6

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low427 : Lower (vars 427) (graphGoal 427) 7 := lower_forest (g:=g427) (i:=0) (hints:=12885983319) (before_sound known55 valid55) geom427 tables427 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps427 : List (Nat × List Nat) := [(459,[101,131]),(427,[]),(442,[135,48,64,81,32]),(474,[101,131,64,32]),(462,[115,101,49,129,32])]
def known427 := extendKnown known55 7 maps427
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid427 : Known known427 := extendKnown_ok valid55 low427 (by decide +kernel)
def g119 : Forest := ⟨119,5,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 := lower_discard (g:=g119) (ci:=(0,1,102,16,5)) (hints:=17827156) (before_sound known427 valid427) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(489,[84,82,132,114,49]),(119,[]),(315,[129,113,97,49,33]),(476,[133,64,16,113,48]),(461,[133,116,49]),(349,[133,117,49]),(504,[82,64,16,130,113,48]),(377,[133,82,114,49]),(371,[134,98,114,50,81]),(347,[134,101,117,49,33]),(123,[101,50]),(470,[84,133,66,114,32,48]),(455,[84,133,116,32])]
def known119 := extendKnown known427 6 maps119
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid119 : Known known119 := extendKnown_ok valid427 low119 (by decide +kernel)
def g491d7 (i : Nat) : Nat := 0xc1000000038cee79950f28502ff1ce9077f8e7461bfa72230fdd20d187cf1090c7bb8c6842f5c424217ce18e10beb0c7043f9842821
def g491l7 : Packing := (10,2,9,0,0,6,0,g491d7)
def g491d8 (i : Nat) : Nat := 0x90bc2d80c80d4060c8e010881c18101640617902f0b603180c02c06179006804000b01f2c06180c301064f0470ad12264168781e00ff483ff4c2ff482ff462ff461ff441ff821f7863fb842fd821
def g491l8 : Packing := (10,1,9,4,1,9,0,g491d8)
def g491d9 (i : Nat) : Nat := 0x80301408032ff
def g491l9 : Packing := (1,0,9,4,1,0,0,g491d9)
def g491samples : Array (Bits × Bits) := #[(0x6735177f3193f6acaee7cb9b6acfdeecabccbee7bab5383fbacfd71a583fa1309dfd85ff33ac33e81ddf2dbbbf3a643ddc535b5f1aef9aa229c99dd2080802204040000070000004402c2c4008200020209884004a24c0d50c29cefc6674dcca,0x92d504944d409a00e84918cb034b023625e820978ad00344000cc8b71a049d09260046e4343300ca02805e75a8363be290e4d41c0d3513171da04183124b0c02100a01100c0e0087318693ce0c17edbeb28f57b62a24c0550c29ccec6634c888),(0xda2fa4fe0a42c7e56e7b7f6dc63e0fd95be827df7db3f7f7834d0d4ff5fd7ef56653ece87a9b68f7664fbf4745cf2b4ccebb3dbcb1bb8c3a7f1ff7bee2a0e447020875a888d5e152b6d38303f494a4c790613a38b933e81a8146f5c4af29021c,0x20208415040a04101b04d2001a02040a50048035084300000c0141a00a000340482a026d140182020000d00200212e20059088900921400210952002183e09028030140020400204440204080c1be028040202903c8020100d5c02021020c),(0x0,0x0),(0xdfd5cbe1f5ff55375c3bd9dfd3a4ab24743775de9ff9dbda9a987ef0ada7372a739774ba6cb4fb959ee3cdf69539bdcef19a617f8d24f6d7bbe443ed00560108b8b6805707020a890900503403405310440641c7048f9404bab598ea328f6641,0xc20043a0845030e110410545508d918201c10c1202640004d548901420500c2864c1a18046a4c4486adcb048046824160440442da1346842024801033d244340820030c00e2124800aa005000881e41d8cf00525040b0004a03490e8328c6641),(0x0,0x0),(0x363afcfcb65b4eeebf42166e3a5fcb67b9f23f6f6fcadf11e7fe6df8d7e7a14b10564b86afffaf3b3d727e4e2d3452fe6ffdd7defdfa112b6d7b963155211c9205097e00087c542006000088e01b0c4c0b2100103a4823f762de0c8d03484be5,0x7384e102008ba31100000582c10441990100680210a0018c9e52004b0558052a483069040800b22293403c724e41a0ac01028413624145c218ca52082414200102130002801c1a400b22285134272601bd76a555920822b522de080d034841c1),(0x5f9e41ca3dbeeff53885ffaef5b7e3bc6f3a33711bf6e4c87b39d7fb265aa986ad7f1ffe6924e3d4f0ac7b9997f072f7a549dab8cecf7c49e9f6ede98280e0008a160173058220499810531016c0e18050441943807c3ff0139b1822fcb0509a,0x30441c4512a3030eac260a90074206493a18e1a1d40022ca20a32e6b450201920000081b9008098684030b102b86c04809378240048a00a0490042a4421200106d108030a140911484082082311e1a40710fbadad07437f0128b0802cc101092),(0xe3d2bb8f6ab17416effda9c1065434f255bfdfec53aecbaeefafb8e71e345fdd98b9a257fef9d5657a0703d4ff5fcbffe6bfcddf42254b169eda2ad72808026540400088f001811660efac4308240023a098a62841917789a4d4e31948d4b4e2,0x650089230006014e00104500d83408891010132074030889d1530340c068405488902003400416014d1500025041c40d0508024242c22828a246b60080805009698124c81270436880000c10004812414d70a849d0903788a0d4221108c03462),(0x65c76e22f2273f7f338874396d6b5b97ef11c6469ecba7f845f421fcb298d56afbad3b5ff752afda91f49fbe46d4d41616debbcfe9d1f3e69edae1d91557199835a18a0402281ea0010000ac010b1a180f0240840fe693646d28624388333925,0xc7b180c21200008ac9a28100e220824300083e1e5093232208506a042a2828482060031004b01040000400581044341023d0a40088a0014e430a014008880a204e480293180c0201441900cc04819e242095a8a69e491404d00620288331824)]
def g491columns : IndexTree ColumnInfo := (IndexTree.fork 137 (IndexTree.fork 68 (IndexTree.fork 34 (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(1,0,490,0,8),(0,1,362,128,8),(129,0,362,0,7),(128,1,362,0,7),(8,0,483,0,7),(32,0,459,0,7),(64,0,427,0,7),(128,0,362,0,7)]) (IndexTree.fork 4 (IndexTree.leaf [(256,0,235,0,7),(2,0,489,0,6),(0,8,163,320,6),(0,128,360,3,6)]) (IndexTree.leaf [(0,256,195,40,6),(2,1,360,128,5),(9,0,482,0,5),(8,1,354,128,5),(33,0,458,0,5)]))) (IndexTree.fork 8 (IndexTree.leaf [(32,1,330,128,5),(65,0,426,0,5),(64,1,298,128,5),(1,128,360,2,5),(257,0,234,0,5),(256,1,106,128,5),(2,128,360,1,5),(72,0,419,0,5)]) (IndexTree.fork 4 (IndexTree.leaf [(64,8,163,256,5),(264,0,227,0,5),(8,256,195,32,5),(256,8,163,64,5)]) (IndexTree.leaf [(288,0,203,0,5),(32,256,195,8,5),(131,0,360,0,4),(3,128,360,0,4),(130,1,360,0,4)])))) (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(73,0,418,0,4),(137,0,354,0,4),(136,1,354,0,4),(161,0,330,0,4),(160,1,330,0,4),(289,0,202,0,4),(193,0,298,0,4),(192,1,298,0,4)]) (IndexTree.fork 4 (IndexTree.leaf [(385,0,106,0,4),(384,1,106,0,4),(296,0,195,0,4),(40,256,195,0,4)]) (IndexTree.leaf [(328,0,163,0,4),(320,8,163,0,4),(0,32,201,258,5),(0,64,417,10,5),(3,0,360,0,4)]))) (IndexTree.fork 8 (IndexTree.leaf [(0,3,264,224,4),(1,2,264,224,4),(0,9,34,448,4),(1,8,162,320,4),(0,33,72,386,4),(0,65,288,138,4),(0,257,66,168,4),(1,256,194,40,4)]) (IndexTree.fork 4 (IndexTree.leaf [(34,0,457,0,4),(2,32,201,256,4),(66,0,425,0,4),(2,64,417,8,4)]) (IndexTree.leaf [(130,0,360,0,4),(40,0,195,0,4),(0,40,129,322,4),(32,8,131,320,4),(8,64,417,2,4)]))))) (IndexTree.fork 34 (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(136,0,354,0,4),(96,0,395,0,4),(0,96,129,266,4),(160,0,330,0,4),(0,160,72,259,4),(32,128,328,3,4),(256,32,201,2,4),(192,0,298,0,4)]) (IndexTree.fork 4 (IndexTree.leaf [(0,192,288,11,4),(64,128,296,3,4),(320,0,163,0,4),(0,320,129,42,4)]) (IndexTree.leaf [(64,256,131,40,4),(384,0,106,0,4),(0,11,0,480,3),(1,10,0,480,3),(2,33,72,384,3)]))) (IndexTree.fork 8 (IndexTree.leaf [(32,3,264,192,3),(33,2,264,192,3),(34,1,328,128,3),(2,65,288,136,3),(64,3,264,160,3),(65,2,264,160,3),(66,1,296,128,3),(128,3,264,96,3)]) (IndexTree.fork 4 (IndexTree.leaf [(129,2,264,96,3),(0,259,0,232,3),(1,258,0,232,3),(0,41,0,450,3)]) (IndexTree.leaf [(33,8,130,320,3),(8,65,288,130,3),(64,9,34,384,3),(65,8,162,256,3),(72,1,290,128,3)])))) (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(128,9,34,320,3),(129,8,34,320,3),(265,0,226,0,3),(8,257,66,160,3),(9,256,194,32,3),(256,9,34,192,3),(257,8,162,64,3),(264,1,98,128,3)]) (IndexTree.fork 4 (IndexTree.leaf [(97,0,394,0,3),(0,97,0,394,3),(1,160,72,258,3),(33,128,328,2,3)]) (IndexTree.leaf [(128,33,72,258,3),(129,32,72,258,3),(32,257,66,136,3),(33,256,194,8,3),(256,33,72,130,3)]))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(288,1,74,128,3),(1,192,288,10,3),(65,128,296,2,3),(128,65,288,10,3)]) (IndexTree.leaf [(129,64,288,10,3),(0,321,0,170,3),(65,256,130,40,3),(128,257,66,40,3),(129,256,66,40,3)])) (IndexTree.fork 4 (IndexTree.leaf [(2,40,129,320,3),(34,8,129,320,3),(74,0,417,0,3),(10,64,417,0,3)]) (IndexTree.leaf [(98,0,393,0,3),(2,96,129,264,3),(2,160,72,257,3),(34,128,328,1,3),(290,0,201,0,3)])))))) (IndexTree.fork 68 (IndexTree.fork 34 (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(258,32,201,0,3),(2,192,288,9,3),(66,128,296,1,3),(2,320,129,40,3),(66,256,129,40,3),(8,96,129,258,3),(64,40,129,258,3),(72,32,129,258,3)]) (IndexTree.fork 4 (IndexTree.leaf [(96,8,131,256,3),(0,168,0,323,3),(32,136,0,323,3),(256,40,129,66,3)]) (IndexTree.leaf [(288,8,131,64,3),(8,192,288,3,3),(72,128,288,3,3),(8,320,129,34,3),(72,256,131,32,3)]))) (IndexTree.fork 8 (IndexTree.leaf [(0,224,0,267,3),(96,128,264,3,3),(32,320,129,10,3),(96,256,131,8,3),(256,96,129,10,3),(288,64,129,10,3),(256,160,72,3,3),(288,128,72,3,3)]) (IndexTree.fork 4 (IndexTree.leaf [(0,448,0,43,3),(64,384,0,43,3),(0,2,264,224,4),(1,32,72,258,3)]) (IndexTree.leaf [(1,64,288,10,3),(10,0,417,0,3),(0,10,0,480,3),(2,8,129,320,3),(32,2,264,192,3)])))) (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(64,2,264,160,3),(128,2,264,96,3),(258,0,201,0,3),(0,258,0,232,3),(2,256,129,40,3),(8,32,129,258,3),(0,136,0,323,3),(8,128,288,3,3)]) (IndexTree.fork 4 (IndexTree.leaf [(128,8,34,320,3),(32,64,129,10,3),(64,32,129,258,3),(128,32,72,258,3)]) (IndexTree.leaf [(128,64,288,10,3),(256,64,129,10,3),(0,384,0,43,3),(128,256,66,40,3),(256,128,72,3,3)]))) (IndexTree.fork 8 (IndexTree.leaf [(2,9,0,448,2),(8,3,0,224,2),(9,2,0,224,2),(10,1,288,128,2),(35,0,328,0,2),(3,32,72,256,2),(67,0,296,0,2),(3,64,288,8,2)]) (IndexTree.fork 4 (IndexTree.leaf [(2,257,0,168,2),(256,3,0,224,2),(257,2,0,224,2),(258,1,72,128,2)]) (IndexTree.leaf [(41,0,194,0,2),(1,40,0,322,2),(8,33,0,386,2),(32,9,0,448,2),(40,1,66,128,2)]))))) (IndexTree.fork 34 (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(9,64,288,2,2),(1,136,0,322,2),(9,128,288,2,2),(1,96,0,266,2),(32,65,0,138,2),(64,33,0,386,2),(96,1,264,128,2),(257,32,72,2,2)]) (IndexTree.fork 4 (IndexTree.leaf [(321,0,162,0,2),(1,320,0,42,2),(64,257,0,168,2),(256,65,0,138,2)]) (IndexTree.leaf [(320,1,34,128,2),(1,384,0,42,2),(257,128,72,2,2),(10,32,129,256,2),(32,10,0,448,2)]))) (IndexTree.fork 8 (IndexTree.leaf [(64,10,0,416,2),(66,8,129,256,2),(2,136,0,321,2),(10,128,288,1,2),(128,10,0,352,2),(8,258,0,224,2),(10,256,129,32,2),(256,10,0,224,2)]) (IndexTree.fork 4 (IndexTree.leaf [(258,8,129,64,2),(264,2,0,224,2),(34,64,129,8,2),(66,32,129,256,2)]) (IndexTree.leaf [(96,2,264,128,2),(162,0,328,0,2),(130,32,72,256,2),(160,2,264,64,2),(32,258,0,200,2)])))) (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(34,256,129,8,2),(194,0,296,0,2),(130,64,288,8,2),(192,2,264,32,2),(64,258,0,168,2),(258,64,129,8,2),(2,384,0,41,2),(128,258,0,104,2)]) (IndexTree.fork 4 (IndexTree.leaf [(258,128,72,1,2),(104,0,131,0,2),(40,64,129,2,2),(8,160,0,259,2)]) (IndexTree.leaf [(128,40,0,322,2),(264,32,129,2,2),(200,0,290,0,2),(64,136,0,259,2),(136,64,288,2,2)]))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(192,8,34,256,2),(264,64,129,2,2),(392,0,98,0,2),(8,384,0,35,2)]) (IndexTree.leaf [(136,256,66,32,2),(256,136,0,67,2),(384,8,34,64,2),(32,192,0,11,2),(64,160,0,259,2)])) (IndexTree.fork 4 (IndexTree.leaf [(128,96,0,266,2),(352,0,131,0,2),(320,32,129,2,2),(416,0,74,0,2)]) (IndexTree.leaf [(32,384,0,11,2),(160,256,66,8,2),(384,32,72,2,2),(128,320,0,42,2),(256,192,0,11,2)])))))))
def g491autos : Array (List Nat) := #[[],[101,131]]
def g491levels : Nat → Packing
  | 7 => g491l7
  | 8 => g491l8
  | 9 => g491l9
  | _ => emptyPacking
def hashg491l8 (i : Nat) : Nat := 0xd4224000000000016058d1404846b09c0000330012761f850fc3
def hashg491l9 (i : Nat) : Nat := 0x4e8e8c002900001e5d080000005b2880064006830e5408bdd10b5001309
def g491index : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 5 22 2 9 4 1 (hashg491l8)
  | 9 => lookupWord 6 24 4 9 4 1 (hashg491l9)
  | _ => fun _ => none
def g491 : Forest := ⟨491,9,fun j => g491samples[j]?.getD (0,0),g491columns,g491autos,g491levels,g491index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom491 : graphValid g491 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=7) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s491_7_0 : block g491 7 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s491_7_6 : block g491 7 6 4=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all491_7 : block g491 7 0 10=true := (@block_merge g491 7 0 6 4 s491_7_0 s491_7_6)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s491_8_0 : block g491 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s491_8_3 : block g491 8 3 7=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all491_8 : block g491 8 0 10=true := (@block_merge g491 8 0 3 7 s491_8_0 s491_8_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s491_9_0 : block g491 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all491_9 : block g491 9 0 1=true := s491_9_0
theorem tables491 : checkedTables g491 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g491 0 0 0 = true)
  · exact (rfl : block g491 1 0 0 = true)
  · exact (rfl : block g491 2 0 0 = true)
  · exact (rfl : block g491 3 0 0 = true)
  · exact (rfl : block g491 4 0 0 = true)
  · exact (rfl : block g491 5 0 0 = true)
  · exact (rfl : block g491 6 0 0 = true)
  · exact all491_7
  · exact all491_8
  · exact all491_9

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low491 : Lower (vars 491) (graphGoal 491) 10 := lower_forest (g:=g491) (i:=0) (hints:=12902752343) (before_sound known119 valid119) geom491 tables491 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps491 : List (Nat × List Nat) := [(506,[64,32]),(491,[])]
def known491 := extendKnown known119 10 maps491
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid491 : Known known491 := extendKnown_ok valid119 low491 (by decide +kernel)
def g145d3 (i : Nat) : Nat := 0x7
def g145l3 : Packing := (1,0,3,0,0,0,0,g145d3)
def g145samples : Array (Bits × Bits) := #[(0xfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6dfd6d,0x408940894089408940894089408940894089408940894089408940894089408940894089408940894089408940894089408940894089408940894089408940894089408940894089408940894089408940894089408940894089408940894089),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xfadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefadefade,0x811481148114811481148114811481148114811481148114811481148114811481148114811481148114811481148114811481148114811481148114811481148114811481148114811481148114811481148114811481148114811481148114),(0x0,0x0),(0x0,0x0),(0xf7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3f7b3,0x206220622062206220622062206220622062206220622062206220622062206220622062206220622062206220622062206220622062206220622062206220622062206220622062206220622062206220622062206220622062206220622062),(0x0,0x0)]
def g145columns : IndexTree ColumnInfo := (IndexTree.leaf [(1,0,144,0,1),(0,1,0,144,1),(16,0,129,0,1),(0,16,0,129,1),(128,0,17,0,1),(0,128,0,17,1)])
def g145autos : Array (List Nat) := #[[],[116],[64],[112,64],[64,112],[112]]
def g145levels : Nat → Packing
  | 3 => g145l3
  | _ => emptyPacking
def g145index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g145 : Forest := ⟨145,3,fun j => g145samples[j]?.getD (0,0),g145columns,g145autos,g145levels,g145index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom145 : graphValid g145 (boundsBefore known491) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s145_3_0 : block g145 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all145_3 : block g145 3 0 1=true := s145_3_0
theorem tables145 : checkedTables g145 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g145 0 0 0 = true)
  · exact (rfl : block g145 1 0 0 = true)
  · exact (rfl : block g145 2 0 0 = true)
  · exact all145_3

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low145 : Lower (vars 145) (graphGoal 145) 4 := lower_forest (g:=g145) (i:=0) (hints:=4) (before_sound known491 valid491) geom145 tables145 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps145 : List (Nat × List Nat) := [(145,[]),(292,[135,84,32,16])]
def known145 := extendKnown known491 4 maps145
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid145 : Known known145 := extendKnown_ok valid491 low145 (by decide +kernel)
def g147 : Forest := ⟨147,4,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low147 : Lower (vars 147) (graphGoal 147) 5 := lower_discard (g:=g147) (ci:=(2,0,145,0,4)) (hints:=116) (before_sound known145 valid145) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps147 : List (Nat × List Nat) := [(147,[]),(294,[132,116,84,32]),(300,[135,84,49,32])]
def known147 := extendKnown known145 5 maps147
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid147 : Known known147 := extendKnown_ok valid145 low147 (by decide +kernel)
def g179d5 (i : Nat) : Nat := 0x10608204002001d2768d03f884fd203f440be213e800
def g179l5 : Packing := (5,1,7,0,0,6,0,g179d5)
def g179d6 (i : Nat) : Nat := 0x6080c7f
def g179l6 : Packing := (1,0,7,3,1,0,0,g179d6)
def g179samples : Array (Bits × Bits) := #[(0xbec502ad09ca3f7840d896f6fafafbc6f43eebddfbd9dff6fe6fea86d77d8a055a13947ef081b12dedf5f5f78de87dd7bbf7b3bfedfcdfd50daefb140ab42728fde103625bdbebebef1bd0fbaf77ef677fdbf9bfaa1b5df62815684e51fbc206,0x18082a909c6a3040ce908b801ce980029010960086230871002200a0003010552138d460819d21170039d3000520212c010c4610e200440140006020aa4271a8c1033a422e0073a6000a40425802188c21c40088028000c0415484e3518206),(0xf92879523614ba95b23fcb1d63ddf478ff9bf5653fa7d1f37ffbbfebb1f250f2a46c29752b647f963ac7bbe8f1ff37eaca7f4fa3e6fff77fd763e4a1e548d852ea56c8ff2c758f77d1e3fe6fd594fe9f47cdffeeffaec7c943ca91b0a5d4ad91,0x884044ec20e3a8500312003010143614800005ec10e460209436203401108089d841c750a00624006020286c2900000bd821c8c041286c406802210113b0838ea1400c4800c04050d852000017b04391808250d880d00442022761071d42801),(0x0,0x0),(0x0,0x0),(0xb493862dc0615d260faff7f9ecebe59b2acdddffb57b6f4f9d86dff3df69270c5b80c2ba4c1f5feff3d9d7cb36559bbbff6af6de9f3b0dbfe7bed24e18b7018574983ebfdfe7b3af966cab3777fed5edbd3e761b7fcf7da49c316e030ae9307d,0xc80050c54722950606206800610012166808c2400a38043280cc48420b9000a18a8e452a0c0c40d000c200242cd0118480147008650198908417200143151c8a54181881a00184004859a023090028e010ca033121082e4002862a3914a83031),(0x7828305004142173d32a3d6bffdf4bf7ddf9337e7dfc79b991397c7f7cf05060a0082842e7a6547ad7ffbe97efbbf266fcfbf8f3732272f8fef9e0a0c140105085cf4ca8f5afff7d2fdf77e4cdf9f7f1e6e644e5f1fdf3c141828020a10b9e99,0xe70200313df1c172d30810c83416340016836a013c11181d56808d4897ce0400627be382e5a6102190682c68002d06d4027822303aad011a912f9c0800c4f7c705cb4c204320d058d0005a0da804f04460755a0235225f38100189ef8e0b9698),(0x0,0x0),(0xe356cd82fbabc2ce7d5d7abe17f7feafeb6f3ebacbf7bf2f6bd5fb5e3bc6ad9b05f757859cfabaf57c2feffd5fd6de7d7597ef7e5ed7abf6bc778d5b360beeaf0b39f575eaf85fdffabfadbcfaeb2fdefcbdaf57ed78ef1ab66c17dd5e1673ea,0x1001201028410048390006040060040091412401144008c40200902414200240205082009072000c0800c008012282480228801188040120482840048040a1040120e400181001801002450490045100231008024090508009008142080241c8),(0x0,0x0)]
def g179columns : IndexTree ColumnInfo := (IndexTree.fork 38 (IndexTree.fork 19 (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(32,0,147,0,5),(0,32,145,2,5),(34,0,145,0,4),(2,32,145,0,4)]) (IndexTree.leaf [(1,0,178,0,4),(2,0,145,0,4),(16,0,163,0,4),(0,1,34,144,3),(0,2,17,160,3)])) (IndexTree.fork 5 (IndexTree.leaf [(0,16,34,129,3),(128,0,51,0,3),(0,3,0,176,2),(17,0,162,0,2),(1,16,34,128,2)]) (IndexTree.leaf [(16,1,34,128,2),(33,0,146,0,2),(0,33,0,146,2),(1,32,144,2,2),(128,1,34,16,2)]))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(0,18,0,161,2),(32,2,17,128,2),(128,2,17,32,2),(48,0,131,0,2)]) (IndexTree.leaf [(0,48,0,131,2),(16,32,129,2,2),(128,16,34,1,2),(0,160,0,19,2),(32,128,0,19,2)])) (IndexTree.fork 5 (IndexTree.leaf [(128,32,17,2,2),(1,18,0,160,1),(16,3,0,160,1),(17,2,0,160,1),(35,0,144,0,1)]) (IndexTree.leaf [(2,33,0,144,1),(3,32,144,0,1),(32,3,0,144,1),(34,1,0,144,1),(128,3,0,48,1)])))) (IndexTree.fork 19 (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(49,0,130,0,1),(1,48,0,130,1),(16,33,0,130,1),(145,0,34,0,1)]) (IndexTree.leaf [(129,16,34,0,1),(144,1,34,0,1),(1,160,0,18,1),(33,128,0,18,1),(128,33,0,18,1)])) (IndexTree.fork 5 (IndexTree.leaf [(50,0,129,0,1),(2,48,0,129,1),(18,32,129,0,1),(32,18,0,129,1),(34,16,0,129,1)]) (IndexTree.leaf [(128,18,0,33,1),(162,0,17,0,1),(2,160,0,17,1),(34,128,0,17,1),(130,32,17,0,1)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(160,2,17,0,1),(16,160,0,3,1),(48,128,0,3,1),(128,48,0,3,1),(0,128,0,19,2)]) (IndexTree.leaf [(3,0,144,0,1),(1,2,0,160,1),(2,1,0,144,1),(32,1,0,144,1),(129,0,34,0,1)])) (IndexTree.fork 5 (IndexTree.leaf [(1,128,0,18,1),(18,0,129,0,1),(2,16,0,129,1),(16,2,0,160,1),(130,0,17,0,1)]) (IndexTree.leaf [(2,128,0,17,1),(32,16,0,129,1),(144,0,34,0,1),(16,128,0,3,1),(160,0,17,0,1)])))))
def g179autos : Array (List Nat) := #[[],[64]]
def g179levels : Nat → Packing
  | 5 => g179l5
  | 6 => g179l6
  | _ => emptyPacking
def hashg179l6 (i : Nat) : Nat := 0x684a40d5b98000640000012
def g179index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 3 11 1 8 3 1 (hashg179l6)
  | _ => fun _ => none
def g179 : Forest := ⟨179,6,fun j => g179samples[j]?.getD (0,0),g179columns,g179autos,g179levels,g179index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom179 : graphValid g179 (boundsBefore known147) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s179_5_0 : block g179 5 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s179_5_2 : block g179 5 2 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all179_5 : block g179 5 0 5=true := (@block_merge g179 5 0 2 3 s179_5_0 s179_5_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s179_6_0 : block g179 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all179_6 : block g179 6 0 1=true := s179_6_0
theorem tables179 : checkedTables g179 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g179 0 0 0 = true)
  · exact (rfl : block g179 1 0 0 = true)
  · exact (rfl : block g179 2 0 0 = true)
  · exact (rfl : block g179 3 0 0 = true)
  · exact (rfl : block g179 4 0 0 = true)
  · exact all179_5
  · exact all179_6

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low179 : Lower (vars 179) (graphGoal 179) 7 := lower_forest (g:=g179) (i:=0) (hints:=1048660) (before_sound known147 valid147) geom179 tables179 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps179 : List (Nat × List Nat) := [(211,[101]),(179,[]),(422,[132,117,100,32]),(358,[132,84,117,100,32]),(364,[135,84,100,49,32])]
def known179 := extendKnown known147 7 maps179
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid179 : Known known179 := extendKnown_ok valid147 low179 (by decide +kernel)
def g243 : Forest := ⟨243,7,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low243 : Lower (vars 243) (graphGoal 243) 8 := lower_discard (g:=g243) (ci:=(32,0,211,0,7)) (hints:=17825876) (before_sound known179 valid179) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps243 : List (Nat × List Nat) := [(243,[]),(486,[101,117,132,32])]
def known243 := extendKnown known179 8 maps243
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid243 : Known known243 := extendKnown_ok valid179 low243 (by decide +kernel)
def g183 : Forest := ⟨183,7,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low183 : Lower (vars 183) (graphGoal 183) 8 := lower_discard (g:=g183) (ci:=(4,0,179,0,7)) (hints:=1049940) (before_sound known243 valid243) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps183 : List (Nat × List Nat) := [(183,[]),(435,[130,98,50]),(219,[101,50]),(438,[132,117,66,98,32,48]),(423,[132,117,100,32])]
def known183 := extendKnown known243 8 maps183
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid183 : Known known183 := extendKnown_ok valid243 low183 (by decide +kernel)
def g181 : Forest := ⟨181,5,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low181 : Lower (vars 181) (graphGoal 181) 6 := lower_discard (g:=g181) (ci:=(0,4,145,32,5)) (hints:=2098436) (before_sound known183 valid183) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps181 : List (Nat × List Nat) := [(181,[]),(409,[133,101,50]),(433,[133,82,98,50]),(217,[101,50]),(405,[133,101]),(436,[117,133,84,66,98,32,48,16]),(421,[117,133,84,100,32]),(309,[135,84,32])]
def known181 := extendKnown known183 6 maps181
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid181 : Known known181 := extendKnown_ok valid183 low181 (by decide +kernel)
def g247d7 (i : Nat) : Nat := 0x2428002004000801a48fb450a05fe39d3073f18c98bbd8c6821df463400779316003ed0c7001fc821800
def g247l7 : Packing := (7,2,9,0,0,6,0,g247d7)
def g247d8 (i : Nat) : Nat := 0xa80a040d081b06b0282440280780a040d8a0d00d014081a140004c361c05020a000d0121c00090a0281052c7fb21226e2a8c83200ff8c6ff4c1ff4c0ff460ff420bf8c6df4c5fd821fe800
def g247l8 : Packing := (9,1,9,3,1,9,0,g247d8)
def g247d9 (i : Nat) : Nat := 0xa0381804042ff
def g247l9 : Packing := (1,0,9,4,1,0,0,g247d9)
def g247samples : Array (Bits × Bits) := #[(0xd25088415eee3b28ef75c57e9fdb1ce7cfd3ebebee99749f0ed2a2fb49f7ceafffd556e54f0b35dd33b9ff77967efbf1aaec736cfde65dfca673b6ed8910af51062003010404a892b200318c8440408c0bf084980a7a596fbe01ca8802cb74a0,0x16e668020920222175148068400011621c4081204a02024e8092c4406e80a442204040641e0004c316d408c48428c808c1a50044221010fc41a481001c58002281012841a80b4010034100708c2002992876788725849633801c80802ca6480),(0x5806e3e572fc41a4a07295063e95e2e8507e7417fef6bd7a77f79a56e799ba73937c892fd6fbc376eb3d799e594fad6946fa38bebfdb5f1f6fff7f227003408aa89fb82ec8bb516941f9cc42328f1233c40a3b2492cda2c6344f645465242d8a,0xa240400800320120082ac80c92a10292015388840b00401c940105108212024405210220046008400020c080d0000108018d640810012082183120503300b04c0230209008240001000020210300070143016294024c82060409401445000d88),(0x1eeb5d2f314adf8fa62d33ffae9fa7324fed9c29b3f79ae7f038cdbb751387be6ceab5eee8ec5db08d7389477cfbf6d7bd9be62fb7d06149ef6d36ff00e0102010400050230000000c06001101200c00200100036df8471440f24107a79a7be4,0xa325725a23d6672454ac0c48800572b8c8b360b423012b1e7c11b45c20d66645430530c4851b392b3080a132b02808440495a490466096805a8b6900d85560348203200180503386081b420093438f974797eed6bcf8471440624006a51a7be0),(0x0,0x0),(0xe3acba7ebd81acff3cf6787fd72712307a813fafd1c874e21d5770fff9246795ff5ec93c14f1affe70087bf186f4eb275e4d7cbbdff7f9d77ee6bbf5071c0b144320448010408684220023accc50a1441b44c4480243400d47e8bcacd8189b7d,0xb600002e0d21858428a8004818a104a0000082845902cd120542408190034030842101080e018c00041210301301111c7004804900c802201a8111a822080048048e841061320a8238402d0010217786690800768003000c46e824a4d010993c),(0xa45f572f9d5f011f1588a7c6ce69f73be894a987656ccb75b83e15e1bbbed939daa67f47e9fc00ac9fd6b3bf3ca51f2e89438f579f1bdf16b2b0da6f00e0102038551858a33800080d970c11032b0c002401212765190e51db940ff3caa4c504,0x4c0805015c0018d38000133320588d041604130a841c84e003ce002159089108a80889007284c01407040c440c97d282024003662182490080440600040a060048404a241583001050c48994240c7068b8681129410108419b940fe10aa48004),(0x331fbd947aa3e5f4416c2ba0e9bdce8f7b6e33fef6d1811940e9fd71ca48e35692ddf395a607e7bb2ff254a8136c2bc925b3d020ddb861eb4eb4b5684000400800882000008311614020004230001223000218000530e1a83b777e4eb481b20c,0x4db18752794092d0a6901592254ae809868c404b20dbaea3233e82e66c6cad11100e010d589c34831e1613392d3606d3907093a64b288941c04e41a480104e831184d52202088824258b101a283ff8febcfe9d6bf53061a83b763e4ab081b204),(0x3dbfa9938c7dded6dbcf78ab52654fe5adc1f7f37dab87bbef0ef306ff71fac5fdaf579cff249ad1e09747aef7b24abffaad61e1655db2a8ddaf7599be0fa4c7c502c7a75c446e169048d2204894e1d8d0bc42d098a41da2893e122319578ad3,0x9009111044284000002320411e700846001421a048024102a4802a6000210a00c2e000901a03308280230200bc000302600110890004500144020704220131904108030041017801000008041c88500470980108a014808116120308050243),(0x0,0x0)]
def g247columns : IndexTree ColumnInfo := (IndexTree.fork 136 (IndexTree.fork 68 (IndexTree.fork 34 (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(4,0,243,0,8),(0,4,211,32,8),(64,0,183,0,8),(36,0,211,0,7),(32,4,211,0,7),(68,0,179,0,7),(1,0,246,0,7),(16,0,231,0,7)]) (IndexTree.fork 4 (IndexTree.leaf [(32,0,211,0,7),(0,64,181,2,7),(66,0,181,0,6),(2,64,181,0,6)]) (IndexTree.leaf [(0,68,145,34,6),(64,4,147,32,6),(0,96,145,6,6),(64,32,145,6,6),(2,68,145,32,5)]))) (IndexTree.fork 8 (IndexTree.leaf [(66,4,145,32,5),(2,96,145,4,5),(66,32,145,4,5),(100,0,147,0,5),(4,96,145,2,5),(32,68,145,2,5),(36,64,145,2,5),(68,32,145,2,5)]) (IndexTree.fork 4 (IndexTree.leaf [(96,4,147,0,5),(0,1,102,144,6),(2,0,181,0,6),(0,16,102,129,6)]) (IndexTree.leaf [(0,32,145,6,6),(128,0,119,0,6),(5,0,242,0,5),(1,4,210,32,5),(17,0,230,0,5)])))) (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(1,16,102,128,5),(16,1,102,128,5),(65,0,182,0,5),(128,1,102,16,5),(2,4,145,32,5),(2,32,145,4,5),(20,0,227,0,5),(16,4,195,32,5)]) (IndexTree.fork 4 (IndexTree.leaf [(4,32,145,2,5),(4,64,145,2,5),(80,0,167,0,5),(128,16,102,1,5)]) (IndexTree.leaf [(96,0,147,0,5),(32,64,145,2,5),(37,0,210,0,4),(33,4,210,0,4),(69,0,178,0,4)]))) (IndexTree.fork 8 (IndexTree.leaf [(81,0,166,0,4),(145,0,102,0,4),(129,16,102,0,4),(144,1,102,0,4),(38,0,145,0,4),(6,32,145,0,4),(34,4,145,0,4),(70,0,145,0,4)]) (IndexTree.fork 4 (IndexTree.leaf [(6,64,145,0,4),(98,0,145,0,4),(34,64,145,0,4),(52,0,195,0,4)]) (IndexTree.leaf [(48,4,195,0,4),(84,0,163,0,4),(0,5,66,176,4),(4,1,98,144,4),(33,0,210,0,4)]))))) (IndexTree.fork 34 (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(0,65,36,146,4),(1,64,180,2,4),(64,1,38,144,4),(129,0,102,0,4),(6,0,145,0,4),(0,6,17,224,4),(4,2,17,224,4),(34,0,145,0,4)]) (IndexTree.fork 4 (IndexTree.leaf [(0,20,66,161,4),(4,16,98,129,4),(132,0,115,0,4),(128,4,83,32,4)]) (IndexTree.leaf [(48,0,195,0,4),(0,80,36,131,4),(16,64,165,2,4),(64,16,38,129,4),(144,0,102,0,4)]))) (IndexTree.fork 8 (IndexTree.leaf [(192,0,55,0,4),(0,192,36,19,4),(64,128,36,19,4),(128,64,53,2,4),(0,7,0,240,3),(4,3,0,240,3),(67,0,180,0,3),(2,65,36,144,3)]) (IndexTree.fork 4 (IndexTree.leaf [(3,64,180,0,3),(66,1,36,144,3),(21,0,226,0,3),(1,20,66,160,3)]) (IndexTree.leaf [(5,16,98,128,3),(16,5,66,160,3),(17,4,194,32,3),(20,1,98,128,3),(32,5,66,144,3)])))) (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(36,1,66,144,3),(0,69,0,178,3),(1,68,144,34,3),(65,4,146,32,3),(68,1,34,144,3),(128,5,66,48,3),(132,1,98,16,3),(1,80,36,130,3)]) (IndexTree.fork 4 (IndexTree.leaf [(16,65,36,130,3),(65,16,38,128,3),(80,1,38,128,3),(0,97,0,150,3)]) (IndexTree.leaf [(1,96,144,6,3),(64,33,0,150,3),(65,32,144,6,3),(1,192,36,18,3),(65,128,36,18,3)]))) (IndexTree.fork 8 (IndexTree.leaf [(128,65,36,18,3),(192,1,38,16,3),(0,22,0,225,3),(4,18,0,225,3),(32,6,17,192,3),(36,2,17,192,3),(64,6,17,160,3),(68,2,17,160,3)]) (IndexTree.fork 4 (IndexTree.leaf [(128,6,17,96,3),(132,2,17,96,3),(82,0,165,0,3),(2,80,36,129,3)]) (IndexTree.leaf [(18,64,165,0,3),(66,16,36,129,3),(194,0,53,0,3),(2,192,36,17,3),(66,128,36,17,3)])))))) (IndexTree.fork 68 (IndexTree.fork 34 (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(130,64,53,0,3),(32,20,66,129,3),(36,16,66,129,3),(0,84,0,163,3),(16,68,129,34,3),(68,16,34,129,3),(80,4,131,32,3),(128,20,66,33,3)]) (IndexTree.fork 4 (IndexTree.leaf [(132,16,98,1,3),(164,0,83,0,3),(160,4,83,0,3),(196,0,51,0,3)]) (IndexTree.leaf [(0,196,0,51,3),(64,132,0,51,3),(128,68,17,34,3),(0,112,0,135,3),(16,96,129,6,3)]))) (IndexTree.fork 8 (IndexTree.leaf [(64,48,0,135,3),(80,32,129,6,3),(16,192,36,3,3),(80,128,36,3,3),(128,80,36,3,3),(192,16,38,1,3),(0,224,0,23,3),(64,160,0,23,3)]) (IndexTree.fork 4 (IndexTree.leaf [(128,96,17,6,3),(192,32,17,6,3),(0,2,17,224,4),(0,128,36,19,4)]) (IndexTree.leaf [(3,0,180,0,3),(0,3,0,240,3),(2,1,36,144,3),(0,33,0,150,3),(1,32,144,6,3)])))) (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(32,1,66,144,3),(1,128,36,18,3),(18,0,165,0,3),(0,18,0,225,3),(2,16,36,129,3),(32,2,17,192,3),(64,2,17,160,3),(130,0,53,0,3)]) (IndexTree.fork 4 (IndexTree.leaf [(2,128,36,17,3),(128,2,17,96,3),(0,132,0,51,3),(0,48,0,135,3)]) (IndexTree.leaf [(16,32,129,6,3),(32,16,66,129,3),(16,128,36,3,3),(160,0,83,0,3),(0,160,0,23,3)]))) (IndexTree.fork 8 (IndexTree.leaf [(128,32,17,6,3),(1,6,0,224,2),(2,5,0,176,2),(3,4,144,32,2),(5,2,0,224,2),(1,18,0,224,2),(3,16,36,128,2),(16,3,0,224,2)]) (IndexTree.fork 4 (IndexTree.leaf [(17,2,0,224,2),(18,1,36,128,2),(2,33,0,148,2),(3,32,144,4,2)]) (IndexTree.leaf [(32,3,0,208,2),(64,3,0,176,2),(3,128,36,16,2),(128,3,0,112,2),(130,1,36,16,2)]))))) (IndexTree.fork 34 (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(4,33,0,146,2),(5,32,144,2,2),(4,65,0,146,2),(5,64,144,2,2),(64,5,0,176,2),(133,0,98,0,2),(1,132,0,50,2),(129,4,66,32,2)]) (IndexTree.fork 4 (IndexTree.leaf [(49,0,194,0,2),(1,48,0,134,2),(16,33,0,134,2),(33,16,66,128,2)]) (IndexTree.leaf [(48,1,66,128,2),(17,64,36,2,2),(17,128,36,2,2),(97,0,146,0,2),(32,65,0,146,2)]))) (IndexTree.fork 8 (IndexTree.leaf [(33,64,144,2,2),(1,160,0,22,2),(128,33,0,22,2),(160,1,66,16,2),(193,0,38,0,2),(129,64,36,2,2),(2,20,0,161,2),(16,6,0,224,2)]) (IndexTree.fork 4 (IndexTree.leaf [(18,4,129,32,2),(20,2,0,224,2),(2,132,0,49,2),(130,4,17,32,2)]) (IndexTree.leaf [(2,48,0,133,2),(18,32,129,4,2),(32,18,0,193,2),(64,18,0,161,2),(18,128,36,1,2)])))) (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(128,18,0,97,2),(130,16,36,1,2),(96,2,17,128,2),(2,160,0,21,2),(130,32,17,4,2),(160,2,17,64,2),(192,2,17,32,2),(4,48,0,131,2)]) (IndexTree.fork 4 (IndexTree.leaf [(20,32,129,2,2),(4,80,0,131,2),(20,64,129,2,2),(64,20,0,161,2)]) (IndexTree.leaf [(148,0,98,0,2),(16,132,0,35,2),(144,4,66,32,2),(4,160,0,19,2),(32,132,0,19,2)]))) (IndexTree.fork 8 (IndexTree.leaf [(36,128,0,19,2),(132,32,17,2,2),(4,192,0,19,2),(68,128,0,19,2),(132,64,17,2,2),(192,4,17,32,2),(112,0,131,0,2),(32,80,0,131,2)]) (IndexTree.fork 4 (IndexTree.leaf [(48,64,129,2,2),(16,160,0,7,2),(128,48,0,7,2),(160,16,66,1,2)]) (IndexTree.leaf [(208,0,38,0,2),(144,64,36,2,2),(32,192,0,19,2),(96,128,0,19,2),(160,64,17,2,2)])))))))
def g247autos : Array (List Nat) := #[[],[64]]
def g247levels : Nat → Packing
  | 7 => g247l7
  | 8 => g247l8
  | 9 => g247l9
  | _ => emptyPacking
def hashg247l8 (i : Nat) : Nat := 0x829003f504b6000000413a48bb
def hashg247l9 (i : Nat) : Nat := 0x414d000001132c8711803c214003080106000c0000002
def g247index : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 4 15 0 8 3 1 (hashg247l8)
  | 9 => lookupWord 4 19 2 9 4 1 (hashg247l9)
  | _ => fun _ => none
def g247 : Forest := ⟨247,9,fun j => g247samples[j]?.getD (0,0),g247columns,g247autos,g247levels,g247index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom247 : graphValid g247 (boundsBefore known181) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=7) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s247_7_0 : block g247 7 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s247_7_6 : block g247 7 6 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all247_7 : block g247 7 0 7=true := (@block_merge g247 7 0 6 1 s247_7_0 s247_7_6)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s247_8_0 : block g247 8 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s247_8_4 : block g247 8 4 5=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all247_8 : block g247 8 0 9=true := (@block_merge g247 8 0 4 5 s247_8_0 s247_8_4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s247_9_0 : block g247 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all247_9 : block g247 9 0 1=true := s247_9_0
theorem tables247 : checkedTables g247 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g247 0 0 0 = true)
  · exact (rfl : block g247 1 0 0 = true)
  · exact (rfl : block g247 2 0 0 = true)
  · exact (rfl : block g247 3 0 0 = true)
  · exact (rfl : block g247 4 0 0 = true)
  · exact (rfl : block g247 5 0 0 = true)
  · exact (rfl : block g247 6 0 0 = true)
  · exact all247_7
  · exact all247_8
  · exact all247_9

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low247 : Lower (vars 247) (graphGoal 247) 10 := lower_forest (g:=g247) (i:=0) (hints:=17827156) (before_sound known181 valid181) geom247 tables247 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps247 : List (Nat × List Nat) := [(499,[130,50]),(251,[101,50]),(502,[117,66,130,32,48]),(487,[117,132,32]),(247,[])]
def known247 := extendKnown known181 10 maps247
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid247 : Known known247 := extendKnown_ok valid181 low247 (by decide +kernel)
def g413 : Forest := ⟨413,6,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low413 : Lower (vars 413) (graphGoal 413) 7 := lower_discard (g:=g413) (ci:=(4,0,409,0,6)) (hints:=8589969412) (before_sound known247 valid247) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps413 : List (Nat × List Nat) := [(441,[50,82]),(473,[98,131,82]),(413,[])]
def known413 := extendKnown known247 7 maps413
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid413 : Known known413 := extendKnown_ok valid247 low413 (by decide +kernel)
def g311 : Forest := ⟨311,6,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low311 : Lower (vars 311) (graphGoal 311) 7 := lower_discard (g:=g311) (ci:=(0,1,294,16,6)) (hints:=8590984532) (before_sound known413 valid413) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps311 : List (Nat × List Nat) := [(411,[117,101,132,48,32]),(407,[117,101,132,32]),(311,[]),(444,[116,133,64,16,97,48]),(429,[116,133,100,49]),(317,[133,49])]
def known311 := extendKnown known413 7 maps311
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid311 : Known known311 := extendKnown_ok valid413 low311 (by decide +kernel)
def g443d7 (i : Nat) : Nat := 0x3d9a3d4505fe39d2879f14b109dd8a5821ef452c007ba212003ed0c7001fc821800
def g443l7 : Packing := (7,2,9,0,0,5,0,g443d7)
def g443d8 (i : Nat) : Nat := 0x5c06188e020cc3204c8030170186640101c80c3120000b066380c205c04202e0314061facda0735041280f00ff8a5ff4a1ff4a0ff460ff420df8a5ef884fd821fe800
def g443l8 : Packing := (9,1,9,3,1,8,0,g443d8)
def g443d9 (i : Nat) : Nat := 0x60681016032ff
def g443l9 : Packing := (1,0,9,4,1,0,0,g443d9)
def g443samples : Array (Bits × Bits) := #[(0x61efb56f0aee75af9de5fb5f813aded86fdfee8f456af097ecfece8d18f1fd538f25b122391ae1e12067f6dbefcfde1dffff9dcf866ecbf2d323ed706e0823d0404002395c42d0a1608a9900212200c80208ee1586836bcf8468047202d35acd,0xd0122ad09529560946840c383546e4e1108e81d018806300a93490e57226903c4a6c80884198019c210cc012c20070641850d1040050710144b120258981444118440428930c00007c150026680524111ca4e898a682694e04680052004258cc),(0x6ba11f5b521f7e1def4baf376f6329b2f9a735e1e8dfef6e563b45fbf02c41e175ba87bd9e95bbbe5b5933673603c253bef822b32750cfad6dd484c339b7400439123c8403800e0a002000db08c5f003d10201c003ba98636262e28884a5c1fc,0xc1ba1941073088151244535940720a2782a956d8882ae2899202001213200432c20d7032528315800c75d95c83c05210508ad00c05d4d46288a900140540a0044200d60040b1e002548862526003c31917e07199ba9210236262e2880085c0ec),(0x0,0x0),(0xd851afe42bf5969c75bf14fe1c466701e104e71efed717b0dce23ab6759ae929be7e76e7fafa050baf129023dd5265b26b0d7bee7fcff06d876cc39ccd009c0102080140802001040101240042000410006100024808d8b225357371e4d43eae,0x300d73e635023980bad3c2331f47b8b459463ac1c900541773c4112b03009a256e8040da1a2043811a41491d4bc0011a9f10085ae020400081a0e96dc0022d18825790611470a1501c0209091e7fca26c6dfee17008c88021257371c4d43eae),(0xf7bee2b6ff7779d7c7cd2e843fa1585f5df8f16c33637fd13343a1984ec69e6dbcfdcbd9495ef7a054afadf11a370deef5e3f7d762a6fa7e6bbb3f34ba40018a44c440221802f0d00cd08b20a52002a80014d42da6551511582fd72488d93073,0x36115200a0220a48909008302380008a6116e08c069801c4243411a88106c800103040734077643c0e10109354c868060090800cc01088a0800869814048aa280180b800410a83280209849060ac3a863481141585114115806d62480912033),(0x5b7b4965e26af714a723dfdce9feba6bb37d7fd3b3fe635a79496e867d94206a15d7d53454f71c75cf877c979b0da23e93811d4f8bbf7cff9bb3c0712a2402089319004229d0808922440ce1059b9056c8201001428ea4858c598c79954c7b1,0x1801869e400453a24da220800905118805008902565001204458304d809048081d800084a524003861000680140c0040a6500e23c2080090031254a24a004030154b205c0c0005400153090d05143ca2680d8e604428ca481085104789500711),(0x0,0x0),(0x5beff7e99d2afb2db17fff3fadd1ae7e3560af1b557ff8de5c5949579e34bfba74b9daba7365bf76cd8d9b2cdb6bbf76ef00cf1869c81d86af74f7cfb85d225e34866e9b454026736c5a12318c864262931c3af821f6868482972b5f4e2a020a,0x800400c60c001000022800000000010490000072304006000002600004002411400014088600000020002800003090280202433320802140044494222201000012200002002114500020180809018468013062601248280809109014e280200),(0xdd7b6b5ebedf814aafb157e550ad15bd3b7fd93083bb210de7fffb73b183ceb743667a7ce7a4685faa336fdf779e7d8d7887a6789c51685617f95eea6f009c2182298140a03d01049305640452180d142ce100025980753afdd25c89710b2c44,0x20b200410c8808458010024c86028430b82b00408123928c08800c2046453651a000024258083a84844141482101e1044006f050011033410045a141019d01064080002080a80028a028c2200200035d9392011e89803532cc520c88300b0040)]
def g443columns : IndexTree ColumnInfo := (IndexTree.fork 140 (IndexTree.fork 70 (IndexTree.fork 35 (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(8,0,435,0,8),(0,8,179,256,8),(264,0,179,0,7),(256,8,179,0,7),(1,0,442,0,7),(2,0,441,0,7),(16,0,427,0,7),(32,0,411,0,7)]) (IndexTree.fork 4 (IndexTree.leaf [(256,0,179,0,7),(0,256,147,40,7),(10,0,433,0,6),(34,0,409,0,6)]) (IndexTree.leaf [(2,256,145,40,6),(0,40,145,258,6),(8,32,145,258,6),(32,8,147,256,6),(8,256,147,32,6)]))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(32,256,147,8,6),(2,40,145,256,5),(10,32,145,256,5),(34,8,145,256,5)]) (IndexTree.leaf [(10,256,145,32,5),(34,256,145,8,5),(296,0,147,0,5),(40,256,147,0,5),(256,40,145,2,5)])) (IndexTree.fork 4 (IndexTree.leaf [(264,32,145,2,5),(288,8,147,0,5),(0,1,298,144,6),(0,16,298,129,6)]) (IndexTree.leaf [(0,32,145,258,6),(128,0,315,0,6),(9,0,434,0,5),(1,8,178,256,5),(17,0,426,0,5)])))) (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(1,16,298,128,5),(16,1,298,128,5),(128,1,298,16,5),(2,8,145,256,5),(2,32,145,256,5),(24,0,419,0,5),(16,8,163,256,5),(40,0,147,0,5)]) (IndexTree.fork 4 (IndexTree.leaf [(128,16,298,1,5),(288,0,147,0,5),(256,32,145,2,5),(25,0,418,0,4)]) (IndexTree.leaf [(265,0,178,0,4),(257,8,178,0,4),(145,0,298,0,4),(129,16,298,0,4),(144,1,298,0,4)]))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(42,0,145,0,4),(266,0,145,0,4),(258,8,145,0,4),(290,0,145,0,4)]) (IndexTree.leaf [(258,32,145,0,4),(280,0,163,0,4),(272,8,163,0,4),(0,2,281,160,5),(0,128,296,19,5)])) (IndexTree.fork 4 (IndexTree.leaf [(3,0,440,0,4),(0,3,264,176,4),(2,1,296,144,4),(0,9,34,400,4)]) (IndexTree.leaf [(8,1,290,144,4),(33,0,410,0,4),(129,0,298,0,4),(1,128,296,18,4),(257,0,178,0,4)]))))) (IndexTree.fork 35 (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(1,256,146,40,4),(0,10,17,416,4),(18,0,425,0,4),(0,18,264,161,4),(2,16,296,129,4),(32,2,281,128,4),(130,0,313,0,4),(2,128,296,17,4)]) (IndexTree.fork 4 (IndexTree.leaf [(128,2,281,32,4),(258,0,145,0,4),(0,258,17,168,4),(0,24,34,385,4)]) (IndexTree.leaf [(8,16,290,129,4),(136,0,307,0,4),(8,128,288,19,4),(128,8,51,256,4),(48,0,395,0,4)]))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(144,0,298,0,4),(16,128,296,3,4),(272,0,163,0,4),(16,256,131,40,4)]) (IndexTree.leaf [(32,128,264,19,4),(0,384,0,59,4),(11,0,432,0,3),(0,11,0,432,3),(10,1,288,144,3)])) (IndexTree.fork 4 (IndexTree.leaf [(1,18,264,160,3),(3,16,296,128,3),(16,3,264,160,3),(17,2,264,160,3)]) (IndexTree.leaf [(18,1,296,128,3),(35,0,408,0,3),(32,3,264,144,3),(34,1,264,144,3),(3,128,296,16,3)])))) (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(128,3,264,48,3),(130,1,296,16,3),(0,259,0,184,3),(2,257,0,184,3),(3,256,144,40,3),(1,24,34,384,3),(9,16,290,128,3),(16,9,34,384,3)]) (IndexTree.fork 4 (IndexTree.leaf [(17,8,162,256,3),(24,1,290,128,3),(0,41,0,402,3),(1,40,144,258,3)]) (IndexTree.leaf [(8,33,0,402,3),(9,32,144,258,3),(33,8,146,256,3),(9,128,288,18,3),(128,9,34,272,3)]))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(136,1,290,16,3),(9,256,146,32,3),(256,9,34,144,3),(264,1,34,144,3)]) (IndexTree.leaf [(49,0,394,0,3),(17,128,296,2,3),(17,256,130,40,3),(33,128,264,18,3),(33,256,146,8,3)])) (IndexTree.fork 4 (IndexTree.leaf [(1,384,0,58,3),(26,0,417,0,3),(0,26,0,417,3),(10,16,288,129,3)]) (IndexTree.leaf [(32,10,17,384,3),(138,0,305,0,3),(10,128,288,17,3),(128,10,17,288,3),(8,258,17,160,3)])))))) (IndexTree.fork 70 (IndexTree.fork 35 (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(256,10,17,160,3),(264,2,17,160,3),(50,0,393,0,3),(32,18,264,129,3),(34,16,264,129,3),(18,128,296,1,3),(128,18,264,33,3),(130,16,296,1,3)]) (IndexTree.fork 4 (IndexTree.leaf [(0,274,0,169,3),(2,272,0,169,3),(18,256,129,40,3),(162,0,281,0,3)]) (IndexTree.leaf [(34,128,264,17,3),(160,2,281,0,3),(32,258,17,136,3),(2,384,0,57,3),(128,258,17,40,3)]))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(130,256,17,40,3),(0,56,0,387,3),(8,48,0,387,3),(16,40,129,258,3)]) (IndexTree.leaf [(24,32,129,258,3),(48,8,131,256,3),(24,128,288,3,3),(128,24,34,257,3),(136,16,290,1,3)])) (IndexTree.fork 4 (IndexTree.leaf [(24,256,131,32,3),(256,24,34,129,3),(264,16,34,129,3),(0,168,0,275,3)]) (IndexTree.leaf [(8,160,0,275,3),(32,136,0,275,3),(128,40,17,258,3),(136,32,17,258,3),(392,0,51,0,3)])))) (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(8,384,0,51,3),(384,8,51,0,3),(48,128,264,3,3),(48,256,131,8,3),(16,384,0,43,3),(32,384,0,27,3),(1,2,264,160,3),(0,33,0,402,3)]) (IndexTree.fork 4 (IndexTree.leaf [(1,32,144,258,3),(32,1,264,144,3),(0,257,0,184,3),(256,1,34,144,3)]) (IndexTree.leaf [(8,2,17,160,3),(16,2,264,160,3),(256,2,17,160,3),(0,136,0,275,3),(0,48,0,387,3)]))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(16,32,129,258,3),(32,16,264,129,3),(0,272,0,169,3),(256,16,34,129,3)]) (IndexTree.leaf [(160,0,281,0,3),(0,160,0,275,3),(128,32,17,258,3),(384,0,51,0,3),(128,256,17,40,3)])) (IndexTree.fork 4 (IndexTree.leaf [(1,10,0,416,2),(2,9,0,400,2),(3,8,144,256,2),(8,3,0,176,2)]) (IndexTree.leaf [(19,0,296,0,2),(2,33,0,400,2),(3,32,144,256,2),(33,2,264,128,2),(131,0,296,0,2)]))))) (IndexTree.fork 35 (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(129,2,264,32,2),(1,258,0,168,2),(256,3,0,176,2),(41,0,146,0,2),(32,9,0,400,2),(137,0,290,0,2),(1,136,0,274,2),(129,8,34,256,2)]) (IndexTree.fork 4 (IndexTree.leaf [(8,257,0,176,2),(1,48,0,386,2),(16,33,0,386,2),(33,16,264,128,2)]) (IndexTree.leaf [(48,1,264,128,2),(273,0,162,0,2),(1,272,0,168,2),(16,257,0,168,2),(257,16,34,128,2)]))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(272,1,34,128,2),(1,160,0,274,2),(128,33,0,274,2),(160,1,264,16,2)]) (IndexTree.leaf [(289,0,146,0,2),(32,257,0,152,2),(256,33,0,146,2),(257,32,144,2,2),(128,257,0,56,2)])) (IndexTree.fork 4 (IndexTree.leaf [(384,1,34,16,2),(2,24,0,385,2),(8,18,0,161,2),(16,10,0,416,2)]) (IndexTree.leaf [(18,8,129,256,2),(40,2,17,128,2),(2,136,0,273,2),(130,8,17,256,2),(136,2,17,32,2)])))) (IndexTree.fork 17 (IndexTree.fork 8 (IndexTree.leaf [(2,48,0,385,2),(18,32,129,256,2),(48,2,264,128,2),(146,0,296,0,2),(144,2,264,32,2),(16,258,0,168,2),(256,18,0,161,2),(2,160,0,273,2)]) (IndexTree.fork 4 (IndexTree.leaf [(130,32,17,256,2),(288,2,17,128,2),(384,2,17,32,2),(56,0,131,0,2)]) (IndexTree.leaf [(32,24,0,385,2),(152,0,290,0,2),(16,136,0,259,2),(144,8,34,256,2),(8,272,0,161,2)]))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(40,128,0,19,2),(160,8,17,256,2),(136,256,17,32,2),(256,136,0,19,2)]) (IndexTree.leaf [(264,128,0,19,2),(16,160,0,259,2),(128,48,0,259,2),(160,16,264,1,2),(304,0,131,0,2)])) (IndexTree.fork 4 (IndexTree.leaf [(32,272,0,137,2),(256,48,0,131,2),(272,32,129,2,2),(128,272,0,41,2)]) (IndexTree.leaf [(384,16,34,1,2),(160,256,17,8,2),(256,160,0,19,2),(288,128,0,19,2),(384,32,17,2,2)])))))))
def g443autos : Array (List Nat) := #[[],[64]]
def g443levels : Nat → Packing
  | 7 => g443l7
  | 8 => g443l8
  | 9 => g443l9
  | _ => emptyPacking
def hashg443l8 (i : Nat) : Nat := 0x44f6d04300ea0000b581420088fb00044
def hashg443l9 (i : Nat) : Nat := 0x42161a572108003693801860040a8000b4d3000000008
def g443index : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 4 15 3 8 3 1 (hashg443l8)
  | 9 => lookupWord 4 19 2 9 4 1 (hashg443l9)
  | _ => fun _ => none
def g443 : Forest := ⟨443,9,fun j => g443samples[j]?.getD (0,0),g443columns,g443autos,g443levels,g443index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom443 : graphValid g443 (boundsBefore known311) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=7) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s443_7_0 : block g443 7 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s443_7_6 : block g443 7 6 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all443_7 : block g443 7 0 7=true := (@block_merge g443 7 0 6 1 s443_7_0 s443_7_6)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s443_8_0 : block g443 8 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s443_8_4 : block g443 8 4 5=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all443_8 : block g443 8 0 9=true := (@block_merge g443 8 0 4 5 s443_8_0 s443_8_4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s443_9_0 : block g443 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all443_9 : block g443 9 0 1=true := s443_9_0
theorem tables443 : checkedTables g443 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g443 0 0 0 = true)
  · exact (rfl : block g443 1 0 0 = true)
  · exact (rfl : block g443 2 0 0 = true)
  · exact (rfl : block g443 3 0 0 = true)
  · exact (rfl : block g443 4 0 0 = true)
  · exact (rfl : block g443 5 0 0 = true)
  · exact (rfl : block g443 6 0 0 = true)
  · exact all443_7
  · exact all443_8
  · exact all443_9

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low443 : Lower (vars 443) (graphGoal 443) 10 := lower_forest (g:=g443) (i:=0) (hints:=12885983316) (before_sound known311 valid311) geom443 tables443 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps443 : List (Nat × List Nat) := [(475,[101,131]),(443,[])]
def known443 := extendKnown known311 10 maps443
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid443 : Known known443 := extendKnown_ok valid311 low443 (by decide +kernel)
def g477d7 (i : Nat) : Nat := 0x1fe800
def g477l7 : Packing := (1,1,9,0,0,0,0,g477d7)
def g477d8 (i : Nat) : Nat := 0x864121ff
def g477l8 : Packing := (1,0,9,0,2,0,0,g477d8)
def g477samples : Array (Bits × Bits) := #[(0xabe96674ef3c1f3dc9e6e4cda265f47613cf4e95d3e47f75b03b66f6d8dffb690fb5db71fd6da758cb547bd7c5a95879fddbe86f240f5be72cb1f5fbf38a18442184a0108801c2b978932ec119308189831a92602b28967ce1e5504ee4a84aac,0x45580c2000f40385a10006c4460000810060a8094f5499349630a2800050046a10a290ca2211e000a0080180080080212140104aa03455000012041c480060e0182d18091662002202060600038038228c225b0232096546141000ee42840a0),(0x0,0x0),(0x2ce2b1fed6558fcf33c37abf6fb86789f5257be4587ef7a7dcf2d3931f8f27d280cd912bc7b6fd9d7fbc47e54d3cd6f2490fd384b6241ffc0e2adf8d63c4022210300d0c600021000100c1002001040070810104f21c43b1ef086596064ad379,0x31562e9bc48d6b0829a48c220711795081aa27b90e232594a80a204e2812475f9580958fc2939013543856e23099d4e652d155484111460f05e8ebe038150040cfcc0081084905060501430159aeb6b6e7abb47f321c43b1ef0865840402c379),(0x5477d7cdf9242ed6ab34f577334ff92bd9f246d3a6a550a4c4bca99ec7abbe4c793fa7c36e9cb8fa30f7fe7a1b87feb3f1da57c7faf9c013ffff40c9b9b02109cc4b524206fa14428060003cc6c46a740c60641835567b00d4ab8e2d611366c1,0x12146a001191010c643393200402f9800090841402015b302861024100212140c406008080814290043c040001a1912c149631100603094804c0022005409808101204018b19a61001003086040e003080a3b46530063b0084a98825210242c1),(0xeffb9ba576ae68fbdc9ba0947b6c5ed74e19fb1bf9db3d8fbbeff59b3e759e1b62fcfc86fd6986aef7fde2aaf77731dc5e770c19db9dbd79b7e96d7cce73c490228480a199044a954e0c1ec3013a1003820c0ae3b49d24e2029431e1bd27b227,0x7a087f18fa501201008088118015aa5005908004200800000010850020121f0012c046f01c90a098014003430338202409e3023950200082380ac5001a448821100c005806104858068088105201406dc7258003949c0020029411e11105b205),(0x0,0x0),(0xea04bfef9f07254d0349982853af93a6befdae59c0e5b2c76e11487ab630777ca44adabeaeefffbdeb25bdd173ee97b6c73fbdb9b6b6a439c723aef02cb0000904491242001a10020020000c82844204006044088fd5cbe05d461e90cdcd8188,0x4d49919a6444a432100068d7cbf004203101594b306880cc4110a0325a80de3531b025453e662426aa82d37acc1a264063004ca3c8b0963321394d9d48a02285a2003802408409e0809d8c6920b1ffcf7f5c4b9a8fd1c0e059461690cccd8108),(0xd7feec0371d7f83db6aaeb8fcf53becccfc08d2f376d7e5babd47e7c60d3dbac7cc9057518ea7d27d8fea3da75d817373ae5f1feb94e619fda3db67757c9dcd4030020b11105882c369f3002180a918a0116988318a1b08faf72ee951a860c4a,0x10000250100058685607602118214a5aa09245200021620868870c59780c0094405800000484007102464a0bc41d0104408780204943020023418aa010831006071082600001205401801060d46bc1010185a4c0801208b8c22ee100a820c4a),(0xbda5add649cdfbc36f579f5e9dd237db29f630b46e7add3f192e878569d96cffdfafb1c9789efedb7f03e465f9d77da94f59ff147d664f77d4edde1b30942322d8324d0c66e025408140c13064412c707c812114cbe200190849933a9a79f557,0x4080100020004c100402004f86c042c380018400098000a538489b05384082008486830294c2c44a1008905c602200021088a83002490303001001cc28a05b20000a07440a25001320004188011494918544b80c9e000080040121a9a793406)]
def g477columns : IndexTree ColumnInfo := (IndexTree.fork 158 (IndexTree.fork 79 (IndexTree.fork 39 (IndexTree.fork 19 (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(4,0,473,0,7),(0,4,217,256,7),(64,0,413,0,7),(0,64,405,8,7)]) (IndexTree.leaf [(0,12,145,320,6),(4,8,145,320,6),(68,0,409,0,6),(0,68,145,264,6),(260,0,217,0,6)])) (IndexTree.fork 5 (IndexTree.leaf [(256,4,217,0,6),(72,0,405,0,6),(8,64,405,0,6),(0,320,145,12,6),(64,256,145,12,6)]) (IndexTree.leaf [(8,68,145,256,5),(64,12,145,256,5),(68,8,145,256,5),(72,4,145,256,5),(256,12,145,64,5)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(260,8,145,64,5),(4,320,145,8,5),(68,256,145,8,5),(256,68,145,8,5),(260,64,145,8,5)]) (IndexTree.leaf [(8,320,145,4,5),(72,256,145,4,5),(1,0,476,0,6),(0,1,332,144,6),(8,0,405,0,6)])) (IndexTree.fork 5 (IndexTree.leaf [(0,8,145,320,6),(16,0,461,0,6),(0,16,332,129,6),(128,0,349,0,6),(0,128,332,17,6)]) (IndexTree.leaf [(256,0,217,0,6),(0,256,145,12,6),(1,16,332,128,5),(16,1,332,128,5),(1,128,332,16,5)])))) (IndexTree.fork 20 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(128,1,332,16,5),(8,4,145,256,5),(4,64,145,8,5),(64,4,145,256,5),(4,256,145,8,5)]) (IndexTree.leaf [(64,8,145,256,5),(8,256,145,4,5),(256,8,145,64,5),(16,128,332,1,5),(128,16,332,1,5)])) (IndexTree.fork 5 (IndexTree.leaf [(256,64,145,8,5),(145,0,332,0,4),(17,128,332,0,4),(129,16,332,0,4),(144,1,332,0,4)]) (IndexTree.leaf [(76,0,145,0,4),(12,64,145,0,4),(268,0,145,0,4),(12,256,145,0,4),(264,4,145,0,4)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(324,0,145,0,4),(320,4,145,0,4),(328,0,145,0,4),(264,64,145,0,4),(320,8,145,0,4)]) (IndexTree.leaf [(5,0,472,0,4),(0,5,72,400,4),(1,4,216,256,4),(4,1,328,144,4),(17,0,332,0,4)])) (IndexTree.fork 5 (IndexTree.leaf [(65,0,412,0,4),(0,65,260,152,4),(1,64,404,8,4),(64,1,268,144,4),(129,0,332,0,4)]) (IndexTree.leaf [(12,0,145,0,4),(20,0,457,0,4),(0,20,72,385,4),(4,16,328,129,4),(16,4,201,256,4)]))))) (IndexTree.fork 39 (IndexTree.fork 19 (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(132,0,345,0,4),(0,132,72,273,4),(4,128,328,17,4),(128,4,89,256,4)]) (IndexTree.leaf [(264,0,145,0,4),(80,0,397,0,4),(0,80,260,137,4),(16,64,389,8,4),(64,16,268,129,4)])) (IndexTree.fork 5 (IndexTree.leaf [(144,0,332,0,4),(192,0,285,0,4),(0,192,260,25,4),(64,128,268,17,4),(128,64,277,8,4)]) (IndexTree.leaf [(320,0,145,0,4),(0,13,0,464,3),(1,12,144,320,3),(4,9,0,464,3),(5,8,144,320,3)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(1,20,72,384,3),(5,16,328,128,3),(16,5,72,384,3),(20,1,328,128,3),(69,0,408,0,3)]) (IndexTree.leaf [(0,69,0,408,3),(1,68,144,264,3),(68,1,264,144,3),(1,132,72,272,3),(5,128,328,16,3)])) (IndexTree.fork 5 (IndexTree.leaf [(128,5,72,272,3),(132,1,328,16,3),(261,0,216,0,3),(256,5,72,144,3),(257,4,216,0,3)]) (IndexTree.leaf [(260,1,72,144,3),(73,0,404,0,3),(8,65,260,144,3),(9,64,404,0,3),(72,1,260,144,3)])))) (IndexTree.fork 20 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(1,80,260,136,3),(16,65,260,136,3),(65,16,268,128,3),(80,1,268,128,3),(1,192,260,24,3)]) (IndexTree.leaf [(65,128,268,16,3),(128,65,260,24,3),(192,1,268,16,3),(0,321,0,156,3),(1,320,144,12,3)])) (IndexTree.fork 5 (IndexTree.leaf [(64,257,0,156,3),(65,256,144,12,3),(0,28,0,449,3),(4,24,0,449,3),(16,12,129,320,3)]) (IndexTree.leaf [(20,8,129,320,3),(0,140,0,337,3),(4,136,0,337,3),(128,12,17,320,3),(132,8,17,320,3)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(84,0,393,0,3),(0,84,0,393,3),(16,68,129,264,3),(68,16,264,129,3),(16,132,72,257,3)]) (IndexTree.leaf [(20,128,328,1,3),(128,20,72,257,3),(132,16,328,1,3),(276,0,201,0,3),(256,20,72,129,3)])) (IndexTree.fork 5 (IndexTree.leaf [(260,16,72,129,3),(272,4,201,0,3),(196,0,281,0,3),(0,196,0,281,3),(68,128,264,17,3)]) (IndexTree.leaf [(128,68,17,264,3),(388,0,89,0,3),(256,132,72,17,3),(260,128,72,17,3),(384,4,89,0,3)])))))) (IndexTree.fork 79 (IndexTree.fork 39 (IndexTree.fork 19 (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(88,0,389,0,3),(8,80,260,129,3),(24,64,389,0,3),(72,16,260,129,3)]) (IndexTree.leaf [(200,0,277,0,3),(8,192,260,17,3),(72,128,260,17,3),(136,64,277,0,3),(16,192,260,9,3)])) (IndexTree.fork 5 (IndexTree.leaf [(80,128,268,1,3),(128,80,260,9,3),(192,16,268,1,3),(0,336,0,141,3),(16,320,129,12,3)]) (IndexTree.leaf [(64,272,0,141,3),(80,256,129,12,3),(0,448,0,29,3),(64,384,0,29,3),(128,320,17,12,3)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(192,256,17,12,3),(9,0,404,0,3),(0,9,0,464,3),(1,8,144,320,3),(8,1,260,144,3)]) (IndexTree.leaf [(257,0,216,0,3),(0,257,0,156,3),(1,256,144,12,3),(256,1,72,144,3),(24,0,389,0,3)])) (IndexTree.fork 5 (IndexTree.leaf [(0,24,0,449,3),(8,16,260,129,3),(16,8,129,320,3),(136,0,277,0,3),(0,136,0,337,3)]) (IndexTree.leaf [(8,128,260,17,3),(128,8,17,320,3),(272,0,201,0,3),(0,272,0,141,3),(16,256,129,12,3)])))) (IndexTree.fork 20 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(256,16,72,129,3),(384,0,89,0,3),(0,384,0,29,3),(128,256,17,12,3),(256,128,72,17,3)]) (IndexTree.leaf [(8,5,0,400,2),(9,4,144,256,2),(21,0,328,0,2),(17,4,72,256,2),(4,65,0,152,2)])) (IndexTree.fork 5 (IndexTree.leaf [(5,64,144,8,2),(64,5,0,400,2),(65,4,144,256,2),(133,0,328,0,2),(129,4,72,256,2)]) (IndexTree.leaf [(4,257,0,152,2),(5,256,144,8,2),(1,24,0,448,2),(9,16,260,128,2),(16,9,0,448,2)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(24,1,260,128,2),(64,9,0,400,2),(65,8,144,256,2),(1,136,0,336,2),(9,128,260,16,2)]) (IndexTree.leaf [(128,9,0,336,2),(136,1,260,16,2),(8,257,0,148,2),(9,256,144,4,2),(256,9,0,208,2)])) (IndexTree.fork 5 (IndexTree.leaf [(257,8,144,64,2),(81,0,268,0,2),(17,64,260,8,2),(1,272,0,140,2),(16,257,0,140,2)]) (IndexTree.leaf [(257,16,72,128,2),(272,1,72,128,2),(193,0,268,0,2),(129,64,260,8,2),(256,65,0,152,2)]))))) (IndexTree.fork 39 (IndexTree.fork 19 (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(257,64,144,8,2),(1,384,0,28,2),(128,257,0,28,2),(257,128,72,16,2)]) (IndexTree.leaf [(384,1,72,16,2),(8,20,0,385,2),(24,4,129,256,2),(8,132,0,273,2),(136,4,17,256,2)])) (IndexTree.fork 5 (IndexTree.leaf [(4,80,0,137,2),(20,64,129,8,2),(64,20,0,385,2),(80,4,129,256,2),(148,0,328,0,2)]) (IndexTree.leaf [(144,4,72,256,2),(4,272,0,137,2),(20,256,129,8,2),(4,192,0,25,2),(64,132,0,273,2)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(132,64,17,8,2),(192,4,17,256,2),(4,384,0,25,2),(132,256,17,8,2),(64,24,0,385,2)]) (IndexTree.leaf [(80,8,129,256,2),(16,136,0,321,2),(24,128,260,1,2),(128,24,0,321,2),(136,16,260,1,2)])) (IndexTree.fork 5 (IndexTree.leaf [(8,272,0,133,2),(24,256,129,4,2),(256,24,0,193,2),(272,8,129,64,2),(64,136,0,273,2)]) (IndexTree.leaf [(192,8,17,256,2),(8,384,0,21,2),(136,256,17,4,2),(256,136,0,81,2),(384,8,17,64,2)])))) (IndexTree.fork 20 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(208,0,268,0,2),(144,64,260,8,2),(256,80,0,137,2),(272,64,129,8,2),(16,384,0,13,2)]) (IndexTree.leaf [(128,272,0,13,2),(272,128,72,1,2),(384,16,72,1,2),(256,192,0,25,2),(384,64,17,8,2)])) (IndexTree.fork 5 (IndexTree.leaf [(13,0,144,0,1),(12,1,0,144,1),(25,0,260,0,1),(17,8,0,320,1),(137,0,260,0,1)]) (IndexTree.leaf [(129,8,0,320,1),(265,0,144,0,1),(264,1,0,144,1),(273,0,72,0,1),(17,256,0,12,1)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(321,0,144,0,1),(320,1,0,144,1),(385,0,72,0,1),(129,256,0,12,1),(28,0,129,0,1)]) (IndexTree.leaf [(12,16,0,129,1),(140,0,17,0,1),(12,128,0,17,1),(152,0,260,0,1),(144,8,0,320,1)])) (IndexTree.fork 5 (IndexTree.leaf [(280,0,129,0,1),(264,16,0,129,1),(392,0,17,0,1),(264,128,0,17,1),(336,0,129,0,1)]) (IndexTree.leaf [(320,16,0,129,1),(400,0,72,0,1),(144,256,0,12,1),(448,0,17,0,1),(320,128,0,17,1)])))))))
def g477autos : Array (List Nat) := #[[],[116],[64],[112,64],[64,112],[112],[131,98],[116,131,98],[131,98,64],[112,131,98,64],[64,131,98,112],[131,98,112]]
def g477levels : Nat → Packing
  | 7 => g477l7
  | 8 => g477l8
  | _ => emptyPacking
def hashg477l8 (i : Nat) : Nat := 0xa9f300000
def g477index : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 6 0 6 0 2 (hashg477l8)
  | _ => fun _ => none
def g477 : Forest := ⟨477,8,fun j => g477samples[j]?.getD (0,0),g477columns,g477autos,g477levels,g477index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom477 : graphValid g477 (boundsBefore known443) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=7) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s477_7_0 : block g477 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all477_7 : block g477 7 0 1=true := s477_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s477_8_0 : block g477 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all477_8 : block g477 8 0 1=true := s477_8_0
theorem tables477 : checkedTables g477 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g477 0 0 0 = true)
  · exact (rfl : block g477 1 0 0 = true)
  · exact (rfl : block g477 2 0 0 = true)
  · exact (rfl : block g477 3 0 0 = true)
  · exact (rfl : block g477 4 0 0 = true)
  · exact (rfl : block g477 5 0 0 = true)
  · exact (rfl : block g477 6 0 0 = true)
  · exact all477_7
  · exact all477_8

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low477 : Lower (vars 477) (graphGoal 477) 9 := lower_forest (g:=g477) (i:=0) (hints:=8640292868) (before_sound known443 valid443) geom477 tables477 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps477 : List (Nat × List Nat) := [(505,[82]),(477,[])]
def known477 := extendKnown known443 9 maps477
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid477 : Known known477 := extendKnown_ok valid443 low477 (by decide +kernel)
def g379 : Forest := ⟨379,8,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low379 : Lower (vars 379) (graphGoal 379) 9 := lower_discard (g:=g379) (ci:=(0,1,362,16,8)) (hints:=12902752340) (before_sound known477 valid477) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps379 : List (Nat × List Nat) := [(379,[])]
def known379 := extendKnown known477 9 maps379
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid379 : Known known379 := extendKnown_ok valid477 low379 (by decide +kernel)
def g507d8 (i : Nat) : Nat := 0xe7bb4e4bf6aad0971a0bc6ec96a84678c941e28280e7a8e78425000c1f8b8c68a5884842f8d8c68a5884821f398e78c6842821f998c68a5842821fa98c6884842821fc98a5884842821f8e8c68a5884800fc68a5884863800f3a8e78c6842800f9a8c68a5842800faa8c6884842800fca8a5884842800f728e7863842800fd28a5863842800fe2884863842800fac8c6884821800fcc8a5884821800fe4884863821800f788e7842821800fb88c6842821800fd88a5842821800fe8884842821800ff0863842821800
def g507l8 : Packing := (24,4,8,0,0,7,0,g507d8)
def g507d9 (i : Nat) : Nat := (if i<1 then 0x37fc634842526ff4c09084a4dfe8c1210949bfd2924213077fa71484260eff4a29084c1dfe905210983bfd2064213077fa20c84260eff8c6908481dfe981210903bfd1824212077fc63282a40eff4c0505481dfe8c0a0a903fbe319291207f7a60252240fef4604a44819fe25118d043afe319419293d7c632622416bf9084c44c1d7f18ca0c903ebe319311207dec63260c10dbf9294a48c6b7e25094918d6fd49040631adfc94a40c635bf1284818c6b7ea4a90318debd29120631adf894220c635bf1288218c6f7a90304318def510608631bd7c63262c427af8c64c2884bdf252983109ebe319306213f6a60c10c427ed821420884f7718c98b085eee31931210afdc94a60c217bb8c64c1842ff2983043085fe608508210afe894463410fbd8c64c4821f7b18c9850437fa4a5312002ff494a524005fe5264a4800fdc9889050017fa4a5306003df262260c005fe929481800bfca4c9030017f9495206003f7262240c007ee4a4481800ff8983043001ff1206086003fe220c10c007af4a28c6884f5e24318d109ebd28631a213d7a20c634427af8218c6884f9f18d14b109f3d306296213e7a60452c427cf4608a5884f9e84114b109dee31a39e10bbda60c73c2177b0c18e7842ef70431cf085ded30239e10bbda30473c2177b4208e7842f7694918d085eec48631a10bdda50c634217bb4818c6842f7704318d085f6e31a29610beda60c52c217db4c08a5842fb68c114b085f6d08229610bf5c634424217eb4c1884842fd6981109085fad18221210bf5a104424217bd1288c6821f7a94918d043ef538a31a087dea51463410fbd4828c6821fda20d109043fb631a212087f6a60442410fed460884821ff220d085043fe631a10a087fca60421410ff9460842821f7c94918d001ef938a31a003df2514634007be4828c6800f7c90318d001ef910631a003df410c634007ee4c5884800fdc985109001fb928a212003f7260c424007ee4a1884800fdc883109001fba086212003fb252431c007f64e2863800fec9450c7001fd920a18e003fb240c31c007f6441863800fed0430c7001fe931610a003fd2624214007fa4a4842800ff4983085001fe928610a003fd240c214007fa821842800ff8989043001ff1292086003fe271410c007fc4c2821800ff8945043001ff120a08600277c94a82060e6f8e75040c1d9f14aa08183bae10941030775c42281060eee8845000c1df5084a00183e3e31a2962139dc73c6342179b8c68a5842f5718d109085f2e29621210bd6c63442410fcd8a5884821ef31cf085043ee631a10a087ecc52c21410fe9884842821f5d18d109001f3a296212003f3442431c0077a8e7842800f7518d085001f6a29610a003f54424214007f2863842800f7918d043001fb2212086003fa431c10c007f8842821800 else 0x3e028406003302180c00cc0060cc0f880900810100102036c140f8c0181f1304002020607c05080c0066043018019800c1e80a101800cc08603003300185e0c046042808c004174390a03b001605c02260016001214106000d030b030e000d030e000b040d010907081820400c0010000006000800040e10030007000483e001505a022c0016061c001c001c00141e1608100182040003040800060416001000012423812181810580040000000001810580040003020b000800000182840060416001001810580040003050818204000000060810000060a10304080000000000000001828426839830308e1041fc18204d077060611c1d839830480f07a0c0c1f83d07306080ec1cc181e030a1d436283a183618361a061a06123a46c54042474246c28603800306024748d890c048e848d850c050c0700050c07000674e6b661e5b25464da4423d633e2d223a1a213609e005fc5f59eede81e15da9d69d29ce9cd5c95c55c15bd5b95b55b15ad5a95a81a41a2da199d99c59b199d98997593592190d8f98b98a58918518117a57396f96b96796395f95b95795655515114fd4e94d549548146d4594193d93c53b139d3052f12b127125d24923522120d1f91e51d119115113d1291150d509508106d059045030ff0fdcfc8f88f48f34f20ee0ea0e8ce78e64e24e10dd0dbcda8d94d80d6cd58d18d04cf0cdccc8c88c74c34c20c0cbf8be4bd0bbcba8b94b80b6cb58b44b30af0a589948fc8387a06dc6446045985585184d84984583ec3ac36c32c2ec2ac26c2001c01801401000c008004)
def g507l9 : Packing := (174,3,8,5,2,12,0,g507d9)
def g507d10 (i : Nat) : Nat := (if i<1 then 0x2014400f43c1a3a8e09180e51e18728e89114151b0e488120c8c0c400f91d0e51a2a008323030e51e468683a068f2380c150941d048011e0611c40d08ea38241d030611e22208f090546d1e1a1688a360c11098011e4701840cc82206808348f160d4120046e1841cc03e0a210720c170301c1e060803e0a210720c17054550fc1203871183c07816010b87c224367c0b000741b24028aa1f0f4388c1b030ef0210f00074d820738108780036680100c151543f04c0f0181d185608818728be058007c8da1010f113c0b004743946d182e0981e020c170540e0dc1200472183e0b82607808305836004791c860b82e0906e0780a0f004308d72eae3517a54d13e7eb373982ca5e47b1cf8b0c3ce10b0177d4bc9dd72e376e4b56d9b2c6b5f4ad9d5caa77504a61d23289740a9e9cec271b360994cba256327091cc8323bf1a8895c3d2153086827c0b1ffefd27cdbd19e46ef6764b9d1cb6e4270fb7c9b62d7a69cb4099aacb2647b11181abea5deae416dab36589abc159aa9652fa8c941e9c44cba5a928e910476a2d9112866421a058fd27b23c79dd8ea673a3869ba8d6669033698d8bc25c82cd9608abe53227892e88f244220a8f7872634818d8b685322580f7866828a10e06182300aa000ffe319293ff8c64e2ffe31928bff8c6482ffe421307ff5044c1ffd311307ff4a44c1ffd409307ff4e24c1ffd309307ff4a24c1ffd209307ff8c6481ffd305207ff8c6441ffd305107ff8c6821ffd291303ff4e24c0ffd289303ff4824c0ffd205303ff4414c0ffe085303ff4a4460ffd389183ff4a2460ffd209183ff481460ffd105183ff821460ffd291083ff4e2420ffd289083ff482420ffd205083ff441420bfe421313bf8c64c4bfe421292ff5064a4efe31930bef4c4482bfe421307bf8c64c1efd311306ff5040c1bfe421206ff506481bfd415207ef4c4481fbd291207fd4c1821ff5206087fd441821ff6085083bf4a48c6efd38a31bbf4a28c6efd20a31bbf1018c6efd20631bbf4418c6efe08631bef8c6884fbd316213ef4c2884fbd28a213ef4c1884fbc306213ef4a1884fbd106213ef821884fbd302213ef4a0884fbd182213ef440884fbd082213fb8c6842fed31610bfb4c4842fed29210bfb4c1842fec30610bfb4a1842fed20610bfb821842fed30210bfb4a0842fed20210bfb460842fed08210bfd106821ff631a087fd4c4821ff5292087fd4e2821ff530a087fd4a2821ff520a087fd4c0821ff5202087fd460821ff5102087fe4c4800ff9292003fe4e2800ff930a003fe4a2800ff920a003fe4c1800ff9206003fe441800ffa086002ef5040c1bed408306fe5000c1ebe31a213cf8a5884dee39e10bbb8c6842f6e29610beb884842ef631a087ed884821fe610a087be8c6800fba212003f6863800fea10a003fc821800 else 0x20785c3d87a1b460c83c3a8c43840ea104621e220f02a3108c3650280717483220782236419007441035144020cc204350c87a1e17044050446c832c350ca3a8e1007004394788328730d4328823c54161a8651b0f8b0bc230d87a8c1439469191003d2c09818768c43c581039469190ee1e340903c362f230541e024791c8621a340f012228dc34580a184211d868a82c048dc0d0c23c68091e47218868a822070140d0c23c64120246e0686090320f0023c8e40d0c1a068011d472182c008840c8f4305819058011b8611e34008f23903430541103802068611e32090040c8dc183998078143d0f21a2a228dc3430e51d868682a228dc34440e011003d868a82406808770d23c601a0386443100b05c1103c3b018306c0833c004010ca03a301a878481e030621e240a00a3013c3c5857050dc4706607c1303c04918687264170880f0d83050540f40c3e0e483100e268301c8f0209b0010c402a30200863c0b000f447200e8c086201004c0b000f0402a1684a0c88a361f23003a03f0f4391872820768f12048021b868884a0e832088f0308e20684751c12208f09054451b1a168420e0c11094191e4701840cc82206862028f161583d0446e1841cd0ba0813c368c144b0f91810c81ca308f0c394411e1a17002220da348c87c70fc3d05c39460a2587a218d044603947881f87a8c0724409184686258868907c8d15004191818728f234344040468709a0e08c368c1443075164603c28861ca3023901b1183c1c00250780da348c87270ec130e51820860e8761e10430e8471c26828768c0725409184686218781d03a8d14430e41b46888020c8c0c3a0791a1a168407c8c12074111b46081f0728823)
def g507l10 : Packing := (132,2,8,8,2,13,0,g507d10)
def g507d11 (i : Nat) : Nat := 0x782c1207010c180e030f0541e4d0e060729198240e030883e0404800703a3960e605000e870a150781c06390c078f030840a00390f180a2781400361e302c100782c1207010d06520b0401e0a421c860e090780c3d0280110383f21a8140400c0e05001c87900a0206e05001e0fc843903a80e0282c1207010d1c581703810063e0d86900082c12060680860e07018e43c1a281e0b0481c0434600416081507c0e021844100617814003660040827000f06cc0082c1207028081e00882c12060d80800307bdd66293cf59631da1dbe5742d097aa964a4814e098f2a841c66091088003ff18dff4c4ffa527fd38bfe985ff4a2ffa417fd307fe183ff481ffa20ffe087fe981ff480ffa307fd103fe841bf8c6f7c427ee10bfb043fe800
def g507l11 : Packing := (22,1,8,8,2,11,0,g507d11)
def g507d12 (i : Nat) : Nat := 0xa08060402006ff
def g507l12 : Packing := (1,0,8,5,2,0,0,g507d12)
def g507samples : Array (Bits × Bits) := #[(0xbf5c9e5778f1e97aa437504aeb33565329f3e232abce03bd68fa7dc1c91af0266884031471e0018641061000000d604000081607020802280c2102190488111380c9098880344414000a0001a179c8c5b8420483b4c301472c35e0ec26f0b02b,0x805000348c80638440209401a120f96d0462746c8600c041851416200028024cd11228b340082911aa410012a10104001c00828b1008900000607003010108dc14f5455a11102d484482745761680045b0020481908301432805e0ec26d0b003),(0xd6fa17fdfffe57f5cdfa9967c5cdeefed2a6cad00e4cb454ca315add68dd0ddf8263dc4082121c009e49e9792422160255a3609000612900d188b006711048240010840463023a49bd75c85c68462426a4968906121e972020b82eaa8706d786,0x22001010c0060000701000042de00003408a0000021401021c0000201439410d0b64800010c1421003844500000100010c00080201023c90000518401800290a89217140c05208424896565808042426a41609021214050020b00ea806009284),(0x0,0x0),(0xbc6c51c67ca5f88f3343fd9935b8a14fafae74b7e53348817591336d36d5c32c611000010809626920b00480c98080202a1408284c100444221644200266a2c8200052510cc101000000270205a91c17822d70b6eacc4dcac9c8190a124180c7,0x2200014804081420000006ca4148580000c0803014010a4008d0064000ea8140446410801212a2228000a104010c8c85020902000328c148500603060282ed38418d24519a146185c0944a3841a1181780246006aacc4cc84988190a02008047),(0xd4fee1d67a2eb16eb278dff7eeae0cf56bb9d70de2057d54bcea4fc19ff3db700c00032255a48004400002040050215400481103930a902304410a11088800035e802980903844a4400010810a01d358d4739a6a86d8e01057f40b50e0ac18c4,0x39a001020104040a901628460408001202840811511d0e802820010054057ca10e00420024320028110084a0082488084146045002042e22a19004408c36e102e9023a80e2ce52132a3c82a80a01d318045198620658a00057f00b10c02400c4),(0x39499eab11fe7f66281c56aa39c95337ef7497b19bcbdeea73bc9c9b96bf6637120838c8001014101040090332001c898081a0c020844090c10011c0d0110c00012680222202a24a068508201106481b0d209f94876baa8dd202f0ff49820853,0x45fb894c14894262094b25f1c012170c0504f059490062c0c0d15697494480c04000200c0720108920210244489a1012f30144c444414100846200110086c6b5508c049b3a8ce1adb2692925d102481908209694844baa8cc200b05709820853),(0x2221f7a951ae9b997d4bca8da32f39cced3e1f7f6d3f0d623d0566a2c1cb159da030c40088030048a8b02070458082001f16402800402540021cc4040106206820101415000100013810a5542c4ac38d4b85309019039008d9455655bd7d4e24,0x94664a12271c8d2072b39101005811cae004747c96ab009630bc99c6b003a9080990039c0040c00545810d010c0101800c690148c0100240e080080444d12c536528aae25a996383769a187a44ac3884b8110900103900090454055b97d4c20),(0xdaf2a83bfa492c7362f06e86ff545f489b40e7793b39fe60e71680e79ea9f8eda4c7003626448982070fd20c007f41164060071491239a0b18e0280a2c005114de492008510c18b0c16a5088d2102bb86b306659603572fc200909021b182d29,0x4003248100610810048843b810050200001180822062001042cb80530880001220881440890010c60422020002002326a0882000a85000401200010422081621020880250c2180a491410900901008804b206218602052bc0008000219080d28),(0x8db532a1e741154f2cf5293c5a52b0f2dbe398bcb5b3e6ab6ecfc7b73f20ef8cf108208900086231000004829a0008a9a00088406c944094200201e082618680012642620cc081020280022235a436c00708406151300db336e2c295e878d6d8,0x9000422249668018a000c0041c21004132000082008e1037332001089000101e2000cb40004c4540089a500b06006300000010211010021300896c80b0711042ae72db2445631e520d0294c2240426c0070800615130013334624280e0785688)]
def g507columns : IndexTree ColumnInfo := (IndexTree.fork 83 (IndexTree.fork 41 (IndexTree.fork 20 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(1,0,506,0,10),(8,0,499,0,10),(16,0,491,0,10),(32,0,475,0,10),(64,0,443,0,10)]) (IndexTree.leaf [(256,0,251,0,10),(0,1,362,144,9),(2,0,505,0,9),(0,8,179,320,9),(0,16,362,129,9)])) (IndexTree.fork 5 (IndexTree.leaf [(128,0,379,0,9),(0,256,211,40,9),(17,0,490,0,8),(1,16,362,128,8),(16,1,362,128,8)]) (IndexTree.leaf [(128,1,362,16,8),(72,0,435,0,8),(64,8,179,256,8),(264,0,243,0,8),(8,256,211,32,8)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(256,8,179,64,8),(128,16,362,1,8),(288,0,219,0,8),(32,256,211,8,8),(145,0,362,0,7)]) (IndexTree.leaf [(129,16,362,0,7),(144,1,362,0,7),(296,0,211,0,7),(40,256,211,0,7),(328,0,179,0,7)])) (IndexTree.fork 5 (IndexTree.leaf [(320,8,179,0,7),(0,32,217,258,8),(0,64,433,10,8),(9,0,498,0,7),(33,0,474,0,7)]) (IndexTree.leaf [(65,0,442,0,7),(129,0,362,0,7),(257,0,250,0,7),(34,0,473,0,7),(2,32,217,256,7),(66,0,441,0,7)])))) (IndexTree.fork 21 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(2,64,433,8,7),(24,0,483,0,7),(40,0,211,0,7),(0,40,145,322,7),(32,8,147,320,7)]) (IndexTree.leaf [(8,64,433,2,7),(48,0,459,0,7),(80,0,427,0,7),(144,0,362,0,7),(272,0,235,0,7)])) (IndexTree.fork 5 (IndexTree.leaf [(96,0,411,0,7),(0,96,145,266,7),(256,32,217,2,7),(320,0,179,0,7),(0,320,145,42,7)]) (IndexTree.leaf [(64,256,147,40,7),(2,40,145,320,6),(34,8,145,320,6),(74,0,433,0,6),(10,64,433,0,6),(98,0,409,0,6)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(2,96,145,264,6),(290,0,217,0,6),(258,32,217,0,6),(2,320,145,40,6),(66,256,145,40,6)]) (IndexTree.leaf [(8,96,145,258,6),(64,40,145,258,6),(72,32,145,258,6),(96,8,147,256,6),(256,40,145,66,6)])) (IndexTree.fork 5 (IndexTree.leaf [(288,8,147,64,6),(8,320,145,34,6),(72,256,147,32,6),(32,320,145,10,6),(96,256,147,8,6)]) (IndexTree.leaf [(256,96,145,10,6),(288,64,145,10,6),(0,128,360,19,7),(3,0,504,0,6),(2,1,360,144,6),(1,8,178,320,6)]))))) (IndexTree.fork 42 (IndexTree.fork 21 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(8,1,354,144,6),(32,1,330,144,6),(64,1,298,144,6),(1,128,360,18,6),(1,256,210,40,6)]) (IndexTree.leaf [(256,1,106,144,6),(10,0,433,0,6),(2,8,145,320,6),(18,0,489,0,6),(2,16,360,129,6)])) (IndexTree.fork 5 (IndexTree.leaf [(130,0,377,0,6),(2,128,360,17,6),(258,0,217,0,6),(2,256,145,40,6),(8,16,354,129,6)]) (IndexTree.leaf [(16,8,163,320,6),(8,32,145,258,6),(136,0,371,0,6),(32,16,330,129,6),(64,16,298,129,6),(16,128,360,3,6)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(16,256,195,40,6),(256,16,106,129,6),(32,64,145,10,6),(64,32,145,258,6),(160,0,347,0,6)]) (IndexTree.leaf [(192,0,315,0,6),(256,64,145,10,6),(384,0,123,0,6),(3,16,360,128,5),(18,1,360,128,5)])) (IndexTree.fork 5 (IndexTree.leaf [(3,128,360,16,5),(130,1,360,16,5),(25,0,482,0,5),(9,16,354,128,5),(24,1,354,128,5)]) (IndexTree.leaf [(73,0,434,0,5),(65,8,178,256,5),(136,1,354,16,5),(265,0,242,0,5),(9,256,210,32,5),(257,8,178,64,5)])))) (IndexTree.fork 21 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(49,0,458,0,5),(33,16,330,128,5),(48,1,330,128,5),(81,0,426,0,5),(65,16,298,128,5)]) (IndexTree.leaf [(80,1,298,128,5),(17,128,360,2,5),(273,0,234,0,5),(257,16,106,128,5),(272,1,106,128,5)])) (IndexTree.fork 5 (IndexTree.leaf [(160,1,330,16,5),(289,0,218,0,5),(33,256,210,8,5),(192,1,298,16,5),(384,1,106,16,5)]) (IndexTree.leaf [(10,32,145,256,5),(66,8,145,256,5),(10,256,145,32,5),(258,8,145,64,5),(18,128,360,1,5),(130,16,360,1,5)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(34,64,145,8,5),(66,32,145,256,5),(34,256,145,8,5),(258,64,145,8,5),(88,0,419,0,5)]) (IndexTree.leaf [(80,8,163,256,5),(136,16,354,1,5),(280,0,227,0,5),(24,256,195,32,5),(272,8,163,64,5)])) (IndexTree.fork 5 (IndexTree.leaf [(104,0,147,0,5),(40,64,145,2,5),(264,32,145,2,5),(264,64,145,2,5),(160,16,330,1,5)]) (IndexTree.leaf [(304,0,203,0,5),(48,256,195,8,5),(192,16,298,1,5),(384,16,106,1,5),(352,0,147,0,5),(320,32,145,2,5)]))))))
def g507autos : Array (List Nat) := #[[],[64],[101,131],[101,131,64]]
def g507levels : Nat → Packing
  | 8 => g507l8
  | 9 => g507l9
  | 10 => g507l10
  | 11 => g507l11
  | 12 => g507l12
  | _ => emptyPacking
def hashg507l9 (i : Nat) : Nat := 0x751d10000d1192708643160000000018a00000090e93602e84a580518000164c0000098e00025986c42a25e4d05da6add4600000048ec1a91f5d83c0011500000000697fad29f6022d00103b958005020000000020e517d25b0d1bf35858000014e30112240000
def hashg507l10 (i : Nat) : Nat := 0xe1dc4120007944847143049f8000000000000000007160000000348984880000004c86000347a000521783de00f00fc2e27088001d450000906800085000000000000000112a00038c89100d0200030600000c6a40edcb26391d3ca21c14c80b486c000787200624d73533525a4418ba000127a0000000225000000038a40003075141800000a943da40800102cf8eb0bf38b0815580649c420c64300000003d500000000c2b723c000000081f80010bd1caf856f2f270e69260002104000213490244e708bf42f14eba4e048585b2a6e45b8058001aaa14810b800000000001c2050e2c4f35080003ce0e529b59f0702e983e8008f45d81de2bb116711f149517d02e0900000a23d8a822a8000b231ca712dac6862e6b3a12d000081eb8c6256295461598f810a500c0002c9251c2b4703532dfb138a6f0c2690e81c593b085403600f0000c33e0b4a90e12470df89c884505943d20b7c4d8000000780203ce24d69290c5809ba6b2138001ab2c230651d48a142f47800029140006c6453f753143800000000000a544062000425204bcc052af00010bc000149e10e80005030c2678d000488cc410000000000000004932c348000936f089632800000018960001a4800068c200000014b70c856088c4d037b8bc00000000001ca400070fc0000001f53d014000186e00038420004119017e268c043a460007a01d15684a80e14ac00068858359893c1300000000000000000121a8000000789a000000000000340000a7c0004251312093ff3de4ff206820b414f8c143c2283d0934820006079c47f0a20000000000145c0004ada000000153aa0d800000000000000b0040ff943000000060dc8b9ecaa6992849b243ca9b372a9e420d0240000001abbf906000710800052660000000b05b40c0003a45d14000064692a40007a05211f06922804742005c3e0000000000688da53989e74b80000000000c9d8000000000000000000002d398bb0000000000000048bf414292c000100a000748e547228a61f4820000000000074f80005a0ee8f800013500016368000000281e00000000000000000426cd438d4b042800084c2865b44c500c39805d029908a00012e4050b833c9cf91200078ee00012c7819a8280007156000000000000012112a7562408048400000854bcd164a000000072ea0000001cae520704e1a543038001a3b000131d8000ed00c00784205004510c3502004b00004082102c020b41d3044700d221a0a000c3031000281670002a12503081c0024200040150c803ac6500c0130043011c809c010990008001
def hashg507l11 (i : Nat) : Nat := 0x4874e597142c24145f476786a64729b427989348640001f1d805000074e0000084ac0480f386df09b512000367ec0cd04d000060151852810000c510000d1d000220dd0c083d59bd63eb880000b09526644d800ab108000000111b0198000b06180bb8a800094af01e000000000000000003039000204369ee962201be5e5067a2cd17287d3169e6815ad1630002081089c00000000000000e3331d4000a149e750003837e070c15a916831f0fc00091bd0026115853f08381739500002582862c8b80000002c680002a2ff5b400029d0000a0480009404000418ce34a9e36480001e1b9578000010400008900000000e6c0000000113843e993051161ed00d401c860000000048ac0000002a050002a09000351e646b539000348200000005994000e1c00000000000917a00e0001c83e1e0c550003d1368a04484088000000390eb177e1500000000001480985c87fa5be071f160000a13c000e08c0000003e7d49480000000000315800001a4000297186ed40e86af0da273600701fc82a71bb913500e80fc1bc1d085498c00007101c216118000549c000e980c3b084000000000000000c4cd1b3811819cc0988e0029000000000000000000000000000031e8c1a61269160000000b8e800030b0000f197d70c04347c10aa0320128213d8d4680509f013193c241000000068c40000000000f4125710000000b57ca6eb1df85bc45112ae11d07e50b800098f1879916625510b4e160001d6e000221f000000004a40002885e3d0003c2f0000873f97d444a002803090800080d000094d40000002c5f000254b499f96c0003d18000063990ac000d83c072f021c0c781bc05c03d01d000000000025190001c1600000002984000000000011ac0000000000915dc3a38dda77658644bb0a0a76745643550e00001000018801110050918008420198a05804d28509008000814e100000a08000c000c062290230042120001234671904210446284e1
def hashg507l12 (i : Nat) : Nat := 0xb0945aa8b41411883919ccc1400187615718a400040d035d4800000000004a6105d52c026804a000a5e8900073f4a8001860000041241db440048300080400794c1143da60002260000050c8a0000000000051841001060
def g507index : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 16 71 4 11 5 2 (hashg507l9)
  | 10 => lookupWord 111 497 5 14 8 2 (hashg507l10)
  | 11 => lookupWord 84 378 5 14 8 2 (hashg507l11)
  | 12 => lookupWord 13 59 4 11 5 2 (hashg507l12)
  | _ => fun _ => none
def g507 : Forest := ⟨507,12,fun j => g507samples[j]?.getD (0,0),g507columns,g507autos,g507levels,g507index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom507 : graphValid g507 (boundsBefore known379) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s507_8_0 : block g507 8 0 24=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all507_8 : block g507 8 0 24=true := s507_8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s507_9_0 : block g507 9 0 30=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s507_9_30 : block g507 9 30 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s507_9_62 : block g507 9 62 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s507_9_94 : block g507 9 94 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s507_9_126 : block g507 9 126 30=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s507_9_156 : block g507 9 156 18=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all507_9 : block g507 9 0 174=true := (@block_merge g507 9 0 126 48 (@block_merge g507 9 0 62 64 (@block_merge g507 9 0 30 32 s507_9_0 s507_9_30) (@block_merge g507 9 62 32 32 s507_9_62 s507_9_94)) (@block_merge g507 9 126 30 18 s507_9_126 s507_9_156))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s507_10_0 : block g507 10 0 17=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s507_10_17 : block g507 10 17 32=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s507_10_49 : block g507 10 49 32=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s507_10_81 : block g507 10 81 13=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s507_10_94 : block g507 10 94 32=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s507_10_126 : block g507 10 126 6=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all507_10 : block g507 10 0 132=true := (@block_merge g507 10 0 94 38 (@block_merge g507 10 0 49 45 (@block_merge g507 10 0 17 32 s507_10_0 s507_10_17) (@block_merge g507 10 49 32 13 s507_10_49 s507_10_81)) (@block_merge g507 10 94 32 6 s507_10_94 s507_10_126))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s507_11_0 : block g507 11 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s507_11_5 : block g507 11 5 17=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all507_11 : block g507 11 0 22=true := (@block_merge g507 11 0 5 17 s507_11_0 s507_11_5)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s507_12_0 : block g507 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all507_12 : block g507 12 0 1=true := s507_12_0
theorem tables507 : checkedTables g507 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g507 0 0 0 = true)
  · exact (rfl : block g507 1 0 0 = true)
  · exact (rfl : block g507 2 0 0 = true)
  · exact (rfl : block g507 3 0 0 = true)
  · exact (rfl : block g507 4 0 0 = true)
  · exact (rfl : block g507 5 0 0 = true)
  · exact (rfl : block g507 6 0 0 = true)
  · exact (rfl : block g507 7 0 0 = true)
  · exact all507_8
  · exact all507_9
  · exact all507_10
  · exact all507_11
  · exact all507_12

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low507 : Lower (vars 507) (graphGoal 507) 13 := lower_forest (g:=g507) (i:=0) (hints:=12902752340) (before_sound known379 valid379) geom507 tables507 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps507 : List (Nat × List Nat) := [(507,[])]
def known507 := extendKnown known379 13 maps507
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid507 : Known known507 := extendKnown_ok valid379 low507 (by decide +kernel)
def g437d6 (i : Nat) : Nat := 0xfc821800
def g437l6 : Packing := (1,2,8,0,0,0,0,g437d6)
def g437d7 (i : Nat) : Nat := 0x180fe800
def g437l7 : Packing := (1,1,8,0,3,0,0,g437d7)
def g437d8 (i : Nat) : Nat := 0x3818e8c13f
def g437l8 : Packing := (1,0,8,0,5,0,0,g437d8)
def g437samples : Array (Bits × Bits) := #[(0xfbf1d52ffa85bbeee3dd2fbfb1018db7fbd5ff29c35ea6f1cfe3ba2aa4f7d75dbc7c69b3eda8fb19b18e7befff2bb55473a676ff1cf4f391cdf31f12d76c6b5f2cb29366efff27976fe7bbd1db7a4e7468136400160a18958d2c3ee692820cb6,0x80110b4d000204abaa65008080002004212200145a88f8a02a044108084109041b80c9030e2800250141470e5094081a0100284162820400005015e449b4201300b060129641202406024002110021818004012a1320196102722ee680000c22),(0x0,0x0),(0x4556cdfe4c1fa85ba63bd446ba7fbfdd9c96a2fef07b5f9d5c3f4dfde9467f39db7ef3af787b63f45a1a7eeddcbd6ab80d6fcdffb7af8ea8fa3fbbabf3c18fe69366bbedf67bf7e2996bb05b14dafff8910c12f5e96145002012e0936b548d64,0x14914805c0c812005084c0224d800d484941260008c0d4840005a00011004530a480804090584200c107054401880b400889109c2d000024ca1a54280340fa08001046010220068c4020050538a2a0100082480656c60492421260826a108164),(0x0,0x0),(0xadfe6f48bb725eef7c749affff5ddf7c795c4ff83f103fb532c5db47137bbe6458edfdd9c3b60bf6eff1f15daa6cbbd7e31cb986fbfcf7a23ce4fd5f372757af75377cf5bb82f5fe94b8efed588d75b64c838108140cb01e0ae8dd4a2332e289,0x2a0c440023e48800419a0c5413c0910b901022400102060d4000944322a440a8601800d0000210180002100084402064e8610780182128486d02e010900180cc9a490f05080e0652000401200660c2000300140148db6012148cd1000312a289),(0xf063b8de876b8385d9db4d5368f9bb3b47fbaf5b3ceadad77724cfd97fdb63ef2effbf154ff3dd0fd74d707647b7d6cfbd5335ddd57b79f7fb7b777daafb3020e2f904aeddd6e9b9f73e757a7e37d871126418e7c890036070112a341569b9c9,0xc108a1280011c59209103a0120428230342280817408007b290010068a601a48401a52ac00a0202a10200032a404a09a1702832180543a000020288144240040044898203414007010082840854c02800c180028a918724d0104083411683881),(0x0,0x0),(0x8bad8afd6efc7e97d2fea1a597c249e82e7e78e51bede77bacdfbfbd32a998eeb7f675d276cff40e7afc947a33e2742bb5b3dfece5822fff5775159ffd93d7f99ffdeff326ef7e74fbf4bcafb9d4acc22490e5080206a88b87c4411cb8a55277,0x45e21010100002141000232144000a50408585820441014085c108840412a640040032282051afc01434a821082253800490401a014c108210ad020b04421b204502802860a0408028710098681c1c1010410214a404868ce901001838a55054),(0x175a766f3bf6f7be6f2dff3d6fe76f6af4e7fb1ee6bde6dfdf9c3c7fee1d2b9bedc99e6cd17dd7e7e56bcfab5950e9365ede4a5d8aa35bdd26cfe9fe3f3fbe745bb8c23d50be98f98345cfafb72fa30983680a1221f14660500382e1cc1f7618,0x280214d03a040044a2430584120c3081829c197c02100b0000500b30608000011a600d102a0509502088288808231024804028401228444130450344801b05a24a06019a81018800825402a2020108604000a09100218920bce9824184074618)]
def g437columns : IndexTree ColumnInfo := (IndexTree.fork 91 (IndexTree.fork 45 (IndexTree.fork 22 (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(1,0,436,0,6),(0,1,292,144,6),(4,0,433,0,6),(0,4,145,288,6),(16,0,421,0,6)]) (IndexTree.leaf [(0,16,292,129,6),(32,0,405,0,6),(0,32,145,260,6),(128,0,309,0,6),(0,128,292,17,6),(256,0,181,0,6)])) (IndexTree.fork 5 (IndexTree.leaf [(0,256,145,36,6),(1,16,292,128,5),(16,1,292,128,5),(1,128,292,16,5),(128,1,292,16,5)]) (IndexTree.leaf [(4,32,145,256,5),(32,4,145,256,5),(4,256,145,32,5),(256,4,145,32,5),(16,128,292,1,5),(128,16,292,1,5)]))) (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(32,256,145,4,5),(256,32,145,4,5),(145,0,292,0,4),(17,128,292,0,4),(129,16,292,0,4)]) (IndexTree.leaf [(144,1,292,0,4),(292,0,145,0,4),(36,256,145,0,4),(260,32,145,0,4),(288,4,145,0,4),(17,0,292,0,4)])) (IndexTree.fork 6 (IndexTree.leaf [(129,0,292,0,4),(36,0,145,0,4),(260,0,145,0,4),(144,0,292,0,4),(288,0,145,0,4),(5,0,432,0,3)]) (IndexTree.leaf [(0,5,0,432,3),(1,4,144,288,3),(4,1,288,144,3),(33,0,404,0,3),(0,33,0,404,3),(1,32,144,260,3)])))) (IndexTree.fork 23 (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(32,1,260,144,3),(257,0,180,0,3),(0,257,0,180,3),(1,256,144,36,3),(256,1,36,144,3)]) (IndexTree.leaf [(20,0,417,0,3),(0,20,0,417,3),(4,16,288,129,3),(16,4,129,288,3),(132,0,305,0,3),(0,132,0,305,3)])) (IndexTree.fork 6 (IndexTree.leaf [(4,128,288,17,3),(128,4,17,288,3),(48,0,389,0,3),(0,48,0,389,3),(16,32,129,260,3),(32,16,260,129,3)]) (IndexTree.leaf [(272,0,165,0,3),(0,272,0,165,3),(16,256,129,36,3),(256,16,36,129,3),(160,0,277,0,3),(0,160,0,277,3)]))) (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(32,128,260,17,3),(128,32,17,260,3),(384,0,53,0,3),(0,384,0,53,3),(128,256,17,36,3)]) (IndexTree.leaf [(256,128,36,17,3),(1,20,0,416,2),(5,16,288,128,2),(16,5,0,416,2),(20,1,288,128,2),(4,33,0,400,2)])) (IndexTree.fork 6 (IndexTree.leaf [(5,32,144,256,2),(32,5,0,400,2),(33,4,144,256,2),(1,132,0,304,2),(5,128,288,16,2),(128,5,0,304,2)]) (IndexTree.leaf [(132,1,288,16,2),(4,257,0,176,2),(5,256,144,32,2),(256,5,0,176,2),(257,4,144,32,2),(1,48,0,388,2)]))))) (IndexTree.fork 45 (IndexTree.fork 22 (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(16,33,0,388,2),(33,16,260,128,2),(48,1,260,128,2),(1,272,0,164,2),(16,257,0,164,2)]) (IndexTree.leaf [(257,16,36,128,2),(272,1,36,128,2),(1,160,0,276,2),(33,128,260,16,2),(128,33,0,276,2),(160,1,260,16,2)])) (IndexTree.fork 5 (IndexTree.leaf [(32,257,0,148,2),(33,256,144,4,2),(256,33,0,148,2),(257,32,144,4,2),(1,384,0,52,2)]) (IndexTree.leaf [(128,257,0,52,2),(257,128,36,16,2),(384,1,36,16,2),(4,48,0,385,2),(20,32,129,256,2),(32,20,0,385,2)]))) (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(48,4,129,256,2),(16,132,0,289,2),(20,128,288,1,2),(128,20,0,289,2),(132,16,288,1,2)]) (IndexTree.leaf [(4,272,0,161,2),(20,256,129,32,2),(256,20,0,161,2),(272,4,129,32,2),(4,160,0,273,2),(32,132,0,273,2)])) (IndexTree.fork 6 (IndexTree.leaf [(132,32,17,256,2),(160,4,17,256,2),(4,384,0,49,2),(132,256,17,32,2),(256,132,0,49,2),(384,4,17,32,2)]) (IndexTree.leaf [(16,160,0,261,2),(48,128,260,1,2),(128,48,0,261,2),(160,16,260,1,2),(32,272,0,133,2),(48,256,129,4,2)])))) (IndexTree.fork 23 (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(256,48,0,133,2),(272,32,129,4,2),(16,384,0,37,2),(128,272,0,37,2),(272,128,36,1,2)]) (IndexTree.leaf [(384,16,36,1,2),(32,384,0,21,2),(160,256,17,4,2),(256,160,0,21,2),(384,32,17,4,2),(21,0,288,0,1)])) (IndexTree.fork 6 (IndexTree.leaf [(17,4,0,288,1),(37,0,144,0,1),(36,1,0,144,1),(133,0,288,0,1),(129,4,0,288,1),(261,0,144,0,1)]) (IndexTree.leaf [(260,1,0,144,1),(49,0,260,0,1),(17,32,0,260,1),(273,0,36,0,1),(17,256,0,36,1),(161,0,260,0,1)]))) (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(129,32,0,260,1),(289,0,144,0,1),(288,1,0,144,1),(385,0,36,0,1),(129,256,0,36,1)]) (IndexTree.leaf [(52,0,129,0,1),(36,16,0,129,1),(148,0,288,0,1),(144,4,0,288,1),(276,0,129,0,1),(260,16,0,129,1)])) (IndexTree.fork 6 (IndexTree.leaf [(164,0,17,0,1),(36,128,0,17,1),(388,0,17,0,1),(260,128,0,17,1),(176,0,260,0,1),(144,32,0,260,1)]) (IndexTree.leaf [(304,0,129,0,1),(288,16,0,129,1),(400,0,36,0,1),(144,256,0,36,1),(416,0,17,0,1),(288,128,0,17,1)]))))))
def g437autos : Array (List Nat) := #[[],[116],[133],[133,116],[82],[116,82],[130,82],[130,116,82],[82,130],[82,116,130],[130],[116,130],[135,84,32],[117,84,132,32],[132,116,84,32],[117,132,32],[135,80,64,32],[117,80,128,64,32],[128,112,80,64,32],[117,128,64,32],[132,64,84,112,32],[80,132,112,32],[128,84,112,32],[80,84,132,112,32],[64],[112,64],[133,64],[133,112,64],[82,64],[112,82,64],[130,82,64],[130,112,82,64],[82,130,64],[82,112,130,64],[130,64],[112,130,64],[135,66,32,80],[114,66,132,32,80],[132,116,66,32,80],[114,132,32,80],[135,66,80],[114,130,66,80],[128,112,66,80],[32,112,130,66,80],[132,66,114,80],[132,114,80],[128,64,66,114,80],[64,132,114,80],[64,112],[112],[133,64,112],[133,112],[64,82,112],[82,112],[130,64,82,112],[130,82,112],[82,64,130,112],[82,130,112],[64,130,112],[130,112],[117,84,66,32,128],[114,84,32,128],[117,66,32,128],[66,116,84,32,128],[117,80,66,128],[114,32,82,66,128],[117,66,128],[114,82,66,128],[84,80,66,114,128],[64,84,114,128],[84,66,114,128],[84,114,128]]
def g437levels : Nat → Packing
  | 6 => g437l6
  | 7 => g437l7
  | 8 => g437l8
  | _ => emptyPacking
def hashg437l7 (i : Nat) : Nat := 0x5be70
def hashg437l8 (i : Nat) : Nat := 0x53000108c0000059003ca
def g437index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 6 0 7 0 3 (hashg437l7)
  | 8 => lookupWord 2 9 1 9 0 5 (hashg437l8)
  | _ => fun _ => none
def g437 : Forest := ⟨437,8,fun j => g437samples[j]?.getD (0,0),g437columns,g437autos,g437levels,g437index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom437 : graphValid g437 (boundsBefore known507) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,listPieces_all (d:=6) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s437_6_0 : block g437 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all437_6 : block g437 6 0 1=true := s437_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s437_7_0 : block g437 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all437_7 : block g437 7 0 1=true := s437_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s437_8_0 : block g437 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all437_8 : block g437 8 0 1=true := s437_8_0
theorem tables437 : checkedTables g437 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g437 0 0 0 = true)
  · exact (rfl : block g437 1 0 0 = true)
  · exact (rfl : block g437 2 0 0 = true)
  · exact (rfl : block g437 3 0 0 = true)
  · exact (rfl : block g437 4 0 0 = true)
  · exact (rfl : block g437 5 0 0 = true)
  · exact all437_6
  · exact all437_7
  · exact all437_8

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low437 : Lower (vars 437) (graphGoal 437) 9 := lower_forest (g:=g437) (i:=0) (hints:=8592033028) (before_sound known507 valid507) geom437 tables437 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps437 : List (Nat × List Nat) := [(437,[])]
def known437 := extendKnown known507 9 maps437
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid437 : Known known437 := extendKnown_ok valid507 low437 (by decide +kernel)
def g439d7 (i : Nat) : Nat := 0x28f3a296212003ea884842800
def g439l7 : Packing := (2,3,8,0,0,3,0,g439d7)
def g439d8 (i : Nat) : Nat := 0x2c0a101603c0630ac07412032400141430005060e00181700140b800906817001f866d048c139b22a9e11807fe296213ff108941ff4824a0f7c52c427bd282213fd109001fe482800e7c52c4277a296003dd109001fa842800
def g439l8 : Packing := (11,2,8,1,3,8,0,g439d8)
def g439d9 (i : Nat) : Nat := 0x231c8a48241b8a8705128bc603830ac504130bc5c3030c05c312c16003a17942813834000a586bb59aa4421906400ff4a4ff0a4ff884ff4a0ff480ff440ef884fe800
def g439l9 : Packing := (8,1,8,4,3,9,0,g439d9)
def g439d10 (i : Nat) : Nat := 0x605001ff
def g439l10 : Packing := (1,0,8,3,3,0,0,g439d10)
def g439samples : Array (Bits × Bits) := #[(0xdd59036d7395adc7ea1558e4637ea6f7541c40506a7ebeebc5dd94fa9e74a237ba3da9f4d662bc1a9a0da49583fa5cc80d77792ff56c15f9ad774a3756ac105e0694500040500122080b231084142c000419ba40c019431dcc662d1720c154e1,0xd9262a1da80018a858a42889a98c0004234a020f7e01088d8e3c02219058162c30e580216331000cb12000c081816300820150be0972a230201684e59180a524d000a0c88338006089014605406042dc9c108770a2114215c8662d1500c14040),(0xa1517950607edf9289bcd6d8a89718af3f641ff73b4978bde45c86536a0cfdfdf655441dcd2dd17666eb706fa129c28742f6cba2f3d83f4c474ff77ea95002006000022683281a9d875008002249d21000a6040a2103721617835f109ca85d0a,0xccb721ad2d1a81900ab170880abb1038a55b2208221a2a70d6204b600e81dd2c48b5c403111026840d68418128df50292d0ab8a84b969624109e048628df90c7a57c0900110960cc084808cbc3209b9a9d41b6503f03521416835c109c88550a),(0xcbf33ee7cb854b7c021f6667d495cf7c5cefa7ceeeb7b5e7948a568bfe91c8efdbe646072ffb0ff83a3109dab0cfd69b5bb5a2a8cdfaeb3ebfe2fcebc5eee400996380893880440030a004c84982008f804000b104d778d06e1f8090c14e20ea,0x81a20868006893a001c020040ca29011262c00265210a80328b4a20000ec806080326901db0d8400e40006810662b83ff0da32001109d244c4064aa636d66132222400a6fc13232080408420039c189259218215280720906e068010c14a20aa),(0x0,0x0),(0xf2afe7327ff873df7ff66fef9356afb9bf167b92ddfb18f1bf5b6b9e4fa6f7bbbc5b7067f94ef2d327dee78a5e4b7964f3f36e5138e76e176fb78f54dddb40ea028031004006a060080c33268004200031095b4492240d8a068198d78adb9734,0x241015404092e700811312620610b01844a0a42001ec064241008cc20b80801249003e0a004810f00cd83106202494a0052c0a00a40c10cb00803202001308900258060528001605242e89700300b923014330825d200d8a068190c2880a9534),(0x37f6a69e9667abba6ed13fd7fb86fadfefbfedead47b65159f294bef56bb38f184c4d5b4f9bc670eebf7f7efede5dd398fef861bebb986cb3b1f12368390ef01c14a0e5a1f810e80f640cc091b6181f4cae2048108888037e1d051ee441ec852,0x2200560012800440a00086002000208218000041006145040000000900000001050000c400c2002300029010900002800200050000202082224011110000000800010000004080100000000018416465001249aac0680002815001ee00148840),(0x0,0x0),(0x3c03dffda6ac9fcdf3eeb359ed78fe89df6bb07be334db6aff67f97bf1fb2d4c5f2b7fbb22790ddf17dc8e543db768473d5a19f6e64656b56c3bedb939afb0b424146124807eb15f0117103624185e003514e10e732d26e0bb3026483b30038d,0x2404002024400030400851040000543180441000000400000823010200020c0040000048802480102040e101400084410000000100001000d400810040002000880000000000000500000001c9f040062ac480d00cc20602110020823300281),(0x882c93b849176d233ca3aad1c7efddef6a96769f868a6bb22ba2e74d61f6fe77cd919effb6cd4065f0081b20db1dffbcf61ad4c471cdedf696d898df3af1690118298cd12401400040a0c0c150a2016b4a0000300c52d961106fde288901e615,0x5444a08460036801022250cb10100060c143f6088c020270d10914f64e003898504c80320410605c095d6068281444000825c8bb0e960c2110b920084120044014002c400284408b2735231a04228308a6cc34401790d96110295e0008014615)]
def g439columns : IndexTree ColumnInfo := (IndexTree.fork 108 (IndexTree.fork 54 (IndexTree.fork 27 (IndexTree.fork 13 (IndexTree.fork 6 (IndexTree.leaf [(2,0,437,0,9),(1,0,438,0,8),(4,0,435,0,8),(16,0,423,0,8),(256,0,183,0,8),(17,0,422,0,7)]) (IndexTree.leaf [(260,0,179,0,7),(0,1,294,144,7),(0,4,147,288,7),(0,16,294,129,7),(32,0,407,0,7),(0,32,145,262,7),(128,0,311,0,7)])) (IndexTree.fork 7 (IndexTree.leaf [(0,128,292,19,7),(0,256,147,36,7),(3,0,436,0,6),(2,1,292,144,6),(1,16,294,128,6),(16,1,294,128,6),(1,128,292,18,6)]) (IndexTree.leaf [(128,1,294,16,6),(6,0,433,0,6),(2,4,145,288,6),(18,0,421,0,6),(2,16,292,129,6),(34,0,405,0,6),(2,32,145,260,6)]))) (IndexTree.fork 13 (IndexTree.fork 6 (IndexTree.leaf [(130,0,309,0,6),(2,128,292,17,6),(258,0,181,0,6),(2,256,145,36,6),(4,32,145,258,6),(32,4,147,256,6)]) (IndexTree.leaf [(4,256,147,32,6),(256,4,147,32,6),(16,128,292,3,6),(128,16,294,1,6),(32,256,147,4,6),(256,32,145,6,6),(3,16,292,128,5)])) (IndexTree.fork 7 (IndexTree.leaf [(18,1,292,128,5),(3,128,292,16,5),(130,1,292,16,5),(145,0,294,0,5),(17,128,292,2,5),(129,16,294,0,5),(144,1,294,0,5)]) (IndexTree.leaf [(6,32,145,256,5),(34,4,145,256,5),(6,256,145,32,5),(258,4,145,32,5),(18,128,292,1,5),(130,16,292,1,5),(34,256,145,4,5)])))) (IndexTree.fork 27 (IndexTree.fork 13 (IndexTree.fork 6 (IndexTree.leaf [(258,32,145,4,5),(292,0,147,0,5),(36,256,147,0,5),(260,32,145,2,5),(288,4,147,0,5),(5,0,434,0,5)]) (IndexTree.leaf [(129,0,294,0,5),(257,0,182,0,5),(20,0,419,0,5),(36,0,147,0,5),(144,0,294,0,5),(272,0,167,0,5),(288,0,147,0,5)])) (IndexTree.fork 7 (IndexTree.leaf [(19,0,292,0,4),(131,0,292,0,4),(21,0,418,0,4),(261,0,178,0,4),(273,0,166,0,4),(38,0,145,0,4),(262,0,145,0,4)]) (IndexTree.leaf [(146,0,292,0,4),(290,0,145,0,4),(276,0,163,0,4),(0,2,277,160,5),(0,3,260,176,4),(1,4,146,288,4),(4,1,290,144,4)]))) (IndexTree.fork 13 (IndexTree.fork 6 (IndexTree.leaf [(33,0,406,0,4),(0,33,0,406,4),(1,32,144,262,4),(1,256,146,36,4),(256,1,38,144,4),(0,6,17,416,4)]) (IndexTree.leaf [(0,18,260,161,4),(32,2,277,128,4),(128,2,277,32,4),(0,258,17,164,4),(4,16,290,129,4),(16,4,131,288,4),(132,0,307,0,4)])) (IndexTree.fork 7 (IndexTree.leaf [(0,132,0,307,4),(4,128,288,19,4),(48,0,391,0,4),(0,48,0,391,4),(16,32,129,262,4),(16,256,131,36,4),(256,16,38,129,4)]) (IndexTree.leaf [(0,160,0,279,4),(32,128,260,19,4),(128,32,17,262,4),(384,0,55,0,4),(0,384,0,55,4),(256,128,36,19,4),(7,0,432,0,3)]))))) (IndexTree.fork 54 (IndexTree.fork 27 (IndexTree.fork 13 (IndexTree.fork 6 (IndexTree.leaf [(0,7,0,432,3),(2,5,0,432,3),(3,4,144,288,3),(6,1,288,144,3),(1,18,260,160,3),(16,3,260,160,3)]) (IndexTree.leaf [(17,2,260,160,3),(35,0,404,0,3),(2,33,0,404,3),(3,32,144,260,3),(32,3,260,144,3),(34,1,260,144,3),(128,3,260,48,3)])) (IndexTree.fork 7 (IndexTree.leaf [(259,0,180,0,3),(0,259,0,180,3),(2,257,0,180,3),(3,256,144,36,3),(258,1,36,144,3),(5,16,290,128,3),(17,4,130,288,3)]) (IndexTree.leaf [(20,1,290,128,3),(4,33,0,402,3),(5,32,144,258,3),(33,4,146,256,3),(1,132,0,306,3),(5,128,288,18,3),(132,1,290,16,3)]))) (IndexTree.fork 13 (IndexTree.fork 6 (IndexTree.leaf [(5,256,146,32,3),(257,4,146,32,3),(260,1,34,144,3),(49,0,390,0,3),(1,48,0,390,3),(16,33,0,390,3)]) (IndexTree.leaf [(17,256,130,36,3),(257,16,38,128,3),(272,1,38,128,3),(1,160,0,278,3),(33,128,260,18,3),(128,33,0,278,3),(33,256,146,4,3)])) (IndexTree.fork 7 (IndexTree.leaf [(256,33,0,150,3),(257,32,144,6,3),(1,384,0,54,3),(257,128,36,18,3),(384,1,38,16,3),(22,0,417,0,3),(0,22,0,417,3)]) (IndexTree.leaf [(2,20,0,417,3),(6,16,288,129,3),(18,4,129,288,3),(32,6,17,384,3),(134,0,305,0,3),(2,132,0,305,3),(6,128,288,17,3)])))) (IndexTree.fork 27 (IndexTree.fork 13 (IndexTree.fork 6 (IndexTree.leaf [(128,6,17,288,3),(130,4,17,288,3),(4,258,17,160,3),(256,6,17,160,3),(260,2,17,160,3),(50,0,389,0,3)]) (IndexTree.leaf [(2,48,0,389,3),(18,32,129,260,3),(32,18,260,129,3),(34,16,260,129,3),(128,18,260,33,3),(274,0,165,0,3),(0,274,0,165,3)])) (IndexTree.fork 7 (IndexTree.leaf [(2,272,0,165,3),(18,256,129,36,3),(258,16,36,129,3),(162,0,277,0,3),(2,160,0,277,3),(34,128,260,17,3),(130,32,17,260,3)]) (IndexTree.leaf [(160,2,277,0,3),(32,258,17,132,3),(386,0,53,0,3),(2,384,0,53,3),(128,258,17,36,3),(130,256,17,36,3),(258,128,36,17,3)]))) (IndexTree.fork 13 (IndexTree.fork 6 (IndexTree.leaf [(4,48,0,387,3),(20,32,129,258,3),(48,4,131,256,3),(16,132,0,291,3),(20,128,288,3,3),(132,16,290,1,3)]) (IndexTree.leaf [(20,256,131,32,3),(260,16,34,129,3),(272,4,131,32,3),(4,160,0,275,3),(32,132,0,275,3),(132,32,17,258,3),(388,0,51,0,3)])) (IndexTree.fork 7 (IndexTree.leaf [(4,384,0,51,3),(256,132,0,51,3),(16,160,0,263,3),(48,128,260,3,3),(128,48,0,263,3),(48,256,131,4,3),(256,48,0,135,3)]) (IndexTree.leaf [(272,32,129,6,3),(16,384,0,39,3),(272,128,36,3,3),(384,16,38,1,3),(32,384,0,23,3),(256,160,0,23,3),(384,32,17,6,3)]))))))
def g439autos : Array (List Nat) := #[[],[130],[117,132,32],[117,128,64,32],[64],[130,64],[117,66,32,128],[117,66,128]]
def g439levels : Nat → Packing
  | 7 => g439l7
  | 8 => g439l8
  | 9 => g439l9
  | 10 => g439l10
  | _ => emptyPacking
def hashg439l8 (i : Nat) : Nat := 0x3a9ab81736d6f443c
def hashg439l9 (i : Nat) : Nat := 0x180140a98a058d00022200030400304207c1c00685a49314c3000a4ec280000008c002c4a08001e4000414892000003320000000040cb040
def hashg439l10 (i : Nat) : Nat := 0x118dc001230000071c000000000000162d458a410010300000f0000b9000a140062800480ea36f11c0a90a1093003150001c7002
def g439index : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 3 12 3 8 1 3 (hashg439l8)
  | 9 => lookupWord 9 39 3 11 4 3 (hashg439l9)
  | 10 => lookupWord 9 38 4 10 3 3 (hashg439l10)
  | _ => fun _ => none
def g439 : Forest := ⟨439,10,fun j => g439samples[j]?.getD (0,0),g439columns,g439autos,g439levels,g439index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom439 : graphValid g439 (boundsBefore known437) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s439_7_0 : block g439 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all439_7 : block g439 7 0 2=true := s439_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s439_8_0 : block g439 8 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s439_8_4 : block g439 8 4 4=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s439_8_8 : block g439 8 8 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all439_8 : block g439 8 0 11=true := (@block_merge g439 8 0 8 3 (@block_merge g439 8 0 4 4 s439_8_0 s439_8_4) s439_8_8)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s439_9_0 : block g439 9 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s439_9_2 : block g439 9 2 6=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all439_9 : block g439 9 0 8=true := (@block_merge g439 9 0 2 6 s439_9_0 s439_9_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s439_10_0 : block g439 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all439_10 : block g439 10 0 1=true := s439_10_0
theorem tables439 : checkedTables g439 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g439 0 0 0 = true)
  · exact (rfl : block g439 1 0 0 = true)
  · exact (rfl : block g439 2 0 0 = true)
  · exact (rfl : block g439 3 0 0 = true)
  · exact (rfl : block g439 4 0 0 = true)
  · exact (rfl : block g439 5 0 0 = true)
  · exact (rfl : block g439 6 0 0 = true)
  · exact all439_7
  · exact all439_8
  · exact all439_9
  · exact all439_10

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low439 : Lower (vars 439) (graphGoal 439) 11 := lower_forest (g:=g439) (i:=0) (hints:=8590984532) (before_sound known437 valid437) geom439 tables439 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps439 : List (Nat × List Nat) := [(439,[])]
def known439 := extendKnown known437 11 maps439
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid439 : Known known439 := extendKnown_ok valid437 low439 (by decide +kernel)
def g375 : Forest := ⟨375,8,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low375 : Lower (vars 375) (graphGoal 375) 9 := lower_discard (g:=g375) (ci:=(0,1,358,16,8)) (hints:=8607761748) (before_sound known439 valid439) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps375 : List (Nat × List Nat) := [(471,[117,132,32]),(375,[]),(508,[133,64,16,113,48]),(493,[133,116,49]),(381,[133,49])]
def known375 := extendKnown known439 9 maps375
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid375 : Known known375 := extendKnown_ok valid439 low375 (by decide +kernel)
def g503d8 (i : Nat) : Nat := 0x3cdf2b688de6543ca140d8f1288c64c5884f8e8c68844a4800bce1494c5884800fc68844a4863800faa8c6884842800fca4c5884842800f728e7863842800fd24a4863842800fe2884863842800fac8c6884821800fe4884863821800fe8884842821800ff0863842821800
def g503l8 : Packing := (13,4,8,0,0,6,0,g503d8)
def g503d9 (i : Nat) : Nat := 0x1e838101e606098603d808261d040d070d000b040d070d070d000835c0826070004c042c00381d80098185808580058105828583b001300084ca082604160b0004c1d800980058105828583b0013000b040b0760026081a0ec004c082060a10d22d8488c3711a0c824488842b888f50716060a1ea0e224341c487b80090f307141e60e283dc004485838890f00121ee00243d41e830e83d06121ea0e2a0e19b72d647c7f8df17e27c3f85f07e023e97b2f25d739e71cdf9b735e686ccd8c3085dab49612b2544a1d3ba674988f110a114187f0eb1a53145bcaf944252438798d817a2884386c08c0ac08000dff18d210903bfd3024212077fa30484240faf8c64c4884bdf252983109ebe319306213f72624424005fe929481800fdc988903001fba211206003e7c634422527cf4c08844a4f9e8c1108949ebc4a231a213f6c63442410fed4c0884821fda8c1109043efa21231a003df2714634007be4828c6800f7c90318d001ef910631a003ef442262c007de4e24c5800fbc90498b001fb9306212003fb442431c007f64e2863800fec9050c7001fd920618e003fb220c31c007fa4c4842800ff4903085001ff1312086003fe442410c007fc4e2821800ff8985043001ff120a086002ee890a82a624df1288c64a4b9e25098b109e3e319316213d6c63442410f9e8c64a4800f9d108949001eba31a212003e7262c424007d64a4863800fcd1090c7001f6929210a003f54424214007f2863842800f7918d043001fb2212086003fa431c10c007f8842821800
def g503l9 : Packing := (56,3,8,4,3,11,0,g503d9)
def g503d10 (i : Nat) : Nat := 0xdb06c0221478b03c47116008f0b4607a03c1b0048620340c82c068560090c40780f0048d228785a320d00a4309c3a5821028052448a1e34108320b00e010f24678050748d2284e1d340e802422c440540a0648620220a908b110106f000611a6221245638d25b122300021078572208878422b106f18607c0c55c06238885648de34c0c3189251bc5a01c610891e158f00036308ae4084568807024422d23c48006906c49298a81c4303a40406d20298680c422123c44111e0845624370a0ad10e008f190e4285641c214811f419081e008f2404407004211e20ac8b20c9011044590f168562a0890a3c2b9207401211588818848f0d16159201a022123c38192348078022c8383c24961010a1ec01212a05802149091060784a48c882e0090a46441d2107906124a24a178002691a440ea0e841c2041923260780c0e10911a44f0688f008891e3c291123c83905681d1b45303c052181918360b816000f1705c0907078824c3e90a0e48430648f0088122874f8360b8103c0e9610c1b0088122874d00c2182e050f20e6c21be0b9fb54b13adca9ba50a0f9d89ab97e9339108e38b68578207d57a87857587216f46d16a46776365e15b458755a5234f64c94a648346043d4063cf3a23753483112bc28f2622171ea19515e1311040b9082041000ffe31a213ff8c6481ffe211303ff4824c0ffd205303ff884460ffd389183ff482460ffd205183ff884420ffd389083ff482420bfe421313df5054c4bfd404313ef4c4884bfe421206ff506481fbd311207ef884481fbe211203df8c64a4f7d311293df4c04a4f7d201293df4604a4fbc41a213ef8c6884fbd306213ef4c0884fbd182213ef420884ff5312087fd0c4821ff6212087fd4c0821ff5202087fd460821ff5102087fe4c4800ffa212003fe4e2800ff930a003fe482800ff9306003fe481800ff9106003cf8844a4ebe31a213cf4c5884fb6212087be8c6800f79316003de4a4800fba212003f6863800fea10a003fc821800
def g503l10 : Packing := (58,2,8,6,3,12,0,g503d10)
def g503d11 (i : Nat) : Nat := 0xd8081b0a41a001f1008492a8301200210f141b0681c060021315416138040e0223378880ea0600e0d05814004071b06c29068008440700c1a0a08814003c783400462020300f05810184068186c29011081cd060d852070180084f0581c0a02072c1601020087e0e1d3de35fd0912bc2ceab2981ea5d0ec22001ff4c4ff8627fe213fe903ff4c0ffa407fd183fe881ff420efa527be213fb043fe800
def g503l11 : Packing := (13,1,8,6,3,10,0,g503d11)
def g503d12 (i : Nat) : Nat := 0xc0a060402006ff
def g503l12 : Packing := (1,0,8,4,3,0,0,g503d12)
def g503samples : Array (Bits × Bits) := #[(0xfe9fb3d95ef233877f90e3ff9bbc308fc63b3fb012450d4eb7191f657eded7c72010692020c80102282000c4008221a198246411c25202201400200081ec00d127004c280152804200490202116c0e0da6b0efc0169508a1804e690bb10e5a6c,0x610500580246220240604ec4944684c0402380642a349800814ca41118801422400c080002600a1324422128a45190001416805412100521410b110020103162cc8500902b17ea790a5c0823c0680e0922b0ef801485082180062903310a1a60),(0xfb57fadaeacff4da90ce976f90ed3e0261d574c905bdb7fec1a37778b87916cecb86040510056ab5009a940b4a50040c25830bae35ac044302a1d9590003d0024043b3844224523d8402696406aee200701851072f46581f0e550c44239b3142,0x6018840480a3e2010d240002002028b0000011241110004498001000c80609060090080048310815801000004248028caa00006200a00400004ae01000325008659c8b11452200208ec82c2ae4200101850070746000804540c04219b0140),(0x2ba4e17515be1113c5ff69fd7751ecdf2a4df3bee9b6208d6f34a6cb4c570fdcf060908845309400d5016920a5218200420880000001b89c200002002a00230018b800509480208033841001b34d54d21821e216c589025398a5a3342df5c0a0,0xa248428800c4128a2016340b0000821ac2205021422518c0604039a12c3082409c200251c10009020c0802001422200881104104a0b824c20190620a102a18110605014b79e426452a87fd02b34d10c2102162060580025388a5013428c5c020),(0x0,0x0),(0x313f142298a6adc50d7814aae4bb81b3ffab0c19eb53e689143971e2e536d99800110b32a24000482844025010023821004034118050010095402480c5500c5104040c2001098402081982985cc4512e9dd034642e40e4406c7252244ce2cf15,0x9cb8c00141000d152906a0014a09033183002102040044142401190621000201040212012c94a044439444c408800484804000880109200008046a218f064e1d110a7f49946011022582e4d41c8451249d0010642a4044006c7052240ce0c504),(0x9beace043bd30e7bde538f3338b7776966ff632e0d082b67f8750a259ec87e7eace800c81903f49146916002a13c405a0698804c09a9e0006a3e01663803632c902a80833a800b0d54a42401ac32387181878dac9931a70cc70480809c2011e6,0x40100044110021000240080019813c01204c8202810040168130401a0001348a001140801400202030000805c8411854140104405002800810248010cc05644ab84002240003008a112000680c10281181828da08811a4040300808084201086),(0x510835afe992e1c89f19408e78735240a99760a1d875d3d00bfe09d7362817dfc304040000000a040000000942000404000001a23400004000014019000090020040120000044010000241043d888aad242bb429f0bc787729aaa2624c81342f,0xd0d80c1416b435008e070033e99c70153435a500201ae02d1a162760cd417a942089002840ca000d1025e06b132042104021582081c6c16598a008401247fcdaff79a6374eebaddffdf7137d3d0088ad2423a428f0b8787729aaa2624c00342f),(0xf6f19e5df58ddaaaa7e6177459cadd3f7f53836ef0b3e25727b1f20f6be5f72700036217828c016a006e969418c01980b9675a004206072381c09c8044bc0c806305610c407b1460885088fa490101535241481ac0d2b5e623991dabc20ca419,0x240320690b050400288001021106800040c0418c10a20c0523040a0c0022198000084b0110150000820101241080a69020015224804508a00108000008980802270802640880484d02113080101005240410018c010b1c603890088c2042019),(0x460e8327be39eb2c727d6e3d8ee0a2f3f8c5bac0d6283be4f56aecb419547c79140890404c32000093000920040dc252401000400800589c481e02261200002c88900053ac002980632014000211cfa80f6612b9522a490875b86a9e33522841,0x1906883346190005598080e4220c41a40493210800ca06091804000440c2090021c2a402203b04c0c28190902218002062842211040002008003108500d083a441bafc908618d930c45802954000c7280e441019522a490874186a0a13122841)]
def g503columns : IndexTree ColumnInfo := (IndexTree.fork 95 (IndexTree.fork 47 (IndexTree.fork 23 (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(64,0,439,0,11),(1,0,502,0,10),(4,0,499,0,10),(16,0,487,0,10),(0,64,437,2,10)]) (IndexTree.leaf [(256,0,247,0,10),(66,0,437,0,9),(2,64,437,0,9),(0,1,358,144,9),(2,0,437,0,9),(0,4,211,288,9)])) (IndexTree.fork 6 (IndexTree.leaf [(0,16,358,129,9),(32,0,471,0,9),(128,0,375,0,9),(0,256,211,36,9),(17,0,486,0,8),(1,16,358,128,8)]) (IndexTree.leaf [(16,1,358,128,8),(65,0,438,0,8),(128,1,358,16,8),(32,4,211,256,8),(68,0,435,0,8),(260,0,243,0,8)]))) (IndexTree.fork 12 (IndexTree.fork 6 (IndexTree.leaf [(4,256,211,32,8),(256,4,211,32,8),(80,0,423,0,8),(128,16,358,1,8),(32,256,211,4,8),(320,0,183,0,8)]) (IndexTree.leaf [(81,0,422,0,7),(145,0,358,0,7),(129,16,358,0,7),(144,1,358,0,7),(292,0,211,0,7),(36,256,211,0,7)])) (IndexTree.fork 6 (IndexTree.leaf [(288,4,211,0,7),(324,0,179,0,7),(5,0,498,0,7),(0,65,292,146,7),(1,64,436,2,7),(64,1,294,144,7)]) (IndexTree.leaf [(129,0,358,0,7),(257,0,246,0,7),(20,0,483,0,7),(36,0,211,0,7),(0,68,145,290,7),(4,64,433,2,7)])))) (IndexTree.fork 24 (IndexTree.fork 12 (IndexTree.fork 6 (IndexTree.leaf [(64,4,147,288,7),(0,80,292,131,7),(16,64,421,2,7),(64,16,294,129,7),(144,0,358,0,7),(272,0,231,0,7)]) (IndexTree.leaf [(96,0,407,0,7),(0,96,145,262,7),(32,64,405,2,7),(64,32,145,262,7),(288,0,211,0,7),(192,0,311,0,7)])) (IndexTree.fork 6 (IndexTree.leaf [(0,192,292,19,7),(64,128,292,19,7),(128,64,309,2,7),(0,320,145,38,7),(64,256,147,36,7),(256,64,181,2,7)]) (IndexTree.leaf [(67,0,436,0,6),(2,65,292,144,6),(3,64,436,0,6),(66,1,292,144,6),(1,80,292,130,6),(16,65,292,130,6)]))) (IndexTree.fork 12 (IndexTree.fork 6 (IndexTree.leaf [(65,16,294,128,6),(80,1,294,128,6),(1,192,292,18,6),(65,128,292,18,6),(128,65,292,18,6),(192,1,294,16,6)]) (IndexTree.leaf [(70,0,433,0,6),(2,68,145,288,6),(6,64,433,0,6),(66,4,145,288,6),(82,0,421,0,6),(2,80,292,129,6)])) (IndexTree.fork 6 (IndexTree.leaf [(18,64,421,0,6),(66,16,292,129,6),(98,0,405,0,6),(2,96,145,260,6),(34,64,405,0,6),(66,32,145,260,6)]) (IndexTree.leaf [(194,0,309,0,6),(2,192,292,17,6),(66,128,292,17,6),(130,64,309,0,6),(322,0,181,0,6),(2,320,145,36,6)]))))) (IndexTree.fork 48 (IndexTree.fork 24 (IndexTree.fork 12 (IndexTree.fork 6 (IndexTree.leaf [(66,256,145,36,6),(258,64,181,0,6),(4,96,145,258,6),(32,68,145,258,6),(68,32,145,258,6),(96,4,147,256,6)]) (IndexTree.leaf [(4,320,145,34,6),(68,256,147,32,6),(256,68,145,34,6),(320,4,147,32,6),(16,192,292,3,6),(80,128,292,3,6)])) (IndexTree.fork 6 (IndexTree.leaf [(128,80,292,3,6),(192,16,294,1,6),(32,320,145,6,6),(96,256,147,4,6),(256,96,145,6,6),(320,32,145,6,6)]) (IndexTree.leaf [(0,32,145,262,7),(0,128,292,19,7),(3,0,436,0,6),(2,1,292,144,6),(1,4,210,288,6),(4,1,354,144,6)]))) (IndexTree.fork 12 (IndexTree.fork 6 (IndexTree.leaf [(33,0,470,0,6),(1,128,292,18,6),(1,256,210,36,6),(256,1,102,144,6),(6,0,433,0,6),(2,4,145,288,6)]) (IndexTree.leaf [(18,0,421,0,6),(2,16,292,129,6),(34,0,405,0,6),(2,32,145,260,6),(130,0,309,0,6),(2,128,292,17,6)])) (IndexTree.fork 6 (IndexTree.leaf [(258,0,181,0,6),(2,256,145,36,6),(4,16,354,129,6),(16,4,195,288,6),(4,32,145,258,6),(132,0,371,0,6)]) (IndexTree.leaf [(48,0,455,0,6),(16,128,292,3,6),(16,256,195,36,6),(256,16,102,129,6),(256,32,145,6,6),(384,0,119,0,6)])))) (IndexTree.fork 24 (IndexTree.fork 12 (IndexTree.fork 6 (IndexTree.leaf [(3,16,292,128,5),(18,1,292,128,5),(3,128,292,16,5),(130,1,292,16,5),(21,0,482,0,5),(5,16,354,128,5)]) (IndexTree.leaf [(20,1,354,128,5),(33,4,210,256,5),(69,0,434,0,5),(132,1,354,16,5),(261,0,242,0,5),(5,256,210,32,5)])) (IndexTree.fork 6 (IndexTree.leaf [(257,4,210,32,5),(17,64,292,2,5),(17,128,292,2,5),(273,0,230,0,5),(257,16,102,128,5),(272,1,102,128,5)]) (IndexTree.leaf [(33,256,210,4,5),(193,0,294,0,5),(129,64,292,2,5),(321,0,182,0,5),(384,1,102,16,5),(6,32,145,256,5)]))) (IndexTree.fork 12 (IndexTree.fork 6 (IndexTree.leaf [(34,4,145,256,5),(6,256,145,32,5),(258,4,145,32,5),(18,128,292,1,5),(130,16,292,1,5),(34,256,145,4,5)]) (IndexTree.leaf [(258,32,145,4,5),(48,4,195,256,5),(84,0,419,0,5),(132,16,354,1,5),(276,0,227,0,5),(20,256,195,32,5)])) (IndexTree.fork 6 (IndexTree.leaf [(272,4,195,32,5),(100,0,147,0,5),(36,64,145,2,5),(260,32,145,2,5),(260,64,145,2,5),(48,256,195,4,5)]) (IndexTree.leaf [(208,0,294,0,5),(144,64,292,2,5),(336,0,167,0,5),(384,16,102,1,5),(352,0,147,0,5),(288,64,145,2,5)]))))))
def g503autos : Array (List Nat) := #[[],[130],[117,132,32],[117,128,64,32],[64],[130,64],[117,66,32,128],[117,66,128]]
def g503levels : Nat → Packing
  | 8 => g503l8
  | 9 => g503l9
  | 10 => g503l10
  | 11 => g503l11
  | 12 => g503l12
  | _ => emptyPacking
def hashg503l9 (i : Nat) : Nat := 0x89c00000c31a280000077788c41f01d202864b8000000004200000000000289c942200069400010c1b8008678af5890220000142d11e0f483430000000570620b0e3110b830
def hashg503l10 (i : Nat) : Nat := 0xb49c4862a6520398001a1b609945800000060a000000000000008dc0002e4613000303a000c1a0000a620000000000000000000000011800021b70cc001e060003a8c0000003078000000819a05f219d07446e115b3152f209000138c000000000000003c000000280258c4c306b800800050b000000000188e612e0728be65902028174c5aa08080000000a84815d8380000000000114612252a0610c80110e088f4408000000000494cd280002068000001017118709c43e00074518b80066a5e6a64b18026570001328001012000000150b6047178084001ce5005404492c000603828400052805158b418a6b370ab112660ab200078d453ff2fb70dcbb5ad616c165b884c8e5b311800000149325688a6434018c6f8002215631000000194cad37490003e2b2a939b0082cb042800000008321220080a1000280002a00c012080100c00000400980218821
def hashg503l11 (i : Nat) : Nat := 0xd6b20c723800000000000002190004454d9a692f0d8000000000943844a83bcc6d17800044a0000000000000e3274b8000000e80518788b9dc000365f49513ae2af048001201a29000002091a438000000343d06e059000000000032582568a7037f8634c350ccceb03a8b1d5c000614540d00801834b122c000000000000184c00000059d80000000000002a26a103910000000aefb20e93c001c2d706e89f42380b000387d8400000002b160420000272a3b26e61660d68140000000002048000e33590f08f00dc2ed687b3c00000064472bfc694b800070d600000078d2090d4f4012390002438ad2000000110a0007010000c1830400008d9e2c0a4d098002857e9e00000034736d534a183c001890a0a700c2a7c8f29ad85dd472c0c0ac02995400060700000013115001744a010118044141211850200b32604a35196
def hashg503l12 (i : Nat) : Nat := 0x42e8392356fb559262940400000000000811a280000000000000000002a400000109d90086e8120d1c7a6000027112b0c10e56008000014300028ab68ea0006c4600a14954c7121c4206006
def g503index : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 10 47 4 11 4 3 (hashg503l9)
  | 10 => lookupWord 42 191 5 13 6 3 (hashg503l10)
  | 11 => lookupWord 41 185 4 13 6 3 (hashg503l11)
  | 12 => lookupWord 11 51 4 11 4 3 (hashg503l12)
  | _ => fun _ => none
def g503 : Forest := ⟨503,12,fun j => g503samples[j]?.getD (0,0),g503columns,g503autos,g503levels,g503index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom503 : graphValid g503 (boundsBefore known375) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s503_8_0 : block g503 8 0 13=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all503_8 : block g503 8 0 13=true := s503_8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s503_9_0 : block g503 9 0 18=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s503_9_18 : block g503 9 18 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s503_9_50 : block g503 9 50 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s503_9_53 : block g503 9 53 3=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all503_9 : block g503 9 0 56=true := (@block_merge g503 9 0 50 6 (@block_merge g503 9 0 18 32 s503_9_0 s503_9_18) (@block_merge g503 9 50 3 3 s503_9_50 s503_9_53))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s503_10_0 : block g503 10 0 11=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s503_10_11 : block g503 10 11 32=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s503_10_43 : block g503 10 43 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s503_10_46 : block g503 10 46 12=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all503_10 : block g503 10 0 58=true := (@block_merge g503 10 0 43 15 (@block_merge g503 10 0 11 32 s503_10_0 s503_10_11) (@block_merge g503 10 43 3 12 s503_10_43 s503_10_46))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s503_11_0 : block g503 11 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s503_11_4 : block g503 11 4 9=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all503_11 : block g503 11 0 13=true := (@block_merge g503 11 0 4 9 s503_11_0 s503_11_4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s503_12_0 : block g503 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all503_12 : block g503 12 0 1=true := s503_12_0
theorem tables503 : checkedTables g503 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g503 0 0 0 = true)
  · exact (rfl : block g503 1 0 0 = true)
  · exact (rfl : block g503 2 0 0 = true)
  · exact (rfl : block g503 3 0 0 = true)
  · exact (rfl : block g503 4 0 0 = true)
  · exact (rfl : block g503 5 0 0 = true)
  · exact (rfl : block g503 6 0 0 = true)
  · exact (rfl : block g503 7 0 0 = true)
  · exact all503_8
  · exact all503_9
  · exact all503_10
  · exact all503_11
  · exact all503_12

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low503 : Lower (vars 503) (graphGoal 503) 13 := lower_forest (g:=g503) (i:=0) (hints:=8607761748) (before_sound known375 valid375) geom503 tables503 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps503 : List (Nat × List Nat) := [(503,[])]
def known503 := extendKnown known375 13 maps503
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid503 : Known known503 := extendKnown_ok valid375 low503 (by decide +kernel)
def g302 : Forest := ⟨302,5,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low302 : Lower (vars 302) (graphGoal 302) 6 := lower_discard (g:=g302) (ci:=(2,0,300,0,5)) (hints:=8591017296) (before_sound known503 valid503) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps302 : List (Nat × List Nat) := [(302,[])]
def known302 := extendKnown known503 6 maps302
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid302 : Known known302 := extendKnown_ok valid503 low302 (by decide +kernel)
def g366d5 (i : Nat) : Nat := 0x13d4e18c64a3
def g366l5 : Packing := (1,3,8,0,0,0,0,g366d5)
def g366d6 (i : Nat) : Nat := 0x147a8a0bf8c64a3bd4c10a3be4c00a3d78a5863e7884863
def g366l6 : Packing := (5,2,8,0,0,5,0,g366d6)
def g366d7 (i : Nat) : Nat := 0x401c0a01012c0a020407902607078e0209140a03001c02b9b90007f4a3fe147fe18f7c4277863
def g366l7 : Packing := (5,1,8,3,1,8,0,g366d7)
def g366d8 (i : Nat) : Nat := 0x20100008497f
def g366l8 : Packing := (1,0,8,3,1,0,0,g366d8)
def g366samples : Array (Bits × Bits) := #[(0x0,0x0),(0xdef8849eefbabd6fb0a497940f9dbde13fa4a2dbc32beffe798d5c3190eedbee6dcd5f3e3632284e6f50dac6d79be3ceb32bb35cff0aa767f3fc69baaed773fffedfb7c76efc747f9fbde8ced47925490002279c20483880700374b2b8276690,0x8a202042410a18c08a27000a404819405152340018550c2620269c1065b49613e34c02624048814349003853814aa96453e040300144f095489296800020089a8c8058eacc068454529002f081c11626348042a98397325048123422b8274010),(0xb54ffbaa56e1f39db755ed52ffde73fe48ad2cd4f6dbb13728ab2d6efbe1ee7ab771a7fd43ee25f7bbee3f27ada67e41d76d4b2fe445dfa6e7738f9e72cb0c27f563dababbb6f9378dfae5b8dfa800960d25886101a18558004c2e4e24c7380d,0x43209148318880c6d981001a130c9c007c011a040c51544e448640320cc800089c0808c200a0a948890b08468a210216dc281d2904e0828c368eba7881668ab688409c58040a32448260120181008ce004c25058698aaa4005962e442047280c),(0x4ef7a167e8d777f30fff626572f5c7fd86bdd12fed718e8008f4e9ffcfdfc51f57247d7e4b19ffdcdad72cd8eb47877e2dd94cf348ff7f3f4891e31dbf6ecbdbeb17af1d0cbe36b57d61dfb7eebf4820b2d010029a14022586909f10d62e806e,0x4011d02e319412000a03c0a709c63c29488e830038932c86004803106c5070d6404029e7806414060102021080ac02a812229260a22e104142b63060c120a2348c9098ba451210501658c4018da010dc304332c1448223e20052de10142e0066),(0x0,0x0),(0xefca297f3ebe1b37ed770c8bea0f5d4db6ceccff8eaf4e11dfddd6f1fb9af7f9fe9ba697bedfb7be76e9f8efebff96f9fea713cfe7b97c9dfe8ebfed49bd7deed50df83ad8e387f827e7234167eab30e482bc0dc45a2781a29656d5115d855b0,0x105c008000010620044840208890200b008c4061428a820002110345820140a40000851832041000046006000400000920122082b218084200204104581900001210230103804902000580000830400180000800000041aeb048c110058815a0),(0x3ec9ff5a3defec4d7bfc55fcb5b832eeedfbb7033d56b75fe7dbcfe8dffd7a9ec2be629dfdd773e74e4a6537fddc7d7fe3fcfcf0dfde8c7d94ff7651d507f3d5b3b2a7ec050febfa7ad8dbdfc14c444120d027022a4c0081d41281e90badae4c,0x35c40c108801441900580250063142060420408d870800505d11208310010108083300080a022800346d41286a014411a0010c0b54000f2a90000813028c5400304e050432a860002025000e22102000020c80000068cc0db7ad01c90380ae08),(0x0,0x0),(0x97ff56dde3446ba2f7beffbb9c7f9d9b5df27f3adc9ddceab7bebe17f64baca31b7edfe0a262fee7f73fa7bc953ddda5e85afec3d16bcbff7f2bdafbe7f0c44a1cf9f9d5f77b9afdf46ed5a2bab79ab0d70c5821d413c7660ba8128feb120933,0xac0220008400401800201d004001029402700010800001112100a8001004800003954200490100a02290908041406c4001014000010064000801040302005549212d000488018089018028647206010008100100007514114a21008bca100011)]
def g366columns : IndexTree ColumnInfo := (IndexTree.fork 84 (IndexTree.fork 42 (IndexTree.fork 21 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(2,0,364,0,7),(4,0,362,0,7),(8,0,358,0,7),(64,0,302,0,6),(0,64,292,10,6)]) (IndexTree.leaf [(66,0,300,0,5),(2,64,292,8,5),(72,0,294,0,5),(8,64,292,2,5),(74,0,292,0,4)])) (IndexTree.fork 5 (IndexTree.leaf [(10,64,292,0,4),(32,0,334,0,5),(256,0,110,0,5),(6,0,360,0,4),(10,0,292,0,4)]) (IndexTree.leaf [(34,0,332,0,4),(12,0,354,0,4),(36,0,330,0,4),(68,0,298,0,4),(260,0,106,0,4),(264,0,102,0,4)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(0,2,268,96,4),(0,4,74,288,4),(0,8,38,320,4),(0,32,72,262,4),(0,256,66,44,4)]) (IndexTree.leaf [(2,4,72,288,3),(4,2,264,96,3),(2,8,36,320,3),(8,2,260,96,3),(2,32,72,260,3)])) (IndexTree.fork 5 (IndexTree.leaf [(32,2,268,64,3),(64,2,268,32,3),(258,0,108,0,3),(0,258,0,108,3),(4,8,34,320,3)]) (IndexTree.leaf [(8,4,66,288,3),(4,32,72,258,3),(32,4,74,256,3),(0,68,0,298,3),(4,64,288,10,3),(4,256,66,40,3)])))) (IndexTree.fork 21 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(256,4,74,32,3),(40,0,326,0,3),(0,40,0,326,3),(64,8,38,256,3),(8,256,66,36,3)]) (IndexTree.leaf [(256,8,38,64,3),(0,96,0,270,3),(32,64,260,10,3),(32,256,66,12,3),(256,32,72,6,3)])) (IndexTree.fork 5 (IndexTree.leaf [(0,320,0,46,3),(256,64,36,10,3),(0,14,0,352,2),(2,12,0,352,2),(4,10,0,352,2)]) (IndexTree.leaf [(8,6,0,352,2),(38,0,328,0,2),(6,32,72,256,2),(34,4,72,256,2),(36,2,264,64,2),(70,0,296,0,2)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(2,68,0,296,2),(6,64,288,8,2),(68,2,264,32,2),(4,258,0,104,2),(258,4,72,32,2)]) (IndexTree.leaf [(2,40,0,324,2),(40,2,260,64,2),(66,8,36,256,2),(72,2,260,32,2),(8,258,0,100,2)])) (IndexTree.fork 5 (IndexTree.leaf [(258,8,36,64,2),(98,0,268,0,2),(2,96,0,268,2),(34,64,260,8,2),(96,2,268,0,2)]) (IndexTree.leaf [(32,258,0,76,2),(258,32,72,4,2),(2,320,0,44,2),(64,258,0,44,2),(66,256,0,44,2),(258,64,36,8,2)]))))) (IndexTree.fork 42 (IndexTree.fork 21 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(4,40,0,322,2),(40,4,66,256,2),(76,0,290,0,2),(8,68,0,290,2),(12,64,288,2,2)]) (IndexTree.leaf [(68,8,34,256,2),(268,0,98,0,2),(12,256,66,32,2),(260,8,34,64,2),(264,4,66,32,2)])) (IndexTree.fork 5 (IndexTree.leaf [(4,96,0,266,2),(32,68,0,266,2),(292,0,74,0,2),(36,256,66,8,2),(260,32,72,2,2)]) (IndexTree.leaf [(288,4,74,0,2),(4,320,0,42,2),(256,68,0,42,2),(8,96,0,262,2),(40,64,260,2,2),(64,40,0,262,2)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(72,32,0,262,2),(40,256,66,4,2),(256,40,0,70,2),(328,0,38,0,2),(8,320,0,38,2)]) (IndexTree.leaf [(264,64,36,2,2),(320,8,38,0,2),(32,320,0,14,2),(256,96,0,14,2),(0,6,0,352,2)])) (IndexTree.fork 5 (IndexTree.leaf [(0,10,0,352,2),(2,256,0,44,2),(0,12,0,352,2),(8,32,0,262,2),(96,0,268,0,2)]) (IndexTree.leaf [(64,32,0,262,2),(288,0,74,0,2),(320,0,38,0,2),(64,256,0,44,2),(14,0,288,0,1),(6,8,0,320,1)])))) (IndexTree.fork 21 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(10,4,0,288,1),(12,2,0,96,1),(32,6,0,320,1),(64,6,0,288,1),(66,4,0,288,1)]) (IndexTree.leaf [(262,0,72,0,1),(6,256,0,40,1),(256,6,0,96,1),(260,2,0,96,1),(42,0,260,0,1)])) (IndexTree.fork 5 (IndexTree.leaf [(10,32,0,260,1),(32,10,0,320,1),(34,8,0,320,1),(64,10,0,288,1),(266,0,36,0,1)]) (IndexTree.leaf [(10,256,0,36,1),(256,10,0,96,1),(264,2,0,96,1),(66,32,0,260,1),(290,0,72,0,1),(34,256,0,12,1)]))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(322,0,36,0,1),(44,0,66,0,1),(12,32,0,258,1),(32,12,0,320,1),(36,8,0,320,1)]) (IndexTree.leaf [(64,12,0,288,1),(72,4,0,288,1),(256,12,0,96,1),(100,0,264,0,1),(36,64,0,10,1)])) (IndexTree.fork 5 (IndexTree.leaf [(68,32,0,258,1),(324,0,34,0,1),(68,256,0,40,1),(260,64,0,10,1),(104,0,260,0,1)]) (IndexTree.leaf [(296,0,66,0,1),(264,32,0,6,1),(72,256,0,36,1),(96,256,0,12,1),(288,64,0,10,1),(320,32,0,6,1)]))))))
def g366autos : Array (List Nat) := #[[],[133,49]]
def g366levels : Nat → Packing
  | 5 => g366l5
  | 6 => g366l6
  | 7 => g366l7
  | 8 => g366l8
  | _ => emptyPacking
def hashg366l6 (i : Nat) : Nat := 0x4
def hashg366l7 (i : Nat) : Nat := 0x2a000040807400180071cd111
def hashg366l8 (i : Nat) : Nat := 0x220000e8b330da9100e4
def g366index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 4 0 0 (hashg366l6)
  | 7 => lookupWord 3 12 1 8 3 1 (hashg366l7)
  | 8 => lookupWord 3 12 0 8 3 1 (hashg366l8)
  | _ => fun _ => none
def g366 : Forest := ⟨366,8,fun j => g366samples[j]?.getD (0,0),g366columns,g366autos,g366levels,g366index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom366 : graphValid g366 (boundsBefore known302) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s366_5_0 : block g366 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all366_5 : block g366 5 0 1=true := s366_5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s366_6_0 : block g366 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s366_6_4 : block g366 6 4 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all366_6 : block g366 6 0 5=true := (@block_merge g366 6 0 4 1 s366_6_0 s366_6_4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s366_7_0 : block g366 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s366_7_2 : block g366 7 2 3=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all366_7 : block g366 7 0 5=true := (@block_merge g366 7 0 2 3 s366_7_0 s366_7_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s366_8_0 : block g366 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all366_8 : block g366 8 0 1=true := s366_8_0
theorem tables366 : checkedTables g366 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g366 0 0 0 = true)
  · exact (rfl : block g366 1 0 0 = true)
  · exact (rfl : block g366 2 0 0 = true)
  · exact (rfl : block g366 3 0 0 = true)
  · exact (rfl : block g366 4 0 0 = true)
  · exact all366_5
  · exact all366_6
  · exact all366_7
  · exact all366_8

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low366 : Lower (vars 366) (graphGoal 366) 9 := lower_forest (g:=g366) (i:=0) (hints:=8607786320) (before_sound known302 valid302) geom366 tables366 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps366 : List (Nat × List Nat) := [(366,[])]
def known366 := extendKnown known302 9 maps366
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid366 : Known known366 := extendKnown_ok valid302 low366 (by decide +kernel)
def g430 : Forest := ⟨430,7,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low430 : Lower (vars 430) (graphGoal 430) 8 := lower_discard (g:=g430) (ci:=(8,0,422,0,7)) (hints:=8859452752) (before_sound known366 valid366) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps430 : List (Nat × List Nat) := [(430,[])]
def known430 := extendKnown known366 8 maps430
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid430 : Known known430 := extendKnown_ok valid366 low430 (by decide +kernel)
def g494d6 (i : Nat) : Nat := 0x219080103650a05b35220e34c34c0b6aa421c69869814dc49d18930d3032ea52280c73a61f954a44c34c1461
def g494l6 : Packing := (5,4,8,0,0,6,0,g494d6)
def g494d7 (i : Nat) : Nat := 0x103c003c00200020e4341c2c0820600120c0a84000380820802010200521c0a104810320105c00301820a4200000404200101090b08004042c04860805858330013066002068c005409808806d02150260222194084083800b8003910190b000b00083c60c26001600160016001078c184c002c002c002c0020f01a0980058005800604040005000808404000000420200000000000000000000000269cc396728e49c838e71ba2f44386708e09c037fcfb9ef3ce766e8dc9b836fcde5ba36f6bed69aab4566acc195b1b600bc16aaba53ea1134a4e466860fe9ed3ba734d91a2324608b915728e4dc939171f83b06e0cc1782dc590ad13a260440830fc1e43a06f0be1682a8500961182083c06e0c8168280460780c81401e028028009fc41e31920efb5020e34c0bf540438d3027f1078634c09fc41d189302f71034e14c0df539038530f7d4e20e14c3df538038530f7e4804e00c39fd40239d18bf51014c3462edd18930d3067f5038e74c0edc38d30d303b74624c34c0ef440530d303b74614c34c09fe4213991837d1014e6460ef930d301183be4c34c0440b7e42130d293dd1014c34a4b7d40430d292df9084c14a4e7d30d305292df9084614a4b7d419185293d74c34614a4f75305185292df9084c24a3b7e42118928edf5064624a3f5d30d18928fdb4c24624a3ded20138830f7d4804e10c3df941138030fcf4c34c44a4f3e18d311293cf4c14c44a4f3d1853112927d5018e74c3ed530d3051867d1074c3821db608539030e7b9084e20c3d6d29138830f6b8844e20c3de608538830f7a8004e20c39f642138430f5d4a44e10c3db621138430f798424e10c3df200138430e7e9084e00c3d7929138030f6e8844e00c3dea10938030f7c8214e00c3e3e3193112938f8c68844a3e5e31a18d28fc78848634a3b5c41d29218f978c64a4863f1d31129218fa78c6884863e6e31928e10bd38634a3842ece31a18e10b9d8c64a4821f35311292087ad8c6884821e7631928e087cd8844a3821f5618d28e087b58c6863821f5529218e087e5884863821ee631a10a087d94a3842821fc618e10a087ae8c6884800eda31a18e003e6884863800eea31a10a003f2863842800ef231a086003ec884821800fd218e086003f8842821800
def g494l7 : Packing := (94,3,8,3,0,11,0,g494d7)
def g494d8 (i : Nat) : Nat := (if i<1 then 0xc5acacb1612ae655caa594e6a50516a8013a69ba4d0a6493069744b2a55927a924485a3f118a8a243fa0f90227e43ea9ef0f467943c29dd8ece74e39f9c70dca6b83459978c6260e2ff97c0bc25d22e196d0b4a5962be9590aaa5462969450a0a4f6273936097e4b0250924890646a228910886642420a8ff07c63ca1dd8e887123701b08d486863341928bb854625810687d038e1ae0cf86182da15e0a284b02260fa07083481720a004882080d205a02080a001e000ffa72261ffd31130ffe9c4987ff4e04c3ffc63241ffd30d20ffe9890c7ff4c34c2ffc31a617fd30d18bfe988983ff4834c1ffa61260ffd189307fe9888c3ff483461ffa61230ffd189187ff1ce981ff4e34c0ff871a607fd30d303ff0c6981ff4e24c0ffa612607fd189303fe9c2981ff4c14c0ffa30a607fd105303ff18c901ff4c3480ff861a407fe18d203fe982901ff461480ffa732307fe319183fe9868c1ff4e2460ffa612307fd189183fe9c28c1ff4c1460ffa30a307fd105183fe986881ff863440ffa60a207fd185103fe984841ff462420dfc632625fe39d30f7f18c987fd0e14c3bfa71061dfd38430efe9c0187f74c3863fba41c31dfe39d30b7f18c9857f8e7462bfa732317dd30d18bef0c68c5fb4c2462bfc73a60efe3193077e9869837f8e7461bfa73230fdd30d187ef0c68c3fd4c1461bfc73a20dfd399106fe9c6883fb4c2441fda31220ff5305106ff1ce981bf8c64c0dfa61a605fe39d182fe9cc8c1f7863460ff2602305fe39d102fe9cc8817f4e3440fda312207ed105103fc9808817f8e7420bfa732105fd38d082fe9c4841fd461420fea20a107f9301083fc8c0841bf0e38c6dfa41c636fe18e31b7e8c518dbf4818c6dfa30c636fd10631b7e90118dbf4608c6dfa204636fd08231bbf18c949df4c34a4ef861a5277e18d293be982949df4614a4f7c634427bd30e213de187109ef863884f7a60c427bd186213de981109ef460884f7a1044277e31928fbe986947df4c24a3efa31251f7d30528fbe8c2947df4414a3fb873431fde31a18fee9890c7f74c2863fba60c31fdd20618fee8830c7f74c0863fba40431fdd10218fee8410c7fb8c6842fda61c217ec30e10bf70c7085fb4c1842fda30c217ed30210bf68c1085fb420842fec63410ff5312087fa987043fd0c3821fea41c10ff618e087fa985043fd462821fea60410ff5202087fa8c1043fd440821ff4634007f930e003fc187001fe863800ff2614007f918a003fc983001fe461800ff220c005bd39030ef69c41877d4e10c3bf270061e7e3192939e988949af8c6884cfc63251f3e21128faf0c6947b78c6863eba52431f9e21218f7718d085db4a3842f9c31c216f631a087ba949043ed884821eea51c10fd618e087f3085043be8c6800f74424007da18e003f5085001fc821800 else 0x4090114028409010a0e10320400c702203018c3c04108185280c04302c3e101880c04340a01104605a0807102480441184024083c038682402207c1a1402103104814680e00203300048605a03028c0c02e051a07800a050c001489070a0e10dc2410181b0521210118182c18220740c80c0058182a038703054088c0e8183b181d0306e381901c006198190340a481901814703207800c1a8183e1c0d028a06c00503076100c20819071841030341b102f406000a608285e05c0704903b0a6081c061b83430a02481c6168170004048202016000887048050016001c080bc001a0f080c86e2033000a4200503432030009048005800341e0d0008330487a30170001c2624121e890008178007a3c00190e068006070e440c86e2c00380807038722400205e001c8f00080351c118002210100c0142081c3d28730387a3082070f4614819804101c941a038200d6062e00143b000e606240c1182e1a101a038010e6060d7003e0010a40c0e41202f00018e02034190e0600c1fc00262c0c018038007a580e060f4701a030307a401a090f4602032170c0b818150e490302a1c8e0603439181703072340a060e460900d0387240480681c39220980090480058006000c0018003000506c00483600240f001600142c03406060f0a80c11030c0e0f034181a8640880c101a190b406088188862030440c4800280c002412031600180030007000a0d800b000a110307030380b406060e0a808728440c4c04394220620168440c1c9101082060e0981c0c1c8f000c00142030006000c0018003800506c00481e002c00300050180050002c2c0030006000e00141b001600180028406000a0900890480058006000c001c00283600241b001207800a000a03000812818503600280030006000c0018002060160b0700917010300bc00390f4333e0406017800721e8667c040c02f000e43d0ccf0440c24090cc04302411800a060a10090a0081858005084184846002823001410830a08c00580050841848460024183800508c00503050804850340a242206140c1bbfdd9aeaf748b92dc0adbf6bcb51da02ccf63ab10d822bcb5ccad9d692b03568aa2d48a9ff4e6a6bd2fa95f4a0a43d16a86f4009eeceea72f3749a8cc926032de95dca8a513266921c85a3bf1b28c7c5b229311c886c38218f0ae840c1a204f00e7fabf49f86fa07b9bd69e96f28782bbd9dbaec4750ba21cf2e56719b819b9edac6c4b549a36d0c66fb2c98cec58606afa9766b7)
def g494l8 : Packing := (204,2,8,7,0,13,0,g494d8)
def g494d9 (i : Nat) : Nat := 0x580453051cc22000c402c190104048a0e0602e0a011cc2200384838082082832003d1d82d20c0202e020809181801828e61100059c17000d41e0c3e041c180b82c045300041c1c0b828661038039c180b008207212303819050cc207007383017051c81c106058300d01094200a703000230104048c0c80404661284018e2f0602c0d01148141080602c2508030e40e782c04190880160208030e0b018002080b0740610062c16020b84400b0580c0010482c200e30940610062588aad4025546f856f9dd1b5f648b8152a6144c788ca95123e3fc6b0a40e412414800ff8c6ff4c4ff4c3ff0c3ff483ff863ff4c2ff462ff4c1ff481ff461ff441ff4c0ff480ff460ff440ff420bf8c6df4a4ef884df4a3f7863fb842fd821fe800
def g494l9 : Packing := (25,1,8,8,0,11,0,g494d9)
def g494d10 (i : Nat) : Nat := 0x501080027f
def g494l10 : Packing := (1,0,8,5,0,0,0,g494d10)
def g494samples : Array (Bits × Bits) := #[(0x0,0x0),(0xd1f8815feff5fc21e8a49d8579abe516a3d095c7d291841261e4c5cfb963e786afab7c7f6dd8c9f9ebee7cbd420891aecb6ad97dc354cf8da72f17ba9a10589b8854a61926c72671216070802c83d425d20d19284c180c849a05393537daf910,0x2420140362410101101002484014018010a0204208418a0c801004000002122014012800090000e60604408e06400228140001a080284200020180000000100800240c4302000000175c82000106000619195010b080c009205282036007900),(0xa1487df4e4a8a5b51feb5e9fb07132c7f2097bf14f5983f7dfd2b73a5db534abc80ccfb9445769425cf45a861efee846215cf68bc488e2a0726b8abcc0a48044050049400930c0820c920820d16c09d0003080d5010e982910f645c84b8175be,0x3033088012101220028a0090ac88400820404aa2b424358cca0900406020eb10104603740485200103060d08a44e4036b28481860969400810710507040001a9a641154a2001042a1099705009301c92690bba41c60c1820106645c80b817096),(0x291c55a5b152dd6be61d2c77277baf2c0c8d501de067d9d7262d1b900f38ebe6defd1b57747e0ee5d078bfd69887b5bf59b7cde2b7bfacbb59be35f905410720308210029008190cd00d870b0200220a2842460202e842607514deeb3084aacb,0x1140202105090789185020e8f21200101d084020024e1c9981903080400cb04832283438403802465c20019e03c48722404ce10e4919180e182814402008e024636600700204c12256c1404d8000d827105da8be248022054145e613084a0cb),(0x0,0x0),(0xe6f3bfaabf5b1a57a7b3e6879ccdb6541de69fa109aebabcfb851fbdb4944834e9d87929ffbdf79ffd33b7c5e7299fa0dd7feec53c7592cc854cfa95a08e7002c6694afc4381c0d12f801074847855810594b074b047a113d7fac025806ac04a,0x4100022040c32c812054930a420285a5803100080b194003000207980d00040d0208480b514009a010890085021084004c196a00b6901000a480e0b8a0558c400100280048c400548400078400808168164440ba2042811145988005804a8048),(0x3c697a57f2e65cfba7d9a13b5ae4c6594699eeb88ca7dd4f94f7efbefb7e5d4ab1cdb924acd40f77d729bee05ea0ff5a26a7ecbabebbe55ffac2fa7f19100209308430031400212c802545810a038024504a0702429801576dc38ace0d3316b1,0xb42004844181430048026c01401a03449e017129d251001025624c004bb504080c882018192c1851181c900000011689080100650108020c1c550293685a50780009890803981188c002200120e2127d8e6a20741490015729c2808e09330630),(0x6e76ceffbbd5ea0199de60e34ffaf9f77172cd26f69cef33eada75f6fe34f9d15f76e7b5ee61933988c67b096979b09ba2d372f5552cff7f163751430200089008108400204606000040200020800000820108080c70a7810d64771edba882ac,0xe921282e8091c8cd6c00979838442fe0dc5560221d4bc7063306842923915e5ce2b9c016dd02b7608217b1e61b9963995498c5845650001c6b022139982d121670940620c80739e41a82004295089fff9e6e6afef4f0a3810d60571ec9a882ac),(0xf79f6a80f36a23ff7d527feeae946aabd8af766b7fcaa7edaa5f72effbdf9f9b4d3eb7cef3bfb893eb0f13fbabdfceff757caf2cea737f7b5af7d726646ba564432b01a4c8381802521a8a5e51142a5a2da06081b1717bfa80092400e8352f64,0x8e4070458804410640006861001000420e003014000208000104b806004c10024c8100002a08545280300200008011880022006900060a3300040a0011a2000008808020031a000100000003040b620580b0050419b160ca8001200040300f20)]
def g494columns : IndexTree ColumnInfo := (IndexTree.fork 86 (IndexTree.fork 43 (IndexTree.fork 21 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(128,0,366,0,9),(4,0,490,0,8),(8,0,486,0,8),(64,0,430,0,8),(0,128,364,2,8)]) (IndexTree.leaf [(130,0,364,0,7),(2,128,364,0,7),(132,0,362,0,7),(72,0,422,0,7),(136,0,358,0,7)])) (IndexTree.fork 5 (IndexTree.leaf [(2,0,364,0,7),(32,0,462,0,7),(256,0,238,0,7),(192,0,302,0,6),(0,192,292,10,6)]) (IndexTree.leaf [(64,128,300,2,6),(128,64,292,10,6),(194,0,300,0,5),(2,192,292,8,5),(66,128,300,0,5),(130,64,292,8,5)]))) (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(200,0,294,0,5),(8,192,292,2,5),(72,128,292,2,5),(136,64,292,2,5),(0,4,202,288,6)]) (IndexTree.leaf [(0,8,166,320,6),(0,64,292,10,6),(66,0,300,0,5),(2,64,292,8,5),(12,0,482,0,5),(36,0,458,0,5)])) (IndexTree.fork 5 (IndexTree.leaf [(32,4,202,256,5),(68,0,426,0,5),(4,128,360,2,5),(260,0,234,0,5),(256,4,202,32,5)]) (IndexTree.leaf [(8,64,292,2,5),(64,8,166,256,5),(8,128,292,2,5),(264,0,230,0,5),(256,8,166,64,5),(160,0,334,0,5)])))) (IndexTree.fork 21 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(32,128,332,2,5),(384,0,110,0,5),(134,0,360,0,4),(6,128,360,0,4),(74,0,292,0,4)]) (IndexTree.leaf [(10,64,292,0,4),(138,0,292,0,4),(10,128,292,0,4),(162,0,332,0,4),(34,128,332,0,4)])) (IndexTree.fork 5 (IndexTree.leaf [(76,0,418,0,4),(140,0,354,0,4),(164,0,330,0,4),(292,0,202,0,4),(288,4,202,0,4)]) (IndexTree.leaf [(196,0,298,0,4),(388,0,106,0,4),(328,0,166,0,4),(320,8,166,0,4),(392,0,102,0,4),(0,2,268,224,5)]))) (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(0,256,194,44,5),(6,0,360,0,4),(4,2,264,224,4),(10,0,292,0,4),(8,2,260,224,4)]) (IndexTree.leaf [(34,0,332,0,4),(32,2,268,192,4),(64,2,268,160,4),(128,2,268,96,4),(0,258,0,236,4),(0,12,130,352,4)])) (IndexTree.fork 5 (IndexTree.leaf [(4,8,162,320,4),(8,4,194,288,4),(0,132,72,290,4),(128,4,74,288,4),(4,256,194,40,4)]) (IndexTree.leaf [(40,0,454,0,4),(0,136,36,322,4),(128,8,38,320,4),(8,256,194,36,4),(96,0,398,0,4),(0,160,72,262,4)]))))) (IndexTree.fork 43 (IndexTree.fork 21 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(128,32,72,262,4),(288,0,202,0,4),(32,256,194,12,4),(320,0,166,0,4),(64,256,130,44,4)]) (IndexTree.leaf [(128,256,66,44,4),(256,128,108,2,4),(0,14,0,480,3),(4,10,0,480,3),(8,6,0,480,3)])) (IndexTree.fork 5 (IndexTree.leaf [(36,2,264,192,3),(68,2,264,160,3),(2,132,72,288,3),(130,4,72,288,3),(132,2,264,96,3)]) (IndexTree.leaf [(4,258,0,232,3),(40,2,260,192,3),(72,2,260,160,3),(2,136,36,320,3),(130,8,36,320,3),(136,2,260,96,3)]))) (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(8,258,0,228,3),(96,2,268,128,3),(2,160,72,260,3),(130,32,72,260,3),(160,2,268,64,3)]) (IndexTree.leaf [(32,258,0,204,3),(192,2,268,32,3),(64,258,0,172,3),(386,0,108,0,3),(128,258,0,108,3),(258,128,108,0,3)])) (IndexTree.fork 5 (IndexTree.leaf [(32,12,130,320,3),(36,8,130,320,3),(40,4,194,256,3),(64,12,130,288,3),(68,8,162,256,3)]) (IndexTree.leaf [(72,4,130,288,3),(0,140,0,354,3),(132,8,34,320,3),(136,4,66,288,3),(268,0,226,0,3),(12,256,194,32,3)])))) (IndexTree.fork 22 (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(256,12,130,96,3),(260,8,162,64,3),(264,4,194,32,3),(100,0,394,0,3),(4,160,72,258,3)]) (IndexTree.leaf [(32,132,72,258,3),(36,128,328,2,3),(132,32,72,258,3),(160,4,74,256,3),(36,256,194,8,3),(0,196,0,298,3)])) (IndexTree.fork 5 (IndexTree.leaf [(4,192,288,10,3),(68,128,296,2,3),(128,68,0,298,3),(132,64,288,10,3),(68,256,130,40,3)]) (IndexTree.leaf [(132,256,66,40,3),(256,132,72,34,3),(384,4,74,32,3),(104,0,390,0,3),(168,0,326,0,3),(0,168,0,326,3)]))) (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(128,40,0,326,3),(40,256,194,4,3),(64,136,36,258,3),(192,8,38,256,3),(72,256,130,36,3)]) (IndexTree.leaf [(136,256,66,36,3),(256,136,36,66,3),(384,8,38,64,3),(0,224,0,270,3),(32,192,260,10,3),(96,128,268,2,3)])) (IndexTree.fork 5 (IndexTree.leaf [(128,96,0,270,3),(160,64,260,10,3),(96,256,130,12,3),(160,256,66,12,3),(256,160,72,6,3)]) (IndexTree.leaf [(384,32,72,6,3),(0,448,0,46,3),(64,384,0,46,3),(128,320,0,46,3),(256,192,36,10,3),(384,64,36,10,3)]))))))
def g494autos : Array (List Nat) := #[[]]
def g494levels : Nat → Packing
  | 6 => g494l6
  | 7 => g494l7
  | 8 => g494l8
  | 9 => g494l9
  | 10 => g494l10
  | _ => emptyPacking
def hashg494l7 (i : Nat) : Nat := 0x510000000008c964
def hashg494l8 (i : Nat) : Nat := 0xb600096b57188000000003bdfad83c0000027c2fcc902ff46305807ce64100c00459001ef05a7d5a0c251a8fa6001f23a60cd62194c00713e2e4559ceb1a190e00000000000000000f0200000000aa40000040d000000002960000000053bdae000000000000000039d001cca417a10000000000010b150250005b80000000011757416000d8531f9980024e0004f14493e8294c2aa74b66e02243a0fd639682881311555da46220015a800335ac1a7c46a1caead4a508392dc0cac0c9228ae5a5b00002a18214000314724b0020001400c204011d102003001
def hashg494l9 (i : Nat) : Nat := 0x36fca25aa7dfba528b0a8ae42a3be47be58000e15c980b1077f97b8c000000f5bdacf0b756000e16d5041443803c743f870007b870c533131000f9d000230ab0934b6c000b050006afd5dc277a1000000bc66aa06bb700000004b400000089c00000081f000e9600000054db630007750000000000000000001c90000000c4ab7000000000222000000000282e8400000000000057347100011a20423e08dd3d9c3666000c1e000000b20d92f9e88357f000544000000000000000a950004c2ca6000b51d9f2a4461293a18a42a37f85362c6f201d1122c77436db942b9ea7b81f3f1b324a106746b91839bbd1a047a345d6790762f4cb78e541557325000000a0d000bb6d88a0e04e40f959fc13352794ab212c4cf5326412e5b2b7828b4b500944f60833ba7ea54280e558adb68d4b53a000000000b9a9a800018f000000000e17000da9000000f26000f9b519d650001246c701b000b320000000000000000007bcc72921000bc0000000000d2b000000000000000000802000640d23469d6018a85e00006e000e1ce480008a3000000000090cbb0bf40021d2290000009999767c80000000004520008492a516a000000010000000000a89ba2c2d55fd0325c14781300007c8c598604e14e0820c00c90808ce0801030060000058000c10002000042800c004f14a10405a04608b04700a0450004470c80426e20c0
def hashg494l10 (i : Nat) : Nat := 0x26a61a860f9fab86e448917448035c253500126280029800004c5000000006098e0000133ecf21a0305492
def g494index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 9 0 7 3 0 (hashg494l7)
  | 8 => lookupWord 32 141 6 11 7 0 (hashg494l8)
  | 9 => lookupWord 68 306 6 12 8 0 (hashg494l9)
  | 10 => lookupWord 9 39 3 9 5 0 (hashg494l10)
  | _ => fun _ => none
def g494 : Forest := ⟨494,10,fun j => g494samples[j]?.getD (0,0),g494columns,g494autos,g494levels,g494index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom494 : graphValid g494 (boundsBefore known430) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s494_6_0 : block g494 6 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all494_6 : block g494 6 0 5=true := s494_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s494_7_0 : block g494 7 0 32=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s494_7_32 : block g494 7 32 19=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s494_7_51 : block g494 7 51 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s494_7_83 : block g494 7 83 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all494_7 : block g494 7 0 94=true := (@block_merge g494 7 0 51 43 (@block_merge g494 7 0 32 19 s494_7_0 s494_7_32) (@block_merge g494 7 51 32 11 s494_7_51 s494_7_83))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s494_8_0 : block g494 8 0 27=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s494_8_27 : block g494 8 27 32=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s494_8_59 : block g494 8 59 32=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s494_8_91 : block g494 8 91 32=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s494_8_123 : block g494 8 123 29=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s494_8_152 : block g494 8 152 32=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s494_8_184 : block g494 8 184 20=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all494_8 : block g494 8 0 204=true := (@block_merge g494 8 0 123 81 (@block_merge g494 8 0 59 64 (@block_merge g494 8 0 27 32 s494_8_0 s494_8_27) (@block_merge g494 8 59 32 32 s494_8_59 s494_8_91)) (@block_merge g494 8 123 61 20 (@block_merge g494 8 123 29 32 s494_8_123 s494_8_152) s494_8_184))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s494_9_0 : block g494 9 0 8=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s494_9_8 : block g494 9 8 17=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all494_9 : block g494 9 0 25=true := (@block_merge g494 9 0 8 17 s494_9_0 s494_9_8)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s494_10_0 : block g494 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all494_10 : block g494 10 0 1=true := s494_10_0
theorem tables494 : checkedTables g494 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g494 0 0 0 = true)
  · exact (rfl : block g494 1 0 0 = true)
  · exact (rfl : block g494 2 0 0 = true)
  · exact (rfl : block g494 3 0 0 = true)
  · exact (rfl : block g494 4 0 0 = true)
  · exact (rfl : block g494 5 0 0 = true)
  · exact all494_6
  · exact all494_7
  · exact all494_8
  · exact all494_9
  · exact all494_10

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low494 : Lower (vars 494) (graphGoal 494) 11 := lower_forest (g:=g494) (i:=0) (hints:=8876221776) (before_sound known430 valid430) geom494 tables494 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps494 : List (Nat × List Nat) := [(494,[])]
def known494 := extendKnown known430 11 maps494
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid494 : Known known494 := extendKnown_ok valid430 low494 (by decide +kernel)
def g495 : Forest := ⟨495,11,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low495 : Lower (vars 495) (graphGoal 495) 12 := lower_discard (g:=g495) (ci:=(1,0,494,0,11)) (hints:=8607786327) (before_sound known494 valid494) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps495 : List (Nat × List Nat) := [(510,[64]),(495,[])]
def known495 := extendKnown known494 12 maps495
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid495 : Known known495 := extendKnown_ok valid494 low495 (by decide +kernel)
def g445 : Forest := ⟨445,9,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low445 : Lower (vars 445) (graphGoal 445) 10 := lower_discard (g:=g445) (ci:=(8,0,437,0,9)) (hints:=8592065796) (before_sound known495 valid495) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps445 : List (Nat × List Nat) := [(445,[])]
def known445 := extendKnown known495 10 maps445
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid445 : Known known445 := extendKnown_ok valid495 low445 (by decide +kernel)
def g253 : Forest := ⟨253,7,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low253 : Lower (vars 253) (graphGoal 253) 8 := lower_discard (g:=g253) (ci:=(0,4,217,32,7)) (hints:=52454660) (before_sound known445 valid445) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps253 : List (Nat × List Nat) := [(253,[])]
def known253 := extendKnown known445 8 maps253
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid253 : Known known253 := extendKnown_ok valid445 low253 (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low125 : Lower (vars 125) (graphGoal 125) 5 := size_of (hints:=52454660) (by decide +kernel)
def maps125 : List (Nat × List Nat) := [(252,[101,84,67,50,32,112,16]),(237,[116]),(125,[])]
def known125 := extendKnown known253 5 maps125
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid125 : Known known125 := extendKnown_ok valid253 low125 (by decide +kernel)
def g509d8 (i : Nat) : Nat := 0xa3be473c10c007ec884821800
def g509l8 : Packing := (2,3,9,0,0,3,0,g509d8)
def g509d9 (i : Nat) : Nat := 0xc03800482a000903042a6021054c062827808504f018a5df1b144d86c03fe8e7800ff9386003fe481800df639e087ed884821dfa39e003fc821800
def g509l9 : Packing := (7,2,9,1,3,8,0,g509d9)
def g509d10 (i : Nat) : Nat := 0x201002131c45028150987224900684c511408140ab09c04415c5584e03241503406099386d21d68b403ff1cfff4e1ffa40dfe39ffb043fe800
def g509l10 : Packing := (6,1,9,3,3,8,0,g509d10)
def g509d11 (i : Nat) : Nat := 0x503012060284c067ff
def g509l11 : Packing := (1,0,9,3,3,0,0,g509d11)
def g509samples : Array (Bits × Bits) := #[(0xd60df40dc734eed1d29b44c188cbaba297fae8dde064f024d377bb7fc8efbdff74224505cc05341008a108c05418420546085c20801803009290200408554007011600a21285508c2080088e01cce00793665478149c9192c14a762712785962,0x10070100223149e2143240100100840c00451a6040205f002080891002088c1024440006290201640882324cc88000090101c004600888500c8287000b38c0802442c246e29f06340f00104e014c000393664058049c80900102662310784160),(0x0,0x0),(0x9bf18ebfcf1fd0f535985bba4aee4af5f6695bbc6fd3a3773ecccefad69ed3b4c7900a18239801807212820401010862814120c8488418a04409048b60220d000000d445a4482b019114060f861b52a7411ba17b8cc26473176118a2b0a48680,0x1142260011180985240d040c880081283003809008100090010d4620c0480582000440050000080167860180341218108d9000590180914b10000106122028b9d3e5b8340098584c932738e821b4204410b807b8c404472136018a2a0008680),(0xc2a5dd32d72e59f9955f1ccf33a4c0ab2daafa8519ca69cac0bbce7ab72fcdc0c8da062106248400508553a0060a10038148100254264100004c3208480127004482908480004324601f17296f44d1009659a154ced415918939720c50ba226,0xcd2149d1080340129370102b08802b00ac422741212002110000520caa150108408009840431009804008e0008e208d081a0c50200221501121102006c62868a03ba038b78b8b2539202380086a44d10016090154ccd4159109193200108a226),(0x76278ea9dc3dfc737b401cd9b9befdc9a1afee9e1e5f63c4eeacaf516d717f6aed6054850800003d808520c11c1a549c40020c009019030e2212081019150008732002b2121250c400600094e8a2e8f82ea941003b21c4f38b7883d808148d0e,0x49064288988220d0848866d00280111c60001843b45a008c818762a9405010848016080144808010020003101091260260019130a062284422d004214821566812c1c290120d84900682f9048a2e8f0288901003b2044638a58819008048802),(0x17ec1b766ede0f32fbe6b2f39e6795115945b168eeaa3e6e0421c77e153b4df8ba4008180090820240528200a384002000e1029f4a2480614d6114c8622aa88088814404a5208101180a06187d229d5352c031d059d4ae0570870a09688450f7,0xd8835910e4e061042da00e061572110d0c344222b0620582e92d209081c1470408a011000a28e4474000900650380030a002300007e00008081424809e44945462c1a008beb47a53360c0c107d209d1312c031805094a8016083020848845036),(0x7399df12da82abaf6d7eb0ac076224bd6b1770e9de91bc1ae1ebf48c4e939367f2c920421020400005081008000081002800010024006400000003208080100004082908000000320400d01e5053363d7257ca8d112022004ede60fcfe1ee450,0xc03022d75c2a0d688fa740b10f94ae0310c01488d214a23985a0e3458aa2478b40202260844c02d9900080b004d60618160078599002000142880f139d7975fc45fc7487474dac6dfdc7de5053322d72174a88112022004e4e60dcfe164450),(0x3a2de1adbb99f7964f037d42bc1cd3788aac72f3f7706dd191bdbe65b58af2e37c021180c405342d8824280148021699060a50201001000eb08228141140400f723602100097004820e00801bb29040ca51a36a7624d71046225715caf41548c,0x8a60000200069010e3853982ec021a8028808003009000e21427008441802247832802500011b0082341058004002d0010682640804104280040509ca0452a195a9121901c402182f097c001b201040c041036a7404131046025104ca701148c),(0xa95ff970bcfa93bef4fb736eee3f607f4eaab5d6cd7f1bbbec523b89f1bfb393e1548220234a8bc232404536a2e5284291b4a25703e298d1096cd0430608a7f088c190414968ae00cb1f216142450be818900c8ae5120aec2c0ca49317710a79,0x40000a100004610001218002058020400080800c18a02004020801002808209703004101061020a00401610404800604040a88200500e004a0002000996920000004740142002800c18061004000e808100c00210202840c0c241116710849)]
def g509columns : IndexTree ColumnInfo := (IndexTree.fork 181 (IndexTree.fork 90 (IndexTree.fork 45 (IndexTree.fork 22 (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(64,0,445,0,10),(0,64,437,8,10),(72,0,437,0,9),(8,64,437,0,9),(1,0,508,0,9)]) (IndexTree.leaf [(0,1,364,144,9),(4,0,505,0,9),(8,0,437,0,9),(16,0,493,0,9),(0,16,364,129,9),(32,0,477,0,9)])) (IndexTree.fork 5 (IndexTree.leaf [(128,0,381,0,9),(0,128,364,17,9),(1,16,364,128,8),(16,1,364,128,8),(1,128,364,16,8)]) (IndexTree.leaf [(128,1,364,16,8),(16,128,364,1,8),(128,16,364,1,8),(145,0,364,0,7),(17,128,364,0,7),(129,16,364,0,7)]))) (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(144,1,364,0,7),(0,4,217,288,8),(0,8,181,320,8),(0,32,217,260,8),(256,0,253,0,8)]) (IndexTree.leaf [(17,0,364,0,7),(65,0,444,0,7),(0,65,292,152,7),(1,64,436,8,7),(64,1,300,144,7),(129,0,364,0,7)])) (IndexTree.fork 6 (IndexTree.leaf [(0,12,145,352,7),(36,0,473,0,7),(4,32,217,256,7),(32,4,217,256,7),(68,0,441,0,7),(0,68,145,296,7)]) (IndexTree.leaf [(4,64,433,8,7),(256,4,217,32,7),(0,40,145,324,7),(64,8,181,256,7),(256,8,181,64,7),(80,0,429,0,7)])))) (IndexTree.fork 22 (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(0,80,292,137,7),(16,64,421,8,7),(64,16,300,129,7),(144,0,364,0,7),(96,0,413,0,7)]) (IndexTree.leaf [(0,96,145,268,7),(32,64,405,8,7),(256,32,217,4,7),(192,0,317,0,7),(0,192,292,25,7),(64,128,300,17,7)])) (IndexTree.fork 5 (IndexTree.leaf [(128,64,309,8,7),(0,320,145,44,7),(64,256,145,44,7),(256,64,181,8,7),(73,0,436,0,6)]) (IndexTree.leaf [(8,65,292,144,6),(9,64,436,0,6),(72,1,292,144,6),(1,80,292,136,6),(16,65,292,136,6),(65,16,300,128,6)]))) (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(80,1,300,128,6),(1,192,292,24,6),(65,128,300,16,6),(128,65,292,24,6),(192,1,300,16,6)]) (IndexTree.leaf [(4,40,145,320,6),(32,12,145,320,6),(36,8,145,320,6),(76,0,433,0,6),(8,68,145,288,6),(12,64,433,0,6)])) (IndexTree.fork 6 (IndexTree.leaf [(64,12,145,288,6),(72,4,145,288,6),(256,12,145,96,6),(100,0,409,0,6),(4,96,145,264,6),(32,68,145,264,6)]) (IndexTree.leaf [(292,0,217,0,6),(260,32,217,0,6),(288,4,217,0,6),(4,320,145,40,6),(68,256,145,40,6),(256,68,145,40,6)]))))) (IndexTree.fork 45 (IndexTree.fork 22 (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(88,0,421,0,6),(8,80,292,129,6),(24,64,421,0,6),(72,16,292,129,6),(104,0,405,0,6)]) (IndexTree.leaf [(8,96,145,260,6),(40,64,405,0,6),(64,40,145,260,6),(72,32,145,260,6),(256,40,145,68,6),(200,0,309,0,6)])) (IndexTree.fork 5 (IndexTree.leaf [(8,192,292,17,6),(72,128,292,17,6),(136,64,309,0,6),(328,0,181,0,6),(8,320,145,36,6)]) (IndexTree.leaf [(72,256,145,36,6),(264,64,181,0,6),(320,8,181,0,6),(16,192,292,9,6),(80,128,300,1,6),(128,80,292,9,6)]))) (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(192,16,300,1,6),(32,320,145,12,6),(96,256,145,12,6),(256,96,145,12,6),(0,256,145,44,7)]) (IndexTree.leaf [(5,0,504,0,6),(4,1,360,144,6),(9,0,436,0,6),(8,1,292,144,6),(33,0,476,0,6),(32,1,332,144,6)])) (IndexTree.fork 6 (IndexTree.leaf [(12,0,433,0,6),(4,8,145,320,6),(8,4,145,288,6),(20,0,489,0,6),(4,16,360,129,6),(64,4,145,288,6)]) (IndexTree.leaf [(132,0,377,0,6),(4,128,360,17,6),(260,0,217,0,6),(4,256,145,40,6),(24,0,421,0,6),(8,16,292,129,6)])))) (IndexTree.fork 23 (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(40,0,405,0,6),(8,32,145,260,6),(32,8,145,320,6),(136,0,309,0,6),(8,128,292,17,6)]) (IndexTree.leaf [(264,0,181,0,6),(8,256,145,36,6),(48,0,461,0,6),(32,16,332,129,6),(64,32,145,260,6),(160,0,349,0,6)])) (IndexTree.fork 6 (IndexTree.leaf [(32,128,332,17,6),(288,0,217,0,6),(32,256,145,12,6),(320,0,181,0,6),(5,16,360,128,5),(20,1,360,128,5)]) (IndexTree.leaf [(5,128,360,16,5),(132,1,360,16,5),(9,16,292,128,5),(24,1,292,128,5),(9,128,292,16,5),(136,1,292,16,5)]))) (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(33,16,332,128,5),(48,1,332,128,5),(81,0,300,0,5),(17,64,292,8,5),(33,128,332,16,5)]) (IndexTree.leaf [(160,1,332,16,5),(193,0,300,0,5),(129,64,292,8,5),(12,32,145,256,5),(40,4,145,256,5),(68,8,145,256,5)])) (IndexTree.fork 6 (IndexTree.leaf [(12,256,145,32,5),(260,8,145,64,5),(264,4,145,32,5),(20,128,360,1,5),(132,16,360,1,5),(36,64,145,8,5)]) (IndexTree.leaf [(68,32,145,256,5),(96,4,145,256,5),(36,256,145,8,5),(260,64,145,8,5),(320,4,145,32,5),(24,128,292,1,5)])))))) (IndexTree.fork 90 (IndexTree.fork 45 (IndexTree.fork 22 (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(136,16,292,1,5),(96,8,145,256,5),(40,256,145,4,5),(264,32,145,4,5),(288,8,145,64,5)]) (IndexTree.leaf [(48,128,332,1,5),(160,16,332,1,5),(208,0,300,0,5),(144,64,292,8,5),(288,64,145,8,5),(320,32,145,4,5)])) (IndexTree.fork 5 (IndexTree.leaf [(0,5,72,432,5),(1,4,216,288,5),(0,9,36,464,5),(1,8,180,320,5),(0,33,72,404,5)]) (IndexTree.leaf [(1,32,216,260,5),(257,0,252,0,5),(256,1,108,144,5),(0,20,72,417,5),(16,4,201,288,5),(0,132,72,305,5)]))) (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(128,4,89,288,5),(0,24,36,449,5),(16,8,165,320,5),(0,136,36,337,5),(128,8,53,320,5)]) (IndexTree.leaf [(0,48,72,389,5),(16,32,201,260,5),(272,0,237,0,5),(256,16,108,129,5),(0,160,72,277,5),(128,32,89,260,5)])) (IndexTree.fork 6 (IndexTree.leaf [(384,0,125,0,5),(256,128,108,17,5),(0,13,0,496,4),(1,12,144,352,4),(21,0,360,0,4),(1,20,72,416,4)]) (IndexTree.leaf [(16,5,72,416,4),(37,0,472,0,4),(4,33,72,400,4),(5,32,216,256,4),(32,5,72,400,4),(33,4,216,256,4)])))) (IndexTree.fork 22 (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(36,1,328,144,4),(69,0,440,0,4),(0,69,0,440,4),(1,68,144,296,4),(4,65,288,152,4)]) (IndexTree.leaf [(5,64,432,8,4),(68,1,296,144,4),(133,0,360,0,4),(1,132,72,304,4),(128,5,72,304,4),(256,5,72,176,4)])) (IndexTree.fork 5 (IndexTree.leaf [(257,4,216,32,4),(25,0,292,0,4),(1,24,36,448,4),(16,9,36,448,4),(0,41,0,468,4)]) (IndexTree.leaf [(1,40,144,324,4),(64,9,36,400,4),(65,8,180,256,4),(137,0,292,0,4),(1,136,36,336,4),(128,9,36,336,4)]))) (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(256,9,36,208,4),(257,8,180,64,4),(49,0,332,0,4),(1,48,72,388,4),(16,33,72,388,4)]) (IndexTree.leaf [(257,16,108,128,4),(272,1,108,128,4),(97,0,412,0,4),(0,97,0,412,4),(1,96,144,268,4),(32,65,260,152,4)])) (IndexTree.fork 6 (IndexTree.leaf [(33,64,404,8,4),(96,1,268,144,4),(161,0,332,0,4),(1,160,72,276,4),(128,33,72,276,4),(256,33,72,148,4)]) (IndexTree.leaf [(257,32,216,4,4),(0,321,0,188,4),(1,320,144,44,4),(64,257,0,188,4),(65,256,144,44,4),(256,65,36,152,4)]))))) (IndexTree.fork 45 (IndexTree.fork 22 (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(257,64,180,8,4),(257,128,108,16,4),(384,1,108,16,4),(0,28,0,481,4),(16,12,129,352,4)]) (IndexTree.leaf [(44,0,145,0,4),(0,140,0,369,4),(128,12,17,352,4),(268,0,145,0,4),(52,0,457,0,4),(4,48,72,385,4)])) (IndexTree.fork 5 (IndexTree.leaf [(20,32,201,256,4),(32,20,72,385,4),(36,16,328,129,4),(48,4,201,256,4),(84,0,425,0,4)]) (IndexTree.leaf [(0,84,0,425,4),(4,80,288,137,4),(16,68,129,296,4),(20,64,417,8,4),(68,16,296,129,4),(148,0,360,0,4)]))) (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(16,132,72,289,4),(128,20,72,289,4),(256,20,72,161,4),(272,4,201,32,4),(164,0,345,0,4)]) (IndexTree.leaf [(4,160,72,273,4),(32,132,72,273,4),(36,128,328,17,4),(132,32,89,256,4),(160,4,89,256,4),(196,0,313,0,4)])) (IndexTree.fork 6 (IndexTree.leaf [(0,196,0,313,4),(4,192,288,25,4),(68,128,296,17,4),(128,68,17,296,4),(132,64,305,8,4),(324,0,145,0,4)]) (IndexTree.leaf [(256,132,72,49,4),(384,4,89,32,4),(0,56,0,453,4),(16,40,129,324,4),(64,24,36,385,4),(80,8,165,256,4)])))) (IndexTree.fork 23 (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(152,0,292,0,4),(16,136,36,321,4),(128,24,36,321,4),(256,24,36,193,4),(272,8,165,64,4)]) (IndexTree.leaf [(0,168,0,341,4),(128,40,17,324,4),(296,0,145,0,4),(64,136,36,273,4),(192,8,53,256,4),(256,136,36,81,4)])) (IndexTree.fork 6 (IndexTree.leaf [(384,8,53,64,4),(112,0,397,0,4),(0,112,0,397,4),(16,96,129,268,4),(32,80,260,137,4),(48,64,389,8,4)]) (IndexTree.leaf [(96,16,268,129,4),(176,0,332,0,4),(16,160,72,261,4),(128,48,72,261,4),(256,48,72,133,4),(272,32,201,4,4)]))) (IndexTree.fork 11 (IndexTree.fork 5 (IndexTree.leaf [(0,336,0,173,4),(16,320,129,44,4),(64,272,0,173,4),(80,256,129,44,4),(256,80,36,137,4)]) (IndexTree.leaf [(272,64,165,8,4),(272,128,108,1,4),(384,16,108,1,4),(224,0,285,0,4),(0,224,0,285,4),(32,192,260,25,4)])) (IndexTree.fork 6 (IndexTree.leaf [(96,128,268,17,4),(128,96,17,268,4),(160,64,277,8,4),(352,0,145,0,4),(256,160,72,21,4),(384,32,89,4,4)]) (IndexTree.leaf [(0,448,0,61,4),(64,384,0,61,4),(128,320,17,44,4),(192,256,17,44,4),(256,192,36,25,4),(384,64,53,8,4)])))))))
def g509autos : Array (List Nat) := #[[],[116],[64],[112,64],[64,112],[112],[82],[116,82],[82,64],[112,82,64],[64,82,112],[82,112]]
def g509levels : Nat → Packing
  | 8 => g509l8
  | 9 => g509l9
  | 10 => g509l10
  | 11 => g509l11
  | _ => emptyPacking
def hashg509l9 (i : Nat) : Nat := 0x1e3cdfa4f4a0160c80020
def hashg509l10 (i : Nat) : Nat := 0xe8801f8000d9801e30002f1812b507e20b8e2ab12eca82aea00000000605c08000cf6a0000010004
def hashg509l11 (i : Nat) : Nat := 0xbd20326150b0981c1045b0071000004390
def g509index : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 3 13 3 8 1 3 (hashg509l9)
  | 10 => lookupWord 7 30 3 10 3 3 (hashg509l10)
  | 11 => lookupWord 4 15 4 10 3 3 (hashg509l11)
  | _ => fun _ => none
def g509 : Forest := ⟨509,11,fun j => g509samples[j]?.getD (0,0),g509columns,g509autos,g509levels,g509index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom509 : graphValid g509 (boundsBefore known125) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=7) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s509_8_0 : block g509 8 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all509_8 : block g509 8 0 2=true := s509_8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s509_9_0 : block g509 9 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s509_9_4 : block g509 9 4 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all509_9 : block g509 9 0 7=true := (@block_merge g509 9 0 4 3 s509_9_0 s509_9_4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s509_10_0 : block g509 10 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s509_10_3 : block g509 10 3 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all509_10 : block g509 10 0 6=true := (@block_merge g509 10 0 3 3 s509_10_0 s509_10_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s509_11_0 : block g509 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all509_11 : block g509 11 0 1=true := s509_11_0
theorem tables509 : checkedTables g509 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g509 0 0 0 = true)
  · exact (rfl : block g509 1 0 0 = true)
  · exact (rfl : block g509 2 0 0 = true)
  · exact (rfl : block g509 3 0 0 = true)
  · exact (rfl : block g509 4 0 0 = true)
  · exact (rfl : block g509 5 0 0 = true)
  · exact (rfl : block g509 6 0 0 = true)
  · exact (rfl : block g509 7 0 0 = true)
  · exact all509_8
  · exact all509_9
  · exact all509_10
  · exact all509_11

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low509 : Lower (vars 509) (graphGoal 509) 12 := lower_forest (g:=g509) (i:=0) (hints:=8642389252) (before_sound known125 valid125) geom509 tables509 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps509 : List (Nat × List Nat) := [(509,[])]
def known509 := extendKnown known125 12 maps509
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid509 : Known known509 := extendKnown_ok valid125 low509 (by decide +kernel)
def g447 : Forest := ⟨447,11,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low447 : Lower (vars 447) (graphGoal 447) 12 := lower_discard (g:=g447) (ci:=(8,0,439,0,11)) (hints:=8591017300) (before_sound known509 valid509) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps447 : List (Nat × List Nat) := [(447,[])]
def known447 := extendKnown known509 12 maps447
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid447 : Known known447 := extendKnown_ok valid509 low447 (by decide +kernel)
def g479 : Forest := ⟨479,10,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low479 : Lower (vars 479) (graphGoal 479) 11 := lower_discard (g:=g479) (ci:=(4,0,475,0,10)) (hints:=8606738532) (before_sound known447 valid447) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps479 : List (Nat × List Nat) := [(479,[])]
def known479 := extendKnown known447 11 maps479
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid479 : Known known479 := extendKnown_ok valid447 low479 (by decide +kernel)
def g383 : Forest := ⟨383,10,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low383 : Lower (vars 383) (graphGoal 383) 11 := lower_discard (g:=g383) (ci:=(0,1,366,16,10)) (hints:=8607786324) (before_sound known479 valid479) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[])]
def known383 := extendKnown known479 11 maps383
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid383 : Known known383 := extendKnown_ok valid479 low383 (by decide +kernel)
def g255 : Forest := ⟨255,10,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low255 : Lower (vars 255) (graphGoal 255) 11 := lower_discard (g:=g255) (ci:=(4,0,251,0,10)) (hints:=17851732) (before_sound known383 valid383) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[])]
def known255 := extendKnown known383 11 maps255
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid255 : Known known255 := extendKnown_ok valid383 low255 (by decide +kernel)
def g431 : Forest := ⟨431,8,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low431 : Lower (vars 431) (graphGoal 431) 9 := lower_discard (g:=g431) (ci:=(1,0,430,0,8)) (hints:=8591017303) (before_sound known255 valid255) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps431 : List (Nat × List Nat) := [(446,[64]),(431,[])]
def known431 := extendKnown known255 9 maps431
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid431 : Known known431 := extendKnown_ok valid255 low431 (by decide +kernel)
def g463 : Forest := ⟨463,7,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low463 : Lower (vars 463) (graphGoal 463) 8 := lower_discard (g:=g463) (ci:=(1,0,462,0,7)) (hints:=8606738535) (before_sound known431 valid431) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps463 : List (Nat × List Nat) := [(478,[135,32,49,64]),(463,[])]
def known463 := extendKnown known431 8 maps463
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid463 : Known known463 := extendKnown_ok valid431 low463 (by decide +kernel)
def g239 : Forest := ⟨239,7,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low239 : Lower (vars 239) (graphGoal 239) 8 := lower_discard (g:=g239) (ci:=(1,0,238,0,7)) (hints:=17851735) (before_sound known463 valid463) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps239 : List (Nat × List Nat) := [(254,[101,117,50,32,64]),(239,[])]
def known239 := extendKnown known463 8 maps239
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid239 : Known known239 := extendKnown_ok valid463 low239 (by decide +kernel)
def g415 : Forest := ⟨415,7,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low415 : Lower (vars 415) (graphGoal 415) 8 := lower_discard (g:=g415) (ci:=(2,0,413,0,7)) (hints:=8589969524) (before_sound known239 valid239) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps415 : List (Nat × List Nat) := [(415,[])]
def known415 := extendKnown known239 8 maps415
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid415 : Known known415 := extendKnown_ok valid239 low415 (by decide +kernel)
def g319 : Forest := ⟨319,7,fun _ => (0,0),IndexTree.leaf [],#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem low319 : Lower (vars 319) (graphGoal 319) 8 := lower_discard (g:=g319) (ci:=(0,1,302,16,7)) (hints:=8591017300) (before_sound known415 valid415) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps319 : List (Nat × List Nat) := [(319,[])]
def known319 := extendKnown known415 8 maps319
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem valid319 : Known known319 := extendKnown_ok valid415 low319 (by decide +kernel)
def g262655d9 (i : Nat) : Nat := 0xe7bb4e4bf6aad0971a0bc6ec96a84678c941e28280a7ee63138550a4a541793b8e78c6542929505e5e639e08550a4a541797a8e7800542929505e6ea31a00150a4a54179f8821800542929505f4d639e31a08548c417d368e78c6800523105f5d239e08600148c417db48c6821800523105f4e639e31a085488417d3a8e78c6800522105f5e239e086001488417db88c6821800522105e4f652a39e31948441797c94a8e7800521105e6f252a31a001484417d3c8e78c6800521105f87642239e31a296087e1e9088e78c68a5800f8f242239e31a086003e5c9088e78a5821800fa7242231a296086003f1c8e78c68a5821800
def g262655l9 : Packing := (24,5,8,0,0,7,0,g262655d9)
def g262655d10 (i : Nat) : Nat := (if i<1 then 0x88417bf49cd000a4420bdfa4e1800522105efd260c00291082e7f639e5294844173fa9c1294a4220bd7d5468e7521105edeaa3c63290882f6f639e319484417b7aa8118ca4220bdbd4e08c6521105efe2a3c00290882f7f151a001484417bf89cd000a4220be3f16a9088e78c6f1f8b2c84473c6378fc51642239e31bc7f14b2111cf18de3f4a19088e78c6f2f8a4c84473c52f97d30642239e297d3f1cf21118d14be9f4e19088c68a5f4fa70484463452fa7d08242231a297e3e2d31cf18d14bf1f1688e78c68a5f8f894473c63452fc7e42239e31a297e3ea031cf18d14be7d1659088e7821f3ec52c84473c10faf639e42231a087d7a9cb21118d043ebd0e59088c6821f5ec52c84463410faf538242231a087d7a94121118d043f3d9088e78c6821f9ea82c73c63410fcf441639e31a087e7b14b1cf18d043edd8e79088a5821f6ea70484452c10fd7452239e296087ebb2111cf14b043f9d9088c68a5821fcea83c63452c10fe7441e31a296087f3b1cf18d14b043f9d5008c68a5821fcea70463452c10f9f859642239e003cfc98b2111cf001e7e8a59088e7800f3f260c84473c0079f928642239e003d7c2cb21118d001ebe4e59088c6800f5f452c844634007af938642231a003d7c94321118d001f3e9088e78c6800f9f282c73c634007cf841639e31a003e7d14b1cf18d001f3e5018e78c6800f9f250c73c634007b7939a422296003dbc9c321114b001ede4c19088a5800faf0a4473c52c007d7a42239e296003ebca0d1cf14b001f5e5018e78a5800faf260c73c52c007e7852231a296003f3d21118d14b001f9e5078c68a5800fcf280c63452c007e7938631a296003df82cb211043001efc8a5908821800fbe484473c10c007df141639e086003ef820b1cf043001f7c8a58e7821800fde484463410c007ef141631a086003f7820b18d043001fbc8a58c6821800fee0b4452c10c007f724222960860032f71cea85252a0b9bb8c6542929505cfcc10aa1494a82e7ea00150a4a541727f29518ca4e20bd3d8c6821527105e9f463400293882f4fa39e001498417a6f1cf18ca4620bd758e7821523105edac63410a91882f5da39e00148c417b6d18d000a4620bdf4821800523105e9dc73c63291082f5e639e085488417b7318d042a4420bd7a8e7800522105edd463400291082f7e20860014884172fb2951cea4220b9bd94a8c6521105e9ec73c63290882e7f252a001484417af91cf000a4220bdbc8c6800521105ede463410a90082f87e42239e31a297c7b2111cf18d043e5d9088e78a5821f4ec84463452c10fc7639e31a296087c7d2111cf18d001e5e9088e78a5800f4f484463452c007c7a39e31a296003cf92111cf043001ebc9088c6821800f9e473c63410c007b72422296086003eb91cf14b043001f9c8c68a5821800 else (if i<2 then 0x4ed075739d1cd4e6072b3931c84e387173891c04df86f73791bb4dd06e336f1b64da86cf35f1a84d386973431974cb065332718f4c406032f316c4af854728913a498049723110b47f03db1df0e846f034f1930c245d82cf15309f44a822b10707c43a81b70cd05c429011f07b033414807b02900a40015ff96b5059294e1efec73a60a90882f7f5381305484417bef1ce982a4620bdf74c14e0523105efdc73a60a91082f7ed305381488417bfb1cea8ca4220bdfd5464e0521105afecb5a70a90882f5f639d385484417cbf1ce9cb14b211b7d4c15411058e7dbeca5280a50c73f8fe42141e39e31b77a9c2a8220b18dbbd4205411058c6f8fc73a72c52c636d7c52639d39a2977f89c2a8220b001bfc4c1541105800dfe4a5280a50c0075de39d39948c416bef2d69c2a4620bd778e74e1523105ebdc73a73291082d7ee5ad385488417af71ce9c2a4420b5fd96b547521105ebeaa3c73a90882f5f639d399484416cfeac228b2111cfe5f4c58a59088e7b3fcb5a50c84473f97e29528642239fc7f1ce9cb21118d6bf5610e59088c6b5fcb5a70c8446378fe39d38642231bc7e9ca9c321118d73f5651488e78c6b9fab40a2c73c635cfe5ad41639e31bc7f210a0b1cf18d73f5611058e78c6f8fa82c52c73c635cfe5ad40639e31bc7f210a031cf18de3f5055018e78c6b9fcb5a50c73c635cfd5a128639e31be3f14a9431cf18df3d5014a18e78c6f2fc73a73484452db7e5ad386422297cbf1ce9c321114b79f5611078c68a5f8fa83c73c63452de7e5ad38631a297e3f1ce9c318d14b77d96b5058e7821f3ec84282c73c10fd7541629639e086dfcac228b211001ede4e58a5908800f6f262c52c844005bfa5ad286422003dbd14a943211001e7e9085068e7800bbf4b5a82c73c0079fa42141639e002efcac220b1cf001f5e5058a58e7800faf262c52c73c005dfa5ad40639e003cfd210a031cf001e7e5055018e7800bbf4b5a50c73c005df95a128639e003ebd14a9431cf001f7c5014a18e7800f5f484283c634005efa5ad41631a003d7d210a0b18d0017be5611058c6800fcf282c52c634007e7939629631a002f7d2d6a0318d001ebe9085018c6800f5f282a80c634005efa5ad28631a002f7cad094318d001f9e8a54a18c6800fde280a50c634005f785a939a296002ff92d6a0b043001efc908505821800fee282c52c10c0067ee39d50a4a54173f69c2a85252a0b9fb4e0542929505cfda102a1494a82f5dd30639d48c417b6f1cf18ca4620bdb74e18c6523105edba70463291882f6dd08231948c417beb1cf042a4620bdf54e0821523105efb273400291882f7d938600148c417bec983000a4620bd7b4c18e7522105eddc73c63291082f6ed386319488417b769c118ca4420bdbb4208c6522105efcc73c10a91082f7e53820854 else 0x1981288c2e44c4610e09226330b31311899845820cc2cc4c4626611608330b0b2118f1845820c4ccd50581410382840090a0b81040090a0b82840e0013333481380054002666690250009858600999aa12c002e001000000000030308000b00081c0020018184060010185040000000002c002e0010000005808416001038004000181840600101850400b00081c0020000c0c20300080c2820058005c002e271bae3c30a772071f8dd238238f3900dc16375c8076001b000d8005c1836001b000b8306c0036001b000c8006400320017060c80064002e0c19000c8006400360017060d8006c0036001b000b8306c0036001b000800a18100000001c102001860400000000000e081001c00263aa0a4923001c1020000060a1001c10200000000000001c002a0a43e2000000000070108000000000000e00151421f1000e001448305446180008dd0853c6e8829e3744e0d1ba2444448c1cc17242ac2460e60b92c1a12307305c981b60d82f8444c1cc0ac191e0e60560c8f07302b064783981560d8324c1cc0ab06c19260e60558360c9307305c583982e2c1cc17158360e60b8ec1b07305c760d83982e3c1cc17160e60b8b07305c560d83982e3b06c1cc171d8360e60b8f07305f0807e03e002f01f001780f800bc07c005e03e002e06f01f001f03780f800f81bc07c007c0de03e003e06f01f001f03780f800f81bc07c007c0de03e003e06f01f001f03780f800e0d104b8114015fb8fbf7cb3de5ea0f337913c75e18f077813bc5dc0edb76b3b15d68eaf74f3a05ce0e5f72138c5bf8deb6ed3755ba0dcb6e33705b78db76d93685b38d976c93605af8d6b6b33585aa0d4b69d34d5a48d1f68d3455a20d0b68334059f8ceb66d33559a0ccb6633305960cab64d3255908c7f63d31d58c8c5f6273125870c336173075830c076012ff57f0be75f12f45798bbb5db2ec5740b8f5b32cc5610adf5672af5558a9b54529e54d0a5752328d5448a1350127c53c09cf4df26b533898b4bd25a52b094749b249522890347923851b88d746323051788b745922b515089744922350f887743921b50d086342f21650a884f41f20e50688233fd1fd4fe07df3ed1f54fa07cb3dd1ed4f6079f3cd1e54f2078b3c31e04ef87773b91db))
def g262655l10 : Packing := (253,4,8,5,1,13,0,g262655d10)
def g262655d11 (i : Nat) : Nat := (if i<3 then (if i<1 then 0xe7521105dfd546521105dfd4e6521105dfd540521105dfd4e0521105dfd4c0521105dfe4c1520105e7f1499088e7e7f1459088e7e7f1259088e7e7f4c59088e7e7f8a59088e7e7f4c19088e7e7f4a19088e7ebf1479088c6ebf8e79088c6ebf1459088c6ebf4e59088c6ebf0e59088c6ebf8a59088c6ebf4e19088c6ebf4a19088c6ebf4e09088c6ebf4a09088c6ebf4209088c6f3f1488e78c6f3f9088e78c6f3f1458e78c6f3f5058e78c6f3f1058e78c6f3f8a58e78c6f3f5018e78c6f3f4a18e78c6edf1279088a5edf8e79088a5edf4e69088a5edf4e19088a5edf4c19088a5edf4e09088a5edf4c09088a5edf4209088a5f5f1498e78a5f5f1488e78a5f5f1288e78a5f5f9088e78a5f5f5068e78a5f5f5018e78a5f5f4c18e78a5f9f1288c68a5f9f9088c68a5f9f1278c68a5f9f5078c68a5f9f1078c68a5f9f8e78c68a5f9f5018c68a5f9f4e18c68a5f9f5008c68a5f9f4e08c68a5f9f4208c68a5efd147908821efd8e7908821efd145908821efd4e5908821efd0e5908821efd8a5908821efd4e0908821efd4a0908821f7d9088e7821f7d5058e7821f7d1058e7821f7d8a58e7821fbd9088c6821fbd5078c6821fbd1078c6821fbd8e78c6821fbd5058c6821fbd1058c6821fbd4e58c6821fbd0e58c6821fbd8a58c6821fbd5008c6821fbd4e08c6821fbd4a08c6821fdd1488a5821fdd9088a5821fdd1478a5821fdd5078a5821fdd1078a5821fdd8e78a5821fdd5008a5821fdd4e08a5821efe4e6908800efe145908800efe4e5908800efe4c5908800efe8a5908800efe4e1908800efe4c1908800efe4a1908800f7e9088e7800f7e5068e7800f7e5058e7800f7e1058e7800f7e4c58e7800f7e8a58e7800f7e5018e7800f7e4c18e7800f7e4a18e7800fbe9088c6800fbe5078c6800fbe5058c6800fbe1058c6800fbe4e58c6800fbe8a58c6800fbe5018c6800fbe4e18c6800fbe4a18c6800fde1488a5800fde9088a5800fde5078a5800fde5068a5800fde4e68a5800fde5018a5800fde4e18a5800fde4c18a5800ffc908821800ffc505821800ffc105821800ffc8a58218009fb542929505d9f8a552610797f94a527105d3f8c6527105d7d821527105d7e800527105d3f8e7526105dbe800526105d778e7523105db78c6523105df5821523105df6800523105d7b8e7522105dbb8c6522105df9821522105dfa8005221059fd94a521105d7d8e7521105dbd8c6521105dfc800521105dbe8c6520105dfc821520105e3f9088e78c6e5f9088e78a5e9f9088c68a5f1f8e78c68a5e7d9088e7821ebd9088c6821f3d8e78c6821edd9088a5821f5d8e78a5821f9d8c68a5821e7e9088e7800ebe9088c6800f3e8e78c6800ede9088a5800f5e8e78a5800f9e8c68a5800efc908821800f7c8e7821800fbc8c6821800fdc8a5821800 else (if i<2 then 0x8a5fdf5014e08a5fdf4c14e08a5fdf1284208a5fdf9084208a5ffd9088e7821ffd8e7505821ffd8e7105821ffd8e78a5821ffd9084e0821ffd5054e0821ffd1054e0821ffd8a54e0821ffe9084e6800ffe4e6505800ffe4e6105800ffe9084e5800ffe5054e5800ffe9084c5800ffe5054c5800ffe4e68a5800ffe9084e1800ffe5054e1800ffe1054e1800ffe8a54e1800ffe9084c1800ffe5054c1800ffe1054c1800ffe8a54c1800ffe5484a1800ffe9084a1800ffe5054a1800bbf5461284e59ff1495074c59ff1494e68a59ff1494e55019ff1494c55009ff1495014a0ddf4a15251079ff545521107dfd4a1521107e7f9085078e7dfd4e1521105dfd4c1521105dfd420521105f5f8e74e58a5f5f8a54e54e1ddf9294e54a1ddf5278a54a1dfd9295014a1fdd4e55014a1aff541127908e7f8e74e6908aff547125908aff541125908aff94a4e5908e7f8e74e5908aff5410e5908edf4e58a5908edf4c58a5908aff94a4e1908e7f8e74e1908e7f4e54e1908aff94a4a1908aff5474a1908edf4e54a1908edf8a54a1908edf8a54a0908b7f5451288e7e7f9085068e7b7f5481258e7b7f94a5058e7e7f9085058e7b7f5411058e7f5f5058a58e7f5f4c58a58e7b7f94a5018e7e7f9085018e7e7f5055018e7b7f94a4a18e7b7f5484a18e7f5f8a54a18e7f7d5014a18e7bbf94a5078c6ebf9085078c6bbf5451078c6bbf5411078c6f3f5078e78c6bbf94a5058c6ebf9085058c6bbf5471058c6bbf5411058c6bbf94a4e58c6bbf5484e58c6f3f5074e58c6f3f8e74e58c6bbf5480e58c6bbf5410e58c6f9f5058a58c6f9f4e58a58c6bbf94a5018c6ebf9085018c6ebf5075018c6ebf5055018c6bbf94a4e18c6bbf5484e18c6f3f8e74e18c6f3f4e54e18c6bbf94a4a18c6bbf5484a18c6bbf5474a18c6f9f4e54a18c6f9f8a54a18c6fbd5014a18c6ebf9085008c6f9f8a54a08c6bdf5411278a5bdf5411078a5bdf1498e78a5f5f5078e78a5bdf1494e68a5f5f8e74e68a5bdf94a4e18a5bdf1494e18a5f5f1274e18a5f5f8e74e18a5bdf1494c08a5bdf1494208a5efd908507821bfd545107821bfd94a505821efd908505821bfd5480e5821fdd5058a5821fdd4e58a5821efd908500821fdd8a54a0821efe908507800efe908506800bfe94a505800efe908505800bfe541105800fde5058a5800fde4e58a5800fde4c58a5800bfe94a501800efe908501800efe505501800bfe94a4a1800bfe5484a1800fde8a54a1800ffc5014a1800d7f4c1527105d7f4c0527105dbf8e7526105dbf4e0526105df78e7523105df74e6523105df74e1523105df74c1523105df74e0523105df74c0523105df7420523105dfb8e7522105dfb4e6522105dfb4e1522105dfb4c1522105dfb4e0522105dfb4c0522105dfb420522105dfd547521105dfd8 else 0x1ca6134bda96992baa53949fa933124da44948308eed1bfa32d45b68a25126a1fb437e855d098a0f5418881c90159fef3fa87ee4fc41f413e367bd4f6d1e9e3cda791cf001dda3b10755ce8d9cdf394671c8e261c0537a86eb8db91b36359c696cd0f99b733226528c8c98e831586194c0f17ed2f785e00ba217082dc45b1cb45964f2c3c57b4ad895752a7253f4a5b147a287c50349ee137426704bf09551279247a48048d7917e225843c085a106220363f7c7d18f5c1e563b9075f0e981cb838806f78da81aee351866f0c6b18482ef05c58b6516522bb45588a75148828204d5897a12662384447885e102e1f403c487370e0c1afc347065d0c16168c2a884ff0918114020483a1065c0bc81558264046607840cd015301d602900340000fff9088e74c5fff8e75054c5fff9088e74c1fff8e75054c1fff8e71054c1fff8e78a54c1fff5288e74a1fff9088e74a1fff8e75054a1fff9084c54e0fff5054c54e0fff9084c14e0fff5054c14e0fff1054c14e0fff8a54c14e0fff5484a14e0fff9084a14e0fff5054a14e0eff8e7908506eff4e0908506f7f9088e74e6f7f5058e74e6f7f1058e74e6f7f8a58e74e6dff8e7929505dff4e1929505dff4e0929505dff420929505eff8e7908505eff4e1908505eff4e0908505eff420908505dff8e7521105dff4e0521105f7f9088e74e5f7f5058e74e5fdf8e75058a5fdf4e15058a5fdf4e05058a5fdf4205058a5fdf8e74c58a5fdf4e04c58a5dff8e7929501dff4e0929501eff8e7908501eff4e0908501eff8e7505501eff4e0505501dff9089294e1dff5059294e1dff1059294e1dff8a59294e1f7f9088e74e1f7f5058e74e1f7f1058e74e1f7f8a58e74e1dff5079294a1dff8e79294a1dff5009294a1dff4e09294a1dff8e75284a1dff4e05284a1fdf8e78a54a1fdf4e08a54a1ffd8e75014a1ffd4e05014a1eff8e7125908eff8e74c5908eff8e78a5908eff1254e1908eff8a54e1908eff8e74c1908eff8e74a1908eff1254e0908eff4c54e0908eff8a54e0908eff4c14e0908eff4a14e0908eff125420908eff8a5420908f7f9084c58e7f7f5054c58e7f7f9084c18e7f7f5054c18e7f7f1054c18e7f7f8a54c18e7f7f5484a18e7f7f9084a18e7f7f5054a18e7fbf9088e78c6fbf8e75058c6fbf8e71058c6fbf8e78a58c6fbf8e75018c6fbf4e55018c6fbf9084e18c6fbf5054e18c6fbf1054e18c6fbf8a54e18c6fbf5074a18c6fbf8e74a18c6fbf4a15008c6fbf9084e08c6fbf5054e08c6fbf1054e08c6fbf8a54e08c6fbf5014e08c6fbf4a14e08c6fbf5014a08c6fbf9084208c6fbf5054208c6fbf1054208c6fbf8a54208c6fdf1288e78a5fdf9088e78a5fdf8e75068a5fdf8e75018a5fdf1284e18a5fdf9084e18a5fdf8e74c18a5fdf1284e08a5fdf9084e08a5fdf5064e)) else (if i<5 then (if i<4 then 0xf037012c06e03c0124a542606e00c2d909224514618c2982d03e038198ca516b0d618c2d85305a07c070370056060904518e04662e689145186b0c60b40f80e0662e9e0a29f830dd24198450787c142241c82e120b1578344882e194bc142ac1c82e120bc158341c82e120b0358f417844462503583417844563ac4b82f038390298f4194703e0d05c329382b14839c18194193312e0bc0e0e40a60d064ec7589705e06c7a0e4173f03e0d05c329382b03629c1a0e4173312e0bc0d8341c82e6065c145a70683905cd0c98eb12e0ac7a0e4173c32e0d05c329219312e0ac1a0e417370382e196101189c1c82f08094768930de07c028f6073a45a3b44b80705e07c0530d1e48ec48bc0f807064bf41cec758960ae07c018f5073d1da25c1701b0d869c0780622a3ca174c37837008425468c758970063d084c2d4a2f00c2980f80f062c38852c7589603e0a8d219701e018898f2859d0ae0dc01109586f05e07c078041e361261bc0f80507c0c6e07c0283a1e2612e03c0f807072bf818f42b82f03e03c010f1b0950ae07c0183e063514c24c3681f01891c0290e064d14a07c078052143c689184b806062425a2940f0970126512380521c0c9c5b38a77136623bc41587930df618dc2b9848307260a8c0c38096ff4dfb8bef97d02f8d5ee9bd877a76f3bde51bc417792ed45d82bab974dae82dcdfb93170eee105bfab7a96ebadbedb57b6636c2ed67da88b4db691ed0b59dab33d655ec8858d4b173624ec36d852b0175f3ebc9d74cae375b7eb62569eacaf5816aefd5b9ab2755e2aaed542aa4f5406a6dd4b5a91f51a6a275433a8314fca9ebd3b1a7174dc29aad33aa6134b8e95ed297a4e3495a9185215a3df46fa8d1d17da2c5451e890d0f0a17f4266839d04da06540327f34fb59f353dfe7accf289e1b3bca76bcebc9d2d39c271fce199be737626d94d979ae3352e692ccff999d327663bcc51985730165f54bc497532e0e5aecb4296392bda56dcac0953529d252cca3e944727ca4e0c99092bf243646e48a090df20fa40147c68ed31cb6378c6aa8cc718ca300c5db8b29156228e44eb898b1226221440687950e921b9c34285f70afe141c231840106e60bec14c8237040206d409380c500c5ff53fae7efafcadf723e877c80f83dee9bd977ab6f47de7cbcc8792ef141e0a3bd87738ed81d97baf3756ee9edd2aba2f73e6e735cce396b7274e3f9c61389170c0e091bf9b7c26f22dd55b8736d26d42d995b1fb60e6bbad6b1ab2b5346a06d349a4b345a6868d00d9e933a166b4cca5976b2b164eac93d90f31e2634cc57d891b0e76140c1bd8092fcb5ef2bc9d775aeba5d12b9357032dd55af0b51d67aacc45910b13160dabbe5704aced5852ace54e2a8d550229d3532ea54148fa8ee5164a1d941d28094f6e9e4538f26e24d3699d53 else 0x9581f05640c518fc1c82e8e0dc00590e52304815c160e432832c80f0285e0596404839194194196405e0bc0e0e41763c582ec78753222325607c159031463f0720ba186417e0c3a9911582705e070720bb2034176443a9901181b1383905d901419325e0ac805a31f83905d10cb82c1c82ec78bc18594191b44e00c785e0da20321650720bb202b04865c160e4176406e030645a320240d82f0819111859452b6875241585b09424c28ad9585f012be8752417802542c0c8888970ee1262787b8095f3f00616c84649984b082ca8d18a21ee02c0f8028868ba1d4c78ad9686b0328bc0303b1e30ba1d856c6c0f80b1ee003b0b81cafb1e1f011d857c63b0a2b2063fc0110998f7004423b08c1380f0063cc80ac0f80f001d8c80bc00b02216404e009948e948251da24c289a51ee00994ec5f0391d290461ac2984b0826847b03f00420523ac5c892652d1da24c349a51ec0ec5cec2984b0826847b802213b0d612c209a11ee00884e3b3808b50bec78a1fe86c45627c078031e387fe011818f3222b03e022d422966640c898ff004f00616c846c1380f0063cc80a3ab80322640424cc0f808b5e00c85901d22b0be03c008e948330be0297c8e9482b1c4c024c897c4c1caa260644460ac1181f01290980dc0185b2118b363898069912f8b808ec16685d8f1581b1ea0e980941d2fb1e1b0dc142cf8050763c663c485300d868b348ac818ff00242760741d303202304e03c018f3202b0d167c0090b20290d1745158f15b2f01e008d18f105d0b52b6360a95780f0016a920c8538095f63c4e022d4af8d82701e00c218f1582f01e002d590168ee14a24c285c603a3dc058ca586b0a612c21828b723d80f80f00511d428c7024b172d1dc29449868b8c0747b80b174f001745946c292af01e002e9241859b19842c789c078023463c4175c058f7001665468c258401362e594cc352af01e002cd24185d42162ec789c07800b316446142eb804216405609c078030863c561a2cf804216405166590af8cb215f10b3e022d48bb1e2b054abc04b02482f0142857d8f1380f00468c788c1701f012c0c80ac1380f00610c78ac178016043cc88a8b585b0ac0c56cac1780f002b6879241986700c0c581911586313e03818af9780f00492950981b80313644424cc30b2a48629c0581f00c0c9614c4f80c1e6325614c1f8041e644561ac2d85313e0307b801d85b1c83ec5c8c3582f0083cc88ac3589f0183cc5cac2982b14607c078041e3e06e00c2d909186b05607c059170083c7614927806062ca5615c0283a1e490561ac3185248c0d41f801d16a1020ac5f03165330de0141d0f2482b0d49341f033172b0c614923806062426e03c0124a54230d618923806062426c0cc70b00f031642be360b81b809604905618c0703160644561bc010f322230c60ac0) else (if i<6 then 0xc436840e1a50c150024ac3064745ba491a3461942874128f508191e2114138012820b723f0a094128f508190d14342c657c85f00190a1328b46434a28886917824321a51444348bd0518a16174286499868899925e00322855a168e24c2d1513a16222642f800c2430a1323a2742c44cb800886945114521ac0281922211c19912083991106013c41d2338508aa200b178157807010902d4fc05100601144179c078022016a50f82fe0f0b525031d90785f9076701e010785a96829452b7076241419325e0ac805a31f83905d0c33807068382d0a0c85941c82ec80b43682f01e00474a4185a8b3e031108bc4830d98aa33a2413018ec17e95083b06f46018ec0abc043004816a6175c048e8602925a0bc023011ea4451d816caa0b5270117433863b0a270119c520b41780f008b6474a41885f0123a17ca49476306e0245c5a97800eb6443e03c00ab1482701e00510a49081f01e005105a94830ece03c00990b52d031d9c046715428ec2aa40f80f002902d4e3b38093219c41d82d780d210bf480c42e0ef0109057cb404b0165a444069078a015f215f2b62a0057cad8c85e1de038488c932370160057cb01186a5422ec8890d0848a028b40cad9a82d038a8470b01512945a0656c80968a7012ca53b80132394504b40c801532b6644b42e84945825c07801324034264450857012c0628a398ad94820baa0c5143295b28b3e02478af8ec28ec23bc00329492b0ae0181c8e94828b32be56c62ea8015f2b6428845c3294821252124238091916461d8513808cc290528a4007315b2905215c04a21602905a1bc030391d290517581c8f160214523b81c8b94928b3e02c00af9602b06e023b08b8b3294517856c7c045e16019552063a8a415b290316656c7c07801562904a063a8ad9542701e004ccaa13801448422cca417808ece004c85994800b323c56c83b0664212a842aa3b2108cc2905e023b0990cc210ae023b0b010a28ba2b748083b380f00167480a2d459f0123b05ca4988591de0217ca4948e8ec17e52084d380b2123c980a1fc5f8b41d0de0047a911380f002ac5208558760bf2924267c045a8b3148478dc07801332a8419c4805a15121121d82fca3105d1458aa56e241459f0123c57c5a94599402be3175400af95b20ba23c500af9059b002c857c82d459a55e0245d2418a28ba2b748082d459f01149480b414a2e062b7120b81a809602cb488b818af95b1e06a0057cad904f701c0c46499170370160057cb01586b05c0dc048ba48330d61845f03322289e28b81a8195b2d0ca0b40f0311c2c06c0c5168195b2448a2843380965c0dc009920a290ca064630315b342da1651780e06e004c8e12099114c0c42b80960385581b05c243222c0d82e151911206c17844c788c1206c17844c80bc1781c1c8150658f1b8031e1683948c else 0x21290cc16914889492d00619814a4948660bc26424a4e705e13240a63a2811a103e50ac2636014321a0d1320da190d091168030c468483c42f0260828a5c08c030f608a0a543c42f02513c10543c42f02300a27820c42b02434c3e1a4a87885604c1144cb8118061ec10424c4370261e850528b8118061e8505c03197058d0f208609c0488344060b1a5f417c006075850a01880c16c286c4e2fb1e8b64e02c818f8b38be5608c4e2fc5b640516716d900f002256183466897800d0f208609c00889d047001c0be030661931d2906816c11847018330c98f147420d48a281885d2f8e801256183266497800c8f108609c00849c84700192521942c6478843061c45816c762da482c45816c118f45b4aa64188d04879043061c456189222d9222b0463d16d2a958530763315a241585b05e03c022b448321de028522244962e661ac1d8bc56890544cc3440cc12f00181d10312470ce128982b0486499067248340d8b10c98ea482b0060f0c85ab202c0d6091621931e4aa68308d18f45b2304830c7a2db202a0c468243c821830e0a701814c32300483414609c06053088c0c78e4948650a192521942c64958650a190a16a22142d444309a0886134110a2114186478845061d04a3d420644c84506191e211418642a8408850b5110d28a221a45e828e89d0b1113217c006875850a01d13a162265c004434a288a290d60140c849586d0c1d0024ac30647441312192561942864309a08760bc268324cc3444cc92f00191d224c284110850b311452644d064309a08995081504a3d420647884504e004a082088fd082504a3d420647884506191e21141862f284089310da10324e423800ca420528d4208428598892d0c124561b430649486507a1642184d0449586889330d110c268221a422830e8251ea10323c42282701211e211418644c84506190da10224)))
def g262655l11 : Packing := (464,3,8,8,1,15,0,g262655d11)
def g262655d12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x451f903e1c7a30ef11d74396c6f90d891a90341c63b0c0d175c2ddc5870aaf14c828144d8095111f8231442407e90f281d2437a06810c8017fc2cb05690a5013ec25d0483089810541e0038906900bf41540271044c071c0d20159021c035c05000550001ffe42239fffc73a837ff9084e6fff1cea0bffd399417ffc73882fff4e6105ffe2509cbffe421397ffa83272fff5054e5fff21098bffd41d317ff883a62fff8e74c5ffea0a98bffd395317ffc73c52fff4e68a5ffe24ea03ffe39d407ffa72a80fff9084e1ffea0a9c3ffc415387ffc52a70fff9084c1ffea0e983ffc41d307ffc73a60fff5054c1ffe20a983ffd395307ff872a60fff8a54c1ffea50943ffe421287ffa93a50fff5074a1ffe20e943ffe39d287ffa82a50fff4e54a1ffea40943ffd315403ffa60a807ff4a1500fff2109c1ffd419383ffa82a707ff1054e0ffe98a9c1ffe295383ffa80a707ff4c14e0ffe9429c1ffe421303ffa82a607ff1054c0fff14a981ffe421283ffa832507ff5054a0ffe98a941ffd405283ffa60a507ff4a14a0fff210841ffd415083ff882a107ff8a5420bff252a0fbfe42141effa92883dff521107efea0f1cfbfe42141bbfc73a735ff929505dff210a0b7fd49c416ffa90882dff9294e5bfea509cbdfd41d397bfc73a72dff5280e5bfea421cbf7d416297efa72c52fdf4c58a5bff252a03bfe4214077fa83a80eff505501bff2529c37fd4a1387bfc73a70f7f4e54e1bff2529437fd4a1286ffa93a50fdf4e54a1fbf14a943ff54052877fc842807df8a54a0dfe24f211bfe39e4237fa734846ff125908dfe9cb211bfc3964237fa62c846ff8a5908dfe9c3211bfd3064237fa50c846ff4e0908dfe981211bfd2824237fa1048477f1288e7eff2111cfdfd41a39fbf892c73f7f5058e7efe20b1cfdfd31639fbfc52c73f7f5018e7efe9831cfdfd28639fdfc844637bf5078c6f7e20f18defe39e31bdfa82c637bf1058c6f7e9cb18defc39631bdfc52c637bf5018c6f7e9c318defd28631bdfa804637bf4e08c6f7e94118defd08231bef894452fdf9088a5fbe24f14bf7d41e297ef883c52fdf8e78a5fbea0d14bf7d39a297efa80c52fdf4e18a5fbe98314bf7d402297efa70452fdf4c08a5fbe84114bff6422087fea83c10ffd107821ffb1cf043ff5416087fe882c10ffd4e5821ffa1cb043ff6296087fea80410ffd4e0821ffa941043ffa422003ff283c007fe506800ffc9cd001ff9416003ff082c007fe4e5800ffc98b001ffa296003ff280c007fe4e1800ffc983001ff9286002dfa93083d7f527105b7ea4c20b7dd48c416fda91082dfd521105bfca4020b9fe42239f5fc8446373f8e78c6dbf21114bd7e39e297cfc63452efd908821efb1cf043ef631a087eec52c10efe908800efd1cf001efa31a003ef452c007fc821800 else 0x1951e321a856078040e8f190d4290940d1249b06c00b357e075a128400b81e0c8b8ca74350a40d1f3b3004814881d2a2e0703a2e8f155f4350cc0d45c1a0745d0852125e2258060cb004284350a4cd2047f0055021421a849d8892658060c66042942902c0f0058207480e8223d81e0103a4063b10d40f002cd1781d20421a8560010a405c14b3c191c180b82e067560c320be642f05c04b319017478e8ea267529180a3c301d0b3b303c045f478c86c1582e0780e008f1d0c40706181222a1b801d466a3c91190c45103c070648460388a86a670520782e029023f80244aa30ec42ceac1b00484c7560780e0e3024064111e82b03c0700c1d20421a756009124054510d40903c060ac01214812a2a18854070a6025ae0d10a32a8510d42b0159300c1c5556c485028afe03112328f1a14c1701c0034478c1a21a85a1484a2582c06afe038060c59ab6e0d01442508c1603c1a1447117542886a158096b800ab83890957f0188917478aafa1a86406a2c2980e0d10a2ea8510a40a03c07005822148128260b80851804448f1e144360340b012d700885204a8a8542582e0780c0c8ca09e42b0159300c1c1e56c48493c8520f09600b040c91210d42b0007922285a86a168542582e0780602b0ab703302d8481042f05c0e06471174a1a4f21580e018383c24210d84b0027917819223a1b0928b82e0780c0c8ba10a4521240f0159048c012156e065a2980893802422a184844e12c0206488c86c2582a0780890996009140ca17c190881e20ab82e0c240380b980dc1817088982e060e015830326c1703c181c05ca1960b830380b9705c0c1c05c202c3b0960a86e0780e010f230343706c02072a3a896078023d039845c1703c0306c045f3a3a8960b0560780e008f230382b06c01072c070a21b80e0d80442747512c16030d301c0222479383600108e03853010cb06c02213c2486e0b81e038040c7c1703c0700078b096078020f03161242b05c0f01c02063a290920780891802430322049403d7fe4fdfdf9f3ee97d3cf99df183ddb7b34f565e8c3ceb7940f155dfb3b9776c0eca5d653a897404e575c7038637044df85bd537736e50db4db4e365b6c20d73dac2354d69f0d2b5a2c340d67acce7d9b9333165b8c9f591431ab6298c40585130395ff0be3d7a22f035d98ba2d7252e135ba4b6456ad2d1959c4b20d60d2bc556b8ac6d5632a8f549ca7bd4dc29815294a425469287350149f253c427334de49a9d32e25f34b64954d28424c7490c911520723cd46f08c65162226f443486c50ae212541a0823d0221ff93f487cc4f781ea53cb4779ced31d2939a87274e291bfd37506cfcd6b1a8b34086694ca318d330ac6054bd1174d2ddc5ab4b3615f92b5c553ca8c14c328dc50649dd136f265c4b64951126b2454477c8ca1153221043448481) else (if i<3 then 0xaa664424f140b3ab0084d1e368c09c167560c8b9646c9d0c403060c8ec2fcd0601b019d9830c8671c32154d9120ce2c6419429808ab838903020ec05203c0621478ce3c1b82e0319445800688f210c400321f306190a438aa191b22419c53643288520338a8a44030126404ceac02202ec933264818648a602908c110214542a0487b03c0707466204a1404409802c083c3c45201e4350b42a04c1526c0f00c055f88181282085c0982e068e22f10250d8130045d14878933a1b0243ca2e0780e0e8bc40942a048791440f01c01604862054090f227800aa49990d8121e40d14c0532c012188147504d80ac88cc405d1c2b40301342202ccc084368cc405a142b3ab0145e202ccc76239838c11016a61970188060228a0b8f82f8c9101486416021fe2029093360b808c11016a504cecc00b3880933424191b22399c58510a11603c04b588519881286a150a0bf01e03802c110c40a120100530580d1c45e20442906a1a13c0780a8b10a2f10280bc14451105b120d0ec910981a5d08b0f0b6802cb3c041e17ca2fa280ee020c89262050ac0564c03070755b121306403830c111160d82b0007a222e0a59e0c2f8b65c16002eb0617c5b360a220380b8905094090230545306c04190c921301805c1580e00760885f890a003051144416c48301582e02220c0241a0d2060ac0700c1c1d121042e0780e0e0f0c0602f05c046407417124f82a002f96780e0c301d0d42d1347f013b0644814805d4860be22e0c0ba4460940902305853061160316d3064290183983442301f0500c551144816cd8288b01e0c598b6685305c070015848340622c262d8a8585305c07001104930065ae0059e028b88824200d03301c14de88b06c003248180008b82c07831662da21403603c070033a2115101900780e00760aa5f890817e0982301850dbc1864c003250280560a191d9836023022132e84516e2028f906e038188b8382f10200d42cba1145b478c22c1b82e0780e008f1d05117003b0d2479223a1684a1182975832142da0ec03514c051fc1f0037920181485a1675607808be8f190cc007f18706181223a1982e067560d808be71153383503c17014811fc0122551675226766018324464c80d4251211514c0503c0306484ce62088f41b81e038060e9020453ab00489202a0b80606766023024074504540f0183700485204102afa1782e020ea322420254294587612c1703c061e465412c3b0921a8520f802c10f244a42d45c170107517120e12a1a85a1582c3b0960780602b0c3cadb41d42c12c17038821f47117490212a1b0ec24856010f244957c254361d84b0551703c061e45d68543b0928b82a0780891802450f2b6c0d10b8830087d21321b828690ec2481e02996009143cb5150c42b033b306c0065421a852068fe00902c0a440e9014ecc0f0 else 0xa2a1422e0b81e028cc3c80960a82f0098207478b7404c029d50a43c8c9c678360b82825c1703c03019865b47962f8178023c599c660941282f05c0e1c85d1f404a0e8248a23d0c9b473b301c00542d4a762390f0c05a94e61940b27b01878602cd00b8be3e43c32148683045c1a1417ce331cc4f60c5b8c0719a144785f388812c1b8042f0a23c701e0c8141717f0638ca439cc4f0180540a3fe0c7014890960d43645c1703c06174792752288f42e6c94142f11e16cb52c1522c2980e0183cb61a23c9c1455c0460120b530668516a1360b01e02b24410fc452a232d0cc254350b42b058820357e1fc07009255b950b3844a0e8280960b0184b104290fa388bb045436030cf05c04b58821f88a5445d9059d5834268c9c6604cea15700120e331d90a23c8c9c4582f0084d1e380a8601709e0183166719c344250802f0684d19369076))
def g262655l12 : Packing := (211,2,8,9,1,15,0,g262655d12)
def g262655d13 (i : Nat) : Nat := 0x180a22c1607068086500d050508b050fc0600202d92165f05c1607010c878e0d05416070180078e0d060280f0083180448068284a1d094003c224034160a0484a0b03804060c612db016090441607060e05d00d0a02a0a1f80c004048482e0a4581c042e1e3834180a804184462f8341905819160d010ba41a0a048488a1401c0601061096d80d050cc0705808803f001115161380418444068242505018ca0306800894450503603038041cb62048103d0380c020e203834150011080a0d0540e030083880e0d0505007018008440882c0c1b0680c00c1d09416070180078f03834000e482c0c150680c00c030a4060d001098250581c060006378ae45b7b4d64dc0163ea14ec9511b60bba667cc555b2604387a8d315923c36858876076003ff908ffd41fff107ffe39fff506ffd39bff505ffc417ff4e5ffc397ff4c5ffe297ff501ffd387ff4c1ffd287ff500ffd383ff4c0ffd283ff420bfe4237f8e7efe31bdf8a5ff6087fe800
def g262655l13 : Packing := (27,1,8,8,1,11,0,g262655d13)
def g262655d14 (i : Nat) : Nat := 0x140c180400bff
def g262655l14 : Packing := (1,0,8,5,1,0,0,g262655d14)
def g262655samples : Array (Bits × Bits) := #[(0x2e280050043404408201a14480944800200050414a09024008228000114104004113040040042000a002220203124229000c04005002206814014180440018d2ab90050b2095b50b05c8c89421b4c606a4dd3525b4233382b085fc040c89f,0x8890482000270420e02c520c002400588850106a016002c48800200010012018a146229100000212000838111500a0152b016701cc971005b124afbb402f5c01892a990050b0011b10b01c0c88421b44604a0582025b4233302b08598000888c),(0x84781d4020ac2015a112c000c30400120044710000200f07524b0000d9ea820200824088968099100810058800038091c529a00c0962e1814050a54ac2022b66042283aa39a181438a35229002d116a700c6833c28b5951b81a680d32898a860,0x41a102e040002544165001c04c84302005c28306826080c8011f6400a4010d285c2130080062080700794e06080080a3014000041b10242848899610002044040282a039a081418821209002d11605008601302831941b81a280d320182820),(0x1010031584200080aa0000000823228358008c029c8504080300c900214418891300840002002045080a04082480800104004103488140c9124000020980114c5c186b9645d3aa529281d9819490740965d70621fa10821b4930a6117916920,0x9464000aa3c302065040009c9e8810089056905642a0088a1021052020a8800a2a6004ee0b0b0880b1895f24009880af7b514a9015b80826019815448201b314c48184b9401d3a852928119809490640805470621ba10820b4830a4111916820),(0x1a80000800101080100513412810408100318212c003002800047106040008040a4126030940442885604a000110044a0802032182100250200000a0052080cac2457cb48a38999151d076b92018fa0d888130560a6354c2c07867c1899216a0,0xa0108118988a45668050950cd8acc421300b028001100002c4141707408343820c0129c3869a221301205905a17903a8274d6ce1371c28a4c00a014441822642c24564b48828191151d076b82018da0d808120560a6144c0c07040c1899002a0),(0x60024084830087600400249400010444080204011200a0802c0000680000246160001114600a2082220410235c8001240284084240010002020b4005000050b16611265181402669196a7292d6a580d14991587084b0b9c08f611496c018664f,0x1000278211c029920e130043108256230024c010181b401050819204cb264d010428804ef2080c0dbfc3454e0a285d80808490062268e0ba48c900043780a0b0260126518140266009426290568580910991587004a0b1c08d00048640186443),(0x5d01721021281700e008200120a200520c78e809000a0191d00081e21c0302943880c006b180010081a49c820e4a001008540411008c0449343f0220c32c0238fcc421d04a57108e92c764240203b81c0f8805870e65c481100988f22c930c,0x40510014509000088600000103040908002000081431230e008008000420010318000424040700348091a1615f50042ca463e204e0c1c407600145fe0402307c40008042401002904664240201b81c098805840661c000100108c220930c),(0x9020100020940080110301404a14401200318100c022040c4202710009a28004004162030040081801600900011004530423a3008260018000408088800083e19314494d03f0449601048117148a64827ff8de09198e2858340b9b440547b4c9,0x4022022400001008288120a025010844058000081000024901820088031018100000420041451164f8df86b05886fc5758b2931ec8e0c75b17b57629ae7dd9a1111009490250448600048107140220827f78de09118e280034091b0404479449),(0x6400ae048608c420e018c48e94490d00884004041614011208098240104130712086002cb00e31c02a1e10017ca1b080e114088a08066021048a00515a04101e6017004e060b4800628921466b359808a520878bf000aa84265453091dd70b30,0x4208104000008240100029200000218006000000a0041c20206800132050928002000000002010a0403482a0e0d7026a547a08f811000f40061250408850020a4014000e060b4800620801422120000884208209d0000804025453001dc70310),(0xb84000b4843180a0a441a2120a290a96788023a20c9506001a40c17240048880f088c0009114625d4014254004442080840503124981a58b8001a200579048819081a92ac04e426a447886bb6e60015c3122528006952375980e43604670050,0xa0b10804020a00901a0000220122802022020000c05a10400000010104000401000c000304040084e42204a5e0620008082110c084317183a608aba3800488809001a02240084228407880392a4000043020508000812170900a43604460050)]
def g262655columns : IndexTree ColumnInfo := (IndexTree.fork 118 (IndexTree.fork 59 (IndexTree.fork 29 (IndexTree.fork 14 (IndexTree.fork 7 (IndexTree.leaf [(4,0,507,0,13),(8,0,503,0,13),(1,0,510,0,12),(2,0,509,0,12),(16,0,495,0,12),(64,0,447,0,12),(17,0,494,0,11)]) (IndexTree.leaf [(72,0,439,0,11),(0,1,366,144,11),(0,16,366,129,11),(32,0,479,0,11),(0,64,437,10,11),(128,0,383,0,11),(256,0,255,0,11)])) (IndexTree.fork 7 (IndexTree.leaf [(5,0,506,0,10),(9,0,502,0,10),(1,16,366,128,10),(16,1,366,128,10),(128,1,366,16,10),(66,0,445,0,10),(2,64,437,8,10)]) (IndexTree.leaf [(12,0,499,0,10),(20,0,491,0,10),(36,0,475,0,10),(68,0,443,0,10),(260,0,251,0,10),(24,0,487,0,10),(8,64,437,2,10),(264,0,247,0,10)]))) (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.leaf [(128,16,366,1,10),(145,0,366,0,9),(129,16,366,0,9),(144,1,366,0,9),(74,0,437,0,9),(10,64,437,0,9),(0,4,219,288,10)]) (IndexTree.leaf [(0,8,183,320,10),(0,128,364,19,10),(0,256,211,44,10),(3,0,508,0,9),(2,1,364,144,9),(4,1,362,144,9),(8,1,358,144,9),(65,0,446,0,9)])) (IndexTree.fork 7 (IndexTree.leaf [(129,0,366,0,9),(1,128,364,18,9),(6,0,505,0,9),(10,0,437,0,9),(18,0,493,0,9),(2,16,364,129,9),(34,0,477,0,9)]) (IndexTree.leaf [(130,0,381,0,9),(2,128,364,17,9),(4,8,179,320,9),(8,4,211,288,9),(4,16,362,129,9),(32,4,219,256,9),(132,0,379,0,9),(4,256,211,40,9)])))) (IndexTree.fork 29 (IndexTree.fork 14 (IndexTree.fork 7 (IndexTree.leaf [(256,4,219,32,9),(8,16,358,129,9),(40,0,471,0,9),(64,8,183,256,9),(136,0,375,0,9),(8,256,211,36,9),(256,8,183,64,9)]) (IndexTree.leaf [(80,0,431,0,9),(144,0,366,0,9),(16,128,364,3,9),(32,256,211,12,9),(3,16,364,128,8),(18,1,364,128,8),(3,128,364,16,8)])) (IndexTree.fork 7 (IndexTree.leaf [(130,1,364,16,8),(21,0,490,0,8),(5,16,362,128,8),(20,1,362,128,8),(132,1,362,16,8),(25,0,486,0,8),(9,16,358,128,8)]) (IndexTree.leaf [(24,1,358,128,8),(73,0,438,0,8),(136,1,358,16,8),(81,0,430,0,8),(17,128,364,2,8),(18,128,364,1,8),(130,16,364,1,8),(40,4,211,256,8)]))) (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.leaf [(76,0,435,0,8),(68,8,179,256,8),(268,0,243,0,8),(12,256,211,32,8),(260,8,179,64,8),(264,4,211,32,8),(132,16,362,1,8)]) (IndexTree.leaf [(292,0,219,0,8),(36,256,211,8,8),(288,4,219,0,8),(88,0,423,0,8),(136,16,358,1,8),(40,256,211,4,8),(328,0,183,0,8),(320,8,183,0,8)])) (IndexTree.fork 7 (IndexTree.leaf [(0,32,217,262,9),(33,0,478,0,8),(0,65,292,154,8),(1,64,436,10,8),(64,1,302,144,8),(257,0,254,0,8),(2,4,217,288,8)]) (IndexTree.leaf [(2,8,181,320,8),(2,32,217,260,8),(258,0,253,0,8),(0,12,147,352,8),(4,32,217,258,8),(0,68,145,298,8),(4,64,433,10,8),(0,40,145,326,8)]))))) (IndexTree.fork 59 (IndexTree.fork 29 (IndexTree.fork 14 (IndexTree.fork 7 (IndexTree.leaf [(48,0,463,0,8),(0,80,292,139,8),(16,64,421,10,8),(64,16,302,129,8),(272,0,239,0,8),(96,0,415,0,8),(0,96,145,270,8)]) (IndexTree.leaf [(32,64,405,10,8),(288,0,219,0,8),(256,32,217,6,8),(192,0,319,0,8),(0,192,292,27,8),(64,128,300,19,8),(128,64,309,10,8)])) (IndexTree.fork 7 (IndexTree.leaf [(320,0,183,0,8),(0,320,145,46,8),(64,256,147,44,8),(256,64,181,10,8),(19,0,364,0,7),(67,0,444,0,7),(2,65,292,152,7)]) (IndexTree.leaf [(3,64,436,8,7),(66,1,300,144,7),(131,0,364,0,7),(13,0,498,0,7),(37,0,474,0,7),(69,0,442,0,7),(133,0,362,0,7),(261,0,250,0,7)]))) (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.leaf [(8,65,292,146,7),(9,64,436,2,7),(72,1,294,144,7),(137,0,358,0,7),(265,0,246,0,7),(49,0,462,0,7),(1,80,292,138,7)]) (IndexTree.leaf [(16,65,292,138,7),(65,16,302,128,7),(80,1,302,128,7),(273,0,238,0,7),(1,192,292,26,7),(65,128,300,18,7),(128,65,292,26,7),(192,1,302,16,7)])) (IndexTree.fork 7 (IndexTree.leaf [(2,12,145,352,7),(38,0,473,0,7),(6,32,217,256,7),(34,4,217,256,7),(70,0,441,0,7),(2,68,145,296,7),(6,64,433,8,7)]) (IndexTree.leaf [(258,4,217,32,7),(2,40,145,324,7),(66,8,181,256,7),(258,8,181,64,7),(82,0,429,0,7),(2,80,292,137,7),(18,64,421,8,7),(66,16,300,129,7)])))) (IndexTree.fork 30 (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.leaf [(146,0,364,0,7),(98,0,413,0,7),(2,96,145,268,7),(34,64,405,8,7),(258,32,217,4,7),(194,0,317,0,7),(2,192,292,25,7)]) (IndexTree.leaf [(66,128,300,17,7),(130,64,309,8,7),(2,320,145,44,7),(66,256,145,44,7),(258,64,181,8,7),(28,0,483,0,7),(44,0,211,0,7),(4,40,145,322,7)])) (IndexTree.fork 7 (IndexTree.leaf [(32,12,147,320,7),(36,8,147,320,7),(8,68,145,290,7),(12,64,433,2,7),(64,12,147,288,7),(72,4,147,288,7),(256,12,147,96,7)]) (IndexTree.leaf [(52,0,459,0,7),(84,0,427,0,7),(148,0,362,0,7),(276,0,235,0,7),(100,0,411,0,7),(4,96,145,266,7),(32,68,145,266,7),(260,32,217,2,7)]))) (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.leaf [(324,0,179,0,7),(4,320,145,42,7),(68,256,147,40,7),(256,68,145,42,7),(8,80,292,131,7),(24,64,421,2,7),(72,16,294,129,7)]) (IndexTree.leaf [(152,0,358,0,7),(280,0,231,0,7),(104,0,407,0,7),(8,96,145,262,7),(40,64,405,2,7),(64,40,145,262,7),(72,32,145,262,7),(296,0,211,0,7)])) (IndexTree.fork 7 (IndexTree.leaf [(256,40,145,70,7),(200,0,311,0,7),(8,192,292,19,7),(72,128,292,19,7),(136,64,309,2,7),(8,320,145,38,7),(72,256,147,36,7)]) (IndexTree.leaf [(264,64,181,2,7),(16,192,292,11,7),(80,128,300,3,7),(128,80,292,11,7),(192,16,302,1,7),(32,320,145,14,7),(96,256,147,12,7),(256,96,145,14,7)]))))))
def g262655autos : Array (List Nat) := #[[],[64]]
def g262655levels : Nat → Packing
  | 9 => g262655l9
  | 10 => g262655l10
  | 11 => g262655l11
  | 12 => g262655l12
  | 13 => g262655l13
  | 14 => g262655l14
  | _ => emptyPacking
def hashg262655l10 (i : Nat) : Nat := 0x45f085ce49282eb7c0000000000174002e3c126e00000c32a77c8009bf81e284600000b3400e0a13b178baa29050000000000030e55a14e0e51002a400292c3eac0000000347c8400f99d5caae223200801313311
def hashg262655l11 (i : Nat) : Nat := (if i<1 then 0x1f9844fc30700018a90007a82e9e41f10d8beab7a40e47b72ca16690238b1689d6aa564c976e41b1b31f75f07699cba30003c0e5e625300019908da2deb52444068729e368321dcb80004718000921717563800320e0002da0000175c8ba6061671c53a60006b1acfc000000000000028f000524d34be710002d1a07ccb7dd45de51bf8ef00028140014d641efd0bb0be4e43500009a447600000000016746955e1933a33ccad883485200000005f3ca8e7ae55fa6e44a000cd50003af696f63c3af3177a0900025280c2000e9cc8c085a7890000000000b4952e8001bcf704753f354000000d7e6498664d3bf700002f5cbac0000000001d51122800000000037a0000000000f4d0000000000719db4f8cc00000000002a13473300003111f2c46b80000012ec00000014d00000000001c48c37f246088001a6e00000000018f0e9f800000000000000004a56bf0007a30c460000394513e6a46567269df468c2ed979b45582998d2b9d8a95a0017093adb11bc4cdd7d6e2a8180a3aa37a0143a20664985293e0003bec98c0012389c1ae700010060d8000000000090f3d34d02a4bb159c440000000c77cda5f60000002885e110f868c00031ee0ea6588681e38d00dd48000000000a48ea5c0004cd9d9800000063a0000000001fb200000000000000007c7636a00000000024ab2e98733b6cec39a400000001cb884b27abb748359eefd422bd854bdef618587ec4a223ec9c0017c804010e239724957db800267caa3f0c8000add01016a32f95dc58f121b80c774000e789b73463807fc80000001617000754c968d05139800167a14e92f0003d0c0000004a9800005b000733c3360004528003f560000003e4d48d17ab3c80037771bcd5454c0000000e84ec3d0f8000e428000001e420003a260de72d00030a800089d11e5bd40000008d3800000000094c80008b0000d348000000000000009f8f6545000000304c00000051fd095133e1c80031545970000000000ce704900004640000005811492aac61dec8ad5c1f479bf14782a0008141a590cfa5f0000000290ad97650000000000164014248e5520000000000923000030c000000f16116800000000000030ea00000039886030988db444af5bd347976e340d80001d08000000000e1f8003e9979f000000000000000051ac001538d17d478001044b414c19a970c407ce4ac00000000078d4000ce8a5c03c80000000000001f62000370a314001aaf56d000000000016eca0c160a9ca204b2c00141a49d0002c18e4d000000000008e308f8db1995e90006d078261816043062d284101091020003c000000a100200440002c691008028000194c02868500461300213840140c0000c05185d41008419880398800480001041080a1014080080001c6a10dc00b861104502142138a6032000 else 0x28000)
def hashg262655l12 (i : Nat) : Nat := (if i<1 then 0x403c0000001e08d0d40a40001231f6b000043a4d6800000000002c3a45f400000000000001cac2268000000017c2159ac8000016e3e9b8d0f69f480a0e44f18e435c196c419b000000093774cb1134000c66919152a4cdbc904000a458000000000080dc000000208d21240000001979012f96200000000002cd30000000001c000a584000e1e8000c8c82c6aa9000000000000000450e12862e115269400000000000000fd18934526c0000001cf90003aa5000180906c0000000050a8eb8000000103408a8000a38f62fab34899000000000011af031c00058144976411d2e50b7ca6000351ea8d9523000000010b399d0000000000000000000000000000b71bb5500000006808000b930000f06ddc5d3281bff25911f62b42480002d65c6f9ebca5700000001c1300032c14370c33035c0002e04f53000314a2d2400051e7d58000333a00038d6a938000000112564a66c413cc5a20000000618f94d643000012475a0000025100000008cf885fe93d363cd900000000000410cd92000252085af85573b78fd0913b5290ff081de1400000000009ad000015040002e08827106a0d2963123a68d756a41c707d04a1077e61c0009a0f519c4cfbc272fbb94a2d6f5f516447bf6e40005188000ce18e39128e99600029cb0001acb000000080c000000000648635022a212fa40002a4dd361da580f8780000000018decd540f24a7b712c69db8ae49f65688a000264b0001dc300000000000000a49c000981ec700003a58000081cf4d6ca012ccf1200000008d5de4a83928c9e4e4000000009d457800000035c0f59c98a5d454a5120be0900017661ea1268d8d2474f118000a4f5c3da28b17bc4180000000000000104015ce6c7be120e78ef084239cba2d94251bd00021990000800d330000a8b3bb4e487783a49125ae5684780003915762c00000000009622cfc709400000021a66b28000d64000065838bc00028cd000000000000000000000ab3987f722401600032330000000000000000010f6b5b400000000000000000fd5800000031430384000e48a91d8ed6142b574c8c1626fa914dd453644034cd4d8c0ac0e1dabe253150e40641fd90f85c000334b00000002ab04eb853e49fd0ac00028fc00002d2c9e00035aead060fb105c532a86a424e3aa40c230c00046dd163e30906b0000000020fd48000000074602be0000b0090c02020a90010011cb04314700100500400400500c0093420010000071823440c12070030070011401400401002810010190000050421c531600508008000200308200100058404000618018500808d0c00c500200000400018504604404d04504000140100000800500014604114810004f00004c0804401000180841000c62c10010400413411400021c04c00c10010400010020010400010c0081003082 else 0xa51c00000011590001a93000000008c0cc04d841aa8d88d1782c4955905219c424b07e00032220000000000000008f8000000210b000345ec8f0000d19d0040001d530000000934400000024660000000d6dabb0a079cb250048f090980006ce40000002d3c5438ac96524000e3baeaea514000a01800074b70e2cb8d46f651078eb37b58f000016c0592c0350650e8000345800000007918b3d8383e3d74ec000000000070a4b5400016cca908585244b240e56faba7500b6931a3976a2ed4af71d99820000d3fa8004efeda3c3b3853c47b0800008186975000000012c04f40000329b114997d4e09c226500000000186b0440004ec65b844bd89800000008f06216f69241d0000000c0391ca06cc00000000000000000f40c0000001d1c000000000000000001343000000085c00000003015c08c000831434201f2737000000014c116f48e34bfc55d73672a00000240000fda8000c94308e00030f5760400058ae0520002ac300000000000000a6c80000000000000000000000001892566533c000000345100000007d21ac2c6f0000243609c65eaaa6e022c310000f47000099e160d8aabefcbc5f39b2c0354b8e51e57d84f3f9bc6a3b30ff20a09986857d1a273d670d321dc874c6eb3667f9ce6d95fbed81112a624d514c3dce1e2364972e806e82371c15f000280b3105f4a54b000004ac0000000d4e444fd71000000000021a3ce8800035585269368f453819980e353da90001cc68e80c32fd10000000114c46840004cf0000480e01822e014b0000000ee4994680b80000cec0000003c6da64f4bd45fc17ee3e800000008870000340c6d5c2a00025780d82247000000040bf33f000108bf9c408f55de9510002c75000223b49144366ce16b509659a8c015465000000012e40000002c57c180000000168400020f2d00884ca4218a101c800011680001220000641dc4876eccdf9175bc4fab5a6934e890236d0dba00009cd21b80002f0e05b0003105f2db91b1b179cc51cc0003304000113800000000ae6afdcce643fc6c513c0c4f2162a70002cb7663a4f80001111d043d3e0000000ad9f86a00023c00000000b2199740000c2100011c9e035c44fa4b8ab00000007550c120000cba140209575a4dad)
def hashg262655l13 (i : Nat) : Nat := 0x42f400130f0000000000000000000000161200011d40000000001e55964000c58000000045cc61211545e000126320484a00000079e4d0bc660004920000058000569f43f0362395a5ed472b7540026159de7176920d103813f159f12ec478cba3ec862420000803d6480002bbd028a9c00048e00000008018c800032db6b9191d22000000142a1540000875a87920b4c3d8c0510002a548adb04529fa0bcf741a6d19e65c6ee210006080000000000189c000000f0e8000000000ec9e315a448ac000622c001e0c152d631885e391b40aac001892fc6e1dc82243feca0000cce4742447c94f20809928000386b2020000000d080000000924c334910000001c9e217b1800000018330003a9a67c000512719400143284c88ac000000000280e568d41768298e88d45f13659651132c123c1af314860884519a9cde0930056a7b4a4000e657a8896288f25019a18e0a9070d9abd8276d1cadd006e3f82ef61825399ba54000113824800023d6a1acc0f1870f0000000f5aed2b9ad734000c0b1472a5e000080610193aead454b9b80000008252271f1c87ead1000000119e000000097c0000000000001ba00000000001c3da06ac8416b11a4d354834e68760cb117b63a00012d800000166d0000001e640009d20000000000326800000000060a81a5e8149f832333d8aa39d00002fc000000a4d0c65e05a31b5c3310000000fce00000000000000002470000a50800000125af4d80020c20000003038001f17814420e580000b05daa8000004000795c92c159e6631ff81e0001638000000ab96462e7f4ba000a5d5a350792226572c6ec5b1312648000001c260000000000629acd8988e0707c5d0c4040000009c780000000000000000876f9700040b0000b1ea91b85333084351f00000015160000000000000000791f00db690074570050800000c03040050220610004050442c00400810810c00c040a08028e38504100300010018304608208118304310208100008000314104690e140000004083849
def hashg262655l14 (i : Nat) : Nat := 0x348000004a4005a000e5015002206128bf1400204001298900112f3e9a0004c003577984051d8ef0819743517362a49c98002930000090c00f1800002d60000000364630807
def g262655index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 14 62 4 10 5 1 (hashg262655l10)
  | 11 => lookupWord 129 582 5 13 8 1 (hashg262655l11)
  | 12 => lookupWord 215 965 6 14 9 1 (hashg262655l12)
  | 13 => lookupWord 92 413 6 13 8 1 (hashg262655l13)
  | 14 => lookupWord 11 51 4 10 5 1 (hashg262655l14)
  | _ => fun _ => none
def g262655 : Forest := ⟨262655,14,fun j => g262655samples[j]?.getD (0,0),g262655columns,g262655autos,g262655levels,g262655index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geom262655 : graphValid g262655 (boundsBefore known319) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_9_0 : block g262655 9 0 23=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_9_23 : block g262655 9 23 1=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all262655_9 : block g262655 9 0 24=true := (@block_merge g262655 9 0 23 1 s262655_9_0 s262655_9_23)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_10_0 : block g262655 10 0 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_10_32 : block g262655 10 32 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_10_42 : block g262655 10 42 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_10_74 : block g262655 10 74 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_10_106 : block g262655 10 106 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_10_138 : block g262655 10 138 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_10_170 : block g262655 10 170 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_10_202 : block g262655 10 202 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_10_234 : block g262655 10 234 10=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_10_244 : block g262655 10 244 9=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all262655_10 : block g262655 10 0 253=true := (@block_merge g262655 10 0 234 19 (@block_merge g262655 10 0 106 128 (@block_merge g262655 10 0 42 64 (@block_merge g262655 10 0 32 10 s262655_10_0 s262655_10_32) (@block_merge g262655 10 42 32 32 s262655_10_42 s262655_10_74)) (@block_merge g262655 10 106 64 64 (@block_merge g262655 10 106 32 32 s262655_10_106 s262655_10_138) (@block_merge g262655 10 170 32 32 s262655_10_170 s262655_10_202))) (@block_merge g262655 10 234 10 9 s262655_10_234 s262655_10_244))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_11_0 : block g262655 11 0 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_11_32 : block g262655 11 32 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_11_42 : block g262655 11 42 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_11_74 : block g262655 11 74 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_11_106 : block g262655 11 106 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_11_138 : block g262655 11 138 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_11_170 : block g262655 11 170 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_11_202 : block g262655 11 202 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_11_234 : block g262655 11 234 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_11_266 : block g262655 11 266 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_11_298 : block g262655 11 298 12=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_11_310 : block g262655 11 310 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_11_342 : block g262655 11 342 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_11_374 : block g262655 11 374 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_11_406 : block g262655 11 406 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_11_438 : block g262655 11 438 8=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_11_446 : block g262655 11 446 18=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all262655_11 : block g262655 11 0 464=true := (@block_merge g262655 11 0 446 18 (@block_merge g262655 11 0 234 212 (@block_merge g262655 11 0 106 128 (@block_merge g262655 11 0 42 64 (@block_merge g262655 11 0 32 10 s262655_11_0 s262655_11_32) (@block_merge g262655 11 42 32 32 s262655_11_42 s262655_11_74)) (@block_merge g262655 11 106 64 64 (@block_merge g262655 11 106 32 32 s262655_11_106 s262655_11_138) (@block_merge g262655 11 170 32 32 s262655_11_170 s262655_11_202))) (@block_merge g262655 11 234 108 104 (@block_merge g262655 11 234 64 44 (@block_merge g262655 11 234 32 32 s262655_11_234 s262655_11_266) (@block_merge g262655 11 298 12 32 s262655_11_298 s262655_11_310)) (@block_merge g262655 11 342 64 40 (@block_merge g262655 11 342 32 32 s262655_11_342 s262655_11_374) (@block_merge g262655 11 406 32 8 s262655_11_406 s262655_11_438)))) s262655_11_446)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_12_0 : block g262655 12 0 22=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_12_22 : block g262655 12 22 32=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_12_54 : block g262655 12 54 32=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_12_86 : block g262655 12 86 32=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_12_118 : block g262655 12 118 22=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_12_140 : block g262655 12 140 32=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_12_172 : block g262655 12 172 32=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_12_204 : block g262655 12 204 7=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all262655_12 : block g262655 12 0 211=true := (@block_merge g262655 12 0 118 93 (@block_merge g262655 12 0 54 64 (@block_merge g262655 12 0 22 32 s262655_12_0 s262655_12_22) (@block_merge g262655 12 54 32 32 s262655_12_54 s262655_12_86)) (@block_merge g262655 12 118 54 39 (@block_merge g262655 12 118 22 32 s262655_12_118 s262655_12_140) (@block_merge g262655 12 172 32 7 s262655_12_172 s262655_12_204)))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_13_0 : block g262655 13 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_13_6 : block g262655 13 6 21=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all262655_13 : block g262655 13 0 27=true := (@block_merge g262655 13 0 6 21 s262655_13_0 s262655_13_6)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s262655_14_0 : block g262655 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all262655_14 : block g262655 14 0 1=true := s262655_14_0
theorem tables262655 : checkedTables g262655 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g262655 0 0 0 = true)
  · exact (rfl : block g262655 1 0 0 = true)
  · exact (rfl : block g262655 2 0 0 = true)
  · exact (rfl : block g262655 3 0 0 = true)
  · exact (rfl : block g262655 4 0 0 = true)
  · exact (rfl : block g262655 5 0 0 = true)
  · exact (rfl : block g262655 6 0 0 = true)
  · exact (rfl : block g262655 7 0 0 = true)
  · exact (rfl : block g262655 8 0 0 = true)
  · exact all262655_9
  · exact all262655_10
  · exact all262655_11
  · exact all262655_12
  · exact all262655_13
  · exact all262655_14

def fronts (ws : List Sig) : List Sig → List (List Sig)
  | [] => [ws]
  | a::as => fronts ws as ++ fronts (a::ws) as

theorem fronts_cover (S : Finset Sig) (base opts : List Sig)
    (lo : base.toFinset ⊆ S) (hi : S ⊆ (base++opts).toFinset) :
    ∃ ws ∈ fronts base opts, ws.toFinset = S := by
  induction opts generalizing base with
  | nil => exact ⟨base,by simp [fronts],Finset.Subset.antisymm lo (by simpa using hi)⟩
  | cons a opts ih =>
    by_cases ha : a ∈ S
    · obtain ⟨ws,hm,he⟩ := ih (a::base) (by
        intro v hv
        rcases List.mem_cons.mp (List.mem_toFinset.mp hv) with rfl | h
        · exact ha
        · exact lo (List.mem_toFinset.mpr h)) (by
        intro v hv
        have h := hi hv
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at h ⊢
        tauto)
      exact ⟨ws,List.mem_append_right _ hm,he⟩
    · obtain ⟨ws,hm,he⟩ := ih base lo (by
        intro v hv
        have h := hi hv
        have ne : v ≠ a := fun e => ha (e ▸ hv)
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at h ⊢
        tauto)
      exact ⟨ws,List.mem_append_left _ hm,he⟩

abbrev RootRoute := Sum Nat (Row × Row)
def routeOK (g : Forest) (cap : Nat) (route : RootRoute) (ws : List Sig) : Bool :=
  match route with
  | .inl i => indexedRoot g cap i ws
  | .inr (a,b) => (bit a (targetOf g) != bit b (targetOf g)) &&
      ws.all (fun w => bit a w == bit b w)

theorem route_sound {g cap route ws}
    (idx : ∀ i, indexedRoot g cap i ws = true → Impossible (targetOf g) cap ws.toFinset)
    (ok : routeOK g cap route ws = true) : Impossible (targetOf g) cap ws.toFinset := by
  cases route with
  | inl i => exact idx i ok
  | inr p =>
    obtain ⟨a,b⟩ := p
    simp only [routeOK,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,beq_iff_eq] at ok
    intro k t _ h
    obtain ⟨v,hv,hd⟩ := live_row_difference h ok.1
    exact hd (ok.2 v (List.mem_toFinset.mp hv))

theorem forest_subsets {g cap raw optional pairs} {route : List Sig → RootRoute}
    (idx : ∀ i ws, indexedRoot g cap i ws = true → Impossible (targetOf g) cap ws.toFinset)
    (ess : checkEssential (targetOf g) raw pairs = true)
    (allowed : raw.all (fun a => !(properB a) || (pairs.map Prod.fst ++ optional).contains a) = true)
    (all : (fronts (pairs.map Prod.fst) optional).all (fun ws => routeOK g cap (route ws) ws) = true)
    {k t S} (hk : k ≤ cap) (h : Live (targetOf g) k t S) (sub : ∀ a ∈ S, a ∈ raw) : False := by
  have lo : (pairs.map Prod.fst).toFinset ⊆ S := by
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ess a ha
    exact raw_required h raw a sub r s hd iso
  have hi : S ⊆ (pairs.map Prod.fst ++ optional).toFinset := by
    intro a ha
    have hp := live_proper h a ha
    have p : properB a = true := by simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using hp
    have v := List.all_eq_true.mp allowed a (sub a ha)
    simpa [p] using v
  obtain ⟨ws,hm,eq⟩ := fronts_cover S _ _ lo hi
  exact route_sound (fun i => idx i ws) (List.all_eq_true.mp all ws hm) k t hk (eq ▸ h)

def certCap : Nat := 14
def certTarget : Sig := 0xfffffffffffffffefffffffffffffffefffffffffffefffcfffffffffffafff0fffffffeffffffeefffffefeffffeeeefffefffcffeeffccfefefcfcaaaa0000
def certRoots : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def certPairs : List (Sig × Row × Row) := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,17,16),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,34,32),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,36,32),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,72,64),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,17,1),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,34,2),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,66,2),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,129,1),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,260,4)]
def certOptional : List Sig := []
def certRoute (ws : List Sig) : RootRoute := match keySet ws with
  | 67053544196914757197 => .inl 0
  | _ => .inl 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem certNoRun {k t S} (hk : k ≤ certCap)
    (h : Live certTarget k t S) (sub : ∀ a ∈ S, a ∈ certRoots) : False := by
  have eq : certTarget = targetOf g262655 := by decide +kernel
  rw [eq] at h
  apply forest_subsets (g:=g262655) (pairs:=certPairs) (optional:=certOptional)
    (route:=certRoute) (raw:=certRoots) (cap:=certCap) _ (by decide +kernel) (by decide +kernel) (by decide +kernel) hk h sub
  intro i ws idx
  exact root_index (before_sound known319 valid319) geom262655 tables262655 (Nat.le_refl _) idx

theorem certLower : Lower certRoots certTarget (certCap+1) := by
  intro p bank hr hit
  have hp : proper certTarget := by unfold proper; decide +kernel
  obtain ⟨k,t,S,hk,h,sub⟩ := reach_live hp hr hit
  by_contra! small
  exact certNoRun (by omega) h sub


def certEval (x : Fin 9 → Bool) : Bool := ((((((((((((x 0) && (x 4)) || ((x 1) && (x 5))) || ((x 2) && (x 5))) || ((x 1) && (x 6))) || ((x 3) && (x 6))) || ((x 0) && (x 7))) || ((x 1) && (x 7))) || ((x 4) && (x 7))) || ((x 2) && (x 8))) || ((x 3) && (x 8))) || ((x 5) && (x 8)))
theorem certEval_bit : ∀ r : Row, bit r certTarget = certEval (sample r) := by decide +kernel
theorem certProper : proper certTarget := by unfold proper; decide +kernel
theorem certInput (a : Sig) (h : a ∈ inputs) : a ∈ certRoots := by
  have ok : inputs.all (fun w => certRoots.contains w) = true := by decide +kernel
  simpa using List.all_eq_true.mp ok a h
theorem certFromInputs (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ certCap) (result : (execute C.gates inputs).getD C.output zero = certTarget) : False := by
  have out := get_rep (execute C.gates inputs) C.output
  rw [result] at out
  obtain ⟨k,t,S,hk,h,sub⟩ := extract C.gates inputs fan certProper (out.resolve_right fun hn => hn certProper)
  exact certNoRun (hk.trans small) h (fun a ha => certInput a (sub a ha))
theorem plainClose (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ certCap) (correct : ∀ x, PEqualNP.MetaComplexity.circuitFun 9 C x = certEval x) : False := by
  have result : (execute C.gates inputs).getD C.output zero = certTarget := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C fan C.output r).trans ((correct (sample r)).trans (certEval_bit r).symm)
  exact certFromInputs C fan small result

end PEqualNP.Outside.L_meta_10968

theorem PEqualNP.Outside.L_meta_10968 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8)) t → 15 ≤ t := by
  rintro t ⟨C,fan,sz,correct⟩
  by_contra! h
  exact PEqualNP.Outside.L_meta_10968.plainClose C fan (by unfold PEqualNP.Outside.L_meta_10968.certCap; omega) correct
