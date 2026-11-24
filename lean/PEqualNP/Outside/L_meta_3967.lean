import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3967_aux
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
open PEqualNP.CircuitLowerBounds
def cLook (nb slots sw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*(iw+pw)) (iw+pw)
  some (word &&& ((1 <<< iw)-1), (word >>> iw) &&& ((1 <<< pw)-1))
def qd8 (i : Nat) : Nat := 0x3a98627584c0139cb2f8b31f9499491494913
def ql8 : Nat × Nat × Nat × (Nat → Nat) := (5,8,6,qd8)
def qd9 (i : Nat) : Nat := (if i<1 then 0x8c46e1a1188dc342311b8684a2370d08446e1a150682000000a35a30a2ba19a079f59f09eb9e69e19dc9d79d29cd9c89c39be9b99b49a299d99898698196f95d94b93992791591090b9069018fc8ea8e58e08db8c98c48bf8ad89b88987786585384182f81d80b7f97e77e27dd7cb7c67b47af7aa7a57a079b79679178c78778277d77877376175c75773873372e72972471270d6ee6dc6ca6b86b36ae6a969769268d68868367e67966766265d64b64664163c63763262060e5fc5f75d85c65a758857656455253352e52952451f51a5155104fe4f94e74e24d04cb4b94a749549047e47947446245043e42c4274154033f13ec3e73d53d03cb3c63c13bc3b73b23a038e36f36a36535334132f31d31831330e2fc2ea2e52d32ce2c92b72b22a029b29629128c28728227d27827326e26924a21e1f21ed1e81e31de1d91ba1b51b01ab18c16014e13c11d0fe0f90f40ef0ea0e50c60a708806904a02b01901400f00a0050002f594433493a2b49351759140f59149752da21d8cc3762d321d84d2b48301358182f480a2f48012f47fe1b57ee1357eb37624737624537624325d7db2757db2757d92757d82757d61357d6a1d23d5d923d21d7b421d7ac1357a42f47a064d2361f579a64d23313579713578061922a64d2291d97722f47662f47628b12144751f214d72b6611e86591e821d7021f56f62616eb1f56cd1b56cd0f56cd0356cd3356cd65d1866551869511864f517f5951721f56691f56641b56640b566403566433566461d16b1f564f3761462f46402f463f65d1436551439511434c91420c9635a1d14066113d65913d33461833461094913a9491399491389491379491321355af1d95a665d1266551269511262f456f37610a2f45582f455765d1076551079511071355453345411355372f453665910464d10433451c33451721d4ee6490f41b54b62f44a92094a71d94a3a050ec2b449b0f548d0754841f547d1b547a9510d12f44511f544c6190c19510bf2094432354432094429510bda1d0b73760b4a1d0b2a350b2a1d0b1a190b09d90b09f50b061d0af9750aea350ad9d90ac5950aca090aca350ac9f50ac9d50aba090ab9c90ab9f50ab5f40ab9b50ab3760ab10543a1054399510a361909d10543110543094909894909794909610542c33442815142115141a1d94196610809d908059508095108015140995107c98907c1b54051514021513fc1f53f01513eb1b53db1de0071f538e1b538c17538c03538c2220061de00619a00615600608a0062f525307121318d1720351720c913a2b40eb2220042220031de0031b50aa2220021de00219a0021050a51050a31050971050961050951050942220011de00119a00108a0011b507e15107715107115106d13106715106215105d33403d2220001de00019a000151035151025 else 0x488c200036420d9081d02000000000000000038d04003a984071a0910426400836420d90b10020000000170400000b820001a43e1a09178245e0f8683e1a0a10438230e08c28230a08c38230800f1a08005c100000000000000003c6820001a6e34200000b8d040353b8d096a6198d058a610000f1a080000000f1a0800c5308000003c34171007c341001a7c342f0d0405d21a14d4cc342e0d078341e0d0403fc1a10000000000348400690800d21001a42069080b8200348400034840d21034840481001a42069080b82000d4c2000000000ea61034840d2753100002e081a43e1a0a880200012801011841e1a0801e1a083c34100000000000000069b0d081bc8416118f28002e6118c000001823d0d08000308dc342034ad4d8463611840d21611b8684c2370d0800000062370d0)
def ql9 : Nat × Nat × Nat × (Nat → Nat) := (222,12,12,qd9)
def qd10 (i : Nat) : Nat := (if i<10 then (if i<5 then (if i<2 then (if i<1 then 0x3b1de03b19a03b6f003b1b138c2f038b22203a1de03a19a03a15603a6f003a2220391de03915603908a0392f03832f038126d3751b137410536f26936f10536c26936c2f03600b135a0c93380c93351053352693351053342693341053332693331053322693321053312693312f032c2220381de03819a03815603898d0384c903808a0381312ed1d92ad18d2922492911b128d03128d2f02756f00372f02742220362220351de0351f12701b12700f12700b12700712700312702f026e2220341de03419a0346f003422203319a0331560332220321de03215603208a0322f02632f026126d2541b12532f022e26d21d1f121b2f01fd1de02f0f11e32f01d619a02eaf002d2611d266102b66102a22202a1de02a1f11ce0f11cd0f11cc2f01c71b11c264902908a0293320291de02864902808a0282f01a62b01a112d1a064902708a0273320272220252220241de0241b118f0f118f2220231de02319a02326118a47002166102022202066101f22201f1de01f22201e1de01e19a01e22201d1de01d19a01d2f01840711831b117f07117f2f117f24917e66101c22201c1de01c19a01c95101c47001c66101b22201b1de01b61901b19a01b95101b64901b60901b08a01b5b001b33201b22201a1de01a08a01aa0501a9c501a94501ae22000e1d000e19000dd9000dd5000d95000e09000e08000dc9000d89000d49000d48000c8a00010517a2051791051791f11791051780b017810517710517619a01964901908a019a050195050193320191051751051741051732311731f11731b11731711731051726610182220181de01819a01895101864901808a018a0501850501897101815116c1051666610172220171de01719a01795101764901798901708a0174b00173320170c51650c516115115d26115c95101694d01667101633201666101522201595101594d01566101422201495101494d01415115b14d15b6610132220135310134f101333201366101222201295101297101233201266101122201195101194d0113320111511552f01552220101de01094d01008a01066100f22200f1de00f95100f64900f08a00f97100f26114e66100c22200c66100b22200b1de00b1f11491b11490f11490b11492b114919a00a2220091de00919a009156009af00096610082220081de00819a008a15008156008951008af00083320082220071de00719a00715600794d00714d1411b11400f114024913f6610062220061de00619a00615600695100694d0061b113d0f113d1de0052220041de00419a0041f110f0f110f0f110b2220031de00319a00308a003a050039710033320030c510a2311091f11091b11091711090f11090c51082220021de00219a00215600294d00208a00219a0010460012220001de00019a00008a000105018151008 else 0x16fc1b16fc0f16fc0716fc0316fc2220981de09819a0986b00982220971de09719a0971560971f16f72220961560960ce096a310969710968f10962220941f16f31b16f30f16f30b16f30316f32220931de0932220921de0921560921b16ed2220911de0911560910ce09122208f1f16e81b16e80f16e80b16e80716e80316e822208e1de08e1b16e422208d1de08d15608d2b16df65d08c1de08c67108c2b06d52b06cd2b06c91316c80316c32b06be2b06b90716b52b06a12b06942f067f2b067a22208a1de0892f06702220881de08819a0886f00881b166c2f066b2220871de08719a0871560876f00872220861de08615608608a0861de0851560850ce08508a08533208527165d1a865a1a86561a86551a86521a864f1a864a2696472f064466108422208465d0841de08465508415608464d0840ce08464908408a0846450840460841316120315fa2f05e06f00832220822220812f05da1b15cf1de07f15607f1b15a92b05a013159d1de07e19a07e0ce07ea3107e8f107e2b058c2b05752095731d956603154d1de07d2f054822207c1de07c19a07c6f007c22207b1de07b15607b08a07b2f05432285362695261295261b151426151066107422207447107143107133207167107033207033206f2614f666106b22206b1de06a6610692220691de0696610682220682220662220651de0651f14d91b14d90b14d90714d90314d92220641de06419a0646b00642f04d56f00632220622220611de0611f14d11b14d10f14d10b14d10714d10314d12220601de06019a0606b00600714aa2f04a71f149d66105f22205f0ce05f33205f2f048922205e19a05e15605eaf005d26147f66105b22205b1de05a6610592220591de0591f147b1b147b0f147b07147b03147b6610582220581de05865905819a0586b00582220571de05719a0571560571f14740714741b146a2614526610542220541f14501b14500f14500b14500314506610532220531de0532220521de0521560522220511de0511560511b14472494456610502220501de0501560500ce0501de04f22204e1de04e19a04e22204d1de04d15604d08a04d22204b1f143b1b143b0f143b0b143b07143b03143b22204a1de04a1b14342220491de049156049971048222047a310479710472b042c1f14192b04182b04161f14122220461de046156046a310469710461f140018d3fb0313fb2b03c82093c62220442220431de0431f13b41b13b40f13b40b13b40313b42b13b42220421de04219a0422220411de041a190411560413320410f13af18d3ad2b03ad1b13ab0f13ab2220401de04019a040156040a090409b10403320400c93aa22203f1de03f19a03f15603f98d03f2f03966f003e2f039522203d22203c1de03c1f13931b13930f13930b13930713930313932f03912220) else (if i<3 then 0x33216466116395116394d163a311639f11633321636611629511629c5162505162a311629f11625f01629b11623321620c59500f195066116195116194d161505161a311619f11619b116197116161515c95115cd71016e15015e15014a1515ba3115be31013e15012e150112f094c2f094b2f094aa1515514d9462f09462f09452f09442f09432f09412f09402f093f222105222104a311048f11048b11042221022221011de1016b01012220ff2220fe1de0fe6b00fe2220fd1de0fd1560fd2220fc1560fc0ce0fca310fc9710fc8f10fc1de0fa1de0f91560f91de0f81560f80ce0f81de0f61de0f51560f53320f36b10f13320f12220ee2220ed1de0ed1f190c1b190c0f190c0b190c03190c19a0ec1b190919a0eb1560eb1b19062220ea1de0ea1560ea08a0eaa310ea9710ea8b10ea1de0e91f19031b19011719010319012220e81de0e819a0e81560e808a0e8dd9001e04001d44001c84001c460012220e7a310e79710e78b10e72b08fa1de0e52b08f11de0e4af00e42598ef2f08e71de0e21560e26f00e29710e18f10e18710e19710e08f10e08710e02b08d26b00df2220dd4310da6b10da3320da3320d95310d86b10d83320d82220d619a0d6a310d68f10d68710d62b08cb6b00d52220d42220d31de0d31f18c82220d219a0d2a310d28f10d28710d22220d11de0d11560d1a310d19710d12b08bd6b00d02220cf2220ce1de0ce1f18bb1b18bb0b18bb0718bb0318bb2b08ba2220cd1de0cd19a0cd6b00cd6b00cc2220cb1f18b81b18b80f18b80718b80318b82220ca19a0ca6b00ca2220c919a0c91560c91560c80ce0c808a0c83320c82220c71de0c71560c70ce0c7a310c79710c78f10c72b08a26b00c62220c52220c41de0c41f18a01b18a00f18a00b18a00318a02b089f2220c31de0c319a0c36b00c32220c21de0c219a0c21560c22220c119a0c11560c10ce0c11b189b0b189b2220c01de0c01560c00ce0c008a0c0a310c09710c08f10c02220be2220bd1de0bd1f18851b18850f18850b18850718850318852220bc1de0bc19a0bc1f18832220bb1de0bb19a0bb1560bb2220ba1de0ba19a0ba1560ba0460ba2220b91de0b919a0b91560b90460b92220b81de0b819a0b81560b80460b82b086c2f08620f185e1de0b72220b619a0b62f085b2220b51de0b519a0b51560b508a0b56f00b52698542f083f6f00b42220b32f083d2220b219a0b26f00b22f082d21d8152f07ff1de0b06f00b01560af21d7ae2f077c2f076a1b175b9710ae8f10ae8b10ae6b00ad2220ab6b10a83320a86b10a73320a73320a66b00a42220a32220a21de0a22220a1a310a18f10a18b10a16b00a022209f22209e1de09e1f17301b17300b173007173003173022209d1de09d19a09d6b009d22209c0ce09c33209c6b009b22209a2220991de0991f else (if i<4 then 0xf81319f865d2536552539512538f12532699f333224e33224a2719ed6612481519e966124566124233224066123a3322392719e01519de95123765d23565523595123564d23465523395123364d2332f09da2f09d4af02283322282719d12f09cf95122666122365922364d22366122264d21f65921e64d21e65921d64d21d64d21c65921b64d21b8f121ba29218a292172699c62f09bd2f09bc1f19b81b19b80f19b80b19b80319b865d20565520595120566120465920465d20365520395120365920266120165d201659201655201951201a312013321ff3321f92719a82719a71f19a71b19a71319a70f19a70b19a70319a76611f73321f61519a02719a09511f46611ef6551ec9511ec6611eb6551ea9511ea64d1ea64d1e96611e86551e89511e83321e22f09986611dca1d1dc61d1da9d91da3321d96611d8a311d83321d80f19936611d7a311d79f11d79711d78711d720998a23198a2f098a2099892f09892f09886491c36091c39ed1c31ac9850f19841ac9831ac9821ac9801b19806491c29f11c29b11c25b11c29711c28b11c25c91bed49029cb10295491bddc9028d490289491bc9f11bc9711bc6611b86611b7a311b71d997ba1d1b55d91b521d97a6611b4a311b41d99791f19795d91b26491b26091b25b01b23321b26611aca091ac6491a93321a96611a8a1d1a86491a85891a8a311a83321a807196b2f196b6491a46091a45491a45b01a4a1d1a35d91a39951a35c91a35491a3a311a35891a2a051a29f11a2a051a112d9662f196466119ca0919ca3119c33219c332199a1d197a31197a1d196a191959d91959f119561d194332194971193871193a311929d9191595191a09191a311919f11913321919d5190a091909c91909f11905f01909b1190332190a3118f60918d33218da1d18c5c918ca0518ca3118c54918ba0518b661189332189661187a1d187a31187a1d186a191859d91859f1185e2201ee1d01ee1901edd901ee1d01de1901ddd901d61d184951184951183971183661182951182a311826611819d9181595181951181a09181a311819f11813321816611809d5180951180a091809c91809f11805f01809b118033218095117e66117d95117de1d01bdd901bdd501bd9501bdc901bd8901bd4901bd7001ba1d17ce2201ae1d01ae0901ad4901a95117a9f1179971179951178951177951176dd9019dc9019d89019a05175a311758b11759511749491739b11739711732f09622f09612f095e66116c95116c94d16b66116a9d916a59516a95116a94d16a14d9592f1958661168a1d1685d916895116894d1689891682f195694d1679c5167661166951166e1d017e19017dd9017e15017dd5017d95017d89017d49017d7001795116594d1659891655051655b016533216566116495116494d164505164a31164 else 0x13eb65d3e96553e99513e92f0b491f1b461b1b460f1b460b1b46031b46a093d465d3c96553c99513c998d3c865d3c76553c79513c798d3c7209b37209b366613c665d3c66553c69513c6a093c665d3c36553c39513c31f1b2a1b1b2a0f1b2a0b1b2a031b2aa093bda1d3ba3323b7a1d3b5a313b58b13b4a1d3b3a193b29d93b29f13b23323b2e1d041dd5041d56041d7004161d3b098d3b03323b09713af98d3aea313ae9d93ad5953ada093ada313ad9f13ad98d3aca093ac9f13ac5f03ac9b13ac3323aca313abe22040e1d040dd9040e14040dd5040d95040d56040e09040d49040e31040e30040df1040db1040d71040d70040eb0040f32040a1d3949d93929d938e59538ea0938d5f038d9b138d33238da1d3892f0b1faf0383af038065d37d65537d95137d98d37c65d37b65537b95137b98d37b209b16209b1565d37565537595137565d3746553749513744c9372105b124c936f105b110c9b10105b10a1d36e66136ca1d36c65936c65536c95136c98d36ca2836c2f0b086613692f0b05661362659362661361659361a09361a1d35fa1d35e66135b65935ba2c35b66135a65935aa3135a2f0afe2f0afb65d35095135065d34e95134e65d34c95134c2f0af72f0af62f0af065d34465d34065933f98d33e4c933e105ae8105ae7105ae6269ae61f1adf949338949337105adb98d33594933598d334949334105ad9269ad998d33298d3319493311f1ad31b1ad30f1ad30b1ad3031ad394931a2b1acb9713198f13172f0ac96613148f13142b0ac12b0ac08f13086713034713034313036b1303a312fe8f12fe2f0ab38f12fc2b0ab12b0ab01b1aaa071aaa031aaa2b1aaa2b0aa7a1d2ec6552ec9512eca312ec6612eb6552eb9512eba312eb2f0a8e151a8a151a89a312e81f1a811b1a810f1a81031a811f1a785952d79512d73322d69d92d13322d16552d06612ce9d92ce5952ce65d2cd6552cd9512cd151a691f1a601f1a521b1a520f1a520b1a52031a526552ba9512baa1d2b93322b86612b66612b43322b26612b0a1d2af5d92af3322af271a3c151a3a271a3a6612ada1d2ad6552ad5952ad9512ad64d2ad58d2ad64d2aa1f1a321b1a320f1a320b1a32031a326612a2a1d2a22b0a251f1a201b1a200f1a200b1a20031a2066129465d294a192946552949512946b02942f0a1c18da1b66129265d2929d9292655292595292951292661291659291655291951291a092919892919b12911f1a1966128e65928e98928e2f0a172f0a161f1a131b1a130f1a13031a132f0a102f0a0e59527ba1d279a31276971276332274a1d272a3127261d271a1926f9d926fa1526f59526ca1d2692f0a0aaf0263af02603322602f09fe1519fd95125c65d25b65525b95125b66125865d25765525795125798d25798925765d2546552549512542719))) else (if i<7 then (if i<6 then 0x2f0cf665d65065565064d650271cf3131cf365564c269cf01a8cf0269cef1a8cef65d64865564864d64865d64765564764d6476f064433264433264133263f25dce8271ce8271ce6271ce564d63865d63765563764d63764963765d63665563664d636e1d084d56084e0d084dcd084e09084dc9084d49084cc9084d7008465d63564963565d63465563464963465d63365563364d6338f163033262e33262aa1d6205d96209a9620a3161e8f161e6f06161d9ce1a1d6125d9612a31611a1d6025d9602261ccca1d6005d960021dcc6a1d5ff8f15ff1d9cc021dcbea1d5fd58d5fda095fda315fd8f15fda095fba315fb8f15fb21dcb3a1d5faa095faa315fa21dcac261ca8a1d5ea3325d95d95d7af05d73325d72f0ca1209c9f209c9e64d5d064d5cf8f15cfa095ba1f1c885f05b13325b164d5a9a1d5a53325a564d5a264d5a12b0c7fa3159c8b159ce1907edd907edcd07ed8d07e2b0c76149c745495948f159464d59264d5912b0c7058d590a315908f15902b0c69a3158f2b0c5f33257765557464d574209c4c2f0c4c64d573209c4b65d57064d570a1d56d66156a661568a1d5655d9565995565995563195c4566156265956264d562a0956299556064d5602f0c43195c422f0c40a1d54f33254b9d9549a09549a1d54664d53c195c3aa1d535269c33129c33269c32129c326615119695119715118f15118b1511cb1071c71071332508cf1070c71070f320702f0c193324e7071c15a314e69714e68b14e62f0c0f2f0c0d9f14de9714de8b14de3324d4a1d4d2a314d29d94d0261c0a21dc092f0c0721dc05231c052f0c0520dc042f0c041b1c006614c49f14c49714c48f14c46614b75cd4b73324b75954ae61d4ad60d4ad2f0bf22f0bf12f0bec2f0beb6614a161d4a160d4a15704a16614a06594a03324a066149f65949fa0949fa2d49fa2c49f1ecbe51ecbe41ecbe21f1be266149d65949da3149d9f149d5f149d8f149d60d497e0d05fa0d495a314953324952f0bde2f0bdd1f1bdb1b1bdb0f1bdb0b1bdb071bdb031bdb2f1bdb2f0bd8a1d48f61d48e9cd48e33248d33248ca3148a9f148a97148a2f0bcc1f1bca1b1bca0f1bca0b1bca031bca2f0bc82f0bc6261bc5261bc0209bbf209bbe661467a1d46421dbbba31463661461a1d461661460661458a09458661456a1d455a1d4543324439d9441a09441a1d43e8b14312f0bb1e22047e150478b142d4f141f47141f6b141fa3141b8b141b2f0b9d8b1419071b921f1b8e1b1b8e0f1b8e031b8ee22046e1d046e14046d560461f1b836553ff9513ff6553fe9513fe6553fd9513fd65d3fc6553fc9513fc5953fba313fb2b0b69a313fa1f1b656613f96613f86593f86613f76593f798d3f76613f66593f61f1b5c1b1b5c0b1b5c031b5c2f1b5c6613eb65d3eb61d3eb6553eb9513eb47 else 0xd200a900800057002e001d00005b19273329272f0eada29911332911e310f12f0eac2f0eaa8b1902e150e72f0ea98b18fc2b0ea76618f3a318f32f0ea32f0ea22f0e9a20de932f1e8765d8da6618d965d8d86618d765d8d765d8d6cb10dac710da2b0e812b0e802b0e7f2b0e7ee1d0d1e150d1d560d19518aee220c733288ae1d0b9dd90b9e220b8dd90b82b0e7a65d87e67187e33287e2b1e773328702b0e722f0e7266186f65d86f8f186f2f0e671b1e619e98559698556618549698548e98544b08549e9853969853231e59271e541f1e54131e542f0e4f271e4e131e4e2f1e4e65d84b65984a66184965d84906de49271e49131e490b1e4797183c65583a95183a8f183a3328372f0e448f1834a3182e0b1e422f0e412f0e402f0e3d2f0e3a65d81361d813af0813271e37131e37271e31131e318f17f83327f7a097efa297efa097eea297ee2f0e2a3327ed6617e16617df6557dc9517dc2f0e246617d86557d89517d82b1e212b0e206717cb5317cb3327c92f0e1a6597c86617bfa1d7be1f1e161b1e160f1e16071e16031e1661d7b121de10a1d7ae6597ae1cde0e1b1e0b1f1e090f1e090f1e0865d7a565d7a49cd7a465d7a33327a3209dfc6617a2a097a26617a1a097a13327a12f0df92f0df86617a06557a09517a0a317a00f1def0f1dec2f1dec0f1de7659784269de32f0ddd2f0ddc0b1dd6af077c2f0dd565d77861d77865d7758b17751f1dc9261dae209dae269dae255dad151dad66176e95176ea0976ea2976e96976e2f0da32f0da21f1da01b1da00f1da00b1da0071da0031da01f1d9b6597616557619517611f1d9866176065976065575f95175f65975e66175d65975d65575d95175d6157595d575996d7599717599697589717588f17588b1758cb10a8c710a8332750cf10a7c710a7f320a72f0d866b073d33273da3173c97173c8b173c2f0d7e2f0d7d9f17359717358b173521dd792f0d7821dd76231d762f0d7620dd752f0d75149d711b1d719f17269717268f172661d71a60d71a60d714e0d09ca0d712a317123327122f0d652f0d641f1d621b1d620f1d620b1d62071d62031d622f1d622f0d61a1d70c61d70b9cd70b33270aa317089f17089717082f0d561f1d541b1d540f1d540b1d54031d542f0d532f0d513326e98b16e861d6e63326e69b16e03326e08f16d28b16d26556c465d6c36556c38b16c32b0d419716b63326af271d301b1d30131d3065d6a76556a76556a68f16a65706a564d6a48f16a464d6a164d69f64d69e65d69d65569d9cd69d65569c95169c65569964d699209d0d209d0c6b066733266733266533266325dd03271d0365d660655660271d02209d01271d01209d00d49085cc908565565d64d65d2f0cff65d65b6096586096566096551a8cfb209cfa269cfa1a8cfa2f0cf965d653655653) else (if i<8 then 0x123d013cf03cdf3cc23ca53c883c6b3c4e3c3d3c2c3c1b3c163bed3bdc3bcb3bba3ba93b8c3b6f3b463b113af43acb3aba3aa93a983a873a463a353a0c39ef39d239b53998396f395e394d393c392b391a390938f838e738d638c538b43897387a385d384038233812380137f037df37ce37c937b837a73796378537743763373a37293718370736ea36cd36b03693367636653654364336323621361035ff35ee35dd35c035af359e358d357c356b355a3549353835273516350534f434e334d234cd34bc34ab349a3489347834673462345d344c34473442343d33fc33eb33863345333432e732d632c532b43297327a325d31ec31ab316a312930e830a7305a30553050304b30162fe12fa02f772f422f012efc2ef72ef22ed52eb82e772e5a2e3d2e202dc72d9e2d5d2d342d232d122d012cf02caf2c7a2c692c582c532c4e2c492c442c272bce2bbd2b7c2b772b722b6d2b442b032ac22a8d2a4c2a0b29b229ad29a829a32992295d290428ff28fa28f528f028df28da28d528d028cb284e283d280827c7279e275d271026b726a626712660265b262625e525a42557251624c924942453240623b92360235b23562351234c232f231e231922fc22bb227a22392234222f21b221a12160215b21562151211c20e720a6205920181fd71f8a1f851f801f7b1f6a1f651f601f5b1f561f511f4c1f471ee21ed11e901e5b1e4a1e151de01d871d761d4d1d0c1cfb1cea1cd91cc81cb71ca61c951c841c731c621c511c281bff1be21bc51bb41b971b861b451b041acf1ab21a951a781a671a561a451a1c19ff19ee19dd19cc19a31986195d1958192f192a19251914190318f218d518b8189b185a183d180817df17aa178d1764175f175a17551744172716e616d516c416b316a21685165c163f162e15ed15dc15cb15ba15a9155014f714b61469142813e713a6137d13541337130212c112a41263122e11e11194118f1166113110e410bb107a10391028100b0ffa0fd10fa80f970f620f150ed40eab0e820e4d0e300de30dba0db50db00dab0d9a0d7d0d780d670d560d450cf80c870c5e0c4d0c3c0c2b0c1a0bf10bd40bc30bbe0bad0b780b670b320af10ac80a9f0a760a590a300a1309ea09c10998097b0952092908f408cb08a20885085c0833081607e107c40783075a073d071406f706ce06b106a006470612060105f005df05ce05b105ac05a7059605850580056f055e054d053c052b051a050904ec04cf04b20495047804670456044504340423041203f503f003eb03e603d503d003bf03ae03a90398038703760365033c032b030e02fd02ec02db02ca02b902a80297028602810270025f025a02550250024b023a02290218020701f601e501d401c301b201a10190017f016e015d014c013b01360131012c012701220111010c00ef00 else (if i<9 then 0xd66db96da86d976d926d756d4c6d3b6d2a6d196d146cf76ce66cd56cac6c836c666c316bf06bd36bc26b996b7c6b6b6b666b556b446b3f6b226b116b006aef6ade6ac16a8c6a6f6a526a356a1869fb69de69c169a46993697669656954693769266915690468f368e268ad6890688b68866875685868476842683d68386833682e68296824681f681a68156810680b6806680167f067df67ce67c967c467bf67ba67b567b067ab67a667a16790674f673e67396734672f671e670d66f066df66c266bd66ac66a766a26691668c66876682667d666c665b664a6645660465c365826541653c65376532652d652864f364b26471642463e363d26379633862df62ce62bd62ac629b628a62796220621b6216620561c4615f611e610d60fc60eb60da60d560d060a760666055604460275fe65fd55fc45fb35f725f195ed85ec75ec25ebd5eb85eb35ea25e9d5e985e875e6a5e595e3c5e1f5e025d9d5d505d3f5d3a5d355d305d2b5d1a5d095cec5cdb5cbe5cad5ca85ca35c9e5c995c945c8f5c7e5c6d5c5c5c4b5c2e5c295c245c1f5c1a5c155c105bff5bee5bdd5bcc5bbb5baa5b995b885b535b125aad5a9c5a975a925a8d5a885a775a665a555a385a1b5a0a5a055a0059fb59f659f159ec59e759e259dd59d859d359ce59bd59a0599b59965991598c598759765959593c59375932592d58ec58ab585e581d580057bf57ba57b557b0576f576a57655760575b574a573957285717570656f556e456d356c256b156a0568f567e566d565c564b563a55d555c455b355a25549553855275516550554f454e354a2543d542c542753c253bd53b853a7535a530152845273526252515204519351225111510050ef50de50d950d45093508250415030501f501a50155010500b50064ff54fd84fc74fc24fbd4fb84fb34fa24f914f804f634f464f414f3c4f374f324f214f104eff4efa4ef54ef04eeb4eda4ec94eb84e9b4e7e4e794e744e6f4e6a4e654e604e5b4e564e454e404e3b4e364e194e084df74df24de14dd04dbf4dae4d914d8c4d874d824d7d4d784d674d624d5d4d584d534d4e4d314d144cf74cda4ca54c884c834c7e4c614c5c4c574c524c114c0c4c074bf64bf14bec4be74ba64b714b6c4b5b4b1a4af14aec4acf4abe4aad4a9c4a434a324a214a1049ff49d6497d496c495b494a493949284917490648f548e448d348c248b148a04847481247dd4778474f470e46cd4698464b45f245a545944547453644e944d844974486445d444c442f441e440143d8437f436e4369436443534312430d430842d342c2428d42704253423641dd419c417f414a40f1408c4033402e3fd53fd03fcb3fc63fb53fb03fab3fa63fa13f603f2b3eea3ec13eb03e9f3e8e3e7d3e483e133df63dd93dbc3d9f3d8e3d7d3d6c3d5b3d4a3d393d283d173d else 0xc69f919f5c9f3f9f0a9ee19edc9eb39e8a9e559e2c9e0f9df29dd59db89d8f9d729d559d389d1b9cfe9cd59cb89c9b9c7e9c619c449c279c0a9bed9bc49ba79b8a9b6d9b5c9b3f9b229b059adc9abf9aa29a919a689a3f9a1699f999dc99bf99969979997499639946991d98f498cb98969879985098339816980597f497e397c697a9978c977b976a974d973c971f970296e596c896ab96829659963c961f960e95fd95ec95cf95b295a1959c958b957a9569954c952f952a950d950894eb94e694e194b894a79496948594689457942e940593f493d793ba939d93809363933a93359324931f930e92fd92e092b7928e92899284927f927a9269924c922f922a920d91fc91eb91da91bd91a09183917291619150914b914691419130911f910e90f190d490ab90829065903c902b900e8ff18fd48fb78f9a8f7d8f608f5b8f568f2d8f048ef38ed68ec58eb48e978e868e758e648e478e368e258e148e038df28dd58db88d9b8d7e8d6d8d388d1b8cfe8ce18cc48cb38cae8c9d8c808c638c528c358c188c138c028bf18bd48bc38ba68b898b788b5b8b3e8b158b048adb8abe8aa18a848a738a568a458a1c89e789ca89ad89908973894a892d891088f388ca88ad8890887388568839881c87ff87e287b9879c877387568739871c870b86ee86dd86b48697867a865d86408623860685e985cc85af859285758558852f851284f584cc84bb8492848d8470845f84428425841483f783da83c983ac838f8372835583448333831682f982dc82cb82ba829d828c826f825e8259824882378226820981f881e781ca81a18190817f816281518128811780ee80c5809c8073806280398028801780067ff57fe47fd37fb67f8d7f7c7f5f7f5a7f3d7f207f0f7ee67ec97eac7e8f7e727e557e387e1b7dfe7de17dd07db37d967d797d5c7d4b7d3a7d1d7d0c7cfb7cea7cd97cbc7cab7c8e7c7d7c6c7c4f7c327c157bf87bdb7bbe7ba17b847b737b627b517b347b177afa7add7ab47a977a867a757a587a3b7a2a7a1979f079df79c279a579887977795a79317920790378e678c978ac788f78667849782c780f77f277d577c477b3778a777977507727770a76ed76c4769b76727655762c760375fe75e175d075cb75ba75a975987593757675657560755b754a753975287517750674f574e474c774c274b1749474837472746d745c744b74467435740073ef73d273c173b073ab739a738973847367733e7321730472ff72fa72f572f072eb72ce72b172a07277725a7231720871f771f271d571d071bf71ae71a971a4719f718e71897184717f716271517128710b70fa70e970d870bb709e7081707070537036702570206feb6fce6fb16fa06f836f726f616f386f336f0a6eed6edc6ed76ed26ecd6ec86ec36ebe6ead6e9c6e8b6e626e456e286df36d)))) else (if i<15 then (if i<12 then (if i<11 then 0x7ed36dd350d333d322d311d2f4d2d7d2c6d2a9d28cd263d246d21dd1f4d1d7d1aed191d174d157d13ad111d0e8d0bfd0bad09dd080d063d052d035d018cfefcfd2cfa9cf74cf3fcf16cef9cedccebfcea2ce85ce68ce57ce3ace29ce0ccdfbcdeacdcdcdb0cd93cd76cd59cd3ccd1fcd02cccdccb0cc9fcc82cc65cc48cc2bcbf6cbe5cbc8cbb7cba6cb89cb6ccb5bcb32cb09caeccadbcad6cab9cab4caa3ca92ca81ca70ca53ca1eca01c9d8c997c986c975c964c947c936c919c8f0c8c7c8b6c8b1c888c85fc842c83dc82cc80fc7f2c7e1c7d0c7b3c796c779c75cc73fc722c705c6e8c6cbc6a2c679c650c61bc5e6c5b1c5a0c58fc566c555c538c503c4f2c4d5c4acc477c45ac431c420c40fc40ac3f9c3dcc3d7c3d2c3c1c3b0c393c382c365c354c343c33ec32dc310c30bc306c301c2f0c2dfc2cec299c27cc25fc24ec231c220c20fc1fec1e1c1b8c19bc17ec161c144c127c116c0f9c0e8c0cbc0bac09dc074c057c03ac029c00cbfefbfd2bfc1bfa4bf93bf76bf59bf48bf37bf26bf09bef8bedbbecabeadbe90be73be56be45be28bdffbde2bdb9bd9cbd7fbd62bd45bd28bd17bcfabce9bcccbcafbc92bc81bc58bc17bc06bbe9bbd8bbc7bbaabb99bb88bb77bb66bb55bb38bb27bafebae1bac4bab3ba96ba85ba74ba63ba52ba41ba24ba07b9eab9cdb9b0b993b976b965b948b92bb902b8d9b8bcb89fb882b871b854b843b832b815b7f8b7dbb7cab7b9b79cb77fb762b745b728b70bb6fab6d1b6c0b6afb692b675b664b647b62ab60db5f0b5afb59eb581b564b547b51eb501b4e4b4c7b4aab481b464b447b42ab40db3f0b3dfb3c2b3a5b388b36bb34eb331b320b303b2e6b2c9b2a0b26bb242b20db1e4b1c7b1b6b199b188b16bb14eb13db12cb11bb0feb0edb0c4b0b3b096b085b05cb033affeafd5afacaf8faf66af49af38af27af16aef9aee8aecbaec6aeb5aeb0ae9fae8eae7dae6cae4fae3eae21ae04ade7adcaadadad9cad97ad92ad81ad64ad5fad5aad49ad38ad27ad16acf9acf4acefacdeacc1aca4ac87ac6aac4dac30ac13abf6abd9abbcab9fab9aab7dab78ab4fab3eab2dab1cab17ab06aaf5aae4aad3aac2aab1aa94aa77aa72aa61aa5caa4baa3aaa1da9f4a9e3a9c6a9b5a9b0a9aba98ea989a96ca95ba956a951a934a92fa92aa925a908a8eba8daa8bda8aca89ba872a86da838a827a80aa7eda7dca7bfa7a2a785a75ca73fa72ea711a70ca707a6f6a6e5a6c8a69fa68ea67da660a64fa63ea62da61ca60ba5faa5dda5c0a5a3a592a58da57ca577a572a555a52ca503a4e6a4b1a488a477a442a40da3f0a3c7a39ea381a364a347a32aa30da2f0a2c7a2aaa281a258a23ba21ea201a1d8a1bba1aaa18da17ca16ba14ea131a108a0eba0b6a0a5a088a06ba05aa055a050a03fa03aa01da0009fe39f else 0x2ba20911901a588d881868068a05cc46c34306902e61a1834b11b100f86986840d2c46c403e1a61a1017311b0d0c1a40b986860d2c46c403e1a61a1017311b0d0c1a40b9868605cc46c34034406902e0231834b11b100f869868405cc46c34306902e61a1f0d30d081a488c8818689c34c34206902e22302361a283481700d0f86986840d20d0446381a61a101711180d0c1a40b84c34106955354003502e22361a383481701180f928683434181a0d0d0488106840020d0506820c1a0b10058803c3416200f0d078683c358342e1ac1a170d60d0b86b06858344342e1a0d0d0686834341a1a0d0d0488d068400030682041a0f0d0414401a200d100688024464410343c1a0f0d60d0b0682c4016200f0d078683c341e1a0b0d041c341e1a08000060d07068383418230c118608c30461c1a0e0d0608c38341c1a0e0d0706838341c1a0800000108c20a1a21a150d10d0a08e86886870474344343823a1a21a1c11d0d10d0d08c2446c342f754f737f71af6fdf6e0f6c3f6a6f689f660f643f61af5fdf5d4f5b7f59af57df560f543f532f515f4f8f4dbf4caf4adf490f473f44af42df404f3e7f3caf3adf384f35bf332f315f2f8f2dbf2b2f295f278f25bf226f1fdf1d4f1b7f19af17df160f143f126f109f0ecf0cff0b2f095f06cf05bf032f015eff8efcfef9aef89ef6cef4fef26ef09eeeceecfeeb2ee95ee6cee4fee32ee2dee1cedffedd6edb9ed9ced7fed62ed45ed28ed0beceeecddecccecc7ecb6eca5eca0ec8fec7eec6dec50ec3fec22ebedebd0ebbfeba2eb85eb68eb57eb3aeb1deaf4ead7eabaea91ea74ea57ea3aea1dea00e9e3e9c6e9a9e98ce96fe93ae929e900e8d7e8aee885e850e84be846e81de818e807e7f6e7e5e7d4e7cfe7b2e795e784e767e74ae745e728e723e706e6f5e6d8e6bbe69ee681e664e653e636e619e608e5ebe5cee5b1e594e577e54ee53de538e51be50ae4f9e4dce4bfe4a2e485e474e457e43ae429e418e413e3f6e3e5e3bce39fe376e359e33ce31fe302e2e5e2bce29fe282e265e23ce21fe202e1e5e1c8e1b7e19ae17de154e137e126e115e104e0ffe0e2e0c5e09ce07fe062e045e028e00bdfeedfd1dfb4df97df92df75df58df3bdf12dedddeb4de97de7ade5dde40de23de1ede0ddde4ddc7dd92dd8ddd70dd53dd36dd0ddcfcdcebdcdadcbddcacdc8fdc72dc55dc38dc1bdbfedbd5dbacdb83db5adb3ddb20db0fdb0adb05dae8dacbdaaeda91da74da57da3ada1dda00d9d7d9bad99dd980d94bd93ad91dd90cd8fbd8ded8c1d8a4d86fd83ad811d7f4d7e3d7d2d7c1d7b0d793d78ed789d754d737d71ad6fdd6e0d6b7d6a6d67dd66cd667d656d639d628d60bd5eed5ddd5ccd5c7d5aad58dd570d55fd542d531d514d4f7d4e6d4bdd4acd483d466d449d42cd40fd3fed3edd3dcd3bfd3) else (if i<13 then 0xf8803074069c5302ec232834e29820e20017141a714f1000b880d20b38a78818465069059c53c40423283482982001701180fe8d1c00068d041a41780bb08c80d20a608005c04603fa34700000d1a08000003902001c81711181180fd8d00d009a807c2ea6088c4603e40f706903901ff1a2cfa311b8d0c1a4164d4dd0188caaa6e8007ac4603ee346069059d5355374062301f380f841a436407fc6896341001eb1180fb8d101a4165d4dd0188cae8007ac4603ee34506905935374062371a306f05cb1180fb8d141a4165d4cd0188dc68c07ac4603ee3440690597537406232820ba001e91180f98d181a5d4dd000b888cc68c0e40d207244604603f63470000022391a148d04024602e20f70de0d9059f1a287b8349a078d0099448c07dc6805404ca001fa03902c82982081721181180fe8d2b46820f60e407203fa34500000d20af8818464074c5302ec232034629e20017211941a714c1071000bb08cc0d20b38a78818465069059c53c404232834829820017011e8d1800068d040000000003492c82001c81180fd8d00d2007c2cb2ea7680e4003e506403901ff1a200f85dd1d01c8007c80e40b203fe3440720690640de12301fb1a3e10041a786806860d24460474340345a200d0d058802c4016200f0d078683c341e1a0f0d0786820c803fc3430696236201f0d30d0b8698684c341069223130d041900b809c08c068a0ae08805c447434504422301f61a21119100b8698685c34c342c1a0e0d07068205d847834302e023160d070683834142342021a1a11f0d0908d0808686042342021a1800434121a090d0608c8685046434282321a1039034812812011941a408c40d205dc35834406902e023183481770d00d1108c8684846840434300004341423e1a11fa034832211a10158682c3417400b0d041c908c40d284603e306901f130d04fd1d0308f08007cac34121a090d0486826a608268005d04604603e706904134002e82302301f382081741180fd0d141a4d4cd000ba08c868c0d268005c04904657f4069823023a1a2834beec11811d0d141a415c08c60d208804630690231034be401e811901a5f2208c08e868a07b0462069353340024823283482b81e811901a4d4cd000ba08c868c0d26a668005cc34434605fa034a118c1a409409386880d26a668005cc344346069b5301f18349a981730d10d141a4d4cd01868868ac341069423130d041c81a407c684603ec34361a082b822017211901a4d4cd000b9868868c0d379008207a846506902501f183481280f8c1a409407f86880d204a206902442302361a21a3211a1010d0c00010d0508c86840a1a090d040b820d2aa6a8006a446c34606955304154002e22301f61a41a48349119100d8682c34161a0911841a488c04c60d2e80261a08186820d2046c4003e4a1a08348 else (if i<14 then 0x2001e89181180f94378113c6860e40123100f8710030ee107405304102e02301fd1a3e200710028ee1d1a082f0176118c1d014c1000b808c07f468f8801c400a3b871003a341c400e20071003880131a098d04c6826341359044041d4032301f31a39aaea019180f9254dd0248c07c92a6482082e8008124603f634834092391a1cacca9ba049180f9656654dd0248e480a082e8124603e475524104172001f71a303903481c81709180fd8d1c3dc1bc191d5490407cce34127406475503d039720338d049d0191d4c0f40e5c80ce34127406475503d0392b8d041900e407c6e34124101f138d0415c48c405ce3403433f445904142302301fd1a3e8d040001f087b86c81c80ff8d14004f403901ff1a248d0415c1100b848c9046a34282351a1011a8d0819014c1000b408c07c068e0d20a6080046034522391a103482081c80f911dc3dc1c896407fc68058e1ee1b2aa668007a07205de348072f53f4002e12301f51a3801a414c1000b808c07f468e00034682000000d20c84b208963453f402e01fd1a2034ba99a039000f940b807dc687c34145e0a208786833e80d3c34c34406902e22361a270d30d081dd88c5c34c342e1a61a113b849783c34125e0920878683c34161a0838683c341e1a0f0d60d0b86b0685c358342e1ac1a130d20d0b8683c341e1a080fd108c0687834185e0c208610420ef8462039c23103b8340170c1df08f06806880ef846207702e4231a3b8517828821c1a087be2000ff0d00d1786820e5c3402c305e623170d30d0b8698685c34c34203922301a1c2f0490430bc1a1a0a2f041783c34105e0920878683c341e1ac1a170d60d0b86b0685c35834261a41a122f078683c34145e0f0d041c341e1a0f0d078683c341e1a087b81c80f8d10428821e1a0f0d60d0b86b0685c358342e1ac1a130d20d091043c341e1a0f0d078683c3418410c20861043c3583424410a20878683c341e1a0f0d0706838341c1a0e0d0706838341c1a0e0d0418341c1a0e0d070683834141a0801834100000e40a608004603e551a083202982001741181180f80d201c814c10008c07cb23410d9059025024e20f1a348d064683e34182351a1411a8d0a08d46840c80a608007c05d04604603e034907205304002301f2e3b83486c812812143dc1a4379104094ba8005dc40e34034507203e03922301f2a3b87b83483200ff8d180001fa611e8d60d10fd308f46b06887e80d2082847a3453f4c23d1a19fa017211a8d10fd308c07f468068a000208d4685046a3423f40b9823023d1a2c11a8d0a08d46847e803e20f70de0b9024423023d1a386f020e118c2e708c07f46b068a17284603e351a0a8d054682a3410f782302301fd1a287ba20820c1191468323410000042391a103482982001701180fe8d1f46820e4072048846026500000d20a else 0x2c341000fb0d0b8683c341e1a0f0d041a786840d2c46046c344069e1a1034f0d081a786840d3c342069e1a1034f0d081a786840d30342e1a0811f0d0b8683834101fc1a170d078683c341e1a0f0d041a708f86800480d3c3420038683c344342e1a08000000000000000004821e1a0f0d0400000000000c34167465304162301f2b0d0400060d0706838344342c1a093a20d0818341003868200001c341e1a0f0d0400d20b248205d846506905924102ec23283482c920817611941a41649040b908ca0000007dd823023a1a203482b920817011941c415c90408c05ca0d2f9048205d046046606935324102e8232a8d0419016414c10608c07c068e0e40a608204603e507405905304182301a0133c8d0686832341a1a0d8d0586820d20b20a608204603fa34700346820e40a608204603e59f406905905304102301fe1a402c82982081180f978683c341e1a0e0d040006802e61a183a02cb29b20911958682c341077623103a02cb29920b11958682c34161a082982081701180f941d014c1040b808c07f868e0e80a608204603e5c1a08000070d0400e1a0f0d10d0b8683046c34282361a1411b0d0819016414c10608c08c07c06900e40a608204603e03c6c1a08000060d0706838344342c1a093a20d0b0682000000060d0706838341c1a093a20d08000000061a0b0d058682c34161a0b0d058682c34105304102e023203a029820817011941d016414e1041040b808f8691834100000c1a0e0d070683834434227441a160d040000000000000038683c34434200000070d0494f8685c34434200007e80b205d84783453f405902ec23c1a29fa03482c817211e0d18fd01640bb08f068b84603e23f405902e42341a280003f405924102ec2328000030d058682c34161a0b0d058682c34161a0b0d058682c34161a0b0d058682c34191a089184193d4fd000b848c08f46804d18401c200e10045041040b908c08c07f468f8401c200e100708038401d1a09a982081739020994fd116416410508c08c07f4691a341022c8a082081721181180fe8d2000d1a087b82cc2089180fd8d183dc378b7436414a903c68e0e80b20a6083c8005c84604603fa34a45e0e8d0617820d20c81b20b26a7e34607406425905904122301fb1a01a483b83492c82c82091181180fd8d278683c341e1a0f0d04000740596536402232b0d041d194d9000b988cac34161a080000038683c344342e1a08000060d0706838341c1a21a1120a0d08000018682c34161a08000060d0706838341c1a21a1120a0d080000000003868200009038685c341e1a08306838341c1a0e0d041050684000000c1a0800000310708c48838462c414231620e118910708c07f0688882846200110708c4000014c1000b808c07ca0007b84000034b29b20017091951041075000b88001f0f))) else (if i<17 then (if i<16 then 0x9180f8814c08c06860601c5302301f1e298118808c06848a603e28530c298208a14c20cf0a6482385384002402320208118809008c4c8203e203001f14298120118c08c07c404603e202301a13a048d18d0cd024684046640202301a101180d0b08f0685847834202ec1a101760d0908d068c6870800462840032023182038d081c808c40820462023081901189c6830a608204630690231034811881a408c40d2046202371a101180d081c808c4064046202301f101180f8b08f0685847834202341a31a1a11e0d0b08f06848468346343355081201180b8c004603e201f0920811880c808c4e341072023101901189c682048046202402310118098808c04c4e341e1a0811f0d081a588040d3c342e1a0f0d041a78684c401023e1a170d040c401e1a0f0d078680685c341e1a081770d085000bb8687c341e1a0834f0d0807c208203fc343e1a080ff0d50d0c1a4113868744603fc343041a23e1a1f0d0450007f8686c401e1a0f0d078683c341e1a0834f0d081a415f8687c341069e1a1001a5d4c40d3c342e1a08348a9f0d0c1a5880405cc40202ee1a101770d081a6880405d4402069e1a1034b10081a78685c34102ee1a10a070d0a50007c40d3c342e1a0f0d041a58805c34101f0f0d0588020d3c34201f0834f0d0b8683c341069e1a170d00d081a407c40d3c342069e1a143400f880bb868405dc342e1a0f0d07868205dc342069e1a1034f0d0b868068405c03f434335361a170d0588020d3c342023e1a170d0706820d02818343c1a081760d080bb068405d8342c1a08a9e0d081a70680687834101fc1a1011e0d0854f068405d8342140c1a1017011e0d0c0bb068407b8342153c1a101760d080bb06858341c1a08a981760d0f06820d2047834302e01fc1a180fe0d080bb068405c03f8343153540c1a18a000fe0d0c0b807c405c03f034306442342018108d08040d210034841a4205c1001710d080b82004118608c3046106908128408c20d214234201000902846840206908348400d210240800f420d36a6846840406908391a9881a4205c1003904d4c2002e21a15a0211a100cd0108c40d20c82000000034ba9881a508c40d2106902e21a181700f8809008c07c66a605c03e33400801a408c4021a090d0400041184000034ba9880f420d204a0463069e1a170d078682446107202e1111910080b98805c34102ee1a101730d080b820069140023e1a2034b10081a78685c34115361a10348786822a7c340343002b8a9d0d0c88c880444610000000004c2ea6122308a0011b0d0e5000d44281c34214002301f61a271000f881a78684c40161a08007d8684280047c343e1a0b100586820023e1a170d0786820cf2a6c40307215361a18a9f0d0854c07d86806882a6280047c340345e1a01a170d0454f8680686047c342223081880 else 0x319fa04fd022a6100220608c304618230c118407c21ee046206911a10108c2001f080f843dc500417204804630de0ca9a1188fd02000a98120800d2046201f080004603e200010460462553823128d0408f4684a3414410aa9e8d28d0c00d203fa34a34402308349a008178d4c403e105e01f10348308816708c46a6048046307202310348488c08c400420061002080e34244022381e186f0436421b2e3420f7087b843642c4616230b8d0408c07c404603e202371a1011840c8210001a408c4be80d363430696230151834f8d081799058e588c8aa6c4602a371a0ba001eb1cf8d101a436588dc68804603420728c8620186c81180f8e32188041bc0bc28c8015106f02f0836432049e899024f44c8b1a18293118817990588c61b2c46e34302301f101180f8808c06841b2046034302301a106f04365c684046171a081180f8808dc6840d24460463223023103903481180d123d031e8046202301f1111840004408097808c5847a342353b1a13a9817081a588c08dc688e8007ac73e34401ff1a13a001eb1cf8d10d4c07fc68600596230231ba001eb1c8dd000f58e6c68805c03f6343c23c1a1611e0d0908f0685847834242341a31a1ba980f881c808c405c03e202301a102f00f8a14d54c08c6046034205e023102f0118808c0684cbc44620690d91034b8d0888d8684080046034302301a102f00f8808c0685a341023d1a122f611881a517858bc8462403024023102f0118836420bc1b204630d902371a183201180d0c17808c40bc046207271a102001180d0c17807c40123081180d0917b46b06868bda358343c5ed1ac1a1e2f00fa8d20d13c6a04c408203f4343059440162001c8836438801840082cc2008366c68408163428400c2004101c6848801e1a013168d60d0b46b0685a35834202ec1a1020a8d20d0e1000c808c6080e342453a1a16298614c21ee1059c53102cc298914c20c530e298514c38a62a620f734010036554c400d971a10010a60480463d1a0e8d07468205da34251a0c29d640208c14cb2346860d21069c231034e11881a508c40d38462069423107b81f8918c02461038d040e420d21b22123f1a013187b9a02900c00001c68224602a244112310048dc68424611230809841a708c5190a4028c84411064074683a34100000b21d1a0e8d04508d0046a62a6206901f01a181700f80d0c16408c47e80bc68030230a299a9881d00b840bc6a62840340102100f8814c0b8424603e200310008c07c647204603e34400a2000f8a1003080104071a11208408c2046102371a107b843dc203e101f0b8d04111c684088634202301f101180f89c6820d2047e340344023320101180f8808c07c40bc0462059080904204603e202301f112c8408c07c40bc0462000f8408c2064046271a08120118808c07c4e34102301f10) else (if i<18 then 0x2f46428d0c1789064806c8124020d908008c07c400d9086c8408c2190102301f103481180ff8d1036432040a6046034306905302301ff1a286c843642190102301a11640417946840a60832803c4002301f1a2004188004603e323902301f186f06c88003e102301f101180d0807c3c341c41c2310208118808c07c49e8082202301f10120118808c07c40d205c202301f101701180d0c0e608c07c60b304603e306905902301f203481c81180f901bc88ec68058805c102e081701180d0c0b82048046203902e22301320118408c07c405c046034306902e023013201180d080b888c07c605c10720803dc21ee08220023d031e8102ea1a1017043dc0b8405c102e08036421b20ae200001b210d90817041c80b807f46880bc07a201fd1a10170408c04c403e134008208409008c407a05da34302ed1a10348118808dc684046640202e71a122f041c986840e41e1a01a170d07869868405dc34c343e1a01a170d30d0b8683c34c342e1a01a1011f0d0b8682047c342e1a0811f0d087d38685c341e1a0f0d0408f86850bc10de24014208494c10440bd0a620f70de1011f0d0b868203fc34202301fe1a187bf0d087d008f868605dc34245e01a170d00d0b8680685c34034205e0811f0d0b868208203e20f7e1a107bf0d0b86820a605dc34305302e02301fe1a2f0d041780b85c341e1a081770d0817820bc1e1a082f041782865c342e1a0a19311f0d0e9078685c354342e1a0829f0d0917828bc1e1a0f0d078683c340342023e1a170d30d0807f8685c340342023e1a170d00d0b8683c358342e1ac1a100ff0d60d0c08f86b068603fc34261a41a170d00d0b86820a7c342e1a0f0d0408f8684047c342023e1a170d078683c340342e1ac1a170d60d0b86b0685c35834261a41a170d040f786806868821441080ff0d0807f8684882184104110e470d0810786850a608221f4053041a40e1a2a20841040b4403fc342067041101770d60d0c0bb8685834434201fc1a112060d081040bb0686046034202401f1034812081c8090404603426410834b118988d868404603e202301a103900f8808c06840721069c231034e11880b908c40d284603e306944182301f202cc1180f8e08c08c07c058805d04603e3025f1a1017040b9c684046102371a101901189c6821bc10250812b8d080b821ee04603e30d9081180d0b86820d2c4602a302e223015182f01c817111901a408d8806082472046323902310390348118c10408c405c102e0817040b8c68405c10644231003642071a0809840b8205c102e71a101e8746b0685a35834202ec1a168d60d081a5068403e1001c68207c4462001c6821ee10f7080f8419005440038d04193c6840eec4620776231311b8d080bb468405da34202ed1a101768d080b9468403fa342041c1a100fd050040069c2302 else (if i<19 then 0x82f011881c808c40e40466403032023103938d081a41911646aa604620320231011b8d0808c06840820462650623100fb8d0808c06840e405c20410231133832429b8d1114c3841a358343c20d1ac1a180fe8d60d0c07f46b06862e9840a34834400019088fc68602230a7a073d039e81002c8208896408c44b21023015101180d08008202a20039011883d02046034202e01f101700f8808c07c404603e271a081180d0bc680684082102301a178d00d0810408c44bc0462223023112c9118118c0682002301a147a043d020d2046202301a1034f8d084680544c461374023108d00a89c68228210111c8d0a4682ea7234634302301a107a01180d0f08f06858478342423c1a1611e0d0b08f06848468346343c23c1a1020811881a408c41b2046e343f1a81510390118810408c4064046271a0820811881c808c44bc0820463032023138d0554c2be81002c9118816408c40b2082046304102310208118990488c5c34c3420410231320b118b8698684c82c46204102310010408c40820462041023102c8208118c7d010710008c8083880046304102310208118810408c41ee1bc204102310007c208204603e30f7a4010fa020d200119000d205c204102310208118810408d88061ee10f708118490588c403e104102310208118810408c40820462c41c231220e118b10508c07c78838460463441c2321a1a20920a118c10408c408204621530800082046204102310208118810408c40820462c41c231220e118b10508c5883846244124142318208118810408c40820462c41041c23023200f8410408c4e80101f081180d0808c06840ee04620778f4059023203bc7a0390119008c07c04c604603e201f0c20840b8205c102e31a10000bc083080046402301f101700f8816408c404603420770446231c7a0610009008c62b2100ac840c808c4e341032023103b8118807c203e1019180f88c8c07c464603e231a083b9918810420ee0822077323100f841dcd4cc8c603e1359753323199190a88cc8c8c4646644212301f12918407c2482124191a107a022491f8d48d1590424bc046292391a10918548c2a64a46212301f1291854c948c4a46a442d4051a31a1aa018d0810548c07c60b2e80046392391a13a00119900e48e4684a4603e252301f129180f881de10007c60ef08003e307784001f1801dc08c40640462077023118d0408c07c404603e235302301f1812011880f40e408c66800720640464340039024023201c81180f8c1dc07c40ee03e207701f103238d09d55c6840c8e34271a083238d09c682ea6e34271a0b8d041bc08c404603e206402310190118808c07c404603e202301f101180f881a408fc6806880b30822c40082ca2088165900404603e202301f1034811f8d00d12bd024a648024410b200408c07c40b2882264008 else 0xc3402a204102310208118816408c40460262024623101180f8808c07c404602e026307203f103b8390170c08c06841ee44603e307202310208118888c08c44460462223023103b8408c06840ee04620720231011841a408c40d20462077023103470d30d0c0b888c40ee05c03e342302312118118908c08c40b304603e307282301f182cc1180f8c96586840e803e202301f102c81700f8c0b807c405c03e202e01f107b86c81180d123d01a408c79e8046a40302301a101180d0808c068408203e202e01f10208118808c07c40460342141123178d0098a468c684ea7234634371a09a981738d0c0b9c6841ee1b2202391a31a19a9811c8d18d1007c2046034202ed1a1011a8d18d0c08c0684082046241a31a101180d080fc08c40820466403041023101180b080e34171a31a1039020f200c1dc0b840bc046202371a101180d0816714c40bc05c202301a101180d0810421e81078d04378200d90f8d079002c80634271a0b8d18d081a408fc6806880b204622410c8d18d08906468523463421230)))))
def ql10 : Nat × Nat × Nat × (Nat → Nat) := (2385,12,16,qd10)
def qd11 (i : Nat) : Nat := (if i<22 then (if i<11 then (if i<5 then (if i<2 then (if i<1 then 0xb65405c1202e08016e480b62405a9202d480164500b81405b8a02d450171680b8b005bda02dad016b680b5b00595a02cac017770099847e4443f1de1f8cd0fe5447f29a3f6491fcc48fc2287f38a3f5051fa628fe8b47f3da3f9ad1fcb68fcbb87ecc23e2221f4a88fa5347d45a3e96d1f5568f99847a4443d1de1eca88f65347ac923d08a1ed028f67147b28a3d8851ef1100787403c3201dd900f0a80785003baa01d9500eab00782403c1001dc900ec480752403a9001c8a00f160075b003958012221e0ef0f05587929a3c08a1e2628f0118793da3c2ee1e1110ec778763343b1561dca68ec2287698a3b0461dcf48ee8b4773da3b9ad1d9770ec888743bc3a19a1d0ab0ea534741143a0461d4d48ea2a47545a3a9ed1d4d68ea5b47515a3a2ee1d6ec80382401c1000dc9006c480322801c0a00e04006e280361401a8a00d44006428032100188c002221c1110dc7786ed58372221b0ef0d85586c444351de1a8ab0d43386ad58351de1a0ab0d033868114341de198ab0cc228663bc311ed8c0d6c585b62c05b16222180ef0c0668602ac3008a183560c06685e08c2f2ac898ef0b8966224b3101de168450b4ab218d582c222159110a8778543db0a1ad85076c282b6140db0a02d85156424888523bc2919a14b560a4ab20e444281de140cd0a0558504442719a138ab09c3384e3db062ac821110987784c33426156130670982284cd5826222128ef0946684a2ac2504612d168965b44b0da2519a12045090118484442319a1182308c778442ac2208a11356084888404441f1de0f8f6b446b5a21dad10ad68836b440b5a24441e1de0f0cd079ab03c4441d1de0e8cd0745583a35ac92220e0ef070668382ac1c0ce0e356070888363bc1b1560d86706c228364441a1de0d0ab06822834558c22220c8ef064668322ac1908a0c8230649a56e35ab62220c0cd060118303bc1708a0b9562706682c114160460b130a4998426444131de09330844888223bc111ed470d6a383b51c15a8e06d47016a3998420444101de0832c84066820d5810222078ef03c6681e2ac0f222070ef0386681c2ac0e1ad41124a019841a4440d1de06b2c8346681a2ac0d0ce06b30830888183bc0c15606067031924181140c19a0584502c118164440a1de050ab028228145587c2ac3d1561c8888123bc0919a048ab026634129920908a049110207781033408156040450201181020a66222038ef01c6680e2ac0708a0382301c7780c3bc0519a0292491998408444041de020cd0107b4881da440ed2011100c778063340308a01b30808888043bc0219a014a88099240411402a050128280a5b4045dc020c51f9168f87b47c35a3e16d1f0768f8ab47c20a3d0c51eb30804888023bc0119a008ab0065440329a016490084500466800114004c5000230004b45e20a02 else 0xf1de2f8cd17cbb8be5593826d9b8f6cdc6b66e25b370ed9b856cdc1b66e05b372ad9b9564d495668559346612f111178778bccb25e19a2f356179984ba4445d1de2e8cd174558ba5dc5d19a2e0ab170bb8b8559322ac988a8cc09b660559306612d91116d974b63bc5b6592d8cd16d954b62ac5b9512d911168668b42ac5a9512d067168bb8b44db2f24997330964888b2cba591de2ccec965954b2b2a591562cca8965634b219c592ee2c936cb492658cc2582222c32c960668b0caa581562c4a8960338b0444571de2b8ab15c338ae1145726d95956cac91654cc2562222b50e959964acbb25619a2b32a958558ad2a25664d2b06715a624ac5dc5626d94956ca5984aa444551de2a8ab154338aac925508a2ace29565b4aa48b2810594136ca1984a84445465d2a0ef151964a8334546552a0ab152544a931a546492a4c4951324a81145466d2a4f69512b0a85dc546612991114d974a63bc53655298ab14e544a6c9a530ce29b2494c228a6444521de290cd148558a419c529892904514a714a518a520462917714b8880fc3a07e1903eec81f8540fc2807d9503eab01f8240fb1207d4903f0281f7140fa8a0726993936c9d984a24445165d288ef144668a2caa5115628ca8944338a2c925198928845145914a2a0a518c5288231459b4a2b58512ee28934c988a64c4db2626992b30940888a0cb25019a2832a940558a12a2500ce28322941414a008c50a2d281771409a648cc24f22227b2e93c7789ecaa4f15627ca893d9349e19c4f6492784513e8b49f3da4f2ee27934c8c9b646cc24e222270ef1399649c3344e655270ab13a5449cc9a4e0ce273249382289cc8a4e9c5272829381189ccda4ea2d274f69397b09d35a4e2ee27134c885a6444db2212d91134c849b642cc24d22226b2e9347789acb24d19a26b2a9345589b2a24d649268451359149aa0a4d04626b369368b49b3da4d9ad26cb6934bb89a4d32066126111131974983bc4c659260cd131954982ac4c9512632693033898c924c989260451319149938a4c505264629301189945a4c9ed264d69325b4991da4cdd9028cd12992494cda4a2ee25436926ab492cc24819a2433091c7788f3b24764923d0491e8b48f3da472ee23b309186688d412469892371101387409c3204dd9027160135b0098d804661229111147788ac324519a22b249158248a114455ac2297711477888c924408a224f69125b48915a44aad2233090c8888743a435d9218cd10d92486b924308a21d1690cbb886cc242222210ef10992484b124208a2150290a8b4853da4219a20b249042288340a419c520cd69054b4829da412ee20b249002288115a40aad2071100f87407c3203dd901eea80f65407c1203e0801ee480f62407a9203d4801e4500f81407b8a03d4501f1100b87405c3202dd9016ea80) else (if i<3 then 0x4669022ac819cd40d04a068b5033da819ad409772059850044480659400cd2005590019c80a09404c4a025250119280e2206f0e8378641bbb20de1406eea8376541baac0de0d06ee68376341bc580dd6c06b309fc888fe3bc7f1563f8671fd924fec127f08a3f9771fd984fc4447ea1d3f0ab1f8338fcc927e5c93f0451fa814fd45a7e2ee3f3309f4888fa3bc7d1563e8671f5924faa927d08a3ed029f6714fb3da7d2ee3ef1103387419c280cdd5066ab03383419b9a0ce090670403372419a920cd480666483322819bb20be0905f0402f624179140be0505ee282f88815c3a0ae14056ea82b55815c120ae08056e482b52415a900ac8a05130d5cab2ae8d87b6ac3d9111e8ab2accc2792223c8ef1e1984ee4447765d3b8ef1dc888ec3bc7619a3b0f6d4c6b6a61db530ada9836d4c0b6a655b532aca892ad40ab2a0cc2752223ab2e9d4778eacb27519a3ab561d4888e83bc7419a3a0ab1d1984e64447365d398ef1cd954e62ac73951399771cc888e43bc7219a390ab1ca634e45594f0eda7036d38ab69c31b4c2aca615652c6b6941db4a06da5156d29984e24447165d388ef1c5964e233471655388ab1c6544e2c9271a0938b369c66b4e28d8712ee38924d243269255949661381111c1974e03bc70659380cd1c1954e02ac70951384c69c11b0e0d5870222378ef1bc558de9926f08a37922d21984dc4446e65d370ef1b8668dccaa6e156374a89ba634dcc926e609372649b8228dccda6e5ac371771b89168c4446d1de368ab1b5324da1146da0536ce29b6514dbc4409e1d04f0c82776413c2809dd504eca82755813c1209e0804ee482762413a9209d4804e45025984d84446c65d360ef1b1954d82ac6c951363249b1324d81146c222358ef1ac668d62ac6b98d35a649ac228d740a6b04635f1102387411bb208e14046ca82355811c1208e08046c482352411a9008c8a0470282371411a8a08105a2934d15984d44446a65d350ef1a8668d4caa6a156354a89aa634d4c926a609350451a9914d4a0a6a046353369a96b0d45dc6a205a2082d109a688453441eda2082d0c9a68615943661349111a6874d2cb26919a34b2a9a4558d32a26964934ae49a5324d21146964534a829a4118d345a694ac349771a4416844d342661341111a1974d03bc68156344a89a1924d0b126808a345169a27b4d05dc68105a0934d05964ce334676493384519d914cf40a675053382319d9b4cf35a672ee33882d009a6802d3401059f934cfc3267c20b3e2699f054cf88b67c3db3e1ad9f0b6cf80b67c20b3d2699eb30998888cccba661de3332c998668cccaa66156334a899a634ccc92664c933045199914cd40a665053351699a7b4cd35a6696d33456998bb8ca4c33c2ac9e356190888c65593b66131111188778c2cc2602223032e980778c04445 else (if i<4 then 0xae22256d0eab57655a334ad156569772b4ab2f0cc2ac2225650eab196558bb2ac19a5632aab055958444aba1d55aecaac669562acab0ce559772ac876ee4db772acbb8ecdd8ab2ec4db752acba9565d198554444aaa1d5532caa976554334aa655550ab2a99355419caa22254d0eaa45595219ca908a54936dcd98550444a8a1d5432aaa055950c9aa80ce54324aa022951c4418e190c7028619854e444a75d9538cd29d9554e2aca764d5386729d9254ec12a708a53b22a9c1194eb58a72ee5390edc48a6e24db716615311129a8754ccb2a65d9530cd2999554c2aca664d530672999254c114a664553516a9a6b54d2daa68ed53456a98889483bca412db3956d9c889463bca31565186728f5242fa9017c8a0b8ef28855944c9aa20ce51045288bb944444a1a1d508ab2859354219ca108a50d16a84bb942cba9f1de4f8cd278bb93c559646594e8cd274779383349c0ce4e1772709b6c65596326db1036d88ab6c4559612acb0124d7cab2becc29b2224d8ef26d965363349b64d4d86726d5b136d589b2224d0ef268339341149a245af136d79985324449965d4c8ef26466932caa9964d4c86726592532c12995494c8452659b532b589956c4c977264916bacc2982224c50ea6196530bb29819a4c4caa619353019c986494c2a4a602293145a982ee4c330a5c8892ecba971de4bb2aa5c5592ec9a970ce4bb24a5d5252e1149719a4b0672582292d40a969c54b023258bb92dbb216e090b70405b6242d91416e050b6e28589a6b84449565d4a8ef2545592ac9a950ce4ab24a542292b3da952ee4a8cd25033928c929408a4a502a527152808c949a94a1772509a6b62535b26dad934d684a6b44db5a149ac934d644a6b21535926dac8d6d644b6b24d358129ac32ca4c66926c9a930ce49b24a4c22926c8a93a0549ce2a4c1192735a938ed49c56a4f5b0299581466148911244bb923c44131de48330a3c8891f43a8fa2d47f0e8463b51d15a8e86d47330a348891b43a8d659468cd235985184448c1de464eca327b5185dc8c6614591122d965163348b99545f1104387421c3210dd9087160432b0204448a1de450cd228559145dc8a22244d0ea24669122ac89a2d44977224889103bc88a19440ab2228351145a889ed441772238881fc3a0fe1907eec83f8501fbaa0fd9507eab03f8881dc3a0ee19076ec83b8501db2a0ed5607330a1c8890ec3a871de438cd21c5590ec1a870ce43b24a1d9b50e5dc871564306721a5b50d1da8686d43330a148890acb28519a428ab2157350a19c85a2d42b30a10889083bc849d9422caa1055908b1a840ce42324a128250945a849ed4217721198506444831de41b2ca0c669062ac830ce41b24a0e825073da835ec41cd6a0cbb906cc2822224132ca086690419c82a2d414d6a0a3b5050da82222408ef2 else 0x369975b43bcda6596d0cd368559b539ada6496d504b68229b4d58da2226c8ef364669b22acd99cd6cd04b64229b208cd9269cd32cb60669b0c92d808a6c0233619b5b05dcd8209cc934e648a7324d398269cbb30b5c889aecbad71de6b8ab35d925af412d708a6b82335cbb9ae4d396269ca8b4e549a7284d393069c9816e4c9a724cc2d62226b32eb58779accb2d619a6b0ab35a735acc92d6a096b02335a8b5ad3dad69ad6b4b6b5a1b5adad821cac10911351ab1a85dcd4e22100ef34c889a543ad2a2d6970e87e3b5a315ad186d68911340669a1c441ee1d0f70c87b7643dc581ecac0f11133c7799e334cf1566797733c8899d43ace19a670ab33a8b59c5dcce222668ef3345599b41acda2d66cf6b34bb99bc441de1d0ef0c8777643bc281dd560e911331875983bccc19a660ab3318359819ccc6ad661773305599619ccb96d65c76b2e1b596444ca1de654ecb2855994b1aca0ce65504b2a8b5945dcca222648cd3243399345ac99ad64c76b261b592444c81de640cd3205599139ac8a0964516b226b5905dcc8222638cd31c5598e19cc7a0963cc4b1e3258fc441ce1d0e70c87376439c281cd560e70687373439b1a1ce2c0e6b607388837c3a1be140deab06f83437b9a1be090df0406f520379921bc8a0df1106b87435c281ad560d70486b82035a901ac8a0d17731888988d58c42ee62130e449b722cc2c322261b2eb0877985558c2222608ef304669825dcc1255c795663d98580444c065d600ef300669808d8c06ac600ef2fc6697e5dcbf261c712ee349b71a5598d2acc6330af88897ccbabe1de5f0cd2f99557c2acbe2225e8ef2f46697a2acbd0ce5ea362f4bb97a4c38b26dc5b2eaf077978334bc6555e0ab2f033978c92bc66d5e2362f0bb9784db8a209c4956624827105598826dc3916e1c6b70e25b8706dc3956e1c8270c55986249c2904e14ab30acc2bb2225db2eaec77976334bb6555d8ab2ed9357619cbb62c5db562ec889743bcba1565d0672e982574114ba6615c9112e5975723bcb96555c8ab2e59357219cb96495cb04ae422972444b81de5c0cd2e05597019cb86095c0452e011970b58b82ee5c70e86776433aac19e090cec486752433a9019c8a0c934e109b7084d38365d5b8ef2dd9556e2acb764d5b8672dd9256ec12b708a5bb34ade7a56e4d3821a8c1136e089a70235181169c0936e044b7024d3801a8c0136e009a6fe3517f26dbf904df89a6fc3517e0a9bf136df89a6fa3517d1adbeb30ad88896ccbab61de5b0cd2d99556c2acb664d5b0672d99256cc12b608a5b322ad81196d3dab69ad5b2d6ada5b56d1dab68ad5b1772d4986f85597c6ac5a330acc889668d8b32ee59b30ac48896345ab1661581112c287560444afa1d57aecabc6695e5dcaf1d9bd1565e99855c444aea1d5732cab97655c334))) else (if i<8 then (if i<6 then 0xd1d0ce8eeab0d75b06baac34d481a6450d355867a9033c8a1991146c33a364451a1568d06746822a343bd189ed8c456c622b62f2db161de8af110c376461c2830d56187040c35206191430e2c186b60c32b061bb22fe0417ea20bf2105f88c2f222899114489678e559c722288b2ec4477a22d5911259e30d6f18ab78c4b3c52ace2911441976203bd101568835644088a1ecbb0f1de878ab43c22a1fa902dc8a1684543811a1c5dd0e169e0854efc88a1acbb0d1de86d0cc3455a1a1150d04686d16c367b61b2db0d8ad86c36c375b0598d82ceac167110ac88a171db0a8ad85436c2888a1233509e2214eec8a78b0538d829eac1491142066a102ad082ee8411141c77a0e2ad079ed8397741f88851bb228e14146ab0a38884fc2827d5613ec689c77a0c2ad060ce8304541a7b60d2db068ed83456c1888a0a19d0508a82d16c163b60b15b05222820ef41055a0819d0408a8271109b7644dc2826d56136e689b6344dc5826d6c1375609877a062ad0304681cf6c0e5b6070db03222810cd40811a0545b029ad81436c0888a023bd0115680d16c067b6032db01e2212eec8978504baac25e0412ea20971184acbaff1de7f9566ed965fc334fe19a7e8673f4bb9facc2fc2227e32cbf0669f819cfc26ddd096ee82b77455bba2acdcb30bec889f6cbafb1de7d8cd3ec559f619cfb6497d8453ed8b1f6d58fb19a7d0673e8229f408cfa4ec7d1773eb76449a8824c4612134ee09a76e4d3b6269da834ed49b76a3dbb512dda934ed1965f2334f90ce7cb24be4229f208cf99ad7cc76be61b5f2444f72227b0cd3d8559ec25bb12add89113d4669ea19cf5e2211f0208f118465dcf4222791566bd985e2444f1661781113c2875e0559ae661779113bc779df3b2ef6ac779566b5985dc444ee65d770ef3b8559dd3daee4ac771773b9985da444ed65d768ef3b6765da2aced222760ab3b1635d819cec2ee76124eb09b758cbaeb61d758ef3ae765d62aceb58d758673ad9b5d65dceb661751113a8559d4b1aea0ce75330ba4889d2cbae91de74cecba4559d2b1ae90ce74b24ba6825d2114e9d56110ef3a0559d019ce8649740453a0119d05dce86617391139c559ce19ce704673d16b9cbb9ce2d3a826dd4096ea1985cc444e665d730ef39a765cc2ace658d73067399925cd412e604673516b9a7b5cd2dae68ed73436b9898748559a44ac72356390889c6559a366171111388889c23bce166170111381975c03bce01edd08d6e843b74215ba106dd0816e84ab742559a06616f91137c779becb2df19a6fb5637d985bc444dea1d6f32cb78669bc2acde2ee6f111374669ba2acdd249cfb30b70889b8cbadc61d6e0ef371965b8334dc1566e4e6b719b5b85dcdc6616d91136d965b6334db1566d8f6e743b73a15b9d2adce876e70ab7385599b6616d111 else (if i<7 then 0xa173754b9b2a5cd562e330ccd97666cab3395199b36ccdab6665dd336619950ecc996664cab3295199516cc8bba64cc33165d98d0ccc5956632a331a0d98d16cc67b662d59312ee98b30cc196660cab3095198506cc273660cdb309ed984d6cc0bba61c445ae192d70a96b850b5b2a5ad562d70696b534b4cc32f65597ca8cbd8365e8d92f2ee97b30cb99565cb2b2e951972c6cba8265d45b2ee1d2cf0a967754b3aac59e0d2cee6967534b2cc32d65996b2acb65465aa9b2da0996cc4cb66b65a5dd2d6619632ccb1956592a32ca09964c4cb28b65935b2c96d961774b3888afc3a57e152bf0a15f558afc1a57dcd2bea695f824afa9257cc92bb30cad97656cab2b95195b26cad9865543b2a655954a8ca993655c4456e192b70a95b654adc1a56d8d2b6a695998652cab2995194b26ca7888abc3a55e152af0a157754abaac55e0d2aee6957534abc1255d492ae6495598650cbb28655944a8ca3888a9c3a54e192a6ec953854a9c2854dd52a6ca953558a9c1254d892a6a49538b0a9ad854e222970e94b864a5c2a52e14296ea94b654a5aac52e0d296a694b8b0a5ad85266193b2ec9d9564f2a32798993f0e947764a3c2a51dd528eca947558a3c1a51dcd28ec6947534a3c1251d8928ea4947324a3ad851655934a8c9a3164d2db268ed93330c959564b2a325e222870c943854a1b2a50e0d286c6943534a0cc324655924a8c9193649c3a4fe1527eea93f5589fc1a4fdcd27ea693f8249fa924fcc927b30c8d96646cab2395191b26c8e62647c3a4ee19276ec93b8349db9a4ed8d2770493b6249d9924e66191326c8a3164545322a2d91476c8998642cbb2165990b2ac865464331321a2890cb44878889bc3a4de1926eec9378549bc284ddd526eca9375589bc124dd8926ea49378b09bad84d6619032ac8254640c9b20e222670e93386499c2a4ce14266ea93365499aac4ce0d266e693363499a9a4ce09266a493332499bb24adad2563692b86491c3a47e0923f1691f7b48fada47d6c23e3691fab48fddc47e192370e9177648bc1245dc922ec49175248b91445ded22ed69175b48bad845cad22e56117ab48bddc45dc9226a491388887c3243d9521f0490f62487a9243e0521f1690f6b48795a43e1d216ea90b82485b9242d492164510b76483c1241e0820ee49076248391441e0520e5690782481c1040c8a207110ff8747fc323fdd91ff0a8ff7547fb2a3fe091fec48ff5247fc0a3fdc51fea28ff8b47fc583fded1fed68ff5b47fad83fead1ff770ff8547dc443de1d1ef0a8f78247bc103ddc91eea48f72287bc3a3ce151e6e48f352479c0a3cc851e70e8ef86477bb23be151dec48ef52477c0a3bc851df0e8eb86475bb23ae151d6e48eb62475a923ae051d6428e888a3f95837d561b11147833a3d45b1e8ed8f436c7888a3a2a else 0x1a93e0949ec4a4f32527b5a91d6d48e76a472b5238da91eee48f112378651bc3a8ce1945f0ea2b76515b2a8ad56456f6a2b6b515ada8acad45636a2b88913c3289d9544f16a278b113b5a89d6d44e56a271b513ddc89e1d446eaa2355911ad888cac4470ea1f7650fb2a87d5643f06a1f7350fb1a87ded43ed6a1f5b50fad887ced43e36a1fbb90fc4485e1942ecaa176350bc3a84dd5426ab21383509b9a84e094271120f87507c3283dd941ecaa0f83507b9a83d8d41f04a0f62507c5a83e2c41ef6a0f6b5079da83c6d41f7720f86505c1a82d8d4171120787503bb281e1440eeaa0765503aac81e0940ec4a0752503c5a81e2c40ef6a076b503ada81d6c40e36a07bb903c4480e194070a20365501aac80e0d406c6a03874ffbaa7fd563ff069ff734ffc127fd493fe649ff888fdc1a7ee093f6a49fb324fdc447de1d3ef069f7734fbc127dd493ee649f7888f4cc3566acab177559986a943b54a2daa7111db874edbb2768ada9b30d4a876a4cb352661a8b2ed46766a2cab519eda8977545986a0cb350e223a70e9d3864e9bb274d953a70e9cf754e7aac73d6c39e561cf888e5c3a72dd93970a1cb654e5aac72661a7b2ed3d8769ecab4f951a7cc6d3d1b69ed5b4f6aca797753d9569d2a34e96da7330d359669acab4d951a6cc6d368b69acc34c65da64ecd3195698b2b4c951a6504d328b6993db4c2eea6330d2d96696cab4b951a5cc6d2e826973db4b5eca5cd6d2cbba96cc34a659a54c6d2a8b69535b4ae2238f0e9c7764e3c2871dd538eca9c7558e3c1271d8938ea49c78b4e3c5871ded38ed69c75b4e3ad871eac38f771c598692cb349655a4ca8d2663693c446fe1d37f0a1bf558dfc126fd4937b30d2197690cab48951a470e9bb764ddbaa6ed95376ab1bb824ddb926ed89376a49bb5b0dccc347a1da3b2ad1e5468ecc34665da332ad1a5468dc446de1d36f0a1b7754dbaac6de0936ea49b7764d7baa6bd9535eab1af524d6cc34565da2b2ad165468b31b45e1d356ec9ab654d5aac6ae09356c49ab524d5ad86a4c9a24f6d125b68915b44661a1d0ed0d96686cab43951a1cc6d0e8a287c4469e1934eca9a7824d3b1269e2c34b30d0997684cab42951a170e9a3754d1aac68e09346e49a3524d1ad868661a0b2ed0596682cab41951a0cc6d07764cfc1267dc933ec499e6368099340a05a0514d026a68145b409ada0456d019867ecbb3f6599fb2acfe5467f31b3fa289fcb44fe6367d2933ea2d9f4d6cfa5b67d31b3de223370e99b864cdbb266e14336ea99b654cdaac66e09336e499b624cda9266d6c32f56197888c6cc33b6ac9d9774ed97674cc339a1d9cd16ce7888bfc3a5fdd92fc76cde2b66ecc336a1d9b32ccd99866b433359d99ab2acd67b66a5dd356619a32ccd3888bbc3a5de192eeec977654bbbb25ce152e70)) else (if i<9 then 0xb4650bbb28cc393655c9ca8e4e8272745393969c9d16e4e5b726cc392659c932ae4a5472541392a29c94d4e4a5a7250d392e226b70eb5b765adc28d6d566b704b5b625ada92d6e046b6a235b119adc58d6d6c6b63635b6b5a9adad4ced6a656b531b5a9ddcd4e196870eb3f7659faaccfded67ed6b3f5b59f95acfc6d67f1133b8b59dc58cedad676b6b3b2b59d8daceeee6770eb375599bad8cdcac66f0eb3376599aaccce0d666e6b3363599bdaccdad666b6b335b1999daccc6d6677733387595aaccae0d656e6b2b82595c32c9e0d64ec6b2788991c3ac8dd96470a32355991c12c8d8964716b238b191bdac8dad646b6b235b1918dac8eee6471131f8658fc28c7d5663f06b1f6358fd58c42eec8f0eb0776583bb2bf65dc732ae3a8771acab8da2dc697763597718cab8ce1d5eeecaf75597bc1abddcd5eec6af597716c3b8b655c5b06e2d927165dd8bdd95e6ab2f373579b1abcded5e6d6af35b579ad8bcced5e7562f3bb97945b8a65dc4b2ae2592712c138964dc4324e2182710c9b87a2dc3c76e1d9870ccbb86655c34e6e199270d41386609c3336e1a8b70d3db866adc31776199870acab8564dc2f0eaeb55975c1abadcd5d704aeb52575992bad495c664ae195708c9b8465dc1b2ae0d93707aacb7dcd5bee4adf5256f992b765dc132ae0992702c13818edc0c56e0597700cab80968c032edfd956fec9b7f968bfb2adf9936fd2db7e8edbf32edf5956fac9b7de1d5b6ab2db8356db9ab6e095b6e4adb5256d992b6e2257f112b76555acc379a1dbcaecde5956f2cdb796adbc9775e5986f143b78655bc506de28b6f0d59782eebc7112af86557b2aabe0d55ec6aad986ef43b775d9bbb2addd836eebdb776adbbb565dcbbaeecc376a1dbb32add9656ecc9b7658dbb504dda8b6eccc375659bab26dd6826eacc374a1dba32cdd1766e8cab74a09ba516dd26b6e8d5b742eeba7112a783553c12a9d4954e64aa5986e743b73655b9b26dcd986e4c9b72d9553f06a9f6354fc12a7d8953e64a9e3b6e2cc37064db8330db9966dd4516e661b6b26db78894dc32a6d9553706a9b6354dc12a6cc953356dacbbad743b6aa2db51775a97b2d05dd688edb3eeaa8b55945b9aa2dc9516a4a8b83543bb29e65db24f6d91ab2c85dd64dd94e6e6a7363538c9b63649b1b36d8dab6c6d59632eeb1b26d8a3b6c4cc3619d9b0b26d85636c2c9361a09b0977585986c0cb3609cdb0324d82826c0cdb60a2db04d6d81ab6c05dd60661afb2cd7d936bfc449ae1d4d706a6b73535c129acc94d330d79976bccab5e64daf70ea6776533c1a99dcd4cec6a6782533b1299cc94cd0ed7788931c1a98d8d4c704a636253199298e1d4b6eca5b6352dc1296cc94b70ea578352bb9a95e1d4a6eca5363529c1294cc94a32cd6d966b4c9b5aa2dacc76d6776527b else (if i<10 then 0xa14c27e009e0c272609bd426cf09a4c264c0986c25d40955824f909270246b0903823c708e84237b08d28232408bcc22cd08a702260088bc21fe087342170084a420cc082402049080081f6307c181eca079b41e1b077501d98074c01cde0725c1c500707c1c0406f781b9706d981b4006c3c1ad306a041a2f0674819540643418f206330189b061a81844060a4180305f4817a105dc0173f05c0c16c705a58162e057f415e2056f0159605594153f0546414f30536014b205204145b050a8140f04fa413b804e48136104cc012ff04b0c12920487c11cd045ec1155044bc11090438c1091040d0100e03f480f8003c8c0ee703a540e43038a00de1036100d27033800c83030c40c0002f100b9302d880b4702c840af002afc0a83028c409be02660097202504091b02274087702144082001f38075b01cd406d80199405fd0170405590141c04aa0113403f000d9c02e900b0c027c009580230007fc01ce006a0018d0059c01410046c00ea003100093001b400310000355a3bc4515e088ae454559878f559c7661e3516f1a1b78d559c565de232ef0998783433c1a0de0d14f068b78315bc186de0b2ef025a380cc3bfa19dfd06efe8a77f2d3bfa2ddfcb6efe1b77ecbbbe968df32eef65a37b151bd9eddecb6ef62b77baad0dd4886e454377b61badb0dcad86f1142355a0fc5b07ded83eb6c1f88a09c450165dddcf6eeeab376d59bb2eeddc76eea2b77555bba661dcb2eee6ab372cbbb858ddc4f4ee27b7705ddb8659dbcd4ede6b76e5ddb765ddb4f4eda6a76d2d3b68e9db2d66d8bbb6ccc3b565ddacf4ed65a76b1d3b59eddacb6ed63b76acb3b49a9da474ed21a7690d1b49adda476ed21b769bb2f9d8d7cea23e7119f3b5af9ced7ce36be71b1f31dbb1d6c7a7563d1ab35ecc3ae661d69776b7875ddaaceed6c776ab3b1637585ddacd5675ee6baf7b5d7adaebd6c75e76baf1b5d7ddceb65dd5eab3a35b1d0cc3a858dd4504ea28a75145ba88edd432ee9e5a34fc3ae6d56736e6b9b825cdc44e3661d1b5668cbbb47c3ae1661d150ee8a2b7430dba1aadd0b30e8196741c44dee226ef0a377559bacc39f659cf97767f875b9bb2dcd566e6f6b736b5b9adadcd6c6e636b731b1b9ddcdc661cf504e78bbb3ccbb9d9cdcecf6e765b73b15b9daadceb30e728273945b9c8adce556e7198736cbb9b9cdcdd04e6f765b3aacd9661cd32ee699673539b9a2eecd6ecb63625b1a88d8c466c6d6b631b5b18d8d8eee6c32ae66547332db9986dccb30e619673141398a29cc516e619872ecbb979cdcbd04e5e8a72f3d3979edcb97765f875afaacd7e096beb635d9872ccb3969cdcb504e5a8a72d3d3969a9cb2f6658bbb2ccc395659cad04e568a72b35395a2dcacd6e561b72acc39465dca32ce527372941394a29ca5146527a72935394969ca4 else 0xa7e429d6ca6d22997ca5e12958ca4cf29144a3c828e5ca34528c50a2ee28910a21328680a16f28448a0cb28268a03d27f809fa427dcc9f0027ab89e3b2774c9dce275989cdd271249c2326f449bab26d0c9b1d26b2c9aa52692099eb267149968264b098a32609497ff25ee0979225c2496e325a1895fd2575c95852557c950d252c0947424f80936d24c1492d424ab892512488091ad245f0911f2422c905a240208fd723de88f3e23b848eb0239208deb236648d52233d48c98230948c2022ee08b7c22ba08a6a227b089c6225d0894e223f088d62218c883d21fac878e21da0870021a8c867d2188085b82156c84f32122c842e20f18830620b8082782094881f52073c810f203a480761ff047f9b1fd7c7f4f1fca47eed1fb747e961fa187e601f7b47d6f1f36c7c5d1ef7c7ba31edf47b201eb907a921e8a879e31e6c879971e54079351e41078911e15477f81dec477541dc3476e71db0476a61da0076651d928762f1d85075f91d77875601d4e875141d38c74c81d18074191cfcc738b1cc8c72f21caac72851c8f871f71c744717f1c53871331c3dc70c61c2ac707a1c0f870231bf186f741bce06f1d1bc086ebb1ba546e7a1b9246de11b63c6d5e1b4306cdb1b2246c4d1b09c6beb1aebc6b5d1ac586af01aa786a571a84069c91a66069671a4d869051a32468821a118680a19f0c677c19c7c66c219a4466551989065dd196846565194fc6519193cc64b7191ec641e18f04638518d2462ec189e46232187ac61a418548610b1828c6067180545fce17e1c5f3517c685eff17b905e9d178d45db7176185d6b174bc5cd2171505be116e105b2716afc5a571684059df166b85972164d858ef16274584b1606857e915e30574515bcc56c215a7056811594056351583c55f41576455be1568c55721555c553c1542c54e5152fc54a4152245463150f4541714ff053e114f1853a014de8535414c6052f214aac52851492451ec1471851a0145e851541440850dc142285064140a04fe113e684f5313bac4eba13a244e581389c4dd5136904d7e134dc4ce51324c4c4112fe84ba812d584b0412bd04ad912af84aae12a784a78129744a42128c84a22127f049e11274449ab12614493312384488412178481711f14477311c8446b9119704615117bc45be11634455c114ac44ef112cc44771106843b210d5442f810a6c423310784419a104f440e0102e8407e101083ff00fed03f830fd1c3eea0fa343e0f0f6f43d4a0f40c3c9b0f0a03baa0ecb03a820e83c397b0e34438740e05c37ba0dd48370b0db3c367d0d8d835e40d5f035140d30834700d020337f0cc8832c50ca2432370c7c031930c50430fa0c2f830820c1182fff0bdac2ed70b9382de60b6502d420b4182cb40b1b42c050aecc2b4b0acc02ad30aab42a870a8a829c20a59428f20)))) else (if i<16 then (if i<13 then (if i<12 then 0x44a7912784494912004479511bf446911147444b1111c4438110c5442d5109a442291064440f9101843eed0f5343bad0e83438150d92434510cc24329d0c4a430bd0c1f4303d0bff42f390bbe42e610b7d42d890b4742cb10acf42aa50a57428c509df426e5097d425890947424b10906423ad0899420c507d441e61072541af50660417e10590414a104ec411e5041c4100503c540ea9037940d79030140b9902aa4096101fb406fd0183405cd016340521012d4031500aa40269007f401bd003e400b900134000cfff33ff34ffb23fe30ff5b3fca8fef93fb20fe973f96cfde83f734fd913f5d8fd5b3f450fcf93f320fc973f1f0fc403f03cfbf43ee88fb503ed00faf93eb78fac33eaa0fa6c3e944f9e93e5d8f9193e2f0f86a3e0b8f7f23deacf76f3dc74f6cb3d9e4f6483d830f5f13d67cf5633d418f4eb3d36cf4c03d2c0f4953d214f4753d168f43f3d0bcf41f3d03cf3ff3cfbcf3b33ce08f3723ccacf3103ca74f2563c7b8f19c3c554f0e23c214f0333bfb0ef793bc9ceebf3b95cede43b5c4ed093b22cec023af44eb693ace0eb123aa7cea6e3a89ce9e03a664e9523a484e8cf3a1c8e84139f90e79239c50e70439b78e69739a48e64039734e54f39420e469390e0e3f138e24e35838bece2ca38a0ce226387d4e1c438678e1363830ce0923807cdfe337e18df2937b04de6f37924dde1376ecdd9537564dd123732cdca537120dbd536d88db0536a74da56368c0d9e93670cd971364d4d8e3362f4d86b36038d7a635e00d72335c78d6b635938d633357b0d584355fcd54e353f0d4aa351e4d41c34efcd39934cc4d30b34a8cd27d34828d1e4345c4d14b343e4d0de342b4d09d341dcd03034080cfd933d98cee833950cdd6335b8ccda332d0cc6d3311ccc2132f68cbb432e90cb7e32d60cb4832c88cb1232bb0cac632a80ca38327c4c989324dcc8cf321c8c81531ee0c75031ba0c675318e4c6133175cc5b131684c591315d8c56631500c4ee3134cc4b831274c482311c8c44c31098c3a830d58c30f30af4c26b30890c1fe3078cc1bd30688c187305b0c146304acc11b303a8c0b930220c03630014bf922fc50beb72f9c0be552f7e0bddd2f658bd5a2f3c8bcd72f2f0bc542f0e4bc292eed8bb642ecf8bb2e2ec4cbb032eb74bacd2eaf4baa22e9c4ba402e83cb9de2e6b4b93a2e348b8802e0b8b8132df30b7852dd50b7392db70b6c12da6cb63e2d88cb6082d7e0b57a2d41cb4c02d294b48a2d1bcb4542d034b3f22ce54b3382cbf0b2892c82cb1c42c6a4b16d2c548b12c2c444b0d52c2e8b0892c0dcaffb2bed0af622bd1caf002bb3caeca2bae8ae942ba10ae5e2b938ae282b860ae082b788adc72b684ad912b604ad712b584ad512b504acd92b2f8ac612afe4abde2ad28aaf82aa6caa332a7b0a9842a4c8a8e02a188 else 0x5754f5d3f574d75d2f174a15d1ed74605d115741f5d01173de5cf0d73925cd2d731a5cba572b85c941722a5c86971ff5c76571be5c661717d5c55d713c5c37d708d5c0956f9c5bdad6f195bbcd6e805b93d6dbb5b6296d385b3f16ccb5b2116c535b0316ba45ae516b8f5ac716ab45aa396a7e5a8b16a1c5a7d969995a5cd69215a3ed68ca5a29168685a02d679859d4566f459b0d66a859a3566515982965ef5977d65cf596d165625941564a859209645c58f7963b858e49636158ced62f458b39625b588d5620f586f561765856d614b5849560bd581d9605b581016025580295fef57e1d5efe57a855e44578215da0575395cfc573595ca5572295c7a571a95c4f570fd5c1956ff95bee56f215b9756d995b3556c115ac8569815a2f5685159c25669d598c5654158c7562b15865560a557ed55f49578055d11573f55cbd56e855a855686558fd55f8556c555965553d5513553e154c755285548655129543a55051540454f7953ce54ea1539854dc9535754cc5531654c1952f654b9952d654a1152325485d51995449950be541b1502553ef54f5553b894e6f539254e0d5379d4dc1535bd4d49534614cf2532814c64531254c2e52f714bc152de94b3352c354abb52a294a0c526bd49475235148775203d480a51e89475b51d59470451b4d4681518bd45e851685457b5142144e2512c5448b5113d443f510bd440950e59434450c4d42f850b7542755096941f25073141a6505a9414f5042140b65026d40494ff2d3f844fd4d3f384fb6d3e9f4fa113e534f8e13e1d4f7593d794f4713cd54f2bd3c5d4f0dd3c1c4efd93bdb4eed53b9a4edfd3b644ecf93b184ebc93acc4e9bd3a494e80939dc4e6d9396f4e44938e14e2c138744e10d38074df01376e4dc4536e04db15369f4da11365e4d90d36284d7dd35a54d579350c4d36d34894d13533fb4ce7933784ccc5330b4cb9532bf4ca3932684c80131a34c49530ff4c365309d4c12d2fee4bef52fa24bdc52f564bced2eff4bb912e874b92d2e1a4b7a52d974b5152d144b3092c914b1292c0e4aec52b6a4ac092ac64aa812a854a8cd2a0d4a79d29c14a53928fc4a27d284d49f95276749c8126fa49acd268249971260a496e1255b4945124ee4932124a2491f124354901123b248d81230e48a99225f488e521e748705219b485a921444847920f84834920ac48245206b48141201f480111fe947f0d1f9d47ddd1f4647cad1f1047b511ea3479c91e41478411dbe476091d51474551ce4472f91c77471451c2b46f391b9246db11b0446ac91a6b468bd1a14467e519d3466e11966464d5191a46379188c460e917fe45f6117bd45e31177145d2d172545bfd16d945acd1698459c9164c4589916004568d15514542914d9451f1141f44edd139144e05135b44d2d132544c2912ef44b7d12c4) else (if i<14 then 0x178c2de2a3789f5e22b78739e1a878609e167784d9e10578351e06177f8ddfc877e31df4577ca9ded877af5dea277941ddfe777b9ddd37770ddda877661dd8877481dcce771c5dbe876e85db1876b19daab76a6dda7576995da4a768e9da2a76811d9de7670dd9b376635d97d765b5d95d76535d906762d1d89976225d81675ee5d79375c81d6fa75b51d68275761d5d375605d57c75451d49675111d41e74f89d3bc74e59d30274ac1d28a74991d1db745cdd11674445d09e740add02673fa9cf8d73c3dcee973a5dce7173825cde3736f5cda273439ccfe73361cc3972f45cb4872afdca57728c5ca0b72795c9ca724adc8fa72351c8ae72171c80a71f91c78771bcdc6ac719edc64a71865c5f371761c5bd7165dc5717152dc525713fdc4d97116dc43570f35c3a770e05c30e70a41c25f708b9c1fd70705c16f704a1c0aa701b9c048700b5c0126ffb1bfb06fe29bf226fbf1bed66fac1be536f8b5bdba6f415bcdf6f2e5bc516efd1bb976edc5bb4b6ec11bade6eab5ba876e8d5b9cd6e595b93f6e439b8e86e1d5b82e6dec1b75e6dce1b7126dbb1b6c66d94db5f66d5e1b5316d2a1b4776d119b4156cf65b3b36ce61b37d6cd31b3266cc2db2f06cafdb28e6c9cdb2586c8c9b20c6c799b1b56c63db1696c4e1b11d6c409b0dc6c2d9b0906c1d5b0446bf9daf956bd0daee66ba7dae4d6b7edad9e6b4adacfa6b249ac356af35ab5a6aca5ab0e6aba1aad86aaf5aa8c6a96daa356a761a9a76a555a9246a425a8d86a2f5a8ad6a275a8776a119a82069eb5a74569c25a6c269a19a629697e1a5d269685a57b69581a52f69425a4d86929da48169141a41f68fe5a39c68cd1a2b6689bda254688e5a1b068655a17a684f9a0cb682eda0ab681bda03367f599f5867c719ee0679e19e3c677a99da3674c19cc8671ad9c3a6707d9bac66ded9b6066cbd9b1466c119ad366ae19a87669859a51668ad99ef666f9998d6657199366641598d4662e59888661b5983c6608597f065f29979965df9976365cc9971765bf196e165b19967465965962865785956365395949e650ad93c364df1930964ab19244647199169644059083641a18fdf63f118f3b63c818ece63a498e77638c18dde635ad8d19632f18c54630098bfd62e558b5962b6d8a896288589a36254588de62365887c620d5883061f4d878c61d6d870961a2d86656174585ab615e984d0612a9841660fc1839e60e39836860cb1830660aa582366081581b360585813b6034d80ad6019980405ff8d7fc85ff0d7fb35fdb17f515fc817efa5fba97ecf5faa57e4c5f7657db35f5857cf95f2f57c975f1f17c615f0ed7c205f0157bdf5eddd7b1a5ebd17ace5e9f17a2a5e81179e95e73979a85e63579725e53179315e42d78ae5e17178365e04177ea5de3577305db7976815d8e975e85d68 else (if i<15 then 0x7e43f990ef6439790df2434b90c6a42e990ae2427190902421a907a641b89067641829057241419049a40f59036a40ca902ea409f90212405e9010e401d8ffde3fc68fe2a3f4e8fc763eec8fa963e698f8e23e078f75a3d9a8f5d23d598f4fa3d238f44e3cf88f3763cb78f2463c6b8f0ea3c098ef623ba78ee063b668ed2e3b1a8ebfe3ad98eaa23a828e9463a158e79239a88e5de393b8e3d238c38e24a38618e0c237f48dee237878dd2e371a8dba636ad8d9f236358d7ba35b28d5da353a8d3fa34b78d1ee343f8cf8a33a68cdd633398cc4e32d78ca9a32758c88e31bb8c5d231388c41e30cb8c26a30748c0e230078bf2e2f798bc9e2ed58baea2e9f8ba122e698b93a2e338b80a2dbb8b5a62ceb8b2662c688b0de2c118af822baf8ae262b638acca2b0c8ab9a2ac08aa3e2a488a80629ba8a57629428a49e28e08a1e2285d8a136283d8a05e27c589d7626ea89a362604897a625d98972625b98964e25788957625428949e250c892ea2452890b2240688e4e238e88e26235888bee22ca88abe227e88936221c886222120882b6202487ec61f8b87dc21f5587cbe1f0987a2e1e39877721dab875ea1d54874ba1d08873b61cc7872861c7b871561bed86f1e1ba186dee1b2986a821a6f869261a238679e19b6866161954864ba18fd8635e18b18622e182385ec2174885c3216e685b02169a8589e15bf8560e15528548614f0852d214838517614378501a13d584eea139f84de6135384cb6131284bde12dc849fe122d8476e11c084696118a8450e10e68425210798417a104383f160f6883c860ea3839720e0a836060d2f833a20ca1831ee0c6b82f8a0bbc82e860b7082cfe0ad782ac60aa1829ee0a6b829420a09826de0965823ca08ab8221608758216a084a820ea082a8203e07e981f6607c981e8e078881de2075281cde06f0819ca06158170e056681376045f80f86036e80da6032d80b6e029f808de01cf806a601838044200ea8031200517ff21ff6b7fd6dff407fc95ff0a7fb0dfe667f959fe467f8adfdd97f675fd4b7f309fc9c7f129fc247f025fbb77ee71fb297eb89fabc7ea85fa917e9d9fa507e7cdf9c27e69df9557e4e9f91f7e335f8bd7e289f87c7e185f83b7e081f8057dfa9f7b97de21f6f47db0df6507d71df53e7d3b1f4a57d229f4597d0f9f4027cf9df37f7cdbdf3497ccb9f31e7cc0df2e87cb09f2a77ca05f2667c92df2307c855f1fa7c751f1b97c679f1367c441f0ea7c311f0517c0adf0057bd99ef097bb8deebd7ba5dee717b8a9edd87b74ded767b515ecc77b285ec447b079ec0e7afa1ebcd7ae9deb297ac65eaf37aa01ea0d7a6ede95e7a381e8c57a1a1e8587a0c9e80179ebde79479e11e75e79ce1e71d79c35e6e779b5de68579875e5b579509e4da791c9e3f478e5de37c78db1e35c78d05e33 else 0x84a897aa22da881ea1c0a858ea11ca83daa0baa81cea02ca7fc29fa9a7db69f10a7b529e98a79729e36a77ea9dd4a76ba9d88a758a9d26a74029ce5a72a69c83a711e9c21a6fc29bcaa6e0e9b52a6c869af0a6b2a9aa4a69a29a37a67ee99caa663a995da64de98fba63569899a614a9821a5f9697caa5db69726a5baa96b9a59f6962ba57929592a5586953ba53a694ada51c69440a506a93d3a4e5e9387a4cd692eea4a9e9260a486691dda46869170a44fe9119a43a290d8a42469060a40be8ff3a3ede8f70a3cfe8f03a3b768e96a39c28e60a38668ddda365a8d5aa347a8ceda331e8ca1a31968c34a2fe28bbca2e2e8b5aa2cd28aeda2af28aaca29968a34a280e89b1a262e8944a23ca88b6a21928828a1f8687a5a1da6872da1bc686b5a1a128648a183285d0a1652856ea157a8522a136e849fa11ba8432a0fda83c5a0e528358a0c4682d5a0a3a8247a080281daa067a814ca04c68100a02e68088a013280059fefa7f989fdca7f579fcf27f169fb967eb49fa0e7e529f8867df09f67a7d6d9f4f27d219f3c27cb49f1e27c479f05a7be59eed27b999ed767b219eb967aa99e9e27a479e8b279f09e6d279789e4f279009e33e789e9e13278269e00277cf9de7a77629dc1676c99da0a76519d82a75c39d61e75409d41274bd9d1da743a9d05273ee9cf4e73979cd4273099cb6272b29c9ae723a9c7fa71c29c64671609c4be70fe9c30a709c9c12a700e9bef26f8b9bd966f299bbb66ea69b9aa6e4f9b8a66e039b7766dac9b5c26d349b3b66ca69b17e6c189af466b8a9ad3a6b079ab2e6a9a9a97a6a179a71669899a50a68f09a2a668839a0f267ea99eba675c99cae66d999aa266779991a660a997be65c99968e655c9945664ef992ce648d9919e64419904263f598f12639e98e0e635d98cb262f098aa662839897662379887261eb986ea6194985ba61489845e60f19832e60a5981d260389801e5fd697ec25f8a97d665f2897bde5ebb97a2a5e4e978a25df79771a5db69769a5d75975125d08973b65cb1971525c0d96f725ba096d925b2896bb25aa59697a5a22967c659b5965ba59329643258db96302588f9617a582d9601e57d695f1a578a95d3a571d95b8656b0959d256439587655ec9577255b6955ea55499546254e7952da548595152541894f7253ab94dea533e94c3652f294ada527a948ce51ec946965169944b650e6942aa50639409e4ff693f164f9f93dba4f3d93c324ef193b5a4eb093a2a4e7a939264e189379e4db6935ea4d3e9340a4cd1932824c6f930fa4c0d92f464b8a92d3a4b1d92bb24ab0929d24a4e9284a49d69263e4953924b648fc9232e488f9217a482d91fc647aa91e12475391c3246d091aaa468491922462d9181e45d6916ee45ab91642456a9156a453f9146644e8912de449c91182443a910))) else (if i<19 then (if i<17 then 0x87701e1c066b013dc03af0099c00f2ffeabfee6ff72bfcaefecebfa1efe35bf7bafdb2bf5dafd45bf426fccdbf246fc60bf0befbfebef62fba7bedaefb2fbec52facdbea72fa76be916fa09be762f99cbe582f92fbe3faf8c2be246f855be066f7ddbde86f765bdcd2f6f8bdb1ef696bd996f629bd7e2f5b1bd5aaf52ebd372f4b6bd26ef45fbd0baf3e7bceaef364bcca2f2e1bca96f269bc8b6f1f1bc6d6f16ebc49ef0f6bc2eaf068bc086eff0bbe7aef62bbcf2ef00bbb12ee88bb932ee1bbb77eedaebb5f6ed4cbb46eecdfbb28eec5cbb0aeec05baf52ebaebadcaeb57bac6eeaf5baae6ea88ba95eea1bba752e998ba546e915ba392e892ba12ee7f9b9e9ee776b9ceae6feb9b0ae686b992ae603b974ae5a1b95eee555b94bee4f3b92dee491b91aee42fb8ffae3c2b8e1ae34ab8c66e2e8b8adee27bb892ae20eb874ae1acb85eee134b843ae0ddb82b2e07bb80fee00eb7f4adfa1b7dc2df29b7be2debcb7a2ede4fb784eddc1b75eadd33b740adcdcb72aedc7ab70fadc0db6f46dba0b6d3adb28b6bdedad1b6a82da64b681ed9e1b66eed98ab6566d91db63b2d8bbb61d2d82db5f9ad79fb5d8ed71cb5b56d699b594ad5f5b568ed551b542ad4ceb52a2d482b5172d420b5016d3eab4ebad388b4d8ad33cb4c2ed2dab4ad2d283b491ed20bb476ad1a9b45b6d131b43aad0b9b4222d057b409ad000b3f6acf9eb3d8acf3cb3c2ecedab3a4ece62b38c6ce00b37c2cde0b3716cdb5b366acd74b350ecd12b33b2ccbbb31fecc4eb3076cbe1b2eeecba0b2e16cb6ab2ce6cafdb2b06ca85b29aaca4fb28d2ca19b27fac9d8b26cac981b2516c909b238ec8b2b2206c850b207ec7eeb1ef6c797b1d9ac756b1cc2c715b1b92c6beb1a62c667b18dac610b17d6c5c4b15f6c54cb146ec4c9b1236c43bb0ffec3e4b0ea2c38db0d72c32bb0c16c2c9b0a0ac230b0856c1efb0752c1aeb05f6c141b046ec0dfb02e6c072b00dac010affaabfb9afe4ebf62afcc6bf00afb12be88af9b6be52af8debe1caf7dabddbaf6aabd84af57abd22af39abcb5af212bc53af032bbbaaee26bb4daec1abad5aea3aba52ae886b9fbae756b9a4ae626b96eae522b922ae3f2b8cbae296b874ae13ab81dadf02b784add22b701adb42b69fad962b611ad72ab583ad4c6b50bad2e6b45cad056b3eface4ab361acc96b2deaca06b250ac87eb204ac77ab1a2ac5c6b140ac43eb0deac28ab066ac07eafe3abe9eaf55abc66aec7aba5aae65ab8d2ae19ab7a2adb7ab5eead34ab3e2acc7ab286ac65ab0a6abd7aae42ab5faacbaaae7aaa82aa64aa926aa0daa7caa9d7aa69aa95faa4baa8f2aa256a82da9f6ea7aaa9dbaa753a9c8aa6f1a9ad6a68fa994ea5f6a96bea573a94b2a4fba932aa4a4a91faa458a90caa40ca8f42a39fa8d8ea33da8c32a2e6a8b02a2 else (if i<18 then 0x3461981a42bf53390107a002ec400730d1865841446868610411a200398690d1911a204343c418690d0f1061a83486898830d41a4344c418690d0d11a1a1223c34868688d1021a1e20c34868708f0d41a43448478690d0c11822c34868908e1121a1b5368008d0d01a2b5368008d0d135c7bd70ff5c03d6f4b5b96d6d975b29d6b8b5aa6d69d75a4fd684f59e2d66f3598bd656b591ed6333589bd61d75844d604f57edd5ef3578bd5d3f5713d5b3356a6d5a03564fd587b55d7d569b555fd548f54e7d52835464d50a353ecd4eef538ad4d3b5312d4bb352c6d4a575259d487751f7d46ef517fd44e35107d4303508fd417b5022d3fc74fcbd3e974f7fd3d0f4f12d3b034e9ad397b4e2dd376f4daad358f4d3dd33db4cbad327f4c4dd309f4bf6d2f174b89d2d374afbd2aff4a78d28f349f5d2713497dd250748efd224b4856d203f47d3d1eb74771d1d03470fd1ba746c3d1a1f464bd18c345f4d168b455bd147f44e3d12f74497d111743fed0edf4386d0d57432fd0bfb42cdd0a9f428cd0917421fd076341b2d05db413ad045340e3d029f406bd0143401fcff8f3f9ccfd573f24cfb773e8bcf93f3e1ecf78b3d9bcf5ab3d23cf39f3cb6cf1eb3c3ecefdf3bb0ced7b3b17ceb9b3aaace9bb3a27ce80739dbce6d7398fce54f3922ce39b38b5ce1e73848cdfaf37a4cdd773721cdbc336bfcda3b365dcd8b33606cd72b35a4cd5cf3537cd3c334bfcd23b345dcd0df3411ccf8333afccdcf332cccb9732a9cc9e3323ccc82f31cfcc67b3157cc49b310bcc33f309ecc1e33047cc05b2fcfcbe7b2f78cbd1f2f00cbb132e88cb9332e1bcb7532d82cb51b2ce9cb2e32c87cb12f2bf9cae9f2b60cac672ad2caadf2a70ca8ff2a03ca77729acca5ef293fca3e328c7ca2872870ca12b280ec9f7727a1c9dc32734c9c3b26c7c9a5b2644c982325ccc969b2575c94e724f2c92db2485c91532418c8f9f23c1c8deb2333c8bb322a5c89a7222dc87c721aac85bb2132c83832099c811f2016c7f971fa9c7db71f31c7bd71ecfc7aa71e83c794b1e21c776b1da9c75b71d3cc74031cc4c727b1c6dc70f31c0bc6f131b93c6d8b1b3cc6c2f1adac6aa71a6dc68c719f5c66e7197dc648318efc62cf1877c61471820c5fbf17c9c5e371751c5caf16fac5acf1677c58ef15ffc573b1571c5503150fc534f148cc51431414c4f6313a7c4daf1345c4c5312e3c4acb128cc4943121fc47e711bdc4633115bc445310e3c429f1076c419b101fc3f0b0f7bc3cff0f0ec3b770e96c393f0dfdc36db0d85c35530cecc32970c5ec30b70bf1c2ed70b6ec2c470abfc29b70a1bc27530998c259f0941c249b08f5c233f089ec21e30852c208707f0c1ea7076dc1cc706dfc1a630651c17a705a2c159b051fc1363049cc11570424c0fa30380c0ce702fdc0adb0264c0 else 0x6d4e20e1a43444b31050d0e20a23c34868896620a1a1c418478690d1029c418478690d1620c23c34868910611e1a43441ee3d020f1a22f48bd16620c408474688d202f0596a708e8d11a30775e817a2c8418474688d222f4408474688d142cc5388108e8d11a305e8b210611d1a23460f93d03785e6abd4c2684408350191b2003ec69cbd3a9b402802e79001fe3488bd16611d1a23450e817a2c84168108e8d11a44740bd16420c23a34468f1dda9c418474688d1a3bc418474688d142cf53e800e4169230460780d243a05e082d0211d1a23478e914e20423a34468d1d02f0418474688d183b9f4446868817911893be1a43438ee17a20c23834068c7d020c4044648838690d0e20e1a83486887d0eae41c47868a7d02b9d54820cb11e1a39f40d075720832447868e7d0eae53c820c817623c3483e875729a41c800c81762303f8680d2cfa0573aa90419223322340424ef8690d0ceae1a83486889dd20a2340444838690d0ceaa411423c34868708f0d41a434448308f0d21a2423c350690d103bc238340688178e4423834068a10520423834068b08e0d01a80441ee378e42411720cb1181fc3490bc72111a1a205e44624ef8690d0f0d41a43434ee17920a232241c34868786a0d21a1a23c348686105118a20e1a434388386a0d21a2441c34868710511e1a434408288c51070d21a18418478690d1211e1a434308308f0d21a24418478690d1220c23834868910611e1a834868b10611e1a43440e419c2cf53e800f81c823a340554566a983e07208e8d0153859ea60f81c823a34054f08e8d11a1c23a34468708e8d11a1c23a344686fd2a994007a2e411d1a3d53790106a003d04607e8d2211d1a23438bd16611d1a23458e81782cb538474688d1c3a05e8b2105a0423a3446911d22f423a34468b1d02cc5388108e8d11a3c740bd16420c23a34468e905118a2cc5388108e8d11a34680b2d4d644408474688d22344598a6105a0423a3446911a229c408474688d1a340598a6b2220c23a3446911a22cc5308308e8d11a3e20c350690d10e44238410680d1611c20834068872111a20434444688058830d21a1e20c350690d131061a83486881a434057083868a1a4340570820b91182338693abd4c20f400640b811e1a034a8470680d0e11c1a034308308e0d01a24238340686fd034857ea611020f4005c08c100115c23c34868708f0d21a18418478690d102b8440820b81282343470d215fa9844e800b81181f02c045508f0d21a1bf40d3d4fa042304607f0d202bb5309a105a002e04808c0fa1a50720d3d4fa002e84607f0d01a4c238418690d0112869ea7723a02230468800fe1a486939010417623c40070e1a4e404105d88f1001cc3480d215ce404105d88f1018640690ae7202082ec41868c32034857ea672020f4005c08c0e61a0)) else (if i<20 then 0x20bb11e2046740d2164e404105d8830d233a0690b27202082e44788101dd3a45ecab1071061a83486931dd2cb538838830d21a3a740bd95420e2043468ee96729c41c4186a0d21a44774b394e20e20c350690d212c841444308308e1161a434508308e1161a4345de8566a983f07c08e8d1e3b85e8474688d153ba2363486889dc2f223634868b1de3a0596a710611d1a23488ef1d02cc5388308e8d11a407c3e81bc32059ea61041181f03d86967d12ca5348288f0d21a3a774e917a2cd539918830d41a434a3e995620e20c34868d1d12cb53591106a0620c3486921dcfa0d93abd032002ec478830d283b9f41b2164eaf53ca60c817623c40b0ee7d0b40d93abd4f2983205c88f0d2c3b9f41b2757a9e53e819001902ec418680d016026f0ee7d06c9d5ea7d0019623c4007d41dcfa0d90b2757a9e53e819001902e447881a1e83b8d90b275429841e800c81722304607c0f61a7a774e916729e20c350690d233a25e3aad4d64620c3486909d22ce53482d031061a43484ee164eaa534820c911e1a4349be8167a983e046078c9df2ae40846868b9d12f2596a6b2211a1a3a74caa905a04234346ce994f20423c3486b011d3ba748bd16664620c350690d253a459ca732120b40c418690d273a45e0b33231061a4347ce917a2ccc84478690d1cfa0741bc1786c841c478800b243a0590ae14c2904105c88c1181f03d86981dd3a6558838830d41a43488ee965a9ac88838830d21a4274caa1071021a2c774b394e20e20c34868f9d32ac414478690d1a3ba59ca6b2220e20c3486909d12ca5308288f0d21a38770e916611e1a43468ee14e11e1a43458b210611e1a43458ee16611e1a43450ef16420c23c34868c1f5fa1f40de167a9853083d001181f03d869a1e83a072ea614c20f400640b81181f03d869a1d02c8570a611020f4005c08c0f81ec34c5e91662984168108e1051a23490b2b2220c238414688d1e2cc5308308e1051a23478b310611d1a23450e916420b408474688d1e3a45908308e8d11a34778e81782cb5359108e8d11a4c778e914e11d1a235008f1de3a05e0b2b2220c23a34469296520893ba748b354f1061a83486901d220a1a1a5388286867d02c9d5c8390311e20c3483e81642b9d5ca690419623c4093e85a02c9d5c820c911e1a41f40b2757a9e410640bb11e20c34a3e8164eae53483d032003205d88f1001fc34069c7d02c8573ab94d20e4006488f10293ba748b394f1061a83486919d02c9d56a79031061a43488b2905a021a20593aa904795724640846868b9d12cb53c8108d0d1920b4084686899d12ce53c8108d0d187b8771bc164e424106588f1001fc34b4ee9d22ce53c4186a0d21a46740b2d4ce4640c418690d222ca4168086899d02ce53c818830d41a4348ce916729e40446868c164e42411a74882868 else (if i<21 then 0x96a61041701f2b53082d001742304607e0d20348576a6105a002e84608c0fc1a504105c08e1001f43460d2d4da002e03e868cfd03482504808f0d1834b536800b80fe1a43470d2d4c1701fc34868c1a7a9b53e80d001701fc34869215c2202e047868a1a5a9b4005c07f0d21a38697901041282303e60d209412023c34868c1a432553a800b911a203e1a4342c3486858690d08341532800b911a1a30720d354ea003504607f0d21a4869aa6722a002e4468800fa1a03404d6105a0140c404c3486841a42bb532a6720a1a0a98412800b911a1a03480d354c20d4005c88c1181f0398690d2c348642a650017023c4007c0d01350693905001702303f8680d20349530820b811e1a03404d01c83495328008c0fe1a03404d21a4a994005c08c0fe1a43404d21a42b84105c88d101834423c34868815c2082e44640d215e2082e04650d27202082303850d215c2082e046618c1a4a994005c88f0d01a3869aa750017223440068f08f0d41a434484786a0d21a20682a65001902e44686ac32034d53a800d41761a3069aa750017223440068f08f0d41a434468186a0d0f0d41a1223c350690d130d41a161a834868786a0d0b0d41a161a8342c35068488c0e61a8344c35068586a0d0911e1a834868888f0d41a1a23c35068786a0d0b0d41a1353c35068688f0d41a1e1a834868688f0d0911e1a1223c342c350690d0f0d41a4343c350690d0c34d530640b811970d41a43430d354c17023039868d86a0d21a186905d8680d00128690ae0e817423c3486800a30d41a4343c350690d0f0d41a4343c350690d0c34d53a800c817023c347c350690d0c34d53a800b81181cc347c350690d0ca982ec348680094a994005d8680d00130692800bb0d01a00260d254c1701cc34004c1a42b83b05d08c0f61a434005308f0d41a434484786a0d21a2423c350690d1211e1a83486881a6a9d400640b811e1a3c23c350690d130d41a434368050017023c34004c0b811e1a834868c300138692a65001761a034004e1a4a002ec34068c300138692a60bb0d01a00260d254ca0423c34068009c341532800bb0d01a002705c09211e1a434010009e0d0411c1a10238342834183418470690d0da041a10238342834183410470690d0c11c1a141a0823045068708c1141a1a775e9166a9e20c34868e9dd7a459ca78830d21a3e744bc755a9e40c418690d202c9d548234eebd32ae48846868d9d12f2596a790211a1a3e744b394f20423435808e9dd7a459ca78830d21a3e740bc165a99c8c818830d21a4e748bc16720620c350690d233a45e8b390111a1a305939090471dd29c4143448ee96620a1a247788288d0d123ba5988286891de20c23c34868b1de20c23c34868b1de20c23c34868b1d12cb538835031061a43480f67d03a05e0b215c20e20c3494e81a42c9c808 else 0x44406808e41702303ec688d01301918470698d0dba4681bc9652082364007d8d2611c1a63438d037920a3905c08c0980c4423834c686dd0392591b2d4e644406808e41902e04607d8d11a026032308e0d31a18724b2366640400640b81181f634a6e81a52cb558a7101a023905c08c1101f6344680980c8023834c68608c0f81a026030b468308e0d31a1a4104607c0d00c2d1a0a4104607d8d01a0186a3418470698d0cfa0641bc14c1702303fc680d00c50681bc364a984005c08c0ff1a03403163d4340de0a6d00a00b705c08c0ff1a034031a1c86f0530802f09902e04607f8d00c58720d2378298401780b89181fe340316f74e4423047080b08f0d21a186939088d1021a03405809a0348644468800994349532800b811e1a43473e81a4a99c80820b81181fc3490d254ca002ec34068c192e42234404c3486847d034d5305c88d101b0d21a10696a654ce41034d533900b911a204340680b01351f40d25031001329f40d254c17023c4006809a0349c805c08f0d01a30692a650017023c3486809a034d53a800b911a20361a834868688f0d41a1e1a8342c350690d0f0d41a161a8342c35068488f0d0911e1a1223c3423e81bc34864aa7500172234408680d2ea061a4343a818690d0c20b4028188098690d0834d53a800b911a2003e05809a4348640838800f8163540c3486867d3a9844082d0311e2003f86921a4321532800b81181fc34869254e11e1a43440d215c2082e446880d08f0d21a18690d015ca9841c3460d21a02b84105c08cc1a42082318692a650017223c34068e1902ba234404c3486841a43404105d868a105a014005c4c34868415ce422344040d27202081fc345c3486841a43214005c08c0fe1a03480d215ca99400478690d1cfa04408288d10170d21a161a434208810511a2002c04cc1a4208161e1a43423e81a6a014021f40d254c2082e04607f0d01a48690820b81181fc34068f08f0d41a43440ae11017223440058099e11e1a83486881c8378690d00b80fe1a38572a60b80fe1a2869089868615c2202e446868a1101701fc34868a1a4a994005c08f0d21a38570820b911a2002668478690d0c349d53901041702302670d254ca0223c34068c1a1e414005d08c0d18a9bc82800ba11c1a33f408308c1191ee84184608c815e11823834408908c11c1a21532800ba11c1a2bf479108c1181f834609af221182383450d054c2082e84650d054ca002e847068c15c2202e84608e0d18343c82800ba1181f8340690f202094005d08c11c1a03480ae10611c1a20570820ba11c1a28696a6104171034b4005c0900fe1a33f40d21040fe1a28697ba1040fe1a28690af86861a42261a186904607c6fd034bc804607ca1a426bc803f868a1a5a984105c0900fe1a02c80e41a5a9b4004807f0d01640690ae11017023286))))) else (if i<33 then (if i<27 then (if i<24 then (if i<23 then 0x4188008d9031a3c408470698d1211c1a63430e45a0322591b314da9a418808e41902303ec6809be20423834c6881c837a591b214c2003204607d8d2a20023834c68817a29c4005c07d8d01a02681ee905a0040e3404cd10211c1a63448a69041702364007d8d01a40534821001702303ec680d203b8690c808c0f9620423834c688967a9b53e80d001702364007c09a8fa753088d039001fe3478ee1c8320de1b22e41181fe34c6957d0388de6a6105a032003ec69203e81c86f0592a61049181f6349be8dd02c953a80d001702364007d8d11a60f50e41902f0599911011c82e046c800fb1a6c23834c6869dc6f4c84828e41181f3c23834c686dd2340d94828e41902364007d308e0d31a18681b21001902303ec68e08e0d31a1c684820b811b2003ec680d20342410800b81181f634069108e0d31a1a770c83642002e04607c0d206f0d903fc698d16fa1744b354da994005c08d9001f63446983d43905e4b314c20d4005c08c0f8135c23834c6865d06f05e4b2c818d1a11c1a63432e81c82f2591b314ea003204607d8d0136423834c6861c92c8d90a60c81181f63482e81a42f2598a75001702404607d8d0136023834c6871a22982e03ec680d0133c23834c6867d029d4005c08c0f81a38f50d0366a002e04607c0d207a8de03fc698d16fa0720b354da9d4068008d9001f63446809b439168ea654fa014005c48c0f81350720ce16629c4047208c0f8134c538470698d1211c1a63434ef1a229a4147208c0f81344538470698d10390d98a6d4d2082364007d8d01a54538470698d10390d90a61001181f63406901c8348598a6d4d20a3926408c1101f63404db14c11c1a63448d114e2001f634068099e29c23834c6891a229a41046c800fb1a03481b2d4c2981fe3450d014d2084004607d8d01a44538470698d11ba072ea6d4fa0340046c800fa53b8728b214c2002303e06901c83435308008c0f81a38726a7d039001fe3460e41a22c85368008c0f81a40728b23645c82303fc698d21ba0710aed4c220416800b99031a500b40de2a61049912303ec6806246f132246c680616fa0694b354da9d406800b89192003ec688d3434968ea654fa01402640b89181f026b1ea1c8322598a6d4e2034005c48c0aae11c1a63430d31a12cc4068048c0a9e11c1a63434ef1a229a410820b8919e11c1a63430e41a46cc536a7101a0032246055508e0d31a18721b214c2002e246c68f1a229c4005c48c0fb1a03488470698d0c34c688a69041712303ec680d24340530800b89181f634069108e0d31a18694b3d4da9f406800b891a13b8690c814c2002e04607c0d24348681b21001702303e06903d4348680a6d001702303e06921c8348684b214c2002303e06921c86c8b90474800ff1a63486e8965a9b4064007d8d01301891ea1c8338644b2d4e6 else 0x11d20e3470e437820023a41c68c1c929a4006a48d8d11a39740e417b29e4005c48ce1bc6f0350474838d192f023234384786849781191a1c23c34248208c508f0d092f02323438478684c68317a8d41a234408346a0d11a245ea350688d137a0d90b294d2002e24678bd46a0d11a26f4ca79001712304607c0f11a026a9e8167299539901072002e24648009acba0de0b2d4c20a1a23404d03dcfa05e0b2104099a2031a11740bc16420d40880c818d222031a10f71bcd4c5c81fe3462e81782c84102651ee7d06f0592801005c81fe349880c68416420887b9f42801005cb2003fc6809a62031a131a0ef42e83672995308390017123026a0bc3209181f634468099c2f2232343c34148288c586821791191a1e1a0b1a0a23c34288346a0d11a2441a350688d1220d1a83446891068d41a234408346a0d11a24680b394ca9841c805001712303ea3e896429c410800b81181f0349aa714c20b2003e8688d1c2f0599900e59001f63478a6c6841dc6c9530a61078d183b8de8a61041c81f30de1b2d038d1229b1a13740bc366a983964007d8d2229b1a10d92a6c686dd03485e0b33201c81f63488a6c68437b8d098d077a1680b394ca9841c805001712303eb0e41a02c8538821009902303e06941a02f4530820b8919a8d11a151a2342a3446854688d0b7a4530820b89181f351a23422a614d6404188007e8d11a46f48a61062002e24607c8d202092303ec688d14342530829011912303ec690d11a50692d016729953083900a002e24607d61902f2592464800b1a11b1a10690bc964918162c2363420ee104918e11b1a10690bc364918162c2363421b248c11b1a20696800fc1e839047c68e0fc9181f02a04cad001e8b9a4007f8d1834a591901041181fe347846c6841a52ca486800f49198348d919007c8063410bc88c8d0f0d042f2232343c3410bc88c8d0f0d058d042f223234344786840798d21a1e1a091a091a091a091a091a09741bc166a9b4028007e8d01348412342ae83782cb532a75029001f40698b354ea003d2464800f813481e23420e2167a9841e800e41712303e07a8d11a026d7e916629b5305d08c0f9c3d859591101a002e84607d0fd22cc5308308c1181fa3404d31a06f05984608e8d183886a8a71021182303f46809a5fa0590ae0ba1182302678d114c2204284608c099dfa4680b314da9c406800ba1182303eb0d016629b535901062002e04607c09adfa0598a6d4d643400800b81181f23404d8fd2340598a6d4d640418800b81181f026c0d116629b53083101a002e04607d4fd2340590a61062034005d08c1181f5c680b314da9841880d001742304607d65d12cd536a7501a002e046c800fb1a23404db7d02cf532a7d00a002e2464800f81359f40de1912cc536a69062002e03ec680d3220423834c6885a12ca) else (if i<25 then 0x8470698d127a0691b254e6424106488d132211c1a63449e836664040446c68d3d06cd538800b91181f03c80d23646401f20691b23200f9211c1a63439e954e6424105c88c0fb1a03499e854e643400800b91181f634069532211c1a63444ee1a4320d91901001702303e06941a46cf4003fc68a1a46f0d917208c0ff1a6348be854ca013244607d8d11a40696ab54ca002e44607d8d11a48f70ced566402e44607cf08e0d31a1cf40d2379aab5307c0b91181f4c23834c68708e0d31a18721b214d11b1a2cf48a60b91181f03c61ee3d0348c807207cd08e0d31a19f40d214ea002e04607c0d207b8f40d23646454005c08c0f81a50f70e41a46c841a8008c0ff1a634abe854ca003d44607d8d11a40692ab54ea034044607d8d11a4a771e83792084144668470698d0e7a45388088c0f81e3423834c6873d229a4144607d8d01a3a771e81c83481f2cf40a61011181f634068f08e0d31a1869ea6d4fa034044607ce3d0390690a6d001181f03480e41a46c8b905c08c0ff1a6349baa4c9118dba0714bc15c2202e446c6900be854ca003d26488c0fb1a23490d2178acd53a800b911b1a2349047c6857202083d44607d8d18348596a772020b4007a88d8d2400941201fe3441bc5646c82504807f8d1c6f0d91720941201fe3471b20940ff1a2753083d001702504807d8d202083d04888c1181f63446900900fb1a18676ab3212082e04a88d1001f4c23834c6873d0348de6aa9041702544607d308e0d31a18f41bc90420a3905c0951181f02aa8470698d0e7a0691b314da9a410640951181f5423834c6873d06c85308009511b1a3a39a34244607c0f016251a0c23834c6869041222303ec680d1a8d041222304607d8d01a31f40a60b81282404607f8d01a02ca1e8364a984004a09011e2003fc680d2c7a0536805005c82e04a08f1001fe340680b34390530804c8128240478800ff1a02cb0e43645c82e04a0901181f03490e419c32059ca79001c82e24608c0f91a026d4bc88c8d0cfa0721bc08c0ff1a3223e34868717a1191a187b0e437829823e3460bc88c8d0f0d0620c2323430bc88c8d0f0d042f2232343c3418bd08c8d0c2f42323430bd08c8d0f7a653c804c81912304607c8d247a0711bc0c811f1a31f40bc36729e402640b891b1a49f41b215f20132c47c68e7d07a0d9ca64c817623e3586927d06ca534804c81712323483e81a06ce53c804c81771a41f41b394c20932c47c6809a0fa0f40b394c9902ec4607f0d24fa0d9ca64c81902e446c688d24fa0f40b214c2013205c08c0f81a50de08810011f1a2a5e44646861c86f02303fc68a9791191a1e1a0e1a0a414462c341447c690d0c3906f0b314e2002e2467a3446854688d0a8d11a151a234223410bd08c8d0e2f42323430d394f2002e24608c9102203e46809ac3e0721bc32 else (if i<26 then 0x204163420d2365a9cc8082d0011815444163421b33202082363451901041181f6340580a9d3b8f70d23201181fe3405901a42f15999008ca3dc34a41082058a08c2c68288c0a8920d1a10f40d214c2002e04a08c0f81a4a2302a2c3414460545868217920a394464c34146488c58682c6829011cd1a1a23e342447c690d0e20d1a83446891068d41a234488346a0d11a244108208c0f9220d1a83446881051181f634468a7d0390670c8d55a0223440c680aaa11b1a10776aad01118152c236342846c6841dc3935368088c0a9a11b1a107244608d8d107b869681c68888c0f883b8690c98800f963b8f70d207c908d8d087bb556800f511a2003e73e83d1a0623c4007f8d1d8d0420b4044607d8d11a351a2342a3446854688d0a2084104607e8d168d11a12f42a6104a013284608c0fd1a4bf42a61062014026508c1181f834a7e854c2094084608c0f91a43f42a64c81242303f4688d20a99402640921181fa3477e908c1181fa3457bb08c1181fa3457e8f561182303f468cf561182303f468afd0a994004908c0fd1a3bf42a65009902484607ce54ca013204908c0fd1a3bf479108c0f91e442304607e8d141ec2313f42a65001242303f468ef201ec2304607cafd0a994007a4ca1181f23484460545868288c0a8b0d0519223161a0b1a0a2302a20834685868246824682468246821a6aab4028008ca1a42f159082423412e81a6aa83d84607cc0888d083a0698b314da9c406800ba11823507b0b31001181fa3460e8179ee85908308c1181fa3497e81a42c85704607e8d1c3a05e08810a1182334740d31782cb536800ba1182303ea0f61e4348610b208c0fd1a43f40e2179e442304607ce1e42f05907b08c119a3a0690b314da9c406800ba1181f50690bcf202242304607ce1a42f0596a6d001742304607d21d22cc536a6105a002e04607d31d0348590a61062034005c08c0faa3a0690b314da9841880d001181f55f42a65001e93244607d8d11a49740d2d56a9d406800b91181f63446967d0323559909062002e4468800fb1a034c88108e0d31a20691bcd55a9a418800b91181f4c408470698d1211c1a63430e41a46cc536a69062003244607d510211c1a63440e436429840446c68c3dc34a416801038d1a29c4005c88c0f81e30770d21906462003e688108e0d31a24534820b91181f634068e14d2084005c88c0fb1a034888108e0d31a20696abd4fa034005c88c0fa0fa069ea6111a001fe3478ee1c8320d917209011e2003fc698d2f8d06fa22363430f77d03886904888cc03e81c8ac8d904a0938d1efa1536805001e93244607d8d11a50690b354ca9d406800b91181f63446961a46cd53e8007f8d187b8720ce1902cd530a53222034005c88d1001f74c88470698d113b8f40d23646471a32771e817aa9cc8482104172234cc8 else 0x607f0d1c7b9f40a61045c82e84673e814c208b905d08c0fe1a43493e817ae404105c88cd86a0d21a19f41bc1792084105c88cf86a0d21a1e1a834868688f0d41a434444786a0d0d20a23c3434a786a0d0f0d41a4343c350690d0f0d41a1223c35068786a0d08e4223c35068986a0d0b0d41a1241c35068786a0d21a1e1a834868688f0d41a4344447868488f0d087b8414468680d162061a83486891030d41a434488186a0d21a2440c350690d103bc530831001722303e78821040fe1a02c588186a0d21a20f704607f0d21a285e0ae10511930d41a43433e87222084105d868d86a0d21a1e1a83486877d02f041c811001722303e88821041701fc345c350690d0cfa4530a61052001fc350690d262084005c08c0fe1a03471bc15c1181fc34868c15c2082e05a88cb8690d0b0d21a1041c3486878690d0a298418800b816a2303e709b10420e1a261a43423e81040fe1a83450ae14c20c4003f86a0d1cfa05708008c0fe1a034705c08c0fe1a4345c350690d0f0d41a104144786a0d130d41a1041c35068786a0d21a1e1a834868688f0d41a1a23c35068786a0d0929e1a834344786a0d0f0d41a4343c350690d0c393dd3aa1061182303f86901c92984105d08c0fc1a3bf40e4f221181f83460e41041ec2323f44a69001742303f0690d21298414800ba1182303f0690fd020e404800ba1182303f069308e0d21a1c1a08410470687068310411c1a182383420470685068294e0d082082383438470690d0c33a2344033e81c86c82504808c0d1d11f1a1223e34868708c8d087a0720a62e412824046069088d100b0d042f44187308c8d141f223161a083e4462c34186508c8d0e19423234386508c8d0cfa0692b23642be40265c6907d07a0692b236729932e3586927d07a0692b236729841265c6927d0349591b394f20132e3405927d07a0692b394f2013205c08c0fe1a59f40d25646ce532640c81731a234a3e83d0349590a61009902e04607c0d2c6cd4008009412023034706488c41c86c84117209412023c4084468805868288c386829051ca234044c341447c690d0e8d11a151a2342a3446854688d087b8696aa106a044007c08d11021cb1a18696aa106a044007e08cf1021cb1a18696a6106a044007e08cf1021cb1a184128010011b1a28396342846468508c8d081f423234384646841a6aaa4007e0f811d1a38f40e4364640b904a0901181a49f41e81a4ac84104607f8d20fa0692b208c0f94fa0f40d25642984005c08c0f81a50f70d2378208401720901181648721bc320208250478838d206c8c80822e4128240478838d257a0691bc5645c93205c07f0d24349591901045c93204607f8d243495926408c0f947a0692b214c2013205c08c0f81a50f72b2d4e6404168008c0aa220b1a10692b2d00118152c4163424ee17920823))) else (if i<30 then (if i<28 then 0x2002e24607f8d1c1702303e068888f0d0911e1a11f40bd14ee404105c88d0d01a4e1a43428ef14c208b905c08c0fe1a4349c350690d0e11e1a43431ef7202082e4465c3486843dcfa1c88831002018fa0411720b81181fc347c3506847d0341d544608c0fe1a39f43aa7232084105d88c1181fc34059614d2082e04607f0d187b85e0ae88c98690d093b8f73e81c8ea9c806586909dc2f05748088cb8690d087bdc808288c98690d0b0d21a10f73aa94c2984117261ee7d03904117208c0fe1a41f40a61102082303f8690d20fa5c80820b816a233441c3486867d06f2410820b816a233841c34868786a0d0b0d41a4343c35068488f0d41a1e1a8342447868488f0d0b0d41a4343c350690d0f0d41a4343c350690d0c340530820ba1181fc34869186a0d21a18f73908ca11823c346c350690d0f0d41a43430822e41742303f868c7d0208b905d08c0fe1a434884786a0d21a2423c350690d10fa04117308c119611e1a83486883de20c4008008ca14c5c82e84607c0d187b9f41720ba1181f03471ee7d02984105d08c0fa1a4423c350690d130d41a1023c35068786a0d0811e1a8343c35068586a0d0920c23c3506881ddfa2530820ba1181f385e3901041742303e67e81061182303f0680b1c6f42304706881ddfa05705d08c11816384408308c118162bf44a61041702d84607ce7d02f4530820b911a1a03488478690d0c3ba530a61480fe1a3423c34868708f0d21a1c23c34868688c1181fc3440478690d0c2f453391100172234340680b242f6530a59001722344005911dcfa0530822e41702303f8690d0165c23c34868608f0d21a19f40e27200fe1a29f40d07211182303f868e7d029a410800b81181fc3481ee17ae4223261a43424ee3782f223261a4342c3486847211182303f868b8690d093b9c80822e41702303f86903de2984105c88cb10611e1a434488308f0d21a20f71bc94c298b903f868e3dcfa1c80822e41901f3c418478690d107b9f40822e51182303e788208f0d21a20de08288d0d01a02c61ef1062004002c53e814c208b905c08f0d01640f71bc1045c823c3461ee7d06f04107a0b811e1a43491ee17a2984144658a78690d0f0d21a12773e817a29a4108288cf14f0d21a1c53c34868714f0d21a1df40bd14ce444005c88d0d01a02ca4ee3dcfa0720658680b1cfa0723901045c82303f86901c92984d39190711e1a38f73e81c82984117208f0d01649f40e414c208b905c08c0fe1a43405963dc3885eb900b9119a11e1a43434ee3782f03905c88cc10211e1a43440478690d0cfa0713902e41181fc3471bc1101e8b906408f0d1cfa0533901045ca2303f869014d2082e04607f0d1b0d41a4343c350690d0f0d41a4343c350690d0d2985339008c0fe1a30f784608f0d10298411720ba1181fc3473e81045c82e84 else (if i<29 then 0xf8d31a2423834c686bd07a0d90b3104209a11c1a63434e81a42f059c800b81202303ec69408e0d31a1c23834c686bd06ce4005c08c0f81a38f71bc3640ff1a63464464685868308e1111a18570880b8918232440880f91a48d90800b811f1a034648208c508f0d0a1191a14232342046468594c2264005c48c1181f03c46921bc320572a6110a002e05a48c90016026c1e8364640b905c08f8d01a41f4ca79001702d24607d8d20fa0f40e41640f94fa0f40e41642984004607c0d246f0c808210017023e3471b22e417023a41c680d1d1181e234305c08c0f81a22232342c341c34148288c5868288d1111a1a23c342e341447c690d0e20d1a83446891068d41a234488346a0d11a2441a350688d127a04103e8688d142ce532a61072014005c48c0fa43906f0cec6883d18d083ba596800b816b2063479e8c6843d18d083d0721b28c80f943bcf40e41bc34a596a6d001702d03ec6993d18d0a7a0720de9641c81f30770e41bd2c81f2c771ee1c92c81f2cf463421ef3d12ab4007ac800f9c3d1f41e8d000f940c68354e2984103e8688d18378578a6d019001f345363420ee36420a3205dc68c1dea9c530820e40f986e8d96800f41771a345363420b354da003d073c68cdd02bc5368007cb14d8d086c8578a607c8366a981f1c5363420ee1bc6c83203e5634105a88c8d0f0d0416a232343c341064c690d0f0d0511a22234344786840b51191a1841a342c3412341234123412e81caa983d0654800f9eba3532a75001ed2003e706446841c82cf53083d001c83224607e8d11a58740e4179eead508308c1181fa34a0e418629b530831001742303e97e81d0393c884608c0f9c3a0720bc0f61182333f40d2179a9b4005d08c1181f48748a6d4c20b4005d08c1181f4c747e814c20c406800ba1182303eabe85d2a9b5328008d9001f634469508e0d31a19744b21119031a2c23834c68708e0d31a19740d2d4c2202304407ce08e0d31a184404607c0f1211c1a63431ee3d06cd4004607c0d1c2202303fc698d168d11a151a2342aa6112a002e05a48c0f9e8d11a13f40e40f41901fa3460ae54ea003d03f468c0ca8d11a1bf42a61101181fa34468e1041951a2344be81a6a9b53a80d009192003ec688d2efa0722a65009181f63446905d039069ea654fa014024607d37d1ba05eaa750011b2003ec688d2afa0722a65001181f63446905d0397532a7d00a002e24607d200d2d4ee4044082d0011b2003e9b901102082303ec68c0ea6113a002e24607d8d1c5c82e03fc688d4c2234005c48c0fb1a3b746a6d001732003ec68e0b81181f6344680d187a0de4828e4170233423834c686dd034c536a7101a002e0460880fa811c1a634305c08c0f81e2423834c6869041702303e068b4683468308e0d31a18f40a6d00a00b905c08c0ff1a034a1e814c else 0x698d0c7ba4104607c0d1611c1a63431ee364a984004607f8d01a42f40a6d00a00b905c08c0ff1a034a1ee8e40ff1a20f70e414c9902303fc68e3dc3485305c48c0ff1a38f703e06861902c8570a40e49182303e46929791191a18721bc15c1181fe346447c690d0cfa0720bc1666402e640c6911058d080c6823dc2f0590820b9901a2031a11f41b310420902f2232343c341083468517a1191a1af42e8366208418724ca9020ba05e1b216420b404804ca9051a505e84646861642b93224608c0f91a38f71b294c298412801005cf1a48de0ae10011f1a2a5e44646871670d0920d1a125e48288c69028d0a2ce1a145e8464686bd0ba0690bc16420c3905d46925d02f059082d012002ea3480bd08c8d0e2f42323430b215c9182324407c8d1c390de0ae10011d20e3474bc08c8d0e11e1a1241a3424bc904118d2051a1423c3424bc08c8d0e11e1a145e8464686bd0ba05e1b21061cd2083c82e83782f0d94814828d1c2f42323438bd08c8d0e2f0232343de81672002e24608c0f91a40771e83642c8530a43238d203205e0b215e6412324070e41a46f05719010411f1a40f71bc3642984108060e43782b8c808208f8d1f7a1740bc3672012330de1b215c298c8047c68e1c86f05719008e9071a385e44646871670d0920d1a105e48288c69028d0a2ce1a105e44646861670d082f2232343447868514e8d41a23445e8165644410820b8d14e8d41a23448a746a0d11a2453a350688d127a0590a61072014005c48c0fa42f2232343c34108346841791191a1a59c3420bc88c8d0d11e1a105e44646869670d09fa0698b294c2082e84607d0fd22c84184608c0fd1a38748b294c20b4005d08c1181f49f40de1902ca539909062002e03ec680d3220423834c6887d06c859482d002071a3c23834c6865d0320d94831011c832046c800faa20423834c6885d0348640b294d20c404720b81182203ec69b10011c1a63440c83662023904607c0f1c3b8641b23200f9620423834c6889041702303ec680d1a20423834c6887d06cb40e4007f8d1a3b8641bc3645c82303fc698d246f0407d0390de0b215c2984124607d8d287a0590af32220340046c800d2611c1a6343a3411e83782f2414720b8119e8d0611c1a63436e83642c8574a6d0011b204423834c686dd0348590af101a00233823834c6861642b82303e48470698d0c6f24104607c0d14fa0de0ae0b81181fe3406903d06f0572802e41702303fc680d287a0de0ae08f8d01a30f40d23782b82e24607f8d206f05703e068908f0d0a11e1a124124607d0d11a28f40a61112082303e64ef86858683868288f0d0a3baf46a710420c2304678ee37a2084107308c1181f42f46a71042082e84608c0fa211c1a63438470698d0c3b4f40d2d5629e4005c08c1101f634b0470698d0e11c1a63431ec07)) else (if i<31 then 0x8178ac84105c8688d267a06f0c8564a9cc808390017123240b0ee184acb40640c68d1058d0820b1a10770c8184ac8d96a732020b4003ec680b3220b1a144163420ee1040fb1a02c50de1902f1599900fc173206340595c682c6821dcace4028048ca3dc6f441a80058a1e47b8721bc10420023e3484ee3dc7a0720de5646c8c803fc680b2c7b8d904607f8d1729e4006448c0f953b8f70c85642093206407f8d247b8de2b24c80f9529a4005c48c0fa1a23474ee3d03795926407cc9dc321590a61009902e04607c0d293b8f71e81906452003fc680b247b8721b234013823a41c6909df20223234448346843dc3b8f42b214c2002e04607c0d282f64063486899030d093be4044646899030d0b0d072023244646899030d093be40446468990111e1a1f1a0a23e3486861072051a834468b1068d41a234488346a0d11a2441a350688d122084103e388346a0d11a2067c80c690d132061a1077c8088c8d132061a164046488c8d132061a1077c8088c8d1320223c3430ef9011191a2041a342c818684bd020d402344a8046841dc8d0aa011a154023421ee1bc3205e2b21040f9ea011a10670835008d1037f5368048c0fd1a30770de19cacf53083d009181fa344696bd0378640bc165a98530820b81181f58f70bc1641742303e65e91782cb53880d001742304607d4bd0378640bc165a984105c08d23dc2f0596a60ba11987b86f0c816629b530831021181f50f70c8179e402e84608c0fa17a05e0b2d4da002e84608c0fa47b8592a7501a002e046c800fb1a234b0c8556a9f402800b89181f4355aa65001702364007d8d11a48779e8379acb55a8050191b2003ec697c698d083d0779e9d4da9d40280cc991b2003ec699c698d083c8779e8d57a9844a8050191b2203ec699c698d083bcf4ea6112a032303e70c910420d4003e5e34c6843ddaad40646c800f9a7a353a80cc99181f63471ee556a9d4068008d9001f63446941e97a55368148c0fd1a3864ea654fa014005c48c0fa07bcf40de9782bb4005cc818d247a5d5088105a0040a64700f70e8364a984126448c0fb1a48f71b24c891b1a28f76ab54ea034005c48c9001f6344696bd2a9b40a654800fd1a38642b3d4ca9f402800b89181f48f70bc566a9d4005c08d9001f6344696bd2a9b40a6548c0fd1a38642b3d4ca9f402800b89192003ea00f70b2d4ee4041680c800fa03caf41bc105a001f3007bf53083d001712303ec6903ddaab4064007d8d187bb4003f46883dd20b400800e79001f38f70ee3d0378646aad001181f634069708e0d31a18779e81906f3556a6d001702364007d8d11a6c23834c68610211c1a63440ef3d0390641b314da98416800c811b2003ec688d3e11c1a63430ef3d0348646ab14da002e0460880fb1a234d0470698d0c3b8641b21041181f03c7a3418470 else (if i<32 then 0xf74e816629841c800ba1182303ea1ef9d02cc530839001742304607d0d2e20c40846868910620423434488310211a1a20f7883500a002328f72a71042082e84607ce3de2084105d08c0f987b9f42a710420c4005d08c1181f434b4e890611823834548208e0d0d208231241046248208e0d0d2ca4184608e0d1620c2343430f61dc320596a654ce464003e988308d0d0c20c23434388308d0d0c348688b394f2022304607d110411a1a18640b3d4d29a414800b911a20026a8ee3dcfa0690c9167299530839001702303f8690d0138441846868710411a1a19f40e2720208320478800fe1a49f42d0164e422304607f0d20a9a412800b81181fc34069110611a1a1c4184686863dc6f0596a654c209a20c2343431ee10511823244104686861e47b859883500a001338791ef164a9c410820b81181349f41bc17a2084107a0b811a1a4c418468686104a0423434488208d0d0c7b9f40e272020e400478800fe1a50f71bc11120823c3461ef9d02c9533901072022304607c0aacfa15348208c0fe1a034788308d0d0e20c23434308308d0d0e20c234343ce8165a99530a47232002303e05543dc34859ca79021182302a81ee1962ce532a61072002e84608c0fac7b9534821041742330f70d3167299530839001742304607d0d322cc41846868890420c2343440b310611a1a245988288c11a1a2a414470686905118920a23127448288e0d1120a23834348288c49051188e4241447068816520a23834448288c4905118920a40446348288f0d0d20a23c34388210511c1a2041447068610511c1a1c4108288e0d1020a231041446208288e0d0c20a23834308288e0d0c20a23144108288e0d11fa3538821041742304607d0d4e2084105d08c1181f3bf40af10420c2303f868efd1a9c410820ba1182303e86a71042082e84608cc1c5e444108308c1181f387179110420c2304607cefd1a9c410820ba1182303e89e81c833864d919001712304646941df204232344de85642cc4148048c11d1a03490ee190ace4024608c0f91a40f40de1902f5538a60b98d11a4cf40c85642c9558a61072012303ea0bd9018d21a2640c3420ee88c8d0f0d040ff1a1077c8108c8d123be4084646881de1191a1ec8c804c81912304607c8d213be4044646883dcac8d926408c0ff1a3a77c80c690d132061a1277c8088c8d132061a161a0f1a0a23e3486871df2042323440ef08c8d0c34e53c800b8918232440880f91a50771e81bc3202e2464818d11a4959c8048d8d11a28772b3900a012303e61ee1c868023e3451ee3d0390d907e08e9071a4277c80c690d1320423c3434ef9001191a2640847868708f0d093be40046468990211e1a1877c8108c8d123be4084646881de1191a1c77c8108c8d123be4004646881049181f1e53c800b89182303e0788d207a06f0c else 0xb0d070d0520a23161a0a23e3486861f02cd538a6148284c868008d316629b1a18691b254c29827047c68edd02cd538a614a6402302a88b314d8d0c2cc5363430b2c6850828d41a234484146a0d11a2420a350688d10ba05e0b232111a206344680b013507c3e81c8338640b2d4da0223634055708d8d083485968088c0a943d8640b2d4f1071a342363422ee1a42cb5368088c0a9e11b1a142363420f83642cb530a408f8d1c2f0590a488d100160267634144605458682905118b0d070d04fa0720d23786c941e358680b24fa0720d2364a084102c73e81c83494108208f8d01341f40e41a46c8532821041181fe3406809b0348d92821049901630f40d2364299410824c81181fe3406809b0390d91a050411e2003e744605458682965118151e1a08414462c341c3414b294e8d0d1031a43434474685868288f8d21a191a091a091a091a08690bc165a995304660f65d03485e0b308c0b1c1111a111a09740d29792cd532820b911b1a234a2ee1952f2598a6104172234423834c6865d12f2591b314c20a2363406809aa11c1a63438470698d0c34a5e4b3d4fa002e44671ee1c8340650c83642984104e08f1001fe34c6809bc01eefa0714bc96511b1a381ba0690bc164a082e446c688d24ba0694b354da99412800b911b1a234b1ee19d2cc536a60b9119e11c1a63439e85d12c94144658470698d0e11c1a63439e85d12c8d98a6d4ca0a23440c680d016026d1ee7d07a069c41c68099e11c1a63438470698d0c7b8720d23786c841a8008c0ff1a63404d8dd034a5e0b354ca0a236344692dd0388576a6111a002e446803740d21792cd532820b911b1a234a6e89642bb539905042082e446c69400d2340a082763456e89792c94104e88d8d01640f70e41a4338644bc9662984105c88d708e0d31a1cf40d29792c8d008288cf08e0d31a18f40d29792cc53082d00172234c23834c68708e0d31a1a59a3429e8dd12f2591b314c208274468800fb1a034da3418470698d0c7b9f40e41a4320d90a63402082704607f8d01a70f41b254c20823c4007f8d01a48f71b214c6804128009c11e2003fc680d307b8724b23642984126409c11e2003fc6983d06c8531a010011e2003e069290511e1a1a41447868710611a1a187b48220f71dc7b8640b254c20e4005c08f1001fc34869c9d120a23834488308d0d0e20c2343431ee7d02c9c8883500a01c7bd538821041702303e708288e0d0cfa1680b27551182303f86907d0348593aa7232084105d88c1181fc3404da54d2082303f8680d1a2cc41846868890420c2343444e890511c1a22414470686905118920a231241447868690511e1a1c41846868710611a1a1841846868710611a1a18692d1954a9841c800ba1182303e869710611a1a187b1ee164271c8c808ca118234841846868710611a1a18)))) else (if i<39 then (if i<36 then (if i<34 then 0x2ca07532820b891b1a28691bc364a0f20e34058ed4ca082e246c68a1bd2f2590a40fd9031a02c04d29dd2cc536a61041702363404d308e0d31a1823834c6869d12f2591b20fc1181f63406809aa11c1a63438470698d0c7b8f40d23642994107e08c0ff1a50f71e81c8348641b214c2092303fc6809b13b8691b214ca082303fc691868308f0d0a11e1a1423c3423e81c86f123634468c1ecfa0f41b2504208230348c341c3414478684fd22c8594a7104a0c2338748b2506118232c747e91642ca5328308ce1de7a0720b394e2083d05c48c1191a026c8bd08c8d0c3ccf40e437829823e3470bc88c8d0d3be1a10f70ee17a6e859990c80f14d8d087b8771e83786c9530a61062071a50791ee1c86f023e3464bc88c8d0d3be1a161a0a53a342447c690d0c3e0721bc14c64023a41c6903dd2cb532464846c6853d03a05e4b21041f1233c236342846c6843dc3b8f40d23646471a3f1a0c2363424bc08c8d0e11e1a125e046468708f0d0929d1a1423c34288146a0d11a2440a350688d117a4591b354c2083e2464800f81ea3405809b62051a8344689bd329cc8c800b89182303c4680b283a0596a632120841c809010d11a02c04d93d02ce532a73212084105c48c90016026c0f33d02ca41083901901c6f0596a614b2071a344163421eeb742971a244163421ee1a59071a0265882c6841f42cb534839012032002c04d2c6821791191a1a77c342c341447468488f0d082f22323430ef86841791191a1c77c3424a746851df0d0911d1a1223c342082c690d0c20d1a1477c3428e8bd06f45305c0b61182323498470698d0e11c1a63430470698d0c3a2591b314da9a416340680b0135423834c68708e0d31a18791ef3d07a0721b214c20e4004607f8d31a026e1ee1c82f0599900b811b204423834c68708e0d31a1823834c68708e0d31a18f71b210411f1a03461ee3786c84103fc698d1c01d06f0592a61049912363481bc4c891b1a20791ee1dc392596a61052002363404d708e0d31a18779e83792ca41046c818d2211c1a6343a3418470698d0c11d1a1023834c6869d06f2596a69052002303ec680d0135d1a0c23834c6861e57a0f41bc3642082303fc680d283c8f41bc364a984104607f8d01a50791e81c86f023e34068e3d0348de1b21049181fe3480f23dc7a0de1b214d2084104607f8d2d2822311f40e43646802704607c0d238d0511f1a43438b31421191a20f70e554c1382303e068e141118b0d0620c23234388308c8d0d28223161a0a594a088c786827d0348d90af9049971a39f41e81a46ce534824cb8d61a49f41e81a46ce53c824c80ff1a49f41e81a46ce53c824c811f1a026a3e81a46ce534824c81701fe3493e81a46ce532640c81731a23493e81a46c8530824c81181fe3406809ac7b8721b209c11e2003e0690941118 else (if i<35 then 0x8470698d103bcf44bc165aa85308288d11de11c1a634444746851de11c1a63448ef08e0d31a20778470698d107b8f40e41a46c8530820fc11e2003fc680d347a0d92a61072062003fc680d24390530839001f9320478800ff1a50720d2364e4041c8008f1001fe3406809b07b8f41b214d208410478800ff1a52594478686905118911e1a1274447068717a11a1a18773e85a06ce5306488c1181fc3404d61d12f0d903f8680b01338773e8364a984105c08c0fa22cc23834868916611c1a43444e888e0d0d2f22383434e888f0d0d20a231223c34868714211a1a1c50846868714211a1a1e748bc3642c8d008308c0fa1a4c23840868708e1021a1c2384086871d0fa0d98821061181e38773e83672a9530820fe11c2003e86809b13a423047068897811c1a1a74047068696611823834868a9d11181e83444e832111c1a205944607a0d1111a2003c32a710611a1a2441846868710411a1a1c4184686861d02f0d90aed4c20823c4007d27d06ce530820b811e2003c05809a8b40d9caa10511823c3405809a43a0de4b3868099620c23434388208d0d0e20c2343430ee1c46ce5308208f1061a02c04d59d06ce5308288c11e1a02c05539d06c841c3404cb10611c1a434488308e0d21a24418470690d1220a230470690d1620c2303c86889d111c1a185e44706869d020a2383444b288e0d21a2250446207c88c49d111e1a1a59447868688f0d21a1c234342846868508d0d083b8d96a6107a042304606907d0388d984608c0f81e38771b254c20c2304607cf08d0d0a11a1a142343420e23661182303e078cfd06cf53088105a042303c83e854c20c2304607c0f1e11a1a1423434284686841dc378d9ea654c2082e84607c0b01358773e8365a984184608c0d206c84105d08c1181e33f40e81ca2cb534820ba1182303f06961f5ee85959108c0f99fa05784607c0f61a02678eefd0378596a69041742304607e0d21a63f40ae9041742303c04ce1c42ba4184607809992084184608c0fa1a3078446468786833d07a0721b214c2083f0474800ff1a034c48208c8d0e11e1a1074a350688d123a51a834468994e6444105c48c1181e234059219d8d21a1e1a0a414464687868288f0d086ce532821049912330d94a650420932246468e1bc6c8c82821049901338641b214ca084126408f8d01a026a0e41a46c94104607cc1798d21a1e1a0a232342c341c341c34144786849d18d21a1e1a0f1a0a23e3486874808d088d0433d202343a4046841bfa9f402474680b183b86f0ce167a9f4024607a8d11a02cb0faf756404184608e1051a40640ae5061182384004cebd229ac82820ba11c2023480de966a9b53282500173206344680b01360644bc966a994105c48c9031a23404d61bc2f259aa7500173206344680b0135cf40aed4e641410820b811b20 else 0x9a001fc3486881a022223c34468088c0fe1a206908288f0d103484468088f0d21a306905c07f0d1034c23c3430d2d4e11e1a20690af8690d102be1a1057c3420d288f0d0c2be1a1057c342aa654da001f2340c342c341c34108386841070d0834a23c3430838684d4c20e1a186908386860ba11e1a83440d308d11e1a83450d308d11e1a834505d08f0d41a202e84786a0d103482e84786a0d21a334005d08c0fc1a2b5303f8690d1034c2344786881a611a23c3440d20ba11e1a43450d38690d0ca9e1a11f4c3423bb8685868215f0d0821e1a10694478686d00a00131b530838686721a001fc3440aed4ca981f202e44607d0d11a022303f86881a511e1a181fc34203f8684d4c0fe1a434444786841a70d21a186905c07f0d1034c23c3430d308f0d21a215305d08f0d41a282e84786a0d103482e84688f0d143482e847868872017423c35068ad4c1902e84786a0d1834c23c3486881a30d41a00240d386a0d00121c8c35068009034b53c35068009434940c35068009434e1a834004854c13e1a834004a09f0d41a002404f86a0d001206904f86a0d0012c2304786a0d1034b5384608f0d41a306968009c0e61a00260d308c1181cc34504908f0d41a002504908f0d41a002504908f0d41a00250d209211e1a834004c09211e1a834004a09211e1a834004a1a5a982484786a0d186002868108c11e1a834584608f0d41a22778b310611a1a2a41447868696520c23047068a1de20c2343448ef10411a1a22770e272020823c41868e1df3a0592a672020a2304605529dc6f2410820b811993bc5988308d0d142cc41846868916620a23046868a16520a23834448288f0d0e3bc4108288e0d143b84144706891de20841447068abd1e44410820ba118233c770eef202082e84608cebd1e44410820ba118233c59c34244786841df0d092ce1a1223c3424b3868454e20c2343440f61782c85708208cc1ec3485e4b210411e1a3e740d2164ea9c80820b812023c3404d79d034859390104170233c418470890d113a223445068817911c1a1a7408288e0d112ca2344506889d111c1a1a59447068696511a2283444e888f0d0d2ca23c3434b288f0d0dee85984708881a42ba4105c08c11183885748308c1101630697909041742304460d2d4d2084105d08c11c22442323424ef86849dee4132446c690d18391591b21072003f0478800fa53be1a12230e1a0a23e3486869dc3b85eb9088d8d21a38f70d23786c9c826408f8d61a48f70d2364299c826588c0ff1a034a4ee17ae404126488d8d21a40f70e41a46c8533901072002303fc680d313be1a12230e1a0e1a0a23e3486861df0d081f2231477c3428ef86851df0d0a3b8770b2f201742304670d216629b538821041742304698470698d0e11c1a63431ee1a46f0d90839001181fe34c69400077)) else (if i<37 then 0x780fd1a184124607e8d10a9c4108207e8d162084124608c0fd1a305e246058617891816185e26448c648d8d0834c23246c68836611923634484648d8d0e11923634384648d8d0c34c2324607c908c91b1a1c23246c68708c91b1a186984648c0f9211923e34c680995a9c23246c6881a611923634484648d8d0c6f12303e31bcd4c9181f23f42e848c0f90b50de24607c81641712303e04ca378aa92303e41bc509a012303e51bc48c0f8cb40de24607c83789192003e4a341a3410bd5018d11a205ea8048c0f902f54026448c0f94a031a1340281c6a8d01328644b2d4c29c4084607e0d207b8de4b308c0fc1a30648800c80f912c85788007e0d147b84447207e0d143925988108c0f943244004607e0d152c8ce88008c0fc1a30f70808e41181f83468800d41181f83458810698d013204003fc6a0d01328d96a71000fc1a026688008c0fc1a0265089c698d0c391680bc48c848d8d083492364146881c46f12303e4246c838d11a205e24607c61789912303e463416e837a1181f83451e88e61181f83451bd08c0fc1a20de0808e61181f286804607e0d106f04047208c0f946f02303f06881789181f193224607c06118d042f12303e31bc96429c2303e51bd08c0fc1a22590ae07e0d103925905cc6881a01181f83441bc9641181f20de04607e0d103404103f0680995a984103f06809941181f83404c81caa992303e4aa69042092303e5aa64c98d11a21536342aa648c9101f0185aa6d00a051a02651b216429c2303f068c3d229a3984607e0d186f0d90b308c0fc1a30688a608c0fc1a285919c08c0fc1a2c530808e41181f83460d114c0fc1a02658a6d002041a63404cd14c1181f83404ca4c81712301842640b89180c21236414686d001751a63440e248c0f80c2123641c688d1091815112302a2482104918c99123018363416805028d01320692474698d1017123a34c68908c9181f83440a708c9181f83451e908c9181f83451bd08c9181f83450e248c0fc1a202e24607e0d102b92303f06881109181f83440e40b891b1a206884648c0fc1a2b4008108c91c1a63466a60ca1192303e50d248f8d31a202e247c698d126402e24607c06166402e24607c06166402e63430d20b89181f01856e81a21181f83454b23661181f834030c8e61181f834030a1ca1181f182e03f06806103925984607c81c91c8b984607cad541701f834404607e0d00c225904607e0d00c2a3916e08c0fc1a01860e408c0f8c1701f02603081c9a982e846c6809981702363404c061434c23c343447880098c34b404478800994e461a115328186861a6a0223026444786858682d4f0d08e4223c343c34108386841a4a061a19f40d386a0d10323532a750087770d0834864a8088f0d14e4540c3432818684d4ea061a18690d15030d21a2b4003f8686d000f8 else (if i<38 then 0x26508c91942f0d94a64ca11923305e5ba3661192328de44648c0ff1ac34608248c0ff1ac3404cc1c82f0572aa88c9198fa0d5c3431bc90420a2324651ee1c82f04428488c919cfa61a10dd1b254f0d103905e08888d8d11a30de17248c0f906f04424607f0d143925e05c88c9191a30de4821041722324665e94688d0c6c85326435e94684b746c8839044a3430bcb761192320718bc48c911034c5e0b248c81782b92324440bc11091922245e05c48c9110340644bc08c9031a23472d09786f12324682d097891903431a10690d0978119034a40047c690d146f42324607f0d143e05e29c48c836611923c3441bc90420923205e1b24c891906cb1a10de84648c0fe1a28de84648c0fe1a28f70bd1001f92328de0bd1001f92328f484648f0d102f44026448c81018d087bc4028008f0d146f42324607f0d146f0b984648c0f9420039047c690d146f42324607f0d143906f4bc48c83792084124640e49781a823240c688d1c3903563433e808f0d0c2c95304786881a52f03504641bd08c9181fc3453e8379200b984648c0fe1a40de84648c0fe1a2c5e1bc48c0fd1a83461bc48c0fd1a245e1bc48c0fd1a83468bc0b89181f83404cc3792012303f468b1786f12303f46a0d1a2f0de24607e0d162f0de2464800fc1a31f40bc10511b1a23460bc10499223246508248d8d0d11923c343e3404c40b89181fc3404ca17aa044044648c09982f54088088c91813304003fc6b0d10a0040634308088c91f1ac3404cd10420940026408248c0fe1a02651ee1662014063451ef100a031a20598802e58d102cc40280c6883de2014063441bc166200b963458802e58d0c3905e0b354c20a232467aa690420a2324650bd54c20932446c688d1ca9841264c68888c91e1a19f48829070d0132d53082900a0013295308248c0fe1a026605c48c0fe1a0265246054490420923185e26448c648c11b1a1a4184648f0d1120423247468099420c2324607f0d1420c2324607f0d013315308308c9181fc34605d08c9182303f868c3782092303f46a0d186f25308248c0fd1a30de08248c0fd1a83460820b89181f83451bc1049181fa35068c3782092303f068a3782092303e41bc1049181f83458821049181fa35068cd4e2084124607e8d41a3c4108248c0fc1a29f40bd32111b1a23460ee1792c859a8088c919c2f4c8a804c91192334c8280c6861dc2f4c8a8088c91982f5538a73211192303e70a632020f1ac3450bd54e29cc844648c0f9ca985399007c817aa9c5399088c9181f3b748a654d8d106cc53072c6883662995363441b314ca983963458a6c68514c1cb1a1c532a6c6861c82f02e05a88c91982f13205c88d8d11a313205cc68617817223246488a3780fd1a18de0a607c63780fd1a182e24607e8d106f01f10de08207e8d103401fa3431bc07c43 else 0x634058b321208231cc804607f8d106ca4104630d2904118da9cc848208f8d141702363430d207f8d31a24c804607c61a66402544608c0b186f05e4821051c82544608d03651913204a88c11986c82563430829001ea3904650820901181fa35068c1041202303f46a0d183482e04607e0d142082404607e8d41a306904808c0fc1a2b535901041202303f46a0d22a02236344680a943bd4044608c0a9420a3226488c1194a022363430c8d4e11a23634584688d8d0e11a23634384688c0f8c3922363430d219211a2303e584688d8d0c7bb1a135384688c0fb1a2cf444607c61782ba23046054a54c20e1a185e46488c11902ba2363430e40b816a23046880c0b51182302a406488d8d11a202e44608d8d101201fa34304807e8d0c2082e04607e8d142b82403f46881041702403f468a0901181fa3442a6b201201fa3450bc0901181f202404607c6d00a002404607ca0901181f19596a60901181f2869a8088d8d11a02a6a8088c11815254026488c11815294063420d2d00a003d47208f8d51a405388108d1181f83461bd08d1181f834508888c0fc1a207288108d1181f286419110211a2303f068e3dc6f42344607e0d186cb5388108d1181f834708888f8d31a224104746861ecac8d96a608f8d11a387104808c0ff1a286904808c0ff1a28690a488c1190fa069e3430bc90420a3944608cc54c99223046054ac682d00a003d47208f8d51a38691b308d11d1a63462a732211a2303f068c3d26442344607e0d18a9cc808888c0fc1a30d919088c0fc1a28de84688c0fc1a28d9447c698d103483f44608c80fd11823193244608c0a918d047a0d984688c0fc1a305744607e0d103942344607c83de11a2303f068a37a11a2303f068a365a9c2344607e0d1817223e34c6881c834a23046880a88c118151a410828e51182302a6264c688d0d8d05a014007a8e411d1a30de84688c0fc1a28720d308d1181f83461bd08d1181f83451bd08d1181f83456808e411d1a202e047468708d11d1a1b4084688e8d31a2c234474698d103882404607f8d1422340047c688d146c82303fc6881a51182302a444608c0a8c2f2410828e511823313244608c0b118d05a014007a8e411d1a34234474698d1211a23a34c688105a003d4722e411f1a3b5303fc6861a41282404607f8d1820b4007a2e41181fe3471b20941181fe3456800f51c8b905c08e8d1c7a42344607e0d146c85384688c0fc1a30b984688c0fc1a28d984688c0fc1a282484688c0fc1a28d984688c0fc1a287217308d1181f282e44607e0d101242344607e0d146cc2344607e0d145cc2344607e0d143935384688c0f943902e246324615e91786f42324650c817a29a23634468c16429a23e34868a3789181fc3442e83782f22324651ee17a6ea2324651ee3786e94020de1b248c0f917a45e))) else (if i<42 then (if i<40 then 0xa6900201034453c34868814f0d21a1c5317288f0d21a29f48a60c911e1a02c68a6905200404478680b1d29e1a1032447868694f0d0929a41c3434a688f0d21a225309a9070d21a282e03f86862e611a2303f868a08c0fe1a183d17288c1181fc3463e87230d41a43450a786a0d0c6f0b9834305c08f0d41a2057c3506861105ce1a83444820bb0d41a242304786a0d112083d84608f0d1529c2304786a0d170d21a1023c342c3486849070d0929e1a434304786849040fe1a434404607f0d0c0fe1a83433e888c0fe1a834505c88c0fe1a834508807f0d41a224103f86a0d103401fc3506881001ea2303f86a0d19298538821062001fc3471ef1000fe1a20f70831000fe1a2c4108310111823c3461ef1000fe1a24410831011181fc3461ee94e2001fc3451ef1000fe1a20de03f86863780fe1a18de39088c0f906f01f10de03e205c07f0d0c1701fc34305c07f0d0c2982e03f86880b80fe1a1a5308207f0d101701fc3435e80961182320670c854c12a23440c688d20ac8d9447c690d143d8d904607f0d147b85e07c0951182331f41b25030d101202303f8688bd21913204b08c11986cc3226409611823305e1b30c812c2304660d23641181fc34058c1c82b95504a88c11a2039f41b386861792084147209511823387208850a2002544608d1020a144007c0951182330dd2a786861ca2014006409511b1a234804808c0fe1a204417208c0fe1a287205c88c11a2023464821051c82e05a0951182342f404b4688d106c93204b4688bd28d086c825a3430e411020025a3458810e411b1a244087208d8d1220439046c6891001c82363448800f41c82363450d20961182303e51b254c12c2304607cc3781f42304607ca0ba1182303e058a1112003e04b08c1181f382e04b08c1181f28690c809511b1a234054e1a41282302a40f63640fe1a2069464094119012b1a10f748008e8d1034a23e3404c890111f1a43404ca1a464025447c690d183482404607f0d146ca3204607c836411b1a18711b208c0fe1a285e99088c1181528de0bc90420a3944608ce1786ccc846488c11986ccc8046c6889011c823a3440f63641202303f868c3dc2f02544608c0a986f05e44608c0a940fe1a105e46409511823281fc34204ac6841e47b940c3440f22e41202303f868c3781181fc34407a2e41181fc3450e4566a9cc804a88c11a20405eaa7321208414720951182348721b354c19223634468e1c86c9536344aa69011c823a3453e81c840901181fc3440e43678d016215304808c0fe1a287204607c60b91182303e054a17920a390720b91182303e84800f51c8b9047468c1a41202303f868a3782203d17207f0d1a20a4104607c836620823634408208d8d0c1702303e388208d8d0c20823634305c08d8d0e2082303fc680b146f34007a08c8365a9823 else (if i<41 then 0xc8e45c81f83451bc15c0fc1a20de0ae07e0d1034823e3486881061192303f868a36611923c34408308c9181fc34508308c9181fc3450e59041f8c2092303f868811020a2324607f0d182b81f83430e4d561181f20ce04607e0d106f42303f0688365a9c2303f068a3781181f83440bc0ba1192384458800f817123202e84607f0d102003905c08f8d21a302e84607f0d106c82e84648c0f952982e24607c89001712324007ca0b911923444488a0b91181f03cc688d016386f05c88d9001602664a690111f1a43404cc0b911f1a434405c07f0d0c1712344407c80b91181fc3441ee1781722324651b22e40fe1a205e05c88c91a22284144648c0f901722303e0798d11a02c71ee5030d0c1e82e03f86881c8171231a410820b891902ca5304607f0d141702303e0798d11a02c04d108c91e1a186904e08c60ba1181fc34405d08c0fe1a20694a608f8d21a282e84607f0d103902e44648c83792084105c88c91983482e44648d11122304105c48c0fd1a83460820b89181fa35068c1041712303f068a94c2082e24607e0d182082e24607e8d41a304105c48c0fc1a29f405c0b511b1a23460ee966a002e05a88c9181f40414640c817123634868e1dea002e44648d1101f38f40de965a9a3203e61ee3d12c8d963451e81bd8d0e7a25963431e80e40f8c7a0720dfc698d147bb1a14f463422a61041771ac3450af14d8d0c2bc5363438a60e58d0c6c8578a6c6883642bc5363440af14d8d0c3902e24607c81781e82e24607cad001f02e24607ca1c81712303e405c48c0f81520d908908c0fc1a286808808c0fc1a2a590a61101181f83460e40b80fd1a203d05c07e8d10a002e03f46881c81701fa34405c07e8d0d208412463aa69042092303e5aa60b49192203e505c07f8d0c17123e3446880ba1181f83444722e41702303f068c0ba1181f834405d08c0fc1a202e04607e0d130d070d070d21a161a0a40c3423e814f0d0cfa057c3486887d05ca23c3441ee1105c8cfa04105d868814e11823c35068a3785ce1a83441ee1a05cc1a20684820bb0d41a2a53c3486878690d0b0d21a161a43424829030d21a21f40a786a0d21a29f417208f0d41a28530882e70d41a2e1a434204786858690d0b0d21a161a43423918690d0c29823c3431ee7d05cc1a205717308f0d41a284105d08f0d41a2c2304786860f611823c3444a614e11e1a20f71bc2e611907b9f40882e487212082ec34444608f0d21a2023c3486863dc5c823434402c148288c0b0d2981611f405c88f0d1111e1a43434829000b0cfa01f43405887d06f61a43441bc2e5118c6f0b910de17288d0d107b8de0a71045cc2330de8822e611906f04105d86883dc6f44117208f0d21a38de8822e411a1a28de88310020423446058e7d2299c8c34868a14f0d08fa45317288f0d146f0b910728 else 0x3264084648f8d61a324103fc6a8d0162a770d39001382302c60c81072042324607f0d1c7be4084648c0fe1a306948008f8d21a28f7c8108c9181fc3461ee19c2f4c8c8048d8d21a44f41b39011913244648ce9de7a069c8088c919223b534a71042092303f46a0d207bc4108248c0fd1a834788210491c1a20f78821049181f83468821049181fa35068c3dda9c4108248c0fd1a83481ef1042092303f068c3dc379596a75009181f38f70c95009181f02a60ef5009912303e50ef5009192203e50ed5009181f2077a804c89181f2877a8048c9101f28f76aa1100ff1a287c1ee07f8d106f04d03fc6883dda981fe3441ee07f8d0c3bd4024607c81eaa0132634468a1dc2202e24607ca9040f887a06f246c800ff1a30d924607f8d103bd4024630ef50099123254005c48c0fd1a2877a8048c0f903bd4026448c0f943bd402464880f96a002e03f46881dc2092303e40f21dc2092303e51b248c0ff1a212364007f8d11a28779e81049181f28779e81049181f28779e81049181f28641b21061181f2b5505c07e0d107b86408208d8d146c82303f06883dc3204103e41b308c0fc1a20f76a708c0fc1a28f704607e0d117a45e0ae4ca1192332f48bc15e1192324460bc15e1192324450c89782b823240c688d1c34241a34348146849786c85726448ca1a52f05704640d2b2120023e34868c37a1192303f868a3dc2f0578800f89198fa0d90830e68d142f0d90af1009912334402810e411e1a28de84648c0fe1a284007208f8d21a28de84648c0fe1a2c5e1bd08c9181f2af40bc3661192303e61bc3652042324607cd1786f12303e41bc9009192003e50c81782bcc8446c688d1c7a2531909078d51a30f71b29028d102f0d90af32099223246799088c9181fc345483c680b0d20223e3486809942b8c848288f8d146f45924607f0d147b85e0ae88c91946c84187346881786c85744648ca3642b81fc3440bc15d11923222324607f0d107b859281868837a2c8d924607ca1c82f0590ae48ca3782f24108288c91982f0590ae48c87d0390d9185e0ae48c0a906ca41a3431bc17920841246548146841786c85726448cb08c91e1a18de84648c0fe1a28de84648c0f9034823e34868837a1192303f868a3782092303f46a0d186f04124607e0d146f2c808248c0fd1a30de08248c0fd1a28de08248c0f902f6538a750111b1a23471e814c20d40e35468c17b29c53a804c91192338770bd94e29d4044648ce17aa031a23440bd5009192203e51b21111c81f83450c91001181f83450808e41181f83450c83222001f83451bc3651cc2303f068d1001382303e41bd1649191a205e24607c61789181f185299048c63782f24108248ca1a46f241247468a1789181f185e24607c6dd07a42303f068a3791c81f83441bc8e45c81f83451bc15c1181f83451b)) else (if i<43 then 0x61e809e11a23a34c68c3dc20c234474698d18390d96a708d11b1a304184688c0fb1a28f484688e0d31a28d984688e0d31a28de1b308d11c1a63461e809e11a2383450e436611a2363451e809e11a230470698d1c7b84184688c11b1a30721b2d4e11a23046c68e10413c23446408209e11a23204184688c0fb1a2827447c698d015282e04e88f8d31a282e04e88f8d31a285948288c616520a23187b48288c61ec2ca414464482d030d21a207b3e8164a9a4144663e89041742321538829061182328f71bc9061190b44414820b811943435348308c119520c2304630d090611823206848308c119120b40c3486887d0a9c4148308c11982724184608c814920c23046448308c118c2724184608c814920c2304643909070d21a21530a49061182328f73e9104208232c41083100170232c41083102118232c410831021182328740c8d4ca9c4148308d11a07b8de08308c872220a4105c88ca1d220a4144608cb10520a2318f748290011903d86448288c819120a2318640c2d4d20a2329f40d290417223286948288c6905a061a43443e81a43224144607cc3dc6f15308288ca37a2084105c88ca3dc6f44108288ca3dc6f04144643e910420d4028108d1181340f748308c0f9220a4104607c83dd20a4004607ca7d0e444148308c1198a9c4148308c11947b8de08308c1194fa44148308c119620a4105c08c816620a4184608ca906118231a4184608c0a9120c2304605489061182302a448308c118da9a4184608c0a9520c2304605489070d21a1a4184608c0f8152c4148308c0f90fa24184607c87d220a4184688c0f9a20a4184607c85a220a4104607ca9052002303e424610c81072012303f868c1dc323534a79009942324680ee1796e8d984648cc1dc2f2dd84648ca1dc3464024640ef9009912320f70c990211923c3464ee364a9e4026448cc19020e4084648c0fe1a38d9c8108c9181fc3460ef1001f12320778804c891903b8646a694ca9e4084648c0fa43b8de1b308c9181f34770839021192303e60ef9009181f24770a59009181f287707e48c9001f28770c25672022324660c8565299538839000fe1a40770c81072013244648ce19220e4044648c0fe1a38770839011181f634468e19020e4024607f0d187b9591b21058d14acc4148207c85662081f18f703e20c85646ca4120770c89046191a9cc848241e80b80f8c324c848230c89040fb1a20f40c33200f9032041c8048c0fe1a30771bc1791192328770bd1011192328771bc88c0fb1a234058e1dc6f041a8007c0b193b959aa79011192332771b354f2022303ec688d0164d5348207f8d51a02c64ef9001712303e50c81072012303f868c3df2022324607f0d187b864c8048c0a953b9591a19009181536404644c89190ace4004607f0d153be4004e08c0fb1a23405809a4 else (if i<44 then 0xe16620b1a20594839006d4d20e4002641ee3d32031a2241c8004c690409883c8f71e837b2031a30794b248c61c92c8d948308d8d187bf1a63431ee1782c82e24651ee3786c923a3451ee9068d0c7b82ea34c6881dd7a123e34468b1dc7b8de246468a17891887b923a34c6883dd2c8d9846c68a3dd2c8d98470698d187ba591b208e0d31a30f41bcc6809917a4598a03421182330670c914ca9a23634468e16429a23e34868a1ec6c823c3444a7104a0c2304651ee17a6e85044608cc7d06e941c3443e81a411e1a23404cc0b81181fe34468a1a411f1a23440e40b91182323454825041722304658b236629953046c68cbd01382384146a0d197a1740470828d41a02671b209c11c20a35068c88d8d11a02a40b2904a0a2304651e81a411e1a23450c8d4e11a23e34c68d08d11b1a1872446c6873d111b1a18f4446c6873d1a9a2363404cb3d0fa22363449e8d0111b1a02659e832111b1a24f41e832111b1a285e44608c0a90fa141a8108d11e1aa3404d037820823c3446809992c85928288c1181532591b294c11d1a28de1b215f0d103902e04646881a4a082302640d208f8d11a214144608c0a9211a23a3431ee1c411e1a234528208c098c34823e34468810511823234054a9646804144608c0a992c82303f46887d211a23a3440d217813823202e04e08c6c688d01518654b288c1190a0a230460548965a9953047468a3d034868047c688d186f0d984688e0d31a304168108d11b1a284184688d8d1020c2344607d8d1434a23e34c6881a5a0223e34c68a0b911f1a63440d21a013a23e34c68c5d11182302a4046c6841c499027047c68a3dc1181f23440a088c118ca0a2304605487d211a23a344aa654e11a23a34c68c1a411f1a234444608c0a8d2ca230460548965a9953047c6a8d18fa069847c6a8d14a0d4084688e8d14a0d4084688e8d1434823e3446881a46f041047c688d187a0d90a708d11c1a63470e436611a2363453e83d211a23e350698d013402e447c698d102d55344608c954ca0a23046054a1a42cb532a608f8d51a39f40d354e11a23e35468e7d03955384688e8d19a995384688e8d31a3553282d0211a2363460d3c6841a46c835047c688d182ca2304605485dca0a23046054b08d11d1a1c234474698d1211a23a34c6887d038827047c68a5dc22340047c688d181702303e468888c118151a5944608c0a90a0a2304634b254c1181fa3453e908d11d1a214184688c0fd1a2c234474698d10a0c2344607e8d14a0c2344636a650611a2303f468d08d11d1a63440d237820824047c688d1e6414144608c0a966414144608c0a9664023634319108d11d1a24c884688e8d31a2b5399108d11d1a63461ee7d011f1a23452640b811f1a206999008c0a906f14144608c0a94348d9046054836411b1a18c804f08d11823a34 else 0x220a4105c88c810412423447088a7d020c2344607ca1051181f02c40e40b91182323454ee08f8d11a20f72b20b9118232a771ee1c411e1a23464ee1041702303e54ee10411f1a203e44608c73d0aa83e44608ca5641fa23046484688e8d0c3ba41047468908d11d1a63440eebd011f1a23458ee3dc6c83f047c688d1c3ba4105c08c80fd118231c234474698d10ac83f44608c908d11d1a187748208e8d1211a23a34c688bd211a23a34c68a3dd7a023e34468b1dc7b8d9047c688d183ba41046307e88c118e11a23a34c6881dc2083f04640e436611a23a34c68d08d1181f63440ee36429823e34468c3dc6c823e34468a3dc1181fe34468a3dc6cc234470698d187bc2344607d8d147bc2344607d8d15a983f447c698d147b83f446c6883dc1fa2363440f87d06842304651b20fe11c20434507d08c118c1f42304633e80fa11823204184688c0fc1a29f408308c1181f286907e48c63dc6cc23c34468a3d01f923e34468a1dc7a069047c690d187bc2324786881a412223247c688d18a084124604c848f8d11a02640ce10491b1a43459e810511923214124605861e52c9231923e3404c71dd2c941a81468a48f8d11a02641e837820923e34468099c34941246368048e8d31a0265247c688d013206804e48c11f1a23404ce1852cd4024644b2506a001fa3404cc1dca08131b532835000fd1a0266a8048c0fd1a0265e3404c43dc6f041247c688d0133cc828248c61a52c94124644b23668d31a23539900ba8d31a2cc805c48e8d31a28d90aed4c64123e34468e1c89902e247c68a1a491b20e344680b193b8691bc50491943ca771ee1068d31a30690474698d103084168007d8d01332c80820b80fb1a28f71e81041f923e34468e3d03492304607f8d11a026808248c0f91a02c51bc9646cc23834c68c9dc7b869082c68a10611b1a1a5e08308c0fb1a2869681c698d1034b20e34c6881a78d31a182ee34c6863786ca23246468a3dc3964005c48cb90091882c853447c690d143925e0820b91192323470f83dc2f05099048cc3dc6cc23247868a3d06cc23246c68b08c91b1a1c23246c6863786cc4024607a8d41a3a4044648f8d51a02668ee3dc7a041247868c1c82ca4163441e))))))
def ql11 : Nat × Nat × Nat × (Nat → Nat) := (3758,9,18,qd11)
def qd12 (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0x7aad4f7369f04d3e29a7bd34f5a69eb453ce9a78d34faaa9f1151e1da3bb3478528eab51e09a3b13478128ea251c46a3c53478a28ef4d1da9a3ad3475a28e34d1c68a3d55478767eeccfd569fc1b3f7367ec6cfe099fb933f6267ea4cfd489f9933f22a7ef4cfda99fad33f5a27e74cfca99f9513faaa7f114ee199db2b3b83676c6cee099db133b5267664cee059dc533b8a276d4ced699d9d33b2a677554ee0d9bb9b377266ea4cdd489b9153776666c6cce0999c11336266664ccc8a99c0b3371666d4ccce999953332a267554ce2295c3b2b86656eccae1495bab2b65656ab4ae0995c112b72656c4cad4995a912b22a5702cadc595a8b2b8a657144ade995b532b5a656b44aca9959512baaa571149e1d93c33277664f0ac9e1493bab276564eab49e0d93b9b276364ea6c9e0993b13275264e64c9e0593b8b275164e62c9e2993c51277a64ed4c9d6993ad1273a64f5549d5687a910f22a18675b08ab608d6f765f7023ed447d908fb119f1115865db03bd6055ac04558046b13d360aaac71138dd971c28e3559c6e6b8d8d71c08e3511c62338e2871ad0e31a1c32cd519aaa19d55926a84555046aacd354aaaa9115419aa819d5011aa330d3222a6cbb4c77a9cecd3156a6b1b4c33a9b24d3a09a61154c11a9d14d39e9a65554d98689115165da23bd4596688cd51156a339b459268d04d108aa208d459a68d14d19a9a2555478896f0eade195bbb2b78516eab2de0d5bb9ab76356f04ade085bb12b75216e64adc8a5acc33c88a7b2ecf1de9e3353d95678ab4f64d9e19d3d9267b04cf08a9ec8b3c11a7b34cf5a89e5553d98671114ea1d9ccb33976670cd4e6559c2ad3993670674e6499c1153991670234ea299c5553877a68674d08a9b453367a66b2ccc19a98c9b3033a6324cc08a98c8b3281664e2cc04698cd3326a66294cc2aa99c4493875270ca4dd949c289375526caa4d5649c1a9373526c6a4e0949c109372526c4a4d4949a9093325264524e0549b8a935152330ca22294cbb2877a532cca19a94cab2855a54a8ca98d94c932932650454a6459540b2941650234a669954532a7a654d4ca969945552998649114965d923bd2596648cd49655922ad265464b26c90ce92c93266264845496459338b254164c62c904692cd3268a64cf4c99a9932d3263a6495549dd93bc1277820eee49dd893b91477814ef021ddc53bb0a77514eea21dc853b90877118eed49dca93b8d27488a18ef431568619d0c22a1823432aa864d36c669f0233e2aa7c4b3609a6c111381de70334e0559c0673808a7008ce0aa9c134d5269a84d34c88968ef2d19a5a2acb433968452d0465a554b49a67934ce2699a4d3319852111241de48cb29066920ab240ce48c929022920232496948554904165134ca2699233475924e8451d5053a98a74118e9551d else 0x20a8111c410d03487234008c202391a0447104340d1953104230689a9883a00470d0346d4f4088e200721a068fa9e80118450d0346bd3dbcc0bc25bbd0bb71bb12ba9fba40b9cdb964b905b8a6b81fb7e8b775b6eeb67bb5f4b595b4fab491b464b423b3ceb333b2a2b207b176b103b0d6b06db02cafd7afaaaf55aeceae5bae06adbbad34acc1ac30abc7ab86aaebaa6eaa2daa00a98da906a8cfa85ca82fa7d0a749a6f4a663a60ea57da51ea4aba44ca401a37aa31ba294a1f9a17ca11da0a0a073a0009f839f569f159e849e1b9d629cdb9c369baf9b829b379ab09a1f99b6996b992a98a39844980397a4974596d296af9646960f959c953394a2941193c6933f92b8923191be912390b090478fca8f938f3e8ec18e268dc78d728d1d8cc88c378b9c8b018aac8a4389b2892188b888278796870f8688860b85c0854d84e48467842683b3835482ff828c820f81ba818d811a80e3808e7ffd7f8a7f177e867deb7d787cfb7cba7c337bac7b257ada7a5379b8793b78fa787d7814778d776076f776ac7611758a74f974c2748b745473e1735a72fb729c720b71b6713970d070676ffe6fa96f186e7d6dec6d796d1a6c436bc66b536acc6a6d69c86973691468d3684c67f7679866df6694662b6590651d64e664b96482644b63ba636562e8627f623461cb6176610d60545fff5fa05f4b5ece5e475dca5d4d5cf85c995c445ba95b545aff5aaa5a0559ba5965591058895816578f5712568b55fa55b95564550f54745401538e5339529e523551cc515950dc50554fa64f5b4ed44e6b4e164d7b4d124c6d4c044b554af64a8d4a2e49e3493e48e9487647db477247094682463745ce451544c0441143a8430342ae423b41dc414b40c44097406040293fac3f1b3ebc3e713dae3d4f3c643bfb3b7e3b0b3aac3a6139bc393f38cc384537dc3769372836d33692365135e8357f352034c1346c33f933a4335932fa3287323231d331743101307a2fe92f622f0d2e862e312dd22d7d2cec2c972c242bcf2b3e2af32a9e2a3529d6296d291828a5281e2797271a269d26162599253024bd245e23ff23aa22f122882201214820df20301fdb1f901f271ec81e691e141dbf1d101c7f1c021b851af41a6d19f0199b191418c91888180b1798171b16c616531612158b154a14b9146413d31342129311f811991112109510220faf0f6e0f230eec0e6f0e060dc50d8e0d430ce40c710bfe0b950b360acd0a780a2d09ce0997094c08d90866081b07b2075306f406bd0686063105fa05c3056e053704ec04a10460041503d4039d03700339030202b702800253021201bd0168013b00fa00cd008c00410000d56b1a916322ac714d8de9b1ad3635a2c654d8ca8b18d363aaac6ecd5d8daba895711aaed4d5ce9ab8d3571a2af5555e22a9c3353812a62354e1da) else (if i<3 then 0x4801c8649184691044902352bd253b22419023208d20c691a55e8ba1bc2f0b3299912007e1c86491a400f83c8d03517d0de10540100b9c831a45e864483194478d2347bd0de166531043248c2307d1a51bc6caa629991a06400fe349bd0de14c410c92308c1f4693a9d906468011a400fe348bd253320418ca23c691a42e86f0b3a9aa62959020e80a007e1ca469003e8d02711ddf4d4c53b2241d00400c823c801fc681a70d06f1b2646802006411e400fe340d31f41a0de14c410e43208f2007f1a0698390d02cea629d9120e80200479003f8d034e1a35314ec8907401003208d2007f1a069a341bd644825e06411e400fe348d018c7d1dd755c8106238821a43e8348d1a9aa6e4083a00651184710434d7d0697222308e20868eeab91a04471043467d068d4d53720415003288c238821a60d23439020e801944611c410d034b7d068d4dc8107405003288c238821a60d2340ae2085d1184710206815d53720415003288c238821a5be9a988820c4710186815dc811041500320ba2308e208681a6baa2085d11847101868d4d5372041d01400ca2308e200721a619c34b902085d118471003881a057d4d53105400c82e88c238801c0698670d2340afa9aa6a0064170460e4340d30c00b8691a057d4d5372043d01400ec320b8230721a0680188d2340aea9886a00761905c120470d034c3002f1dcf495753922238821a06933bce82f0b2eaaa6e448320447104340d3677bd059d4e419003288e208681a80993bce92aea724483200470d035012e77bd05e165c89064088e208681a58efa988311c340d1877bd353104238681a38ee3a0b22084657d07417a55d4c415022388a208681a60ee2f4aba988311c45104340d2b53d002308a1a068c3bea611a340d14771d059d4c531042338eefa0e92ad9111c410d03499d05e165d554cc8d02238821a0696fa0e92aea764082a0447104340d2e74166c8d003288e208681a80953a4ab64681200470d035012674178593234088e2007a1a06943bcab6408311c410d03481dc59b234008e1a068f7a0b229d9020e80118408d247416441d002328ee3a0b229d901180471ddf41d255d4e48906238821a06973a0b2eaaa6e448320447104340d2df4d4c41502238681a3ce82cea720c8019447104340d2a749575392241900238681a4ce82cb9120c8111c410d0349d4c4188e1a068ba988211c340d16f417859d4c411002346903a0bc2c882119477bd3531042328e82f5aba9882190468d21f494c4108c0228eefa4a720c470d0347754537224188e1a068e3bbe9298821180467d2531044088e1a068f29c82194470d034694e4108e1a068ae40821180447224188e1a068b2988311c340d15d594c410c8238681a3ca6208470d034554d4008d1a20e82f0b3a988211986816453b2041100234690fa6a6 else 0x41d00400c823c801fc681a71e86f1b32999120880190479003f8d234d54e41c691a248211a418d2345178c89071a468a7b1e9a999020872190479003f8d034cbd0f4378d916553320410c823c801fc681a70ee7a0af640821c85c9184693d2c81054088f1a468f7a2e82f0b22bd9022083200721905c16a4611a44112408d4ef4b22419023208d20c691a4de8ba0b22bea729aa6e408820e81202801c8641705a918469003e0f2357bd05e164c8906408ca23c691a55e82c8afa989b64082172461183e8d30777d0f41cb53d02320cb2007f1a58b22b9aaa98a7a06400fe349bd2c81043288f1a468e3d2e8390bc2cea626883a007a1c86491a400fa3507d0f41cb53320410e423c801fc681a60f4392a626882a007a192460fa34b3d072d4cc8906320b82d08f2007f1a469afa0e329b91208821944611c34a1ddf475453722411043288c238696fa4a620c4611c3467d0de775d51062308e1a43e8eac83118470d19d57224188c23868cfa3ab29b90220825cc4611c34a7d07115dd5722411043288c2353e8344a6e44822086411c3497d1d514dc8904410c8238692fa4a6e40825c86411c3481ddf494c53722411043288c238696fa0e2e4483118460fc3487544d7224188c23868efa1bc298825c865118470d25f47565314dc8904410ca2308e1a58e2e4482194461183f0d21f494c53722411043208e1a4be8e448220865118460fc3493dc4d720411003288c2307e1a0696fa1bc2b8a6e408220065118460fc340d35f415e53135c8106401002e88c2307e1a069cfa1e8aaea764083202801904a118400ab4775d0f4b22328831a46917a2e8ac8b2aaaa62988320280128460ab6f454cc8902328831a46903b9e9a9d9020864128460124f4b2041502328831a46917a2e8eaea6a9d9020c80a02641904a1182aebd155b22400ca20c691a45e8eaaa764082202641904a11a34b7d35310540100b90e71a45e8ba2aba9991a0480a0064128460f82c0abb53720c89044107f1a3de82f19120465106348d22f4136c8104320902307d1a06943bbe87a6a7a00471003f8d26f4136c8104400c82408c1f46957a59020c6511c418d23481ec795d05e55753d003d0902307d63bbe9a999120e802006411c400fe340d34f43655332241d00400c8238801fc681a6be87a6a6640821c86411c400fe340d30f41cb5332241d004008e2007f1a06987a6a66448219049118471003f8d2340ab5f419c5e166c8104390c92308d2046983bae87a4a764483194478d234abd1743785e1664048c234811a06977a2a6644832046511e348d24773d0de94c410e43248c2349e929882a046511e348d22f45d05e165d5d4e53b2041d02400e5320c92308d2046a57a0b329d9120c80194478d234abd0597555314ec810540101320c923469b7a2e82f0b3a9ca764083a0)) else (if i<6 then (if i<5 then 0x408211a418d2277bd253906408c8234831a46957a0e86f0b329aa66408320080192469003c8d0340b02723dcf4d4e4110640c831a44ef7a19120c81194478d23491def494c418ca23c691a41ee7a6a629d9020c8019047906340d30f73d0de364c8904419003208f20c681a69ee7a1bd6448220c8019047906348d31f43d05e1675394c50b2041d003208d8ba1e929c83194418d2348bd17417859340501074008d37a2a664483194418d23485ddf45d0f41675394d53b2141105400c823055e7a4a620a81194418d2348bd05994e410ca20c691a41b22caa6299a0646818d22f45d05e16653320410fc3209c230811a0681604e0fa1e9a9e8011c418d1ef4322418ca238831a46917a0bd29883194418d23481ec795d06917859d4c52d003f09c23059afa6a629d9020e8019047106340d2cf73d35314ec8504415003208e20c681a69e964083a006413c4611c418d2340ab1f41c655d4e48722411043288c238821a68eefa0b2eaaa6e448220c801944611c410d39f4d4c4188c23868cfa1bceebaa20c4611c3487d0597564188c238821a44e8fa0e22c8aeeaca6e448220c801944611c40f7d16895753921c8904419003208d73a3e8eaaa627391208832006411acf77d353720411003208d03bbe8308b3a9aa6e448220c801944611c410d3df41c4597224188c238801f86947b8eefa1bc2caa62086511846a9d07172241d02400ca2308e2007d73a3e82cea6a9b9120883200641182ac9d1f4165c8904419003288c238801f869a3e1ee3b9e8378ce320bcaaea76448019246902340d44f4b22418ca23c691a38ef7a0bcacaaaa98a620c809184690234d9def454cc8906408ca23c691a51e964082a046511e348d2077bd05e75753b2041d02404c83248c234811a7cef7a2ab644832006511e348d2877bd05e55753b2041d02400c92308d220892046a13bde9644832046411a418d234a1def45575394dc810740901400c92308d2007c1e46a23bea6e4191208839003f8d2677bd05e322419023288f1a46947b89b64082192461183e8d24f4b20418ca23c691a38f87b8ef7a0de2f2aba989a20e80a02469003e8d40f73d35310540c801fc6907bde9a99912086411e400fe348d2df419c5e1645794ec8107400e43248c234811a78eeba1e92cca76446511e348d28777d0f4364c8904414cb20c6943b9e86f0bc2c8af29d90208721924611b5f4378dd36441c831a39e92cca764082a046511e348d2af45d05e3645915cd5b2041d02400e5320c92308d2046a57a0b26ad91204478d2348bd1741785915e53b2041d00390c92308d220892046a37a4b329d912046411a418d234abd1743785e36459322400e43248c234801f0791a85e82c9912046511e348d22f43785794ec81043248c2307d1a5de92cca764083194478d23491ddf436653322 else 0x459c6883b8e4389bc2cca7204469183f8d2df47562307f1a2de82cbaa644811183f8d21f41c8de1665311041500400e62348c1fc69d7a3e86f1b22cca72026511a468d2c771a0de94e408c93208d2007f1a5de8fa1bc6c8b22919c64480990469003f8d39f437a53105401003f2e4398c93208d2007f1a7be8391bc2cca72006a11a400fe34b1dcf454cc8106324ca2348c1fc681361bc20a80200738d19f41c8d954cc8106400ca2348c1fc68136de8fa2a66408320464990469003f8d026d3d25332041901408c93288d2307e1a469a6f0b2a98a6642460f9ef47d05994cc8106405003288d2307d1a6be8344a664083202811926411a400fe350d234f1ddf4d4d53d01404c923c801fc691a63e8391bc2083f8d19f4378d916553d01404c923c801f4698fa1bca9a801ca6491e400fa34a7d0721675354f405013248f2007f1a469a6f0829903e47d35354f40501324801fc691a51bc640820fe348d01879de743d0597565372241106400c82d88c23881f3b8ef3a0bc2cb9120c801944611c410d36779d0f41785972241106400ca2308e20869d6e846906348d16dd164c8c691a28ef6e8838d23457d07477459755c81062308e2086963dbe83a0d22f0af2aea62085d118471036741c459754410922308e204ce8348b2e40821744611c4099d1f41785795753720410c82e0922308a2070ee7a59120c65106348d22f41d05e564595555314c419003e08d93bde8a999120c81194418d234a9def4556c8906400ca20c691a54ef7a0bc6448320465106348d2877bd2c8106328831a46907bde87a1b2a9991208832006411c418d034e3dc773d35332241106400f83288c238831a469e3bbe838caba9aa7640821944611c400f434e7d074774d9164c81062308e2086963bbe86cbaa1744611c410d26747d071364597575394d5311041d02400c82e0b62308e200781aace8fa0bc6c8a4680a064083a006411b1f4956c8320415003f0f83208c205be83a1bc2bcaba98a42085d118471002cd9d071365d51062308e2005933a3e82bcaaa98a4208641744611c400f83c0d02d01ddf41c75308c1f07a1a40e2eae801905c1183e0f034915c410b8230781a30ee308b3a9ca6a9d90208649184690234d3d253105408ca23c691a45e929d9120c6411a418d23491def41d05e1675394cc8107400fc3248d200791a0681695e864483194478d23471def417a53b20418ca23c691a50fa3bde8378bc2cea629591a007e91a408d02cfbd061d4c53b20410c823c831a4696ba1e9646348d16c85031a468964046906348d145eb2041c691a29ee3b9e8338bc2cd9020c801924611a408d38773d2539063288f1a46917a0e86f0bc2c8832024611a408d034c9def454cc8906408ca23c691a51ee6f1ba6c9919063479def416653906400ca23c691a51ee7a5906) else (if i<7 then 0x9003f8d234c3dc7754d404c923c801f46927b8c9a9aa7a0280992479003f8d234c3dcf47553221ee326a6a9e80a02649003f8d234b3dc64d4d53d01404c923c801fc691a61eee40820f90f73d04107f1a468cfa0e46f4b26cca629d911944691e350d234e7d25994ec8104398ca2307f1a53e8391bc2c9ab298a76408820a80201721cc469183f8d48771a0de964d994ec89023208d2007f1a6be86f4b26cca764082a00805c873190469003f8d40773d0de36459148c89023288d2307f1a69bc2c8738d12f4364539022307f1a3de8fa1bc6c8a4644811904e11a400fe34d3d0d994c53106405023288d2307f1a8691a70eefa1b3a028091e400fe348d29f43785915c4107f1a39bc6c8b2a02460f99f41c8d9164573574050123c801fc691a6be86c991a02809003f8d2349378d9164c848c1f31bc6c8b22b8a62083f8d23493d153904414c8234801f86927a2b26caa720882990469003f0d2cde1071a19e8392b26caa7208821fa470d28de110419001f29e86f0bca999120882994469183eb3d072379dd164d51062307f1a51e8392a764082a00805c872170469003f8d38773d07216553322405002e88d2307f1a469cfa1e8393911183f0d1cf41c8de165531043d2e4390ba2348c1f6de8390b329aa7202801704e11a400fe34dbd1f41785954cc8901400ca2348c1f869a7a4a6a9882a006511a460fe350d2ef47d05915d5314c41901400ca2348c1fc6a1a7be9a9aa6222801ca479003f8d234b7d072d4d53d01404801fc691a53e8390b3a9aa7a028091e400fe348d31c81104107f1a28e4208641705a0fe348d21f41c86954ec8106324c82407f1a86983d8ee7a2b26caa629c80a0264120471003f8d3c797d2c81063208e2007f1a49e8ee9b2208471003f8d21f41a4d9754238801fc6917a1b2eac8011c400fe3487d07254ec811041500402e42408e2007f1a75e8fa2b26cca6a9c80a0264120471003f8d234f1dcf41a55332240502324c82408e2007f1a059efa1e86cb9011c400fc3481eef43644d7224008e2007f1a53e86f2a62087a5cc649904811c400fe340b39f41c95936553322405002408e2007f1a059d7a390644809905c11c400fc34abd1f41a55936553320419013208c1fc6a1a71e929aa620c80a0464990471003f8d4348d3af47d0d954c41901404c8238801f8691a6de8fa4a6a9883a0480a006411c400fa34d1ddf41a75354f405013208c1fc691a63e8390821284811e3477d06936553d01404c82307f1a4696fa0d3a9aa6a02641183f8d234a7d0721a75354f405013208c1fc691a63aa20a64128481199f41a75354f405013208c1fc691a59b2e4083a004a120460fe349104250922308c1fc691a43e8391bd29c649944691e350d234b1dcf4378d9164c89013288d2307f1a63e9298821cc651183f8d20de37 else 0x277bd0f4564d994dc8904419013208e20c69d3b9ef7a1b2e44832026411c400fe34c9def43d069365c8904419013208c1fc6a1a469e7b9e834ea6e42658d23483dc69365537213288f1a46927b9e834ea6e426511e348d2477bd0d975641106400fd3208e2059ee34aa6e407e994478d23491def41a4d9722411064008c1fc6967b8d3a9b902087e9903f8d234a3dc69d4c410fe2308f1a46923e9e8ee9b22c99020c478d24f71dcf494cc85043f8c93208d20c691a68deeaa831182c53d05e94cc8505320ba2348d1a05963c8ee7a6a6a9a82a026491e418d23409b4691935354d41d01324831a4681358ee326a6a9a82a026491e400fe348d026d3d069d4cc85042ec811a05937a1e8348c830aa764190a0a6491e418d23409bc7b7d072366c83214148f1a4694fa1b36463441edf41c8de3654133e86f0bc6c990a0a468d20f71dcf4378d9164c8904419013288d23c691a7cef7a1e86f1b22cca7208832026511a468d3a773def4378d9164d0322419013208d20c691a78f23b9e8a999120883204649944691e3409b8793dcf4d4d534c923c831a4681359ee6f2a78d10f71675354d3248f20c691a04d43c8ee6f1909963463df5354d324831a4681341ee6f0838d10793dcde3204148f1a4690fa0e434ca664482a0c649904f8d4348d347b3d0d9322415053209c238831a59e8ee9b26408211c418d21f41a5d5904238831a3de8fa1b329aa720a829904e11c418d234d3d15332241506324c8238831a04d6bbbe86f2a66428220a811926411c418d026e7d0721a6535042e08e204681655e8eaa8211c400b1af47d25354d41105320b82708e2007f1a468167be834ea6a9a83a026411c418d23409b1f41c8d008e20c68ca99a011e3447d069d4d53505404c823c691a04d6fa0e4348b3a9aa6a0e80990478d23409b5d54c82708e202be834ea6a9a82990460fe348d026b340c85042323e868190a0a64138478d23493d064564d954c531053288d2307f1a469a7b9baa9a649183f8d23489dcf71bd593655594d53106404ca2348c1f71e8340c96446411a418d207c9dcf7564d954cce901404c8234801fc69c7baa62026411a400fe348d24f419153320418c93288d2307f1a5cee7b9b226b91204460fe3493dd531013248f1a468f3b9ee392b26cca6a9c80a04469183f8d36773dc6f722404c83288c1f4cee7bca6a9c80a04649904e11a400fe34d9dcf41795936553322405013288d2307e1a469e7b8c86caa7a028099247)))
def ql12 : Nat × Nat × Nat × (Nat → Nat) := (456,7,16,qd12)
def qd13 (i : Nat) : Nat := 0x3417a375aac820c823470d043413bbd2a6c82090064208d06941a08682f4a994d9041a00c847208d0696d564502411a29dde95329b2082401908e411a0d303417a54ca6c820d0064208d06941a09dde9536410680401908e411a0d31e8596a94d9041a010064239046834d7a54c83200d15e8d5a9b208340200c847208d06981a0bd2a6c820d0080321046834a7a54ca6c820d00803211c82341a606821a086821a080ee742ad4c90412008c401a012c00000e855a9922804011888401a012c000000742ad4d91402008c401a01280000000000003a156a6482090046200d240000000000a641118688000000054e802210068a0000000000000000000000000000000000008207dc7ce7c07617537456dd6ab63a62c5cd5bf54e4d44a24314233c435334533732931b3162ae2a92a429f29a23222d22822321e2191ba1b51b01ab1a61a119c19719218d18813212d12812311e11911410f10a0e10dc0d70d20cd0c80c309108c08708207d07807306e06906405f05a05505004b04604103c03703202d02802301e01901400f00a005000e59dd9d91e4dd8dd0de49e09dc9d89d09cc9e45e05dc5d85d45d05cc5c85d81cc1c81c41a596595d9991591a4d64d98d58d90d50da496496099c95c99895899095098c94c9a45645a056059c55c59855855459055058c54c58854859815818c14c18814818414412591d919124d18d10d2492091c91891090c92452051c51851451050c50851810c1081041
def ql13 : Nat × Nat × Nat × (Nat → Nat) := (93,0,12,qd13)
def qh9 (i : Nat) : Nat := 0x200180000010400
def qh10 (i : Nat) : Nat := 0x14c2901918ac00032c00032859a2ec0001841ec42811c3101fc2b82f00005b00000000005aa8b875c0006b88b80680300fc2dc178095adc8c5c981c45902780002440a81e00000000e0354050595f0d9f000033034c0000884180000780000000000029889f037000022c1880003480c80002fc0281540003580000000001b9a200640000001d4074374404001ee81ac17c1b4002cc80f429800c2883042600000000021f01740000cc0729680d02502940002ec00000028027c0004240000000002b00002640c428c0b0001aec00022401c12c2343640902a009c0002581d80c00000000e80002081a03401c00d42140002546e83084c807c58414800049c08c6ec16c0002103511401141f015c1280000980002482000001c9b0d9dc2e43698a81dc1186941f81cc0002280082045e81300859e815813c0f800003c33656c1204112b84081b01401f402c1a40ec30c19c00000004400026c2cc2b466c00036c301eecd600003601680000000380202c02e010d15408001403431440c2842f825c160580000150aec41c2318a433c3240004f00029440b5a6c1000104d827429c2d00d80a000297070c26989c1441951340bc0001105140002704c421c138af01980000002f400034400000031c0e46f41bc6c42c423c2a40542ac1341701a822024c6c035c5a00182381240001e40485b800018c0ac1e8d3c00000006004c05c2182bc2e82c820c0dc3180f02404000b80580000a40005b41801042d41d00011301640240004f699406c0000041082a82d804032042c3380a0b080b01e05010a82e080e05014000102406061604808030900800010480008280400804002604406010d81c12282302010010200024030080c043a0e05014030182802060d9142400
def qh11 (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0x4b84b40000179b00000604024e02ef16e8022e066d0000011507af11a606c704ab04c503a600a00001205c06209b00d01100203010b01909f02206a00600804303d03a01a0060001250000051d412a00310b01702105e00900f01f00400300f0c600002606900100d03500000502510b02300101707000f03800101f0010001bf08e05e01800f00402700100300400105600001b00205f00a0640110340be09210005200001e00204700608c00305300209214c02d01703200003907600301a00910c00700204908f1ec0530650020340b601301c09002e01812e00f00103e06c01f10d0350210110570060ad12600b00700108001605602101207e0030030f501200000902100900002800202a0ea01600706000308e0020010000540a70050b200600700606503103c0760060090a500201708603901700d0260f600006001000001b00300000001e00501300100600102300402600200500502501a00000100300100501f01500100201800d00000700302902500002e00101200000f01d1320000a000500b05f01d00000801f01000000800702c04302401307100506c00600104500200000800205a00c01f03200100f05603f00700000c00700103100600700b00000002c00002f00801e0960061040940020bf0a800c02605d00701407b02700300001300507a02508500000101b00000700000001400300203006203902d01202a00202801e0360030040db00103d00b02400d00401400400200702100f00d06b01500500000602b00300002000300100200b00004600001000b03704b00001b00000c00001601000700701500c02406600f00700d00001400404a00900400803000400900501500501f02000702c00102403300002903400101d00b07600d02800001502201500600900000100004f00300c0060380010b900000900100200800401800002903c02503d05e03802100201400f00a01b02b00800e00403c00701f00103f00600300300302201b00400001700500000f01d00703903600800d01901501400903300001700010800003e00000102e00700b00002104000400401f00201000102208301f00100202800506900a03900900202a0020050090850040eb00200000000000302a0000010010bb03e00000f00000204703202c00007202300500c00500000200d00001400003900400303500002400000900200600000a01601005700c05d00707b00000101b03608902100a01300600006103401100300300000101501700000500000203204c00d00c03900200500000000102601301200000000404300001701b00500400002900800000100200000b00f00b01000200001902401f00100601102803e00100701000202002f01807a01a00200800100000302f01a00301803c00000101c00001201601b002059008026011 else 0x4301a1067c0000006c08a105350000052a00c90000089305ac027912e80492065a000011e800000000012015c60000007904bb006b00b60932053202cb044c00000000042c10250514000013a2050a0000009b07de148000c7000000000432091514a5254110d50539000001de05aa02e607b51718146f000018ca02c00000017800a6017a0231000013e5000004cc00000396011f06cc0192664f00d42799001303d8045c161027960864000000000644079400000839185f094d614e0000080f00180255000000000000000005bc00001764000006a404230000000000a50000068f0200146800000650000015c905dc074806f3069c090b11aa00af01b1172804780000006808c3002f056e009d03b205b403e015a4015708e602cd03ff03aa000000000590061724b3078001ee000012390000000003650022623100000684042a171c15bf002e07251220448a01ba08ad00001475000002e9007a030f079e0025106d052e04e9054215460000467405eb00f611e90657156a171a049b0456000008310000067f000500000000000006f000000671107205290197125b174d0000006205cb055705ee0664031200a0033006e0000000730000051117be18d6080a07bf063f04651062088b0733174101c405510000086300cc08380353000003ceb3ff04b70681008310fb0000b6291471005000000709000000a8104a01e1083b00c1045483fa0000000004c0554108fe144f045a0339171e080e71550000000002b018f30901110200001831000000009682103505040066157105970562059e093a06bc08e805a704ea0680050307cc072300000000002107da079966540730126502070212003701e4851608b81716026e07e7066800160731012119090358075100b76544086c0448059c0481700600000761a49316f2b4ec07f6114800ef001e715914a0001c03d900460000033e023504f7000017e7025e00d60000051b0049000013dc07ec151b078206b606cb0000020a049410d60014000006d905da08d202a8053e089008b3171d023d04e8000002de10420715047a0000040608db05e817570266000000fd000008c603d10464000002ab0000079b07b3061f02df0933000018d805b603360000109f011c02f703f6033a02f20000000012ea016d00000574032016e2090404f5029c05100804000002d6174b05fc10ea0880142001f4186905a1081e0738091a068c046a008600d22616043a16bb087100000110039c000002c50642615304ca000005f0000c000002bb0000004f16ca0592000015c50000002d0000002a04b600000550018b028106d409280420a457066707bc739202ce103d173d000065a4000001760000044d0001000014b301aa01520568176e17270000015e0793013b091e090f02d8011209400497067a006904) else (if i<3 then 0x5908821499048f00000000000002ac08dc009a09101758169d03e402f6086906ee03cb9725182d054d0000178113da000004d803eb035000ae861b01db08fa011b00000000737f025d02b405de853e000010430378052704ee05ec07cf01d39663074c04d1146c06a8176b0133715b1749440000a4065e06c6031d04f90000018323fc07e311dd04ed00000487018e7798854005d704c7016c05a6073903e902a4b450075a01fe677b034807880000a8ee01080721000005e70000091704eb044500000180058506d5638d0911070002f1035f0764019f01d908e2103f047c028305fa08c1053d03ad004e0833006f650016e30538070d15dfb54a080c042b0930072f032105700937043d064f177308ca029a0000182f014d14c903d700000060115d010f10c80401186804900000013100450194145d0000035618f902ee000011a900000000000010e70225030b639d000000dc00a200000000031302930675036a02e100000000091908f4024007b9088706610000000002d76397073200000000000000000138000001410579084e00c3000005ca00000507054700000000174e000007f81493076d024a00000242055e04ef08090000151506df058f0167037a00fa055f00260428176c07d8093b00de08c50000000000720000000003711908028a062c106c18fd05c1081400001421639318f501e7092f000000b40314023a039d765606770707087007c4077e104e058106e90223027c03be073a07c116520000a4ed03c402b800000000094814f108df000000bba4e20000000004a7015c00a104430457000000000310083d051614cb3453044918600728452e093f073e00000000032300000000071e0000073c06af615c00001770144d444416990774066c115105f4062b00bc0300000044bb0254035c276100240737177e0536101b12dd048906f403e201b4148c00000140000006dd24b502fe04820000026c64f804bf06740897251603f903720000065324af0000028e017006f90196051e0000000018b1171406c205cf06d2009008da156e27976826048304cf059b1653027007d7022d04d4047f050911d2147e723d000000000000139e0032016a05c703c8046310dc000010db0778039008ce85430916000006eb01f718be01721088679701cf08cf03fe16b90580085406870147064a0000000006ae175600000415000007b8020400001153000007a401d004dc0000b4c711df069a00be0576069365b0063b0000005b146600e102ca146000940071021611284548000001fc000004420425061014030000168e0311000013fc0000000004a400000000087900000000070303440000018d0000a4650129019d6655007b02691651008a0583000047000000092002710044083404c603a302af01c008ea0000614a0000017709 else 0x32615f14b9000003dd000000000000091303c9065806ec083507e901d100000392052f23f9101a076200000000038e000003d600840000072d000000000000048d034e0118009c04de0000021f0000006707ca037c07eb064600004519000003b90000154b05f618fc00000591087700b0036714500017185c066303a90726120e000014c408b7b40405750484a8ef0000052601ca0000000003ec000006e3000000e2082e00310000126417cb000001a401fd0000019e02ff454c010000000000041f107100d707020801b40307f1051900000755000006b2000000000000053f06fc0162000002d404c90643861907c200001565059f00001045025f0035054b123d08d00000103c0000006444500179020d0000047b0000081108d708190618008700c60000012815e60144448101d7001906f80896027801301563006e110005ab02f3041c003a016e00e31776121f016007aa1811063408ee13e10931023702f8106a000008850874967c279505b30480069d03a2092203080553144c0333125a06071867000000000000047001c8089e0000000008ac04e20435000000d51863143402a604da000000000000000001bb0000145900000000020200000000041200000479000001ab152d851516c50397048a00db000010cf0000107408660000154c1049946e05cc000000000705000003b477ce07c8082907c607e5050200581735058c06ba14270631021073a8144202d902e2b518367c02b6174c00ac08e401c7006d16b6782673a003470243015f050106d60000186b0000254003e1614f077008b615340000000016e900090000000014cd18f80000000002e51647454b068610200000076f0858000000000000014b0000115701c5022a17430354084016c3623d14a10411041665ae01f315c400000450072c010a084501bf556fb54e0468149007fd005584b30860060a07b60000186c05ef000006b8000006280000652805670000a8ed043e73ab074302d001ae653605a8000005964725187204a2070c05f5088308bc05551041102a0000715e00000779000004fd75ae103e003d08ff615915160717051d676d000003c3103905ff00000620074f012ba46d07200000a5940000079d16c202bc000000000000052b12df008db434104f18bf06aa1562049f082b03f7027d03b0000e0023000205bb0491085200000155105708cb148a6006034b013603c700000329556d046700ab0000077606c907ef27980273076308241272022f67c408b4066504fb0691776a0595032c078f102e086b0496021e2547171b058b0867043110e317121423004a05a001e0089a05bf061a000004ac063007e013d801710493000004b40888028b013a092903ee07ff000d0927055c053705e218bb1259083603370000000003ef071a0061146200f806)) else (if i<6 then (if i<5 then 0xdb000003820012086208f805df00001038049906970936a46f04170569554001a80578094905340790152a032d05c8738b03c605be34460623146e085a0825089b00fb08a6038702da00001733010da468034c07ac00ea0195000004a600001470000017440000714f033b04240000036204bc06b1184c0000249e0565000008e7000000810000000000000000034609050000638b0000615703bb0742000006d100000000000002c200f305e3007408c8000010360000020507cd071c615d0556086e02c3085b0000030316bc106b052400000495105e03ca04340000063e02ec18c40028861a03f1000017300000000001dc032400000000000000000000038d00000612064910440000172a04c100000352105a0000614806ac000008f3000014690113000004ce149104f8000000bdb732044a0000000000000000000007db05ce03af0000652a017b07c014ad0000000006f715f505610238037601e3015b003302a519020812079218a9089410da045b04510000000006b500ed093463a403011217018f765501a5340f01f905c304ec000804070676472303cd0000b45d04f405a4094f6151254508eb0000045306f50000029f001007f2037006e701be02eb18c6074e024d074d000000e401b504dd033400060724038614180636055410c1078a182714280865b62800000830087d1906074100000950b4eb0466051a0184032804cb0000084d08060048067d000007ae025963a3056f14c102b50226045e0848094504754485044e0508049e000005b283f1031a000000981771447808d408a8025c07d302ba000004af010c06a3253e04f3164202e7033110d88517104d0000000000ec1268059a000008b500ca014c02aa0656000006c40304173c1402002b03c5000000630921031811b224b1050f02dc056c15d307110765172118c30844028f06ad000008fb006a056d665308100828081f036e08cc14490772185b0735160f088e01f00000037d032f07e81877029d0706146d07bd000007d50000093d148105fe068b046e05a309180213027e14c30224090e614d08dd080715e00000000000000381081b03ba0678049d00000249069605b9024f16c60000070f06d7000004b20850000014ec08ae00001260009905e10710144600000000a4ad77c2063d02c8114c034218ec05fd43f3023ea4b208d60000074605ba090314b10608057d4434146166510319a67000b9067e000000004733147d0208061100c20000004000000332064b639500000000637f06e2017f03cc8616000005b1106300000000040f0175352e466f01a7653110fa05e5078400000292000000e50798152e00000000000003e6043c15ad016b0282050e012d126200ee052115c700910000024710a008e984ae03bc08050287061e085712e72610000003fa08 else 0xe6164800700522079c0000a68102320000014200a30000078904050000b4ea076b0787165000dd094416c7173b080d044f0000164a0000000030b140ad17170868066f06f10000060b00cf02740477106008910000052d000002090000048c7797028500000614187f041a01f201f51560044000f104d5076a07f5120d13d9012401d608760546147300f50206018208030886050b0907054104b8109e0057007c083f07ed146b000000e607960000000017970000156c04d20441103b087a02950220045d0000085d0683054a01a30000075c00000655035513e200000000080b057b0268010900000148025308ef10e900000528063a017d003f092600d8172005c6032706a20906149f008c011a102f104004d704620190094202010085764e07a3148e040315420146715f087e077f18cb04c306380672172f000008e5082308de03c00000000005931696069f06600391000003ed051501e2062417c206a0012c071906e8b45f0808015805dd00000769000004aa00000000115504c40000041903a5125d000010df025005232546141b04e0074a02f4078565e0000003f8022b064d000001da00cd0692107a046f06b4020e07166545094a090a06ce053a03da18d500000000001d13d7062705f9b45e090806dc11580230069904db00000884019902181783089c0000026017c00000025600590688011d05ae004c0000047107e6000002e001c900000652091201630654043b038b0193190703df00000000b52d0559a4c31078082c0000138c01ad011106fb000000000000070b060102fa0899261803730000187300eb05d1000002ae021a000009390802016f057302ad00000000149214a402f9000001bc0000000000004401063905883724000005c4030d0000000015a708a504a103e8852a186a08c715d5164606ef07340000149483fb000003b302bd012a08b100000767007d186104c2084300001009161100a906e4003805c900e8046b07a601b66789a0b3000008410251146302140000036304020000023c67c20875000018cf000008be00000000106507ea0881010207f414bd13f7000001ac13aa04a8061d12d40239066e07a8652d0000000007a5030a028003e3000010270938781e046d0377000018c107b701eb169206de1864014e0783021c05b506e111da06ea025a04ff06bd00b5070111a875440753066a06220756094b0000a4861644000307520637090d000000a7036101c205d9138e04a5172e0712085101e9185e001f0791000701ec060e253d068a462908bb04e5155f009f08c014a808ec04c80747140a073b10e6017e04e107b203bf07a90651068e0341176f853f046c008e00aa07fa0821038300000264085c00bf2235156f08f063ab057f033d0291038c000001b2045815b810fd02be0000036c10ce05) else (if i<7 then 0xfc065f187508c9091f0773043044bd01ea092b05992233022c0056000002a0007723fe18cd0000104c000000000000056b039f092e653b060d0000249d0000165508d901b8081d087c014f06c3050003a4000006fe0075078e037901c605ed01a905580191052c0544000065b1104b041d07dc00000185148d000003510000b733046106a6061b149584af0000015015e165ac06a101d410e2033f0325079a057c0000084b028604b0063c009516a807d6047e0000000f0914652b000000000438187e15c00000100d173a063200000605010e01a0000014330000452d0000000006700000013f13e010000388005112dc05d50277045f944603f416170000109c148218f1073d070404f600d0021514ba08e1013c000007c5084901ff0097000000000082148303bd08c2004705f8000005d30132064e06ed0878173e0349000017360000089200000437100610e408a202450813075b00000036149b081c0513679510cb06b0031c0149088c0000044610d916c8000008ed15c810d7033c00f724ad000000ce01610000107900000000039804e724b2020b08d3103407a00309151404130744105b092c615402c4012200c403ae7780a412000b076c034d44ce0299171f0000173f6158006500001488076802a9064502a21451070817310474179a00001445000000000359138b04d007b1083c1812176a000008c4715a03c1004100d90236031f0302000006350816000004100034089f012e0217075416490000078608aa057703f20000715d1645000004360366051204fc07fb03ab002700b8615e1472003b05a202b90000032b07c3164302d1082d0000000002b2029b0766174a0582077705e407ee12e60000147f06e5000010fe000005ad00000272091b019a0219079f004b0000037e854154e20393051813f8089d041b0000177f17890275062f015307c702520750144b08f714530134144e025707f00615019804fe046915430589000006f2172b145a2544054f01431715066601cb04df042d086f0594092a0096043f0000122301c3000010d0088a06790244148f038919010315081805200571853d090c07f90000076eb481029e0000087201e80000062a44be0531023363a2039e055213f3146a00cb050da61800f4000004a3125f083e0647080002d505af0759149c017302c1084707e4001104551417139306ff0165147c06a7001a0669010316a70600018a15d4055b0856678807cb042673a706c80000079715f40000348f074004f00262052516bd05301030000018c0000015cb0000013d0169000010de00000290181d11c5008007dd021106c510f9087b017c149e00000603171904bd0689094606fd08b904e3084c05a914c802e8071f010708610053082f0447027f0000614c00000000062d053c000002fc0924a61706 else (if i<8 then 0x40000615b037b049c0648000008e00427000010310294000007f3036f06b70000187418c5000004141619000006d80229038000000925022200b1051767610771092d08f9a742072214ee06abb4ce057a64f7121d1410665096e5b44f00000000000018ce035b24b00000000003a765de0000011703570368126900000000060907d900000000034f037407ad17bd000015c208ba058706850000172308150947000003fd003c75b106caa56f0000000002760076000073a906be04ae026d157002b10000000005e9090007df0000065d02fb000000001258077504e6070e0543069408d8000004b500f90000016406620000107704331037040d05c0141a140005f203de071302db069500df06b30000027a13f100006147008f0000028801b90000072e01450000000013fd0338048e0000094e000014c602e401f60586042203d5000004fa0000026f1154018c04a90000000007a70757054846ed05f704000935023b823314bf14b0054508d118bd0228013504f1000007b04518188000e000000104089810dd06fa0227109d01ce17b7030705d0072b1740164fb40244a203d000000817005c028c0563084a0004145201cd047d00000054352d172d1871076065370020000001ed077b082665af1710000011bd10e5000002a7026506a5174f009e0151040a000000004731023f02e302cc1007013905d8013e18cc0000000006f6000006db000007ce088f00150000059d084f122b03a100e901fb00c0045900004549025b078b1026000005b80000069b714a07e208e30444092301fa04ba077a102d053b007f01c1057205d666520000000008f6086a0000071d04290000000002b700007774090208f51409018800f2064000fc021d000004d60000185d000003d2068d0000b675072708cd0000000013e40000060f0418000004f2042e02c9005f0000040c00000092000007810078178008b000d300000000000008a712661830042111e303fc056404cd11ab037f0000060c0106115c000005c2472403750000056000000000777815b203b501f1048b011e0485106e000000b3020f000002bf01d204e406da0029615ab444b4ca0186000015c1038f072a00000698077c0000040b0000000003e7000006d003b70000000007d217750399075f04760000000004080000015a0000252a0000030e01e6179c0853000018250000015d01f80000074b051c0941075e0714000000c807f76396677201190000011485420125038a05bd14b8082a0472016805f108220409088d02210000a233039502460690035a01270000029801b70488000006131774000003160000105d17a2253b02960364053308d504be03a8017401370452104701af050600b20305065b1465000065e1024c03e502cf03450000171100009492026b057e0030007e10 else 0x1216000000000360061900000000067301df000007fe03b105d4024800001238031700000439000013a685460000172c00000000041e015601b3004d00000625156b067b1832000007a2073615ac051f01164480086d000003f305e60105034001540039100c11de02c605b0000065e20000000002a1568103cf367f16ac05cd065c06cd0384036d01e51070145477fc151c012618b503a008550297005a050c08fc15cc00ff08f202d2154a036b02580093012323fd091d162b019c01bd00000718122208730473000000d10000175a00890000063304a0173706410549466c090904ad0000000005f3000003d4061c172904b9016613ab034ab5190385462803d3058e027b102b000008a90000125eb8ec000014ab073f0895039b05ea0000024b10460306056a00000052000000ba13dd6773151a06bb75e20827000004b1015903f0028902f508a4000005c5000000000263039a0000068207ba02dd083a02f0000002edb4560000028d018705400000093c0000054e1641064c0000000001d5066b11e7046007c916e1145e1426000004d907e1853c0000032a06b905fb1498078c000004d301d8003e01894675000000000000000008bd02fd085e000006021738010b08ab0000071b08f124ac06160000a684087f0629085f023407d1001b058d004300000758021b030c173400ad02a3171317cc08b2074901a6372500c5059801a2014a050508af0859176d178705d20000000000005233000005a5020c08a00837084608a3005e035e1742070a120a03db0000000007ab033500f016c90322004207b46149072913a4069e06260795020343fa3483082003ea03c202b300e708bf032e000006a9042f02ea01ef026a062e146714c584b5012f1862058a088900000000077d055d0000000006bf058407be000012e46155137e06cf03ac172200fe049a000a849f031b0369000005b72615054c0000000000000000008800007536093e0000002c18c7153f0000346b0000000000000842019b13a516d607a11422026703dc00da0326005d075d0394040e094c081a000000001763091c035d182307d45491018103b808fd0000060600000486000003fb170113df055a000016ab03f50498176202c7074506c003b6153701cc031e861c07bb02d3010111c407fc0566008b1048000004b3028405e013d601dd103a18f0078d06d307d001b0034306c1024102610621000004))))
def qh12 (i : Nat) : Nat := (if i<8 then (if i<4 then (if i<2 then (if i<1 then 0x801900f014c05e00a047808802404e01a003c00e002003800000002d0078140000047015000000400100102780b4000029801402000300f80c0006079002803800603605702100160130088028006047013007c070001005001c02613800480c80ca013014803c014018003802c09a01703d8008032029001801800600801900340060c800002f400600b0010050030028002808c006005002000c00e0050008008008022044004006c00400000700580c1001801800a00c002014004e0010090038220001023001c04e002032000004a0be041015c000085000003c00802000700040a600d00280340080730008000088097007000005c00202c80140060d3039008400001c009001400c03200082100940000000004064038006003813c006000002c01a0ed05100dc05800e00800bc000010000007800200000300ac002000010002409000503400a401400100000a00260190060030004012005802401e017013000800200a002026801a01a00e809408c016000002801c01f01b010802201b013002800a020002000c000028007812c04a018001010c05000000d80ec00800001400140420030008054018000022814c000045002004000003d00380a0002002000800c0280000000074008007000003011e00000200000e4029002000402200100280900aa01100e00000580080048000104025009001400401200d009406a01a00001dc00800c009002001a03c012805403805e003802800000e01a00780080030000000022003005807001e00b00300741880320178008008001001002001407f00500ac01200f000000001e011009000802201000200d800c000000803405403f026800c00200f059806c058008013803c0240020008018016002024801800002400b802800e004015800c006001005000800a00201800bc01800f001000005400000280a402c04d00a800c000004000813c05000b000000000200e016801000200200f80100180290160008008000006006c00a006000000c004000017005c00000300a007001c00601081a001401d00800a800400200f01a405002c000003000c048047805800a009018000800000802e800c00a00500e800c00602c003012c042006001002c02e00300e8008000004003003c0e2014007000401400a0038000028000004800000002102d005000202100100d800000b0010010006001000801800000100900540dc01f02d00000000290108014004001007803804201000800580040100158000004011000805000002002200080020260048008000058002000800800d0000000002007003800c026043004800400e06f001000002a00f005000002e0260108038070046000002c0de002001010000400d004007c00a004001000407e018011800c0ba02b003002005c0000038000000003 else 0xb0d30070d095c043c000008e3070705c3018b0068000e1d3004eb023b09241026013100e5000000000b7508860aa6044b07081d7800000000000000003503034c0dfe04a8abcb0de81d8500000c17000004d401ff00000000112e0abc0b460000000008ad00000a3309cd000013ca000003ad05cc00001b8b000002e7059f058c0c641b6e00c10000000000000b98000003f50eaa0000424b000019600d2004ec11c503c219ee0c5d00000ea300000e0508c10000a7fd0a30032c02ca049b012c07620bee1ce300001d9508a21d940000011807c000000013800005a00501e003014201700682400180c50068010002049033001801c00f00300e01100da046800000e00000001841160b00520018036015008007400e03901100ac0a800800b800010a02e00c003c01c01000403c803800000a000809200102a80080260420de000c00203f005027c1fe12900e001c090000001830c028000061801805e0090028098002042004008c1ae008001823401c0550000014000016002036c00606b000012001604803503ac00401002e000000604101880d80000b8000006019210b00a0284214000004003800000102280000ac000004825c03a0ca002821801810800400d000812d00900a804c000021813c05403f000003418400300100b402c01e041814813801d04e809008402600500a40de014001801802a00500b005000c004031801802602b00d800802a045005001009a00b048002408a003001000c00800801b80880080d400000f400000f00d800800000200002b400005c010808402600102a808c05202104c80a801000101d007800200f009821c022001001812409c01d038800000e018002046807804400081d436602c001809808200002980300040050198000008141015000406001301a00140ca004021801005c00b0220248000105001000c01000002c008c0200000000008000004002001400006a01300d400a00000f8010000001006008008e00c02800200b002700601a8156001009830002802602a0010002008044800818404202b802001600200180641d600a0010050014002011842802c011000000800000300900f80fa045049001406a000039036c0ca0020178178000017001018800000503b823001e01d007801c0f20201b680e001602e02900540cc07a01d80280080700020000008000008000c00801001d80e000e00e016802c01a03001b8000000005021800800200600182bc00001601080ac00002901e0040024001002800404602e0098288006009005801c02201300c81b0046004039026400005d00901440000f5010015800004b00901b810801203081e402c00700b002000401600b8000008032008001004a00200f0034000001000800804c032002002005800200c00b011e002000807c00e009029012) else (if i<3 then 0xd00001948000004f816ff087f09d6052e12e102921a5d000007650bba0b0c0000085b11d6174949ec0000000001f102bd1b2f036e03a1000000001079000007db013a00950cd90b626691051808ed01b40ba80b7f0d03151c0e0201df108a11d2193e0b8f020c0000072f0d980126024c03d406a70d8c0000049fa4db056c07bc079c08f31e3400000e07ab990d1a051e0580197d0000004810202c86043a0a921c490a069a03000009091ab100000d26000004fbaa9600000c0c093a082110e9047116d50d010c29053862e90000000025b80c950d1d181001ed03d201361315000006431e1e0c080b6a8350000008a90e5d0c9e04b407a8036d0cb302c600300d5502830c5c34d8000004bc026b00001d19ad8f0bb709d223401112a4e000cc055401030e8003b500001d7703240960896f12db0b02183708020a78000000000e43000003c416310ac20be10af21d550000010e1ca21e1102cf0d3f3afd05e906520928076b0a210000001d099011130a371cc70c1806dc0dbf05580de502a91727094d118a047f1cda1e6a00001d810e9c1243049d0d48150000f21364000044bd656503040000199a0c6d009600001ca17912011401e01d430d1f00fa032806060000000011651425000008be0bb00000000007c60bf011211a630bd2039c00000848072a0582068b00000000196f00381b4b0a1d0625085909ba183f1c3e05a50afe000007d01bc9044407fd0000000006a4162c000000000d3d043102680458031e09220c63048f1132000019710e2500000dd100000a991b7308690000080b4bf9173c19141d670540119900000d230cb90d36053d07ab0c1204f300000934067919d1062215551afe05a31150000b0deb0368424409cb03940e8a03d700000e580000000016ca0b34180a055b09020000000000000000012d01900ddd00df0000008800001d920abb0000068217bb041400000a8b16270de708161bea01fa0000021b01190b0508510c700000005b85a6114602231b9706e9000000000da000001d0d000004741b67083b099a03cd00000c04019e08b81b80000063900a460000162e00000e0900001c1c1a9a0a5700000347000000001e7503a802e217ae000035060c7703061a757a46000003f0054b17b5142308b657fa6a3606040000018f19cf15a807cc0510638b058800000b2000000e1c000007f57d130c020000062e04ac0e7821ab130e06f3174b60f2049305470a580c5406e5147e000006c10d8418740661000009830dd439b71ab60dc100000bd914f300000a54059e120c17c015400000000019dc062707ef09f701650de00d380000010905c01741061e0c66126f09f103110000000000008356013f0b1b1c5813454bfa0542017000000456114808220e3115440b0b000007ae0632000007d71b90000047f51b7 else 0xb05a0047c0cb50c0a0bbb0c27000000000a9c03c6754006f41557057202540000083001a50000037f0e2714fd057705140628054501720dc5019c094c0709008711880d5f0a32137f00000153004a00000000013d062d04861cc10d1931860bc549ee078a086602860e3d06810c681a9b3c0e02510e6247f2067d055303df17be253b0c0d790e1ba80aab0a660028042d01ba08ac01280acc02d31dfe1a390a7a00604192000041df00000000196803000da206260d6a65871a860a47025d04a30bed12ab0acb000002310776000002e600ac0e0c0d52070408651ab3145c0d7f04220000058b0000020e00000a0e0ba500761e080be0049800fc07d609a507fe1c7f0aa70000000025b5067b690a077300fb193c0a001a770b1302ab0000039e00000000661206350a03056d1d46045a0e1f000d0caf01800b869b5b152a1cdf026d110d09551e4d072c026a1a6f00c7068c0334029805290d9300000a7700000db501febbfb0147017f1d4e154501e1093c00001c6f00001941638d0000114106b000000cd203620000000017ac0b5a1ba10e87a1d9ad551bb8000006ee1cd0152d0a38759e03d8057a098f03f431481cd805f30a7d0000080d12f1000011450634037801ab19ce11a701db0d650000048907a10bb609af0b47573200e41c55008a04b31c850e8b0000068400000236086b099400f109c70de60d5a19360907000021a9000065a503d00303042a017b06d9044e035c15870157106d05090ca4091d1088063119e36617072307950def6388017602391e10000000000000014302f7070100000ce30b3b15f300000c851c4ab16416ad1823029d47f400000875a7fa0d5b010600000137096100000c7c0ac70000016000000cd80d3913828234000000000e94083f04cd000000000afd0d000e0a00080b830000a9a906940ba606b4000016b30722070f0000000011970c361a8b0000088a0000063c0a8c00000000060d1ca004000a5cb9420cd40000000006c902b506980bdd0e1100cd06e00df105ee21ae023d000009bf1d89000011400b38b9320b4f0c96048c195c0b2860e81c86424d068e1c26005f0000000007520a8a091906f901494b68074805b668e70d7289db083109a711250508b48c1bf809a10d3b1a0216d75c85abfb00000000162a01ae097505b5179f081f018d0b331ba906d0102b4bfb0ad801940e4b1c7b063f0bb900e608a1074712f3638c0482083431960d501d49823301ac185a12aa0b5c19ec4b7e087825a2089a0d86056a1e54002e063b0c760636013479000000019b1e410212b1d80bf109f41d3100000c1b073b022008421c24077e0bc81de802291e32081505d00ca00dfa059500000cec137c000005e70a6500000a5009570e5b0000000002fb056700d600000a9b0c14a7fe0d1300001d140000135)) else (if i<6 then (if i<5 then 0x1e7300db0ae91cba0000000005030cef14a7000004a40785000000001e4c000033b3010002c5000017332237032a00120cee07051e4a0000000072ef190f0d4100001c6b0367059006444844014d05980b100d801cb9bbf90bcd17dd0a61038d1a4c0c01069714ed04be19de04200530093015620e7608500763137a00000219223e000008d40000038c0c7f007d1e3b05c1125e8351034a0c41000002ef1a3e00001c230c3814da0bca00000c060e211e7b000005229ba500000000011e075a1cde01a304130a7b116d0000000007ed04c712481d3d1c8209aa000008770bc413570a4807af02330cba000009c405b802fa76810af61582000011e61e5c07211be21bf20cfa0000046e8afc000001c95c2300000b5e0167115601510a3eb98b0bc20cc6149d347a11283bda0d6317c10de91a61045b1002015d0bc66614121e0000000000c90000000000000144b97f05ff021d823608da07d1000009d702c81c5283551c8d02d200000b3e038801071bb5000002260ccb14a2077d033500001c6e05c500000c2f017d0db40e220092000001840e7700001cc205480904142c041c06f600000a200bfe0d32105dbb6806f108bd136a000012c200007ce2180800000000037401c15c25059604fa030d00001c250737021816de0d6916e2055c0ae00ae71c5c08230232036b05ef06c50000000000001918000008461e700dcf0aea08181aa200001e360000035389dd00000703703e0c4c068f095002160753041809c1ac1806db0c7203490000048e47f7184e06df0e18044502a81e6044ba0d345aaf0df415925c8209a90000000000001d4d025802a0061a00001a420965000009691aa613a307820000066e059209260e3f0eab0000a73201e70000014c000011e20000414300000000000000000ddb0a850ea800000e150b6b091b0000aa230000193414ef85a8039b05e80d8b008e0000000017d3108709ed145b17f500cf00001ccc11dd00560af014cc0000190d11d00b2f0da8207f0000000000000dbb00000302054e068901b808490000b1e00000000001bb834d197c011d073c29e1000000000000823a0c870d2c011b00001d6d05430b93157c06b31e201a98000004960000136703130c2d18e511ca031b00000c37082701b60c470881009e0e680c98057400001aaf05e000000af30e5306770a5d000057f909c8000062af00001a6700000e51067e1b8a0e3400000be80bda18e8000006cb13691287496a00000201000007aa125d033c00f815771b96000000000e1e04a1039908100d7e02f014fc04df1d4b0b2d14dc022b0000823d0b53077109050bab0e64138002f60a49000000001c3002be07441ac6000007fa000000aa0e6b000006880cc206761dd500000000703c020b0161000008d11454095d0784000000001c390000084 else 0x709b442040797000000001e1f026200001c811b1604260443690d0c6900000000155108bc0000043f0a8d1d8f000004ae008f0000172c0ae11b8900001411000006d500000585b7f70e70000007144999000005a2000002ce00000bcb000002b3024425b40df91c051c65000008ea0000000004c912d801f50ac4046f084700ca063d7ca60cb11005002402b614770000060e2c8e06851b4a3505174303900a74007f09cc7393038a0cdf057b00000c8c05dd0000000003eb1bec089e00000e5702d805da07c817ad000017310718185b1be1000000001b190003092f014803080dbe3a870aaa0dd500930a23076604490c791e030d22060b008d005e0e7411c8690f0000037b0ced000047f10101001616d1155007e3152b8971000000000e36122e08700d14000000001c030e2c08cb02bc5be108e6130c02ec48460ca6041f02ad6c6e00a515d514b700001e0f000044b801cd00000d1708af000006410000072600000cf1035409a60e4f042c0871035d06ea09a30029094e00000000123c09d800a80b5b06fb16c50336069e1c51018e0000098a035f01b905a91b9f1c59099700ea14a407910dca0350000006101a73000001e21c67145802bf0291140f00000330079d037d162b0450118b11d8055600490d6e037a00a00b6f14c900a200000b8a00000c1505860dfd0000097b05501226010b0b3c00000a55823b1a3301560000198d00800d4f0a3429e203d5007508790000000006c30b410746081a062f028107b912ee000007bb00001a9e02b800d4000000003b5b1aad0df30b61661506b508e80b0d03a409d00b250e91075e63960ce02afe04d50000000021a80284031a000008b0007b048a160a00000e98090b023e1cb400e009c20d04130a024b00b007dc1a89084c1b9e0a72041d179d182d00000000000009910e400d790271150101c51a59000004bb16dc000000000000034b0b8705fc0c23043d000000002af9000000000b2a0a590000172d08c5023a0b941e230b6c17450c350e8e03ac00d80c5100001857026e01bf0b3f49ed02eb055a06d80828056b00001deb0d89049000000999118300000dc70523186851d0096d048800000b11145103ab01c406710668025f1185032f00000880017400a100000a1905010000159a0b850bc909b242490463000006da1196081c0000137d01bc053ebb7a0dcc000011ae0000150b00001a7c007a05b2008c06bc1afd038201d4088314180b8200000e8d114a09e513ef000000000257015f000000000000089000001ccb11a30e9d000065e4629e0562029c03fb0af40acf0e1302880a76143f07e70369000008400e4407e014cb04e82543004ba97c198e59ee024e00000062000000000730000018110a1e1c10189e0dd81a680b2e03b917b600001943000089e41e495d55a960000) else (if i<7 then 0xb044a019225a80be9190300000c2a00001d3c0adc0348062a01e315580ce525b6047685a4000006ad00329b3c00c018c3000002d16aa9021507930d3e00af17fe07780cc800fd0dba0b48157d0c5e00940b070a140ad006181a2d00000e9700001aaa05bc01d71d2607860e2a03a0101e011244be052d000000000e54126400000c100000083d1af900000b1a0234aac200000a1007ba000000000c8b0a2619d309fb000007c500000500048000000690155d09ec03e709e6024d0ae20c591ce0009909de0e0600001b5a07fb8c820000033b000015e601f81170119400001139115e1d76059d000008fb030e14d81b95080a0d4415d90000119c09631bda652f00000bd11c20036104c00000603d07cb135c119001691512169800001c54000008740c5600000000603a02e003d604c10d8e08c60bde090005750ab711581aa500001e5f000000b101a616fa089c119e09f200000dae09b0160707331d7412df021e1cd9034004671c2a000008670000050a042f1c770a3b03cb21a20e3a9ba41c8b6c34067f04bd0ca1077213470a820962b4b90000b24e04811bb118c601540a5e08ab0be409ce00a406570c480e190bfa0d56061d06e1253c19d0024115d802f20000000000003abc069d01020000000017d10a310e7304f11cbb0b7805eca4f400001a5304f200ed0d5e0ea405780a7f3aba03a60c190d9a190b0986122b07ec1ac003de0206098d04d6150a00004840087b1b9a0000033a0659021f0b0602b90237139400350e2905d2118f172a02c71564074f084a0cad049204e516f407ce068342476228022d0dce0a2f075f00ab0bf2059c07241dea00040a9d13680d7ba5df14810e160e5225a9001001ef08c70b14187c07a41a5c0c3c066a0b09183b177e025a0564006a056007891b650cf4020505e301ad1818739504191966046901a905d1158c0c1f03f60a8f100c1d400b660811065c122a140d0ad906bf016f0a670b8403bd02a50c750ac3116c0dda051305b302f50e3909ea00000cd50000081e000006a51a3a0b880b4e0457090800000c6b06c41ab70c43107c18c50000097c0bb80d87082d0000036a62ee1a991111112a000015460ab40000000003bb08a7000002100db60b400c8f184d06b90a240000127403b009390aa8000004170648083c02aa00000d3c000000000b49115500001acb021701661cc51c3d078c113a04a71bf089e204e30000000014e100000e8821630ae40312000000001b2e0ea61c1d1cdb07320000000000000000086c00000000253f00000d4503c002ff0bf915180000000007d90d6c023c17530000000000000000000000000246040d000002d407390e7b00a70000114e03e30000000000000000034f0000178800000b161d7f0055000000000c8313e3000005f607b25bf0045c011a0000092 else 0x7000016cf85a10473095f000001be027e000000000ae6395d0b8c183001de06c807ac03b10bf304bf078013770e9b0c4f0b210df000000a2706991560056801fc035500ef00000000000041b405ab00000692000016231d3b085a0a8e1d710000083e69d600000775035202e40c58000009db08db07270aad03f20e55002a1967082c01e509c30911161300000a3f186d1a4e050b19300000058a01c608cf0519000000000000000f03e20aec000000000b290bac1d6b0dc00bef484300000e086ca45cd109b9077a00001a9d061f76910c8803760d0b0d9d0e6c040c066d00ad0c1e159e000025ad49ef03ce0533010500000d74029f1313003717871a6200000000026f1de91cb229e00000223f000000b50b6d074ba50f07f80e6e16210cb400000b4a60e20a0509460ea5066c0000064f042b005a090f0000424e0d020de306fc55ad037e09e70b630073175a046c00000dea823f032909840000000004e610b208cc3a6d09030e1009b517fd000003450a970000344fbb7e12a1041b000008d6603b0000000006f800000b7a0000000007110b790000000019090000000005ed000006ce150d035b1162000001c0000018ca0b9e011606bb00000b0fa3b60504072502a10933000000000a6909870000098501682973029e1d2d0860aa70128515d31ccd000001b20c9905b409c915290c0f15ae161b0031057e0af50783002d154900001be908e918780dde0342050216a902a612e905e5000009df04ee137e000004831cbc006503911533296f0cf9090c10561e4409ee1c7025ae046b1c0889e309dc10860c9b0000065e00000000074a0a940000096f0da5141616c600000b74114c0d49159b00001be719616aa81b6c058470ed05911d370dc814df1bee073a0bad11cb0e9f0ae8acbd0da61aa815b102891752038300000000000005dc08f71e3c136b048b031700001bf500000077000000001b880270001f05211b790bfb000000000bd60dd6000006d700911a06078f0863000007a70000027b0000000008b908eb0000000005461d4a0cc5095a05320e461cab0a3d064a17f400260a4119b70455054a1b980e140ce41a8502b700000da304840c90131901641e72075c17b400b701950941153819390d3a151e514c03ee3ba6b9471d8a000005060bc706f5071c10e30bf407e200001be455ae194b045144a00552350208840aeb0e5f0d21015b0e920e6a060f032e145a0b2b02851a8d2c8104d21a6b0a280d7009380d310ca3085608ca04703ba4150c12254b7d1b3c0000b20416c81bab08d2173807590e861d6805c81d441c3f1c000ce804cb9ba6bb7908f5639303d34d1801ee02d94bfc0bd00570070a099c1ba3017e000000000c8d484702d700000c57080417d9000007690ac61cdc000a1543061b0e011abf002200850000137))) else (if i<12 then (if i<10 then (if i<9 then 0x800000459098900f0000000000000000008451344b18200001d720b96108b1c4d197e0bfd148918f10c49000017290000150f06ca063314ec17b3035e075804f00000000003be064c0e03077b55aa1ded022c04230e1a085701cc0cf3144d15aa000002740a130043030c0a4e090a000005f710210301166b000004c418160000094906fe0247000000001ab4000001420ac508e70000198f1696000001791aa110b411b8aa15550f032d006700000ab603aa0d0e096c1a7e000005ba0ad1093705fb03e90c090b5709670e83000016b401850d58026919b20601193b1bac000012f20e67093b17550000092a0ab203511ab50cb20a1f0720199b0953115f03a70000004f0954000011440a18156a03440a5f07e4020f0000000009f809eb01820629151d11d90b4b639200000e37066f0e95002109ca0000123a03fe00bb00004b7c15e005cf2afc0cc408e111470000058f1c9f0a81031d097e00001a9f003c065302a7007105b700691076069f000006a31b3600000d7610b3638e009d16c203a30c6e00000d430b370aaf088d0a905d8f00005ab800000b1c0897a5ab108922400da900000ace0230000004b8030500001e210db100000bae025004850992000000001388000000000995a74a6c720a9f187d044f06c0000000000743000000000d4b1bd500007614027700001c2700000d4700000e81162201eb8c8a12fb0a790000000006de0c4b00000756037c08de0123061613910000119d05f40dc20000080913ed0d5907e64ace02760a8709060a680000000018611c5002730d4e046104400ba1019908bf5c9402140a9525b714a3000015f71ca31c1900003b24173600000c3910b600000be7028e0a5a061416190000016d03c704d90b510ad3000613e1000009710aa9000014c7000002351b6a1e511a3d0000000016000e5c0c0e006d134602e819cd030a05970ca701f217fa03c90ccaa19808f209dd0c890a93014e39e2154e1e554b7003e502c11df71d2c25441e53061c02f40cf7018c0000038b08a4079b028201f644361c6904680cf2051c0000084f015a1a8e0000115d0c111e120d0c0380184b08d001930eac02870d600cf6000002ea00bd03ff026316c71849aa830ab50000042701c30d0d09ab01980b5207b40c300a6a0c1c089f0000092e02960a391e1a02dd0b6800009ad216240ddfb113009b03c5010405870dd21149075406d40b5f031505f90517081703210000073508431e6906a8000001291a050cf8062b0b0e15811d931c5da47d0bdc52730a621c010c240d0a05340ce7a98f11b2040f0aef00fe09400d0f6908000c044d18fa195f06ae025e12ea06cc0000053a03e4175415ad659d0000000008fe09d914c82c3d08f80c860000091f0c670e2805120052034e78e71be800000000076f0000acd104e00df else 0xe03cf296e0e0e0000006c0932073409810a8904dc60f109e10aa300000370000002430dbd07b8089100001476011c01250c6517b200001b1b04f70d71a6fe0b6e1ac201f70d95000085aa09ac1131a50b03920bd40a9a0465000001d00294098c07e8018903090a4343621e631e5e05a7005d0a0a024907d30af9150515a603ed1c8c0460083a09b80bbc05f80d1808fd055e1c2e036f0108145d0a8816f11c890c45010c1baa09d517f60cbb03b4013003930ad503ca02040c0b0a4b03a21b3f007405c609cf598f09430ba21229052f06171c116cba066299b70b9506a6055104a20bcc0307060005261e4708c475a50ce100000d6d0290009f82030673ae320d6114d000f3000000000825184c0e2f0000042e01830af8074504ba00001e3900001d4c05b0448c1e1809c0017c000005c9000016ab05b10c9a11d10cd39506093f25a61c93000081ac421e168706cf0000b9eb0a25014b0ead000009fd0af7010d1a951d01000002240c1a12ed1c83069a02672351034115d4000006c71aee000000000000153603a516d40b300207050702ed1d360cb012650892181900000a0814488c3c000000000a7c0b5d3a1f0a4f156802de11b75d6800bf1ab0072d0bf67577163206e41171790c0c250cc1017a0a0d02450966089419001b84a75606501b2d0cea138c08d70d4004db1a608af91cc31672b99901210de11542000000001814076a0000235507611d900c800000155e13840a4c1e1415a2151300700e63087a102500000323075512050079022104e206b709120b3d06ff016b0053000002c30b151c2807be6558115902ee0e30424860f0000085ae07a20e1d000000000e69012713810000155314f41b05051600000209bace0411018819330964151b0b970be502801ce50dcb107b15d60a4aac830536a27300000691029a036500c40cdb000008a51a6e0d8200000a110000118907a0159907da0000077700000e5e000001a108ec00001a383b3c00000a9e0daa04350d5d1ba209180046026600000cbf0c7e172805e434fd11a9019607d500ff00000adb0ae306b106bd0d4a0434153e004d032000000000157b04aa0000049700001d86002c09140d1e0000000005cb000013a911dc0000078e006e156b000000000da10a350ca20000119a001b11b907b70e41738f0712051b000000000c2001f0025c000008b305eb02f9000000000a3c000002ae12c8011f000012f40cf505de19cc0b8900000b7b00f608cd1227050500000e3b04030c6f06381d2f06b614e805d601b704d70ab000000baf0c5f1502019f1565056105ad01e90039000013400885761700000a71064b001101e411e70b03000000000cae000000000a420c4d0aa20478099615370260069569091aef0000253d8c8e107a02a30cc3198c00000a8005e105650000b12) else (if i<11 then 0xf09d30360085519a804660000084d62840dc90b010979089b9abb1bfb17441a0005be01620d8504c303891d25000019111c140ad244bc04946c800aff1c1705ca0c60066400000a60154814e7007c00000a8602e16aa71c370872070e038f000000000c9303c8153d099808a3000004080000b36205390000003415ab0000000089df16f900a31c22178604d81a93028c071a05ce00b365200aa41b87012e03ef00001583000008330afb0d990000051f182107ea08010b4209290000210d1aae0b8b08f4a34e09bb0000004000001a6907400b081e37000016dd16c0096e5bfb002f000016d60bff079a0e7d005000000000095900000a0900c61b6b1c8a038606b800000be61c2d0000060c1d800d9400a61b1a00000b1d01b0183c1e04161d154f08a814a5073f010f03cc05aa00f50e2b00000b3500170000018600e90d961c0f02b4112411980d4c0d8a0cde07f70ddc0a6e024015d105db04f40dd714320bec186e05ac02c925410000603e022f000004e400000ea70000054f16010d0514f70000000000000b9a0dc3000006e6071b18bc0a6c064200000515076e11da059909f90d6b0c610b8d092004520bb2053b690004b0a9350ca5071608a60000141a0a70060211cf059b093562ef107d1c34000000000000126b39a61b4d1a6673920000072900001a880000134d18580a160e2419b900000e7a00000b2207e100001a7b041510ee00000db90405000012d0000008030df6ac84000018500a1500000c9100001c1a041e112f03bc0a4d048d0ba0000000000b72abab06460add000006e20000086214f000001956004503721d91174a0da7121c223b079f160e0d7800a906d3000000000b1f06d2082f5e32000002bb02cb05bf05d80e3201d10b3100001e0e0000062c0d11012b1c1e1c3c100900000000000000f700000b800b2c085300001a01000012ca1bb7834000000adf09ff05ae094a8238042517fc1bc7005403330b17a7f808b4142904b609e304c602fc015c150e0bb51187095606091ab90c3b02b1000016710d2800d211100e2008a055a2046d12210ad600000d150ea203b201b30a0c06701e3a00000000089d04380000147d09fa05280c9700000b642542021a0a641d3a0b9c0000000000de000009da00000a1b8237076d00d108ff07de00591c7a06aa17af34540aa0055f000014b20000000001fd07648240073806a002df17bc1aa40b7c0e4217560000000006fa049e01c80aa500000b9900970cb6823e097d0bb306a102e5081307ad54f457530000000009c5547d14ff09b604c203f3021303bf00000e590a832afd104e223d079003710cc7143e14241e42110f05660ac008580c7d0c22017789e112b01a030000195d154103ae0e4e0b8e003e1742173e042114ee0e6600001ac90b9f00090000000002a29c0 else 0x21ac3087e0000172eb4be0cbc6d13102d02fd002303270000a75304ed0daf069300001d8300001e38015000000675000000001bad0a511a570717000009420064085f0000000000868235168507bd083904fe55a900000000000001bd0000093d156c173d05f01d7e9b9f000000000cd7abe11e6700007cf10b44000018331263b9ee12f5140900000000000012f00000000011950cd60b180dc6050f08b2603c0b7106190bcf1d8e00000138088e000008dd1b74119305630d6207b3000005d315190000019a0359000000001b0810080439122f000005bd0d9b02af02a409f506ba073d000000000d0804cf0000087d0001157a0025071d000012280000008210220d91424c05e2088b05d70a400abe05830dbc0dab000004a07cf4194900001c210000211a0ce60000a14c0d2b00b9039d000015da19460dff11c919731138155c08ee078d00f4bb7b0000001a21ad11c1000002cd0314000003f707e94d2c0000162801a209a01935000009d4000000000b000000005c0b900c942c820e6f19fa0bbe0000000000001e0b08efbafa0dec000007d206ec0000072b0bd719010b3208b507c106dd055d06d605e6095b0e9001a8029b1160195b08050d66834c0000000009ad147907603a3107f3047906b215f9031f050c195904a60bd500000e840e4803fd000081ad00000ba909931bf16a41000009580aca1c0a000015e70bc10a120a0f03af186000001d87a4d30000000013420de41d48ae31049a0ae506a2122c00006239638f000003b7057901350abd739404fc138d4e4810b50e170aed0c6ca7fc0e8f054400b2067a0e4701a71d1507b113dd04530d8d0c05a93d00891b8d0696073107df020000008af8086a00150549000004de000002d6000000000b0400000bbf6ce23bf7060713a7000000b81746027c0000029509100e1b18391ccf0000091e0000015e0b5503ba000009bc0bea0e3c09ef01b1035802e9092d187101730e820000031600000000000000000b700b8100000b1e00003bc40824000016fe1d8b063a1c1311a207dd08ba14a112e700981c5b0000091606f055df25a703c30b920000079208c902020bfc14411d520ab300000605000011af6eab19e400e805a8013200000889056e00000000a4ac00001df90968086f09fc0d9c0ada16b2ab7108c2085e0e710078057d06491bb0000012d116d30d37043e00001122160c03dc0c42066b074c03ec00001a820d1c077c04ff0c0300070e7e04f50893000003ea0639050e062311a803878c810d2d02ba0b4c0395094565c306ed000004c5047b11a600000000000002da01f40000000014cd06a904b2158a0442193d0a2209360bb403b60a7e086e4afa08f9000002f1034306870000011504b7062114a8058eb9e901100873047500ec01f9015900000b43082900001c5)) else (if i<14 then (if i<13 then 0x69e500000a2e03f90000103b00000000052baa92012205f208df02ac00e769ca0b230000111b1a47083701e80ded0b3916250d7c1d0b068d01aabd181ac1072e04cc033805fe0ccd0ca90ea90e61b7f20d9200130c53050d1b69071f026c05c20613088c000000610c920253067c0c6200001d241cca0da4066300000a019abc00000a2b00000000027d00000158153f000007d8186c01ec000015a018bf0000b1431366057c00000e8511a51e580d53008b0000000004b947f30a0401a01a210c4e0000114d013e0e750e230593000015110208a7190278180facd50000194401630d5c790a00001a7901d80d730c1300000cd000000686186307c2a5a900000807041606c60d2f011715fc02c2000015971e0c088f07006c9b834f0433047e0db218516c960000120217c71a370ac90c3215a400c203730cb7110a0e0f0000145e00001348000063890674038500000976000056280794000000000d68053c3a0300bc04950b671670575600000000000006f71d8d008108f010b7070c13654b38099d424301e600000d29028b0000183e010a0e6001c70608103d09ae00eb1108054c00c800ce080c00001a87096a0000000017f700001b750cbe1c4f0462157e03370901074908440000000009c6000009be117b0000000015db009a0bd3142714c485a20364019114fb000000330d810e8c1bfd09b70d07065f0339089801da0aa109b10b7d094708320dcd8afb0ab1040e000008d81d7a029325a5090e03da07980cdc09170c711ba00cb81a7d0bbd0e4900000a6300000000071902970d2a01af08c3078700000afc835400000c3e06240dd9000000000000000001550d751b8100000000297207f606ac0000064e023f0000157800b407100e93098005250a290000097409a2190c00000b9d093e0b6500001be601c20988000000000175100d44ab0a2d09701c091bef0000076800001aac07570b1203b3027509e80cce00000000000013850c7b0951047d09d100002356080f01cb11e5571907a307a50c9f07741e4302270000085c1cdd057f0cfc0511128b1693014114a0120e13090140000019d417d7000009250bc000000bce082a0000091302f307c4113b14db603908ae00ee0b5605550aac06af1e5d3b291d82013b25af075d221c00001919181200000e0b099e00000000000002dc079e069b0000153400000cc900001bfa02d00000056f0c4a0e500741077f0be300dc0000000006660000040a1a9103970dfb639103e00000118606ef07f90d9e0d160000058d077915dc1b7c06e70000127111ba00361cc803d905d4031000000e7970e860ee000007bf17890a53000000001cd7000000000ea1000000140e7f0de2057100000a9104b500000000000018ec000003320319161203fc000007c900001c530b3606450000074 else 0xe0a17aa3f197807a6080e00be1bb601ca140e1c1f1d1f0c2b0c52028daac504120bf5033e091516bd0c3f088811b000190b6000000cac17981c4600000c9d0cbd14a9035a043000000dac07150ce9194c0b9b66130dd019b614ce00000c460e5600001b680d670000000000000000090d152c1b3b00001aa01e82166f0242094b01ea00003ab507361a650000162906c20bc3096b000001d200d700000e6d00000b6900ba018100c3036c04d1071e000005df00001758000000001a14000000510cff131804a9030f000000720dee05ea000000000c0700001615166d0d1b05a10ade07b6000008b79bda00003c26098b0c34064d016a000508aa00001aa3094808e500000000000018151360040204c81c410272000000001c1b000005810000ad68000012fd0e38000005200cda047a18ff0c5a031c1c360379089900000000007e2540122d00000000045f111c0a560265027f0410032511840df200000d9f049c033d07cf03631b5b70e21180835306f2032205f5002b039a0a1a0812114b07f20000013c0000084e9b95739008f647f60a840e0005370838031806540000000004540d3507516394092c078110810973149e424a0000343a000009e41c480db3135200000d25055702c400d016b101fb17ab04e11d6e0377149c05730819161013100429047716e10057000073961836080603fa01ce0000bb7c0000000000001c15196a082e000004fd1a8c11a401110aee0d42166c036602550ad717261be50882000002b007ee001c1bc414d70ac11c0e097f76150c260ea009441bd9022a0d6408d900000042141000000ab908dcbb7d1be30000041a045e00000c7400004947052a07d4062001d9009c034d07ff04dd099b000000000b450ca8051d039812e50e2e00000000000000da00000000000022390000037500000000095e152e0a73117f00000ccc061104060594000000000000000000000aba0cd111de07c00000053f0caa092b00d300000702034606150b761df80c000b4d0000075008fa06ab1d7902e30d3303f11cd60d4d000018280197574a8c3d00001a040118018a0b5000001b9b153a0d060c3d025b00000c4414a6058900007612020d0000000001a4234e0000130b0e350a5b0c8103571d47000017320a2a0000162d104d030b0d270c2ca1888afe01450df500000bf80000080006560e7c18d1061205a4019d0ceb0d88032b00001d2a0bd80000086d000001520d240a980e89006604ef07f111e0000016da033f0c5b1a9419ed49700083b9ea02d50d83099f0ba7074d00000000000008bb00000000142e0cf0000069020c78039f19d205af00b6086108350020000002480c8a6c5d65f1059a000000000b580cab0000003b144c1521194a000006e3022200000381000000000826000019631b1807eb01b50660000) else (if i<15 then 0x7065d0041001e03e885a303dd1030154705761beb0d540ba300000b24000000000203044608081d380e720178000015a7000000f90ab8055900cb04ca15e903b80d100228000007fc05240d510c7a03560d570a440cc000000db7000089dc05a60c3a04321bb40d7757fd027907f000000728081b00001bbf1be0065b0d97068a014f01130beb0baa19e0000013921c5615dd02990c21004e1d8c0d2e000008140abf0000000013db738a1e4f0c400bdf0c550000897000580630790d0c6a04da091a10030ac80a07000016df0ad400e30e2d1e28014a0c50821c0680067809e9094f3aa907cd00001b31020a0d46013300e16a4604ce1bcb00000ba401870e9a14f5000001dc053109a889e00000000008681b990000044c022e0000009000d507c30b770c7309fe000000000c9c09bd0c3101460c820db8182514c50cfd0424065505d50448235402591343a9ee1bb3000018e6046a0000498b09f00b7e09f60afa110912ce09a45bcb0db01082000044bb0000144000000e9914eb18c412c413830d6f1393000019fd12300472079609f306030e65003a00001a64052c0ccf0c840bb169100b59054d004400001a801a36085d1262000005c72c3e15860e0d235200ae04f600005ac5002719e91c07039621af0000012005f11c16070b15351b6d06eb0a1c178a0000128913a5052709e202520a3600000b7304471aa708520c16076c02c01b060b3a00dd0a451b820651074e00000cdd08ce1e570b1900000b0a091c1c2b42341bae00004242054100180535104f08760000a1d00a9605d90e4d07700491122485a7ac2309723a120000021102f808e22c871c2c07b00e4a0d091e6b02b21d35038401d309520cfe1d880256060a0864082b08200c33083629e40000028a07c70000497f0000000257fe0000023800000e4c08fc07f409e00000066700000ce29bc4a1a91d8400000dc40e9600000b26012f0047021c004c151a00000000063e44b70af100000000040b07130923006306471d33000000001ac80000006b0000000004d0116f000029dc087c03e1000004990000000000000a6f16afa7f9000004ad00001b30000014ea16ae0000051a14e9003d1b170000043b000000001b1500000e5a0e3e7c5304ea0000000085a906be0124000000d9016e1c8e0d7a11570aae0000026108c01e2408870a2c1b9d00000d120dd306e8000059d3006f155b00000dad11d40cfb3ad20d9004af0000000001dd0df80854149f04e9043607e50331075b06fd000001710896008402fe0000097805cd1bff197a0000b1df0895000016f0000019620569000000000407000007a956fe000014d403db05bb06720c1d05c418800706027a03a91a9c148d0acd1c8800000d7d00000a75000005b904a503f80a5204f9024a0c8e19690b541a7a0bf7187a0c2 else 0x186b02db0139042803d11574000004640000424506cd10e81ac415a51b5600000bdb1c0621b0081d07881e660799000007b50be20437000000000a0215220000000000000000000005fd43ae0b270d8f08d51349078b03e600009afd02640000173f04410000016c04040e33012a1b4300000e9e08410000191609b3000005fa0401000017401453073e0000000000000a0b140719ff000019970e12444901cf000008e0000000e2069c000007ca1cc900001b6603c11bed00000e2600000a6d08f11dfd100e108304e70e4517bd10041c12183d045d098e0c2803261b640b9104b1110e076700001683024f0a3a06650dfc1c2901f389de6ce1194d038e098208c81a8a08e40a6b04ab097a1a74093100000e040000064017bf02cc1d4f065a06d101d506690225155a125f063704870921000014e600001d7001d6124a028f040900c504d308d3003f15760658151608b1170a1c5a2c8514fe000023531260097))))
def qh13 (i : Nat) : Nat := (if i<1 then 0x4082300000a408f811a35f000062c00019e000054048404e05b80001381a30b1000000008e07280006660001b206c458210305286ec0f01610dd01ba9a60001dc85a438613c00001542924a200002e20d0100085070040c000194800025c16c15f8b481d000000006cc00002c045000000116a000090c6c200014e06880000000120004000000150000001823b0000b785ca08c00003c400014004a8a6028a04d01781a847856603289a859e0fe0b283e80e00fc09c008c3320710b3038c40601415a8e8c04c442b241a343700000000804000202000036800029a128835c00009f00003bc27e17507484ec6aa01000000ac1c000705585640861390b000000002f01a8800000014f00003cd81021502780001202dc00002900c60e402c83380260480df05fc052188148892052a0851c6848832415b1b5d3a034223d03f0e880be12c1db006469600005189d833600000004382342c409480684f417c0d400000c019a42401146360000738d65e2a00000000006b475200005d814c15703f80002b0d170b8822000018905e81004be0cb08b00006741aa0340c6195a31a0458a3c08c18306a80006f23350095240000000000041c34a0b509b0d8010025c574002800018d09b832801e00d000041430e0320db025c00032d1aebab41921741990ba02840df0e30a6c6260000000a2801216e084a5341a82d30140144182016000031823c0eb09280b824c2630a58c2017811911d000035c133029800069e27d000064471600000000000003ad0a2001032020809a82bc52e094000046c29800007103b40621200d581741a404a0002a405e40b0000028800153a03205741ee15f06201b429c2ce0808a7c1e000001380003580deba68af007608703906182d005e0000d485fa07302585f42383ac000027800014a075060819011323400001a20fd000018803e000061015877609a0ce0ee21440e105402cc2c805c0af0000130044198000022a32f034810800031603e00015a61a000004a800013a05006c0000368000069c52000047382c4256156033041813b04f016856892a16d04c800054e0ff0d9015d67436a000054855e1790a305506f614303b83d400018e85084c400013d10c05a837817a05b06982e0000030888c2ce1bd018043c2b82ad0918cd826812706d83647220f871800005180b40ca033c1723750000f4e4ce000071c0350000d000040200b0103f0140f020281ec4401060154702485106c4603c110142f2805a00c38154000541f0141a0600e0782a040201286604c0c00c0f09c000380003c0604c020480402c0e0a809088280280020000004070000b01801000000000102c0d018000600100c1400400000040ac2e0000100404008090001005011050050201b0200b0084800c0108839030150000a12400018070140000001 else 0x55101d832c0d304d800058c0001228b8c1802cc18001e804201b00002a400010b00023d84e80670418000ad419f17382b90a017301a045018a018063800012608602c08c056608406b000094224e02d808832e2890000a0c76a1410b181ac0a800e004000c00003905681b1a2a17b2278a8822201e1188a644f80380a980dce6d4a2090891808e00504486740000d80004d480a009202480942503151ab00082e40ec70400001860000c501d004000006e0000000244089071021812f01f0d70562b7b0bc08fc3720bf0290d7810401108686102d60000db88140740002b482c802a25d1c80e7c22e0000a88420000377000070800007b00003e46760be05d0b5012c18c07d8d50326124123870414204c132833468c18119c800035a00004880000fa00000000005f80001c7000000003309f06141580000c7823c38a0d007b000110a03c0e380000000ee08f8a1c5e800b17d81d45421b400003d000000000004745fe0aa0000398432c3000006fc28e00000006bc00001d000066000000000002040001a900b80182fc0f203c80fc40826909905349480bb01e810414e0350ca816836a0360aa8a3434822d082000019817725181bc0000001758374000c9e09686002de01c098000022030b015)
def qLev : Nat → Nat × Nat × Nat × (Nat → Nat)
  | 8 => ql8
  | 9 => ql9
  | 10 => ql10
  | 11 => ql11
  | 12 => ql12
  | 13 => ql13
  | _ => (0,0,0,fun _ => 0)
def qIdx : Nat → Nat → Option (Nat × Nat)
  | 9 => cLook 2 10 4 3 4 qh9
  | 10 => cLook 66 380 9 8 4 qh10
  | 11 => cLook 658 4043 12 12 4 qh11
  | 12 => cLook 1132 6937 13 12 4 qh12
  | 13 => cLook 134 812 10 9 4 qh13
  | _ => fun _ => none
def cRec (k i : Nat) : Nat × Nat :=
  let L := qLev k
  let x := packedAt L.2.2.2 (i*(L.2.1+12)) (L.2.1+12)
  (x &&& ((1 <<< L.2.1)-1), x >>> L.2.1)
def cStep (st : Nat × List Decor × List Decor) (gi mv : Nat) : Nat × List Decor × List Decor :=
  let op := mv &&& 3
  let ia := (mv >>> 2) &&& 15
  let ib := (mv >>> 6) &&& 15
  let ka := (mv >>> 10) &&& 1 == 1
  let kb := (mv >>> 11) &&& 1 == 1
  let a := st.2.1.getD ia defaultDecor
  let b := st.2.1.getD ib defaultDecor
  let z := codeDecor op a b
  (st.1 ||| ((ia ||| (ib <<< 4) ||| (op <<< 8)) <<< (10*gi)), st.2.1 ++ [z], z :: opKeep (op==2) ka kb a b st.2.2)
def cRoot : List Decor := decodeBank 1 0x140 (wiresOf dead)
def cGo : Nat → Nat → Nat → Nat × List Decor × List Decor
  | 0, _, _ => (0x140, cRoot, cRoot)
  | f+1, k, i => cStep (cGo f (k+1) (cRec k i).1) (14-k) (cRec k i).2
def cNode (k i : Nat) := cGo (14-k) k i
def cState (k i : Nat) : List Sig := (cNode k i).2.2.map Prod.fst
def cLinked (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (qLev k).1 then none else
    (dead.autos[pair.2]?).map fun perm => (cState k pair.1).map (movedWord (perm.map swapRows).reverse)
def cRules (k i : Nat) : List BoundPool :=
  let L := qLev k
  let base := L.1*(L.2.1+12)
  let pos := base+L.1*L.2.2.1+packedAt L.2.2.2 (base+i*L.2.2.1) L.2.2.1
  let nr := packedAt L.2.2.2 pos 5
  (getPairs L.2.2.2 7 (15-k) nr (pos+5)).filterMap (fun (a,b) => buildRule dead (cNode k i).1 (15-k) (cNode k i).2.1 a b)
def cContext (k i : Nat) : NodeContext :=
  ((k,(cNode k i).2.2.length,(cNode k i).2.2,preCov (cNode k i).2.2,cRules k i,
    fun tag => ((qIdx k tag).bind (cLinked (k-1))).toList) : NodeContext)
def cVerified (k i : Nat) : Bool :=
  prelim (targetOf dead) (cContext k i) && (if k=0 then true else testAll (cContext k i) (cContext k i).2.2.1)
abbrev cR : Fin 768 → Row := asRow fun j => (dead.samples j).1
abbrev cS : Fin 768 → Row := asRow fun j => (dead.samples j).2
theorem cStep_faith (st : Nat × List Decor × List Decor) (gi mv : Nat)
    (hb : ∀ w ∈ st.2.1, faithful cR cS w) (hw : ∀ w ∈ st.2.2, faithful cR cS w) :
    (∀ w ∈ (cStep st gi mv).2.1, faithful cR cS w) ∧ (∀ w ∈ (cStep st gi mv).2.2, faithful cR cS w) := by
  obtain ⟨o, bank, ws⟩ := st
  have hz : faithful cR cS (codeDecor (mv &&& 3) (bank.getD ((mv >>> 2) &&& 15) defaultDecor)
      (bank.getD ((mv >>> 6) &&& 15) defaultDecor)) :=
    moved_faithful (faithful_get hb _) (faithful_get hb _) _
  refine ⟨fun w h => ?_, fun w h => ?_⟩
  · change w ∈ bank ++ [codeDecor (mv &&& 3) (bank.getD ((mv >>> 2) &&& 15) defaultDecor)
      (bank.getD ((mv >>> 6) &&& 15) defaultDecor)] at h
    rcases List.mem_append.mp h with h | h
    · exact hb w h
    · rw [List.mem_singleton.mp h]; exact hz
  · change w ∈ codeDecor (mv &&& 3) (bank.getD ((mv >>> 2) &&& 15) defaultDecor)
      (bank.getD ((mv >>> 6) &&& 15) defaultDecor) :: opKeep ((mv &&& 3)==2) ((mv >>> 10) &&& 1 == 1)
      ((mv >>> 11) &&& 1 == 1) (bank.getD ((mv >>> 2) &&& 15) defaultDecor)
      (bank.getD ((mv >>> 6) &&& 15) defaultDecor) ws at h
    rcases List.mem_cons.mp h with h | h
    · rw [h]; exact hz
    · exact hw w ((keep_sub _ _ _ _ _ _).subset h)
theorem cGo_faith : ∀ f k i, (∀ w ∈ (cGo f k i).2.1, faithful cR cS w) ∧ (∀ w ∈ (cGo f k i).2.2, faithful cR cS w) := by
  intro f
  induction f with
  | zero =>
    intro k i
    have h := decode_faithful 1 0x140 (wiresOf dead) cR cS (wires_faithful dead)
    exact ⟨h, h⟩
  | succ f ih =>
    intro k i
    exact cStep_faith _ _ _ (ih _ _).1 (ih _ _).2
theorem cLinked_gen (A : Array (List Nat)) (st : Nat → List Sig) (num k : Nat) {T : Sig}
    (names : ∀ x ∈ A.toList, autoOK T (x.map swapRows) = true)
    (earlier : ∀ i < num, Impossible T k (st i).toFinset)
    {pair : Nat × Nat} {out : List Sig}
    (h : (if pair.1 ≥ num then none else (A[pair.2]?).map fun perm => (st pair.1).map (movedWord (perm.map swapRows).reverse)) = some out) :
    Impossible T k out.toFinset := by
  split at h
  · contradiction
  next valid =>
    cases e : A[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))
theorem cLinked_sound (k : Nat)
    (names : ∀ x ∈ dead.autos.toList, autoOK (targetOf dead) (x.map swapRows) = true)
    (earlier : ∀ i < (qLev k).1, Impossible (targetOf dead) k (cState k i).toFinset)
    {pair out} (h : cLinked k pair = some out) :
    Impossible (targetOf dead) k out.toFinset :=
  cLinked_gen dead.autos (cState k) (qLev k).1 k names earlier h
theorem imp_zero {T : Sig} {ws : List Sig} (hT : T ∉ ws) : Impossible T 0 ws.toFinset := by
  intro t u lo h
  have ht : t = 0 := by omega
  subst t
  generalize he : ws.toFinset = S at h
  have eqS : S = {T} := h (fun k _ S => k = 0 → S = {T}) (fun _ _ => rfl) (fun _ _ _ hn => by contradiction) (fun _ _ _ _ _ hn => by contradiction) rfl
  exact hT (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
theorem cVerified_sound (k i : Nat)
    (prior : k>0 → ∀ j < (qLev (k-1)).1, Impossible (targetOf dead) (k-1) (cState (k-1) j).toFinset)
    (checked : cVerified k i = true) : Impossible (targetOf dead) k (cState k i).toFinset := by
  have geo := geomdead
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geo
  have samples := chart_pairs geo.1.1.1 geo.1.1.2
  have cols : ∀ ci ∈ dead.cols.values, Slice (vars dead.mask) (targetOf dead) (subcube ci.1 ci.2.1) ci.2.2.2.2 :=
    fun x hx => col_sound x (boundsBefore known383) (before_sound known383 valid383) (geo.1.2 x hx)
  have names := geo.2
  have hc : cVerified k i = (decide (((cContext k i).2.2.1.map Prod.fst).Nodup) &&
      !(((cContext k i).2.2.1.map Prod.fst).contains (targetOf dead)) &&
      (if k=0 then true else testAll (cContext k i) (cContext k i).2.2.1)) := rfl
  rw [hc, Bool.and_eq_true, Bool.and_eq_true] at checked
  obtain ⟨⟨h1, h2⟩, h3⟩ := checked
  have hN : ((cNode k i).2.2.map Prod.fst).Nodup := of_decide_eq_true h1
  have hT : targetOf dead ∉ (cNode k i).2.2.map Prod.fst := by
    intro hm
    have hcont : ((cContext k i).2.2.1.map Prod.fst).contains (targetOf dead) = true := List.contains_iff_mem.mpr hm
    rw [hcont] at h2
    exact Bool.noConfusion h2
  by_cases h0 : k=0
  · subst k
    exact imp_zero hT
  have test : testAll (cContext k i) (cContext k i).2.2.1 = true := by
    rw [if_neg h0] at h3
    exact h3
  apply node_sound (raw:=vars dead.mask) samples (cGo_faith _ _ _).2 hN hT _ _ test
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound dead cols h
  · intro tag xs hx
    have e : ((qIdx k tag).bind (cLinked (k-1))) = some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact cLinked_sound _ names (prior (by omega)) h
def cBlock (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => cVerified k (start+n) && cBlock k start n
theorem cBlock_at {k start n} (h : cBlock k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    cVerified k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [cBlock,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem cBlock_merge {k start a b} (h : cBlock k start a=true)
    (h' : cBlock k (start+a) b=true) : cBlock k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [cBlock,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,cBlock,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
theorem cMakeBlock {k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → cVerified k i = true) :
    cBlock k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cBlock,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def cContexts (k start n : Nat) :=
  ((List.range n).map (start+·)).map (cContext k)
def cHeader (k start n ar : Nat) :=
  (cContexts k start n).all (fun c => c.2.1==ar && prelim (targetOf dead) c)
def cRowCut (k start n ar lo len : Nat) :=
  let xs := cContexts k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem cRowCut_at {k start n ar lo len} (h : cRowCut k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (cContexts k start n)) (cContexts k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem cRowCut_merge {k start n ar lo a b}
    (h : cRowCut k start n ar lo a=true) (t : cRowCut k start n ar (lo+a) b=true) :
    cRowCut k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact cRowCut_at h (lo+j) (by omega) (by omega)
  · exact cRowCut_at t (lo+j) (by omega) (by omega)
theorem cCutsRun {k start n ar} (h : cRowCut k start n ar 0 ar=true) :
    runBatch k ar (cContexts k start n)=true := by
  let xs := cContexts k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := cRowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
theorem cCutsBlock {k start n ar} (hd : cHeader k start n ar=true)
    (h : cRowCut k start n ar 0 ar=true) : cBlock k start n=true := by
  apply cMakeBlock
  intro i lo hi
  let xs := cContexts k start n
  have hm : cContext k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  show (prelim (targetOf dead) (cContext k i) && (if k=0 then true else testAll (cContext k i) (cContext k i).2.2.1)) = true
  rw [Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cCutsRun h)
def cBoxes (k start n ar lo num : Nat) : Nat → Prop
  | 0 => cRowCut k start n ar lo num=true
  | d+1 => cBoxes k start n ar lo (num/2) d ∧ cBoxes k start n ar (lo+num/2) (num-num/2) d
theorem cBoxesCut {k start n ar lo num d} (h : cBoxes k start n ar lo num d) :
    cRowCut k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := cRowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cCells (k start n ar rows : Nat) : Nat → Prop
  | 0 => cHeader k start n ar=true ∧ cBoxes k start n ar 0 ar rows
  | d+1 => cCells k start (n/2) ar rows d ∧ cCells k (start+n/2) (n-n/2) ar rows d
theorem cCellsBlock {k start n ar rows d} (h : cCells k start n ar rows d) :
    cBlock k start n=true := by
  induction d generalizing start n with
  | zero => exact cCutsBlock h.1 (cBoxesCut h.2)
  | succ d ih =>
    have v := cBlock_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
theorem cForest_all (top : Nat) (rows : ∀ k ≤ top, cBlock k 0 (qLev k).1 = true) :
    ∀ k ≤ top, ∀ i < (qLev k).1, Impossible (targetOf dead) k (cState k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro hk i hi
    exact cVerified_sound 0 i (by omega) (cBlock_at (rows 0 hk) i (by omega) (by omega))
  | succ k ih =>
    intro hk i hi
    exact cVerified_sound _ i (fun _ => by simpa using ih (by omega))
      (cBlock_at (rows _ hk) i (by omega) (by omega))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb8_0 : cBlock 8 0 5 = true := by
  apply cCellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qa8 : cBlock 8 0 5 = true := qb8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb9_0 : cBlock 9 0 46 = true := by
  apply cCellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb9_46 : cBlock 9 46 176 = true := by
  apply cCellsBlock (ar:=10) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qa9 : cBlock 9 0 222 = true := (cBlock_merge (start:=0) (a:=46) (b:=176) qb9_0 qb9_46)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb10_0 : cBlock 10 0 8 = true := by
  apply cCellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb10_8 : cBlock 10 8 256 = true := by
  apply cCellsBlock (ar:=10) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb10_264 : cBlock 10 264 256 = true := by
  apply cCellsBlock (ar:=10) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb10_520 : cBlock 10 520 256 = true := by
  apply cCellsBlock (ar:=10) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb10_776 : cBlock 10 776 200 = true := by
  apply cCellsBlock (ar:=10) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb10_976 : cBlock 10 976 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb10_1232 : cBlock 10 1232 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb10_1488 : cBlock 10 1488 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb10_1744 : cBlock 10 1744 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb10_2000 : cBlock 10 2000 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb10_2256 : cBlock 10 2256 129 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qa10 : cBlock 10 0 2385 = true := (cBlock_merge (start:=0) (a:=2256) (b:=129) (cBlock_merge (start:=0) (a:=2000) (b:=256) (cBlock_merge (start:=0) (a:=1744) (b:=256) (cBlock_merge (start:=0) (a:=1488) (b:=256) (cBlock_merge (start:=0) (a:=1232) (b:=256) (cBlock_merge (start:=0) (a:=976) (b:=256) (cBlock_merge (start:=0) (a:=776) (b:=200) (cBlock_merge (start:=0) (a:=520) (b:=256) (cBlock_merge (start:=0) (a:=264) (b:=256) (cBlock_merge (start:=0) (a:=8) (b:=256) qb10_0 qb10_8) qb10_264) qb10_520) qb10_776) qb10_976) qb10_1232) qb10_1488) qb10_1744) qb10_2000) qb10_2256)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_0 : cBlock 11 0 2 = true := by
  apply cCellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_2 : cBlock 11 2 256 = true := by
  apply cCellsBlock (ar:=10) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_258 : cBlock 11 258 6 = true := by
  apply cCellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_264 : cBlock 11 264 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_520 : cBlock 11 520 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_776 : cBlock 11 776 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_1032 : cBlock 11 1032 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_1288 : cBlock 11 1288 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_1544 : cBlock 11 1544 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_1800 : cBlock 11 1800 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_2056 : cBlock 11 2056 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_2312 : cBlock 11 2312 38 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_2350 : cBlock 11 2350 256 = true := by
  apply cCellsBlock (ar:=12) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_2606 : cBlock 11 2606 256 = true := by
  apply cCellsBlock (ar:=12) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_2862 : cBlock 11 2862 256 = true := by
  apply cCellsBlock (ar:=12) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_3118 : cBlock 11 3118 256 = true := by
  apply cCellsBlock (ar:=12) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_3374 : cBlock 11 3374 256 = true := by
  apply cCellsBlock (ar:=12) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_3630 : cBlock 11 3630 128 = true := by
  apply cCellsBlock (ar:=12) (rows:=0) (d:=4)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qa11 : cBlock 11 0 3758 = true := (cBlock_merge (start:=0) (a:=3630) (b:=128) (cBlock_merge (start:=0) (a:=3374) (b:=256) (cBlock_merge (start:=0) (a:=3118) (b:=256) (cBlock_merge (start:=0) (a:=2862) (b:=256) (cBlock_merge (start:=0) (a:=2606) (b:=256) (cBlock_merge (start:=0) (a:=2350) (b:=256) (cBlock_merge (start:=0) (a:=2312) (b:=38) (cBlock_merge (start:=0) (a:=2056) (b:=256) (cBlock_merge (start:=0) (a:=1800) (b:=256) (cBlock_merge (start:=0) (a:=1544) (b:=256) (cBlock_merge (start:=0) (a:=1288) (b:=256) (cBlock_merge (start:=0) (a:=1032) (b:=256) (cBlock_merge (start:=0) (a:=776) (b:=256) (cBlock_merge (start:=0) (a:=520) (b:=256) (cBlock_merge (start:=0) (a:=264) (b:=256) (cBlock_merge (start:=0) (a:=258) (b:=6) (cBlock_merge (start:=0) (a:=2) (b:=256) qb11_0 qb11_2) qb11_258) qb11_264) qb11_520) qb11_776) qb11_1032) qb11_1288) qb11_1544) qb11_1800) qb11_2056) qb11_2312) qb11_2350) qb11_2606) qb11_2862) qb11_3118) qb11_3374) qb11_3630)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb12_0 : cBlock 12 0 58 = true := by
  apply cCellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb12_58 : cBlock 12 58 230 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb12_288 : cBlock 12 288 168 = true := by
  apply cCellsBlock (ar:=12) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qa12 : cBlock 12 0 456 = true := (cBlock_merge (start:=0) (a:=288) (b:=168) (cBlock_merge (start:=0) (a:=58) (b:=230) qb12_0 qb12_58) qb12_288)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb13_0 : cBlock 13 0 24 = true := by
  apply cCellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb13_24 : cBlock 13 24 45 = true := by
  apply cCellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb13_69 : cBlock 13 69 24 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qa13 : cBlock 13 0 93 = true := (cBlock_merge (start:=0) (a:=69) (b:=24) (cBlock_merge (start:=0) (a:=24) (b:=45) qb13_0 qb13_24) qb13_69)
theorem qTables : ∀ k ≤ 13, cBlock k 0 (qLev k).1 = true := by
  intro k hk
  interval_cases k
  · exact (rfl : cBlock 0 0 0 = true)
  · exact (rfl : cBlock 1 0 0 = true)
  · exact (rfl : cBlock 2 0 0 = true)
  · exact (rfl : cBlock 3 0 0 = true)
  · exact (rfl : cBlock 4 0 0 = true)
  · exact (rfl : cBlock 5 0 0 = true)
  · exact (rfl : cBlock 6 0 0 = true)
  · exact (rfl : cBlock 7 0 0 = true)
  · exact qa8
  · exact qa9
  · exact qa10
  · exact qa11
  · exact qa12
  · exact qa13
def or04 : Sig := bin true (inputs.getD 0 zero) (inputs.getD 4 zero)
def supplied4 : List Sig := inputs ++ [or04]
theorem sup4_len : supplied4.length = 10 := by decide +kernel
theorem sup4_proper : ∀ i < 10, proper (supplied4.getD i zero) := by
  unfold proper; decide +kernel
theorem sup4_mem (i : Nat) (hi : i < 10) : supplied4.getD i zero ∈ supplied4 := by
  rw [List.getD_eq_getElem _ _ (by rw [sup4_len]; exact hi)]
  exact List.getElem_mem _
theorem or04_bits (r : Row) :
    supplied4.map (bit r) = List.ofFn (sample r) ++ [sample r 0 || sample r 4] := by
  simp only [supplied4,List.map_append,List.map_singleton,or04,bit_bin,sampled]
  rfl
def nbr4 (i : Fin 9) : Nat := [4,2,1,2,0,0,1,2,3].getD i.val 0
def absent4 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< nbr4 i)
def present4 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< nbr4 i))
theorem or4_witness : ∀ i : Fin 9,
    (bit (absent4 i) graph != bit (present4 i) graph) &&
    (supplied4.all fun w => w == inputs.getD i.val zero ||
      bit (absent4 i) w == bit (present4 i) w) = true := by decide +kernel
theorem roots4 {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ supplied4) :
    S = inputs.toFinset ∨ S = supplied4.toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := or4_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absent4 i) (present4 i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : or04 ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [supplied4,List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [supplied4,List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed
def rootTable : List (Nat × Nat × Bool × Bool × Nat × Nat) := [(0,1,false,false,0,0),(1,0,false,false,0,0),(0,1,true,false,24,0),(1,0,false,true,24,0),(0,1,false,true,25,0),(1,0,true,false,25,0),(0,1,true,true,69,0),(1,0,true,true,69,0),(0,2,false,false,1,0),(2,0,false,false,1,0),(0,2,true,false,26,0),(2,0,false,true,26,0),(0,2,false,true,27,0),(2,0,true,false,27,0),(0,2,true,true,70,0),(2,0,true,true,70,0),(0,3,false,false,2,0),(3,0,false,false,2,0),(0,3,true,false,28,0),(3,0,false,true,28,0),(0,3,false,true,29,0),(3,0,true,false,29,0),(0,3,true,true,71,0),(3,0,true,true,71,0),(0,5,false,false,0,1),(5,0,false,false,0,1),(0,5,true,false,24,1),(5,0,false,true,24,1),(0,5,false,true,25,1),(5,0,true,false,25,1),(0,5,true,true,69,1),(5,0,true,true,69,1),(0,6,false,false,3,0),(6,0,false,false,3,0),(0,6,true,false,30,0),(6,0,false,true,30,0),(0,6,false,true,31,0),(6,0,true,false,31,0),(0,6,true,true,72,0),(6,0,true,true,72,0),(0,7,false,false,3,1),(7,0,false,false,3,1),(0,7,true,false,30,1),(7,0,false,true,30,1),(0,7,false,true,31,1),(7,0,true,false,31,1),(0,7,true,true,72,1),(7,0,true,true,72,1),(0,8,false,false,1,1),(8,0,false,false,1,1),(0,8,true,false,26,1),(8,0,false,true,26,1),(0,8,false,true,27,1),(8,0,true,false,27,1),(0,8,true,true,70,1),(8,0,true,true,70,1),(1,2,false,false,4,0),(2,1,false,false,4,0),(1,2,true,false,32,0),(2,1,false,true,32,0),(1,2,false,true,33,0),(2,1,true,false,33,0),(1,2,true,true,73,0),(2,1,true,true,73,0),(1,3,false,false,5,0),(3,1,false,false,5,0),(1,3,true,false,34,0),(3,1,false,true,34,0),(1,3,false,true,35,0),(3,1,true,false,35,0),(1,3,true,true,74,0),(3,1,true,true,74,0),(1,4,false,false,6,0),(4,1,false,false,6,0),(1,4,true,false,36,0),(4,1,false,true,36,0),(1,4,false,true,37,0),(4,1,true,false,37,0),(1,4,true,true,75,0),(4,1,true,true,75,0),(1,5,false,false,7,0),(5,1,false,false,7,0),(1,5,true,false,38,0),(5,1,false,true,38,0),(1,5,false,true,38,1),(5,1,true,false,38,1),(1,5,true,true,76,0),(5,1,true,true,76,0),(1,6,false,false,8,0),(6,1,false,false,8,0),(1,6,true,false,39,0),(6,1,false,true,39,0),(1,6,false,true,40,0),(6,1,true,false,40,0),(1,6,true,true,77,0),(6,1,true,true,77,0),(1,7,false,false,9,0),(7,1,false,false,9,0),(1,7,true,false,41,0),(7,1,false,true,41,0),(1,7,false,true,42,0),(7,1,true,false,42,0),(1,7,true,true,78,0),(7,1,true,true,78,0),(1,8,false,false,10,0),(8,1,false,false,10,0),(1,8,true,false,43,0),(8,1,false,true,43,0),(1,8,false,true,44,0),(8,1,true,false,44,0),(1,8,true,true,79,0),(8,1,true,true,79,0),(1,9,false,false,11,0),(9,1,false,false,11,0),(1,9,true,false,45,0),(9,1,false,true,45,0),(1,9,false,true,46,0),(9,1,true,false,46,0),(1,9,true,true,80,0),(9,1,true,true,80,0),(2,3,false,false,12,0),(3,2,false,false,12,0),(2,3,true,false,47,0),(3,2,false,true,47,0),(2,3,false,true,48,0),(3,2,true,false,48,0),(2,3,true,true,81,0),(3,2,true,true,81,0),(2,4,false,false,13,0),(4,2,false,false,13,0),(2,4,true,false,49,0),(4,2,false,true,49,0),(2,4,false,true,50,0),(4,2,true,false,50,0),(2,4,true,true,82,0),(4,2,true,true,82,0),(2,5,false,false,10,1),(5,2,false,false,10,1),(2,5,true,false,44,1),(5,2,false,true,44,1),(2,5,false,true,43,1),(5,2,true,false,43,1),(2,5,true,true,79,1),(5,2,true,true,79,1),(2,6,false,false,14,0),(6,2,false,false,14,0),(2,6,true,false,51,0),(6,2,false,true,51,0),(2,6,false,true,52,0),(6,2,true,false,52,0),(2,6,true,true,83,0),(6,2,true,true,83,0),(2,7,false,false,15,0),(7,2,false,false,15,0),(2,7,true,false,53,0),(7,2,false,true,53,0),(2,7,false,true,54,0),(7,2,true,false,54,0),(2,7,true,true,84,0),(7,2,true,true,84,0),(2,8,false,false,16,0),(8,2,false,false,16,0),(2,8,true,false,55,0),(8,2,false,true,55,0),(2,8,false,true,55,1),(8,2,true,false,55,1),(2,8,true,true,85,0),(8,2,true,true,85,0),(2,9,false,false,17,0),(9,2,false,false,17,0),(2,9,true,false,56,0),(9,2,false,true,56,0),(2,9,false,true,57,0),(9,2,true,false,57,0),(2,9,true,true,86,0),(9,2,true,true,86,0),(3,4,false,false,18,0),(4,3,false,false,18,0),(3,4,true,false,58,0),(4,3,false,true,58,0),(3,4,false,true,59,0),(4,3,true,false,59,0),(3,4,true,true,87,0),(4,3,true,true,87,0),(3,5,false,false,5,1),(5,3,false,false,5,1),(3,5,true,false,35,1),(5,3,false,true,35,1),(3,5,false,true,34,1),(5,3,true,false,34,1),(3,5,true,true,74,1),(5,3,true,true,74,1),(3,6,false,false,19,0),(6,3,false,false,19,0),(3,6,true,false,60,0),(6,3,false,true,60,0),(3,6,false,true,61,0),(6,3,true,false,61,0),(3,6,true,true,88,0),(6,3,true,true,88,0),(3,7,false,false,19,1),(7,3,false,false,19,1),(3,7,true,false,60,1),(7,3,false,true,60,1),(3,7,false,true,61,1),(7,3,true,false,61,1),(3,7,true,true,88,1),(7,3,true,true,88,1),(3,8,false,false,12,1),(8,3,false,false,12,1),(3,8,true,false,48,1),(8,3,false,true,48,1),(3,8,false,true,47,1),(8,3,true,false,47,1),(3,8,true,true,81,1),(8,3,true,true,81,1),(3,9,false,false,20,0),(9,3,false,false,20,0),(3,9,true,false,62,0),(9,3,false,true,62,0),(3,9,false,true,63,0),(9,3,true,false,63,0),(3,9,true,true,89,0),(9,3,true,true,89,0),(4,5,false,false,6,1),(5,4,false,false,6,1),(4,5,true,false,37,1),(5,4,false,true,37,1),(4,5,false,true,36,1),(5,4,true,false,36,1),(4,5,true,true,75,1),(5,4,true,true,75,1),(4,6,false,false,21,0),(6,4,false,false,21,0),(4,6,true,false,64,0),(6,4,false,true,64,0),(4,6,false,true,65,0),(6,4,true,false,65,0),(4,6,true,true,90,0),(6,4,true,true,90,0),(4,7,false,false,21,1),(7,4,false,false,21,1),(4,7,true,false,64,1),(7,4,false,true,64,1),(4,7,false,true,65,1),(7,4,true,false,65,1),(4,7,true,true,90,1),(7,4,true,true,90,1),(4,8,false,false,13,1),(8,4,false,false,13,1),(4,8,true,false,50,1),(8,4,false,true,50,1),(4,8,false,true,49,1),(8,4,true,false,49,1),(4,8,true,true,82,1),(8,4,true,true,82,1),(5,6,false,false,9,1),(6,5,false,false,9,1),(5,6,true,false,41,1),(6,5,false,true,41,1),(5,6,false,true,42,1),(6,5,true,false,42,1),(5,6,true,true,78,1),(6,5,true,true,78,1),(5,7,false,false,8,1),(7,5,false,false,8,1),(5,7,true,false,39,1),(7,5,false,true,39,1),(5,7,false,true,40,1),(7,5,true,false,40,1),(5,7,true,true,77,1),(7,5,true,true,77,1),(5,8,false,false,4,1),(8,5,false,false,4,1),(5,8,true,false,32,1),(8,5,false,true,32,1),(5,8,false,true,33,1),(8,5,true,false,33,1),(5,8,true,true,73,1),(8,5,true,true,73,1),(5,9,false,false,11,1),(9,5,false,false,11,1),(5,9,true,false,45,1),(9,5,false,true,45,1),(5,9,false,true,46,1),(9,5,true,false,46,1),(5,9,true,true,80,1),(9,5,true,true,80,1),(6,7,false,false,22,0),(7,6,false,false,22,0),(6,7,true,false,66,0),(7,6,false,true,66,0),(6,7,false,true,66,1),(7,6,true,false,66,1),(6,7,true,true,91,0),(7,6,true,true,91,0),(6,8,false,false,15,1),(8,6,false,false,15,1),(6,8,true,false,54,1),(8,6,false,true,54,1),(6,8,false,true,53,1),(8,6,true,false,53,1),(6,8,true,true,84,1),(8,6,true,true,84,1),(6,9,false,false,23,0),(9,6,false,false,23,0),(6,9,true,false,67,0),(9,6,false,true,67,0),(6,9,false,true,68,0),(9,6,true,false,68,0),(6,9,true,true,92,0),(9,6,true,true,92,0),(7,8,false,false,14,1),(8,7,false,false,14,1),(7,8,true,false,52,1),(8,7,false,true,52,1),(7,8,false,true,51,1),(8,7,true,false,51,1),(7,8,true,true,83,1),(8,7,true,true,83,1),(7,9,false,false,23,1),(9,7,false,false,23,1),(7,9,true,false,67,1),(9,7,false,true,67,1),(7,9,false,true,68,1),(9,7,true,false,68,1),(7,9,true,true,92,1),(9,7,true,true,92,1),(8,9,false,false,17,1),(9,8,false,false,17,1),(8,9,true,false,56,1),(9,8,false,true,56,1),(8,9,false,true,57,1),(9,8,true,false,57,1),(8,9,true,true,86,1),(9,8,true,true,86,1)]
def rootEntryOK (p q : Nat) (ka kb : Bool) (e : Nat × Nat × Bool × Bool × Nat × Nat) : Bool :=
  e.1 == p && e.2.1 == q && e.2.2.1 == ka && e.2.2.2.1 == kb &&
    (cLinked 13 (e.2.2.2.2.1, e.2.2.2.2.2)).any
      (fun xs => sameWords xs (childTwo supplied4 (supplied4.getD p zero) (supplied4.getD q zero) true ka kb))
def rootOK : Bool :=
  (List.range 10).all fun p => (List.range 10).all fun q => [false,true].all fun ka => [false,true].all fun kb =>
    p == q || supplied4.contains (bin true (supplied4.getD p zero) (supplied4.getD q zero)) ||
    rootTable.any (rootEntryOK p q ka kb)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem rootOK_true : rootOK = true := by decide +kernel
theorem cImp (p q : Nat) (hp : p < 10) (hq : q < 10) (hpq : p ≠ q)
    (hz : bin true (supplied4.getD p zero) (supplied4.getD q zero) ∉ supplied4) (ka kb : Bool) :
    Impossible graph 13 (childTwo supplied4 (supplied4.getD p zero) (supplied4.getD q zero) true ka kb).toFinset := by
  have h := rootOK_true
  unfold rootOK at h
  have h1 := List.all_eq_true.mp h p (List.mem_range.mpr hp)
  have h2 := List.all_eq_true.mp h1 q (List.mem_range.mpr hq)
  have h3 := List.all_eq_true.mp h2 ka (by cases ka <;> simp)
  have h4 := List.all_eq_true.mp h3 kb (by cases kb <;> simp)
  simp only [Bool.or_eq_true, beq_iff_eq] at h4
  rcases h4 with (h4 | h4) | h4
  · exact absurd h4 hpq
  · exact absurd (List.contains_iff_mem.mp h4) hz
  obtain ⟨e, _, he⟩ := List.any_eq_true.mp h4
  simp only [rootEntryOK, Bool.and_eq_true, beq_iff_eq] at he
  obtain ⟨_, hx⟩ := he
  cases hl : cLinked 13 (e.2.2.2.2.1, e.2.2.2.2.2) with
  | none => rw [hl] at hx; simp at hx
  | some xs =>
    rw [hl] at hx
    have hs : sameWords xs (childTwo supplied4 (supplied4.getD p zero) (supplied4.getD q zero) true ka kb) = true := by
      simpa using hx
    have geo := geomdead
    simp only [graphValid, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at geo
    have imp := cLinked_sound 13 geo.2 (fun i hi => cForest_all 13 qTables 13 le_rfl i hi) hl
    have htgt : targetOf dead = graph := by decide +kernel
    rw [htgt, sameWords_sound hs] at imp
    exact imp
theorem orPins (pins : List Nat) (short : pins.length ≤ 2)
    (zn : gv supplied4 ⟨GateOp.or, pins⟩ ∉ supplied4) (zp : proper (gv supplied4 ⟨GateOp.or, pins⟩)) :
    ∃ p q, p < 10 ∧ q < 10 ∧ p ≠ q ∧ gv supplied4 ⟨GateOp.or, pins⟩ = bin true (supplied4.getD p zero) (supplied4.getD q zero) := by
  match pins, short, zn, zp with
  | [], _, _, zp => exact absurd (by simp [gv]) zp.1
  | [i], _, zn, zp =>
    have e : gv supplied4 ⟨GateOp.or, [i]⟩ = supplied4.getD i zero := by
      simp only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, (bin_laws _).2.1]
    rw [e] at zn zp
    exact absurd zp ((get_rep supplied4 i).resolve_left zn)
  | [i, j], _, zn, zp =>
    have e : gv supplied4 ⟨GateOp.or, [i, j]⟩ = bin true (supplied4.getD i zero) (supplied4.getD j zero) := by
      simp only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, (bin_laws _).2.1]
    rw [e] at zn zp ⊢
    by_cases hi : i < 10
    · by_cases hj : j < 10
      · by_cases hij : i = j
        · subst hij
          rw [(bin_laws _).2.2.2.2.2] at zn zp
          exact absurd zp ((get_rep supplied4 i).resolve_left zn)
        · exact ⟨i, j, hi, hj, hij, rfl⟩
      · have z0 : supplied4.getD j zero = zero := List.getD_eq_default _ _ (by rw [sup4_len]; omega)
        rw [z0, (bin_laws _).2.1] at zn zp
        exact absurd zp ((get_rep supplied4 i).resolve_left zn)
    · have z0 : supplied4.getD i zero = zero := List.getD_eq_default _ _ (by rw [sup4_len]; omega)
      rw [z0, bin_comm, (bin_laws _).2.1] at zn zp
      exact absurd zp ((get_rep supplied4 j).resolve_left zn)
theorem closeOr (pins : List Nat) (short : pins.length ≤ 2) (C : Circuit)
    (fan : PEqualNP.MetaComplexity.FanInTwo C) (small : C.size ≤ 13)
    (correct : ∀ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [x 0 || x 4]) ++ [GateOp.or.eval (pins.map (fun j => (List.ofFn x ++ [x 0 || x 4]).getD j false))]) = edge x) : False := by
  have noRun : Impossible graph 14 inputs.toFinset := dead_start (before_sound known383 valid383) geomdead tablesdead
  let g : Gate := ⟨.or, pins⟩
  let z := gv supplied4 g
  let w := supplied4 ++ [z]
  have zbit (r : Row) : bit r z = GateOp.or.eval (pins.map (fun j =>
      (supplied4.map (bit r)).getD j false)) := by
    simpa only [z,g] using run_bit r g supplied4 (Or.inr (Or.inl rfl))
  have eqGoal : (execute C.gates w).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates w).getD C.output zero) = bit r graph
    rw [←b_read,execute_bits _ _ _ (fun a ha => (fan a ha).1),edge_table]
    change C.eval (w.map (bit r)) = edge (sample r)
    simpa only [w,List.map_append,List.map_singleton,zbit,or04_bits] using correct (sample r)
  have out := get_rep (execute C.gates w) C.output
  rw [eqGoal] at out
  obtain ⟨k,t,S,hk,run,hs⟩ := extract C.gates w fan graph_proper (out.resolve_right fun hn => hn graph_proper)
  have hk13 : k ≤ 13 := by change C.gates.length ≤ 13 at small; omega
  have finish (S' : Finset Sig) (k' t' : Nat) (hk' : k' ≤ 13) (run' : Live graph k' t' S')
      (sub : ∀ a ∈ S', a ∈ supplied4) : False := by
    have formed : represented inputs or04 ∨ witness inputs or04 :=
      bin_rep true (get_rep inputs 0) (get_rep inputs 4)
    obtain ⟨l,v,U,hl,run'',sub'⟩ := pull_gate run' formed sub
    obtain e | e := roots4 run'' (fun a ha => List.mem_append_left _ (sub' a ha))
    · exact noRun l v (by omega) (e ▸ run'')
    · have h4 : or04 ∈ U := e ▸ List.mem_toFinset.mpr (List.mem_append_right _ (by simp))
      exact (by decide +kernel : or04 ∉ inputs) (sub' or04 h4)
  by_cases hzz : z ∈ S ∧ z ∉ supplied4
  · obtain ⟨zS, zn⟩ := hzz
    have zp : proper z := live_proper run z zS
    obtain ⟨p, q, hp, hq, hpq, hzeq0⟩ := orPins pins short zn zp
    have hzeq : z = bin true (supplied4.getD p zero) (supplied4.getD q zero) := hzeq0
    have pa := sup4_proper p hp
    have pb := sup4_proper q hq
    have hab : supplied4.getD p zero ≠ supplied4.getD q zero := by
      intro e
      apply zn
      rw [hzeq, e, (bin_laws _).2.2.2.2.2]
      exact sup4_mem q hq
    let U := S.erase z
    have tail : Live graph k t (insert z U) := by
      rw [show insert z U = S from Finset.insert_erase zS]
      exact run
    have hu : ∀ v ∈ U, v ∈ supplied4 := fun v hv => by
      obtain ⟨hne, hm'⟩ := Finset.mem_erase.mp hv
      rcases List.mem_append.mp (hs v hm') with h1 | h1
      · exact h1
      · exact absurd (List.mem_singleton.mp h1) hne
    have hf : z ∉ insert (supplied4.getD p zero) (insert (supplied4.getD q zero) U) := fun hh => by
      rcases Finset.mem_insert.mp hh with eq | u
      · exact zn (eq ▸ sup4_mem p hp)
      rcases Finset.mem_insert.mp u with eq | u
      · exact zn (eq ▸ sup4_mem q hq)
      · exact zn (hu _ u)
    rw [hzeq] at hf tail zn
    generalize hA : supplied4.getD p zero = a at *
    generalize hB : supplied4.getD q zero = b at *
    have full := Live.binary pa pb hab hf tail
    have sub3 : ∀ v ∈ insert a (insert b U), v ∈ supplied4 := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hA ▸ sup4_mem p hp
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hB ▸ sup4_mem q hq
      · exact hu v hv
    rcases roots4 full sub3 with he | he
    · exact noRun (k+1) t (by omega) (he ▸ full)
    have he : supplied4.toFinset = insert a (insert b U) := he.symm
    have hn : supplied4.Nodup := by decide +kernel
    have am : a ∈ supplied4 := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ supplied4 := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (supplied4.erase a).erase b
    have er : rest.toFinset = (supplied4.toFinset.erase a).erase b := by
      rw [show rest = (supplied4.erase a).erase b by rfl, erase_fin (hn.erase _) b, erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin, kept_fin, er, he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;>
        by_cases jb : j = b <;> simp [ka, kb, aa, bb, ja, jb, hab, Ne.symm hab]
    have eq : (childTwo supplied4 a b true ka kb).toFinset = insert (bin true a b) U := by
      change (bin true a b :: kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have imp := cImp p q hp hq hpq (hA ▸ hB ▸ zn) ka kb
    rw [hA, hB] at imp
    exact imp k t hk13 (eq.symm ▸ tail)
  · apply finish S k t hk13 run
    intro a ha
    rcases List.mem_append.mp (hs a ha) with h | h
    · exact h
    · have hza : a = z := List.mem_singleton.mp h
      by_contra hn
      exact hzz ⟨hza ▸ ha, hza ▸ hn⟩
theorem mainOr : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (¬∃ (x6 : Fin (9 : ℕ)) (x7 : Fin (9 : ℕ)), x6 ≠ (0 : Fin (9 : ℕ)) ∧ x6 ≠ (4 : Fin (9 : ℕ)) ∧ x7 ≠ (0 : Fin (9 : ℕ)) ∧ x7 ≠ (4 : Fin (9 : ℕ)) ∧ x6 < x7 ∧ x1.Perm [↑x6, ↑x7]) ∨ List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x3.gates < (2 : ℕ) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro x1 hlen x3 hfan hsize _
  refine Classical.byContradiction fun hcon => ?_
  have hc : ∀ x : Fin 9 → Bool, x3.eval ((List.ofFn x ++ [x 0 || x 4]) ++ [GateOp.or.eval (x1.map fun i => (List.ofFn x ++ [x 0 || x 4]).getD i false)]) = edge x := by
    intro x
    by_contra hne
    exact hcon ⟨x, hne⟩
  exact closeOr x1 hlen x3 hfan hsize hc
end PEqualNP.Outside.L_meta_3967_aux

open PEqualNP.Outside.L_meta_3967_aux in
theorem PEqualNP.Outside.L_meta_3967 :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (¬∃ (x6 : Fin (9 : ℕ)) (x7 : Fin (9 : ℕ)), x6 ≠ (0 : Fin (9 : ℕ)) ∧ x6 ≠ (4 : Fin (9 : ℕ)) ∧ x7 ≠ (0 : Fin (9 : ℕ)) ∧ x7 ≠ (4 : Fin (9 : ℕ)) ∧ x6 < x7 ∧ x1.Perm [↑x6, ↑x7]) ∨ List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x3.gates < (2 : ℕ) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  exact mainOr
