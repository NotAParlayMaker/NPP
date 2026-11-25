import Mathlib
import PEqualNP.Defs
-- The gate bank is checked on a separating sample of assignments to the five inputs.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_8686_aux
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 13
def zero : Sig := 0
def one : Sig := BitVec.allOnes 13
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

def Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ proper target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset Sig) (a : Sig), t=u+1 ∧ S=insert a U ∧ proper a ∧
      neg a ∉ insert a U ∧ Live target k u (insert (neg a) U)) ∨
    (∃ (U : Finset Sig) (a b : Sig) (d : Bool), S=insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live target k t (insert (bin d a b) U))
theorem Live.stop {target : Sig} (hp : proper target) : Live target 0 0 {target} := ⟨rfl,rfl,hp⟩
theorem Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
    (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
    Live target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
    Live target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {target : Sig} {motive : ∀ (k t : Nat) (S : Finset Sig), Live target k t S → Prop}
    (stop : ∀ (hp : proper target), motive 0 0 {target} (Live.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)),
      motive k t (insert (neg a) U) tail → motive (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)),
      motive k t (insert (bin d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset Sig} (h : Live target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using Live.ind with
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

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
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

def bit (i : Fin 13) (a : Sig) : Bool := a.getLsbD i.val
lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp [i.isLt]
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




def target : Sig := 4921
def raw : List Sig := [347,5677,7086,7216,8128]
def rowNums : List Nat := [3,5,6,7,9,14,17,20,21,22,26,28,30]
def eqBits (i j : Fin 13) (S : Finset Sig) := ∀ a∈S, bit i a = bit j a
lemma equal_of_live {k t S} (h : Live T k t S) (i j) : eqBits i j S → bit i T = bit j T := by
  induction h using Live.ind with
  | stop hp => exact fun same => same T (by simp)
  | @unary k t U a ha hf tail ih =>
    intro same
    apply ih
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl|hv
    · simp [bit_neg,same a (by simp)]
    · exact same _ (by simp [hv])
  | @binary k t U a b d ha hb hab hf tail ih =>
    intro same
    apply ih
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl|hv
    · simp only [bit_bin,same a (by simp),same b (by simp)]
    · exact same _ (by simp [hv])
def leBits (i j : Fin 13) (S : Finset Sig) := ∀ a∈S, bit i a = true → bit j a = true
lemma le_of_live {k t S} (h : Live T k t S) (i j) :
    t=0 → leBits i j S → bit i T = true → bit j T = true := by
  induction h using Live.ind with
  | stop hp => exact fun _ h => h T (by simp)
  | unary ha hf tail ih => omega
  | @binary k t U a b d ha hb hab hf tail ih =>
    intro ht ord
    apply ih ht
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl|hv
    · have va := ord a (by simp)
      have vb := ord b (by simp)
      simp only [bit_bin]
      cases d <;> cases hia : bit i a <;> cases hja : bit j a <;> cases hib : bit i b <;> cases hjb : bit j b <;> simp_all
    · exact ord _ (by simp [hv])


def sep (t : Nat) (S : Finset Sig) := ∀ i j : Fin 13, bit i target=true → bit j target=false →
    ∃ a∈S, if t=0 then bit i a=true ∧ bit j a=false else bit i a ≠ bit j a
def sepDecision (t S) : Decidable (sep t S) := by
  letI (i j : Fin 13) : Decidable (∃ a∈S, if t=0 then bit i a=true ∧ bit j a=false else bit i a ≠ bit j a) :=
    Finset.decidableExistsAndFinset
  unfold sep
  infer_instance
lemma sep_of_live {k t S} (h : Live target k t S) : sep t S := by
  intro i j yes no
  by_cases ht : t=0
  · simp only [if_pos ht]
    by_contra! neither
    have le : leBits i j S := by
      intro a ha hi
      simpa using neither a ha hi
    have := le_of_live h i j ht le yes
    simp_all
  · simp only [if_neg ht]
    by_contra! eq
    have := equal_of_live h i j eq
    simp_all

def cut (S : Finset Sig) (a : Sig) (keep : Bool) := if keep then S else S.erase a
lemma cut_back (a : Sig) (U : Finset Sig) :
    cut (insert a U) a (decide (a∈U)) = U := by
  by_cases h : a∈U <;> simp [cut,h]
lemma cut_comm (a b : Sig) (ab : a≠b) (U : Finset Sig) (q : Bool) :
    cut (insert a (insert b U)) a q = insert b (cut (insert a U) a q) := by
  cases q <;> ext v <;> simp [cut,Finset.mem_erase,Finset.mem_insert] <;> grind



def bank : Nat → Nat → List (Finset Sig)
  | 2,0 => [({347,4653,8112} : Finset Sig),({347,5677,7088} : Finset Sig),({347,5693,7072} : Finset Sig)]
  | 3,0 => [({16,347,5677,7072} : Finset Sig),({48,347,5677,7040} : Finset Sig),({347,4652,5677,8112} : Finset Sig),({347,4653,7040,7216} : Finset Sig),({347,5677,6192,7040} : Finset Sig),({347,5677,7072,7216} : Finset Sig),({347,5677,7072,7741} : Finset Sig),({347,5677,7072,8112} : Finset Sig),({347,5677,7086,8112} : Finset Sig),({347,5677,7102,8176} : Finset Sig),({347,5677,7103,8176} : Finset Sig),({347,5677,7167,8112} : Finset Sig),({347,5693,7086,8176} : Finset Sig)]
  | 4,0 => [({16,347,5677,7086,8176} : Finset Sig),({48,347,5677,7086,8128} : Finset Sig),({63,347,5677,7040,7216} : Finset Sig),({63,347,5677,7086,8176} : Finset Sig),({347,960,5677,7086,7216} : Finset Sig),({347,4652,5677,7040,7216} : Finset Sig),({347,4653,7086,7216,8128} : Finset Sig),({347,4910,5677,7216,8128} : Finset Sig),({347,5168,5677,7086,8128} : Finset Sig),({347,5677,5952,7086,7216} : Finset Sig),({347,5677,6176,7040,7216} : Finset Sig),({347,5677,6192,7086,8128} : Finset Sig),({347,5677,7040,7086,7216} : Finset Sig),({347,5677,7040,7086,8112} : Finset Sig),({347,5677,7040,7167,7216} : Finset Sig),({347,5677,7072,7086,7216} : Finset Sig),({347,5677,7072,7216} : Finset Sig),({347,5677,7072,7216,8128} : Finset Sig),({347,5677,7072,7216,8176} : Finset Sig),({347,5677,7084,7216,8128} : Finset Sig),({347,5677,7086,7104,7216} : Finset Sig),({347,5677,7086,7216,8064} : Finset Sig),({347,5677,7086,7216,8112} : Finset Sig),({347,5677,7086,7216,8128} : Finset Sig),({347,5677,7086,7216,8137} : Finset Sig),({347,5677,7086,7216,8144} : Finset Sig),({347,5677,7086,7216,8145} : Finset Sig),({347,5677,7086,7216,8160} : Finset Sig),({347,5677,7086,7216,8176} : Finset Sig),({347,5677,7086,7225,8128} : Finset Sig),({347,5677,7086,7728,8128} : Finset Sig),({347,5677,7086,7741,8176} : Finset Sig),({347,5677,7086,8112} : Finset Sig),({347,5677,7086,8112,8128} : Finset Sig),({347,5677,7086,8126,8176} : Finset Sig),({347,5677,7087,7216,8128} : Finset Sig),({347,5677,7102,7216,8128} : Finset Sig),({347,5677,7103,7216,8128} : Finset Sig),({347,5693,7086,7216,8128} : Finset Sig)]
  | 4,1 => [({266,4652,7216,8128} : Finset Sig),({347,5677,7072,7216} : Finset Sig),({347,5677,7086,8112} : Finset Sig),({347,5677,7086,8160} : Finset Sig),({5499,5677,7086,8128} : Finset Sig)]
  | 5,0 => [({9,347,5677,7086,7216,8128} : Finset Sig),({16,347,5677,7086,7216,8128} : Finset Sig),({63,347,5677,7086,7216,8128} : Finset Sig),({266,347,5677,7086,7216,8128} : Finset Sig),({320,347,5677,7086,7216,8128} : Finset Sig),({347,975,5677,7086,7216,8128} : Finset Sig),({347,1105,5677,7086,7216,8128} : Finset Sig),({347,2514,5677,7086,7216,8128} : Finset Sig),({347,4652,5677,7086,7216,8128} : Finset Sig),({347,5152,5677,7086,7216,8128} : Finset Sig),({347,5632,5677,7086,7216,8128} : Finset Sig),({347,5677,6015,7086,7216,8128} : Finset Sig),({347,5677,6176,7086,7216,8128} : Finset Sig),({347,5677,7040,7086,7216} : Finset Sig),({347,5677,7040,7086,7216,8128} : Finset Sig),({347,5677,7086,7167,7216,8128} : Finset Sig),({347,5677,7086,7168,7216,8128} : Finset Sig),({347,5677,7086,7216,7547,8128} : Finset Sig),({347,5677,7086,7216,7741,8128} : Finset Sig),({347,5677,7086,7216,7844,8128} : Finset Sig),({347,5677,7086,7216,8111,8128} : Finset Sig),({347,5677,7086,7216,8126,8128} : Finset Sig),({347,5677,7086,7216,8128} : Finset Sig),({347,5677,7086,7216,8128,8155} : Finset Sig),({347,5677,7086,7216,8128,8173} : Finset Sig),({347,5677,7086,7216,8128,8174} : Finset Sig),({347,5677,7086,7216,8128,8176} : Finset Sig),({347,5677,7086,7216,8176} : Finset Sig)]
  | 5,1 => [({63,347,5677,7086,7216} : Finset Sig),({266,5677,7086,7216,8128} : Finset Sig),({347,975,5677,7086,8128} : Finset Sig),({347,1105,5677,7216,8128} : Finset Sig),({347,2514,7086,7216,8128} : Finset Sig),({347,4652,7086,7216,8128} : Finset Sig),({347,5152,5677,7086,8128} : Finset Sig),({347,5677,6176,7086,8128} : Finset Sig),({347,5677,7040,7086,7216} : Finset Sig),({347,5677,7040,7216,8128} : Finset Sig),({347,5677,7086,7216,8128} : Finset Sig),({347,5677,7086,7216,8176} : Finset Sig),({347,5677,7086,7547,8128} : Finset Sig),({347,5677,7086,8128,8176} : Finset Sig),({5677,7086,7216,7547,8128} : Finset Sig),({5677,7086,7216,7844,8128} : Finset Sig)]
  | 6,0 => [({347,5677,7086,7216,8128} : Finset Sig)]
  | 6,1 => [({347,5677,7086,7216,8128} : Finset Sig)]
  | 6,2 => [({347,5677,7086,7216,8128} : Finset Sig)]
  | _,_ => []
def Next (k t : Nat) (S : Finset Sig) : Prop :=
  S.card+t ≤ k+1 → t ≤ k → sep t S → S ∈ bank k t
def nextDecision (k t S) : Decidable (Next k t S) := by
  letI := sepDecision t S
  unfold Next
  infer_instance
def Checked (k t : Nat) (S : Finset Sig) : Prop :=
  (∀ a∈S, t>0 → neg a ∉ S → proper (neg a) → ∀ q : Bool, Next k (t-1) (insert (neg a) (cut S a q))) ∧
  (∀ a∈S, ∀ b∈S, a≠b → ∀ d : Bool, bin d a b ∉ S → proper (bin d a b) → ∀ q r : Bool,
    Next k t (insert (bin d a b) (cut (cut S a q) b r)))
def properDecision (a : Sig) : Decidable (proper a) := by unfold proper; infer_instance
def AU (k t : Nat) (S : Finset Sig) (a : Sig) : Prop := t>0 → neg a ∉ S → proper (neg a) → ∀ q : Bool, Next k (t-1) (insert (neg a) (cut S a q))
def unaryDecision (k t S a) : Decidable (AU k t S a) := by
  letI (j u : Nat) (v : Finset Sig) := nextDecision j u v
  letI (v : Sig) := properDecision v
  unfold AU
  infer_instance
def AB (k t : Nat) (S : Finset Sig) (a b : Sig) (d : Bool) : Prop := bin d a b ∉ S → proper (bin d a b) → ∀ q r : Bool, Next k t (insert (bin d a b) (cut (cut S a q) b r))
def binaryDecision (k t S a b d) : Decidable (AB k t S a b d) := by
  letI (j u : Nat) (v : Finset Sig) := nextDecision j u v
  letI (v : Sig) := properDecision v
  unfold AB
  infer_instance
def both (k t : Nat) (S: Finset Sig) (a b : Sig) : Prop := a ≠ b → ∀ d : Bool, AB k t S a b d
def pairDecision (k t S a b) : Decidable (both k t S a b) := by
  letI (d : Bool) := binaryDecision k t S a b d
  unfold both
  infer_instance
def decChk (k t S) : Decidable (Checked k t S) := by
  change Decidable ((∀ a ∈ S, AU k t S a) ∧ (∀ a ∈ S, ∀ b ∈ S, both k t S a b))
  exact @instDecidableAnd _ _
    (@Finset.decidableDforallFinset _ S _ (fun a _ => unaryDecision k t S a))
    (@Finset.decidableDforallFinset _ S _ (fun a _ =>
      @Finset.decidableDforallFinset _ S _ (fun b _ => pairDecision k t S a b)))


lemma no_run (checks : ∀ k t, k<6 → t≤6 → ∀ S∈bank (k+1) t, Checked k t S)
    {k t S} (hk:k≤6) (ht:t≤6) (hs : S∈bank k t) (h : Live target k t S) : False := by
  induction k generalizing t S with
  | zero => cases t <;> simp [bank] at hs
  | succ k ih =>
    have check := checks k t (by omega) ht S hs
    rcases h with ⟨u,U,a,rfl,rfl,_,hf,tail⟩ | ⟨U,a,b,d,rfl,_,_,ne,hf,tail⟩
    · have hnext := check.1 a (by simp) (by omega) hf (live_proper tail _ (by simp)) (decide (a∈U))
      rw [cut_back] at hnext
      have nx := hnext (live_size tail).2 (live_size tail).1 (sep_of_live tail)
      exact ih (by omega) (by omega) nx tail
    · have hnext := check.2 a (by simp) b (by simp) ne d hf (live_proper tail _ (by simp)) (decide (a∈U)) (decide (b∈U))
      rw [cut_comm a b ne,cut_back,cut_back] at hnext
      have nx := hnext (live_size tail).2 (live_size tail).1 (sep_of_live tail)
      exact ih (by omega) ht nx tail
def RootCheck (k t : Nat) : Prop := ∀ S∈raw.toFinset.powerset, Next k t S
def rootDecision (k t) : Decidable (RootCheck k t) :=
  @Finset.decidableDforallFinset _ raw.toFinset.powerset _ (fun S _=>nextDecision k t S)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck0_0 : (bank 1 0).all (fun S => @decide (Checked 0 0 S) (decChk 0 0 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root0_0 : RootCheck 0 0 := by
  exact @of_decide_eq_true _ (rootDecision 0 0) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck0_1 : (bank 1 1).all (fun S => @decide (Checked 0 1 S) (decChk 0 1 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root0_1 : RootCheck 0 1 := by
  exact @of_decide_eq_true _ (rootDecision 0 1) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck0_2 : (bank 1 2).all (fun S => @decide (Checked 0 2 S) (decChk 0 2 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root0_2 : RootCheck 0 2 := by
  exact @of_decide_eq_true _ (rootDecision 0 2) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck0_3 : (bank 1 3).all (fun S => @decide (Checked 0 3 S) (decChk 0 3 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root0_3 : RootCheck 0 3 := by
  exact @of_decide_eq_true _ (rootDecision 0 3) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck0_4 : (bank 1 4).all (fun S => @decide (Checked 0 4 S) (decChk 0 4 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root0_4 : RootCheck 0 4 := by
  exact @of_decide_eq_true _ (rootDecision 0 4) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck0_5 : (bank 1 5).all (fun S => @decide (Checked 0 5 S) (decChk 0 5 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root0_5 : RootCheck 0 5 := by
  exact @of_decide_eq_true _ (rootDecision 0 5) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck0_6 : (bank 1 6).all (fun S => @decide (Checked 0 6 S) (decChk 0 6 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root0_6 : RootCheck 0 6 := by
  exact @of_decide_eq_true _ (rootDecision 0 6) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck1_0 : (bank 2 0).all (fun S => @decide (Checked 1 0 S) (decChk 1 0 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root1_0 : RootCheck 1 0 := by
  exact @of_decide_eq_true _ (rootDecision 1 0) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck1_1 : (bank 2 1).all (fun S => @decide (Checked 1 1 S) (decChk 1 1 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root1_1 : RootCheck 1 1 := by
  exact @of_decide_eq_true _ (rootDecision 1 1) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck1_2 : (bank 2 2).all (fun S => @decide (Checked 1 2 S) (decChk 1 2 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root1_2 : RootCheck 1 2 := by
  exact @of_decide_eq_true _ (rootDecision 1 2) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck1_3 : (bank 2 3).all (fun S => @decide (Checked 1 3 S) (decChk 1 3 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root1_3 : RootCheck 1 3 := by
  exact @of_decide_eq_true _ (rootDecision 1 3) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck1_4 : (bank 2 4).all (fun S => @decide (Checked 1 4 S) (decChk 1 4 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root1_4 : RootCheck 1 4 := by
  exact @of_decide_eq_true _ (rootDecision 1 4) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck1_5 : (bank 2 5).all (fun S => @decide (Checked 1 5 S) (decChk 1 5 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root1_5 : RootCheck 1 5 := by
  exact @of_decide_eq_true _ (rootDecision 1 5) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck1_6 : (bank 2 6).all (fun S => @decide (Checked 1 6 S) (decChk 1 6 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root1_6 : RootCheck 1 6 := by
  exact @of_decide_eq_true _ (rootDecision 1 6) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck2_0 : (bank 3 0).all (fun S => @decide (Checked 2 0 S) (decChk 2 0 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root2_0 : RootCheck 2 0 := by
  exact @of_decide_eq_true _ (rootDecision 2 0) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck2_1 : (bank 3 1).all (fun S => @decide (Checked 2 1 S) (decChk 2 1 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root2_1 : RootCheck 2 1 := by
  exact @of_decide_eq_true _ (rootDecision 2 1) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck2_2 : (bank 3 2).all (fun S => @decide (Checked 2 2 S) (decChk 2 2 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root2_2 : RootCheck 2 2 := by
  exact @of_decide_eq_true _ (rootDecision 2 2) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck2_3 : (bank 3 3).all (fun S => @decide (Checked 2 3 S) (decChk 2 3 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root2_3 : RootCheck 2 3 := by
  exact @of_decide_eq_true _ (rootDecision 2 3) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck2_4 : (bank 3 4).all (fun S => @decide (Checked 2 4 S) (decChk 2 4 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root2_4 : RootCheck 2 4 := by
  exact @of_decide_eq_true _ (rootDecision 2 4) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck2_5 : (bank 3 5).all (fun S => @decide (Checked 2 5 S) (decChk 2 5 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root2_5 : RootCheck 2 5 := by
  exact @of_decide_eq_true _ (rootDecision 2 5) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck2_6 : (bank 3 6).all (fun S => @decide (Checked 2 6 S) (decChk 2 6 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root2_6 : RootCheck 2 6 := by
  exact @of_decide_eq_true _ (rootDecision 2 6) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck3_0 : (bank 4 0).all (fun S => @decide (Checked 3 0 S) (decChk 3 0 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root3_0 : RootCheck 3 0 := by
  exact @of_decide_eq_true _ (rootDecision 3 0) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck3_1 : (bank 4 1).all (fun S => @decide (Checked 3 1 S) (decChk 3 1 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root3_1 : RootCheck 3 1 := by
  exact @of_decide_eq_true _ (rootDecision 3 1) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck3_2 : (bank 4 2).all (fun S => @decide (Checked 3 2 S) (decChk 3 2 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root3_2 : RootCheck 3 2 := by
  exact @of_decide_eq_true _ (rootDecision 3 2) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck3_3 : (bank 4 3).all (fun S => @decide (Checked 3 3 S) (decChk 3 3 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root3_3 : RootCheck 3 3 := by
  exact @of_decide_eq_true _ (rootDecision 3 3) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck3_4 : (bank 4 4).all (fun S => @decide (Checked 3 4 S) (decChk 3 4 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root3_4 : RootCheck 3 4 := by
  exact @of_decide_eq_true _ (rootDecision 3 4) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck3_5 : (bank 4 5).all (fun S => @decide (Checked 3 5 S) (decChk 3 5 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root3_5 : RootCheck 3 5 := by
  exact @of_decide_eq_true _ (rootDecision 3 5) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck3_6 : (bank 4 6).all (fun S => @decide (Checked 3 6 S) (decChk 3 6 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root3_6 : RootCheck 3 6 := by
  exact @of_decide_eq_true _ (rootDecision 3 6) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck4_0 : (bank 5 0).all (fun S => @decide (Checked 4 0 S) (decChk 4 0 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root4_0 : RootCheck 4 0 := by
  exact @of_decide_eq_true _ (rootDecision 4 0) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck4_1 : (bank 5 1).all (fun S => @decide (Checked 4 1 S) (decChk 4 1 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root4_1 : RootCheck 4 1 := by
  exact @of_decide_eq_true _ (rootDecision 4 1) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck4_2 : (bank 5 2).all (fun S => @decide (Checked 4 2 S) (decChk 4 2 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root4_2 : RootCheck 4 2 := by
  exact @of_decide_eq_true _ (rootDecision 4 2) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck4_3 : (bank 5 3).all (fun S => @decide (Checked 4 3 S) (decChk 4 3 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root4_3 : RootCheck 4 3 := by
  exact @of_decide_eq_true _ (rootDecision 4 3) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck4_4 : (bank 5 4).all (fun S => @decide (Checked 4 4 S) (decChk 4 4 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root4_4 : RootCheck 4 4 := by
  exact @of_decide_eq_true _ (rootDecision 4 4) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck4_5 : (bank 5 5).all (fun S => @decide (Checked 4 5 S) (decChk 4 5 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root4_5 : RootCheck 4 5 := by
  exact @of_decide_eq_true _ (rootDecision 4 5) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck4_6 : (bank 5 6).all (fun S => @decide (Checked 4 6 S) (decChk 4 6 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root4_6 : RootCheck 4 6 := by
  exact @of_decide_eq_true _ (rootDecision 4 6) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck5_0 : (bank 6 0).all (fun S => @decide (Checked 5 0 S) (decChk 5 0 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root5_0 : RootCheck 5 0 := by
  exact @of_decide_eq_true _ (rootDecision 5 0) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck5_1 : (bank 6 1).all (fun S => @decide (Checked 5 1 S) (decChk 5 1 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root5_1 : RootCheck 5 1 := by
  exact @of_decide_eq_true _ (rootDecision 5 1) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck5_2 : (bank 6 2).all (fun S => @decide (Checked 5 2 S) (decChk 5 2 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root5_2 : RootCheck 5 2 := by
  exact @of_decide_eq_true _ (rootDecision 5 2) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck5_3 : (bank 6 3).all (fun S => @decide (Checked 5 3 S) (decChk 5 3 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root5_3 : RootCheck 5 3 := by
  exact @of_decide_eq_true _ (rootDecision 5 3) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck5_4 : (bank 6 4).all (fun S => @decide (Checked 5 4 S) (decChk 5 4 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root5_4 : RootCheck 5 4 := by
  exact @of_decide_eq_true _ (rootDecision 5 4) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck5_5 : (bank 6 5).all (fun S => @decide (Checked 5 5 S) (decChk 5 5 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root5_5 : RootCheck 5 5 := by
  exact @of_decide_eq_true _ (rootDecision 5 5) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma ck5_6 : (bank 6 6).all (fun S => @decide (Checked 5 6 S) (decChk 5 6 S)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root5_6 : RootCheck 5 6 := by
  exact @of_decide_eq_true _ (rootDecision 5 6) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root6_0 : RootCheck 6 0 := by
  exact @of_decide_eq_true _ (rootDecision 6 0) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root6_1 : RootCheck 6 1 := by
  exact @of_decide_eq_true _ (rootDecision 6 1) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root6_2 : RootCheck 6 2 := by
  exact @of_decide_eq_true _ (rootDecision 6 2) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root6_3 : RootCheck 6 3 := by
  exact @of_decide_eq_true _ (rootDecision 6 3) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root6_4 : RootCheck 6 4 := by
  exact @of_decide_eq_true _ (rootDecision 6 4) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root6_5 : RootCheck 6 5 := by
  exact @of_decide_eq_true _ (rootDecision 6 5) (by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
lemma root6_6 : RootCheck 6 6 := by
  exact @of_decide_eq_true _ (rootDecision 6 6) (by decide +kernel)
lemma checks : ∀ k t, k<6 → t≤6 → ∀ S∈bank (k+1) t, Checked k t S := by
  intro k t hk ht S hs
  interval_cases k <;> interval_cases t
  · exact @of_decide_eq_true _ (decChk 0 0 S) (List.all_eq_true.mp ck0_0 S hs)
  · exact @of_decide_eq_true _ (decChk 0 1 S) (List.all_eq_true.mp ck0_1 S hs)
  · exact @of_decide_eq_true _ (decChk 0 2 S) (List.all_eq_true.mp ck0_2 S hs)
  · exact @of_decide_eq_true _ (decChk 0 3 S) (List.all_eq_true.mp ck0_3 S hs)
  · exact @of_decide_eq_true _ (decChk 0 4 S) (List.all_eq_true.mp ck0_4 S hs)
  · exact @of_decide_eq_true _ (decChk 0 5 S) (List.all_eq_true.mp ck0_5 S hs)
  · exact @of_decide_eq_true _ (decChk 0 6 S) (List.all_eq_true.mp ck0_6 S hs)
  · exact @of_decide_eq_true _ (decChk 1 0 S) (List.all_eq_true.mp ck1_0 S hs)
  · exact @of_decide_eq_true _ (decChk 1 1 S) (List.all_eq_true.mp ck1_1 S hs)
  · exact @of_decide_eq_true _ (decChk 1 2 S) (List.all_eq_true.mp ck1_2 S hs)
  · exact @of_decide_eq_true _ (decChk 1 3 S) (List.all_eq_true.mp ck1_3 S hs)
  · exact @of_decide_eq_true _ (decChk 1 4 S) (List.all_eq_true.mp ck1_4 S hs)
  · exact @of_decide_eq_true _ (decChk 1 5 S) (List.all_eq_true.mp ck1_5 S hs)
  · exact @of_decide_eq_true _ (decChk 1 6 S) (List.all_eq_true.mp ck1_6 S hs)
  · exact @of_decide_eq_true _ (decChk 2 0 S) (List.all_eq_true.mp ck2_0 S hs)
  · exact @of_decide_eq_true _ (decChk 2 1 S) (List.all_eq_true.mp ck2_1 S hs)
  · exact @of_decide_eq_true _ (decChk 2 2 S) (List.all_eq_true.mp ck2_2 S hs)
  · exact @of_decide_eq_true _ (decChk 2 3 S) (List.all_eq_true.mp ck2_3 S hs)
  · exact @of_decide_eq_true _ (decChk 2 4 S) (List.all_eq_true.mp ck2_4 S hs)
  · exact @of_decide_eq_true _ (decChk 2 5 S) (List.all_eq_true.mp ck2_5 S hs)
  · exact @of_decide_eq_true _ (decChk 2 6 S) (List.all_eq_true.mp ck2_6 S hs)
  · exact @of_decide_eq_true _ (decChk 3 0 S) (List.all_eq_true.mp ck3_0 S hs)
  · exact @of_decide_eq_true _ (decChk 3 1 S) (List.all_eq_true.mp ck3_1 S hs)
  · exact @of_decide_eq_true _ (decChk 3 2 S) (List.all_eq_true.mp ck3_2 S hs)
  · exact @of_decide_eq_true _ (decChk 3 3 S) (List.all_eq_true.mp ck3_3 S hs)
  · exact @of_decide_eq_true _ (decChk 3 4 S) (List.all_eq_true.mp ck3_4 S hs)
  · exact @of_decide_eq_true _ (decChk 3 5 S) (List.all_eq_true.mp ck3_5 S hs)
  · exact @of_decide_eq_true _ (decChk 3 6 S) (List.all_eq_true.mp ck3_6 S hs)
  · exact @of_decide_eq_true _ (decChk 4 0 S) (List.all_eq_true.mp ck4_0 S hs)
  · exact @of_decide_eq_true _ (decChk 4 1 S) (List.all_eq_true.mp ck4_1 S hs)
  · exact @of_decide_eq_true _ (decChk 4 2 S) (List.all_eq_true.mp ck4_2 S hs)
  · exact @of_decide_eq_true _ (decChk 4 3 S) (List.all_eq_true.mp ck4_3 S hs)
  · exact @of_decide_eq_true _ (decChk 4 4 S) (List.all_eq_true.mp ck4_4 S hs)
  · exact @of_decide_eq_true _ (decChk 4 5 S) (List.all_eq_true.mp ck4_5 S hs)
  · exact @of_decide_eq_true _ (decChk 4 6 S) (List.all_eq_true.mp ck4_6 S hs)
  · exact @of_decide_eq_true _ (decChk 5 0 S) (List.all_eq_true.mp ck5_0 S hs)
  · exact @of_decide_eq_true _ (decChk 5 1 S) (List.all_eq_true.mp ck5_1 S hs)
  · exact @of_decide_eq_true _ (decChk 5 2 S) (List.all_eq_true.mp ck5_2 S hs)
  · exact @of_decide_eq_true _ (decChk 5 3 S) (List.all_eq_true.mp ck5_3 S hs)
  · exact @of_decide_eq_true _ (decChk 5 4 S) (List.all_eq_true.mp ck5_4 S hs)
  · exact @of_decide_eq_true _ (decChk 5 5 S) (List.all_eq_true.mp ck5_5 S hs)
  · exact @of_decide_eq_true _ (decChk 5 6 S) (List.all_eq_true.mp ck5_6 S hs)
lemma roots : ∀ k t, k≤6 → t≤6 → RootCheck k t := by
  intro k t hk ht
  interval_cases k <;> interval_cases t
  · exact root0_0
  · exact root0_1
  · exact root0_2
  · exact root0_3
  · exact root0_4
  · exact root0_5
  · exact root0_6
  · exact root1_0
  · exact root1_1
  · exact root1_2
  · exact root1_3
  · exact root1_4
  · exact root1_5
  · exact root1_6
  · exact root2_0
  · exact root2_1
  · exact root2_2
  · exact root2_3
  · exact root2_4
  · exact root2_5
  · exact root2_6
  · exact root3_0
  · exact root3_1
  · exact root3_2
  · exact root3_3
  · exact root3_4
  · exact root3_5
  · exact root3_6
  · exact root4_0
  · exact root4_1
  · exact root4_2
  · exact root4_3
  · exact root4_4
  · exact root4_5
  · exact root4_6
  · exact root5_0
  · exact root5_1
  · exact root5_2
  · exact root5_3
  · exact root5_4
  · exact root5_5
  · exact root5_6
  · exact root6_0
  · exact root6_1
  · exact root6_2
  · exact root6_3
  · exact root6_4
  · exact root6_5
  · exact root6_6

open PEqualNP.MetaComplexity
def sampleInput (i : Fin 13) (v : Fin 5) : Bool := (rowNums.getD i.val 0).testBit v.val
theorem excludes (f : (Fin 5 → Bool) → Bool) (has : HasCircuitSize 5 f 6)
    (rows : ∀ i : Fin 13, f (sampleInput i) = bit i target) : False := by
  obtain ⟨C,hm,hsize,he⟩ := has
  have images : ∀ i : Fin 13, raw.map (bit i) = List.ofFn (sampleInput i) := by intro i; fin_cases i <;> decide
  have out : (execute C.gates raw).getD C.output zero = target := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let i : Fin 13 := ⟨j,hj⟩
    change bit i ((execute C.gates raw).getD C.output zero) = bit i target
    rw [← b_read,execute_bits _ _ _ (fun v hv => (hm v hv).1),images,←rows]
    exact he _
  have prop : proper target := by unfold proper; decide
  have rep := get_rep (execute C.gates raw) C.output
  rw [out] at rep
  have mem : target ∈ execute C.gates raw := rep.resolve_right (fun h => h prop)
  obtain ⟨k,t,S,hlen,live,sub⟩ := extract C.gates raw hm prop mem
  have bounds := live_size live
  change C.gates.length ≤ 6 at hsize
  have hk : k≤6 := by omega
  have ht : t≤6 := by omega
  have root := roots k t hk ht S (Finset.mem_powerset.mpr (fun v hv => List.mem_toFinset.mpr (sub v hv)))
  exact no_run checks hk ht (root bounds.2 bounds.1 (sep_of_live live)) live
end PEqualNP.Outside.L_meta_8686_aux

namespace PEqualNP.Outside.L_meta_8686_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def table (x : Fin 5→Bool) := Nat.testBit 0xeae8ea88 (∑ i : Fin 5, if x i then 2^i.val else 0)
def upper : Circuit := ⟨[⟨.and,[0,1]⟩,⟨.or,[5,3]⟩,⟨.and,[1,2]⟩,⟨.or,[0,7]⟩,⟨.and,[2,4]⟩,⟨.or,[9,6]⟩,⟨.and,[8,10]⟩],11⟩
theorem upper_mono : Monotone2 upper := by
  intro g hg
  simp only [upper,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
theorem upper_ok : ∀x : Fin 5→Bool,upper.eval (List.ofFn x)=table x := by decide +kernel
theorem rows_ok : ∀i : Fin 13, table (sampleInput i)=bit i target := by decide +kernel
end PEqualNP.Outside.L_meta_8686_aux
theorem PEqualNP.Outside.L_meta_8686 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xeae8ea88 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeae8ea88 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have good : 7 ≤ s := by
    by_contra! small
    obtain ⟨C,ops,size,eq⟩ := h
    exact PEqualNP.Outside.L_meta_8686_aux.excludes _ ⟨C,ops,by omega,eq⟩ PEqualNP.Outside.L_meta_8686_aux.rows_ok
  exact ⟨PEqualNP.Outside.L_meta_8686_aux.upper,PEqualNP.Outside.L_meta_8686_aux.upper_mono,good,
    PEqualNP.Outside.L_meta_8686_aux.upper_ok⟩
