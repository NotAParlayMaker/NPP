import PEqualNP.Defs
import Mathlib

-- The live-set extraction is adapted from the checked L_meta_4807.
namespace PEqualNP.Outside.L_meta_5552_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
abbrev Sig := BitVec 16
def zero : Sig := 0
def one : Sig := BitVec.allOnes 16
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

def Live (target : Sig) : Nat → Finset Sig → Prop
  | 0, S => S = {target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Bool), S=insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live target k (insert (bin d a b) U)

lemma live_proper {k S} (h : Live T k S) : ∀ a ∈ S, proper a := by
  induction k generalizing S with
  | zero => obtain ⟨rfl,hp⟩ := h; simpa using hp
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,ha,hb,_,_,tail⟩ := h
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun x hx => ih tail _ (Finset.mem_insert_of_mem hx)⟩
lemma live_size {k S} (h : Live T k S) : S.card ≤ k+1 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl,_⟩ := h; simp
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,ha,hb,_,hf,tail⟩ := h
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have bound := ih tail
    rw [Finset.card_insert_of_notMem hu] at bound
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega
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
  exact Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  cases l with
  | nil =>
    rcases ho with rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)

private lemma pull_gate {w : List Sig} {z : Sig} {k S} (h : Live target k S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+1 ∧ Live target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,⟨U,a,b,d,rfl,pa,pb,hab,hf,ht⟩,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k S, k ≤ gs.length ∧ Live target k S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,⟨rfl,hp⟩,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,T,by simp; omega,hu,hT⟩
def bit (i : Fin 16) (a : Sig) : Bool := a.getLsbD i.val
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

abbrev Row := Fin 16
def target : Sig := 4398
def raw : List Sig := [15,240,3840,61440,4369,8738,17476,34952]

lemma separates {k S} (h : Live T k S) {r s : Row} (hp : bit r T=true) (hn : bit s T=false) :
    ∃ a ∈ S, bit r a=true ∧ bit s a=false := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := h
    exact ⟨T,by simp,hp,hn⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩ := h
    obtain ⟨v,hv,pos,negRow⟩ := ih tail
    rcases Finset.mem_insert.mp hv with rfl|hu
    · rw [bit_bin] at pos negRow
      cases d <;> cases e : bit r a <;> cases f : bit s a <;>
        cases g : bit r b <;> cases i : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),pos,negRow⟩

def nextSet (S : Finset Sig) (a b : Sig) (d : Bool) := insert (bin d a b) ((S.erase a).erase b)

def rec3_0 : List Sig × List Nat := ([15,4352,8738,52476],[0,0,0,128,36,16,25,32,0,128,0,0,0,137,0,132,36,16,0,137,0,0,16,84,25,32,0,132,16,84,0,0])
def rec3_1 : List Sig × List Nat := ([15,4593,52428,65314],[0,0,25,38,25,26,38,16,25,38,0,0,32,32,16,16,25,26,32,32,0,0,16,86,38,16,16,16,16,86,0,0])
def rec3_2 : List Sig × List Nat := ([240,4383,8738,65484],[0,0,25,38,16,20,32,36,25,38,0,0,38,16,25,25,16,20,38,16,0,0,16,86,32,36,25,25,16,86,0,0])
def rec3_3 : List Sig × List Nat := ([240,4383,12066,64716],[0,0,25,38,16,20,32,36,25,38,0,0,38,16,25,26,16,20,38,16,0,0,16,86,32,36,25,26,16,86,0,0])
def rec3_4 : List Sig × List Nat := ([240,4383,52428,65314],[0,0,25,38,32,36,16,20,25,38,0,0,25,26,38,16,32,36,25,26,0,0,16,86,16,20,38,16,16,86,0,0])
def rec3_5 : List Sig × List Nat := ([240,4383,53196,61986],[0,0,25,38,32,36,16,20,25,38,0,0,25,25,38,16,32,36,25,25,0,0,16,86,16,20,38,16,16,86,0,0])
def rec4_0 : List Sig × List Nat := ([15,240,4352,8738,52428],[0,0,0,38,0,128,38,16,25,32,0,38,0,0,0,132,16,84,32,256,0,128,0,132,0,0,0,137,0,134,38,16,16,84,0,137,0,0,0,86,25,32,32,256,0,134,0,86,0,0])
def rec4_1 : List Sig × List Nat := ([15,240,4369,8738,65484],[0,0,0,38,25,258,38,16,25,25,0,38,0,0,89,134,16,84,32,89,25,258,89,134,0,0,0,16,32,32,38,16,16,84,0,16,0,0,16,86,25,25,32,89,32,32,16,86,0,0])
def rec4_2 : List Sig × List Nat := ([15,240,4369,12066,64716],[0,0,0,38,25,259,38,16,25,26,0,38,0,0,89,198,16,84,32,90,25,259,89,198,0,0,16,16,32,32,38,16,16,84,16,16,0,0,16,86,25,26,32,90,32,32,16,86,0,0])
def rec4_3 : List Sig × List Nat := ([15,240,4369,52428,65314],[0,0,0,38,25,260,25,26,38,16,0,38,0,0,89,257,32,90,16,84,25,260,89,257,0,0,0,32,16,16,25,26,32,90,0,32,0,0,16,86,38,16,16,84,16,16,16,86,0,0])
def rec4_4 : List Sig × List Nat := ([15,240,4369,53196,61986],[0,0,0,38,25,261,25,25,38,16,0,38,0,0,89,134,32,89,16,84,25,261,89,134,0,0,32,32,16,16,25,25,32,89,32,32,0,0,16,86,38,16,16,84,16,16,16,86,0,0])
def rec4_5 : List Sig × List Nat := ([15,3840,4593,52428,61986],[0,0,0,25,25,38,25,30,38,16,0,25,0,0,89,89,32,134,16,257,25,38,89,89,0,0,32,32,16,16,25,30,32,134,32,32,0,0,16,86,38,16,16,257,16,16,16,86,0,0])
def rec4_6 : List Sig × List Nat := ([15,4352,8738,17476,35064],[0,0,0,128,38,16,25,32,25,38,0,128,0,0,0,137,0,134,0,132,38,16,0,137,0,0,0,86,16,84,25,32,0,134,0,86,0,0,32,256,25,38,0,132,16,84,32,256,0,0])
def rec4_7 : List Sig × List Nat := ([15,4352,8738,17652,34952],[0,0,0,128,36,16,25,32,25,39,0,128,0,0,0,137,0,132,0,135,36,16,0,137,0,0,16,84,0,87,25,32,0,132,16,84,0,0,32,256,25,39,0,135,0,87,32,256,0,0])
def rec4_8 : List Sig × List Nat := ([15,4369,8738,17652,65416],[0,0,25,36,36,16,25,32,25,25,25,36,0,0,0,16,32,32,48,48,36,16,0,16,0,0,16,84,16,87,25,32,32,32,16,84,0,0,32,89,25,25,48,48,16,87,32,89,0,0])
def rec4_9 : List Sig × List Nat := ([15,4369,8738,35064,65348],[0,0,25,52,38,16,25,38,25,25,25,52,0,0,0,16,48,48,32,32,38,16,0,16,0,0,16,84,16,86,25,38,48,48,16,84,0,0,32,89,25,25,32,32,16,86,32,89,0,0])
def rec4_10 : List Sig × List Nat := ([15,4369,8738,52476,65280],[0,0,25,36,36,16,25,32,0,25,25,36,0,0,0,16,32,32,256,128,36,16,0,16,0,0,16,84,16,90,25,32,32,32,16,84,0,0,32,89,0,25,256,128,16,90,32,89,0,0])
def rec4_11 : List Sig × List Nat := ([15,4593,8738,52428,65280],[0,0,25,38,38,16,25,32,0,25,25,38,0,0,16,16,32,32,89,89,38,16,16,16,0,0,0,86,16,257,25,32,32,32,0,86,0,0,32,134,0,25,89,89,16,257,32,134,0,0])
def rec4_12 : List Sig × List Nat := ([15,4593,12066,52428,61440],[0,0,25,38,38,16,25,26,0,29,25,38,0,0,16,16,32,32,89,93,38,16,16,16,0,0,16,86,16,257,25,26,32,32,16,86,0,0,32,198,0,29,89,93,16,257,32,198,0,0])
def rec4_13 : List Sig × List Nat := ([15,4593,17476,34952,65314],[0,0,25,38,25,26,25,27,38,16,25,38,0,0,32,32,48,48,16,16,25,26,32,32,0,0,0,257,16,86,25,27,48,48,0,257,0,0,16,87,38,16,16,16,16,86,16,87,0,0])
def rec4_14 : List Sig × List Nat := ([240,3840,4383,8738,64716],[0,0,0,89,25,38,16,20,32,36,0,89,0,0,25,25,16,259,32,258,25,38,25,25,0,0,38,16,25,29,16,20,16,259,38,16,0,0,16,86,32,36,32,258,25,29,16,86,0,0])
def rec4_15 : List Sig × List Nat := ([240,3840,4383,52428,61986],[0,0,0,89,25,38,32,36,16,20,0,89,0,0,25,25,32,261,16,260,25,38,25,25,0,0,25,30,38,16,32,36,32,261,25,30,0,0,16,86,16,20,16,260,38,16,16,86,0,0])
def rec4_16 : List Sig × List Nat := ([240,4383,8738,17476,65416],[0,0,25,38,16,20,32,36,48,52,25,38,0,0,38,16,25,32,25,25,16,20,38,16,0,0,0,86,16,87,32,36,25,32,0,86,0,0,32,258,48,52,25,25,16,87,32,258,0,0])
def rec4_17 : List Sig × List Nat := ([240,4383,8738,20292,63624],[0,0,25,38,16,20,32,36,48,52,25,38,0,0,38,16,25,25,25,29,16,20,38,16,0,0,16,86,16,87,32,36,25,25,16,86,0,0,32,258,48,52,25,29,16,87,32,258,0,0])
def rec4_18 : List Sig × List Nat := ([240,4383,8738,34952,65348],[0,0,25,38,16,20,48,52,32,36,25,38,0,0,38,16,25,43,25,25,16,20,38,16,0,0,0,87,16,86,48,52,25,43,0,87,0,0,32,258,32,36,25,25,16,86,32,258,0,0])
def rec4_19 : List Sig × List Nat := ([240,4383,8738,36744,62532],[0,0,25,38,16,20,48,52,32,36,25,38,0,0,38,16,25,25,25,29,16,20,38,16,0,0,16,87,16,86,48,52,25,25,16,87,0,0,32,258,32,36,25,29,16,86,32,258,0,0])
def rec4_20 : List Sig × List Nat := ([240,4383,8738,52428,65280],[0,0,25,38,16,20,32,36,0,89,25,38,0,0,38,16,25,32,25,25,16,20,38,16,0,0,0,86,16,260,32,36,25,32,0,86,0,0,32,258,0,89,25,25,16,260,32,258,0,0])
def rec4_21 : List Sig × List Nat := ([240,4383,8738,53196,61440],[0,0,25,38,16,20,32,36,0,93,25,38,0,0,38,16,25,25,25,29,16,20,38,16,0,0,16,86,16,261,32,36,25,25,16,86,0,0,32,258,0,93,25,29,16,261,32,258,0,0])
def rec4_22 : List Sig × List Nat := ([240,4383,12066,17476,63624],[0,0,25,38,16,20,32,36,48,52,25,38,0,0,38,16,25,26,25,27,16,20,38,16,0,0,16,86,16,87,32,36,25,26,16,86,0,0,32,259,48,52,25,27,16,87,32,259,0,0])
def rec4_23 : List Sig × List Nat := ([240,4383,12066,34952,62532],[0,0,25,38,16,20,48,52,32,36,25,38,0,0,38,16,25,27,25,26,16,20,38,16,0,0,16,87,16,86,48,52,25,27,16,87,0,0,32,259,32,36,25,26,16,86,32,259,0,0])
def rec4_24 : List Sig × List Nat := ([240,4383,12066,52428,61440],[0,0,25,38,16,20,32,36,0,93,25,38,0,0,38,16,25,26,25,29,16,20,38,16,0,0,16,86,16,260,32,36,25,26,16,86,0,0,32,259,0,93,25,29,16,260,32,259,0,0])
def rec4_25 : List Sig × List Nat := ([240,4383,17476,34952,65314],[0,0,25,38,32,36,48,52,16,20,25,38,0,0,25,26,25,27,38,16,32,36,25,26,0,0,0,260,16,86,48,52,25,27,0,260,0,0,16,87,16,20,38,16,16,86,16,87,0,0])
def rec4_26 : List Sig × List Nat := ([240,4383,17476,36744,61986],[0,0,25,38,32,36,48,52,16,20,25,38,0,0,25,30,25,25,38,16,32,36,25,30,0,0,32,261,16,86,48,52,25,25,32,261,0,0,16,87,16,20,38,16,16,86,16,87,0,0])
def rec4_27 : List Sig × List Nat := ([240,4383,20292,34952,61986],[0,0,25,38,32,36,48,52,16,20,25,38,0,0,25,25,25,31,38,16,32,36,25,25,0,0,32,261,16,86,48,52,25,31,32,261,0,0,16,87,16,20,38,16,16,86,16,87,0,0])
def rec5_0 : List Sig × List Nat := ([15,240,3840,4369,8738,64716],[0,0,0,38,0,25,25,270,38,16,25,29,0,38,0,0,0,89,89,198,16,84,32,93,0,25,0,89,0,0,198,128,16,258,32,257,25,270,89,198,198,128,0,0,0,16,32,32,38,16,16,84,16,258,0,16,0,0,16,86,25,29,32,93,32,257,32,32,16,86,0,0])
def rec5_1 : List Sig × List Nat := ([15,240,3840,4369,52428,61986],[0,0,0,38,0,25,25,271,25,30,38,16,0,38,0,0,0,89,89,261,32,94,16,84,0,25,0,89,0,0,201,128,32,260,16,259,25,271,89,261,201,128,0,0,0,32,16,16,25,30,32,94,32,260,0,32,0,0,16,86,38,16,16,84,16,259,16,16,16,86,0,0])
def rec5_2 : List Sig × List Nat := ([15,240,4352,8738,17476,34952],[0,0,0,38,0,128,38,16,25,32,25,48,0,38,0,0,0,132,16,84,32,263,48,262,0,128,0,132,0,0,0,137,0,134,0,135,38,16,16,84,0,137,0,0,0,86,0,87,25,32,32,263,0,134,0,86,0,0,0,256,25,48,48,262,0,135,0,87,0,256,0,0])
def rec5_3 : List Sig × List Nat := ([15,240,4369,8738,17476,65416],[0,0,0,38,25,272,38,16,25,32,25,25,0,38,0,0,89,135,16,84,32,264,48,89,25,272,89,135,0,0,0,16,0,32,48,48,38,16,16,84,0,16,0,0,0,86,16,87,25,32,32,264,0,32,0,86,0,0,32,257,25,25,48,89,48,48,16,87,32,257,0,0])
def rec5_4 : List Sig × List Nat := ([15,240,4369,8738,20292,63624],[0,0,0,38,25,273,38,16,25,25,25,29,0,38,0,0,89,134,16,84,32,89,48,93,25,273,89,134,0,0,0,16,32,32,48,48,38,16,16,84,0,16,0,0,16,86,16,87,25,25,32,89,32,32,16,86,0,0,32,257,25,29,48,93,48,48,16,87,32,257,0,0])
def rec5_5 : List Sig × List Nat := ([15,240,4369,8738,34952,65348],[0,0,0,38,25,274,38,16,25,43,25,25,0,38,0,0,89,134,16,84,48,265,32,89,25,274,89,134,0,0,0,16,0,48,32,32,38,16,16,84,0,16,0,0,0,87,16,86,25,43,48,265,0,48,0,87,0,0,32,257,25,25,32,89,32,32,16,86,32,257,0,0])
def rec5_6 : List Sig × List Nat := ([15,240,4369,8738,36744,62532],[0,0,0,38,25,275,38,16,25,25,25,29,0,38,0,0,89,135,16,84,48,89,32,93,25,275,89,135,0,0,0,16,48,48,32,32,38,16,16,84,0,16,0,0,16,87,16,86,25,25,48,89,48,48,16,87,0,0,32,257,25,29,32,93,32,32,16,86,32,257,0,0])
def rec5_7 : List Sig × List Nat := ([15,240,4369,8738,52428,65280],[0,0,0,38,25,276,38,16,25,32,0,25,0,38,0,0,89,267,16,84,32,266,0,89,25,276,89,267,0,0,0,16,0,32,256,128,38,16,16,84,0,16,0,0,0,86,16,259,25,32,32,266,0,32,0,86,0,0,32,257,0,25,0,89,256,128,16,259,32,257,0,0])
def rec5_8 : List Sig × List Nat := ([15,240,4369,8738,53196,61440],[0,0,0,38,25,277,38,16,25,25,0,29,0,38,0,0,89,134,16,84,32,89,0,93,25,277,89,134,0,0,0,16,32,32,134,142,38,16,16,84,0,16,0,0,16,86,16,260,25,25,32,89,32,32,16,86,0,0,32,257,0,29,0,93,134,142,16,260,32,257,0,0])
def rec5_9 : List Sig × List Nat := ([15,240,4369,12066,17476,63624],[0,0,0,38,25,278,38,16,25,26,25,27,0,38,0,0,89,199,16,84,32,90,48,91,25,278,89,199,0,0,16,16,0,32,48,48,38,16,16,84,16,16,0,0,16,86,16,87,25,26,32,90,0,32,16,86,0,0,32,258,25,27,48,91,48,48,16,87,32,258,0,0])
def rec5_10 : List Sig × List Nat := ([15,240,4369,12066,34952,62532],[0,0,0,38,25,279,38,16,25,27,25,26,0,38,0,0,89,198,16,84,48,91,32,90,25,279,89,198,0,0,16,16,0,48,32,32,38,16,16,84,16,16,0,0,16,87,16,86,25,27,48,91,0,48,16,87,0,0,32,258,25,26,32,90,32,32,16,86,32,258,0,0])
def rec5_11 : List Sig × List Nat := ([15,240,4369,12066,52428,61440],[0,0,0,38,25,280,38,16,25,26,0,29,0,38,0,0,89,268,16,84,32,90,0,93,25,280,89,268,0,0,16,16,0,32,137,141,38,16,16,84,16,16,0,0,16,86,16,259,25,26,32,90,0,32,16,86,0,0,32,258,0,29,0,93,137,141,16,259,32,258,0,0])
def rec5_12 : List Sig × List Nat := ([15,240,4369,17476,34952,65314],[0,0,0,38,25,281,25,26,25,27,38,16,0,38,0,0,89,269,32,90,48,91,16,84,25,281,89,269,0,0,0,32,0,48,16,16,25,26,32,90,0,32,0,0,0,259,16,86,25,27,48,91,0,48,0,259,0,0,16,87,38,16,16,84,16,16,16,86,16,87,0,0])
def rec5_13 : List Sig × List Nat := ([15,240,4369,17476,36744,61986],[0,0,0,38,25,282,25,30,25,25,38,16,0,38,0,0,89,135,32,94,48,89,16,84,25,282,89,135,0,0,0,32,48,48,16,16,25,30,32,94,0,32,0,0,32,260,16,86,25,25,48,89,48,48,32,260,0,0,16,87,38,16,16,84,16,16,16,86,16,87,0,0])
def rec5_14 : List Sig × List Nat := ([15,240,4369,20292,34952,61986],[0,0,0,38,25,283,25,25,25,31,38,16,0,38,0,0,89,134,32,89,48,95,16,84,25,283,89,134,0,0,32,32,0,48,16,16,25,25,32,89,32,32,0,0,32,260,16,86,25,31,48,95,0,48,32,260,0,0,16,87,38,16,16,84,16,16,16,86,16,87,0,0])
def rec5_15 : List Sig × List Nat := ([15,3840,4369,8738,17652,63624],[0,0,0,25,25,36,36,16,25,32,25,29,0,25,0,0,199,128,16,90,32,89,48,264,25,36,199,128,0,0,0,16,32,32,48,48,36,16,16,90,0,16,0,0,16,84,16,87,25,32,32,89,32,32,16,84,0,0,32,93,25,29,48,264,48,48,16,87,32,93,0,0])
def rec5_16 : List Sig × List Nat := ([15,3840,4369,8738,35064,62532],[0,0,0,25,25,52,38,16,25,38,25,29,0,25,0,0,198,128,16,91,48,89,32,265,25,52,198,128,0,0,0,16,48,48,32,32,38,16,16,91,0,16,0,0,16,84,16,86,25,38,48,89,48,48,16,84,0,0,32,93,25,29,32,265,32,32,16,86,32,93,0,0])
def rec5_17 : List Sig × List Nat := ([15,3840,4369,8738,52476,61440],[0,0,0,25,25,36,36,16,25,32,0,29,0,25,0,0,205,128,16,90,32,89,0,266,25,36,205,128,0,0,0,16,32,32,137,192,36,16,16,90,0,16,0,0,16,84,16,94,25,32,32,89,32,32,16,84,0,0,32,93,0,29,0,266,137,192,16,94,32,93,0,0])
def rec5_18 : List Sig × List Nat := ([15,3840,4593,8738,52428,61440],[0,0,0,25,25,38,38,16,25,32,0,29,0,25,0,0,89,89,16,268,32,134,0,267,25,38,89,89,0,0,16,16,32,32,89,93,38,16,16,268,16,16,0,0,0,86,16,261,25,32,32,134,32,32,0,86,0,0,32,198,0,29,0,267,89,93,16,261,32,198,0,0])
def rec5_19 : List Sig × List Nat := ([15,3840,4593,17476,34952,61986],[0,0,0,25,25,38,25,30,25,31,38,16,0,25,0,0,89,89,32,134,48,135,16,269,25,38,89,89,0,0,32,32,48,48,16,16,25,30,32,134,32,32,0,0,0,261,16,86,25,31,48,135,48,48,0,261,0,0,16,87,38,16,16,269,16,16,16,86,16,87,0,0])
def rec5_20 : List Sig × List Nat := ([15,4369,8738,17476,35064,65280],[0,0,25,52,38,16,25,32,25,38,0,25,25,52,0,0,0,16,0,32,48,48,262,128,38,16,0,16,0,0,0,86,16,84,16,91,25,32,0,32,0,86,0,0,32,266,32,265,25,38,48,48,16,84,32,266,0,0,48,89,0,25,262,128,16,91,32,265,48,89,0,0])
def rec5_21 : List Sig × List Nat := ([15,4369,8738,17652,34952,65280],[0,0,25,36,36,16,25,32,25,39,0,25,25,36,0,0,0,16,32,32,0,48,263,128,36,16,0,16,0,0,16,84,0,87,16,90,25,32,32,32,16,84,0,0,32,266,32,89,25,39,0,48,0,87,32,266,0,0,48,264,0,25,263,128,16,90,32,89,48,264,0,0])
def rec5_22 : List Sig × List Nat := ([15,4369,8738,17652,36744,61440],[0,0,25,36,36,16,25,32,25,25,0,29,25,36,0,0,0,16,32,32,48,48,135,143,36,16,0,16,0,0,16,84,16,87,16,94,25,32,32,32,16,84,0,0,32,89,32,93,25,25,48,48,16,87,32,89,0,0,48,264,0,29,135,143,16,94,32,93,48,264,0,0])
def rec5_23 : List Sig × List Nat := ([15,4369,8738,20292,35064,61440],[0,0,25,52,38,16,25,25,25,38,0,29,25,52,0,0,0,16,32,32,48,48,134,142,38,16,0,16,0,0,16,86,16,84,16,95,25,25,32,32,16,86,0,0,32,89,32,265,25,38,48,48,16,84,32,89,0,0,48,93,0,29,134,142,16,95,32,265,48,93,0,0])
def rec5_24 : List Sig × List Nat := ([15,4593,8738,17476,34952,65280],[0,0,25,38,38,16,25,32,25,48,0,25,25,38,0,0,16,16,32,32,48,48,89,89,38,16,16,16,0,0,0,86,0,87,16,269,25,32,32,32,0,86,0,0,0,267,32,134,25,48,48,48,0,87,0,267,0,0,48,135,0,25,89,89,16,269,32,134,48,135,0,0])
def rec5_25 : List Sig × List Nat := ([15,4593,12066,17476,34952,61440],[0,0,25,38,38,16,25,26,25,27,0,29,25,38,0,0,16,16,32,32,48,48,89,93,38,16,16,16,0,0,16,86,16,87,16,269,25,26,32,32,16,86,0,0,0,268,32,198,25,27,48,48,16,87,0,268,0,0,48,199,0,29,89,93,16,269,32,198,48,199,0,0])
def rec5_26 : List Sig × List Nat := ([240,3840,4383,8738,17476,63624],[0,0,0,89,25,38,16,20,32,36,48,52,0,89,0,0,25,25,16,278,32,273,48,272,25,38,25,25,0,0,38,16,25,32,25,29,16,20,16,278,38,16,0,0,0,86,16,87,32,36,32,273,25,32,0,86,0,0,32,270,48,52,48,272,25,29,16,87,32,270,0,0])
def rec5_27 : List Sig × List Nat := ([240,3840,4383,8738,34952,62532],[0,0,0,89,25,38,16,20,48,52,32,36,0,89,0,0,25,25,16,279,48,275,32,274,25,38,25,25,0,0,38,16,25,47,25,29,16,20,16,279,38,16,0,0,0,87,16,86,48,52,48,275,25,47,0,87,0,0,32,270,32,36,32,274,25,29,16,86,32,270,0,0])
def rec5_28 : List Sig × List Nat := ([240,3840,4383,8738,52428,61440],[0,0,0,89,25,38,16,20,32,36,0,93,0,89,0,0,25,25,16,280,32,277,0,276,25,38,25,25,0,0,38,16,25,32,25,29,16,20,16,280,38,16,0,0,0,86,16,271,32,36,32,277,25,32,0,86,0,0,32,270,0,93,0,276,25,29,16,271,32,270,0,0])
def rec5_29 : List Sig × List Nat := ([240,3840,4383,17476,34952,61986],[0,0,0,89,25,38,32,36,48,52,16,20,0,89,0,0,25,25,32,283,48,282,16,281,25,38,25,25,0,0,25,30,25,31,38,16,32,36,32,283,25,30,0,0,0,271,16,86,48,52,48,282,25,31,0,271,0,0,16,87,16,20,16,281,38,16,16,86,16,87,0,0])
def rec5_30 : List Sig × List Nat := ([240,4383,8738,17476,34952,65280],[0,0,25,38,16,20,32,36,48,52,0,89,25,38,0,0,38,16,25,32,25,48,25,25,16,20,38,16,0,0,0,86,0,87,16,281,32,36,25,32,0,86,0,0,0,276,32,274,48,52,25,48,0,87,0,276,0,0,48,272,0,89,25,25,16,281,32,274,48,272,0,0])
def rec5_31 : List Sig × List Nat := ([240,4383,8738,17476,36744,61440],[0,0,25,38,16,20,32,36,48,52,0,93,25,38,0,0,38,16,25,32,25,25,25,29,16,20,38,16,0,0,0,86,16,87,16,282,32,36,25,32,0,86,0,0,32,277,32,275,48,52,25,25,16,87,32,277,0,0,48,272,0,93,25,29,16,282,32,275,48,272,0,0])
def rec5_32 : List Sig × List Nat := ([240,4383,8738,20292,34952,61440],[0,0,25,38,16,20,32,36,48,52,0,93,25,38,0,0,38,16,25,25,25,43,25,29,16,20,38,16,0,0,16,86,0,87,16,283,32,36,25,25,16,86,0,0,32,277,32,274,48,52,25,43,0,87,32,277,0,0,48,273,0,93,25,29,16,283,32,274,48,273,0,0])
def rec5_33 : List Sig × List Nat := ([240,4383,12066,17476,34952,61440],[0,0,25,38,16,20,32,36,48,52,0,93,25,38,0,0,38,16,25,26,25,27,25,29,16,20,38,16,0,0,16,86,16,87,16,281,32,36,25,26,16,86,0,0,0,280,32,279,48,52,25,27,16,87,0,280,0,0,48,278,0,93,25,29,16,281,32,279,48,278,0,0])
def rec6_0 : List Sig × List Nat := ([15,240,3840,4369,8738,17476,63624],[0,0,0,38,0,25,25,282,38,16,25,32,25,29,0,38,0,0,0,89,89,199,16,84,32,271,48,93,0,25,0,89,0,0,199,128,16,265,32,260,48,259,25,282,89,199,199,128,0,0,0,16,0,32,48,48,38,16,16,84,16,265,0,16,0,0,0,86,16,87,25,32,32,271,32,260,0,32,0,86,0,0,32,256,25,29,48,93,48,259,48,48,16,87,32,256,0,0])
def rec6_1 : List Sig × List Nat := ([15,240,3840,4369,8738,34952,62532],[0,0,0,38,0,25,25,283,38,16,25,47,25,29,0,38,0,0,0,89,89,198,16,84,48,272,32,93,0,25,0,89,0,0,198,128,16,266,48,262,32,261,25,283,89,198,198,128,0,0,0,16,0,48,32,32,38,16,16,84,16,266,0,16,0,0,0,87,16,86,25,47,48,272,48,262,0,48,0,87,0,0,32,256,25,29,32,93,32,261,32,32,16,86,32,256,0,0])
def rec6_2 : List Sig × List Nat := ([15,240,3840,4369,8738,52428,61440],[0,0,0,38,0,25,25,284,38,16,25,32,0,29,0,38,0,0,0,89,89,274,16,84,32,273,0,93,0,25,0,89,0,0,205,128,16,267,32,264,0,263,25,284,89,274,205,128,0,0,0,16,0,32,137,192,38,16,16,84,16,267,0,16,0,0,0,86,16,257,25,32,32,273,32,264,0,32,0,86,0,0,32,256,0,29,0,93,0,263,137,192,16,257,32,256,0,0])
def rec6_3 : List Sig × List Nat := ([15,240,3840,4369,17476,34952,61986],[0,0,0,38,0,25,25,285,25,30,25,31,38,16,0,38,0,0,0,89,89,275,32,94,48,95,16,84,0,25,0,89,0,0,201,128,32,270,48,269,16,268,25,285,89,275,201,128,0,0,0,32,0,48,16,16,25,30,32,94,32,270,0,32,0,0,0,257,16,86,25,31,48,95,48,269,0,48,0,257,0,0,16,87,38,16,16,84,16,268,16,16,16,86,16,87,0,0])
def rec6_4 : List Sig × List Nat := ([15,240,4369,8738,17476,34952,65280],[0,0,0,38,25,286,38,16,25,32,25,48,0,25,0,38,0,0,89,280,16,84,32,277,48,276,0,89,25,286,89,280,0,0,0,16,0,32,0,48,258,128,38,16,16,84,0,16,0,0,0,86,0,87,16,268,25,32,32,277,0,32,0,86,0,0,0,263,32,261,25,48,48,276,0,48,0,87,0,263,0,0,48,259,0,25,0,89,258,128,16,268,32,261,48,259,0,0])
def rec6_5 : List Sig × List Nat := ([15,240,4369,8738,17476,36744,61440],[0,0,0,38,25,287,38,16,25,32,25,25,0,29,0,38,0,0,89,135,16,84,32,278,48,89,0,93,25,287,89,135,0,0,0,16,0,32,48,48,135,143,38,16,16,84,0,16,0,0,0,86,16,87,16,269,25,32,32,278,0,32,0,86,0,0,32,264,32,262,25,25,48,89,48,48,16,87,32,264,0,0,48,259,0,29,0,93,135,143,16,269,32,262,48,259,0,0])
def rec6_6 : List Sig × List Nat := ([15,240,4369,8738,20292,34952,61440],[0,0,0,38,25,288,38,16,25,25,25,43,0,29,0,38,0,0,89,134,16,84,32,89,48,279,0,93,25,288,89,134,0,0,0,16,32,32,0,48,134,142,38,16,16,84,0,16,0,0,16,86,0,87,16,270,25,25,32,89,32,32,16,86,0,0,32,264,32,261,25,43,48,279,0,48,0,87,32,264,0,0,48,260,0,29,0,93,134,142,16,270,32,261,48,260,0,0])
def rec6_7 : List Sig × List Nat := ([15,240,4369,12066,17476,34952,61440],[0,0,0,38,25,289,38,16,25,26,25,27,0,29,0,38,0,0,89,281,16,84,32,90,48,91,0,93,25,289,89,281,0,0,16,16,0,32,0,48,137,141,38,16,16,84,16,16,0,0,16,86,16,87,16,268,25,26,32,90,0,32,16,86,0,0,0,267,32,266,25,27,48,91,0,48,16,87,0,267,0,0,48,265,0,29,0,93,137,141,16,268,32,266,48,265,0,0])
def rec6_8 : List Sig × List Nat := ([15,3840,4369,8738,17476,35064,61440],[0,0,0,25,25,52,38,16,25,32,25,38,0,29,0,25,0,0,205,128,16,91,32,279,48,89,0,276,25,52,205,128,0,0,0,16,0,32,48,48,137,192,38,16,16,91,0,16,0,0,0,86,16,84,16,95,25,32,32,279,0,32,0,86,0,0,32,273,32,272,25,38,48,89,48,48,16,84,32,273,0,0,48,93,0,29,0,276,137,192,16,95,32,272,48,93,0,0])
def rec6_9 : List Sig × List Nat := ([15,3840,4369,8738,17652,34952,61440],[0,0,0,25,25,36,36,16,25,32,25,39,0,29,0,25,0,0,205,128,16,90,32,89,48,278,0,277,25,36,205,128,0,0,0,16,32,32,0,48,137,192,36,16,16,90,0,16,0,0,16,84,0,87,16,94,25,32,32,89,32,32,16,84,0,0,32,273,32,93,25,39,48,278,0,48,0,87,32,273,0,0,48,271,0,29,0,277,137,192,16,94,32,93,48,271,0,0])
def rec6_10 : List Sig × List Nat := ([15,3840,4593,8738,17476,34952,61440],[0,0,0,25,25,38,38,16,25,32,25,48,0,29,0,25,0,0,89,89,16,281,32,134,48,135,0,280,25,38,89,89,0,0,16,16,32,32,48,48,89,93,38,16,16,281,16,16,0,0,0,86,0,87,16,275,25,32,32,134,32,32,0,86,0,0,0,274,32,198,25,48,48,135,48,48,0,87,0,274,0,0,48,199,0,29,0,280,89,93,16,275,32,198,48,199,0,0])
def rec6_11 : List Sig × List Nat := ([240,3840,4383,8738,17476,34952,61440],[0,0,0,89,25,38,16,20,32,36,48,52,0,93,0,89,0,0,25,25,16,289,32,288,48,287,0,286,25,38,25,25,0,0,38,16,25,32,25,48,25,29,16,20,16,289,38,16,0,0,0,86,0,87,16,285,32,36,32,288,25,32,0,86,0,0,0,284,32,283,48,52,48,287,25,48,0,87,0,284,0,0,48,282,0,93,0,286,25,29,16,285,32,283,48,282,0,0])
def rec7_0 : List Sig × List Nat := ([15,240,3840,4369,8738,17476,34952,61440],[0,0,0,38,0,25,25,267,38,16,25,32,25,48,0,29,0,38,0,0,0,89,89,266,16,84,32,265,48,264,0,93,0,25,0,89,0,0,205,128,16,263,32,262,48,261,0,260,25,267,89,266,205,128,0,0,0,16,0,32,0,48,137,192,38,16,16,84,16,263,0,16,0,0,0,86,0,87,16,259,25,32,32,265,32,262,0,32,0,86,0,0,0,258,32,257,25,48,48,264,48,261,0,48,0,87,0,258,0,0,48,256,0,29,0,93,0,260,137,192,16,259,32,257,48,256,0,0])
def bank : Nat → List (List Sig × List Nat)
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => [rec3_0,rec3_1,rec3_2,rec3_3,rec3_4,rec3_5]
  | 4 => [rec4_0,rec4_1,rec4_2,rec4_3,rec4_4,rec4_5,rec4_6,rec4_7,rec4_8,rec4_9,rec4_10,rec4_11,rec4_12,rec4_13,rec4_14,rec4_15,rec4_16,rec4_17,rec4_18,rec4_19,rec4_20,rec4_21,rec4_22,rec4_23,rec4_24,rec4_25,rec4_26,rec4_27]
  | 5 => [rec5_0,rec5_1,rec5_2,rec5_3,rec5_4,rec5_5,rec5_6,rec5_7,rec5_8,rec5_9,rec5_10,rec5_11,rec5_12,rec5_13,rec5_14,rec5_15,rec5_16,rec5_17,rec5_18,rec5_19,rec5_20,rec5_21,rec5_22,rec5_23,rec5_24,rec5_25,rec5_26,rec5_27,rec5_28,rec5_29,rec5_30,rec5_31,rec5_32,rec5_33]
  | 6 => [rec6_0,rec6_1,rec6_2,rec6_3,rec6_4,rec6_5,rec6_6,rec6_7,rec6_8,rec6_9,rec6_10,rec6_11]
  | 7 => [rec7_0]
  | _ => []

def childList (ws : List Sig) (a b : Sig) (d : Bool) : List Sig :=
  bin d a b :: ws.filter fun c => c != a && c != b

def sameList (u v : List Sig) : Bool :=
  u.all (fun a => v.contains a) && v.all (fun a => u.contains a)

def failsAt (ws : List Sig) (r s : Fin 16) : Bool :=
  bit r target && !bit s target && ws.all (fun a => !bit r a || bit s a)

def checkMove (k : Nat) (ws : List Sig) (clues : List Nat) (a b : Sig) (d : Bool) : Bool :=
  let z := bin d a b
  if a == b || ws.contains z || z == zero || z == one then true else
  let c := clues.getD (2*(ws.length*ws.idxOf a+ws.idxOf b)+(if d then 1 else 0)) 0
  let ys := childList ws a b d
  if c < 256 then failsAt ys (Fin.ofNat 16 (c/16)) (Fin.ofNat 16 (c % 16)) else
    match (bank k)[c-256]? with
    | none => false
    | some next => sameList ys next.1

def checkRec (k : Nat) (rec : List Sig × List Nat) : Bool :=
  rec.1.all fun a => rec.1.all fun b => checkMove k rec.1 rec.2 a b false && checkMove k rec.1 rec.2 a b true

lemma no_fail {k : Nat} {ws : List Sig} (live : Live target k ws.toFinset) (r s) :
    failsAt ws r s ≠ true := by
  intro h
  have hh := Bool.and_eq_true_iff.mp h
  obtain ⟨yes,no'⟩ := Bool.and_eq_true_iff.mp hh.1
  have no : bit s target = false := by simpa using no'
  have bad := List.all_eq_true.mp hh.2
  obtain ⟨a,ha,ar,as'⟩ := separates live yes no
  simpa [ar,as'] using bad a (List.mem_toFinset.mp ha)

lemma sameList_eq {x y : List Sig} (h : sameList x y = true) : x.toFinset=y.toFinset := by
  simp only [sameList,Bool.and_eq_true,List.all_eq_true,List.contains_iff_mem] at h
  exact Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (h.1 a (List.mem_toFinset.mp ha)))
    (fun a ha => List.mem_toFinset.mpr (h.2 a (List.mem_toFinset.mp ha)))

lemma move_link {k : Nat} {ws : List Sig} {clues} {a b : Sig} {d : Bool}
    (h : checkMove k ws clues a b d = true) (ne : a≠b) (fresh : bin d a b ∉ ws)
    (safe : proper (bin d a b)) (live : Live target k (childList ws a b d).toFinset) :
    ∃ rec ∈ bank k, (childList ws a b d).toFinset = rec.1.toFinset := by
  obtain ⟨s0,s1⟩ := safe
  simp only [checkMove,Bool.or_eq_true,List.contains_iff_mem,beq_iff_eq] at h
  rw [if_neg (by tauto : ¬ (((a=b ∨ bin d a b ∈ ws) ∨ bin d a b=zero) ∨ bin d a b=one))] at h
  let c := clues.getD (2*(ws.length*ws.idxOf a+ws.idxOf b)+(if d then 1 else 0)) 0
  let ys := childList ws a b d
  change (if c < 256 then failsAt ys (Fin.ofNat 16 (c/16)) (Fin.ofNat 16 (c % 16)) else
      match (bank k)[c-256]? with
      | none => false
      | some rr => sameList ys rr.1) = true at h
  by_cases lt : c<256
  · rw [if_pos lt] at h
    exact False.elim (no_fail live _ _ h)
  · rw [if_neg lt] at h
    cases heq : (bank k)[c-256]? with
    | none => simp [heq] at h
    | some rr =>
      rw [heq] at h
      exact ⟨rr,List.mem_of_getElem? heq,sameList_eq h⟩

lemma child_eq (ws : List Sig) (a b : Sig) (d : Bool) :
    (childList ws a b d).toFinset = nextSet ws.toFinset a b d := by
  ext v
  simp [childList,nextSet]
  tauto

lemma ok3_0 : checkRec 2 rec3_0 = true := by decide +kernel
lemma ok3_1 : checkRec 2 rec3_1 = true := by decide +kernel
lemma ok3_2 : checkRec 2 rec3_2 = true := by decide +kernel
lemma ok3_3 : checkRec 2 rec3_3 = true := by decide +kernel
lemma ok3_4 : checkRec 2 rec3_4 = true := by decide +kernel
lemma ok3_5 : checkRec 2 rec3_5 = true := by decide +kernel
lemma ok4_0 : checkRec 3 rec4_0 = true := by decide +kernel
lemma ok4_1 : checkRec 3 rec4_1 = true := by decide +kernel
lemma ok4_2 : checkRec 3 rec4_2 = true := by decide +kernel
lemma ok4_3 : checkRec 3 rec4_3 = true := by decide +kernel
lemma ok4_4 : checkRec 3 rec4_4 = true := by decide +kernel
lemma ok4_5 : checkRec 3 rec4_5 = true := by decide +kernel
lemma ok4_6 : checkRec 3 rec4_6 = true := by decide +kernel
lemma ok4_7 : checkRec 3 rec4_7 = true := by decide +kernel
lemma ok4_8 : checkRec 3 rec4_8 = true := by decide +kernel
lemma ok4_9 : checkRec 3 rec4_9 = true := by decide +kernel
lemma ok4_10 : checkRec 3 rec4_10 = true := by decide +kernel
lemma ok4_11 : checkRec 3 rec4_11 = true := by decide +kernel
lemma ok4_12 : checkRec 3 rec4_12 = true := by decide +kernel
lemma ok4_13 : checkRec 3 rec4_13 = true := by decide +kernel
lemma ok4_14 : checkRec 3 rec4_14 = true := by decide +kernel
lemma ok4_15 : checkRec 3 rec4_15 = true := by decide +kernel
lemma ok4_16 : checkRec 3 rec4_16 = true := by decide +kernel
lemma ok4_17 : checkRec 3 rec4_17 = true := by decide +kernel
lemma ok4_18 : checkRec 3 rec4_18 = true := by decide +kernel
lemma ok4_19 : checkRec 3 rec4_19 = true := by decide +kernel
lemma ok4_20 : checkRec 3 rec4_20 = true := by decide +kernel
lemma ok4_21 : checkRec 3 rec4_21 = true := by decide +kernel
lemma ok4_22 : checkRec 3 rec4_22 = true := by decide +kernel
lemma ok4_23 : checkRec 3 rec4_23 = true := by decide +kernel
lemma ok4_24 : checkRec 3 rec4_24 = true := by decide +kernel
lemma ok4_25 : checkRec 3 rec4_25 = true := by decide +kernel
lemma ok4_26 : checkRec 3 rec4_26 = true := by decide +kernel
lemma ok4_27 : checkRec 3 rec4_27 = true := by decide +kernel
lemma ok5_0 : checkRec 4 rec5_0 = true := by decide +kernel
lemma ok5_1 : checkRec 4 rec5_1 = true := by decide +kernel
lemma ok5_2 : checkRec 4 rec5_2 = true := by decide +kernel
lemma ok5_3 : checkRec 4 rec5_3 = true := by decide +kernel
lemma ok5_4 : checkRec 4 rec5_4 = true := by decide +kernel
lemma ok5_5 : checkRec 4 rec5_5 = true := by decide +kernel
lemma ok5_6 : checkRec 4 rec5_6 = true := by decide +kernel
lemma ok5_7 : checkRec 4 rec5_7 = true := by decide +kernel
lemma ok5_8 : checkRec 4 rec5_8 = true := by decide +kernel
lemma ok5_9 : checkRec 4 rec5_9 = true := by decide +kernel
lemma ok5_10 : checkRec 4 rec5_10 = true := by decide +kernel
lemma ok5_11 : checkRec 4 rec5_11 = true := by decide +kernel
lemma ok5_12 : checkRec 4 rec5_12 = true := by decide +kernel
lemma ok5_13 : checkRec 4 rec5_13 = true := by decide +kernel
lemma ok5_14 : checkRec 4 rec5_14 = true := by decide +kernel
lemma ok5_15 : checkRec 4 rec5_15 = true := by decide +kernel
lemma ok5_16 : checkRec 4 rec5_16 = true := by decide +kernel
lemma ok5_17 : checkRec 4 rec5_17 = true := by decide +kernel
lemma ok5_18 : checkRec 4 rec5_18 = true := by decide +kernel
lemma ok5_19 : checkRec 4 rec5_19 = true := by decide +kernel
lemma ok5_20 : checkRec 4 rec5_20 = true := by decide +kernel
lemma ok5_21 : checkRec 4 rec5_21 = true := by decide +kernel
lemma ok5_22 : checkRec 4 rec5_22 = true := by decide +kernel
lemma ok5_23 : checkRec 4 rec5_23 = true := by decide +kernel
lemma ok5_24 : checkRec 4 rec5_24 = true := by decide +kernel
lemma ok5_25 : checkRec 4 rec5_25 = true := by decide +kernel
lemma ok5_26 : checkRec 4 rec5_26 = true := by decide +kernel
lemma ok5_27 : checkRec 4 rec5_27 = true := by decide +kernel
lemma ok5_28 : checkRec 4 rec5_28 = true := by decide +kernel
lemma ok5_29 : checkRec 4 rec5_29 = true := by decide +kernel
lemma ok5_30 : checkRec 4 rec5_30 = true := by decide +kernel
lemma ok5_31 : checkRec 4 rec5_31 = true := by decide +kernel
lemma ok5_32 : checkRec 4 rec5_32 = true := by decide +kernel
lemma ok5_33 : checkRec 4 rec5_33 = true := by decide +kernel
lemma ok6_0 : checkRec 5 rec6_0 = true := by decide +kernel
lemma ok6_1 : checkRec 5 rec6_1 = true := by decide +kernel
lemma ok6_2 : checkRec 5 rec6_2 = true := by decide +kernel
lemma ok6_3 : checkRec 5 rec6_3 = true := by decide +kernel
lemma ok6_4 : checkRec 5 rec6_4 = true := by decide +kernel
lemma ok6_5 : checkRec 5 rec6_5 = true := by decide +kernel
lemma ok6_6 : checkRec 5 rec6_6 = true := by decide +kernel
lemma ok6_7 : checkRec 5 rec6_7 = true := by decide +kernel
lemma ok6_8 : checkRec 5 rec6_8 = true := by decide +kernel
lemma ok6_9 : checkRec 5 rec6_9 = true := by decide +kernel
lemma ok6_10 : checkRec 5 rec6_10 = true := by decide +kernel
lemma ok6_11 : checkRec 5 rec6_11 = true := by decide +kernel
lemma ok7_0 : checkRec 6 rec7_0 = true := by decide +kernel
lemma checked {k : Nat} (hk : k < 7) : ∀ rec ∈ bank (k+1), checkRec k rec = true := by
  interval_cases k <;> simp only [bank,List.mem_cons,List.mem_nil_iff,or_false] <;> intro rec h
  · cases h
  · cases h
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok3_0
    · exact ok3_1
    · exact ok3_2
    · exact ok3_3
    · exact ok3_4
    · exact ok3_5
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok4_0
    · exact ok4_1
    · exact ok4_2
    · exact ok4_3
    · exact ok4_4
    · exact ok4_5
    · exact ok4_6
    · exact ok4_7
    · exact ok4_8
    · exact ok4_9
    · exact ok4_10
    · exact ok4_11
    · exact ok4_12
    · exact ok4_13
    · exact ok4_14
    · exact ok4_15
    · exact ok4_16
    · exact ok4_17
    · exact ok4_18
    · exact ok4_19
    · exact ok4_20
    · exact ok4_21
    · exact ok4_22
    · exact ok4_23
    · exact ok4_24
    · exact ok4_25
    · exact ok4_26
    · exact ok4_27
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok5_0
    · exact ok5_1
    · exact ok5_2
    · exact ok5_3
    · exact ok5_4
    · exact ok5_5
    · exact ok5_6
    · exact ok5_7
    · exact ok5_8
    · exact ok5_9
    · exact ok5_10
    · exact ok5_11
    · exact ok5_12
    · exact ok5_13
    · exact ok5_14
    · exact ok5_15
    · exact ok5_16
    · exact ok5_17
    · exact ok5_18
    · exact ok5_19
    · exact ok5_20
    · exact ok5_21
    · exact ok5_22
    · exact ok5_23
    · exact ok5_24
    · exact ok5_25
    · exact ok5_26
    · exact ok5_27
    · exact ok5_28
    · exact ok5_29
    · exact ok5_30
    · exact ok5_31
    · exact ok5_32
    · exact ok5_33
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok6_0
    · exact ok6_1
    · exact ok6_2
    · exact ok6_3
    · exact ok6_4
    · exact ok6_5
    · exact ok6_6
    · exact ok6_7
    · exact ok6_8
    · exact ok6_9
    · exact ok6_10
    · exact ok6_11
  · rcases h with rfl
    · exact ok7_0

lemma impossible {k : Nat} {ws : List Sig} {clues : List Nat} (bound : k≤7)
    (full : ws.toFinset.card=k+1) (init : (ws,clues) ∈ bank k) :
    ¬ Live target k ws.toFinset := by
  intro run
  induction k generalizing ws clues with
  | zero => simp [bank] at init
  | succ k ih =>
    obtain ⟨U,a,b,d,eq,ha,hb,hab,hf,tail⟩ := run
    have fresh : bin d a b ∉ U := fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have lim := live_size tail
    rw [Finset.card_insert_of_notMem fresh] at lim
    rw [eq] at full
    have na : a ∉ U := by
      intro aa
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem aa : a ∈ insert b U)] at full
      have := Finset.card_insert_le b U
      omega
    have nb : b ∉ U := by
      intro bb
      rw [Finset.insert_eq_of_mem bb] at full
      have := Finset.card_insert_le a U
      omega
    have na' : a ∉ insert b U := by simp [hab,na]
    have er : (childList ws a b d).toFinset = insert (bin d a b) U := by
      rw [child_eq,eq]
      simp [nextSet,na',nb]
    have ch := checked (by omega : k<7) (ws,clues) init
    simp only [checkRec,List.all_eq_true,Bool.and_eq_true] at ch
    have aw : a ∈ ws := List.mem_toFinset.mp (eq ▸ Finset.mem_insert_self _ _)
    have bw : b ∈ ws := List.mem_toFinset.mp (eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have ch' : checkMove k ws clues a b d = true := by cases d <;> simp_all
    have absent : bin d a b ∉ ws := fun m => hf (eq ▸ List.mem_toFinset.mpr m)
    obtain ⟨⟨nw,nc⟩,member,newEq⟩ := move_link ch' hab absent (live_proper tail _ (Finset.mem_insert_self _ _)) (er ▸ tail)
    have exactEq : nw.toFinset = insert (bin d a b) U := newEq.symm.trans er
    apply ih (by omega) _ member (exactEq ▸ tail)
    rw [exactEq,Finset.card_insert_of_notMem fresh]
    rw [Finset.card_insert_of_notMem na',Finset.card_insert_of_notMem nb] at full
    omega


lemma needs : ∀ a ∈ raw, ∃ r s : Fin 16, bit r target=true ∧ bit s target=false ∧
    ∀ x ∈ raw, bit r x=true → bit s x=false → x=a := by
  intro a hm
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨1,9,by decide,by decide,?_⟩
    intro x hx
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · refine ⟨5,9,by decide,by decide,?_⟩
    intro x hx
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · refine ⟨8,0,by decide,by decide,?_⟩
    intro x hx
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · refine ⟨12,0,by decide,by decide,?_⟩
    intro x hx
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · refine ⟨8,9,by decide,by decide,?_⟩
    intro x hx
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · refine ⟨1,0,by decide,by decide,?_⟩
    intro x hx
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · refine ⟨2,0,by decide,by decide,?_⟩
    intro x hx
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · refine ⟨3,0,by decide,by decide,?_⟩
    intro x hx
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

lemma all_inputs {k S} (live : Live target k S) (sub : S ⊆ raw.toFinset) : S=raw.toFinset := by
  apply Finset.Subset.antisymm sub
  intro a ha
  obtain ⟨r,s,yes,no,only⟩ := needs a (List.mem_toFinset.mp ha)
  obtain ⟨q,hq,qr,qs⟩ := separates live yes no
  exact only q (List.mem_toFinset.mp (sub hq)) qr qs ▸ hq
lemma lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (4398 : ℕ).testBit (4*u.val+v.val)) 7 := by
  rintro ⟨C,hm,hsize,he⟩
  have legal : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) := by
    intro g hg
    have op : g.op = .and ∨ g.op = .or := (hm _ hg).1
    rcases op with h|h <;> simp [h]
  have images : ∀ i : Fin 16, raw.map (bit i) = oneEach (Fin.ofNat 4 (i.val/4)) (Fin.ofNat 4 (i.val % 4)) := by decide
  have truths : ∀ i : Fin 16, bit i target = (4398:ℕ).testBit (4*(Fin.ofNat 4 (i.val/4)).val+(Fin.ofNat 4 (i.val % 4)).val) := by decide
  have out : (execute C.gates raw).getD C.output zero = target := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let i : Fin 16 := ⟨j,hj⟩
    change bit i ((execute C.gates raw).getD C.output zero) = bit i target
    rw [← b_read,execute_bits _ _ _ legal,images,truths]
    exact he _ _
  have properT : proper target := by unfold proper; decide
  have mem : target ∈ execute C.gates raw := (out ▸ get_rep (execute C.gates raw) C.output).resolve_right (fun h => h properT)
  obtain ⟨k,S,hk,live,ss⟩ := extract C.gates raw hm properT mem
  have eq := all_inputs live (fun _ h => List.mem_toFinset.mpr (ss _ h))
  subst S
  have nn : raw.toFinset.card = 8 := by decide
  have bound := live_size live
  change C.gates.length ≤7 at hsize
  have len : k=7 := by omega
  subst k
  have start : raw.toFinset = rec7_0.1.toFinset := by decide
  exact impossible (k:=7) (ws:=rec7_0.1) (clues:=rec7_0.2) (by decide) (by decide)
      (by decide) (start ▸ live)

def eight : Circuit :=
  ⟨[⟨.or,[6,7]⟩,⟨.or,[5,8]⟩,⟨.and,[0,9]⟩,⟨.and,[1,5]⟩,
    ⟨.or,[2,3]⟩,⟨.and,[4,12]⟩,⟨.or,[10,11]⟩,⟨.or,[13,14]⟩],15⟩

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (4398 : ℕ).testBit (4*u.val+v.val)) 8 := by
  refine ⟨eight,?_,by decide,by decide⟩
  intro g hg
  simp only [eight,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp


end PEqualNP.Outside.L_meta_5552_aux

theorem PEqualNP.Outside.L_meta_5552 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4398 : ℕ).testBit (4 * u.val + v.val)) 8 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4398 : ℕ).testBit (4 * u.val + v.val)) 7 :=
  ⟨L_meta_5552_aux.upper,L_meta_5552_aux.lower⟩
