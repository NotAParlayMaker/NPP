import PEqualNP.Defs
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto

-- The signed circuit search follows L_meta_10856 and L_meta_8453 (Apache-2.0).
-- Each search leaf either fails a separation test or restricts to a certified smaller graph.

namespace PEqualNP.Outside.L_meta_14286.Model
open PEqualNP.CircuitLowerBounds

def certificateWord (words : List Nat) : Nat :=
  words.foldl (fun value word => (value <<< 64) ||| word) 0

abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
theorem getRep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (getRep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (getRep w i) (getRep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (getRep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

theorem extractPlan {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

theorem bRead (i) (w : List Sig) (j : Nat) :
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
  simp only [bRead]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

theorem exeBits (gs : List Gate) (i) (w : List Sig)
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
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
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
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
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

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
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

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
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
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [(OfNat.ofNat (certificateWord [0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa])),(OfNat.ofNat (certificateWord [0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc])),(OfNat.ofNat (certificateWord [0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0])),(OfNat.ofNat (certificateWord [0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00])),(OfNat.ofNat (certificateWord [0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000])),(OfNat.ofNat (certificateWord [0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000])),(OfNat.ofNat (certificateWord [0xffffffffffffffff,0x0000000000000000,0xffffffffffffffff,0x0000000000000000,0xffffffffffffffff,0x0000000000000000,0xffffffffffffffff,0x0000000000000000])),(OfNat.ofNat (certificateWord [0xffffffffffffffff,0xffffffffffffffff,0x0000000000000000,0x0000000000000000,0xffffffffffffffff,0xffffffffffffffff,0x0000000000000000,0x0000000000000000])),(OfNat.ofNat (certificateWord [0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0x0000000000000000,0x0000000000000000,0x0000000000000000,0x0000000000000000]))]
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

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
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

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

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
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
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
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



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
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
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

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

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
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

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

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

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
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

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
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
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
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
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
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

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
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
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 256
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 256 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 256 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 256 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 256 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

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
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
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
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 256) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 256) (j : Fin 9) :
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
  let n := v.toNat % 2305843009149157119
  (n*(n+971)) % 2305843009149157119
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 256 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 256) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 256 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
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
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)


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
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
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
  exact hi k hk run

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


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


end PEqualNP.Outside.L_meta_14286.Model

namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
open PEqualNP.CircuitLowerBounds

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat)

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def count (g : Atlas) := g.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.1
def tip (g : Atlas) := g.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2
def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g-k
  let v := record g k i
  selectLive (v >>> (10*d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/64,raw.getD (b/8 % 8) zero,raw.getD (b % 8) zero)::tips raw (v >>> 8) n

def cutIndex (h : Nat) : Fin 45 := ⟨min ((h % 256)-1) 44,by omega⟩
def cutPair (j : Fin 45) : Sig × Nat :=
  match j.val with
  | 0 => ((OfNat.ofNat (certificateWord [0x5555555555555555,0x5555555555555555,0x5555555555555555,0x5555555555555555,0x5555555555555555,0x5555555555555555,0x5555555555555555,0x5555555555555555])),10)
  | 1 => ((OfNat.ofNat (certificateWord [0x3333333333333333,0x3333333333333333,0x3333333333333333,0x3333333333333333,0x3333333333333333,0x3333333333333333,0x3333333333333333,0x3333333333333333])),10)
  | 2 => ((OfNat.ofNat (certificateWord [0xf0f0f0f0f0f0f0f,0x0f0f0f0f0f0f0f0f,0x0f0f0f0f0f0f0f0f,0x0f0f0f0f0f0f0f0f,0x0f0f0f0f0f0f0f0f,0x0f0f0f0f0f0f0f0f,0x0f0f0f0f0f0f0f0f,0x0f0f0f0f0f0f0f0f])),9)
  | 3 => ((OfNat.ofNat (certificateWord [0xff00ff00ff00ff,0x00ff00ff00ff00ff,0x00ff00ff00ff00ff,0x00ff00ff00ff00ff,0x00ff00ff00ff00ff,0x00ff00ff00ff00ff,0x00ff00ff00ff00ff,0x00ff00ff00ff00ff])),9)
  | 4 => ((OfNat.ofNat (certificateWord [0xffff0000ffff,0x0000ffff0000ffff,0x0000ffff0000ffff,0x0000ffff0000ffff,0x0000ffff0000ffff,0x0000ffff0000ffff,0x0000ffff0000ffff,0x0000ffff0000ffff])),10)
  | 5 => ((OfNat.ofNat (certificateWord [0xffffffff,0x00000000ffffffff,0x00000000ffffffff,0x00000000ffffffff,0x00000000ffffffff,0x00000000ffffffff,0x00000000ffffffff,0x00000000ffffffff])),9)
  | 6 => ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0x0000000000000000,0xffffffffffffffff,0x0000000000000000,0xffffffffffffffff,0x0000000000000000,0xffffffffffffffff])),9)
  | 7 => ((OfNat.ofNat (certificateWord [0xf0f0f0f,0x000000000f0f0f0f,0x000000000f0f0f0f,0x000000000f0f0f0f,0x000000000f0f0f0f,0x000000000f0f0f0f,0x000000000f0f0f0f,0x000000000f0f0f0f])),8)
  | 8 => ((OfNat.ofNat (certificateWord [0xff00ff00ff00ff,0x0000000000000000,0x00ff00ff00ff00ff,0x0000000000000000,0x00ff00ff00ff00ff,0x0000000000000000,0x00ff00ff00ff00ff])),8)
  | 9 => ((OfNat.ofNat (certificateWord [0xf000f000f000f,0x000f000f000f000f,0x000f000f000f000f,0x000f000f000f000f,0x000f000f000f000f,0x000f000f000f000f,0x000f000f000f000f,0x000f000f000f000f])),7)
  | 10 => ((OfNat.ofNat (certificateWord [0xff00ff,0x0000000000ff00ff,0x0000000000ff00ff,0x0000000000ff00ff,0x0000000000ff00ff,0x0000000000ff00ff,0x0000000000ff00ff,0x0000000000ff00ff])),6)
  | 11 => ((OfNat.ofNat (certificateWord [0xf0f0f0f0f0f0f0f,0x0000000000000000,0x0f0f0f0f0f0f0f0f,0x0000000000000000,0x0f0f0f0f0f0f0f0f,0x0000000000000000,0x0f0f0f0f0f0f0f0f])),7)
  | 12 => ((OfNat.ofNat (certificateWord [0x333300003333,0x0000000000000000,0x0000333300003333,0x0000000000000000,0x0000333300003333,0x0000000000000000,0x0000333300003333])),6)
  | 13 => ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xffffffffffffffff,0x0000000000000000,0x0000000000000000,0xffffffffffffffff,0xffffffffffffffff])),8)
  | 14 => ((OfNat.ofNat (certificateWord [0xf0f0f0f0f0f0f0f,0x0f0f0f0f0f0f0f0f,0x0000000000000000,0x0000000000000000,0x0f0f0f0f0f0f0f0f,0x0f0f0f0f0f0f0f0f])),7)
  | 15 => ((OfNat.ofNat (certificateWord [0xf0f0f0f,0x000000000f0f0f0f,0x0000000000000000,0x0000000000000000,0x000000000f0f0f0f,0x000000000f0f0f0f])),5)
  | 16 => ((OfNat.ofNat (certificateWord [0xff00ff00ff00ff,0x00ff00ff00ff00ff,0x0000000000000000,0x0000000000000000,0x00ff00ff00ff00ff,0x00ff00ff00ff00ff])),6)
  | 17 => ((OfNat.ofNat (certificateWord [0xff00ff00ff00ff,0x0000000000000000,0x0000000000000000,0x0000000000000000,0x00ff00ff00ff00ff])),5)
  | 18 => ((OfNat.ofNat (certificateWord [0xf000f000f000f,0x000f000f000f000f,0x0000000000000000,0x0000000000000000,0x000f000f000f000f,0x000f000f000f000f])),5)
  | 19 => ((OfNat.ofNat (certificateWord [0x55005500550055,0x0055005500550055,0x0055005500550055,0x0055005500550055,0x0055005500550055,0x0055005500550055,0x0055005500550055,0x0055005500550055])),8)
  | 20 => ((OfNat.ofNat (certificateWord [0x33003300330033,0x0033003300330033,0x0033003300330033,0x0033003300330033,0x0033003300330033,0x0033003300330033,0x0033003300330033,0x0033003300330033])),8)
  | 21 => ((OfNat.ofNat (certificateWord [0xff000000ff,0x000000ff000000ff,0x000000ff000000ff,0x000000ff000000ff,0x000000ff000000ff,0x000000ff000000ff,0x000000ff000000ff,0x000000ff000000ff])),8)
  | 22 => ((OfNat.ofNat (certificateWord [0x505050505050505,0x0505050505050505,0x0505050505050505,0x0505050505050505,0x0505050505050505,0x0505050505050505,0x0505050505050505,0x0505050505050505])),8)
  | 23 => ((OfNat.ofNat (certificateWord [0x303030303030303,0x0303030303030303,0x0303030303030303,0x0303030303030303,0x0303030303030303,0x0303030303030303,0x0303030303030303,0x0303030303030303])),8)
  | 24 => ((OfNat.ofNat (certificateWord [0xf0f00000f0f,0x00000f0f00000f0f,0x00000f0f00000f0f,0x00000f0f00000f0f,0x00000f0f00000f0f,0x00000f0f00000f0f,0x00000f0f00000f0f,0x00000f0f00000f0f])),8)
  | 25 => ((OfNat.ofNat (certificateWord [0xffff0000ffff,0x0000000000000000,0x0000ffff0000ffff,0x0000000000000000,0x0000ffff0000ffff,0x0000000000000000,0x0000ffff0000ffff])),6)
  | 26 => ((OfNat.ofNat (certificateWord [0x33333333,0x0000000033333333,0x0000000033333333,0x0000000033333333,0x0000000033333333,0x0000000033333333,0x0000000033333333,0x0000000033333333])),8)
  | 27 => ((OfNat.ofNat (certificateWord [0x55555555,0x0000000055555555,0x0000000055555555,0x0000000055555555,0x0000000055555555,0x0000000055555555,0x0000000055555555,0x0000000055555555])),8)
  | 28 => ((OfNat.ofNat (certificateWord [0x555500005555,0x0000555500005555,0x0000555500005555,0x0000555500005555,0x0000555500005555,0x0000555500005555,0x0000555500005555,0x0000555500005555])),9)
  | 29 => ((OfNat.ofNat (certificateWord [0x333300003333,0x0000333300003333,0x0000333300003333,0x0000333300003333,0x0000333300003333,0x0000333300003333,0x0000333300003333,0x0000333300003333])),9)
  | 30 => ((OfNat.ofNat (certificateWord [0xffffffff,0x00000000ffffffff,0x0000000000000000,0x0000000000000000,0x00000000ffffffff,0x00000000ffffffff])),5)
  | 31 => ((OfNat.ofNat (certificateWord [0xffff,0x000000000000ffff,0x000000000000ffff,0x000000000000ffff,0x000000000000ffff,0x000000000000ffff,0x000000000000ffff,0x000000000000ffff])),7)
  | 32 => ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0x0000000000000000,0x0000000000000000,0x0000000000000000,0xffffffffffffffff])),5)
  | 33 => ((OfNat.ofNat (certificateWord [0x3333333333333333,0x0000000000000000,0x3333333333333333,0x0000000000000000,0x3333333333333333,0x0000000000000000,0x3333333333333333])),8)
  | 34 => ((OfNat.ofNat (certificateWord [0xf0f0f0f0f0f0f0f,0x0000000000000000,0x0000000000000000,0x0000000000000000,0x0f0f0f0f0f0f0f0f])),4)
  | 35 => ((OfNat.ofNat (certificateWord [0x5500000055,0x0000005500000055,0x0000005500000055,0x0000005500000055,0x0000005500000055,0x0000005500000055,0x0000005500000055,0x0000005500000055])),7)
  | 36 => ((OfNat.ofNat (certificateWord [0x3030303,0x0000000003030303,0x0000000003030303,0x0000000003030303,0x0000000003030303,0x0000000003030303,0x0000000003030303,0x0000000003030303])),7)
  | 37 => ((OfNat.ofNat (certificateWord [0xf0f00000f0f,0x0000000000000000,0x00000f0f00000f0f,0x0000000000000000,0x00000f0f00000f0f,0x0000000000000000,0x00000f0f00000f0f])),4)
  | 38 => ((OfNat.ofNat (certificateWord [0xffff0000ffff,0x0000ffff0000ffff,0x0000000000000000,0x0000000000000000,0x0000ffff0000ffff,0x0000ffff0000ffff])),6)
  | 39 => ((OfNat.ofNat (certificateWord [0x1111111111111111,0x0000000000000000,0x1111111111111111,0x0000000000000000,0x1111111111111111,0x0000000000000000,0x1111111111111111])),5)
  | 40 => ((OfNat.ofNat (certificateWord [0x3333333333333333,0x3333333333333333,0x0000000000000000,0x0000000000000000,0x3333333333333333,0x3333333333333333])),7)
  | 41 => ((OfNat.ofNat (certificateWord [0x33003300330033,0x0000000000000000,0x0033003300330033,0x0000000000000000,0x0033003300330033,0x0000000000000000,0x0033003300330033])),7)
  | 42 => ((OfNat.ofNat (certificateWord [0x5050505,0x0000000005050505,0x0000000005050505,0x0000000005050505,0x0000000005050505,0x0000000005050505,0x0000000005050505,0x0000000005050505])),7)
  | 43 => ((OfNat.ofNat (certificateWord [0x111100001111,0x0000111100001111,0x0000111100001111,0x0000111100001111,0x0000111100001111,0x0000111100001111,0x0000111100001111,0x0000111100001111])),8)
  | 44 => ((OfNat.ofNat (certificateWord [0x5555,0x0000000000005555,0x0000000000005555,0x0000000000005555,0x0000000000005555,0x0000000000005555,0x0000000000005555,0x0000000000005555])),6)
  | _ => (zero,0)
def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let cut := cutPair (cutIndex hint)
  let cs := tips raw (hint >>> 12) (hint/256 % 16)
  (makePool true cut.1 raw cs).any (fun pool => poolCut true cut.1 cut.2 k cs.length pool ws)

def mirrorSteps : List Move := []

def variant (g : Atlas) (code : Nat) (ws : List Sig) : List Sig :=
  if code % 2 == 1 && autoOK (target g) mirrorSteps then ws.map (movedWord mirrorSteps.reverse) else ws

theorem variant_ok {g k ws} (h : Impossible true (target g) k (List.toFinset ws)) (code : Nat) :
    Impossible true (target g) k (variant g code ws).toFinset := by
  unfold variant
  split
  next e =>
    simp only [Bool.and_eq_true] at e
    exact rotate_excluded h _ e.2
  next => exact h

def links (g : Atlas) (k tag : Nat) : List (List Sig) :=
  let code := locate g k tag
  let row := code / 2
  if row < count g k then [variant g code (vals g k row)] else []

def checkRow (g : Atlas) (k i : Nat) : Bool :=
  let ws := items g k i
  let vs := ws.map Prod.fst
  let h := tip g k i
  decide vs.Nodup && !vs.contains (target g) &&
    (if h != 0 then deadTest (roots g) vs k h else
      testAll (k,ws.length,ws,preCov true ws,[],links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 256 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
    ∀ k i, i < count g k → tip g k i ≠ 0 →
      Slice true (roots g) (target g) (cutPair (cutIndex (tip g k i))).1 (cutPair (cutIndex (tip g k i))).2

theorem checked {g : Atlas} {r s} (ready : Ready g r s) (k : Nat)
    (good : ∀ l ≤ k, ∀ i < count g l, checkRow g l i = true) :
    ∀ i < count g k, Impossible true (target g) k (vals g k i).toFinset := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi
    have h := good k (by omega) i hi
    simp only [checkRow,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at h
    by_cases hn : tip g k i = 0
    · simp only [hn,bne_self_eq_false, Bool.false_eq_true,ite_false] at h
      by_cases hk : k=0
      · subst k
        intro n cap run
        have : n=0 := by omega
        subst n
        have hm : target g ∈ (vals g 0 i).toFinset := run.1 ▸ Finset.mem_singleton_self _
        exact h.1.2 (List.mem_toFinset.mp hm)
      apply node_sound (raw:=roots g) ready.1 _ h.1.1 h.1.2 _ _ h.2
      · intro a ha
        exact decode_faithful _ _ _ _ _ ready.2.1 _ ((selectLive_sub _ _).subset ha)
      · simp
      · intro tag xs hx
        simp only [links] at hx
        split at hx
        next le =>
          obtain rfl := List.mem_singleton.mp hx
          exact variant_ok (ih (k-1) (by omega) (fun l hl => good l (by omega)) _ le) _
        next => simp at hx
    · simp only [bne_iff_ne.mpr hn, ite_true] at h
      have test := h.2
      simp only [deadTest,Option.any_eq_true] at test
      obtain ⟨bank,he,hc⟩ := test
      exact poolCut_sound (ready.2.2 k i hi hn) _ he h.1.1 hc

def segment (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && segment test start n

theorem segmentRange {test start n} (h : segment test start n=true) (i : Nat)
    (lo : start ≤ i) (hi : i<start+n) : test i=true := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_of_ge lo hi)
  | succ n ih =>
    simp only [segment,Bool.and_eq_true] at h
    by_cases eq : i=start+n
    · exact eq.symm ▸ h.1
    · exact ih h.2 (lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq)

def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def g0K6 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x3684,0x48e0410f224e98e0,0x10031025103c6a30,0x000b03004c50b006,0x80112874c954800f,0x862440b8700602aa,0x3a80257010050401,0xfd43fd42fd41fd40,0xfd32fd31fd30fc43,0xfd21fd20fc42fc32,0xfd10fc41fc31fc21,0xfc40fc30fc20fc10,0xff40ff30ff20ff10,0xff41ff31ff21fe10,0xff42ff32fe21fe20,0xff43fe32fe31fe30,0xfe43fe42fe41fe40]))
  | _ => 0
def g0K5 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x6417c45c82f86b90,0x5dc5420bf8a841f7,0x15082fe2a185dc54,0x40bf8a881f715103,0xf20b887d50710fa9,0x0e21ed25c42fe2a0,0x87d0c710f792e21f,0x715c42f88b885f0d,0x710be12e217f4508,0x6fe6a10dfd14319f,0xa2863bf450c7eea2,0xa1ddd4543bfa8a87,0x7f5150afea2a07d4,0x5741dea1e837f451,0x077e8ba0fd0c741b,0xfa8a657f514c2be6,0xa20dfcd441ef9a88,0x3f515cc7ea4398fd,0x44331eea1e637f35,0x0c7e88398f7cd731,0xfb88663f741cc6f8,0x8b98dfd4520b7928,0x637f250c7de4a18d,0xbc9441bf92883ef2,0x5107ea2b90fb50b2,0x1f699643dd35c86f,0xe4a10f7cd721f792,0xe43ec20c86f88b90,0xdf0d721bf280437a,0x500c7f4a018df940,0x31bd28083fa50106,0xfca020fe50210fc9,0x8421f515843ba6b0,0x85fc1410ef9ac21f,0x820843f60b087ec8,0x210fd88421f71084,0x2f88b085f0d610be,0x12c217e05d06fc0b,0x98df81721bfa2865,0x7f5250efea4a0fbd,0x4940b7a92817f525,0x03da4ba16f50342b,0xfa2885bf45d0bd84,0x1a16fd0342bfa926,0x37f524c2be6a215f,0xcd442ef9a885f905,0xccbda4b997750f32,0xee986657f350cbbe,0x6b99770c732fd82e,0x65df30ccaf88b995,0xf89510bf28865765,0x110beca2215f9444,0x2fc82c43f541887e,0xa2110fb49621bf8a,0x843f431887ee2b10,0xfec1621fb88443f7,0x31887ee4310fbc86,0x21be22c437c35886,0xfca0195e94042fd2,0x80857e5010bf2811,0x07b4ca20f690c41e,0xd25882fe0a107b10,0xa20fd82c41fb2088,0x3de41107bc8620f7,0xa14417c45882f86b,0x105f05620bf02e85,0x7e05ccafc0b10df8,0x5742bf0ae657e158,0x82fea6a177d4d41a,0xfa9a837f53506fea,0x6a0774d743dea0e8,0x77f4510f7e8ba1f7,0x0c743dfa0e877e35,0x486fc6a905b94843,0xf7290877e5210fea,0x2b197b50a32f690c,0x65dd358cafe4a197,0xbc9632fb8ac65ec2,0x08cbde43197bcca3,0x2ef99465ee208caf,0x88b195f8d510bb28,0x887f65110efca221,0xfd50631ee99463dd,0x358c7ba6118dfc54,0x31ee21c63f7158c7,0xbe6118fdcc631ef9,0x8c63df328c7be871,0x8df11631be12c637,0xa5010ff4a021df94,0x043fca0461f9108c,0x3ea2b18774d630bf,0x82861f7158c3f60b,0x187e08230fd98461,0xdf308c3f641187e8,0x4230be22c617c258,0xc2f82b185f81743b,0xf02c657e058c6fc2,0xba1df85632bf0ac6,0x17e25d0efc4b18df,0x89630bf22a657e45,0x4c6fc8a98774ca43,0xee98c87dd3090f7a,0x8b21dfcd443ef9ac,0x87df3090fbe6321f,0x7cca43efa1c87bf4,0x390efc8a90df9152,0x0f699485ed2190bd,0xa41216f51642bf92,0x885ef2590bde4121,0x7bc8642f7a1485bf,0x4290bdc65215f0d6,0x42bf22a21f531907,0xea4320fd44241dea,0x2c837f15107ee2b2,0x0fdc4241fba0c83b,0xf41907ec4320fd8c,0x641be1ac837c2590,0x7f261207e48240fc,0x88481bd45902fe0a,0x207ec1640fda0481,0xbf40903f421207e8,0x8240fd184817c359,0x02f84b205f05640b,0xf02c877e0590afc0,0xb20df85643bf0ac8,0x57e15902fc4b21df,0x89641bf12c817e35,0x90afc6b20df8d640]))
  | 1 => (OfNat.ofNat (certificateWord [0xd45882fa8b195f51,0x631bea2c617d3548,0x6fa6a905f4d632be,0x9a8857d5210ef88a,0x995f4d510be9ac63,0x7d35106faa221df1,0x1531be9a8437d358,0xc2fa6a205f54043b,0xe22a617d35082fa6,0xa085f4d740bfa2c6,0x17d35c82fa6b885f,0x4d741bfa2c637d35,0xc86fa6b085f4d742,0xbfa2c657d35886fa,0x6b105f4d642be9ac,0x837d35902f8a6a17,0x714d41ae29a837c5,0x3506f8a6a05fcd64,0x0bf9ac837f3590bb,0xa8621ef50c43bf9a,0xc877d25442fa4b10,0xdf49441bea88857c,0x45486fa4a18df544,0x32be1aa437d25882,0xfa4a205f54042be2,0x2a417d250c2faa01,0x95f0d520be928217,0xd25d02fe8b105f49,0x730bf9ac417d25c4,0x2fa4ba0dfd1621be,0x92e637f35886fa4b,0x085f49743bfa2e65,0x7d258c6fa4b185f4,0x9643be92c837d259,0x02f8a4a1df14941f,0x6292816c52502f8a,0x4a05fc9640bf92c8,0x37f2590fda842177,0x4d442dea10857f25,0x90af8a498df14930,0xbf92c617f258c6fe,0x6ba15fc9743f6990,0x65dd320cafe4b195,0xf11432be8ac217d1,0x5102faa020df1151,0x0be8a8617d500c6f,0x86a885f45420bea8,0x0437c25442fa2ba0,0x5fd1610be8ae615f,0x35842fe6b085f457,0x20bf92c217d15d0a,0xfe8b90df45732af9,0xae437f35c86fa2b1,0x05f45743bfa2e637,0xd158cafa2b185f45,0x643be8ac857d1590,0x3e8a2a1dd14543be,0x28a877c5150af8a2,0xa05fc5640bf8ac85,0x7f1590fea8220fb4,0x9441ee9a883bd411,0x06fe2b20df14532b,0xe28a6177158c2fe2,0xb185dc5632bf8ac6,0x57f35d06fe2ba1f5,0x4c431fa98863f521,0x0c7ea2018fb49431,0xee99063dd310c7ba,0x6018ef51431bf8ac,0x63dc430c7e88218d,0xf11431be28a417f1,0x5882fe4b98dfc573,0x2bf92e837f15d0be,0xa4210fb48421bf8a,0xc437c45086f86a10,0xdf41741bfa2e217d,0x05cc6fe6b885f417,0x21b792e217f25c42,0xfa0ba15fd1720be8,0x2e657f35c82fa0b1,0x0df41743bfa2e617,0xd058cafa0b18df41,0x643be82c857d0590,0x6f8a0a1fe14142bc,0x282857c5050af8a0,0xa0dfc1641bf82c85,0x7f0590ff280207d4,0x5440f692881dd351,0x037a80205fc1640b,0xe282657c504c6fe0,0xb18dfc1632bf9ae8,0x17f05d0ff2601877,0x4c030bf82c617c45,0x0c2f8a090dec1621,0xbf82c436f25cc2fe,0x4b985ec1732bf82e,0x657f25d02fe0ba17,0xa48020fc98041f92,0x0083f220107d4542,0x0f699041ed21083d,0xa4010774d420dea2,0x8417f05883d88410,0x7e10020be228417c,0x35082fe2b905fc17,0x21bf8ae617f05cc6,0xfe2ba05fc1741fc8,0x8021f510042fe0b0,0x85f11410be1a8217,0xc25042fe8a085fcd,0x410bf928217f4508,0x27e8a106fd1420af,0x9a8417f35083be6a,0x105fd1430bfa8287,0xfb5050af6a0a15fd,0x4142bfa8283f905d,0x037a85a05fd1440d,0xfa2e81f820d02fea,0x0995fd4131af9a88,0x17f35103be6a207e,0x41730f692e61dd43,0xcc3ba65985fcd430,0xee18e61df35cc3de,0x4b985f11730bfa82,0x437f250c2de4a205,0xfc9440f792881f93,0x0c83f20b907e4432,0x0f6a16417f25083f,0x081907bc9720fda0]))
  | 2 => (OfNat.ofNat (certificateWord [0x3d4c0000000002d8,0x0000069110800118,0x000000000008ad0c,0x227000000628bb22,0x8000000000002e85,0x3809000994c50003,0xc084800132412000,0xf80c600030c7f800,0x0f28288880000053,0x0000003ec390c48f,0xb08c540000000000,0x0000000484a442b8,0x9f0d4000a5125000,0x70c0023d00087400,0x00038e0140000000,0x0858fb8290000b40,0x01ae2b4000000000,0xa02e50f8e8000000,0xc829e5446442706b,0x3a60380000010c41,0xc000004100004900,0x00003d46f2693d87,0xc4fc0003b6570000,0x000009f84500039a,0x0005f0a842a4d8e1,0x0000a84a83380035,0xe0014e80000096c4,0x71fc03e18c000a51,0x524e4d38fa00044c,0x7980000059cb4266,0x35823ca00000003c,0x942a2a0ba0002400,0x0000498b6a9a0009,0xa8151c8432001239,0x6521a95c9f9cc190,0x5b00003a06c97537,0x8343bc001448004b,0x41b00d0b00004e00,0x011b000000cb98c1,0x062fc000004a23ac,0x9f2244e011c4d186,0x0003a4a220d2c69b,0x40000031c0000000,0x01b6128000263d20,0x00002110ee000000,0x004200000007d000,0x3b4fd0004a400000,0x154000330000002e,0x0000000000005a8c,0xa0e05520dc001950,0x002980000000024d,0x4a9a6000000f08fe,0x2aa00120a3c07c00,0x0da01d0f80005a83,0x8000818ec8842421,0xd0330000000005b1,0x4902400012a2238c,0x0000016e0ec38cd5,0x90a3dc8680000000,0x02f07c05536a0000,0x0049000001280b32,0x663853a287000254,0x3d00045200000043,0x000204830004e228,0x44e0000000800005,0x6000004200001180,0x0006080000060000,0x01c0000034000003,0x8000002000004e00,0x0007c00000180000,0x13000001400000bc,0x000028800005c000,0x006c000012c00008,0x2000009800000080,0x0000200000058000,0x02100000d2000054,0x8000004000007d00,0x0001000000b40000,0x0100000c800000c2,0x0000000000029000,0x0003000002c00000,0xe4000089800004f0,0x0000160000000000,0x00000000a8000005,0x6000001000000380,0x0008e000002e0000,0x00c0000118000025,0x000000e000020400,0x000080000a600000,0x0000000000000018,0x000003000000c000,0x00dc000004800000,0x0000008200002bc0,0x0001600000010000,0x000000001800003e,0x8000009000004c00,0x000bff280985e540,0x43fca8087f940482,0xf2a0217e54042fca,0x0221f930442f2a02,0x0de54031fca8083f,0x9500c6f20b995e41,0x621faa0a63755110,0xfeaa221fd50521ba,0xa8885f55110bea82,0x887d48510ba8a881,0x7515082ea2b195d4,0x5630f6a12656d521,0x0fdaa421fb50921f,0x6992436d25106da4,0xa18fb50920b69288,0x16d25cc2da4b8877,0x50d32ae9a885dd43,0x4c6ba6a20f750d30,0xee992615d35102ba,0x6a10574d721ae9ac,0x21bd435067a8a18e,0xf509409ea28417d4,0x54cafa8a98df5153,0x0bea2c877d45486f,0xa8a905f51642bea2,0x8657d45442fa8b20,0xdf51431bea28437d,0x45902fa8a185f514,0x20bea28217d45cc2,0xfa8b905f51710bea,0x2e637d45c86fa8b0,0x85f51732bea2c437]))
  | 3 => (OfNat.ofNat (certificateWord [0xa6dc000000000000,0x000054e000f98b43,0xc6a2c00000480000,0x6100023089400000,0x4944c0000000002a,0x80000000082c0000,0x025a000000160007,0x58002a1000680638,0x00000000001e7000,0x0000000005000078,0x8dd39413c9e17f14,0x800000116000000a,0xb108000000428000,0x000004d800000001,0x1b9a904e6d82f000,0x0789840000000000,0x04e800392a340180,0x0000000df1810420,0x006b0000007600e0,0xf7376000e8823000,0x5040b96126e00009,0x9780000012a87200,0x01d50a00000067c0,0x3188146000001ed3,0x0697953147000000,0x0000000097000000,0x4360007e8824ee50,0x93b29c00000006a0,0x02bca808e19e0008,0x983711200032c1aa,0x235200010b96b132,0x0000000000047c00,0x1853441580781100,0x04392fa2e0006751,0xc000290000000000,0x0000000262000648,0xd1a432c4704ac800,0x0587d0440e630400,0x100976000934001d,0x70808d0180af29e3,0x10000fc466915060,0x001b43d8000b8180,0x950001b90009e80a,0x00000084ced0d900,0x000067a7c34a000b,0x307f000000949640,0x00000000001f2000,0x0000019caa000122,0x0001807791a00008,0x80020f000000321c,0x400098c3da640328,0x1000002000910000,0x0000094c000004fe,0x490000000ca54cc7,0xa352680000002411,0x68ec00000000000f,0xd8002021c41882b2,0xf864c001b300077c,0xee80045a000cc010,0x49e000e285f5000f,0xcf400050c0013380,0x0000478000000008,0xfc0f275296980001,0x5100000000045000,0x0f4ce20300005514,0x1fe45e00058a8300,0x0394ff83b3a40000,0x00001e8960001994,0x643a800061000258,0x48259232a9000000,0x0007880000000000,0x1451960005e40024,0xb000000dd00b37e1,0x880001b3800011d1,0xea3369cc8a800204,0x57c0024900000000,0x00024e9b80010400,0x00006e2940007501,0xc800064480000590,0x10514000000003b8,0x0029f0005ed1812c,0x0006c0198ac23a00,0x0000000000009d10,0x016e001391ad51e2,0xb4878003fa8f8001,0x5d00000000000000,0x00000160378a2140,0x8cd00034c000003b,0x81a4f78000de0005,0xe9f2216000d88000,0x000000012325e798,0x500001125c400000,0x1000015280000000,0x0780000000006c21,0xe286920000002200,0x00000d23aa870000,0x681224ac0015b350,0x000e58000006c82e,0x000000000be81829,0xa000b784d1929ac0,0x0000144001038524,0x6c0000024c000000,0x002970a25e84386d,0x1aa12d3e80a25ca6,0xc001170008800000,0x0000001360980000,0x000022c00000003a,0x8c370110ab80051c,0x328398000404a03f,0x1eb2b09e09d90900,0x09a0002023540004,0xa05a000000000002,0xd21094c8d02e4000,0x000002fc7414b000,0x000000000003ea35,0x0c68700986006093,0xd0009182c0000000,0x0000187504000001,0xa1218a8d3d8003f2,0x001189e520683800,0x1ce0007900029201,0x81e0002564725187,0x6000262a4c558000,0x5e000b9800000278,0x0000000262c17152,0x2ea6684b8d140a2b,0x8000530002c82080,0x01be5394208d0007]))
  | 4 => (OfNat.ofNat (certificateWord [0x5dc001,0x841ce35c71174000,0x9e40000037a4d400,0x00449c0000000020]))
  | _ => 0
def g0K4 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x7450c757654c4319,0xd597318c65d65cc6,0x31b5d95310c67565,0xd06418f597419067,0x761515329dd85454,0xc27565d0731ad518,0x31d06d46345741a7,0x4db45d06b46150f4,0x19dd8535d0277614,0xd742d6543351074d,0x25cd441975973190,0xef16010731dc4173,0x1886e52610731b94,0x9b10cc6d53610731,0xa751b35cc6d46150,0xf31e550f41cc7682,0x0d45209bc98450c7,0x6950c9431d948725,0x0c74d32c9431cb51,0x7250c66d65c8632d,0x3cdb250c76716c94,0x31f14c7250c72f45,0xc94319bc9b158c36,0x726c5630da543251,0x074d35c94419b597,0x2190b4f35c94419b,0xc9b159026f261454,0x3d9c985150ecd360,0x8321ab51820c86e8,0x6050b21dac172188,0x67a600d4219e9804,0x50867a6011431dc4,0x42500c7692594031,0xd64c2500c7394594,0x0319e596108c35b3,0x694031dcc5a500c7,0xd13194031ced1650,0x0c76b25940319e98,0x3158cb7260c5632d,0xa496501075935940,0x419e596109035b35,0x94041dac96501067,0xa60c56429e980515,0x0f726014543b64d8,0x20842b94608210ba,0x18940842eb26c421,0x09bc9b358434f26c,0xd6109e98335c875a,0x60cd72197cd84544,0x26f26115109b5973,0x28ca5d65cca329b5,0x974290a3d65d0a42,0x9bd89454c26f6251,0x5109b59742882b96,0x0d1742ab51820d0a,0xac6250342ba18125,0xd0ba820d0342d50c,0x7524c75950cd442d,0x55473510a5d65cca,0x4397cdb259065f36,0x14940d3cd852502d,0x9600c732a751831c,0xcad46150f32d5c57,0x328ca766111432dc,0x5425110b55359444,0x29d5962190757359,0x44429d9872590e76,0x6114940d99845250,0x2f1600c621ad5183,0x1886d46350621b5c,0xdb218866e2641741,0x9e980450ca6e2641,0x743dc5465010b593,0x5940429e59620903,0x5b3594042dc94650,0x10ae96010a20ae51,0xb05882e86250220b,0x9584428836515882,0x32b34d842882cd36,0xc8620ea503428836,0x8208174297cd8454,0x8276611152097cd8,0x454867a601152197,0x5974390e3d65d0e4,0x397d8d454865f635,0x151097597438c6b5,0x61d1743a751831d0,0xe9c6350743b51853,0x5d0f9431d0743da0,0x8235483695094843,0xd95465210e6d658c,0xa429b98b359026e6,0x214d41d398853506,0xe51608232ab51820,0x8cae86050a32bac1,0xb328ca5e36457409,0x78d915d0b7150944,0x43d954a5110e7565,0x8c641d994a5110ed,0x96010e31b641b328,0xc6d56110e31ad51b,0x158c6d46350631b3,0x588438c6cd26cc23,0x1e5507438c771519,0x4043da54a5010e79,0x658c240da94a5010,0xf7251940439e9833,0x590a7a6014d41d69,0x8053506f11608230,0xae518208c2e86250,0x230bac9b308c26e6,0x2115309d984454c3,0x5431857439b98845,0x4c67a60115319d98,0x4454ca7a6011532b,0x65833590ed906cca,0x43b55873590ecd62,0xcd643b349b3090ee,0x960c9642b9587259,0x0ae5168ca42b34db,0x2590acd36c8642bc,0x58315906f1068864,0x1b949b15906e526c,0x4241b54db1590755,0x310d641bc45b0590,0x2f1168c240ba49b0,0x5902d936c1640b64,0xda10903692009640]))
  | 1 => (OfNat.ofNat (certificateWord [0xc27716816329dc58,0x258c2771611630d9,0x49b158c35535c563,0x09dc58158c274614,0xd7409dc58458cb67,0x1548632d54d7158c,0xa7716096319d1853,0x5d0a77168d520f14,0x85320c6e52610431,0xf14c5250c765250c,0x710b5585320c6d56,0x14c031e54c5450c7,0x5535c5631b54d841,0x0c6d56110c31b511,0x9310c755350c710d,0x54d43188755150c7,0x30d545431ccacd62,0x10c31d349431cc27,0x716116209bc9845c,0xc67716117328fd18,0x35c425f36117109b,0xc9835c426f261171,0x0d9c9521c434d36c,0x97109b59420c866c,0x26417419b59420d0,0xa5f36117209e1814,0x54ca7860515219ec,0x1a259067b0689643,0xdc4585050b693214,0x142da4845050b692,0x014142da4985050b,0x593614142ce51850,0x50a7b0689640da10,0x85050a7b060d641c,0xe51440082e862500,0x409ec1a258c67b06,0x116319ec18458ca7,0xb06857329ec18358,0x867b0611621dcc15,0x108876925c1621d6,0x4db058867b060562,0x09e18125d066f261,0x1730da41725cc365,0x16c9730d3c9532cc,0x26d65082329b0990,0x5d0e6f26d41319ec,0x1845ccb7116c1732,0xda49705ccb5b054c,0x3329e594208c2786,0x0497439ec1b524c7,0xe11048420bc45840,0x083e12045420dc45,0x4208c3c9304c820b,0xa58132082e960484,0x20f248135083a920,0x51420da49705882e,0x92610020ba580420,0x82e84648020da494,0x20843692508230b6,0x4d84008359350821,0x0da41420c8769050,0x8232b95844208365,0x1508232b34d84208,0x34d35083219dc584,0x5c827b06117219dc,0x5845cc27b0611731,0x8fd18250425f3609,0x4108fd18350425f3,0x6114109bc9835042,0x6f26114109e59710,0x8427565c42108fd1,0x8350833515d1420c,0x74d7450823d65d03,0x42ea483450825f36,0x11420d64c3350835,0x515cd420d34cb350,0x831d45cd42097597,0x30ccb4f26cd420d6,0xc1b35083c920cd42,0x0c7d17350825f36c,0x1621d6cdb058876b,0x65480209e5972088,0x26d65c8220bad952,0x00827965cc230975,0x97308c27965d0240,0x8f597409027b6051,0x5329ed8145486796,0x5d0320ae51820d02,0xe86241740ab49b45,0xd02b86050b40d50c,0x7504c75515cd440d,0x3497351025d65cc2,0x4397cdb059065f36,0x14142d6cd85050ac,0xd260c730a751831c,0xc2d46150f30d5c57,0x308c27b60497419b,0xc98450c27b604974,0x3d9457251034d35c,0x94409b5972090b4f,0x35c9440bc45840c8,0x37115c8230ba4984,0x0c82d93610320d64,0xd720842ad46c9720,0xba18142c83a942d0,0x32097cdb25c434f3,0x6c97109dc5835082,0x771611420dc44315,0x0836521c5420d54d,0x7150833545c54209,0xd597108876726c54,0x20dcc1b15083e120,0xc5420cdd17150835,0x735c54209dc5b05c,0xcb7316c17329dc5b,0x25cc36716c97309d,0xc58450c36525c544,0x0d54d7151027565c,0x4241d5cd71510367,0x25c54409dc5b0590,0xe771614142dcc585,0x050ae5260c710ad5,0x1831c42d46350710,0xd5cd7108423f460d,0x42197cd845086756,0x5c86219b59721887,0x3950d1431cb49745,0x0c63d65d0743e54c]))
  | 2 => (OfNat.ofNat (certificateWord [0x6896439e41a2590,0x7655154843d94954,0x1107655150842d94,0x9541c43953150d41,0xc5515310c755454c,0x431d54d541107555,0x150c439d584454ca,0x756111530cd51531,0x0c7355150c439d55,0xa5110e77654c6419,0xdd95418c7553114d,0x41d5584535067561,0x11520cd515210c75,0x52114d419d584525,0x027561c9643d5545,0x3510a7556944429d,0x584450cb65611494,0x0d9495100c735454,0x4031d54405350675,0x16141429d45b0590,0xf651549440d54553,0x51027516116109d4,0x58450c27516c9730,0x9d45b05ccb65154c,0x820d545535083351,0x5514209d45825842,0x7516114209d45835,0x082751611730d545,0x7358427516117209,0xd45845ccb5515cd7,0x219d458458827516,0x8d520d9455428ca7,0x516856329d458458,0xca7516856309d458,0x458c27516096309d,0x45a058ca75168963,0x09d4582590275168,0xd6429d45a359034d,0x3550842d35494310,0xf4d3550b219b5884,0x54c66d6211530cb5,0x15320826d6214d41,0x9b58b359026d5694,0x843d3588535066d2,0x6115109b49b35843,0x4d3548420cb51521,0x0826d26145439b49,0xb159034d254d4419,0xb498458866d26c56,0x30d3495300c72d25,0x514319b498358866,0xd2611431cb515200,0x834d254d440cb495,0x401026d26116209b,0xd952090a6d261143,0x09b498450426d260,0xd4109b49b504c74d,0x2550f309b49a05cc,0xa6d26117309b49a0,0x58866d26117109b4,0x9835c426d2611731,0x9b498458426d2681,0x7319b498458c66d2,0x6116309b49a058c6,0x6d260d6419b49a05,0x90e6d2681641974d,0x8454865d3611520c,0x7515320c65d36149,0x40974db259065d36,0x11632974d8454431,0xd454c431c74d5411,0x065d361163197d95,0x3190e5d361142197,0x4db25c431d454c03,0x1974d85050a5d36c,0x1641974d8458c25d,0x36c1621c74d54508,0x25d3609630974d84,0x50825d3611410974,0xd8250425d3611720,0x974d845c425d36d4,0x520974da158ca5d3,0x611721974da158c2,0x5d3611610974d825,0x8425d3681721974d,0x8458865d36116209,0x74da158825d36096,0x40974da1590a5d36,0x856408f518359063,0xd460d4218f518259,0x023d460d4208f518,0x350423d46094108f,0x51835c423d460961,0x08f518358863d460,0x96301f597059023f,0x46096309718d4548,0x65c635151097cda1,0x59025f3685642c75,0x18535065f3685643,0x97cd8259031d4510,0xc3197cda158825f3,0x6116208fd1835886,0x5f36116219b18945,0x4c26c62515109bc9,0xa059066f2681643d,0x34d8525032d46149,0x409bc9a0590a6f26,0x0d641cb514420826,0xf26816319bc98458,0xc26f261163197cda,0x05c866f26817318f,0xd18258425f360961,0x097cd8458434d26c,0xd61097cd8358425c,0x36457409bc984584,0x25f3611721d3cd53,0x2c865d650c732970,0xd915d0a5f36d4520,0x9759431d0e746151,0x5329d185454c2771,0x68d6409dc5a3590b,0x652614543d54c851,0x50f553114543d54d,0x85150f553014543c,0xd5185150e77168d6,0x41d510c5150e7716,0x09640cd514410c6d,0x463504419dc5a258]))
  | 3 => (OfNat.ofNat (certificateWord [0xc9e428000000000d,0x306b52440c0017d0,0x00000000002de86c,0x0d07639c00000088,0x142464eb0005523a,0x4cd86e3123c810a9,0x3460878002b816a5,0xf82a8f60f8278110,0xea3f44c84ba17452,0x1784fa361b089895,0x8710b63c4228c11b,0x81b5261ee3cc840c,0x69b42b43311c8704,0x12319359065809c0,0x0884b56056561000,0x48c430ae80003e00,0x0118bc00076cfb95,0x6164411029c001c7,0x4d468a60106a4032,0x41134604b18324d8,0x2a4160373be2e54f,0x8d108e6ad5280040,0xc001568000005013,0x0a7529e4d5138001,0x9054c2caa139a000,0x5880029644000035,0x546a142d16b32e00,0x0c994e00032ccf02,0xa170524051b541a7,0x14600ba3ea1347f8,0xcd26e33c539a2186,0x868200f812649143,0x9783483e55007504,0x89c5238f743e7f03,0xd0070a69f1118ae3,0x6c2b0061bf11e0b4,0x260c21205412895e,0x2fe7b51e0870f20e,0x03ba9122ca04ba12,0xe59a8549d0131da2,0xd040a550004a45da,0x131466b89e1d5354,0x4a804900562a9952,0x1eb4246e81b0d707,0x272115999474730e,0xc9ef5141048a1213,0xc83753797b1007fc,0x2b1be1325449a294,0x51c9104484358a64,0x03da5a0006e0f90f,0x5104000d025341c1,0xa8000de396000a39,0x111160514d000566,0x0012525838e38c4d,0x8540909f4628ab2e,0x4156c0e52814f810,0xf06086040182b533,0x528410284003a1cb,0x800600a820c50e9c,0x024440d0a24a020a,0x6ca85342300b0404,0x304041810e040410,0x1002858062248861,0x404e8204f8080086,0xc0833a005240a0c2,0x9e08000103014630,0x1a0000a1e5803302,0x480a226101900000,0xb00124c4271000a0,0x03a0400102145088,0xc8c2870400980161,0x9c051a0418006080,0x0a02080860400197,0x1408080261c00202,0x00006141800114b0,0x1071600582040000,0x0020800100600010,0x01819c222c1840c6,0xc802100000010200,0x140204e811800302,0x0278583060c08100,0x00002000f7150544,0x43dc5415110b7115,0x50040dc541411077,0x15048431dc455300,0x83711550230da541,0x5210fa92050940ca,0x5152008369454802,0x0da4954010369505,0x0842d64d54010359,0x5050c43d64d54084,0x27960115329e5804,0x54c739454c0209e5,0x80535067960cd642,0x9e55a5010f596014,0xd419e58045487394,0x548020d65413510b,0x3950508429e55a50,0x10a7b65482409e58,0x0450ca7b6550220d,0xa4c0525036920149,0x40da580525027960,0xcd721d64d5100833,0x94544020da440525,0x027960145439e583,0x1590b695049441d6,0x5413510679569404,0x19e583158cb69504,0x9431d6541320c739,0x50514319e55a500c,0x67960114319e5804,0x508679600d421d6c,0xd5308435960cd721,0xdc5805150f731544,0x230dc583158cbd11,0x04c031bc580410c7,0xd1504c431b658043,0x0c67906117319e41,0x845c876905c97109,0xe41b524c7590550f,0x329e41a05ccb5905,0x0c7329e41845ccb7,0x105506219e41a058,0x8771050c6219e418,0x4588679060d6219e,0x41a15cca79061163,0x29e418458c679068,0x96319e4183590679]))
  | 4 => (OfNat.ofNat (certificateWord [0x5,0x942fa8f4a88d5442,0x5c50c554000f00ca,0x3d1699f321200000,0x0002f8a40d400028,0x24d81f02e000670a,0xc1bd3ecb0c221151,0xf47d141a96150b05,0x1880032465400000,0x31600017abe00094,0x03f9310000015e80,0x00001e1690db3004,0xf8aa26e20e8b477a,0x9947cadc001770fc,0x000001ac24a0014c,0x0013f655c8b85203,0x0994e491825e0001,0x2abf45e37cf19753,0xe00002b80030a000,0x00108000000f414d,0x0c4174e30003b0a5,0xc0011f1a6810c780,0x028a77089a573fa6,0xe52f8e2000a2c762,0xc90008607982709c,0xad100a725a014562,0x2b60944e4a40d41a,0xa7796788c5767452,0x49da4645c46d0004,0xd28004b23315a7a8,0x8d000000a7400000,0x538000b600000000,0x0b716254e3ad662c,0x74766ecd6a5d5560,0x00100b00c07e52f1,0x0a13839d0e8722d2,0x7b13f24318e4b4a3,0x1af276014bd26210,0xc43d652a200067cc,0xe8630000400e2604,0x4093cc39b224c001,0x560003109d85008e,0x4808885e9d73f078,0x90600034a0001e84,0x607e8f4ad8a50004,0xa0980bf1a498c729,0x234f079d40120360,0x780ae1832c29ed05,0x800000b2d1206c21,0x65c0002342844040,0x00a429881c6727f4,0x323ec2e28418800d,0x152645185d95e002,0x32cab85516739e99,0x82488310a46d6a24,0x523a2d90e0690366,0x4473042512b21368,0x6736e7512d88d23c,0x049351860e851027,0xa954b249c0e8000d,0xeb19160260004711,0x28000005a8308003,0x94000000d6000908,0x7200000032529000,0x0000541d0001c068,0xc000000002bc8900,0xb3866c4001f15747,0x84000000d0001170,0x0036603c000d01b2,0x83d338003880010a,0x1e92f27940000000,0x04f52400059c4fc0,0x000020a8580029e0,0x522f8cd0732663b8,0x7e1a70fa16018aa8,0x3780584a1a111427,0x48718a2cc8e0c628,0x23fca6c5ba284f42,0x54ee90d3a4abc960,0x920560cc650fd270,0x9d07f1733a050d59,0x2b54ac638cc06449,0x619859aaa2be5a10,0x116d47e384c114a3,0x080c0b22b902e000,0xb01c100028968a77,0x078548ca2032449a,0x0000341309340f00,0x02040ec0020a4e67,0x0800208442000000,0x1946e3a048800000,0x0000008400000108,0x8000000341400449]))
  | _ => 0
def g0K3 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x16008c4ebc84,0xbe680064529e7c00,0x00b60000024c3c18,0x40388ac2b2ae1428,0x80980626223aa034,0x7a3088a804003200,0x92007846000c9a3e,0x902e000070008236,0x9cc8587e00b0aa00,0x6650002c62860e24,0x8ec4b456a2124a00,0x00c01008ca7642a6,0x0a1c601eac746a00,0x00b8a41a00720054,0x5e2044ba00000000,0x00c65c5a2a6c9448,0x966eb10220844610,0x1e10600018029288,0x023006109040287a,0x09aa2090841c8515,0x1048420e822092a6,0x018f1110515300c7,0x30b024c28a878c58,0x14614543ca22c9b0,0xa0a1631165185050,0xb18a2a2c20041984,0x546250040c62c0a2,0x88218e515018d411,0x07a0a824299063d0,0x5413149431e22a09,0x8a8a18f41154c132,0x083a08aa409a841c,0x84552051420c622a,0xa304118661151894,0x08c384a2a6099041,0x925816214d41c528,0xab02641062945581,0x21083849aa40a284,0x18a5192009640c52,0x8a93080106294558,0x042083143b28a900,0x411a5d44648020c5,0x24aa304108629255,0x18208c30c9b28c28,0x285865153610020c,0x32c0a30a6a0e1960,0x514430c70c9aa8c1,0x0421924d46250040,0xc926a31281085517,0x010c5150e68b808c,0x988638a415460832,0x1ca20c18ea498e19,0x0551831ccb28828c,0x2a1e658c415460c6,0x21ca20a31a8310e2,0x905518208cb82a2a,0x4299063894994614,0x543c4a8a9308218e,0x452518d4110722b0,0xa6c2928189585461,0x4940c4a8ab088410,0x705254c5450c7129,0x2a8c18e219149463,0x50710c2a8ab0a641,0x8e1545585300c70a,0xa32621ac83855153,0x610431c2a8ab0886,0x18e1476515310c62,0xaba88c98863854d5,0x460c710c2a6aa306,0x310e151551831cc3,0x0a8aa8c18e658945,0x54608232c1a6ca30,0xa4a060d454d84208,0x306b128c29a83835,0x156210c31c1a6aa3,0x04190e0d2551831c,0xc2a2b908628a8791,0x4946150f3098ae42,0x326218e45260c750,0x4c6b0b8884282859,0x84546050a32a926e,0x210a0a1649351814,0x2c8670b888c90041,0x98458208d5209926,0xe232401064936083,0x5148384a2a419a84,0x14a5d420d0342a2a,0x8e18ea098f214548,0x3150828aba863a0e,0x874a51c20d4520e0,0xa8a98e4a18f11454,0xc6500c695baa81a1,0x4414551c31d4931a,0x528e1040ba151775,0x507438c694a38411,0xaa414551c3185743]))
  | _ => 0
def g0K2 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x3100405000,0x00060270a21811d9,0x4548020a11801d94,0x54c431c211651c20,0x8d520a09381d9454,0x8020c093651c20d4,0x520c110651c31d49,0x31a05821d9454c43,0x1c052651c31d4131]))
  | _ => 0
def g0N (k : Nat) : Nat :=
  match k with
  | 2 => 8
  | 3 => 102
  | 4 => 725
  | 5 => 682
  | 6 => 40
  | 7 => 1
  | _ => 0
def g0R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g0K2 (i*60) 60
  | 3 => packedAt g0K3 (i*49) 49
  | 4 => packedAt g0K4 (i*38) 38
  | 5 => packedAt g0K5 (i*27) 27
  | 6 => packedAt g0K6 (i*16) 16
  | 7 => packedAt g0K7 (i*5) 5
  | _ => 0
def g0I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g0K2 (483+((h/3+packedAt g0K2 (480+(h % 3)*1) 1) % 18)*4) 4
  | 3 => packedAt g0K3 (5168+((h/34+packedAt g0K3 (4998+(h % 34)*5) 5) % 128)*8) 8
  | 4 => packedAt g0K4 (29244+((h/242+packedAt g0K4 (27550+(h % 242)*7) 7) % 856)*11) 11
  | 5 => packedAt g0K5 (20466+((h/228+packedAt g0K5 (18414+(h % 228)*9) 9) % 1138)*11) 11
  | 6 => packedAt g0K6 (710+((h/14+packedAt g0K6 (640+(h % 14)*5) 5) % 49)*7) 7
  | 7 => packedAt g0K7 (6+((h/1+packedAt g0K7 (5+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g0Pos : Nat → Bits
  | 0 => 0x0
  | 1 => 0x0
  | 2 => (OfNat.ofNat (certificateWord [0xfc513c2f3dd6fa97,0xdba5e0f76bcd679e,0xad555f48b72d2ed2,0xd297b4bfc513c2f3]))
  | 3 => (OfNat.ofNat (certificateWord [0x2ca245e7cf4f7dbb,0x4dc42f7bb5d7aaab,0x37ab495d5b563265,0x772bdbf2ca245e7c]))
  | 4 => 0x0
  | 5 => (OfNat.ofNat (certificateWord [0x5514e8f91b3fa9dd,0x886ef7bd66ebd3d5,0xa53e6e6a6d9b6c59,0xbafe9555514e8f91]))
  | 6 => (OfNat.ofNat (certificateWord [0x9a28ff4248ffd110,0xeef77bdeb972e2e7,0xc7cf8b8f8ee3b76f,0xe34d1a69a28ff424]))
  | 7 => (OfNat.ofNat (certificateWord [0xe3cf9294a7fe1ffe,0xff7fbdef3e7cfcf9,0xf9f3f3f3f0ffc78e,0x3c71e38e3cf9294a]))
  | _ => 0
def g0Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x0
  | 2 => (OfNat.ofNat (certificateWord [0xfc001c07322801e0,0x00783e00007f0000,0x01fc03fc000007f0,0x0001fc0fc001c073]))
  | 3 => (OfNat.ofNat (certificateWord [0xe7c0b00000,0xf07fc000000000fe,0x01fffc0000000000,0x3f81fff000000e7c]))
  | 4 => 0x0
  | 5 => (OfNat.ofNat (certificateWord [0xe0f804c01e00,0xff8000003f8000ff,0xfe0000000003f800,0x3ffe0000000e0f80]))
  | 6 => (OfNat.ofNat (certificateWord [0xff0007001fff,0x000000003fffff00,0x000000000003ffff,0xc0000000000ff000]))
  | 7 => (OfNat.ofNat (certificateWord [0xf00000803e000,0x0000000fc0000000,0x0000000000fc0000,0x0000000000f00000]))
  | _ => 0
def g0Atlas : Atlas := ⟨7,rawDecor 236 g0Pos g0Neg, (OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffff0fff0,0xfff0fff0ff00ff00,0xf0f0f0f000000000,0xffffffffffffffff,0xfffffffffff0fff0,0xfff0fff0ff00ff00,0xf0f0f0f000000000])), g0N, g0R, (fun _ _ => 0), g0I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def g1K5 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0xeac000260c1,0x00000000f2c8488c,0x000080000002000a,0x5c72a00480252855,0x4a83400d80302c68,0x04001100127921c0,0x21930046000003e9,0xcc8a3a0042000038,0x0004000140000080,0xed32fd43fd42fd41,0xfd40fd32fd31fd30,0xfc43fd21fd20fc42,0xfc32fd10fc41fc31,0xfc21fc40fc30ec20,0xfc20fc10ff40ff30,0xff20ff10ff41ff31,0xff21fe10ff42ff32,0xfe21ee20fe20ff43,0xee32fe32fe31fe30,0xfe43fe42fe41fe40]))
  | _ => 0
def g1K4 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0xc000043351,0xc30002f090a2d391,0x6000d4e242c592b0,0x12e26254115420f3,0xa0b36041f5751174,0x55618323f2148540,0x21e4911292223194,0x7002052124d3c335,0x5033e2a074b341a4,0x04c38501d004f4a0,0x02731080000000e0,0x0530613000000000,0x000001000003d281,0x45844003b00001b0,0x00500465a3728192,0x77a28c0982b0ca81,0x006a8118002084d0,0x400400218d795010,0xef2a020de54031bc,0x82e857905886eaa2,0x21dd45430ba8a841,0x75159039a6498534,0xd420b69ac656d521,0x0eda6a105b4d620b,0x6928836d250c6da4,0xa185b49740b692e6,0x16d25c42da4b98db,0x49643ae9a8835d35,0x0827a8a18cf51430,0x9ea28413d4584278,0x8a98db14940b792c,0x876c524c2d84a884,0xfd1610ba28a87771,0x59036a8220dbc973,0x1b792e2168504cbd,0x0a0995e14132b628,0x2656f058caf60b10,0xdbc9730b792e817b,0x05d0bd280107a440,0x20f28a841cd35083,0x5a8a105bc1620f41,0x80413f450835e8a1,0x057cd420e79a8413,0xf450c3d6a0995ed4,0x132e699661e820cc,0x2de4a185dc5420f3,0x8a84177150c27e8a,0x18ddd4543af9a883,0x6f250c6de4a20de9,0x4031bd28083e8208,0x42dea4a05bd4930b,0x712a216f05083d04,0x1105b94843e69946,0x56f250caeca221de,0x94043b612c616e25,0x8c27c8a98fa08240]))
  | _ => 0
def g1K3 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x202800000000,0x0001ca24b800000b,0x0780a8c0004224ac,0x38610098001821a0,0x1458000000200016,0xa03493550020d24d,0x510083153550441d,0x1455350832515514,0x20c34d5450824d36,0x09630d8458504cb4,0x93614132ca518504,0xca6b06896309a181,0x25cc6686049643b8,0x4583008361150824,0x0aa5183008329450,0x8210c34d7450832b,0x4614132b24d820cc,0x2c8604cb30d14d71,0x5083631614132b24,0xd820842c93608240]))
  | _ => 0
def g1K2 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x1243,0x005904593614132c,0x422ca30a09964115,0x4d820903049b28c2,0x8265825153608210]))
  | _ => 0
def g1N (k : Nat) : Nat :=
  match k with
  | 2 => 5
  | 3 => 25
  | 4 => 91
  | 5 => 44
  | 6 => 1
  | _ => 0
def g1R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g1K2 (i*49) 49
  | 3 => packedAt g1K3 (i*38) 38
  | 4 => packedAt g1K4 (i*27) 27
  | 5 => packedAt g1K5 (i*16) 16
  | 6 => packedAt g1K6 (i*5) 5
  | _ => 0
def g1I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g1K2 (247+((h/2+packedAt g1K2 (245+(h % 2)*1) 1) % 7)*4) 4
  | 3 => packedAt g1K3 (1004+((h/9+packedAt g1K3 (950+(h % 9)*6) 6) % 43)*6) 6
  | 4 => packedAt g1K4 (2643+((h/31+packedAt g1K4 (2457+(h % 31)*6) 6) % 115)*8) 8
  | 5 => packedAt g1K5 (794+((h/15+packedAt g1K5 (704+(h % 15)*6) 6) % 68)*7) 7
  | 6 => packedAt g1K6 (6+((h/1+packedAt g1K6 (5+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g1Pos : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0x3c24f9df5d57d7db,0xabc1f6e3bbaedcf5,0x5aabf516eaeb2d59,0x6a97acbfc67849f3]))
  | 1 => 0x0
  | 2 => 0x0
  | 3 => (OfNat.ofNat (certificateWord [0x454bbe7d3efbfb4d,0xc85efb6ddcd77559,0xed5b17ab732c5662,0xbf2bf3f2d88a977c]))
  | 4 => (OfNat.ofNat (certificateWord [0xe8e3c8b4f4dd5d88,0x6def71f6e99b9ead,0x49f3654dbac99b4c,0xdafea55543d1c791]))
  | 5 => 0x0
  | 6 => (OfNat.ofNat (certificateWord [0x92fd1373fffe90fe,0xfef7bdbb76e5d73e,0x7e7db9f1dc72e3f7,0xf34d3a69ad25fa26]))
  | 7 => (OfNat.ofNat (certificateWord [0xff92240ff890feef,0x7f7bde3c78f9e7cf,0x8f9e3e7e1f7cff87,0x1c71c38e31ff2448]))
  | _ => 0
def g1Neg : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0x1c0039a0a0e00000,0x707c003f80000000,0x0fe03f80007f0000,0x0001fc0fc0380073]))
  | 1 => 0x0
  | 2 => 0x0
  | 3 => (OfNat.ofNat (certificateWord [0x3be02c00000f0,0x7f800000000007f0,0x0fffc00000000000,0x1f81fff00000077c]))
  | 4 => (OfNat.ofNat (certificateWord [0xe0e3c04b0f00e0ff,0x80001fc000fe07ff,0xf00000001f8003f8,0x1ffe000001c1c780]))
  | 5 => 0x0
  | 6 => (OfNat.ofNat (certificateWord [0xfc000c0000ff00,0x0000000000fff800,0x00000000000003ff,0xe00000000001f800]))
  | 7 => (OfNat.ofNat (certificateWord [0xff0000700fff0000,0x00001fffff000000,0x000000001ffffc00,0x0000000001fe0000]))
  | _ => 0
def g1Atlas : Atlas := ⟨6,rawDecor 217 g1Pos g1Neg, (OfNat.ofNat (certificateWord [0xffffffffffffffff,0xffaaff00ffaaff00,0xffaaffaaffaaffaa,0xaaaa0000aaaa0000,0xffffffffffffffff,0xffaaff00ffaaff00,0xffaaffaaffaaffaa,0xaaaa0000aaaa0000])), g1N, g1R, (fun _ _ => 0), g1I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def g2K5 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x4,0xd38e0a748a446000,0x100000b12060000c,0x2a1839c2800d1f00,0x0058050011215210,0x0003c01017302450,0x010000001a3c0005,0x4052990400da6560,0x0000000000200004,0x0031100000000000,0xed32fd43fd42fd41,0xfd40fd32fd31fd30,0xfc43fd21fd20fc42,0xfc32fd10fc41fc31,0xfc21fc40fc30ec20,0xfc20fc10ff40ff30,0xff20ff10ff41ff31,0xff21fe10ff42ff32,0xfe21ee20fe20ff43,0xee32fe32fe31fe30,0xfe43fe42fe41fe40]))
  | _ => 0
def g2K4 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x8807aa800662a0,0x68a3e0044641e9c1,0x678a25ca60072508,0x67e002e468c82000,0x052a01a604c22900,0x0002c00000c387c4,0x8764000aa3068627,0x010b29a5a0a1432a,0xe283a3c840e26040,0x05e18b456b06c588,0xe54006a203688003,0x400a400420000ac6,0xe2400984a94009e0,0x092004e129674001,0xc023812461d51201,0x0b108a209c221004,0x3084214001795010,0xef2a020de54031bc,0x82e857905886eaa2,0x21dd45430ba8a841,0x75159039a6498534,0xd420b69ac656d521,0x0eda6a105b4d620b,0x6928836d250c6da4,0xa185b49740b692e6,0x16d25c42da4b98db,0x49643ae9a8835d35,0x0827a8a18cf51430,0x9ea28413d4584278,0x8a98db14940b792c,0x876c524c2d84a884,0xfd1610ba28a87771,0x59036a8220dbc973,0x1b792e2168504cbd,0x0a0995e14132b628,0x2656f058caf60b10,0xdbc9730b792e817b,0x05d0bd280107a440,0x20f28a841cd35083,0x5a8a105bc1620f41,0x80413f450835e8a1,0x057cd420e79a8413,0xf450c3d6a0995ed4,0x132e699661e820cc,0x2de4a185dc5420f3,0x8a84177150c27e8a,0x18ddd4543af9a883,0x6f250c6de4a20de9,0x4031bd28083e8208,0x42dea4a05bd4930b,0x712a216f05083d04,0x1105b94843e69946,0x56f250caeca221de,0x94043b612c616e25,0x8c27c8a98fa08240]))
  | _ => 0
def g2K3 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0xb1,0xc000280a88016890,0x0983863266ae1245,0x284a0c1e0194d800,0x3c3493550020d24d,0x510083153550441d,0x1455350832515514,0x20c34d5450824d36,0x09630d8458504cb4,0x93614132ca518504,0xca6b06896309a181,0x25cc6686049643b8,0x4583008361150824,0x0aa5183008329450,0x8210c34d7450832b,0x4614132b24d820cc,0x2c8604cb30d14d71,0x5083631614132b24,0xd820842c93608240]))
  | _ => 0
def g2K2 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x21304,0x003904593614132c,0x422ca30a09964115,0x4d820903049b28c2,0x8265825153608210]))
  | _ => 0
def g2N (k : Nat) : Nat :=
  match k with
  | 2 => 5
  | 3 => 25
  | 4 => 91
  | 5 => 44
  | 6 => 1
  | _ => 0
def g2R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g2K2 (i*49) 49
  | 3 => packedAt g2K3 (i*38) 38
  | 4 => packedAt g2K4 (i*27) 27
  | 5 => packedAt g2K5 (i*16) 16
  | 6 => packedAt g2K6 (i*5) 5
  | _ => 0
def g2I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g2K2 (247+((h/2+packedAt g2K2 (245+(h % 2)*1) 1) % 7)*4) 4
  | 3 => packedAt g2K3 (986+((h/9+packedAt g2K3 (950+(h % 9)*4) 4) % 30)*6) 6
  | 4 => packedAt g2K4 (2612+((h/31+packedAt g2K4 (2457+(h % 31)*5) 5) % 113)*8) 8
  | 5 => packedAt g2K5 (794+((h/15+packedAt g2K5 (704+(h % 15)*6) 6) % 70)*7) 7
  | 6 => packedAt g2K6 (6+((h/1+packedAt g2K6 (5+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g2Pos : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0x3c24f9df5d57d7db,0xabc1f6e3bbaedcf5,0x5aabf516eaeb2d59,0x6a97acbfc67849f3]))
  | 1 => 0x0
  | 2 => (OfNat.ofNat (certificateWord [0x454bbe7d3efbfb4d,0xc85efb6ddcd77559,0xed5b17ab732c5662,0xbf2bf3f2d88a977c]))
  | 3 => 0x0
  | 4 => (OfNat.ofNat (certificateWord [0xe8e3c8b4f4dd5d88,0x6def71f6e99b9ead,0x49f3654dbac99b4c,0xdafea55543d1c791]))
  | 5 => (OfNat.ofNat (certificateWord [0x92fd1373fffe90fe,0xfef7bdbb76e5d73e,0x7e7db9f1dc72e3f7,0xf34d3a69ad25fa26]))
  | 6 => 0x0
  | 7 => (OfNat.ofNat (certificateWord [0xff92240ff890feef,0x7f7bde3c78f9e7cf,0x8f9e3e7e1f7cff87,0x1c71c38e31ff2448]))
  | _ => 0
def g2Neg : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0x1c0039a0a0e00000,0x707c003f80000000,0x0fe03f80007f0000,0x0001fc0fc0380073]))
  | 1 => 0x0
  | 2 => (OfNat.ofNat (certificateWord [0x3be02c00000f0,0x7f800000000007f0,0x0fffc00000000000,0x1f81fff00000077c]))
  | 3 => 0x0
  | 4 => (OfNat.ofNat (certificateWord [0xe0e3c04b0f00e0ff,0x80001fc000fe07ff,0xf00000001f8003f8,0x1ffe000001c1c780]))
  | 5 => (OfNat.ofNat (certificateWord [0xfc000c0000ff00,0x0000000000fff800,0x00000000000003ff,0xe00000000001f800]))
  | 6 => 0x0
  | 7 => (OfNat.ofNat (certificateWord [0xff0000700fff0000,0x00001fffff000000,0x000000001ffffc00,0x0000000001fe0000]))
  | _ => 0
def g2Atlas : Atlas := ⟨6,rawDecor 181 g2Pos g2Neg, (OfNat.ofNat (certificateWord [0xfffffffffafaf0f0,0xfffffffffafaf0f0,0xfafafafaaaaa0000,0xfafafafaaaaa0000,0xfffffffffafaf0f0,0xfffffffffafaf0f0,0xfafafafaaaaa0000,0xfafafafaaaaa0000])), g2N, g2R, (fun _ _ => 0), g2I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g3K6 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def g3K5 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0xdd44,0x00800100018020fa,0x887b50bba877d50b,0xfa87dc43bc87ee42]))
  | _ => 0
def g3K4 : Nat → Nat
  | 0 => 0x80dc44150e350943
  | _ => 0
def g3N (k : Nat) : Nat :=
  match k with
  | 4 => 2
  | 5 => 8
  | 6 => 1
  | _ => 0
def g3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt g3K4 (i*28) 28
  | 5 => packedAt g3K5 (i*17) 17
  | 6 => packedAt g3K6 (i*6) 6
  | _ => 0
def g3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt g3K4 (58+((h/2+packedAt g3K4 (56+(h % 2)*1) 1) % 4)*2) 2
  | 5 => packedAt g3K5 (145+((h/3+packedAt g3K5 (136+(h % 3)*3) 3) % 18)*4) 4
  | 6 => packedAt g3K6 (7+((h/1+packedAt g3K6 (6+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g3Pos : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0x5ff6f4255b92bb5e,0x4a76f12a2a91b26a,0x2b27496158afee82,0xffe3478e124915e7]))
  | 1 => (OfNat.ofNat (certificateWord [0x7a12be4aada4ddaf,0xdb9282543522c4b4,0x554abbd2a957f57f,0xc1648bf02492f2f8]))
  | 2 => 0x0
  | 3 => 0x0
  | 4 => (OfNat.ofNat (certificateWord [0x6aa4d69336f6e932,0x92a4949ee7c30ee6,0x86eed25437fca595,0x4aa0fc9271c72329]))
  | 5 => (OfNat.ofNat (certificateWord [0xb347651cc74711c5,0x1c4728e779f798c1,0x18ff3f6ffa194629,0x94c91124fe07fc42]))
  | 6 => (OfNat.ofNat (certificateWord [0x3c7879e0f8781e09,0xe1784f07be7beff9,0xff8c2388c462784e,0x271622497ff84094]))
  | 7 => (OfNat.ofNat (certificateWord [0xc07f81ff007f9ff1,0xfe7f8fffc07c0f01,0xe0f03c0f07838070,0x38183fffc9248800]))
  | _ => 0
def g3Neg : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0x7ffe0000001ffe,0x007ff00000000000,0x000000000003ff80,0x3fe0038e000000e7]))
  | 1 => (OfNat.ofNat (certificateWord [0xff80000000001fff,0xff80000000000000,0x00003ff00003ffff,0xc00003f00000f0f8]))
  | 2 => 0x0
  | 3 => 0x0
  | 4 => (OfNat.ofNat (certificateWord [0x7fe000,0x00000007ff800ffe,0x00ffc00007fc0000,0x00003c0071c70300]))
  | 5 => (OfNat.ofNat (certificateWord [0x7fffff000,0x00fffffff8000000,0x000000007e07fc00]))
  | 6 => (OfNat.ofNat (certificateWord [0x7ffffffff,0xff00000000000000,0x000000007ff80000]))
  | 7 => (OfNat.ofNat (certificateWord [0x7fffff,0xfffffff800000000,0x0000000000000000,0x00003fff80000000]))
  | _ => 0
def g3Atlas : Atlas := ⟨6,rawDecor 243 g3Pos g3Neg, (OfNat.ofNat (certificateWord [0xffffffffffffffff,0xffffffffeeee0000,0xeeeeeeeeeeeeeeee,0xeeeeaaaaeeee0000,0xffffffffffffffff,0xffffffffeeee0000,0xeeeeeeeeeeeeeeee,0xeeeeaaaaeeee0000])), g3N, g3R, (fun _ _ => 0), g3I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g4K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def g4N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def g4R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt g4K3 (i*4) 4
  | _ => 0
def g4I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt g4K3 (5+((h/1+packedAt g4K3 (4+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g4Pos : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0xd5f9b1e5cbaf9c5d,0xd5f9b1e5cbaf9c5d,0xd5f9b1e5cbaf9c5d,0xd5f9b1e5cbaf9c5d]))
  | 1 => 0x0
  | 2 => (OfNat.ofNat (certificateWord [0xcf9e96ead5dda5ce,0xcf9e96ead5dda5ce,0xcf9e96ead5dda5ce,0xcf9e96ead5dda5ce]))
  | 3 => 0x0
  | 4 => 0x0
  | 5 => 0x0
  | 6 => (OfNat.ofNat (certificateWord [0xbfebfb776fb6daf5,0xbfebfb776fb6daf5,0xbfebfb776fb6daf5,0xbfebfb776fb6daf5]))
  | 7 => (OfNat.ofNat (certificateWord [0x7ebfdfbbf6db6faa,0x7ebfdfbbf6db6faa,0x7ebfdfbbf6db6faa,0x7ebfdfbbf6db6faa]))
  | _ => 0
def g4Neg : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0x2b031c3c00e38c0d,0x2b031c3c00e38c0d,0x2b031c3c00e38c0d,0x2b031c3c00e38c0d]))
  | 1 => 0x0
  | 2 => (OfNat.ofNat (certificateWord [0x3033e00078fc00ce,0x3033e00078fc00ce,0x3033e00078fc00ce,0x3033e00078fc00ce]))
  | 3 => 0x0
  | 4 => 0x0
  | 5 => 0x0
  | 6 => (OfNat.ofNat (certificateWord [0x403c00007f0000f0,0x403c00007f0000f0,0x403c00007f0000f0,0x403c00007f0000f0]))
  | 7 => (OfNat.ofNat (certificateWord [0x83c0003f80000f00,0x83c0003f80000f00,0x83c0003f80000f00,0x83c0003f80000f00]))
  | _ => 0
def g4Atlas : Atlas := ⟨3,rawDecor 197 g4Pos g4Neg, (OfNat.ofNat (certificateWord [0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa,0x0000000000000000,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa,0x0000000000000000])), g4N, g4R, (fun _ _ => 0), g4I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g5K6 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def g5K5 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x500,0x00013700402602fa,0x887b50bd8a5f431f,0xb887dcc7dea5ee42]))
  | _ => 0
def g5K4 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x20,0x086cbc58031b50d9,0x10ab518529b15942]))
  | _ => 0
def g5N (k : Nat) : Nat :=
  match k with
  | 4 => 4
  | 5 => 8
  | 6 => 1
  | _ => 0
def g5R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt g5K4 (i*28) 28
  | 5 => packedAt g5K5 (i*17) 17
  | 6 => packedAt g5K6 (i*6) 6
  | _ => 0
def g5I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt g5K4 (116+((h/2+packedAt g5K4 (112+(h % 2)*2) 2) % 6)*3) 3
  | 5 => packedAt g5K5 (139+((h/3+packedAt g5K5 (136+(h % 3)*1) 1) % 17)*4) 4
  | 6 => packedAt g5K6 (7+((h/1+packedAt g5K6 (6+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g5Pos : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0xc25764ced7267762,0x545a4ea2c47270b9,0x3457bd9377c6ff42,0xff9478e1252979db]))
  | 1 => (OfNat.ofNat (certificateWord [0xe4a9a9576bee9304,0xa864956f68aee94a,0x58abd6f792897dbf,0x8288bf025ce2be1c]))
  | 2 => 0x0
  | 3 => (OfNat.ofNat (certificateWord [0xc932d1a24c4b2589,0x3dcf1876bde4a217,0xf10dfb7f7ebf9509,0x1521092f1f073fe0]))
  | 4 => (OfNat.ofNat (certificateWord [0x71ccfddc718cc631,0xcef7ddc330c8cc67,0x7ffe93a5a4d1a9d5,0xa98fd247e847ca4d]))
  | 5 => (OfNat.ofNat (certificateWord [0x9e0f1e0782f0785e,0x0f79fe7bdefff7fc,0x62311c4647224e26,0x4e522497fff81092]))
  | 6 => 0x0
  | 7 => (OfNat.ofNat (certificateWord [0x1ff01fe7fcff7f9f,0xff81e07c1f0f0787,0x83c1e078783c7038,0x7063fffc92942520]))
  | _ => 0
def g5Neg : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0xe0000007ff007fe0,0x0000000000000000,0x0001ff807fc07fc0,0x7f8038e0000039db]))
  | 1 => (OfNat.ofNat (certificateWord [0x7ffff8000,0x0000007fe00ff800,0x0001ffff80007fff,0x80003f001ce03e1c]))
  | 2 => 0x0
  | 3 => (OfNat.ofNat (certificateWord [0xffe007ffff00007,0xfc01ffffffff8000,0x000000071f073fe0]))
  | 4 => (OfNat.ofNat (certificateWord [0x1ff800000000,0x0fffff8000000007,0xfffe000000000000,0x0003c007e007c000]))
  | 5 => (OfNat.ofNat (certificateWord [0xffffffffffffff8,0x0000000000000000,0x00000007fff80000]))
  | 6 => 0x0
  | 7 => (OfNat.ofNat (certificateWord [0x1fffffffffff,0xf000000000000000,0x0000000000000000,0x0003fff800000000]))
  | _ => 0
def g5Atlas : Atlas := ⟨6,rawDecor 187 g5Pos g5Neg, (OfNat.ofNat (certificateWord [0xffffffffffeeff00,0xffffffffffeeff00,0xeeeeaaaaeeee0000,0xeeeeaaaaeeee0000,0xffffffffffeeff00,0xffffffffffeeff00,0xeeeeaaaaeeee0000,0xeeeeaaaaeeee0000])), g5N, g5R, (fun _ _ => 0), g5I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g6K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def g6N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def g6R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt g6K3 (i*3) 3
  | _ => 0
def g6I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt g6K3 (4+((h/1+packedAt g6K3 (3+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g6Pos : Nat → Bits
  | 0 => 0x0
  | 1 => 0x0
  | 2 => (OfNat.ofNat (certificateWord [0xded7ded7ded7ded7,0xded7ded7ded7ded7,0xded7ded7ded7ded7,0xded7ded7ded7ded7]))
  | 3 => 0x0
  | 4 => 0x0
  | 5 => (OfNat.ofNat (certificateWord [0xbf6dbf6dbf6dbf6d,0xbf6dbf6dbf6dbf6d,0xbf6dbf6dbf6dbf6d,0xbf6dbf6dbf6dbf6d]))
  | 6 => 0x0
  | 7 => (OfNat.ofNat (certificateWord [0x7fba7fba7fba7fba,0x7fba7fba7fba7fba,0x7fba7fba7fba7fba,0x7fba7fba7fba7fba]))
  | _ => 0
def g6Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x0
  | 2 => (OfNat.ofNat (certificateWord [0x2203220322032203,0x2203220322032203,0x2203220322032203,0x2203220322032203]))
  | 3 => 0x0
  | 4 => 0x0
  | 5 => (OfNat.ofNat (certificateWord [0x440c440c440c440c,0x440c440c440c440c,0x440c440c440c440c,0x440c440c440c440c]))
  | 6 => 0x0
  | 7 => (OfNat.ofNat (certificateWord [0x8830883088308830,0x8830883088308830,0x8830883088308830,0x8830883088308830]))
  | _ => 0
def g6Atlas : Atlas := ⟨3,rawDecor 164 g6Pos g6Neg, (OfNat.ofNat (certificateWord [0xfffffffff0f0f0f0,0xfffffffff0f0f0f0,0xf0f0f0f000000000,0xf0f0f0f000000000,0xfffffffff0f0f0f0,0xfffffffff0f0f0f0,0xf0f0f0f000000000,0xf0f0f0f000000000])), g6N, g6R, (fun _ _ => 0), g6I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g7K6 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def g7K5 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x44a8007b80,0x000000018400002b,0x3b1a5181040cfa88,0x7b487da41dd53dea,0xa6f50fd8a5bc40f7,0x907dc43de43ef52d,0xfa1ef9037ca9de53]))
  | _ => 0
def g7K4 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x11a,0x002808ba58052b95,0x8452a74d8408f558,0x40d354c52ec44040]))
  | _ => 0
def g7K3 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x810c0d226c88,0x0818c5591010324b,0x02a6296456154c52]))
  | _ => 0
def g7N (k : Nat) : Nat :=
  match k with
  | 3 => 4
  | 4 => 6
  | 5 => 16
  | 6 => 1
  | _ => 0
def g7R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt g7K3 (i*39) 39
  | 4 => packedAt g7K4 (i*28) 28
  | 5 => packedAt g7K5 (i*17) 17
  | 6 => packedAt g7K6 (i*6) 6
  | _ => 0
def g7I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt g7K3 (158+((h/2+packedAt g7K3 (156+(h % 2)*1) 1) % 7)*3) 3
  | 4 => packedAt g7K4 (170+((h/2+packedAt g7K4 (168+(h % 2)*1) 1) % 8)*4) 4
  | 5 => packedAt g7K5 (284+((h/6+packedAt g7K5 (272+(h % 6)*2) 2) % 31)*5) 5
  | 6 => packedAt g7K6 (7+((h/1+packedAt g7K6 (6+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g7Pos : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0xe7896ed929665949,0x6969751627271726,0x95efb2377e37be8a,0xffcd249294cbcee7]))
  | 1 => (OfNat.ofNat (certificateWord [0x6bd2b36a52a8aa92,0xb192ab7b4afea94b,0x2af6def9144bdb7f,0x895249257395f0f8]))
  | 2 => 0x0
  | 3 => (OfNat.ofNat (certificateWord [0xb5a4c5b484d13424,0xdf3cc3b5fe4a42fe,0x437b6f77b5fc8a11,0x12a0924e7c39ff00]))
  | 4 => (OfNat.ofNat (certificateWord [0xc6c719f8ff01f8c7,0x1bdfee198c8c8cef,0xffa2745a268d13a5,0xa4c3e38fa13e5229]))
  | 5 => (OfNat.ofNat (certificateWord [0x7381e3f1fe3c038,0x1de7f3deefef7f8c,0x0c43886439121c46,0x4704fc0fffc08442]))
  | 6 => (OfNat.ofNat (certificateWord [0xf83fe03fe7fdff3f,0xfe0703e0f0f070f0,0x707c0f87c1e3e078,0x7838fff84a212994]))
  | 7 => 0x0
  | _ => 0
def g7Neg : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0xffc0000000000000,0x0000000000000000,0x007ff007fe03ff80,0x7fc000000001cee7]))
  | 1 => (OfNat.ofNat (certificateWord [0x3ff00ff8000,0x007ffff80003ffff,0x800000007381f0f8]))
  | 2 => 0x0
  | 3 => (OfNat.ofNat (certificateWord [0x1ff803ffff0000ff,0x807ffffffffc0000,0x0000000e7c39ff00]))
  | 4 => (OfNat.ofNat (certificateWord [0x3ff801ffc0,0x1ffffc00000000ff,0xff80000000000000,0x0000e38f803e0000]))
  | 5 => (OfNat.ofNat (certificateWord [0x3ffffe0000,0x1fffffffffffff00,0x0000000000000000,0x0000fc0fffc00000]))
  | 6 => (OfNat.ofNat (certificateWord [0x3fffffffff,0xe000000000000000,0x0000000000000000,0x0000fff000000000]))
  | 7 => 0x0
  | _ => 0
def g7Atlas : Atlas := ⟨6,rawDecor 123 g7Pos g7Neg, (OfNat.ofNat (certificateWord [0xffeeffeeffeeffee,0xeeeeaaaaeeee0000,0xffeeffeeffeeffee,0xeeeeaaaaeeee0000,0xffeeffeeffeeffee,0xeeeeaaaaeeee0000,0xffeeffeeffeeffee,0xeeeeaaaaeeee0000])), g7N, g7R, (fun _ _ => 0), g7I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g8K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def g8N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def g8R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt g8K3 (i*4) 4
  | _ => 0
def g8I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt g8K3 (5+((h/1+packedAt g8K3 (4+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g8Pos : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0xf7faf9edd76fb57b,0xf7faf9edd76fb57b,0xf7faf9edd76fb57b,0xf7faf9edd76fb57b]))
  | 1 => 0x0
  | 2 => 0x0
  | 3 => (OfNat.ofNat (certificateWord [0xaf9d4ef2eb9dcadc,0xaf9d4ef2eb9dcadc,0xaf9d4ef2eb9dcadc,0xaf9d4ef2eb9dcadc]))
  | 4 => (OfNat.ofNat (certificateWord [0x9de9db675f369ce9,0x9de9db675f369ce9,0x9de9db675f369ce9,0x9de9db675f369ce9]))
  | 5 => 0x0
  | 6 => (OfNat.ofNat (certificateWord [0x7ebfefbbeddb6f96,0x7ebfefbbeddb6f96,0x7ebfefbbeddb6f96,0x7ebfefbbeddb6f96]))
  | 7 => 0x0
  | _ => 0
def g8Neg : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0x8018c0001e3801b,0x08018c0001e3801b,0x08018c0001e3801b,0x08018c0001e3801b]))
  | 1 => 0x0
  | 2 => 0x0
  | 3 => (OfNat.ofNat (certificateWord [0x5031f00071fc00dc,0x5031f00071fc00dc,0x5031f00071fc00dc,0x5031f00071fc00dc]))
  | 4 => (OfNat.ofNat (certificateWord [0x633e003c7e000ce0,0x633e003c7e000ce0,0x633e003c7e000ce0,0x633e003c7e000ce0]))
  | 5 => 0x0
  | 6 => (OfNat.ofNat (certificateWord [0x83c0003f80000f00,0x83c0003f80000f00,0x83c0003f80000f00,0x83c0003f80000f00]))
  | 7 => 0x0
  | _ => 0
def g8Atlas : Atlas := ⟨3,rawDecor 89 g8Pos g8Neg, (OfNat.ofNat (certificateWord [0xffaaffaaffaaffaa,0xaaaa0000aaaa0000,0xffaaffaaffaaffaa,0xaaaa0000aaaa0000,0xffaaffaaffaaffaa,0xaaaa0000aaaa0000,0xffaaffaaffaaffaa,0xaaaa0000aaaa0000])), g8N, g8R, (fun _ _ => 0), g8I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g9K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def g9N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def g9R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt g9K3 (i*4) 4
  | _ => 0
def g9I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt g9K3 (5+((h/1+packedAt g9K3 (4+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g9Pos : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0xf7eef9f737afd5bb,0xf7eef9f737afd5bb,0xf7eef9f737afd5bb,0xf7eef9f737afd5bb]))
  | 1 => (OfNat.ofNat (certificateWord [0x6f754eeadb5dab5c,0x6f754eeadb5dab5c,0x6f754eeadb5dab5c,0x6f754eeadb5dab5c]))
  | 2 => 0x0
  | 3 => 0x0
  | 4 => (OfNat.ofNat (certificateWord [0xddfddf6eef76be6d,0xddfddf6eef76be6d,0xddfddf6eef76be6d,0xddfddf6eef76be6d]))
  | 5 => (OfNat.ofNat (certificateWord [0x3ea7ebb37d9b4f92,0x3ea7ebb37d9b4f92,0x3ea7ebb37d9b4f92,0x3ea7ebb37d9b4f92]))
  | 6 => 0x0
  | 7 => 0x0
  | _ => 0
def g9Neg : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0x8018c0001e3801b,0x08018c0001e3801b,0x08018c0001e3801b,0x08018c0001e3801b]))
  | 1 => (OfNat.ofNat (certificateWord [0x90c1f00381fc031c,0x90c1f00381fc031c,0x90c1f00381fc031c,0x90c1f00381fc031c]))
  | 2 => 0x0
  | 3 => 0x0
  | 4 => (OfNat.ofNat (certificateWord [0x2306003c0e000c60,0x2306003c0e000c60,0x2306003c0e000c60,0x2306003c0e000c60]))
  | 5 => (OfNat.ofNat (certificateWord [0xc3f8003ff0000f80,0xc3f8003ff0000f80,0xc3f8003ff0000f80,0xc3f8003ff0000f80]))
  | 6 => 0x0
  | 7 => 0x0
  | _ => 0
def g9Atlas : Atlas := ⟨3,rawDecor 51 g9Pos g9Neg, (OfNat.ofNat (certificateWord [0xeeeeaaaaeeee0000,0xeeeeaaaaeeee0000,0xeeeeaaaaeeee0000,0xeeeeaaaaeeee0000,0xeeeeaaaaeeee0000,0xeeeeaaaaeeee0000,0xeeeeaaaaeeee0000,0xeeeeaaaaeeee0000])), g9N, g9R, (fun _ _ => 0), g9I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g10K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def g10K5 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x1b0400e200e8800,0x000013944ca8c094,0x2340004a00d05000,0x0a80000118014000,0x001e000110000008,0x001802900ac00400,0x640000000000024c,0x0283e40000000cb8,0x01c00000480000c2,0xc2ce800000f12001,0x6000000740008016,0xf940fd43fd42fd41,0xfd40fd32fd31fd30,0xfc43fd21fd20fc42,0xfc32fd10fc41fc31,0xfc21fc40f830fc30,0xfc20fc10ff40fb30,0xff30ff20ff10ff41,0xff31ff21fe10ff42,0xff32fe21fe20ff43,0xfe32fe31fe30fe43,0xfe42fe41fa40fe40]))
  | _ => 0
def g10K4 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x8a3a7c0,0xea2000a204614809,0x6340400701a56b00,0x022549e00681c3c7,0x298001600004e260,0x0620090449c88945,0x0002e000000121e0,0x00000925ca600843,0x6286a76660060003,0x08c00000010b42c0,0x05a240000782a007,0x4000006ae484a186,0x4ac008682aa00003,0x2003ea48e006c7a0,0x29aa00c005842527,0xe004c5e38086ea8b,0x240b8420880ef202,0xa0519ee290e31844,0x000c001847b94050,0xe728a185e51640bc,0xa28617945cc2f2a0,0x21f614d40ac29a81,0x7853502f66b205e5,0x4042bca808379500,0x86f20ba0de41742b,0xc82e8779058caf20,0xb18dd54443baa888,0x575150c2ea2b995b,0x54843b6928836d25,0x0c2da4b98d74d442,0xae9a8835d35086ba,0x6b90574d7109ea28,0x433d450c2b8a6a05,0xb14941ba28a856f2,0x5cc6ee2b99794842,0x1af9ae215f35c82f,0x0a0a1de14132bc28,0x2637b058c6f60b19,0x5ec1743f88a861e9,0x250c3b26418764c4,0x30dca28617b058c3,0xb086185ec1742bd8,0x2e833f450c3768a1,0x85ed4143bda82657,0xb504c6f66a18760c,0x330b792861eb250c,0x2ee2a187cc54309f,0xa28435f35086eea2,0xa157cd441ec18663,0x6f25106f4a010de9,0x4041b7a92835f351,0x0bb061995d94442b,0xd28085db53502bea,0x6a06e50343ec1868,0x76e5210eeca221de,0x94043dca04817b05,0x102f06b205e81643]))
  | _ => 0
def g10K3 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x2,0x800a0000300001a4,0xb0001e0000000120,0x1400000000070000,0x088000e12a580680,0xb8c2100009820006,0x0000080000000034,0x003516114d40d845,0x5250c3311551430d,0x2588535032925514,0x30c6515320c31945,0x4c4308e518359031,0x94614d4096cda059,0x0e583641741960d9,0x05d0b254548421b4,0x584430c351150c33,0x2b2588430c349250,0xc331ca517250c331,0x45c5430a651830cc,0x699460c332a65183,0x0d0e986350343d29,0x8853503526114d40]))
  | _ => 0
def g10K2 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x10840,0xc07905856214d40c,0x22c2a30a6a061115,0x51830ccb04b128c2,0x9a8182495460c331]))
  | _ => 0
def g10N (k : Nat) : Nat :=
  match k with
  | 2 => 5
  | 3 => 25
  | 4 => 91
  | 5 => 44
  | 6 => 1
  | _ => 0
def g10R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g10K2 (i*49) 49
  | 3 => packedAt g10K3 (i*38) 38
  | 4 => packedAt g10K4 (i*27) 27
  | 5 => packedAt g10K5 (i*16) 16
  | 6 => packedAt g10K6 (i*5) 5
  | _ => 0
def g10I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g10K2 (249+((h/2+packedAt g10K2 (245+(h % 2)*2) 2) % 7)*4) 4
  | 3 => packedAt g10K3 (986+((h/9+packedAt g10K3 (950+(h % 9)*4) 4) % 60)*6) 6
  | 4 => packedAt g10K4 (2612+((h/31+packedAt g10K4 (2457+(h % 31)*5) 5) % 125)*8) 8
  | 5 => packedAt g10K5 (779+((h/15+packedAt g10K5 (704+(h % 15)*5) 5) % 89)*7) 7
  | 6 => packedAt g10K6 (6+((h/1+packedAt g10K6 (5+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g10Pos : Nat → Bits
  | 0 => 0x0
  | 1 => (OfNat.ofNat (certificateWord [0xe0979cbd557dae97,0x4bc1f1deaf5d9555,0x7555e916fa4b4c98,0xbd8bd8bfc5c12f39]))
  | 2 => (OfNat.ofNat (certificateWord [0x2570bf773fbeb7bb,0x885ef6edd736bcf9,0xdab52bab6a958bb5,0x5555f7f2ca4ae17e]))
  | 3 => 0x0
  | 4 => 0x0
  | 5 => (OfNat.ofNat (certificateWord [0x4ba3e56cffd5fb10,0xddef7b759baf5ead,0x53e74dcdb326db16,0x6f7f5555529747ca]))
  | 6 => (OfNat.ofNat (certificateWord [0x93fd08e3fde921dd,0xeef7bdbae5cb973e,0x7cf9f171dc78eddb,0xf9a69a69a527fa11]))
  | 7 => (OfNat.ofNat (certificateWord [0xfe4a521ff90ffdfe,0xff7bde3cf9f3e7cf,0x9f3e7e7e1fbff1e3,0x8e38e38e39fc94a4]))
  | _ => 0
def g10Neg : Nat → Bits
  | 0 => 0x0
  | 1 => (OfNat.ofNat (certificateWord [0xe0039cc2ae0001e0,0xf07c1fc0000007f0,0x1fc07f801fc00000,0x0fc0fc0fc1c00739]))
  | 2 => (OfNat.ofNat (certificateWord [0x701f08c001c000,0xff80000001fc0000,0x1fff8000000001fc,0x0000fff00000e03e]))
  | 3 => 0x0
  | 4 => 0x0
  | 5 => (OfNat.ofNat (certificateWord [0x383e013000e01ff,0x00000000fe0007ff,0xe00000000000fe00,0x0fff0000000707c0]))
  | 6 => (OfNat.ofNat (certificateWord [0x3fc001c000ffe00,0x00000000fffff800,0x000000000000ffff,0xf00000000007f800]))
  | 7 => (OfNat.ofNat (certificateWord [0xfc0000600ff00000,0x00001fff00000000,0x000000001fff0000,0x0000000001f80000]))
  | _ => 0
def g10Atlas : Atlas := ⟨6,rawDecor 230 g10Pos g10Neg, (OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffff0f0f0f0,0xfcfcfcfccccccccc,0xf0f0f0f000000000,0xffffffffffffffff,0xfffffffff0f0f0f0,0xfcfcfcfccccccccc,0xf0f0f0f000000000])), g10N, g10R, (fun _ _ => 0), g10I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g11K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def g11K5 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x1852000200447c5,0x001e640005298000,0x0c800240004d2738,0x5d28016000210000,0x0090000a8d040150,0x02c00008284c9002,0x26d180000061d560,0x00071c014000000f,0x0030000000000025,0x80002c000000000a,0xed32fd43fd42fd41,0xfd40fd32fd31fd30,0xfc43fd21fd20fc42,0xfc32fd10fc41fc31,0xfc21fc40fc30ec20,0xfc20fc10ff40ff30,0xff20ff10ff41ff31,0xff21fe10ff42ff32,0xfe21ee20fe20ff43,0xee32fe32fe31fe30,0xfe43fe42fe41fe40]))
  | _ => 0
def g11K4 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0xb3a432331375,0x414254404320a3b0,0xf4a3e10003800083,0x6393d204724591a1,0x62f425501483c572,0x95100061f194f2d5,0x82a2e264d501d000,0x0410e00000028450,0x0004600000952000,0x2002b1b18334e003,0x5052c5a4c3403562,0x211075312170d004,0x94b000015303f401,0xe211c13270c0a42a,0x6bf39258630e0880,0x8628400800280005,0xe3802a000b795010,0xef2a020de54031bc,0x82e857905886eaa2,0x21dd45430ba8a841,0x75159039a6498534,0xd420b69ac656d521,0x0eda6a105b4d620b,0x6928836d250c6da4,0xa185b49740b692e6,0x16d25c42da4b98db,0x49643ae9a8835d35,0x0827a8a18cf51430,0x9ea28413d4584278,0x8a98db14940b792c,0x876c524c2d84a884,0xfd1610ba28a87771,0x59036a8220dbc973,0x1b792e2168504cbd,0x0a0995e14132b628,0x2656f058caf60b10,0xdbc9730b792e817b,0x05d0bd280107a440,0x20f28a841cd35083,0x5a8a105bc1620f41,0x80413f450835e8a1,0x057cd420e79a8413,0xf450c3d6a0995ed4,0x132e699661e820cc,0x2de4a185dc5420f3,0x8a84177150c27e8a,0x18ddd4543af9a883,0x6f250c6de4a20de9,0x4031bd28083e8208,0x42dea4a05bd4930b,0x712a216f05083d04,0x1105b94843e69946,0x56f250caeca221de,0x94043b612c616e25,0x8c27c8a98fa08240]))
  | _ => 0
def g11K3 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0xc20000a80000,0x99c28000002261e0,0x0600c69402c00000,0x0090016000000a00,0x9040000000000000,0x0020eb8048000004,0x203493550020d24d,0x510083153550441d,0x1455350832515514,0x20c34d5450824d36,0x09630d8458504cb4,0x93614132ca518504,0xca6b06896309a181,0x25cc6686049643b8,0x4583008361150824,0x0aa5183008329450,0x8210c34d7450832b,0x4614132b24d820cc,0x2c8604cb30d14d71,0x5083631614132b24,0xd820842c93608240]))
  | _ => 0
def g11K2 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0xc84,0x111904593614132c,0x422ca30a09964115,0x4d820903049b28c2,0x8265825153608210]))
  | _ => 0
def g11N (k : Nat) : Nat :=
  match k with
  | 2 => 5
  | 3 => 25
  | 4 => 91
  | 5 => 44
  | 6 => 1
  | _ => 0
def g11R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g11K2 (i*49) 49
  | 3 => packedAt g11K3 (i*38) 38
  | 4 => packedAt g11K4 (i*27) 27
  | 5 => packedAt g11K5 (i*16) 16
  | 6 => packedAt g11K6 (i*5) 5
  | _ => 0
def g11I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g11K2 (249+((h/2+packedAt g11K2 (245+(h % 2)*2) 2) % 7)*4) 4
  | 3 => packedAt g11K3 (968+((h/9+packedAt g11K3 (950+(h % 9)*2) 2) % 60)*6) 6
  | 4 => packedAt g11K4 (2643+((h/31+packedAt g11K4 (2457+(h % 31)*6) 6) % 109)*8) 8
  | 5 => packedAt g11K5 (809+((h/15+packedAt g11K5 (704+(h % 15)*7) 7) % 76)*7) 7
  | 6 => packedAt g11K6 (6+((h/1+packedAt g11K6 (5+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g11Pos : Nat → Bits
  | 0 => 0x0
  | 1 => (OfNat.ofNat (certificateWord [0x3c24f9df5d57d7db,0xabc1f6e3bbaedcf5,0x5aabf516eaeb2d59,0x6a97acbfc67849f3]))
  | 2 => 0x0
  | 3 => (OfNat.ofNat (certificateWord [0x454bbe7d3efbfb4d,0xc85efb6ddcd77559,0xed5b17ab732c5662,0xbf2bf3f2d88a977c]))
  | 4 => (OfNat.ofNat (certificateWord [0xe8e3c8b4f4dd5d88,0x6def71f6e99b9ead,0x49f3654dbac99b4c,0xdafea55543d1c791]))
  | 5 => 0x0
  | 6 => (OfNat.ofNat (certificateWord [0x92fd1373fffe90fe,0xfef7bdbb76e5d73e,0x7e7db9f1dc72e3f7,0xf34d3a69ad25fa26]))
  | 7 => (OfNat.ofNat (certificateWord [0xff92240ff890feef,0x7f7bde3c78f9e7cf,0x8f9e3e7e1f7cff87,0x1c71c38e31ff2448]))
  | _ => 0
def g11Neg : Nat → Bits
  | 0 => 0x0
  | 1 => (OfNat.ofNat (certificateWord [0x1c0039a0a0e00000,0x707c003f80000000,0x0fe03f80007f0000,0x0001fc0fc0380073]))
  | 2 => 0x0
  | 3 => (OfNat.ofNat (certificateWord [0x3be02c00000f0,0x7f800000000007f0,0x0fffc00000000000,0x1f81fff00000077c]))
  | 4 => (OfNat.ofNat (certificateWord [0xe0e3c04b0f00e0ff,0x80001fc000fe07ff,0xf00000001f8003f8,0x1ffe000001c1c780]))
  | 5 => 0x0
  | 6 => (OfNat.ofNat (certificateWord [0xfc000c0000ff00,0x0000000000fff800,0x00000000000003ff,0xe00000000001f800]))
  | 7 => (OfNat.ofNat (certificateWord [0xff0000700fff0000,0x00001fffff000000,0x000000001ffffc00,0x0000000001fe0000]))
  | _ => 0
def g11Atlas : Atlas := ⟨6,rawDecor 218 g11Pos g11Neg, (OfNat.ofNat (certificateWord [0xffffffffffffffff,0xffccff00ffccff00,0xffccffccffccffcc,0xcccc0000cccc0000,0xffffffffffffffff,0xffccff00ffccff00,0xffccffccffccffcc,0xcccc0000cccc0000])), g11N, g11R, (fun _ _ => 0), g11I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g12K7 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def g12K6 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x2380a,0x122c1a2688148a7e,0x000000000044248c,0x22360c4a52807a16,0x86007c005a000000,0x00322e0000000000,0x82003c0008001000,0x0028000000000070,0x4200465676205c2a,0x18006a68660e005e,0x046e30544c480062,0x064e007484000000,0x001c0000408e3a3e,0x721e60785064346c,0x0058000000280019,0x0000c10021000020,0x26000e80223003fc,0xa87d547ea43f510e,0xea1ff553faa7fd52,0xfea8ff543fa87fd4,0x2fea0ff503f8a9fd,0x32fe98ff4c3f8a7f,0xc43fe90ff483f8a5,0xfc42fe197f443f8a,0x3f441fe20ff0c7f8,0x43fc50fe207f0c3f,0x841fc10ffa87fd03,0xfe61ff20fb887fc4,0x3fea3f741ffa0ffc,0xc7fe43fe10ffa97f,0xd0bfe65f621ff10f,0xf883fea7ff43ff19,0x7f8c7fc61ff54ef2,0x1ff90ffc85fe41ff,0x207f953fca7fe52f,0xb28ff947f4a1fe50]))
  | _ => 0
def g12K5 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0xd1000c0c40130081,0x8e2a008110404a05,0x0000383003030304,0x0000400000873014,0x18008005850200c8,0x20000001fc58550f,0xc54151fc54121fc4,0x4150fc44140bc580,0x41f654143de54154,0xde54153be55a50be,0x58054be58053f618,0xd50be58052be5804,0x2de54052be58051b,0xe58041fc54041fc5,0x8041be41b51be41b,0x52be41b53be41a32,0xbe41a31be41b54f9,0x48542f948532b949,0x841b949a51f55454,0x3dd545549d55841b,0xd58552bd58550bd5,0x5a51bd55841bd55b,0x10bd55b41bd55a21,0xbd58454bd19151bd,0xd1a51bd58453bd58,0x520f548543bd49a2,0x1bd58452bd49841b,0xd58442bd11921bd5,0x8432bd49b10bd49b,0x41bdd1a21bd49a51,0xf948452f544143bd,0x45a10bd45850bd45,0x840bd58041bd1191,0x0bd45830bd45820b,0xd45b50bd45b20bd4,0x5b52bd45a20bd45b,0x53bd45a32bd45a30,0xbd45b54bd45a43bd,0x45a42bd45a40bd45,0xa52bd45a50bb5885,0x4bb58853bb49841b,0xb49831bb49840bb4,0x9830bb49a43bb49a,0x51bb49a50e750d54,0xe750d40b751a43b7,0x58c54b74d852b74d,0x842b74d841b74d84,0x0b74db40b74db20b,0x74db41b74db42b74,0xda54af51853af518,0x52af518309f55842,0x9f558419f558409f,0x558309f55a20b718,0xd50b7cda549fd5a2,0x0bb18954bbc9a50b,0xbc9a51bbc9a43b7c,0xdb42bd18554bdc5a,0x50bdc5a52f518543,0xbd18543bd18542bd,0x18540bdc5a40bdc5,0xa42bdc5a43bdc5b5,0x4f949841f550c41f,0x54d841dd55841bdc,0x5a41bdc5a30bdc5a,0x32b7cdb41bdc5b53,0xbdc5a20bdc5b52bd,0x41b41bdd1b10b7cd,0xb20bd41a21bd41a5,0x1f618143be18143b,0xec1b54bec1a31bec,0x1a32b7cdb40bec1b,0x53fc44030bec1b52,0xbdc5b20bdc5b50be,0xc1b519fd5830afd1,0x8309fd5840bdd815,0x1f6d8143bed8143e,0x750f40b7cd840fc4,0x4330bdd8121bbc98,0x30bbc9840bdc5820,0xbdc5830bdc5840bd,0xc5850fc54310fc44,0x310f550f10bdc581,0x0bd11b109fd5841d,0xdd5841bdd8554f5d,0x8543bdd8543bdd85,0x42bdd8540fc54341,0xf550f41f54db41bd,0xd1841ed10741f5cd,0xb41b7cd841f5cd84,0x1bbc9831bbc9841f,0x9c9841be98041fc9,0x8041be98051bd81b,0x419fd5842bbd8954,0xbdd8951f948752af,0xd1852b7cd842b7cd,0x852bd89910bd9843,0x2bd98442bd98452f,0xc54221f948621f55,0x0e21bdc5821bd11a,0x21be98042be98052,0xbd81a21bd85b42f6,0xd8d50b7d8d50de54,0x353afd1853bb9885,0x3f948632bd98453b,0xe98053de54354dd5,0x4754b798c54f6542,0x43f554643f548643,0xf544243f545a43f3,0x49a43e750e43b7cd,0x843f3c9a43f5c5a4,0x3f510643f5c4243f,0x5d0643f588643bb9,0x8854f948642bd984,0x54be98054fc44240,0xe750e54bd95921de,0x54252bd95910fc54,0x251f949a51f550e5,0x1dd54651bdc5851f,0x9c9a51f590e51bd1,0x1a51fc54650fc486,0x50fc44250fc45a50,0xfa49a50f650e50de,0x54250bec1850fac9,0xa50fcc5a50fc1065,0x0fcc4250fcd0650f,0xc88650f690e50fc9,0x4650fc98550bd81a,0x51bd85a54bd89a51]))
  | 1 => (OfNat.ofNat (certificateWord [0xc0210ac7a0e02d0,0x54631007880c7d16,0xa0590a81a1043942,0x01056491b8481041,0x10420699e7b19a00,0x0006700000000588,0x8265090000005001,0x00021a008d80014c,0x598921a1520c9e60,0x00ec1e0000000e72,0x182620de000002b9,0x28260a86c8002f00,0x076888000000d228,0x460e80f89a7c1a40,0x02226b82a3992c30,0x9b4778ca5e04a8b1,0x461c9705d9540000,0x6001aa7480055800,0x0b1ce088640010c4,0xc9367121e65a0e52,0x81c250000012a001,0x682fa04340266d8f,0xc6b0d42a80000000,0x47a00728525107a3,0x9020028000020a33,0x04c86080848465b9,0x308aa08320f66f93,0x84984e160f0790da,0x04800000006f2025,0xf82e4f8fa1b17468,0x9ea5401e4e85e489,0xee25992850b07c85,0xa2995e741f84417a,0x5921645866538000,0xc1a8001d83f9cc21,0x9c070824280e2420,0x380021c1891c2e1f,0x61d8ea338b269a0c,0x891140018e759600,0x60281707c1d12e23,0x9b0560a2000f8000,0xc43d0ba1a98a1c16,0xc4d106571dc10172,0x358a47f83a719900,0x022e141021f8d200,0x1d40000023226601,0x480d89c0015a0000,0x005008002204686e,0x3c9fa22800000c64,0xf000120003b80061,0x1ba001123709e181,0x7c661a00f1e07f0b,0x66181014a1c9a118,0x5818954040860048,0x1063a340002e1108,0x33e3c482121408e1,0x4041082c0c7610a2]))
  | _ => 0
def g12K4 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x172154550c321c3,0x6142f250048043f4,0x60053000000453b0,0x207301d2b004f310,0x00b000a092358004,0xb43001120291b0f5,0x019003a4d1841382,0xd34561e40062a330,0xd1f35083d57004e4,0xa52394c245101050,0x042002227122c1a0,0xe4726153c2e103e2,0x8134403160049375,0xc0084000ac016d80,0xc840415028240083,0x8000038ac8fbee15,0x049841dc24ca84a3,0x7849e6154338b82a,0xc20e715055841ae2,0xaf30aa19c55950d0,0x738ab2a110cf1705,0x58419e2e0322a3b4,0x5846354278b808c9,0x0f615048452f2220,0xa1a81ac519100c33,0x8ab220186d11018d,0x509e2e030aa93c5c,0x31690f70b024c20e,0xd16050c41da2c09b,0x0839c5815610678b,0x3cc020f195050d54,0xb328e31aa15655c6,0x050e6c3b2a0a1e59,0x504d852c72a0a30a,0x51e55c6050e3cabe,0x0d196695018954cd,0x2ad934a13c5d8419,0x42788388d10cf107,0x11a519cae4322a33,0x949c464436290a6c,0x296a52151852b8a4,0xe30a873949c6150e,0x7293e2daa6c52650,0xc41d8a4c9b083994,0x9956106729388d10,0xce527c5b539ca4e2,0x36213949e5644362,0x9328728ce52789a5,0x19ca4e234a33949e,0x069478aa8a86aa65,0x55650c41caa6cab0,0x831d55c464863aab,0x88c884755711a518,0xeaae236211d55c46,0x8874aa188c90cd57,0x61064393a8e31aa1,0x9c5835610732936a,0xc20cd576d0643da2,0xc19b083b149b3610,0x72aab66c20ee160c,0x9841ccaad93083b8,0x49a6010738ab4c02,0x0ce77255b41ba2e1,0x8b487745c04190ee,0x29388321ec52690e,0x51aaaae20c879c54,0x25648738a84ac884,0xf25758041bc24e20,0xca17849e51942b8a,0xb883286727055841]))
  | _ => 0
def g12K3 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x12000a8,0x00018e4150485361,0x4b885412151852c9,0x16151c63543245c1,0x4311921c911051c6,0x35430555d4311921]))
  | _ => 0
def g12N (k : Nat) : Nat :=
  match k with
  | 3 => 6
  | 4 => 89
  | 5 => 280
  | 6 => 72
  | 7 => 1
  | _ => 0
def g12R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt g12K3 (i*50) 50
  | 4 => packedAt g12K4 (i*39) 39
  | 5 => packedAt g12K5 (i*28) 28
  | 6 => packedAt g12K6 (i*17) 17
  | 7 => packedAt g12K7 (i*6) 6
  | _ => 0
def g12I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt g12K3 (302+((h/2+packedAt g12K3 (300+(h % 2)*1) 1) % 11)*4) 4
  | 4 => packedAt g12K4 (3651+((h/30+packedAt g12K4 (3471+(h % 30)*6) 6) % 106)*8) 8
  | 5 => packedAt g12K5 (8498+((h/94+packedAt g12K5 (7840+(h % 94)*7) 7) % 334)*10) 10
  | 6 => packedAt g12K6 (1368+((h/24+packedAt g12K6 (1224+(h % 24)*6) 6) % 112)*8) 8
  | 7 => packedAt g12K7 (7+((h/1+packedAt g12K7 (6+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g12Pos : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0x37ed72252fdae4a7,0x6b1291989688c8b2,0x589f6f24f6e27f70,0x7fe0f8e04492f39b]))
  | 1 => (OfNat.ofNat (certificateWord [0x7225364a55ed7da9,0x282522a12bbb512e,0xf127b5ed92449faf,0xe0a13f008b8e7c1c]))
  | 2 => 0x0
  | 3 => (OfNat.ofNat (certificateWord [0xda49da939a498932,0x4c49c3424dddbbe4,0x924bfafeff5fe522,0x8546092513f07fe0]))
  | 4 => 0x0
  | 5 => (OfNat.ofNat (certificateWord [0x638e631ce38e31c4,0x718e778c71eefdbf,0xdffd2348a4692a35,0x2a68524bc3ff9089]))
  | 6 => (OfNat.ofNat (certificateWord [0x7cf07de0fcf05e0f,0x82f07bf7ff0f21c8,0xe4723c8f4791d3c9,0xd393a493fd242536]))
  | 7 => (OfNat.ofNat (certificateWord [0x80ff81ff00ff9ff7,0xfcfffc0781f03e0f,0x0783c0f0781e1c0e,0x1c1c3ffe22494a40]))
  | _ => 0
def g12Neg : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0xfffe0000ffe007,0xff00000000000000,0x0003ff007fe01ff0,0x1fe038e00000739b]))
  | 1 => (OfNat.ofNat (certificateWord [0xff00000000fffff8,0x0000000001ffc00f,0xf803ffff80001fff,0xe0003f00038e7c1c]))
  | 2 => 0x0
  | 3 => (OfNat.ofNat (certificateWord [0x1fffff0,0x0003ffffffffe000,0x0000000003f07fe0]))
  | 4 => 0x0
  | 5 => (OfNat.ofNat (certificateWord [0x7ff801ffffff,0xfffc000000000000,0x00000003c3ff8000]))
  | 6 => (OfNat.ofNat (certificateWord [0x7ffffe000000,0x0000000000000000,0x00000003fc000000]))
  | 7 => (OfNat.ofNat (certificateWord [0xffffff,0xffff800000000000,0x0000000000000000,0x00003ffc00000000]))
  | _ => 0
def g12Atlas : Atlas := ⟨7,rawDecor 235 g12Pos g12Neg, (OfNat.ofNat (certificateWord [0xffffffffffffffff,0xffffffffff00ff00,0xffeeffeeffeeffee,0xaaaaaaaa00000000,0xffffffffffffffff,0xffffffffff00ff00,0xffeeffeeffeeffee,0xaaaaaaaa00000000])), g12N, g12R, (fun _ _ => 0), g12I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g13K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def g13N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def g13R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt g13K3 (i*3) 3
  | _ => 0
def g13I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt g13K3 (4+((h/1+packedAt g13K3 (3+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g13Pos : Nat → Bits
  | 0 => 0x0
  | 1 => 0x0
  | 2 => 0x0
  | 3 => (OfNat.ofNat (certificateWord [0xded7ded7ded7ded7,0xded7ded7ded7ded7,0xded7ded7ded7ded7,0xded7ded7ded7ded7]))
  | 4 => 0x0
  | 5 => 0x0
  | 6 => (OfNat.ofNat (certificateWord [0xbf6dbf6dbf6dbf6d,0xbf6dbf6dbf6dbf6d,0xbf6dbf6dbf6dbf6d,0xbf6dbf6dbf6dbf6d]))
  | 7 => (OfNat.ofNat (certificateWord [0x7fba7fba7fba7fba,0x7fba7fba7fba7fba,0x7fba7fba7fba7fba,0x7fba7fba7fba7fba]))
  | _ => 0
def g13Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x0
  | 2 => 0x0
  | 3 => (OfNat.ofNat (certificateWord [0x2203220322032203,0x2203220322032203,0x2203220322032203,0x2203220322032203]))
  | 4 => 0x0
  | 5 => 0x0
  | 6 => (OfNat.ofNat (certificateWord [0x440c440c440c440c,0x440c440c440c440c,0x440c440c440c440c,0x440c440c440c440c]))
  | 7 => (OfNat.ofNat (certificateWord [0x8830883088308830,0x8830883088308830,0x8830883088308830,0x8830883088308830]))
  | _ => 0
def g13Atlas : Atlas := ⟨3,rawDecor 200 g13Pos g13Neg, (OfNat.ofNat (certificateWord [0xffffffffffffffff,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0x0000000000000000,0xffffffffffffffff,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0x0000000000000000])), g13N, g13R, (fun _ _ => 0), g13I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g14K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def g14N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def g14R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt g14K3 (i*4) 4
  | _ => 0
def g14I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt g14K3 (5+((h/1+packedAt g14K3 (4+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g14Pos : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0xd5f9b1e5cbaf9c5d,0xd5f9b1e5cbaf9c5d,0xd5f9b1e5cbaf9c5d,0xd5f9b1e5cbaf9c5d]))
  | 1 => 0x0
  | 2 => 0x0
  | 3 => (OfNat.ofNat (certificateWord [0xcf9e96ead5dda5ce,0xcf9e96ead5dda5ce,0xcf9e96ead5dda5ce,0xcf9e96ead5dda5ce]))
  | 4 => 0x0
  | 5 => (OfNat.ofNat (certificateWord [0xbfebfb776fb6daf5,0xbfebfb776fb6daf5,0xbfebfb776fb6daf5,0xbfebfb776fb6daf5]))
  | 6 => 0x0
  | 7 => (OfNat.ofNat (certificateWord [0x7ebfdfbbf6db6faa,0x7ebfdfbbf6db6faa,0x7ebfdfbbf6db6faa,0x7ebfdfbbf6db6faa]))
  | _ => 0
def g14Neg : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0x2b031c3c00e38c0d,0x2b031c3c00e38c0d,0x2b031c3c00e38c0d,0x2b031c3c00e38c0d]))
  | 1 => 0x0
  | 2 => 0x0
  | 3 => (OfNat.ofNat (certificateWord [0x3033e00078fc00ce,0x3033e00078fc00ce,0x3033e00078fc00ce,0x3033e00078fc00ce]))
  | 4 => 0x0
  | 5 => (OfNat.ofNat (certificateWord [0x403c00007f0000f0,0x403c00007f0000f0,0x403c00007f0000f0,0x403c00007f0000f0]))
  | 6 => 0x0
  | 7 => (OfNat.ofNat (certificateWord [0x83c0003f80000f00,0x83c0003f80000f00,0x83c0003f80000f00,0x83c0003f80000f00]))
  | _ => 0
def g14Atlas : Atlas := ⟨3,rawDecor 169 g14Pos g14Neg, (OfNat.ofNat (certificateWord [0xffffffffff00ff00,0xffffffffff00ff00,0xaaaaaaaa00000000,0xaaaaaaaa00000000,0xffffffffff00ff00,0xffffffffff00ff00,0xaaaaaaaa00000000,0xaaaaaaaa00000000])), g14N, g14R, (fun _ _ => 0), g14I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g15K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def g15N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def g15R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt g15K3 (i*4) 4
  | _ => 0
def g15I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt g15K3 (5+((h/1+packedAt g15K3 (4+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g15Pos : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0xf7faf9edd76fb57b,0xf7faf9edd76fb57b,0xf7faf9edd76fb57b,0xf7faf9edd76fb57b]))
  | 1 => (OfNat.ofNat (certificateWord [0xaf9d4ef2eb9dcadc,0xaf9d4ef2eb9dcadc,0xaf9d4ef2eb9dcadc,0xaf9d4ef2eb9dcadc]))
  | 2 => 0x0
  | 3 => 0x0
  | 4 => 0x0
  | 5 => (OfNat.ofNat (certificateWord [0x9de9db675f369ce9,0x9de9db675f369ce9,0x9de9db675f369ce9,0x9de9db675f369ce9]))
  | 6 => (OfNat.ofNat (certificateWord [0x7ebfefbbeddb6f96,0x7ebfefbbeddb6f96,0x7ebfefbbeddb6f96,0x7ebfefbbeddb6f96]))
  | 7 => 0x0
  | _ => 0
def g15Neg : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0x8018c0001e3801b,0x08018c0001e3801b,0x08018c0001e3801b,0x08018c0001e3801b]))
  | 1 => (OfNat.ofNat (certificateWord [0x5031f00071fc00dc,0x5031f00071fc00dc,0x5031f00071fc00dc,0x5031f00071fc00dc]))
  | 2 => 0x0
  | 3 => 0x0
  | 4 => 0x0
  | 5 => (OfNat.ofNat (certificateWord [0x633e003c7e000ce0,0x633e003c7e000ce0,0x633e003c7e000ce0,0x633e003c7e000ce0]))
  | 6 => (OfNat.ofNat (certificateWord [0x83c0003f80000f00,0x83c0003f80000f00,0x83c0003f80000f00,0x83c0003f80000f00]))
  | 7 => 0x0
  | _ => 0
def g15Atlas : Atlas := ⟨3,rawDecor 99 g15Pos g15Neg, (OfNat.ofNat (certificateWord [0xeeeeeeeeeeeeeeee,0xaaaaaaaa00000000,0xeeeeeeeeeeeeeeee,0xaaaaaaaa00000000,0xeeeeeeeeeeeeeeee,0xaaaaaaaa00000000,0xeeeeeeeeeeeeeeee,0xaaaaaaaa00000000])), g15N, g15R, (fun _ _ => 0), g15I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g16K6 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def g16K5 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0xd,0x59cc0028a0000000,0x000c020011800022,0x4441fea21ed20eea,0x9f750fd8a5f441ee,0x187bc83ee21f741f,0x7a9778c3bc87de53]))
  | _ => 0
def g16K4 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0xc140,0x185d0845bc58041b,0xa58052ad119109b1,0x5920a75183097558,0x30d354c52e550c41]))
  | _ => 0
def g16K3 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x80348b,0x028620e496054c52]))
  | _ => 0
def g16N (k : Nat) : Nat :=
  match k with
  | 3 => 2
  | 4 => 8
  | 5 => 14
  | 6 => 1
  | _ => 0
def g16R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt g16K3 (i*39) 39
  | 4 => packedAt g16K4 (i*28) 28
  | 5 => packedAt g16K5 (i*17) 17
  | 6 => packedAt g16K6 (i*6) 6
  | _ => 0
def g16I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt g16K3 (80+((h/2+packedAt g16K3 (78+(h % 2)*1) 1) % 4)*2) 2
  | 4 => packedAt g16K4 (233+((h/3+packedAt g16K4 (224+(h % 3)*3) 3) % 10)*4) 4
  | 5 => packedAt g16K5 (248+((h/5+packedAt g16K5 (238+(h % 5)*2) 2) % 28)*5) 5
  | 6 => packedAt g16K6 (7+((h/1+packedAt g16K6 (6+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g16Pos : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0x95af654b5554b65a,0x2b4acb64d2b49939,0x5afbbc97bf17fb93,0xffac9294a52be777]))
  | 1 => 0x0
  | 2 => (OfNat.ofNat (certificateWord [0xa2d5a8952f3d51f9,0x458d1589655dea57,0xf13dd7bc8a29dd7f,0x12912e714ae6f878]))
  | 3 => (OfNat.ofNat (certificateWord [0xcb1ad22689a268ac,0x96f9e61fc86fb7f2,0x945eebf7dafe4924,0x2542452b9cf8ff80]))
  | 4 => (OfNat.ofNat (certificateWord [0x8c63e3f80dcff330,0x18de7f31818edf7f,0xdfe88d2513429189,0x49878f83e0ff2111]))
  | 5 => (OfNat.ofNat (certificateWord [0x707cfcff3e0b81c1,0xe0efbfddfff8e464,0xe190f23a1c8d1e4e,0x8e1bf843ff444a2a]))
  | 6 => (OfNat.ofNat (certificateWord [0x7f80ff3fcff3fdfe,0xfff0381e0e0f0787,0x061f03c3e0f1e070,0xf063fffe109094c4]))
  | 7 => 0x0
  | _ => 0
def g16Neg : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0x8000000000000000,0x0000000000000000,0x001ffc03ff01ff80,0xff8000000000e777]))
  | 1 => 0x0
  | 2 => (OfNat.ofNat (certificateWord [0xffc01ff,0x00000000000ff807,0xf81ffffc0001ffff,0x00000e7000e6f878]))
  | 3 => (OfNat.ofNat (certificateWord [0xffc01ff00ffff8,0x001ffffffffe0000,0x000000039cf8ff80]))
  | 4 => (OfNat.ofNat (certificateWord [0xffc00ffffe00,0x00ffffe0000fffff,0xffe0000000000000,0x00038f83e0ff0000]))
  | 5 => (OfNat.ofNat (certificateWord [0xfffff0000000,0x00fffffffff00000,0x0000000000000000,0x0003f003ff000000]))
  | 6 => (OfNat.ofNat (certificateWord [0xffffffffffff,0xff00000000000000,0x0000000000000000,0x0003fffc00000000]))
  | 7 => 0x0
  | _ => 0
def g16Atlas : Atlas := ⟨6,rawDecor 125 g16Pos g16Neg, (OfNat.ofNat (certificateWord [0xfffafffaffaaffaa,0xfafafafaaaaa0000,0xfffafffaffaaffaa,0xfafafafaaaaa0000,0xfffafffaffaaffaa,0xfafafafaaaaa0000,0xfffafffaffaaffaa,0xfafafafaaaaa0000])), g16N, g16R, (fun _ _ => 0), g16I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model
def g17Hint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0x7
  | 8 => 0x8
  | 9 => 0x9
  | 10 => 0xa
  | 11 => 0xb
  | 12 => 0xc
  | 13 => 0xd
  | 14 => 0xe
  | 15 => 0xf
  | 16 => 0x10
  | 17 => 0x11
  | 18 => 0x12
  | 19 => 0x13
  | 20 => 0x14
  | 21 => 0x16
  | 22 => 0x19
  | 23 => 0x1a
  | 24 => 0x1f
  | 25 => 0x20
  | 26 => 0x21
  | 27 => 0x23
  | 28 => 0x26
  | 29 => 0x27
  | 30 => 0x13101
  | 31 => 0x16101
  | 32 => 0x17101
  | 33 => 0x1d101
  | 34 => 0x1f101
  | 35 => 0x2e101
  | 36 => 0x2f101
  | 37 => 0x2f104
  | 38 => 0x2f109
  | 39 => 0x37101
  | 40 => 0x37105
  | 41 => 0x37106
  | 42 => 0x37108
  | 43 => 0x3711b
  | 44 => 0x3711c
  | 45 => 0x41104
  | 46 => 0x4711a
  | 47 => 0x53101
  | 48 => 0x53102
  | 49 => 0x53105
  | 50 => 0x53106
  | 51 => 0x53107
  | 52 => 0x54107
  | 53 => 0x54109
  | 54 => 0x54122
  | 55 => 0x56101
  | 56 => 0x56102
  | 57 => 0x56104
  | 58 => 0x56105
  | 59 => 0x56106
  | 60 => 0x5611d
  | 61 => 0x5611e
  | 62 => 0x5612c
  | 63 => 0x57101
  | 64 => 0x57102
  | 65 => 0x57104
  | 66 => 0x57105
  | 67 => 0x57106
  | 68 => 0x57107
  | 69 => 0x57109
  | 70 => 0x5712a
  | 71 => 0x5d101
  | 72 => 0x5d102
  | 73 => 0x5d103
  | 74 => 0x5d105
  | 75 => 0x5d107
  | 76 => 0x5f101
  | 77 => 0x5f102
  | 78 => 0x5f103
  | 79 => 0x5f105
  | 80 => 0x5f106
  | 81 => 0x5f107
  | 82 => 0x5f108
  | 83 => 0x5f117
  | 84 => 0x5f118
  | 85 => 0x5f119
  | 86 => 0x5f12b
  | 87 => 0x65107
  | 88 => 0x65109
  | 89 => 0x65122
  | 90 => 0x66101
  | 91 => 0x66102
  | 92 => 0x66103
  | 93 => 0x66104
  | 94 => 0x66106
  | 95 => 0x66108
  | 96 => 0x6610e
  | 97 => 0x6610f
  | 98 => 0x66115
  | 99 => 0x66118
  | 100 => 0x6611b
  | 101 => 0x6611c
  | 102 => 0x66125
  | 103 => 0x66129
  | 104 => 0x67107
  | 105 => 0x67109
  | 106 => 0x67122
  | 107 => 0x6712a
  | 108 => 0x6e101
  | 109 => 0x6e102
  | 110 => 0x6e103
  | 111 => 0x6e104
  | 112 => 0x6e105
  | 113 => 0x6e11d
  | 114 => 0x6e11e
  | 115 => 0x6e12c
  | 116 => 0x6f101
  | 117 => 0x6f102
  | 118 => 0x6f103
  | 119 => 0x6f104
  | 120 => 0x6f105
  | 121 => 0x6f107
  | 122 => 0x6f109
  | 123 => 0x6f114
  | 124 => 0x6f115
  | 125 => 0x6f116
  | 126 => 0x6f117
  | 127 => 0x6f118
  | 128 => 0x6f119
  | 129 => 0x6f12a
  | 130 => 0x77101
  | 131 => 0x77102
  | 132 => 0x77103
  | 133 => 0x77104
  | 134 => 0x77105
  | 135 => 0x77106
  | 136 => 0x77108
  | 137 => 0x77114
  | 138 => 0x77115
  | 139 => 0x77116
  | 140 => 0x77117
  | 141 => 0x77118
  | 142 => 0x77119
  | 143 => 0x7711b
  | 144 => 0x7711c
  | 145 => 0x7711d
  | 146 => 0x7711e
  | 147 => 0x77124
  | 148 => 0x7712b
  | 149 => 0x7712c
  | 150 => 0x93101
  | 151 => 0x96101
  | 152 => 0x96105
  | 153 => 0x97101
  | 154 => 0x97107
  | 155 => 0x9d101
  | 156 => 0x9f101
  | 157 => 0x9f103
  | 158 => 0x9f106
  | 159 => 0x9f108
  | 160 => 0xa6101
  | 161 => 0xa6103
  | 162 => 0xae101
  | 163 => 0xae105
  | 164 => 0xaf101
  | 165 => 0xaf104
  | 166 => 0xaf107
  | 167 => 0xaf109
  | 168 => 0xaf114
  | 169 => 0xaf115
  | 170 => 0xaf116
  | 171 => 0xb7101
  | 172 => 0xb7103
  | 173 => 0xb7105
  | 174 => 0xb7106
  | 175 => 0xb7108
  | 176 => 0xb711b
  | 177 => 0xb711c
  | 178 => 0xc511a
  | 179 => 0xc6120
  | 180 => 0xcc107
  | 181 => 0xcc109
  | 182 => 0xce105
  | 183 => 0xce119
  | 184 => 0xce11d
  | 185 => 0xce120
  | 186 => 0xce12d
  | 187 => 0xd3101
  | 188 => 0xd510e
  | 189 => 0xd5129
  | 190 => 0xd6101
  | 191 => 0xd6105
  | 192 => 0xd7101
  | 193 => 0xd7102
  | 194 => 0xd7104
  | 195 => 0xd7105
  | 196 => 0xd7106
  | 197 => 0xd7107
  | 198 => 0xd7109
  | 199 => 0xd711b
  | 200 => 0xd711c
  | 201 => 0xdd101
  | 202 => 0xde10e
  | 203 => 0xde10f
  | 204 => 0xde129
  | 205 => 0xdf101
  | 206 => 0xdf102
  | 207 => 0xdf103
  | 208 => 0xdf105
  | 209 => 0xdf106
  | 210 => 0xdf107
  | 211 => 0xdf108
  | 212 => 0xdf10c
  | 213 => 0xdf10d
  | 214 => 0xdf11a
  | 215 => 0xdf122
  | 216 => 0xdf128
  | 217 => 0xdf12b
  | 218 => 0xe7107
  | 219 => 0xe7109
  | 220 => 0xe7122
  | 221 => 0xee101
  | 222 => 0xee105
  | 223 => 0xef101
  | 224 => 0xef102
  | 225 => 0xef103
  | 226 => 0xef104
  | 227 => 0xef105
  | 228 => 0xef107
  | 229 => 0xef109
  | 230 => 0xef114
  | 231 => 0xef115
  | 232 => 0xef116
  | 233 => 0xf7101
  | 234 => 0xf7102
  | 235 => 0xf7103
  | 236 => 0xf7104
  | 237 => 0xf7105
  | 238 => 0xf7106
  | 239 => 0xf7108
  | 240 => 0xf7116
  | 241 => 0xf7119
  | 242 => 0xf711b
  | 243 => 0xf711c
  | 244 => 0xf711d
  | 245 => 0xf711e
  | 246 => 0xf712b
  | 247 => 0xf712c
  | 248 => 0x5753201
  | 249 => 0x5753202
  | 250 => 0x5753205
  | 251 => 0x5753207
  | 252 => 0x5756201
  | 253 => 0x5756202
  | 254 => 0x5756205
  | 255 => 0x5f53201
  | 256 => 0x5f53202
  | 257 => 0x5f53205
  | 258 => 0x5f53206
  | 259 => 0x5f5d201
  | 260 => 0x5f5d202
  | 261 => 0x5f5d205
  | 262 => 0x6617201
  | 263 => 0x662f201
  | 264 => 0x6657201
  | 265 => 0x6657202
  | 266 => 0x6e0e205
  | 267 => 0x6e0e21d
  | 268 => 0x6f5d201
  | 269 => 0x6f5d202
  | 270 => 0x6f5d205
  | 271 => 0x6f5d207
  | 272 => 0x6f66201
  | 273 => 0x6f66202
  | 274 => 0x6f6e201
  | 275 => 0x6f6e202
  | 276 => 0x6f6e205
  | 277 => 0x7737206
  | 278 => 0x7756201
  | 279 => 0x7756202
  | 280 => 0x7756206
  | 281 => 0x776e201
  | 282 => 0x776e202
  | 283 => 0x776e203
  | 284 => 0x9357201
  | 285 => 0x9657201
  | 286 => 0x9753201
  | 287 => 0x9756201
  | 288 => 0x9766201
  | 289 => 0x9d5f201
  | 290 => 0x9f53201
  | 291 => 0x9f5d201
  | 292 => 0xa657201
  | 293 => 0xa66f201
  | 294 => 0xae6f201
  | 295 => 0xaf5d201
  | 296 => 0xaf66201
  | 297 => 0xaf6e201
  | 298 => 0xb756201
  | 299 => 0xb76e201
  | 300 => 0xd35f201
  | 301 => 0xd677201
  | 302 => 0xd766201
  | 303 => 0xd766202
  | 304 => 0xd766206
  | 305 => 0xd76621b
  | 306 => 0xd76621c
  | 307 => 0xd7a6201
  | 308 => 0xd7a6206
  | 309 => 0xd7a621c
  | 310 => 0xdd6f201
  | 311 => 0xdf41207
  | 312 => 0xdfc1207
  | 313 => 0xee77201
  | 314 => 0xef66201
  | 315 => 0xef66202
  | 316 => 0xefa6201
  | 317 => 0xf70e21d
  | 318 => 0xf7b7205
  | _ => 0
def g17K11 : Nat → Nat
  | 0 => 0xff
  | _ => 0
def g17K10 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x504cc0b92d,0x29b98401c4540001,0x400000011c0001a4,0x7158014461180000,0x3c0028fc9c400000,0xbcd96560c8015dac,0x5c008c38e878a4e0,0x01a0000100f5bcac,0xdcb5919d381970d5,0x95996c8401101020,0x0095c001b14c0001,0x30918d7401540c01,0x7cb0000151080030,0x64a8247c00800169,0x8000f80120004468,0xe40474a188006c08,0x0049c800005801cc,0x35794814010c0000,0x000000c49801a904,0x013400013c1cf1b4,0x00882ccd24d0ed14,0xa400000000232401,0x983000c000460001,0x10002c0000a81803,0xc000430003a02001,0x850000ff510007bd,0x64007fd76007fd75,0x02ffd74007fd7300,0x7fd72017fd7100ff,0xd70007fd6502ffd6,0x404ffd63007fd620,0x17fd6100ffd6003f,0xfc7602ffd54007fd,0x53047fd52017fd51,0x00ffd50037fc7503,0x7fc6502ffd4302ff,0xd42017fd4100ffd4,0x002ffc7402ffc640,0x2ffc54007fd32017,0xfd3100ffd30027fc,0x73027fc63027fc53,0x02ffc43017fd2100,0xffd2001ffc7201ff,0xc6201ffc5202ffc4,0x201ffc3200ffd100,0x17fc71017fc61017,0xfc51017fc41017fc,0x31017fc2100ffc70,0x00ffc6000ffc5000,0xffc4000ffc3000ff,0xc2000ffc1000fff7,0x000fff6000fff500,0x0fff4000fff3000f,0xff2000ff71000fff,0x10017ff71017ff61,0x017ff51017ff4101,0x7ff31017ff2100ff,0xe10007ff7203fff6,0x2037ff5202fff420,0x27ff32017fe2100f,0xfe20007ff7303fff,0x63037ff5302fff43,0x01ffe32017fe3100,0xffe3002fff7402ff,0xf6402fff5402ffe4,0x302ffe42017fe410,0x0ffe40007ff7503f,0xff6502ffe54027fe,0x5301ffe52017fe51,0x00ffe50007ff7603,0x7fe6502fbe6402ff,0xe64027fe6301ffe6,0x2017fe6100ffe600,0x3ffe76037fe7502f,0xfe74027fe7301ffe,0x72017fe7100ffe70]))
  | _ => 0
def g17K9 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x81d7fc51bb033ffd,0xe162077ff346e40e,0xffe28dd80d7fd0ab,0x10efffa156202dff,0x422c43affe845880,0x97fd06b10e7ffa0d,0x62015ff40ac438ff,0xe81588037fd00b10,0xdfffa0162075ff1c,0x6ec0effe68dcc1df,0xfc71bb003efde164,0x76dff246ecedffe4,0x8dd8bdf7d0ab2177,0xefa0d642e7df412c,0x85bfbe81590b5f7d,0x00b203aff9637600,0x7ffbc2ca0effe68d,0xd41dffcb1bb016ff,0xa1165387ff422ca0,0x4bfe83594dfffd06,0xb280effa0965377f,0xf412ca02bfe81594,0xdbffd02b2806ffa0,0x165367ff402ca00b,0xfe7859401ffcf0b2,0x837ef9e164065ff3,0xc2c40cffe785880f,0xf7cecb201fbf9d96,0x503f7f3b2c407dfe,0x765d80fffcecbb1e,0x7ff9d97528fff3b2,0xe644ffe765c9577f,0xf0ebb01fff9d9650,0x3fff3b2c44bffe76,0x54c67ffcec99317f,0xf9db72697ff3b6e6,0xe4ffe76dd40fdfce,0xdbb01fff9db7603e,0xff3b6ec00bfe7854,0xc17ffcf0a997bef9,0xd564037bf3aaca06,0xf7e7554c0dbfceab,0xaa1fff9d576037ff,0x3aaea50ffe755cc8,0x7ffceab9292ffe1d,0x75037ff3aaca3bff,0xe755880dffceaa98,0xcbff9d532627ff3a,0xee4d1ffe75dcc0de,0xfcebba81bff9d775,0x036ff3aeeaeeffe7,0x5dd90dffce8bb1e3,0xff9d17527fff3a2e,0x642ffe745c8e1ffc,0xe8b28ebff9d16225,0x7ff3a2a631ffe744,0xc987ffce9b9343ff,0x9d37371fff3a6eae,0xdffe74dd8157fcf0,0x9902bff9e132027e,0xf39aa604fde734c8,0xbbf7ce6b20137f9c,0xd7342fff39aec77f,0xfe735d409ffce6b9,0x907ff9cd724e5ffc,0x3ae66fffe7359473,0xffce6b1013ff9cd5,0x3027ff39a64c2ffe,0x73dc809fbce7b981,0x3ff9cf73026ff39e,0xe6e2ffe73dd5d9ff,0xce7bb00ffb9c9620,0x1ff7392645cfbe72,0x59007bfce4b9213f,0xf9c9763b7ff392ea,0x4effe725cc07ffce,0x4b9266ffe1d72377,0xff392ca03ffe7258,0x893ffce4a980fff9,0xc93201ff7396e403,0xffe72dc807bfce5b,0x933fff9cb7370fff,0x396eaebffe72dd8b,0x7f7ce2b220fff9c5,0x763afff38aea4dff,0xe715cc81ffce2b91,0xb7ff9c5651c7ff38,0xac448ffe7154c61f,0xfce299307ff9c772,0x677ff38ee6e0ffe7,0x1dd5d5ffce3bb16b,0xef9c164417ff382e,0xc74ffe705d499ffc,0xe0b98ffff9c17236,0x7ff382ca37ffe705,0x888fffce0a98bfff,0x9c132607ff386e4c,0xdffe70dcdbfffce1,0xbaba7ff9c376227f,0xf432e407bfe865c8,0x87ffd0ab901affa1,0x572217ff422e405b,0xfe845c883ffd06b9,0x012ffa0d72207ff4,0x0ae402bfe815c87f,0xffd00b9006ffa017,0x228fff432e607bfe,0x865cca1ffd0ab981,0xaffa157327fff422,0xe605bfe845cc9dff,0xd04b980effa09732,0x6fff40ae602bfe81,0x5cc99ffd00b9806f,0xfa01733cfff432ea,0x07bfe865d4f1ffd0,0x8ba816ffa11753bf,0xff41aea04bfe835d,0x4edffd04ba80effa,0x09753afff40aea02,0xbfe815d4e9ffd00b,0xa806ffa017543fff,0x42aec06bfe855d90,0xdffd08bb016ffa11,0x7642fff41aec04bf,0xe835d909ffd04bb0,0x0effa097641fff40,0xaec02bfe815d905f,0xfd00bb006ffa0176]))
  | 1 => (OfNat.ofNat (certificateWord [0x6757fea0eece9ffd,0x40dd9dbffa91bb3b,0x7ff1d37676fffa46,0xecedffc64dd9dbff,0x8a9bb027ff4cb767,0x57fe98eece9ffd30,0xdd81dffa71bb3b3f,0xf1cf76767ff9c6ec,0xecffc63dd9d9ff8a,0x7bb3b7ff10f76757,0xfe90eece9ffd20dd,0x81dffa51bb3afff1,0xcb7675fff946eceb,0xffc62dd9d7ff8a5b,0xb3b7ff10b7675ffe,0x196ece9ffd10dd9d,0x5ffa31bb3abff1c7,0x76757ff8c6eceaff,0xc61dd9d5ff8a3bb3,0xabff10776757fe18,0xeeceaffc21dd9d3f,0xfa11bb3a7ff1c376,0x74fff846ece9ffc6,0x0dd9d3ff8a1bb3a7,0xff1037674ffe186e,0xce9ffc20dd9d3ff8,0x21bb3a7ffdc37674,0xeffb86ece9fff60d,0xd9d3ffea1bb3a7ff,0xd037674fff986ece,0x9fff20dd9d3fee21,0xbb3a7ffc4376757f,0xfb8eeceadff71dd9,0xd5ffec3bb3abffd4,0x776757ffa0eeceaf,0xff31dd9d5ffe43bb,0x3a7ff84376077ffb,0x96ec07fff62dd9dd,0xffea5bb3b7ffd0b7,0x6767ff996eceaffe,0x21dd9d3ffc41bb03,0xbffdcf76076ffb9e,0xec07fff63dd9ddff,0xea7bb3b7ffd0f767,0x5fff196eceaffe31,0xdd9d3ffc61bb3b7f,0xfdd37676fffb26ec,0xedfff54dd9dbffc8,0x7bb3b7ff90b76757,0xff20eece9ffe40dd,0x81dffeebbb01fffd,0x977676fff2a6ecec,0xffe53dd9d7ffca5b,0xb3abff9477674fff,0x286ec09bfe6854c1,0x3ffcd0a997bef995,0x64037bf32aea06f7,0xe6554c0ddfccab2a,0x1fff99576037ff32,0xaea50ffe655cc87f,0xfccab928affe1965,0x037ff32aca3bffe6,0x55880dffccaa98cb,0xff99532627ff32ee,0x4d1ffe65dcc0dffc,0xcbbabbbff9977603,0x5fe2c6eceeffc58d,0xd80bd7f0cb221bef,0x991763c7df322ea4,0xffbe645cc85f7cc8,0xb9282efe1964387d,0xf322ca05fbf86590,0x75f7cc8b112bef99,0x153437ff322ec78f,0xfe645d49fffcc8b9,0x90bff99172387ff3,0x22ca3affe6458895,0xffcc8a98c7ef9913,0x218fff32264c3fbe,0x64dc987ffcc9b934,0x3ef99373687ff326,0xe6e3fbe64dd5c7ff,0xcc9babb7ef993767,0x6fff326ec05bfc48,0xdd9dbff891bb026f,0xf9a13204fff34264,0x04fde635ccbbf7cc,0x6b2217ff98d763bf,0xff31aea04ffe635c,0xc83ffcc6b91bfff9,0x8d651cfff31ac404,0xffe6354c09ffcc69,0x930bff98f72027ff,0x31ee6e2ffe63dd5d,0x9ffcc7bb012ff0e3,0x76767fe1c6ec03fe,0xe625c807fdcc4991,0x73ef9896401f7f31,0x2c484ffe625d8edf,0xfcc4ba93bff98973,0x01fff312e497bff8,0x6588ddffcc4b280f,0xff9896224fff312a,0x603ffe624c807ffc,0xc5b933fff98b7370,0xfff316eaebffe62d,0xd8077f851bb3afff,0x0a3762dfdf30ac88,0x3ffe615d8ebffcc2,0xba937ff98573207f,0xf30ae46dffe61594,0x71ffcc2b1123ff98,0x553187ff30a64c1f,0xfe61dc99dffcc3b9,0xb83ff98775757ff3,0x0eec02bfc18dd9d5,0xff831bb16bef9816,0x4417ff302ec74ffe,0x605d499ffcc0b98f,0xfff98172367ff302,0xca37ffe605888fff,0xcc0a98bfff981326,0x07ff306e4cdffe60,0xdcdbfffcc1baba7f,0xf9837600dfe046ec,0xe9ffc08dd9d37fc1,0x1bb3a7ff82376755,0xff0c6eceaffe18dd]))
  | 2 => (OfNat.ofNat (certificateWord [0xd5c1ff883bab83ff,0x0c775707fe10eead,0xfffd08dd5bfff8e1,0xbab7fff183756fff,0xf846eadfffc50dd5,0xbfff881bab7fff0c,0x3756fffe106eadff,0xfc10dd5bfffee1ba,0xb7f7fdc3756ffffb,0x06eadffff50dd5bf,0xffe81bab7fffcc37,0x56ffff906eadfff7,0x10dd5bfffe21bab8,0x3ffdc775707ffb0e,0xeae0fff51dd5c1ff,0xe83bab83ffcc7757,0x07ff90eeadfffe10,0xdd41dffee5ba83b7,0xfdcb75727ffb16ea,0x06fff52dd5c7ffe8,0x5bab8bffccb75707,0xff10eeadfffe20dd,0x41dffee7bab93ffd,0x8f75037ffa9eeae3,0xfff43dd5c3ffc65b,0xab83ff8c7756ffff,0x186eae3fff74dd5c,0x7ffec9bab8fffd53,0x7571fff21eeae3ff,0xe42dd5c1ffc83bab,0x7fff9037506fdfc2,0xac808bff8558811f,0xff0ab101fefd9564,0x03fbfb2aca07eff6,0x55d80fdfecab101f,0xffd9576037ffb2ae,0xa51fff655cc89ffe,0xcab9376ffe156503,0x7ffb2aca07fff655,0x880dffecaa98cfff,0xd953262fffb2ee4d,0x2fff65dcc0dffecb,0xba81eff1a375727f,0xe346ea86ffe545d8,0xf1ffca8ba93fff95,0x173217ff2a2e470f,0xfe5459475ffca8b1,0x12bff9515318fff2,0xa264c3ffe54dc9a1,0xffca9b9b8fff9537,0x502dfe246eae3ffc,0x48dd4117fcb09902,0x3ff96132027ef29a,0xe604fde534c8bbf7,0xca6b2013df94d534,0x2fff29aec77ffe53,0x5d409ffca6b9907f,0xf94d724ddffc2aa6,0x6fffe5359473ffca,0x6b1013ff94d53027,0xff29a64c2ffe53dc,0x809ffca7b9b8bff9,0x4f75025fe1c6eae2,0xffc38dd407fdca4b,0x9173ef94964377bf,0x292ca84ffe525d8e,0xdffca4ba93bff949,0x7301fff292e46eff,0xe5259407ffca4b11,0x27ff9495301fff29,0x26403ffe52dc99ff,0xfca5b9b87ff94b75,0x01dfe146eae1ffc2,0x8dd4b7f7ca2b220f,0xff945763afff28ae,0xa4dffe515cc81ffc,0xa2b91b7ff945651c,0x7ff28ac448ffe515,0x4c61ffca299307ff,0x94772677ff28ee6e,0x0ffe51dd4057f831,0xbab83ff063752d7d,0xf282c882ffe505d8,0xe9ffca0ba933ff94,0x1731ffff282e46cf,0xfe505946fffca0b1,0x11fff9415317fff2,0x8264c0ffe50dc99b,0xffca1b9b7fff9437,0x500dfe046eadfffc,0x08dd5bf7fc11bab7,0xfff82375705ff0c6,0xeae0ffe18dd41d7f,0xc51ba83bff963720,0x77ff146ea0ebfe38,0xdd401ffef0a983bf,0xf96373077ff1c6ea,0x07bff6854c97ffed,0x0a9816ffa1153257,0xff422a603bfe8254,0xc93ffd04a980affa,0x0553247ff40aa601,0xbfe8054c8fffd00a,0x9b8eff9237571fff,0x246ea10fff865d40,0x17ff0cba827ffe19,0x7304dffc32e60fff,0xf865c81f7ff0cb93,0xa7fd4437603fdeb2,0x6ec0eefd68dd813b,0xfae7bb3ab7f5c776,0x74efeb86ec07ffd6,0x8dd81dffaebbb3b7,0xff5d376077feb9ee,0xc0effd72dd9d5ffa,0xe3bb3a7ff5c37674,0xdffc32ec07ffd65d,0xd9dbffac9bb01fff,0x58f7603ffeb16ece,0xaffd61dd9d3ffac1,0xbb01fffde37603ef,0xfbc6ecedffd54dd8,0x13ffaa7bb3bfff54,0xb76757fea8eece9f,0xfd50dd81dffab1bb,0x3bbff1d776777ffa,0xc6eceeffc65dd9db,0xffa87bb3b7ff50b7]))
  | 3 => (OfNat.ofNat (certificateWord [0x6501fff192c449ff,0xe3254c07ffc64990,0x0fff8cb7267fff19,0x6e603bfc28dcd9ff,0xf851b996fef8c564,0x41fff18aec75ffe3,0x15d49bffc62b9903,0xff8c57236fff18ac,0xa38ffe3158891ffc,0x62a98c3ff8c53260,0xfff18ee4ceffe31d,0xcc057f831b9b3bff,0x063732d7df182c88,0x2ffe305d8e9ffc60,0xba933ff8c1731fff,0xf182e46cffe30594,0x6fffc60b111fff8c,0x15317fff18264c0f,0xfe30dc99bffc61b9,0x806ff0237366ffe0,0x46e6cdbfe08dcd9b,0xffc11b9b3aff8637,0x3677ff0c6e60ebfe,0x28dcc15ffef09903,0xbff8e372077ff146,0xe607bff684c867ff,0xed09901affd61321,0x97ffac26405bff48,0x4c863ffe909900af,0xfa0532187ff40a64,0x01bfe804c85fffd0,0x09921bffe1176435,0xffc22ec78fff845d,0x4f17ff08ba93fffe,0x117327dffc22e642,0xfff845c8857ff08b,0x921bffdd1763c7ff,0xba2ea4ffff745cc8,0x5ffee8b91c3ffdd1,0x651d7ffba2c44aff,0xf7454c63ffee8993,0x0fffdd372687ffba,0x6e670bff84594e1f,0xff08b28eaffe1162,0x1d7ffc22c486fff6,0x45d8f1ffec8ba93f,0xffd9173217ffb22e,0x470fff6459475ffe,0xc8b112bffd915318,0xfffb2264c3fff64d,0xc9a1ffec9b992aff,0xe1153257ffc22a68,0x6fff545d8f1ffea8,0xba93fffd5173217f,0xfaa2e470fff54594,0x75ffea8b112bffd5,0x15318fffaa264c3f,0xff54dc9a1ffea9b9,0x8c6ff9213218fff2,0x426486ffe435d8f1,0xffc86ba93fff90d7,0x3217ff21ae470ffe,0x4359475ffc86b112,0xbff90d5318fff21a,0x64c3ffe43dc9a1ff,0xc87b9a1bff909763,0xc7ff212ea4fffe42,0x5cc85ffc84b91c3f,0xf909651d7ff212c4,0x4affe4254c63ffc8,0x49930fff90b72687,0xff216e683ffe415d,0x8ebffc82ba937ff9,0x0573207ff20ae46d,0xffe4159471ffc82b,0x1123ff90553187ff,0x20a64c1ffe41dc99,0xdffc83b9a0bff901,0x763a7ff202ea4cff,0xe405cc7fffc80b91,0xb3ff901651bfff20,0x2c447ffe4054c5ff,0xfc8099303ff90372,0x66fff206e6c3bfe4,0x8dc987ffc91b9342,0xff92373687ff246e,0x612fff855d8017ff,0x0abb047ffe157300,0x5ffc2ae608fff855,0xc8117ff0ab937ffd,0x44375007deb26ea0,0xef7d58dd411bfae5,0xbab7f7f5c375077f,0xebb6ea06ffd58dd5,0xc7ffae9ba83bff5c,0xf75077feb96eae0f,0xfd71dd5bfffae1ba,0xb7effe1575037feb,0x2eeae3ffd64dd5cb,0xffac7ba823ff58b7,0x5707feb0eeadfffd,0x60dd41dffad1bab9,0x3ff1db7571ffeaa6,0xea06ffd53dd40dff,0xaa5bab83ff547756,0xfffea86ea06fff78,0xdd40dbfef1bab93f,0xfda375037fe32eea,0xe3ffd43dd5c7ffa8,0x5bab83ff507756ff,0xfea06eae3ffd48dd,0x5c7ff8e9bab8fff1,0x937571fffa46eae3,0xffc54dd411ffa65b,0xab83ff4c7756fffe,0x986ea0effd38dd5c,0x5ff8e7bab8bff18f,0x75717ff9c6eae2ff,0xc53dd5c7ff887bab,0x83ff487756fffe90,0x6ea0effd28dd5c3f,0xf8e5bab87ff18b75,0x70fff946eae1ffc5,0x2dd5c7ff885bab87,0xff0cb756fffe886e,0xae0ffd18dd5c1ff8,0xe3bab83ff1877570,0x7ff8c6eae0ffc51d]))
  | 4 => (OfNat.ofNat (certificateWord [0x5910bffe64bb1dff,0xfcc975027ff992e6,0x03fff325c9777ff0,0x4991bfffcc96501f,0xff992c404fff3254,0xc07ffe649900fffc,0xcb72025fe1c6e4c2,0xffc38dc8b7f7c42b,0x220fff885763afff,0x10aea4dffe215cc8,0x1ffc42b91b7ff885,0x651c7ff10ac448ff,0xe2154c61ffc42993,0x07ff88772015fe0c,0x6e4c1ffc18dc8b5f,0x7c40b220bff88176,0x3a7ff102ea4cffe2,0x05cc7fffc40b91b3,0xff881651bfff102c,0x447ffe2054c5fffc,0x4099303ff8837200,0xdfe046e4c0ffc08d,0xc9817fc11b9303ff,0x8237260dff0c6e4c,0x1ffe18dc801fbf06,0xbb002f7e0d7604ff,0xfc1aec09bff835d8,0x21fff06ba802ffe0,0xd7507fffc1ae40fb,0xff835c99bfea21b9,0x83bf74e373677ee9,0x8ee6cdfdd30dcc13,0xf7ac9b98277f5db7,0x3077febb6e60effd,0x75dcda1ffae9b981,0x3ff4e373077feb96,0xe6ceffd71dcd9bff,0xae1b9b36ffe0d730,0x4ffeb2ee6d0ffd64,0xdcc09ffac7b9827f,0xf58b73677feb0ee6,0xcdffd60dcc1dffad,0x1b9b4bff1db73687,0xfeaa6e604ffd53dc,0xda7ffaa5b9b3bff5,0x477366ffea86e60e,0xffd58dcda3ff8ebb,0x9b47ff19773687fe,0xa1ee6d0ffd42dcd9,0xdffa83b9b37ff503,0x73687fea46e6d0ff,0xc74dcda1ff8c9b9b,0x43ff15373027fe99,0x6e6ceffd31dcd9bf,0xfa61b9813ffde373,0x026ffbc6e6d2fff6,0x8dcc09fb8c7b9813,0xff18f7368fffac6e,0x604ffc53dcda1ffe,0x91b9b43ff10f7367,0x7fe90ee6cdffd20d,0xcc1dffa51b9b3fff,0x1cb7367ffe316e6c,0xfffc52dcda1ff885,0xb9b3fffca37367ff,0xe196e6cdffd10dcd,0x9dffa31b9b3bff1c,0x773677fe30ee6cef,0xfc51dcd9dff883b9,0xb3bffc6373677fe1,0x8ee6ceffc21dcd9b,0xffa11b9b37ff1c37,0x366ffe306e6cdffc,0x50dcd9bff881b9b3,0x7ffc237366ffe186,0xe6cdffc20dcd9bff,0x821b9b37ffdc3736,0x6fffb06e6cdfff50,0xdcd9bffe81b9b37f,0x7cc37366fff986e6,0xcdfff20dcd9bfee2,0x1b9b37ffc4373677,0xffb8ee6cefff61dc,0xd9dffea3b9b3bffd,0x0773677ef98ee6ce,0xfff31dcd9dffe43b,0x9b37ff84373077ff,0xb96e6d2fff62dcda,0x3ffea5b9b43ffd0b,0x73027ff996e6ceff,0xe21dcd9bffc41b98,0x26ffe0d6504fffc1,0xaca09fbf83590137,0xff06b1027ffe0d62,0x25fefb1aa633fdf6,0x34c80ff7ec6b201f,0xbfd8d7603fffb1ae,0xc79fff635d409ffe,0xc6b9913ffd8d7203,0xfffb1aca07fff635,0x8809ffec6a9813ff,0xd8d3262fffb1ee4d,0x2fdf63dcc09ffec7,0xb981eff1a373697f,0xe346e606fdf5354c,0xbdf7ea6b201bdfd4,0xd75037bfa9aca87f,0xff535d80dffea6ba,0x813ffd4d7321fffa,0x9ae4c9bff8354c0d,0xffea6b28efffd4d6,0x2027ffa9aa604fff,0x534c989ffea7b901,0x3ffd4f73035fe2c6,0xe6d1ffc58dcd0dff,0xe86bb1e3ffd0d752,0x7fffa1ae642fff43,0x5c8e1ffe86b28ebf,0xfd0d62257ffa1aa6,0x31fff434c987ffe8,0x7b9343ffd0f7302d,0xfe246e6d0ffc48dc,0xc07fdc64b900ffb8,0xc96201fef192645c,0xfbe3259109ffc64b,0xb1dbff8c975277ff,0x192e603ffe325c92,0xd7ff06991bbff8c9]))
  | 5 => (OfNat.ofNat (certificateWord [0x57526fffb0ae640f,0xff615c8dbffec2b2,0x8e3ffd8562247ffb,0x0aa630fff614c891,0x7ff02a9923ffe055,0x32dfdfa8ac86df7f,0x5159507ffea2bb1d,0x7ffd457526fffa8a,0xe640fff515c8dbff,0xea2b28e3ffd45622,0x47ffa8aa630fff51,0x4c907ffe82bb1d7f,0xfd057526fffa0ae6,0x40fff415c8dbffe8,0x2b28e3ffd0562247,0xffa0aa630fff414c,0x8617ff02990c3ffe,0x0532247ef98aa630,0xfdf314c8b7f7e62b,0x220fffcc5763afff,0x98aea4dfff315cc8,0x1ffe62b91b7ffcc5,0x651c7ff98ac448ff,0xf3154c61ffe62990,0xe3fbc85622dfdf90,0xac883fff215d8ebf,0xfe42ba937ffc8573,0x207ff90ae46dfff2,0x159471ffe42b1123,0xffc8553187ff90a6,0x45afbe1059105ffc,0x20bb1d3ff8417526,0x7ff082e63fffe105,0xc8d9ffc20b28dfff,0x8416223fff082a62,0xfffe104c825fff04,0xbb002ffe0976007f,0x7c12ea00bef825d4,0x11fff04ba822ffe0,0x97508fffc12e600b,0xff825cd81fea21b9,0x03bfb4a372607f69,0x06e400fbd64dc811,0xbfaebb903bff5db7,0x2077febaee4c3ffd,0x74dc81dffae7b900,0xfff4a37260ffeb8e,0xe4c0ffd70dc9817f,0xf04b9023ff597726,0x1ffeb26e4c6ffd63,0xdc807ffac5b9307f,0xf58772607feb06e4,0x0effd68dc98bff8e,0xdb930fff55372047,0xfea9ee403ffd52dc,0x983ffaa3b9303ff5,0x4372077feac6e4c4,0xffc75dc989ff8cbb,0x930fff50f7261ffe,0xa16e4c1ffd41dc98,0x1ffa81b930fff523,0x7261ffe3a6e4c3ff,0xc64dc987ff8a9b90,0x0fff4cb7260ffe98,0xee4c0ffd30dc81df,0xfa71b930bff1cf72,0x617fe31ee4c2ffc5,0x3dc987ff887b9307,0xff48772607fe906e,0x403fff78dc807bfe,0xf1b9317ffda37201,0xffe316e4c4fff58d,0xc807fd8a5b900fff,0x14b7261fffa46e4c,0x3ffc42dc985ffe71,0xb900fff0cb72607f,0xe886e4c1ffd18dc9,0x83ff8e3b9307ff18,0x77260ffe28ee4c1f,0xfc41dc983ff863b9,0x307ffc637260ffe1,0x0ee4c0ffd08dc981,0xff8e1b9303ff1837,0x2607fe286e4c0ffc,0x40dc981ff861b930,0x3ffc2372607fe106,0xe4c0ffc10dc981ff,0xee1b9303ffd83726,0x07ffa86e4c0fff40,0xdc981ffe61b9303f,0xbc8372607ff906e4,0xc0ff710dc981ffe2,0x1b9307ffdc77260f,0xffb0ee4c1fff51dc,0x983ffe83b9307ffc,0xc77260fff90ee4c0,0xffe10dc8117ff04b,0x2823ffe096506fdf,0xc12c807fef625880,0xff7ec4b201fbfd89,0x7603f7fb12ca07ff,0xf625d8f3ffec4ba9,0x47ffd897301fffb1,0x2e4bebff825880ff,0xfec4b280fffd8962,0x25fffb12a603fff6,0x24c807ffec5b901e,0xff1a37262ffe346e,0x408bff8254c11fff,0x04a98effbd496219,0x7f7a92645efbf525,0x900defea4baa1fff,0xd4976037ffa92ea5,0x0fff525cc07ffea4,0xb901bffd496501ff,0xfa92c406fff5254c,0x07ffea499313fbd4,0xb7201fffa96e406b,0xfc58dc989ff8b1b9,0x21bffd09763c7ffa,0x12ea4ffff425cc85,0xffe84b91c3ffd096,0x51d7ffa12c44afff,0x4254c63ffe849930,0xfffd0b7202dfe246,0xe4c3ffc48dc809fd,0xe6499013f7cc9730,0x27ef992a65dfbf32]))
  | 6 => (OfNat.ofNat (certificateWord [0x8dcdbf7fa11baba6,0xff42376417fe402e,0xc01bfc805d8e9ff9,0x00ba806ff2017526,0x7fe402e601bfc805,0xcc7fff900b9006ff,0x201722d7de382c88,0x2ffc705d8e9ff8e0,0xba933ff1c1731fff,0xe382e46cffc70594,0x6fff8e0b111fff1c,0x15317ffe3826401b,0xfc80594d9ff900b2,0x96bef2016400dfe4,0x02c437ffc8058803,0x7fe11bb16bef1816,0x4417fe302ec74ffc,0x605d499ff8c0b98f,0xfff18172367fe302,0xca37ffc605888fff,0x8c0a98bfff181320,0x0dfe402a647ffc80,0x54c037fe11ba96be,0xf14164417fe282ec,0x74ffc505d499ff8a,0x0b98ffff14172367,0xfe282ca37ffc5058,0x88fff8a0a98bfff1,0x4132417fe202ec74,0xffc405d499ff880b,0x98ffff10172367fe,0x202ca37ffc405888,0xfff880a98bfff101,0x3200dfe402642fff,0xc804c8037fe11b99,0x6bef0c164417fe18,0x2ec74ffc305d499f,0xf860b98ffff0c172,0x367fe182ca37ffc3,0x05888fff860a98bf,0xff0c13200dff846e,0x45afbc2059105ff8,0x40bb1d3ff0817526,0x7fe102e63fffc205,0xc8d9ff840b28dfff,0x0816223ffe102a62,0xfffc204c8b5f7820,0xb220bff041763a7f,0xe082ea4cffc105cc,0x7fff820b91b3ff04,0x1651bffe082c447f,0xfc1054c5fff82099,0x20bffe0176415ffc,0x02ec74fff805d4e9,0x7ff00ba933ffe017,0x3265ffc02e63ffff,0x805c87f7ff00b916,0xbefdc164416ffb82,0xec74dff705d505ff,0xee0bb1d3ffdc1752,0x67ffb82e63ffff70,0x5c8d9ffee0b28dff,0xfdc16223fffb82a6,0x2ffff704c8d97ff0,0x0b29b3ffe01652d7,0xdfc02c837bff8058,0x86ffff00b116bafd,0x81642d7dfb02c86c,0xeff6059505ffec0b,0xb1d3ffd8175267ff,0xb02e63ffff605c8d,0x9ffec0b28dfffd81,0x6223fffb02a62fff,0xf604c88f7ff00a99,0x1fffe01532d7dfa8,0x2c86cf7f5059505f,0xfea0bb1d3ffd4175,0x267ffa82e63ffff5,0x05c8d9ffea0b28df,0xffd416223fffa82a,0x62ffff504c905ffe,0x80bb1d3ffd017526,0x7ffa02e63ffff405,0xc8d9ffe80b28dfff,0xd016223fffa02a62,0xffff404c85f7ff00,0x990bfffe013223fe,0xf982a62ffdf304c8,0xb5f7e60b220bffcc,0x1763a7ff982ea4cf,0xff305cc7fffe60b9,0x1b3ffcc1651bfff9,0x82c447fff3054c5f,0xffe60990dffbc816,0x217ff7902645afbf,0x2059105ffe40bb1d,0x3ffc8175267ff902,0xe63ffff205c8d9ff,0xe40b28dfffc81622,0x3fff902a62ffff20,0x4c8b5f6e20b220bf,0xdc41763a7fb882ea,0x4cff7105cc7ffee2,0x0b91b3fdc41651bf,0xfb882c447ff71054,0xc5ffee209916befc,0x4164417ff882ec74,0xfff105d499ffe20b,0x98ffffc4172367ff,0x882ca37fff105888,0xfffe20a98bfffc41,0x3241fffc0aec83bf,0xf815d8ebfff02ba9,0xd6ffe057526fffc0,0xae64dbff815cc81f,0xff02b9102ffe0572,0x2dfdfb8ac883dff7,0x15d907ffee2bb1d7,0xffdc57526fffb8ae,0x640fff715c8dbffe,0xe2b28e3ffdc56224,0x7ffb8aa630fff714,0xc8db7ff02b29b7ff,0xe0565007dbc0ac85,0xbfbf81590717ff02,0xb10e3ffe05622df5,0xfb0ac85bfbf61591,0x07ffec2bb1d7ffd8]))
  | 7 => (OfNat.ofNat (certificateWord [0x8d32035ffac6e604,0xbff38dd409eb8a6a,0x9813f714d532efde,0x29ac804f7c5354d0,0xbff8a6bb1dfff14d,0x75027fe29ae641ff,0xc535c8dfff8a6b28,0xe7ff14d62027fe29,0xaa604ffc534c80b7,0xfe91b9a1bff10d76,0x3c7fe21aea4fffc4,0x35cc85ff886b91c3,0xff10d651d7fe21ac,0x44affc4354c63ff8,0x869916fef4856441,0xffe90aec75ffd215,0xd49bffa42b9903ff,0x4857236ffe90aca3,0x8ffd2158891ffa42,0xa98c3ff485322d7d,0xe902c882ffd205d8,0xe9ffa40ba933ff48,0x1731fffe902e46cf,0xfd205946fffa40b1,0x11fff4815317ffe9,0x02640fbfd28dcc11,0x7fa51ba83eff4a37,0x6427fe412ec03bfc,0x825d811fd904ba80,0xefb209753b7fe412,0xea03bfc825d49dff,0x904b980eff209730,0x1ef6392e403fec72,0x5c8b9f78e4b200f7,0xf1c972427fe392ec,0x76ffc725d49dff8e,0x4b980fff1c972105,0xffbc6e46effc7259,0x407ff8e4b1127ff1,0xc95301ffe3926403,0xbfc82594ddff904b,0x2973ef2096403dff,0xb46e403bff28dd80,0x7fd8c4b1173ef189,0x6401f7e312c484ff,0xc625d8edff8c4ba9,0x3bff1897301ffe31,0x2e46effc6259407f,0xf8c4b1127ff18953,0x01ffe3126403bfc8,0x254c93ff904a981a,0xffd637201dff946e,0xa03fec5258807fd8,0xa499173ef1496437,0x7be292ca84ffc525,0xd8edff8a4ba93bff,0x1497301ffe292e46,0xeffc5259407ff8a4,0xb1127ff1495301ff,0xe2926405bff48dc9,0x0dff884bb1e3ff10,0x97527ffe212e642f,0xfc425c8e1ff884b2,0x8ebff10962257fe2,0x12a631ffc424c809,0x7fe71b900effca37,0x301fe61926403fec,0x324c807fb8649917,0x3ef0c964427fe192,0xec76ffc325d49dff,0x864b980fff0c9723,0x77fe192ca03ffc32,0x58893ff864a980ff,0xf0c9322d7de882c8,0x82ffd105d8e9ffa2,0x0ba933ff441731ff,0xfe882e46cffd1059,0x46fffa20b111fff4,0x415317ffe88264c1,0xbfd18dc99d7fa31b,0x9b82ff46375755fe,0x8c6ec83ffc815d80,0x57f902bb1d7ff205,0x75015fe40aea4dff,0xc815cc057f902b99,0x03ff20572015fe40,0xae45bfbc7159107f,0xf8e2bb1d7ff1c575,0x26ffe38ae640ffc7,0x15c8dbff8e2b28e3,0xff1c562247fe38aa,0x630ffc714c8057f9,0x02b29b7ff205652d,0xfda40ac85bfbc815,0x90057f902b10e3ff,0x20562015ff8c6ec5,0xbfbc6159107ff8c2,0xbb1d7ff1857526ff,0xe30ae640ffc615c8,0xdbff8c2b28e3ff18,0x562247fe30aa630f,0xfc614c8057f902a9,0x923ff20553015ff8,0xc6ea5bfbc5159107,0xff8a2bb1d7ff1457,0x526ffe28ae640ffc,0x515c8dbff8a2b28e,0x3ff14562247fe28a,0xa630ffc514c907ff,0x882bb1d7ff105752,0x6ffe20ae640ffc41,0x5c8dbff882b28e3f,0xf10562247fe20aa6,0x30ffc414c8057f90,0x2990c3ff20532015,0xff8c6e65bfbc3159,0x107ff862bb1d7ff0,0xc57526ffe18ae640,0xffc315c8dbff862b,0x28e3ff0c562247fe,0x18aa630ffc314c80,0x57fe31b916fef085,0x6441ffe10aec75ff,0xc215d49bff842b99,0x03ff0857236ffe10,0xaca38ffc2158891f,0xf842a98c3ff08532,0x605fe846e4cdbfd0]))
  | 8 => (OfNat.ofNat (certificateWord [0x505888fffaa0a982,0x2ff56372005feac6,0xe600bfd58dd90fff,0x90abb01aff215762,0x87fe42ae606bfc85,0x5cc87ff90ab901af,0xf21572036be3aaea,0x06f7c755d40dbf8e,0xabaa1fff1d576037,0xfe3aaea50ffc755c,0xc87ff8eab9092ffd,0xe375037fe3aaca3b,0xffc755880dff8eaa,0x981aff215621dffe,0x42ac407bff68dd40,0xd7feb1bb01b9f195,0x65037be32aca06ef,0xc655950fff8cabb0,0x1bff19575287fe32,0xae643ffc655c80df,0xf8cab28efff19562,0x037fe32aa631bfd4,0x84c90dffa86bb1e3,0xff50d7527ffea1ae,0x642ffd435c8e1ffa,0x86b28ebff50d6225,0x7fea1aa686ffd425,0xd8f1ffa84ba93fff,0x50973217fea12e47,0x0ffd4259475ffa84,0xb112bff5095341ff,0xea0aec75ffd415d4,0x9bffa82b9903ff50,0x57236ffea0aca38f,0xfd4158891ffa82a9,0xa0bff501763a7fea,0x02ea4cffd405cc7f,0xffa80b91b3ff5016,0x51bffea02c447ffd,0x4054d877fa91b934,0x2ff5237371dfea46,0xeaedbfd48dd90dff,0x908bb016ff211763,0xc7fe422ea05bfc84,0x5d49fff908b9816f,0xf21173217fe422e4,0x05bfc845c90dff8e,0x8bb1e3ff1d17527f,0xfe3a2e642ffc745c,0x8e1ff8e8b28ebff1,0xd162257fe3a2a605,0xbfc84594e1ff908b,0x2816ff211621d7fe,0x422c405bff48dd90,0xdff8c8bb1e3ff191,0x7527ffe322e642ff,0xc645c8e1ff8c8b28,0xebff19162257fe32,0x2a605bfc8454c95f,0xf908a9816ffd2375,0x437fe2a2ec78ffc5,0x45d49fff8a8b990b,0xff15172387fe2a2c,0xa3affc5458895ff8,0xa8a98c2ff6053217,0xdfec026409fbd644,0xc813ffaec99023ff,0x5d53218ffeba2640,0xaffd784c809ffae6,0x9900fff5c932187f,0xeb8a642fffd704c8,0x11ffaca990c7ff59,0x13204ffeb426404f,0xfd634c807ffac499,0x0c3ff5853217ffeb,0x026433ffc764c863,0xffaa899023ff5613,0x2027fea9a6403ffd,0x524c861ffaa2990b,0xfff54132197fe3aa,0x6432ffc654c863ff,0xa90990c7ff50d321,0x8ffea126430ffd41,0x4c85fffa80990c7f,0xf1d13218ffe32264,0x31ffc544c861ffb0,0x2990bfff60132075,0xfe3c2640affc784c,0x80f7f8d0990cfff1,0xa132035fe2c26432,0xffc584c80b7f8909,0x90c7ff121322dfde,0x98ac883ffd315d8e,0xbffa62ba937ff4c5,0x73207fe98ae46dff,0xd3159471ffa62b11,0x23ff4c553187fe98,0xa645afbd3059105f,0xfa60bb1d3ff4c175,0x267fe982e63fffd3,0x05c8d9ffa60b28df,0xff4c16223ffe982a,0x62fffd304c8017fa,0x71b9002ff4e37504,0xdfe9c6ec09fdc835,0xd8097b906bb217ff,0x20d76025fe41aec7,0x7ffc835d4097f906,0xba907ff20d72025f,0xe41ae404ddc735cc,0x09fb8e6b9977ef1c,0xd64026fe39ae685f,0xfc735d8efff8e6ba,0x813ff1cd7320ffe3,0x9ae422bff78dccdf,0xff8e6b28e7ff1cd6,0x2027fe39aa604ffc,0x734c8097f906b29b,0xfff20d652efde41a,0xc804bfc8358873ff,0x906b101effda3730,0x25ff9c6ec04fdc63,0x54c09fb8c699177e,0xf18d6442ffe31aec,0x77ffc635d409ff8c,0x6b9907ff18d7237f,0xfe31aca39ffc6358,0x809ff8c6a9813ff1]))
  | 9 => (OfNat.ofNat (certificateWord [0x58d760077ebb2c40,0x8efd65588d9dfac0,0xb28277f5d973046f,0xebaae483dfd715d9,0x05bfae0bb1d37f5c,0x175005febc2ca86b,0xfd845d8137fb0cb9,0x802ff5e16241dfec,0x0aec82bfd805d801,0xffb0abb21bff6117,0x604ffec1aec00ffd,0x825d907ffb02bb20,0xbff60176415feb46,0xec78bfd845d4017f,0xaf0a9822ff615723,0xadfec0aea74bfd80,0x5d401ffb0cba803f,0xf5d9753c7fec22ea,0x00ffd835d411ffb0,0x4ba9d7ff605753a7,0xfec02ea74bfd58dd,0x49f7fb08b990aff6,0x1172437feba2ec78,0xffd745d4017faf09,0x9136ff60573265fe,0xc02e609ffd865cc1,0x3ffaecb9803ff615,0x73007febaae64fff,0xd845cc9fffae8b98,0x4fff6097326ffec0,0xae64cffd805cc997,0xfa71b9902ff60572,0x1fdfec02e40fffd8,0x65c81fffaecb9023,0xff61572047febaae,0x442ffd845c885ffa,0xe8b903fff60d7207,0xffeb9ae440ffd815,0xc87fffb00b90feff,0x4a37241ffeb8aec7,0x5ffd715d49bffae2,0xb9903ff5c572417f,0xeb82ec74ffd705d4,0x99ffae0b98ffff5c,0x172385fec22ca09b,0xfd6854c117fb0ab1,0x1b6ff60565365fec,0x02ca00ffd785940f,0xffaecb281bff5d56,0x5387feba2ca09ffd,0x7359411ffae4b29b,0x7ff5c565367feb82,0xca70ffd8459413ff,0xb06b2823ff609653,0x6ffec0aca6cffd80,0x5941d7f8f0b2803f,0xf1e1651d5fec22c4,0x86ffd645d8f1ffac,0x8ba93fff59173217,0xfeb22e470ffd6459,0x4137fad09901fff5,0x8d763d7feb1aea04,0xffd635cc8bffac6b,0x901fff58d651c5fe,0xc0ac437bfd805881,0x9ffaf0b101fff5d9,0x62047febaac43aff,0xd7458813ffae6b10,0x0fff5c9621c7feb8,0xac437ffd7058811f,0xfb0ab101fff59562,0x1d7fec22c43affd6,0x458813ffb06b101f,0xff58d621c7fec0ac,0x437ffd805881d7f8,0xf0b1033ff1e16241,0xffeb0aec75ffd615,0xd49bffac2b9903ff,0x5857236ffeb0aca3,0x8ffd6158905ffac0,0xbb1d3ff58175267f,0xeb02e63fffd605c8,0xd9ffac0b28dfff58,0x162005feb46e409b,0xfd68dcc017fad1ba,0x9e7ff2197503dfe4,0x32ea51ffc865cc0f,0x7f90cb9913ff2197,0x203dfe432e407cfc,0x765d80fdf8ecbb01,0xf7f1d97603ffe3b2,0xec79ffc765d4a3ff,0x8ecb9913ff1d9721,0x3dffbc6ec07ffc76,0x5940fff8ecb112af,0xf61153437feaa2ec,0x78ffd545d49fffaa,0x8b990bff55172387,0xfeaa2ca3affd5458,0x8117fab099122ff6,0x055323dfec02a609,0xffd7654c01ffaf0a,0x981bff5d553257fe,0xba2a604ffd7354c1,0x1ffae4a9923ff5c5,0x5323ffeb82a609ff,0xd6854c0dffacaa99,0x2bff59153027feb1,0xaa608ffd6254c91f,0xfac2a991fff58153,0x25ffe3b2a64affd8,0x454c95ffaa8a9823,0xff60953247fec0aa,0x647ffd8054c1d7f8,0xf0a982fff1e15303,0xdfe342a64bffc685,0x4d11ffaa4bb01bff,0x54975297fea92e60,0x3ffd525c80dffaa4,0xb280fff54962037f,0xea92a683ffd515d8,0xebffaa2ba937ff54,0x573207fea8ae46df,0xfd5159471ffaa2b1,0x123ff54553417fea,0x82ec74ffd505d499,0xffaa0b98ffff5417,0x2367fea82ca37ffd]))
  | 10 => (OfNat.ofNat (certificateWord [0x3780200011c00000,0x42e0000003200000,0x1838290004f40000,0x0000000000c50000,0x002280000008c000,0x0000e00000312000,0x0000480000011c11,0x0000b4000001b700,0x0000498070006481,0x0800004000000380,0x000000e800000034,0x00000008024000d1,0x0000004b8000003d,0x0000000580080000,0x0000000460000008,0x0000000974000000,0x1400600011800000,0x0ec000000c800000,0x00b0680000c00000,0x004c000000260000,0x0001000000270000,0x0003401800020000,0x0010c00200012801,0x0006280000035a00,0x0002770000009a00,0x0001450008003820,0x000000c000000168,0x00000cdc00000008,0x0000003400800002,0x000000fdc0000026,0x8008000890000000,0x1800000000000000,0x7808c0001a000000,0x0500300000800000,0x022000000490bc00,0x0010000000300000,0x002e0000017d0000,0x000000000027c0e0,0x0007200000001000,0x000000000000bc0b,0x8000000000016600,0x2001578230000200,0x0000006000000400,0x00000018000000bc,0x0000065601800008,0x0040001e0010000b,0x4000000960000002,0x10000017700b0000,0x20000000061cc000,0xc500600003000000,0x13c020000a400000,0x0010000005184700,0x00a06480043a0000,0x01b4000000c38000,0x0064400000244028,0x001e300e00001800,0x0002943780014200,0x0000000000012480,0x000009c0000004a0,0x000002d000000000,0x0200005400000004,0x004000110000000b,0x8000000800d00019,0xc0000000b0000000,0x10490000280f0000,0x2a000000a2004000,0x8c8000000ec00000,0x3500000001300000,0x0020000000380280,0x000c0000003a0000,0x000200000048c000,0x0000000000014000,0x0007e8000000cc00,0x00004a0080001500,0xc000068000000580,0x0000156000000040,0x200002d800000314,0x0000004600000002,0x01200114800000c2,0xc000003c80000015,0x2014000078000000,0x005400019e004000,0x0400000042000000,0x024000000d600000,0x1790000000480700,0x0080000001460000,0x000b000000010000,0x004d80000015e004,0x0001500000005007,0x0000c40000007000,0x0000390040004e00,0x2000018020002d7d,0xa882c882ff5105d8,0xe9fea20ba933fd44,0x1731fffa882e46cf,0xf5105946ffea20b1,0x11ffd4415317ffa8,0x826400fed7258811,0xfdaa4b9003fb5c93,0x204ff6b126438fed,0x215886ffda40b10b,0xffb4813204feeb1a,0xe600fdd7354c01fb,0xae699023f754d322,0x47ee98aa630fdd31,0x4c88ffba60a98bff,0x74c1322df5eb0ac8,0x5aebd6059001f7af,0x0b201fef59176007,0xdeb22ea09fbd645c,0xc01f7ac8b916fef5,0xc5642d7deb82c800,0xfbd855900ff7ac8b,0x2827ef60d64007de,0xc12c85bfbd81590b,0x5f7b00b2037ef1e1,0x6403fdeb1ac807fb,0xd64588b7f7ac2b21,0x6bef5816403fde3b,0x2c809fbd6454cbff,0x7aa4b216fef54564,0x2d7dea82c85efbc7,0x5590bdf790ab217b,0xef19564007bebaac,0xa00f7d7554c13efa,0xcaa9823df5497536,0xfbea8aca6cf7d505,0x9401dfaecb2827bf]))
  | 11 => (OfNat.ofNat (certificateWord [0x2200021d01a03121,0x762e80000fc881c0,0x0011f48ce7f90000,0xa804d20000a98604,0xabe3c70000cb4d2a,0x4190001b74d165b6,0x07c037c6f619f000,0x18b800011a244855,0x8d385d303288c415,0x25f43c0000052811,0x91b6154cb2881109,0xb95c005056d2209a,0x5866466e24e8000d,0xc46d30000000b4a0,0x000e28984c045a13,0xd00c8071e6263318,0x0009ee65b0000000,0xe320bf0000618000,0x1a504f11dc7ae319,0x2d1172000056a264,0x8f7c74e7f2396046,0x0000072263914824,0xe41200010e06ea51,0xd1b28000eb629800,0x000000a456815919,0x58a6a1db0ef0000e,0x3a28b00008600004,0x2a037012c9f077f3,0x679478c386470860,0x0006580003340854,0x00045c31e0698136,0x3bc3070000e62666,0x0880000f8c733070,0x06806fe4fa0c100e,0xc2800a130d019869,0x200032419ac40053,0x800000000002ca3d,0x71ef000000026200,0x00ea0702271a0d85,0x1c41b202921c0420,0x1d3dd1eb019a0000,0xb892ec2482192c91,0xcd40000de1d18000,0x9026f100016c0000,0x7e33e1904c0005dd,0x06e8ed01aa115000,0x0000c4800000020e,0x8a9e00013f026800,0x00000000aec52657,0xf1869cc8dea14500,0x000006f03db33493,0x2000000030d8fcc3,0x281510f38e4c0000,0x0043282006ec6d14,0x1c85a064e21628e1,0xea000000000017e0,0x32a42d09c00003a0,0x05f3e615f418632f,0x0ad80d4fc041f2dc,0x9574f0c01f0001b8,0xc60c7293f800bcc8,0x067617a03285ee6f,0x734c800086a8243a,0xf89ac37c1a82eb95,0x384a40130001b5c7,0xde58800020200006,0x0127583ac0b20000,0x001344fb20000ba9,0xeb42981732b304d8,0x94c0000001a18180,0x24322b00004f6458,0x4081a989d850f377,0x0734dd880d3921b8,0x0b0a036000185874,0x8444000129c00000,0x0000164c9f277e00,0x0205905200033695,0x88fb455740399948,0xd885722d8b6c0008,0x5c0288000d660000,0x000e6429e0003be9,0xe7c8280003e58000,0x0000000000ddc8ec,0x8023608000000000,0x2228160b506a1013,0x000048222f0f1172,0x47e227901c063468,0x85192b61424e5e32,0x61698cb8cd40fa09,0x484ec07a25e00013,0x84de044e12c0000b,0xb45372df1164c0a0,0x003ef0000b0006a1,0xdb88284785d50cd8,0x0002546b533817c8,0xf705432ec0dac000,0x08a0000002200a00,0x0018000000049900,0x00ba034000d00000,0x01f4800000140000,0x00010000000a100e,0x0002d80700065400,0x0000240000003300,0x000009000000fc40,0x0000096038000000,0x000025f800000410,0x0000000000000142,0x0000007180a00046,0xc000000180000002,0xf000000d00000004,0xf004000068098002,0x4601e0000a005000,0x1c00000001000000,0x0100000000800000,0x015c018000140740,0x007c000001fd0000,0x0005c01000100000,0x0000100000004120,0x0001b80200021600,0x00000203c0017700,0x000000c000000000,0x00000880000001d0,0x0000007c028002fe,0x1940000000000001,0x00a000ae00080003,0xa0000000f00a0006,0x5000000010000003,0x52018002cc03e000]))
  | 12 => (OfNat.ofNat (certificateWord [0xf315400002263df0,0x00093e4262160eac,0x4ee86c3be0000bee,0x00016580005d63ee,0x3a191780007e520d,0x0ec83220000bd8d6,0xca4a04612b8000b3,0x019c3488ab8e8839,0x80d38b9058821f06,0x7a0240a86171e71c,0x1444a74a07a9db06,0xb86373ae836cb642,0x6c05980005586cd1,0xb41b600003330000,0x000cc400017d0000,0xfbe0000238261042,0x0000001f10ee61ea,0x0000e08db831e0c3,0xa140b16000132981,0x8dca59d077180c09,0xc5631e105e086062,0x32b896ec00079b25,0x416b00000fc1d000,0x0090a7203050434b,0x9c3f02f1a1b4d603,0x3a01989f05f82c11,0x9e1410ca40a33fd9,0xbe01561701c20fdc,0x00036e0720000000,0x0003f59d30bc87d2,0x00000000000002e6,0x00000006c3000000,0x10b40000528ec000,0x004a0000b7400000,0x03f080010286941a,0xa04a000000000000,0x6800000000001687,0xc87e832a80009081,0x093e01b480005112,0xbd8870c5625c0f19,0xa6cec600000001c4,0x7540000001a48000,0x03c0000000a043e7,0x15286c0e18000061,0x170000025122e856,0x00000000a687d4c5,0x81172da00004fe00,0x011f00410c03d01f,0x4967c6487a50f280,0x003b800019296f4c,0xa86191a81154b3c6,0x713c793b45b83221,0x8c08401fa38919d9,0xf24d9c8180001508,0x0007571569bd8148,0x4820441820000150,0x0001734000000278,0x0000a8819d00019e,0x41c600014a8c0400,0x086709e00010440b,0xc1a2902882c23000,0x015f8eec56000013,0x0105e0000000d440,0xde7d536f911858e1,0xd33c4065c6e084e2,0x7393f82647d41c91,0x40007207e2059fd4,0xd264c12880c404c0,0x3b929d0ec4000506,0x0001de00000002f4,0x0620b5a0000001fb,0x85ac5af3ba1c5cd8,0x41a30999e34f6c25,0x4128000096412b07,0x303944c62682908d,0xa82c276513712540,0x000af00020280005,0x391c08bf46840000,0x0008080000000539,0xb400005ea0000000,0xcbe78a33016c4028,0x0003c800003d8000,0x3b3092c2d63f63f6,0x913105c283119845,0x03a40001e2851c00,0x07cd3f110c8b1a00,0x011e84940d627a07,0x81b50e0e67431796,0xb855451b29700908,0xbe3860000000f185,0x8e00018e80001ed0,0x1103c42400b71351,0x2309d44d04218000,0x0b671e1b18000000,0x708299a0648663d8,0x1060ae80fe000407,0x8bfc5ae6a20eb000,0x00004430001bc801,0x20a217400008a200,0x019f00001b200038,0x50f449d02402c186,0xb8e6c7471751fd8f,0x160001f182589982,0xd9182187c6c80001,0xee92280000640c70,0x1040d800040995e8,0xdbc00010d9250000,0x1a24018fe0000083,0x00021782004e53ff,0x1f40eb24212ef06d,0xd02e7f30e50d5888,0x083717a9cc006200,0x015b00005be3a100,0x00000cea1b300003,0xa451e00f15f8d4c0,0x003d514909d40007,0xb5000000095a47e3,0x5c97701a04db3fb9,0x1802d83670001750,0x0000001e91318f62,0x6e11de93d03420ad,0x16d000067a000000,0x173cf0653632e9f1,0x4eac70e14684987b,0x40002009ca012010,0x129a133cad646d39,0x187080007c700000,0x00b2e4fd2748b60b]))
  | 13 => (OfNat.ofNat (certificateWord [0xbac000000180020a,0x2f31578db43260cc,0x0001964e1a5ee2b2,0x9690c9c35700010f,0x0d6c85b1149910d7,0x400043708d09e655,0x621118542cc61439,0xf97b0d482421701c,0x9d02421442698cc8,0x905e52d989bc62a0,0x0834289b444e0002,0x4781080000e81a40,0x8accf840309f8000,0x0002d1431952c416,0x53d122137cc8a687,0x00003dc000631033,0x9834542000161800,0x00000000000000b4,0x078400000009ae00,0x02cd8a78fce6291a,0x905749706a73a790,0xece241f8000177ce,0x766da00007004400,0x001d6042c9b44503,0x6292d4ff00003881,0x3610942a633ba0b0,0x0000002840ecc722,0x1bb30583385e0000,0x01395302864253b5,0x046c1b07c10000b4,0x00001b418f9d4cc7,0x63dc3b813808a62c,0x90ba071c00e5ed3d,0xd83ec8f800017886,0xf44be18f02817e44,0x2e1cb1d30e949620,0x0000019240008583,0x1e80000000430001,0xb3080e40f171989c,0x6b442332c000061c,0x1fe022800099a567,0x31908a86b0112097,0x9f0836201816a0c7,0x45c22ab2d31d0000,0x06a5000000000077,0x538e1dc847e40c15,0x1800000068f02e1b,0x989847113ec17140,0x0043d10193b841a2,0xc60171da40000000,0x0019e000082a1111,0x6dc5487b3434a094,0x0006d50898000d5a,0x79636b1dbc0006c6,0x2c61a80058302000,0x0ad41de6ab20a800,0x02c000017482a073,0x607b000000000000,0x00b51ab89420cb09,0x097807188340000e,0xfca2c2c803e12f08,0x483c60b18e34e120,0x0022d04b0aa44063,0xb6834c66a14e3469,0x45cf440b120118a8,0x8928231be062c11e,0x0700c20bf8b147ef,0x3a086f00003cb076,0x9c682841160f7000,0x0e9200002217185c,0x458f1e00000ff41f,0x000003c8eb400003,0x106bcb0e4340000c,0x144e01a40000578c,0x1853f31415c80187,0xd1140a14849412e1,0xfc8ee058a34b0000,0xc8462e2a719b0ea1,0x02a6571e99c0cbe6,0x67e0ec80000002e5,0x424831810868805e,0x87602e486a3eb122,0xc5f00d142a85bc0e,0x852a10916241e817,0x71a601d8f300ec00,0xb111cbc27821611f,0xf42620b60f41b647,0x1675205d8c483344,0xbf14387e837206d3,0xb100000001671ca9,0xf2062842e21f8000,0x0003be20497bc1a4,0x76735b827400040e,0x0bc9584a561fb0ac,0x95004584b70011e1,0xc0003eb3410000cc,0x84bd3c48d7c0004a,0x213880000007ca00,0x011c0bf400000000,0x00e004783390000b,0x4621d00012682946,0x8a00000fcf726730,0x0019442746c81e61,0x15083a69f0c50f94,0x1281020058cfcc1e,0x1f30000a88ec87bf,0x0000ee838678131a,0x00006d26500e70d0,0xcba223807f878000,0x000023da0c50401d,0xf11680008ae7613f,0x5051873402b3d09f,0x4c5f63cd18b04743,0xd281b0029c18d526,0x350002130c7e0003,0x100be4fb81eb0489,0x040a8c39706410bc,0xc447b44239c4c332,0x4630000000000697,0x000138886207527f,0x8a100007b2237800,0x0ee24ae000201081,0x07ec3822018e2834,0xf41e92f85ce00001,0x80f3c0005cb1951b,0x240bc33911089180,0x9a66f21391a818a0,0x002d494887d85233]))
  | 14 => (OfNat.ofNat (certificateWord [0x1b11aa0c7c02a0b2,0x8a68f540ac10308d,0xcb320001c3800002,0xe0002390acc07c11,0xc1838fd475c00030,0x994600147db2730a,0x14000000091a1bc2,0x723281b885b8aa20,0x001fe00000003740,0x000e580000001320,0x00013e00037d8b54,0x0005e6431093c2f8,0x03a2ed9d185362f2,0x07396689a430a21c,0x8b48ed60a008f000,0x1034000083800065,0x23b621f0238af083,0xb133024c4121cc39,0x680006265820c91a,0xbc1026c42ff02281,0x6a00e1ef1e8c6002,0x5a09a80000002a90,0x0012b0ffe1ff2388,0x9d00000a626983f8,0x000000000000025a,0x0003fa0e21018000,0x0001c0400039d0bf,0x00004f044f06d190,0xccfa0002ba8000be,0x05fc0001c945d825,0xb049101035a3082a,0x494c890c2cc0bf9e,0x5c0000250000000f,0x2a00037a0c705100,0x8739b80003f20000,0xa480003ae0000000,0x010a940000d50488,0x52e09711206d4bec,0x49217b1438000000,0x3c70d7468285605c,0x156c968000148993,0x00c60003208000b8,0x861103e89543ba00,0x026a997094883304,0x10dcc98639f00015,0x7099c85d2868a245,0x723ea3c886c85048,0x6820691d48e60000,0x0009d81740002e38,0xa3000000023c8568,0x0002471d494b0de6,0x81e0871188d7e000,0x40e8b002100ea000,0x0798dd4000298931,0x4aaa4de10f135908,0x267f000083859e6c,0x02890f0cc9400021,0x580004102900000b,0xbc37400003b81589,0xa865307b0bb40008,0x4b109a1501604931,0xbe937106049e0e89,0xa243060000001520,0x12a2cd0f88d346de,0x68024d85100ae24e,0x0e30000ac86db2a0,0x8000000792250170,0x4f2879d2b49a0c70,0x0490000146800000,0x00e498601e639c0f,0x79a38c840000001c,0xe0a2a4f131680004,0x4679e1c29d500001,0x960fe00780004363,0x9c83e453823b0000,0xadc5780003d3125c,0x97239424c0ad0000,0x02d37e8001084000,0x390a09909e111310,0x8790cf404c41a84f,0x400000027b1db882,0x269a28a0d1800049,0x9087806c7a835e12,0xb0000dfc85100014,0x1ca027602f891850,0x7e6b400006403ec3,0xc103d0000e9a0000,0x001a780007421580,0x0000223fe0000000,0x5dc00003c149ca76,0x7a71671498382232,0x0820ffc40252413e,0x9cb895475c42218d,0x845c84523484d066,0xe32b2899a3086e66,0x739e15dc1b81e135,0x51134a8a0002dc00,0x00b843e62c30174d,0x62103400178908c6,0xc738a80010c22b12,0xf49bac0404a53d58,0x00039e1542c2112c,0x00016d4058c2c6cc,0x7793db97acbea000,0x41391fc15c00029e,0x00006fc0003650ee,0xc78817d0000a2802,0xa08b00008a0f484a,0x33c98d1ced032300,0x00000c6000000005,0x04a5e5d209f0d006,0x0634a38f9ff00381,0x8033d9a106c24280,0x0000008f45290001,0x3d48c80290000000,0xeb07851ac80004a6,0x0003a419782be0aa,0x4169258ea2099000,0x1c9905007929f1d1,0x4884000000127106,0x464b3519194e1e00,0x034c01200002e63a,0x717fc7921d401a00,0x003ee57c25b0e780,0x000000000fd10a65,0xc3000198453a3c81,0x261d542f486b2940,0x0009100000002190]))
  | 15 => (OfNat.ofNat (certificateWord [0x38a37416540,0x0c0032470c444e61,0x9803487d055031b2,0x8516f020c0000001,0x000b7e0003748934,0x0006bb000000100a,0x3f21c81bfc492000,0x19c17290902b8000,0x0d387f400034e8af,0x8500000255800023,0xe44a0a412cc83800,0x0214a19897464d38,0xb086800073e29688,0x108dc00042c89c84,0xba7ce01b80001380,0x002b71568dc88380,0x0018402c815c20f0,0x554ef60000430000,0xd2083e000055ce16,0x2450fe82f8318334,0x2ac12440000d71b0,0x1a047c075e124132,0x8a1847414c8000a6,0x020f37c80040c229,0x60dc15e44721c838,0xc0310bb22350e20c,0x686e426718615340,0x9e7cf4070f880004,0xcb000193cd780b22,0xce00000000000461,0xbb4dde0000001968,0x11a4803038304000,0x0003ee86ac000604,0x2f38754d7c61d02a,0x8180906000000000,0x095e0e20a91ae0c4,0xa6b228286140000d,0x44201cd075a00028,0xf8000f3861e1aa93,0x64c707af2ac8fb4e,0x960002a380c81720,0x0025806fcae610a0,0xb48fa0ef430f3f48,0x81ce7448d10286d8,0x0000003cc8768000,0x3b53d80000b4e420,0x0429824bfa4fb000,0x1ddc8d057606b038,0x4d585ab098000075,0xe4fc15e939008000,0x02cb20045bc38e14,0xf9b2c0006fc28196,0xa8a1641729000000,0xe66fa0000de48305,0x5430900480320231,0xc18c24fe23fd42f8,0x0003e421140f9578,0x6f400000000007b2,0x0003de80004b2639,0x198000046c66c000,0x1f5d0780001f0898,0x83525903cd13c895,0x228600002d0ae800,0x023308e89de6bd00,0x0031c7ac72a02996,0x04dce3312fd80000,0x006462358124b6a5,0xba00000007940000,0x001cac1120003910,0x52c7443fb0001cf4,0xade00d26e8678358,0x7a938d858819282b]))
  | _ => 0
def g17K8 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0xef74ca7854d4fbbd,0x649e15353edf5967,0x854c17d7e785d553,0x05e7f5e67854d3d9,0xfd759e15352e7f5c,0xe7854d4b3ff975e1,0x53546fdc427854d4,0xbbdf329e15352e7f,0xdce7854d3d9ff759,0xe15305e7f9e37854,0xd3db7e659e153556,0xef9927854c0f3fc6,0x99e153287d79d573,0x54cbddbe75591759,0x46efe1d645d50fe7,0xe755d9650375fe5d,0x755965377c599e16,0x543edf9d568dd40d,0xd7f975d55393ddfe,0x5d7554d493fc599e,0x153286df9d538dd4,0xc9fb675e05646277,0xb9d7825d589bee75,0xe0975006f79d7835,0xd90fb7e75e157628,0x6df9d7855ccbdf3e,0x75593752f76f9d56,0x4dd501bee74e0975,0x45ef79d3835d80b3,0xfc499e16502cff12,0x67854c15dee785c9,0x32057779e1734c81,0x59ff975e1324ecff,0xe5d784c883fce735,0xc9323bfd79cd7554,0xc09ddf975cd5391d,0xf7e5d7354cefbde7,0x35637302777e5d73,0x4ca457df975cd324,0xe4ff0e67854cc5fb,0x673e0564006fb9cf,0x825d4efbde73e0d7,0x5024ff0e6785949d,0xfce725cd32427bb9,0xc97658807def975c,0x9628fdfbe5d72589,0x09bee725a37201f7,0xbe5d724ca3d7ef97,0x5c932276fb9c938d,0xc8b9dbe725917290,0x6efe1d645c8c7fb6,0x72e0564426fb9cb8,0x25d89dbee72e0973,0x2e7eb9c964dc8b9d,0xbe72593726a6f79c,0xb835d8073fc299e1,0x6501cff0a67854cf,0xfbee71e0975456f7,0x9c7835d8053fc199,0xe165014ff0667854,0xd71fb670e05643f6,0xfb9c3825d513bde7,0x0e0d7600cff02678,0x594033fc099e1535,0x8cff82678595513f,0xe099e153584ff866,0x785942ffb679e056,0x454cff8667854d5f,0x3fe299e1650beefa,0x25645c80f7ee965c,0x96203eefa19645c9,0x593fe79e09764fcf,0xf8a67854c777ee95,0x5c962195fba55724,0xc8bdbbe855917262,0x77b9e7825d589bee,0x79e0975025fba4d7,0x24c8bbbbe8359172,0x4ecff9e7825ccb7b,0xbe81591722d6efa0,0x1645c94f3fe399e1,0x6525df7a597354c6,0x77de965cd3269777,0x9e7835d9a5bde79e,0x0d76035f7a557354,0xd4b3fe399e15301d,0xf7a49734c80f3fe9,0x65e132034ffa5578,0x4c80b3fe945e1320,0x14ffa45784c8033f,0xe905e132004ff926,0x78595553fe499e15,0x30beefa25645d40f,0xbbe865917503ddf9,0x66785955d3fe599e,0x165006fba1b825d5,0x01bee84e09752eee,0xfa0d645d40977e93,0x5d553024ff966785,0x4c01bee83e09752e,0x6efa09645d4dd77e,0x925d5652deefa056,0x45d4ffbee81e0975,0x2d6efa01645d4fdb,0xee80e097503cffa5,0x97854c0b3fe945e1,0x5301cffa497854c0,0x53fe915e15300cff,0xa417854d4f3fe699,0xe153035bf9a67859,0x40d3fe699e165006,0xf7a17835d917bde8,0x4e0d7601dbfa4976,0x588073ff98609766,0xa6f7a0b835d915bd,0xe81e0d7644ef7a03,0x835d80d3fe955e16,0x202cffa517858809,0x3fe935e162014ffa,0x4578588033fe905e,0x1622f5efa5578590,0xbb7be935e1642e5e,0xfa4978590b77be91,0x5e1642d5efa41785,0x900b3fe945e16502,0x4ffa4d78594073fe,0x925e165014ffa457,0x8594033fe905e165]))
  | 1 => (OfNat.ofNat (certificateWord [0xb9a1724c813bde68,0x5cd32634ff9a538d,0xc9cb3fe694e37561,0x6f798d38dc9c5bde,0x634e3755a7ed98f8,0x159001bee63e0975,0x024ff0e7865d4093,0xfe935a375277f398,0x9734c8b9fae62591,0x7201fbbe19725889,0xdbee625e1328eefb,0xe19725892f3fe925,0xa3725a7ed98b8159,0x109bee62e0976696,0xf798b835d8073fc2,0x9e197501cffde568,0xdc80d3fe955a3720,0x1cffa4968dd40b3f,0xe945a372024ffa4d,0x68dc8ffbee61e097,0x5696f7987835d805,0x3fc19e1975014ffa,0x4568dd4053fe915a,0x3725a7ed98381590,0xfdbee60e0975696f,0x7983835d8033fc09,0xe197500cffa4168d,0xd4033fe905a37279,0xcff827865d5e53fe,0x19e19755b7ad9a78,0x15916dfb669e0564,0x77cff8a7865d431b,0xee69e0975634ff9a,0x7825cc1dbef785c9,0x6262eef9a164dc81,0xdaff785d962076bf,0xe5968dc9d73fe69e,0x09763d4ff8e7865d,0x595ede69e0d76696,0xf79a7835d801bbf8,0x959175084ff92786,0x5d4c3bbf89591723,0x07ee42778591e9fb,0x510de164307ed467,0x78591ebebd61de16,0x47a7af58378590c1,0xebd69de164306ef6,0x2778591ebdbd71de,0x1647a76f5c378591,0xdb7bf985e1643076,0xfde778591ebfb719,0xde1647afed207785,0x91e9fbb09de1647a,0x76fdc378591b5ebf,0x60de1647a7edc437,0x8591ebdbf71de164,0x0bfede0778591b5e,0xbf61de16476fafe1,0xb78591dbbbf86de1,0x642f6efa15855914,0x77bf9861564327ed,0xa1781590bd7bc59d,0xe164317eda0f8159,0x0bb7bc39de1642e6,0xefa0982591317bf9,0x86096431feda0b81,0x590b97bc29de1643,0x96efa0585590b77b,0xc19de1645c7eda03,0x81590b57bc09de16,0x47a5ef82778591eb,0x7be19de164305ef8,0xa778590bd7be9560,0x9642edefa4d82590,0xb77be91609642d5e,0xfa4182590c17be39,0xde16472cff9a7855,0xcdc9bbe685937507,0x6dfde1755941db7f,0x9556376076bfde17,0x65941daff965a375,0x774ff967865d41d9,0xfc78de1657779f19,0x778594e17be941e1,0x6537df7a4c78594d,0xd7ee921e16536dfd,0xa4478594d97fa901,0xe165305ef9677859,0x0bb7be93615642e5,0xefa4985590b77be9,0x1615642d5efa4185,0x590017be79615645,0x8efd442785954dbb,0xd649e1650075f5d6,0x785954fb7d539e16,0x50073f5da785955f,0xafd629e1650067f5,0xe2785954d9fd769e,0x1655767f5d678595,0x5d3ff891e1655779,0xf1967859563bf710,0x9e165536bfd8a785,0x955db7f539e16557,0x67fdd6785954d9ff,0x769e165536ef9927,0x8594019ff789e165,0x005ef9e5825901bb,0xbe786156406eef9e,0x1825902fdbe785e1,0x6456defe5d785902,0xffb678e0564306ef,0x9e3785902fdbe78d,0xe1640677b9e17258,0x819cfe785d962066,0x7fe5d78589355ff9,0x760976564ffe5d78,0x58889eee765c9623,0xcf9f9d9755940fcf,0xf975d96595dbf1a6,0x785940fcff975d96,0x2955bfe5d7658957,0x3fc699e1653cebf9,0xd958dd969fb676e0,0x564006fb9db825d5,0xa5dde76e0d76696f,0x79db835d8f3afe76,0xe1975546fd442785,0x4c17dde785cd534f]))
  | 2 => (OfNat.ofNat (certificateWord [0xe7855ccc5fb653e0,0x564626fb94f825d5,0x85bde53e09733bef,0x794f835d4093fc39,0xe15762eeef0e164d,0xd4093ff795637303,0xcffda558dcc093fe,0x935637602cffa515,0x8dccb9fae5259172,0x8df9f94976594c7f,0xb652e05646a6f794,0xb835d8073fc29e15,0x7601cff0a7855ccb,0x9bbc285937501cff,0xa4958dd8073fe925,0x6373626fb947825d,0x515bde51e0d76014,0xff067855d8053fc1,0x9e15732deef06164,0xdd4053fe91563760,0x14ffa4558dcd71fb,0x650e0564626fb943,0x825d513bde50e0d7,0x600cff027855d803,0x3fc09e15732d6ef0,0x2164dd4033fe9056,0x37600cffa4158dcd,0x213fe09e1576734f,0xf827855ce75bbe08,0x5937547cff867855,0xd9cf3fe19e15739d,0xeef86164dd42ffb6,0x59e0564444ff8a78,0x55d8a53fe29e1573,0x306ef8a164dd579f,0x6e59e0975626fb96,0x7825d5cb3fe39e15,0x760d6f7967835d81,0xdbdf785cd53076f7,0xe4d38dd4c1bbe385,0x9375076dfde17554,0xc1db7f9556373714,0xff8e7855cc1d9fc7,0x8de153717d714f78,0x54c253fe49e15767,0x44ff927855ccf53f,0xf965e15379efd443,0x865d4f3bbd64e197,0x50879fe5975594f5,0xb7d53e1975086bf5,0xa7865d421afd76e1,0x975776bf597865d5,0xe79fd70e1975774f,0xf9a558dd9e79ff70,0xe197579efdc43865,0xd431bef86e097577,0x6dfd4f865d5ddaff,0x65e1975007afe597,0x8591db6bf965e164,0x76defe59785908b3,0xff965e13207fbbe5,0x9725888b7ef965c9,0x32226efe19645c81,0xfaff965e16207dbf,0xe59825d9d73ff965,0xe16204f77dd97354,0xc13ddf765cd32076,0xbfdd968dc81daff7,0x65a37574cff1e786,0x5d569fb776e05645,0xe6fbddb825d595ed,0xf76e0d76696f7ddb,0x835d9476bf966156,0x40cfafe598559147,0x7bf966156404ef79,0xa17354cf5b7e685d,0x5533d4ff9a558dcc,0xa1f5e655cd532f7c,0xf995645d40de7f86,0x5d565286df995785,0x4e4db7f865d56568,0xedf99558dcdddb7e,0x6556376514ff1678,0x65d569fb665e0564,0x627db997825d589b,0xee65e0975696f799,0x7835d9a3b7e65e0d,0x7543edf997855d80,0xd3ff795a3754c5af,0xe59825902debf966,0x09644c5efe598259,0x1fdfae645c9627d7,0xeb991724ca0bf9e6,0x45cd5380fe799173,0x4ca29f3e645d5658,0x77cf9917554d0deb,0xf865e1643c7afe59,0x645d485ebf965917,0x2387afe198559075,0xebf86609643ceef9,0x91785950dbbf865e,0x164226ef99178588,0xfbbbe645e15392de,0xfe59645d4abbbe64,0x5e132925efe59645,0xc8e1bbf86615641d,0x6efe19825918bbbe,0x645a372726ef9916,0x8dd4fbbbe6456373,0x3ceef99158dd8abb,0xbe644e372746ef99,0x138dd56deb786e05,0x645b6ede1b815916,0xdfb786e056462eef,0x993825d801fae64e,0x0975006eb993825d,0x501bee64e09752ae,0xef993825cd87ebf9,0x65937299defe5964,0xdc9a5f9e64e0d766,0x96e7993835d9a5bd,0xe64e0d763eeef993,0x835d5c9bbe64e157,0x6746ef993855cdc7,0xebf96593759e5efe,0x5964dd4f3bbe64e1,0x97502cff127865d4,0x0b3fe945a37522ef]))
  | 3 => (OfNat.ofNat (certificateWord [0x38dd501bef43e097,0x545ef7127835d80b,0x3fc49e0d7502cffd,0x2538dd407fcf835c,0x9322e7eb8c9645c9,0x09eee325d962426f,0xb8c97858a39bef83,0x5c9324b4ffa4938d,0xc8c7fb632e056427,0x6fb8cb825cda9bdc,0x29e0d7601cff0a78,0x35d4073ff794e372,0x03cffda538dc80d3,0xff594e37201cffa4,0x938dd40b3ff494e3,0x723fefb8c7825d51,0x5bdc19e0d76014ff,0x067835d4053fe914,0xe375014ffa4538dc,0x971fb630e05643f6,0xfb8c3825d513bdc0,0x9e0d7600cff02783,0x5d4033fe904e3750,0x0cffa4138dc835bd,0xe09e0d763dcff827,0x835d5afbde19e0d7,0x63e4ff867835d56b,0xfb639e0564634ff8,0xe7825d835bde29e0,0xd7669cff8a7835d4,0x31bee39e0975076f,0xbde1724c81dbdf78,0x5cd32076f7e4d38d,0xc8c1bbe385937267,0xcff8e7825cc013ff,0x945e165474ffe517,0x858835bdf84e0d76,0x3ecffe517854c31b,0xef84e09752acffe5,0x1784c979bef74e09,0x75656f7dd3835d91,0xd3ff945a372094ff,0xe5168dd401bef64e,0x0975696f7d93835d,0x8fb3ff9456373084,0xffe5158dd989bef5,0x4e0975006f7d5383,0x5d8ab3fe494e3727,0x44ff92538dd401be,0xe43e09756a6f790b,0x835d8ffbee41e097,0x5456f7907835d8fd,0xbee40e097544ef79,0x03835d91d3fe49e0,0x9760c6fb927825d4,0xab3fe49e09730d6f,0x7927835d8fb3fe49,0xe0d75005efe55785,0x91113ff955e16248,0x6fd443855d9c9bbd,0x64e15760979fe557,0x659425b7d59e1576,0x096df5d7855d9c9b,0x7d65e1576446bf58,0xb855d9219fd70e15,0x7643cffe5568dd52,0x19ff70e1576486fd,0xc43855d9c9aff62e,0x15760d6f7e17835d,0x8a53ff955e132736,0xfd443855cc23f5f9,0x55cd53296f74cb85,0x5cdcbbbd64e15730,0x8edf567855cc23b7,0xd75e1573716df54f,0x855cdc53fe594e37,0x5736fdc43855cdc5,0xbdf32e1573716dfd,0x4f855ccbfbbf8559,0x1729d7ed44164dd4,0x11def755c9620477,0xbdd5724c8c1f3d58,0x593759dfaf58564d,0xd675ebd60593752f,0xf6f5c964dd675dbd,0x70593759d6efe156,0x45d4bddbf7859375,0x076dfdd558dcc1db,0x7f75563766fcff1e,0x7855ce77fb491593,0x759d76fdc164dd67,0x5ebf60593759d7ed,0xc4164dd401fb7915,0x93759dfafd8564dd,0x579f6f75e0975626,0xfbdd7825d4c1dbf7,0x259375656f7dd783,0x5d8bf7bf95609640,0xbfcfe15855901bbb,0xf855e1642feefe15,0x82591bd7bf956156,0x40bfede1781590c1,0xbbc9859375046fbe,0x157258911aff855d,0x962444ffe5568dc8,0x89eef655c96203f9,0xfe157659489aff65,0x5e1629cebfe15765,0x958baff655a37243,0xebfd9568dd5bb3fc,0x69e15765a7edd978,0x15918baff65e0976,0x626fbd97825d5a5e,0xdf65e0d76696f7d9,0x7835d80f3fc69e15,0x7303eef1a164dd45,0x33ff7956376626fb,0x953825d517bde54e,0x0d7602cff127855d,0x80b3fc49e157302c,0xffa5158dd811bee5,0x85c932296f796173,0x4c8a53fe594e3722,0x0ff394d724c809f5,0xf855cd5320ef794d,0x784ca43bdf855cd5,0x3616f794d38dc9c5,0xbde534e3754dcff0]))
  | 4 => (OfNat.ofNat (certificateWord [0x5d801bdd84e0d760,0xdef760b835d9afbd,0xd81e0d76006f7603,0x835d9a4fdd76e0d7,0x6006f75d7835d801,0xbdd74e0d7665ef75,0xcb835d9afbdd71e0,0xd76006f75c3835d9,0xa5bdd79e0d76696f,0x7597835d9a5bdd64,0xe0d76696f758b835,0xd9a5bdd61e0d7669,0x6f7583835d9a5bdd,0x69e0d76697371db8,0x35d9a5edc76e0d76,0x697771db835d9a5b,0xdc76e0d76006f755,0x3835d801bdd52e0d,0x766bef7547835d80,0x1bdd50e0d76006f7,0x567835d835bdc85e,0x0d76656f71d7835d,0x9a5bdc65e0d76006,0xf750b835d9afbdd4,0x1e0d7649ef750383,0x5d801bdd49e0d764,0x5ef7213835d995bd,0xc74e0d76696f7193,0x835d917bdc54e0d7,0x642ef7e27835d90b,0xbdf79e0d7642ef7d,0xa7835d801bdf59e0,0xd7645ef7d27835d9,0xafbdd21e0d76006f,0x7483835d837bdd29,0xe0d766a6f720b835,0xd995bdc72e0d7669,0x6f718b835d9a9bdc,0x52e0d7645ef710b8,0x35d9a9bdf29e0d76,0x6bef7443835d9afb,0xdd19e0d76456f720,0x7835d995bdc71e0d,0x76696f7187835d91,0x5bdc51e0d76456f7,0x107835d915bdf19e,0x0d76456f7087835d,0x801bdd09e0d7644e,0xf7203835d995bdc7,0x0e0d76696f718383,0x5d913bdc50e0d764,0x4ef7103835d913bd,0xf09e0d7644ef7083,0x835d913bdc10e0d7,0x60d6f7e03835d835,0xddf70e0d76656f7d,0xc3835d9a5bdf60e0,0xd76006f7d43835d9,0x17bdf40e0d766a6f,0x7c83835d9affd710,0xe0d766bef5c43835,0xd915bdf10e0d766b,0xef7e07835d9afddf,0x71e0d76656f7dc78,0x35d9a5bdf61e0d76,0x6bef7d47835d9afb,0xdf41e0d766bef7c8,0x7835d913bde10e0d,0x760d6f7e0b835d99,0x5bdf72e0d76697b7,0xd8b835d9a5bdf62e,0x0d76006f7d4b835d,0x917bdf42e0d76456,0xf7887835d913bde2,0x0e0d763defd44383,0x5d421f5f935d5530,0x86f74e7835d421bd,0xd73e0d7568ef754f,0x835d4f9bdd31e0d7,0x53def74c3835d4f5,0xbbd64e0d753d6df5,0x97835d4ef3ff9356,0x3733bef718f835d4,0xefbdf30e0d753def,0xdc43835d4efbdf31,0xe0d750c6fbe0f825,0xd41ffcf935c93222,0xdfbe4d725881fbdf,0x935e13222eefe0d6,0x45c99f3ff935e132,0x076f7dcd38dc81db,0xdf734e37504f3fdc,0xd7659413cff735d9,0x6266cff1e7835d56,0xbfb773e05645e6fb,0xdcf825d5a5ddc79e,0x0d76696f71e7835d,0x8b17bf93615643d6,0xdfe0d7559413aff8,0x35d9651adefe4d82,0x590d3bbf835e1645,0xafede0f815908bbe,0xf835c96204ebfe0d,0x76588013df935a37,0x20d6f7e4d68dc98d,0x3ff935a372004f7e,0x4d68dd435bdf935a,0x37572cffe4d68dd5,0xf7fcf635c93287fd,0x7d8d7554cf5bdf63,0x5637362ebfd8d68d,0xc9c9aff635a3755a,0x7edd8f8159001bef,0x63e0975697b71a78,0x35d9a5bdc69e0d76,0x3d6f7d8f835d40f3,0xfc69e0d753d4ffe4,0xd58dd80df5f835d5,0x532f7cfd4d645d50,0xfe7f535d96543edf,0xd4d785966db7f835,0xd5533bedfd4d58dc,0xdddb7f535637664c,0xff167835d4c9fb75,0x3e0564627dbd4f82,0x5d589bef53e09750,0xd6f7167835d84b3f,0xf794e37503cffda5]))
  | 5 => (OfNat.ofNat (certificateWord [0x579bec71e09753fe,0xfb187825d589bec5,0x1e09753fefb10782,0x5d4ffbec31e09753,0xfefbc67825d591be,0xd09e09753f6fb203,0x825d579bec70e097,0x53f6fb183825d589,0xbec50e09753f6fb1,0x03825d4fdbec30e0,0x9753f6fbc27825d4,0xfdbec10e0975646f,0xbe03825d591def70,0xe09755e6fbdc3825,0xd591bef60e097562,0x6fbd43825d591bef,0x40e0975646fbcc38,0x25d591fe710e0975,0x646f9c43825d591b,0xef10e097563efbe0,0x7825d579bef71e09,0x7563efbd87825d58,0x9bef51e097563efb,0xd07825d58fbef31e,0x09753f6fb843825d,0x4a7bf510e097308f,0xf3e49734c823bed2,0x9e097307efb5cb82,0x5cd85bed32e09732,0x9efb483825cca5bd,0xd53e0973636ef593,0x825cc9d3ff924e37,0x2276fb14b825cc9d,0xbef20e097329efdc,0x43825ce5dfb51059,0x372307eb4a164dca,0x5dfad205937297fa,0xf58564dca5debd60,0x593722ff6f5d564d,0xca5dbbf825917204,0x75fdc97559411d7f,0x725d553604ff1e78,0x25ccb9dbf7859372,0x2e7eb14964dca5ff,0xb49159372977afd8,0x164dca5dfaf20593,0x72977edc4164dc80,0x1fb7915937297faf,0xd8564dc989dec79e,0x0975626fb1e7825d,0x4bf7bf9261564046,0xdfe097559511aff8,0x25d9650bfebe0982,0x5901bbbf825e1642,0xfeefe09855917f7b,0xf92609640bfede0b,0x81590c1bbc985937,0x2444ffe4968dd40f,0xeef825d9623cf9fd,0x8975594f3aff625e,0x16596ebfe0976589,0x09aff625a372726b,0xfd8968dd57d3fc69,0xe09765a7edd8b815,0x9031bec69e097503,0xcff1a7825cc0fbbc,0x6859372296f7e097,0x354c11b7f825d553,0x004fbe4958dcc31b,0xef925637369cffe4,0x958dcc013ef92563,0x760c6fbe4958dd9d,0xf3ff9256376817f3,0xd49734ca31eef525,0xd962446fbd4968dc,0x8a5bef524e3722f7,0xcfd49645d5a3b7f5,0x256373776dfd4958,0xdd8c9fb752e05644,0x46fbd4b825d989f6,0xc59e0975626fb167,0x825d4a5bef52e097,0x3987ebd4964dc80d,0x3fc59e0976034ff1,0x67825ccbdbbc5859,0x37202cff127825d9,0x01bec49e097502cf,0xf127825cca53ff92,0x4e375027f3e09734,0xc8eff5f325d5533b,0xef7cc97854e59bdf,0x825cd32276f7cc93,0x8dc9c5bdf324e375,0x5dcff0e7825ccc5f,0xb732e0564024ff0e,0x7825d831bec39e09,0x752eeef0e164dc80,0x53fc19e09763fefb,0x067825d4053fc19e,0x09732deef06164dc,0x971fb620e056400c,0xff027825d8fdbec0,0x9e097500cff02782,0x5ccb5bbc08593724,0x64ff827825d991be,0xe09e097529cff827,0x825ce5dbbe085937,0x246cff867825d98f,0xbee19e09752a4ff8,0x67825ce5fbbe1859,0x3720bfed8a781590,0x01bdf935e165005f,0x7e4d855d8017df93,0x61975004f7e4d785,0x94017df935e1653d,0x4ffe4d7859401f9f,0x935e164005e7e4d7,0x8590d37bf935e164,0x0def7e4d78588377,0xdf9360976004f7e4,0xd785888b3ff935e1,0x62007f5443835d80,0x1bd510e0d76697e7,0x593835d9a5b9d64e,0x0d76007b7597835d,0x837edd62e0d766bf,0x775c7835d801ddd7,0x0e0d76006f761783]))
  | 6 => (OfNat.ofNat (certificateWord [0xffb478e05645a7ed,0x58f8159169fb562e,0x05645a7ed5838159,0x0b7fb569e05645a7,0xed1db815916bfb55,0x3e0564337ed54b81,0x59171fb550e05640,0xbfed56781590c9fb,0x475e0564327ed217,0x8159169fb465e056,0x45afed4cb8159171,0xfb530e05645afed4,0xe781590c5fb473e0,0x564317ed20f81591,0x69fb463e0564317e,0xd14f8159171fb520,0xe05640bfed4a7815,0x90c7fb472e056431,0xfed20b8159169fb4,0x62e056431fed14b8,0x1590c7fb432e0564,0x0bfedde781590b7b,0xb789e05642dfede2,0x781590b7fb769e05,0x64327edd6781590c,0x5fb739e056431fed,0xca78159171fb509e,0x05645c7ed1c38159,0x171fb480e05645a7,0xed1838159171fb45,0x0e05645c7ed0c381,0x59171fb420e05645,0xc7edc278159171fb,0x770e05645c7ede03,0x8159169eb760e056,0x45a7edd838159171,0xfb750e05645c7edc,0xc38159171fb720e0,0x5640bfed1e781591,0x1b3ff915a37247cf,0xfe4568dd4d1ebf61,0x5e16488fafd85645,0xd613ebf61591722b,0xfafd858559069ebf,0x61609642dfad1a78,0x1590b7fb469e0564,0x3e4ffe4558dcde53,0xff91563762f7cfd4,0x58559235e7f515d9,0x65327ed16781590a,0x93ff914e37273cff,0xe4538dd5f3fcf315,0xc93286fd7cc57554,0xcefbdf3156373317,0xed0e781590b9faf2,0x1609648bfbbc8576,0x588c7fb429e05645,0xc7ed02781591717b,0x609e05645c7ed827,0x8159001bef925e16,0x5005fbe49855d801,0x7ef9261975004fbe,0x4978594017ef925e,0x165444ffe4978594,0x017bf925e164466f,0xd443825d825eef92,0x5d962096fb4a7825,0xd81fbed72e097662,0xefb58b825d919bed,0x20e097662eef5938,0x25d911afd65e0976,0x424ffe4968dc909b,0xec52e0976426fbc8,0x3825d919bf710e09,0x76006fbe497854c0,0x17ef9260d75005fb,0xe49855cc013ef925,0xe153005fbe497854,0xca53ff925e153647,0xf9443825d591be51,0x0e0975007eb59382,0x5d401bad64e09750,0x07db597825d401f6,0xd53e09756477b5c3,0x825d401bed86e097,0x5006fb5db825d401,0xbed84e0975006fb6,0x0f825d58fbed81e0,0x975646fb603825d5,0x88fed75e0975006f,0xb5d3825d401bed73,0xe097563efb5c7825,0xd591bed70e097562,0x6fb5e7825d589bed,0x65e0975006fb5938,0x25d401bed63e0975,0x63efb587825d591b,0xed60e0975006fb5a,0x7825d431bec86e09,0x755e6fb1db825d58,0x9bed54e0975626fb,0x54f825d589bed51e,0x0975626fb543825d,0x589bed59e0975627,0x5b1d7825d589f6c7,0x5e09756277b1d782,0x5d589bec75e09756,0x26fb197825d401be,0xd43e097563efb507,0x825d591bed40e097,0x5006fb527825d501,0xbec84e09755e6fb1,0xd3825d501bec64e0,0x975626fb153825d5,0x8fbed31e0975646f,0xb4c3825d401bed39,0xe09750c6fb20f825,0xd579bec73e097500,0x6fb18f825d589bec,0x53e0975406fb10f8,0x25d4bfbbf8259175,0x3b6fbe27825d4edb,0xef79e0975006fbda,0x7825d4edbef59e09,0x75406fbd27825d40,0x1bef39e0975646fb,0x443825d58fbed19e,0x09753fefb207825d]))
  | 7 => (OfNat.ofNat (certificateWord [0xb48160964396ef20,0x585590053fc915a3,0x72014ff24568dd40,0x53ff19e1975014ff,0x24558dcc053fc915,0x63762deefc6164dd,0x4053ff19e1573014,0xffc67855d8053fc9,0x14e372014ff24538,0xdd4053ff19e0d752,0xdeefc6164dc8053f,0xf19e0973014ffc67,0x825d9717b509e056,0x4464ff427825d8a7,0x3fd09e0973976ef4,0x2164dc8f73fd09e0,0xd75484ff427855d9,0xcd3fd09e15739d6e,0xf42164dd5e73fd09,0xe19757a5ef427785,0x91633fd099e16554,0x4ff4267854c033fc,0x905e1652d5ef2417,0x8590033fc905e162,0x00cff2417854cb5b,0xbc805917500cff24,0x1784c8b5bbc80591,0x7200cffc267854c0,0x33ff099e1652d5ee,0x24185590e3fb8906,0x15642d5ef2418559,0x0b57bc90609642d5,0xeec2778590b57bf0,0x9de16400cff24168,0xdc8033fc905a3750,0x0cffc27865d4033f,0xc905637300cff241,0x58dd8b5bbf085937,0x500cffc27855cc03,0x3ff09e157600cff2,0x4138dc8033fc904e,0x37500cffc27835d4,0xb5bbf085937200cf,0xfc27825cc033ff09,0xe0976484ffe41785,0x95237bf905e16446,0x4ffe417858a336ff,0x905d9653dcffe417,0x854e21bbf8059175,0x895dfe4175594a73,0xff905e13281df7e4,0x17354dff7df905cd,0x327e5fbe4172589f,0x17ef905c932846ef,0xe01645c923dbf705,0xe1648876fdc1645d,0x625d7f705d565867,0x5fdc17554e33cff7,0x05d9658b73fdc176,0x589219ff705e1650,0x767fdc168dd41d9f,0xf7056376005eee41,0x8559001fbb906156,0x438defe418559079,0x7bf906096438eefe,0x0185591193ff905a,0x372484ffe4168dd4,0xd1ebf605e164887a,0xfd81645d611ebf60,0x591722bfafd81855,0x9069ebf606096489,0x79fd8175594f73ff,0x905637379cffe415,0x8dd8bdf3f5061564,0x8cf9fd4176594a73,0xff904e372734ffe4,0x138dd5f1fcf305c9,0x32867d7cc17554ce,0xfbdf30563737fff3,0xc81734c8b9faf206,0x09648b7bbc817658,0x909bef205a372276,0xfbc8138dc9f9fe71,0x05c9627c7f9c4172,0x4ca07fd7105cd537,0xfff5c41734c923fb,0x7105e164887edc41,0x645d611fb7105917,0x238fedc418559079,0xfb71060964897ddc,0x417559619f77105d,0x5538cfbdc4176596,0x2def7105d962486f,0xdc417859519bf710,0x5e1623defdc41785,0x4ca7bf7105e13246,0x6fdc4168dc921bf7,0x105a3753defdc415,0x8dcde7bf71056376,0x29efdc4138dc9cdb,0xf7104e37547cffe4,0x57859401fb7915e1,0x64005ede45785912,0x57bf915e16446cff,0xe4578588f93ff915,0xe15388eefe05645d,0x62777f915d5652a4,0xffe45784ca097df9,0x15cd53805f7e4573,0x4c9fb7ef915c9628,0x4eefe05645c925db,0xf715e1648d73fdc5,0x765962fcff715d96,0x2005ede458559001,0xfb79161564395efe,0x4585590017b79160,0x9640e7ede4582590,0x7b7bf91609645c7a,0xd583815902ffb578,0xe05645a7ed5db815,0x9001fb575e05645a,0xfed5cf8159001fb5,0x72e05645c7ed5c38,0x15902ffb579e0564,0x0bfed6178159169f,0xb565e05645afed60,0xf815902ffb582e05,0x645c7ed603815902]))
  | 8 => (OfNat.ofNat (certificateWord [0x935e1642ede724d7,0x8590bb7bc935e164,0x22ef724d785890b7,0xdc9360976024f724,0xd78588093fc935e1,0x6204fb724d765941,0x3edc935d9623d6f7,0x20d855d88bbdc836,0x097642df7e27835d,0x8ef7dc935d975024,0xf7e27835d8eff5c9,0x35d553025d724d75,0x54cefbdc8360d750,0x25f724d755ccbbbb,0xc8359175025df24d,0x7554cbbbbc835917,0x2024ffce678594ef,0xddc73615733bf771,0xcd755cd85bdc734e,0x372716f71cd38dd4,0x453ff399e1532ede,0xf24d85590bb7bc93,0x609642edefce7785,0x90093dc935a37263,0x6f724d68dc8093fc,0x935a372024f724d6,0x8dd5cbbdc935a375,0x024ff24d68dd40f3,0xff69e0d75024ffce,0x7865d4eff5c635d5,0x533bef718d58dcc0,0x93fc93563762eeef,0xce164dd4093ff39e,0x15763bfd714d7854,0xc433ff39e157302c,0xff12538dd40b3ff4,0x9e0d7569cff4a783,0x5d5113fd29e15762,0x94ff4a7855ccbfbb,0xd285937577cff4a7,0x865d4c37bd29de16,0x457cff4a6785953f,0x3fd299e153446fb2,0x4978595097ec9261,0x5763b5fb249865d4,0x073ec925e165375f,0xb24978594073fc92,0x5e1652e5ef249785,0x9109eec925d96242,0x6fb209825d8076fc,0x925d962296fb2497,0x854ced7ec9260d75,0x275fb249855cc073,0xec925e15324dfb24,0x97854c073fc925e1,0x532ffeb209645d4b,0x9bac8259175047db,0x24975594dd76c925,0xd565047db2497554,0xd11bec8261975426,0xfb209765d4a5bec8,0x260d753b5fbe2782,0x5d49d7ec925d5730,0x1cfbe27825d4b9bb,0xc8259175375df249,0x755949dfcc925cd3,0x201df3249734c807,0x7dc925cd3201cffc,0xa67854c073ff299e,0x1652e76b1c9645c8,0xb9fac72591722e76,0xf1c9645ca0dbbf78,0x59372104ffde7825,0xccb97bc92615640b,0xeefe6164dc8b97bf,0x29de1642e7eb2098,0x2590b9bbc8260964,0x01cff24968dd40fb,0xbf685937203cffda,0x7825cc073ff29e19,0x750fcffda7825d80,0x73ec925637369efb,0x24958dcc073fc925,0x637301cfb24958dd,0x9dfbec925637601c,0xff24958dd8bdbbf5,0x859372034ffd6782,0x5ccb9bbf28593750,0x1cffca7855cc0d3f,0xf59e097601cffca7,0x855d89dfcc525cd3,0x2427bb1497658909,0xbec525a372276fb1,0x4938dca37e7c525d,0x96502cffd27825cc,0x0b3ff49e097601cf,0xf24938dd4bbbbf38,0x5937201cffca7835,0xd4093ff39e09760f,0x4ffce7825cd1b3fd,0x19e09762a4ff4678,0x25ce5fbbd1859372,0x3e4ff467835d51f3,0xfd19e157673cff46,0x7855ce77bbd18593,0x75794ff467865d5e,0xb7bd19de164584ff,0x46678595533fd199,0xe153014ff2457859,0x525fb4915e1642dd,0xed24578590b77bc9,0x15e164014ff24578,0x588053fc915e1532,0xdeef205645d4053f,0xc915e1322deef205,0x645c8053ff199e15,0x3014ffc6678594b7,0x7b49161564397ed2,0x4585590b77bc9161,0x5642dded24582590,0x7bfb491609642dde,0xf24582590b77b719,0xde1642ddefc67785,0x90e5bb4816156449,0x7ed2057859223fb4,0x915917584fed2456,0x45c8b77b789e0564,0x397ed205855907bf]))
  | 9 => (OfNat.ofNat (certificateWord [0x5a37243dbf5a7785,0x95cbafd635a37544,0x6bf58968dd5219fd,0x705e165004ff6517,0x8594f53fd965e153,0x444ff655785891f3,0xfd915e165484ff64,0x1785950f3fd799e1,0x65474ff651785888,0xb3fd965e13246cff,0x64578589193fd905,0xe162424ff4a7825d,0x9053fd795a3753ec,0xff6517854ca53fd9,0x55e1323e4ff64578,0x54cf73fd905e1533,0xbcff5e67854ce93f,0xd7956376034ff261,0x765d4ab3fd945e13,0x22a4ff645784c8a7,0x3fd905e132274ff4,0xa7825cc993fd794e,0x375024ff261755cd,0x093fd79e0976274f,0xf5e7825ccef3fd79,0xe0d7543cff5e7855,0xd8093fd79e157303,0x4ff5e7865d5113fd,0x955a3723d4ff5a55,0x8dcc019fd781e165,0x14cffe26785951d3,0xfd945a372004ff65,0x168dd58d3fd694e3,0x7272cff5a538dd51,0x13fd925a37546cff,0x64568dc91f3fd915,0xa375464ff64168dc,0x9213fd905a375634,0xff5a7825cd093fd6,0x9e097601cff1e568,0xdc8f53fd69e0d757,0x2cff5a7855cd219f,0xd705a37543cff5a7,0x855d80d3fc795a37,0x553cff5a67854c0d,0x3fd699e16503cff2,0x597854cf3afc8661,0x97503ebf219765d4,0x0f3fc965e13203cf,0xfda67854cf3cfc76,0x615762273f1d9825,0xd8f3cfc765d97562,0xebf1d968dc9c9afc,0x765a37513cffda67,0x8594fb3fd9456373,0x004ff65158dd8a53,0xfd594e3723d4ff64,0xd58dd8179fc785e1,0x5369cff64958dcdd,0xf3fd92563763e4ff,0x64558dcde53fd915,0x63763dcff64158dc,0xde73fd9056376444,0xff567825d8a53fd5,0x9e09733bcff56783,0x5d4093fc79563730,0x3cff1a558dcc1daf,0xd765637679e7f5c1,0x58dd9dd3fd59e197,0x5774ff1e558dd95d,0x3fd599e165024ff5,0x667854c0d3fc955e,0x16243f9f25576594,0x0d67c955d96543ed,0xf215855d80d77c95,0x5d975035bf255765,0x940d3fc955e13228,0x6df215855cc0db7c,0x855d57343f5f1d58,0x65d50fd7c755d975,0x2875f1d5835d4a1d,0x7c755d57368edf1d,0x558dcdddb7c75563,0x76124ffd667854c0,0xd3fc955a37203cff,0xda7855cd0fe7c655,0xe16514f9f1947859,0x4473ff59e19752ac,0xff52538dc9d13fd4,0x94e375474ff52782,0x5d8ab3fd49e09733,0xecff527835d4013f,0xd49e1576744ff527,0x855cc013fd49e197,0x5004ff5267859555,0x3fd499e15302cff2,0x51785940b3fc945e,0x16202cff2517854c,0x0b3fc945e13202cf,0xfd267854c0b3ff49,0x9e16502cff25168d,0xc80b3fc945a37502,0xcffd27865d40b3fc,0x945637302cff2515,0x8dd80b3ff49e1573,0x02cffd27855d8a53,0xfd924e3752a4ff64,0x538dc9cf3fd914e3,0x7529cff64138dc9c,0xd3fd904e375634ff,0x4e7825d98dbbd385,0x9372274ff4e7825c,0xc073fc794e37203c,0xff1a538dc80d3fc5,0x94e37202cff12538,0xdc9cb3fd39e15767,0x2eef4e164dd41db7,0xd754e375714ff4e7,0x855cdc53fc794e37,0x503cff1a538dd4f5,0x3fd39e19756ddef4,0xe7785914f3fd399e,0x16552cff4e67854c,0xf5bdc935e16542df,0x724d855d8ef7dc93,0x61975024f724d785,0x94df7dc935e16502,0x4ff24d78594d3f9c]))
  | 10 => (OfNat.ofNat (certificateWord [0xd32276f7261734c8,0x073dc985cd3201df,0x7261734c81d9dc78,0x5cd32076f71e1734,0xc815ddc785cd3286,0xfd74c57554cf9bdd,0x3156373867d74c17,0x554cf7bdd3056373,0x636f758d38dc8a5b,0xdd534e372276f74c,0x938dc9cbbdd634e3,0x75285f74e77854ca,0x5bdd324e3753cfcf,0x59175594f5f3d645,0xd5532ffcf549645d,0x4e5f3d516156438f,0xcf5418559125ebd6,0x15e16488faf58564,0x5d613ebd61591723,0x97af585855907beb,0xd616096448faf581,0x7859221ebd605917,0x5847af581645c8e3,0xebd60615641e7af5,0x81825910d6bd69de,0x164006ef5e185590,0x017bd941e16534ee,0xf60d7859001bbd78,0x609642feef615825,0x90e3bbd80615642f,0xf6f5d5645c925dbd,0x715e16448f6f5c17,0x859221dbd7059175,0x005ef5e585590f3b,0xbd645e16534def64,0xd78590017bd79609,0x64495ef645785912,0x37bd905e164435ef,0x6277859089bbd645,0xe1623d6ef5917854,0xcbfbbd855917288e,0xef605645d621bbd8,0x059175886ef56164,0xdd48bbbd645e1328,0x4eef605645ca11bb,0xd8059172846ef4a1,0x64dc8b17bd936156,0x42fdef65582590e5,0x7bd916156438def6,0x4185590c17bc7961,0x5641adef64d82590,0x7b7bd91609641e5e,0xf64182590c17bc79,0x60964006ef66164d,0xc801bbd98593750b,0xeef225645d4c3bbc,0x895917206e6f1e17,0x8590c1bbc785e164,0x0bf6f1e178590517,0xbf79de16462eef5a,0x164dc90d7bd69de1,0x64726ef5a164dd40,0xfbbc865917503eef,0x219645c8bfbbd585,0x93723d6ef59158dc,0xcf3bbd6456376005,0xef56778590bd7bc9,0x55e1642f6ef21564,0x5c8bdd3c75591752,0xf7cf1d5645d4bddb,0xc755917583eefde1,0x64dd4bd7bc956096,0x40beefe6164dd4bd,0x7bf59de1642f6cf2,0x1585590bdf3c8561,0x5642f6ef21585590,0x0fbbf68593750079,0xf595765d411e7d62,0x5d5658979f581755,0x94f5b7d685d55304,0x6df6097559411d7d,0x725d5658975f5c17,0x5594f5b7d655e153,0x89ddf64575596257,0x7d905d5653cedf26,0x1755940f37c985d5,0x6503ddf654785941,0xd97c785d565076df,0x1e17559401d7d751,0xe165076df5d568dd,0x4f3e7c965d56503d,0x9f259755940f77c9,0x65d565046df60975,0x54c13e7d535d9650,0x475f5c97554e19d7,0xd705d5533d6df54d,0x78594efb7c985d55,0x3024df2617554c09,0x77c985d5530765f1,0xe17554c1db7c785d,0x55305f5f1e17554e,0x35e7d515d9658cf9,0xf54176594f5b7d65,0x563733bddf567785,0x4da7b7d52563733c,0xddf56778594f5b7d,0x535637677edf5495,0x8dd813afd835d965,0x446bf6157658813c,0xfd735d9658d73f5c,0x57659633cfd705d9,0x65446bf5957858a3,0x36fd905d96543ebf,0x261765940d2fc985,0xd965035bf6587859,0x41d8fc785d965076,0xbf1e17659401cfd7,0x61e16504ebf60d76,0x58813cfd735d9628,0xbf3f5c57658a2dcf,0xd705d962446bf589,0x7859509afc985d96,0x201cbf2617658807,0x6fc985d9620763f1,0xe1765881dafc785d,0x9620673f1e176589,0x11afd655a372636b,0xf58d68dc909afd62]))
  | 11 => (OfNat.ofNat (certificateWord [0x10002380080210a1,0x7044d6800404c050,0x05c18c0000102142,0xc202000c00702048,0x05002c00f301c106,0x0018100140400c14,0x0020000002950e09,0xc80004c703061c40,0x234080120c060800,0x248349020008b060,0x4009000400008009,0x8004007031434184,0x0038002000000304,0x4101c002c0070404,0xa0024445050820a0,0x00c0c0a400000030,0x40920d04001832c0,0xc200220871806001,0x03001881b2c14089,0x002c69b040408b02,0x0048760200180200,0x1304004086002419,0x60220014081c0095,0x2090010208a83200,0x099d040cd80006c0,0x9102680011c54103,0x082038408005801e,0x2480606080940430,0x0080c0840c040800,0x8020860f0e248000,0x2042810c18001045,0x4008020c20868043,0x0300200050e2cd04,0x00040010024c0f04,0x2010536080010a28,0x30c072c000041400,0xb3600001004c20c0,0x0000801438203103,0x03040808185100c4,0x830038a01140c407,0x0404780020400402,0x0420800401810604,0xc01040810b080401,0x900603820c001041,0x204104000c017f99,0x01e165005ee42778,0x590017f5911e1657,0xe7f944172589f1fe,0x5105c93281ff5441,0x7354dfffd5105cd3,0x248fed4417859221,0xfb51059175847ed4,0x41645c8e3fb51061,0x5641e7ed44182592,0x25f75105d565867d,0xd4417554e33ef510,0x5d9658b7bd441765,0x8921bf5105e16546,0x6fd44178588f7bf5,0x105e15329efd4417,0x84c919bf5105a372,0x486fd44168dd4f7b,0xf5105637379efd44,0x158dd8a7bf5104e3,0x72736fd44138dd40,0x17b519de16407ff3,0x5c9734c813fcd625,0xcd32047f354d724c,0x9f3fcd315c9327c7,0xf34c1724c889fad6,0x2591722ffeb54964,0x5c81feed725d9620,0x47bb5957258811be,0xd855c962005fb648,0x785948bbed685c93,0x20477b5d5725888b,0xbed625e1327edfb6,0x4572589f97ed905c,0x962226fb26172588,0x0f3ec985c96203df,0xb261725881d9ec78,0x5c962076fb1e1725,0x8819dec785c96207,0x6fb5c968dc889eec,0x965c96203dfb2597,0x258811bed585c932,0x1ddfb255725888bf,0xad325917204fbb4c,0x97658811ded755c9,0x3222efb4c978589f,0x17ed905c932195fb,0x255724c883bec985,0xc932024fb261724c,0x8097ec985c932076,0x7b1e1724c81dbec7,0x85c9320577b1e172,0x4c81dbed724e3722,0x0ff324d724c8097c,0xc935c932025fb24d,0x724c883fcc635c93,0x21efeb485825922f,0xeed215d9627fff34,0x81734c879fad2060,0x9648b7bb48176589,0x19bed205a37229ef,0xb48138dc813f9d64,0x5cd53007d754d755,0xcc13f5d655cd5304,0xef75a17354c017dd,0x931e16504ef75a17,0x34c8a5bdd585cd32,0x04f775d97354ca5b,0xdd535e132825f764,0x57354e077dd905cd,0x5325df72597354ca,0x1bdc985cd53034f7,0x2617354c0d7dc985,0xcd53076771e17354,0xc1dbdc785cd5305f,0x771e17354c1dbdd7,0x356373287d725573,0x54c0d75c955cd530,0x35f72557354c13f9,0xd645cd32047d74c9,0x7554c13ddd765cd3,0x2296f74c97854e01,0x7dd915cd327fdf76,0x41734c8677dc965c]))
  | 12 => (OfNat.ofNat (certificateWord [0xad560c0001a4d340,0x018a0275c1c0011c,0x00004141202150e1,0xa199709acd594710,0xc9a50671a81ab941,0x01758cd994de5115,0x75c801a317081648,0x84e5000000068545,0x570c37ccf9ad8000,0x00058c0009d00b00,0x000015ec00044400,0x056928d19c000000,0x0015acad10405b80,0x00000000000c7064,0x0cd4000e40a60600,0xe380000000005800,0x000157bcc0d41400,0x05a10196c0000488,0x308cad230d21bc13,0x90001300f647143b,0xc67ca28f7c0003b0,0x0018c439596daf51,0xdccb0b55bb41c419,0x092d7912b936c840,0x00023808ce100000,0x018980016d9a3ce0,0x4f4ce0dc3c929514,0x5d469d8149a4c94e,0x30abd8adccce5d9c,0x4f45ca14286244bc,0x14592119550005c0,0x000017fd6b1ac9b9,0x1bdc0006b582dbec,0x3b4000b649cdaa59,0x603600e56955093d,0xc148000001284000,0x94cd9c000000bc80,0x01b80d7d295d8c00,0x1dd00012f8554000,0x134ac00010386615,0xf9c881d940985807,0x5db0cc0b0d47d24d,0x80151906ccdc8092,0x457840008d154cf9,0x9d0412d354d80001,0x44800019c638ba4e,0x65320e29424b3952,0x19501612cd4d449d,0x07893ca4d661adc7,0xc8a89a61b41ae85e,0x1580b50c5db5c859,0x1c4021199875c4c5,0x40fac9d918c99c6b,0x00013d96cd3d55b1,0x1b8000268000cf4e,0x48210c84031bf44c,0x8000000f18000001,0x3c834c000bb04c40,0x00000ddc0001bcea,0xd9cd3a4fe43ace8d,0x3c0508001888d3d0,0xe5cf85f5c44594a5,0x5839dc8060b90bf0,0x078bb513c8746909,0xbc245171935d3939,0xd1e86c53e1c78000,0xa651641fd0fc9a09,0x0c0ecb88c8c0a93f,0x5435ac40008f1b6c,0x6d9aa1bc95cd629d,0x4438879d4b534891,0x0000000ebc000001,0x3f886c0000000001,0xc9ce934ce801ec34,0x59380013b40004a9,0x6e994d7b56e40000,0x00ba0000ec4c0418,0x5b442c811818dc74,0x7fd680ef4fb4000b,0x4c0000008b192401,0x8ed1238ea8408b78,0x0010f1b986a4000d,0xa51b58d13cc234b2,0x02fdb74f7471cde9,0x21861d6fdc0cb342,0x6000000000000000,0x09f147466800133c,0x0000014c91d978c0,0x00001978354818b1,0x0c98299a08f8d091,0x8f19e491c96414d4,0x88000000dc868c00,0x10b40015dc984001,0x83002cad9bd9c5d4,0x5dba8905b3c001bf,0xcec908d1ad1057b8,0x03c1394a0699ae15,0xc81317e9d7c500cf,0x18c18796bd140324,0x35937cc812a4a48f,0xdc199364848854c5,0x8000ca800106100c,0x000000a417980a40,0x00931e008181de8e,0x0016010812a04280,0x160c2bb1a1838c7e,0x4010204040220608,0x6010804202042001,0xf02dc10500389021,0x2f002c140068e062,0x03002a4888708054,0x8304501003000104,0x3a001132e0098d2c,0x55b013678006000c,0x20372b4011050040,0xb720028304001030,0xc0c2013e3afb72ef,0xce22201908302140,0x03280530c0028103,0x02048b5120840908,0xd830d1a30000560c,0x0840048e84023820,0xa0a2079d02080090,0xc0400a226c00b0c4,0x80804028c0714680,0x830028100000959b,0x0800080004812400,0xb86067a0898f2e14]))
  | 13 => (OfNat.ofNat (certificateWord [0x400014e800064cd2,0xc614000001d641b0,0x001420001bccccc4,0x0d6140000008fc8a,0x00000000007816ac,0x9a80e8768cd800d1,0xa024070d9b112958,0x86a9bf0945c50000,0x000008dbcb305c50,0x6882990d5bd48000,0x0a800008cd288968,0xf60504ea000065d1,0xc976511c845a2998,0x4400365045a4cf15,0xcbd6690257cdba4b,0xdcd05119c30c4082,0xd9b4a50051dcd545,0x6f9868860664000e,0x1995dc1494081400,0x04d964d9bd3102cc,0xeb19f0ef0af4e2c4,0xd1d9994875000000,0x0335d614cd6543a4,0xa3d5300000008ac0,0x0043db4c000001ae,0xce3c0017750d5c65,0xa68000560000df40,0x00d240000005486f,0x80015f4000001a54,0x73c000001b2c0002,0x3000196400054d4b,0xd690925a5d3e4490,0x0690a09dd3956257,0xf802435c7545ad7c,0x04600002b12a8644,0x9e13b8571404db02,0xf1930dcd2206e021,0xc2c5675001bd47e4,0x4e967ca240003f9a,0x8c0014a8aa87f457,0x8db40008a8000a98,0x00036989586c0018,0x40000e9c97d25478,0xd7047789490f9a75,0x71cd1106468076d8,0x35a446dd35848000,0x0000f0121c7acfe9,0xc218f8b980a1be09,0x01430c2c1d1b8577,0x98812fc001594000,0x2e49193842240000,0x015605d91f105071,0x1db4000b9c1a0aa0,0x001804fbc5308ec7,0xb15c10b1d089c945,0x024c75d818c48170,0xaecfa0f50d015b43,0x203497a800118529,0xc001cd820400104c,0x0005296453740016,0x35a90f2927cce56a,0x01e0000d8ca10c24,0x0cda39008af9638e,0x90c68890d49d5d2a,0x084c2e05cdb9c865,0x80dd6c9e8071cd40,0x00001a64b288c591,0x4081769308001200,0x0dddbc2a56f4d70e,0xb5d0dc1121566dc3,0x84b56a5259b790bc,0x719b581554f910c3,0xe06c06f5d4d9f81a,0x99ed134544f38265,0x689318ec146851c9,0xed2d0ee87a412442,0x4a0d7602953a1098,0xdd0f4845cf2c2503,0x91c9ce08441d3c33,0x8bf488d9d045577d,0x1a5918b7588535dc,0xa5c5562c3ed7018b,0xd94062d22c4e150c,0x9f4c2903191d09d8,0xa42202bcbb8708f7,0x8c0056cdf1010694,0x7bc8991cc188a6c9,0x9804838d7512c45b,0x1d5105d69820c744,0xfcdb70f9d5e4775b,0x242f8b71a0d8500a,0xc001cb9cb06d50c0,0x13cae56e0c38f040,0x00001665ab571587,0xd2498dc0018ed4f0,0xb940014b9bac8e00,0x01c6c6cc0018e518,0x8180a01998001d85,0x728278f90d19d280,0x7d41ca192092b16c,0x94ac6b8315c40c3d,0xcf4000001c706e4b,0x1452c000f4148cd5,0xd89057dcad328000,0x000c090b889c9fd1,0xe0000bc0001cd08d,0x581c000088000058,0x88172cdd8650ce00,0x015856f0fb866d55,0x4d08001605928001,0x4dd990de10c5c840,0x000018e800000000,0x13c40000013ec000,0x000eec8947480000,0x0025c0000007dc62,0x05898fc000838000,0x00000000125d4900,0x004f9020995150ec,0xdca8cb9da8ba8d75,0x0d8fec0002583101,0x5da8433ce84000a0,0x88e80000007340c0,0x0000d4001da00001,0x0da2128000197c4f,0xcf84001130000281,0x074e1c0000000000,0x00001cb44a5d2d34,0x4cbcf3517d4ec2d5]))
  | 14 => (OfNat.ofNat (certificateWord [0xe7c87c2189549c5,0x31c000a7ca5d7e43,0xcd7b028908800000,0x1a78449cfc001564,0x721550168d30f6d7,0x199552904683c946,0xdc946bc6a0d55204,0x0d17357edc8cc75d,0xb93995a8410ae809,0xd3bd7385111b112c,0x5fc9804f1558da92,0x60b8cb3d9e95e06c,0x8bf89c01b8b00115,0x0f4041bd0ce80017,0x311a8001b307cdb6,0x94453d05c80006ac,0x0007f8b60c51b557,0xacd153a8759124e8,0x9af9b348b5658be9,0xb05da4cc55241040,0x01c60931d34d6800,0x101c5b4000bd4f24,0x001274ca04700000,0x0000060588c98db4,0x93f00016dcc9d2d4,0x7d8fd90e98e12dd8,0x2051400126c61800,0x03d98d9a483f0001,0xd68d959f40004dcd,0x44f30000bbd910df,0xc5ddaf0920e61bb0,0x23daac44c0008c9c,0x2817c6759a52b429,0xc001a94951211631,0xb648711f44ad1d52,0xac150001181ba0e0,0x157d7c5781100039,0x43d9c81b5110794c,0xfd809650438b7ca9,0xdc2cd6da04635901,0x9acb248c0bd1640e,0x34f0dd10bc431d83,0xd829d74378dc430c,0x36c0f5844e753e80,0x0190881d15400000,0x1b10fc80001dc4a1,0xc08821d24d40001a,0x8916800000000000,0x0430000c10001be5,0x73da1d2e42b5b509,0xb4851335331d1cad,0xd2f4000b08a2d0cc,0x8dc0fd9d89f8ea44,0x98d0dd18d285a4f8,0x9d00824d505f8ca5,0x0580f1b005582000,0x00c306894611595d,0x0a059fdd21d80001,0x5e9969b8972120c9,0x75d591bcd9175800,0x02702d0770d38001,0x4e12e1b19265228c,0x5507cef917842000,0x17d8f5912156944d,0x458f5d1ecc19ab12,0x500658b159dad0ff,0x8d88000a68094ab8,0x0000013505bc0000,0x018b55d44588f400,0x04840014784cd419,0x4b1c485918644e43,0x30c896d4c4cbe1b2,0x1dac000000290000,0x000e69afcf094c0f,0x1c0000003a968c24,0x800152d6ed6197f1,0xbf9d41535298000e,0xe40012bca213888f,0x80bdbc56709b9b1d,0x33847da10e4cb192,0x3dbb9ce03dccb44d,0x4b819a92e992d160,0x108c7997589ca956,0x001e5b0c000001c0,0x1d79acc7c4001771,0xb7c429d89aa80000,0x00044141a009d460,0x8a70000dc0730000,0x00077c001cc48b8b,0x2d7a500453809953,0x985cd85b60304bcd,0xd15b290950d0b458,0x114380019d45e883,0x039c7a0fc5b39871,0xcdd49d1d0790054a,0x8d42d2f1495b8db0,0x9dc1d559b80010a5,0x98d2d976d8a83280,0x01be9138989cc053,0xd0141d57dd6d0000,0x085a2d63d8b8a38c,0x6041c04d361684ed,0x809042cf80c15144,0xa347d19803996c58,0x613b019400446d8f,0x561c1cc3e81adc18,0x0001c15795286f17,0x88960e59ce4ab0f5,0x557411c00000006c,0x28c2ed0292340005,0x50ed40015fc810ff,0xc8e555c385240f68,0x6fdcec8bcbfcbe48,0x6801c000ded17572,0x4fe17e10817f4318,0xd650dc518da00015,0xc450d60927058441,0x8970d798c8760e99,0x2687014655983c56,0xb859c72da6cbd817,0x8e6c3d0b68374a75,0xac1cf0938958a79d,0x499dc3c083c805cc,0x932d484479b14000,0xb1c9081e80008347,0x98fb060c74d85400,0x00016780017a10a8,0x2c0ac81280015903]))
  | 15 => (OfNat.ofNat (certificateWord [0x18d55a400000000,0x0000b6c000655504,0x00184cdb8e940104,0xb07847ed65c1f80b,0x4000a14f94000001,0x94599d38c7880000,0x00e543fd75400000,0x0c1da58bedd3055d,0x7944b8ad4c6dd9c2,0xa00d8740e4428452,0x05ec0c848d7c9610,0x2d8e707b9620c200,0x346583503804f4c9,0x15485e44947d5a9c,0x0e085d748d9896d3,0x15c05c915d9a4064,0x9959710f205c0b04,0x95c4ec0b86d1abd5,0x712edae51e4c4497,0x8000a91904000370,0x00130cfd5368e209,0x342aca302dcb58aa,0xd74c16d3ac5741f4,0x5f000169dc80edc2,0xb9a1427c000a58e7,0x8fa48794fcee19a0,0xcc8eb80000005d0b,0x48fc1379bbd0ed03,0xd340efc629a25a70,0x2292c15413249913,0xfdc58ac4a1d0549e,0x5c7ccd0daccecb40,0x474ae114c2540005,0x247c0e14000000d1,0xc2087b4df9a7d9e1,0x0acc64b5c9140000,0x014c54f551c564f7,0x0000d4dc68fa8000,0x46502c6100000000,0x00000450d6140cff,0x164953cab57d54d8,0xff58240010492780,0x00bad56d989d9000,0x11f80014d076558d,0x5a0631a343f53808,0x0c0f8c351486edb9,0x5c3432ca44afc8a5,0x2c9d700019c0888a,0xf0301d94728acc00,0x11fd109c98001440,0x0007242a88d90340,0x014e43e422c00116,0xc1580c56a8b84110,0x26c4c0001a98f102,0xf47e83a05986e984,0x8435400a85744000,0x739c242e84041015,0xf0000dd5dc515d22,0x41f193d5107056b4,0xc7ce257d13703d46,0x790714994a49b179,0xcf3c3b91907a95b8,0x5a80293045347e0f,0xd108463caa57407f]))
  | _ => 0
def g17K7 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x78591abcce3c726b,0xc2c86bde5247935e,0x16435ef2903c9af0,0xb21a769f60e4d785,0x90d7bcb88726bc2c,0x800de5e47935e164,0x6b6f2f03c9af0b21,0xa769f61e4d785900,0x19ea88726bc2c445,0xce7593935e162236,0x7ae21c9af0b1003d,0xd1105c3835d801de,0x888301c1aec00ef4,0x44170e0d769bf7a2,0xc088706bb24fbd14,0x0443835d801de888,0x241c1aec00ef4441,0x09e0d769bf72ac88,0x8706bb4dfcd47644,0x3835d927dca25221,0xc1aeccaab722965e,0x0d766559b8f4b2f0,0x6bb34a9dc8a5c383,0x5d90b1ee45726c2a,0xecd2b3729970e0d7,0x60d74b90ab2f06bb,0x32b95c755d7835d9,0x95cce3a2e9c1aec8,0xbec715154e0d766a,0x579944c2f06bb352,0xbcca25d7835d9a95,0xe6512b3c1aec8aaf,0x528584e0d764557a,0x942a4f06bb2279d8,0x805c3835d995cec3,0x82e1c1aec89ef414,0x110e0d7644f7a612,0x88706bb227bc8204,0x83835d801de8886a,0x1c1aec8aef4e8110,0xe0d769c57af40887,0x06bb002bd7a16138,0x35d8015ebd0a93c1,0xaec00af3e8985e0d,0x7600579f44baf06b,0xb002bcfa2567835d,0x913de910221c1aec,0x00ae7e8d98593720,0x0573f46cc2c9ba80,0x23dfa365168dd401,0x5e7d1ad3c12ea00c,0xf5443935a3726567,0x9ae5c9ad1b90033c,0xd20e4d68dc98d9ce,0xb2726b46e4d4cf31,0x4b935a3726a679e4,0x1c9ad1b93333d710,0xe4d68dc8019e7a97,0x26b46e400cf54439,0x35a37572e73ac9c9,0xad1bab2b35d75e4d,0x68dd5999eb88726b,0x46ea00cf3d8f9256,0x3736256deb431f04,0xba86b35c59567835,0xd9015d7a50c7c12e,0xa8bce712549e0d76,0x3fd7cd4231f04ba9,0xfabeaa018f825d51,0x39ec04a13c1aec18,0x8fbaa463e09750c6,0x79c739cf04bab63b,0x964a443835d913de,0x920221c1aec1acd7,0x96759e0d76004d7f,0x4cbcb0ab23c66bfa,0x65e5825903bc5e3c,0x72cbc2c8f0da724f,0x965e1647aed6923c,0xb2f0b20036b791e5,0x97859001b4fc9f2c,0xbc2c8b3daee5b906,0x15645ced6f2dc8b0,0xab23c6abfa666164,0xdc83b55fd3330b26,0xeaf4daee1909de16,0x47a67770c84ef0b2,0x3d76b78646778591,0xeb9dbc3233bc2c8a,0x1cebe2664e097538,0xed770dc830ab21c7,0x3bb86e418559125b,0x5bc3722bc2c892ce,0xde1b915e164396d6,0xf0dc8b0ab21cb3b7,0x86e45855907bb5bc,0x3722c12c83dcede1,0xb916096400675cc9,0xc92f0b28033ae64e,0x497854e6bdd2884c,0x9c12ea80eab5aa64,0xe09759a575f4cb27,0x04bacd3d2c759938,0x25d66bdd3884c9c1,0x2ea00ceb99392563,0x7300675cc9c92b1b,0xb1eb39e64e4d7859,0x517b4fc3726bc2c8,0x8bce7e1b935e1642,0x2e73cc9c9af0b14d,0xfb9664443835d98d,0x9cf32726b46e4e5c,0xe7993935a3759bf7,0xa4c088706bb2cf6b,0xa6ae418559001b5b,0x35722bc2c8b9dad9,0xab91615645bed6cd,0x5c8b04b20632ee69,0xda7825d4010fed4e,0xf13c2ca0ec7ede19,0x01e1659f697f2fcb,0x2f0b22f32ee76e49,0x58dd9959af3af26b,0x46eacae57dd675e0,0xd765e679ce7c92b1,0xb9b2b3ce72e4d68d,0xc913de938221c1ae,0xc89ef4a0110e0d76]))
  | 1 => (OfNat.ofNat (certificateWord [0x8119de16439ef603,0x5c830ab23df7b31a,0x42778590013dbd0a,0xf2c2ac8008fde859,0x45e165004f6f42bc,0xb04b22576b560e45,0x785901bcda3c722b,0xc2c86bde524f915e,0x164356d6ec1c8af0,0xb21cf6b560e45855,0x90e59dac5722c2ac,0x864ecd2179161564,0x39676f15c8b0ab21,0xcf7b090e45855900,0x1bd9c8722c2ac859,0xdadd8391615641f6,0xd6ac1c8b04b20db6,0xb760e4582590015d,0xbd0b30b26e400aed,0xe8598593750047ef,0x42ca2d1ba8bb7b38,0x142778590b73da45,0x722c12c864f4d1d5,0x75e056431df4944b,0xaf02b218fda4725c,0xb8159165bd9c0f20,0xc2ac8f7daed8509d,0xe1647aed6ed48cef,0x0b21cf6bb61e4185,0x59125b5a35722bc2,0xc872dad1ab916156,0x41eed68d5c8b04b2,0x0023f7a152678595,0x2b3db05722bc2c87,0x39ed82b916156400,0x6f6435c830ab20fa,0x7b60ae4582591111,0xf6cd50dc12ea528f,0xb66a83e0975004f5,0xf44bcb0ab20023ef,0xa265178595299f28,0x8724bc2ca00ceb59,0x3925e1650069d8ed,0xc930abb22356c75e,0x49865d511b3632f2,0x4bc2ca00cf324f92,0x5e16500679907c93,0x0abb2533e710e497,0x8594ad9f288724bc,0x2a600ceb593925e1,0x53296ad8ebc9306b,0xa8035cc73e49855c,0xca5ba629f24bc2a6,0x56cf9c43925e1530,0x057d34031f04ba80,0x2be5a118f825d665,0xdd2882c9c12ea00a,0xf946a43e097598f5,0x5ac2b2704baccbaa,0xd60593825d6615d6,0xb54c9c12eb30f4b1,0xd564e097500575a9,0x431f04ba802bad4a,0xda7825d4015d6a56,0xc7c12ea00aeb52a7,0x6e097500575a9543,0x704baaf2b6c8a597,0x825d5796b63d2cbc,0x12ea18e9b21965e0,0x9755e56d914a9f04,0xbaaf2d6c7a54f825,0xd4015b6ad0c7c12e,0xa00a7b5e863e0975,0x3b47d915c9306baa,0xf38ec765db825d50,0x15d7a550dc12ea80,0xaebd2a76e09755e7,0x358e8ba704baa03a,0xac64593825d4015e,0x651b0dc12ea00af3,0x28d76e09750c7699,0x06a9f04baaf39cc7,0x35cf825d4015e651,0xad3c12ea00eb358c,0x63e097540575e95b,0x1f04baa03b8c4350,0xf825d663dd250ac9,0xc12ea7faf928564e,0x09753fd7ce3521f0,0x4baccbaaf6059382,0x5d665dd3882c9c12,0xea00ee9e8564e097,0x50057cf42b2704ba,0xcc7aaf61593825d4,0x3197634ad3c12ea0,0x08fbe8994563766c,0xe7ca21c92b1b9af3,0x3cd73e4958dcd7b9,0xe698f24ac6e6d9cf,0x34c3925637300675,0xac9c92b1b98033cc,0x63e4958dcdb39e79,0x8724ac6e6bdcf9c4,0x392563735ee79e63,0xc92b1b9bdb3e510e,0x4958dd8019d6b272,0x4ac6ecbccbb5db92,0x563765ee7ce21c92,0xb1bb202baf4ada78,0x25d5019d624a93c1,0x2ea18cf30e539e09,0x755e53def431f04b,0xa9ea3dd9aa17835d,0x8013cfd1af2c2ac8,0x008f7e8d945e1650,0x067aa21c9af0b29e,0xb39d64e4d78594f5,0xa6e3b726c2aec00d,0x571d793619753d6c,0xb8cbc9af0b28033c,0xc92e4d78594019e6,0x41726c32ea81cf5c,0x43935e16500679f2,0x5c9af0b28033cf82,0xe4d865d4013cfd1a,0xf2c12c800de54439,0x35e16435ed3ac3c9,0xaf0b200369d60e4d]))
  | 2 => (OfNat.ofNat (certificateWord [0x2c9c2ce3429aa58c,0x03eaa839a5e27194,0x40182711bc490ea1,0x2a6e1b280529a21e,0x98e8e1129908e309,0x141196e8ca4a328f,0x24413a051f40ca56,0xa2844210bc070e80,0x30c6b20922814400,0x07e421ea71800822,0x160d0505c800a48e,0x2000600004800250,0x9f83e00000000006,0x00000022e659d627,0x8008501287268728,0x042e0000000078a9,0xe000000011836a04,0x8a95600164338000,0x00001f17e000ba64,0x9b022a3a61920830,0x006f9f27faa00000,0x05c146b29ba4d1a4,0x4d9888a158000006,0x41c2000004e00036,0x20c18e0100282044,0x42296a0029022201,0xa502282040000708,0x0e11c88000c2840e,0x342810e185845610,0xa820204185020400,0x10400407071c0022,0x200025100c2882c0,0x0297000010b00100,0x16021c1030204202,0x040070002000000e,0x0019900080810000,0x0014e04005040ca8,0x0006af320ba8f0b2,0x8034f9905d878594,0x018fcc82f03c2ca2,0xcd9e195901e16500,0x6f623484ef0b23df,0x6b9614277859001b,0x5cb5213bc2c8f7de,0xc20509de1640069e,0xb22bb0f0b28af674,0x6564478595ef3dad,0x0233bc2c82dcf5e2,0x510e0d7600576a35,0xc4ac8ba99f6b56a4,0x6778591efb5ab023,0x3bc2c800d5b64975,0x1e165156cd8cac90,0xf0b28023eda918f8,0x25d55f1f7d4b0dc1,0x2ea168fbea584e09,0x754fc7df52c1f04b,0xa81335c9854d755c,0xc093ae4d2a6baae6,0x06ad7229535d5730,0x75ab8f4a9aeab980,0x34dd935d8785944d,0xb2e32b263c2caa78,0xf7ea585e0d760ac7,0xbf52c2706bb002ab,0xd6ae25645d4bd1de,0x54af0c2ac860c6f1,0xe578615642e47795,0x2bc304b21831bc79,0x5e182590b43dfcd7,0x2cbc2c85eacf2957,0x861564086c78caca,0x0f0b281b27c98595,0x765d40d33e4d2cab,0xb2ea07a9f229655d,0x9750758f8f4b2aec,0xba8a717f895d6785,0x962b87fc4aed3c2c,0xa010ffea5789e165,0x8af0f8cabc0f0b29,0x7679ca35e5855900,0x91ee51b28bc2ca04,0x8f7e6b935e1652ec,0xf3946bcb04b21767,0x9f9ae4d78590291e,0xfd4b01c1aec048f7,0xe2b93615762ed739,0x46cc2c9b9176b9ca,0x366164dd4091ee51,0xb28b46ea5c9eb289,0x796156401c7d944c,0xa2f0b280e3ef9ae4,0x978594071f7cd724,0xbc2a65ccebe2564e,0x09758df4d904b2ae,0xcba9bb36f8959782,0x5d4071f7c5724c1a,0xea038fb289945637,0x62dcf6942bcb0ab2,0x00a3f4a165178594,0xb73da50af2c12c87,0x2aed28578615642d,0xcf6f35c8af0b216e,0x7b79ae4585590b75,0xda50b30b26e45bae,0xd28598593750147e,0x942ca2d1ba96ebb7,0x1ae25645d6155dbc,0x5722c2ac85b9ede2,0xb91609640147e942,0xa4cf0b2a567b50ae,0x4578590e73da8572,0x2c2ac83e9ed42b91,0x609642d4f7140bcb,0x0ab20063f8a06517,0x8594b53ddcd720c2,0xac8018fe281499e1,0x65004f7740bcb0ab,0x20023fba06517859,0x4e7b5cb0f20c2ac8,0x65ece21790615643,0x9ef6123c830ab21c,0xfbb081e4185590e7,0xbd840f20c2ac8f4d,0xaeda909de1646e6d,0x6ec08cef0b21c76b,0x86ae4185590011fd,0xd02933c2caf79ede]))
  | 3 => (OfNat.ofNat (certificateWord [0x1787700,0x0572301c000b1800,0x5ea1e00000679cc6,0x68b21a904020eea0,0x8c43f800438883b0,0x0007800b51422b00,0x0000240b08c000f8,0xa91ee2601aab0d86,0x31540e8000004208,0x0ae77a724c28e5a2,0xb2000625d02e002b,0xe1b9e82d80046940,0x52244101b89d2524,0x99a83f0769a8e46b,0x2c27c1164889ab48,0x000f00013a20a128,0x8429ae2aa98479ec,0x37800b30005b27a3,0xc25824068b58d454,0x0002a00069ad0792,0x94001d0000f67d84,0xc17a5a91ac47f1b6,0x0026c9024c20aaa4,0xa25c000724f28c4b,0x9f80618456886358,0x309f166168a40029,0xc9d9e0738780e1e6,0x00132409c0818546,0x62a298094b026288,0x8e00aa100da26922,0xae4a976580520000,0x062a1a2894c00200,0x000000a202000002,0x98007e8002000e00,0x0d209ab0760b4332,0x34548642c17c4b00,0x605800ae2368fa0e,0x4f9da53a4e431628,0x499c6ca54891d2a1,0xab4ae8000020a9e2,0x18a416a029066a89,0x6750f44701008800,0x908561615e720dca,0x9abc008be19a3cad,0x9b43207468266172]))
  | _ => 0
def g17K6 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x28d0679009601c00,0x00e20800052da443,0x0066b11a5a909de1,0x640a63d3a944180e,0x0d769ed3b08b4690,0x9de16485d3b38b86,0xb90615640054cdb3,0x1db92615760054cd,0x6b1cf92615730068,0xcd7a58c63e097500,0x53c9b018f9256373,0x0053c5b118f92563,0x730051cd7b18f925,0x637300554db21d79,0x3619750076911058,0x3935e1646b53948b,0x443935e1640073c1,0x10483935a3720051,0x5f8b1d793619755d,0x66b26a86b9061564]))
  | _ => 0
def g17K5 : Nat → Nat
  | 0 => (OfNat.ofNat (certificateWord [0x35aca,0x423110583935e164]))
  | _ => 0
def g17N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 6 => 16
  | 7 => 364
  | 8 => 1909
  | 9 => 2160
  | 10 => 116
  | 11 => 1
  | _ => 0
def g17R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt g17K5 (i*83) 74
  | 6 => packedAt g17K6 (i*72) 63
  | 7 => packedAt g17K7 (i*61) 52
  | 8 => packedAt g17K8 (i*50) 41
  | 9 => packedAt g17K9 (i*39) 30
  | 10 => packedAt g17K10 (i*28) 19
  | 11 => packedAt g17K11 (i*17) 8
  | _ => 0
def g17H (k i : Nat) : Nat :=
  match k with
  | 5 => g17Hint (packedAt g17K5 (i*83+74) 9)
  | 6 => g17Hint (packedAt g17K6 (i*72+63) 9)
  | 7 => g17Hint (packedAt g17K7 (i*61+52) 9)
  | 8 => g17Hint (packedAt g17K8 (i*50+41) 9)
  | 9 => g17Hint (packedAt g17K9 (i*39+30) 9)
  | 10 => g17Hint (packedAt g17K10 (i*28+19) 9)
  | 11 => g17Hint (packedAt g17K11 (i*17+8) 9)
  | _ => 0
def g17I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt g17K5 (84+((h/1+packedAt g17K5 (83+(h % 1)*1) 1) % 1)*1) 1
  | 6 => packedAt g17K6 (1164+((h/6+packedAt g17K6 (1152+(h % 6)*2) 2) % 23)*5) 5
  | 7 => packedAt g17K7 (23058+((h/122+packedAt g17K7 (22204+(h % 122)*7) 7) % 436)*10) 10
  | 8 => packedAt g17K8 (99909+((h/637+packedAt g17K8 (95450+(h % 637)*7) 7) % 2257)*12) 12
  | 9 => packedAt g17K9 (92160+((h/720+packedAt g17K9 (84240+(h % 720)*11) 11) % 2716)*13) 13
  | 10 => packedAt g17K10 (3521+((h/39+packedAt g17K10 (3248+(h % 39)*7) 7) % 166)*8) 8
  | 11 => packedAt g17K11 (18+((h/1+packedAt g17K11 (17+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g17Pos : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0x844beff78222ffdf,0xd0049ffff81507e0,0xf804211088442212,0x1117c3c78f3c3ce7]))
  | 1 => (OfNat.ofNat (certificateWord [0xbfdc211104457fee,0xeffff00448220bff,0x00084221108be1f0,0x222bfc07f03fc0f8]))
  | 2 => (OfNat.ofNat (certificateWord [0xfdfbff7b7fff8442,0x4089208890881021,0x08909f0f81104425,0xf0f3fff8003fff00]))
  | 3 => (OfNat.ofNat (certificateWord [0x890422208880884,0x8110411121402042,0x1121044227c3fe01,0xff03ffffffc00000]))
  | 4 => (OfNat.ofNat (certificateWord [0x111c844390119108,0xf22272223803fc84,0x207c1ff007fc8041,0xfffc444091044429]))
  | 5 => (OfNat.ofNat (certificateWord [0x21e1087c211e220f,0x04438443c20c4108,0x427fe80407fffffe,0x4040888902088942]))
  | 6 => (OfNat.ofNat (certificateWord [0x3e020f8041e043f0,0x087c087c04708210,0x847ffffffa010880,0x8401111224511094]))
  | 7 => (OfNat.ofNat (certificateWord [0xc003f0007e007c00,0x0f800f800780ffff,0xffc2108844221109,0x0882222448a22200]))
  | _ => 0
def g17Neg : Nat → Bits
  | 0 => (OfNat.ofNat (certificateWord [0x3ffff80007fff,0xf0000ffff80003e0,0xf800000000000000,0x0003c3c78f3c3ce7]))
  | 1 => (OfNat.ofNat (certificateWord [0xfffc000000007fff,0xfffff000000003ff,0x000000000003e1f0,0x0003fc07f03fc0f8]))
  | 2 => (OfNat.ofNat (certificateWord [0xffffffffffff8000,0x0000000000000000,0x00001f0f80000001,0xf0f3fff8003fff00]))
  | 3 => (OfNat.ofNat (certificateWord [0x7c3fe01,0xff03ffffffc00000]))
  | 4 => (OfNat.ofNat (certificateWord [0xfc00,0x007c1ff007fc0001,0xfffc000000000000]))
  | 5 => (OfNat.ofNat (certificateWord [0x7fe00007fffffe,0x0000000000000000]))
  | 6 => (OfNat.ofNat (certificateWord [0x7ffffff8000000,0x0000000000000000]))
  | 7 => (OfNat.ofNat (certificateWord [0xffff,0xff80000000000000,0x0000000000000000]))
  | _ => 0
def g17Atlas : Atlas := ⟨11,rawDecor 255 g17Pos g17Neg, (OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffffefff0,0xfffefffeffeeffee,0xfefefafaeeee0000,0xffffffffffffffff,0xfffffffffffefff0,0xfffefffeffeeffee,0xfefefafaeeee0000])), g17N, g17R, g17H, g17I⟩
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_2_0 : Interval g0Atlas 2 0 8 := block_range (n:=8) (by decide +kernel)
theorem all0_2 : Interval g0Atlas 2 0 8 := b0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_3_0 : Interval g0Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_3_16 : Interval g0Atlas 3 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_3_32 : Interval g0Atlas 3 32 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_3_48 : Interval g0Atlas 3 48 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_3_64 : Interval g0Atlas 3 64 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_3_80 : Interval g0Atlas 3 80 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_3_96 : Interval g0Atlas 3 96 6 := block_range (n:=6) (by decide +kernel)
theorem all0_3 : Interval g0Atlas 3 0 102 := (concat (concat b0_3_0 (concat b0_3_16 b0_3_32)) (concat (concat b0_3_48 b0_3_64) (concat b0_3_80 b0_3_96)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_0 : Interval g0Atlas 4 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_16 : Interval g0Atlas 4 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_32 : Interval g0Atlas 4 32 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_48 : Interval g0Atlas 4 48 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_64 : Interval g0Atlas 4 64 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_80 : Interval g0Atlas 4 80 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_96 : Interval g0Atlas 4 96 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_112 : Interval g0Atlas 4 112 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_128 : Interval g0Atlas 4 128 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_144 : Interval g0Atlas 4 144 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_160 : Interval g0Atlas 4 160 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_176 : Interval g0Atlas 4 176 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_192 : Interval g0Atlas 4 192 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_208 : Interval g0Atlas 4 208 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_224 : Interval g0Atlas 4 224 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_240 : Interval g0Atlas 4 240 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_256 : Interval g0Atlas 4 256 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_272 : Interval g0Atlas 4 272 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_288 : Interval g0Atlas 4 288 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_304 : Interval g0Atlas 4 304 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_320 : Interval g0Atlas 4 320 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_336 : Interval g0Atlas 4 336 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_352 : Interval g0Atlas 4 352 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_368 : Interval g0Atlas 4 368 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_384 : Interval g0Atlas 4 384 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_400 : Interval g0Atlas 4 400 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_416 : Interval g0Atlas 4 416 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_432 : Interval g0Atlas 4 432 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_448 : Interval g0Atlas 4 448 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_464 : Interval g0Atlas 4 464 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_480 : Interval g0Atlas 4 480 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_496 : Interval g0Atlas 4 496 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_512 : Interval g0Atlas 4 512 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_528 : Interval g0Atlas 4 528 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_544 : Interval g0Atlas 4 544 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_560 : Interval g0Atlas 4 560 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_576 : Interval g0Atlas 4 576 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_592 : Interval g0Atlas 4 592 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_608 : Interval g0Atlas 4 608 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_624 : Interval g0Atlas 4 624 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_640 : Interval g0Atlas 4 640 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_656 : Interval g0Atlas 4 656 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_672 : Interval g0Atlas 4 672 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_688 : Interval g0Atlas 4 688 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_704 : Interval g0Atlas 4 704 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_720 : Interval g0Atlas 4 720 5 := block_range (n:=5) (by decide +kernel)
theorem all0_4 : Interval g0Atlas 4 0 725 := (concat (concat (concat (concat (concat b0_4_0 b0_4_16) (concat b0_4_32 (concat b0_4_48 b0_4_64))) (concat (concat b0_4_80 (concat b0_4_96 b0_4_112)) (concat b0_4_128 (concat b0_4_144 b0_4_160)))) (concat (concat (concat b0_4_176 (concat b0_4_192 b0_4_208)) (concat b0_4_224 (concat b0_4_240 b0_4_256))) (concat (concat b0_4_272 (concat b0_4_288 b0_4_304)) (concat b0_4_320 (concat b0_4_336 b0_4_352))))) (concat (concat (concat (concat b0_4_368 b0_4_384) (concat b0_4_400 (concat b0_4_416 b0_4_432))) (concat (concat b0_4_448 (concat b0_4_464 b0_4_480)) (concat b0_4_496 (concat b0_4_512 b0_4_528)))) (concat (concat (concat b0_4_544 (concat b0_4_560 b0_4_576)) (concat b0_4_592 (concat b0_4_608 b0_4_624))) (concat (concat b0_4_640 (concat b0_4_656 b0_4_672)) (concat b0_4_688 (concat b0_4_704 b0_4_720))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_0 : Interval g0Atlas 5 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_16 : Interval g0Atlas 5 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_32 : Interval g0Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_48 : Interval g0Atlas 5 48 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_64 : Interval g0Atlas 5 64 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_80 : Interval g0Atlas 5 80 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_96 : Interval g0Atlas 5 96 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_112 : Interval g0Atlas 5 112 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_128 : Interval g0Atlas 5 128 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_144 : Interval g0Atlas 5 144 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_160 : Interval g0Atlas 5 160 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_176 : Interval g0Atlas 5 176 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_192 : Interval g0Atlas 5 192 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_208 : Interval g0Atlas 5 208 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_224 : Interval g0Atlas 5 224 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_240 : Interval g0Atlas 5 240 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_256 : Interval g0Atlas 5 256 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_272 : Interval g0Atlas 5 272 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_288 : Interval g0Atlas 5 288 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_304 : Interval g0Atlas 5 304 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_320 : Interval g0Atlas 5 320 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_336 : Interval g0Atlas 5 336 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_352 : Interval g0Atlas 5 352 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_368 : Interval g0Atlas 5 368 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_384 : Interval g0Atlas 5 384 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_400 : Interval g0Atlas 5 400 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_416 : Interval g0Atlas 5 416 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_432 : Interval g0Atlas 5 432 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_448 : Interval g0Atlas 5 448 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_464 : Interval g0Atlas 5 464 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_480 : Interval g0Atlas 5 480 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_496 : Interval g0Atlas 5 496 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_512 : Interval g0Atlas 5 512 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_528 : Interval g0Atlas 5 528 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_544 : Interval g0Atlas 5 544 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_560 : Interval g0Atlas 5 560 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_576 : Interval g0Atlas 5 576 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_592 : Interval g0Atlas 5 592 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_608 : Interval g0Atlas 5 608 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_624 : Interval g0Atlas 5 624 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_640 : Interval g0Atlas 5 640 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_656 : Interval g0Atlas 5 656 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_672 : Interval g0Atlas 5 672 10 := block_range (n:=10) (by decide +kernel)
theorem all0_5 : Interval g0Atlas 5 0 682 := (concat (concat (concat (concat (concat b0_5_0 b0_5_16) (concat b0_5_32 (concat b0_5_48 b0_5_64))) (concat (concat b0_5_80 b0_5_96) (concat b0_5_112 (concat b0_5_128 b0_5_144)))) (concat (concat (concat b0_5_160 b0_5_176) (concat b0_5_192 (concat b0_5_208 b0_5_224))) (concat (concat b0_5_240 (concat b0_5_256 b0_5_272)) (concat b0_5_288 (concat b0_5_304 b0_5_320))))) (concat (concat (concat (concat b0_5_336 b0_5_352) (concat b0_5_368 (concat b0_5_384 b0_5_400))) (concat (concat b0_5_416 (concat b0_5_432 b0_5_448)) (concat b0_5_464 (concat b0_5_480 b0_5_496)))) (concat (concat (concat b0_5_512 b0_5_528) (concat b0_5_544 (concat b0_5_560 b0_5_576))) (concat (concat b0_5_592 (concat b0_5_608 b0_5_624)) (concat b0_5_640 (concat b0_5_656 b0_5_672))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_6_0 : Interval g0Atlas 6 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_6_16 : Interval g0Atlas 6 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_6_32 : Interval g0Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem all0_6 : Interval g0Atlas 6 0 40 := (concat b0_6_0 (concat b0_6_16 b0_6_32))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_7_0 : Interval g0Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem all0_7 : Interval g0Atlas 7 0 1 := b0_7_0
theorem all0 : ∀ k ≤ 7, ∀ i < count g0Atlas k, checkRow g0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all0_2 i (by omega) hi
  · exact all0_3 i (by omega) hi
  · exact all0_4 i (by omega) hi
  · exact all0_5 i (by omega) hi
  · exact all0_6 i (by omega) hi
  · exact all0_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_2_0 : Interval g1Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem all1_2 : Interval g1Atlas 2 0 5 := b1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_3_0 : Interval g1Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_3_16 : Interval g1Atlas 3 16 9 := block_range (n:=9) (by decide +kernel)
theorem all1_3 : Interval g1Atlas 3 0 25 := (concat b1_3_0 b1_3_16)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_4_0 : Interval g1Atlas 4 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_4_16 : Interval g1Atlas 4 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_4_32 : Interval g1Atlas 4 32 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_4_48 : Interval g1Atlas 4 48 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_4_64 : Interval g1Atlas 4 64 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_4_80 : Interval g1Atlas 4 80 11 := block_range (n:=11) (by decide +kernel)
theorem all1_4 : Interval g1Atlas 4 0 91 := (concat (concat b1_4_0 (concat b1_4_16 b1_4_32)) (concat b1_4_48 (concat b1_4_64 b1_4_80)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_5_0 : Interval g1Atlas 5 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_5_16 : Interval g1Atlas 5 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_5_32 : Interval g1Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem all1_5 : Interval g1Atlas 5 0 44 := (concat b1_5_0 (concat b1_5_16 b1_5_32))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_6_0 : Interval g1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all1_6 : Interval g1Atlas 6 0 1 := b1_6_0
theorem all1 : ∀ k ≤ 6, ∀ i < count g1Atlas k, checkRow g1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all1_2 i (by omega) hi
  · exact all1_3 i (by omega) hi
  · exact all1_4 i (by omega) hi
  · exact all1_5 i (by omega) hi
  · exact all1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_2_0 : Interval g2Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem all2_2 : Interval g2Atlas 2 0 5 := b2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_3_0 : Interval g2Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_3_16 : Interval g2Atlas 3 16 9 := block_range (n:=9) (by decide +kernel)
theorem all2_3 : Interval g2Atlas 3 0 25 := (concat b2_3_0 b2_3_16)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_4_0 : Interval g2Atlas 4 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_4_16 : Interval g2Atlas 4 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_4_32 : Interval g2Atlas 4 32 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_4_48 : Interval g2Atlas 4 48 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_4_64 : Interval g2Atlas 4 64 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_4_80 : Interval g2Atlas 4 80 11 := block_range (n:=11) (by decide +kernel)
theorem all2_4 : Interval g2Atlas 4 0 91 := (concat (concat b2_4_0 (concat b2_4_16 b2_4_32)) (concat b2_4_48 (concat b2_4_64 b2_4_80)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_5_0 : Interval g2Atlas 5 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_5_16 : Interval g2Atlas 5 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_5_32 : Interval g2Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem all2_5 : Interval g2Atlas 5 0 44 := (concat b2_5_0 (concat b2_5_16 b2_5_32))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_6_0 : Interval g2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all2_6 : Interval g2Atlas 6 0 1 := b2_6_0
theorem all2 : ∀ k ≤ 6, ∀ i < count g2Atlas k, checkRow g2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all2_2 i (by omega) hi
  · exact all2_3 i (by omega) hi
  · exact all2_4 i (by omega) hi
  · exact all2_5 i (by omega) hi
  · exact all2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_4_0 : Interval g3Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem all3_4 : Interval g3Atlas 4 0 2 := b3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_5_0 : Interval g3Atlas 5 0 8 := block_range (n:=8) (by decide +kernel)
theorem all3_5 : Interval g3Atlas 5 0 8 := b3_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_6_0 : Interval g3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all3_6 : Interval g3Atlas 6 0 1 := b3_6_0
theorem all3 : ∀ k ≤ 6, ∀ i < count g3Atlas k, checkRow g3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all3_4 i (by omega) hi
  · exact all3_5 i (by omega) hi
  · exact all3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_3_0 : Interval g4Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem all4_3 : Interval g4Atlas 3 0 1 := b4_3_0
theorem all4 : ∀ k ≤ 3, ∀ i < count g4Atlas k, checkRow g4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all4_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_4_0 : Interval g5Atlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem all5_4 : Interval g5Atlas 4 0 4 := b5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_5_0 : Interval g5Atlas 5 0 8 := block_range (n:=8) (by decide +kernel)
theorem all5_5 : Interval g5Atlas 5 0 8 := b5_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_6_0 : Interval g5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all5_6 : Interval g5Atlas 6 0 1 := b5_6_0
theorem all5 : ∀ k ≤ 6, ∀ i < count g5Atlas k, checkRow g5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all5_4 i (by omega) hi
  · exact all5_5 i (by omega) hi
  · exact all5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_3_0 : Interval g6Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem all6_3 : Interval g6Atlas 3 0 1 := b6_3_0
theorem all6 : ∀ k ≤ 3, ∀ i < count g6Atlas k, checkRow g6Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all6_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b7_3_0 : Interval g7Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem all7_3 : Interval g7Atlas 3 0 4 := b7_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b7_4_0 : Interval g7Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem all7_4 : Interval g7Atlas 4 0 6 := b7_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b7_5_0 : Interval g7Atlas 5 0 16 := block_range (n:=16) (by decide +kernel)
theorem all7_5 : Interval g7Atlas 5 0 16 := b7_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b7_6_0 : Interval g7Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all7_6 : Interval g7Atlas 6 0 1 := b7_6_0
theorem all7 : ∀ k ≤ 6, ∀ i < count g7Atlas k, checkRow g7Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all7_3 i (by omega) hi
  · exact all7_4 i (by omega) hi
  · exact all7_5 i (by omega) hi
  · exact all7_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b8_3_0 : Interval g8Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem all8_3 : Interval g8Atlas 3 0 1 := b8_3_0
theorem all8 : ∀ k ≤ 3, ∀ i < count g8Atlas k, checkRow g8Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all8_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b9_3_0 : Interval g9Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem all9_3 : Interval g9Atlas 3 0 1 := b9_3_0
theorem all9 : ∀ k ≤ 3, ∀ i < count g9Atlas k, checkRow g9Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all9_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b10_2_0 : Interval g10Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem all10_2 : Interval g10Atlas 2 0 5 := b10_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b10_3_0 : Interval g10Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b10_3_16 : Interval g10Atlas 3 16 9 := block_range (n:=9) (by decide +kernel)
theorem all10_3 : Interval g10Atlas 3 0 25 := (concat b10_3_0 b10_3_16)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b10_4_0 : Interval g10Atlas 4 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b10_4_16 : Interval g10Atlas 4 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b10_4_32 : Interval g10Atlas 4 32 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b10_4_48 : Interval g10Atlas 4 48 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b10_4_64 : Interval g10Atlas 4 64 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b10_4_80 : Interval g10Atlas 4 80 11 := block_range (n:=11) (by decide +kernel)
theorem all10_4 : Interval g10Atlas 4 0 91 := (concat (concat b10_4_0 (concat b10_4_16 b10_4_32)) (concat b10_4_48 (concat b10_4_64 b10_4_80)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b10_5_0 : Interval g10Atlas 5 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b10_5_16 : Interval g10Atlas 5 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b10_5_32 : Interval g10Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem all10_5 : Interval g10Atlas 5 0 44 := (concat b10_5_0 (concat b10_5_16 b10_5_32))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b10_6_0 : Interval g10Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all10_6 : Interval g10Atlas 6 0 1 := b10_6_0
theorem all10 : ∀ k ≤ 6, ∀ i < count g10Atlas k, checkRow g10Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all10_2 i (by omega) hi
  · exact all10_3 i (by omega) hi
  · exact all10_4 i (by omega) hi
  · exact all10_5 i (by omega) hi
  · exact all10_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b11_2_0 : Interval g11Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem all11_2 : Interval g11Atlas 2 0 5 := b11_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b11_3_0 : Interval g11Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b11_3_16 : Interval g11Atlas 3 16 9 := block_range (n:=9) (by decide +kernel)
theorem all11_3 : Interval g11Atlas 3 0 25 := (concat b11_3_0 b11_3_16)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b11_4_0 : Interval g11Atlas 4 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b11_4_16 : Interval g11Atlas 4 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b11_4_32 : Interval g11Atlas 4 32 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b11_4_48 : Interval g11Atlas 4 48 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b11_4_64 : Interval g11Atlas 4 64 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b11_4_80 : Interval g11Atlas 4 80 11 := block_range (n:=11) (by decide +kernel)
theorem all11_4 : Interval g11Atlas 4 0 91 := (concat (concat b11_4_0 (concat b11_4_16 b11_4_32)) (concat b11_4_48 (concat b11_4_64 b11_4_80)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b11_5_0 : Interval g11Atlas 5 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b11_5_16 : Interval g11Atlas 5 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b11_5_32 : Interval g11Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem all11_5 : Interval g11Atlas 5 0 44 := (concat b11_5_0 (concat b11_5_16 b11_5_32))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b11_6_0 : Interval g11Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all11_6 : Interval g11Atlas 6 0 1 := b11_6_0
theorem all11 : ∀ k ≤ 6, ∀ i < count g11Atlas k, checkRow g11Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all11_2 i (by omega) hi
  · exact all11_3 i (by omega) hi
  · exact all11_4 i (by omega) hi
  · exact all11_5 i (by omega) hi
  · exact all11_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_3_0 : Interval g12Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem all12_3 : Interval g12Atlas 3 0 6 := b12_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_4_0 : Interval g12Atlas 4 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_4_16 : Interval g12Atlas 4 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_4_32 : Interval g12Atlas 4 32 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_4_48 : Interval g12Atlas 4 48 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_4_64 : Interval g12Atlas 4 64 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_4_80 : Interval g12Atlas 4 80 9 := block_range (n:=9) (by decide +kernel)
theorem all12_4 : Interval g12Atlas 4 0 89 := (concat (concat b12_4_0 (concat b12_4_16 b12_4_32)) (concat b12_4_48 (concat b12_4_64 b12_4_80)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_0 : Interval g12Atlas 5 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_16 : Interval g12Atlas 5 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_32 : Interval g12Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_48 : Interval g12Atlas 5 48 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_64 : Interval g12Atlas 5 64 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_80 : Interval g12Atlas 5 80 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_96 : Interval g12Atlas 5 96 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_112 : Interval g12Atlas 5 112 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_128 : Interval g12Atlas 5 128 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_144 : Interval g12Atlas 5 144 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_160 : Interval g12Atlas 5 160 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_176 : Interval g12Atlas 5 176 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_192 : Interval g12Atlas 5 192 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_208 : Interval g12Atlas 5 208 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_224 : Interval g12Atlas 5 224 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_240 : Interval g12Atlas 5 240 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_256 : Interval g12Atlas 5 256 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_5_272 : Interval g12Atlas 5 272 8 := block_range (n:=8) (by decide +kernel)
theorem all12_5 : Interval g12Atlas 5 0 280 := (concat (concat (concat (concat b12_5_0 b12_5_16) (concat b12_5_32 b12_5_48)) (concat (concat b12_5_64 b12_5_80) (concat b12_5_96 (concat b12_5_112 b12_5_128)))) (concat (concat (concat b12_5_144 b12_5_160) (concat b12_5_176 b12_5_192)) (concat (concat b12_5_208 b12_5_224) (concat b12_5_240 (concat b12_5_256 b12_5_272)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_6_0 : Interval g12Atlas 6 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_6_16 : Interval g12Atlas 6 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_6_32 : Interval g12Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_6_48 : Interval g12Atlas 6 48 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_6_64 : Interval g12Atlas 6 64 8 := block_range (n:=8) (by decide +kernel)
theorem all12_6 : Interval g12Atlas 6 0 72 := (concat (concat b12_6_0 b12_6_16) (concat b12_6_32 (concat b12_6_48 b12_6_64)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b12_7_0 : Interval g12Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem all12_7 : Interval g12Atlas 7 0 1 := b12_7_0
theorem all12 : ∀ k ≤ 7, ∀ i < count g12Atlas k, checkRow g12Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all12_3 i (by omega) hi
  · exact all12_4 i (by omega) hi
  · exact all12_5 i (by omega) hi
  · exact all12_6 i (by omega) hi
  · exact all12_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b13_3_0 : Interval g13Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem all13_3 : Interval g13Atlas 3 0 1 := b13_3_0
theorem all13 : ∀ k ≤ 3, ∀ i < count g13Atlas k, checkRow g13Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all13_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b14_3_0 : Interval g14Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem all14_3 : Interval g14Atlas 3 0 1 := b14_3_0
theorem all14 : ∀ k ≤ 3, ∀ i < count g14Atlas k, checkRow g14Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all14_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b15_3_0 : Interval g15Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem all15_3 : Interval g15Atlas 3 0 1 := b15_3_0
theorem all15 : ∀ k ≤ 3, ∀ i < count g15Atlas k, checkRow g15Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all15_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b16_3_0 : Interval g16Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem all16_3 : Interval g16Atlas 3 0 2 := b16_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b16_4_0 : Interval g16Atlas 4 0 8 := block_range (n:=8) (by decide +kernel)
theorem all16_4 : Interval g16Atlas 4 0 8 := b16_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b16_5_0 : Interval g16Atlas 5 0 14 := block_range (n:=14) (by decide +kernel)
theorem all16_5 : Interval g16Atlas 5 0 14 := b16_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b16_6_0 : Interval g16Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all16_6 : Interval g16Atlas 6 0 1 := b16_6_0
theorem all16 : ∀ k ≤ 6, ∀ i < count g16Atlas k, checkRow g16Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all16_3 i (by omega) hi
  · exact all16_4 i (by omega) hi
  · exact all16_5 i (by omega) hi
  · exact all16_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_5_0 : Interval g17Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem all17_5 : Interval g17Atlas 5 0 1 := b17_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_6_0 : Interval g17Atlas 6 0 16 := block_range (n:=16) (by decide +kernel)
theorem all17_6 : Interval g17Atlas 6 0 16 := b17_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_0 : Interval g17Atlas 7 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_16 : Interval g17Atlas 7 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_32 : Interval g17Atlas 7 32 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_48 : Interval g17Atlas 7 48 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_64 : Interval g17Atlas 7 64 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_80 : Interval g17Atlas 7 80 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_96 : Interval g17Atlas 7 96 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_112 : Interval g17Atlas 7 112 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_128 : Interval g17Atlas 7 128 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_144 : Interval g17Atlas 7 144 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_160 : Interval g17Atlas 7 160 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_176 : Interval g17Atlas 7 176 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_192 : Interval g17Atlas 7 192 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_208 : Interval g17Atlas 7 208 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_224 : Interval g17Atlas 7 224 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_240 : Interval g17Atlas 7 240 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_256 : Interval g17Atlas 7 256 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_272 : Interval g17Atlas 7 272 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_288 : Interval g17Atlas 7 288 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_304 : Interval g17Atlas 7 304 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_320 : Interval g17Atlas 7 320 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_336 : Interval g17Atlas 7 336 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_7_352 : Interval g17Atlas 7 352 12 := block_range (n:=12) (by decide +kernel)
theorem all17_7 : Interval g17Atlas 7 0 364 := (concat (concat (concat (concat b17_7_0 b17_7_16) (concat b17_7_32 (concat b17_7_48 b17_7_64))) (concat (concat b17_7_80 (concat b17_7_96 b17_7_112)) (concat b17_7_128 (concat b17_7_144 b17_7_160)))) (concat (concat (concat b17_7_176 (concat b17_7_192 b17_7_208)) (concat b17_7_224 (concat b17_7_240 b17_7_256))) (concat (concat b17_7_272 (concat b17_7_288 b17_7_304)) (concat b17_7_320 (concat b17_7_336 b17_7_352)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_0 : Interval g17Atlas 8 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_16 : Interval g17Atlas 8 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_32 : Interval g17Atlas 8 32 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_48 : Interval g17Atlas 8 48 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_64 : Interval g17Atlas 8 64 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_80 : Interval g17Atlas 8 80 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_96 : Interval g17Atlas 8 96 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_112 : Interval g17Atlas 8 112 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_128 : Interval g17Atlas 8 128 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_144 : Interval g17Atlas 8 144 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_160 : Interval g17Atlas 8 160 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_176 : Interval g17Atlas 8 176 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_192 : Interval g17Atlas 8 192 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_208 : Interval g17Atlas 8 208 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_224 : Interval g17Atlas 8 224 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_240 : Interval g17Atlas 8 240 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_256 : Interval g17Atlas 8 256 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_272 : Interval g17Atlas 8 272 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_288 : Interval g17Atlas 8 288 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_304 : Interval g17Atlas 8 304 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_320 : Interval g17Atlas 8 320 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_336 : Interval g17Atlas 8 336 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_352 : Interval g17Atlas 8 352 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_368 : Interval g17Atlas 8 368 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_384 : Interval g17Atlas 8 384 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_400 : Interval g17Atlas 8 400 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_416 : Interval g17Atlas 8 416 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_432 : Interval g17Atlas 8 432 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_448 : Interval g17Atlas 8 448 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_464 : Interval g17Atlas 8 464 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_480 : Interval g17Atlas 8 480 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_496 : Interval g17Atlas 8 496 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_512 : Interval g17Atlas 8 512 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_528 : Interval g17Atlas 8 528 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_544 : Interval g17Atlas 8 544 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_560 : Interval g17Atlas 8 560 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_576 : Interval g17Atlas 8 576 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_592 : Interval g17Atlas 8 592 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_608 : Interval g17Atlas 8 608 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_624 : Interval g17Atlas 8 624 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_640 : Interval g17Atlas 8 640 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_656 : Interval g17Atlas 8 656 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_672 : Interval g17Atlas 8 672 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_688 : Interval g17Atlas 8 688 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_704 : Interval g17Atlas 8 704 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_720 : Interval g17Atlas 8 720 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_736 : Interval g17Atlas 8 736 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_752 : Interval g17Atlas 8 752 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_768 : Interval g17Atlas 8 768 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_784 : Interval g17Atlas 8 784 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_800 : Interval g17Atlas 8 800 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_816 : Interval g17Atlas 8 816 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_832 : Interval g17Atlas 8 832 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_848 : Interval g17Atlas 8 848 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_864 : Interval g17Atlas 8 864 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_880 : Interval g17Atlas 8 880 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_896 : Interval g17Atlas 8 896 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_912 : Interval g17Atlas 8 912 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_928 : Interval g17Atlas 8 928 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_944 : Interval g17Atlas 8 944 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_960 : Interval g17Atlas 8 960 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_976 : Interval g17Atlas 8 976 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_992 : Interval g17Atlas 8 992 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1008 : Interval g17Atlas 8 1008 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1024 : Interval g17Atlas 8 1024 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1040 : Interval g17Atlas 8 1040 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1056 : Interval g17Atlas 8 1056 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1072 : Interval g17Atlas 8 1072 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1088 : Interval g17Atlas 8 1088 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1104 : Interval g17Atlas 8 1104 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1120 : Interval g17Atlas 8 1120 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1136 : Interval g17Atlas 8 1136 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1152 : Interval g17Atlas 8 1152 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1168 : Interval g17Atlas 8 1168 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1184 : Interval g17Atlas 8 1184 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1200 : Interval g17Atlas 8 1200 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1216 : Interval g17Atlas 8 1216 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1232 : Interval g17Atlas 8 1232 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1248 : Interval g17Atlas 8 1248 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1264 : Interval g17Atlas 8 1264 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1280 : Interval g17Atlas 8 1280 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1296 : Interval g17Atlas 8 1296 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1312 : Interval g17Atlas 8 1312 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1328 : Interval g17Atlas 8 1328 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1344 : Interval g17Atlas 8 1344 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1360 : Interval g17Atlas 8 1360 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1376 : Interval g17Atlas 8 1376 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1392 : Interval g17Atlas 8 1392 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1408 : Interval g17Atlas 8 1408 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1424 : Interval g17Atlas 8 1424 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1440 : Interval g17Atlas 8 1440 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1456 : Interval g17Atlas 8 1456 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1472 : Interval g17Atlas 8 1472 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1488 : Interval g17Atlas 8 1488 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1504 : Interval g17Atlas 8 1504 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1520 : Interval g17Atlas 8 1520 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1536 : Interval g17Atlas 8 1536 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1552 : Interval g17Atlas 8 1552 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1568 : Interval g17Atlas 8 1568 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1584 : Interval g17Atlas 8 1584 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1600 : Interval g17Atlas 8 1600 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1616 : Interval g17Atlas 8 1616 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1632 : Interval g17Atlas 8 1632 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1648 : Interval g17Atlas 8 1648 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1664 : Interval g17Atlas 8 1664 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1680 : Interval g17Atlas 8 1680 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1696 : Interval g17Atlas 8 1696 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1712 : Interval g17Atlas 8 1712 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1728 : Interval g17Atlas 8 1728 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1744 : Interval g17Atlas 8 1744 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1760 : Interval g17Atlas 8 1760 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1776 : Interval g17Atlas 8 1776 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1792 : Interval g17Atlas 8 1792 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1808 : Interval g17Atlas 8 1808 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1824 : Interval g17Atlas 8 1824 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1840 : Interval g17Atlas 8 1840 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1856 : Interval g17Atlas 8 1856 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1872 : Interval g17Atlas 8 1872 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1888 : Interval g17Atlas 8 1888 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_8_1904 : Interval g17Atlas 8 1904 5 := block_range (n:=5) (by decide +kernel)
theorem all17_8 : Interval g17Atlas 8 0 1909 := (concat (concat (concat (concat (concat (concat b17_8_0 (concat b17_8_16 b17_8_32)) (concat (concat b17_8_48 b17_8_64) (concat b17_8_80 b17_8_96))) (concat (concat (concat b17_8_112 b17_8_128) (concat b17_8_144 b17_8_160)) (concat (concat b17_8_176 b17_8_192) (concat b17_8_208 b17_8_224)))) (concat (concat (concat b17_8_240 (concat b17_8_256 b17_8_272)) (concat (concat b17_8_288 b17_8_304) (concat b17_8_320 b17_8_336))) (concat (concat (concat b17_8_352 b17_8_368) (concat b17_8_384 b17_8_400)) (concat (concat b17_8_416 b17_8_432) (concat b17_8_448 b17_8_464))))) (concat (concat (concat (concat b17_8_480 (concat b17_8_496 b17_8_512)) (concat (concat b17_8_528 b17_8_544) (concat b17_8_560 b17_8_576))) (concat (concat (concat b17_8_592 b17_8_608) (concat b17_8_624 b17_8_640)) (concat (concat b17_8_656 b17_8_672) (concat b17_8_688 b17_8_704)))) (concat (concat (concat b17_8_720 (concat b17_8_736 b17_8_752)) (concat (concat b17_8_768 b17_8_784) (concat b17_8_800 b17_8_816))) (concat (concat (concat b17_8_832 b17_8_848) (concat b17_8_864 b17_8_880)) (concat (concat b17_8_896 b17_8_912) (concat b17_8_928 b17_8_944)))))) (concat (concat (concat (concat (concat b17_8_960 (concat b17_8_976 b17_8_992)) (concat (concat b17_8_1008 b17_8_1024) (concat b17_8_1040 b17_8_1056))) (concat (concat (concat b17_8_1072 b17_8_1088) (concat b17_8_1104 b17_8_1120)) (concat (concat b17_8_1136 b17_8_1152) (concat b17_8_1168 b17_8_1184)))) (concat (concat (concat b17_8_1200 (concat b17_8_1216 b17_8_1232)) (concat (concat b17_8_1248 b17_8_1264) (concat b17_8_1280 b17_8_1296))) (concat (concat (concat b17_8_1312 b17_8_1328) (concat b17_8_1344 b17_8_1360)) (concat (concat b17_8_1376 b17_8_1392) (concat b17_8_1408 b17_8_1424))))) (concat (concat (concat (concat b17_8_1440 (concat b17_8_1456 b17_8_1472)) (concat (concat b17_8_1488 b17_8_1504) (concat b17_8_1520 b17_8_1536))) (concat (concat (concat b17_8_1552 b17_8_1568) (concat b17_8_1584 b17_8_1600)) (concat (concat b17_8_1616 b17_8_1632) (concat b17_8_1648 b17_8_1664)))) (concat (concat (concat b17_8_1680 (concat b17_8_1696 b17_8_1712)) (concat (concat b17_8_1728 b17_8_1744) (concat b17_8_1760 b17_8_1776))) (concat (concat (concat b17_8_1792 b17_8_1808) (concat b17_8_1824 b17_8_1840)) (concat (concat b17_8_1856 b17_8_1872) (concat b17_8_1888 b17_8_1904)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_0 : Interval g17Atlas 9 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_16 : Interval g17Atlas 9 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_32 : Interval g17Atlas 9 32 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_48 : Interval g17Atlas 9 48 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_64 : Interval g17Atlas 9 64 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_80 : Interval g17Atlas 9 80 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_96 : Interval g17Atlas 9 96 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_112 : Interval g17Atlas 9 112 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_128 : Interval g17Atlas 9 128 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_144 : Interval g17Atlas 9 144 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_160 : Interval g17Atlas 9 160 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_176 : Interval g17Atlas 9 176 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_192 : Interval g17Atlas 9 192 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_208 : Interval g17Atlas 9 208 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_224 : Interval g17Atlas 9 224 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_240 : Interval g17Atlas 9 240 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_256 : Interval g17Atlas 9 256 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_272 : Interval g17Atlas 9 272 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_288 : Interval g17Atlas 9 288 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_304 : Interval g17Atlas 9 304 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_320 : Interval g17Atlas 9 320 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_336 : Interval g17Atlas 9 336 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_352 : Interval g17Atlas 9 352 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_368 : Interval g17Atlas 9 368 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_384 : Interval g17Atlas 9 384 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_400 : Interval g17Atlas 9 400 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_416 : Interval g17Atlas 9 416 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_432 : Interval g17Atlas 9 432 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_448 : Interval g17Atlas 9 448 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_464 : Interval g17Atlas 9 464 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_480 : Interval g17Atlas 9 480 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_496 : Interval g17Atlas 9 496 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_512 : Interval g17Atlas 9 512 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_528 : Interval g17Atlas 9 528 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_544 : Interval g17Atlas 9 544 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_560 : Interval g17Atlas 9 560 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_576 : Interval g17Atlas 9 576 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_592 : Interval g17Atlas 9 592 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_608 : Interval g17Atlas 9 608 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_624 : Interval g17Atlas 9 624 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_640 : Interval g17Atlas 9 640 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_656 : Interval g17Atlas 9 656 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_672 : Interval g17Atlas 9 672 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_688 : Interval g17Atlas 9 688 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_704 : Interval g17Atlas 9 704 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_720 : Interval g17Atlas 9 720 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_736 : Interval g17Atlas 9 736 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_752 : Interval g17Atlas 9 752 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_768 : Interval g17Atlas 9 768 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_784 : Interval g17Atlas 9 784 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_800 : Interval g17Atlas 9 800 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_816 : Interval g17Atlas 9 816 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_832 : Interval g17Atlas 9 832 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_848 : Interval g17Atlas 9 848 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_864 : Interval g17Atlas 9 864 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_880 : Interval g17Atlas 9 880 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_896 : Interval g17Atlas 9 896 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_912 : Interval g17Atlas 9 912 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_928 : Interval g17Atlas 9 928 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_944 : Interval g17Atlas 9 944 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_960 : Interval g17Atlas 9 960 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_976 : Interval g17Atlas 9 976 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_992 : Interval g17Atlas 9 992 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1008 : Interval g17Atlas 9 1008 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1024 : Interval g17Atlas 9 1024 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1040 : Interval g17Atlas 9 1040 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1056 : Interval g17Atlas 9 1056 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1072 : Interval g17Atlas 9 1072 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1088 : Interval g17Atlas 9 1088 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1104 : Interval g17Atlas 9 1104 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1120 : Interval g17Atlas 9 1120 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1136 : Interval g17Atlas 9 1136 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1152 : Interval g17Atlas 9 1152 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1168 : Interval g17Atlas 9 1168 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1184 : Interval g17Atlas 9 1184 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1200 : Interval g17Atlas 9 1200 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1216 : Interval g17Atlas 9 1216 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1232 : Interval g17Atlas 9 1232 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1248 : Interval g17Atlas 9 1248 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1264 : Interval g17Atlas 9 1264 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1280 : Interval g17Atlas 9 1280 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1296 : Interval g17Atlas 9 1296 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1312 : Interval g17Atlas 9 1312 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1328 : Interval g17Atlas 9 1328 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1344 : Interval g17Atlas 9 1344 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1360 : Interval g17Atlas 9 1360 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1376 : Interval g17Atlas 9 1376 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1392 : Interval g17Atlas 9 1392 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1408 : Interval g17Atlas 9 1408 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1424 : Interval g17Atlas 9 1424 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1440 : Interval g17Atlas 9 1440 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1456 : Interval g17Atlas 9 1456 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1472 : Interval g17Atlas 9 1472 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1488 : Interval g17Atlas 9 1488 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1504 : Interval g17Atlas 9 1504 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1520 : Interval g17Atlas 9 1520 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1536 : Interval g17Atlas 9 1536 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1552 : Interval g17Atlas 9 1552 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1568 : Interval g17Atlas 9 1568 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1584 : Interval g17Atlas 9 1584 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1600 : Interval g17Atlas 9 1600 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1616 : Interval g17Atlas 9 1616 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1632 : Interval g17Atlas 9 1632 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1648 : Interval g17Atlas 9 1648 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1664 : Interval g17Atlas 9 1664 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1680 : Interval g17Atlas 9 1680 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1696 : Interval g17Atlas 9 1696 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1712 : Interval g17Atlas 9 1712 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1728 : Interval g17Atlas 9 1728 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1744 : Interval g17Atlas 9 1744 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1760 : Interval g17Atlas 9 1760 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1776 : Interval g17Atlas 9 1776 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1792 : Interval g17Atlas 9 1792 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1808 : Interval g17Atlas 9 1808 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1824 : Interval g17Atlas 9 1824 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1840 : Interval g17Atlas 9 1840 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1856 : Interval g17Atlas 9 1856 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1872 : Interval g17Atlas 9 1872 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1888 : Interval g17Atlas 9 1888 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1904 : Interval g17Atlas 9 1904 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1920 : Interval g17Atlas 9 1920 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1936 : Interval g17Atlas 9 1936 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1952 : Interval g17Atlas 9 1952 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1968 : Interval g17Atlas 9 1968 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_1984 : Interval g17Atlas 9 1984 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_2000 : Interval g17Atlas 9 2000 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_2016 : Interval g17Atlas 9 2016 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_2032 : Interval g17Atlas 9 2032 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_2048 : Interval g17Atlas 9 2048 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_2064 : Interval g17Atlas 9 2064 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_2080 : Interval g17Atlas 9 2080 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_2096 : Interval g17Atlas 9 2096 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_2112 : Interval g17Atlas 9 2112 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_2128 : Interval g17Atlas 9 2128 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_9_2144 : Interval g17Atlas 9 2144 16 := block_range (n:=16) (by decide +kernel)
theorem all17_9 : Interval g17Atlas 9 0 2160 := (concat (concat (concat (concat (concat (concat (concat b17_9_0 b17_9_16) (concat b17_9_32 b17_9_48)) (concat (concat b17_9_64 b17_9_80) (concat b17_9_96 b17_9_112))) (concat (concat (concat b17_9_128 b17_9_144) (concat b17_9_160 b17_9_176)) (concat (concat b17_9_192 b17_9_208) (concat b17_9_224 b17_9_240)))) (concat (concat (concat (concat b17_9_256 b17_9_272) (concat b17_9_288 b17_9_304)) (concat (concat b17_9_320 b17_9_336) (concat b17_9_352 b17_9_368))) (concat (concat (concat b17_9_384 b17_9_400) (concat b17_9_416 b17_9_432)) (concat (concat b17_9_448 b17_9_464) (concat b17_9_480 (concat b17_9_496 b17_9_512)))))) (concat (concat (concat (concat (concat b17_9_528 b17_9_544) (concat b17_9_560 b17_9_576)) (concat (concat b17_9_592 b17_9_608) (concat b17_9_624 b17_9_640))) (concat (concat (concat b17_9_656 b17_9_672) (concat b17_9_688 b17_9_704)) (concat (concat b17_9_720 b17_9_736) (concat b17_9_752 (concat b17_9_768 b17_9_784))))) (concat (concat (concat (concat b17_9_800 b17_9_816) (concat b17_9_832 b17_9_848)) (concat (concat b17_9_864 b17_9_880) (concat b17_9_896 b17_9_912))) (concat (concat (concat b17_9_928 b17_9_944) (concat b17_9_960 b17_9_976)) (concat (concat b17_9_992 b17_9_1008) (concat b17_9_1024 (concat b17_9_1040 b17_9_1056))))))) (concat (concat (concat (concat (concat (concat b17_9_1072 b17_9_1088) (concat b17_9_1104 b17_9_1120)) (concat (concat b17_9_1136 b17_9_1152) (concat b17_9_1168 b17_9_1184))) (concat (concat (concat b17_9_1200 b17_9_1216) (concat b17_9_1232 b17_9_1248)) (concat (concat b17_9_1264 b17_9_1280) (concat b17_9_1296 (concat b17_9_1312 b17_9_1328))))) (concat (concat (concat (concat b17_9_1344 b17_9_1360) (concat b17_9_1376 b17_9_1392)) (concat (concat b17_9_1408 b17_9_1424) (concat b17_9_1440 b17_9_1456))) (concat (concat (concat b17_9_1472 b17_9_1488) (concat b17_9_1504 b17_9_1520)) (concat (concat b17_9_1536 b17_9_1552) (concat b17_9_1568 (concat b17_9_1584 b17_9_1600)))))) (concat (concat (concat (concat (concat b17_9_1616 b17_9_1632) (concat b17_9_1648 b17_9_1664)) (concat (concat b17_9_1680 b17_9_1696) (concat b17_9_1712 b17_9_1728))) (concat (concat (concat b17_9_1744 b17_9_1760) (concat b17_9_1776 b17_9_1792)) (concat (concat b17_9_1808 b17_9_1824) (concat b17_9_1840 (concat b17_9_1856 b17_9_1872))))) (concat (concat (concat (concat b17_9_1888 b17_9_1904) (concat b17_9_1920 b17_9_1936)) (concat (concat b17_9_1952 b17_9_1968) (concat b17_9_1984 b17_9_2000))) (concat (concat (concat b17_9_2016 b17_9_2032) (concat b17_9_2048 b17_9_2064)) (concat (concat b17_9_2080 b17_9_2096) (concat b17_9_2112 (concat b17_9_2128 b17_9_2144))))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_10_0 : Interval g17Atlas 10 0 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_10_16 : Interval g17Atlas 10 16 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_10_32 : Interval g17Atlas 10 32 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_10_48 : Interval g17Atlas 10 48 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_10_64 : Interval g17Atlas 10 64 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_10_80 : Interval g17Atlas 10 80 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_10_96 : Interval g17Atlas 10 96 16 := block_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_10_112 : Interval g17Atlas 10 112 4 := block_range (n:=4) (by decide +kernel)
theorem all17_10 : Interval g17Atlas 10 0 116 := (concat (concat (concat b17_10_0 b17_10_16) (concat b17_10_32 b17_10_48)) (concat (concat b17_10_64 b17_10_80) (concat b17_10_96 b17_10_112)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b17_11_0 : Interval g17Atlas 11 0 1 := block_range (n:=1) (by decide +kernel)
theorem all17_11 : Interval g17Atlas 11 0 1 := b17_11_0
theorem all17 : ∀ k ≤ 11, ∀ i < count g17Atlas k, checkRow g17Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all17_5 i (by omega) hi
  · exact all17_6 i (by omega) hi
  · exact all17_7 i (by omega) hi
  · exact all17_8 i (by omega) hi
  · exact all17_9 i (by omega) hi
  · exact all17_10 i (by omega) hi
  · exact all17_11 i (by omega) hi
end PEqualNP.Outside.L_meta_14286
namespace PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286.Model PEqualNP.CircuitLowerBounds
def Complete (g : Atlas) := ∀ k ≤ top g, ∀ i < count g k, checkRow g k i = true
theorem frozen {g : Atlas} {p n} (ready : Ready g p n) (complete : Complete g)
    (atRoot : vals g (top g) 0 = roots g) (row : 0 < count g (top g))
    (xs : List (Sig × Row × Row)) (pr : proper (target g))
    (test : checkEssential (target g) (roots g) xs=true) (names : xs.map Prod.fst=roots g) :
    Lower true (roots g) (target g) (top g+1) := by
  apply lower_impossible pr (essential_plain test).1 (essential_plain test).2
  · intro a ha
    exact essential_ok test a (List.mem_toFinset.mpr (names ▸ ha))
  · rw [←atRoot]
    exact checked ready _ complete 0 row

theorem low0 : Lower true (roots g0Atlas) (target g0Atlas) 8 := by
  have ready : Ready g0Atlas (asRow g0Pos) (asRow g0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k j _ hn; exact False.elim (hn rfl)
  exact frozen ready all0 (by decide +kernel) (by decide) [(inputs.getD 2 zero,32,36),(inputs.getD 3 zero,64,72),(inputs.getD 5 zero,4,36),(inputs.getD 6 zero,8,72),(inputs.getD 7 zero,4,132)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem low1 : Lower true (roots g1Atlas) (target g1Atlas) 7 := by
  have ready : Ready g1Atlas (asRow g1Pos) (asRow g1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k j _ hn; exact False.elim (hn rfl)
  exact frozen ready all1 (by decide +kernel) (by decide) [(inputs.getD 0 zero,16,17),(inputs.getD 3 zero,64,72),(inputs.getD 4 zero,1,17),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,8,136)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem low2 : Lower true (roots g2Atlas) (target g2Atlas) 7 := by
  have ready : Ready g2Atlas (asRow g2Pos) (asRow g2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k j _ hn; exact False.elim (hn rfl)
  exact frozen ready all2 (by decide +kernel) (by decide) [(inputs.getD 0 zero,16,17),(inputs.getD 2 zero,32,36),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33),(inputs.getD 7 zero,4,132)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem low3 : Lower true (roots g3Atlas) (target g3Atlas) 7 := by
  have ready : Ready g3Atlas (asRow g3Pos) (asRow g3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k j _ hn; exact False.elim (hn rfl)
  exact frozen ready all3 (by decide +kernel) (by decide) [(inputs.getD 0 zero,16,17),(inputs.getD 1 zero,16,18),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,32,160)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem low4 : Lower true (roots g4Atlas) (target g4Atlas) 4 := by
  have ready : Ready g4Atlas (asRow g4Pos) (asRow g4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k j _ hn; exact False.elim (hn rfl)
  exact frozen ready all4 (by decide +kernel) (by decide) [(inputs.getD 0 zero,64,65),(inputs.getD 2 zero,128,132),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,4,132)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem low5 : Lower true (roots g5Atlas) (target g5Atlas) 7 := by
  have ready : Ready g5Atlas (asRow g5Pos) (asRow g5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k j _ hn; exact False.elim (hn rfl)
  exact frozen ready all5 (by decide +kernel) (by decide) [(inputs.getD 0 zero,16,17),(inputs.getD 1 zero,16,18),(inputs.getD 3 zero,128,136),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33),(inputs.getD 7 zero,8,136)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem low6 : Lower true (roots g6Atlas) (target g6Atlas) 4 := by
  have ready : Ready g6Atlas (asRow g6Pos) (asRow g6Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k j _ hn; exact False.elim (hn rfl)
  exact frozen ready all6 (by decide +kernel) (by decide) [(inputs.getD 2 zero,32,36),(inputs.getD 5 zero,4,36),(inputs.getD 7 zero,4,132)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem low7 : Lower true (roots g7Atlas) (target g7Atlas) 7 := by
  have ready : Ready g7Atlas (asRow g7Pos) (asRow g7Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k j _ hn; exact False.elim (hn rfl)
  exact frozen ready all7 (by decide +kernel) (by decide) [(inputs.getD 0 zero,16,17),(inputs.getD 1 zero,16,18),(inputs.getD 3 zero,64,72),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,1,65)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem low8 : Lower true (roots g8Atlas) (target g8Atlas) 4 := by
  have ready : Ready g8Atlas (asRow g8Pos) (asRow g8Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k j _ hn; exact False.elim (hn rfl)
  exact frozen ready all8 (by decide +kernel) (by decide) [(inputs.getD 0 zero,16,17),(inputs.getD 3 zero,64,72),(inputs.getD 4 zero,1,17),(inputs.getD 6 zero,1,65)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem low9 : Lower true (roots g9Atlas) (target g9Atlas) 4 := by
  have ready : Ready g9Atlas (asRow g9Pos) (asRow g9Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k j _ hn; exact False.elim (hn rfl)
  exact frozen ready all9 (by decide +kernel) (by decide) [(inputs.getD 0 zero,16,17),(inputs.getD 1 zero,16,18),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem low10 : Lower true (roots g10Atlas) (target g10Atlas) 7 := by
  have ready : Ready g10Atlas (asRow g10Pos) (asRow g10Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k j _ hn; exact False.elim (hn rfl)
  exact frozen ready all10 (by decide +kernel) (by decide) [(inputs.getD 1 zero,64,66),(inputs.getD 2 zero,32,36),(inputs.getD 5 zero,4,36),(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,4,132)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem low11 : Lower true (roots g11Atlas) (target g11Atlas) 7 := by
  have ready : Ready g11Atlas (asRow g11Pos) (asRow g11Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k j _ hn; exact False.elim (hn rfl)
  exact frozen ready all11 (by decide +kernel) (by decide) [(inputs.getD 1 zero,16,18),(inputs.getD 3 zero,64,72),(inputs.getD 4 zero,2,18),(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,8,136)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem low12 : Lower true (roots g12Atlas) (target g12Atlas) 8 := by
  have ready : Ready g12Atlas (asRow g12Pos) (asRow g12Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k j _ hn; exact False.elim (hn rfl)
  exact frozen ready all12 (by decide +kernel) (by decide) [(inputs.getD 0 zero,32,33),(inputs.getD 1 zero,64,66),(inputs.getD 3 zero,64,72),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,8,136)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem low13 : Lower true (roots g13Atlas) (target g13Atlas) 4 := by
  have ready : Ready g13Atlas (asRow g13Pos) (asRow g13Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k j _ hn; exact False.elim (hn rfl)
  exact frozen ready all13 (by decide +kernel) (by decide) [(inputs.getD 3 zero,64,72),(inputs.getD 6 zero,8,72),(inputs.getD 7 zero,8,136)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem low14 : Lower true (roots g14Atlas) (target g14Atlas) 4 := by
  have ready : Ready g14Atlas (asRow g14Pos) (asRow g14Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k j _ hn; exact False.elim (hn rfl)
  exact frozen ready all14 (by decide +kernel) (by decide) [(inputs.getD 0 zero,32,33),(inputs.getD 3 zero,128,136),(inputs.getD 5 zero,1,33),(inputs.getD 7 zero,8,136)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem low15 : Lower true (roots g15Atlas) (target g15Atlas) 4 := by
  have ready : Ready g15Atlas (asRow g15Pos) (asRow g15Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k j _ hn; exact False.elim (hn rfl)
  exact frozen ready all15 (by decide +kernel) (by decide) [(inputs.getD 0 zero,32,33),(inputs.getD 1 zero,64,66),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,1,65)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem low16 : Lower true (roots g16Atlas) (target g16Atlas) 7 := by
  have ready : Ready g16Atlas (asRow g16Pos) (asRow g16Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k j _ hn; exact False.elim (hn rfl)
  exact frozen ready all16 (by decide +kernel) (by decide) [(inputs.getD 0 zero,16,17),(inputs.getD 2 zero,32,36),(inputs.getD 3 zero,64,72),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,1,65)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem lift0 : Lower true [inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffffcfff0,0xfffcfffcffccffcc,0xfcfcf0f0cccc0000,0xffffffffffffffff,0xfffffffffffcfff0,0xfffcfffcffccffcc,0xfcfcf0f0cccc0000])) : Sig) 10 := by
  have lifted := lift_ok (raw:=[inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffffcfff0,0xfffcfffcffccffcc,0xfcfcf0f0cccc0000,0xffffffffffffffff,0xfffffffffffcfff0,0xfffcfffcffccffcc,0xfcfcf0f0cccc0000])) : Sig)) (base:=roots g0Atlas) (G:=target g0Atlas) (ms:=fixRows 18 0) (xs:=[(inputs.getD 1 zero,16,18),(inputs.getD 4 zero,2,18)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low0
  have charge : 8 + (([(inputs.getD 1 zero,16,18),(inputs.getD 4 zero,2,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 10 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice0 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨0,by decide⟩).1 (cutPair ⟨0,by decide⟩).2 :=
  slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift0
theorem lift1 : Lower true [inputs.getD 0 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffffafff0,0xfffafffaffaaffaa,0xfafafafaaaaa0000,0xffffffffffffffff,0xfffffffffffafff0,0xfffafffaffaaffaa,0xfafafafaaaaa0000])) : Sig) 10 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffffafff0,0xfffafffaffaaffaa,0xfafafafaaaaa0000,0xffffffffffffffff,0xfffffffffffafff0,0xfffafffaffaaffaa,0xfafafafaaaaa0000])) : Sig)) (base:=roots g0Atlas) (G:=target g0Atlas) (ms:=fixRows 17 0) (xs:=[(inputs.getD 0 zero,16,17),(inputs.getD 4 zero,1,17)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low0
  have charge : 8 + (([(inputs.getD 0 zero,16,17),(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 10 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice1 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨1,by decide⟩).1 (cutPair ⟨1,by decide⟩).2 :=
  slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift1
theorem lift2 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xffffffffffeeff00,0xffeeffeeffeeffee,0xeeeeaaaaeeee0000,0xffffffffffffffff,0xffffffffffeeff00,0xffeeffeeffeeffee,0xeeeeaaaaeeee0000])) : Sig) 9 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xffffffffffeeff00,0xffeeffeeffeeffee,0xeeeeaaaaeeee0000,0xffffffffffffffff,0xffffffffffeeff00,0xffeeffeeffeeffee,0xeeeeaaaaeeee0000])) : Sig)) (base:=roots g1Atlas) (G:=target g1Atlas) (ms:=fixRows 34 0) (xs:=[(inputs.getD 1 zero,16,18),(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low1
  have charge : 7 + (([(inputs.getD 1 zero,16,18),(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 9 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice2 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨2,by decide⟩).1 (cutPair ⟨2,by decide⟩).2 :=
  slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift2
theorem lift3 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffefef0f0,0xfefefefeeeeeeeee,0xfefefafaeeee0000,0xffffffffffffffff,0xfffffffffefef0f0,0xfefefefeeeeeeeee,0xfefefafaeeee0000])) : Sig) 9 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffefef0f0,0xfefefefeeeeeeeee,0xfefefafaeeee0000,0xffffffffffffffff,0xfffffffffefef0f0,0xfefefefeeeeeeeee,0xfefefafaeeee0000])) : Sig)) (base:=roots g2Atlas) (G:=target g2Atlas) (ms:=fixRows 66 0) (xs:=[(inputs.getD 1 zero,16,18),(inputs.getD 6 zero,1,65)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low2
  have charge : 7 + (([(inputs.getD 1 zero,16,18),(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 9 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice3 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨3,by decide⟩).1 (cutPair ⟨3,by decide⟩).2 :=
  slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift3
theorem lift4 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffff0fff0,0xfffefffeffeeffee,0xfafafafa00000000,0xffffffffffffffff,0xfffffffffff0fff0,0xfffefffeffeeffee,0xfafafafa00000000])) : Sig) 10 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffff0fff0,0xfffefffeffeeffee,0xfafafafa00000000,0xffffffffffffffff,0xfffffffffff0fff0,0xfffefffeffeeffee,0xfafafafa00000000])) : Sig)) (base:=roots g0Atlas) (G:=target g0Atlas) (ms:=fixRows 3 0) (xs:=[(inputs.getD 0 zero,32,33),(inputs.getD 1 zero,64,66)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low0
  have charge : 8 + (([(inputs.getD 0 zero,32,33),(inputs.getD 1 zero,64,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 10 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice4 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨4,by decide⟩).1 (cutPair ⟨4,by decide⟩).2 :=
  slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift4
theorem lift5 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffefff0fffefff0,0xffeeffeeffeeffee,0xeeee0000eeee0000,0xffffffffffffffff,0xfffefff0fffefff0,0xffeeffeeffeeffee,0xeeee0000eeee0000])) : Sig) 9 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffefff0fffefff0,0xffeeffeeffeeffee,0xeeee0000eeee0000,0xffffffffffffffff,0xfffefff0fffefff0,0xffeeffeeffeeffee,0xeeee0000eeee0000])) : Sig)) (base:=roots g1Atlas) (G:=target g1Atlas) (ms:=fixRows 6 0) (xs:=[(inputs.getD 1 zero,16,18),(inputs.getD 2 zero,128,132)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low1
  have charge : 7 + (([(inputs.getD 1 zero,16,18),(inputs.getD 2 zero,128,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 9 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice5 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨5,by decide⟩).1 (cutPair ⟨5,by decide⟩).2 :=
  slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift5
theorem lift6 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xfffffffffffefff0,0xfffffffffffefff0,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfffffffffffefff0,0xfffffffffffefff0,0xfefefafaeeee0000,0xfefefafaeeee0000])) : Sig) 9 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xfffffffffffefff0,0xfffffffffffefff0,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfffffffffffefff0,0xfffffffffffefff0,0xfefefafaeeee0000,0xfefefafaeeee0000])) : Sig)) (base:=roots g2Atlas) (G:=target g2Atlas) (ms:=fixRows 10 0) (xs:=[(inputs.getD 1 zero,16,18),(inputs.getD 3 zero,128,136)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low2
  have charge : 7 + (([(inputs.getD 1 zero,16,18),(inputs.getD 3 zero,128,136)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 9 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice6 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨6,by decide⟩).1 (cutPair ⟨6,by decide⟩).2 :=
  slice_correct (ms:=fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift6
theorem lift7 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xffeeff00ffeeff00,0xffeeffeeffeeffee,0xeeee0000eeee0000,0xffffffffffffffff,0xffeeff00ffeeff00,0xffeeffeeffeeffee,0xeeee0000eeee0000])) : Sig) 8 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xffeeff00ffeeff00,0xffeeffeeffeeffee,0xeeee0000eeee0000,0xffffffffffffffff,0xffeeff00ffeeff00,0xffeeffeeffeeffee,0xeeee0000eeee0000])) : Sig)) (base:=roots g1Atlas) (G:=target g1Atlas) (ms:=fixRows 2 0) (xs:=[(inputs.getD 1 zero,16,18)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low1
  have charge : 7 + (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 8 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice7 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨7,by decide⟩).1 (cutPair ⟨7,by decide⟩).2 :=
  slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift7
theorem lift8 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xfffffffffefef0f0,0xfffffffffefef0f0,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfffffffffefef0f0,0xfffffffffefef0f0,0xfefefafaeeee0000,0xfefefafaeeee0000])) : Sig) 8 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xfffffffffefef0f0,0xfffffffffefef0f0,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfffffffffefef0f0,0xfffffffffefef0f0,0xfefefafaeeee0000,0xfefefafaeeee0000])) : Sig)) (base:=roots g2Atlas) (G:=target g2Atlas) (ms:=fixRows 2 0) (xs:=[(inputs.getD 1 zero,16,18)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low2
  have charge : 7 + (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 8 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice8 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨8,by decide⟩).1 (cutPair ⟨8,by decide⟩).2 :=
  slice_correct (ms:=fixRows 72 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift8
theorem slice9 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨9,by decide⟩).1 (cutPair ⟨9,by decide⟩).2 :=
  slice_correct (ms:=fixRows 12 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) low3
theorem lift10 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfefef0f0fefef0f0,0xeeeeeeeeeeeeeeee,0xeeee0000eeee0000,0xffffffffffffffff,0xfefef0f0fefef0f0,0xeeeeeeeeeeeeeeee,0xeeee0000eeee0000])) : Sig) 6 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfefef0f0fefef0f0,0xeeeeeeeeeeeeeeee,0xeeee0000eeee0000,0xffffffffffffffff,0xfefef0f0fefef0f0,0xeeeeeeeeeeeeeeee,0xeeee0000eeee0000])) : Sig)) (base:=roots g4Atlas) (G:=target g4Atlas) (ms:=fixRows 18 0) (xs:=[(inputs.getD 1 zero,16,18),(inputs.getD 4 zero,1,17)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low4
  have charge : 4 + (([(inputs.getD 1 zero,16,18),(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 6 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice10 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨10,by decide⟩).1 (cutPair ⟨10,by decide⟩).2 :=
  slice_correct (ms:=fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift10
theorem slice11 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨11,by decide⟩).1 (cutPair ⟨11,by decide⟩).2 :=
  slice_correct (ms:=fixRows 68 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) low5
theorem lift12 : Lower true [inputs.getD 0 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xfffffffffff0fff0,0xfffffffffff0fff0,0xfafafafa00000000,0xfafafafa00000000,0xfffffffffff0fff0,0xfffffffffff0fff0,0xfafafafa00000000,0xfafafafa00000000])) : Sig) 6 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xfffffffffff0fff0,0xfffffffffff0fff0,0xfafafafa00000000,0xfafafafa00000000,0xfffffffffff0fff0,0xfffffffffff0fff0,0xfafafafa00000000,0xfafafafa00000000])) : Sig)) (base:=roots g6Atlas) (G:=target g6Atlas) (ms:=fixRows 9 0) (xs:=[(inputs.getD 0 zero,32,33),(inputs.getD 3 zero,128,136)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low6
  have charge : 4 + (([(inputs.getD 0 zero,32,33),(inputs.getD 3 zero,128,136)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 6 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice12 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨12,by decide⟩).1 (cutPair ⟨12,by decide⟩).2 :=
  slice_correct (ms:=fixRows 82 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift12
theorem lift13 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero] ((OfNat.ofNat (certificateWord [0xfffefffeffeeffee,0xfefefafaeeee0000,0xfffefffeffeeffee,0xfefefafaeeee0000,0xfffefffeffeeffee,0xfefefafaeeee0000,0xfffefffeffeeffee,0xfefefafaeeee0000])) : Sig) 8 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero]) (T:=((OfNat.ofNat (certificateWord [0xfffefffeffeeffee,0xfefefafaeeee0000,0xfffefffeffeeffee,0xfefefafaeeee0000,0xfffefffeffeeffee,0xfefefafaeeee0000,0xfffefffeffeeffee,0xfefefafaeeee0000])) : Sig)) (base:=roots g7Atlas) (G:=target g7Atlas) (ms:=fixRows 4 0) (xs:=[(inputs.getD 2 zero,32,36)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low7
  have charge : 7 + (([(inputs.getD 2 zero,32,36)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 8 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice13 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨13,by decide⟩).1 (cutPair ⟨13,by decide⟩).2 :=
  slice_correct (ms:=fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift13
theorem slice14 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨14,by decide⟩).1 (cutPair ⟨14,by decide⟩).2 :=
  slice_correct (ms:=fixRows 132 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) low7
theorem lift15 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 6 zero] ((OfNat.ofNat (certificateWord [0xffeeffeeffeeffee,0xeeee0000eeee0000,0xffeeffeeffeeffee,0xeeee0000eeee0000,0xffeeffeeffeeffee,0xeeee0000eeee0000,0xffeeffeeffeeffee,0xeeee0000eeee0000])) : Sig) 5 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 6 zero]) (T:=((OfNat.ofNat (certificateWord [0xffeeffeeffeeffee,0xeeee0000eeee0000,0xffeeffeeffeeffee,0xeeee0000eeee0000,0xffeeffeeffeeffee,0xeeee0000eeee0000,0xffeeffeeffeeffee,0xeeee0000eeee0000])) : Sig)) (base:=roots g8Atlas) (G:=target g8Atlas) (ms:=fixRows 2 0) (xs:=[(inputs.getD 1 zero,16,18)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low8
  have charge : 4 + (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 5 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice15 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨15,by decide⟩).1 (cutPair ⟨15,by decide⟩).2 :=
  slice_correct (ms:=fixRows 164 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift15
theorem lift16 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero] ((OfNat.ofNat (certificateWord [0xfefefefeeeeeeeee,0xfefefafaeeee0000,0xfefefefeeeeeeeee,0xfefefafaeeee0000,0xfefefefeeeeeeeee,0xfefefafaeeee0000,0xfefefefeeeeeeeee,0xfefefafaeeee0000])) : Sig) 6 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero]) (T:=((OfNat.ofNat (certificateWord [0xfefefefeeeeeeeee,0xfefefafaeeee0000,0xfefefefeeeeeeeee,0xfefefafaeeee0000,0xfefefefeeeeeeeee,0xfefefafaeeee0000,0xfefefefeeeeeeeee,0xfefefafaeeee0000])) : Sig)) (base:=roots g9Atlas) (G:=target g9Atlas) (ms:=fixRows 68 0) (xs:=[(inputs.getD 2 zero,32,36),(inputs.getD 6 zero,1,65)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low9
  have charge : 4 + (([(inputs.getD 2 zero,32,36),(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 6 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice16 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨16,by decide⟩).1 (cutPair ⟨16,by decide⟩).2 :=
  slice_correct (ms:=fixRows 136 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift16
theorem lift17 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 5 zero] ((OfNat.ofNat (certificateWord [0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000])) : Sig) 5 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 5 zero]) (T:=((OfNat.ofNat (certificateWord [0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000])) : Sig)) (base:=roots g9Atlas) (G:=target g9Atlas) (ms:=fixRows 4 0) (xs:=[(inputs.getD 2 zero,32,36)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low9
  have charge : 4 + (([(inputs.getD 2 zero,32,36)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 5 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice17 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨17,by decide⟩).1 (cutPair ⟨17,by decide⟩).2 :=
  slice_correct (ms:=fixRows 200 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift17
theorem lift18 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero] ((OfNat.ofNat (certificateWord [0xeeeeeeeeeeeeeeee,0xeeeeaaaaeeee0000,0xeeeeeeeeeeeeeeee,0xeeeeaaaaeeee0000,0xeeeeeeeeeeeeeeee,0xeeeeaaaaeeee0000,0xeeeeeeeeeeeeeeee,0xeeeeaaaaeeee0000])) : Sig) 5 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero]) (T:=((OfNat.ofNat (certificateWord [0xeeeeeeeeeeeeeeee,0xeeeeaaaaeeee0000,0xeeeeeeeeeeeeeeee,0xeeeeaaaaeeee0000,0xeeeeeeeeeeeeeeee,0xeeeeaaaaeeee0000,0xeeeeeeeeeeeeeeee,0xeeeeaaaaeeee0000])) : Sig)) (base:=roots g9Atlas) (G:=target g9Atlas) (ms:=fixRows 64 0) (xs:=[(inputs.getD 6 zero,1,65)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low9
  have charge : 4 + (([(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 5 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice18 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨18,by decide⟩).1 (cutPair ⟨18,by decide⟩).2 :=
  slice_correct (ms:=fixRows 140 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift18
theorem lift19 : Lower true [inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffcfcf0f0,0xfcfcfcfccccccccc,0xfcfcf0f0cccc0000,0xffffffffffffffff,0xfffffffffcfcf0f0,0xfcfcfcfccccccccc,0xfcfcf0f0cccc0000])) : Sig) 8 := by
  have lifted := lift_ok (raw:=[inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffcfcf0f0,0xfcfcfcfccccccccc,0xfcfcf0f0cccc0000,0xffffffffffffffff,0xfffffffffcfcf0f0,0xfcfcfcfccccccccc,0xfcfcf0f0cccc0000])) : Sig)) (base:=roots g10Atlas) (G:=target g10Atlas) (ms:=fixRows 16 0) (xs:=[(inputs.getD 4 zero,2,18)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low10
  have charge : 7 + (([(inputs.getD 4 zero,2,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 8 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice19 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨19,by decide⟩).1 (cutPair ⟨19,by decide⟩).2 :=
  slice_correct (ms:=fixRows 9 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift19
theorem lift20 : Lower true [inputs.getD 0 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffafaf0f0,0xfafafafaaaaaaaaa,0xfafafafaaaaa0000,0xffffffffffffffff,0xfffffffffafaf0f0,0xfafafafaaaaaaaaa,0xfafafafaaaaa0000])) : Sig) 8 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffafaf0f0,0xfafafafaaaaaaaaa,0xfafafafaaaaa0000,0xffffffffffffffff,0xfffffffffafaf0f0,0xfafafafaaaaaaaaa,0xfafafafaaaaa0000])) : Sig)) (base:=roots g2Atlas) (G:=target g2Atlas) (ms:=fixRows 64 0) (xs:=[(inputs.getD 6 zero,1,65)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low2
  have charge : 7 + (([(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 8 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice20 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨20,by decide⟩).1 (cutPair ⟨20,by decide⟩).2 :=
  slice_correct (ms:=fixRows 10 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift20
theorem lift21 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffff0f0f0f0,0xfefefefeeeeeeeee,0xfafafafa00000000,0xffffffffffffffff,0xfffffffff0f0f0f0,0xfefefefeeeeeeeee,0xfafafafa00000000])) : Sig) 8 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffff0f0f0f0,0xfefefefeeeeeeeee,0xfafafafa00000000,0xffffffffffffffff,0xfffffffff0f0f0f0,0xfefefefeeeeeeeee,0xfafafafa00000000])) : Sig)) (base:=roots g10Atlas) (G:=target g10Atlas) (ms:=fixRows 1 0) (xs:=[(inputs.getD 0 zero,32,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low10
  have charge : 7 + (([(inputs.getD 0 zero,32,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 8 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice21 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨21,by decide⟩).1 (cutPair ⟨21,by decide⟩).2 :=
  slice_correct (ms:=fixRows 24 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift21
theorem lift22 : Lower true [inputs.getD 1 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xffffffffffccff00,0xffccffccffccffcc,0xcccc0000cccc0000,0xffffffffffffffff,0xffffffffffccff00,0xffccffccffccffcc,0xcccc0000cccc0000])) : Sig) 8 := by
  have lifted := lift_ok (raw:=[inputs.getD 1 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xffffffffffccff00,0xffccffccffccffcc,0xcccc0000cccc0000,0xffffffffffffffff,0xffffffffffccff00,0xffccffccffccffcc,0xcccc0000cccc0000])) : Sig)) (base:=roots g11Atlas) (G:=target g11Atlas) (ms:=fixRows 32 0) (xs:=[(inputs.getD 5 zero,128,160)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low11
  have charge : 7 + (([(inputs.getD 5 zero,128,160)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 8 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice22 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨22,by decide⟩).1 (cutPair ⟨22,by decide⟩).2 :=
  slice_correct (ms:=fixRows 5 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift22
theorem lift23 : Lower true [inputs.getD 0 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xffffffffffaaff00,0xffaaffaaffaaffaa,0xaaaaaaaaaaaa0000,0xffffffffffffffff,0xffffffffffaaff00,0xffaaffaaffaaffaa,0xaaaaaaaaaaaa0000])) : Sig) 8 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xffffffffffaaff00,0xffaaffaaffaaffaa,0xaaaaaaaaaaaa0000,0xffffffffffffffff,0xffffffffffaaff00,0xffaaffaaffaaffaa,0xaaaaaaaaaaaa0000])) : Sig)) (base:=roots g1Atlas) (G:=target g1Atlas) (ms:=fixRows 32 0) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low1
  have charge : 7 + (([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 8 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice23 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨23,by decide⟩).1 (cutPair ⟨23,by decide⟩).2 :=
  slice_correct (ms:=fixRows 6 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift23
theorem slice24 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨24,by decide⟩).1 (cutPair ⟨24,by decide⟩).2 :=
  slice_correct (ms:=fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) low12
theorem lift25 : Lower true [inputs.getD 0 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xfffffffffff0fff0,0xfffffffffff0fff0,0xfafafafa00000000,0xfafafafa00000000,0xfffffffffff0fff0,0xfffffffffff0fff0,0xfafafafa00000000,0xfafafafa00000000])) : Sig) 6 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xfffffffffff0fff0,0xfffffffffff0fff0,0xfafafafa00000000,0xfafafafa00000000,0xfffffffffff0fff0,0xfffffffffff0fff0,0xfafafafa00000000,0xfafafafa00000000])) : Sig)) (base:=roots g6Atlas) (G:=target g6Atlas) (ms:=fixRows 9 0) (xs:=[(inputs.getD 0 zero,32,33),(inputs.getD 3 zero,128,136)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low6
  have charge : 4 + (([(inputs.getD 0 zero,32,33),(inputs.getD 3 zero,128,136)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 6 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice25 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨25,by decide⟩).1 (cutPair ⟨25,by decide⟩).2 :=
  slice_correct (ms:=fixRows 82 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift25
theorem lift26 : Lower true [inputs.getD 0 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffafff0fffafff0,0xffaaffaaffaaffaa,0xaaaa0000aaaa0000,0xffffffffffffffff,0xfffafff0fffafff0,0xffaaffaaffaaffaa,0xaaaa0000aaaa0000])) : Sig) 8 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffafff0fffafff0,0xffaaffaaffaaffaa,0xaaaa0000aaaa0000,0xffffffffffffffff,0xfffafff0fffafff0,0xffaaffaaffaaffaa,0xaaaa0000aaaa0000])) : Sig)) (base:=roots g1Atlas) (G:=target g1Atlas) (ms:=fixRows 4 0) (xs:=[(inputs.getD 2 zero,128,132)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low1
  have charge : 7 + (([(inputs.getD 2 zero,128,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 8 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice26 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨26,by decide⟩).1 (cutPair ⟨26,by decide⟩).2 :=
  slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift26
theorem lift27 : Lower true [inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffcfff0fffcfff0,0xffccffccffccffcc,0xcccc0000cccc0000,0xffffffffffffffff,0xfffcfff0fffcfff0,0xffccffccffccffcc,0xcccc0000cccc0000])) : Sig) 8 := by
  have lifted := lift_ok (raw:=[inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffcfff0fffcfff0,0xffccffccffccffcc,0xcccc0000cccc0000,0xffffffffffffffff,0xfffcfff0fffcfff0,0xffccffccffccffcc,0xcccc0000cccc0000])) : Sig)) (base:=roots g11Atlas) (G:=target g11Atlas) (ms:=fixRows 4 0) (xs:=[(inputs.getD 2 zero,128,132)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low11
  have charge : 7 + (([(inputs.getD 2 zero,128,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 8 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice27 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨27,by decide⟩).1 (cutPair ⟨27,by decide⟩).2 :=
  slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift27
theorem lift28 : Lower true [inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffff0fff0,0xfffcfffcffccffcc,0xf0f0f0f000000000,0xffffffffffffffff,0xfffffffffff0fff0,0xfffcfffcffccffcc,0xf0f0f0f000000000])) : Sig) 9 := by
  have lifted := lift_ok (raw:=[inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffff0fff0,0xfffcfffcffccffcc,0xf0f0f0f000000000,0xffffffffffffffff,0xfffffffffff0fff0,0xfffcfffcffccffcc,0xf0f0f0f000000000])) : Sig)) (base:=roots g0Atlas) (G:=target g0Atlas) (ms:=fixRows 2 0) (xs:=[(inputs.getD 1 zero,64,66)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low0
  have charge : 8 + (([(inputs.getD 1 zero,64,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 9 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice28 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨28,by decide⟩).1 (cutPair ⟨28,by decide⟩).2 :=
  slice_correct (ms:=fixRows 17 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift28
theorem lift29 : Lower true [inputs.getD 0 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffff0fff0,0xfffafffaffaaffaa,0xfafafafa00000000,0xffffffffffffffff,0xfffffffffff0fff0,0xfffafffaffaaffaa,0xfafafafa00000000])) : Sig) 9 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfffffffffff0fff0,0xfffafffaffaaffaa,0xfafafafa00000000,0xffffffffffffffff,0xfffffffffff0fff0,0xfffafffaffaaffaa,0xfafafafa00000000])) : Sig)) (base:=roots g0Atlas) (G:=target g0Atlas) (ms:=fixRows 1 0) (xs:=[(inputs.getD 0 zero,32,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low0
  have charge : 8 + (([(inputs.getD 0 zero,32,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 9 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice29 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨29,by decide⟩).1 (cutPair ⟨29,by decide⟩).2 :=
  slice_correct (ms:=fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift29
theorem lift30 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 6 zero] ((OfNat.ofNat (certificateWord [0xffeeffeeffeeffee,0xeeee0000eeee0000,0xffeeffeeffeeffee,0xeeee0000eeee0000,0xffeeffeeffeeffee,0xeeee0000eeee0000,0xffeeffeeffeeffee,0xeeee0000eeee0000])) : Sig) 5 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 6 zero]) (T:=((OfNat.ofNat (certificateWord [0xffeeffeeffeeffee,0xeeee0000eeee0000,0xffeeffeeffeeffee,0xeeee0000eeee0000,0xffeeffeeffeeffee,0xeeee0000eeee0000,0xffeeffeeffeeffee,0xeeee0000eeee0000])) : Sig)) (base:=roots g8Atlas) (G:=target g8Atlas) (ms:=fixRows 2 0) (xs:=[(inputs.getD 1 zero,16,18)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low8
  have charge : 4 + (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 5 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice30 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨30,by decide⟩).1 (cutPair ⟨30,by decide⟩).2 :=
  slice_correct (ms:=fixRows 164 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift30
theorem lift31 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfff0fff0fff0fff0,0xffeeffeeffeeffee,0x0000000000000000,0xffffffffffffffff,0xfff0fff0fff0fff0,0xffeeffeeffeeffee,0x0000000000000000])) : Sig) 7 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfff0fff0fff0fff0,0xffeeffeeffeeffee,0x0000000000000000,0xffffffffffffffff,0xfff0fff0fff0fff0,0xffeeffeeffeeffee,0x0000000000000000])) : Sig)) (base:=roots g13Atlas) (G:=target g13Atlas) (ms:=fixRows 7 0) (xs:=[(inputs.getD 0 zero,64,65),(inputs.getD 1 zero,64,66),(inputs.getD 2 zero,128,132)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low13
  have charge : 4 + (([(inputs.getD 0 zero,64,65),(inputs.getD 1 zero,64,66),(inputs.getD 2 zero,128,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 7 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice31 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨31,by decide⟩).1 (cutPair ⟨31,by decide⟩).2 :=
  slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift31
theorem lift32 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 5 zero] ((OfNat.ofNat (certificateWord [0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000])) : Sig) 5 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 5 zero]) (T:=((OfNat.ofNat (certificateWord [0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000,0xfefefafaeeee0000])) : Sig)) (base:=roots g9Atlas) (G:=target g9Atlas) (ms:=fixRows 4 0) (xs:=[(inputs.getD 2 zero,32,36)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low9
  have charge : 4 + (([(inputs.getD 2 zero,32,36)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 5 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice32 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨32,by decide⟩).1 (cutPair ⟨32,by decide⟩).2 :=
  slice_correct (ms:=fixRows 200 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift32
theorem lift33 : Lower true [inputs.getD 0 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xfffffffffffafff0,0xfffffffffffafff0,0xfafafafaaaaa0000,0xfafafafaaaaa0000,0xfffffffffffafff0,0xfffffffffffafff0,0xfafafafaaaaa0000,0xfafafafaaaaa0000])) : Sig) 8 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xfffffffffffafff0,0xfffffffffffafff0,0xfafafafaaaaa0000,0xfafafafaaaaa0000,0xfffffffffffafff0,0xfffffffffffafff0,0xfafafafaaaaa0000,0xfafafafaaaaa0000])) : Sig)) (base:=roots g2Atlas) (G:=target g2Atlas) (ms:=fixRows 8 0) (xs:=[(inputs.getD 3 zero,128,136)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low2
  have charge : 7 + (([(inputs.getD 3 zero,128,136)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 8 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice33 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨33,by decide⟩).1 (cutPair ⟨33,by decide⟩).2 :=
  slice_correct (ms:=fixRows 66 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift33
theorem slice34 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨34,by decide⟩).1 (cutPair ⟨34,by decide⟩).2 :=
  slice_correct (ms:=fixRows 204 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) low9
theorem slice35 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨35,by decide⟩).1 (cutPair ⟨35,by decide⟩).2 :=
  slice_correct (ms:=fixRows 25 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) low10
theorem slice36 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨36,by decide⟩).1 (cutPair ⟨36,by decide⟩).2 :=
  slice_correct (ms:=fixRows 38 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) low1
theorem slice37 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨37,by decide⟩).1 (cutPair ⟨37,by decide⟩).2 :=
  slice_correct (ms:=fixRows 86 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) low14
theorem lift38 : Lower true [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 6 zero] ((OfNat.ofNat (certificateWord [0xfffefffeffeeffee,0xfafafafa00000000,0xfffefffeffeeffee,0xfafafafa00000000,0xfffefffeffeeffee,0xfafafafa00000000,0xfffefffeffeeffee,0xfafafafa00000000])) : Sig) 6 := by
  have lifted := lift_ok (raw:=[inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 6 zero]) (T:=((OfNat.ofNat (certificateWord [0xfffefffeffeeffee,0xfafafafa00000000,0xfffefffeffeeffee,0xfafafafa00000000,0xfffefffeffeeffee,0xfafafafa00000000,0xfffefffeffeeffee,0xfafafafa00000000])) : Sig)) (base:=roots g15Atlas) (G:=target g15Atlas) (ms:=fixRows 12 0) (xs:=[(inputs.getD 2 zero,32,36),(inputs.getD 3 zero,64,72)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low15
  have charge : 4 + (([(inputs.getD 2 zero,32,36),(inputs.getD 3 zero,64,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 6 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice38 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨38,by decide⟩).1 (cutPair ⟨38,by decide⟩).2 :=
  slice_correct (ms:=fixRows 144 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift38
theorem lift39 : Lower true [inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xfffffffffff0fff0,0xfffffffffff0fff0,0xf0f0f0f000000000,0xf0f0f0f000000000,0xfffffffffff0fff0,0xfffffffffff0fff0,0xf0f0f0f000000000,0xf0f0f0f000000000])) : Sig) 5 := by
  have lifted := lift_ok (raw:=[inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xfffffffffff0fff0,0xfffffffffff0fff0,0xf0f0f0f000000000,0xf0f0f0f000000000,0xfffffffffff0fff0,0xfffffffffff0fff0,0xf0f0f0f000000000,0xf0f0f0f000000000])) : Sig)) (base:=roots g6Atlas) (G:=target g6Atlas) (ms:=fixRows 8 0) (xs:=[(inputs.getD 3 zero,128,136)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low6
  have charge : 4 + (([(inputs.getD 3 zero,128,136)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 5 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice39 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨39,by decide⟩).1 (cutPair ⟨39,by decide⟩).2 :=
  slice_correct (ms:=fixRows 83 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift39
theorem slice40 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨40,by decide⟩).1 (cutPair ⟨40,by decide⟩).2 :=
  slice_correct (ms:=fixRows 130 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) low16
theorem slice41 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨41,by decide⟩).1 (cutPair ⟨41,by decide⟩).2 :=
  slice_correct (ms:=fixRows 74 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) low2
theorem slice42 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨42,by decide⟩).1 (cutPair ⟨42,by decide⟩).2 :=
  slice_correct (ms:=fixRows 37 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) low11
theorem slice43 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨43,by decide⟩).1 (cutPair ⟨43,by decide⟩).2 :=
  slice_correct (ms:=fixRows 19 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) low0
theorem lift44 : Lower true [inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 6 zero,inputs.getD 7 zero] ((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfff0fff0fff0fff0,0xffccffccffccffcc,0x0000000000000000,0xffffffffffffffff,0xfff0fff0fff0fff0,0xffccffccffccffcc,0x0000000000000000])) : Sig) 6 := by
  have lifted := lift_ok (raw:=[inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 6 zero,inputs.getD 7 zero]) (T:=((OfNat.ofNat (certificateWord [0xffffffffffffffff,0xfff0fff0fff0fff0,0xffccffccffccffcc,0x0000000000000000,0xffffffffffffffff,0xfff0fff0fff0fff0,0xffccffccffccffcc,0x0000000000000000])) : Sig)) (base:=roots g13Atlas) (G:=target g13Atlas) (ms:=fixRows 6 0) (xs:=[(inputs.getD 1 zero,64,66),(inputs.getD 2 zero,128,132)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low13
  have charge : 4 + (([(inputs.getD 1 zero,64,66),(inputs.getD 2 zero,128,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 6 := by decide +kernel
  rw [charge] at lifted
  exact lifted
theorem slice44 : Slice true (roots g17Atlas) (target g17Atlas) (cutPair ⟨44,by decide⟩).1 (cutPair ⟨44,by decide⟩).2 :=
  slice_correct (ms:=fixRows 49 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lift44
theorem fullBound : Lower true (roots g17Atlas) (target g17Atlas) 12 := by
  have cuts (c : Fin 45) : Slice true (roots g17Atlas) (target g17Atlas) (cutPair c).1 (cutPair c).2 := by
    fin_cases c
    · exact slice0
    · exact slice1
    · exact slice2
    · exact slice3
    · exact slice4
    · exact slice5
    · exact slice6
    · exact slice7
    · exact slice8
    · exact slice9
    · exact slice10
    · exact slice11
    · exact slice12
    · exact slice13
    · exact slice14
    · exact slice15
    · exact slice16
    · exact slice17
    · exact slice18
    · exact slice19
    · exact slice20
    · exact slice21
    · exact slice22
    · exact slice23
    · exact slice24
    · exact slice25
    · exact slice26
    · exact slice27
    · exact slice28
    · exact slice29
    · exact slice30
    · exact slice31
    · exact slice32
    · exact slice33
    · exact slice34
    · exact slice35
    · exact slice36
    · exact slice37
    · exact slice38
    · exact slice39
    · exact slice40
    · exact slice41
    · exact slice42
    · exact slice43
    · exact slice44
  have ready : Ready g17Atlas (asRow g17Pos) (asRow g17Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact cuts _
  exact frozen ready all17 (by decide +kernel) (by decide) [(inputs.getD 0 zero,16,17),(inputs.getD 1 zero,16,18),(inputs.getD 2 zero,32,36),(inputs.getD 3 zero,64,72),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,4,132)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots := roots g17Atlas
def fullWord := target g17Atlas
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample8 (r : Row) (i : Fin 8) := bit r (fullRoots.getD i.val zero)
theorem table8 : ∀ r, posted (sample8 r) = bit r fullWord := by decide +kernel
theorem raw8 : List.ofFn (fun i : Fin 8 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval8 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample8 r) = fullRoots.map (bit r) := by rw [←raw8,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample8 r)).trans (table8 r)
theorem binaryLower (low : Lower true fullRoots fullWord 12)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 12 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval8 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_14286.Model.Repr at out
  rw [nrm_id (by decide +kernel : bit 0 fullWord=false)] at out
  obtain ⟨k,S,hk,run,sub⟩ := extractPlan gs fullRoots legal (by simp) pg (out.resolve_right (fun h => h pg))
  rw [nrm_map (by decide +kernel : fullRoots.all plainWord=true)] at sub
  have rr := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have supplied : supply true (fullRoots.map observe) (S.toList.map observe) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q,B,hr,hit,hq⟩ := contraction (observe_proper pg) rr _ Reach.start supplied
  have bound := low q B hr hit
  omega

def mono : List Gate := [⟨.or,[3,7]⟩,⟨.or,[4,6]⟩,⟨.or,[2,3]⟩,⟨.or,[0,2]⟩,⟨.or,[0,1]⟩,⟨.or,[11,7]⟩,⟨.and,[9,12]⟩,⟨.and,[13,5]⟩,⟨.and,[8,6]⟩,⟨.and,[7,10]⟩,⟨.or,[14,15]⟩,⟨.or,[16,17]⟩,⟨.or,[18,19]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ correct
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨gs,o,?_,Nat.le_refl _,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := legal g hg
    exact ⟨op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg))),len⟩
  · push Not at clean
    obtain ⟨a,ha,hop⟩ := clean
    have lo := binaryLower low gs o (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal) correct
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot,hop] at e
    exact ⟨mono,20,monoShape,by change 13 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_14286
open PEqualNP.Outside.L_meta_14286 in
theorem PEqualNP.Outside.L_meta_14286 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := solve fullBound
