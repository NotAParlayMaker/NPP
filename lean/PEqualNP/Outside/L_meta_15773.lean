import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_15773.Model
open PEqualNP.CircuitLowerBounds
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

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
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


abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
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
  let n := v.toNat % 2305843009213693951
  ((n*n % 2305843009213693951)*(n+7)+971*n) % 2305843009213693951
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
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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


end PEqualNP.Outside.L_meta_15773.Model

namespace PEqualNP.Outside.L_meta_15773
open PEqualNP.Outside.L_meta_15773.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

def SBf (j : Nat) : Nat := [8, 12, 4, 4, 4, 4].getD j 0

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d (SBf j) k cs.length pool ws)

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

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
    ∀ k i, i < count g k → tip g k i ≠ 0 →
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) (SBf (min ((tip g k i % 8)-1) 5))

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

end PEqualNP.Outside.L_meta_15773

namespace PEqualNP.Outside.L_meta_15773
open PEqualNP.Outside.L_meta_15773.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x90a0099c247439e2a0109f56116204a4412d4ca4a171c040165e8d38b14b83001ea0d804400c00480002a106480c0600d0d000e48002ee00000030e800080ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20ee20fd20fc20ec20ff10fe10f610fd10fc10f410
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x41f8400837080107ecc020ef18041dc30083f06010760c020f790041fa20083da40107e48020f7aa041ee54083daa8107b15020f7a9841ee53083daa6107b14c20f7a1841ee43083da86107b10c20f7a8841ee51083daa2107b14420f7a0841ee41083da82107b10420f798841ee31083da62107b0c420f7280416e50083d4a0107bd0020f5a0041ee400835c80107b50020f620041ac40083d080106a10020f798041eb30083dc6010738c020f698041ec300839860107a0c020e4180417f54c42fca9886f953109f2a6217d54c437aa9884f55310be2a6217f53c42fca7887794f10af29e217d53c43baa7885754f10be29e217f52c42fca5887b94b10b7296217d52c43daa5885b54b10be29621fb40c437c81886f10310fc20621b840c43f66188778c310ee18621f830c43b061887ec8310f710621ec20c43f041887a08310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c21f741843ec83087d50610fa20c21f731843ec63087d4c610fa18c21f721843ec43087d48610fa10c217e508437c81086f10210ef18421dc30843dc41087b08210fb88421fb10843eea9087d95210faaa421f454843eea7087d94e10faa9c21f453843ee87087d90e10faa1c21f443843eea5087d94a10faa9421f452843ee85087d90a10faa1421f442843ee65087d8ca10fa99421f432842eca1087dd0210fb20421b640843ea81087d10210da20421f730843ec6108758c210fa98421f430843a861087dc8210fb10421e620843ea41087d08210f2104217f544437ea8884fd5110bf2a2217d54442f8a8886f151109e2a2217f53443bea68857d4d10bf29a217d53442f8a6887714d10ae29a217f52443dea4885bd4910bf292217d52442f8a4887b14910b629221be40443788088778c110ee18221ee20443d840887ec4110fb082217f54042fca8085f55010be2a0217f53042fca6085f54c10be298217f52042fca4085f54810be290217e51043ee82087d90410faa0821f441043ee62087d8c410fa98821f431043ee42087d88410fa90821f421042fca0087ed0010df20021bc40043f080086e10010fd98021de30043b860087e0c010ec18021fb20043dc40087b08010fc10021e820043ee20087e84010fa88021f910043eea8087d95010faaa021f454043eea6087d94c10faa9821f453043ee86087d90c10faa1821f443043eea4087d94810faa9021f452043ee84087d90810faa1021f442043ee64087d8c810fa99021f432043eca0085d94010f928021f740043e680087d90010db20021f540043e880086d10010f820021b040043ee60087ccc010fb18021d630043ea60087d0c010ea18021f030043a060087dc8010f990021f620043cc40087d48010fa10021e420043e040087808010
  | 1 => 0x840cc37081985fd5230bf2a4617d548c2f8a9185f54e30efa1c61de438c3ba87187710e30bf294617d528c3be6518778ca30ee99461dc328c2fca3185f54630ef98c61de318c3ba6318770c630bf28461be408c378811877cc230fd98461df548c3bca9187755230ee2a461df528c3bca5187754a30ee29461df428c3bc85187750a30ee21461df518c3bca3187754630ee28c61df418c3bc83187750630ee20c61df218c3bc43187748630ee10c615e508c3be81187790230cf20461dd408c3b881186710230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa9261ef524c2dea4985f14930f6292616c524c2fea2987dd4530bba8a617c514c3e8a2985d14530df20261bc404c3f66098778c130bfaa0617e540c2faa8185f15030bf29861df430c3bc86187750c30ee218617e520c2faa41877cc830ef19061dd320c3b864185f94430bea8861df310c3bc6218774c430ee188617e500c3f680186f90030de20061f8400c370801877cc030fd18061dd300c3f2601877d5030ef2a061dd540c3b8a81877d4830ef29061dd520c3b8a41877d0830ef21061dd420c3b8841877d4430ef28861dd510c3b8a21877d0430ef20861dd410c3b8821877c8430ef10861dd210c3b842187794030af28061da500c3be801876d0030ef200619e400c3ba80187710030ce20061d8400c33080185fd5320bf2a641be54c827ca9905f55320deaa6413d54c82f8a9905fd4f20bf29e41de53c82bca7905f54f20eea9e415d53c82f8a7905f94720fb28e417651c82faa3907d54720baa8e41fb40c837c81906f10320fc20641b840c83f66190778c320ee18641f830c83b061905fd5220bf2a4417d54882f8a9105fd4e20bf29c417d53882f8a7105f54a20f7a1441ee42883da85107b10a20f799441ee32883da65107b0ca20bf28c417d51883de43107b88620f690c41ec21882fca1106f90220de20441de30883b861107bc8220fd90441ef54883dca9107b55220f62a441ef53883dca7107b54e20f629c41ef43883dc87107b50e20f621c41ef51883dca3107b54620f628c41ef41883dc83107b50620f620c41ef31883dc63107b4c620f618c416e50883de81107b90220d720441ed40883d881106b10220f798441ee308839c61107b4c220f618441cc30882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53482fea2907dd4520bba8a417c51483e8a2905d14520df20241bc40483bc6090770c120fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4107bd0820f721041ed42083d884107bcc820f719041ed32083d864105f94420bea8841ef21083dc42107b48420f6108417e50083f680106f90020de20
  | 2 => 0xc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498fbd4931b7a92637c524c7d8a498db14931fb98a63de314c6fea098fed4131bda82637c504c7f0a098de14131bfaa0637e540c6faa818df15031bf29863df430c7b88618df94831bea9063de320c7b86418df94431fba0863f4410c7be6218fd8c431ee98863f5310c7aa6218df94031bea80637f54c86fca990df55321be2a6437f53c86fca790df54f21be29e43f741c87e88390fdcc721fa18e437e50c86faa190dfd5221bf2a4437d54886f8a910dfd4e21bf29c437d53886f8a710df54a21f7a1443ec42887de6510fb0ca21bf28c43ef21887ee4310df94221bea84437f544877ea890cfd5121bf2a2437d54486f8a890ef151219e2a2437f53487bea690d7d4d21bf29a437d53486f8a690f714d21ae29a43f721487dc4290dfd4121fda82437b50486f8a090fe14121bc282437f54086fca810df55021be2a0437f53086fca610df54c21be298437e52087de8410fb10821f799043ec32086fca210fdd0421fa20843f731087e86210fbc8421fb10843ed21087ea4210f948421bf280437d50086fca7a07794f40af29e817d53d03baa7a05754f40bf29681ee52d02dca5a05f54b40f6a96816d52d02fca3a07d94740bb28e817d51d03eaa3a05d54740beaa4817e53902faa7206fd0e40df21c81bd439037887205f94a40bea9481bf429037c85206f50a40de214817e51902faa3206fd0640df20c81bd419037883205f94240dfa0481fb409037ea7206f94e40dea9c81bc539037ea5206f94a40dea9481bc529037e65206f8ca40de99481bc329037ea3206f94640dea8c81bc519037e63206f8c640de98c81bc319037e43206f88640de90c81bc219027ca1205fd4d40efa9a815f53502f8a6a07714d40ae29a817f52503dea4a05bd4940be29281ec52502d8a4a05fd4540fba8a817751502f8a2a07d14540ba28a81fb405037c80a05f95040bf298817d531037e86206f90c40dea1881bc43102fca4205f54840dfa1081be421037a84206f10840bf288817d511037e82206f90440dea0881bc41102fca0206fd0040fd20081bd40103f280206fd4c40df29881bd5310378a6206fd4840df29081bd5210378a4206fcc840df19081bd321037864206fd4440df28881bd5110378a2206fcc440df18881bd311037862206fc8440df10881bd211037842206f940409f28081ba50102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc2fca5987b94b30b7296617d52cc3daa5985b54b30bf28e61f651cc2eca3985f54730faa8e617551cc3f681986f90330de20661f
  | 3 => 0x2e0880000000c03400008004008000030000040000100000400002000018010030040040101e00000c0000600e0000000c01a008000010040080180400e03c000030060000380000003c0300400000000000028010000000020000000d0000080c00c00603403000000000000010020080280201606000004000000048000180000281d0000080080000c01802807012004000010080000380000000801002000010038040000180080300e00000801004028020000280200400000e00000000004008000000060001d0000060000c80c02401804004004004000020000000000400403c00000000020030050120040100000000001801bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a87f75150eeea2a1df14543fa28a87745150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310f3a8621df94843bea90877e5110efaa221df94043bea80877e53d0afaa7a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855f5350af8a6a17714d42ae29a85ef4250b7c84a15fd4542fba8a85775150af8a2a17d14542ba28a857f5050bf6a0a15ed4142be28285f85050af0a0a15f95042bf298857d5310b7c86216f10c42bf29085bf4210bdc84216f50842f6a1085ad4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccbde85997b10b32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65df438cbb887195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbde6499778c932bfa8a65f7514caeea2995f14532fa28a6574514cafea0997ed4132bda82657c504cbf0a0995e14132bfaa0657e540cafaa8195f15032bf29865df430cbb886195f94832f7a1065ec420cbbe64197b8c832ee99065ed320cb9a64195f94432bea88657e500cafaa0195f94f41bea9e837e52d06faa5a0df94341bea86837d54906fca720df54e41df21c83bc43906fca520df54a41df21483bc42906fca320efd0641fba0c837e50906faa120dfd4d41efa9a835f53506f8a6a0f714d41ae29a837f52507dea4a0dbd4941be29283ec52506d8a4a0fdd0541df20a837f50507f6a0a0ded4141be28283f850506f0a0a0df95041bf298837d531077c8620ef10c41bf290837d521077c8420ef10841bf28883bf41107ec8220ef50441faa0883b541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52c
  | 4 => 0x75a86e10a00062e0008d62b21ee04854847800038234e7b800011025074827e82200001e54000075e70e1dc1e600062a00052a5160580000000008261be2b40c428c7964400fc6b223400032c30e6200000006d084c0000000000000000000000000000000002ec0000000004040008b28300003e86e00008a608052c00000077e0003160006707ba68c0001aa2d83c83ae0a46c63cc80e0000000240005ca00000000084e0382000006fa8687860e01540000007ec2203ea0004ca31e34000a0ee4b21d200013e5f20003fa25a0000e44de41a00000024228249669832e63c8c400c3327220003ee72e6488841362160000000000000c60027fc3880000000e20000001e00000004480007b24860000008080000007ce0005761b40001200000006ba53e00000000000014a75460e4f601c0000000002fc0000000000000621f885a00000000000043a00000004a62811c1a649e0980008180001a000026a2802f64cc36a2564205f41980f487428a5a200050a6b62920004fa65e39c18a4983366c25da3d25045586081a20000004e000007e0004327a40004b603c00000000087800000009c67e0000002726a44061862b03468721b014c2900b021851e3a079a6f200000088c81e0008b41820000008a80000007d443600022e00070458a89e8500d67f00000006065b06240003548067a01460000004a20da81244266a8b670200000000079c00000040e00000000082a0002dc3e60007c600073a5060680000002ae00009271e0000000880005780000008560d88a06ce00048460a01800000002e89a00020a0007425441f433407a0004ce00051a0002e82603ca6de0746aa8e26f45960003bc72a0001006821900f00545c800026e2e20006ae7006e203268023017473644c0761584e45f074e46c5a60002f020e0007a21d40006d40000008580000000006cc0000000000000001162626a20008da42c4a00b217a0f20840002ac1021ba8407a64920000000007c286c13800059a00032434400043056a2a25647842ca31245211a660004028008000060080000502a028008100020180480600000c0980600001401000000024018020020a4048080000100000f0060100101206600801801008000060180000140280200000003000002004000000040240100001000c0100100205c0b80100a01000006012048000010060040080300a00c0001600a000000060020100080500001800000004000030030020240200100002c0100400e000000060000040000402800806002004008000090060000000000800811002006008078000100000000200000c0180200a000008010000040480b000004000070040280080000e000000010000040400200a0400100000802c0180000002002806000000008000100040000000000404000000000030
  | 5 => 0x366a839e00052e21a48e7523080000001500004ee3a478e0008660000348864d20000007de0a68288e44628c221005e3060003ce59c8025f80008d83864aa0002223ac7e40000000000000000000001924104f20007d00000000000000001126968445380d45c00000006ea00000031006c32a8c82987925220000941cc37e4467c000051483a0002660447f41d80000000003565d053251200027a4f02d00000000000003f67560002ea6ac72c8cc08a0003844c00aa8de00006a0002d44a433c6d870c2aa03029c73e5fa17c19422624008642672820c78a66483c4f44543028d045c4e86dc5ec16a1c629628456e1c007061611e4181045200967b40ea77c37c1c47583508ae6c04c255c7826bc88e30c1ca7947d62680004947d80005b68b000000000036e5a036086a00081067447277810600024a0000081e839000000000000000012e6102ba1085de0000000000000102ee0004ac0000000003c400000000000000024e6388e60000ce5cc47c34a8c00000006006ca0008006a00000000000000006be0000005266ee00081c00037a0005fc00074c7606028e014240c3987200007ea2b800036c21200000057a15e0000000000000005087f600076400000000045e0000003e00002c400024c0007e268828600000069479086012a0001ce2d213200075080a0000000ae2e41640000005820007fe5f600031c23e54c5e66f81de53a0d232833e3228dc15a2c80006f61e20e62c035e2460000008ce65a41e00058e00054a0000005883c006e04683200004e7305d261e27c3b635a0ca0c05c20000000004d600000076833024475c2b600048c02a18e38e2e642a0ba7bc05a0e867a4be4664da5ce43e1da0ac3f823620640812247416800045a0b466e0000001527ee6180000000000000226fe00000000079e5601fe0007380000006467b66505ea0000000005a48942c613049003a7180001607c81783d049c7ae00000066800019e1407343e25ee8040000005b200000000000000000053000012800000076a4ea85c5e24280141803d62ce0007882de6784d86583b04b80000000000a822a1f060400059069e0005c65460000003202241568140000000002fe0004380006902520003dc0005d60003f200019627000005005688285e37063000000016e82c0000002323c674a00046a0004bc13436800016c68469c68e6e86c83a87b044e0f60de8807060b650240a70a00000000064e0000001841261ac1d68ca4fe18c2c27dc0005c45800003d48340000000004a84f80000003d80005500648980000000005d40b80000008524a600078c00000000000000000041c0f809a0007e883e17080c7c436600059426c5e419a0000000003927767463b21fa31464c58453c8d200000023c00001a76601221c5e80a066648a64a31a2cc1f64b4
  | 6 => 0x3382be3f43723526424246e634247a0001486363e40004ec4607a80000000000000000000001bc0000004b08426c47728963962f40be7e676e2382e06407266ec59287a71665c00000000000041461c34c4e646e5d800057487601619c67638c2f84560001f261a4c462248063266c81a5aa0008900000005ba17e3267f23fc7aa00000043c59e0008a26b042251825428800050071010c0ec62c71282e61471400045071c4640a235c0002a05520003ec2bc2940fa6527ac00010e8aa1c88885567e01d01c23188462fa89c00e7328b80003486d643477000021e0000005861ae63424859808e45862638a3be4127985545428bc00063a0284dc6540000000008703940004c638020411841613a0005ae00050c63e51c1725a823a84840044425e82029a47e5b409065600000000000400035804c89288a77a03e00067c00000000000022800000000000027421400060c0000060000002a80000006b428e8c61a80008620006a60005bc00012c5be0000001ea0fe57c0002640000000000007446b80661767cc1b868a0005700003da00000000000000074000071a55e6da0000600cc13c78000033a0720000000005b837839a1a458c00000051000005200000030a5fe3a65dc0008640008383de47642e4ba0dc2da30487c76c7da7be0bc0424680263fe6923ba1ec6120820002782027244028542a63f06e44c80004820000005ac57e0002d60d00000206440001240004703a211425c7085681fc7fa1624e23620000360001e47f80008ba3763b40004d083629e5628d46620c856c0002586fc5344ae2a48167d214444a84a5240006724d400055a07c0000005e00000001885660004880000006f00000008ac7ca00054e1b600002c3aa14e2f200036408c00020800022c50e0000003c26864fc87e0006d273c8a40001660001b200000000000000069a00076257204005c3008be15c0c249a82452877409e3743b80782760005
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xc40043b36210010ec98840043b16210010ec18840043b35210010ec94840043b15210010ec14840043b33210010ec8c840043b13210010ec0c8400427565cc010ad99330042b564cc010b998b30042e562cc010ec90330043b040cc010bc597300437165cc010bc99330043b264cc010ac99330043b164cc010bc19330042f262cc010f898b30042e262cc010f858b30042f2608c010ec10230042d6608c010b49823004356508c010f494230043d3408c010e59023004394408c010f41023004390408c0109dd9530042b7644c010ad19130042e7624c010b918930043b0404c010ec90030043b0400c010f44c030042d6600c010f49803004356500c010f494030043d3400c010e590030043d2400c010e490030043d1400c010e510030043d0400c010e410030042f3650c010bc59430042f2640c010bc19030042f2630c010f498c30043d2530c010f454c30043d3430c010f490c30043d1430c010f410c30042f2620c010f4cc830043d2320c010f44c830043d0320c010f4d9430043d2650c010f459430043d0650c010f4d9030043d2640c010f459030043d0640c010f4d5030043d2540c010f455030043d0540c010f4d8830043d2620c010f458830043d0620c010f4d4830043d2520c010f454830043d0520c010f4d0830043d2420c010f450830043d0420c0109d59720042b664c8010ad59320042d663c8010b558f20043b240c8010ec10320043d230c8010f40c320042f165c8010dc59720042f264c8010ec99320042b264c8010ec59320042f064c8010bc98f20043d263c8010b498f20043d163c8010bc18f20042f26088010ec10220043d03088010b998220042e26088010d994220043e25088010f8d0220043a64088010e910220043e04088010e810220043e33088010f18c220043c43088010f80c220043c030880109dd9520042b76448010ad19120042d76348010b518d20043b04048010f40c120043b24008010ec10020043d23008010f40c020043e12008010b998020043e26008010d994020043e25008010f8d0020043a64008010f890020043a24008010f850020043a44008010f810020043a04008010f8cc020043c63008010f88c020043c23008010f84c020043c43008010f80c020043c03008010bcd9420042f16508010bc99020042f06408010bc98c20042f06308010bc98820043e26208010f894820043e15208010f8d0820043e24208010f850820043e04208010f8cc820043e23208010f84c820043e03208010f8d9420043e26508010f859420043e06508010f8d9020043e26408010f859020043e06408010f8d5020043e25408010f855020043e05408010f8d8c20043e26308010f858c20043e06308010f8d4c20043e25308010f854c20043e05308010f8d0c20043e24308010f850c20043e04308010
  | 1 => 0x433a5210010ce14840043b26110010ec584400433a5110010eccc440043b23110010ec4c440043b03110010ecc8440043b22110010ec48440043b02110010ae99330042ea62cc010bc58730042da608c010e6102300439a400c010e61003004279650c010f4cc430043d2310c010f44c430043d0310c010d69943004359650c010d69503004358540c010d69483004358520c010f498430043d1610c010d694430043d3410c010f490430043d1410c010f410430043d3210c010f488430043d1210c010f408430042ba64c8010b698f20042f161c8010ba98220043a84088010f20c220043aa4008010ea10020043ca3008010f20c020042796508010f8c8420043e22108010f848420043e02108010da99420043696508010da95020043685408010da94c20043685308010f898420043e16108010da94420043e34108010f890420043e14108010f810420043e33108010f88c420043e13108010f80c420042b664c4010ad59310042d663c4010b558f10042e662c4010b958b10043b040c4010f40c310043e020c40109e59610042776544010add9110042b46444010b5d8d10042d46344010b9d8910042e46244010ec10110043d03044010f8081100427b6544010ae19110042d86344010ba18910042f260d5010b5d8d54042d46355010b9d8954042e46255010cd55054042f26015010bc98353042b76454c10ad19153042e76254c10b918953043555314c10bc98053042f260d0c10bc58343042f26090c10bc58243042776550c109d19543042e76250c10b918943042f36050c10bc18143043954310c10bc98352042b76454810ad19152042d76354810b518d52043655214810bc98052042f260d0810bc58342042f26090810bc582420427765508109d19542042d76350810b518d42042f36050810bc18142043a54210810bc98332042f160cc810bc98232042f1608c8109dd953204274654c810add9132042b4644c810bcd8132042f0604c810f14c832043726094010bc59650043716594010bc99250042f26394010bc98a500427565d0010b598f40042d563d0010b998b40042e562d0010bc597400437165d0010bc98f40043d263d0010b498f40043d163d0010bc98b40043e262d0010b898b40043e162d0010bc98240042b66090010ac98240043365090010ec94240042776550010b5d8d40042d46350010b9d8940042e46250010ec50040042b66010010ec98040043365010010ec94040042f36510010bc59440042f26410010ec99040043b25410010ec55040042f26310010ecd0c40043b24310010ec50c40043b04310010bc98840043b34210010ec90840043b14210010ec10840043b36510010ec99440043b16510010ec19440043b36310010ec98c40043b16310010ec18c40043b35310010ec94c40043b15310010ec14
  | 2 => 0x604ca10f14c832842d663d0210b558f40842e662d0210b958b40842d76350210b518d40842e76250210b918940843b26010210ad99330842b564cc210b998b30842e562cc210ec1033084396408c210e510230842b7644c210ad19130842e7624c210b918930843b0400c210f498030843d3400c210e59003084394400c210f41003084390400c210ad99320842b564c8210b598f20842d563c8210ec10320843d030c8210e990220843a44088210f18c220843c43088210add9120842b46448210b5d8d20842d46348210ec10020843d03008210f898020843e34008210e990020843a44008210f810020843a04008210f8cc020843c63008210f10c020843e03008210f00c0208423e64951109798e544425d63951109b98a544426d62951109d586544425f63551109718d544426f62551109b189544427761551109ed81544423e65151108f980544423c6015110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a53442756194d108fd91534423c6454d109bd89534426c6254d109dd85534427b6054d1097994534431f5414d10c7150534425e6014d1097180534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949109d586524423f64549108f191524425f63549109718d524427761549109ed81524426e6514910cbd50524432c5414910d3d4c524434c53149109b980524426c60149108f996404431f5390110c714e404432f5290110cb14a404423e6510110c7d4c404431c5310110cbd48404432c521011097996304431f548c110c7152304434f528c110d314a304425e650c110c7d50304431c540c110d3d48304434c520c110e6100304426e6588110cbd52204432c5488110d3d4e204434c53881109b994204432f5408110cb150204434f5308110d314c20443a84008110f20c0204433854c4110d614f104436852c4110cdd5210443345484110d5d4e10443545384110d9d4a1044364528411097d8d540425c63550109bd89540426c62550108fd91530423c6454c109bd89530426c6254c108fd91520423c645481097d8d520425c63548108f992510423d64944109798e510425d63944109b98a510426d62944109d59641042f16090410cd15141042d76350410b518d41042e76250410b918941042f360504109d594410433554104109d59631042f1608c410add9131042b4644c410d514d31042e7624c410b918931042f3604c4109d5943104355530c4109d59621042f16088410add9121042b46448410b5d8d21042d46348410d914921042f360484109d59421043655208410b698f40042ea62d0010bc58740042ba60900109e59440043b34110010ec90440043b14110010ec104400433a6510010ce594400433a5310010ce14c400
  | 3 => 0x20f294430083c9510c020f214430083cb410c020f290430083c9410c020f2104300825e63d53109758f54c426e62d53109b58b54c433b60553109798c54c425d63153109b98854c426d62153108f99353c423d64d4f109b98b53c426d62d4f10c795253c431d5494f10c795153c431d5454f10d6d8153c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c425e63d4b109758f52c432e5494b10cb55252c434e5394b10d354e52c432e5454b10cb55152c434e5354b10d354d52c436b6054b108f99052c423d6414b109798c52c425d6314b10b698f40c435a53d0310ba98b40c436a52d0310c794e40c431d5390310cb94a40c432d5290310c794c40c431d5310310cb94840c432d5210310ce55040c435a5310310da94840c42b96510310ce59440c433a5310310e694c40c431a5310310e654c40c43385310310ce94840c43aa5210310ca94840c43a95210310ce14840c42ba64cc310ce95330c42ea62cc310da94b30c431e548c310c755230c434e528c310d354a30c4398408c310c795030c431d540c310d394830c434d520c310e690030c4398400c310ce95030c4359530c310da94830c42d9650c310d659430c435a540c310e695030c431a540c310e655030c4358540c310d694830c43ca520c310d294830c43c9520c310d614830c42ba64c8310ce95320c42da63c8310d694f20c432e5488310cb55220c434e5388310d354e20c43a84088310f20c220c432e5408310cb55020c434e5308310d354c20c43aa4008310ea10020c43ca3008310f20c020c433a5408310d694c20c43695208310ba59420c43696508310da95020c43aa5408310ca95020c43a95408310da15020c436a5308310f294c20c434a5308310f254c20c436853083109798f548425d63d52109b98b548426d62d52108f993538423d64d4e109b98b538426d62d4e108f993528423d64d4a109798f528425d63d4a10cd95141842d76350610b518d41842e76250610b918941843375410610add9131842b4644c610d594d31842e7624c610b91893184357530c610add9121842b46448610b5d8d21842d46348610d994921843675208610e610030843a84008210f20c020842b664c4210ad59310842d663c4210b558f10842e662c4210b958b10842d663d5210b558f54842e662d5210b958b54842f260d5210cdd5254842f26015210ad99353842b564d4e10b998b53842e562d4e10bc98353843575394e10bc98053842776550e109d19543842e76250e10b918943842f36050e10bc18143843954310e10ad99352842b564d4a10b598f52842d563d4a10bc98352843675294a10bc98052842776550a109d19542842d76350a10b518d42842f36050a10bc18142843a54210a109dd953284274654ca10add9132842b4644ca10bcd8132842f0
  | 4 => 0xed9520082b86448020b618d20082f06148020ba98354082cf6355020b318d54082e76155020b9185540832d5415020ba98054082ea60d4c20abd9153082ac6454c20b9d8553082e46154c20d354c53082ea6014c20ba98343082e960d0c20ba98243082e96090c209bd95430826c6550c20b9d8543082e46150c20bad8143082e86050c20e350c43082ea60d4420abd9151082ac6454420b3d8d51082cc6354420d954451082ea6014420ba98341082e960d0420ba98241082e960904209bd95410826c6550420b3d8d41082cc6350420bad8141082e86050420e950441082ea60cc420ba58331082ea608c420ba582310826f654c4209b19531082af644c420ab19131082eb604c420ba18131083c5310c420da98250082ea6494020ba98e50082ea61940209b59740082ce63d0020b358f40082e661d0020b958740082e965d0020da59740082ea63d0020f298f40082ca63d0020f258f40082ea61d0020f898740082e261d0020f858740082ea6090020ab98240082aa6090020cb94240083aa50900209bd9540082cf6350020b318d40082e76150020b918540083a94010020ab98040083aa6010020cb94040083aa5010020bad9440082e96510020ba99040083aa6410020ea95040083a95410020ba98c40083ab4310020ea90c40083a94310020ea10c40082ea6110020ead0440083aa4110020ea50440083a84110020ead9440083aa6510020ea59440083a86510020ead8c40083aa6310020ea58c40083a86310020ead4c40083aa5310020ea54c40083a85310020ead8440083aa6110020ea58440083a86110020ead4440083aa5110020ea54440083a85110020eacc440083aa3110020ea4c440083a831100209b59730082ae64cc020ab59330082e661cc020b958730083aa40cc020ea10330082e965cc020da59730082ea64cc020ea99330082aa64cc020ea59330082e864cc020ba98730083e261cc020b898730083e161cc020ba98230083a8408c020b398230082ca608c020d394230083ca508c020f2d02300838e408c020e310230083c8408c020e2102300826f654c020abd9130082ac644c020b9d8530082e4614c020ea10130083aa400c020ea10030083c9300c020b398030083ca600c020d394030083ca500c020f2d00300838e400c020f2900300838a400c020f2500300838c400c020f21003008388400c020bad9430082e9650c020ba99030082e8640c020ba98c30083ca630c020f294c30083c9530c020f2d0c30083ca430c020f250c30083c8430c020ba98430083cb310c020f28c430083c9310c020f20c430083cb650c020f299430083c9650c020f219430083cb640c020f299030083c9640c020f219030083cb540c020f295030083c9540c020f215030083cb610c020f298430083c9610c020f218430083cb510c
  | 5 => 0x418826f654c6209b19531882af644c620ab19131882eb604c620ba18131883c5310c620b398f40882cd63d0220b998740882e561d0220b3d8d40882cc6350220b9d8540882e46150220ea98040882ae64cc220ab59330882e661cc220b958730883a840cc220e3902308838c408c220abd9130882ac644c220b9d8530882e4614c220ea10030883ca600c220f2d00308838e400c220e310030883c8400c220e2100308823e64951209798e544825d63951209b58a544827661951209d586544825f63551209718d544826f62551209dd85544827461551209ed81544823e6515120c7d53534831c54d4d208f992534823d6494d209798e534826d6294d209d98653482756194d208fd91534823c6454d209bd8953482776154d209d185534827b6054d2097994534831f5414d20c7150534833754d4520cd153514835753d4520d514f51483375414520cd15051483575314520d514c514823e6590120c7d4e404831c5390120cdd46404833451901208f994404831f5310120c714c40483375110120cd144404825e658c120c7d52304831c548c120d5d463048354518c12097994304831f540c120c71503048357510c120d51443048398400c120ce153204835853c8120dc147204832f5488120cb152204834f5388120d314e20483675188120d9146204825f63550209718d540827761550209d185540823f6454c208f19153082776154c209d185530823e64948208f592520825e63948209758e520826d6590820ba582420832c5450820b3d8d42082cc6350820b9d8542082e46150820bad81420826d6510820cb550420826d658c820ba58232082af644c820ab191320834c534c820b9d8532082e4614c820bad81320826d650c820d354c320823f64544208f191510825f63544209718d51082e960c8420abd9121082ac6448420b3d8d21082cc6348420bad8121083655108420b698f40082e962d0020bc98740082ba60900209e59440083ab4210020ea90840083a94210020ea108400833a6510020ce594400833a5310020ce14c40083aa6210020ea588400833a5210020eacc840083aa3210020ea4c840083a83210020ce94440083ab2110020ea88440083a92110020ea08440082ba64cc020ba58b30082f261cc020b69823008398408c020e69003008398400c0209e59430083cb320c020f28c830083c9320c020f20c8300835a650c020d6594300835a540c020d615030083ca620c020f2588300835a520c020f2d0830083ca420c020f250830083c8420c020d694430083cb210c020f288430083c9210c020f208430082ae64c8020ab59320082ce63c8020b358f20082e661c8020b958720083a840c8020f20c3200826f6548020abd9120082ac6448020b3d8d20082cc6348020b9d8520082e46148020ea10120083c830480209
  | 6 => 0x2da62d0030f298b400c2ca62d0030f258b400c2da61d0030f4987400c2d261d0030f4587400c2da6090030a7982400c29a6090030c7942400c39a509003097d95400c2cf6250030b3189400c2d76150030b5185400c3994010030a7980400c39a6010030c7940400c39a5010030b6d94400c2d96510030b6990400c39a6410030e6950400c3995410030b6988400c39b4210030e6908400c3994210030e6108400c2da6110030e6d04400c39a4110030e6504400c3984110030e6d94400c39a6510030e6594400c3986510030e6d88400c39a6210030e6588400c3986210030e6d48400c39a5210030e6548400c3985210030e6d84400c39a6110030e6584400c3986110030e6d44400c39a5110030e6544400c3985110030e6c84400c39a2110030e6484400c39821100309798f54c825d63d53209d98754c827561d5320ced8154c825e63153209758c54c827661153209d58454c823e64d4f208f59353c827661d4f209d58753c831e5494f20c755253c831e5454f20c755153c835b6054f208f99053c823d6414f209d98453c82756114f20cd95251c83355494720d594e51c83555394720cd95151c83355454720d594d51c83555354720dcd8151c82da63d0320d694f40c82f261d0320dc94740c831e5390320c754e40c83365190320cd54640c831e5310320c754c40c83365110320cd54440c83395410320d694c40c83725110320ae59440c83396510320ce94c40c839a5310320c694c40c83995310320ce14c40c833a5110320ec94440c83325110320ec54440c82ba64cc320ce95330c82f261cc320dc94730c831e548c320c755230c8356518c320d554630c8398408c320c795030c831d540c320d594430c8355510c320e690030c8398400c320ce95030c8359530c320dc94430c82d9650c320d659430c835a540c320e695030c831a540c320e655030c8358540c320d694430c83d2510c320d494430c83d1510c3209798f548825d63d52209d987548827561d52208f993538823d64d4e209d987538827561d4e20cb95142882cf6350a20b318d42882e76150a20b9185428832f5410a20abd9132882ac644ca20d394d32882e7614ca20b9185328834f530ca20abd9121882ac6448620b3d8d21882cc6348620d99452188398400c220ab99320882ad64c8220b398f20882cd63c8220b998720882e561c8220b398f54882cd63d5220b998754882e561d5220ba983548832f5495220ba98054882ae64d4e20ab59353882e661d4e20b958753882ea60d4e20d3d4e53882ea6014e209bd95438826c6550e20b9d8543882e46150e20bad8143882e86050e20e350c43882ae64d4620ab59351882ce63d4620b358f51882ea60d4620d9d4651882ea60146209bd95418826c6550620b3d8d41882cc6350620bad8141882e86050620e9504
  | 7 => 0xd4630d5d46518c2da601463097d95418c25c6550630b3d89418c2cc6250630b6d81418c2d86050630e5504418c25f654863097195218c29f6448630a7191218c2db6048630b6181218c3c52108630b398b408c2cd62d0230b5987408c2d561d0230b3d89408c2cc6250230b5d85408c2d46150230e6980408c23e64951309758e544c26e62951309b58a544c27661951309d586544c25f63551309bd89544c26c62551309dd85544c27461551309ed81544c23e6515130cbd53524c32c54d4930cbd50524c32c5414930cdd53514c33454d4530d9d4b514c36452d4530cdd50514c3345414530d9d48514c36452145308f996404c32f5290130cb14a404c3375190130cd146404c23e6510130cbd48404c32c5210130cdd44404c3345110130ce153304c36852cc130dc147304c31f548c130c7152304c34f528c130d314a304c357518c130d5146304c26f62550309b189540c27761550309d185540c23e6494c308f592530c25d6590c30b6582430c31c5450c30b3d89430c2cc6250c30b5d85430c2d46150c30b6d81430c25d6510c30c7550430c23f64548308f191520c27761548309d185520c2d960cc830a7d91320c29c644c830b5d85320c2d4614c830b6d81320c34d520c8308fd91510c23c64544309bd89510c26c6254430b6583310c29f644c430a7191310c2cf624c430b3189310c2db604c430d5544310c2d963d0030ba98b400c2f261d0030ae982400c2796510030e6d0c400c39a4310030e650c400c3984310030ce994400c3396510030e698c400c3996310030ce94c400c33a5210030e6cc8400c39a3210030e64c8400c3983210030ce944400c39b3110030e68c4400c3993110030e60c4400c29e64cc030a7593300c2ce62cc030b358b300c2d661cc030b5587300c39840cc03097d95300c29f644c030a7191300c2cf624c030b3189300c2d7614c030b5185300c398404c0309ed95300c2b8644c030ba189300c2f0614c030b6983540c2cf6255030b3189540c2d76155030b5185540c31d5415030b6980540c2da60d4830a7d91520c29c6454830b5d85520c2d46154830d3548520c2da6014830b6983420c2d960d0830b6982420c2d9609083097d95420c25c6550830b5d85420c2d46150830b6d81420c2d86050830e3508420c2da60d4430a7d91510c29c6454430b3d89510c2cc6254430d5544510c2da6014430b6983410c2d960d0430b6982410c2d9609043097d95410c25c6550430b3d89410c2cc6250430b6d81410c2d86050430e5504410c2da60c8430b6583210c2da6088430b6582210c25f654843097195210c29f6448430a7191210c2db6048430b6181210c3c52108430d6982500c2da6494030b698a500c2da619403097597400c2ce62d0030b358b400c2d661d0030b5587400c2d965d0030d6597400c
  | 8 => 0x40da14b405037051d0140c7d4e405031c5390140cbd4a405032c5290140cdd46405033451901409bd89531026c6254c409dd8553102746154c40ae58343102af6250c40ab18943102b76150c40ad18543102bb6050c40c754c431025f63548409718d521027761548409d18552102b960d0840a7d8d421029c6350840add8542102b46150840aed81421032d521084097d8d511025c63544409bd89511026c6254440ae583411029f6350440a718d41102af6250440ab18941102bb6050440cd544411029e63d0040a758f40102ae62d0040ab58b40102b661d0040ad587401023f6550040a7d8d401029c6350040abd8940102ac6250040add8540102b461500409ed9540102d86350040ba18940102f06150040ae98353102af6254c40ab18953102b76154c40ad185531031d5314c40ae98053102ba60d4840a7d8d521029c6354840add8552102b46154840cb54852102ba6014840ae98332102b960cc840ae98232102b9608c8408fd95321023c654c840add8532102b4614c840aed8132102b8604c840e34c832102ba60d4440a7d8d511029c6354440abd8951102ac6254440cd54451102ba6014440ae98331102b960cc440ae98231102b9608c4408fd95311023c654c440abd8931102ac624c440aed8131102b8604c440e54c431102ba60c8440ae58321102ba6088440ae582211023f65484408f195211029f6348440a718d21102bb6048440ae18121103a52108440ce98250102ba6394040ae98a50102ba61940409b98b54cc26d62d53309d98754cc27561d5330ced8154cc26e62153309b58854cc27661153309d58454cc32e5494b30cb55252cc32e5454b30cb55152cc36b6054b30cd95251cc3355494730d994a51cc3655294730cd95151cc3355454730d994951cc3655254730dcd8151cc2ea62d0330da94b40cc2f261d0330dc94740cc32e5290330cb54a40cc3365190330cd54640cc32e5210330cb54840cc3365110330cd54440cc3395410330da94840cc3725110330ae59440cc3396510330ce94840cc3aa5210330ca94840cc3a95210330ce94440cc3b25110330cc94440cc3b151103309b98b548c26d62d52309d987548c27561d5230c7951438c2cf6250e30b3189438c2d76150e30b5185438c31f5410e30a7d91328c29c644ca30d3949328c2d7614ca30b5185328c29f644c630a7191318c2cf624c630b3189318c356514c630a7993308c29d64cc230b398b308c2cd62cc230b5987308c2d561cc230b398b548c2cd62d5230b5987548c2d561d5230b6983548c31f5495230b6980548c29e64d4a30a7593528c2d661d4a30b5587528c2da60d4a30d3d4a528c2da6014a3097d95428c25c6550a30b5d85428c2d46150a30b6d81428c2d86050a30e3508428c29e64d4630a7593518c2ce62d4630b358b518c2da6
  | 9 => 0x593538867a60d4e219e583538872f5410a21d3d4c328863f64542218f191508865f63542219718d508863e60d51218f992544865e63951219758e544867a60951219e582544865f63551219718d544866f62551219dd85544867b60551219e181544863e65151218f980544871f54d4d21c7153534865e60d4d218f992534863d6494d219798e534867a6094d219e582534863f6454d218f191534866f6254d219dd85534867b6054d219e181534865e6514d21c7d50534871c5414d2197980534873454c8521d514f214872c5488521d314e214863e64d41218f593504865e63d41219758f504873b54d4121ce153504875b53d4121d614f504873a64d4121ce593504875a63d4121d658f504873b5414121ce150504875b5314121d614c504873b6414121ce190504875b6314121d618c504876b6214121dcd8450487732114121da884504865f63550219718d540867b60550219e181540865e63150219758c540863f6454c218f191530867b6054c219e181530863e6414c218f590530866d6510821cb55042086e561108219b594320874d530c821b958432086756510421cd55041086e56210421e91084108675650c421d554c31086e5620c421f10c831086e562884219bd9521086ac6448421b318d21086e860484219dd9521086b46448421b518d21086f06048421b9d9521087676548421e9d9121086e66448421b919121087a46448421a919121087c76348421b998d21086e46348421f118d21086c46348421f8d8121086e46048421f818121086e06048421d9486500863f64540218f191500865f63540219718d500875b6054f40d394e52d034d5394b40d394d52d034d5354b40dad8152d03565394740d554e51d03665294740d954a51d03565354740d554d51d03665254740d954951d03736054740c794d43902af6250e40ab18943902b76150e40ad185439029f6350a40a718d429032e5250a40add8542902b46150a40a7d8d419029c6350640abd8941902ac6250640cd945419029e63d0240a758f40902ae62d0240ab58b40902b661d0240ad58740902ae62d4e40ab58b53902b661d4e40ad58753902ba60d4e40c7d4e53902ba6014e40a798f529029d63d4a40ad98752902b561d4a40ae983529032f5294a40ae980529023f654ca408f19532902b7614ca40ad18532902bb604ca40ae181329038d320ca40a798f519029d63d4640ab98b51902ad62d4640ae98351903375194640ae980519023f654c6408f19531902af624c640ab18931902bb604c640ae1813190395310c6408fd95219023c6548640a7d8d219029c6348640aed8121902b86048640e9484219034f53d4940d314f525034f5314940d314c525035753d4540d514f515036752d4540d914b51503575314540d514c51503675214540d9148515035853d01
  | 10 => 0xd066f62543419b18950d065f63542419718d509066f62542419b189509065e60d4d4197980535074f53d4941d314f525066e60d4941d3d4c525074c53149419b980525075453d0541d914b415071c5390541cb14a415065e63d41419758f505066e62d41419b58b505075b53d4141d614f505076b52d4141da14b505075a63d4141d658f505076a62d4141da58b505075b5314141d614c505076b5214141da148505073b6414141d6d8c50507586314141dad8850507686214141dcd8450507734114141ce904505066f6254c419b189531067b6054c419e181531071d5310c41ad584431065f63548419718d521067b60548419e181521072d5210841ad58442106b564904418fd95411069c6350441ab18941106b860504419dd9541106d46350441b918941106f06050441add9541107376550441e5d8d41106b46350441e518d41106946350441e9d8941106b46250441e918941106a46250441ecd8141106b46050441ec18141106b06050441cd506501065f63540419718d501066f62540419b189501066e62d53319b58b54cc67a60d53319e58354cc73754107318fd9150cc63c64543319bd8950cc66c62543319b98b548c66d62d52319e983548c67960d5231c7d50438c63f64542318f191508c66f62542319b189508c63e60d51318f992544c66e62951319b58a544c67a60951319e582544c65f63551319bd89544c66c62551319dd85544c67b60551319e181544c63e65151318f980544c72f54d4931cb153524c66e60d4931cbd50524c72c54149319b980524c73454cc531d914b314c71c548c531d314a314c63e64d41318f593504c66e62d41319b58b504c73b54d4131ce153504c76b52d4131da14b504c73a64d4131ce593504c76a62d4131da58b504c73b5414131ce150504c76b5214131da148504c73b6414131ce190504c75b6314131dad88504c7686214131dcd84504c7733114131d68c4504c66f62550319b189540c67b60550319e181540c66e62150319b588540c65d6510c31c7550430c6d56110c318fd91520c63c64548319ed81520c6786054831d3548320c6d5610c8319d594410c7355410431b558c410c7944310431b558e310c65f654c431a7191310c6cc624c431b6181310c677654c431ad191310c6e4624c431bc181310c6d7654c431d5d95310c797644c431b5991310c6d4644c431e5191310c694644c431f1d89310c6d4624c431f1189310c6c4624c431f4d81310c6d4604c431f4181310c6d0604c431d54c6500c63f64540318f191500c66f62540319b189500c65e63d53219758f54c867a60d53219e58354c863e64d4f218f59353c867a60d4f219e58353c87375410721d5d4c31c863f64543218f19150c865f63543219718d50c865e63d52219758f548867a60d52219e583548863e64d4e218f
  | 11 => 0x9c6150c43e51854310e946150c43e6d814310e9c6050c43e61814310e986050c439dd855210e7461548439ed815210e7860548439bd895110e6c62544439ed815110e786054443c750e5010e6f62540439b1895010e7761540439d1855010e5f63543429718d50d0a7761543429d18550d0a5f63542429718d5090a7761542429d1855090a5e60d4d42979805350b4c53d0942c714e4250b5753d4542d514f5150a7660d4542d5d4c5150b545314542d9d085150b3642145429d9805150a5e63d41429758f5050a7661d41429d5875050b5b53d4142d614f5050b7351d4142dc1475050b5a63d4142d658f5050b7261d4142dc5875050b5b5314142d614c5050b735114142dc1445050b3b6414142d6d8c5050b586314142dad885050b6b4214142ce9085050b736114142dc1845050a776154c429d1855310a7b6054c429e1815310b1d5310c42ab5884310aad64908428fd954210a9c6350842ad1854210ab860508429bd954210acc6350842b91854210ae86050842abd954210b2f6550842e3d8d4210aac6350842e318d4210a8c6350842e9d854210aac6150842e91854210aa46150842ead814210aac6050842ea1814210aa8605084297d8d5110a5c63544429ed815110a786054442cb50a5010a5f63540429718d5010a7761540429d1855010a7661d53329d58754cca7a60d53329e58354ccb2f5410b328fd9150cca3c64543329dd8550cca7461543329d987548ca7561d52329e983548ca7960d5232c7d50438ca3f64542328f191508ca7761542329d185508ca3e60d51328f992544ca7661951329d586544ca7a60951329e582544ca5f63551329bd89544ca7761551329d185544ca7b60551329e181544ca3e65151328f980544cb2c54cc932c7152324cb3754d4532cd153514ca7660d4532cdd50514cb345414532d9cc8514cb5632145329d980514ca3e64d41328f593504ca7661d41329d587504cb3b54d4132ce153504cb7351d4132dc147504cb3a64d4132ce593504cb7261d4132dc587504cb3b5414132ce150504cb735114132dc144504cb3b6414132ce190504cb5b6314132dad88504cb6b3214132d68c8504cb736114132dc184504ca7761550329d185540ca7b60550329e181540ca7661150329d584540ca5d6510c32c7550430cacd6210c329b594420cb2d5410832b358c420cb8c4310832b358e320ca5f654c832a7191320cad4614c832b6181320ca6f654c832ab191320cae4614c832ba181320cacf654c832d3d95320cb8f644c832b3991320cacc644c832e3191320ca8c644c832f1d85320cacc614c832f1185320cac4614c832f2d81320cacc604c832f2181320cac8604c8328fd91510ca3c64544329ed81510ca786054432d34ca500ca3f64540328f191500ca7761540329d185500ca5f63543419718d5
  | 12 => 0x1c01000004400800001401400005c00800000800c0280180000480640600bc00c00802800001c00801800000001003401000c00401403000005c00000002001000000000000001400c00000400c00001002800402c00800000800401c00400400801000000000000001c00000000405000c02000c01402c00000803c00407c00003801400000000400000400c00801800000402403c00000800000001400800000001800000801000002000401400000800000001801000000001400800000401802001c01400000c03400c03c00804001400007c00801000c02001c00000001c07c01000800400400000c00000400c00c00000000400000400c00000000000400800000400001000400000400000000c01c00402000802400401000800401801405400800400400c0000040000000000080500040200040040000dc00400400000401800400000000801801800801c00003003003000807400400c00402807800000000000404400000000000000400c00800001400000003c01400001c00000005800001000000000c00c00001400402401c01800402000000000c05c02000c0000080000000140000000b000c03000000400000c04000c02400402800000002c00002802c01000400001c00000004002001c02400000000c01c00001c04c00400000000400c00000400c00000400802000800400000401400400801000000400c00400401001000403402403401001800001800001404801002c00000c07001400400000c00000000400000801002807401803000401001800000400804402407401401c02400800000000800c00402402800800800000000001401800401800400401002800000c00002c03c00001800800002400001003400400002400000400001800001800400800800c0080000000a000001801401400000401400401000000c00404800000401400001400c00801c04c00001001400400800000000000400800001806c03400803000000c0040040040140000000240100040080040000626f62543439b18950d0e7761543439d18550d0e6f62542439b1895090e7761542439d1855090e6e60d4943d3d0c5250f2e43149439b9805250f6752d4543d914b5150e7660d4543d9d485150f645214543d5d0c5150f3643145439d9805150e6e62d41439b58b5050e7661d41439d5875050f6b52d4143da14b5050f7351d4143dc1475050f6a62d4143da58b5050f7261d4143dc5875050f6b5214143da1485050f735114143dc1445050f3b6414143d6d8c5050f5b4314143ce90c5050f6b6214143da1885050f736114143dc1845050e9d6490c438fd954310eac6250c43ad1854310eb86050c4397d954310ecc6250c43b51854310ed86050c43a7d954310f1f6550c43e3d894310e9c6250c43e31894310e8c6250c43e5d854310e
  | 13 => 0x449100000000004600378000000000000000114e02545929100009b7035219453e1e53ca8cc47682a6091918418c00000000000001892bb00000000000001e00dbe62a150800000062b1420000fda02f000000000057e1c90000c4e31713c95140000000f4823804486f1a4905c71c00034713fc9888461f3022000026600006940005550000000e845d61618a241ce42000015090b21780000000a688e10398000d66261000000000000000000002aa000258813071000000000005e49fe0000d0849000000000000000001d98000000a2e0000000cc000051e1d2c000922000146d1c65af000097d160000000000020e00005d00000000001b016a800042d51a000000000037b80000006db09280f8df637700000000005610c500009ac16f0000c1c7426fe13e83789c07aa168144800040323818653d200000011c49200003a68be8d6a09e37f8000b6c507338201c6d25be0368ab49c82261570e6d1a41643cb80000005583698e7807e9d31720b947fc86c0000c0444a093000149868a000189926cc92000220000000099625318f84da84e4e788f4f8073c09a0b7cb289275118000bf87a02608000eac6a93e98000b8c959106800001400800800000800400000000c00000000001001403800c05c00000002401000400000802000800000000000000001400000400400001400000804800002c00c04005c02000800800000c00400c00000402400c00000003c00001c00400c00009000800400000c00001004c0100180d800001803800407802801000001000000001000000400c00801400800000c00000806800000800002000401000804400c02801000002c01c00000400000400400804000000002400400400006800400401800400000000000001001c01001402400c00800400800000400000c00000c00800000800c03800001400000005c00401c04000c01400000000803002800000c01c01002000400001800400c00000c00400004802000000800000000001400800000801000001c01003c00000402000000002403000401402000802000000800002400800001000000800000800800801400000000405000400001001c01401801400c01001000c00000000001000c01000000c02800400400000800001403c02800401000002800000000c01803804005400801800401c00000403000400400000000800000000000403401c00400c00000c01000000000400400c00c00c00400004c00400000804400800000000800002400001001401003801800000c00400400400c00000000000400400000000001802404c00802000000001400c00001400400c02800003001c00001000000000000400400000000005401000801c00800000007c02801001000400000000400000400003800804c00800800801c0040080040240180
  | 14 => 0x4000009b201c00027b085456a2a7866012200000019b0000181000000000046727e00000000000000000000009000000000000025c8730798707498255856c000000143c0000000001b34000949000245000000000024a416a90f13f157075e3533108000000308000009c0cc0003210bc0da826a2e11d7400021a4992624fac2593530000bb879b00000009e08960001a8400073434100010c26f04bb000051000050ba604c880001490000c5c7013ed086d3c4955515836432e93c116a37c4228d6281a854feaa080000b7054828006482f526631d231125c92800043f88ed00665d08898ece380002b293500005f93f0000082a93f4a594852d63a832f0eb51f00002e2000004c0000001e4c0000003d980003a4171477a2288e6410000092c0b20004b01f70ca600017725dca90162171800000000011e0000d16000000206038e36d2fa81411a20830000efc0000b2051800000022800018bcf4478c28117680008b11ca13882783fb493019c8f241d1550bd40006e2075a03438c1bd39480f40007214a09c18000a4a150000000000033780009ba6d14490fb47be262123807890a1874d096589181510e987d01d81742bc00011385bb0dd80000007201b086b80409851c3800059c0c20d006bc00000034e0000c749fa0002638000000000000000015e346139838a0000000e8c84896f0000e98000000000000130e13200000000001ca4a0000000004352116f13ac97f44d8df4e2aa510f800a46cc34100027f400037236e000147654e13e0000f1476c000222099216d2cf00000b45ce38d013cfb02d84b50250a5a25b19397dd4667940f08cecc461f1449a54009234613b89541fca5403d1f383b03761a78bad0606ae38c1cb836e4991ad14cd0b66520001c506d05131f5000111255e3b30000b9a2b0429116867e9d539f0f6c0003001639c44adc70b01da03c15a2742c596a0c3852423a83854422b11a52030b349983ee9aa83ec4ab03e9db453c0002d880000000004e2800000000000000740000004209c7c40c00047200000009a500025790ba00024c12c90801674a2067019a0003a78608df252200000143580000000000000328000000000024e2ff999119000039980007e036e391a72c0000a540592c00000003b281b11c43193442700762000190a0749f49e851323d448217b45316dc48467421281588f010040d990d49a52b29b8000230a1a19a8fa108a0001e709500002bb03f109d0740000001ee052200021a011c00000000000003d03c32da076c4200000000bf901200000022a0f72829000000000000010b07ac2cc00000000000005f82b79f1cd2a6960ee19e42425f344381d93345a4435266c65e7ab2628210000000244a1c8e360003f48e6017848a189000090400000000001300001f1867532e00045c91d11
  | 15 => 0x6ea2122fa00009dc53000022f40001a62ba8c8c09000000022148ae12a23300000002af00002840006bd0000000c4c871405183c00010319e80006ac44f0ef062c000566000000000000000000000006d007c1d6400000000018fc0007d92f0000009650c029a5480000cf0000000000a484968000c34272000147536278d24d14f8ed4895342037ce728d908a0fb940e84d4d681000002e638480002246484111c002202874f20000000000000277c00051c00000011a600024b28506b027604f91740003e02be960cd8c6084809ad137a55b1e295b12ea000000140000097e1c28000ac635e00022f906c816222a5a42e42bf097a3b800000027b0cf0000000201000000000000001c04a42ec11a80b123c00051c8000e7e37a4d71ab00004c61a39ed8ea62730000bcc33c5922f699cce441280001f28832a0a0ed00000000000a7000056e00000004d89400000a01c3c000a1f00017014047a94f980009ae00003000010ec7384960d3026a0003b018180002972788000b0863750288245323f929c134c0006a34fc88f80000000ad800000025812800001f400000000000000b02c484704143fd2681b2485066715c00b88bc3c200010500009a800008fc8225d900004acfca11e0bb20444288101cb25d07085110000000ab461000015ed1b8000376209c0000000000000f8a30e4c1872c00000040b80000000003510bf40002db319a4f50f09370000e2cdd458f34a080800067c00000003f09f23bb0480e3a6040000000b860ef4008e0934e36c000086004689e19f21783808060001d1814c0002430a88000a3f0df14543d4000000000135826500000000000000001e20d0c7450000000f048ae3ff9120fc201919625f107800018199ac5960160000dcc59a6e307921e8c8c3d7000151c00083123d04303ac0000000e7c62a0003eda6a907a30400006a52b80720a90000ec45d33488000be239128c80000005951b100000004e900000000000751ca93a094637907e945c6a04630000aa4efa41c00003a8d8a77c5239d205f02c603c89700001b6000186000000044c13440000ce30682f80000001c1860000011d261a3288f84814ad000000016b01d00012c649300010480000003cc8000c120004ac29140006753238000e9400041da0ac000232367863523299f47c942cbd608c00010ec0007274c58000f2c00023621f80003ec0f99c98ffa7bb00000011740000000c2800057049d89accca843284985105a6bf00000000004af0000a0c0009381b7853cfd867e1e782a48d22bc2ef1434000000000000000000045f8288ece6d91b223a4ee034400000000700000001530bd42011d60878b8a7983d6800145a0000f716290a89a9000218c00044600000011da8fb37001c40006e51ad96cd3ea00042580010b48cf00000006fe0004
  | 16 => 0xdc24da0018620356000445a48483e881203a1a48aa00010715a528e9b9300000148c000000000000000000000009660000d99b484ba8d417b24bc0009d1000000000000006980000006dd00000000000000b800006e00000ae0190000000206987866681300000014025d83d3a7347480000000ec03fc130074a6e0c6800033d8cacf902e144b9a0019668f00008cc00006800000013322ff27e80001e292b0001e1c59e7610000000abe0e6134800000033a20480000007c44118ba8b0e05144f80007b41ff25d80009f07cc30718d40003e50000000000943000094c0000005188da80008564e1937d4243991c5131d2680dd08b16352fa4873e9167437451020c28a084243f42aa7242161e400018a0ec600000007ec7a43f427a80005de5a934800012a81b42be00010086010000000b8e000375a2cc99e93600791250e83d303109e80009c200024442b0663101a480f5800007a800045214c4cf0408c623183e58b24e5e1f2000079c7540000001d5d2c8000000056475261217380000340410f314a400031b00003100100f600000013d40004b90000cb013a5098000000000019800086c49e00017b01000002b205207ee3f351c09143628b60b0152c00019014800000001d51888d74ba88aa2de852d3741ec1bda45cc1405700000012005390b082b13e8256000064863c00016084e0ac400000008000000002a223f0df814646700000000000001038e486983731c592ba59c1560c2c00045225b90980000000000a9c0005e54828000bcc00000000000006b70000cc828489109619c4f82a2f41b9fcc0007f4000000000000005ca4601b40000002314000000031800000000006b000049800011b00010a017c3cd0a54000000000000000000000016080000000a480000008b500000008d400000000c84dc000524a39c3825e30ca223c0000003f40ef8cb88140000e300006a02828ef133835c3db9ae87b2a0b0001210c0a81c0de0a300005ba0001f7c47018535780013bc4440000c940002242991e7000028b3b780000be1a3285219800017911d0c980003e74310000a822fc29180000000000001e1800037e000231865a000082948000073a00000011f40002c710f05a200000000000002d32eb84f91e896222b0d9400075200023546aa0001599d68de80000001f9000070237912b12ae150000149c000000000000108400000026ac11a000328132821e47b4b71efc75c1d10002340e066cb0bd02246be75106380005042de4d81a9c0000004ee19dc000000000172c1ee00000018b00d600043e81dc0000000002210000a0e0e6800000022b08d800144472841328007b04e30000d5c96c0d51b1a7f13a87791cd01340003373c5800000000000014fc00029d4e40000cd45a61269880aa0000116000000035432c9b90
  | 17 => 0x3b62b40000afe00000000000000000001b391424130e49e141b01a80001b20c5a00049700013a43fa1dd06c904003000010bc0008db47ea6ec1245b500020380006f839a800137c05d1a0273815600b33f8000882000000000070c0000cd8000000a5349a80000000000a5029c1fe0002bc80000000001921a240008022378000a9a00045684ec0007ba2ae8fc47d228d52900004f000036d00005da000226000000000024e01600000000000000f8c0000000000a1000001c80000560004e39a28000a1b0d3a844d0694d1200de144e9e100019548b60004ee922ce549660001e408361934b986392549243fca2393287433621c7800041a27528f8e5a7f700000001205fb39d80008a87440099fe8fe200013019b82b46fa51b26d43da97b29605a00006d646024a051e1ce0e20f8495020739921ed3487ef00000004320004e3064549669e000020800039751800000003c100115cc00005e47305b039015d05b935400048f254a8b0a5e0000001664c486c00e78000c70a4e034800000024a0000000f48000000006c0000003d180009b081f37411dc48c6b24759d548a6979000280c3480004ad800000000000028340005fd0000388e2426841225200940000000000a6c0004fd91f91180000000968d486ad1eb1f3471a0003d928a45680003ea91f49d85143f39dc8f12000000141043800000017e885c00000014e941829a3129394816736022992d3d65ab20f07508668a50c20e24bd01d73608000e9c0442c400000ca3c82a8a710de20003fd800000007f38c87f13dc2854468ed489c0d400000003ea1082ff14f0000000414000000091c32880013b40003c90000000a1d3959724000000292800000069d151800012a3d12ba1f8d2843061e682288a21454b60e94af473103c026855030f0000ce04886542bb927528a69b235a94026660b41c227523e4f2087168ccb489a00000000005e74c923dc0001c20000bec0000004bd000000000022fa40d16800000000001da83205a000016c31a2759aacd0e1ef253877c0000003d8000049e00046380004d800025e055800042906028a824e1390002020a8086e0000000c0400000000000000000001ae4000000265800033e0a83498e810f21e23b71404e9800625e8000aa46e94e080000009652fb000029a00000000000002c416c94c53406ef0000000c9e000000000099a17d00000012a200000019f4b0c44d32000000c2000000066821400009e92852a630d24183e4a0c0ee2971c3000000000025e0000773000217c54a09901e16c8f3a4321b89cdd40c0002870138a920003f5898c0005b000024680004350caa6753f011a3bf9cb120400000a9da47fe000117035d4202f933d0af516e2310b9a0a81a29f70df9fc00009090001d907380fb47f800051c5db
  | 18 => 0xa1691e0d2465a201891c89ce27108fa360c1834b4618f410001752a181f00000004a5000022646842ba90000063612b800081023900000001e64f90000000a8ca432e900000007770001e8400000000011d80001b500000000006563d3016ce0a0003309d50000000416000000033044a03200000000000d44b7013f115082097c0000000b680000000000f100008af000000000000000000000000001a680009b600000000005848ab41a187c0004dc3d7a75d19600028f92d0ed663930a8c08000a323fb000000000000000007960360001660628085000178859800041aa2a49fc51600003040001f9452001ccae3203528b289445d51ee049800040f1dc80000005df00005500004ef4c680001c600024407e8652000000159cfa818348200000683ab31480000008480000f753260002d70000e928e819500000000000dc1eb8000a1e1a90c4000027b3ef00000000000000d9c00061d3fe00011789f11a415c400059319c95811e640a512000000017700000004424c8000163000086d0000000fa22e952a8e4c00000049280000009e0083000000000041980000005dd0000ac800000000024751ba6920140000daa0bb178800031e000000184c1404013f7224122a26f2c81ae000040c35e000060a9a24b422ec74469910627640142643a3a6d0fcc2934860000cbe7a505f99a4ef0990091015446800000027b458a83f0000f24d987d73cf2810aa8907486973006a8f64661dec12c98a37e8bdc95c7813881dc40000000cca3b0f780000d80000416a192d08c7c000000000000120c47f4432584c0e6763390cd930493a000000000084c41f185892a4b538984a42c6a1c48925300008da04788546442374ca8630d624474300b00000000000000000000000027bc0007e21219e10000464045a14536c17f00000000005f20b2a3a8dda0000ee8394e108444d9004522c081382043400089900010b02a69e33af1ef88460003311f40bde7252e5259c0000004c8a0e4dec00000016b10b00003cf8f1d3cc45033c23941a070a00a154c3b200010b9dd0b023c00002324de600035f000062c00000000000007ea40d1b9c7ec1372030030000000000000149e37422c1d6142c10900001ec69c4f7270800000000029e97a45e84432cfa740d600001ef03280008fe51d1238efc0b331e12e80008a036190003544304e62304f7a15f17128806380242690000000000000196c8dc64a52080010941e34a704052e00000001e3800082527a24f80000002e08924f92000488112c0000dc0000000000267000000095a00015c800022a9f60550a1887a86721899040009b31d914613fe000000000056a9bf4c40f50f680f42e400000007680a39ed4e2e1191ac80000000b100000011e28472028000a3498000000000000000720fac93e86812f000
  | 19 => 0x8ca2d64c320153180000fe80342628a300013b400098f1de80011701170000000eea00026110e44a26b63ff1d6c0000000001f0c65c4de0001c38a9400000005f919a5f00000000c8a104000000121c16e49c825c0006ee417800139430c2dfa048ebe64e37aa17053888346f12489e642b016836c86e43a36f1de8b3605c4ec02bc13a00000009d45368150d68b5410c3b830d9aa0fe446d2cb88100003ef0000b500005564f397400000003e7980cbc215725297444fe01205212fc01c5a51178af947a09b00014788b828a33300a90ee37c34f916440a40416e8000c6436b4de000146a223311156543000000000000002304b69aed158381363a894a760000000fd44260000000150000000240008400000018480003c0000417089c30c0000000e752be7f800200003ee00000021d400000031800001e074114a000134600015d253c0000b8435a46d3ca66d00000009540001d38000000270000000000000043e212410e6850d09cc0d2e000000000015c8f00b48040c983b70001a6922675c2d01e3c00038f3a024206869840000000ae4617461068800052a000000000073d00013000023e41c801481382ab4320a04aae1c300c0b20b726683469d400009db00000010325ee29414d425a12400000008448532e78000000000000000003e141107800000000036500007004381ea8888b2281e4d79e4400000010f80000004b811000011ae946308a084b0004600010f8000000000123482c33447928dc00000000000000000000000000000000174051134c5850e81f081d09f03868f88b4e0cc3d4000000063d0cb23109f644a1dd830cc9a8a200011082d487342781b81a404206283f07f05e4266000043a0002521a04dae0371e5238028601750783810e056b2d6a42c7e42d72b68a6141212e52b0f192e2a4c1fe1ec52620740dc9b085c06d814b133800090
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x8590744c030042e1b926018021701c9300c010b84e5a0060085c172d0030042c9384801802134dd9400c010aa6eaa0060085c37250030042e03928018021649c0400c010d24c020060087125010030042583a2ca180212c9d2630c010b24e931860085917498c30042e1394c618021705ca630c010b26e8a9860085907454c30042e1b92a618021701c9530c0109a2ed21860085537550c3004348322861802170dc9430c010b80e4a186008553754c830042c9ba26418021641d1320c010b26e8b2860085907459430042e1b92ca18021701c9650c010ca2ca32860085537559030042a83aac81802170dc9640c010b80e4b206008691641903004269bb2a818021341d9540c010b86e4aa060085c0725503004388aa0a81802154dd5620c010aa0eab1060085937458830042c83a2c418021b0588620c0109a6eca9060085937454830042c83a2a418021d0548520c0109a6eca1060084d07650830042a9baa8418021541d5420c010f028421060086926390320043493188190021a458c40c8010d24c91864008692640c32004348b206190021349cc64c8010d24c931e40086916498f2004349322c7900212c9d063c8010b84e7a0440085a274cc220043c02046110021e09003088010f008018440084b0701912004268380c6900212c9d84048010c66ca20240086936310120043483188090021349d83048010ca6ca1824008693640c12004348320609002168dd12008010b40e890040085c37348020042e039a4010021709cf4008010b82e7a0040085a2709002004271bb2801002158dd54008010b86e6a0040085c07350020042d13808010021a89804008010e44a020040085a274cc020042d0ba66010021709c23008010f04811804008780408c02004271bb2601002158dd53008010b46e898040085a0744c020042e13806010021b09803008010e84a01804008782400c020043c020060100212c1d165080109a0e6b2840084b274988200426939cc410021389ca6208010b44e931040085a17498820042e139cc410021705ce6208010b46e8a9040085a07454820042e1b9aa410021701cd52080109c2ed2104008563755082004350322841002170dcd4208010b80e6a1040084e1768c820042b1baa641002168dd13208010b40e899040086c0634c820042d1ba2ca10021681d16508010b86e6b2840085c0735942004330b28ca1002158dd56408010ac0eab2040085c37359020042e039ac810021a859064080109c6ecaa040084e07655020042e1b9aa810021701cd5408010e42a82a040085637558c20042b03aac61002168dd16308010b40e8b1840086c16318c2004271bb2a610021381d95308010b46e8a9840085a07454c20043a0a98a61002138dd943080109c0eca1840085637550c20042b03aa8610021e050c4308010
  | 1 => 0x40042c839a4220021c81492110010b26e89886008590744c430042e1b926218021701c9310c010ca2ca18860085187459430042a4392ca1802164dd1610c010b20e8b0860085c37258430042e0392c218021469d2510c010a94e52886008551759043004269bb28218021c4151410c010b86e4a0860085c07250430042a8bac421802134dd9210c010b26e890860085907448430043a0292421802168dd12108010b40e890840085c37348420042e039a4210021985942108010a50e8b2840085487359420042d1ba2c210021681d16108010b86e6b0840085c07358420042953a4a210021529ce5108010ac2eb20840084e37650420043902a2821002170dcd4108010b80e6a084008561758c42004271bb2621002168dd13108010b40e89884008740534c420043493188188021a458c40c4010d44c420620086a16210310043493206188021a459030c4010d84c418620086c1620c310043513204188021a859020c4010d84c610620086c1630831004349b188088021a418c4044010d46c420220086a0621011004349b206088021a41903044010d86c418220086c0620c11004351b204088021a81902044010d86c610220086c0630811004269386c6aa021389c36255010a28e6aa0a808524725505404259386c8a9821389c36254c10a28e8a98a6085447254c5304270392c1a1821381c96090c109c4e1b1286084e272d81430428a3aa8621821611c94310c10b20e0a1886084b270d915204269386c6a9021491d15214810a88e6a90a4084d073583420426839ac121021349c363508109a4e7b0284085247550842042c239a8421021681c14210810960e8b0664084b0745823204259386c8990212c9d3604c810a88ea9906408584744c832042e03826419021b098e62d0010d82c731680086c26358b40042c9b9a8020021641cd4010010b46e4a0080085a07250040042c939cc820021645ce6410010b44e532080085a17299040042c9b9aa820021641cd5410010b46e4aa080085a0725504004299baa862002168dc94310010b40e4a1880085337550840042c9b9a8420021641cd4210010b26e6b2880085907359440042d1b92ca20021681c96510010c62ca32880085337558c40042983aac62002168dc96310010b40e4b1880086916318c4004259bb2a62002168dc95310010b40e4a9880087115314c4004299baac4200214c1d56210010b26e6b108008590735884004350b10c4200212cdd95210010b26e6a908008590735484004390a90a4200212cdd93210010960ec9908008533754c840042983aa6420021e04c83210010d44c520660086a2621033004350b108198021389c864cc010d44c931660086a16498b3004351322c598021709cb408c010964ec2026008633651013004351b108098021a8188404c010b26e898060
  | 2 => 0x8618041a2191430c020b86e2a1860105c07150c30082a5baa621804162dd1310c020b10e8988601058b7459430082c43a2ca1804170dc5650c020b80e2b2860106496519430082a5baac818041521d5640c020b86e2b2060105c0715903008344b20c81804132dd9540c020990ecaa060105c37155030082e038aa818041c2550540c020a96eab08601058b7458430082c43a2c218041b0584610c020996eca88601058b7454430082c43a2a218041d0544510c020996eca0860104c87650430082a5baa8218041521d5410c020f0282208601064a5398b40c432531ca5a06214a9c85310310e14a729081887095394840c438529aa420621469cc5210310c54a9316618862a6494b30c43852908118621c294a400c310e14a420061887095210030c42a5390a818621c2952520c310e12a9290618870a5454830c428d3a0a4186218695263c8310c34c929e418870a5310220c43852a06110621c294e4008310e14a620041887095310020c43852a46010621c29503008310e12a8180418854a7315020c43852a4a610621c25525308310e14a8a98418852a7414c20c430b2a0c6a0c21899506250610a2ce7aa0830852672d50418430a324a698c219194c624c610a2ce9a98630854672d4c3184312324a490c219118e5248610a4ce9a90430854673d48218428b39ea92a421499cb5495210a64e1aa4a90851674d4e53842a3396a729c21549c35394e10a2eeaa1887085847250c43842c83828621c21499d35294a10a8ce7a94a50856270d4a5284293baa8421421611cd4210a10b40e0a108508547754c832842c23a26419421701c1320ca10d44c420661085c272d0030843493188190421a499030c8210f008018441085c273d0020842d13a66010421e01023008210f04801804108780400c0208428c380a818221469d4400c110c34ca200608870b52100304438429080182214a1c05408110a90e0298408852a7510020443153288010221c2d4c4008110e10a6200408854a750c020443253286010221c2d503008110e10a818040884d0735824104270392c120821851506350410c48a831282084d273d814104271396c0a0821451cd5410410a48e4aa082084b0745823104270392c11882185190534c410c88a631262084b274d813104271396c098821451d1530c410a88e4a9862084b074582210426839ac110821891905248410c88c629242084b274d81210426939ec090821491d15208410a88e6a9042085937350440042c839a822002168dc94110010b40e4a08800863165104400428c39aca200214a1c96510010b26e6b0880085907358440042d1b92c220021681c96110010a34e7288800852a729444004298bac62200212cdd93110010e20a698880085a3724c440042d039262200214c5d62110010966ec908800859373484
  | 3 => 0xcd6510020b16e6b1080105887358840082d1b8ac420041681c56210020a34e72908010529758c84008255bb26420041c214d3210020b46e299080105a0714c84008255bb2422004162dcd2110020b10e6908801058b744c830082c43a2641804170dc5320c020b80e29906010649650c8300828c3a2ca1804162dd1620c020b10e8b1060105c37158830082e038ac418041469d2520c020a92eb21060104cb7650830083842a2841804170dc5420c020b80e2a1060104cb7648430082c5ba24218041621d1210c020d14c620640106896310320083513088190041a858440c8020d14c81864010689640c320083613086190041b058430c8020d16c62024010688631012008351b088090041a81844048020d16c81824010688640c12008361b086090041b01843048020994e1b1aa8104e270d85540828639aa82a041491c55415020954e1b22a6104e270d8553082863a2a629841511c55314c209c0e2b0686104e0715824308271386c2a1841389c76050c20a18eaa1886105847150c43082c438286218412a9c36454420994e1b1aa2105247454451082a239aa228841321cd60d0420990e6b0482104ca70d8d410826539ec0a0841491d54110420b08e6a0882105a07050441082543a2c1988412a1d1608c420954e1b2262104aa74d8131082a23aa6218841611d1310c420b80e098862106c2639874008360b1cc3a0041b098d61d0020b16e6a0080105887350040082d1b8a8020041681c54010020b14e732080105897399040082d138cc820041685c66410020b16e6aa080105887355040082d1b8aa820041681c55410020a56eaa1880105a37150c40082d038a86200414add54110020b16e6a0880105887350440082c5b9aca20041621cd6510020b46e2b2880105a0715944008314b28ca200414add56310020a50eab1880105a37158c40082d038ac620041a258c6310020956eca9880105a37154c40082d038aa620041c254c5310020a56eab08801058b7358440082c439ac220041a85846110020956eca88801058b7354440082c439aa220041c85445110020956ec98880104a8764c44008295baa62200414a1d53110020f026218880106a26190330083513088198041a858440cc0209c4e232660106a2649873008350b24c398041a899161cc020b84e3a0460104aa761013008315b288098041a8d84404c020d40c2202601058b744c030082c43a2601804170dc5300c020b80e298060105c271d0030082e0b8e8018041629c2400c020996eca00601054b7550030082e1b8a8018041701c5400c020b14e0200601068a60100300838528080180412a1d1650c020954e9318601058a7498c30082c4ba4c618041709c6630c020b82e3318601058b7454c30082c43a2a61804170dc5530c020b80e2a9860104c97690c30082a5baa
  | 4 => 0x16e49888018588724c4400c3453108198061a258840cc030d24c2206601869161103300c345b108098061a2188404c030d26c2202601869061101300c265386c4aa061349c36155030a18e4aa0a81851471550540c24d386c8a9061349c36154830a18e8a90a41854471548520c26838ac1a1061341c560908309a4e1b0a84184d271d81420c2863aa8421061611c54210830b10e0a10841849a70d91510c265386c4a8861451d15114430a88e4a88a2184c872583410c264392c120861329c36250430994e5b02821851475504410c2c23928220861641c14110430930e8b06421849874582210c24d386c890861269d36048430a88ea908421858474484210c2e03824210861b098a61d0030d82c530e80186c262587400c2c5b928020061621c94010030b26e2a00801859071500400c2c5394c820061625ca6410030b24e3320801859171990400c2c5b92a820061621c95410030b26e2aa0801859071550400c28dbaa842006164dc54210030b20e2a10801851b75504400c2c5b928220061621c94110030b16e4b28801858872594400c2c9b8aca20061641c56510030c32ca328801851b75588400c2c9b8ac420061641c56210030d12c4310801849b76548400c2c9b8aa420061641c55210030e12a4290801851b75584400c2c5b92c220061621c96110030d22c2308801849b76544400c2c5b92a220061621c95110030e22a2288801849b76484400c24c3b2422006146dd52110030a30ea908801878121084400c32929cc3a06419498e51d0320a64e229881907125394440c8388a9ca220641c494d5110320c64a930e61906326494730c83892888118641c4946400c320e24a220061907115110030c82a9388a818641c4952510c320e22a928861907125454430c83072a0c6a1441899506150a20a1ce7aa0851052671d504288306324a6994419194c614ca20a1ce9a98651054671d4c3288312324a290c419118e5148620a1ce7aa4a91052671d525488295386a92a441439d35394e20a8ce3a9ca71054a70d4e5388287baa8621c41611c54310e20b10e0a18871052674d4651882a339ea328c41589c35194620a4eeaa0883105847350441882d03828220c4151dd5310c620b08e898863105c0704c431883513088198441709c7400c220a34ea200609061a651003048389a888018241c4144400c120990e6b0484104e07158242083062a0c6a1041891506150820994e7b0284104e271d81420828639aa821041491c55410820950e8b0464104e0715823208306320a6990419114c614c820954e9b0264104e271d8132082863a2a619041511c5530c820950e8b0642104c87358321082553a6c090841329cf6048420a48e8a8842105447354421082c5b9a8420041621cd4210020b46e2a1080105a0715084008314b288420041461
  | 5 => 0xd45750c83108722b286418843299d2644842198ce73224210ce2709912108653380c890843a1193634842194ce931a4210cc67398d2108671384c690843a1d906348421d08c831a4210cc67018d2108750326c090843b018f6048421cc6ca3024210ea3641812108750320c090843b0d8c6048421d80c63024210e63751812108751ba0c090843a81d06048421d86e63024210ec07318121086923a24328043511cd2194021ac0e090ca010e0e53189439030b298c2a1c818318e5250a40c4ca430a8520614639454190312314a2a0c81439cb5394e40a2ce3a9ca72051a70d4e539028739ea529481499c75294a40a54e1a94a52050f754c832902c238a6419481621c1320ca40a2ce7a8ca32052672d465190299386a328c8145dd5310c640b08e49886320590704c43190293baa4210c81611cd2108640b40e090843204a872583431025838ac1a18812a9cb6050c40964e3b02862050c7254c431028a38aa621881261cd60d0840960e2b06842049a73d81421025938ec0a1081431cd5210840a48e2a908420498735834110254392c1a0881269cf6050440954e5b028220514735444110292392a2208812a9c36254c40964e1b0aa62050c7254c531028a38aa629881269c36354840964e1b0aa42050c73548521029238aa4290812c1c560cc840960e2b0464204b270d85321025938ec099081431d5320c840b08e29906420588704c8321024d386c6a88812a9c36254440a28e6a88a220524725445110254392c1988812a1c9608c440954e1b1262204aa72d81311028a3aa6218881611c9310c440b20e0988622049873583211024c39ac110881269c36348440934e7b0242205247548421102c239a4210881681c12108440cc4a530e81986626294740cc391294a220661c854a5110330e44a4a88819860e54189438c30b2a0c2a1c61439cb5410e30a2ce3aa0871860c64949328c323290c29946185192514c630c88c528a631850e72d52548c28b38ea92a461469c35495230a1ce9a94a51854671d4a528c2a5386a52946143dd54210a30b08e2a10851858870508428c28b3a6a328c61519cb5194630aa4e1a8ca31851775504418c2c23928220c61641c14110630a8eea908431858474484218c2e03824210c61321c96090c309a0e2b04861860c54189430c30a2a0c2a1861329cb6050c309a4e3b02861850c72550430c28a38aa821861261d160cc8309a0e2b06641849a74d81320c26938ec099061431d1520c830a88e2a90641849874583310c264392c198861269d3604c430994e5b02621851474544310c2a2392a21886162dc94310030b10e4a1880185937150c400c2c838a8620061865944310030b16e4b1880185887258c400c2c9b8ac620061641c56310030936ec9908018593714c8400c2c838a642006126dd93110030b
  | 6 => 0x310a8c382a621885291c56210c42950e0b10862148e7018d4210b4231ec2a1085a1d8c6150842d08c630a84214a6701854210b4431ec0a1085a81876050842c56ca302842168b631814210b44318c0a1085a8d846050842d40c2302842162b751814210b45b98c0a1085a21cc6050842d46e230284216a0711814210a8639a8528085491c54294042a50e0a14a02152671d5042cca95386a821665459c75410e32a34e1aa0871963264987504cb18320c2282651c1c16115032a28e2aa0861951870550430ca6238ac421865321c16210c32a48e2aa0841952870550420ca6238ac621065321c16310832a1aea218841960d6510c420ca473a4c899065319c6644c832994e1322641948e70191320cb42326c299065a1d90614c832d08c830a64194c670185320cb44326c099065b0187604c832c96ca302641968b64181320cb44320c099065b0d84604c832d80c2302641964b75181320cb45ba0c099065a21d0604c832d86e230264196c071181320ca863a26528065511c53294032a90e0994a01964a6398b5050724318c428283431c95310c41a30e0a988620ca4725844310658382c221883431cd5210841a50e0a908420c94735844210658382c221083259c06350441d08c7b128220e87631894110742318c4a0883299c06250441d20c7b028220ea062d814110719b28c0a0883a4d8c6050441d20c63028220ea3621814110750310c0a08838cdd46050441d26e63028220e90731814110751b90c0a0883a81c86050441a28e6a0ca020d247250650106983828328083499cb5410731a64e1aa08398d0e72d50438c68d386a821c638a99262d4131c50c8310a098c6870588540c686392a821863461c15410c31988e4b088618cd070584430c6863a2a419063521c1520c831928e8b086418cd070584320c692392a8208634c1c15410431988e4b188218cd07058c410c68aba8862086385594431043192ce93226218cc672991310c669384c898863259c0644c431d08c9b126218e8764189310c742320c498863319c0624c431d20c9b026218ec062d81310c729b28c098863a4d90604c431d20c83026218ec362181310c760310c09886394dd4604c431d26e83026218e9074181310c761b90c098863b01c8604c431a28e898ca018d44724c6500c6a83826328063459cf5410721a64e1aa08390d1674d4c31c86a9386a618e43439cf5410a21a54e1aa08510d0e74d4c32886a5386a6194438699263d4121c30c8318a090c587058c540861c382c829843431cd5410821a50e0aa08410cc4735844208670382c221043431d1530c821a90e0a986410ca4745843208670382c219043451cd5410421a60e0aa08210cc4735884108670382c420843495d44210421c4aca2108210d147454c31086a8382a618843291d1620c4219c0e0b10621
  | 7 => 0xa8b351c91cc354cc80001f02f8000064a5c000c987a0000918ef8000000ce0924ff4f1866521096c5a800034883cb84458e0843c3e47bd110f25044e28001219049038d0c8002987685dc63c7cd290f84b540acc4c0ec3308b839c9d508c000cccc289b0158018c3c50002094868c860b28cf50c8fd0308000604424fc8050010374f4487c8411fc0603b09ec358000444aa4958ab0d14000c94bdc8fc0c8220f60b20e590f47040006a8970564000000bac000f1d1044800000e521c5609a8281050e40000508440900504260318ef10592000004306e0dc85ac584d088f098cd8c8e097c881030470000d0120cb5c920e80000000000c9ce3c0010ec9e82a8000000bf11d4f411c400034d198ec0b392803847e072c3500009f0aec26828ce6c8787c80bc000000d2000118000000077d27c000570b1424400000049c848000000000ad40140080200e01001800008008018150040000280300a000018010160480500000e00001001004038000140020000480f0000000a0030000040000601e024000000040040300000200c0580b002020060020000000100f012004010130000140500e04804c0000200401c0081100a0040b80c04a00808810006000010030020000d001000008040020000080000d014000008000060000080500000c010010020240000b030020018020020540000100600c03800012000018030020080100b026044020000240000380002c004020010120040000001800801000004004020060040a0000030000340080500400400012000004008020000080000000a0000480a0280400282a0000040200901a0240b816030000000000000180800300602c008030000780100600000414800000000070030060180000200007c000010000880080a0220c0280000000041900a0000040080001203c028150100140001600a0000500000404c068120020000001e012080008000020080200f00c02400801002000000050040000300300205c088010080240000000000400000008008000020000000000400000402007000010018000120040100b000008000000000080101e000004098000000680001200200808003006000010170060000000000002c000000100000600102400c078010000080000000001c0100200601c010000020200080000601c0a800000000000040de00c018090000000083d02802c0000c00001000662629875050f30310c228287239c06250c43d08c5b0a8621e87621854310f42310c2a1887259c06150c43d10c5b028621e9061d814310f0db28c0a1887a2d886050c43d10c43028621e93611814310f48308c0a188786dd46050c43d16e43028621e88721814310f49b88c0a1887a41c46050c43a18e4a1ca021d147150e5010e8c38287280879498e61d4142ca0c6308a0a15147154c4
  | 8 => 0x5400124c6251184d027d000de0e98001070968ea4d1c3650a48bcd840809bce8cfe0000e34001248000000b4400046019c000000e7919c78cf30000cfcd48d805b00005340000005947f499c8e88c02fc0010249c0000c342340004682b49e511c0010bc000000c400011f44f122492c0007111b4d7c000000000000000000000fb400081880c67c8100e00290b024c0007e8000000fa8820000c18b4800000076c000694000000b6c3e0000b404c0bcd03cc100010c055c990ee484c000e052640011749c8d18f69164485168000f7c000a58934da4cb4d2c000ca8311040eb80001fd06000126c2e8db8f98038335188488000b9cfbd0289d0000095034bbd25836c8e4ac8b4d1300004b005c1809a465d1d11608a8c71154000ba86f0074d90240c60658a80abcc7cff10d0000bb4f146ec79400000039053800000018c588000d54bfc02cc005d800000c5110f8c9017514cbc8ba4c2cbe4000cd05a01640000001d8000f940000003f86cc0011a84dc99447d04d004000001108888000000000000a0022400000117d06ce20de8a904b41ac33905ce9c728a3c6843b87d0f0c200408288a6c6dd0e06481845482a4d38cd4fb0b8000118ca50000dc4000000084b7d1ec5e414ce48000000ae00007384f400010020901cbec5683a059ccf0000634cd8f545e0000000000034f78f28f9000116cdf9209064c08000134e54004e380004e8000960a6400000074c000088000000b080a43bc7a4000544fb800000026cc6d00c0000000004542c421c188e7d0fc6d100838d254f6d0906549fcad0f58000ed40011500011411e4000b900006744cc000ce4000d340001b016000000000040ccb91b8fc4b0113421430444c9500002c0ff80011bc650000b2408c9c48444780000003cc0fc8ac0000000f8d79144f10000c648dc46c778984a40ebcdb4850b640005cc60c044530954314d04e84000000000c500004ac380de40000000009f40005750a84c4f34e94d983d47f0cb00005d4a20000a38b10528000c5800108523528c9140e804c00000000000007832cef431c0001c0fec89cb041a8dac3d00000006400004a42dc00090488d2400003b47185c069929c290f64c04e00000550000a4822875d2500000008701a4aad1e809c07c0007909284145b4000000e880000008952704a07dc1dc0008ec3d8000000000a3000000055869c2052a4ab40000000004385d094c000000f9cacc37d23c0a08084209886a4bc122cbf46b4000000f5cbc4000464744d6c000a88c0c0006c40007c47b00011147a86f47881a0b3c6d8a6000010d1e0fd48b41ec2f0734328e64000000a04ddc4d80f4770764264000000638580000aa07ac0006a10980002744900004c886d1acc444e42ac000ae40012991dcf002d079ca18e19184255294d681787e4578be0
  | 9 => 0x5b8108000000ad87200c4360dcc0000001191c1204fc071c0000000001c46b8758a74b75068000d88000a682940001e0345080000000d94190f0400000062ced0b506d43ac218ee00011f8000000c8d148628f8c3701d4e5c688e24b18834b8c39829ce14524b98b68dbcd24afcecd2a8d2853c1109ccf2073cc80ce820ca24910b1c0b450c24813c43464d010d10ffc3dcdf4af01d10181c8394000cf817c000bb0000058d4c00000097890c600bf8c745c4a8ca34a0c0ccae87b83fc61caa881cced2846685c86906c10ccca10b40b80000005ec520499244b588d86807fc8b0b94000250cbc0000006143c052cc540b04009e0000fcc5fd25c0008580006c80008f87b4c383c8dc00000000000000011b003c7306e8210eac30c5bc00000000070d0dc00000091c000f2c000cdc0480000691292209b507caf4e50e446791a4c242e05184f8748168198dfd12445c944a1425d078d30884e68008140fe8cc40009391f04d4fe4c146b0000cc08c423ce60a28000000ee83e800000009810513c00006c001288a84b0d1a00005e8000a980000000000000000011785a4000a70a7c368618000814138000a1cc5c908000c7800096479838800102c774124114001238a2c030930000014dd015ce2c3c483812841c00056d1940005152a08284e057cd5cf3cc84a449748cc1301450b8dec150f48cacfa0c480005f0b88780f74000740000d7400048c0004b82bd0d4000320000e0c7d44fc6088d11700010a0194000404000a10428bd4708000278d60000448418e30598a78000940bd0000efcab80549ac0250e47c0b2ceec000854ac0e9055433d0f01703f0b780f0000e74f4c1cced811c85ceb416d15c0000dcd64fa40000003000001e4f700d0f89094edc6e4dd4000fd8d3c8d4e101bd191158864410f80db0d401f52611001209dc0412140004a8a54868fdd138000000f080006107144ec000d582b00006fc7d80902387f814909c000000000ec4000d50000b300002580000000011d842c1b8eb045000095c0001b4f380003a412c0012288c82e4724001120001278c20070e4cd70d9d10cdf09800010750ac000000000e1d02000082c4942f40002a0af870001c0002d8000270adc5f458c83112c6308980007ec000d449b89f88042850e8000bb80000001e88a48a00012682d40008900000005f8a4c66c000ec8dd8da8000324000154000000000000000ea8da093c0006ac0000000002ed0140000000000010d8000000620000824e710880002b83ecc308749d8b608f4bd87847549a07600d4c1c3f4a940000d859000000035c660ca4000000000000670a9cac4474000644f500012300000003a8540b704bc000230fac1f800099822c0002cd274be86f8750340a080c051cc68000c8854c6bc2c8ba03790c4ea00010
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x5a000010004a0000006c0000000000000000080032000000007400006a00007a6272000000000000000002584048005e0012003a00560000001a0000060a820000001e007024000028783c461600000000001800000000220000340000006820425400000000000044502c00000000000000006000265c007e000000004e5200800c2e387600642a1c143000000000000000000000004c00007c000e366e00003e660400000004010200000201010003030000010601010201090001c80721c46050c43c80731c46050842c80741c4604c832c80731c86050441c80741c8604c431c80741cc6048421a80815886210030b00815485210030a80825846110030b00825445110030a80864842110030b00854842110030d00531c53210020d00541c5420c020a808158c6310020b008154c5310020a80835846110020b00835445110020a80864c43110020b00854c43110020c80641c5430c020a0884594650c020a0885590640c020a8081590640c020a0886550540c020b0081550540c020a8084584610c020b0084544510c020a8086504410c020b0085504410c020d00531c93110010d00731492110010d00541c9410c010d0074149210c010d00541cd4108010d007414d3108010a808258c6310010b008254c5310010a80835886210010b00835485210010a80864c83210010b00854c83210010c80641c9430c010a1084594650c010a1085590640c010a8082590640c010a1086550540c010b0082550540c010a8084588620c010b0084548520c010a8086508420c010b0085508420c010c80641cd4208010c807418d3208010a20845946508010a40835946508010a20855906408010a80835906408010a20865505408010b00835505408010a408558c6308010a808458c6308010a408654c5308010b008454c5308010a808650c4308010b008550c4308010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1140
  | 4 => 2647
  | 3 => 1195
  | 2 => 66
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (i*5) 5
  | 6 => packedAt s0K6 (i*16) 16
  | 5 => packedAt s0K5 (i*27) 27
  | 4 => packedAt s0K4 (i*38) 38
  | 3 => packedAt s0K3 (i*49) 49
  | 2 => packedAt s0K2 (i*60) 60
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (6+((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s0K6 (864+((h/16+packedAt s0K6 (768+(h % 16)*6) 6) % 58)*7) 7
  | 5 => packedAt s0K5 (34960+((h/380+packedAt s0K5 (30780+(h % 380)*11) 11) % 1655)*12) 12
  | 4 => packedAt s0K4 (111170+((h/882+packedAt s0K4 (100586+(h % 882)*12) 12) % 3843)*13) 13
  | 3 => packedAt s0K3 (62933+((h/398+packedAt s0K3 (58555+(h % 398)*11) 11) % 1578)*12) 12
  | 2 => packedAt s0K2 (4136+((h/22+packedAt s0K2 (3960+(h % 22)*8) 8) % 166)*8) 8
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffdfe0ffffff801fffffffffe03fffff0fff
  | 3 => 0xffffefff07ffffffe007ffffffffc07ffff0ff
  | 4 => 0xfffff7fff83ffffffff801ffffffff80ffff0f
  | 5 => 0x7bffffc1fffffffffe007fffffff01fff0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffff802210842592a4a9325896e2c58b167777
  | 2 => 0xffffa05e21084af6893254a92b702ad5ab0bbb
  | 3 => 0xffff9084f2109324dda469324db56066cdb0dd
  | 4 => 0x90847a11c4711c771c471d9b340f1dd0e
  | 5 => 0x610843de0781e0781f87e1e3c7881eee0
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xccc0c000c0000000ccc0c000c0000000ccc0c000c0000000ccc0c000c0000000ccc0c000c0000000ccc0c000c0000000ccc0c000c0000000ccc0c000c0000000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_15773
namespace PEqualNP.Outside.L_meta_15773
open PEqualNP.Outside.L_meta_15773.Model
def s1K11 : Nat → Nat
  | 0 => 0x1
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 11 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 11 => packedAt s1K11 (i*1) 1
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 11 => packedAt s1K11 (2+((h/1+packedAt s1K11 (1+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x0
  | _ => 0
def s1Atlas : Atlas := ⟨11,rawDecor 1 s1Pos s1Neg, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15773
namespace PEqualNP.Outside.L_meta_15773
open PEqualNP.Outside.L_meta_15773.Model
def s2K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (6+((h/1+packedAt s2K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffe07fffffffffffff87fff
  | 1 => 0xfc1f03f07c0f81f81ff8e1c3c387878787aaaa
  | 3 => 0xffe003ff800ffe001fff01fc03f807f807cccc
  | 4 => 0x3fffff000001ffffe0003fff80007f0f0
  | 5 => 0xfffffc00000000001ffffffffc00000007ff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x5546659329552ba16e5868d349a696970baaaa
  | 3 => 0x98caaaa51a6a68aab6ab117512ea277115cccc
  | 4 => 0xd294d34a53434d34db35ba222377722226f0f0
  | 5 => 0xe318e38c638c71c71dc6ddbbb8444444477f00
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaaaaaaaaaaeeaaaaaaaaaaaaaaeeaaaaaaaaaaaaaaeeaaaaaaaaaaaaaaeeaaaaaaaaaaaaaaeeaaaaaaaaaaaaaaeeaaaaaaaaaaaaaaeeaaaaaaaaaaaaaa, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15773
namespace PEqualNP.Outside.L_meta_15773
open PEqualNP.Outside.L_meta_15773.Model
def s3K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (6+((h/1+packedAt s3K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffe07fffffffffffff87fff
  | 1 => 0xfc1f03f07c0f81f81ff8e1c3c387878787aaaa
  | 2 => 0xffe003ff800ffe001fff01fc03f807f807cccc
  | 4 => 0x3fffff000001ffffe0003fff80007f0f0
  | 5 => 0xfffffc00000000001ffffffffc00000007ff00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x5546659329552ba16e5868d349a696970baaaa
  | 2 => 0x98caaaa51a6a68aab6ab117512ea277115cccc
  | 4 => 0xd294d34a53434d34db35ba222377722226f0f0
  | 5 => 0xe318e38c638c71c71dc6ddbbb8444444477f00
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xeaeaaaaaaaaaaaaaeaeaaaaaaaaaaaaaeaeaaaaaaaaaaaaaeaeaaaaaaaaaaaaaeaeaaaaaaaaaaaaaeaeaaaaaaaaaaaaaeaeaaaaaaaaaaaaaeaeaaaaaaaaaaaaa, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15773
namespace PEqualNP.Outside.L_meta_15773
open PEqualNP.Outside.L_meta_15773.Model
def s4K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (6+((h/1+packedAt s4K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffe07fffffffffffff87fff
  | 1 => 0xfc1f03f07c0f81f81ff8e1c3c387878787aaaa
  | 2 => 0xffe003ff800ffe001fff01fc03f807f807cccc
  | 3 => 0x3fffff000001ffffe0003fff80007f0f0
  | 5 => 0xfffffc00000000001ffffffffc00000007ff00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x5546659329552ba16e5868d349a696970baaaa
  | 2 => 0x98caaaa51a6a68aab6ab117512ea277115cccc
  | 3 => 0xd294d34a53434d34db35ba222377722226f0f0
  | 5 => 0xe318e38c638c71c71dc6ddbbb8444444477f00
  | _ => 0
def s4Atlas : Atlas := ⟨3,rawDecor 47 s4Pos s4Neg, 0xeaaaeaaaaaaaaaaaeaaaeaaaaaaaaaaaeaaaeaaaaaaaaaaaeaaaeaaaaaaaaaaaeaaaeaaaaaaaaaaaeaaaeaaaaaaaaaaaeaaaeaaaaaaaaaaaeaaaeaaaaaaaaaaa, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15773
namespace PEqualNP.Outside.L_meta_15773
open PEqualNP.Outside.L_meta_15773.Model
def s5K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s5K3 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s5K3 (6+((h/1+packedAt s5K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffe07fffffffffffff87fff
  | 1 => 0xfc1f03f07c0f81f81ff8e1c3c387878787aaaa
  | 2 => 0xffe003ff800ffe001fff01fc03f807f807cccc
  | 3 => 0x3fffff000001ffffe0003fff80007f0f0
  | 4 => 0xfffffc00000000001ffffffffc00000007ff00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x5546659329552ba16e5868d349a696970baaaa
  | 2 => 0x98caaaa51a6a68aab6ab117512ea277115cccc
  | 3 => 0xd294d34a53434d34db35ba222377722226f0f0
  | 4 => 0xe318e38c638c71c71dc6ddbbb8444444477f00
  | _ => 0
def s5Atlas : Atlas := ⟨3,rawDecor 31 s5Pos s5Neg, 0xeaaaaaaaeaaaaaaaeaaaaaaaeaaaaaaaeaaaaaaaeaaaaaaaeaaaaaaaeaaaaaaaeaaaaaaaeaaaaaaaeaaaaaaaeaaaaaaaeaaaaaaaeaaaaaaaeaaaaaaaeaaaaaaa, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15773
namespace PEqualNP.Outside.L_meta_15773
open PEqualNP.Outside.L_meta_15773.Model
def gbK12 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK11 : Nat → Nat
  | 0 => 0x20982581870f1c808b998b04222491848f9a068d8c169713911f1895099421261a87828510a683000015900a0006010c9f8580000000241d80090d17930000002396001e80001b0e1c0825229219088a8ea19d03a32012949e0000021b80010322002031a38102062811924082220000100021039314ffd5051fe5413ff5504dfc5412ffd4c49fe5311ff54c45fc5310ffd0c41fe430fff50c3dfc430effd4839fe520dff54835fc520cffd0831fe420bff5082dfc420affcc829fe3209ff4c825fc3200ffd4403fe5100df94403fd5100ff144037c5100ffd0403fe4100ef90403fd4100ff10403bc4100ffcc403fe3100f78c403fd3100ff0c403dc3100ffc8403fe2100fb88403fd2100ff08403ec2108ffd40237f50087f9401ffd5007df5401dfc5006ffd001bbf40067f90017fd4005ef50015fc4004ffcc013df30047f8c00ffd3003f74c00dfc3002ffc800bef20027f88007fd2001fb48005fc2000ffc4003f71000ff84003fd1000fd44003fc10
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x8a
  | 3 => 0x98a
  | 4 => 0x128a
  | 5 => 0x150a
  | 6 => 0xca
  | 7 => 0x9ca
  | 8 => 0x12ca
  | 9 => 0x168a
  | 10 => 0x10a
  | 11 => 0xa0a
  | 12 => 0x130a
  | 13 => 0x180a
  | 14 => 0x14a
  | 15 => 0xa4a
  | 16 => 0x134a
  | 17 => 0x198a
  | 18 => 0x3ca
  | 19 => 0xcca
  | 20 => 0x15ca
  | 21 => 0x170a
  | 22 => 0x40a
  | 23 => 0xd0a
  | 24 => 0x160a
  | 25 => 0x188a
  | 26 => 0x44a
  | 27 => 0xd4a
  | 28 => 0x164a
  | 29 => 0x1a0a
  | 30 => 0x58a
  | 31 => 0xe8a
  | 32 => 0x178a
  | 33 => 0x18ca
  | 34 => 0x5ca
  | 35 => 0xeca
  | 36 => 0x17ca
  | 37 => 0x1a4a
  | 38 => 0x74a
  | 39 => 0x104a
  | 40 => 0x194a
  | 41 => 0x1a8a
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 12 => 1
  | 11 => 78
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 12 => packedAt gbK12 (i*15) 6
  | 11 => packedAt gbK11 (i*26) 17
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 12 => gbHint (packedAt gbK12 (i*15+6) 9)
  | 11 => gbHint (packedAt gbK11 (i*26+17) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 12 => packedAt gbK12 (16+((h/1+packedAt gbK12 (15+(h % 1)*1) 1) % 2)*1) 1
  | 11 => packedAt gbK11 (2210+((h/26+packedAt gbK11 (2028+(h % 26)*7) 7) % 94)*8) 8
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffffffff80fffffffffffffffff421c3f87fff
  | 1 => 0x1c1c1f07ff0e0e0f8383e0f83e0bdebd57aaaa
  | 2 => 0xe01fe007fff00ff003fc00ffc00c1f3e67cccc
  | 3 => 0xffe00007fffff00003ffff00000fe03f87f0f0
  | 4 => 0x7fffffffffc000000000fffc007ff00
  | 5 => 0xfffffff80000000000000000000ffffff80000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x0
  | 1 => 0xc8c9d138b06464e8993a2e8bc11ce9d53aaaa
  | 2 => 0x6117a425d5b08bd212f484f7842c172e65cccc
  | 3 => 0xb7a10846e6dbd084237bde21084ee03786f0f0
  | 4 => 0x202108778ededef78210842108f7bc0077f00
  | 5 => 0xdbdbdef04081010840421084210fbdfbf80000
  | _ => 0
def gbAtlas : Atlas := ⟨12,rawDecor 63 gbPos gbNeg, 0xeeeaeaaaeaaaaaaaeeeaeaaaeaaaaaaaeeeaeaaaeaaaaaaaeeeaeaaaeaaaaaaaeeeaeaaaeaaaaaaaeeeaeaaaeaaaaaaaeeeaeaaaeaaaaaaaeeeaeaaaeaaaaaaa, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15773
namespace PEqualNP.Outside.L_meta_15773
open PEqualNP.Outside.L_meta_15773.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_32 : Interval s0Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_64 : Interval s0Atlas 2 64 2 := block_range (n:=2) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 66 := (concat bs0_2_0 (concat bs0_2_32 bs0_2_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_32 : Interval s0Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_64 : Interval s0Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_96 : Interval s0Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_128 : Interval s0Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_160 : Interval s0Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_192 : Interval s0Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_224 : Interval s0Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_256 : Interval s0Atlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_288 : Interval s0Atlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_320 : Interval s0Atlas 3 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_352 : Interval s0Atlas 3 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_384 : Interval s0Atlas 3 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_416 : Interval s0Atlas 3 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_448 : Interval s0Atlas 3 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_480 : Interval s0Atlas 3 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_512 : Interval s0Atlas 3 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_544 : Interval s0Atlas 3 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_576 : Interval s0Atlas 3 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_608 : Interval s0Atlas 3 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_640 : Interval s0Atlas 3 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_672 : Interval s0Atlas 3 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_704 : Interval s0Atlas 3 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_736 : Interval s0Atlas 3 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_768 : Interval s0Atlas 3 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_800 : Interval s0Atlas 3 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_832 : Interval s0Atlas 3 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_864 : Interval s0Atlas 3 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_896 : Interval s0Atlas 3 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_928 : Interval s0Atlas 3 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_960 : Interval s0Atlas 3 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_992 : Interval s0Atlas 3 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_1024 : Interval s0Atlas 3 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_1056 : Interval s0Atlas 3 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_1088 : Interval s0Atlas 3 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_1120 : Interval s0Atlas 3 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_1152 : Interval s0Atlas 3 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_1184 : Interval s0Atlas 3 1184 11 := block_range (n:=11) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1195 := (concat (concat (concat (concat (concat bs0_3_0 bs0_3_32) (concat bs0_3_64 bs0_3_96)) (concat (concat bs0_3_128 bs0_3_160) (concat bs0_3_192 (concat bs0_3_224 bs0_3_256)))) (concat (concat (concat bs0_3_288 bs0_3_320) (concat bs0_3_352 (concat bs0_3_384 bs0_3_416))) (concat (concat bs0_3_448 bs0_3_480) (concat bs0_3_512 (concat bs0_3_544 bs0_3_576))))) (concat (concat (concat (concat bs0_3_608 bs0_3_640) (concat bs0_3_672 bs0_3_704)) (concat (concat bs0_3_736 bs0_3_768) (concat bs0_3_800 (concat bs0_3_832 bs0_3_864)))) (concat (concat (concat bs0_3_896 bs0_3_928) (concat bs0_3_960 (concat bs0_3_992 bs0_3_1024))) (concat (concat bs0_3_1056 bs0_3_1088) (concat bs0_3_1120 (concat bs0_3_1152 bs0_3_1184))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_128 : Interval s0Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_160 : Interval s0Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_192 : Interval s0Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_224 : Interval s0Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_256 : Interval s0Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_288 : Interval s0Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_320 : Interval s0Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_352 : Interval s0Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_384 : Interval s0Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_416 : Interval s0Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_448 : Interval s0Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_480 : Interval s0Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_512 : Interval s0Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_544 : Interval s0Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_576 : Interval s0Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_608 : Interval s0Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_640 : Interval s0Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_672 : Interval s0Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_704 : Interval s0Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_736 : Interval s0Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_768 : Interval s0Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_800 : Interval s0Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_832 : Interval s0Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_864 : Interval s0Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_896 : Interval s0Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_928 : Interval s0Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_960 : Interval s0Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_992 : Interval s0Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1024 : Interval s0Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1056 : Interval s0Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1088 : Interval s0Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1120 : Interval s0Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1152 : Interval s0Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1184 : Interval s0Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1216 : Interval s0Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1248 : Interval s0Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1280 : Interval s0Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1312 : Interval s0Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1344 : Interval s0Atlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1376 : Interval s0Atlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1408 : Interval s0Atlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1440 : Interval s0Atlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1472 : Interval s0Atlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1504 : Interval s0Atlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1536 : Interval s0Atlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1568 : Interval s0Atlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1600 : Interval s0Atlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1632 : Interval s0Atlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1664 : Interval s0Atlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1696 : Interval s0Atlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1728 : Interval s0Atlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1760 : Interval s0Atlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1792 : Interval s0Atlas 4 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1824 : Interval s0Atlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1856 : Interval s0Atlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1888 : Interval s0Atlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1920 : Interval s0Atlas 4 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1952 : Interval s0Atlas 4 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1984 : Interval s0Atlas 4 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2016 : Interval s0Atlas 4 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2048 : Interval s0Atlas 4 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2080 : Interval s0Atlas 4 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2112 : Interval s0Atlas 4 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2144 : Interval s0Atlas 4 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2176 : Interval s0Atlas 4 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2208 : Interval s0Atlas 4 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2240 : Interval s0Atlas 4 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2272 : Interval s0Atlas 4 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2304 : Interval s0Atlas 4 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2336 : Interval s0Atlas 4 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2368 : Interval s0Atlas 4 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2400 : Interval s0Atlas 4 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2432 : Interval s0Atlas 4 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2464 : Interval s0Atlas 4 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2496 : Interval s0Atlas 4 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2528 : Interval s0Atlas 4 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2560 : Interval s0Atlas 4 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2592 : Interval s0Atlas 4 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_2624 : Interval s0Atlas 4 2624 23 := block_range (n:=23) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 2647 := (concat (concat (concat (concat (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 (concat bs0_4_96 bs0_4_128))) (concat (concat bs0_4_160 bs0_4_192) (concat bs0_4_224 (concat bs0_4_256 bs0_4_288)))) (concat (concat (concat bs0_4_320 bs0_4_352) (concat bs0_4_384 (concat bs0_4_416 bs0_4_448))) (concat (concat bs0_4_480 bs0_4_512) (concat bs0_4_544 (concat bs0_4_576 bs0_4_608))))) (concat (concat (concat (concat bs0_4_640 bs0_4_672) (concat bs0_4_704 (concat bs0_4_736 bs0_4_768))) (concat (concat bs0_4_800 bs0_4_832) (concat bs0_4_864 (concat bs0_4_896 bs0_4_928)))) (concat (concat (concat bs0_4_960 bs0_4_992) (concat bs0_4_1024 (concat bs0_4_1056 bs0_4_1088))) (concat (concat bs0_4_1120 (concat bs0_4_1152 bs0_4_1184)) (concat bs0_4_1216 (concat bs0_4_1248 bs0_4_1280)))))) (concat (concat (concat (concat (concat bs0_4_1312 bs0_4_1344) (concat bs0_4_1376 (concat bs0_4_1408 bs0_4_1440))) (concat (concat bs0_4_1472 bs0_4_1504) (concat bs0_4_1536 (concat bs0_4_1568 bs0_4_1600)))) (concat (concat (concat bs0_4_1632 bs0_4_1664) (concat bs0_4_1696 (concat bs0_4_1728 bs0_4_1760))) (concat (concat bs0_4_1792 (concat bs0_4_1824 bs0_4_1856)) (concat bs0_4_1888 (concat bs0_4_1920 bs0_4_1952))))) (concat (concat (concat (concat bs0_4_1984 bs0_4_2016) (concat bs0_4_2048 (concat bs0_4_2080 bs0_4_2112))) (concat (concat bs0_4_2144 bs0_4_2176) (concat bs0_4_2208 (concat bs0_4_2240 bs0_4_2272)))) (concat (concat (concat bs0_4_2304 bs0_4_2336) (concat bs0_4_2368 (concat bs0_4_2400 bs0_4_2432))) (concat (concat bs0_4_2464 (concat bs0_4_2496 bs0_4_2528)) (concat bs0_4_2560 (concat bs0_4_2592 bs0_4_2624)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_64 : Interval s0Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_96 : Interval s0Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_128 : Interval s0Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_160 : Interval s0Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_192 : Interval s0Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_224 : Interval s0Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_256 : Interval s0Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_288 : Interval s0Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_320 : Interval s0Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_352 : Interval s0Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_384 : Interval s0Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_416 : Interval s0Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_448 : Interval s0Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_480 : Interval s0Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_512 : Interval s0Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_544 : Interval s0Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_576 : Interval s0Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_608 : Interval s0Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_640 : Interval s0Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_672 : Interval s0Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_704 : Interval s0Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_736 : Interval s0Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_768 : Interval s0Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_800 : Interval s0Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_832 : Interval s0Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_864 : Interval s0Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_896 : Interval s0Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_928 : Interval s0Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_960 : Interval s0Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_992 : Interval s0Atlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_1024 : Interval s0Atlas 5 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_1056 : Interval s0Atlas 5 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_1088 : Interval s0Atlas 5 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_1120 : Interval s0Atlas 5 1120 20 := block_range (n:=20) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1140 := (concat (concat (concat (concat (concat bs0_5_0 bs0_5_32) (concat bs0_5_64 bs0_5_96)) (concat (concat bs0_5_128 bs0_5_160) (concat bs0_5_192 (concat bs0_5_224 bs0_5_256)))) (concat (concat (concat bs0_5_288 bs0_5_320) (concat bs0_5_352 bs0_5_384)) (concat (concat bs0_5_416 bs0_5_448) (concat bs0_5_480 (concat bs0_5_512 bs0_5_544))))) (concat (concat (concat (concat bs0_5_576 bs0_5_608) (concat bs0_5_640 bs0_5_672)) (concat (concat bs0_5_704 bs0_5_736) (concat bs0_5_768 (concat bs0_5_800 bs0_5_832)))) (concat (concat (concat bs0_5_864 bs0_5_896) (concat bs0_5_928 bs0_5_960)) (concat (concat bs0_5_992 bs0_5_1024) (concat bs0_5_1056 (concat bs0_5_1088 bs0_5_1120))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_32 : Interval s0Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 48 := (concat bs0_6_0 bs0_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_7_0 : Interval s0Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_7 : Interval s0Atlas 7 0 1 := bs0_7_0
theorem alls0 : ∀ k ≤ 7, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
  · exact alls0_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_11_0 : Interval s1Atlas 11 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_11 : Interval s1Atlas 11 0 1 := bs1_11_0
theorem alls1 : ∀ k ≤ 11, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_11 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
theorem alls2 : ∀ k ≤ 3, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 1 := bs3_3_0
theorem alls3 : ∀ k ≤ 3, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 1 := bs4_3_0
theorem alls4 : ∀ k ≤ 3, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 1 := bs5_3_0
theorem alls5 : ∀ k ≤ 3, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_11_0 : Interval gbAtlas 11 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_11_32 : Interval gbAtlas 11 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_11_64 : Interval gbAtlas 11 64 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_11 : Interval gbAtlas 11 0 78 := (concat bgb_11_0 (concat bgb_11_32 bgb_11_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_12_0 : Interval gbAtlas 12 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_12 : Interval gbAtlas 12 0 1 := bgb_12_0
theorem allgb : ∀ k ≤ 12, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allgb_11 i (by omega) hi
  · exact allgb_12 i (by omega) hi
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 28, 30),(inputs.getD 2 zero, 26, 30),(inputs.getD 3 zero, 22, 30),(inputs.getD 4 zero, 14, 30),(inputs.getD 5 zero, 14, 46)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 12 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 56, 58),(inputs.getD 3 zero, 50, 58),(inputs.getD 4 zero, 42, 58),(inputs.getD 5 zero, 26, 58)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 52, 54),(inputs.getD 2 zero, 50, 54),(inputs.getD 4 zero, 38, 54),(inputs.getD 5 zero, 22, 54)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 4 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 44, 46),(inputs.getD 2 zero, 42, 46),(inputs.getD 3 zero, 38, 46),(inputs.getD 5 zero, 14, 46)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 4 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 28, 30),(inputs.getD 2 zero, 26, 30),(inputs.getD 3 zero, 22, 30),(inputs.getD 4 zero, 14, 30)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 13 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 28, 30),(inputs.getD 2 zero, 26, 30),(inputs.getD 3 zero, 22, 30),(inputs.getD 4 zero, 14, 30),(inputs.getD 5 zero, 14, 46)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeaaaeaaaaaaaeeeaeaaaeaaaaaaaeeeaeaaaeaaaaaaaeeeaeaaaeaaaaaaaeeeaeaaaeaaaaaaaeeeaeaaaeaaaaaaaeeeaeaaaeaaaaaaaeeeaeaaaeaaaaaaa
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 13 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 62 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) (SBf 4) :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have s5 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 5 zero)) (SBf 5) :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have allCuts : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val) := by
    intro v
    fin_cases v
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
  have low := boundgb certgb allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372906 * 2 ^ 32 + 3937053354) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sample6 (r : Row) (i : Fin 6) := bit r (fullRoots.getD i.val zero)
theorem table6 : ∀ r, posted (sample6 r) = bit r fullWord := by decide +kernel
theorem raw6 : List.ofFn (fun i : Fin 6 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval6 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample6 r) = fullRoots.map (bit r) := by rw [←raw6,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample6 r)).trans (table6 r)
theorem binaryLower (low : Lower true fullRoots fullWord 13)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 13 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_15773.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.and,[3,6]⟩,⟨.and,[4,6]⟩,⟨.and,[1,2]⟩,⟨.and,[2,7]⟩,⟨.and,[1,3]⟩,⟨.and,[5,8]⟩,⟨.or,[0,12]⟩,⟨.or,[0,11]⟩,⟨.and,[9,12]⟩,⟨.and,[8,15]⟩,⟨.or,[10,13]⟩,⟨.and,[14,17]⟩,⟨.or,[16,18]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,19⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 13) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3937053354) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3937053354) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨⟨gs, o⟩, legal, hsize, correct⟩ := hs
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨⟨gs, o⟩, ?_, hsize, correct⟩
    intro g hg
    obtain ⟨op, len⟩ := legal g hg
    refine ⟨?_, len⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    exact op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg)))
  · push Not at clean
    obtain ⟨a, ha, hop⟩ := clean
    have lo := binaryLower low gs o legal (fun x => correct x)
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot, hop] at e
    refine ⟨⟨mono, 19⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 14 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_15773

open PEqualNP.Outside.L_meta_15773 in
theorem PEqualNP.Outside.L_meta_15773 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3937053354) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3937053354) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
