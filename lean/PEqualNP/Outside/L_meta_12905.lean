import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12905.Model
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


end PEqualNP.Outside.L_meta_12905.Model

namespace PEqualNP.Outside.L_meta_12905
open PEqualNP.Outside.L_meta_12905.Model
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

def SB : Nat := 7

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d SB k cs.length pool ws)

def mirrorSteps : List Move := [swapRows 33]

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
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) SB

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

end PEqualNP.Outside.L_meta_12905

namespace PEqualNP.Outside.L_meta_12905
open PEqualNP.Outside.L_meta_12905.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x60001dc0e49c0000862023a2003276a7c0404a6e08c4ab9740303ac04a2149ad61a78558800e080041040210223ff43fe43fd43fc43ff41fe41fd41fc41ff31fe31fd31fc31fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x86175510c3f8a2187fd0430ff20861fd410c3f882187fcc430ff18861fd310c3f862187f88430fe90861fc210c2fca0187fd0030ff20061fd400c3f880187fcc030ef98061fe300c3f460187f4c030ee98061f9300c3fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5887f94b10bf29621fd52c42faa5887f14b10be29621ff42c43fc85887f50b10fe21621ff32c43fc65887f4cb10fe19621ff41c43fc83887d90710fea0e21f541c43f883887fcc710ff18e21f631c43fa63887d4c710fe18e21ff21c43fc43887d88710fe90e21f521c43f843887fd0310ff20621fd40c43f881887fcc310ff18621fd30c43f861887fc8310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5087fd0a10ff21421fd42843f885087fcca10ff19421fd32843f865085f54610ffa0c21f741843fc83087f50610fe20c21f441843fe63087f8c610fe98c21fc31843fe43087f88610fe90c21fc21842fca1087fd0210ff20421fd40843f881087fcc210ff18421fd30843f861087fc8210ff10421ff10843ee21087ec4210ffaa2217f54443fca8885f95110feaa2217d54443f8a8885f15110ffa9a217f53443fca6885f94d10fea9a217d53443f8a6885f14d10ffa1a21fe43443fa86887f10d10ffa92217f52443fca4885f94910fea92217d52443f8a4885f14910ffa1221fe42443fa84887f10910ff99221fe32443fa64887f0c910ffa0a21fe41443ec82887f50510faa0a21fc41443fe62887f8c510fb18a21fd31443ea62887f0c510ff90a21fe21443ec42887f48510fa90a21fc21443fe80887f90110fea0221fc40443fe60887f8c110fe98221fc30443fe40887f88110fe90221ff10443f620887f84110fb08221ff54042fea8087f95010bf2a021be540427ca8087f55010beaa021bd540427aa8087f15010be2a021ff53042fea6087f94c10bf29821de53042bca6087f54c10bea9821dd53042baa6087f14c10be29821ff43043fc86087f50c10fe21821ff52042fea4087f94810bf29021ee52042dca4087f54810bea9021ed52042daa4087f14810be29021ff42043fc84087f50810fe21021ff32043fc64087f4c810fe190217e51043fe82087dd0410ff20821fd41043f882087d10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xd21087ea4210f948421ffa8043fe50086fca010ff54021bea8043fc50087fea7a07f94f40bf29e81fd53d02faa7a07f14f40ffa1e81bf43d03fc87a07f50f40dea1e81fc43d03fea3a07f94740bf28e81fd51d02faa3a07f14740ffa0e81bf41d03fc83a07f50740dea0e81fc41d03fe63a07f8c740fe98e81fc31d03fc43a07f48740fe10e817d54903fea7207f94e40bf29c81fd53902faa7207f14e40ffa1c81fe43903fa87207f10e40ffa8c81fe51902fca3207f54640bea8c81fc51903fe83207f90640fea0c81fc41903fe63207f8c640fe98c81fc31903fc43207f48640fe10c817e50903fe81206fd0240fda0481ff53502fea6a077d4d40afa9a81fe53503faa6a07f14d40be29a81dc53502b8a6a07fd0d40dfa1a81fe43503fa86a06f50d40fe21a81ff51502fea2a07dd4540bba8a81fe51503faa2a07f14540be28a81f451502e8a2a07fd0540dfa0a81fe41503fa82a06f50540fe20a81ff31503fc62a07f4c540fe18a81fe21503fa42a07f08540ffa0281fb40503fc80a06f90140bf2a081ff53103fca6205f94c40ef298815e53103faa6205f54c40eea98815d53103f8a6207fd0c40ff21881fd43103f886207fd4440ff288817e51103eca2205d94440fea88817d51103eaa2205d54440fe28881ff41103fc82207f50440fe20881ff31103fc62207f4c440fe18881fe21103fa42207f08440bf28081ff401037e80207f90040fd20081fd401037a80207e50040ffaa6617f54cc3fca9985f95330feaa6617d54cc3f8a9985f15330ffa1e61fe43cc3bc87987f50f30eea1e61fc43cc3fea3987f94730bf28e61fd51cc2faa3987f14730ffa0e61fe41cc3fa83987f10730ff98e61df31cc3fc63987f4c730ee98e61fc31cc3fc43987f48730fe10e61ff40cc3fc81987f50330fe20661ff548c2fea9187f95230bf2a461fd548c2faa9187f15230be2a4617d538c3fe871877d0e30ff21c61fd438c3f887187710e30ffa8c61fe518c2fca3187f54630bea8c61fc518c3fe83187f90630fea0c61fc418c3fe63187f8c630fe98c61fc318c3fc43187f48630fe10c617e508c3fe81187f90230fea0461fc408c3fe611877cc230fd98461ff544c2fea8987f95130bf2a261fd544c2faa8987f15130be2a261ff434c3fc86987790d30fea1a61dd434c3f886987fd4530bfa8a61fe514c3faa2987f14530be28a61ff414c3fc82987f50530fe20a61ff314c3be62987f8c530fe98a61dd314c3f862987f88530fe90a61fc214c3fe80987f90130fea0261fc404c3fe60987ecc130ff18261de304c3fea8185fd5030ff2a0617e540c37ca8184f95030feaa0617d540c37aa8184f55030fe2a0617c540c2fca6187fd0c30efa1861fe430c3fa86187f10c30ee21861ff510c3fca2185f94430fb2886176510c3faa2185f54430faa8
  | 2 => 0x7fea020ff94041bf28083fd50106faa020ff14041ffaa6637f54cc7fca998df95331feaa6637d54cc7f8a998df15331ffa1e63df43cc7fc8798ff50f31fe21e63dc43cc7fea598ff94b31bf29663fd52cc6faa598ff14b31ffa1663fe42cc7fa8598ff10b31ff99663df32cc7fe8398ff90731fea0e63fc41cc7fea198ff94331bf28663fd50cc6faa198ff14331ffaa4637f548c7fca918df95231feaa4637d548c7f8a918df15231bea9c63ff438c7fc8718ff50e31fe21c63ff528c7fca518df94a31fea94637d528c7f8a518ffd0a31ff21463fd428c7f88518ffcca31ff194637e518c7fe8318fdd0631ff20c63fd418c7f88318fd10631ff98c63df318c7ee6318ffd4231ff284637e508c7faa118df54231fe28463ff544c6fea898ff95131bf2a263fd544c6faa898ff15131be2a263ff434c7be8698ff90d31fea1a63fc434c7b88698ffd4931bfa9263fe524c7faa498ff14931be29263ff424c7fc8498ff50931fe21263ff324c7be6498ff8c931fe99263dd324c7fe8298fdd0531ff20a63fd414c7f88298fd10531ff98a63f7314c7fc6298f78c531ffa82637f504c7fca098ff54131fe282637c504c7fea818dfd5031ff2a0637e540c7faa818df55031fe2a0637c540c6fca618ffd0c31ff21863fd430c7f88618ffd4831ff290637e520c7dca418db94831fea90637d520c7daa418db54831fe29063ff420c7fc8418ff50831fe21063ff320c7fc6418ff4c831fe190637e510c7fe8218ff90431fea0863fc410c7fe6218f7cc431ff18863f6310c7fa6218f74c431fa98863d5310c7fea018ff94031bf28063fd500c6faa018ff14031ffaa4437f54887fca910df95221feaa4437d54887f8a910df15221ffa9c437f53887fca710df94e21fea9c437d53887f8a710df14e21ffa1c43fe43887fa8710ff10e21bea9443ff42887fc8510ff50a21fe21443ff32887fc6510ff4ca21fe194437e51887fe8310fdd0621ff20c43fd41887f88310fd10621ff98c43fe31887ec6310ff4c621fa98c43fc31887fe4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fea690dfd4d21ff29a437e53487faa690df54d21fe29a437c53487fe8690ff90d21fea1a43fc43487fe8290fdd0521ff20a43fd41487f88290fd10521ff98a43fe31487ec6290ff4c521fa98a43fc31487fc4290fb88521ffa82437f50487fca090ff54121fe282437c50487fea810dfd5021ff2a0437e54087faa810df55021fe2a0437c54087fea610dfd4c21ff298437e53087bca610d794c21fea98437d53087baa610d754c21fe298437c53087fe8610ff90c21fea1843fc43086fca210ffd0421ff20843fd41087f88210ffcc421ff18843fd31087f86210ff88421fb10843f
  | 3 => 0x800000800400800400400801001803800c00000000402000000000000400000400001401401400400401000000000000000800000800c00000800000400400000000000400003001801800c00800403c02400002800400c00401800c00c00800000400000001000400000000400400800000000000402000000000400800000c00001000000400800000000007c00001401400400000c00000000000001003000800000800400400001800400800002400400400800400c00c00000c00000400400001400000001400002c00000400000801000800400800000000400400400003c00000400000000000000001000800400000000c02800000400000400401000c00002400000000400401c00001800407c00000000000800400800400001000001400402800800000803c00000c00c00000001801800401000005400c00002400000001400801000000000000400c01000400000000000400400000800800000400800400800001000001400800000000001401801400800000c01000000002000400400ffea3a1ff94743bf28e87fd51d0efaa3a1ff14743ffa8687fe50d0efca1a1ff54343bea8687fc50d0efaa921df94e43ffa1c87bf4390fbe8721ffd4643ff28c877e5190feca321dd94643fea8c877d5190feaa321dd54643fe28c87ff5090ffca121df94243fea84877d5090ff8a121ffd0d43efa1a87fe4350f7c86a1ffd4543bfa8a87fe5150ffaa2a1ff14543be28a87ff5050efea0a1ff94143fea8287fc5050ef8a0a1df95043bf29887ff4310f7e8621ff90c43ef21887fd4310f7a8621f750c43ffa8887fe5110efca221ff54443bea8887fc5110ffea021ff94043bf28087fd5010efaa021ff14043ffa9e83fe53d06fca7a0ff54f41bea9e83fc53d07fe87a0ff90f41fea1e83fc43d07fea5a0ff94b41bf29683fd52d06faa5a0ff14b41ffa1683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9c83fe53906fca720f794e41af29c83fd53906faa720f754e41aea9c83fc53907fe8720ff90e41fea1c83fc43907fea520ff94a41bf29483ee52906dca520ff54a41bea9483ed52906daa520ff14a41ffa1483fe42906fca320ffd0641dfa0c83f741907fea120ff94241bf28483fd50906faa120ff14241ffa9a837f53507fca6a0ff54d41fe29a837c53507fe86a0ff90d41fea1a83fc43507fea4a0dfd4941ff29283fd52507f8a4a0df14941ffa1283fe42507fa84a0ffd0541fba0a83fe415077c82a0ffd4141bfa8283fe50507faa0a0ff14141be282837e54107fea620ff94c41bf29883fd53106faa620ff14c41ffa1883fe43107fa8620ff10c41ffa9083fe52106fca420ff54841bea9083fc52107fe8420ff90841fea1083fc42106fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f5411
  | 4 => 0xef00015e9a40561319150000000408ca000000000000206d6199590e80008d8000000000ee97b5e38001b680011800008080000000000010f5e09108aed1b80005204e9b81bfce894a58889112821ac0000000000e00002ba11d398000000000000000000000a280000000019880022080000000000000000000000000006b8001dc80004480000000004284f0a900ac000000d55940b052e0e540000000000000000000015c12584209ac0017f8000000001430000000000cb8000000ed84b00000000000019b8000000c58001c00390000c50248000cf80005e0ace1d0000481344cd00013c0000500c800000000014c9980250dc8001db15013345d1c30f280000000000000000000000000000000019000000000000000000000000000000000003380000000000000000000000004c0000000000d340000000000000000013310881c5e61400000581d98000000838c3c00098c0010900000005c19e932400043c1bd8e84e4515c0a18a195695e10c780000010f8002178e786ec6f191800000000000000000000014dc38000000c05b000000000000000000000000000021421180000000017099ac0000021040010d000115549c8900000000000000000000000005ae0b0000000000000000000000078f98000000738001f68600000000000001008000000c28000000279f0800196000031dae9d88000c14bc0538e640003700014a02c92f00018c00000009b80000000000000012440000000000021c8e500000013a000000151965c0009900000005a0001aa0b30000000000280000000000000000e70e5c000000000000000001ae5cf8000000000010000000000000000000001024000001efc000000000000ea8000000000000af80000000000000000000000016a03a82c45bc315ef400000002400000000000400000000800400000000000400000000c00000000800000401000001004000400000000400000c02002800c03400c00400400000000401c00800000401800002000400c00c00400000001000801000000800000400000000000800005400401400801400402c00000000800402401c01000400400000c01801400000c00000c00001400000001c01400800400c00401800400000400c00000801800400000000403c01000c00000400000400401000000000000400400400400000800000801c00400400000001400000800400000801001001000000000800400400c00402800001000400400001000800000c00002000c00000000000000000400c00000802400800000000000000800800000400c01800002800400800400c00400800000000400000000401800000400400400400802400400000000000400400400000c00000000401000000401400800c00400400400000000000c00000400401c00
  | 5 => 0x18d933c1e0121f98d582e512d348001bedc5822822d4212d826850c000001a76010410001dbcce80b0000d44000e118280000002306e800111cc719f0270000899850000f180000005900010181196040d8000ea0530000000000000e9d600c68000000000000000000000000000000000000000001da0000000001f91914001b9d118c21f115a9690000e59a89cbc0000000000021982c110c001b30000000000001a095f80000000015b80000014c000222c000000b982f80002b000000000018874000179567141a1a4000000000000000001ce0bec0001794740000000001920e01f80000020c80021380000020380000014440000000001800000000000000016985f8200001cd80000000000012fc000000340000001c717180000000000000000004980000000022212b89f14a80010e1b098c80007a4000000435678000000eac00000000148d02c0000000000021f8e680000000009a06441dc0000000000000007f8000001ad8eb4002130fdc084000000000054000000000000458de0000000000000ffc0000c9ac4fc4e320a00008e800000000000114ceb80000000000000000015580000000017c9abc3dcc11f000006dd8f8000c9800000063c0000000010b9f50305e6989011e071a7ca00fc1481061aa8a70360000828001fd9e286915a2180000000908209d0d131860000000000001168000680000001d05784001fd18b9ba96540000000680000009980002103080002d1161c20000000001560000000000000e95e80000000000000001820000cd8001120bfce847e9cc4000000000001e180000000000012890a80014380000000000000000000000000002d8be8000f48864000000000c30c34000000e016346708480003f0000c48000994000bf4c080000000010edfc8cc8fd513a07412ce80b007c800107950886122c000889bb0e740007e03d845618dfa0000002124001c2a1680002e9d319380000000000000013b921405c001c883c80944d800000000053515c000000001d10001a9851198c4611fcf808244d0000000709d297a9ad00000002980000000000000002a9a6e24400000006400000000217c0000000000020b83800000000000000000021b14104a80000003b8975f488a2159279bf00000001c89e11f8000000002078551308e480000000010405e8000000001840000002068000001ca01287d4001cf0000fe8000001cb19840011100740006fc000ec0000000000000000000b500017e0001b48000000000000001d51ce8000000001650000000000002148001898000e380000013e800000160981c470000108000a19be8ec5a78000000088bf80022400008b86a9fec138001581a649700002f4000320144db8001458b24001934000001ea000000000120de0c0000000010fc00210e12000095c
  | 6 => 0x11d4abd9a892c0011ea2380009400020080009e8000001e7944c57042415000007c1e8001ab17d0000b195394f9550000aa0000071568001298001d79429c817287c41f1ba0140f403d4000000000aadb84000ad04fe02a091710000000000000000bb8d24000000001f61b406d9e40000001ef9528000001949f780000000016304a0000000000f00710000000d080000000000000f0000000000000001ef1b99620d1400000013207d880044000000d39570cb00000000000007f000192400164db88bf00018693c90b1d5a0992f8000000000000000000000000000000000001f300000000000000000000000015d16440000018f161071d488d7a05c000000001f400018a962d7a40021909f8439b58000000000000000001080000001b788680000003e800000000163a2252700000000000009b49a940896c0000000000011d8000000e8c0009300000000a8000000000001c98002110001190000000d7d6f80000000000000004000000000003c4000001660002170000000000780001464000ab8000634000000c00001099050000e40000000508000000a30821f58001d08001134f39468001448fad0108a800081ca080000000000000000007a80000008d0000bc94546081d54780003d0001d008140400000019304a4288ff19b21e9068441d400020f0000d20000e99669818001c900005e47cc001920290000d6851e1e01c0158000464790fe0de93a8000a597887b8310c55d38641ee01b8f682a14d0fbc6f9290161ca800184833c000001c0597c000000000000000000000001a000018d161c000001f280f80003bc000000000001975229649911c68c2c00099d7e9f38001768ba8001ec2054000001e509d981523534dbe192d7990f0c1c0016400000000008a4000b14ff95300014f087000000000000000180ced00b8000001bd95d86100000000000000000016a40000000000000017adac8000c19b60000000001b20000000b106b4001f88001a58001520000b0c87400004c000c0c0a4000660f200000000000000016d5f0c0000000015892689800009d0000001b112d000146000000000097c000028000000000000b791e400161493c00000000000065a1840000000000007bdbc9a48000ee4638000edc0020d2230001371368000b49102160000001a68000000000000000000000000000ac4001e88000000000002040000d88721218000960000000000000000000be00000510c80000e80000011f48508f9ed894c3adbf40018660e9fe4001388002150db00000000000019be02000000191d6e8000000000529e04978b58000000af1978001158d2c0000012ec000001cd00020a8000a800015c8adc000001a20000000735e48001970001eb8001c600001d93f0000000000a407b53d08c983579db29b511480005d9e
  | 7 => 0x19cfd89550a00000000019a00005a9a312a0568001321a60f605f00016da0d9f22201eb0af40000000002fcf703f82ccc400014e8000a69700001de99900018a0000ef8d6462d800d74ae4001200b21680951249b7000104806d0700011ec000000818944000000e6c000000000000624000000000000001f70000000001038000000000984810d5c3a45de1f1d70000000ae0001870000000000000000468000fd0788ec8d4c000000ad5584000000000000000000388001810404e90000c880000000000019e0ab0001689471b14e20430000000000e7c0000018080000000017f0000000ecddb8001e200000003b0000d4a100f94000001929760731da9014001000000d3c0011c0000000918ed46840008780000012c0000000001d80000000000000000d18000000000000001540001d4957923d188000000001ec9310398000000a99c50a500003b58e0559b8c3000015fc0000000000000003c0000000000001210478001ae00010c0000000000000d81ac0000a38000000b88001c48c25ea80001cdbb8000001f1830c0000002d400196c00000028d9080000000000000014adaba1bcd00000ba0000001d60000000000001fc000124c0012600014949c86980005cda38000000018000b684f8fb8bd87686f42dd2508308b06c1bd0688d849c025a060000c5cdf00021d92e80000000000013b00000002600009b015520a0508591b0958b38001af0001ad549011000008c0017b804960c00147c000000f11bc0000e08000b280000800017500000302ed23079c00000023c000000000008000000000000000000000000ae9fdc0011ccca8fa467a1089241687a1878000da1fe9a5000122000000000117854c1ac4b9dfdfd4b4049146dd1d6f0d90a60d70d8c000f900000c07507283cc5c40021a80020f9df4488329e99f054e0aa5b18f9c000d50fb000079a0301707612240000000016e1780001021db4000000000dd1df9f800000000013e0000001be4450da80009880000000000000000017300015912a9df00000000000013600000000006a0001bdcd0da294847ad01d7786300017480016c0001d90000000000000000000000000e19859969b945b8ea400000131de9d144000000000000fed7700011251f0704948b806ce23c0011a00000000000000000022100000000003240d0000001625d20000000000001de13900020000002f2128000f58000598bd102a064000002058eb1340ad99054b90d8518e286d40016c932c0021c40905c8000059830000000000c600000022480000000014b00006b16640015b00001a80019d978d1dcc9190ddd09352380010354d8c4c969498b61a187701b0061059b39cc8d6c5b40000019f8834000d408006e5fb11c8fa1dd8748000920000494001cb834800042c000000000a4800100400
  | 8 => 0xb90d980000000000019c8fa9af99c11a9140758000000ff5fba1b9e58218359e90330000000000629599358c3813c001acc4180005240004ec0017c00003a0220369030f787022188f18b06200012b13500006ca048000000000000000b70000000000000000001738000000588649e700013381980000016a84f40012ca1b4000038cc0a78000001fe0000001d181a117082d6b06d1c79bd40000011d1d15a84001740000000651998929eea088001a90000d60001951e31104f080000013045480000020c100c001838000000dfa0fc0000000000000003e224c5040bc000fe4ce00000000001d07d00006186e0000aa8000000000000e60ebc000000000134fcc0000000007c0001dc00016b9ccd128714000000001995380c44000000000000000000b1c0011140000000006695480004c80005d40000000017b0000000001658000000a10f50000d10000000fc8778001cc0000fb4000b080017a18243788417d9bf87b11e00021a1a1000000000093800000113cbb0350000000000000002114000ee000000000137800088000119800145c0000007d800000070c4e0dd8578001328ab4000900149758ac1790000000000000000001d69c10001440000000000000000000000000000000000000000000002228098f322355f1510001720dc19d0ac80000221c0001ff8afca20674a8853e0808c1c40100d1c0000a02e1241628001a80000000f88000000000718d296d0000000000000000000319a71b900000000000000005b0001314239fa8002018124001ed09a53f8001ff121d3d8d3000130c9640000008e15e0cf0240000541c35301c18000000000001451204002
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe500427d63940109f98a500427d62940109f58650043774194010dd106500427d65d0010cf953400433d54d0010d794f400435d53d0010db94b400436d52d0010edd07400427f65900109f596400433e5490010cf552400435e5390010d754e400436e5290010db54a40042f66190010bd586400427f6550010cf951400433d5450010b7d8d40042dc6350010d794d400435d5350010bbd8940042ec6250010db949400436d5250010bdd8540042f46150010edd05400427f65100109f994400427d65100109f194400433e5410010cf55040042de6310010b758c400435e5310010d754c40042ee6210010bb588400436e5210010db54840042f66110010bd584400427d65cc010cf953300433d54cc010d794f300435d53cc010db94b300436d52cc0109fd96300427d658c010cf952300433d548c010d794e300435d538c010db94a300436d528c010bd98630042f5618c0109fd95300433e544c010cf551300435e534c010d754d300436e524c010db549300427f650c0109f994300427d650c0109f19430042be640c010af590300433e540c010cf550300435e530c010d754c30042ee620c010bb588300436e520c010db54830042f6610c010bd584300427d65c8010cf953200433d54c8010d794f200435d53c8010db94b200436d52c80109fd96200427d6588010cf952200433d5488010d794e200435d5388010db94a200436d5288010bd98620042f561880109fd95200433e5448010cf551200435e5348010d754d200436e5248010db549200427e65080109f594200427c6508010cf950200433d5408010d794c200435d5308010bd98420042f56108010cf953100433d54c4010d794f100435d53c4010db94b100436d52c4010dd59710042f664c4010bd193100437754c4010ed953100437554c4010ed553100433554c4010ddd4f10043d653c4010dd54f10043d553c4010d554f100437752c4010f994b100437552c4010f954b100436552c4010cf952100433d5484010d794e100435d5384010db94a100436d5284010bd58610043765184010be596100437965840109e59610043ba5484010ee55210043da5384010f654e10043ea5284010fa54a10042f96184010de94610043f25184010fcd0610043f041840109fd95100433e5444010cf551100435e5344010d754d100436e5244010db54910042f76544010ddd9510042776544010bd99110042f46444010ddd5110043b65444010dd55110043b55444010cd55110043775344010f594d10043755344010f554d10043555344010ddd4910043e65244010dd54910043e55244010d954910042f76044010dd94110042fb6544010ded95100427b6544010ee95110043b95444010f694d10043d95344010fa94910043e95244010bed8510043f36144010de94510043f25144010
  | 1 => 0x435d5310810db948420436d52108109fd97320427e65cc8109f597320427c65cc810cf953320433d54cc810d794f320435d53cc810db94b320436d52cc8109fd96320427e658c8109f596320427c658c810cf952320433d548c810d794e320435d538c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810cf951320433d544c810d794d320435d534c810db949320436d524c810bdd8532042f4614c8109fd94320427e650c8109f594320427c650c810cf950320433d540c810d794c320435d530c810db948320436d520c810f34c832042f6610c810bd584320427e64944109f592510427e63944109f58e510427d62944109f597410433e54d0410cf553410435e53d0410d754f410436e52d0410db54b41042f565d0410dd597410427565d0410ddd5341043b654d0410dd55341043b554d0410cd553410437753d0410f594f410437553d0410f554f410435553d0410ddd4b41043e652d0410dd54b41043e552d0410d954b41042f560d04109fd96410427d6590410cf952410433d5490410b798e41042dd6390410d794e410435d5390410bb98a41042ed6290410db94a410436d5290410bd98641043765190410be98241042f960904109fd95410433e5450410cf551410435e5350410d754d410436e5250410db549410437651504109fd94410427d6510410cf950410433d5410410d794c410435d5310410db948410436d5210410be98041042f96010410dd59441042756510410bd99041043b66410410ddd5041043b65410410dd55041043b55410410cd55041043775310410f594c41043755310410f554c41043555310410ddd4841043e65210410dd54841043e55210410d954841043f26010410bd58041043f160104109f597310433e54cc410cf553310435e53cc410d754f310436e52cc410db54b310427f658c4109f596310433e548c410cf552310435e538c410d754e310436e528c410db54a3104376518c410be98231042f9608c4109fd95310433e544c410cf551310435e534c410d754d310436e524c410db5493104376514c4109fd94310427d650c410cf950310433d540c410d794c310435d530c410bb98831042ed620c410db948310436d520c410f54c431042fa600c410be580310427d65c8410cf953210433d54c8410d794f210435d53c8410db94b210436d52c84109fd96210427d6588410cf952210433d5488410d794e210435d5388410db94a210436d5288410dd94621042fa6088410be582210427f6548410cf951210433d5448410d794d210435d5348410db949210436d5248410dd945210427f65084109f594210433e5408410cf55021042de6308410b758c210435e5308410d754c210436e5208410db54821043e52108410be98021042f960084109f992500427d64940109f98
  | 2 => 0x65d0c109f197430433e54d0c10cf553430435e53d0c10d754f430427f6590c109f996430427d6590c109f196430433e5490c10cf552430435e5390c10d754e43042ee6290c10bb58a43042f66190c10bd586430427f6550c109f995430427d6550c109f195430433e5450c10cf551430435e5350c10d754d43042f76150c10bd185430427f6510c109f994430427d6510c109f194430433e5410c10cf550430435e5310c10d754c43042be64d4810af593520433e54d4810cf55352042de63d4810b758f520435e53d4810d754f520427e64d4810cf993520423e64d48109f593520433d64d48108f593520427e63d4810d798f520425e63d48109f58f520435d63d48109758f520437661d4810de983520427d6594810cf952520433d5494810d794e520435d5394810dbd4a520427e64948109f592520427e63948109f58e520426d6594810dbd52520436e5494810eb952520432e5494810db55252043ad5494810cb552520436c5494810dbd4e520436e5394810f394e520434e5394810db54e52043cd5394810d354e520436c5394810dbd92520436e6494810db592520436c6494810dbd8e520436e6394810db58e520436c6394810dbd0e520436e4394810db50e520436c4394810db986520436c6194810db982520436c6094810cf951520433d5454810d794d520435d53548109fd91520427c64548109fd8d520427c6354810dbd89520427f61548109f585520436f6554810dbd51520436e5454810eb951520432e5454810db55152043ad5454810cb551520436c5454810dbd4d520436e5354810f394d520434e5354810db54d52043cd5354810d354d520436c5354810dbd91520436e6454810db591520436c6454810dbd8d520436e6354810db58d520436c6354810dbd0d520436e4354810db50d520436c4354810db985520436c6154810db981520436c6054810db04152042be6414810af590520433e5414810cf55052042de6314810b758c520435e5314810d754c52042ee6214810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6114810dd984520427661148109f980520437a60148109fd97420427e65d08109f597420427c65d0810cf953420433d54d0810d794f420435d53d0810db94b420436d52d08109fd96420427e65908109f596420427c6590810cf952420433d5490810b798e42042dd6390810d794e420435d5390810db94a420436d5290810bd98642042f561908109fd95420427e65508109f595420427c6550810cf951420433d5450810d794d420435d5350810db949420436d5250810bdd8542042f461508109fd94420427e65108109f594420427c6510810cf950420433d5410810d794c420
  | 3 => 0x110bdd9210442f56484110dd95210443745484110bdd8e10442f56384110bdd8a10442f56284110fcd4210442de63d5010b758f54042ee62d5010bb58b540427e63d5010d798f540425e63d50109f58f540435d63d50109758f540427e62d5010db98b540426e62d50109f58b540436d62d50109b58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540427e63950109f58e540427e62950109f58a540423d6595010ed186540433f6395010cf98e540433d6395010cf18e540433f6295010cf98a540433d6295010cf18a540433e6195010cf186540433e6095010cf182540433f64550109fd8d540427c63550109fd89540427c62550109fd85540427d6155010dd185540427f60550109f581540433f6555010ed185540433f6355010cf98d540433d6355010cf18d540433f6255010cf989540433d6255010cf189540433e6155010cf18554043346155010cf981540433c6055010cf04154042be6415010cf55054042de6315010b758c54042ee6215010bb588540427e6415010cf990540423e64150109f98c540435e63150109798c540427d6315010d758c540425d63150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109d984540427e6015010de98054042be64d4c10af593530433e54d4c10cf55353042ee62d4c10bb58b530427e64d4c10cf993530423e64d4c109f593530433d64d4c108f593530427e62d4c10db98b530426e62d4c109f58b530436d62d4c109b58b530427e61d4c10dd987530427e60d4c10de983530427d6594c10cf952530433d5494c10d7d4e530427e6494c109f592530427e6294c109f58a530425d6594c10d7d52530435e5494c10e7952530431e5494c10d7552530439d5494c10c7552530435c5494c10d7d92530435e6494c10d7592530435c6494c10d7d8a530435e6294c10d758a530435c6294c10d7986530435c6194c10d7982530435c6094c10cf951530433d5454c109fd91530427c6454c10d7d8d530427f6254c109f189530427f6154c109f585530427f6054c109f581530435f6554c10d7d51530435e5454c10e7951530431e5454c10d7551530439d5454c10c7551530435c5454c10d7d91530435e6454c10d7591530435c6454c10d7d89530435e6254c10d7589530435c6254c10d7985530435c6154c10d7981530435c6054c10d704153042be6414c10af590530433e5414c10cf55053042de6314c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530425e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109d984530427e6014c10de980530427f65d0c109f997430427d
  | 4 => 0x714c324436f520c910db14832443cd320c910bd98432442f5610c9109f997414433f54d0510cf15341442fa60d0510be583414427e6590510b798e41442dd6390510bb98a41442ed6290510bd996414437665905109d99641442f56490510dd95241443745490510f598e41442f56390510f558e41442d56390510f998a41442f56290510f958a41442e56290510bd982414427c6550510cfd51414433c5450510bed8141442f86050510dd19541442746550510edd9141443b75450510dd95141443745450510ed15141442f76350510bdd8941443f36050510bd18141443f060505109f99441442f66110510ed504414427e65cc510d7d4f314435c53cc510be98331442f960cc5109f99631442f6658c510dd99631442f7648c510bd5923144376548c510dd15231442f5638c510dd94e3144374538c510bd58a3144377528c510dd54a31442f6608c5109f195314435f534c510d714d31442fb604c510be1813144374654c5109d19531442f7644c510bd5913144376544c510dd15131443d7634c510f5d4d3144376534c510dd14d31443d4534c510d514d31443d7434c510f510d31442f7624c510ddd493144375524c510f5cc931443d5324c510fcd8131442f4604c510fc181314427e650c510bb98831442ed620c510bd98431443d5310c510dbd4b214436c52c8510be98321442f960c85109f99621442f66588510dd99621442f76488510bd59221443765488510dd15221442f76388510bd58e21443775388510dd54e21442f56288510dd94a21443745288510bd982214436f5248510db14921442fb6048510be18121442f76448510bd59121443765448510dd15121442f76348510bd58d21443775348510dd54d21443e76248510f9d4921443765248510dd14921443e45248510d914921443e74248510f910921443e63248510f94c921443f36048510bd18121443f060485109f99421442de6308510b758c21442f66108510f9484214427e65d0110cfd53404433c54d0110bd98740442f561d0110ed507404427e65901109fd95404427d65501109f195404433f5450110cf15140442df6350110b718d40442ef6250110bb18940442f76150110bd18540443b541501109f99440442de6310110b758c40442ee6210110bb58840442f66110110bd584404427e65cc110d7d4f304435c53cc110bd98730442f561cc110f54c7304427e658c1109fd95304427d654c1109f195304435f534c110d714d30442f7614c110bd18530443d5314c1109f99430442be640c110af59030442ee620c110bb58830442f6610c110bd584304427e65c8110dbd4b204436c52c8110bd98720442f561c8110f9487204427d65481109f19520442f76148110bd18520443e52148110fc90710443f141c4110fc8c710443f131c4110fc88710443f121c4
  | 5 => 0x544436c62551109b189544427f6155110ddd85544427761551109fd81544437b60551109f994544433d5415110cf990544427e63151109f58c544427e62151109f588544427e6115110dd584544427c61151109f980544427c60151109f993534427d64d4d109f98b534427d62d4d10d7d4e534427e6494d109f592534427e6394d109f98a534427d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10bbd8953442ec6254d109fd91534433f6454d108fd91534427c6454d10cf191534423c6454d10d7d8d534427f6254d10dbd89534426f6254d109f189534436c6254d109b189534427f6154d10ddd85534427f6054d10ded81534427e6514d10d754c53442ee6214d10bb588534427e6414d109f590534435e6314d109f988534436e6214d109b988534427d6214d10db588534426d6214d109f98453443756114d109f184534427e6014d109f180534427f65d0d109f997434427d65d0d109f197434435f53d0d10d714f43442f661d0d10bd587434427f6590d109f996434427d6590d109f196434433f5490d10cf15243442ee6290d10bb58a43442f66190d10bd586434427f6550d109f995434427d6550d109f195434427f6510d109f994434427d6510d109f194434433f5410d10cf150434435f5310d10d714c43442f66110d10bd58443442fa6010d10be580434427e64d49109f593524427e63d49109f58f524436f52949109f992524427d64949109f98e524427d6394910dd58652443796094910afd9152442bc6454910b7d8d52442dc63549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910ddd85524427f6054910ded81524427e6514910b798c52442dd6314910db548524427e64149109f590524427e6314910d798c524425e63149109f58c524435d63149109758c524436e62149109f184524427f65d09109f997424427d65d09109f197424436f52d0910db14b42442f661d0910bd587424427f65909109f996424427d65909109f196424433f5490910cf15242442de6390910b758e42442f66190910bd586424427f65509109f995424427d65509109f195424427f65109109f994424427d65109109f194424433f5410910cf150424436f5210910db14842442f66110910bd58442442fa6010910be580424427f65cc9109f997324427d65cc9109f197324435e53cc910d754f324436f52cc910db14b32442f661cc910bd587324427f658c9109f996324427d658c9109f196324435f538c910d714e324436e528c910bd98632442f5618c9109fd95324427e654c9109f595324427c654c910d794d324435d534c910db949324427f650c9109f994324427d650c9109f194324435f530c910d
  | 6 => 0x27e64d4a109f593528427e63d4a109f58f528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528427f6454a109f191528427f6354a109f18d528436f6254a10af99052842bd6414a10b798c52842dd6314a10db548528427f65d0a109f997428427d65d0a109f197428433e54d0a10cf553428427f6590a109f996428427d6590a10b798e42842dd6390a10db94a428436d5290a10bd98642842f56190a109fd95428427e6550a109f595428427c6550a10cf951428433d5450a10db949428436d5250a10bdd8542842f46150a109fd94428427e6510a109f59442842fa6010a10be580428427f65cca109f997328427d65cca109f197328435e53cca10d754f328427f658ca109f996328427d658ca10db94a328436d528ca109fd95328427e654ca109f595328427c654ca10d794d328435d534ca10db949328436d524ca10bdd8532842f4614ca109fd94328427e650ca109f59432843cd320ca10bd98432842f5610ca10cf953418433d54d0610be98341842f960d0610dd597418437754d0610ed953418437554d0610ed553418437753d0610dd54f418437752d0610dd54b41843f260d0610bd58341843f160d0610b798e41842dd6390610bb98a41842ed6290610cf951418433d5450610bed8141842f86050610bd59441843756510610ed99041843775410610dd55041843775310610dd54c41843775210610dd54841842f56010610d794f318435d53cc610be98331842f960cc610d794d318435d534c610bed8131842f8604c610bb98831842ed620c610f54c4318436e52c8610db54b21842fa60c8610be583218436e5248610db54921842fb6048610be18121842de6308610b758c21843e52108610cfd53408433c54d0210edd07408433e5490210cf55240842f66190210bd586408433f5450210cf15140842df6350210b718d40842ef6250210bb18940842f76150210bd18540843b74150210cf950408433d5410210b798c40842dd6310210bb98840842ed6210210bd98440842f56110210d7d4f308435c53cc210d794e308435d538c210bd98630842f5618c210d7d4d308435c534c210af99030842bd640c210d794c308435d530c210bb98830842ed620c210bd98430842f5610c210bd98620842f56188210bd597108437565c4210bd99310842f464c4210ddd53108437554c4210ddd4f108437553c4210ddd4b108437552c4210be597108437965c42109f98f544427d63d51109f98b544427d62d5110cfd52544427e64951109f98e544427d63951109f98a544427d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f63551109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189
  | 7 => 0x24c710bd18131c435e530c710d754c31c42ee620c710bb58831c43d5310c710be98031c42f9600c710db94a21c436d5288710be98221c42f96088710bdd9221c42f56488710dd95221c43745488710bdd8e21c42f56388710ddd4e21c43755388710dd94a21c43e65288710f954a21c43745288710bd98221c43f26088710fc58221c42f76548710ddd9521c42f76448710bd59121c43765448710dd15121c42f76348710bd58d21c43775348710dd54d21c43e76248710f9d4921c43765248710dd14921c43e45248710d914921c43e74248710f910921c43e63248710f94c921c42f46048710b798c21c42dd6308710db94821c436d5208710f948421c42fa6008710be58021c433e54d0310cf55340c42f661d0310bd58740c43b541d0310cf95140c433d5450310b7d8d40c42dc6350310bbd8940c42ec6250310bdd8540c42f46150310ed50540c42de6310310b758c40c42ee6210310bb58840c42f66110310bd58440c435e53cc310d754f30c42f661cc310bd58730c43d531cc310d794d30c435d534c310bdd8530c42f4614c310f54c530c42be640c310af59030c42ee620c310bb58830c42f6610c310bd58430c42f661c8310bd58720c43e521c83109f98f548427d63d52109f98b548427d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a54842df6355210b718d54842ef6255210bb189548433f64552109fd8d548435f635521097d8d548427c6355210d718d548425c63552109fd89548436f62552109bd89548427c6255210db189548426c6255210ddd85548433d5415210b798c54842dd6315210bb98854842ed6215210cf990548427e6315210d798c548425e63152109f58c548435d63152109758c548427e6215210db988548426e62152109f588548436d62152109b58854843756115210de980548427e64d4e109f593538427e62d4e109f58b538437561d4e10de983538435f5394e109f992538427d6494e109f98a538427d6294e109fd91538427c6454e10d7d8d538427f6254e109f18953842be6414e10af590538435d5314e10bb98853842ed6214e109f990538433e6414e108f990538427d6414e10cf590538423d6414e10d798c538427e6214e10db988538426e6214e109f588538436d6214e109b58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438433e54d0e10cf553438435f53d0e10d714f438427f6590e109f996438427d6590e109f196438435e5390e10d754e43842ee6290e10bb58a43842f66190e10bd586438427f6550e109f995438427d6550e109f195438433e5450e10cf551438435e5350e10d754d43842f76150e10bd185438427f6510e109f994438427d6510e109f194438435f5310e10d714c43842fa6010e10be5804384
  | 8 => 0x109f58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f10dd98653c427f6454f109f19153c435f6354f109fd8953c427c6254f10d754c53c42ee6214f10bb58853c427e6414f109f59053c435e6314f109f98853c436e6214f109b98853c427d6214f10db58853c426d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10d794f43c435d53d0f10bd98743c42f561d0f109fd9643c427e6590f109f59643c427c6590f10bb98a43c42ed6290f10bd98643c42f56190f109fd9543c427e6550f109f59543c427c6550f109fd9443c427e6510f109f59443c427c6510f10d794c43c435d5310f10bd98443c42f56110f10dbd4a52c427e6494b109f59252c427e6394b109f58e52c427f6454b109f19152c427f6354b109f18d52c42de6314b10b758c52c436d5214b109f99052c427d6414b109f98c52c435e6314b109798c52c427d6314b10d758c52c425d6314b10dd98452c43796014b109fd9742c427e65d0b109f59742c436e52d0b10db54b42c42f661d0b10bd58742c427f6590b109f99642c427d6590b109f19642c42de6390b10b758e42c42f66190b10bd58642c427f6550b109f59542c427c6550b109fd9442c427e6510b109f59442c427c6510b10db94842c436d5210b10bd98442c42f56110b109fd9732c427e65ccb109f59732c435e53ccb10d754f32c42f661ccb10bd58732c427f658cb109f99632c427d658cb109f19632c436e528cb10db54a32c42f6618cb10bd58632c427f654cb109f59532c427c654cb10d794d32c435d534cb10db94932c436d524cb109fd9432c427e650cb109f59432c427c650cb10f34c832c42f6610cb10bd58432c433f54d0710cf15341c433e5490710cf55241c42de6390710b758e41c42ee6290710bb58a41c42fa6090710be58241c43756590710dd95241c43b65490710ed55241c43745490710f598e41c42f56390710f558e41c42d56390710f998a41c42f56290710f958a41c42e56290710bd98241c43f26090710fc58241c433f5450710cf15141c42f76550710ddd9541c43b76450710edd5141c43765450710dd15141c43b45450710bdd8d41c42f76250710bd18141c433e5410710cf55041c43b54110710be98041c42f96010710d7d4f31c435c53cc710d794e31c435d538c710be98231c42f9608c710dd59631c42f7648c710bd59231c4376548c710dd15231c4376538c710f594e31c43d5538c710dd14e31c42f5628c710dd54a31c42f6608c710fc98231c43f1608c710d7d4d31c435c534c710bdd9531c4377654c710bdd9131c42f5644c710dd95131c4374544c710f5d8d31c43d7534c710dd94d31c4374534c710f514d31c4354534c710f5d0d31c43d4434c710bdd8931c4375524c710f5cc931c43d53
  | 9 => 0x949410c36d5250430dd945410c37551504309fd94410c27e65104309f594410c33e5410430cf550410c36e5210430db548410c3765110430dd544410c33e54cc430cf553310c35e53cc430db94b310c36d52cc430dd947310c37551cc430be983310c2f960cc4309f596310c33e548c430cf552310c36e528c430db54a310c375518c4309fd95310c33e544c430cf551310c35e534c430db949310c36d524c430dd945310c33e540c430cf550310c2ee620c430bb588310c36e520c430db548310c376510c430dd544310c3d5310c430be980310c2f9600c4309fd96210c27e65884309f596210c33e5488430cf552210c36e5288430db54a210c3765188430dd546210c27f65484309f595210c27c6548430cf951210c33d5448430b7d8d210c2dc6348430dd945210c37551484309fd94210c27e65084309f594210c33e5408430cf550210c2de6308430b758c210c3765108430dd544210c3e521084309f992500c27d6494030d7d0e500c35c43940309f597400c33e54d0030cf553400c39f43d0030dd947400c37551d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd6390030dd946400c37551900309fd95400c33e5450030cf551400c2df6350030b718d400c39f4350030bdd85400c2f46150030dd945400c37551500309fd94400c27e65100309f594400c27c6510030cf950400c33d5410030b798c400c2dd6310030bd984400c2f56110030dd944400c3755110030cf953300c33d54cc030dd947300c37551cc030b7993300c2dc64cc030d7d53300c39e54cc030d7553300c39d54cc030c7553300c3d651cc030d7547300c3d551cc030d5547300c33e548c030cf552300c2dd638c030d794e300c376518c030dd546300c3ba548c030ee552300c2f9638c030de94e300c3da538c030f6d0e300c3d8438c030fc946300c3f1518c0309fd95300c33e544c030cf551300c376514c030dd545300c2df654c030d7d95300c25f654c030b7991300c2dc644c030d7d51300c39e544c030d7551300c39d544c030c7551300c3d6514c030d7545300c3d5514c030d5545300c2df604c030d7941300c2fb654c030ded95300c27b654c030ee951300c3b9544c030bed8d300c3db634c030de94d300c3da534c030fc945300c3f1514c030b798f54c42dd63d5310bb98b54c42ed62d53109f98f54c435e63d53109798f54c427d63d5310d758f54c425d63d53109f98b54c436e62d53109b98b54c427d62d5310db58b54c426d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c43766195310cfd9154c427f63553109f18d54c427f62553109f18954c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c427e64d4f109f59353c427e62d4f
  | 10 => 0x40c33c6395030cfd86540c33e6195030cf586540c33c6195030cf982540c33c6095030cfd91540c27f63550309f58d540c35c63550309fd85540c27c6155030cfd95540c39c6355030cf98d540c33c6355030c718d540c33f6155030cf985540c33d6155030cf185540c33e6055030cf181540c33c3055030af990540c33d5415030bd984540c2f561150309f990540c33e64150308f990540c27e6315030d798c540c25e63150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a60150309f992530c27d6494c309f597430c33e54d0c30cf553430c2dd65d0c30d7597430c25d65d0c30d7d53430c39e54d0c30d7553430c39d54d0c30c7553430c2dd60d0c309fd96430c27d6590c30cf952430c33d5490c30b798e430c35e5390c30bd986430c2f56190c30be982430c2f96090c309fd95430c33e5450c30cf551430c35e5350c309fd94430c27d6510c30cf950430c33d5410c30be980430c2f96010c30d7594430c25d6510c30b7990430c39e6410c30d7d50430c39e5410c30d7550430c39d5410c30c7550430c3da6010c30b7580430c3d96010c30af993510c2bd64d4430cf953510c33d54d4430bb98b510c2ed62d4430cf952510c33d5494430ddd46510c27e64944309f592510c27e62944309f58a510c3775494430dd952510c3b65494430cd952510c3755494430ed552510c3355494430dd152510c3d74394430f510e510c3775294430dd94a510c3e65294430d994a510c3776494430dd992510c3756494430dd192510c3746394430ddd0e510c3764394430dd50e510c3744394430ddd8a510c3766294430dd58a510c3746294430dd982510c3746094430cf951510c33d5454430db949510c27f64544309f191510c35f4354430d710d510c27f62544309f189510c3776554430ddd51510c3765454430ed951510c3365454430dd551510c3b55454430cd551510c3745454430f5d0d510c3d44354430ddd49510c3765254430f9949510c3665254430dd549510c3e55254430d9549510c3776454430dd991510c3756454430dd191510c3766354430ddd0d510c3574354430dd90d510c3754354430dd10d510c3544354430ddd89510c3766254430dd589510c3746254430dd981510c3746054430dd0c1510c2be6414430af590510c33e5414430cf550510c2ee6214430bb588510c36e5214430db548510c2f66114430dd544510c27f65d04309f997410c27d65d0430cf953410c33d54d0430db94b410c36d52d0430dd947410c37551d04309fd96410c27e65904309f596410c33e5490430cf552410c2de6390430b758e410c2ee6290430bb58a410c36e5290430db54a410c3765190430dd546410c27f65504309f595410c27c6550430cf951410c33d5450430b7d8d410c2dc6350430db
  | 11 => 0x7761551309f185544c37461551309d185544c27f6055130ded81544c27e6515130cf550544c33e64151309f98c544c35d63151309f18c544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d309f996434c2f66190d30bd586434c2de6590d30d7996434c25e6590d30b7592434c35e5490d30d7152434c3d66190d30b7586434c3d56190d30b5586434c2de6090d309f195434c33f5450d30cf151434c2fb6050d30be181434c35c6550d3097195434c39f6450d30e7d51434c35e5450d30d7151434c39c5450d30b7d85434c3db6050d30b7181434c3d86050d309f994434c2de6310d30e750c434c27e64d45309f593514c27e62d45309f58b514c3775194530afd91514c2bc6454530bbd89514c2ec6254530bb988514c2ed6214530dd544514c27e64145309f590514c27e6214530db988514c26e62145309f588514c36d62145309b588514c27e65d05309f597414c27c65d0530b798f414c2dd63d0530ddd47414c37451d05309f996414c27d65905309f196414c33f5490530cf152414c2de6390530b758e414c2ee6290530bb58a414c27f65505309f995414c27c65505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c3775110530dd144414c2fa6010530be580414c27e65cc530b7997314c35e65cc530b7d93314c2dd64cc530d7953314c35c54cc530b758b314c35f52cc530d7147314c2de60cc530b758e314c377518c530dd146314c2fa608c530be582314c377514c530dd145314c2fb604c530be181314c2df644c530b7591314c35e544c530d7151314c2df624c530d7d49314c3d7614c530f5d45314c35c514c530f5145314c354514c530f5d05314c3d4414c530f6d81314c2dc604c530f6181314c27e650c530b798c314c2ee620c530bb588314c3d5310c5309f996214c27d65885309f196214c2de6388530b758e214c36f5288530db14a214c3d531885309fd95214c27e65485309f195214c2de6348530b758d214c3d531485309f994214c27d65085309f194214c2de6308530b758c214c3775108530dd144214c3e521085309f997404c33f54d0130cf153404c2de63d0130b758f404c39d43d01309f996404c27f65501309f595404c27c6550130cfd51404c33c5450130b7d8d404c2dc6350130e750d404c2f76150130bd185404c27e6510130b798c404c2dd6310130bd984404c2f56110130f690f304c3d943cc130f6cc7304c3d931cc130b7d92304c2dd648c130d7952304c35c548c130b7586304c3db508c130bd987540c2f561d50309f98f540c35e63d50309f987540c37661d50309d987540c27d61d5030dd587540c27561d50309f983540c37a60d50309f596540c33f54950309f986540c27d61950308f596540c39c6395030cf98e5
  | 12 => 0xc730dd54431cc3d5310c730be98031cc2f9600c7309fd9621cc27e65887309f59621cc2de6388730b758e21cc3765188730dd54621cc3d531887309fd9521cc27d65487309f19521cc2de6348730b758d21cc3765148730dd54521cc3d531487309fd9421cc27e65087309f59421cc2de6308730b758c21cc3e52108730cf95340cc33d54d0330b798f40cc2dd63d0330e750f40cc33e5450330cf55140cc2df6350330b718d40cc39d4350330bdd8540cc2f46150330b798c40cc2dd6310330bd98440cc2f56110330d758f548c27e61d52309f587548c37a60d5230cfd52548c27e61952309f586548c2f76155230bd185548c33f6455230d7d8d548c27f6155230ddd85548c27761552309f185548c37461552309d185548c33d5415230bd984548c2f56115230cf990548c35d63152309f984548c37661152309d984548c27d6115230dd584548c2756115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c35d65d0e30d7d53438c39e54d0e30d7553438c39d54d0e30f6983438c2dd60d0e30f6583438c2f66190e30bd586438c33e5450e30cf551438c2fb6050e30be181438c2dd6510e30d7594438c39e6410e30d7d50438c35d5410e30b7580438c37751946309f992518c27d64946309f98a518c27d62946309fd91518c27c6454630d7d0d518c35c43546309fd89518c27c6254630af990518c2bd6414630bb988518c2ed6214630dd544518c27f65d06309f997418c27d65d0630cf953418c33d54d06309fd96418c27e65906309f596418c2de6390630b758e418c2ee6290630bb58a418c3765190630dd546418c27f65506309f595418c27c6550630cf951418c33d5450630b7d8d418c2dc6350630dd945418c37551506309fd94418c27e65106309f594418c2fa6010630be580418c376518c630dd546318c2fa608c630be582318c376514c630dd545318c2fb604c630be181318c2ee620c630bb588318c3d5310c6309fd96218c27e65886309f596218c3765188630dd546218c27f65486309f595218c27c6548630b7d8d218c2dc6348630dd945218c37551486309fd94218c27e65086309f594218c2de6308630b758c218c3e52108630cfd53408c33c54d0230e7d0f408c33e5490230cf552408c2de6390230b758e408c33f5450230cf151408c2df6350230b718d408c39f4350230bdd85408c2f46150230cf950408c33d5410230b798c408c2dd6310230bd984408c2f56110230b7597308c35d65cc230b7993308c2dc64cc230d7d53308c35d54cc230d7547308c2f965cc230de597308c27e61d51309f587544c33f54951309f992544c27d6395130d758e544c27e61951309f586544c27d6095130de582544c2f76155130bd185544c33f64551309fd8d544c35f635513097d8d544c27f6155130ddd85544c2
  | 13 => 0xdd946211037551884409fd95211027d65484409f19521102bf6448440af191211035e5348440d754d21103765148440dd545211027f65084409f994211027d6508440b798c21102dd6308440d794c211035d5308440dd94421103755108440f9484211035e53d0040d754f401037651d0040dd547401039e53d0040cf54f401039d53d0040c754f40103b651d0040cf54740103b551d0040cd54740102bd6490040cf952401035e5390040d754e40103765190040dd54640102f96490040de95240103ba5490040f694e40103d95390040fc94640103f151900409fd9540102df6350040b718d401035e5350040d754d40102f76150040bd18540103765150040dd54540102bf6550040cfd95401023f6550040e7d8d401039c6350040e794d401033d5350040e754d401031d5350040edd8540103b46150040ed945401033d5150040ed54540103355150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103db6350040f618d40103da5350040f654d40103f36150040fc18540103f25150040fc54540102f661d5330bd58754cc35e63d53309f98754cc37661d53309d98754cc27d61d5330dd58754cc27561d5330de58354cc33f5495330d798e54cc27e61953309f58654cc33f64553309fd8554cc27c6155330cf55054cc33e6415330d798c54cc27e61153309f58454cc3796015330cfd5343cc33c54d0f30cf95243cc33d5490f30bd98643cc2f56190f30be98243cc2f96090f30d759643cc35e5490f30e795243cc39d5490f30d715243cc3d66190f30b758643cc3d56190f30b558643cc2de6090f30f698243cc3d96090f30cfd5143cc33c5450f30b7d9543cc35f6550f30e7d9143cc39f5450f30d795143cc35c5450f30e715143cc2df6150f30b718143cc33e5410f30cf55043cc39d4310f30be98043cc2f96010f30ddd4651cc27e64947309f59251cc27e62947309f58a51cc27f64547309f19151cc27f62547309f18951cc2ee6214730bb58851cc37551147309fd9741cc27e65d07309f59741cc2de63d0730b758f41cc37651d0730dd54741cc27f65907309f99641cc27d6590730b798e41cc2dd6390730bb98a41cc2ed62907309fd9541cc27d65507309f19541cc27f65107309f99441cc27d6510730b798c41cc2dd6310730dd94441cc3755110730dd94731cc37551cc730be98331cc2f960cc730b7d9331cc2dd64cc730d795331cc35c54cc730b758b31cc35d52cc730d794731cc3d651cc730f554731cc2de60cc730f698331cc3d960cc730b7d9531cc35f654c730b7d9131cc2dd644c730d795131cc35c544c730b7d8931cc35d524c730f5d8531cc3d7514c730d794531cc3d4514c730f5d0531cc3d4414c730b718131cc2ee620c730bb58831cc37651
  | 14 => 0x4640503bb5090140bd98753102f561d4c40d7d4e531027e6194c409f586531035c6494c40d7d86531035e6194c40d7586531035c6194c40d7982531035c6094c409fd85531027c6154c40d7d95531035e6454c40d7d85531035e6154c40d7585531035c6154c40d7981531035c6054c40d710153102de6314c40d754c53102f66114c40bd584531033e54d0c40d794f431035d53d0c40be98343102f960d0c409f596431035d5390c40bd98643102f56190c409fd95431033e5450c40d794d431035e5310c40d754c43102fa6010c40be58043102de63d4440b758f511035e53d4440d754f51102ee62d4440bb58b511035e5394440d754e511037751944409f98e511027d63944409f98a511027d6294440ddd4e51103765394440f594e51103565394440dd54e51103d55394440d554e51103745394440ddd4a51103765294440f994a51103665294440dd19251103776394440dd98e51103756394440dd18e51103774394440dd90e51103754394440dd10e51103776294440dd98a51103756294440dd18a51103766094440dd182511035e5354440d754d511036e52544409fd8d511027c63544409fd89511027c6254440ddd9551103775354440dd94d51103d65354440d594d51103755354440f554d51103555354440dd14d51103775254440dd94951103e65254440d994951103755254440f954951103655254440dd99151103776354440dd98d51103756354440dd18d51103774354440dd90d51103754354440dd10d51103776254440dd98951103756254440dd18951103766054440dd18151103744054440b798c51102dd6314440d794c511035d5314440bb98851102ed6214440db948511036d5214440bd98451103755114440cf953411035e53d0440d754f411036e52d0440db54b411037651d0440dd54741102fa60d0440be583411027d6590440b798e41102dd6390440d794e411035d5390440bb98a41102ed6290440db94a411036d5290440dd546411027f6550440cf951411035e5350440d754d411036e5250440db54941103765150440d794c411035d5310440db948411036d5210440dd94441103755110440be98041102f960104409fd97311027e65cc4409f597311035e53cc440d754f311036e52cc440db54b311037651cc440dd547311027f658c4409f996311027d658c440d794e311035d538c440db94a311036d528c440dd9463110375518c4409fd95311027d654c4409f19531102bf644c440af191311035e534c440d754d311036e524c440db5493110376514c440dd545311027f650c4409f994311027d650c440d794c311035d530c440bb98831102ed620c440db948311036d520c440dd9443110375510c440f54c4311027f65884409f996211027d6588440d794e211035d5388440db94a211036d528844
  | 15 => 0x5035c5314540dbd48515037551145409f98c515027d63145409f988515027d6214540bd99451503766514540ed59051503775314540f5d4c51503575314540dd94c51503755314540dd14c51503d45314540d514c51503b74314540ed50c51503775214540f9d4851503675214540dd94851503755214540dd14851503e45214540d914851503776414540ddd8c51503766314540dd58c51503746314540ddd0c51503764314540dd50c51503744314540ddd8851503766214540dd58851503746214540ddd8051503756014540dd500515027e65d0540d7d4f415035c53d0540dbd4b415036c52d0540dd14741502be65d0540cf99741502bd63d0540e7d4f415039c53d0540af58b41503af52d0540eb14b41503b751d0540cf14741503b451d0540cd14741502be60d0540af59241502de6390540b758e415035f5390540d714e41502ee6290540bb58a415036f5290540db14a41503775190540dd14641502fa6090540be582415035f5350540d714d415036f5250540db14941503775150540dd14541502fb6050540be18141502bf6350540e7d4d415039c5350540afd8941503af5250540eb14941503b76150540edd45415033c5150540ed14541503bb6050540af18141503b860505409f99441502be6410540d7d4c415035c5310540dbd48415036c5210540ddd4441503b541105409f997315027d65cc5409f19731502be64cc540af593315035f53cc540d714f315039f43cc540dbd4b315036c52cc540ddd47315037451cc5409f996315027d658c5409f19631502be648c540af592315035f538c540d714e315036f528c540db14a3150377518c540dd14631503b7418c5409fd95315027e654c5409f19531502be644c540af591315035f534c540d714d315039f434c540dbd49315036c524c540ddd453150374514c540edd05315027e650c5409f594315027c650c540af99031502bd640c540d7d4c315035c530c540bb98831502ed620c540dbd48315036c520c540ddd443150374510c540f54c431502fa600c540be580315027e65885409f596215027c6588540af99221502bd6488540d7d4e215035c5388540dbd4a215036c5288540ddd4621503745188540edd06215027f65485409f995215027c6548540af99121502bd6448540d7d4d215035c5348540ddd4521503745148540edd05215027e65085409f594215027c6508540af99021502bd6408540b798c21502dd6308540d7d4c215035c5308540ddd4421503745108540f948421502fa6008540be580215035f53d0140d714f405037751d0140dd14740503db53d0140f614f40503bb43d0140ee50f40503f351d0140fc14740503bb41d0140ee507405035f5390140d714e40503775190140dd14640502bd6390140e7d4e405039c5390140af58640503b75190140ed1
  | 16 => 0xd6508740af99021d02bd6408740b798c21d02dd6308740f948421d035f5394e409f986539027d6194e409fd85539027c6154e40d754c53902f66114e40bd584539035e5390e40d754e43902f66190e40bd58643902fa6090e40be582439035e5350e40d754d43902fb6050e40be181439037751946409f98e519027d63946409f98a519027d62946409fd8d519027c63546409fd89519027c6254640b798c51902dd6314640bb98851902ed6214640dd54451902de6390640b758e41902ee6290640bb58a41903765190640dd54641902fa6090640be58241903765150640dd54541902fb6050640be181419027f65cc6409f997319027d65cc640d794f319035d53cc6409fd96319027e658c6409f5963190376518c640dd546319027f654c6409f595319027c654c640afd9131902bc644c640d794d319035d534c640dd9453190375514c6409fd94319027e650c6409f59431902ee620c640bb58831903d5310c640be98031902f9600c6409fd96219027e65886409f59621903765188640dd546219027f65486409f595219027c6548640afd9121902bc6448640dd945219037551486409fd94219027e65086409f59421902de6308640b758c21903e52108640be98021902f96008640af597409033d65d0240cf54f409033d51d0240be597409037965d02409f987535027d61d4d40e7d93535035f64d4d40d7d87535035e61d4d40d7587535035c61d4d40d7d83535035d60d4d40d7d4e53502f66194d40bd58653502f76154d40bd185535035d5314d409f984535027d6114d40b7994535035e6514d40e7590535035f6414d40d7d84535035e6114d40d7584535035c6114d40d7d80535035d6014d40d7500535027e65d0d40d714f43502be65d0d40cf997435039f53d0d40cf14f435039c53d0d40c714f43502bd61d0d40af98343502bd6490d40d7d4e435035c5390d40bd98643502f56190d40be98243502f96090d40d7d4d435035c5350d40bed8143502f86050d40e7d8d435039f5350d40cf14d435039c5350d40afd8543503bb6050d40af18143503b86050d409f99443502be6410d40d7d4c435039d4310d40d7d4f515035c53d45409f98f515027d63d45409f98b515027d62d4540edd93515037753d4540f5d4f515035753d4540dd94f515037553d4540dd14f51503d453d4540d514f51503b743d4540ed50f515037752d4540f9d4b515036752d4540ddd93515037763d4540dd98f515037563d4540dd18f515037743d4540dd90f515037543d4540dd10f515037762d4540dd98b515037562d4540dd18b515037760d4540dd58351502de6394540b758e515035f5394540d714e51502ee6294540bb58a515036f5294540ddd4651502df6354540b718d515035f5354540d714d51502ef6254540bb189515036f5254540d7d4c51
  | 17 => 0x84219dd9521087765448421dd15121087775348421f594d21087755348421f554d21087555348421bdd8921087765248421f994921087e74248421f990921087e54248421f910921087e73248421f98c921087e53248421f90c921087e76548421b9d9521087676548421f9d9121087e66448421f959121087e46448421f9d5121087e65448421d995121087e55448421f915121087645448421f9d8d21087e66348421f958d21087e46348421f9d4d21087675348421f994d21087c65348421f954d21087655348421f154d21087455348421f914d21087e74348421f990d21087e54348421f910d21087e76048421f998121087e56048421f918121086de63d4021b758f500875e53d4021d754f50087e521d4021d794e500875d5394021f9486500877b50940219f992500867d64940219f98e500867d6394021d794d500875d5354021f9485500867f64540219f191500867f63540219f18d50087762154021dd48550087652154021af99050086bd6414021b798c50086dd6314021d794c500875d5314021f948450087795014021d7d4e53d02f66194f40bd58653d027e6194f40dd98653d02766194f409f58653d03756194f409d58653d027f6154f409f18553d035d5314f40d794f43d035d53d0f40be98343d02f960d0f40cf94f43d039e53d0f40e754f43d02bd61d0f40af98343d03ba60d0f40ee58343d02f66190f40bd58643d02bf6550f40cfd9543d039f6350f40e7d4d43d033e5350f40e714d43d02bf6150f40af18143d035e5310f40d754c43d039d4310f40be98043d02f96010f40b798e51d02dd6394740bb98a51d02ed6294740ddd4651d027e6394740d798e51d025e63947409f58e51d035d63947409758e51d027e6294740db98a51d026e62947409f58a51d036d62947409b58a51d027f63547409f18d51d027f62547409f18951d03755114740dd94741d037551d0740be98341d02f960d0740af58f41d02bd62d0740cf94741d03b651d0740ed54741d02be60d0740ee98341d03b960d0740b798e41d02dd6390740bb98a41d02ed6290740afd9541d033f6550740afd8d41d02bf6250740edd8541d03b75150740cf94541d03b45150740af18141d03765110740dd54441d03b54110740be98041d02f960107409fd9731d027e65cc7409f59731d02be64cc740af59331d039f43cc7409fd9631d027e658c7409f59631d02be648c740af59231d03b7418c7409fd9531d027d654c7409f19531d02be644c740af59131d039f434c740edd0531d027f650c7409f99431d027d650c740af99031d02bd640c740bb98831d02ed620c740f54c431d027f65887409f99621d027d6588740af99221d02bd6488740edd0621d027f65487409f59521d027c6548740af99121d02bd6448740edd0521d027f65087409f99421d027
  | 18 => 0x8f590504867e6314121d798c504865e63141219f58c504875d63141219758c50487774114121dd10450486de63d5021b758f540867e63d5021d798f540865e63d50219f58f540875d63d50219758f540867e61d5021dd987540867661d50219f983540867d60d50219f596540873f54950219f98e540867d63950219f982540867d6095021cfd91540867f63550219f18d540867f60550219f181540873d5415021b798c54086dd6315021be98054086f960150219f990540873e64150219f98c540875e63150219798c540867d6315021d758c540865d63150219f984540877661150219f980540877a60150219e980540867d6015021de580540867960150219f993530867d64d4c219f987530877661d4c219f983530867d60d4c219f596530875f5394c219f992530867d6494c219f982530867d6094c2197596530875f5494c21d7952530875d5494c21d7152530875f6494c21d7992530875d6494c21d7192530875e6194c21d7186530875f6094c21d7982530875d6094c21d7182530867f6454c219f191530875f6354c219fd81530867c6054c21d7d95530875f5454c21d7951530875d5454c21d7151530875f6454c21d7991530875d6454c21d7191530875e6154c21d7185530875c2154c21d7d81530875e6054c21d7581530875c6054c21b798c530875d5314c219f990530867d6414c219f98c530875e6314c219798c530867e6114c21dd98453086766114c219f980530867d6014c219fd97430867e65d0c219f597430867c65d0c21d794f430875d53d0c21bd98743086f561d0c219fd96430867e6590c219f596430867c6590c21d794e430875d5390c21bd98643086f56190c219fd95430867e6550c219f595430867c6550c21d794d430875d5350c219fd94430867e6510c219f594430867c6510c21d794c430875d5310c219f992510867d64944219f98e510867d63944219f597410875e53d0421d754f410877651d04219fd96410867d6590421cf952410873d5490421b798e41086dd6390421d794e410875d5390421bb98a41086ed62904219fd95410875e5350421d754d410867f65104219f994410867d65104219f194410873e5410421cf550410875e5310421d754c41086ee6210421bb58841087765110421ed504410867d65cc421d794f310875d53cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c421dd946310867f654c421d794d310875d534c421dd945310867f650c4219f994310867d650c4219f194310875e530c421d754c31086ee620c421bb58831087d5310c421d794e210875d5388421dd95221087745488421ddd4e21087d65388421dd54e21087d55388421d554e21086f56288421b958a21087765288421f994a210867f6548421d794d210875d5348421bdd952108777654
  | 19 => 0x1544867c60551219f994544873d5415121cf990544867e63151219f58c544867e60151219f580544867e64d4d219f593534867e60d4d219f58353486be6494d21af592534875f5394d219f992534873e6494d218f992534867d6494d21cf592534863d6494d219f98e534867d6194d21dd586534867e6094d219f582534867f6454d219f191534875f6354d219fd8553487776154d219fd81534867c6054d219f994534875d5314d219f990534867d6414d21d798c53487756114d219f980534867d6014d219fd97434867e65d0d219f597434867c65d0d21cfd53434873c54d0d21d794f434875d53d0d219fd96434867e6590d219f596434867c6590d21d7d4e434875c5390d21bd98643486f56190d219fd95434867e6550d219f595434867c6550d21cfd51434873c5450d21d7d4d434875c5350d21bdd8543486f46150d219fd94434867e6510d219f594434867c6510d21d794c434875d5310d21bd98443486f56110d219f997414873f54d0521cf15341486ee62d0521bb58b414877665d05219d997414877754d0521edd53414877554d0521ed15341486f563d0521ddd4f414877553d0521bd98b41487e662d0521b998b41487e562d0521f9d0b41486f560d05219f99641486de6390521b758e41486ee6290521bb58a41486f661905219fd95414867d65505219f195414873f5450521cf15141486ef6250521bb189414867e6510521bd99441487766510521bd99041487b66410521ddd5041487755410521bd58c41487775310521dd54c41487e76210521bd98841487e46210521f9d0841487e44210521bd580414867e65cc521d7d4f314875c53cc521bb98b31486ed62cc5219f99631486f6658c521dd99631486f6648c521bd1923148776548c521dd15231486f5638c521dd94e3148774538c521f9d8a31486f6628c521f918a31487e7428c521f910a31487e6328c521bd582314867f654c5219f595314867c654c521d7d4d314875c534c521bbd8931486ec624c521dd1953148674654c521bd99131486f4644c521dd9513148774544c521f5d8d31487d7534c521dd94d3148774534c521f514d3148754534c521f5d0d31487d4434c521f9d8931486f4624c521f918931486e4624c521f9d0931487e4424c521f5cc931487e6324c521f54c931487e5324c521f14c931486f7604c5219f99431486ee620c521bb58831486f6610c521f54c431486ee6488521bb19221486ef6388521bb58e21487e75188521f9d0621487e44188521f98c621487e53188521bb582214867e64d41219f593504867e63d41219f58f504877631d4121dd4c7504877b5094121afd9150486bc6454121b7d8d50486dc6354121af99050486bd6414121b798c50486dd6314121de540504867e6414121cf990504863e64141219f590504873d6414121
  | 20 => 0x873d64d4e218f593538876d62d4e21dd987538867e60d4e219f583538875f5394e219f992538867d6494e21dd986538867e6094e219f582538867f6454e219f191538875f6354e219fd81538867c6054e21d754c538867e6414e219f590538875e6314e21db58853887766114e219f980538867d6014e219fd97438867e65d0e219f597438867c65d0e21d794f438875d53d0e21bb98b43886ed62d0e219fd96438867e6590e219f596438867c6590e21cf952438873d5490e21bb98a43886ed6290e21bd98643886f56190e219fd95438867e6550e219f595438867c6550e21bdd8543886f46150e219fd94438867e6510e219f594438867c6510e21cf950438873d5410e21d794c438875d5310e21bd98443886f56110e21cf953428873d54d0a21bd98742886f561d0a21b798e42886dd6390a21bd586428873e5450a21cf55142886f76150a21bd18542887ad4210a21d794f328875d53cca21bd98732886f561cca21d794d328875d534ca21bdd8532886f4614ca21f34c832886f5610ca21bd597418877565d0621ddd53418877554d0621bd58f418877753d0621dd54f41886f662d0621bd583418873e5490621cf55241886de6390621b758e41886ee6290621bb58a418873e5410621cf55041886ee6210621bb58841886f56510621dd59441887b66410621ddd5041887b65410621dd55041887b55410621cd55041886f56310621ddd4c41887755310621bd98841887e66210621f958841886f56010621d7d4f318875c53cc621d794e318875d538c621bb98a31886ed628c621bd5963188775658c621bd99231886f4648c621dd9523188774548c621dd94e31887d6538c621f554e3188774538c621bd98a31887e6628c621f958a31886f5608c621d7d4d318875c534c621bdd953188777654c621bd99131886f4644c621dd9513188774544c621f5d8d31887d7534c621dd94d3188774534c621f514d3188754534c621f5d0d31887d4434c621bd18931887d7324c621f54c931886f7604c621d794c318875d530c621bb98831886ed620c621f54c431886f565c8621dd59721886f664c8621bd19321886f763c8621bd58f218877b50942219f992508867d64942219f98e508867d6394221ddd06508877441942219fd91508867c64542219fd8d508867c6354221dd8c550887753154221dbc8550886be6414221af59050886de6314221b758c50887795014221b798f54486dd63d51219f98f544875e63d51219798f544867d63d5121d758f544865d63d5121dd587544867e60d51219f583544873f5495121b798e54486dd63951219f992544867e6395121d798e544865e63951219f58e544875d63951219758e544867d6195121dd586544867e60951219f582544873f64551219fd8d544867c63551219fd85544877761551219fd8
  | 21 => 0x65508319f195420c76e5250831db549420c67f65108319f994420c67d6510831db948420c76d5210831d794f320c76e52cc831db54b320c6f661cc831bd587320c67d658c831db54a320c67f654c831d794d320c76e524c831bd984320c6f5610c8319f992510c67d64944319f597410c76e52d0431db54b410c77651d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd6390431bb98a410c6ed6290431db94a410c76d52904319fd95410c76e5250431db549410c67f65104319f994410c67d65104319f194410c73e5410431cf550410c6de6310431b758c410c76e5210431db548410c7765110431ed504410c76e52cc431db54b310c75e54cc431d7153310c7ce52cc431d754b310c7cd52cc431d354b310c6dd638c431d794e310c76e528c431db54a310c776548c431dd152310c6f5638c431b558e310c776538c431f594e310c7e6528c431dd54a310c7e5528c431d954a310c67f654c431db949310c76d524c431b7d95310c75f654c43197d95310c75e544c431d7151310c7ce524c431d7549310c7cd524c431d3549310c6df614c431d7945310c7d7414c431f5905310c7d5414c431f5105310c6f7654c431ddd95310c677654c431dd951310c774544c431bdd8d310c7d7634c431dd94d310c7d6534c431f5d0d310c7d6434c431f550d310c7d4434c431f9949310c775524c431f9549310c765524c431f5cc9310c7d6324c431f54c9310c7d4324c431f5d95310c6d7654c431d5d95310c7d7644c431f5991310c7d5644c431f5191310c7d7544c431f5951310c756544c431f5551310c7d4544c431d5151310c7d7624c431f5989310c7d5624c431f5189310c7d7524c431f5949310c7c6524c431f5549310c755524c431f1549310c745524c431f5149310c7d7424c431f5909310c7d5424c431f5109310c7d7604c431f5981310c7d5604c431f5181310c6ee62d4031bb58b500c76e52d4031db54b500c7d531d4031db94a500c76d5294031f54c6500c77b50940319f992500c67d64940319f98a500c67d6294031db949500c76d5254031f54c5500c67f64540319f191500c67f62540319f189500c75f3154031dd8c5500c75d3154031dd4c5500c7553154031af990500c6bd6414031bb988500c6ed6214031db948500c76d5214031f54c4500c7795014031b798f54886dd63d52219f98f548875e63d52219798f548867d63d5221d758f548865d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548867e60952219f582548873f64552219fd8d548867c6355221dd185548867f60552219f181548873d5415221cf990548867e63152219f58c548876d6215221dd984548867e60152219f58054886be64d4e21af593538867e64d4e21cf993538863e64d4e219f593538
  | 22 => 0x531bb98a414c6ed6290531bd986414c67f65505319f595414c67c6550531cfd51414c73c5450531b7d8d414c6dc63505319f994414c6f66510531dd994414c6f66410531ed990414c7775410531dd550414c7d76310531bd98c414c7d46310531f5d0c414c7d44310531bd588414c7775210531f5cc8414c7d53210531bd580414c6f664cc531bd193314c7d743cc531f510f314c6f562cc531f5ccb314c7d532cc531bd583314c6de648c531b7192314c6dd628c531f5d46314c7d7418c531f5106314c6dd608c5319f993504c67d64d41319f98b504c67d62d4131d7ccb504c75d32d4131ded42504c6bf6454131af191504c6ef6254131bb189504c6be6414131af590504c6ee6214131bb588504c77950141319f990504c73e64141318f990504c67d6414131cf590504c63d6414131d7d0c504c75c43141319f988504c76e62141319b988504c67d6214131db588504c66d6214131ddd04504c7744114131bb98b540c6ed62d50319f98f540c75e63d50319798f540c67e62d5031db98b540c66e62d50319f58b540c76d62d50319b58b540c67e61d5031dd987540c67661d50319f983540c67d60d50319f596540c73f54950319f98a540c67d62950319f982540c67d6095031cfd91540c67f62550319f189540c67f60550319f181540c73d5415031bb988540c6ed6215031be980540c6f960150319f990540c73e64150319f98c540c75e63150319f988540c76e62150319b988540c67d6215031db588540c66d62150319f984540c77661150319f980540c77a60150319e980540c67d6015031de580540c67960150319f992530c67d6494c319f597430c75e53d0c319fd96430c67d6590c31cf952430c73d5490c31bb98a430c6ed6290c31bd986430c6f56190c319fd95430c67f6510c319f594430c73e5410c31cf550430c75e5310c31e750c430c6f66110c31bd584430c76f52948319f992520c67d64948319f982520c67d6094831dbd52520c76e5494831db552520c76c5494831dbd92520c76e6494831db592520c76c6494831db18e520c76f4394831db90e520c76d4394831db10e520c76e6194831db186520c76f6094831db982520c76d6094831db182520c67f64548319f191520c67f60548319f181520c76f6554831dbd51520c76e5454831db551520c76c5454831dbd91520c76e6454831db591520c76c6454831db98d520c76f4354831db90d520c76d4354831db10d520c76e6154831db185520c76c3154831dbd81520c76e6054831db581520c76c6054831bb988520c76d52148319fd97420c67e65d08319f597420c6de63d0831b758f420c76e52d0831db54b420c6f661d0831bd587420c67f65908319f996420c67d6590831b798e420c6dd6390831db94a420c76d5290831bd986420c6f561908319fd95420c67d
  | 23 => 0xd550418c7b55410631cd550418c6f66310631f598c418c7d56310631bd588418c7755210631bd580418c6dd65cc631d7597318c75e54cc631d7153318c75d52cc631bd597318c77565cc631bd993318c6f464cc631bd58b318c6f560cc631ded42508c67e64942319f592508c67e62942319f58a508c7774194231dd106508c67f64542319f191508c67f62542319f189508c75f3154231af990508c6bd6414231bb988508c6ed6214231de540508c6ee62d5131bb58b544c75d63d51319f98b544c76e62d51319b98b544c67d62d5131db58b544c66d62d5131dd587544c67e60d51319f583544c73f5495131bb98a544c6ed62951319f992544c67d6395131d758e544c67e6295131db98a544c66e62951319f58a544c76d62951319b58a544c67d6195131dd586544c67e60951319f582544c73f64551319fd8d544c75f63551319fd89544c67c62551319fd85544c77761551319fd81544c67c60551319f994544c73d5415131cf990544c67e62151319f588544c67e60151319f580544c67e65d0d31cfd53434c73c54d0d31bd987434c6f561d0d31d7997434c65e65d0d31d7d53434c79f54d0d31d7553434c79c54d0d31b758b434c6de61d0d31f5987434c6d661d0d31f5587434c6dd60d0d319f996434c6de6390d31bb98a434c6ed6290d31bd986434c67c6550d31cfd51434c73c5450d31bdd85434c6f46150d319f994434c6de6510d31d7994434c6de6410d31e7990434c75f5410d31d7550434c6dd6210d31f5d84434c6de6110d31f5184434c6dd6010d319f993524c67d64d4931d7d0f524c75c43d49319f983524c67d60d4931af992524c6bd6494931dbd4a524c76d52149319f990524c67d64149319f980524c67d60149319f997424c67d65d09319f197424c73f54d0931cf153424c67e65909319f596424c67c6590931b798e424c6dd6390931dbd4a424c76c5290931bd986424c6f561909319fd95424c67e65509319f195424c73f5450931cf151424c6df6350931b718d424c76f5250931db149424c6f76150931bd185424c67e65109319f594424c67c6510931b798c424c6dd6310931bd984424c6f56110931b7997324c75e65cc931b7993324c6dc64cc931d7953324c75c54cc931d714b324c7d761cc931b7987324c7d461cc931b7583324c6dd638c931dbd4a324c76c528c931bd986324c6f5618c931bdd85324c6f4614c931d7951324c75c544c931f5d85324c6dc614c931f5185324c6d4614c9319f997414c73f54d0531cf153414c6de63d0531b758f414c6f665d0531dd997414c67665d0531ddd53414c7b754d0531dd553414c7b454d0531bd98f414c7d663d0531b598f414c7d563d0531f5d0f414c7d443d0531bd58b414c77752d0531f5ccb414c7d532d0531bd583414c67e6590531b798e414c6dd6390
  | 24 => 0x43cc6de61d0f31b758343cc73e5490f31cf55243cc6ee6290f31bb58a43cc6f66190f31bd58643cc73e5410f31cf55043cc6f66110f31bd58443cc75d6510f31e799043cc75f5410f31e795043cc75d5410f31e755043cc71d5410f31b758843cc6de6110f31f598443cc7d56110f31b758043cc6be64d4b31af59352cc76f5294b319f99252cc67d6494b319f98252cc67d6094b319fd9152cc67c6454b31d7d0d52cc75c4354b319fd8152cc67c6054b31db54852cc67f65d0b319f99742cc67d65d0b31db94b42cc76d52d0b31bd98742cc6f561d0b319fd9642cc67e6590b319f59642cc73e5490b31cf55242cc6de6390b31b758e42cc6f66190b31bd58642cc67f6550b319f59542cc67c6550b31b7d8d42cc6dc6350b319fd9442cc67e6510b319f59442cc73e5410b31cf55042cc6de6310b31b758c42cc76e5210b31db54842cc6f661ccb31bd58732cc75e54ccb31d715332cc6de61ccb31f598732cc7d561ccb31cf95341cc73d54d0731b798f41cc6dd63d0731b798e41cc6dd6390731bb98a41cc6ed6290731cf95141cc73d5450731b7d8d41cc6dc6350731ed50441cc77b50943319f99250cc67d6494331d7d0e50cc75c43943319f98a50cc67d62943319fd9150cc67c64543319fd8950cc67c6254331d7cc950cc6be6414331af59050cc6ee6214331bb58850cc7795014331bb98b548c6ed62d5231d758f548c67e62d5231db98b548c66e62d52319f58b548c76d62d52319b58b548c77661d52319f983548c67d60d5231cfd52548c67e62952319f58a548c67e60952319f582548c73f64552319fd89548c67c6255231dd185548c67f60552319f181548c73d5415231cf990548c75d63152319f988548c67d6215231dd984548c67e60152319f580548c73e54d0e31cf553438c6f661d0e31bd587438c6ee6290e31bb58a438c6f56190e31cf951438c73d5450e31bdd85438c6f46150e31e750c438c6be64d4a31af593528c76f5294a319f992528c67d6494a319f982528c67d6094a319fd91528c67c6454a319fd81528c67c6054a31db548528c67f65d0a319f997428c67d65d0a31b798f428c6dd63d0a31db94b428c76d52d0a319fd96428c67e6590a319f596428c73e5490a31cf552428c6de6390a31b758e428c6f66190a31bd586428c67f6550a319f595428c67c6550a31bdd85428c6f46150a319fd94428c67e6510a319f594428c73e5410a31cf550428c76e5210a31db548428c6f66110a31bd584428c6f6618ca31bd586328c6f565d0631dd597418c77754d0631dd553418c6f663d0631bd58b418c77552d0631bd583418c73e5490631cf552418c6de6390631b758e418c6ee6290631bb58a418c73e5410631cf550418c6de6310631b758c418c6f56510631dd594418c7b66410631ddd50418c7b65410631d
  | 25 => 0x75f5350d41d714d43506f76150d41bd185435067e6510d419f98f525067d63d49419f983525067d60d4941b798e52506dd6394941dbd4a525076d52149419f98c525067d63149419f980525067d6014941b798e42506dd6390941dbd4a425076c5290941bd98642506f56190941bdd8542506f46150941ddd4f415077752d0541bd58341506de6390541b758e41506ee6290541bb58a415079e6390541e758e41507ae6290541eb58a41507b75190541af582415067e63d41419f58f505067e62d41419f58b505077b5094141b7d8d50506dc6354141bbd8950506ec6254141b798c50506dd6314141bb98850506ed6214141de540505067e6314141d798c505065e63141419f58c505075d63141419758c505067e6214141db988505066e62141419f588505076d62141419b58850507774114141d7d4e531067e6294c419f58a53107766194c419f982531067d6094c419fd89531067c6254c419fd81531067c6054c41d754c53106ee6214c41bb58853106fa6014c41be580531075e53d0c41d754f43106f661d0c41bd587431067d6590c41bb98a43106ed6290c41bd586431067f6550c41d794c431075d5310c41e750c43106f66110c41bd584431076f52948419f98e521067d6394841dd986521067e60948419f582521067f63548419f18d521067f60548419f18152106de6314841b758c521076d5214841be98052106f96014841db94b421076d52d0841bd98742106f561d08419f59642106de6390841b758e42106f561908419fd9542106f66110841bd584421075e6394441d758e511076e6294441db58a51106bd6490441cf95241106de6390441b758e41106ee6290441bb58a41106f56490441dd95241107b65490441f598e41106f56390441f558e41106d56390441f998a41106f56290441f958a41106e56290441bd982411067f6550441afd95411073f65504418fd9541106bf6150441cf94541106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441bdd8d41107b64350441ed10d41106f76250441ed90941107b44250441bd181411077b50940419f98e501067d63940419f98a501067d62940419fd8d501067c63540419fd89501067c6254041cfd0550107764154041cf50550107754154041b798c50106dd6314041bb98850106ed6214041de54050106ee62d5331bb58b54cc75e63d53319f98b54cc76e62d53319b98b54cc67d62d5331db58b54cc66d62d5331dd58754cc67e60d53319f58354cc73f54953319f98a54cc67d62953319f98254cc67d6095331cfd9154cc75c63553319fd8954cc67c62553319fd8154cc67c6055331cf55054cc73e6415331d798c54cc67e62153319f58854cc77561153319f98054cc67d6015331b759743cc75d65d0f31d7d5343cc75d54d0f31b758b
  | 26 => 0x1d0b41ded4250d067e63943419f58e50d067e62943419f58a50d067f63543419f18d50d067f62543419f18950d06de6314341b758c50d06ee6214341bb58850d07795014341bb98b53906ed62d4e41d7d4e539067e6294e419f58a539067e6094e419f582539075f6494e41d7d8a539075e6294e41d758a539075c6294e41d7986539075c6194e41d7d82539075e6094e41d7582539075c6094e419fd89539067c6254e419fd81539067c6054e41d7d95539075d6454e41d7d89539075e6254e41d7589539075c6254e41d7985539075c6154e41d7d81539075e6054e41d7581539075c6054e41d754c53906ee6214e41bb588539075e53d0e41d794e439075d5390e41bb98a43906ed6290e41bd98643906f56190e41d794d439075d5350e41bdd8543906f46150e41d754c439079d4310e41b798f52906dd63d4a41d794f529075d53d4a41d794e529075d5394a41dbd4a529067e6394a419f58e529067e6094a419f582529076f5394a41db94e52907ce5394a41d394e529076d5394a41f354e529074d5394a41db14e529076f6494a41dbd8e529076e6394a41db58e529076c6394a41dbd0e529076e4394a41db50e529076c4394a41db186529076f6094a41db982529076d6094a41db182529075e5354a41d754d529067f6354a419f18d529067f6054a419f181529076f6554a41dbd4d529076e5354a41f394d529074e5354a41db54d52907cd5354a41d354d529076c5354a41db591529076f6354a41db98d529076d6354a41db18d529076f4354a41db90d529076d4354a41db10d529076e6154a41db185529076f6054a41db981529076d6054a41db18152906de6314a41b758c529075e5314a41d754c529076d5214a41d794f429075d53d0a41db94b429075e5390a41d754e42906f66190a41bd586429075e53d0641d754f419076e52d0641db54b41906bd65d0641cf597419079e53d0641e754f41907ae52d0641eb54b41906f565d0641dd59741907d653d0641dd54f41907d553d0641d554f41907e652d0641dd54b41907e552d0641d954b41906f560d0641b798f50906dd63d4241d794f509075d53d4241bb98b50906ed62d4241db94b509076d52d4241d794e509075d5394241db94a509076d5294241ded42509067e63942419f58e509067e62942419f58a50907774194241d794d509075d5354241db949509076d52542419fd8d509067c63542419fd89509067c6254241cfd0550906de6314241b758c509075e5314241d754c50906ee6214241bb588509076e5214241db548509077950142419f98b535067d62d4d419f983535067d60d4d41d7d4e53506ee6294d41bb58a535075d5314d419f988535067d6214d419f980535067d6014d419f997435075f5390d41d714e43506ee6290d41bb58a43506f66190d41bd5864350
  | 27 => 0x43bb58b5190f7751946439f98a5190e7d62946439f9825190e7d6094643edd0e5190fd74394643ddd4a5190f765294643f994a5190f665294643ddd925190f746394643ddd0e5190f776294643dd98a5190f756294643dd18a5190f776094643dd9825190f756094643dd1825190f6e5254643d7d0d5190e7f62546439f1895190e7f60546439f1815190f776554643edd0d5190fd74354643ddd495190f765254643f99495190f665254643dd5495190fe55254643d95495190f756454643dd98d5190f774354643d5d0d5190f776254643dd9895190f756254643dd1895190f776054643dd9815190f756054643dd1815190eee6214643bb5885190f6e5214643db5485190f755114643bd9875090ef561d4243dd9475090f7551d4243dd9465090f755194243ded425090f5f43942439f9865090e7d6194243dd9455090f755154243cfd0d5090e7f61542439f1855090ef66114243bd5845090f765114243dd5445090f795014243b75834350ef66190d43bd5864350f9f5390d43ed9864350fb56190d43af5824350f5f43d45439f98b5150e7d62d45439f9835150e7d60d4543bb98a5150eed6294543ddd465150f7551145439f9885150e7d62145439f9805150e7d60145439f9875050e7d61d4143ded425050ef76154143bd1855050ef66114143bd5845050f795014143d7d0c5050e7e6114143dd9845050e7661141439f5845050f7561141439d5845050f766194c43dd5865310ebd6490c43cf9524310ef66190c43bd5864310edd6490c43d79524310f9e5490c43f59864310edd6190c43f55864310ed56190c43b79824310e7f6550c43afd954310f3f6550c438fd954310ebf6350c43cf94d4310edf6550c43d7d954310e5f6550c43b7d914310f9f6450c43d79514310f9e5450c43b7d854310edc6050c43ddd465110e7e62944439f58a5110e7e60944439f5825110e7f62544439f1895110e7f60544439f1815110eee6214443bb5885110f755114443be9805110ef96014443ded425010e7e61940439f5865010f3f4354043d790d5010f3d4354043d750d5010e7f61540439f1855010ef66114043bd5845010f795014043bb98b53d06ed62d4f41d7d4e53d06ee6294f41bb58a53d067e6294f41db98a53d066e6294f419f58a53d076d6294f419b58a53d07756194f419f98253d067d6094f419fd8953d067c6254f419fd8153d067c6054f41d754c53d075e53d0f41d754f43d06f661d0f41bd58743d06ee6290f41bb58a43d06f66190f41d794c43d075d5310f41bd98443d06f56110f41b798f52d06dd63d4b41b798e52d06dd6394b41dbd4a52d067e6394b41d798e52d065e6394b419f58e52d075d6394b419758e52d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d076d5214b41bd98742d06f56
  | 28 => 0xe0004000000c000001c004001000300000000000000000400200080010004004002400a0008000000800e0000000000000a0000000000c0020000008000800100000000020012000400000a800300000020058000000c005002c00000040000024022000401b00040030008003001400d000000100140090000008002800e000000800080000000019000000f000001900dc01300840000000000001800000000040000000000000400000080008017001c0000014005000800e0088008000802a00000000008000000c000006c00000040060010000000c00000040020048000005c000002400b0014005001c00b000000100400010000003000400200040010000002007000b000c003003c0000094000000401200000020000016006c0070004004000800400000030018017000401000d0008001c005004000900140070010009002c017000c0110008005000800000000010004000000000e0000000000c00300000000008001000c005001c000000000900080050000001008400000280170000008000c000005400e0018000000000f000400600000000000000001c002001000000040010030001001400e0000000000000400080050000000000000a00000080038023000c016000000c0004002001800300440000048006008c00b0054006003800000100040018010001c012001c00f0014000001c0030000004000400f00000020008003000c00300100080000002000c0000020001001c005000800000000160000001000c002000c0010014002001400c000000b000000300300010004001002c000001400100dc0000020005002800400000030004003001c002002c0080004000000c000000000100000000004005001000600000040000000000001b000c007002000000040020004002002400400180000000008000c002000000e0000000000000c000000c00040010028004005c02f000400b00180030020003001000d002c0000010000003c00a00a00000004005003000d001000200080000008001000c00100080000000017007c00f0014003000002a000c001000400e00500040048001000800a000c01400200160008004001400a00340130000007008c000000400a0014001004c0000034026001800e00200000004002000000000000010040000000400100340010014005004000000040020004001000401500040040000009bb98b51d0eed62d4743bb98a51d0eed6294743ddd4651d0e7e6294743db98a51d0e6e62947439f58a51d0f6d62947439b58a51d0e7e60947439f58251d0e7f62547439f18951d0e7f60547439f18151d0f755114743ded4250d0e7e61943439f58650d0e7f61543439f18550d0ef66114343bd58450d0f795014343af5974390f3d65d0e43b75974390f5d65d0e43b75834390eee62d46
  | 29 => 0x54000000c008001400000040000004006000002f000800d000c0020000001000000000000000000000001800200080000064002000c002004c002001401100000000004004000c00500000020028001001400d000400100140010004005000800500040090068002004400b000000000800010004002004c000000400500000000000002000400300b80030038002004c004002c00d00140020044001000c00000000230088002001c00700000000010004000000900b40090008000009c00800000000008000000000000000000050000001800600140000024002009c00c0000001000804d001c003000800f000000000000000004000007400200100060024002001000a0000000000c00000080000000003003c0090000003003400700100000020006001800200240090008001007c0010090000000800c0000003000000d0018001000c003000000500040040000000000400b000800a0014002004c0000004009000000300200010000001000000300140080000024000c0000038008000400000100120004004003c0060014002000400300180090020000004800b0014004001400000cc008003400b0024002000c0000008000001c00000280000030000000001400000070004015000400000200000000000000000000040030008006000c000002800000040110004000000400e00000010000001000800800040060008001000000300780020000002000c00000040010000000004800a005800300040060000000000400900080090010002000400600040000004009003c0060038005002c003000c00200100140000000000000800000020048000000000000040080000007000800100000070010000000c00c0044009001c00200100060004000001000600240050040006000c00100040000018003000000000000080000003006400c00000010014011000c00b000801d00080100004012000c003000c0010010011000c00600800050000000002401100100000000000000000f003c000000400000200040010004000c000001000900000030000009000000b00440090074001001c006002000100000030000003000000100000000014005000400200c0000000000f000c001000c000004c0020000029000000000440040028001004c001002802a00280050000000000004a001c00000000000004001000400f00340010130000001c001000001a00000020020000002000300000030024000000c000000000b00040020000007003401a0000003000c00d00340090010003000400000040090000000001400100040010008000000004f0004014000001000000110000004000c00000040000000007005c00100780360000000004800600000040008007000000200180020004000006c00b000800f0000002002c0030020
  | 30 => 0x8006003400500140000018002000401300240000014001005c00b00040040000003001c00c001800100380190000000000000a000800000000100068000002c0010000005001000e002401b00040040018000000400000000020000008001000100000050024000000000a00040000008001000400e00140160000000000000300bc002000c001001c0250014006001000000280010030001001c004000000200480000004000005c000000401b0000002001000000400000000003000c003001c00500780080034000002400200140030004000000000000bc0da000000300100010000021003000c0050001002c0000000000000c00100140050040005000000200080020000001000400e000c00000480040004006000000200000090044022000800f002400f001400b0004000009800b001400c004c007000001700240000000011004c002000000900000090000000000c000001c004005400400040000000003000400400080060028001000c0020000005005c00000000010010015000c008001800300000000004014007c0020004007000c005000000100000030014000000000f0030000000001800000160018000003800900000000000000003c00d002c004000001400100040000002001400a0000001000400000000260038005000000e00480020000001000400400840030024003000400700000060048004000400d00080010008003000000400000010000004001000000400000024001000403000040120044000000400000000000000001000400200040030088007000000c00000080034009000c0000008000003802a00040070034002006c000000001c00600020078001000000d00200200004008001800b004c002000000f000000300400060014007002000c001403f001800b0008000000c001002800200180000060000000000000040020004002000c00a000800100140020058001000001400340080028000001c001000c003001400000000050020002000c0060008015002800b00100000000000000400b0018001003c00200100000008001002000500a8000000000200040020024000006c0000030000003400f00000040010003000400600000010004000001000300040000008001000800500240020008007001c0000040001001c01a000400e0010005001000b00080050004000000c000001c00400000080044023001c0060040000003801b000800000080010044000000c00000000180000002003400100080150004003001400000000010044000001800b001001f0000000005c001005400200080110050011003800300240050004001000000800040020020000000401e00040020000000000c0140000001003c001000800000040030000002000000000000050000001001000000000010010002
  | 31 => 0x84005000c001004c05f000400600000020000001006c00a001800a000800400380030014005002c008000c00000580000034001000000c0008033000800000080010004000003400d0004000002000000b400700340330008000000000c000c0000010006001000200480030000006000000e00040000008002000c004001c005000000400000040000001000800000280070000008000000b00a401100040080000002000000000000030000007000000600100020014026000002a000002400000020000000003c0070004000000000000100180000006001400f000801e00000050004028000c00e00000000004003000c0000004001000000e003801100040090000003000000a003000900200010004001000000000000300004011000800200a0002005000500100010000005000000900180000070001006c0080008003002400100000030000000003c00600180060004003000000d003c004000c002000400000200090000006000000a001000300140000004006000800000000010010000000c01500000110004000000001a0024003000000b0004002000800200000010000003000000a000400d00000000008003002c00000600000038000001400000240060010019003c00b000c00000040000000001001000200400000028009001c011002c00200080000010008000000300000010000002000c000000c002000000e000c010000000700440010018005003400e002c00200140050008010000000400340000004001000c017000000700040000008015000400f0020001000000c002c003000c02100080000010002000000100000060034011009800200000000028000001800000000000040000000c000004800000080130058000005c021005000100180030004005000800c000c0010020000000c00000140060004005005800200000180004002000800400040170030000000000600440000008001000c00a0008002006c007001c00200000000004008000c001001002900280060008001000400400080050008000000800e000000c00080040000005001c00000480000000004008000200000070010007000400000000050000005001800000000000014003001c011000400000200010010004002c009000800000040080040021015c00000000000010000000801c00e4002003c00000000020010005000000100040080028007000800e004c001001c00100000020000000003802b0000016000c007000c0020000000000400e000400200280070000003003000a00c4030005000000000090030008000c004001400100100020008000001400100000010028000000c00200c4015002400000040040020001005000a002800000a00040008006001000600000010000004004c0040004009000001a0070003002
  | 32 => 0x5b1219c5859e450000e86000000080a29ebb97ad681ba15b400000007ef9a0c4678000496965000000001db0cb2030298602f009e1548000220c000000129d000000000000000000000000223e0002719303a926ac128bb0c200002ab8d960000e8848983520000874000086c000111749926d8a318000b8d044058006daa6b80005e31bde32a1ad95349b216ac8d4e0000000000257898504620002a5200000005d9640a00000000000a84ae51e200002adc00000008b211ab92f400064f8006028000000000007660000463800057c00003c299129c3c00000000006178eee00014344abc00087980004112df24bf80e248b801682f124200023f005e1e6d7da93bc66225b6070a2309e300ce260800084f67430e18f90a129c1d71e13343f12cb4a3f19cc0fe05d2b19eec27841cac44312c11a614d84709ffc8a014fe00019e22f2967d8041f52a0f201e74a80002ee8b3300022bab111b47b43800082200009fb81be923866000008f039b10366999aab4ff8000aad96dbba9ee49007a2629f40dbe7f6e51e29dd4828248c96b1323565d10ed000027d40000bc477680006552002ade951846e278230a1e9398c0bdc1342a17b8f9c8016f80006cee516069ad9a7de13ba42f606b35bae1c0d51e6e1271d4404a9e9a14a082d21285246ba8c4e0a1894c78e99b47684f6e408da5a28dadf19f60a1c8ef000068452a495180005041b668a40000000046a08f1d1e6ec263a3fc8b442a514f8714800053f673665300003be800040f296e43b574c944dcfc26e8f1a79861be2368184003001400000010000000003c0160000016000000100000000010005000c00300180050000001001000000280030014001002c0010054005000000b000800d00000130010000002c000004800000200000008005004000000180080004008002c0000000001000c01e000000100040010144002007c0000000001000000100540000044014001800500540210004000000c000001002300000050014000005c00a00000000048000001c016000000b00280030014005001c00200500000000013000000e00340070004000005000b000c00e001000000040020048000000000000080050014000000000d0000000008800200080000018000001c000001400600140000010001001c00200040000034000001400700080000004043000c002000400200180000018005000800600180070014000000c0000054007004c00b0008000007801e0000000001802200080000018007000001b002401700040050044001001000d00200060000000000001f0034003000c0070024001004c001000401600040060024020000c00d0090008003c009002c0040008000000c001001800000000020000005000000000080010010004000000000200000000005002c00
  | 33 => 0x3b380d35dc12a01dbc04a8450b24a53800000009f2000188800016cc113262676f80000000d9046bdd68000259a6ab55c8bb84e4473a62e10000000480000000000001be500c6ba00007c3a21300015e255f81e06a200006f687ac09b11b0221d84671caee800000008b880000000eea0002c9253b2552221ae6e79096e300006ea648956e00005d6000047400005a08649dae6c08f26242800028980003d1923431c859eae6c00000016060da80000000d9266194e1542ad32a738000a51800060b0000000136e0002b600002f2c85400006278bff307a8ca4980dfc862125d746212a175015673c987186f27f8b2b95de935c5427a2050c0bd800067eacaa8d8000000027464d0800099c20200c515ea0002eae80e2c1e0000000ba2c00088da0f814100000000000000000000021b30000d6000000000000f1c0000000ba1cd3400b00005c4269637622f91f68b3a5889d9c6d2977f000000069b0d3a33e108f5b7a3c40002d060c480001a2133650a00000002df0a8c124fa87000000000003c0a7318e7886300010760002d2a000181847a8000000192a34d400000000000000c6a43b18ae000176f5e914e00002c0c00029c80d20d3b9ec8000000209f0000000000000048606e5367880e02295f20001904309aad6ac74406ac49d4a5f39b16300d81e9cf85cdbce000019a884e9792dab6748adca14ae93082070604e0000217892e0001bf149a0e3d6335be464e44080aa80000002ed3319000093f233293389c21d1220c6a3819a000000011a2526810d4c43bb6bd47369cb249340000002d40000137296c800062d0000ab7ac242078000866800068689720000000000000000000000000000000104e4ab800087dcfea7b45354000044490bdfae16b8000b808000000000000000000be2dca1f09aa40000000000260ea2f9e47bd580004a8c0000000af469f23eead58342000000000006cd0d8836daa10eac3bb05ea00028f3000208c00008e84c4da740001f220ea80007ee06569eaaafc00010e43b71320000144332aad160000000b79539304b00007b4828841916b85d98e72b39a6c6949014b0000b28baa09948822dce6790000000000082040001fa800001c80000001d5a9e79a0e8efa4b28e5026619d000039724a43470e21b019b4cb56849e57b800013f9bce0002d1200010cc9daaac61af226625480b14f903932c0a788bb00e826f98c0642590b26ac0b0033254ee6d15c206fa80009b01c36b909a6a0000f86b6513da3f90b92000248c31e212625e9c7006e18ad00029b15f126bc8b15a38000066661aa4085e1963e8fc8aee689e10b1d20c62b3807e41f3a7256d0106a5be033804780007a7d433000000066da6f108823f80269f366a4eea1780a0820f1052a72d20ee51580000542dd65b8800038727b76d62a1b00
  | 34 => 0x978000000000000019c24d301648d2aa3800017e669c2b0604cd61c0000000b1b00005ba65880001112000271b80880006dfec36000106806ac1c61c4286a0d690844a6eb1644280003cd0ff4000000083629ba83297eb000131a0e88ea200008a636d000000000000002a8a00005dc000000000000003eec00000000000000f840000fe00000f8e00026400000c0406400000002b4456500005430a8daf3ee2a6a110405a4a9927a500005ed000025500000002f5ea2f0b4c00010ce5af5c8a6ee5ec06700b635a5c000a71000001680009cdd79788aaadaac28e70459266093dca1894185da1561d1c7c20bde0000000620c00004709d2528ddb2a190e7b0000bee00008d972f4db82214000345175000014120000ac6bd2000000006e60000000280251f469ee14bce92c8b2780004fc15fe2161a1817e8f3e0ca0ad839f9ff67b90000000008600004d62021da49440c34a818e52000000071e80002f2d010a6f2085739c00015f802a48f585d4e50301159800032800000dea9a8000000000000000000eb09e8548c630daf47922bca02dc94e8ba02c2b2580000002eb3000211032380004b700fd00019ae5992af00001a295a500002d71bb481edccd94f24be476800020b9e370000000000136300008b2164a9cc4e71a9500015ce8e32e702f5adc2000064e01f94cc95a93187aa52cc00008e27e50000616177cb3580008938f930000000b68925800028e2000000000012372f51d6000000000000000000030a09040003ef850600000003f280007848000819c7e800010be0001593000265a000000087d99a5b8d60999909ae60002e5100000000002f5c82e8e0012d80002af2a2800023f419b8da80a7059a0c99acc49bd90a0f687d269561b000027180bd2c184e45ac10f090bb896a06a506c93a0000e0600000003a3c8c85e28e223a7099cb13828c0732f08a46a9fa16d868982e2c8c93c01a250917b8a48000038ec00073b98620000000503818067f16012a9000000000002b58ad238b05e20001a06a1d1970000266a24c0c5c5ec40003cb0e98b328219a36086e86fd5615e409be000153e0188e0200019330000ff0428d50e1fb039200010a4a5300000000cdc4410488b3a800067401c0649dec406723200002c64000145c6c8ccfa00007fe1780bcd95e9dd22db2882ab100009eb00003b480005f686ca05fae406d6a532079000090b9a50677dcc45f80dec639a458b480f8822d8cc80001190086a4eb9a4195e7d28b9c08d00008a91e2d54800000002c7800007580002b4c3d0118d0001614764c00033b22c18c3aa0e000000086a00004529490b7e16bb7440e1226920c642625706381c8400024b800023a8108a058acf000024a20a399e447000000005c3ae624ae6cfa207266800014a04a6876963c0e550299ee3b6f80
  | 35 => 0x7ca800095880000001822b2400000db25b8ac398fb78e2340617e0aa45d0f4a3d917c8aa4a5ee15182ea89b9f8a474a53a4b627f09772194bbe04b884f0b4983403dc21e5e62a548e8154d9bf66b5e61835896286cb2de100010756c31fb01b526b2000291498aa9906b10d5e695c000000000055ac6fc96c2c12687800082c06a489e00000d32042000000022c000000014e60002bbc863961000000000250000940032d8bd11670000baa0001a8a0002384557c7928f61ea08f2294004f28568f58aaa3f00bc6b67271283888b801900003620000a6a8000b0c000098580000000a3c000116e00026026c6800003e8f242dcd3b47132b385d204781298b649f31dba55e427c6652d841abce2a37c1322a6bc78626281cb9e356cb997932cb77eaaa6cf192d34c41da55127df7eb2794b2f163c81ceca60000000678c0000002c699d5800000022265fe18e8b32299a0002985aef9aba2471eab695aaa62711f9e4d119a68fe88368d302d044f87c61861ed74509bf34152222448a26412b80d2251c08851b2f418b31c4a8f78b667fe800000000007322f18a5aabea2b921de5491370ae88a32ba5841a7091d7441b290c00013407e8400092d0d2700009caba629368478820a2b404cb8dcc3a00015d20fa000000000003d3a12c45d41240a019375b352b0a0819986c3ae685120ec910c2b485d620e4aed1e80a2c4f76257a84c1f8d864ab314f4b1706cc954258a663800054f44841cd92ee80f93a424780000001b5c967d7f06b1ab1e01616c62659232000000000027ae8c5087a7b61f3f0000ade9879e504b3a20482691275f54000446660d4199d262968ba600020556538b8c669235ebbf80000be80001339a86ae025d240c16ee2151c340000000a2d00009fc9b0a3688d824502ef27c5000000022da0000000051000000000001c49c1a0f780000cc2afa62152a17ad0000296c0000000000000000000007a214e00000000000000097c00013fa00000000000b575628000a3040000002e9c000000000000000001d8eaba94356510000000237c69016e58751edf5a61c8d0a3c00077800009d3952aae900008c06c70aac800049f0fa60000000b97d4640000f306af000026a08280c3158002d400078bc000625e9e6000061c000000083000000002a7809da4608400fc27062822885cc8600000001f8130863147630000d5643880003b19574000000000000001d2aa9e2524edd0d29e6f31c00000001a2b5ac943c645ad7c2ba14c6baecb9fa7b2b5e5c99608927ab1f5ad89e8343a29ca7faae3785800000000006a5e878a7f1a3eb91e1a2b6ba5119c519ce00021f43c4adad88d25a104e965c8ff86a0121580336c9dee28b00000001d8c3fe8d8a71d940abd9983505a25369b6ab500001de689d400031d8e9a000046e5
  | 36 => 0x2de89cba742000024e284571491a1f213e69b353fb272733c273a7aee2f6647ca6656e9947071212bbcd10c03f30000a478dda6aa00007360b2c1dd84fb00d0c480000000bcf9f800000000818ee8a32fc00007e06be6470000000051689a840e00020940b8839e642082a194aefc68b92e060c2e9985014880000daa33f80002b09d0c000000040a88a12e1800051e53c89522c0400013fb8e5800078610aaa5f219861809dc00000000000a9e67a169c32ea2693700fdb5728e23a645d481bb8e08682800033de4443771fef00028f42f6000000018d68f99368689297064d08a58d89af519f97a887f90948748d7a6521ff111f039a98c810c00010a57e3a26c6c2145a7a25ac94012e7e9ab078c30303fa7aeae922fcc00043c0696ae782790000cd800000002b1c00000011520001b441380000134ec54ab8189cb4411087f50000bb4858612faac20f892bab939af63af044600000007ae6f0b9f1930c2cc643abaf40000b3800000000000000000842a4661282f64471d04c1011bb600023b00001d970002a9056a8000aae00000000000000000000000000001ce22641f7c0002d094b4915125800000000000939133c8c7215609c91d6a2209147bd03400000a865d89f5e4985328457940c8ade8e6ba5c06600005c4b9580006668b90b05000071b9cc6000251422900006b8d10e25e40003ec672600499c68c30000243c0de5ae89ac0f18b346fb8a3a82595424575f4e9e9800034dc00000001940421d168058a4890fad866c801dc697900e56a00004b189f68a5538a6964faa67b800048e986600000000002e58370800061486827e36bd153697bc00004260001c5e0000a0e75e40009feacda70b1e73057011412c1087000098545e800024ccb5864fe24f46186b27009c8287180000e580006e784860001e5a23853a03752a725b603ce00012bc2ab12f800009a6a6a5b892fc186800028c0000032a90e13b62aa6ba56e60ebe4a50000a0f8000000180d5e38e3500014de0dc804e94f98e54569a9b76a2a206d18a762cd6aa27ed2d4a2ff8018bb41c5a19e80000000000b9aa988000025f70a88f8b5d0beb000051b9398000851a066142c00067961e80000ba22c32ea039d17ee00b82cb7099f2c2a39a582a6a6a0a55887e2d4825837e970600005a600027a300000009a20000af31b437f79b3a00000000002cfc0002e8501d83182131cec4850bbc435a4f5363158d000000040852520df400095c80004119a651ab27728fd83bd000000036c0d9c0000bf6000122061310140000000000000000015dc155000000000009d3496400018b28da8000ae399d823a57c501b800035f180c3b7a534b8e01f759d268c00028ae315299e0c79cb61031e328c7573e6301ece4b4014600020831aa029490421816d4800000000000000
  | 37 => 0x2b309fd038a6dd2b0c0ec228a02fae3397013006abcc1c7a28bad2f9c3824ff47f29ba19693a91bca00000007a14000230a5da730800000000006b4c00000010f894b80000001a2561ca3cea26c77000000007fa8c849df0000056a35230091c8a6c90320001ad40001d5006180007db0bd159e925454edc9392093eaac72ab46a461d8ad393ca0000b5448e411100004a800000004fc8af600000008a10f70000000000010a2000000000000009632a489b84000a6b0acf000093122ba3197b300005865e22ba88c820001d0400008ea937921e52ba4400001b22000000046dc0000bc957f0001fce0001e44000102c54a0aab3319ed33722ef0ad913c66ea1a8176061580810c24528800023c896b0000000920055639f1a340001736659c00068c000055be9d87ef0040000036f00024f4000000000000f157fc0009c311370d91ffe000267c000077300000004af80003a322aea52000000000004ad8000000000000010739b580009f01e64000000000000004c9a4722184000000235469ae50e8cb9da39cac0003de00000002c743f62c405164c564a5aabe0002a6200013a6000216800021129739c586101b377fd0000458677630222029802d362d5a81e00017a9000150400018a2124000040d000027f23aeb8280f057022488bf93c4af70f0c92ba66249f972d7ac571666497ae06b82ec29898989ea29e0a2592829bd213e1dfdf602122b32152889534c109c0002c0014613620c108fe4c7c00061e6072aba40cc1b792ec2b418da0002f1527f8000ae8505b74b97d23fd99e0946c000000227c569155a91f9794a5b107e0000000b5380c17ac868463d84007140000b7423a0b5e60ea8dd21600000ace000000080e622b374204a5e124ac6529b7d3c624a60ee1374abd1be800000006482780488ac8e0000752afe2196339001ab1e9acb074adb81b566b3a42850a42b9e346298000000125cb0b29531d505968356ec41f2000080711b2a7900005db183244d0934915144d3f68000000010f2fec000000172b93600003270000a828ed585fa2c30000ac03c7a9e8000152e000000074ca06d4bc0f36ae1138e82b07a8b6c28da2110ca28af24ba1c8570d21948d2b5181ba3db0f5e0002d6675a90ea92896c7387c5f81a889e6798163000008967b2acec6a8045472a188653fc000aec00009bf188978d40007bfc0fe1402add7ea2021b99124836987ba0b001f36319f060000000bce4f99b7ba7cea0e0000444265db271b8e00f1ff05c3ca1667c827e4bc8590a274efc3c8a6d41dd1e2c2992a649822aee283057aaf1a6fa00000005b4142e00021c415c2b6228e0510b4b984774098bd0000000b5c060442d45fca6840ee21e024c4266eb12df1484302a88651ec6401bc94bc8ff19900ab9a264a3087639a190c0729180000095d
  | 38 => 0x7a4a06c8aca540000218400019dd6928814225da4c693a00e00009f90001250939d2da5d72cc0ad68d161c001a810ca0f46f182b06151ee60f59a20193ed54a69e9f32a20e5ea969458a7500008c89c6c57e874961285f2adf02d8ab6ca4c42251a33782503513ada6b488e845a40000abb1cd09cc987eaf9952c98b15ae2ed2a0c33edf676eddce4685137886996262d01a3a25b8ab67500ed77248ac396408d400009da08596042f6961512f005e8e3815253e9d77af916369e18f82826d7fc6bf5749b7686688e92b7051b567e0682026767479946a1b4900000000001639a2421b242d93985fb295c5bd84a2ada83ee36189b6a0ba8467a04e30208531424b107b0bd472319e29cbabc8e733bd09d49bf4100a5e1cf000704efa7729b67b1464233b5977b3429027e8a0a65a29f9a0000cd679e0f5681886cb3b153774328000392142603996e659a2e008952ce22758244af0800026c0d9800002ff82c9a04b58a5ea0f22bf669da7b89481048792d20a1c2886816e0e3478500000002f068706e1340a05b09730bfa94c40002bc80007f02c385d5c0005539df63b813ac66f8840147062a00006f050e0000000281a61d50a8392c00039ea41400000000000000af0053c0000000011a56e7b71759000207882820c20000d9458d5ef857607800002bfa00023b66374000b5800002148de83ee5b76088a40c61c0000524a8a615808843ff1e639d880baba3096c65d47dc1d4dadd0001359ab51ec607e8000000000061d00bb0000000538c4141de8ccc000118f000000077e000022f2a6a0b9074e000156c2ad014c00021e486ea80c0001a42af49bd95d691f263e4000a55270212080008456d00b5c8000471400018380009309e6a00000000001fa30002d8a63cacbe4e0d159822ac222e3a75400012d600025bc473df7234200002381fe033e6c7c113a2ca469587c2c7090938ca9124a628e84a7a12e2ab5a120af2edfb071cfa735172756dab3471121a40bb941c9c8ee46ba6ca542fd5f4c2ac86d856f4d3627c1c2eba524d57730c105ffc16f634ae546bec8325e65b25a90a57c9c1430300019847cc1f347ba8c9ab5709c65fcd7e722391b98f1810660c4a128c7d11cae9a318538854c71d19461348d24b8b1f200ed1c0a2a6ca0a558a54a2e340000002938b42ecd20b49b3f69e000069b527a32326c264a072f2240000464959026487ca34e24d427300d60d1000a7108a7a60916bc030e9b53bc0000a690bc8bbb800002016340000000b16a8b000000000002d4c158a0762c58c600001e460001b143fee3c026c935d000050e04d000048fc52c7e22f17a7c84e461cc00018b981f7952d56347ec666e8e8a8028a4a0a020961a768a04590a6ba1d8a58413e00000001696843d6575abee76507ae163ae8000a0086640001676172
  | 39 => 0x26128adca98b0000c0f75727a40000b391b81a5c0002b981a521fc00000003d7207c000000000014e7841800000000007c12a6800000007af800000028927c29e7923700000002293250845e6378000bcf1c4600014e4b7d26a2848065c00000007be9d080a7ac6a6058000000016284200008d380001821f6696084607ab4a74bb968b3000000000000008ce04b2000071e5f09d5664c0000ae09ed95bac00012514be0001b821f7deb843f8000843800000000000000000baaae483b627527a415721d0c0004ba00007ec80007695f7e6a1e7c2abb6b46000000018980000001191000000000023706f820366d0923843502be93e817583758a412eacb278c4d0f6be930b466aaa45d8c00029ba1612db8d6a000107cb4314a434b88caba9021c55752f17244f9200012c2000230800016a6aee8f284a3e83200010b86670000ac1e5185ee5f0d43da575000045098e0000b719dd0bd49c941b6421899ec8384df9bd8850a2207c6282cb54129f0ab1c14366a1725021bf276580002201210b2e000000021078f724f8000000000000000001078768003a00000002ef83e0195133d2ac20cb3d6a46e08d80000001dd4b3a2d887bf58090002c081bb159b42dc00062fa8d6842593c8194000000000057a0ed90001dc446c58ea76200000a8190e0000000a2d63060001bf097d065a7e9800076f20dc2e91bf470deed615d22520000a92000055e3fb8ae2000000002a196075781ee000289c00000000000dac4108000956a1f20000000aa0800000019b1000010285680002540000000000044017c0131836e00001884c480000000000000000000000000000e3c000000077c0000000076d00029b09430d7606d1e9c3454000000145043240003179380a1400000000644000212400000b92304d6400020bb4b29cf3a7011f85758000b8e97c1442e0fa1591b80601232a0000e6925b6ebe0000580241959950bee8443b81a47e40800995173aace889c0000000000184d2821184000000000013588c0800018184fc83ca88a6a16f1e7a9242a1c9494099b1eaf5d2a45000000004269a532a31299770130a000236668b19a2000221e8e8a3dab3caa1a3b223463f215061fb91a0555813207f1570008227ab8a0ac1887041e1ec29300000c6e0001486af6000071a80001351612b9100002dd00000002a9602381910000000000051e000026e0002d820000c003f988cf281a50a00026cc00014d41c545d00000dc60000aa2a201da6000000006f400048680c4bb558c10001d922ce000012480000001a4178d86dc33522db74f2f4054219005130dca1ee225c49c11e046b241636b95680001e967bc25acb6da798bc6e50425685406f100000000000868000059aa2b83749d94956000063b21ea00005ce00000007a12ca0252a20e22f55589a60e1
  | 40 => 0x8030000000000011ea566b68079b13200000001a633f180009190d0412640008931e6b7a2ca6d03c9e3e00020797af074b0002b965f840001941850396c0005928000000000028b9d3e6759e0417b00005f600009ece77d8848c8a0d45a4625aa77a59b29f8000193abd80834000290497eae86169063e00028ff401800000029b400000001ae00009a24900000012e00000007dc028aa950000512c55a0eea00a070c00000000005542a2cb260fb400009049b140002e211705c2a4ee33aa4e029280000f5061401091dc0000226000242d00002303c5ae0600028d463b9f6212a8b3d2d80bcfaf88e9ebb9a1aa62299a83b8a1f85b096fe17c0c920e711f6bc72e313e56b2600000000000c740000e4277c8000000274000024360002c2a7e8117e5f3583654595e47dd821bb1580e009a10df75b295a4822256b5b08aca5888756fb2350bd606861b7512c5a8184488e0000b512b2c8379b8852e17809ae033a96b800050a80001538da4672a814688a6f3346147abb91126768928e20fa45618e274896a81a9679a5ca0000ea6373800018d9a45000182a0000a7ebc30000a2b1b7cb6f00009a51ad08e2000094700009219474000088242200008d6a006b20d6582842ccc8bc0d1954e241292ed39a6a8995d715a37e6712f325e848d838fa8aa99da0ce93304360b99e4e7b3d7d674a0970665ae2ea3915765ec82b200012acbb9ce56797603000000005db5742b6b27a9110ac6014d25fc5e800001fe109d0001cb8437800008285769bb2de47020fe290c28d130e1fc26786dd89cc22064bd9fb633a0b5e6121f9224c96ad3792e806d9dc16a57800067e6e8871a035c815c00029582747f327da4fe400041bc000621c0003e303a47c00000629e1742d3817a9c89a44a848000ba400008828000000000000000009388000000000073e064d17a22dc5521ba4586825a5de000060fd14c00010a6663202a5c00d260584a8344b88e61f7a2ce656c177000181c5958b3c0c6800000004f19b2a8eca340f320000000bcda13800000005c2183e000000000000006bf00001622d7a0002dfa000117f5752b58b0f107a00025020000cca7994000bac27871cc00004f318c70000000000000000000001e50afe83940000000a3077e873f32d806cb59298247c000000012b40e45a1c2b28ea86de818a9c4400005542a4833dbc5023151700020520002c02718a2cb168a45e46f0bb89890f3a3ce0fdc89d8f7a66e80000000cfc2dc01f102ce3984da86280001ae23ebe86667215bc4a067b0000124c650a0df08016ed00018260000000000057b0001bcb6e9614c080800008922a6505a3d238e072000028d245119ea52b064c4734dee71380006c153e29a007a6453c9382b45286884067c86016fc618663c0000e2e00027210001682000000002
  | 41 => 0x44dc3835299f08f3298a451958e55d68dc00004f005a80001f503550002d6a00016d9bad91029de115771820a10d783ae72a925e00000000000000bd89f3a67ee91600000000000bc20001fe2560a0a8ad4871885cc3a6000000000000003898000891a0d4000255c75a6442356a056955aa1fa9ba05445e0b675b9e13208ea8f8240a6ff79a0a5e7346ac04f829899ac27e88722288045a71c45acb9e87e89d0b6c84fa23f06f48be25f86ef9ab68a51e709f9870e6bb9b244a219ec5a30f5000013960000ae6067878262f0ff844f5c351701062a03a2e0bac863c6cf89de481e5646a41d8a000240678900ac85ba250ab7e68e6f5167c63214c08cf2e7800000005a1980191f0dc44e3e87e39900003ef2ef46cd109e13280f62c7989a0dd22585d4800048a924aab8950260ce75a99110f41d69be2bcf400000025250000090b3da10c00025a200000000000cae00000004baa08f000115c6d391283e90000974da0862a0cf53c10e8a16622d34cc205a1ac022cbd1842800000b03838860112862201e1b9a3131f5489c1ae4aa82a327c5ac42a11017cb788eae8f900006afdac07f48a580002c867d208df0001cbe59c0f6863e07663419e7eaa702de5e540002521968245a1b1294a8c2227db0b4652a7a3a25ad84ca9e2b8f28b5aa2c9e668eb0c2e382800000001f4000187da7fc27052c17acb3e130d8902e720f286c8bbadaef20b00000c80fa000000002a5e2e42902a600a5a41a31003668b7dba778f22ec0000871344de0a0000b1400028a0000136c8af8000761000000000000001e1ca3e8000000267a000000026d00007e080009a7800092c145f000000000025e000011694e2091857080003fa0cbe000288e0002d4200000004082806000000010b8d0a6ae135a3968b9615115f6b5b85ee596a69c4d1819286d09b8056211a2cba0b456447344bd00006408000259676e4e796a4000000090901b69ad58176aa868e87720645c0a6fe574122c0384000582a9ca0fc59aa82748b10000862000000003400009998b12000230a5b80000000000055494dc0000d521ad0000ae7e92a90980000ae000000000008e08000000133e000097815a107010d192e0c59d8226100000000532541400000000000002ae7a47000063901b97af4d5493422a22fa9e7a00026c4b8c87260b10e7f6cda51200012845c116467f58b0a377800048d979a948a214691c000171800000010c7ab482387b40000ae4a898455110900000008ea8b7e37d94c82a9c1e62061fdd5e8972c68ca3580001ada46f8ac4ac6953a154157852c86d27a8ae20416400059ca8c474c000000014ba8628fd0982a6c880e93db00014526b389ee8c585367538bd7988ab8c4a011660000cb89b81b9402a8f082af800092a878e0e040007936747056c000b08000000000
  | 42 => 0x3f0000000000029f0000046489ac000b1958aa9e96cac05226f8ac4c0008ad071640464e513128042a6093e823a2d0034646246cccc2813000000005ca00000004fd20906ce5ec7b0400000000000a440000222800052d000041c6950501800044d80000000000680800032d000000000005f0c000000172092f0e54000285c9ee8000b6aa2cf289099e1f5800000009d87ce1153b0fa85e0da2014a0a8d1eaea1c17846d57c1ca22d62c800001468070000187a7469bd0000000022ad80a1b5a1620c3ae8e45812c307500000000d200000000363973c000000035d0000455800000005a8000000031191fc7bf117300027380000000000000000024340c65b9200000009e4832eb8da34b57f162a3500898138c0006b349746db8b7800000a322880000002e8270a0000255836015f197c79da7e24ec80006da000000002905202a041cb524e6859e060000d8000000004738e4a9468cc168a83a80cb16669f9000054f133f39661d07cb8526a1c8a4e1e780000002024000203b6d59aac1ce23315d390c450ea1ac5cc800092713be0002ef63f35a98bcee3d00002c48215a60c3ec99c394ada7f89800000000000000295800017180000a7f8458000843642c58e2ae12a59cfe4a414f25d1aaca072047251c946a7dd09fa145dd64b93c41260080000001155386a40ebca00000002a3417ec8260000000000236c45f27bc2090126529af220a0a8700000fa8378a07723e8000613a8f0490076488c9b8630b19fd2d190da7ca13d22c120f043768266ec415e0000000a35e90106097220259f9643e43b91da92a68ce800020190e634400007150000000134e60207114d480000000000992069e976000000010b40002378a46173b0d42c0a30c000000000007204a7c49c9c220000936b77923eb7b1cce5f6cb2a489069aa70cc1a000000023028bf00009c099d2720a7d8b9383a074063299767d600002b5201a0001b487b352ef3341d6282c4000bc59e744c09648a9d24ec00000000cca860bb51e0800003fe795ad8c0001f6e04400000000000794a49a5d500000000926000069277080005c4c00000000004658000000000015b254caaf00000000000ae2109b0002f04000135e00010dcbc500000001e3b85d80000000000886497600000009c9000000d8000143c0000170000000023f40fa0c40000eb61671bae01b41f20000000b9300004021b7e50da0c8000299700026f251f8bd0050a93ca3c800068a25600000b4800026dc0001dbd10b00008619d80a6613ec00000008be9b0d403e6124fb9b544c90000000187f000113900000000001366000162c9d911e87349d369cd0d686a705081c7ddb80faa70800015815c4494670f5a6e27f57305f90d58098160c4be9d76679e6505179fc8b37800000002b66a4800073024dc45f4ce98
  | 43 => 0x4a34b3f0fd2d8e4742544192953285b06121cba074a80131638e983897f8ed60fb145761ded148e6a012430dc8e68fdd7e02c833e258848a5b70054b906e303518bfc5a698800e7595100001cf3468998704007c12314547d1000000023953daab6825600000000af0aeb200815c841c67b675e6f71a3c0140ab14c3800049aa22c0002b9db4a154c304902200000001199bac0000000a971ee0bc2a692a69400062519384414000000000021dc0000000be80002bb6000270b77191939aa9d9e9bdd978857800013682526d5ea2a5731baab84274a60b89440001420b1497a616b03242c218453a0029a000000096f80008bf000000000000000000b94a7beb731906a59221837c80301dc6c58845d781a939c330000000000123c3ee26f500016b05bb191d00001b05a1247a0001c5c2ea17c65089a365dd2a0f653cee91148000723c000000000000011a20002994986867665b2976a82191439c4000576913068b544600000009d16b8a93d871c01487a05b14bae37aae5a99700008a09510345dd2036f16ac197861a4fe00006049e9e2c6966e75e000cb56297ea7180d88d700000002d245110000000000005b800000015e6525068c38a5e33934a102a7a91b48bc91584180b724e11e3f0fb40000000ec40839af3000103383f06e9000000000000000000000000076018c02a88b12eaf000191b3f3a3b89c68c90797800074500001d54d5003d000078a000010417680002315734ead89be6e0c05352920e31b5e277c34e6dc28285c24db66f1ed0aa2781967720d42b351b107370000b210c3c66f17249990000a9780008c12d98ae6ac16bd124180461b280000d3c00000001d7413ea0c15c1b4e8bb6afd00007000ef63b3000044ede4a0000000000073277a1f423cf000064c80000001e2eb0988f654680007bb2c28836c47e0000e5839940003a400000000d3d0000ca46e580006a096dfb30863a8a6016c1fe93608b7ae2600886a6057dd2c00003bc0000000ba99ba134320c33d5000076540000e1037600011c6b799c8c6561ef276d204fb9366fb8c78ab87b78888981265683f5172a071b6c6d54f9ca929163683dbfe43f000000027fea7416aa90c8000a1ba1038489013a2e14967aa80002a06b6e000108c90894004b12292593807a2da6f3f00000002e1e6584fdca20988159a3334d72aba1114587d5e00e018fa5cd025c4c117ba7de88720002286baf207e8fb1fd80000fd7aeb8efeb6022aca85872a069c00010e90bc0000000836800074e00004aec000740111805b53482b1421ea1090269cb03b13fdda101b5eeec55c474c8aa10a02f9996a54895660000000bb788af602d9727f912561e58d21535c2986bb209c1d7032296c58e3608000073666be84d19104cea76849b400050c8000b811af100000009e89e959c00
  | 44 => 0x2dc03fe400093180004b911c4000298f0000aaf0f30000042c7fc0d62606649400022a954a42553a2b78000000020e618800004341a9a0000000ab950e896a03a000000005570a9988e8000000100aa05acb600023929c1190d75197532226e0e42400000002d4800000000001f3c000294ab1b80006b08000662dec37d72bd6332d4f6000219e42e800022fa75899c8000a778000000000000000009f280009dd18c960423424468bb08856af841b8cb08a300005952b7461b2a8c00000007a640008179c7f93c5d24b88800000014378d21fec6074a3f9a1a7de0c01afe77d0be2a878be01f625bd0001a626ec9a72affa0efb96e8e047b9faa50600001efa37a817114e5bea0d9a4f8ac800008ce684c000b8212e262a590b226a7905b6a96646b6dd2b2080000000d780000000000258e0002ca8000075002080000000ad5ab9000056fc000b18aeb4bbaae7c308800000000000000632000159e0002c72aae80000002cc4000233eaca0e7624aa766000299c812231a00faef90000000672eca40000000000000000021b66f243aca3a800035e40007c088a80001ad696cc00000000000000000000000000012aa3a392a800000006778000bcc2476000010935f800003180000002dea0001a7a00e1ce82be8a8247e87aa3dd00000000000000259c0df800000000006d825190000eb88c999820001c968210f4426388a08b980004249bb36c9ad905ecdc9006b000000000007ba18d892da8a1556cdd623100000ec96204b78000b3905f40001e699742e247078c1820143061761f10b3711a9336a7fc5e4ad5e0c411cc49fe9870000b3e39820869f104ee0000000780000000013ce8ed2a9400000007f2af2600022d7876e9849db07d0790489248ee4460000000000228e00021ce99319dcaea81d6000197a4d900001e0400000000000000a7da6f9efe0002300aa264f32f02928000097e0000000000026a27b12768ca400000000008b9c9750000c7c1de6b3e0111d0e130000041240001cea0be4859bbc26b86720f9000012b1b1881c5ed40000ec200018964a712a20000000000049d0001b7888f2744a511ec800017d0633926295d093c5dc800000011ca8632c7651980000001602000135000020617288594ad092356572d1843dc00028f800031e90862ec9d70bb8ab4aaac01bc70e9782000006f000000046a8002bbdc11a23b023272602da3e00c6822b480201a024603a00003999cea338a54e7c900000002040a21120e878af2a1cb112a259a900000280a000000039e1e67a26959c1dc99a07fe000061680000d059c92334d48481425e2198a2a33480001061dfc00007a498d00000000000a8f09a05da8000576ec345b48000029205196900003850aa00c54745a6308f432981ce5d79a034e1837800000000000000000170b
  | 45 => 0x6ae405e40000ee63aca0ad4cec000000000067a4af8000162eaf4000000026ae6c02bf075e8f948181c9e00000000f42c8800000e75ca82bfbab5b2e55511ba000000050e40000000210000031b2e000000001d5800000000001c0700003bb000048e000000000000001f980104aac0dc1c4ef420000000b1f905c0000000686c000b6ead08000285a0000000000120c00002f0000000000000000000864526a2d8a8b8c7ebd2aa267d186c0000171285e800051b9c3c0002e536c180007a75dfe000000000017faa8f8000000000000027d2a86000090094b60000000000123052dca4410800009248f7b3f76f120180f720355e4c3c385f62e600000e512d457f4b855bd000056c80000ef95309a980008bd4000a0d239c00000007da6c3277597475b38000a5ca0cc44caf4e1c0900dafb22e30b50724202800003a8120ad50248528475ea06096878694040df0584310ab7e5e7070448487cc5f5d6c8658aa6683d81f035109aa9e3a45c67e1ee13e5a55400000009681e82b18e4903f7a1ec00000001b900008f885e60000b267668d1b81fed3c5bc0dbaad980001809b62000287c02d29ee864290ea78977a0001e988d91924063aeba5400850256636e00023d41c5000000010748928cf6b2c0ea00000000b99800000008dd00019fe0002e60225000000015a62e08d70932aeb500000480001e2a00000006c7c0005a6d51e4aa55f80000000183203285fd7ea000270d95d8ceb00005fe2aead1c33100000002b185d540001df14786f3248409e8000000000000022776265ae084c15b8000257e000000046084d89e8118cb87800000005b2b2ea5f211b2d26000027879f188e29b215467d98cb00000008dd9353000000044840000000000409000000000000001dd8000186e38600000000000000000000000008b444dc7d400000001d063ca814a000000000025c82afc0000000fae6a99fda00023250001728a2e8eaa3b011aea8451a449e000022ea14a636dc867220b9a33d06e7b8f16bebc64000000214e68540009f700000b1a182ab41f56163239020f2f24000268a67ddaa90002a5613fea700002c2e8b02b7892dc000b97000079700007f991ec312a478bc38a225448bce64d998a5bc8e6e56823e000018901da2b5c65010d5561498814e8f975ab800e05813fc496d47657b00000e1c000000043150b076e1c8866279ec000036a069a6cc0002d40e4672913d48ba8a785fb53e83fbcdf813c82fe6f20514ad02bdea508aea82cd1e48a590ff35981d87838cceb955a0060dca700d1a79c51a11e23e29ba221a80005901f4102715968b49de200017e80000b7d000000007140000001d9000a17fd53f01300001e1e0000000000041600008040001a731a000001ec400004d9bf800000007ac1dec60bc0000e39a645358000000
  | 46 => 0xf4000000242000000008eca35750746d306a9daa21f254269a000052280008af4d3307465c20001f8cbb828100011bba9bb9eda00000000002e7a55000002d89af0054e5233f510c843ac5301cf197e5988000000000081a000000006ae00006c2bb2ad9e000147c8780b0600000007548a50b3f8b4289a000000000004e407bc00012467b892028dbc00009417aa032a0c5a0ea452badde490000c98000095c0001e8c63427850000000b478bd27a19eae8325d99340a0ff1e68424184077e7c701fe000101277a90809c79ba09699c329ce40008415148000181411700003c800000000000a42141a8e1961b0000e201e6158c1b3a3055d91ce657e5588bcb9a80000079da2925ec000000000025d65a39c1c84e90a91fc1116acd800044900000000000a3397f40000000232d4c20ca4ff52b2675c00025f613d085a7d680000000f7c000000030a8000347508e000001478300007191aae824532e3525ca61e200000000000669c00039889e234896d6722569d7e726822b2cf14926252a76b27ec6b4ac4a8e02e1a17791684bf55c40002edc8dfc00032b0000615800098713c0095873e89d00008f08000043800064f41e850c1ac832f22bf45961ae00000000000000b20000000000000001a486ce0000000216600000000001f842fb0000886a49492e498c000258027e268b4b013c2738156369f9b4173582dca3f9fba1eb8d5c2bf0a141008abdac400000001f68603c000000178872c264a1878ae080d18fc91a806ab7f056a9b1e52c93f9e5896609934cdeb9900027969e2884688016ca09280ec40718fe64c469c4314112649a5e828a2f50477af0094a16786598ecd5f31c409ed22163a599b03b50ee40001c3e37d0000b8fd3f64e3138214b8da000025c678f58070001ea8139a6520001878441ca609b781070000000503400053ed7be00000008291f647331abe00022727c3c000729c00095b0000ae9c00000019808ca29741b41eb5000183abbe8a684160e6f518a6f60dc06c6512845a9918e403ee86902a40f58b99c6fb70c1376a4e8f66b3c289f8cb13d62379c87811af1a1fd273c8c427e09dc2a4c1e107427d02aa83892ddc23322aaa0007b55339ad53f2d5849cbd80e430878a511606e000170ca18800001d137b6590000800174096ee171000262e0001e30b721e438bba4880092b20126065811d80001f4dfc49c5a15c2c388b47199842913207a5efceb4af6889e00008222c898a013795f42fd0842b5d91fe587a38a37f800042e4bf803222a081c15695ce15b0961af2023926110000000000000034a1ff200000009b88d3ea892c9a58387f6a1e91a682ba9f462add869fd8f7e527031c79c8000a6662d50a480005564d0b0e62a408cd93926e992b234a95a21d3ebf21919bfa6b2a74f61ed34a936a25eb3e6d9
  | 47 => 0x566000000020980001dbb742ac682430000000181a00007b400028545e6157a0000000a581514000103888901280a10d0d63880002440000000000000012cd000000000000008769c0e0001f8fa13931c5dd800087c1283bc08dcc2bb2a58411c3ad5c79f1e000000016d00007a38000000217c807c00000000b80000f6216f0000a232628b03aa8e000000000000000000a0200000000000000204a8c93ec07c0162800016e80008fa9bbb950c000499ab769c0e11800000000002ec6a65800000000006b14000126800024480003b681e239380005328000286889949b214400020d2bb300004ea0385063164c9422a6c87097abadb171a56fa129727033452a2ace2230d4c0cf1919b5fa8481802ee9b92a244337916c49d11766f59bc263729b82342812a4d10d766e083a5008ada6745b72a0924007509db66566e124b2c00093a956047d2e652aa00006a5ae189d800980001dcab469f251dd518a559000000000005d5ada84760cc700008d6a9f0a1500002640000000000022ea680000560c4383d48c0599390b029c84eaaf81b32a7040001a28c80b7bc0002a020ab0001c7c6c71106b4d043c000066c0002041ba8c0009c39b1200028a2ba694d046224c0ab22dc45f5259662fe8cc7f650fab17820c4de9a5460d293299ba01893a195072f1c0c83590d8a3d84e23d81af239a97965dba1d686e04e8aa1aaac272177e06d509753c10d2551a3e876c11110ba0fa2084958656b16d71922ae694e21cc75c80002a98000a8e86fa1bd84f6248017072eaed81259414a10115052626b14482636ba7428d7355eac4f7098940080000000e5072bade344fc9229a90cee71219c11e41c1f5b50767393552600000002738000a9f86240002a980001f2695a26d063325b407400000001ac71308b8400017f200c988c55de8de54540003112f37316a5e6675211c3381d9b6a3171c83b298eb7f96e499fa13f6f4444858c8ce62421072b974f0664b1a52aa0263e00029bd62c185ba2f56a88a0ec8a44e117b00012044d58ef22da97b04ce00002db40005f7244a0001d3a633c000497db040000924291aa46624a08022469069229ef65925e9700027d62e80000527ac460ff12e6a34c000ae7119c42288305ad0f1000000000000000000215200000007f4000000002a62040c14a9422b179b0d84246845860f000091c197440c5adc66ca0fe73d14ea447c80c02da334081816600000002878b7600021041d44a5c62040006a52d3e2e5183d8278e1e00000009ca0000000002638a0b7a000000015716600001b2a0000140ac080000001b8400000000002cee152000029d6b2200000000410d32b28800045a88c694c0e470000000759a30d44f000000000000000000000010a00002cc27d000062b269a0a89ac30001c1200000007019cde0a
  | 48 => 0x83000029bc000000000000000005a20000667995a00007b60000000591000000000003cb9bd20000000000000014880000001d9f2a3c0001aa800027800563a50a8a74d2e6c00000000002d2c7f180000000e360001ca000000002cc8000000000000028b600027170662053663d46f0002f4c81110915ba17fe1d3501e2c6216427a905600001ec3402e4b6b450180000c502e2a0a20001206133deee5e7aa880ae82e09b3870c00000001b121ee73285f700016dd000000015b8000000143100017e23e794600000000b338ce7655905a547140bbae172e44540849aa0000a1a1f8643c80000000000acb921c1732dd41ad80000001b6400000007c313ae3fb4000000229e6da800082d400000000000000fac00029220001eb60000ffe00000000000512a749895975255eb1409b5077824203903b63f480004d727ea6b7a42830cacc6431a70a27900f839d4c204179f1285c211930598ba7fa297a05d19456f0270126f2a364d7e9d6aa6928a438cc0b32226842d2aa1032799abb6d0e169b9081a8ac198d4142496852026249b8c3e44e9a60977a9248c3e45a00018761202178abd93100001e266e400000000af100026f09fc400063098b6000247466b213600000002eb1e39620a24208f80002c658f44ee0f422fc80006e727b6839dfa41de1d225ba992f0001198aaba6100000000bc422d40000000000000000026ef09022dd08a9cf60001b8a88b90a75e6c71a0000f987e6259e000098f30d80000001bd3000000014f800000029c2571985c4df00000002e7405381f66ad0000000127d3d2133210a9d12709ca6a6462b2a0000000ac02bce5fa557308a2228650de9b5ca40000d5a9a600000000000000aff2d9219c00004bf1162000000000003f65861c9a971000093b5ddc4799592457e37200013a19c40fd60000a42ba0548e0002a4400022c9000085c000292c0002d020001016a1b0b682dc672aaec80002688000000060a4de641c28d14404f78000ba340009e680000000cc00000000b548000bd516d54ea87b20002bee000000000000000002858000000018d0000000143ea88887b2a566ea0e40000755000000006feba942145f2a2c63b04e4c54d1a9e23ba89400004b42b326b63b2a9800001ed675f02549d76d30bb8c0004068e92ae80d128729bfc9b9a87600000002f4ecf467680080352d787a9a92ea9d83f20002e61000000000017b697c0000000122800002c800001ea00000004751de42e3c00042b18b800001b200000008d100009f21815000000049119a90000fb600000009c1a03c0f98000ba564c80002e9e9d4216a3ba1edd000079c438000068368c84ae07464c788c96cc115b71fa27e9649b8cac5202c5a017f6379a40475b86e351090cf0e2058e777800016a844b81380001d5858263520e038100
  | 49 => 0xf481229e10fd92a71adb60ee368af1163a7010ef806dd082a68904a53a25949d4e78b170aedaafa0c523de4f0000013d800000008b09e7d000165202ba5a994b62b6000169e0002a14773a6782058b10ac2196e0c08000000246c139c000000103a00004cc6018000bd682d6b941b504c191c06b3eece55a902e0002bb800023240cd80000a3980051c04568e9973921c13e6000000031b0616ae180002cc24a80000000000274c1482ec88c4958b67d13b0000155e217c0000000000a3b84a41b8890e52a991e9122b24000191a00000000f0000002498280000c664002050b7d8be42f317de1c3d11e6ee1d4c111d1b505d9f32abac5024149bbd5d81f3eb4e04ec2cd8cf215f6c3a7b089807902bc879c6330a8096c0942d8c4bab2d7b26682fc3d328367c691b6000043eb2525ba35b0c9480b836903f062ca5a00c21f123ba93c97d96cf5feeb6929fda6366b46210c5882d840a935acd8589243c6c7ac1a5a888d1907a77e8a6ad0444d415426182b47f702ca00000fb15e000000007e2870000000006f800020040001af865486ba655d6997c8d3d09b4a5e234b00000000000000000093107080f6244e811c000abf81723
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x843e74194300421eba0ca180211b9c8650c0108dae4328600843d75990300421fbaac8180210fdda540c01087aed2a0600843f76550300421ebb2a81802187992530c010c3ac9298600861e6454c300430eb22a6180211b5d6620c010c5ca9310600862d54988300432729cc4180219354e620c0108deeab10600862e545883004316aa2c4180219394d620c010c9aa6b10600846f769483004236bb4a4180218b992520c010c5ac9290600846f765483004236bb2a4180218b991520c010c5ac8a90600863654984300431aaa4c2180219554e610c010ccca5308600866552984300431b2a2c2180218d551610c010caca6b086008655535843004333292c21802199549610c010c6aa930c4008655539862004332a94c3100211ddd56188010c6aa8b0c4008655535862004332a92c3100210f9d2650801087ae9328400845e73994200422eb9cca100210f9d0650801087ae8328400845e73194200422eb98ca100210fdda540801087aed2a0400843f76550200421ebb2a81002117dda53080108baed298400861e6494c200430eb24a61002117dd953080108baeca98400861e6454c200430eb22a6100218d9526108010c6aa9308400865653984200432aa9cc2100218d9516108010c6aa8b08400865653584200432aa9ac210021999496108010ccaa4b08400847575193100423abb6a988021555cf54c4010acae5aa6200847776553100431b322a9880218ddd954c4010c68ecaa6200847576d4f100429aba6a788021595cb53c4010e2aa929e20087165454f100438aaa2a7880219599153c4010ca8c8a9e200853574d4b10042aab9ea588021c955252c4010e8aa729620087265454b1004392aa2a588021d194d52c4010e8aa6a9620086666454b1004332322a5880211d5da5184010c72cb2a4200863965552100432cb2ca708021965955384010e32a8a9c20086696594a1004334b2aa508021ca55152840108f2ed28c200847575991100423b3b6a888021555cf5444010acae5aa2200853575951100431bb2ca8880211d1d95444010c68c8aa2200863765551100431bbb2a8880218d1d954440108eceda9a200853574d4d10042b2b96a688021555d65344010caecb29a20087155494d100432bb2aa688021c59515344010e2aa8a9a20086566454d100432a322a6880211d9db5244010a6ae9a92200855573d4910042b2baca48802199d965244010e4aa92922008745539491004333b2aa488021c99515244010e4aa8a9220087465354910043a2a9aa488021999915244010cc8c8a92200863554d81100432aa9ec0880219954b6044010c76cb2a2200863b65551100432db2ca68802196d955344010e32a8a9a200866b659491004335b2aa488021ca55152440108f4ed28a20087315494510043a8a9ca288021d854a5144010
  | 1 => 0x3104237bb4a4188211b5da520c4108deeca90620846d76548310432bb2a621882195595310c410e2ca89886208715544c43104362b126218821d1949310c410e8aa4988620863954980310431caa2c0188219694d600c410cd2a4b04420845e73d94210422eb9eca10821175d66308410c3ca9318420861d5498c210422fbaac610821879516308410c3aa8b18420845f7694c210422ebb4a61082117dd953084108baeca98420864e639482104326b1ca4108219398d5208410c9ac6a904208565715482104333b2a4210821995952108410e4ca89084208725544842104362b1a4210821d194d2108410e8aa6908420863954980210431caa2c0108219a94960084108bee6b24a00845c735925004237b92c9280211b1c964940108eaec20ca00853575d07400431ab2e83a0021c554f41d0010e4aa5a0e800863554986400432aa9cc3200219954a61900108eeeab0c800863554586400432aa9ac3200219954961900108eee3b2a800861e54d8d400430eaa6c6a0021879506350010c3aa831a800845e7694d400422e3b4a6a0021179d953500108b8eca9a800862e54d894004316aa6c4a00219394f6250010c9aa7b12800862e541894004316aa0c4a00219394c6250010c9aa6312800846e7694940042363b4a4a002193d8e5250010c98c7292800846e7654940042363b2a4a002193d8d5250010c98c6a92800863654d85400431aaa6c2a00219594f6150010caaa7b0a800866652d854004332a96c2a00218d9506150010c6aa830a800865653185400432aa98c2a0021999486150010ccaa430a800853575d05400431bb2e82a0021c554f4150010e4aa5a0a800845e73d94400422eb9eca200211b9cb65100108dae5b28800845e73994400422eb9cca200211b9ca65100108dae5328800847571594400422f398ca20021175cc65100108dce4328800846d72194400422ebacc620021879526310010c3aa9318800845f7558c400430f2a2c6200218755163100108beed298800845d7694c400422fbb2a620021175d953100108daeb310800862e549884004316aa4c4200219394e6210010c9aa7310800846f7558840043172a2c4200218b5516210010c9ca6b10800864d535884004237bb4a4200211b5da5210010c9cc7290800864d639484004237bb2a4200211b5d95210010c9cc6a90800864d63548400431aaa4c2200219594e6110010caaa73088008666529844004332a94c2200218d9516110010c6aa8b08800865653584400432aa9ac220021999496110010ccaa4b08800863554986300432aa9cc3180219954a618c0108eeeab0c600863554586300432aa9ac31802199549618c01087ce9b28600843d74d943004237396ca180211b5cb650c01087ce9328600843d749943004237394ca180211b5ca650c0108eae2b2860
  | 2 => 0xca210211e9c0651081087ce932e640843d74997320421f3a0cb990210f5d065cc81087ce932c640843d74996320421f3a0cb190210f5d0658c81087ce932a640843d74995320421f3a0ca990210f5d0654c810a98e4a9a640854c73549320423abaec2990218d553614c810caaa7b0a640866552d85320423aba8c2990218d550614c810caaa630a640866552185320421f3a4ca190210f5d2650c8108eae2b28640843e74194320421eba0ca19021535ca530c810a9ae7290640854f754c832042a6baa641902193d95320c810c9aca990640870e544c83204386aa264190218d952610c810c6aa9308640865653984320432aa9cc2190219994a610c810ccaa5308640863654584320431aaa2c2190219594d610c810caaa6b086408666525843204332a92c219021b14c9610c810c6ce8b2e820855573d5341042b2b96a9a08218d59654d04108eaeda9e820853574d4f41042b2b96a7a08219559653d0410e2aa929e82086556554f410438b2a2a7a0821c555153d04108eaeda96820853574d4b41042aab9ea5a08219959652d0410e4aa929682087455394b4104332b2aa5a0821c995152d0410e4aa8a9682087465354b41043a2a9aa5a08218d55160d0410caaa6b06820866552583410422f39ecb20821175cf65904108dce5b2c820846d72d96410422ebacc720821879526390410c3aa931c820845f7558e410430f2a2c7208218755163904108beed29c820845d7694e410422fbb2a720821175d953904108daeb314820862e5498a4104316aa4c5208219394e6290410c9aa7314820846f7558a41043172a2c5208218b5516290410c9ca6b14820864d5358a4104237bb4a5208211b5da5290410c9cc7294820864d6394a4104237bb2a5208211b5d95290410c9cc6a94820864d6354a410432ab1ca3208219958a5190410c72a8b048208659539804104334a94c0208218e9516010410cb2a6b00820866952580410429abacc8208218d5966410410aaae7aa0820856572d50410429abaca8208211ddd95410410c6cc8aa0820853776550410431bbb2a8208211d5db5310410a6ae9a98820856572d4c41042aabaca620821c55525310410e2ca8a9882087155454c410432b322a620821c59915310410a6ae9a90820855573d4841042b2baca420821c95525210410e8aa72908208726545484104392aa2a420821d194d5210410e8aa6a908208666645484104393322a420821d454e6010410ec2a5300820847775580410431aaa2c0208219554d6010410ccaa4b0082086b26458041043a8a9ac020821d85496010410cb2a6b04620846e72d943104236b96ca18821555c5530c4108daeb310620862e549883104316aa4c4188219394e620c410c9aa7310620846f7558831043172a2c4188218b551620c410c9ca6b10620864d53588
  | 3 => 0x9263d4810c3ac931ea40861e6458f520430eb22c7a90218d59261d4810caac730ea40852e74d4a5204296ba6a529021539cf5294810a9ae7a94a40854e73d5252042a6b9ea929021c91c55494810a9ce62a4a40854d7315252042973a6a7290214b5d35394810e1ca929ca40870d5494e52043872a2a729021c35515394810a5ce829ca40852d7414e52042a739ec929021535cf6494810acce3b24a40864d6318e52042b3388c7290211b9da43948108daed21ca4085667190e52042b2b8c8729021539cc6194810a9ae630ca40852e741825204296ba0c129021539cc6094810a9ae6304a40845e73d91520422eb9ec8a90211d9c46354810a5ce9b12a40852d74d8952042a739ec4a9021535cf62548108dcedaa2a40854e73d5152042a6b9ea8a9021c91c65454810e48e2aa2a40846e7615152042a7398a8a9021535cc54548108dceda9aa40852e74d4d5204296ba6a6a9021c39525354810e1aa929aa40870e5454d5204386aa2a6a90211b9d85354810a5ce829aa40852d7414d52042a739ec8a9021535cf6454810acce3b22a4085647159152042b238ac6a90219358c6354810acce231aa40846e7690d5204236bb486a9021599c64354810acae321aa4085677150d52042b238a86a9021539cc6154810a9ae630aa40852e741815204296ba0c0a9021539cc6054810a9ae6302a40852e740415204296ba020a9021539cc1054810a9ae6082a40843d76950520421fbb2a829021879526314810c3aa9318a40861e5458c520430eaa2c629021175da5314810c3cc9298a40861d6494c520422fbb2a629021879915314810c3ac8a98a40862e549885204316aa4c4290219394e6214810c9aa7310a40846f765485204317322a4290218b5915214810c9cc6a90a40864d63548520430f324c629021875926314810c3cc8b18a40861d6458c520431b324c2290218d5926114810cacc7308a40865563984520431cb24c029021179ce65d08108bae732e840845e73197420422eb98cba1021179cf65908108bae7b2c840845e73996420422eb9ccb210211d5c565908108bce632c840845d73196420422ebacc721021879526390810c3aa931c840845f7558e420430f2a2c7210218755163908108beed29c840845d7694e420422fbb2a721021175d95390810c9cc7294840864d6394a420432731aa5210219358d5290810c6ca930c840863554986420432b29cc3210219554e6190810ccaa530c840863654586420431aaa2c3210219594d6190810caaa6b0c8408666525864204332a92c321021179ce65508108bae732a840845e73195420422eb98caa10211d5d76150810c6aa9b0a840865553d854204332a96c2a10211d5d46150810c6aa830a8408655531854204332a90c2a1021179ce65108108bae7328840845e73194420422eb98
  | 4 => 0x5ae530aa80851e73181540428eb98c0aa0214b9c86055010a5ae4302a80843f76550540430eaa4c62a021875516315010c5aa9310a80862d54588540430f324c62a021879916315010c5cc9310a80864e639885404326b1cc42a0218b9916215010c9cc6b10a80864d63588540432b31cc22a0219558e6115010cccc5308a80866562984540432cb1cc02a0219a58a6015010c5ca9316a60862d5498b53043172a2c5a98218b55162d4c10c68e2b26a60862e6498b5304316b24c5a98218b99162d4c10c5ac8b16a608635649875304332b14c3a9821479d35394c10a3ae9a9ca60854e72d4e53042a6b96a729821539cb5494c10a9ae5aa4a6087147155253042a7390a929821535c85494c10a9ce5b24a60854d72d9253042ab38ec929821935886294c10aace2314a60854e7218653042a6b90c329821479d06094c10a3ae8304a60854e7218253042a6b90c1298211b9cb6454c108dae5b22a60851e74d8d530428eba6c6a9821539cb6354c10a9ae5b1aa60845e76d5153042a7396a8a9821535cb5454c10e28e32a2a60871471551530422f3b0a8a9821539c85454c10a9ae42a2a60854e72d9153042a6b96c8a9821559c76454c10aa8e2b22a608554715895304326b10c4a9821559c46254c10a9ce430aa60854d72185530428f3a0c0a9821475d06054c10a9ce4302a60854d72181530428f3a020a9821475d01054c1087aed2a0a60843f76550530430f2a4c629821875526314c108beeca98a60861e6454c530430eb22a6298218b9526214c10c5aa9310a60864d5398853043172a2c4298218b5516214c10c9aa6b10a60861e6498c530430eb24c6298218b9926214c10c5ac9310a60864e639885304317322c4298218b5916214c10c9cc6b10a60863664984530431ab24c2298219998a6114c10ccac5308a608639649805304237394cba18211b5ca65d0c108dce432e860846d72197430423b388cba18211b9cb6590c108dae5b2c860846e729964304236b94cb218211d5c56590c108dce432c860846d72196430423b388cb218211b5d66290c10c5ca9314860862d5498a430432729cc5218219354e6290c108deeab14860862e5458a4304316aa2c5218219394d6290c10c9aa6b14860847575986430431b2a4c3218218d5526190c10caaa730c860863654586430431aaa2c3218219594d6190c10caaa6b0c860846e729954304236b94caa18211b9c86550c108dae432a860847671195430423abaec2a18218d5536150c10caaa7b0a860847575185430431aaa0c2a18219554c6150c108dce5328860846d729944304237390ca218211b5c86510c108ece2328860847a70194430430f2a4c7a90218755263d4810c3ca8b1ea40861d5458f520430f324a7a90218759253d4810c3cc8a9ea40861d6454f520431a38ac9a9021879
  | 5 => 0x847675d923144272b96c918a211d5d8548c510c6ac82a462885657214e314423bbb2a518a214d1d1528c510aa8e6a94628854d7214d314423b3aec898a21395cb644c5108e8eab2262884767695131442ab39ca898a218dd90544c510aacebb1a62885567394d314423b3b0a698a21595c8534c510b8ae429a62885567614d314432b3b0a698a21559d0534c510e8ce429a62885557214d31443a2b90a698a21515c8534c5109aceda1a628855675d0d314432a32e8698a21551d4434c510ca8ca21a62887145410d31442e8b808698a211d1d9524c510a68e8a9262885547354931442aa3ae6498a21d1d4b324c510aa8ea9926288745524c9314425aba0c098a21395c8604c510d8ac4988628854d7314b214423b3aec910a21355cf64885108eaec2a4428863564152214423b3aec710a212d5d363885108eeeca9c42885347454e21442b2392a710a21555cc5288510a9ae6292428847675d91214426ab9ec890a21599ca5448510c6ec82a242885347454d21442b2392a690a21599d762485108ecec29242885557314921442e2b98a490a21599d85248510cccec29242885667414921443a3398a490a21595cc5248510e8ae629242885457314921442733b68490a21599d74248510ac8ea21242887245410921442f0b808490a21591d63248510e8ea71924288564754c921443a2a9a6490a212d5d060485109aae630242886c563484214426ab9cc3a0221395ca61d0110a68eaa0e808845f73595404422e39acaa02211bdc96550110c3ea831a808861c5418d4044317aa0c4a02218b1506250110c68a9b0a80885347550540442d838282a0221535c853cc110ca8a6b0e6088554754c7304421fba2ca982210f1d1654c1108dee4b2a608854d7214d3044272b90c298221551d5314c110ca8ca98a608854d7314b2044332292c3902210fdd16548110878e8b2a408845f73595204422e39aca90221355cc6148110cc8ca90a40885d17390710442f0b94838822135dcd64841109cee4b24208863564152104432731cc5aa0219358e62d5010c9cc6b16a80864d6358b540432ab1cc3aa0219958a61d5010a3ce7aa4a80851d73d525404297396a92a0214b5cb54950108dce531ca80846d7298e540423b38cc72a021179ce62950108bae7314a80852e7298e5404296b94c72a0214d9c66395010a3ce7314a80851d7398a540429b38cc52a021479ce6195010a3ae730ca80852e729865404296b94c32a021479cc6095010a3ae6304a80852e721825404296b90c12a021479cf6455010a3ae7b22a80852e72d915404296b96c8aa02117dcd60550108b8e6b02a80852e7298d5404296b94c6aa0214d9c66355010a68e2b1aa80851e73989540428eb9cc4aa0214d9c66255010a68e2b12a80851e73985540428eb9cc2aa0214b9ca6155010a
  | 6 => 0x8431aaa2c220421475d053cc210a9ae429e610845e7614d308428eba0a698421535c8534c210c3ac9298610845f7654c308430eb22a6184219394d620c210c9aa6b10610865653584308432aa9ac2184211ddd954c4210c6cc8aa621085577355310842b3b92a9884211b9ca63951108dae531ca88845e7398a544422eb9cc52a22187d906355110c9ec7b12a88864c63d895444317b20c4aa22193d8c6255110c98c6312a88865763d85544432a31ec2aa22199d8b6155110cc8c5b0aa88843f76550544428e39aa82a2214b1c954151108bce7308a88845d73984544422f398c02a221175cc60151108dee4b26a68846c72593534423bb8ac9a9a21871936354d10c5ec9b12a68862c64d895344317b20c4a9a218b1906254d10c9ec6312a68866571189534431a326c2a9a219918b6154d108beeca98a68851c7454c53442a6392a629a219354d6214d10c9cc6b10a688666625845344332b12c229a210f9d06014d1087ae8300a68846e72d974344236b96cba1a21535c853d0d109cae530e8688474755874344237396cb21a211b5cb6590d108eae3b2c868846e721964344236b90cb21a211d9c46590d10c5ea9314868862c5498a434423a3aac321a218d1516190d108dee4b2a868846c72595434423bb8acaa1a211bdc96510d108d8e4b28868846e721944344236b90ca21a21535c85310d108e8eab08868865453584434423c3aac021a2117dcd64d49108b8e6b26a48861f64d8d524430e326c6a922187d906354910c38c831aa4886557118d524431a326c2a92219518f61549108deeca90a48852c7454852442a639aa4292219358d5214910c98e4b18a48864d63988524422f398c229221175cc61149108bce7b2e848845d73d9742442a6b98a5a1221355ce61d09108bce7b2c848845d73d96424422f398cb21221175cc65909108ece232c848861f5498e424430e2a4c7212218d15161909108bee6b2a848845c73595424422fb9aca21221171cd65109108bce6328848845d7319442442a6b98a4212219914961109108f0eab00848843e74d97324421eba6cb99221471d153cc910a98e4a9e648854d7314b324421f3a6cb192210f5d3658c910a9ae429c648843f74595324421e3a2ca99221179da534c910a38e8a9a648854c7254d32442373b4a4992210fdd1650c910878e8b28648847671194324422ebb6a619221535c8530c910a9ae6290648854e754c832442a63aa641922193d95320c910c9aca990648865753584324432a29ac21922199d49610c910cc8a4b0864886c532584324432b32cc720a21959956390510caca8b1c82886545458e414433332cc520a21b158e6290510ccccab1482886c66358a4144362b1ac520a21999516290510cc8a8b14828847676151414426ab98c0a0a21395c86050510a9ae429e628
  | 7 => 0x698e21d45c0534c710aaceba1a63885547510d31c42aa39aa498e21551d5324c710e8aa499263884b57418131c4272b90c098e2117dd9530c710c9ca6b10638864d5358831c4362b126218e21b44c5600c7109aae7b2443884777559221c431ab20a910e212d5d36388710aaae629443884d573d9121c423b3b4a890e21599ca54487108eceda9a43885647254d21c42f0b86a490e211d9d85248710aaae629243884e67614921c42e2b98a490e21599d85248710cccec29243885667414921c43a3398a490e21595cc5248710e8ae629243885457314921c43b0b80a490e21599d74248710ac8ea2124388564758c921c42b23aa6490e21d154d324871096ae830243884d57318121c4326b1ca410e219358d5208710d8ac690843886e12158021c426ab9cc3a0621395ca61d0310c6ca830a81886555318530c4272b90c2986211b9ca63952108dae531ca90845e7398a548422eb9cc52a42193d8f6255210c98c7b12a90864f631895484326318c4aa42195d8f6155210ca8c7b0aa90866762d855484332316c2aa4210fdd95415210c3aa8b18a90862d54588548430f322c62a4219398e6215210c9ac7310a90862e64588548432731ac42a4219358d6215210cacc6b08a908655635845484333312c22a4219958961152108dee4b26a70846c72593538422fbb2a629c21875915314e10c9aa6b10a70861c73590538430eb24c629c218b9926214e10c5ac9310a70862e645885384316b22c429c219398d6214e10c6cc8b08a708635645845384333312c229c21995896114e108dce432e870846d72197438428e39aa9a1c21475d053d0e10a9ae429e870846e72d964384236b96cb21c211b9c86590e108dae432c870864e5358a4384326a9ac521c219594d6190e10caaa6b0c870846f725954384236392caa1c211b9c86550e108dae432a870845e7694d4384237390ca21c211b5c86510e108baeda98870851d7414c43842a6b90a621c2117dcd64d4a108b8e6b26a50846f765485284316b22a4294219358d5214a108bce632e850845d731974284296392a9a1421179cf6590a108bae7b2c850864d6394a4284326b1aa521421999496190a10ccaa4b0c850845f73595428422e39acaa1421179cc6550a108bae632a850843e74197328421eba0cb994210fdd1654ca10878e8b2a650843e74195328421eba0ca99421531c9534ca10a98e6a92650864f654c83284326b2a6419421b14c9610ca10aaee6aa6830856772553418423abb6a820c2155dcd5410610acee4aa0830847576d4c418429bba2a620c211d5db5210610a6ee8a9083086c5624c43184362b1a4210c21475cc54d0210a5ae42a6810843e76151408428eb98a8a04214b5c8545021087eecaa0810861e5458c408430eaa2c6204218b9516210210c5aa8b108108636545844
  | 8 => 0x26310030c3ca8b18801861d5458c400c23abacc2200618d9526110030c6aa9308801847775584400c31b2a2c2200618d55161100308eaed288801865663944400c32ab1ca2200619998a5110030ccac5288801847776544400c32b31aa2200619558d5110030cccc4a88801866562544400c2aab8ea99806117dd954cc030c3cc8aa6601861f76553300c30e3b2a998061c555251cc030e2ca8a8e601871554547300c3a3292a398061d154951cc030cacc8a8e601865464547300c22ebb4a7180611e5da538c030e62a8a8c601845d75991300c22f3b6a898061555c7544c030a3aeb2a2601861f65951300c22e3b2a89806187191544c030c3ecaaa2601861f76551300c30e3b2a89806195d96514c030e2aa928a601865765545300c38b2a2a298061c5551514c030e8ca4a8a601874552545300c32b322a29806195191514c030c3aa9b02601863b65951300c31db2aa898061c6552534c030ce6cb28a601867365545300c398aa2a298061d494d514c030c9cc7316a98864d6398b54c432731ac5aa6219358d62d5310cacc730ea9886556398754c4333314c3aa6219958a61d53108dce531ca98846d7298e54c422f39cc52a621175ce629531087eecaa0a9885557398454c42b2b94c22a621595ca61d4f108dce5b22a78846d72d9153c422fbb2a629e219354d6214f10c9cc6b10a7886656298453c4237396cba1e211b5cb65d0f108dce532e878846d7299743c432aa9cc3a1e21395ca61d0f108dce5b2c878846d72d9643c4237390cb21e211b5c86590f108dce532a878846d7299543c4237390ca21e211b5c86510f10a3ae9298878845e73d9152c422eb9ec8a96211bdd95214b10c9ac6a90a5886556398452c422f39ecba1621175cf65d0b108bce732e858845d7399742c426ab9cc3a16219954a61d0b108bce7b2c858845d73d9642c422f398cb21621175cc6590b108bce6328858845d7319442c4296ba4a4216210f9d365ccb1087ae9b2e658843e74d9632c421eba6cb19621531c9534cb10a98e6a92658864f654c832c4326b2a6419621b14c9610cb10caacb31c83886556558e41c432b2a2c720e21951516390710ccacb31483886c56398a41c4332b2ac520e21b198d6290710d8ac6b1483886665458a41c43322a2c520e21b458d6090710dc2c4b04838843e7615141c42d8b86a8a0e211d9d8545071096cec2a283884d57318141c4272b90c0a0e210fdd95410710d6282b00838854d7214f31c4272b96c918e211ddd5648c710c6ac82a463885657214e31c422f3b0a698e21535c8534c7109cae5b2263884767695131c42ab39ca898e21745c3534c7108ecec29a63885657214d31c426b3b0a698e21715c8534c710aacec29a63886567614d31c42ab3a0a698e21d19c8534c710aaae429a63887457214d31c42a2b90a
  | 9 => 0xce5b22a21856572d91510c2aa39ac8a8861555c343544308eced21aa2185667290d510c2b2b9486a88615c9c04354430ae2e021aa2187167410d510c3a938086a8861555c04354430ea2e021aa21855473589510c2ab398c4a8861995886254430a6ce8302a21853574181510c2b3390c0a8861595c86054430a6ce8182a218535740c1510c2b2b9060a88610f5da541443087eecaa0a21862e54988510c316aa4c4288618b9516214430c5aa8b10a21846d76948510c317324a4288618b59252144308deeca90a21862e64548510c316b22a4288618d9526114430c6aa9308a21866652984510c332a94c2288611ddd95114430c6cc8a88a21863564544510c333312a2288619958951144308dce532e821846d72997410c237396cb208611b5cb65904308dce532c821846d72996410c30f2a4c720861875526390430c3ca8b1c821861d5458e410c236bacc5208618b9526290430c5aa9314821846f7558a410c3172a2c5208618b55162904308deed294821846d7694a410c32731ca5208619358e52904308deeca94821846d7654a410c32731aa5208619358d5290430caac728c821866662946410c332b14a3208619598d5190430caac6a8c821866662546410c332b12a3208611b9c865504308dae432a821845d75d8d410c30eaa6c6a0861875506350430c9ec6a92821864c63549410c32bb1aa2a08619518d51504308dce5328821846d72994410c338a8ac1988611b5d6620c430c5ca9310621862d54988310c237baac4188618b951620c430c5aa8b10621846d76948310c237bb2a4188619998a510c430ccac5288621866662544310c332b12a218861c5951310c430e2aa898862186c5624c4310c3a32926218861d1549310c430c72a9300621863954580310c33928ac0188610f9d2658843087ae932c421843e74195210c21eba0ca90861175d76348430c3aa9b1a421861d5418d210c32bb1aa2908619518d5148430ac8e4a8a421843e74994210c21eba4ca10861879526308430c3aa9318421861e5458c210c30eaa2c6108619598e5108430caac7288421856572944210c32b31aa2108619558d5108430aceea908421856575484210c333b2a4210861995952108430e4ca8908421872554484210c362b1a4210861175d84394030a3aeba1e801861d65d0f400c38ba1aa3a00618755263900308beeab1c801861d5458e400c32b31aa3200619558d5190030c3ca9b1a801861d54d8d400c30f2a0c6a0061875506350030a3aeba1a801861f65d0d400c31b2a6c2a00618d5536150030c6ca830a801863554185400c23b3b4a2a00611d1da5150030caec728a801865463945400c333b14a2a00619918a51500308ececa8a801847476545400c32bb1aa2a00619518d5150030e2e86a8a801866762545400c332312a2a00618755
  | 10 => 0x45e75d91314c266b96c898a61559c6544c530c3ec82a2629855675d85314c2a6b90a298a61715c8514c530aacec28a629865676145314c2ab3a0a298a61d19c8514c530aaae428a629874572145314c2a2b90a298a61359db414c530aaceba0a629855475105314c38a2a08298a61745c0414c53093ae830262984cd72181314c362b126218a61595c45288530ca8ca98c4298747524c6214c22f3acc690a61275d26348530ca8ca98a429843f74594214c21e3a2ca10a619558f5108530caac6288429856572144214c2b33aa4210a61591d52108530ccaca90842986c563484214c26ab8cc7a0261471d543d0130c38a9b1a809851c7550d404c2cc38286a02618dd506150130c68a830a80985d17190f304c26bb8ac91826187590548c130cccc530ea81865663587540c333312c3aa0619958961d5030a6ce3aa4a81853571d52540c237394c32a0611b5ca6195030a6ce331ca8185357198e540c28f39cc32a0614b9ca6195030a5ae530ca81853671182540c29ab88c12a0614d9c76455030a6ae3b22a8185367198d540c29ab8cc6aa061479ce6155030a5ce530aa81852d72985540c28e39ac2aa0614d9c46055030a6ae2302a81843f76550540c31aaa4c22a0618d5516115030c6cc9308a81865663984540c333314c22a0618d9916115030cacc6b08a81866662584540c332b12c22a0619c5866015030c3ce8b2e861855571d53430c30eb2ca9a18618755160d0c308eaeb30c861863654986430c31aaa4c3218611ddd56190c30c6ca8b0c861863554586430c32b29ac3218618e5516090c30c74a8b00861851d75990430c30eb2cc821861555c75410c30a3aeb2a0861845f76550430c30f322a82186147dd95410c30c3eecaa0861845f75580430c30eaa2c021861a69916010c30c5ca9316a21862d5498b510c3172a2c5a88618b55162d4430a6ce9a8ca21853574d46510c2b3396a328861595cb5194430acce5aa4a21856572d52510c38a39aa928861599c85494430acae42a4a21855575d0e510c38aaa68728861c55504394430a6ce9a94a21853574d4a510c3932a4a528861c95525294430aace7b24a21856672d92510c2b2b96c928861599c86394430acae431ca2184757690e510c2b33948728861595ca4394430aace6314a2186656218a510c29b3a0c1288614d5d06094430acce4304a21856572182510c237396c8a88611b5cb64544308ecedaa2a21856672d51510c2b2b96a8a8861c51ce5454430e28e6aa2a21847676151510c2b3390a8a8861595c85454430aaaeba1aa21871654d0d510c38aaa686a8861c59504354430e2aa821aa21853674d49510c29aba6a4a8861c99525254430e4aa9292a21874743949510c3a221ca4a8861c99515254430e4aa8a92a21874743549510c3a221aa4a8861559cf6454430ac
  | 11 => 0x10339b28c2a00819cd965150040ce6caa8a80207325454540103a8a9aa2a0081d85495150040cacc730ea9986666298754cc32b31ac3aa6619998961d5330ccac4b0ea99846e7298654cc236b94c32a6610fdd95415330aaae3318a9986556598643cc32ab2ac321e61b19896190f30d8ac4b0c87986565458643cc32a2a2c321e61b45856090f3087cec2a2879859970d5143cc22f3b0a8a1e61279d85450f309aae2302879843f7655043cc34ca1ac021e611b9cb64547308dae5b22a3984777654451cc332b12a228e611b9cb65d07308dae5b2e839846e7299741cc236b94cba0e61335ca63d0730cacc6a8e839846e72d9641cc236b96cb20e614d5d2511073099ae5b26639845f7559331cc30eb20a998e61335cb644c7308bced2a263985567195131cc2aa38aa498e61745c3514c7309acec28a63985c57214531cc2ab3ae8298e61275d0604c73099ae430263986656294431cc332b12a218e61b1589310c730da262b00639843e74d9621cc21eba6cb10e61275d26348730ac8e4a8a4398654654c521cc3a2a926290e6199d952108730ccaca90843986c56348421cc26ab8cc7a06618795063503308dce530ca91846d72986548c32bb1ec2aa46199d8b6155230caec630aa91866762185548c332310c2aa4610fdd95415230c6aa8b08a91865563984548c333314c22a4618d9916115230caac6b08a91866662584548c332b12c22a46155dc554d0e308baedaa0871855771550438c30fb2086a8c611ddd95114630c6ac8a88a31866562544518c29a38aa9a0c611b9cb65906308dae5b2c831865563946418c332b14a320c619558d5190630ccac4a8c831846f72595418c236392caa0c611b9c865506308dae432a83186c5624c4318c21fba2ca90c610f1d1654863087ce832a431843d74195218c2b2392a290c6199d952108630ccaca90843186c563484218c29ab88a9a04610f9d85450230a6ae22a2811843f76550408c30f2a2c620461875516310230c6ca8b08811863554584408c22fbb2a9984618799154cc230aaee2aa6611846e72986544c236b94c32a26195d8f6155130ccec5b0aa89863764185544c32bb18c2aa26199d886155130cc8c430aa89843f76550544c29a38aa82a261959966190d30caccab0c86986c662586434c362b12c321a61959516190d30ca8a8b0c869845e76151434c26ab88c0a1a611bdc964d45308d8e4b26a29847776544514c29a3a2a228a61591c95114530ccac4a88a2984cd7298f414c2b2b90a3a0a611b9c865905308dae432c829861c5458e414c317aa4c520a618b15262905308dee4b28829846c72594414c237390ca20a611b5c86510530caac6288829856572144414c22f3aec998a61335cb64cc5308baec2a6629861d64153314c2a6b90a398a61595c8518c530acae428a6298
  | 12 => 0x288819994a6114440ccaa5308a22047776544511032b31aa2288819558d5114440cccc4a88a220665625445110338a8ac1a088117dda53904408baeca9c822064e5398a4110326a9cc5208819394d6290440c9aa6b14822046f7694a411032731ca5208819358e52904408daeca94822064e6354a4110326b1aa5208819598d5190440caac6a8c8220666625464110332b12a3208819654e6010440cd2a53008220659535804110334a92c0208819c94560104408dce532e622046d729973110237394cb188811b5ca658c4408dce432a622046d72195311021ebaec89888187d91534c440c38c8a9a62205547154d3110317b22a4988818b191524c440c6ec8a8a62206346454531102aa39aa2988811b9cb650c4408dae5b28622046e729943110236b94ca18881555c6530c4408daeb310622064e539883110326a9cc4188811bdd5620c440c9ca6b10622064d535883110237bb4a4188811b5da520c4408deeca90622046d7654831102aab9ca2188819998a510c440ccac52886220666625443110332b12a21888155dd5310c440aaaea9886220657654c4311032ab2a6218881b1589310c440e8ca49886220745524c4311022f39ccb10881175ce65884408bce632a422045d73195211021ebaec89088187d915348440c38c8a9a422063764545211031a322a290881591c951484408bce7b28422045d73d94211022f39cca10881175ce65084408baeb318422045f7558c211022fbb4a610881175da53084408beeca98422045d7654c211032b31ca2108819558e5108440acae5288422065663544211032ab1aa21088159dd52108440acaea9084220667654842110332b2a4210881b158d2108440e8ca6908422074553484211038aa9ca3a0081c594d51d0040e2aa6a8e8020726525474010392a92a3a00810f5da54900408f2ed2a480207515354640103b0a92a320081171da53500408bceca9a802065653d85401032aa9ec2a00819594c6150040caaa630a802047476945401032bb1ca2a00819518e5150040ccec528a802066462945401023b3b2a2a008195d8d5150040ca8c6a8a8020667625454010332312a2a008187dcf6550040c38e7b2a802063771d95401031a38ecaa008187d976350040c3eca31a802061f6594d401030fb2aa6a0081479d95350040a38eca9a802063765d85401038aa9ec2a00818dd946150040d28c630a8020715531854010352310c2a00818dd965150040e2aa728a802063765545401038b29aa2a0081c554d5150040e4ca4a8a802072552545401029b3b2a2a00814d1d95150040e2ec6a8a8020714635454010393b12a2a0081c91895150040cb6e7b2a802065873d954010339b8ecaa00819c1c76550040cb6cbb1a802065b6518d401032db2ca6a008196d955350040e34a8a9a802067365d8540
  | 13 => 0x620c540c98a731062a046c755883150327a9ac418a819314d620c5408deeda9062a046d76d483150237bb0a418a811b5d8520c540cccc5a8862a066562d44315031b320a218a81555cc510c540cccc428862a06656214431502ab3aa6218a81551d5310c540cacca98862a0654654c4315034b3226218a81b1589310c540e8ea498862a0744524c4315032c29cc018a819c146600c540da262b0062a045f73596215022e39acb10a81879905388540c3ac829c42a062e64d4a215031b320a310a818d59051885408bce7b2a42a045d73d95215021f3acc890a81275ce6448540acce5a8a42a063465d05215022fb9aca10a81171cd65085408bce632842a045d73194215022f3acc610a81171d563085408beeda9842a045d76d4c215022fbb0a610a81175d85308540cacc7a8842a065563d44215031b320a210a819598c5108540caac628842a05657214421502b33aa4210a81591d52108540cccca90842a06646548421503533224210a81b158d2108540e8ea690842a074453484215033828cc010a81b84856008540e28a628c80a07245214640502ab38ea729881555c75394c40a9ce430ca62054d72186531032ab08c329881559c46094c40aaae2304a62046e721855310236b90c2a9881471d16154c40a9ce430aa62054d72185531032ab08c2a9881559c46054c40aaae2302a62045f7654c531032aa9cc2298819554d6114c40cb2a6b06862065553986431032aa9ac3218819694d6010c40c9ca7316a22064d5398b511032729ac5a88819354d62d4440aace7a8ca22055573d4651102b3396a328881595cb5194440acce5a9ca22056572d4e51102b3390a728881595c85394440aace7a94a22055573d4a51103a329ca528881d154e5294440caac631ca2205667218e51102b2b90c7288811d9da4394440acce521ca2205657290e51102ab398c528881555cc6294440ccac4314a2205567318251102aab98c128881599c86094440acae4304a22046e7218d5110236b90c6a8881179cc62544408bae6312a22047676d4d51102b3396a6a8881595cb53544408ecec29aa2205667214d51102b2b90a6a8881559cf5254440aaae7a92a2207465394951103a2a9ca4a8881d194d5254440e8aa6a92a2205347458d511032ab18c6a8881599c86354440acae431aa2204757690d51102b339486a8881595ca4354440ae4e021aa2205717010d511029a3a2c4a8881559cc6254440aaae6312a2206656218951102ab398c0a8881555cc6054440acce4302a2205657218151102ab39880a8881555cc4054440acae4202a22045d7694c511022fbb2a6288819394e6214440c9aa7310a22064e535885110326a9ac4288811b5da5214440c9cc7290a22064d639485110237bb2a4288819398d5214440c9ac6a90a22065653984511032aa9cc2
  | 14 => 0xe7316a2a05667294f51502b2b94a7a8a8159dc953d4540ac8e4a9ea2a07157414f515038a29e87a8a81d1d4f52d4540e88a7a96a2a06576398f51502b3394c7a8a81595ca63d4540a6ae831ea2a04757690f51502b339487a8a81595ca43d4540aace7316a2a05557398b5150333b14c5a8a814d5d062d4540c9ea7314a2a064c5398a5150327a9ac528a819314d6294540c9cc7a94a2a064d63d4a515032b31ea328a819558f5194540cccc5a8ca2a066562d46515022f3b6a6a8a81179d85354540c9ea7b12a2a064c53d895150327a98c4a8a819314c6254540c9ec7a92a2a064c63d49515023bbb2a228a8155dcd5114540aa8e6a88a2a05677254451502b2392a228a81959975314540e2ac9a98a2a04757694c51502b3394a628a81595ca53145408eeeca98a2a05677254c51502b2392a628a81959945314540e2ae8298a2a07156414c515029b3ae8628a81c514f4314540e28a6a18a2a066665d4851503a3a9ea428a81d114f5214540e4ac9a90a2a04757694851502ab39ca428a81555ce52145408eeeca90a2a05577354851502aa39aa428a81d1d4c5214540e88a6290a2a0725641485150393a18a428a81c950c5214540aace7b20a2a055573d9051502b3396c828a81595cb6414540a6ae9b18a2a05357418c515032ab18c628a81599c86314540acae4318a2a05717018c515023abb48628a81599ca4314540acae5218a2a07154310c515029aba6c428a814d5d06214540aace6310a2a0555731885150332b10c428a815c5c06214540aaee6a00a2a05547350051502b3b928028a81591c94014540c3cca29e82a062e6514b4150386298a5a0a818d99751d0540e2ea628e82a0714531474150393a90a3a0a81c914851d05408bceb31c82a045c7558e415022ebb6a720a81175d853905408dceb31482a064f5398a415032629cc520a811b1d56290540c9ea6b1482a064c5358a4150236bb6a520a819398f5290540c9ac7a9482a046d7614a4150327318a520a819358c5290540cacc7a8c82a065563d464150333316a320a819958b5190540cacc628c82a0655631464150333310a320a81995885190540ce0a330482a0673511814150386298a4a0a81c514c5150540e48a428a82a049d731814150256b90c0a0a81acd846050540e28a6a0882a0724525044150237b92cb98a811b1c965cc540c3cc829e62a061d6414f3150317320a598a818b59052cc540c6cc9a8e62a046f725963150236392cb18a8187993538c540c5cc829462a062d6414a315031b320a318a818d590518c5408dce5b2a62a046d72d95315021f3acc898a812b5ca644c540aace3a9a62a061c65d0d31502ab39ea298a818d197414c5408dee4b2862a046c725943150237390ca18a811b5c8650c540c3cc829862a05557114c31502373acc418a8193d4e
  | 15 => 0xa67418121086d2ba0c090843719cc6048421b8ae63024210f45531812108673bb243a8043b198d21d4021d8ac690ea010f465348750087a2a9a43a8043d154d21940218bee6b24a010c5c7359250087a329a42a8043d154d21540218bce6322a010c5d731915008733bb242a8043991d92154021cc8c890aa010e676348550087b1b8242a8043d81c121540218baed298a010e1e6494c500870eb24a62804317dd95314021c3cc8a98a010e1d6454c5008673bb24228043a99912114021d4ac8908a010ec6634845008762b1a4228043d154d21140218f6eca80a010e3964540500872ba9ac329e819998a6194f40cccc4b0ca7a06656258653d022fbb2a629e81555c653d0f40b2ae329e87a04b571d9543d02ccb86a6a1e81279d85350f4096ae230287a05557194c43d034ca1ac021e819558f5194740ccac5a8ca3a064e6398a51d0326b1cc528e819398d6294740c9ac6b14a3a04777654451d02aab9ca3a0e81595ca51d0740b2ae728e83a05a57294741d024eb9ecaa0e812b5cb6550740b62e1a8a83a04b67614541d024eb98c0a0e812b5c86050740aaae728883a05657294441d0358a0ac020e811b9cb65cc7408dae5b2e63a046e72d9631d0236b96cb18e811b9cb654c7408dae5b2a63a04ad7299131d0237396ca18e811b5cb650c740cacca98863a0696644c431d0362b126218e81179cf65887408bae7b2c43a045e73d9521d022eb9eca90e81275ce64487408bce7b2843a045d73d9421d033332a4210e81a99912108740d8ac690843a046e721855390236b90c2a9c8117dd95314e40caaa6b08a72065653586439032aa9ac321c811b9c863546408dae431aa32045e73189519022eb98c4a8c811ddd95114640caac6a88a32066562544519032ab1ca320c819958a5190640caac6a8c8320665625464190237b92ca98c811b1c9654c6408dce432a632046d7219531902aa38aa698c81551cd514c6408dce5b28632046d72d94319032bb2a6218c8195595310c640d8ac498863206d131580319022fb9aca90c81171cd65486408bce632a432045d7319521902b2392a290c81179cf65086408bae7b284320667654842190332b2a4210c81b158d2108640dc242b00432051f73597409029bb8acba04811b9ca61d4d408dae530ea6a054e7298753502a6b94c3a9a8195d8661d4d40a3ae830ea6a065753986535032ba9ac329a8117dd95314d40aaee2a98a6a05547154c53502ab38ec829a81555c76414d40a3ae9b08a6a051d7418453502a7390c229a81535c86114d40caac2308a6a055970184535030f32ea7a1a811d9d66190d40caea730c86a065453986435023a3aac321a8195d4d6190d40ca8a6b0c86a065853982435032da98c0a1a812d5c46050d40d36c630286a046e7298f5150236b94c7a8a81179ce62d45408ba
  | 16 => 0x872729ac5208439354d62904218bce73288210c5d73994410862f398ca20843175cc6510421c9aa73108210c6f755884108726a9ac4208434d5d25110421a6eeaa088210f1653504410861f3a6cb188430f5d3658c421c9aa73146210c6f7558a3108726a9ac5188439354e620c421c9ca6b106210e4d53588310872bb2a621884395595310c421d8ac49886210d557315221086b8b80a9108431d5da52884218ecec2a24210d557315121086b8b80a8908431d9db5348421aaaeb29a4210e576594d210872bb2aa690843d19c95348421e88e4a9a4210e5553d8921087a2a9ca490843d154f4248421acaeb2124210dc67390921086e2b9c8490843d154e4248421aceeaa124210f455350921087932a08490843d154c4248421acaeb9924210f4553cc921087a2a9c6490843d154d3248421acaea1924210f45530c92108732baeca90843999db6548421acce9b2a4210d6573d9521086b2b86ca90843719cf6448421b8ae7b224210d657599121086e339cc890843715ce6448421aceeab224210ea56419121086733b6a890843719cf5448421b8ae7aa24210d667695121086b23b4a890843599d25448421e4ec92a24210f246495121086b2b9ca890843595c254484219ccec2a24210dc67315121086e2b98a890843789c05448421bc2e02a24210d667615121087333b0a890843599d05448421e4ce82a24210f467315121086b2b98a890843d15cc5448421a8ae62a24210f627015121086b2b80a890843d85c05448421ac2e02a24210d657598d21086d33a4c690843695d26348421aceeab1a4210ec56318d21086733b6a690843599db5348421ccceda9a4210d6674d4d21086b2b86a690843595d65348421b8aeb29a4210d457594d2108763b2ca690843d1d965348421e8ca929a4210f445494d21086b33b2a690843591d95348421ac8e8a9a4210f477354d21087a3b1aa690843d118d5348421acee0a9a4210f477554d2108763b2aa690843d1d955348421e8ea8a9a4210f465454d21087a2aa2a690843d11515348421e8eeca9a4210f467654d21087a2bb2a690843d11d95348421e8ee8a9a4210f467454d21087a2ba2a690843d11d15348421e8ec8a9a4210f466454d21087a2b22a690843d11915348421e8ee0a9a4210f467054d21087a2b82a690843d11c153484219ccec29a4210d667514d21086e3398a690843d154c53484219cceda1a4210ce576d0d21086b3bae8690843591d74348421e8aa7a1a4210ce67690d2108672bb48690843599d64348421acaeb21a4210f455390d21086b3baa8690843591d54348421e8aa6a1a4210d667510d21086b2ba88690843d154c4348421e8aa7b024210d657598121087a2a9cc09084359dd56048421b4ee8b024210da47458121086e3b9ac090843711cd6048421e8aa6b024210d
  | 17 => 0xa43395c262d0521ccccba168290c5e73d95414862eb9ecaa0a43555cf54105218eeecaa08290ce47258c414869aba6a620a431ddd95310521accea3108290dc57318841486f0b80c420a43599d74210521e4aa82108290ce472580414872629ac598a43399ca648c5218ecea3246290c757695231486ab39ca918a434d9d2538c521b4ce9b146290d667518a31486733b68518a43715cf428c521d4cc82146290ce472582314861f3a6ca98a430f5d3654c5218eceb3226290ce672991314863b3b4a898a43559ce544c521aacebb1a6290d367494d31486ab39ca698a431d9d8534c521aacec29a6290e567614d31486ab3a0a698a43d15c8534c521aaae029a6290d5675d0d314878a2a68698a43551d4434c521b8ae421a6290ce67518931487333a8c498a43399d0624c5219cae03126290ce676d0931487523268498a43391d8424c521b8ae62126290e5465cc931487623166498a4399196324c521b8ae71926290f44538c931486aa3aa6498a4395195324c521d88c49926290e64654c931487a3b2a6498a43d1195324c521c88ca9926290ec6644c931487623226498a43d1951324c521e88a89926290ec532d813148762b126218a432b9d36388521d4cc820c4290ec5638c62148763b1a6310a43179ce64d41218bae7326a090c3e7498f504861eba4c7a8243d14c931d41218f6eca80a090e3771590504871a38ac828243879926314121c3ac9318a090e1e6458c504870eb22c6282431d5db4114121c6ac9a08a090e5563d04504871ab2082282439558c4114121cacc730ea810e5563987540863b38cc72a04317dcd60950218b8e6b04a810c5e73181540862eb98c0aa0430fdd95415021c72a8b00a810e5563984540872d31cc02a0439658e6015021c74c8b00a810e5a63580540872cb1ac02a0439c9856015021ab4e02a4a610d597015253086ab38ec929843875906494c21a3ce8304a610d1d7418253086ab388c1298431d9c76454c2187ce8302a610c3d74181530862f3b6a8a9843179d85454c21ab4e02a2a610d597015153086ab38ec8a9843559c66454c21c3ac8322a610d1e74985530868eba4c2a984347dd16054c21a38e8b02a610d5471581530868f3a0c0a9843475d06054c21aace2302a610c5f7654c530863b38ccba18431e9c065d0c218f2e032e8610c7575987430872aa9cc3a1843395ca61d0c218eeeab0e8610e5553587430863b388cb218431d5d66190c21caca730c8610e55539864308672b94c3218439594d6190c21caaa6b0c8610c7671995430868e3a2a6a18431d9c46510c218f4e03288610c7970194430868eba4a621843179cf65904218bae7b2c8210c5d7598e410862fbaac72084317dda53904218baed29c8210c5f7654e410862ebb2a7208438b9526290421c9ca73148210e4d5398a410
  | 18 => 0x4c431b8ee4b026218dc472581310c7a2a92c098863659d0604c431b2ae83026218dc672181310c6e2b90c098863d1548604c4319aeec98ea018ec6624c7500c762b1263a8063d194931d4031e8aa498ea018f45524c6500c637b92c9280631b1c96494031e8ca498aa018f45524c5500c637390c8a80631b5c86454031caeec98aa018e54764c5500c72a32262a806395d893154031ea6e098aa018f50704c5500c636bb4a4280638b9925214031c5ac9290a018c6f76548500c717322a4280638b59152140319aeec988a018e96644c4500c74ab226228063b19893114031d8ac4988a018f45524c4500c63dbb2a0280638e5915014031c9cc6b16a910e4d6358b548872ab1cc3aa4439958a61d5221a3ce7aa4a910d1e73d91548862f398c0aa443175cc605522187eecaa0a910d55739845488732b14c22a4438d1c564d4e21c5cc8b16a710e35649875388732b14c3a9c43479d35394e21a3ce9b1aa710c3e74181538861eba0c0a9c4317dd95314e21ccac5308a710ce57198b43887172a2c521c438d9526190e21c6aa930c8710c7a70194438863cb80ca21c43355ce61d0a21c6aa830a8510e55531853288762992c219443555cf54d06218eaeda9e8310d3574d4f418866ab9cc5a0c43879526390621c3aa931c8310e2e5458a41886aab9ea820c431ddd95410621a6eecaa08310e3776550418869aba6a620c438d5516010621a3ce9a9e6310d1e74d4d318862f3b0a698c43399ca644c621aace72a26310c767615131886cb3a6a698c43715cb534c6218ecec29a6310cd67614d31886ab3b0a698c43959d8534c621aace829a6310f457214d31886aab80a698c43559d7434c621b8ae5a1a6310d547510d318878b2a08698c43b1189324c6218beeca986310e4e535883188726a9ac418c43b1589310c62196ce9b1e4310c5f73592508862e39ac9284431d5d84194221ca8c698aa110c7b76540508872b31ac3aa2439558d61d5121ccac4b0ea890e1f5458e544872ab8cc72a2439598d61951218bce6302a890c5d73181544861fbb2a82a243475ce64151218bee6b00a890c5c73580544870eb26a729a43871cd6494d21c6cc8b0ca690c3e74181534861eba0c0a9a4317dd95314d21a3ae9318a690e6562584534863ab8ecba1a43479cf54d0d21a3ae929e8690c7571d96434863a3aac321a4395d4d6190d21ca8a6b0c8690ce472586434862eb9ccaa1a431edc16550d218f0e0b2a8690c5e7614d434863b3aec2a1a43399cb6150d218f4e03288690c7970194434862ebb4a621a43475d25310d218beeca988690c74755844348672392c221a43335ce62d0521c58a8b168290d5573d53414863bbb2a7a0a43355ce62d0521b8ae73168290ce67598b41487333acc5a0a43b19ce62d05219cae73168290ec57398b4148662b9cc5a
  | 19 => 0x530c8418e6652586420c732a92c3210634b1d15250831a5ae92908418e6552587320c733292c2190638795263904318daeb3148218c6f7558a410c636bb4a5208639398e5290431c9ac72948218c6f7654a410c72731aa5208639358d52904318beeab188218e4e63548410c726b1aa4208634d5d25110431a6eeaa088218f2652504410c6a6b90a998863565c054cc4318baed29c6218d6572152310c6b8b80a9188631d5da538c4318bcec2a26218d4d72151310c6acb80a89886393d96524c431c9ecaa926218f4671549310c7a238aa498863d154b414c431aaaeb20a6218dc672905310c6e2b948298863d154a414c431aaeeaa0a6218f4552505310c78b2a08298863d1548414c4318ecec2a26218d6572151310c6b8b80a898863555d6434c431b8ce521a6218dc57290d310c6abbaa8698863c5950434c431ccecb2926218e6765549310c7a329aa498863d19cd524c431e8ec6a926218f4743549310c7a321aa498863d150d524c431e8886a926218f4552cc9310c6aabac6498863d154a324c431e8aa41926218e5575d95310c72b3b6ca98863559d3654c431aaae5b2a6218d5570d95310c6e3396c898863715cb644c431aaaeb3226218dc672991310c6e2b94c89886355dd5644c431d2ac83226218cd676d51310c6e3396a898863715cb544c431aaced2a26218d5476951310c6ab3a4a898863c5d92544c431e28c92a26218d5572951310c6aab84a898863359d8544c431b8ce42a26218dc572151310c6e9380a898863745c0544c431aacec2a26218e5676151310c6ab3a0a898863c59d0544c431e8ce42a26218d5572151310c7a2b90a898863515c8544c431ea4e02a26218d5570151310c7a8b80a898863545c0544c431aaaeb3126218d9674989310c6caba4c49886355dd5624c431d8ac43126218cd676d49310c6e2baca498863b1d96524c431e8ecb2926218f4654949310c7a22a4a498863559d9524c431aa8eca926218d5474549310c7a3b12a498863d1189524c431aaee0a926218f4775549310c763b2aa498863d1d95524c431e8ea8a926218f4654549310c7a2aa2a498863d1151524c431e8eeca926218f4676549310c7a2bb2a498863d11d9524c431e8ee8a926218f4674549310c7a2ba2a498863d11d1524c431e8ec8a926218f4664549310c7a2b22a498863d1191524c431e8ee0a926218f4670549310c7a2b82a498863d11c1524c4319acec2926218dc672149310c7a2a90a498863359db424c4319aaeda126218d5775d09310c7a2a968498863359da424c4319aaed2126218d5675909310c6aabac8498863d154a424c431aaeeaa126218d5475509310c7a2a928498863559d4424c431aaaea2126218f4552109310c7a2a96c098863555d6604c431e8aa53026218d5775581310c6cbba2c098863651d16
  | 20 => 0x471580434c70eb2087a92638b59352949318deeca90a498d2e72d53424c66a38ac7212639358f5290931c9ac62948498cd473586424c733a92c3212639914961909319ace3b1a8498cd673d85424c63d380ca212631e5c065109319a8e2b188498cd473584424c66b38cc999263179d464cc931a9ce52a66498d9674d87324c6ab3a8c399263351c560cc931a9ce52a26498cd675185324c72b3a8c299263359d0614c9319aae030a6498ccd7298f414c70e2a2c7a0a63595cb54d05319cae531e8298dc57298f414c66b3acc7a0a63959d663d0531d8ce531e8298cd57298f414c762b94c7a0a63315ca63d05319aae131e8298d5675d0f414c72b32e87a0a639599443d05319aeed9968298ec562ccb414c66bbb265a0a63651d132d0531acae5aa08298c7776550414c6ab3a8c620a63715c86310531ba2e03188298d5675d0c414c78aaa08620a63351cd6210531a6ae9a908298d9674cc8414c66a3b26420a63b158932105319a8e6b008298e966410f314c762b166598a63a5990418c5318dce5326a098c6d72993504c61f3a4c5a82630f5d262d41318f6eca80a098e1f73590504c70e39ac8282638ddc56414131c68e2b20a098c5d76d0c504c70eb268628263875904314131c5cc9310a098e2d64988504c717322c4282638b5916214131c9e86b10a098e4c43588504c63abb682282638d5934114131ccac5a08a098e3564104504c732b1082282639398e62d5031c9cc6b16a818e6662987540c732b14c3aa0631bdc960950318d8e4b04a818c6e72181540c636b90c0aa0630fdd95415031c72a8b00a818e4e63588540c732b14c22a0639a98a6015031cd2c5300a818e3a64580540c72d31ac02a0639a9896015031cd2c4b00a818e7261580540c636bacc5218631bdd56290c31c6ca930c8618d1d7494c430c68fbaa86218631ddd56110c31ad4e02a4a418d6970152520c6a739ec929063599c76494831c5ac8324a418c6d7690e520c6b338c8729063595c64394831e1a8621ca418d2e74182520c696ba0c129063539cc6094831acce2304a418c3e74181520c61eba0c0a90631b9db54548318dcec2a2a418d6a70151520c6b4b80a8a9063539cf6454831acce3b22a418d4e73991520c6b338cc8a90638b5906454831a5ce931aa418d2d7498d520c6373b486a9063599c64354831acae321aa418d667110d520c6b2b8886a90634b9d26154831a5ae930aa418d2f74581520c6963a2c0a9063531cd6054831ac8e2b02a418d2e74181520c696ba0c0a9063539cc6054831acce2302a418c6f76548520c66ab8cc7a106317dd563d0831c9cc6a968418e4d6354b420c66ab9cc3a10639954a61d0831ccaa4b0e8418cd57198e420c72731ca5210639358e5290831c9cc6a948418e4d6354a420c66ab9cc3210639994a6190831ccaa
  | 21 => 0x727a9ac529a8317dd95314d41c9ea6b1486a0e4c5358a435072ba9ac321a839358f52949418deeca90a4a0e4d63d4a4250726b18a52128399d496190941d1cc731482a0c6e7298f5050636b94c7a8283179ce62d41418bae7316a0a0c7b76540505072731cc4282839358e6214141c9cc6b10a0a0e4d63588505072ab1e82282839958b4114141ae2e1a08a0a0c6e721815310636b90c0a988317dd95314c41c9aa6b10a620e59535805310672b94c3a1883179cc60548418bae6302a420c6f765485210726b1aa4290839a54960148419aae730e8420e4e6398a5110726b1cc5288839398d6294441c9ac6b14a220c3d76952411063abb4a920883a59516390441d8ac73148220ec66358a4110762b1ac520883a99516290441b2ce7b228220da672d9141106d339486a0883659ce42504419aae63028220ce5721814110637390c6a80831b5c863540418bce6312a020c5d7318950106aab9c82a8083595ca4154041ae4e120aa020d7070505501063dbb2a0280839658d5014041cd2c4a80a020e4e6358b54cc72b31ac3aa6639998961d5331ccac4b0ea998d2e72d5254cc697396c8aa6631b9c860553318dae4302a998c3f7655054cc6a6b94c62a6639598d6115331a9ae5aa68798ccd7298743cc7172a4c521e638b5526290f31c6ca8b0c8798d4d72d5043cc62fbb2a821e6347dd95410f31c3eecaa08798e1d5458043cc6973a6a5296630f9d06054b3187ae8302a598c6f7654852cc66ab9cc3a1663879526390b31c3aa931c8598e365458642cc666b94c7a0e638755063507318dee4b24a198c6c7259250cc62ebb087286631edd95014331c9ac7316a918e4d6358b548c72ab1cc3aa4639958a61d5231a5ce5aa4a918d2e72d91548c637390c0aa4631b5c8605523187eecaa0a918e5563984548c6b2b94c22a463395ca61d0e31c6aa830a8718d2e74d4a528c61f3a0c0a94630f5d06054a318deeca90a518cd57198f428c70f2a2c7214638d9526190a31c6aa930c8518d6572d53418c672b94c7a0c63879516390631c5ca93148318e2d5498a418c6b2b96a820c631ddd95410631a6eecaa08318e3776550418c71aaa2c020c631bdc964942318d8e4b24a118c7576106508c63dbb2a0284639358e62d5131c9ac6b16a898e5563587544c733312c3aa2639958961d5131c5ea8b14a898e4d6398a544c726b9cc52a263995c66295131cccc4b0ca898c6e72181544c636b90c0aa2630fdd95415131a5ae5320a898c6f72580544c636392c02a263395ca61d0d31c68a8b0e8698d4d72d53434c666b94c3a1a63715ca61d0d319aceb30e8698e5675987434c763394c3a1a63355ca61d0d31d8ae530e8698cc572987434c66ab84c3a1a63535cb5410d318beecaa08698cd471588434c6ab3a8c221a63715c86110d31ba2e03088698cd
  | 22 => 0x887b19896190c43d8ac4b0c8621e96545864310ecb38ec8a1887355c46050c438dce4302a221c6d721815110e3bbb2a228887995895114443ce2a2b00a221d557190d5010ead38486a8087561c143540438dce430aa021c6d721855010e3dbb2a0280879c5855014043a9ce5a9ca7a0e4f5358a53d0733312c329e83995896194f418dce4302a7a0c6d7218153d062fbb2a629e83535ca53d0f419cae530e87a0d4d7294c43d06a739ea5296839358f5294b418bce6302a5a0c5d7318152d0637bb2a429683355ce61d0b418f6eca80a1a0d4e72d4e53906a6b96a729c83539cb6494e41a9ae5b24a720d1d74d8a5390726b10c529c83559c46294e41a9ce430ca720d4d7218653906ad380c329c83565c06194e41a3ae8304a720d4e7218253906a6b90c129c83559c46094e418dce4302a720c6d72181539068eba4c4a9c83551c56254e41c9ac4312a720d567118953906a7390c2a9c83535c86154e41aace3302a720d1f74581539068eba0c0a9c83539c86054e41a9ae4302a720d5671181539062fbb2a629c839354e6214e41c9aa6b10a720c6d7598a439072729cc521c839354e6290e418deeab148720e4e5358a4390726a9ac521c839554e6190e41caca6b0c8720e5553d8543906a739ea529483535cf5294a41a9ce7b24a520d4d73d925290696ba6c7294839358c6394a41acce231ca520c6d7690e52906b338c8729483595c64394a41e1a8621ca520d4e7318652906a6b98c3294835a9c06194a41ad2e030ca520d2d7418252906a7398c129483535cc6094a41acce2304a520c5e73181529062eb98c0a94831b9db5354a418dcec29aa520d2d7498d52906b238ac6a94839358c6354a41acce231aa520c6e7690d52906b338c86a9483595c64354a41acee2a1aa520d647150d52906a7398c2a9483535cc6154a41acce3302a520d2f745815290696ba0c0a9483539cc6054a41a9ae6302a520d6671181529062ebb4a62948317dd95314a418deeca90a520e4e635485290726b1aa429483175da5390a418beeca9c8520e5653986429072aa9cc3214839594d6190a41caaa6b0c8520e6652586429070eb2ca7a0c838759553d0641c5acb2968320f0e5394b4190716b2aa5a0c839559653d0641caacaa9e8320e656594b41907a2a9ca5a0c839959552d0641e8ca6a968320f455354b419072aa9ac1a0c839954960d0641c9ca7316a120e4d5398b509072729ac5a84839354d62d4241c9cc7296a120e4d6394b509072731aa5a84839358d52d4241ae2e1a0ca120c6e7218d5090636b90c6a8483179cc62542418bae6312a120c5d7694c509062fbb2a6284839394e6214241c9aa7310a120e4e535885090726a9ac4284831b5da5214241c9cc7290a120e4d639485090637bb2a4284839398d5214241c9ac6a90a120c7b765405090
  | 23 => 0x600100000000040000000000002003000800000000000000100020010038010008001002001c00800300000000080010008000002002000801000600500000100000000000008008000000000c000000001800400000200080100000000000004000008002800000800000000100000000008000002000001000800400300200000000080060008000003000003400000e000801400400200080180040020028054000003000001400400000580040080070008020000002006000000000800100080020000038008000001002000800c0000010038000006004007400e000001805c00a002000000000000300000000020020008000000000000800000400000080000100080090014006000000000800e000000800c00200100000040000010008020004000000000400400000000000020000000000000000000000800a001000000c0040000000000000020000800c016001003000c000000000002000200000780280000020000008000007000000000000300080000020030058000002000000801400000e0000020004001000000c0000040010004000000000800400000000000000000000028014004000000000800000100380040040070010004002001000001001600200100040000010000010000004001000000000800080080000020008004040006000000800c0000000000000001001800800a008000800000000200000000040040000000002001001800000200000180080040010018000006004000801c0000030008014001599cb5194743ccac5a8ca3a1c6e7218151d0e36b90c0a8e871ddd951147438f6eca80a1a1d6672d465190eb2b96a328c874d5d74394643aaaeba1ca321f274394a5190eb3396c928c87595cb6494643acce431ca321d657218e5190eb9380c728c875c5c06394643a6ae9b14a321d567318a5190f32b10c528c874d5d06094643aace6304a321d66721825190eb2b90c128c871b9c860546438dae4302a321d3575d0d5190eaabae86a8c87d1d0e5254643e8e86a92a321d5570d0d5190e9aba4c4a8c87551cd6254643aace6312a321e65621895190eab39cc0a8c874ddd16054643a6ae8302a321d56731815190eb3390c0a8c87595c860546438daed290a321c6f765485190e3bbb2a228c87999895114643ccac4a88a321e66629475090f32b14a3a84879998951d4243ccac4a8ea121d5970d0e5090e37390c2a84871b5c861542438eaed288a121e66629445090f32b14a2284871ddd95114243cccc4a88a121e65625445090e3dbb2a028487a998a6190d43ccac5a8ca2a1c77765445150e37394c3a82871b5ca61d41438f6eca80a0a1d5970d0c5050f33314c228287999896114143ccac4b08a0a1e57435845050f33314c329887999896194c43ccac4b0ca621c3d769524310e2ebb4a921
  | 24 => 0x10000001000000400c0020000004000000000000400000100100100100000018000016000000002402601200380040000040008000000000001000000000000000000040060028000000000006000400a0050030004002001000000000401100180080020000000014002000000000000000600500100000050010004010000000800c0000020010004002000002800c010000000803800c0000008010000005000000000e000000000c01000000300040080000028010002000000001800000100480380020010000004000000002000000400300000000020220008004002002001000800000000180000040010000008002002002800800000300000180000010000004006002001801000000900380000020030008010002000001000c000000000000000000100100040020010010004000010000001000000000e802c00000c000800001e000000005400600000080080020010000004004000000000000200000200180020010000020004001002000000400700100100120010080004000000001800400200000000040020000070004004003002001800c000003800400c0010000010004002000000000200400080000020110068000008000001002c0000000000000012001002800001c0000040008000004003000000400d001800c00200000000040000030038010002001008000400800500180040040030000000024008000800800400c003001000400000300100000000000004000000000000801a0050000008000006004800001c00100080040000020010008000000000002000000a0000004000005002001800202600000040020020010000000000000000001200400d000c0000000000000000006003000400000000000040120010008010000001004000c004001004800c000000000000000c003000005000400100000240020000040010000000000800000000500000380000000020000002005001000c0000010030014002006000000000000200200000040020000000004005000000400000200280140060000010008000000000000c00e0070010004000001002801000400600080000180000000004058001000000000800a00000000060020010000000001002800800800400000000040040010008002003000800000600000180000000000010000000000001800000c000001800c0000000018000004000000001c000004000000000000100300000080000020000004001000000c000000000000400000000000000000050000000006000004003000c000000801400e0060000010000003000001c0000030000004000000000000400400700200000000090030000000000002000c002000001801c000001000800401000300000080000050088004012000001000c008000002000800000200000180
  | 25 => 0x1b746948352c936444fd78a8f8da3241b66c395dbca5542e340010620000000568eba0000000000000000368e1f40008920001938000adb1ca00000000002f725040000000000d840000003c9acd4000a2e00000000000c4801400400400180000000000000014000001000804c0000000048004002003001800401600000000040000000000010000007000000000c003003002c00400100280000000050000000000001000000001200200080380000020000000000002001000401200200000000000010000008000003000000800400700000200120000000010004000001800c0000090010010002000000800000c0000028000000000001000000c000000800000000600080080000000000000000007001000800000200080000020040008000000000000000000c002000000000a004001000c00600b000800c00000200080000000040000000002000008000000000000100040180080010000004008000000c00000000080000000000018000000006003000000a0050008004000009000000000e0000018000006002003800000800000a00000060000020008008000000003c000009005800000001100000180020070008000002001000000000000500380040040080008000000007006801c00c00800100180000010000000000002000800000400000000100000030010000002000001800400600a00000000040000040004006000002800000400100080000020010008000016000000000000a00400000000040030008000000000000000c00400100100000120020018000000000000000001e00200000040160000008000002001000802000000200180040040000008004002002001800401a000004801800600000000000040030008000000000002800c008005002000000000400080100020010008008000003000800001800600100000060010008004000003001000000200500000000000010008000000000003800000200200080000080000000018002001000000000000b008800c004000003800000a003000800000c001001801000c0010000000000005000800400400700000040000040008000000000002000400000000000080040000000000004004000004400000300000000000000000000014000000000c008003005800000000100100000060010028000000001001000c0060030000000000000000800800c00100000040160000010000002000000000c0000010000004000000002800c0040030028000000008002001c0020030008008004000001002c00000100080000000000068000008000000800400600000080000040000010000008006000003c01e001000800c00200400000000000030000024006001004000000000a0000018002001001000000c007000002000e00000000100280060
  | 26 => 0x88d80e02f85da1d1580c000000ce129f2c4e2760fc64aafc20005c3cc57204dc9b0b9f400005200003ce9e7c00000070e80000006f78000001290000000000000000000000000000000e4800055800000000012720000001b614c00000f98000d84e6c61f9b3163579400000000003541530000828add231ad30e389a60000ac400092200018700000005850001b61e730000000000adf0550000000c33288ead80009142ed8000d2270b50a000019000012e8774000bb500026722baca3317a89914806f00000000003ca00000000001a6c0b1dd40008c8000000000000000000000000000001191294a4970c099000000000023c60000001d30000000000000000000009355aa263a62000000000009a0000000000000f0c159afd7beed051118001abc0db081b4e0bc29e10003cb00000004769ecdda21a83c621f6000d6800000d7acc00000000009b20006a78001128cf02310000062d150003760a8cc2700023e4e9ebc02bb000067ec90000000000000000000017042650002d120000004f2c0017660005eab1fca7e66c4a3f3cc960803acc9af9448ea4104800000029511a38eef0d00000023372042f6000000000000000000000000003c3cdb8000da963d0000ce6d4104d1b7c1bfef32340b2426ad3b1f497f57067845cb4b350d49875ab98b81426f6bfeb785988000469edf00000000001294cb2000523eee80000004de169400000072d4478000f2976d0bad335000000000197e1d01fc0ae53e6a250000000000af62374001c2690e11b815d8faec70051e3da6000003e890dd0a00050b9a6d98ee3900011948d3b62dba80000000006d20000e725d5000000000000010025780005c23ef2cec0000006402eb9d543c42f1dbb4bb2cee1e09b6800096c68b6359b4e42302e9f1e000d746b11994cd6769425a27c2cc86e55a3d1814ce563da8001bd6a4508d2988d4c53d7410000000b87000010c000000000157819c0000000d1c5f20001738aec0004bb3120000000000000288d7019fb0000001b2a4c3429087c13267200025ecb64994695171f0b68230d189b017000051e0000af50001080000000000000000000000000007a510200000000000004e32f78001576e971c5819162400000000016dd00072a80008c50004d7942a000000000393c0006796860510e0500000000000000006b380000000000000000000000000000094c000286c9edb5d20b59580000009707268fd9366158817894820cf19800097c00000021f2bf800000000005f80008d0d9b6d1c1e08855a0800132e1fb03340003d0d222ec01ed4a81db000305101d0373309d58ec70000000000000c6b0000001cb60005ee51f40000000001f5a0000005d44001d5e000371effdb8e7f6367800000000000033881cc00049780000006b6311b0708e2dfb0000
  | 27 => 0x8649dea00000000000000000002e280e069f6a9a5adaea5d3deac0000000006b880000000003b100000000007a80000c067d1bce00019183e47130000000b7a80000000007c5000344e000bd400000000000001e463690540000000000cf40002f612c4000000310800000000043880000000001631a7248c43778f000000002000020d11d8acb0000678000dad205800000054d00000000001732ee4000000c990001ac8000000225800000015400017a379c4cf03940000000004a8ad5813ace643291080000000000000000000000000000000048c80000000006dd82bc000af21d40000e2881322388516aa000781ad9e46addd00004313443d05b1a0d4320da2c5c629c50c5a6b797a00da78d1674b16571769d1501f6876a7683af17a0000000000000000000000013700000006d98000000b66b098611c7a5320000000000000000000000000000000019a600000000007c96020d4a41b29800018e000000000000036d4cd500000000000000005d600014dc0000003cf85b6000000000184910d1ff12c9510d3a00000000000003dbb395e4a38c0003a2000000000022de00000000036b8f150970001f06692bee03fa2741c600033228a8c125dba98203c0008bf59740000009463c03acc68a69e25b00003b005b0000000000000000000000000009f00005dc9e25eef8d0e527fa00000000000000002dd97360004614001c9c000000000000000078452480000000000e25d760003c6800000000034ee588da50006e4ae68000071dbcfb601068818000a9400005335c800053e00000005edb3c3e05a79f886fa000000311cbe4195557ad14a520fd800361c00000000000015a2000000107444478234cdfe0dcf0ba0160000000d8600006319ae81e000000076c000548b97572c5455d501940002185d66a5855c00022fa9580000003f2c000000888400800000090c00000000000000bc7278f443b155d1f380000fe474800075e28873c2848ff20000002ef0000000000323c000000475198c00039d1c510854ea9699adb9b4b6880200d00016a000028434c8dc17ab0001d5c1a6393ce1bcd6826c2e799a6188dc0f279d000041c8f058b05b80002fd000000146873315800000000000d780006a0000393000000000000000015b8b1d3b30000d862564eb41cfc4424278e9734000000000202708cc8400000000000000001c880002d11b20000000cd60002669aae12198f378c00061600035657563b3000000000018940317700000000000000000000000000000000000000015948a1cc90e00fda000114800166691a00000000000000003b4c0000002ba8001ad40470000000e130000e680004ec7155b48000000000000213400012500031a9ae6000000000106444c800000000038d80000000000000c530c0000cd18003838000
  | 28 => 0x20000000000ddbc0e3e51ff0000c25000000000000070f83d1b3e00075584a0a86def16b1c9cb526fa546800142a7af5c2096000000076780018620000000001556e5580000000000000002a7c00000054330d01ac11b43200000000005e600006ce2f523919dc8f200037187b415c9b43047b0400000000000005c20003fa8cadaaa8dc06e834079249a5e4d280778821ea100015c6230000000116ac190f89260d69d9a43000000000003c272480000000002829a13e48000000000000037bad115c4eb10af8000e5c0003f91a2800067bb008000000bbe40580000000007a4acfdadc00000026600000001c864d8c9e0000003b6400050716015cd52ebbb9ddaf64a8e2914ecacb2d743c52ea5cd51f66f50d31c120000000002138e7800035e0c4574e0d70000000000d373e9c0000000002360000000000000247c00000000002d40e20000000000000ea20000000dde9400003b186e80002880000a9c00057d8000f54d0200035205a00002522a65b750005d1b1905f0dd900014983ca00000023282670000d10001bfa11360f1b940000002fc40000005bfe5d2bfc822f0b000000073bdb000000000005b180018300009d84e85c40020000022957400000029b8000000a0520e00000000000000000114a321054000d760001f2e95d66134600010907ffe4540a80018a4ccd0002e5ebc9b1e0000ec0ab41fd503800000000000037c00000000000001134c1000000000000000000308000000000000084e000126c00000027000000000003814758000a41000000000088c00000000005fc06b0870d4400040c0001cd80000006948e45df49fa3620000000000125c000fcc0000000001b1e00007ab9a9c0c87900026ec00000000005670d20004e2ed9d5ccbe78cb3d14000000000000000000041428c00000a7d9432b88f68aa0001d6c000800a018000000eca0001478c583236ef97c7af600045400000000000b100016cc4d051f17300008a980004d00000002d85ad6000e84000161ccb4b3657ec60c630ece0001c8200000000000018daa2800000016a90003f075595d49f54d41c440500002bb8dd80000001700000000e8a000000000091800010286960002091d2600052a00000000000000000c3969b9c68001cac9f4ecd0002ca27bc00014d8000b960005dfb3bd97aaa15b9ab00cc300000002518269106442708000c79689b8b80000000002864b2600000000000000000600c18000be50000001042bfe20005e8000000000289c0cc0004b200000001a00000c680008df000000000000000004740001110fe6e04000f1c6961df8000750e4f94cd37b3cc0003ad00009f800019280004096f51fc4000d9c80017c2000a6d0de98addcc9c97090000f8600000000008023391618000000dea80000019664ca0000001b4600031e
  | 29 => 0x80001c0b571000000000000000012084040000000c1400000000009a800013900004b0000b5f01ce0f94d200032e00000002e37519011ab8b8600000000000002b42404dfa501460800090076f5b0800075a00021e24102c29ed63f31e17886cd54837d42b80ff69281f97f01be0a51e57e567d96c624a167400000000011063a15ce0aa00000002668000000000000116000042e00000000000005b72ed0000d4e0003b848c085844640000000000003004bf475c1b30001bbc9174d20000000d5a347400160b00000022410860000001dcc00000000000000000000000000000000000344a82e0000000000000a664eb14140000000000000834b906512e236e27fe8001bccf2aa5c01b00013d60000000000be8000000000072a000031400000072179b58c8c6c3c367ba5d55a40b95103268000a2f00000008df28d0002fc0000000000310ca00d2400022540000000000000000000416818406d0000d280000000000148000000000000000000008840da60584800000005e00003c800000000008f600023c40000000001705b9cf230c391300005c4340272a684a9e1a19cd04ea7e90ff9b1dcfec9422bb10846cbb13b596180000a99d71f022ac82e86c000000000040a40001e2000000256454400000015a400056f0000000ea60000000859cd20000002f4867c34e0003030e865ad6d5226dba445217d13ac6d85bc64d8001d7051473ea94026da4db8711841f27cc39f86c91c20000002a61a0c00000019a04220000000001d4c3080e1a994ff3abe777000149c7eef43800000005880006440000000000001ccc2cb00004b4000000000000189a00044bb5300005ec8002341e5c0005c34da55187d7000027d86cd5f5f780000002e512a1d5600000034c800145a0007828970cfeba0a1d1d200006876c6ae5c7447c6843853de1c1085f8b05d60e00000024c51e76890000001456105b180f61bacaf88e24000102b0d9788000000a7400000017d0667000000161e00000028093a833300000017159f14035c68756000656800155c6d74b9000000000040ac000c625aa3d300000003fb0000000000000000000003000057400008f80000000049aa29f0000000012200000000013270004e6800035600000000000000000b4012800000000000000000000002298cc437a44b282400001760b00000000000002d3400058352880d000074b61d1f9f1e416c22b1ef4d343310000000000000200715c00000000000000000bc4a180002cd54a0003650000ee848f3b09e100002e46ef4a960000000000000000343098800000000000000000000003a640000000002c831841ee00013c8000120556a77cca02170000000000147000000000067d8002675e42698a4a95300000000000000000bd75d7d8a800064100025f40000000003c82b2
  | 30 => 0xc8000000000000078bb742aa54d66f900000000000000000001c96b400000000000dd400a0f95bfc2d75fa1d6f57a0004df00008fec4558fb044fc69e3ddce028f320004e098e02d400000036b74c200041b92deee282c00000012e200000000000000840000e9000000042a1e48fdfb08e7da2a553817c082a260072ecb6f48000f643ff7981338b4f42d0000001a405ff000000100597e60fb59089a91500000000002320001a50000320064c0000cb9ba164ce35c5e00000017180000000002dc180100066f0001e2600022832f800000000000000009c70002334000445ef42bba000ec81ef9d6800000062e8000000e930000001dae0004e20000c2800021a400180e000000211400000044ce5dc0000007601ef800035503a000000067e726110c00051a0002100bb1358095a75f8de9d25b60e620000007a11d32efd00000033657440000001746000cff000000000070100029f40000000000000000b3072389202608a88001d4000000062b0000000000723000072f00000000000000004dc80003820d200029f0952e752e2ea3dc388b927a88e400000000000005fe69800000012c60001cd0000000aeb8002bbeec80000003bf8d75df40e6c00090e6e038b1c318a621b3bf87c11df69321a1f329ba6050201a107e68b014100013ce05f0001db46160000000001d1600000000000006b8800000084400037508904e600000003b157e04416129c00006786e580012a6000000000000000000014105786a300023d09aa000000000000000000002fc000000000217000059d389336c000000340c0000c40000001409c2842f51c223c6040000000000ece876000069f63b8a57701838090499000313c000d340001ae078450d305338d01a70214baac00460000000000afccb1291c00179a40630c27f8000aac3a6a57c44ae080000000d1b000780c00000000042b000000000037302180003ab8fc008949eae9b6e6d18d2ce5f00018cc000aed80036e1216b235008000d908e58000001b5017426d8000262d8e6a2000051c0000001c640000006a83964000bdc0000000dc88848000000000000259a4b400000000032a562200057c0000000edc00004d9dc86450000001850000000000000000000000000000005d004c67deaf38000000fe1000443b5fba924a080014ac00061e6d925ba00000045600000000003c0746000000036898982a64e946c3128000000597000007a1b40e58000df80000001774000000293c001a3300046a0000c1a123000000175200000000000000002c00000f1bf4b5438000000a3a0000001d1279b0cc2df80000005b10000000eba76dac6dde9000000000000000014f27713100002fcfc6a6de0003afb305af385a00008c40000000002c24d2a4be4be17d4bda000531ab80668056928a1e939e00012
  | 31 => 0xf70f40000000003b400000001a600000000000000000000000000000000054800024f800057455e186c000cda00005912880005e3881964abdb93d16f40006d30a6c000f8cbd1120b069dcecf9524269cd1c01b2d72d2000000033780012d20006cc00000000007814000bc05a01c545bd2aa00007096b365aafa6f44001b2c000000000000000000031d0000e284c136d87da00000015000008c700000000008c40002c60000e2b78323802840002e4000000000000000004fa0000cd0000000c61140170c8a500015b2db74829130000f1a0004d35e5001891200000008aef822744d800000009c985a26a449f0000000090000000782747800066e30385e400000017621f000000018600007e417524700002749fc00006d4caa0004712fec000f328002c0adc2e325221d4645600000000000000004930000162000000000000000075b37e9b9a0003128000000ba820f89a54385e222a0539e8010736900000000006f229ec000000000080400052279f8f480008c345b17aa000ac7000000009600049c00006d418f3df911000000035bb1557ac00000000000004e549a329d24e00000038c00000000000000000704415800185e3606aa31f10ea6b46b6895c9560000000001354000000004400000065580000000005db265754a6bd7648000000000000000028a000000098ca460000b3b2f17ce5922b900000ce7177060000000c329ae0000000e964c81ff926083d609050036ee5300000016c366d027400000095a0000000b34d6b5ec312c00000079a80000000000000001dec65400000013910005a190ac62c0005f18000000db100031440000002d9c0015ac0e8e88fd3194251f800243c44e75921c0e4000000034600000000000000000fba77934f400000034a00000000000000c100000000006e2af2d3dc0000adae4e0e400067434bc0000006b296e50e800000000012da9164f78000000000000000000000000000009922208967ac99ce0000000001d725fc0939474e5e7cf000284e000e99e91a4fc378e653840d21b6e0000002d38000a760001e840004ac16e00018ce0005e100001c77db00000000009ff0001a21e69ec3539813c39e00000000000000000002f146f25e347e8000000ba19748001795dd021819793c15cf78fc33c31040515a000000000022a800164e0003ee0000ccc67c9df98a000019c077000000032e46000000000000003cbc00000067207d5c05000000133121a37815f000000000005453a1cc8cce1fd49c4743bc1000171d1d068b15693bd5e84ec00000017f7d696f005442143b20000afd86e6810000001d1891d0000000e2106d29290a450258c6c81220000a46000262e00000077e14240006b50cdb7988937556ed9628000a0d00000000000001da036800000005600013c300043dd7675
  | 32 => 0x63757f4001e4c2ab00000000003ee3e16d6a8eef4d107e071e8207c193891c075dd1222b1207bab2c1c35b7a57000079b856000055f1160288000cd151103159a85af9422b1800000979e3c04e82000439ad4c9da00022d000020200078b9e5b2d08fa242166c00013d00029c8000000000016000083300000015886fb67c000174a0002d08000000c5c7a3c000000f3402b02d9a3603f00000000000000003b9395e000235a8ccf9f000000000000000000000000007df0f180000001e100000000ec0000000000000000000000183a0000000001420000000000000000005b80000002de5fb8440000ba62a8000000000025440014fc8b1054800136200000012bc00033d333c000000da6f129f600000e4b4e1bfab8a7cb0001e440000001932ec70c229de1d8fa80004358a1800098800000000000000005aa00857fac397470000c4e2125e197a49e22be953c00000000000000000007d600035d96f600000000000004ee0ef92b80004d800028fcd4200000000001de2509e5c00003e00001d800078cace74c77196920006cb9a4a00009879c80002e4ef2000293170998537809641495a645feb356ebafc8000000000dd70000000bf6a06000342c00000000000000001331438000dd65126610000000000000000000000000000000000001ab37090be84c000000000078a0000000000000000000000000000018b5afc0001fb80000000000002c8e00043500000003a6da52969c800009db00000000000001d399d4710a425932df477489c00038b45e668d5f68acae8ce743f400016388930000001d8a0000000000000000590800000077c00037b936a0000000000000ca5409da43e1e63e034092832e2d30000000d8a12467b000049e6603af5a80000c09467800063218d0002de1cb0e813d03234afa31d0dcb32400000055b80010829324044259a5c0005ef0000f0c00000025480000000001560000d280001d1c0003750000000000000092400000046a4d00000fdc042229a671b153706be46a838c000000122c0000004dc0000000e410001f4000000000000006ae00000004a7a2c15e0000000000c3d800000000000054a8000000c6514920fd00600000000002960a016c8a910ccb0311321100005d4645a33b8c44401898dfd31e00000000000000000002c05ca224c55c8d79c4e0000ca000000000000015100000000000000d6f00000000000000000eabc5104465662a08840000006750000000a4b88140009283cdb47c001c409bd0168000000c180001d95524b24325b5b162097780000757076a828ab70cce81c79790001a3a0000000000fc521e0638000c889934a68066d5600067680000000002508000000000000000000000041e1796000e090001f13e2200000000003ac000065bbec000b7d8000000c170004
  | 33 => 0x37d80003788001ff6000d7c0000000104bf24df8000000000000000000000000000018e00000000000000a9a00000000000000001608ada3c06fc86740920000000000fd80000002a6d008b986b09fae000f367893cf45aa0000002b54192000000000000000006f000000043f800000000000000037f055299633eb8a4000c0d2f38000176ba44850001e1a00037f8000000999bcf028e0006cb58680000001d9389f4376960004ae0984594bcf00020e40000ad4ee80000009ae0000000000000000000000000044b40006ba0000f5b2e428c5d68002024000e6000000000003d300000019f80000001f000000000a40001b0800052e9f80a7400002a80000000cd000000173e4b401dd350c103c7bcb09f0fdef27879a5519aa20d348fab8a1fba3a7024480006ec483ac6e00000000027b000000017106b800096f8001f48000ead5532314acec22000000000000049489dc0000000000000a1d0000000001cf8cc56019f1036600033d80000000000002baa000caa000000000087000035dd31a32a6590000000000491b42807199e598d458e465a72c425920000006ae8d97608aa20dd20c0db80000000fc41d60006c00000000000000194de360004092de80006a8edf0001c6292c77880005ee00043c000103a5f7460deb9c7c00005eb854ba1b88749350c0000000001e8c0000000002fcc000000747b02096e475135aa50408cf45338001a4cd52379000007c00061b45c1e2d000000000120a0000000c840007cd5e317e080d39209100000000000c716fcb620002f152400000005aeae7a00000008028380000000001ea0f121c828c98e8000a890c31ced3d200000019080002794630000da8d7dc7780000000000003a70278f043d2800000000000017900e63360d62289de884f2c2a36edbc6d6ba8bbe581464959f290cd92d8980030812edd8b6c9b3d492200059a2831c040000000c496547dc8000001d7878b210675db63bb9227acc8000d08771bbc19060d4000000000000024b99483ce701872000000000000000000009470000000000a686ac028cbec7fa800000141073e00000000009498000001a3b0000000118b1c000044c0017f24e71d50000000c2600036fce0e8e43850a2c070e0f52a80000000a70000000da0718bf5b0100007ea2630dedb32cd02a922108e6e383ff8e7d3190001ef40011b90000003800af676c09c0c28670dbc338129d90a5b047280000008d500009c93c67052d26f98d2f00078b0000000e9100000000005b87848000000e9540c8000000000000235c000000400c82000040e0eb800000000d36af64400089a8000a300000004b2984800000000018a400055c56427dc79c51c000000104a0003f808b20000000000000000000705a515100a364b713fd2c20e245687018780006159856
  | 34 => 0x5cd60003715dc97f89c557be3319680000000000af495b000279000000000000003b74c16d79864227b12f4c31dc000000776215cd5400040d17c40007c900000001b80000002cae68827f00036487ea00000014b960997a27b03186360006bfaed372887b14990a8ab69898fd17e4e9800000000000f400056a0000000000434000000000000000008b600063722ec73c2d228a522200000000000000000000000000032d720000000cb6c9762203d8000c1f8002dfe4149c65e485b470661d3233534bccef80002bc13cc10b0360b20eee0000002bac0000ad8000e080000000dd8000db5a774670d000000b03800000000a8e26b8ce92cc1c47903a800008e650780000005de305800000000000038847a8c660003181b060004a7b02c000e44000000000098e8000000000c8200000000000006650ae9cc4000000176800078338999ce6000000001c6dbf00002fec0003ee0003f64c1c01675faf800004883734ef36e50090000002db599fa1180000016940005cedd51e4500036c8001c224a32d2c3040000002963828fc8838290800000000000006000000007a5000025cbb887383a8000000000000000000036e8b5049c7e50000f1c0a2d1c0000000d37000000000000000054198ec00000031a3aa4a40d0a80014d53a7000785179fbfe5c2d8a8000000c93000000000000037b00005d0e706ad800148e4f40000000d2000035dc2940ab87758a00000000000000000eb11a41550000000657030e3480ebb65a2e84a40006e914eab9e22a89e102f88d17088a00024dc000000073c000000de24130cc8000682800000000000000020380000000000000e7ab648001fc658a6728000fe8996c892189d96acac6862d96cb32ab9fda12cf42a42d1d7e8b32a480002f5165c000b2fd6c800000000000000000005ca3a75f1d206bbfad42dc845cae68ac97380000000000328000e6100000000000000aa8000b303df8000001770a1b00000012d49c0000000084c9f22c8000105b82019819a400000057840007f992e00000004bcb9e7a1809c3e4b200000000000000000000071c00057b4001bda00000000000000006d6185c0007e98dbe6d93aa4f025c98e5a7a59564c0000d1e04e00000000002fc18f800045b00151c800000000000000000000005b5800000000035294e40009fd5b7800043a0001a9222ce30b7759888f8682b32c29a6374b25b30c463649f2e86f4da2fa7aa93a0c0a3837ea3e716716ac763564916b1c40000000000b9065839600011780003fe800000066edcc000000000000000000000003290002d6d17aaecab01c9034e8365ca40c07b417f17800001006fd8df80017970000003d104f00003eac000ad8c6944bee440000002418e5a0b4bb74c4965000000000032d8000aed71f8000000b080003b5535acfd
  | 35 => 0xd45d000062eceb01e0001a12000000000000000000000000000000ab9d38d8c4a20002b601f000024080000007ba479ac33d4ae3c469800115c4082430000e0ce77109a868dac1e65b000b80008ab6a2bcc8b161495a6513e8ce17d5cc8000000c2180016043c4000000000000000000016e80ea0002e0175c00085d14d00014fe00012a80000009c8000345d462b5180000012ba0b20000000000000509946c0003e13788000000b5e000000170b0000a804242db00000037cc000000000261a4fc000000000000057c000000000000000021280000000ed0000000000045800176000000010a2000d7000a81700000004f012340003713d8000107608e31e172588ce405d795094f21c7396837b9986b3f6f047de191de4525590000e5a00000006e40000000000000000000004c000ed20481276eec00038f108ec131692b73c90e74d9be871a89526bdece880011bc0000000f98000000000000000000050b0000d246d5000000082000000032583b89ed80033b0000000523400082c00000013f8000a642b1800000000050c00000005b7000000000000058590da0004490000f58000ba980000000005cda2724180000000001f8e00039300000000000000000000000000247a28c0002196a00000499e4a57dc0000002a745980000000000000000be68e3944974400022f5899ac5a8c7fb00000011fd00000000001ca55558323cb452a35663000000000047c3581dd4000000000000000057fc0000003650000001074b9d64884a896a20f7950000000960738bd1c60294224a4000000782f2e31d83600000000001b3674fa858000000aa060d80018f6000000000090a000000081d776566000000000000000000000000000000150000ac904482b2000c34e2f23dc33e00013380000000000000000f7600006880000000000002030ba60004c188fce64f48c469320000d796e7a9680000001910001a086cc8000000000e1052daa74000000293800155498c000000098a0000000001052000000000000026d77facaa56e00000013880000000000000a6288e4c840000000000000001846000004000000032f160b6240000006c400000000002601ac191c380e361cdc3a4cf2000000000000000000007fa3eb0003768000000561800000000700013f100f80840f9920000b3c00036aca30000000230201e0003aa4000000000000000039439c6033ad554e5ebf341fca000920356846556631000000013310000000001b9000000038b000000000000000000000002e318800004b6c0006d600032e8b99733d888000ddc00009e00026ac019bea04280013220005678ad400064000000011ba5df5c73c000000003670a61e50709643a425e9caef2d7858d33249e00000010418820002fac0000003b53105c6e0005e428edd1ac2900023d
  | 36 => 0x9d724000000167c3d40004f2b99c3c80000000000f077e183b800000000062f8000000a2c00000000000000000000000000424370479a49f0000000db6ae8d9780000002965020000000000000026d980f1a56122f00008174649358c1ea4880018fc00000000000013d09801140148faa6110002c08000000521c0015500003784000bca0000000001b5700062700a800039800000011f800068d105400000035940016ca7f7000256048087e8003405a8e77037380000000000f00000000000134287dc4812f70c963c29a0006bd3c8771a39700000000000000000000000000665b0b56c8a0b6beab154d4d3f51b91a4000a1d3d2c001dd600064e00010c4000000000000045c0000001d06763000000000099b00016b000000000000000000003dc20450ce00014280000008e18002d7000048a3e2d4d0000f2d3410000588b0500000010004c21be0000000810000229ae1e1b15fd0da00006b3690800069e0006d55ab15040000001d601da0002eac000000a5200036855ce000566390caf20000000a0d50800000000000000000001496000000000072f97691c0000000000000000000000000026880000000000000fc00001cc00022da33294e5acb4720000002f4c5940000000ea000000000055200000000000002eb404ab584b79759726b6a1848f70000bf480000000006ca29c3a782ec00072a400000000044c80014bc003000000030a0000000000c3486f23a0000000bf193008ec000f073bd22809ee3595108000000af28000bbd68b0002dd82ac000000000000031900000000001f6000000000000000066f80000000000002900000ca400003a0000a5f00000000000004a80e8ce1a1b63b00b7dbd3994aab92e1a280005389be0a6c4e10000000000b8280000006a60000000000000000436a79b2f000021900000b20006d317bfdac0002bc0000000e4900024000000005378000342ada0000000000000000000000047a45f0000fa2cb511eac38840d100002cee22400000000000004bd0000000000035000000139800000031308cc0000000000000000015baf975b7b90000c3cd068b20000000d6dd3e0b880006be57f58d00004ccb744431b7e000274ccbc531cf60007290001cf2a8b49d800000000000033c40000000000000000000203a5fdb440000002b85142976000000089000000000000007bc0000030000eed4c580018e4000181800000097400003a492c98e0002f6c0000001228001c340000003015c2cae90000001e048fe16380005b00000002da0a0c000728000163941e0000c957ec978890b2c0f9b87e6a50000000000046284abdd0000000b74000ad003c3a846c600079393cc804000000000000020c000000000072a4fcb7716fd000000000000065f1579c0efe859e1d006b45d400033e2b9427eed
  | 37 => 0x6214507bd91459639600001bec320468fd093a0160a09ea43f2f268542b787b20796ce1690d2e314000380d5a649379db6f477724e8000e11c2195671980000000001a69d10000af58000000000324737a36cc860002b50001e902b2615000000074bf432ef3a2481441716f226e33c0001ce00005eb0001c940000000000000918a53000000162e04c61a80000006e20001f200000000000000c2a8630002346c6a298800173a00014a8000000000000000000000025b1019faa000aec08b856b494cdd0000000000d0f0001993e207813fffac18630003ea22bc1b200020690658920006d3f9d80000001518000ca29a33a9000139400070d98800a0c8600034f00009b71c3341c000a8a3c82ac80000000003ab0d0100000000010a2000706800000000000007397640fa3c8c000d525e1f4f800081e00000013a8000000000000000019180000000000000001ae78b0000540000000000000000004780000000000e6000000000000007492ab16b624cc29de762241c564d000000070e00000017f90d60000002352000bdf000267670a00000004832220001fca4f4000cb772100000004590001128e8a0000000000000000000000000051100000000000000000000000e3a59c8000d538180000000528edf30038d800011400003f4d48000000154d5e2000000043ca14399323998e0000006a580000005b4d802f88000000000000000000033fd47c00000000000018b4d1133b2e565e838f1e580000000000001588000a4d421204a00000059cd37cf680000002a8c00036d6e0290a124ecc297b2b0a068050001960000e6e0000f6c000e074d08000ef05615ad0000000000748267dda8df20003c5e000b8f3ab400000000000000000005b574e80000000004f510cc00010479c0000df503a000000000000000018191e164c360800000000057980000006f4000000000000000000000003ec00010d800000076230014000004239c7c000e2a0000001a3e93377e800000000037f202b26a50c4840000000000451f81000022a800000000000000000000000001d2906000000000022dc65a00000730e00000001c1ee0060800074a00012545a25f0c00000009c45140018c676e0002f840006100000000000787000000000022a0002de5df57c20000000d5c43f55c2960ddcd0d0000000e620000000000000d035cc4000df7af7000126c00052680000000003998000e6dade249000000000000077124900001020000000000c730002d48000cdc3eed2e800000078c8ee00001b81db8000b0800000008e1af00000000f5cddf132269362f82ab63800000147a6c03f4400000050bd772524000000000280cf5a0004de6e85a567d3070000059e00070f1e688580b3696b0aa08237e69a8b685f60005f2187cf4e05e0000000000da009974
  | 38 => 0x6e233e9e9e614800035400000000012a80004da3ddc0000007032db000067667e937a7d9ce4e3557a800041700059f423b3c5328508bb9400023a31110e48da00004a95d60000000e2baa077c60c80000002380002732738000000000271ea2e7ac00000000003cf00000010aa21c4c8c000000000000000000000000000004dc0006c1209c188f2203000010a000046592f00009d30000000ddda7a0003298000bec560a7688506e5f539270000000000272c4407e103a4000ee800077b87b0ec216071d92fc57ab85000255ce3a2aecd29a4f5f88596800f8f6523a90001a120000000000000000b190c9b63381e4ad49080008e05d24d05144aa20000000000882bda000000109200008b00000000001dc8000000000000000104800067f00000000c3000000000000078077b14d89ac000173e000af49660ff0000e5400000000007f300013780000006c0800131443d03700cd67000014e11d838491b00011f97121f45860f880000000001f5200035a27d90ed7d200019a800000000014c8000f48b0ac92bbbc198dca00000011fee010001ba200020518a8000cd40000001e5c000bdd35f8079ba10006d2c0013e8d9d00000007a20000002cdd8a00000000000d2d000650000187978e30200000000003cc00000000006b194a000000000007f0f622150000001b41ccf00016f804c00005207f80000003a532a000030d6e9a611970bd3000238c0045d00bb94f19c046f000153cefa000000094c0000002899abc0000000002a1556200041795ac00000069b34cc00a233000397800077b2c49f4a0008a580000015e3b95263b30c0003bd0f0c0015ae8e749e37c40d2a8107bb34800094b4b3800000000000007d8000cc8254163400092b0020000000000000000000000000025e4000a4b00038140000003f38001842d0f8318000000000477385c0000002b813e02300000000000b460004363812d4e0004488000000d39000096800000000000011180000000001cc650f0002016a9281dc2f21fc000eb700000017a072875f8000d2bb8b00022d000018b378d5657c0c75000000000050e6c6ceb0000f186c2a6c8e1f8c38000716000534e4e8a5e000b358001094000000147a8780000000001390d0a00075eb6d0542742601379c00000061f0934000740785567000053b4b9b9e93a954101900014f000057c8001e62e7e403bba4f10b7f0000000000d8a6eabc7cce208f0b5892d0e44786161ed8f0a21a4e83a696a23
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x46114d40c51615c06114d40c47635ca63d4540c4573d8a62d4540c45635c86314540c51635c06314540c45735886214540c61625c06214540945829c7534c540945829cf514c540a458114d620c540c4573588510c540a4582195310c540c1475991310c540a4485589310c540c4675589310c540c4475589310c540a4786d49310c540a4586149310c540945839cb5148540c45635c85108540a45831952108540c24759912108540a448558d2108540c467558d2108540c447558d2108540a4786d4d2108540a458614d2108540c45725846194c40c45725846154c40c45635c86394440c45735886294440c45635c86354440c45735886254440945821c5534c440945821cd514c440a458194d620c440c457358a510c440a4582d95310c440a4785589310c440c4775589310c440c4575589310c440a4586949310c440a4586549310c440945831c95148440c45635ca5108440a4583d952108440a478558d2108440c477558d2108440c457558d2108440a458694d2108440a458654d2108440a148654c6150040e05531886150040c147618d5150040c24761895150040e04631895150040a458298d51d0730945829c6544c730945829d7414c730c24745895114530c45635c85110530945829c6544c530945821d4414c530c45635c85108530864875952108530a24845952108530c467558d2108530991811c14350130a19859916010c30d12745c04354430a4785589310c430e0654589310c430e0554589310c430a4586949310c430c45635ca5108430c477558d2108430c457558d2108430e065458d2108430e055458d2108430c45535ca61d0f10c457354a61d0b10945829ce544c710945829d7434c710945821d4434c710945839ca5448710945839d74248710945831d44248710c45535c8614c310a0c8454d6214d10a458214d6110d10c45725c46354910c0c7458d5214910a45811c96314910a4583149611091084c87595320c910a0c84595320c910a458214d610c910a4583149610c910a46854c9610c910a44854c9610c910945829ce544c510945821d4434c510950855c0434c510a4486549324c510b0484549324c510945839ca5448510945831d44248510960855c04248510b048454d3248510991831c141501109a1821c14150110a458214d61cc110a458314961c8110a458294d610c810a4583949610c810a47854c9610c810a45854c9610c810e06544c9610c810e05544c9610c810a31859916010410e126454d6010410e22645496010410a458154d620c410a4582d95310c410a4785589310c410e0654589310c410e0554589310c410a4586949310c410a4586549310c410c45635c55208410a4583d952108410a478558d2108410e065458d2108410e055458d2108410a458694d2108410a458654d2108410
  | 1 => 0x19468790d524c431945829d3654c431947825c3654c431945859cb644c431947825c2544c431d41729c0544c431c52765c0544c431d12745c0544c431d42725c0544c431d41725c0544c431b4180152524c431916849d9524c43194687d51524c431a4686d51524c431b4280151524c431b4180151524c431b0684dd9524c431b0584dd9524c431b06849d9524c431b05849d9524c431a4686dd1524c431a46869d1524c431d05741d1524c43194687d91524c43194587d91524c43194687991524c43194587991524c431e0564191524c431a44865c1524c431b07845c1524c431b04845c1524c431a46861c1524c431b06841c1524c431b05841c1524c43185686dd7424c431c467654b424c431c457654b424c431c467654a424c431c457654a424c431b0484549424c43194687549604c43194487549604c431d0774549604c431d0474549604c431945859c8604c43194787548604c431d0674548604c431d0574548604c431a45821d93154031a45821913154031b11841c13154031a47865493114031c47765493114031e06645493114031e05645493114031c457358a6115221c46765c8534c621951801d4434c621c45725c663951218c5831c96010521951801d4434c521944855c8434c5218e1801d8424c521b0684d95324c521a4685991324c521a4686951324c521a8684d8d3188521c45535ca61d0c21c45535ca6190c21b06849c95348421b05849c95348421945859ce42484219478754e42484219458754e4248421945839d36548421947835c36548421945859cf6448421947835c25448421d41739c05448421c62765c05448421d22745c05448421d42735c05448421d41735c05448421b41801525348421926849d9534842194687d515348421a4686d515348421b42801515348421b41801515348421b0684dd95348421b0584dd95348421b06849d95348421b05849d95348421c45761d95348421a4686dd15348421a46869d15348421d05741d1534842194687d91534842194587d915348421946879915348421945879915348421e05641915348421a44865c15348421b07845c15348421b04845c15348421a46861c15348421b06841c15348421b05841c1534842186686dd74348421961801d74348421c457654f4348421c467654e4348421c457654e43484219448754d4348421b048454d43484219468754d60484219448754d6048421d077454d6048421d047454d6048421945859cc60484219478754c6048421d067454c6048421d057454c6048421a45831d92154021a45831912154021b21841c12154021a478654d2114021c477654d2114021e066454d2114021e056454d2114021945821c5534c640945821cd514c640a4582d95310c640945831c95148640a4583d952108640c4572d8661d4d40c457258
  | 2 => 0x9002781928670000f8c0259dc481fa018b43e81a2f1346e0320081e8cdcc69e1a755aa140ee1d248000be9096c5e01c000fc39854598865390a58814531f26908279a180000837000282020006613197540007519f40a462a5962249e40114570e4001e40b952352224c08071872748527a00a8119216190708da0008500172000b6060440000063dbe7d8688b88a478ea0d20a7292e8023b00048000002e9de28800580006300000000000560010800000000000006a002320d82c8f8f8660004a8203106e1f8c862958000000008e0000074188088006e8840002800000001b0775b40014434846001ce841f4139d844228330e2379c4490d68e8945e940679ec64e344d9263a1fc6546c0e8881913e7b8386183c698b05a8784f220681480a8013d1bc8780012cce4b0104590c308f28517c558ae7c040000e026180269a10b4165d22c3d84d4681b011a94105a8d88c000ac000008c5c81292209a0e1f00075800871b628d1c0653a6a164002492a80e1d8c68e19a32a16519da000a16b9f83604f3c1381c0002a07a04a2a5b9ac00024000002c800001e23400063994000925f9a25285c0000f84912298416c9821791803168418421820c241918c1ea2702b5d830579547823c3f800912084ca26509fe70184188002e17089000000a43b15a43800010000018050004000080100200088185000038240a000801414010800002040180c0a1b2302406190800444000186002161d000000402000000500008280103840041f0b0003a1c130000e16030081000018041801008501a080187c220800020000400800062e16814081d0580002010002002050587c003f951811c14354043951831c14154041961821c14154041a458298d6115331c45635ca6115231c45735c662951318c5821c56010d318d1801d932105318c5821cd6010531a458198d52d0831c457354a61d0831a458198d5290831c457354a6190831b06849c5524c431b05849c5524c431945859ca414c4319478754a414c431945859ca434c431b06849cd524c431b05849cd524c43
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 27
  | 6 => 1098
  | 5 => 6068
  | 4 => 3921
  | 3 => 293
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*5) 5
  | 7 => packedAt gbK7 (i*16) 16
  | 6 => packedAt gbK6 (i*27) 27
  | 5 => packedAt gbK5 (i*38) 38
  | 4 => packedAt gbK4 (i*49) 49
  | 3 => packedAt gbK3 (i*60) 60
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (6+((h/1+packedAt gbK8 (5+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (510+((h/13+packedAt gbK7 (432+(h % 13)*6) 6) % 49)*6) 6
  | 6 => packedAt gbK6 (35646+((h/500+packedAt gbK6 (29646+(h % 500)*12) 12) % 2898)*12) 12
  | 5 => packedAt gbK5 (265724+((h/2510+packedAt gbK5 (230584+(h % 2510)*14) 14) % 9942)*14) 14
  | 4 => packedAt gbK4 (212279+((h/1550+packedAt gbK4 (192129+(h % 1550)*13) 13) % 8173)*13) 13
  | 3 => packedAt gbK3 (18552+((h/108+packedAt gbK3 (17580+(h % 108)*9) 9) % 389)*10) 10
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7fe1fffffffffff03870fc3ffffffffe023fff
  | 1 => 0x83fe0f8f07c3e1ffc07f1fc70e1e1e1f1dd293
  | 2 => 0x3fff00ff803fe1fff801ff80fe01fe1e1e31c
  | 3 => 0xfc00000ffffc001fffffe0000fffe001fe03e0
  | 4 => 0xfffffff00000001ffffffffff0000001fffc00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x200001000000000000200900220200000425
  | 1 => 0x2944a31232954a92c2350d422714545d0cd292
  | 2 => 0x51886524519a88b55a8415904b5099c5616318
  | 3 => 0x191d4a48a510ccd9ab5641008d99d089b603c0
  | 4 => 0x62118c00c623110e34689a24e0010110dbb800
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeeaaaa8feeaaaa8feeaaaa8feeaaaa8feeaaaa8feeaaaa8feeaaaa8feeaaaa8feeaaaa8feeaaaa8feeaaaa8feeaaaa8feeaaaa8feeaaaa8feeaaaa8feeaaaa8, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12905
namespace PEqualNP.Outside.L_meta_12905
open PEqualNP.Outside.L_meta_12905.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_128 : Interval gbAtlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_160 : Interval gbAtlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_192 : Interval gbAtlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_224 : Interval gbAtlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_256 : Interval gbAtlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_288 : Interval gbAtlas 3 288 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 293 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 (concat bgb_3_96 bgb_3_128))) (concat (concat bgb_3_160 bgb_3_192) (concat bgb_3_224 (concat bgb_3_256 bgb_3_288))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_128 : Interval gbAtlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_160 : Interval gbAtlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_224 : Interval gbAtlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_256 : Interval gbAtlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_320 : Interval gbAtlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_352 : Interval gbAtlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_384 : Interval gbAtlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_416 : Interval gbAtlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_448 : Interval gbAtlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_480 : Interval gbAtlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_512 : Interval gbAtlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_544 : Interval gbAtlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_576 : Interval gbAtlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_608 : Interval gbAtlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_640 : Interval gbAtlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_672 : Interval gbAtlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_704 : Interval gbAtlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_736 : Interval gbAtlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_768 : Interval gbAtlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_800 : Interval gbAtlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_832 : Interval gbAtlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_864 : Interval gbAtlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_896 : Interval gbAtlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_928 : Interval gbAtlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_960 : Interval gbAtlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_992 : Interval gbAtlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1024 : Interval gbAtlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1056 : Interval gbAtlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1088 : Interval gbAtlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1120 : Interval gbAtlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1152 : Interval gbAtlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1184 : Interval gbAtlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1216 : Interval gbAtlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1248 : Interval gbAtlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1280 : Interval gbAtlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1312 : Interval gbAtlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1344 : Interval gbAtlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1376 : Interval gbAtlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1408 : Interval gbAtlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1440 : Interval gbAtlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1472 : Interval gbAtlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1504 : Interval gbAtlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1536 : Interval gbAtlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1568 : Interval gbAtlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1600 : Interval gbAtlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1632 : Interval gbAtlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1664 : Interval gbAtlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1696 : Interval gbAtlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1728 : Interval gbAtlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1760 : Interval gbAtlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1792 : Interval gbAtlas 4 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1824 : Interval gbAtlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1856 : Interval gbAtlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1888 : Interval gbAtlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1920 : Interval gbAtlas 4 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1952 : Interval gbAtlas 4 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1984 : Interval gbAtlas 4 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2016 : Interval gbAtlas 4 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2048 : Interval gbAtlas 4 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2080 : Interval gbAtlas 4 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2112 : Interval gbAtlas 4 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2144 : Interval gbAtlas 4 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2176 : Interval gbAtlas 4 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2208 : Interval gbAtlas 4 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2240 : Interval gbAtlas 4 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2272 : Interval gbAtlas 4 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2304 : Interval gbAtlas 4 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2336 : Interval gbAtlas 4 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2368 : Interval gbAtlas 4 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2400 : Interval gbAtlas 4 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2432 : Interval gbAtlas 4 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2464 : Interval gbAtlas 4 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2496 : Interval gbAtlas 4 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2528 : Interval gbAtlas 4 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2560 : Interval gbAtlas 4 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2592 : Interval gbAtlas 4 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2624 : Interval gbAtlas 4 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2656 : Interval gbAtlas 4 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2688 : Interval gbAtlas 4 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2720 : Interval gbAtlas 4 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2752 : Interval gbAtlas 4 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2784 : Interval gbAtlas 4 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2816 : Interval gbAtlas 4 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2848 : Interval gbAtlas 4 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2880 : Interval gbAtlas 4 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2912 : Interval gbAtlas 4 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2944 : Interval gbAtlas 4 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2976 : Interval gbAtlas 4 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3008 : Interval gbAtlas 4 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3040 : Interval gbAtlas 4 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3072 : Interval gbAtlas 4 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3104 : Interval gbAtlas 4 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3136 : Interval gbAtlas 4 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3168 : Interval gbAtlas 4 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3200 : Interval gbAtlas 4 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3232 : Interval gbAtlas 4 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3264 : Interval gbAtlas 4 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3296 : Interval gbAtlas 4 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3328 : Interval gbAtlas 4 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3360 : Interval gbAtlas 4 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3392 : Interval gbAtlas 4 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3424 : Interval gbAtlas 4 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3456 : Interval gbAtlas 4 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3488 : Interval gbAtlas 4 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3520 : Interval gbAtlas 4 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3552 : Interval gbAtlas 4 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3584 : Interval gbAtlas 4 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3616 : Interval gbAtlas 4 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3648 : Interval gbAtlas 4 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3680 : Interval gbAtlas 4 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3712 : Interval gbAtlas 4 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3744 : Interval gbAtlas 4 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3776 : Interval gbAtlas 4 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3808 : Interval gbAtlas 4 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3840 : Interval gbAtlas 4 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3872 : Interval gbAtlas 4 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3904 : Interval gbAtlas 4 3904 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3921 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat (concat bgb_4_224 bgb_4_256) (concat bgb_4_288 bgb_4_320)) (concat (concat bgb_4_352 bgb_4_384) (concat bgb_4_416 bgb_4_448)))) (concat (concat (concat bgb_4_480 (concat bgb_4_512 bgb_4_544)) (concat (concat bgb_4_576 bgb_4_608) (concat bgb_4_640 bgb_4_672))) (concat (concat (concat bgb_4_704 bgb_4_736) (concat bgb_4_768 bgb_4_800)) (concat (concat bgb_4_832 bgb_4_864) (concat bgb_4_896 bgb_4_928))))) (concat (concat (concat (concat bgb_4_960 (concat bgb_4_992 bgb_4_1024)) (concat (concat bgb_4_1056 bgb_4_1088) (concat bgb_4_1120 bgb_4_1152))) (concat (concat (concat bgb_4_1184 bgb_4_1216) (concat bgb_4_1248 bgb_4_1280)) (concat (concat bgb_4_1312 bgb_4_1344) (concat bgb_4_1376 bgb_4_1408)))) (concat (concat (concat (concat bgb_4_1440 bgb_4_1472) (concat bgb_4_1504 bgb_4_1536)) (concat (concat bgb_4_1568 bgb_4_1600) (concat bgb_4_1632 bgb_4_1664))) (concat (concat (concat bgb_4_1696 bgb_4_1728) (concat bgb_4_1760 bgb_4_1792)) (concat (concat bgb_4_1824 bgb_4_1856) (concat bgb_4_1888 bgb_4_1920)))))) (concat (concat (concat (concat (concat bgb_4_1952 (concat bgb_4_1984 bgb_4_2016)) (concat (concat bgb_4_2048 bgb_4_2080) (concat bgb_4_2112 bgb_4_2144))) (concat (concat (concat bgb_4_2176 bgb_4_2208) (concat bgb_4_2240 bgb_4_2272)) (concat (concat bgb_4_2304 bgb_4_2336) (concat bgb_4_2368 bgb_4_2400)))) (concat (concat (concat (concat bgb_4_2432 bgb_4_2464) (concat bgb_4_2496 bgb_4_2528)) (concat (concat bgb_4_2560 bgb_4_2592) (concat bgb_4_2624 bgb_4_2656))) (concat (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784)) (concat (concat bgb_4_2816 bgb_4_2848) (concat bgb_4_2880 bgb_4_2912))))) (concat (concat (concat (concat bgb_4_2944 (concat bgb_4_2976 bgb_4_3008)) (concat (concat bgb_4_3040 bgb_4_3072) (concat bgb_4_3104 bgb_4_3136))) (concat (concat (concat bgb_4_3168 bgb_4_3200) (concat bgb_4_3232 bgb_4_3264)) (concat (concat bgb_4_3296 bgb_4_3328) (concat bgb_4_3360 bgb_4_3392)))) (concat (concat (concat (concat bgb_4_3424 bgb_4_3456) (concat bgb_4_3488 bgb_4_3520)) (concat (concat bgb_4_3552 bgb_4_3584) (concat bgb_4_3616 bgb_4_3648))) (concat (concat (concat bgb_4_3680 bgb_4_3712) (concat bgb_4_3744 bgb_4_3776)) (concat (concat bgb_4_3808 bgb_4_3840) (concat bgb_4_3872 bgb_4_3904)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_32 : Interval gbAtlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_64 : Interval gbAtlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_128 : Interval gbAtlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_160 : Interval gbAtlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_224 : Interval gbAtlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_256 : Interval gbAtlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_288 : Interval gbAtlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_320 : Interval gbAtlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_352 : Interval gbAtlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_384 : Interval gbAtlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_416 : Interval gbAtlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_448 : Interval gbAtlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_480 : Interval gbAtlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_512 : Interval gbAtlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_544 : Interval gbAtlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_576 : Interval gbAtlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_608 : Interval gbAtlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_640 : Interval gbAtlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_672 : Interval gbAtlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_704 : Interval gbAtlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_736 : Interval gbAtlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_768 : Interval gbAtlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_800 : Interval gbAtlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_832 : Interval gbAtlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_896 : Interval gbAtlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_928 : Interval gbAtlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_960 : Interval gbAtlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_992 : Interval gbAtlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1024 : Interval gbAtlas 5 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1088 : Interval gbAtlas 5 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1120 : Interval gbAtlas 5 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1184 : Interval gbAtlas 5 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1216 : Interval gbAtlas 5 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1280 : Interval gbAtlas 5 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1312 : Interval gbAtlas 5 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1376 : Interval gbAtlas 5 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1408 : Interval gbAtlas 5 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1440 : Interval gbAtlas 5 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1472 : Interval gbAtlas 5 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1504 : Interval gbAtlas 5 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1536 : Interval gbAtlas 5 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1568 : Interval gbAtlas 5 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1600 : Interval gbAtlas 5 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1664 : Interval gbAtlas 5 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1696 : Interval gbAtlas 5 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1760 : Interval gbAtlas 5 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1792 : Interval gbAtlas 5 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1856 : Interval gbAtlas 5 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1888 : Interval gbAtlas 5 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1952 : Interval gbAtlas 5 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1984 : Interval gbAtlas 5 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2048 : Interval gbAtlas 5 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2080 : Interval gbAtlas 5 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2112 : Interval gbAtlas 5 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2144 : Interval gbAtlas 5 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2176 : Interval gbAtlas 5 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2208 : Interval gbAtlas 5 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2240 : Interval gbAtlas 5 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2272 : Interval gbAtlas 5 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2304 : Interval gbAtlas 5 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2336 : Interval gbAtlas 5 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2368 : Interval gbAtlas 5 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2400 : Interval gbAtlas 5 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2432 : Interval gbAtlas 5 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2464 : Interval gbAtlas 5 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2496 : Interval gbAtlas 5 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2528 : Interval gbAtlas 5 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2560 : Interval gbAtlas 5 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2592 : Interval gbAtlas 5 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2624 : Interval gbAtlas 5 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2656 : Interval gbAtlas 5 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2720 : Interval gbAtlas 5 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2752 : Interval gbAtlas 5 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2816 : Interval gbAtlas 5 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2848 : Interval gbAtlas 5 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2880 : Interval gbAtlas 5 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2912 : Interval gbAtlas 5 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2944 : Interval gbAtlas 5 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2976 : Interval gbAtlas 5 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3008 : Interval gbAtlas 5 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3040 : Interval gbAtlas 5 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3072 : Interval gbAtlas 5 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3104 : Interval gbAtlas 5 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3136 : Interval gbAtlas 5 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3168 : Interval gbAtlas 5 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3200 : Interval gbAtlas 5 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3232 : Interval gbAtlas 5 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3264 : Interval gbAtlas 5 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3296 : Interval gbAtlas 5 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3328 : Interval gbAtlas 5 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3360 : Interval gbAtlas 5 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3392 : Interval gbAtlas 5 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3424 : Interval gbAtlas 5 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3456 : Interval gbAtlas 5 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3488 : Interval gbAtlas 5 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3520 : Interval gbAtlas 5 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3552 : Interval gbAtlas 5 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3584 : Interval gbAtlas 5 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3616 : Interval gbAtlas 5 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3648 : Interval gbAtlas 5 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3680 : Interval gbAtlas 5 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3712 : Interval gbAtlas 5 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3744 : Interval gbAtlas 5 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3776 : Interval gbAtlas 5 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3808 : Interval gbAtlas 5 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3840 : Interval gbAtlas 5 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3872 : Interval gbAtlas 5 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3904 : Interval gbAtlas 5 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3936 : Interval gbAtlas 5 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3968 : Interval gbAtlas 5 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4000 : Interval gbAtlas 5 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4032 : Interval gbAtlas 5 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4064 : Interval gbAtlas 5 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4096 : Interval gbAtlas 5 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4128 : Interval gbAtlas 5 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4160 : Interval gbAtlas 5 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4192 : Interval gbAtlas 5 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4224 : Interval gbAtlas 5 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4256 : Interval gbAtlas 5 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4288 : Interval gbAtlas 5 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4320 : Interval gbAtlas 5 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4352 : Interval gbAtlas 5 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4384 : Interval gbAtlas 5 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4416 : Interval gbAtlas 5 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4448 : Interval gbAtlas 5 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4480 : Interval gbAtlas 5 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4512 : Interval gbAtlas 5 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4544 : Interval gbAtlas 5 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4576 : Interval gbAtlas 5 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4608 : Interval gbAtlas 5 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4640 : Interval gbAtlas 5 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4672 : Interval gbAtlas 5 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4704 : Interval gbAtlas 5 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4736 : Interval gbAtlas 5 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4768 : Interval gbAtlas 5 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4800 : Interval gbAtlas 5 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4832 : Interval gbAtlas 5 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4864 : Interval gbAtlas 5 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4896 : Interval gbAtlas 5 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4928 : Interval gbAtlas 5 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4960 : Interval gbAtlas 5 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4992 : Interval gbAtlas 5 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5024 : Interval gbAtlas 5 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5056 : Interval gbAtlas 5 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5088 : Interval gbAtlas 5 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5120 : Interval gbAtlas 5 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5152 : Interval gbAtlas 5 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5184 : Interval gbAtlas 5 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5216 : Interval gbAtlas 5 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5248 : Interval gbAtlas 5 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5280 : Interval gbAtlas 5 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5312 : Interval gbAtlas 5 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5344 : Interval gbAtlas 5 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5376 : Interval gbAtlas 5 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5408 : Interval gbAtlas 5 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5440 : Interval gbAtlas 5 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5472 : Interval gbAtlas 5 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5504 : Interval gbAtlas 5 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5536 : Interval gbAtlas 5 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5568 : Interval gbAtlas 5 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5600 : Interval gbAtlas 5 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5632 : Interval gbAtlas 5 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5664 : Interval gbAtlas 5 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5696 : Interval gbAtlas 5 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5728 : Interval gbAtlas 5 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5760 : Interval gbAtlas 5 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5792 : Interval gbAtlas 5 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5824 : Interval gbAtlas 5 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5856 : Interval gbAtlas 5 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5888 : Interval gbAtlas 5 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5920 : Interval gbAtlas 5 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5952 : Interval gbAtlas 5 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5984 : Interval gbAtlas 5 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6016 : Interval gbAtlas 5 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6048 : Interval gbAtlas 5 6048 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 6068 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896))) (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))) (concat (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280))) (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)))))) (concat (concat (concat (concat (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)) (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664))) (concat (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760)) (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)))) (concat (concat (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952)) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240))))) (concat (concat (concat (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)) (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432))) (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)))) (concat (concat (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)) (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816))) (concat (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912)) (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008))))))) (concat (concat (concat (concat (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 (concat bgb_5_3136 bgb_5_3168))) (concat (concat bgb_5_3200 (concat bgb_5_3232 bgb_5_3264)) (concat bgb_5_3296 (concat bgb_5_3328 bgb_5_3360)))) (concat (concat (concat bgb_5_3392 (concat bgb_5_3424 bgb_5_3456)) (concat bgb_5_3488 (concat bgb_5_3520 bgb_5_3552))) (concat (concat bgb_5_3584 (concat bgb_5_3616 bgb_5_3648)) (concat bgb_5_3680 (concat bgb_5_3712 bgb_5_3744))))) (concat (concat (concat (concat bgb_5_3776 (concat bgb_5_3808 bgb_5_3840)) (concat bgb_5_3872 (concat bgb_5_3904 bgb_5_3936))) (concat (concat bgb_5_3968 (concat bgb_5_4000 bgb_5_4032)) (concat bgb_5_4064 (concat bgb_5_4096 bgb_5_4128)))) (concat (concat (concat bgb_5_4160 (concat bgb_5_4192 bgb_5_4224)) (concat bgb_5_4256 (concat bgb_5_4288 bgb_5_4320))) (concat (concat bgb_5_4352 (concat bgb_5_4384 bgb_5_4416)) (concat bgb_5_4448 (concat bgb_5_4480 bgb_5_4512)))))) (concat (concat (concat (concat (concat bgb_5_4544 (concat bgb_5_4576 bgb_5_4608)) (concat bgb_5_4640 (concat bgb_5_4672 bgb_5_4704))) (concat (concat bgb_5_4736 (concat bgb_5_4768 bgb_5_4800)) (concat bgb_5_4832 (concat bgb_5_4864 bgb_5_4896)))) (concat (concat (concat bgb_5_4928 (concat bgb_5_4960 bgb_5_4992)) (concat bgb_5_5024 (concat bgb_5_5056 bgb_5_5088))) (concat (concat bgb_5_5120 (concat bgb_5_5152 bgb_5_5184)) (concat bgb_5_5216 (concat bgb_5_5248 bgb_5_5280))))) (concat (concat (concat (concat bgb_5_5312 (concat bgb_5_5344 bgb_5_5376)) (concat bgb_5_5408 (concat bgb_5_5440 bgb_5_5472))) (concat (concat bgb_5_5504 (concat bgb_5_5536 bgb_5_5568)) (concat bgb_5_5600 (concat bgb_5_5632 bgb_5_5664)))) (concat (concat (concat bgb_5_5696 (concat bgb_5_5728 bgb_5_5760)) (concat bgb_5_5792 (concat bgb_5_5824 bgb_5_5856))) (concat (concat bgb_5_5888 (concat bgb_5_5920 bgb_5_5952)) (concat bgb_5_5984 (concat bgb_5_6016 bgb_5_6048))))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_32 : Interval gbAtlas 6 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_64 : Interval gbAtlas 6 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_128 : Interval gbAtlas 6 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_160 : Interval gbAtlas 6 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_224 : Interval gbAtlas 6 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_256 : Interval gbAtlas 6 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_288 : Interval gbAtlas 6 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_320 : Interval gbAtlas 6 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_352 : Interval gbAtlas 6 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_384 : Interval gbAtlas 6 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_416 : Interval gbAtlas 6 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_448 : Interval gbAtlas 6 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_480 : Interval gbAtlas 6 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_512 : Interval gbAtlas 6 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_544 : Interval gbAtlas 6 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_576 : Interval gbAtlas 6 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_608 : Interval gbAtlas 6 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_640 : Interval gbAtlas 6 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_672 : Interval gbAtlas 6 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_704 : Interval gbAtlas 6 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_736 : Interval gbAtlas 6 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_768 : Interval gbAtlas 6 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_800 : Interval gbAtlas 6 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_832 : Interval gbAtlas 6 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_864 : Interval gbAtlas 6 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_896 : Interval gbAtlas 6 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_928 : Interval gbAtlas 6 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_960 : Interval gbAtlas 6 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_992 : Interval gbAtlas 6 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1024 : Interval gbAtlas 6 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1056 : Interval gbAtlas 6 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1088 : Interval gbAtlas 6 1088 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1098 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)))) (concat (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 27 := bgb_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allgb_3 i (by omega) hi
  · exact allgb_4 i (by omega) hi
  · exact allgb_5 i (by omega) hi
  · exact allgb_6 i (by omega) hi
  · exact allgb_7 i (by omega) hi
  · exact allgb_8 i (by omega) hi
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

theorem boundgb (cert : Complete gbAtlas) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfeeafeeafeeaaaa8feeafeeafeeaaaa8feeafeeafeeaaaa8feeafeeafeeaaaa8feeafeeafeeaaaa8feeafeeafeeaaaa8feeafeeafeeaaaa8feeafeeafeeaaaa8
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813546 * 2 ^ 32 + 4276791976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
theorem binaryLower (low : Lower true fullRoots fullWord 10)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 10 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_12905.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.or,[1,2]⟩,⟨.and,[6,7]⟩,⟨.or,[0,8]⟩,⟨.and,[1,2]⟩,⟨.and,[0,7]⟩,⟨.or,[10,11]⟩,⟨.or,[3,12]⟩,⟨.and,[0,6]⟩,⟨.or,[13,14]⟩,⟨.and,[9,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813546 * 2 ^ 32 + 4276791976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813546 * 2 ^ 32 + 4276791976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
    refine ⟨⟨mono, 16⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 11 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_12905

open PEqualNP.Outside.L_meta_12905 in
theorem PEqualNP.Outside.L_meta_12905 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813546 * 2 ^ 32 + 4276791976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813546 * 2 ^ 32 + 4276791976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
