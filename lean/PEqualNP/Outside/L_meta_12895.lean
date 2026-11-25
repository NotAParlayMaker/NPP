import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12895.Model
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


end PEqualNP.Outside.L_meta_12895.Model

namespace PEqualNP.Outside.L_meta_12895
open PEqualNP.Outside.L_meta_12895.Model
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

end PEqualNP.Outside.L_meta_12895

namespace PEqualNP.Outside.L_meta_12895
open PEqualNP.Outside.L_meta_12895.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x28c903815400125138030989073c9101a18001001684029004c0232e1019f00200002c3ca8e1a6ce80008888000180804a0000421ce04004d00244cff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41f641fd41f541fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841fc21082fca0107fd0020ff20041fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887f90710fb20e21fd41c43ea83887f10710ff98e21fe31c43fa63887f0c710ff90e21fe21c43fa43887f08710ffa0621fe40c43fa81887f10310ff98621fe30c43fa61887f0c310ff90621fe20c43fa41887f08310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff99421fe32843fa65087f0ca10bea8c21ff41843fc83087d90610fea0c21f541843f883087fcc610fb98c21fe31843fa63087f0c610fa18c21ff21843ee43087f88610fe90c21fc21843e843085f94210ffa0421fe40843fa81087f10210ff98421fe30843fa61087f0c210ff90421fe20843fa41087f08210ff88421f710843f621087fd5110bfaa221fe54442fca8887f55110beaa221fc54442f8a8887fd4d10bfa9a21fe53442fca6887f54d10bea9a21fc53442f8a6887fd0d10ff21a21fd43443f886887fd4910bfa9221fe52442fca4887f54910bea9221fc52442f8a4887fd0910ff21221fd42443f884887fcc910ff19221fd32443f864887fd0510ff20a21f641443fa82887d50510fe20a21ff31443fc62887f4c510fe18a21ff21443fc42887f48510fe10a21ff40443fc80887f50110fe20221ff30443fc60887f4c110fe18221ff20443fc40887f48110fe10221ff10443f620887f84110fb08221ff54042fea8087f95010bf2a021be540427ca8087f55010beaa021bd540427aa8087f15010be2a021ff53042fea6087f94c10bf29821de53042bca6087f54c10bea9821dd53042baa6087f14c10be29821ff43043fc86087f50c10fe21821ff52042fea4087f94810bf29021ee52042dca4087f54810bea9021ed52042daa4087f14810be29021ff42043fc84087f50810fe21021ff32043fc64087f4c810fe190217e51043fe82087f90410fb20821fd41043ea82087f10410ff98821f731043fc62087f4c410fe18821f431043fe42087dc8410ff10821fd21043f842087d08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xd540c2faa8187f15030be2a0617e530c3fe86187f90c30fea1861fc430c3fea4187f94830bf29061fd520c2faa4187f14830ffa1061fe420c3fa84187f10830ff99061fe320c3fa64187f0c830ffa8861fe510c2fca2187f54430bea8861fc510c3fe82187f90430fb20861fd410c3ea82187f10430ff98861fe310c3fa62187f0c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7905f14f20ffa1e41fe43c83fa87907f10f20ffa1641fe42c83dc85907f50b20f6a1641fc42c83fe65907bccb20ff19641fd32c83f865907b0cb20ffa8e41fe51c82fca3907f54720bea8e41fc51c83fe83907f90720fb20e41fd41c83ea83907f10720ff98e41fe31c83fa63907f0c720ff90e41ef21c83fc43907f48720f690e41fc21c83fe81907f90320fea0641fc40c83fe61907f8c320fe98641fc30c83fea9105fd5220ff2a4417e54883faa9105f55220fe2a4417c54883fea7105fd4e20ff29c417e53883bca7105794e20fea9c417d53883baa7105754e20fe29c417c53883fe87107f90e20fea1c41fc43882faa5107fd0a20ff21441fd42883f885107fcca20ff19441fd32883f865107fd4620ff28c417e51883faa3105f54620fe28c41ff41883fc83107d90620fea0c41f541883f883107fcc620ff18c41fd31883f863107fc8620ff10c41fd21883f843105f94220ffa0441fe40883f481107f50220fca0441fc40883fe61107f8c220fe98441fc30883fe41107bc8220fd90441ff54482fea8907f95120bf2a241fd54482faa8907f15120be2a241ff53482fea6907f94d20bf29a41fd53482faa6907f14d20be29a41ff43483fc86907f50d20fe21a41ff42483fc84907b90920fea1241ed42483f884907fcc920f799241fe32483fa64907f0c920f619241ff51482fea2907dd4520bba8a41fe51483faa2907f14520be28a41f451482e8a2907fd0520ff20a41f641483fa82907d50520fe20a41ff31483fc62907f4c520fe18a41ff21483de42907f88520fe90a41ed21483f842907fd0120ff20241fa40483fa80907e50120fe20241ff30483fc60907f4c120fe18241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041fd54082faa8107f15020be2a041ff53082fea6107f94c20bf29841fd53082faa6107f14c20be29841ff43083fc86107f50c20fe218417e52083fe84107f90820fea1041fc42083fe64107f8c820fe99041fc32083fea2107f94420bf28841fd51082faa2107f14420ffa0841fe41083ec82107f50420faa0841fc41083fe62107f8c420fe98841fc31083fe42107f88420fe90
  | 2 => 0x3fea6a05fd4d40ff29a81fd53503f8a6a05f14d40ffa1a81fe43503fa86a07f10d40ffa92817f52503fca4a07f54940fe292817c52503fe84a07f90940fea1281fc42503fe64a07f8c940fe99281fc32503fea2a05fd4540ff28a81fd51503f8a2a05f14540ffa0a81bf41503fc82a07d90540fea0a81bd41503ea82a06d50540fe20a81ff31503fc62a07f4c540fe18a81ff21503fc42a07f48540fe10a81ff40503f680a07f90140df202817e54103fea6207f94c40bf29881de53102bca6207f54c40bea9881dd53102baa6207f14c40ffa1881fe43103fa86207f10c40ffa9081fe52102fca4207b94840b729081fd52102faa4207b54840b6a9081fc52103fe84207f90840fea1081fc42103fe64207f8c840fe99081fc32103fea2207f94440bf28881f651102eca2207f54440bea8881f551102eaa2207f14440ffa0881fe41103ec82207f50440faa0881fc41103fe62207f8c440fe98881fc31103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9985fd5330ff2a6617e54cc3faa9985f55330fe2a6617c54cc3fe87987f90f30ef21e61fd43cc3ba87987f10f30ffa9661fe52cc2fca5987f54b30bea9661fc52cc3fe85987f90b30fea1661fc42cc3fe65987f8cb30ef19661fd32cc3f86598770cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fb20e61fd41cc3ea83987f10730ff98e61df31cc3fc63987f4c730ee98e61fc31cc3fe43987f88730fe90e61fc21cc3fe81987f90330fea0661fc40cc3fea9185fd5230ff2a4617e548c3faa9185f55230fe2a4617c548c2faa7187fd0e30ff21c61fd438c3f887187fd4a30ff294617e528c3dca5185b94a30fea94617d528c3daa5185b54a30fe29461ff428c3fc85187f50a30fe21461ff328c3fc65187f4ca30fe19461ff518c3fca3185f94630fea8c617d518c3f8a3187fd0630ff20c61f6418c3fa83187d50630fe20c61ff318c3fc63187f4c630fe18c61ff218c3fc43187f48630fe10c617e508c3fe81187f90230fd20461fd408c3f281187f10230ff98461df308c3f661187fd5130bfaa261fe544c2fca8987f55130beaa261fc544c2f8a8987fd0d30ff21a61de434c3fa86987750d30fe21a61ff524c2fea4987f94930fea9261fc524c2f8a4987fd0930ff21261fd424c3f884987fcc930ff19261de324c3fa64987f0c930ee19261ff514c2fea2987dd4530bba8a61fe514c3faa2987f14530be28a61f4514c2e8a2987fd0530ff20a61f6414c3fa82987d50530fe20a61ff314c3be62987f8c530fe98a61dd314c3f862987fc8530ff10a61fd214c3f842987fd0130ff20261fa404c3fa80987e50130fe20261ff304c3f660987f8c130ef18261ff540c2fea8187f95030bf2a061f
  | 3 => 0x6218ff4c431ee98863f5310c7fea018ff94031bf28063fd500c6faa018ff14031ffaa6437f54c87fca990df95321feaa6437d54c87f8a990df15321ffa9e437f53c87fca790df94f21fea9e437d53c87f8a790df14f21ffa1e43fe43c87fa8790ff10f21ffa1643fe42c87fa8590ff10b21ff99643fe32c87fa6590ff0cb21ffa0e43fe41c87ec8390ff50721faa0e43fc41c87fe6390ff8c721fe98e43fc31c87fea190ff94321bf28643fd50c86faa190ff14321ffaa4437f54887fca910df95221feaa4437d54887f8a910df15221ffa9c437f53887fca710df94e21fea9c437d53887f8a710df14e21ffa1c43fe43887fa8710ff10e21bea9443ff42887fc8510ff50a21fe21443ff32887fc6510ff4ca21fe194437e51887fe8310ff90621fb20c43fd41887ea8310ff10621ff98c43fe31887fa6310ff0c621ff90c43ef21887ee4310ffd4221ff284437e50887faa110df54221fe28443ff54486fea890ff95121bf2a243fd54486faa890ff15121be2a243ff53486fea690ff94d21bf29a43fd53486faa690ff14d21be29a43ff43487fc8690ff50d21fe21a43ff42487fc8490ff50921fe21243ff32487fc6490ff4c921fe19243ff41487fc8290fd90521fea0a43f541487f88290ffcc521ff18a43fd31487f86290ffc8521fb90a43fe21487dc4290ffd4121bfa8243fe50487faa090ff14121be28243ff54086fea810ff95021bf2a043fd54086faa810ff15021be2a043ff53086fea610ff94c21bf29843fd53086faa610ff14c21be29843ff43087fc8610ff50c21fe218437e52087fe8410ff90821fea1043fc42087fe6410ff8c821fe99043fc32086fca210ffd0421ff20843f641087fa8210fd50421fe20843ff31087fc6210ff4c421fe18843ff21087de4210ff88421fb10843fd21087da4210fd48421ffa8043fe50086fca010ff54021bea8043fc50087fea7a07f94f40bf29e81fd53d02faa7a07f14f40ffa1e81fe43d03fa87a07f10f40ffa9681fe52d02fca5a07f54b40bea9681fc52d03fe85a07f90b40fea1681fc42d03fe65a07f8cb40fe99681fc32d03fea3a07f94740bf28e81f651d02eca3a07f54740bea8e81f551d02eaa3a07f14740ffa0e81bf41d03fc83a07d90740fea0e81bd41d03ea83a06d50740fe20e81ff31d03fc63a07f4c740fe18e81ff21d03fc43a07f48740fe10e817d54903fea7207f94e40bf29c81fd53902faa7207f14e40ffa1c81fe43903fa87207f10e40ffa9481fe52902fca5207f54a40bea9481fc52903fe85207f90a40fea1481fc42903fe65207f8ca40fe99481fc32903fea3207f94640bf28c81fd51902faa3207f14640ffa0c81fe41903ec83207f50640faa0c81fc41903fe63207f8c640fe98c81fc31903fe43207f88640fe90c81fc21902fca1207fd0240dfa0481fb409
  | 4 => 0xffd0a41ff21483fd42907f88520ffcca41ff19483fd32907f86520df94641ffa0c83bf41907ee8320ffd4241ff284837e50907faa120df54241fe284837554907eea720fd94e41faa9c83f453907ee8720fd90e41faa1c83f443907eea520fd94a41faa9483f452907ee8520fd90a41faa1483f442907ee6520fd8ca41fa99483f432907eea120fd94241faa8483f450907fea6a0dfd4d41ff29a83fd53507f8a6a0df14d41ffa1a83fe43507fa86a0ff10d41ffa92837f52507fca4a0ff54941fe292837c52507fe84a0ff90941fea1283fc42507fe64a0ff8c941fe99283fc32507fe82a0fdd0541ff20a83be41507fea0a0dfd4141ff28283fd50507f8a0a0df14141fbaa283b754507eea6a0fd94d41faa9a83f453507ee86a0fd90d41faa1a83f443507eea4a0fd94941faa9283f452507ee84a0fd90941faa1283f442507ee64a0fd8c941fa99283f432507eea0a0fd94141faa8283f450506fca820ffd4c41ff298837e53107faa620df54c41fe29883ff43107fc8620ff50c41fe21883ff52107fca420df94841fea90837d52107f8a420ffd0841ff21083fd42107f88420ffcc841ff19083fd32107f86420df94441bb28883ff411077e8220ff90441fb20883fd411077a8220fd50441ffa8083fe50106fca020ff54041bea8083fc50107fea998dfd5331ff2a6637e54cc7faa998df55331fe2a6637c54cc7fe8798ff90f31fea1e63fc43cc7fea598ff94b31bf29663fd52cc6faa598ff14b31ffa1663fe42cc7fa8598ff10b31ff99663fe32cc7fa6598ff0cb31ffa0e63fe41cc7ec8398ff50731faa0e63fc41cc7fea198ff94331bf28663fd50cc6faa198ff14331ffaa4637f548c7fca918df95231feaa4637d548c7f8a918df15231bea9c63ff438c7fc8718ff50e31fe21c63ff528c7fca518df94a31fea94637d528c7f8a518ffd0a31ff21463fd428c7f88518ffcca31ff19463fd328c7f86518df94631ffa0c63fe418c7ec8318ff50631faa0c63fc418c7fe6318f7cc631fb98c63ff508c7fca118df94231fea84637d508c7f8a118ffd5131bfaa263fe544c6fca898ff55131beaa263fc544c6f8a898ffd0d31ff21a63fd434c7f88698ffd4931bfa9263fe524c7faa498ff14931be29263ff424c7fc8498ff50931fe21263ff324c7fc6498ff4c931fe19263ff414c7fc8298fd90531fea0a63f5414c7f88298ffcc531fb98a63fe314c7bc6298ffd4131bfa8263fe504c7faa098ff14131be28263ff540c6fea818ff95031bf2a063fd540c6faa818ff15031be2a0637e530c7fe8618ff90c31fea1863fc430c7fea418ff94831bf29063fd520c6faa418ff14831ffa1063fe420c7fa8418ff10831ff99063fe320c7fa6418ff0c831bf28863ff410c7fc8218fd90431fea0863f5410c7f88218ffcc431ef98863fe310c7ec
  | 5 => 0x742faa8e857551d0bf8a3a17fd4342ff286857e50d0bfaa1a15f54342fe286857d5490bfea7217f94e42bf29c85fd5390afaa7217f14e42ffa1c85fe4390bfa87217f10e42bf29485ff4290b7e85217bd0a42ffa8c85fe5190afca3217f54642bea8c85fc5190bfea1217f94242bf28485fd5090afaa1217f14242ffa9a857f5350bbea6a157d4d42ff29a85fd5350bf8a6a15f14d42ee29a855c5350bfe86a17f90d42fea1a85fc4350bfe84a17bd0942ff21285be4250bfea2a15fd4542ff28a85fd5150bf8a2a15f14542ffa82857f5050bfca0a17f54142fe282857c5050afca8217fd4c42ff298857e5310bbca6215794c42fea98857d5310bbaa6215754c42fe29885ff4310bfc86217f50c42fe218857e5210bfe84216fd0842ff21085ee4210bfa84216f50842f6a1085ff5110bfca2215f94442fb28885765110bfaa2215f54442faa8885755110bf8a2217fd4042ff280857e5010bf4a0215e94042fea80857d5010bf2a0215e54042fe28085ff54ccafea9997f95332bf2a665fd54ccafaa9997f15332be2a665ff43ccbfc87997790f32fea1e65dd43ccbf887997fd0b32f7a1665fe42ccbfa85997f10b32f621665ff51ccbfca3995f94732fea8e657d51ccbf8a3997fd4332ff286657e50ccbfaa1995f54332fe28665ff548cafea9197f95232bf2a465fd548cafaa9197f15232be2a4657d538cbfe871977d0e32ff21c65fd438cbf887197710e32bf29465ff428cbfc85197b90a32fea1465ed428cbf885197fcca32ef99465ef328cbfea3197f94632bf28c65fd518cafaa3197f14632ffa8465fe508cafca1197f54232bea8465fc508cbfea8995fd5132ff2a2657e544cbfaa8995f55132fe2a2657c544cbfe86997f90d32ef21a65fd434cbba86997f10d32ffa1265fe424cbdc84997f50932f6a1265fc424cbfe64997bcc932ff19265de324cbfea2995fd4532ff28a65fd514cbf8a2995f14532ffa82657f504cbfca0997f54132fe282657c504cbfea8195fd5032ff2a0657e540cbfaa8195f55032fe2a0657c540cafca6197fd0c32efa1865fe430cbfa86197f10c32ee218657e520cbfe84197bd0832ff21065fd420cbf884197b10832ff99065df320cbfc64197b8c832fe99065dd320cbda6419734c832ffa8865fe510cafca2197f54432bea8865fc510cbfea0197f94032bf28065fd500cafaa0197f14032ffa9e83fe53d06fca7a0ff54f41bea9e83fc53d07fe87a0ff90f41fea1e83fc43d07fea5a0ff94b41bf29683fd52d06faa5a0ff14b41ffa1683fe42d07fa85a0ff10b41ff99683fe32d07fa65a0ff0cb41ffa8683fe50d06fca1a0ff54341bea8683fc50d06faa920ffd4e41ff29c837e53907faa720df54e41fe29c83ff43907fc8720ff50e41fe21c83ff52907fca520df94a41fea94837d52907f8a520
  | 6 => 0xa00000001e00202400600001200a00202000000003c00000004600000800000000400c01c00000001e00a00000000a00a00a00200800000200000e00c00800601600200000601800402c04e00800800800400201c01200000800e00a00000001a00802202e00001200e00200000200e00a04200401c00600600a01200202c00402200801a00601003000401800200200000000000202600600802401a00000c00000a01000401403c00201e01200800e00201800000e03801200600c00200601600c00000000600c00201400002601a00201200200201000201200000202001400800400203c01801401000400000202600600000000600a01601600e00001200a01000800200a00000200400001c00c00600600802a00601200200000000400001400000000e04e01601801400000800000400600400000001c00400a00002400400200404200003200000c00200000e00800000001000e00c00c00400200000000000603000800002800000800400000200400800000000801604000c00200000200001002200000401400200600200600000400401400a01600200000800600401200200c00c00400000200800c01800e08400a00600a00c00000e00001c00a00200a00200000400001e00c00000000200000000200e00000000e00e00600000a00000a00602000001a00400001e00000c00801e00e00800e00001400000600200400405200002001400800402a00200400a00200000001401e00600000000a01000000c00000601200000000200604001000000c00a008000002002002000002000012000002004004006008008003ff52d0ffca5a1df94b43fea96877d52d0ff8a5a1ffd4743ff28e877e51d0feca3a1dd94743fea8e877d51d0feaa3a1dd54743fe28e87ff50d0ffca1a1df94343fea86877d50d0ff8a1a1df55243bf29c87ff4390f7e8721f7d0e43ffa9487fe5290efca521ff54a43bea9487fc5290ffea321ff94643bf28c87fd5190efaa321ff14643ffa8487fe5090efca121ff54243bea8487fc5090ffe86a1f7d0d43ff21a87be4350ffea4a1dfd4943f7a92876f5250ffca4a1ff54943fe292877c5250fd8a4a1db14943ffa8a877f5150ffca2a1ff54543fe28a877c5150ffea0a1dfd4143ff28287fd5050ff8a0a1df14143bf2a0877e5310ffe8621efd0c43ff21887de4310ffa8621ef50c43eea1887ff5210ffca421df94843f7290876e5210ffaa421df54843f6a90876d5210ff8a421ffd4443ff288877e5110feca221dd94443fea88877d5110feaa221dd54443fe28887ff5010ffca021df94043fd280877a5010ffaa021df54043fca8087795010ff8a021ffd4f42ff29e857e53d0bfaa7a15f54f42fe29e85ff43d0bfc87a17f50f42fe21e85ff51d0bfca3a15f94742fb28e857651d0bfaa3a15f54
  | 7 => 0x45ed015328e810105f8af50841fdcec6d00410286014300005e8eb42c11d8f54001b04d51afdce4000a60f5c000be4000b59accce12d5959768000000de000130177042ce441f995518400034dc35b8de0ce0400137d00c294990e31b38000245cd8001a60cd96840017f5a69a987083959145c8000000001b0dd600000000019fd618d997c534cacd741155bd555c000001bf00003c0000000000f3913453086c0000b1234000310000001938614ce4c24cd060da200000007b52906a8cc93fd788aa85a985c001790000000dfc3a4000d359ec000880498000000001d34001584000654b4400000165d8b882857c3040016e46c92b5b200011bc99db7c000a5c4c89e424d8e5d640019d885ce000011b80a4c3d5240009045d1dd41a1bbc9e0e3d359320da4001104980c993800012d8b98fc4a201b483c0004a801000130c9a068da515f1308000e7d48d97c000bac320199abd02cb214c43fcf8000007c000078000e35be5c3cc701cd7e0e102f9351c101c9e000009dc001731d011717ad83c000778dac034411108868000b80001519b700008c489411d059991b5cdd89680013040002d05742cc000d580000000007d4950014019490635addb00a2879976c1a8f85278439af9709165a1897051c001ba8c4db4ddf8630b15ac9595564000d9c001734f983f17b00014ec001d1c000000289c44001448001d4d12ccfd57c26826c00115dd500000009d4c1c01d6bde49d5de4163cad9988dc8000d480000000fcc380000003cc0000000012fc0018c8000608000ff127c21cfedbfc0014a8000e91b0803d20dc28c51bf851098c0ec000998001c058c142c1b00010b40899788659a06d80855c95dc270398c652a46cc001db516809c40cba8cf1ac4588891d91a053e400400002a00800800600000000000600200000a00400000200a00400200202400600600201800000003a00007400203800200401000a00003e00200002800c01c00000000400000000002e00200200000c02000000000600200600002400000c00200400401e00600000601200800c00c00000601e00001800000a00000400800600600802800201200800204200000800a03200200000800a00800000400200403800001200000800c02a00e01200c00404201000a00600000001600000001400600000400400400200000a00202001800401200200200a00201a00400000400801401200000000600400a00600201800e08600000000e00001001800000a00800200000200600600605401000600400801a00200600200800401a01e00003e00200200001000000e00e02203200c03e00803400000201200c00800400000800000a00201800000200001800000200000200000c00a01200000200000603400400000003a00400600000000000400600000c004004004006
  | 8 => 0x19204f844953cac1bccd11508001814000528a911603b5d81504a31bb0000170554001330000644238149268ee4ad4000000001cf4f51cfcd5cf48ab43c82b5db88b932c2b887958c3ac358de8ae8001a38208aec4711fc0000000f40e44618553e0261b74ef43283e0fe50a53703dd244de5a400000000000000000004bdc50c8c000b9092414ceb956c0010d9c5c7d80008551a8000649ce12096cd649d844840006dda0c4d000007110cf612309649080004b0d4cac8f590dce9c3389447aceddce9dbc3bd4ad7e80000000008acca0f8c4e90ecfa04e4a753d5774c81b61551bd945d461158001910cb87e174969c00170c2c4cb5e5cf2d138f25b14a514751a4000000aad7cd67ccd5680cdcf693acb5c000ff5a74d75050a693b1b856950d5e040016258d04c40000000007bc000c494a1d98431795719a6d88800000164d6d09789b54592a888cf880ac8d8000f1cc94580ffc1249c9280360ad071991c0a8b4c784cc4668ccd2519e56043c4dcd59d5a124c000000000000e50001e112ec1edab0001bc000077526041c0000019e0000000e88a79aa030091de3de359c0534b64c740009f49fc2fcd7d2202315e53ec0000000011f175c00084076d520f9dd9dd3d29437c0005f0d3924800014147020d51c0004cc001450c601f00c1c196e9a89a3d6600000018e8000000d2c000c9dca0830001e64028b9d09cb1cb194380019654c80003483f9a4d404000ef80000000013bc58d7e57b9558bb4afcb413b80013cd8800003f4001214b948880010f0a656d400000134535c8b482d03d6515f40005ac9f9830bccbd19a889ca00001d3027d1300e8d55118000001478001779cbd5413b4518000f6cb047114b99bc00000179835dd247ed4001507959989c423c050fad219a1d71c054514000001dd80000000004240015d8e14001d18cf8001c49b2cba4dd17d8cf5bdc44c0016b975400017563832c0007b103038cd45a8498473c0009a4000001a64808000000b2d8c42a96b42a56340018bc000000661929cdcd8d265008c6c674b082a162168c001bd11e8e2d3490b982800128c000000000c5c0004f0541201aac4758d92dd6f4c4166990dcad1881d00015c5804899a9cda9bacf04da1bc58355c1ae0850000abc740464a14a0c49000004c000001560000000000000558000fdc12919d1a03b0bb15fd980a380009380018707b933536800000000017c91875982c001b787f40f19d57fde09bb8d240000000007f80000000019dc0000000013d0000225174000364df917c000194825a0908803000069522c6408cc764f44eb1a48000000f4d410408d600984b9d38334dec910ef05bcfb904c000dd406c068000000a187f1c7c000a2dc840000000012e093cc88000684a105d554d8648840002849d986cc099000005b18742bcc
  | 9 => 0x414309729bf57a55386c1e4c6189f1e44159a7cbf17a06100001b896d72400140c0b91280014415285dc00095cba1318000000000001c64ed5d580000000000000000000019a400000113ce8d49d8a99f8845a30001918a80001c9c8a800127056c2298ed52c1847d126ddd0b2465c30cdbd6556dc1687151b18581f4000458401da88e0000000000d1800069d2109adcc07e88706900000000011dde31d89e380007c4810c2d945e1dab8738000001aa4d0c000000000000e59bec8c00000005648014e47fc0015755a5b6c2010a8e29b34000000001cf1781cf8b29e2416da944f4fe0001374b7c520404024c180d4fe8d70000109e600013dc4458240001c1c397145987dc18cbec000d0000021516c249005c20a45a580016c16400000001c40013d8efdd8ce080013a445472d6c8000001ddc0006259b80016f901d9241d50191ccfd80010602798cc00052435400000093566c094000000000fd00000000006586f0000d680006a19b12b9c8cb6cf901bc13498911d7ec75d31d760d046393f400181813180880d5cceac8580000000018d4ff98396456c4ee002c2e8fcd6000000000015b05fcfd55ac5f505c2506b16907e5610001da14a4045378fb0389435a70a4950d1459354d0001ccd6fd6700000009298a40c8001800ec5110000000000000b340000000002800000000015d00000000004792c14b15e05c10540010493980000009b8af0ea1098000fa4001d048ec000d640003e52ac000000001568298955a34001c404889d0e0c1450c5be97d174dab52f50009b0be138d7058fd869674e65dc1da5d49d68680f0c8a50a08b06b92f8189de85487489e89ecc10c58671be00003906f88380006fdc6160cd81094834001c71315285c68001d944ec6bcc7d3114cc789340724ab0db143cd941d8f283a987c000f20b74d79e299691e4001b108bd4bc001d0ccbcb49c2d2982218489c0c147a173c00167969846c0008a06f44196a4db56a12c97bd090000495a44000001a91239d6d4d80018100000000000001640d9038cc0000001e2c00000000047c00110138596ddad0349593f9c01cb89a84ac0000000010780000000008f94088f5860d8971177c254001c09d20a6c0015a94880000014e9c98c78000920ed0f7d08ce7000000000045d14c001c1d7c8058e6db818f4e99360fc9ba17441a461c00172d7a9dcd1c59f10ad57887c9cdd74a8de50000af8d40378ebd0748f00741395d4000001b89cb50f4049c140006b40012f000000077d2e936ce1800193d3f05702ac0000000019096f000000008c09147ce687c8000000001274000b00f702c80000000000000000610d149912479de14d900018a11c9a8c29c421b3179d38813d720a3584053d4540bd44c7cc7285680002e0001cc40000002e4000f18754000064bd400000
  | 10 => 0x20ae46e08d45b8e20e1cae178c1e4d1c55c0003d5179531b1ca1d1d54f80003d80001e0fb40008e9070b0c745a78001b58e4caa40000000008c83e8000000c0c0014280019049bc860000001c587500000008fd99c7811f49006c400125ce60234771ad99600ccaddc88e404a5b49180e79e6852c039b55b241203d1878318114000205e540004e00004dce74d30818324000000001b91bc9a81a2425c509bb476878c00d1414448dccb1b44d840000006e8504cac1799516596e192c0007a4c018e17c00a0ec8c69229dc8ce906c000000848e5400028d8512b00005c56286504d8bbc0019cc0016a80000019300f80000000000000011e1af5aed6d994c00000000000010d5ec590001b3cc34ca8f41b993a13c80000002f4100d14000961a1400000000159959033ca9c5cc84c00121cb85ad4000414370e251c189d5140015b59e9ac000019d0400014f1df597554473439c000791db0000ed8001689a015548e400161c0005a42640000000007300000000000dd9c4b1000180c00000000000043c00081400000000005c000ecc0000003ece5c2ec000a84bdd1ed588b61845204000001534000001821c30001c54000434001045b280009949144a05791b4000000000be941800181c0000000011200002b10cceec00000000000000000141cf00001354b894c022c584000c300000000000010e40010e050d14918c000930bc863cbc5ae400090c000f14000e94441cc892cb78154dc06a4db8538bf4218cec3b9b65464345b51971a2d469c25d44bc036cf34ea8a8862cea5decf310696ad62cd3cac50bd4d4c28f95b954e18ad6ecec00206784516642110c00d1571b41d7818070dd70000118b3c804000a3d5b80007200000012bc0000018f12a12400014240000013386280010641ac940001254760f09af06d4a04000000000d6c275ae96080000000000011f9de0001c90bfd8f8000b69258001a2831c4c07a95f95805005d80018dc1914f4a40000000001115700000df1ad0000000000001ca8000000e38000c90001d7d1d1948105020bb80007c04b54b4698a55194fa811133dca51992c4b50350595b685510c80000019b5a119d18b11ac240ee8a083846657d5aa80017b57500000000017393a8000dc4b30545890560a988d0fbc001d14df4000f10001080000001b9ddc40011900019ac6880014ddcd5615d0939cd081e80013c4d213c071c000bd897c0009480e0e48604bf8000000c84000000374001289b19a5c4817f074d8999c9cb000176523c00175812cc44c21151c79c80f646ad07ca94ab859d7dc0048740090fca58a7d0f97f864c0b522529c0000005e10b198c0000019940000005e5885e58621984a4dba5484f752cddfc6e40c4f781dd84c0000014805a0c559f4160b7149539000000195c00094c15c468000001
  | 11 => 0xb39d29a543304d40006eca249742916b10256312e5e18e85d553944fdc0d421c742d82dc81d8b448dc6cb8dc94a7188cca53247055480815000007010e82f0001d2ddf00015e8000000001940fc1c4c49d4fc314001364000001e2067c38146c259de53e9510340ddd5bdd10f3c001cd0d28368b55d412d1784aa054c5b43a189466c4282d48
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe400435d5390010db94a400436d5290010bd98640042f561900109fd95400433e5450010cf551400435e5350010d754d400436e5250010db54940043b541500109fd94400427e65100109f594400427c6510010cf950400433d5410010b798c40042dd6310010d794c400435d5310010bb98840042ed6210010db948400436d5210010bd98440042f561100109f597300433e54cc010cf553300435e53cc010d754f300436e52cc010db54b30043d731cc0109fd96300427d658c010cf952300433d548c010d794e300435d538c010bb98a30042ed628c010db94a300436d528c010bd98630042f5618c0109fd95300433e544c010cf551300435e534c010d754d300436e524c010db54930042f7614c010bd18530043d7314c0109fd94300427e650c0109f594300427c650c010cf950300433d540c010d794c300435d530c010db948300436d520c010bd98430042f5610c010f64c0300427d65c8010cf953200433d54c8010d794f200435d53c8010db94b200436d52c8010f9c87200427f65880109f596200433e5488010cf55220042de6388010b758e200435e5388010d754e200436e5288010db54a20042f66188010bd586200427f6548010cf951200433d5448010d794d200435d5348010db949200436d5248010bdd8520042f46148010f9c85200427f65080109f994200427d65080109f194200433e5408010cf550200435e5308010d754c200436e5208010db54820042f66108010bd58420043e92008010cf953100433d54c4010d794f100435d53c4010db94b100436d52c4010dd59710042f764c4010bd593100437754c4010ed953100437554c4010ed553100433554c4010bd98f10042f463c4010f594f10043d553c4010bd98b10042f462c4010f994b10043e552c4010cf952100433d5484010d794e100435d5384010db94a100436d5284010bd58610043765184010be596100437965840109e59610043ba5484010ee55210043da5384010f654e10043ea5284010fa54a10042f96184010de94610043f25184010fc90610043f14184010fccc610043f03184010fcc8610043f021840109fd95100433e5444010cf551100435e5344010d754d100436e5244010db54910042f76544010ddd9510042776544010bdd9110042f56444010ddd5110043b65444010dd55110043b55444010cd55110042f66344010bd18d10043d65344010f554d10042f66244010bd18910043e65244010f954910042f76044010dd94110043f34044010fc10110043f23044010fc4c110043f22044010fc48110042fb6544010ded95100427b6544010ee95110043b95444010f694d10043d95344010fa94910043e95244010bed8510043f36144010de94510043f25144010fcd0510043f04144010fc8c510043f13144010fc88510043f12144010
  | 1 => 0x43b65450410cd95141043755450410ed55141043355450410dd15141042f46350410ddd4d41043765350410f594d41043565350410dd54d41043d55350410d554d41043745350410bd18941043775250410dd94941043e65250410d994941043755250410f954941043655250410dd14941042f760504109fd94410427d6510410cf950410433d5410410d794c410435d5310410db948410436d5210410bd98441042fa6010410be580410427d65cc410cf953310433d54cc410d794f310435d53cc410db94b310436d52cc410bd597310437565cc410bdd9331042f564cc410ddd5331043b654cc410dd55331043b554cc410cd553310437753cc410f594f310437553cc410f554f310435553cc410bd98b31043e652cc410f954b31042f560cc4109fd96310427d658c410cf952310433d548c410d794e310435d538c410db94a310436d528c410bd98631042fa608c410be582310427f654c410cf951310433d544c410d794d310435d534c410db949310436d524c4109fd94310427d650c410cf950310433d540c410d794c310435d530c410db948310436d520c410be98031042f9600c410dd5943104275650c410bdd9031042f5640c410ddd5031043b6540c410dd55031043b5540c410cd55031042f6630c410f598c3104377530c410f594c3104375530c410f554c31042f6620c410f994831043e5520c410fc98031042f5600c410fc58031042f1600c4109f597210433e54c8410cf553210435e53c8410d754f210436e52c8410db54b21042f565c8410dd59721042f764c8410bd593210437754c8410ed953210437554c8410ed553210433554c8410bd98f21042f463c8410f594f21043d553c8410ddd4b21043e652c8410dd54b21043e552c8410d954b21042f560c84109fd96210427d6588410cf952210433d5488410d794e210435d5388410db94a210436d5288410bd98621042fa6088410be582210427f6548410cf951210433d5448410d794d210435d5348410db949210436d52484109fd94210427d6508410cf950210433d5408410d794c210435d5308410db948210436d5208410be98021042f96008410dd59421042756508410bdd9021042f56408410ddd5021043b65408410dd55021043b55408410cd55021042f66308410bd18c21043d65308410f554c21042f66208410f998821043775208410f994821043755208410f954821043f26008410bd58021043f16008410bc580210427e64940109f592500427e63940109f58e500427e62940109f58a500427d6194010dd90650043754194010ddcc650043743194010ddc86500437421940109f597400433e54d0010cf553400435e53d0010d754f400436e52d0010db54b40042f661d0010bd58740043b541d00109fd96400427d6590010cf952400433d5490010d794
  | 2 => 0x6354810db18d520436f4354810db90d520436d4354810db10d520436e6154810db18552043646154810db981520436c6054810db04152042be6414810af590520433e5414810cf55052042de6314810b758c520435e5314810d754c52042ee6214810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520426e62148109f984520437661148109f980520437a60148109fd97420427e65d08109f597420427c65d0810cf953420433d54d0810d794f420435d53d0810db94b420436d52d0810bd98742042f561d08109fd96420427e65908109f596420427c6590810cf952420433d5490810d794e420435d5390810db94a420436d52908109fd95420427e65508109f595420427c6550810cf951420433d5450810b7d8d42042dc6350810d794d420435d5350810db949420436d5250810bdd8542042f46150810bed8142042f860508109fd94420427e65108109f594420427c6510810cf950420433d5410810b798c42042dd6310810d794c420435d5310810db948420436d5210810bd98442042f56110810be98042042f960108109fd97320427e65cc8109f597320427c65cc810cf953320433d54cc810d794f320435d53cc810db94b320436d52cc810bd98732042f561cc810be98332042f960cc8109fd96320427e658c8109f596320427c658c810cf952320433d548c810d794e320435d538c810db94a320436d528c810bd98632042f5618c810be98232042f9608c8109fd95320427e654c8109f595320427c654c810cf951320433d544c810d794d320435d534c810db949320436d524c810bdd8532042f4614c8109fd94320427e650c8109f594320427c650c810cf950320433d540c810d794c320435d530c810db948320436d520c810f34c8320427e64944109f592510427e63944109f58e510427e62944109f58a510427d65d0410cf953410433d54d0410d794f410435d53d0410db94b410436d52d04109fd96410427d6590410cf952410433d5490410d794e410435d5390410db94a410436d5290410dd94641042fa6090410be58241043776590410dd59641042756590410bd59241043775490410dd95241043b65490410dd55241043b55490410cd55241043745490410bd98e41043775390410dd94e41043d65390410d594e41043755390410f554e41043555390410dd14e41042f66290410ddd4a41043765290410f994a41043665290410dd54a41043e55290410d954a41043745290410fc98241042f56090410fc58241042f160904109fd95410433e5450410cf551410435e5350410d754d410436e5250410db54941043765150410bdd9541043776550410edd9141043775450410dd951410
  | 3 => 0xc10cf951530433d5454c109fd91530427c6454c10d7d8d530427f6254c109f189530427f6154c109f58553043746154c109fd81530427d6054c10d7d95530435f5454c10d7951530439e5454c10c7951530435d5454c10e7551530431d5454c10d715153043d46154c10d7d91530435e6454c10d7591530435c6454c10d7d89530435e6254c10d7589530435c6254c10d7985530435c6154c10d5185530435e6054c10d7181530435c1054c10af99053042bd6414c10cf950530433d5414c10b798c530435d5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f98c530435e6314c109798c530427e6214c10db988530426e6214c109f588530436d6214c109b588530427e6114c10dd984530427e6014c10de980530427f65d0c109f997430427d65d0c109f197430433e54d0c10cf553430435e53d0c10d754f43042f661d0c10bd587430427f6590c109f996430427d6590c109f196430433e5490c10cf552430435e5390c10d754e430427f6550c109f995430427d6550c109f195430433e5450c10cf551430435e5350c10d754d43042ef6250c10bb18943042f76150c10bd18543042fb6050c10be181430427f6510c109f994430427d6510c109f194430433e5410c10cf550430435e5310c10d754c43042ee6210c10bb58843042f66110c10bd58443042fa6010c10be58043042be64d4810af593520433e54d4810cf55352042de63d4810b758f520435e53d4810d754f520427e64d4810cf993520423e64d48109f593520433d64d48108f593520427e63d4810d798f520425e63d48109f58f520435d63d48109758f520427e61d4810dd987520427e60d4810de983520427d6594810cf952520433d5494810d794e520435d5394810dbd4a520427e64948109f592520427e63948109f58e520426d6594810dbd52520436e5494810eb952520432e5494810db55252043ad5494810cb552520436c5494810dbd4e520436e5394810f394e520434e5394810db54e52043cd5394810d354e520436c5394810f9186520436f6494810db992520436d6494810db192520436f6394810db98e520436d6394810db18e520436f4394810db90e520436d4394810db10e520436e6194810db186520436e6094810db182520433e5454810cf551520435e5354810d754d520427f64548109f191520427f63548109f18d520436f62548109fd85520427d6154810dd185520427f60548109f581520436f6554810dbd51520436e5454810eb951520432e5454810db55152043ad5454810cb551520436c5454810dbd4d520436e5354810f394d520434e5354810db54d52043cd5354810d354d520436c5354810f9185520436f6454810db991520436d6454810db191520436f6354810db98d520436d
  | 4 => 0xb14921442fb6048510be181214427e65085109f997404433f54d0110cf15340442f661d0110bd58740443b541d01109f996404427f65501109f595404427c6550110cfd51404433c5450110bdd8540442f46150110ed505404427e6510110b798c40442dd6310110bb98840442ed6210110bd98440442f561101109f997304435f53cc110d714f30442f661cc110bd587304427e658c110bb98a30442ed628c1109fd95304427d654c1109f195304435f534c110d714d30442f7614c110bd185304427e650c1109f997204436f52c8110db14b20442f661c8110bd587204427e6588110b798e20442dd63881109fd95204427d65481109f195204436f5248110db14920442f76148110bd185204427e6508110fc90710443f141c4110bdd9210442f56484110ddd5210443755484110dd94e10443745384110dd94a10443745284110fcd4210442de63d5010b758f54042ee62d5010bb58b540427e63d5010d798f540425e63d50109f58f540435d63d50109758f540427e62d5010db98b540426e62d50109f58b540436d62d50109b58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540427e63950109f58e540427e62950109f58a540437661950108f59654043b66195010cfd8e540433e6395010cf58e540433c6395010cfd8a540433e6295010cf58a540433c6295010cf98654043366195010cf186540433e6095010cf182540433f64550109fd8d540427c63550109fd89540427c62550109fd85540437661550109f585540427561550109fd81540427d6055010cfd9554043b66155010cfd8d540433e6355010cf58d540433c6355010cfd89540433e6255010cf589540433c6255010cf98554043366155010cf185540433e6055010cf181540433c1055010af990540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150108f990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427661150109f980540437a6015010af99353042bd64d4c10cf953530433d54d4c10bb98b53042ed62d4c109f993530433e64d4c108f993530427d64d4c10cf593530423d64d4c109f98b530436e62d4c109b98b530427d62d4c10db58b530426d62d4c109f987530437661d4c109f983530437a60d4c109f596530433e5494c10cf552530435f5394c109f992530427d6494c109f98a530427d6294c1097596530435f5494c10d7952530439e5494c10c7952530435d5494c10e7552530431d5494c10d715253043d46194c10d7d92530435e6494c10d7592530435c6494c10d7d8a530435e6294c10d758a530435c6294c10d7986530435c6194c10d7982530435c6094
  | 5 => 0x534437b6054d109f994534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427e6114d109f184534427e6014d109f180534427f65d0d109f997434427d65d0d109f197434435f53d0d10d714f43442f661d0d10bd587434427f6590d109f996434427d6590d109f196434427f6550d109f995434427d6550d109f19543442ef6250d10bb189434427f6510d109f994434427d6510d109f194434435f5310d10d714c43442ee6210d10bb58843442f66110d10bd58443442fa6010d10be580434427e64d49109f593524427e63d49109f58f52442de6394910b758e524436f52949109f992524427d64949109f98e524435e63949109798e524427d6394910d758e524425d63949109f98a524427d6194910dd586524427d6094910de582524427f64549109f191524427f63549109f18d524436f62549109fd85524437761549109dd85524427f6054910ded81524427e6514910db548524427e64149109f590524427e63149109f58c524436e62149109f984524427c61149109f980524427c60149109fd97424427e65d09109f597424427c65d0910dbd4b424436c52d0910bd98742442f561d09109fd96424427e65909109f596424427c65909109fd95424427e65509109f595424427c6550910b7d8d42442dc63509109fd94424427e65109109f594424427c6510910b798c42442dd6310910dbd48424436c5210910bd98442442f56110910be98042442f960109109fd97324427e65cc9109f597324427c65cc910d7d4f324435c53cc9109fd96324427e658c9109f596324427c658c910dbd4a324436c528c9109fd95324427e654c9109f595324427c654c910d7d4d324435c534c910dbd49324436c524c9109fd94324427e650c9109f594324427c650c910f34c832442f6610c910bd58432442fa600c910be580324427e65d0510cfd53414433c54d0510be98341442f960d05109f99641442f66590510dd99641442f56490510ddd5241443765490510dd55241443745490510ddd4e41443765390510dd54e41443745390510ddd4a41443765290510dd54a41443745290510bd982414427c6550510cfd51414433c5450510bed8141442f86050510dd995414437465505109d19541443b76450510ddd5141443b75450510cdd5141443765450510dd55141443745450510ed15141443775350510dd94d41443755350510dd14d41443775250510dd94941443755250510dd14941443f36050510bd18141443f06050510bc181414427e6510510bd98441443b541105109f997314435f53cc510d714f31442fa60cc510be583314427e658c5109f195314435f534c510d714d31442fb604c510be181314427e650c5109f997214436f52c8510db14b21442fa60c8510be583214427e65885109f195214436f5248510d
  | 6 => 0x2f76050610fcd8141843f06050610d794f318435d53cc610be98331842f960cc610dd59731842f764cc610bd593318437754cc610dd553318437753cc610f594f318437553cc610f554f31842f662cc610fc98331842f560cc610fc583318435e534c610d754d31842fb604c610be18131842f5650c610dd59431842f7640c610bd5903184377540c610dd55031843d6630c610ddd4c3184375530c610bd98831842f5600c610db94b218436d52c8610be98321842f960c8610dd59721842f764c8610bd593218437754c8610dd55321842f663c8610bd18f218437752c8610f994b218437552c8610f954b21843f260c8610bd58321843f160c8610db949218436d5248610bed8121842f86048610bd59421843756508610bdd9021842f56408610ddd5021843755408610bd98c21842f46308610f998821843775208610dd54821842f56008610cfd53408433c54d0210bd98740842f561d0210ed507408433e5490210cf55240842f66190210bd586408433f5450210cf15140843b54150210cf950408433d5410210b798c40842dd6310210bb98840842ed6210210bd98440842f56110210d7d4f308435c53cc210f5cc7308435e538c210d754e30842ee628c210bb58a30842f6618c210bd586308435f534c210d714d30842f7614c210bd18530843d7314c210d794c308435d530c210bd98430842f5610c210dbd4b208436c52c8210f9c8720842de6388210b758e208436e5288210db54a20842f66188210bd586208436f5248210db14920842f76148210bd18520843e72148210db948208436d5208210bd98420842f56108210bd597108437565c4210bdd9310842f564c4210ddd53108437554c4210bd98f10842f463c4210bd98b10842f462c4210be597108437965c42109f98f544427d63d51109f98b544427d62d5110ddd87544433f54951109f992544427e63951109f58e544427e62951109f58a544427d6195110dd586544427561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f63551109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427f6055110ded81544427e6515110cf550544433e64151109f98c544427d63151109f988544427d62151109f98454442766115110dd584544427c61151109f980544427c60151109f993534427d64d4d109f98b534427d62d4d10d7d4e53442ee6294d10bb58a534427e6494d109f592534427e6394d109f98a534436e6294d109b98a534427d6294d10db58a534426d6294d109f58653443756194d109f58253443796094d109fd91534427c6454d10d7d8d534427f6254d109f189534427f6154d10ddd8553442776154d109fd81
  | 7 => 0x3152109798c548427d6315210d758c548425d63152109f988548436e62152109b988548427d6215210db588548426d6215210dd584548437a6015210bb98b53842ed62d4e109f993538427d64d4e109f98b538436e62d4e109b98b538427d62d4e10db58b538426d62d4e10dd587538437a60d4e10d7d4e538427e6494e109f592538427e6294e109f58a538427f6454e109f191538435f6354e109fd89538427c6254e10ddd85538435d5314e109f990538427d6414e10d798c538427e6214e109f58853843756114e10de980538427f65d0e109f997438427d65d0e109f19743842f661d0e10bd587438427f6590e109f996438427d6590e109f196438435e5390e10d754e438427f6550e109f995438427d6550e109f195438435e5350e10d754d43842ef6250e10bb18943842f76150e10bd185438427f6510e109f994438427d6510e109f19443842ee6210e10bb58843842f66110e10bd58443842fa6010e10be58043842de63d4a10b758f528427e64d4a109f593528427e63d4a10d798f528425e63d4a109f58f528435d63d4a109758f528437561d4a10de983528436f5294a109f992528427d6494a109f98e528427d6394a109fd91528427c6454a109fd8d528427c6354a10dbd8952843776154a10db548528427e6414a109f590528427e6314a109f58c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10bd98742842f561d0a109fd96428427e6590a109f596428427c6590a10db94a428436d5290a109fd95428427e6550a109f595428427c6550a10b7d8d42842dc6350a10db949428436d5250a10bdd8542842f46150a109fd94428427e6510a109f594428427c6510a10b798c42842dd6310a10bd98442842f56110a10be98042842f96010a109fd97328427e65cca109f597328427c65cca10db94b328436d52cca10bd98732842f561cca109fd96328427e658ca109f596328427c658ca10d794e328435d538ca10bd98632842f5618ca109fd95328427e654ca109f595328427c654ca10bdd8532842f4614ca109fd94328427e650ca109f594328427c650ca10d794c328435d530ca10db948328436d520ca10f34c832842fa600ca10be580328433e54d0610cf55341842fa60d0610be58341842f56590610dd59641843775490610dd95241843755490610dd15241842f66390610ddd4e41843765390610dd54e41843745390610bd98a41843775290610dd94a41843755290610dd14a41842f56090610cf951418433d5450610bed8141842f86050610ddd9541843b76450610dd95141843b65450610cd95141843755450610ed55141843355450610dd15141842f46350610ddd4d41843765350610dd54d41843745350610bd18941843775250610dd94941843755250610dd1494184
  | 8 => 0x10bd58443c42fa6010f10be58043c427e64d4b109f59352c427e63d4b109f58f52c437661d4b10de58352c436f5294b109f99252c427d6494b109f98e52c427d6394b109fd9152c427c6454b109fd8d52c427c6354b10dbd8952c436d5214b109f99052c427d6414b109f98c52c427d6314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c42f661d0b10bd58742c427f6590b109f99642c427d6590b109f19642c427f6550b109f99542c427d6550b109f19542c42df6350b10b718d42c42fb6050b10be18142c427f6510b109f99442c427d6510b109f19442c42de6310b10b758c42c42f66110b10bd58442c42fa6010b10be58042c427f65ccb109f99732c427d65ccb109f19732c42fa60ccb10be58332c427f658cb109f99632c427d658cb109f19632c42fa608cb10be58232c427f654cb109f99532c427d654cb109f19532c427f650cb109f99432c427d650cb109f19432c43cd320cb10bd98432c42f5610cb10cfd5341c433c54d0710cf95241c433d5490710be98241c42f96090710dd59641c43765490710ed95241c43755490710ed55241c43355490710dd15241c43775390710dd94e41c43755390710dd14e41c43775290710dd94a41c43755290710dd14a41c42f66090710fc98241c43f16090710cfd5141c433c5450710bdd9541c43776550710edd9141c43775450710edd5141c43375450710dd95141c43755450710dd15141c43b45450710ddd4d41c43765350710dd54d41c43745350710ddd4941c43765250710dd54941c43745250710bd18141c433e5410710cf55041c43b54110710be98041c42f96010710d7d4f31c435c53cc710d794e31c435d538c710be98231c42f9608c710d7d4d31c435c534c710d794c31c435d530c710be98031c42f9600c710dbd4b21c436c52c8710db94a21c436d5288710be98221c42f96088710dbd4921c436c5248710db94821c436d5208710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310ed50740c433e5450310cf55140c42f76150310bd18540c43b54150310b798c40c42dd6310310bb98840c42ed6210310bd98440c42f56110310d794f30c435d53cc310bd98730c42f561cc310bb98a30c42ed628c310d794d30c435d534c310bdd8530c42f4614c310f64c030c436e52c8310db54b20c42f661c8310bd58720c42de6388310b758e20c436e5248310db54920c42f76148310bd18520c43e920083109f98f548427d63d52109f98b548427d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a54843756195210cfd91548427f63552109f18d548427f62552109f18954843756155210cf55054842de6315210b758c54842ee6215210bb588548433e64152109f98c548435e6
  | 9 => 0x546310827f654c4209f595310827c654c420d794d310835d534c420dd9453108375514c4209fd94310827e650c4209f594310836e52c8420dd947210837551c8420be98321082f960c84209f596210827f6548420db94921083765108420dd54421082fa6008420be580210827e64940209f592500827e6394020d798e500825e63940209f58e500835d63940209758e50083764194020dd506500827d65d0020bd98740082f561d0020ed507400827f65900209f596400833e5490020cf55240082ee6290020bb58a400837a50900209fd9540083b54150020de941400827f65100209f994400827d65100209f194400833e5410020cf55040082de6310020b758c40082ee6210020bb58840082f66110020bd584400827d65cc020d7d4f300835c53cc0209fd96300827d658c020d794e300835d538c020bb98a30082ed628c0209fd95300835f534c020d714d30082f7614c020bd185300827f650c0209f994300827d650c0209f194300835e530c020d754c30082ee620c020bb588300836f54c8020db553200836e53c8020db14f200836d51c8020f990720083e541c8020b798e20082dd6388020bb58a200836e5288020ded5220083795488020f698e20083d96388020be58a200837a5288020fa94a20083f24188020fc506200827f6548020bdd8520082f46148020bbd95200836f65480209bd95200836f5448020db551200836e5348020db14d20083e76148020f9185200836d5148020f990520083e54148020bbd81200836e5048020fa90120083e94048020fa8c120083e93048020bed95200837b65480209ed95200837b5448020de55120082fb6248020fad89200837a5248020fa94920083ea4248020fa50920083ea3248020fa4c920083f36148020fc18520083f24148020fc50520083ea2148020fa085200827e63d53109f58f54c427e62d53109f58b54c437661d5310de58354c433f54953109f98e54c427d63953109f98a54c427d6295310dd98654c433f64553109fd8d54c427c63553109fd8954c427c6255310dd98554c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c427e64d4f109f59353c427e62d4f109f58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f109fd9153c427c6454f10d7d8d53c427f6254f109f18953c435d5314f109f99053c427d6414f10d798c53c427e6214f109f58853c43766114f10de58053c427f65d0f109f99743c427d65d0f109f19743c42f661d0f10bd58743c427f6590f109f99643c427d6590f109f19643c427f6550f109f99543c427d6550f109f19543c42ef6250f10bb18943c42fb6050f10be18143c427f6510f109f99443c427d6510f109f19443c42ee6210f10bb58843c42f66110f
  | 10 => 0x40827e6015020de980540827a60150209f993530827d64d4c209f98b530836e62d4c209b98b530827e61d4c209f587530827e60d4c20de983530827d6594c20d7d4e530827e6494c209f592530827e6194c209f586530827f6454c209f191530835f6354c209fd89530827d6254c209fd85530827c6154c20af99053082bd6414c20d754c53082f66114c20bd584530827e6414c20cf990530823e6414c209f590530833d6414c208f590530827e6314c20d798c530827e6214c20db988530827e6114c20dd98453082766114c209f58453083756114c209d584530827e6014c20de980530827f65d0c209f997430827d65d0c209f197430833e54d0c20cf55343082f661d0c20bd587430827f6590c209f996430827d6590c209f196430835e5390c20d754e430827f6550c209f995430827d6550c209f195430833e5450c20cf551430835e5350c20d754d43082ef6250c20bb189430827f6510c209f994430827d6510c209f19443082ee6210c20bb58843082f66110c20bd58443082fa6010c20be580430827e64948209f592520827e63948209f58e520827d65d0820bd98742082f561d08209fd96420827d6590820cf952420833d5490820db94a42082fa6090820be582420827f6550820b7d8d42082dc6350820db949420827f65108209f594420833e5410820cf55042082de6310820b758c42082f66110820bd58442082fa6010820be580420827d65cc820db94b320827f658c8209f596320835e538c820d754e32082fa608c820be582320827f654c8209fd94320827d650c820d794c320835d530c820db94832083cd320c820be98032082f9600c820ddd46510827e64944209f592510827e63944209f58e510827f64544209f191510827f63544209f18d51082be6414420af59051082de6314420b758c510837551144209fd97410827e65d04209f597410833e54d0420cf553410827f65904209f996410827d6590420dd94641083755190420ddd9641083766590420dd59641083746590420bd59241083775490420dd95241083755490420dd15241083775390420dd94e41083755390420dd14e410837652904209fd95410827d65504209f195410833e5450420cf55141082ef6250420bb18941083765150420dd54541082fb6050420be18141083776550420dd99541083756550420dd19541083b76450420ddd5141083765450420ed95141083365450420dd55141083b55450420cd55141083745450420ddd4d41083765350420dd54d41083745350420f9d8941083e46250420dd94941083f36050420fc181410827f65104209f994410827d6510420bd984410827f65cc4209f997310827d65cc420d794f310835d53cc420bb98b31082ed62cc420be98331082f960cc4209fd96310827e658c4209f5963108376518c420dd
  | 11 => 0xed6288520ddd4621483745188520be98221482f96088520ddd4521483745148520bed8121482f86048520bbd9121482ed6448520bb98d21482ec6348520f9d8521483e75148520db14521483e45148520f990521483e54148520fad8121482ec6048520fa18121482e860485209f99421482ee6208520ddd44214827e65d0120cfd53404833c54d0120bb98b40482ed62d0120bd98740482f561d0120ddd47404837451d0120ed507404827e6590120ddd4640483745190120be996404837a6590120be592404837a5490120de152404837b5390120de54e40483eb6290120be98a40483e86290120fa90a40483e94290120facca40483e83290120fcd4640483f05190120fc90640483f14190120fac8640483e921901209fd95404827d65501209f195404833f5450120cf15140482ef6250120bb18940483775150120dd14540483b54150120be195404837865501209e19540483bb6450120eed51404837a5450120de15140483b85450120ded4d40483795350120fad8940482f86250120fa18940483ea4250120fa50940483eb3250120fa0c940483f35150120fc14540483bb4150120fc90540483b94150120fc50540483b14150120fac8540483e921501209f99440482de6310120b758c40482ee6210120bb58840482f66110120bd58440483775110120dd14440482fa60101209f997304835f53cc120d714f30482ee62cc120bb58b30483cc32cc120ddd47304837451cc1209f99630482ee628c120bb58a3048377518c120dd146304827f654c1209f595304827c654c120d7d4d304835c534c120bbd8930482ec624c120f30c930482f7614c120bd1853048377514c120dd145304827e650c120ddd443048374510c120f64c0304837751c8120dd14720482fb64c8120be59320483ea42c8120fa50b20483eb32c8120fa0cb20483f351c8120fc14720483f241c8120fc50720483eb21c8120fa48720482de6388120b758e20483775188120dd14620482ef6488120bb59220482ee6388120f398e20482ce6388120f358e20482ec6388120bb58620483e75188120f914620483e64188120f950620483eb5088120fa90220483e940881209f98f540827d63d50209f98b540836e62d50209f987540827d61d50209f983540837a60d50209f596540833f5495020bd98654082f561950209f98e540827d63950209f986540837661950209d986540827d6195020dd58654082756195020cfd91540827f63550209f18d540827f62550209f589540827f61550209f185540833d5415020b798c54082dd6315020bd98454082f561150209f990540833e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f988540836e62150209b988540827e6115020dd984540827661150209f584540837561150209d5845
  | 12 => 0xc920f3d0c32483cc430c920bb58432482ee600c9209f993514827d64d45209f98f514827d63d4520bd593514837754d4520dd953514837554d4520dd153514837753d4520dd94f514837553d4520dd14f51483e762d4520f990b51483e542d4520f9ccb51483e432d4520ddd93514837664d4520dd593514827564d4520dd193514837763d4520dd98f514837563d4520dd18f514837743d4520dd90f514837543d4520dd10f514837762d4520ddd0b514837642d4520dd50b514837442d4520ddccb514837632d4520dd4cb514837432d4520ddd83514837560d4520ddd46514837551145209f990514827d64145209f98c514827d6314520bd99451483766514520bd59051483775414520dd95051483755414520dd15051483775314520dd94c51483755314520dd14c51483e56214520f990851483e54214520f9cc851483e43214520ddd9051483766414520dd59051482756414520dd19051483776314520dd98c51483756314520dd18c51483774314520dd90c51483754314520dd10c51483776214520ddd0851483764214520dd50851483744214520ddcc851483763214520dd4c851483743214520ddd8051483756014520dd480514827e65d05209f597414827c65d0520bb98b41482ed62d0520ddd47414837451d0520be98341482f960d05209f996414827d65905209f19641482ee6290520bb58a41483775190520dd14641483776590520bd996414837665905209d99641483756590520bd196414837465905209d19641482f56490520ddd5241483765490520dd55241483745490520ddd4e41483765390520dd54e41483745390520f998a41483e56290520f990a41483e54290520f9cca41483e432905209fd95414827e65505209f19541483775150520dd14541483776550520bd995414837665505209d99541483756550520bd195414837465505209d19541483b76450520ddd5141483765450520dd55141483745450520ddd4d41483765350520dd54d41483745350520f998941483e56250520f990941483e54250520f9cc941483e432505209f994414827d65105209f19441482ee6210520bb58841482f66110520ddd4441483745110520be98041482f960105209f997314827d65cc5209f197314837751cc520dd147314827e658c5209f596314827c658c520bb98a31482ed628c520ddd463148374518c5209fd95314827e654c5209f19531482ef624c520bb1893148377514c520dd14531482fb604c520be181314827e650c5209f594314827c650c520bb98831482ed620c520ddd443148374510c520be98031482f9600c5209f997214837451c8520bb997214836e65c8520bbd9321482ed64c8520bb98f21482ec63c8520f9d47214836c51c8520f9147214836451c8520f990721483e541c8520bb98321482
  | 13 => 0xded81544827e6515120cf55054482de6315120b758c54482f66115120bd584544833e64151209f98c544835e63151209798c544827d6315120d758c544825d63151209f988544836d62151209f188544827e6115120dd984544827661151209f584544837561151209d584544837960151209f993534827d64d4d20db58b534827e61d4d209f587534835f5394d20bd98653482f56194d209f992534827d6494d209f98e534827d6294d20db58a534827e6194d20dd98653482766194d209f58653483756194d209d586534827d6094d20de58253482bf6454d20af19153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534835f6354d209fd89534836f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209f994534835d5314d209f990534827d6414d20d798c534827e6214d209f188534827e6114d209f584534827f65d0d209f997434827d65d0d209f197434835f53d0d20d714f43482ee62d0d20bb58b43482f661d0d20bd58743482fa60d0d20be583434827f6590d209f996434827d6590d209f196434833f5490d20cf152434835e5390d20d754e434827f6550d209f995434827d6550d209f195434835e5350d20d754d43482ef6250d20bb189434827f6510d209f994434827d6510d209f194434833f5410d20cf150434835f5310d20d714c43482ee6210d20bb58843482f66110d20bd58443482fa6010d20be580434827e65d0920cfd53424833c54d0920bd98742482f561d0920be98342482f960d09209f99642482ee6590920db99642482ed6490920db952424836c5490920bb98e424836f5390920db54e42482ed6190920fad8242482ee6090920fa182424827c6550920cfd51424833c5450920b7d8d42482dc6350920bed8142482f86050920db195424826c6550920ebd9142483af5450920db951424836c5450920eb15142483cf6350920bb18d42483cc6350920b318d424836f5350920db54d42482ef6150920fad8142482ec6050920fa181424827e6510920b798c42482dd6310920bb98842482f66110920bd58442482fa60109209f997324835f53cc920d714f32482fa60cc920be583324836e65cc9209b99732482ef64cc920bb593324836e54cc920db153324836f53cc920f3d4f324836d53cc920f314f32483ce43cc920f350f32482ed61cc920bb98332483ea60cc920ba98332483e960cc9209f996324835e538c920d754e32482ee628c9209f195324835f534c920d714d32482fb604c920be181324827e650c920d794c324835d530c920f34c832482ee650c920db99432482ef640c920bb590324836e540c920db15032482ee630c920f398c324836f530c920f394c324836d530c920f354c324834d53
  | 14 => 0x95418833e5450620cf551418835e5350620d754d41882ef6250620bb18941883765150620dd54541883776550620dd99541883756550620dd19541883b76450620ddd5141883765450620ed95141883365450620dd55141883b55450620cd55141883745450620ddd4d41883765350620f594d41883565350620dd54d41883d55350620d554d41883745350620f9d8941883e462506209fd94418827e65106209f594418835e5310620d754c41882fa6010620be580418827f65cc6209f997318827d65cc620d794f318835d53cc620bb98b31882ed62cc6209fd96318827e658c6209f596318835e538c620d754e318827f654c6209f595318827c654c620d794d318835d534c620bed8131882f8604c6209fd94318827e650c6209f594318835e530c620d754c31882fa600c620be580318835e53c8620d754f218835e5388620d754e21883765188620dd54621882fa6088620be582218835e5348620d754d21883765148620dd54521882fb6048620be181218835e5308620d754c218835e53d0220d754f40882f661d0220bd58740883b541d0220cf952408833d5490220d794e408835d5390220bb98a40882ed6290220be59640883796590220de95240883ba5490220ee55240883785490220ded4e40883da5390220de54e40883d95390220d654e40882fa6290220fa98a40883e96290220fc90640883f14190220d794d408835d5350220ed50540882fb6550220ded9540883bb6450220de95140883785450220ded4d40883da5350220de54d40883d95350220d654d40882f86250220eed0540883f24150220ee50540883f14150220ec505408833e5410220cf55040882de6310220b758c408835e5310220d754c40882ee6210220bb58840882f66110220bd584408835e53cc220d754f308835e538c220d754e30882ee628c220bb58a308835e534c220d754d30882f7614c220bd185308835e530c220d754c30882ee620c220bb58830883d9300c220d794f208835d53c8220bb597208836d65c8220dbd53208836d54c8220db94f20883ce53c8220d394f20883cd53c8220db14f208836d51c8220f990720883e541c8220be597208837965c8220bed9320882f964c8220f694f20883d953c8220fc90720883f141c82209f98f544827d63d5120ddd87544827e61d51209f587544837461d5120cfd5254482f66195120bd586544827e64951209f98e544827d63951209f58a544836d62951209f986544837661951209d986544827d6195120dd586544827561951209f58254483796095120b7d8d54482dc6355120bdd8554482f46155120cfd91544827f6355120d7d8d544825f63551209f18d544835c63551209718d544827f6255120dbd89544827f6155120ddd85544827761551209f185544837461551209d185544827f605512
  | 15 => 0x8837a6095220cfd91548827f63552209f18d548827f61552209f185548833d5415220b798c54882dd6315220bd98454882f56115220cf990548827e6315220d798c548825e63152209f58c548835d63152209758c548836d62152209f984548837661152209d984548827d6115220dd58454882756115220de980548827e64d4e209f593538836d62d4e209f987538827d61d4e20de983538835f5394e209f992538827d6494e209f986538827d6194e20d7d52538835e5494e20d7552538835c5494e20d7d92538835e6494e20d7592538835c6494e20d7d8a538835d6294e20d7d86538835e6194e20d7586538835c6194e20d7982538835c6094e209fd91538827c6454e20d7d8d538827f6154e209f185538835f6554e20d7d51538835e5454e20d7551538835c5454e20d7d91538835e6454e20d7591538835c6454e20d7d89538835d6254e20d7d85538835e6154e20d7585538835c6154e20d7981538835c6054e20d754c538827e6414e209f590538835e6314e20db588538827e6114e209f584538837a6014e209fd97438827e65d0e209f597438827c65d0e20d794f438835d53d0e20bd98743882f561d0e20be98343882f960d0e209fd96438827e6590e209f596438827c6590e20d794e438835d5390e209fd95438827e6550e209f595438827c6550e20d794d438835d5350e20bbd8943882ec6250e209fd94438827e6510e209f594438827c6510e20d794c438835d5310e20bb98843882ed6210e20bd98443882f56110e20be98043882f96010e20cf953428833d54d0a20d794f428835d53d0a20bd98742882f561d0a20be98342882f960d0a20d794e428835d5390a20cf951428833d5450a20b7d8d42882dc6350a20d794d428835d5350a20bed8142882f86050a20b798c42882dd6310a20d794c428835d5310a20bd98442882f56110a20be580428835e53cca20d754f32882fa60cca20be583328835e538ca20d754e328835e534ca20d754d32882fb604ca20be181328835e530ca20d754c32883cd320ca20b798f51882dd63d4620d794f518835d53d4620d794e518835d5394620ddd46518827e64946209f592518827e63946209f58e518835e5354620d754d518827f64546209f191518827f63546209f18d51882be6414620af59051882de6314620b758c518835e5314620d754c518837551146209fd97418827e65d06209f597418833e54d0620cf553418835e53d0620d754f41882fa60d0620be583418827f65906209f996418827d6590620d794e418835d5390620dd94641883755190620ddd9641883766590620dd59641883746590620ddd5241883765490620dd55241883745490620ddd4e41883765390620f594e41883565390620dd54e41883d55390620d554e418837453906209fd95418827d65506209f1
  | 16 => 0xe60ccb20d794e32c835d538cb20be98232c82f9608cb20d794c32c835d530cb20f34c832c82fa600cb20be58032c836d650cb20bbd9032c82ed640cb20db95032c836c540cb20f398c32c836f530cb20f394c32c836d530cb20f354c32c834d530cb20f3d0c32c83cc430cb20bb58432c82ee600cb20fa98032c83e9600cb20b798f51c82dd63d4720ddd4651c827e64947209f59251c827e63947209f58e51c827f64547209f19151c827f63547209f18d51c837551147209fd9741c827e65d07209f59741c82ee62d0720bb58b41c827f65907209f99641c827d6590720bb98a41c82ed6290720dd94641c83755190720ddd9641c83766590720dd59641c83746590720ddd5241c83765490720dd55241c83745490720ddd4e41c83765390720dd54e41c83745390720f998a41c83e56290720f990a41c83e54290720f9cca41c83e432907209fd9541c827d65507209f19541c83765150720dd54541c82fb6050720be18141c83776550720dd99541c83756550720dd19541c83b76450720ddd5141c83765450720dd55141c83745450720ddd4d41c83765350720dd54d41c83745350720f998941c83e56250720f990941c83e54250720f9cc941c83e43250720fcd8141c83f060507209fd9441c827e65107209f59441c82ee6210720bb58841c827f65cc7209f99731c827d65cc720dd94731c837551cc720be98331c82f960cc7209fd9631c827e658c7209f59631c835e538c720d754e31c82ee628c720bb58a31c827f654c7209f59531c827c654c720bbd8931c82ec624c7209fd9431c827e650c7209f59431c835e530c720d754c31c82ee620c720bb58831c8376510c720dd54431c837651c8720dd54721c82fa60c8720be58321c82ef64c8720bb59321c82ee63c8720bb18f21c836e51c8720f994721c83e551c8720f990721c83e541c8720bb98321c83ea60c8720fa58321c82ef6548720dbd9521c82ef6448720bb59121c82ee6348720bb18d21c83e76148720db94521c83e64148720f950521c82ec6048720dd94421c83755108720be98021c82f96008720cf95340c833d54d0320bb98b40c82ed62d0320bd98740c82f561d0320ed50740c833e5450320cf55140c82ef6250320bb18940c83b54150320b798c40c82dd6310320bb98840c82ed6210320bd98440c82f56110320d794f30c835d53cc320bb98b30c82ed62cc320f30cb30c82ee628c320bb58a30c835e534c320d754d30c82ef624c320bb18930c83cc324c320bdd8530c82f4614c320b798f54882dd63d52209f98f548835e63d52209798f548827d63d5220d758f548825d63d5220db58b548827e61d52209f587548837a60d5220cfd5254882f66195220bd586548827e63952209f58e548827e6195220dd986548827661952209f586548837561952209d58654
  | 17 => 0x30bd584400c35f54cc030d7553300c35e52cc030d7547300c3d641cc030f5507300c2dd638c030d794e300c2ee628c030bb58a300c37b548c030de552300c2f9638c030de94e300c3da538c030fa98a300c3e9628c030fc906300c3f1418c0309fd95300c2f7614c030bd185300c2df654c030d7d95300c25f654c030d7d51300c35d544c030d7949300c3d7614c030f5185300c35d514c030f5905300c3d5414c030b7d81300c35e504c030f6901300c3d9404c030bed95300c37b654c0309ed95300c37b544c030de551300c2fb634c030f6d8d300c37a534c030f694d300c3da434c030f650d300c3db324c030f64c9300c3f3614c030fc185300c3f2414c030fc505300c3da314c030f60c5300c27e63d53209f58f54c836e62d53209f98754c827d61d5320de58354c833f5495320bd98654c82f561953209f98e54c827d6395320db98a54c827e6195320dd98654c827661953209f58654c837561953209d58654c833f64553209fd8d54c827c63553209fd8554c827c6155320cf55054c82de6315320b758c54c82f66115320bd58454c833e64153209f98c54c835e63153209798c54c827d6315320d758c54c825d6315320db98854c827e6115320dd98454c827661153209f58454c837561153209d58454c83796015320bd98753c82f561d4f209f99353c827d64d4f20db98b53c827e61d4f20dd98753c827661d4f209f58753c837561d4f209d58753c837960d4f20d7d4e53c827e6494f209f59253c827e6194f209f58653c827f6454f209f19153c835f6354f20db18953c827f6154f209f18553c835d5314f209f99053c827d6414f20d798c53c836e6214f209f98453c827d6114f20de58053c827f65d0f209f99743c827d65d0f209f19743c82ee62d0f20bb58b43c82f661d0f20bd58743c827f6590f209f99643c827d6590f209f19643c835e5390f20d754e43c827f6550f209f99543c827d6550f209f19543c835e5350f20d754d43c82ef6250f20bb18943c827f6510f209f99443c827d6510f209f19443c82ee6210f20bb58843c82f66110f20bd58443c82fa6010f20be58043c82f661d0b20bd58742c833e5490b20cf55242c82fa6090b20be58242c836d6590b20db95242c83ae5490b20eb55242c836c5490b20bb98e42c836f5390b20db54e42c82ed6190b20bb98242c83ea6090b20fa58242c82df6350b20b718d42c82ef6550b20dbd9542c83af6450b20db95142c836c5450b20f3d8d42c82ec6350b20f318d42c82cc6350b20dbd4d42c836d5350b20bbd8542c82ec6050b20cf95042c833d5410b20b798c42c82dd6310b20bd98442c82f56110b20be98042c82f96010b20bb59732c836d65ccb20bbd9332c82ed64ccb20db95332c836c54ccb20dbd4f32c836d53ccb20f390f32c83cd43ccb20bb58732c82e
  | 18 => 0x9fd96430c27d6590c30cf952430c33d5490c30d794e430c2fa6090c30be582430c27f6550c30d794d430c2ef6250c30bb189430c27f6510c309f594430c33e5410c30cf550430c2ee6210c30bb588430c2f66110c30bd584430c2fa6010c30be580430c36f52948309f992520c27d64948309f986520c27d61948309fd91520c27c64548309fd85520c27c6154830af990520c2bd6414830db548520c2f66114830bd584520c27f65d08309f997420c27d65d0830cf953420c33d54d0830bd987420c2f561d08309fd96420c27e65908309f596420c36e5290830db54a420c27f65508309f595420c27c6550830cf951420c33d5450830b7d8d420c2dc6350830db949420c36d52508309fd94420c27e65108309f594420c2de6310830b758c420c2f66110830bd584420c2fa6010830be580420c36e52cc830db54b320c2fa60cc830be583320c27d658c830d794e320c27f654c830d794c320c36e520c830db548320c3cd320c830be980320c2f9600c830ddd46510c27e64944309f592510c27e62944309f58a510c27f64544309f191510c27f62544309f189510c2be6414430af590510c2ee6214430bb588510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c27f65904309f996410c27d6590430dd946410c3755190430ddd96410c3766590430dd596410c3746590430bd592410c3775490430dd952410c3755490430dd152410c3765390430dd94a410c37552904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c3765150430dd545410c2fb6050430be181410c3776550430dd995410c3756550430dd195410c3b76450430ddd51410c3765450430ed951410c3365450430dd551410c3b55450430cd551410c3745450430f5d8d410c3d46350430dd94d410c3765250430dd549410c3f36050430fc181410c27f65104309f994410c27d6510430bd984410c35e53cc430dd947310c37551cc430be983310c2f960cc4309f596310c27f654c430d794d310c376510c430dd544310c2fa600c430be580310c27f65c84309f997210c27d65c8430b798f210c2dd63c8430db94b210c36d52c8430be983210c2f960c84309fd96210c27e65884309f596210c3765188430dd546210c27f65484309f595210c27c6548430db949210c36d5248430dd945210c37551484309fd94210c27e65084309f594210c27e64940309f592500c36e6294030db58a500c3764194030dd506500c27d65d0030bd987400c2f561d0030ed507400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c37a50900309fd95400c3b54150030de941400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c2ee6210030bb588400c2f6611
  | 19 => 0x1314c2f8604c530b7d91314c2dd644c530b7189314c3d7614c530f5d45314c35c514c530f5145314c3d6414c530f5505314c3db604c530b7181314c3d8604c530b6181314c27e650c530b798c314c377510c5309f997214c27d65c85309f197214c2df63c8530b718f214c37751c8530dd147214c27e65885309f596214c27c6588530b798e214c2dd6388530ddd46214c37451885309fd95214c27e65485309f195214c2df6348530b718d214c3775148530dd145214c2fb6048530be181214c27e65085309f594214c27c6508530b798c214c2dd6308530ddd44214c3745108530be980214c2f960085309f997404c33f54d0130cf153404c2de63d0130b758f404c2f661d0130bd587404c37751d0130dd147404c3b541d01309f996404c3775190130dd146404c2fa6590130de996404c2f96490130de952404c3785490130f6d8e404c2fa6390130f618e404c3da4390130f650e404c37b5290130f68ca404c3d83290130fcd46404c3f05190130fc906404c3f14190130f6cc6404c3d931901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c3775150130dd145404c3b54150130be195404c37865501309e195404c3bb6450130eed51404c37a5450130de151404c3b85450130f6d8d404c2f86350130f618d404c3da4350130f650d404c37b5250130f68c9404c3d83250130fcd45404c3f05150130eed05404c3f24150130ee505404c3f14150130ec505404c3db3150130f64c5404c27e6510130b798c404c2dd6310130bb988404c2ed6210130bd984404c2f56110130ddd44404c3745110130be980404c37751cc130dd147304c2fb64cc130be593304c3da43cc130f650f304c3da32cc130f60cb304c3f351cc130fc147304c3f241cc130fc507304c3db31cc130f64c7304c2ee628c130bb58a304c377518c130dd146304c2df648c130b7592304c2de628c130f398a304c2ce628c130f358a304c2dd618c130f5d46304c3d4518c130f5906304c3d5418c130f6d42304c3da408c130f6502304c27e63d5030d798f540c27e62d50309f58b540c27e61d50309f587540c27e60d5030de983540c27d6595030cfd52540c2f66195030bd586540c27e62950309f58a540c27e6195030dd986540c27661950309f586540c37561950309d586540c33f64550309fd8d540c27d63550309fd89540c27c62550309fd85540c27c6155030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6415030cf990540c27e6315030d798c540c25e63150309f988540c36e62150309b988540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a60150309e980540c27e6494c309f592530c27d65d0c30bd987430c2f561d0c30
  | 20 => 0xc2de628c930d7d4a324c3cf528c930f314a324c3ce428c930f350a324c2dd618c930b7982324c3da608c930b6982324c3d9608c930dbd49324c36c524c930bed81324c2f8604c9309f994324c3cd320c930b7994324c35e650c930b7d90324c2dd640c930d7950324c35c540c930b7988324c3ce620c930d7d48324c3ce520c930f3548324c3cf420c930f3108324c2dd610c930b7980324c27e64d45309f593514c27e62d45309f58b514c2f564d4530ddd53514c37654d4530dd553514c37454d4530f5d8f514c3d643d4530f550f514c37752d4530dd94b514c37552d4530dd14b514c3d632d4530f50cb514c37764d4530dd993514c37564d45309d593514c37464d4530ddd8f514c37743d4530dd90f514c37543d4530dd10f514c37762d4530dd98b514c37562d4530dd18b514c37742d4530dd90b514c37542d4530dd10b514c37732d4530dd8cb514c37532d4530dd0cb514c37760d4530dd583514c3775194530dd544514c27e64145309f590514c27e62145309f588514c2f66514530dd994514c2f56414530ddd50514c3765414530dd550514c3745414530f558c514c3d64314530f550c514c3775214530dd948514c3755214530dd148514c3d63214530f50c8514c3776414530dd990514c37564145309d590514c3746414530ddd8c514c3774314530dd90c514c3754314530dd10c514c3776214530dd988514c3756214530dd188514c3774214530dd908514c3754214530dd108514c3773214530dd8c8514c3753214530dd0c8514c3776014530dd580514c37530145309f997414c27d65d05309f197414c2de63d0530b758f414c37751d0530dd147414c2fa60d0530be583414c27e65905309f596414c27c6590530b798e414c2dd6390530ddd46414c3745190530ddd96414c2f66590530dd996414c2766590530dd596414c2f46590530dd196414c2746590530bd592414c3775490530dd952414c3755490530dd152414c3d66390530f558e414c3d64390530f550e414c3775290530dd14a414c3d63290530f50ca414c27f65505309f995414c27c6550530ddd45414c3745150530ddd95414c2f66550530dd995414c2766550530dd595414c2f46550530dd195414c2746550530edd91414c3775450530dd951414c3755450530dd151414c3d66350530f558d414c3d64350530f550d414c3775250530dd149414c3d63250530f50c9414c27e65105309f594414c27c6510530b798c414c2dd6310530bd984414c3775110530dd144414c2fa6010530be580414c27e65cc530dd147314c2de65cc530d7997314c2df64cc530b7593314c2de62cc530f5d47314c35c51cc530f5147314c35451cc530f5907314c3d541cc530b7983314c2dd638c530ddd46314c374518c530be982314c2f9608c530ddd45314c374514c530bed8
  | 21 => 0x5450230be18d408c3ea5250230de549408c3e95250230da549408c3bb4150230fc905408c3b94150230fc505408c3b14150230cf950408c33d5410230b798c408c2dd6310230bb988408c2ed6210230db948408c36d5210230bd984408c2f56110230db94b308c36d52cc230b7597308c35d65cc230d7d53308c35d54cc230d794b308c3ce52cc230d394b308c3cd52cc230d7547308c3d641cc230f5507308c2f965cc230de597308c2fb64cc230be593308c3ea52cc230fa54b308c3f241cc230fc507308c27e62d51309f58b544c37761d51309f987544c27d61d5130dd187544c33f5495130bd986544c2f561951309f992544c27d6395130d758e544c27e62951309f58a544c27e6195130dd986544c27661951309f586544c37561951309d586544c27d6095130de582544c2ef6255130bb189544c2f76155130bd185544c33f64551309fd8d544c35f63551309fd89544c36f62551309bd89544c27c6255130db189544c26c62551309fd85544c37761551309dd85544c27c6155130dd185544c27461551309fd81544c37b60551309f994544c33d5415130bb988544c2ed6215130bd984544c2f56115130cf990544c27e6315130d758c544c27c63151309f988544c36e62151309b988544c27d6215130db588544c26d62151309f984544c37661151309d984544c27d6115130dd584544c2756115130de580544c27e65d0d30cfd53434c33c54d0d30bd987434c2f561d0d30be983434c2f960d0d309f996434c2de6590d30d7996434c2dd6490d30d7952434c35c5490d30b798a434c2dd6190d30f6d82434c2de6090d30f6182434c27c6550d30cfd51434c33c5450d30bbd89434c2ec6250d30bed81434c2f86050d30d7195434c25c6550d30e7d91434c39f5450d30d7951434c35c5450d30e7151434c3cf6250d30b7189434c3cc6250d30b3189434c2df6150d30f6d81434c2dc6050d30f6181434c27e6510d30b798c434c2ee6210d30bb588434c2f66110d30bd584434c2fa6010d309f993524c27d64d4930d790f524c35d43d49309f987524c27d61d4930dbd4a524c2f66194930bd586524c2bf6454930af191524c2f76154930bd185524c36d52149309f990524c27d64149309f984524c27d61149309f997424c27d65d09309f197424c2de63d0930b758f424c36f52d0930db14b424c2f661d0930bd587424c2fa60d0930be583424c27e65909309f596424c27c6590930cfd52424c33c54909309fd95424c27e65509309f195424c2df6350930b718d424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930dbd48424c36c5210930bd984424c2f56110930be980424c2f960109309f997324c36f528c930db14a324c2fa608c930be582324c2df648c930b7592324c35e548c930d7152324
  | 22 => 0xa30db185528c36e6054a30db181528c36d5214a309fd97428c27e65d0a309f597428c36e52d0a30db54b428c2f661d0a30bd587428c2fa60d0a30be583428c27f6590a309f996428c27d6590a30db94a428c36d5290a309fd95428c27d6550a309f195428c2df6350a30b718d428c36e5250a30db549428c27f6510a309f994428c27d6510a30b798c428c2dd6310a30db948428c36d5210a30bd984428c2f56110a30be980428c2f96010a30db94b328c36e528ca30db54a328c2fa608ca30be582328c36e524ca30db549328c2fb604ca30be181328c36d520ca30f34c8328c2ee62d4630bb58b518c36e52d4630db54b518c36e5294630db54a518c37751946309f992518c27d64946309f98a518c27d6294630db949518c36d52546309fd91518c27c64546309fd89518c27c6254630af990518c2bd6414630bb988518c2ed6214630db948518c36d5214630dd544518c27f65d06309f997418c27d65d0630cf953418c33d54d0630db94b418c36d52d0630be983418c2f960d06309fd96418c27e65906309f596418c36e5290630db54a418c3765190630dd546418c3776590630dd996418c3756590630dd196418c3775490630dd952418c3755490630dd152418c3765290630f994a418c3665290630dd54a418c3e55290630d954a418c27f65506309f595418c27c6550630cf951418c33d5450630b7d8d418c2dc6350630db949418c36d5250630dd945418c3755150630ddd95418c3766550630dd595418c3746550630edd91418c3775450630dd951418c3b65450630cd951418c3755450630ed551418c3355450630dd151418c3d76350630f518d418c3765250630f9949418c3665250630dd549418c3e55250630d9549418c27f65106309f994418c27d6510630db948418c36d5210630be980418c2f96010630db94b318c36d52cc630db94a318c36d528c630dd946318c375518c630be982318c2f9608c630db949318c36d524c630dd945318c375514c630bed81318c2f8604c630db948318c36d520c6309fd97218c27e65c86309f597218c2de63c8630b758f218c36e52c8630db54b218c27f65886309f996218c27d6588630db94a218c36d52886309fd95218c27d65486309f195218c36e5248630db549218c2fb6048630be181218c27f65086309f994218c27d6508630db948218c36d5208630be980218c2f96008630db94b408c36d52d0230bd987408c2f561d0230ed507408c33e5490230cf552408c2de6390230b758e408c36e5290230db54a408c2f96590230de596408c37a5490230ee952408c3b95490230de152408c2fa6390230f698e408c3d96390230fa94a408c3795290230fa54a408c3695290230fc906408c3f14190230db949408c36d5250230ed505408c2fb6550230ded95408c3bb6450230de951408c378
  | 23 => 0xd94541cc3755150730bed8141cc2f86050730ddd9541cc3766550730dd59541cc3746550730edd9141cc3775450730dd95141cc3755450730dd15141cc3d66350730f558d41cc3d64350730f550d41cc3765250730dd54941cc3d63250730f50c941cc3f36050730fc18141cc27f65107309f99441cc27d6510730b798c41cc2dd6310730dd94731cc37551cc730be98331cc2f960cc730b7d9331cc2dd64cc730b798b31cc35e51cc730f594731cc3d551cc730f590731cc3d541cc730b798331cc3da60cc730f658331cc2df654c730d7d9531cc2df644c730b759131cc2dc624c730f5d8531cc35e514c730f590531cc3d5414c730b718131cc376510c730dd54431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730b7d8f21cc2dc63c8730dd94721cc37551c8730be98321cc2f960c87309fd9621cc27e65887309f59621cc2de6388730b758e21cc36e5288730db54a21cc27f65487309f59521cc27c6548730b7d8d21cc2dc63487309fd9421cc27e65087309f59421cc2de6308730b758c21cc36e5208730db54821cc3765108730dd54421cc33e54d0330cf55340cc2de63d0330b758f40cc2f661d0330bd58740cc3b541d0330cf95140cc33d5450330b7d8d40cc2dc6350330ed50540cc2de6310330b758c40cc2ee6210330bb58840cc2f66110330bd58440cc2ee62d5230bb58b548c35d63d52309f98b548c36e62d52309b98b548c27d62d5230db58b548c26d62d52309f987548c27d61d5230de983548c33f5495230bd986548c2f561952309f98a548c27d62952309f986548c37661952309d986548c27d6195230dd586548c2756195230de982548c33f64552309fd89548c27c62552309fd85548c27c6155230cf550548c2ee6215230bb588548c2f66115230bd584548c33e6415230d758c548c27e6215230db988548c26e62152309f588548c36d62152309b588548c27e6115230dd984548c27661152309f584548c37561152309d584548c37a6015230cf953438c33d54d0e30bd987438c2f561d0e30be983438c2f960d0e30cf951438c33d5450e30bbd89438c2ec6250e30bed81438c2f86050e30bb988438c2ed6210e30bd984438c2f56110e30be580438c36f5294a309f992528c27d6494a309f986528c27d6194a30dbd52528c36e5494a30db552528c36c5494a30dbd92528c36e6494a30db592528c36c6494a30dbd8e528c36f4394a30db90e528c36d4394a30db10e528c36f6194a30db986528c36d6194a30db186528c36e6094a30db182528c27f6454a309f191528c27f6154a309f185528c36f6554a30dbd51528c36e5454a30db551528c36c5454a30dbd91528c36e6454a30db591528c36c6454a30db58d528c36f4354a30db90d528c36d4354a30db10d528c36f6154a30db985528c36d6154
  | 24 => 0x40103bb6450040de95140103ba5450040f694d40103795350040f654d40103595350040fa94940103795250040fa54940103695250040fc94540103f15150040fc90540103f14150040d798f54cc27e62d53309f58b54cc27e61d53309f58754cc37960d5330cfd5254cc2f66195330bd58654cc35e63953309f98a54cc27d62953309f98654cc37661953309d98654cc27d6195330dd58654cc2756195330cfd9154cc27f62553309f18954cc27f61553309f18554cc33d5415330bb98854cc2ed6215330bd98454cc2f56115330cf99054cc35e63153309f98854cc36e62153309b98854cc27d6215330db58854cc26d62153309f98454cc37661153309d98454cc27d6115330dd58454cc2756115330de58054cc2f661d0f30bd58743cc33e5490f30cf55243cc2fa6090f30be58243cc35d6590f30d795243cc39e5490f30e755243cc35c5490f30b798a43cc2dd6190f30b798243cc3da6090f30f658243cc2ef6250f30bb18943cc2df6550f30d7d9543cc39f6450f30d795143cc35c5450f30f3d8943cc2dc6250f30f318943cc2cc6250f30b7d8543cc2dc6050f30cf95043cc33d5410f30bb98843cc2ed6210f30bd98443cc2f56110f30be98043cc2f96010f30bd98752cc2f561d4b30dbd4a52cc27e6494b309f59252cc27e6194b309f58652cc27f6454b309f19152cc35e4354b30d750d52cc27f6154b309f18552cc36d5214b309fd9742cc27e65d0b309f59742cc2de63d0b30b758f42cc2f661d0b30bd58742cc27f6590b309f99642cc27d6590b30db94a42cc36d5290b309fd9542cc27d6550b309f19542cc2df6350b30b718d42cc36e5250b30db54942cc27f6510b309f99442cc27d6510b30b798c42cc2dd6310b30bd98442cc2f56110b30be98042cc2f96010b30db94b32cc36d52ccb30be98332cc2f960ccb30b759632cc35d658cb30b7d9232cc2dd648cb30d795232cc35c548cb30d754a32cc3ce428cb30f350a32cc2dd618cb30b798232cc36e520cb30db54832cc3cd320cb30be98032cc2f9600cb30b7d9032cc2dd640cb30d795032cc35c540cb30f398832cc3ce520cb30d754832cc3cd520cb30d354832cc3cf420cb30f310832cc2dd610cb30b798032cc3da600cb30f658032cc2ee62d4730bb58b51cc37751947309f99251cc27d64947309f98a51cc27d62947309fd9151cc27c64547309fd8951cc27c6254730dd54451cc27f65d07309f99741cc27d65d0730b798f41cc2dd63d07309fd9641cc27e65907309f59641cc2de6390730b758e41cc3765190730dd54641cc3776590730dd99641cc3756590730dd19641cc3775490730dd95241cc3755490730dd15241cc3d66390730f558e41cc3d64390730f550e41cc3765290730dd54a41cc3d63290730f50ca41cc27f65507309f59541cc27c6550730d
  | 25 => 0x36d5214440bd98451103755114440cf953411035e53d0440d754f411036e52d0440db54b411037651d0440dd54741102fa60d0440be583411027d6590440d794e411035d5390440db94a411036d5290440dd54641102f56590440dd59641102756590440bd59241103765490440dd94e41103d65390440d594e41103755390440f554e41103555390440dd94a41103e65290440d994a41103755290440f954a411036552904409fd95411033e5450440d794d411035d5350440db949411036d5250440dd94541102f76550440ddd9541102776550440edd9141103765450440cd95141103765350440f594d41103565350440dd54d41103d55350440d554d41103765250440f994941103665250440dd54941103e55250440d9549411035e5310440d754c411036e5210440db54841102f66110440dd94441103755110440be98041102f960104409fd97311027e65cc4409f597311035e53cc440d754f311036e52cc440db54b311037651cc440dd547311027f658c4409f996311027d658c440d794e311035d538c440db94a311036d528c440dd9463110375518c4409fd95311027d654c4409f195311035e534c440d754d311036e524c440db5493110376514c440dd54531102fb604c440be181311027f650c4409f994311027d650c440d794c311035d530c440db948311036d520c440dd9443110375510c4409fd97211027e65c84409f597211035e53c8440d754f211036e52c8440db54b211037651c8440dd547211027f65884409f996211027d6588440d794e211035d5388440db94a211036d5288440dd946211037551884409fd95211027d65484409f195211035e5348440d754d211036e5248440db54921103765148440dd54521102fb6048440be181211027f65084409f994211027d6508440d794c211035d5308440db948211036d5208440dd94421103755108440dd90650103754194040d794f401035d53d0040db94b401036d52d0040bd98740102f561d0040dd947401037551d0040ed90740103b541d0040e794f401039d53d0040eb94b40103ad52d0040ed98740103b561d0040ed947401033d51d0040ed547401033551d0040af592401033e5490040d794e401035d5390040db94a401036d5290040dd94640103755190040be592401037a5490040ee95240103da5390040de54e40103d95390040d654e40103ea5290040de54a40103e95290040da54a40103f25190040fc54640103f24190040fc506401027f6550040d794d401035d5350040db949401036d5250040dd94540103755150040ed90540103b54150040afd95401033f65500408fd95401039e5350040e754d40103ae5250040eb54940103b65150040cf54540103b55150040cd54540102bf6050040cf94140102fb6550040ded95401027b6550040bed91
  | 26 => 0x194840db986521036d6194840db186521036e6094840db182521035e5354840d754d521027f63548409f18d521027f61548409f185521036f6554840dbd4d521036e5354840f394d521034e5354840db54d52103cd5354840d354d521036c5354840db991521036f6354840db98d521036d6354840db18d521036f4354840db90d521036d4354840db10d521036f6154840db985521036d6154840db185521036e6054840db181521036c4054840b798c52102dd6314840d794c521035d5314840bb988521036d5214840bd98452102f56114840d794f421035d53d0840db94b421036d52d0840bd98742102f561d0840be98342102f960d08409f596421035e5390840d754e421036d52908409fd9542102df6350840b718d421035e5350840d754d421036e5250840b798c42102dd6310840d794c421035d5310840db948421036d5210840bd98442102f56110840be98042102f960108409fd97321027e65cc8409f597321035e53cc840d754f321036e52cc840db54b321027f658c8409f996321027d658c840d794e321035d538c840db94a321036d528c8409fd95321027d654c8409f19532102bf644c840af191321035e534c840d754d321036e524c840db549321027f650c8409f994321027d650c840d794c321035d530c840db948321036d520c840f34c832102de63d4440b758f511035e53d4440d754f51102ee62d4440bb58b511036e52d4440db54b511035e5394440d754e511036e5294440db54a511037751944409f98e511027d63944409f98a511027d6294440ddd4e51103765394440f594e51103565394440dd54e51103d55394440d554e51103745394440ddd4a51103765294440f994a51103665294440dd54a51103e55294440d954a51103745294440dd19251103776394440dd98e51103756394440dd18e51103774394440dd90e51103754394440dd10e51103776294440dd98a51103756294440dd18a51103774294440dd90a51103754294440dd10a51103773294440dd8ca51103753294440dd0ca51103766094440dd182511035e5354440d754d511036e5254440db549511027f63544409f18d511027f62544409f18951103776554440ddd4d51103765354440f594d51103565354440dd54d51103d55354440d554d51103745354440ddd4951103765254440f994951103665254440dd54951103e55254440d954951103745254440dd99151103776354440dd98d51103756354440dd18d51103774354440dd90d51103754354440dd10d51103776254440dd98951103756254440dd18951103774254440dd90951103754254440dd10951103773254440dd8c951103753254440dd0c951103766054440dd18151103744054440b798c51102dd6314440d794c511035d5314440bb98851102ed6214440db9485110
  | 27 => 0x40ddd4941503745250540edd0941503b64250540ed50941503b44250540fcd8141503f06050540edd9541503b46550540edd8d41503b66350540ed58d41503b46350540edd4d41503b65350540ed54d41503b45350540edd8941503b66250540ed58941503b46250540edd4941503b65250540ed54941503b45250540edcc941503b63250540ed4c941503b43250540edd8141503b36050540ed98141503b56050540ed18141503b060505409f99441502be6410540bd98441503b541105409f997315027d65cc5409f197315037751cc540dd14731503b541cc540be98331502f960cc5409f996315027d658c5409f19631502be648c540af592315035f538c540d714e31503b5418c5409fd95315027e654c5409f19531503b5414c5409f994315027d650c5409f19431502be640c540af590315035f530c540d714c3150377510c540dd14431503b5410c540be98031502f9600c5409f997215027d65c85409f197215037751c8540dd14721503b541c8540be98321502f960c85409f996215027d65885409f19621502be6488540af592215036f5288540db14a21503b541885409fd95215027e65485409f19521503b541485409f994215027d65085409f19421502be6408540af590215036f5208540db14821503775108540dd14421503b54108540be98021502f96008540bd98740502f561d0140ed50740502f963d0140be58b40503f261d0140fc58740503bb41d0140fc90740503b941d0140fc50740503b141d0140ed90640503b54190140af58640503bb5090140dd98654103756195040bb98b53102ed62d4c40bd98753102f561d4c40d7d4e531027e6294c409f58a531027e6194c409f586531035c6494c40d7d8a531035e6294c40d758a531035c6294c40d7d86531035e6194c40d7586531035c6194c40d7982531035c6094c409fd89531027c6254c409fd85531027c6154c40d7d95531035e6454c40d7d89531035e6254c40d7589531035c6254c40d7d85531035e6154c40d7585531035c6154c40d7981531035c6054c40d710153102de6314c40d754c53102ee6214c40bb58853102f66114c40bd584531035e53d0c40d754f43102f661d0c40bd58743102fa60d0c40be583431027d6590c40d754e431027f6550c40d794d43102ef6250c40bb189431035e5310c40d754c43102ee6210c40bb58843102f66110c40bd58443102fa6010c40be58043102de63d4840b758f521035e53d4840d754f52102f661d4840bd587521035e5394840d754e521036f52948409f98e521027d63948409f986521027d6194840dbd4e521036e5394840f394e521034e5394840db54e52103cd5394840d354e521036c5394840db192521036f6394840db98e521036d6394840db18e521036f4394840db90e521036d4394840db10e521036f6
  | 28 => 0x58241903765150640dd54541902fb6050640be18141903b76450640dd94d41903755350640dd94941903755250640fcd8141903f060506409fd97319027e65cc6409f597319035e53cc640d754f31902fa60cc640be583319027f658c6409f996319027d658c6409fd95319027d654c6409f195319035e534c640d754d319027f650c6409f994319027d650c640be98031902f9600c6409fd97219027e65c86409f597219036e52c8640db54b21902fa60c8640be583219027f65886409f996219027d65886409fd95219027d65486409f195219036e5248640db549219027f65086409f994219027d6508640be98021902f96008640bd98740902f561d0240ed90740903b541d0240af597409033d65d0240ed98740903b561d0240cf54740902f965d0240de59740902f963d0240be58b40903f261d0240fc58740903f241d0240fc507409027e62d4d409f58b535027e61d4d409f587535035f5394d40bbd8953502ec6254d40bdd8553502f46154d40d754c535027e6214d409f588535027e6114d409f58453503796014d409f99743502f661d0d40bd587435035f5390d40d714e43502fa6090d40be582435035f5350d40d714d43502ef6250d40bb18943502fb6050d40be181435027e6510d40bb98843502ed6210d40bd98443502f56110d40be980435027e63d49409f58f525027e61d49409f587525036f5294940b7d8d52502dc6354940bdd8552502f46154940db548525027e63149409f58c525027e61149409f584525037960149409f99742502f661d0940bd587425036f5290940db14a42502fa6090940be58242502df6350940b718d425036f5250940db14942502fb6050940be181425027e6510940b798c42502dd6310940bd98442502f56110940be980425027e65cc9409f597325027c65cc940dbd4b325036c52cc940be98332502f960cc9409f996325027d658c9409f196325035f538c940d714e32502fa608c940be582325027f654c9409f995325027c654c9409f994325027d650c9409f19432502be640c940af590325035f530c940d714c325036f520c940db14832503cd320c940be98032502f9600c9409f98f515027d63d45409f98b515027d62d4540ddd4651502df6354540b718d51502ef6254540bb189515037551145409f98c515027d63145409f988515027d62145409f99741502be65d0540cf997415033c51d0540af98341502bd6490540ddd4641503745190540be98241502f96090540bd59241502b56490540ddd4e41503745390540ddd4a41503745290540fc98241503f16090540ddd4541503745150540bed8141502f86050540edd8541503b75150540cf14541503b45150540eed8141502bc6050540ee18141503b76450540ddd4d41503745350540edd0d41503b64350540ed50d41503b443505
  | 29 => 0x1d02b76550740cdd9541d03b76350740ed98d41d03b56350740ed18d41d03b75350740ed94d41d03b55350740ed14d41d03b76250740ed98941d03b56250740ed18941d03b75250740ed94941d03b55250740ed14941d03b73250740ed8c941d03b53250740ed0c941d03b76050740ed98141d03b56050740ed18141d03765110740dd54441d03b54110740be98041d02f960107409fd9731d027e65cc7409f59731d037651cc740dd54731d03b541cc7409fd9631d027e658c7409f59631d02be648c740af59231d0376518c740dd54631d03b5418c7409fd9531d027d654c7409f19531d0376514c740dd54531d03b5414c740bed8131d02f8604c7409fd9431d027e650c7409f59431d02be640c740af59031d0376510c740dd54431d03b5410c7409fd9721d027e65c87409f59721d037651c8740dd54721d03b541c87409fd9621d027e65887409f59621d02be6488740af59221d03765188740dd54621d03b541887409fd9521d027d65487409f19521d03765148740dd54521d03b54148740bed8121d02f860487409fd9421d027e65087409f59421d02be6408740af59021d03765108740dd54421d03b54108740bb98b53902ed62d4e40d7d4e539027e6294e409f58a539027e6194e409f586539037a6094e40bdd8553902f46154e409fd89539027c6254e409fd8553903776154e409dd85539027c6154e40dd18553902746154e40d754c53902f661d0e40bd587439035e5390e40d754e43902fa6090e40be582439035e5350e40d754d43902ef6250e40bb18943902fb6050e40be18143902ee6210e40bb58843902f66110e40bd58443902f96010e40b798f52902dd63d4a40dbd4a529027e6394a409f58e529027e6194a409f586529037a6094a40bdd8552902f46154a409fd8d529027c6354a409fd8552903776154a409dd85529027c6154a40dd18552902746154a40db54852902f661d0a40bd587429036e5290a40db54a42902fa6090a40be58242902df6350a40b718d429036e5250a40db54942902fb6050a40be18142902de6310a40b758c42902f66110a40bd58442902f96010a409fd97329027e65cca409f597329036e52cca40db54b32902fa60cca40be583329027f658ca409f996329027d658ca40d794e329035d538ca40be98232902f9608ca409fd95329027d654ca409f19532902bf644ca40af191329027f650ca409f994329027d650ca40d794c329035d530ca40db948329036d520ca40f34c832902fa600ca40be580329037751946409f98e519027d63946409f98a519027d62946409fd8d519027c63546409fd89519027c6254640b798c51902dd6314640bb98851902ed6214640dd54451903765190640dd54641902fa6090640be58241903765390640dd54e41903765290640dd54a41903f26090640fc
  | 30 => 0x5f5394f409f98a53d027d6294f409f98653d027d6194f40bbd8953d02ec6254f409fd8953d036f6254f409bd8953d027c6254f40db18953d026c6254f409fd8553d027c6154f40d754c53d02ee6214f40bb58853d02f66114f40bd58453d035e53d0f40d754f43d02f661d0f40bd58743d02fa60d0f40be58343d02ef6250f40bb18943d035e5310f40d754c43d02ee6210f40bb58843d02f66110f40bd58443d02fa6010f40be58043d02f661d4b40bd58752d036f5294b409f98e52d027d6394b409f98652d027d6194b40b7d8d52d02dc6354b409fd8d52d035f6354b4097d8d52d027c6354b40d718d52d025c6354b409fd8552d027c6154b40b798c52d02dd6314b40db54852d02f66114b40bd58452d036e52d0b40db54b42d02f661d0b40bd58742d02fa60d0b40be58342d02df6350b40b718d42d02de6310b40b758c42d036e5210b40db54842d02f66110b40bd58442d02fa6010b40be58042d027f65ccb409f99732d027d65ccb40d794f32d035d53ccb409fd9632d027e658cb409f59632d036e528cb40db54a32d027f654cb409f59532d027c654cb40d794d32d035d534cb40db94932d036d524cb409fd9432d027e650cb409f59432d02be640cb40af59032d03cd320cb40ddd4651d027e63947409f58e51d027e62947409f58a51d03b66494740ddd4e51d03765394740dd54e51d03745394740ddd4a51d03765294740dd54a51d03745294740dd19251d03776394740dd98e51d03756394740dd18e51d03774394740dd90e51d03754394740dd10e51d03776294740dd98a51d03756294740dd18a51d03774294740dd90a51d03754294740dd10a51d03773294740dd8ca51d03753294740dd0ca51d03776094740dd58251d027f63547409f18d51d027f62547409f18951d03776554740ed99151d03775354740dd94d51d03755354740dd14d51d03775254740dd94951d03755254740dd14951d03766454740ddd8d51d03766354740dd58d51d03746354740ddd0d51d03764354740dd50d51d03744354740ddd8951d03766254740dd58951d03746254740ddd0951d03764254740dd50951d03744254740ddcc951d03763254740dd4c951d03743254740ddd8151d03756054740dd54451d037651d0740dd54741d02fa60d0740be58341d033e51d0740ed94741d03b551d0740af98341d03ba60d0740ee58341d03755190740bd59641d03756590740dd94e41d03755390740dd94a41d03755290740dd94541d02bf6550740cfd9541d03b76150740edd4541d033e5150740ed94541d03365150740ed54541d03b45150740af18141d02f76550740ddd9541d03b76450740dd94d41d03755350740edd0d41d03b64350740ed50d41d03b44350740dd94941d03755250740edd0941d03b64250740ed50941d03b44250740edd954
  | 31 => 0x14c21d798c530867e6214c21db988530867e6114c21dd984530867e6014c21de980530867a6014c219f58053087796014c219e580530867f65d0c219f997430867d65d0c219f197430873e54d0c21cf55343086f661d0c21bd587430867f6590c219f996430867d6590c219f196430875e5390c21d754e430867f6550c219f995430867d6550c219f195430873e5450c21cf551430875e5350c21d754d43086ef6250c21bb189430867f6510c219f994430867d6510c219f19443086ee6210c21bb58843086f66110c21bd58443086fa6010c21be580430867e64948219f592520867e63948219f58e520867d65d0821bd587420867f65908219f596420873e5490821cf55242086f66190821bd586420867f6550821b7d8d42086dc63508219fd94420867d6510821cf950420873d5410821b798c42086dd6310821bd98442086f56110821be98042086f960108219f597320867f658c8219f596320875e538c821d754e32086f6618c821bd586320867f654c8219fd94320867d650c821d794c320875d530c821f34c832086f6610c821bd584320867e64944219f592510867e63944219f58e510867d65d04219fd96410867d6590421cf952410873d5490421bb98a41086ed6290421dd94641087776590421bd596410877565904219d59641086f56490421ddd5241087765490421ed95241087755490421ed55241087355490421dd15241087775390421dd94e41087755390421dd14e41087e66290421bd58a41087e56290421dd94a41086f660904219fd9541087765150421bdd9541087776550421edd9141087775450421dd95141087755450421dd15141087775350421dd94d41087755350421dd14d41086f76250421dd94941086f460504219fd94410867e65104219f594410867c6510421cf950410873d5410421bb98841086ed6210421bd984410867d65cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c4219fd95310867f650c4219f994310867d650c4219f194310875e530c421d754c31086ee620c421bb58831087e641c8421f950721086ed6288421db94a21086f76488421bd59221087775488421dd55221086f56288421dd94a21087e65288421bd982210867f6548421bbd95210876f65484219bd9521086ef6148421db94521087e63148421f94c521086f76548421ddd9521086776548421bdd9121086f56448421ddd5121087755448421bdd8921087e76248421dd94921087e65248421f98c921087e53248421bd181210877b50940219f992500867d64940219f98e500867d6394021dd906500877541940219fd91500867c64540219fd8d500867c6354021dd90550087754154021dbc85500876d2154021af99050086bd6414021b798c50086dd6314021de54050086f661d4f40bd58753d03
  | 32 => 0x19f996434867d6590d219f196434867f6550d219f995434867d6550d219f19543486ef6250d21bb189434867f6510d219f994434867d6510d219f194434875f5310d21d714c43486ee6210d21bb58843486f66110d21bd58443486fa6010d21be580434867e65d0921cfd53424873c54d0921bd98742486f561d09219f996424867c6550921cfd51424873c5450921b7d8d42486dc6350921bdd8542486f461509219f99442486de6310921b758c42487ad4210921bd98442486fa6010921be580424867e65cc921d7d4f324875c53cc921bd98732486f561cc9219f996324867c654c921d7d4d324875c534c921bdd8532486f4614c9219f99432487cd320c9219f997414873f54d0521cf15341486ee62d0521bb58b414867e6590521bd99641487766590521bd59241487775490521dd95241487755490521dd15241487775390521dd94e41487755390521dd14e41486f662905219fd95414867d65505219f195414873f5450521cf15141486ef6250521bb18941487766550521bd195414877465505219d19541487b76450521ddd5141487b75450521cdd5141487765450521dd55141487745450521ed15141487775350521dd94d41487755350521dd14d41487e76250521bd18941487e462505219f99441486f661105219f997314875f53cc521d714f31486ee62cc521bb58b314867e658c5219fd95314867d654c5219f195314875f534c521d714d31486ef624c521bb189314867e650c521f54c431486f764c8521bd593214877754c8521dd55321487e75188521f990621487e54188521bb582214867e64d41219f593504867e63d41219f58f504877641d4121dd50750486de6394121b758e504877b5094121de540504867e64141219f590504867e63141219f58c50487764114121dd504504877721141219f98f540867d63d50219f98b540876e62d50219f987540877661d50219f983540867d60d50219f596540873f54950219f98e540867d6395021dd986540867e60950219f582540873f64550219fd8d540867c6355021dd985540867f60550219f181540873d5415021b798c54086dd6315021be98054086f960150219f990540873e64150219f98c540875e63150219798c540867d6315021d758c540865d63150219f988540876e62150219f984540877661150219d984540867e6015021de980540867a60150219f580540877960150219e580540867e64d4c219f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530867f6454c219f191530875f6354c219fd81530867c6054c21af99053086bd6414c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e63
  | 33 => 0x4f438875d53d0e21bd98743886f561d0e219fd96438867e6590e219f596438867c6590e21cf952438873d5490e219fd95438867e6550e219f595438867c6550e21bbd8943886ec6250e219fd94438867e6510e219f594438867c6510e21cf950438873d5410e21d794c438875d5310e21bb98843886ed6210e21bd98443886f56110e21be98043886f96010e21cf953428873d54d0a21bd98742886f561d0a21cf951428873d5450a21b7d8d42886dc6350a21bdd8542886f46150a21b798c42886dd6310a21bd58442886fa6010a21be580428875e53cca21d754f32886f661cca21bd587328875e534ca21d754d32886f7614ca21bd18532887cd320ca21cf952418873d5490621bb98a41886ed6290621bd59641887756590621dd95241887b65490621dd55241887b55490621cd55241887745490621ddd4e41887765390621dd54e41887745390621bd98a41887e66290621f958a41886f76550621ddd9541887b76450621ddd5141887765450621dd55141887745450621ddd4d41887765350621dd54d41887745350621bd189418873e5410621cf55041886ee6210621bb588418875e538c621d754e31886ee628c621bb58a318875e530c621d754c31886ee620c621bb58831887d5310c621bb597218876d65c8621bd597218877565c8621bdd9321886f564c8621ddd53218877554c8621ded42508867e64942219f592508867e63942219f58e50887764194221dd506508877721942219fd91508867c64542219fd8d508867c6354221dd90550887754154221dbc8550886be6414221af59050886de6314221b758c508877950142219f98f544867d63d5121ddd87544867e60d51219f583544873f54951219f992544867e63951219f58e544867d6295121db58a544867d6195121dd586544867561951219f982544867d6095121b7d8d54486dc6355121bed8154486f86055121cfd91544867f6355121d7d8d544865f63551219f18d544875c63551219718d544867f6255121dbd89544867f6155121ddd85544867f6055121ded81544867b60551219f181544877860551219e181544867e6515121cf550544873e64151219f98c544867d6315121dd584544867e60151219f580544867e64d4d219f593534867e60d4d219f583534875f5394d21be98253486f96094d219f992534867d6494d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d21de982534867a6094d219f58253487796094d219e582534867f6454d219f191534875f6354d219fd89534876f6254d219fd8553487776154d219fd81534867c6054d219f994534875d5314d219f990534867d6414d21d798c534867e6014d219f580534867f65d0d219f997434867d65d0d219f197434875f53d0d21d714f43486f661d0d21bd587434867f6590d2
  | 34 => 0xc867d64d4f21db98b53c877561d4f219f98353c877a60d4f219e98353c867d60d4f21de58353c867960d4f21d7d4e53c867e6494f219f59253c867e6094f219f58253c867f6454f219f19153c875f6354f219fd8153c867c6054f21d754c53c867e6414f219f59053c875e6314f21db98853c87756114f219f98053c867d6014f219fd9743c867e65d0f219f59743c867c65d0f21bd98743c86f561d0f219fd9643c867e6590f219f59643c867c6590f21d794e43c875d5390f219fd9543c867e6550f219f59543c867c6550f21d794d43c875d5350f21bbd8943c86ec6250f219fd9443c867e6510f219f59443c867c6510f21bb98843c86ed6210f21bd98443c86f56110f21be98043c86f96010f21bd98742c873e5490b21cf55242c86f66190b21bd58642c86df6350b21b718d42c873e5410b21cf55042c86de6310b21b758c42c87ad4210b21bd98442c86f56110b21be98042c86f96010b21d794e32c875d538cb21bd98632c86f5618cb21d794c32c875d530cb21f34c832c86f6610cb21bd58432c873e54d0721cf55341c86ee62d0721bb58b41c86f56590721dd59641c87775490721dd95241c87755490721dd15241c87775390721dd94e41c87755390721dd14e41c86f56290721bd98241c873e5450721cf55141c86ef6250721bb18941c86f76550721ddd9541c87b76450721dd95141c87b65450721dd55141c87b55450721cd55141c87745450721ddd4d41c87765350721dd54d41c87745350721bdd8941c87e76250721f918941c86f46050721d794f31c875d53cc721bb98b31c86ed62cc721d794d31c875d534c721bbd8931c86ec624c721b798f50c86dd63d4321b798e50c86dd6394321ded4250c867e64943219f59250c867e6394321d798e50c865e63943219f58e50c875d63943219758e50c87764194321dd50650c867f64543219f19150c867f63543219f18d50c87764154321dd50550c87795014321b798f54886dd63d52219f98f548875e63d52219798f548867d63d5221d758f548865d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548877661952219f982548867d6095221cfd91548867f63552219f18d548877661552219fd81548867c6055221cf550548873e64152219f98c548867d6315221db588548877661152219f980548867d6015221af99353886bd64d4e219f993538873e64d4e218f993538867d64d4e21cf593538863d64d4e21db58b538877661d4e219f983538867d60d4e21d7d4e538867e6494e219f592538867e6094e219f582538867f6454e219f191538875f6354e219fd81538867c6054e21d754c538867e6414e219f590538875e6314e21db58853887766114e219f980538867d6014e219fd97438867e65d0e219f597438867c65d0e21d79
  | 35 => 0xd5490c31bd986430c6f56190c319fd95430c6ef6250c31bb189430c67f6510c319f594430c73e5410c31cf550430c6ee6210c31bb588430c6f66110c31bd584430c6fa6010c31be580430c76f52948319f992520c67d64948319f982520c67d60948319fd91520c67c64548319fd81520c67c6054831af990520c6bd6414831db548520c6fa6014831be580520c67f65d08319f997420c67d65d0831cf953420c73d54d0831bd987420c6f561d08319fd96420c67e65908319f596420c76e5290831db54a420c67f65508319f595420c67c6550831cf951420c73d5450831b7d8d420c6dc6350831db949420c76d52508319fd94420c67e65108319f594420c6de6310831b758c420c6f66110831bd584420c6fa6010831be580420c76e52cc831db54b320c6f661cc831bd587320c67d658c8319fd95320c76e520c831db548320c7cd320c831bd984320c6f5610c8319f992510c67d64944319f597410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c7765190431ddd96410c6f56590431dd596410c6756590431bd592410c7775490431dd952410c7b65490431dd552410c7b55490431cd552410c7745490431f598e410c6f56390431f558e410c7765390431dd94a410c7755290431bd982410c67f6550431dd945410c6f76550431ddd95410c7b76450431ddd51410c7765450431dd551410c7745450431bdd8d410c7765350431dd949410c7755250431bd181410c67f65104319f994410c67d65104319f194410c73e5410431cf550410c6de6310431b758c410c6f66110431f5907310c7d541cc431b758e310c75e538c431bdd92310c6f5648c431ddd52310c775548c431bd58e310c776538c431f594e310c6f6608c4319fd95310c6df654c431d7d95310c65f654c431b7d85310c75e514c431bdd95310c777654c4319dd95310c6f7644c431bd591310c777544c431dd551310c6f7634c431f5d8d310c776534c431f594d310c7d7324c431f54c9310c6f4604c431ded42500c67e64940319f592500c67e62940319f58a500c7764194031dd506500c67f64540319f191500c67f62540319f189500c7764154031dd505500c75f3154031d74c5500c6be6414031af590500c6ee6214031bb588500c77950140319f98f54c867d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c867e63953219f58e54c877561953219f98254c867d6095321cfd9154c867f63553219f18d54c877561553219fd8154c867c6055321cf55054c86de6315321b758c54c86fa6015321be58054c873e64153219f98c54c875e63153219798c54c867d6315321d758c54c865d6315321db98854c877561153219f98054c877a60153219e98054c867d6015321de58054c86796015321be98353c86f960d4f219f99353
  | 36 => 0x5131bed81544c6f86055131cfd91544c67f6355131d7d8d544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd85544c67f6055131ded81544c67b60551319f181544c77860551319e181544c67e6515131cf550544c73e64151319f988544c67d6215131dd584544c67e60151319f580544c67e65d0d31cfd53434c73c54d0d31bd987434c6f561d0d319f996434c67c6550d31cfd51434c73c5450d31bbd89434c6ec6250d31bdd85434c6f46150d319f994434c79d4310d31bb988434c6ed6210d31bd984434c6fa6010d31be580434c67e64d49319f593524c67e60d49319f583524c76f5294931be982524c6f96094931db548524c67e64149319f590524c67e60149319f580524c67e65d09319f597424c67c65d0931dbd4b424c76c52d0931bd987424c6f561d09319f996424c67d65909319f196424c67f65509319f995424c67c6550931b7d8d424c6dc63509319f994424c67d65109319f194424c6de6310931b758c424c76f5210931db148424c6f66110931bd584424c6fa6010931be580424c67e65cc931dbd4a324c76c528c931bd986324c6f5618c931dbd49324c76c524c931bdd85324c6f4614c9319f994324c7cd320c9319f997414c73f54d0531cf153414c6de63d0531b758f414c67e6590531bd996414c7766590531bd592414c7775490531dd952414c7755490531dd152414c6f66390531ddd4a414c77452905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c7766550531bd195414c77465505319d195414c7b76450531ddd51414c7b75450531cdd51414c7765450531dd551414c7745450531ed151414c7d76350531bd18d414c7d46350531ddd49414c77452505319f994414c6f66110531bdd93314c6f564cc531ddd53314c77554cc531f5d46314c7d6418c531f5506314c6dd608c5319f993504c67d64d41319f98b504c67d62d4131dd907504c77541d4131bb98a504c6ed6294131ded42504c77950141319f990504c67d64141319f988504c67d6214131dd904504c7754114131ddcc4504c67e63d5031d798f540c67e62d50319f58b540c67e61d5031dd987540c67e60d50319f583540c67d6595031cfd52540c67e62950319f58a540c77661950319f982540c67d6095031cfd91540c67f62550319f189540c77661550319fd81540c67c6055031cf550540c6ee6215031bb588540c6fa6015031be580540c67e6415031cf990540c67e6315031d798c540c67e6215031db988540c66e62150319f588540c76d62150319b588540c67e6115031dd984540c67661150319f980540c77a60150319e980540c67d6015031de580540c67960150319f992530c67d6494c319f597430c6f561d0c319fd96430c67d6590c31cf952430c73
  | 37 => 0xcf95141cc73d5450731b7d8d41cc6dc6350731bdd9541cc7776550731edd9141cc7765450731ed95141cc7755450731ed55141cc7355450731dd15141cc6f76350731f5d8d41cc7d46350731dd94941cc7755250731bd18141cc6ee62d4331bb58b50cc6ee6294331bb58a50cc77b50943319f99250cc67d64943319f98a50cc76e62943319b98a50cc67d6294331db58a50cc66d6294331dd90650cc77541943319fd9150cc67c64543319fd8950cc67c6254331dd90550cc7754154331de54050cc6ee62d5231bb58b548c75d63d52319f98b548c76e62d52319b98b548c67d62d5231db58b548c66d62d5231dd987548c67e60d52319f583548c73f54952319f98a548c67d6295231dd986548c67e60952319f582548c73f64552319fd89548c67c6255231dd985548c67f60552319f181548c73d5415231cf990548c75d63152319f988548c67d6215231dd984548c67e60152319f580548c73e54d0e31cf553438c6f661d0e31bd587438c73e5450e31cf551438c6ef6250e31bb189438c6f76150e31bd185438c6ee6210e31bb588438c6f56110e31be980438c6f96010e31af993528c6bd64d4a31dbd4a528c67e6494a319f592528c67e6094a319f582528c67f6454a319f191528c67f6054a319f181528c76d5214a319fd97428c67e65d0a319f597428c76e52d0a31db54b428c6f661d0a31bd587428c67f6590a319f996428c67d6590a31cf952428c73d5490a319fd95428c67d6550a319f195428c6df6350a31b718d428c67f6510a319f994428c67d6510a31cf950428c73d5410a31b798c428c6dd6310a31db948428c76d5210a31bd984428c6f56110a31be980428c6f96010a31db94a328c76d528ca31bd986328c6f5618ca31db949328c76d524ca31bdd85328c6f4614ca31f34c8328c73e5490631cf552418c6de6390631b758e418c6f56590631dd596418c7765490631ed952418c7755490631ed552418c7355490631dd152418c6f66390631f598e418c7d56390631dd94a418c7755290631bdd95418c7776550631edd91418c7775450631dd951418c7755450631dd151418c6f46350631dd949418c7755250631cf950418c73d5410631b798c418c6dd6310631b7597318c75d65cc631bd597318c77565cc631bdd93318c6f564cc631ddd53318c77554cc631ded42508c67e64942319f592508c67e62942319f58a508c7764194231dd506508c77731942319fd91508c67c64542319fd89508c67c6254231dd905508c7754154231d7cc5508c6be6414231af590508c6ee6214231bb588508c77950142319f98b544c67d62d5131ddd87544c67e60d51319f583544c73f54951319f992544c67d6395131d758e544c67e62951319f58a544c67d6195131dd586544c67561951319f982544c67d6095131bbd89544c6ec625
  | 38 => 0x742106f561d08419f596421067f6550841b7d8d42106dc6350841b798c42106dd6310841db948421076d5210841bd98442106f56110841be98042106f960108419fd97321067e65cc8419f597321075e53cc841d754f321067f658c8419f996321067d658c841db94a321076d528c8419fd95321067d654c8419f195321075e534c841d754d321076e524c841db549321067f650c8419f994321067d650c841f34c832107766394441dd58e51107774394441dd90e51107754394441dd10e51107766294441dd58a51107774294441dd90a51107754294441dd10a51107773294441dd8ca51107753294441dd0ca51107766094441dd58251106bd6490441cf95241106f56490441dd95241107b65490441dd94e41107755390441dd94a411077552904419fd9541107765150441afd95411073f65504418fd9541106bf6150441cf94541107365150441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141107765350441dd54d41107765250441dd549411077b50940419f98e501067d63940419f98a501067d6294041dd906501077541940419fd8d501067c63540419fd89501067c6254041cfd0550107764154041cf50550107754154041b798c50106dd6314041bb98850106ed6214041de540501075e63d53319f98b54cc67d62d5331dd58754cc67e60d53319f58354cc73f54953319f98a54cc67d6295331dd58654cc67e60953319f58254cc73f64553319fd8954cc67c6255331dd58554cc67f60553319f18154cc73d5415331bb98854cc6ed6215331be98054cc6f96015331cf99054cc75e63153319f98854cc76e62153319b98854cc67d6215331db58854cc66d6215331dd58454cc67e6015331de98054cc67a60153319f58054cc77960153319e58054cc6f661d0f31cf95243cc73d5490f31bd98643cc6f56190f31bbd8943cc6ec6250f31cf95043cc73d5410f31e750c43cc6ee6210f31bb58843cc6f66110f31bd58443cc6fa6010f31be58043cc6fa60d4b31be58352cc76f5294b319f99252cc67d6494b319f98252cc67d6094b319fd9152cc67c6454b319fd8152cc67c6054b31db54852cc67f65d0b319f99742cc67d65d0b31bd98742cc6f561d0b319fd9642cc67e6590b319f59642cc76e5290b31db54a42cc67f6550b319f59542cc67c6550b31b7d8d42cc6dc6350b31db94942cc76d5250b319fd9442cc67e6510b319f59442cc6de6310b31b758c42cc6f66110b31bd58442cc6fa6010b31be58042cc76e52ccb31db54b32cc6f661ccb31bd58732cc76e520cb31db54832cc7cd320cb31bd98432cc6f5610cb31cf95341cc73d54d0731b798f41cc6dd63d0731bd59641cc7756590731ddd5241cc7765490731dd55241cc7745490731bd58e41cc7765290731dd54a41cc6f66090731
  | 39 => 0x7d66310941b598c42506f56310941f558c42506d56310941ed90c42507b44310941bd98842507b74210941f990842507b54210941f950842507a54210941bd98042507f26010941bc98042506f56010941fc58042506f16010941bdd9732506f665cc941bd59732506f465cc941bdd9332506f664cc941bd59332506f464cc941edd5332507d643cc941f550f32507e752cc941f914b32507e742cc941f910b32506f660cc941bd58332506f7658c941bd99632506f5658c941bd19632506f7648c941bd99232506f5648c941bd19232507b7548c941bd58e32507d7538c941f514e32507d7438c941f510e32506f6628c941f990a32507e5428c941f5cca32507e7328c941bd98232506f5608c941bdd9532506f6654c941bd59532506f4654c941bdd9132507b7644c941add9132506f6644c941bd59132506f4644c941ed19132506b4644c941edd5132507d6434c941f550d32507e6424c941f950932507e7324c941f58c932506f7604c941bd18132506f7650c941bd99432506f5650c941bd19432506f7640c941bd99032507b6640c941ad99032506f5640c941ed59032506b5640c941bd19032507b7540c941bd98c32507d7530c941f514c32507d7430c941f510c32506f6620c941f9d4832507e4520c941f9d0832507e4420c941f5cc832507e6320c941f54c832507e5320c941f14c832506f6600c941bd58032507b764d4141ddd5350507b754d4141bd98f50506f563d4141bd98b50506f562d4141ed59250507b75494141bd98e50506f56394141dd94e50507745394141bd98a50506f56294141dd94a50507745294141bd98250507775094141fcd4250507b76454141edd5150506f76354141f5d8d50506d76354141bd18d50507d46354141b518d50506f76254141f9d8950506e76254141bd18950507e46254141b918950507f35054141dd94150506f66514141ed59050507775414141edd5050506f66314141f598c50506d66314141bd58c50507d56314141b558c50507765314141dd14c50506f66214141f998850506e66214141bd58850507e56214141b958850507765214141dd14850507775014141fc94050507755014141fc54050507715014141d7d4e531067e6294c419f58a531067e6094c419f582531067f6254c419f189531067f6054c419f181531075d5314c41bb98853106ed6214c41be98053106f96014c41d794f431075d53d0c41bd98743106f561d0c419f596431067f6550c41bbd8943106ec6250c41d794c431075d5310c41bb98843106ed6210c41bd98443106f56110c41be98043106f96010c41dbd4a521067e63948419f58e521067e60948419f582521067f63548419f18d521067f60548419f18152106de6314841b758c521076d5214841be98052106f96014841db94b421076d52d0841bd98
  | 40 => 0x6214141de540505067e6314141d798c505065e63141419f58c505075d63141419758c505067e6214141db988505066e62141419f588505076d62141419b58850506f663d5141bd58f54506f662d5141bd58b54506f660d5141bd58354507b763d5141ed98f54507b563d5141ed18f54507b762d5141ed98b54507b562d5141ed18b54507b760d5141ed98354507b560d5141ad58354507b460d5141ddd5353507b754d4d41bd98b53506f562d4d41bd98353506f560d4d41ed59253507b75494d41bd98e53507775394d41f5d4e53506f66294d41bd58a53506f66094d41bd58253507b76454d41edd5153507d75354d41dd94d53506f76254d41f9d8953506e76254d41bd18953507e46254d41b918953506f76054d41fcd8153506f36054d41bd18153507f06054d41bc18153506f66514d41ddd5053507b75414d41ddd4c53507d65314d41dd54c53507d55314d41bd98853506f56214d41bd98053506f56014d41bd997435077665d0d419d99743507b754d0d41bd98b43506f562d0d41bd98343506f560d0d41bd59243507b75490d41bd98e43507d75390d41f514e43507b74390d41f5d0e43506f66290d41bd58a43506f66090d41bd58243507b75450d41f5d4d43507d45350d41f5d0d43507b64350d41bdd8943507e76250d41b9d8943506f46250d41f918943506e46250d41bdd8143506f46050d41bd99443507766510d419d99443506f66410d41edd5043506f66310d41edd0c43507d64310d41ed50c43507d54310d41e550c43506f66210d41f998843506e66210d41bd58843507e56210d41b958843506f66010d41fc98043506f26010d41bd58043507f16010d41bc580435077754d4941edd5352506f663d4941bd58f52506f660d4941bd58352507b56494941edd5252506f66394941bd58e52506f66294941ddd4a52507e75294941bd98252506f56094941edd9152507b75454941bdd8d52507d76354941b5d8d52506f46354941f518d52506d46354941f9d4952507765254941bdd8152507f36054941bcd8152506f46054941fc18152506f06054941bd99452507775414941edd5052506f66314941bd58c52507775214941f994852507755214941f954852506f66014941bd58052506f665d0941dd997425067665d0941edd5342506f663d0941bd58f42507b743d0941ed50f42506f660d0941bd58342506f56490941edd5242506f66390941bd58e42507b64390941ed10e42506f66290941f9d4a42507e45290941edd0a42507e74290941bd98242506f56090941edd5142506f76350941f5d8d42506d76350941bd18d42507d46350941b518d42507b74350941ed50d42507e75250941f914942507e74250941ed90942506f76050941bd18142506f66510941dd99442506766510941bd99042507b75410941bd98c425
  | 41 => 0xa41f594e32907d5538ca41f5d0e32907d4438ca41f990a32907e5428ca41f5cca32907e7328ca41bd98232906f5608ca41bdd9532906f6654ca41bd59532906f4654ca41bdd9132906f6644ca41bd59132906f4644ca41f590d32907d5434ca41f990932907e5424ca41f9cc932907d6324ca41bdd8132906f4604ca41bdd9432906f6650ca41bd59432906f4650ca41bdd9032906f6640ca41bd59032906f4640ca41f594c32907d5530ca41f5d0c32907d4430ca41f994832907e5520ca41f9d0832907e4420ca41f5cc832907e6320ca41f54c832907e5320ca41f14c832906f6600ca41bd58032907b564d4241bd98f50906f563d4241bd98b50906f562d4241bd98e50906f56394241dd94e50907745394241bd98a50906f56294241dd94a50907745294241ddd4250907f35094241bdd8d50906f46354241bdd8950906f46254241fcd4150907765054241ed59050906f66314241f598c50906d66314241bd58c50907d56314241b558c50907765314241dd14c50906f66214241f998850906e66214241bd58850907e56214241b958850907765214241dd14850907775014241fc94050907755014241fc540509077150142419f98b535067d62d4d41dd587535067e60d4d419f583535075f5394d41bbd8953506ec6254d41bed8153506f86054d41d754c535067e6214d419f58853507756114d419f980535067d6014d419f99743506f661d0d41d7d4e435075c5390d41bd98643506f56190d41d7d4d435075c5350d41bbd8943506ec6250d41bdd8543506f46150d419f994435079d4310d41bb98843506ed6210d41bd98443506fa6010d41be580435067e63d49419f58f525077561d49419f983525067d60d4941dbd4a52506df6354941b718d52506fb6054941be181525076d52149419f98c525067d6314941dd584525067e60149419f580525067e65d0941bd987425076f5290941db14a42506f66190941bd58642506df6350941b718d425076f5250941db14942506f76150941bd185425067e6510941b798c42506dd6310941eb50842506f66110941be98042506f960109419f997325067d65cc9419f197325076f52cc941db14b32506f661cc941bd587325067e658c9419f596325067c658c941d7d4e325075c538c941bd98632506f5618c9419fd95325067e654c9419f19532506bf644c941af19132506f7614c941bd185325067e650c9419f594325067c650c941af99032506bd640c941d7d4c325075c530c941dbd48325076c520c941f34c832506f6610c941bd58432506f663d0541bd58f41506f662d0541bd58b41506f660d0541bd58341507b75190541af582415067e63d41419f58f505067e62d41419f58b505077b5094141b7d8d50506dc6354141bbd8950506ec6254141b798c50506dd6314141bb98850506ed
  | 42 => 0x794e329075d538ca41bd98632906f5618ca419fd95329067d654ca419f19532906f7614ca41bd185329067f650ca419f994329067d650ca41d794c329075d530ca41db948329076d520ca41f34c832906f6610ca41bd58432906bd65d0641cf59741906f565d0641dd59741906f663d0641bd58f41906f662d0641bd58b41906f660d0641bd583419077b50942419f98e509067d63942419f98a509067d62942419fd8d509067c63542419fd89509067c6254241cfd0550906de6314241b758c50906ee6214241bb58850907795014241ed59353906f662d4e41f998b53906e662d4e41bd58b53907e562d4e41b958b53906f660d4e41bd58353907775394e41f5d4e53906f66294e41bd58a53906f66094e41bd58253907d75354e41dd94d53906f76254e41bd18953906f76054e41bd18153907b56414e41ddd4c53907d65314e41dd54c53907d55314e41bd98853906f56214e41bd98053906f56014e41bd597439077565d0e41bd98b43906f562d0e41bd98343906f560d0e41f594e43907d55390e41edd0e43907d74390e41bd98a43906f56290e41bd98243906f56090e41f594d43907d55350e41f5d0d43907b64350e41bdd8943907e76250e41b9d8943906f46250e41f918943906e46250e41bdd8143906f46050e41bd59443907756510e41edd0c43907d64310e41ed50c43907d54310e41bd98843907e66210e41b998843906f56210e41f958843906e56210e41bd98043907f26010e41bc98043906f56010e41fc58043906f16010e41ed59352906f663d4a41f598f52906d663d4a41bd58f52907d563d4a41b558f52906f660d4a41bd58352906f66394a41bd58e52907775294a41f9d4a52906f66094a41bd58252906f76354a41bd18d52907e75254a41dd94952906f76054a41bd18152907b56414a41bd98c52906f56314a41ddd4852907e65214a41dd54852907e55214a41bd98052906f56014a41bd597429077565d0a41bd98f42906f563d0a41bd98342906f560d0a41bd98e42906f56390a41f994a42907e55290a41edd0a42907e74290a41bd98242906f56090a41bdd8d42907d76350a41b5d8d42906f46350a41f518d42906d46350a41f994942907e55250a41f9d0942907b64250a41bdd8142906f46050a41bd59442907756510a41bd98c42907d66310a41b598c42906f56310a41f558c42906d56310a41edd0842907e64210a41ed50842907e54210a41bd98042907f26010a41bc98042906f56010a41fc58042906f16010a41bdd9732906f665cca41bd59732906f465cca41bdd9332906f664cca41bd59332906f464cca41f590f32907d543cca41f994b32907e552cca41f9d0b32907e442cca41bd98332906f560cca41bdd9632906f6658ca41bd59632906f4658ca41bdd9232906f6648ca41bd59232906f4648c
  | 43 => 0x320cbcc614c832f3d81320cacf604c832f3981320cbcd604c832f3181320cbcd32d4432f34ca510cb7751944329f992510ca7d64944329f982510ca7d6094432f34c9510ca7f64544329f191510ca7f60544329f181510cabe6414432af590510cbcd3214432dd544510cafa6014432be580510cbcd32d4032f34ca500cb7b50940329f992500ca7d64940329f986500ca7d6194032f34c9500caf76154032bd185500ca7f64540329f191500ca7f6154032ddd85500ca7761540329f185500cb7461540329d185500cabe6414032af590500cbcd3214032bd984500caf56114032de540500cb5f5394f419f98a53d067d6294f419f98253d067d6094f419fd8953d067c6254f419fd8153d067c6054f41d754c53d06ee6214f41bb58853d06fa6014f41be58053d075e53d0f41d754f43d06f661d0f41bd58743d06ef6250f41bb18943d075e5310f41d754c43d079d4310f41bb98843d06ed6210f41bd98443d06f56110f41be98043d06f96010f41dbd4a52d067e6394b419f58e52d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d06de6314b41b758c52d076d5214b41be98052d06f96014b41db94b42d076d52d0b41bd98742d06f561d0b41b7d8d42d06dc6350b41b798c42d06dd6310b41db94842d076d5210b41eb50842d06f66110b41bd58442d06fa6010b41be58042d067f65ccb419f99732d067d65ccb41d794f32d075d53ccb419fd9632d067e658cb419f59632d076e528cb41db54a32d067f654cb419f59532d067c654cb41afd9132d06bc644cb41d794d32d075d534cb41db94932d076d524cb419fd9432d067e650cb419f59432d06be640cb41af59032d07cd320cb41ded4250d067e63943419f58e50d067e62943419f58a50d067f63543419f18d50d067f62543419f18950d06de6314341b758c50d06ee6214341bb58850d07795014341bb98b53906ed62d4e41d7d4e539067e6294e419f58a53907766194e419f982539067d6094e419fd89539067c6254e41dd185539067f6054e419f181539075d5314e41bd587439075e5390e41d754e43906f66190e41bd586439075e5350e41d754d43906ef6250e41bb18943906f76150e41bd18543906ee6210e41bb58843906f56110e41be98043906f96010e41b798f52906dd63d4a41dbd4a529067e6394a419f58e52907766194a419f982529067d6094a419fd8d529067c6354a41dd185529067f6054a419f181529076d5214a41bd587429076e5290a41db54a42906f66190a41bd58642906df6350a41b718d429076e5250a41db54942906f76150a41bd18542906de6310a41b758c42906f56110a41be98042906f96010a419fd97329067e65cca419f597329076e52cca41db54b32906f661cca41bd587329067f658ca419f996329067d658ca41d
  | 44 => 0xb3d5415032bd984540caf56115032be980540caf960150329f990540cb3e64150329f98c540cb5e63150329798c540ca7e6215032db988540ca6e62150329f984540cb7661150329d984540ca7d6115032dd584540ca7561150329f980540cb7a60150329e980540ca7d6015032de580540ca7960150329f992530ca7d6494c329f597430caf661d0c32bd587430cadd65d0c32d7597430ca5d65d0c32d7d53430cb5d54d0c32f3d8b430cadd62d0c32f318b430cbd661d0c32f5587430cadd60d0c329fd96430ca7d6590c32cf952430cb3d5490c32b798e430cb5e5390c32bb98a430caed6290c329fd95430cb5e5350c32bbd89430ca7f6510c329f594430cb3e5410c32cf550430caee6210c32bb588430caf66110c32bd584430cafa6010c32be580430cb5d6510c3297594430cade6410c32e7990430cb5f5410c32e7950430cb5d5410c32e7550430cbce6210c32b7588430cbcd6210c32b3588430cbd66110c32f5584430cbda6010c32b7580430cbd96010c32b6580430ca7e64948329f592520cb5f4394832d710e520ca7d65d0832bd987420caf561d0832bb597420cb6d65d08329b597420cb6f54d0832db553420cbcf63d0832bb58f420cbcc63d0832db94f420cbcf43d0832f310f420cbe661d0832f9587420caed60d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd6390832bb98a420cb6e52908329fd95420cadf6350832b718d420cb6e52508329fd94420ca7e65108329f594420ca7c6510832cf950420cb3d5410832b798c420cadd6310832bd984420caf56110832be980420caf96010832bb594420cb6d65108329b594420caee6410832eb990420cb6f5410832eb950420cb6d5410832eb550420cbce6310832bb58c420cbcd6310832b358c420cb6e5310832f3d0c420cbcc4310832f9984420cbe56110832fa980420caed6010832fa580420cae96010832b7993320cadc64cc832d7d53320cb5d54cc832f3d0b320cbcc42cc832b7583320cadd638c832d794e320caee648c832bb192320cb6f548c832db552320caed638c832b358e320cb6e538c832f394e320cbcf438c832f310e320caed608c8329fd95320cadf654c832d7d95320ca5f654c832b7991320cadc644c832d7d51320cb5d544c832b7d89320cb5e524c832f3d09320cbce424c832f3509320cbcc424c832b7d81320caef654c832dbd95320ca6f654c832bb991320caec644c832dbd51320cb6d544c832bbd8d320cbcf634c832db94d320cbce534c832f3d0d320cbce434c832f350d320cbcc434c832bbd81320cbcf654c832b3d95320cb4f654c832f3d91320cbce644c832b3991320cbcd644c832f3191320cacc644c832f3d51320cb4f544c832f3951320cbcd544c832d3551320cbcc544c832f3d85320cbce614c832f3585
  | 45 => 0x2542329fd85508ca7c6154232de540508ca7e61d51329f587544ca7e60d51329f583544cb3f5495132bd986544caf561951329f992544ca7d6395132d758e544ca7d6295132db58a544ca7e6195132dd986544ca7661951329f586544cb7561951329d586544ca7e60951329f582544cb3f64551329fd8d544cb5f635513297d8d544ca7f6255132dbd89544ca6f62551329fd85544ca7c61551329fd81544ca7c60551329f994544cb3d5415132bd984544caf56115132be980544caf96015132cf990544cb5d6315132db588544ca7e6115132dd984544ca7661151329f584544cb7561151329d584544ca7e6015132de980544ca7a60151329f580544cb7960151329e580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d32bd987434caf561d0d329f996434cade6590d32d7996434ca5e6590d32b7592434cb5e5490d32d7152434cbcf6290d32b798a434cbcc6290d329f195434cb3f5450d32cf151434caef6250d32bb189434cb5c6550d3297195434cb9f6450d32e7d51434cb5e5450d32d7151434cb9c5450d32f3d89434cadc6250d32f3189434cacc6250d329f994434cade6310d32bb988434caf66110d32bd584434cafa6010d32be580434ca7e65d0932cfd53424cb3c54d0932b798f424cadd63d0932bd987424caf561d09329f996424caee6590932db996424ca6e6590932bb592424cb6e5490932db152424cbcf6390932bb98e424cbcc6390932f390e424cbcd43909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424caec6550932db195424ca6c6550932ebd91424cbaf5450932db951424cb6c5450932eb151424cbcf6350932bb18d424cbcc6350932b318d424cbce4350932f350d424ca7e6510932b798c424cadd6310932bb988424caf66110932bd584424cafa6010932be580424caef64cc932bb593324cb6e54cc932db153324cbce43cc932f350f324cadf648c932b7592324cb5e548c932d7152324cbcf528c932f390a324cbcd428c9329f993514ca7d64d45329f983514ca7d60d4532af992514cabd6494532ddd46514cb7551145329f990514ca7d64145329f980514ca7d60145329f993504ca7d64d4132d790f504cb5d43d4132db90b504cb6d42d4132dbccb504cb5e32d41329f987504ca7d61d4132ded42504cabf6454132af191504caf76154132bd185504cb7950141329f990504ca7d64141329f984504ca7d61141329f98f540cb5e63d50329f98b540cb6e62d50329f987540ca7d61d50329f983540ca7d60d50329f596540cb3f5495032bd986540caf561950329f986540cb7661950329d986540ca7d6195032dd586540ca7561950329f982540ca7d6095032cfd91540cb5c6355032db189540ca7f61550329f185540ca7f60550329f181540c
  | 46 => 0x32f998742ccbe561d0b32bb58342ccb3e5450b32cf55142ccadf6350b32b718d42ccade6310b32b758c42ccaf66110b32bd58442ccafa6010b32be58042ccaed6510b32db59442ccbae6410b32dbd5042ccb6d5410b32f398c42ccaed6310b32f358c42ccacd6310b32f390c42ccbcd4310b32f998442ccbe56110b32fa98042ccaed6010b32fa58042ccae96010b32be98351ccaf960d4732ddd4651cca7e64947329f59251cca7e60947329f58251cca7f64547329f19151cca7f60547329f18151ccb755114732bd98750ccaf561d4332ded4250cca7e64943329f59250cca7e61943329f58650cca7f64543329f19150ccb5e4354332d750d50cca7f61543329f18550ccb795014332d758f548cb6e62d52329f987548ca7d61d52329f983548ca7d60d5232cfd52548caf66195232bd586548cb6e62952329f986548cb7661952329d986548ca7d6195232dd586548ca7561952329f982548ca7d6095232cfd91548cb5f63552329fd85548ca7c61552329fd81548ca7c6055232cf550548caf66115232bd584548cafa6015232be580548cb3e6415232d758c548cb6e62152329f984548cb7661152329d984548ca7d6115232dd584548ca7561152329f980548cb7a60152329e980548ca7d6015232de580548ca796015232cf953438cb3d54d0e32bb98b438caed62d0e32bd987438caf561d0e32d7597438cb5f54d0e32e7953438cb5d54d0e32e7553438cbce62d0e32b758b438cbcd62d0e32f5987438cbd561d0e32b7583438cb3e5450e32cf551438caef6250e32bb189438caed6210e32bd984438caf56110e32be980438caf96010e32b7594438cb5d6510e32e7990438cb5f5410e32d7550438cbce6210e32b7588438cbcd6210e32b3588438cbd66110e32f5584438cbda6010e32b7580438cbd96010e32b6580438caf661d0a32bd587428cb3e5490a32cf552428cade6390a32b758e428caed6590a32db596428cb6e5490a32eb952428cbad5490a32db152428caee6390a32f398e428cbcd6390a32f3d0e428cbcc4390a32b7d8d428cadc6350a32bbd95428cb6f6550a32ebd91428cb6e5450a32db151428cbcf6350a32bb18d428cbcc6350a32b318d428cbcf4350a32f310d428cb3e5410a32cf550428cade6310a32b758c428caf66110a32bd584428cafa6010a32be580428cadd65cca32d7597328cade64cca32b7193328cb5f54cca32d7553328cadd60cca32bb597328cb6d65cca32bbd93328caed64cca32db953328cb6c54cca32be983518caf960d4632ddd46518ca7e64946329f592518ca7e60946329f582518ca7f64546329f191518ca7f60546329f181518cb755114632bd987508caf561d4232ded42508ca7e64942329f592508ca7e61942329f586508ca7f64542329f191508cb6e4254232db509508cb6f3
  | 47 => 0x98c5110add6314442d794c5110b5d5314442bd9845110b755114442be9805110af96014442b798f5010add63d4042d794f5010b5d53d4042bd9875010af561d4042dd9475010b7551d4042d794e5010b5d5394042dd9465010b755194042ded425010a7e63940429f58e5010a7e61940429f5865010b7b5394042de94e5010bda5394042d694e5010b795394042f654e5010b595394042de14e5010bbb4294042fa90a5010bb94294042fa50a5010b7b5194042de9465010bf25194042dc9465010b795194042fc5465010b715194042de1465010b786494042ded8e5010b7a6394042de58e5010b786394042ded0e5010b7a4394042de50e5010b784394042de18a5010b7b4294042de90a5010b794294042ded865010b7a6194042de5865010b786194042d794d5010b5d5354042dd9455010b7551540429fd8d5010a7c6354042db9095010b6d42540429fd855010a7c6154042ded955010b7b5354042de94d5010bda5354042d694d5010b795354042f654d5010b595354042de14d5010bbb4254042fa9095010bb94254042fa5095010b7b5154042de9455010bf25154042dc9455010b795154042fc5455010b715154042de1455010b7a6454042ded8d5010b7a6354042de58d5010b786354042ded0d5010b7a4354042de50d5010b784354042de9895010b7b4254042de9095010b6a4254042de5095010b694254042de1095010b7b6154042de9855010b796154042de1855010ade6314042b758c5010b5e5314042d754c5010af66114042bd5845010b765114042dd5445010afa6014042de5405010b5e63d5332db58b54cca7e61d53329f58754cca7e60d53329f58354ccb3f5495332bd98654ccaf56195332d798e54cca7e6195332dd98654cca7661953329f58654ccb7561953329d58654cca7e60953329f58254ccb3f6455332dbd8954cca7f61553329f18554cca7f60553329f18154ccb3d5415332bd98454ccaf56115332be98054ccaf96015332cf99054ccb5e6315332db58854cca7e6115332dd98454cca7661153329f58454ccb7561153329d58454cca7e6015332de98054cca7a60153329f58054ccb7960153329e58054ccaf661d0f32bd58743ccb3e5490f32cf55243ccaee6290f32bb58a43ccb5d6590f32d795243ccb9e5490f32e755243ccb5c5490f32b798a43ccbce6290f32f358a43ccaec6250f32b7d9543ccb5f6550f32e7d9143ccb5e5450f32d715143ccbcf6250f32b718943ccbcc6250f32b318943ccb3e5410f32cf55043ccaee6210f32bb58843ccaf66110f32bd58443ccafa6010f32be58043ccb3e54d0b32cf55342ccade63d0b32b758f42ccaf661d0b32bd58742ccaed65d0b32db59742ccb6f54d0b32eb95342ccb6d54d0b32eb55342ccbce63d0b32bb58f42ccbcd63d0b32f390f42ccbcd43d0b
  | 48 => 0x50a7d61d4142b798e5050add6394142d7d4e5050b5c5394142ded425050adf6354142b718d5050b5f5354142d714d5050af76154142bd1855050b5f5314142d714c5050b7950141429f98c5050a7d63141429f9845050a7d6114142dd9865410b756195042bd9875310af561d4c42be9835310af960d4c42d7d4e5310a7e6194c429f5865310a7e6094c429f5825310bcc6294c42d71925310b5e6294c42d718a5310b5f6194c42d79865310b5d6194c42d71865310b5f6094c42d79825310b5d6094c42d71825310b6c6254c429fd855310a7c6154c429fd815310a7c6054c42d7d955310bcc6254c42d79915310b5e6254c42d71895310b4c6254c42d71095310b5f6154c42d79855310b5d6154c42d71855310b5f6054c42d79815310b5d6054c42d71815310ade6314c42d754c5310af66114c42bd5845310afa6014c42be5805310b5e53d0c42d754f4310aee62d0c42bb58b4310af661d0c42bd5874310a7d6590c42d754e4310a7f6550c42d794d4310aef6250c42d794c4310b5d5310c42bb9884310aed6210c42bd9844310af56110c42be9804310af96010c42d794f4210b5d53d0842bd9874210af561d0842e794f4210b9d53d0842ed9874210bb561d0842af5924210b3e5490842d794e4210b5d5390842bb5924210b6e5490842eb9524210aee6390842f394e4210b6d5390842f354e4210b4d53908429fd954210adf6350842b718d4210b5e5350842d754d4210abf6550842cfd954210a3f6550842e7d8d4210b9c6350842e794d4210b9d5350842afd894210b3e5250842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210bcf6350842bb18d4210bcc6350842b318d4210bce5350842db54d4210bcd5350842d354d4210ade63d4442b758f5110b5e53d4442d754f5110afa60d4442be5835110b5e5394442d754e5110b7751944429f98e5110a7d63944429f9825110a7d6094442ddd4e5110b765394442f594e5110b565394442dd54e5110bd55394442d554e5110b745394442edd0a5110be64294442ed50a5110be54294442dd1925110b776394442dd98e5110b756394442dd18e5110b774394442dd90e5110b754394442dd10e5110b746294442ddd0a5110b764294442dd50a5110b776094442dd9825110b756094442dd1825110b5e5354442d754d5110a7f63544429f18d5110a7f60544429f1815110b776554442ddd4d5110b765354442f594d5110b565354442dd54d5110bd55354442d554d5110b745354442edd095110be64254442ed5095110be54254442dd9915110b776354442dd98d5110b756354442dd18d5110b774354442dd90d5110b754354442dd10d5110b766254442ddd095110b764254442dd5095110b744254442ddd815110b766054442dd5815110b746054442b7
  | 49 => 0x755354742dd14d51d0b766454742ddd8d51d0b766354742dd58d51d0b746354742ddd0d51d0b764354742dd50d51d0b744354742dd58951d0b776054742dd98151d0b756054742dd18151d0b755114742bd98750d0af561d4342dd94750d0b7551d4342dd94650d0b755194342ded4250d0a7e63943429f58e50d0a7e61943429f58650d0b765154342dd54550d0a7f63543429f18d50d0a7f61543429f18550d0ade6314342b758c50d0af66114342bd58450d0b765114342dd54450d0b795014342d7d4e5390b6e6294e429f9865390a7d6194e429f9825390a7d6094e429fd855390a7c6154e429fd815390a7c6054e42d754c5390af661d0e42bd5874390b5e5390e42d754e4390aee6290e42bb58a4390b5e5350e42d754d4390aef6250e42bb1894390aed6210e42bd9844390af56110e42be9804390af96010e42bd9874290af561d0a42af5974290b3d65d0a42ed9874290bb561d0a42bb5974290b6d65d0a42bb58f4290b6e53d0a42f99874290be561d0a42bb5834290b7751946429f98e5190a7d63946429f9825190a7d60946429fd8d5190a7c63546429fd815190a7c6054642dd5445190ade6394242b758e5090b7b50942429f98e5090b5e63942429798e5090a7d6394242d758e5090a5d63942429f9865090a7d6194242bdd855090af461542429fd8d5090a7c63542429fd855090b7761542429dd855090a7c6154242dd1855090a746154242de5405090a7e61d4d429f5875350a7e60d4d429f5835350bcf62d4d42d7d935350b5f62d4d42d758b5350b5f61d4d42d79875350b5d61d4d42d71875350b5f60d4d42d79835350b5d60d4d42d71835350b5f5394d42d754c5350b6d6214d429f9845350a7d6114d429f9805350a7d6014d42b79945350b5e6514d42f35885350b5f6414d42d7d885350b5d6214d42d35885350b5d4214d42d7d845350b5e6114d42d75845350b5c6114d42d7d805350b5e6014d42d75805350b5c6014d429f9974350b5c53d0d42bd9874350af561d0d42d7d4e4350b5c5390d42bb98a4350aed6290d42d7d4d4350b5c5350d42bbd894350aec6250d429f9944350b5f5310d42bb9884350af66110d42bd5844350afa6010d42be5804350b5f53d0942d714f4250af661d0942bd5874250aed63d0942f3d4f4250b6c53d0942f314f4250b4c53d0942f99874250be561d0942bb5834250b5f5390942d714e4250b9f5390942e714e4250baf5290942d7d4f5150b5c53d45429f98f5150a7d63d45429f9835150a7d60d4542b798e5150add6394542d7d4e5150b5c5394542ddd465150adf6354542b718d5150b5f5354542d714d5150afb6054542be1815150b5f5314542d714c5150b7551145429f98c5150a7d63145429f9805150a7d6014542d7d4f5050b5c53d41429f98f5050a7d63d41429f9875
  | 50 => 0x94443dd18a5110f776094443dd9825110f756094443dd1825110f6e5254443db5495110e7f62544439f1895110e7f60544439f1815110f776554443edd0d5110fd64354443ed50d5110fd54354443ddd495110f765254443f99495110f665254443dd5495110fe55254443d95495110f745254443dd9915110f766354443ddd0d5110f764354443dd50d5110f744354443ddd895110f766254443dd5895110f746254443ddd815110f766054443dd5815110f746054443bb9885110eed6214443db9485110f6d5214443bd9845110f755114443be9805110ef96014443bb98b5010eed62d4043db94b5010f6d52d4043bd9875010ef561d4043dd9475010f7551d4043db94a5010f6d5294043dd9465010f755194043ded425010e7e62940439f58a5010e7e61940439f5865010fbb4394043f690e5010fb94394043f650e5010f7b5294043de94a5010fea5294043da94a5010f795294043fa54a5010f695294043de14a5010f7b5194043de9465010ff25194043dc9465010f795194043fc5465010f715194043de1465010f786494043de18e5010f7b4394043de90e5010f794394043ded8a5010f7a6294043de58a5010f786294043ded865010f7a6194043de5865010f786194043db9495010f6d5254043dd9455010f755154043d790d5010f5d43540439fd895010e7c62540439fd855010e7c6154043ded955010fbb4354043f690d5010fb94354043f650d5010f7b5254043de9495010fea5254043da9495010f795254043fa5495010f695254043de1495010f7b5154043de9455010ff25154043dc9455010f795154043fc5455010f715154043de1455010f7a6454043de98d5010f7b4354043de90d5010f5a4354043de50d5010f594354043de10d5010f7b6254043de9895010f796254043de1895010f7b6154043de9855010f796154043de1855010eee6214043bb5885010f6e5214043db5485010ef66114043bd5845010f765114043dd5445010efa6014043de5405010ef661d4f42bd58753d0b5f5394f429f98653d0a7d6194f429f98253d0a7d6094f42dbd8953d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42bd98453d0af56114f42be98053d0af96014f42d794f43d0b5d53d0f42bb98b43d0aed62d0f42bd98743d0af561d0f42bb18943d0b5e5310f42d754c43d0aee6210f42bb58843d0af66110f42bd58443d0afa6010f42be58043d0b7751947429f98e51d0a7d63947429f98251d0a7d6094742ddd4e51d0b765394742dd54e51d0b745394742dd19251d0b776394742dd98e51d0b756394742dd18e51d0b774394742dd90e51d0b754394742dd10e51d0b776294742ddd8251d0b766094742dd58251d0b7460947429fd8d51d0a7c63547429fd8151d0a7c6054742ddd9551d0b775354742dd94d51d0b
  | 51 => 0x3f3d8f5250fcf43d4943eb90f5250f6f64d4943dbd8f5250f6f43d4943db90f5250f6f61d4943db9875250f6d61d4943db1875250f6f60d4943db9835250f6d60d4943db1835250f6f5294943db5485250f5f43149439f9845250e7d61149439f9805250e7d6014943bb9945250f6e6514943f358c5250fcf4314943eb90c5250f6f6414943dbd8c5250f6f4314943d3d0c5250f6e4314943db50c5250f6f6114943db9845250f6d6114943db1845250f6f6014943db9805250f6d6014943db1805250f6f52d4543db14b5150e7e62d45439f58b5150e7e60d45439f5835150eee6294543bb58a5150f6f5294543db14a5150f775194543bbd895150eec6254543dbd495150f6c5254543bed815150ef86054543dbd485150f6c5214543dd5445150e7e62145439f5885150e7e60145439f5805150f6f52d4143db14b5050e7e62d41439f58b5050e7e61d41439f5875050eee6294143bb58a5050f6f5294143db14a5050f7b5094143bbd895050eec6254143dbd495050f6c5254143bdd855050ef46154143dbd485050f6c5214143de5405050e7e62141439f5885050e7e61141439f5845050f766195043dd5865410ef661d0c43bd5874310fb661d0c43ed5874310ebd6490c43cf9524310edd6490c43d79524310f9e5490c43b798a4310e7f6550c43bbd894310eec6250c43afd954310f3f6550c438fd954310ebf6350c43cf94d4310faf6250c43eb1894310edf6550c43d7d954310e5f6550c43b7d914310f9f6450c43d79514310f9e5450c43f3d894310edc6250c43f31894310ecc6250c43bd9875210ef561d4843be9835210ef960d4843dbd4a5210e7e61948439f5865210e7e60948439f5825210fcc6394843ebd0e5210fce4394843eb50e5210fcd4394843db1925210f6c6394843dbd0e5210f6e4394843db50e5210f6f6194843db9865210f6d6194843db1865210f6f6094843db9825210f6d6094843db1825210f5e4354843d750d5210e7f61548439f1855210e7f60548439f1815210f6f6554843f318d5210faf4354843f390d5210fad4354843f350d5210f6e6454843db98d5210f6f4354843db90d5210f4e4354843db50d5210f4d4354843db10d5210f6f6154843db9855210f6d6154843db1855210f6f6054843db9815210f6d6054843db1815210eee6214843db5485210ef66114843bd5845210efa6014843be5805210eee62d4443bb58b5110f6e52d4443db54b5110efa60d4443be5835110f6e5294443db54a5110f7751944439f98a5110e7d62944439f9825110e7d6094443edd0e5110fd64394443ed50e5110fd54394443ddd4a5110f765294443f994a5110f665294443dd54a5110fe55294443d954a5110f745294443dd1925110f746394443ddd0e5110f764394443dd50e5110f776294443dd98a5110f7562
  | 52 => 0x8000000000000000001000400580000008000000000000002001200580008000000000000028000000000200008000000c000c0010002001a0004000800000040000001800a00060000005800000000024000800100040008001000a0000000c0008001000000000000000000000080000007000000000018005000200080018003000000080008001000000000000002000c00000040000000800080000006000000180000001000000000010005000000000010006000000200000002000000000038006000400100000007000000000048000000000040000003000000000030000000200040038000000800000000002000000040008000000800080008002000000000010002000200000000000000200000008004000200080000001000000040010000000600000000003000a000c00000010000000c000800200040000000000500020000002800200080002f661d4b43bd58752d0f6f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0ef66114b43bd58452d0efa6014b43be58052d0f7751947439f98a51d0e7d62947439f98251d0e7d6094743ddd4a51d0f765294743dd54a51d0f745294743dd19251d0f776394743ddd8a51d0f766294743dd58a51d0f746294743ddd8251d0f766094743dd58251d0f7460947439fd8951d0e7c62547439fd8151d0e7c6054743ddd9551d0f775254743dd94951d0f755254743dd14951d0f766454743dd58d51d0f776254743dd98951d0f756254743dd18951d0f776054743dd98151d0f756054743dd18151d0f755114743bd98750d0ef561d4343dd94750d0f7551d4343dd94650d0f755194343ded4250d0e7e62943439f58a50d0e7e61943439f58650d0f765154343dd54550d0e7f62543439f18950d0e7f61543439f18550d0eee6214343bb58850d0ef66114343bd58450d0f765114343dd54450d0f795014343bd9874390ef561d0e43af5974390f3d65d0e43ed9874390fb561d0e43b75974390f5d65d0e43b758b4390fd661d0e43f55874390edd60d0e43dbd4a5290f5f4394a439f9865290e7d6194a439f9825290e7d6094a439fd855290e7c6154a439fd815290e7c6054a43db5485290f7751946439f98a5190e7d62946439f9825190e7d60946439fd895190e7c62546439fd815190e7c6054643dd5445190eee6294243bb58a5090f7b50942439f98a5090f6e62942439b98a5090e7d6294243db58a5090e6d62942439f9865090e7d6194243bdd855090ef461542439fd895090e7c62542439fd855090f7761542439dd855090e7c6154243dd1855090e746154243de5405090ef661d0d43bd5874350edd62d0d43f59874350fd561d0d43b75834350f9f5390d439f9875250e7d61d49439f9835250e7d60d494
  | 53 => 0x2000800080000000000000080150002000c00500090002000c0010002000c00000000008000000000010000000600080000000000000000000007000a000400000030004000c00a8003000e00040000001000000000010000000000100038005000400000000000000000000030000000200180000008000200080000000000200140038000000000080000006000a00240050014000000000010003000000040008002000000180000000000e000000080070006000c0010009000a00000010001000000000008002000000440018000000200000000009000000140000004000200000038003000c000000000000008000800000000008001400000030002000400080000000000400100030002000000f80010002000000000010006001c0000002000600000010002000200040000001000600000010000000e00000000007000e00000018002000200200000002000000040000000000000140008002000200000018002000000040068000000200040020000000000000000000000c0008001800100020008000000000080004001000100100000002800500000000004800100020000002800200000004001000300000008000000200080000001800b000000000000007000800000030000000000040000000000000000000000001000000000000000200000000000000000140008000000200180008001000400040000000000000000000000000000240008001000000180000000000200000020003000c00040000001000000000008008000000100008000000200100000000000000000010001000000000010001000000000010007000000040008002000400040030001000600000000000000c0000000800a000000140008001000000000010000000e000c0000005001000000010002000400000008000000600000008000001200000010002000200000000000000600080000001000a001c00000000002000800380010000000000000030000000400000010008000400180030008000c002000b000600000000001000200040010000000200140000001000e000000000010008000c0000002001600000068001000000000000007000200000000015000000080000002000000040030000000000040000002001000000000003000a001c000000d000000040020000000800080020003000200040008000000600180010000000200100010000000c000000180010000000c0008002000a000000000030002000400180020002001800000020000000000000000012001800300000002000c00000020000003400000020006000800000090004000000000050000000000100020000000400080000004000400180010002000000400050000000c0000000000000000018000000000180008000000a0000002000200060004000
  | 54 => 0x40000000a000000180050000000000000000002003400080000000000800000020004002c0000000000400040018000000000000000007000200140008000000c001800000000002003c001800000020018000000100040000000000000000000006800000000000000000100140018002000100040000000000000020010000800200040000001000000000008003000f00100008001000000000004000000500000000003800200020000005000100000010000800300000000000000000000004001000000080000000000300360004002000b0004001000280000002000000000010000000000000030000000400180010000000000480000002000800180010014001400100000000000c0000002000200000040000000a00040008000000000080018001000000240008000000a000400100010006000c0000001000a002800380000000000000000000002000800100010000000400380000006001800000050000000400280010002000400000030000001000080000006000000180020004002c0010001000000000000008000400000000000000000000000000000400000000000000200000000001000000080028000000000000000000000600040050006000000000000001000a0004001800200020000001000100000004000000e000c000800080000002001c00280030002000000000040010000000080010002000400900000012001400700000002000000800030000000800000030006000c00000000004001800080000008000000000000000000c00080000006000000000020006000c00000000002000c00080010000000000000000000000400280010002000c00000010000000000300020000000400000030002000c000000000000008006800100000018001800000000000000000200040000000000500000014003000000020000002000200000014001001000000004000800500020008003000000000004002000100020010000000600040000000800000000008000000400020000000000a0000000000100000004000000000010008000000080000000000400000040008001000080010000000000080000018000400200060000000000000020002000000200040006000800080000000000000180020002000400380000018000000100020000002400000000004004c00080000000000000000050002001000280040000000000480010000000000080010006000000000070002000c00180000000000400080100002000400000040000000000000020002001000200040000000000180040000000000080010004000000180000000000000080080000001800000000000000400080000002000000000010012000c0040000000200000000000000400040000003000000040000001000000000010000000
  | 55 => 0xa00000008000000e000800000000000005c00100010000002c0018000000a000000000010004000000100010010000800300010008000000000020010000000080020004000c0000000000000180030000000000000000000000000000000003000200000018000000000240000001000000180030000000000100000000000000140010000000000080000000000200000018002000000040008005000e000c00000030006001400080000000002400400000004000400000000000000400100010004000800100000004000c001000000000008002000100000000000000d00000038000000200120008001000b000200000000000000a00080008002000600180000001000200080040000000c000000000050000000000000000000000c0030001000200040028013000600000018000000200000020000002e002400080050000000000000040004000400280000010000c000800d0002000000000000000001000600000002000400000010002000000100040000000c0008002000600080008002000000100018000000e000c004000000000004001800500060014000000000020004000000100000000001800000000004000000a0000000c0010000000200000008000000a00000000002000200000018002000000080000002000000000000002000800180000001001200040008000000000040000005000400000008004000200180008000000000000000001000c00200000000000400000008004000000000000000000200000000011000400080000003000000100008000000200100000001000000000000001000600000000002000200000068006000200100008000000e0014000000000000038000800000000014000000900060000000000000080000002800000000000001000100040000000800000080000000800100000000002000000160014004000500100000002000000020000000000c0000000400100010004000000000000002000000000010000000000000000002001400080020000001c00000010002000c00700010000000800000000000000000100050000001400000000004000400680070000000800080060006000000280010000001000000010000000000000000002000c001000300020008004000200000010000000100000004000000c00020000000000500000000000000700000000000800400020000000000000060010000000b000000080000007000a000000000000000002000000000000002000080000000000000200050002000800180000006001800000030002001800080000002000000300000002000000100000010000000180010004000400280010002000000000000004000000000130004002c0028001000800100008000000600000000001000200080000001000c000400
  | 56 => 0x180030000000000080000000000000080010006000c00000000000000000400000000002400280040000000000000050002000000080000000000800300000000000000000020010001000000010002000000000090000004400080000000000000000030000000000000090002000400000010006000400080000004002800080000000000400200030002000400080020000000800000000000000400080040000000000000000022000400080040000000800080000000003c0018000000600100008000000400040008002000e006400000000002000400080000002000400000030004000400100030002003400100000000000800080020000000000000000002001800000000002000000080010000001400180050002000c0010000000600040008000000000080020001001600000000004000e000000c8006000000000000000000400040008000000a000000180010012000400500060000000c00280000006000000080020002001000100000014000c00080000000000400100000004001c000000100020000001001a000000000008001000000000000003000a00000010016000200000000001001e000400400010000001c00000030000000c0000000000c000800500000006001800080000000000400000000000003c0008000000200100000000000200000000002000000040000000000000000028003000200480010002000600040008002000800040010001000200200018000000000040038000000200000000000000000000010004001800000000001000000040028008000400080058000000a00000010003000e000400300000000000800080060004001400080000002000c0008000000e00000018003000e001000000080000000400000000002000800100010000000000000000000000800000040000000000100000002001400000030000000c00400110004001800b0000000400040048000000200000008000000200180038000000000280028007000400000008008000a001800000000000000000000060000000000100000002000800000000000000400000040000000400300000004000c0010002000600100000002000200000008001000000080008000001000080000000000800040008001000400040000007000200000010000000000000000001000000000018002000000000018001000400400000000000a000000000040002000000000060000001000000040000000800000000000000400080010000000000000010000000400300030000000000080000002000000180000000000400080000006000400100010006000000180020000000400b000100020008000800800000000000000500120004000800100000000000000200040004006800000000000000000300040000000000100
  | 57 => 0x980000000000c0038000000000380038001000800240018001000800040028000000c000000080060000000000000000000000000080070000000000100000000001400380000006000c00180000006001000000010002001000100000008002c00000020004000400080000002000000080000008000400680020006002000080000002002c00000030002000000080040000000000000010002000000000010010000400000020000000000000060000000000080010002000000000050002000000000000000000400000010000000000000000002000000380000008000000000040006001800000020000000000080060004001000200000002000400280010002000000180060002000000100000002002000180050002000000000010000000800180120000000000200030000000000000090004000000080010000000400000050000000400100010000000000180000006001400100020000004c0000000000a000000180050002000c004000d00000000001800100000000000000000000018001800300080000000000e000200000000000000600040048001000000040008001000000000000000000c000c00100010002001000100000006000400400020000000c00300000000000400000000000000000000010000000400480010002000000000010006000c00000000008000000100000002001000280030004000000100000004000000000060006000c00000040018000c00000000000000400100030002000000600000006000000000020000000400100020002000400080090012000000000000002000000000080010000000180010002000800000000008000c0000001000000000018001000600000000003000200040000002003e00040008005000000040058001000a000000480000002000000000000004000400080000006002800100000002001c000000000000000001800000020000000800c0004000000000000004000000500030000000800280040002000800000000000000400100020008000400000040018000800000010000000000000050002001000000040004000000000010002000400080010000000000080000000000000000000006000800000000002000000000000000000400080000006000000080050004000000000020000000400000000004000000000090000000000080000002000000100040004000000000000002002000080000006000400100000002000800000010004004400200020004000400000050000000000000000000000c00000000002002c0008000000000040000000000200000000000000400100000002000400080038000000a003000400020022000000000000002000c0000009000000040030007000400000000005000200040000000000400000
  | 58 => 0x28000001600000020004000000000020000000000000010003000a000c0018002000400040000000000e0004000000000000000000800c0000000000080000000000c0000005000c000000200040002001000000000002000000280090002000400000050000000c0000000000400100010002000200000010003000000000000000000400100040001000000080020000000a00000010003000200040018000000e00140000010000400000010008000000140000002000400000000003000200000000000000400040018000000000100018000000200340020000000600340000008000000040000003000a000c00c8004000000040010000000200000008006000000000000007000200000008002000200000038000000600000000002000a0000001000b000000380010000000c000c002000000060018004800000000014005000000020000001000000000004000800500000014000800100040000002800000000000001000100040004000000200040004000800000040000001800200000000000800000000000002000100020000001800000020004001000000080004001800000020018000000300080000000000000000024001000100040000000800000080000001800300000024002000100040008002000200000000000800500100000000000200000024002000100060004001000000020000003800000000000000000400000010000800000040000001000100040004000000300020000001000000000000001800000080008001000100020000002800c00000004000000200020020002800100000004000000100000000001000200020004000800200000000002000000000000002800000000000000800000120004001000a000000040000000000000000008000000000000008001000600000018002000000000008001000000040028000000800000000002001400040000013000400000018009000400000000001000400000008000000800080000000000000180000001000000000048008000000040000005000a000800100000000000c0000005000c00000008008000000040000000000200040038011000200040028000000a000800080000004000800000050002000000000020000000000000000004000000000000008000000080010000000400080020008000000080010000000400000000004001c00000020004001000000000000001400000020002000400100050002001c00000000002000800080000002000000280000000000000100040000000400180020012000400000050000000000100010000000000080000000000400300020004001c00280000006001000380010000000400080000004000800080050000000000880000004000000080020004007800300000004001c00080000
  | 59 => 0xc5d000022a4000000000001d5c00011ed971500000000000000011b6000000000000000000000027940000348c000023d0fc24f14d2a124e29bc0000eb3161752a4369933d0000311c00000000000000000000000000000000001ad800014fc2904ccca65b420a114505b0000000000000001396000000008372c2c492a00008128ea8000000000001a830000000000002b40000000068d0000000040b400000000000000037e8000000068c0fe60000450e000043a24cd18d61b38cba12ab4d4468a07a40dcb000000012880000339068d514500004f0400000000000024e161c0000555339e03a409d800000002e592ad0b583d0a256cc09a085000016bc00012f50c96000089b27ee4b3659140000a6700007fa80880dd2570400009e90000000000000000000338800002379f1b351600015081e960000000000002a60000000000022d8000000000000cb40000408c000000000005e3c0002aa0000000004b900004be00000e8c000000004308c228000000000000000000189e00000000b394aec000000000003a50241400029dc00000000000000000000006000000080000000000400100020000000800000000002000c00200000002000000080000000000c00080000006000000000000000000000000000006001000000000002001c0000000000c0028001000100060008000000000000008000000100020010000000000000000001800400000000001000600020008006800000040000000000200000008000000200020004000000300020048000000100000008003000300000000001000000000008000000900020004000800e000c00180010000000e00000000001000200000000000000200000000001000000000008000000a00000000001000200040018000000400040000000000a0010000000200000000000000b0000000400380090010000c000000100060000000000000020000000800300020000003800100000000000800100000008002000100000004000000100020000000800000020004001800000000000000800100000000000000000020004005800a0000003800080020002000000500000000000000180000000000800080050000000800000010006000000500010000000000080000006001c0018003000a00040008000000800100028000001e00000018004000a000000080010004000000180000000000400000020006000800080010002002c00400000002000400000000002000000180030008000000000000002000c002000a0000001800200000000001800000010004000c00000000002000800480000000000000000000000000c0008002000200100000001000000000010007000600000000000000c000c001000700040000000001100000004000800300020010000800200000000
  | 60 => 0x2bcf48620000cbe1c8d00000000665000000008330000000000000000f200000000037bc136952d0ce24ed43c889344396a9bc0de892a47e21f080001990000000000001a640000844401b14d250a600011d025cb00009364000000041383e2400025cf4d9a4044b2a8000066000006fc80004c30a6200000000501c4070876800000004ca4000115335400000000155f18e60000000000014700a44000175600000000000000050bc000000029f000005cf4000036b088c3c60000000057f286103f609f0304200000000000000000000000000000000000000000000000000002b2300000001479883c4adc000000000004c346a2000000e2513041ac0000000000047ac000000027c215b010593c905c83370000000000009208bb4000034c60000db90000000037ac0000000401c061000000002596000000011d1000067c13a3a2d6333e5024f7e9cac3baa00003859326269c00000000000559c00000000d2744aa0000000000015a0000000020834a8e7948c868fdc43be0d40000000000001a1000006da10b600000001b7600000000000107615360000d5591083e1a00010e70d6621f20000ce49ac305dc2edc000110c31c03c8000027162e4299ccfb3000054a87eb8000000050e00000000000000000000000000012b244e800028ad000000006cd20d831fc4af143420990000000000006f40e8c6480fa7804800bc79d80000283506400009af10a529820000cd927790f3200000000000000022780a4800016e489b0ad080003b0c00000000b1c18ac000000000003d7e00012e2800000002d30b40813d000000000002b5f17b6647c22a8f0e17501cd000000000000000141c8000048266340000d5d000000000000f103de67e00000000000000000000000000000000c2718873cf4000000004e10000aa780002a1e000000291bc2210260c401c77c9e94000000014a688042ac66694698a93f58643e702ce86f90664711863e0a6429f8a1e8aa99e3e3d44094c473a33610ba73f88b69565521c35fd5638f9638343ad105f2b8f19e882b0614000000006ccc48e204e0d828fdd4360b27299aa53c0000000413e3b612ef29ad0df03554823859c56d290e15419a81231a8d0086d80001c7a91a8000000045e866012378000000038d4414000000009004000280700000000e18800040704d600002b81000073f4000276400000804dc70e521588ab8cb9915490000b0a8000000000001e114d6000055cc743839a817817f60000a5780000eaa00000000000042026bc0000000000000000000000464451a00000000000000005878000262a78e400000001b3a2bed4501bfc28200d280000000265602e000027043bb65d50000000000008f9c0000f543a4850e4000150800001a5c000000000000000ee58b890000000000000000000
  | 61 => 0xc0000b390000000071d000000000840ae00000000000000000000000034109fa800000000000224c00015f30a384b18000000000008a38b9600000000000000000001b760000fb500000000000000004f50000575800022fb000000006bc199500000000c0800000000000094c80000000000155580004054a8b00000000000000000000000000000000000a8400008d5000000002b4e3ea54ef85e800847544ae38000000023100000000000000007e680003fe20000b0f27730000000000000000000388c0000000000000000002b9a00002ad5323958e26ae793c000000000000000fa29e83542c000112c92fc00000001276a702237ea1e49c68000321200000000000000000000001aaf00000000011a3522f540000000000000009b100000000000048882e6000000000000e2e0000000021490d81387000000000000a7d00004f60cdb01d327aea2f41a2852930da0fbd43f0c8b42e463b0a6e878700000000000000000003b340000000098a8820957282f325800000000000000000000001dec118e00005989c13418a2e6d118148c0000000056a0000204006b411c1de60d9e00004500000329c106c0000000274800007070000000000000000000000000000001c2a0000aa28000000000009afc000000000009a152e626c1421e0f74fb082e2466836104881d110000000072f800000000000000283e38ca955094180000000000156880001f180000000207100cc0000000000000005ee8bf300004f840000480000037520000000000022e8000132b167a00000000c280b9e29fe548c355a5643e2e70d424d80000000733400000003618000000000000000000141580000000000000000001e1a9f141b8000019a40000d3e8000471600000000000454cb0f40000fc949b84b4922c98b300004c7c00000003fde9f0cc510000000000000002a2b43ea00000000ae73ec6000000000000000a25c000000000005eec000000000004ab400000004af00f19420a4a6509c7179414000028ec557517d2236000084543b411ee184c607cad900002d820000000000000000000ac90970000052a0000180649e87c102a0a4641554356d0c00cd92e00196c000271e178858950818ab826c00000f58107330a20000a400a8c58b065b000000e5278c583d607190e10a817f0000227807ea4d4c00000000000000101e8000520a00000000000000000010e900001056000000000001cc400013070000000000010e4000000000000e7c8c53093c17c0fbc0000000000000000000000000011509cb034980000485a68a0000000000000000000000156c80003a26000122100002ca075e8c608c5b44843560a488801000038600000000000000000000000096e00014ef000000000000000299b000000000001265000000000e50000073e4da0000
  | 62 => 0x26ce9dc00001f2e3426633c000000000000000000000000002f9c000199a000000006ec0d1e1176023477300000000000000020560000000000006582c0200000000000000000014c28000000028240000cfa3bba5e3553a80670000970d320abb0000000009089b3a3bc2298ca810000000092fccbaa1f8160400000000000000000000001a6500004a6d16900000000328d218000028fc0000aac80000000607000012645884a118dbb800000000000c430000580636cc4712b263be200012d480003fa6a8e800000000000a9300000fc10000000006c9a4914e4000000024c11a847ba096f0acb00009668000025900000000f9a13c32c1800000000000578e00000e400000000000112381ed34380000000000048d800000000000000000012c69c8203782124896800000000001325000000000000000000022a800000000000000000005690000445a7f781d38000000000013a5058401e48050000000000000000000155a000037b000000000000a5d80001e17000000000000be61b4621200001af700009a340002069184a00000000c353822000000000001dc800011608000000000012ab984317820000e5a00000000b11866280004910000085b87080000000000000001eca00000000000277e735000000000000a89c00000003fdc100c20e00004c669f388eb89c9105c000000010b1384400000000758103400000000f67447c0cf92979b060000000000000000000a6d0000000000000000a9d8000453200009c315d300008364315800051ba74cc84c1c771d2e9c8c000000015669430b478000000000000000000000000000000000000000000000000575a5780000000000000000000000000005688b160e45000000007f3a73f0000000000024355618ad0c2ab8000388226cc4ee20331f8ca4b00b11b2521c83c0044a8326000094a029a03b7000000ac00000000000000060280000000707c013954700003e9940085994eee0d68d0d99b942fc00000000f5352820ae0a629e2912de000114c079700000000d39860f0000000023024a1425a00006ee0856235842280ec00db2682000038f981d000000000001bd22de6953093a1a17022424e08a7a8091c8600002a78000000000000000000576606653a1044a130696284109703481cab94223800044ba00000000a40000000000001773000050d8cc200003b4825f8d25a5a453c8000016f0000000069e40002a2344266f59046a66900002cf400000000000000100180000000a22917085270432a33435b1ab500000000000000000000001026800000000000ae4920c14cc72c40001a374c2853b06098000560c393865680000000194c65a80000bb0305c3d12b090000000133000000000000110f000000006b080000000000000005a8800000000000000000049f
  | 63 => 0x3f71476000029819bc2ecc000000000000000a220758997d00007a78000107441241df40000f7e0000386852f9ffc000051b81f52b60519e11b8ea098f000000000c4c80002b3c1d5845c8000346600012a5abb81cd00f5c00590390c7898e484890462d6e56651fc013e3e42810ce7d005d20a6981d04390823526011017d811322660001191a3cb245400000000017000000000000000000055a00000000501463f404c80da00ae054400000000000000000000001d3c08c000000004ed062300000000576290100000000000000000000000000002fc2ca0000000077a000006f20000000000017960000afdccf9000000002940000000048ae5e6c000000000003498000000050c00000e4d1bfa37e2000125a000045dc644c2c7298a0078679ce1916a105d4382c4d6245231625b144a71a0928461bb8fd31200002892895ab000052d000000000000188600000000211000000000000f2b24d480c000018d40000000000000001c420000f79000052a647193d28000000000000002a43000000000000000359eaf9889e8d8a2a1203e097c000000009331629800005e6a6186429c560000141ca7b916c0bf24cb4000000000003b7800000000000000075797f1000066e8abb0000508018780000000000000000000ba2068c37386c3a92200004748000000000005aa40000000121c0d3473800002afc0000000000000000000000000022ec00000002a9255742e083f1000007f491e48e5272200000000000000032820000c0492f6376084f800025190000a36c00000000000437062e0000000000002352bb455f800000000000000000008ad1c335868506c00016d6193e000029e0000583e1520747a55111e29380bbc21c902ee731008d0638172800000000c8e000000000001cad456000000000b69000000002ed800000000000000097b57a20000a138000000074504e321910000a18d3280b3a000055b0d2ca1fa00004c9cb33288e0000524c00000000000000000000000000000000000003e1400006200e383e3c0000000000000003595397814d00000000000000000000000daf800016640000d7f0000000000000001ac6000050acc6580002f5a09f135016371ade0000000000054820001564130e000031880000d1225b4258c088839244a608780290000016c000000000004992000000000000000000000017ef00000000000000000000000000294600000000000000056d05bac0001fc33d9aa07800011e100006494000000025920000762a81103065c09043253a33b25e4c90d00002d106bf400000000000a0e8e57924700003c0c3fa0d4a0000000122300003e9600000000000000000000000000000095b0f54278f00000000000291b4a7c0000000175500000c2c9f49e551e2c3a18b2b800002c817f800
  | 64 => 0xaa00000001c0c42da835838c800000000000afd000000007dc002000000000000025600003f7830200411328000002f0000000000000000000000017c425d11a0800049cc0598000000000000cc4000000000000000000000000000000726a679440c9a6948f8d5340049bf400012a6000000005340000292400008550000000037fc000000000000000000000028f200000000000000000007008000000000000000df300008fa0000000031d0000029d2512000000014878ee936ba80600000000316a8f4000015cb15d285f0000000005d8afa40000c4840be01f4b0894cb19fc0a60e798ff80000000000000001eb000001ed8000403c0000aa69d59000032f480e97a00000000000000000000801c000000000009bf8c4981a400000000000000041689b20000028638c4594d10e800058480000000000000000000000136f473aa1d000000000f4c47fc00006a100006414000154c42a29b2d40b237408a412595d30000240c0000f24218e51960000000161c0000000000000000c66295c00028243c0ca98539b01e60ebca0e000000004ae800002400da9000023990d10000000031385e49f4d00002050000000000000000000277600000000000000051d0937c55f800000007e28000000000000000000000000006e996261266000000002a8000057f65910000162437884494e9580000000a7c400000000000313553b96293d565bf070e80000000000000000000000000000022c800006ce00001bfd0000130c00006fa000071ecb170000000086e43e6282500006f1459480001c2653c519018340000ab2c00002c126fead14ca392ec1c680000798147b1e14472132214e33b5c0000b6c9f9500002d9400023ed000096ec0001d8a000065691668000538c000000025ea566a5fc0000223c000056e400029791fb68d7c000276a00004e28000000030aa000000008203a9409a800010ec0252753953d800054ae04b8000010a0000000000026570000284c0000cc243323a38000000000009674000000000000614c77817200000ea00000000000000006b5000000001740dc4abc40000000000000004dc48028230837b455035c0752a31e00000000fc1040a531e000000000001e4e5030000000000000000418000037b60000000040d0000337800000000c288854667ab9f4482000000018d7000000000000000000000000000b7a00000000000000024200000000181e26900000db8239b000024e888987c0000080ac0001126052000000000bd3000000000001723293600008c60000000000000000356000001240001e793d4a000000002af00be3ff80001f5135c0a2e81599bb82c0a55e818e9f6821de05f08bd036200549d74b6a0000000000000001fbd0000000025a935400000000000000000
  | 65 => 0xc6aa6f800000000d8490740000000112800000000000000070096040f8228e4000150b80000000203800000000000000000029360000000000000000000000000000000000a9707fe80000000000000000000000000000000000000000155a80d7000000000000000000018b935b969e36887ee80000000251a317c0000257085400000aa08ac000013f0e7e1a6200000000000000057b207ac000000000003c440001ca600000000000000055a88d4000019231a8a7b891ad848f180487f504404ce2fa42914ce602f60000907006790b0350a006d5a028560000381c000000000000000d01800000001cd80000393000023fc0000c2a000000000ce0e813d18a30c00019db39846bf01b008b60760237435c81c2130200000002b66494e050d437831440dc00000002abd3b7a00000002245000013980000000330c60ec0aa86f60a0a00000002234000093b80000000111a2a94000000000000000000000000008f34000000000000000000177a2b2c00000001f6f000000000001a945208a960000000006ae35e80000000000000000000000417a00014d580000000a2509798ecf000038f88a221e735882018000000043ca13651ea188803b283ad585000034cc60f1533089642b833c510f9dcd0c3800005628000000000005932ad20000a710000225f00000000b1d990000009be131d0000000026e0000264900000000a47a2a5000042e064980000000000000000001bf8104c0000431000038bc000000000000000323800000000000c1580003f0a0000000256017426ae948600004cd85c880001c5a2026000088100000000398c000006400003f3cd3e16db0000730558700000af8000000000002d7400000000000000095f080c00000000180000022830000000000022de5020a128000000000000000000000000000001209a4d4000073e0f729bd000000000000271300000000000166c00000000f15800000000000000000016ae1250000123a00000000000000000000000000185e305e0000048ac28283a68980000000000018880001af4000000000001b690000230c00022d0000000005310000157834088ed94a4000000003a80000000000000000000000000016131b0e000000006e3886b0000a80c00000001956000115d800000007fb40000000000000000000000000031451e1800050e4000000000000000000000000000000000000000000000000000028ef3564aa0021e1df927ba0334dad0000285889f02591be510446468cb01b7114aa926505080000000000089a09db0a760000ce58000385600011809e27586e718400000000000000069c165a489e00013490000000068600000000000000000000a024db63a511001f5c41283bb400025ac00007b58000000000002e8000009f80000000000000001a8600000
  | 66 => 0xc4e813c25c81b3481200002dee000000025402dcc9ff8000000000000000000188006fe00000001fc00c906f60000000000000000000000016bc0000000228f359c00000000000219a5d640000000000089a52c19f33178016c900486d800006efcc6480000adc9650000000000007c080000db94e760000000000000000000f17000000002b44e9a000000000ca0c768bb54e3e5facd8c1244000000011b600003b262f9400021e400000000630800000008ae4e0b0000000000008f6a27600000000000000042d80000000096c000000007eb0d8900009bd80000a5b04de000067300000f6a0000e7b000000000000000000000000000d301443000055bcbb682e7103c0000d1f00000000000145f1582143c087c7859b470000000097d2a0a1fd42cb081f00003faa0000000000003f045840000000000092783e68000000000000000000000026190dd0d5624306d400000000293c1abc00017170000000052e0000275c0000000000000000000000000000000000000263d3c5888ed38d0f210000805c00017a9211ea458c2980000000000000000000000000000000002568000003725ba00009728bcc800000000000afa9f1d58560000f5e80004762000036a0137444000004938d3b00007bb1205892d00000000000000019ac873400013a200000d8d5170000000000011ee0000507875f95f8801800000000f7d00000000000000000003e8e2b2000003da0000000000007cf088a000003415703ab400000000000550a00000b2800000005de4e4021443b004ae50c380002a3000000000bfc000018c94f0a12c000000003ae9def000000000002aad50106eac5eb86fe212600000000000455a000000000003a440001562a767248c31947298000522a00000001c6b2cda000084200000000000126e9b090000a140000000050ec00008830000000000002f5000000000000ec380002c8c5d9d18321cf389800013ef80000000000000000000000043c97f00002d3a6ec40000000533e12e89580fb30000000135c8000565252d4000000044d49eb4bc1825b0afc00000000000000000009120000000000000000000000000000000d190000a72c0001ed8366895fc0001f0c00002c6000023e2000000000001fdf00000000f6904a3107c87c09fd952f0dbe9e54611000000008ea0000057800000000a6f9b9754d202c4000135b0000914c0000000000000000001d3c0000000126404a40f027a80ac500f00de672f12220000000087aca720000000020cc0001d170000ad20e2280000000974cba208a80000000000000000000000000000000116247cb5900004e100001479249c2ebe80040000fb141a283707f0168540242dfc00006310000000000000002d7a5ebd370800000002ab8222295c0000a9a94c220c30000000000000004
  | 67 => 0xfa748940000ad6800000006c680000000000094e4c38a6230000306c0000000000081bc2598000000000000000aa0306a8564732284b0ea200010b891831dc2136d5ff1a8e41a600009a8081c0000ad28f919192000098349d59cd522e2924c00005dd426a9f812edaaec00009878dc98000458000003828000347665881b90000000000007e21b0f00000000c00250e2b7a00015c22b7e0000000000026340000000000020d73b4a8768b570000558800000002ae9055c98c83491e57121a5f9485b22311524671c49ca08436e82a00000000023fa5f28bce91aa2cbc2d1c000099e000000000000000000000004d2000000005f60d60a42e5678aeed55a15fc00000000000000033ea4f88000000000001f400000aac000000000002b740000000000009883c3400014e1a701479e1b8c2c02b53000045e0000000022ea43f8ff011dd0000000014b2a5500000000c2782c00000164c0001eae1abe79580000000370e9f7800000ee00000000000000033240000000000007a602152f18000000033340000000000000011800000116e7d7800000df3e4c000000000000000783800000000000997ccf40000000000000000000000000000000000000009d80000000178c4da93f68000166c7bd04f08000000000009a010a600000000000000016b4ac9c000049930ea0c9d0a2a45038f2328893b8d9b345aa3580001a9902fc529c000000000000001114000000000ce80000000000066ac000000000006c54000000000001b1c0000e46000000000001c3c0000000000004c0085e29ec00009aa00000000000000000006f34a8213144c12486d04d13e44bcc0000f2f0225280a5c6d271247a51d284c0ff593f542cc00003e324e508a800007f7231c03f4299400028cc0000000000000000d3c000000000000000000000000001dce06b00002a6c000000000000d4700007e3000000003e1200000a21f004f6a5c689b8127023884e30cb7800022d2627c02c800006d829f134e1602000052a84478000000000013c4000000006e684e800000000000000000004c26000000000001a5600000000eac0e4a000000000003c88b0000001f9640828044a1d9201000000012b8000000000000000000000000000f9000000ea60000000281a1a120000000233b51684414000000013bc000000023b90000000000020783d109fec4a98000000073692062c3b0000000023d183e00009f04fcc800017f000008990f251c746f1cd4b8ca500000000000000000006f980001a0f00004d6400000a6000029101ff951b3eee000000013442ef651a8000000007be00008f400000000000000025d401207e84d760000237c66804df21bd00000000000000000000000000000051829a60e4386750f2a450c82f88d60000ac94000274b1ee20fec
  | 68 => 0x4000000036fa000095f0000452a3224000000056ee87bc0001f540000ab712c88b9800000000000223d00004471259000000000000000067f578c3388355026028e00000b87264b0000aa2c000000000000000a7a00002a4a00011f78000000000013cc0000285e5edc33803e4089c9a3c0000000420e00000000c451f8a00000000000000039240000000000000005db0d740000765cc9f80002254000000013f00fae000000008d500004b654312b072b3061740002b7c0a28a49d23f000015a60000000000000000000000111d00000000b8500000000146d3a2a9b30000af2800014b7000000000001e243fa44ef800000000000000031f800000000000000000000006e0800000002e18000000028d9000000000000000000000008d38659310a000000000004dce3eb43ef28d2552aa5748352a4f0d7c24c521411fa04dc00000000000000012bd2998c16104c511c00000000640000046594a237f6aca0b78248a0000511000007f245f2811c0001b88000029c4d5b24f80000163478d1e260dda69400000000509e58b54610000000000011d686174cb800000002b5b2c0e413400000003c4a000034b000000006d500000d9400003b289ca80004bea697905f94bc20caa5891950b80000000013108000000000000000000000000000000000000000000000000201a00000000c4208b000011a68000017a000000000003fb888680001e7800000000d49185f0abe0d0c000000038ae00000002a891dfe19f93c0287116ee8990000277a283479340000c6a2c7ab034000079e000000011e08f010000af0c9ff2c5000000000000000000000000000000010b221b120f8e7114a85ff0000000029802f7c70c8ba72e127878000205e23a851cd27201de50f0000000000000000741902588ee2780383533b8cba0e0200002ae94180ab80000000007e0000000000000004e800b20fec0000414a14a800022d407c200000000000000000012cc8000000014d80000000000000001c8000000000000bfb0000000000000000000000000000000000000000000000e20000000000001456000000005fd23f6039a000000018a913a40a6cb1080ab13847134a8f23d3227e00000000000000069a54b78000000000009d9aab00ba68128b9b29b6495853449dc84bb08d6aa946091f4323c600007a3a82000000238000236958863d991cc800000009a90c3d06e826d83ef844803ac00005a60000000030286b9400000000000000000000000000000000000000000364800017430000000040a800000000000000191000000a500d397b2000000014f19d620000082400019f7000000004608000095200006198a2100002f380002b184e38000000000002d6a353839300000000000114f101606580f5130e26f039944aa00001ebe00008a0400005c2
  | 69 => 0x26aa000070183590000781143200001bd000008cb800017fa4b5c988232e000000008bb800013120000514800000005d8ccbd8000135000000000000000000000001afa5894902818e00001bf69fe878e1dda000019b800007dc0000167c16fa4a00000000124700003bbc57d0c150000000014b400010cc39646c340000000000000011718000000033600000000000001e0000291c0c041a88a059a58000050e06eb9cf100000000c9e800000005ce491e000000000000dd29829000000009ed0000000000013aa8000000099840001d29155a278800004d60e0655893d7254f2bfc00000000000536e0000000281b37c468b13508000000041e00000c0c0a30a76c7e5a93b357603d47f30000354c0000ea810523ddc0bdc61713d9000000000000000000000014be124341f6000000000004f5211645aea7d320d2350400000004cf6a8814dc0000000060340000000064600000001a8d32e27ae113f000000004e0c000000000003e9400000002b700000a7b000000003f5ccfb2af1429000015b213170a7aaff00001d61000000010e18000307a000000000003b807250000000004be6edc000000000000000f109ce802c66d950c08c3a00001e8c564ac02042c0000000219233fc7318000014000004ec000011de366200003fd000000004e3c781000044702ec00000e6900009258000000052ca2ef80000000000000000000000000000000001da3000000000000000000000004b400003c5a6bac00000000000000054880000788000000000000000999c7d70000283c23d4751a1291dfc6044000000042048c940001b5c00000000000000000001f9400000000000000000000000000156c0000000228c0000000000038fa00002038fe24ad6000000000004ec40000e5c8488000005047c32b570192afb0eaa9eb400381c6c000209b1556179400000002cfe00000001d390000a5a40000000000043d870f0000000000000000eba4e2a49a40001166100a00000000000300a031c0000f41038a0000e40800051c44f512068000510a0000b1407db1b000000292000042760d305c9800001a05bb4c6c1df500000000c9d000000000000000000047cc000000000000000000035300004dae000000019ed00000000b9f8076114c4f98bb8800000000001390aa821344593400007450000ae60be1217953ac00a0023824f000076b0fe7000000001b2096f8000000071b800000000fe6000000000000000000000000001bdc000000000004348000109a0efc000000009ba1a9f031ab0a4000220447aa9e1c9a5000049188cfc00008ad276251940000e8d000000000000000000000000001df60e40000052c94322da259d492e8000000049f08f805700612000000005e40000000129a99a8195e327800000001c2c000000015f70000970
  | 70 => 0x54edaa8d80000544142aa25c57480000000000000000001368000000000ef54681935394ea6e400000000000065428e88804418316000000000b5c513c00000000000000001280000000abd4c69a7d646922e640002b7b35a6a4340000dcf1ad691e0236800054840000b058000000000000001da02cf247d130589ad45fa5ca401d24cb0be205140eaa5a82ce85790eb3a3860aac42b000008fc00000000fd1800002a4000000000005774553872581fb00002b5c5261d822a1a69554ca080a0000535945c881f070e6ca40000000406206bc00010ea4f5e00014fd8000000000000000000000056055121e7f0e7c0000000000000002b8c000000000000000fe39c5326320000fc2036f48209a000000000286a000129a2b95396e14c4050a4fa19d2000000015912106000000000000000859423c800000008ef000028ee0a00814503d0d8f0000b0780b48000000050900000000521400008afab1600000e38a5600000000b0e8420000000003ab40000000000054b14aa00000000000103f99b53e32af40920298900000000f4b817900000000000139b16d640c800000002cca00001dc80000000000000005a7120e00011c71c071cdc3dbd1160000218e0000000000002125ba885100002608abec00000000000000053082a43f54000000019c61f1c0000000259e26002c4400000000000000033d0000000000000002c3500002a4c000000040d659640000c323606869400000000000000000014ae26f2000000000000000000000008d400000000e968000219c259800017e80d3e595140fa75b0328000000000003b4e2d2c00012aa13763afc00000000000ad3427f00531e5c000000000002fb8836800027f51a3a58c80001cde41e60be451ca5610000000000000000000a5808b50000562e23340000000000047c400020ae2dae0001508a34c2f3c213ca670993424a2584000104c0d64432c0001253000029dc00005f24436000000008fe000000010a78000000037303c60000497800004ed0b3308900000bf0000000000000000100f00000001064000025108a7c51a000051c20000000000053d4365c0002ab247f800000000b01086874a8000000000002c2400000000000000000000000000000000000000000a73c0002a96250081d4da8828500002b9800000001c84461c53c2c093eda27d00002c4d47a25094000022b15d600000000000104800015008f220d2a2a7c000000000000000617a9ff4dd2611926d96c94a082a3961798162f5640cc82a1d8b00000000000000047acae50fa980000cce00000000a2f0000a1740001af147342fc0e2c9b6b578a46880001737253e993400000002bfe0000fbe800000004e0000000000000a9d07411c9000004a754a58e0a3e9000000000000000002cc000000000000001017000
  | 71 => 0x551d4014400000000000061489d099aa000000000000b08000000006080908000000011218d9c00000000000000000000000702800000003d10000000000001ce90248000000056505381ec00d40000026522390000000052397270000000000000003dbc0000000000000000000e8c8000000031c0ad8953e28f800000000000011e000059200000000000097a0000000002b80001fd900003f30c3e00004c40391c000000000000000000000000000000000164700006d8c000000006be00000000000377400f440c0000000000011f80000548a81d800008cc0000619c165928e0000000000000003ab80000000000021ae5da434496fb343aa4c800002ef2a3e00002d2249121f400003660000201c00000001f2238b63b685028d595076000010e000000009c4800012600000406c000000033a453852e40fb50a4a79a000020f900008aa400016c63106000000000000e5e000142680000000371007d85600f1031b53a21ea700000b10f75269705e4000000000003b3200000001172000028c00001e2a0fa8a5401d5800003a000000029dca5826187c0002997000000000001ad600000000000000000000001449000000000000d11800000006e2c00000003ad606600000000000006dcbfd0000000000000001e64000000000000000000000000000000532a0000ae3113e0000909c7459cd91ec6000000011624a540000000224032ce00015f197cf54b61064b6f84a22c5e2bd8000000004081af0000000000008d3cf07904a06568e3400000000000000020f91480000aee4000008712d6683136b1461000089d4000000040b497b400000000000910d3ed000051ea6f185708000000091602d28000313c0000aea863a395c9508000000000007c94f37229c014610d44b10000470e626000019e223c853e000018be15f28340dca941c43120a4c3dc94ea415e00004da00000e7a0000d6fab322ede0000ad3000000006f64ce1800000003f8c844264e1a0c58880001190000016e80002b4600003d2c000000021ee0000000000000000000061aabc000028a000000004ace0000272800000003b0400000000000000061a05a940c80b1831d800000000000000162a39de00000000000431e000000000ac1ac03e202b8800000000000264911800009180000000000000000000000036e65f58000184d0e04261097700e053ecae1c492a7dd00006b5c000000000004098000000000007db000000001f0a000000012bb23f6000133120ea40a69e7800021b500007c7c0000ecc0000000074e9b300000000000000000baa000000011a9006eaf34b180a4d000000000000000450c000000005091d4cadb00001fb800006c1400000c607ce8cbc4190000000043d108c0bca0000259c0001e9f090a2c800002a06000007f939e1ba052bc6f
  | 72 => 0x3c320000e4509ba000072a80000000246e00000000000000000000000000000055f4000000055ee8c9847b9ead35c20000f75800012820e5827f98ea00000000000000008a084810fb29e91fda48b000000883120ace807391ad0000735800028f118340000000000000000000b721636000000000b3800000001cc87cd82800bfa62b90fb8e9b000063a550400004b16200000000000000000084803e3000083f40000000000057ac61ea2aa000000011879b620000320884a0a421e8433740001db738f055ac0000a0a000046603a723b0192096e00f814304c4e80640000000473051fc1d31e43326c5924b21226f0000000057e067c1a5800007d100d447c800001c88497043405d800000003f58095145780000000774131d8d0f069e36ac09b0000000087e40000000236407a08942357090e5be00000000437c2e2c640a4f70000260800000000000000000000005732872925d800000000000ca88000128600009eda74c1b5454191be8000000000002c11ef001e8000000000000000000000000001ca28c64202800000002d3447799b7000036b453a8d7b00000000000137d0000000000007370c6800003af925e390cb0606c0a8770000000094a27cd000000000000000306e197c65ba82909989e10059000008f800013990000333c00000000ca940a09064000123d56567704000141232dc00015da855100000000ef5800024c200000000ebd220800000000c7e000000005ed28b309404404846a96d4dc060d8c9683160602053c000062f0a3291fcc7711df1de8000056c000032f2000000024090000504c0000000000000000000000000065b4cf0091b2a86000000000000000000144c800000000000000261f4d6000000002a133d9000000000000019c8d7097c80002bdc0000000000025ee00002d5800046e6000000000000000770c0001bb31e127f088788000000000000001542364410454589b92349e000000012f1274c00005080000000000002d40000282a177c0000000000000000000000000060290f60db122580ae4962aa7f044c00004160000289800000000000000042b80001b114bee98d8000133410722eb15ed066239c8000000000e600007f8800001b90b8c00000000000000000000000000129e0000e8580004dc60000000000000002ca00000000000000014fba10e39a40000000083800000000000249800000000103105b00000000000000000000000000000000000001418a70e000000000001cd00000a590000000000000000000213a4b6000012f41839000041380002315046ea900da480000000000000013fd00000000000000000002b810a3a05c00008490676839a1c4421e82388a3151785a49102a9bf00000c0d54c20793ab000000000000575c520498e000050f800014eb90
  | 73 => 0xa88000097404de86ec0000163141390ba189627e4b7b274102fe81f8e8495fd000000000001a87000000000000d0100000000cb300000f3e000062f0d15204e00000fc9ff919807c60eba28de00000000000151a0000034c000248d00de1b1142603f8000000000000fce00000000e708000024c7fa147d8b5b0000000152d00004c7c876ca7d933d177a9504ba41038540e42f554824bd36963ebc935ac480c10749c09c85d147d628d417d2659467000005be83d1264600010da000000009f500001d78344875940000000528638dcb0685673004723000005664b5e08d4000117e43465274e3f800000b40000e132af000000000000000000001aa00000000281a00005b18af4372000015060000000000002fb2aa255d400010dba2320e521ca90ab8000514679f40001ce900004b207192a60527050f53d202bb00000000b6580003ade000056080001d807f40000095a0000000000000000000000000029aa0e2c0000acd80000000000079919020a140000bef11b0305aaae457700000bd60000d7495f1073a807cc7b1e811b9494240001e300cc20000d629b83132a0000b5c9121340e0205344800037bc000005a00000ae4000032100000000a9b8000000000000a94c80939d00000000a2800002adc3f5402d800000009e0546a0000000062980002174041a0000ce880000000796c00000001a7a5b8800002d200000000c45296c00008fe95cb0e1513140a3ca4501164320ab0400029f3503a54d131304e82d5e78707bb00000000000143d8000369c164147f06f00000000000000002dce0000000000000000f980000000000000000000000000098a8000000048c40000000017b564471608dda1a00000000000003534bca000127ca9071d0a000146483bb00001f8c14492db16ac8608ba99d253016aef0918198f513c82e50769e5f4e06a2043751e6c5620186434d8538238284754ea8a3716f8156803c89e300000000000000000000000000000000004f4c8f4800000000000000000052f600014fc800048420000000000000005cd05c7800000003f1c0001d9600000000000000000000000a1480002930200c22d80dc08ec5dd40000000175a64e0000000000ac86a4c621a02000000009e7888100000529302832d00006cf551ca59741309301383ab1f4cda87cd514233219b61c8456a805c05d65aed17b28dc4d763f0c8de17300000252492b1a9d021864c400000000000000000000000000000137da1d81e54000000020f80aa6325c000000000000000a5c000000001620ff9a0a0414c50cc000000000000000d7f908746da7610c68106f2bc6475800016680f3437182658f4a1cea22755058b0452e8000048b8000000000000000000000000000001b4f032e0000000000037be0000f6780000000000000023aa149c0
  | 74 => 0x3b1800000000000a7008d715b80000f231279000000000000884000000000000000090400012888000415a9f5c1f90000000027dcf2c000004e61fe000003c0000035700000000077c1c4cd1880004a0400006f4800000000000ef2800000000b0d2120f95309286ecb7f00002d387d9ceb9800000000ecc000090a1942ad1c4d00000000047b0c7100000000000000000000000000049a832449520000a6506b4000036590351f89000000000000000014800008448000000071480002a181a9e69d45c4111130989ee536a909e36ae7224a6400000c48000000003c300000000dbd8000000000000000000475e00007ba1e6b000062693f8a211541277ece3795a945d64b5800000000000000103680000000000000000000000000048c12bd066a0a7430d8000000000013cb00001cfa3f50438800056dc0000bf6930700003fa53f38000000000009178000221e00001b2000000003f78000000000007ce400000001f340000c0c098d00009b0c00007ad471000000001a780000000109ba5cd000039000000f5b00006f700000000000000000000f7000000000f8400000000000000000000c7a00000000000000008b8000255000000000200000000000000000000000000000d3d11f5000034dc8d0800000007a54e4b8000000000000001dbe00006b440001bbd00007e90000000000000ff0000202900000000000000020c29c740000000000000000000f62478e27985e2a3a70000000000000000000ac8000000001800343458ea2720000000094996b342141d6c0001c3600000ad400016b800000000bd70000000000000000000420251e89db20c4000000000b6000000001f8000013200000000000016e800004394000000000000000000000000000000000000001a400000000000128400000000000000000000000000000000014898cf6000000000000000510e6c0820c01d74fde000000012b810a0000000000003a803ae521b879c1ea4762145dac3600000000dcf0c0e3ba4000009c0ccb56c4718c2f9800024d01ea8b5197fb40d00000a2500004a88000000001ff0000000000000001e8c00011960b6a00002cbd1a412b2457c67980001664000000000001a1a000000000000325000050f139880000000a6b800000000000565c2268878420c0000000000016ec000033280000000aefc8c20000000000000000000344046193181e9805c00a5c08c1d630a0c08608738c644b020ec8fce8000452090d800019fb000052141c788e547f60000e00964800008f841698000000000000000000000024bc000000044980000386000000000000000000018b40000ac68000000000013fc800000009f84b520000000000010ff12cc23480000000000000008df8000000000000000000120f4e7412943bf12981d480000db08
  | 75 => 0x94e23ee6000088dab081c0c2944bd0960336b00d5129721f22a24af591a1043057843adc7aea2a43e8821293b4815f00003ff0000000000007d6000015380000000000000000000521000000002d189051441000000000000fd0000000000000000000000000000000277c2800577526304150f68ae750f100002738137c00011550000a2e077a8bf329523edd30b0f3b106a0000000000000009a940001f7c0000000091a18680000000087580001a100000000130a0000000000019850000000007ea7720000ad540188000072a551000020d4456a0000000000000000000eb5000000001ec8e51103c00000000328194925aa0000c5e0ee5000006cc0000000543e4e48000000000002a240f200000000a070000000034a2552cedd8f7d0000000071380000000442cb19a2e01c560bfc00000004d746bc890b80003b7400000000000000000000000f6e1e6e000118b01923f3806e848b1b2a000000010cf800000006cf881a2bc10000a31d5318b054cbc1d0d1db80000afe1b880001d6d000000012fa11470000000109b00001df688640001b4a57be09dc0001ecc051a5f380000207000021b400004f42a546800916a3c01bc4921c38c2331281064750c41bf600000e845111446133000000000eee0c5a6cac43304120000527cd352b89520c00014701f4a4d7c9b7c000000000000000000000000007e1821e8dc2520400000000e7e0000000000000000a3e00000000000000000001af00002b660fd02cd194a00000000000000000000000d27000000003164000000009e4000161800000000000000000000000000000005c70c2000010f315ca000000008180000532600000001f3a000000000000000000000002f00000000000004e880004608000001f2b9e28e89f600000d7200004c844b4929c13d4abb8000000000000000000068700001ab0001228855e656fcd0a933f44d04940e5f0000315a9ca405788bc251e95cc4c28e081580a5b800029da079e0000000056b0000660c000049a000082e8490aa5d34c2445000000002cc0979d2da8000240800001c50000227600013c480004fa208c8660a9c1260a00000002bef433a00015b88000000000013b09f3d0000a8a800016fa000000000001689000000003e48bbf14a6000000000001f1600002fd000913d8976000000000d0a000111b80003c265f2000012cf0000000000014593d785f0c0000000005e3fc02430000000000000000000170c4708000019b00001928000000056b41b54000000000005bc85f78000000093f4db311da180ea8940e0aafd140855994068000067e07886418000514805b800023210000000000000000000000000000000000000000018972d0e4cc867d8000000025c400000000000000129482694388000000000000000000000001900000
  | 76 => 0x7bd0000205000000000f91387c00000000000527c6e9cda28f7b44dc00012c124002c680000fc90ea243d40be08172a51254672e8ca98000000000014cc0000000086f000000003dc88de898b25183a7609a0000095e00000000000000000000000000000050464bec000000000000000000000036fe23c0b8e80003df200000000000000000000000000151a28ccec90c44000033a90d987834cec00016008373091200000000000000000009d400000000a0d0000000018220001252009400000000000000000008be04bb9bbc0000000000000004d841c515409b7a03ba48c901600002882000017ea4d200009c6423980000000112c0000c7f000046d00000b123e0c4a681ba187e10ea84c8edf82a700004f58f1e000000000000000000000005d8000000000c340000000000028be04353370738365a00000000000000000001b400001da84008000000000000000b5f00000000000067c95f202b40000323043800000000000000000000000a7d09d70000adc8a37800058a8000104714b94008725400028d100000000000000000000000a071b35259400000000000510c4eb51fea7d00c98a5443b997452c6200000000000000084980000000542400013fe000003800000000039c45e0000000000000000000036c8000000052c9397056f120c12f000022e64c6e6fb80961e0b35f277140000000000000015bc98d500009efc26f0000219400001b70000251800000448000000004093e62ad50000000009029994e40427098e91854cfe8c2800020ce0000000041b80000000000108b000000ee0000cf480004dde00000b0172e0000ac0800000001a4a20c4fb8a3750ba8864d17609ab37940000000142600008d0c0000000000000000000000000000000000000000000000000000579c966000022792e4c00000000f6d4d2a9f70000188900000000aab0000000000000000000000000004a629f40000000006a8000383c00000000000000000013c8800000000a80a930000000009540001a454aea0000000000000005c9400000002020000000001e9000004942ee0000092600013678000137e0000c890f610c0c0000d5c88ab1b106430cab1be7438a8e3c816000000002590000000055f00000000000008803691054800031b2000000015d100009c14000000012fe4e644ee8000261a00012878000000000013081c393746000000018a80000000046812974bc82238a7711e7322272a0295a91900000001213166f00004368000070f1b40257021c83110000000156da47245d013d800021af0334695d429000000000001071a38c3ccc0f04000000044e0000030906f506ca46a0f40000056fa6ba0d6d942212a43d443d620c726dc70b93378a832e3c780000025fc00000000fe5800000000000000125b2f220000b2d
  | 77 => 0x500001cda0aa400000000f90a7448518000000000001e8284400005d2c0001d8100000000f23a483414487080001ce50b865308ae825f60bbc0288e9891cb00000000000000000000001599800000005bd516500001c4a00009118694354a10f80001dad000058e0f70044104e03200cee1cea10a689d000002dc40689b1400000000000a8fc000282227ce72644d728651ac226c16091ed1000080700000000000000010e60000000009f4f038d1152aa00000001a1e000000000000000093e0000000000000000000000000000000000000000000001c9c85a0000000092e00001c401eac0000ed09e890000773817800004baa8a10000000000000000000106638cc00006b480000000000000000000000000000014a14b406e7060f8000496000014d4000000005aa80000000000050444d880000eda79a40000000058e000000000003fc883344a593d5388e0000000000000000000000000000000000d1a0000070c3274000063700001d88ff48000376c9ef87ed185629740000000000000003218d36174d000000000002842000000003921dbc36b200000000ba4023224ec67080002e02755014d000000000000000137849ec00013af80001fe63c78e4b0000000000015db00000000000000000003d485cf8d2d0000000048ed3e4000000000000491000032b600000001add4dfe518c00001f53ce600001ea9d1c1fc25ac128a800016a886700000ebc572200005781ae44474859004b00001c5c7994bc1000000000000000069c000000000b98000000000000001915000000006dc0000126c0000000000000000000000000000000000000257918d80000961858a11be04e8f1185680000ace400000000000000000008fa0794605524ea590000056540001cc0000066c50201d5e32d41914000000000009c9000023a138842c0cd12a12b0000000000028e40000000000001350000000055d015c35382ac8000000046f800000000000182a00000000000000000000000000104aa098b680000000000010d3998c000054d450700002ac80000000135f00000001373238a50ce259402713362f886ab40000000000051702f7072806f00000c970000065c000015192b700000001462140600007cb482c000000000000c6f0000000000006de000000000000eb8800041de04c40000cb10f2800007638ba30ce80000eb48bd40000180c000057455ec00010ad9df33b34000000007e84d646a68ba32b8c420804883b30000000000000000000000000000000000107a000029929b00000000113380002a068188000254500007e0400000000000000069a1f1c03189f6c000120a45b480f00002acd2e1a0000000123f4f64000000002400000aaa4ab99b7c2cec8c3415fa9902fea9f9072e80000c429a382cf29af000000000000000000
  | 78 => 0x56000111215cc00000000a2d08ea49d0995000000001a66000000006ae529201c800026b6000021bc00000003f5e971c0000000322800000000000240482f000000002e20267c15d00000000594421080000000ae9c836972a0000000000000001af800000000408000000003cc00004e7c0000e03000000004c3d563000000003d640000000316e00008ea95d70000000000012c40000468000017e2000010d800000ed3a4639715268e1f015453c11d99e1d4b7ea34c000277f2e749af463924ce0000aef800021ee00003bc00001f1600000000b3f15a800002924000182e000006e00000000000004bc000231b1394000059e172f398a22280000a1a4a2e2fe400002d100008ddd476a8fd000017100000000421200000000ea1000029bc8cd0af30afa0814dab000000005b000000000000097c4f6b8000046600000002b3d47d200000000000000000009b498c34e700000c5000000000000000002ab000063980000000457e780531101c40000a010000000029d60000000000000000000f83a6ed000055e52518a873b220000c539d2c00001fc0e63860d0000a5cc000000000000000000000000008fe496380000000aa109de9fa9000000005c500000000000000000003732a9e40002a88307e8e50b968000000000006f00d4607e20000000016f4050a480000125c00003d240000000571a2284558aad7532c000000000004de40000d05000000000000000000022f854cd39aa0df00000000000099d1e9888cc46288090a5c6f303fc914c4d665b685ca8000000000000001df70000410c05698691ed657b00000000000000000000000095a000083b80000000a39c00023a200000000000164300008a486df8000000093cd06780000000000086b00000d0444b800028a20bd20000b3d800000000000000000000000000e301d5b351474980000000389200015b5800000000000e81000000000000ba0aa534bf6889912d8000000044f0000000000002ca8000046841b600000001d98000050a86b882082b840000eeb1f5f059a2fb40000dbe00003064000000046d60000494068e2c0c000000000002f4449f5207800000004ba0000000000000000000045e31ce37240000000425c56dc7ec95931c78198d50e0a980000000079d04d74ecc92000000000000022a4c591aa1557e7c1487980004df800000001d4d0000083ce4e1ab8000075c000000000000000000013ed1f404f38be300000000000000000002c329588b0909ce00009fd8000000022b243f40000000441600cc0000000000000015c92555477e000000000c83522000000000001cee0000000000024d800009982a4e10f8434000006ba15840000f480823000000015f6a3f400000000000209337820000000000000001234000000000001dec0000ea700003250c3
  | 79 => 0x6d000041ea000000024e73b3e00005af97ea000000000b0800055d0000000001570000000000000003fcc6784679a5ff0c7c211046504a13d8642680000371269a057892a81043758af6ce21a4692a1600000000000287c11748b700000000303c00025530000232045900000000ab08cdd92292260473800000004a362cc00000361000000000000d210000000000000000000000000000000498000160b80000cde00000000000000000013d4000003640000000032105b200000000c7800000000000000000005b481d880000000000140a0e3b06aa00003b7800000000000000000000000000290000000002704f709d301a6a000000000000000808c0001a0d4a405f6d1ca878200007a6c00000002dd20c5523980000000000000000000000809c59f925954a01f6000000000000000120a97584bb4668872d00002f7c13bc000126e095600000001ec533a641e80000dc80f4a7cf8000015300006b24f58959d00000674000000028ae0000fe796830000000000001c339e8ac9132c288448ca80b400015870f568e1450928bf00000000f7f00004b0800000000000000000000000000170a315c000041a0000000000008f4000000000000d1c0000000000020f02e3e203d47d00000000000000000000a2c407c00002da2874401800010642fa860483208a014eea00003b51b1700000000000102b52fe000000000000000000111080001f841344ba380000000a6a529b00003328094000012544dee00000000e9c0d6200000000000000000001c680000000000000013f81d127970000000050240000e7b8000448ca2843269390392200003ba2ae700000000eb4192154520000af68000000000000000000000000000001fb400000000fd680004f460000290a261536a9f195bc26c95842143c00018b800000000000000018060000b859331000078600000000000000000000000000000000000000487200000002ab71016000083804e41328657c81e80000000a86c00025a6000030acad5aa3d327c18747ca0000003c49ecc6390753d388e8cffa04d300642b0c1c61a52000000013cf80004e1a000000000000690917c4e58aff31e4000000018cd00000001262000033a0000000000000196334cd3800b900006370000000003ca000012523790000000000029fa5570000118900000000aa9907480000000000000010150000000000000004364000108d9c6a38ce2978000000013ea9bd40000000000095980c9830a00002aa40002c0f0000481d3020000159a000000022011c5a0000000000000000000000000000000000e258a8f00000000000000000000000d560d49000048700000278000000000000000000084a8213000000002da138300001b8600000000000000000000002628000000000000000000000009e500002e
  | 80 => 0x78f4000250828ce00011a3a5dc00000000000269b1aa000007f622ef00007aa8fdf800007460000f350000063c3b740000000000000000001009138a000092900000000000004b99392a520000a729fec081600013f98b37000097c85ec000000009f1c94220c93c224e1408580001b7410b0c950000383089ec3bc00003cb254dc00000000d020000a4a08ba19f86bd8ef20e90000000013f127570fac589871523dd0dba93c8000000025408588aee19500298000000029753c84000015e800000004894027a0ab399600000000000000028806ea13df25a600000000000000007d8000015d03b80000000000029d04d1cc93252d485400000000b0d00000000d6c94f30000709c000119e000000000002b3f0000550400000000000000125c87c40ece045c90984dd05246aa40001c71000051ac5c81c0f00008cf854a98cc000033b0000069000000000f1b939451580000000279d00006ebc000155b000000000000000000000012650000349000013570133390a89fc0002add587e405000d00000000000002815e80000aa19158914e0ad236b00000f2c08b4153134600000000803400028ce02460000dd20000332e87400000000431a000000000000000794c0001e7b2aa0269c0000000000000000001e8400000001073800000009fac000000000009d640001ed4000031bc0000845000000003182afa00004d3ccb927cf44308b2d24da67100000000000243e2fc200003df80000000a92800013eb00000000000178800004ed000018bd00005ab00000000496655fc000000000000000d07000004b81f9c6a400004edc00010390dd054a4000079699df000097440000000401800000000000000054c126889460c860000dba80001de6af202f110a929fa3d40ea21aa7060a089072607651e3e1e853f6087026cc84a00001982000000007ad09580000000000000003abe6510ca1897800009e30712250600000000e90000000000000877207453840000000227d00000000000000000009e5c000136b000047140001c4a2fe4000000000001b5c0000000000011da0000ab6a6ee0000000142180000000464d54c864e347e000000014550b7a0000000000000000000be812e6000079f8c1880004c147c2cc491b000000462855b0772000000012d728e54ee23768a29800051ae8ee92c980000000000000000004e6865a400019160000000000026120000000000008aa000060c0d8a140f3278000000006eb41c0000027d0bcb00007e406c88000034000007cc0000000000000001b0150dc00000000c660000000082d000000001afcf141b810000918ccb4072e11b400000001dfd175e00015980ab700000000000000048305f2c000000000000000000000036d800007142a3753349ee00000000000000000001d77000000002
  | 81 => 0x33ca60c00000000000000000000001058000056da0000ab9000055c40e10000000030e60000000000000000000000000053a400000002bd500000000000000011c200015c50cef049c000000000001aea854800005b500000000000000015040000000000000001d34df60f0c510600000001d030000a69400000000c02a50144b1f5700000000000000000001968000000045ea00000001fa5000000000000000000077f14d39f3211d69e70cf5822f4042525800017ff00e251088e4800000002ac000019f3553a6d80a0b9f6e2002752c00000002d280000000000000000000000000007020000506127f0fa24c093601f4600008eac0000000000000000000000000000000000513000000000000000432c000000011503876000000000004d1000000000437243e000039d9d2138327f0400005ad1456000000000000000000107100000000000108a00000000adcd2178000000038c0bdaa592000000013351dfe0000531c0b69abd0000201c000000034d000000002ba000000000000267200005b780000e96255e00011e30fa403e20000000204f4f3600000000c8c37900000000000000008a74f4891e50000a9c4d931d8c0000000016a027b0000000000000000000182c0000000000000000001e4900000000000000030e8000000000000000a51000000002e941658f2700003ca2000000000000000000124b800000008e4d5b513f639cc11a40000000000000000001eca3cc000014d1000040c20000000229a00003e645baa44c3868727c00000002f0c29b06828484000000015f400000000261c0000b4e41485c193b68000000000000000000369800000000b7b0000000000025655576000078300003a1a00010d60000000035480000e66000000013ab0ff500000000de1800001bc000098c0d30000000000002aff41200000000077629ea0000000000000000000a5a000000000000000000000000000000000000002a991149fb100000000a8e800051902c4c83400000d8c66f800015800000000006e99ac38d25554000174c000000004f014a60d4e10104fb25a719880000000000000009170f95800000004cbcf2580000000000000015a0154202188d197dd3848482c0000000000000000001b2700000000ffe80003d9c661c65b00000000000000000001b8a000145baba100008fa91051a3d194c0000af10ecb24320b294d200001a160000e6b873c320681c09f4137a000042bd5648ff900008b1c1718c7d27102f3c4e0276c2328552800003660000a7f4000000000006b413bf2297000000009b09acb000000006ea800045567be07b91d854b9c367d4de847d1dde379863daa33337e3ee09a126874c8688b8860082d000000003c48000060e5a291bb0174000096cce49080d000000005e110050
  | 82 => 0x7370ef6a601000000007a00b1013f4099d5c70913242c0000b43131a0000000054c976b42a07b6cc5f93d113fa2134a1722650c6c04ac0002ba514647bf03b0989c000000008e78bb851ee00000000c0d407e378d36f1d0a00001bbc2c790354ffa4bc0cf88287371a5afc61080000000000000000004c0600000000cbb0000000018d800046d400000000dde3e9c000000000000000956000000000000acb80001d080000001c5b79bbe2c3a0000999800000000000000000052748a44000000041c25710000047b087e28d8a5680000f1c000000000002294830800000000000a55d1898bff4dd424810978c63019821f43e1aa930000000000008611bec0000000000000008b3000000000000000084e8e4a35660000d4116c70000a1b433980001b0600009cd00000f26000000006520000ab58a0387b1000026940000000066c000000025b24b4221080001ab40000000000000003f30a89873d0000000029e8000187b2c7c00000002113560832c80000526000061001a38000000090188a09ce220ce722d322800000000000b8a14c3441a0000000017d3d1ea4789430000000056d48020000526a000000003bc3aae5df80000c5d0000000000002791e7a0000000000000008c9c7a19f3100009b9400000000768000000000004d040b7400023da00000000000000000000000b33a0b8191480d4000164b0d96000000026a7000000001b50000047c1b14000205d00000000000000000007d480001157000000005e90000167c2ad0b890e390000000000000004b9267946f907064af600015969de9000058e80000182000045080001bf02a440000c831f4009a85970f5ba7d92010a50818b805800006804000000048aca85000000000000984541f8030203200000000000256600000000b0c00005df52339ef600002de0000000000000000f698000257e08e55eb800021c60000b02051e0fc84d9492fa71800003e000f1800000000000000000000008968000000000000000000000000005e8d4d322d90000000148a143f00002d888cf80000d009c3149e9af0277606450c5ab58449203e90a58022000083b893393a3340c00000000000037c000016b22af0000430d37998f80000000000000001e462664000000042be9e3800980001752000000010ab0ffc0000000000021a409d12a92945000000000000000000070dc000263800006258e128000000000000000397000000000000fa30000a8c849e8bbc55de85ec1560bd04efa00000000000000000008ab03890e5a7c5400000002cfa9e14a4327a0000000000000fbb000000000001158000000014a410492e1ea04c000000000000000000212758880000b888000000000015b3800001600000000000000000000a808e5906680000178800045460000d9e275319240000
  | 83 => 0xcde898580000961505da44e4c9e0000fc58000000000000000b462cac00000000a2500000000b410000000000000000000000000000000000306488494ff000000000f3903987f7000000000000000000000000000baa000061b0000000000006190000000000000000000000016cc00000ad9cf23a986e287498000000000000000000000000015e59f1432480000000168b2322a53800021560f8a000000015ba00000000000000039da0000000000000002d2000026aa15f400005b700004fca1c10000153c524a7fe843b96fd4ec033d400002810d7a431434d22c500000000000210b00000000ca4270f000000008bf868322ba000000000000000584c4f90b55025a991933f0000000000014ee8000352c0000ef395e1000000000538000000000003a2000045e45704000000019fa00014730121000000540000000000000010f0a3b6477a67740000ce44d8c326054080000000000045e80000000000000026830000000000000000000000115d0000000007240000000000000005452c3e51220000000000000000b6c86c81562e6242ec0001fb729b000000000000249a668c000000000000000dee80000000000000000000000000000017ec00000000000000004360000dc200000000000000011f600001e2c00000000000000000000000f4830fd5af000000000000000003437280000d798000043a65f80000000000000009e680002a261d280000000000023e4e0e8000000017d400000002730000048e800000000000000000000007c400000000000000000000000000060b000023ae000000000000000326616dc37e00004db44d4400000000ef200000000b4217d6000000000001cf600000000000000000002e90da5238e0000f0d80000cee0000f0f8000549078d934b00000000262c95d24eb0000a764000017a00000000000000008a60a6400000003f6a4a54000000000006d5400000004a0a0000126aaf400005f8cf0180000000000000000000000000000000000000000000000000000000003a27bd179063fc000000000004534b041bc9000000000000000375c34a128f086a3e700000eec9346285a9ecc60310f200000000000200b00004a1c9d4800000000000d4a80004da800013012412563897f80000000000098fc4f200002f68000000000004280071898d80000000abe400000000000000000014d000004df000002420000806c25f13c22494699c65800000000000000000000000b11c0000000000000012e000002b34000093f000000005ecc0000000152800000000000000000000001a5d000000013a489fb0000000000000000000000023188870632576542c0000000090a45d300fe375458500000a690000a2690bb80004bc48f5c0000000000000000000000444421ec442a020000000000000000
  | 84 => 0x1cbc5ad92458cf00000000120f00000b544a90000000029ce63f050a0000000000000000000000009f811d1a10000000000000000000000000001c0000000000ca325c621f6542833b00454ae41e587839c0804c2acf86189d1e516a37455d4a382000000000000000000000001ba9de2000081980000000000095a5415194f000000000000000000000012bb800048400000000000000002118000000000002378000000025620000c50800001948f7800009542f020d08000188f00000000000097d00005d8400026fa2462a865439809f4122936072b91b553a67f687f280000000000000027ac494aa56c0002a4700009d3c9fd00001dee7fc122e9372000048f805f19d83d0400008ce0000000000000000000000000000000000000000000000000000089447a780001ed8734c25304a856fe3794f0800ea3b8e5a685da01b40e348f142608000442c00000001c2f3c6a0000000000000000000000000000000000f432296000000000000000565400000002449000000000000f974ede9a040000000000094c158592a948363e3c7b480003a0229ac00000000000000000000000000000085020d24e00000000000001f42000148893aa00008d94ef1a3e30000000000000000000311cdeb80002b0c93c46d7a22f0dac8fd4000185a553400000000000000068f0000164f000000004b9944e1c0856bcdc61fbb0000a531525909f00000000749000000003ffc0000000164a0c2000000000000000000000003700000000007ed00000000000000000000000000000015b60000c9b99ee3eea0000000000000004c8800000000000000000012ed0000000000006280000175c2bd882a3be8178d3941d5303008b6cbc207dd000000000000000000000009921c702efe7c0c000234512ae5b1000000003ac04b613290000000000013240000000007dc00010c8000000000000000000000000000000000000000000000000046f4000000000000000000000000008538000000000000000000000000000000000000018ee5d6c00012ea0000000016119fa000063ac0002a6b0000000000008434da6a5680000a6d000036d000000001cb0000000008e9000000000000ace000000d40000000000000000000e094244363400008b10000a03c469800000003f4400b2b4200000000f9fa4020000000000029e6000093d4a46a17f55505b9559a0b81387a1f9800000000000a3540001d0400005df00000000214e69c928b047200003368eec0000000000002b08000000082a953b0fac00008da000004900000000000000002084893923e03290aec91c014aa7780db844dc000000000006db468b97762466000059d907f012a0000e0a1e93499e17d13cd00000000888c0000000000000011501bf84164a4d020100003a5ea22554780000000664
  | 85 => 0x221024428328bc53fc00001c18ac780000f055152619862a0000000078c46be8e6c00000000aa018790000000038ba1d70000490499f00002de23211088000026ec0d600001d323e8295c514a068d3d92898cf1c0000424200000000000147800000001a5f1a260001342000017ba00000001c680000000000023053d32000149180001b4400000000a1c25ca00001bea08b00005e140000000000000000000101000059ac42a8000000000005dd000000009cdc00000000000000000000004564000048a08100000151800021f10000000161686e9000000011b31be30000000000023350000a0d47db25ee526e4b38ac62b5900007c3c000243300000000000000000000000de58000271600000000000301000000000000292e0000a9d00000000af791da800000002410cb5a1670000000000000003940026d24f80000000a42400002d74e2262e449e168e30b600000000229000000000000000000000008f900002bbe8c5d1acaa15075c000000017a5000026453c5a29b036a00000002b90000065080001c1b00000000000000024929af08ff00000000000000009d800000000c1190f52cdc1230000285738161764000000028e200000000000086655189a486b30404000000000000000000000000000000000073b000000000000a3480004a3e32b8ed58000000000000000000000000000000000000000000001aa2000000000000000463e701000000000000000139600004e9a0000e0e1257000011995d798d10000000076da1a618767f20d71800052100000000230700000000000258800007d80000195d00000000000217a116a000000016d50000000000000003136af840000000000089ad3d380005602590000000000000000000000002aee80dc2b1000000000000000122711b23a68ccc23531dc03e340002bd4000000002fb8a2a00000000a6d8bc342e620d000013bc556c34a901d0bec536400000001f300000535c67c000000000000000000052206848d110b1e1da613a405400001b820000cb98d620000000000028c046e00a2c0000000000041ec91c150f4e4e00000000d6e18820aa8ce08ec900006df80000754355c000110e000000000000000000052c2000000000000000000000021970000415c0002b832bf00000d8d80001656000144a848300006368000000000002020d29800000009dec00004d2000000009bb828c13a88584420800027dc81080000000000023cce64000004e432b09baa3b4000000012128000000000000000000000000000001d830000a86914480000000a270fbd92a5149e0000c4a29ca000051b40000909581881b000013f900004a44014a56f000049200d1a0b5000000000000000000020ec000000000000d100000000000000000001fc600000000000000
  | 86 => 0x4c4c0000f7857384eb0b4f95781a08562c00000000000000000024ea000000002f689e93c10000000013380000000000000000000aeb00000000000017b000000000000aa7c5019f560000000000014540000000000000000000000000000000000000000003771f6000015a802c921d2000000000003d34ab7c00000003a9000012a18214000011b06a68ca0124c000000016904d8e0e207da2a8c2a0e3bac000000000ea000147c8c9100000000000000000007d2400000000000000000000003176000043f0186000000000000000000055d47932805326887a414e00000000000151a0000000036dc00000000000000067413a52712921471894e63850000031600001e9c98c46ca84c4000000012cb1b1e014a00000000924000000004a2800000000f70000274e000095a0f97a65300006c7433617c03c1800011ae845c000000014a39fb322b8acb072094b100000e64000211f00007dd08d883f92faa00000002972053e000033c0000411eab4044d800058400ff5007955400000000000000033b4a730ee79be803e80000bc5024300c0012826c020009e28200fac843a0c140c340001ccc07ac00005429dc900002de4bc923553936000019da6d116daaa7148b9c7e319427593b2813000008f6088716ce44b024ac19c88a20000a62c0c52a3608500000b8c800006346778e6f800000009ef0df5996315d871b032b8a4a08288ce440980000000000000000004fd015a92a6a49a1a2000004db80000000000128184eb000000000000f3823f80030e8e800026e2000000021ae00000000cfe800026121d1c000024b000000000000000020a00000000000000096946cf1d0f20fc70b497016973dde000135c0000261600007b40fca3e7800003de8af200000000e8d800034ee2c1c96a00001e8aa2b80001b2100000000000000000000000000000000000000107117900001a280001b2000006b010b7215e00000000000000000000000e1d1d9008ae1561462a273000000000000000520643792af8ae80000089cb400000570a103c000048e00000000e8a80000000000000007ef04ea5ceca9b134b27d400001bf066b168a579c00029f80000160cf1004cf0b82000104b0000423257d810900000000af247be0000000000001d100000000576cb771f3b0af400000001b3b00000001358800000007e1c0000e1c3952880800000000000ab285c39f8800000cdc7001d6e4790738caaf0000000000011f913f24a58197800000000000652c000000000000000000228b0000000000015582a7e0000a4c9f9b00008b7c000000000000000000255d1538955923aa1dc2e920000f78ab5c2498ab6800000000000000158a8caa11d8412d1630000000045bcfad9c7c000000000001a4100000000dcd874217d499750cd25a33e2400
  | 87 => 0x8380000000000000000020a5d3244384400000000000000082f25ef00003c4c8b3800000000000000000033c822313a90a181a9600000000000000000000000a3a00e68998e2a80000000000160380000000a8c477d000008560fac3d00000000000000000000000000000002836000000000000000000093a400010990b6847dc2858000348e3ac1589161b000099e0000000000004500a4a800000000000000000000006a6148c000036200000000112f2484829caf502cf00004ad8bad000047fe0001385800000000000000000000002834000000058085828977800058220000f610000112200000000000169400000000ed62e2c00013652c413b9813b94f1213c00000000bae92634cd00000d5180003d4c000049f000051f8000089c0000430a00000001aea000026f000000000000000000000000000000028b8000000000000000000000039f000000000000000000000003208000000000000b9c6a10000000000000000e5d800000008660000000054600b1528a000048dc00000001b2f273e0000000000000000d7000000004f5400000000000000000000000306000000000001b8519a854f400000000000000000022b6000016f80000000084e000000023d925a204500000000217c0000508800000000000dad984100000000ef51e340000000000000004b78000000000000000a9787d51c214da4000000028b24cfa1d0444e000000009ab40000fc800003615312000015be08a0a6323cc0000a6040c4000000001f3800000000000000160a1416000002680000000000000000000000000061bc00000004c4a42840000000000000006688ec409f25f4d0ca9b3f2a2e875953e945e00005f64001a24d078a0000b3e150016443630c252b7042a684e00000000000097b0981969331e80ac507905860dce6110000000000004dec47b0000000054855f2800048da55c4000000035780001263800000000000000009c1aa86578e2425ab4d3207f08b1a8f6579872f5224263c2db000000000000000000000002799165c40dcc79ac2e009883d0031030f3bf45b4c00006d3157c9ec000021420000000000000000000a47400023a600000344661a175242433b80000a9652600000c0d000000000000ce7235100008b38000000021cc00000000c1c00000000ebe0000000048a088005a1158caa90000148907b20000b6eab373a9e90207378000301c0000000000000000000000065113200b985ec800000002cd000000000268000000000000000003873c0000114e0000000000000000000000000000000000ca0000000000000000000000005e511f280003a20000000016cc00000000951297800000000000123921d01ad4e6788e31872861913b8000225200002450bb11eee5368f5a84c80000000030480000000000062300
  | 88 => 0x4180efc00000001d0600012938000404c0000000000000008dfc85f80005676212c000000000000000effa358035656a81cdab3103b600000001fa80000662c4960000085a0000000149a32e00d9d34f80000000a9c8f2a0e294b6c93540002c562c3e0000716000023724a5932a9a5c055a99ac5ba05d632509b90000033c000000002d0000000003701107996412d40000000000000000000000000000005f44000000045c8000030c00a9422e4480bbb95b4315e1facd97214c000056f01c18000000000000000000495c00014970543324e0b5400011e631e2a1f424c00002580000120b108600000000395a3d20000597400018543044349048d2963000002788ce8000000000000000f5c0000727912a0fba2bf200011b88c23000096c53458000000017840f7832200008b250d680700000000000000000000000000000000000aaa80000000000000000001f0100000000000091246880000000022c41aa2fc94ac0ddd4a7014084f700004cc80000000025d0000000000000003ff0ae202caa4550d920e00c8500002312805922690440000000019ea51d000033c80000000155e0000000128b14b491ac0000000000070c0512000003980000e838000000000000000bb22f380000000000000000000eb60000000000000000a260ccc00012a4800032f4437c0000000183c1e3c15412f2000034804f7816a00000000d6a1ed5541a2558352868600000000000000051c638fc00013b839d61b4872412763fec438888a85e73336abf8fcb8817541c1f640001e92000000000000000000000000000000000089884d19df02f98aef40002bf403e4000000000001e320000cb08afd00000000c70909232ec0000b2700004af40000000000000004f055010ebb00001ea44289cb800000001349857304bc153443991b70ff602801a01c0a0bf6000000019d6021000000000c9638588bcc0000000000000009dd0000389e44c400009960000621014501a200000000000231400000064000000007ec646000025d921502a407aba4b6286e0000000000000000000fe2046433668a148148000000065143e5000011c8000000027b101d60001058800000000000c7a81df35003ce43989404316c091cc8b8b1b1fb05c1521a2ae4199090f40000000338490692809e8757e066382e4000000003c7457697b600000d487cf800000003950000194d14580000000047f000000000000000000000000001a560000a16c8621db90000a2c13f180000000000000000000c4a00000000000476400011b9109b05ea59c400006e42d868300ef012350000000000000000000000083e0000000000000002c5913d600000000d904758000000014620000572000000000000855400000000000000000012c2376a355d1280000056c0000000000000005
  | 89 => 0x850d3261751319c59a4000000000000000616885c393a000000000003b8800011c200000b929f54fc78000505a00000000000000000012fe800048e8a9654b30efd1f0600001111e8d3fc6747d4bd0f1400009d18e89000018600000e738000246c561472814c93148000072200f700005ca000000000000000000029c80000a3ac0000c270000507d07b8bc700000c4cbb800002a5c96f94e4a34e49565fe14630000000000010a48000414600000000000000011c0000000000003ec80001ac8000067e40000eb200006b700740000000000005aca015000000010be80000000aaf8c72800000001dd400000003b6c20a55c325460000000000000000000000000009320000000058500000000612c0001d2e082c90880000f93457a000011f800000000001403000000008c74000000012522600bdf85491a64000029f80004b12534c000006b294a02ec49f84e3000003c400022e5000000000002097157a95f400000004c5c270c40625b70cc07ab000000000000000000003182658000000000000000000000000000000000069d245e000000000000000000000000000000000000000000000000000008408e88490c00012fd00000000000000000003eca7a2c0001c44000000014c6aa8e000000002d120e854f40000439005100006fdc6b98b2d000092e87fb8000000000000000000191a2b640001b9d00000000000000018700c10000000005429ad14e69daf379c37e100d000000008b54c1200000000000000004bf000032900000000000000000008000524c0ea53f49bf31de2a64872d800000000000ded0000225600000001bed445676380000000318c0000000000000240000000000000000000ffb8a1d49f8000151e261d413cb168000000026765b808d29a322b12000000000000962930c00000001ac6000000000000000000075b18e30000000043b2c31000000013489fd40000000000019ca0fd40000000000024da3d800001d37231c0000d8529a1000053a400008d20000000000006350ec00880000000000000000000289b00000000000202f0654abc800014f90000000000004253fea8d287f904811a0e874401680f64a64108829c84e249ae6afc0000db5000000000000a58509000000000000000027540000000036c000000000000000000000000003bae00001860dfa00002b9000024232f62600ccf181e0000000000000000136400000000000000000014f395cf43ba00000001bf50000000000000000406a3b022f91cc00000ee0ce68000000060cc0001f2c1170000000000004a26063840c8911525200000002492000014d40001000584e00000000000000000000a100000000000000000000000000000010414902a7a0a4819b000008b0c498027100009378df0042e15ca01a400000001c6600000000
  | 90 => 0x9c84000000003709d362eca45cc8649eb61df02f440000000000080f800000000000646c0001ba813f8000049b80002904000056b00000000000000000001116ab84da025e1054427fd1b7a39f0000a4a80c48000059c000000003c213daa4040000cd530ee0000000000000002c00049178741504e5c57f00000000000003f800000000000000034b00000000e470a464bac000117b8000000075580000c3e0c54000008e0e0200000000000173800002fb800000003f1a1dac000000050601354000000000000000000000000000d04000000027ca0000dda00000000000000005a321f07e44351886e15bc00015fd0672345c55841e6879200009c6d54d9f721288606cba813cc02b02178f05161035dca4b4bfb8063009a3a600ed086232567888b8988b4000079c888d1a44062046e06252ba225208ad0fae8000153cb0cc79f8000000000001e42619393000000000d00454e1ae06ec99ec0dfea240a1890591b0c94f40000cbf00001c349668000000046b800000000a9c000043c800000000000000000000001370000000000000000000000000003cf90e02a4648a80000094159c3b7000000002a56212e003c00028490ed86fd115ba361000015dc6f3a0b326fc86281cf05520f0c0001248134c00000000a76811e32106b88a779dd11a7c000022480002d2c000000000000c0a000000000003b66750cc2b8000000000000002beb000034500002bb20000110c000000000000000302000010747ba44ce211200000000c83800000000000000000026549ead03180001bbe848d18800000dc000012e1098f0000000078d80001cce00015a2225e56a29688d1500f3242a00003c510512998000000025210b228ab913886f10000000000022820000000000000002f4e9c5c3bf86de0000359c00000001bc85f7c3bd0000059800000001d0031f44354727a86600007b400002b21042a61d8000000000000b9444b9cb6000093680000d4012a000000000000337a0000000169932b06ac40000000000000009f1ac39000000000000000000027a00000d8e0000000000018db000063e400013de0b6c00000000000000000000001e6728c000000000000000000003320c7508e800010999be9000000000000000000025e4000000030b200013660000000000005678000000000000000000442817bd575800000008390f0a03a515e2000000001480000000000025634eb000000000000567000000000000000000000000000490800005b61d52416e6a6d0409a19390684c4000075c4c000000868817000000000a86285400005ea000000002bca0658a5f07d2000000003b20e61438eabb54fe1af8000000000002bd8555e13dcceba6510000215d45288d109544ce53880a23000000001360000000000010608000103a34f0aa780000000
  | 91 => 0x2b9b0000000000020050bfe000160280004648434c8af00004a1a73b060080002c9464bd4c1000030080000fd9278a000000002e5800036644a2400021681ce431a4563978e31167ca813580002c56893c00000000000000000024470000000061480000000007d4f780000000a4900000000000000015cb8000000000000000da70000682d62906d157ce06a43ababc00a080000551000047480000b3c21b638ba975c2de1ad232383a100001085274e072cfad2bb700000000000000024120000e5580001ad80000adb000024ea90ac000138e000000010261f350e200000000072331547b71548a0360000000028900002eb8000108000000000000161c00003626a5c00001a8620a066a4db7ab63173486ac0000000000000000001362000092b4000288b01885d5c8a8a1fb00000000000000000000000000000011b000015bb2260048a689c000159000000000c5800000b128114dd10bd5409000004d300003dba77b8d73000017e878fc5ae292f00007f9d3d115271828000000000001104000000000001a6c92bd6118000000000000000000000000000000000000073ec0000000117eaea0346067b00001ea024880000d6eb02d3af25e02e402e7d5a7233c335c3af8d4490d800008af10b194dc0000020c8b2800000000001103901e000089e800008a540882d9c53c800000009a741f6000025048254be6936d000000000000000000000000000000000000000002b11186c7360cc4a62d0a504fc40001a900000000112580000000a7941e58000265c83e87350000098c64c80000000000000007b20ae2338aad4800018824a9400000000c74000014f8e0829eb4488466c4db138123f087b4a2690e045a20001115000020f224655fe853300000000000000000000000000127a408c3fac3e9890328a40000000000040ce000000000000000000000000000000000000000003ea03bb0984000005fc47bc0000522000000001c5800000000000000292800000000000000000000000bf200004fee000092d1bd43a2c46ad36e00003d7600000001208141e00004a523602f929baceb217a40000a5a800000000000874c0000000000000014f68000000000005b200003a8c3fe8000000000000000000000000007904000133a000000013958ada000000009e5899a2cc21e7433e8c500000000000010fc00008a4d61100000000321ca471f9a00003cd800000005754000000010ff4abc000000025003f8a00000000115496e00000000000000000005c885cf48740000928a69000007e38d10800000000000000035d2d56a6c53f30000261835790a680001f1400000000d2e000000014bea0130eb440a895600c017c000000000000497ca3e14558c6e0000000069780004c36a0605fb8000000000006a22c1a4a560000f37
  | 92 => 0xa10714e720000caa80000000000158000ef0000000000019783c040000f7f8d7e17666294779000000000000000000000002f8d4ea2bf235483d7d1f000000e606bec6c1000000000000000000000008650000000000006d040000c7620ba000000000001b7a00011560000000000007de00000a1000005c900000f6c7ca4000000045ae000000000003a74000000003e50000a5ad2b50000076c00000000000000000000001a7e208a00008868d2900000000797889a457000005778000297e452c27980000000000041b00ff34742948a2da59c0000000154b80000000705c0000000005c37c00001e0d3aba942c00025f31bd44b7403d1d3f4fe439594b38000000000011ce0db622d000015508a742e3800000000000164248140001724266a06fc8ec16b103c215d402a06db1a2c6bd4a9000001c2832cca6227090000374cf0916cd1a7e000090704cd075a0000000000000000000ad205640f5e8c24000000000000000000000008ea063c3a916a827400000000000013422e300000ff40000000000000000000af4d4530000000000012698e1030c07acc2148000372c000095a80ec3efe000078b92850000000000002633276000044c0000371e0000bff0a1755a664792229c0e12aa00900001c7344a43d340000000304a0000b4d800015720000a28852f02e2878c00025310000b14400016b40000000104500001098108c0001ee62ee471c800000000000075000015c3000000003220f3500000000000104800000000000052c3c94219c3db94882148000008000000000000000000002f344200336a52342d6000123b800027a00000000285f035c952020f0000000047e40000000000001b4000000050328f280000000000000000000b1a00000000000000000000000000000000005db000000002b9a00002cd86f72ba879c4000072200006530a8b000000004b8c000000013185008c3596a600000000671ac4000006cb00001fcd2cc42e700001a40235e463c23285370000159400003e2020e000000015a5034c91f40000000000000008d99d9c00007ca0444807b0000767560b000047064490ee9a43f000046008c5a44b00000000a580000023690b0c5a022d00003fa000000000000000000027bb000085e00002006000000000001bf93322000000000000000326c2c08ba5356e7a74a9226654e8694dc00009e552b2574912b22e23d7413e00001df2000000000000f2400000000000000000000000db700003b6800000000000563a0000000000020e458e4ac21d1a3b6229d8000000000000000000000038c8000000007590b8a00000002642000007f400008b000000000d47816b0000a630000000000000000000000000000001029000020622ee55a499fc4b0c000000015d8000000007ba800000000000535070e000
  | 93 => 0x786fbcfdb1ee343542430233800000000000d3d800000002a740000000447e0000ad600fc00003e10e828d2d10be00000002a623f4eac50e3d02e1000028580000a15000068ac0000780162e55f00000000486491c40001cd1565e12f54859f11288a2a912c014202ee800005f49d3d000000000001b64000076253540000508e000000000003cea224800000000000000000013454b2a0000000000000000000f50804b061c01852f580001a72000076327b648ec000000000002e780ebc8f1000000000c083ea800000000000000000000000000000261500000000000000000000000000000020c40000c100349157642d54e38000000000009b200000000000000015bb2a6213f44ec956a3c5e00014ec000000000000b2c0000092a0000b3b80000000000000006070000603c0708000479c4c94133044f000084200000000000000000000000001a70fc4ff16201dec000000010360000000000000000000a6ed25400000000000000000000000000000000000000847011500000000ade8000000000000000000000000000000fee871c46506120847000058aa0000d8ca39700008bfd343119510043060000000000007b6800022e9000023ec00000000000000047e80002f7a33ac000000042e0a1700000000000000000000b4f3f7c8cb40000bd61a187dd800018dd00003b71271800000003664000000036a60000000275a171c99c12019fff0b2ead8400000001b640000dd09e7730fe00000000000000000000000000163e00000000f15000003e4000000054420000f8d02130000000000027a6000000000000000000037f44e4285a00002e108ec80000000051c0001d95000000009398b06000000001118000000000000000000000000000000000533a947032b233309d4000000000001d7000000000000000000000000106530e0e1400004a735540f4800000003ffc00000000000093a21911ad146600000000000000000007e4c00000000000000077524410000a2a800000001daa00000001e6113520000e59824843a869b8a1a0bde023a052c434000000000000ce01f7a00000000000085823c08c3144697082f82a810000000000000000f9b0a3f0f60000000013930000000162284c243aa000000029f5223e333000000004e6051e10658bcc45844bad1678b0e11e41005333095f4ba4ad2c199900c0ab20e0902c0bfe0c2a8000f518ed12118a37c000000000000000000253c00d800000001da912f8487800024070000000052b228d22f646042d9a75c00000000e5228ca000000003061e6d00004e78a141efb32ae07b95468000000066750c6232b00005280b382bf337e439ac00021580000000000018780b308ce8000000054d000000000000110c0000f2e8000000032e0ccb05b13b603848c061bcf2b3e000138
  | 94 => 0xd5800001083f0061ba05700001ee0ed91f940000000000000000000000000000000000000000024ec223c273cc62800000000000000126f0000a6f0000213d3c7400011efaa3b555866bc3729182365037d50f42a6d41ec8accdf21bbb498400008708000202e0000000103b00000000f470000000076a00000000000000000000000000000000000e7316fc28f44302bf500002408016037905602dc000000004d4c6628000258c08487858b7a17bc00000000000079b3ca07650000070700006548e090000000000000001f0e00000000cfa0000000000000000d1b0362807428880000000ac0cdff97b04406000000017c7108e0fc0c878000000000000000000449442c8000267c53000000000155c3aec8718f76a3bb033c00000000000000000000000ce000000001104800000000000000000000004458653a6b50000000156180003fe43b20638859230ca00000000000384635300920c200000446540116ad4c58adbcfd1245b00002e0c8851c7600001ab554a00003648402c03e191900000000000000000000000000101a000000010df80000000000000008693e26281858c8000000000012089691562693ec00026084ffe0000000000000000000000000000002be118c000000000000000000000000000667000052be4edc0000000410493580002a7c4afc0000000000000000c7c00000001416000000000c2000000000000b6100000000000108b000094fc9a18262000000012682c1c0000252000012e14f747968ff28f0f22fa000004992a70000000000014b356980a08a0500000754327000000001bee00000000000000025350120000000000000001f7e00000000eba800000000000000000000000000a2e800000000000000000014000000000273d0000000000000e308200000d1b00000000000046019590000000000000000000247883e8000212a00010fa0000069c000000000002224000000016cf508a4664000003b000074e0344081102b26b9c021aaa30000609c000230326e64b04af789f30df679f030724ef0b9a14043478fbd46520000000000000009f1000007cb3ed266d00001b36000066900000000000000000000000000029fc491800021820000000000000005eb00000f7300000001216800000002f34d148dcd06a2b054d358000000000000001b230ef83cd00000000000018a4000000000000000095211e32fe0000000000000000000000207d00003b5c00023911f0e12c0000275418f22ce14c71e334b68331828194751d2a047d553800000001a4400018f7000052ec00026291e529b74d21882f377290f04808b97029cb074000000000000000c0b8000000000000000000162c0000000070a030e0000000000000000000000000000000000000000016e25d3840da154000022b93032ade21
  | 95 => 0x38058fc00000380000000000000000000a4cd1072a5f00003dfc00000005444000000013dc1ed400000000b60115e0000da40000511e07588db0000000000000000f9d0ee0acd800000001dc615000001807000077e0c130000427244e400000002166148c3a00000000000001978000168800000001e054cc600007d41ddc18165801385287516825cccb2906550000000046e23b81a3e500cecf233730c645acd6a9895000036c161e0000000000013a400000000000058580000000000000000000000000000000000000073c00000004500000000000000000000000000001148000000000000f765160910a6f400000000f63922e00000000000000000003fed5600ed9407600005ce80000264139c0000000000059cc000140146ac000000029f2000000003619da627e60000000000019a000000000000502e3254000000000005580e0a800006d213b486ea461404a0000c1c00000000affc0000000000012e40000000370c46200000000053c08ec0000000000037b40000a1b000000000000000000000013742a38000000004f8990b561e83b0ff0826507fc0000b719b6800000000000000000000000e369ab012da19700002b4f000000000002227545a7a280001f4c2a38000112bab932aae5a940000000000030100002559150c4d480d280000f0a000000000004f923aa40002c5700000000000000000000000000000037848d88fbc8000000053c936c800054c8442400000000000465869100000c2c292c15b9ea9000000011a580004bba000016c000022c0000000000003dbe00000002b65000000006870000000000000000000000000000000000546a193c000286900000000f3a000000000000000151103a400000000ce746220000000000047123ee40000000000008d018020081cc06358d638b2300007d90000000000005be40001ee72edc0000e069bc000005ee06d0800000000000ae7000033700000000000000001ce4000000000007284168000041f87430000000000000000bf9a381000030280000000145c51200000000000000000000000000048751ff0863000000000000be10000000141622d320c60000be2800011104a4800014d52db8af88eefa83d00001ecc00000004d56b0194c89ecb0000628c0000000000000000000000000000014751c0534b6a3c10d095393afa54a0062889f17ea00000000cc9000000000001bea093867a80002b0d4d9c3221255168d1e0823a074380001024122c00021d90000a68023c00000000000000015de00002734000231a428c6cdd1a31a422e0851b05a18f3123e69100da911101f56233800012e71184af7400025c447840000000000023a000000000477020602e868196161594000000024b500002500aa299301dbe0001065000007d00000000000000000000f
  | 96 => 0x40c0d3000000000000000021390cf000000000000000000040ee000032e8f0803e600008ee0000000000003f4950e0000816c00000001c2e0000000155254e0000000000000000000000016c800002864000124f00000000a6a21b108127ac800000001a14000000000000000000000010ad41189bb1495800000000000000000031560000d37a58e4c5649c48dd00000000105d17680000000000000029ec0000274c000201000001a749e20000000009252928000000000006c588c91f7eac1434c8df11d56155075a80000d800000000154840c051243fa8000016e9e18000215d57a4588c000071e000000000000000000081544da9f550000000000000000000000000016e10000000000020c6000000000000000000000011cf000018a4271c2a584b404b46c2c000054550d60000e7a80004f24519111a800048f61ef004e8000275e5084000246837305d0958d8000104e00013f81e15000000005ee15c0000076a80001fdb0e582eec8e1976430c20ba400006130e90000062600004a4488946ed9c2000000000000158f2a56448c2d816ef3d8ca3d00002367000051000f380000000000119e9740000020fc00000000000281c00026a90478000066380000000228c00003ba2f2000008ad800000001a9000000001cca5ff40000000004200000000bf110ca86a0d669ef714c069c400025df00000884000000039e05e2c000000009c03024000000028ee0a20761000000000000142000000000000000100a00000000e3a968400000000000000000000000000185c3f3c16ed1b70000095c5c600000000543a7ec12ae00000000000090680000d765da8207000000000000000000015503a440000e1b000000000001cbf278e0001357a8b633a80000000000040440000cce29312e9ead040001b9f08ac5f9cda19a764d28449c8b219d52bcc0000249000051500ba06248a6e38065b0858a0c991da00000a828b4900000000000000000000000000000025fa33fca5b000000000000e9aa9a34c2e65dcdd910f0334c4d6865f11070000522c00024892ae80000ea3806a00000001558a52600000000dc880000000000000000003e6e8704c6909b91ef2000000000000000a7140000000000000000000000078e1c540000000000000000001981000000000001d8d50a20000000064000000000dd680000ed200000000f810fec1c014bf0da800000000d5f000000003aa867280000000a054000000000005d78000218349c28a30f1900b558920000bcf800012ba23e15fb2c19051c0000e28a9e04ed696b4000000000000000de9a3080000611c0000000175639d1502917012dc62055599c8f3a842d4cbc0000000008c08000000000000000000000044da827400016ec00007f586f080001ac80074e6e80263ce0730c00000005
  | 97 => 0x504297e497f800000008568ebd800025c400000000000000000000000a2730fa189c00005855000000037304fb000000011f7000026c67140a418d5a000000003dd1a164ada4318349a6f1000030911510000000000000000000007e4880000253b369a00002dc00000000961c1d222e70000000135600000f5c0000000000043fe00000000000000067e00000000000000000001b6a2ec40001247800000000000000000008769f0000000000000062c07200003050000000000002044000000003c91dd0798c67b80003af211f80000000000085a8000000031f60000000000032525bfd18700001d180000000000000009e0c000000000000000499800054ca0000830000000002a2c85c80001f20000000000002708000000000002f2aa27c0000000000004fc32a0a9a1bfc6de00001514000000000000000000000000001aa800008ba800021410000000117e01a157b800000001b04000098bceb9000000005af080180002f7219a4000025200005a8081d27f43c12000116e000053a0000000000000000000000000000000146873caa871e6600006c98f3c00007ee522880000a8ea46800024ff000058f00001aca15ba54540000000266e8224af48000000000011d48e99000000013a82a7800000000000279041ba6d9c000000002a08e00000000000000000d8387490e980000000000000000000ae280000000610800000000ee22580aa890d42cc600000000000533800000000175000058240000000399ca6780000000000000003a78000000099012d50000000000000000000000000013d08000000000000000c601fde69d02e0050d000000014e7000023a6000000000000000000000000000000000133a044c3d72839400000000000a0cc00009cc0000000071b13fc00000000b0c0000267873b81f00e8a000010743a580002a646a315fc161a000077513518000394a30b026801810a2a3460afdaa7356ea0bb43fe04c70000b13c31181d100003f90d0a254e367210187cf09970e7e559d27803d80000000000000000000000000003de3c8a2648000210c000000014dd00000000000000019a70000600400000000000000000000000000866c4c700000000568c7e8000004146320000230b096ca230b9aa6751caa1f7c00000004fa4a1fd51780000cd0000150784f0421a0000000000002d054649408c1d205ea8f80000be400000000000090f000096f506f07330000000084b1382498a22640000a2d00000000000087f00000000759800000000000000000048cc000128386a92e0eafa9435000027e8000000000000000af8158c80110000722038ea5b90000000073f9ade222e279d3e50000000000000000000000000014b88af741e2000091322170b5835a0000000000000000000104000000000
  | 98 => 0x80000000000000000000000000000000000000555c0000c468000000000000001b1f000009180000000000000010ef00004cb4000081f863900000000000000000007b10000000007987f288a2a494263c0000000216f000000000001d3e0000000000000000000000000001b000000000000000000000000c72068b00006b313db87a700007b64f7a9f42000058d4000269e2af6a2742bc83120000035810b833858140000000122b0fb49e355678ff612ec562153382564ea20001480000000000e806b687fd000000014060000000000000f500000b94521c5a91f2442d20000000000000005e980000aea154e0000000001000000000000135d24e40000000000000000001625800000004ec8b4a91a645fc00000000000297a00000000000000016e400015b02b0690ecaed0d79191e08c40000f5e46f6326800017894ab6a484cf78000000000000001a0400007930ab4a7cb58360000000000000003b38654102112ea000000000003ec400000000b403afe68440001eaf0000000000000000f20a18400000005400000000009c435da480c1f4a05446608d9098087113f0600000001a462b7c84690fe28a74f6823800000000000001052cf9fc92cd480c946d1b080000b13800000004db0a200389000018d0000141b8cbc55c0000000000004072000000027253f3e3f7d03e0c67000085d800000000000000000000002cbe4ba400015ae000000004ef8000000032e4e4989470000527000000000000000139522dd46c67f4403299650000000070780000000000025c0000349a0000000000000000000000000027c008d800007f10a88766c76900001336905c96e04ec52ee8580891000007e62eb8000000000000000000206541fcb094bcc175227fe00000000000000000000002b5d307400005399c4e00006244000000000009c980000000000000005f40000000000002ed00000354000000000000000000052196a730c400001bd0000000000000000000396a0000cd0a94a03501f1c74f80c134720000ea2905c00000000000000041cc0000cffa51a472c071d2fc0c551d00ab3000023be1fa4000057a8883318449e0000000000005fb91e200001be80bd00000000000000000002774299e61c0000000031bea4480002c103b840000000000000000000000076e2fe885295f700000c400ed4e0480000000000096800003b440000000000000008e9400000000f8251f5285239038a8a24c0000000000000000000000125c02002b180000a1c0000000000028960db400000000da015b552206d71aa253f854b8aa31e24335c00018ac000000000000b73000010c80001ada47d800002df87ee0000000000000000f1a000000010cf0b160000d36a0ff000090150dc00000000000000000004c1e000088180002514169800002b2
  | 99 => 0xae8cd890d980000000137c80000000000142c8000472461c8feb979712a222f87c92be4008c0000358055e0000000000000000eee0000000000007dc0000dff00000bf00000000054a27d8150916216ca1fa6963c0001cc900000000cae00001d864f20827808c3ed65a881be000024960000459800056a86bbc00002be0bcc8d785fb0acc345e0000000000000000000d8b17da30326de4000000000000000000000038be19240000b353e4e89208090611253c0000000000000000000000106c0000002000000060000590490a000026ac00000000a08000000000002bab000066b4000000000000000beb8000262249880000a484f26000102c94143b1e70a40000000000000e415e2a4939c08fcc06c23c94bd2000122d027a2c4e000000000000000000000000001878496012c00000000000004c00003310a4e400000000000000000011ea03d800000000000000035d8000164c00001ffc000000051fe0000caa00001aee000000017e9000000000cf82fc52ac878077100000000233d4f7000000000000000000055b061b80001b5e00004fbc000000000009cb45c69ec1000020580000000000000005a814d900000000f1d924500006c700001a3800000000000000000000000000000004a2687c000050c31800000d6c066a1bac00000000000000094900002763000000000000000000000000000e26226a73fc0000000000081ec0001d495306736c3df0a1f34943fc40000000000000007aa800039460000000010e00000000000000000000000000000000000000000000000000000000213f0000000000011493cc40000000135c0000a02cee300005006528c0dd80000000000149e000025421b28000000012f400000000000122a000000000000c4c70e00002733295600008e6837600006f841f6a82e27ee3f74000002034fe00009890000340a1188000000000000000000000000000001258ab1a00001c2400000000000000000000002c2a4e4553f1a9e0000000000008c607300000ffd81ce2f18000000000000000000063d0394000009fc00011c02be000007940cdf3b902c54da3000020ac022813217f9571628f80001b4210b4051
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x863554185300432b298c2980219554c614c010ccca430a600866552185300432bb2e6298021c5553314c01087ce9328600843d749943004237394ca180211b5ca650c01087ce8328600843d741943004237390ca180211b5c8650c010c6aa9308600866552984300431aaa2c2180219594d610c010ccaa4b086008659654c0300438caa26018021d2549300c010da2c2980600866565c872004392aa64390021179cf65880108bae7b2c400845d7598e200430f2a4c7100218755263880108beeab1c400861e5458e200430eaa2c71002117dda53880108baed29c400845f7654e200422ebb2a7100219398e5288010c9ac7294400864e6354a2004326b1aa5100218d5526188010c6aa8b0c400866552586200423bb8eca900218d9536148010c6aa9b0a400865653d85200432aa9ec2900219994b6148010ccaa5b0a400863654185200431aaa0c2900219594c6148010caaa630a4008666521852004332a90c29002199d972148010e4aa990a400843e74994200421eba4ca10021179ce65080108bae7328400843e74194200421eba0ca10021179cc65080108bae6328400863554984200432aa9cc2100218d5516108010caaa6b084008666525842004334b2a4010021ca5512008010e92a690040086e161480200423abaec9880211d5db54c4010c6ac8aa6200863676553100431abb2a9880218d55263c40108eaea31e20086355418f100438aaa4a788021c555153c4010c6aa931620084757518b100431aaa0c588021c955252c4010e4aa8a9620087455354b100423abb4a3080218e5965484010c72caaa420086596594e100432cb2aa708021c65515384010cd2cb29420086696554a1004394aa2a508021d254d52840108f2ed28c2008671659061004338b2a83080211d5d365440108eeeab2220084d4735911004272392c8880211d9db5444010a6aeb2a2200863765951100423b3b2a8880218dd915444010c6ecaaa2200863676551100431abb2a888021cc1c154440108eaeb31a20086355498d1004273394c6880218d5506344010caecb29a20087155494d100432bb2aa688021c555153440108eaeb312200863554989100426b39cc4880218d5506244010ccecb2922008725549491004333b2aa488021c95515244010e8aa6a92200863554d8110042793b68088021cc5534044010ae2ea20220085d17310110042f0b908088021cc5523044010bc2e518220084f0764c11004398aa26088021b418d3044010e62a910220085d17388110042783b24088021cc5512044010dc0c4902200863b65951100431db2aa88802196d965344010cb6caa9a20087195454d1004335b2ca4880219ad955244010e52a8a92200874953549100423d3b4a288021cc5525144010ae2eba0a20084f27610510042793b462880213c9da2144010
  | 1 => 0x2104332b2ca590821c955252c8410e4ca8a9642087255454b21043a329aa590821d154d52c8410ccec8a9642086656454b210431aaa2c1908219a5496088410c72a9300420865953980210431caa2c0108219654d6008410cd4a4b00420847774594210423abaec8108213c5c364084108eaedaa0420853575950210423abb2a8108218dd915408410c6ac8aa0420863676550210431abb2a8108218d55263084108eaea31842084b57418c210431aaa0c6108213c5c06308410e2aa929842087155454c210431aaa4c410821995966208410e4aa9310420853574d482104392aa4a4108211ddd95208410cccc4a9042087255454821043a2a9aa410821cc55260084108eeeab004208635545802104398aa2c0108213cdd56008410ce6eab0042086735458021043592a2c0108219c5516008410d62a8b00420863154580210436929ac010821b454d6008410dc4a4b0042086e152580210431b32283280218d59141940108eae2b2e800853571553400431b2a4c3a00218d55261d0010caca730e8008655539874004333294c3a00219954a61d0010c6ca8b0e800863554587400432b29ac3a00219554d61d0010ccca4b0e800866552587400431ab2a83a0021c594d41d0010e2aa6a0e8008726525074004392a9283a00218d55261900108eeeab0c800863554586400429ab8aa8a00218dd954150010e2ca6a0a800871553505400439329282a0021c954941500108bce7b28800845d73d944004237396ca200211b5cb65100108bce7328800845d739944004237394ca200211b5ca65100108eae2b28800845e73194400422eb98ca200211b9c865100108dae4328800845d7598c400430f2a4c6200218755263100108beeab18800861e5458c400430eaa2c62002117dda53100108baed298800845f7654c400422ebb2a6200211b5d66210010c5ca9310800862d54988400432729cc4200219354e62100108deeab10800862e545884004316aa2c4200219394d6210010c9aa6b10800846f769484004236bb4a4200219398e5210010c9ac7290800846f765484004236bb2a4200219398d5210010c9ac6a90800863554984400432b29cc2200219554e6110010ccca5308800866552984400431b2a2c2200218d5516110010caca6b088008655535844004333292c220021995496110010caacb98e600871554cc73004237396cb180211b5cb658c0108daeb314600862e5498a3004316aa4c5180219394e628c010c9aa7314600846f7558a30043172a2c5180218b551628c010c9ca6b14600864d5358a3004237bb4a5180211b5da528c0108deeca94600846d7654a300431aaa4c3180218d551618c010caaa6b0c600847771d95300431b2a6c2980218d553614c010caca7b0a600865553d853004333296c2980219954b614c010c6ca830a60
  | 2 => 0xa52082199dd95290410cc8eca9482084757614a410429aba0a520821559cc5290410aaae6294820873154982410423bbaac1208218d5516090410e62a8b0482084f3755824104339baac1208219cd516090410d64a8b048208671545824104358aa2c1208218c5516090410da4a6b0482086d1535824104371292c120821b85496090410aace7aa2820855573d5141042b3396a8a0821595cb5450410a6ced2a2820863765551410429b3b2a8a08211d9d85450410a6ce82a282085567315141042aab98a8a0821599c85450410acae42a282086355418d4104278b80c6a08214d9d35350410a6ae9a9a820856672d4d41042b2b96a6a0821555d65350410e2ca929a82087155494d410438bb24a6a08211d1d95350410e2ca8a9a82087155454d410432a3b2a6a0821c5d915350410a6ce829a82085357414d41042ab398a6a0821599c85350410acae429a8208635541894104278b80c4a08214d9d35250410a6ae9a92820855673d4941042aab9ea4a0821595d65250410e4ca929282087255494941043a329ca4a0821d154e5250410e4ec929282084747654941043932a2a4a0821c95515250410e8ca6a9282087455354941043323b2a4a0821c9d915250410a6ce829282085357414941042ab398a4a0821555cc5250410acce4292820863554d81410431aaa4c2208219594e6110410caaa73088208666529844104332a94c2208219654e6010410cd2a5300820863a54580410432ca9ac0208219a54960104109e6e0b26620855573d53310431ab22a9988218d59554cc410c6cecaa6620863576553310429aba6a7988219559653cc410e2aa929e62087165454f310438aaa2a79882195d9153cc410caac8a9e62086355498b3104278b84c598821c955252cc410e8aa729662086656554b3104392aa2a598821d154d52cc410c6aa8b06620865953582310431caa4c0188219a54a600c410c72a8b00620865a535803104334a92c0188211ddd1650c4108eaebb2062084f170d90310423abb6a8188214d5d6540c4108eaecaa0620863764550310431ab22a8188218d9d9540c410c6aecaa062086355498c310432ab2cc618821c5552630c410a6ae9a9862087155494c310423bbb2a6188219598d530c410e2aa8a986208635549883104392aa4a418821c9551520c410e8aa6a90620873154980310423bbaac0188218d551600c410e62a8b0062084f3755803104339baac0188219cd51600c410d64a8b006208671545803104358aa2c0188218c551600c410da4a6b0062086d1535803104371292c018821b8549600c4109e6e0b26420856572d53210431ab22a9908218d59554c8410c6cecaa6420863576553210431aaa4c7908213c5c263c84108eaea31e42086355418f210438aaa4a7908219559553c8410e2aa8a9e420853574d4b
  | 3 => 0xce65508108bee6b2a840845c73595420422f398caa1021175cc65508108baebb1a840861e54d8d420430eaa6c6a1021175d46350810c3ca831a840861d5418d420422f3b4a6a1021171da53508108bceca9a840845c7654d4204327b1ca4a10219318e5250810c9ec6a92840864c63549420431aaa6c2a10219954b61508108eaea30a840863554185420431caa6c0a10219a54b60508108f2ea302840845e73d94420422eb9eca21021179ce65108108bae7328840847571594420423cb82ca21021179cc65108108bae6328840847671194420423d380ca21021175d66310810c3ca9318840861d5498c420422fbaac621021879516310810c3aa8b18840845f7694c420422ebb4a62102117dd953108108baeca98840864e639484204326b1ca4210219398d5210810c9ac6a90840847575984420431aaa4c2210219594e6110810caaa73088408666529844204332a94c2210218d9516110810c6aa8b08840865653584420432aa9ac221021999496110810ccaa4b08840847975980420431caa4c0210219694e6010810cb2a7300840866952980420431d2a2c0210218e5516010810cb4a6b008408659535804204335292c0210219a549601081087ce932e640843d74997320421f3a0cb990210f5d065cc8108eaeb30e6408635549873204332a94c3990218d55161cc810caca6b0e640866552587320423cbacc1990218e55260cc810cd2a5306640863954583320432d29ac1990219a54960cc81087ce932c640843d74996320421f3a0cb190210f5d0658c8108eaeb30c640863554986320432aa9cc3190218d551618c810caaa6b0c640866652586320423cbacc1190218e552608c810cb2a7304640863954582320432ca9ac1190219a949608c81087ce932a640843d74995320421f3a0ca990210f5d0654c810a98e4a9a640854c73549320431aaa6c2990219554f614c810ccaa5b0a640847575185320431aaa0c2990213c5c0614c81087ce9328640843d74994320421f3a0ca190210f5d0650c8108ece2328640847a7019432042a6b94a619021535ce520c810a9eea990640854d754c83204327b2a641902193595320c810e1ca8990640870d544c8320431caa2c1208214d5d36590410aace7aa4820855573d5241042b3396a920821595cb5490410a6aecaa482085567315241042aab98a920821599c85490410acae42a482086355498e410423abb6a7208214d5d35390410acce5a9c820856572d4e410438aaa4a7208219598d5390410e2aa8a9c82086577654e410432a3b2a7208211d5d85390410a6ae829c82085667214e41042b2b90a7208218d55262904108eaeda94820853574d4a41042ab39ea520821555cf5290410e4aa929482087465394a41043a2a9ca520821999895290410e4aa8a9482087465354a41043a2a9a
  | 4 => 0x3cc8b1ea40861d6458f520431ab24c3a90214b9d35294810a5ae9a94a40854e73d4a52042a6b9ea5290211d9c664948108bee6b24a40845c7359252042a739ea929021535cf5494810e4ce32a4a4087267155252042a7398a929021535cc5494810a5ce9a9ca40852d74d4e52043872a4a729021c35525394810e1ca8a9ca40870d5454e52043a238aa7290214b9d05394810a5ae829ca4087255418652042b338cc92902153dcd6494810a98e6b24a40854e7319252042a6b98c929021599c46494810ad4e0324a40856671d8e52042b5386c7290219358c6394810acce3a1ca40856571d0e5204237bb287290211b1d943948108dcec21ca40846d7610e52042b33888729021595c44394810ad4e021ca4085697010e52042a739cc129021535ce60948108bce6322a40845d73191520423b388c8a90214b9d36254810a5ae9b12a40854e73d8952042a6b9ec4a90211b9db5454810a9ce7aa2a40854d73d51520439338ca8a9021c99c554548108dcec2a2a40854e7315152042a6b98a8a90211b9db5354810a5ce9a9aa40852d74d4d52043872a4a6a9021c35525354810e1ca8a9aa40870d5454d52043a238aa6a90211b9d85354810a5ce829aa40852d7414d52043932a0c2a9021c95506154810e8ca630aa4087455318552042b338cc8a902153dcd6454810a98e6b22a4085647159152042b4382c8a9021539cc6454810a9ae6322a4085667119152042b5380c8a9021599c66354810ad4e131aa4085647158d5204326b18c6a9021599c74354810acae3a1aa40846f7650d52042363b286a90211b9d843548108daec21aa4085667110d52042b2b8886a90215a9c04354810ad2e021aa4085657418552042a739cc0a9021535ce6054810a5ce8082a40852d7404152042a739820a9021535cc105481087aed2a0a40843f76550520430f2a4c629021875526314810c3ca8b18a40861d5458c520422ebb4a629021879925314810c3ac9298a40845f7654c520430f322a629021875915314810c5ca9310a40862d54988520432729cc4290219354e62148108deeca90a40862e645485204316b22a4290219398d5214810c9ac6a90a40863671990520431b38ac829021879926314810c3ac9318a40861e6458c520430eb22c6290218b9926214810c5ac9310a40864e639885204326b1cc4290218d5926114810caac7308a40863964980520432cb1cc029021179ce65d08108bae732e840847571597420422f398cba1021175cc65d08108ece232e840847575987420431aaa4c3a10219594e61d0810caaa730e8408666529874204332a94c3a10213c5c261d0810c6ca8b0e840863554587420432b29ac3a10219554d61d0810ccca4b0e840866552587420422f39ccb21021175ce65908108bce632c840845d73196420422f39ccaa1021175
  | 5 => 0x87167155253042a7390a929821535c85494c10e2aa830ca6085567199253042a7b92c929821531c96494c10a9ce4324a60854d7219253042ab388c929821569c06494c10aace3b14a60855a70d8a5304326b10c529821539ca6094c10a9ae5304a60846e721915304236b90c8a98211d9c46454c10a3ce9b1aa60851d74d8d53042a7396c6a9821535cb6354c108bcedaa2a60854e72d5153042a6b96a8a9821c59c65454c10e2ce2aa2a60845e7615153042a7390a8a9821535c85454c10e2ca830aa6087155418553042ab38cc8a982153dc96454c10a98e4b22a6085547159153042ac382c8a9821539c86454c10a9ae4322a6085567119153042ad380c8a9821559c66254c10ab4e1312a608554715895304326b10c4a9821555d06154c10a9ce5302a60854d72981530428f3a020a9821475d01054c1087aed2a0a60843f76550530430f2a4c629821875526314c108beeca98a60861e6454c530430eb22a6298218b9526214c10c5aa9310a60864d5398853043172a2c4298218b5516214c10c9aa6b10a60863671990530431b38ac829821879926314c10c3ac9318a60862e649885304316b24c4298219398e6214c10c5cc8b10a60862d64588530432731ac4298218d5926114c10ccac5308a608639649805304334b14c0298211b9ca65d0c108dae532e8608475715974304237390cba18211b5c865d0c108ece232e860847575987430431aaa4c3a18219594e61d0c10caaa730e86084f170987430431b2a2c3a18218d55161d0c10caca6b0e8608655535874304237394cb218211b5ca6590c108dce432c860846d721964304237394caa18211b5ca6550c108dee4b2a860846c725954304237390caa18211b5c86550c108daebb12860862e54d894304316aa6c4a18219394f6250c10c9aa7b12860846d7518943043172a0c4a18218b5506250c10c9ca6312860864d53189430431aaa6c2a18219554f6150c108eaea30a860863554185430431caa6c0a18219654f6050c108f2ea302860846e72d944304236b96ca218211b9ca6510c108dae5328860847571594430423cb82ca218211b9c86510c108dae4328860847671194430423d380ca218211b5d66210c10c5ca9310860862d54988430432729cc4218219354e6210c108deeab10860862e545884304316aa2c4218219394d6210c10c9aa6b10860847575984430431aaa4c2218219594e6110c10caaa7308860863654584430431aaa2c2218219594d6110c10caaa6b08860847975980430431caa4c0218219654e6010c10c74a8b00860863954580430432d29ac0218219654d6010c10c3ca931ea40861d5498f520430f2a2c7a90218755163d4810c3cc929ea40861d6494f520430f322a7a90218759153d4810c6ce3326a40863671593520430f324c7a90218759263d4810c
  | 6 => 0x1442b2b94a720a211ddd95390510aace729482885557394a414423bbb2a520a2155dcd5450510aa8e6aa282885677255141442b2392a8a0a211d9d85450510a6cea2a282884767694d414429aba4a6a0a21599ca5350510acae529a82884777654d414423a3b2a6a0a214ddd153505108eced29282885357494941442ab39ca4a0a21555ce52505108eeeca92828847476549414429bba2a4a0a21ccd536050510e66a830282884f27518141443393a8c0a0a219cd506050510ce2a830282886d2731814144368b98c0a0a219c94c6050510ce0a630282886e2721814144370b90c0a0a219c9486050510ce0a4302828863665504414432c29ac198a219a14960c8510c6ea8b0e808853475507404431b32a83a02216c1c141d01108bee6b2a808845c735954044237b92caa02211b1c96550110a68eaa0a808846e72d953044236b96ca982219514f614c1108bce7b2a408845d73d952044332296c2902218d5935484110aa8e6aa420885647255210442b3394a708221559ce5284110ca8e2b1ea80864e6398b5404326b1cc5aa0219398d62d5010c9ac6b16a8086647158b540428f39ea92a021475cf5495010a5ce5aa4a80852d72d525404237b92c72a0211b1c963950108bee6b14a80845c7358a540429b38ec72a0214bdc96395010a58e4b1ca80852e7218e5404296b90c72a0214d9c46395010a74e031ca80853671d8a540428fb9ac52a021471cd6295010a3ce6314a80851d7318a540429b388c52a0214e9c06295010a3ce6304a80851d731825404297390c12a0214b5c86095010a3ce7b22a80851d73d915404297396c8aa0214b5cb64550108dce431aa80846d7218d540422f398c4aa021175cc6255010a6ce3b1aa80852f7258d5404296392c6aa0214d1c56355010a70e0b1aa80852e7218d5404296b90c6aa0214d9c46355010a74e031aa80853671d89540428fb9ac4aa021471cd6255010a68e2b12a80853870589540428f398c4aa021475cc6255010a6ce2312a80853a70189540429b39cc2aa0214d9ca6155010e62e130aa80851e73181540428eb98c0aa0214b9c86055010a5ae4302a80843f76550540430eaa4c62a021875516315010c5aa9310a80862d54588540430f324c62a021879916315010c5cc9310a80864e639885404326b1cc42a0218b9916215010c9cc6b10a80864d63588540432b31cc22a0219558e6115010cccc5308a80866562984540432cb1cc02a0219a58a6015010c5ca9316a60862d5498b53043172a2c5a98218b55162d4c10c6ce3326a608636715935304317324c5a98218b59262d4c10c5cc8b16a60862d6458b530431ab24c3a9821479d35394c10a3ae9a9ca60854e72d4e53042a6b96a7298211d9c66494c108dee4b24a60846c7259253042a7396a929821535cb5494c10e2ce32a4a60
  | 7 => 0x8a0c21595c85450610a6ce9a9a830853574d4d41842b3396a6a0c21595cb5350610a6ce829a83085357414d418429b3a6a4a0c214d5d35250610aace7a92830855573d49418429b3a0a4a0c214d5d05250610e62a9b02830873154181418432ca98c098c218d591540c6108eaeda98630866952181218431ab22a810c212d5d063086109e2e0318430847576d48218421f3b0a8a04210fdd95410210c6ca8b0881086355458440842a7396a7984219394e628c210c9aa7314610854e72d4d308422f3b0a69842117dd9530c210a9ce7a96410864e6394a208432731aa510421539cf52482108dcec292410846f76548208431ab22a9884211b9ca63d51108dae531ea8884777158f544422f39cc5aa221175ce62d51108eee2b16a88864f63d89544432631ec4aa22193d8c6255110c98c6312a88865463d855444332316c2aa2219618f6055110cd0c5b02a88843f76550544422f398c02a221175cc60151108dce4300a88846d72180544423ab8cc9a9a2193d4d6294d10cccc4b0ca68866a62582534423aba6c2a9a2117dd95314d108eae3320a68846f725905344236392c829a21535ca6314d108dce5300a68846d72980534423ab8ecba1a211bdc965d0d108d8e4b2e868847671197434423a3aac3a1a219514d61d0d109e0e0b0e868846e72d964344236b96cb21a211ddc56590d108dce532a868846d729954344237b92caa1a211b1c96550d108eee2b2a868847b705954344237396ca21a211b5cb6510d108eae3b28868847970d944344237390ca21a211b5c86510d108ece2328868847a701944344327a9ac421a219314d6210d108e8eab08868865753584434423c3aac021a2196d4d6010d10cb0a6b008688475719935244326b1ea5292219598d6194910cb4c6b04a48847574d855244237bb2a4292211d5c664149108bee6b20a48845c7359052442a6b9cc429221179ce60149108bae7300a48847571d97424422fb9acba1221171cd65d09108ece232e8488474755874244332292c3a12213c1c161d09108bce7b2c848845d73d96424423bb8acb21221179ce65509108bae732a848845f73595424422e39acaa12211ddc565509108f6e0b2a848845e73d94424422eb9eca212211d5c765109108f2e1b28848845e73194424422eb98ca212211d9c465109108f4e0328848864d63d484244326b18a4212211d1d56110910ccea4b088488478755804244335a92c0212219a14960109108eae3b2e648847970d97324423ab8ecb192211e5c3658c91087ee8b2a648843c74595324423bb8aca99221539cb534c910a9ce7a92648847771594324421f3a0ca192210f5d0650c910c9cca990648864c654c8324423b3acc2192211d1d5610c9108f0eab0064885577355241442aa39aa920a2159dc95490510ac8e4aa482885667294e4
  | 8 => 0xe52880208f2ed29440107315450620082373b6a8900411b9d85348020a5ae829a40105657114d2008333b2ec29004199d946148020ccecb20a40104e4765052008333b2a8290041c95514148020a9ce728240107295490120083d0a0a80900415a5d63048020e90a698240105e0714c1200823d3b6a890041725cf6248020e52a921240105cb7350920082b5baa64900419cd976148020ce6ca30a40106736590520082783b282900419cd954148020e62a8a0a401056975885200833930ac1aa6210fdd954153108beeca98a7886726158053c4237394caa1e211b5ca6550f108dee4b2a878846c7259543c4237396ca21e211b5cb6510f108dce4328878846d7219443c4237bb2a4296219c9856014b108bce732a858845d7399542c422fb9acaa1621171cd6550b108bce7b28858845d73d9442c422f398ca21621175cc6510b1087ce932a658843d7499532c421f3a0ca196210f5d0650cb10a6ae9a9c83885357414e41c429aba6a520e214d5d05290710e62a930483887315458241c421f3b0a8a0e216c5c35450710e62e1aa283884767615141c425b3b0a8a0e211d9db5350710a6ae929a83885377454d41c423b3b6a4a0e214d5d25250710a6ee8a92838843f7655041c4358a0ac020e21179d8534c7108beeca98638846e7614921c4237bb2a410e218d55261d0310caca630a61886665218520c4338b0cc1aa4211bdc963952108d8e4b1ca90845f7358a548422e39ac52a421551cd6155210ac8e4b0aa90843f76550548432731cc42a4219358e6215210c9cc6b10a90864d63588548432b31ac22a4219558d6115210cccc4b08a90866562584548432cb1cc02a4219a58a6015210cd2c5306a70854e72d4e5384237390c8a9c211b5c86454e10a9ce5b1aa70845f7654c5384338b0cc029c211b9c865d0e108dae432e870846e729964384236b94cb21c211b9ca6550e108dae532a870846f725954384236392caa1c219394c6250e10c9aa6312870846e72d944384236b96ca21c211b9c86510e108dae432887086596398352842a739ea529421179cc6454a108bae6322a50854e73d895284237bb2a4294219c5866014a108bce632e850845d73197428422f39ccb21421175ce6590a108bce732a850845d73995428422fb9acaa1421171cd6550a10c98c7292850864c63549428422f39eca21421175cf6510a108bce6328850845d73194428421fba2ca994210f1d1654ca1087ce8328650843d7419432842a6b94a619421535ce520ca10a9eea990650854d754c8328427838ac019421559cc5490610aaae62a483085667215241842b2b90a920c21599cb5390610acae5a9c83084777654e41842ab39ea520c21555cf52906108eeeca94830847676951418429b3b4a8a0c218d9da5450610aace62a283085557315141842b3390a
  | 9 => 0xae3324a61046e72191530823b388c8a98411d5c46454c208f4e0322a61045f7654c530830eb22a6298419554d6114c208ece3320a61047571990530831b38cc8298418d5c66414c20c6ce2b20a61063571590530830eb24c6298418b5926214c20c6cc9308a61063564984530823aba4c2298418d9916114c20c6ac8b08a610656635845308333312c2298411ddd16114c20c72c9300a61067161980530823b38ecba18411d5c765d0c208dce432e861047671197430823ab88cba18411e9c065d0c20c6ca8b0e8610635545874308237394cb218411d9c46590c208eae232c861046e729954308237b92caa18411d9c46550c208eae232a861046d7518943083172a0c4a18419394c6250c20c9aa631286104e970189430823b38eca218411d5c76510c208dae4b28861046e72194430823b388ca218411d5c46510c208f4e0328861046d75988430823cbacc0218411edd56090820c98c7292841045e73d94420822eb9eca21041879516310820c3aa8b18841063654584420831aaa2c2210418e5526010820cb2a7304641054d7254c32082a6b9ca41904153dd5320c8208eeeca88a21063564544510832ab1aa2288414d5d36590420aace632c82105557319641082ab398a920841555cc5490420acce42a482105727015241082b3396a7208411d9d853904208eaec29c82105367414e410829aba0a72084117dcd65504208b8e6b2a821045e73195410822eb98caa08414d9c654504208daebb12821067151181410829bba2caa084155dcd6550420aa8e6b2a82105567319541082aab98caa0841599c86550420a6aebb22821047676951410829abaca8a08414d9da5450420c6ced2a2821053676551410823b3b0a8a08414d9d05450420aace62a282105557315141082b3390a8a08415c9c05450420a6ce9a9a821053574d4d41082b3396a6a08411d9d853504208eaec29a82105367414d410829aba0a6a0841595d76250420e4aa9b128210725541894108398aa6c0a08415c5d46050420ce2ca3028210731541814108370310c0a08411bdd562cc42087ce832a621043d74195310832b31c83280419558e4194020c6cc8a0ca01063564506500832b31a83280419558d4194020c6acaa0e801045e73d96400822eb9ecb200411bdd56290020ab2e728480106376550540082acb9ca0a0041cc50650500208bce7b28801045d73d94400822f398ca20041175cc6510020c3ca8b18801061d5458c4008316aa4c4200418d9516110020c6aa8b08801054e72d4f300828eba0a798041555c453cc020c9ca7314601064d5398a30082a7396a698041569c3534c0208bcec29a601051d7414d30082aab88a6980410f9d0650c02087ae8328601045f7654c3008237baac4180414b5d053c8020acae229e4010725545072008236bb4a5100419398
  | 10 => 0x67051980314833828ac018a411b9d764c85209d4e131e429046e7518f214833332ea390a41591d541c8520d4ac8a0e42904ce73983214833828cc110a419cd446048520998e6b2242904e8705912148275384c690a41591d54148520d4ec8a0a42904ea7518121483353a8c090a413a5d06048520dc6a230242906e0511812148371208c090a41b85046048520a6ae22a680904cc7358b404823b3acc3a02411d1d561d01208eaeda8e809047576147404829aba0a3a02414d9d541d0120a68eaa0e809055973152404829c3a2a720241729cf6290120ad4ea31480905687550a40482e439a85202413a9db3290120ad4eb9948090749530ca4048339328a3202415c9d64190120ae0eaa0c80904e876486404822fb9acaa0241171cd6550120a6ae22a28090535741454048333b10a2a0241991885150120a6ceaa0a809053475505404823d3b0a8a0241565cc5450120b62e22a280904787654d404833432c84a02415a1d54250120cd0caa1280905c87350940482753b664a02415a9d73250120cd0cb9928090668650c940482d4ba064a0241d254c3250120ce0cba8a80906706514540482d8ba0a2a02415c9d64150120ce0cb20a80905b17490540482b83aa82a02419c1954150120f4484a0a80907a1425054048399baa82a02416c9d54150120b60eaa0a8090730755054048399b2a82a0241cc1954150120e66a6a0a80907315350540483d139282a0241e85c94150120f46c4a0a80907a06250540483d199282a0241e80c94150120f428390a80904e87648540483d0a0a42a02411dddb51101208eaeda88809065663d44404832ab1ea2202419998b5110120ccac5a88809047776144404823abb0a2202419598c5110120caac62888090666621444048332b10a2202419314d62cc120cccc428e6090665621473048333316a3182419958b518c120cccc428c609066562146304821fba2ca982410f1d1654c120c9aca192609047675d85304823b3a8c2982411d9db514c1208ecec28a6090750514c03048354b248590241721cd42c8120ae0eaa0e409065663d46204832ab1ea3102419598c5188120caac628c40904ce73d92204836331ea310241b198c5188120d8cc720c4090564755062048352b228310241b198d4188120d94c7a8440906a964902204836531c8110241b298d4088120f4282a04409045e73983540822eb9cc1aa0411b1c963950208ece231aa8104757118d540822fb9ac4aa041171cd625502087eecaa0a81061d5458c540831aaa2c22a041879916315020c9cc7310a81064d63988540832b31cc22a0419558e6115020cccc5308a81063664584540832b31ac22a0419558d6115020cccc4b08a81065a63980540832cb1cc02a0419c9866015020ce2c3300a81047671993530823ab8cc9a98411d9c66494c208e
  | 11 => 0x482b8b86c7a8a411d9db43d45208eaeda1ea2905677250f51482b239287a8a411d9d843d45208eaec21ea2905667210f51482b2b9087a8a415c9c043d4520ae2e021ea29055673d8b51482aab9ec5a8a411d5db42d4520aaee6a16a2905547350b514823b3b085a8a41559cc42d4520aaae6216a2905727010b51483a299065a8a41559cf60d4520aaae7b06a29047776544514831ab26a828a411d5da54145208eeecaa0a2905577355051482aa39aa828a418d5905414520aace62a0a29055573150514823abb4a628a411ddd95314520a6ee8a98a2905347454c51482b33ac8428a41a95924214520b88e6a10a2905e270cc851482b33a86428a41d154c3214520acae5b20a2905567319051482aab98c828a41595c86414520ae2e0320a29056572d8c514829b3a0c628a414d5d06314520acae4318a2905717018c514823b3b68628a411d5db4314520c6ac9a18a2906356450c51482b3b928628a41591c943145208ecec218a2904757610c51482b33908628a41595c84314520ae4e0218a2905717010c514829b3a6c428a414d5d36214520aace7b10a29055573d88514823abb68428a418d5924214520aaee6a10a2905547350851482b9b828428a415c1c142145208ecec210a2906356410851482ab3988428a41555cc4214520ae4e0210a29057270cc851482b8b866428a41d14c832145208bce632e829045d731974148333316a3a0a419cd4660d05209d0e0b148290666621464148332b10a320a41559cf6590520aaae7b2c829053574196414831aba0cb20a41995c86590520aaee6aa482905547355241482ab398a920a41555cc54905208eced29c82904757694e414823bbb2a720a411d1d95390520a6ee8a9c82905347454e414833232cc520a41991956290520bc0e0b1482906666590a41482b23aa8520a41999954290520b88e6a14829056675cca414833332e6520a41789c33290520cccca1948290745530ca414823b3accaa0a414d5d26550520c6ae932a82905577359541482aa39acaa0a415cdc16550520ccae432a82904767695141482abb9aa8a0a41551cd54505208ecec2a282905567315141482aab98a8a0a411d9da53505208eaed29a82904777654d414823a3b2a6a0a414ddd15350520a68e8a9a82905367414d414829aba0a6a0a41599d66250520cc8cb312829056475589414833232ac4a0a41711cd6250520bc0e0b1282906646590941482b23aa84a0a41991954250520e48a8a1282905c47350941482b33ae64a0a41991973250520bc4e19928290664650c941482d2ba064a0a41d154c32505208bce6328829045d73194414823b3acc220a41999885110520ce0a330082904e87058a3148333310a318a419918b514c520ce6a2302629043e74194314821eba0ca18a4199988510c520ccac42886290
  | 12 => 0x29a418ddc76454d20c68e3b22a69047671191534823ab88c8a9a41875cc6454d20c5ae4322a69063671191534831ab88c8a9a418e5c06454d20c38c9b1aa69062c64d89534831bb26c2a9a418d1936154d208eae9b0aa69063764185534831a320c2a9a411d5d06154d208beeca98a69051c7454c534823b38cc829a411d5c66414d208ece3b2e869047571d97434823bb8acba1a411d1c565d0d208ece232e86904757119743482363aac5a1a411d9d661d0d208e8eab0e869047875583434823b38ecb21a411d5c76590d208eee2b2c869047471596434828eb98a921a41471d15390d208ece3b2a869047571d954348237b92caa1a411ddc56550d208e8e2b2a869046c72195434822f3b4a6a1a41171d95350d20a38e8a9a869046e75d894348275386c4a1a419394c6250d20c9aa6312869046d72d94434823b38eca21a411d5c76510d208f2e1b28869047771594434823a38aca21a41179cc6510d208dce4328869047671194434823ab88ca21a41175db5310d208d8eab10869062f545884348327a9ac421a419314d6210d208eceb308869047475584434823c3aac021a418ed516010d20cb6a6b00869065853580434823b3acc3a12411d1d561d09208bce732c849045d73996424826739ccb21241535ce6590920a9ae62a484904ea7098e4248236bb6a7212411bdd95390920a58e8a9c84904e870586424826739cc1212415a9d46090920c3ea831a849061c5418d42482373b0a8a1241535cc5450920c98cbb1a849064c6518d42483273a8c6a1241935d46350920d1ea831a849064e5418d42483262a0c6a1241a315063509208dceda9a849064c63d4d42482363b2a6a12414b1d15350920c98c6a9a84906c863d814248365b18c0a12411b9d764cc9209d4e1b26649046d769533248236bb0a999241535cc54cc920a58e8a9e649070c5490f32482a63aa87992413a9d660cc920cd4eb30664904e974983324828e3a2a719241179d8534c920a9ae5298649045f7654c324828e3a2a6192411b5da540c9208daec2a0649054d7315032482e4b84a6192411bdd9530c920a58e8a9864904cf7654c32482c63a2a61924172dc1530c920a9eeca98649064f7654c3248387ba2a619241531d1530c920e18e8a98649050c7454c3248327b22a61924193591530c920e8ee2a9864907447154c32482a7b82a619241d2dc1530c92099aeda18649054f75d0c32482e4b868619241335d8430c920a9aea218649070c5410c32482e4b8086192413a1c1610c920c6ac9aa6a2905577355351482aa39aa9a8a418d59054d4520aace62a6a29055573153514829bba2a7a8a414d1d153d4520b8ce7b16a2907245450b51482e239a85a8a41789c332d4520e8aa6196a2905567319351482aab98c9a8a41595c864d4520ae2e0326a29056572d8f51
  | 13 => 0x60d0620cb2a6b06831045e73996418822eb9ccb20c414d5d36590620aace732c83105557399641882ab398cb20c41555cc6590620aace7aa4831055573d5241882ab398a920c41555cc54906208bce632a831045d73195418829b38ca8a0c419394f6250620c9ca631283105567399541882aab9ccaa0c414ddd16550620aace632a831055573195418829abaec8a0c41559cf5450620aaae7aa2831047676951418829b3b4a8a0c418d9da5450620e64e12a2831053676551418823b3b0a8a0c41559cc5450620aaae62a2831053674d4d418829aba6a6a0c41c59525350620e2aa929a83107176494d418838b2a2a6a0c41c55515350620e2ec8a9a83105367414d418829aba0a6a0c41c95536250620e8ca7b1283107255418941883a3298c4a0c41179ce65106208bae7328831065953980418832ca9ac020c419394e62cc620c9ca6b16631065953d81318832ca98c098c419694d600c620cb2a7b02431065953181218832b29cc3a04419554e61d0220caca6b0e811065553587408838b29a83a0441c554d41d0220c9ca7314811064e5358a40882acb98a920441965965390220cb2caa9c81107195454e40883a8a9c8320441d454d4190220e2ca6a0a811071553505408823d3b0a8a0441565cc5450220e36c8a9a811071953d0540883a8a9c82a0441c654d4150220e64a8a0a8110751535054088399baa82a0441cc1d54150220d66caa0a8110733655054088399a9a82a0441e494d4150220e62a6a0a8110791535054088388a9a82a0441e8dc94150220f40e4a0a811045d7598c408822fbaac620441175da53102208beeca98811064e539884088326a9cc4204418b5516210220c9ca6b10811064d53588408832b29cc2204419554e6110220c6ca8b08811063554584408832b29ac2204419554d6110220c9ca7314611064d5398a308832729ac5184419594f614c220caaa7b0a611065653185308832aa98c2984419394e620c220c9ca6b10611054e73d532088326b2ca7904419359553c8220e8ca720e41107255450720883a329a83904419659653c8220cb2caa9e41104767198f544823ab8cc7aa2411ddc563d51208e8e2b1ea89045f7358a544822e39ac52a241531cd6295120c3ec831aa89064c63d89544832bb1ec2aa2419518f6155120caec630aa890654631855448333b10c2aa2419c187605512087eecaa0a89051c735505448327b92c62a241931c96315120c9cc6b10a89064d63588544822f398c42a241175cc6215120cacc7308a890655639845448332b14c22a2419598d6115120caac6b08a89066562584544832d31ac02a2419658d6015120cd2c4b00a890672615805448338b0ac02a2411d9c664d4d208eae3326a69047671992534823ab8cc929a419958a6194d208eae930ca69047774586534833930ac1
  | 14 => 0xeda9c83905c47350a41c83a2a986520e413a5c86050720aace732a83905557399541c829bba2caa0e411d9da54507208ecec2a283905567315141c82aab98a8a0e411d9db53507208eaeda9a83905377454d41c829a3a2a6a0e414d9d05350720a6ae829a83905c47358941c82f0382c4a0e41c91514250720b88e6a1283905a5740c941c83a2a9864a0e419c9946050720bc2e430283906e26218141c8274b94c198e410f9d3658c72087ae9b2c639064d5398a31c8352b228390e41781c141c872099ce730643904cc7359121c8274382c890e413a9c26348720d4ec8a0a43905357195340c826639ac5a06414d5c65450320c9aa631261906565318530c832aa98c2986419398d62d5220ce4c3304a91067161982548821fbb2a82a4418d5516115220c9cc6b10a91064d63588548832b31cc22a4419558e6115220ccac5308a91063664584548832b31ac22a4419558d6115220ccac4b08a910659639805488334b14c02a4411d9c664d4e208eae3326a71047671992538823ab8cc929c41559c65494e20aaae32a4a7105567115253882aab88a929c41559c66494e20aaae3324a71054f7259253882a6b90c929c41559c46494e20aaae2324a71055a7019253882ab38ec529c41555c76294e20a9ae5b0ca71055a70186538828f3a0c129c41475d06094e20aace2304a71055571182538823b388c8a9c411d5c46454e208bcedaa2a7105567195153882aab8ca8a9c41179d85454e20aace22a2a7105557115153882ab38cc8a9c41555c66454e20ab4e1322a71054f7259153882a6b90c8a9c41559c46454e20aaae2322a71055a70191538828fba2c4a9c41471d16254e20aaee2b12a7105547158953882ac382c2a9c4117dd95314e208ece3320a710475719905388334b14c029c411d9c765d0e208eae3b2e871047671197438823ab88cba1c419594e61d0e20caaa730e871065653587438832aa9ac3a1c419654e60d0e20cb2a6b06871064e53d894388327298c4a1c419354c6250e208ece3b28871047571d94438823b388ca21c411d5c46510e20c9ca7310871064d53988438832729ac421c419354d6210e20caca7308871065553984438832b29ac221c419554d6110e20cb2a7300871065a53580438832ca9ac021c419594e61d0a20caaa730e851063654587428831aaa2c3a14419594d61d0a20caaa6b0e851065953983428832ca9ac1a1441175d76350a208baea31a851045e7694d428822e3b2a6a1441175da5310a208beeca98851065653984428832aa9cc2214419594d6110a20caaa6b08851065a53580428832ca9ac0214419694d60cca20cb2a7b02651045d7694c518830f324a628c418759253146208beeca98a31061e6454c518830eb22a628c411ddd95114620c6ac8a88a31045e73997418822eb9ccba0c419654e
  | 15 => 0x5673152410c2b3390a920861595c85490430ae4e02a4821846f72595410c236392caa08611b9c865504308dae432a821853671951410c22ebaec6a08619c5446050430a6ee8b2a821856772595410c2b2392caa0861559cc6550430acce432a821856572195410c29abaec8a08611d9da5450430a6aeb2a2821853676951410c31b3b4a8a08614d9d954504308ecec2a2821853674151410c2ab398a8a0861599c85450430acae42a2821857270151410c2aabaec6a0861c55536350430e2aa831a821873154d81410c2b8ba8c0a08619c5946050430e62a830282186d063181410c22fbaac7908610f9d0654843087ae832a421863664506500c31ab2283280618d59541d00308beeab1c801863765505400c398a0ca0a0061875526310030c5ca8b10801862d54588400c31b2a2c2200618d5516110030e2aa8a0e601845d7694e300c23cbb4a718061cc551418c0308bcedaa2601865765d85300c32bb28c29806195d96414c0309a8eca0a601865765505300c38aaa28298061c6552404c030f2282a02601847a76d51300c2e4b96c698061c6552434c030b96e4a1a601855b754c9300c339b2ec2980619cd94614c030ce6cb20a60184f076505300c339b2a8298061cc551414c030ab2eb18a60186666298654c8333312c32a6411d9c763553208eae3b1aa99043f7655054c8326392c62a6419358e6215320cacc7308a9906556398454c832b31ac22a6419558d6115320cb4c6b00a9906596358054c8335312c02a6419c9856015320ce2c2b00a9904767199353c823ab8cc9a9e411d5d261d4f208eee8b0ea7906726158353c82ab38ea729e411d9c66494f208eae3324a7904767119153c823ab88c8a9e41559c76354f208beeca98a7904767199053c823ab8cc829e419a9896014f208ece3b2e879047571d9743c823b388cba1e411d5c465d0f208ece332c87904757199643c823b38ccaa1e411d5c66550f20c9ca6312879064d5318943c823b38eca21e411d5c76510f208ece232887904757119443c82a6b98a9216411bdd95390b2099ce7304859046e7615142c82a6b98a8a164193d946350b20c9aea31a859064e5418d42c83262a0c6a1641b29c06350b20d92e031a859046e76d4d42c832631ea6a16411b1d95350b20c98c6a9a85906395458042c8236bb4a9996411b5d854ccb20a9ae62a6659065a5358032c8236bb4a819641535cc540cb208deeca98659054f7654c32c8327bb2a619641531d1530cb20c9ec8a98659064d6454c32c8266bb6861964153dd7430cb20a9aea21865905c97010c32c82ab39ea328e411ddd951147208bce7b2c839045d73d9641c822f39ccb20e41175ce6590720a6ae9b2c839055673d9641c82aab9ecb20e41559ce6590720aaae732c83905567315241c82aab98a920e411d9db53907208ea
  | 16 => 0xc26c382c898a61551d5414c530d2ec8a0a62984da75181314c32d3a8c098a61365d0604c530da6a230262986d051181314c369208c098a61b4504604c5309b4e1b1e429845e7518f214c26c382c710a619598c5188530ca8c7a8a429867351181214c21f3a0ca10a610f5d06508530cacc6288429865563144214c33828cc010a619c1456008530a6ae22a680984cc7258f404c23b3acc3a02611d1d561d01308eaeda8e809847576147404c29aba0a3a02614d9d541d0130a68eaa0e809856972152404c2e5396c720261569d46390130ab0eaa1c80985c87250e404c26d3b465202619c9945190130ae4eb20c809857075506404c26c3b263202614d5c45450130a6ae828a809865763145404c32a318a2a02614d9d54150130a68eaa0a809847a76151404c2b4b90a8a02616c5c45450130cb0cb21a80985587550d404c32c32a86a0261721c943501309b4ed1928098658658c9404c32c32864a0261665d03250130ce0cba8a809867065145404c2d8ba0a2a02615c9d64150130ce0cb20a80985b174905404c2b83aa82a02619c1954150130f2486a0a809879143505404c399baa82a02616c9d54150130b60eaa0a809873075505404c399b2a82a0261cc1954150130f24e6a0a809879173505404c3c9b1a82a0261e418d4150130e66a4a0a809879232505404c3c819282a0261e450731501309b0ec98a8098791414c5404c23bbb6a2202611d5db5110130cacc7a88809865563d44404c333316a2202619958b51101308eeec288809847576144404c32b318a2202619558c5110130cccc4288809866562144404c34cb248798261721c943cc130ae0eaa0e609866662d46304c332b16a31826199988518c130ccac428c60984ce72d92304c363316a318261b1988518c130d8cc520c609855475506304c34ab228318261b1989418c130d94c5a84609869964902304c3653148118261b2989408c130f2282a04609847671189540c23ab88c4aa0610fdd95415030c5aa8b10a81863554584540c32731cc42a0618b9916215030c9cc6b10a81865663984540c333314c22a0619958a6115030c6cc8b08a81865663584540c333312c22a061995896115030cd4c5300a81866962980540c33930cc02a0619c58660150308f6eab04861864e53189430c3172a2c4218618b5516210c30c6ca8b08861863554584430c31caa4c0218611d9c664948308eae3324a41847671191520c23ab88c8a90611bdd95214830c5ac8a90a41866552584520c23b38ecba10611d5c765d0830c6ca8b0e841863554587420c23b388caa10611d5c46550830c3ca831a84184d97018d420c32631ca4a10619318d52508308ece3b28841847571d94420c2a7baa64190611ddd95114430c6ac8a88a21866562544510c29aba6cb20861599c86590430acae432c82185
  | 17 => 0x8a618d59054d4530acce42a6a29856572153514c2e3396c7a8a61c515143d4530b88e4a1ea2985377454b514c29a3a2a5a8a61749c232d4530e8aa4196a29855573193514c2b3390c9a8a61595c864d4530ae2e0326a29856672d8f514c2b2b96c7a8a611d5db43d4530acee4a1ea2985647250f514c23b3b087a8a61599c843d4530acae421ea2985727010f514c2aab9ec5a8a615c5c362d45308eceda16a29847576d0b514c2abb9a85a8a61551cd42d45308ecec216a2984757610b514c2ab39885a8a61555cc42d4530ae4e0216a2985717010b514c3a299065a8a61599cb60d4530acae5b06a29847776544514c31ab26a828a611d5da54145308eeecaa0a29856772550514c2b2392a828a618d5905414530acce42a0a29856572150514c2ab3ac8628a61a55924314530b88e4a18a29847576948514c23bbb2a428a614ddd15214530a68e8a90a2985d2708c8514c2ab3a86428a61d15483214530aaae7b20a29855573190514c2b3390c828a61595c86414530ae2e0320a29853674d8c514c29aba6c628a61599cb6314530acae5b18a29847576d0c514c31ab248628a6159dc94314530ac8e4a18a2985737050c514c2b83828628a611d9d84314530c6ac8218a2985667210c514c2b2b908628a615c9c04314530aaae7b10a29853674188514c29aba0c428a61555cc6214530ae2e0310a29847676d08514c23abb68428a618d5934214530c6ac8a10a29855773508514c2aa39a8428a611d9d842145308eaec210a29855673108514c2aab988428a615c9c04214530ae2e0210a298572708c8514c2b8b846428a61d14c832145308dce432e829846d72197414c32b31ea3a0a619cd4660d05309b0e0b1c829865663146414c32ab18a320a61599cb6590530acae5b2c829853574196414c31aba0cb20a61955cc6590530acee4aa4829856472552414c2b3390a920a61595c85490530ca8cb31c82986546558e414c2e8382c720a61959964390530aa8eaa1c82986566550e414c2e23928720a61959963290530ba4e11948298656650ca414c23b3accaa0a614d5d26550530c6ae932a829856772595414c2b2392caa0a615cdc16550530caae632a829847676951414c2b3b92a8a0a61591c954505308ecec2a2829856672151414c2b2b90a8a0a61559d66350530ca8cb31a82985547558d414c32a32ac6a0a61711c96350530ba0e0b1a82986546590d414c2aa3aa86a0a61951954350530e28a8a1a82985c47250d414c29b3a0a4a0a614d5d05250530ca8cb19282985d2708c9414c32a32864a0a61655d032505308dce4328829846d72194414c23b3acc220a619598c5110530ce0a3300829845e75d93314c26d384c598a619599751cc530aa8eaa0e629869564507314c267394c198a619c146608c530ce6a230262984cc72591314
  | 18 => 0x1d0230ccca4b0e811866552587408c39329283a0461c954941d0230c9cc7294811864d6394a408c2b4b90a9204619a5965290230cd2caa9481187295454a408c3b0a948320461d85494190230e4ca4a0a811872552505408c23d3b0a8a04615a5c85450230e56c8a92811872952d05408c3b0a9482a0461ca5494150230e64a8a0a811876152505408c399baa82a0461cc1d54150230d66caa0a811873365505408c3c9b9a82a0461e41cd4150230f44a4a0a811873152505408c3d0a9282a0461c85494150230c3aa8b18811846d75988408c237baac4204611b5da5210230c9cc7290811864d63948408c237bb2a4204619398d5210230c9ac6a90811866652984408c332a94c2204618d9516110230c6aa8b08811866652584408c332a92c220461539cb54cc230c9acb296611864d6554b308c3a32948398461c555141cc230e8ca4a0e61186696594b308c334b2aa5984611d9c662d51308eae3316a8984777158b544c23a38ac5aa261531c96395130c5ec8312a89864f63189544c333b16c2aa2619918b6155130caec630aa89866762185544c332310c2aa2619c187605513087eecaa0a89852c72550544c326b1cc42a2619358d6215130c9ee6b10a89864c73588544c32ab1cc22a2619998a6115130ccac5308a89865563584544c333312c22a261995896115130cb2c6b00a89866a62580544c334b12c02a2619c9856015130ce2c2b00a89847675987434c23a3aac3a1a611b9ca6590d308dae532c86984ce72996434c2a6b94cb21a61535c85490d309b4e131486984d870586434c267394c121a61569d46090d30c5ea8312869862c54189434c22f3b0a8a1a61535c85450d30c98cbb12869864c65189434c3273a8c4a1a61935d46250d30d1ea8312869864e54189434c3262a0c4a1a61a31506250d30d90c5b0286986cb62181434c23b38cc9a92611d5c664d49308beeca1ea49854c7250f524c237bb2a4292614b1d152149308ece3320a49847571990524c23bb8acba12611d1c565d09308ece232e849847571197424c23b3acc3a12611d1d561d09308eee2b2c849847471596424c296b90a9212611d9c765509308eae3b2a84984da70d8d424c23bb8aca212611d1c565109308ece2328849847571194424c30faa2c6212619358f5210930c9ac6290849847675984424c23a3aac2212618ed516010930cd6a4b00849866852580424c26d386c919261175d8548c930a9ae42a4649870c5490a324c2a63aa8519261369d6608c930cb4eb30464984d974982324c22ebb4a819261175d8540c930a9ae42a064985c970948324c267bb2a419261631d1520c930b96e0a9064984cd76d08324c2e4b868419261335d8420c930a9aea210649870c54108324c2e4b808419261361c1610c930c6ac9aa6a29856772553514c2b2392a9a
  | 19 => 0x3304a91843f76550548c31aaa2c22a4619358e6215230c9ac6b10a91865563984548c333314c22a4619958a6115230c6cc8b08a91865563584548c333312c22a461995896115230cb2c7300a91866962980548c31b2a2c3a1c618d55161d0e308daebb12871846d75189438c23b38cc9294611d5c66494a30acce32a4a51856571952528c2b3388a929461595c45494a30acce3324a51856571992528c2a7b9ac929461535cc6494a30acce2324a51856571192528c2b5380c929461599c76394a30acae3b1ca51856671d0e528c2b2b8e87294611bdd94394a30acce221ca5185657110e528c2b4b808729461535cf6194a30ad4e030ca51852e74182528c296ba0c129461599c46094a30acae2304a51847671191528c23ab88c8a94611b9db5454a30acce32a2a51856571951528c2373b0a8a9461599c45454a30acae22a2a51856671991528c2b2b8cc8a94615a9c26454a30a9ee6b22a51854d73191528c2b3388c8a9461595c46454a30ad4e0322a51852f7458d528c2963a2c6a946159dc56354a30ac8e2b1aa51856671d0d528c2b2b8e86a94615a9c34354a30ad2e1a1aa51846c7650d528c2b338886a9461595c44354a30ad2e021aa51856870585528c237bb2a4294611d9c765d0a308eae3b2e851866652987428c332a94c3a14619994961d0a30ccaa4b0e851866952983428c334a92c1a146193d8e5250a30c98c7292851864c63549428c23b38eca214611d5c76510a30c9cc7290851864d63948428c32731aa4214619358d5210a30ccca5308851866552984428c333292c221461995496110a30cd2a5300851866a52580428c334a92c0214619a949608ca30cd2a5b02651846d76948518c317324a428c618b59252146308deeca90a31862e64548518c316b22a428c611ddd95114630c6ac8a88a31846e72997418c236b94cba0c619a54a60d0630cd2a4b06831846e72996418c236b94cb20c614d5d36590630acce532c831856572996418c2b3390cb20c61595c86590630acce5aa4831856572d52418c2b3390a920c61595c854906308dce432a831846d72195418c29b38ca8a0c6193d8e5250630c98c7292831856672995418c2b2b94caa0c614ddd16550630acce432a831856572195418c29abaec8a0c61599cb5450630acae5aa2831847676951418c29b3b4a8a0c618d9da5450630e64e12a2831853676551418c23b3b0a8a0c61599c85450630acae42a2831871554d8d418c38aaa0c6a0c61c99525250630e4aa9292831872764949418c3a3b1ca4a0c61d118e5250630e4ca8a92831872554549418c393b22a4a0c611b9ca65106308dae5328831866952980418c334a92c020c619a54b604c630cd2a4302631864e6394b218c326b1ca590c619a54b6048630cd2a4302431866a52580218c333294c3a04619954a6
  | 20 => 0x552547401029bbb2a3a00810f5da54900408f2ed2a480207495394a40103a529aa520081d254d5290040ea2a728c80207615294640103a8a9aa320081d85495190040ae2eb20c80207515390640103b0a9483200815cdd54190040ea2a6a0c802076152506401029abac82a00818dd964150040c6ecaa0a802071653505401038aa9a82a0081c99494150040e4aa4a0a802061f6594d401030fb2aa6a00818bd965250040c5ecaa92802070d53549401031bb2ca2a00818dd955150040e2ca6a8a8020715535454010393292a2a0081c95495150040cb6cb29a802065b6554d401038db22a6a00819ad965250040e92a7292802066b6554940103a529aa4a0081d254d5250040e56c8a9280206736594540103a8a9ca2a0081d854a5150040ce6caa8a80207325454540103a8a9aa2a0081d85495150040ae2eb20a80206736590540103a8a9c82a0081d854a4150040ae6eaa0a80206736550540103992a282a0081d454d4150040ec2a4a0a80206566398654cc32b31ac32a6611d9c762553308eae3b12a99843f7655054cc32731ac42a661931cd6215330cccc5308a9986656298454cc333312c22a661995896115330cb4c6b00a99866a6258054cc334b12c02a6619c9856015330ce2c2b00a99854d7215243cc267394c121e61179d85450f30a9ae42a2879864f6518943cc326ba8c4a1e61939506250f30c98a831287986ca7018943cc364b80c4a1e618e5516010f30acce3a94a5984767199252cc23ab8cc9296611d9c46454b308eae2322a59845e7690d52cc2a639286a96611bdd95214b308ece3b2e859847571d9742cc23b38ccb216611d5c66590b30c98c7292859864c6354942cc23b38eca216611d5c76510b308baed2a4659845d7615232cc2a6b90a919661175da540cb30a9ae42a0659854f7654832cc327bb2a419661531d1520cb30c9ec8a90659864d6454832cc266bb6841966153dd7420cb30a9aea21065985c97010832cc2b3396a328e611ddd951147308dce5b2c839846d72d9641cc237394cb20e611b5ca6590730a6ae9b2c839856672d9641cc2b2b96cb20e61599ca6590730acae532c83985667215241cc2b2b90a920e61711c94390730e8aa419483984d97318141cc2b3394caa0e61595ca6550730a6ee8b2a83984767695141cc23b3b0a8a0e61599c85450730acae42a283985c47258d41cc2e8382c6a0e61c51514350730b88e4a1a83985377454941cc29a3a2a4a0e61655d03250730e8aa419283986726518141cc2e8b98c0a0e61b498c6050730d2ac8a0e63985d07050731cc267394c198e61331c9644c7309b0e0b2263986976450531cc26d386c790e61365ce60c873087ce9b2c439843d74d9621cc32731aa510e614d5c654d0330998e4b1e81985357195140cc326b1cc5aa4619c9866095230ce2c
  | 21 => 0x3a2a9ca528881d194d5294440e8aa6a94a2205567314a51102aab98a5288811d5db4394440acee4a1ca2205647250e511023abb08728881599c84394440acae421ca2205727010e51102b8b8087288811d5db4294440aaee6a14a2205547350a511023abb08528881559cc4294440aaae6214a2205727010a51102b8b808528881d14c83294440aace6304a2205557318251102b3390c128881595c860944408eceda9aa22056672d4d51102b2b96a6a88811d9d85354440acce429aa2205657214d511023b3b6a4a8881559cf5254440aaae7a92a2207465394951103a2a9ca4a8881d194d5254440e8aa6a92a2204767614951102ab398a4a8881555cc5254440ae0e0b1aa22047676d0d51102b3b9286a8881591c943544408ecec21aa2205667210d51102b2b9086a88815c9c04354440ae2e021aa22057070589511023b3b684a888155dcd4254440aa8e6a12a2204767610951102ab39884a8881555cc4254440ae4e0212a22057170109511029bba264a88814d1d13254440e8a64192a2205567318151102aab98c0a8881599c86054440acae4302a2205567310151102aab9880a8881599c84054440acae4202a22045d7694c511022fbb2a6288819394e6214440c9aa7310a22064e535885110326a9ac4288811b5da5214440c9cc7290a22064d639485110237bb2a4288819398d5214440c9ac6a90a22065653984511032aa9cc2288819994a6114440ccaa5308a22047776544511032b31aa2288819558d5114440cccc4a88a22066562544511032ca9cc1a08819a54a60d0440cb2a6b068220669525834110338a8ac1a0881955965390440caacaa9c82206656594a41103a329ca520881d154e5290440ccacaa9482207465354a41103a2a9aa5208814d9da5450440caecb29a82207176494d411032bb2aa6a0881c5d915350440ccecb29282207465394941103a2a9ca4a0881c9d925250440ccecaa9282207465354941103a2a9aa4a0881c9d915250440cb2a7300822066952980411032ca9ac0208819a5496010440ce4a2b00822046e729973110236b94cb988811b9ca658c4408dae532c622046e721953110236b90ca988819654f604c440cd2a5b02622067151d81311032ca98c0988819a548604c4408dce5328622046d72994311022f39ccb90881175ce65c84408bce732c422045d73996211022f398ca90881175cc6548440cb2a7b02422066952d812110338a8ec0908819654c6048440cd2a4302422045e73994211022eb9cca108819594e61d0040caaa730e8020666529874010332a94c3a00819594d61d0040caaa6b0e8020666525874010332a92c3a00811d5da51d00408eeeca8e802071653507401038aa9a83a0081c994941d0040e4aa4a0e802070d5354b401038b29aa3a0081c554d51d0040e4ca4a8e802072
  | 22 => 0x8811d5d661d0c40caca730e862065553987431023bbaac3a18819594d61d0c40caaa6b0e862065953583431032729ec4a18819394c6250c408daeb310862064e539884310326a9cc4218811bdd56210c40c9ca6b10862064d53588431023abacc2218819594e6110c40caaa7308862047775584431032b29ac2218819554d6110c40cb2a7300862065a53580431032b29cc3a90819554e61d4840caca6b0ea4206555358752102a739ea529081535cf5294840acce3a94a42056571d4a52102b338ea729081595c75394840acce229ca4205657114e52102a7398c929081535cc6494840acce2324a420565711925210326b18c729081599c74394840acae3a1ca42046c7650e5210236bb08729081599c44394840acae221ca42056a7010e52102b4b808729081539ce6094840a9ae7304a42046e76d4d52102b338ea6a9081595c753548408dcec29aa4205667114d52102b2b88a6a9081599c66454840acae3322a42052c7458d5210326b18c6a9081599c74354840acae3a1aa42056a70d0d52102b4b8686a90811bdd943548408dcec21aa4205667110d52102b2b8886a90815a9c04354840ad2e021aa4205687058552102a739cc0a9081535ce6054840a9ce6202a42054d73101521022ebb4a62908117dd95314840c9ca7310a42064d539885210237bb2a4290819398d5214840c9ac6a90a42065653984521032aa9cc2290819954a6114840caca6b08a420655535845210332a92c2290811d5d661d0840caca730e8420655539874210333294c3a10819954a61d08408eeeab0e842065653587421032aa9ac3a10819994961d0840ccaa4b0e842065953983421032ca9ac1a10819a54960d08408b8ed29a842045e7654d4210327b1ca4a10819318e52508408baeb318842045f7558c421022ebb4a62108117dd95310840c9cc7290842064d63948421032731aa4210819358d52108408eaeb308842065653984421032aa9cc2210819994a6110840ccaa5308842047775584421032b29ac2210819554d6110840ccca4b08842066552584421032d29cc0210819654e6010840cd2a5300842065a53580421032ca9ac0210819a94960108408ece332e642047571997321023b38ccb190811d5c6658c8408ece232a642047571195321030fb22a699081531c9534c840c5ec8a92642054c73549321023b38cca190811d5c6650c840a9ae5298642054d7394832102a7baa6419081535d5320c840c9eca990642064d654c832102c63a264190819394e62d4440c9aa7316a22064e5358b5110326a9ac5a88819398e52d4440c9ac7296a22064e6354b5110326b1aa5a8881559cf5194440aaae7a8ca22056672d4651102b2b96a328881599cb5394440acae5a9ca2205667214e51102b2b90a728881559cf5294440aaae7a94a2207465394a5110
  | 23 => 0x14d409d2e530486a064f531894350326298c4a1a811bdd95214940a98e6a90a4a056471548525026cb9cc1212819318f5250940c98c629284a047771594325023a38aca192811d9c4650c9408eae232864a04b57199032502a6b90a619281535cc520c940a9cea99064a054c754c83250346b2264192819614d600c940cd0a4b0064a04777654451502aa39aa228a81591c951145409b2e630282a04e97218141502ccb98c0a0a816a5c86050540b64e121a82a07145350d41502d3b9286a0a81691c94350540b4ce421a82a05a57210d41502d938086a0a816c9c24250540b2ee6a1282a059473509415039229284a0a81659cc4250540b2ae621282a05b27010941502e8b98c0a0a81785c86050540b62e1b2a82a05367598d41502d9384c6a0a816c5c26350540a68eab1a82a05a77258d41502d2392c6a0a816cdc16350540b60e0b1a82a05b27018d41502d8b80c6a0a816c5c25350540b4ee4a9a82a05a47254d41502d9b82a6a0a81c554c5350540a6ceb31282a05b27098941502d8b84c4a0a814d1d56250540b2ee6b1282a05947358941502d9b82c4a0a816c1c16250540b64e031282a05b17018941502d8b84a4a0a8165dcd5250540b28e6a9282a05b3705494150392a90a4a0a816c9c33250540b62e199282a05b2708c941502d8b8464a0a814ddd53250540a68ea99282a0536750c9415029aba864a0a81e14c83250540b64e019282a05b1700c9415035832ec0a0a816c5cf6050540b62e5b0282a05b2709814150359b04c0a0a8165dcd6050540b28e6b0282a05a77258141502d2392c0a0a814d9d46050540b2ce630282a05957318141502d3390c0a0a81695c86050540b64ec30282a06b27618141502d93a8c0a0a81cc9d46050540f24e630282a05b17318141503c8b98c0a0a81645cc6050540f44e430282a05b17218141503d0b90c0a0a81685c86050540c6acaa0e62a04e9729833150358a0cc198a81ac50560cc540c6ecaa0a62a046f725943150236392ca18a811b9c8650c5408dae432862a061d6414c3150358a0cc018a819c145600c540d6282b0062a063565507215026cb9cc190a81ac50660c8540d6282b0642a063765505215022fb9aca10a81171cd65085408bce632842a045d731942150316b20a410a81ac5066008540ce0a2b0042a06b1415802150275b92c7a028136dcd62d0140b66eca0e80a06b3765074050358b1a83a0281ac58941d0140a9ce5a9ca62054d72d4e53102ab38ea729881555c75394c40a9ce4324a62054d7219253102ab388c929881555c46494c40c9ac4314a62054e7298253102a6b94c129881559c66454c40aaae3322a62051c745895310326b10c4a9881561c16154c40a9ce5302a62054d72981531022fbb2a6298819354e6214c40c9aa6b10a62065553984531032aa9ac229
  | 24 => 0x21aa3a05727010d51d02b8b8086a8e8155dcd6254740aa8e6b12a3a05737058951d023b3b684a8e8155dcd4254740aa8e6a12a3a04767610951d02ab39884a8e81555cc4254740ae4e0212a3a05717010951d029b3a064a8e814d5d03254740e8a64192a3a05577358151d02aa39ac0a8e8159dc96054740ac8e4b02a3a04777654451d0338a8cc1a0e8159dc95390740ac8e4a9c83a05577354a41d02aa39aa520e816c5c35150740c6ecaa8a83a04b67614541d02b3b92a6a0e81591c95350740b4ee4a1a83a05a47250d41d038aa9886a0e81699c84350740b4ae421a83a05577354941d02aa39aa4a0e8165dcd4250740b28e6a1283a05967310941d02cab9884a0e81c95484250740a6aeb31a83a05377558d41d02d3b92c6a0e81691c96350740b66e0b1a83a05b07058d41d025b3b6a6a0e816c5c35350740b4ee4a9a83a05a47254d41d025b3b0a6a0e81c554c5350740b4ce429a83a05a57214d41d02d8b80a6a0e814d5d66250740a6eeab1283a05977358941d02ca39ac4a0e816cdc16250740b60e0b1283a04b676d4941d02d8b86a4a0e8165dcd5250740b28e6a9283a04b67614941d02cb398a4a0e81655cc5250740e4aa429283a05b17014941d029bbaa64a0e814d1d53250740a6cea19283a0535750c941d03c299064a0e818dd976050740c6ecab0283a05977358141d02ca39ac0a0e8169dc96050740b48e4b0283a05967318141d02cab98c0a0e81699c86050740b4ae430283a06b16018141d033928cc020e81ac5056010740c6acaa0e63a046e72d9631d0236b96cb18e818d592518c7408dee4b2a63a046c7259531d031bb2a8298e81ac507604c740ce2a230263a06356494431d031ab2a8390e81179cf65887408bae7b2c43a06356494621d022fb9aca90e81171cd6548740c6ecaa0a43a06b141d8121d0338a88c090e818d5925108740a9ce5a9ca72045f7654c5390274b94c121c819394c6250e40c9aa6312872054e73d4a5290237bb2a429481365ce6090a40c98c7292852064c63549429023b38ecb994811d5c765cca40cd2a5306652047671d96329023ab8ecb194819654e608ca408eee2b2a652047471595329025cb80c8994811ddc5650ca408e8e2b28652054d7294c32902a6b9ca41948153dd5320ca40a9aea990652058c744c8329023bbb2a228c811ddd953906408eeeca9483204d9731814190274b90c0a0c811d1d953506408e8eca9283205d17318141902f0b90c0a0c811b9cb65cc6408dae5b2e632046e729973190236b94cb98c81551c553cc6409d2e5306632045e73d97219022eb9ecb90c81179ce65c86408bae732e43205647154b219026cb9cc190c818d59661d0240c6acab0e81204eb7258f409026db9ac5a04819c59661d0240ce2cab0e812045f7654c53502a6392a629a81551c553
  | 25 => 0x75984430863bbaac321043179cf65108218bae7b288410e1e5458c420870eaa2c6210438d5526110821c74a8b008410e3954580420872aa9cc319043179cf65904218bae7b2c8210e2d5498a410869aba6cb20843559cf6590421aaae7b2c8210d567315241086aab98a9208435c9c05490421ae2e02a48210c7576d4e410869aba6a7208431d5d85390421a6ae829c8210d727014e41086b8b80a720843c955262904218eeeab148210f255458a410863b3b0a8a0843559cc5450421aaae62a28210d727015141086b8b80a8a08434ddd15350421a6ce829a8210d357414d41086b9380a6a08435c5c05350421a6ae92928210c5e73194410862eb98ca208438d552611042187ce9b2c6210c3d74d963108726a9cc5188430f9d0650c42187ae83286210c6d7694a210871ab22a9108431d5da52884218eae9b2a4210c77755912108678382c8908431d9db54484218ececaa24210e3764551210871b32283280438d59141940218bce6322a010c5d7319150086b838282a80431edd95014021c72c8a80a010e5963540500862fbb2a629e81531c95314f40c9aa6b10a7a054c7254f43d023abacc3a1e811ddd561d0f40a98e4a9887a064e5358843d0326a9ac421e811d5d66110f408eeeab0887a06595358043d0237bb2a429681531cd5214b40c9ac6a90a5a054c7354b42d023abacc3a16811ddd561d0b40c9ac729085a054c7354842d0326b1aa4216811d5d66110b408eeeab0885a06695258042d023b38ccb996811d5c665ccb40a98e4a9e65a04767199632d023ab8ccb19681531cd528cb408ece232a65a04757119532d02a6392a699681531cd524cb408ece332865a04757199432d025ab8cc819681531d5320cb40c9eca99065a064d654c832d0346b22641968159dc95394740ac8e4a9ca3a05667214e51d02b2b90a728e8155dcd5294740aa8e6a94a3a05567314a51d02aab98a528e81559cc6494740aaae6324a3a05667219251d02b2b90c928e814d9d36394740acce5b1ca3a056572d8e51d029b3a0c728e811d5db4394740acee4a1ca3a05647250e51d023abb08728e81599c84394740acae421ca3a05727010e51d02b8b808728e814d9d36294740aace7b14a3a055573d8a51d029b3a0c528e811d5db4294740aaee6a14a3a05547350a51d023abb08528e81559cc4294740aaae6214a3a05727010a51d02b8b808528e81d14c832947408eceda9aa3a05677254d51d02b2392a6a8e811d9d85354740acce429aa3a05657214d51d023b3b6a4a8e8155dcd5254740aa8e6a92a3a04767614951d02ab398a4a8e81555cc5254740aace7322a3a05557399151d02b3394c8a8e81595ca6454740acee4b1aa3a05647258d51d02b9b82c6a8e811d9db4354740acee4a1aa3a05647250d51d023b3b086a8e81599c84354740acae4
  | 26 => 0x3cb86ca21c431e9c06510e218f2e03288710e2e545884388716aa2c421c439394d6210e21c9aa6b108710e3554984438872aa9cc221c438e9516010e21c72a8b008710e5a53580438872ca9ac021c438d55261d0a21c3ca831a8510e1d5418d428869aba6a720c434d5d05390621e4aa93148310f255458a41886ab39ea8a0c43555cf54506218ecec2a28310d3674d4d418869aba6a6a0c434d5d25350621c5ca8b108310e4e53588318871ab22a990c438d9914194221c6ac8a0ca110c7b76540508863d384c7aa2431e5c263d51218bce7306a890c5d73983544872631ec4aa24396d8f6055121cb0c7b02a890e5b63181544872c318c0aa2439ad886055121ce6c2302a890e6972181544861fbb2a82a2431d5c664d4d21cb6a6b04a690e69629825348738b0cc129a439a5ca6094d218beeca98a690c757199053486acb84c629a431d5c765d0d218f6e0b2e8690c7870597434863a3aac3a1a439514d61d0d218f4e1b2c8690c7970d964348637b92caa1a431edc16550d218f0e0b2a8690c6e75d894348636b96ca21a431d5c76510d218f4e1b288690c7970d94434863d380ca21a431e5c06510d218d8eab108690e4f53588434872629ac421a431d1d56110d21caea6b088690e5b53580434872c29ac021a438dd5161d0921aaee6aa48290d547355241486b9b82a920a435c1c15490521ae4e129c8290d717094e414862fb9acaa0a43171cd6550521a6ae1aa28290d577355141486aa39aa8a0a431d9d85450521a6cea2a28290c767694d414869aba4a6a0a435c9c25350521ae2e129a8290c747654d414869bba2a6a0a434d1d15350521e4ea9b128290f2754189414872629ac598a438d59354c8521ae0e0aa64290e5963d42504863dbb2a0282438d99141141218f4e031aa810c797018d540862f398c0aa043175cc605502187eecaa0a810e1d5458c540871caa2c02a043879916315021c9ac7310a810e5663984540872ab1cc22a0439698e6015021cb2c7300a810e7261980540871d322c02a0439698d6015021cb2c6b00a810e6a62580540873930ac02a0431d9c66494c218ece2322a610c7a70191530863cb80c8a984317dd95314c21c3ac8a98a610e5953580530871b38cc8298438d9c56414c21c3ac9318a610e2d64988530871ab24c2298438e9926014c21c72c9300a610e3a64580530871cb22c0298439698d6014c21cd4c4b00a610e7261580530873838ac0298431d9c465d0c218f4e032e8610c7970197430863abacc3a18438d55261d0c218f4e032c8610c79701964308637394caa18431e9c06550c218f2e032a8610c6d7518943087172a0c4a18438b5506250c21c9ca63128610e4d53189430863d386ca218431e5c36510c218dce43288610c7671194430863d380ca218431e5c06510c218daeb3108610c75
  | 27 => 0x63c5d536350531e2ea831a8298e3564d53314c6b8382a998a639a58b50941318f6eca80a098e3664504504c63d380c4aa0631e5c062550318dce4302a818c6d72181540c61fbb2a82a0638b5516215031c72a8b00a818e2e64588540c72731ac42a0639998a6115031ccac5308a818e6a62980540c734b14c02a0639c9866015031c74c8b00a818e5a63580540c735312c02a0639a5896015031ce4c2b00a818c7775586430c7172a2c4218638b5516210c31c6aa93088618e3a54580430c71caa2c0218631e9c064548318f2e0322a418c6f76548520c716b22a4290639a5496014831c6aa930e8418c7a70195420c63cb80caa1063879506350831c3aa831a8418e4c63949420c72631aa4a10631e9c365108318f2e1b288418e1d5498e410c69aba6cb20863599cb6590431acae5b2c8218d6672152410c6b2b90a9208635c9c05490431ae2e02a48218f155498e410c63bbaac720863c555163904318ecec2a28218d6672151410c6b2b90a8a08635c9c05450431ae2e02a28218d357494d410c69bba2a4a08638d55261104318baed29c6218e3564552310c63abb4a7188631d5d3654c4318eeeab226218cf070591310c63b3b6a8988631d9d9544c431c6ec8aa26218e3664506500c71ab2283280631b9c864540318dae4322a018d7070505500c63dbb2a0280638e5915014031cd2c4a80a018c5e7398354c862eb9cc1aa6435c1c1615532187eecaa0a990e4d6398854c872b31ac22a6439558d6115321cb4c7300a990e596398054c8738b0cc02a6439698d6015321cb2c6b00a990e6a6258054c8738b0ac02a6439c58660d4f21cd4c4b06a790d5a70d4e53c863d380c8a9e431e5c06454f21ab4e1b1aa790c5f7654c53c8733312c229e431e9c065d0f218f2e032e8790c7a7099643c863cb84cb21e431e9c26550f218f2e132a8790e4e5318943c8726a98c4a1e431e9c36510f218f2e1b288790c7a7019443c863cb80ca21e438d5516110b21caca6b086590d567315241c86aab98a920e435c9c05490721ae2e02a48390d7270d4e41c86b8b86a720e431d9da5450721a6ee0aa28390d567315141c86aab98a8a0e435c9c05450721ae2e02a28390d3574d4d41c86b9386a6a0e435c5c35350721a6ce829a8390d357414d41c8792aa6c4a0e43c955062507219cae43028390e4d5318931c86ad39ea12864395dc56394321ca8e2b1ca190e587058e50c872b31c83286439558e4194321c6cc8a0ca190e566350650c872ab1a8328643179cc64543218bae6322a190c7b7654050c872731ac5aa443479cf5495221a3ce7b22a910c5e73181548862eb98c0aa4430fdd95415221c6ce3326a710e36715935388717322c5a9c438d59261d4e21a3ce9a9ca710d1e74d8d538862fbb2a629c439958a6114e21caca730e8710c7a70d9443886
  | 28 => 0x4141ec4c4a80a0a0f61625405050637394c1298831b5ca6094c418beeca98a620e4d53588531072ca9ac0298839594e61d0c41c9ca6b108620e4d53588431072aa9cc2218839694d6010c41cb2a6b008620c5e73982521062eb9cc1290831bdd95214841c9ac6a90a420e69525805210733294c3a10839358e5210841c9ac6a908420e65529844210735292c0210839a54960108418f4e032a6420c797019532106a6392a699083531cd524c841c9eca9906420e4d654c8321063abb6872888359dc94394441ac8e4a1ca220c757610e51106b33908728883595c843944418eaeda14a220d577350a51106aa39a85288831d5d84294441aace6214a220d557310a51107a299065288830f5da54904418eaed2a48220c7b76540501072cb1aa0280839a58950140418dce5306a998c6d7298354cc6b8382c2aa6630fdd95415331c9cc6b10a998e666258454cc732b12c22a6639a98a6015331cd2c5300a998e716198054cc72d31ac02a6639a9896015331cd2c4b00a998e716158054cc71aaa2c221e635a9c35294b318f4e0322a598c797019152cc637bb2a4296631e9c26590b318f2e132c8598e4c6394942cc72631aa4a16631e9c36510b318f2e1b288598d667215241cc6b2b90a920e635c9c05490731ae2e02a48398c767695141cc69bb82a8a0e63599c85450731acae42a28398d727015141cc6b8b80a8a0e63c55536350731e2aa831a8398cd57318141cc6b5396a12866399dc56294331cc8e2b14a198e666290650cc732b1483286638d9914194331cccc4a0ca198e656250650cc637390c8a86631b5c864543318f6eca80a198e4d6398b548c697396a92a4634b9cb64552318dce4302a918c6d72181548c61fbb2a82a4638d55261d0e31c5ca83128718e2d54189438c6973a6a5294631bdd95214a31ccca530e8518c7a70d94428c63cb86ca21463879516310a31c3aa8b188518e4d63948428c726b1aa4214638d5526110a31ccaa53088518e3a54580428c71caa2c0214639a9496010a31cd2a4b008518f155498e418c78aaa2c720c63599cb5450631acae5aa28318c7676151418c69aba4a4a0c63879516310631c6ac8aa66318e3664506508c71ab2283284631edd950142318f4e1316a898c797098b544c637394c1aa2631b5ca60d5131c9ec6312a898e6b62d81544c734316c0aa26396d8c6055131cd6c4302a898e6862181544c739b08c0aa263965cc605513187eecaa0a898e3754587434c735a92c1292631bdd952149318f6e0b2e8498c7870597424c732292c3a12631e9c065109318f2e03288498e4d63d48424c726b18a42126399d496110931cd6a4b008498e6852580424c6b3b92a920a63591c95490531ae6e0aa48298d7070552414c69ab86a8a0a6359dc95450531ac8e4aa28298c7676151414c69b3a8a8a0a
  | 29 => 0x2264a0cb675191325071b3a8c899283a55cc644c941d4ae432264a0eb270191325065ab80c899283ac5c0644c941962e032264a0cb676d51325065a3b6a899283359da434c941d28c921a64a0cd47650d325074a3228699283711c9434c9419cced21264a0ea46490932507c321c8499283391d9424c941d48c8a1264a0dc47350932507c2a1a8499283a9193324c941d28c919264a0cb674181325065aba0c0992832ddd1650c9419e6e0b2864a0cf0705943250679380ca192833c5c0650c9418eceb32064a0cb576990325065b3acc8192838d9d6640c94196ae132064a0e94735903250752392c8192832ddc1640c9418ecea32064a0cb674190325066b398c819283399c8640c9419e4e032064a0cf170190325065bbb6a8192832d5db540c941d2ac9a9864a0e556514c325074ab20a619283715c8530c9419aaeda1864a0d5675d0c325074ab268619283355d8430c941aacea21864a0e956410c32506e2b908619283745c0430c941d4ac9a9064a0e65651483250752b20a419283715cc520c9419caeda1064a0d6675d083250752b268419283e1d0f420c9419caec21064a0d66751083250752b208419283715cc420c941f088621064a0de170108325074ab266419283a9592320c941b8ae719064a0cd7764c832506ca3a26419283a5591320c9419ceec99064a0da4744c83250752b22641928371dd9320c941d8eec99064a0dc6754c832506e23aa6419283e1dd1320c941b8ce899064a0dc4744c832507c23a26419283611d1320c941d8ec899064a0f86644c83250762b226419283e1591320c941d0ac899064a0f87544c832506e3b8264192832d9d2600c94196ae930064a0c7775580325063a3aac0192836c5c354d41419cee4b1ea0a0ce47258f505066bb9ac5a8283351cd62d4141d2ec9b1aa0a0e9754d8d505074bb20c6a8283a5d506354141d4ec9b12a0a0ec763d89505076231ec4a8283a9d536254141d4ec8312a0a0ec7631895050762318c4a8283a9d506254141da0c7a82a0a0ee062d41505072a31ca0a82839918a5054141ae2e1aa0a0a0db170d50505074ab24c62828395d526314141d2ea9318a0a0e956458c505072baa2c628283a5d516314141da0e0b18a0a0e556394c50506b8b80a628283a95926214141d8cc7310a0a0ec5639885050733aa4c428283a9d526214141d4ac8b10a0a0ec6635885050762b1ac42828399d516214141d4ea8b10a0a0ee0705885050732b14a4282835c5c052141418eeeca80a0a0d547354050506b2392a0282833cdd95014141ba0e6a80a0a0de07254050506b9bb2a0282839cdd95014141e66e8a80a0a0f316454050507a9b9aa0282835c1cd5014141ea0e6a80a0a0d507354050507a931aa028283d458d5014141ec6e4a80a0a0d707254050507b0392a028283581c9501
  | 30 => 0x45884350753a1ac421a83b190d6210d41d4a86b1086a0ec5435884350742a1ac421a839c9966010d41f228730086a0ee2629804350770b14c021a83acd526010d41d2a86b0086a0e726558043507c8a1ac021a83b89896010d41dc2c4b0086a0eb2745804350759aa2c021a83acd0d6010d41da486b0086a0eb1435804350768a1ac021a83a450d6010d419ace7304a4a0cd573982525074bb26c6a9283a5d536354941d2ec831aa4a0e975418d525076231ea4a9283acd936054941da6c7b02a4a0ed063d815250759ba6c0a9283acd536054941d66c8302a4a0ed3631815250768318c0a9283ac5d06054941d66a8302a4a0ee3521815250739290c0a92831ddd95214941ae0e0a90a4a0ce77654852506e239aa429283781c15214941b48e4a1e84a0da57210e42506d8b808721283599d742909419ace730484a0cd573982425063a3aac121283699cb5450941d2ea9b1a84a0e975418d4250762b90c6a12832d9db4350941d28c7a1a84a0e946350d42506d239286a1283b118f5250941d88c629284a0d6675d09425076231e84a1283a518e4250941caccb31884a0e975498c425072b32ac621283a5d516310941d88e4b1884a0cb57690c425074ab1c8621283a558c4310941b4ae421884a0db17010c425074ab1e8421283999964210941b4ae921084a0ec563908425065bbb28421283651cd4210941d2ac6a1084a0ce776508425073332a8421283711cd4210941d8ac6a1084a0da7765084250753bb28421283a99954210941e4ccaa1084a0f877350842506d239a8421283e11cd4210941b08e6a1084a0f86635084250752b1a8421283e158d4210941d0ac6a1084a0e7265980425076931cc021283b458e6010941f428530084a0eb3549804250752a12c0212839c9956010941da4c6b0084a0ed16358042507d0a12c021283ac9d16010941d66a8b0084a0eb243580425075821ac021283acd096010941dc484b0084a0eb1425804250770a12c021283a850960109419e4e1b2e64a0cf170d97325065bba2cb992831d9d664cc9418ecea32664a0cf2701933250678b80c999283a519143cc941b88e4a1e64a0d6675d0b32507c2a1e8599283599d442cc941d4ec821664a0dc57310b32507c32188599283785c042cc94196ce930664a0cb5749833250679386cb192833c5c3658c94196ee8b2c64a0c7675992325063b3a8c9192833c9c0648c9419e2e032464a0d5675d0e32506ab3a88719283a5d90438c941b8ae421c64a0dd17010e32507c221c8519283a9191428c941b88e6a1464a0f874350a325065b3a4c1192832d5d2608c94196ae9b2a64a0cf3705953250678382ca992832d5c3644c9418eceb32264a0cb674991325066bb9ac89928339dc9644c9418ecea32264a0cf2701913250678b80c8992832d9d8644c941b62e03
  | 31 => 0x23928699483399da424ca41b88e6a126520cb5749943290679380ca194833c5c0650ca419e4e03206520cf17019032906e2b94a619483355db430ca41b8ae42186520dd17010c32906e2b9ca419483395db420ca41b8ae62106520de170108329066bbb2641948339dd9320ca41b8eec9906520ec7764c832906e3baa6419483715d5320ca41b8ce89906520dc4744c83290763b226419483b1591320ca41b8ee09906520c7775580329063a3aac019483399cb63542419cae5b1aa120cd673d89509066ab9ec4a8483a55926314241d2ac8b18a120e556394c50906b8b80a628483a95926214241d8cc7310a120ec5639885090752b22c428483b198d6214241d8ac6b10a120e656294850906b8b80a4284831ddd950142419e6eca80a120d73765405090739bb2a028483cc5915014241ea4c6a80a120f516354050907b1312a028483d858950142418beeca98a6a0d4c7254c53506ac382a629a8393d4c6250d41c98a631286a0d8c7250c4350746a1ac421a83a650d6010d418deeca90a4a0d4c7354852506b4382a4292839318f5250941c98c629284a0d8c735084250746b1a8421283aa509601094196ce232264a0cb970191325063db82ca192831e1c1650c9418f4e032864a0c7970194325065b38cc819283535c8530c941a9ae629064a0d4e754c832506a63aa6419283631d1320c941d1ac899064a0e54535843250732292c2192831bdc963d41418d8e4b1ea0a0c5f7358b505062e39ac5a82831edd95014141ab0e6a80a0a0d6872540505072bb8ac628283951c56314141c9cc7310a0a0e4d63988505072731ac4282839358d6214141ccee2b10a0a0e647158850506d3396c7aa283695cb63d5141d2ec731ea8a0d9673d8b54506cab9ec5aa283a9d8a62d5141b2ce6306a8a0d957318354506d3390c1aa283695c860d51419cce5304a6a0ce5729825350753b26c4a9a83a9d536254d41d4ec8312a6a0ea7541895350763a98c4a9a83acd936054d41dc6c5b02a6a0ee062d815350759ba6c0a9a83acd536054d41d66c8302a6a0ee3621815350770310c0a9a83ac5d06054d41d66a8302a6a0ed3531815350739298c0a9a831ddd95314d41ae0e0a98a6a0cd77654c53506e2392a629a83741c15314d41aaceba1c86a0ce6729824350672b94c121a831d1d56090d41b2ce7aa286a0d5675d0d4350753aa6c4a1a83a9d506250d41d8ea631286a0ec4531894350763a18c4a1a83a990c6250d41caccb21886a0d957490c435065bbb28621a83691c94310d419aeeca1886a0e566550c43506e23928621a8365dd94310d41d2eeca1886a0e966550c435078b32a8621a83e1dc94310d41b28e4a1886a0f847250c43506c23928621a83999966210d41f0a8731086a0ea754988435074aa1ac421a83999956210d41f0a86b1086a0ea75
  | 32 => 0x54d5d06154032c6ce830aa01947574185500cb1aba0c2a80650d5d06154032cace630aa01965573185500cb33390c2a8065995c8615403299eec990a01968e644c8500cb46b226428065b14ca6114032d8a64b08a01947b76540500cb1cb22a028065d24c95014032ce2c2a80a01946e7298253d0636b94c129e8317dd95314f41c9aa6b10a7a0e595358053d072b29ac3a1e83631c94310f41c9ca6b1087a0e4d5358843d0746a1ac421e839554d6110f41cb4a6b0087a0e595358043d074ca1ac021e83179ce6094b418bae7304a5a0c6f7654852d0726b1aa4296839a5496014b41ccca4b0e85a0e4d6394842d0726b1aa421683631cd4210b41d1ac6a1085a0e655258442d0735292c0216839a5496010b41d5284b0085a0c7a7019532d063cb80ca996832e5c0644cb41a98e4a9a65a0d4c7354932d0727b2a641968393595320cb41b18e899065a0e8d644c832d063dbb2a0286839658d5014341cd2c4a80a1a0d4e72d4e5390637394c129c831b5ca6094e418beeca98a720e4e531894390726a98c4a1c83539cf5294a418bce7304a520c5d739825290637bb2a4294839318e5250a41c98c6a928520c7a70d97329063cb86cb994839954a61cca418f4e1b2c6520c7970d96329072aa9cc319483535ca530ca41a9ae72906520d4f754c832906a6baa64194831b9cb63542418dae5b1aa120c5e73d89509062eb9ec4a84831edd95014241d4ac9316a720ea56458b53906e3396a729c83399ca6094e419cae5304a720dc672d4d539063bbb2a629c8335dd95314e419cce53048720ce572982439063bbaac121c83b194c6250e41d8aa63128720ec743189439065bbb28621c8335dd94310e41b88e4a188720e65659884390732b2ac421c83b190d6210e41d8a86b108720e71659804390771314c021c83b858a6010e41ce2cab008720ee2625804390770b12c021c83b490d6010e41da286b008720e956498f529074ab22c7a9483719cf5294a419ace7304a520cd57398252906e339ea4a94831ddd95214a419ceeca90a520cd673982429066ab9cc1214831ddd56090a41d8ae431a8520ec463949429076231aa4a1483b118f4250a41caacb3188520e556558c4290762392c621483b158e4210a4196eeca108520ce77650842906e239a8421483b158d4210a41ce2cb3008520ed2639804290768b1cc0214839c5956010a41da4c6b008520ed1635804290771212c021483b85096010a419e4e1b2e6520cf170d97329065aba4cb994833c9c064cca419e2e03266520dc47250f329073332aa599483715cc42cca41bc2e02166520cf270d963290678b86cb194832d5d2658ca419e4e03246520cf170192329072b32aa719483715c8438ca41ba2e021c6520dc47350a329065aba0ca994833c9c0644ca419e2e03226520cd67690d32906e
  | 33 => 0x832a9aeba18841964d65d0c420caa6ba88621065935944310832b92e0218841966565984420cb62b1cc221065995956110832d8ac6b08841966965980420cb64b1cc0210659a5956010832d94c6b0084196c963580420cb7130ac021065b85856010832cd6a8b0084196aa54580420cb34aa2c021065aa5516010832d94e6b0084196c973580420cb65a1ac021065b210d60108329b2e0326641945f76553320cb0f322a999065a399342cc832a9aea21664195c97010b320ca2ebb4a7190653a5c0648c8328deecaa4641962e64552320ca36bb4a719065a3993438c832a9aea21c64195c97010e320ca2ebacc899065365c0644c8328bcedaa2641945c76551320cb0e322a899065535d7424c832d18c9a1264195c671d09320cae2b8e8499065339da424c832e1aa921264194cc76509320caa6ba88499065719c4424c832b8ae221264195ca70109320cae4b8084990651b5d6644c8329d2e0322641946e76d51320ca363b2a8990658b191544c832a9aeba1a641968c64d0d320cae338e8699065715c7434c83299ced21a641970d5490d320ca663b28699065535d4434c832b8ce221a64195c57110d320cae53808699065725c0434c832c9aebb2a64194ce74d95320ca66b86ca99065939db654c832a9ae9b2a641954d75991320cae338cc899065715c6644c83299aeb322641964d75991320ca673a4c899065b19c6644c832d8ae332264194cd70991320caa7baac899065719c4644c832b8ae232264195ca70191320cae4b80c899065935d4644c832d1ce832264196c671191320cb62b88c899065b29c0644c83299ae032264196c970191320ca64b80c899065339db544c832a9cedaa2641964e76d51320cb27326a89906593193544c832998ed2a2641954d75951320cb46324a899065719c6544c832b8ae32a264194cf76551320ca663b2a899065a3191544c832a9cecaa2641954c76551320cb263b2a899065131d9544c832e1ee8aa2641970f64551320cb27322a89906593191544c832e18c8aa264194ce76151320caa73a8a899065719c4544c832b8ae22a264195ca70151320cae4b80a899065535d6614c832b1ce930a641958d74985320caa7baac299065339d3604c832c9ea9b02641964d54d81320caa6bacc09906553dd5604c832b1ee8b02641958c74581320cae3b8ac099065711c5604c83299eec996a21943e74181510ca1eba0c0a886533dd93214432d1cc8990a21968d644c8510ca3bbb2a2288658d5915114432e8a64a88a2196c932980510cb64992c0288659c545601443299eec996a0194cf764ca500cae5b8265280651d9c664940328eae3324a0194cf764c9500cae5b8264a8065b14cb615403296ae830aa0196c532185500ca3b388c8a80651d5c464540328eae9b0aa01943e74185500ca1eba0c2a806
  | 34 => 0xa11947771583544ca3a38ac1aa2658dd51619513287eecaa0a89953571990544cb26b1ac42a2659558e6115132ccac5308a89965563584544cb32b12c22a2659658e6015132cd2c5300a89967261980544cb38b0cc02a2659658d6015132cd2c4b00a89967261580544cb38b0ac02a2658dd5161d0d32c68a8b0e869964d72996434caacb80a921a65539d46290d32c9cca314869962c54d89434ca2f3b0a8a1a65565c05450d32c98cbb1286994ce75189434cb273a8c4a1a65939506250d32c98a8312869963754587424cb1a2a2c3a1265935ce6590932ad2e02a4849954e7518e424cb27328c721265539d64390932c9ccb21c849954c7550e424cb2732a87212658715363509328dcec2a2849956970151424cb2632ec6a1265339d46350932c9cea31a849964e5418d424cb262a0c6a1265539d64350932c98cb21a849954c7550d424cb2632a86a12658b59054cc932ad2e02a6649968d6490f324cb0eb20a919265565c0548c932d1ac9214649963564d46514ca3bbb2a228a651d9c664d41328eae3326a09954c7250f504caa639a85a82650f9d261d413287ae930ea09947b76540504ca3b38cc8282651d5c664141328eee2b06a81947471583540cb26318c4aa0651d9c460550328eae2302a81943f76550540cb1aaa2c22a0658e5516015032cacc7308a81966662984540cb1b322c22a0659598d6115032cccc4b08a81965a63980540cb35314c02a0659c9866015032ce2c3300a81963a64580540cb2d31ac02a0659a9896015032ce4c2b00a81967161580540cb26392cba1865535d762d0c32c9acbb1686195c97018b430cb2ab2cc3a1865b1d8a61d0c32caacab0e86196c762587430ca67b92c1a18651bdd56290c32c5aa9310861963654584430cb1aaa2c2218658e9516010c32c72a8b00861945f76550430cb26b2cc42186517dd56210c32c9acab1086194cf75588430cb27baac42186593d516210c32c9aa8b1086194cf70588430cb2ab2cc221865b158a6110c32caacab0886196c562584430cb2cb2cc021865b258a6010c32cb2cab0086196ca62580430cb64b12c021865b49856010c32da2c2b00861965b54580430cb4d2a2c021865965516010c32d32a8b0086196ca72580430cb64b92c021865175d84394832a9ae421ca41964c73597420caa6baec7a10659359763d0832b92e031e841954d75d0f420cb26b2e87a1065535d443d0832c9aca21e84195c97010f420cb32b2cc3a1065b1d8e61d0832ccacab0e84196c763587420ca67b9ac1a106517dd56390832c3aa9318841963654584420cb1aaa2c2210658e9516010832c72a8b00841946f76550420cb26b2cc6210651bdd56310832c9acab1884194cf7558c420cb27baac62106593d516310832c9aa8b1884194cf7058c420ca36bb4a6210659358e5310
  | 35 => 0xd0d5010ab4b9686a80855c9c74354042ae2e3a1aa02156b7250d5010a3d3b086a80855a9c84354042ad2e421aa0215727110d5010ab8b8886a80855c9c74254042ae2e3a12a02156a739095010aadb9a84a8085561cd4254042e56e8a12a02174b735095010ab439a84a8085d21cd4254042a90e6a12a02155a731095010aacb9884a80855c9c44254042ae2e2212a021568725855010a9d3a0c2a8085569cc6154042ab2e630aa02156a721855010a2ebb4a62808517dd95314042caca7308a021655539845010b2b29ac2280859554d61140428eaed288a021656639445010b2ab1ca2280851ddd95114042cacc6a88a021655635445010b2d29cc0280859654e6014042ce4a3300a021671519805010a3dbb2a0280859698d5014042cb2c6a80a021672615405010b38b0aa0280859398d62d5332cacc730ca9996566358654cca3b38ec0aa6651d5c7605533287eecaa0a99964e6358854ccb32b14c22a665995896115332cd2c5300a9996726198054ccb38b0cc02a6659698d6015332cd2c4b00a9996726158054ccb38b0ac02a665565c05490f328bcec2a287995597015143ccb27b2ec4a1e65939506250f32c98a8312879962d5458843ccb32b2cc3a16659959561d0b32c3ca831a859946d76d5042ccb26b2cc62166593d516310b32c9aa8b1885994cd7690c42cca67bb28621665995966110b32d8ac730885996656558442ccb62b1ac2216659a5966010b32d92c730085996696558042ccb6531ac021665b258d6010b32dc4c2b0085996e16158042ccb35aa2c0216659a5516010b32d9486b0085996c94358042ccab9386a328e651ddd95114732ae4e3a84a1994767199250cca3ab8cc9286651d9c464543328eae2322a19954c7250d50cca3dbb2a0286659358e62d5232cccc530ca91966662586548ca3b38ec0aa4651d5c7605523287eecaa0a91964d63988548cb2ab1cc22a4659558d6115232cb2c7300a91967261980548cb38b0cc02a4659658d6015232cd4c4b00a91967261580548cb38b0ac02a4659559661d0e32caacab0e871962e54189438ca2ebb6a821c65935966210e32c9ea8b10871964d54588438cb2ab2cc221c65b158a6110e32caacab0887196c562584438cb2cb2cc021c65b258a6010e32cb2cab0087196ca62580438cb64b12c021c65b49856010e32da2c2b00871965b54580438cb2caa2c021c655a5c05490a32b92e021c851946e76151428cab4b80a8a146593d976350a32c9ca831a851964c5418d428ca673b686a1465339d84350a32b92e021a851961d5458c428ca6cb80c99946517dd954cca32c3cc8aa6651946d76953328cb16b24a9994655a5c054cca32ae4e1a8ca31947776544518cab938ea1284651d9c664942328eae3324a11947671191508ca3ab88c8a8465531cd42542328f6eca8
  | 36 => 0x392a7288855c9c05394442ae2e029ca2217455390a5110a9bbaa852888559dd54294442b88e6a14a2217455350a5110a9b3a6c728885599cb63944428eaeda1ca2215677250e5110a3abb08728885599c84394442acae421ca2215727010e5110ab8b80872888555dcd4294442aa8e6a14a221536741825110aab398c128885555cc6094442acce4304a22145e731815110a2eb98c0a88851d9db5354442ae4e1a9aa22157170d4d5110ba2392a6a88851d9d85354442ae4e029aa2215717014d5110b8aa9e84a8885d154e4254442a6eeaa12a221715535095110ab3baa84a8885711cd4254442e8aa6a12a2215647258d5110a3b3b686a888559dc943544428ecec21aa2215667210d5110ab2b9086a88855c9c04354442ae2e021aa221557735095110aaa39a84a8885559cc4254442aaae6212a221564725815110a9b3a0c0a8885559cc6054442aaae6302a221566721815110a2ebb4a62888517dd95314442caca7308a221655539845110a3bbb2a2288859598d5114442caac6a88a22165a539805110b2ca9cc0288859c5466014442cb4a6b00a221659535805110b38a8ac0288859594e61d4042caaa730ea021656535875010b2aa9ac3a80859598e51d4042caac728ea021656635475010b2ab1aa3a8085569cf5094042ab2e7a84a02157271d425010ab8b8ea1280851ddc563940428e8e2b1ca02157271d4e5010ab8b8ea728085d21c95394042ae4e229ca0215717114e5010ba4a9c85280854edd54294042ad6eaa14a0215c87350a5010ba4a9a8528085569cf5194042ab2e7a8ca021752539465010ba8a9ca328085d494d5194042ea2a6a8ca02155a731465010aacb98a328085569cc6494042ab2e6324a021572711925010ab8b88c9280855a9cb6394042ae6e2b1ca0215707158e5010ab938e87280855c5c74394042ad6e4a1ca0214797610e5010ab539087280855a5c84394042ae4e221ca0215717110e5010ab938e85280855c5c74294042ab6e6a14a0215587350a5010a9d3a0c328085569cc6194042ab2e630ca02156a721865010aa639a84a8085179cc61540428bae630aa02147a76d4d5010ab938ea6a80855c5c75354042e90e529aa0217487254d5010a3d3b0a6a80855c9c45354042ae2e229aa02171953d095010ba529c84a8085d254e4254042a76eaa12a021719535095010ab5baa84a8085721cd4254042e94a6a12a021749535095010a3d3b6a2a8085569cf5154042ab2e7a8aa021752539455010ba8a9ca2a8085d890a5154042ec28528aa021752535455010ba8a9aa2a8085ccd095154042ec484a8aa021731425455010bb0a12a2a80851e9d85154042ab4e628aa021559731455010ab938cc8a80855c5c66454042ad4e5b1aa0215387458d5010ab4392c6a80855cdc56354042ae0e2b1aa02156a72
  | 37 => 0x9959661d0a42ccacab0e8521477765445190a9aba0c2a84858d9d06154242c6ae830aa121666721855090b32b90c2a84851edd95014242aace3b16a6a155571d8b5350aab38ec1a9a85555c760d4d42cb6c1306a6a154d721835350a2fbb2a629a851ddc56014d428e8e2b00a6a155671d885350aaab8ec429a85569c36214d42ab2e1b10a6a154f705885350aa6b96c229a85475d06114d42a9ae4308a6a155a701845350aacb80c229a85535cb6014d42a9ae5300a6a1557715805350aaa38ac029a85475d06014d42a9ae4300a6a1556711805350aaab88c029a85965806014d42ca8a730e86a1654535874350b2629cc521a859314f6250d42c9ea631286a164f539884350b2ba9cc221a8595d4d6110d42cb6a730086a165b535804350b2ba9cc3a12859514e61d0942caea6b0e84a1654535874250b26b18a7a1285d114e61d0942e88a6b0e84a164c535834250a2f39cc1a8a85175ce60d45428bceda9aa2a145e7614d5150b2da9ec0a8a859614f6054542cb6a6302a2a1658531815150a3bbb2a228a855c1c151145428bce730ea0a145d739875050a2f3b6a6a8285179d85354142caea7b0aa0a165453d855050b2ba98c2a82859514c61541428f6eca80a0a1570715405050aab38ea729885555c75394c42ab4e1a9ca62155970d4e5310a3bb8ac1298851d1c56094c42aace2324a621555711925310aad380c929885565c06494c42a9ce5304a621557715825310aaa38ac129885559c66454c42aaae3322a62151e749855310aa7394c2a9885531c96154c42c98c5b02a62154e729815310a8e3a2c0a9885531c96054c42aaee2b02a621554715815310a2fbb2a6298859554e6114c42caaa6b08a621659539805310b2ca9ac0298859354d62d0c428eaeb30e8621656539874310b2aa9cc3a18851ddd561d0c42caca6b0e8621655535874310b2729ec4a18859354e6210c42c9ca6b108621475759844310b2b29cc2218859554e6110c428eeeab088621656535844310b2aa9ac2218851e5d66010c42cb4a73008621659539804310a3dbaac0218859694d6010c42cb2a6b008621656539874210b2aa9cc3a10859594d61d0842caaa6b0e842143d769524210a36bb4a9210859398d53908428b8ed29a842145e7654d4210b0fb9ecaa1085871cf6550842c3ecbb1a842161f6518d4210b0fb2ca6a108587d955350842c9ee7b2a842164c73d954210ad2b8ca8a108593d976350842c9eca31a842164d7518d4210b472a0c6a1085331da5350842c9ecb29a842164c6354d4210a663b2a6a108593d955350842a9ceca9a842154c7654d4210b263b2a6a1085c3d915350842cb4a7306a221659539835110b2d29ac1a88859654d60d4442aace7a8ca22155573d465110ab9386a3288855c5c35194442ae4e1a9ca22157170d4e5110ba2
  | 38 => 0x43ad2e430ca021d4c7250d5010e37390c2a80871b5c86154043a76eaa1aa021d5b7550d5010ee439286a80871e9db5254043ae4e3a92a021d7171d495010fa439ca4a8087d290e5254043e9287292a021f48735495010f95a1aa4a8087d290d5254043e5286a92a021f49435495010e3d3b0a4a80875c9c45254043ae2e2292a021c7a76d455010eb5396a2a80875a5cb5154043ec4a528aa021f61529455010fa921ca2a8087d450e5154043ec4a4a8aa021f61525455010f99a1aa2a8087d490d5154043e6286a8aa021f51435455010e3d3b0a2a80875a9c85154043ad2e428aa021d72719915010eb8b8cc8a80875c9c74354043ae2e3a1aa021d5a7290d5010eb5b9286a80875a1c94354043e36e8a1aa021f4b7250d5010eac39286a8087d21c94354043a90e4a1aa021d6a7210d5010eb4b9086a80875c9c44354043ae2e221aa021d5a73d895010e9c3a2c4a8087561cd6254043ae6e2b12a021d70715895010eac39ac2a80874e9d06154043ab4e630aa021d6a721855010eb4b90c2a80871b5da52140438deeca90a021e66529845010f32a94c228087999496114043ccaa4b08a021c75769445010f33314a2280879958a51140438eeeca88a021e66625445010f32b12a2280879a94a6014043cd2a5300a021e72519805010f38a8cc0280871edd95014043cd4c4a80a021e69625405010f3930aa0280879c58550140438eee2b04a7a14747158253d0a2fbb2a629e859654d6014f428eaeb30e87a14777558743d0b26a9ac421e851d5d66110f428eeeab0887a165a5358043d0b2ca9ac021e855c9c05394742ae2e029ca3a15567319251d0aaab98c928e855c9c06494742ae2e0324a3a156572d8e51d0a9b3a0c728e851d5db4394742ac8e4a1ca3a14757610e51d0ab33908728e85595c84394742ae4e021ca3a15717010e51d0aab39ec528e85555cf6294742a6ce8304a3a15567318251d0aaab98c128e85595c86094742ce2c0304a3a145e7318151d0a2eb98c0a8e851d9db53547428ecec29aa3a15727014d51d0ab8b80a6a8e85559ce6454742aaae7322a3a15727099151d0ab8b84c8a8e8559dc96354742ae6e0b1aa3a15707058d51d0a3b3b686a8e85591c943547428ecec21aa3a15667210d51d0ab2b9086a8e855c9c04354742ae2e021aa3a15577358951d0aaa39ac4a8e855cdc16254742ae0e0b12a3a15577358151d0aaa39ac0a8e8559dc96054742a6ce8302a3a15567318151d0aaab98c0a8e85595c86054742ce2c0302a3a14777654451d0a3bb8ac7286851d1c563943428eaed288a1a16566394450d0b2ab1ca2286851ddd95114342cacc6a88a1a16556354450d0a3dbb2a0286859658d50143428beeca98a72164e531894390b1ab2cc3a14858d59561d0a4299ee6b2e852154c735974290b26b1ca7a1485
  | 39 => 0x8621e2c72d954310f17b2ec4a18878bd946250c43c9ee5b2a8621e4c72d954310ecab8ca8a188793d976250c43c9eca3128621e4d751894310f472a0c4a1887599c75294843acae3a94a421d6a70d4a5210eb4b86a5290871ddc560948438e8e2b04a421d2f7550e5210e663b2872908753dd54394843acce2324a421d65711925210eb5380c9290875a5c06494843acce3a1ca421d6571d0e5210e363b28729087539ce6094843acee2b04a421d64715825210ea739486a9087531c94354843a5eeaa1aa421ccc7650d5210ea7baa86a9087599c66454843acae3322a421d6671d0d5210eb2b8e86a90871bdd94354843c9eeca1aa421d4c7650d5210f263b286a9087c3dd14354843a5ce930aa421d4e739855210ea639ac2a9087539ce6054843a58e8b02a421d4c735815210eb3b8ac0a9087591c560548438deeca90a421e65529845210f32a92c2290879a54a6014843cd2a4b00a421e6a529835110f34a94c1a88879a94960d4443cd2a4b06a221d6672d465110eb2b96a3288875c9c35194443ae2e1a8ca221d377550e5110eabbaa8728887711c94394443ae4e1a94a221d7170d4a5110fa239aa528887d190d5294443e8a86a94a221d727014a5110eb8b80a52888759dc94394443ac8e4a1ca221d3674d8a5110eab39ec5288874d9d06094443aace6304a221d66721825110eb2b90c1288871b9c860544438dae4302a221d377550d5110eabbaa86a8887711c943544438eceda92a221d7270d495110eb8b86a4a8887d11cd5254443e4e86a92a221f46435495110f92a1aa4a8887d150d52544438ecec292a221d72701495110eb8b80a4a888759dc94354443ac8e4a1aa221d667210d5110eb2b9086a8887551cd6254443aa8e6b02a221d36741815110eab398c0a8887599c86054443acae4302a221c6d769485110e37bb2a4288879994a6114443ccaa5308a221c77765445110f33312a228887995895114443cd4a5300a221e69529805110f38a8cc0288879a9496014443cd2a4b00a221e71515805110f33294c3a80879954a61d4043ccca4b0ea021e65525875010f33314a3a80879958a51d4043cccc4a8ea021e65625475010eb5396a1280875a5cb5094043ae4e3a84a021d7171d425010e3bb8ac5280871d1c56294043a76eaa1ca021d5b7550e5010ee439287280875c9c75294043ae2e3a94a021f487354a5010fa521aa528087d250d5294043ae4e2294a021d717114a5010eb5396a3280875a5cb5194043ec4a528ca021f61529465010fb1292a328087d85495194043ad4e428ca021d69721465010eb5390c9280875a5c86494043ae4e2324a021d71711925010eb938e87280875c5c74394043ad6e4a1ca021d687250e5010ead39ec5280875cdc56294043ae0e2b14a021d3a741865010ead398c3280875a9c861940
  | 40 => 0x20008000000000000000000002000000000280020020000002800a000000200100020000002000000000700020038000000800a0070014002000600300020020006001001400280000018006001800e00700000000004000000400000000010002003006400000000008000002000000f800c0048004005800000080000010006000000000500080000010001000800200040050002004000000600060030002000801c00b8004004000a00900000018004001800a0000000002801e00d00340028000000000400080000020012001001000180000160000001003c000800a00b800400000120000030000800c0018014000c777158252d0e3a38ac1296871bdd95214b43cd2a4b00a5a1d727014a51d0eb8b80a528e87599c86494743acae4324a3a1d727019251d0eb8b80c928e87599cb6394743acae5b1ca3a1d5573d8a51d0e9b3a0c528e874d9d06094743aaae6304a3a1d667218251d0eb2b90c128e879c58060947438dce4302a3a1c6d7218151d0e3b3b6a4a8e871d9d85254743ae4e0292a3a1d717014951d0eb3394c8a8e87595ca6454743ae4e1322a3a1d717099151d0eb3b92c6a8e87591c96354743ae6e0b1aa3a1d707058d51d0eabb9ac4a8e875cdc16254743ae0e0b12a3a1d577358151d0eb3b92c0a8e87591c96054743a6ce8302a3a1d557318151d0eb3390c0a8e87595c86054743ce2c0302a3a1c777654451d0e3bb8ac5286871d1c562943438eaed288a1a1e666294450d0f32b14a2286871ddd95114343cccc4a88a1a1e656254450d0e3dbb2a0286879a5895014343c6acb30e8721e35655874390e67b92cba1c87531c965d0e43caacb30e8721e55655874390ea6b9687294871bdd95214a438eeeca88a321d35741855090f1b3a0c2a84878d5d06154243cace630aa121e55731855090e3dbb2a028487599c763d4943acae3b1ea4a1d6671d0f5250eb2b8e87a9287599c760d4943acae3b06a4a1e6b609835250ea6b98c1a92871bdd95214943a9ae5a18a4a1c77715805250e3a38ac029287599c76314943acae3b18a4a1d6a70d8c5250eb4b86c629287599c74314943acae3a18a4a1f4671d0c5250fa2b8e8629287535c34314943a9ae7b08a4a1d2d741845250ea6b98c2292875a9c06114943ad2e0308a4a1d4d73d805250ea6b9cc02928759dc56014943ac8e2b00a4a1d2d741805250ea6b98c029287599c46014943acae2300a4a1e69601805250e37394c1a8a871b5ca60d45438dceda92a2a1c6e761495150f35a96c0a8a879a14b6054543cd6a4302a2a1e68521815150e3bbb2a228a875c1c151145438dce530ea0a1c6d729875050e373b6a4a82871b9d85254143ccea5b0aa0a1e6452d855050f33a90c2a82879914861541438f6eca80a0a1d70715405050e1ebb4a921887175da5490c43c5ee5b2a
  | 41 => 0x2003800000000100008014000800000380000018004001000e00000020018008002000200100020000000000800000000040008000002800600000000008004003800c00480040010002009000000080040000000000000400b800000a800a000800400a000000000040010002007801a002000000180060008002000801c00380060000000001801400c000c0008000001800e00200060018002002000a006000000000000038004002000c0038006001002a0008000000000a0030004000000000000100020002001000800080020000000000800000000000000000002800000280140008000007000400a8000001800e00200040020000000000800000000030006000000000d8018000000000000100030000000000000300020000002000001400000060018004000800e003000e0000006000000a00100020000000006800400380000060000007800c005000200600040000000002800400500020010008001000c001001e0008002001001a00100040070000000000000080020018002000000a000000200100040010000002000c0008000000000400000000028000000000c0018000001800c0000000001801200680140000018001801a001000400600060000006000000000480000008006002000a0020004009800a0040000007800e000001000280000000004000800800000000000008005800400000100080008002000400500020008000001000200180000010014003000000e8010000000000000000010020000801600080000028006000000000a8006000800400900020008006001000000200000000014001800400c800401100020008002000005600180000010000000000000080080028008001800600300120000000000800a000000a00180280020010003002a00480040028000003800400100000008004001001400100020008000007801e0010000005800c000800c0018000000800a000000400100240030000001800c000000400700040078004000000a0028014003000c00080020018006000000200100060060028004800000100100000002001000e0008000002801e00a8000000801c0080012002800e00c0000000000a010001000080040000000000000200000120050004004000000000180020002001000a000000200200040018004003001200080140000000001000200000000078026002000200000040030004007800e00480040000000002000000080000010004001000800100000000016000001c004000c007000400000060010004001000200300020000002000000800200000008000000000a0000006008000400280000068002000000800080000000000000800000000000000000000800000500380000018002800e00c0000000000000300000020006003800a000800a001000600
  | 42 => 0x8008009001000b00040088000000801200000060010008003800200480040030000006003800080040008000001801400000020080000000800e000800000300000000000000800000000200018000000000000000000000000000800c001000e000000000100000020022001000e000001800000040000000000000e001000200500000010000000800000080000000024003801a000000a0170004004801a0000000000000600000040010000000000000280000000000002801c00e0004001000200080040020002001000a001001400000020010002000000000600360008000003000e00180000078002001003e0008000001000000000020000000000801e00e800600000020038002014800000200000038012003800600180000020000000800200000060038002000000a003800e002000e0000046001800000000020010004004000000000180068006007800600b0040005000e00280000000000000000c000001800100060020050000801c006800200300060008002003000000300140000002004800200000160010008000800a000002c00100000008002000800c00300020028000000801a0028006004000c00080080058000007001a0030004001800200b001c0040002004800a005000800000080028000000000000000000000002003000000500040000004000000a0038002000800600000240000004000000200100020000004000800200580040000002005801a0000002000802600080000000002002804c0028010004801000d8002001800800100340000010000000c00180000028006000000400900020028004000800200080000000014000000000380060038030005800000280080050000000000000080400008000000000c00080040020000000000400000020000000002000400200040008002000800200300020000002000800c001800600780140010006000000a00000020008000000800200100040000002000000e0020000004800000b000000180000008010000001c000000200480040000002001800000000040000006000800000680180030000002000400000000000000002800a000000800000060008006000000a000000c0010004001802200280020010004001000400480020010018003800000900000038004000800800000060000000000000a00100080090000001000a001000200080040000004000000000200060000006004801c005800200380180000066001800a00080080000000003800a004802e00300120000008001800c000000000080000000012000000200000020010002000000800300040000004003001a001800a002802c0000008002000a00080000010000000801200200040000002000000c002000400180040000004005800600180040000046000000200580
  | 43 => 0x400080020020004000001e0008002000800200080000030006000800200080000040004001000a001000e009000e00c800a000000000000120000002001800600180000008000001001000000080008004000000000400120008008002000600080080010006000800a0018012002000200000000020028014800e001002600500080050004001802c00280040050000005000c00680020010010001000800100020018000001800e001800a00080000000000004000000180040028010000001a002803a006803000000040018000000000a000800400080000008000001801c0038020003000800080040008004002800000080000058006002000200000020018006000800e002000a000800000100020018002001800a000800a002800000080380040004007800600080000020004002000600180120010000003800000000260000004004000400c8000002801c00b000e001000a0078014004800c001801000300020010000000800000000020008004001000000200120070000003000200100080010000001806200280020040036003000a00080100000002005000000180200000000000000200000000018020000000e000800400980060008006004800200200000020000000000e0008006000800400000000018000005000600000000000000004001a0008000002800c0020004000000200180080000004007000000080200000004000000a00080000058002006800e002001c00000020030002001000800000020018000002001600100020000000001000200600060018002003804e0030004010800000000000000000006000000080040018000009000e00180000008010003800800580180038006001800600300020010014002801c000000000000000008000000800e00800040008002000000e0038008001800000500020030002001000c005800200100020030004000800a00c000400000020008000006000600100080028006005000600100000028004001000c00c80080020000004000e0010000000000600300060010002000000a000002000680020070000000800e000800000000000020000002803400080040010006000001400000160000000004000e0018000006000000000000010000001000400180020028022000000a0010000000000400300000010000000000800c8000000800200580040008000000000e0020004005000200000040060000003800000000000058010003800000000000000000000800800280160010012000001c003800a00000020038016006000600080060000024004000200000000090014000004a00b0008002000200c80060000004001000200680020000000000000000480000000006000000a002800000000400008004000000000000040000000000001400000000
  | 44 => 0x160d9c6b200018623c642d10658000000000050c06c6000023c5985a73078c3dd4ac1776108d2601554df667ad0db67b928637f023253cd724000000050754190000000272800000000000000000000043400000000000eac00001d31c5c0005d98305000115700019a332c921b51d8000000000000000006380ec25d9c0000000000517d0f00000000000155d000000064ec68323dcdbe0000000000000000000000000000000188917700000000000000000000000004d88000283800000000000000bc600000002ac52681c2c00035b400000008f84b6059343551f400018f20001a743e24d6f4fac5ed548d8631ad869f63f50b81c493094379642000000000000001d88000000000000000000104000000000000000000cf88870001a904c08eae64916e41ce961f12c000000000000000000000183e2ab4000000059f42f580044d1877695000031d1550000000000016bf25d58ce449d3b6610d27265cd75603a02963f5838f42ec00080020050012001001c001000000d80000000000001800a002001c00200060018022002800c000000000800060020002000000200080040000000000000400000000018004000800a000801200280040028000007000000080060008012002000400000080018012000000c00a80000040002000000000000020018002000000000f800c001000200180080000000001801800000000078014001000600000040010002000001a00c001c000800200000140000000001000400080080000010005800000000100030010000800000100000058028005800000700000008010000000000480020000000001800800480020068002002000000180000008004000000c00400000000000000000000400040030002000000400000000000000000000200800000008000003800c00b80000018006001800000000160000002001000000700080000006000000a000003e00880060050006002800000280120008000001800e000801000900040020000009001200000040000000001001000000000010008001000200200000008000001000a00000000020006001801e0008000001802a0008000000800600380060010000003801c00080000008006000000400b000000180060000000000800c00000060008006001802c0010002000803800300220028000006001800000220010000009801c0010004002000c0050016000000600200000008000006800000000000058044000802e00f00000038002000800e00000040010012006800800100020000000000001e000000200280000038008002000200200020018006005000a0040002000801400f0002001000c0040006001001c0018002003000200480100058000000000a0048018003800c00000080010008003000c011800e0000000005000000a0
  | 45 => 0x17f900a00013be4d04306069c58e00010da3f500001ce490e5ffda380a44f6427bd18f53e53833e20249578c00006b589c699c000000035d2988f0d41141ba060400027b15901ea4f0b180d1463abc63f0000756584526d595400031480004728d1c10c579465299e8398052633b50cd21cd7530f4033d3fbd6d400000000ccce0e444c96915e12bf5140544415cbe2584896f000000000007252be99bf00012b30001a1c6930000080107800010470000000359901d54180002c70000000000043d4000096065b4f54d5823f8435000000040583e40eed5020000000416000000000000b8957d10b80150b991646220130694800037cc000689400000000003a0c000379552119bc81455d588e00000004168a9f000000045fc75962918f602c0000470d143000070441b0a6c0130ed300003c429709d25b70d300000000000198600017395cb99cd4ac846f446d9501440d3e2489398426814a07e000040100005ae00000ea4207000056515a90dd494d5433ef46b446000000001a3709519b75310000182400042c923637e0e7a5ed54e300000003584a340f0000000003bc00000004530293256c548228537a00018eb000000053f800021e993336d800000000000000000653000000000002e6400000013f00000abc42f858d006932f000091000004be6570000003c0000000ec70ef80005bc0000000000066597ed314cb4d29e86fd67fc0005c00000571000000014fc07d419f255028d31c54ba4ae45af4238bad31386621ac009b000016467100003adcfe15cd400019746a03b315d216d8a7000005bf420000052e0000000169300000004e00000000005651c40000c914922c5989450f559a4d350460000000627810d00010360000faa30c8000220d5b52ae0f9046b580e1a4d559568170c311400000009c053fd0ee27c800057b80003f9994e000013f0000bc300011886a3d2e538e81aa39919bd15d82f60000dec05800000000b8a000000066380005e054b71aa0447000000000013190000dd10000a932418ab300017250000e9e39880005bc432f005cceb44dc0002dfd4bc16f89f900000000000000690083e0000dd81aa43400c9977317040000000000471000038d8d113e499450000f6945c15b41ae110900014940000d7500000004480c3816e98ca3a441d73df80005de0e870d14e20277054c43f81b052298580000b100000f6f1960c8d18ecd13240999f47dc000157094c00013ec6208d5622a0e0c449091b3f554111ed00000000bec53b463132b844829119370000000177438b162400000082b84700000000034d65e04100370000000000000001be1fd4000014c9954a2022e0000000000122f69a400000005475785a885d2c000000085d10fc3181acc00046ec369658400000014040b700002f696c000016ec1d70
  | 46 => 0xb542ef571352c000000018c3000158d00018d12f900000f7c96412117eb4e5c51a383d84f000000014e02cf46c848309dc59d45480000001039269800000004905860c70517819300002780001a5c358c5a70000b40079459405b90d90000000000000000000003e1d5493d20000000000000007e5679849d19a4c17187c0000dcc00028d8000193566f6845a480c7400049f8241212913c62e572f089c02616a92ab519482f2f510df0238c970ed48a6515d89837e4ddd4360a2f306d03b2cdc3003248000000080429a0f4f53a4b0d37fd13d5bd880660186603f8c39b23a800000000003c890ca00000001348166135ca8117dc0000ec800007818504ce00000000e333b6083555fccc500015eb2af5444000148100010e011f8000000146b1e84c0633755cc0f3c99b2fac0000001a21000110a0000a9d33ed3014440000090c0b50000b8f4e7474a0000000444417d000000000000005c84000297400049b8000598c0000000000000000000013ef00000001c9c00040dc40255b412f20d02a51d20dda621cbcb3080e7f4a7550a5474e84648ccc70f8cd1b46853c7122d78c48443905ff04b9445819d58e98e5564c56100d0c4b00006b500003e8486000000018e96158000000000052b80005bb56f20000000242400003851fe2f4c00065c400000000003bd429a00018a667e800000013a700013fe3d6000014d00004c4859063f8b32190000042100000000000424ca1c071d07c2810f33327c3ff34386076a6d0331ef0adf4bc4ddf5ad8b295014a741234f626791652197c68a4a7d0b906f0559698150b00000000b9ce1d2c20ecb0db10b300014ce51f836d000000069dce0011f05420a306d234759d74850fc13a480000000000000000062d890a0000641000000000008b34cdc80b59d80a400000003ad4000000043c088439f0bd50ab0d0c2e52c9045800005e8615c4c723cc00000019990000000000000000000004d2c68d4264e63057800060d4b0e00386c942d946d000136a1d7c89c54e52b72780e2b39488a41a0438100000000000000000000038bd595235d0ec000000000000003d1977153a06fe3f1825d2fa15993be158c4c3970e4868fee0000b8169c000000000002de80f9288d3703495106464d02522e19f3562091235f1a01508400000000002ef8000472599336e91c100004ef51205f41044c8c4cb800000000000000dfd000081933187000000000000000000000003cc52a201719c50000aaf0000e43000059c3c90506060ced44ded6804420d2c20b507352bd9ba4ad800029e17230000a5b519825a0a6400005d19085500000556000000018bf00001564e515df4ed40004bbd47354ccbde03c80006a3400017fc00068b8f2e4d5d61600018b312d800068f91da2fc919463dc90f04e5501099c0000000000
  | 47 => 0xd49c54986078d920b8026d000133b00017e900000000001a0c0000000000000052ad75750b574900010c648f000033f40001faccdb4555445141c46b0001915228cab247c44b3207cf1c0000000189c1ea26340005af4b023625a3f26743586909368333931500000005b1997756a8ac52f8008711ec74b29f80002d8c95a000171b526515d4a0800023ec4d60000cc000013e500000001b08000000000030bc00014e59d10000f9e000156017c46013e18000196815000000000eb46104c148ff00005f3293003631cc0004a0c000000000067180004eec0001430adb5a1c00041497cf659c5922f10afb1b5160e5fa826e02c830751c838c13b1a46529c159429cef60c3166e18d874619c435013b4b2365a0bfa3f3577d608d15e27082c24b9045743904ee2a54037032d15c04a153b0369a1e18216fc4cccce729f4b18000029c000000028400006320000000101f597515435b07855b2c000000000022309d30000b485314af92eb83270b25a5d05a17030000000604c235651c0000000000152c0000000000000079615b136021480001200894507c00000003e2494121245b800000013ee000147a0000000019012c000014600000002a280000000000000000036cccb80dd800000006cf255834708dcc284b7c00000015221abc000342458a5db02ed000190b1dd9a532d40b931a2c8e068ccc2609bca3c00008ae341c000000008c000127700000000000ea300015f138c0872002957159b46385f5400018480005ad138557053b21dcc84931815d567dc00023654dd36dc8a24b1000012ac00000005695c7c0005150f1112b84eb237421600018bb361c0000000fbb00016d7000000004f44f86124a693b6c00023b10cf4b0461100019ac3f1c0000c49715322582252d0e162938bf81460f0c3f7c0631ee559b00002304e3598b2658000453cc820ecc000000020e0e94a4b00000000000f9c0018000025ca924fc4000644000006d10c945040002eacc2e624d17653500003cd1184034970653005045b3579d00000000000000195c0000001a9a0000a160000ca40000be95a78f8b0e200001ca00005add8ba0000aea3e6521f3c1400002654ad640094b53d40000000000000000068e8ddc04f8000672461820c425000008a7551c264000116f000184e09d04e500012cb000000000009a3486432146fd4933f3837800000002e180963ec58de1f2c0000f4c000402000011c00001e41a4a38b400054b929067f1714000039850880000000f7800000004c941b9287cc140e353ac000108a24c996f00241d035e103d34e46533478ec05d446b15a4906a3f010fb36d400000000001ffd29e508c0004db00000000000559867b5bec91f1fcd8d3000193056dc00000017a8000167e572907253c982d00018dc08f5489154000000013c1655
  | 48 => 0x2c00000009114bf4000066c5d4552d2e84db573000012cf3bdc4611144000000159c586841f24142aa2dbced62b0991466981f05c794154a440002c28e2627a800000000002b8c0002b9c5005f9597d000000000000005b1d0c700012975f9837a3facfe0000175b36095a7000000000000002c30fc900002bc685931600000005ac4ae13058541000000000006f6483c1c159a800016580000cfcc07535c000364400017e801f000000041c400000000000000000000000040e893a000000000000001e7000050f83440000000000101438651e5456474f0bc8901000085b000000061f0f4d00013e1017c0003b050cb1799644441c6641f8400000018b7000124339503f43b153c252a82ec00001ef2ee02c52f60d2261ed3fc05f0b2238ed7c03630000000018900003e026e05545fe92fa17b184a00017e703b00002ad4c0c26c96d90d94d342afd82a3994b1a4bd52471f5c31132600001a0925d3ed02b1312800013c9a130271a12207488e0cf0c015ee991a4d617414b30af70f98cd65b097e349e40234d68e5a0b6d3b941bc0005b58bcf35102022a98a8d13414a5000000058c04fc2f9c4b857883d96640051380cee9475c194315c35f42d09535434489541c2a60268000184c8e10a519f61fc40000e745705bdc45f00011af00003ae34208fa4b9c79e30e4b4a00019a410380001c800003c5800000016aa000000023acdad4de4000000198302b81ce00000001bb40000000a9a00000000000cef18d059100147984f7504d02054df168d63211288500e1c000224d3590000f974a996013dc800000013c532e40005f4cc41048d5e800017e4519ce4f17d95c927acf2b3e9c00015e45cb00001264dfc0005cec2810a894a3533107015603f91c1c10b4a01187000000000000000000b7c4714f494fdc0000000000000081a1f4520d37410175dbc00000017182560b6400000000fe910d03bd7ac4d386e968ada98000164657fc0004814c9d44ec000492580a0000000000000000010d200018693fc40003a6c5d531407be4edd51300000001bd189d043c00000002a0233d859000124e1f2800000000002734000000000039c98924cb138f2cf167913a80001cd000034d4fc81738000557d31a3418d0f3b10000265ccd241391f039ec0006578fd93c0800000003c500000005c2525f01480000ea86280000fec000000028b00bf513c57d0d5400000000002ed070e00000000000bc9000000000000003ed536700016033d1c00036114d259f53722d7952917000001bec34b0000c022bf4f5b35c85053bb911830f14e0000000002f800016d5296582d3145da4455179c67512d04e05a040004b54000000000000009ac021079a50dd7a44c6c0002ee8f6800000001f34000000185a178083b34697e8392046d09816954df866848d06b
  | 49 => 0x5938683cd4f50967084cca961ac000687400000000005c59210000191710488cb47643421cf59760030bd154683d41c615275f585da00e00b6367c00000000323634203000000019e581a0bfd4cb51bcbd2000114744640000000000199d1951fb120b0c8000000012630000ea04f5c21a00008fc000109d0001636406c7f041319130c40c7c0000af449183b10f0cfa01af87a602cc16b0d6400000f91be14f84ca000152a0be4eb90000af606fc9402b297830a14e153c780006a00ca566d56a730cd2231c4477466803f646e0de149cd6964f994e500000aa0040102410545c69e00000000c37000167000018f525040f300014d30000000000004500000000f2000000000000001a102e9c1903174745233560a66a035e00009075a206ec58080003b2400065349a84e8c00000017de0000000350404f19c15920000a1a01380000b8400000016d11bd51781158c9a25f98a11b345536778d2107a533a43a872400007b6000028400000000000000000000000008ed5fe40003600a6e000000003180001c24000360c000000009e6020000000000030755a300002ca10900002fdc5ac00008df0000cbc687d83d113800037480df3d6800038f4000000000000000001428000399800000013730000f7c2f313cd0d3923b3d81392637d5d600006fa35f4000000135b00017a968b41854b7800031a59f500009c517301434ea8000000075e000011e00000005d2904341d400060f0000000005a529046e10d8ba64f4400031a865c3698d5514dda050000000625995600b400000006b718d516600000003a4c0003ad00000000f183e0c8d000011b900000001ce000000000004ab4f03060000000007915c7129c1dbc0005bf86c0146cdcc0c3994400008ab00000005b380000000ea400012b553bcb19061011a35a80000000000000000049c000026a96575be8e4e2f7400060249a50000000000076128a0000177c0004b502e31ca40000000ce8336494a473cd4b00000003bf000000000002830000000000000010c44e240000001114419c000581957800000000000000000050320840000000a960000000092c00062f40000001a3c1ae47b3368c0003efc0000000f844e28429000000047d48232468d9308c40001f90000041c079000163e00000002ff05a924c417100000001f892bb000000043d0000127d6380000e132c7400055218bc4c8881733a8a8b441545837153a400007f643e800033b1654201c0000f600000000000330d45b0000c3f0000000555c000000000031ac00000000000000000000003a00000000000000416c00000000fb3c1129500017fe00014c72470cfc00010ff000000000000000000000000001100000000001860118c000000149e45a80001c0c1fa00016210e4d48e61e40000000d9600a16492a088f218
  | 50 => 0x27d40100000000000000000020c000000000000005ef400000000003d2c0001fb406f00001fb000086845000003570a0828fc2d76a300002efcd99000192d340c2244674d7764e015a392c00000003220b1c0002a640001d503742a186860f5990e000000009880000001a2a110d9f90cb906146996b94508a171be40001b3800000000001b54a7c0200a5e000162a000061e029c0004c0056803e0d1200013df0001871062cb1224905a140c00002cb4000106c000000000032a92c031b000001556a924ad04b5bd01634b880001b290911a88d473bc84090000000000128f000045900000002c5c0000000001000121c29900000000000000119b04e10a2000000000000002b5825e0001258000082c58a52e03a39a89000193200014ca0000fd2195481828b9812640ca60393047d08158420d30ba9408c0006a70fda51a0368171874c509da85022cd5e0000000469544b20540005c280000000000605400054f0ad425c07dd5eb4ccc0000b150000ed706e0bf9121850b0d987fc00000001a1588f47f52940000000264da29000000000018a06484f0a61f99b603340000001927363cd760accd0d18a97f6674c5675fcc0624ca96344cfd65a67ecc900450ce30c113910e64d3b053800003b4000262978028c80000c345c700005ea543987d3ac532432ec000510c3033db5a235ee0c7e231d0d70000cff00000000000000147cdcd01d400069f8fc34f6cad22fd819834ccffb40b0d1537c0000539800000000004e8400031e09b500015801074000000141a485956e5f412a752c81dc4f683c25b05a0d35fd24158a110b2000e040000000126c00000004960000edd00000005309591000000025dc000641922117590015aac6a10001429000151c000180d0000e140000000012d51767480005d1598f42fc00052f93ab04604945650ebe000158700014dc37540003a60c5b39cc0003d9cc400000ad958900000001a64094818a69992520edcb7e1ced6260000b4b2a3912d0a54000000000000004130000000000000053680006700899000000000000000000aff00000000000000000000061c14e746580002dd000052155af44019af415124d0000000000000000007ea365c918424921e044196b260480f000193637a40000000000000000000006e01524c7500000000000000000cac368bcf4250241415fc905c0fc8000322c5bb00000005009a4e1b1da76111082200010e321397db18645012e1028b00000003dfc4264becbbb4d296271c880000000000000055d2e581ab465c000416577b3f700001a9d0050840e804de0bc863480000000b4700000003a04ee706ec00067585c8633d3040224daa653c000267827a00009a16788b0b004cd4c0430fcb5c6816f064909846f020a2a0c0001d99020549979f14f590d000000010dc9
  | 51 => 0x23a14f0000000154663bc00000002ae614800000000003e88b6061315c32fb400034140004dbd2d75ccc2fc31bc12b00000003ff1a6e53d053f056c0004f24a9406b80004e4c000055c000396c2111bf00000000ac8480400032bc93f1fd000d66a494f657400000007d4295cef318b91ab00000000000cb70001a021028000665c000000097162b4094000188c059c0003d6589168280000000000172444c0ab165c30f99cb00016a2340400023d097f0000000000000000000001790da01150000000000055a52db4f4d16c2c6d4e1160c00026ac36306dd5da54440e0230c0002ebcc475e9d84000016d3051d9b1198423b60580bc4fc8b9f40fc6910020d9b3a284143a1400058fcf6e0b40c3100000003a500000000eb212d57550d28000646000012bd08200017d857e886f13d00000000000521c00001111f8133da9900000a31c401220000000000000037c80000000000000000021c40001268e790000000000000052880000000bf45cc40ee2ddcfdb54f8fa144cc5d00574cc938c582758003ce65453a63fc9a58404c6df379d28a15dda87294c61d2320c1c000000006c80000000e230000a2d2c140006924000243000026e4a3346900006770000000000023e46662c0400028f51a300000005f18000000000000000004d44b2f000000060b8000325800008a07aa4e1804029c8e054908e95251c8e90e8400054c516565f100d00ac88a221853a3d51631000199800009c80000000000000032b4000219c00000000000000000381ca0d0000b490001a92000194b0000000420da2c136c00042c07c900016eb00000005dc86e2107867c5fc0000076902b37a96683c540000000acc00000004ee0000000109503616c546a80f13084826000000025b8fd3000000026dc0003d840000000000000029d00016e91e319f824b51a200006c829a956a3cf5475099933220dd7d92ffd60c2e78c723b28bc70000ce044a80004ba94a121a8c25000157200001c41d9ced9000000004b56c91a5ca8f46c022009f5220000000051ec00000015bd285488800019194eb45170e24a5f000182f0bc40b166255ac61bc5820000000143400050e8bfb00002925fdd93e691d1a7000186727d80000000648000073c0000c5e000000045ec0000cdc0000930000000156c4045207304800030ec00016889de1b840000000dae63b42042e1522515cd5240000271282ce225da15a8000000000009ee00001a32524000049d6a626000001ebcc0b1598e755a8578b000000000000000000aa8353c21707d14db4f38dcf10f4e9d46700003becbf500012d90678000000000043155564534000000000000001d9000155e00e451353c028a0001230020c81e640800053f40000000000000105d0000edf00012ff000024a000000000017f869580000000dc64
  | 52 => 0x76416a02262fc4c114bf955153440002d7032d5d34000092155c27904c6448cf7d66884bc2624e8631ed47901fd0621e7400063000003124f6c605c234000004d18a40006608d0438c8bcd370452728ac78716643a0000182624f1a6d000005b0000000195115626707fb6604ece000000000012e900000000001a223e4c000000175a5d4891300000004f3c20d63c533e483125124bc4a829ec1e8541513a4a148d456c0000098c00069bca7600007722de07ae466027314c968a25450f300008d30f94afe422c0004cac00060300001cb40001fdd1fb3cfc0002dccb824c4d02a65f917e64480006350000153c95f00000000000000676021500002472914f326940000497132758d51b30000000000000032140000d6c0002474ea827740004204000283cb76079029e378858560fc42146359cf00b00db599139a0f496bc0000000213000019ac5fd3ec8a7f66ad08f49506e744550ce00003380410fb94958452097da7a000157400009da0000000000026b00000000001a7b000120200009734d006560000c99000000000016b0258400050913f312fc9d509d8880053c9fe2ab0db82fc025600005ad59dce592bb0000000095d000066c35c14250000ba212c4a3900000000000d200000e420000000321897a0000eff03f89393e9017a573cbdc033904f0c6c0000000c0a00500000000000567c0000bd0733000000002bc7d25410ae950b80001f9cee61ba8000000000038fc000000116b454d4690ed13d8000000008cc00006807c238a538100019b837780000000552353953a152885e143992b65a4000000014809b0fb355480000000f70480104868d918b3f5c9e816d0b8921f46d8007484d000021e0638b25000095e407048241ac0002e5d52d00001990000b6a032800060700001f70fff125c000328c0005dc000000000001cdc6e820a053547740003210acd000000000000000001330334000035e400039000002d44000000144a20a98af3dec8db67d02d9313cc592d698684fa97343d308ce46c45720000a4d49a8000000173d4bd0ccd0000a5a57d8b0460d13d9604175e3d0198d5cf800000016594494644376400000016f5121cf270000000300d43664fc0000d4c000565ca650000000696d6e839100000a3883d00000004d08e8861450ef20c128d41243cb60040001264153169400054481ee22c099100000000000030226910c0000ac700003fe21d56516944bf3000144e00000864d54cb132d84a111991d05b6c540568458435ada4507197c364744723eacee13d98763656837e0fb0af31cbc18618155b8352439a0cb047937b538259fd64c0001701409c00067b01094f48689503000014ed07460608c94410bdf00000001a8d56b0cd995200014c818192381bac0004ed00003a70000667000035800000001
  | 53 => 0x896000007da000144134b883308740002538a711d6187a4af91452ce4d5a00002b963049d00dac5cd000178d0000000000179a66f80e34f8800050c8000000091400012ba359413458e40005188b060000000593c00007c80000000d5d0000c6500000000000b950000000000000000000000ad44285d840002498e022bd41de23715531ab880848a4000000022200000000000000000020900001064910000000000000000000001484699572b03f00000000c5f3ce179267314ee646c000400c832531809562115203fb4db922f400044bc00039751443c802ad2909535000000000000000588000334ce680000ed20001995000000033e800000000003c000004d1c0000000000000115a51f4d2a20808666288000438526528d40004ea1477000179b0000000221041a02f4000078800066796ef00010ae4b200001e0000013c58290000a024a6119e00007de367088207d89a71558baa3b440000000000524400054557993a2c00021844da3da833b37dc08f41e409321b562564f4000000031c0000633218c0003a5800029851684c742a939847d000013a200011ea45d400000004e44df4000000070c0000be3186d45d000096b67295bc23a12331e896ea1ff50eb000021f503c00019f939000018c500009f10000bc2298c5ab0000b26592000036ec00000010ed39042c60bdc0004448000000021963e42bf38b000021552a90c3c000000000056b591100000002aa8a2a00000000000908000027b65800000000000000000000000000000000000000065a833100000000eb10503110033543184800000003bf441c0000f1f57dc00040b4e0163fd7260df5149641172809440000b550a80000e973a24642434c92a214d5f90e48eb32b3856d5b2838e000046a00000003e3c00013e800053ec000271800000000004438c613ed8000000000000000d9000084b000000057b00001794e08479c00000000000514c67000000027ec68c000000004a81c30000b69322145947555be650c00000000000af4dee4f5800040a10340000000008535220b800003745fb1e0ca75000183a21140000000000000158200000000000b3e1e7c0000000401000000028883ee5af84a2000056400000000000e67000098c2df400000958f425218cc0001a41439928400000000000000000000001b00005ca40000000957000161732802d33430a20000000022b57321888000000014d0000d2625b08094e78ef42b10e5c527ce3c00000004b41259000070f477c00000004220000d6e31311a80001a3d18bd5e72028000000063a000000000000003308f08000000000017020ec0e0d00019ed00019070d88c083244cdf3e447530dfcf2c4e5569b1ca942f3fd056369c44b22c501a63e01474169031649d10295f80212096c000000081200000000000000
  | 54 => 0xe397800014a8325335c6f043e16bb000000021d9581658c5bc22740000000acb00000000ea0a11664400057ecff313dc2b700900005efc0914a800c524b00001a019e500011990d5000000000004dacd005dfcf7756ad1362d596e7629d9790001660693cb4c44b03ea2f3999b33f8b6500001695d0c00035481eb248158b4f80b530000000000078120380000000a0700000000475562378c00041f8b460001565155d54e37087971c4cba8500c5250001339000000000008130001789351470100000000000000000007b000000000004a64a38000308d4401f3cf2d1be00004890000024168b1578ee313a52f924e0a433061a262a9400027c0fb0000056b00002af00000004ae0f305a1400000017ce5d3c000000000000011eb03982e46750a5100019390e197b70000000000122c4bcd84b00016d0270400000018f35b8d186527105e4f29a7d1d80827423155b2d994b62d6558a597cd2b072c00000003152680a033ab4c8a5eb8af8000164038184a52ae491901e800057d40003ce467400bc8cc38848bf52409e51db126b572000000000000001287000000000000000000000000000039a977e5a3c0004d0cea92b68f4a1eed0f1000000063596ad00016dd63a0ffe49f42d62c9d0ba6a780a527dc8c05fb8f1053d800042c4802000000000000004eb945100000004a4c0001338000225d5c73a94f5f611ceda057d9e33ee17c7000040b499d8d72d5507b66ec0000000b8b000022d00017f10000000000000000011ec0000e110ff45b32b4000000006c302e557b0a1cdeb00000000000d1448f810116f53e305e18da19b875d42bc00064d06d700000000a0000034a4d500001a4300017cd49d8c1e552824f3c6d4612369782553cf5d01949bd174cea71f301bd0000e4d31204160000b3605d80000001a0b56cc0000001a0e000000067f953400000000c7d03c2ced69900008c5008893d1a219945fbc00060140004ad18b108ac0005bf400000000005e704a402b40003284aa118b400060e00002c4c0000000f5e16610d03390000000084600017c85de8f79012000000015a630b0000000154c15bc0920b68ad80bc16c432fc93b44d442b661c00000000004c449fd4b4c00000002683d59177679c00000002ba632cf5710e80005708f6343094a62e0047300016e600009f313a15d068a111745c5299000000000006040000616137c00000000000000fad000161e3bbc02e0000f0f00019b90a5ca1e12dc0c9188000052cd3a0000020842dcd0b3e154e40000ebd42243b60e58934000000043446305d803721a9463e0fad3b3017909e33e594656109273f0983b5e4508d32540c26191a72162d24b46448d53ce8bb004002b204e800010c17104640ca252fc6a6467d81456d800045e484f4bac0eb39a47794bb123540c4551042
  | 55 => 0x12d15cb03c716c80000000a3a000000012a800000018ab1388e2e09954e219e14b5000000026205f95934e515bfd09428f80003c98245000041700000002a8cbea000160803a4e6b00000000000000421800066b43a3000035100000000000000000057e000042d52b137118558c457c988b09d4000000106522f00005a900002394c6846d8000000000065b800013511e657392a844a0b21270c1db03fd4705a4589a1d408a938d43093c5077c57159e91b79941374d3645a307b100013b001d000000011fc5159a1519f59576560ef02e957882d60ab459c4c811d68f3e00003464c855d922a989952c4efe189469d54c11c754580d1596c00000001f11f8c00025a06ab00000001a40000000072300011266388bb30000d6905dc9a21da08c45d30ea6130000043c92694aa80001c5826a5688e1213144de11c405902210ad40981915ea8a4f44842cc25e11cd64242984e2cf37118890b2e406e54d301173409683459da090000f8c0000b1137910a100013490000e28386cf8e631d27f000151863356df64c40001304b8350701f700004e300009f816dc42f39191302ec560f047cfde1ab00004bc800047fcf9f00000000000000336827250488772e6931c0301a190ee572a1f98e9a5d395640000ee500000004af02fe034d4205c2d2923f2844d1100d403320000000028201a8000458544c01f800010600002094dfa0000188332d66b0000b79280478b06d44f6000045a51699c80ba80002a10fc50000f43570007200009f41cf83de06a44bb2540cb339d9151489c2f8055596204ed8465479353119c9e922ec0351fa00192030054260d93a2ae8b9d47510e952f598a19b40000000dbc000000000009be69549b4654ca2533103c9000017341dc5eb22bc646681c0003f6020f35f88392ba0d3d476000016b800004b940d402c0000a9000005b575c3d9400000017bc000052f3e2836e3c688d1303d02e55049654d41a8e4e7c4a7278d48666b8851000187200000000f30cd5000123d000000000005a0239d17d4290ae6156c97925d816a523c6965acd0f75cfc3296340e1f000000000010e22a9c54e579400029540e200008ac417c0001b40c9e3bb1096223d18a39f400049bc00062b000000000de06a07a8581197257cc8d851f149d558c000000076500011c6315032b639d434049457149900000000652000161323880002fb800000000000000f2532ac99836152da46b11dc349c000000157c68c130600000001ab40004c7cf514b0c7356a0400002a40003c4c00048a039e46680003388917000138413c01374abc1c000016105255222010d8b43a3cc2a695c86909e491629bc72b5180944000008d2a7000007b0ad5304c31425c97081f54cf04fb48b729ad875000037101a0c940634d48282484461b17bb2d0807828ed8a
  | 56 => 0x46092d25e958b800000000a406c4043956f0000000452c000520800000014ea1e3cda1348c73200000005bcc6e32aac0003ae015255841400001289150d5033a409cb5f5c7fe61a980b000197f4e30ea12a8014b0000af100000f54cd93e900000003fe11850ef4f9a0a0cb8800000005b0c0004cb52a532e96b50000864483800043f1777617d50f12303ba020978a000048e00f000000000001f38dd700000000a3c00000018d85e1c136028086c2280f1713309e6622986e0000000394c3490dc048a0001a3b0000000537800015fc0006115363671da1419384dd48fd3fb205927556904981f619743afcb6b583542a38a974250acb3123592c511b0836035175f5c103604dd986d000185b2e912783e94d38000172731680001e542fb5f74f3600003a40000f445d204d94d700005e380006a5cfa6232869c5a1939957a840045f08be67bc0005e78308240c00000016b20284000000197b6a2c731406000063b8cbd11dc00067080000000d816704dfe000075b6398b4f1de91d100010630d5d74700000005c88000000000027d41b30000a5064a80000000c9b0000f9b0001662492093e65b10d600000001db47843be4000000154459cc00000000000000e2700013f40000b38276443800000000000e580000f96544019c34d97112ca8d64000165e5f101d400014d800000000000e6d1e355004ab87c72cd01cd03f42b41b4c000698c00023080a6575d10211d00001a3c000551474100000004f71069369c9c4000192f5a60000349000006c40000000521068889539b0b6e05845f043a04cd2a9092100000003bb4ae40000bd9504000033280005134d730000c22000093700001fd000000000001c20001335520c8422874bfe3239a171dd400000002c80fdc0000000c554ef11d232993960000b57000040c2a240000ce400019cc00000007ad00011bd45b5a6b63e8000475800046040a2000188013980003dd4def000160925898b062147d6307c0000000a000000000000003d0000000515414218b000001b875500012bd0000abe057082b31dd38825ec6f25fed7194f791b50001853426c000000000016c0f2a00000004ffc7931efd69d0000332503957a1cb800068d13444f4060a1edd52c0000fac1c5031a24cc4195d7539b482450931703dc54c809f019cab70000777000114e00000001fe8afc0000000371c0000000b2b00000002eb064a30d85b809a400034fd076621835669f0000372864c62400000000b9c00007c143700000000000210c000000000000008e340f80002e6cd7b2120000101964b00008471c8400034c59550000000000038a0e7193c279c60d000090d6a199fd0fc0a4a60080f41fc81ed61d0000659445e072077f000045d2035854292169c000000026ed637000059a1ee8665000001e000126c00
  | 57 => 0x3058d50000ffa0000000563c000000000029650fd1cd80ab0000fbe00000000000000000041523bc158321c00000000c35abc4200000747000033a0000046000137c00014b91e6c67f3894000000000000013312ee529a4b090380000b2e000014c0955160000078e48a97e16404a88418024649ec0000000d8e000000013106bc28dc3f50e440006614bdb5d947a40000000419887800005c3000052842a800030348891b683525880a8c603d57353e90245c3c0000aa011c1944cf1275979800000e7031c91e47a443e5f240fa36206493be99a7576ca970f2864b0bcc6d1421ca1327885d260c0698000027f19a800000010a522c808508d800000001f9000000051a800000008961d080000000ae00000000525cd7a000135e50c40000910000347c0003fdce6e00013340000c1000000004024c2d149000000017b00000f1259ec000000000000000000b7ce71000078200017e20f9c000000000069342383dc4000626cd4651088401180000447d2ac00018110070eea000081016205140000986468001b0bf400033d185e50f18242f287b831b87f820f143b607407d4d858830000f53000153607311fa1a5470d5f289153f89865086009d286549b2651348306935d07f01df4dd4382460d1ee000000060c400034e80004810a6730c14c905f8000000000056fd12951b059700000000000000000000050592a400000000000000000000000003d71ed568d4b353cb276000004f04320000000000000000004920000000299997504d563b58b14f76495051000040d29cc7c6073c239001d52f15d444624d915b066965816301b646dcdd415b89ed46e83641214acf124454500005ee1dac1ff4c99a031e49377000000000fcdc85be400039bc0001bb98be00019a5500006117850e75e541d20c8c000000124f239877b0000b725cdd25b648800018f4bc112a41c538408595ce0a38619962b000191e1e6405028512550de430a4c1d5b11978abb501d7c55ed151452340002bc198000011ef00011394d9800000012085e4c7c80b780004ea421c3f112a142993c60001a6a00010152ff5a201ec0b433f3c0004b8c000547d63d697842505112f803583db54658764f302eb4ca154d642800059d412000000000e509ba00a900f41a000000007a7000044b0a2400000004072ccc00000010c80000d190cd04c20000e5600000004c206d901287ee26b45c400012ca250da3533a40005e5823e42d4000309c5860000ecd17082a1000000000015ae113ce1c2a157fd000128b376d36568c8ad74ac437b5b5531e44e0259120423a3d40d8a35093e440795b94a8c77d00015cb22d8cac63e04c9339995f5cd902124a40000000495601d2034968242509800057440002b240002cc115828142883d3984400006db4fe4000000000000007023bc40
  | 58 => 0x9660000fd01fa5413289cee257d04d30ba40005b842e8000000041fcb3f00000200000fa35ead7da0000c622e387d349f0000375906e4f9c53600000003a6420b64988c65118d2d5df0d9465c006008180491728e5002605f256943d524b808a32f842c2181678689c87b45284e748b82c126b80d540bcb0722789af5c1516248acf2814a508815ec0003ee8ac0000194939f00000001a4400014c36a44eeb0b10000636cc3411a00004474fcc3e556a850a038466105fc2e8c9fa2bb400013f91ce542400000012151f100000000f235cf02d233940002248000000175400017b10000e8c36742dd590417f2da0000000130c2188b3a0000000000000061fd22d5358512362d8a50efc18759585d72b70d325b8168229e40004ec400042a43f80894000000000000019b369e56e5000000048e56cc00000000d840003b0ce1759c800b0c78cf701d8b5257908de329c0000000000677c0000ebc0000000c050000f746324000000000000011e000018b52a899bc3b542c30bbc00057f905600000003d1540b000000000007e0000194854a000000017405ab80000000672000130d1b991c839c152b5dd4ae25ed85d8074400013d543f000092512e80005bb80003ebc0000000000230424000016901d0161b5850c2b000000000016431d3506d0464a181c28a2420455dd689113e143d45332c17cb5a680003dd974639e1022167900c12219e1198c52e33e0000302506444c94bb276ccb459a4d86382459507cd9d900000000000d68000101a00000004d7da040000cee000000051fcb20505c000000000000014cd00000ea0454000000000000000000000e5f1f640003fa190f60dd3ba36b0057000000031e55540e0d750000000000000000754f3500016c8000129b5998ff00000ff91f7c00011a4000506c0005751226587000057bd8202f5cf0e00012576754000000054d0000ba00000000000000000006770000000224174436d0427215c00009f96676984ac633c8be507602c06598000414c54621d07510000ab0454127a32d469b27fc778000033549140000001a1a00017cc1ae99356a54000355040300006ff5874b1f4f0d4062828d2f65b400014200000000000562540a0f0400005c8c3d425c000176c82400001e700015fd47e4ebc0000daf1e943e93660000368800038900001c9910f428c0003ff40005b8852d0a6d3f661e00000000511000177914543f100009ce5051a935fb00b70000000000000026f000066840004c2cd282f58ba10000f9d000000000013f517785d93b406230c0400000001794b2400000000004c280005e5d2dc3b2055a33456d822442be549590c27f16a30001a8a4b98000000000000000000e9c3193440000542101900010c324a000011e81650000000000000048297c233600000ac08e4016088b5
  | 59 => 0x291c80300010c00000c581c1816c5658e8d3678ee400000003eb800014c4f063528000253400053ac8815ec900614644fd3b700000000dc30001044523055f17e000057e0fe52b782ee1b04b7100000005f440ac00009630000dab2c3c00036a40000000f9800015dc011d6ac359c0004ff40000c4c00008bc6215d8842a0000000111557912b40000000b61000000000000000a9c0122f141975e8d1c200004d800000e422c53f861cc87f000169f1fe444243d80005b78000190c2fa0000000000000000011e3000000038d00002d880001020cf63e3498231199ce116d3561c6c0000000a524730000514872c000000021f91f621940003e08d903f9c0c86a0c0a800000004ef400000000000000aee55d800068185303aa80002c006dd4e38e1e0108bef000060c00015670000000000000000000000001a0000000002cd4e0a1dc517204ccda435446aa59b143931993a55994b9263b18dd5d8d2c616c45d1310863200000004db8000000000000015c64038f2f0000a9b21e465052a075200009520dbc0000000b8744fc000000078669fc0000984e554fe95b20000a1b0000600433139c161c000031114848c41545a5d3106064000458d5774f00000000000040480000ca89991b2c61c45e8f7a4bb4645295096a323c9852f84c19178930f217c0005dd178f000153d14795e003c05b90000f09000000000017a00000add1e20d9a00000000758c7d24d4000044c98b072592e5124341490183627512e167c10075a500002b940000000cc14a30e74000036a1cfc4e14b1d1e813700004ca40001f14000594c00000004a315d069a0000000000000000000000000000000155500000000000000000000000011b4000000029dc0005c1ca293d555d359e8f1d5ee40001a1c377000077055c000000000003f445220000fea000000000000002e440000000000000000042b199a1b7124c31d924a3fa4cf52db01750691a8226cc5163c840cc66213e84bd80003ca4000000000068c40003ae800000000002a60000391c78956740000000dcb00012ce62a57a100004c3000157e1714000000076e000000040c95421c7553f45d0c934d18ab65e405e900017a22ca068e301000000018f007746373edd3200f84004266851c53e085c585511a13cc86b2744ecf0e555e9357cea202e8a4624000002b4cb8d24c018f0198f5c01a59d033cca8701c149a26c0e374874a90511c000000155a3a7c87c2924000251852b6a100000000000678047600002863dacb6d26486e45fd47b20fcd81f6458b983b80c3a66c07ef0001a395660a1234f013204143300000db0631901035659da2d7562331587440001674430449c50780002004974000115f0df005d1f0d5a9223477e25f4000124c6920b517b300001e12d383a22168f414b74d4d00004d54998
  | 60 => 0x925e13e40004efc2bb0001586065430b0000dce160400000011e164800000630000600c8ba20fc00021500004b58e0b5814000206d8c2638d8a35a38e4528c195b4394eab3d4861425b4fbc158107d47c806d185d20620a4e490d719ea27242b646387bd2104c435db82cb4d3d7643724ad141542141bc4b455340b030c08a26264069e0fb40182dc0d7469b107a36c8d57000000000000000001a6235c48855c5c9cf1b598fb546c00038f8000110553700000000d3c71e000000054e00000f44ec6000000000014ec625c0000000f94226d9db000162e114000040d559e2884000042110105440002dd4000000097c365425700016222f980004dd15bb5760000000000000004782c2400000011de4790c7a66a900247886a412807ab0000f8100ecac10000743000164700016d20000da85a100005f5178600019b444708f5663046513fcd0a5c8199258cc3c604a400021b8b2c345cbb51808bbc267cdfb26a400030a4df50a8c69944ac000000170d000162d0000d182d9cb5f261c00001dc00012f48a523d80002f54a311c214d953c40000524bb60001000000024e00011ed46b8dbd2bc83fb63859f2535461a60c962f591573a63f16cf4e1c12403d82ab18e582157b558e4da4e185fd000000000000000000000000000000002a0000015f000068607c064a467a30901fe46a4c800000bd039f88d21d5c0003aed18926d995900000bb318ca58178cb1e046c00069a00005da94a91bbc02700000000b3400000000b40000000000034801ccd37000064f000024d088c00000000005cb40001e2858035889c73ac1a595f04624257181b44c40001c6459b52013c833715fc00008581afd6891c152373694de800000000000000132c0003f751d3000058f000000060cc00020158250001213464879438e0df40395a5f273000000000001278ca80000229356cbb764709b11bdd6ba6674000000027000000004ebc9552e516a562a80000458ede327025318999b21aec1ca56157d2278420111d474e5e9800000000003c0591f31909a450d5a9d69d523230d5a4b0ca121700000001c68a4060a031700000000000000000060f0fbc0003a091cb5940fa80e5d9dd00a43ab000007c000000000017be4240dbf18380000000db100010d400000001da512223c00cf30380000000000000000017d4000000000026398d9000000014b00000000a0600000005e140003cec0002f000000000e7751901af0000fe4000040f2a44cde1e8c000000000000000d7000148b0000730101161900000000000000169898f0ff0112686da080000000000000002e00000000000000000041088f1000047f0000000000067669694884cf40000000000581c71f000000000017dc5f7c74909f1964000000062a00001b1518c0000000140800004c40000001040
  | 61 => 0x51b96f80000c6d00017580000f730000aae21c12621a508ee00000001344000000000000000000000b8c000000042f0000000000020704393144f3c000083a4bb81111eb10f91c54de64f10000354c0004c0d8550000c7f000029f29580000000df144b942c000000014cc62b00000000000000560d10333500000000bb23c1caef000000001ac6cc15e98390000b41000000000004640001323000010300000c14bdc0000340ff555a109c4c5d9050001712158989556e800000000000000aa900008b56a50000148184d0000000618597a670c6845060fa9627d8e4191cb3d577935413ec0001c7171d6011759573400010ed33c333c000000063c000000000003da0000e5720e0000148ca6d610400067c592c2260c00000185c518d17339289844bc076a06958ea62041ac1e81496000022c000192859f044959388fd000038533852fc275d6da277c3804478000320d2815799085502012100000004c6000008fc0006a588b405ec25c498534562c840519649455280a410ee0031114c0000000433683d433079821b173c48f50e0b4412b0eb6132164a37103a63458d4357c176b60ac000000000021581700000b7b000000008a8a9e250835a0000ff600011db5db40f700011690001784000000014740002bac1a10000071000182c0000904117000000005ef000018200000003ba000000009235ebd88d00009bf000000000014785a8185d31340000000000227d0a00dd4de02d6c00065088b91f6c6f300002d838e400065014cf3054dc058f000047cd04a0b3
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xd4150130a90865cd4150130b10855cd4150130d10755cd4150130b80825cd4150130c1475591418c130c4475989418c130b1085505408c130e8262505408c130a60825946050430e115418c6050430c1476551414c030c3076551414c03084c87591530cb20b05831514250720d04541cd4250720b048454c3250720d057454c3250720a52839946050720b11831d54150220c31715c06454d20a0c8454c6250d20c0c7418d5350920a0d8615243cc920c0d861d1530c920d06811d1530c920d05811d1530c920d09801d1530c920c0c74d91530c92084c87591530c920d0474dc5530c920d04741c5530c9208a9841c1610c920d04541cd42d4520b048454c32d4520c15645cc5414520c26755924214520b048454c3214520c25641c94314520c15645cc4214520a25841966290520c46651cd4290520a478654c3290520b048454c3290520c44651cd6250520c60651c16250520b05831514250520c44651cd4250520d04541cd4250520c60659c332505209a1849c33250520a448654c3250520b048454c3250520d057454c3250520a60855046048520b088454c3290120c25741885150120c48651cd4250120a488654c3250120d097454c3250120c30655d05150120d20755094150120e20655094150120b808350941501209308754d4150120a308654d4150120b22859c94150120aa0865c94150120b20855c94150120d20755c94150120b80835c94150120b2285cc94150120f01530c94150120a0c84594324c120c24755914188120c447598d4188120b20855054088120e82635054088120a50835946050420e21541886050420d11735065050020c24765514148020b098414d3048020b418114d3048020c3076551414802090c845d5320ca10a0d84195320c910a50835506050510a60825506050510a628294c6050510cc1735c86050510a52839486050510c31545c261d0c10c31545c261d0810c31545c0614c810e115494d6090410e115454d6090410e21549496090410e21545496090410e41535496090410c31545c06350410c31545c06250410a33805d954cc410c31545c262cc410a31809d9540c410e115494d600c410e115454d600c410e2154949600c410e2154549600c410e4153549600c410a33805d954c8410c31545c263c8410a31809d95408410835875506308410c31545c06308410e115494d6008410e115454d6008410e21549496008410e21545496008410e41535496008410e1154585300c010e4152585300c010e21545852008010e41535852008010a14835d95444010a24825d95444010b11831c15444010b21821c15444010c25549ca6344010c15549ce6244010c32765534044010d21545ca3044010c30765513044010e115418d3044010d11545ce2044010c30765512044010e21541892044010
  | 1 => 0x1c85645c8530c941c85645c8430c941c91645c0430c941a6080594520c941c85645cc520c941a8586d0f420c941c8576d0f420c941c85645cc420c941a858610c420c941c857610c420c941b818010c420c941ca1645c0420c941d80435c0420c941991801d1320c94189487591320c9419a1801d1320c9418a487591320c941946859d1320c941986849d1320c941946851d1320c9419c1801d1320c941b81801d1320c941c85861d1320c941986851d1320c941d06851d1320c941d82801d1320c941985801d1320c941d81801d1320c941981801d1320c941c8474d91320c94198487991320c941a8586991320c9418c487591320c94198487591320c941c8787591320c941a8687591320c941a8487591320c941c8487591320c94188487591320c941c8675591320c941c8475591320c94198687d51320c941c8564dc1320c941a91841c16314141aa1841c16214141c33765915014141d11641cd50141419508798d50141419508758d5014141e116458d5014141d4073dc95014141d43731c95014141d40731c95014141d21641c95014141d42631c95014141d41631c95014141960879895014141d40739895014141960875895014141e21645895014141d40735895014141e41635895014141a31841c56014c21a488254d6010f40a48835496010b4084c87595320cb40d05744c83254740b048254c4350740d05535c84350740b04835484250740d05735484250740b048254c5350740d05535c85350740d11535c05350740b04835485250740d05735485250740d21525c05250740b04854c83250740d05754c83250740a90835806050740aa0825806050740989801d1320ca409a1829c24350540d04531c94350540991839c24250540d047314942505409a1829c26350540b048254c5350540991839c26250540b04835485250540b04854c832505409a3825cf6050540993835cb6050540d81739c86050540d82735c86050540d81735c86050540ca17250660cc540c917350660c8540aa38258d41d0140a938358941d0140a0c845886254c40a0c8458c6354840c0d651d1320c840b04844c8325444084c87591520cb30b05821514350730d04541c94350730b04845483250730d05745483250730a62829946050730b21821d54150230a0d86152428c930899841c1610c930d04541c943d4530b048454832d4530c25645c85414530c16755924314530b04845483214530c25645c84314530c15641cd4214530a15841966390530c46651c94390530c44651c96350530c50651c16350530b05821514350530c44651c94350530d04541c94350530c50659c23250530991849c23250530a5085504604c530c157418c5150130c48651c94350130c30655d05150130d107550d4150130e106550d4150130b808250d4150130b12859c
  | 2 => 0x506250d32a49801506350932a88845c96010c32c49655c043d0832a88845cd6010832a4985d0d6010832a1980191544c832c84645c7424c832a2980191544c832c84645c7434c832a85819d0644c832c45759c4644c832c45755c4644c832c49759c0644c832c49755c0644c832cc2715c0644c832cc1715c0644c832a4980193544c8328c9801da544c832a8980192544c832c84645c6544c832a8980191544c83284e87991544c83284e87191544c832a4980191544c832b0581191544c832b0980191544c832e05644c95114432e41325456014432c85744c86154032c15749cc6154032c15745cc6154032c25749c86154032c25745c86154032e09644c95014032e41325855014032a888250d6010f41a88835096010b41c0d651d1320cb41989801d1320cb4188c87591320cb41ac08250d6010e41ac0835096010a419c1801d1320ca418c487591320ca41c8474591320ca41e116498d5014241e116458d5014241e21649895014241e21645895014241e41635895014241a888250d6010d41a88835096010941989801d1320c94188c87591320c941c0c75591320c941a8682d8e63d5141a8683d8a62d5141a8683d506250d41a4685d0c6250d41c46651c94310d41c85861c94310d41c86651c94310d41d06651c94310d419848750e6210d419848750d6210d41c878750d6210d41a848750d6210d41c848750d6210d41b808250e6010d41e814358a6010d41a848250d6010d41a938650d6010d41b808250d6010d41e81439896010d41e81435896010d41aa08250d6010d41ac08250d6010d41e838250d6010d41a908250d6010d41e808250d6010d41a808250d6010d41a8682d506350941c467518f4250941c91635c04310941c46651cd4210941c85861cd4210941c86651cd4210941d06651cd42109419848798d42109419848758d4210941a868758d4210941a848758d4210941c848758d4210941b808350a6010941e816350a6010941a84835096010941aa3865096010941b80835096010941e82635096010941e81635096010941aa18210d6010941a90835096010941ac0835096010941e83835096010941aa0835096010941e80835096010941a80835096010941a918019143cc941c84641c943cc941c87645cc42cc9419858790c42cc941ca3645c042cc941d82435c042cc941c87645c8438c941c93645c0438c941b818010e428c941aa180191428c941c84641cd428c94198687d0d428c941c85735c8644c941c91735c0644c941ca1725c0644c941a9180192434c941a9180191434c941c84641c9434c941aa180192424c941a868690e424c941c867690e424c941aa180191424c941c84641cd424c941a848650d424c941c847650d424c941aa180193324c941a9180192324c941c84731c9640c941a5080594530c94
  | 3 => 0x4032962000ec8e0000000000000b080000000000003b876061c41b144b61c800216bb9d8522ea968c4c80001f85a421b22a2bad20260e000071ead4ab6d00e2832cc9811a8c3428380053800a93224eb44ca09249154002987c9bc6818266aaa4a0c86702cc79be2117c689fa86b0ecf8560d25019a6a2434c0e8000000a0480ec12fe808002600043a8e160004824819166001b8aa1607b8e400168628cc9e000952e29e916881508d91e3d9764f172658c240a4e643384d1f6ca8543fa801e1ba341845a904a22ce8a86e22b3a000007fa6c2300075a34002d24f8003735ca10820300022050cb26812afa6217000046a9800b18006a18cd40000017ec1b36001de181e0000000010689800149d279294d88008f0e6a78d4002422b1ce660000000000000c4000928000010a6500054800698009d88e000001092a9f21e2a95c0532400228003469784c88b5a002c01c86a440daba2f8bc8742b800d80e000000b2b1a058bac2100c08003e2726dae400000a594200000002e0992c827940a1a3e292ec6ba907989c13a701a1dada1ec5933c3590c000006c16e7e36a0c800600000000008246078c086000af8000023a6d0008c800c2b4a51936000b61ea040000000282001a4a880000210348a0000de001c2001864c2f40027e0bac400224740e87c25249ab800174c31fc00000cb800ab2d4000b200000001dc55ab49012e2d0f267a9ac4b3000132bf2a026806d9a4c00000c985cb58c671a562c354c70b8b9958913169d1ac002bc3d044ac9181f000751380000078a66d62f0b6880d9000000000000045206578045b0f00000000000000009b800cd0000000053122000002f92c988a217848bd9788b8283e9aa008a60000101801008020000500800030000040d0000b0040a00401024000240101401004020280404011048010240100c0900c000080000000000070140200c0a00c0a020080200400c02000050040000000000000001f0040400001000000100107c0f080070140c0100f08401000010200a04c010040101800020050300b0081200803014020300300c02000000680001401018230100b02406000000b4080100a00004008010080000c000000000400034000340301801a60825806054743c15749cc6154243925841c56014943c29745806014943c61715806014943a85819506250c439448750d52944439448750d52544439488750d52940439488750e52540439488750d5254043b408250e5154043b408250d5154043a50835806054742c25749c86154242915841c56014d42c19745806014d42c51715806014d42a858195063508429448754d42944429448754d42544429488754d42940429488794d42540429488754d4254042b408350a5154042b40835095154042a49801506250f32a49801506350a32a49801
  | 4 => 0x8a582517a56992001c0c60007d2920029ca3000cc91200000730ce3602a828ea63862258002181a000003f000c011ca2a140f1ca0203600000000009707080000c5208002de0fab08b34ed58bc84ad0872dc528307a010d7800ab800090
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xc00100300600000009881400600800c008805c8c9053a640295a28e0d2e397a8124c0000000da5000000f560002104000003c0002458a8a80340101f1088b0016013870c160c70b0618100021878602040520640645c6544c832c04b2b003a26419683481901d1644c83290650130a1ac530086a0ca0261439896010d419404c286b12c021a832809858d42980425065013131a84b0084a0ca0261635096010941a40c80c83928799283481901907350a3250690320320e4a1a64a0d20640641cd424c941c40c35003a2641928388186600744c832506903203a6c899064a0c6064087991320c941a034af0eb226419283086989d5644c8325070210eb22c6a80a0a0f00591631c95014141c1043ac8b12a028283c01641cd62540505068812eb1ac4a80a0a0e1021d635895014141a80492a6b80a6a0e81500935497014941d0220930baa6419283a0441261745483250730c0832b0938464a0a619007520943505404c3400ca41286a0a8098604218755cd4150130c803a904b9a82a0261a008598941502304c220930ba2a61928390601619811d1530c920c04c33003a2a619241901816007454c32483040cac24e199282904412617454c3250520c02432e8a9864a0a419007520d4250540483400ca41a84a0a8090608218755c94150120c803a906b9282a02415009754c3250540482c012ca9864a0a8090680216635054088120
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 42
  | 6 => 1947
  | 5 => 11355
  | 4 => 6815
  | 3 => 438
  | 2 => 49
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*5) 5
  | 7 => packedAt gbK7 (i*16) 16
  | 6 => packedAt gbK6 (i*27) 27
  | 5 => packedAt gbK5 (i*38) 38
  | 4 => packedAt gbK4 (i*49) 49
  | 3 => packedAt gbK3 (i*60) 60
  | 2 => packedAt gbK2 (i*71) 71
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (6+((h/1+packedAt gbK8 (5+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (756+((h/14+packedAt gbK7 (672+(h % 14)*6) 6) % 56)*7) 7
  | 6 => packedAt gbK6 (60357+((h/649+packedAt gbK6 (52569+(h % 649)*12) 12) % 2570)*12) 12
  | 5 => packedAt gbK5 (488265+((h/3785+packedAt gbK5 (431490+(h % 3785)*15) 15) % 21942)*15) 15
  | 4 => packedAt gbK4 (365729+((h/2271+packedAt gbK4 (333935+(h % 2271)*14) 14) % 9895)*14) 14
  | 3 => packedAt gbK3 (27740+((h/146+packedAt gbK3 (26280+(h % 146)*10) 10) % 578)*10) 10
  | 2 => packedAt gbK2 (3591+((h/16+packedAt gbK2 (3479+(h % 16)*7) 7) % 77)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3e3c3e3ffc3fffc38e3838e0fff1fffc4271ff
  | 1 => 0xc03fc03e3fc7fffc0fc03f00e1fe3ffd8c4e3f
  | 2 => 0x3fffc03ff83e3ff0003fff01ffc7020f8fcc
  | 3 => 0xffc000003fffc03fffffc00001fff803f00ff0
  | 4 => 0xffffffffc000003ffffffffffe000003fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x444885405808401820888222c5049284210d5
  | 1 => 0xa88924a84a35282c0c45311450a212d18c462a
  | 2 => 0x9512940c9093905690021a4e0534841a068b4c
  | 3 => 0x1803193121221c9b2693800809c92062d00db0
  | 4 => 0x20202000020421204924249090000081296000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfffae888fffae888fffae888fffae888fffae888fffae888fffae888fffae888fffae888fffae888fffae888fffae888fffae888fffae888fffae888fffae888, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12895
namespace PEqualNP.Outside.L_meta_12895
open PEqualNP.Outside.L_meta_12895.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 49 := block_range (n:=49) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 49 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_192 : Interval gbAtlas 3 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_288 : Interval gbAtlas 3 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_384 : Interval gbAtlas 3 384 54 := block_range (n:=54) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 438 := (concat (concat bgb_3_0 bgb_3_96) (concat bgb_3_192 (concat bgb_3_288 bgb_3_384)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_384 : Interval gbAtlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_480 : Interval gbAtlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_576 : Interval gbAtlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_672 : Interval gbAtlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_768 : Interval gbAtlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_864 : Interval gbAtlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_960 : Interval gbAtlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1056 : Interval gbAtlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1152 : Interval gbAtlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1248 : Interval gbAtlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1344 : Interval gbAtlas 4 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1440 : Interval gbAtlas 4 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1536 : Interval gbAtlas 4 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1632 : Interval gbAtlas 4 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1728 : Interval gbAtlas 4 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1824 : Interval gbAtlas 4 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1920 : Interval gbAtlas 4 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2016 : Interval gbAtlas 4 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2112 : Interval gbAtlas 4 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2208 : Interval gbAtlas 4 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2304 : Interval gbAtlas 4 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2400 : Interval gbAtlas 4 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2496 : Interval gbAtlas 4 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2592 : Interval gbAtlas 4 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2688 : Interval gbAtlas 4 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2784 : Interval gbAtlas 4 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2880 : Interval gbAtlas 4 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2976 : Interval gbAtlas 4 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3072 : Interval gbAtlas 4 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3168 : Interval gbAtlas 4 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3264 : Interval gbAtlas 4 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3360 : Interval gbAtlas 4 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3456 : Interval gbAtlas 4 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3552 : Interval gbAtlas 4 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3648 : Interval gbAtlas 4 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3744 : Interval gbAtlas 4 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3840 : Interval gbAtlas 4 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3936 : Interval gbAtlas 4 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4032 : Interval gbAtlas 4 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4128 : Interval gbAtlas 4 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4224 : Interval gbAtlas 4 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4320 : Interval gbAtlas 4 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4416 : Interval gbAtlas 4 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4512 : Interval gbAtlas 4 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4608 : Interval gbAtlas 4 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4704 : Interval gbAtlas 4 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4800 : Interval gbAtlas 4 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4896 : Interval gbAtlas 4 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4992 : Interval gbAtlas 4 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5088 : Interval gbAtlas 4 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5184 : Interval gbAtlas 4 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5280 : Interval gbAtlas 4 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5376 : Interval gbAtlas 4 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5472 : Interval gbAtlas 4 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5568 : Interval gbAtlas 4 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5664 : Interval gbAtlas 4 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5760 : Interval gbAtlas 4 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5856 : Interval gbAtlas 4 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5952 : Interval gbAtlas 4 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6048 : Interval gbAtlas 4 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6144 : Interval gbAtlas 4 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6240 : Interval gbAtlas 4 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6336 : Interval gbAtlas 4 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6432 : Interval gbAtlas 4 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6528 : Interval gbAtlas 4 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6624 : Interval gbAtlas 4 6624 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6720 : Interval gbAtlas 4 6720 95 := block_range (n:=95) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 6815 := (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_96) (concat bgb_4_192 bgb_4_288)) (concat (concat bgb_4_384 bgb_4_480) (concat bgb_4_576 bgb_4_672))) (concat (concat (concat bgb_4_768 bgb_4_864) (concat bgb_4_960 bgb_4_1056)) (concat (concat bgb_4_1152 bgb_4_1248) (concat bgb_4_1344 (concat bgb_4_1440 bgb_4_1536))))) (concat (concat (concat (concat bgb_4_1632 bgb_4_1728) (concat bgb_4_1824 bgb_4_1920)) (concat (concat bgb_4_2016 bgb_4_2112) (concat bgb_4_2208 (concat bgb_4_2304 bgb_4_2400)))) (concat (concat (concat bgb_4_2496 bgb_4_2592) (concat bgb_4_2688 bgb_4_2784)) (concat (concat bgb_4_2880 bgb_4_2976) (concat bgb_4_3072 (concat bgb_4_3168 bgb_4_3264)))))) (concat (concat (concat (concat (concat bgb_4_3360 bgb_4_3456) (concat bgb_4_3552 bgb_4_3648)) (concat (concat bgb_4_3744 bgb_4_3840) (concat bgb_4_3936 (concat bgb_4_4032 bgb_4_4128)))) (concat (concat (concat bgb_4_4224 bgb_4_4320) (concat bgb_4_4416 bgb_4_4512)) (concat (concat bgb_4_4608 bgb_4_4704) (concat bgb_4_4800 (concat bgb_4_4896 bgb_4_4992))))) (concat (concat (concat (concat bgb_4_5088 bgb_4_5184) (concat bgb_4_5280 bgb_4_5376)) (concat (concat bgb_4_5472 bgb_4_5568) (concat bgb_4_5664 (concat bgb_4_5760 bgb_4_5856)))) (concat (concat (concat bgb_4_5952 bgb_4_6048) (concat bgb_4_6144 bgb_4_6240)) (concat (concat bgb_4_6336 bgb_4_6432) (concat bgb_4_6528 (concat bgb_4_6624 bgb_4_6720)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_288 : Interval gbAtlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_384 : Interval gbAtlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_480 : Interval gbAtlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_576 : Interval gbAtlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_672 : Interval gbAtlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_768 : Interval gbAtlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_960 : Interval gbAtlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1440 : Interval gbAtlas 5 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1536 : Interval gbAtlas 5 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2112 : Interval gbAtlas 5 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2208 : Interval gbAtlas 5 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2304 : Interval gbAtlas 5 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2400 : Interval gbAtlas 5 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2496 : Interval gbAtlas 5 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2592 : Interval gbAtlas 5 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2880 : Interval gbAtlas 5 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2976 : Interval gbAtlas 5 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3072 : Interval gbAtlas 5 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3168 : Interval gbAtlas 5 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3264 : Interval gbAtlas 5 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3360 : Interval gbAtlas 5 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3456 : Interval gbAtlas 5 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3552 : Interval gbAtlas 5 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3648 : Interval gbAtlas 5 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3744 : Interval gbAtlas 5 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3840 : Interval gbAtlas 5 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3936 : Interval gbAtlas 5 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4032 : Interval gbAtlas 5 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4128 : Interval gbAtlas 5 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4224 : Interval gbAtlas 5 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4320 : Interval gbAtlas 5 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4416 : Interval gbAtlas 5 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4512 : Interval gbAtlas 5 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4608 : Interval gbAtlas 5 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4704 : Interval gbAtlas 5 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4800 : Interval gbAtlas 5 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4896 : Interval gbAtlas 5 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4992 : Interval gbAtlas 5 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5088 : Interval gbAtlas 5 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5184 : Interval gbAtlas 5 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5280 : Interval gbAtlas 5 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5376 : Interval gbAtlas 5 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5472 : Interval gbAtlas 5 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5568 : Interval gbAtlas 5 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5664 : Interval gbAtlas 5 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5760 : Interval gbAtlas 5 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5856 : Interval gbAtlas 5 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5952 : Interval gbAtlas 5 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6048 : Interval gbAtlas 5 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6144 : Interval gbAtlas 5 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6240 : Interval gbAtlas 5 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6336 : Interval gbAtlas 5 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6432 : Interval gbAtlas 5 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6528 : Interval gbAtlas 5 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6624 : Interval gbAtlas 5 6624 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6720 : Interval gbAtlas 5 6720 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6816 : Interval gbAtlas 5 6816 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6912 : Interval gbAtlas 5 6912 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7008 : Interval gbAtlas 5 7008 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7104 : Interval gbAtlas 5 7104 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7200 : Interval gbAtlas 5 7200 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7296 : Interval gbAtlas 5 7296 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7392 : Interval gbAtlas 5 7392 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7488 : Interval gbAtlas 5 7488 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7584 : Interval gbAtlas 5 7584 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7680 : Interval gbAtlas 5 7680 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7776 : Interval gbAtlas 5 7776 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7872 : Interval gbAtlas 5 7872 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7968 : Interval gbAtlas 5 7968 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8064 : Interval gbAtlas 5 8064 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8160 : Interval gbAtlas 5 8160 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8256 : Interval gbAtlas 5 8256 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8352 : Interval gbAtlas 5 8352 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8448 : Interval gbAtlas 5 8448 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8544 : Interval gbAtlas 5 8544 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8640 : Interval gbAtlas 5 8640 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8736 : Interval gbAtlas 5 8736 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8832 : Interval gbAtlas 5 8832 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8928 : Interval gbAtlas 5 8928 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9024 : Interval gbAtlas 5 9024 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9120 : Interval gbAtlas 5 9120 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9216 : Interval gbAtlas 5 9216 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9312 : Interval gbAtlas 5 9312 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9408 : Interval gbAtlas 5 9408 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9504 : Interval gbAtlas 5 9504 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9600 : Interval gbAtlas 5 9600 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9696 : Interval gbAtlas 5 9696 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9792 : Interval gbAtlas 5 9792 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9888 : Interval gbAtlas 5 9888 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9984 : Interval gbAtlas 5 9984 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10080 : Interval gbAtlas 5 10080 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10176 : Interval gbAtlas 5 10176 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10272 : Interval gbAtlas 5 10272 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10368 : Interval gbAtlas 5 10368 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10464 : Interval gbAtlas 5 10464 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10560 : Interval gbAtlas 5 10560 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10656 : Interval gbAtlas 5 10656 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10752 : Interval gbAtlas 5 10752 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10848 : Interval gbAtlas 5 10848 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10944 : Interval gbAtlas 5 10944 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_11040 : Interval gbAtlas 5 11040 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_11136 : Interval gbAtlas 5 11136 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_11232 : Interval gbAtlas 5 11232 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_11328 : Interval gbAtlas 5 11328 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 11355 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat (concat bgb_5_288 bgb_5_384) (concat bgb_5_480 bgb_5_576))) (concat (concat bgb_5_672 (concat bgb_5_768 bgb_5_864)) (concat (concat bgb_5_960 bgb_5_1056) (concat bgb_5_1152 bgb_5_1248)))) (concat (concat (concat bgb_5_1344 (concat bgb_5_1440 bgb_5_1536)) (concat (concat bgb_5_1632 bgb_5_1728) (concat bgb_5_1824 bgb_5_1920))) (concat (concat (concat bgb_5_2016 bgb_5_2112) (concat bgb_5_2208 bgb_5_2304)) (concat (concat bgb_5_2400 bgb_5_2496) (concat bgb_5_2592 bgb_5_2688))))) (concat (concat (concat (concat bgb_5_2784 (concat bgb_5_2880 bgb_5_2976)) (concat (concat bgb_5_3072 bgb_5_3168) (concat bgb_5_3264 bgb_5_3360))) (concat (concat (concat bgb_5_3456 bgb_5_3552) (concat bgb_5_3648 bgb_5_3744)) (concat (concat bgb_5_3840 bgb_5_3936) (concat bgb_5_4032 bgb_5_4128)))) (concat (concat (concat bgb_5_4224 (concat bgb_5_4320 bgb_5_4416)) (concat (concat bgb_5_4512 bgb_5_4608) (concat bgb_5_4704 bgb_5_4800))) (concat (concat (concat bgb_5_4896 bgb_5_4992) (concat bgb_5_5088 bgb_5_5184)) (concat (concat bgb_5_5280 bgb_5_5376) (concat bgb_5_5472 bgb_5_5568)))))) (concat (concat (concat (concat (concat bgb_5_5664 (concat bgb_5_5760 bgb_5_5856)) (concat (concat bgb_5_5952 bgb_5_6048) (concat bgb_5_6144 bgb_5_6240))) (concat (concat (concat bgb_5_6336 bgb_5_6432) (concat bgb_5_6528 bgb_5_6624)) (concat (concat bgb_5_6720 bgb_5_6816) (concat bgb_5_6912 bgb_5_7008)))) (concat (concat (concat bgb_5_7104 (concat bgb_5_7200 bgb_5_7296)) (concat (concat bgb_5_7392 bgb_5_7488) (concat bgb_5_7584 bgb_5_7680))) (concat (concat (concat bgb_5_7776 bgb_5_7872) (concat bgb_5_7968 bgb_5_8064)) (concat (concat bgb_5_8160 bgb_5_8256) (concat bgb_5_8352 bgb_5_8448))))) (concat (concat (concat (concat bgb_5_8544 (concat bgb_5_8640 bgb_5_8736)) (concat (concat bgb_5_8832 bgb_5_8928) (concat bgb_5_9024 bgb_5_9120))) (concat (concat (concat bgb_5_9216 bgb_5_9312) (concat bgb_5_9408 bgb_5_9504)) (concat (concat bgb_5_9600 bgb_5_9696) (concat bgb_5_9792 bgb_5_9888)))) (concat (concat (concat bgb_5_9984 (concat bgb_5_10080 bgb_5_10176)) (concat (concat bgb_5_10272 bgb_5_10368) (concat bgb_5_10464 bgb_5_10560))) (concat (concat (concat bgb_5_10656 bgb_5_10752) (concat bgb_5_10848 bgb_5_10944)) (concat (concat bgb_5_11040 bgb_5_11136) (concat bgb_5_11232 bgb_5_11328)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_288 : Interval gbAtlas 6 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_384 : Interval gbAtlas 6 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_480 : Interval gbAtlas 6 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_576 : Interval gbAtlas 6 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_672 : Interval gbAtlas 6 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_768 : Interval gbAtlas 6 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_864 : Interval gbAtlas 6 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_960 : Interval gbAtlas 6 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1056 : Interval gbAtlas 6 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1152 : Interval gbAtlas 6 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1440 : Interval gbAtlas 6 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1536 : Interval gbAtlas 6 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1632 : Interval gbAtlas 6 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1824 : Interval gbAtlas 6 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1920 : Interval gbAtlas 6 1920 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1947 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 bgb_6_576) (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)))) (concat (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344))) (concat (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632)) (concat bgb_6_1728 (concat bgb_6_1824 bgb_6_1920)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 42 := block_range (n:=42) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 42 := bgb_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allgb_2 i (by omega) hi
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 5 zero,inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfffae888e888e888fffae888e888e888fffae888e888e888fffae888e888e888fffae888e888e888fffae888e888e888fffae888e888e888fffae888e888e888
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,17,49)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,17,49)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808392 * 2 ^ 32 + 4240490688) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12895.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,5]⟩,⟨.and,[4,6]⟩,⟨.or,[1,7]⟩,⟨.or,[4,6]⟩,⟨.and,[3,9]⟩,⟨.or,[8,10]⟩,⟨.or,[1,6]⟩,⟨.or,[6,10]⟩,⟨.and,[12,13]⟩,⟨.or,[2,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4240490688) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4240490688) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12895

open PEqualNP.Outside.L_meta_12895 in
theorem PEqualNP.Outside.L_meta_12895 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4240490688) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4240490688) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
