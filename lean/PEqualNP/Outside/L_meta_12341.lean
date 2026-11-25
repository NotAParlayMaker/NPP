import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12341.Model
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
  (n*(n+971)) % 2305843009213693951
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


end PEqualNP.Outside.L_meta_12341.Model

namespace PEqualNP.Outside.L_meta_12341
open PEqualNP.Outside.L_meta_12341.Model
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

end PEqualNP.Outside.L_meta_12341

namespace PEqualNP.Outside.L_meta_12341
open PEqualNP.Outside.L_meta_12341.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x7800048000000001c0080000000001d000000044400000098009000040000300000000000320000000000000000d800a00000000000000000000000000000098000000000000000040000000000000000f0000000000000000001c000000001f4200000000002700000000000000000000000000000000000000000000000000000080004400000005000000025000000e0000000000c000009000000000000000000168c00000000000000d000058017000000600000000000004003400000000150000018000000000500000000000000000000000000000000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841f551082eaa2107f14420ffa0841fe41083fa82107f10420ff98841fe31083fa62107f0c420ff90841fe21083fa42107f08420bf28041ff40083fc80107f50020fe20041ff30083fc60107f4c020fe18041ff20083de40107f88020fd10041fd20083da40107e48020f490041ff54c42fea9887f95310bf2a621fd54c42faa9887f15310be2a621ff53c42fea7887f94f10bf29e21fd53c42faa7887f14f10be29e21ff43c43fc87887f50f10fe21e21ff52c42fea5887f94b10bf29621fd52c42faa5887f14b10be29621ff42c43fc85887f50b10fe21621ff32c43fc65887f4cb10fe19621ff41c43fc83887f50710fe20e21ff31c43fc63887f4c710fe18e21ff21c43fc43887d88710fe90e21f521c43f843887fd0310ff20621fd40c43f881887fcc310ff18621fd30c43f861887fc8310ff10621fd20c43f841887fd5210bfaa421fe54842fca9087f55210beaa421fc54842f8a9087fd4e10bfa9c21fe53842fca7087f54e10bea9c21fc53842f8a7087fd0e10ff21c21fd43843f887087fd4a10bfa9421fe52842fca5087f54a10bea9421fc52842f8a5087fd0a10ff21421fd42843f885087fcca10ff19421fd32843f865085f54610ffa0c21fe41843fa83087f10610ff98c21fe31843fa63087f0c610ff90c21fe21843fa43087f08610bf28421ff40843fc81087f50210fe20421ff30843fc61087f4c210fe18421ff20843fc41087e88210fe90421f920843f841087fc4210fb88421fb10843fea8885fd5110ff2a2217e54443faa8885f55110fe2a2217c54443fea6885fd4d10ff29a217e53443faa6885f54d10fe29a217c53443fe86887f90d10fea1a21fc43443fea4885fd4910ff292217e52443faa4885f54910fe292217c52443fe84887f90910fea1221fc42443fe64887f8c910fe99221fc32443fe82887f90510fea0a21fc41443fe62887f8c510fe98a21fc31443fe42887f88510fb10a21fd21443ea42887f08510ffa0221fe40443fa80887f10110ff98221fe30443fa60887f0c110ff90221fe20443f440887f48110fc90221fc20443fe20887ec4110ff08221f610443fea8085fd5010ff2a0217e54043faa8085f55010fe2a0217c54043fea6085fd4c10ff298217e53043faa6085f54c10fe298217c53043fe86087f90c10fea1821fc43043fea4085fd4810ff290217e52043dca4085b94810fea90217d52043daa4085b54810fe290217c52043fe84087f90810fea1021fc42043fe64087f8c810fe99021fc32042fca2087fd0410ff20821fd41043f882087fcc410ff18821fd31043f862087fc8410ff10821fd21043f842085f94010ffa0021fe40043fa80087f10010ff98021fe30043fa60087f0c010ff90021fe20043fa40087f08010ff88021f710043fc20087e84010fe88021f510043f220087c44010
  | 1 => 0xf424c3fc84987f50930fe21261ff324c3fc64987f4c930fe19261ff514c2fea2987f94530fea8a61fc514c2f8a2987fd0530ff20a61fd414c3f882987fcc530ff18a61fd314c3f862987fc8530ff10a61fd214c3f842987fd0130ff20261fd404c3f880987fcc130fd98261fe304c3bc60987fd5030bfaa061fe540c2fca8187f55030beaa061fc540c2f8a8185f94c30ffa1861fe430c3fa86187f10c30ffa9061fe520c2fca4187f54830bea9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830fe99061fc320c3fea2187f94430bf28861fd510c2faa2187f14430ffa0861fe410c3fa82187f10430ff98861fe310c3fa62187f0c430ff90861fe210c3fa42187f08430bf28061ff400c3f680187f90030fea0061fc400c3f080187fcc030ef98061fe300c3f460187f4c030ee98061f9300c3fea9905fd5320ff2a6417e54c83faa9905f55320fe2a6417c54c83fea7905fd4f20ff29e417e53c83faa7905f54f20fe29e417c53c83fe87907f90f20fea1e41fc43c83fe85907f90b20fea1641fc42c83fe65907f8cb20fe99641fc32c83fea3907f94720bf28e41fd51c82faa3907f14720ffa0e41fe41c83fa83907f10720ff98e41fe31c83fa63907f0c720ff90e41ef21c83fc43907f48720f690e41fc21c83fe81907f90320fea0641fc40c83fe61907f8c320fe98641fc30c83fea9105fd5220ff2a4417e54883faa9105f55220fe2a4417c54883fea7105fd4e20ff29c417e53883faa7105f54e20fe29c417c53883fe87107f90e20fea1c41fc43882faa5107fd0a20ff21441fd42883f885107fcca20ff19441fd32883f865107fd4620ff28c417e51883faa3105f54620fe28c41ff41883fc83107f50620fe20c41ff31883fc63107f4c620fe18c41ff21883fc43107f48620fe10c417e50883fe81107f90220fea0441fc40883fe61107f8c220fe98441fc30883fe41107bc8220fd90441ff54482fea8907f95120bf2a241fd54482faa8907f15120be2a241ff53482fea6907f94d20bf29a41fd53482faa6907f14d20be29a41ff43483fc86907f50d20fe21a41ff42483fc84907f50920fe21241ff32483fc64907f4c920fe19241ff51482fea2907f94520fea8a41fc51482f8a2907fd0520ff20a41fd41483f882907fcc520ff18a41fd31483f862907fc8520f790a41fe21483fa42907b48520fe10a41ff40483fc80907f50120fe20241ff30483fc60907f4c120fe18241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041fd54082faa8107f15020be2a041ff53082fea6107f94c20bf29841fd53082faa6107f14c20be29841ff43083fc86107f50c20fe218417e52083fe84107f90820fea1041fc42083fe64107f8c820fe99041fc32083fea2107f94420bf28841f651082eca2107f54420bea8
  | 2 => 0x2faa7a07f14f40ffa1e81fe43d03fa87a07f10f40ffa9681fe52d02fca5a07f54b40bea9681fc52d03fe85a07f90b40fea1681fc42d03fe65a07f8cb40fe99681fc32d03fea3a07f94740bf28e81fd51d02faa3a07f14740ffa0e81fe41d03fa83a07f10740ff98e81fe31d03fa63a07f0c740ff90e81fe21d03fa43a07f08740beaa481ff53903fca7205f94e40fea9c817d53903f8a7207fd0e40ff21c81fd43903f887207fd4a40ff294817e52903faa5205f54a40fe29481ff42903fc85207f50a40fe21481ff32903fc65207f4ca40fe19481ff51903fca3205f94640fea8c817d51903f8a3207fd0640ff20c81fd41903f883207fcc640ff18c81fd31903f863207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681207fd4d40bfa9a81fe53503faa6a07f14d40be29a81ff43503fc86a07f50d40fe21a81ff52502fea4a07f94940fea9281fc52502f8a4a07fd0940ff21281fd42503f884a07fcc940ff19281fd32503f864a07fd4540bfa8a81fe51503faa2a07f14540be28a81ff41503fc82a07f50540fe20a81ff31503fc62a07f4c540fe18a81ff21503fc42a07f48540fe10a81ff40503f680a07f90140df202817e54103fea6207f94c40bf29881fd53102faa6207f14c40ffa1881fe43103fa86207f10c40ffa9081fe52102fca4207f54840bea9081fc52103fe84207f90840fea1081fc42103fe64207f8c840fe99081fc32103fea2207f94440bf28881fd51102faa2207f14440ffa0881fe41103fa82207f10440ff98881fe31103fa62207f0c440ff90881fe21103fa42207f08440bf28081ff401037e80207f90040fd20081fd401037a80207e50040ffaa6617f54cc3fca9985f95330feaa6617d54cc3f8a9985f15330ffa1e61fe43cc3fa87987f10f30ffa9661fe52cc2fca5987f54b30bea9661fc52cc3fe85987f90b30fea1661fc42cc3fe65987f8cb30fe99661fc32cc3fea3987f94730bf28e61fd51cc2faa3987f14730ffa0e61fe41cc3fa83987f10730ff98e61fe31cc3fa63987f0c730ff90e61fe21cc3fa43987f08730ffa0661fb40cc3fc81987f50330fe20661f840cc3fea9185fd5230ff2a4617e548c3faa9185f55230fe2a4617c548c2faa7187fd0e30ff21c61fd438c3f887187fd4a30ff294617e528c3faa5185f54a30fe29461ff428c3fc85187f50a30fe21461ff328c3fc65187f4ca30fe19461ff518c3fca3185f94630fea8c617d518c3f8a3187fd0630ff20c61fd418c3f883187fcc630ff18c61fd318c3f863187fc8630ff10c61fd218c3f843185f94230ffa0461fe408c3fa81187f10230ff98461df308c3f661187fd5130bfaa261fe544c2fca8987f55130beaa261fc544c2f8a8987fd0d30ff21a61fd434c3f886987fd4930bfa9261fe524c3faa4987f14930be29261f
  | 3 => 0x8518ff90a31fea1463fc428c7fe6518ff8ca31fe99463fc328c6fca318ffd0631ff20c63fd418c7f88318ffcc631ef98c63f7318c7fea118ff94231bf28463fd508c6faa118ff14231ffaa2637f544c7fca898df95131feaa2637d544c7f8a898df15131ffa1a63fe434c7fa8698ff10d31ffa92637f524c7fca498ff54931fe292637c524c7fe8498ff90931fea1263fc424c7fe6498ff8c931fe99263fc324c7fe8298ff90531fea0a63fc414c7fe6298fdcc531ff18a63de314c7fea098dfd4131ff28263fd504c7f8a098df14131ffaa0637f540c7fca818df95031feaa0637d540c7f8a818df15031bf29863ff430c7fc8618ff50c31fe21863ff520c7fca418df94831fea90637d520c7f8a418ffd0831ff21063fd420c7f88418ffcc831ff19063fd320c7f86418df94431ffa0863f7410c7fc8218ff50431fe20863f4410c7fe6218f7cc431ff18863f6310c7fa6218f74c431fa98863ff500c7fca018df94031fea80637d500c7f8a018ffd5321bfaa643fe54c86fca990ff55321beaa643fc54c86f8a990ffd4f21bfa9e43fe53c86fca790ff54f21bea9e43fc53c86f8a790ffd0f21ff21e43fd43c87f88790ffd0b21ff21643fd42c87f88590ffccb21ff19643fd32c87f86590ffd0721ff20e43fd41c87f88390ffcc721ff18e43fd31c87f86390ffd4321ff286437e50c87faa190df54321fe28643ff54886fea910ff95221bf2a443fd54886faa910ff15221be2a443ff53886fea710ff94e21bf29c43fd53886faa710ff14e21be29c43ff43887fc8710ff50e21fe21c437d52887fe8510ff90a21fea1443fc42887fe6510ff8ca21fe99443fc32886fca310ffd0621ff20c43fd41887f88310ffcc621ff18c43fd31887f86310ffc8621f790c43f721887fea110ff94221bf28443fd50886faa110ff14221ffaa2437f54487fca890df95121feaa2437d54487f8a890df15121ffa9a437f53487fca690df94d21fea9a437d53487f8a690df14d21ffa1a43fe43487fa8690ff10d21ffa1243fe42487fa8490ff10921ff99243fe32487fa6490ff0c921ffa0a43fe41487fa8290ff10521ff98a43fe31487fa6290ff0c521ff90a43f721487fc4290fb88521ffa82437f50487fca090ff54121fe282437c50487fea810dfd5021ff2a0437e54087faa810df55021fe2a0437c54087fea610dfd4c21ff298437e53087faa610df54c21fe298437c53087fe8610ff90c21fea1843fc43086fca410ffd0821ff21043fd42087f88410ffcc821ff19043fd32087f86410df94421ffa0843fe41087fa8210ff10421ff98843fe31087fa6210ff0c421ff90843ef21087fc4210fd88421fe90843ed21087ea4210f948421ffa8043fe50086fca010fe94021bd28043fd50086faa010fe54021bca8043fc50087fea7a07f94f40bf29e81fd53d
  | 4 => 0x5f94332fea86657d50ccbf8a1997fd5232bfaa465fe548cafca9197f55232beaa465fc548caf8a9195f54e32ffa1c65fe438cbfa87197f10e32bf29465ff428cbfc85197f50a32fe21465ff328cbbe65197bcca32ffa8c65fe518cafca3197f54632bea8c65fc518cbfea1197f94232bf28465fd508cafaa1197f14232ffaa2657f544cbfca8995f95132feaa2657d544cbf8a8995f15132ffa1a65fe434cbfa86997f10d32ffa1265fe424cbfa84997f10932ff99265ef324cbfc6499778c932ffa8a657f514cbfca2997f54532fe28a657c514cbfea0995fd4132ff28265fd504cbf8a0995f14132ffaa0657f540cbfca8195f95032feaa0657d540cbf8a8195f15032bf29865ff430cbfc86197f50c32fe218657e520cbfe84197bd0832ff21065fd420cbf884197b10832ff99065df320cbfc64197b8c832fe99065dd320cbda64197fd4432ff288657e510cbfaa2195f54432fe28865ff500cbfca0195f94032fea80657d500cbf8a0197fd4f41ff29e837e53d07faa7a0df54f41fe29e83ff43d07fc87a0ff50f41fe21e83ff52d07fca5a0df94b41fea96837d52d07f8a5a0ffd0b41ff21683fd42d07f885a0ffccb41ff19683fd32d07f865a0ffd4341ff286837e50d07faa1a0df54341fe286837d54907fea720ff94e41bf29c83fd53906faa720ff14e41ffa1c83fe43907fa8720ff10e41ffa9483fe52906fca520ff54a41bea9483fc52907fe8520ff90a41fea1483fc42907fe6520ff8ca41fe99483fc32906fca320ffd0641dfa0c83f741907fea120ff94241bf28483fd50906faa120ff14241ffa9a837f53507fca6a0ff54d41fe29a837c53507fe86a0ff90d41fea1a83fc43507fea4a0dfd4941ff29283fd52507f8a4a0df14941ffa1283fe42507fa84a0ff10941ff99283fe32507fa64a0ff0c941ffa0a83f741507fc82a0ef90541ffa82837f50507fca0a0ff54141fe282837c50506fca820ffd4c41ff298837e53107faa620df54c41fe29883ff43107fc8620ff50c41fe21883ff52107fca420df94841fea90837d52107f8a420ffd0841ff21083fd42107f88420ffcc841ff19083fd32107f86420df94441ffa0883bf41107fc8220fd90441fea0883bd41107ea8220ffd4041ff280837e50107faa020df54041fe28083ff54cc6fea998ff95331bf2a663fd54cc6faa998ff15331be2a663ff43cc7fc8798ff50f31fe21e63ff52cc7fca598df94b31fea96637d52cc7f8a598ffd0b31ff21663fd42cc7f88598ffccb31ff19663fd32cc7f86598ffd0731fba0e63fe41cc7fa8398ff10731fa20e63ff50cc7fca198df94331fea86637d50cc7f8a198ffd5231bfaa463fe548c6fca918ff55231beaa463fc548c6f8a918df54e31ffa1c63fe438c7fa8718ff10e31ffa9463fe528c6fca518ff54a31bea9463fc528c7fe
  | 5 => 0x800400000200300500900100701500300100302500a00200700900700d00004c03600001a01a00000000200b00100f01300700300300100600100500a03e00000300100000001000001d00500400000000300001d00000200000501600000100d00200c00000600100900001100300300c00500100000400900300a00100901000900104403000300200200e00200002200000700100000702900503e00000000000101c01001100000300800400000100000600000500000300e00101800006b00003300700101900000000000000000001600000200400000000900000600600600100600cffa9687fe52d0efca5a1ff54b43bea9687fc52d0ffea3a1ff94743bf28e87fd51d0efaa3a1ff14743ffa8687fe50d0efca1a1ff54343bea8687fc50d0efaa921df94e43ffa1c87bf4390fbe8721ffd4a43ff294877e5290ffaa521df54a43fe29487ff5190ffca321df94643fea8c877d5190ff8a321ffd4243ff284877e5090ffaa121df54243fe28487ff4350fbe86a1ff90d43df21a87ff5250efea4a1fbd4943b7a9287fe5250ffaa4a1ff14943be29287ec5250ed8a4a1ffd4543bfa8a87f75150eeea2a1ff94543fea8a87fc5150ef8a2a1fd14543ba28a87ff5050efea0a1fed4143bda8287fe5050ffaa0a1ff14143be28287f85050ef0a0a1df95043bf29887ff4310f7e8621ff90c43ef21887fd4310f7a8621f750c43cea1887ff5210ffca421df94843fea90877d5210ff8a421ffd4443ff288877e5110ffaa221df54443fe28887ff5010ffca021df94043fea80877d5010ff8a021ffd4f42ff29e857e53d0bfaa7a15f54f42fe29e85ff43d0bfc87a17f50f42fe21e85ff51d0bfca3a15f94742fea8e857d51d0bf8a3a17fd4342ff286857e50d0bfaa1a15f54342fe286857d5490bfea7217f94e42bf29c85fd5390afaa7217f14e42ffa1c85fe4390bfa87217f10e42bf29485ff4290b7e85217bd0a42ffa8c85fe5190afca3217f54642bea8c85fc5190bfea1217f94242bf28485fd5090afaa1217f14242ffa9a857f5350bfca6a17f54d42fe29a857c5350bfe86a17f90d42fea1a85fc4350bfe84a17bd0942ff21285be4250bfea2a15fd4542ff28a85fd5150bf8a2a15f14542ffa82857f5050bfca0a17f54142fe282857c5050afca8217fd4c42ff298857e5310bfaa6215f54c42fe29885ff4310bfc86217f50c42fe218857e5210bfe84216fd0842ff21085ee4210bfa84216f50842f6a1085ff5110bfca2215f94442fea88857d5110bf8a2217fd4042ff280857e5010bfaa0215f54042fe28085ff54ccafea9997f95332bf2a665fd54ccafaa9997f15332be2a665ff43ccbfc87997f50f32fe21e65ff42ccbde85997f90b32fea1665fc42ccbd885997fd4732ff28e657e51ccbfaa3995f54732fe28e65ff50ccbfca199
  | 6 => 0x480000000000009bab7e8be96ab0e12c3f8000a98abe4d2c8cbca0000e60aac481162e40002fecd226e294c2aa3427c8e691c82e0007d46265aed5c10c93c610000ccc32a22a84226249c3b8d7a7cc39e3dc1e2ad00000fc4c2a364a0d6a000280000aea958000b2c7de000026000214000000d64bf04be48eb7a71c3509da000c3cba29766d648ad20d46856c7a4ee0000003565eeac209a72400078a6148909e20004da000b9c27483c0000000003683440005964567e65548f401e0005deb701d400000000096e00079c7ea11c55e6aa98ecc6000450338baa2ca000000000d441c200013c0da340c384deb9a6064e61d088e3587e040a20e3002ac00024c7280007920000e80000009f81ea2367101ba000000bb2c3e6e08548dc62061c0000b4b3c38e8785e6ad88e20520a800081a57a000d523c6134ae6594c70cf0a5646898ac684365baad673020a8eea685240ba56802c4aa602daa26c424760d500d80385985ecb1e7fec22898a82288690550b38cce8fc7a6d3e49200700000000700f00100103300207500000100300d00000700000900000100100f00200006e00600601600300006a01f02700300000300100500301500000000000b00200000701a00200e00d00b01e00503f00b00000900300d00200c00200000300200a00500400300200a00900c00000100800000500300400300100f00100a00000000d00001700503a00300102400700f00000601100100200200900700500000200800000001000001700200900400600100300701500100300900200100200000b00300100d00b00c00300000000c01000001902700000300800902400000500100c02100900501700100000000000302001600000000000100000300700201200900000100700003a00300400800101000000100700000000000100100900000500000a01200000000400200703900700100d00800900000400800501301200000600001201900000401300f00000300500200700001d00601200903d00a00500200c00000200100000800000203100100900400200101b0f400001200400104902600200b00a00400006800701500700200400a00100001b00000200301b00400600000000d00003c05100000900003900200401602500100400100201000003b00300100000000d00600700200d00100102100000000e00100500300000700800400b00702300403701503c00209d05005403000c00000100200100500400400803700100200200100600200100100600800100100600103b00400009b00100d01901100200900f00300800000500400800000c01400801d01d02601401700400800309d00400700001000200002b00100000a00100100500502d00000201b01900300100802300200000c03900000200e000005000000002000005002032005
  | 7 => 0x445a240816024cb0000930b8458e1f600000009270272c0dcaf075c50a34a9781b4a6e1ce8884266809827e254882840c72e4ec048b08ada81cb5a51ac9a5f019e8a616099c76e2b0b24b3e86e88670ad90da88d479ec046ba7989e47f8734ae4a58a10be03e413a6d2d3abf67a40c8ca8cdc08012e4f0b6c6de5be5a8648cfc58a0b05dab2e30e4a4cfe8fa7621a01849e63d6a8ab9696831c7f0220000000460182000b345c09326da15e53068ac8421609043026a00061841655abb80000005d6d6c1a45668ec5a49640008060d40005d2000000000248ad2d2c03e3e83e23f45c4ce4beac9874ca0e6465b050e20600008a474ae2000ca4562c4c38047a9ae0000000008ccce6000d74866a302a611a22c00028a2ec506000aa83ec38abd0000264a50be68147c60003ce99ed2e7da8e800077ca8c50c6fe0f0a329c8b600f899675a000000d72000154000954d96c6443c3de2ba2ae2da8a20003100000000001aca087aeaae92a366088000000b880006b00008b88d279a0006c4000af20622eaa1c000ab07aa0006327069d4a701fe934a020000007a000082a3d400083e5860000008b0cd8716912d482c6a1e0000000a47700004b4000000000dac8b60000000006ae0005fa23cc00aec73ca240000000000000000000000000000005c86f605034c0003b41281104b2408400198a6448639c19659e000780000522000b2033a00087600070e348c6a1ee060c5a71200000065823438800000063a00071e0003368ca0000009c400000000657e0000001dc7c20002d60000002dc00064e3cc0000003f00000000009fe000d546fc0c23fe4c690890416659a0accd4cd0786008c340009ea27a1aa0000405bc1b649e9265840006dcce899a0be78c45ca3c02e5e003c7ce212ca01060008f0cea1da3e0868d8ca1602ad405088ea6cc1589dc09618a4f6b768641bc800cee242cba2185046f4d70c546a40007ec25e0f4be274618c44a000cc0a2e24e2087ba00093e4f2c740cccb20006ea9d83a60b2000a4c7369bc9d20001567d230233eda0d66a3ac2c4187ca24abaca0615214495a75884c564ac48a0c52aee54e63491e94869c4428aa740c3265a1406a22f2a6c81232290610a00000061682669244880ac1600093a5b663076c6227c09c2412b58000b9800000008e65c188000d34aaa61e75052a1d2186afa00057c00089e0000002e2000a76aa400097ac72d9caf657684ea800a06082000000003527145f2924da45c20005e29520329a87ac000000000528da6858b662849ce33283690e276000c80a9a85a4c4a7c9606120162d4d8ed2a124000accb724fa59c3044c85ce2d8170c1e3ae16a08c16cb3240600021e4ba2c4b4a16e0000000002bea7839883468e000c6e434cbc1f08c45ca7b8c503c00000ec0006c66b20000000001
  | 8 => 0x67c6000005b442ebb468831489200015aa6609ed4e0008d60000002a4b4c85230c3f27080003fc536bb60009e84d07bc8f29a200087e3d842a1182306942ee000d26d56684b360ee69a9be000c10000c82b1a258838a0aa7e6421e03740000000c400000005c0009200000004b0ace000c78000000000570d92000000000000b04a8e8500a6b6201447066ad08d16a0017ea484d64762b64cc2ce7dc0009100000009720008c61fc10e33c0fe5f6802748bee000000ce08c0720aa2328d103be37eb288b40000007383ba662a2a0863aa6b81a20000004b6000000ab80000007b46a8cc2000bc800060c83044e9b41d870052e2e62667e4cda12a3a4000000000bfc482b865ac8a80000007e8d6023ea84000000bb0bf80001f8d1c6c0000d24004bd8000000000030918bc427209836ccc4d4a0b6d7c01c49632e00034621a66c466784b6e7c40000ea40e52c5886748440007ee4f893663c542986c4e0001de084000d1222e23a4466ec2faa1a000000306bbe000c086e297e0002c000a6a071a4e2202d3c6e64ae13ea20094b189ee0ae5022aa27054055c76a6d46bc25abd41467fcb6a46206cb90132c9c296022bec61a03a6d01caaa641e29e37cb5c000a2294cb106241b23ca1e6a9e87a4383b0d0a56e28eba08625fe532bba2a8c4444c8e49924d83fa6a69844ea9c656ab8c5ea02828cb56000a88000a6a1040005920e284a17adae4ce9ec558ab6a3892890ab801d6c02000d30440c0cafe9fad88000ab2bae174ae089c0bcc40000150ac6a26138172b26950a920006cec180ca578848254686aca42cd38822000a5ec90308c7cb0ab8a0125dc65e5b841462e0667b6326a964720c607aa74000af86b61080000007680009700009b82c889a1fa7b2cac7a2bce5b22b29b28f65e8b0c000b9477a0006d8444808c94d0e73e95c9de00069e000b68b5000000000000094a91a00045474ebfa000c66bd200091660a6963a2000000804776cf8ca6bf2226126a9c000000b2243a36a9446ee06400063e74abe48324646c25600002227fa01a10239a45e9000561a6cc82b82f62d207829a92c4783869989a0884c609f43c84900de8bc05a6406be0009aac564a200000000096647c00000021c000000abc7947228e0000000c7647e0000009f62785d4000940000cbe5a0bbccec000360adc0000002a2130000000000a5a8d8b74000a94bdad6e00e7648823300fa81e204000bdc53a8fe6e87a8114ae8054000ca27885723da8da09c1ae3240e4bfe4ca7f4c2e0000581c42603a849a0d68ba0005fc0008de00083a4843c41e8af4d06000d0400000035e000000a727d6c8897c3b62568b200082c000da204a00055654a0000f6772000000000ad4ab42449a4120b54252bd672631aa628701c03b2a4679051cd1a672042082a5201841a38238
  | 9 => 0x4f44d4194432c2453e68c97467eb7c392c3035486095ea42cf2846d860345006c8a0467a396d94420d78168c4a2bc000c58c5c9b690ca54d28b48c148189fc36485cb4646ab421922826f02de4fcaa0ac814253c77819c1c675e896824a189ac94e19a14e650b2ace20f274473a0000000000003c25cc0003724c0d227c8636afc0007d87b0178000b1614ac127741769d64dcd582b40000d062c000d5a9901a837a9b088c000000698000ba804e000638718bc2d9e000268000000000d3293800000096c1f2228914c3a000628000c8e0008d05e46f2a90488c1cc8a00035c4e000077e8749f0a4a320c7e80e60e36e88ab3a0005204acb823d238c4288a4caa2f4bde7545a29569e09f2b4e682bc6072c920a28408ce46e1123ee4a83ea3e680c100d14782394d9ab022c239053898c480b643a0c282d0880cb4d8016400c010362c5ecca7f2604aacbcc20c3d08aeb5e66e3424e4c1a5740465f84041b8668666232246a40546298c6c25c2cc2102a0a8634ea14d9864c94686c1ec0e0a4452606eb30d765145183acb063f679629035a1802e092e00215c3788f8d184584bc6fa670d5e1b087cd0032c676122534902494076a2ccd611e2f0cb882004cb8e334942ade41c48c5906649ca312292544a0c72abc0b1c51270c46cc2617cba449823827ea5cb9e19006a872d1e18e8c251e250c0ea28cfa7d0b78652316a60766a7aa3e000d8a1e4582d8264478e5525d87320ce0000d26f83bc9808acd0cac030a036ba658c7f6d02b44c46cb65109d0b400200740c066085ec86d42654376656410162704c961bec62c9e5f45aa4fe0b807e5c6c209c0cf41cc4e8a122fcd4cc06000a4e9a6580c0ac4206843ec36d68bf437054c04499464a810b52d62caeb001c8be88945a6cf60000002f80004a62247569cc00040286a75214c7be31e6acb142e88c8452abacde7421365161f4d844b86e405e6782866ca6b4000d7e318b92422000b1298829c5d000062a07056c962d3607c922
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xb210427f65884109f596210436e5288410db54a21043765188410be98221042f960884109fd95210436e5248410db549210437651484109fd94210427d6508410db948210436d5208410f948421042fa6008410be580210427e64940109f592500427e63940109f58e500427e62940109f58a500427d61940109f597400436e52d0010db54b400427f65900109f596400433e5490010cf552400436e5290010db54a40042f66190010bd586400427f6550010db949400436d52500109fd94400427e65100109f594400427c6510010cf950400433d5410010db948400436d5210010bd98440042f56110010ee500400427d65cc010db94b300436d52cc0109fd96300427d658c010d794e300435d538c010db94a300436d528c010bd98630042f5618c0109fd95300436e524c010db549300427f650c0109f994300427d650c0109f194300435e530c010d754c300436e520c010db54830042f6610c010bd58430043d9300c0109f597200436e52c8010db54b200427f65880109f596200436e5288010db54a20042f66188010bd586200437a50880109fd95200436e5248010db549200437a50480109fd94200427e65080109f594200427c6508010db948200436d5208010bd98420042f56108010fa480200436e52c4010db54b100437565c4010ddd4b10043e652c4010dd54b10043e552c4010d954b100436e5284010db54a10042f56184010dd94610042f96584010de59610042796584010ded4a10043ea5284010de54a10043e95284010da54a10042f96184010bc586100437a5184010fc946100427f6544010db949100436d5244010bdd95100437765440109dd9510043775244010f994910043755244010f954910043655244010bdd8110043765044010fcd0110043f24044010fc50110043f04044010fccc110043f23044010fc4c110043f03044010fcc8110043f22044010fc48110043f02044010bed95100437b65440109ed95100437b5244010fa94910043795244010fa54910043695244010bed8510043f36144010de94510043f25144010fcd0510043f24144010fc50510043f04144010fccc510043f23144010fc4c510043f03144010fcc8510043f22144010fc48510043f02144010fcd9510042f36544010dcd9510043f36444010fc99110043f16444010fc19110043f35444010fc95110043f15444010fc15110043f36344010fc98d10043f16344010fc18d10043f35344010fc94d10043f15344010fc14d10043f34344010fc90d10043f14344010fc10d10043f36244010fc98910043f16244010fc18910043f35244010dcd4910043f25244010f894910043f15244010dc54910043e15244010d854910043f05244010fcd0910043f24244010fc50910043f04244010fccc910043f23244010fc4c910043f03244010
  | 1 => 0x427c6550c10cf951430433d5450c10d794d430435d5350c10bbd8943042ec6250c10bdd8543042f46150c10bed8143042f86050c109fd94430427e6510c109f594430427c6510c10e750c430427e64d48109f593520427e63d48109f58f520427e61d4810dd987520427e60d4810de983520427d6594810dbd4a520427e64948109f592520427e63948109f58e520426d6594810dbd52520436e5494810db552520436c5494810dbd4e520436e5394810db54e520436c5394810dbd92520436e6494810db592520436c6494810dbd8e520436e6394810db58e520436c6394810dbd0e520436e4394810db50e520436c4394810db986520436c6194810db982520436c60948109fd91520427c64548109fd8d520427c6354810dbd89520427f61548109f585520427f60548109f581520436f6554810dbd51520436e5454810db551520436c5454810dbd4d520436e5354810db54d520436c5354810dbd91520436e6454810db591520436c6454810dbd8d520436e6354810db58d520436c6354810dbd0d520436e4354810db50d520436c4354810db985520436c6154810db981520436c6054810db04152042ee6214810db548520427e64148109f590520427e63148109f58c520427e6214810db988520426e62148109f984520437661148109d984520427e6014810de980520427a60148109fd97420427e65d08109f597420427c65d0810db94b420436d52d08109fd96420427e65908109f596420427c6590810db94a420436d52908109fd95420427e65508109f595420427c6550810db949420436d5250810bdd8542042f46150810bed8142042f860508109fd94420427e65108109f594420427c6510810db948420436d52108109fd97320427e65cc8109f597320427c65cc810db94b320436d52cc8109fd96320427e658c8109f596320427c658c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810db949320436d524c810bdd8532042f4614c810bed8132042f8604c8109fd94320427e650c8109f594320427c650c810db948320436d520c8109f992510427d64944109f98e510427d63944109f98a510427d62944109f597410436e52d0410db54b410427f65904109f596410433e5490410cf552410436e5290410db54a41042fa6090410be582410427f6550410db949410436d52504109fd94410427d6510410cf950410433d5410410db948410436d5210410ed50441042fa6010410be580410427d65cc410db94b310436d52cc4109fd96310427d658c410d794e310435d538c410db94a310436d528c410be98231042f9608c4109fd95310436e524c410db549310427f650c4109f594310435e530c410d754c310436e520c410db54831043d5310c410be98031042f9600c4109f597210436e52c8410db54
  | 2 => 0x5248510dd14921443e45248510d914921443f36048510bd18121443f06048510bc181214427e6508510bd98421443e52108510be980214427e65d0110cfd53404433c54d0110bd98740442f561d01109f996404427f65501109f595404427c6550110cfd51404433c5450110bdd8540442f461501109f994404427e65cc110d7d4f304435c53cc110bd98730442f561cc1109f996304427f654c1109f595304427c654c110d7d4d304435c534c110bdd8530442f4614c1109f994304427e65c8110dbd4b204436c52c8110bd98720442f561c8110f9487204427e6588110be996204437a6588110be58a204437a5288110de14a20443f36188110be98620443f06188110fc88620443f121881109fd95204427d65481109f195204436f5248110db14920442f76148110bd18520443e52148110be195204437865481109e19520443eb6248110fad49204437a5248110de14920443e85248110da14920443f36148110be18520443f06148110bc18520443eb2148110fc88520443e92148110fc48520443e121481109f99420442f66108110bd58420442fa6008110fa48020442fb62c4110be58b10443f221c4110fc48710442f76284110bd58a10443f35084110fc88210443f12084110bb98b54042ed62d50109f98f540427d63d50109f98b540436e62d50109b98b540427d62d5010db58b540426d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d6295010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540427f60550109f581540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150109f98c540435e63150109798c540427d6315010d758c540425d63150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109f980540437a6015010bb98b53042ed62d4c109f993530427d64d4c109f98b530436e62d4c109b98b530427d62d4c10db58b530426d62d4c109f987530437661d4c109f983530437a60d4c109f596530435f5394c109f992530427d6494c109f98a530427d6294c109fd91530427c6454c10d7d8d530427f6254c109f189530427f6154c109f585530427f6054c109f58153042be6414c10af590530435d5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f98c530435e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109f980530437a6014c109fd97430427e65d0c109f597430427c65d0c10cf953430433d54d0c109fd96430427e6590c109f596430427c6590c10d794e430435d5390c109fd95430427e6550c109f595430
  | 3 => 0xd109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109f994534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427e6114d109f184534427e6014d109f180534427f65d0d109f997434427d65d0d109f197434435f53d0d10d714f434427f6590d109f996434427d6590d109f196434433f5490d10cf152434427f6550d109f995434427d6550d109f19543442ef6250d10bb18943442f76150d10bd18543442fb6050d10be181434427f6510d109f994434427d6510d109f194434433f5410d10cf150434435f5310d10d714c434439d4310d10bd98443442f56110d10be98043442f96010d109f993524427d64d49109f98f524427d63d4910dbd4a524427e64949109f592524427e63949109f58e524427e62949109f586524437561949109f58252443796094910afd9152442bc6454910b7d8d52442dc63549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910db548524427e64149109f590524427e63149109f58c524436e62149109f984524437561149109f184524427e6014910de580524427c60149109fd97424427e65d09109f597424427c65d0910dbd4b424436c52d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910bd98642442f56190910be98242442f960909109fd95424427e65509109f595424427c65509109fd94424427e65109109f594424427c6510910cfd50424433c5410910dbd48424436c5210910bd98442442f56110910be98042442f960109109fd97324427e65cc9109f597324427c65cc910dbd4b324436c52cc9109fd96324427e658c9109f596324427c658c910d7d4e324435c538c910bd98632442f5618c910be98232442f9608c9109fd95324427e654c9109f595324427c654c9109fd94324427e650c9109f594324427c650c910d7d4c324435c530c910dbd48324436c520c910bd98432442f5610c910be98032442f9600c9109f997414433f54d0510cf15341442fa60d0510be583414427e65905109f195414433f5450510cf15141442fb6050510be181414427e65105109f997314435f53cc510d714f31442fa60cc510be583314427e658c5109f195314435f534c510d714d31442fb604c510be181314427e650c5109f997214436f52c8510db14b21442fa60c8510be583214427e6588510bd99621443766588510bd58a21443765288510dd14a21443f36088510bd98221443f060885109f195214436f5248510db14921442fb6048510be181214437465485109d19521443e76248510f9d492144376
  | 4 => 0xf98e528427d6394a10de982528427f6454a109f191528427f6354a109f18d528436f6254a10db548528427e6414a109f590528427e6314a109f58c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a109fd96428427e6590a109f596428427c6590a10be98242842f96090a109fd95428427e6550a109f595428427c6550a10bdd8542842f46150a109fd94428427e6510a109f594428427c6510a10be98042842f96010a109fd97328427e65cca109f597328427c65cca109fd96328427e658ca109f596328427c658ca10be98232842f9608ca109fd95328427e654ca109f595328427c654ca10bdd8532842f4614ca109fd94328427e650ca109f594328427c650ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610cf951418433d5450610bed8141842f86050610ed504418435e53cc610d754f31842fa60cc610be583318435e534c610d754d31842fb604c610be18131843d5310c610db94b218436d52c8610be98321842f960c8610db949218436d5248610bed8121842f86048610f948421842f96008610cf952408433d5490210bd98640842f56190210cf950408433d5410210bd98440842f56110210d794e308435d538c210bd98630842f5618c210d794c308435d530c210bd98430842f5610c210dbd4b208436c52c8210db94a208436d5288210bd98620842f56188210be59620843796588210de94a20843ea5288210fa54a20843785288210be98620843f26188210fc586208436f5248210db14920842fb6548210ded9520843eb6248210fad49208437a5248210de14920843e85248210da14920842f86148210fac8520843e92148210db948208436d5208210bd98420842f56108210fa48020842f565c4210dd597108437752c4210dd54b10842f965c4210de59710842fb62c4210be58b108427e63d51109f58f544427e62d51109f58b544433f54951109f992544427e63951109f58e544427e62951109f58a544427d6195110dd586544427d6095110de58254442df6355110b718d54442ef6255110bb189544433f64551109fd8d544435f635511097d8d544427c6355110d718d544425c63551109fd89544436f62551109bd89544427c6255110db189544426c62551109fd85544437761551109fd81544437b60551109f994544433d5415110cf990544427e63151109f58c544427e62151109f588544427e61151109f184544427e60151109f180544427e64d4d109f593534427e62d4d109f58b534435f5394d109f992534427d6494d109f98e534427e6294d109f58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af19153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354
  | 5 => 0x52c427c6454b109fd8d52c427c6354b10dbd8952c436d5214b109f99052c427d6414b109f98c52c427d6314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c427f6590b109f99642c427d6590b109f19642c42f66190b10bd58642c427f6550b109f99542c427d6550b109f19542c42fb6050b10be18142c427f6510b109f99442c427d6510b109f19442c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c427f658cb109f99632c427d658cb109f19632c42f6618cb10bd58632c427f654cb109f99532c427d654cb109f19532c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c42f6610cb10bd58432c433e5490710cf55241c42fa6090710be58241c433e5410710cf55041c42fa6010710be58041c435e538c710d754e31c42fa608c710be58231c435e530c710d754c31c42fa600c710be58031c436f52c8710db14b21c436e5288710db54a21c42fa6088710be58221c43756588710dd94a21c43e65288710f954a21c43745288710bd98221c43f26088710fc58221c436f5248710db14921c42f76548710ddd9521c43e76248710f9d4921c43765248710dd14921c43e45248710d914921c42f46048710db94821c436d5208710f948421c42fa6008710be58021c433e54d0310cf55340c42f661d0310bd58740c433e5450310cf55140c42f76150310bd18540c43b94010310d794f30c435d53cc310bd98730c42f561cc310d794d30c435d534c310bdd8530c42f4614c310f64c030c436e52c8310db54b20c42f661c8310bd58720c43e521c8310db94920c436d5248310bdd8520c42f46148310f948520c42f66108310bd58420c43e920083109f98f548427d63d52109f98b548427d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a548433f64552109fd8d548427c63552109fd89548427c6255210cf550548433e64152109f98c548427d63152109f988548427d6215210dd584548437a60152109f993538427d64d4e109f98b538427d62d4e10dd587538437a60d4e10d7d4e538427e6494e109f592538427e6294e109f58a538427f6454e109f191538435f6354e109fd89538427c6254e10d754c538427e6414e109f590538435e6314e109f988538427d6214e10dd584538437a6014e109fd97438427e65d0e109f597438427c65d0e109fd96438427e6590e109f596438427c6590e109fd95438427e6550e109f595438427c6550e10bbd8943842ec6250e10bdd8543842f46150e10bed8143842f86050e109fd94438427e6510e109f594438427c6510e10e750c43842fa6010e10be580438427e64d4a109f593528427e63d4a109f58f528437561d4a10de983528436f5294a109f992528427d6494a109
  | 6 => 0x3b940100209f597300837651cc020dd547300827f658c0209f596300835e538c020d754e30082ee628c020bb58a3008376518c020dd546300827f654c020dd9453008375514c0209fd94300827e650c0209f594300827c650c020d794c300835d530c020bb98830082ed620c020dd9443008375510c020f64c0300837651c8020dd54720083e651c8020db54720083e551c8020d954720082ed6288020db94a20083765188020dd54620082f96288020ba58a200837a5288020fa94a20083f25188020de54620083f15188020dc546200827f6548020dd94520083755148020bbd95200836f65480209bd9520083e65148020db54520083e55148020d954520082ef6048020db94120083eb4048020fa90120083e94048020fa10120083eb3048020fa8c120083e93048020fa0c120082fb6548020ded95200827b6548020bed8920083eb6248020de94920083ea5248020fad0920083ea4248020fa50920083e84248020facc920083ea3248020fa4c920083e83248020fc94520083795148020fc54520083715148020fac8520083ea2148020fa48520083e82148020fad9520082eb6548020dad9520083eb6448020fa99120083e96448020fa19120083eb5448020fa95120083e95448020fa15120083eb6348020fa98d20083e96348020fa18d20083eb5348020fa94d20083e95348020fa14d20083eb4348020fa90d20083e94348020fa10d20083eb6148020fa98520083e96148020fa18520083eb5148020fa94520083e25148020fa54520083695148020f854520083615148020fa14520083eb4148020fa90520083e94148020fa10520083eb3148020fa8c520083e93148020fa0c5200827e63d53109f58f54c427e62d53109f58b54c437661d5310de58354c433f54953109f98e54c427d63953109f98a54c427d6295310cfd9154c427f63553109f18d54c427f62553109f18954c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c427e64d4f109f59353c427e62d4f109f58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f109fd9153c427c6454f10d7d8d53c427f6254f109f18953c435d5314f109f99053c427d6414f10d798c53c427e6214f109f58853c43766114f10de58053c427f65d0f109f99743c427d65d0f109f19743c427f6590f109f99643c427d6590f109f19643c427f6550f109f99543c427d6550f109f19543c42ef6250f10bb18943c42f76150f10bd18543c42fb6050f10be18143c427f6510f109f99443c427d6510f109f19443c439d4310f10bd98443c42f56110f109f99352c427d64d4b109f98f52c427d63d4b10dd98752c437960d4b10dbd4a52c427e6494b109f59252c427e6394b109f58e52c43766194b109fd91
  | 7 => 0x550c20cf951430833d5450c20d794d430835d5350c20bbd8943082ec6250c20bdd8543082f46150c20bed8143082f86050c209fd94430827e6510c209f594430827c6510c20e750c430827e64948209f592520827e63948209f58e520827d65d08209fd96420827d6590820cf952420833d5490820be98242082f960908209fd95420827f65108209f594420833e5410820cf55042083ad4210820be98042082f960108209f597320827f658c8209f596320835e538c820d754e32082fa608c820be582320827f654c8209fd94320827d650c820d794c320835d530c820f34c832082fa600c820be580320837751944209f992510827d64944209f98e510827d6394420ddd5251083765494420dd55251083745494420ddd4e51083765394420dd54e51083745394420ddd9251083766494420dd59251083746494420ddd8e51083766394420dd58e51083746394420ddd0e51083764394420dd50e51083744394420dd18a51083774294420dd90a51083754294420dd10a51083773294420dd8ca51083753294420dd0ca51083766094420dd182510827f64544209f191510827f63544209f18d51083776554420ddd5151083765454420dd55151083745454420ddd4d51083765354420dd54d51083745354420ddd9151083766454420dd59151083746454420ddd8d51083766354420dd58d51083746354420ddd0d51083764354420dd50d51083744354420dd98951083774254420dd90951083754254420dd10951083773254420dd8c951083753254420dd0c951083766054420dd18151083742054420bd984510837551144209fd97410827e65d04209f597410837651d0420dd547410827f65904209f996410827d6590420dd946410837551904209fd95410827d65504209f19541082ef6250420bb18941083765150420dd54541082fb6050420be181410827f65104209f994410827d6510420dd944410837551104209fd97310827e65cc4209f597310837651cc420dd547310827f658c4209f996310827d658c420dd9463108375518c4209fd95310827d654c4209f19531082ef624c420bb1893108376514c420dd54531082fb604c420be181310827f650c4209f994310827d650c420dd9443108375510c420db94b210837651c8420dd54721082fa60c8420be583210827d6588420dd546210827f6548420db94921083765148420dd94421083755108420f948421082fa6008420be580210827e64940209f592500827e63940209f58e500827d65d0020dd947400837551d00209fd96400827d6590020cf952400833d5490020bb98a40082ed6290020dd946400837551900209fd9540083765150020dd545400827f65100209f994400827d65100209f194400833e5410020cf55040082ee6210020bb58840083765110020dd5444008
  | 8 => 0x209f594414827c6510520cfd50414833c5410520bb98841482ed6210520ddd4441483745110520be98041482f960105209f997314827d65cc5209f197314837751cc520dd147314827e658c5209f596314827c658c520d7d4e314835c538c520bb98a31482ed628c520be98231482f9608c5209fd95314827e654c5209f195314827e650c5209f594314827c650c520d7d4c314835c530c520bb98831482ed620c520ddd443148374510c520be98031482f9600c5209f99721482ee65c8520db997214836c51c8520fad8321482ee60c8520fa18321482ed6288520ddd4621483745188520be98221482f96088520ddd4521483745148520bed8121482f86048520f9d8521483e75148520db14521483e45148520d914521483eb6048520bb18121483e86048520ba181214827e6508520bb98821483e52108520be980214827e65d0120cfd53404833c54d0120bb98b40482ed62d01209f996404827f65501209f595404827c6550120cfd51404833c5450120bbd8940482ec62501209f994404827e65cc120d7d4f304835c53cc120bb98b30482ed62cc1209f996304827f654c1209f595304827c654c120d7d4d304835c534c120bbd8930482ec624c1209f99430482f961c8120fac8720483e921c8120bb58620483eb5088120bd98754082f561d50209f98f540827d63d50209f98b540836e62d50209f987540837661d50209d987540827d61d5020dd587540827561d50209f983540837a60d50209f596540833f54950209f98e540827d63950209f986540827d6195020cfd91540827f63550209f18d540827f62550209f589540827f61550209f185540833d5415020b798c54082dd6315020bd98454082f561150209f990540833e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f988540836e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a6015020bd98753082f561d4c209f993530827d64d4c209f98b530836e62d4c209f987530837661d4c209d987530827d61d4c20dd587530827561d4c209f983530837a60d4c209f596530835f5394c209f992530827d6494c209f986530827d6194c209fd91530827c6454c20d7d8d530827f6254c209f589530827f6154c209f18553082be6414c20af590530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209f988530836e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c209fd96430827e6590c209f596430827c6590c20d794e430835d5390c209fd95430827e6550c209f595430827c6
  | 9 => 0x994318827d650c620be98031882f9600c620dd94621883755188620be98221882f96088620dd94521883755148620bed8121882f86048620f948421882f96008620cf952408833d5490220bb98a40882ed6290220cf950408833d5410220bb98840882ed6210220d794e308835d538c220bb98a30882ed628c220d794c308835d530c220bb98830882ed620c220bb597208836d65c8220db54720882f965c8220de59720882f961c82209f98f544827d63d51209f987544827d61d5120cfd52544827e64951209f98e544827d63951209f58a544836d62951209f986544827d61951209f58254483796095120b7d8d54482dc6355120bdd8554482f46155120cfd91544827f6355120d7d8d544825f63551209f18d544835c63551209718d544827f6255120dbd89544827f6155120ddd85544827761551209f185544837461551209d185544827f6055120ded81544827e6515120cf550544833e64151209f98c544827d63151209f988544827c62151209f984544827d61151209f993534827d64d4d209f987534827d61d4d20d7d4e534827e6494d209f592534827e6394d209f58a534836d6294d209f986534827d6194d209f58253483796094d20afd9153482bc6454d20bdd8553482f46154d209fd91534833f6454d208fd91534827c6454d20cf191534823c6454d20d7d8d534827f6254d20dbd89534827f6154d20ddd8553482776154d209f18553483746154d209d185534827f6054d20ded81534827e6514d20d754c534827e6414d209f590534835e6314d209f988534827c6214d209f984534827d6114d209fd97434827e65d0d209f597434827c65d0d20d7d4f434835c53d0d209fd96434827e6590d209f596434827c6590d20cfd52434833c5490d209fd95434827e6550d209f595434827c6550d20bbd8943482ec6250d20bdd8543482f46150d20bed8143482f86050d209fd94434827e6510d209f594434827c6510d20cfd50434833c5410d20d7d4c434835c5310d20e750c43482ee6210d20bb58843482fa6010d20be580434827e65d0920cfd53424833c54d0920be98342482f960d09209f996424827c6550920cfd51424833c5450920bed8142482f860509209f994424827e65cc920d7d4f324835c53cc920be98332482f960cc9209f996324827c654c920d7d4d324835c534c920bed8132482f8604c9209f994324827e64d45209f593514827e63d45209f58f51483775194520afd9151482bc6454520b7d8d51482dc6354520dd544514827e64145209f590514827e63145209f58c514837960145209f997414827d65d05209f197414837751d0520dd147414827e65905209f596414827c6590520cfd52414833c5490520bb98a41482ed6290520be98241482f960905209fd95414827e65505209f195414827e65105
  | 10 => 0x1c827f64547209f19151c827f63547209f18d51c837551147209fd9741c827e65d07209f59741c827f65907209f99641c827d6590720bb98a41c82ed62907209fd9541c827d65507209f19541c82fb6050720be18141c827f65107209f99441c827d6510720bb98841c82ed62107209fd9731c827e65cc7209f59731c827f658c7209f99631c827d658c720bb98a31c82ed628c7209fd9531c827d654c7209f19531c82fb604c720be18131c827f650c7209f99431c827d650c720bb98831c82ed620c720dd94721c837551c8720be98321c82f960c8720db94721c83e651c8720f954721c82ee60c8720fa98321c83e960c8720bbd9521c836f6548720f9d8521c83e75148720db94521c83e45148720bb18121c83765108720dd54421c83e52108720be98021c82f96008720cf95340c833d54d0320bb98b40c82ed62d0320cf95140c833d5450320bbd8940c82ec6250320ee50040c835e53cc320d754f30c82ee62cc320bb58b30c835e534c320d754d30c82ef624c320bb18930c83d9300c3209f98f548827d63d5220db58b548827e61d52209f587548837a60d5220cfd52548827e63952209f58e548827e61952209f586548833f64552209fd8d548827c63552209fd85548827c6155220cf550548833e64152209f98c548827d6315220db588548827e61152209f584548837a60152209f993538827d64d4e20db58b538827e61d4e209f587538837a60d4e20d7d4e538827e6494e209f592538827e6194e209f586538827f6454e209f191538835f6354e209fd85538827c6154e20d754c538827e6414e209f590538835e6314e20db588538827e6114e209f584538837a6014e209fd97438827e65d0e209f597438827c65d0e209fd96438827e6590e209f596438827c6590e209fd95438827e6550e209f595438827c6550e20bbd8943882ec6250e20bdd8543882f46150e20bed8143882f86050e209fd94438827e6510e209f594438827c6510e20e750c43882fa6010e20be580438833e54d0a20cf55342882fa60d0a20be583428833e5450a20cf55142882fb6050a20be18142883ad4210a20d794f328835d53cca20be98332882f960cca20d794d328835d534ca20bed8132882f8604ca20f34c8328837751946209f992518827d64946209f98e518827d6394620de982518827f64546209f191518827f63546209f18d518837551146209fd97418827e65d06209f597418827f65906209f996418827d6590620be98241882f960906209fd95418827d65506209f19541882ef6250620bb189418827f65106209f994418827d6510620be98041882f960106209fd97318827e65cc6209f597318827f658c6209f996318827d658c620be98231882f9608c6209fd95318827d654c6209f19531882ef624c620bb189318827f650c6209f
  | 11 => 0x7c6550430cf951410c33d5450430b7d8d410c2dc6350430dd945410c3755150430bed81410c2f860504309fd94410c27e65104309f594410c37651cc430dd547310c2fa60cc430be583310c27d658c4309fd95310c376510c430dd544310c3d5310c430be980310c2f9600c4309fd97210c27e65c84309f597210c36e52c8430db54b210c27f65884309f996210c27d6588430dd946210c37551884309fd95210c27d65484309f195210c2df6348430b718d210c36e5248430db549210c3765148430dd545210c2fb6048430be181210c27f65084309f994210c27d6508430f9484210c2fa6008430be580210c27e64940309f592500c27d65d0030be597400c37965d0030ded53400c37954d0030be58f400c37a53d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd6390030be982400c27f65500309fd94400c27e65100309f594400c27c6510030cf950400c33d5410030b798c400c2dd6310030be594400c37965100309e594400c2fa6410030ee990400c37b5410030ee950400c3795410030ee550400c3395410030f698c400c2f96310030f658c400c2d96310030de94c400c3db40cc030f6103300c2dd638c030d794e300c2fa648c030be192300c2f9638c030de94e300c3da538c0309fd95300c2df654c030d7d95300c25f654c030b7d81300c35e504c030f6901300c3d9404c030bed95300c37b654c0309ed95300c2fa644c030be191300c2fb634c030f6d8d300c37a534c030f694d300c3da434c030f650d300c3da324c030f60c9300c3da314c030f60c5300c27e63d53209f58f54c836e62d53209f98754c827d61d5320de58354c833f54953209f98e54c827d63953209f98654c827d6195320cfd9154c827f63553209f18d54c827f61553209f18554c833d5415320cf99054c827e63153209f58c54c836e62153209f98454c827d6115320de58054c827e64d4f209f59353c836e62d4f209f98753c827d61d4f20de58353c835f5394f209f99253c827d6494f209f98653c827d6194f209fd9153c827c6454f20d7d8d53c827f6154f209f18553c835d5314f209f99053c827d6414f20d798c53c836e6214f209f98453c827d6114f20de58053c827f65d0f209f99743c827d65d0f209f19743c827f6590f209f99643c827d6590f209f19643c827f6550f209f99543c827d6550f209f19543c82ef6250f20bb18943c82f76150f20bd18543c82fb6050f20be18143c827f6510f209f99443c827d6510f209f19443c839d4310f20bb98843c82ed6210f20cf95242c833d5490b20be98242c82f96090b20cf95042c833d5410b20be98042c82f96010b20d794e32c835d538cb20be98232c82f9608cb20d794c32c835d530cb20be98032c82f9600cb20ddd4651c827e64947209f59251c827e63947209f58e5
  | 12 => 0x905309f596414c27c6590530cfd52414c33c54905309fd95414c27e65505309f195414c27e65105309f594414c27c6510530cfd50414c33c5410530b798c414c2dd6310530ddd44414c3745110530be980414c2f960105309f997314c377518c530dd146314c2fa608c530be582314c377514c530dd145314c2fb604c530be181314c27e650c5309f997214c27d65c85309f197214c37751c8530dd147214c27e65885309f596214c27c6588530dbd4a214c36c52885309fd95214c27e65485309f195214c27e65085309f594214c27c6508530dbd48214c36c5208530ddd44214c3745108530f9484214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d01309f996404c27f65501309f595404c27c6550130cfd51404c33c5450130b7d8d404c2dc63501309f994404c3b94010130de953304c37854cc130f6d42304c27e63d5030d798f540c27e62d50309f58b540c27e61d50309f587540c27e60d5030de983540c27d6595030cfd52540c27e62950309f58a540c27e61950309f586540c33f64550309fd8d540c27d63550309fd89540c27c62550309fd85540c27c6155030de181540c33d5415030bb988540c2ed6215030bd984540c2f561150309f990540c33e64150309f98c540c35e63150309f988540c36e62150309b988540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a60150309f992530c27d6494c309f597430c27f6590c309f596430c33e5490c30cf552430c2fa6090c30be582430c27f6550c30bbd89430c2ec6250c30bdd85430c2f46150c30bed81430c27f6510c309f594430c33e5410c30cf550430c39d4310c30be980430c2f96010c30dbd4a520c27e64948309f592520c27e61948309f586520c27f64548309f191520c27f61548309f185520c2be6414830af590520c36d5214830bd984520c2f561148309fd97420c27e65d08309f597420c33e54d0830cf553420c27f65908309f996420c27d6590830db94a420c36d5290830be982420c2f960908309fd95420c27d65508309f195420c33e5450830cf551420c2df6350830b718d420c36e5250830db549420c2fb6050830be181420c27f65108309f994420c27d6510830db94b320c36d52cc830be983320c2f960cc8309f596320c27f654c830db948320c36d520c830f34c8320c2fa600c830be580320c37751944309f992510c27d64944309f98a510c27d62944309fd91510c27c64544309fd89510c27c6254430af990510c2bd6414430bb988510c2ed6214430dd544510c27f65d04309f997410c27d65d0430cf953410c33d54d04309fd96410c27e65904309f596410c3765190430dd546410c2fa6090430be582410c27f65504309f595410c2
  | 13 => 0xdb949328c36d524ca30bed81328c2f8604ca30f34c8328c37751946309f992518c27d64946309f98a518c27d62946309fd91518c27c64546309fd89518c27c6254630bb988518c2ed6214630dd544518c27f65d06309f997418c27d65d0630dd947418c37551d06309fd96418c27e65906309f596418c27f65506309f595418c27c6550630b7d8d418c2dc63506309fd94418c27e65106309f594418c3765110630dd544418c2fa6010630be580418c376518c630dd546318c2fa608c630be582318c376514c630dd545318c2fb604c630be181318c3d5310c6309fd97218c27e65c86309f597218c36e52c8630db54b218c27f65886309f996218c27d6588630dd946218c37551886309fd95218c27d65486309f195218c2df6348630b718d218c36e5248630db549218c3765148630dd545218c27f65086309f994218c27d6508630f9484218c2fa6008630be580218c33e5490230cf552408c2de6390230b758e408c33e5410230cf550408c2de6310230b758c408c3b94010230b7597308c35d65cc230be597308c37965cc230de953308c37854cc2309f98b544c27d62d51309f987544c27d61d5130cfd52544c27e64951309f58e544c35d63951309f98a544c27d62951309f986544c27d61951309f582544c3796095130bbd89544c2ec6255130bdd85544c2f46155130cfd91544c27f6355130d7d8d544c27f6255130dbd89544c26f62551309f189544c36c62551309b189544c27f6155130ddd85544c27761551309f185544c37461551309d185544c27f6055130ded81544c27b60551309f994544c33d5415130cf990544c27e63151309f18c544c27e62151309f588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d309f996434c27c6550d30cfd51434c33c5450d30bbd89434c2ec6250d30bdd85434c2f46150d30bed81434c2f86050d309f994434c39d4310d309f993524c27d64d49309f987524c27d61d4930dbd4a524c2bf6454930af191524c2f76154930bd185524c36d52149309f990524c27d64149309f984524c27d61149309f997424c27d65d09309f197424c36f52d0930db14b424c27e65909309f596424c27c6590930cfd52424c33c54909309fd95424c27e65509309f195424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930dbd48424c36c5210930be980424c2f960109309f997324c36f528c930db14a324c2fa608c930be582324c36f524c930db149324c2fb604c930be181324c27e650c9309f993514c27d64d45309f98b514c27d62d4530ddd46514c2bf6454530af191514c2ef6254530bb189514c37551145309f990514c27d64145309f988514c27d62145309f997414c27d65d05309f197414c37751d0530dd147414c27e65
  | 14 => 0x8854cc27d62153309f98454cc27d6115330de58054cc33e5490f30cf55243cc2fa6090f30be58243cc2ef6250f30bb18943cc2f76150f30bd18543cc2f86050f30cf95043cc33d5410f30e750c43cc2fa6010f30be58043cc36f5294b309f99252cc27d6494b309f98652cc27d6194b309fd9152cc27c6454b309fd8552cc27c6154b30db54852cc27f65d0b309f99742cc27d65d0b309fd9642cc27e6590b309f59642cc2fa6090b30be58242cc27f6550b309f59542cc27c6550b30bed8142cc2f86050b309fd9442cc27e6510b309f59442cc2de6310b30b758c42cc36e52ccb30db54b32cc2fa60ccb30be58332cc36e520cb30db54832cc2fa600cb30be58032cc37751947309f99251cc27d64947309f98a51cc27d62947309fd9151cc27c64547309fd8951cc27c6254730dd54451cc27f65d07309f99741cc27d65d07309fd9641cc27e65907309f59641cc2fa6090730be58241cc27f65507309f59541cc27c6550730bed8141cc2f860507309fd9441cc27e65107309f59441cc2de6310730b758c41cc37651cc730dd54731cc2fa60cc730be58331cc376510c730dd54431cc2fa600c730be58031cc27f65c87309f99721cc27d65c87309fd9621cc27e65887309f59621cc27f65487309f59521cc27c6548730bed8121cc2f860487309fd9421cc27e65087309f59421cc3e52108730be98021cc2f96008730cf95340cc33d54d0330b798f40cc2dd63d0330be59740cc37965d0330ded5340cc3ba54d0330de55340cc3b954d0330f698f40cc2f963d0330f658f40cc33e5450330cf55140cc2df6350330b718d40cc2f96510330de59440cc3ba6410330ded5040cc3795410330be58c40cc2ee62d5230bb58b548c2f661d5230bd587548c35d63d52309f98b548c36e62d52309b98b548c27d62d5230db58b548c26d62d52309f987548c37661d52309d987548c27d61d5230dd587548c27561d5230de983548c33f54952309f98a548c27d62952309f986548c27d6195230cfd91548c27f62552309f189548c27f61552309f185548c33d5415230cf990548c35d63152309f988548c27d62152309f984548c27d6115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c33e5450e30cf551438c2ef6250e30bb189438c2f76150e30bd185438c2fb6050e30be181438c39d4310e30dbd4a528c27e6494a309f592528c27e6194a309f586528c27f6454a309f191528c27f6154a309f185528c36d5214a30bd984528c2f56114a309fd97428c27e65d0a309f597428c36e52d0a30db54b428c27f6590a309f996428c27d6590a309fd95428c27d6550a309f195428c2df6350a30b718d428c27f6510a309f994428c27d6510a30db948428c36d5210a30be980428c2f96010a30db94a328c36d528ca30be982328c2f9608ca3
  | 15 => 0x5036f5208540db14821503775108540dd14421503e52108540be98021502f96008540de14f40503bb5090140d7d4e531027e6294c409f58a531027e6194c409f586531027f6254c409f189531027f6154c409f18553103786054c40d754c53102ee6214c40bb58853102f66114c40bd584531035e53d0c40d754f43102fa60d0c40be583431027d6590c409fd9543102ef6250c40bb18943102f76150c40bd18543102fb6050c40d794c431035d5310c40e750c43102fa6010c40be580431036f52948409f98e521027d63948409f986521027d61948409fd8d521027c63548409fd85521027c6154840b798c52102dd6314840db54852102f66114840bd584521036e52d0840db54b42102fa60d0840be583421027d65908409fd95421036e5210840db54842103ad4210840be98042102f960108409fd97321027e65cc8409f597321035e53cc840d754f321027f658c8409f996321027d658c840db94a321036d528c840be98232102f9608c8409fd95321027d654c8409f19532102bf644c840af191321035e534c840d754d321036e524c840db54932102fb604c840be181321027f650c8409f994321027d650c840ddd46511027e63944409f58e511027e62944409f58a511027f63544409f18d511027f62544409f18951102de6314440b758c51102ee6214440bb58851103755114440dd947411037551d0440be98341102f960d04409f596411027f6550440dd94441103755110440ed50441102fa6010440be580411027f65cc4409f997311027d65cc440d794f311035d53cc4409fd96311027e658c4409f5963110376518c440dd54631102fa608c440be582311027f654c4409f595311027c654c440afd9131102bc644c440d794d311035d534c440dd9453110375514c440bed8131102f8604c4409fd94311027e650c4409f594311027f65c84409f997211027d65c8440db94b211036d52c84409fd96211027e65884409f59621103765188440dd546211027f65484409f595211027c6548440afd9121102bc6448440db949211036d5248440dd94521103755148440bed8121102f860484409fd94211027e65084409f59421103e52108440be98021102f96008440af592401033e5490040be592401037a5490040ee95240102fa63900409fd9540102bf6550040cfd95401023f6550040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140102f86350040eed0d40103b94350040ee90940103b84250040ee90540103b84150040d798f54cc27e62d53309f58b54cc27e61d53309f58754cc37960d5330cfd5254cc27e62953309f58a54cc27e61953309f58654cc33f64553309fd8954cc27c62553309fd8554cc27c6155330ded8154cc33d5415330cf99054cc35e63153309f9
  | 16 => 0xe520ca40db54832902fa600ca40be580329037751946409f98e519027d63946409f98a519027d62946409fd8d519027c63546409fd89519027c6254640bb98851902ed6214640dd54451903765190640dd54641902fa6090640be58241903765150640dd54541902fb6050640be18141903b541106409fd97319027e65cc6409f597319037651cc640dd547319027f658c6409f996319027d658c6409fd95319027d654c6409f19531902bf644c640af191319027f650c6409f994319027d650c640dd9443190375510c640be98031902f9600c6409fd97219027e65c86409f597219036e52c8640db54b219027f65886409f996219027d6588640dd946219037551886409fd95219027d65486409f19521902bf6448640af191219036e5248640db54921903765148640dd545219027f65086409f994219027d6508640f948421902fa6008640be58021902bd65d0240cf59740902f965d0240de597409037a53d02409f98b535027d62d4d409f987535027d61d4d40d7d4e53502ef6254d40bb18953502f76154d40bd185535035d5314d409f988535027d6214d409f984535027d6114d409f997435035f5390d40d714e43502fa6090d40be582435035f5350d40d714d43502ef6250d40bb18943502f76150d40bd18543502fb6050d40be181435027e6510d40e750c435027e63d49409f58f525027e61d49409f587525036f5294940b7d8d52502dc6354940bdd8552502f46154940db548525027e63149409f58c525027e61149409f584525027e65d0940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bed8142502f860509409f994425027e65cc9409f597325027c65cc940dbd4b325036c52cc9409f996325027d658c9409f196325035f538c940d714e325027f654c9409f995325027c654c9409f994325027d650c9409f19432502be640c940af590325035f530c940d714c325036f520c940db14832502fa600c940be580325027e63d45409f58f515027e62d45409f58b51503775194540b7d8d51502dc6354540bbd8951502ec6254540dd544515027e63145409f58c515027e62145409f588515027e65d0540ddd4641503745190540be98241502f96090540ddd4541503745150540bed8141502f860505409f994415027e65cc5409f597315027c65cc540ddd47315037451cc5409f996315027d658c5409f196315035f538c540d714e315027f654c5409f995315027c654c5409f994315027d650c5409f19431502be640c540af590315035f530c540d714c3150377510c540dd14431502fa600c540be580315027e65c85409f597215027c65c8540ddd47215037451c85409f996215027d65885409f196215036f5288540db14a215027f65485409f995215027c65485409f994215027d65085409f19421
  | 17 => 0x4021de98d50087796354021de18d500877b4354021de90d50087794354021de10d500877a6254021ded09500877a4254021de50950087784254021decc9500877a3254021de4c950087783254021de985500877b4154021de90550087794154021de105500877b3154021de8c550087793154021de0c5500877b2154021dac85500877a2154021dc88550087792154021da48550087712154021d848550087782154021f948450086fa6014021de540500875f5394f409f98a53d027d6294f409f98653d027d6194f409fd8953d027c6254f409fd8553d027c6154f40ded8153d035d5314f40d794f43d035d53d0f40be98343d02f960d0f40bbd8943d02ec6250f40bdd8543d02f46150f40be18143d035e5310f40d754c43d039d4310f40be98043d02f96010f40dbd4a52d027e6394b409f58e52d027e6194b409f58652d027f6354b409f18d52d027f6154b409f18552d036d5214b40db94b42d036d52d0b40be98342d02f960d0b40db94842d036d5210b40be98042d02f96010b409fd9732d027e65ccb409f59732d027f658cb409f99632d027d658cb40be98232d02f9608cb409fd9532d027d654cb409f19532d02fb604cb40be18132d027f650cb409f99432d027d650cb40af99032d02bd640cb40ddd4651d027e63947409f58e51d027e62947409f58a51d027f63547409f18d51d027f62547409f18951d03755114740dd94741d037551d0740be98341d02f960d0740dd94441d03755110740be98041d02f960107409fd9731d027e65cc7409f59731d027f658c7409f99631d027d658c740be98231d02f9608c7409fd9531d027d654c7409f19531d02fb604c740be18131d027f650c7409f99431d027d650c740af99031d02bd640c7409fd9721d027e65c87409f59721d027f65887409f99621d027d65887409fd9521d027d65487409f19521d02fb6048740be18121d027f65087409f99421d027d6508740f948421d02fa6008740be58021d02ee62d4e40bb58b53902f661d4e40bd587539035f5394e409f98a539027d6294e409f986539027d6194e409fd89539027c6254e409fd85539027c6154e40d754c539035e5390e40d754e43902fa6090e40be582439035e5350e40d754d43902ef6250e40bb18943902f76150e40bd18543902fb6050e40be181439039d4310e40dbd4a529027e6394a409f58e529027e6194a409f586529027f6354a409f18d529027f6154a409f185529036d5214a40bd98452902f56114a40db94a429036d5290a40be98242902f96090a40db949429036d5250a40bed8142902f86050a40eb508429027f65cca409f997329027d65cca40db94b329036d52cca409fd96329027e658ca409f596329027f654ca409f595329027c654ca40afd9132902bc644ca409fd94329027e650ca409f594329036
  | 18 => 0x9f992520867d64948219f98e520867d63948219f597420867f65908219f596420873e5490821cf55242086f66190821bd586420867f65508219fd94420867d6510821cf950420873d5410821eb50842086f66110821bd584420867d65cc8219fd96320867d658c821d794e320875d538c821bd98632086f5618c8219fd95320867f650c8219f594320875e530c821d754c32087cd320c821bd98432086f5610c8219f992510867d64944219f98e510867d63944219f597410867f65904219f596410873e5490421cf55241086ee6290421bb58a410867f65504219fd94410867e65104219f594410867c6510421cf950410873d5410421bb98841086ed6210421ed504410867d65cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c4219fd95310867f650c4219f994310867d650c4219f194310875e530c421d754c31086ee620c421bb58831087d5310c421bb58a210876e5288421bd58a21086e56288421dd94a21087e652884219fd9521086ef6548421dbd95210866f6548421bbd85210876e5148421f9d0521087e64148421f950521087e44148421f9cc521087e63148421f94c521087e43148421bdd95210877765484219dd9521086f76248421f9d8921087765248421f994921087e74248421f990921087e54248421f910921087e73248421f98c921087e53248421f90c921087e76548421b9d9521087676548421f9d9121087e66448421f959121087e46448421f9d5121087e65448421f955121087e45448421f9d8d21087e66348421f958d21087e46348421f9d4d21087e65348421f954d21087e45348421f9d0d21087e64348421f950d21087e44348421f9d8121087e66048421f958121087e46048421f948750087e52194021ded42500867e64940219f592500867e63940219f58e500877b5494021de95250087795494021de152500877b5394021de94e50087795394021de14e50087eb2194021fc88650087e92194021fc48650087e12194021ded92500877a6494021de59250087786494021ded8e500877a6394021de58e50087786394021ded0e500877a4394021de50e50087784394021de18a500877b4294021de90a50087794294021de10a500877b3294021de8ca50087793294021de0ca50087786194021ded06500877a4194021de50650087784194021decc6500877a3194021de4c650087783194021dec86500877a2194021de48650087e521540219fd91500867c64540219fd8d500867c6354021dbc8550087762154021db48550087752154021d9485500877b6554021ded51500877a5454021de55150087785454021ded4d500877a5354021de54d50087785354021fac8550087f22154021fa48550087f12154021f8485500877b6454021de99150087796454021de191500877b635
  | 19 => 0x543486ef6250d21bb18943486f76150d21bd18543486fb6050d21be181434867f6510d219f994434867d6510d219f194434873f5410d21cf150434875f5310d21d714c434879d4310d21bb98843486ed6210d21bd98443486f56110d219f997424873f54d0921cf15342486f661d0921bd587424867e65909219f195424873f5450921cf15142486f76150921bd185424867e65109219f997324875f53cc921d714f32486f661cc921bd587324867e658c9219f195324875f534c921d714d32486f7614c921bd185324867e650c9219f997414873f54d0521cf15341486ee62d0521bb58b414867e65905219fd95414867d65505219f195414873f5450521cf15141486ef6250521bb189414867e65105219f997314875f53cc521d714f31486ee62cc521bb58b314867e658c5219fd95314867d654c5219f195314875f534c521d714d31486ef624c521bb189314867e650c521bd58321487e75188521bb582214867e64d41219f593504867e63d41219f58f504877b5094121afd9150486bc6454121b7d8d50486dc6354121de540504867e64141219f590504867e63141219f58c50486fa60d5021be583540867e63d50219f58f540867e62d5021db98b540867e61d5021dd987540867e60d5021de983540867a60d50219f583540877960d50219e583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf55054086de6315021b758c54086fa6015021be580540867e6415021cf990540867e6315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e58054086fa60d4c21be583530867e64d4c219f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c21de983530867a60d4c219f583530877960d4c219e583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530867f6454c219f191530875f6354c219fd81530867c6054c21af99053086bd6414c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6314c21d798c530867e6214c21db988530867e6114c21dd984530867e6014c21de980530867a6014c219f58053087796014c219e580530867f65d0c219f997430867d65d0c219f197430873e54d0c21cf553430867f6590c219f996430867d6590c219f196430875e5390c21d754e430867f6550c219f995430867d6550c219f195430873e5450c21cf551430875e5350c21d754d43086ef6250c21bb18943086f76150c21bd18543086fb6050c21be181430867f6510c219f994430867d6510c219f194430879d4310c21
  | 20 => 0x867e63952219f58e548867e60952219f582548873f64552219fd8d548867c63552219fd81548867c6055221cf550548873e64152219f98c548867d6315221db588548877661152219f980548867d60152219f993538867d64d4e21db58b538877661d4e219f983538867d60d4e21d7d4e538867e6494e219f592538867e6094e219f582538867f6454e219f191538875f6354e219fd81538867c6054e21d754c538867e6414e219f590538875e6314e21db58853887766114e219f980538867d6014e219fd97438867e65d0e219f597438867c65d0e219fd96438867e6590e219f596438867c6590e219fd95438867e6550e219f595438867c6550e21bbd8943886ec6250e21bdd8543886f46150e21bed8143886f86050e219fd94438867e6510e219f594438867c6510e21e750c43886f66110e21bd584438873e54d0a21cf55342886f661d0a21bd587428873e5450a21cf55142886f76150a21bd18542887ad4210a21d794f328875d53cca21bd98732886f561cca21d794d328875d534ca21bdd8532886f4614ca21f34c8328873e5490621cf55241886ee6290621bb58a418873e5410621cf55041886ee6210621bb588418875e538c621d754e31886ee628c621bb58a318875e530c621d754c31886ee620c621bb58831886ed65c8621db59721886f565c8621dd59721886f560c8621ded42508867e64942219f592508867e63942219f58e508867f64542219f191508867f63542219f18d508876f2154221de540508867e63d51219f58f544867e60d51219f583544873f54951219f992544867e63951219f58e544867d6295121db58a544867d6195121dd586544867e60951219f58254486df6355121b718d54486fb6055121be181544873f64551219fd8d544875f635512197d8d544867c6355121d718d544865c63551219fd89544876f62551219fd85544877761551219fd81544877b60551219ed81544867c6055121de181544867860551219f994544873d5415121cf990544867e63151219f58c544867e60151219f580544867e64d4d219f593534867e60d4d219f583534875f5394d219f992534867d6494d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d219f58253486bf6454d21af19153486fb6054d21be181534867f6454d21cfd91534863f6454d219f191534873c6454d218f191534875f6354d219fd89534876f6254d219fd8553487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f994534875d5314d219f990534867d6414d21d798c534867e6014d219f580534867f65d0d219f997434867d65d0d219f197434875f53d0d21d714f434867f6590d219f996434867d6590d219f196434873f5490d21cf152434867f6550d219f995434867d6550d219f19
  | 21 => 0x61cc8319f596320c67f654c831db948320c76d520c831f34c8320c6f6610c831bd584320c67e64944319f592510c67d65d0431bd597410c77565d0431ddd53410c77554d0431bd58f410c77653d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd6390431bd986410c67f65504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431bd594410c77565104319d594410c6f66410431ed990410c7775410431ed950410c7755410431ed550410c7355410431f598c410c6f56310431f558c410c6d56310431dd94c410c7d741cc431f5107310c6dd638c431d794e310c6f6648c431bd192310c6f5638c431dd94e310c7d6538c4319fd95310c6df654c431d7d95310c65f654c431b7d85310c75e514c431f5905310c7d5414c431bdd95310c777654c4319dd95310c6f6644c431bd191310c6f7634c431f5d8d310c776534c431f594d310c7d6434c431f550d310c7d6324c431f50c9310c77b50940319f992500c67d64940319f98a500c67d62940319fd91500c67c64540319fd89500c67c6254031af990500c6bd6414031bb988500c6ed6214031de540500c67e63d53219f58f54c876e62d5321dd58754c867e60d53219f58354c873f54953219f98e54c867d63953219f98254c867d6095321cfd9154c867f63553219f18d54c867f60553219f18154c873d5415321cf99054c867e63153219f58c54c876e6215321dd58454c867e60153219f58054c867e64d4f219f59353c876e62d4f21dd58753c867e60d4f219f58353c875f5394f219f99253c867d6494f219f98253c867d6094f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c875d5314f219f99053c867d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f219f19743c867f6590f219f99643c867d6590f219f19643c867f6550f219f99543c867d6550f219f19543c86ef6250f21bb18943c86f76150f21bd18543c86fb6050f21be18143c867f6510f219f99443c867d6510f219f19443c879d4310f21bb98843c86ed6210f21cf95242c873d5490b21bd98642c86f56190b21cf95042c873d5410b21bd98442c86f56110b21d794e32c875d538cb21bd98632c86f5618cb21d794c32c875d530cb21bd98432c86f5610cb21cf95341c873d54d0721bb98b41c86ed62d0721cf95141c873d5450721bbd8941c86ec6250721ed50441c875e53cc721d754f31c86ee62cc721bb58b31c875e534c721d754d31c86ef624c721bb18931c87d5310c721ded4250c867e64943219f59250c867e63943219f58e50c867f64543219f19150c867f63543219f18d50c877950143219f98f548867d63d5221db58b548877661d52219f983548867d60d5221cfd52548
  | 22 => 0x1319f181544c77860551319e181544c67e6515131cf550544c73e64151319f988544c67d62151319f980544c67d60151319f997434c73f54d0d31cf153434c6f661d0d31bd587434c67e6590d319f195434c73f5450d31cf151434c6ef6250d31bb189434c6f76150d31bd185434c6fb6050d31be181434c67e6510d31e750c434c67e64d49319f593524c67e60d49319f583524c76f5294931afd91524c6bc6454931bed81524c6f86054931db548524c67e64149319f590524c67e60149319f580524c67e65d09319f597424c67c65d0931dbd4b424c76c52d09319f996424c67d65909319f196424c73f5490931cf152424c67f65509319f995424c67c65509319f994424c67d65109319f194424c73f5410931cf150424c6de6310931b758c424c76f5210931db148424c6f66110931bd584424c67e65cc931dbd4a324c76c528c931bd986324c6f5618c931dbd49324c76c524c931bdd85324c6f4614c9319f994324c67e65d0531cfd53414c73c54d0531b798f414c6dd63d05319f996414c67f65505319f595414c67c6550531cfd51414c73c5450531b7d8d414c6dc63505319f994414c7b54110531dd953314c77454cc531f5d46314c67e64d41319f593504c67e62d41319f58b504c77b5094131afd91504c6bc6454131bbd89504c6ec6254131de540504c67e64141319f590504c67e62141319f588504c67e63d5031d798f540c67e62d50319f58b540c67e61d5031dd987540c67e60d50319f583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c73f64550319fd89540c67c6255031dd185540c67f60550319f181540c73d5415031bb988540c6ed6215031be980540c6f960150319f990540c73e64150319f98c540c75e63150319f988540c76e62150319b988540c67d6215031db588540c66d62150319f984540c77661150319f980540c77a60150319e980540c67d6015031de580540c67960150319f992530c67d6494c319f597430c67f6590c319f596430c73e5490c31cf552430c6f66190c31bd586430c67f6550c31bbd89430c6ec6250c31bdd85430c6fb6050c31be181430c67f6510c319f594430c73e5410c31cf550430c79d4310c31bd984430c6f56110c31dbd4a520c67e64948319f592520c67e60948319f582520c67f64548319f191520c67f60548319f181520c6be6414831af590520c76d5214831be980520c6f960148319fd97420c67e65d08319f597420c73e54d0831cf553420c67f65908319f996420c67d6590831db94a420c76d5290831bd986420c6f561908319fd95420c67d65508319f195420c73e5450831cf551420c6df6350831b718d420c76e5250831db549420c6f76150831bd185420c67f65108319f994420c67d6510831db94b320c76d52cc831bd987320c6f5
  | 23 => 0xf98252cc67d6094b319fd9152cc67c6454b319fd8152cc67c6054b31db54852cc67f65d0b319f99742cc67d65d0b319fd9642cc67e6590b319f59642cc6f66190b31bd58642cc67f6550b319f59542cc67c6550b31bdd8542cc6f46150b319fd9442cc67e6510b319f59442cc6de6310b31b758c42cc76e52ccb31db54b32cc6f661ccb31bd58732cc76e520cb31db54832cc6f6610cb31bd58432cc73e54d0731cf55341cc6de63d0731b758f41cc6f565d0731dd59741cc77754d0731ed95341cc77554d0731ed55341cc7d663d0731bd58f41cc7d563d0731cf95141cc73d5450731b7d8d41cc6dc6350731bd59441cc7756510731ed99041cc7775410731dd55041cc6f56310731ded4250cc67e64943319f59250cc67e62943319f58a50cc67f64543319f19150cc67f62543319f18950cc7795014331bb98b548c6ed62d5231be983548c6f960d5231d758f548c67e62d5231db98b548c66e62d52319f58b548c76d62d52319b58b548c77661d52319f983548c77a60d52319e983548c67d60d5231de583548c67960d5231cfd52548c67e62952319f58a548c67e60952319f582548c73f64552319fd89548c67c62552319fd81548c67c6055231cf550548c73e6415231d758c548c67e62152319f588548c77661152319f980548c67d6015231cf953438c73d54d0e31bd987438c6f561d0e31cf951438c73d5450e31bbd89438c6ec6250e31bdd85438c6f46150e31bed81438c6f86050e31e750c438c76f5294a319f992528c67d6494a319f982528c67d6094a319fd91528c67c6454a319fd81528c67c6054a31db548528c6fa6014a31be580528c67f65d0a319f997428c67d65d0a31db94b428c76d52d0a319fd96428c67e6590a319f596428c67f6550a319f595428c67c6550a31b7d8d428c6dc6350a319fd94428c67e6510a319f594428c76e5210a31db548428c6f66110a31bd584428c76e528ca31db54a328c6f6618ca31bd586328c76e524ca31db549328c6f7614ca31bd185328c7cd320ca31cf952418c73d5490631b798e418c6dd6390631cf950418c73d5410631b798c418c6dd6310631ed504418c6dd65cc631d7597318c6f565cc631dd597318c77654cc631dd153318c77b50942319f992508c67d64942319f98a508c67d62942319fd91508c67c64542319fd89508c67c6254231bb988508c6ed6214231de540508c67e62d51319f58b544c67e60d51319f583544c73f54951319f992544c67d6395131d758e544c67e62951319f58a544c67d6195131dd586544c67e60951319f582544c6ef6255131bb189544c6fb6055131be181544c73f64551319fd8d544c75f63551319fd89544c76f62551319bd89544c67c6255131db189544c66c62551319fd85544c77761551319dd85544c67f6055131ded81544c67b6055
  | 24 => 0x525067d63149419f980525067d60149419f997425076f5290941db14a42506f66190941bd586425076f5250941db14942506f76150941bd185425067e65109419f997325067d65cc9419f197325076f52cc941db14b325067e658c9419f596325067c658c941d7d4e325075c538c9419fd95325067e654c9419f195325067e650c9419f594325067c650c941af99032506bd640c941d7d4c325075c530c941dbd48325076c520c941bd98432506f5610c941dd14f41507b751905419f98f505067d63d41419f98b505067d62d4141ded4250506df6354141b718d50506ef6254141bb189505077950141419f98c505067d63141419f988505067d6214141d7d4e531067e6294c419f58a531067e6094c419f582531067f6254c419f18953107746154c419fd81531067c6054c41d754c53106ee6214c41bb58853106fa6014c41be580531075e53d0c41d754f43106f661d0c41bd587431067d6590c419fd9543106ef6250c41bb18943106f76150c41bed8143106f86050c41d794c431075d5310c41e750c43106f66110c41bd584431076f52948419f98e521067d63948419f982521067d60948419fd8d521067c63548419fd81521067c6054841b798c52106dd6314841db54852106fa6014841be580521076e52d0841db54b42106f661d0841bd587421067d65908419fd95421076e5210841db54842107ad4210841bd98442106f561108419fd97321067e65cc8419f597321075e53cc841d754f321067f658c8419f996321067d658c841db94a321076d528c841bd98632106f5618c8419fd95321067d654c8419f19532106bf644c841af191321075e534c841d754d321076e524c841db54932106f7614c841bd185321067f650c8419f994321067d650c841af592411073e5490441bd59241107765490441ed95241106f663904419fd9541106bf6550441cfd95411063f6550441afd85411073e5150441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141106f46350441edd0d41107b54350441ed90941107b44250441ded42501067e63940419f58e501067e62940419f58a501067f63540419f18d501067f62540419f18950106de6314041b758c50106ee6214041bb58850107795014041d798f54cc67e62d53319f58b54cc77561d53319f98354cc67d60d5331cfd5254cc67e62953319f58a54cc67e60953319f58254cc73f64553319fd8954cc67c6255331ddd8554cc67f60553319f18154cc73d5415331cf99054cc75e63153319f98854cc67d6215331dd58454cc67e60153319f58054cc73e5490f31cf55243cc6f66190f31bd58643cc6ef6250f31bb18943cc6f46150f31bed8143cc6f86050f31cf95043cc73d5410f31e750c43cc6f66110f31bd58443cc76f5294b319f99252cc67d6494b319
  | 25 => 0xa7c6054432af990510cabd6414432dd544510cafa6014432be580510cb7b50940329f992500ca7d64940329f986500ca7d61940329fd91500ca7c64540329fd85500ca7c6154032af990500cabd6414032bd984500caf56114032de540500cb5f5394f419f98a53d067d6294f419f98253d067d6094f419fd8953d067c6254f41ddd8553d067f6054f419f18153d075d5314f41d794f43d075d53d0f41bd98743d06f561d0f41bbd8943d06ec6250f41bd18543d06fb6050f41be18143d075e5310f41d754c43d079d4310f41bd98443d06f56110f41dbd4a52d067e6394b419f58e52d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41db94842d076d5210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d067f658cb419f99632d067d658cb41bd98632d06f5618cb419fd9532d067d654cb419f19532d06f7614cb41bd18532d067f650cb419f99432d067d650cb41af99032d06bd640cb41ded4250d067e63943419f58e50d067e62943419f58a50d067f63543419f18d50d067f62543419f18950d07795014341bb98b53906ed62d4e41be98353906f960d4e41d7d4e539067e6294e419f58a539067e6094e419f582539067f6254e419f189539067f6054e419f181539075d5314e41d794e439075d5390e41bd98643906f56190e41d794d439075d5350e41bbd8943906ec6250e41bdd8543906f46150e41bed8143906f86050e41e750c439076f5294a419f98e529067d6394a419f982529067d6094a419fd8d529067c6354a419fd81529067c6054a41db54852906fa6014a41be580529076e5290a41db54a42906f66190a41bd586429076e5250a41db54942906f76150a41bd18542907ad4210a419fd97329067e65cca419f597329076e52cca41db54b329067f658ca419f996329067d658ca419fd95329067d654ca419f19532906bf644ca41af191329067f650ca419f994329067d650ca41db948329076d520ca41bd98432906f5610ca41af597419073d65d0641bd597419077565d0641dd94f419077b50942419f98e509067d63942419f98a509067d62942419fd8d509067c63542419fd89509067c6254241bb98850906ed6214241de540509067e62d4d419f58b535067e60d4d419f583535075f5394d41bbd8953506ec6254d41bed8153506f86054d41d754c535067e6214d419f588535067e6014d419f580535067e65d0d41d7d4e435075c5390d41bd98643506f56190d41d7d4d435075c5350d41bbd8943506ec6250d41bdd8543506f46150d41bed8143506f86050d419f994435079d4310d419f98f525067d63d49419f983525067d60d4941dbd4a52506df6354941b718d52506fb6054941be181525076d52149419f98c
  | 26 => 0x551329ed81544ca7c6055132de181544ca7860551329f994544cb3d5415132cf990544ca7e61151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d329f996434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d32bdd85434caf46150d32bed81434caf86050d329f994434cb9d4310d329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e65909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424ca7e6510932eb508424cb6e54cc932db153324cbcf528c9329f993514ca7d64d45329f983514ca7d60d4532ddd46514cabf6454532af191514cafb6054532be181514cb7551145329f990514ca7d64145329f980514ca7d60145329f993504ca7d64d41329f987504ca7d61d4132ded42504cabf6454132af191504caf76154132bd185504cb7950141329f990504ca7d64141329f984504ca7d61141329f98f540cb5e63d50329f98b540cb6e62d50329f987540ca7d61d50329f983540ca7d60d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d6095032cfd91540cb6c62550329fd85540ca7c61550329fd81540ca7c6055032cf550540caf66115032bd584540cafa6015032be580540ca7e6415032cf990540ca7e6315032d798c540ca7e6215032db988540ca7e6115032dd984540ca7661150329f584540cb7561150329d584540ca7e6015032de980540ca7a60150329f580540cb7960150329e580540ca7e6494c329f592530ca7d65d0c329fd96430ca7d6590c32cf952430cb3d5490c32bb98a430caed6290c329fd95430caef6250c32bdd85430caf46150c32bed81430caf86050c329fd94430ca7d6510c32cf950430cb3d5410c32e750c430caee6210c32bb588430ca7e64948329f592520ca7d65d0832bb597420cb6d65d0832dbd53420cb6d54d0832bb58f420cb6e53d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd6390832bb98a420ca7f65508329fd94420ca7e65108329f594420ca7c6510832cf950420cb3d5410832b798c420cadd6310832bb594420cb6d65108329b594420caee6410832eb990420cb6f5410832eb950420cb6d5410832eb550420cb2d5410832f398c420caed6310832f358c420cacd6310832db94c420cbcf42cc832f310b320cadd638c832d794e320caee648c832bb192320caed638c832db94e320cbce538c8329fd95320cadf654c832d7d95320ca5f654c832b7d89320cb5e524c832f3909320cbcd424c832bbd95320cb6f654c8329bd95320caee644c832bb191320caef634c832f3d8d320cb6e534c832f394d320cbce434c832f350d320cb7751944329f992510ca7d64944329f982510ca7d60944329fd91510ca7c64544329fd81510c
  | 27 => 0x42ded425010a7e63940429f58e5010a7e61940429f5865010a7f63540429f18d5010a7f61540429f1855010ade6314042b758c5010af66114042bd5845010b795014042d798f54ccb6d62d53329f98754cca7d61d53329f98354cca7d60d5332cfd5254cca7e61953329f58654cca7e60953329f58254ccb3f6455332dbd8954cca7f61553329f18554cca7f60553329f18154ccb3d5415332cf99054ccb5e6315332db58854cca7e61153329f58454cca7e60153329f58054ccb3e5490f32cf55243ccaee6290f32bb58a43ccaec6250f32bdd8543ccaf46150f32bed8143ccaf86050f32cf95043ccb3d5410f32e750c43ccaee6210f32bb58843ccb3e54d0b32cf55342ccade63d0b32b758f42ccaed65d0b32db59742ccb6f54d0b32eb95342ccb6d54d0b32eb55342ccbce63d0b32bb58f42ccbcd63d0b32cf95142ccb3d5450b32b7d8d42ccadc6350b32bb59442ccb6d6510b32eb99042ccb6f5410b32db55042ccaed6310b32ddd4651cca7e64947329f59251cca7e60947329f58251cca7f64547329f19151cca7f60547329f18151ccb755114732ded4250cca7e64943329f59250cca7e61943329f58650cca7f64543329f19150cca7f61543329f18550ccb795014332bd987548caf561d5232be983548caf960d5232d758f548cb6e62d52329f987548cb7661d52329d987548ca7d61d5232dd587548ca7561d52329f983548cb7a60d52329e983548ca7d60d5232de583548ca7960d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cf550548cb3e6415232d758c548cb6e62152329f984548ca7d61152329f980548ca7d6015232cf953438cb3d54d0e32bb98b438caed62d0e32cf951438cb3d5450e32bbd89438caec6250e32bdd85438caf46150e32bed81438caf86050e32e750c438cb3e5490a32cf552428cade6390a32b758e428cb3e5410a32cf550428cade6310a32b758c428cbad4210a32b7597328cb5d65cca32bb597328cb6d65cca32db953328cb6c54cca32ddd46518ca7e64946329f592518ca7e60946329f582518ca7f64546329f191518ca7f60546329f181518cb755114632be980518caf96014632ded42508ca7e64942329f592508ca7e61942329f586508ca7f64542329f191508ca7f61542329f185508caf66114232bd584508cb7950142329f987544ca7d61d51329f983544ca7d60d5132cfd52544ca7e64951329f58e544cb5d63951329f58a544cb6d62951329f986544ca7d61951329f982544ca7d6095132bdd85544caf46155132bed81544caf86055132cfd91544ca7f6355132d7d8d544ca7f6255132dbd89544ca6f62551329fd85544cb7761551329dd85544ca7c6155132dd185544ca7461551329fd81544cb7b6
  | 28 => 0x94f43d0b5d53d0f42bb98b43d0aed62d0f42bb18943d0af76150f42bd18543d0afb6050f42be18143d0b5e5310f42d754c43d0b9d4310f42bb98843d0aed6210f42ddd4651d0a7e63947429f58e51d0a7e60947429f58251d0a7f63547429f18d51d0a7f60547429f18151d0b755114742ded4250d0a7e63943429f58e50d0a7e61943429f58650d0a7f63543429f18d50d0a7f61543429f18550d0b795014342bd9875390af561d4e42be9835390af960d4e42d7d4e5390a7e6194e429f5865390a7e6094e429f5825390a7f6154e429f1855390a7f6054e429f1815390b5d5314e42d794e4390b5d5390e42bb98a4390aed6290e42d794d4390b5d5350e42bbd894390aec6250e42bdd854390af46150e42bed814390af86050e42e750c4390abd65d0a42cf5974290aed65d0a42db5974290b6e53d0a42ddd465190a7e63946429f58e5190a7e60946429f5825190a7f63546429f18d5190a7f60546429f1815190b755114642be9805190af96014642ded425090a7e63942429f58e5090a7e61942429f5865090a7f63542429f18d5090a7f61542429f1855090af66114242bd5845090b7950142429f9875350a7d61d4d429f9835350a7d60d4d42d7d4e5350af76154d42bd1855350afb6054d42be1815350b5d5314d429f9845350a7d6114d429f9805350a7d6014d429f9974350b5f5390d42d714e4350aee6290d42bb58a4350b5f5350d42d714d4350aef6250d42bb1894350af76150d42bd1854350afb6050d42be1814350a7e6510d42e750c4350b6c53d0942ebd4a4250a7e63d45429f58f5150a7e60d45429f5835150b775194542b7d8d5150adc6354542bed815150af86054542dd5445150a7e63145429f58c5150a7e60145429f5805150a7e63d41429f58f5050a7e61d41429f5875050b7b5094142b7d8d5050adc6354142bdd855050af46154142de5405050a7e63141429f58c5050a7e61141429f5845050b5f5394c429f9865310a7d6194c429f9825310a7d6094c42db1895310a7f6154c429f1855310a7f6054c429f1815310b5d5314c42bd9845310af56114c42be9805310af96014c42d794f4310b5d53d0c42bb98b4310aed62d0c429f5964310a7f6550c42bbd894310af76150c42bd1854310afb6050c42be1814310b5e5310c42d754c4310b9d4310c42bb9884310aed6210c42af5924210b3e5490842bb5924210b6e5490842eb9524210aee63908429fd954210abf6550842cfd954210a3f6550842afd894210b3e5250842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210aec6350842ebd0d4210bad4350842ddd465110a7e63944429f58e5110a7e60944429f5825110a7f63544429f18d5110a7f60544429f1815110ade6314442b758c5110b755114442be9805110af960144
  | 29 => 0x50e7d62d41439f9875050e7d61d4143f6d0f5050fba43d4143ded4b5050feb52d4143dad4b5050f7a52d4143de54b5050f7852d4143fa14b5050f6852d4143ded475050ff351d4143dcd475050f7a51d4143de5475050f7851d4143fc1475050f7051d4143ded935050f7b63d4143ded0f5050f7a43d4143ded8b5050f7a62d4143de58b5050f7862d4143ded875050f7a61d4143de5875050f7861d4143bb98a5050eed6294143dbd4a5050f6c5294143bd9865050ef56194143ddd465050f745194143ded425050eef6254143bb1895050f6f5254143db1495050ef76154143bd1855050f775154143dd1455050f6f5214143db1485050f775114143dd1445050f7950141439f9885050e7d62141439f9845050e7d6114143be9945050f7a6514143f6d0c5050fba4314143ded485050feb5214143dad485050f7a5214143de5485050f785214143fa1485050f685214143ded445050ff35114143dcd445050f7a5114143de5445050f785114143fc1445050f705114143ded905050f7b6314143ded0c5050f7a4314143de50c5050f7b6214143de9885050f796214143de1885050f7b6114143de9845050f796114143de1845050ebd6490c43cf9524310edd6490c43a75924310f5e5490c43e79524310e7f6550c43bbd894310eec6250c43bdd854310ef46150c43bed814310ef86050c43afd954310f3f6550c438fd954310ebf6350c43cf94d4310faf6250c43eb1894310fb76150c43ed1854310fbb6050c43ee1814310edf6550c43d7d954310e5f6550c43b7d914310f9f6450c43d79514310f9e5450c43f3d894310fcc6250c43f5d854310fd46150c43f6d814310fd86050c43e7d954310e9f6550c43c7d954310f9f6250c43e3d894310f9e6250c43e75894310f9c6250c43e31894310f9f6150c43e5d854310f9e6150c43e75854310f9c6150c43e51854310f9f6050c43e6d814310f9e6050c43e75814310f9c6050c43e61814310f9d43d4843e750e5210f6f52948439f9865210e7d61948439f9825210e7d6094843e750d5210e7f61548439f1855210e7f60548439f1815210f9d4314843db5485210ef66114843bd5845210efa6014843be5805210f9d43d4443e750e5110f7751944439f98a5110e7d62944439f9825110e7d6094443e750d5110e7f62544439f1895110e7f60544439f1815110f9d4314443bb9885110eed6214443dd5445110efa6014443be5805110f9d43d4043e750e5010f7b50940439f98a5010e7d62940439f9865010e7d6194043e750d5010e7f62540439f1895010e7f61540439f1855010f9d4314043bb9885010eed6214043bd9845010ef56114043de5405010f5f5394f429f98653d0a7d6194f429f98253d0a7d6094f42dbd8953d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42d7
  | 30 => 0x800a00180020008003000000100040020014012001001100080020004009000000000140010000009002000000080040004003000800400000040004000000c0050000000000c00300000000010000000000000000130000010001000300040020000000001800000000000000000000f6f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0f7b50943439f98a50d0e7d62943439f98650d0e7d61943439fd8950d0e7c62543439fd8550d0e7c6154343de54050d0ebd65d0e43cf5974390edd65d0e43d75974390f6f5294a439f9865290e7d6194a439f9825290e7d6094a439fd855290e7c6154a439fd815290e7c6054a43db5485290f7751946439f98a5190e7d62946439f9825190e7d60946439fd895190e7c62546439fd815190e7c6054643dd5445190f7b50942439f98a5090e7d62942439f9865090e7d61942439fd895090e7c62542439fd855090e7c6154243de5405090f9f5390d439f9875250e7d61d49439f9835250e7d60d4943f3d0f5250fae43d4943dbd935250f6f63d4943dbd0f5250f6e43d4943dbd875250f6e61d4943db5875250f6c61d4943dbd835250f6e60d4943db5835250f6c60d4943dbd4a5250ef66194943bd5865250efa6094943be5825250ef76154943bd1855250efb6054943be1815250f6d52149439f9845250e7d61149439f9805250e7d6014943bb9945250f6e6514943f3d0c5250fae4314943dbd905250f6f6314943dbd0c5250f6e4314943db50c5250f6f6114943db9845250f6d6114943db1845250f6f6014943db9805250f6d6014943db1805250f6f52d4543db14b5150e7e62d45439f58b5150e7e60d45439f5835150fd743d4543ed90f5150f7752d4543f9d4b5150f6752d4543dd94b5150f7552d4543dd14b5150fe452d4543d914b5150f7764d4543ddd8f5150f7743d4543dd90f5150f7762d4543dd98b5150f7562d4543dd18b5150f7760d4543dd9835150f7560d4543dd1835150eee6294543bb58a5150f6f5294543db14a5150f775194543be9825150ef96094543bbd895150eec6254543dbd495150f6c5254543bed815150ef86054543dbd485150f6c5214543dd5445150e7e62145439f5885150e7e60145439f5805150ef66514543dd9945150fd74314543ed90c5150f775214543f9d485150f675214543dd9485150f755214543dd1485150fe45214543d91485150f776414543ddd8c5150f774314543dd90c5150f754314543ddd885150f766214543dd5885150f746214543ddd805150f766014543dd5805150f746014543dbd4b5050f6c52d4143ddd475050f7451d41439f98b5
  | 31 => 0x4000003c0000004004002800000140000000000001000400040020000001000000000140030000000000000800000030008000000000000000010044001000000200040020024000001800200040020000004000c00000000080024001000c00200100010018003000000100080290004000000000c000000800140080004004000c0080008003000c00500140000010002000400100280000008002000400400100110004012002000200000000000001000c00700000010000001000c007002c00d000000000000000008004000400100000050008002000800500000060040000001c00100040010024005002800000100040000005000000000080040010002000000100080040018002000000400000070000000004400000340040000000001800b000c0040000000002800800000010038004002400000240000000001000c0010010003003400300040020024003004c0100000002001c003002400000100060024003000c006000400b00000030000000008c008000000000180020000004000400000000050024000002400a00000010000009000000000000040008002001000200000020004006003c000000400300000100008000001000000000030020000000c0060000002004c004000000100140000008008001400200000010010006000c00600000010014003000000b0004000000000200200000000001001c00100000040000004000400500000000000001000c004003c00000040050008001000000900000010000003000c000000c00b001800600000050000000001c002000c0080000005000c0040030000001000000040180010002003400100000030004003000c0010000000001c000000800000000040008001001c001000c001001c0030004003001400000000010008001000c00800300050014000001c00500000090000004000400000000040000000006c0000008000000400a00040000000001001000000140000000010000000800000010000006001400a000400700000010000000000000600180010000000000000900000020000000000c002002c00a0004001000800000100020000002000000000000010010000000001c0000000000000000000040000000000800200040030000010000000b002000000080000008000001c001001400c00040000004001000400b000400700000000000001001c002000c00600000040010009000c000001c00100080000000000000000000040000008009001c0020000000003400200200050004003000c005000000900000070008006000c004000000000640050064000000800000000060004001001c0040004006000400e00080250004005000000600000000000000000800000000000044004000400600040010050001000000c000c00400100020038003
  | 32 => 0x20004000002c00600340020008004001c0000000004000800000100050064010000c002000000200080000034000001c00b00040130010007000000900140060024000001400100000010000006000800c00180030000001000400a001c000002c000000000100180010000000000c000003400300280000018000001400200000000000004001800200000000000000000400100000040008004000801b0000007000c000004000100040020000000000000c00080020004000002800a00180130000002000400a000800000000140010003005000300100000008000000c001000000300080010000000000000000000060000003000000a0030000001800000000000014000000400400080040004000004c00100000090010002000000100140000008002001400000000010000003000000a00000000008004000400300000000000000002800000080010004000000800000040030038003001c0010004001000000100100100008000000c00000240020000001000c0000014003000000200200000000000001c0110018000000000000240000000000001401500000010000000000000500100000000000000800100000040008001002800000100040044010002000100040000040006002000200100080000002004c003000c000000c009000000e000400200380020000004000c0130000010001000100040030004000000c0050004010000c00100140000004002000800000080010000002000001200200020020001000000600340000008000000000a00000000008001000000e001000700000160004000000400500000000008000000c00a000000100240010000001001000a000000000080040000000001c00000540030000000001000200040040004000000c00c0000003000000b00180010004002000000d003c000000400000000020000003000000000100000014000001c0010004022000000100140070004006001000000040050014000000000500140080000003003400000000080010002000000600000040000000001800a000000000100010024000000000000000100020007001800200000000010000000000d001800100000020000003000c000001c0000008002000400000000000000003002c0060000001004000000000010004008000800000000000010009000c007000000000240000034001000000e00040000000007004400400000010000000000000200000030000006001400d000c00200000000000000000c00000000000008000000800300000050010000000000000000000004000000000000180020028000001c0030000000001c003000000100000010008006000c0000000000000800300180050000008001000300000010008000001800300180010008003003c00000080000000000000
  | 33 => 0x1000200300020000001000c000000c006002000000000000018000000c00000000070004004000400800180000008000001c01c0000003000c0040020002001800400040000004010000801200000030004000001000b000c0000020002000000b001000200000010004002001c000002000200080000000001001c00b0000000000400000080000000002000400b000800500080000010000000000500080070008000000400000140010000002000c00700000020008000000c001000000000000000014000000400000540000014002004c000000800d002400b0048001000000500000020000004001c00300000010000000000800100140050000005001c0010000003000c003001c000000800a00000000000007000000200440020014000000400300040020000007000400a0028003001400400140000010003001400200380000000015000000100100040020001001001f0000003000000300000030014000000c003000000c0000000002400200200080008001000000300000040008005000800000000000004003001400900000020000002000000400180060004001000000200040030000002002000100000010000002000001a00080020000005000400000040020008006000c006001c0010014001003800600100000008000000000000040010000000000000b000800000140010008008000000a0008007000400b000400000240020008006000000000040020004000002800e0018005002400e00000000044001001c000001c00000040010018002001c00400080000028002000c000000000000bc00300280000000000005000200300020008000000c0000000002000800500000020000001002c001002400000080060028000000c0000008000000000100040010014005000400900380000004006000000100400000014000000400000000000000000002400d0000005000c004000000c0020007000000a00000030000003000c000001c000000400300200040000001004800000000010030002003c0040008010001c001000000000080040000003000000200140020004000000800300000010000002000c0010004000002400000100080004008000000c002800200040020000000002800e000800500040000004000000400100000000000001000801e001400a0010001000c003000c007000000100280010014004000401500000000000000001001500080100000004002800a0000003007c004001c002000c0090018000000000000040000000002000400000080040010000007800300040020008003001400d00040050010000003000000180070008005000000f000400000200030000004001c006000400d0004004000c00100000040014000000000200000000008002001400000040010000008000400
  | 34 => 0x6ac38e8887a0e5a95e80007af0eb21f48000c741cfc5a080003a0a3500000bbe53f11481fc9f6e5bc0000000000072c800003e00000000000000000000000000000000000000000000008d1800015a0440000000043db2c477295024cc02320000000542aaee5b1a35800016f85a5000000000000688000705800000031ae9138000000193c0001a22966108c000190022980000000000000186e1a000006f10000000000069903940002a845fba1620002e446b68b128cf29d400000008b9296600022620000a0ca0d80008d382ac000304848628087c30000c9700000de8000000000000011c6cf927b0c199f4a7562abcc480e2c29a11ae2ad24b8000310653d29646a7000000000009c60000000000090980000000000000330476b109e000000000024482e88a409f38000000000093180000000000000198c000252600000000d500000020000000000000000000018000000c0010000000000000b0000008000000400140000000001001c0030000004000800a00000010018000000c000002000100000000000006000400000080060000000000800200000010000001000400100300000038000001800000000000084001000400400000030000000000800000000000000003000c00700180010004000000400c00040090014000000c0010000000002c004004c000000c00200140080000000001c00f000000100000000008003001400100100010008000000800600000020008002000000000000000000002001c00100080020014007000c0000010001000800100100000014001000000300140010010001000800500180080038001000c00400080010010000002c00e0000000001c00100000080024001001c00300000000018000000000000000000008011002800500140000000000004800200000000004001000000200280000000000001800500000000000000000c006001000300000000008002000800100040000000000000c005002000b0024000000000000140010018000000000200000020010000000000800040010010013000000200000000030009001800b0000001000400000000050010002000400300180010004000000000200000000088003001c0010000008000c003001801300000010008002006c000000000f000c0160000001000c0020014001001c00000000120018000000000a0004000000800200000000000000000000100380020004002000401300000150008005002c005000002300040000000000003c002000400100000000004002000400f00080000008000002000c00000000008001001c003000001500000050004003000400200040000000000000000000080000010000000400000000000008003002400500040010014001003c003000800000080000000002000c000000c00300
  | 35 => 0x641f6c0001d1c00000000001d54000000000000009452e1e3d48f5800000005ecaa3600000000002f2400c9ef200029a8ac697b06879e541c89f949ce829a75a858601e329ac3385eaab09bfecc72cd8993a19a9722fcc9fa308ac490000000000001a0000b5b8c0a438800092d800000000000001c581058000a01a7d231d800000000005bb207600000f262380008b48000000070eb3504e081d27820998b4c0c89820900000006e80003879e4c00000003a6966681114dcbb684369a224e4cb182da57a23bab422b46294800056800000000e788a20fe04bb2ea2000000042517c068014720000e520001c5cafe10cc0e580004e08000a53800000003f0418a318807257eb018c2200031786a000000000000000000000007565730000b7500002cc00000002678000000049e80009cb0000000000000000000001e660e7a816a0b0f340d484608bb1bb8000000090f1d220002e4a9d600009f18000b0a229600008d228922ea0fa105c0000000208aec02c100000000000112805e000245eb6b000000030222e980005292e2c0fb32bc93ba180bdd8da45b400005de000000000000000000669b0b40250000932000079a177c0000000cd0000000000000002f50c9f929400025ea00000000ed85f6bfbab483d50000a3f800085525de000210aa5f9b1e88200009550dce576acda6f9271e2be079a2d489fc0002f945d68000c8f81261f900000d113a00000a60000315000000002b30000c648000605906a809000000000000000000000000000017960000000000000000006f29241bbe79b8716000000000000000000a3400000008b080004b5000064e800080d315e882af2000800003e90a720001084c472b6c00012f80001440000000025eac928ca826e86a8e040001e4493800000000000a3a8f1e0001c900000000000000068b192200000008cc0c40000279200028429bf800000000000000f62a9f800000027048b194040000000000119ea46a3d60002c78000071213900005ab2aae00019c2a090000a3180000002df20001adc581b1845e10b8e4cfa3d45f8a85480f8d2c982ae38b51048200030ec6ec0cee00024f800000000002f320002328386826a00013ac00017e068d0e6c21c30be8258000000149e0000000000253a97180002d2800064d0000b391a1000028e800000000b900006c080003ca8000805251c000111843f1fd637980003a580000002e6200000006c99c002cd0ec00000694234000000000000000000000148236f800073f800055780006ca800000024a80001cd8000000023e28880000000000000071180000000e54000000000000005e00b3c0002fc88080000652ab64122b294a7b18be0001918c29885a6d9800078d80be7920000cd704de0d080000000000000000000000005ea865600022bc88519
  | 36 => 0xbb80ae00701d78000aad8f569e60eb453b8000b1dac0c0000000000000077c186a00000000002ffc0000000209a93e000000000000001e28816c190b24694800000000000001ddc0001d92000000094d000000000000000000b999bbac18800033a2a7a11b00003098a26000225457898e0c858000000201e00029b600000000000000856236ccbd000000032ac51312461fbb052875910e00006d0804326e04408b22c880006480000bd7ab68c5f000000000003da0000000042e000103e000000027180002b6000000000000000b4e54bae2e0000000a9d0a641e331dc329180c88109680000000867800000000000000000a278588000000000000009482b0000013d20000000a642938000042200000000002bb8ccc800000001aa0001eb00118e400001802ad380000000fb800d847800000005f3b17a78e1a2ea568000ab81f34759af463b925764c9ac9c3428a4668e17faa2b339e00000003ed8000689000000023f20000750000101c6c3a1900000424000000000000000002c9a0000a4400012086980000ae1ae9ebc583ea0000000a6f00000002370000000000000004c20000589a02c0001ed2ce1051ec2702de000062a000125400000000000000000000000013ee79e0a107fe0000708a18c0390000730aaf429612961ab955485b15b625d30260aa87f4666245402a9e6a871321a892a3389de11e800005a8000000000000000000000000323a3f2214c0000000c831b00a948000a308fe20002f8e987283e000000000024060002830895ab0800000000003138000187429400000000000000043003b80000000000000000020b800019b99e20001e766f58000ccd8000483938843c95eabb40fc0ced93aa2e00c2e7c3a17617f11b29f68000484b3ea9a618bc84b93b68b708065d4870838e80007cb052e08030f6000006a821abe22ef26cca13a6185179d6c934a00817495b40ea2daa830ae1600000009d3800043525a4000000045000000002b020000252000000000024aa9252ea49b480000000000000067e0003366b9e0000a5d0000362840657c84b2225a5922a1307ebd283922df800073da53800000000000000ba3800000032f0aeb14b60000000359000055080004b330901e180009b20dd00001c5400033700000164000000000027c07032464a84048e10b000000001d067c89d096800004de800000019a879d00005f41e8a149a6ce00009622af33240000000000021c8059e4a41080004d400003b418f25d611d61430000000300c8dd86645640844000300a63c00000000000beb10e0bcd807c329b0b602180000000c3e64d8162048b1084bf800000000000001ffa8d7800000019aa504884e0df00000000d905e48cd29f59338cce18a29a911b83cb12e0a8e0346bd0a018000057e45a0000000005c0
  | 37 => 0xcf580000001b34ae580009b8a620bef81464b191fc5c00ce40000000000141e32307b80000000416800000000006e188aa0000000755a36867c00002248000000000067b00000002f266602fb4c3f248e04d87605ad21787f48000000308e000000000000000000000000000046f800095321cc13024389c529280001ec000000000000000000000000032fa000000088c242821ba46e0cc800000004dc0000000ce0990e6cf333c00010324012b9e51d00007b61f28a8922b600000007d501d8ae81d2843990d012180009ec80007490000000250c0000000000000037da0987deac420000000000000000000007238ac4a7480000000e90a4880000001bb200007d6b6a28620001092852000097e0ffe00027c80001ad81ba8c707b68e20884098ea99acb8000000000000f62810000000000000004ee000212a00005c0992000099095c200023bc000065404f26be7e580000000818000205c00000000002ec2c6400004b880000000000b7f0000000000000003284a0a3ac46b227600000000000000000241e4bc1ce00000a8c959021a113156c8460b8cad61dfc0000d3440d27aa66508be00000000001c2014a8d62c1280007b8309a55984505d215de9d98fa8b37aebe2b4000000027be000236090d2cc61210000562081e0fd800000000003d20d708800c369e5a8047ad8b0ace31ae8a971cec3a2aa5052cae14238264c9e9800000029a0bab91720001b8200025bc9c58000000000027780008720b02000174241500002339020000000000000006a400000002a5e6ddb32000000002519f4258c2e56ac985406e42d3e3de07103a1157e82b00003758000000000000000000002c0a0fc86186e780005e2834e782aa54000269a0002ce8000000000011a6aac8000512a37a864a2d000023cc0001a0c00000006bc8a368c79d00000112883487e0b30033a82a1aee87d08b44ef24e80000000000027c0000c06bdc800000000002a8ad0e000300800000003f5a07000000000000f7e1918fb278d0044003070c00011560000a56c25072a000068a00033063c9339caa58b7c214800055a80000908d2641231be98f2348400320400012b200001025f2ae262c82eee00000000000000000132a0000978c300000a16000000005460000000c8d84f617d000048a8000000020ea918bd6000279e7ae9ea858730d60000272b872eb8bc0207e0001924000027007f12d019116ba6410000000000000026a0636afa4cc080003b78ace93e96f6a158000b67224000006caa238000000000000000d600030bc9022f3858f098c00019a07638000000308c7f885424dca7741e880008e9834035e0b0e7ed099e853af442aa1e248df887400029968280ea6022a9ac3a4ad5a77900009e39d865991b7e567b29870630f0c2c1b3a4660
  | 38 => 0x9f72650124026614b80002c10270936c91733fc0000a7080300000001310ad7a4b092f1aa08c9126609006080002dd600000003f092f60000000cb5a7549c680006088c8400012de00022fc0002df400000002c531bacc68b44c7d31a662eb35492e840213f13d43be00000000ba03fc85f261720e80000000000118c9ea00000002d6c000000000000006649984264a54600024ca4670a78643019e0000000000111a0000000000000000000000000000000113aae41eaa0a8162a0001d5a0002dfa95d1bc600000002c180001b519f60000000000294a00010400000000b580000000076c0002b820001e18000115495716784b7000099c00000a9000000000004828000a168000000000043a9a74b760000000241a0000696ac480400000000000000000014ae0000000c80000005728b0b7e026c2c400000000000000077c00033f80000000ce180000000000000150c2640000a2e1e26000000056680000002eac212000000007aa00006e20001edc0002e103eb1c80000000072b99880000c68000000000000005d32cf002c84be00000a80002522714a50e000187e00000004ba871a27680008718000a6e8000000000000000001d48000be980000000000000000000000000000000ba0aca8c5f8000000000000000008c88000bb7a3f400024a00002378464800077f80000001a3c0002e32af50000000213814d0f4e62b800037180008ad01f275f800000000001e98b387c814000000e645cb2ca6a03204002900003e480000000000a0f06d64338000710800021994a8462a2aa000000000000002d880004619ab2500b2ea23600009de885ea669e1cc1e09aca82a81aa20851000022904e623fac5ba1ae82ba08ca75ae840002e903d128a04de08e40003218aa1989e00024c05c19b0ab5e2be4c928cfa9c1800000000003f2800000013a8c13800000000005250000000000000000000002d8a00000000000000000334a0000000000000064a0000bbc80004f9334e47880000000000000285032500007761cc60000d7c0a1b14c19e06a60002114a3b28c40001e1abf8800073100000000ade00000000000000000000060280008e688cc3340d0c00000008e813ec0000000000000038288580000910000000000000000002a900001e5e000000088a800000000000000000000000000000003a1a38ac760000138b06e000124200000003fb8f0abea26b253a00000000000a9d8000000000000000002f000000002dc808d151cad0000058c80007378e5e443246800000002420fb00000bfe0000000000000000000000000000000000000000001982b9cb0d82b400019ea00015560e92b924510592b0b09964cc8000000000000000007f400000001c480001d50000228e931114201480007e9ab0c36a800000011a49b700009758000
  | 39 => 0x3f1800067406761ad00ce0000000c73a54a0002db8000325400000000000fd000000005fa9a7c000000006d800000000006de00000000dd8000000088a17acaf9930418c828c9fc8000965800089c32e485c80005a6286c1468356000083804333769272e0642ea8920000a82415935e31094083b20a80000000023c8000000000000000000000000000000000028e400000000000000000000000000001ac000000000005c71a9e0a0aaac00f11ba616a4b26bc03680001b383b480002821454000000000020fe00000000f60000b8f848800015f0c818f1813d1b4c4ec95d456c000077580000000000000300200014982538000000000000023da37c000030580000000000000000044b00006520000921ada20000e6e31f894052fa26c10107acad428646fd10685f98000aa88000c8c2bbe53b12f4000000000000000000d1428f9aa60e98000601a74c000224c5d71e4e96c936a39c8bdaa1db0d4c24a4a48efb202812aeb688fb13c00028e0c1c8baa0000df45cd80000f4800000000000001878a79010600017f2082a93acb3a32cbdb924a4e29f9c86884ea486b3000000de40002fe6c0900000001a0600000000002062726115062310d81fd8000719a6845cca10cafb00001b700001b10eae422834c3d420929598064000206e5601b4649e19441c1991e8238000cd48c780c485b00000000c1c30b89d730ea0d2800038f8e24000000000000001d2a46c0000000000113069b996a60e298663a91bc7ea9bceaa91ca25c085f885f0000000000000015fa00000008bd800041b8000cab99de000048c801800034a800032d187003400008498faa24093800001ea6511a548a768c6c25d8000000000000003c8000327000001f8b400000c8d1d7839284ca000048000014d8ae3800087282d400022e061c80580002f3a7d68000883a43a317121c000000000012840000000bdd28a29faa15c0000616ab2b23200012069942aa094fa8e249a2c3a569b2de621072c00032aa9371a329a52caa1358000000019c75804d00000000000000000000004efaa880001acc1ae0ec4542030e00012b4c9b0000000040c22716c22a70000465acae000000000000004df1360bdc0000907097e0000080000000037b80006d799a200014f001823ee9e3064e0000000695a3c264285fa00007580002d9229d00000122a1e7a5a8f69e2ac2a71c014cb1d160029680003bc000000012b043d000094100000000000000135800000000000000b1c82c857280000001e283980bde33e0000284a9b000007dc0000000c7000001830ac0000000000000005790000afc80006d2800000006980002dba644800059400000000398bd01b28888912627b80005b71f9a3dc15502e58f0848e0fe48118000000000080380004ee00000000000000268032000008f1
  | 40 => 0x975629aa15e1cbaf0286088aeaf226745ef116e2fa22641d317dc5a5a69000021b02faa75255728dc2480000000135a8b9888a44531de00000000c980009a7af545a3281c2a780008250000000147e0001f3c05e0ff4838a3c42d1a8ae000257c1682d967a30000000318e00000000001bee55280004910918b592a48000187a00003840000528b53800033c205e76094d652180009d9000049d0000b4100001dd9d1600000000000000000000012a928a4d9000096a00000001eea0002b3800000000002e924df86e4667949ca6d1e989ca8d8c01c8db040c111294ba99494225849c8007a2d8100e0f10b16a19a8527ef80000000aecc43800000026c062580000000128997a236aef066227c9aaa0000000a708aca0afad7091c173c5659e8818d8f1213c0a3c0000b2c0000d429b69ff62702a6ca4daa061b7800000028d60000000000298e000000000000000001b6e0000000a061a480002bd60001532391244c000000046880007730a2e45e82fa0000becbb806661c80000b14a6c40002b42b7780000002ec829531e2000015e2f20000a331250b2f96f29400000cfb800000000006a38000385062c00000007521ce60000ff600000005378a322c721f830a95b84d70e2200026f470e84e8000316652203360000000000122232a80000001e8e0002926000000000000000002a8c00000002eeb4040000000c58b14020c12eec8b80005c222860001dbcb9a1d96b9f2a3c00020cc6b3a9de73b80007bb2d2e226281e00009fe17800000000074000000000004080000742baf00000000000c718b769262b841fb275a00020bc8b2000000000004cba6527fc0fa05c63042ac60d320b0ab6a2b1b13eb77000075100008b505a400000008b100000860300000000000027e49ae0000a83166086e87820001fe8000002e90b08e27a812a60001aca5f09cc8000000000000007b41cca000000099f80000000000a5125b820380b6a7880000b711b00000000ce2a7de8d10ea80bf824a0002bc01040000b88800000029500000c54bac2a4a096096a9d1000000000000000000109800000000000002f148412bfc71b94c098922444580000180104e0a580006a48d1e8fb19f40001c32bfb235600000007e800006cb2e5ecf21e8477c80007c700001e4000000000000000000888000007117125968000000000000000007809df60000000c31b0aa00007b075a148c0000000819215a5f1016c8bc000058e93740718e380000000000000000033a0224148a5298a6e41da0b698480000000000654333e9bc0000440b252000052cb900aa400013c65510cb20c1122e22380005b6adea3c58a1cb802d4200000004da0d9c48f2fdc00032f20001e3cb8db3e0000000021aa02e30c099ca60b2a2000166c1c606f650fa9d8960330800007fe000000
  | 41 => 0x688000014f0000000290200029ca6152a2081aa8da9ee22d822c00000000000000000020f0000b5f00001e5000000002564681e1e1458000000121e00030d2361800000030105dd863a3a880003372282000184e8c180000001b18515800069095c06d200003269916b2907fa254238e2b8af3400000000002f1e6820000045000000020607631c8c915800040200000000000769864c41780000000000b1f8000000000095b00000002342000000016aa72e35b800000025127f9967e000285c00000009543130000000000000007ee29e81da00000e189ceb702932000000000000000000000acb80009e0000000000001ba20664e197748a800005b2a11c13e00007d181cc18085b8b4a9f300001f2200000ac7c09954a8c092800004d489d03ce88727cab1f18b2000000008c0000af8127cbd3afc471808fab00000000000000000000000000032e800000000001632202a4a80000000000000000000018c6a4580001d69bf800016fa71da052a692588cc8a90000018a600023b299500007c98bd0c930000cb811b600001d40000cd400000000000000000237200006880000000000090e000000000006ce0001c1a000184a0000000b1e9c24000000068280002bc8000000000037e8f2e43017405e9aa22cf32f4c000000000012cabb723123e21d2069183da5d113185bb800000008d69fe1ec40000fec26c91da000273e000000029715c400011de93880004e50316000168a0001cea0000000cca800000013fc597a30a00016aa454aafc534000062a8000000239c72f0732c1680001d1a02a00007001271f80000002ac511f90000126e23a000000000000001feab12861ec1a23ae4650dfe8b7800077e000000000006392390adc2de60f58000963270c0000000000000000000000609d9a0000798b6090be8ff03d440d9fcc3188c74973a422c7c9a0e3858b0c75bb0f262027341f1237ca6732be3d6a9be70d141c79f2266b55231075e9c2a9640db645784701b82e968788124ba329767ce284c06faf900000000c6cb26a40b800000020ce00000008739b447a6989a056a03c52e97907778b90000000047515a26100000c2900e0cef000094c15d8c050330b260000000000032e0d360f413a4c0d8ce200000000000000000280e0001b08bfe1aa46590376000000000000000000fbc74e80009b180000000000cd880001a0803a7f000000000000c2080004d3800035d26e8a9c1ffe000303eb328a4a12c0cbe4d51b3600000000001ab60002c0e000000000010280000000000000065b8000c6e0d22360800003a800050831ea989885005e800000018644c30c5a00029f2b2d80004b62b14000221800031b6000000000010a60000bc2aa7a658c87ad02b7821d800000008f200009e92e04799038827c2570013a2325da883a94
  | 42 => 0x284a00016700000000000000000000009d2838a580800000011f0a7d0000190806e0000b82b181c1040e19d26e5055eba68efa6aa13e23b726aea112f58c8e14d2cf709ba27225cc5ac9f8a39333ac00001e4b0d099400025f2b158bdc492098a00029faccb800004f80000000c9800000001e4adb27f1000000000005b78000a5b012c71b2c64015aff4b8223b40582a9a6b78e667bc2b545d2b38e000000044a87444810000000000079b000070b12bc1d20000b7400004308000cb2800025b0bd2093277251e80000000ca8c66a20600019e6cf2aa8ac3f8efe564aaf82dd21063aeab300000b6ab070eac2710000c988afe6782dce4068be0556800000020f430e1b223658cec0a9800090606300bca3667410000bbe80005b89f760002dbe010b3d8000000016730400b28000000000000010500000000000000000000008d68000a2980fa0000000985a39203c23ea4e718c83bd25c404c305e575818aabd8000000000000002940000fea0002b7e00026f82bba8be3ce2130000092c4c3a87c76c14f605c8f6000000000000000000000074b8000ae8ab7c7a0ae547de318a00024300001ef61711db454f1e626e2a1de8a910146588c8208e05b472d16e4b528000000093ec462d0a0002f1a0002672970023e4bc80000001b044e1000000016c8cfb000098b2184000097028692001060308000000063b80005190000000000012e00000002b16bbd8000a26288a2f3800000000008fc00007752ab800000002411d0aa1b8000b24000000006ecc1b2b7874683643e88d306cc0d3a00029cc00011ca00033c2cd825e60002c1ab58994e00000000001f0600000b85928b3e91109486df20c05dca4a253e9d26ba50a38b239cd6000000026d0000000131a0001cb00002c220000000afd800059619b2000000000000001cd800000000003a30aba000112413e98e6145139e51d8000054810800000003e780005de80000000000368aaea0001e2200032dc76a16bc75301de06607ba6dc800039d1da0bde907c350220c00000000002f3c68101580002a6e7c21e302379a1c8be0000000229c0001f8e0000000738a3ce1b4b3b0102800058388c6c570000000106c47080001e2228a00024765d880004af80000000bb600007e8000000077a83b200032b0000000000000003da9eae0002bdca64a1707c58000b809c0421e88ba0001f5e00000005ae144e00000c8c9c80000000000ca380004fe30468ec29c8000157a5111e0c0002d588da8d12af188fe91813703a001a0744a3de4259b1c345877080080009851aec69880000fe8466000000074610b28211efe2780000c82000000033640002d30b890a90b5e871e4a3a7ecc90a82eb8a311eba002680002d2cb22a69c6f82e7e1ce2a60000000056285ac6ae195c048028a00000
  | 43 => 0x3507228000ab9a7260002b1e6fe89348f48c4a000031000000007cb96522fd000000004c63de914a66b0caca452bb4000000000000005fb0000000000064c000024985e207a97de1d896865ac1fc8af3000000015fe3e7000000024360000000000000000000000001a54000038c00000000000e1800017b8809a756922898491e901871e92a45ea00006a880005670000000000000000000000c7c000107044d82b2000010416580000000d0e000107e88e19a474c00000000000996b23c18e00000001a94156000000013408378000000134abc3800070b800000021ec9f4328acdb8000c13000000000006351fde0000000000262e7d3a272cfe86c875920280db0724000000000032648068ac2000000000010e80001c0e0000000000000039d8000000000052380004b38c560000000cd192ae6f72c5800021a00001ee68781a58595a790a958c9e0002f6a00000c01b6ac325e6801c06c24ce9fd24ea412a9b200000000000000a53023644200004f7863cb21932c619800011500003ad97f4bedab4a00003de64500008fe1fb0b0b813a71d00000000000000289c6af055000029a60000000285b0e8000308400012a0000140c60927428ac14e00000000bd8255a00029700002860a1e00007840000535150ec2c80000003086000127694924020002260582800035ab1e8091801abc2a70e6b1820412db01c0000000771000066e00006440000018800044d199c26fadb0804b02c9429ae030c91106d3800010c93d65650000000170400008b6ae2000006c8000c40800000026ba0000000760000079cb2600ca95ee0001e5258d000014e8cc650aa60e5c41e0e4cf123680cb1006a695be934224675d00007cc80004e69dec147000046080000002cb0a4600000001fec23d80001188c90c2624d63e28ca2b1ba9c092b14c490300008209ba8000000000006a2187000050d85242222a1a48300de84394fe0002578adc919000000a64d8800000004c2000000000002ea21da6a60fb80000000000000000000000000000000000000050c03906fb00003050000000234c00000000000000cf48000000000058492980000000bea98b81a78000bcaa40ac71000000000000001f0a1ef051883f2e7a75f253282f8f860a7000000015364c2aad82f9152800030e0bf9178c00020a203698a811c800035480003e109e4ce6a682c0f0000bfa29c6aa7168e000268e0002e2027881fe58b9ed6b730000bb5a8f4a500000c679e4600000000000000259268c00000000e3800000000000001f12000000000000007e3000000021bc68593ae0000ee0c7497a200012801529f8800016b6abc0cfc1a382984fd95c8884a6d4084a77c31b80000002b9a00003780000fda0000000501a60413c800000000000eb800000029687f0b13a00032e89ad03800
  | 44 => 0xab5ae34bfc000036d0d4e00000004d58000456101212b00006e580001aa266e76e179400000009f500007b7800000015845f200000000000acf26eca9329300a231820002ce6b7b0b9200011c45c923142860c641081aeaa3293e038bb152ab6a786380091e00000004cdb37c8ae2d6a65f873a0002dd20d82ac4a7f97cc00017f00000000ce90000b1980000000000000000052f0d000502c548e880003b089a8000000000000000001b8c000000015500000000000cbb80005d380000000000000000000020d6cf780005b51b160000000000291246d111e2e291327e880005cc000009e014487f0d060632c62000000000032ec000318810a1c5e5b60000000213e0000000000111c505a7c40c7200030d2d4881427680c50000c618000925a8100000000000035e0ee1ed429780002772d4621f3004a8d06a0000000000000002b2170e4eea0ee00000002f105e600022cabd7000000002b0000277600000000001f6a8c329ea261ae1a1ac8000c50800084b26de0000000c7200000000f6c54d2f8cb682e9800032469c409b671a1b54be71cfabf78dca00004d20000f3609425e060c800038c80005f525689b8089e22500004240cf63f30000000094400000000000000000084a0000000000203061f1bcc0000f028f9877acc38000166328000000000000000000000083a800000000000000000000126aae91f6833d25dc4c70f64987a11aa490f3a72133340001c4cb208502b4980004b900001ec800015c00000001c8200000000002a98000182e0000000000124c00000000000000000000039e800000000007a50fd464e0b6470980000000f7c00000005f5800000000001689ea234724a68701d1445c31562af8000000151452c000000032966931c28588335eb7f81f69cc062e2a61bf02e722e81b18ae4000321000032440002aa8cdd20a400024623572d660000d2e0000df20000302a37800000006be00009d400000005d9906037b27a2a8aa6ca0002e3a0002e2a00000003c52a08c8280004c0802214d800068a00000001af80001b9ca5f14b41de00000000a4e266af22782000054400009b409d685b8b5c0319be21a417d8451aef8a2a0eea00000006560000bb1260292b94c68db98d6bd6aa169c705b206591063a3800014c91f2790b0f800000000000000c368ad40001dae00014346a1800090c800000000001568d54553a4fc000000000000002ec000024580000000000b178000000000000020da00026000001a4000000003cf208a743a4741cd000055c958200000c245fa58e00000000001e90b2e80000f01da400000001721728be2800096da2ba080a890924882a16e80000000000374877e0000000aae8374744169006a06066d0068669c0eb086f8d605db31e69679616983041c46a80000000000c8b0000a250
  | 45 => 0x13c20002e4800013b400000009beb03a5aa04ba00031225d7800051a800030300000000000000141a7e90000ca21dee00016e00001a986a32f0492328f26148000000000000000000001f5c99700000000000000000060d800088900000000bf82ff1bc8c1d80000000000a5e80009c080000000d2800019b49699bda6db160cbe88490660a8c8000116a0000000000000083e31d6b7900000000000b4d2d2431980000001baa00028d05a9000029b1bd82209ec80001e50663800000031280000000c2b10647d4abd8afe80009a5800094a01ce76629100000d48bac81b4000000000000000000000cdf80000000a20590a9f609717ae48b041278b33f655d331e0f900004a2232e00007b427eabaac65143ac902ad0000000000000002eb000030a21564d2270054b00000e800001f3000000007745400000c76b22434910743a60d689aaa11e86506f87d987fc3721bac35604923a81ad465eb0a0662946242b96fc08e85ae84e8d980000d66c968214000000003d192cc5209d20002f780001d4ec18123a0002c18005864a015000079c000000000003239716b4582ee00000000001c1ca2e84a000027dc00007d42ca1a840000000bc480000001d9e7b900008a6000017b14f80000000b1a95d000031bcc7eada4000166200000002feb14648a00008508000659800000000000001b5c000305600005560000dba22880002268000000192600000000000000000000000026a2351000000014267cf801200000000000000000000000016ce96d2630cbe0000000000000021f200000009f60adc00024f2c70800057e233aa0880000001ae2593af3085d191c6c9000072e0000000000043f9cbaba1a1202c02088cee84ae62d0cb600012fa3ed11cc9050bca7d4000a65d0000000181c6e20000000084243588da000000021912645c30a42311878eb1300000001c723d7275e366a9046dd00000000d02a77000000008d4393979c0000000cb48276106831a71580009d005a60000832986a7baa2d000000000000000000bd20e62000033e0000e5c360000000012700002c9e05f80007ae2b6e084000083e8000747a380183aba800018f686b0000a5605c666b96086568d500000000ac8a7ae000057c0bd97b6992adcaaf3a88cc0c3198b6b80001890c6a00000005ce2b36000000047d0166000047400028aa00000000000000b48000000000ba0000000c5d00000000d18661af840002ad2000000000006fa00030967f3800000015ba7e195cec2a17a41c12f2e061a8267cea60667f1d94221a04c532800000005d40000000b09251ea3b970a7f8229ec5810ca00083f456301007190b986000764000203866d918065daff267911e479e88c4999226e60f2c460af00e8a8091783c410b40ffb17277d245866e90b658e227c5ba053e3248000
  | 46 => 0x54f8000336000081230d033aaaec000000000000000000c5000000000002c20cc3000074aab04000087205d0000a17972a0000000a2c800086a11e072aa9ce7ea1e86aa9a54205a88f4000000004708ee420a6d837524e657181e6000305c87f9dc8000000000000008a50000af4afda4ad9de6bbd2df693694c2cc60bee15913a648ca5c28489bbc000000067f8828b63b1343d0a9b8bf4836e40092e6be6acb2b3e2e4e0000be60758a8e6c18000000253652119787420e700000000cc5a7ee6262a32b8f2a280000000b5700000000000426a25a750b3a2000135200001ca000186897b0000000000000000a0000119a7be0ffca662ba69d180001e00000ce225d4391aa187cd800006b1bae00000000000000000000098887de85280004f30000b7a32b61770c1a3c19770000010a3331c1e3ae060a65c0ebc456800000000003841d5200000002ecb3300001c96142327800025d002118ca1f2800071e000024e000072a1a9600015a40000840cd306fcb4f2f100a0000000011f66c8283acd40000757b3424b5ac5000000002e100004f3aee88d523aa1f60f9a0000a942ac101e7f691d22850ee62cd8216692a95211ab116000123e6270000000000064083389c880003518eaa299800015b20e462c0ce04720456000000000020b81e12292a8bac6ccff87ea00010ac2a180001fe0000cf880000002ef0000000000000000700ea401b000000000009db163e0000000000000015700000ff000060200000001a6a6d880002549bfccf0000000000006a08000a0a8fa697f00e2ac2b392000046800000000000000810951e2de068c5b98000000000049393dc76280001e800001c2800000004c400000007e4a13422e0000a3c21c20781a7e000000085a8000000165c0002d680001c9a0000000000000000009f6000000000000000002d3a00030206f5000000010ecbc20000000245070d9eb44ae00000003114a26971ec310000c52837e000000000002ce5c82f66caa1b147c415dc0000000a419d3e0000000b0f1e20165287a19c0b2e559243e27b1db200033726e81b0cb122eb400009ea00000000002a6800010a400018a4c429410875000000000000f880d40000000026922000000003f48a969f8800000020b200000000002b24c39873012780000000000000000062480000001ec6000086246a0000ab9000000000005ee85e839f954845b0000000000000024d891180000001b8e0000000000000000027fcab88f94423b3280cd1a30144830c38a18ec22900000000010550307c73e00000000efccec8fd800027608089dc641609824030de2190019a7d88000b968bf218522ac16d80006e48ba409883e000006341bd0000721800066f24f096a8000000054e0000000aa0330aae6184802202600001afcb309d3c0001568505
  | 47 => 0x88000cf680005a7000000025f60f72cea000000000000003e58000c7e07968fda9e69128b5e53aaf06be0a6ee3af8f28cea066c9208900bf282e8a432724ad99c0a08bb2fcbb3b1265ffb2cca0090442c9800000000000000000c5da2ceaa3800000009cc00002a800000000000000000278800000009d4000096f800000000000000000bec32220001e5c0001e9eb1c25824c9016e3c31c929468dae903abfe91092c8862249eb23276e00000000001daa5a89e320000000346a942a0a1b428e9107200000000e8b01e8d893da00000006fc992a83da04e73d035a8d48f76cda8ada8d28000bee8000716800000a058014e0e4200013e6000000097630006189ee29af0e0684a2552585298c55b853074b155254924245f6ab94796a42e2370af663e1f0405db3782020a002b49a784fd200aafaa31c14024d400020f0000311200000004ce80000001d06000209a0eb000099104a60001a7200003660002e741669f1e95b902c6ed945200000008a880003038000bd580000000bf0bff9c6a9a498c22fdaacc2699ef40000000634acd60001c623620000933093a00018fa73696fe00000006fda73800018440000aa60000000000000000011667f6027aa5aa2263441826ce98194c0a043c1881c7c074af6c8ed8000000000095c800000000009ed800064216100000000c85004a0001dce18f879e436821e12d00000000000854188875c86e6000000086d19e81f88c5800030cc17784a474c8000000000008a08543809714000081cbe600000000000b9480000da83720000000000339600017d20002416b54a6600000c5e9768a020ada0727110b541758b8810e2dda558073ca0e000000000000001ac8a578000000222c0001d8400001920000cc09040000cefb180000085c0000d760000000032800000023b856b800000000008f400003398000ac400001f180000000942ad5888063f8000bc31e04442aaf2000000000006040000000000229a2b58000000000005c0000b9c2f2c8c12d1c00028d800000007ec96d2b020000b100000000000053c800000032d4000000072f98d8000000036b2078000000000000000000000aec9dfa0001b32000095600012a2a7c12ac0000000b0781bc68f942400000000a78e9c00000002621a440c78000000000000000000000000b7bb154afc2e723f3800033200000000000000138e000000000008fc5930000675000000000000002d50be4800000033102f881e20000000000000099b30de671245a0002646bf400b42ae091c188a3a8acaad5eae00a0e498800067002480ae8000304800000033f2000152ab170000974a95c8c580001cf80008f921440002e760000000aa4800017b825a0691f98300180e4612db4897a6d63639692c5c19be67712da0001a12ca999421191a8858a0000000000
  | 48 => 0x7d300260000f4031220dc03f0000000000050e1ae4440056a7ca88c812582e210fb3ae00005046c400007dc179ead800bc383800009faed80000000aec00c40000000000256a700b29200000000001432978adb6a991f74b0124f6276225000026f6000000022b0000686a68647a9efa0000000bd88000414833c89e00001940d7e44f17988869e060000ef6a04ab3ab450b9e5d900001580000aeea16800018cc00015040001a4e00007f0453800000006feb611d3800000003cc057ac3080005e226386b5811e4c52a729558960c1101342231c3e2acb2c230080005200000c6a0000c4d9c8808b12ba8dd1dbe4261016c2b929c71009a209500009bf10dc37aa036b048000bd4ab3e0078000801000000000006ed00000001c386e8983a63d31e06160b9a7370000aa08000a518da066c0000000000034f0444bb90000a34800000019ca7f90cbc00001126b4266229e996c63f0000a689f480000cda00000008311c0800027940000de05a00000cda00000000e3600029e0000121459e92586f08000000000000033f043c0000000000000018dc00000005168000000032e000000000000002e5000074d224e96c0000000000000015e600000007789a76c898000000146800000002a48264aaf80000000000000049a0000000c5a80001b0a9d03bb800000000000000000bf18a2c00018de200ac26b849856967000030e8000000000000000000001dd00890000000000040a978e00000009e100d800008c05a780000002dc45aba3265d195aaa4f0a3045f301a0001b8400000006d80000000226aba2800012f0000000000000027362ba80007fb8fe8a1197b40001f840001b9842700000000e2a0d8800000013b0be8000084d800092682fc7a48c8845730ee75da1085bd32680003050add2b440000c9600000000d623e2b2214606bdae461d527b453692d20000f4a8500ba800015769e70f985ce9ab45fe1e16b25ae6c60b0e5600017a097c00009fe8208a551a5ecc9800022a33e600032c00b48b86205151a000271200008a0215906659b8000000210037a28846dc14aa38d1546b250000cb8a1100002efcb34946ea33a0f20d20a7c2491890cd20000b6f000052432b24e32ab0000000019cad720000000000000000009ae815892abf500000000000bf810fa3d993f2000067a00000000001828591a48800032749618582ba82e6e000000078e80008b880007298000545800015d15ec00000960000000000000084900000000b6c00031fc0001cc0000129000022be000000065180002de800000013ea2a800001362d328361654244ab5c638ac4e00000006300f3e00000000002b5a0001ac2c53800074d942800000007eb981a7ac80000000000544a16600005220dc00dc24b8ed400007a80000ef20000000cb4000058
  | 49 => 0xb380000cb231a54ea2f25cb8afca300dccb6191f89ac000e20d17bec7da54469b0b7291e1ab078ba22e29f9cf27a90f6e5170000b4e2820257aafe2d980000001a14000000000000009f9a99ec93847c1731176cde9cf00000f0e00027bc1ef9c140002a2640410de2d20000a9e00000000000a61000026e06cc9dc000000000002abb132512000047b00007019ecc0001f64ba70d940c800000002eaa10380000000000a5e328401400002032b0600006f000000007c015f4000000000000000000f8c3f100000000000714095a000000008880000001f58a4233ce8bf800000000002ad90868e61ac069a31b4000218a24f207c2c600000c90292827266a4a180007330000910199600000000000000af4000000011644a7a676000000039a096e0003344000000000005203fe1b5800003bab860132cd6971a000160456b00004588000000000000001da000000000000000f3000000000000000000282800087d91ee00d039ac32800000014e6000228400f8000000000040e9fac1728dda0001d88ac8000000000008f70000b678a88b0fb0c800023400b105f000000003b2af8000033e8000000015b8000000000000000009b900005fa000061d9c947bb850a7c52f9e000118e0000000000263e3c121b6b9a80003e028b6a4700007352610489a8a42be8e306768e584b1188a3c680000001c4e90a8ddc116a19ca3e0cf2bfdb16c0000000000058a06e1558000329010d01560002840b48800000000000000000b4a012e7ee80000000b08c4418128242fae0be030ab5fa5e41d9a668914943c31385066341e7e7270eec255005a062094c28a276a2d099ce020814818a166895800008341f4000010221a100000001d405878bae00000001c0b31200000000000000000000031ca0a61e900002d4084ccf511880d7000036a0a1e47429f806380000002c44b20023c20021f04f60000000000000000000002c02000000000000000000000000216024d8000000292c96880005f1b2b867bb1d4c151c3085f80000000000000000000000005db81c24fc1e2a000000044f80000000c869f826324feb27a384890c00003e61968cd645d01f049c9b52c568ae60002d4c0000000c63000000000003fe80b06f9900655f0000355896625603c62028a22c5a3158000000013309aa8be80000000000b631a5c43116d600004941af2e4c00000004c78804cad0000000000000024de0a1230042e09f860c2394c9d9a500000000000015091f882c15306c03e42f889fd80003d7844200033d0b370000aaa81dc00021a6bb8a9aa94b000091ca25c0000000081800000015b23a78000bca00002f52d76000000010aa5fa0001ebe86900000002a5a941800000022b200000004dd8cfe94f0bcc6f2a2346580000b620000000041e9f0a67a0000000a2180
  | 50 => 0x91a00005ce0ef045c5a980000a3acfc293014ec160000409a412485a51837f00004c58000a7f000000009bc00009e6b3300ec61b00005910da681b0000a2f2e584289da20002ab48f82a6ac0aa1468c0ad066e6ad1e8748c1030100a2357acfe671b10c00005e46012a127bf22586bd000013b0000b340000672140e0001db65321578000252acce961ab3231fe000000000000000001230a1c86ac00020c80002f8600000000000000170b00e733a73c1948498069b2201979b1a3b3232000028fa11180004809d9c2329418b3d1fc6bc627cc0b302a299022a6c9980003d30000159800000b0000a8380008e330e20000244298ad1200007b6bfa8000a588658563ad940000000000031877800000e0b39025f0000a4800001ca01e8000134400000000000000000290a6cfa1dc98ea58a9b098608f006d8c942a425cd1ee80001c1249b13460000000000226800000002ab2eea00012e8000208065480000b189f400000003b6800067e1a2a62b12fc49fb0f41052ae82c7993e0f0b1b030f044e314928cca1ad8087e80004f40000675997c332a19638f1b56b05a388b442cee5b1000000010a0000091a00000000e70000bf6121059f0df8cd580000001dd2322afb81338000000000060f8000000000000000007fd000056f00000000000c97800000020c600020540000000000260800033c4ab00000bcf800000000000000000a81000019f00009998000000000000008ea000000009380000000fdc0000006acb26560002fb2af08018c6932a006baaceabea28cb500562a47908800c11389ad8c082068d38000000043b80006178000a52328c73400000000000000320e04e2c680001cd29500e500000000000000000020e00001c4a61180004d0800051b04a2a3f00005619c3c2212da600003b49578c1c9c20000ab2000054e00009ab125a0001b805c89bdea8f858e77a15e00002f9600000003821fd459d814200500002ed0000000090acf180000000000000000052b181400004da02705d80001624000185000000007ab059e6730aaa3080000000000000000000001f6000000007e080000000000000000000000005a20e6a00000000b9861200000000000ec600000004798f20bfea9c40000000c1d2bf4ad30000c9201680000000260209e0002b52795ae0e00017540000184796000020800001438cae8b30000000000041e1d4a43480007ed800035b0000ca90a9a9baa634333925c7c685be19a9ad251e000000000004c880003eb8000ca0aecc1f00000c4bb088000000000000006578b700ef8668944000000000003dc80003e0aeca0899300c1e8000c95a0ec000000097a008c00000001f400000000000c0c81547b099723c98000743000000000004948000bb1a17a96e981e5b0011621faa2c92124be3f78000a39817c7
  | 51 => 0x337800023c2466000030600003b02bc1beab66000000020aa2090000cb20000baa227e6f41a6684ca8705161abe02b80000000000cb62b282da27281f9800000000000000000000000043900000000000000000000000000002f1cb5d162c0002ade4772a9454600004a69768c792cf20001ce400000005dfade28e78572cb68548431ab3227280000000000758912e03fa8344cd1a2620f99d80002c3088eb39454898420000000a4d022001da68a71f80005390000a6b9f44039800011d8000000000000020d49df8f1c7f2b09e538804c411a70a0000000000247c0002f7e9ff80006808000b3b0dc291a8cc40001e4025700000000b1a2db88108cd800000000000002a5887a8000840800000000006ae8000b052f7c000126024507ce000000000000000000000000000000000004b080000000f741a498348bb9234a8700001dbb16400030183c01f2429d800011794ce82c0000000000088792c0b7080002cc8af440f000007b000031e8000000003807eaadcbda000035e94a0cc50000cb985768c2000000000005a69396c0bae64000000000006a40000000ba9a33417693c86f4a5aeba2319c00010802ca811aa6014920b006740b8196826c043a5e0a0ba16f32ba19707ae519a98a4d3076a5589b6a00030ba98a9fbc0b60d2000002d0367875c00015a800000007802cf635ca3fe000327c508b3800722ca22d5b1ee6251d464aa30389aa1b6813f914c034869a000112200000002d6a1640001f7e00013a2b6433aa958ab8aa621be8c9621d06d69636b281ff29d21e9cc4b0000328000055331aa3700ae00001dc049780007290000526b3580000000356af648c3b3b8816273293f9bc018699fa0002c5a3e3a636448233200015201f0874eb66886c383157095600000003006000312a00000009e68930876a13c139a1e43ba06aa72b2d1811b80000000e94189800000010b000000000002b7a8fa0000b4319568f62a4034f800011600003d18000b2b14700000000bf080000000000009000000024ec06023820000b400001fdc00020b44412bb6c1a97e415e000086c800032c08ec0001cb600008bc00033989080000b8c000000000000000000a4387da00000000002cbc000194c00020ca0000cc2000000000000000000b3ac36000000000000001b640002df0000012a000000049582f000001f4000000000008c230b1afa4a480000001b2e1d00000770800000000000001932470000000000000000000d0080000001ae68e196be3b59b7a1dc9224c200290c72800007ba868966800000000005748a2a0002a44000000004621b8a801e800278c6057d96cc0003012000000075c00000002762000184ca0c9d90c8a295660624b436f0000acd00000000000c4100003420fbe4f10000cfd2fd60000000402a92e0831
  | 52 => 0x69ea2ae9309640a98800039f069c5fd80005a810f80000000000139242f332c11fac38024982abb52cc49fc0544a85218e000000000000000000000a1d0000000000000022c00000000000000000006ba3b8800008a800036e25f40002b1cbae88460002814000248003300008d91e3e00000000000000000000000011ce00000000000000c3e8000bbf8860241936625ca4f48e59a3600007265e180003ee800050b040058600045289320bf014420bd227a4f28000b2d047a7ff2ed20000a4859a800000011d8b388000b9700000000000000014a6218c4caf1176020486b696b1648727ab8c47f9e60c688000000000000000000001ca062829ee00028d48b68552b46acfaaeba112add94cc00031a0000058441eabda00000000fe000000000004aa98107df10aaa1a80000000000541a5ee54c00002f180004f01ddab558000a258000000000051f00004ca0a0600016eac7311fa8b58c9cb98267c81a22803b6321c17422a88d723840bb0ae8ca79dba3110000a5c8000026000059d31f096521e6000000027a00003ccacce0000e484c49a18cbfa03a00018821640000b4d8000c8480669bc96720001f5697f89a49b99390268010e00000008f2aa4e00000000000836000173e00000008168000bb9800000004a8a58319600000000000000afa1ba6ab1904c566254e8bd1d0298a11163870bd8d00280ac8a8000b8303aa23987c89e81f9e6b11a5a6e9296e000223c000000000000003411f184c1aa7cb828e26000000063a2248000000062d80000000000364a848b38000024cb016c392dc60000000cdb10c82d61496192000037113e8894b11ab90a51664ba5ca1120db2890800057f000050280006a2abdec3727ac0000c1800000000000fe63612fbc00018ceab509225c980000000000000087809780005ff00002529e140000000000000000010a8000000068e80000000000000000000000000000ff0c7b31ac0002152024007eafb8610ca70a3a0001aae4ffa2161e72fce3b3a19835300006bfae5017f80004db80000f280000ab84c85d41b12a20000800000000001aac839a07a0b5999009d2116ced3034000071c000000000000000001b504092eec50b9ce8a1f9450af28f225a12b628cf87140001eca7570000784a1ee30932f6a000d4a114a404631008e000000030780005498dde1bbac8421a199a0002a3ac28a1862a28000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x847676d4910042b2baca48802199d965244010ccecaa9220087627054910043b0382a4880219954b6044010ec2a5a0220087615290110043b0a928088021d85484044010ec2a59822008761528c110043b0a926088021d85483044010ae2eb902200876152c8110043b0a944088021d85492044010ae2ea102200876152081100423d3b6a4880215a5d65244010cd6cb292200866b6554910043b138aa488021d81c55244010cd2a5b0a200876152d85100423d3b4a288021d854a5144010ec2a5a0a20087615290510043b0a928288021d85484144010ec2a598a2008761528c510043b0a926288021d85483144010ae2eb90a200876152c8510043b0a944288021d85492144010ae2ea10a2008761520851004338baeca880215c9db6544010ce4edb2a200857172d9510042b8bacc8880215cdd56444010ba6e6b2220085d07359110042f1b92c888021781c96444010d62c832220084f276d5110042f1396a888021785cb54440109e4ec2a220085d27315110042e8b98a888021789c85444010bc2e42a220085717598d10042b9baac6880216cdd16344010b60e8b1a20085e37258d10042f0392c688021b458c63440109e4eda9a20085e272d4d10042f0b96a6880213c9d85344010b64e829a20085b17414d10042f1390a688021785c853440109e6eca1a20084f07650d10042b9baa86880215c1d54344010bc6e4a1a20085e07250d10042b93a886880215c5d44344010f228621a20085717598910042b9baac4880216cdd16244010b60e8b1220085d37358910042e839ac488021b858862440109e4eda92200857276d4910043393b6a4880215c5d65244010bc2eb2922008561759491004371b2ca488021d8d965244010ae4eca9220085707654910043b1b92a488021d8d895244010ec0c4a922008763755491004371b2aa488021d8d955244010ec6a8a9220087625454910043b0aa2a488021d81515244010ec6a6a9220087625354910043b0a9aa488021d814d5244010ec6eca9220087627654910043b0bb2a488021d81d95244010ec6e8a9220087627454910043b0ba2a488021d81d15244010ec6c8a9220087626454910043b0b22a488021d81915244010ec6e6a9220087627354910043b0b9aa488021d81cd5244010ec6c6a9220087626354910043b0b1aa488021d818d5244010ec686a9220087624354910043b0a1aa488021d810d52440109e4ec29220085727514910042f1390a488021d85485244010ec2a5a1220085727590910042b8bac8488021d854a42440109e6eca1220084f07650910043b0a9284880215c9d44244010ae2ea21220087615210910043b0a9664880215c9d63244010ae2eb1922008761528c91004279bb264880213c1d93244010ec2a49922008572750c910042b8ba86488021d85483244010
  | 1 => 0x430423b38ccaa18211e9c26550c108dee4b2a860846c72595430423bb8acaa18211edc16550c108dce432a860846d72195430428e39aa8a1821471d15350c108daebb12860846d75189430423aba8c2a18218d9506150c10caca630a86084f170185430423cba8c0a18218e9506050c10cb4a630286084f1711814304237394ca218211b5ca6510c108dce4328860846d72194430423b388ca218211e9c06510c10c3ecaa18860861d6550c43042a7398a929021535cc5494810a5ce829ca40852d7414e5204316b20c9290219358c63948108deeca1ca40846c7650e52042b3b8a8729021591c54394810ad6e0a1ca4085687050e5204386a1887290211b9db54548108dcec2a2a40854e7315152042a6b98a8a90211b9db53548108dcec29aa40852e7414d5204296ba0a6a902153dcd6454810a98e6b22a4085647159152042b4382c8a90218b5906454810a5ee8b1aa40852c7458d52042b238ac6a90215a1c16354810c9ac631aa40846f7650d52042363b286a902159dc54354810ac8e2a1aa40856b7050d52042b438286a9021c350c43548108deeca90a40845e73197420422eb98cba10211d9c465908108f4e032c840845f73595420422e39acaa10214b1d15250810ccaa5b0a8408475751854204332a90c2a10213c5c06150810cd2a5b028408479751814204334a90c0a10213c5c460508108bce6328840845d73194420423b388ca210211e9c06510810a5ae9290840843e74197320421eba0cb990211d9c4658c8108f4e032c640843f74595320421e3a2ca99021531cd524c810ccaa5b0a6408475751853204332a90c2990213c5c0614c810cd2a5b026408479751813204334a90c0990213c5c4604c81087ce8328640843d74194320423b388ca190211e9c0650c810a9ae72906408669529824104334a92c120821c99494110410cd2a53008208669525804104334a94c1188219a549608c410e8ca49886208669529803104334a92c0188219a54a60884108f6eab04420866952582210423cb82ca10821595c55208410cceca9084208665654842104334a94c0108219a9496008410cd2a4b0042086e1215802104332a94c3200219954961900108dce5328800846d72994400422f398ca20021175cc65100108dce4328800846d721944004332a94c220021995496110010e54a4a008008665529863004332a92c3180211b9ca650c0108dae5328600843e74194300421eba0ca180211b9c8650c0108dae43286008665529843004332a92c218021d2949300c010ccaa530c4008477755862004332a92c3100211d5c56508010ad2e0a904008665529842004333292c210021995496108010cd6ca9004008669654802004370b0a40100211d5db52c40108eaed28c200847976d4a1004334b2ca5080219a59552840108f2ed28c20
  | 2 => 0xc021a218e1516010d10cb0a6b0086884f071580434430fb26c6a9221871936354910c3ec831aa48861c6418d5244316326c4a92219318f6254910c68c9b0aa48865463d85524431c326c0a92219618f60549108deeca90a48852c7454852442a639aa4292219c58560149108bce7b2e848845d73d97424422f39ecb21221175cf65909108e8eab0c84884f070586424423c3aac1212213c1c560909108bee6b2a848845c73595424423bb8acaa12211edc165509108bee6b28848845c73594424422f398ca21221175cc65109108e8eab088488634545844244332292c2212213c1c161109108f0eab008488638545804244334292c0212213c1c5601091087ce9b2e648843d74d97324421f3a6cb192210f5d3658c9108e8eab0c64884f070586324423c3aac1192213c1c5608c91087ee8b2a648843c74595324423bb8aca992211edc1654c91087ee8b28648843c74594324421f3a0ca192210f5d0650c9108e8eab086488654535843244332292c2192213c1c1610c9108f0eab006488658535803244334292c0192213c1c5600c910c70a8b068288658535833144334292c190a215c9d46088510accebb12428856672949214423b3b0a490a21599d85248510cccec29242887617014921442793a8c090a219c9d46048510c68a8b0e808845f73595404422e39acaa02211bdc965501108d8e4b2a808865453587304421fba2ca982210f1d1654c1108dee4b2a608846c725953044332292c390221591d521c8110bc0e090e40885727518620442b83aa4310221d8149218811087ee8b2a408843c74595204422fb9aca90221171cd6548110ac8ea90a40886646548520442b53aec4902215a9ca52481108f4ec292408856a7614920443353b0a490221d85c452481109e4ea30a408867275185204433432e4290221b81872148110ce0cb10a40885e17288520443b029442902215a1d52148110cd0ca90a408857075485204433832a4290221d81d52148110ac0ea90a408876365485204437032a4290221d81952148110cc0ca90a40886e1614802044370b144388221b8d8921c4110dc2c510420886e3624821044332b14c3aa0219a58a60d50108dee4b1ca80846c7258e540421fbb2a82a021875516315010c3cc8b18a80864e639885404326b1cc42a0219398d6215010c9ac6b10a808655639845404332b14c22a0219658e6015010cd2c5300a808665629875304334b14c1a98211bdc96494c108d8e4b24a60845f7654c530430eb22a629821875926314c10c5cc9310a60862d649885304317322c4298218b5916214c10c6ac9308a60866562984530431cb24c0298219a58a6014c108dce532e860846d729974304237390cba18211b5c865d0c108dce532c860846d729964304237390cb218211b5c86590c108dce532a860846d72995
  | 3 => 0x8d5148020ec4c6a8a40107616354520083b031aa290041d8d0d5148020ec486a8a40107614354520083b021aa2900413a9d85148020bc4e228a40107615114520083b0a8e82900415a9d64148020ad2eb20a4010761519052008275bb282900413a1d94148020ec2a2a0a401056a7510520082b4ba88290041d85444148020ec2a398a401056a758c520082b4bac6290041d854631480209d6ec98a40104e8764c520083b0a8a62900415a9d43148020ad2ea18a4010761510c5200833930ac1aa6210fdd95415310ce4c2b00a9886726158353c422fbb2a629e219c9856014f108dce532a878846d7299543c4237b92caa1e211b1c96550f108dce4328878846d7219443c433930ac1a96211bdd95214b10ce4c2b00a58845e7399542c422eb9ccaa1621179cc6510b108bae6328858843e7499532c421eba4ca996210f9d0650cb1087ae8328658846e7614921c42f0b86a490e211d9d852487109ccec29243885667614921c43333b0a490e21d85c052487108deeca90438866a5258021c4334a92c010e21b84856008710c6aa830a81886555318530c4332a90c290621781c12148310dc2c2900418867161983548421fbb2a82a4219c5866015210ce2c3306a70845f7654c5384338b0cc029c211b9ca6550e108dae532a870846f725954384236392caa1c211b9c86510e108dae43288708671619835284237bb2a4294219c5866014a108bce732a850845d73995428422f398ca21421175cc6510a1087ce932a650843d74995328421f3a0ca194210f5d0650ca10c72a83028308659531813184334a90c090c21b848560086108dcec29241085e171d49208423d3b0a4904213a9d85248210ad4ec292410866a7614920843b0b88a490421b818521482108deeca904108666525842084332a92c210421b85852008210c3ec831aa88864f63d89544432631ec4aa2218bd906255110c9ec6312a88864c63189544432a31ec2aa2219918b6155110cb0c7b02a88866862d81544421fbb2a82a221471cd5415110a58e4aa0a88846f7258c5444236392c62a221871936354d10c5ec9b12a68862c64d895344317b20c4a9a218b1906254d10c9ec6312a68863464d855344332316c2a9a218e1936054d10cd0c5b02a68845f7654c534428e3a2a629a21531c95314d108dee4b20a68846c725905344237396cba1a211b5cb65d0d108dce5b2c868846d72d964344237394caa1a211b5ca6550d108dee4b2a868846c72595434423bb8acaa1a211edc16550d108e8e232a868847870195434423b3aec2a1a213c9c36150d108f4ebb0286884f271d814344237b92ca21a211b1c96510d108dce4328868846d72194434428eb98a821a21475d05310d10a3ceaa18868851c7550c434423a3aac221a218d1516110d10ca8a6b0886884f070584434423c3aa
  | 4 => 0xcee4a1aa2105647250d51082b9b8286a88415c1c14354420e2a8621aa2105727090951082b8b8484a88415c9c04254420ae2e0212a210572708c951082b8b8464a88415c9c03254420ae2e0192a21047776544510822fb9acaa0841171cd65504209d2e03128210534745454108333b12a2a0841991895150420ce2a3b0282104e9721814108338a88c0a08414d5d2511042087ee8b2a621043c745953108274b80c498841551cd514c420ccec4a8a6210664625453108338a8ec0988413a5c8604c420ce2a23026210555739443108338a8ac1908419c5466008420ce4a2b0042106e1215802108333312a3200419958951900208bce6328801045d731944008333312a220041995895110020e64a2a008010666625463008332b12a3180410f9d0650c02087ae83286010666625443008332b12a218041d4945300c0208daed29440104797694a2008333b2ca29004199d955148020ec4e0a8a40107607054520083b0a8e8090041d85464048020ec2a2a0240107615110120083b0a8e6090041d85463048020ec2a29824010761510c12008339b2ca2900419cd955148020ec4a4a8a40107627254520083b1b12a290041d8d095148020ec484a8a40107614254520083b0212a290041d8cc95148020ec464a8a40107613254520083b0192a290041d85472148020ad2eb10a40107615188520083b0a8842900419a5d76548020cd4edb2a401056971d9520082b4bacc8900415add56448020b96e6b2240105c87359120082f1b8ac890041781c56448020d52c832240104ea76d5120082f138ea890041785c754480209d4ec2a240105ca7315120082e4b98a890041789c45448020bc2e22a240105697598d20082b5baac6900416add16348020b50e8b1a40105e37158d20082f038ac690041b258c63480209d4eda9a40105e271d4d20082f0b8ea6900413a9d85348020b54e829a40105a97414d20082f1388a690041785c453480209d6eca1a40104e87650d20082b5baa86900415a1d54348020bc6e2a1a40105e07150d20082b53a886900415a5d44348020f128621a40105697598520082b5baac2900416add16148020b50e8b0a40105cb7358520082e439ac290041b858461480209d4eda8a40105e1759452008371b2ca290041d8d965148020ad4eca8a40105687654520083b1b0aa290041d81855148020ec6eaa8a40106e36554520083b1b2aa290041d8d515148020ec4a8a8a40107615454520083b02a2a290041d8d4d5148020ec4a6a8a40107615354520083b029aa290041d8dd95148020ec4eca8a40107617654520083b03b2a290041d8dd15148020ec4e8a8a40107617454520083b03a2a290041d8d915148020ec4c8a8a40107616454520083b0322a290041d8dcd5148020ec4e6a8a40107617354520083b039aa290041d8d
  | 5 => 0x47b705954348236390caa1a411b9d76250d209d4e1b12869047a75d814348275396c0a1a411ddc56510d208e8e2b28869047671194434823ab88ca21a41475cc5410d20a3ae8298869051e7550c434828e3aa8621a411b1d56210d20c58a8b10869064c535884348274382c421a411e1d56010d20c70a8b008690658535804348274392c021a418e15160d0920cb0a6b06649047776544514829a3a2a228a41551cd51145209d0e0b1482904e872582414822fb9aca20a41171cd65105208bce6328829045d7319441483162a2c420a413a1c16210520ccac42888290638545804148274392c020a419c14560105209d0e0b1462904e872582314821fba2ca18a410f1d1650c52087ce8328629043d74194314832629ac418a413a1c1620c520ccac42886290658535803148274392c018a419c145600c520ad4ea306429056675d8521482b33b0a290a41999d85148520ec2e028a42904ea7518121483353a8c090a418b15162d01208bee6b2a809045c73595404832629ac5982410fdd1654c120878e8b2a60906e161c872048333312c3aa0419c58660d50208eee2b1ca8104747158e540821fbb2a82a041875516315020c3cc8b18a81064d63988540832b31cc22a0419558e6115020cacc6b08a810655635845408333312c22a0419658e6015020ce2c3300a810666625875308338b0cc1a98411ddc56494c208e8e2b24a61045f7654c530830eb22a629841875926314c20c5ac9310a61063664984530831ab24c2298418d9916114c20c6ac8b08a61066662584530831cb24c0298419c5866014c208ece332e861047571997430823b388cba18411d5c465d0c208ece332c861047571996430823b388cb218411d5c46590c208dce532a861047671995430823ab8ccaa18411e9c26550c208dee4b2a861047771595430823a38acaa18411d9c46550c208eae232a861051c73551430828e3a2a6a18411b5d46250c20c5ca8312861064e531894308274b80c4a18411d5d76150c208eaea30a861047975181430831d2a0c0a18419694c6050c209d2e4302861047671994430823ab8cca218411b9c86510c208ece2328861047571194430823d380ca2184187d954310c20c3acaa1886105567315251082aab98a9288414d9d05394420a6ae829ca21063564192510832ab18c7288411ddd943944208e8eca1ca2105677250e51082b239287288415cdc14394420ae0e0a1ca2107154310e5108392a108528841d14c832944208ecedaa2a2104767615151082ab398a8a8841555cc54544208eceda9aa2104767614d510829b3a0a6a88414d5d05354420aaee6b22a2105547359151082b2392c8a88415c1c16454420c6ac8322a2105377458d510829a3a2c6a8841591c96354420ae0e0b1aa2106556318d510823bbb286a88411d1d94354420a
  | 6 => 0x24c326b18a4212619a14960109308eeeca88a29853474544514c2b2392a228a611bdc965105308d8e4b28829846e72194414c236b90ca20a61871516310530caac6288829867051580414c21fba2ca10a610f1d16508530acae2290429856572144214c2b33aa4210a61591d521085309b0e6b00429866b52580214c334292c010a619cd456008530ce0a2b0042986e121580214c30e2a2c7a02610fdd95415030c5aa8b10a81863554584540c317322c42a0619398d6215030cccc5308a81866562984540c31b322c22a0619598d6115030cccc4b08a81866562584540c334b14c02a0619c5866015030c72a9304861851d73550430c237bb2a4290618b5915214830ccaa4b08a4184d973982420c23bb8acaa10611d1c565508308ece232a841847571195420c30eaa0c6a10618e5506050830cd2a4302841847776544510c31ab22a2288619958951144309b2e7304821846f72595410c236392caa08611b9c865504308dae432a821861d5418d410c31caa0c0a08619c544605043087ee8b2a421843c74595210c21f3a0ca908610f5d06548430c98c6a92421856471549210c32a31aa290861591c95148430cd2a4302421867151181210c333b2a42108619959521084309b2e730042186e121580210c30eaa4c7200614e5d66410030a72eb2a0801847b76550400c29dbb2a8200618edd954100308f6eab1880184db7558c400c32dbaac620061175da538c0308f2ed29c60184da76901300c23cbacc898061361d9434c030d30c8a1a60185c87250d300c2e838a86980619a98960d532087eecaa0a99066a6258054c8335312c1a9e4117dd95314f20cd4c4b00a7904767199543c823ab8ccaa1e411ddc56550f208e8e2b2a87904767119443c823ab88ca21e411ddd95114720bc2e1a8a43904e67614521c8338a8ac010e41b84856008720c5aa8312819064d5318930c8334b14c1aa4410fdd95415220cd2c5300a91066962983538822fbb2a629c419a58a6014e208ece332a871047571995438823bb8acaa1c411d1c56550e208ece2328871047571194438831caa0c0a14419654c604ca208eeeca88a3106e121580218830fb20c6aa2419318f6255120caec7b0aa89065463d85544831bb20c2aa24195d8c6155120ca8c630aa89066762185544832c31ec0aa2419c187605512087eecaa0a89051c73550544829a38aa82a2411ddc563151208e8e2b18a89061c64d8d5348316326c4a9a418dd936154d20c68c9b0aa69063764185534831a320c2a9a4195d8c6154d20ccec430aa69063864d81534833830ec0a9a4117dd95314d20a38e8a98a6905547154c534823bb8ac829a411d1c56414d208ece3b2e869047571d97434823b38ecb21a411d5c76590d208ece332a8690475719954348237b92caa1a411ddc56550d208e8e2b2a869
  | 7 => 0x629c819694c6050e408deeca90a52066552584529023b38ccb994811d5c665cca40a9ae72906520477765445190332b12a228c811b9ca65cc6408dae532e63205557394431902b238aa490c81591c95148640cceca908432066565484219037090ac010c8117dd95314d40a98e4a98a6a05547154c5350327a98c4a1a819314c6250d40caea630a86a065453185435032c29ec0a1a811bdd95214940a98e6a90a4a056471548525023bb8aca192811d1c5650c9408ece232864a047571194325030eb20a6192818b590520c940cd0a4b0064a04777654451502aa39aa228a81591c951145408dee4b2862a046c725943150237390ca18a811b5c8650c540c3ac829862a063564144315033828ac018a8117dcd65085408b8e6b2842a05657114821502b2b90a210a81599d52108540ac8ea90842a04b8745802150335a92c010a819a1496008540ce6a2b0042a067051580215037090ac010a8117dd95314c40c9aa6b10a620655535845310237bb2a4290819358d5214840ccaa4b08a4204b974982321023bb8aca990811d1c5654c8408ece232a642047571195321030e322a6990819654c604c840cd2a4302642047776544511032ab1aa228881995895114440972e9304622046f725953110236392ca988811b9c8654c4408dae432a622061c6454d311032ca98c0988819c544604c4408bee6b2a422045c73595211022f398ca90881175cc6548440c58c8a92422056471549211031a322a290881591c95148440cd2a43024220671511812110333b2a4210881995952108440972e930042206e121580211021ebb4a9200811e5da5490040d30c6a1a80205a87250d40102d838a86a00810fdd95415330cb4c6b00a99863a5458043cc237bb2a4296611d9c76590b308eae3b2c85984777654451cc237396cb20e611b5cb6590730dc242b00439861d5418d40cc23cbb6a8206619998a61d5230ccac530ea91866662587548c332b12c3aa4619a98a60d5230cd2c5306a91867261983548c338b0cc1aa4610fdd95415230cb2c7300a91863a54181438c237bb2a429461995496114a308ece332e851847571997428c296ba4a4214611ddd95114630ccac4a88a31846e72997418c236b94cba0c614d5d25110630ac8e2a92431856472545218c333b2a4210c61995952108630dc242b00431861e5458c408c317b20c4aa26193d8c6255130ccec5b0aa89866462d85544c31bb20c2aa26195d8c6155130ccec430aa89866462185544c335b16c0aa2619a18b6055130ce6c3b02a89867061d81544c21fbb2a82a2614b1c95415130a68e2aa0a89862f54189434c3162a0c4a1a618dd506150d30c68a830a869863854d81434c237bb2a4292614b1d15214930ac8e2a90a49847771594424c23a38aca212611d9c465109308eae2328849861c5458c4
  | 8 => 0x56348421b4ee8b1a4210da47458d21086f1b82c690843781c16348421d8ac631a4210ce676d4d21086f1386a690843785c353484219ccec29a4210da67414d21086d2ba0a690843789c05348421bc2e029a4210ce77650d21086723b2869084359dd54348421ac8eaa1a4210de37050d21086f03828690843599d44348421acaea21a4210f854310d21086b2bacc09084359dd56048421b4ee8b024210da47458121086e3b9ac090843711cd6048421dc2c03024210ce77648750086ad398a928043565cc5494021a74e829ca010d397414e50086b5baa43280435cdd52194021bc6ea90ca010f6375486500871cb20c9280439658c63940218f6eca1ca010c787650e50086b5b9287280435a1c94394021ae6e2a1ca010d707150e500878ca188728043ca5084294021e9264194a010f314110650087a8988632804399dd92154021cc8ec90aa010f637048550087b038242a80431e9db54540218f4ec2a2a010d5a7315150086acb98a8a80431e9db53540218f4ec29aa010d3a7414d500869cba0a6a80435add52154021ae6ea90aa010de37548550087b1baa42a8043d8d952154021ec6a890aa010f625448550087b0aa242a8043d81512154021ec6a690aa010f625348550087b0a9a42a8043d814d2154021ab6e6b22a010d587359150086b4392c8a80435c1c56454021c72c8322a010d3b7458d500869c3a2c6a80435a1c96354021ae0e2b1aa010e596318d500863dbb286a80431e1d94354021ad6e4a1aa010d687250d50086b9b8a86a80435c1c54354021e328621aa010d727190950086b8b8c84a80435c9c44254021ae2e2212a010d72718c950086b8b8c64a80435c9c43254021ae2e2192a010d6a7290550086b4b9482a80435a9c84154021ad2e420aa010d6a728c550086b4b9462a80435a9c83154021ad2e418aa010f637148550087b130a42a8043d8d052154021ec48290aa010f614148550087b020a42a8043d8cc52154021ec46290aa010f613148550087b018a42a8043d8dc92154021ec4c490aa010f634248550087b121242a8043d85092154021ec08490aa010f633248550087b119242a8043d84c92154021ec06490aa010f637648550087b13b242a8043d85d92154021ec0ec90aa010f637448550087b13a242a8043d85d12154021ec0e890aa010f636448550087b132242a8043d85912154021ec0c890aa010f637348550087b139a42a8043d85cd2154021ec0e690aa010f636348550087b131a42a8043d858d2154021ec0c690aa010f634348550087b121a42a8043d850d2154021ec08690aa010f61210855008673bb24228043b848660140218f6eca80a010f6121540500862fbb2a629e811bdd95214b408ece3b2c65a047571d9632d023bbb2a228e811b9cb658c7408dae5b2c63a06e12158021d022fbb2a
  | 9 => 0x4e03288710c7970194438871aaa0c2a14439554c614ca218f6eca80a110e1f6418d544872631ec4aa2439518f6155121cb6c7b02a890e5863d81544871db20c0aa24396d8c6055121cb0c6302a890e6b621815448739b08c0aa2430fdd95415121a38e6aa0a890d3870550544863db82c62a2431e1c16315121c38c9b1aa690e2c64d89534871a326c2a9a438ed936054d21c70c9b02a690e3b64181534871c320c0a9a4396d8c6054d21cd6c4302a690e7361181534862fbb2a629a43471d15314d21ab0e0a98a690c7b70590534863c382c829a431e9c365d0d218f2e1b2e8690c7a70d96434863cb86cb21a431e9c26550d218f2e132a8690c6f72595434863bb8acaa1a431edc16550d218f0e0b2a8690c6e75d89434867338ec4a1a431d9d76150d219cce5b0a8690c7b70594434863c382ca21a431e9c06510d218f2e03288690d1d73150434868eba0a621a43479d54310d21a38eaa188690c6c7558843487162a2c421a439314d6210d219c8e2b108690c7475584434871a2a2c221a439514d6110d219c8e4b088690e3454587424872a29ac3992438b15162d05218bee6b2a8290c5c73595414872629ac598a430fdd1654c521878e8b2a6290c7b76540504869c3a2a028243561cd5014121cd4c4b06a810e7261583540863db82c72a0431e1c1639502187eecaa0a810e1d5458c540870f322c62a0439358e6215021caac7308a810e5a63980540872cb1cc02a0439698d6015021cb2c6b00a810e6a62580540873930ac02a0439a98960d4c21ce4c2b06a610c7b70592530863c382c92984317dd95314c21c3ac8a98a610e1d6498c5308716b24c4298438d5926114c21c74c9300a610e3964980530871d322c0298438e5916014c21cd4c4b00a610e7261580530863d384cba18431e5c265d0c218f4e032e8610c7970197430863d384cb218431e5c26590c218f4e032c8610c79701964308637394caa18431d9c66550c218f4e132a8610c7970995430863db82caa18431e1c16550c218f4e032a8610c7970195430868e39aa8a1843471d15350c218daea3128610e2e541894308727298c4a1843395c46250c218eaea30a8610e3654185430872b298c2a1843395c86150c218f2ebb028610c7975181430863d384ca218431e5c26510c218dce43288610c7671194430863d380ca218431e5c06510c21c3ecaa188610e1d6550c430862f398ca20843175cc651042187ce83286210c3d741943108636bb4a5108431d5da5288421ccaebb2a4210e6676d9521086b2b86ca90843595d66448421aceeab224210dc77359121086e239ac89084378dc16448421bc0e0b224210ea56419121086733b6a890843789c35448421bc2e1aa24210ce67615121086e3398a890843715cc5448421bc4e02a24210de17015121086b2bacc69084359dd
  | 10 => 0xc6f7654852506a639aa4292835a1c152149418f6e0b2864a0c7870594325063d380ca192831e5c0650c941c3ac829864a0e2d641483250732292c2192831edd95014141ab0e6a80a0a0d6872540505062fbb2a6298839354d6214c41cb2a6b00a620c6f765485210726b1aa4290839a549601484196ae930c6420c7b70595321063c382ca990831e9c0654c8418f2e032a6420e1c6454d321072aa98c29908399548614c84187aed2a48220c7576952411074a31a86a0883691c94350441b60e0a1a8220c7b76540501072cb1aa0280839a589501404187eecaa0a998e566358454cc71b2a2c221e631bdd95214b318f4e1b2c8598c7970d9642cc70eaa0c6a0e631d5db54107318f6eca80a198e6662987548c732b14c3aa4639a98a60d5231cd2c5306a918e7261983548c735312c1aa4639a58960d5231ce4c2b06a918c3f76550548c72ab1cc22a4638d9506150e318deeca90a518e6952580528c63d384cba14631e5c265d0a31a5ae92908518e1e5458c418c63dbb2a0284639a5895014231c5ec8312a898e4f63189544c733b16c2aa2639918b6155131cd6c5b02a898e6862d81544c739b0ec0aa2638ed906055131cb6c6302a898e6b62181544c734310c0aa2639cd84605513187eecaa0a898d2c72550544c69c382a82a2638bd506250d31c58a83128698e3454d85434c71daa0c0a1a638e1506050d318deeca90a498d2c74548524c6b4382a4292631edc165109318f0e0b288498c7a70194424c63cb80ca21263871516310931c9ac62908498e6452584424c70e2a2c7a0a631edd95014131a70e8a80a098d6872540504c61fbb2a82a0638b5516215031c72a8b00a818e2e64588540c72731ac42a0639958a6115031cd4c5300a818e6962980540c71d322c02a0639698d6015031cd4c4b00a818e6962580540c73930ac02a0638d5526190c318deeca90a418e2d64548520c734a92c029063355ce61908318f6e0b2a8418c7870595420c63d380caa10631e5c06550831c3aa831a8418e3554185420c732a90c2a1063875526390431a6aeb3208218d3575950410c63bbb2a8208634ddd95410431c6eecaa08218c777558c410c66bbaac62086395dd563104318baed29c6218c757694e310c66b3b482988631d5d6644c4319a8eca1a6218e946450d310c6e23928698863741c1434c4318f6eca80a018e3964540500c734b12a0280639998961d532187eecaa0a990e666258454c8733312c3a9e4317dd95314f21cccc4b08a790c7a7099543c863cb84caa1e431edc16550f218f0e0b2a8790c7a7019443c863cb80ca21e438b5506250721c9aa63126390c7b7654050c8732b14c3aa4430fdd95415221ccac5308a910e6562987538862fbb2a629c439958a6114e218f4e132a8710c7970995438863db82caa1c431e1c16550e218f
  | 11 => 0x10f46a1ac4288871ddd95114443e2a86a88a221e65625445110f4ca1cc028887a650d6014443ce2a2b00a221c9f7650f5010e3b388c4a80871d5c462540438dce430aa021c6d721855010e4fbb28628087a350e6214043d1a86b10a021e95439845010f4aa1ac2280871edd95014043e3286a80a021e69625405010f38b0aa02808717dd95314f428eeeca88a3a147b7654050d0a2fbb2a629c859394c6250e428eeeca88a321671515805190a3dbb2a0284859c58550142428beeca98a6a15547154c5350aac382a629a859314f6250d42caea630a86a1654531854350b2da98c0a1a859614c6050d428eeeca88a2a1554735445150ab8382a228a851edd95014142ab0e6a80a0a1570715405050a2fbb2a6298859554d6114c42cb2a6b00a62143d769524210a36bb4a921085a318d4350842b48e2a1a84215a87050d4210a3bbb2a2288859558d5114442ce2a2b00a22147b765405010b2cb1aa0280859c585501404287eecaa0a99964e6358854ccb172a2c421e65875506350b328daedaa085994777654451cca3dbb2a0286659998a61d5232cccc4b0ea91966a62983548cb3930cc1aa4659c58660d5232cd4c4b06a91967261583548cb38b0ac1aa4650fdd95415232c9ac7310a91962e54189438cb0f2a2c6214651ddd95114632ce2a2b00a31947b76540508cb38b0aa02846599d8b6155132c6ec830aa89965763185544cb33b10c2aa2659ad8b6055132ce6c3b02a89967061d81544cb1db20c0aa26596d8c6055132cd6c4302a89967361181544cb38308c0aa2650fdd95415132a68e2aa0a89953870550544cb162a6c4a1a658dd506150d32c68a830a869963b54181434cb1c2a0c0a1a658715163d09328eeeca88a29953474544514cab8382a228a651edd95014132a70e8a80a09957071540504ca1fbb2a82a0658d5516115032c72a8b00a81963664584540cb2b31ac22a065999896115032ce4c3300a81967161980540cb1d322c02a0659698d6015032cd4c4b00a81967261580540cb38b0ac02a0658b5526290c32c3aa931c841952d75990420ca96baca8210651bdd95410832a5eecaa0841962f76550420ca37baac62106533dd56310832c9eeab18841945d7694e320ca36bb4a719065339da424c8328daeb32264194cc7650d320cb463228699065711c5434c832b90e0a1a641947776544510cb1ab22a2288659c54560144328f6eca80a01963964540500cb38b0aa02806517dd95314f418deeca90a5a0c7a70d9632d063cb86cb196831edd950143418beeca98a720e56531854390637bb2a4294839a5496014a418f4e132e6520c797099732906a6b9ca4194831edd95014241cd2c4a80a120c5f7654c53506a6392a629a83561c15314d41c9ea631286a0e4c53189435072a29ec2a1a8396d4c6050d41cb0a630286a0
  | 12 => 0xa82871d9d85154143ccec428aa0a1e64621455050e3dbb2a0282875adc95014143ad0e4a80a0a1d73715405050eb838aa0282879a99752141438f2ed290a0a1d72719485050eb8b8ca4282871edd95214143ae6e2a90a0a1d70715485050f35328a428287d2d0c5214143e5486290a0a1e7265d445050fb1a96a228287d814b51141438f2ed288a0a1d6a729445050eb4b94a2282871edd95114143ad6e4a88a0a1d68725445050f39328a228287d8d485114143ec0a4288a0a1f53431445050f99218a2282875adc94314143ad0e4a18a0a1d737150c5050eb838a86282874e5d06214143ab2e6310a0a1e69621885050eb9388c4282875c5c46214143a72e8308a0a1d59731845050eb5390c2282875a5c86114143ce2c2308a0a1c3d769524310e2ebb4a9218878bd976250c43c5eca3128621e3765d854310f1bb28c2a1887a91886150c43c76cbb028621e3b651814310f54310c0a1887ac1846050c43c9ecbb128621e4f651894310f2bb2ec2a188795d946150c43d88c430a8621e5b65d814310f2db28c0a1887b21886050c43da0c23028621e1d75d954310f0f3b6caa1887a3d976250c43e1ecbb128621d1d759894310ec7394c4a1887659c66250c43b2ae33128621d9a709894310eccb84c4a188747dd56250c43b2ee2b128621d94715894310ecdb82c4a1887661c16250c43b1cec3128621e8e761894310f47b28c4a1887c3d946250c43d2ecbb0a8621f1765d854310fc3b16c2a1887e118b6150c43a3aeb30a8621d8e729854310ec6b94c2a1887a318a6150c43b2ce330a8621d9a709854310eccb84c2a188747dd56150c43b1ee4b0a8621d8c725854310ecdb82c2a1887661c16150c43d18c430a8621d96761854310f4b3b0c2a1887a5d946150c43e2eca30a8621f87621854310f4b310c2a1887a51886150c43f08c430a8621e84621854310f4db2ec0a1887c6d976050c43f16c5b028621f8862d814310fc9b0ec0a1887e41876050c43a3aeb3028621d8e729814310ec6b94c0a1887a318a6050c43b2ce33028621d95719814310f4a30cc0a1887669c26050c43a3eeab028621d8f725814310ec6392c0a188765dc56050c43b28e2b028621e8c621814310f4a308c0a1887669d86050c43d34ec3028621e9b651814310f8db28c0a1887e2d886050c43d34c43028621e98621814310fc4310c0a1887a21886050c43f26c23028621e9a611814310f4c308c0a1887e41846050c43d20c23028621c9f7650f5210e3d380c2a90871e5c061548438ece2302a421c75711815210e4fbb286290871bdd95214843e1a86a90a421e95439845210f4aa1ac229087995496114843d3287300a421e99435805210f34a92c02908727dd943d44438f4e0312a221c79701895110e37390c0a88871b5c8605444393eeca18a221e8d4398851
  | 13 => 0x800c00000000400000000800406c00001001800000c00000006000000000800400001403800800800000000002800000800002000c00c01000c00000000000001c00800801c01401000400402401400800000801800000c00800400000800000400000001c00000000000c00c00000000400400001000000001001800c00000800001400002400000c00000c00c00400c00000800401802000400001000000001c03404c01400001800800000000401400400802c00000000000000800800001402401000401001400c00001000000400401400237bb2a4296871ddd951147438f6eca80a1a1c6f765485290e3bbb2a228c871edd950142438f4e130ea4a1c79709875250e3b38cc1a92871d5c660d4943ccec330ea4a1d6a709875250eb4b84c3a9287599c660d4943acae3306a4a1e6b609835250f33a94c32928799d496194943cd6a5304a4a1e6b525825250e37bb2a42928759dc55214943ac8e2a90a4a1d6b705485250eb4382a4292874b5d06114943a9ae6308a4a1e65611845250eb5380c2292875a5c06114943a5ae8300a4a1d4d731805250eb3388c029287595c46014943cd2c0300a4a1c7a7098b5150e3cb84c5a8a871b9ca60d45438dae5306a2a1d727094b5150eb8b84a5a8a875cdc152d4543ae0e0a96a2a1e676298b5150eb9384c5a8a875c5c262d4543acce5306a2a1d65729835150f39b04c1a8a879998b5194543ccac5a8ca2a1e6b529825150f34294c128a879cd466094543cd6a4b04a2a1e68525825150f39a8ac128a871b9db52545438dcec292a2a1e6b52d815150f34296c0a8a879ad486054543cd0a4302a2a1c77765445150eb3b92a228a87591c95114543ae6e0a88a2a1d70705445150f3332ea428a871d5da5214543ae4e1290a2a1d71709485150e3bbb2a428a875cdc15214543ae0e0a90a2a1e66651485150fa3a18a428a87c990c5214543acee4a18a2a1d647250c5150e9aba0c428a87555cc6214543ccac4310a2a1d72701885150eb8b80c428a874d5d06014543aaae6300a2a1d66721805150eb2b90c028a879c58060145438ece3316a0a1c757198b5050e37394c3a82871b5ca61d4143ae4e3296a0a1d717194b5050eb9b8aa5a82875c1c552d4143ec6a5a8ea0a1f6052d475050eb5394a3a82875a5ca51d4143ad6e4a8ea0a1d68725475050fb1a90a3a8287d814851d4143cd6c5316a0a1d727198b5050eb8b8cc5a82875a9ca61d4143ad2e530ea0a1e73619875050f33a94c3282879914a6194143ccea4b0ca0a1e64525865050f33316a3282879958b5194143cccc428ca0a1e65621465050f35316a1282879a58b5094143ce4c3a84a0a1e7161d425050e373b6a4a82871b9d85254143ccea5b0aa0a1e6452d855050f33a90c2a82879914861541438eceda8aa0a1e6762d455050f32316a2
  | 14 => 0x70b0c4c523211c860e0ef00700000f81cc08613907de55b15306f475c6793f6000000080205b0fd8ffa3b200000000000002c700000003b002380000000000f813d87403222579fd8cd822f000012897a00026c800001001c00400400800000400400000002800001400001800000801000400000001c01c00400006800000400001400002400800400c00800400000001800000c00000400000400001000c00001000001801800c00003c00401002000400c00000800001801000003c00000400000800000000000000000000000000000000400c04000000800000c00400801000400000400000800800c00000400c00000c00000400800400400000000000801c03800c00801000000000400000c00400800400000002c00400800400403001800401001401c00400400400400400000004000802800000000002000002001800400800800001c00400400c00400c00801c00800c00c00800000001000000001800800001c00c00003002400000000800801c00000400000000800800000800800000400000401400001000800000000000000400400001400000000400000c00400000000400001400c00c01001801801004800c00000801000001801c02000001c00000c00400000002c00000c00400c00000400001401401400800401400000800400000000800002c00401c00000000401800401000800000401400800002001400001c00004400000000c01000400000400000401000800400400002c02000c00001800800800000c00c00000000000000001001400000802000000000000000c00c01000c00000000000800000000800400000001800001001000000000000400400000400400c01400400800000000800000400400401000c00400800000000400000400c00001c01000000000002402000001400000400801400c00000000800000000400400000400000001001400000800000800401c00800000001800400002000000401400001800000000005400000c00000405c00c00c00001800000001000800400400000000801000400c03800400800000800000002400c00800002802401800400400000c00000000c00000000000400402c08400400000800000402002400000000800400000800800800800801800400000000400000000c00401000c00800c01800c00400002402400800400c00003800000400400400000801400000c00400400000800801400801800000c00000401000c00002400c00400000800800400000002000400000400002000000400000c00000802005c00405400c00001c00800400800c00000000000001c00400400c00003801001000000001400001000c00000400400000000401000000000800800001400000000000400001800001c00400802c00400000002c00000000002400000400003
  | 15 => 0x33200003f800000000000000003af99280004df000000000033700000007ce00019700000000000000000e3600006ba20c78c68616d8000b44537000215835800000017c00220c20001c2068859145680009201b500002888d80000139c8d0f82201e59e88d467340001de06e631018310402a00000001cc0a8a87e3689da8b7c00000000000003ac39510380000000000d9012800040c8000aee86f37da1ac8962d036f80000000000000000c84000000000003400000009500005b4000002816000000004147f00a7219800000088c23e80002ee635261000000011f3248ca8ccc2743b9800000045f403218040c83e26903351d25f340b1140c4a88f31300005ec1d73231acc94414200013307fc848108878cc8628909d86a06aa15d3438000bfa0e914e800114084011f80006ce4290000000c120ab0c584e09a868b109a3f075243736b9a5021423c24e012d1d42fd0ca82e8d046831218708eb41fa19a9be41a07ab00000008fe0000d09160000793000228c0005ac0000000600226119a0c800000000000011f62821890c682046aa0df00010ec8e80000000d960000ac071cd940003aa000100200000011f91c609e37b8000d8400032d91d40003b8469a054da45723271fcc0000790000d1899e05713517005ce45d38f98ccf900910001774000430000000000000000000000005d300000005f00001ef9c34e7e0003e180bc0000003df060916a14504c18480007602b0800071400035e0480000000287000011c11b00020300001701758fb400042b000078800000003b08e00005110c80a9c0004b63f81648ec80a60b41d0021a82f3ae80000004210000000000000000130400087700023c8268000029a04c4ae132329a02c3cc00026387d82560002eb00000000000000cccc9a43e0518fcc7d000000022710061ce2e794e4fa030337800010301c91db91a845c5c319c1e5431a000409000000000000017200006ff00000004280003ee1c04e343db297821c0da83b16d000095600041c0000f1a0003d7960119204608d01d40000c7387000000067e4738000a861fd0000000000000000000000000000000000000000750c580003791948000c3200003b96bc00000000022600000000000a2cfdc03803300007f200006d8000ae253a300a1a40000002301e3c6284493668ac00007893378a100007fc00000000000002ba00000000000000000cfe0001ab0bcc6864cb00000010ce84100000011b80000b580000000000000000b1800000016a000047416f000000000012f80002aa2b835a00000001393f400008040000000000f880000691aa4550000000000400052721706b49d07fa45c968402e000000000000000000012340000002f582000007a607580003f00000000b1400000000000000000000ae000079c8100001d
  | 16 => 0x18204000143c382f10080001cf00000000000000f040003082e280000204711048a7800000000000000000001d980001dc000000000000000013907b0cce41632a0f2800000000000000000003671edc00001c00000000000000a88000e8400010b9a4067800000001084d02fe0000000000000000000000000018111e48b252d00000000004ca00012040000000001a48000501000142871e00019c8a340000f000000010120003c40000106336000000000000000000000000000000000a9a0004140000aa60000000a706c435e2dc113caa05350000b1c0000000540000c3e00000021646f084c0000814b7e000084a0c055e59f00000000000000000078000000000209c0000000000000000000000094000000000000000000000000000e520000001c501820003b800000001f43d48001078000000000052231b1e018809d8000000000044639d3ad80000000000f58b24f3e27b00000000003a50e21ae06745300000b4c18a69b03184c118c7393088000fd20902e500000008a500000000000000e794a0f1c60f0000000954115000000000030e000151c9f62b10a9800000000000009c40000000000a804ea00000686c07b000038380000004d80001bf40008bd0ec0374f480000001208bb81593ef8120814133000015400086300004f0f320a5252800000000000000004f200000014840003ba2381870b1a00028f8000d2665713b9e5c8ee7b300000000006da000002030a00000021ec00000000000007a0072000000000000007ca384dc42a11ad8830de8000000148800088800004182e403013f13bd1242ea42300009f4000477878400012e07a8658de63da3fc00000000001428ea895800003c0ec4fe20000001dd042000044514f43003d521d800000000000000000000001ce2078000000000063ca580001291cc448836100013b503e4520e400000001aa2118000ea078c3cd10e8e4c000000000000000000000006e03653d520e4fc47563388000d580000000000dea0003c2800000000000000000000000000000afa000000000000000000001640000000000000000000000082c0005a400000000004510000000000000000000012443500014a800000015693102fc4b52eb80010b4784000006c0000002ef9370ada66d1c284dc00000010d0e2092a1d61109ec800000000000000006dd27287cc1680000000000000000000000000037e0000f1025a00000000003a2891000162918849d22600944642421bfa06c00071d16884d88b4000000180c00039900011b80427cb1c08000a6c2c808e00005366bb00000000003e325d164cf84000000182800000033100000000001358000b3804308c00000000000000000000000000038c1960000000000000131000000000027028300005007bf0000e846b40
  | 17 => 0x62e028961c0000001480acceda00026a80000000004160ddc00076817d0b38c5200000000000000670e5000000000000000000000f43dc800000059a0000000e2035924897883268113020eb40004ea2f6000010c6e634f0b8078400032f0000712617000000000000000011d80000000001ab8e7a0004169f501f68da289808c21c4a43938b0c8325241f900640004dd419a218b0274f0171f68be4000040800000000000006740c400000011f00007dd00000000000001c20ca01580000f48bd501c0f708798d80005520e800000000004271ed40e20e243d000000000033980000002ab0bd1c60000000000000000026526d0ad8a46000000000106a0001978000000000000000055c000000191c000000009800000000024918c800000044a171842c00040380009300000000000000000000000000000000000002b4706000099c90041c000127c0fa54c10400011da00034e0f78e7c000000000053e0000000c5c0000002ce8000fca61b12410d8f3a7492cd824d15c89f3e300000003d215f1b240003d300000000005600328ffc00000000000000004c8000000000074b14c16f0dc862121400000000001c18000ba00002790524000516469000000065900011a03e202d00000011aa6e83dd205cbf274720909307f88f53af00000000003e600003220002af000046a00000000009a200000005b81c88661af9004db0590000000000000000007800000003e080001fa0000000f1c54a0b200000000003e10001b8c1d0000000000018800c36a02b400000044200000008d100011087008f400000004d26393558000bea8083bb08a44c84cd15a8000a3200000010b506223400e80007ae5592901588f0c3ec1ba8000e581790a7a0340003660d0000000006c3328000f8e3524610604d7e000000000090e0001b60b011c8000000008846200016e0000544000159000000000000000001f0000185a05000026300000000000001e4992c0000001e608ac1427790a9000000030100000004042011e280000bc6e7000000000000046500000000f63f0000000032400009700000003e900000000001a086e852e00000000000001102839318cba2f90000624fd40003f1a1f4ec447a2c1800025400000013fc34a8740001eb00008d636280e90a000000000ccefc6a40a58000f5a63d00000000000000000000000096000002ca3c14d0fa84f519c61d2f699acfb212f4598000f7867611c82240002c2000236d084391079800000000000000011bc2a400004f8000703000145510049e0b09a000002220c3087c00000000005d4b9a2e11741400adc0000000b551d607a0000b8c0000002f7208800000000006880006c000015ad1c00000000000a7e00021798c0af60000001d383a800000000004b07940000
  | 18 => 0x3540006b625f083c00000005ca0805686be000000080045e00000000000000000001136000345000000000000000000000000000000f7a0002ca87180000001ec8aa836841123080007ee00046080d880a04d0000000ba271900012cc34e40c0a001841f47354108000a044e70000b600004430000e9c11e2370000d700004e900000000000001c800002107e722d99ec0000004238c8000040330a845c7e88f3093022800006e12d8000bca0002948000f9e51c2c5a0280000bb00000009a05b500000000a40002ea0000a68276000000043c0004248000e4a00000000010c46c7000000014846733e1a3444e06f000000001e000330800071a62f407800000077b2b38000000000000000000044638280000fc00015d94c80000de3e280000002ef00000010520000001f5856e0001431ddcbb4000000176ccf41dd00022fc00000206313e069033d0c4055061400000000ac1e26950f7033d1e08514291d20de400602484e858c6b906f9e011125b943512246643740cc12a451806a0ad99d4080000271a1a06a00002f18000000000000000000000000000011982cd2e6154476873644593f80520e01a100c4166256116800000011300000000000000000fc02d219f00000009bc000000000088e2ff2b823e872e1460000a292020002be0000ece0001b021909103bc0000000a783d60000d4c0001a40000d5c92667400000f80001d300020d80000003579b700005790ef825ce7425128ba40015e76900000000005ba000000000021900000000000000000bc4f7600000000011768f938b815000032106a19040006eb2848000df81f22ec8d2c1b81da257000000044516c8db424a0001371434ae65573aba14c00026d3380a4800000042200000001b120c1d0400000012e879411a00004f8bec0002f00000cf800000035400006d200040d0000000000000000084400025f9bb40001164388000ad209b0d9839c83a3980699ca0e2228f3591cc87a80412030ae48900b813113ac50617f450934c6f474405b800040800000000000b804c00000000000000001e8ce2a000453042c0000000001f6c1d800045a0f9000000047b9c4c00000000000010b084a116221c5da2870001e611320000000158db65ae3e5052099200010d80fc47434a20d000104885b0001cf067600000023f84148ee2f005580000000000530000000000087405800000022f81b26c81710000cbe000000000000020700000010bc00000000002da000390800039a0003be000031c000000000094209a065000027e0000000000bfc6e93568cb024600031f80000000580000000078879000000073e000000128c00043c000070c8a830c000000064e07f14a00000001d93ec0790bd48e23a98ed80001030c211acb6200029980000005fb1e69df4f9c1764468b3c180
  | 19 => 0x3d420144aa14706d032000038c0000964c448b600000000000000000d38a16672139a3c40000002ca15585be3fb37016645c874c3c81ad482e5b000009980000000890b980005050000000c881de0002274000000000000000000000000000000001e8800000000000000000000000000000e3800000005943063b520588700007001360968cd462b370892ce048f81929de82d47920f38c8c0005f14399dac0000000000000000771000000000000022b80001540000000890ac811900000000002463970cc07ca00000f800000075146e8c7499c3a40e920dca9e84500019a0970610000229032401811f000094071200019586e483d1560c2417a0000001a30efe00003580000006c100000000e087502d871400e000322800000000000000002c059e000000060a0003e9a1b861a0000000000000576000000029c00042a000000000018f94e07d40001209798e66456384962408a4071f700003d427c16a0000ec255f0001dbccb012105723b033c8ff22a8000b1e073239905000035846ca1c82fa5750af000089c5f628d8da891619a0000000d4000000000000000001651c583960000bc000062640d000224000000000000000003e91df0bb89328c3000000000029a16b986915223b154800000000000021b00005ab3698000000000000000000000007680000000000001cec0000cc26b80009c45ce01d8d3490a0000000c105d200000000000c000000000000000d131c123103a1d53968c7802a0000000000000000000123cc625852220628fea57a07e0854d741240000000a944d6000000081200013e80008644db3c11a14000135344129c23a66e00016982e27464150af40008820000b580005260ca00000ba0002ef000000000000014f8fe8000000237c00064f0b983240000840000000000000000000000000027800007e28653c180004de00000000000000000ff800112a00000000000000000000000ec67cd316800000028e00000000000ce0001fecb407a00000000a56000000234000000000000002cc20e00020b8f5c5f81499bc4d1e0003150e189ea0691128a5857e000000000073628144b82c44f000033b92c47d64831a6140c0008a71e19a7409c0004308670000000000000000085f2929c88d888fd21e98a01e488e0708f9891c00030100010681fe2a580000000d637f0fe800032b2ae800000000000010a80000000001a10c7679b2bf22a072423628e8f740006242cb80007b85b600000000001b82e900005f800032885f0f4a8c70888000daa08b42a85d000a69a0000da0f420000000000a927b63cb0000ecc00041f80000685630001d480002f211e9fc80000000000000bde1bf00000000006fa1c993f457800000006d91ca57f09100000500001878b2c0b40002600000d2c000000065c000000000
  | 20 => 0xc000115636b00012d00000000000000f3c2490000c9800000030a00000000002b300000000000000000b0406835280000000000000000e5e3bd000039800072b2368cd00000001c1180000000004e000000016c2b413e475600000009fcbaa0000000000b4e00000000003ee18c24300000000000000000a9c000000000000014a0d700000000000002174c7c5583119d0c000315000224c58200030b10b079e000000000006e5b200012c00005310002320cc647b3f780005460003b71d640000000dd800096400041d07a00004270121c90ab80000001620000689340a2b000033f000000000600045b8000632512000000007a00000000002de00014400004a636e000000083c82b1fe9d6004c3e223792b40004a6000109400002000000011440001d41814cb40001be8000950095000000048a84f2e213983b62281a380010ae00045e0938a206ea0cd9a646308b800000000006970000a640004042cb000000000000013c400035100018e83801293a28000c681b70001460e140004369c30f807e1286000000000045880000000001b889e80000000000000e940003ff919800000000021c000000037600002c470f46697908707a727982805986ef00000007c08b23da00007ea1670dc8000f624f41888000b520092dd906c4bc22a2820000d8600000001103f200001512505740003ce1920bfe8780001cdc00000000017dc00000000000000000000000000424000347000034600005f0b1068a3a303d9550c4e00021306ac0005c90000df0fd61040001d5477e5cb00000000000120001dc8ca44c302f9b300000001c38000c58000044000075e000000000000012c20a84008480000000000000000000000000072040007b413224000000006de5e13099450af01a6000170800000044280000003b90000000bf800035380000006f647309343320000001a7c00015f00000000002e500000000000000000000000000000171ca8c000000208c0000000000000000896000143cdbc4bc1c7000000000000022c0000000377000000036310680000005b31e400000e8000000232cd8c00013095080004e011802140000000e092580006782e08d7400000036b2350aca1011d117a50967b0041235c15200000002d40008ba23c0c700001af1301fb40007753ea80000000002209a84000555028000000046230f0000dca7c907f125cc780002770e5800000030585ec0007040001228fee00400013f011811e17a00000002470000e5017e0002de80000007d7000210cfc88d83f30000000000000000089464c0001d340008810de0dd881056c4629ff8cc07f900000008720000001b6406a0000000bdc0000003488000f0215725b830c8a618700000000007d12318000a8210704e9af4d6258435b979cf14000127966077600033e994000
  | 21 => 0x2f400000006400001838c1a76503216dc0002ec000045000040f000000000000000000000005f401c8cb4494000000000000000031b80000000000000e98000791000049c0000000f79a987166f80000000000000101956800000000000000008af07f9ce104c0000d48d24b5a1b22970000f166b00a21b409726181a0168d1341280190360cb800038580000004400001268a10000000000000065500000000000000001384fbc5aa0002170ade1fb21a2094000000000230052a0000000000000000000000000000046791948d25402d2926c000000000000087e4f72a21468000000351000000084d1989c7869e413000000002c14300015200000000000e547340000a0800000056a000000000060634c03940000000000d5113c42000000002c8484000181cbf46cf3b600003b8218000000089a2d229d8dec9765d820f8001038000334800000087f000058c86245c47b013c0000004550000c182dd3d
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xd2154021b238458d2154021b208458d2154021e416318d21540219638750d21540219608750d2154021a638650d2154021a608650d2154021f014310d2154021a61811496008540a61821456008540a62854856008540c88631c94350040c90631c54350040a61811496008530a61821456008530a62854856008530c88641c9434c030c90641c5434c0308e1819c36250d208e1819cb6050d208e1811c16210d208e1811c96010d20a14835906454420a148458c6354420961801c94354420961821c14354420a148650c4354420a61801895150420c61725446050420a6180189514c420c6172544604c420a88835906448020aa0815906448020a888458c6348020ac08158c6348020961811d54348020961851c54348020961819d44348020a888650c4348020d097550c4348020aa0845846148020ac0835846148020b42831515148020b41831515148020b228414d5148020b218414d5148020b23845d95148020b20845d95148020b43835d95148020b40835d95148020a60865d15148020b43835d15148020b40835d15148020d21741d15148020963875915148020960875915148020b43835915148020b40835915148020e21641915148020a60865cd5148020b23845cd5148020b20845cd5148020d41731cd51480209638758d51480209608758d5148020b238458d5148020b208458d5148020e416318d51480209638750d51480209608750d5148020a638650d5148020a608650d5148020f014310d5148020c63765454148020c637654531480208e1829c36150d108e1829c76050d108e1821c16110d108e1821c56010d10a0c835906454810a0c8458c6354810961801c54354810961811c14354810a0c8650c4354810c61525c06150810c61525c46050810c61525c0614c810c61525c4604c810a61815496008410a61815952008010a90835906444010aa0825906444010a908458c6344010ac08258c6344010961821d54344010961851c94344010961829d44344010a908650c4344010d117550c4344010aa0845886244010ac0835886244010b42831515244010b41831515244010b228414d5244010b218414d5244010b23845d95244010b20845d95244010b43835d95244010b40835d95244010c61761d95244010a60865d15244010b43835d15244010b40835d15244010d21741d15244010963875915244010960875915244010b43835915244010b40835915244010e21641915244010a60865cd5244010b23845cd5244010b20845cd5244010d41731cd52440109638758d52440109608758d5244010b238458d5244010b208458d5244010e416318d52440109638750d52440109608750d5244010a638650d5244010a608650d5244010f014310d5244010c63765494244010c63765493244010961825d43244010
  | 1 => 0x7800a05b002840000440000000642f400006004096554f1fc00446c990eca569b350260000cc6c5e040002a2d0010c9e6e6aadca8a0131e8ae004700000003c800fa000ea6000006092800006c2e19e00578007a00001d128000027112564a8000000000000000638012ea80000000486124874b323b280205163112686410e0065f383300000572f9960720001ae003b9a4de273d8000000001492c0000000524939b1400113f0016a0000000005848ac800ce0000008195388932ac1022d724100184008c001e176b1510013a000ba1000063600000000032400ba001d51a006a02884d6418002600000fcba0000078006611800000040189145c002d1a0353e2ac186b00000005a00000d418518680000000000000000010e4d289b400003380120aa328c45400001300000000f80000003181c34390850ab6000c8000001001a20000000009b1bafd48008000001000280201000000402008000412000040a0300804020c09010060501808000104010020a000000a000380002030300c0002038100601010a40a0000000000200814020e0081c0002000000002c63615c261d4943c6171d8260d4943c61615c06114943c61715806014943c63625c262d4543c6172d8260d4543c61625c06214543c61725806014543c63625c662d4143c6172d8661d4143c61625c46214143c61725846114143c88629c26150c43a86829886150c43a92809886150c43e80621876050c43c84629c66050c43c86721866050c43a8a829886050c43a92819886050c43e8062d846050c43a8a829846050c43a92819846050c43e83621846050c43e80621846050c43e05435496114843e09435496014843e05435895114443e11435456014443e09435895014043e11435855014043c84631c54350842c88631c14350842c84641c5434c832c88641c1434c832c84631c94350441c90631c14350441c84641c9434c431c90641c1434c4318e1809c76250d218e1809cb6150d218e1801c56210d218e1801c96110d21a84835906448421aa0805906448421a848458c6348421ac08058c6348421961801d54348421961851c14348421961809d44348421a848650c4348421d057550c4348421aa0845806048421ac0835806048421b42831512154021b41831512154021b228414d2154021b218414d2154021a18835906454021a188458c6354021961811c94354021961821c54354021a188650c4354021b23845d92154021b20845d92154021b43835d92154021b40835d92154021a63865d12154021a60865d12154021b43835d12154021b40835d12154021d21741d12154021960875912154021b43835912154021b40835912154021e21641912154021a63865cd2154021a60865cd2154021b23845cd2154021b20845cd2154021d41731cd21540219608758
  | 2 => 0x1289078000a000241c172f000680696552536918c002f18000728f4d0ec8c002727c0000000003e000b00000280d8245600531c48ac35680016b0
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x420000001e00404821c0000028005160e8491f0a0000b344cb860854e1b3a006810600c98184400044007800018003018e500001804865d54310d210868412cba0e890aa010d4024d741d12154021a104bac832242a80436009359064485500868812cb98e690aa010d40251731cd2154021a204bac631a42a80436009458c6348550086a012ea188690aa010d802594310d2154021c04432eaa188690041420965d07454520082a0126ba0e8a8a401050825d641915148020b0049ac8322a290041440965cc7354520082a0128b98e6a8a401051025d6318d5148020b004a2c631aa2900415009750c4354520082c012ca1886a8a40106042197550c4344010a104a2ec3b2a488021440935d876549100428412cba0e8a92200854024d741d15244010a104bac8322a4880216009359064549100428812cb98e6a922008540251731cd5244010a204bac631aa4880216009458c6354910042a012ea1886a9220085802594310d5244010
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1752
  | 5 => 6659
  | 4 => 2306
  | 3 => 218
  | 2 => 35
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
  | 7 => packedAt gbK7 (744+((h/13+packedAt gbK7 (640+(h % 13)*8) 8) % 247)*7) 7
  | 6 => packedAt gbK6 (54312+((h/584+packedAt gbK6 (47304+(h % 584)*12) 12) % 2103)*12) 12
  | 5 => packedAt gbK5 (284108+((h/2219+packedAt gbK5 (253042+(h % 2219)*14) 14) % 10635)*14) 14
  | 4 => packedAt gbK4 (122210+((h/768+packedAt gbK4 (112994+(h % 768)*12) 12) % 4050)*13) 13
  | 3 => packedAt gbK3 (13728+((h/72+packedAt gbK3 (13080+(h % 72)*9) 9) % 347)*9) 9
  | 2 => packedAt gbK2 (2551+((h/11+packedAt gbK2 (2485+(h % 11)*6) 6) % 51)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3ff80ffffc07fff03f1f8ff87ffe1fe078fe3f
  | 1 => 0xc07ff01ffff80fffc01ff1ff87ffe1e38f1fc7
  | 2 => 0x7fffe03ffff01fffe001fff87ffe1c0fe3f8
  | 3 => 0xff8000003ffffffffffffe00007ffffff003ff
  | 4 => 0xffffffffc000001fffffffffff80001ffffc00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x830a6142847122500b05825a2a968aa0386e1b
  | 1 => 0x9510a4c50890e492c00a90aaa32aa8c18b16c5
  | 2 => 0x2a214289912241d555200133324ccc8c0da368
  | 3 => 0xc058b1622448909a653240000711116d001b6
  | 4 => 0x30460c1803870e0e389c49c44400001b66d800
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfee8e800fee8e800fee8e800fee8e800fee8e800fee8e800fee8e800fee8e800fee8e800fee8e800fee8e800fee8e800fee8e800fee8e800fee8e800fee8e800, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12341
namespace PEqualNP.Outside.L_meta_12341
open PEqualNP.Outside.L_meta_12341.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_32 : Interval gbAtlas 2 32 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 35 := (concat bgb_2_0 bgb_2_32)
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
theorem bgb_3_192 : Interval gbAtlas 3 192 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 218 := (concat (concat bgb_3_0 (concat bgb_3_32 bgb_3_64)) (concat (concat bgb_3_96 bgb_3_128) (concat bgb_3_160 bgb_3_192)))
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
theorem bgb_4_2304 : Interval gbAtlas 4 2304 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 2306 := (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)))) (concat (concat (concat bgb_4_288 bgb_4_320) (concat bgb_4_352 bgb_4_384)) (concat (concat bgb_4_416 bgb_4_448) (concat bgb_4_480 (concat bgb_4_512 bgb_4_544))))) (concat (concat (concat (concat bgb_4_576 bgb_4_608) (concat bgb_4_640 bgb_4_672)) (concat (concat bgb_4_704 bgb_4_736) (concat bgb_4_768 (concat bgb_4_800 bgb_4_832)))) (concat (concat (concat bgb_4_864 bgb_4_896) (concat bgb_4_928 bgb_4_960)) (concat (concat bgb_4_992 bgb_4_1024) (concat bgb_4_1056 (concat bgb_4_1088 bgb_4_1120)))))) (concat (concat (concat (concat (concat bgb_4_1152 bgb_4_1184) (concat bgb_4_1216 bgb_4_1248)) (concat (concat bgb_4_1280 bgb_4_1312) (concat bgb_4_1344 (concat bgb_4_1376 bgb_4_1408)))) (concat (concat (concat bgb_4_1440 bgb_4_1472) (concat bgb_4_1504 bgb_4_1536)) (concat (concat bgb_4_1568 bgb_4_1600) (concat bgb_4_1632 (concat bgb_4_1664 bgb_4_1696))))) (concat (concat (concat (concat bgb_4_1728 bgb_4_1760) (concat bgb_4_1792 bgb_4_1824)) (concat (concat bgb_4_1856 bgb_4_1888) (concat bgb_4_1920 (concat bgb_4_1952 bgb_4_1984)))) (concat (concat (concat bgb_4_2016 bgb_4_2048) (concat bgb_4_2080 (concat bgb_4_2112 bgb_4_2144))) (concat (concat bgb_4_2176 bgb_4_2208) (concat bgb_4_2240 (concat bgb_4_2272 bgb_4_2304)))))))
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
theorem bgb_5_6048 : Interval gbAtlas 5 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6080 : Interval gbAtlas 5 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6112 : Interval gbAtlas 5 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6144 : Interval gbAtlas 5 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6176 : Interval gbAtlas 5 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6208 : Interval gbAtlas 5 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6240 : Interval gbAtlas 5 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6272 : Interval gbAtlas 5 6272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6304 : Interval gbAtlas 5 6304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6336 : Interval gbAtlas 5 6336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6368 : Interval gbAtlas 5 6368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6400 : Interval gbAtlas 5 6400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6432 : Interval gbAtlas 5 6432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6464 : Interval gbAtlas 5 6464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6496 : Interval gbAtlas 5 6496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6528 : Interval gbAtlas 5 6528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6560 : Interval gbAtlas 5 6560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6592 : Interval gbAtlas 5 6592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6624 : Interval gbAtlas 5 6624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6656 : Interval gbAtlas 5 6656 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 6659 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))) (concat (concat bgb_5_608 (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800))))) (concat (concat (concat (concat bgb_5_832 (concat bgb_5_864 bgb_5_896)) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992))) (concat (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 bgb_5_1216)))) (concat (concat (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408))) (concat (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504)) (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 bgb_5_1632)))))) (concat (concat (concat (concat (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728)) (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824))) (concat (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)) (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 bgb_5_2048)))) (concat (concat (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240))) (concat (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)) (concat (concat bgb_5_2368 bgb_5_2400) (concat bgb_5_2432 bgb_5_2464))))) (concat (concat (concat (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)) (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656))) (concat (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752)) (concat (concat bgb_5_2784 bgb_5_2816) (concat bgb_5_2848 bgb_5_2880)))) (concat (concat (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)) (concat bgb_5_3008 (concat bgb_5_3040 bgb_5_3072))) (concat (concat bgb_5_3104 (concat bgb_5_3136 bgb_5_3168)) (concat (concat bgb_5_3200 bgb_5_3232) (concat bgb_5_3264 bgb_5_3296))))))) (concat (concat (concat (concat (concat (concat bgb_5_3328 (concat bgb_5_3360 bgb_5_3392)) (concat bgb_5_3424 (concat bgb_5_3456 bgb_5_3488))) (concat (concat bgb_5_3520 (concat bgb_5_3552 bgb_5_3584)) (concat (concat bgb_5_3616 bgb_5_3648) (concat bgb_5_3680 bgb_5_3712)))) (concat (concat (concat bgb_5_3744 (concat bgb_5_3776 bgb_5_3808)) (concat bgb_5_3840 (concat bgb_5_3872 bgb_5_3904))) (concat (concat bgb_5_3936 (concat bgb_5_3968 bgb_5_4000)) (concat (concat bgb_5_4032 bgb_5_4064) (concat bgb_5_4096 bgb_5_4128))))) (concat (concat (concat (concat bgb_5_4160 (concat bgb_5_4192 bgb_5_4224)) (concat bgb_5_4256 (concat bgb_5_4288 bgb_5_4320))) (concat (concat bgb_5_4352 (concat bgb_5_4384 bgb_5_4416)) (concat (concat bgb_5_4448 bgb_5_4480) (concat bgb_5_4512 bgb_5_4544)))) (concat (concat (concat bgb_5_4576 (concat bgb_5_4608 bgb_5_4640)) (concat bgb_5_4672 (concat bgb_5_4704 bgb_5_4736))) (concat (concat bgb_5_4768 (concat bgb_5_4800 bgb_5_4832)) (concat (concat bgb_5_4864 bgb_5_4896) (concat bgb_5_4928 bgb_5_4960)))))) (concat (concat (concat (concat (concat bgb_5_4992 (concat bgb_5_5024 bgb_5_5056)) (concat bgb_5_5088 (concat bgb_5_5120 bgb_5_5152))) (concat (concat bgb_5_5184 (concat bgb_5_5216 bgb_5_5248)) (concat (concat bgb_5_5280 bgb_5_5312) (concat bgb_5_5344 bgb_5_5376)))) (concat (concat (concat bgb_5_5408 (concat bgb_5_5440 bgb_5_5472)) (concat bgb_5_5504 (concat bgb_5_5536 bgb_5_5568))) (concat (concat bgb_5_5600 (concat bgb_5_5632 bgb_5_5664)) (concat (concat bgb_5_5696 bgb_5_5728) (concat bgb_5_5760 bgb_5_5792))))) (concat (concat (concat (concat bgb_5_5824 (concat bgb_5_5856 bgb_5_5888)) (concat bgb_5_5920 (concat bgb_5_5952 bgb_5_5984))) (concat (concat bgb_5_6016 (concat bgb_5_6048 bgb_5_6080)) (concat (concat bgb_5_6112 bgb_5_6144) (concat bgb_5_6176 bgb_5_6208)))) (concat (concat (concat bgb_5_6240 (concat bgb_5_6272 bgb_5_6304)) (concat (concat bgb_5_6336 bgb_5_6368) (concat bgb_5_6400 bgb_5_6432))) (concat (concat bgb_5_6464 (concat bgb_5_6496 bgb_5_6528)) (concat (concat bgb_5_6560 bgb_5_6592) (concat bgb_5_6624 bgb_5_6656))))))))
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
theorem bgb_6_1088 : Interval gbAtlas 6 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1120 : Interval gbAtlas 6 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1152 : Interval gbAtlas 6 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1184 : Interval gbAtlas 6 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1216 : Interval gbAtlas 6 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1280 : Interval gbAtlas 6 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1312 : Interval gbAtlas 6 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1376 : Interval gbAtlas 6 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1408 : Interval gbAtlas 6 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1440 : Interval gbAtlas 6 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1472 : Interval gbAtlas 6 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1504 : Interval gbAtlas 6 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1536 : Interval gbAtlas 6 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1568 : Interval gbAtlas 6 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1600 : Interval gbAtlas 6 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1632 : Interval gbAtlas 6 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1664 : Interval gbAtlas 6 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1696 : Interval gbAtlas 6 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1752 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608))) (concat (concat bgb_6_640 (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832))))) (concat (concat (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 bgb_6_1056))) (concat (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)) (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)))) (concat (concat (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504))) (concat (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)) (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 40 := (concat bgb_7_0 bgb_7_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfee8fee8fee8e800fee8fee8fee8e800fee8fee8fee8e800fee8fee8fee8e800fee8fee8fee8e800fee8fee8fee8e800fee8fee8fee8e800fee8fee8fee8e800
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,3,35)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,3,35)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276682472 * 2 ^ 32 + 4276676608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12341.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,2]⟩,⟨.and,[0,2]⟩,⟨.or,[4,5]⟩,⟨.and,[3,8]⟩,⟨.or,[7,9]⟩,⟨.or,[6,10]⟩,⟨.or,[3,8]⟩,⟨.and,[6,10]⟩,⟨.and,[1,11]⟩,⟨.or,[13,14]⟩,⟨.and,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682472 * 2 ^ 32 + 4276676608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682472 * 2 ^ 32 + 4276676608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12341

open PEqualNP.Outside.L_meta_12341 in
theorem PEqualNP.Outside.L_meta_12341 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682472 * 2 ^ 32 + 4276676608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682472 * 2 ^ 32 + 4276676608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
