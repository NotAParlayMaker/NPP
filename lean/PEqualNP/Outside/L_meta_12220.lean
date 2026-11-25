import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12220.Model
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


end PEqualNP.Outside.L_meta_12220.Model

namespace PEqualNP.Outside.L_meta_12220
open PEqualNP.Outside.L_meta_12220.Model
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

def SBf (j : Nat) : Nat := [6, 6, 6, 6, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_12220

namespace PEqualNP.Outside.L_meta_12220
open PEqualNP.Outside.L_meta_12220.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x18c00000a0000100c010000b24d3c50010000081c238228400be41bc41de31dc31ee21ec21be40bc40de30dc30ee20ec20fb10f610f410f810f010
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x30550308f61625335244000000011004e29500b0060075c00080018418020c16510431d220843c4310873080186a10020e41804172508436480086c10010e918021d030043c440087808010d920821b041043a46208740c410f110821e02104366a8086c15010e9a9821d053043c6a4087814810
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x40403105414c10c815052043405314810
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 25
  | 2 => 3
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | 2 => packedAt s0K2 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (297+((h/5+packedAt s0K4 (272+(h % 5)*5) 5) % 29)*6) 6
  | 3 => packedAt s0K3 (723+((h/8+packedAt s0K3 (675+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s0K2 (117+((h/1+packedAt s0K2 (114+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffbf83ffffc00fffffffc03ffff0ff
  | 4 => 0xffffffffffdffc1ffffff003ffffffc03fff0f
  | 5 => 0xefffe0fffffffc00ffffffc03ff0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffff00884212c95264b12dd2d2d2d777
  | 2 => 0xffffffffff011084255264a95256e565656bbb
  | 3 => 0xffffffffff42790849bb48d2649b7039b9b0dd
  | 4 => 0x2423d08e238ee388e3b9b03e3d0e
  | 5 => 0x18421ef03c0f03f0fc3e3e303ee0
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xc0c0c000c0000000c0c0c000c0000000c0c0c000c0000000c0c0c000c0000000c0c0c000c0000000c0c0c000c0000000c0c0c000c0000000c0c0c000c0000000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_12220
namespace PEqualNP.Outside.L_meta_12220
open PEqualNP.Outside.L_meta_12220.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x910a2003470001400000400033903cb30600008400005be41bc41de31dc31ee21ec21be40bc40de30dc30ee20ec20fb10f610f410f810f010
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x48000000258038030510000a0000153540001910c12d70001d340920f600000000060040000080e510431d220843c4310873080186a10020e41804172508436480086c10010e918021d030043c440087808010d920821b041043a46208740c410f110821e02104366a8086c15010e9a9821d053043c6a4087814810
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x81003105414c10c815052043405314810
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 25
  | 2 => 3
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | 2 => packedAt s1K2 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (297+((h/5+packedAt s1K4 (272+(h % 5)*5) 5) % 27)*6) 6
  | 3 => packedAt s1K3 (723+((h/8+packedAt s1K3 (675+(h % 8)*6) 6) % 44)*6) 6
  | 2 => packedAt s1K2 (117+((h/1+packedAt s1K2 (114+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffbf83ffffc00fffffffc03ffff0ff
  | 4 => 0xffffffffffdffc1ffffff003ffffffc03fff0f
  | 5 => 0xefffe0fffffffc00ffffffc03ff0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffff00884212c95264b12dd2d2d2d777
  | 2 => 0xffffffffff011084255264a95256e565656bbb
  | 3 => 0xffffffffff42790849bb48d2649b7039b9b0dd
  | 4 => 0x2423d08e238ee388e3b9b03e3d0e
  | 5 => 0x18421ef03c0f03f0fc3e3e303ee0
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xa0a0a000a0000000a0a0a000a0000000a0a0a000a0000000a0a0a000a0000000a0a0a000a0000000a0a0a000a0000000a0a0a000a0000000a0a0a000a0000000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_12220
namespace PEqualNP.Outside.L_meta_12220
open PEqualNP.Outside.L_meta_12220.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x2000000000490053d028c38000400d0000072c00020060c100404be41bc41de31dc31ee21ec21be40bc40de30dc30ee20ec20fb10f610f410f810f010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x182402110002800453560170000064c02c73c050200c48040054310e001320000000e510431d220843c4310873080186a10020e41804172508436480086c10010e918021d030043c440087808010d920821b041043a46208740c410f110821e02104366a8086c15010e9a9821d053043c6a4087814810
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x1103105414c10c815052043405314810
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 25
  | 2 => 3
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | 2 => packedAt s2K2 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (297+((h/5+packedAt s2K4 (272+(h % 5)*5) 5) % 31)*6) 6
  | 3 => packedAt s2K3 (723+((h/8+packedAt s2K3 (675+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s2K2 (116+((h/1+packedAt s2K2 (114+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffbf83ffffc00fffffffc03ffff0ff
  | 4 => 0xffffffffffdffc1ffffff003ffffffc03fff0f
  | 5 => 0xefffe0fffffffc00ffffffc03ff0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffff00884212c95264b12dd2d2d2d777
  | 1 => 0xffffffffff011084255264a95256e565656bbb
  | 3 => 0xffffffffff42790849bb48d2649b7039b9b0dd
  | 4 => 0x2423d08e238ee388e3b9b03e3d0e
  | 5 => 0x18421ef03c0f03f0fc3e3e303ee0
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0x88888800880000008888880088000000888888008800000088888800880000008888880088000000888888008800000088888800880000008888880088000000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_12220
namespace PEqualNP.Outside.L_meta_12220
open PEqualNP.Outside.L_meta_12220.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x10c00008b00a0c000e00000125000734f00000500818100000df43be43bc43dc439c43ef42ec42ef32ec32f741f441f731f431fb40f840fb30f830
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x3003422d06114945411c60c058500f2404c05c000000838a0040038030e00074794e43c7a90878c5210f2ea221e514443cda8087985010f1887a16310c42c621e658c430cb2887a0e510c41d2210839443cc7288618f10c831cc21e8198431035084206c10440cc21e6198430c3906418740c430
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x80004003045214443c21485010f105114043
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 25
  | 2 => 3
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | 2 => packedAt s3K2 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (297+((h/5+packedAt s3K4 (272+(h % 5)*5) 5) % 29)*6) 6
  | 3 => packedAt s3K3 (723+((h/8+packedAt s3K3 (675+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s3K2 (118+((h/1+packedAt s3K2 (114+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffbf83ffffc00fffffffc03ffff0ff
  | 1 => 0xffffffffffdffc1ffffff003ffffffc03fff0f
  | 2 => 0xefffe0fffffffc00ffffffc03ff0
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | 5 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xffffffffff40f84212fb4254952dd216d6f077
  | 1 => 0xffffffffff210bc425495ed12656d6d21b770b
  | 2 => 0x12109e4992649bb49b5b5b523bb0
  | 4 => 0xffffffffff0421088e2388e238e3a3a3a39ddd
  | 5 => 0x84210f03c0f03c0fc3c3c3c2eee
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xe8e8000000000000e8e8000000000000e8e8000000000000e8e8000000000000e8e8000000000000e8e8000000000000e8e8000000000000e8e8000000000000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_12220
namespace PEqualNP.Outside.L_meta_12220
open PEqualNP.Outside.L_meta_12220.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x2c012000000d80020000000840000068000589cc1d26a0e154c1578e3c485251834000007ca085410009048032320b54801e1d591322c003445c02e00001c00302000131c2c2060604000ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32ef32fe32fd32fc32ec32ff41fe41fd41fc41ff31f731fe31fd31fc31f431ff21fe21fd21fc21ff40fe40fd40fc40ff30fb30fe30fd30fc30f830ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x61dc320c3d86418730c830bf288617d510c3ee6218778c430ee18861f4310c3a862185f94030fda0061fa400c3f280187e10030ef98061fa300c3ba60187e4c030fdaa061fa540c3f2a8187e15030fd298617a530c3b4a6187ed0c30eda1861fa430c37486187e50c30fc21861b8430c3b086186610c30fda9061fa520c3f2a4187e14830fda1061fa420c3f284187e10830fd99061eb320c3f46418768c830fc99061f8320c3b064187a0c830e419061fb510c3f4a2187e54430fc28861fb410c3f482187e50430fc20861fb310c3e662187e8c430ed18861f9310c3f06218760c430f818861d0310c3f642187e88430fc90861f8210c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c837c87906f10f20f799641ec32c82fca3905f54720fb98e41f431c83f681907e10320fd98641f830c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c538837c87106f10e20bea9441ef42883d885107bcca20f6194417e51882faa3107dcc620fa18c41ee21883d843105f94220fd98441f830883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20df21a41bc43483de64907b0c920bfa8a41f751482eea2905f14520fa28a417451483ee62907d0c520fd98241f830483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20df21841bc43082fca4107bd0820f621041ef32083d864105f94420bea8841f731083e862107b88420f6108417e50083f680107e10020fd98041f830083de40107e88020f690041f920083d240105fd5310bf2a6217d54c42f8a9885fd4f10bf29e217d53c42f8a7886f90f10de21e217f52c42fca5885f54b10be29621ef32c43d865887dcc710fa18e21fb40c43f081887ecc310fc18621fb20c43f041885fd5210bf2a4217d54842f8a9085fd4e10bf29c217d53842f8a7086f90e10de21c217f52842fca5085f54a10be29421ef32843d865085f54610fba0c21f441843ee63087d0c610fb90c21f421842fca1087ecc210fc18421f710843f621085fd5110dfaa2213f54442fca8885f55110be2a221bc5444278a8885fd4d10efa9a215f53442fca6885f54d10be29a21dc53442b8a6886f90d10de21a217f52443dea4885bd4910bf292217d52442f8a4887b14910b629221ef32443d864887dcc510fa18a21fb30443f060887ec4110fb082217f54042fca8085f55010be2a0217f53042fca6085f54c10be29821be430437886085fd4810bf290217d52042f8a4087bcc810f6190217e51043ee82087d10410fb98821f431043ee42087d08410bf28021fb40043f080087ecc010fc18021fb20043f040087dc4010fd08021f510043f220087c44010
  | 1 => 0xe50c86faa190dfd5221bf2a4437d54886f8a910dfd4e21bf29c437d53886f8a710ef90e21de21c437d52887de8510fb10a21f799443ec32886fca310fdcc621fa18c43ef21887ee4310df94221bea84437f544877ea890cfd5121bf2a2437d54486f8a890ef151219e2a2437f53487bea690d7d4d21bf29a437d53486f8a690f714d21ae29a43be43487788690fbcc921f619243f731487e86290fdc8521f710a437f50487f6a090ded4121be28243f850486f0a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610ef90c21de218437e52087de8410fb10821f799043ec32086fca210fdd0421fa20843f731087e86210fbc8421fb10843ed21087ea4210f948421bf280437d50086fca7a05f54f40df21e81bc43d02fca5a05f54b40f799681ec32d02fca3a05f54740fb98e81f431d02faa9205f94e40bea9c81be439037887205f94a40bea9481be429037885207bcca40f6194817e51902faa3206f90640de20c81f731903e863205f94240dfa0481fb40902fea6a077d4d40afa9a817c53503b8a6a05714d40df21a81bc43502fea4a07bd4940b7a92817c52503d8a4a05b14940f799281ec32502fea2a07dd4540bba8a817c51503e8a2a05d14540fb98a81f431503f680a06f90140bf2a0817e53102faa6206f90c40de218817e52102faa4206f90840de21081ef32103d864205f94440bea8881be411037882207dcc440fa188817e501037e80207e90040dea0081f9401037280205fd5330bf2a6617d54cc2f8a9986f90f30de21e617e52cc2faa5987bccb30f6196617e51cc2faa3987dcc730fa18e61fb40cc3f481987e50330fc20661fb54cc3f4a9987e55330fc2a661fb43cc3f487986e90f30fca1e61f843cc37087987ed4b30fd29661f952cc3f0a5987ed0b30fd21661f942cc3f085987eccb30f599661fa32cc3f265987e0cb30f419661fb51cc3f4a3987e54730fc28e61fb41cc3f483987e50730fc20e61fb31cc3e663987e8c730fc98e61f831cc3e063987ec8730fd10e61f921cc3f043985fd5230bf2a461be548c27ca9185f55230deaa4613d548c2f8a9185f54e30efa1c61be438c37887187710e30ce21c617e528c3dca5185b94a30bea9461ed528c2daa5187bcca30ef19461dc328c3d86518730ca30bf28c61f6518c2eca3185f54630faa8c6175518c3ee6318778c630ee18c61f4318c3a863185f94230bd28461df308c3f661185fd5130dfaa2613f544c2fca8985f55130be2a261bc544c278a8986f90d30de21a617f524c3dea4985bd4930be29261ec524c2d8a4987bcc930f6192617f514c3eea2985dd4530be28a61f4514c2e8a2987dcc530fa18a61fb304c3bc60985fd5030bf2a0617d540c2f8a8185f94c30efa1861be430c37886187710c30ce218617e520c2faa4187bcc830ef19
  | 2 => 0xcaf0a0995fd5032bf2a0657d540caf8a8195f94c32efa1865be430cb7886197710c32ce218657e520cbde84197b90832f6a1065ec420cbbe64197b8c832ee99065ed320cafca2195f54432bf280657d500cbdea8197b95032f6aa065ec540cbdca6195b94c32e729865ef430cb9e86197b90c32d721865ed430cbd886196b10c32e6218658c430cbdea2197b94432f6a8865ec510cbdea0197b94032f6a8065ec500cafca7a0df54f41df21e83bc43d06fca5a0df54b41f799683ec32d06fca1a0df54341beaa4837e53906faa720ef90e41de21c837e52906faa520ef90a41de21483ef32907d86520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077c86a0ef10d41bfa9283ef52506dea4a0df14941f6292836c52507de64a0fb0c941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53106faa620ef90c41de218837e52106faa420ef90841de21083ef32107d86420df94441dfa0883f6411077a8220fd50441daa08837e50106faa020dfd5331bf2a6637d54cc6f8a998ef90f31de21e637e52cc6faa598fbccb31f619663f741cc7ec8398fd50731fa20e637e50cc6faa198fdd5331fb2a663f554cc7e8a998fdd0f31fb21e63b643cc7ea8798fd10f31da21e63f752cc7eca598fd54b31fa29663f742cc7ec8598fd50b31fa21663f732cc7ce6598fd8cb31fa99663f432cc7c86598fdd4331fb28663f550cc7e8a198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31efa1c63be438c7788718f710e31ce21c637e528c7dca518db94a31bea9463ed528c6daa518fbcca31ef19463dc328c7d86518f30ca31bf28c6376518c7be6318fdcc631bf28463fa508c6f4a118df54231fca846379508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c77c8698ef10d31bfa9263ef524c6dea498df14931f6292636c524c7de6498fb0c931fb98a63de314c6fea098fed4131bda82637c504c7f0a098de14131bfaa0637e540c6faa818df15031bf29863df430c77c8618ef10c31ee218639c430c6fca418df54831f799063de320c7b86418fb0c831e6190637e510c7ee8218fd90431faa0863f4410c7be6218fd8c431ee98863f5310c6fca018df54031fbaa063f6540c7eaa818fd15031fb2986376530c7aca618fdd0c31eba1863f6430c76c8618fd50c31fa21863b4430c7a88618e510c31fba9063f6520c7eaa418fd14831fba1063f6420c7ea8418fd10831fb99063e7320c7ec6418f58c831fa99063f4320c7a86418f90c831e219063f7500c7eca018fd54031fa280637f54c86fca990df55321be2a6437f53c86fca790df54f21be29e43be43c87788790fbccb21f619643f741c87e88390fdcc721fa18e437
  | 3 => 0x8008000000020100001501a0000100200000c00004016008010020000100100100800c0380800c000000010060000280400200c0000100400406007004010008000000000100101200007008004014020040080000101200600c0000000603c068050060081000100000c000000060000500b00e010008040040000480301802001002000000008000000040000600000c0081b02a0040100500600000808004018010030040080000800601c01004008008000020020000000d0040000080000600003000000028030090040040000101e008008080020300b0010020240980500000000805002004000130020000080000200c04807bf29687ee52d0edca5a1df54b43f6a96876d52d0efca3a1fd94743bb28e877d51d0feaa3a1dd54743bf28687fa50d0ef4a1a1df54343fca86877950d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df542439f29c87bf5290f7ca521ef54a43de29487bf5190f7ca321ef54643de28c87bf5090f7ca121ef54243de28487df4350f7c86a1dfd4943f7a92876f5250ef8a4a1fb14943b6292877f5150feea2a1ddd4543be28a87f45150ee8a2a1dfd4143fda82877b5050ef8a0a1fe14143bc282877e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea8087be5310e7ca621e794c43dfa9087be5210f7aa421ef14843dfa8887be5110f7aa221ef14443dfa8087be5010f7aa021ef14043bf29e857d53d0b7c87a16f10f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7c86a16f10d42f7a1285be4250afea2a17dd4542bba8a857c5150be8a2a15d14542bfa8285fb5050af6a0a15f14142fc28285785050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842d6a10857e5110afaa2215f94042bea80857f54ccafca9995f55332be2a665be43ccb7887997bd0b32f721665ed42ccbd885995f94732bea8e657e50ccafaa1997bd5332f72a665ed54ccbd8a9997bd0f32f721e65ae43ccbda87997b10f32d621e65ef51ccbdca3997b54732f628e65ef50ccbdca1997b54332f6286657f548cafca9196f952329f2a4657d548cb7aa9194f55232be2a4657d538cbbe87196f90e32de21c65dc438cb3887195f94a32b729465df328cbde65195f94632fb28c6576518cafaa3197d54632baa8c657e508cbf4a1195e94232bea8465f9508caf2a1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8996f90d32de21a65ef324cbbc64995fd4532fba8a6577514caf8a2997d14532ba28a657f504cbf6a0995ed4132be28265f8504
  | 4 => 0x5ea65a38a00061800072205200000000080a0005f075c00083e00038000000000000012a00000031600000000000045825a00022a17e8e05707e442c0000000000ec5444880005c200000056400000000069c00063a2482a80a80000004c05cc0006bc0000007ee00000037a7f04a40c83ae0788a84741c80000f47a26aa4e88505e870850e00046e00000000000000087e1140000000003a000041478234c0340003c60007807264e07288ba29200000000000035023434a0000000026900004b80001f621a0000005521280000000001460002400006d47ce00000000000e79c6e226267a28e3da00000000000000000036680200061e5a00004a044e6c666e29c7002cc7b00241da6540000002bc0008860003ea4521aa4402d400003014c2141e87580008365882040001c200020a00046286c0003ce0005ba1860004a24cc00040600000000082c4801cc37486a6be8b619a8045ae8d00008c60207900000008163a200077000000000000000000000082a00013e0000004288800001d20006ae4225348102420007c400015600024a6d263800057800000046016835613268e20200800000054c1503dc0000100000421ca11059c7aa1b67940000000000008220000000ce0000000001f213a2c65c44d429442e30c0007240007425fe5183ba0000007e85bc0006b80a400023a52a32e3182d270e4c245c2fa00033400075216e8ca10e00023e71c51430271a6248b81721e05942862763f25665e028c0007860004163c28883f000047844809e8348740004d622655885c3e04660000006a809237e00030862e76a00033e0000005dc2ce84e7b251a78c0003e800024649e08400035832c48400011c1b05a67d60005de0007d40000000003206960000006a68266420e42645da6e00000004900007f68827343b42587b800000000034e56869426867054a00000014e2b00863900005be81818a4e217c45a0d274a04049a89e00070a0000003d25b248a00031000033a0000006726f22da00082e07483a05468c36c43c1344560004e600a02000801000018048000020300000201000001801018004010010000000980300a0080080000a00400000012018010030020040781300e02001000004000018060100180000200200c010050000000280000400000003002024000000020000000200c00402803006014028020000080280600c00800000004010048010020000000100000c0080d018004000010000140400502201c028020000100000200400000000006000010000000080500000a004018010020100c80104001c0200b0020080080100000001804000010000090000000000000c0080280000602400003000010010020080140b00601c000028000080000080101e014008010000000000c0000000a80500000c0180000e000000
  | 5 => 0x1e00000000075606400044200000041c6e83787dc4a884c29a0000f62160000005840007a00000000007d058c59a0005ce00079e0bc00000025e31c37624419002e6627687382080008528328060001d04388b20000ac2ee0000000000006a009c8565324180007fe00000078400066c7141481a66027a81a24da4945486d030020e5f805c1b20d82b643a2805ec4f01fe6340686364460e201400000062c1ea00008c3605860007fa5f22501ee78810a00009056c8721f000026c0e86880001700b600065600000087a7ae2e05825006ba8e400068600004a19812e00000006a8380000000006c00001807500006300007640000000004ac16a53e6483962f600054e0004ec5123320000ea35a1dc00000033c3c011a4761c671863c1423400ba2ea0000003063942103ca0c25e202829606c00000065c0006001a046a00038c0007d250273015a1fa0161d62fe8de3aa22c8bc0ee89232a0000004e40005460003380003220000005a20007bc31a2a068000000000000000000002264e66a6280008581947b43708204b60000000007f82be22088a80e12426636a76c66420657a53a6ca08838404c43622e2ac3a82388122c21660004321581e481c6661124b407019200055a20c0008a03d07124c86740de0006c40000001ac00030e00000000000050887c0004640004303be0005d27a40007747e259664036486876263200078e40a5a859e17417a88c6d60985c00000000364721224c48c430a85400000074c3b600000000057c58a8962d60002541826160000000000000000000000a000000039a0002820000003e200000062a55474421e0c41f84507de2b874609415228800a1002366e673e0005b00003461645605c83980003303de00027c4f849602c0d009677807a31408a5220fa12000000000000000033685e2c03f62ca0f00000005b40562300007ea2ec6086ac0003d85a40004ee40e6f60000004fe00000075446c00000060653800047e0002ae4266ea7fc07c85a1760044de2a63b01400008080005d81b41ce66023c00000041a0008400580004925626cc4865927a68c219c04e39e4248448aa6224123ec7726500320a27102f000000000055632624c25c88e2700000006f00003440a67d800011652c00041e10800019655015414a2e27960000006824440000000000008605b60000000001e60004b267843e2de0e08000008b411867628a12c4bc44c1042c43ee2842124ea6ec49c5c60008be0480600000001267e01a86fc0000002e60006e468a7ca00c1300000000c60000005fa1d42f808078a0008a28e60388d647c4ca75a38870200022801e7662b26f48c000669260e44a5100003cc00016200076e0623042786a44f66fa27e0000008ac5284dc67c51e2240002aa0000da4fc10235e8c80000000007206a22723f8
  | 6 => 0x5f650a5d600018c26021c4024aa7045200b43860b87c06dc4700000004ba01c8982e48d873a38257236200016010c73c6d800000048e0002c83b800000000000025600035c5423720000000760187ec0003d64b08e216c77672c0008768626de00072e5360003c44f40007480000004fa0006b40000000000001440000000000000001d85e40c060453c50400019e0ca5d400001a8da42a3fe3a42ba0e664a1bc3f407e0464541b877c69a0000003ac00000058e0002a265279a15c4be1f400077a0001e20007b645e1362908dc8143a600000060c7606200000000000ae00002a4f20003680000003422328ce48250600057e00000081a68400071e0003b227a0006980f208271656a11e59861c00005e0002b40006ce00000087826e7da3243920007c218820061002600000089c00000000006e65e64c8903fa0000005907f40000fc83c00038e0001065404a60005302f25ac6681ae5fc00000084818e0005ca70c2f479800063e0006fe89a0dc72a0002fc0000aa00051673600000055e8ae00003e00009a40000083000040800069e0003121de04400000015e67e2221fc4044340002d00000002e886e0008d274e0000be00029847a0000000720000000000008944c60008b00006c880c0124ae00006600055c6ee7ac00003a3bc2a400000000013c3e40008460007c682805a6f826a6124981c07e65ee1be6b600000000058000000000084a2d88a40004200006147400000000fe39c03c5740cc0001384683d40b28d46585e651c0005f48a63547f23e61ba00088461a1ec0007060004d052675e50c7cc64677e0000000000002740002dc0004100f80005aa1c424e8cc3520007c848c0b03284d20d66c284234852e1a46446da5d00000000500005b800000037c2180000008244d84ce00000060a7322520005248640007be6b200000029e57686608e7ba40c0006266b000056e1780007923c83fc36e0d400081e1848703
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xe544426e62951109b58a544425f63551109718d544426f62551109b189544427761551109ed81544423e65151108f98c544423e64d4d108f593534426e62d4d109b58b534431f54d4d10c7153534431e64d4d10c7593534434e62d4d10d358b534435561d4d10d6583534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534427b6054d109d18453442786014d1097994534431f5414d10c7150534431f6414d10c7190534434f6214d10d318853443576114d10d6d80534423e6590d108f196434431f5390d10c714e434423e6510d108f194434431f5310d10c714c434432f54d4910cb153524434f53d4910d314f524426e63d4910cb90f524432c43d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109ed81524426e6514910cbd50524432c5414910d3d4c524434c53149109b98c524432e4314910cb10c524426e65cc9109b197324432f54cc910cb153324434f53cc910d314f324426e650c9109b194324432f540c910cb150324434f530c910d314c324438c430c9109d997314433754cc510cd153314435453cc510d9d4b314436452cc510bc9833144337540c510cd1503144357530c510d514c3144394430c510d9d483144364520c510f10c8314427a65cc110ced53304433854cc110d614f304436b52cc110da14b30442f261cc110ced503044338540c110d6d4c3044358530c110e610c304436b520c110da14830443c8320c110f40c4304433854c4110d614f104436852c4110cd15210443545384110d914a104425f63550109718d540426f62550109b189540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530427661d4c109e983530423f6454c108f191530426f6254c109b18953042776154c109ed81530431f5310c10c714c430423f64548108f191520425f63548109718d520423e64148108f590520434f530c810d314c320438c430c8109d59441043355410410bc5804104275650c410d594c3104394430c410f10c831042f1600c4109d59421043655208410bc58021042796510010ce55040042f16110010ec1044004279650c010d694c3004398430c010f20c830042f1610c010f40c430042796508010da54820042f16108010f808420042796584010bc58610042776544010ad19110042d46344010b9189100427b6544010ae19110042d86344010ba18910042f36544010dcd9510043b36444010bc99110042f06444010ec19110042b06444010f4d8d10042f26344010bc18d10043d06344010b418d10043725344010dc14d10043b24344010ec10d10043e36244010bc98910042f06244010f818910042e06244010f8cc910043e03244010
  | 1 => 0x823c6590d20c7d4e434831c5390d208f994434823c6510d20c7d4c434831c5310d209b997324832f54cc920cb153324834c53cc920ba983324832f540c920cb150324834f530c920d314c324838c430c920cdd53514833454d4520d5d4f514835453d45209d98f514833643d4520cd10f514836732d4520d90cb51483375414520cd15051483575314520d514c51482766314520cd90c51483344314520d9cc8514836432145209d997314827465cc520cdd53314833454cc520d5d4f314835453cc5209d9943148274650c520cdd503148334540c520d5d4c3148354530c520e510c31483c4320c5209e997304833b54cc120ce153304835853cc120ba98b304837351cc120dc147304833b540c120ce150304835b530c120d614c3048398430c120f20c83048373510c120dc14430483d0310c120ce153204835853c8120dc147204832c5488120d314e2048364518812097d8d540825c63550209dd85540827461550209d984540827561150208f993530823d64d4c209b98b530827661d4c209d587530827a60d4c208fd91530823c6454c209bd8953082776154c209d185530831f5310c20c714c430826d6510820cb55042082e960108209b594320834e530c820e310c32082e9600c8208fd91510823c645442097d8d510825c6354420d5d4c3108354530c420e510c31083c4320c420d954421082e960084209e59440083395410020ba58840083a842100209e594300835a530c020e610c30082e9620c020f20c830083d0310c020ba58a200826f6548020ab19120082cc6348020b9185200827b6548020ae19120082d86348020bc18520082eb6548020dad9520083ab6448020ba99120082e86448020ea19120082a86448020f2d8d20082ea6348020ba18d20083c86348020b218d200836a5348020da14d20083aa4348020ea10d20083e36148020ba18520083e06148020b818520083e33148020f80c5200825e63d53109758f54c426e62d53109b58b54c423e64d4f108f59353c426e62d4f109b58b53c423f6454f108f19153c426f6254f109b18953c431e5310f10c754c43c423e64d4b108f59352c425e63d4b109758f52c434e530cb10d354c32c438c430cb10d594c31c4355530c710e510c31c43c4320c710ced5040c435a53cc310d614c30c4398430c310f20c830c43d0310c310dad4820c425e63d52109758f548426e62d52109b58b548423e64d4e108f593538426e62d4e109b58b538423f6454e108f191538426f6254e109b189538431e5310e10c754c438423e64d4a108f593528425e63d4a109758f528434e530ca10d354c328438c430ca10cdd50418435653cc610d514c3184394430c610f10c831843675208610d694c3084359530c210e610c30843c8320c210f40c4308423e63d51108f992544425e63951109758
  | 2 => 0x648c430ae592310c39a438c430e610e310c2ea628c430ba58a310c3cb328c430f20ca310c2f2618c430b6596310c359658c430b6992310c39a648c430a6992310c399648c430b6192310c2da628c430f298a310c2ca628c430f258a310c2da618c430b4986310c27b654c430aed91310c2b8644c430e610d310c2eb624c430ba189310c3c8324c430e690c310c398430c430f2cc8310c3c8320c430f44c4310c2da640c430b6190310c2da620c430b6984310c3d2610c430f4944310c3d1510c430f4d04310c3d2410c430f4504310c3d0410c430bc98c310c3d2630c430dc94c310c3d2530c430f4d0c310c3b2430c430f490c310c392430c430f450c310c3b0430c430f410c310c390430c430f4cc8310c3e3320c430f0cc8310c3d2320c430f44c8310c3d0320c430f80c8310c3c0320c430f4d94310c3d2650c430f4594310c3d0650c430f4d90310c3d2640c430f4590310c3d0640c430f4d50310c3d2540c430f4550310c3d0540c430f4d88310c3d2620c430f4588310c3d0620c430f4d48310c3d2520c430f4548310c3d0520c430f4d08310c3d2420c430f4508310c3d0420c430b698f210c2d963c8430e610f210c3c832c8430f40c7210c2da6388430b658e210c3984388430f20ca210c3d031884309ed95210c2786548430aed91210c2b86448430b6d8d210c2d86348430e610d210c3c83248430f40c5210c2db6308430b618c210c3984308430f20c8210c3d03108430f8484210c25e63d53209758f54c827661d53209d58754c823e64d4f208f59353c827661d4f209d58753c823f6454f208f19153c82776154f209d18553c831e5310f20c754c43c834e530cb20d354c32c838c430cb20d594c31c8355530c720e510c31c83c4320c720ced5040c835a53cc320d614c30c8398430c320f20c830c83d0310c3209798f548825d63d52209d987548827561d52208f993538823d64d4e209d987538827561d4e208fd91538823c6454e209dd8553882746154e20c794c438831d5310e20cbd50428834e53cca20d314c328838c430ca20d594c3188355530c620e510c31883c4320c620d694c3088359530c220e610c30883c8320c220f40c4308823e63d51208f992544825e63951209758e544827661951209d586544825f63551209718d544826f62551209dd85544827461551209ed81544823e65151208f98c544823e64d4d208f593534827661d4d209d587534831f54d4d20c7153534831e64d4d20c7593534834d62d4d20d5987534835561d4d20d6583534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209bd8953482776154d209d185534827b6054d209b188534825e6514d20c7d50534831c5414d20c7d90534831c6414d20d3d8853483576114d20d5184534835b6014d208f996434
  | 3 => 0x30bad89300c2e8624c030f20c9300c2f3614c030bc185300c3d0314c030b698f540c2eb6255030ba189540c2f36155030bc185540c3395415030b698c540c35a6394c30b6992530c2da6294c30b6986530c27965d0c30ba98b430c2e962d0c30bc987430c2f161d0c30b6597430c35965d0c30b698b430c3ca62d0c30b298b430c3c962d0c30b6987430c3d261d0c30b4987430c3d161d0c30b698e430c2ba6390c30a698e430c33a5390c30e694e430c27b6550c30bad89430c2e86250c30bcd85430c2f06150c30e650c430c2ba6310c30e698c430c33a5310c30e694c430c2db6510c30b6594430c2da6410c30e6990430c39a5410c30e6550430c2da6210c30b6984430c39b6510c30e6994430c3996510c30e6194430c39b6210c30e6988430c3996210c30e6188430c39b6110c30e6984430c3996110c30e6184430c39843d4830e610e520c2bb6454830ae191520c3984354830bcd85520c2f06154830e610c520c3695214830b698f420c2d963d0830e610f420c2da6390830b658e420c39843908309ed95420c2786550830b6d8d420c2d86350830e610d420c2f36150830bc185420c3984310830ea508420c39843cc830da94f320c3ca53cc830f2d0f320c3aa43cc830ea10f320c3c843cc830e210f320c279658c830ae992320c2b9648c830e690e320c398438c830ba98a320c2f2618c830bc586320c2d9658c830d6596320c2da648c830e6992320c29a648c830e6592320c2d8648c830b698a320c2ca628c830b6986320c3d2618c830b4986320c3d1618c8309ed95320c2bb644c830ae191320c398434c830bcd85320c2f0614c830e690c320c398430c830f24c8320c2da640c830b6190320c2da620c830f2988320c3ca520c830f2548320c3cb420c830f2908320c3c9420c830f2108320c2da610c830ba98c320c3ca630c830da94c320c3ca530c830f2d0c320c3aa430c830f290c320c38a430c830f250c320c3a8430c830f210c320c388430c830f2d94320c3ca650c830f2594320c3c8650c830f2d90320c3ca640c830f2590320c3c8640c830f2d50320c3ca540c830f2550320c3c8540c830f2d84320c3ca610c830f2584320c3c8610c830e610f510c3c832d4430e610e510c3c83294430aed91510c2b86454430e610d510c2eb6254430ba189510c3c83254430e610c510c3c83214430dc544510c2da63d0430b658f410c39843d0430f20cb410c2da6390430b658e410c3984390430f20ca410c27b65504309e195410c2db6350430b618d410c3984350430bad89410c2e86250430f20c9410c3984310430f20c8410c3b14110430e610f310c3c832cc430dc94f310c3d253cc430f4d0f310c3b243cc430ec10f310c3d043cc430e410f310c3e332cc430f48cb310c3d032cc430f80cb310c3c032cc4309e596310c2ba
  | 4 => 0x9cca518c3563294630d50ca518c3643294630d10ca518c3365454630cd551518c3944354630d9949518c3655254630f10c9518c3364354630cd10d518c3673254630d90c9518c33654cc630cd553318c39443cc630d994b318c36552cc630f10cb318c29e648c630c7952318c2ce628c630d394a318c31e540c630d3948318c355510c630cd950318c335540c630e590c318c394430c630d9948318c365520c630f1cc8318c3c4320c630b5594318c355650c630d5950318c396540c630c5950318c395540c630d5150318c356520c630f1948318c346520c630f1548318c33a54cc230ce553308c36a52cc230da54b308c37251cc230dc547308c23e64951309b98a544c26d62951309d986544c27561951309e582544c25f63551309bd89544c26c62551309dd85544c27461551309ed81544c23e65151308f98c544c23c63151308f996434c23e6510d30cbd53524c32c54d4930cb90f524c32c43d4930cbd50524c32c5414930cb90c524c32c43149309b997324c32f54cc930cb153324c26e650c930cbd50324c32c540c930e310c324c33754d4530cd153514c36752d4530d914b514c33643d4530cd10f514c36732d4530d90cb514c3375414530cd150514c3675214530d9148514c3364314530cd10c514c3673214530d90c8514c27665cc530cdd53314c33454cc530d9d4b314c36452cc5309d994314c337540c530cd150314c394430c530d9d48314c364520c530f10c8314c33b54cc130ce153304c36b52cc130da14b304c37351cc130dc147304c31c548c130d314a304c354518c1309bd89540c26c62550309dd85540c2746155030b398b430c2d661d0c30b6583430c29e6390c3097594430c31e6510c30c7594430c39a6010c30e6580430c31c43948308fd91520c23c64548309dd85520c2746154830e310f320c29e648c830b398a320c2d6618c830b6582320c38e430c830e310c320c34e540c830d3150320c3ca600c830f2580320c31c4394430d30ca510c23f64544308f191510c26f62544309b189510c39443cc430f10cb310c29e648c430b398a310c2d6618c430b6582310c396430c430e510c310c3c7320c430f10c8310c356540c430d5150310c356520c430f4980310c3d1600c4308f992500c23d6494030c710e500c34c3294030d50c6500c39843d0030f20cb400c3d031d00309e596400c2d96390030e610e400c3c83290030f40c6400c3385450030b6d8d400c3984350030bad89400c2e86250030f20c9400c2f36150030bc185400c3d031500309e594400c3395410030e610c400c3c83210030f40c4400c2ba648c030ae592300c398438c030ba98a300c2e9628c030f20ca300c2f2618c030bc586300c3d0318c03097d95300c29c644c030b3189300c2d4614c0309ed95300c2bb644c030ae191300c398434c
  | 5 => 0x405033451901409bd89531026c6254c409dd8553102746154c40c794c43102b96010c4097d8d521025c63548409dd8552102746154840cb54842102b96010840e310c321025f63544409718d511026f62544409b18951103355110440ae5804110394430c440f10c831102b964900408fd95401029c6350040ab18940102b461500409ed9540102d86350040ba18940102f06150040aed95401033b6550040e6d8d40102b86350040e618d40102986350040ce94d40103ab6250040ae18940103a86250040aa18940103ab3250040ea0c940103b36150040ae18540103b06150040ac18540103b33150040ec0c5401026e62d53309b58b54cc27661d53309d58754cc38c430cb30e510c31cc3c4320c730ce95140cc2eb6250330ba18940cc2f36150330bc18540cc33b5410330b698f54cc2ea62d5330ba58b54cc2f261d5330bc58754cc33b5495330b698c54cc2ea62d0f30ba58b43cc2f261d0f30bc58743cc2eb6250f30ba18943cc2f36150f30bc18543cc39a6310f30ae99352cc2b964d4b30bc98752cc2f161d4b30dad4a52cc27b6550b309e19542cc2db6350b30b618d42cc2f36150b30bc18542cc3a94210b30ea90f32cc3a843ccb30ae99232cc2b9648cb30e610e32cc2f2618cb30bc58632cc2bb644cb30ae19132cc2f3614cb30bc18532cc398430cb30f298c32cc3cb430cb30ea90c32cc3a8430cb30f210c32cc388430cb30ae99351cc2b964d4730ba98b51cc2e962d4730dcd4651cc27b65507309e19541cc2db6350730b618d41cc2eb6250730ba18941cc3b14110730ec90f31cc3b043cc730f8ccb31cc3e032cc730ae99231cc2b9648c730e610e31cc2ea628c730ba58a31cc3c8328c730aed9131cc2b8644c730bad8931cc2e8624c730e610c31cc3c8320c730f498c31cc3d3430c730ec90c31cc3b0430c730f410c31cc390430c730f8cc831cc3d2320c730f40c831cc3e0320c730f00c831cc27b65487309e19521cc2bb6448730ae19121cc2db6348730b618d21cc3e121087309b98b548c26d62d52309d987548c27561d5230c7d8d548c26e62152309b588548c27661152309d584548c2ce62d0e30b5987438c31d5410e30a7594438c31d6510e30c710e528c32e5494a30cb552528c38c4394a30d3d0e528c32e4394a30cb10e528c34c4394a30c310e528c32e5454a30cb551528c38c4354a30cb90d528c32c4354a30cb953328c32d54cca30e310f328c29e648ca30c7952328c2d6618ca30c7950328c34d520ca30cb950328c32d540ca30e390c328c38c430ca30b3594328c34d650ca30d3950328c38e540ca30c3950328c38d540ca30d3150328c31c4394630d30ca518c3365494630cd552518c3944394630d994a518c3655294630f10ca518c3574394630cd90e518c3344394630d510e518c3144394630d
  | 6 => 0x71c5310d219b997324872f54cc921cb153324874c53cc921b9987324872f540c921cb150324874f530c921d314c324878c430c9219d997314873754cc521cd153314875453cc521b998b3148737540c521cd1503148757530c521d514c3148794430c521f10c8314873454c8521d514f214872c5488521d314e214873b54d4121ce153504875b53d4121d614f504867a63d4121ce90f504873843d4121daccb504876832d4121dccc7504877031d4121ced5050487385414121d6d4c504875853141219e98c504873a4314121ce10c504876b3214121da0c850487733114121dc0c450487732114121da884504865f63550219718d540867b60550219e181540867a60150219e580540863e64d4c218f593530866e62d4c219d987530867a60d4c219e583530863f6454c218f191530867b6054c219e181530871f5310c21c714c430866d6510821cb55042086e561108219b594320874e530c821e310c32086e5610c8219d59441087355410421b958841087a442104219d5943108756530c421e510c31086e5620c421f10c831086e562884219bd9521086ac6448421b318d21086e860484219dd9521086b46448421b518d21086f06048421b9d9521087676548421e9d9121086e66448421b919121087a46448421a919121087c76348421b998d21086e46348421f118d21086c46348421d994d21087645348421e990d21087a44348421f8d8121086e46048421f818121086e060484218fd91500863c645402197d8d500865c63540219bd8953d026c6254f409dd8553d02746154f40c794c43d031d5310f40d394c32d034d530cb40e310c32d0356530c740d554c31d0394430c740f10c831d026f6254e409b18953902776154e409d185539031e5390e40d394c329034d530ca40e310c3290356530c640d554c3190394430c640f10c8319026e62d4d409b58b535027661d4d409d587535034e62d4d40d358b535035661d4d40d5587535035960d4d40c7d90535034f6214d40d318853503576114d40d5184535035b6014d40c714e43502ba6090d40c7d4c435034f53d4940d314f525026e63d4940cb90f525032c43d4940d3d4c525034c53149409b98c525032e4314940cb10c525026e65cc9409b197325034f53cc940d314f325026e650c9409b194325034f530c940d314c325038c430c940d5d4f515035453d4540d9d4b515036452d45409d98f515033643d4540cd10f515036732d4540d90cb51503575314540d514c51503675214540d914851502766314540cd90c51503344314540d9cc8515036432145409d997315027465cc540d5d4f315035453cc540d9d4b315036452cc5409d9943150274650c540d5d4c3150354530c540e510c3150367520c540d914831503c4320c540d614f405036852d0140dc147405031c5390140cb14a
  | 7 => 0x210c31e5d80430c7966010c31e5580430c7946010c31e510f520c7944394831add91520c6b46454831e510d520c6f36054831bc181520c7944314831d9548520c6d663d0831b558f420c79443d0831b598e420c6d56390831e510e420c67765508319d195420c6d76350831b518d420c7944350831bcd81420c6f06050831e510c420c7a54210831e510f320c76653cc831f194f320c7c743cc831e990f320c7a443cc831f110f320c78443cc8319d596320c6b6648c831ad592320c796438c831e510e320c6e6628c831bc982320c6f1608c831b5596320c755658c831b5992320c796648c831a5992320c795648c831b5192320c6d6628c831b198a320c6d6608c831f4982320c6d2608c831f4582320c677654c831add91320c6b4644c831e510d320c6f3604c831bc181320c796430c831e510c320c7c5320c831b5990320c6d4640c831b5988320c7c6620c831f1948320c7c5520c831f1d08320c7c6420c831f1508320c7c4420c831b5980320c6e6630c831f198c320c766530c831f194c320c7c7430c831e990c320c7c6430c831e190c320c7c5430c831e910c320c7c4430c831e110c320c7c7650c831f1994320c7c5650c831f1194320c7c7640c831f1990320c7c5640c831f1190320c7c7540c831f1950320c7c5540c831f1150320c7c7600c831f1980320c7c5600c831f1180320c79443d4031f10cb500c7944394031f10ca500c6b76454031ad191500c7944354031b9d89500c6e46254031f10c9500c7944314031f10c8500c77150140319798f54c865d63d53219e98354c867960d53218f99353c863d64d4f219e98353c867960d4f218fd9153c863c6454f219ed8153c86786054f21c794c43c871d5310f21d394c32c874d530cb21e310c32c87375410721d594f31c8754530c721e510c31c87c4320c7219798f548865d63d52219e983548867960d52218f993538863d64d4e219e983538867960d4e218fd91538863c6454e219ed8153886786054e21c794c438871d5310e21cbd50428874e53cca21d314c328878c430ca21d594c3188755530c621e510c31887c4320c6218f98f544863e64951219798e544865d63951219e9825448679609512197d8d544865c63551219bd89544867761551219ed81544867860551218f994544863e63151218f993534863d64d4d219e983534867960d4d21c7d53534871c54d4d21c7993534871d64d4d21d358b534875561d4d21d6983534875960d4d218f992534863d6494d219798e534867a6094d219e582534863f6454d218f191534866f6254d219dd85534867b6054d219e181534865e6514d21c7d50534871c5414d21c7d90534871c6414d21d3d8853487576114d21d6d8053487586014d218f996434863c6590d21c7d4e434871c5390d218f994434863c6510d21c7d4c4348
  | 8 => 0x31e610e508c76a5294231da54a508c7c83294231d6d0e508c73a4394231ce10e508c7584394231c610e508c76b3294231d68ca508c7583294231da0ca508c7483294231dccc6508c73a5454231ce551508c7984354231da949508c7695254231f20c9508c73a4354231ce10d508c76b3254231da0c9508c77331542318f992544c66e62951319b58a544c67561951319e982544c679609513197d8d544c66f62551319b189544c67761551319ed81544c67860551318f994544c63e6590d318f994434c72f54d4931cb153524c72e43d4931cb10f524c72f5414931cb150524c72e4314931cb10c524c66e65cc931cbd53324c72c54cc9319b994324c72f540c931cb150324c78c430c931cdd53314c73454cc531d9d4b314c76452cc531c7152314c74c528c531ced53504c73854d4131dad4b504c76852d4131ce90f504c73843d4131daccb504c76832d4131dccc7504c73b5414131ce150504c76b5214131da148504c73a4314131ce10c504c76b3214131da0c8504c7733114131d68c4504c66f62550319b189540c67b60550319e181540c6ce62d0c31b5587430c6da60d0c31a798e430c65d6510c31c7994430c71d6510c31e5984430c7956110c31c710e520c63f64548318f191520c67b60548319e181520c78c43cc831a7992320c6ce628c831b5586320c6da608c831e390c320c78c430c831d3950320c74c540c831f1984320c7c5610c8318f992510c63d6494431c710e510c74c3294431e510f410c7c432d04319d596410c6d56390431e510e410c7c43290431cd151410c6d76350431e510d410c6e76250431b9189410c7c43250431bcd81410c6f060504319d594410c7355410431e510c410c7c43210431ad992310c6b5648c431e510e310c6e6628c431b958a310c7c4328c431bc982310c6f1608c43197d95310c69c644c431b3189310c6d8604c4319dd95310c6b7644c431ad191310c794434c431b9d89310c6e4624c431f10c9310c6f3604c431bc181310c71c4394031d30ca500c63f64540318f191500c66f62540319b189500c6d663d5031b9d89540c6e46255031bcd81540c6f06055031cd550540c6d66315031d598e530c6d66494c31b598a530c6d66094c319d597430c6e662d0c31b958b430c6f260d0c31bc583430c6d565d0c31d5597430c6d662d0c31f198b430c6c662d0c31f158b430c6d660d0c31f4983430c6d260d0c31f4583430c6d66390c31ad98e430c6966390c31cd94e430c7965390c319dd95430c6e76250c31b9189430c6f36050c31bc181430c7954310c31ad98c430c7966310c31cd94c430c7965310c31b5d94430c6d56510c31b5990430c7966410c31e5950430c7955410c31b5988430c6d66010c31e5d94430c7966510c31e5594430c7946510c31e5d88430c7966210c31e5588430c7946
  | 9 => 0x58b535075561d4d41d6983535075960d4d41c7d90535074f6214d41d318853507576114d41d6d8053507586014d41c714e43506b66190d41c7d4c435074f53d4941d314f525066e63d4941cb90f525072c43d4941d3d4c525074c53149419b98c525072e4314941cb10c525066e65cc9419b197325074f53cc941d314f325066e650c9419b194325074f530c941d314c325078c430c941d514f415076452d0541c714e415072c5290541d6d4f505075853d4141dad4b505076852d41419e98f505073a43d4141ce10f505076b32d4141da0cb505075b5314141d614c505076b5214141da148505067a6314141ce90c50507384314141dacc850507683214141dcd04505073a41141419bd89531066c6254c419ed8153106786054c41c794c43106b56110c4197d8d521065c63548419ed8152106786054841cb54842106b56110841e310c32106b564904418fd95411069c6350441ab18941106b860504419dd9541106d46350441b918941106f06050441add9541107376550441e5d8d41106b46350441e518d41106946350441cd94d41107a76250441ad18941107a46250441a918941107a73250441e90c941107b36050441ad18141107b06050441ac181411065f63540419718d501066f62540419b189501066e62d53319b58b54cc67a60d53319e58354cc78c430cb31cd95141cc6e76250731b918941cc6f36050731bc18141cc7375410731b598f54cc6e662d5331b958b54cc6f260d5331bc58354cc7375495331b598c54cc6e662d0f31b958b43cc6f260d0f31bc58343cc6e76250f31b918943cc6f36050f31bc18143cc7966310f31ad99352cc6b564d4b31bc98352cc6f160d4b31d9d4a52cc6776550b319d19542cc6d76350b31b518d42cc6f36050b31bc18142cc7a54210b31e990f32cc7a443ccb31ad99232cc6b5648cb31e510e32cc6f2608cb31bc58232cc6b7644cb31ad19132cc6f3604cb31bc18132cc794430cb31f198c32cc7c7430cb31e990c32cc7a4430cb31f110c32cc784430cb31ad99350cc6b564d4331b998b50cc6e562d4331dcd4250cc66e62d52319b58b548c67a60d52319e583548c71f63552319b988548c66d62152319e980548c6796015231b398b438c6da60d0e31c7550438c69d6510e31c7594438c71c4394a31cb952528c72d5494a31e310e528c74f4394a31cb90e528c72c4394a31d310e528c70c4394a31cb951528c72d5454a31e310d528c72e4354a31cb10d528c72e54cca31cb553328c78c43cca31a7992328c71e548ca31b6982328c71e540ca31d3548328c72e540ca31cb550328c78e430ca31e310c328c6cd650ca31d3594328c74e540ca31e3950328c70e540ca31e3550328c74c540ca31cd953318c73554cc631d994b318c76552cc631c710e508c74c3294231ce952508c73954942
  | 10 => 0x8cb584394232c610e508cb6b3294232ce951508cb395454232e610d508cb725154232dc545508cb3a4354232ce10d508cb6b32542328f992544ca6d62951329d986544ca7561951329e982544ca79609513297d8d544ca6f62551329dd85544ca7461551329ed81544ca7860551328f994544ca3e6590d328f994434cb2f54cc932cb153324cb1c548c932cdd53514cb3454d4532cd90f514cb3443d4532d9ccb514cb375414532cd150514cb364314532cd10c514cb673214532d58c8514cb3b54d4132ce153504cb7351d4132dc147504cb3a43d4132ce10f504cb6b32d4132ced50504cb385414132dcd44504cb705114132ce90c504cb384314132dacc8504cb5a32141329dd85540ca7461550329ed81540ca786055032b358b430cad661d0c32b6983430ca9e6390c3297594430cb1e6510c32c7594430cb8e6210c32e3588430ca3e64948328f592520cb1c4394832e310f420ca6d6590832b358e420cb8c4390832cb151420cacf6350832e310d420cae76150832b9185420caeb6050832ba181420ca6d6510832cb550420cb8c4310832ab992320caad648c832e310e320cae6618c832b9586320caea608c832ba582320ca5f654c832a7191320cad4614c832b6181320ca6f654c832abd91320caac644c832e310d320cae7614c832b9185320caeb604c832ba181320cb1c43944328fd91510ca3c64544329ed81510ca786054432c710e500ca3f64540328f191500ca7761540329d185500cace63d5032b9d85540cae46155032bad81540cae86055032cb550540cace6315032d398e530cace6494c32b3986530cace6094c329b597430cae661d0c32b9587430caea60d0c32ba583430cacd65d0c32d3597430cace61d0c32f1987430cac661d0c32f1587430cace60d0c32f2983430caca60d0c32f2583430cace6390c32ab98e430ca8e6390c32cb94e430cb8e5390c329bd95430cae76150c32b9185430caeb6050c32ba181430cb8d4310c32ab98c430cb8e6310c32cb94c430cb8e5310c32b3d94430cacd6510c32b3990430cb8e6410c32e3950430cb8d5410c32b3984430cace6010c32e3d94430cb8e6510c32e3594430cb8c6510c32e3d84430cb8e6110c32e3584430cb8c6110c32e3d80430cb8e6010c32e3580430cb8c6010c32e310f510cb8c4394432abd91510caac6454432e310d510caeb6054432ba181510cb8c4314432d9544510cb8c43d4032e310e500caaf6454032ab191500cb8c4354032b9d85500cae46154032e310c500cb6950140329bd8953d066c6254f419ed8153d06786054f41c794c43d071d5310f41d394c32d074d530cb41e310c32d066f6254e419b189539067b6054e419e181539071e5390e41d394c329074d530ca41e310c329066e62d4d419b58b535067a60d4d419e583535074e62d4d41d3
  | 11 => 0x3f6550c43abd894310eac6250c43add854310eb46150c43aed814310eb86050c4397d954310ecc6250c43b51854310ed86050c439dd855210e7461548439ed815210e7860548439bd895110e6c62544439ed815110e7860544439bd895010e6c62540439dd855010e746154043c798e5310e9e6294c43a79865310e9e6094c43add855210eb46154843aed815210eb86054843cb5485210eaf6254443ab1895110ebb6054443ae1815110f355114443abd895010eac6254043add855010eb46154043ce5405010e776154f429d18553d0a7b6054f429e18153d0b1e5310f42c754c43d0a776154e429d1855390a7b6054e429e1815390b1e5390e429d9875350a7561d4d429e9835350a7960d4d42d358b5350b5661d4d42d55875350b5a60d4d42d65835350b1f6414d42d3d885350b576114d42d51845350b5b6014d42d61805350b1c5390d42ab98a4350b1f5310d42d314f4250b1c5390942d5d4f5150b5453d45429d98f5150b3643d4542cd10f5150b575314542d514c5150a766314542cd90c5150b344314542d9d085150b364214542d6d4f5050b5853d4142dcd475050b7051d41429e98f5050b3a43d4142ce10f5050b5b5314142d614c5050b735114142dc1445050a7a6314142ce90c5050b384314142dad085050b3a42141429dd855310a746154c429ed815310a786054c42c794c4310aad6210c42ab5924210a3f6550842a718d4210ab46150842ae1814210a6f6550842b318d4210ae46150842ba1814210aaf6550842cbd954210b8f6350842ab18d4210b8c6350842a318d4210b2e5350842e9d854210aac6150842e91854210aa46150842ead814210aac6050842ea1814210aa8605084297d8d5110a5c63544429ed815110a78605444297d8d5010a5c63540429dd855010a7461540429d98754cca7561d53329e98354cca7960d5332cb95142ccae76150b32b918542ccaeb6050b32ba18142ccb2f5410b32b398f54ccae661d5332b958754ccaea60d5332ba58354ccb2f5495332b398c54ccae661d0f32b958743ccaea60d0f32ba58343ccae76150f32b918543ccaeb6050f32ba18143ccb8e6310f32ab99351ccaad64d4732ba98351ccae960d4732d9d4651ccaae64d4332ab59350ccae661d4332b958750ccb6b50943329d987548ca7561d52329e983548ca7960d5232c7d8d548ca7661152329d584548ca7a60152329e580548cad661d0e32b6983438cb1d5410e32a7594438cb1d6510e32cb953328cb2d54cca32c710e518cb365494632cd552518cb944394632d5d0e518cb364394632cd10e518cb544394632c510e518cb673294632cd951518cb355454632e510d518cb364354632cd10d518cb673254632c710e508cb3a5494232ce552508cb984394232dc946508cb715194232d6d0e508cb3a4394232ce10e5
  | 12 => 0x40000002004000000400400300000000000000000000000002000800000000b0000034002024000001000200300000000020000008034000000001002800000000080180100080028008000005000800401e00100180040060020058000004002000000c00400300080000080000008000000000001000800e002001801400400e003002c058007000000001400300000040020000000020014000000000c00200301600040200000010000000001001000c004000001000c000002000801800a0000038020002002001000000000b000000800200000100080040030050010002000000000000c0050010000000002002000400000100080000000020048004000002002800c002001006801001e002000800400000300000000020060000038000000002000000200600000100020090050008000000000000000c00000000000000000030004002000003800400a006000801000000000400000100020000004000008003802800600000000100000030018000002005001000000000300000000020000000010004004000800c01c009000000000a0000060004014004000001400000d00180100040000000000008002000001800a00200080080060000018000002001000000000200200000000020000040004000000009000000000200100000020010068008010004000004000000e000000400400000000180000000008014004000002000c0040000000000000002000800000000000000080020030008000000003000800c0000000000000002001001802800000200100040000010000000002022004005c00c0080010008000009000001c008000000000803200f002000000000000180000000000028000008000002000000800900000000640140038018004019003800001400100100a8026003001000800800300100100000000008000000007000800000000000280080020000060050008003001800000400100300000000140030004014000000000000000b00180480000020008017665294743d954a51d0f665254743d954951d0f6a5294343da54a50d0f725194343dc54650d0f6a5254343da54950d0f725154343dc54550d0eae62d0e43ab58b4390eb661d0e43ad5874390eba60d0e43ae5834390eb661d4a43ad5875290eba60d4a43ae5835290f2f5294a43ab98b5190ead62d4643ae9835190eb960d4643cdd465190eae62d4243ab58b5090eb661d4243ad5875090f3b5094243cb90f5250f4f4314943cb90c5250f6752d4543d914b5150f3643d4543d9d485150f645214543d5d0c5150f364314543dad4b5050f6852d4143dcd475050f7051d4143ce90f5050f6b5214143da1485050f735114143dc1445050f5b4314143ce90c5050eae62d0c43ab58b4310eb661d0c43ad5874310eba60d0c43ae5834310e
  | 13 => 0x56e80400000008ba0000002134c6e00031494a0750003406826d0f83020000028a4611a0f9187cca09b00000001084695000000000046a0002078ad81ab1ada664000136401a0e821e0bb00005c896e00042026a80000001b28000f84a051db204445c1df10c80005846aa000000000000000c000000004b0000000a440000000000f105ce18f00000008ae00000000004070000000e506f84de8b286e092a1e1a1f91960193ce95194109410001e78dbc94c4099dd0000a04065800000070a25899b859662216322c09767ad3a2a5090308412141e8045e8b41ae956129c81f06685f8fe88db3bb9fd45da93149923604560761f780ecb3a66d241174504016a21522d869c1bd4c888cd22051721a94246120fe32e0930d9e9c515509ac0de67c213082474a2c709612202549ac00000003066ad01395a40623f8000000093a2544a68000dca000001c000001001000400000c002001000a00000100100020020030000000000001800000800300000000020030000000004000002800400a00000b80000000000008004002000002801400400000b000c000000000800000000b00100000020030028000000002000000c000006000000c000001001801000200400000180020010000004008002000000000600300000100000000000000002006000800000000200180080020000008008000020000001c004000000000c000004002800c00600600200080020000020000004000000800000001a00100000180030028044000000000000000e007001000400c007002001801e0020018004006002000800001200200280d4000001000001c0080000000004000000003000c000001000000001200e000800800401300000000080010020010000000000800c008012000804c00800100200000040000050014004000005000000e009001001000000b00180540020070010010000000001803000a001002801c00000100e0004000009003009400000400d80240000000000058002005002000c002000000000000000b00500000000050080000000001000001000c001004000000000100080080060060020010000002002000000a00b00000000020000008020000006000000401200000080000000000030000022001000001800a001000000800000600000740080050008008002006000803401e00100100040140040010004006002000000000400100380040000000000000004013000002000000000080000040000000008000006000800000200100100000000000000000002000000805800a0000050000000000001000c0120010060000000002000800000200000200000100010040014002004000001000200000000040000000030004010000000000800000100000080000000008014006007000002000000400000040000
  | 14 => 0x5a63e7000078089079a47c800147c46c4c520b83380940000000000000192924cbf00000000000000000000024cf5e2a6000000000000042a00000005e54e70000000000000085800000000009b000000026a80011748d100000000000000000001280a3d00000000005060000000ab69d2000044917601b0b01ab05a882819012492387544a2100c1341d6023866864e5db1f51548f8032831680009489cd416800000095b281000123c2d70000de4a680000d98000cfc3d200022ad02e00038e800000000006700fc0000000d1000000060020f8000da800000000d45989644fd99fc0d23d44608195286659145a7e92b00003d31e0000058b33c0000c1e00028026c847e00008b9cad33c87b390000147491d106000103406a06005081e28b500018d000000000011880000004fb00000003ce0a5800000000000000009e63d33cb80000002c8000000000020a2cc00000000000000820a5294700014fc0000000000000000000000000000072a00006ece9a53c000118436a00030ea3a86a27e133a17e8fc646e32880007807a24ec8000b7c8ca47f150c00000000000010100004399f809c47ec16708048fc6b845c2770e622654d59bd40000ed2758be4f7275a0000ce0b7a0000000000f9a00016b14ec88a1bf00111fce6c3a2397a8ece3e8c63bda418bd40f83b7000024e36129a97fc00034930980000000000000000ae60001508af00003cc34600000004470000f9000042029700008ae4040000001418000427800000063d0000000000000000235000000000000000006890000b7470e1094f78488dcc083494800000000004200000008b7000000000036c09701b80007110000c989c000001f189c000000042829cdce0001131158150000000027c86079200002800000000e81e2c0004cf45200008320000000eb4afc0000000000b6e2b40be938c8a012100000000000002a683e4142318421a03c00047100007e4a1a78c09c01589de8de1a79100e6671e2178f20d820a34af0728da21560521a8074241812d8dd0aa81dd35b9d04d563da00000000009612a580000000000e280000002ba0fe87ed32643f00002c0e921750000000d306834b50f712c63800000000000000000234c00013a34c90ac00000049611440003a4352872c0004f81401f60824000000252c1704ab30d20d800000048f80000000000000000d6a0ba4ef9b391c06c00e110ec00040124715a0fe42571a022045080500c50ebc7b60003ce16080000992d3800000017300011ec000000000000000058e31b0fe40003a306080007742d800011793c667913d1b74644980201160014a72314ba268c902234dd8abd2006411aa84dc00056f018195074019546c80000000001419d980680000000000d5c20236f80000009fd46600012a052128f93c88d00950
  | 15 => 0x515216485a24d19a8148000101379a9301ae00019da3eccd600000000008a60000000cf49ea9cc20aa44c00070409f92351c68dc0000000b0a0001de8fc0dd29170da27840000000ea2878bea9e400028c43dc9e71ff18f10e200021e80000009b60b700000000000000edc00095a00000011169d840d8000e368df5090b9cd9654a28d24e0a1e00000027f12745610bc8e6c8d68530001b9000000c000003c000000000034c0000000000f7c0000004d21db51c42b0016808433299700005b4d082be0000000c645860d2800000001110a0000d2e4dc1378ccc0880000000e640000dd2c78000ed80000000000d0e55000020c481600038a926400000000000000000000000000d1e000000000000024649c80013680003ea00000000000000ab445200004390c484492e3e5800000061c28a9c64aee0000001a0800016c0178470f700fc102069000020b00d22500004a01351d0000028700025b11ac99000012d878460123e8000aa61ac2430f749421473ab9c3800061100001e12788990000000000000015920436e00000000003860000000000f580000000bc853600000000000000e000003b02ee6e303c800115e00033313c47e8000000000000092b00000001c234301000003c600000000000000000d422f8b980001b0000110a0001720bac168000000000000093303312000001d346100000000003e397bd1e60004cfa95904e8504b391d40000000000000000000000000000088932b06e05cc79000000000009da4ee886d1e000000019dc91644d07b89c82e874a1ca91d02ce821194815472e88f32497f0b7678a3200184dc460d0000cd88680001252740000000430275cf1c80500021e10e4703000000000085e000000044200000022b400000046807108980001f08ddca72299000264895a000000000000000000000000003c94418fd8d425a125a19140001e500000013e64230001e54c7600000000000000000001dcc00001300004ec0000000000ecc00098b000259514c9f137e13fc00078d3c1000053c11900000000000002c38788d4469b1969ff80001163b20000ed48c300008c11540000b5875c7da46944c06353ee0004f9000094e0000001a900000004198b3c000058000000000006d0000000e02000000000031e000000000000005110880000000000001d8c0000911dfa7503280ad1961a680b21fe0000000000000000000117200007b04f87d84840869784c163c62f9133007420511c21950000000000b000003d02cba52400050a00003a11ae00022d153000018e02d28d0510000000000046a51913a197c00050531700011d8000362000000000004600000000000469ec04fa0002f48000000000000000138c1ef0001728000410268902000010500000008b2644000124400000000002387643823d99568
  | 16 => 0x2e27a8392a8040001761880000c041ed40711940008150d6823c4ce00002d974d2e61d51431ec8480a33000178800023d1f90000be652034a24104ba7c30e61c2c55015a134800000000019e0000000a1300017490b039e4df81709f42de4b82444260a094a797400000d005480001d4000000000030ca3c0589cec0002b3000031c00000000004cc5721a91e58dd8aae5b4221921c000a182d48fb907e8522d19a4c00026840a05946a04f400014dc00000000008dc00000039c910848a0c317a0000ea40004a308a937c0000002064a6484c00015c00005470000001224608000000000000000000011d20fd15200700005254e3a0280d80002b918a89a400034884c800000000000000000002aa8000eca0000a780000000003d2800000042752817ac0000002518000b861ec00ea17c5fe692000171c0003b103580014aa000000000000089d0000000f8a6a926f00000000001239714c7400000000000003240000000000000101800086400000007700005303c2a630b3e5420000000000581000127d0c800038900000001ce000000094400025c13e534c0000000d48000000000000000058300000000005892d880000005c401228a40000000001ad8cb457f000087065691b000274d14600000000000001f5458800032051000020300000003e8000038e9ca47d219801c7e62899ed00009250631f445b20002fb8d2ceb02e11e68001378a074ab92bc9d083c00026940000000001ed42506ba0000000000000000131017e76800000007c40000000e589e03b900000003ec73e2871590b7e8630f8a3b89b61e800000000000000000e142ba354005800000000000000b883a0004160000daa937000000105e3d73a70ed4bce9862a20d980008e500008908580003b38000dec010478964d31a5410000000dde4140430b8c00000000019a800000000000005aa0002eba4b40243b408d80011ea00000000004ee00000000000000003a6000000043c42e9e6045875d098800014400000000001840000001658000540000000012407100001c837c1490000c7400000018580000005a01909fec0009080000e982e000012180000007c800000005f400039d20580e600014d07a40007dd000118c00052f0000dc8a48000000000052a7bd1ea80012d622d0cd8a74d8c00016200000000000001cfc00000045005ec0000000001a1800083e0161af00000000a68ef8a3c826466a5740005fb1c980000000000000000000344000042000000000000000000000001f70d640001c18a587ea55d2d7800000056200000005825903fd0c48000a3f1c7800000000049a858457097e336000127c9682c40854c9a0002838760b541ae4ba80000002632f889782f42783b800a84f20000200a2549021700013609ac260000000050427b3800000000000
  | 17 => 0x641180009a89230000000bb494823929013466962d68344380a4e2dc8000424824269800000027120999cc0002b508a8000000490000192906e8eb35880013d00003b492314400000000000000000000000124e8f42f31300b8216420b80004504ca00020d4000839491055c5220004fa800143471c000000000000002400000001fc191800130400000000000003a9000000000067a000031400000026f80000008e8000000000041604090b86c698f0758c700000000002908000000000000098e6bb46e800032c7134f820e000061b0000000ad400017780003b4856000000023c341469000127633412880011f00140cc1e581b600021f21447a219d4f6a58853e84a4b00eb8702000103185920a0001760000c702702cc825d0c2936425a41c91269018c814c3e68d503a8b9545c8300021d6460a6b414c0e2400003d02f80012e40002efa7086948cf39e113cc128124b4865c0000000000db80000001000000de447900021543046eb000039c0008c700a8000ab297800018e40000001c5000136e3de4d79ce0afa0c420e0dcc7109ee000000029851b0000a8c2c60005139634000470000225800035e1b695e4606756000000133646f4bd1d182aa313000000000030e0001f4d4600000000258f6e5a403d2638d720000001d20000571481959c9c24960c01bb097873417d8e1944aa3844f0bf0d7e8700b101291247621129eed406a1518424347587a12728dc4eec57809e1c413883691de0c5c1040bc0000354fa43c43e781149546552cd9c34b2490f5168000f6c348507000066200018d88ec00074750b800000000000013a8f0c53a39317b800000000000000861ff02e800075473d000000015800034f80000008ce000000000000000021d800063e0000000ec22dc18a01f4cc207e0000aacb9a1aa000243878a00d3ef883c4e64c10bf939073e92423e00002220282b58000ca67fc00000000fe11f1888d092a600023b084c7fa000000037d0de00000000000000000001be81b44bd3ca23f400000011b25500006674361b0c9ee70951114b400012444e1fb42b67814ce278800053617c1420000000000000000000000021a8cd0000000000000064e00000000006574d400000000000000000b643d93e50aa400000024c00000007a9266a68061a0b9000000114e4240001a2800000040e800000018b331800004654f0000098d4c63139117180009962640f992de6472fc9bf8cc885b15613b478e1ea09a00000001040001e2535c75c000040c06627f0ac800000057549420ec00000000000011925fd1bf800067c58c2d41f6c0000000000b4400083d00000007f486b079257cd16000433a7047e687a168262043c9a1000000012064f00000010b40001bd87480005ac00000007f69a90000cc80009c00c40b7cd1a2bf4ca818
  | 18 => 0x44e000000000000029c0c880010029190000000602000252800148e4fd37011cc3cea0f3921524ffa6330778bcc00007b49e8f2800000000002d4d0220d0000ce8d10a4b26704f48be0370340d9d110285000149d20217c000225ce5a038225000000000000000004fc00000018784906a300025fd43a48f0001d540984330001fa8834000000000059203c000000000025f06e185c34621a00000001641810380da06600c83f8211c0004a6369800000000000000013fc95c000000000000008c00011ce00026827a4f620002820000ba80a6229000000079900000000000000000000a24716323000110c7442ea800000000012092140001a11ce00000009ec000081c5b400001906bd3744ac07700005620002ae0000000017146990c8ce6b0162957c68a0000a31f194a4000000189000000000014440000003eb8000e34000000000051c00028b0798ed65ab4438000000400000000000000000000000000000001780000000515a2f40000003839e9000030400000009d88950f08d7c3bc0000cf8704c28000000000016c12f00000000005030000000a7000000022088f47910a197a116689f1619e7d164a324ac800009c6c941a052804475b0d30358bfc4584158fdc0125c00ac0bf881c97b00f1eb80000003d18954dd400004e9404cba0003bc82f40005b300010e8a9c01f4f50c1c5760005228000000000000000000000002f0000a4c26e454a5980003164540000bc80000000fad1220000002070a8a40c000054400099a2d70bf400057a131000028270652a000114461504e0000a5419e0278d70ce000000023dd3d67ab316286c0000004241cc098c1e429881040000000001b1d0c452c00000009f84a8000254800084900000000006ee40124253a272115b21f4f9289b1cd000145012b1801694f0e3ff42e12792ac77f37f800000000000000000000000000ab89ce00019c857905277c362a7e079e1441ca186408c1cf0550b486ae7da4499de0a56671000280095287400006f0c0c4d70458000d7a00000006c510077e0000964c7e7e4000154451449a359a554c0665209189d8a2800047b18d4000a1109326c43ee0000001650cc000037693640000001979df4392107000061c0000000831e100006691eb18100000002051fc400000003a215c61ea0a2b689609f6890230260400018c3f58000c5e5d848d05e104400000006e92e2000000000000000000002ac92a83252080000000003fc8ca800000000000013c000024ba6612605b80578000544a060000350b786650000000e521cd000000005200051222f05c41454d380007563370f80394b7453d2eea6cd1cc46628e03c01301db4e78af54202db02124844443644a88a94000000000000000062b00012508ee0003a984b54940002ee0000000000000000062a1c
  | 19 => 0x17a8018e5800000000d873a9b84790538000000000038c0006c8000173c618000342a1b800000015900000008752da8d647d28682bb1cb80004da0d00910000000000000000007c374119000067600000000000000000998b9200700000013ca90b0000000bbc0005289dc80004411c68000e6a000000000000016800007ac0000000ec80009743460000000b90a233a180007d023a0fd042800015400002207200de0000474d3c0002eb15784ea0000000000c0a7d500000001b00000000000a3a31a1bc0000e2888c1c91abc00000000000005186d72c5000000062827b01dcff084e4cea11146e45b0c49fcca6615334e9a007602902b282b8ce410e46d21180000fa4810000f3664b0001838000000477a8d80003841c60ff14720000001170fee945434800117e32e1501b5872200025f854813c0004e59b34cde2343eb2450adc18412d069d14a73722700000007bc412984949e6be40800002a04460000a3d0fe36a10c2458b8450b09c98990540005298b34c1834d33a8000e2e000000000000000048512cc0000670001b30d9492640495d0000a3526282f83900b31a385980000003df14f911c0004d1111036c9f92030520c845ec000000000000003104a45240000318000de000048a83646b05ed11c80580006e100000000000002748000000000000000000000032f0eec0c896d2b188c800010b50c9de84964051f892c93e80c900000004f80000001c9cc400fb36900006ac0001b7800000000000021e400000012900000000001f00000f74000178800000031f00002dc0005f00001644e180000000e9c3648c8000094ce640000001bec47c00040592d4b4c6d8000000097235a3b880000006da44200000000000001efc9866f70000000000000450a3fd30800012712f86c400024e00004c200035395ec77062333e87d086c97900000000002422ce0000000a442b0000049e000000000086e5b65068d4c0000252089598e8400051601244da00000000002be00000000000000003b7a5f010000000000000007e814a00000009890000000fec6581b580000000000000a9c0000000000000000a463f4800000038b0000000a3065b00027248aa08a00000000000000000000836702000292542c6d00001f381c49d5000000089200000024d00720cc08980000000000a024300004ae000293508a00000000000007ff00000000000004eda5dc6ea00022a272143800000000000005840000000fb20890002528000000236a884326000000000143e77500000000006fd3c9a46000000000000000009e6000033d30600000004500008ed00004307309850001398c982ea1be8000d50000000000000000000000000006f100017641d2a434ca172c00048a4ef000000000007a97d8d1c97d4eb1c612eca14225800118837a3a580
  | 20 => 0xe0a000258000000070f21c87e13fe4dd00005bcdf27e2214a4bc240a2f0001f100007ef212800078259e3e08000db22ee0b480000004ee002a6d400067b0c900009fc00000014300000000001d7800000000000005e061843ba2b04a012513211e0cc40e606500000005a207a10e0000000000178c00000019f80000002200001e9cfca4210c280014045f4000166800010017b907800000000000000002813181e3c1e67aa0000d30fce7ee305126c00021f3e626b50da88a1f28000d8405412b201c00000036e040852621d09a800000000000025b91f81b037a28986f80002649e0c00000000008c46fc6102048e38e9e30a00003fc1a40000001c205ec000000000130e40d000083800088d2be000060c60700008f0d389c3265800009a751000120d416000000189527e40f00000004b89b900025d02b80e41ec0840a9075f0001558ec00014030ba47c69201249884b2a0002d8000118a0570002390fbc00046023845d000000006e40006db0000744ea0000000000022000000000200004c217000000000
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x106886390d20082543b08690041a218c4348020e10a621a40106a064d85200836031ec290041a8d906148020d40c830a40106c3631852008360318c290041389cc6148020cc4a630a4010660531852008351218c290041a810c61480209c4ed98a40106a064cc5200836031e6290041381d83148020d40c818a40106c0630c520083a02986290041e010c3148020a18e4a98878850c7454c32c428a3a2a618e21511c9530c710a34e7aa0818852a72d5040c42953a6a410621529cf5208310a18e4a98870850c7454c328428b39ea820c21499cb5410610a4ce9a90430854673d48218428c3a2a618421521c9530c210c1cc9316a68860c641885344287396a621a21451c45310d10a30e0298868860e6310f524428739ea819221439d3530c910a88e229864885487014c32442873a88619221431d4430c910c1cca218648860c6510c32443182a4c198a219414e60cc510cc0a5306628851673d50314428b3a6a618a21519cb530c510a2cea21862885147510c31442a339ea418a21c110f520c510e08862906288546750c831442a23a86418a21c1d50320c510e08a8190628863054987304432829cc3982219814a61cc110a34e7aa0608851a74d4c30442a5396a618221541c4530c110a34ea21860885187510c30442a539ea418221c210f520c110e1086290608854a750c830442a43a86418221c2d50320c110e10a81906088713540c430443882a06218221d0d48310c110e80a4188608844c735885404287396a621821459c75310c10a34e1a98860841c7359052042873a6a619021519c7530c810a94e1a986408514735504104292392a820821341cd60104109c0e4b0082084b0745803104270392c018821491d15208410a88e6a9042084b074580210426839ac010821461cd5410010a50e4aa080084d0735844004270392c2200214c5d44110010c62ca20880084b0745843004270392c2180214a1d15208010a90e6a9040084b074584200426839ac210021585d42108010cc2ca10840084b274991100426939cc888021389ca6444010964e6322200869064d8d10042593a4c688021349ce63440109c4e531a20086536518d1004349b20c688021a41906344010ca6ea31a20086937418d10043483a0c688021b0dc86344010d80e431a20086306494d100432831ca6880218c1905344010ca0c629a20084b27690d100434831c86880212c1d84344010d20c621a20087105310d1004350326c488021b018f6244010964e931220084d2739891004271394c488021a8d906244010d40c831220086c3631891004360318c488021389cc6244010cc4a63122008660531891004351218c488021a810c62440109c4ed99220086a064cc9100436031e6488021381d83244010d40c819220086c0630c910043a02986488021e010c3244010
  | 1 => 0x310c3c021e6418861649d2320c430b22e919062185c2728c8310c269bb2641886154dd5320c430b26e89906218590744c8310c2e13986418861b098c320c430e84a61906218782430c8310c3c0218641886164dd1650c430b20e8b2862185c372594310c2e0392ca1886154dd5640c430aa0eab2062185c372590310c2e0392c818861a4590640c4309a6ecaa062184d076550310c2e1b92a818861701c9540c430e22a82a0621855375588310c2c9ba2c418861641d1620c430d82c431062184d376548310c2c9ba2a418861641d1520c430e82a429062184d376508310c2683b2841886154dd5420c430aa0eaa10621878142108310c24c3a2c790861261d16388430934e7b22421849a74d8d210c24d3b08690861261d84348430c36ca21a42186186510d210c325b286490861921943248430d16c81924218688640c9210c329b286290861941943148430d26c818a4218690640c5210c24d3a6c610861329cb63084309a4e3b18421856075484210c2d03a24210861701cd2108430d80c6908421878043484210c28a38aa621e41431d1530cb20a88e2a9865905147454c31c828d39ea8206414c9c75410320a28e2a98871050e73d50428829338ea821441451d1530c620a30e8a9861105507154c308830b324c3a9a41851906114d20a2ce3a98869050c7214c43483142a4c1992419214e60cc920a1ce7aa0649050e74d4c32482a338ea619241439d4430c920a18ea21864906166310f514832331865a8a41c110c32d4520ac4e1990a290704430c8514828b39ea818a41459d3530c520a2cea21862905147510c314830b3288618a4185194430c520c8cca1906290644650c83148383aa06418a41c1150320c520c50a931660906485398b3048331310a398241469cf540c120a34e9a98609055271d4c304828d3a88618241461d4430c120e16a81906090708540c830482a939ea218241c410f510c120e8065a8860907104314430483a0190a218241549d4310c120aa0ea1886090713540c430483882a06218241151cd6115020a1ce5a98861051671d4c430828d386a621841431cd5410820a48e2aa084104c873580420827038ac0210412a1d1600c8209c0e2b00641051674d4c31082a3396a618841549c3530c420a48e8a8842105447354421082543a2c010841321cd6008420a30e6aa0801053071550400826439ac420041381c56210020a52ea21080106296510840082543a2c418041381c5620c020954e932240104ca73991200827138cc8900412a9cc6448020d10c9b1a40104aa7498d200826539cc690041389c66348020c96ca31a401068b6418d2008344320c69004192dd46348020d16e831a40106887418d2008361b88c690041b01c46348020c50c929a40106486394d2008314320a6900419218c5348020954ed21a40
  | 2 => 0xa821861641c55410c30b16e4b28861858872594430c2c9b8aca21861641c56510c30c32ca328861851b75588430c2c9b8ac421861641c56210c30d12c4310861851b75584430c2c5b92c221861621c96110c30d22c2308861849a7610d520c34821ec2a9061a410c6154830a50e8a90a41870843548520c2b038aa429061341c563d08309a0e2b1c84184d271d8d420c30db2886a10618619443508309a4e7b0a841869043d85420c348218c2a10614a1d54210830b10e6a1084185a071508420c2e138e8799061a490e618c830d208730c641869043586320c269388c919061a4992618c830d22c930c641869264586320c24d3b0869906186d94434c830d2087b0a641869043185320c2c5ba26419061621d1320c830b86e299064185c0714c8320c24d3a4c419061629d2620c830b12e931064185c271988320c2e0b8cc41906162dd1520c830b10e8a9064185c371548320c2e038aa419061325da420c830a96eaa10641868864508320c2e1b8a8419061701c5420c830b84e3a1864185c171d0c320c2c539c861906132dd9430c830a96eaa1864185c37150c320c2e038a8619061629cc430c830d14c6218641870a5310c320c2c5ba2ca19061621d1650c830b86e2b2864185c071594320c2a5baac819061521d5640c830b86e2b2064185c071590320c344b20c81906132dd9540c830990ecaa064185c371550320c2e038aa819061c2550540c830a96eab08641858b74584320c2c43a2c219061b0584610c830934ec21aa21868843d89510c344218c4a8861329d83254430d16c8192a218688640c9510c2983a2a228861c410d5114430ac0e4a88a21874032544510c264392c7a0861321c96390430994e5b1a821861b6510d410c30c32886a0861329cf6250430d1087b12821868843189410c2653b064a0861321d83250430c96ca1928218648650c9410c2983aa8220861641cd4110430b40e4a08821878032504410c2e13968798861e010f32cc430b24e91966218782430cb310c3c02186598861a290e628c430d108731462186884358a310c3453266518861a2990328c430d12c819462184ca72192310c345324c518861a2592628c430d14c8b14621849a7610d310c30db288698861a210f624c430d108631262184ca760c9310c325b286498861a2d90324c430d10c81926218593744c4310c2c83a2621886170dc9310c430b80e4988621849a74984310c2c93a4c218861645d2610c430b84e530862185c172984310c2c9ba2a218861641d1510c430b86e4a8862185c072544310c268bb4821886154dd5410c430d20c8a0862185c372504310c2e03928218861709cb430c430b82e5a1862185927390c310c269bb2861886154dd5430c430b86e4a1862185c07250c310c2c93988618861a498c430c430e24a6218621878243cc8
  | 3 => 0x8b6150040d26c630a8020690631854010351b10c2a0081a81886150040964e630a8020632531854010351990c2a0081a80c86150040964ed98a802069063cc5401035031662a00812c1d83150040d20c618a80206a0620c540103c019062a00818a9506250330c64a830a819852a72d5040cc29938ea820661469cf5495330a54e5aa4a99853271d5254cc2953a6a529661589c75294b30a56eaa1085985887350842cc2d038a8421661a410e618cb30b84e3a18659853274d4651cc2b1396a328e614cdd54110730b20e6a0883985a07250441cc3c02186598e61a210e628c730d14c819463985c272d0c31cc3c021e6418e61649d2320c730f04861906398780430c831cc2b1baa4210e61681d12108730b80e6908439854671d0e528c30b2a4c319461519c4540ca30e0887294a3187044354a518c3832a06528c61c15503294630a8ce5a1ca31870443cca518c28b3a46528c61c190c3294630e0886194a31870443949518c3832a064a8c61c110c3254630e08872966318706540cb318c3072a4c518c6183992528c630e0c87290631870443948318c38221aa418c61c1953320c630e0ca81906318705540c8318c2a3390a818c61c1952520c630e0aa9290631870654548318c2873a8861926183994430c930e0886196a298704430c8514c28b3a88618a6185994430c530e0887a90629870443148314c2a33a86418a6191994320c530e0ea81906298704540c8314c286392ca21861451c56510c30b16e4b00861858872580430c2c9b8ac021861641c56010c30b16e8b00641858874580320c2e1b8ac019061701c5600c830b26e8b00621859074580310c2e1b92c018861701c9600c430c1cc8194a018616640c6500c264392c720061341c56390030c92ca1948018651650c6400c265396c6a0061349c76350030d1087b12801862854189400c344218c4a0061329d83250030e10a8192801869043d85400c360196c2a00618c1506150030d208630a80186c032185400c2693b062a0061c41503150030d86c418a80186c0620c5400c294392a8200614c1c55410030a32ea21880186884398a300c34421ac518061a2990328c030d12c8194601869043986300c360194c318061a410d618c030d8064b0c6018692640c6300c348b206318061b0988318c030d82c418c601868843d89300c344218c498061a2d90324c030d10c8192601869043d85300c360196c298061a410c614c030d806430a6018693640c5300c3483206298061b0d88314c030d80c418a60184ca73d89540c26939ec2aa0614a1c95415030a60e2aa0a8186c262987430c360b14c3a1861b098961d0c30b16e4a1886185887250c430c2c9b8a8621861641c54310c30b14e5320861858972990430c2c938cc821861645c66410c30b16e4aa0861858872550430c2c9b8a
  | 4 => 0x86e0aa06418dc070550320c782aa0a81906351dd5600c831b0ee8b006418d8474580320c760b00c019063259d84354031d0887b12a018e8443189500c6633b064a8063a1d903254031d08c8192a018d3074540500c78821aa028063581c95014031e8064a80a018d187054c43c86863a2a619643521c1530cb21a2ce7aa08390d3270d5041c868c382a621c43439cf5410a21a54e1aa08510d147454c31886a8382a618c438699260d4d21c30c8300a690d1a70d4c43487122a4c3992439114e61cc921a1ce7aa06490d0e74d4c32486a5386a619243439d4430c921a18ea2186490e245498b314872229cc598a43459cf540c521a2ce9a986290d5270d4c314868b3a88618a43451d4430c521e0ea81906290f04540c8314870d31887a82439298c32d4121e1086196a090e52630c7504878821863a8243d00c831d4121ac4e3990a090f08430c850486b13966228243c410c3114121e8064188a090c58735805408687396a621843459c75310c21a34e1a988610d0c735504208694382a821043311cd61108219c0e0b088410ca4745843208670382c219043451cd5410421a60e0aa08210cc4735884108670382c420843495d44210421c4aca2108210ca4745883108670382c418843299d2644842198ce73224210ce2709912108653398c890843a1193634842194ce931a4210cc67398d2108671384c69084391d946348421d0ec831a4210e846418d2108723ba8c690843a1dd06348421d08e831a4210ec37018d2108760380c690843891925348421c88c729a4210e246414d2108722318a690843299da4348421d08c721a4210ca47610d21087423188690843c114c4348421d40c9b024210ec063d812108751b20c090843a81906048421d86c63024210ec0631812108671398c0908439894c6048421cc0a63024210ea2431812108750218c090843431c95310f40a28e2a9887a05447154c32d02a2392a618e81511c5530ca40a88e4a986320646629875350322310c229a818614e6090d40a1ce5a9886a051671d4c435030731887a92814a9c24314940a8ce3a9864a060e6510c325030b31887a8a819198c32d4540e0886196a2a05327090c51503822186428a81519cb530c540c2cca21862a054673d48315038221ea418a81c110c520c540a8cea19062a0544750c831503233286418a8191194320c540950e4b0086204b071580431028639aa421081491c55210840930e6b0084204b071580421028a39aa220881491c95110440930e6b0082204a872580411030db28c6a008186dd46350040d16e431a80206887218d4010349b88c6a0081a41c46350040c30c729a802068863d894010345b18c4a0081a218c6250040954e6312802062a5318940102553b664a0081a218f3250040950ec1928020688630c9401034831ec2a0081a81
  | 5 => 0x8e904398232cc6e138686196634c9d35094331ac4e5a84a198d4a70d0e528c70d2a4c119463529c0540ca31e1087294a118f084354a508c7852a06528463c25503294231a94e5a1ca118f0843cca508c68d3a46528463c290c3294231e1086194a118f0843949508c7852a064a8463c210c3254231a1cea2186498e0e6510c324c78421865a8263c210c3214131a18e4b288618d8772584430c6c2392c22186364dc16110c31b20e0b088618d8774584320c6c23a2c21906370dc1610c831b80e0b086418e0e640ca510c662392c720863341c16390431c8aca1948218cc672d8d410c669386c6a0863a110f6250431c48a83128218e8443189410c6633b064a0863c11503250431d2087b028218ec032d81410c7182a0c0a0863a410c6050431d80643028218d2472550410c698382a820863455d44310431d08873146218e844358a310c7433206518863a1590328c431d20873046218ec032982310c74821ac118863b00c9608c431d0887b126218e8443189310c743b206498863a1190324c431d2087b026218ec032d81310c748218c098863b00c8604c43198ce7b12a818cd273d81540c692392a82a0634c1c15415031d84c53068618ec162983430c761312c1a186361dc94310c31b08e4a188618d937050c430c6c83828621863619ca6410c31b0ae53208618d9270990430c6c8b84c82186361dc95410c31b08e4aa08618d9370550430c6c8382a82186361dc96510c31b08e4b288618d9370594430c6c8382ca21863855946510c31a2eeab108618d9370588430c6c8382c421863a15886210c31a2eeab008618d8772580430c6c2392c021863a45806010c3192cec21aa418e9043d81520c748218c0a9063491d15214831e0886a90a418d6070548520c668382c7a1063341c163908319a4e1b1a8418e176510d420c70a32886a1063349cf6050831d2087b028418e9043181420c6923aa8421063611cd4210831b40e0a108418dc270d0f320c74921cc119063a410e608c831d2086b046418cd270192320c749324c119063a4592608c831d24c8b046418c967610d320c70bb288699063a410f604c831d20863026418d87744c8320c6c23a2641906370dc1320c831b80e09906418c9674988320c6c33a4c419063615d2620c831b84e13106418dc170988320c6c3ba2a419063611d1520c831b86e0a906418dc070548320c662bb4841906351dd5420c831d08c8a106418dc370508320c6e03828419063709c3430c831b82e1a186418d867390c320c663bb2861906351dd5430c831b86e0a186418dc07050c320c6c33988619063a198c430c831e0ca62186418d8774594320c6c23a2ca1906370dc1650c831b80e0b286418d4775590320c6a23aac81906370dc1640c831b80e0b206418e8564190320c663bb2a819063311d9540c831b
  | 6 => 0x310b07b28c6a108583dd46350842d0ee231a84216847118d4210b45b80c6a1085a21c06350842c18c729a842168463d854210b43b18c2a1085a118c615084294ce630a8421626531854210b4431ec0a1085a81876050842d16c63028421688631814210b51b08c0a1085a81846050842954e6302842162a531814210b132a0c2a16658a9506050b32a4ce3aa0859952a70d5042cca8739ea92a665499c75495332a54e1aa4a99952674d4651ccab1386a328e654a9d35094332ac4e3a84a19955270d0e518cb8821ca328465c410d5194232aa4e3a1ca11971043945508cac3b8ac421865611c56210c32b16e0b10861958870588430ca6238ac721065321c1639083298ce3b1a84194ca70d8d420cb4221ec2a1065891506150832d088630a841968843d81420cb142a0c0a1065a210c6050832a48e2aa0841952870550420ca86ba88621065a110e618c832d0886b0c641968843982320cb4421ac119065a110f614c832d088630a641968843d81320cb44218c099065319cf6155032994e7b02a81952471550540ca94382a82a065b098660d0c32d82c330686196c261583430cac3b8a8621865611c54310c32b16e0a1886195887050c430cac338cc821865615c66410c32b14e1320861958970990430cac3b8aa821865611c55410c32b16e0aa0861958870550430cac3b8aca21865611c56510c32b16e0b28861958870594430cb06b28ca2186543dd56110c32b16e0b08861958870584430cb42b08c22186543dd56010c32b0ee2b00861958471580430cb44b00c021865239d84354432d1087b02a21968843181510ca923a2a228865c110d5114432ac0e0a88a21948e7610d500cb4221ec2a8065a110c6154032a50e8a80a01970843540500cab038aa028065431c95310f41a30e0a9887a0d487054c32d06a4382a6194839298a60d4d41c90c4300a6a0e14539864350687396a621a83469c35310d41c1cc621ea4a0d267190c52506a5386a61928383994430c941c34c621ea0a0e4a630cb505078421865a82834c9c64314141e1086190a0a0ca4725844310658382c221883431cd5210841a50e0a908420c94735844210658382c22108385d946350441c2eea31a8220e877218d4110742390c6a0883a4dc06350441d20e031a8220e146394d411074231ec4a0883a1d8c6250441d08c63128220ca6731894110713298c4a0883299db3250441d08c79928220ca4760c9411074231864a0883a418f6050441d40c5b028220e93631814110748318c0a0883a8d886050441d40c43028220cb2731814110719298c0a0883a8cc86050441d40643028220e265418941cc7192a0c0a0e63499cb5410731a64e1aa08398d1673d5254cc693396a92a6634c9c35495331a4ce9a94a598d6270d4a52cc693baa8421663611cd4210b31b40e0a10859
  | 7 => 0xc00000069c34800000006c6644810dc750000a590d8991090bc8474dec1190604d845494ce547088a804c68c92c4204904d4da52105c4cbc6a52504a03b446859842c0585d8fbc4a90d51b8b98e7c988700d541dd148a3849d1bc860fdcbad134ce4e880383e058d18523cb14018fccd34e4090c6bcc9409c88cf880a853c0ece149f0244730e840246acc789e0c18d2841827c314ab0000000d48cf0a0400089cc141f82a8ed4dfd04c8f8f146dcb54a4c7245a90306d81c8cf50885a4db4d04790fc42c08ec6581fc828c55234d2481c3c8c5d1c8aa5070e1c268f54dbcca00008547b51511a0f0927c000000000f80000000a44d7c65526ca0c62ca18000000ddd1ccfe0270b7099418c87c5c11f50040000004c475400000048c00039c6140800004ccb38000190968ed9240000000000c802649cc0002ec2bcaa0f31094cec00072800c030070000001080101a0080280401201c0680d0360000b006000000010020000080380b00c104098030040000281a01c0180001203e008000040040000000100c0080e00001406c0b8070240000180401a0140001c000000008ae028074100070020000480a0040140c07b01a0040e80000e008030000020000000100a0080a00302603411017000090000020040240680e0140040180e004064018000000280301500e0000000003c01c05000000020000000080343000102c00c008070060040001001218c0382301e000038000020440e80802e0040000000e00c0b002000080050010021180080000000400014000014078040040000080406e0040a00600c0000001a00001c00802012024010000020001500800c05c030010040040500005400802800002000010000080040a8090020280180900a000000050000040f80200e0240000004c0181a80d0240b00080001a0580f0010000080200003200402000002020000070000180100a01c0000480000e00400001018000000010280081f80900e014000010000000080001a0240c80500204002800002000068000000880000000002801804002078008040280100f0030060200f0090140000181200200c000010100000002200402801011008000000030140041482b00a074090150000000180b00a0300f00900600c018140140240180a0060081600101a00c07810000024008400000d80080500800003005002004020000980041200a0200140bd2671d4a5290e95386a529487499cb5194643a64e1a8ca321d2a72d425090e9938ea128487491c55214843a50e0a90a421d24725445110e98382a2288874a1c95014043a60e2a80a021d147154c43d0a8c382a621e859498660d4d42ca0c2300a6a160c5398a4350a8b38ea621a85469c35310d42c2cc621ea2a15267290c5150b0d31887a82854a9ca4314142948e2b1086214a8705884
  | 8 => 0x340010d0c30f450f84500080008d8ba0b78000ae0001098d9c504740974e78b3c3844b901431906c5dcdf1278d7120d2a033101cd00a08630a6cf28ab400108c21c7f4d64a68000be905479400000117cfd4f6045cac04dc594a74908875040e70810f48d9883c6885d4000d882544ec000534014fa84e01640000890b43686e812088861c4a44091a8bc42f86480fce6876c000c0ca2c0004b0ccc79813d1c09802c88c4ce11e4ce91b40648fd1e05f4784eb434cb050ec91cafc36cd1873c0a4b0c959044734f50400b642e055c67c4bccb4eb09d8e801441b4168140470b9cf6c610484dc926404400008c6e0290fe8a88c68cc0fc8001064148d84f34fb47c4a98e94000000818e4849905d1d09c11c40b8934c8c3b8b804e4da01b883875ca3c7d0f79130c4c0001ecf240010a000000000115c3a4600e10000e05154cd044c378f3c0010c911024d1d48908b0000de4c1d2889b4000c6c2389b902d2540007c0d682b47c89ace5840cd085b49e8000e381b1180000000000000000000868d1c3ac001164b10780004c603fcd5864c50cfb8dc400000029c2040006340000003940008a00000000dc8b4200000ca8000b84ae8930c040000c0590000000a8c5d121ca4857400117800003c8f4b08000cb056065c1d40006f46c0d79218938bd49bc7e8c591e8000b44e2800025815c000054c5085c041008390160d40310824ec40008cc001290570f68000000bb80009f4000000984000c988940002948a48984f4e606cce34334f58884cf9100d3c444000c707790c000013800054d158f9cda8f40dc0ea4000000ee00b40000e8000000000f38f9116056c0100006a80005cc001274ecc00119443cf103e86ed038ebc6603407180f9108f8c7a0645188b5846116c9a88e09b0604000f5c77c60c000a208043201f457cef0fd8efc00128469800119026c8d43d44c00c47b10bcf7c4c8dac08400032cc440000011746a0d5125805c0311141049103551702dcb1c7144d0000388e4c7a4578000914cac114df8c091ec23452909c274229198bd00006b8de82f40e4a1069000000095c0002d00006c496cb40fc06084407d5074b500e01280000000007ec0d40008412000002b8dcc184000edc000000af45200000005b0d946380d0ee4510178b4882c694a601300007cd124bcc00022450086c0005accd51205140001c0d7417ce300010ac31c7fc000650000a5c960370000000000928000000000800f64e081ac54422cbdc6745b8be45f01944e89fc58471ca70c488c8478380be0214398f986707bc978ea811cf0400034528c8086411f83cc7642d51d8cc4cc8eb90c400000097037c6683010e46800007b8acc954bd802c56833c550000b30cdcdb0488704b606e425c5a0000bc0ef40783c00006d44ac3a87d8bbc174bf0d90f84ff8000
  | 9 => 0x788001220c900003580cc000aa80003d80000000007dcf180000003049a0b9493ce90774a94c741d06783f8d8cd2c000000000000770ff0870d5c0008200a0000000000e8c3605ec0004fcb28a9000028d280000ba45592302cca003f074466cfac54830c59d00d128d104648bcb900f11450b07586f10a8c2c7f0a35068000060a30814000d4d26097d0f0329080000000430710e210a428522cb341987acb68a512a40002182200006c8c002f06f820cad12048448304b42300c8458ab8b4c3bca1c3641549dd1fced0f1c16c01c000e44524001024dd478ca9d050e9d000bfc540fd0000b882ac00098c000bf4000624f0c80c000000000d14e24000fe4564d6c035020ff49d03ec00051c91812d0cc1352941a4580000050a54abc2e472c964eac000000091078ae4508850d6124c000000094e00251084998a84c2838c70c5888e44240d8720ad82c46b119d0347680010b80010f4c9d168749118020b005c89503b02a0f00db89c4cd8848c38f4c1d8924c64cfc8b8834339268375224554308dd87f84351a52a8684f205bc47c74c6d129c9f8b6cd20100538af8f951f08c10284152700008dc1a800010c404000000000240280000d80000adc180f708d08590101cd14c8f01f0fa0000cb85f8448c24b207a818920912cfa507caecaac23cbece502983a03f5138de0438a14ee85e01bc3e40000009c8e2ce18000001104d0c1100006180002d80002601c446c2090e00011b0e740000006fc9204285301252980007e4a244106287600000bd0190580982108647e04f0000a640001e82880000000010fcbf8000af0e9800041c00125cac800014c9a4bb41e000111c5e4ec0ad4000b7c07c5e8df487800000000027800000088079c84c0009483c4000c843d123903cb2cfb02b015099c19c0b063c9d4d44e6d0e8a40ca4e0c940028e3c4943241a0fec4f8a781e4b74ffcd3894435c8e80acba83dc070b8d18d10ca80ea0a7c048d305fc0009049e452c000000000a28ac4e5cdd0ec8bb0ef92289ed248f74170eed244248620108c88b25215048e648ad1dc2fc7380f4c202e8c11140c3c350000f2c5180000011ac6b4b1913cc402a4900b5c158074068000000c7cc
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x11000010860f179e071699181980200d139289800c000d8005828a9e90048f81158e8b1a1d1c8000000e0a14971a92131d80001f0c9b9f880383000b9180150916041c00018687888214001b052080988906000421a040c101001440310005050a08081c80711c06350842a80805846110c32a80815806010c32d00431c15114432d00431c55014032c80721c06350441e00540c86050431a80805886210c31a80825806010c31d00431c15214831c80641c1420c831a0485590640c831a8080590640c831a0486550540c831b0080550540c831a8084580600c831d00431c95014031d00740c95014031c80741c06348421c047614c4348421e005310c6048421c80721c46350040a80860c83150040c80760c83150040e00540c86150030e00541883150030a80815886210c30a80825846110c30d00431c55214830c80641c5420c830a0885590640c830a8081590640c830a0886550540c830b0081550540c830a8084584610c830d00431c95114430d00740c95114430980870c94110430d00750c94110430c80641c9410c430a1085590640c430a8082590640c430a1086550540c430b0082550540c430a8084588620c430b0084548520c430a8086508420c430b0085508420c430c407518d2108430c807418d21084309808710d2108430d007510d2108430c80741c46348020c087614c4348020e005310c6148020c407614c3148020e006414c3148020a808610c3148020c807610c3148020c80741c86344010c107614c4344010e005310c6244010c407614c3244010e006414c3244010a808610c3244010c807610c3244010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1140
  | 4 => 2647
  | 3 => 1195
  | 2 => 66
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (i*5) 5
  | 6 => packedAt s4K6 (i*16) 16
  | 5 => packedAt s4K5 (i*27) 27
  | 4 => packedAt s4K4 (i*38) 38
  | 3 => packedAt s4K3 (i*49) 49
  | 2 => packedAt s4K2 (i*60) 60
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (880+((h/16+packedAt s4K6 (768+(h % 16)*7) 7) % 69)*7) 7
  | 5 => packedAt s4K5 (34960+((h/380+packedAt s4K5 (30780+(h % 380)*11) 11) % 1655)*12) 12
  | 4 => packedAt s4K4 (112052+((h/882+packedAt s4K4 (100586+(h % 882)*13) 13) % 4227)*13) 13
  | 3 => packedAt s4K3 (62933+((h/398+packedAt s4K3 (58555+(h % 398)*11) 11) % 1435)*12) 12
  | 2 => packedAt s4K2 (4114+((h/22+packedAt s4K2 (3960+(h % 22)*7) 7) % 80)*8) 8
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffdfe0ffffff801fffffffffe03fffff0fff
  | 1 => 0xffffefff07ffffffe007ffffffffc07ffff0ff
  | 2 => 0xfffff7fff83ffffffff801ffffffff80ffff0f
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | 5 => 0x7bffffc1fffffffffe007fffffff01fff0
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xffffa03e108425f684a92a5896e815ab970777
  | 1 => 0xffff9042f1084a92bda24ca92b6ad035ab70bb
  | 2 => 0xffff888427909324c93769324dad5aa0cdbb0d
  | 3 => 0x10842211c4711c471c471d1a34670ddde
  | 5 => 0x610843de0781e0781f87e1e3c7881eee0
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xe800e80080008000e800e80080008000e800e80080008000e800e80080008000e800e80080008000e800e80080008000e800e80080008000e800e80080008000, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_12220
namespace PEqualNP.Outside.L_meta_12220
open PEqualNP.Outside.L_meta_12220.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x502c00358000001a100002e38e983e00020183c0242a18000440098000045000000009006802300000110000f000001708000801c5eb539642000004a002805600014000082900a8da60e00012320600004040818000000000c00080ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32ef32fe32fd32fc32ec32ff41fe41fd41fc41ff31f731fe31fd31fc31f431ff21fe21fd21fc21ff40fe40fd40fc40ff30fb30fe30fd30fc30f830ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x61dc320c3d86418730c830bf288617d510c3ee6218778c430ee18861f4310c3a862185f94030fda0061fa400c3f280187e10030ef98061fa300c3ba60187e4c030fdaa061fa540c3f2a8187e15030fd298617a530c3b4a6187ed0c30eda1861fa430c37486187e50c30fc21861b8430c3b086186610c30fda9061fa520c3f2a4187e14830fda1061fa420c3f284187e10830fd99061eb320c3f46418768c830fc99061f8320c3b064187a0c830e419061fb510c3f4a2187e54430fc28861fb410c3f482187e50430fc20861fb310c3e662187e8c430ed18861f9310c3f06218760c430f818861d0310c3f642187e88430fc90861f8210c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c837c87906f10f20f799641ec32c82fca3905f54720fb98e41f431c83f681907e10320fd98641f830c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c538837c87106f10e20bea9441ef42883d885107bcca20f6194417e51882faa3107dcc620fa18c41ee21883d843105f94220fd98441f830883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20df21a41bc43483de64907b0c920bfa8a41f751482eea2905f14520fa28a417451483ee62907d0c520fd98241f830483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20df21841bc43082fca4107bd0820f621041ef32083d864105f94420bea8841f731083e862107b88420f6108417e50083f680107e10020fd98041f830083de40107e88020f690041f920083d240105fd5310bf2a6217d54c42f8a9885fd4f10bf29e217d53c42f8a7886f90f10de21e217f52c42fca5885f54b10be29621ef32c43d865887dcc710fa18e21fb40c43f081887ecc310fc18621fb20c43f041885fd5210bf2a4217d54842f8a9085fd4e10bf29c217d53842f8a7086f90e10de21c217f52842fca5085f54a10be29421ef32843d865085f54610fba0c21f441843ee63087d0c610fb90c21f421842fca1087ecc210fc18421f710843f621085fd5110dfaa2213f54442fca8885f55110be2a221bc5444278a8885fd4d10efa9a215f53442fca6885f54d10be29a21dc53442b8a6886f90d10de21a217f52443dea4885bd4910bf292217d52442f8a4887b14910b629221ef32443d864887dcc510fa18a21fb30443f060887ec4110fb082217f54042fca8085f55010be2a0217f53042fca6085f54c10be29821be430437886085fd4810bf290217d52042f8a4087bcc810f6190217e51043ee82087d10410fb98821f431043ee42087d08410bf28021fb40043f080087ecc010fc18021fb20043f040087dc4010fd08021f510043f220087c44010
  | 1 => 0xe50c86faa190dfd5221bf2a4437d54886f8a910dfd4e21bf29c437d53886f8a710ef90e21de21c437d52887de8510fb10a21f799443ec32886fca310fdcc621fa18c43ef21887ee4310df94221bea84437f544877ea890cfd5121bf2a2437d54486f8a890ef151219e2a2437f53487bea690d7d4d21bf29a437d53486f8a690f714d21ae29a43be43487788690fbcc921f619243f731487e86290fdc8521f710a437f50487f6a090ded4121be28243f850486f0a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610ef90c21de218437e52087de8410fb10821f799043ec32086fca210fdd0421fa20843f731087e86210fbc8421fb10843ed21087ea4210f948421bf280437d50086fca7a05f54f40df21e81bc43d02fca5a05f54b40f799681ec32d02fca3a05f54740fb98e81f431d02faa9205f94e40bea9c81be439037887205f94a40bea9481be429037885207bcca40f6194817e51902faa3206f90640de20c81f731903e863205f94240dfa0481fb40902fea6a077d4d40afa9a817c53503b8a6a05714d40df21a81bc43502fea4a07bd4940b7a92817c52503d8a4a05b14940f799281ec32502fea2a07dd4540bba8a817c51503e8a2a05d14540fb98a81f431503f680a06f90140bf2a0817e53102faa6206f90c40de218817e52102faa4206f90840de21081ef32103d864205f94440bea8881be411037882207dcc440fa188817e501037e80207e90040dea0081f9401037280205fd5330bf2a6617d54cc2f8a9986f90f30de21e617e52cc2faa5987bccb30f6196617e51cc2faa3987dcc730fa18e61fb40cc3f481987e50330fc20661fb54cc3f4a9987e55330fc2a661fb43cc3f487986e90f30fca1e61f843cc37087987ed4b30fd29661f952cc3f0a5987ed0b30fd21661f942cc3f085987eccb30f599661fa32cc3f265987e0cb30f419661fb51cc3f4a3987e54730fc28e61fb41cc3f483987e50730fc20e61fb31cc3e663987e8c730fc98e61f831cc3e063987ec8730fd10e61f921cc3f043985fd5230bf2a461be548c27ca9185f55230deaa4613d548c2f8a9185f54e30efa1c61be438c37887187710e30ce21c617e528c3dca5185b94a30bea9461ed528c2daa5187bcca30ef19461dc328c3d86518730ca30bf28c61f6518c2eca3185f54630faa8c6175518c3ee6318778c630ee18c61f4318c3a863185f94230bd28461df308c3f661185fd5130dfaa2613f544c2fca8985f55130be2a261bc544c278a8986f90d30de21a617f524c3dea4985bd4930be29261ec524c2d8a4987bcc930f6192617f514c3eea2985dd4530be28a61f4514c2e8a2987dcc530fa18a61fb304c3bc60985fd5030bf2a0617d540c2f8a8185f94c30efa1861be430c37886187710c30ce218617e520c2faa4187bcc830ef19
  | 2 => 0xcaf0a0995fd5032bf2a0657d540caf8a8195f94c32efa1865be430cb7886197710c32ce218657e520cbde84197b90832f6a1065ec420cbbe64197b8c832ee99065ed320cafca2195f54432bf280657d500cbdea8197b95032f6aa065ec540cbdca6195b94c32e729865ef430cb9e86197b90c32d721865ed430cbd886196b10c32e6218658c430cbdea2197b94432f6a8865ec510cbdea0197b94032f6a8065ec500cafca7a0df54f41df21e83bc43d06fca5a0df54b41f799683ec32d06fca1a0df54341beaa4837e53906faa720ef90e41de21c837e52906faa520ef90a41de21483ef32907d86520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077c86a0ef10d41bfa9283ef52506dea4a0df14941f6292836c52507de64a0fb0c941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53106faa620ef90c41de218837e52106faa420ef90841de21083ef32107d86420df94441dfa0883f6411077a8220fd50441daa08837e50106faa020dfd5331bf2a6637d54cc6f8a998ef90f31de21e637e52cc6faa598fbccb31f619663f741cc7ec8398fd50731fa20e637e50cc6faa198fdd5331fb2a663f554cc7e8a998fdd0f31fb21e63b643cc7ea8798fd10f31da21e63f752cc7eca598fd54b31fa29663f742cc7ec8598fd50b31fa21663f732cc7ce6598fd8cb31fa99663f432cc7c86598fdd4331fb28663f550cc7e8a198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31efa1c63be438c7788718f710e31ce21c637e528c7dca518db94a31bea9463ed528c6daa518fbcca31ef19463dc328c7d86518f30ca31bf28c6376518c7be6318fdcc631bf28463fa508c6f4a118df54231fca846379508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c77c8698ef10d31bfa9263ef524c6dea498df14931f6292636c524c7de6498fb0c931fb98a63de314c6fea098fed4131bda82637c504c7f0a098de14131bfaa0637e540c6faa818df15031bf29863df430c77c8618ef10c31ee218639c430c6fca418df54831f799063de320c7b86418fb0c831e6190637e510c7ee8218fd90431faa0863f4410c7be6218fd8c431ee98863f5310c6fca018df54031fbaa063f6540c7eaa818fd15031fb2986376530c7aca618fdd0c31eba1863f6430c76c8618fd50c31fa21863b4430c7a88618e510c31fba9063f6520c7eaa418fd14831fba1063f6420c7ea8418fd10831fb99063e7320c7ec6418f58c831fa99063f4320c7a86418f90c831e219063f7500c7eca018fd54031fa280637f54c86fca990df55321be2a6437f53c86fca790df54f21be29e43be43c87788790fbccb21f619643f741c87e88390fdcc721fa18e437
  | 3 => 0x80280100000000000008004048020040040480000800c04800004010128010000040200300004c0000a002000008090000000f00f00001800015002004008040000100100401a09000800000018068040020041b8030020040100100202400003000044000010000080200502401c00800006000000090000100100201801c020120260140000300200c038030000080201201c00000002006028000010020100180101c00c0100600000800800000078000090020040500000a00c00800004000080030020000681303e0000401a006004030040080000000000a0040281102017402814000000000000020000080400000400801bf29687ee52d0edca5a1df54b43f6a96876d52d0efca3a1fd94743bb28e877d51d0feaa3a1dd54743bf28687fa50d0ef4a1a1df54343fca86877950d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df542439f29c87bf5290f7ca521ef54a43de29487bf5190f7ca321ef54643de28c87bf5090f7ca121ef54243de28487df4350f7c86a1dfd4943f7a92876f5250ef8a4a1fb14943b6292877f5150feea2a1ddd4543be28a87f45150ee8a2a1dfd4143fda82877b5050ef8a0a1fe14143bc282877e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea8087be5310e7ca621e794c43dfa9087be5210f7aa421ef14843dfa8887be5110f7aa221ef14443dfa8087be5010f7aa021ef14043bf29e857d53d0b7c87a16f10f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7c86a16f10d42f7a1285be4250afea2a17dd4542bba8a857c5150be8a2a15d14542bfa8285fb5050af6a0a15f14142fc28285785050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842d6a10857e5110afaa2215f94042bea80857f54ccafca9995f55332be2a665be43ccb7887997bd0b32f721665ed42ccbd885995f94732bea8e657e50ccafaa1997bd5332f72a665ed54ccbd8a9997bd0f32f721e65ae43ccbda87997b10f32d621e65ef51ccbdca3997b54732f628e65ef50ccbdca1997b54332f6286657f548cafca9196f952329f2a4657d548cb7aa9194f55232be2a4657d538cbbe87196f90e32de21c65dc438cb3887195f94a32b729465df328cbde65195f94632fb28c6576518cafaa3197d54632baa8c657e508cbf4a1195e94232bea8465f9508caf2a1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8996f90d32de21a65ef324cbbc64995fd4532fba8a6577514caf8a2997d14532ba28a657f504cbf6a0995ed4132be28265f8504
  | 4 => 0x8940e80327dc51224c1c600074a0de00065e23031a32286a3c25680da3105580001260000000001005cc6b446c3d249062a4f85b01ea0ae33a5487143ac1e05ac0002260006940000003ba2f24628a481414e0000001201060662e60000000dc0001ee8a00000007f413200000008200063c00034c0000000001380001f03b67947886245a20003fc3021f400029a8e08065a870e1848ce5e07907f066e5ae0840e28663e25ba4b23ea0142288e489c1b400015a3a67a04ce0002ea0cc1cc00000081200000015063e00064c43619c23630858e32a71271c0000006a27d68dc4a80001ae6da8226746920007e282e1d26f677c8b81fe74484c5aa83c54c6be1924c873477200000026600000000011055e6c249673e42e1703de7ec45c0008c861a0005a05060005941548ba17e15e5085001288568b00001940000000000000000000004540007c800074200034a36e4e26f28827325048024c200072400a5505fc0c20006dc6c64a08b617822400000026a4340000006c00000000000000005da18a6600004fa00079e45e00028c3cc2647da00039a50c6082ac0008900000000000006f45c842c4c60008c01c48d22c059000000000000021065846a00000000000000000068c0008e613000000028856a7104840007d814c0000000004c07d031e5e600000000052400000058888c5dc8c211800035c0006a66e88ac39045022c0002ee1580006228e23960003fa01237e71a0002460003e083e7e640e2b60000180ca0000000007800000005bc3386e00006d80002f00000003aa0006463fe7b84860004300003f40000000002fc69020e03c09401a74c4746321c26e681800060687e17c6bc4c459c7840000002500001560008625d40004a676860a4da0008442a66540965b87be1ba64a44819000021a87a1be80a00000000085e0000003ca0000007280fe0001ac2a874e36247870813e1dc21605e4080581c07861ca6a03e639c45a3dc44a0fc5545b440c5c43447c036a5566627661148d400026e70400052830e6146ca8005fa00002a008088050000080000701e0180080000001400000000004050090040040180700200c000000000ac008060220200080907a0000301b0000080280102c00c110000000000c0000020000280701001c0200301603402006000000098020000100380101a020000000060080580300a0100a8050040080000001a0140080b00000c008020000340080000a08c000010040040080000e0000000000001c01800002040000040040040180a000000000000000040080001c008000000180680682300a0000500201e004008000000100380201404803800006004000000000000000500200c0200600a008010040020100180000802000800002014028000060001200300000c0a0030020180000c01e0080e8
  | 5 => 0xd42c807406a43e4040883d041819e5a408e04c8324022e04946ae28289e00061e0a43c02b25920006666f80300005de4fe00000004a4a40a80000000004ca0ba0603f60540200007360008aa12400015c52e52689818e27a5e26300401b274800015254e2c456200085006e0003d40008b40a600026800009c0000000007c20780006ba0000003f20008248a223c11e3a88700002d438402637250a0000008cc0000ac60c7e42d80d200041200010a0f00000006ac8d80007780003786b27503a422a1d873001e5785828400a28540c000019802a00078a72c00073a0000d00000000004aa00000061c05252c8462d08201222d67924327bc4521d450e00085c09a0002b00005c610400023a8c644200089268200011600030c10e6a43480505421a04fc2220000004f667a22e00025c00052a2967d212e8741da3683a07f25101a854a4d468e5743325462d20004b430a79c0005360086863582600f60002a053282619a3a20700224144ea8488ae3862081d665027e3047d42420000004a27b24f40002c23be29253e08c00075846800000018c7221ce58454400413625800053428409e83070c7ce25e0000000000000000000000000000000007fa82a13436c55c00051a0004e600081a04614a4f07c634e2dc4ec00035a6ea2cc00038200083a0b460e3660003540004d27fe2447a67708da5401083f062875e2566d67f64b60ea0007c425a0003f87ca47a0008ca4d88d687214000036000056411c00059e3060004d66fc4e851e5764f28100000006043bc25200063400013c0000007ee8bc0005ce0003741762a24e00000004663c80001d02744005806840000000005ee00049e8767de2183ae17441c46400003478e00014800045818807c4280720001b00e08c400c7ba00081e0000c44b84ae04272011a27634201c2b43766b63348640b058667861067c44c13a29c7962be68a0ce3ee85a69629858a7b421c6b810239e27220a44e06800000053a7cc64036409870653c00077a29e52270a7522aa6ec0003e412c00000006c00000033e2ba00014604e6700003981bc0000361640762f62fa64e00068000000029449c4760000004704ba00076a6cc0002540aa1861967aa7ae0626c42ec00014284e0b264867603848e56600080c3e81620007e86ee5964986f000086c37a00063a84a66c03e2bc18075483644449a0002e21f200056c0b823e5c065200016e3d876e8de27824e0005d838a6a87a80ec0006fe00005a6360000000006263507e06d043c3b47740fa0004560000000000008786726120000004460005f024a2c68a612a16c2326b00003240001a600048a00037058c5fe0000be3b048c89a5527465d62a400000002e0003ce0561de35226c0007160d843a8844b01a400007e35e00067e8800002f800023447e1b600000077e
  | 6 => 0x6e421453808000088a80e3c641a7fc53070265a4063367764ac5f657251621e00051c0e42de79847c62c3300000000002ae0000004de88e8d06fa4d02066aa0002ce0000003460d620c57e0e60000f48be3182fe5f476c7b622041009234083444028a51800000088600002479a57a3560006de1e86ce2ca8962620063162da6c882832e66a8167f82400b611278c65642a1fa27c0164cc40a08a7380862043947640000f255a00223814472a0001a20001600000a000000029032804800037c1e64be87c4ee00000046e00010c00000003a5706445980006d24dc0440000000006380007260001fc4380001f64223b20002000f80007a200000069c57c00005c82c7006006e242456e5be30000000024832068800000084217275a0007828606d446016a0001663d64723143265ca1b866832c0ee3925ec5f242033c3ec5143808583121e47ac2025601c84821f87567a460280452086e48083862000000038e76259a65c6187b07405f802c69e28e5025d04880005c269a62e5d25b66423880000001e23da41e7ea7600000000004165ea42601073c71869807a8888b22e40002e82f42806648080003c400000027072e6160c83b80005e831c8a82b85a675c00e5e471e5b28524bc1822860bc0c60640280901681aa4e41ec17a21238c49286881c0
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xe544426e62951109b58a544425f63551109718d544426f62551109b189544427761551109ed81544423e65151108f98c544423e64d4d108f593534426e62d4d109b58b534431f54d4d10c7153534431e64d4d10c7593534434e62d4d10d358b534435561d4d10d6583534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534427b6054d109d18453442786014d1097994534431f5414d10c7150534431f6414d10c7190534434f6214d10d318853443576114d10d6d80534423e6590d108f196434431f5390d10c714e434423e6510d108f194434431f5310d10c714c434432f54d4910cb153524434f53d4910d314f524426e63d4910cb90f524432c43d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109ed81524426e6514910cbd50524432c5414910d3d4c524434c53149109b98c524432e4314910cb10c524426e65cc9109b197324432f54cc910cb153324434f53cc910d314f324426e650c9109b194324432f540c910cb150324434f530c910d314c324438c430c9109d997314433754cc510cd153314435453cc510d9d4b314436452cc510bc9833144337540c510cd1503144357530c510d514c3144394430c510d9d483144364520c510f10c8314427a65cc110ced53304433854cc110d614f304436b52cc110da14b30442f261cc110ced503044338540c110d6d4c3044358530c110e610c304436b520c110da14830443c8320c110f40c4304433854c4110d614f104436852c4110cd15210443545384110d914a104425f63550109718d540426f62550109b189540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530427661d4c109e983530423f6454c108f191530426f6254c109b18953042776154c109ed81530431f5310c10c714c430423f64548108f191520425f63548109718d520423e64148108f590520434f530c810d314c320438c430c8109d59441043355410410bc5804104275650c410d594c3104394430c410f10c831042f1600c4109d59421043655208410bc58021042796510010ce55040042f16110010ec1044004279650c010d694c3004398430c010f20c830042f1610c010f40c430042796508010da54820042f16108010f808420042796584010bc58610042776544010ad19110042d46344010b9189100427b6544010ae19110042d86344010ba18910042f36544010dcd9510043b36444010bc99110042f06444010ec19110042b06444010f4d8d10042f26344010bc18d10043d06344010b418d10043725344010dc14d10043b24344010ec10d10043e36244010bc98910042f06244010f818910042e06244010f8cc910043e03244010
  | 1 => 0x823c6590d20c7d4e434831c5390d208f994434823c6510d20c7d4c434831c5310d209b997324832f54cc920cb153324834c53cc920ba983324832f540c920cb150324834f530c920d314c324838c430c920cdd53514833454d4520d5d4f514835453d45209d98f514833643d4520cd10f514836732d4520d90cb51483375414520cd15051483575314520d514c51482766314520cd90c51483344314520d9cc8514836432145209d997314827465cc520cdd53314833454cc520d5d4f314835453cc5209d9943148274650c520cdd503148334540c520d5d4c3148354530c520e510c31483c4320c5209e997304833b54cc120ce153304835853cc120ba98b304837351cc120dc147304833b540c120ce150304835b530c120d614c3048398430c120f20c83048373510c120dc14430483d0310c120ce153204835853c8120dc147204832c5488120d314e2048364518812097d8d540825c63550209dd85540827461550209d984540827561150208f993530823d64d4c209b98b530827661d4c209d587530827a60d4c208fd91530823c6454c209bd8953082776154c209d185530831f5310c20c714c430826d6510820cb55042082e960108209b594320834e530c820e310c32082e9600c8208fd91510823c645442097d8d510825c6354420d5d4c3108354530c420e510c31083c4320c420d954421082e960084209e59440083395410020ba58840083a842100209e594300835a530c020e610c30082e9620c020f20c830083d0310c020ba58a200826f6548020ab19120082cc6348020b9185200827b6548020ae19120082d86348020bc18520082eb6548020dad9520083ab6448020ba99120082e86448020ea19120082a86448020f2d8d20082ea6348020ba18d20083c86348020b218d200836a5348020da14d20083aa4348020ea10d20083e36148020ba18520083e06148020b818520083e33148020f80c5200825e63d53109758f54c426e62d53109b58b54c423e64d4f108f59353c426e62d4f109b58b53c423f6454f108f19153c426f6254f109b18953c431e5310f10c754c43c423e64d4b108f59352c425e63d4b109758f52c434e530cb10d354c32c438c430cb10d594c31c4355530c710e510c31c43c4320c710ced5040c435a53cc310d614c30c4398430c310f20c830c43d0310c310dad4820c425e63d52109758f548426e62d52109b58b548423e64d4e108f593538426e62d4e109b58b538423f6454e108f191538426f6254e109b189538431e5310e10c754c438423e64d4a108f593528425e63d4a109758f528434e530ca10d354c328438c430ca10cdd50418435653cc610d514c3184394430c610f10c831843675208610d694c3084359530c210e610c30843c8320c210f40c4308423e63d51108f992544425e63951109758
  | 2 => 0x648c430ae592310c39a438c430e610e310c2ea628c430ba58a310c3cb328c430f20ca310c2f2618c430b6596310c359658c430b6992310c39a648c430a6992310c399648c430b6192310c2da628c430f298a310c2ca628c430f258a310c2da618c430b4986310c27b654c430aed91310c2b8644c430e610d310c2eb624c430ba189310c3c8324c430e690c310c398430c430f2cc8310c3c8320c430f44c4310c2da640c430b6190310c2da620c430b6984310c3d2610c430f4944310c3d1510c430f4d04310c3d2410c430f4504310c3d0410c430bc98c310c3d2630c430dc94c310c3d2530c430f4d0c310c3b2430c430f490c310c392430c430f450c310c3b0430c430f410c310c390430c430f4cc8310c3e3320c430f0cc8310c3d2320c430f44c8310c3d0320c430f80c8310c3c0320c430f4d94310c3d2650c430f4594310c3d0650c430f4d90310c3d2640c430f4590310c3d0640c430f4d50310c3d2540c430f4550310c3d0540c430f4d88310c3d2620c430f4588310c3d0620c430f4d48310c3d2520c430f4548310c3d0520c430f4d08310c3d2420c430f4508310c3d0420c430b698f210c2d963c8430e610f210c3c832c8430f40c7210c2da6388430b658e210c3984388430f20ca210c3d031884309ed95210c2786548430aed91210c2b86448430b6d8d210c2d86348430e610d210c3c83248430f40c5210c2db6308430b618c210c3984308430f20c8210c3d03108430f8484210c25e63d53209758f54c827661d53209d58754c823e64d4f208f59353c827661d4f209d58753c823f6454f208f19153c82776154f209d18553c831e5310f20c754c43c834e530cb20d354c32c838c430cb20d594c31c8355530c720e510c31c83c4320c720ced5040c835a53cc320d614c30c8398430c320f20c830c83d0310c3209798f548825d63d52209d987548827561d52208f993538823d64d4e209d987538827561d4e208fd91538823c6454e209dd8553882746154e20c794c438831d5310e20cbd50428834e53cca20d314c328838c430ca20d594c3188355530c620e510c31883c4320c620d694c3088359530c220e610c30883c8320c220f40c4308823e63d51208f992544825e63951209758e544827661951209d586544825f63551209718d544826f62551209dd85544827461551209ed81544823e65151208f98c544823e64d4d208f593534827661d4d209d587534831f54d4d20c7153534831e64d4d20c7593534834d62d4d20d5987534835561d4d20d6583534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209bd8953482776154d209d185534827b6054d209b188534825e6514d20c7d50534831c5414d20c7d90534831c6414d20d3d8853483576114d20d5184534835b6014d208f996434
  | 3 => 0x30bad89300c2e8624c030f20c9300c2f3614c030bc185300c3d0314c030b698f540c2eb6255030ba189540c2f36155030bc185540c3395415030b698c540c35a6394c30b6992530c2da6294c30b6986530c27965d0c30ba98b430c2e962d0c30bc987430c2f161d0c30b6597430c35965d0c30b698b430c3ca62d0c30b298b430c3c962d0c30b6987430c3d261d0c30b4987430c3d161d0c30b698e430c2ba6390c30a698e430c33a5390c30e694e430c27b6550c30bad89430c2e86250c30bcd85430c2f06150c30e650c430c2ba6310c30e698c430c33a5310c30e694c430c2db6510c30b6594430c2da6410c30e6990430c39a5410c30e6550430c2da6210c30b6984430c39b6510c30e6994430c3996510c30e6194430c39b6210c30e6988430c3996210c30e6188430c39b6110c30e6984430c3996110c30e6184430c39843d4830e610e520c2bb6454830ae191520c3984354830bcd85520c2f06154830e610c520c3695214830b698f420c2d963d0830e610f420c2da6390830b658e420c39843908309ed95420c2786550830b6d8d420c2d86350830e610d420c2f36150830bc185420c3984310830ea508420c39843cc830da94f320c3ca53cc830f2d0f320c3aa43cc830ea10f320c3c843cc830e210f320c279658c830ae992320c2b9648c830e690e320c398438c830ba98a320c2f2618c830bc586320c2d9658c830d6596320c2da648c830e6992320c29a648c830e6592320c2d8648c830b698a320c2ca628c830b6986320c3d2618c830b4986320c3d1618c8309ed95320c2bb644c830ae191320c398434c830bcd85320c2f0614c830e690c320c398430c830f24c8320c2da640c830b6190320c2da620c830f2988320c3ca520c830f2548320c3cb420c830f2908320c3c9420c830f2108320c2da610c830ba98c320c3ca630c830da94c320c3ca530c830f2d0c320c3aa430c830f290c320c38a430c830f250c320c3a8430c830f210c320c388430c830f2d94320c3ca650c830f2594320c3c8650c830f2d90320c3ca640c830f2590320c3c8640c830f2d50320c3ca540c830f2550320c3c8540c830f2d84320c3ca610c830f2584320c3c8610c830e610f510c3c832d4430e610e510c3c83294430aed91510c2b86454430e610d510c2eb6254430ba189510c3c83254430e610c510c3c83214430dc544510c2da63d0430b658f410c39843d0430f20cb410c2da6390430b658e410c3984390430f20ca410c27b65504309e195410c2db6350430b618d410c3984350430bad89410c2e86250430f20c9410c3984310430f20c8410c3b14110430e610f310c3c832cc430dc94f310c3d253cc430f4d0f310c3b243cc430ec10f310c3d043cc430e410f310c3e332cc430f48cb310c3d032cc430f80cb310c3c032cc4309e596310c2ba
  | 4 => 0x9cca518c3563294630d50ca518c3643294630d10ca518c3365454630cd551518c3944354630d9949518c3655254630f10c9518c3364354630cd10d518c3673254630d90c9518c33654cc630cd553318c39443cc630d994b318c36552cc630f10cb318c29e648c630c7952318c2ce628c630d394a318c31e540c630d3948318c355510c630cd950318c335540c630e590c318c394430c630d9948318c365520c630f1cc8318c3c4320c630b5594318c355650c630d5950318c396540c630c5950318c395540c630d5150318c356520c630f1948318c346520c630f1548318c33a54cc230ce553308c36a52cc230da54b308c37251cc230dc547308c23e64951309b98a544c26d62951309d986544c27561951309e582544c25f63551309bd89544c26c62551309dd85544c27461551309ed81544c23e65151308f98c544c23c63151308f996434c23e6510d30cbd53524c32c54d4930cb90f524c32c43d4930cbd50524c32c5414930cb90c524c32c43149309b997324c32f54cc930cb153324c26e650c930cbd50324c32c540c930e310c324c33754d4530cd153514c36752d4530d914b514c33643d4530cd10f514c36732d4530d90cb514c3375414530cd150514c3675214530d9148514c3364314530cd10c514c3673214530d90c8514c27665cc530cdd53314c33454cc530d9d4b314c36452cc5309d994314c337540c530cd150314c394430c530d9d48314c364520c530f10c8314c33b54cc130ce153304c36b52cc130da14b304c37351cc130dc147304c31c548c130d314a304c354518c1309bd89540c26c62550309dd85540c2746155030b398b430c2d661d0c30b6583430c29e6390c3097594430c31e6510c30c7594430c39a6010c30e6580430c31c43948308fd91520c23c64548309dd85520c2746154830e310f320c29e648c830b398a320c2d6618c830b6582320c38e430c830e310c320c34e540c830d3150320c3ca600c830f2580320c31c4394430d30ca510c23f64544308f191510c26f62544309b189510c39443cc430f10cb310c29e648c430b398a310c2d6618c430b6582310c396430c430e510c310c3c7320c430f10c8310c356540c430d5150310c356520c430f4980310c3d1600c4308f992500c23d6494030c710e500c34c3294030d50c6500c39843d0030f20cb400c3d031d00309e596400c2d96390030e610e400c3c83290030f40c6400c3385450030b6d8d400c3984350030bad89400c2e86250030f20c9400c2f36150030bc185400c3d031500309e594400c3395410030e610c400c3c83210030f40c4400c2ba648c030ae592300c398438c030ba98a300c2e9628c030f20ca300c2f2618c030bc586300c3d0318c03097d95300c29c644c030b3189300c2d4614c0309ed95300c2bb644c030ae191300c398434c
  | 5 => 0x405033451901409bd89531026c6254c409dd8553102746154c40c794c43102b96010c4097d8d521025c63548409dd8552102746154840cb54842102b96010840e310c321025f63544409718d511026f62544409b18951103355110440ae5804110394430c440f10c831102b964900408fd95401029c6350040ab18940102b461500409ed9540102d86350040ba18940102f06150040aed95401033b6550040e6d8d40102b86350040e618d40102986350040ce94d40103ab6250040ae18940103a86250040aa18940103ab3250040ea0c940103b36150040ae18540103b06150040ac18540103b33150040ec0c5401026e62d53309b58b54cc27661d53309d58754cc38c430cb30e510c31cc3c4320c730ce95140cc2eb6250330ba18940cc2f36150330bc18540cc33b5410330b698f54cc2ea62d5330ba58b54cc2f261d5330bc58754cc33b5495330b698c54cc2ea62d0f30ba58b43cc2f261d0f30bc58743cc2eb6250f30ba18943cc2f36150f30bc18543cc39a6310f30ae99352cc2b964d4b30bc98752cc2f161d4b30dad4a52cc27b6550b309e19542cc2db6350b30b618d42cc2f36150b30bc18542cc3a94210b30ea90f32cc3a843ccb30ae99232cc2b9648cb30e610e32cc2f2618cb30bc58632cc2bb644cb30ae19132cc2f3614cb30bc18532cc398430cb30f298c32cc3cb430cb30ea90c32cc3a8430cb30f210c32cc388430cb30ae99351cc2b964d4730ba98b51cc2e962d4730dcd4651cc27b65507309e19541cc2db6350730b618d41cc2eb6250730ba18941cc3b14110730ec90f31cc3b043cc730f8ccb31cc3e032cc730ae99231cc2b9648c730e610e31cc2ea628c730ba58a31cc3c8328c730aed9131cc2b8644c730bad8931cc2e8624c730e610c31cc3c8320c730f498c31cc3d3430c730ec90c31cc3b0430c730f410c31cc390430c730f8cc831cc3d2320c730f40c831cc3e0320c730f00c831cc27b65487309e19521cc2bb6448730ae19121cc2db6348730b618d21cc3e121087309b98b548c26d62d52309d987548c27561d5230c7d8d548c26e62152309b588548c27661152309d584548c2ce62d0e30b5987438c31d5410e30a7594438c31d6510e30c710e528c32e5494a30cb552528c38c4394a30d3d0e528c32e4394a30cb10e528c34c4394a30c310e528c32e5454a30cb551528c38c4354a30cb90d528c32c4354a30cb953328c32d54cca30e310f328c29e648ca30c7952328c2d6618ca30c7950328c34d520ca30cb950328c32d540ca30e390c328c38c430ca30b3594328c34d650ca30d3950328c38e540ca30c3950328c38d540ca30d3150328c31c4394630d30ca518c3365494630cd552518c3944394630d994a518c3655294630f10ca518c3574394630cd90e518c3344394630d510e518c3144394630d
  | 6 => 0x71c5310d219b997324872f54cc921cb153324874c53cc921b9987324872f540c921cb150324874f530c921d314c324878c430c9219d997314873754cc521cd153314875453cc521b998b3148737540c521cd1503148757530c521d514c3148794430c521f10c8314873454c8521d514f214872c5488521d314e214873b54d4121ce153504875b53d4121d614f504867a63d4121ce90f504873843d4121daccb504876832d4121dccc7504877031d4121ced5050487385414121d6d4c504875853141219e98c504873a4314121ce10c504876b3214121da0c850487733114121dc0c450487732114121da884504865f63550219718d540867b60550219e181540867a60150219e580540863e64d4c218f593530866e62d4c219d987530867a60d4c219e583530863f6454c218f191530867b6054c219e181530871f5310c21c714c430866d6510821cb55042086e561108219b594320874e530c821e310c32086e5610c8219d59441087355410421b958841087a442104219d5943108756530c421e510c31086e5620c421f10c831086e562884219bd9521086ac6448421b318d21086e860484219dd9521086b46448421b518d21086f06048421b9d9521087676548421e9d9121086e66448421b919121087a46448421a919121087c76348421b998d21086e46348421f118d21086c46348421d994d21087645348421e990d21087a44348421f8d8121086e46048421f818121086e060484218fd91500863c645402197d8d500865c63540219bd8953d026c6254f409dd8553d02746154f40c794c43d031d5310f40d394c32d034d530cb40e310c32d0356530c740d554c31d0394430c740f10c831d026f6254e409b18953902776154e409d185539031e5390e40d394c329034d530ca40e310c3290356530c640d554c3190394430c640f10c8319026e62d4d409b58b535027661d4d409d587535034e62d4d40d358b535035661d4d40d5587535035960d4d40c7d90535034f6214d40d318853503576114d40d5184535035b6014d40c714e43502ba6090d40c7d4c435034f53d4940d314f525026e63d4940cb90f525032c43d4940d3d4c525034c53149409b98c525032e4314940cb10c525026e65cc9409b197325034f53cc940d314f325026e650c9409b194325034f530c940d314c325038c430c940d5d4f515035453d4540d9d4b515036452d45409d98f515033643d4540cd10f515036732d4540d90cb51503575314540d514c51503675214540d914851502766314540cd90c51503344314540d9cc8515036432145409d997315027465cc540d5d4f315035453cc540d9d4b315036452cc5409d9943150274650c540d5d4c3150354530c540e510c3150367520c540d914831503c4320c540d614f405036852d0140dc147405031c5390140cb14a
  | 7 => 0x210c31e5d80430c7966010c31e5580430c7946010c31e510f520c7944394831add91520c6b46454831e510d520c6f36054831bc181520c7944314831d9548520c6d663d0831b558f420c79443d0831b598e420c6d56390831e510e420c67765508319d195420c6d76350831b518d420c7944350831bcd81420c6f06050831e510c420c7a54210831e510f320c76653cc831f194f320c7c743cc831e990f320c7a443cc831f110f320c78443cc8319d596320c6b6648c831ad592320c796438c831e510e320c6e6628c831bc982320c6f1608c831b5596320c755658c831b5992320c796648c831a5992320c795648c831b5192320c6d6628c831b198a320c6d6608c831f4982320c6d2608c831f4582320c677654c831add91320c6b4644c831e510d320c6f3604c831bc181320c796430c831e510c320c7c5320c831b5990320c6d4640c831b5988320c7c6620c831f1948320c7c5520c831f1d08320c7c6420c831f1508320c7c4420c831b5980320c6e6630c831f198c320c766530c831f194c320c7c7430c831e990c320c7c6430c831e190c320c7c5430c831e910c320c7c4430c831e110c320c7c7650c831f1994320c7c5650c831f1194320c7c7640c831f1990320c7c5640c831f1190320c7c7540c831f1950320c7c5540c831f1150320c7c7600c831f1980320c7c5600c831f1180320c79443d4031f10cb500c7944394031f10ca500c6b76454031ad191500c7944354031b9d89500c6e46254031f10c9500c7944314031f10c8500c77150140319798f54c865d63d53219e98354c867960d53218f99353c863d64d4f219e98353c867960d4f218fd9153c863c6454f219ed8153c86786054f21c794c43c871d5310f21d394c32c874d530cb21e310c32c87375410721d594f31c8754530c721e510c31c87c4320c7219798f548865d63d52219e983548867960d52218f993538863d64d4e219e983538867960d4e218fd91538863c6454e219ed8153886786054e21c794c438871d5310e21cbd50428874e53cca21d314c328878c430ca21d594c3188755530c621e510c31887c4320c6218f98f544863e64951219798e544865d63951219e9825448679609512197d8d544865c63551219bd89544867761551219ed81544867860551218f994544863e63151218f993534863d64d4d219e983534867960d4d21c7d53534871c54d4d21c7993534871d64d4d21d358b534875561d4d21d6983534875960d4d218f992534863d6494d219798e534867a6094d219e582534863f6454d218f191534866f6254d219dd85534867b6054d219e181534865e6514d21c7d50534871c5414d21c7d90534871c6414d21d3d8853487576114d21d6d8053487586014d218f996434863c6590d21c7d4e434871c5390d218f994434863c6510d21c7d4c4348
  | 8 => 0x31e610e508c76a5294231da54a508c7c83294231d6d0e508c73a4394231ce10e508c7584394231c610e508c76b3294231d68ca508c7583294231da0ca508c7483294231dccc6508c73a5454231ce551508c7984354231da949508c7695254231f20c9508c73a4354231ce10d508c76b3254231da0c9508c77331542318f992544c66e62951319b58a544c67561951319e982544c679609513197d8d544c66f62551319b189544c67761551319ed81544c67860551318f994544c63e6590d318f994434c72f54d4931cb153524c72e43d4931cb10f524c72f5414931cb150524c72e4314931cb10c524c66e65cc931cbd53324c72c54cc9319b994324c72f540c931cb150324c78c430c931cdd53314c73454cc531d9d4b314c76452cc531c7152314c74c528c531ced53504c73854d4131dad4b504c76852d4131ce90f504c73843d4131daccb504c76832d4131dccc7504c73b5414131ce150504c76b5214131da148504c73a4314131ce10c504c76b3214131da0c8504c7733114131d68c4504c66f62550319b189540c67b60550319e181540c6ce62d0c31b5587430c6da60d0c31a798e430c65d6510c31c7994430c71d6510c31e5984430c7956110c31c710e520c63f64548318f191520c67b60548319e181520c78c43cc831a7992320c6ce628c831b5586320c6da608c831e390c320c78c430c831d3950320c74c540c831f1984320c7c5610c8318f992510c63d6494431c710e510c74c3294431e510f410c7c432d04319d596410c6d56390431e510e410c7c43290431cd151410c6d76350431e510d410c6e76250431b9189410c7c43250431bcd81410c6f060504319d594410c7355410431e510c410c7c43210431ad992310c6b5648c431e510e310c6e6628c431b958a310c7c4328c431bc982310c6f1608c43197d95310c69c644c431b3189310c6d8604c4319dd95310c6b7644c431ad191310c794434c431b9d89310c6e4624c431f10c9310c6f3604c431bc181310c71c4394031d30ca500c63f64540318f191500c66f62540319b189500c6d663d5031b9d89540c6e46255031bcd81540c6f06055031cd550540c6d66315031d598e530c6d66494c31b598a530c6d66094c319d597430c6e662d0c31b958b430c6f260d0c31bc583430c6d565d0c31d5597430c6d662d0c31f198b430c6c662d0c31f158b430c6d660d0c31f4983430c6d260d0c31f4583430c6d66390c31ad98e430c6966390c31cd94e430c7965390c319dd95430c6e76250c31b9189430c6f36050c31bc181430c7954310c31ad98c430c7966310c31cd94c430c7965310c31b5d94430c6d56510c31b5990430c7966410c31e5950430c7955410c31b5988430c6d66010c31e5d94430c7966510c31e5594430c7946510c31e5d88430c7966210c31e5588430c7946
  | 9 => 0x58b535075561d4d41d6983535075960d4d41c7d90535074f6214d41d318853507576114d41d6d8053507586014d41c714e43506b66190d41c7d4c435074f53d4941d314f525066e63d4941cb90f525072c43d4941d3d4c525074c53149419b98c525072e4314941cb10c525066e65cc9419b197325074f53cc941d314f325066e650c9419b194325074f530c941d314c325078c430c941d514f415076452d0541c714e415072c5290541d6d4f505075853d4141dad4b505076852d41419e98f505073a43d4141ce10f505076b32d4141da0cb505075b5314141d614c505076b5214141da148505067a6314141ce90c50507384314141dacc850507683214141dcd04505073a41141419bd89531066c6254c419ed8153106786054c41c794c43106b56110c4197d8d521065c63548419ed8152106786054841cb54842106b56110841e310c32106b564904418fd95411069c6350441ab18941106b860504419dd9541106d46350441b918941106f06050441add9541107376550441e5d8d41106b46350441e518d41106946350441cd94d41107a76250441ad18941107a46250441a918941107a73250441e90c941107b36050441ad18141107b06050441ac181411065f63540419718d501066f62540419b189501066e62d53319b58b54cc67a60d53319e58354cc78c430cb31cd95141cc6e76250731b918941cc6f36050731bc18141cc7375410731b598f54cc6e662d5331b958b54cc6f260d5331bc58354cc7375495331b598c54cc6e662d0f31b958b43cc6f260d0f31bc58343cc6e76250f31b918943cc6f36050f31bc18143cc7966310f31ad99352cc6b564d4b31bc98352cc6f160d4b31d9d4a52cc6776550b319d19542cc6d76350b31b518d42cc6f36050b31bc18142cc7a54210b31e990f32cc7a443ccb31ad99232cc6b5648cb31e510e32cc6f2608cb31bc58232cc6b7644cb31ad19132cc6f3604cb31bc18132cc794430cb31f198c32cc7c7430cb31e990c32cc7a4430cb31f110c32cc784430cb31ad99350cc6b564d4331b998b50cc6e562d4331dcd4250cc66e62d52319b58b548c67a60d52319e583548c71f63552319b988548c66d62152319e980548c6796015231b398b438c6da60d0e31c7550438c69d6510e31c7594438c71c4394a31cb952528c72d5494a31e310e528c74f4394a31cb90e528c72c4394a31d310e528c70c4394a31cb951528c72d5454a31e310d528c72e4354a31cb10d528c72e54cca31cb553328c78c43cca31a7992328c71e548ca31b6982328c71e540ca31d3548328c72e540ca31cb550328c78e430ca31e310c328c6cd650ca31d3594328c74e540ca31e3950328c70e540ca31e3550328c74c540ca31cd953318c73554cc631d994b318c76552cc631c710e508c74c3294231ce952508c73954942
  | 10 => 0x8cb584394232c610e508cb6b3294232ce951508cb395454232e610d508cb725154232dc545508cb3a4354232ce10d508cb6b32542328f992544ca6d62951329d986544ca7561951329e982544ca79609513297d8d544ca6f62551329dd85544ca7461551329ed81544ca7860551328f994544ca3e6590d328f994434cb2f54cc932cb153324cb1c548c932cdd53514cb3454d4532cd90f514cb3443d4532d9ccb514cb375414532cd150514cb364314532cd10c514cb673214532d58c8514cb3b54d4132ce153504cb7351d4132dc147504cb3a43d4132ce10f504cb6b32d4132ced50504cb385414132dcd44504cb705114132ce90c504cb384314132dacc8504cb5a32141329dd85540ca7461550329ed81540ca786055032b358b430cad661d0c32b6983430ca9e6390c3297594430cb1e6510c32c7594430cb8e6210c32e3588430ca3e64948328f592520cb1c4394832e310f420ca6d6590832b358e420cb8c4390832cb151420cacf6350832e310d420cae76150832b9185420caeb6050832ba181420ca6d6510832cb550420cb8c4310832ab992320caad648c832e310e320cae6618c832b9586320caea608c832ba582320ca5f654c832a7191320cad4614c832b6181320ca6f654c832abd91320caac644c832e310d320cae7614c832b9185320caeb604c832ba181320cb1c43944328fd91510ca3c64544329ed81510ca786054432c710e500ca3f64540328f191500ca7761540329d185500cace63d5032b9d85540cae46155032bad81540cae86055032cb550540cace6315032d398e530cace6494c32b3986530cace6094c329b597430cae661d0c32b9587430caea60d0c32ba583430cacd65d0c32d3597430cace61d0c32f1987430cac661d0c32f1587430cace60d0c32f2983430caca60d0c32f2583430cace6390c32ab98e430ca8e6390c32cb94e430cb8e5390c329bd95430cae76150c32b9185430caeb6050c32ba181430cb8d4310c32ab98c430cb8e6310c32cb94c430cb8e5310c32b3d94430cacd6510c32b3990430cb8e6410c32e3950430cb8d5410c32b3984430cace6010c32e3d94430cb8e6510c32e3594430cb8c6510c32e3d84430cb8e6110c32e3584430cb8c6110c32e3d80430cb8e6010c32e3580430cb8c6010c32e310f510cb8c4394432abd91510caac6454432e310d510caeb6054432ba181510cb8c4314432d9544510cb8c43d4032e310e500caaf6454032ab191500cb8c4354032b9d85500cae46154032e310c500cb6950140329bd8953d066c6254f419ed8153d06786054f41c794c43d071d5310f41d394c32d074d530cb41e310c32d066f6254e419b189539067b6054e419e181539071e5390e41d394c329074d530ca41e310c329066e62d4d419b58b535067a60d4d419e583535074e62d4d41d3
  | 11 => 0x3f6550c43abd894310eac6250c43add854310eb46150c43aed814310eb86050c4397d954310ecc6250c43b51854310ed86050c439dd855210e7461548439ed815210e7860548439bd895110e6c62544439ed815110e7860544439bd895010e6c62540439dd855010e746154043c798e5310e9e6294c43a79865310e9e6094c43add855210eb46154843aed815210eb86054843cb5485210eaf6254443ab1895110ebb6054443ae1815110f355114443abd895010eac6254043add855010eb46154043ce5405010e776154f429d18553d0a7b6054f429e18153d0b1e5310f42c754c43d0a776154e429d1855390a7b6054e429e1815390b1e5390e429d9875350a7561d4d429e9835350a7960d4d42d358b5350b5661d4d42d55875350b5a60d4d42d65835350b1f6414d42d3d885350b576114d42d51845350b5b6014d42d61805350b1c5390d42ab98a4350b1f5310d42d314f4250b1c5390942d5d4f5150b5453d45429d98f5150b3643d4542cd10f5150b575314542d514c5150a766314542cd90c5150b344314542d9d085150b364214542d6d4f5050b5853d4142dcd475050b7051d41429e98f5050b3a43d4142ce10f5050b5b5314142d614c5050b735114142dc1445050a7a6314142ce90c5050b384314142dad085050b3a42141429dd855310a746154c429ed815310a786054c42c794c4310aad6210c42ab5924210a3f6550842a718d4210ab46150842ae1814210a6f6550842b318d4210ae46150842ba1814210aaf6550842cbd954210b8f6350842ab18d4210b8c6350842a318d4210b2e5350842e9d854210aac6150842e91854210aa46150842ead814210aac6050842ea1814210aa8605084297d8d5110a5c63544429ed815110a78605444297d8d5010a5c63540429dd855010a7461540429d98754cca7561d53329e98354cca7960d5332cb95142ccae76150b32b918542ccaeb6050b32ba18142ccb2f5410b32b398f54ccae661d5332b958754ccaea60d5332ba58354ccb2f5495332b398c54ccae661d0f32b958743ccaea60d0f32ba58343ccae76150f32b918543ccaeb6050f32ba18143ccb8e6310f32ab99351ccaad64d4732ba98351ccae960d4732d9d4651ccaae64d4332ab59350ccae661d4332b958750ccb6b50943329d987548ca7561d52329e983548ca7960d5232c7d8d548ca7661152329d584548ca7a60152329e580548cad661d0e32b6983438cb1d5410e32a7594438cb1d6510e32cb953328cb2d54cca32c710e518cb365494632cd552518cb944394632d5d0e518cb364394632cd10e518cb544394632c510e518cb673294632cd951518cb355454632e510d518cb364354632cd10d518cb673254632c710e508cb3a5494232ce552508cb984394232dc946508cb715194232d6d0e508cb3a4394232ce10e5
  | 12 => 0x800800400800c01c01000000005400401000800000001801800000800000006000000800002800801400000406002c00000800000000000c00000001804c01c00400c00400003000000400004c01400002004800001800003800400800c00400000000000007c0080000a002000400003400400400c00401c00800000000001800002801400008001800403800400000c00402808c00400000000000001801800000c00002400000800c0580000040080080140380140b400c01802400000004c02c00400000000001801c00400c00000800c0240080240d403401800c00005400c01000002000c00400800400004800800400002402800802c00000000400800000c00000000802804400400000000000c00000401c00000000000400404800c00c00003c02400000000000000003400400400000000001800400001801400000000002c00400805c01007c01400c00000400c01002000000004c04001000000400001800800400000403404400001401000c00000800401000000000002401001c0040000000280080080100180080100100040640dc00400000c00000c05c03803001000400000401002404800000801400c04800000001400400000402c00800401001007800c01c00404000c01000000000000000c03400000805003800000c03c05800000000c01c03001401001800000002000800002002800002800800c00000000c02400000000801802000c0000080180180b800002001400800c00407003000400c00002800800401003000400000800000401403000800c01c00001003804406800000006c00800806801402c07802001000c01803c00000800000000001002000c00800403000000000400000401004800000c00c02c00c01400c00c00002801c00800c0080700140080080f401400c00000000400000800000000001000000401801c02002800800400403402000000800401000000401c0300000000180280680b000000c01400000000002000002c00402c02000c000024057665294743d954a51d0f665254743d954951d0f6a5294343da54a50d0f725194343dc54650d0f6a5254343da54950d0f725154343dc54550d0eae62d0e43ab58b4390eb661d0e43ad5874390eba60d0e43ae5834390eb661d4a43ad5875290eba60d4a43ae5835290f2f5294a43ab98b5190ead62d4643ae9835190eb960d4643cdd465190eae62d4243ab58b5090eb661d4243ad5875090f3b5094243cb90f5250f4f4314943cb90c5250f6752d4543d914b5150f3643d4543d9d485150f645214543d5d0c5150f364314543dad4b5050f6852d4143dcd475050f7051d4143ce90f5050f6b5214143da1485050f735114143dc1445050f5b4314143ce90c5050eae62d0c43ab58b4310eb661d0c43ad5874310eba60d0c43ae5834310e
  | 13 => 0x62352411852cd2626900003540008d345980013060002b723a48e87f007d0000e067c00001b6c866000000000000010f00000000000001ce80000000000000000c020321f985800009660f9a29800062d00017a0000000000263802222e0000bfcf360000a01b380005e70580000aa07983739af858a0003040000658740133000000040e39e8000e920003841db855a3ec010a29000000000005d40008f52870000fcc7b517297500de6cc0748cbcc727f40d22034f0859200006e432c26b2909158f003ca0448000e5e52b00008805c68560001d280000002bf9d0883080a3320d18bb64104f08708000a510000078000a0d2bca84c1d800004900e400043813d9c54ebc00047c813c00026c0ac0cd0b6449d000000117400000002107909571a680009e8488000133087a0000000000000000214a23400045539892e000086e4bd20f0da066d0000c2cd1029d0a382cd3361d6324871839299f216800031496531b00000000004fd126c00022600002a80000000001dc000000012d80010cc25a00016f8c543892cf000118e00000012a007ea1808f90c5212949467015c0000004690000f50000000276c00000000000000003c93e2800400000401405404800000c02001401400801000800800000402800401803400002001001802401000800c00000800000003c00001000004802800400806400003000802401800003401801c02c00800003000402400000803c00000000000000003800000000400000802000000003000404800000800001000400005000000004400000000400001c00400400c01402400400000002801c00c03000000403400000000001c05805803800402c05000800001803c03001c00001c02000400000000c00400c01401400001c00401400801802401400400800800c00006004400000400c00402801400400000000001403400c0a400000000402c01c0000000cc01c00006000401000400000402800001800803000000000404001001802400400001c00400400000400006808c00803c00000c00400003800c00000401800c00400400000004002c00400000800000c00002400c00001400000003000000004802800001000400801c01401001c00802000800001400400800800800006000800414c00c0a800003003c00400000c00c00400800003800000000400400001c00401000401400000000000400000001c04800000000800c00c01c01801001402000800800000801401001801c01c00000400002000800400003401c00002400400c00400400000402000400401002002c00400c04800400000001000805400004c00000800800002800c00406000007000002800401400002c02400800002c00801000801401c02400400400001c00002002006000800001c0440000040000000000140000040040
  | 14 => 0x33700001141170000d44a5800000021a07ea00031aa698d908d7000000010e0003341a90ac482042500000003ff0021eb8000000095800016a53b0001328094000000000000031d21c83500000000359c940000001060b38e4e4ef2e8888868613639819ac85463710c25f00005e30c428fcd5475607526a8a520062a60000bd8702000000055e0000001794dbc0004e580013587584d808400004b44479f8c000000498800000073b38b8000b440001c09fbcfb25d702000000004c20001ba4e8258821900000002a920da8cc6fe00040c8c0d3123c53608000940000000000000000000000000000003ac8cb4000000000109c00000000000000004d933300000005990000234a5e6cb0a305880000000000000a3c87819f8c5c00094a000000036875431e800044a0000000efc3200002c720c01e40d33fea7943da00000016ec4325da000000000045a14681c1106000278a230cfe13200000b45f003443e00006e200000015bc00000000002e800069b000000000000000005d00002ee1000308000a27187250512041339a20a000000021b80000000002200000aaa89100108ec000697367a13c00000000021d8e7e5641f80000fb4000000000086038501780002de0000bb09f4000000187800129816c282a24c00063b0001ec000000042316a935a2554aca394a9c42000020b52bc8ae378957c1fe22a43c990ce3a0001179bd1244362518800111c68900008d40000004ce0000000a46313a848bb269200026146f000000000000006f32d7001c43e57400012e80003cd06b03bc30090326399800009b435d9e9901e00021da258e080301339d480000002590000fa82d815ba388524771072886947242b4241810c663180fea724f9e91f350884d1144cd0b4927884407613918ac2b275341d23d8e549b700000011846b12b68000f1e1640000c7c932000179000000051427501c8bc069922f98f8ab49b851484940b40000000e880400000000000ec6000000000010259a00000000007610000fbd064a1400023cc0006dc2fe9b6940200020c8910ab84ae3fe0000000000000000000000000000000006fd4300000eda0002d796f42e41e33f42858ece1e4228800061882c10e1fb0dc200000004a0030417000009458424915b00000008ef02e9164d048d61539d2c0000004978000f6e0002d005f00000004149fc42ee0540001ce134200000000013b80e120f09b90b89c3000279cb200f00000000cd296b40d165000043f3418000000000388a538b064821c100643767192be800000062c0000000ed690a0000d5082400004b24800004d12178000cae2b94eb1cf80000004320aac19800000000000000000000fb800044e000000053e000044000054a11b0060000c2400000000005c225c22380011
  | 15 => 0x6100dc00037b00007b0a4432310509444fb4b0007ca742b100000001e80003f5a300c0097042f0001112000432813807a2dc42d22800000f14518000a4a2174dea6ac00006a00022e43b827800002650ea00015617700001c44248a0c0001a523684908fc34900013780000002e520c53c60002ef9cb903c000000202d30e4344f7800124e3990000b6c00089c14795c40001dd2f082a526e2244bb80009581430000df800034800005100000004eb96cc9c259d00000000340000000001454000317800128600030c03cd2f25d03f100006e6000000000125a6d33e7140947451c35800012be7660cf0be4be43a30000f5c00000000018b800000000026fcbf08f838980000000004288000000000000000000067a1b8000000028818500dc0da9cd40721e91c647700000cc5f600043197b48389d51a3800098c129000000022490839d28649cc0003b515593020000001610fbc0004f5881c0009233ae9f2c6763af00000012b476f00b163cda411e00004b874c0152c1061cbea5630001c853180081149948ffe00000000001880004b72959250000203826c00000000000006382d6000184c0000004b880000000000000000312000000266149c9a51e980009a66170e0a44125670f38e0000cee8de52a143c5bc85801c1ef40846a835d0990e165cd395a0912a65454dc88d006a000000000098848d000135c00000035997ac2467aa1d0049c00090e3d98d4c39c49a37306c40ac3b71601468f885c405c1d90d4c49236f8000a0e29b000020800067000000000006f2000130c2204bc51080000000001c7000000000034e8c000000004b0a7e00000000000d3cdd80003629c1c0001bd0001460a54a2c1049da057c8a5000000034265400007dcdda5594310d4095e4d60f4a930a9e0b2007a6407aa3ae4fe23c40000c004b869d3460eb06804e036c00a0c5a380c4c4352a697750c221b52586709b88ad0000778464315032800046c13c1db10a000000000000003b41d52b5874000057b0b887f8c0e04c4578000f402d50001ef8000a414e6183c0000000000ed4f902ed1cc0d14d6a0000d5202000000018325d0c503b103da4f80000000000de909a00049a1d687f87754a39bc066e8cc4f0000000094b000000013469407f24a86443102ff071541675738600007962c630f000003624534713c08848f00002150e207cd1d402ac12871600018582aa3234f8097494c83e2d0a890000000151800000000000000009ce0003dda8400000004c00aa881e0002b600002680001ac8000000a37000000000000000023600001a909f17b91c21f11cd20e0000a110000000000000000000000033833b1a940004961738dec00065e46c8fb4a3e46c0001b580000001fc15d8000000000000031c49c4bc000046e33900000000004570
  | 16 => 0x25cc00096c088a51000000000000000000000000accd780002d896b06fa8773019624b8e00009b89fc8f24c50000000c944fc2fe282497c4db0000be94709c01d200000000000a715187b650c1c5a3180000003298a24a6e0a311c25b4fb01522300bf4e8e2e014f08293c49a24e703806d6a0c1140e44e78000034210c6f8476142879c788a5537205fc57e5cf4740cf0fe64433c128d41a46a91f8979838043a3e5090410093c174197c1ee57706d1284f5600041a101400095002984b49e47fb3110dbcbe000052680011968f2529800000000034200000000004d784280000002670000fbe0000000ecce0279747a00000000bf00014c80000000001921468000000220451c4a50999be87a890b2cb8418e6a61910294185be5a50098eb113e7ea118a5547782ea3d0a57000082b1c98000cc411800007b0190058000000000000000000007ba87239c982d128000390194521e00000016e506e94200023f400000018f09b40000000001714d1ea251ae124c0001a64e0a2005506c71e188482da00017800b8b0c3d100000013f21500f08634370000468a5a945c57c4832058c96a32000000000005900012293ee5a646a14d06229ba00000014400000001dc89f453d3eb1a700620000e900000008db3011958c686740001cb400000024800000000dd2e10000a6a0004d40000a5000000000006ac4b00001b240004a724c060864e0002d3a1b40006d500027d89aa4631b60c810761b0057a12cdfc8022471a88ba6330307055104468008693f8a8800018da2686b44650b500000006d10001f311aa00023c0d380c43640ab277922e64020205b8a8ea280002610b360003ee20a80009264a418fcdfe7a90800000f262ef371a73cb485f411804a80000004640b2143c9be058883c75a91530609dd31e86a2710b2874a93f2b4a7d000000011380000000004d8888c00000027b10f00f40640002874d9400050d800072e0004c9156cdea00012710b03d40001d48000c367e400014cc0a00001bba0bc0000003af8000234325000000000000000026ed19e2624f321145e83b40f10f041fa8390d68ff41c699700006f0a4e99545e000102e14c0650908fe4441000000000000015d0288ed85800000568fa018f26e97e42600224d49a0441a00000009f00000000ec00008908ec0d181981ea76000009007fc31600013fc00000043591900002084cd06cca8600000000000000bd46800000004da00020d80001a03c59de53fe1d904594288b68840000000000000000000000053c000000111019b4908d2c7721533189ee000028a04c00003181a20001bbc00000047d824c60400028e8000000000021a4cc0000002a119a8c7459f00000000007d71e380043223630db8000b820691e017a499019d0688404bee67100009580000000000000
  | 17 => 0x40000002250a2d07a74d47f81140005cb000098c0006911ce1f6d1300004d900000000553d61d152fc20e15001f40e87b420591cd228a2b23f8000c123d90908e3c5486a30001e682fc9511510f900006723450bd45d87e00eb92252f67231259c7c83a5490dd25592fa6e23bfa8192de450303070ce0a1b53e1830cd5a9353ce1e142e051500005ccd9a6eb32227cc0fe6c61ba8c98eec3fb36a12540006bf023908c2065ba40a80004044704e2998c4e29fe000287c7a053051e91c92ba1db3c19be51d49d10000c1100e6b800000008de00023515f838e85013b09e50d877d000000000006338f0594f2c00000000005f88fe0000de46ae000323800000000000002700000000001adc00033508c800000000000029280000000000000b6e26a000264cae424819ea7092e40c7234000000067d0000db908e00032c8000a2e00000000000004ed1a200009620000059ad07985fb42087805d22750e404d541e46100021bceca0003fb97000000000000ce80000b9000000000000000000000009a7486000000000000007e52c60002d800000000002d400000001ca47200011509040001fe40000dc00003b800000037ba458ed200039ba55059800008a004149009e1788000ae00001b4800105c00014c1e2053836526a00000000002339b801ae1af49200000005931f58e3000000000006ad48e1070000b3c00052e1402518e862504faa91452c7c74fd8f9c0003b840990902b69e900009490426110f915986801090bd24e547c79d0e7933cf201783a2073451800003c0bd93487a313095604b21314620000ea015d3502370178a3628427404e85164a010453ba8351890ca867c3551ba1f48ca02c340e08fc0b68c12702710f8c45246503f0c344712601ad923a6862d6934810c8c30df28890be23a43f18f048c615198a28931034a3ca0134aa215c03c9360d8409f15e85acf1a9c64ac188c68232123da07419c1485168eac0003a71f5000080c3e034aa6282ce41a00011744722954768fd80c092527c01703a622100004580000490f7a7c4d5656a2aa0d81328a0008705e42cc7145118604c200000000b1c000000000000000000000000000000002db0c5014299d1b6a4c002e8c53458b5c40c0000000000d5854a00015cc3067780000000c6435e0001e1916896700022540007c93891fe800000000005a000000000000000000000001f049466300000f480000000000ccc0000000000b4050e000000000000003b09e9fd800000044c80001be3e84cf14e0000449289800092887d42d800006c4800000000b7e24327e8a100003fa175a43400011d2e71630f443df36212440009ee4f60000b8600010b1ca42ae73325680000000002820a404bc0002e900006be00336e800000013f00000003f800014980000000003930ac13a4091
  | 18 => 0xa40c0051492a072a58e780003b030e0a191d62810001df800000000002d920217d039900852291c014800113c126000196000053e00025150a48b700006fc2400000fa19b11760f93d6944880209d37c13e43d65950000c244d078a31022a468410200000000004e30000618ee60003aa800000000000014d80001e628180003248aa39207306505ab00000345a684245f012c0003f2000130400044648020cc2265b51cf9dec000026182a174a4815f16917914844df449201070050028585043280001328f8d2d20002ef198400000023726f00000000ef93a4284000065a4b8a3641f00027913228bf45918152228594b427b40000000000000000000000000000044c000000000000000018900009ea43380000006e8501000000069f213215400047d41f800000000051318e0c980db1f0830400073200000000000000001894046578456154c0007e900009501400000000000bec000000000145e00021b00000000001df053c2a20e812b80006cc00000025fd11640a0821ddcea259600008f85ee0003d200003dc2823f68a5d4a466f49d0000000000000000029229933c8000000000000164491e000000000000068524580b00008050000000fa67740001c340004664890f8800091e12380005e6000000144484267e000000000045352008100008e72e499e0192557242a2746524b6284962808252d4b11b945b27b13c703b47763083a31d3858251908e14e4106000000000000057a22f0f6870e4e41c81f740006ee0000000000a502fd00ac99664f06c0fdc72802a11e8b44aa40a54db19d417c8dd0fc19082584b30cc82dc15a84e1958b2c0000000001ba8d2c3070428c68e368b53d2a62c35c44f3a602d01585483c38af0d300440b0a93c72c4f7305023ccb40003f708780004440001fd4ffc00015c161c000000127a14c52800010186a032e0a6000148800077a06c800061a2334fe89bc21099908a95a06989b335c8000db0810002a1a52a43e903b80000005d800013b030a9130000ef40003cf0001f448103b2240800000000000000713b00003e10a6914e5a92dc13b80000a43de123049a5103399094e6c38a2a00d6d01200000008b00000001648854f1800040019340003a1000285d4781f600000900007061eb1efc3ea00000012accf69b509d81d4d5e89b15a91708f44b74f4072d2c80c52de2018c3e87b3ea800000001d3ae00003d07b950507c12b65812311fe0caa00000003900001930000d841ec65d49480014100000000000000000171042c0500a70309c6096a00029880004228fa00000000007481300bf8000000199000072400000000009720000000f703f600007300000009f232d89cc4f43ce4128ac920e93d180802488a8a102915d4a0200000000000000001c200010360de0001d880000000000e5
  | 19 => 0x3d3a90c0000000000000000000000000000097510080000002e401d23986e48df286800049407c0001660f320000002460000012385253c000690482a21d30c6fc00012f4bfe00010580000000003cf80010e80005020000000484000000000000032083ec0000004ed20485768ab00000382f669a3c08000c9c56731080001ce0003871730e3422b3848f7870c81f129831942a4583f29218cb800007c06b0e5082636c91d447891b4811874952932291866059a08c4398d745a84f30a692fc81825809ca030b683193ca962cf6441521f1f9cf1279134f21c445a8fc4ec8da80002c42439ebc0be5ef01e000020a0002b280006ec000000246400000049b0000c8a0a81dd1cb085c5414bb23dcabc04644b985140a19f0ca84bca409a019728c02189d4000287011c46b24b9df0d0e67c50717586d0a0340a02540000000cd0f980000511ac03340000004e38000eb66b21b3a3b80d80002f1000071a3240b18000d4e0003cf000100225100000000008b044300013be8da09d01f828a6c34e421c09ea3c62348240aba1d4306a00c2bc4544960fd09ca7004d700004e068d23e171871044d45c12a83ca5f329306c897684010ea33466c8b61d516346269820e88ad0ac08850001ab800099600014fc00087f4e500000004e800000000000000000000c520cf000000131a44b000215c5ba1fa071168c07c000000097c00000000028ec55c02702f24687f2000206932400000049d8b98000000000000000000000000011925610000000d7a0002e4012024414a000105800084c2c28f080000003601ee815c7e137d82ec81259c00000000007b61f29e4904e4a412600000e23830000000906000000000054c000275800108800000000000006d700009f8cce403033900093e8822f51340cca81110a25352702da346274ce9e0002f8975517a39b0ff8a84e44a1
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x106886390d20082543b08690041a218c4348020e10a621a40106a064d85200836031ec290041a8d906148020d40c830a40106c3631852008360318c290041389cc6148020cc4a630a4010660531852008351218c290041a810c61480209c4ed98a40106a064cc5200836031e6290041381d83148020d40c818a40106c0630c520083a02986290041e010c3148020a18e4a98878850c7454c32c428a3a2a618e21511c9530c710a34e7aa0818852a72d5040c42953a6a410621529cf5208310a18e4a98870850c7454c328428b39ea820c21499cb5410610a4ce9a90430854673d48218428c3a2a618421521c9530c210c1cc9316a68860c641885344287396a621a21451c45310d10a30e0298868860e6310f524428739ea819221439d3530c910a88e229864885487014c32442873a88619221431d4430c910c1cca218648860c6510c32443182a4c198a219414e60cc510cc0a5306628851673d50314428b3a6a618a21519cb530c510a2cea21862885147510c31442a339ea418a21c110f520c510e08862906288546750c831442a23a86418a21c1d50320c510e08a8190628863054987304432829cc3982219814a61cc110a34e7aa0608851a74d4c30442a5396a618221541c4530c110a34ea21860885187510c30442a539ea418221c210f520c110e1086290608854a750c830442a43a86418221c2d50320c110e10a81906088713540c430443882a06218221d0d48310c110e80a4188608844c735885404287396a621821459c75310c10a34e1a98860841c7359052042873a6a619021519c7530c810a94e1a986408514735504104292392a820821341cd60104109c0e4b0082084b0745803104270392c018821491d15208410a88e6a9042084b074580210426839ac010821461cd5410010a50e4aa080084d0735844004270392c2200214c5d44110010c62ca20880084b0745843004270392c2180214a1d15208010a90e6a9040084b074584200426839ac210021585d42108010cc2ca10840084b274991100426939cc888021389ca6444010964e6322200869064d8d10042593a4c688021349ce63440109c4e531a20086536518d1004349b20c688021a41906344010ca6ea31a20086937418d10043483a0c688021b0dc86344010d80e431a20086306494d100432831ca6880218c1905344010ca0c629a20084b27690d100434831c86880212c1d84344010d20c621a20087105310d1004350326c488021b018f6244010964e931220084d2739891004271394c488021a8d906244010d40c831220086c3631891004360318c488021389cc6244010cc4a63122008660531891004351218c488021a810c62440109c4ed99220086a064cc9100436031e6488021381d83244010d40c819220086c0630c910043a02986488021e010c3244010
  | 1 => 0x310c3c021e6418861649d2320c430b22e919062185c2728c8310c269bb2641886154dd5320c430b26e89906218590744c8310c2e13986418861b098c320c430e84a61906218782430c8310c3c0218641886164dd1650c430b20e8b2862185c372594310c2e0392ca1886154dd5640c430aa0eab2062185c372590310c2e0392c818861a4590640c4309a6ecaa062184d076550310c2e1b92a818861701c9540c430e22a82a0621855375588310c2c9ba2c418861641d1620c430d82c431062184d376548310c2c9ba2a418861641d1520c430e82a429062184d376508310c2683b2841886154dd5420c430aa0eaa10621878142108310c24c3a2c790861261d16388430934e7b22421849a74d8d210c24d3b08690861261d84348430c36ca21a42186186510d210c325b286490861921943248430d16c81924218688640c9210c329b286290861941943148430d26c818a4218690640c5210c24d3a6c610861329cb63084309a4e3b18421856075484210c2d03a24210861701cd2108430d80c6908421878043484210c28a38aa621e41431d1530cb20a88e2a9865905147454c31c828d39ea8206414c9c75410320a28e2a98871050e73d50428829338ea821441451d1530c620a30e8a9861105507154c308830b324c3a9a41851906114d20a2ce3a98869050c7214c43483142a4c1992419214e60cc920a1ce7aa0649050e74d4c32482a338ea619241439d4430c920a18ea21864906166310f514832331865a8a41c110c32d4520ac4e1990a290704430c8514828b39ea818a41459d3530c520a2cea21862905147510c314830b3288618a4185194430c520c8cca1906290644650c83148383aa06418a41c1150320c520c50a931660906485398b3048331310a398241469cf540c120a34e9a98609055271d4c304828d3a88618241461d4430c120e16a81906090708540c830482a939ea218241c410f510c120e8065a8860907104314430483a0190a218241549d4310c120aa0ea1886090713540c430483882a06218241151cd6115020a1ce5a98861051671d4c430828d386a621841431cd5410820a48e2aa084104c873580420827038ac0210412a1d1600c8209c0e2b00641051674d4c31082a3396a618841549c3530c420a48e8a8842105447354421082543a2c010841321cd6008420a30e6aa0801053071550400826439ac420041381c56210020a52ea21080106296510840082543a2c418041381c5620c020954e932240104ca73991200827138cc8900412a9cc6448020d10c9b1a40104aa7498d200826539cc690041389c66348020c96ca31a401068b6418d2008344320c69004192dd46348020d16e831a40106887418d2008361b88c690041b01c46348020c50c929a40106486394d2008314320a6900419218c5348020954ed21a40
  | 2 => 0xa821861641c55410c30b16e4b28861858872594430c2c9b8aca21861641c56510c30c32ca328861851b75588430c2c9b8ac421861641c56210c30d12c4310861851b75584430c2c5b92c221861621c96110c30d22c2308861849a7610d520c34821ec2a9061a410c6154830a50e8a90a41870843548520c2b038aa429061341c563d08309a0e2b1c84184d271d8d420c30db2886a10618619443508309a4e7b0a841869043d85420c348218c2a10614a1d54210830b10e6a1084185a071508420c2e138e8799061a490e618c830d208730c641869043586320c269388c919061a4992618c830d22c930c641869264586320c24d3b0869906186d94434c830d2087b0a641869043185320c2c5ba26419061621d1320c830b86e299064185c0714c8320c24d3a4c419061629d2620c830b12e931064185c271988320c2e0b8cc41906162dd1520c830b10e8a9064185c371548320c2e038aa419061325da420c830a96eaa10641868864508320c2e1b8a8419061701c5420c830b84e3a1864185c171d0c320c2c539c861906132dd9430c830a96eaa1864185c37150c320c2e038a8619061629cc430c830d14c6218641870a5310c320c2c5ba2ca19061621d1650c830b86e2b2864185c071594320c2a5baac819061521d5640c830b86e2b2064185c071590320c344b20c81906132dd9540c830990ecaa064185c371550320c2e038aa819061c2550540c830a96eab08641858b74584320c2c43a2c219061b0584610c830934ec21aa21868843d89510c344218c4a8861329d83254430d16c8192a218688640c9510c2983a2a228861c410d5114430ac0e4a88a21874032544510c264392c7a0861321c96390430994e5b1a821861b6510d410c30c32886a0861329cf6250430d1087b12821868843189410c2653b064a0861321d83250430c96ca1928218648650c9410c2983aa8220861641cd4110430b40e4a08821878032504410c2e13968798861e010f32cc430b24e91966218782430cb310c3c02186598861a290e628c430d108731462186884358a310c3453266518861a2990328c430d12c819462184ca72192310c345324c518861a2592628c430d14c8b14621849a7610d310c30db288698861a210f624c430d108631262184ca760c9310c325b286498861a2d90324c430d10c81926218593744c4310c2c83a2621886170dc9310c430b80e4988621849a74984310c2c93a4c218861645d2610c430b84e530862185c172984310c2c9ba2a218861641d1510c430b86e4a8862185c072544310c268bb4821886154dd5410c430d20c8a0862185c372504310c2e03928218861709cb430c430b82e5a1862185927390c310c269bb2861886154dd5430c430b86e4a1862185c07250c310c2c93988618861a498c430c430e24a6218621878243cc8
  | 3 => 0x8b6150040d26c630a8020690631854010351b10c2a0081a81886150040964e630a8020632531854010351990c2a0081a80c86150040964ed98a802069063cc5401035031662a00812c1d83150040d20c618a80206a0620c540103c019062a00818a9506250330c64a830a819852a72d5040cc29938ea820661469cf5495330a54e5aa4a99853271d5254cc2953a6a529661589c75294b30a56eaa1085985887350842cc2d038a8421661a410e618cb30b84e3a18659853274d4651cc2b1396a328e614cdd54110730b20e6a0883985a07250441cc3c02186598e61a210e628c730d14c819463985c272d0c31cc3c021e6418e61649d2320c730f04861906398780430c831cc2b1baa4210e61681d12108730b80e6908439854671d0e528c30b2a4c319461519c4540ca30e0887294a3187044354a518c3832a06528c61c15503294630a8ce5a1ca31870443cca518c28b3a46528c61c190c3294630e0886194a31870443949518c3832a064a8c61c110c3254630e08872966318706540cb318c3072a4c518c6183992528c630e0c87290631870443948318c38221aa418c61c1953320c630e0ca81906318705540c8318c2a3390a818c61c1952520c630e0aa9290631870654548318c2873a8861926183994430c930e0886196a298704430c8514c28b3a88618a6185994430c530e0887a90629870443148314c2a33a86418a6191994320c530e0ea81906298704540c8314c286392ca21861451c56510c30b16e4b00861858872580430c2c9b8ac021861641c56010c30b16e8b00641858874580320c2e1b8ac019061701c5600c830b26e8b00621859074580310c2e1b92c018861701c9600c430c1cc8194a018616640c6500c264392c720061341c56390030c92ca1948018651650c6400c265396c6a0061349c76350030d1087b12801862854189400c344218c4a0061329d83250030e10a8192801869043d85400c360196c2a00618c1506150030d208630a80186c032185400c2693b062a0061c41503150030d86c418a80186c0620c5400c294392a8200614c1c55410030a32ea21880186884398a300c34421ac518061a2990328c030d12c8194601869043986300c360194c318061a410d618c030d8064b0c6018692640c6300c348b206318061b0988318c030d82c418c601868843d89300c344218c498061a2d90324c030d10c8192601869043d85300c360196c298061a410c614c030d806430a6018693640c5300c3483206298061b0d88314c030d80c418a60184ca73d89540c26939ec2aa0614a1c95415030a60e2aa0a8186c262987430c360b14c3a1861b098961d0c30b16e4a1886185887250c430c2c9b8a8621861641c54310c30b14e5320861858972990430c2c938cc821861645c66410c30b16e4aa0861858872550430c2c9b8a
  | 4 => 0x86e0aa06418dc070550320c782aa0a81906351dd5600c831b0ee8b006418d8474580320c760b00c019063259d84354031d0887b12a018e8443189500c6633b064a8063a1d903254031d08c8192a018d3074540500c78821aa028063581c95014031e8064a80a018d187054c43c86863a2a619643521c1530cb21a2ce7aa08390d3270d5041c868c382a621c43439cf5410a21a54e1aa08510d147454c31886a8382a618c438699260d4d21c30c8300a690d1a70d4c43487122a4c3992439114e61cc921a1ce7aa06490d0e74d4c32486a5386a619243439d4430c921a18ea2186490e245498b314872229cc598a43459cf540c521a2ce9a986290d5270d4c314868b3a88618a43451d4430c521e0ea81906290f04540c8314870d31887a82439298c32d4121e1086196a090e52630c7504878821863a8243d00c831d4121ac4e3990a090f08430c850486b13966228243c410c3114121e8064188a090c58735805408687396a621843459c75310c21a34e1a988610d0c735504208694382a821043311cd61108219c0e0b088410ca4745843208670382c219043451cd5410421a60e0aa08210cc4735884108670382c420843495d44210421c4aca2108210ca4745883108670382c418843299d2644842198ce73224210ce2709912108653398c890843a1193634842194ce931a4210cc67398d2108671384c69084391d946348421d0ec831a4210e846418d2108723ba8c690843a1dd06348421d08e831a4210ec37018d2108760380c690843891925348421c88c729a4210e246414d2108722318a690843299da4348421d08c721a4210ca47610d21087423188690843c114c4348421d40c9b024210ec063d812108751b20c090843a81906048421d86c63024210ec0631812108671398c0908439894c6048421cc0a63024210ea2431812108750218c090843431c95310f40a28e2a9887a05447154c32d02a2392a618e81511c5530ca40a88e4a986320646629875350322310c229a818614e6090d40a1ce5a9886a051671d4c435030731887a92814a9c24314940a8ce3a9864a060e6510c325030b31887a8a819198c32d4540e0886196a2a05327090c51503822186428a81519cb530c540c2cca21862a054673d48315038221ea418a81c110c520c540a8cea19062a0544750c831503233286418a8191194320c540950e4b0086204b071580431028639aa421081491c55210840930e6b0084204b071580421028a39aa220881491c95110440930e6b0082204a872580411030db28c6a008186dd46350040d16e431a80206887218d4010349b88c6a0081a41c46350040c30c729a802068863d894010345b18c4a0081a218c6250040954e6312802062a5318940102553b664a0081a218f3250040950ec1928020688630c9401034831ec2a0081a81
  | 5 => 0x8e904398232cc6e138686196634c9d35094331ac4e5a84a198d4a70d0e528c70d2a4c119463529c0540ca31e1087294a118f084354a508c7852a06528463c25503294231a94e5a1ca118f0843cca508c68d3a46528463c290c3294231e1086194a118f0843949508c7852a064a8463c210c3254231a1cea2186498e0e6510c324c78421865a8263c210c3214131a18e4b288618d8772584430c6c2392c22186364dc16110c31b20e0b088618d8774584320c6c23a2c21906370dc1610c831b80e0b086418e0e640ca510c662392c720863341c16390431c8aca1948218cc672d8d410c669386c6a0863a110f6250431c48a83128218e8443189410c6633b064a0863c11503250431d2087b028218ec032d81410c7182a0c0a0863a410c6050431d80643028218d2472550410c698382a820863455d44310431d08873146218e844358a310c7433206518863a1590328c431d20873046218ec032982310c74821ac118863b00c9608c431d0887b126218e8443189310c743b206498863a1190324c431d2087b026218ec032d81310c748218c098863b00c8604c43198ce7b12a818cd273d81540c692392a82a0634c1c15415031d84c53068618ec162983430c761312c1a186361dc94310c31b08e4a188618d937050c430c6c83828621863619ca6410c31b0ae53208618d9270990430c6c8b84c82186361dc95410c31b08e4aa08618d9370550430c6c8382a82186361dc96510c31b08e4b288618d9370594430c6c8382ca21863855946510c31a2eeab108618d9370588430c6c8382c421863a15886210c31a2eeab008618d8772580430c6c2392c021863a45806010c3192cec21aa418e9043d81520c748218c0a9063491d15214831e0886a90a418d6070548520c668382c7a1063341c163908319a4e1b1a8418e176510d420c70a32886a1063349cf6050831d2087b028418e9043181420c6923aa8421063611cd4210831b40e0a108418dc270d0f320c74921cc119063a410e608c831d2086b046418cd270192320c749324c119063a4592608c831d24c8b046418c967610d320c70bb288699063a410f604c831d20863026418d87744c8320c6c23a2641906370dc1320c831b80e09906418c9674988320c6c33a4c419063615d2620c831b84e13106418dc170988320c6c3ba2a419063611d1520c831b86e0a906418dc070548320c662bb4841906351dd5420c831d08c8a106418dc370508320c6e03828419063709c3430c831b82e1a186418d867390c320c663bb2861906351dd5430c831b86e0a186418dc07050c320c6c33988619063a198c430c831e0ca62186418d8774594320c6c23a2ca1906370dc1650c831b80e0b286418d4775590320c6a23aac81906370dc1640c831b80e0b206418e8564190320c663bb2a819063311d9540c831b
  | 6 => 0x310b07b28c6a108583dd46350842d0ee231a84216847118d4210b45b80c6a1085a21c06350842c18c729a842168463d854210b43b18c2a1085a118c615084294ce630a8421626531854210b4431ec0a1085a81876050842d16c63028421688631814210b51b08c0a1085a81846050842954e6302842162a531814210b132a0c2a16658a9506050b32a4ce3aa0859952a70d5042cca8739ea92a665499c75495332a54e1aa4a99952674d4651ccab1386a328e654a9d35094332ac4e3a84a19955270d0e518cb8821ca328465c410d5194232aa4e3a1ca11971043945508cac3b8ac421865611c56210c32b16e0b10861958870588430ca6238ac721065321c1639083298ce3b1a84194ca70d8d420cb4221ec2a1065891506150832d088630a841968843d81420cb142a0c0a1065a210c6050832a48e2aa0841952870550420ca86ba88621065a110e618c832d0886b0c641968843982320cb4421ac119065a110f614c832d088630a641968843d81320cb44218c099065319cf6155032994e7b02a81952471550540ca94382a82a065b098660d0c32d82c330686196c261583430cac3b8a8621865611c54310c32b16e0a1886195887050c430cac338cc821865615c66410c32b14e1320861958970990430cac3b8aa821865611c55410c32b16e0aa0861958870550430cac3b8aca21865611c56510c32b16e0b28861958870594430cb06b28ca2186543dd56110c32b16e0b08861958870584430cb42b08c22186543dd56010c32b0ee2b00861958471580430cb44b00c021865239d84354432d1087b02a21968843181510ca923a2a228865c110d5114432ac0e0a88a21948e7610d500cb4221ec2a8065a110c6154032a50e8a80a01970843540500cab038aa028065431c95310f41a30e0a9887a0d487054c32d06a4382a6194839298a60d4d41c90c4300a6a0e14539864350687396a621a83469c35310d41c1cc621ea4a0d267190c52506a5386a61928383994430c941c34c621ea0a0e4a630cb505078421865a82834c9c64314141e1086190a0a0ca4725844310658382c221883431cd5210841a50e0a908420c94735844210658382c22108385d946350441c2eea31a8220e877218d4110742390c6a0883a4dc06350441d20e031a8220e146394d411074231ec4a0883a1d8c6250441d08c63128220ca6731894110713298c4a0883299db3250441d08c79928220ca4760c9411074231864a0883a418f6050441d40c5b028220e93631814110748318c0a0883a8d886050441d40c43028220cb2731814110719298c0a0883a8cc86050441d40643028220e265418941cc7192a0c0a0e63499cb5410731a64e1aa08398d1673d5254cc693396a92a6634c9c35495331a4ce9a94a598d6270d4a52cc693baa8421663611cd4210b31b40e0a10859
  | 7 => 0x2a039c7d441800000040c51d1f51011c48800710c4620adc4906d8424630114838b80958af01ecc008242ec000180000fa46e86008d8498a68c4c8c09746d07bd1547c4c6090c75d15d004fc90c8d186b0f784488a05511f08f0e6c2c918d17c0e899c1bc4583e4000590934000c8c0005d00002109acb241d020829d1ad1187147e0a45035164fe501c92068c6780bc78cf24d583fcb84000b2d2883381184fc098970bdcb39038a88000000864d651f8d40930f6866c8680e500c87c3a5234c0c0600001e00e0ff4bb4f851e8d14e4d290eb5224760ec007cd94938cfceec698ff04202784a084cbcc52cd3c2b015d150000aa491cd1c6c0de90a04f8814c6cc84a04d50abc4a4ec41605990149e8000028d0ce94ef0a700008d456c2ac5490c0148324001204b3035c000001158c98330ea0d310d4f581b925cca4e58b090e4000f142280100101001a0000f81300c00c000010001680580000000017002000018230080080680681300000c00002000000030000040040000400e0006b8160000000580c0000080200201c00c0582a0000040980400201c0101d0040040081e01c0001280000202c010020060d40182400003c0080100400c030010000041200202206405000006014000050020082000700e0080380c03c0040180107c000008070300000282500a0640680300600c038050080000181100000c0a81d00002c068170000140085400001c0980001200800800000000008030000000080003e000000070040080281d07c000008010200000081a00800005800014014218080080040480000e034028060040180000100e028038000100001b8000520240080002601c1900102c004070000180000002d00600001006018008018120340040000f034000038000620080580100400802801002000060180040200100000e060018130060f40080100200000000008000118010001440080500801c0f8000260000e80003401c008030000080201d04a028028010080140600d0980000200c0020880280e01e0180400100001c03805000014030060060000980000c0080280900200c08002066000058000180042c000058000000020080340180601606c0100800a000000000040000a00601600c160010020240381200002c0300100600c01001000008008000020000f8040000240280204e00001004002000000030200081e8000080100052671d4a5290e95386a529487499cb5194643a64e1a8ca321d2a72d425090e9938ea128487491c55214843a50e0a90a421d24725445110e98382a2288874a1c95014043a60e2a80a021d147154c43d0a8c382a621e859498660d4d42ca0c2300a6a160c5398a4350a8b38ea621a85469c35310d42c2cc621ea2a15267290c5150b0d31887a82854a9ca4314142948e2b1086214a8705884
  | 8 => 0x7929891848c7640d416857900000cca038852893cbb08c4dc83f86b5060b34000914a1017828c440000f40000000378274e48ef8e1126800127507c2d024c0000005591211d05ecbd923c000b28b48184c580010a8ed11ecf4c6447cc00124d14ca00efce241c114882ca7c4550b000097cbb89a0b4c0000186085a8bd43085145200a40000000005312548aca8d208e40444000844b888088300a8000000828fd0a0c3580008c800071caecf983981945100005b8dd4554be44307d8ab411c000000a9476c564c48670aaca3cea898c0008bccd8c150785403cc2d4259069110f28000000000000b10bc09646183bc79ca84001198134d250cc5801907fc02c12cead138c9c5d425cb6125072c704508f0099847506c5a038c174b512387b03a8d90df4594b14a4806ce3c5fc2342046342b80d908c8a48712209fc74818c8f8021168bd03b0bfc4ad29c4d4f74848a987084e0f3519c0000010f40c80b0124001260ee042c5bc8110d03808a82402f528c1dc00047ca644b45390f800040474c4dcc382452640f8738e08a9cce4068e9c5f843465cca9070038e0400009c4a862cbc8a581ccd6c4c058cc241f0b406acd54fdd098000e8cd10354000de000023c0842dc0004380007400002a8000000f70000e28ae800101109c298000000000410fb11c8cf41fc0000008841d42c0300df0000d9800000081c260fd4a74be02680011311bd0b80009c91a8000acc72022c0006c8000c288e921c4848901e84d0cacf391a000000000111ce1888c27000000041cd7d1cc6f12a04282e8805258094fe07f48dc5e8fd8000ce00811dc90000046c1088789500006e46dd10c224280ad503cac43d0f3054c3907a800000019c0ccb98d2c9d4c90724d440900009408947e4c74ab90841a0768b944ecb3cb8cd8c000fec04c83c800a18001244e98e0cc212700010e80008b1200b449e48200000a0684ddc0002cc000000e70a306ccba4360c7c858fc0dfc7544f118514446859cc94dd09443f05dc464ac0eb0000000c2ce307d0088a1c90877c00000000078010cb74000c780000006f927d0410a5088f0420d104138198c310f0b68798904dc52a87b4568000328000c08d280000002f0000000504a082142841882205cc0000000000001542300005c89a51e452438401c954794000ac8584f906ec000000001214000000364744e8821cf449810b41c4cb4b70ad8d84f60c89180faccc47741a4898368034fa81ad280519190d6105c27c874948e601500d080c050f4800069c5345d8cb0cf122d074e340004d8e5d10889c2501e4000314588fc4000c180641f8000e6800085070c7f834c8e4d20f1d01800014c0011c05f4a38f500000010809c4000688f64000b6c000f6d20c924e00f3c000000f1800037445c001228674834290680ce8c1cdd81d8
  | 9 => 0xc34ec80acba80000000002bc7ecea5160f08e8424800014400102c9b47780483e8b791b05ac0f5248c3c9a8e507aced4c10ecc1110441582c516cf8c9d8218a340ec000b5c6240741711d80000004500b8c40ebcdb8008d9cb580012841f40000012186a4e443403dcf2d174d08000d004cc318ad098461cb0c000d044b805cc440010588d00006c45000b4af9170fb4dad140bf8fbc000e54000bf46386fcee921000000000112c000000b00d88a4cd70254d806b8bc4165128fe905109416c0f00007a00141a8c70edce38000408a6c120df87f03f43a104c0400fc000b7c96cdcc000000ccd09060c0007580006480010480003340000000007840000007a4000dbc00124036c0001300011e0ffc00013c03ccd4b6467cb9c0000000000001408ec1b4650000cdc00092805463d05408c2884bc370c80ef4000000cc0470da09f8c6800073c0000005445f0045134000000000000994000000a150d90ec0000000011888b4f0c350cc886c560478cb80002d8af46a0fa07c03ec2f8000344000e20668000000cd000044cae4000304001125194ba09dc000000db0480000000e800000004011d46940002b4afc7701b11785a47e83c000000031c00033c5b46400000003483ad008d5c664001230fb86d495c0049b09903950645b0cf84e40c053c3b864c92d0282e51a4a90d4d1b8100e90e650dc5c48b82003b49ecd349882a4570058710414aa0eb9024a604888f4c54f100dc50cf5c6041284b08fcc051b4de4bacd48000d784e89b8f7c9bcf88841278e148cc4c437ce789e07311fc4946bca78000960f203106f402485d0fc000000e74bf030c9f4c509f00007c8000f94000b900004f4b54be8b18000860a5094c7909792a41c8becdb4a24dc0f9c3e00000006587b83c913c17c7510e06282fc57526c9d0910ff9294690f542e09c0000f80000e2ca40614010000b04000ae05e0da4000fcca289cc660d68d74a80238dec6a843c000888c64a20000a2c3c47186547345c04611143208e057c610d39020ee4ceca54a5c32c264ed8c5caa8968788e1cab085426cb201043d42940010307dc6e07004c80c50bd0ac728000030b1c55c818cbc49cda8000e7c5e43d8bbc0
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x4854007646000066002a3c0000820018004a6a0000008000720028000000001a000032401c04680038000000000014002200000e3664000000000000007a00004e0612342c7e305a70160000000000000000000000003e00007426000a00001e2e6c08025c005e24440c3a50000062004c0000005800207c000000566052006e0000004200000078001000000401000100000000020804010103000000000500c80711c06350842a80805846110c32a80815806010c32d00431c15114432d00431c55014032c80721c06350441e00540c86050431a80805886210c31a80825806010c31d00431c15214831c80641c1420c831a0485590640c831a8080590640c831a0486550540c831b0080550540c831a8084580600c831d00431c95014031d00740c95014031c80741c06348421c047614c4348421e005310c6048421c80721c46350040a80860c83150040c80760c83150040e00540c86150030e00541883150030a80815886210c30a80825846110c30d00431c55214830c80641c5420c830a0885590640c830a8081590640c830a0886550540c830b0081550540c830a8084584610c830d00431c95114430d00740c95114430980870c94110430d00750c94110430c80641c9410c430a1085590640c430a8082590640c430a1086550540c430b0082550540c430a8084588620c430b0084548520c430a8086508420c430b0085508420c430c407518d2108430c807418d21084309808710d2108430d007510d2108430c80741c46348020c087614c4348020e005310c6148020c407614c3148020e006414c3148020a808610c3148020c807610c3148020c80741c86344010c107614c4344010e005310c6244010c407614c3244010e006414c3244010a808610c3244010c807610c3244010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1140
  | 4 => 2647
  | 3 => 1195
  | 2 => 66
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (i*5) 5
  | 6 => packedAt s5K6 (i*16) 16
  | 5 => packedAt s5K5 (i*27) 27
  | 4 => packedAt s5K4 (i*38) 38
  | 3 => packedAt s5K3 (i*49) 49
  | 2 => packedAt s5K2 (i*60) 60
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (880+((h/16+packedAt s5K6 (768+(h % 16)*7) 7) % 90)*7) 7
  | 5 => packedAt s5K5 (34960+((h/380+packedAt s5K5 (30780+(h % 380)*11) 11) % 1505)*12) 12
  | 4 => packedAt s5K4 (111170+((h/882+packedAt s5K4 (100586+(h % 882)*12) 12) % 3843)*13) 13
  | 3 => packedAt s5K3 (62933+((h/398+packedAt s5K3 (58555+(h % 398)*11) 11) % 1435)*12) 12
  | 2 => packedAt s5K2 (4136+((h/22+packedAt s5K2 (3960+(h % 22)*8) 8) % 138)*8) 8
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffffdfe0ffffff801fffffffffe03fffff0fff
  | 1 => 0xffffefff07ffffffe007ffffffffc07ffff0ff
  | 2 => 0xfffff7fff83ffffffff801ffffffff80ffff0f
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0x7bffffc1fffffffffe007fffffff01fff0
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xffffa03e108425f684a92a5896e815ab970777
  | 1 => 0xffff9042f1084a92bda24ca92b6ad035ab70bb
  | 2 => 0xffff888427909324c93769324dad5aa0cdbb0d
  | 3 => 0x10842211c4711c471c471d1a34670ddde
  | 4 => 0x610843de0781e0781f87e1e3c7881eee0
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xe8008000e8008000e8008000e8008000e8008000e8008000e8008000e8008000e8008000e8008000e8008000e8008000e8008000e8008000e8008000e8008000, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_12220
namespace PEqualNP.Outside.L_meta_12220
open PEqualNP.Outside.L_meta_12220.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x61d00640006400f800000038080163400000000000f12566d798664c00000800002e0002e001c0230a85380740c0aa000003100014000000036720000000c000d0000a0000005806e00d000000000120000000000002a0000000203000000026000000f76087000000b1c440000000016804a414a4140003500000000000000004400000000100010000000500010000010000060001000100ffd5003fe5400ff55003fc54017fd4c05fe53017f54c05fc5300ffd0c03fe4300ff50c03fc43017fd4805fe52017f54805fc5200ffd0803fe4200ff50803fc42007fcc801fe32007f4c801fc32017fd4405fe51017f54405fc5100ffd0403fe4100ff50403fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21017fd4005fe50017f54005fc5000ffd0003fe4000ff50003fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42004ffcc210027fc6108013fd3084009fe1842004ffc8210027fc4108013fd2084009fe1042004ffc4210027ee210800ffb1084015ffb2a200abfd9510006feca880027f6544015ff32a2002bf99510057faca8802afd6544015fe32a2002bf19510056f8ca8800a7c6544013ffb222009bfd91100077ec888002bf6444013ff3222001bf9911004ffac888026fd6444013fe3222001bf1911004f78c888006bc6444013ffaa22009ff9511004ffaa888027fc5444001ffb1a2000bfd8d10007bec688002df6344001ff31a2008bf98d10007fac688002fd6344001fe31a2008bf18d10007b8c688002dc6344015ffa9a200aff94d10057faa68802bfc5344013ffa1a2009ff90d1004ffa8688027fc4344001ffb122000bfd8910007dec488002ef6244001ff3122007bf98910007fac488002fd6244001fe3122007bf18910007d8c488002ec6244015ffa92200aff94910057faa48802bfc5244013ffa122009ff9091004ffa8488027fc4244001ff9922000ff8c910007fa6488003fc3244015ffa8a2003ff94510057faa28800ffc5144013ffa0a2003ff9051004ffa828800ffc4144001ff98a2003ff8c510007fa628800ffc3144001ff90a2003ff88510007fa428800ffc2144015ffa822004ff94110057faa088013fc5044013ffa022004ff9011004ffa8088013fc4044001ff9822004ff8c110007fa6088013fc3044001ff9022004ff88110007fa4088013fc2044007ff8822003fec4110027fc2088013f61044009ffb282004bfd9410027fcca0800afe6504009feb282006bf59410027f8ca08012fc6504009ffb202004bfd9010027fcc808006fe6404009feb202005bf59010027f8c808012fc640400bffaa02005ff9501002ffaa808017fc5404009ffb182004bfd8c10027fcc608022fe6304009feb182000bf58c10027f8c608012fc630400dffa982006ff94c10037faa60801bfc530400bffa182005ff90c1002ffa8608017fc4304009ffb102004bfd8810027fcc40801efe6204009feb102000bf58810027f8c408012fc620400dffa902006ff94810037faa40801bfc520400bffa102005ff9081002ffa8408017fc4204001ff9902000ff8c810007fa6408003fc32040077f3082003ffd441001ffca20800ffd5104007fe2882003ffd041001ffc820800ffd4104007fe2082003ffcc41001ffc620800ffd3104007fe1882003ffc8410007ee420800ffe2104007fe9082003ff0841001fe84208012fe6004009ffa802004ff94010027faa008013fc5004009ffa002004ff90010027fa8008013fc4004009ff9802004ff8c010027fa6008013fc3004009ff9002000fec8010027fc4008013fd2004009fe1002004fe08010027fe2008013f71004009ff0802004fe84010027fa2008013f51004007fc8802000fc44010
  | 1 => 0xffe320800ffe9904007ff0c820027fec210013fe61080077f3084004ff58420005fac210013fc6108021ffa884010ff94420087faa210043fc510801fffa08400fff9042007ffa821003ffc4108001ff9884000ff8c420007fa6210003fc310800fff9084007ff88420007dc421001ffd210800ffe1084007fb08420025fcc010013ff5008009ff2804004ff54020027f8a010013ff4008009ff2004004ff50020027f88010013ff3008009ff1804004ff4c020027f86010013ff2008009f79004004ff88020027f44010013fd2008009f69004007fe48020007d2401000fff65c40077fb2e2003ff99710015fccb8800ffd65c401d7eb2e2003ff1971001df8cb8800fff64c40077fb262003ff9931000dfcc98800ffd64c401b7eb262003ff1931001df8c988037ff54c401bff2a6200dff5531006ff8a98800fff63c40077fb1e2003ff98f10045fcc78800ffd63c40017eb1e2003ff18f1001df8c78803bff53c401dff29e200eff54f10077f8a788037ff43c401bff21e200dff50f1006ff8878800fff62c40077fb162003ff98b1003dfcc58800ffd62c40017eb162003ff18b1001df8c58803bff52c401dff296200eff54b10077f8a588037ff42c401bff216200dff50b1006ff88588003ff32c4001ff1962000ff4cb10007f8658800fff51c4007ff28e2003ff5471001ff8a38800fff41c4007ff20e2003ff5071001ff8838800fff31c4007ff18e2003ff4c71001ff8638800fff21c4007ff10e2003ff4871001ff8438803bff50c4009ff286200eff54310027f8a188037ff40c4009ff206200dff50310027f88188003ff30c4009ff1862000ff4c310027f86188003ff20c4001fd9062004ff88310007fa4188013fc20c4001fc1062004ffd9610025fecb08013fe65840057f32c2004ff59610065facb08013fc65840097e32c2004ffd9210025fec908013fe64840037f3242004ff5921005dfac908013fc64840097e324200bffd521005ffca90802ffd5484017fe2a42004ffd8e10025fec708013fe63840117f31c2004ff58e10005fac708013fc63840097e31c200cffd4e10067fca708033fd5384019fe29c200bffd0e1005ffc870802ffd4384017fe21c2004ffd8a10025fec508013fe628400f7f3142004ff58a10005fac508013fc62840097e314200cffd4a10067fca508033fd5284019fe294200bffd0a1005ffc850802ffd4284017fe2142000ffcca10007fc6508003fd3284001fe1942009bf58610067fea30800ffe5184019fea8c2003ff1461005ffe830800ffe4184017fea0c2003ff10610007fe630800ffe3184001fe98c2003ff0c610007fe4308003f72184007ff10c2000ff4861001ff84308003f421840097f3042004ffd4210027fca108013fd5084009fe2842004ffd0210027fc8108013fd4084009fe2
  | 2 => 0x2009ffea91004ffe5488027feaa44013ff15220027fec710012ff6388009ff31c4008bf98e20027fac710002fd6388009fe31c4004bf18e200a7fea710053fe5388029fea9c4014ff14e2009ffe871004ffe4388027fea1c4013ff10e2008dfac510053ff528800fff2944014ff54a2003ff8a51004fff428800fff2144013ff50a2003ff88510003ff328800fff1944000ff4ca2003ff86510013ff6188009ff30c4003bf98620027fac310002fd6188009fe30c4014ffd46200a7fca310053fd5188029fe28c4013ffd062009ffc831004ffd4188027fe20c4000ffcc620007fc6310003fd3188001fe18c4007ffc8620007fc4310003ee2188001fe90c4007ff08620007d84310012fe6088009ffa844004ff94220027faa110013fc5088009ffa044004ff90220027fa8110013fc4088009ff9844004ff8c220027fa6110013fc3088009ff9044004fbc822003ff6411004bff65480257fb2a4000dfd9520004feca9004bfe65480057f32a4012ff59520095faca9004bfc65480057e32a4012df19520014f8ca90047ff64480237fb224000efd91200057ec890047fe64480037f3224011ff5912008dfac890047fc64480037e3224011ef1912000d78c890047ff5448023ff2a24011ff5512008ff8a890003ff63480017fb1a4000f7d8d20005bec690003fe63480117f31a4000ff58d20005fac690003fc63480117e31a4000f718d20005b8c69004bff5348025ff29a4012ff54d20097f8a690047ff4348023ff21a4011ff50d2008ff8869004bff524800fff2924012ff5492003ff8a490047ff424800fff2124011ff5092003ff88490003ff324800fff1924000ff4c92003ff86490003ff61480017fb0a4000fdd8520005eec290003fe6148001feb0a4000ff1852001df8c290003f461480017a30a4012ffd4520097fca29004bfd5148025fe28a4011ffd052008ffc8290047fd4148023fe20a4000ffcc520007fc6290003fd3148001fe18a4007ffc8520007fc4290003fd214800ffe10a4012ffd4120027fca09004bfd5048009fe2824011ffd0120027fc8090047fd4048009fe2024000ffcc120027fc6090003fd3048009fe1824007ffc812003ff64090013fe2048009f71024004ffd9420025feca10013fe65080057f3284004ff59420085faca10013fc65080097e3284004ffd9020025fec810013fe64080037f3204004ff5902007dfac810013fc64080097e320400fffd502007ffca81003ffd540801ffe2a04004ffd8c20025fec610013fe63080117f3184004ff58c20005fac610013fc63080097e3184010ffd4c20087fca610043fd5308021fe298400fffd0c2007ffc861003ffd430801ffe2184007bf9882003ffea41001ffe520800ffea904007ff1482003ffe841001ffe420800ffea104007ff1082003ffe641001
  | 3 => 0xeb0a6000ff1853001df8c29806bff514c035ff28a601aff545300d7f8a298067ff414c033ff20a6019ff505300cff88298023ff314c001ff18a6000ff4c530047f86298003ff214c001ff10a6000ff48530007f8429806bff504c009ff282601aff54130027f8a098067ff404c009ff2026019ff50130027f88098023ff304c011fd9826004ff8c130027bc6098013ff650c0097fb286004ff99430015fcca18013fd650c0317eb286004ff19430025f8ca18013ff640c0097fb206004ff9903000dfcc818013fd640c02f7eb206004ff19030025f8c81805fff540c02fff2a06017ff550300bff8a818022fe630c011ffa986008ff94c30047faa618023fc530c011ffa186008ff90c30047fa8618023fc430c009ffb106004ff9883003dfcc418013fd620c0017eb106004ff188300c7fea418063fe520c031fea906018ff148300bffe841805ffe420c02ffea106017ff10830047fe6418023fe320c001ef1906008ff4c830047f86418023dc320c009ffb086004ff9843001dfcc218013fd610c0017eb086004ff184300c7fea218063fe510c031fea886018ff144300bffe821805ffe410c02ffea086017ff10430047fe6218023fe310c001ef1886008ff4c430047f86218023dc310c001ff9086000ff88430007fa4218003fc210c0097f3006004ffd40300c7f6a018013fe500c009fea806004ff14030027f0a018013ff400c02ffda006004ff90030027fa8018013fc400c009fc2006004ffcc030027be6018013fe300c009fd1806004ff4c030027ba6018023f9300c00fffb2e4007bfd972003ffccb9000afe65c800ffeb2e4016bf5972003ff8cb9001efc65c800fffb264007bfd932003ffcc990006fe64c800ffeb264015bf5932003ff8c99001efc64c802bffaa64015ff953200affaa990057fc54c800fffb1e4007bfd8f2003ffcc790022fe63c800ffeb1e4000bf58f2003ff8c79001efc63c802dffa9e4016ff94f200b7faa79005bfc53c802bffa1e4015ff90f200affa8790057fc43c800fffa964007ff94b2003ffaa59001ffc52c800fffa164007ff90b2003ffa859001ffc42c800fff9964007ff8cb2003ffa659001ffc32c800fffb0e4007ff9872001dfcc39001ffd61c80017eb0e4007ff187200b7fea39005bfe51c802dfea8e4016ff147200affe8390057fe41c802bfea0e4015ff10720007fe6390003fe31c8001fe98e4000ff0c72003ffe439001ffe21c800ffe90e4007ff087200b7fea190013fe50c802dfea864004ff143200affe8190013fe40c802bfea064004ff10320007fe6190013fe30c8001fe9864004ff0c320027fecb10012ff6588009ff32c4002bf99620027facb10052fd6588009fe32c4004bf19620027fec910012ff6488009ff3244001bf99220027fac91004efd6488009fe3244004bf192
  | 4 => 0x883fe5008441fea804220ff140210fffe801087ffe400843ffea00421fff10021047fecb98022ff65cc011ff32e6002bf99730047facb9807afd65cc011fe32e6008bf19730047fec998022ff64cc011ff3266001bf99330047fac998076fd64cc011fe3266008bf193300effea998077fe54cc03bfeaa6601dff15330047fea798023fe53cc011fea9e6008ff14f30047fe8798023fe43cc011fea1e6008ff10f30047fec598023fe62cc00f7f3166008ff58b30005fac598023fc62cc03dffa96601eff94b300f7faa59807bfc52cc03bffa16601dff90b300effa8598077fc42cc011ff9966008ff8cb30047fa6598023fc32cc011ffb0e6008ff9873001dfcc398023fd61cc0017eb0e6008ff187300f7fea39807bfe51cc03dfea8e601eff147300effe8398077fe41cc03bfea0e601dff10730047fe6398023fe31cc011fe98e6008ff0c730007fe4398003fe21cc001fe90e6000ff087300f7fea19807bfb50cc009ff286601eff54330027f8a19807bf850cc03bffa06601dfed0330027fc8198077fd40cc009fe206601dfe10330027fecb18012ff658c009ff32c6002bf99630027facb18072fd658c009fe32c6004bf19630027fec918012ff648c009ff3246001bf99230027fac91806efd648c009fe3246004bf192300dffea91806ffe548c037feaa4601bff152300cdfac718073ff538c011ff29c601cff54e30047f8a71806fff438c011ff21c601bff50e30047f88718013ff628c009ff3146007bf98a30027fac518002fd628c009fe314601cffd4a300e7fca518073fd528c039fe294601bffd0a300dffc851806ffd428c037fe2146008ffcca30007fc6518003de328c001fe9946008ff0ca30007b86518013ff618c009ff30c6003bf98630027fac318002fd618c009fe30c601cffd46300e7fca318073fd518c039fe28c601bffd06300dffc831806ffd418c037fe20c6008ffcc630007fc6318003de318c001fe98c6008ff0c630007b86318003ff218c001ff10c6000ff48630007f84318012fe608c009ffa846004ff94230027faa118013fc508c009ffa046004ff90230027fa8118013fc408c009ff9846004f7cc230047f6611806bff654c0357fb2a601aff99530015fcca9806bfd654c0357eb2a601aff19530015f8ca98067ff644c0337fb226019ff9913000dfcc898067fd644c0337eb226019ff1913000df8c898067ff544c033ff2a26019ff551300cff8a89806bff534c011ff29a601aff54d30047f8a698067ff434c011ff21a6019ff50d30047f88698003ff624c0017fb126000ff98930007fac498003fc624c00f7e312601affd49300d7fca49806bfd524c035fe2926019ffd09300cffc8498067fd424c033fe2126008ffcc930007fc6498003fd324c011fe1926000ffd8530005fec298003fe614c001f
  | 5 => 0x4e21127fca710893fd5388449fe29c4223ffd0e2111ffc871088ffd4388447fe21c4221bf58a21127fea51081ffe5288449fea944207ff14a2111ffe851081ffe4288447fea144207ff10a21007fe651081ffe3288401fe9944207ff0ca2101dfcc31080fff5188407ff28c4203ff5462101ff8a31080fff4188407ff20c4203ff5062101ff8831080fff3188407ff18c4203ff4c62101ff8631080fff2188407f790c4207fdc862101ffec11080ffe60884097f3044203ff58221005fac11080ffc6088449ffa844224ff94221127faa110893fc5088447ffa044223ff9022111ffa811088ffc4088445ffb2a4222bfd9521006feca908027f6548445ff32a4202bf99521117faca9088afd6548445fe32a4202bf19521116f8ca9080a7c6548443ffb224221bfd91210077ec890802bf6448443ff3224201bf9912110ffac890886fd6448443fe3224201bf1912110f78c890806bc6448443ffaa24221ff9512110ffaa890887fc5448401ffb1a4200bfd8d21007bec690802df6348401ff31a4208bf98d21007fac690802fd6348401fe31a4208bf18d21007b8c690802dc6348445ffa9a4222ff94d21117faa69088bfc5348443ffa1a4221ff90d2110ffa8690887fc4348445ffa924207ff94921117faa49081ffc5248443ffa124207ff9092110ffa849081ffc4248401ff9924207ff8c921007fa649081ffc3248445ffa8a4203ff94521117faa29080ffc5148443ffa0a4203ff9052110ffa829080ffc4148401ff98a4203ff8c521007fa629080ffc314840fff90a4207fdc852101ffc429080fee2148401ffb024200bfd8121007f6c090802fb6048401ff3024200ff58121007f8c090812fc6048401fc3024200be18121117fea09088bfe5048445fea824222ff1412110ffe8090887fe4048443fea024221ff1012101ffeca1080eff6508407ff3284202bf9942101ffaca10882fd6508407fe3284203bf1942101ffec81080eff6408407ff3204201bf9902101ffac81087efd6408407fe3204203bf190210fffea81087ffe540843ffeaa0421fff1502101ffec61080eff6308407ff3184208bf98c2101ffac610802fd6308407fe3184203bf18c21107fea610883fe5308441fea984220ff14c210fffe861087ffe430843ffea18421fff10c2103dfcc41081fff520840fff2904207ff5482103ff8a41081fff420840fff2104207ff5082103ff8841081fff320840fff1904207ff4c82103ff8641080efe6108407ffa884203ff9442101ffaa21080ffc5108407ffa084203ff9042101ffa821080ffc4108407ff9884203ff8c42101ffa621080ffc3108407ff9084203fbc842101ffc421080ff62108407fe9084203fb4842103fea4210803e52108407ffb004203ff98021025fcc01080ffd60084017eb004203ff18021107fea010
  | 6 => 0x5fea92622aff1493114ffe84988a7fe424c453fea126229ff10931047fe6498803fe324c401fe9926208ff0c931157fea29880ffe514c455fea8a6203ff1453114ffe829880ffe414c453fea0a6203ff10531047fe6298823f7314c407ff18a6203f78c531007fec098802ff604c401ff3026200ff58131007f8c098812fc604c455ffa82622aff94131157faa0988abfc504c453ffa026229ff9013114ffa80988a7fc404c407ffb286203bfd943101ffcca1880afe650c407feb286228bf5943101ff8ca1880efc650c407ffb206203bfd903101ffcc818806fe640c407feb206227bf5903101ff8c81880efc640c44fffaa06227ff9503113ffaa81889ffc540c4117f3186208ffd4c31047fca618823fd530c411fe2986208ffd0c31047fc8618823fd430c411fe2186203ffd883101ffcc41881efe620c407feb106200bf5883101ff8c4188a3ff520c451ff2906228ff54831147f8a41889fff420c44fff2106227ff5083113ff88418823ff320c411ff1906200f78c831047fa6418823fc320c411ee1906203bf9843101ffea2188a3f7510c407ff2886203ff5443101ff8a21880ff4510c407ffa086227fdd043101ffc821880ffd410c407fe2086203fd1043101ffe621880fdf310c407ff1886203fd8c43101ffa621880fdd310c411fa9886203ffd803101ffcc018812fe600c407feb006200bf5803101ff8c0188a3ff500c451ff2806228ff54031147f8a01889fff400c44fff2006227ff5003113ff8801881fff65c840f7fb2e4207ff99721015fccb9081ffd65c844d7eb2e4207ff1972103df8cb9081fff64c840f7fb264207ff9932100dfcc99081ffd64c844b7eb264207ff1932103df8c990897ff54c844bff2a64225ff5532112ff8a99081fff63c840f7fb1e4207ff98f21045fcc79081ffd63c84017eb1e4207ff18f2103df8c79089bff53c844dff29e4226ff54f21137f8a790897ff43c844bff21e4225ff50f2112ff8879081fff52c840fff2964207ff54b2103ff8a59081fff42c840fff2164207ff50b2103ff8859081fff32c840fff1964207ff4cb2103ff8659089bff51c8407ff28e4226ff5472101ff8a390897ff41c8407ff20e4225ff5072101ff88390803ff31c8407ff18e4200ff4c72101ff8639081fff60c840fff3064204bf9832103ffac190802fd60c840ffe3064226ffd4321137fca19089bfd50c844dfe2864225ffd032112ffc8190897fd40c844bfe2064203ffd962101dfecb1080ffe65884057f32c4203ff59621125facb1080ffc65884077e32c4203ffd922101dfec91080ffe64884037f3244203ff5922111dfac91080ffc64884077e3244223ffd522111ffca91088ffd5488447fe2a44203ffd8e2101dfec71080ffe63884117f31c4203ff58e21005fac71080ffc63884077e31c4224ffd
  | 7 => 0x1901ffd420c80ffe2106407fb1083203ffe641901fdf320c80fff1906407fb8c83203ffa641901fdd320c811f69906407ffd843203ffcc21900efe610c80ffeb086400bf5843203ff8c2190c3ff510c861ff2886430ff54432187f8a2190bfff410c85fff208642fff5043217ff8821901fff600c80fff3006404bf9803203ffac019002fd600c80ffe3006430ffd4032187fca0190c3fd500c861fe280642fffd003217ffc80190bffd400c85ffe2006408ffd9731045fecb98823fe65cc4057f32e6208ff59731175facb98823fc65cc4117e32e6208ffd9331045fec998823fe64cc4037f3266208ff5933116dfac998823fc64cc4117e326622dffd533116ffca9988b7fd54cc45bfe2a66208ffd4f31047fca798823fd53cc411fe29e6208ffd0f31047fc8798823fd43cc411fe21e6208ffd8b31047fcc59881efe62cc411feb166200bf58b31047f8c5988bbff52cc45dff296622eff54b31177f8a5988b7ff42cc45bff216622dff50b3116ff88598823ff32cc411ff1966208ff4cb31047f865988bbff51cc45dfba8e6203ff94731177faa39880ffc51cc45dfa28e622dffd073116fee839880ffe41cc45bfea0e6203ff1073116fe88398823ff60cc411ff3066204bf98331047fac198802fd60cc411fe306622effd4331177fca1988bbfd50cc45dfe286622dffd033116ffc81988b7fd40cc45bfe2066203ffd963101dfecb1880ffe658c4057f32c6203ff59631165facb1880ffc658c4077e32c6203ffd923101dfec91880ffe648c4037f3246203ff5923115dfac91880ffc648c4077e324622bffd523115ffca9188affd548c457fe2a46229bf58e31167fea718823fe538c459fea9c6208ff14e3115ffe8718823fe438c457fea1c6208ff10e3101ffec51880ffe628c40f7f3146203ff58a31005fac51880ffc628c459ffa94622cff94a31167faa5188b3fc528c457ffa14622bff90a3115ffa85188affc428c411ff9946200ff8ca31007bc6518803fd328c411fe1946200f70ca3101dfcc31880fff518c407ff28c6203ff5463101ff8a31880fff418c407ff20c6203ff5063101ff8831880fff318c407ef98c6208fdcc63101ffec11880ffe608c4097f3046203ff58231005fac11880ffc608c459ffa84622cff94231167faa1188b3fc508c457ffa04622bff9023115ffa81188affc408c455ffb2a622abfd9531157fcca9880afe654c455feb2a622abf59531157f8ca9880afc654c453ffb226229bfd913114ffcc898806fe644c453feb226229bf5913114ff8c898806fc644c453ffaa26229ff9513114ffaa8988a7fc544c455ffa9a6208ff94d31157faa698823fc534c453ffa1a6208ff90d3114ffa8698823fc434c401ffb126200bfd8931007fcc498803fd624c401fe3126207bf18931157fea4988abfe524c45
  | 8 => 0xf54f32047f8a799023ff43cc811ff21e6408ff50f32047f887990dbff52cc86df7a966407ff94b321b7faa59901ffc52cc86df62966435ffd0b321afde859901ffe42cc86bfea166407ff10b321afd88599023ff61cc811ff30e6403bf98732047fac399002fd61cc811fe30e6436ffd47321b7fca3990dbfd51cc86dfe28e6435ffd07321affc83990d7fd41cc86bfe20e6408ffd8332047fcc199012fe60cc811feb066400bf58332047f8c1990dbff50cc86dff2866436ff543321b7f8a1990d7ff40cc86bff2066435ff503321aff8819901fff658c80f7fb2c6407ff99632015fccb1901ffd658c8697eb2c6407ff1963203df8cb1901fff648c80f7fb246407ff9923200dfcc91901ffd648c8677eb246407ff1923203df8c9190cfff548c867ff2a46433ff5523219ff8a9190c6fd638c869ffa9c6408ff94e321a7faa719023fc538c867ffa1c6408ff90e3219ffa8719023fc438c80f7f3146407ffd4a3203ffca51901ffd528c80ffe2946407ffd0a3203ffc851901ffd428c80ffe2146407ffcca3203fbe6519023ef328c80fffb0c6407ff9863201dfcc31901ffd618c8017eb0c6407ff186321a7fea3190d3fe518c869fea8c6434ff1463219ffe83190cffe418c867fea0c6433ff1063203ffec11901ffe608c8097f3046407ff58232005fac11901ffc608c869ffa846434ff942321a7faa1190d3fc508c867ffa046433ff9023219ffa81190cffc408c865ffb2a6432bfd9532197fcca9900afe654c865feb2a6432bf59532197f8ca9900afc654c863ffb226431bfd913218ffcc899006fe644c863feb226431bf5913218ff8c899006fc644c863ffaa26431ff9513218ffaa8990c7fc544c865ffa9a6408ff94d32197faa699023fc534c863ffa1a6408ff90d3218ffa8699023fc434c865ffa926407ff94932197faa49901ffc524c863ffa126407ff9093218ffa849901ffc424c811ff9926408fbcc93203ffc649901fde324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6403bf18532197fea2990cbfe514c865fea8a6432ff1453218ffe82990c7fe414c863fea0a6431ff10532007fec099002ff604c801ff3026400ff58132007f8c099012fc604c865ffa826432ff94132197faa0990cbfc504c863ffa026431ff9013218ffa80990c7fc404c80fffb286407bfd943203ffcca1900afe650c80ffeb286430bf5943203ff8ca1901efc650c80fffb206407bfd903203ffcc819006fe640c80ffeb20642fbf5903203ff8c81901efc640c85fffaa0642fff9503217ffaa8190bffc540c8117f3186408ffd4c32047fca619023fd530c811fe2986408ffd0c32047fc8619023fd430c811fe2186407bf9883203ffea4190c3ef520c80fff2906407ff5483203ff8a41901fec520c80fffa10642ffbd083203ffc84
  | 9 => 0x200580580000000180000100480000100800100081b80080080080180100180980080400080000a80100b00200100080700280000000380600780600100700400080000180080000780000300280000000000400000081401c00780000700200480080000000880080180080300002780100000180180000580100000000801300480080000580480000000500100000280500000080001200000000680000080200100480280480000200000080400180100180180000280000200c80100000280280300200100480000200400180080000300180580080000100081600080100b00400000c81180000700000e00100300080280000000080780280400200080000000a80100280380100580280080000880380581980780000000080000180080080200000080100100280180480080080b81700001600500080180e80280000180480000d00280000000280300480000180000180001101200180080600180980000280080100680000600280200380080c80180180000400500000180100000100080100000180700200100b81780380500000481700c00000000080000a00200000580000000480000000280180300000700000000000180202180200480000180480200000080080200000000000480600080080000280000000000000180180400080480000300080881480080100080001080480400600000c80201400480380401280580000000680000e00180000380100300080300800080000480080180101680400200280280800300201800000200000281280a00680380000280000e00000000100100b80180400100d00480100101080d00081280300100d80000100200300380000100000700000200800700380200101200180280100700080100580000000680180000080900200300000100000b80380000180180080000280000180701300300000400200280580a80a80900300d00000600480100080f00000200080080380180400100d80080280100280000700180d00200080100700480a00180680380000300300280000000000200000000080000580580100000200300000780000080080500480080200000080000280180180201380100a00000a80380080000300400480280300000000000000400080000080200000080600680180000280080000000480d80100100680000080e00000080080400100100301480800000000e00000000080200000380300480000500200780180080000000e80080100000000180d802007007000000004001800023ff65cc8117fb2e6408ff99732015fccb99023fd65cc86d7eb2e6408ff19732045f8cb99023ff64cc8117fb266408ff9933200dfcc999023fd64cc86b7eb266408ff19332045f8c9990d7ff54cc86bff2a66435ff553321aff8a999023ff53cc811ff29e6408f
  | 10 => 0xb0000000004af00000000059f60f3fd4210004a80001b74ae0000005331c36131c40fd6167762e05dc42841655a0000aa16166125d5df0d60ee02138914c1e813858454032f2200520006242801c53f90000005c32125ba39e7ba76f39b5874562d569050f48c24c30f6fe5395da4620001300000003a53910002ef7c53b20000007d60005ad59800011b7d71dd0004952932d63e630760600000000036f26e00006400011a5d06d103c0a95e63eb00000067150968b3a933371922d1260660000b90001ba0007d10000000713474db76b1575922f40ae6881d70990287374a355b6204045836d64da59610e16333a7cc43e1490001330510007a30000000005160003d35a10002cc46901b0005d100030159b0000000000900000006b56662e80000003e177300071d22541c72545e27e00036a68d0000000a400000000000049371b77000026142300015f20b00061d00000000019f00000000000058f70c4d34960d400032a2f664720501f42c1d13455e05b55e90610005624bc5be7cb5971cc75963c1750c209d1e400058c6dd58050c2820003e90001d816849a5c562140d09702619600f4671864a20b72e55146d423962e3651133817352fd2dd3793ce1725f610c3362845aa35341700000036300017b0002ab2e969b4c30001df00060a00023d36b78624a50835c6420c004f1be1dc2000000000000000f475f1270000000000005410000000000000003410001c767938e0006180007ac0000000003e800000039873974e0003b82310000000002d00000007d035930034627907e00021b0320005600b63660002d800059c2962294a67830235b90ca00073a00000a00000043c0000006e900052016d35f76638f61f47320a5e264d1fb6560ef51121329b42f1d64641741f900000032e0005e557b5321f26436aa54a5582a36330004010c82c92010007580000000003a843f33c14f00052a65d0007065c072f0000003c03a10852e70006633c978f0002402226c062835b12c0020003872ed0007aa3c556b67637c0007447603c70000050001fc00000037100000028b00055d0e90003836e804349e3390000002971010f96f641962a1d50e71a62555a76361f56644dd61e3444352710de22354b0000000f047d0005b70004dc14a0000000000000003290000d10000000000bc5fa34a0000004120004a70002b85472e644611027d68a0006cf5741d94cb0000005560005ff6af6957410eb64975c5893ef3be18f1f16921157b841f2866513ff5dd7903587b12073dd65806f6320c537322c4bf08321630574500700b80501080280080100700200480080080000180000700480181500100d00080480080280980180080d80480000400a0018018000010030010000048008238030058000018008000020000000008018000000028030
  | 11 => 0x847515481d31676cc5b166c4410005052a85252366f045340e00000000028e1f02103ac00047800000000065a5f463b00000000019161207468f3ec19a0003940005ed7a100002a3cd50b27c5cb00000046b5ac18400000070f6d22fa2a60c108b18c6547301cf2c521969e5186d839a1801240007176e21557930006622af0004062f54b91142490002210005540000000000000005d517900057012000000000019055700000026604a78b0dc1ca78436718800010f0005ae1d26782703480001eb61b4310001ac6ba7952343b00cb39376230658a6a22c45ec7d30355fe73325165f56400012b75e0ff06800066a05d01d2db7b67685de0b26ed5237bf2f70e50630006a947600072900062f0c94ca0781994c24b346e2092be0007d945d00000072c77d51b1e05f77a264f4f35c91700000d30394ba1b94a10006054f244400016e00025218b00000005e0000006f32ae0006bd69970400017a00079433f4d113a23f7275270003da00000062647a27444936e0425bf68731a2cb5cc25956e47b4f13974f041d7ae5a967511e6b31fd6694b56f523354452900000000004c43615947c00000057e0003d62507de3044b20be78c3b14a40006400004d235445c1316ec0bd5a01cd7960000000000001690003287a75824140000005725550000006740005f019d0790300007b30000006466db4e909376471e0000000004850546fd6e52a41786f249013577951e22b0585ce5734716c211d53b3c27bc0ec2b27004c559448e6297812040ac5353de7577db4a02895e836c6b027262c26b05b37853d63a72a1294c07150870004cc0012f82456b418200000000032100040f62b0000000000004e80000c700000000034f0000000000000006b80000007c25f225800000065b0000006a530a5690007090000000000003f069d00048875a00000000058578275004949c0000007bb2787c31c10571da4830f36fc6a75f101105519e34d1176ab3d473f0913a45301476e403a1773b460d53c41e5a504137d30d03e7010f87221ee0e636948f64442640a07b3fe2020002b340817e0005060003f24a500048b1e60005b60005d36014454102d303400000000067000024e71400039f1af6316b20083d87567037740440003516eb76a7c10ea5224754331890000000957cd00077b2e25b357a66d35530c0cd5e40066f72c16912df52b3df38541b47e23c58625c40b3fa4c723861000c33114e3250a200070a0da00074f3f70002480f10000000000000001e200000000065238c4b721742b4344033232430000003370000006c40000531ff00072812100056d0001bf53800060b7b500000000031d53a1a210848d6b16ff0000005455ab0003cf0002f200025e57508c2ea6680004ac2b50000007a43ea7ca7180007726de4a909a7ce2d14c10b800075
  | 12 => 0x647802c67af3b60000006c35c200000069653f7c00df6ea4b622a59507d5210000005520000004744e200064b4554183e30bf3ae0000003150fa0000000000a600000007670b00000000902200000073b17d4941601285100000000000001a46384375461341f75c63d016c29c60c6d05fc3621b80001c065e60400043b00002c1a17883174630001766734bd7a000d1aa38228a6df14d2ad5eb6da19856c00046d3aa51a5cd2762ca0000000000ad3742d23c31c808d2b63200723d74420001a52b46193c84fd0d20884fc26d6276e613d68957f42409428f0002bc2d958b7cf3704d700000017c45b0500e300061a00053400e1546804323f156655c4d60000000005c71f84921a306530e5bd32774b5ee2b734b3301ce3103c61c978703d4ab5ca00019b2a77b97524b10000007400d06394aa5d82a03180004b03030006570000001a06dc00021c0000000006b60004b450a2da0003ee5a83cb0153f32680000702b033d7970004393e70007246ae00006000038020e0003af0005880004bb3640773116c85016984e160e0c462d44f68e1977a51bb5ea6486072063770001b02cd3dc0002c767c1414e00006021c224d10745a33476700075430833e5070005a47b00e466f38467f00b3fb2ac0005f30004381021160475d40a042d2f95d904e2633d270d4590002d42c227727f23076d0005c826040008f00000040c02752e4976fa23b55000022838b2572694fb4812470005150004c60000004fa1956d56550000f50001b230221a4683a379832b0000000140042372752874b85b87d85c13b944e1fa49b31e5ef33232207f2835a306a5cf0003506c702f50054953100000051d79e09b19c3c46e30ce72026437b0897a83951424702887367652aa7d25902b110a65972d57844344074615c12f21e41306d0006a300009e25a0ab56171300000000068334e0000000000000005422621190001660003f410025f66000061176e00000021f12500073d61424254f0e81bd6095d74cf2a50002fe0002e300029801a1500000000003ca00006e00000058d21100027300000032665056827a18524b1b563e3090002560000b45b25bc0000182cf7c81712810001061040007751b335273e6e026f3887165043923ad1a70006cb0000006e16ce2157ab0004526bf6a870700000066b0af1b171f23535a10d0006033960000000000004110750002eb35600000000032d5d61922b92f300015a00068479d0000006a00001443240004577106256850000000004de0004df7313387120000002c302d71c2e10000004ad4480004d442e5530ba37f57c49f62238d25439d25b7387260b055919300077f54c00074a06c0fb3e41736bc31400000015e1de48611f0006930a710b3bf4f55f500000001976149800022612e4f40376672f031f0c34be422000
  | 13 => 0x58e4581ad1111652467115db1e521d3136303601450e124f3431533a06bb2de70e15b2920001430000000000000000000000000000a164104865c13c67b0c600071a14b2bf0007340000007dd0005e700000029528d0000006fb00052f00000038600000000048248700043d00073c16a7a60290fc5174993b744a0dd22f37e59a29f7b70007992913d110900012a2ff0001e16d77c43bb0f622708e0000001ef46a14610375d31b4c90000000007b200008072b00000006b63700000000040577a00064c00074305c16b0001f613f1940005281ab2655fd00057969736800057d0004cd0620000cf0000000000004f729400034c2c802474d0000004ed3f55d210509f66e3727694ec2a941a5af56300072e4f91182bd69f00029d5127490002ee00078d4654f80006b94f60db00065338a00015604b21858113b6be68c00067e5990674ce1510003e05e100000039c2412440cc5430e20001e700015d0a35933f65f900000079a6ac5bb3195a61bc0b53a60002fc7c902e0007424476080000001a826c55e03601e00000000040700018e01c0001fe63d0004847781830002084272ce51c05f0256ef20d5240137ad46f68645f47700064a6ad0fe4c400017f0004e46f40006810006d31ec2ba6c65134ff3754ef04546600044d0004ee2a135735e41500013900000000077e78e42a12d1220000696f852c04d18700000056747f77c7050003120200007716cd1401c661529a72356f32c3e52a20bb6174610d55e305a0ed1ed04631650e0b169433569a59d3c10160a867d00000054e6c918a1b63f844b6f926a0f718d70825355f3d900052d6a10005021b44807b46726ee0d845022e2e439075357616f3760860001234250000000004d52d700036d1580000591e37d479c3ed7910004e60003ba30b4e50560316354096c10000986d91f414849101248a20f11c4e75773426f142935d0405364d903802b4eb4ea7da4fe0d94c84026c57896e77be51f27b44c47253e6b73bc72113233b5517a950d4796a451937a00052600046c20c5a20814606230004d849d6827021db1cb66559e2670001524d00007551ea61c0000001d40000006a60005c47c60001360002240004307d50000000007c75710000004890e063f00000064554d03b0002030000003fc03f00000056a1ae63401067760074c0002dc28c7921627857630032fb56564e3ab4540b353709c3b55b43cc1f32f13d579f0174e369c1375f823a3b376c07c09209673208a2c042078a7bd18107a3bd0d72852146ca36129923e1d02ec50329e39900000045134907308243a1120003a20003403db00000000000074867a3e20002900005b05915fb7770f20a51e91a90000000000007dc0000002327472bb13e03331c00000079b3a71
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc75588100147c7558810004ff7458810006bf7458810004bf745881000cfe7458810004fd745881000cfc7458810006bc745881000cbc7458810004ff7358810006df7358810004df7358810044fc7358810006dc7358810044dc7358810024ff7258810026ef7258810006ee5258810006ed5258810006ee4258810006ed425881001cff715881001cfe715881001cfd715881001cfc715881001ef4715881001cf4715881001eee215881001eec215881001ef4215881001ee42158810024ff7058810024fe7058810024fd7058810024fc7058810026f87058810024f87058810026ee2058810026ec2058810026f82058810026e82058810044ff76cc810024fe76cc810004fd76cc810024fc76cc81003eee62cc810006ed62cc81001df671cc810005f571cc810025fa70cc810005f970cc81003cff768c810024fe768c810004fd768c810024fc768c8101fedf638c810046dc638c810004ff764c810024fe764c810004fd764c810024fc764c810005f7714c81001df4714c810005fb704c810025f8704c81003cff760c810024fe760c810004fd760c810024fc760c8101f6df630c810046dc630c81003eee620c810006ed620c81001df576c84101cef576c841001df672c841001fe672c841001ef762c84101cef562c84101edf770c84101cff370c84101edf570c84101eff070c84101eef660c841001ff260c84101eff020c8410025f976c80101cef976c8010025fa72c8010027ea72c8010026fb62c80101cef962c80101e5fb71c80101cff371c80101e5f971c80101e7f071c80101e6fa61c8010027f261c80101cff321c80101e7f021c8010027f37644010025f37644010006f376440101dff375440100077375440101c7f275440101dff175440101c7f075440101c7707544010027f36544010027f26544010027f16544010027f065440101d7f37444010007b374440101bff274440101d7f174440101bff074440101bfb07444010027f36444010027f26444010027f16444010027f064440101bff354440101bff254440101bff154440101bff05444010007f37344010007d37344010007f27344010007f17344010007f07344010007d07344010027f36344010027f26344010027f16344010027f063440101c7f353440101c7f253440101c7f153440101c7f053440101bff343440101bff243440101bff143440101bff04344010007f37244010007e37244010007f272440101cdf27244010007f17244010007f072440101cdf07244010007e07244010005e07244010027f36244010027f26244010027f16244010027f062440101c7f352440101c7f252440101c7f152440101c7f052440101bff342440101bff242440101bff142440101bff04244010007f33244010007f23244010007f13244010007f03244010
  | 1 => 0xc910004fd764c910004fc764c9100067f654c9101967c654c910006bf644c91018ebc644c910006df634c910046dc634c910006ef624c91003eec624c91003cff760c910004fe760c910004fd760c91003cfc760c9100067f650c9101867c650c910006bf640c91017ebc640c910006df630c910046dc630c910006ef620c91003eec620c910024fe76cc510024fc76cc5100067f65cc5101767c65cc510006bf64cc51016ebc64cc510006df63cc510046dc63cc510006ef62cc510006ec62cc510025fa70cc510005f970cc51001ff010cc510024fc764c5100067f654c5101567c654c510006bf644c51014ebc644c510006df634c510046dc634c510006ef624c510006ec624c510005fb704c510025f8704c51001ff0104c510024fe76c8510024fc76c85100067f65c85101367c65c8510006bf64c851012ebc64c8510006df63c8510006dc63c8510006ef62c851003eec62c8510025fa70c8510005f970c851001ff010c8510024fc76485100057f75485100557c75485100067f65485101167c6548510005bf744851004dbc7448510006bf644851010ebc6448510005df7348510005dc7348510006df6348510006dc6348510006ef624851003eec624851001fe42148510005fb7048510025f8704851001ff0104851001cfe76cc11001cfc76cc1100067f65cc1100f67c65cc110006bf64cc1100eebc64cc110006df63cc110046dc63cc110006ef62cc110006ec62cc11001df671cc110005f571cc110027f010cc110044ff764c110004fd764c11001cfc764c1100067f654c1100d67c654c110006bf644c1100cebc644c110006df634c110046dc634c110006ef624c110006ec624c110005f7714c11001df4714c110027f0104c11001cfe76c811001cfc76c81100067f65c81100b67c65c8110006bf64c81100aebc64c8110006df63c8110006dc63c8110006ef62c811003eec62c811001df671c8110005f571c8110027f010c811003cff7648110004fd764811001cfc76481100057f75481100557c75481100067f65481100967c6548110005bf744811004dbc7448110006bf644811008ebc6448110005df7348110005dc7348110006df6348110006dc6348110006ef624811003eec6248110005f7714811001df47148110027e82048110027f01048110004ff7558c10014fe7558c10004fd7558c10014fc7558c10004ff7458c1000cfe7458c10004fd7458c1000cfc7458c10024ff7358c10026df7358c10004ff7258c1003cfc7258c1001cff7158c1001cfe7158c1001cfd7158c1001cfc7158c1001ede3158c1001edc3158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c10004ff75588100067f75588100047f7558810014fe7558810004fd7558810014fc75588100067
  | 2 => 0x67f65589100067c6558910005bf745891004dbc7458910006bf6458910006bc6458910005df7358910005dc7358910006df6358910006dc6358910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf745891000cfe7458910004fd745891000cfc7458910006bc745891000cbc7458910004ff7358910006df7358910004df7358910044fc7358910006dc7358910044dc7358910006ef7258910004ff7158910006f77158910004f77158910004ff7058910006fb7058910004fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc6418910006df6318910006dc631891003eee6218910006ed621891020ef76118910206fb6018910005ee7618910006ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910207eb101891020fe6101891020fe41018910207e8101891003eef751891003eee751891003eed751891003eec751891003eef741891003eee741891003eed741891003eec7418910006ef5418910006ee5418910006ed5418910006ec541891003eef731891003eee731891003eed731891003eec7318910006ef5318910006ee5318910006ed5318910006ec5318910006ef4318910006ee4318910006ed4318910006ec431891003eef711891003eee711891003eed711891003eec7118910006ef5118910206ee5118910006ed5118910206ec5118910006ef4118910206ee4118910006ed4118910206ec4118910206ee3118910206ec311891003eef701891003eee701891003eed701891003eec7018910006ef501891020eee5018910006ed501891020eec5018910006ef401891020eee4018910006ed401891020eec401891020eee301891020eec3018910206ef1018910206eb101891020eee101891020ee61018910006ed101891020eec101891020ee41018910206e81018910044ff76cc910004fe76cc910004fd76cc910044fc76cc9100067f65cc9101b67c65cc910006bf64cc9101aebc64cc910006df63cc910046dc63cc910006ef62cc91003eec62cc91003cff768c910004fe768c910004fd768c91003cfc768c9100067f658c9101a67c658c910006bf648c91019ebc648c910006df638c910046dc638c910006ef628c91003eec628c91001df6718c910005f5718c910025fa708c910005f9708c910004ff764c910004fe764
  | 3 => 0xc7218d10006df5218d10006de5218d10006dd5218d10006dc5218d10006df4218d10006de4218d10006dd4218d10006dc4218d10046df7118d10046de7118d10046dd7118d10046dc7118d10006df5118d1022ede5118d10006dd5118d1022edc5118d10006df4118d1022ede4118d10006dd4118d1022edc4118d1022ede2118d1022edc2118d10046df7018d10046de7018d10046dd7018d10046dc7018d10006df5018d10226de5018d10006dd5018d10226dc5018d10006df4018d10226de4018d10006dd4018d10226dc4018d10226de2018d10226dc2018d1022edf1018d10226de1018d10006dd1018d10226dc1018d1003cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910004ff75d8910014fe75d8910004fd75d8910014fc75d8910004ff74d891000cfe74d8910004fd74d891000cfc74d8910044fe73d8910004fd73d8910006ef52d8910006ee52d8910006ed52d8910006ec52d8910006ef42d8910006ee42d8910006ed42d8910006ec42d891001cfe71d891001cfc71d8910024fe70d8910024fc70d891003cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d891021feb10d8910217e610d8910217e410d891021fe810d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910216ef71d891021eee71d8910006ed71d891021eec71d8910006ef51d891021eee51d8910006ed51d891021eec51d8910006ef41d891021eee41d8910006ed41d891021eec41d891021eee31d891021eec31d891021eef70d8910216ee70d8910006ed70d8910216ec70d8910006ef50d8910216ee50d8910006ed50d8910216ec50d8910006ef40d8910216ee40d8910006ed40d8910216ec40d8910216ee30d8910216ec30d891021eef10d8910216ee10d8910216ec10d89100557e75989100057d75989100067f65989100067c659891004dbe7498910005bd7498910006bf6498910006bc6498910005de7398910005dd7398910006df6398910006dc6398910006ef62989101eef761989101e6fb60989100057f75589100557c7558910
  | 4 => 0x8d10024fc70d8d10044de76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d1023fdb10d8d10237d610d8d10237d410d8d1023fd810d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d10236df71d8d1023ede71d8d10006dd71d8d1023edc71d8d10006df51d8d1023ede51d8d10006dd51d8d1023edc51d8d10006df41d8d1023ede41d8d10006dd41d8d1023edc41d8d1023ede21d8d1023edc21d8d1023edf70d8d10236de70d8d10006dd70d8d10236dc70d8d10006df50d8d10236de50d8d10006dd50d8d10236dc50d8d10006df40d8d10236de40d8d10006dd40d8d10236dc40d8d10236de20d8d10236dc20d8d1023edf10d8d10236de10d8d10236dc10d8d100557e7598d100057d7598d100067f6598d100067c6598d1004dbe7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d10005ee7298d10005ed7298d100057f7558d100557c7558d100067f6558d100067c6558d10005bf7458d1004dbc7458d10006bf6458d10006bc6458d10005ef7258d10005ec7258d10004ff7558d100067f7558d100047f7558d10014fe7558d10004fd7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d1000cfe7458d10004fd7458d1000cfc7458d10006bc7458d1000cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1003cfc7258d10006ec7258d1003cec7258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d10046de6318d10006dd6318d10005de7618d10006de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d1022fdb1018d10227d61018d10227d41018d1022fd81018d10046df7518d10046de7518d10046dd7518d10046dc7518d10046df7418d10046de7418d10046dd7418d10046dc7418d10006df5418d10006de5418d10006dd5418d10006dc5418d10046df7218d10046de7218d10046dd7218d10046d
  | 5 => 0x5dbc7448610005df7348610005dc734861003eee6248610006ed624861001fe42148610005fb7048610025f8704861020df5760861001ef5760861001fe6720861020ef7620861020fe7620861020ee76208610266f5620861020fe4620861001df7700861020df5700861001ff2600861020fe6200861020fe420086100557e76d95100567e76d95100147e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d951025f7b10d95102577610d95102577410d951025f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95102567f71d951025e7e71d95100567d71d951025e7c71d95100067f41d951025e7e41d95100067d41d951025e7c41d951025e7e31d951025e7c31d951025e7e21d951025e7c21d951025e7f70d95102567e70d95100567d70d95102567c70d95100067f40d95102567e40d95100067d40d95102567c40d95102567e30d95102567c30d95102567e20d95102567c20d951025e7f10d95102567e10d95100567d10d95102567c10d951004dbe76d911004ebe76d911000cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d911024fbb10d9110247b610d9110247b410d911024fb810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110246bf71d911024ebe71d911004ebd71d911024ebc71d9110006bf51d911024ebe51d9110006bd51d911024ebc51d911024ebe31d911024ebc31d911024ebe21d911024ebc21d911024ebf70d9110246be70d911004ebd70d9110246bc70d9110006bf50d9110246be50d9110006bd50d9110246bc50d9110246be30d9110246bc30d9110246be20d9110246bc20d911024ebf10d9110246be10d911004ebd10d9110246bc10d9110044fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10004ff75d8d10014fe75d8d10004fd75d8d10014fc75d8d10004ff74d8d1000cfe74d8d10004fd74d8d1000cfc74d8d10006df53d8d10006de53d8d10006dd53d8d10006dc53d8d10006df43d8d10006de43d8d10006dd43d8d10006dc43d8d1003cfe72d8d10004fd72d8d1001cfe71d8d1001cfc71d8d10024fe70d
  | 6 => 0xc7558b10004ff7458b1000cfe7458b10004fd7458b1000cfc7458b10004ff7358b10044fc7358b1001eef7258b10024fc7158b1001eee2158b1001eec2158b10006fb7058b10044ff76ccb1001cfe76ccb10004fd76ccb1001cfc76ccb10025fa70ccb10005f970ccb1003cff768cb1001cfe768cb10004fd768cb1001cfc768cb10046de638cb10006dd638cb1001df6718cb10005f5718cb10004ff764cb1001cfe764cb10004fd764cb1001cfc764cb10005fb704cb10025f8704cb1003cff760cb1001cfe760cb10004fd760cb1001cfc760cb10046de630cb10006dd630cb10046de63cc310006dd63cc31001df671cc310005f571cc310044ff764c310046de634c310006dd634c310005f7714c31001df4714c31003eee62c8310006ed62c831001df671c8310005f571c83101e5f976c831026ef976c8310025fa72c83101e6fb62c83101e7ea62c831026ef962c83101e7e962c83101e7f271c83101e5f971c831026ff171c8310026fa61c831003cff76483100057f75483100757c7548310005bf744831006dbc7448310005df7348310005dc734831003eee6248310006ed6248310005f7714831001df47148310027e82048310205f97608310026f97608310027ea7208310206fb6208310207eb6208310206eb620831026ef96208310207e86208310025fb7108310205f97108310027f26108310207ea2108310207e82108310004ff7558e10014fe7558e10004fd7558e10014fc7558e10004ff7458e1000cfe7458e10004fd7458e1000cfc7458e10026df7358e10004ff7258e1003cfc7258e10024fc7058e10026de3058e10026dc3058e10004ff7558a10014fe7558a10004fd7558a10014fc7558a10004ff7458a1000cfe7458a10004fd7458a1000cfc7458a10004ff7358a10044fc7358a10026ef7258a10006f77158a10024fc7058a10026ee2058a10026ec2058a10044ff76cca10024fe76cca10004fd76cca10024fc76cca1001df671cca10005f571cca1003cff768ca10024fe768ca10004fd768ca10024fc768ca10046de638ca10006dd638ca10025fa708ca10005f9708ca10004ff764ca10024fe764ca10004fd764ca10024fc764ca10005f7714ca1001df4714ca1003cff760ca10024fe760ca10004fd760ca10024fc760ca10046de630ca10006dd630ca10046de63cc610006dd63cc610025fa70cc610005f970cc610044ff764c610046de634c610006dd634c61001fd4314c610005fb704c610025f8704c61003eee62c8610006ed62c8610025fa70c8610005f970c86101edf576c8610266f576c861001df672c86101eef762c86101efe662c8610266f562c86101efe562c86101eff270c86101edf570c8610267f170c861001ef660c861003cff76486100057f75486100657c7548610005bf7448610
  | 7 => 0x8c2001cfc7158c20024fe7058c20024fc7058c20026de3058c20026dc3058c20004ff75584200067f75584200047f7558420014fe7558420004fd7558420014fc75584200067c75584200147c7558420004ff7458420006bf7458420004bf745842000cfe7458420004fd745842000cfc7458420006bc745842000cbc7458420004ff7358420006df7358420004df7358420044fc7358420006dc7358420044dc7358420026f77158420006f65158420006f55158420006f64158420006f5415842003ef7215842003eec215842003ef4215842003ee42158420024ff7058420024fd7058420026f87058420026f61058420026f41058420026f81058420026f01058420044ff76cc420024fe76cc420004fd76cc42003dee72cc420005ed72cc42001ef661cc420006f561cc420025fa70cc420005f970cc42001cff768c420024fe768c420004fd768c420236df638c420046dc638c420004ff764c420004fd764c420024fc764c420005ef724c42003dec724c420005fb704c420025f8704c42001cff760c420024fe760c420004fd760c420226df630c420046dc630c42001ef6610c420006f5610c42003ded7688420206ed768842003dee718842003fe6718842003eef6188420206ed6188420215ef7088420207eb7088420215ed7088420217e87088420216ee608842003fea6088420217e81088420027eb7648020025eb7648020006eb764802028feb75480200076b754802027fea754802028fe9754802027fe8754802027f687548020027eb6548020027ea6548020027e96548020027e86548020287eb7448020007ab7448020277ea7448020287e97448020277e87448020277a87448020027eb6448020027ea6448020027e96448020027e86448020277eb5448020277ea5448020277e95448020277e85448020007eb7348020007cb7348020007ea7348020007e97348020007e87348020007c87348020027eb6348020027ea6348020027e96348020027e8634802027feb534802027fea534802027fe9534802027fe85348020277eb4348020277ea4348020277e94348020277e84348020007eb7148020007e37148020007ea7148020007e97148020007e87148020205e87148020007e07148020005e07148020027eb6148020027ea6148020027e96148020027e8614802027feb514802027fea514802027fe9514802027fe85148020277eb4148020277ea4148020277e94148020277e84148020007eb3148020007ea3148020007e93148020007e83148020004ff7558f10014fe7558f10004fd7558f10014fc7558f10004ff7458f1000cfe7458f10004fd7458f1000cfc7458f1001edf7358f10004ff7258f1003cfc7258f10024fc7158f1001ede3158f1001edc3158f10004ff7558b10014fe7558b10004fd7558b10014f
  | 8 => 0x1ef6731852001ef5731852001ef47318520006f75318520006f65318520006f55318520006f45318520006f74318520006f64318520006f54318520006f4431852001ef7721852001ef6721852001ef47218520006f752185201cef65218520006f552185201cef45218520006f742185201cef64218520006f542185201cef44218520006f732185201cef63218520006f532185201cef4321852001ef7701852001ef6701852001ef5701852001ef47018520006f7501852020ef65018520006f5501852020ef45018520006f7401852020ef64018520006f5401852020ef4401852020ef6301852020ef430185201cef720185201cef3201852020ef6201852020ee62018520006f5201852020ef4201852020ee420185201cef02018520004fe76cc520004fd76cc520044fc76cc5200067f65cc5201767c65cc520006bf64cc52016ebc64cc520006df63cc520046dc63cc520006f761cc52001ef461cc520004fe768c520004fd768c52001cfc768c5200067f658c5201667c658c520006bf648c52015ebc648c520006df638c520046dc638c52003dee728c520005ed728c520006f7618c52001ef4618c520025fa708c520005f9708c520004ff764c520004fe764c520004fc764c5200067f654c5201567c654c520006bf644c52014ebc644c520006df634c520046dc634c520006f7614c52001ef4614c520004fe760c520004fd760c52001cfc760c5200067f650c5201467c650c520006bf640c52013ebc640c520006df630c520046dc630c520006f7610c52001ef4610c520024fe76885200067f65885201267c6588520006bf648852011ebc6488520006df6388520006dc6388520006f7618852001ef46188520025fa7088520005f9708852003fe82088520024fc76485200057f75485200957c75485200067f65485201167c6548520005bf744852008dbc7448520006bf644852010ebc6448520005df7348520005dc7348520006df6348520006dc6348520006f7614852001ef4614852003fe42148520005fb7048520025f8704852003fe8204852003cfe76cc12003cfc76cc1200067f65cc1200f67c65cc120006bf64cc1200eebc64cc120006df63cc120046dc63cc12003dee72cc120005ed72cc120006f761cc120006f461cc120027e820cc120044ff764c120004fd764c12003cfc764c1200067f654c1200d67c654c120006bf644c1200cebc644c120006df634c120046dc634c120005ef724c12003dec724c120006f7614c120006f4614c120027e8204c120004ff7558c20014fe7558c20004fd7558c20014fc7558c20004ff7458c2000cfe7458c20004fd7458c2000cfc7458c20024ff7358c20026df7358c2003cff7258c2003cfe7258c2003cfd7258c2003cfc7258c2003ede3258c2003edc3258c20004ff715
  | 9 => 0x751d8520006f651d8520006f551d8520006f451d8520006f741d8520006f641d8520006f541d8520006f441d8520024fe70d8520024fc70d8520006f765d85200077765d85200067765d8520006f665d8520006f565d8520006f465d85200077465d85200067465d8520006f764d8520007b764d8520006b764d8520006f664d8520006f564d8520006f464d8520007b464d8520006b464d8520006f763d8520007d763d8520006d763d8520006f663d8520006f563d8520006f463d8520007d463d8520006d463d8520267f320d85201efe620d85201efe420d8520267f020d8520006f775d8520006f675d8520006f575d8520006f475d8520006f774d8520006f674d8520006f574d8520006f474d8520006f754d8520006f654d8520006f554d8520006f454d8520006f773d8520006f673d8520006f573d8520006f473d8520006f753d8520006f653d8520006f553d8520006f453d8520006f743d8520006f643d8520006f543d8520006f443d85201eef772d8520266f672d8520006f752d8520266f652d8520006f552d8520266f452d8520006f742d8520266f642d8520006f542d8520266f442d8520006f732d8520266f632d8520006f532d8520266f432d8520266f770d85201eef670d8520006f570d8520006f750d85201eef650d8520006f550d85201eef450d8520006f740d85201eef640d8520006f540d85201eef440d85201eef630d85201eef430d8520266f720d85201eef620d85201eef420d85200957e75985200057d75985200067f65985200067c659852008dbe7498520005bd7498520006bf6498520006bc6498520005de7398520005dd7398520006df6398520006dc6398520216ef6298520006f761985200057f75585200957c75585200067f65585200067c6558520005bf745852008dbc7458520006bf6458520006bc6458520005df7358520005dc7358520006df6358520006dc63585200067f65185200067c6518520006bf6418520006bc6418520006df6318520006dc631852020eef621852001ef66118520006f561185201e6fb6018520005f67618520006f67618520006f76518520007776518520006776518520006f66518520006f56518520006f46518520007746518520006746518520006f76418520007b76418520006b76418520006f66418520006f56418520006f46418520007b46418520006b46418520006f76318520007d76318520006d76318520006f66318520006f56318520006f46318520007d46318520006d463185201cff3201852020fe6201852020fe420185201cff0201852001ef7751852001ef6751852001ef5751852001ef4751852001ef7741852001ef6741852001ef5741852001ef47418520006f75418520006f65418520006f55418520006f4541852001ef77318520
  | 10 => 0x8d200057d7598d200067f6598d200067c6598d2008dbe7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d20005f67198d20005f57198d200057f7558d200957c7558d200067f6558d200067c6558d20005bf7458d2008dbc7458d20006bf6458d20006bc6458d20005f77158d20005f47158d20004ff7558d200067f7558d200047f7558d20014fe7558d20004fd7558d20014fc7558d200067c7558d200147c7558d20004ff7458d20006bf7458d20004bf7458d2000cfe7458d20004fd7458d2000cfc7458d20006bc7458d2000cbc7458d20006df7358d20004ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d2001cfc7158d20006f47158d2001cf47158d20004ff7058d20006fb7058d20004fe7618d200067f6518d200067c6518d20006bf6418d20006bc6418d20046de6318d20006dd6318d20005de7618d20006de7618d20004de7618d20006df6518d200075f6518d200065f6518d20006de6518d20006dd6518d20006dc6518d200075c6518d200065c6518d20006df6418d200079f6418d200069f6418d20006de6418d20006dd6418d20006dc6418d200079c6418d200069c6418d20297db2018d201f7ce2018d201f7cc2018d20297d82018d20046df7518d20046de7518d20046dd7518d20046dc7518d20046df7418d20046de7418d20046dd7418d20046dc7418d20006df5418d20006de5418d20006dd5418d20006dc5418d20046df7218d20046de7218d20046dd7218d20046dc7218d20006df5218d20296de5218d20006dd5218d20296dc5218d20006df4218d20296de4218d20006dd4218d20296dc4218d20046df7118d20046de7118d20046dd7118d20046dc7118d20006df5118d20006de5118d20006dd5118d20006dc5118d20006df4118d20006de4118d20006dd4118d20006dc4118d20296df2118d20296dc2118d20046df7018d20046de7018d20046dd7018d20046dc7018d20006df5018d201f6de5018d20006dd5018d201f6dc5018d20006df4018d201f6de4018d20006dd4018d201f6dc4018d20296df2018d201f6de2018d20006dd2018d201f6dc2018d201f6de1018d201f6dc1018d20024fe76cc920024fc76cc9200067f65cc9201b67c65cc920006bf64cc9201aebc64cc920006df63cc920046dc63cc920025fa70cc920005f970cc92003fe820cc920024fc764c9200067f654c9201967c654c920006bf644c92018ebc644c920006df634c920046dc634c920005fb704c920025f8704c92003fe8204c9200067f65d85200067c65d8520006bf64d8520006bc64d8520006df63d8520006dc63d8520004ff75d8520014fe75d8520004fd75d8520014fc75d8520004ff74d852000cfe74d8520004fd74d852000cfc74d8520044fe73d8520004fd73d8520006f
  | 11 => 0x2be7f20d95202b67e20d95200967d20d95202b67c20d95202b67e10d95202b67c10d952008dbe76d912008ebe76d912000cbe76d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d91202afbb20d91202a7ae20d91202a7ac20d91202afb820d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006be53d9120006bd53d9120006bc53d91202a6bf72d91202aebe72d912008ebd72d91202aebc72d9120006bf52d91202aebe52d9120006bd52d91202aebc52d91202aebe32d91202aebc32d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d91202aebf21d91202aebc21d91202aebf70d91202a6be70d912008ebd70d91202a6bc70d9120006bf50d91202a6be50d9120006bd50d91202a6bc50d91202a6be30d91202a6bc30d91202aebf20d91202a6be20d912008ebd20d91202a6bc20d91202a6be10d91202a6bc10d9120044fe76d8d200067f65d8d200067c65d8d20006bf64d8d20006bc64d8d20004ff75d8d20014fe75d8d20004fd75d8d20014fc75d8d20004ff74d8d2000cfe74d8d20004fd74d8d2000cfc74d8d20006df53d8d20006de53d8d20006dd53d8d20006dc53d8d20006df43d8d20006de43d8d20006dd43d8d20006dc43d8d2003cfe72d8d2003cfc72d8d2001cfe71d8d20004fd71d8d20044de76d8d20006df65d8d200075f65d8d200065f65d8d20006de65d8d20006dd65d8d20006dc65d8d200075c65d8d200065c65d8d20006df64d8d200079f64d8d200069f64d8d20006de64d8d20006dd64d8d20006dc64d8d200079c64d8d200069c64d8d2029fdb20d8d201ffce20d8d201ffcc20d8d2029fd820d8d20006df75d8d20006de75d8d20006dd75d8d20006dc75d8d20006df74d8d20006de74d8d20006dd74d8d20006dc74d8d20006df54d8d20006de54d8d20006dd54d8d20006dc54d8d201fedf72d8d2029ede72d8d20006dd72d8d2029edc72d8d20006df52d8d2029ede52d8d20006dd52d8d2029edc52d8d20006df42d8d2029ede42d8d20006dd42d8d2029edc42d8d20006df71d8d20006de71d8d20006dd71d8d20006dc71d8d20006df51d8d20006de51d8d20006dd51d8d20006dc51d8d20006df41d8d20006de41d8d20006dd41d8d20006dc41d8d2029edf21d8d2029edc21d8d2029edf70d8d201fede70d8d20006dd70d8d201fedc70d8d20006df50d8d201fede50d8d20006dd50d8d201fedc50d8d20006df40d8d201fede40d8d20006dd40d8d201fedc40d8d2029edf20d8d201fede20d8d201fedc20d8d201fede10d8d201fedc10d8d200957e759
  | 12 => 0xd728c720004ff764c720004fd764c72003cfc764c720005fb704c720025f8704c72001cff760c72003cfe760c720004fd760c720046de630c720006dd630c720046de63cc320006dd63cc32003dee72cc320005ed72cc320044ff764c320046de634c320006dd634c320005ef724c32003dec724c320004ff7558e20014fe7558e20004fd7558e20014fc7558e20004ff7458e2000cfe7458e20004fd7458e2000cfc7458e20026df7358e20004ff7158e2001cfc7158e20024fc7058e20026de3058e20026dc3058e20046de63cca20006dd63cca20025fa70cca20005f970cca20044ff764ca20046de634ca20006dd634ca2003fcc324ca20005fb704ca20025f8704ca20004ff7558620014fe7558620004fd7558620014fc7558620004ff745862000cfe7458620004fd745862000cfc7458620004ff7358620044fc7358620026f77158620024fc7058620026f61058620026f41058620044ff76cc620024fe76cc620004fd76cc62003dee72cc620005ed72cc62001cff768c620024fe768c620004fd768c620046de638c620006dd638c620025fa708c620005f9708c620004ff764c620004fd764c620024fc764c620005ef724c62003dec724c62001cff760c620024fe760c620004fd760c620046de630c620006dd630c62001ef66188620006f56188620025fa7088620005f9708862003dee7188620216ef6188620217e6618862021eed6188620217e56188620217ea7088620215ed708862021fe9708862003eee608862001cff76486200057f75486200a57c7548620005bf744862009dbc7448620005df7348620005dc734862001ef66148620006f5614862003fe42148620005fb7048620025f8704862020ded760862003eed760862003fe6710862020eef610862020fe7610862021eed610862020fe4610862003def700862020ded700862003fea600862020fe410086200957e76d95200967e76d95200147e76d95200067f64d95200067e64d95200067d64d95200067c64d95200073c64d95200063c64d95202bf7b20d95202b76e20d95202b76c20d95202bf7820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95202b67f72d95202be7e72d95200967d72d95202be7c72d95200067f42d95202be7e42d95200067d42d95202be7c42d95202be7e32d95202be7c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067e41d95200067d41d95200067c41d95202be7f21d95202be7c21d95202be7f70d95202b67e70d95200967d70d95202b67c70d95200067f40d95202b67e40d95200067d40d95202b67c40d95202b67e30d95202b67c30d9520
  | 13 => 0xc53001ef4618c530025fa708c530005f9708c530024fc764c530006f7614c53001ef4614c530005fb704c530025f8704c530004fe76c8530004fd76c853003cfc76c8530006f761c853001ef461c8530004fe7688530004fd768853001cfc7688530006ef628853003eec6288530004ff7648530004fe7648530004fc76485300057f75485300d57c7548530005bf74485300cdbc7448530005df7348530045dc7348530005fb7048530025f87048530004fe7608530004fd760853001cfc7608530006ef620853003eec6208530006f7610853001ef46108530007e52108530004ff7558830014fe7558830004fd7558830014fc7558830004ff745883000cfe7458830004fd745883000cfc7458830026ef7258830046ef3258830046dc3258830046ec3258830004ff715883001cfc7158830026ee2058830026ec2058830045dd768c830296dd768c830045de728c830047ce728c830046df628c830296dd628c83022dde718c8302eede618c8301fddf708c8301fddd708c8301fede608c830047da608c8302e7db508c8301ffd8508c8302dfdb408c8301ffd8408c830004ff7558430014fe7558430004fd7558430014fc7558430004ff745843000cfe7458430004fd745843000cfc7458430004ff725843003cfc7258430026f77158430046f73158430046dc3158430046f43158430026f61058430026f41058430045dd768c43022edd768c430295de728c4302d6de628c430045de718c430047d6718c430046df618c43022edd618c430235df708c430235dd708c430236de608c430047da608c4302cfdb508c430237d8508c4302c7db408c430237d8408c43003cff76c8430024fe76c8430004fd76c8430045de73c8430005dd73c843001cff7688430024fe7688430004fd7688430045de7388430005dd7388430004ff7648430004fd7648430024fc76484300057f75484300c57c7548430005bf74484300bdbc7448430005df7348430045dc7348430005fb7048430025f8704843001cff7608430024fe7608430004fd760843022ddf7308430045dc7308430007e52108430025fa7008430005f97008430004ff7558f20014fe7558f20004fd7558f20014fc7558f20004ff7458f2000cfe7458f20004fd7458f2000cfc7458f2003edf7358f20024fc7258f2003ede3258f2003edc3258f20004ff7158f2001cfc7158f20004ff7558720014fe7558720004fd7558720014fc7558720004ff745872000cfe7458720004fd745872000cfc7458720004ff7358720044fc7358720024fc725872003ef7715872003ef7215872003ef42158720006fb7058720044ff76cc72003cfe76cc720004fd76cc720025fa70cc720005f970cc72001cff768c72003cfe768c720004fd768c720046de638c720006dd638c72003dee728c720005e
  | 14 => 0x46de608ca3003cff764ca3003eee624ca30006ed624ca30047cc324ca30005fb704ca30025f8704ca301f5dd760ca30046dd760ca30047ce720ca301f6df620ca3029edd620ca3031fcf520ca3029fcc520ca30317cf420ca3029fcc420ca3023dde710ca3030ede610ca30045df700ca301f5dd700ca30047da600ca30004ff7558630014fe7558630004fd7558630014fc7558630004ff745863000cfe7458630004fd745863000cfc7458630004ff725863003cfc7258630026f77158630006f75158630006f45158630006f74158630006f44158630024fc7058630026f61058630026f4105863001ef6618c630006f5618c630025fa708c630005f9708c63029dde728c6302d6de628c630045de718c630236df618c630237d6618c63023edd618c630237d5618c630237da708c630235dd708c63023fd9708c630046de608c63001cff764c63001ef6614c630006f5614c630047d4314c630005fb704c630025f8704c630225dd760c630046dd760c63029dde720c630306de620c630047d6710c630226df610c63023edd610c6302ffd7510c63023fd4510c6302f7d7410c63023fd4410c630045df700c630225dd700c630047da600c63003cff76c8630024fe76c8630004fd76c8630045de73c8630005dd73c863003eee62c8630006ed62c863001cff7688630024fe7688630004fd7688630045de7388630005dd738863001ef66188630006f56188630004ff7648630004fd7648630024fc76486300057f75486300e57c7548630005bf74486300ddbc7448630005df7348630045dc734863003eee6248630006ed624863001ef66148630006f56148630005fb7048630025f8704863001cff7608630024fe7608630004fd760863023ddf7308630045dc7308630007e52108630004ff75d8930014fe75d8930004fd75d8930014fc75d8930004ff74d893000cfe74d8930004fd74d893000cfc74d8930006ef52d8930006ec52d8930006ef42d8930006ec42d893001cfe71d8930004fd71d89301fedf6398930006ef62989300057f75589300d57c7558930005bf74589300cdbc7458930005f77158930005f471589301f6df631893003eee6218930006ed6218930024fe768c930006ef628c93003eec628c930025fa708c930005f9708c930024fc764c930006ef624c93003eec624c930005fb704c930025f8704c930004ff75d8530014fe75d8530004fd75d8530014fc75d8530004ff74d853000cfe74d8530004fd74d853000cfc74d853003cfe72d8530004fd72d8530006f751d8530006f451d8530006f741d8530006f441d8530236df6398530006f761985300057f75585300d57c7558530005bf74585300cdbc7458530005ef7258530005ec7258530226df631853001ef66118530006f56118530024fe768c530006f7618
  | 15 => 0x6644842101fe5644842101fe46448421327e75448421327e65448421327e55448421327e45448421007e77348421007c77348421007e67348421007e57348421007e47348421007c4734842101fe7634842101fe6634842101fe5634842101fe4634842132fe7534842132fe6534842132fe5534842132fe45348421327e74348421327e64348421327e54348421327e44348421007e77048421007e37048421007e67048421007e57048421007e4704842120de47048421007e07048421005e0704842101fe7604842101fe6604842101fe5604842101fe4604842132fe7504842132fe6504842132fe5504842132fe45048421327e74048421327e64048421327e54048421327e44048421004ff75580210067f75580210047f7558021014fe7558021004fd7558021014fc75580210067c75580210147c7558021004ff7458021006bf7458021004bf745802100cfe7458021004fd745802100cfc7458021006bc745802100cbc7458021004ff7358021006df7358021004df7358021044fc7358021006dc7358021044dc735802101efb7058021006fa5058021006f95058021006fa4058021006f9405802103efb205802103eec205802103ef8205802103ee8205802101efb105802101ef4105802101ef8105802101ef01058021004ff7558b30014fe7558b30004fd7558b30014fc7558b30004ff7458b3000cfe7458b30004fd7458b3000cfc7458b30024fc7358b30046ef7258b30046ef3258b30046ec3258b30004ff7158b3001cfc7158b30004ff7558730014fe7558730004fd7558730014fc7558730004ff745873000cfe7458730004fd745873000cfc7458730024fc7358730004ff725873003cfc7258730046f77158730046f73158730046f4315873003cff76c8730044fe76c8730004fd76c873001ef661c8730006f561c873001cff7688730044fe7688730004fd768873003eee6288730006ed6288730004ff7648730004fd7648730044fc76487300057f75487300f57c7548730005bf74487300edbc7448730005df7348730045dc7348730005fb7048730025f8704873001cff7608730044fe7608730004fd760873003eee6208730006ed620873001ef66108730006f56108730007e52108730025fa7008730005f97008730004ff7558a30014fe7558a30004fd7558a30014fc7558a30004ff7458a3000cfe7458a30004fd7458a3000cfc7458a30026ef7258a30006ef5258a30006ec5258a30006ef4258a30006ec4258a30004ff7158a3001cfc7158a30024fc7058a30026ee2058a30026ec2058a3003eee628ca30006ed628ca30025fa708ca30005f9708ca30045de728ca301fedf628ca301ffce628ca3029edd628ca301ffcd628ca3023dde718ca302eede618ca301ffda708ca301fddd708ca3029fd9708ca30
  | 16 => 0x812126efb21d81211e6fa21d81211e6f821d81211157e75981210057d75981210067f65981210067c659812110dbe7498121005bd7498121006bf6498121006bc6498121005de7398121005dd7398121006df6398121006dc6398121006fb60981210057f75581211157c75581210067f65581210067c6558121005bf745812110dbc7458121006bf6458121006bc6458121005df7358121005dc7358121006df6358121006dc63581210067f65181210067c6518121006bf6418121006bc6418121006df6318121006dc6318121216ef62181211eef76118121026fa6018121006f96018121005fa7618121006fa7618121006fb65181210077b65181210067b6518121006fa6518121006f96518121006f86518121007786518121006786518121006fb6418121007bb6418121006bb6418121006fa6418121006f96418121006f86418121007b86418121006b86418121006fb6318121007db6318121006db6318121006fa6318121006f96318121006f86318121007d86318121006d863181211cff32118121207ea2118121207e821181211cff02118121026fb7518121026fa7518121026f97518121026f87518121026fb7418121026fa7418121026f97418121026f87418121006fb5418121006fa5418121006f95418121006f85418121026fb7318121026fa7318121026f97318121026f87318121006fb5318121006fa5318121006f95318121006f85318121006fb4318121006fa4318121006f94318121006f84318121026fb7218121026fa7218121026f87218121006fb52181211cefa5218121006f952181211cef85218121006fb42181211cefa4218121006f942181211cef84218121006fb32181211cefa3218121006f932181211cef83218121026fb7118121026fa7118121026f87118121006fb5118121206fa5118121006f95118121206f85118121006fb4118121206fa4118121006f94118121206f84118121006fb3118121206fa3118121006f93118121206f831181211cefb21181211cef32118121206fa2118121206ea2118121006f92118121206f82118121206e821181211cef02118121004ff7558c21014fe7558c21004fd7558c21014fc7558c21004ff7458c2100cfe7458c21004fd7458c2100cfc7458c2101cff7358c2101edf7358c2103cfe7258c2103cfc7258c2103ede3258c2103edc3258c2101cfe7158c2101cfc7158c2101ede3158c2101edc3158c21004ff7058c21024fc7058c2101fe7764842101de77648421006e7764842133fe7754842100767754842132fe6754842133fe5754842132fe4754842132f64754842101fe7654842101fe6654842101fe5654842101fe46548421337e77448421007a77448421327e67448421337e57448421327e47448421327a4744842101fe7644842101fe
  | 17 => 0x30ede4118d21006dd4118d2130edc4118d21306df2118d2130ede2118d21006dd2118d2130edc2118d21046df7018d21046de7018d21046dd7018d21046dc7018d21006df5018d21006de5018d21006dd5018d21006dc5018d21006df4018d21006de4018d21006dd4018d21006dc4018d21306df2018d21306dc2018d2130edf1018d2130edc1018d2101cfe76cc92101cfc76cc9210067f65cc9211b67c65cc921006bf64cc9211aebc64cc921006df63cc921046dc63cc92101df671cc921005f571cc92103fe421cc92101cfc764c9210067f654c9211967c654c921006bf644c92118ebc644c921006df634c921046dc634c921005f7714c92101df4714c92103fe4214c92103cfe76cc52103cfc76cc5210067f65cc5211767c65cc521006bf64cc52116ebc64cc521006df63cc521046dc63cc52103dee72cc521005ed72cc52101fe421cc521044ff764c521004fd764c52103cfc764c5210067f654c5211567c654c521006bf644c52114ebc644c521006df634c521046dc634c521005ef724c52103dec724c52101fe4214c5210067f65d81210067c65d8121006bf64d8121006bc64d8121006df63d8121006dc63d8121004ff75d8121014fe75d8121004fd75d8121014fc75d8121004ff74d812100cfe74d8121004fd74d812100cfc74d8121044fe73d8121004fd73d8121006fb50d8121006fa50d8121006f950d8121006f850d8121006fb40d8121006fa40d8121006f940d8121006f840d8121006fb65d81210077b65d81210067b65d8121006fa65d8121006f965d8121006f865d81210077865d81210067865d8121006fb64d8121007bb64d8121006bb64d8121006fa64d8121006f964d8121006f864d8121007b864d8121006b864d8121006fb63d8121007db63d8121006db63d8121006fa63d8121006f963d8121006f863d8121007d863d8121006d863d812126ff321d81211e7ea21d81211e7e821d812126ff021d8121006fb75d8121006fa75d8121006f975d8121006f875d8121006fb74d8121006fa74d8121006f974d8121006f874d8121006fb54d8121006fa54d8121006f954d8121006f854d8121006fb73d8121006fa73d8121006f973d8121006f873d8121006fb53d8121006fa53d8121006f953d8121006f853d8121006fb43d8121006fa43d8121006f943d8121006f843d81211e6fb72d812126efa72d8121006fb52d812126efa52d8121006f952d812126ef852d8121006fb42d812126efa42d8121006f942d812126ef842d8121006fb32d812126efa32d8121006f932d812126ef832d812126efb71d81211e6fa71d8121006fb51d81211e6fa51d8121006f951d81211e6f851d8121006fb41d81211e6fa41d8121006f941d81211e6f841d8121006fb31d81211e6fa31d8121006f931d81211e6f831d
  | 18 => 0xc64d8d212d7d721d8d212efce21d8d212efcc21d8d212d7d421d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d212eedf72d8d212d6de72d8d21006dd72d8d212d6dc72d8d21006df52d8d212d6de52d8d21006dd52d8d212d6dc52d8d21006df42d8d212d6de42d8d21006dd42d8d212d6dc42d8d212d6df71d8d212eede71d8d21006dd71d8d212eedc71d8d21006df51d8d212eede51d8d21006dd51d8d212eedc51d8d21006df41d8d212eede41d8d21006dd41d8d212eedc41d8d212d6df21d8d212eede21d8d212eedc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006df40d8d21006de40d8d21006dd40d8d21006dc40d8d212d6df20d8d212d6dc20d8d212eedf10d8d212eedc10d8d211157e7598d210057d7598d210067f6598d210067c6598d2110dbe7498d21005bd7498d21006bf6498d21006bc6498d21006df6398d21005fa7098d21005f97098d210057f7558d211157c7558d210067f6558d210067c6558d21005bf7458d2110dbc7458d21006bf6458d21006bc6458d21005fb7058d21005f87058d21004ff7558d210067f7558d210047f7558d21014fe7558d21004fd7558d21014fc7558d210067c7558d210147c7558d21004ff7458d21006bf7458d21004bf7458d2100cfe7458d21004fd7458d2100cfc7458d21006bc7458d2100cbc7458d21006df7358d21004ff7258d21006ef7258d21004ff7158d21006f77158d21004ff7058d21006fb7058d21004fb7058d21024fc7058d21006f87058d21024f87058d21004fe7618d210067f6518d210067c6518d21006bf6418d21006bc6418d21046de6318d21006dd6318d21005de7618d21006de7618d21004de7618d21006df6518d210075f6518d210065f6518d21006de6518d21006dd6518d21006dc6518d210075c6518d210065c6518d21006df6418d210079f6418d210069f6418d21006de6418d21006dd6418d21006dc6418d210079c6418d210069c6418d21307d72118d2130fce2118d2130fcc2118d21307d42118d21046df7518d21046de7518d21046dd7518d21046dc7518d21046df7418d21046de7418d21046dd7418d21046dc7418d21006df5418d21006de5418d21006dd5418d21006dc5418d21046df7218d21046de7218d21046dd7218d21046dc7218d21006df5218d21306de5218d21006dd5218d21306dc5218d21006df4218d21306de4218d21006dd4218d21306dc4218d21046df7118d21046de7118d21046dd7118d21046dc7118d21006df5118d2130ede5118d21006dd5118d2130edc5118d21006df4118d21
  | 19 => 0x822100cfc7458221004ff7358221044fc735822101cfc715822101efb705822101efb105822101ef810582211157e76d95211167e76d95210147e76d95210067f64d95210067e64d95210067d64d95210067c64d95210073c64d95210063c64d952135f7721d95213576e21d95213576c21d952135f7421d95210067f74d95210067e74d95210067d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d95210067f43d95210067e43d95210067d43d95210067c43d95213567f72d952135e7e72d95211167d72d952135e7c72d95210067f42d952135e7e42d95210067d42d952135e7c42d952135e7e32d952135e7c32d952135e7f71d95213567e71d95211167d71d95213567c71d95210067f41d95213567e41d95210067d41d95213567c41d95213567e31d95213567c31d952135e7f21d95213567e21d95211167d21d95213567c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f40d95210067e40d95210067d40d95210067c40d952135e7f20d952135e7c20d95213567f10d95213567c10d952110dbe76d912110ebe76d912100cbe76d9121006bf65d91210073f65d91210063f65d9121006be65d9121006bd65d9121006bc65d91210073c65d91210063c65d912134fb721d9121347ae21d9121347ac21d912134fb421d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006be53d9121006bd53d9121006bc53d9121346bf72d912134ebe72d912110ebd72d912134ebc72d9121006bf52d912134ebe52d9121006bd52d912134ebc52d912134ebe32d912134ebc32d912134ebf71d9121346be71d912110ebd71d9121346bc71d9121006bf51d9121346be51d9121006bd51d9121346bc51d9121346be31d9121346bc31d912134ebf21d9121346be21d912110ebd21d9121346bc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf50d9121006be50d9121006bd50d9121006bc50d912134ebf20d912134ebc20d9121346bf10d9121346bc10d9121044fe76d8d210067f65d8d210067c65d8d21006bf64d8d21006bc64d8d21004ff75d8d21014fe75d8d21004fd75d8d21014fc75d8d21004ff74d8d2100cfe74d8d21004fd74d8d2100cfc74d8d21006df53d8d21006de53d8d21006dd53d8d21006dc53d8d21006df43d8d21006de43d8d21006dd43d8d21006dc43d8d21024fe70d8d21004fd70d8d21044de76d8d21006df65d8d210075f65d8d210065f65d8d21006de65d8d21006dd65d8d21006dc65d8d210075c65d8d210065c65d8d21006df64d8d210079f64d8d210069f64d8d21006de64d8d21006dd64d8d21006dc64d8d210079c64d8d210069
  | 20 => 0xcfe74d8931004fd74d893100cfc74d8931006ef52d8931006ec52d8931006ef42d8931006ec42d8931024fe70d8931004fd70d89312eedf6398931006ef62989310057f75589311557c7558931005bf745893114dbc7458931005fb7058931005f8705893130edf631893103eee6218931006ed621893101cfe768c931006ef628c93103eec628c93101df6718c931005f5718c93101cfc764c931006ef624c93103eec624c931005f7714c93101df4714c931004ff75d8131014fe75d8131004fd75d8131014fc75d8131004ff74d813100cfe74d8131004fd74d813100cfc74d813103cfe72d8131004fd72d8131006fb50d8131006f850d8131006fb40d8131006f840d8131006fb60981310057f75581311557c7558131005bf745813114dbc7458131005ef7258131005ec7258131236df6318131026fa6018131006f96018131004ff7558831014fe7558831004fd7558831014fc7558831004ff745883100cfe7458831004fd745883100cfc745883101eef7258831046ef3258831046dc3258831046ec325883101eee215883101eec2158831004ff7058831024fc7058831045dd768c831306dd768c831045de728c831047ce728c831046df628c831306dd628c8312eddf718c8312eddd718c8312eede618c831047d6618c83136fd7518c8312efd4518c831367d7418c8312efd4418c831225de708c8311fede608c831004ff7558031014fe7558031004fd7558031014fc7558031004ff745803100cfe7458031004fd745803100cfc7458031004ff725803103cfc725803101efb7058031046fb3058031046dc3058031046f8305803101efb105803101ef81058031004ff7558f21014fe7558f21004fd7558f21014fc7558f21004ff7458f2100cfe7458f21004fd7458f2100cfc7458f2103edf7358f2101cfc7258f2103ede3258f2103edc3258f21004ff7058f21024fc7058f21046de63cc721006dd63cc72103dee72cc721005ed72cc72101fe621cc721044ff764c721046de634c721006dd634c721005ef724c72103dec724c721004ff7558321014fe7558321004fd7558321014fc7558321004ff745832100cfe7458321004fd745832100cfc7458321004ff7358321044fc735832101cfc725832103efb705832103efb205832103ef82058321004ff7558e21014fe7558e21004fd7558e21014fc7558e21004ff7458e2100cfe7458e21004fd7458e2100cfc7458e2101edf7358e2101cfc7158e2101ede3158e2101edc3158e21004ff7058e21024fc7058e21046de63cca21006dd63cca2101df671cca21005f571cca2103fe721cca21044ff764ca21046de634ca21006dd634ca21005f7714ca2101df4714ca21004ff7558221014fe7558221004fd7558221014fc7558221004ff745822100cfe7458221004fd745
  | 21 => 0xe70d8532004fd70d8532006f761985320057f75585321957c7558532005bf745853218dbc7458532005fb7058532005f870585322eedf631853201ef66118532006f56118532004ff75d8132014fe75d8132004fd75d8132014fc75d8132004ff74d813200cfe74d8132004fd74d813200cfc74d813201cfe71d8132004fd71d8132006fb50d8132006f850d8132006fb40d8132006f840d8132006fb60981320057f75581321957c7558132005bf745813218dbc7458132005f77158132005f471581321fedf6318132026fa6018132006f96018132004ff7558432014fe7558432004fd7558432014fc7558432004ff745843200cfe7458432004fd745843200cfc745843203ef77158432046f73158432046dc3158432046f4315843203ef7215843203ef42158432004ff7058432024fc7058432004ff7558032014fe7558032004fd7558032014fc7558032004ff745803200cfe7458032004fd745803200cfc7458032004ff715803201cfc715803203efb7058032046fb3058032046dc3058032046f8305803203efb205803203ef82058032004ff7558b31014fe7558b31004fd7558b31014fc7558b31004ff7458b3100cfe7458b31004fd7458b3100cfc7458b3101cfc7358b31046ef7258b31046ef3258b31046ec3258b31004ff7058b31024fc7058b31004ff7558331014fe7558331004fd7558331014fc7558331004ff745833100cfe7458331004fd745833100cfc745833101cfc7358331004ff725833103cfc7258331046fb7058331046fb3058331046f83058331004ff7558a31014fe7558a31004fd7558a31014fc7558a31004ff7458a3100cfe7458a31004fd7458a3100cfc7458a3101eef7258a31006ef5258a31006ec5258a31006ef4258a31006ec4258a3101cfc7158a3101eee2158a3101eec2158a31004ff7058a31024fc7058a3103eee628ca31006ed628ca3101df6718ca31005f5718ca31045de728ca312eedf628ca312efce628ca312d6dd628ca312efcd628ca312efd6718ca312eddd718ca312d7d5718ca31046de618ca31235de708ca311fede608ca3103cff764ca3103eee624ca31006ed624ca31005f7714ca3101df4714ca3130ddd760ca31046dd760ca31047ce720ca3130edf620ca312d6dd620ca3137fcf520ca312d7cc520ca31377cf420ca312d7cc420ca31045df710ca3130ddd710ca31047d6610ca31235de700ca311f6de600ca31004ff7558231014fe7558231004fd7558231014fc7558231004ff745823100cfe7458231004fd745823100cfc7458231004ff725823103cfc725823101cfc715823101efb7058231006fb5058231006f85058231006fb4058231006f8405823101efb105823101ef81058231004ff75d8931014fe75d8931004fd75d8931014fc75d8931004ff74d8931
  | 22 => 0x1002800c000004000000001000b00200100000010008008000000005002c006000000800000000a001001c0080000018000020002004800c020000001000c01400000080040040000000004000001002000400400200080040140010010004000001000800000a0230030014000000001001001000000000080000020008004006000000000000200000380000020040038000032005002800400000f0040004022003000000000a005000001c0020220068020006001000802400200100080180060040000050004007004000400e000002000c002001000800c01a003000000c002001003000c0040000008040002000004000800000200200b400c0000008010000000000000c0000000018000002000001000000a004001802c00c008000001c0000130000000002002003800c0000000030010000007002000800000000000180080000048018002003000800400400b005800000600b001801c0000010000028002001001000001a00400000040000000018000000000000000007a000000802400c0000040024000009000003000a0120028000016000000000c0120000000000000000003000800200400000080000000028004000000000001000a00000100100020050000008018007000800000600a001803800000000180000000000000008000000000000401a001003003400800400000040080020008000000001002002800000b000000000a005000003000200200b004800000000000000000050000010000008000001c022001001000c00a006004ff7558732014fe7558732004fd7558732014fc7558732004ff745873200cfe7458732004fd745873200cfc745873203cfc7358732046f77158732046f73158732046f43158732004ff7058732024fc7058732004ff7558332014fe7558332004fd7558332014fc7558332004ff745833200cfe7458332004fd745833200cfc745833203cfc7358332004ff715833201cfc7158332046fb7058332046fb3058332046f83058332004ff7558632014fe7558632004fd7558632014fc7558632004ff745863200cfe7458632004fd745863200cfc745863203cfc725863203ef77158632006f75158632006f45158632006f74158632006f4415863203ef7215863203ef42158632004ff7058632024fc7058632004ff7558232014fe7558232004fd7558232014fc7558232004ff745823200cfe7458232004fd745823200cfc745823203cfc7258232004ff715823201cfc715823203efb7058232006fb5058232006f85058232006fb4058232006f8405823203efb205823203ef82058232004ff75d8532014fe75d8532004fd75d8532014fc75d8532004ff74d853200cfe74d8532004fd74d853200cfc74d8532006f751d8532006f451d8532006f741d8532006f441d8532024f
  | 23 => 0x240000020010000000001000001c00000300180040000040088040002002000800800000300200080000040008004000000000000000600a000805800000000200000060000078000002000000000000000600380000080010000020000013000004801600a001000000e00200100740020050018000002000005000400200000100000080010000000000000000800000600000000000020040000014022002001001000600100c80000040050020028006004005000000600600100000020030018004002000003002000a0010008004002000003000400200f000000802a0010000008004008000009c00e003000000c0040060008010000000000802400e007000000400000000180000000000040004000006000802c0000040018000002007000000000600000100140020010018000000001003800000000000c0008012000001800800200000080000000010000004000002001000c002000000802c00000700180040000000000008014003000000000000200f0004002001002002400200000000080040000008008000002000001c008000001800000000200000080000040000020004004002006c00000100100100000000048004000000001000800c00400080040120000068000000000002000000600000d80080080030000000004000001000400a0020030000002004001800400200000000140000000008000000005001000001e000000000400e0000000000000001000000000000200000100000000000000004005002002c024000000800400c0000000004002003000801001600500100000000000010000000003000000001400300000080060000020048008001000000005c002001000000000e000000000800400180100000010028014000000000800c004000000001000600000080000000040010028000002000000000400000000000020000008000002008003801801a000000000000c000001800c00400100100000000000018008006002001000000c006004800801a003001000401e000003803c0060000040008000011000006400200000180100020030000020000002002802400800d000000800000400100040080070000008004000000800000a000000800c0020020018028018001000001c01000600c00040080000018000008009001001800c002001000000200700080100000020010018000002000000000200000000040020000010004000003000001000600200000000040000008008006000000800800000200180000120020000000000007000000c0020000010024016005002003401400b000002800000c0070000000007003003000200300180040000000040060000000002000c0160060000004002009000000c0040040040000006008000001c0040040098064006011001800000000
  | 24 => 0x5000000001899249c71b98000ea800003f80000000000000000e5a0001f2b52c0000000000000c62000121800000000000000015900360000f54998000000000044e2c65deae0c000882204a6c8f862f3055abf56a68b10000000c6800000000000009fa000380800000000038c800000000522b110e23a54380003880004e31ab02fa338479311800000000000013dcdcf20c00000008d80ad00000000000000001d9c17954180000000000000000000d8431b1b18a6a0003f8000115e3d7069a7f400090229280000000100000000bb484812e80000006af00000000002161c82eb15642d421600003d40002920000000acf6900c000000001d68001c5c00000000001d200000000013d40000003af88bc36721f000130892b3ed2d04afe9b761b9ca859c0005272d10000579000000000000000026a40000002d400018640000002c180008ab4a634c12de0a4206bb200006a15700e08000000000322464268919f80000000000000000000000291000007215b00028b00000000000dc800000000000d000041c5e18000e4e0001d980005e0d1400004780a60000000000f8a0005959c312b40000000000000c6f0000ea97521934a01999d4e5e86f900008bad3d49927a400015c00006b800061200000000907194058a9482a00008a80000000000002928000a746ff2c919ae51700021b40005f200008e4892000328837c000c210002a21114eca09a88b87c441e0000e1dd62a6d28d8000006002802800c0010048008008004000800800a0000008030006003000802800400100180000040020028000010002000803400a015000800000600000000240000020008008010005001000c0020000000000000001000002400a0000000008002008006800000000d001801400000500100000020020008018000001000000000601a000804800a002001801401600300080040080000008000000002000800000800000300100020040028000008004002000400e00800000c0012000002000800a0000000040000001000800403c00200700180020070008010000003007000800000200000040000000000008000005001800000c0000008008000000000000800000200180000000010010000004000002800c0000000000004004002001001c008000003800c014003000000800600600000040020000038004006005001803c000002000800401200000180000000040008008002009001000000200400080000040020010014000008002801c000002002004c0020010008000002000001003400800000000000000050070008008003002000000c00200180100080000018008006000001800000600100a000400600c001800000000c00000300280010000004002000001005c00600000080100000030000000002000000000000000300180
  | 25 => 0x189d1225153920990000000000000000000045315340000000000000000708000000144424d5c70000928000467000032cc807372720b7800000000002360006d38000e221910d79f3199408f715a124f52e7146600000000000e5b7e40000002ca80000003e662991988fc00000000000003fc0002905b9ca6c756b15536892e60380010360006f280000000000000ba00000fa0000c088083b91243858454d101970000000000000091000003d00022a000014f5f5000000000048b800000000000026580aad9d63d00000480000001d040000000000000ef26682a585ad0aa34842a1b9800000070db981d640732521f01a42d2e1df80009c0d6d0002a7d5bec5a0e8000127000000030f8626a255330000554d8600001286e22a77118000000a7a38a1ec8f9cac400018dc000d0b614b4ec000eed00000000004410002ffc000bb87438000000730316000090c9c33873068cc8eda000077cb428ba32119f15a2b8251782fc00097e57b25a000000018c00000000000000308abaa150fc0a789fc54a43f8001b8a0000002304daec772d2000159c2a300012e16a82b14bb8d1916ac393ac800111291000000013f0d3c0000d6000000004f00007c800077a00006bab2000023ddbaa4c53f48001d5602133db7b502e5a70000000000bee05080000009330000000b100004939a81b2cb8d527a551a040a90000ac0000e105b5361ce8a4af4f3046509600000000001a80000001fb8000da100000010b4cfe3ca021000047c0000000f2a000529381cee04651b800000003830a495653b630155d92a0656c9523b283d8764ac1de00000000002ad8000000d0e736b079a9add9181800000e54f6b88f7c8346fb56681d02cc97d00001a5bcc53b5af0000eac000000000000084e6fa8d949eea9a0002a9d31a000000024ccb899d00029c000000056eaf140000000000378000e4f0000001bae87a3ec8b9800049c29b1b6187eae8000289dd7e4f55581b7d8f2c9e22822640000380001bf51e200044680000006e500000000000004e881d97200000000000d1e00069d00011260002a316701720004ab2a997deb8101f16b0fe630c00000002300000000000000000246a780000c1600006795a09c100000000000005ff000000034f0001e480001d1000000167a0000001d35d4612b0001fb0f3e00057091c0b5ecef5a4a1c16425930000ea021a00000006a4000a03619ae2dcfe7162fe1964d9edd656588dd980e262e80000b6416f6869f191360001dd13fc00063b0000d0c00000043c0c880000006b4000000020438e13ecb280f309a0e252fe28d2408000f108f300037c5aaa00002a000000000058cb0b039ce14731a0e8f6ace2000040800059d6a78000e001fc00018a40000000c700007a2a5c184004800076f000258c0003545b6b9dd7
  | 26 => 0xda202575d00000000000000000000c6000000000002590000001a2e7905c7ae6c654bf66cf0000a5c00000000000000000000000000d2400000008b000055a0ba9ba6d692f018307faa2900008700005a5550ba443d80004f1112c000000526800000000000025813280e4000298810c4b75d6b38d9169a5000050d3a46563ef00000000000df29fdc0aa01000000069400045b800118a0000002a4000032033d0b259a60006fc06690466a4123a78cebc0006d9800052600000035417728041451dedb6c7b474537cc69a00000002cddd2e0e000095ce94aca5238abda945203d20000fec0000002a5852e00000029a00005f80539b4c9786e800008cc9d2000000104c0003a10001668c561e34cc9e744e2e5e5b60b75022985592800000000000020344d00002d333a0000ebc284392482c00000002600000007260000b120d134d83d18b2000000000000000024fa2380000000002e900002b40620000ee600061780000000006e880009d078e5c30000bdc8a46648001802e466340024c120bc5bc89b590210e6d0028c9fa08e42e80000000003b100006a20005c000000001d40000000000b685aa8cec0008350002a000003d9000000168ca5800000014c236a0001469836d8b0002a94a5a00002c031c000d373928bd400000000032457340004f3a630f2e05200000000006141a396c000027d0c380010d492264bba31d761500028fdcf4aedb5d980b989a4ca6ee90cd0a0b7f6ef80000003100e387a4af01e400031c99ec000000000065a00058d85b000000000016e8000087000048c0005d5000000021466f093800100e21e1cd000000000064380005aa75f122b9e8f883f8323340175c13155886ec8a6ebd0000c684c0b0b51880b53043954902974324bbb00038040000006d433fcdc89652c295ac0000006c48f3421600041d80000000b725e800000096c0000000000d1c74e0001d368123cd00002c861c00018740008205a621cc000c4977a9ab84a85b10ba8f74c64000115aff5cb800007400012740000000df800000000015d8a804100000000ecc00000000004206d207613b091400018a0000ba80001f3800073000041c35040000000000000bc40002a400005fa85e00008441fc000140921cef83e96ac95ec0000001a2b70c0000ea7682fac848cbb0608b5c000ca80000ce4cfa0005ab08098dc0000001608000d0c50695f8d220f700030f4000000000000000000026780002c6b270002a5000000000000540001d80001a2c00096a0000000d3cc28571a534ec209b0002f9c6aaaf9722000000000000018cc20e000000000000000000000007de3760932ea8e420000001d098ec000000228862273500006d142c00030d2cc0046de455d16d105c00030aac690b08ec64a00006800000000000a0c00000000000000000
  | 27 => 0x12f00019600000000000b9eab72d7000000083d00000010128fb46b00000e44e748b0001d069ac0002a70960e5a00004255247f119ab9e080099e75a800112000000000000002cb57f1305b8200000000000007600000000d46568689a1014960000000075664a8f704a6ed788dbb4a587241b8ef046c80002ace0362116d5544000000000126a2f7230000000000000000011da2962b6915924ce11078193c000a783781dc42c000019300000009d400000011b60006a41f44c2000021c13d000041200000000004f9747800174e57000020304c41bf21700000006301f800000000006cbadf918e37f35f00000000005ad0a198120001201829b9200000024b00000000c00f7160a6c864980007f644e0002c5007e00000012d1202000104b9091922585eba4940e2543631963808c000000000117a4ed65cae8d84a7fc32184e80c886b73f3abd85c0001fa00b0bba9dc43b0865a105f00000000000be125d865400000000000019c8000137800118400002880008c88e50962e70000c8c089800193ac8f000000000000073980000009306910001840b4025500015e00000000510c4a000000291169659725b0001b88b1e00008b00000000000000000717657a6e413a1a868922b9adcc1f6e90001c621cf4bd00000003124ae367caf81f20001358d0a000532800000053e0c20000b720000001444b3ec9c71f0000000000000000000060e0000001c160000000000000ccb0001a5943485158e00000001bd00000000003f26ccb5e91724722318a80bc23c00002219c4e9b572fb7dda4a3cb2df329400000010e818da927682e72ab98b83d80002be9b8c000000000105400000039ec0000001a5803c50aee82e091a0000e5b0001c88000de90000959c8ee1c0002210c3eb0c2ba0001b684d23fa3b9059ab7375c10a00000c52be9509476e863bc11ac0006e00002171c30c40554b1b00001813529a00c947c806ebb780001774693b600000000d80000000cea000000127a067000000108aad90002b0585a4ba14c07558ae6991ca13b9a2c99f4ebb4c86d675a710006d4a2ba24d79779aa40af000077800000012481e0434bd57271a4c41eaee754242d39a00035a138594004b722af049f82f600025b4edc000407335000072319f37a945627600037004fc000000223066eb882a9abad4285626ef057c3d66553110001396be02ac2cf10cc8711bab9c164c0004dfa34163a000000000000000000000014deaed07ca9550c8da500023f1dbe00000020c00000004378a241ae00056031e04e48650358001aea000748000091e000759a710e146714fb8c100000001cd8001d16000000070023eaff5c4a00c0005f15da9b84a28dbf33b1f6086227037615a857a0000000fa94f2aaf1e811110ac13005004e40f4000000060c00000038984f8
  | 28 => 0x5dd8d940001d455360002892f18000bde5dfb6017f2000472295c0004195021a380000002b78000b8e9240880edca562ad00000013d00000fd80000000005638000000a004c0000000000000023f58ac2de6d800000001295182a615c4ea126f33694fa0003c88001dcc000329af3000095000000000009bd0000bd00000000000758e3a00022c80007c2d980000000c2e5cd0c335e400079e00000012722921b6384926eb592d58be40eec753029be06b812a0000104eaa8520f30e5d46a00000020946620000c1326dd3e0000000000000000000320c4fee376759fac000000000178dba080167a19dd822e5019eb578b7e9f05130000000c48000309c000000000000000050a0003bc81d65df48f2dbcae48f525135917b4e3b10db79c0002dc4c732e08d2ed40f8800166600000027ec00038862730f1a0e2e70002c48cfed543002f90000eac13c393540adf60e18001b24ef32498001d4a40207fb8b0266e225102e600003b8132b2c40000003933b75cca20370c80000000000001530d0e0000002c10fa8879498800000094367c00007860001e792f9214532000264d12a42d0001f2800043600039bd56c25c04913c80002bf6d3079dcd000075b128cd3040e230ba24b808804ada5b806000000000007ece9e235090880a0003bd1fbdd8c08c0000ead652000000148d61eeb4383a1655d8dbc00020b0b7600014200000001b900000000007f800000013620000000000566000000000000000072c000000000000035700b291158828cd6ae02670a9e195aa59236f1fed7648330001a89b2287e000000000078453b05953300007289dd89842522d18e5812e0000001214000000000000000076400011dcabe5316a632fdac6d2972a88280004f801e36dcdf80000a40000000da400013bd828ade46eb4d40de43c5a68e700001171f601a8482e085449f7c86011c00000013549da5e122d811662a4a4b6358b600000000018cad065a780000987832f9b6f8000cc81b199b400009560aa68996e04f4e614e936c1fa481984419e7a0510b0916a08fa3538fe8ff2ad452d296423ab990f6ad6c7b639206600000845734898001446a2d6e537bd5d452158f917c0009d8535000000000000000000002d21ea0a68ffa66c000000000032c37900005060b871683541c200000013600005ed000079400070600000000000002a289b1b360000003b300008695c8a07800000052000003847c70c825ecf6200024b80000000da000302c0009870003828748c264f785440000002ebae99d0a0006d504900000e224c000194c0000e280000009ec0300df40009570b6b98561242113ba47d190328192a6e00003362b192b44b60004f200012e610300008a5224000206000000000000000013bc58449f86a9234d230000000000eb0000000186cb75
  | 29 => 0xe29c80004e60003769949a887931068b44000d8e00035c084000052180000000000000000000000000000000091b29c00004f6000036208800000000000018600fc2ae00000000001481280cf0e0c0000000e806793ae3a5c0004880f400007160005e7b538fda0ad1918000000000000000188696b00000340005b3729000190493b635a0000005750428ab80009b074c1cd0000d462b02cec1fad2f1851d24000ae952f2ec40004ce4e500013347aa0d9a5a4f789ed4208000e64e1700024b40000001338001ce4ae51a92e7400005c52d8001d2400054b80000000000000000000000676392904c00043e343d8e20000001cac000d7f773800000061933280000007721260000000cd052114f02e6d6c0000001c1e1284620c75436ee059b32b4f4600030981986e80a66f10000000000313000000000000000011aa3c20000a901ea00031fb6b92080001d3b7f1a6c2e40003a54000c7d00000000004f360e8bed93e8a900000000000006ad8000000411058000157c75d00000002228182879ef94d2b2f00000000a00006b9aa900000001000000f049c0546000000000000000000003b20189da86c88eb0001ad4164000337000070c000000142400000074a000061c0000000000000a630002e4c00022d022a1b0000b5100000000001db00000000000003e68001ddce2800000001ac3f900000011667282590af0dce36f00029edb46d2d00012d4a4c342000000000045c00033dc6bc0003588000000c8a000319033ebca0003958000000000207c2c20000002f700520007408000f369810000c5980044d00023980000000001ac83c014a55fa8098e0b2800035140005ef00000000000003810000cc600016b2f9929c0004bc0e29aee00000009b906c8e0749b5f952600047b00009a84c45172794a3aa7206524a8dac52744e170da720000001b00e8c2a25519981b581890d32cfcb5455149a2578ab481d491a058a18dfb28111b81ec13b155836469c4510a69e1ccc4cae28b129cc823c1187b2117dab7c62c1811124ec71233414b0647953217ac4445a0000291800054700021804d404311f8b11ac033402b800000000018e00007621697710694d9a6c30001b2973e90d00030880006730000000000bbe398808800064704c8000210b5d26eaaf51867a84343198000b710249acdcd41452b700000001e10000000000000752390d8e80c96dc800130c60369408f8c5039f6628e159e4c3a326000112eb450001be800086234e359c00000020500007880005c92b0800000000000a000000028080000000004bc80016000000000064f7a0004a53b04000519000218400000013d02ed8620000000000dc48856a880018269a420bb5ad8da0000003304000bd400039980000002bd251d99c48000000000004c02b30001558000000264
  | 30 => 0x650260db06924f0000e350c680000006d4000000000000050e8001b0ad562c880010b64744441cbc810d094ac000061200054c92440009b35ef92cda8480f2c3800000001307d8e3400030646e20a519e01e00000000004cd4238000ca8000000089805400016dba980007032e10458000a196c1b6546f870f6fe8fc5c803800138a21cf86214ff078934049e09038e01908cb163ba38bfe427375ad38e20018048915000017e5beafe8c3600065900000003e800000013ba0000002e3000056400000000f211a00037e8d88c8d2ab0001be000000000010040a80000300000c04508976da580000000138da000013aba580001b200025d48b400010b80000000004840ae4336e136f6144c0560006be80017a66ee70f273c00000057e3475dca0111bd034000000000028f41ca0004dd2fa5a32863000383400056c6ce3adc5fe0b11da8b80496769036a6416d26612fc88d09aab964b800007582ac18f9f74d1407000000006b40000000b41d8400015c0000a3ecf9742005ca0e00000000017a24df00000011703690ae9c8094a66b00000014fc00036080000000004652bc800036201d9c340009180000000000a1c0031d6006400049f071972800013a000188e3bb0ff23a102a00014a00000006cb0bf81b80000005d81c691c62fc1bb80000000002e30000000dcc1ff0691b620000001920000000000000031873e6bd80016e43a0695a029b84d4700000004be0005853b59832da904a1770f0a7a13f0800026ed3f00033d4a202180001724000d533010000000ea90002ce0000000000020c47a6905071aec000d570000894a7a00000000000000007258f8cdd478a000173000001a65d0000aa000054e9b146a065f55c8001d806c2421000138a7f2559b5d00003bd4ac80000004470001cb0f6cbe8746a518000000000134516000036604f4898c030000ec0000e6b0a0800000008a5fb8e38f72b6729600016068fe0788c6d8ce4da63f2b58c96000000000000062300000002e40000000000e6658a0001e350280000000000c80d8f00000000007d25b216f400000000000000004c974d32d15ccb9531a801015c0005cf1e5853e33271a321997abc9681bb556cc4fa10580009160001bc843c8ce30b00000008e6000530257c40267e000000000000000037d00000005b800000000003e100015ce0012fa0fd40006085a3a87800000059c8e740000000002f1d078bdd0000000904b7742b800000000000000000008f8000000175e00302fb6291e80000000001dc25037151ca43320d84710b64c9c672761b42955abd600000000000000001dac0000002722b480000000000001232ced182800003e9f60000380000000000074951a4140000f200000000000f48000eae2fb88c8f320000000ebc00000016780014be0001b30001deccd
  | 31 => 0x44356942d6b841b066a351474000509a684000e255ed80000000003d600006a635b35480000003413fb800147c00000000000001760002378000000000065d7ca7d60db800031e9644250000f749835fa27f0ba671200001ed11629c0670ae800000003e800122a0ed0002654beab180002d08f38d661d194fdcceeef4c535bc83a1d764d1f2d3560cb60e06ac854b8719824319a20001283128000cdf1140db595200051b2e94460c5f00000000001cd00000000002fa2e2000000092f00028d0000e3c000000000005e36d00019cebb702b0c9db745ca21c8a0045e1dd17c328c0000003bf1f7000012500000017140001da00007dab1300000000000005e92829d9ea370a7000000090f00000003ec9f40ac854c92cbf100000019a487566eb241956ac331c80016f47150000000000e064b3800069200000000000000003dba94c0008be3c605a800000045d800000000031f0ffcec60000e4000188a0000000b8d3f233a3ea800000000071e907c000000000000000000000000000004bf6e6800174200045080000000005049bdd6ca5610a3abd06c0c41000000000000015ab6f4000000000062c1dccfd13080000000002e5b26401c96273aa13c00043f0000001346de8426a5142b000000000000000000002d482424e565f2925768ad82eb304085e00016c0f3000000046880000000023d7959c000d7c2cb1ee146422400000001de2b613c80000009000c29b7151c3070000001392e001ab800000000022300000000004c4811c5d85800000000a0ab5800000012ba0004e9800112c12d000000000040b000163400000000008ec000bf30001f4c85200074e974800043a766800000022000028f000000000000000000001cf3b4da3678f6c403994e60000000000000000099154989e0000003238000ce63f000000003d32aa00008f672e00000007c0000089000040e00056b9d5c7088e900020e56c6b970001e61aba00000022500000005c2ad2980c88f00000017b031566606d4000ab853b8e9400082859680011de000720a81d966caa000000000000005a921000015433a0450f82be2000000088a000000000000000000000000000002008e3c0d000000028e56f665e1e3a5d8884000000000000024e2e880009b26ef00000000000000001bd19b80000000000314cf345e2cf87949556619f91a4c46c00000000000004d6881400000030698b948a74c255a470000e1f00000000004f60003a082f4c0d34238e481e5b823eaa1834e92128000002a40000ab8000000b0e39fb811b043a911191000001742ab98783946bc0000000e3e00038f331cd6e16e244800000042235300000000002310001164abc05d000084c000026884c00000013180000006ba5338d10eda7db19e00016ec4e600038bcf4c20868a800110600057a8a
  | 32 => 0x7fd66e9eb07389a53105ea6d128fdb6a00014700000005280e0913c00073b00000000000000000000ad21d90b38000000000219253c000000000239c000cd936380013c2cfc555b130bce8982242019bd600009c11fc298000000204000000000000000000000002d7c4b40006ed2318000c6a77517a40004d017086740741681e299c19f400000000018e600000006b40002ed082a599a666ab3d598b4582a4c755000095263d00002f844200004e000000000043715114706e30ca07c0bf6000433aee8f4400047f93ad7ea705000329c0002364c9000086e54e000050800000056e1b3800000000000000000000000b94cea00066d80000008210002a11140a6b333b1ed7f8cd66c9b4f8eca00000021d00000006669bcc0006380ed303000000068d189123ae1a680800000000000000000000000000a9800000000000000000004600ed834277473600000005710000b7c0000006f7000000078100021300006d50480e31038cb608200011c20000000000d1800064b00003f29092db88e000000076280000000000328000028db27198e4400000037480000000000001f940000000000001af06165f631fdbfe3d60be12e552ab16303b478b6c0000001c11bc60003a18000000e3a0003b640000007121940000a186788000000c020000e053e69ae0000000000bcd0000000990e3000000000007483f10000000777000000080c5d95d0074c000ca21438d7c00021576e0000000dad2c30000e02475000040000000000000000000000b100000002ca00029d58a283e15b80005c400000000019b0d113ff1a545dc6aa6c82f64d28e3f197a295870c120b809f02189441df016853a58b5551ae1450b3446d1595ba847115f269939c31704d02591a6be34a439e40000003858f389b68810002274f1253453e0001930000477164195800000000000001a00000000f6065d178bb451547a7751388400033376bb33d8463ee3f50620a388310de317837055500004f013eab50002b19abe05b41900000000000002b25a542824be00016020a200039f4000e1d4220000000ddb0001b640000000000200c1e6066b282a8bca4d31ac80302f099b00000004aa89f0001fe92a60000001cf4e966f60002b69ce800000000004a2a0b000000000036835cb6056f05fd0000000000000000303d3bed620a31790f92d8c310130cd245373f3a548eeabf0194a708424cee2cc97f885652958aad88000000346a09cd7e71800000013e48f00002bc4000837000000000000000004b8000443000000000069f00000000009d9000000000000069380811680b60000001b8e0000002fec93474e57b80011d40000001934e12cc2453b1f08de9bc5811b2402c0005db00003b87532af20bc0000000001241a68000503000000000045fab900003780001b7558a6
  | 33 => 0x44a00000000000002f330d4c8a00000580003e6afb6b080002804d70002eac000a6e0000e8800048300000000009724230ac87260000000000000000000000000000072e9bd40ba4a66441a208aa000000000006eed200000000000003a8000000000000000000000004ba1ad920e0007648000e88d180000000000000000000092a00000034c581c000040aca8000c4b7788b3104800044d000131e0a577580000000000000000c92e88634b6bc7920005a19e00de2e363df8b4dcc8c344169db0000a2a2d13568dfe0005ba00013ea00068f915c00000024936ad7f03a632bb7600002fe0ce35d86f62c253899a5cb20000000001d72e6255033840000350000f78000b3a2950f183e81ba6053015830000179138800058c0000a2c00012f05a000036ca544830b680002a800017e80383f33f19a7487a1a237f166000000043ea1dce8e1cc00008d585471b00012656d6b113e8285c00021f4029d6c2f60004f8894d03492800000002aa0001b08000e6e0000000a54000000127966d19a9716ee305c4cc000000126c0000000002c8d79c00010300bc0f8686000314962ecd53dd86b00005d800010d00002e90d1b95cb3c2140041ce40004dc5988000b02d6a0ff800000000074c8000cb60000000000000ce500000000000003d7265c000bbc00011e996a00076213c197858f000131c000000300b94d98c00027888f00000000002d2000028f2588000000a810001a5c00082b000000108639900020fc0007b35458000000e803c58c780009a800022b40002eb0000000000000160262c000b0d0002cd4000d403be8db98ba00000011e00008a33a78000000000000000000090500007d40000000f7000165c00020380000005ad62812740000000000000d02000287000113c4ea3b3a87cfea4ae32c00000000002998000bd8de00000001b969d03058101948b6013580000000440002bcc0009a73410d597800005120fac69800000034100000bd186a4d85181065090c90b90acc3f30000db6b2c0000f69228de134d0000576a0c2d48000a600005c200016c200054280010a690e04680cc84a7cf0cc0000000808271ab4c91c1b10003b8c00000042f800142000000000017e4aef6620000e780004eb00015b6b084ce100c000752063000000020c5240bbc00062f03a90ed7a048c2fb000000000033518f0000b2200008c53aacf02868488aee24a1489be4efe1ef0001ac0000101000000137ca560002a4400000000000000000000000000000000439000000000041a00000000001548000996b076ac00003fa00046f80019c045271485780000004a095052524c634180000000000002a09ae40000000000fd07360001968c74e540b89410846d9a00000017902c30002a28000000642b1500c2549724083894200046b8c64296d380002
  | 34 => 0x674b9d8d502a10fb80012c2000000254503200062236e000094200000000000e339d0000b8abcb650b18400000000021ec000000044000000073821a80014a0af81d730ac00000016284d81e400014d81f8000ecb00002b00000005540000ffe00006183e0000b6e0003a8000052f28f282000008200000000008f900004fc59000022d8000000e690000000000cfb0001af48da0006311460c30000000350c00000000000018100000000000112000000372153c0003eb8000f5a
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xb70855cd100400176708b9a20080deec2117344010005f1c12e68802000be0825cd1004001ae0ea39a20080036c1d07344010235e9438e68802000dd2871cd1004089ba6ec39a2008003b4dd87344010007a9ba8e68802000dd2751cd1004001ba0ea39a2008003d41d47344010006a83a8e68802000f93741cd1004001ba4e839a2008003741d07344010007c83a0e68802000d90741cd10040833e50fb92200810678a1f7244010216f1bb6e48802000ee376dc91004001ec6ebb922008003d81d77244010007d1ba6e48802000fa074dc91004001f86e7b922008003f01cf724401000578c34e48802038b72859c910040016e30b39220080035cdd67244010006b83ace48802037bb2849c910040017630939220080036cdd27244010006d83a4e48802000bd2839c910040017a307392200800374dce7244010006e839ce48802041be2829c9100407b3e70eb922008002bce197244010005b9c2ae48802038b70855c9100400176708b9220080deec2117244010005e9c1ae48802000bd0835c91004001ae6ea39220080035c1d47244010006d9ba0e48802000db0741c91004001ba6e63922008003741cc72440101cef1390e48802000de1721c910040857c50e392200800378a1c724401020ef1bb0e48802000ee3761c91004001bc6ea3922008003d8dd47244010006b1ba8e48802000de2751c91004001bc2ea3922008003781d47244010007b03a8e48802000d60751c91004001bc6e83922008003e8dd07244010006d1ba0e48802000de2741c91004001bc2e83922008003781d07244010007d03a0e48802000da0741c91004001bc6e63922008003f0dcc7244010006e1b98e48802000de2731c91004001bc2e63922008003781cc7244010007e0398e48802000dc0731c91004083bc70c392200810778a18724401020ef0c30e48802041de0861c91004073bc70a39220080e778a1472440101cef0c28e48802039de0851c91004083bc6ca392200810778994724401020ef0b28e48802041de0651c91004073bc70839220080e778a1072440101cef0c20e48802039de0841c91004083bc6c8392200810778990724401020ef0b20e48802041de0641c91004001bc6a83922008003789507244010006f0aa0e48802000de0541c91004073bc70639220080e778a0c72440101cef0c18e48802039de0831c91004083bc6c639220081077898c724401020ef0b18e48802041de0631c91004001bc6a639220080037894c7244010006f0a98e48802000de0531c91004001bc68639220080037890c7244010006f0a18e48802000de0431c910040013e50f99220080027c61f32440101cef0396648802004af2868c910040015e30d19220080e7781ca3244010004f9c3a6488020009f0874c91004073bc0e499220080e7781c83244010
  | 1 => 0x8e9b12408800333dcf62481100066639ec49022043ce471d8920440095d501b1240880123da1b71481100063bb2ee29022000c7465dc5204400196ec9b8a40880032d19371481100066bb1ee29022000cd463dc520440999c8c5b8a40880022fe117558c1000c5e422eab1820008ef825d5630400f1d904baac6081e63de057558c1001c7a40aeab1820788fb805d563040091f100baac6080021fe157458c100143e42ae8b1820008ef825d1630400f1d904ba2c6081de3de057458c1001c7a40ae8b1820768fb805d163040091f100ba2c60800a1fa1f75588103563a38eeab10206ae6421dd562040ad8f0e1baac40815b9a08375588100045fc22eab1020018bc845d562040011bf06baac4080223720d755881001c7a40aeab1020048f8805d562040ad0fd0e3aac4081d71d1c475588103af32108eab102074c78701d562040e9cd0403aac4080062fa1f74588100061fbaee8b102000c3c75dd162040d1968e3ba2c4081a3a908774588102a65c386e8b102054ea820dd162040010ff0aba2c40800a1f21574588100046fc1ae8b1020088dc835d162040071e902ba2c4080123e20174588102a45f438e8b102000c3f751d16204001878ea3a2c4081cf2d1c4745881039f52108e8b102072cb8701d162040e5d50403a2c40800317dd773588100062e3aee6b102000c9f74dcd6204001938e9b9ac408177351c773588102ef6210ee6b10203fcd870dcd620407fd9041b9ac4080ff3360b73588100062fba8e6b102000c5c751cd620400193ee839ac408003271d0735881030e6a388e6b102061ec4211cd620407d9b0e039ac4080fbb20807358810016363aca4b1020048ec8754962040075c902a92c408012ba201525881000e563a484b1020048ec8750962040075c902a12c408012ba201425881002477c3ac59902036a6c8558b320406b55908b16640800f399c562cc81002675382c5990200087f855d932040050f90abb264080022fe11764c81000c5e422ec990203f8df835d932040071e902bb264080123e201764c8100446e41aec1902030a6c85588320405f55908b106408002b3e0d620c8100257943eec8802004cf287dd91004001ce0ebbb22008003ac1d3764401038db943eea8802038d7287dd51004095ae6edbaa20080039cddb7544010007983a6ea8802070bb287dd1100406fb650fba220081236cddb744401000759bb6e88802000f3375dd11004001e60ebba2200811b74ddb734401000769bb6e68802000f5375dcd1004001ea0ebb9a2008003e4dd37344010007c83a6e68802000af1869cd10040716e50b39a2008002dc6167344010006b83ace68802037bb2849cd10040017630939a20080036c1d27344010225e941ce68802000be2829cd10040017c30539a2008002bce197344010005b9c2ae68802038
  | 2 => 0x3654851025f3210eca90a204ac7870d9521440e117d0dba242880030fd9774485100061e32ee890a2069cac62dd121440d1b6021ba242881fa2fa1f64485102445e43ec890a2000c3f75d912144001878ebb224288127a908764485102465c386c890a20448de86dcd21440018becbb9a42880031719773485100064fb26e690a2000c9c64dcd21440b5998c5b9a42881777404373485102346f430e690a2000c5f651cd21440018b8ca39a428800327d9073485100064e320e690a2060ccc621cd21440c3ba02039a428818237a1f63485102346e43ec690a2000c5f75d8d21440018b8ebb1a428800327dd363485100064e3a6c690a2047ec421d8d214408d9b0e1b1a428816a37a1c63485100446e438c690a2000c5f7518d21440018b8ea31a428800327dd063485100064e3a0c690a2045ec42118d21440899b0e031a42880031bdd76248510006363aec490a2000caf74d892144001958e9b12428800333dcf62485100066639ec490a2003ae681d8921440859d0e1b1242880031ed9770485100063c32ee090a2000cbb64dc12144001970c9b82428800336d8f70485100066c31ee090a204dce862dc121440819cce23166088107b804062cc1100466a31ae39822000ce4625c730440010ff0abb2608800a1f215764c1100045fc22ec98220018bc845d9304408d1bf06bb260880023be09764c11003c76412ec9822047cd471d8d30440819c8e23126088107b8040624c1100063a32ee29822000cb464dc530440019c8c5b8a608801f3918971c81100043fc2aec902200287c855d9204400117f08bb240880062f21176481100046fc1aec90220088dc835d920440851df04bb240880f63de0576481101e47dc02ec902207d87e86dd52044001878c9baa408815f1b18b75481102b6b8086ea902207c87e87d9520440970f90fb2a40880030f1d3654811025e3a38eca902204ae6820d9520440f717d0dba240880030fd9774481100061e32ee89022055cac62dd120440a9b6021ba240881ea2fa1f644811024c5e43ec89022000c3f75d912044001878ebb2240881272d1c7644811024754106c890220458de86dcd20440018becbb9a40880031719773481100064fb26e69022000c9c64dcd20440a7998c5b9a40880ff74043734811023c6f430e69022000c5f651cd20440018b8ca39a408800327d9073481100064e320e69022052ccc621cd204407dba02039a408814a37a1f634811023c6e43ec69022000c5f75d8d20440018b8ebb1a408800327dd363481100064e3a6c69022047cd471d8d204408dd9041b1a408814e37a1c63481100446e438c69022000c5f7518d20440018b8ea31a408800327dd063481100064e3a0c69022045cd47118d2044089d904031a40880031bdd76248110006363aec49022000caf74d89204400195
  | 3 => 0x63122000e4f65d8c6244001c98cbb18c488003a3d93631891000746326c63122082ecb10d8c6244107d8c21b18c48820fb1043631891041764086c631220008ed8798c62440014dd0b318c4880029b616631891000557424c63122000aad8498c62440011df0eb18c4880029be1563189100053642ac63122000aaf8458c624400155908b18c488003339d8631891000727b28c63122000e4c6518c6244001d1ec8318c488003a3190631891040765880c63122081ec61018c6244103d8820318c488203b2040631891000716aa0a83122000ace83150624400159b062a0c4880023be1d531891003c7643aa63122000aaf8454c624400155908a98c488002b9e0553189102057240aa63122000aeb8054c62440835d100a98c488002aba10531891000556c20a631220008ef8750c624400f1d90ea18c4880029be1543189100053642a863122000ae78150c62440815c902a18c488002bae01431891020d74402863122000a6e8510c62440014db0a218c488106baa03511891000574c06a23122040ee010d4462440015d700a88c488106ba201511891020770082a23122041aea80d0462440015d301a08c488103b8043411891000575c02823122041ae8805046244081dc020a08c488102b9a07501891000572c0ea03122041ee010d4062440015cf02a80c488102b9205501891020f70082a03122040ae681d0062440015cb03a00c488107b8043401891000573c0a803122040ae4815006244083dc020a00c4880029be1510189100053642a203122000aaf84440624400155908880c488002b3e0d10189100056641a203122041ae78144062440815d700880c4880021fe1576cc9100143e42aed99220008bf845db324400317908bb6648801e3720d76cc9100043fc2aed192200287c855da324400117f08bb464880062f211768c91003c76412ed1922047cd671d8e324408d9b4e1b1c64880123d219718c9100063a32ae31922000cb4645c6324400f9c8c4b8c64880127c201718c91001c7c432e11922000c78655c23244001970c8b84648801f3a189708c91001cf840ae1192200287e85dd932440010fb0bbb264880062fa13764c9100045ec26ec992200087f855d932440050f90abb264880022fe11764c91000c5e422ec99220008f7815d932440011f700bb264880223720c764c91003c76410ec99220078de87d8d32440111dd0fb1264880021fe15760c9100143e42aec19220008bf845d8324400317908bb064881073a9c062cc51020770080c598a2000ce8625c3314408d9b0e1b1a62881073a1c0624c51020770080c498a2000c7865dc13144001970c9b8262880033a18b704c51003e74312e190a207187e86dd52144001878c9baa42881af1b18b7548510356b8086ea90a207f87e87d9521440950f90fb2a42880030f1d
  | 4 => 0x2440018baea31cc488003279d063989100064eba0c73122000c6e75d8a62440018daebb14c4880032b9d3629891000656ba6c53122000cce73d8a624400199ae7b14c48800a1fa1b75589102543e436eab12200087e87d956244001878e9b2ac4880021fa1c65589100061e3a0cab1220018be86dd162440911790dba2c4880030fd9774589100061e32ee8b1220008be87d91624400187eebb22c4880030f1d764589100045f438c8b122000c3f751916244001878ea322c48800317d9773589100062e32ee6b122000c9f64dcd6244001938c9b9ac48800317d9473589100062e328e6b122000c9f641cd6244001938c839ac48800237a1f63589100062fbaec6b122000c5c75d8d624400193ee9b1ac488003271d363589100046f438c6b122000c5f7518d62440018b8ea31ac48800327dd063589100064e3a0c6b1220008bf845d5624400317908baac48800237e0d75589100446e41aeab1220008ef825d562440011ef02baac4880023ee0175589100061fbaee8b122000c3c75dd162440010ff0aba2c48800a1f21574589100046fc1ae8b1220088dc835d162440011df04ba2c4880023de0574589100047dc02e8b122000c3f751d16244001878ea3a2c48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880031bdd77258910006363aee4b122000caf74dc96244001958e9b92c48800333dcf72589100066639ee4b122000c7775dc562440018e8ebb8ac4880032ddd371589100065a3a6e2b122000cd773dc562440019a8e7b8ac4880031edd770589100063c3aee0b122000cbb74dc16244001970e9b82c48800336dcf70589100066c39ee0b1220008ef8758862440014df0ab10c4880029b215621891000557c22c43122000aac84588624400159f06b10c488002b320d6218910006373b6ca312208ae6b10d946244117ccc21b28c48822f99043651891045734086ca31220008ed87994624400155d09328c488002ab61265189100056741cca3122000acd8399462440011df0eb28c488002abe11651891000556422ca3122000acf83594624400159906b28c4880031b9d8651891044735880ca3122089e66101946244113cc820328c4882239a0406518910006573b6c83122000e2f65d906244001c58cbb20c48821baac43641891043f53086c83122087ea410d90624410dd5021b20c4880023b61e64189100053742cc83122000a6d85990624400159d07320c488002b360e641891000477c3ac83122000a6f8559062440014d90ab20c488002b3e0d64189100056641ac83122000cae761906244001c5eca320c4880038b194641891042755880c83122085ea610190624410bd4820320c488213aa0406418910006673b6c
  | 5 => 0x8002b3e096318d1000566412c631a2000c5e76d9463440011bb0f328c688002a7a126518d100054ec24ca31a2000ace82994634400159b05328c68800237e1d6518d100054fc22ca31a2000a9c84594634400159f04b28c688002b32096518d100062f3b0ca31a208ee5b10194634411fcac20328c68823f950406518d104772c080ca31a2000c9e76d906344001c3ecbb20c688003871976418d100046ec3cc831a2000a5e8599063440014bb0b320c688002b3a0a6418d1000566c14c831a20008df8759063440014bf0ab20c688002972156418d1000567c12c831a2000acc82590634400193cec320c68800387d946418d100070e328c831a208ce9b10190634411bd2c20320c688237a50406418d104674c080c831a20088de8715063440011bb0e2a0c688003875505418d100056dc02a231a2044ad88054463440015b700a08c688112b62014118d100056bc0aa031a2045ad48154063440015af02a00c688116b52054018d100052fc2a2031a2000a5c85440634400153f08880c688002a72111018d1001477c3aa5b1220018ef8750b624400155d0932ec488002ab61265d89100056741ccbb122000acd83997624400155f08b2ec488002ab21165d891000567c1acbb122000acc835976244001c5ecbb26c4880038b19764d89100053742cc9b122000a6d85993624400159d07326c488002b360e64d891000537c2ac9b122000a6c85593624400159f06b26c488002b320d64d891000717b28c9b122000e2c651936244001c9ecbb1ec4880039319763d891000747b26c7b122000e8c64d8f62440014dd0b31ec4880029b61663d891000557424c7b122000aad8498f62440014df0ab1ec4880029b21563d891000557c22c7b122000aac8458f6244001c9eca31ec4880039319463d891000747b20c7b122000e8c6418f6244001c5aa82a6c488002b3a0c54d891000566c18a9b1220008ef8754f62440011d90ea9ec488002abe1153d891000556422a7b122000ae78154f62440875c902a9ec488002bae0153d891021574402a7b122000aae8414f624400155b0829ec4880023be1d43d89100047643a87b122000a6f8550f62440014d90aa1ec488002b9e0543d891021d7240a87b122000aeb8050f62440855d100a1ec4880029ba1443d891000536c2887b122007c6c625d6624400187ce9b2cc4880030f9d065989100061fb2ae93122000c3c655d2624400f958c4ba4c4880030f9d764989100061ebaec93122000c3e75192624400187aea324c48800317d9673989100062e32ce73122000c9f649ce6244001938c939cc48801f3318a73989100062fb2ae73122000c5c655ce624400193ec8b9cc48800327191739891003e66312e73122000c5e75d8e62440018baebb1cc488003279d363989100064eba6c73122000c5e7518e6
  | 6 => 0x52e42a87b1a2000acf8250f634400159904a1ec68800297a1443d8d100052ec2887b1a2000a9e84997634400153b0932ec688002b3a0a65d8d1000566c14cbb1a2000a9f84597634400153908b2ec688002b3e0965d8d1000566412cbb1a2000e1f65d936344001c38cbb26c68800297a1664d8d100052ec2cc9b1a2000ace82993634400159b05326c68800297e1564d8d100052e42ac9b1a2000acf82593634400159904b26c68800387d9464d8d100070e328c9b1a2000a9e84dd7634400153b09baec688002b3a0b75d8d1000566c16ebb1a2047ad681dd7634408d5ab03baec68811ab6a0375d8d1023d6cc06ebb1a2000a9e849d7634400153b093aec68800297a1774d8d100052ec2ee9b1a2000ace82dd3634400159b05ba6c68811eb5a0774d8d102356ac0ee9b1a2046ada80dd3634408f5b301ba6c68800297a1674d8d100052ec2ce9b1a20008de8715363440011bb0e2a6c6880038755054d8d102356ac08e5b1a2047ad9801cb63440118b8c6bacc6880030f9d36598d100061f3a0cb31a2000c3f655d26344001878caba4c6880232718d7498d100061f3aec931a2000c3d75d92634400187cea324c6880030f5d46498d100062f3aec731a2000c5d75d8e634400193ce9b1cc688003275d36398d1000637b2ce531a2000c6c659ca634400195ec9394c6880032b1927298d1000667b1ce531a2008ccc639ca63440018decab94c6880031b1957298d1000657b22e531a2000cac645ca634400199ec6b94c6880233318d7298d100043f43ecab1a2000c3c74d9563440010fd0e32ac6880030f1d06558d100061fb2ee8b1a2000c3c65dd1634400117d0fb22c6880030fdd76458d100061e3aec8b1a20008be87191634400187eea322c6880030f1d46458d1000637b2ee4b1a2000c6c65dc9634400195ec9b92c6880032b1937258d1000637b28e4b1a2000c6c651c9634400195ec8392c6880032b1907258d100045fc22eab1a20018bc845d563440011bf06baac6880023be097558d1003c76412eab1a20008f7815d563440011f700baac6880030fdd77458d100061e3aee8b1a200087f855d163440050f90aba2c68800237e0d7458d1000477c12e8b1a20078ec825d163440011ef02ba2c6880023ee017458d100061fba8e8b1a2000c3c751d163440018beebb9ac688003171d77358d100064fba6e6b1a2000c9c74dcd63440018deebb92c6880031b1d77258d1000657ba6e4b1a2000cac74dc9634400199ee7b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d100063a3aee2b1a2000cb474dc563440019c8e5b8ac6880031e1d77058d100065c3a6e0b1a2000ce872dc163440011bf0eb18c68800297e156318d100052e42ac631a2000a9f8458c634400153908b18c68
  | 7 => 0xea87cc520080013d30f98a4010103781c7314802002575434629004000ae9868c52008081bc0e318a40100027ae1d3148020004f443a629004040de0714c52008081bc0e218a40100022fe117558f1000c5e422eab1e20008ef825d563c400f1d904baac7880123d2057558f100043fc2ae8b1e200287c855d163c40011df04ba2c78801e3b2097458f100247a40ae8b1e20088fb865c332c40071bf0eb1c658800f359c5638cb102346fc3ac79862003cd47158d30c40851df0eb1641880f63de1971c831001e7238ac490620008bf845d5638400317908baac7080023be097558e1003c76412eab1c20048f8805d563840010ff0aba2c70800a1f2157458e1000477c12e8b1c20078ec825d163840091f100ba2c7080223de1971cca100246fc3ac719420448df8758f31840831df0eb1643080f23ee1970c861002674382c490c200087d8799365440014bd07326ca880029760e64d951000537414c9b2a2000a6d8299365440010ff0eb26ca8800297e0d64d95100052e41ac9b2a2000a6f8259365440014d904b26ca880030fdd274d95100052f41ce9b2a2000a5d839d3654400147d09b9eca880028f61373d951000537416e7b2a2000a6d82dcf65440974ed03b9eca8812a9d60773d95102553d406e7b2a204ba7980dcf654400147d0939eca880028f61273d95100043fc3a87b2a200087c8750f65440014df04a1eca880029b20943d95100053bc0a87b2a204ba748150f65440014f700a1eca8812a9e20143d95100043f43887b2a200087d8710f654400187cedb2ec8880022f61e65d91100051f42ccbb222000a9e83997644400153b0732ec888002aba0a65d911000556c14cbb2220008bf87597644400153f06b2ec888002a720d65d911000557c12cbb222000aac82597644400147d0c32ec8880030f9d865d91100061fbacebb222000a9e839d7644400153b073aec8880028fa1773d91100051ec2ee7b222000aae82dcf644400155b05b9ec888126ada0773d91102455ac0ee7b222048aba80dcf644409357301b9ec8880028fa1673d91100051ec2ce7b2220008bf8754f64440011790ea9ec888002abe0953d911000556412a7b222000ab78154f644409356902a9ec888002aee0153d91102455c402a7b2220008be8714f644400117b0e29ec8880062fa1375d8d100045ec26ebb1a20078ee82dd763440011db05baec68800e3da0775d8d100247ac0eebb1a20048fa80dd763440071f301baec68800a1fa1774d8d100043ec2ee9b1a20078ee82dd363440011db05ba6c68800e3da0774d8d100247ac0ee9b1a20048fa80dd363440071f301ba6c68800a37e1d53d8d100054fc22a7b1a2000a9c8454f634400159f04a9ec688002b320953d8d100054f420a7b1a2000a9d8414f63440031bf0ea1ec68800297e1543d8d100
  | 8 => 0xb39a40100035a1d67348020275d5424e69004000ba9849cd2008001b50e939a40100faf2a0e7348020005f140ce69004000be1819cd20080015d70cb9a4010002dae15734802027db442ae69004000bab845cd200809d75108b9a4010002f8e057348020005f040ae69004000d68751cd2008001b50e839a40100fef2a1c7348020006e5438e6900403edcb761cd2008001d96ec39a4010003d2dd47348020006e53a8e69004000dc8751cd2008001e90ea39a4010003521d47348020007c5ba0e69004000dca741cd2008001b90e839a4010003e21d07348020006c43a0e690040419ea87dc520080833c50fb8a40100f778ddb714802000771bb6e29004000f6375dc52008001ec0ebb8a4010003e8dd37148020007d03a6e29004000fc373dc52008001f80e7b8a4010002ba61a714802027db542ce29004000b69859c52008001ad6eb38a40100035a1d67148020275d5424e29004000ba9849c52008001b56e938a40100036a1d27148020005e541ce29004000bc9839c52008001b96e738a4010003721ce714802020df140ce290040429eb875c520080015d70cb8a4010002dae15714802027db442ae29004000bab845c5200809d75108b8a4010002f2e0d7148020005e441ae29004000d6b751c52008001ad0ea38a40100036add07148020006d43a0e29004000dcb731c52008001b90e638a4010103789c47148020006f0b88e2900403dbe2871c52008001bc50e38a401010778dd8714802000771bb0e29004000de3751c52008001ec6ea38a401000358dd47148020006f13a8e29004000de1751c52008001bc0ea38a4010003d81d47148020006b03a8e29004000de3741c52008001f46e838a401000368dd07148020006f13a0e29004000de1741c52008001bc0e838a4010003e81d07148020006d03a0e29004000de3731c52008001f86e638a401000370dcc7148020006f1398e29004000de1731c52008001bc0e638a4010003f01cc7148020006e0398e29004041de3861c52008083bc50c38a401010778618714802020ef0430e29004040de3851c52008081bc50a38a4010103786147148020206f0428e29004041de3651c52008083bc4ca38a401010778594714802020ef0328e29004040de3841c52008081bc50838a4010103786107148020206f0420e29004041de3641c52008083bc4c838a401010778590714802020ef0320e29004000de3541c52008001bc4a838a4010003785507148020006f02a0e29004040de3831c52008081bc50638a40101037860c7148020206f0418e29004041de3631c52008083bc4c638a40101077858c714802020ef0318e29004000de3531c52008001bc4a638a40100037854c7148020006f0298e29004000de3431c52008001bc48638a40100037850c7148020006f0218e290040009
  | 9 => 0x63485200062e3a8c690a4000c9f7418d2148001938e831a429014bb108463485201f66c380c690a4000c7775d8521480018e8ebb0a42900032ddd361485200065a3a6c290a4000cd773d8521480019a8e7b0a42900f73c1c361485200063db2ee090a4000c7865dc12148001976c9b8242900032e19370485200066db1ee090a4000cd863dc121480799e0c3b8242900233318d72cc1201ce73390c39824000ce5721873048083dc04030e60900021fe15764c1200143e42aec98240008bf845d9304800317908bb260900fe37e0d764c12029e66396c69824000c6c65dc93048001958c9b92609000339dc8614c1201ce72390c29824041ee020185304800117f08baac6100062f2117558c2048c77c12eab1840078ec825d563080011ef02baac61000e3d2057558c200247c402eab18400087f855d163080050f90aba2c6102423be097458c2003c76412e8b1840008f7815d163080071e902ba2c6100123e2017458c200143f43eeab08406bc6c72dd561080d7cc843baac21012b1e1c3755842025738086eab0840008bf845d5610800317908baac21000237e0d75584200446e41aeab0840078ec825d561080ff8d8e43aac2101ff99084755842038e3c380eab084071e70101d5610800317d0fba2c2100030fdd774584200061e3aee8b084069cac72dd161080d3d4843ba2c2101232e1c3745842024758086e8b08400087f855d161080050f90aba2c21000237e0d74584200446e41ae8b0840078ec825d1610800187eea3a2c2100030f1d474584203f656390e8b08407eea4211d161080e1970e03a2c2101c3ac04074584200062fbaee6b084000c5c75dcd610800193ee9b9ac210003271d373584202d666396e6b08405aec421dcd610808d9b0e1b9ac21011bb404373584202366ac0ee6b084000c5f751cd61080018b8ea39ac21000327dd073584200064e3a0e6b084060ccc721cd61080c1d884239ac210113361c0735842022768080e6b084002c747594561080091e90ea8ac21001eb9209515842002578402a2b084001cb47490561080091e90ea0ac21001eb920941584200257840282b08402ea7485587310805b56908b0e621001f399c961cc42002679382c3988400087f855d931080050f90abb262100022fe11764c42000c5e422ec9884028a7485584310804f56908b086210002b5e0d610c4200267543eec9004000e6875dd92008001d50e9bb240101d2daa1f754802027eb543eea9004056d6b76dd52008001cd6edbaa4010003ca1d37548020395d543ee8900404edaa87dd120080a9b56edba24010003aaddb744802000795baee89004000f2875dd1200807fb96edb9a4010003b2ddb7348020007a5baee69004000f4875dcd2008001f16e9b9a4010003e21d3734802000574c34e6900404fb6a859cd20080016d3
  | 10 => 0x30a4000e976418c6148001d28c8318c29024bb4c80631852049f63100c630a4093ec42018c6148125da040318c2900038d55054185200056b418a830a4000ad58315061480011ef0ea98c29000e3d21d53185200055bc22a630a4000ab48454c61480015cf04a98c2900e6b9209531852000579c02a630a4041af08054c614800156d08298c290002ad61053185200047bc3a8630a40038f48750c61480014ef0aa18c2900029d215431852000573c128630a4039ae48250c61480015e700a18c290106bc20143185200053b4288630a4000a758510c61480835e501a90c290002bc60352185201cf70106a430a4000af38054861480835e100a90c2900e7b8081521852020d794068430a4000af180d086148073dc041a10c290002bce01421852020d784028430a4039ee02050861480835e501990c290002bc60332185201cf701066430a4000af3804c861480835e100990c2900e7b808132185201cd73416a030a4000ae582d406148083dc041a80c290002b9e0950185201cd72412a030a4041ee02054061480735cd05a00c290002b960b401852020f701068030a4000ae78250061480735c904a00c290107b808140185200053bc2a4030a4000a7485480614800156f08900c290002ad21120185200056bc1a4030a4000ad48348061480835cf04900c2900f2bce0120185200043fc2aed98a400287c855db314800117f08bb662900062f21176cc52001c6e41aed98a400087f855da31480050f90abb462900022fe11768c52000c5e422ed18a40038f4815da31480a799ce5b1c62900ff369c3638c5200063632ae518a4000cac645ca31480079c8c2b9462900127a201728c5200063c32ae118a4000cb8645c2314800f3d104b84629000f3c185708c5200143f42eec98a400087d85dd9314800317d09bb262900022f613764c5200446e418ec98a40038f4811d931480010ff0abb0629000a1f215760c5200045fc22ec18a40018bc845d831480079e0c2b8442901d21fa1b75485200061e326ea90a406ac7461dd521480d7ad041baa42901d61fa1f65485200061e3a6ca90a4057e6421d9521480ad8f0e1b2a42901ca2fa1b74485200061fb2ee890a4000c3c65dd121480d1968c3ba242901a76a083744852039c5f43ec890a4000c3f75d912148001878ebb224290157a908764485202a65c386c890a403e8de86dcd21480018becbb9a42900031719773485200064fb26e690a4000c9c64dcd21480bb9a8c3b9a429016b7208373485201fc6f430e690a4000c5f651cd21480018b8ca39a429000327d9073485200064e320e690a4061cd4611cd21480c1b904039a429018637a1f63485200062fbaec690a4000c5c75d8d214800193ee9b1a4290003271d3634852029f6210ec690a403fcd870d8d21480bb1bd0e31a429000317dd4
  | 11 => 0x4800187ce832cc2900030fd9574985200061e32ae930a4003cb4615d2614800187cebb24c2900030f5d764985200061f3a8c930a4000c3d7519261480018becb39cc2900031719673985200064fb24e730a4000c9c649ce61480079a8c339cc29000317d9573985200062e32ae730a4000c9f645ce6148001938c8b9cc29000f3518573985200062f3aec730a4000c5d75d8e614800193ce9b1cc290003275d363985200062f3a8c730a4000c5d7518e614800193ce831cc290003275d063985200063b3aec330a4000c7575d86614800196ce9b0cc2900032d5d361985200066b39ec330a4000cd573d8661480050fd0dbaac29015a1f21b75585200043f43ecab0a4000c3c74d9561480010fd0e32ac2900030f1d0655852000c5f436e8b0a40548bc86dd1614800187ecbba2c2900030f19774585200045f43ec8b0a4000c3f75d916148001878ebb22c2900022fa1c64585200061fba8c8b0a4000c3c7519161480018becbb9ac2900031719773585200064fb26e6b0a4000c9c64dcd61480018beca39ac2900031719473585200064fb20e6b0a4000c9c641cd61480011bd0fb1ac29000317dd763585200062e3aec6b0a4000c9f74d8d6148001938e9b1ac29000237a1c63585200062fba8c6b0a4000c5c7518d614800193ee831ac290003271d063585200047bc3ac230a4000a778558461480014e90ab08c290002ade1161185200055a422c230a4000ad78358461480015a906b08c2900031d9db65185204e739906ca30a409de6620d94614813bcc841b28c2902739c08365185200047ac3cca30a4000ab684994614800156b09328c290002b5a0e65185200056ac1cca30a40008f787594614800156f08b28c290002ad21165185200056bc1aca30a4000ad48359461480018ecec328c29026b9cc8065185204df33100ca30a409be64201946148135ce040328c2900032d9db64185200071bb2ec830a4000e3465d906148131d6641b20c290267a988364185204cf52106c830a4098eb020d9061480011eb0f320c2900029da1664185200053ac2cc830a4000ad68399061480015ab07320c2900023de1d64185200053bc2ac830a4000a748559061480015af06b20c290002b520d64185200065b3b0c830a4000e37651906148001c68ca320c29025bacc8064185204bf53100c830a4097ea420190614812dd6040320c290003359db63185200072bb2ec630a4000e5465d8c6148001d2ec9b18c290003a519363185204a769906c630a4095ec620d8c614812bd8841b18c290253b408363185200047ac3cc630a4000a768598c61480014eb0b318c290002ada1263185200055ac24c630a40008f78758c61480014ef0ab18c2900029d21563185200055bc22c630a4000ab48458c61480019acec318c29000395d9463185200072a328c6
  | 12 => 0x32b1d37258d200063bbaee2b1a4000c7475dc5634800196ee9b8ac6900032d1d37158d200066bb9ee2b1a4000c77751c563480018e8ea38ac6900032ddd07158d200065a3a0e2b1a4000cd7731c563480019cee438ac6900031e1d77058d200065c3a6e0b1a4000cf071dc163480011bf0eb18c69000297e156318d200052e42ac631a4000a9f8458c634800153908b18c690002b5e056318d200056a40ac631a4000c5e76d9463480011bb0f328c690002a7a126518d200054ec24ca31a4000ad68199463480015ab03328c69000237e1d6518d200054fc22ca31a4000a9c8459463480015af02b28c690002b52056518d200062f3b0ca31a40a0e5b201946348143c9c40328c690287930806518d205072c100ca31a4000c9e76d906348001c3ecbb20c690003871976418d200046ec3cc831a4000a5e8599063480014bb0b320c690002b5a066418d200056ac0cc831a40008df8759063480014bf0ab20c690002972156418d200056bc0ac831a4000ad481590634800193cec320c69000387d946418d200070e328c831a409ee9b20190634813fd1c40320c69027fa30806418d204f74c100c831a40088de8715063480011bb0e2a0c690003875505418d200056dc02a431a403ead88054863480015b700a10c6900fab62014218d2000567c12a031a4052acc82540634800159f04a00c69014ab32094018d200052fc2a4031a4000a5c85480634800153f08900c690002a72112018d201fe6c386c69924000c7865dc13248001970c9b82649000a3de1d51d852000c7bc3a83b0a4000ab684997614800156b0932ec290002b5a0e65d85200056ac1ccbb0a4000ab784597614800156908b2ec290002b5e0d65d85200056a41acbb0a4000e3765d936148001c68cbb26c2900029da1664d85200053ac2cc9b0a4000ad68399361480015ab07326c2900029de1564d85200053a42ac9b0a4000ad78359361480015a906b26c2900038dd9464d85200071a328c9b0a4000e5765d8f6148001ca8cbb1ec290003a5d9363d85200074a326c7b0a4000a768598f61480014eb0b31ec290002ada1263d85200055ac24c7b0a4000a778558f61480014e90ab1ec290002ade1163d85200055a422c7b0a4000e576518f6148001ca8ca31ec290003a5d9063d85200074a320c7b0a4000e355415361480015ad062a6c290002b560c54d85200047bc3aa7b0a40008f48754f614800156f08a9ec290002ad21153d852000573c12a7b0a404cae48254f61480015e700a9ec2900f6bc20153d85200055b420a7b0a4000ab58414f61480011ef0ea1ec2900023d21d43d85200053bc2a87b0a4000a748550f61480015cf04a1ec290132b920943d852000579c0287b0a403daf08050f61480014ed0a21ec2900029d61443d852001e3a30aeb30a4000c3e74d9661
  | 13 => 0x476c16ebb1a40038f681dd763480011eb03baec69001e3e60375d8d200143f42ee9b1a400087d85dd3634800f1dd05ba6c6900123b60b74d8d2001c7b40ee9b1a40008f581dd3634800f1f301ba6c69000a37e1d53d8d200054fc22a7b1a4000a9c8454f63480015af02a9ec690002b520553d8d200054f420a7b1a4000a9d8414f63480031bf0ea1ec69000297e1543d8d200052e42a87b1a4000ad78150f63480015a902a1ec69000297a1443d8d200052ec2887b1a4000a9e84997634800153b0932ec690002b5a0665d8d200056ac0ccbb1a4000a9f84597634800153908b2ec690002b5e0565d8d200056a40acbb1a4000e1f65d936348001c38cbb26c69000297a1664d8d200052ec2cc9b1a4000ad68199363480015ab03326c69000297e1564d8d200052e42ac9b1a4000ad78159363480015a902b26c69000387d9464d8d200070e328c9b1a4000a9e84dd7634800153b09baec69014eb3a0b75d8d201fd66c16ebb1a4000ad681dd763480015ab03baec6900feb6a0375d8d2029d6cc06ebb1a4000a9e849d7634800153b093aec69000297a1774d8d200052ec2ee9b1a4053ace82dd3634807f59b05ba6c690002b5a0774d8d200056ac0ee9b1a403fada80dd363480a75b301ba6c69000297a1674d8d200052ec2ce9b1a40008de8715363480011bb0e2a6c6900038755054d8d201fd66c10e3b1a4053ad9801c763480118b8c6bacc6900030f9d36598d200061f3a0cb31a4000c3f655d26348001878caba4c6900232718d7498d200061f3aec931a4000c3d75d92634800187cea324c6900030f5d46498d200062f3aec731a4000c5d75d8e634800193ce9b1cc690003275d36398d200063bb2ce331a4000c74659c6634800196ec938cc6900032d1927198d200066bb1ce331a4008cd4639c663480018eecab8cc6900031d1957198d200065bb22e331a4000cb4645c663480019aec6b8cc6900233518d7198d200043f43ecab1a4000c3c74d9563480010fd0e32ac6900030f1d06558d200061fb2ee8b1a4000c3c65dd1634800117d0fb22c6900030fdd76458d200061e3aec8b1a40008be87191634800187eea322c6900030f1d46458d200063bb2ee2b1a4000c7465dc5634800196ec9b8ac6900032d1937158d200063bb28e2b1a4000c74651c5634800196ec838ac6900032d1907158d200045fc22eab1a40018bc845d563480011bf06baac6900023be097558d200047bc0aeab1a40038f4815d563480011f700baac6900030fdd77458d200061e3aee8b1a400087f855d163480050f90aba2c69000237e0d7458d2000477c12e8b1a40008f7815d163480071e902ba2c6900023ee017458d200061fba8e8b1a4000c3c751d163480018beebb9ac690003171d77358d200064fba6e6b1a4000c9c74dcd63480018d8ebb92c690
  | 14 => 0xd849d9214c0111b9063b242980123e20076485300043fc2aec10a600287c855d8214c00117f08bb042980062f2117608530005734324210a6000ae486484214c0837c10090842980022fe11755883000c5e422eab1060088dc835d5620c0011ef02baac41800e3d20575588300043fc2ae8b10600287c855d1620c0111b906ba2c4180023de05745883001c7a40ae8b1060008bf845d5610c00317908baac2180223720d755843000477c12eab0860078ec825d5610c0010ff0aba2c21800a1f21574584300446e41ae8b0860008ef825d1610c00f1d904ba2c2180021fe1576484300143e42aec90860008bf845d9210c00317908bb2421817637e0d764843020df0402421086018978855c0210c02f37108b80421800276e0d70084300045fc22eab1e40018bc845d563c80091d904baac7900023de057558f2001c7a40aeab1e400087f855d163c80050f90aba2c7900123b2097458f200047bc0ae8b1e40038f4815d163c800f99ce4b1c63900fe37e1d63cc32003e66392c698640008bf845d5638800317908baac7100023de057558e2001c7a40aeab1c40048f8805d563880010ff0aba2c71000a1f2157458e200047bc0ae8b1c40038f4815d163880091f100ba2c7100fa37e1d63cca2020c7bc3ac310c40408fb865c221880099e0e0b0a43100021f61e64d95200052f41cc9b2a4000a5d8399365480014ed03326ca900029d60664d95200043fc3ac9b2a4000a5f8359365480014b906b26ca900029de0564d95200053a40ac9b2a4000c3f749d365480014bd073a6ca900029760e74d95200051f426e7b2a4000a3d84dcf65480af4dd05b9eca9015a9b60b73d95200053b40ee7b2a4000a7581dcf65480ad4f501b9eca9015e9e60373d95200051f424e7b2a4000a3d849cf65480010ff0ea1eca900021f21d43d952000537c1287b2a4057a6c8250f65480014ef02a1eca900029d20543d95200053dc0287b2a4056a788050f65480010fd0e21eca900021f61c43d95200061f3b6cbb2240008bd87997644800147d0b32ec890002a7a0e65d91200054ec1ccbb224000ab681997644800156b0332ec8900022fe1d65d91200054fc1acbb224000a9c83597644800156f02b2ec890002ad20565d91200051f430cbb224000c3e76197644800187eeb3aec890002a7a0e75d91200054ec1cebb224000a3e85dcf644800147b0bb9ec890156aba0b73d91202a556c16e7b224000ab681dcf644800156b03b9ec890152aea0373d91202ad5cc06e7b224000a3e859cf644800147b0b39ec8900022fe1d53d91200045e43aa7b224000aaf8254f64480ab55904a9ec890002ade0553d91200055a40aa7b224000abb8054f64480a957100a9ec8900022fa1c53d91200045ec38a7b2240018be84dd7634800117b09baec69001e3ba0b75d8d2002
  | 15 => 0xc382421090778618704842120ef0430e09084241de3851c12108483bc50a382421090778614704842120ef0428e09084240de3651c12108481bc4ca3824210903785947048421206f0328e09084241de3841c12108483bc508382421090778610704842120ef0420e09084240de3641c12108481bc4c83824210903785907048421206f0320e09084200de3541c12108401bc4a83824210803785507048421006f02a0e09084241de3831c12108483bc50638242109077860c704842120ef0418e09084240de3631c12108481bc4c638242109037858c7048421206f0318e09084200de3531c12108401bc4a638242108037854c7048421006f0298e09084200de3431c12108401bc48638242108037850c7048421006f0218e0908420287e87dd560084af8d8e5baac01092f1d1c775580212bf34106eab00424be7010dd5600840117f08baac0108062f21175580210046fc1aeab0042088dc835d560084f98d8e43aac0109f71d1c475580213e734100eab00427de70101d5600840317d0fba2c0108030fdd774580210061e3aee8b004255cac72dd16008493968e3ba2c010957aa083745802124f58086e8b00420087f855d160084050f90aba2c01080237e0d74580210446e41ae8b004200c3f751d16008401878ea3a2c0109eb2b1c874580213de5a388e8b00427aea8201d160084f7d60203a2c01080317dd773580210062e3aee6b004200c9f74dcd6008401938e9b9ac01094f331cb735802123e6a38ee6b004253ec820dcd600848fda021b9ac01091f3660373580210062fba8e6b004200c5c751cd600840193ee839ac010803271d0735802129666390e6b004245cd4711cd60084a5d904039ac010917b404073580210163c3aca0b0042038f887541600840f5d104a82c01080ebc205505802100e5c3a480b0042038f887501600840f5d104a02c01080ebc20540580210043fc2aec90e600287c855d921cc00117f08bb243980062f21176487300246e41aec90e6000ae78648421cc0015cb0c9084398106f820121087300f4bc42ae010e601d9b8845c021cc00f9d4c4b80439800f3c985700873002674382c49946004cf070585318c0010ff0abb2431800a1f21576486300045fc22ec90c60018bc845d9218c0091f100bb2431816b3398b73486302ee6b30ee690c6000c6c75589218c001958e8b12431800eb9205624863002674382c490c6000c7475585218c001968e8b0a431801eb9209614863002678382c290c6003ce776484218c0019caec9084318106f8201210863000477c3ac43126000a6c85588624c00155908b10c498002b9205621893003e74312e119260008f787584614c0014e90ab08c298002ad211611853000572412c230a6003cf0615c2314c0050fd0b3b242980021f616764853000c5f424ec90a60008b
  | 16 => 0x1181211ed79c0a4230242008bf845d5630840317908baac61081e3b2097558c2101c7a40aeab1842008fb805d563084091f100baac6108021fe157458c210143e42ae8b1842078ec825d163084071e902ba2c6108023ee017458c210247c402e8b184203ce687dd92108401cc8ebbb24210803a91d376484213adb343eea9084265d6687dd521084d5aceedbaa421080399ddb7548421007923a6ea9084273ba687dd121084c9b4d0fba242109a369ddb744842100753bb6e89084200f2775dd12108401e48ebba2421097771ddb734842100763bb6e69084200f4775dcd2108401e88ebb9a4210803e1dd37348421007c23a6e69084200ae5869cd21084019ceed39a4210996d9a167348421005b2c2ce69084200d64759cd21084c974d0939a4210802e96127348421006d23a4e69084261bc6839cd21084017c50139a4210802f8602734842100573c32e69084200b67855cd21084cb6c90ab9a4210802e9e117348421325d2422e69084200be3805cd21084017c100b9a421080339dd87348421006b23a8e69084200da4741cd21084bb78d0e39a421080371a1c734842130ee3bb0e69084200ec7761cd210840198eec39a4210803d1dd47348421006e33a8e69084200dc4751cd2108401e88ea39a4210803511d47348421007c3ba0e69084200dc6741cd2108401b88e839a4210803e11d07348421006c23a0e690842419e687dc121084833c50fb8242108f378ddb704842100771bb6e09084200f6375dc12108401ec0ebb824210803e8dd37048421007d03a6e09084200fc373dc12108401f80e7b824210802b961a704842132db342ce09084200b65859c12108401aceeb3824210803591d67048421325d3424e09084200ba5849c12108401b4ee93824210803691d27048421005e341ce09084200bc5839c12108401b8ee73824210803711ce7048421205f1404e090842419e7875c121084015cf0cb824210802d9e15704842132db242ae09084200ba7845c121084c974908b824210802f1e0d7048421005e241ae09084200d67751c12108401ac8ea382421080369dd07048421006d23a0e09084200dc7731c12108401b88e63824210907789c07048421006f0b80e0908423cbe2871c12108401bc50e382421090378dd8704842100771bb0e09084200de3751c12108401ec6ea382421080358dd47048421006f13a8e09084200de1751c12108401bc0ea3824210803d81d47048421006b03a8e09084200de3741c12108401f46e8382421080368dd07048421006f13a0e09084200de1741c12108401bc0e83824210803e81d07048421006d03a0e09084200de3731c12108401f86e6382421080370dcc7048421006f1398e09084200de1731c12108401bc0e63824210803f01cc7048421006e0398e09084241de3861c12108483bc50
  | 17 => 0x24200ad88358060484018f4edb28c090ab39cc87651812156f3510eca30242ade6821d946048559ce043b28c0908023e61e65181210055d424ca3024200ab98499460484015b507328c090802b660e65181210047dc3aca3024200abb84594604840157108b28c090802b6e0d65181210056c41aca3024200c7a761946048555ce642328c090aaf9a884651812155f34108ca30242aae70211946048401974edb20c0908038ed9764181210071c32ec830242a8eb321d906048553d5443b20c090aa7aa08764181215475810ec830242008f98799060484014f50b320c0908029e61664181210056d41cc83024200ad98399060484011f70eb20c0908029ee1564181210053c42ac83024200adb8359060484015b106b20c0908032e9d864181210071db28c83024200e3865190604854dd6642320c090a9faa884641812153f54108c830242a6eb02119060484019b4edb18c09080396d9763181210072c32ec63024200e9b64d8c6048401d30c9b18c090a93b4c87631812152f6510ec630242a5ec821d8c6048549da043b18c0908023e61e63181210053d42cc63024200a798598c604840157509318c090802ae61263181210047dc3ac63024200a7b8558c60484014f10ab18c090802aee1163181210055c422c63024200cda7618c6048401cb6ca318c0908039619463181210074db20c63024200e986418c6048545da642318c090a8fb2884631812151f64108c630242a2ed02118c6048401c72a82a0c090802b6a0c54181210056cc18a830242008fb8754c60484091f10ea98c090802aee1153181210055c422a63024200aeb8254c60484735d104a98c090802bce0553181212057840aa63024200aba8414c604840157308298c0908023ee1d43181210247c43a863024200a7b8550c60484014f10aa18c090802bae0943181211cd74412863024200af38150c60484815e102a18c0908029ea1443181210053cc28863024240af281d4860484015e303a90c0908e7b8087521812100579c0aa43024240af0815486048473dc042a90c090902bca07421812100578c0e843024239ee021d0860484015e702a10c090902bc20542181211cf7010a843024240af281cc860484015e303990c0908e7b8087321812100579c0a643024240af0814c86048473dc042990c0908e6baa0b511812100574c16a23024240ee021d4460484015d704a88c0908e6ba20951181212077010aa23024239aea82d0460484015d305a08c090903b8087411812100575c12823024239ae8825046048481dc042a08c0908e6baa0b311812100574c16623024240ee021cc460484015d704988c0908e6ba20931181212077010a623024200a7b8548460484014f10a908c090802aee1121181210055c422423024200adb8348460484015b106908c09090abae092
  | 18 => 0x840317908bb2629096b331cb634c5210063632ee498a4200cac64dc931484051f70ea86c0908063ee1d40d81210055d424cbb024200ab98499760484015b50732ec090802b660e65d81210055dc22cbb024200ab88459760484015b706b2ec090802b620d65d81210071db2ec9b024200e3865d9360484014f50b326c0908029e61664d81210056d41cc9b024200ad98399360484014f70ab26c0908029e21564d81210056dc1ac9b024200ad8835936048401c76ca326c0908038e19464d81210072db2ec7b024200e5865d8f6048401d36c9b1ec090803a619363d81210053d42cc7b024200a798598f60484015750931ec090802ae61263d81210053dc2ac7b024200a788558f604840157708b1ec090802ae21163d81210072db28c7b024200e586518f6048401d36c831ec090803a619063d81210071caa0a9b024200ada8315360484015b3062a6c0908023ee1d53d81210047c43aa7b024200abb8454f604840157108a9ec090802bae0953d812126d74412a7b024200af38154f60484795e102a9ec090802aea1053d81210055cc20a7b0242008fb8750f60484011f10ea1ec0908029ee1543d81210053c42a87b024200aeb8250f604849b5d104a1ec090802bce0543d81211e57840a87b024200a7a8510f60484014f30a21ec0908131e18175981210061f3a6cb3024200c3e74196604840187ecaba4c0908030f19574981210265c302e93024200c3e75d92604840187aebb24c0908030f9d464981210061eba8c93024200c5f659ce60484018b8cb39cc09080327d9273981210064e324e73024204cd8609ce60484018becab9cc0908031719573981210064fb22e73024200c9c645ce60484099b0c0b9cc090803179d763981210062ebaec73024200c9e74d8e604840193ae9b1cc090803179d463981210062eba8c73024200c9e7418e604840193ae831cc0908031e9d760981210063cbaec13024200cba74d826048401972e9b04c090803369cf60981210066cb9ec1302420287e86dd560484d50f90dbaac0908021fa1f65581210061e3a6cab02420087e871956048401878e832ac0908062fa1b74581213445e436e8b024200c3f65dd16048401878cbba2c0908022fa1f64581210061fbaec8b024200c3c75d91604840117d0e322c0908030fdd464581210061e3a8c8b024200c5f65dcd60484018b8cbb9ac09080327d9373581210064e326e6b024200c5f651cd60484018b8ca39ac09080327d9073581210064e320e6b0242008de87d8d60484018beebb1ac090803171d763581210064fba6c6b024200c9c74d8d60484011bd0e31ac09080317dd463581210062e3a8c6b024200c9f7418d6048401938e831ac0908023ee1d60181210053dc2ac03024200a7885580604840157708b00c090802ae21160181210056dc1ac03
  | 19 => 0x3179d76398d210062ebaec731a4200c9e74d8e634840193ae9b1cc6908031ed967098d210063c32ce131a4200cbb649c26348401970c9384c69080336d8e7098d210466c31ce131a4200c7b655c263484018f0cab84c6908032ed917098d210065c322e131a4200cdb635c263484119b0c6b84c6908021fa1f6558d210061e3a6cab1a420087e871956348401878e832ac6908030fd977458d210061e32ee8b1a42008be87d91634840187eebb22c6908030f1d76458d210045f438c8b1a4200c3f751916348401878ea322c6908031ed977058d210063c32ee0b1a4200cbb64dc16348401970c9b82c6908031ed947058d210063c328e0b1a4200cbb641c16348401970c8382c6908022fe117558d2100c5e422eab1a42008df835d563484011df04baac6908023de057558d210047dc02eab1a42048f8805d5634840187eebba2c6908030f1d77458d210043fc2ae8b1a420287c855d163484011bf06ba2c6908023be097458d210047bc0ae8b1a42008fb805d163484091f100ba2c6908030fdd47458d210061e3a8e8b1a4200c5f75dcd63484018b8ebb9ac69080327dd37358d210064e3a6e6b1a4200c6c75dc96348401958e9b92c6908031d1d77158d210065a3a6e2b1a4200ce772dc563484018f6ebb82c6908031e1d77058d210065dba6e0b1a4200cb874dc163484019b6e7b82c6908031edd47058d210063c3a8e0b1a4200cbb741c16348401970e8382c69080336dcc7058d2100675b90e0b1a4200cf3711c163484011bf0eb18c69080297e156318d210052e42ac631a4200a9f8458c634840153908b18c690802b6e016318d210056c402c631a4200c5e76d9463484011bb0f328c690802a7a126518d210054ec24ca31a4200ada8099463484015b301328c69080237e1d6518d210054fc22ca31a4200a9c8459463484015b700b28c690802b62016518d210062f3b0ca31a42b0e57211946348563c9c42328c690ac7930846518d215872a108ca31a4200c9e76d906348401c3ecbb20c690803871976418d210046ec3cc831a4200a5e8599063484014bb0b320c690802b6a026418d210056cc04c831a42008df8759063484014bf0ab20c690802972156418d210056dc02c831a4200ad880590634840193cec320c69080387d946418d210070e328c831a42aee9721190634855fd1c42320c690abfa30846418d215774a108c831a42088de8715063484011bb0e2a0c690803875505418d210056bc0aa431a4261ad48154863484015af02a10c690986b52054218d2100567c12a231a4260acc82544634840159f04a08c690982b32094118d210052fc2a4231a4200a5c85484634840153f08908c690802a72112118d212ee6a38ec69924200c7465dc53248401968c9b8a64908021fe15764c5210143e42aec98a42008bf845d9314
  | 20 => 0x2ec1ce9b2a4200a3e84dcf654840147b09b9eca909ae9ba0b73d952135536c16e7b2a426aa7681dcf65484d74eb03b9eca908029ea0373d95210053cc06e7b2a4200a3e849cf654840147b0939eca908021fe1d43d95210043e43a87b2a4200a6f8250f65484d74d904a1eca908029de0543d95213553a40a87b2a4200a7b8050f65484014f100a1eca908021fa1c43d95210043ec3887b2a4200c3e76d97644840117b0f32ec8908028fa1665d91210054f41ccbb224200a9d8399764484015750132ec890802ae60265d91210045fc3acbb224200a9f83597644840153906b2ec890802aee0165d91210055c402cbb224200a3e86197644840187cec32ec8908030fdd675d91210054f41cebb224200a9d839d7644840147d0bb9ec8908028f61773d912134d57416e7b224268aad82dcf64484d156d03b9ec8909a6ad60773d91210055d406e7b224200ab980dcf644840147d0b39ec8908028f61673d91210045fc3aa7b2242008bc8754f644840155f04a9ec8909a6ab20953d91210055bc0aa7b224268ab48154f644840157700a9ec890802ae20153d91210045f438a7b2242008bd8714f644840317d09baec6908022f61375d8d2101c76c16ebb1a42078f581dd763484091f501baec6908023e60375d8d210143f42ee9b1a420087d85dd363484071db05ba6c69081e3d60774d8d210247d406e9b1a42008f980dd363484051bf0ea9ec690802a7e1153d8d210054e422a7b1a4200adb8054f63484015b100a9ec690802a7a1053d8d210054ec20a7b1a42018df8750f63484014bf0aa1ec6908029721543d8d210056dc0287b1a4200ad88050f63484014bd0a21ec6908029761443d8d210054f424cbb1a4200a9d8499763484015b50132ec690802b660265d8d210054fc22cbb1a4200a9c8459763484015b700b2ec690802b620165d8d210070fb2ec9b1a4200e1c65d9363484014bd0b326c6908029761664d8d210056d404c9b1a4200ad98099363484014bf0ab26c6908029721564d8d210056dc02c9b1a4200ad8805936348401c3eca326c6908038719464d8d210054f426ebb1a4200a9d84dd763484b559d05baec690976b360b75d8d212ed6b40eebb1a425aad581dd763484015b501baec690802b660375d8d210054f424ebb1a4200a9d849d763484014bd0bba6c6908029761774d8d212d567416e9b1a425dacd82dd363484bb5ad03ba6c69096ab560774d8d210056d406e9b1a4200ad980dd363484014bd0b3a6c6908029761674d8d210046f438a9b1a42008dd871536348401c3aa82a6c690976b360870d8d212d56ac08e1b1a4208c5c635d6634840187ce9b2cc6908030f9d06598d210061fb2ae931a4200c3c655d26348411938c6ba4c6908030f9d76498d210061ebaec931a4200c3e75192634840187aea324c6908
  | 21 => 0x340001000100200080ac02803400802000006802800002c09400400c01406401c04402401001c01c07403400404800808c00001403411401c00800402c0bc00c01c00000c01001c23c06800000001000000000402c0d800001c0c403005409c01803000800008403001410400000c02800005403002400000001400007c00004400405c01000c0200100d00000040380000000fc01c00000805801401406c06c00001000401000000802c00800406400000c0200040100000340080000a40080040840040140140000140280000000c800000400004800c00000002800003c01408800002409803807400800000000801400010001400400401001800c00c0040001bc00c0040680180340040e400000007400000000001800001002001400400404801401408000404002000000000801400c02401403400000c04007400401000c02403000c0100080040000e406c00400800c00c0000040000a00000840100040c800400001803802401800400400c0180000080040000000d80d401800002400c024011ef0eb08c2990029d21561185320055a422c230a6400af080584614c8011f70eb00c0990029e21560181320055c422c03026400af081580604c80117f08baac2190062f21175584320047dc02eab0864048f8805d5610c8010ff0aba2c21900a1f21574584320047dc02e8b0864048f8805d1610c80117f08baac0190062f21175580320047bc0aeab0064038f4815d5600c8010ff0aba2c01900a1f21574580320047bc0ae8b0064038f4815d1600c8079c8e2b1265188023be1d62189310053642ac43126200aac84588624c4015d100b10c49881f39189718c9310047dc3ac03026200a7885580604c40157108b00c098802ba20960181310045fc22eab1062018bc845d5620c4111b906baac4188023ee0175588310247c402eab10620087f855d1620c4050f90aba2c4188223720d74588310047dc02e8b1062048f8805d1620c40117f08baac0188062f211755803100477c12eab0062078ec825d5600c4010ff0aba2c01880a1f215745803100477c12e8b0062078ec825d1600c40117f08baac7908062f2117558f2101c76412eab1e42008fb805d563c84091f100baac7908021fe157458f210143e42ae8b1e42038ec825d163c84011f700ba2c7908123e2017458f212ec6fc3ac798e42008bf845d5638840317908baac71080e3d2057558e210047dc02eab1c42048f8805d563884010ff0aba2c71080a1f2157458e2101c7a40ae8b1c42008fb805d163884091f100ba2c71098637e1d63cca210043ec3cc9b2a4200a5e8399365484014bb07326ca908029ea0264d95210053cc04c9b2a420087f8759365484014bf06b26ca908029720d64d95210053dc02c9b2a4200a7880593654840187ee93a6ca9080297a0e74d9521005
  | 22 => 0x805001801400401403005000c00000401800401c0100200000040300200e801006c02000000002c00000004401c00412402400403000401000800000001000002400003c00400000000004403000000401800000002c0140000b800400003c00c05400000002400c00c00000001401401800001000400400000000420000c0180000300000100340c817403000c07c00800400000000400402c02c00000800806023405811c0280e400010c03002000003402c01400000000801806c0000380040500000201c401004405002005c03000400400000c00000400400401000c00000000000003003003402002800000000400c00400c0000180e801002c01006c09800000002004400403000403801c00c00000001812400007000000400007402803407c01401c0100ec0400d000800002000000800412000c1541c400005007000808401000000000400c0cc00400c01000402801800001800c00c0b803406800014c03c06001808c00401803800000c0000000040040040000bc04400002803c04401009000003c00002c00000c00000001c05400400006007804804003000402400401400001804805001800003401405000801c0080040bc00009402000802801000401402001000403402c0540c400000402802800403000c00000402c02000800c0000500240c400400006800000000002408804800402000800400c01400006408001400005402009c06001c02400002401001000801403003800005400004401000401800c06c01005c03c00c0000040040cc00001802000c02c01407c09c00005c02c00005001800800c00000407400402c01800000c09400400003000000000c0040000100340080000040280000300b00941140e000003801001401801400400000000800400003400000c05801c00c0300c812401400000402001804802802400000404000806c0040200b400800800800400800403c00c06000c01011807400001c00000400000c00000400001001802800000800c03c02001008403403c03800000400800001c00400800400002000000000002400000400000403409000000001401c0040400140080000340000340080580040240140340200080080300040080200340041980080340000240400000b000405000000800012001800c03400000000008400c00800800001c00006802c00405400003c04800c00c00c00002c01410800000000001802410403800400403c0000a802006002c01800801c0840000100780040140840d000c0bc00004000000400001400005009400001c00802000807c05813c02c01802800c00800006c05800000800402c01c02c00400400007802800006800800800c00000406400003c01c04001809c06c00801800801013000800001806400402c03c0000340a400000000005c018004
  | 23 => 0x822c0000005c500000009f83908000d5c8e14e40a7c0007514838c0847a9b50001cfc000ad12dc84c8b0e8e93ec00ac0002420001d5c0645b859e097cef4aa91dfab94c705f94df8ec04065223a7063564c27252a06005e474c36d938c7bc03a000268c0007b50f88a880008bc15e02483e40ef26304b027444438e0f841044175c01140a20458210ac109369af44100807365ef369a10914473100000005f88e2188800106800012180016b6627343a9242a4043112082097a0cb15aa2d948005b2610c240000000400d609de24e0002890b60b7243e2be83d641a52813fc00055843b9cc8a6263a2c0a93cc886831cf881d20a2c54b284841507f9366a4616049145231e053d476a1f20310e7646836ea2e1646b3a1e80c0467a8e64cc8b64e748ee0b81248376a632a9a9d1710561199918038499d00028847089d80001e8400062635c92180008cc1f807e0d52b4e000000146e0000c40000000b130559d8072a41d0e504fc7b28ff16f05f40003363d79150cc825a21a1808d9c93f35d88ec1c037f3358ca00e000000000011480000000d4068858356d8c1926c00043a92c4a120003ff0cdc00059f161a1e93ba7c025803247462580002a755a02dd00013f0dcc37533a00dc4c60002b30f58b42000000129006c6d905c00013006961929e44be261c575aae80002820000000536a010000fec000978000000096ca2a00018d0b12a9c4d1000019e3693200658e9e2c81f8997924a8875bd251c1187ed54f8fb89a800000026c800009425989b400021614721308188b5413ab68a74a2b501826c16e41028c29487a42b9303993491ea3547c270d6e22ff4c810b15929e159f132d56a230022ab8420487308319b81d20002710a7800000052e80004d66cb37a2d2c0004ed5daaa190300590e403200003ab2898c50e2a43617099e06160000a0800041a06620312ad31400000000000000000249f7ce0e1da2f400000001464af86e000000004395552b8b75547800000000047797580000a136100009f411f19d225542215b49a000040a7672d5112555866d3f2a134d3c1f71e097d93922a60000000d26657174162172eb301fb030ce8e4b81dd2da959c9324fa89714c849c1acad7911c6a057f0c3c0f40e6561ab606de3c20609a145ec5b7000258833662345698485087721e395344aaaad07a06f8e3a51d38c97d527800059a0e257687bc04287155203ec0001dd077051500000000303ff23f197542840917180011e40000001f353ee0004c88e34d444da4dc95c5466b824311c1448a3ad2450e640008313d3001006c01401400000000400400400c00408800000000000000c07802002c00400c0000040200040a402000001400006c00802400804004c04400401c01c21000c01400000400002001000400006402800c02c0580080000
  | 24 => 0xe5d929510a49a40005a900590f68b02cb991412605d0001fd017e0002ce91886a69c246fa5000ae00000010ece14b083ae000000000000000cc0000000b18000f4863d1e62b516580002618374d6e8ac38200008aa00000023291360004be82544d40004fb00015300db18380ed1020005aa2358f3c2011a392443f41ea3bf0c21154b481e182d13c8a9958809054ae1a842f8385128ba754481a03667404ef07b52a49b315092f8000538225a0315765fc11a00b000000020102e491a22538317207004885b287846986bd404a3e89728740002b00d1eb3d000000000045d4dd2b1c92e8c50000e5020200008e0680e82404190846c7045f331b27c558299e0a626dd60295005316613806ea1e681b0e666fa40598d43e87f65a609f0600afc4bba27854a7a34e8a1e4a480e84531c98da4a6a05f1f8433260957d81b843487e41294385a07d24c71a2864e92a2538000768ba02ee27fc00000000000000000002f91820d542c14840000a6e0002ef2498df800000021800000005ce2acc0000000879ddd6302f93f50000ec8000473a6710bc97e5bf29447fa9f3479a47d5c8b351d20f8d44e01550f062d50e42826b82280009c63e7a0008ac00001c00003ae00022d000109eb3b00f000000000000000000001ae24f074141229900000000006470000c904289853c6ad980006c62c61784000ab82f398fd0602eb0538000000a9a58a1fa40000000002a9c72499b35a8e448383100f78f5066419111caccc2081173881d4024832b4c30e3127aa3e583a1740a67ae13413f89c84704781aacdfc81c221009c4f42405d8028165a5721c08000e4016a2ff13940003e0298172d6e0a9129dac3400000040184690b449423f803cad00ac2c70000000000379000051e00027404c00000005c209d02460000f4800160a9ae0000000c5a06d17311a907644100028b4b9c557000000000033441201846e2ab2000231c09e00000000000001781b32ad1408b0320a95e4832a174ca9e3c7726f14b39380ca85a300000000000000a8000000000048900000000003ad273c0000003af00011b26790000bf40003f7000000000000e56f0000422689231ac790aa2d710505381082892812160552b2b1a7811000034306fabe0cfe22d5a200001e6000124a8680d21b229a152121a4643f10000000b002cc98840003744682ac4ec2119000184000096a487193ca8a729000104844472850c8a60cf864e1c78edcfae238000136cdb422733d26514b089c00027f00006ad3c21a6805e53908480016e8000357a24483c5a81232e540001a10000c38ad236e0b8963d55c00000000000000004328094e2e1de00012156b24755051c351086ca3ff90950f036b41ba9047f817541e0000194aa04360a0567297c3a5a5742442511978b814b47493891acc000000130
  | 25 => 0x6026557278c2998000cb25ed14d10a83583193fd1e7cbd68723e0ae914bc07313f2ec90da85329e885489c7452bda4c51d84354f30628b86b7749b9fb0ea4a821372e651b692b1d70000bc48ba1c9911c69494c257999571c0f51582bb816c9290aa80000002d800013149089461b515bd3d26a628599f54ea3d52219df0c0200000029342ca0b53e399ec2c8000000211000090b53100010c882b1910d1443200000029c8000a1051010f8ce46f00eb27a0ce28154f0296c1b05ff555083c59245737191dc52023a3f0183408c06701aa9c15ae1384358ef0c3c6b4146800163a9820002970000b792821b40ef649619c01ac0000000fb0b9c88c5644e52dd81a600000000001660003d500007fc46c27daea170600000002bcc940dc1199c4d1ea76d4882515004a9540a179000000032580012403aa2a70a749c21923fc29b14f22e53ecad4066083a2bea808f9c50837b922ce4e7465c39e70aac312071ae186c895a5b617dc88a19736e05202541d139a14a53c46172ec21a47b48594c0a4ec2f208f11425d005c23e17527045fc00805809d42a8a2811e2e055363b32e80ddd1bc6923dc29d810c49a1579ff55c65705a38610d984de2da800041678b0001f684bc1fc2d31b855e65540f9873c26e0002a38c7925e2860510facbaa10e2a10350aa4a8a00025054880004082e305f043322f0000000b2f542ab303c8b5f57fa43d35656047182e8d8e8a80ff0024f6e9f420381fc2308d111bad606c0aa64cb0170a40ab006b00a876a9ed06699c0c1819335b1e6484838b0898eb0a34437051a320d3898c53020a965c81d00015f0e886ac4111db830c00055298ec99269b2098ebd5f279d3c804cc1f07c327e80000f69600ac2d58f8a63917996500007960c80a480007b451781e44049ef1f98069462000250262400012856210f407e2d207f8af551c8fb44f9bfd1b0b460afa9c52da661000067527461d28685ec7528b132aa20c03e3171ce927d66c9fa2a49949058493540250cb8835e319117cf0c6945070480764a1c08403491c857a23c2c8067237b3979301616a6f4ea12dc00016f3ac869161e6b116a1868ee01810e39b780000003770000e28bac23a22312e0000163ad5c0004ae04fa06c0001d8396084917e58519fa3f51ee083046960874a4c12d29a002dc96f4da1e20cd030c4c69e248d252136aa22c45c0ed29784f412227d58d89dc4fe36c1bc9a109d84f53379208fa88c2252a05c6408a332c146c7447e757315b16c200522cad15026604127a564a6a8ae56a90f0c563c914ba0cc8445d304d22806365460310a9cd800d10cf83795244a340917b83302b256783f46be5af0ba1ea0b2c96b4e200b527055e2970940f58ba51ee2dad6486bc01e00c40065e62c827710926d434fa2f923c6fd000178c64c9194ec8de132
  | 26 => 0x248bd0000fd5472aa237b0000000aa10b6a1583c620900004d8a886d85b98aad35447202500000001d2003a2404c80000000000e6002251a00014d611430f80015c07b10001a185064f9000000095260e230800003a4f85a129ec1ec6a72ba8c4d5e272d0001a212062ad00000015fa3613af800169405f3d59f30d9084b2730278000a181f906302ee00056e24d46ae84a0928724312b85000000018e0754b3279449675b0002ec43caa25384818c3b2bb329f07b0e024b20a584f0faa7de49c8b8880283905510fca147bd26713c834468b3c10ac4d9294e5cdac4873491b5b38870d22151532ab357422df4a50d6c0fa9492ce01c804201711f89303f2591381a60c0aaa7f18e284cfeaa8457784304f25230721de505066c24389596c015c4968fa07da17e5d52e3cae848c2a78d9c2d8b3f28cac9c14aa1f11b17ece1640a1db212004c8e850a85285487ba41b26844e6bab2c228148065e951e8d7421421f5bfa5e947eb1a5b1adece6c1d3198aad8c502cd49f233d4645db0ac9ae86086df2fc194081635c3ee0dcd2aab9f4f624c101e36d1edac551ec30d2b995015ba47912ea170b5c05800000013aab314400cf08908c137c8ea050e2ed00011cce5439e2b6800000037d000180cf720002fe8000000a4e0000c140009b833b8000000916000000059e6765dc80000000b1360815865a8b200007b84c452834088111a80ec47c9e5424e0d703029e8b8c0c517da81c8229bd020800175cbb81f31d580000000002380000076408a2ac5de0000180000024823000057836ea3853e190c31c0005850000bd800002716e87a600400019255be8a51a4002c8a67ee000000000094b00005fc8e2913204262c00060050601f04e047d26b07fd6120000e2264919c5b20001bcd51a09645b9cdce3080728780f47141070ea96a542c6e72660100b1437e40697503c00c00000fd13e42cb0002ba40000005090000000000000241800097225d06a85549fd594006d0dc79229b1d285b466026c288c6c46062cd84012c874800028a41ee00059c094cf7c8a15558f182161c3282908d08e0024f80000e1e6131b191bd6de37611016ac6f46240a69e0125ca48319acc865ca6d413273103228b576a020706166293801906482d48ba25cd1832a533808c35e46b16aa75cafe4f439e03e825c8714bd8000d3260557a812ccea4df5cb00000005ca50580001d400029f800174c7d63889da44b606f0000ec40528dd12b800000000002d00000002c21e728f15e087f1df03c80001b13aea14889e3523c71d98120295206ab6501c0fc00020f400000055fa6a4a0c0000000000000000286000122a4b43d380011685c241080000006eb00026f963e2664ad95f80001bd36ba4ccccc2f044e9904abe7a0000156839c0e50002d88a0e6e420a1f9063e40f02
  | 27 => 0xe39cb83380000000000000ab729317440009c71ce0eed58c6223f8800133427b54a0770b786d6583106c8602b7391a01043c5623929c90a020f05a49a380000003241f1022212f5c6ab2c27c1870001e600007d32aca9f8000000445000085a2d3000095000096e11198440006b00c79a7540063c38d80000000000000ab000091c000000045448153e80017120001601c7cefa0004009a3411c00030c139cf0e00000020d40009ac4bf800135a820490a33428420e2a81a5c954a303e4122456c126009aca891c7534aa05e95ac1c6522800120050341fa18cb8009d4d329e0b5a6671f51b152888673d98f5d62e96944d1284d8822b3e49efc58c0fe0d2a57800040508b1e0c0e82590001988b6687d000114833c1b64ab8fe45dc9d31f49c315900004379e500001151108c740385d7157107d5e44395d6a91d12c5df449a9b952e23546baba026ab6e3d691e93fc0002750bd40008a94c9a3d0dd2a662800afc0009bc14001504ce8d250d811c6768061aa0788f5224725302250a0af72e4a69559426546e07045c859e27b2198be80000b598dc0001cd0002d3d73466a5a693dd2120784a68a58ca245c0000a8c0005cf0001e14be0614000000171600030b254d01400c10600016a6578457a1c059842043b00006e46be50313747ba26c4e29cacdf057700000012149272d1156c870775000248d6c86e83412d70d64a433b5a2e41480c63232738a3e42f17d2da052834b178945c99e6691c31f4172832c3dd86681dc61b5d481dc1980b241f000066a7b01ad2394c2a99f00000000000001c41b44000aea20b00000686e046200003040000000d18aa26bf38029654982ba4bb16ec2c28615d18e853605b65d79ff00005c12251c7800045b3eeae440000002c306a400000035c086c8980ad50ea15c00059300000012d01f00aba8b02240005579b8800000000825613b60242139a600003df26980000000003b10000b160001a70000ad498418b23b400000000010b961c0002eeaaf40004901be0000000a533481199584ae200020591961df00085c955071659496542a600023e0b294be3420002db52587e807da22023a6c33769320fe00001f3a5e40002693a103e53d6abe54f2d047f43c5000000000000039c27693a47650000e600003a014518b923441854412640000001d315d848875438116800007d1000120c00000053099f8ede2ec0829cf426298726e1828f942a052583acc58000138abd80000000002c6513000015d997d18600052a80015a400d4f72691724176494087566e12d50698bcb580bb1c38000220323350825caca3d125e10c87906e5000069c0007731e00000d9e4bb31007990a260f2a58d540729d025a8c54ace0002c69e8849000058600009580000ca80000004bf1de8b395787b235425083805414352a58b
  | 28 => 0xc526ec00009480009e722000008f60001c816f50a82db0f400002b422900000008ec0000281288000000149ab9c0002134179ed918c1bc4eb1de16220883211274f4a05e5cf253c1b23d80329958bd41670408148f3400024c0001484a831378f3d64a22f3c9839d34e653146248911e36539c94711f86f500018642d252b2df1fac0005a44b8945000074d2df8ad0000b9000015ad2086a40a2800000000026387ec6808da00013402720480710000df60192759da0000b2226200009e04f321d10383ce708265057436a31a1e20000000bb71b8000036814700004d049499800004a51924cd5bc13c42e68383f923c4cb4b933f30bd0adc0000682a04cb619451d8f2c08438548e9c8809a00013c0000a9446715f2264a984ad0d5a7ec55009800026d8b0089201f272d37600006d02f573000019f0d247ca1d43bb0000c600002fd2d0c0007c2000080040c7db2ed1f195d830a0000510ed81401cb2a2d6faa730faa83c0009110002da573a0005ae800162c3032e62d6910c0d5421800164207156980000002d100005580008eb331a2cc71c5b400002a551862a3f18da0588a563b19fcd46c05100522252e6a6845da40429e22603f0c60a589882130ca503e3410ed8d350b61851fc0000a222b300000000005cd00018f800044d0b40000bca09c0ee86e8fee000274a6a0f140000001e6d76c55d03219cc5220bc3ac08b15e882e0e596c5034ac534a884092a55c00a2a8c8caa4a3cba3005382d615c18c45b881e4d8a4300002884c7a7e46a28fe10ba77cfde48053b86fcc4a8460be158ca5a00000013440001b000019700004d5118800111aaa400003382068a70dc84780007fb2189c682768453e5a8888dc9754b6068cb3473e4271d0c0000001cb81a92c282951d11b49dc1494a419302568410789bbc4c060b10c1144a4a16235294780004001d3a49100a7351e514c944c7715be2d00bc04d9475258c00051600008c80001fd0c1a7352a20004f1a55835a0000000fbc0008d5000000095014300889d80006a33bfad44e1ca695042c70eaa3e229e2409080028000234d0d0b55174971421a0000e6150c85600000000017440ae51714480002850610000b4e24d4428bdc000a9300017486ac9a00b0000034c0002
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x181f7560e75d911000607a1d54153634400181d875505418d1000683551831536244001a0d5460c541891020cb8a438154c62440812e291e01531891020cb8a438150c62440812e291e0143189105e709084751d16204177c28201d4745881058f11084751cd6204143c48201d4735881057f21084741cd620413fc88201d073588105d64ca1c75dd11004001d10751d373440100064ca10759cd1004001932851d27344010006581d6829cd10040019a074a0a73440105cd54a56751cd1004001592949d4734401000570a4a751cd1004001c53761d47344010007441d7741cd1004001552959d073440105c564a52741cd10040015c2929d0734401000724dd8741cd1004001d13751d07344010007441d4741cd1004001d20751d3724401000730dd873dc91004001d40751cf7244010007601d073dc910040738e07261a72440101ce581c9859c91004001932841d672440101ce681c9849c91004001932851d27244010006541d6839c9100400199074a0e72440101ce701ca839c910040739c07260e724401000634618739c91004001952851ce724401000664a10739c91004001563955c8724401000558255721c910040015a3945c8724401000568251721c910040015c3935c872440100057024d721c9100416f562959d4724401000568a52751c910040015a1949d4724401000570a4e751c910040015c1939d4724401000568e51751c910040015a0945d4724401000570e4d751c910040015c0935d472440105b558a5c751c91004001d2375dd07244010007481d7741c91004001562959d0724401000558656741c9100416b5a2949d0724401000570a4e741c910040015c1939d0724401000558e55741c91004001560955d0724401000570e4d741c910040015c0935d072440105a568a5c741c91004001d23751d07244010007481d4741c91004001d4375dcc7244010007501d7731c91004001d8374dcc7244010007601d3731c91004001562959cc724401000558656731c910040015a2949cc724401000568652731c910041675c2939cc724401000558e55731c91004001560955cc724401000568e51731c910040015a0945cc724401059570a5c731c91004001d43751cc7244010007501d4731c91004001d83741cc7244010007601d0731c91004001d2154150724401000570a4c541c910040015c193150724401000478e61531c910040731e09854c724401000538e59531c910040834e09654c724401000568e51531c910040015a09454c724401000568a50531c910040015a19414c724401000478e61431c910040731e09850c724401000538e59431c910040834e09650c724401000558e55431c910040015609550c724401000558a54431c910040015619510c72440101ce381c9868c910040831e09221d3244010
  | 1 => 0x607a1d54153634800181d875505418d2000685551831536148001a155460c541852020cb8a438254c61480732e292e01531852020cb8a438250c61480732e292e01431852062f09084751d16108175c30101d4745842058711084751cd610811fc50101d4735842057721084741cd610811bc90101d073584205de4aa1c75dd12008001d08751d373480200064aa10759cd200800192a851d27348020006581d6819cd20080019a074a06734802062552a56751cd200800158a949d4734802000570a46751cd2008001c4b761d47348020007421d7741cd200800154a959d0734802061d62a52741cd20080015c2919d0734802000722dd8741cd2008001d0b751d07348020007421d4741cd2008001d20751d3714802000730dd873dc52008001d40751cf7148020007601d073dc520080818e07161a7148020206581c5859c5200800192a841d67148020206681c5849c5200800192a851d27148020006521d6839c5200800198874a0e7148020206701c6839c520080819c07160e714802000632618739c5200800194a851ce714802000662a10739c52008001563955c4714802000558255711c520080015a3945c4714802000568251711c520080015c3935c471480200057024d711c52008185562959d4714802000568a52751c520080015a1949d4714802000570a4e751c520080015c1939d4714802000568e51751c520080015a0945d4714802000570e4d751c520080015c0935d4714802060d58a5c751c52008001d2375dd07148020007481d7741c52008001562959d0714802000558656741c520081815a2949d0714802000570a4e741c520080015c1939d0714802000558e55741c52008001560955d0714802000570e4d741c520080015c0935d071480205fd68a5c741c52008001d23751d07148020007481d4741c52008001d4375dcc7148020007501d7731c52008001d8374dcc7148020007601d3731c52008001562959cc714802000558656731c520080015a2949cc714802000568652731c5200817d5c2939cc714802000558e55731c52008001560955cc714802000568e51731c520080015a0945cc71480205ed70a5c731c52008001d43751cc7148020007501d4731c52008001d83741cc7148020007601d0731c52008001d2154150714802000570a4c541c520080015c193150714802000478e61531c520080811e09854c714802000538e59531c520080834e09654c714802000568e51531c520080015a09454c714802000568a50531c520080015a19414c714802000478e61431c520080811e09850c714802000538e59431c520080834e09650c714802000558e55431c520080015609550c714802000558a54431c520080015619510c7148020206381c5868c520080831e09121d314802000607dd1839d36544
  | 2 => 0x8579926871d77448421007411d474dcd21084c38c683dda734842100649a10759cd2108401926851d27348421006581d6809cd21084019a074a02734842100711ddb751cd21084014c5969d4734842167d51a56751cd2108401586949d4734842100570a42751cd2108401c47761d4734842100721ddb741cd2108401d0475dd073484210053165a741cd2108401546959d0734842167561a52741cd21084015c2909d0734842100721dd8741cd2108401d07751d07348421007411d4741cd2108401d20751d3704842100730dd873dc12108401d40751cf7048421007601d073dc121084838e07061a704842120e581c1859c12108401926841d6704842120e681c1849c12108401926851d27048421006511d6839c1210840198474a0e704842120e701c2839c121084839c07060e704842100631618739c12108401946851ce704842100661a10739c12108401563955c0704842100558255701c121084015a3945c0704842100568251701c121084015c3935c070484210057024d701c1210859b562959d4704842100568a52751c121084015a1949d4704842100570a4e751c121084015c1939d4704842100568e51751c121084015a0945d4704842100570e4d751c121084015c0935d4704842166558a5c751c12108401d2375dd07048421007481d7741c12108401562959d0704842100558656741c121085975a2949d0704842100570a4e741c121084015c1939d0704842100558e55741c12108401560955d0704842100570e4d741c121084015c0935d0704842165568a5c741c12108401d23751d07048421007481d4741c12108401d4375dcc7048421007501d7731c12108401d8374dcc7048421007601d3731c12108401562959cc704842100558656731c121084015a2949cc704842100568652731c121085935c2939cc704842100538e59731c12108401563955cc704842100558255731c121084015a3945cc704842100568251731c121085915c2971cc704842100730dd8731c12108401d43751cc7048421007501d4731c12108401d83741cc7048421007601d0731c12108401d2154150704842100570a4c541c121084015c193150704842100478e61531c121084831e09854c704842100538e59531c121084814e09654c704842100568e51531c121084015a09454c704842100568a50531c121084015a19414c704842100478e61431c121084831e09850c704842100538e59431c121084814e09650c704842100558e55431c121084015609550c704842100558a54431c121084015619510c704842163f0a080751d1600858dc30101d4745802150712080751cd600851dc50101d473580214f722080741cd6008519c90101d0735802120e3820176484218c0832e090219210853000607dd1839d3654800181f7560e75d912
  | 3 => 0xa09dc07a785b800000a4678f60f8001d0006f84c329e6a413aab0aa4f2446e0545107e000625e13066a4a60a3694020002b28020e002c21905c6997c2e0140112c2b000968449084601a5e00194232709500080a200322a288c6000b0000000000079000451ae000ce001b4002a0a6852a99c23d11c178001e0a60b1d0378702d1720029c0d85a530005c0000007aae800af0120e2242ba6646904ac1a0ad0805609e341ba7a1cca90243fad25e8fa990006c8000022c00000641f48c8e48681a05800a3a3e489ce4600010800971f83f1125d99c2a03c56abe00000888bcb280a7a800a5a86000820024636a104a09000072198002295e981a80000000000b40009f800922c04a800371268ba4e519f0648c8249b6000683a9500009893000000008580063000001800000021acc7598643240001fe0d1380a0b65d294398d49a208001d81b07c020e068800b227c4dab80014000000851ac539e2348c40b8005080058a181a8480e90e7eaa80089ca79660012e7b9346aa7a728000c000000186926a00000872b6b189a360000027245a76211b05700000000428be750000a96a47800182a281900551e0000000018e00284000263c23a8c15200000000003ca0c4903200000000000015608800002385a000000769d0a03b896620000023c7c9ec61000000ba71840a326e3a1bc2c81c7106e0392000000662627696400228358cc3080000058000f8a48005f80022196b11c87f01096160002ae2393e89910529de9494813a6c74a885b2048d0940000000000a60000028a0010884906388561298a7d8ec9593287a0a1400040a80aa9c0b38c00582816010000814050002c30020201c001b000140800000301c000100c1609010001a0105800021100008080007828000300004560008008000f01000000003078000a0089c180a01834000001008000c0180c041701000020c050180607000040202000001a040300404060082c0e021102800100c01c280000000040e018ac000102810000000607dd1839d3654840181f7560e75d912100607a1d54153634840181d875505418d2100686551831536048401a195460c5418121204b8a478254c60484732e292e055318121204b8a478250c60484732e292e05431812100709ddb75dd1210
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x20400035015464c541c12108401a80aa3262a0e29004000d40551931507244010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x5
  | 2 => 0x6
  | 3 => 0x2
  | 4 => 0x1
  | 5 => 0x4d
  | 6 => 0x4e
  | 7 => 0x3
  | 8 => 0x4
  | 9 => 0x94d
  | 10 => 0x94e
  | 11 => 0x124d
  | 12 => 0x124e
  | 13 => 0x138d
  | 14 => 0x138e
  | 15 => 0x8d
  | 16 => 0x8e
  | 17 => 0x98d
  | 18 => 0x98e
  | 19 => 0x128d
  | 20 => 0x128e
  | 21 => 0x150d
  | 22 => 0x150e
  | 23 => 0xcd
  | 24 => 0xce
  | 25 => 0x9cd
  | 26 => 0x9ce
  | 27 => 0x12cd
  | 28 => 0x12ce
  | 29 => 0x168d
  | 30 => 0x168e
  | 31 => 0x20d
  | 32 => 0x20e
  | 33 => 0xb0d
  | 34 => 0xb0e
  | 35 => 0x140d
  | 36 => 0x140e
  | 37 => 0x154d
  | 38 => 0x154e
  | 39 => 0x24d
  | 40 => 0x24e
  | 41 => 0xb4d
  | 42 => 0xb4e
  | 43 => 0x144d
  | 44 => 0x144e
  | 45 => 0x16cd
  | 46 => 0x16ce
  | 47 => 0x3cd
  | 48 => 0x3ce
  | 49 => 0xccd
  | 50 => 0xcce
  | 51 => 0x15cd
  | 52 => 0x15ce
  | 53 => 0x170d
  | 54 => 0x170e
  | 55 => 0x94055
  | 56 => 0x94056
  | 57 => 0x4b
  | 58 => 0x4955
  | 59 => 0x4956
  | 60 => 0x150a
  | 61 => 0x1549
  | 62 => 0x3c9
  | 63 => 0x15c9
  | 64 => 0x8a
  | 65 => 0x209
  | 66 => 0x1409
  | 67 => 0x128a
  | 68 => 0x249
  | 69 => 0xca
  | 70 => 0x1449
  | 71 => 0x12ca
  | 72 => 0x1489
  | 73 => 0x130a
  | 74 => 0x14c9
  | 75 => 0x134a
  | 76 => 0x124b
  | 77 => 0x138b
  | 78 => 0x98095
  | 79 => 0x98096
  | 80 => 0x8995
  | 81 => 0x8996
  | 82 => 0xcb
  | 83 => 0x12cb
  | 84 => 0x1609
  | 85 => 0x130b
  | 86 => 0x1649
  | 87 => 0x134b
  | 88 => 0x1440d5
  | 89 => 0x1440d6
  | 90 => 0x144b
  | 91 => 0x15c0d5
  | 92 => 0x15c0d6
  | 93 => 0x15ca
  | 94 => 0x252d5
  | 95 => 0x252d6
  | 96 => 0x24b
  | 97 => 0x3ca
  | 98 => 0x3d2d5
  | 99 => 0x3d2d6
  | 100 => 0xb0215
  | 101 => 0xb0216
  | 102 => 0x20b15
  | 103 => 0x20b16
  | 104 => 0x160a
  | 105 => 0x148b
  | 106 => 0x164a
  | 107 => 0x14cb
  | 108 => 0x15c255
  | 109 => 0x15c256
  | 110 => 0x3d455
  | 111 => 0x3d456
  | 112 => 0x289
  | 113 => 0x2c9
  | 114 => 0x409
  | 115 => 0x40a
  | 116 => 0x449
  | 117 => 0x44a
  | 118 => 0x180c
  | 119 => 0x184c
  | 120 => 0x198c
  | 121 => 0x19cc
  | 122 => 0x10b
  | 123 => 0x10a
  | 124 => 0x14b
  | 125 => 0x14a
  | 126 => 0x28b
  | 127 => 0x2cb
  | 128 => 0xc092
  | 129 => 0x24211
  | 130 => 0x12c092
  | 131 => 0x144211
  | 132 => 0x10092
  | 133 => 0x28211
  | 134 => 0x130092
  | 135 => 0x148211
  | 136 => 0x14092
  | 137 => 0x2c211
  | 138 => 0x134092
  | 139 => 0x14c211
  | 140 => 0x100d2
  | 141 => 0x28251
  | 142 => 0x140d2
  | 143 => 0x2c251
  | 144 => 0x188c
  | 145 => 0x1a0c
  | 146 => 0xc053
  | 147 => 0x3c211
  | 148 => 0x12c053
  | 149 => 0x15c211
  | 150 => 0x10053
  | 151 => 0x40211
  | 152 => 0x130053
  | 153 => 0x160211
  | 154 => 0x14053
  | 155 => 0x44211
  | 156 => 0x134053
  | 157 => 0x164211
  | 158 => 0x100d3
  | 159 => 0x403d1
  | 160 => 0x140d3
  | 161 => 0x443d1
  | 162 => 0x24053
  | 163 => 0x3c092
  | 164 => 0x144053
  | 165 => 0x15c092
  | 166 => 0x28053
  | 167 => 0x40092
  | 168 => 0x148053
  | 169 => 0x160092
  | 170 => 0x2c053
  | 171 => 0x44092
  | 172 => 0x14c053
  | 173 => 0x164092
  | 174 => 0x28253
  | 175 => 0x403d2
  | 176 => 0x2c253
  | 177 => 0x443d2
  | 178 => 0x21451
  | 179 => 0x20251
  | 180 => 0x21491
  | 181 => 0x20291
  | 182 => 0x214d1
  | 183 => 0x202d1
  | 184 => 0x24291
  | 185 => 0x242d1
  | 186 => 0x2c291
  | 187 => 0x44411
  | 188 => 0x44412
  | 189 => 0x215d1
  | 190 => 0x203d1
  | 191 => 0x21611
  | 192 => 0x20411
  | 193 => 0x21651
  | 194 => 0x20451
  | 195 => 0x3c411
  | 196 => 0x3c451
  | 197 => 0x2c293
  | 198 => 0x14112
  | 199 => 0x14113
  | 200 => 0x95d2
  | 201 => 0x83d2
  | 202 => 0x9612
  | 203 => 0x8412
  | 204 => 0x9652
  | 205 => 0x8452
  | 206 => 0x3c412
  | 207 => 0x3c452
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2015
  | 6 => 3831
  | 5 => 3002
  | 4 => 362
  | 3 => 3
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | 8 => packedAt gbK8 (i*26) 17
  | 7 => packedAt gbK7 (i*37) 28
  | 6 => packedAt gbK6 (i*48) 39
  | 5 => packedAt gbK5 (i*59) 50
  | 4 => packedAt gbK4 (i*70) 61
  | 3 => packedAt gbK3 (i*81) 72
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | 8 => gbHint (packedAt gbK8 (i*26+17) 9)
  | 7 => gbHint (packedAt gbK7 (i*37+28) 9)
  | 6 => gbHint (packedAt gbK6 (i*48+39) 9)
  | 5 => gbHint (packedAt gbK5 (i*59+50) 9)
  | 4 => gbHint (packedAt gbK4 (i*70+61) 9)
  | 3 => gbHint (packedAt gbK3 (i*81+72) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1720+((h/20+packedAt gbK8 (1560+(h % 20)*8) 8) % 151)*7) 7
  | 7 => packedAt gbK7 (82607+((h/671+packedAt gbK7 (74555+(h % 671)*12) 12) % 2660)*12) 12
  | 6 => packedAt gbK6 (200489+((h/1277+packedAt gbK6 (183888+(h % 1277)*13) 13) % 6118)*13) 13
  | 5 => packedAt gbK5 (189118+((h/1000+packedAt gbK5 (177118+(h % 1000)*12) 12) % 3603)*13) 13
  | 4 => packedAt gbK4 (26420+((h/120+packedAt gbK4 (25340+(h % 120)*9) 9) % 478)*10) 10
  | 3 => packedAt gbK3 (246+((h/1+packedAt gbK3 (243+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffffffc01ffffffe00ffffffcfc3fe1ff0fff
  | 1 => 0x3ffffffe00fffffff007ffff3fc3fe1ff0ff
  | 2 => 0xffc00fffffff007ffffff803ffcffc3fe1ff0f
  | 3 => 0xffffffffffffffffffffff0003fffffff
  | 4 => 0xfffff0000000007ffffffffc03ffffc001fff0
  | 5 => 0xffffffffffffff800000000003fffffffe0000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x56d5b2dc40ab5596e2055aaf2c5c1de0ef0777
  | 1 => 0x1226d56d56209aab6ab104d7552dc2ee1770bb
  | 2 => 0x9b4489b66b35104db359a8839a8eec3761bb0d
  | 3 => 0xc0300e3b8dc6e371dc6e3718e3f0001bbaddde
  | 4 => 0xe3b8e0030180c07e1f8fc7e103f7774001eee0
  | 5 => 0xfc3f0fc3f1f8fc00180c060203fbbbbddc0000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xe8e8e800e8008000e8e8e800e8008000e8e8e800e8008000e8e8e800e8008000e8e8e800e8008000e8e8e800e8008000e8e8e800e8008000e8e8e800e8008000, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_12220
namespace PEqualNP.Outside.L_meta_12220
open PEqualNP.Outside.L_meta_12220.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 3 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 25 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 17 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 3 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 25 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 17 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 3 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 17 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 3 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 17 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 66 := block_range (n:=66) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 66 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_96 : Interval s4Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_192 : Interval s4Atlas 3 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_288 : Interval s4Atlas 3 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_384 : Interval s4Atlas 3 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_480 : Interval s4Atlas 3 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_576 : Interval s4Atlas 3 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_672 : Interval s4Atlas 3 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_768 : Interval s4Atlas 3 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_864 : Interval s4Atlas 3 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_960 : Interval s4Atlas 3 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_1056 : Interval s4Atlas 3 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_1152 : Interval s4Atlas 3 1152 43 := block_range (n:=43) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 1195 := (concat (concat (concat bs4_3_0 (concat bs4_3_96 bs4_3_192)) (concat bs4_3_288 (concat bs4_3_384 bs4_3_480))) (concat (concat bs4_3_576 (concat bs4_3_672 bs4_3_768)) (concat (concat bs4_3_864 bs4_3_960) (concat bs4_3_1056 bs4_3_1152))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_864 : Interval s4Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_960 : Interval s4Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1056 : Interval s4Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1152 : Interval s4Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1248 : Interval s4Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1344 : Interval s4Atlas 4 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1440 : Interval s4Atlas 4 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1536 : Interval s4Atlas 4 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1632 : Interval s4Atlas 4 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1728 : Interval s4Atlas 4 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1824 : Interval s4Atlas 4 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1920 : Interval s4Atlas 4 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_2016 : Interval s4Atlas 4 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_2112 : Interval s4Atlas 4 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_2208 : Interval s4Atlas 4 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_2304 : Interval s4Atlas 4 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_2400 : Interval s4Atlas 4 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_2496 : Interval s4Atlas 4 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_2592 : Interval s4Atlas 4 2592 55 := block_range (n:=55) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 2647 := (concat (concat (concat (concat bs4_4_0 (concat bs4_4_96 bs4_4_192)) (concat (concat bs4_4_288 bs4_4_384) (concat bs4_4_480 bs4_4_576))) (concat (concat bs4_4_672 (concat bs4_4_768 bs4_4_864)) (concat (concat bs4_4_960 bs4_4_1056) (concat bs4_4_1152 bs4_4_1248)))) (concat (concat (concat bs4_4_1344 (concat bs4_4_1440 bs4_4_1536)) (concat (concat bs4_4_1632 bs4_4_1728) (concat bs4_4_1824 bs4_4_1920))) (concat (concat bs4_4_2016 (concat bs4_4_2112 bs4_4_2208)) (concat (concat bs4_4_2304 bs4_4_2400) (concat bs4_4_2496 bs4_4_2592)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_864 : Interval s4Atlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_960 : Interval s4Atlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_1056 : Interval s4Atlas 5 1056 84 := block_range (n:=84) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1140 := (concat (concat (concat bs4_5_0 (concat bs4_5_96 bs4_5_192)) (concat bs4_5_288 (concat bs4_5_384 bs4_5_480))) (concat (concat bs4_5_576 (concat bs4_5_672 bs4_5_768)) (concat bs4_5_864 (concat bs4_5_960 bs4_5_1056))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 48 := bs4_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_7_0 : Interval s4Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_7 : Interval s4Atlas 7 0 1 := bs4_7_0
theorem alls4 : ∀ k ≤ 7, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
  · exact alls4_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 66 := block_range (n:=66) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 66 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_192 : Interval s5Atlas 3 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_288 : Interval s5Atlas 3 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_384 : Interval s5Atlas 3 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_480 : Interval s5Atlas 3 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_576 : Interval s5Atlas 3 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_672 : Interval s5Atlas 3 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_768 : Interval s5Atlas 3 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_864 : Interval s5Atlas 3 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_960 : Interval s5Atlas 3 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_1056 : Interval s5Atlas 3 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_1152 : Interval s5Atlas 3 1152 43 := block_range (n:=43) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 1195 := (concat (concat (concat bs5_3_0 (concat bs5_3_96 bs5_3_192)) (concat bs5_3_288 (concat bs5_3_384 bs5_3_480))) (concat (concat bs5_3_576 (concat bs5_3_672 bs5_3_768)) (concat (concat bs5_3_864 bs5_3_960) (concat bs5_3_1056 bs5_3_1152))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_288 : Interval s5Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_384 : Interval s5Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_960 : Interval s5Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1056 : Interval s5Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1152 : Interval s5Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1248 : Interval s5Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1344 : Interval s5Atlas 4 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1440 : Interval s5Atlas 4 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1536 : Interval s5Atlas 4 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1632 : Interval s5Atlas 4 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1728 : Interval s5Atlas 4 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1824 : Interval s5Atlas 4 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1920 : Interval s5Atlas 4 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2016 : Interval s5Atlas 4 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2112 : Interval s5Atlas 4 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2208 : Interval s5Atlas 4 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2304 : Interval s5Atlas 4 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2400 : Interval s5Atlas 4 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2496 : Interval s5Atlas 4 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2592 : Interval s5Atlas 4 2592 55 := block_range (n:=55) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 2647 := (concat (concat (concat (concat bs5_4_0 (concat bs5_4_96 bs5_4_192)) (concat (concat bs5_4_288 bs5_4_384) (concat bs5_4_480 bs5_4_576))) (concat (concat bs5_4_672 (concat bs5_4_768 bs5_4_864)) (concat (concat bs5_4_960 bs5_4_1056) (concat bs5_4_1152 bs5_4_1248)))) (concat (concat (concat bs5_4_1344 (concat bs5_4_1440 bs5_4_1536)) (concat (concat bs5_4_1632 bs5_4_1728) (concat bs5_4_1824 bs5_4_1920))) (concat (concat bs5_4_2016 (concat bs5_4_2112 bs5_4_2208)) (concat (concat bs5_4_2304 bs5_4_2400) (concat bs5_4_2496 bs5_4_2592)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_96 : Interval s5Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_192 : Interval s5Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_288 : Interval s5Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_384 : Interval s5Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_480 : Interval s5Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_576 : Interval s5Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_864 : Interval s5Atlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_960 : Interval s5Atlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1056 : Interval s5Atlas 5 1056 84 := block_range (n:=84) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1140 := (concat (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat bs5_5_288 (concat bs5_5_384 bs5_5_480))) (concat (concat bs5_5_576 (concat bs5_5_672 bs5_5_768)) (concat bs5_5_864 (concat bs5_5_960 bs5_5_1056))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 48 := bs5_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_7_0 : Interval s5Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_7 : Interval s5Atlas 7 0 1 := bs5_7_0
theorem alls5 : ∀ k ≤ 7, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
  · exact alls5_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
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
theorem bgb_4_288 : Interval gbAtlas 4 288 74 := block_range (n:=74) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 362 := (concat (concat bgb_4_0 bgb_4_96) (concat bgb_4_192 bgb_4_288))
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
theorem bgb_5_2976 : Interval gbAtlas 5 2976 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3002 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 bgb_5_288)) (concat (concat bgb_5_384 bgb_5_480) (concat bgb_5_576 bgb_5_672))) (concat (concat (concat bgb_5_768 bgb_5_864) (concat bgb_5_960 bgb_5_1056)) (concat (concat bgb_5_1152 bgb_5_1248) (concat bgb_5_1344 bgb_5_1440)))) (concat (concat (concat (concat bgb_5_1536 bgb_5_1632) (concat bgb_5_1728 bgb_5_1824)) (concat (concat bgb_5_1920 bgb_5_2016) (concat bgb_5_2112 bgb_5_2208))) (concat (concat (concat bgb_5_2304 bgb_5_2400) (concat bgb_5_2496 bgb_5_2592)) (concat (concat bgb_5_2688 bgb_5_2784) (concat bgb_5_2880 bgb_5_2976)))))
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
theorem bgb_6_1920 : Interval gbAtlas 6 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2016 : Interval gbAtlas 6 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2400 : Interval gbAtlas 6 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3744 : Interval gbAtlas 6 3744 87 := block_range (n:=87) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3831 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 bgb_6_576) (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)))) (concat (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344))) (concat (concat bgb_6_1440 bgb_6_1536) (concat bgb_6_1632 (concat bgb_6_1728 bgb_6_1824))))) (concat (concat (concat (concat bgb_6_1920 bgb_6_2016) (concat bgb_6_2112 (concat bgb_6_2208 bgb_6_2304))) (concat (concat bgb_6_2400 bgb_6_2496) (concat bgb_6_2592 (concat bgb_6_2688 bgb_6_2784)))) (concat (concat (concat bgb_6_2880 bgb_6_2976) (concat bgb_6_3072 (concat bgb_6_3168 bgb_6_3264))) (concat (concat bgb_6_3360 bgb_6_3456) (concat bgb_6_3552 (concat bgb_6_3648 bgb_6_3744))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_288 : Interval gbAtlas 7 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_384 : Interval gbAtlas 7 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_480 : Interval gbAtlas 7 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_576 : Interval gbAtlas 7 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_672 : Interval gbAtlas 7 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_768 : Interval gbAtlas 7 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_864 : Interval gbAtlas 7 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_960 : Interval gbAtlas 7 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1056 : Interval gbAtlas 7 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1152 : Interval gbAtlas 7 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1248 : Interval gbAtlas 7 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1440 : Interval gbAtlas 7 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1536 : Interval gbAtlas 7 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1632 : Interval gbAtlas 7 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 95 := block_range (n:=95) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2015 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 bgb_7_576) (concat bgb_7_672 (concat bgb_7_768 bgb_7_864)))) (concat (concat (concat bgb_7_960 bgb_7_1056) (concat bgb_7_1152 (concat bgb_7_1248 bgb_7_1344))) (concat (concat bgb_7_1440 (concat bgb_7_1536 bgb_7_1632)) (concat bgb_7_1728 (concat bgb_7_1824 bgb_7_1920)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 60 := block_range (n:=60) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := bgb_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 1 := bgb_9_0
theorem allgb : ∀ k ≤ 9, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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
  · exact allgb_9 i (by omega) hi
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 28, 30),(inputs.getD 2 zero, 26, 30),(inputs.getD 3 zero, 22, 30),(inputs.getD 4 zero, 14, 30),(inputs.getD 5 zero, 14, 46)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 28, 29),(inputs.getD 2 zero, 25, 29),(inputs.getD 3 zero, 21, 29),(inputs.getD 4 zero, 13, 29),(inputs.getD 5 zero, 13, 45)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 26, 27),(inputs.getD 1 zero, 25, 27),(inputs.getD 3 zero, 19, 27),(inputs.getD 4 zero, 11, 27),(inputs.getD 5 zero, 11, 43)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 50, 51),(inputs.getD 1 zero, 49, 51),(inputs.getD 2 zero, 49, 53),(inputs.getD 4 zero, 35, 51),(inputs.getD 5 zero, 19, 51)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 14, 15),(inputs.getD 1 zero, 13, 15),(inputs.getD 2 zero, 11, 15),(inputs.getD 3 zero, 7, 15),(inputs.getD 5 zero, 11, 43)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 14, 15),(inputs.getD 1 zero, 13, 15),(inputs.getD 2 zero, 11, 15),(inputs.getD 3 zero, 7, 15),(inputs.getD 4 zero, 11, 27)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 14, 15),(inputs.getD 1 zero, 13, 15),(inputs.getD 2 zero, 11, 15),(inputs.getD 3 zero, 7, 15),(inputs.getD 4 zero, 11, 27),(inputs.getD 5 zero, 11, 43)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xe8e8e800e8008000e8e8e800e8008000e8e8e800e8008000e8e8e800e8008000e8e8e800e8008000e8e8e800e8008000e8e8e800e8008000e8e8e800e8008000
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3907577856 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12220.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,2]⟩,⟨.or,[4,5]⟩,⟨.or,[0,7]⟩,⟨.and,[0,7]⟩,⟨.and,[4,5]⟩,⟨.or,[6,9]⟩,⟨.or,[1,2]⟩,⟨.or,[3,10]⟩,⟨.and,[12,13]⟩,⟨.and,[8,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3907577856 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3907577856 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12220

open PEqualNP.Outside.L_meta_12220 in
theorem PEqualNP.Outside.L_meta_12220 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3907577856 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3907577856 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
