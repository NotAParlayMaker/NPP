import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12333.Model
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


end PEqualNP.Outside.L_meta_12333.Model

namespace PEqualNP.Outside.L_meta_12333
open PEqualNP.Outside.L_meta_12333.Model
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

end PEqualNP.Outside.L_meta_12333

namespace PEqualNP.Outside.L_meta_12333
open PEqualNP.Outside.L_meta_12333.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2720580004800b8000811000000f8034a490000980000000d8d320800b001800000951880e14e800024000000000000000000000a0f1c00001087888000000215054000007018026300180028001000200002061c0000000080ff43df43fe43fd43fc43dc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841fc31083fe42107f88420fe90841fc21082fca0107fd0020fda0041fe40083fa80107f10020fc20041ff30083fc60107f4c020fe18041ff20083de40107f88020fd10041fd20083da40107e48020f490041ff54c42fea9887f95310bf2a621fd54c42faa9887f15310be2a621ff53c42fea7887f94f10bf29e21fd53c42faa7887f14f10be29e21ff43c43be87887f90f10fea1e21fc43c43b887887fd4b10bfa9621fe52c42fca5887f54b10bea9621fc52c42f8a5887fd0b10ff21621fd42c43f885887fccb10ff19621fd32c43f865887fd0710ff20e21fd41c43f883887fcc710ff18e21fd31c43f863887fc8710ff10e21fd21c43f843887fd0310fda0621fe40c43fa81887f10310fc20621ff30c43fc61887f4c310fe18621ff20c43fc41887f48310fe10621ff54842fea9087f95210bf2a421fd54842faa9087f15210be2a421ff53842fea7087f94e10bf29c21fd53842faa7087f14e10be29c21ff43843be87087f90e10fea1c21fc43843b887087fd4a10bfa9421fe52842fca5087f54a10bea9421fc52842f8a5087fd0a10ff21421fd42843f885087fcca10ff19421fd32843f865085f54610ffa0c21f741843fc83087f50610fe20c21f441843fe63087f8c610fe98c21fc31843fe43087f88610fe90c21fc21842fca1087fd0210ff20421fd40843f881087fcc210ff18421fd30843f861087fc8210ff10421fd20843f841087fc4210fb88421fb10843fea8885fd5110ff2a2217e54443faa8885f55110fe2a2217c54443fea6885fd4d10ff29a217e53443faa6885f54d10fe29a217c53443fe868877d0d10ff21a21fd43443f886887710d10ffa92217f52443fca4885f94910fea92217d52443f8a4885f14910ffa1221fe42443fa84887f10910ff99221fe32443fa64887f0c910ffa0a21fe41443fa82887f10510ff98a21fe31443fa62887f0c510ff90a21fe21443fa42887f08510ffa0221fe40443fa80887f10110ff98221fe30443fa60887f0c110ff90221fe20443fa40887f08110ff88221fb10443fc20887d84110ffaa0217f54043fca8085f95010feaa0217d54043f8a8085f15010ffa98217f53043fca6085f94c10ef298215e53043faa6085f54c10eea98215d53043f8a6085f14c10ffa1821df43043fc86087f50c10fe21821dc43043fea4085fd4810ff290217e52043faa4085f54810fe290217c52043fe84087f90810fea1021fc42043fe64087f8c810fe99021fc32042fca2087fd0410fba0821fe41043fa82087f10410fa20821ff31043fc62087f4c410fe18821ff21043fc42087f48410fe108217e50043fe80087ed0010ff20021fd40043f880087e10010ff98021fe30043fa60087f0c010ff90021fe20043fa40087f08010ff88021f710043fc20087e84010fe88021f510043f220087c44010
  | 1 => 0xd314c3f862987fc8530ff10a61fd214c3f842987fd0130ff20261fd404c3f880987fcc130fd98261fe304c3bc60987fd5030bfaa061fe540c2fca8187f55030beaa061fc540c2f8a8185f94c30ffa1861df430c3fc86187f50c30fe21861dc430c3fea4187f94830bf29061fd520c2faa4187f14830ffa1061fe420c3fa84187f10830ff99061fe320c3fa64187f0c830ffa8861fe510c2fca2187f54430bea8861fc510c3fe82187f90430fea0861fc410c3fe62187f8c430fe98861fc310c3fe42187f88430fe90861fc210c2fca0187fd0030ff20061fd400c3f880187fcc030ef98061fe300c3f460187f4c030ee98061f9300c3fea9905fd5320ff2a6417e54c83faa9905f55320fe2a6417c54c83fea7905fd4f20ff29e417e53c83faa7905f54f20fe29e417c53c83fe879077d0f20ff21e41fd43c83f887907710f20ffa1641fe42c83fa85907f10b20ff99641fe32c83fa65907f0cb20ffa8e41fe51c82fca3907f54720bea8e41fc51c83fe83907f90720fea0e41fc41c83fe63907f8c720fe98e41fc31c83fe43907f88720fe90e41fc21c83fe81907ed0320ff20641fd40c83f881907e10320ff98641fe30c83fa61907f0c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ffa1c41df43883fc87107f50e20fe21c41dc43882faa5107fd0a20f7a1441fe42883fa85107f10a20f621441ff32883fc65107f4ca20fe19441ff51883fca3105f94620fea8c417d51883f8a3107fd0620ff20c41fd41883f883107fcc620ff18c41fd31883f863107fc8620ff10c41fd21883f843105f94220ffa0441fe40883fa81107f10220ff98441fe30883fa61107f0c220ff90441ef20883f641107fd5120bfaa241fe54482fca8907f55120beaa241fc54482f8a8907fd4d20bfa9a41fe53482fca6907f54d20bea9a41fc53482f8a6907fd0d20efa1a41fe43483fa86907f10d20ee21a41ff42483fc84907f50920fe21241ff32483fc64907f4c920fe19241ff51482fea2907f94520fea8a41fc51482f8a2907fd0520ff20a41fd41483f882907fcc520ff18a41fd31483f862907fc8520ff10a41fd21483f842907fd0120ff20241fd40483f880907fcc120ff18241fd30483f860907fc8120fd90241fe20483dc40907fd5020bfaa041fe54082fca8107f55020beaa041fc54082f8a8107fd4c20bfa9841fe53082fca6107794c20af29841fd53082faa6107754c20aea9841fc53082f8a6107fd0c20efa1841fe43083fa86107f10c20ee218417e52083fe84107bd0820ff21041fd42083f884107b10820ff99041fe32083fa64107f0c820ffa8841fe51082fca2107f54420bea8841fc51083fe82107f90420fea0841fc41083fe62107f8c420fe98
  | 2 => 0x3b887207fd4a40ff294817e52903faa5205f54a40fe29481ff42903fc85207f50a40fe21481ff32903fc65207f4ca40fe19481ff51903fca3205f94640fea8c817d51903f8a3207fd0640ff20c81fd41903f883207fcc640ff18c81fd31903f863207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681207fd4d40bfa9a81df53502bea6a07f94d40fea9a81fc53502f8a6a07714d40ae29a81ff43503be86a07f90d40fea1a81fc43503b886a07fd4940bfa9281ef52502dea4a07f94940fea9281fc52502f8a4a07b14940b629281ff42503fc84a07f50940fe21281ff32503fc64a07f4c940fe19281ff51502fea2a07dd4540bba8a81fe51503faa2a07f14540be28a81f451502e8a2a07fd0540ff20a81fd41503f882a07fcc540ff18a81fd31503f862a07fc8540ff10a81fd21503f842a07fd0140fda0281fe405037c80a05f95040ffa9881fe53102fca6207f54c40bea9881fc53103fe862077d0c40ff21881fd43103f886207710c40ffa9081fe52102fca4207f54840bea9081fc52103fe84207f90840fea1081fc42103fe64207f8c840fe99081fc32103fea2207f94440bf28881fd51102faa2207f14440ffa0881fe41103fa82207f10440ff98881fe31103fa62207f0c440ff90881fe21103fa42207f08440bf28081ff401037e80207f90040fd20081fd401037a80207e50040ffaa6617f54cc3fca9985f95330feaa6617d54cc3f8a9985f15330ffa1e61df43cc3fc87987f50f30fe21e61dc43cc3fea5987f94b30bf29661fd52cc2faa5987f14b30ffa1661fe42cc3fa85987f10b30ff99661df32cc3fc65987f4cb30ee99661fc32cc3fea3987f94730bf28e61fd51cc2faa3987f14730ffa0e61fe41cc3fa83987f10730ff98e61df31cc3fc63987f4c730ee98e61fc31cc3fe43987f88730fe90e61fc21cc3fe81987f90330fea0661fc40cc3fea9185fd5230ff2a4617e548c3faa9185f55230fe2a4617c548c2faa7187fd0e30efa1c61fe438c3fa87187f10e30ee21c61ff528c3fca5185f94a30fea94617d528c3f8a5187fd0a30ff21461fd428c3f885187fcca30ff19461fd328c3f865187fd4630ff28c617e518c3faa3185f54630fe28c61ff418c3fc83187f50630fe20c61ff318c3fc63187f4c630fe18c61ff218c3fc43187f48630fe10c617e508c3fe81187f90230fea0461fc408c3fe611877cc230fd98461ff544c2fea8987f95130bf2a261fd544c2faa8987f15130be2a261ff434c3be86987f90d30fea1a61fc434c3b886987fd4930bfa9261fe524c3faa4987f14930be29261ff424c3fc84987f50930fe21261ff324c3be64987f8c930fe99261dd324c3f864987fd4530bfa8a61fe514c3faa2987f14530be28a61ff414c3fc82987f50530fe20a61ff314c3be62987f8c530fe98a61d
  | 3 => 0x8618ff90c31fea1863fc430c7b88618ffd4831ff290637e520c7faa418df54831fe29063ff420c7fc8418ff50831fe21063ff320c7fc6418ff4c831fe190637e510c7fe8218ff90431fea0863fc410c7fe6218f7cc431ff18863f6310c7fa6218f74c431fa98863ff500c7fca018df94031fea80637d500c7f8a018ffd5321bfaa643fe54c86fca990ff55321beaa643fc54c86f8a990ffd4f21bfa9e43fe53c86fca790ff54f21bea9e43fc53c86f8a790ffd0f21efa1e43fe43c87fa8790ff10f21ee21e43ff42c87fc8590ff50b21fe21643ff32c87fc6590ff4cb21fe19643ff41c87ee8390ff90721fea0e43fc41c87e88390ffcc721ff18e43fd31c87f86390ffd4321ff286437e50c87faa190df54321fe28643ff54886fea910ff95221bf2a443fd54886faa910ff15221be2a443ff53886fea710ff94e21bf29c43fd53886faa710ff14e21be29c43ff43887be8710ff90e21fea1c43fc43887b88710df54a21ffa1443ef42887fc8510ff50a21fe21443ec42887fe6510ff8ca21fe99443fc32886fca310ffd0621ff20c43fd41887f88310ffcc621ff18c43fd31887f86310ffc8621f790c43f721887fea110ff94221bf28443fd50886faa110ff14221ffaa2437f54487fca890df95121feaa2437d54487f8a890df15121ffa9a437f53487fca690df94d21fea9a437d53487f8a690df14d21ffa1a43df43487fc8690ff50d21fe21a43dc43487fe8490ff90921fea1243fc42487fe6490ff8c921fe99243fc32487fe8290ff90521fea0a43fc41487fe6290ff8c521fe98a43fc31487fe4290fdc8521ff10a43ee21487fea090dfd4121ff28243fd50487f8a090df14121ffaa0437f54087fca810df95021feaa0437d54087f8a810df15021ffa98437f53087fca610df94c21ef298435e53087faa610df54c21eea98435d53087f8a610df14c21ffa1843df43087fc8610ff50c21fe21843dc43086fca410ffd0821f7a1043fe42087fa8410ff10821f621043ff32087fc6410ff4c821fe190437e51087fe8210fdd0421ff20843fd41087f88210fd10421ff98843fe31087fa6210ff0c421ff90843ef21087fc4210fd88421fe90843ed21087ea4210f948421ffa8043fe50086fca010ff54021bea8043fc50087fea7a07f94f40bf29e81fd53d02faa7a07f14f40ffa1e81df43d03fc87a07f50f40fe21e81dc43d03fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681fe42d03fa85a07f10b40ff99681fe32d03fa65a07f0cb40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a07f90740fea0e81fc41d03fe63a07f8c740fe98e81fc31d03fe43a07f88740fe90e81fc21d02faa9207fd4e40ff29c817e53903bca7205794e40fea9c817d53903baa7205754e40fe29c81ff43903be87207f90e40fea1c81fc439
  | 4 => 0x5f94032fea80657d500cbf8a0197fd4f41ff29e837e53d07faa7a0df54f41fe29e83ff43d07be87a0ff90f41fea1e83fc43d07b887a0ffd4b41ff296837e52d07faa5a0df54b41fe29683ff42d07fc85a0ff50b41fe21683ff32d07fc65a0ff4cb41fe19683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9c83fe53906fca720f794e41af29c83fd53906faa720f754e41aea9c83fc53907fe8720f7d0e41ff21c83fd43907f88720f710e41ffa9483fe52906fca520ff54a41bea9483fc52907fe8520ff90a41fea1483fc42907fe6520ff8ca41fe99483fc32906fca320ffd0641dfa0c83f741907fea120ff94241bf28483fd50906faa120ff14241ffa9a837f53507bea6a0d7d4d41ff29a83fd53507f8a6a0df14d41ee29a835c53507fe86a0f7d0d41ff21a83fd43507f886a0f710d41ffa92837f52507dea4a0dbd4941ff29283fd52507f8a4a0df14941f6292836c52507fe84a0ff90941fea1283fc42507fe64a0ff8c941fe99283fc32507fe82a0fdd0541ff20a83be41507fea0a0dfd4141fda82837b50507fca0a0ff54141fe282837c50507f0a0a0de14141bf2a083ff53107fca620df94c41fea98837d53107f8a620ffd0c41efa1883fe43107fa8620ff10c41ee21883ff52107fca420df94841fea90837d52107f8a420ffd0841ff21083fd42107f88420ffcc841ff19083fd32107f86420df94441ffa0883bf41107fc8220fd90441fea0883bd41107ea8220ffd4041ff280837e50107faa020df54041fe28083ff54cc6fea998ff95331bf2a663fd54cc6faa998ff15331be2a663ff43cc7be8798ff90f31fea1e63fc43cc7b88798ffd4b31ff296637e52cc7faa598df54b31fe29663ff42cc7fc8598ff50b31fe21663ff32cc7be6598ff8cb31fe99663dd32cc7f86598ffd0731ff20e63fd41cc7f88398ffd4331ff286637e50cc7faa198df54331fe28663ff548c6fea918ff95231bf2a463fd548c6faa918ff15231be2a4637d538c7fe8718f7d0e31ff21c63fd438c7f88718f710e31ffa9463fe528c6fca518ff54a31bea9463fc528c7fe8518ff90a31fea1463fc428c7fe6518ff8ca31fe99463fc328c6fca318ffd0631ff20c63fd418c7f88318ffcc631ef98c63f7318c7fea118ff94231bf28463fd508c6faa118ff14231ffaa2637f544c7fca898df95131feaa2637d544c7f8a898df15131ffa1a63df434c7fc8698ff50d31fe21a63dc434c7fea498dfd4931ff29263fd524c7f8a498df14931ffa1263fe424c7fa8498ff10931ff99263df324c7fc6498ff4c931ee99263fc324c7fe8298ff90531fea0a63fc414c7fe6298fdcc531ff18a63de314c7fea098dfd4131ff28263fd504c7f8a098df14131ffaa0637f540c7fca818df95031feaa0637d540c7f8a818df15031bf29863ff430c7be
  | 5 => 0xc43dfa1887fe4310fbc8621ff50c43dea1887dd4310ffea421ff94843bf29087fd5210efaa421ff14843ffa8887fe5110efca221ff54443bea8887fc5110ffea021ff94043bf28087fd5010efaa021ff14043ef2a0875e5410f3ca821f7d4843ef29087dd5210fb8a421f7d4443ef28887dd5110fb8a221f7d4043ef28087dd5010fb8a021ffd4f42ff29e857e53d0bfaa7a15f54f42fe29e85ff43d0bbe87a17f90f42fea1e85fc43d0bb887a17fd4742ff28e857e51d0bfaa3a15f54742fe28e85ff50d0bfca1a15f94342fea86857d50d0bf8a1a15f55242ffa9c85fe5390afca7217794e42af29c85fd5390afaa7217754e42aea9c85fc5390bfe872177d0e42ff21c85fd4390bf887217710e42bf29485ff4290b7e85217bd0a42ffa8c85fe5190afca3217f54642bea8c85fc5190bfea1217f94242bf28485fd5090afaa1217f14242ffa9a857f5350bbea6a157d4d42ff29a85fd5350bf8a6a15f14d42ee29a855c5350bfe86a177d0d42ff21a85fd4350bf886a17710d42ffa1285ef4250bfc84a16f90942ffa8a857f5150beea2a15dd4542ff28a85fd5150bf8a2a15f14542fa28a85745150bfea0a15fd4142fda82857b5050bfca0a17f54142fe282857c5050bf0a0a15e14142bf2a085ff5310bfca6215f94c42fea98857d5310bf8a6217fd0c42efa1885fe4310bfa86217f10c42ee218857e5210bfe84216fd0842ff21085ee4210bfa84216f50842f6a1085ff5110bfca2215f94442fea88857d5110bf8a2217fd4042ff280857e5010bfaa0215f54042fe28085ff54ccafea9997f95332bf2a665fd54ccafaa9997f15332be2a665ff43ccbbe87997f90f32fea1e65fc43ccbb887997fd0b32ff21665fd42ccbf885997fd4732ff28e657e51ccbfaa3995f54732fe28e65ff50ccbfca1995f94332fea86657d50ccbf8a1997fd5232bfaa465fe548cafca9197f55232beaa465fc548caf8a9195f54e32ffa1c65df438cbfc87197f50e32fe21c65dc438cafca5197fd0a32ff21465fd428cbf885197fcca32ef99465ef328cbfea3197f94632bf28c65fd518cafaa3197f14632ffa8465fe508cafca1197f54232bea8465fc508cbfea8995fd5132ff2a2657e544cbfaa8995f55132fe2a2657c544cbfe869977d0d32ff21a65fd434cbf886997710d32ffa1265fe424cbfa84997f10932ff99265ef324cbfc6499778c932ffa8a657f514cbfca2997f54532fe28a657c514cbfea0995fd4132ff28265fd504cbf8a0995f14132ffaa0657f540cbfca8195f95032feaa0657d540cbf8a8195f15032bf29865ff430cbbe86197f90c32fea1865fc430cbb886195f94832ffa1065fe420cbfa84197f10832ff99065df320cbfc64197b8c832fe99065dd320cbda64197fd4432ff288657e510cbfaa2195f54432fe28865ff500cbfca019
  | 6 => 0x1400000000e00200c01a00a00000802c00200600200200200400200200c00000000c00601e00c00000000000200000001e00000000200600001e00601400200000800200200c01000000400401800400a01a02000a00c00800000200000800000e00000407e00000001000a00800000000801400200001600602e00200000600000005000201a00601201c00000001c01000203a00800800400000c01601000000200001600200200000000a01000200200e00400400002a00400600801a00601600a00e00000801401400600000000002e02800a01600000000000000001400600400200601000006601003401804200402a00a00000000e01e00a00000002a00000001800000a00801c01800800a00000001000000000200000000000200800402000e00400000c00000000200400000403c00200a00003000200000202801600000000001000400a00600a00600001a01e00400201800000400400400000a00400a00600203000200000000200000c00800000200600400200200200200200200400200000200600e06a00000801a00400200e00000000000200000c00002200e00001000800000002c04202000600c01000000400000200000c01800802a00001a00000200200600400202e00400e00000201800000a00601c00400200600200000200000200400600000800203200c00601200000800000600400400803c00800a00200e00001a00800200000800000200400000a00000000400000000800200400800000400402e02401600600400600202600202000a00201200000200800000201201005400a00000000202800600200200601c01200000000e00000200200000201200003a00600000200a00200200200600001a02404200000603c00201200a00004800800000c01c00200a00201200001400800200000c00400200201401c01000001002c00203000000001000200400000200400800000200004601c00a00600200200a00006c03800000a00006200e01c00800e00004200c00600e00c008010002006050000016000000000004000001ff52d0ffca5a1df94b43fea96877d52d0ff8a5a1ffd4743ff28e877e51d0ffaa3a1df54743fe28e87ff50d0ffca1a1df94343fea86877d50d0ff8a1a1f7d4b43ef29687dd52d0fb8a5a1f7d4743ef28e87dd51d0fb8a3a1f7d4343ef28687dd50d0fb8a1a1df55243bf29c875e5390ffe8721efd0e43efa1c87ff5290ffca521df94a43fea94877d5290ff8a521ffd4643ff28c877e5190ffaa321df54643fe28c87ff5090ffca121df94243fea84877d5090ff8a121ffd0d43efa1a87fe4350f7c86a1ffd4943bfa9287fe5250ffaa4a1ff14943be29287ff5150efea2a1ff94543fea8a87fc5150ef8a2a1ffd4143bfa8287fe5050ffaa0a1ff14143be282877e5410efca621ffd0
  | 7 => 0x2d35cff0c090f42a8074ac92703400019b1cd8874001bb0000000a24955b401406d9bd540c00041d6d9855621bd9acc0019cc04970c0012c00007b82192bc000001914755c5000128538cf3cf452d18b015dbe1b48000000000000000d20000000000000000000388648000f0000000069d0e4000f6000000000000159c001c017f8000000a5c638000000c99478000dd00002002b00018191480013b8000e384a000181cbd4e4d578000b14de80000000012f19fcfb541c000fe541933c00053573424d705b88ddd9b4001b4d5000015540018f0000cd92cd469c3d11998da60d2cc34d308ac1b0f6821c864000368f38001205800290f9c8c80542649040019a95bd738a64001235d280000011d985c990cc5b516642685b92200016387b4bec0000000017b400144d6dcec58644158208050a455156190ca3c7d957ceb0ba47597544e80000006588915c01bc000d71b31671d147c000000192c1e8ff80017894f5d4818c420e18000db096d5e00003fc000348001c0dcac860138d145416f155d54ce64000330abc001325cb8e700003c41d9a710cc781490130d900000001b81ad58c001944000000000ed0110a8c000000000ed40014a4c60e8c1f10900000006a892800000000172c33cc95a958086780000018d4000000df90d14d8e78000dc53289a1b785f57104adafc3d1529bc4588474cbd6a86247fcb1c0051d1c1d0d83a01ed1b0000ea8d80a44c20000001b000014b8001030e1c001768d48d10000000170f05d019980000008504687ddb20df182d2118ad245bb45a01dd9f16b4741c8d9d07d03cc0000c00600580017203c1395a4445d0194e47314d124d2dc405b048c40000000000000011e14b07c991c0014a0001708dcc00177800000000106cda000076552c4ec118000a497fc000f2c0256102f0000001b080007a82dccb80007200006d56b10f00016a0000f885e9c40768000000001654fd8e5c6004013000016e0318ee8380000ca0000524c1c000ae4470ef4000000b792f566104cbb000000068c57153d3c000127899c2ac1a5991145961b808e9c2d7d87b0001274ba0c8507cc71079208144d853e0e2c48916810461000000032884891c9d4925010560ee08c1ca8c297d5681a7c344788f4d2aca080e1c15d906f002832c00a04200200000000200e00000001001600202200200200400001000000000203e00800000a00000600200000400601000801201a00200000200800000200401a01600401400000400000000400400401a00800c00200000401200c00000001200000000002000004601001000000600400c00801001002e00000e02e00600000000400600000800400200a01003a00800a00001800000402c01e00600e00000000000600e00800000e00805400200400000602200601400401a002000002
  | 8 => 0x11901549ace344a5d3145c8889cc149cc40d09d10ad76097ca7c7ec56c0009e9d94a553c583cfdd6fcedcb9c9140000000018c130d78c0002b87a46746a00f1bf0868964d003f5b380014389215f07080018440010f8001d7d16000055c000bf0d4dcd0cdd9a494872ce21b9850c120000de400195ce6800039965c7e8a00cad68921c2840000000007c4b886c4bbc001ca58bd330001ae88015b905559400108c5315c80000000000000000001f85e563125c361014158000000000000001928000be40017ec001931784b40e884c80010600001091edb905d085ceada986200000000b0001ad01517a548816c000001a000000005dc000000f2126d68db1d51c7840000000000ec44c001cedb64c75888000001c480009017e4000000000000d0573d47400000000143c001485ce034d8a5804e90080001cc11f99b9b0c00c000000c91000830000dd9b71b6947c27d5a91e9b2d458cc040d824000000df436555912400127cb99a0c00118c000000e314645789e40001b5901084d4035d4b487d4ed1f5748bf46c0884585ac471daa4001379995c603f9c94000378c49b1043c00120caf9238000dbc4c461800000085586095da30b3c4657015696e93ad7a8c546cdc74fa87bd38452179102c261c6c42c0017751b8bad744001919574fccaad0095655ac12cd992e1349c84ae04d13d8fd001c1940000001c01c4001588b49505831b3c0000000013b0c0dd88000f740000791a90b8bd80007704510496503c9bf53890b5225d243159c58e0c381800dc001c7c7a1d0d530a6da802f96580014ac00000048ce55bada38000c519dd895598088168710c2d6251d45c5cfc774ee46e1d8cd7d32cc800006641fd48db256d40fc64c2c55f83d59480011640009196adc880008fc000001050a90d0c74c514a04000001668d44000000b8c0003d884c3a80000000000411b58d8001724cc9c4d69063c6e8001d50b55a5db9c000839ab5770f485cc0014c14bd345249bdc73939d12839571d6048d0d9ca29a211dc2082d19545a92546718689b4660f143740b52519e844081d2ec294bfcf6d3510e8b6d6bc6b45556b976cfbc2bc00000000147041000056975c00188ca68c44f24ae84300000016019bc4b9b94b29265134ad14f02cd5f4f7c0008dc000001101640581cd57cc00054584ca74af5c688954fc304e1563c0008f00012d80000009c80000000014496ed22c6954611a5d656746bcb5da6ce48971cf06fd509131965aac0015c4000e7c4c00008d851820c8b4b2c011bc1120d6d7b806ca815e4d60dd49094cd154501a1400137cc24b35be4001d609c094c274178840984001b8c998fb12b05b16993dc4e04940000009f40b8ac57a038c001ae4b0c7f8000000a31c08000b04000000001d38000001be9839958815024000ab15342f40014
  | 9 => 0x52db29088c40000e9d66c00028000022c000bb80003ec0006dc2fc000001bb99edb5c0000017e802d80c0006ec460b51cb43b0001c340006051ac0003e45e000193c4f0e11ac8408e0cdc87e456400123c61cb640bd5703540000019711880e9bcc0003bd0b0e8057cb694048801cc0011a199c0000014e8db4000001180c04001c9c000000000960f1c0006f8001bf98a0001938a4000000102949db60fe12141e40006b09317e1a8caed2c4cfce416e45f0001af00980004fc5a40000009a400185197837d4344b46f4b7dda046d2f92a98fc7f07f45ed920000f347ad2897c0538b2483576577c0010d40017dc6d0000439298e758f866dc598b465c7184dc4f9d11ac00007990dc000f11cf54c81907783e1a08b75421a2cf284d56cc51d3a80a5034458b3905c75cf50b4ca858c9c05d71309454000ba8d34068e58001ba85f880c001260ab8000fc954800187dda4000000000cf9178000c886911f13f57f03f0d78ff428cadd3580a0e297f5cb0000000a88da40016c4000198a21d1c091ad80000d94a91716943e8000ce42300004900000000005d8258f8d891d74b08001875320000750174000001740000000249859d0400000103dc383a488d1c9cdc000c30bd0000000a9413d989185984cb17ad51519cca400136dd4d8113153bd4e096929517d2011fd61c5bc70da90ebc0012e87900002e85940452682117bcf9964800000000000000000000190974d628320ed892cf5c1355812a0d3c511834598c4c7458cc3ad904aa1364115c913559a17518dda1cf0c07c2357986c8a59ab102030d39883d7d038425d3f0000734001218f94d94e98000008000c58cb4f84fb94442204cda34c7817d1bc4e48cd69cce054c644000b44240a9c255a413fc000a2d0e115c270d68a793d5390c1478c635d99924acc6ac6811e4e4476c9102157815399c853c000c5cc3d794001c649b0cec0009c52c9228a1d5840009fda74684ffd6855cd62c0004b00c40858a917447c8b96d00000010fcc00870b20000014821634000000001d34000d8c001d9c00048194d3e516d8e40015fc000000a380002c8018be095000000000011c000000001aa8224000c8c244001150000000000d58390f71424dfcef0001d79b6cda8064000000030000844000000000eb8000000000000d38001a78e95518000000000fe86548d4000714000034efd12cfac000d090800000019d59f88100000000000003509bc828000000e08bc400125960d60909cea000000134d9f40002d829c00058c2d5a500010c4dc1c450a0614b91bfc00148146cded3c90599c0000000001281618000f78f5593501c2e40000006302895e87e018400000000128db7431cd5d109340f40100a711410c8bcce05a6426c76113c8e4de08e181533889c0ccf305d523000164ccd400031
  | 10 => 0x5c80d460d1c11154519108a93cd2d4dad4dce514317595a4001ba4a50160188bc17c9d5d8988f9318fec0f40205b40c898c33803cd75094819540001a540010400000000000019ac165879bedc21975a492b94098c459c4f41d150dca0125840001980f18b703b9240000001a88001d3c2511c46298700009380017c4bc9498000c640019400000000000000000000010bcd1c0000014d56442a40017307018b8308705ab98f4001a253680013a12b52a52906b94150392e597c09daa18ed5edc5d52000167c39c79400036d6c80000002b40006a50ec4bcfc0b851cc508505d68d28000cd0b30000941110b813edc983708a4000001ba0001c28668238ad515890c10c6889889f0f089e04a8a11da82edb7d5dc1d5410c69cc8f58b18725a188b1c78001441af540111c0009f8cf4651d6c484c11aecd24000cf15b1334a340a80000adc300000700008bdd20529d08ab50c0995381524000000bb4640001bc8d65360ec1881af80016140000018842e16a405d715c10000001b44001a9dad4001cf9428db88f5c19c802c0000000000000a18000000000038c18000f9032400000000000000023dc2400172886cbdca980e556c000be80000000001c80015a03008ececc5ad14c000d190a9d589a95b55116f8e846e5c540017b082400189c0000009340011980003359e53702059d89d9a05374000ea479c000b955d444400000000008c359d40f6449c42400129c0001a1cbc128574ec8000298001005b1473db84fa4fa1b54000000000000000094000ef8000000b58000000eec000000c9dd2dce4000000d50aa8aa49b8590a60eb5311a58e3c9ed0992fca0d969d8069882dabda29b19104a4d3a47d58d0c7c899b583dc0500000000009dd3f9304000000c6c93caf02a0000000418fc40014c400179d550000974bf862cca8558499bbd068ce9b34000afd6f4000b116782793b4fd53d0ad98280f9a85adce254f80016c100c3b4001139d85c7000014d10d8493e9a115d996c228a145488a0e6c00186c000000f80978858001a3d494981d548080005fc000000001591bd0879a6804c67cccc19d544000d540001f4000b60434000001075951ccc00000000000000047931c7cc000000001ce9044958000e00ac0001a4d5d09458e877dd181a8729d44000455719194000000000000748e604d8608448b00000000001ae04285c1065070000d899e00000001e0000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x2400427f6550010b7d8d40042dc6350010d794d400435d5350010bbd8940042ec6250010bdd8540042f461500109fd94400427e65100109f594400427c6510010cf950400433d5410010d794c400435d5310010bd98440042f56110010be594400437965100109e59440042fa6410010ee990400437b5410010ee95040043795410010ee55040043da5310010f654c40043db4310010f610c400437a5210010de14840043f26110010be58440043f16110010bc584400437a5110010fcd0440043f041100109f597300435e53cc010d754f300427f658c0109f596300435e538c010d754e30042f6618c010bd586300427f654c010d794d300435d534c0109fd94300427e650c0109f594300427c650c010d794c300435d530c010bd98430042f5610c010f64c0300427d65c8010d794f200435d53c80109fd96200427d6588010d794e200435d5388010db94a200436d5288010bd98620042f561880109fd95200435e5348010d754d200427f65080109f994200427d65080109f19420042de6308010b758c200435e5308010d754c200436e5208010db54820042f66108010bd58420043e92008010d794f100435d53c4010dd59710042f664c4010bd19310043d653c4010f554f10043d743c4010f510f10043f340c4010fc103100435e5384010d754e10042f56184010dd94610042f96584010de59610042796584010be99210042f86484010f694e10043d95384010f6d0e10043d84384010be58610042f16184010de94610043f25184010fcd0610043f041840109fd95100435e5344010d754d10042f76544010ddd9510042776544010bd99110042f46444010f594d10043d55344010f5d0d10043d44344010bdd8110043765044010fcd0110043f24044010fc50110043f04044010fccc110043f23044010fc4c110043f03044010fcc8110043f22044010fc48110043f02044010bed95100437b65440109ed9510042fa6444010be19110043da5344010f654d10043db4344010f610d10042fb6144010fcd85100437a5144010fc94510043f34144010fc90510043f14144010fc10510043f33144010fc8c510043f13144010fc0c510043f32144010fc88510043f12144010fc08510043f36544010bcd9510043736544010fcd9110043f26444010bc99110043f16444010fc19110042f06444010fcd5110043f25444010fc55110043f05444010fcd8d10043f26344010fc58d10043f06344010fcd4d10043f25344010f494d10043f15344010f454d10043f05344010fcd0d10043d34344010fc90d10043f14344010fc10d10043d04344010fcd8910043f26244010fc58910043f06244010fcd4910043f25244010fc54910043f05244010fcd0910043f24244010fc50910043f04244010fccc910043f23244010fc4c910043f03244010
  | 1 => 0x436e5290810db54a42042f66190810bd58642042fa6090810be582420427f65508109f995420427d65508109f195420433e5450810cf55142042df6350810b718d420435e5350810d754d420436e5250810db54942042f76150810bd18542042fb6050810be181420427f65108109f994420427d65108109f194420435e5310810d754c420436f5210810db148420427f65cc8109f997320427d65cc8109f197320435e53cc810d754f320427f658c8109f996320427d658c8109f196320435e538c810d754e320427f654c8109f995320427d654c8109f195320435e534c810d754d32042f7614c810bd18532042fb604c810be181320427f650c8109f994320427d650c8109f194320435e530c810d754c32042f6610c810bd58432042fa600c810be580320427e64944109f592510427e63944109f58e510435f4394410d710e510427e62944109f58a510427d65d0410d794f410435d53d0410bd597410437565d0410ddd53410437554d0410f594f41043d553d0410f5d0f41043d443d0410dd94b410437452d0410fcd8341042f560d0410fc183410427f65904109f596410433e5490410cf55241042de6390410b758e410435e5390410d754e41042f66190410be98241042f960904109fd9541042df6350410b718d410435e5350410d754d41042ef6250410bb18941042fb60504109fd94410427d6510410cf950410433d5410410d794c410435d5310410be98041042f96010410dd59441042756510410bd99041043b66410410ddd5041043b65410410dd55041043b55410410f594c41043d55310410f5d0c41043d44310410dd94841043745210410fc98041042f56010410fc58041042f160104109f597310435e53cc410d754f310427f658c4109f596310435e538c410d754e31042fa608c410be582310427f654c410d794d310435d534c4109fd94310427d650c410d794c310435d530c410f54c431042fa600c410be580310427d65c8410d794f210435d53c84109fd96210427d6588410d794e210435d5388410db94a210436d5288410be98221042f960884109fd95210435e5348410d754d210427f65084109f59421042de6308410b758c210435e5308410d754c210436e5208410db54821043e52108410be98021042f960084109f992500427d64940109f98e500427d6394010d7d0e500435c43940109f98a500427d62940109f58650043774194010dd106500427d65d0010d794f400435d53d0010be597400437965d0010ded53400437954d0010f694f40043d953d0010f6d0f40043d843d0010de94b400437852d0010fcd8740042f961d0010fc187400437a51d0010fcd0740043f041d00109fd96400427d6590010cf952400433d5490010b798e40042dd6390010d794e400435d5390010bd98640042f56190010be98
  | 2 => 0x6594c10d7d4e530427e6494c109f592530427e6294c109f58a530425d6594c10b7992530435f5494c10d7952530435d5494c10d7152530435f6494c10d7992530425e6494c10d7592530435c6494c10d7d8a530435e6294c10d758a530435c6294c10d7986530435c6194c10d7982530435c6094c109fd91530427c6454c10d7d8d530427f6254c109f189530427f6154c109f585530427f6054c109f581530435f6554c10b7191530435f5454c10d7951530435d5454c10d7151530435f6454c10d7991530435d6454c10d7191530425c6454c10d7d89530435e6254c10d7589530435c6254c10d7985530435c6154c10d7981530435c6054c10d704153042de6314c10d754c530427e6414c109f590530427e6314c10d798c530425e6314c109f988530427d6214c109f98453043766114c109f980530437a6014c109fd97430427e65d0c109f597430427c65d0c10d7d4f430435e53d0c10d754f430435c53d0c10b7d97430435f65d0c1097d97430435e65d0c10b7597430435d65d0c1097597430435c65d0c10d7d53430435e54d0c10d7553430435c54d0c109fd96430427e6590c109f596430427c6590c10b798e430435e5390c10d754e43042f66190c10bd58643042fa6090c10be582430427f6550c109f995430427d6550c109f195430435e5350c10d754d43042f76150c10bd18543042fb6050c10be181430427f6510c109f994430427d6510c109f194430435f5310c10d794c430435d5310c10d714c43042df6510c10d7d94430425f6510c10d799443042dd6510c10d7594430425d6510c10d719443042de6410c10e7990430435f5410c10d7950430435d5410c10d715043042de63d4810b758f520435e53d4810d754f520427e64d48109f593520427e63d4810d798f520425e63d48109f58f520435d63d48109758f520435f43d4810d710f520427e61d4810dd987520427e60d4810de983520427d6594810d794e520435d5394810dbd4a520427e64948109f592520427e63948109f58e520435f4394810d710e520435e5354810d754d520427f64548109f191520427f63548109f18d520435f4354810d710d520436f62548109fd85520427d61548109fd81520427d6054810af99052042bd6414810b798c52042dd6314810d794c520435d5314810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520435f4314810d710c520427e6214810db988520427e6114810dd984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420435e53d0810d754f420436f52d0810db14b420427f65908109f996420427d65908109f19642042de6390810b758e420435e5390810d754e420
  | 3 => 0x910be98042442f960109109fd97324427e65cc9109f597324427c65cc910d794f324435d53cc910dbd4b324436c52cc910bd98732442f561cc910be98332442f960cc9109fd96324427e658c9109f596324427c658c910d7d4e324435c538c9109fd95324427e654c9109f595324427c654c910d794d324435d534c9109fd94324427e650c9109f594324427c650c910d7d4c324435c530c910dbd48324436c520c9109f997414433f54d0510cf15341442fa60d0510be583414427e6590510b798e41442dd63905109f195414433f5450510cf15141442df6350510b718d41442ef6250510bb18941442fb6050510be181414427e65105109f997314435f53cc510d714f31442fa60cc510be583314427e658c5109f195314435f534c510d714d31442fb604c510be181314427e650c5109f997214436f52c8510db14b21442fa60c8510be583214427e65885109f195214436f5248510db14921442fb6048510be181214427e6508510b798c21442dd6308510f9484214427e65d0110cfd53404433c54d0110bd98740442f561d01109f99640442de6390110b758e404427f65501109f595404427c6550110cfd51404433c5450110b7d8d40442dc6350110bbd8940442ec6250110bdd8540442f461501109f994404427e65cc110d7d4f304435c53cc110bd98730442f561cc1109f996304427f654c1109f595304427c654c110d7d4d304435c534c110bdd8530442f4614c1109f994304427e65c8110dbd4b204436c52c8110bd98720442f561c81109f996204427f65481109f595204427c6548110dbd49204436c5248110bdd8520442f461481109f99420442de6308110b758c20443e92008110de953104437854c4110f6d0f10443d843c4110dd95210443745484110f5d0e10443d44384110fcd4210442de63d5010b758f540427e63d5010d798f540425e63d50109f58f540435d63d50109758f540427e62d50109f58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540435f63950109f98e540427d6395010d718e540427e62950109f58a54042df6355010b718d54042ef6255010bb189540433f64550109fd8d540435f635501097d8d540427c6355010d718d540425c63550109fd89540436f62550109bd89540427c6255010db189540426c62550109fd85540427d6155010dd185540427f60550109f58154043786055010cf55054042de6315010b758c54042ee6215010bb588540427e6415010cf990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427e6015010de980540427e64d4c109f593530427e62d4c109f58b530427e61d4c10dd987530427e60d4c10de983530427d
  | 4 => 0xfd85544437761551109dd85544427f6055110ded81544427b60551109f994544433d5415110cf990544427e63151109f58c544427e62151109f588544427e61151109f184544427e60151109f180544427e64d4d109f593534427e62d4d109f58b534435f5394d109f992534427d6494d109f98e534427e6294d109f58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af19153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109f994534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427e6114d109f184534427e6014d109f180534427f65d0d109f997434427d65d0d109f197434435f53d0d10d794f434435d53d0d10d714f434435f65d0d10d7997434435d65d0d10d7197434435f54d0d10d7953434435d54d0d10d7153434427f6590d109f996434427d6590d109f196434433f5490d10cf15243442de6390d109fd95434427e6550d109f595434427c6550d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10d7d4c434435e5310d10d754c434435c5310d10bd98443442f56110d10be98043442f96010d10d7d94434435e6510d10d7594434435c6510d10b7990434439e6410d10d7d50434439f5410d10c7d50434435e5410d10d7550434435c5410d10e7150434431c5410d10f598443443d56110d10f698043443d96010d109f993524427d64d49109f98f524427d63d4910d7d0f524435c43d4910dbd4a524427e64949109f592524427e63949109f58e524435f4394910d710e524427e62949109f586524437561949109f58252443796094910afd9152442bc6454910b7d8d52442dc63549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910d7d0d524435c4354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910b798c52442dd6314910db548524427e64149109f590524427e6314910d798c524425e63149109f58c524435d63149109758c524435f4314910d710c524436e62149109f984524427c61149109f980524427c60149109fd97424427e65d09109f597424427c65d0910dbd4b424436c52d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910b798e42442dd63909109fd95424427e65509109f595424427c6550910b7d8d42442dc6350910bdd8542442f46150910bed8142442f860509109fd94424427e65109109f594424427c6510910cfd50424433c5410910dbd48424436c5210910bd98442442f56110
  | 5 => 0x528425e6314a109f58c528435d6314a109758c528435f4314a10d710c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10db94b428436d52d0a109fd96428427e6590a109f596428427c6590a10b798e42842dd6390a10bd98642842f56190a109fd95428427e6550a109f595428427c6550a10b7d8d42842dc6350a10bdd8542842f46150a10bed8142842f86050a109fd94428427e6510a109f594428427c6510a10db948428436d5210a10be98042842f96010a109fd97328427e65cca109f597328427c65cca10d794f328435d53cca10be98332842f960cca109fd96328427e658ca109f596328427c658ca10db94a328436d528ca109fd95328427e654ca109f595328427c654ca10d794d328435d534ca10db949328436d524ca10bdd8532842f4614ca109fd94328427e650ca109f594328427c650ca10bd98432842f5610ca10cf953418433d54d0610be98341842f960d0610dd597418437754d0610ed953418437554d0610ed55341843d743d0610f510f418437652d0610dd14b41843f260d0610bd58341843f160d0610b798e41842dd6390610cf951418433d5450610b7d8d41842dc6350610bbd8941842ec6250610bed8141842f86050610bd59441843756510610ed99041843775410610dd55041843d74310610f510c41843765210610dd14841842f56010610d794f318435d53cc610be98331842f960cc610d794d318435d534c610bed8131842f8604c610f54c4318436e52c8610db54b21842fa60c8610be583218436e5248610db54921842fb6048610be18121842de6308610b758c21843e52108610cf952408433d5490210b798e40842dd6390210bd98640842f56190210b7d8d40842dc6350210bbd8940842ec6250210bdd8540842f46150210cf950408433d5410210bd98440842f56110210d7d4f308435c53cc210d794e308435d538c210bd98630842f5618c210d7d4d308435c534c210d794c308435d530c210bd98430842f5610c210db94a208436d5288210bd98620842f56188210b798c20842dd6308210db948208436d5208210bd98420842f56108210fa48020842f565c4210dd59710842f664c4210bd19310843d743c4210f510f10842f965c4210de597108437a54c4210de15310843db43c4210f610f10842de63d5110b758f544427e63d5110d798f544425e63d51109f58f544435d63d51109758f544427e62d51109f58b544433f54951109f992544427e63951109f58e544427e62951109f58a544427d6195110dd586544427d6095110de58254442df6355110b718d54442ef6255110bb189544433f64551109fd8d544435f635511097d8d544427c6355110d718d544425c63551109fd89544436f62551109bd89544427c6255110db189544426c62551109
  | 6 => 0x2f96088710b798c21c42dd6308710db94821c436d5208710f948421c42fa6008710be58021c433e54d0310cf55340c42f661d0310bd58740c42f965d0310de59740c437b54d0310ee95340c437954d0310ee55340c43db43d0310f610f40c437a52d0310de14b40c43f261d0310be58740c43f161d0310b798e40c42dd6390310cf95140c433d5450310b7d8d40c42dc6350310bbd8940c42ec6250310bdd8540c42f46150310be59440c43796510310ee99040c437b5410310de55040c43db4310310f610c40c437a5210310de14840c42f96110310d794f30c435d53cc310bd98730c42f561cc310d794d30c435d534c310bdd8530c42f4614c310f64c030c436e52c8310db54b20c42f661c8310bd58720c436e5248310db54920c42f76148310bd18520c42de6308310b758c20c43e92008310b798f54842dd63d5210bb98b54842ed62d52109f98f548435e63d52109798f548427d63d5210d758f548425d63d52109f98b548436e62d52109b98b548427d62d5210db58b548426d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a54842df6355210b718d548433f64552109fd8d548435f635521097d8d548427c6355210d718d548425c63552109fd89548427c6255210ddd85548433d5415210cf990548427e63152109f58c548427e62152109f58854843756115210de980548427e64d4e109f593538427e62d4e109f58b538437561d4e10de983538435f5394e109f992538427d6494e109f98a538427d6294e109fd91538427c6454e10d7d8d538427f6254e109f189538435d5314e10bb98853842ed6214e109f990538427d6414e10d798c538427e6214e10db988538426e6214e109f588538436d6214e109b58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438435f53d0e10d794f438435d53d0e10d714f438435f65d0e10d7997438435d65d0e10d7197438435f54d0e10d7953438435d54d0e10d7153438427f6590e109f996438427d6590e109f19643842f66190e10bd586438427f6550e109f995438427d6550e109f19543842f76150e10bd185438427f6510e109f994438427d6510e109f194438435f5310e10d794c438435d5310e10d714c43842fa6010e10be580438435f6510e10d7994438435d6510e10d7194438439e6410e10d7d50438435e5410e10d7550438435c5410e10f698043843d96010e109f993528427d64d4a109f98f528427d63d4a10d7d0f528435c43d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528435f4394a10d710e528427f6454a109f191528427f6354a109f18d528435f4354a10d710d528436f6254a10b798c52842dd6314a10db548528427e6414a109f590528427e6314a10d798c
  | 7 => 0x4153109f98c54c427d63153109f98854c427d6215310dd98454c437960153109f99353c427d64d4f109f98b53c427d62d4f10dd98753c437960d4f10d7d4e53c427e6494f109f59253c427e6294f109f58a53c427f6454f109f19153c435f6354f109fd8953c427c6254f10d754c53c42ee6214f10bb58853c427e6414f109f59053c435e6314f109f98853c436e6214f109b98853c427d6214f10db58853c426d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10d7d4f43c435e53d0f10d754f43c435c53d0f10d7d9743c435e65d0f10d759743c435c65d0f10d7d5343c435e54d0f10d755343c435c54d0f109fd9643c427e6590f109f59643c427c6590f10be98243c42f96090f109fd9543c427e6550f109f59543c427c6550f10bed8143c42f86050f109fd9443c427e6510f109f59443c427c6510f10d7d4c43c435e5310f10d754c43c435c5310f10bd98443c42f56110f10d7d9443c435e6510f10d759443c435c6510f10e799043c435f5410f10d795043c435d5410f10d715043c43d66110f10f558443c427e64d4b109f59352c427e63d4b109f58f52c435f43d4b10d710f52c437661d4b10de58352c436f5294b109f99252c427d6494b109f98e52c427d6394b10d7d0e52c435c4394b109fd9152c427c6454b109fd8d52c427c6354b10d7d0d52c435c4354b10dbd8952c42de6314b10b758c52c436d5214b109f99052c427d6414b109f98c52c435e6314b109798c52c427d6314b10d758c52c425d6314b10d7d0c52c435c4314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c436e52d0b10db54b42c427f6590b109f99642c427d6590b109f19642c42de6390b10b758e42c42fa6090b10be58242c427f6550b109f99542c427d6550b109f19542c42df6350b10b718d42c42f76150b10bd18542c42fb6050b10be18142c427f6510b109f99442c427d6510b109f19442c436e5210b10db54842c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c435e53ccb10d754f32c42f661ccb10bd58732c427f658cb109f99632c427d658cb109f19632c436e528cb10db54a32c427f654cb109f99532c427d654cb109f19532c435e534cb10d754d32c436e524cb10db54932c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c42fa600cb10be58032c433e5490710cf55241c42de6390710b758e41c42fa6090710be58241c42df6350710b718d41c42ef6250710bb18941c42f86050710cf95041c433d5410710be98041c42f96010710d7d4f31c435c53cc710d794e31c435d538c710be98231c42f9608c710d7d4d31c435c534c710d794c31c435d530c710be98031c42f9600c710db94a21c436d5288710be98221c4
  | 8 => 0x209fd9540082df6350020b718d400835e5350020d754d40082ef6250020bb18940082f76150020bd185400827f65100209f994400827d65100209f194400833e5410020cf550400835e5310020d754c40082ee6210020bb58840082f96510020de59440082796510020be99040083ba6410020ded5040083ba5410020de55040083b95410020f694c40083d95310020f6d0c40083d84310020fa98840082f96210020fa58840082e96210020de94840083eb4210020fa108400837a51100209f597300835e53cc020d754f300827f658c0209f596300835e538c020d754e30082ee628c020bb58a300827f654c020d794d300835d534c0209fd94300827e650c0209f594300827c650c020d794c300835d530c020bb98830082ed620c020f64c0300835e53c8020d754f20082ee64c8020bb19320083ce53c8020f354f20083cf43c8020f310f20083eb40c8020fa103200835e5388020d754e20082ed6288020db94a20082fa6488020be19220083da5388020f654e20083db4388020f610e20082f96288020ba58a200837a5288020fa94a20083eb4288020fa10a200827f6548020d794d200835d5348020bbd95200836f65480209bd9520082ee6448020bb19120083ce5348020f354d20083cf4348020f310d20082ef6048020db94120083eb4048020fa90120083e94048020fa10120083eb3048020fa8c120083e93048020fa0c120082fb6548020ded95200827b6548020be99120082f86448020f694d20083d95348020f6d0d20083d84348020bed8920083eb6248020de94920083ea5248020fad0920083ea4248020fa50920083e84248020facc920083ea3248020fa4c920083e83248020fac8520083ea2148020fa48520083e82148020fad9520082eb6548020dad9520083eb6448020fa99120082ea6448020fa59120083e86448020ba19120083eb5448020fa95120083e95448020fa15120083eb6348020fa98d20083e96348020fa18d20083eb5348020fa94d20083ca5348020fa54d20083c95348020fa14d20083eb4348020f2d0d20083ea4348020fa50d20083e84348020f210d20083eb6148020fa98520083e96148020fa18520083eb5148020fa94520083e95148020fa14520083eb4148020fa90520083e94148020fa10520083eb3148020fa8c520083e93148020fa0c520082de63d5310b758f54c42ee62d5310bb58b54c427e63d5310d798f54c425e63d53109f58f54c435d63d53109758f54c427e62d5310db98b54c426e62d53109f58b54c436d62d53109b58b54c437661d5310de58354c433f54953109f98e54c427d63953109f98a54c427d6295310b7d8d54c42dc6355310cfd9154c427f6355310d7d8d54c425f63553109f18d54c435c63553109718d54c427f62553109f18954c437b6055310cf55054c433e6
  | 9 => 0x952420833d5490820b798e42082dd6390820d794e420835d5390820bb98a42082fa6090820be582420827f6550820b7d8d42082dc6350820d794d420835d5350820bdd8542082f46150820bed81420827f65108209f594420833e5410820cf550420835e5310820d754c42082fa6010820be580420836d65108209b59442082ee6410820eb990420836f5410820eb950420836d5410820eb55042083ce5310820f354c42083cf4310820f310c42083ea6010820bb58042083e96010820ba580420827d65cc820d794f320835d53cc8209fd96320827d658c820d794e320835d538c820be98232082f9608c8209fd95320835e534c820d754d320827f650c8209f594320835e530c820d754c32083cd320c820be98032082f9600c820b798f51082dd63d4420d794f510835d53d4420d794e510835d5394420ddd46510827e64944209f592510827e63944209f58e510835f4394420d710e510836f4294420db10a510835e5354420d754d510827f64544209f191510827f63544209f18d510835f4354420d710d51082be6414420af59051082de6314420b758c510835e5314420d754c510837551144209fd97410827e65d04209f597410833e54d0420cf553410835e53d0420d754f410827f65904209f996410827d6590420b798e41082dd6390420d794e410835d5390420bb98a41082ed6290420dd94641083755190420be98241082f960904209fd95410827d65504209f195410833e5450420cf55141082df6350420b718d410835e5350420d754d41082ef6250420bb18941083765150420dd54541082fb6050420be181410827f65104209f994410827d6510420d794c410835d53104209fd97310827e65cc4209f597310835e53cc420d754f310827f658c4209f996310827d658c420d794e310835d538c4209fd95310827d654c4209f195310835e534c420d754d31082ef624c420bb18931082fb604c420be181310827f650c4209f994310827d650c420d794c310835d530c420bb98831082ed620c420be98031082f9600c420d794f210835d53c8420dd947210837551c8420be98321082f960c84209f596210835e5388420d754e210827f6548420d794d210835d5348420b798c21082dd6308420d794c210835d5308420dd94421083755108420f948421082fa6008420be580210827e64940209f592500827e63940209f58e500835f4394020d710e500836f4294020db10a500827d65d0020d794f400835d53d0020be597400837965d0020ded53400837954d0020f694f40083d953d0020f6d0f40083d843d0020fad8b40082f962d0020fa18b400837a52d0020fad0b40083e842d0020de947400827f65900209f596400833e5490020cf55240082de6390020b758e400835e5390020d754e40082ee6290020bb58a40082fa60900
  | 10 => 0x40836e62d50209f987540827d61d50209f983540837a60d50209f596540833f5495020d7d8e540827e63950209f58e540835c63950209f986540827d6195020b7d8d54082dc6355020bdd8554082f46155020cfd91540827f6355020d7d8d540825f63550209f18d540835c63550209718d540827f62550209f589540836c62550209fd85540837761550209dd85540827c6155020dd18554082746155020de181540833d5415020b798c54082dd6315020bd98454082f561150209f990540833e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f988540836e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a60150209f993530827d64d4c209f98b530836e62d4c209f987530827d61d4c209f983530837a60d4c209f596530835f5394c209f992530827d6494c209f986530827d6194c209759653082de6494c20d7d52530835e5494c20d7552530835c5494c20d7d92530835e6494c2097992530835d6494c20d7192530835e6294c20d718a530835f6194c20d7986530835d6194c20d7186530835e6094c20d7182530827f6454c209f191530835f6354c209fd89530827d6254c209fd85530827c6154c20d7d9553082dc6454c20d7d51530835e5454c20d7551530835c5454c20d7d91530835e6454c20d7591530835c6454c2097191530835e6254c20d7189530835f6154c20d7985530835d6154c20d7185530835e6054c20d7181530835c2054c20b798c530835d5314c209f990530827d6414c209f98c530835e6314c209798c530827e6214c20db988530827e6114c209f584530827e6014c20de980530827f65d0c209f997430827d65d0c209f197430835f53d0c20d794f430835d53d0c20d714f43082df65d0c20d7d97430825f65d0c20d799743082dd65d0c20d7597430825d65d0c20d7197430835f54d0c20d7953430835d54d0c20d7153430827f6590c209f996430827d6590c209f19643082de6390c20d794e430835d5390c20bb98a43082ed6290c20be98243082f96090c209fd95430827e6550c209f595430827c6550c20d794d430835d5350c20bbd8943082ec6250c20bed8143082f86050c209fd94430827e6510c209f594430827c6510c20d7d4c430835e5310c20d754c430835c5310c20b7d94430835f6510c2097d94430835e6510c20b7594430835d6510c2097594430835c6510c20b7990430839e6410c20d7d50430835e5410c20d7550430835c5410c209f992520827d64948209f98e520827d6394820d7d0e520835c43948209f597420835e53d0820d754f42082ed65d0820db597420836f54d0820db55342083ce53d0820f354f42083cf43d0820f310f42083eb60d0820bb58342083e860d08209fd96420827d6590820cf
  | 11 => 0xde6390d209fd95434827e6550d209f595434827c6550d209fd94434827e6510d209f594434827c6510d20cfd50434833c5410d20d7d4c434835e5310d20d754c434835c5310d20bb98843482ed6210d20be98043482f96010d20d7d94434835e6510d20d7594434835c6510d20b7990434839e6410d20d7d50434839f5410d20c7d50434835e5410d20d7550434835c5410d20e7150434831c5410d20f398843483cd6210d20f698043483d96010d209f997424833f54d0920cf15342482fa60d0920be583424827e6590920b798e42482dd63909209f195424833f5450920cf15142482df6350920b718d42482f76150920bd18542482fb6050920be181424827e65109209f997324835f53cc920d714f32482fa60cc920be583324827e658c9209f195324835f534c920d714d32482fb604c920be181324827e650c9209f993514827d64d45209f98f514827d63d4520d7d0f514835c43d4520ddd4651482bf6454520af19151482df6354520b718d51482de6314520b758c514837551145209f990514827d64145209f98c514835e63145209798c514827d6314520d758c514825d6314520d7d0c514835c43145209f997414827d65d05209f197414837751d0520dd147414827e65905209f596414827c6590520cfd52414833c5490520b798e41482dd63905209fd95414827e65505209f19541482df6350520b718d41482ef6250520bb18941482fb6050520be181414827e65105209f594414827c6510520cfd50414833c5410520bb98841482ed6210520ddd4441483745110520be98041482f960105209f997314827d65cc5209f197314835e53cc520d754f31482ee62cc520bb58b314837751cc520dd14731482fa60cc520be583314827e658c5209f596314827c658c520d7d4e314835c538c5209fd95314827e654c5209f195314835e534c520d754d314827e650c5209f594314827c650c520d7d4c314835c530c520ddd443148374510c5209f99721483775188520dd14621482fa6088520be58221483775148520dd14521482fb6048520be181214827e6508520b798c21482dd6308520f9484214827e65d0120cfd53404833c54d0120bb98b40482ed62d01209f99640482de6390120b758e404827f65501209f595404827c6550120cfd51404833c5450120b7d8d40482dc6350120bbd8940482ec6250120bdd8540482f461501209f994404827e65cc120d7d4f304835c53cc120bb98b30482ed62cc1209f996304827f654c1209f595304827c654c120d7d4d304835c534c120bbd8930482ec624c1209f994304837a54c8120de15320483db43c8120f610f204836e5488120db15220483cf4388120f310e20483eb5088120b798f54082dd63d50209f98f540835e63d50209798f540827d63d5020d758f540825d63d50209f98b5
  | 12 => 0x90620b798e41882dd6390620bb98a41882ed62906209fd95418827d65506209f19541882df6350620b718d41882ef6250620bb18941882fb6050620be181418827f65106209f994418827d6510620dd94441883755110620be98041882f960106209fd97318827e65cc6209f597318835e53cc620d754f31882fa60cc620be583318827f658c6209f996318827d658c620dd9463188375518c6209fd95318827d654c6209f195318835e534c620d754d31882ef624c620bb1893188376514c620dd545318827f650c6209f994318827d650c620bb98831882ed620c620dd94621883755188620be98221882f96088620dd94521883755148620bed8121882f86048620b798c21882dd6308620f9484218833e5490220cf55240882de6390220b758e40882ee6290220bb58a40882df6350220b718d40882ef6250220bb18940882f76150220bd185408833e5410220cf55040882ee6210220bb588408835f53cc220d714f308835e538c220d754e30882ee628c220bb58a308835f534c220d714d308835e530c220d754c30882ee620c220bb58830882ed65c8220db59720882ee64c8220bb19320883cf43c8220f310f20882f965c8220de597208837a54c8220de15320883db43c8220f610f20882de63d5120b758f544827e63d5120d798f544825e63d51209f58f544835d63d51209758f544827e61d51209f587544833f54951209f992544827e63951209f58e544827d6295120db58a544827e61951209f586544827d6095120de58254482df6355120b718d54482f76155120bd185544833f64551209fd8d544835f635512097d8d544827c6355120d718d544825c63551209fd89544836f62551209bd89544827f6155120ddd85544827761551209f185544837461551209d185544827f6055120ded81544827b60551209f994544833d5415120cf990544827e63151209f58c544827e62151209f188544827e61151209f584544827e64d4d209f593534827e61d4d209f587534835f5394d209f992534827d6494d209f98e534827d6294d20db58a534827e6194d209f586534827d6094d20de58253482bf6454d20af19153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534835f6354d209fd89534836f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209f994534835d5314d209f990534827d6414d20d798c534827e6214d209f188534827e6114d209f584534827f65d0d209f997434827d65d0d209f197434835f53d0d20d794f434835d53d0d20d714f434835f65d0d20d7997434835d65d0d20d7197434835f54d0d20d7953434835d54d0d20d7153434827f6590d209f996434827d6590d209f196434833f5490d20cf15243482
  | 13 => 0xb758e40c833e5450320cf55140c82df6350320b718d40c82ef6250320bb18940c82f76150320bd18540c82f96510320de59440c83ba6410320ded5040c83795410320f6d0c40c83d84310320be58840c837a5110320d794f30c835d53cc320bb98b30c82ed62cc320d794d30c835d534c320bbd8930c82ec624c320f64c030c82de63d5220b758f54882f661d5220bd587548827e63d5220d798f548825e63d52209f58f548835d63d52209758f548836d62d52209f987548837661d52209d987548827d61d5220dd587548827561d5220de983548833f54952209f98e548827d63952209f986548827d6195220b7d8d54882dc6355220cfd91548827f6355220d7d8d548825f63552209f18d548835c63552209718d548836f62552209fd85548827c6155220cf550548833e64152209f98c548827d6315220db588548827e61152209f584548837a60152209f993538827d64d4e20db58b538827e61d4e209f587538837a60d4e20d7d4e538827e6494e209f592538827e6194e209f586538827f6454e209f191538835f6354e209fd85538827c6154e20d754c53882f66114e20bd584538827e6414e209f590538835e6314e20db588538827e6114e20dd98453882766114e209f58453883756114e209d584538837a6014e209fd97438827e65d0e209f597438827c65d0e20d7d4f438835e53d0e20d754f438835c53d0e20d7d97438835e65d0e20d7597438835c65d0e20d7d53438835e54d0e20d7553438835c54d0e209fd96438827e6590e209f596438827c6590e20bb98a43882ed6290e209fd95438827e6550e209f595438827c6550e20bbd8943882ec6250e209fd94438827e6510e209f594438827c6510e20d7d4c438835e5310e20d754c438835c5310e20be98043882f96010e20d7d94438835e6510e20d7594438835c6510e20e7990438835f5410e20d7950438835d5410e20d715043883da6010e20f6580438833e54d0a20cf55342882fa60d0a20be583428836d65d0a20dbd5342883ae54d0a20db55342883ad54d0a20f3d0f42883cc43d0a20fa98342882ed60d0a20fa58342882de6390a20b758e428833e5450a20cf55142882df6350a20b718d42882f76150a20bd18542882fb6050a20be18142882ed6510a20db59442883ae6410a20dbd50428836d5410a20f3d0c42883cc4310a20bb580428835e53cca20d754f32882fa60cca20be583328835e534ca20d754d32882fb604ca20be18132883cd320ca20ddd46518827e64946209f592518827e63946209f58e518835f4394620d710e518836f4294620db10a518827f64546209f191518827f63546209f18d518835f4354620d710d51882de6314620b758c518837551146209fd97418827e65d06209f597418837651d0620dd547418827f65906209f996418827d65
  | 14 => 0x8d54c827f61553209f18554c837b6055320cf55054c833e64153209f98c54c827d6315320db98854c827e61153209f58454c837960153209f99353c827d64d4f20db98b53c827e61d4f209f58753c837960d4f20d7d4e53c827e6494f209f59253c827e6194f209f58653c827f6454f209f19153c835f6354f209fd8553c827c6154f20d754c53c82f66114f20bd58453c827e6414f209f59053c835e6314f20db98853c827e6114f20dd98453c82766114f209f58453c83756114f209d58453c83796014f209fd9743c827e65d0f209f59743c827c65d0f20d7d4f43c835e53d0f20d754f43c835c53d0f20d7d9743c835e65d0f20d759743c835c65d0f20d7d5343c835e54d0f20d755343c835c54d0f209fd9643c827e6590f209f59643c827c6590f20be98243c82f96090f209fd9543c827e6550f209f59543c827c6550f20bed8143c82f86050f209fd9443c827e6510f209f59443c827c6510f20d7d4c43c835e5310f20d754c43c835c5310f20bb98843c82ed6210f20d7d9443c835e6510f20d759443c835c6510f20e799043c835f5410f20d795043c835d5410f20d715043c83ce6210f20f358843c833e5490b20cf55242c82de6390b20b758e42c82fa6090b20be58242c82df6350b20b718d42c82f76150b20bd18542c82f86050b20cf95042c833d5410b20be98042c82f96010b20d7d4f32c835c53ccb20d794e32c835d538cb20be98232c82f9608cb20d7d4d32c835c534cb20d794c32c835d530cb20be98032c82f9600cb20ddd4651c827e64947209f59251c827e63947209f58e51c835f4394720d710e51c827f64547209f19151c827f63547209f18d51c835f4354720d710d51c82de6314720b758c51c837551147209fd9741c827e65d07209f59741c837651d0720dd54741c827f65907209f99641c827d6590720b798e41c82dd6390720be98241c82f960907209fd9541c827d65507209f19541c82df6350720b718d41c82ef6250720bb18941c82fb6050720be18141c827f65107209f99441c827d6510720bb98841c82ed6210720dd94441c837551107209fd9731c827e65cc7209f59731c835e53cc720d754f31c82ee62cc720bb58b31c827f658c7209f99631c827d658c720dd94631c8375518c7209fd9531c827d654c7209f19531c835e534c720d754d31c8376514c720dd54531c82fb604c720be18131c827f650c7209f99431c827d650c720be98031c82f9600c720dd94721c837551c8720be98321c82f960c8720b798c21c82dd6308720dd94421c83755108720f948421c82fa6008720be58021c833e54d0320cf55340c82ee62d0320bb58b40c82f965d0320de59740c837b54d0320ee95340c837954d0320ee55340c83db43d0320f610f40c83ea62d0320be58b40c83e962d0320de94740c82de639032
  | 15 => 0xc27f65d08309f997420c27d65d08309fd96420c27e65908309f596420c2de6390830b758e420c36e5290830db54a420c27f65508309f595420c27c6550830b7d8d420c2dc6350830db949420c36d5250830bdd85420c2f46150830bed81420c2f860508309fd94420c27e65108309f594420c35e53cc830db94b320c36d52cc830be983320c2f960cc8309f596320c27f654c830d794d320c36e520c830db548320c3cd320c830be980320c2f9600c830bb98b510c2ed62d4430ddd46510c27e64944309f592510c35f4394430d710e510c27e62944309f58a510c27f64544309f191510c35f4354430d710d510c27f62544309f189510c37551144309fd97410c27e65d04309f597410c27f65904309f996410c27d6590430b798e410c2dd6390430dd946410c37551904309fd95410c27d65504309f195410c2df6350430b718d410c2ef6250430bb189410c3765150430dd545410c2fb6050430be181410c27f65104309f994410c27d6510430d794f310c37651cc430dd547310c2fa60cc430be583310c27d658c4309fd95310c35e534c430dd944310c375510c430f54c4310c2fa600c430be580310c27f65c84309f997210c27d65c8430dd947210c37551c84309fd96210c27e65884309f596210c36e5288430db54a210c27f65484309f595210c27c6548430b7d8d210c2dc6348430bed81210c2f860484309fd94210c27e65084309f594210c2de6308430b758c210c36e5208430db548210c3765108430dd544210c3e521084309f992500c27d6494030d7d0e500c35c43940309f597400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c27f6550030b7d8d400c2dc6350030bbd89400c2ec6250030bdd85400c2f461500309fd94400c27e65100309f594400c27c6510030cf950400c33d5410030b798c400c2dd6310030ee500400c2de64cc030b7193300c35e54cc030d7153300c35d52cc030d7547300c2dd638c030d794e300c2f9638c030de94e300c3da538c030f6d0e300c3d8438c0309fd95300c2df654c030d7d95300c25f654c030b7991300c2dc644c030d7951300c35c544c030d7549300c35d514c030b7d81300c35e504c030f6901300c3d9404c030bed95300c37b654c0309ed95300c2fb634c030f6d8d300c37a534c030f694d300c3da434c030f650d300c3da324c030f60c9300c3da314c030f60c5300c2de63d5320b758f54c82f661d5320bd58754c827e63d5320d798f54c825e63d53209f58f54c835d63d53209758f54c836e62d53209f98754c837661d53209d98754c827d61d5320dd58754c827561d5320de58354c833f54953209f98e54c827d63953209f98654c827d6195320b7d8d54c82dc6355320cfd9154c827f6355320d7d8d54c825f63553209f18d54c835c6355320971
  | 16 => 0xc5410530b798c414c2dd6310530ddd44414c3745110530be980414c2f960105309f997314c2de65cc530d7997314c2de64cc530b7193314c35e54cc530d7153314c2dd62cc530d7d4b314c35c51cc530b7983314c2dd638c530ddd46314c374518c530be982314c2f9608c530ddd45314c374514c530bed81314c2f8604c530b7991314c2dc644c530d7951314c35c544c530b7d89314c35f524c530f5d85314c3d7514c530d7145314c3d4514c530d5145314c3db604c530b7181314c3d8604c530b6181314c27e650c530b798c314c27e65c85309f597214c27c65c8530b798f214c2dd63c8530ddd47214c37451c8530be983214c2f960c85309f996214c27d65885309f196214c2de6388530b758e214c36f5288530db14a214c2fa6088530be582214c27f65485309f995214c27c6548530b798d214c2dd63485309f994214c27d65085309f194214c2de6308530b758c214c36f5208530db148214c3775108530dd144214c3e521085309f997404c33f54d0130cf153404c2de63d0130b758f404c27e6590130b798e404c2dd63901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c2ef6250130bb189404c2f76150130bd185404c27e6510130f6d0f304c3d843cc130f6ccb304c3d932cc130f6cc7304c3d931cc130b7992304c2dc648c130d7952304c35c548c130b758a304c2dd618c130f6d42304c27e63d5030d798f540c25e63d50309f98b540c27d62d50309f987540c27d61d50309f983540c37a60d50309f596540c33f5495030d718e540c27e62950309f58a540c27e61950309f586540c33f64550309fd8d540c25f63550309f58d540c35c63550309fd89540c27c62550309fd85540c27c6155030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6415030cf990540c27e6315030d798c540c27e6215030db988540c26e62150309f588540c36d62150309b588540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c309f592530c27d65d0c30d794f430c2dd65d0c30d7597430c35f54d0c30d7953430c35d54d0c30d7153430c2dd60d0c309fd96430c27d6590c30cf952430c33d5490c30b798e430c2fa6090c30be582430c27f6550c309fd94430c27d6510c30cf950430c33d5410c30d794c430c2fa6010c30be580430c35f6510c30d7594430c25d6510c30b7990430c39e6410c30d7d50430c35e5410c30e7950430c31e5410c30d7550430c39d5410c30d7150430c3da6010c30b7580430c3d96010c30b6580430c2f661d4830bd587520c36f52948309f992520c27d6494830d7d0e520c35c43948309f986520c27d61948309fd91520c27c6454830d7d0d520c35c43548309fd85520c27c6154830db54852
  | 17 => 0x51309f987544c27d61d5130cfd52544c27e64951309f58e544c35d63951309f98a544c27d62951309f986544c27d61951309f582544c3796095130bbd89544c2ec6255130bdd85544c2f46155130cfd91544c27f6355130d7d8d544c25f63551309fd89544c36f62551309bd89544c27c6255130db189544c26c62551309fd85544c37761551309dd85544c27c6155130dd185544c27461551309fd81544c37b60551309f994544c33d5415130cf990544c35f63151309f98c544c27c63151309718c544c27e62151309f588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d30d7997434c25e65d0d30d7197434c35f54d0d30e7d53434c35e54d0d30d7553434c35c54d0d30e7153434c31c54d0d30b758b434c2dd61d0d30b7983434c3da60d0d30b6983434c3d960d0d309f996434c2de6390d309f195434c33f5450d30cf151434c2fb6050d30be181434c27e6510d30b7994434c35e6510d30b7990434c39e6410d30d7d50434c35e5410d30d7550434c35c5410d30b7588434c2dd6110d30b7980434c27e64d49309f593524c35f43d4930d710f524c27e61d49309f587524c36f5294930afd91524c2bc6454930bdd85524c2f46154930db548524c27e64149309f590524c35f4314930d710c524c27e61149309f584524c27e65d09309f597424c27c65d0930dbd4b424c36c52d09309f996424c27d65909309f196424c33f5490930cf152424c2de6390930b758e424c27f65509309f995424c27c6550930b7d8d424c2dc6350930bdd85424c2f46150930bed81424c2f860509309f994424c27d65109309f194424c33f5410930cf150424c2de6310930b758c424c36f5210930db148424c2fa6010930be580424c27e65cc930b7997324c35e65cc930b7993324c2dc64cc930d7953324c35c54cc930d714b324c2dd61cc930b7983324c2dd638c930dbd4a324c36c528c930be982324c2f9608c930dbd49324c36c524c930bed81324c2f8604c930b7991324c2dc644c930d7951324c35c544c930f3d89324c3cf524c930d7149324c3cc524c930d3149324c2df614c930f6d81324c2dc604c930f6181324c2d8604c9309f994324c2de630c9309f993514c27d64d4530d7d0f514c35c43d45309f98b514c27d62d4530d7ccb514c35d32d4530ddd46514c2bf6454530af191514c2ef6254530bb189514c37551145309f990514c27d6414530d7d0c514c35c43145309f988514c27d62145309f997414c27d65d05309f197414c37751d0530dd147414c27e65905309f596414c27c6590530cfd52414c33c5490530b798e414c2dd63905309fd95414c27e65505309f195414c2df6350530b718d414c2ef6250530bb189414c2fb6050530be181414c27e65105309f594414c27c6510530cfd50414c33
  | 18 => 0xdb54921cc3765148730dd54521cc2fb6048730be18121cc27f65087309f99421cc27d6508730b798c21cc2dd6308730f948421cc33e54d0330cf55340cc2de63d0330b758f40cc2de6390330b758e40cc33e5450330cf55140cc2df6350330b718d40cc2ef6250330bb18940cc2f76150330bd18540cc3b94010330d758f548c27e62d52309f58b548c27e61d52309f587548c37a60d5230cfd52548c35f63952309f98a548c27d62952309f986548c27d6195230cfd91548c35f63552309fd89548c27c62552309fd85548c27c6155230cf550548c33e6415230d758c548c27e62152309f588548c27e61152309f584548c37a6015230cf953438c33d54d0e30be983438c2f960d0e30d7597438c35f54d0e30d7953438c39e54d0e30c7953438c35d54d0e30e7553438c3da60d0e30b7583438c3d960d0e30cf951438c33d5450e30bed81438c2f86050e30b7594438c35d6510e30e7990438c35f5410e30d7950438c35d5410e30d7150438c2dd6010e30dbd4a528c27e6494a309f592528c35f4394a30d710e528c27e6194a309f586528c27f6454a309f191528c35f4354a30d710d528c27f6154a309f185528c36d5214a309fd97428c27e65d0a309f597428c27f6590a309f996428c27d6590a30b798e428c2dd6390a309fd95428c27d6550a309f195428c2df6350a30b718d428c2f76150a30bd185428c2fb6050a30be181428c27f6510a309f994428c27d6510a30be980428c2f96010a30db94a328c36d528ca30be982328c2f9608ca30db949328c36d524ca30bed81328c2f8604ca30f34c8328c37751946309f992518c27d6494630d7d0e518c35c43946309f98a518c27d62946309fd91518c27c6454630d7d0d518c35c43546309fd89518c27c6254630dd544518c27f65d06309f997418c27d65d06309fd96418c27e65906309f596418c2de6390630b758e418c27f65506309f595418c27c6550630b7d8d418c2dc6350630bbd89418c2ec6250630bed81418c2f860506309fd94418c27e65106309f594418c2fa6010630be580418c376518c630dd546318c2fa608c630be582318c376514c630dd545318c2fb604c630be181318c3d5310c6309fd97218c27e65c86309f597218c2fa60c8630be583218c27f65886309f996218c27d6588630be982218c2f960886309fd95218c27d65486309f195218c2df6348630b718d218c27f65086309f994218c27d6508630b798c218c2dd6308630f9484218c33e5490230cf552408c2de6390230b758e408c2df6350230b718d408c2ef6250230bb189408c2f76150230bd185408c33e5410230cf550408c2de6310230b758c408c2dd65cc230d7597308c2de64cc230b7193308c35e54cc230d7153308c35d52cc230d7547308c2f965cc230de597308c35d63d51309f98b544c27d62d
  | 19 => 0x254cc35c63953309f98a54cc27d62953309f98654cc27d6195330cfd9154cc35c63553309fd8954cc27c62553309fd8554cc27c6155330cf55054cc33e6415330d798c54cc27e62153309f58854cc27e61153309f58454cc3796015330b759743cc35d65d0f30d7d5343cc35e54d0f30d755343cc35c54d0f30b758b43cc2dd61d0f30b798343cc33e5490f30cf55243cc2fa6090f30be58243cc33e5410f30cf55043cc2fa6010f30be58043cc35d6510f30e799043cc35f5410f30d795043cc39e5410f30c795043cc35d5410f30e755043cc2dd6210f30b758443cc2de6010f30f698043cc3d96010f30dbd4a52cc27e6494b309f59252cc35f4394b30d710e52cc27e6194b309f58652cc27f6454b309f19152cc35f4354b30d710d52cc27f6154b309f18552cc36d5214b30bd98452cc2f56114b309fd9742cc27e65d0b309f59742cc36e52d0b30db54b42cc27f6590b309f99642cc27d6590b30b798e42cc2dd6390b309fd9542cc27d6550b309f19542cc2df6350b30b718d42cc2f76150b30bd18542cc2fb6050b30be18142cc27f6510b309f99442cc27d6510b30b798c42cc2dd6310b30db94842cc36d5210b30db94b32cc36d52ccb30be98332cc2f960ccb30b799332cc2dc64ccb30d795332cc35c54ccb30d794b32cc3ce52ccb30f354b32cc2dd61ccb30b798332cc3da60ccb30f658332cc2df654cb30d7d9532cc2de644cb30b719132cc35e544cb30d715132cc3cf624cb30d794932cc2df614cb30b718132cc36e520cb30db54832cc2fa600cb30be58032cc37751947309f99251cc27d6494730d7d0e51cc35c43947309f98a51cc27d62947309fd9151cc27c6454730d7d0d51cc35c43547309fd8951cc27c6254730d7cc951cc35d3254730bb98851cc2ed6214730dd54451cc27f65d07309f99741cc27d65d0730dd94741cc37551d07309fd9641cc27e65907309f59641cc2de6390730b758e41cc27f65507309f59541cc27c6550730b7d8d41cc2dc6350730bbd8941cc2ec6250730bed8141cc2f860507309fd9441cc27e65107309f59441cc2de6310730b758c41cc3765110730dd54441cc37651cc730dd54731cc2fa60cc730be58331cc2de64cc730b719331cc35e54cc730d715331cc2dd62cc730d754b31cc35e51cc730f594731cc3d551cc730b798331cc3da60cc730f658331cc2df654c730d7d9531cc2de644c730b719131cc35e544c730d715131cc2df624c730d754931cc3d7614c730d794531cc2dc604c730dd94431cc375510c730be98031cc2f9600c7309fd9721cc27e65c87309f59721cc2de63c8730b758f21cc36e52c8730db54b21cc27f65887309f99621cc27d6588730b798e21cc2dd6388730dd94621cc37551887309fd9521cc27d65487309f19521cc2de6348730b758d21cc36e5248730
  | 20 => 0x27d6590840b798e42102dd6390840e710e421027f6550840b7d8d42102dc6350840bdd8542102f46150840bed81421039c4310840db948421036d5210840be98042102f960108409fd97321027e65cc8409f597321035e53cc840d754f32102fa60cc840be583321027f658c8409f996321027d658c840db94a321036d528c8409fd95321027d654c8409f19532102bf644c840af191321035e534c840d754d321036e524c840db54932102fb604c840be181321027f650c8409f994321027d650c840ddd46511027e63944409f58e511035f4394440d710e511027e62944409f58a511027f63544409f18d511035f4354440d710d511027f62544409f18951103786054440b798c51102dd6314440bb98851102ed6214440dd544511037651d0440dd54741102fa60d0440be583411027d6590440b798e41102dd6390440e710e411027f6550440b7d8d41102dc6350440bbd8941102ec6250440bed81411039c4310440dd94441103755110440be98041102f960104409fd97311027e65cc4409f597311035e53cc440d754f31102fa60cc440be583311027f658c4409f996311027d658c440dd9463110375518c4409fd95311027d654c4409f19531102bf644c440af191311035e534c440d754d3110376514c440dd54531102fb604c440be181311027f650c4409f994311027d650c4409fd97211027e65c84409f597211036e52c8440db54b21102fa60c8440be583211027f65884409f996211027d6588440dd94621103755188440be98221102f960884409fd95211027d65484409f19521102bf6448440af191211036e5248440db54921103765148440dd54521102fb6048440be181211027f65084409f994211027d6508440b798c21102dd6308440f9484211035e6394040d758e501035f4394040d710e501039f43d0040e710f40102bd6490040cf95240102de6390040b758e40102f96490040de95240103ba5490040f698e40103d96390040f6d0e40103d84390040be98a40102fa61900409fd9540102df6350040b718d401039f4350040e710d40102ef6250040bb18940102f76150040bd18540102bf6550040cfd95401023f6550040e7d8d401039c6350040ebd8940103ac6250040edd8540103b46150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103db6350040f618d40103db4350040ee90d40103b84350040f610d40103984350040fad8940102f86250040fa18940102e86250040fcd8540102f86150040fc18540102f06150040bb98b54cc2ed62d5330bd98754cc2f561d5330d798f54cc27e62d5330db98b54cc26e62d53309f58b54cc36d62d53309b58b54cc27e61d5330dd98754cc27661d53309f58754cc37561d53309d58754cc37960d5330cfd5
  | 21 => 0x4214540ddcc851503763214540dd4c851503743214540ddd8051503756014540dd500515027e65d0540d7d4f415035c53d0540dbd4b415036c52d0540dd14741502de6390540b758e415035f5390540d714e415036f5290540db14a41503775190540dd14641502fa6090540be58241502df6350540b718d415035f5350540d714d41502ef6250540bb189415036f5250540db14941503775150540dd14541502fb6050540be181415027e6510540d7d4c415035c5310540dbd48415036c5210540ddd44415027e65cc5409f597315027c65cc540d7d4f315035c53cc540dbd4b315036c52cc540ddd47315037451cc5409f996315027d658c5409f196315035f538c540d714e315036f528c540db14a3150377518c540dd146315027f654c5409f995315027c654c540d7d4d315035c534c540dbd49315036c524c540ddd453150374514c5409f994315027d650c5409f194315035f530c540d714c315036f520c540db1483150377510c540dd14431502fa600c540be580315027e65c85409f597215027c65c8540d7d4f215035c53c8540dbd4b215036c52c8540ddd47215037451c85409f996215027d65885409f196215035f5388540d714e215036f5288540db14a21503775188540dd146215027f65485409f995215027c6548540d7d4d215035c5348540dbd49215036c5248540ddd45215037451485409f994215027d65085409f19421502be6408540af59021502de6308540b758c215035f5308540d714c215036f5208540db14821503775108540dd14421503e52108540be98021502f96008540d7d4f405035c53d0140dbd4b405036c52d0140ddd47405037451d0140f6d4f40503d853d0140f6d0f40503d843d0140fad4b405037852d0140fa14b405036852d0140fcd47405037851d0140fc147405037051d0140b798e40502dd6390140d7d4e405035c5390140e7d0e405039c4390140dbd4a405036c5290140ddd4640503745190140e798e405039d6390140e7d4e405039c5390140ebd4a40503ac5290140edd4640503b45190140eed42405035f5394c409f98a531027d6294c409f986531027d6194c409fd89531027c6254c409fd85531027c6154c40d754c53102ee6214c40bb58853102f66114c40bd584531035e53d0c40d754f43102fa60d0c40be583431035e54d0c40f698343103d960d0c409f59643102de6390c409fd95431035e5310c40d754c43102fa6010c40be58043102de6410c40e7990431035e5410c40f698043103d96010c40dbd4a521027e63948409f58e521035f4394840d710e521027e61948409f586521027f63548409f18d521035f4354840d710d521027f61548409f18552103786054840b798c52102dd6314840db54852102f66114840bd584521036e52d0840db54b42102fa60d0840be583421
  | 22 => 0x940bd185525035f5314940d714c525036d52149409f98c525027d6314940d7d0c525035c43149409f984525027d6114940bb994525036e6514940dbd4c52503cf5314940d3d4c525036e5314940db54c525036c5314940f314c525034c5314940f3d0c52503cc4314940dbd90525036f6314940db98c525036d6314940db18c525036f4314940d3d0c525036e4314940db50c525036c4314940d310c525036f6114940db984525036d6114940db184525036f6014940db580525036d40149409f997425035f53d0940d714f425036c52d0940b798e42502dd6390940d7d4e425035c5390940dbd4a425036c5290940be98242502f96090940b7d8d42502dc6350940d7d4d425035c5350940dbd49425036c5250940bdd8542502f46150940bed8142502f860509409f994425035f5310940d714c425036f52109409f997325027d65cc9409f197325035f53cc940d714f325036f52cc940db14b325027e658c9409f596325027c658c940d7d4e325035c538c940dbd4a325036c528c9409fd95325027e654c9409f195325035f534c940d714d325036f524c940db149325027e650c9409f594325027c650c940d7d4c325035c530c940dbd48325036c520c940be98032502f9600c940d7d4f515035c53d4540dbd4b515036c52d45409f98f515027d63d4540d7d0f515035c43d45409f98b515027d62d4540ddd4f51503d753d4540d5d4f515037653d4540dd54f515037453d4540f514f515035453d4540f5d0f51503d443d4540ddd4b51503e752d4540d9d4b515037652d4540dd54b515037452d4540f914b515036452d4540ddd93515037763d4540dd98f515037563d4540dd18f515037743d4540d5d0f515037643d4540dd50f515037443d4540d510f515037762d4540dd98b515037562d4540dd18b515037742d4540dd90b515037542d4540dd10b515037732d4540dd8cb515037532d4540dd0cb515037760d4540dd58351502de6394540b758e515035f5394540d714e51502ee6294540bb58a515036f5294540db14a51503775194540b7d8d51502dc6354540d7d4d515035c5354540bbd8951502ec6254540dbd49515036c5254540d7d4c515035c5314540dbd48515036c5214540dd544515027e63145409f58c515035f4314540d710c515027e62145409f58851502f66514540dd99451503775314540f5d4c51503575314540dd94c51503755314540dd14c51503d45314540d514c51503d74314540f510c51503775214540f9d4851503675214540dd94851503755214540dd14851503e45214540d914851503776414540ddd8c51503766314540dd58c51503746314540ddd0c51503574314540dd90c51503754314540dd10c51503544314540ddd8851503766214540dd58851503746214540ddd0851503764214540dd5085150374
  | 23 => 0xf18951902de6314640b758c519035e5314640d754c51903755114640d794f419035d53d0640b798e41902dd6390640d794e419035d5390640e710e41903765190640dd54641902fa6090640be58241902df6350640b718d419035e5350640d754d41902ef6250640bb18941903765150640dd54541902fb6050640be181419035e5310640d754c419039c43106409fd97319027e65cc6409f597319035e53cc640d754f319027f658c6409f996319027d658c640d794e319035d538c6409fd95319027d654c6409f19531902bf644c640af191319035e534c640d754d319027f650c6409f994319027d650c640d794c319035d530c640be98031902f9600c6409fd97219027e65c86409f597219035e53c8640d754f219037651c8640dd547219027f65886409f996219027d6588640d794e219035d5388640db94a219036d52886409fd95219027d65486409f19521902bf6448640af191219035e5348640d754d219027f65086409f994219027d6508640b798c21902dd6308640d794c219035d5308640db948219036d5208640dd94421903755108640f948421902fa6008640be580219035e53d0240d754f409039f43d0240e710f40902bd65d0240cf597409039e53d0240e754f40902f965d0240de59740903da53d0240f654f40903db43d0240f610f409037a52d0240de947409027e62d4d409f58b535027e61d4d409f587535035f64d4d40d7d8b535035e62d4d40d758b535035c62d4d40d7d87535035e61d4d40d7587535035c61d4d40d7d83535035d60d4d40d7d4e53502ee6294d40bb58a53502f66194d40bd58653502ef6254d40bb18953502f76154d40bd185535035d5314d409f988535027d6214d409f984535027d6114d40b7994535035e6514d40d7d90535035f6214d40d7988535035d6214d40d7188535035f6114d40d7984535035d6114d40d7184535035f6014d40d7580535035d4014d409f997435035c53d0d40b7997435035e65d0d409799743502de6390d40d7d4e435035c5390d40be98243502f96090d40d7d4d435035c5350d40bed8143502f86050d409f994435035f5310d40b7994435035e6510d409799443502de6410d40e7990435035f53d4940d714f525027e63d49409f58f525035f43d4940d710f525027e61d49409f587525036f53d4940f3d4f525034f53d4940db94f525036d53d4940db14f52503cc53d4940d314f52503cf43d4940f310f525036f64d4940dbd8f525036e63d4940db58f525036c63d4940dbd0f525034f43d4940db90f525036d43d4940db10f525034c43d4940dbd87525036e61d4940db587525036c61d4940dbd83525036d60d4940b798e52502dd6394940d7d4e525035c5394940dbd4a52502f66194940bd58652502df6354940b718d525035f5354940d714d52502f76154
  | 24 => 0x51d027d6394740d758e51d025d6394740d7d0e51d035c43947409f98a51d027d62947409fd8d51d027c6354740d7d0d51d035c43547409fd8951d027c6254740ded8151d03755114740dd94741d037551d0740be98341d02f960d0740b798e41d02dd6390740b7d8d41d02dc6350740bbd8941d02ec6250740be18141d03765110740dd54441d02fa6010740be58041d027f65cc7409f99731d027d65cc740be98331d02f960cc7409fd9631d027e658c7409f59631d027f654c7409f59531d027c654c740bed8131d02f8604c7409fd9431d027e650c7409f59431d027f65c87409f99721d027d65c8740be98321d02f960c87409fd9621d027e65887409f59621d02fa6088740be58221d027f65487409f59521d027c6548740bed8121d02f860487409fd9421d027e65087409f59421d02be6408740af59021d02de6308740b758c21d03e52108740d7d4e539027e6294e409f58a539027e6194e409f586539035f6494e40d7d8a539035e6294e40d758a539035c6294e40d7d86539035e6194e40d7586539035c6194e40d7982539035c6094e409fd89539027c6254e409fd85539027c6154e40d7d95539035d6454e40d7d89539035e6254e40d7589539035c6254e40d7d85539035e6154e40d7585539035c6154e40d7981539035c6054e40d754c539035e53d0e40b7597439035d65d0e40d794e439035d5390e40be98243902f96090e40d794d439035d5350e40bed8143902f86050e40d754c43902dd6510e40d7594439039e6410e40b798f52902dd63d4a40d794f529035d53d4a40bd98752902f561d4a40d794e529035d5394a40dbd4a529027e6394a409f58e529035f4394a40d710e529027e6194a409f586529035e5354a40d754d529027f6354a409f18d529035f4354a40d710d529027f6154a409f18552902de6314a40b758c529035e5314a40d754c529036d5214a40d794f429035d53d0a40b798e42902dd6390a40d794e429035d5390a40e710e429036e5290a40db54a42902fa6090a40be58242902df6350a40b718d429035e5350a40d754d429036e5250a40db54942902f76150a40bd18542902fb6050a40be181429035e5310a40d754c429039c4310a409fd97329027e65cca409f597329035e53cca40d754f329027f658ca409f996329027d658ca40d794e329035d538ca409fd95329027d654ca409f19532902bf644ca40af191329035e534ca40d754d329027f650ca409f994329027d650ca40d794c329035d530ca40be98032902f9600ca40b798f51902dd63d4640d794f519035d53d4640bb98b51902ed62d4640d794e519035d5394640ddd46519027e63946409f58e519035f4394640d710e519027e62946409f58a519035e5354640d754d519027f63546409f18d519035f4354640d710d519027f62546409
  | 25 => 0x6ec64c8421f394f21087cd53c8421f3d0f21087cc43c8421f9d0721087e441c8421d794e210875d5388421bb58a210876e5288421bd99221086f46488421f594e21087d55388421f5d0e21087d44388421bd58a21086e56288421dd94a21087e65288421f9d0a21087e442884219fd95210875e5348421d754d21086ef6548421dbd95210866f6548421bb99121086ec6448421f394d21087cd5348421f3d0d21087cc4348421bbd85210876e5148421f9d0521087e64148421f950521087e44148421f9cc521087e63148421f94c521087e43148421bdd95210877765484219dd9521086f66448421bd19121087d65348421f554d21087d74348421f510d21086f76248421f9d8921087765248421f994921087e74248421f990921087e54248421f910921087e73248421f98c921087e53248421f90c921087e76548421b9d9521087676548421f9d9121087e66448421b999121087e56448421f919121086e46448421f9d5121087e65448421f955121087e45448421f9d8d21087e66348421f958d21087e46348421f9d4d21087e65348421f194d21087e55348421f154d21087e45348421f9d0d21087c74348421f990d21087e54348421f910d21087c44348421f9d8121087e66048421f958121087e46048421b798f50086dd63d4021d794f500875d53d4021f9487500875e5394021d754e50087e52194021ded42500867e64940219f592500867e63940219f58e500875f4394021d710e500876f4294021db10a50087774194021dd106500875e5354021d754d50087e521540219fd91500867c64540219fd8d500867c6354021d7d0d500875c4354021af99050086bd6414021b798c50086dd6314021d794c500875d5314021f948450087795014021d7d4e53d027e6294f409f58a53d027e6194f409f58653d027f6254f409f18953d027f6154f409f18553d035d5314f40d794f43d035d53d0f40be98343d02f960d0f40f698343d03d960d0f40d794c43d035d5310f40be98043d02f96010f40e799043d03da6010f40f658043d02de6394b40b758e52d036f5294b409f98e52d035e6394b409798e52d027d6394b40d758e52d025d6394b40d7d0e52d035c4394b409f98652d027d6194b409fd8d52d027c6354b40d7d0d52d035c4354b409fd8552d027c6154b40ded8152d036d5214b40db94b42d036d52d0b40be98342d02f960d0b40b798e42d02dd6390b40b7d8d42d02dc6350b40bdd8542d02f46150b40be18142d036e5210b40db54842d02fa6010b40be58042d027f65ccb409f99732d027d65ccb40be98332d02f960ccb409fd9632d027e658cb409f59632d027f654cb409f59532d027c654cb40bed8132d02f8604cb409fd9432d027e650cb409f59432d02de6394740b758e51d037751947409f98e51d035e63947409798e
  | 26 => 0x290c21bd98643086f56190c219fd95430867e6550c219f595430867c6550c21d794d430875d5350c21bbd8943086ec6250c21bdd8543086f46150c219fd94430867e6510c219f594430867c6510c21d7d4c430875e5310c21d754c430875c5310c21b7d94430875f6510c2197d94430875e6510c21b7594430875d6510c2197594430875c6510c21b7990430879e6410c21d7d50430875e5410c21d7550430875c5410c219f992520867d64948219f98e520867d6394821d7d0e520875c43948219f597420875e53d0821d754f42086ed65d0821db597420876f54d0821db55342087ce53d0821f354f42087cf43d0821f310f42087e761d0821bb58742087e461d08219fd96420867d6590821cf952420873d5490821b798e42086dd6390821d794e420875d5390821bb98a42086f66190821bd586420867f6550821b7d8d42086dc6350821d794d420875d5350821bdd8542086fb6050821be181420867f65108219f594420873e5410821cf550420875e5310821d754c42086f66110821bd584420876d65108219b59442086ee6410821eb990420876f5410821eb950420876d5410821eb55042087ce5310821f354c42087cf4310821f310c42087e66110821bb58442087e56110821b9584420867d65cc821d794f320875d53cc8219fd96320867d658c821d794e320875d538c821bd98632086f5618c8219fd95320875e534c821d754d320867f650c8219f594320875e530c821d754c32087cd320c821bd98432086f5610c8219f992510867d64944219f98e510867d6394421d7d0e510875c4394421dbd0a510876c42944219f597410875e53d0421d754f41086f565d0421dd597410877754d0421dd55341087d653d0421f554f41087d743d0421f510f41087e762d0421bd58b41087e462d0421dd94b41087e742d0421f910b410867f65904219f596410873e5490421cf55241086de6390421b758e410875e5390421d754e41086ee6290421bb58a41086f661904219fd9541086df6350421b718d410875e5350421d754d41086ef6250421bb18941086fb6050421be181410867f65104219f994410867d65104219f194410873e5410421cf550410875e5310421d754c41086ee6210421bb58841086f56510421dd59441086756510421bd99041087b66410421ddd5041087b65410421dd55041087b55410421f594c41087d55310421f5d0c41087d44310421f998841086f56210421f958841086e56210421dd94841087e74210421f9108410867d65cc421d794f310875d53cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c4219fd95310875e534c421d754d310867f650c4219f994310867d650c4219f194310875e530c421d754c31086ee620c421bb58831087d5310c421d794f210875d53c8421bb9932108
  | 27 => 0x21bbd8941486ec6250521bed8141486f860505219f994414867e65cc521d7d4f314875c53cc521bb98b31486ed62cc5219f996314867f654c5219f595314867c654c521d7d4d314875c534c521bbd8931486ec624c5219f994314877654c8521dd15321487d743c8521f510f214876e5488521db15221487cf4388521f310e21487e751885219f993504867d64d41219f98f504867d63d4121d7d0f504875c43d4121ded4250486bf6454121af19150486df6354121b718d50486de6314121b758c504877950141219f990504867d64141219f98c504875e63141219798c504867d6314121d758c504865d6314121d7d0c504875c4314121b798f54086dd63d50219f98f540875e63d50219798f540867d63d5021d758f540865d63d50219f98b540876e62d50219f987540877661d50219f983540867d60d50219f596540873f5495021d7d8e540867e63950219f58e540875c63950219f982540867d6095021b7d8d54086dc6355021bed8154086f86055021cfd91540867f6355021d7d8d540865f63550219f18d540875c63550219718d540876c6255021dd185540867f6055021ded81540867b60550219f181540877860550219e181540873d5415021b798c54086dd6315021be98054086f960150219f990540873e64150219f98c540875e63150219798c540867d6315021d758c540865d63150219f988540876e62150219f984540877661150219f980540877a60150219e980540867d6015021de580540867960150219f993530867d64d4c219f98b530876e62d4c219f987530877661d4c219f983530867d60d4c219f596530875f5394c219f992530867d6494c219f982530867d6094c219759653086de6494c21d7d52530875e5494c21d7552530875c5494c21d7d92530875e6494c2197992530875d6494c21d7192530875e6294c21d718a530875e6194c21d7186530875f6094c21d7982530875d6094c21d7182530867f6454c219f191530875f6354c219fd81530867c6054c21d7d9553086dc6454c21d7d51530875e5454c21d7551530875c5454c21d7d91530875e6454c21d7591530875c6454c2197191530875e6254c21d7189530875e6154c21d7185530875c2154c21d7d81530875e6054c21d7581530875c6054c21b798c530875d5314c219f990530867d6414c219f98c530875e6314c219798c530867e6214c21db988530867e6114c21dd984530867e6014c219f580530867f65d0c219f997430867d65d0c219f197430875f53d0c21d794f430875d53d0c21d714f43086df65d0c21d7d97430865f65d0c21d799743086dd65d0c21d7597430865d65d0c21d7197430875f54d0c21d7953430875d54d0c21d7153430867f6590c219f996430867d6590c219f19643086de6390c21d794e430875d5390c21bb98a43086ed6
  | 28 => 0xd0f21887d443c8621ded42508867e64942219f592508867e63942219f58e508875f4394221d710e508876f4294221db10a508867f64542219f191508867f63542219f18d508875f4354221d710d50886de6314221b758c50887795014221b798f54486dd63d51219f98f544875e63d51219798f544867d63d5121d758f544865d63d51219f983544867d60d5121cfd52544867e64951219f98e544867d63951219f58a544876d62951219f586544877561951219f982544867d6095121b7d8d54486dc6355121bed8154486f86055121cfd91544867f6355121d7d8d544865f63551219f18d544875c63551219718d544867f6255121dbd89544866f62551219fd85544877761551219dd85544867f6055121ded81544867b60551219f181544877860551219e181544867e6515121cf550544873e64151219f98c544867d63151219f980544867d60151219f993534867d64d4d219f983534867d60d4d21d7d4e534867e6494d219f592534867e6394d219f58a534876d6294d219f58653487756194d219f982534867d6094d21afd9153486bc6454d21bed8153486f86054d219fd91534873f6454d218fd91534867c6454d21cf191534863c6454d21d7d8d534867f6254d21dbd89534867f6154d21ddd85534867f6054d21ded81534867b6054d219f18153487786054d219e181534867e6514d21d754c534867e6414d219f590534875e6314d219f980534867d6014d219fd97434867e65d0d219f597434867c65d0d21d7d4f434875e53d0d21d754f434875c53d0d21d7d97434875e65d0d21d7597434875c65d0d21d7d53434875e54d0d21d7553434875c54d0d219fd96434867e6590d219f596434867c6590d21cfd52434873c5490d21b798e434867f6550d219f995434867d6550d219f195434867f6510d219f994434867d6510d219f194434873f5410d21cf150434875f5310d21d794c434875d5310d21d714c43486ee6210d21bb58843486f66110d21bd584434875f6510d21d7994434875d6510d21d719443486de6410d21e7990434875f5410d21e7d50434871f5410d21d7950434875d5410d21d7150434879c5410d21c715043487ce6210d21f358843487d66110d21f5584434867e65d0921cfd53424873c54d0921bd98742486f561d09219f99642486de6390921b758e424867c6550921cfd51424873c5450921b7d8d42486dc6350921bdd8542486f46150921bed8142486f860509219f994424867e65cc921d7d4f324875c53cc921bd98732486f561cc9219f996324867c654c921d7d4d324875c534c921bdd8532486f4614c9219f994324867e65d0521cfd53414873c54d0521bb98b41486ed62d05219f99641486de6390521b758e414867f65505219f595414867c6550521cfd51414873c5450521b7d8d41486dc63505
  | 29 => 0xc867d6394321d7d0e50c875c4394321ddd0650c877441943219fd9150c867c64543219fd8d50c867c6354321d7d0d50c875c4354321b798c50c86dd6314321de54050c86de63d5221b758f54886fa60d5221be583548867e63d5221d798f548865e63d52219f58f548875d63d52219758f548876d62d5221dd987548867e60d5221de983548867a60d52219f583548877960d52219e583548873f54952219f98e548867d63952219f982548867d6095221b7d8d54886dc6355221cfd91548867f6355221d7d8d548865f63552219f18d548875c63552219718d548876f62552219fd81548867c6055221cf550548873e64152219f98c548867d6315221db588548877661152219f980548867d60152219f993538867d64d4e21db58b538877661d4e219f983538867d60d4e21d7d4e538867e6494e219f592538867e6094e219f582538867f6454e219f191538875f6354e219fd81538867c6054e21d754c53886fa6014e21be580538867e6414e219f590538875e6314e21db58853887766114e219f980538877a6014e219e980538867d6014e21de58053886796014e219fd97438867e65d0e219f597438867c65d0e21d7d4f438875e53d0e21d754f438875c53d0e21d7d97438875e65d0e21d7597438875c65d0e21d7d53438875e54d0e21d7553438875c54d0e219fd96438867e6590e219f596438867c6590e21bb98a43886ed6290e219fd95438867e6550e219f595438867c6550e21bbd8943886ec6250e219fd94438867e6510e219f594438867c6510e21d7d4c438875e5310e21d754c438875c5310e21bd98443886f56110e21d7d94438875e6510e21d7594438875c6510e21e7990438875f5410e21d7950438875d5410e21d715043887d66110e21f5584438873e54d0a21cf55342886f661d0a21bd587428876d65d0a21dbd5342887ae54d0a21db55342887ad54d0a21f3d0f42887cc43d0a21f998742886ed61d0a21f958742886de6390a21b758e428873e5450a21cf55142886df6350a21b718d42886f76150a21bd18542886fb6050a21be18142886ed6510a21db59442887ae6410a21dbd50428876d5410a21f3d0c42887cc4310a21bb584428875e53cca21d754f32886f661cca21bd587328875e534ca21d754d32886f7614ca21bd18532887cd320ca21cf952418873d5490621b798e41886dd6390621bb98a41886ed6290621b7d8d41886dc6350621bbd8941886ec6250621bed8141886f86050621cf950418873d5410621bb98841886ed6210621d7d4f318875c53cc621d794e318875d538c621bb98a31886ed628c621d7d4d318875c534c621d794c318875d530c621bb98831886ed620c621bb597218876d65c8621bb99321886ec64c8621f3d0f21887cc43c8621bd597218877565c8621dd953218877454c8621f5
  | 30 => 0xd5434c431f58c9310c7d4324c431bb98b500c6ed62d4031ded42500c67e64940319f592500c75f4394031d710e500c67e62940319f58a500c67f64540319f191500c75f4354031d710d500c67f62540319f189500c75f3154031d74c5500c7795014031b798f54c86dd63d5321be98354c86f960d53219f98f54c875e63d53219798f54c867d63d5321d758f54c865d63d5321db98b54c877561d53219f98354c877a60d53219e98354c867d60d5321de58354c867960d5321cfd5254c867e63953219f58e54c867e60953219f58254c86df6355321b718d54c873f64553219fd8d54c875f635532197d8d54c867c6355321d718d54c865c6355321ddd8554c867f60553219f18154c873d5415321cf99054c867e63153219f58c54c876e6215321dd58454c867e60153219f58054c867e64d4f219f59353c876e62d4f21dd58753c867e60d4f219f58353c875f5394f219f99253c867d6494f219f98253c867d6094f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c875d5314f21be98053c86f96014f219f99053c867d6414f21d798c53c876e6214f21dd58453c867e6014f21de98053c867a6014f219f58053c87796014f219e58053c867f65d0f219f99743c867d65d0f219f19743c875f53d0f21d794f43c875d53d0f21d714f43c875f65d0f21d799743c875d65d0f21d719743c875f54d0f21d795343c875d54d0f21d715343c867f6590f219f99643c867d6590f219f19643c86f66190f21bd58643c867f6550f219f99543c867d6550f219f19543c86f76150f21bd18543c867f6510f219f99443c867d6510f219f19443c875f5310f21d794c43c875d5310f21d714c43c86ee6210f21bb58843c875f6510f21d799443c875d6510f21d719443c879e6410f21d7d5043c875e5410f21d755043c875c5410f21f398843c87cd6210f21cf95242c873d5490b21b798e42c86dd6390b21bd98642c86f56190b21b7d8d42c86dc6350b21bd18542c86fb6050b21be18142c873e5410b21cf55042c86f66110b21bd58442c875f53ccb21d714f32c875e538cb21d754e32c86f6618cb21bd58632c875f534cb21d714d32c875e530cb21d754c32c86f6610cb21bd58432c873e54d0721cf55341c86ee62d0721bb58b41c86f565d0721dd59741c877754d0721ed95341c877554d0721ed55341c87d743d0721f510f41c87e662d0721bd58b41c87e562d0721b798e41c86dd6390721cf95141c873d5450721b7d8d41c86dc6350721bbd8941c86ec6250721bed8141c86f86050721bd59441c87756510721ed99041c87775410721dd55041c87d74310721f510c41c86f56210721d794f31c875d53cc721bb98b31c86ed62cc721d794d31c875d534c721bbd8931c86ec624c721f54c431c877b50943219f99250c867d64943219f98e5
  | 31 => 0xd41319f58b504c75f32d4131d74cb504c77b5094131afd91504c6bc6454131bbd89504c6ec6254131de540504c67e64141319f590504c75f4314131d710c504c67e62141319f588504c67e63d5031d798f540c65e63d50319f98b540c67d62d50319f987540c77661d50319f983540c67d60d50319f596540c73f5495031d718e540c67e62950319f58a540c67e60950319f582540c73f6455031d718d540c67f62550319f189540c67f60550319f181540c73d5415031bb988540c6ed6215031be980540c6f960150319f990540c73e64150319f98c540c75e63150319f988540c76e62150319b988540c67d6215031db588540c66d62150319f984540c77661150319f980540c77a60150319e980540c67d6015031de580540c67960150319f992530c67d6494c319f597430c75e53d0c31b7597430c75d65d0c31d7d53430c75e54d0c31d7553430c75c54d0c31b7587430c67f6590c319f596430c73e5490c31cf552430c6de6390c31bd986430c6f56190c319fd95430c67f6510c319f594430c73e5410c31cf550430c75e5310c31bd984430c6f56110c31d7d94430c75d6510c3197594430c6de6410c31e7990430c75f5410c31d7950430c79e5410c31c7950430c75d5410c31e7550430c75c5410c31f5984430c6dd6110c31f5584430c6d56110c31be983520c6f960d4831dbd4a520c67e64948319f592520c75f4394831d710e520c67e60948319f582520c67f64548319f191520c75f4354831d710d520c67f60548319f181520c76d52148319fd97420c67e65d08319f597420c67f65908319f996420c67d6590831b798e420c6dd6390831db94a420c76d52908319fd95420c67d65508319f195420c6df6350831b718d420c76e5250831db549420c6f76150831bd185420c6fb6050831be181420c67f65108319f994420c67d6510831d794f320c76e52cc831db54b320c6f661cc831bd587320c67d658c8319fd95320c75e534c831db948320c76d520c831f34c8320c6f6610c831bd584320c67e64944319f592510c75f4394431d710e510c67d65d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd63904319fd95410c6df6350431b718d410c6ef6250431bb189410c6fb6050431be181410c67f65104319f994410c67d65104319f194410c73e5410431cf550410c6de6310431b758c410c7b54110431b7993310c6dc64cc431d7953310c75c54cc431d754b310c6dd638c431d794e310c6f5638c431dd94e310c7d6538c431f5d0e310c7d4438c4319fd95310c6df654c431d7d95310c65f654c431b7991310c6dc644c431d7951310c75c544c431d7549310c6df614c431d7945310c7d6414c431f5505310c6f7654c431ddd95310c677654c431bdd8d310c7d7634c431dd94d310c7d6534c431f590d310c7
  | 32 => 0x19f98a508c67d62942319fd91508c67c6454231d7d0d508c75c43542319fd89508c67c6254231d7cc5508c7795014231d758f544c67e62d51319f58b544c67e60d51319f583544c73f54951319f992544c67d6395131d758e544c67e62951319f58a544c67d6195131dd586544c67e60951319f582544c6ef6255131bb189544c6fb6055131be181544c73f64551319fd8d544c75f635513197d8d544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd85544c67f6055131ded81544c67b60551319f181544c77860551319e181544c67e6515131cf550544c73e6415131d7d8c544c67e62151319f588544c67e60151319f580544c67e65d0d31cfd53434c73c54d0d31bd987434c6f561d0d31d7997434c65e65d0d31d7197434c75f54d0d31e7d53434c75e54d0d31d7553434c75c54d0d31e7153434c71c54d0d31b758b434c6de61d0d31f5987434c6d661d0d31f5587434c6dd60d0d319f996434c6de6390d319f195434c73f5450d31cf151434c6f76150d31bd185434c67e6510d31b7994434c75e6510d31b7990434c79e6410d31d7d50434c75e5410d31d7550434c75c5410d31b7588434c6de6110d31b7580434c67e64d49319f593524c75f43d4931d710f524c67e60d49319f583524c76f5294931afd91524c6bc6454931bed81524c6f86054931db548524c67e64149319f590524c75f4314931d710c524c67e60149319f580524c67e65d09319f597424c67c65d0931dbd4b424c76c52d09319f996424c67d65909319f196424c73f5490931cf152424c6de6390931b758e424c67f65509319f995424c67c6550931b7d8d424c6dc6350931bdd85424c6f46150931bed81424c6f860509319f994424c67d65109319f194424c73f5410931cf150424c6de6310931b758c424c76f5210931db148424c6f66110931bd584424c67e65cc931b7997324c75e65cc931b7993324c6dc64cc931d7953324c75c54cc931d714b324c6de61cc931b7583324c6dd638c931dbd4a324c76c528c931bd986324c6f5618c931dbd49324c76c524c931bdd85324c6f4614c931b7991324c6dc644c931d7951324c75c544c931f3d89324c7cf524c931d7149324c7cc524c931d3149324c7d7614c931b7185324c7d4614c931b5185324c6df604c9319f994324c6de630c9319f997414c73f54d0531cf153414c6de63d0531b758f414c67e6590531b798e414c6dd63905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c6ef6250531bb189414c6fb6050531be181414c67e6510531f5d0f314c7d443cc531f5ccb314c7d532cc531b7992314c6dc648c531d7952314c75c548c531b758a314c7d7518c531b7582314c67e64d41319f593504c75f43d4131d710f504c67e62
  | 33 => 0x4852cc6fa6014b31be58052cc67f65d0b319f99742cc67d65d0b31db94b42cc76d52d0b319fd9642cc67e6590b319f59642cc6de6390b31b758e42cc67f6550b319f59542cc67c6550b31b7d8d42cc6dc6350b31bdd8542cc6f46150b31bed8142cc6f86050b319fd9442cc67e6510b319f59442cc6de6310b31b758c42cc76e5210b31db54842cc76e52ccb31db54b32cc6f661ccb31bd58732cc6de64ccb31b719332cc75e54ccb31d715332cc75e52ccb31f394b32cc7cd52ccb31b798732cc7d661ccb31f558732cc6dd60ccb31b7d9532cc75f654cb31b799132cc6dc644cb31d795132cc75c544cb31f3d8932cc75e524cb31b718532cc6df604cb31db94832cc76d520cb31bd98432cc6f5610cb31cf95341cc73d54d0731b798f41cc6dd63d0731b798e41cc6dd6390731cf95141cc73d5450731b7d8d41cc6dc6350731bbd8941cc6ec6250731bed8141cc6f86050731ed50441cc77b50943319f99250cc67d6494331d7d0e50cc75c43943319f98a50cc67d62943319fd9150cc67c6454331d7d0d50cc75c43543319fd8950cc67c6254331d7cc950cc75d3254331bb98850cc6ed6214331de54050cc75d63d52319f98b548c67d62d5231dd987548c67e60d52319f583548c73f5495231d7d8e548c67e62952319f58a548c67e60952319f582548c73f6455231d7d8d548c67f62552319f189548c67f60552319f181548c73d5415231cf990548c75d63152319f988548c67d6215231dd984548c67e60152319f580548c73e54d0e31cf553438c6f661d0e31bd587438c75d65d0e31d7d53438c75e54d0e31e7953438c71e54d0e31d7553438c79d54d0e31f5987438c6dd61d0e31f5587438c73e5450e31cf551438c6f76150e31bd185438c6dd6510e31d7594438c79e6410e31d7d50438c75e5410e31d7550438c75c5410e31b7584438c76f5294a319f992528c67d6494a31d7d0e528c75c4394a319f982528c67d6094a319fd91528c67c6454a31d7d0d528c75c4354a319fd81528c67c6054a31db548528c67f65d0a319f997428c67d65d0a319fd96428c67e6590a319f596428c6de6390a31b758e428c67f6550a319f595428c67c6550a31b7d8d428c6dc6350a31bdd85428c6f46150a31bed81428c6f86050a319fd94428c67e6510a319f594428c6f66110a31bd584428c76e528ca31db54a328c6f6618ca31bd586328c76e524ca31db549328c6f7614ca31bd185328c7cd320ca31cf952418c73d5490631b798e418c6dd6390631b7d8d418c6dc6350631bbd89418c6ec6250631bed81418c6f86050631cf950418c73d5410631b798c418c6dd6310631b7597318c75d65cc631b7993318c6dc64cc631d7953318c75c54cc631d754b318c6f565cc631dd597318c77b50942319f992508c67d6494231d7d0e508c75c439423
  | 34 => 0x1075f4354841d710d521077461548419fd81521067c6054841b798c52106dd6314841db54852106fa6014841be580521076e52d0841db54b42106f661d0841bd587421067d6590841b798e42106dd6390841e710e421067f6550841b7d8d42106dc6350841bdd8542106fb6050841be181421079c4310841db948421076d5210841bd98442106f561108419fd97321067e65cc8419f597321075e53cc841d754f32106f661cc841bd587321067f658c8419f996321067d658c841db94a321076d528c8419fd95321067d654c8419f19532106bf644c841af191321075e534c841d754d321076e524c841db54932106f7614c841bd185321067f650c8419f994321067d650c841d798e511075d6394441d7d0e511075c4394441e7d0f411079c43d0441af592411073e5490441b798e41106dd6390441bd59241107765490441ed95241107d66390441f558e41107d74390441f510e41106f66290441bd982411067f6550441b7d8d41106dc6350441e7d0d411079c4350441bbd8941106ec6250441bed8141106f86050441afd95411073f65504418fd95411079f6350441e718d41107af6250441eb18941106bf6150441cf94541107bb6050441ee18141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441f5d8d41107d46350441f5d0d41107b64350441ed10d41107d44350441e510d41107e76250441bd18941107e46250441b918941107f36050441bd18141107f06050441bc181411077b50940419f98e501067d6394041d7d0e501075c43940419f98a501067d62940419fd8d501067c6354041d7d0d501075c43540419fd89501067c6254041b798c50106dd6314041bb98850106ed6214041de54050106ee62d5331bb58b54cc6fa60d5331be58354cc75e63d53319f98b54cc76e62d53319b98b54cc67d62d5331db58b54cc66d62d5331dd58754cc67e60d5331de98354cc67a60d53319f58354cc77960d53319e58354cc73f5495331d718e54cc67e62953319f58a54cc67e60953319f58254cc73f6455331d718d54cc67f62553319f18954cc67f60553319f18154cc73d5415331cf99054cc75e63153319f98854cc67d6215331dd58454cc67e60153319f58054cc6dd65d0f31d759743cc75f54d0f31d795343cc75d54d0f31d715343cc6dd62d0f31b798743cc6dd60d0f31cf95243cc73d5490f31bd98643cc6f56190f31cf95043cc73d5410f31bd98443cc6f56110f31d759443cc79e6410f31d7d5043cc75e5410f31e795043cc71e5410f31d755043cc79d5410f31b758843cc6de6110f31f598443cc7d56110f31b758043cc76f5294b319f99252cc67d6494b31d7d0e52cc75c4394b319f98252cc67d6094b319fd9152cc67c6454b31d7d0d52cc75c4354b319fd8152cc67c6054b31db5
  | 35 => 0xc534c941dbd49325076c524c9419f994325067d650c9419f194325075f530c941d714c325076f520c941db14832506f6610c941bd584325075f53d0541d714f415076f52d0541db14b41507d753d0541f514f41507d743d0541f510f41507e752d0541dd14b41507e452d0541d914b41506de6390541b758e415075f5390541d714e415079f4390541e710e415076f5290541db14a415079e6390541e758e415079f5390541e714e41507af5290541eb14a41507b75190541d7d4f505075c53d4141dbd4b505076c52d41419f98f505067d63d4141d7d0f505075c43d41419f98b505067d62d4141ded4f50507db53d4141d6d4f505077a53d4141de54f505077853d4141f614f505075853d4141f6d0f50507d843d4141ded4b50507eb52d4141dad4b505077a52d4141de54b505077852d4141fa14b505076852d4141fcd0750507ba41d4141ded93505077b63d4141de98f505077963d4141de18f505077b43d4141d6d0f505077a43d4141de50f505077843d4141d610f505077b62d4141de98b505077962d4141de18b505077b42d4141de90b505077942d4141de10b505077b32d4141de8cb505077932d4141de0cb505077b61d4141ded07505077a41d4141b798e50506dd6394141d7d4e505075c5394141bb98a50506ed6294141dbd4a505076c5294141ded4250506df6354141b718d505075f5354141d714d50506ef6254141bb189505076f5254141db149505075f5314141d714c505076f5214141db148505077950141419f98c505067d6314141d7d0c505075c43141419f988505067d6214141ddd0450506fa6514141de994505077b5314141f6d4c505075b5314141de94c50507795314141de14c50507d85314141d614c50507db4314141f610c505077b5214141fad48505076b5214141de94850507795214141de14850507e85214141da14850507f34114141ee904505077b6414141ded8c505077a6314141de58c50507786314141ded0c505075b4314141de90c50507794314141de10c50507584314141ded88505077a6214141de58850507786214141ded08505077a4214141de50850507784214141decc8505077a3214141de4c850507783214141ded84505077b4114141dcd04505077a4114141de504505075f5394c419f98a531067d6294c419f982531067d6094c419fd89531067c6254c419fd81531067c6054c41d754c53106ee6214c41bb58853106fa6014c41be580531075e53d0c41d754f43106f661d0c41bd587431075e54d0c41f598743107d561d0c419f59643106de6390c419fd95431075e5310c41d754c43106f66110c41bd58443106de6410c41e7990431075e5410c41f598443107d56110c41dbd4a521067e63948419f58e521075f4394841d710e521067e60948419f582521067f63548419f18d52
  | 36 => 0x42419f98e509067d6394241d7d0e509075c43942419f98a509067d6294241ddd06509075e5354241d754d509067f63542419f18d509075f4354241d710d509067f62542419f18950906de6314241b758c509075e5314241d754c509077950142419f98b535067d62d4d419f983535067d60d4d41d7d93535075f62d4d41d798b535075d62d4d41d718b535075f61d4d41d7587535075f60d4d41d7983535075d60d4d41d7183535075f5394d41bb98a53506ed6294d41be98253506f96094d41bbd8953506ec6254d41bed8153506f86054d41d754c535067e6214d419f588535067e6014d419f58053506de6514d41d7994535075f6414d41d7d88535075e6214d41d7588535075c6214d41d7d84535075d6114d41d7504535075f6014d41d7980535075d6014d41d7180535067e65d0d41d714f43506de65d0d41d7997435065e65d0d41b798e435075f5390d41d714e43506f66190d41bd586435075f5350d41d714d43506f76150d41bd185435067e6510d41d7d4c43506de6510d41d7994435065e6510d41b7990435079e6410d41d7d4f525075c53d49419f98f525067d63d4941d7d0f525075c43d49419f983525067d60d4941dbd4f52507cf53d4941d3d4f525076e53d4941db54f525076c53d4941f314f525074c53d4941f3d0f52507cc43d4941dbd93525076f63d4941db98f525076d63d4941db18f525076f43d4941d3d0f525076e43d4941db50f525076c43d4941d310f525076f61d4941db587525076f60d4941db983525076d60d4941db18352506de6394941b758e525075f5394941d714e525076f5294941be98252506f96094941b7d8d52506dc6354941d7d4d525075c5354941bed8152506f86054941d7d4c525075c5314941db548525067e63149419f58c525075f4314941d710c525067e60149419f58052506ee6514941db994525076f5314941f3d4c525074f5314941db94c525076d5314941db14c52507cc5314941d314c52507cf4314941f310c525076f6414941dbd8c525076e6314941db58c525076c6314941dbd0c525074f4314941db90c525076d4314941db10c525074c4314941dbd84525076d6114941db504525076f6014941db980525076d6014941db180525067e65d0941d7d4f425075c53d0941db14b42506de6390941b758e425075f5390941d714e425076f5290941db14a42506f66190941bd58642506df6350941b718d425075f5350941d714d425076f5250941db14942506f76150941bd18542506fb6050941be181425067e6510941d7d4c425075c5310941dbd48425067e65cc9419f597325067c65cc941d7d4f325075c53cc941dbd4b325076c52cc9419f996325067d658c9419f196325075f538c941d714e325076f528c941db14a325067f654c9419f995325067c654c941d7d4d325075
  | 37 => 0xd798e52d065e6394b419f58e52d075d6394b419758e52d075f4394b41d710e52d067e6094b419f58252d067f6354b419f18d52d075f4354b41d710d52d07776154b419fd8152d067c6054b41db54852d076e52d0b41db54b42d06f661d0b41bd58742d06de6390b41b758e42d06df6350b41b718d42d06f46150b41bed8142d06f86050b41db94842d076d5210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d06f661ccb41bd58732d067f658cb419f99632d067d658cb419fd9532d067d654cb419f19532d06f7614cb41bd18532d067f650cb419f99432d067d650cb41b798e50d06dd6394341ded4250d067e6394341d798e50d065e63943419f58e50d075d63943419758e50d075f4394341d710e50d067e62943419f58a50d067f63543419f18d50d075f4354341d710d50d067f62543419f18950d07795014341d7d4e539067e6294e419f58a539067e6094e419f582539075f6494e41d7d8a539075e6294e41d758a539075c6294e41d7986539075c6194e41d7d82539075e6094e41d7582539075c6094e419fd89539067c6254e419fd81539067c6054e41d7d95539075d6454e41d7d89539075e6254e41d7589539075c6254e41d7985539075c6154e41d7d81539075e6054e41d7581539075c6054e41d754c539075e53d0e41b7597439075d65d0e41d794e439075d5390e41bd98643906f56190e41d794d439075d5350e41bdd8543906f46150e41d754c43906dd6510e41d7594439079e6410e41b798f52906dd63d4a41d794f529075d53d4a41be98352906f960d4a41d794e529075d5394a41dbd4a529067e6394a419f58e529075f4394a41d710e529067e6094a419f582529075e5354a41d754d529067f6354a419f18d529075f4354a41d710d529067f6054a419f18152906de6314a41b758c529075e5314a41d754c529076d5214a41d794f429075d53d0a41b798e42906dd6390a41d794e429075d5390a41e710e429076e5290a41db54a42906f66190a41bd58642906df6350a41b718d429075e5350a41d754d429076e5250a41db54942906f76150a41bd18542906fb6050a41be181429075e5310a41d754c429079c4310a419fd97329067e65cca419f597329075e53cca41d754f329067f658ca419f996329067d658ca41d794e329075d538ca419fd95329067d654ca419f19532906bf644ca41af191329075e534ca41d754d329067f650ca419f994329067d650ca41d794c329075d530ca41bd98432906f5610ca41d794f419075d53d0641e7d0f419079c43d0641af597419073d65d0641e794f419079d53d0641bd597419077565d0641f594f41907d553d0641f5d0f41907d443d0641dd94b41906de63d4241b758f509075e53d4241d754f50906ee62d4241bb58b509075e5394241d754e509077b509
  | 38 => 0x504ca7e64141329f590504cb5f4314132d710c504ca7e61141329f584504ca7e63d5032d798f540ca5e63d50329f98b540cb6e62d50329f987540ca7d61d50329f983540ca7d60d50329f596540cb3f5495032d718e540ca7e61950329f586540ca7e60950329f582540cb3f6455032d718d540ca7f61550329f185540ca7f60550329f181540cb3d5415032bd984540caf56115032be980540caf960150329f990540cb3e64150329f98c540cb5e63150329f988540cb6e62150329f984540cb7661150329d984540ca7d6115032dd584540ca7561150329f980540cb7a60150329e980540ca7d6015032de580540ca7960150329f992530ca7d6494c329f597430cb5e53d0c32b7597430cb5d65d0c32d7d53430cb5e54d0c32d7553430cb5c54d0c32b758b430ca7f6590c329f596430cb3e5490c32cf552430cade6390c32bb98a430caed6290c329fd95430ca7f6510c329f594430cb3e5410c32cf550430cb5e5310c32bb988430caed6210c32d7d94430cb5d6510c3297594430cade6410c32e7990430cb5f5410c32d7950430cb9e5410c32c7950430cb5d5410c32e7550430cb5c5410c32f3988430cadd6210c32f3588430cacd6210c329f992520ca7d6494832d7d0e520cb5c43948329f597420ca7f65908329f596420cb3e5490832cf552420cade6390832b758e420ca7f6550832b7d8d420cadc6350832bdd85420caf46150832bed81420caf860508329fd94420ca7e65108329f594420ca7c6510832cf950420cb3d5410832b798c420cadd6310832eb508420cade64cc832b7193320cb5e54cc832d7153320cadd638c832d794e320caed638c832db94e320cbce538c832f3d0e320cbcc438c8329fd95320cadf654c832d7d95320ca5f654c832b7991320cadc644c832d7951320cb5c544c832b7d89320cb5e524c832f3909320cbcd424c832bbd95320cb6f654c8329bd95320caef634c832f3d8d320cb6e534c832f394d320cbce434c832f350d320cafa60d4432be583510cb7751944329f992510ca7d6494432d7d0e510cb5c43944329f982510ca7d60944329fd91510ca7c6454432d7d0d510cb5c4354432d7cc9510cb5d32544329fd81510ca7c6054432dd544510caf661d4032bd587500cb7b50940329f992500ca7d6494032d7d0e500cb5c43940329f986500ca7d61940329fd91500ca7c6454032d7d0d500cb5c4354032d7cc9500cb5d32540329fd85500ca7c6154032de540500cb5f5394f419f98a53d067d6294f419f98253d067d6094f419fd8953d067c6254f419fd8153d067c6054f41d754c53d075e53d0f41d754f43d06f661d0f41bd58743d07d661d0f41f558743d075e5310f41d754c43d06f66110f41bd58443d079e6410f41f598443d07d56110f41b798e52d06dd6394b41dbd4a52d067e6394b41
  | 39 => 0xcb5e54d0e32e7953438cb1e54d0e32d7553438cb9d54d0e32f398b438cadd62d0e32f358b438cb3e5450e32cf551438caef6250e32bb189438cadd6510e32d7594438cb9e6410e32d7d50438cb5e5410e32d7550438cb5c5410e32b7588438cb3e5490a32cf552428cade6390a32b758e428cadf6350a32b718d428caf76150a32bd185428cafb6050a32be181428cb3e5410a32cf550428cade6310a32b758c428cadd65cca32d7597328cade64cca32b7193328cb5e54cca32d7153328caed65cca32db597328cb7751946329f992518ca7d6494632d7d0e518cb5c43946329f982518ca7d60946329fd91518ca7c6454632d7d0d518cb5c4354632d7cc9518ca7f60546329f181518cb755114632ded42508ca7e64942329f592508cb5f4394232d710e508ca7e61942329f586508ca7f64542329f191508cb5f4354232d710d508cb5f32542329fd85508ca7c6154232de540508cb5d63d51329f987544ca7d61d51329f983544ca7d60d5132cfd52544ca7e64951329f58e544cb5d63951329f58a544cb6d62951329f986544ca7d61951329f982544ca7d6095132bdd85544caf46155132bed81544caf86055132cfd91544ca7f6355132d7d8d544ca5f63551329fd89544cb6f62551329fd85544cb7761551329dd85544ca7c6155132dd185544ca7461551329fd81544cb7b60551329ed81544ca7c6055132de181544ca7860551329f994544cb3d5415132cf990544cb5f63151329f984544ca7d61151329f980544ca7d60151329f997434cb3f54d0d32cf153434caee62d0d32bb58b434cb5e65d0d3297997434cb5c65d0d32d7d53434cb9f54d0d32d7953434cb5d54d0d32d7153434cb9c54d0d32c7153434cade62d0d32f398b434cace62d0d32f358b434cadd61d0d32b7583434ca7e6590d32b798e434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d329f994434cade6510d32d7994434cade6410d32e7990434cb5f5410d32d7950434cb5d5410d32d7150434cade6210d32b7584434cadd6010d329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e6590932b798e424cadd63909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424caf76150932bd185424cafb6050932be181424ca7e6510932f3d0f324cbcc43cc932b7992324cadc648c932d7952324cb5c548c932f3d4a324cadd618c932b7582324ca7e64d45329f593514cb5f43d4532d710f514ca7e60d45329f583514cb775194532afd91514cabc6454532bed81514caf86054532dd544514ca7e64145329f590514cb5f4314532d710c514ca7e60145329f580514ca7e64d41329f593504cb5f43d4132d710f504ca7e61d41329f587504cb7b5094132afd91504cabc6454132bdd85504caf46154132de54
  | 40 => 0x6550842cfd954210a3f6550842e7d8d4210b9c6350842afd894210b3e5250842edd854210bb46150842eed814210bb86050842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210bcf6350842f318d4210bcf4350842eb90d4210bac4350842f310d4210b8c4350842f9d854210aec6150842f91854210ae46150842fad814210aec6050842fa1814210ae86050842ddd465110a7e63944429f58e5110b5f4394442d710e5110a7e60944429f5825110a7f63544429f18d5110b5f4354442d710d5110a7f60544429f1815110ade6314442b758c5110b755114442be9805110af96014442ded425010a7e63940429f58e5010b5f4394042d710e5010a7e61940429f5865010a7f63540429f18d5010b5f4354042d710d5010a7f61540429f1855010ade6314042b758c5010af66114042bd5845010b795014042bd98754ccaf561d5332be98354ccaf960d5332d798f54ccb6d62d53329f98754ccb7661d53329d98754cca7d61d5332dd58754cca7561d53329f98354ccb7a60d53329e98354cca7d60d5332de58354cca7960d5332cfd5254ccb5c63953329f98654cca7d61953329f98254cca7d6095332cfd9154ccb5c63553329fd8554cca7c61553329fd8154cca7c6055332cf55054ccb3e6415332d798c54ccb6d62153329f98454cca7d61153329f98054cca7d6015332b759743ccb5d65d0f32d7d5343ccb5e54d0f32d755343ccb5c54d0f32b798b43ccadd61d0f32b758343ccb3e5490f32cf55243ccaee6290f32bb58a43ccb3e5410f32cf55043ccaee6210f32bb58843ccb5d6510f32e799043ccb5f5410f32d795043ccb9e5410f32c795043ccb5d5410f32e755043ccade6210f32f398843ccbcd6210f32b758443ccadd6010f32cf95342ccb3d54d0b32b798f42ccadd63d0b32b798e42ccadd6390b32cf95142ccb3d5450b32b7d8d42ccadc6350b32bdd8542ccaf46150b32bed8142ccaf86050b32eb50842ccb7751947329f99251cca7d6494732d7d0e51ccb5c43947329f98251cca7d60947329fd9151cca7c6454732d7d0d51ccb5c43547329fd8151cca7c6054732dd54451ccafa6014732be58051ccb7b50943329f99250cca7d6494332d7d0e50ccb5c43943329f98650cca7d61943329fd9150cca7c6454332d7d0d50ccb5c43543329fd8550cca7c6154332bd98450ccaf56114332de54050ccb5d63d5232db98b548ca7e61d52329f587548ca7e60d52329f583548cb3f5495232d7d8e548ca7e61952329f586548ca7e60952329f582548cb3f6455232d7d8d548ca7f61552329f185548ca7f60552329f181548cb3d5415232cf990548cb5d6315232db988548ca7e61152329f584548ca7e60152329f580548cb3e54d0e32cf553438caee62d0e32bb58b438cb5d65d0e32d7d53438
  | 41 => 0x5429f5805150af66514542dd9945150b775314542f5d4c5150b575314542dd94c5150b755314542dd14c5150bd45314542d514c5150bd74314542f510c5150be74214542ed9085150b776414542ddd8c5150b766314542dd58c5150b746314542ddd0c5150b574314542dd90c5150b754314542dd10c5150b544314542ddd885150b774214542d9d085150b764214542dd5085150b776014542dd9805150b756014542dd1805150b5f53d4142d714f5050b7751d4142dd1475050a7e63d41429f58f5050b5f43d4142d710f5050a7e61d41429f5875050b7b53d4142f6d4f5050b5b53d4142de94f5050b7953d4142de14f5050bd853d4142d614f5050bdb43d4142f610f5050beb42d4142ee90b5050b7b51d4142fcd475050b7351d4142de9475050b7951d4142de1475050bf051d4142dc1475050b7b64d4142ded8f5050b7a63d4142de58f5050b7863d4142ded0f5050b5b43d4142de90f5050b7943d4142de10f5050b5843d4142ded8b5050b7b42d4142de90b5050b7b61d4142de9875050b7961d4142de1875050ade6394142b758e5050b5f5394142d714e5050af66194142bd5865050b775194142dd1465050b7b5094142b7d8d5050adc6354142d7d4d5050b5c5354142bdd855050af46154142ddd455050b745154142d7d4c5050b5c5314142ddd445050b745114142de5405050a7e63141429f58c5050b5f4314142d710c5050b6f42141429f9845050a7d6114142be9945050b7a6514142ded4c5050bdb5314142d6d4c5050b7a5314142de54c5050b785314142f614c5050b585314142f6d0c5050bd84314142fad085050bba4214142ded445050bf35114142dcd445050b7a5114142de5445050b785114142fc1445050b705114142ded905050b7b6314142de98c5050b796314142de18c5050b7b4314142d6d0c5050b7a4314142de50c5050b784314142d610c5050b7b6214142ded085050b6b4214142de9085050b794214142ded845050b7a6114142de5845050b786114142d7d4e5310a7e6194c429f5865310a7e6094c429f5825310a7f6154c429f1855310a7f6054c429f1815310b5d5314c42bd9845310af56114c42be9805310af96014c42d794f4310b5d53d0c42bb98b4310aed62d0c42d79534310bce62d0c42f358b4310a7d6590c42b798e4310a7f6550c42d794c4310b5d5310c42bb9884310aed6210c42b79904310b9e6410c42d79504310bce6210c42f35884310b5e6394842d758e5210b5f4394842d710e5210b9f43d0842e710f4210abd6490842cf9524210ade6390842b758e4210aed6490842db9524210bae5490842f398e4210bcd6390842f3d0e4210bcc4390842bb9864210aee60908429fd954210adf6350842b718d4210b9f4350842e710d4210af76150842bd1854210afb6050842be1814210abf
  | 42 => 0x75944390b5d6510e42e79904390b5e53d0a42d754f4290b9f43d0a42e710f4290abd65d0a42cf5974290b9e53d0a42e754f4290aed65d0a42db5974290bce53d0a42f354f4290bcf43d0a42f310f4290ade63d4642b758f5190b5e53d4642d754f5190afa60d4642be5835190b5e5394642d754e5190b7751946429f98e5190a7d6394642d7d0e5190b5c4394642dbd0a5190a7e60946429f5825190b5e5354642d754d5190a7f63546429f18d5190b5f4354642d710d5190a7f60546429f1815190ade6314642b758c5190b5e5314642d754c5190b755114642b798f5090add63d4242d794f5090b5d53d4242bd9875090af561d4242d794e5090b5d5394242ded425090a7e63942429f58e5090b5f4394242d710e5090b6f42942429f9865090a7d6194242d794d5090b5d53542429fd8d5090a7c6354242d7d0d5090b5c43542429fd855090a7c6154242b798c5090add6314242d794c5090b5d5314242de5405090a7e61d4d429f5875350a7e60d4d429f5835350b5f64d4d42d7d8b5350b5d62d4d42d7d875350b5e61d4d42d75875350b5c61d4d42d7d835350b5e60d4d42d75835350b5c60d4d42d7d4e5350af66194d42bd5865350afa6094d42be5825350af76154d42bd1855350afb6054d42be1815350b5d5314d429f9845350a7d6114d429f9805350a7d6014d42b79945350b5e6514d42d7d905350b5f6214d42d75885350b5d4214d42d7d845350b5e6114d42d75845350b5c6114d42d7d805350b5e6014d42d75805350b5c6014d429f9974350b5c53d0d42b79974350b5e65d0d42979974350ade6390d42d7d4e4350b5c5390d42bb98a4350aed6290d42d7d4d4350b5c5350d42bbd894350aec6250d429f9944350b5f5310d42b79944350b5e6510d42979944350ade6410d42e79904350b5f53d0942d714f4250bcf53d0942f314f4250bcf43d0942f310f4250ade6390942b758e4250b5f5390942d714e4250b9f4390942e710e4250b9e6390942e758e4250b9f5390942e714e4250baf5290942d7d4f5150b5c53d45429f98f5150a7d63d4542d7d0f5150b5c43d45429f9835150a7d60d4542ddd4f5150bd753d4542d5d4f5150b7653d4542dd54f5150b7453d4542f514f5150b5453d4542f5d0f5150bd443d4542f9d0b5150bb642d4542ddd935150b7763d4542dd98f5150b7563d4542dd18f5150b7743d4542d5d0f5150b7643d4542dd50f5150b7443d4542d510f5150b7762d4542ddd0b5150b7642d4542ddd835150b7660d4542dd5835150b7460d4542b798e5150add6394542d7d4e5150b5c5394542ddd465150afa6094542be5825150adf6354542b718d5150b5f5354542d714d5150afb6054542be1815150b5f5314542d714c5150b7551145429f98c5150a7d6314542d7d0c5150b5c4314542dbd085150a7e6014
  | 43 => 0x5210edd6114843f55845210ed56114843b79805210fda6014843b69805210edd6014843f65805210ed96014843e79935110f9e54d4443b798b5110edd62d4443d7d4b5110f5d52d4443b79835110edd60d4443b75965110f5e5494443e79525110ede6294443b758a5110f5f5194443f5d465110ede6094443b75825110f5e5454443e79515110edf6254443b71895110f5f5254443d75495110fd75154443d79455110edf6054443b71815110f9e6414443e79505110ede6214443f39885110ece6214443b75885110fcd6214443b35885110ede6114443d7d445110fd65114443d75445110fd55114443d55445110ede6014443f69805110eda6014443b75805110fd96014443b65805110f9e64d4043e79535010ede62d4043b758b5010f5f52d4043d754b5010ede61d4043b75875010f5f51d4043d75475010edd6594043d79525010f9e5494043b798a5010edd6294043b79865010edd6194043d7d425010fdb5094043d79515010f9e5454043b7d895010edc6254043d7d495010f5d5254043b7d855010edc6154043d7d455010f5d5154043f6d415010f5e5054043e79905010f9e5414043b79885010fce6214043b39885010edd6214043f35885010ecd6214043b79845010fd66114043b59845010edd6114043f55845010ed56114043b79805010f5f5014043f69405010f5d5014043f65405010f595014043d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42d794f43d0b5d53d0f42bb98b43d0aed62d0f42f398b43d0bcd62d0f42d794c43d0b5d5310f42bb98843d0aed6210f42e799043d0bce6210f42f358843d0ade6394742b758e51d0b7751947429f98e51d0b5e63947429798e51d0a7d6394742d758e51d0a5d6394742d7d0e51d0b5c43947429f98251d0a7d60947429fd8d51d0a7c6354742d7d0d51d0b5c43547429fd8151d0a7c6054742dd54451d0ade6394342b758e50d0b7b50943429f98e50d0b5e63943429798e50d0a7d6394342d758e50d0a5d6394342d7d0e50d0b5c43943429f98650d0a7d61943429fd8d50d0a7c6354342d7d0d50d0b5c43543429fd8550d0a7c6154342de54050d0b5f5394e429f9865390a7d6194e429f9825390a7d6094e42d7d925390b5e6294e42d718a5390b5f6194e42d79865390b5d6194e42d71865390b5f6094e42d79825390b5d6094e42d71825390a7f6154e429f1855390a7f6054e429f1815390b5f6554e42d75915390b5e6254e42d71895390b5f6154e42d79855390b5d6154e42d71855390b5f6054e42d79815390b5d6054e42d71815390b5d5314e42d794f4390add65d0e42d75974390b5e5390e42d754e4390aee6290e42bb58a4390b5e5350e42d754d4390aef6250e42bb1894390b5d5310e42b
  | 44 => 0xe7f6054a439f1815290f6d5214a43bb98b5190eed62d4643be9835190ef960d4643ddd465190f5f43946439f98a5190e7d62946439f9825190e7d6094643d7d0d5190e7f62546439f1895190e7f60546439f1815190f755114643bb98b5090eed62d4243bd9875090ef561d4243ded425090f5f43942439f98a5090e7d62942439f9865090e7d6194243d7d0d5090e7f62542439f1895090e7f61542439f1855090f795014243e7d4e4350f5f43d49439f9875250e7d61d49439f9835250e7d60d4943dbd4a5250ef76154943bd1855250efb6054943be1815250f6d5214943d7d0c5250e7e61149439f5845250e7e60149439f5805250f5f43d45439f98b5150e7d62d45439f9835150e7d60d4543ddd465150eef6254543bb1895150efb6054543be1815150f755114543d7d0c5150e7e62145439f5885150e7e60145439f5805150f5f43d41439f98b5050e7d62d41439f9875050e7d61d4143ded425050eef6254143bb1895050ef76154143bd1855050f795014143d7d0c5050e7e62141439f5885050e7e61141439f5845050ebd6490c43cf9524310edd6490c43d79524310f9e5490c43b798a4310edd6290c43b79864310edd6190c43b79824310edd6090c439fd954310ebf6550c43cfd954310e3f6550c43afd8d4310f3e5350c43b7d954310f5f6550c4397d954310edf6450c43e7d914310f5e5450c43e79514310edf6250c43b71894310edf6150c43b71854310edf6050c43b71814310f6f52948439f9865210e7d61948439f9825210e7d60948439fd855210e7c61548439fd815210e7c6054843db5485210ef66114843bd5845210efa6014843be5805210f7751944439f98a5110e7d62944439f9825110e7d60944439fd895110e7c62544439fd815110e7c6054443bb9885110eed6214443dd5445110efa6014443be5805110f7b50940439f98a5010e7d62940439f9865010e7d61940439fd895010e7c62540439fd855010e7c6154043bb9885010eed6214043bd9845010ef56114043de5405010ede6295043b758a5410ede6195043b75865410ede6095043b75825410f1e6495043d798a5410f5d6295043d79865410f5d6195043d79825410f5d6095043e75965410f9f6295043e798a5410f9d6295043e718a5410f9f6195043e79865410f9d6195043e71865410f9f6095043e79825410f9d6095043e71825410f9e64d4843e79535210ede61d4843b75875210ede60d4843b75835210edd6594843d79525210f9e5494843d7d4a5210fcf5294843b79865210edd6194843b79825210edd6094843d79515210f9e5454843f3d495210f5e5254843b7d855210edc6154843b7d815210edc6054843e79905210f9e5414843b79885210f5f5214843f39485210f5d5214843f35485210f4d5214843b79845210fd66114843b5984
  | 45 => 0x40020004005000001700080010004000002c0040000008002c00a0008005000000200000100008005002400200080000044000002c002000c00000000070028002001000100000010000006001800200080080004001000400200080010008004000000500040060008000001000000000020008002000000000140000000006000c010001400b00040050018000000400100000010000003000400c0000011000000100000020010005000400000000010004008000000000000000000001000000000280000004005000800000000010008005000c0030020001003000100080010010000000000200200000038003000000a000000100080010000000000400000180070000002000c006001000d0000007000c0000000008001400a002c00b000c006000c002000000d000c00000040040004001000800000000030004000000000500000000004003000000000180050010003000000100040000004002000c00000036f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0f7b50943439f98a50d0e7d62943439f98650d0e7d61943439fd8950d0e7c62543439fd8550d0e7c6154343de54050d0f9e64d4b43b798752d0edd61d4b43b798352d0edd60d4b43d7d4a52d0fcf5294b43d3d4a52d0ede6194b43b758652d0ede6094b43b758252d0fcf5254b43d794952d0edf6154b43b718552d0edf6054b43b718152d0f9e6414b43d7d4852d0fce5214b43d754852d0fcd5214b43b798452d0edd6114b43b798052d0edd6014b43e799351d0ede62d4743b758b51d0f5f52d4743d754b51d0ede60d4743b758351d0ede6294743b758a51d0f5f5194743f5d4651d0f575194743b798251d0edd6094743b7d8951d0edc6254743d7d4951d0f5d5254743f5d4551d0f5e5154743b7d8151d0edc6054743e799051d0ede6214743b758851d0f5f5114743f594451d0f5d5114743f554451d0ede6014743b758051d0f9e64d4343b798b50d0edd62d4343d7d4b50d0f5d52d4343b798750d0edd61d4343d7d4750d0f5d51d4343b798a50d0edd6294343b798650d0edd6194343d7d4250d0fdb5094343d6d4250d0edf6254343b718950d0f5f5254343d754950d0edf6154343b718550d0f5f5154343d754550d0fdb5054343d794150d0f9e6414343b798850d0edd6214343b798450d0edd6114343d7d4050d0fda5014343d754050d0fd95014343af5974390f3d65d0e43b75974390f5d65d0e43bd9875290ef561d4a43be9835290ef960d4a43dbd4a5290f5f4394a439f9865290e7d6194a439f9825290e7d6094a43d7d0d5290e7f6154a439f1855290
  | 46 => 0xc001000c00100000000004006006400300240020008004000400100040090000000000400200080020014001001400400140000008000001000100300010004001000000b001000100000000018004000c0200004004000c003000c000000400c0000000003c007000400000240020004005000000100000000000002001800100000010004000002000300080000090003000c00200080000000001000000a0000009000400400200040004002000c00a00080040010000000801b00440080020002000400100040030000000000c0010000003000c008001c000000000300000120000000001c0000000000000400a0008001000000600000010000000000400000080000014004002800000000010024000000000000240010018007000c00500040000000001001c00000140000000005000800000200140000002000000000240000000007000400000000010014000000400000140000000000000c000006c00600280010004002002800200040030004000005c006000400e000400400100000014001000401400380020004000000000200040090004000001800000000000000001000c00300000050004005000000100000030000000001400200000000024002000000000080010000000000c0020004003001c00100040000000002000400300000020000007000000c0014003000800000200100008004000400f0004000001000100380050000002000c0040024001001400000080010000000000000300140000008012001c000000001c00000000034004001000400100050008002000c001000000500180000000002000c000000800000340040004003000c000001000000080000000005003000100000020010001000000a000800800280020004005000c001000c002001000300000000018000001000100080030004000000c0000018004001c000000400000080010020002000c0000020001000000e001c00000000010000001000c006000c00400100000024000001c00c00000000008002000c000001c00200a4002000000200000020018004001000c001c0020050001000400100080020004001000c00100200070004015000c00c0020001000000d000800d000400100000000020002000000000140000008003001000000100070000002003400100040000000001000000100080000000010000000e002c007004c0060024000000c001002c0000004016000000300000030004000001000800000000028000000000200040010000007000000000000060000000000c01e0000000000000200000040008000000400000240000000003000c00600040010000005000400c000401e000c001001c001000c0020000006003000100000000004000000001c000400000280000004003004000300080070000002001c00
  | 47 => 0x40010002002c006000c00600080000020000000401c0000004000c009000800e000800000140050038001004c00300080000010006001000200000000008001001c001002000000040010000000000800000080000000004000000200000010008015001400a00000000000001000c0020008005000000100140000000000000400600140020004000000400000040010000008000000100040010014001000000d000c007002c0030014000001000d0000004000000800040010004000001c00000040010004001000000000040000000000000800100480040004001003c003000000600000060000004000c009002000100080010010001000400000000000000005000c00800100010000002000000700180000008001000c0000030002001400000040020018000001800000040000018001000400200200020038000000000000000070024000000000400040020090001000c0020000001001c0020034000001800600040080000001000c004001c00000140030004002001000500180000014000000c0000010000001c00f0000001000c011000000000000020000001001c0050004000000000200040050004000002800a0010000002c0060000000000801a001000000040030004004000c0050000003001c000000800e000000000040090010000000000000000000008005000001000040000000000001c0030000003002c00100080010000003000c005000c00600080060008006000400400040070020002000c007001400100000030000001000000400080000004002000c00300080060008001000000900400000010000000001b004c00200000020000005000000000040090038000000000100000110020000000c004000400b00080040020003000000800000040000001000400600000010018000000000100000000004001001400400100020044010000c00200000000008006000c0000000000000400e0008000000c00200000100000004001400000100000000002002c0070004003001c001000000200040000004001000000100380000008006003c005001c0010000000004000400280000000000000400000080000008000001c007000c000000000300000000004007003c0000008008003c00200100030000000000c00200100020004000001000200000000010001000400100040000000001000000000000000004004001400500000020018000000c00000000010000000000800400100050014002000400c0000000000000100000030000001000c0010024000000800200040020000002000800a000c0000000000000400700000080008006000c0130028000002c0020028000001c00a000400300080020068002003c00500040010000003001000200300000004000001000000000080004000000800100
  | 48 => 0x8008000400100040000018001000000600080000004003001c00500280010010005000000100000040000027000800d0004001000c0000004003000000b000400a0008000000000400000020000001000000000180000008005003c0010008000000400a00000010000001000400000100050000000000800000140020000005000400100080030000000000001b0008000001800a000800d000c00500040020000002000401400040000000000000c007003400000000010000000000400e0018001000000900000000000000000000200080060014001006800800040020004002000400400200040004000000000000000020000001002000300100060000000003c00c000c0000018000000000d00000090014007001400600000030000001001c0030008000000800000080000000004000000100180020004003001000400040030000000000000000000010008000000000200000050008005001c002000000800000010000013000c00000100030020002000000a000000000000000000000000000200040030014000000000300080000004004001c00100080040000005001400100000040044000000c00100080070000000000400000180030004000001c00a000000300040060004006000c001001000100080000004001000801700040090004004000000500000050000002001400100100000014004000000a0020027000000000040010034000000c011000c000001000a001c0010004005006c00000080000008003000000300080050000001000c00600000000000001000000300000050000006000c00000000030000000001c006001000700480010000001001400400040090004000000000000080000000000001400a000400800040070000000003001b0010000000000200200040010000000c00200040010000000000c0020010003000400000000050004004000400b00280000014000000800300200010004001001000000000000000004004400100000000018000000000000040000000004000400200080060018015000000100000000004002000c003000c000000000c0020000000800400000010000002004c00000080000000000000000000040020014000000c000000400000000000008000000c00b00000010000001000000700000050004001001000400080030000000000000000000000018004000c003000000000140010000002001400000000040000001000c004000000e00040060000002000c0000014001000400000000020008000000000b0008004000000100080000004001002c0000004003006000300040030000000000000a000000200000040000001007c0000004000001c0010008000000c002000c0070000001001000b0000010001800400000000050002000c004005000700000
  | 49 => 0xa0004000000800000140030000024001c0050000000007800800040010000010003000200040000004004000c002000400d00000000010004001800800580000020000000c000000c0010004007000800400000010004003002c0000000000000c000000c0050004002000c001002000000000120000005001000000380040008000000000f00000040010000001c00500200000000000002800a0000002001000100100070000001006400000000020000001001800600040010014003001800d00000000038002000000d00000000004000001c00a0004000000000300080050000002000400200140060000004001000200080000000000000000600180060004002000401500000020008000000000300000060004000003800b000000b002c00000040010004000000c0000014001000c00c00200000010003001c005001c0050008000000c005000c0000010000001c0000014000004800700240010000004000c000001000a0000000000000200040030018001000000100140040008002000c0030004000000400f0004005000800200000040004003000400600000150000008000c004000000100100020008005000000000000000000009003c0040014000000800000300010000005000c00000000030044000001800400040010010005002800300000000000000002000600140040004001000800800000000004000001000e00040030000002000000200040010004004000c00100140010000001000c000001400700240020008001000c0050004000001000b00000010000002002800f000c0060024002001c000000000000100000000007000400200080000008000000000300040050004001000000b00040000008009002000000140100000001000c00000080090028000003000500080030000002000400000040020004001000c0020000005001000000080070000004001000a00080050000003000000a00140080008000001400000040040004004000400000040000008001000402300240000000001000000300000000000006000000100000050000002000400000240040000000000c000000c003000000400040050008002000400000000000004000003000000000030000000000000b000400100000010020004000000200000010000000000400100140030000000000800e000000700000090000003002c00000000000000002000000000040000000003000000700300000010001000000e0000004001c000000400d0030006000400000000010000002000c001002800300040040004000000000000080040000001000000700000060000001001c000000c005003c003000400000080010008000000000000180010020002005400300000040000009001c006000000000040060014013000c00300180030
  | 50 => 0x800600000000007001c009000400000000010018000000400400200020010001000000200200050000001000000000000010004003000000000140040008000001400500100040000000000001c00040030000000003c000000000800000010008000000800100000010000001003400000000020014003001c0010010006000801500040060000004001400100000030004000002400000140120028000001800100180000014000000c0010010000000400000000000000000000000e0048000000c00100080070004000001800000500080004000000000700340060000000003400000000040004000002c003001800a00040000010008000c0000030000000800000000010008001000400500000000008007000c002000800500040010000000000000700080040038009002c0010000001000c00000140020004001002000000080020000002000000100000020004003002c008003400e0004013000c0040004001001c000000400a000c0150000006000000400100010018001000000100280020008000000c00200040010018000001c0060028001000000000000020000005000c0030004001000800000180060014000000800800380180018004000800900040010008009000c008000000300240070004006000c0000004000003000300480000004002000400200000020000000000800200000020000000000000000080050000000000000600280020000001000c00200340020000001001400000000010014002000000300000000000002000000600000000010005001c00100000010010002000800600040010030004000000400000000000003000000000000020038002000800600000040000002000800a000c000000000000000040004002000000100180000000003000000000000080008000001000600000070014004000400300100010004000000000000000060004001000800600000000000001001800200000020018006000000700000000018001000000200040000008000000400000000060018001000400500000000004008001800100000020014000000000200000000000008002800f00000000000000000400400100000004000009001600040190018001001000100000020000003000001100180000000000001c004001c00000000000000012003400000340040004000000000300080010000007000c0060000003001c000000000300040030004000000400b00000070034006001c0000000002001c00200080000018002000000100140010018000000400d00040020054003000000200040010000000000800000500020000001000000600000020000005000000a000800000040000008001000c0000000002000400000080000008000000c00400040000004005003800000180000000
  | 51 => 0x1de928e2c462678000000025e200000000d4400007a2000000000000000000003da09c0000000024c911b8952ca9189d327f816c8608200b1d500000529950200000028000000024080a9cc06961b2f1e21709db80004506000000000000000000078e17660000000000000000000669007100c900000000000000000000000c2080003e921c6806d00ed000000006e902680000146c000075900008214849000000000000000087e20de080c00022220402302c3c70000212a43bcd15229d00000338d05000032260000000060f0b1e9550000000049d2362910b800038725140ab7165c37b04178dfe806f20860cf8cc706a91acc6bd49d7182124e21f4413988533544230800000000000000108a13cc2cf65fe08c7000010e20f90c8100002cf40470000000000000000545800000000000000000000004a7526d05a82b3097e800000000000000090800003a1a1e550a387b1009c0ad1320a5dd0e3e8fe80910000000029f4f1d0cf50050000000000000b44000000021a100000000000000000006ebcaa400001e661d2c82c000049ba00003ae800000007748000000000009970aa097e6000000002070000000000000000000234e73700000000000000012db25fd08fa5a842bd9ab347461b10c2991d200007630efa8629000000011c61fb8000032206ff00000a3c6478e120000441a7a70a97000000000d0467e06ed0000511c000000000003514000018a0cb852407631e2c33b239986cb0fa7330a4b90db022692ab41ee4e8b000000003a5c25c089f00001be400000000000000000000bb1bdc08c0e4d01ac39d242dc00012c50000924d00d147d0000081000012fb00005b98cb38fbb4cc07104f318e5e0d5479ecec0800036be200c76b19cf12b81e60000006103288d611648c9c3ecc14d4082855c38601e185671d393cd21f8122f948e1b7e0000000000000005ba400004c700006a9c0000000398a00011d01a31011e0000000000000000da478300002e6c2ca40000000013e0000000000000000000000221000000000d9514cf45c2043c9340005001c000000000300140000000004000400500000060010001000000500100010004008000000100000040000002000c000002000500040000000000000c00000080050000000001c00000080000018000001c0040000001002c001000000000000010000000000c0030004003000400000040010008000000800100100000000001000c000000000500080010000001000000200140000000000000401000000020014000000000000080030000003000c00200080030044003000000900000000004000000c0040050012000000000140010020001000000000040020004006000000000040030000000000400000200000000002000400900040070038000001c000
  | 52 => 0x80000f94194c799cb9e09ec24181de11e70bb536d00f58b7900003a8203790d28000000016ec0000000000000006d925ef0f92000000000004020808400023ea000000004ce000047ce00000001c4b032400003cb80000000000000020bc000033a00000000212800009be9b4a144c7488000066227a88f80000000008263a00ecd83142ece1e9400000003bd81d3c0002612304a00000001f82000027f000008190000859128b000000007f247b000002d000000000000000007920000000000005b38000000000000000000156300002608000058d0000654c00025252a603f75331a32d2544291c33583c6214455e43e9017600005a7400000000bc6813908722a30130212c00008e50000000072d01b51cb600009a186360000627c8be9942204c0000ed080002daa00001fc0000000085f42d0984000000000d04873e00008fc8809000000000001135800000000d4800002d22a9a4d7c4790442142603910ab928d0b3c86484b1045e2c2400001c790544288843cc7a00001168951461498a3434c7c6000021001e1e12dc2190dfa00000000cd4967f00008da0de3a2921e2061088a60000000061e41081a5647f81285151185e3ee46a34a6f827008da0c1071383bc00002fe44f5000004326d2071119bb42da251125d815f15d6000129da05700000000606000025126e28cd624c149660da845f1c4a1ebc271c54209b10000050d04c1a333e668170c3d80000b800000a688000303c43c0000204200000000000072a000000000000000000000011a3025f2cfa432c0f206472836464800021b6186e09a40000000462a36ccf5d82ff207c3440527000029340000000000000001ef80000000000000000001bc23e00468c000000000005d7907a00000000000058c800014680000f2380a426e40000000000000007294d7a1f9a08424f24000081c00000d7023805b607d48f1047200000000242800016972fdc1ffc00015c200000001039000000000000000000000005918d22a3de000000000000000000016445e580350000000113601190000000090d197e2abc7634020245e27f61b140000000000000002f3085200000000000193b000000000000000000074840001321000051d08da000000008afc8f88f53304e1c847769d98051447d1171954726d6758c2c30000220800002799edb412a845cab500000000467110100000000569ce469664000052946241528072662f000000001e020000000000000000000a990b5b000028040001f79152a19dc0f68f360000000000004be000099186878000167c58c52d11e3c0e5000000000000120669c8daaa36433b494e4741a149000081341eb8b8c000099852c894101cb28c0491d1999164a1f2c904897f09b603ec1799fe3000028f861894b000003e107e980004ade00002832450
  | 53 => 0x2b8c00000000000000000005600941339c0000bbc0000232c0c749fc214044060de08df132f41d0000000000b30000000000000002dbc0000bd78d6c17ae0000000000000008c29203917e38386839152a02344f64b600000c34080e000127511a8280c697001b9de9329e4008cf817dd066e6ef45161faa43260d4000011e6000009b800024922bba71346f89d8b13ea0670b3f012d3ece84040000cfb364a78b49c8189c00008488faf127031585a311ce865d0e7e27c0d64800000004c3c0001d67444291f8000000027d83ff904f07160c0829a4e549de338e017b4a938000000066c00001f3a00001c8000003f23cc8000000010c5000000010f013080000000000000000d7895440001f6f000019b84f5852500004d6000023ad0680000000022db4b460000000159b209a54dc78f8abe30ce0000000000000000f04db717a03b920000a8293a4077e000030480001c1c00000000da900004c005d38bc100000000f97a347000000007fd04ac00001151235164429a000000001feb000000001118000182e00006a40744072a75e800000003558000111f92a716c87704aaa800011d20000000016012c008e8ad19fe00f00149c10a21e72eae10b85f70000000042b015293730000000018d196f1f880000000000000000000000000040e8383c00017da390275c470ca46000000000cb480000000000130a0000000053e86bb151e0000000000000000000000000000002bf090549f98dab1d32000000004df1e300000b8080000000140d3250b0809ec6d0c000247444ee0000991093b00000000000000008f600000000000000000000001dfd00002674eca0bfb19060000000000009068d9c8380b37342435900001615391c00005b6800042648240000000000000000cfa000000000a40000000000000000000096f28f01fb4000135300002074000187641e40000000236b182a000070a0000446873344a2828d051c54bc47817b5480c5da8000107a3744433d09613d80c787fd89a09fc524ae000034f0533002a0000ab98000000000000001dba07ce31240000000385a000000000001d9234380000000000000000001e2f20420000b0211dc145018e482e98d811f400008d580001b3a00004ac2380045668f40000000000043f0d3a158a42dc4c486028000295e000000000002f5687ec000000029b6665c00000000000000052a00003a7c0000000000003046cd86c880001f56831400000004c0836e47ef8000000083446ae000007d037a924c9775000023b49191cb82d1023fc81f99a800000000fac8c4c3078796c000000000006668a690000112454200388000000013448270e321d0e2d7801d097000000000000000021be1ae8000000043e24a28000156d00006f14c2d9d1a02a83a6131f98d50000206d174a5491c56533
  | 54 => 0x8059185082cac4768d0107544a3c5ac4a969a7d0000000000000000cda00000000a6a075c0000000044300007a500001c7f0462215ca3897ac24401294c1f80000000314400013b100000000000084300004ab800006b422e27e3883e90a4000000007a486720d4a02bc0000723000000002c801bc3be27f600ad91cb16960000000119718260000df300000000196c000258400000000fe600000000000000000000dea93fc0000d31000051b40000000000081640002433151000000001dd900000000000000000001f040001fbd3ad800000000ca8000021a40000000108e0000e5f00002e9c263509d14ea09e80000c8e1029000037c000000003bb8652800012ad3c421f71063140f000040512b609c0000000006941dea21400000ac00d1b13121b788a5077d00008a404dca0d70306977907a800000003b4c000050200005b84000000037e400000000000000000000000000000e000000020d0000000002ec000000004b890240000140c04bc12e9f371686000001602761c3e3428a539c0f1122000064d85f400000000569000000005d1456d80002e6e35c89e5109d12040000000000030220000000000046f200000000f2700004d54000088a000007608b19cac177213e107b93e800000000000185f31dc72c40000fb6000040b0fa100003ac87f94f1717a6486a1020125a53809662c88a3703561bb67cacb6d80cc3bf696612e49c27333033c4e428c4a09ca10d000022b035e200000000000321e0000f1f800000007ed000000000000000000007621c9200003cb18ca000000005d71e6549ea00010251cef0b5c78ed20a000000a40610b93934c48900000000197a0000000000006ad0eb800000000d27000000000000af72e948ecc000000027ee6740000088c0320000000017fd0000000039c8278000000000001a6300006da46e18000014a6bb4cab82e10ce0899c6f0800000306f5c8e603ed16c01f400000000465e0000e0a800000007df8e4911aa121c7b9527124d1000000000000000000075dc86e000000000000505023b1fce87c8aed19332f2e0eecf401437149e28ec64080004cb66fe4000197136e60aac7ca80001a585881234800000001964a1f8000194400000000d5f38fa0000f3c06ab000000000000968382800000e2000000006250e6f829a262c81ec717154c33569098fc3036800000000000074600000000de99db500000000236002441542ce00000f3c0b8e00400001e1b000005580000be6000052640000000000000009f5a2cf2d8a150c76088c434c400002aa01272a783e38d06866f4548117130b252200000d1038d8efc48b8996446324e444604004d5e1cd02f188dec1ad1c6f36840000c57938000007718d291c9c000029c478299520000741498685e206268f3400023570000000084b000
  | 55 => 0x2d00007f4c67b84a2031e80f01301c7735a6649876695e5063e000000023dc00000000000000035549130000000000005740fff971733f80000000000000000000a800000198417e8b069c251bf63abcb251c6a43e08618a8b0ecc431a805d1c6813a175600000001fdb257400000000ee600fa34250230f7c0f7a79287c9924f0a500000d321afc0000024000000003a6a000000000001b5400000000cd710620000a9288c51a5a39bc000147032160000c9a107900006c0c00001ea00000000e36000025ba5c5000002e600924f94c57000000002a8400000003a5e0000000006c3136621c0000f0e28b279d0000000000004bf4db280000e7a3f9049100003fcc000000012af000068b8dd6a175000035b8a4b81b000000000a4aa4f91c620560feb98c4187c450c3a2956c0000144060700000000000049b8000000069b80002455000098e1258989544a040a03eaa5582d6635540000d9b00008ba0cb8000024f656d49931b880000000133490ee407a00010f7000000000000ec016390b2c000000000000d360000ab09121000011e499e0ee81e5613fc64a926c45781f9cc8b8a0b29c4490c84f128631e42d311b8800022b00000000057500006a5400011ca43847548aeb890d1b384f780f412ea07d233e02792359274c20b4a89219134c044089ed0c01321200011df1ed601d0000058a800049b8000000000000d5881f46c720ff317e587c5bf05f9000000000000000000040a8000000000004eb49db10440000000000025430000862419300000000000000000003a5448b43bd1f69000015f875c800000000000c5880002904000083a894e3efa7068982a3050622721c70b0cb9239e17d4f6398e7130605a43eb8f3220720000ee2819d37740dcc37d16ca0000000000000000000000068624180000000000009bf1484167c00014dd00000000b5a9e73371e10340000c5e1f5c97f855a9d2348741b300002634000022200001679372a8b401d5000000000000000115036b644f000013cb00006780000000000003b900000f54000063a865a18582988380c00014ed160a000108b1add024000000000000000000000d3000024540000000071246102134579800000003330000150f00000000b68800013305e1400021c847060eb08db9e4928ba67e8bf5a167194000006be25114a880e5c00000003bd60c945b9a4f2380430ecf2025e70950184c5d4a5f246cc182c875827a42d44f4112c0b0c390804d40001b3c2bb86230cb1841f00000d5060c95e10000000000000001cd8000072f825c26403908c96a40039ce42a00001c8a0000679cb04257308a07624a7580002d16768921b1cc8036621f13201bf035a271e4594000000000000a070000299486000001c8c32885f5506788b52c5641a0c2ba0ef0ee82ad800010b03b642e
  | 56 => 0x2260000ab9000000007d411568000000000000001e8100005aec00015c312da6ae04170c274b8a0000aff00002426000071f00002fd4000008d800035081be0000110c2132255888785d7455e8ea44b1a00510e84b28000258100003975313839c00006890dc8800005f253bcf18039b00007f449f48d61057e91750f40d29048e558000000000000000000001f02cc400012061e11430414802858d94000047d400000002bac0000e6b800000000000c1483ee000010750979d330b00000055b80004ca07d68000000005a27f38716878131de2f902e20ce51e501014317a02b000035e0cee00000d260c0451216554ccc130c0001aba433020e8f8b965032c400010958ce3274a4d6c000139700004660da6800032fa0000d8f19bf1e5253603f587f00a8071ed08585df000000000000eb2000064e92139ca809a6372401e0000000000000000000000066d428f971821c60c4000000000206000000024540000000000000002d684494c981d8847c233284ac932c25242e7cd3089b331108efc4a18fc31f68492006306061df63398503a2330d48000014e2665000092400001503000016e800000001afe1ac00000000000010e00ea02a60000000000018432d7e1e2428a0a7400001a0cad4873c16e070ecbf3904b21e62710698119e206c0000b4e0000334e90f8ac2800000000bc400000000a38000053c80004a2600000000a1100000000000179d4c740000bd4000002de0590000168e00001584a01229e05a6000083200000000000000006553da8000000021cb44ae0000000000000003140b94002700000b146ba193e20260000cd69dcb00000001311800019a800000268a5104f215f40001d742416644000000002f0c00001000000061c000000008720c480000c550d1919a4000129a891e00005024beb1cb400000000893000020c4176400012162d4800006480000000094984051331159a1f6c75c1f104738421800021850c141d2822c000000000000c3a800048426964a648c80000000012dc113d00002918afd8000000000000000000000000000000000392c3a145718ced295c825848b00c5374e895087d0000000000006da800000000000b2d0cd503422e550048000485e00000001ca63d64900800000000000000000000003b0c000055390a30f24000000000000000500ccd0083b1e182be9029901742427d8c55880001c9e000000000003b32000000000003ba8000000000001d5667ac000166c3da257000000fa80000189513193e420381e10c4c80000000852c0000000000000008690def266e63040c70a661d08933c3e0000026960d6000008020000000078b18c2000000000000000000000008391e8c00000000000000000003bb83a01494000032f00258e470000000000000000000631800004
  | 57 => 0x41b3ada367c000164f000000000000000074a3f6800023770fe80000ba080000000829c000000045f80000000100d00003a2c000000000000000000008400000000c9100000000000085a8ce73f8c0b24aba139b358076ed056153b18d001048022462244e00f476a1c1f48b04468d8891bf475e5c100001f3000001a5000000000b2658140001052000000000000b2d0000000114e020a000000000001ff000000000a21986c000000000000000000054c4e01a16009140930000000028f856b4b5f23940a2200000001d3f052a34d012a80003800749800000001eb800000000000000050100001efb000000000000000013a942c952971500000000000000029e873240000000000000001e58c6b00000010ebd9249000066d8000000000000000a8488bb07700000c7b80c8000000011fe800033043d649d79ea13c7a2ce521b88ab1a061610000000042aa56084478123080c61707fa00000a2a4da4a7807830000480407b03550000636d278228a0000000000000000bfe49641e406503e5043fc000225e000085cc2de00000be20e9843b84692cae6458f1c8171383c6bd918e8053000048540000000000000000001f383bdc26f044b9a0411d691ace18a1fc4af207681e28a6b440e4974000242d07a000003f996cd309607d0afd000000000000142a3b04b2455dc000048b304800000750ccf00001d400000000278c28841c922ae0000000040d1f291c88000000013843ed40000e5f8000087400005e991f635aa000015824ab00000000d0e85da000071f000014b90000096c000085800003588000000047081a280000e3d000069e400000fe3fc82d9515580002fe47a6800016c803be11b800000003a6e000000022710000000000000000000000000012ff08c0197c699814a376452700000e5300007f400000a3a00000000ff88000000000000000000198234906558000000000005fe90e947e63e7805e123d354a1a08b0099032aa60cb0b07261e3b244154000000000001a60000000000000000000186e00000000000184946d894f85338000000000000000000000068a4000000005e8780d2db9fb52a9232f8508150445260000a490a6f3c9606a8ce50b9802800000000000000000000dba00000000000117500001512220406100003afa0000000000025aa4104a2f0828146c000000000004b004b0864c9c054372596400002b2000005d0fd7856900006bacdbf000003c0000000000000000000000021f900008ffc7a2800049400000fa081a745a656b00001fa600004318000082c3ba000007ce80004c128c2c3668000000000000001e33000067e0000000004c615100000000127a00000000000000000011c50000124640e00001368311216d0e370000110c13c400000002d4600000001ae912c24a0822d00000c500
  | 58 => 0x93080001c5c21d473d84f68782160817f10d013c4327096cc5a88f613b400c28fea010a17b0532035196330dac940ce1198d03af084643bf175d075a611c000054f000000000000d23330600000000000098a000130e00000000000000000000d905670000143806940978000025100000000dbc00003b7a19f8bcc0000000000000001b7500006e2ca20000000002fb0fcf0de542f46fe81bc878d3f366704000203102a20000b3780003cec1bf09189552000000012040e763f9e00004178a250b2803bc000247c3b720000000000042b2000000009e6000000000000b5700000adc00024451a2600500000000000004c09cf0000204096308ca0e0200007bc83dd80000000075c000188e2a7a000123e876e3740000000000002e4487712e400002316000000000000000000116387f1388a0000eb40d900a1c00000002092000092f91bf800033260000efba54c090c6c5467a0546229000000001c1900000000acf800000005ef10b2963e3cfe139c84397a142a80000efb00004a90000000015830000862c4a8000000000000ff500000000000000016c1000023cc451800000000000000000019d8341130122b13c4a2d88d6f032e1a0c08d800004001ab40000e2882f216484e3452195172af04b7000000002f8e3f38000005e00000000a3f931800002414e7100003d7228c40000000000038440001a7803b89288aab9cba0f3e8edca52189d0a588be811002401e7c32901e0266b1c0c7be07c5800000000000439800031a881fc0001f7500006ea8000000000000000d2b80003c0819300ad16580000000101805fd1b44966897d0000412887dc78a994339786144000198f00000000c29032700003a6c53825ad010c38d4c0c8000000066c92810f4417e44158ca3044000005d9400019df00003b7860e225f3020169000000001bce7384ee5080528b07f1c0001176000005080001b860000526c0000000000090a8137a33e0bf63a5427a8000000089100001ccf4306000085484651ef44b503f5106e2da06a4896200001d225234000000024ce5f00758000000000000f7f90bf45868f5d1e9246829627d0d0c623e800005da4000067424c82f30ef7823d05804d845baa38823d200010288000000000000bc953f41a41c6000014f5016c0000bffa5741dca8e4400003842b7a8150bfb800000000df4e2d800001e600011268000000089f4f3a832d000000008031093000000009888000000060dc00017fc0c641fb800020dc2cc24f04000000000000000000130a000000001168000000000000000000000046b0d3d00003b0459200001e8600009990000000000004c50c0b8000346e43788590000000004683840c3f16ac1d4800000000000207841011a12ca83e18000000000000000000110a00000000afa08b221a827150f78
  | 59 => 0x680000000003fe000000002360dcb961a1d664a21146800000003138000084a000044bce17a656000024a4d500000213041a8c0f8155010a84b8f2b0f6336b84b487131e4f1cc60ee920491cd26c6259c76d880400006bfc547800026944c4ca5e963d030c2c185f385ec3ee65c9907c14f811ea0000f2e0000000022683a6991400000600e7c80003a780000000214d47ec97392da14ec49e627787b408e1000023050e482382760000000000001afa94f400006e6479e00000000000466a005c0000fff1b780000000000027181318000000038783fe08b7194d19e00000f76800000008ccca1e80002e705bfc18d96bd173839b53030f621ee86684000000045284af0f130000086c59c40000e3a0000000000000000e6e000116ba59500000000f5d1d9326b284d1160800010fa0000c74000028100d5c5ca0000000000000001253100c0000fd6a181413e08a817b1976000076d03ba9c100000381c0001fac067e1d9c0000c7400004ee48609c354bc8000000000002166423926b00000000000000019d40000910c000000003721298000000000001d44225a6670000000000005e5103e000000000001d1a2fd05648000000000000001b922056000000000000000000125b955f0c96000000000002f628290000091b2ccc4700ecf000000005d304921ef4000014dc00009f70c40894875525f437de34f09351e5500006bf800007e30000311875d05b00000000000000000000000000000003c9c5d64061a4f4000000000698710000093300000000000000006e69fa91858573466d9c5d10900bf8000083637f681f8ed217b600567fdc572188a0dfc000129613b82e0c65a809512a425ae27c472800003f0200000001c72267e91dc66d03b91e1689f82c4a20900002f3c05500000000078c451180810d496a9022830f00006ed42af0000138200000000a041f6e0000000000001e26edc8111d96000000002c2800000000000000000000002d7c000000011740f8c3088f414a026f28ac4034534ec68b40d59e87000000006bf00003cf85a4c73b8000000000000ef00000000000011b80002d440000d2f029800006ff07971f65366a681800000000000033c00000003692000000020cb21f60000de31272000083689af00001b42143c85d25ab1f8c87b52b6800000000000000211d174a000000000001b2e00000000000000052e000013a32b6c00000000000000031a4000165118040000000208000003b88000000000004e0c0000b470b14547043d1e3725cc7dd800000000a460000c7300000000000000000000b4e31080001b3e210038dd20b800040d6257931112691f14679485a07c4000077e0e5b800024103d9c0000000000017ac0000000000000000000000000000000001fa036a800011c1044e1fdc00006b9a5e30000
  | 60 => 0x4e5000005260b710ef87f90ab492c0000056e102263d4000193c00000fd09e8953a49de4788e1c0c850144574c8ca832f1a8c7c98ba8a3ed0000086033b112a4b721bcd1f793ce3ec06ead0140b182f54016c64200162318000087a1d6e13c800000590000169c7b74cca86a2196e40b8ceb16cc133485792f3152627302698916200f05c490908aa07ab201e34d90031db048601674000069f00001da8923185a073c1b0c0000e9f073e8924e3a95922d081e1cdc0000000000000a6c80000bee0000000180048a64be4987045247300000000241a04a800002ea200747b0000000000000a5e04c8bd91307433c1c240000ac30000000000000002bbe00000000b1e012c0000e7f80003a620e886a11aa41e2e53949aa09cc076a56945c00809037654300000000041654340000000000000000000000243e000000000003050604800000002b480df00000000000000007c3800010f20000000000000009684e1d0000000000003930fd6000000002e6000017e22f78d44000000004f4825c872e054600000000000450c00000000000000000002f400002cd699c0000000000000588000192b33025224633857612843ee44149340000053d80000000000000000000a40235200000000a5a0a5212d8ab300003a6877cc81880000000000000023cc000028e0000000033200000000000000000000000141133a67a98d668000324a4054723186a00001ff8ac494c000006fd4408000000000000000000045b000007101ef60ec20e04157149d20e80000000000000007ecc000000000008ce0eea8000000000007f902820000878c000248000003cc400000000000000000000002bde4ac077c00000000000000016ba0000000085e0000000091989e101b11570642099b02ba44a625f06a98c560fee00000ec96f9469a7f2800000000000000096f000000000000b1c12513b380000fb61e5d0000659000000001b6000002398c65000000006d7800022e00cd092b0b091ed200000000000031800011eb25203f9a0844377120e2e46901089100004c027d5517692d6015036b84c91b9f000052fc3ab0727354201c0c8914412b760ccc69a892101ae0000fc91aae17200d24ea10bcd2c065c207ea2578008476bc00026580eee789c4c092eb3d9a467c1fd16df30704604614105300000000000000039328db8fa2a0ce04260000c6f000002da671917aa5e935c667a000009a7000017080001a0827320000000253c27ec7ac4720a5f9283a5df118c8000290c8bbc5de80000fbe0c2c78900003a563c4cc4580000ae40000000081203dc507800017461aea0a8132189f629d055c4000014532f8000105686bb000020207000e741bf0000032b913820be419c000064116a417581458000000057f44f3940736748ff893ea52d1b6e9064775
  | 61 => 0x1c4913fe49bc7b7800006dc000000000003aba00000000548163e06a40000000283297c00000c6d270a70d8000000000000000df3800000120000000038c2f848e1c7140ff1000000004a600000e5800011071a424c7a83f881d0275108c01d07cc800034d02f6854f0e2400000000000000000002ac000000001cd249b4bc3842c00003cd00000000195e02b40e98c360dc80000a6b0000000000012b380000000868c70c00002ed80000ebf20f000002b143b6800000008f94000232138bc7908435a11e025c000022b15e700001d54000000002d000000000000000000000000b2a3312059c6c0a31e0b9c26dc21312ab2a4468d532b87760c9c00000000000000000000000000000004e0c93978812280df804487da000078d0559800005c0000000000003a365f48dfb11db00007bbc9dfa2001fd0000112e9c58000057600000b1c00000000112141a49fa90ec0ff250913ca000000015f020688af90280000000087600001bd400007d387a902712f160cc11538000000067a49a3172f372c0c54fa392650898493800003f9000000008a6800000000000b1b8000000000001ed800000004441284000000000000000000000000000f6f00002d7031652de25281bfe2b8078a206e02d60e9cc851904192e2aad25e16741caa58b80000849000000004bd80001c20000065d1185212e83280000000000084f51a1861d000000000000bbc258c000000000000000000047e1f3c467e00000000000000000000000000166c0000342868746040000cd880002e22407c618000002ba3e6c0000aef014c9838000000023c26ec4a5b00003f2c00000000000000000005470a551ad281b0643a3ae082e00004ef9f2439ba13f914f932500000000c0280000f54790518f80000dfe70c80000b31223a00003001b4020ae5dc80000a321eca00000000000015600002591f52000000000000c0700004f54000000000000000af71a6c00000000000000000007ce40000000000051840001f1138e837c82d4800030b28e94000249600000000000000000000000000156b1f846d601c100e600003614fb5922529ee46ccc82a246000079c92569114000021b8a358000303626f908e000027da0000f9518d3471649dc00006e9478a078400010f609c45b1c0000913262a27c83cf1ea70bb670b80001d6506c693600001b9800002988000022c000000000000000184a3cec000055938c474c00000000433a832000015b706fe000131500000000851400017804a5e00000000000229e569872e1abe1440645501c2547486280d89d40f4349a0477471a056817845c48f7516183abc4f145df830910304d352aa9dff00004478ddf14cd10b20000eab151144f81fe091f80002f4800009eb0000358c3980bd1800037504bc00000000000000000001b6f000
  | 62 => 0x9a7960000229600000934000000000004e08bef0000000000001c4a02d396c3bd403680003ca2000000009963402000000000002cd2980c8818ce41ef62a5c7bf02d021769934c6b0000355a5cb082425463c007eacbed8000000000000000979000000000000ac6000000006da1c6d072c803528a8000000000004f79ab1000047390e21b7f0d201b752b123890000000057c800000000000fc2000027ba0688739000049ca848102a8000000040d4f1c1b52000042312d000000000000000000003ec84980540800000000000000000000000000000000028c4000035f0e1a00000bf08760a8000008ce4f711610316800000001b83000000006c3a49f4bfe6a5800000000e2a6eec9b0000013f45e04000056225200001051204f00008a3c000000030543ef400000000e52797885719e44c8e6e40000230300003420c908000000061180c998f0132a49e87b5000024246748a5307ce00000001178800000000000d4f80000000291400003912c84000000000000c3647b87e680004ad66a2c000000049140000000000038105720af500004cd000003a10a5719a600004cb897e26f434dc3590a0d2b7e0404fef0000448000000001ae13c505a251f4926e0000000000000001dd243b400009f4210400f8000248900008c94000021e4a64706c000000041049074e7323c318dc00009f1176000007ac08958000136c17207e80000120c7e0ce2f80000000347c51a9f9102b20000b9d11d5214a1254000135200005cc0b9e988f000037391ca80000000000072723c60e7000000000eb500000000c3e8ba40c04838922697b00000000014b00000000000000025421a340000903000000000000000076907347efc0000000000087507510e393e2400000d70000000000000000f7d0a12000038a0000000003280002495000078f825f80000748947511b8b5837b41c4c8f7800042ac043855e87c73cae0000ad025972fbe000000005160c0e875818e00003ca0000000019f5000000000000039000016e03d810ce3c38687cda09c9f000000000000000401872b4000262c3dfa0000000000045000000000000000009380000000000000000621800000005898f818dd3000076f113294fc20120001126111144301a3c00000000c581834000000036b400003c591d610ac0000e4ba1b048d8234c00005710ad45c288dc00eb448430e40001344000068600002291325c000025d00000da81bd05a982ee1a7c001800020bf0000000000023bb000000000001e5300000000000000003f669c000000003dc215141b12065086085081d91b3b28d000010be00000daa1dbc09c86df32da00000000b033f62809013f0b3514e48ad4ca01f5318060000eb52378000000005f809c23c16000045b80000000224c2f39e600ec092e84998cf20000481400
  | 63 => 0xa0800018be1d7c0000f0946ea0f60bd29d5f28d87de8a9c00000a561b64e65800036c67700a8f993605f47e4c0001be4000027f80000a441e9e7150000114700000000de58259246c0000c06179e36d896f8948801b00009528bff000000000000c7e800000000000cf7a491000029645f5000035520000c2800001f2200007d0895a00007d5800008a413c21048000107b196000004650000000069ac5170000415e3ec42988bad3464301086601150e183105042235d0000000000004d42740000115e8000000000004ec8f1e239000000001f152dfc45052d909040a5c0000000209b00000000000000007fa00011a7a313006c6c08000000000000000000165b0000000000000003598656400017c81162215400000000000000000018233c280000000127f107c000000003903a100000c9c8000000052b48681ebf00000000d9680000c8050991c7a50e000000000001e6a2b980000000000000006ca423f00004a487139074993124a803700000000055800005a497ba3a202c748af000002220000000000029f200000000000000065cc00008340000690000016b0285400005ba0000115000fc000000000003574000000047540000000000030fc727400008d2480600000000000000000000001ec8000055c00000000127e0000000000000003dd878000003e7c0000c42800042f64f0c47ea517411a436400000000000000000017cc0442000000021d200002af12a90463000047b009d8000000083641419b9a07305cfc0e88df900000000275000013b6496c00007fa1cd000000001c8300000000e9b0080000000006d18000000000000000000000000000000807000000000000d8b05c6355c017981a00000001215936d1002797d2d4157f00006314a5ba476168a2b552e18ccd000060d8dfa0e62000072891848f6b16220374e2c868e3b7e0000a7e9c2b1d908784d71142b4a8298d81250fde45ee66a893118e328d2400c9da999e032e6298f0784030d963ea8c0ea50634be3e90a738bce0000173cbcd09f3085e3c443f60000458c3eb027696ee25460000b849dac437a67b80001e293100354869e9e0a14e691d4db696820ba60000000240f2258023800000003dae1a700760bc80000430865180004106000000011f3008a5fb00001a26000048cce1ea50505da4bd810b0e7000000a74fd1130c0000315c00000000000000000000003a86000000000001664152c000094b000069a516400000000000000015590000255400005c1000047440001e9500002d8c7868000320e000000007720000000000000002bcc97942691a3a374892701d488fe49a482180001a1500008804bf9888d335c8570536192943525640a1ca163267648f08b99c9e00000000ead00002c740000000000035122524f71800000004b3d094800043
  | 64 => 0x9a39ced38680888cad84a730f093186a00fe500000000ada15ff31c274300000000102a000000009bb130a1184450800008e8519d0130e75022e69bd25c953335363a7466c127800001850ae58000017e0000df40ad81d620000000221d000000000002151290a63d910e1371000024743061a663c88718c58b058700247824e24058b49d62aec00000004b8067f45fb0ea700001d8c0000000000080a8000000006d61248ec70b260396460851c800000000000b8b0000000008f0000000013580000000000013400000568a49403cc5118a1820d31d4c00007d49a6746fa24210760ecb000000000000a7b46e400000001ee6058e000000000001396769c00020a10000544c00006b5099800000001d4f00000000000000000000000000000043bc280020080002d0a00000000c4035d88b700000000287600000000000489400000001da8191a2720a63809523fe000047700004bf80000000000028884eb000022d900005144541157e0cf60000e81000017020000000000007d600004dc0ad700000000000000049a60000000000019dc0000000000037040000afb800026f2347800000000000000000011d73e284538191800000006904dff1616166602088ae871d00a22a4c5d30a0e4792656829525e1000018b4fd70bed3a144a1400000000000090d259063d0000000004c800022ae00000001d3d3a32000000013511e7213b806a0000045000000000ab436720d3027e000005f60000d7280002114000000000000000139800015290000000000009572eb6670c93a9f95000069c4000233425962f700001673000055380000dc4000012140000000254c50f054e0e130dee000000022064cde071cc1a23a11ec8000010d82452f6e2b58f4518cd26cc69f8b3b94454c9251e91378573358a8958226928006a22e7472680462ba800011d20ac41834819c000148a12685684eeba58b0a7c0000f2d211809c800007bb8000000056380001a8f297698940001db80000000015a800000008e9d0160969301414f00000000000000004c598a0121200000000000000073c803000000dd0217516d0000193a01a4c3a0000000029b40001af9000021440000000000061c829c844f001a2094761850c1d9c24b53199ba64ba8790cf5a00000dd6000127683e018480000fd912370aa680504bc24ae25828a641a6800014600128000031600004a10000000027fe0000000255300008dd800000002ba40000aa792834b1c236860e80000000000000000000aa0000000001754bc4000000000000000359d2d89cae00000000c008f57194e4b6d10d26554c9c6348182947b0b0400000001b2f17361d9104d1956000000002f000000000000000000000000000034e8f25171663b0cc9000000003cdc19a99ec17a0254c0000000000037046
  | 65 => 0x1db10b4044fc2489a75000045080001ab446fc0000000001d00006114000000000004940000223c0000000045f94c6063c44cc000000000000000000000001148e9800021fe411800000001cee0c0662e900f041947f262e02b0000014b0000113c8eec000000000000d00000000001620000000000007d90a052eda5f345a3106c093a2fa49c484dc1a5c13081d89153009e3cb0afb05d1049e07880000000246000007d0216b00000000f268000229600000000000075000006c219372540000000017d30d9e30993130ed7489600d00001e2200003fc0000000009fa86ac832874142905d407b71cfa14f47d50991a039315a2c340659b50382c6bc0ad584c40394000106080002e666a649938000041e0000000000039b000007f00f704a8074506e40000000037f0000000000b4723c00014c500000000bd48000000000012b50de422762d500002208087c6e74beba566370e839d07e264829967c7cb72a2f8065426b48988fb039169294c5399e62cbe0000b408fca2ec665b8b3b000002e67d7ce4a00f40abe000111b12c729500000000021200000000000000000000000000127e00008c690378000000000000001f40071c0000bc8971d40ec000031a037500000000000069216fe268424b1b3731e67be52ce05ac3782000000014050000000057b000000000000000000042460000de78928333600010890a2700002f24b6ca6212a840000dab00002e00869d12512b9000062f8ead800038ca0000000000000008acc0001519368a000109389fb263400000001a51352636180000000000064d40002447000086b82a722e002660000a2e00000a8e00006fe935a0000000000000000000000000000001a3074c87c00000101a000092d1bac41d639940000a4d3e9e000000001c52b640000000000000007348900170d2102505d19e0ff935de00000001f4800000000df71077000095f000000000a7e3e882c705012d860000df50ec047a88cd90e8065621100000000000000000000000000000004f8d24703f53e2665940000000000000010a707b600000000761000042e20000000046b0000000101f000000000000000084f0000000021500003bce693cf7403d34ca200001ffa52117802e489998c2a17942a80ab3a2f30000523c0001d794ac64bb90830000000000008200f51335e41fc000000016fa05a8fcb883300005b3c133949631225308000186b253e000000403cc00f057a40000000452e2808357800000002734000000000004e70000000015580e84000000000000000308000000007358000000037188b5800000003dfc35e8868a22d00009204de400001b10871c9250000153436d80000649353c018c63910ca2c2e00009109caf00005451233859b18aa63e4f969a5d4a5c09111369c7a1e4090b91a280fc0
  | 66 => 0x97440001456230606fcb758000000000000000707000000000000f24198e485c0001e46000047640000000000093344b30000000092fcf83000035943facb751e9200000000d930a3f2fc20000546000008ec58940000000000093e866b00000000000000000000000079d0e7800012ba00000000000000027700000000000000000000000000000000000000000007fc4bb8aa915b40000000000028965e4cc648ef61b3400011e592ed14a40001236a5711f1829b8eac135c3830000000011a500004b8449c25f1021800001a58bfe2a5400010c393bc1f1000000000915177c2b98c411e1e038c376497a9f7f394e0000000232b34460000b5600004afc1698000000000000000212000000008da4000000015bc0000ca08000000000010cf800000000000000000017de00009461960000000007ed800000000000000000333ba000000008bc368c1d4ccf100003a4a06a000021ea00000000000068d0000013116700000000000131d8000000019451470d220ce68e781c5a1b527de56c448587ac2dea12800001f0401ac923cc04a1f32ec80000000163400006c3400008604756000000000003f0a8224922800010ce37d4d8b800000001c104d90f471f2c92f477b9e1a0e1a0000000128b3a005dc4000065426f600000001eb51f7c000000000000b1000000001d6b49f814986000000084a6f7400000003ccc6ffc0001e152d5e000018303744aec2b1c0000000230c447c20606c046946b0d0478134091a455800000001dbe27680e91ab63ab80000961800004180000000000000002cac000000000006ea40001e2000008f8c6b50c5221e48bc0ea51b9400000000c90179241f4000110f04450bd24458c8892d30f5a000034d000041aa0000b208baf00001cbc6b7a1bc32586630afc909b000062a40000d1436ae2f14360a01f471c0e751b981962186000035b00000000000000019c200000000000000000003f48d1f929800043d583638000477a43952560328120e1f2800000000ee08f4c68288d40dc077e8a85000100003184e6f160a00000b68000000000002ac81a387352a72000016c0fc018b88c004c6000000000000000000000000000000220f0000865128f86174b52000088999bd000000000b60c6f000000000002102000058b08398000494600009f3800028f24fb820f100b00000000fa880000000000085780002bda000027600001b944d40cf99f3d000068e05770aba0000000004d80003616000000000000000992c9e00000000000000001e191fde16600000c1b00005724e0309ae1a76446d2c2a11100265c0cb7e000000003cb4f9295c11392301921f80003e0278410eba61801188a80fa6056f0000000131721bb0e4849e4f379e821f1a66d0af605ee359e937cbb98f8900000000
  | 67 => 0x931ef0000000000001bb40c803eb083046aa0000239000000000c34000000004e887f461d0000297c000024d017a00002c28000174739ee205c5bb9a4e309094687fea061221c3af12f996902fc60000d23000000006204113800032360000aeda390000000003d30000212064bcaa2a2b2482090048d01f98101c86e8b4f1a1a2d5488282bc97dc3f28827097a15442dfa4aa81d186ae374a0d648701ec62264247c000000000000000ce400000f8c407887b8f50047e000097b8000000000000000c73000017e0ad111620c4e3550880006a37be26d0e8180ae01c60000e2180572a940000000000000000fd8f5980004212856805d000000000000e280000000095a0c638000176634490860c53000065402ce012616f8246458a0000000069dc4988a6507f60000b65a587306422a40940522243c13349fc8208000000000000aa600000000cc68b481f660000000000027f47b541c400001fb21dacc26a6240000287435c9dae000050e8b9d9bc0000000000000d0b00000b5000000001a2a0000b27000005ac00005c51b1603f2219013e9e9729c6898457396874c2e00001e78d38112000010e89f4b00008238000013c4a7e55002e1961c026c000054c000019640000000029400007decf8b11f73cd87c20fe125ea000059742252527496a00000001cdb15be7f648ec018d1a2e471c31b86d000000680b319bce00005b74dbb80001b8c000130d93fd2f3e087020e000000003f84000000000000000b8c84de21c85b0800009f800004f991cc849f30e067e407c800000000000d7e838a28ca11e90db9d8441be83a80002205448275889688711071a8a04d57800024b846bc4688f711046249491f07d828300000f49a55c36143664000049000006158f62827f3642409c000195c35f07448b39265f00005e1027ca1be3c5455591399bde3b9c7a64136250a22ee4044de192be2afa31e5121a5d6162021409b21d0b45e40000000047c48ca6aecaf589e22c860000000000026ee0b7c86b105a10f0436c0000000000000000001df0056667b4eed09511d8a28a8000000000009594000250019547cfc6c124de00000f74f0f9e5900f88490a26a2fd2d144e1c76c89d109ae68d00001c091200552c8da8e0806646cb80000f9f1cf064a8dce036c32967bc0000012b0000133c00001fc06303c2057ea23a00005d84d9f82cf000034840000000000000000000d26304c6a14000049e3a08285c0001466084e00011da0a5b402c1b4c0000c213cd65cb40002228000000000000000000000000000000167600000d780002f9e327c000000000003d1800002cd13c6000000000000cb4000038100000000520c00004d000000000d75059238221b0895b00003f8000010ea8e6b2428332044f22aa00000000a77000048c800000000000
  | 68 => 0x89c80000297075e575494f078a0f5e8c700000000000000000001fb6263297b077f9f8742625ef910890193634105800000000000000047013c71daa00000000b0130da5d200000000000087d10590000199635dca0f9b64310c0000f9b066c00180000557830c0000000000000001f2e7514000000000000000000119310b40000a5a80e00a7a70fc13581c2066c00007621c93289c83cc85e8000152815550ee9c294bd60f2400008e7300c0000b0f000000000000e7f0000000058912cd800015720000000010600006870136855d4ab401b8d7019873aaa678489a800013f22334000257a11cc4ea40000000000097640000000348e121c94e0ad42b2210a03d207250000074000019494b847c74f970000030289c000026522e2000000001b663f3e308c0000635000005240000ca1127200007f31b3d10da6ad400000002e8016dc3ec8000447a65a00001436124c5a58f681a4b244c000016181571192861000000004c0a461c00000002c1e00002478cac000000000001a7b364649340001cf3000046105c2800005d81d6c73c8b07144629286f59c55000000000000124000000010ff80003502000000000000ca4606124b9cfc00001d6115080001c8600000580e1e0000513d2df8c22432a497c00015ba2f360b6cac798da000047f800000002a2a0000000182f128e4038b04800042067b2c874000003109640282000027e20000dbd063800000000fcc80002dae46e504e8000160065e01c3800033fe26bca59842b1dd696252c301eb1cdc47503980000150a008c00002ce062e1f3c2a680003dd65f14000000000005ca918b800029c000000000000161c0000964800026480000000000029305874dc980000af05fb40000000000000000000000000005c0897000039d8000000000004bbe5fe916a00000d3200011540d8007bc5864d98011200000000ef68000000000000001b4400002d9ccf8a3b82b5000000000000389e000000001be000097d924d1f3b0b4a91e50e1a1740b664c7427580001a4000005c321ec00000d0c000000012ec0000000000000003698d4b8000366810683250000301c221c00008db00000000ffe800000006e787b609a82f860000883172000007084dda06dc37085d103fb0000000000000000f920000928400002e900000000e551ceb44f000e0d4e0000177000009a28000070a00001e7211300005fc464a23812b3a0000bf780000000953d09d81a5073206dc4330bb71ba26b380000331256484f12058000166800006e01328320c000000006672e7c6530cb58e2c283873c08a895ca40bc471800018fb3c482d3c6ca95cf1f827a60706206d00000000000195d3d94168c7eb94fe39203bc52088ae8489e00000001d13234c406c21b92b116c247ec0000000000000000000000391297e
  | 69 => 0xf4ee200000000648c9a784110e2e000073d117f00001ff400015b8000026e92c6800029568f54a5088960000000091c00002f140000000000049b200005a50a6100000000cb3000031da0000000067a2f2a03c0f36a3223b4a4be0baf88d60000718049a82d71cce85c80001a5500cc09ec5cba629218e155cd938a1622be685c1a7a46300ba5ee0d5f83f0379800011a70dcc351404003f7833b000000009642594000083e42c192bd486818fc000000000000000c55800019b8087ca4592070000488c000176e05908c40ec19e022b1a86d000023d93fa40000000000000009768d22093000000000000208a4bb0000000000001e464e383fa8a2d0000000044294c321ce0000578000e000026000000000000000003db8cc31fc65c09300000000c87a88000000026043d6906b00002742715c000092b35644844ffa80003c2663f00001ec010d831c4697877f455295c0d3f9b5e0cd4000000000000cf265d4000000024566714000097146762930d60a3491eb0620d1731d5000002a40c1991c30000257cf2902e70f18000000000000548118800000003e36751c2e685302d6e7af40000000404e7f74e638000000000000000814000080c8bf815f20844852800023ca000000005c882bd2f884dd477000004b3e000000000000a2400000001b4e225a1c0cb92054a499000000000000125409040000000000096900000b1707c44bf83988dde25528fd00790ded00be90a12ae85d010f60310df106d7000080d056800002de600003180de300008350ce5800044d098291d9000048c25c309c996404674000067984551d3431900001a20240492a0313037700001b600000fd522de00006f3028f356024488cc87c52ab8000111c1f2046e80000223800005bc8ab000023df00000000000000000005de46bd800000000000ccb142000000000000000014ba9080e398c5d0cf00000cdd230d215418e8f0b089d01b675f11149756049c0000acb8079000086884a40303235c0000d0ca07508ae6ee42f984ad3b46020c1a7000000000f44000231204040000000000000001c3c30b1f611d6e4e4800000000000000068e80003d3698a0f0718b3000000000000000143c6bc80001794152248b927711eb3f3a28ac1b789993df8987cc5d9a48236000006a50000000044dc0000000000000011e0800000001adc25e828639720000ba78b7b023a000099d16a941c236c400009b000002e3408c000000004cac54500002c6a6b98c27248630049088d8c0ed8160400000001ec100000270000151b0000000000003463ce20668b62000021ba00000000000000037b1117000000000000d0d89ce22802ec0688800000006ccc55500003eb800012418ea003900001199126600000000000000015c41008000000028520000745000038d20000000000
  | 70 => 0x152138910875180001b500000c8e892c00003990000000000007aacced87a3000054b0000115a0624000000023a80000000000022b82eaa136846aa53718f400005eb0b301e14593492382dd444800000000000112817786af144935a858ec9eb91290000549089a1a4c19160924000000000000a6c8d68c2f05b20000b839ef51f6a227000002650000000000018032e3c3c68000000003ec0000f4f80003d6c12ed08400000000000000000000000000000025ac37c21c040001ed32be2000117d80003f1000000000ce200000348000000021800000000199c04842774719a1c100ea70300000000000006d867e88684ad2000026c8aa200380000000088e294065e4e388dd416f2000041e83be02520000c3196b2102c0000000000000007b90000163247c8290491a88380000053c54b16f410a8000082899cc023c5e34ff603b647ea000000012ec00000000677a2140000456400005e41c760000a1a8000147a6decd96213903ba43886d29b0000000000000000000000000fd206bd2e3698ac5b50794039c6ca0000052d3d0a32383278be80740930cf371ec2000035c46d380002d2800010501d0e181e5e0c00000000000488800009d0000000000002363000005f43f416e0095e5b2455f8d0112e403d43d70000000042d8000162900000000000000018b662840001581000031fc03913d30000229c00005d2478e00010b60f9a000022a80001c523a128d10000000000007fcc000000000000000195917233e4268cfa69d180e382650af1800000003bbc0001e234472423c0000ae93b6c0f5100c119107c20000274800030ca0000cb09fe7384c39cce7d800000000000000259300540000000241326e04dd80000c4b000066cc43280003d4600007ae90000000000064f025808621468d43a57b1c3800009f808b306e000000000bd1481a0000dd081c9119c000110c800000000000319800000000000bfa019b41fa00012d380000f205df44561d610da2228080b082612c87ea0b30000020a0042435f8000111698e4faea4ce121e85dc0000000000000008f9212600000000b718c821428220cca706d20fcc000033200000f6a034464c159300000000480800006047ee800000003da403b870da07705fa888cbad211a192c1b8c00007fb000079dc0000000153e49d0000025212780aeccdb875a43662254a6f24d73d1e27f40000000208e6f805f1239725b272f422c900a19fc232c7bc87bc16ec637475d986627be8f0046804ae00000000000000000004d9400004c9000064f40001a050c10000101d088044f407592600a8332f60000a79800000004244fe18d4d2be6000000015940be070f891d800000000000000000000002bd000000002c8a3e04ecf921934f800012b2023900000000b38000047e00f48000265e338825
  | 71 => 0x22c77080002d4a76cc62d0c380c445dfcba685ca0000492c00000003de6806c000000003320000000208712406ef0967000000008718000070b0000892cc1880000d94000082d9ea82d5c0000f8380003eb63ce8d8e1d7f2aca254899f15c700000000000000000009834e4d80002c445f18cbfa1052b0e360c1bd21c523f44e210d69ca0284a0000c2e99fb1de438a52c409e00f1e11a07119281132684f857e1d460000000000000003b540000a3b0afe21fc7350c8d12ef4c8a0000b72000015b24620000118900008a6cddc07e52a0c0000d43104a362811907069da915980000000000010e01cb4db90000371200000001a0b0000006820a0000000000008a30000250e3b3c00000000000000000000001088508cd99000023204094af100000000000000018161fc400008ba148417b689fc0000000158200000000a1a31980c840000b840b960000f908000000000002da8e0145680000000042028ae3050000140b4092874c0001de200000000bbb8000000000000000ebf00000000000000003161e84000247200001b84acf1d7000000000e58209900000ce8000000000005eb4edb80a700000000d73867f00000000d24a57d259a58080000000057c0000000000000006d3d30980001e944f808421ddb2598000086688cf1db8117c32181cd0000585106e947700000000000000042cc00004da800000004f8474f00003ad200008a4a0c449d800010009b5348de17a80000ad311e85c68c728efe0000000000000000fa86c100001e070000838cfbb800000000000000000016b8000000780000000306000000003f900000fc006fd0000000000000000908000000000b5051200000001a0f3aec905921c00000000144c00008d9213e00009318000000000010d7800000007564d13a47f000096bc71f837200000000de9000002884e7c96d00301f7038f00000000091c00000001770000087ac0000e86319c7168d91099004ac000000022c400000d7521c800027d48b4809602cc000000000000000000036f8d4a000000007df0000000000000000000000000006fb013300000e1c65b0b5c836549680614000136f1e900000350000000009754000000028907a9510b017f00007784b1091011768000053b9c7e3a0212049be062e24363e94c25019119a20078dcc8d9849ce85c021e17a746583c0865989271d5a6b1c0001a6542982e380c4a5070000000010e80001550573822888134b604ab0000082200002104fc81ff24b060001045a50c0648938c2cca6192bf800012ac8aea1d7c31ecb23860500001d98000136c2722000092a800001d23c7506f00000000000107705aa39aa7ae0235228b2858186890e04c000000000e9d9ba3222e05951a10000474400000000000042a784811481612ef600000000277000099a83f221
  | 72 => 0x8731b482f512578c2b3a9c82cc14086182eec00010b08df7099c00002338d930f747d880f980000000000000008c00000000000002b1000000000000000000000000001e9d000055d42581b1f0f360000e26104629aa50592398c75312477a074b1ddd08cc0dc400012610d9238843780000000000008ef1e911b120001144000000000000000000044588b0000000000b5e40740a6800028c814602b2000043b4804cb18025a00000000000000000004a6ce5592940b8c43546958000000091c0853116500000e185db22dd13a84fd4ab4840a3be86dd8b0995d929544d89282000011905ca48038000256a4580d098ca5210a60b8d1c874e1ce27e3c000000031646efcb879f0e130c00000000000360c78740002197000093c4000102d3bfc902833e08843e68199800000003a9200000000000000000000000b13379a04850850000127400011658840364800007f51d1d33ec4cb8552886215844e280001e7031a260e800023f70eca2b71009167c200a0000000000000000000e62155b35ae0001142000040c4718400000000000830c406000000000000000000000006ba00000c540000000041c800000007e9c52f9735150c0b2c68e1d4d20c620ac6bc92e800005d483d3853a1822000114a9f2700001c887c19d513dd21920000000000005b4c19c80002240824c000000040100000ea40000000014284e31fd648824ae121e989a00000000000000000000000000000033ae00000000000000000008db0000000082f80000000000000000001e6200005f940000e250000011cecb8000000035440000000000000000000000000080a40000bb2284825d4d8c8b2c00001f780000000000060eccdc981c000038140000eae035a0000431a0374a360000000211b182c996905c244646ac311400000002ca66d3011989e84b987b704c21112302a7530000000000004cd40001cf41de63914bba24a6327e97d40000000106e5714f5622f9275420f0d828b3d0c766b7ccbb9ac83150805457d8df4266012ac0000b0f05aa6550000189e1c80701cbce04b434940001194a40e214e898824c0000155a86a880c0000000022e400000000000000088496e8000073080001c9539ca9844000215f342c00012438ea13f4a76ac68106441a86000050a989800003a08ca291bb4b3a44a10012248000000000000c3d1ecc33fd166022e00000d990bc0000253428644de8615459a132800003fe000091e860f8000223845900000dd700004a5cb9891e7149200011a620b000009210e20266248ae3dd4c3882c12ec42f105b4a07c0b18983c26a989641c00000ec80000114c0000ee98b9944b600000002227000000000000000000078600001ea4000088ac773800000002090ef200000000095cff7800000005c140001381000000000001ce42dd84
  | 73 => 0x8844117fb2d300a844ea800000000000d48800002f0785c4a0000040080000fa5000010ea00009830c91108476f874e000024485de909b1105342838a89ee0a1c16a00000000000024520000000000012383be932a00002d245efc000231600005ce51cb191f000a00007e3800000005cd12190000265400010e700002aba0ca4000000035b20000e298a92417a000000014ff4c2033e40000ff31064000000006ef499625e9228826a16368d88de8036d000013a00002459323230f008f95181624178404d235c371c732911300000000000000023d02da42b74d880cb800006f6c8b58000476a0000b1b0f07408821bc0e0893e1de073d40001d8512d634e8156a0580000000000004100000000000023ee2dce00003cd1ffb00001b680000000000067440000d603b4c5d0800000003f7c50f8f2a057437e60d4c00023242a6a356c00000001e083558b9900003b0e51540000ce1321c6a30000000022cc0000b5b0000022097101d807b3159e000133600000db60000000000035040000aef0000000000006e800001bc4150407280000962000069293fe2d56226c00019a624880000a87000033086ec0000000041b07f04ae20000000047b419c00000d1647c08b09e963f1443c49a40cfa1e84000000001fa0000000000000000000000000014d700005bc0000000002fc39f110995b90000128ca56000000006210000000030260194000000000005c2c000000046a699087df8000174200003791059000021d85788c76026e0000735142107cc000002c1a9a098254acfe5a3270b5a358c833000004f800011db1d2700a845ecd038e1d000000000000e30466002dc0001452247260d4f6700002b2c0000793000000009854d2982622e388da8e3225db00007f10220861f2f94102c000000000006cc5055a23219525bbc4d492a8000084e033a80003bbc298c00003d90000273c0e794c11cfc741cf620000000000008ce8000000000000000000000065540000d5900002ffc8080cd03a2a394824607b80000000000005bf2af83d2c24420114a1a00009c3086101f0000010389170ca619a4f8f1c2200001fc92af86b325d20d6c000000009128c38d17859a2c0e00000000000301694d8a7d8be349548038000226402106f8c222002e000058a00001b093c987d100000974317a06c8bd9800037020000bf4a019000000000001422477400008baa2fe0bb81a5c00020a320f800005b7930b4b7a8bd08e480003eda0000d1e215202cc755c0fe8ffc0ace87e122900c00000638909287474b8e01ac9fa00004bb894483d480000000091904088b800004c107ce00001ad60000a9f0000480a00007448000000000000000db80000352c0001f0c241e00005fd0baa0000434cac2000009ac07d4fab82ea000053a4000000000002dc47c79
  | 74 => 0x80003a1e98f8c3e00000866000000000000000263c00023b900000000000216f000046e8e4300002efc00008918b9a0f4400001b0000000002de88869aa311f20000000138f300e707450912c008a60000e618cb546b607dc55180000000000000000000eae9100bec8000115c000000000000000000000000000510000089380000f22550c0000000000000007a600000d8c0000e6898c800000000000217e30a85ab400000000000000063e25340e00915800018550a0a26a8000000035b0000021d9e90144400000000000354c00000000000000041f8000000000008adc6701c2c079a50b45ec8d9e00006f5844c000044ea754c99484820af40000000160000000000000099139000000627a110000000011a898c000007118daea0c71a9c0000b5e0000000000000000000017c0000e948d4c406a33d869c9de639221e809b709e92756539000007343d5a000050d80000f500a000ae03ef117a0504fea89d6000000010fd11e400000000000235a0cc632b41afa18f37e28f680001179060e69340488e7b038600000001fe9000000012ab1008000088a93168f6d141802045f28a9b3f12000000000000000000000003ab0000527806a9c823910907c3301061000000000000000000000000001972000000000001cd300005da0e2b157b00000000033800024ec00000001c37000083947af80000000000000014802b187a0cb7d02b817f000000000000241a58180000000000000000000cdd00004d9c4b50f90020e112497e148c23148ef0c310b8300005e393181b0e00000f7cb7d96c02fc8000048d113e3c0c50d04cfa1e4059432ec1f296271e32420c1bd96831d4a94e83b6203f009022c08e082b616d800001a40bd20b9218c400000bd00006da80000000000078200001e8d09ee143400005b116740000000258f0610377435088cc20ec6a00c0a0696328e4c6c46b8131301e3f70e3302f70cca1a240000000164007c4161206924d60000f70000036f200002cba4e10000000000000003a5086407fd999d08de527c03113db20e26ed8b151b7d46c06f64c75a550000000011370000193400000b9040f108a931c9ab1d2e421a81ccafaa23b000080cc00024e81c2e7c700002341000045a800000001b8e000000000000000000000000003fda0000000080b4000000041080444aae0000000000000000000000000046da231c000105c0000368000015af30988aec399169b20f0726077e820d034800cc0cf082a257600009e6800015488a250e51ed902f6000024a23230000459c000176f00000000124056b00004de022300cd000000000001203000000000001f0200000000b7b8000000000003cc8911018e000114122743d926b70a900eac37ee5fa00000c9228008b9c00000003bca7fe4519998026382d34fb821b20000
  | 75 => 0x28b400000000000000029f80000566000012d40000000394667345970000161648d0000000028a60000864894a4b0400000a380df10fe000037600000000000047880001a64000000005be4c5e8810b05821a279058bc8d89ea9446a2e20c749f0d0000000000018b907683034f1881ef00000000ba5a2ee47f08b28cec0000000000012b700000000000000005632566000000000001c6c00000000000000004fc000000042d20000ad990be128c00002659dfc0cfa000000020430000896800000004a3240cd0a7956200001c78ce01d9122d86c200001cf80f9a0a4800023dd0a008f8800009a400000000a5100000a2e000004f2287197e0000000217f000000000000000000000000001b5920d60000000005911f61c14c9200002f7a0000eef868c00007af0028103000008a30000000000000000a2d975821fa2820ca41454347c00010e0000046363b4907220253792002c11f11fc425a222400000001fee1a9c00000000000000111280000000323c5f5800000004234000000028d40000000000000000000000000000000000000000000003f3c0000000000054411af097333bc810000021f544c05dac00003f318b08690034000000000000617125e000047e01758031000000000000f98040a275c00000002a3a00010350000423e3f1400017d10000000077181bd0000000000000003de20d9c00025cb2826755013904bc48780000bda1e8e000071108980ebd294656f0a909acb1efe0c008060342346069a92b019b819d47478fdb8d5823fa63e879782a2198a8e7cf2288f700ec00009809dcf1a7e0000c7f8209000000000000104272c40bcdf2a62021720754000231803d800002bba1300f383c882f91f8c30c82e1c000000046de29a000000000c46554000000000000696c52f234b00000edc6461eae0000926d0b116da230000000000000483c00011ed9fa31d680000eeb00004bee3e8c3be1b014cdc2dc823880001a9e00010d6217612206b4058d1334325081e83eea498125c78046e592f34aee2ee82a60e0a3d125bc45ae928f344447e40000b8200007b0c75b0e512d2a6ecc00000c100000000e8880000000000073f800043146adc000171f273a00000000000000098c8a0a1546432c47800000000005a000000016912064108c00000000000061c8620000000000010820fed1c16000000006e200006e6c000000000000000326989046900000ec7800045c8000000000000baa2550f9600a111c653c4a061b073f167bb0ffa01462112282400000002cea000090503fc4aea61a43f49beb18880000000218e07e237a0aa880002fb02f8409f000000006894ef90b8f0ab03e991e8a56126e80000000000041b631a905d2091489c7c8d182000042b03d3811a8e480000129103225c1257e000110f
  | 76 => 0x202ef2eb8000011323b111ba000114d02c64b2c59b8754a2de18f013e85301fbc1e063d340000000000066f00000c0830080000000000007280000000000025c04908000003b3fb800002f7800033ee000000023ec17ee4a84979217900003fd800010a1000007940000000000000000000e61466e0000000000000006d4400000000e7689d8662184f338e000000000003b8e8ae4cac000000000000e83225900008308e7517cb277c000098811bc21f2533088a9118167e36e800004ef0000000000013090c8a00010fb0000000000000f900000000702d168a47b000000011428c20101e000000000000d7000000001ab90ada00003bd80000000635c0000000000015b0000011400000000000017c16aa070000000000000000103c00004b76000112e0a9900000000413800000000990acc800000008fec00020631962931083016dc0b7a8854000000000009328000000000000000cc3015e3cf2857484d1b7114ea0ae52d70e15000000000000df61642993c0000cc60b0260f400004fb00004ec8749800027347cc80000000000048bc0001b0c1a1a46f526da66d20da3b1d00e8bb1000000000000000000000006de80000000957916f80000000000128e13420000000000000002dda7adc8210409125e0000000111916d0270c427187a1c12729000025d72e1c000000005ab00000a7c395800000000000000000041ec0000000199411be7330d7d9a3602dc72ecd7989882b168ca803b8c3315fe667c1e3a04b22d0906d1f88f822ade25b03108ce92f9228bcf9a990c159402d0e198bc64bf660f8d0621b1199c1f88ee104aa45843b408aa92e716b41a18ef0145f426a74e0dfc13a24a66159432f1c6b3cfc85a12f0260b05323300070833c029008bc270a0222e5c81e40000150277a0000d7723e6000000000001fda00008ad879f8a03000000001281cc10000496000004dd3c6408d1171264400002f800001d1724a4253c00000002aec085c000103745d600800a90e3827280000000198a022c000000000000000944000000004254000000000000000000077c800023d400000002056000052c8471163f3d7c1ccc0000000334a53c8d95a2d500005f88fdc8000000000000000000000000000001eaa304481040000000000000010a320b726fe6c6c9728000000090b0b4798a21d1c0000000098701f45f407c28642000000007b9a48d42b600011e421332ca40000172000000000abc22e800000000000000000000005b60f4201cc2d325978d8e800000008e18fbc000039e263c520e0c2d00002f1d25395d100000a304e91f0f2210518125b00003ddc00010a98000000093dc0001cda2cce816800000001e8000001d9817732e800000000000215a1a0400000000000000094c800009b00000e0995e42c5a53991e10000000
  | 77 => 0xae0000c1680000d220099064816300008d7c7ec00000c3c10e48cd9d660890967852813bb00000bd46951332000026ac000195e000051bc0000f3500007da000020cc29680000000054200000000b1e00004440000000000003456891c87c02320d10392cdf6800007aa23e0cc88000000060e4d2d0000000000000000000285c6840ff09be926fc149044c90b12b540000a9b168d3e1653844c709a2000019c4b89851d31b880eca190a7600008764d5e8c86000051080000ed10f26000000000000000000130e80733b2a00011d60d8d34da30240000aec05f05bd800024a40000000000008ef0000000105b2607331000003ce8000099000006a39d2d044a00003090743000044e4ff7000000006a400000eca0000879800000003dbe00007d79b4b000000004b280000e148dc0000000029a8000000008a5000017d8000000000000000f502530490a0aa403fa30600005cac826000000008d500000f2a0f0a00000000cdf0128000000000000000738c86b8284100000003e180003ee262dc0000000000036b05a0075e0000000003d0d92000095380001b6249040000d898cde0d2a00008c691c523486eb8f4f104900006e14f7d00000d500001023942f43700000bea1fb00000000081da0600000630cbc118e000007628000000000000000c30000035a468440000bfc0000618400000002b2a14d10ce0000000000010f4800018d8521d0ed8000000000007e40eda06c20000000000038d0886cb90955441e2974829900000000816c00016a70000000123c00004c786a386eb0af519145b888ef967824820000000133d371a18a8ce4800000000000000000000220f08fba02f03d9800000000000000068009b50748355000012988bf501161ec8a8d000000002e240001f1a00000000457a3070000000031f0b6600001cd8e8e00000000561800000000f986080f3ea55b00009314000191800008df0000131f00000001105800000000234bf0000008f089a815e0000267000000000000000000000001024461e0000e670c4d000028611b2a0a90ef22e8c00c990d00000f0cea225e818e07f88a3a8000000052e800000d0000000000000fbc00000000f850e92262e3324abd0000000000a400000000aac0000000000000005220000000000002d089398f3d3060000103420a81cac00007e48c93000000011930000000000008bd2107256e0f290a18102378858308b480001c94000063ba63500f6908c52b06e5196c6d9d1bd0000150e6878000000023c68cf4e050000316c8174adf09d82f9c00008ad800027688954e960fba401423a0e9d000000000000ff4000000008080000000000002d040dd000000000000000204c00002130f988000186428f0579000038f00000330800038ce943c7f6207100000000bc4800020461dc48e
  | 78 => 0xee8000368e1bc4be0800027661544eba9ae4319e95340000b6e28e40000f0611a20ed04398021800029b80000cd180b14b4c776030e000004c23f30000000000000000000000000000001133113a1dba0000000000047240000000013d46c200001b2232e067a00000001e68000000008559df913dc8cc49ab94da000035400002518029c12a45d11743000010fd0c400000000067cf82874c0d623a20f848c63414c2a345b59045000000002a9000035ee322481e800000005be000017a238500fb030c80001d1e974cd109eda2b607db803f20b52ac80000f57a5cd2d8c297005620a514f060ac05010693ff8518c2bf8000086a6c48e071a5839c0052c000083f00001b9c5658000000000010d400000000000000000000000000002e1cb3000000006ea80002f2049f0000135d3c6a000000001b4248068b0000000000000000000000000000000ffd09a50f90503437d80001e6059943159753003e504886401b8000032f4b6b219a115a000000010e100006a0c000000018fc000054e8000382e00011061ac43a40854000024fe0000000073e82aa29780000dea80002d0c000000000003200000000000003b3a0000000029100004794d2807e100000a1ccea8000340650cc2e29ad6470a000000022ba00008bb1122800000003c8430718a41d482ea0d901611000000011f580000000000122d1c423b341d24000000000004e2c000000000008d0105880000a32000099c8000143e75cc52408b617be64c8aac248b243a8e6c6e10e5815c231f400007064c982d10fdd8000316a000039d06ea00000000633265d0000463cc34000048e240686b80ceb358483ecb261f8d3316028ca698e1249f04cb51a80e8c417681c00000000207859240ca80000000000034219e30000000087a8f7200004c78f6c00000cb0000078d800034860000000225136f8000042f8000000069cc0001b6b0000000000000000000000000010da31b20000e50800000001ed08838000484a442c6ec0e4c417210a479c0000000000012370d49000000000000b27000037a4000000006ec24601c187880000094cb369cc649520000b6a000028e60000000000049a8302800004e32d34262800000000000000022d8e8126922fccdb09d600d4c14e03670000290200002ee8097000057a0e8f895b0000000000025d02cd000000001534361e9124085995117587490d6d24121b5a5eb890c1145286200940000f5540060f700000d68000052a437b00002a0e0434ffc1c2030de000128a0088000046c8f738000465000012950000000000000000b2f4a5231800a9805535b679848be00000000000005c0ddc00005e5889b00000000125c000260c3e4400003230e2f337c000020200003a8023a8d2a0c350000283cf6780000900000000000000af800000001e8b1c
  | 79 => 0x1980000000004387d300000000e068000000000000000000195c0000000049b0000878800000001f96363ca489f4603d28a600d1800008ee61fc00019a22b5c5a806091dd1312e781460f14154b6a2b95076a02e17764a58249929342821264000000014fe833442f000028fc6a740000000000024d8f7ba05200000a78000000009384668000000000000000000000011d800012220000000000000001f58000067a92e5231100000000010914400000000c220668000078ac0000000000088f8000000028028bfc00000000000923007e8835449e97b4981857025682de007b929545ec6dc00000000398036ec4cd9d723202629400000000000292cbaa224e000000012d28af800002e591178000000059a823a9c04000092207e88dcf37a25fd5017a5990000000000000003b9a00000001178000047400000bd500003fa468b11523ffc00001e2164b00000000b530aae427e4f6491400000000000104424e600009354dee000000000000ee400004852000000008c30f7e000000000000000000119017b94c1000008920c62000000000000c471fea0000c3b9e0d000000008f405362e4a94ac00003220a923a502ad9f9c25c600000fc1fdf316000004b710d83556253511880003ade0000e3b17f60a4202a400018cb000000000000719000000007480000000000000001cfd22da00000000a6431c84fc8000104f0000825c00021cc0000000124f0f5b0000000000000001590216cf3d00000000524c46f20c003b66ce10941a98041c371421e800000003eb40000000217014ec0a60000000000000001a280000341c00025cf3b5a819877a0000000072c80000595000063f89d3924c05504e540000000000078d922d8000000003fd1091f19000000000000a7c31be000000000000000000000000002f760000a2600000000000004900002d5050280001799082a00011a9000045ca00003008000000000000000000382400004860df34970359451ba4f649f6000000000000000711c0000000063200010570000279e0001318a57f0000962902fa653000057812b918f8145210612e31dcc000000000001c010000866c000000000000000cff22a61c080000a250000311a0000ee1800011ec4ee823f87c24bdc1dcc0000000437e35b400000002e920e0096805b9396a8c30d7d00000000000000002e8473483982780000126400000000000385400005c980000000000000005072ad0377c000005601720000a80a49d000000000000de00000000105a000006bc5fe40000bc32d3e0818a8580d800640000c160000000000000000000472600000000125000000010f29fa100000b9400022c501b200008e1142700002bb400005fe00002cf0e6c8000269c0000ea5a1990000986872a00002b3480701fb8b59285098dc5
  | 80 => 0x22b8039ccaf8000000096e909b9ce83476474c0002523173c3364c4992df1b188c5000000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x85597510e100432cb2887080211e5da5184010d64c9a0c200847575991100432bb2ca68802195d955344010caecba1a20085557510d100432bb288688021a51904344010d60c9a0220084f27690110042e939c8088021745ce40440109e0eca0220085d37350110042e839a808802178dc94044010bc0e4a0220085d27308110042e8b9840880211e5d66444010cb6cb29a200865b6554d100432db2e8688021565d44344010cb6ca21a20086986410d100423d3b4a288021ac19341440109e4ed20a20085d27390510042e8b9c82880213c1d94144010ba6e6a0a20085d07350510042f1b928288021781c94144010ba4e610a20085d1730851004338baeca880213c9d36544010ae4edb2a200867276d9510042e939ec888021745cf6444010ae2eb32220084f1759911004338bacc8880213c9d26444010ae6eab2220085d37359110042e839ac88802178dc96444010bc0e4b2220086b27419110042793b6a888021749cf5444010ba2e7aa220084f0769511004358324a8880213cdd954440109e0ecaa220086b06455110042e9b9aa888021741cd5444010bc6e4aa220085e07255110042793b0a888021749cc5444010ba2e62a220085e27215110042f0b90a8880215c5d66344010ae6eab1a20085b37458d10042d83a2c68802178dc96344010bc0e4b1a20086d16318d10042793b6a688021745d65344010da6cb29a20087536594d10042e93a4a688021b49925344010da0c929a20087537554d1004369b2aa688021d4d955344010ba0e8a9a20086d26454d1004368322a688021d4d515344010ea2a8a9a20084f27614d10042e9398a68802174dd74344010ba2eba1a20086d365d0d10043a9b2e8688021b49934344010da0c9a1a20084f27690d1004278bb48688021ac1924344010ba4e721a20084f37650d10042783b286880215c9d44344010ae2ea21a20086b06410d10042e9ba88688021d49d44344010ba2ea21a20087517510d10042a8ba88688021b4d944344010ea6ca21a20085d27410d10043c93a08688021e4d904344010da4c821a20086d06410d10043c83208688021a41904344010ae2eb31220085737558910042d9ba2c4880216c1d16244010ba6e6b1220085d07358910042e9398c488021745cc6244010dc2c431220084f276d4910042e939ea488021745cf5244010ea2a729220084f27614910042d93a0a4880216c5d05244010ba4e629220085d17314910043a8a98a488021d854852440109e4ed21220084f17690910043583248488021749ce4244010ba2e721220084f37650910042783b284880215cdd54244010ae0eaa1220085d37350910042e839a84880215c9d44244010ae2ea21220086b06410910042b93ae64880215c5d732440109e6ec99220084f0764c910042793b064880213c5d83244010
  | 1 => 0x320422fb9ac928821171cd6494410ac8e4aa682086556554f41042aabae87a0821555d443d04108eaec29682085357414b41042b8baec1a0821179cf65904108bae7b2c820846e72d964104236b96cb20821175d663904108beeab1c820845f7694e410422ebb4a72082117dd953904108baeca9c820845e7694d410422e3b4a6a0821179d953504108b8eca9a820864e53d894104326a9ec4a08219394c6250410c9aa6312820865a53d81410432ca9ec0a08219654e6010410cb2a6b0082084777655041042b2392a820821c55525310410aaaeba18820865565d0c41042aaba88620821955944310410e2aa8218820847576148410429aba0a4208211ddd560104109e6eab00820867375580410436929ac020821b454d6010410da686b0082086d043580410432ca9ac1188211b9cb650c4108dae5b286208655654c4310432d29ac018821b44c5600c410cb2a7304420866952982210432ca9ac110821179cf65084108bae7b28420845d7598c210422fbaac61082117dda53084108baed298420845f7654c210422ebb2a610821595c55208410e8ca6908420874553484210422fb9ac928021171cd6494010ad0e4aa680086596554f40042acbae87a0021565d443d00108f2ec29680085397414b40042b8baec3a00211e5da51d0010ae2ea20e800845e73d96400422eb9ecb200211b9cb65900108dae5b2c800845d7598e400422fbaac72002117dda53900108baed29c800845f7654e400422ebb2a7200211ddc765500108bced29a800845c7694d400422f3b2a6a0021171d95350010c9ca7b12800864d53d894004327298c4a00219354c6250010caca7b0a800865553d85400432b298c2a00219554c61500108bce7328800845d73994400422f398ca20021175cc65100108dce4328800846d72194400432aa9cc2200219554d61100108f6ecaa0800856872550400432cb2ca620021c65525310010cb2caa98800855975d0c400432cb2e8620021565d44310010cb2ca21880087195410c400423cbb0a4200214e5d052100108f6eab0880084f3755844004339baac220021b494d6110010da2a6b0880086d343584400436821ac2200219c5974110010ae2ea20880086716510440043c821882200219554d618c0108dce5b28600846d72d94300432b29ac21802196595300c010da2c29806008655539862004332a94c3100219554d61880108bce7b28400845d73d94200422f39cca10021175ce650801087ce8328400843d74194200422f398ca10021175cc65080108baeb318400845f7558c200422fbb4a610021175da53080108beeca98400845d7654c20042b4b82a410021d294d2008010e92a690040084757519310042aaba88788021ac99340c40108eaed28c200847975192100432cb2ca708021965955384010cb2cba1c20
  | 2 => 0xca218211b5c86510c108ece2328860847a70194430422ebb6a621821175d85310c10a3ce9b28860845e74d94430430f3a6ca21821175da6510c10a3ce8328860854e7219443042a6b90ca21821559c46510c10ab4e0328860845d75990430422ebb6a82182117dda5410c108beecaa0860854f7255043042a6392a821821179d85410c108baec2a0860854e7215043042a6b90a82182117dcd64d48108b8e6b26a40845e7498f520422e3a2c7a902117ddb43d48108baeda1ea40845f7610f520422ebb087a90219558e61d4810cb2c7306a40845f73592520422e39ac929021179cf64548108bae7b22a40861f6410d520430e32086a9021175da5314810c3cc9298a40861d6494c520422fbb2a629021879915314810c3ac8a98a40846f765485204316b22a42902187dce6414810c38e7320a40845f73590520422e39ac82902187dcd6414810c38e6b20a40862c72590520431a38ac8290218e1c16414810c3cc9318a40861d6498c520422f3a4c629021879916314810c3ac8b18a40845c7458c520422fbb68629021175db4314810c3cc9a18a40861d64d0c520422fbb08629021175d84314810c3cc8218a40861d6410c5204316b24c4290218d5926114810c72c9300a40845e73997420422eb9ccba1021179cc65d08108bae632e840852c725534204296ba0a5a1021179cf65908108bae7b2c840845e73996420422eb9ccb21021179cc65908108bae632c840845d7598e420422fbaac72102117dda53908108baed29c840845f7654e420422ebb2a721021471d153908108eaeb30c84084f170986420423cbacc1210213c5c660908108bce732a840845d73995420423b38ccaa10211e9c265508108bee6b2a840845c735954204237b92caa10211ddc565508108f6e0b2a840845e73195420422eb98caa1021175d763508108baea31a840845e7694d420422e3b4a6a1021179d953508108b8eca9a840846e76949420432b29ec2a10219554f61508108eaea30a840863654185420432b298c2a10219554c6150810ccca430a8408665521854204278b80c2a10219694f6050810cb2a7b02840847975181420431d2a0c0a10219694c6050810cb2a6302840866a521814204334a90c0a10213c5c460508108bce7328840845d73994420422f398ca21021175cc65108108ece2328840847a70194420428e3a2a6210211b5db52108108daec290840852d74148420423b388cb990211e9c065cc81087ce832c640843d74196320421fba2ca990210f1d1654c810a98e4a9a640865553d85320423aba8c2990219554c614c8109e2e030a640865953d81320423cba8c0990219654c604c8109e2e2302640843e74194320421eba0ca19021535ca530c8108eaeb30864084f170984320432b29ac2190211e5d6600c8109e2e3300640865a53580
  | 3 => 0xd761509109e4e1b0a848847a75d81424427938ec0a122117dcd65109108b8e6b28848845e73194424422eb98ca212211d1d56110910cc8a4b0884884f070584424423c3aac0212219a14960109109e0e2b00848843e74d97324421eba6cb99221471d153cc910a98e4a9e648854d7314b324423a3aac3992213c1c161cc9108f0eab0664884f071583324421f3a6cb192210f5d3658c91087ee8b2a648843c74595324423bb8aca992211edc1654c9108bced29a648845c7654d324428e3a2a699221531c9534c9108eae3b28648847970d94324421fba2ca192210f1d1650c9108bce6328648845d76d4c324430faa0c6a0a21871506350510c5ea8312828862c54189414431c2a6c0a0a219614d60cc510cd0a4b06428845f73595404422e39acaa02211bdc965501108d8e4b2a808861f5418d404430e2a0c6a02218bd506250110c58a8312808863454d85404432a29ac3982210fdd1654c110878e8b2a608846f725953044236392ca982219914961c811087ee8b2a408843c74595204422fb9aca90221171cd6548110e30a821e20887145410e104422f39cc52a021175ce62950108bee6b14a80845c7358a5404327b1ec4aa0219318f6255010c9ec6312a80864c63189540422fb9ac2aa021171cd61550108dee4b0aa80846c72585540432bb18c2aa0219518c6155010ccec430aa80866462185540422fb9ac0aa021171cd60550108dee4b02a80846c72581540432db18c0aa0219618c6055010cd6c4302a808668621815404338308c0aa0210fdd95415010c5aa8b10a80864e639885404326b1cc42a0218b9916215010c9cc6b10a80864d63588540432ab1cc22a0219958a6115010cb2c7300a80866962980540430f324a929821879915494c10a9ee4aa4a60854c7255253042a7390a929821535c85494c10a9ce5b24a60854d72d9253042ab38ec929821569c36494c10c9ac4314a6085567118a53042ad380c529821539c86194c10a9ae430ca60854e7218253042a6b90c129821179db5454c10c38c92a2a60861c6455153042a7b92a8a9821531c95454c108bcec2a2a60854e7215153042a6b90a8a982153dc96454c10a98e4b22a6085547159153042ac382c8a982147dd16254c10a38e8b12a6085547158953042ac382c4a9821935886254c108beeca98a60846e721974304236b90cba1821479d365d0c10c3ce9b2e860851e7419743042a7390cba1821535c865d0c10a9ee4aa6860854c7255343042a7390a9a1821535c854d0c108dce5b2c860846d72d96430423abacc3218213c5c26190c10caca6b0c8608479759824304278b8cc1218219694d6090c108bee6b2a860846f725954304236392caa1821179da5350c10caaa7b0a8608475751854304278b80c2a18219654f6050c108f2ea30286084f1711814304237390
  | 4 => 0xcec5b0aa88866462d85544432db1ec0aa2219618f6055110cd6c5b02a88866862d81544421fbb2a82a221471cd5415110a58e4aa0a88845f73588544422e39ac42a221179ce61151108bae7308a88845e73980544422eb9cc02a221875cf6454d10c3ee6322a68861c64d8d5344317b26c4a9a218b1936254d10c5ec8312a68862c641895344327b18c4a9a218d1936154d10cc8c5b0aa68863864d815344334316c0a9a2117dd95314d10a38e8a98a68854c7254c5344237396cba1a211b5cb65d0d10a9ee4a9e868854c7254f434428f3a6cba1a21539cb65d0d10a9ae5b2e868851e7419743442a7b92a9a1a21531c954d0d10aaee2aa6868855b705534344237396cb21a211b5cb6590d108eae3b2c868847970d96434422eb9ccaa1a211bdc96550d108d8e4b2a868847771595434423db82caa1a211bdc96510d108d8e4b28868846e721944344236b90ca21a21475cf5410d108baed298868851d7494c434428fba2a621a2153dc95310d10a98e4a98868847475584434432a29ac221a213c1c16110d108f0eab00868865853580434427838ac021a21479d36510d10a9ee4b28868854c72594434428f3a0ca21a21539c86510d10a9ae4328868851e75990434422ebb6a821a21475db5410d10c3aedaa0868851e74950434422fbb2a821a2153dc95410d10a98e4aa086885577155043442adb82a821a21479d45410d10a3eec2a0868851d76150434438a2a4c221a21551d56110d10ca8cab0886887145458443442e8382c221a21c61526010d10ab0eab00868865865580434438c2a2c021a21741c56010d10da2c2b00868845f73593524422e39ac9a922117dcd64949108b8e6b24a48861e6410e524430eb208729221179cf64549108bae7b22a48861e73d91524430eb9ec8a922187dcc6454910c38e6322a48861f64d8d524430e326c6a9221179d36354910c3ec831aa48861c6418d524422f3a0c6a9221179db43549108b8eda1aa48861f64d0d524430e32686a9221179d843549108b8ec21aa48861f6410d524430e32086a92218b1936254910c98c7b12a48863464d85524432a31ec2a92218e1936054910cb0c7b02a48846f7654852442963a2a429221531cd52149108bee6b20a48845c73590524423bb8ac8292211edc164149108bce9318a48845c7458c5244326392c62922117ddb43149108baeda18a48845f7610c524422ebb08629221179cc61149108bae6308a48845e73180524422eb98c029221179cf65d09108bae7b2e848845e73997424422eb9ccba1221179cf65909108bae7b2c848847571d96424423cb86cb21221179cc65909108bae632c848861f5498e424430e2a4c721221179ce65509108bae732a848845f73595424422e39acaa12211ddc565509108f6e0b2a848847471195424423c380caa12211d9
  | 5 => 0x854e72d5043c42a6b96a821e2117dd95410f10ca8cab08878845f7359352c422e39ac9a96218799043d4b10c3ac821ea5886726158352c422fb9ac929621171cd6494b108bce7b22a58845d73d9152c4237bb2a4296219358d5214b108bee6b20a58845c7359052c422f3a4c629621171d16314b108beeda18a58845d76d0c52c422fbb08629621175d84314b10c9ac7310a5886556398452c433930ac029621179ce65d0b108bae732e858845e73d9642c422eb9ecb21621179cc6590b108bae632c858845e7399542c422eb9ccaa162117dcd6550b108b8e6b2a858845e7319442c422eb98ca216210f9d2654cb1087ae932a658854d7214f31c422f3b0a698e21535c8534c7108beeca98638864d6394821c4326b1aa410e219a9496008710ad4e5aa681886365418540c423cbb6a8206215a9cb5410310e36a821881884797614840c432aa98c298621995486148310c9cc7316a90864d6398b548432731ac5aa4219358d62d5210cccc4b0ea90865a63983548432cb1cc1aa4219a98a60d5210cd2c5306a90867161983548422f39cc52a421175ce6295210caec7b0aa90865463d85548421fbb2a82a4219c5866015210ce2c3306a70845f7654c5384326a9ac429c219398d6214e10cccc4b08a708669629805384338b0cc029c211b9ca65d0e108dae532e870854e7214f43842a6b90a7a1c21479d365d0e10a9ce532e870854d72997438428f3a0cba1c21539cb54d0e10a9ae5aa6870846e721964384236b90cb21c211b9ca6550e108dae532a870846e721944384236b90ca21c21539c85310e10a9ae4298870865853580438428f3a6ca21c21479d06510e10a9ce4328870854d72194438422ebb6a821c21539cb5410e10a9ae5aa0870845f76550438432c32ac021c2117dcd64d4a108b8e6b26a50861e6410f528430eb2087a94219c58660d4a108bee6b24a50845c73592528422f39ec8a9421175cf6454a108deeca90a50864d63548528422fb9ac829421171cd6414a108bce9318a50845c7458c528422fbb68629421175db4314a108beec218a50845d7610c5284326b1cc4294219658e6014a10ce2c3300a50845e73997428422eb9ccba1421179cf6590a108bae7b2c850845e73196428422eb98cb21421179ce6550a108bae732a850845f73595428422e39acaa1421179cc6510a108bae6328850843e74995328421eba4ca99421599cb54d0610c74a8302830847576d5041842b3396a820c21c5d5043106108eaec2908308659531813184334a90c090c21535c853cc2108bcec29a610854d7214d308422fbb2a6184219358e5208210c9ac6a90410866652584208422f39cc52a221175ce6295110c3ec831aa88864f63d89544432631ec4aa2218bd906255110c9ec6312a88864c63189544432bb1ec2aa2219518f6155110c
  | 6 => 0x82b4bacc8900413a5d66448020cd2eb32240104ea7499120082b5baac89004172dcd6448020b90e6b2240105e37159120082f038ac890041aa9d064480209d4edaa240105ca73d5120082e4b9ea8900413a1da5448020d50c92a240104eb7655120082743b2a890041aa1915448020b96e6aa240105c87355120082f1b8aa890041781c554480209d4ec2a240105ca7315120082e4b98a890041789c45448020bc2e22a240105697598d20082b5baac6900416add16348020b50e8b1a40105e37158d20082f038ac690041b258c63480209d4eda9a40105c97594d2008365b2ca690041d2d965348020b94e929a40106ca6494d2008364324a690041d2dd55348020d96caa9a401074b6554d20082e43a2a690041b29915348020d90c8a9a401074b5454d20083a4aa2a6900413a9d85348020b94e629a40105cb75d0d20082e4bae8690041b2d974348020e96cba1a40106ca64d0d200836432686900413a9da43480209d2ed21a40106a86490d20082e539c86900413add943480209d0eca1a401056a7510d20082b4ba88690041aa1904348020b96ea21a401074a7510d20082e4ba88690041d25d44348020a92ea21a40106cb6510d20083a5b288690041729d04348020f14e821a401078b6410d20083653208690041b21904348020f10c821a40106886410d20082b4bacc2900415add56148020b56e8b0a40105a87458520082e5b9ac290041721cd6148020b94e630a40105c9731852008370b08c2900413a9db5148020b94e7a8a40105c973d4520083a4a9ca2900413a9d85148020b54e828a40105a97414520082e5398a290041725cc5148020e92a628a40107615114520082753b482900413a5da4148020d50c920a40105ca7390520082e4b9c82900413add941480209d0eca0a401056b7550520082b43aa829004172dcd4148020b90e6a0a401056a7510520082b4ba88290041aa1904148020ad4eb98a401056975cc52008275bb262900413a1d931480209d4ec18a40104e9760c5200832731cc5aa6219358e62d5310c9cc6b16a98864d6358b54c432b31cc3aa6219558e61d5310cccc530ea9886656298754c4335312c1aa6219c98560d53108bce7314a98845d7398a54c432db1ec0aa6219618f605531087eecaa0a9886726158054c433930ac1a9e2117dd95314f10c9aa6b10a78864e6358853c4332b14c229e219a9896014f10ce4c2b00a78846e7299743c4236b94cba1e21539c853d0f10a9ae429e878851e74d9743c42a7394cba1e21535ca65d0f10a3ce832e878854e72d5343c42a6b96a9a1e211b9c86590f108dae432c878846e7299543c4236b94caa1e211b9c86510f108dae4328878854e7214c43c42a6b90a621e219514d6110f10a3ce9b28878851e7419443c42a7390ca21e21535c86510f108baedaa0878
  | 7 => 0xb20841175cf65904208bce732c821045d73996410822ebacc72084117dd563904208beed29c821045d7694e410822fbb2a720841175d95390420a38e8a9c82104e97098a4108274b94c12084117dcd65504208b8e6b2a821045e73195410822eb98caa0841175d763504208baea31a821045e7694d410822e3b4a6a0841179d953504208b8eca9a821064e53d894108326a9ec4a08418b9506250420c9ca6312821064d531894108274b80c4a08419918a5150420cc8c4a8a821065a53d81410832ca9ec0a08418e9506050420cb4a63028210659531814108274b90c0a08419c9446050420ce2a2302821045e73994410822eb9cca20841471d1531042087ee8b2a621043c7459531082aa38aa6988419354f624c420c9aa631262104e970189310832ca9ec0988419654c604c4209d2e430262105557194c3108274b84c4188419394d620c4209d2e5300621065a53580310832ca9cc1908419654d60c84208baeb318421045f7558c210822ebb4a61084117dd95308420e8ca6908421074553484210822fb9ac928041171cd6494020ae0e2aa680106596554f40082acbae87a0041565d443d0020ad2ebb1680105697510b400822f39ecb20041175cf65900208baeb31c801045f7558e400822fbb4a720041175da53900208beeca9c801045d7654e400822f3b4a6a0041171da53500208bceca9a801045c7654d400832729ec4a00419354f6250020c9ca6312801064d53189400832b29ec2a00419554f6150020caca630a801065553185400822f39cca20041175ce65100208bce6328801045d731944008326a9cc4200419354d62100208f6ecaa0801057071550400832cb2ca620041c65525310020cb2caa98801055975d0c400832cb2e8620041565d44310020cb2ca21880107195410c400823dbaac4200413add56210020cd6eab1080106ca535884008364a9ac420041b2d0d6210020d9086b10801066965d0840082b4ba884200419a5944210020f1086210801064d5358a300832729ac41804196595300c020d92c4980601054d7510f200835532681900411b5da5288020ab2ea21c40104797694a200835532685100411b5d66448020c9ecb29a401064f6554d2008327b2e8690041535d44348020c9eca21a401068c6410d200835432680900413a9da4048020b94e720240105c97390120082743b2809004172dcd4048020b90e6a0240105e37150120082f038a80900411e5d66448020cb6cb29a401065b6554d200832db2e8690041565d44348020cb6ca21a40106986410d200835432684900413a9da4248020b94e721240105c97390920082743b2849004172dcd4248020b90e6a1240105e37150920082f038a8490041729cc2148020b92e610a401066975d9520082753a6ca900419a9db6548020b94e7b2240105c973d912
  | 8 => 0xc6055020cd0c4302a810673611815408338308c0aa0410fdd95415020c6aa8b08a81064d63988540832b31cc22a0419558e6115020c6cc8b08a81065663584540832ab1ac22a041999896115020cb2c7300a81067161980540830f324a929841879915494c20aaee2aa4a6105547155253082ab388a929841555c45494c20a9ce5b24a61055671d9253082aab8ec929841569c36494c20aace2314a6105557118a53082a7390c329841955846194c20ab4e030ca6105567118253082aab88c129841179db5454c20c38c92a2a61061c6455153082abb8aa8a9841551c55454c208bcec2a2a6105567115153082aab88a8a9841531c96454c20aaee2b22a6105547159153082ac382c8a984147dd16154c20a38e8b0aa61054c7258553082ac382c2a9841955846154c208beeca98a61047671197430823ab88cba1841479d365d0c20c3ce9b2e861051e7419743082ab388cba1841555c465d0c20aaee2aa686105547155343082ab388a9a1841555c454d0c208ece3b2c861047571d964308236bacc5218413a5c26290c20c9ca6b148610479759824308274b94c1218419694d6090c208bee6b2a861047771595430823a38acaa1841179da5350c20c9aa7b12861046d751894308274b80c4a18419654f6050c208f2ea30286104e9721814308237390ca218411d9c46510c208eae2328861047a70194430822ebb6a621841175d85310c20a3ce9b28861045e74d94430830f3a6ca21841175da6510c20a3ce8328861054e7219443082ab388ca21841555c46510c20ab4e0328861045d75990430822ebb6a82184117dda5410c208beecaa086105577155043082aa38aa821841179d85410c208baec2a086105567115043082aab88a82184117dcd64948208b8e6b24a410564715534208326b2aa7a1041535d743d0820a9aea21e841056975d83420822f39ecb21041175cf65908208baeb31c841045f7558e420822fbb4a721041175da53908208beeca9c841045d7654e420822f3b4a6a1041171da53508208bceca9a841045c7654d420832b29ec2a10419554f6150820caca630a841065553185420832d29ec0a10419654f6050820cb2a73008410659535804208237bb2a821041591c55410820e1aa9298841054d75d0c4208326b2e8621041535d44310820c9aca218841070d5410c4208237baac0210413add56010820cd6eab0084106ca535804208364a9ac021041b2d0d6010820d9086b008410659535823208326b2a64190419694d600c820d9264b00641045f73592510822e39ac928841179cf64544208bae7b22a21061f6410d510830e32086a8841175da5314420c3cc9298a21061d6494c510822fbb2a628841879915314420c3ac8a98a21047776544510831ab22a228841179ce65d04208bae732e821053471553410822f39ec
  | 9 => 0x6c3b02a89067061d81544821fbb2a82a241471cd5415120a68e2aa0a89045e73988544822eb9cc42a24117dcd61151208b8e6b08a89061d73d91534830fb98c8a9a41871936354d20c58c9b12a69063764d85534831a326c2a9a418dd906154d20c68c830aa690657631855348333b10c2a9a418e1936054d20ce0c3b02a69045f7654c534828e3a2a629a41551c55314d208ece3b2e869047571d9743482abb8aa7a1a41551c553d0d20a3ce9b2e869055671d9743482aab8ecba1a41479d065d0d20a9ee4aa686905577155343482aa38aa9a1a4156dc154d0d208dae5b2c869047671d96434823ab8ecb21a411e5c36590d208bae732a869046f72595434823bb8acaa1a411d1c56550d208f6e0b2a869047771594434823a38aca21a411d9c46510d208eae2328869051d73d50434822ebb4a621a41475d25310d20a3ee8a9886905577154c43482aa38aa621a411b1d56210d20c98a6b1086904e870588434823c3aac021a419614d6010d209d0e4b00869051e74d9443482abb8aca21a41551c56510d20a3ce832886905567119443482aab88ca21a41479d66410d208baedaa0869051d76d50434830ebb6a821a41479d25410d208beecaa0869054f7255043482abb8aa821a41551c55410d20ab6e0aa0869051e75150434828fbb0a821a41475d85410d20e18a9310869054c75588434832632ac421a41c31516210d20b90e0b1086907185498043482ac3aac021a41961956010d20e30a8b0086905c8725804348364b12c021a4187d506350920c38a831a849063754185424831a2a0c2a12418e1536050920cb0a6b06649045f73593514822e39ac9a8a411ddd95114520a68e8a88a29055473544514822fb9ac828a41171cd64145208bce9318a29045c7458c514832a38ac628a4117ddb43145208baeda18a29045f7610c514822ebb08628a41179ce65d05208bae732e829045e73196414822eb98cb20a4187d526390520c38a931c829045e73995414822eb9ccaa0a413a9c362505209d4e5b02829045f73594414822e39aca20a41179cc65105208bae632882904e8705884148332b10a220a413a1c96010520ce0a2b00829051c7454f31482aa38aa798a413a1c162cc520aaae628e62904e872583314822f3b4a698a41471d1534c520aa8e2a9a629043f74594314821e3a2ca18a41175db530c5208bee6b2a809045c73595404830faa0c6a0241871506350120c58a9b12809063754185404831a2a0c2a02419314d62cc12087ee8b2a609043c74595304838c2a08790241c315043881208bce730ca81045d73986540822fb9ac32a041171cd61950208bee6b12a81045c735895408327b18c4aa0419318c6255020caec7b0aa81065463d855408332316c2aa04195d8c6155020ca8c630aa81066462185540832db18c0aa0419618
  | 10 => 0x5d071501300c26d3b4869806156dd5434c030ab2eb1926018559758c5300c32731cc5aa6419358e62d5320cacc730ea9906556398754c8333314c3aa6419598d61d5320caac6b0ea9906666258754c8335312c1aa6419c98560d53208bce730ca99045d7398654c832db1ec0aa6419618f605532087eecaa0a99066a6258054c8335312c1a9e4117dd95314f20caaa6b08a7906566358453c8333312c229e419a9896014f20ce4c2b00a7904767199743c823ab8ccba1e41559c453d0f20aaae229e879051e74d9743c82ab38ccba1e41555c665d0f20a3ce832e879055671d5343c82aab8ea9a1e411d9c46590f208eae232c87904767199543c823ab8ccaa1e411d9c46510f208eae232887905567114c43c82aab88a621e419314d6210f20a3ce9b28879051e7419443c82ab388ca21e41555c46510f208baedaa0879055671d5043c82aab8ea821e4117dd95410f20c98cab1087905557114f32c822f3b0a699641555c4534cb208beeca98659045f7359251c822e39ac928e41179cf64547208bae7b22a3904777654451c832ab1aa228e41179ce65d07208bae732e839045e73d9641c822eb9ecb20e4117dcd65507208b8e6b2a83906556394421c832ab1aa210e415c9c754d0320c5ca8312819047976d5040c82b938ea820641c6d504310320c9aa6312619065663987548832ab1cc3aa4419958a61d5220cacc6b0ea91065563587548832d31cc1aa4419658e60d5220cd2c5306a910672619835488338b0cc1aa441179ce61952208bae730ca91064f63d89548832631ec4aa4410fdd95415220cd2c5300a91066962983538822fbb2a629c419554d6114e20ccac5308a710656635845388334b14c029c419c5866014e208ece332e87104757199743882ab388a7a1c41555c453d0e20a3ce9b2e87105567199743882aab8ccba1c41479d065d0e20aace3aa6871055571d53438823b388cb21c411d5c46590e208ece332a871047571995438823b388ca21c411d5c46510e20aace229887105557114c438832c29ac021c41479d36510e20a3ce832887105567119443882aab88ca21c41175db5410e20aace3aa0871055571d50438822fbb2a821c41961956010e20acce3aa6851063a541814288236bb6a821441599c75410a20e1ea8218851065953181328822fb9ac928c41171cd64946208bce7b22a31045d73d91518823bbb2a228c419558d51146208bce732e831045d73997418822f39ecb20c41175cf65906208bee6b2a831045c7359541882aab88a798441179d8534c220aaae229a611045f7654c308822f39cc32a241175ce6195120c3ec831aa89064f63d89544832631ec4aa24195d8f6155120ca8c7b0aa89066762d85544831bb20c2aa24195d8c6155120ca8c630aa89066762185544832db1ec0aa2419618f6055120ce
  | 11 => 0x4c2b238aa4292611ddc564149308e8e2b20a49854d7210c524c30e2a2c721261361c163909308ece332a849847571995424c23bb8aca212611d1c565109308ece2328849847571194424c326b18a4212618e1516010930cd0a4b0084984da70993324c30f320a999261361c161cc9309b4e1322649854e72951324c30e320a899261539d7624c930a9cec292649864e76149324c327320a49926193190524c9309b4ea302649865a75181324c32d2a0c09926196150604c9308eeeca88a29853474544514c2b2392a228a611bdc964145308d8e4b20a2985557110c514c30e2a2c720a61361c163905308dce532a829846d72995414c237b92ca20a611b1c965105308dce4328829846d72194414c32ab18a220a618e1516010530ce0a2b0082984da70993314c30f320a998a61361c162cc5309b4e1322629855671951314c30e320a898a61559d7614c530aacec28a629865676145314c32b320a298a6195190514c5309b4ea302629865a75181314c32d2a0c098a6196150604c5308bceb31a429849c7458d214c26c382c690a610fdd16508530878e8b2842984d87058c214c326b1ea410a619358c5208530acae2290429865563d44214c32ab18a210a61595c85108530accea908429856475484214c30e2a6c6a02618bd506250130c58a8312809863754185404c31a2a0c2a026187990548c1308eee2b14a8184747158a540c237b92c32a0611b1c9619503087eecaa0a81864e63588540c333314c22a0619958a6115030cacc6b08a81866662584540c332b12c22a0619a58a6015030ce2c3300a81854e72153430c2a6b90a9a1861559c454d0c30aaae22a6861851e74d94430c28fbb4a82186117dd95410c30a3ce82a0861871a54980430c22fbaac021861c69516010c309b6eab00861865b75580430c32d2a2c021861961516010c30acce3a94a4185597010d520c237bb2a4290611d9c665908308eae332c84184d97098e420c32731aa5210611ddc565508308e8e2b2a841864c63949420c333290c2a1061995486150830cd4a4302841866952181420c2b3396a328861565c043544308eeeca88a21846e72996410c236b94cb20861365c26390430cacc6a8c821846f72595410c236392caa08619518e5150430cc8c528a821866462545410c339288c0a08619c544605043087ee8b2a421843c74595210c22ebaec690861365c26308430acae3290421864e63548210c2b2b94a2108619598d5108430aceea908421856575484210c30f32687280618795263900308beeab18801861e64953300c2a6b90a998061555c454cc0308baed29c60184797694e300c22f3a6ca98061175d6644c0308b8ed2a2601861c64951300c22f3b0a898061535c8544c030aaae22a2601855975901300c26c3b28098061a6191404c030b90e4a026018
  | 12 => 0x280810f5da54900408f2ed2a4802061f65d0d401030fb2886a0081a310c6250040d288630a802061f65d8d401030fb28c6a00818bd976250040c5eca312802068c63189401031bb2ec2a00818dd946150040d28c630a80206a46218540102cd39ec8a008196d976350040cb6ca31a80204da76d0d401032db2e86a0081669ce43500409b4ec21a802065b6510d40102cd3b086a0081a69d84350040d36ca21a802071b6510d4010335b2ec4a0081e210f6250040d3086312802066b651894010365b18c4a0081b218c6250040f108631280206aa541894010365a18c4a0081aa90c6250040d508631280206c8431894010344218c4a00819cd976150040f2087b0a80206e062d85401034c218c2a00819cd946150040da6c630a80206d06318540103c8218c2a0081b8d886150040dc0c430a80206b2541854010369a18c2a0081ac90c6150040d608630a80206d0431854010348218c2a00819398e62d5330c9cc6b16a9986566398754cc333314c3aa6619958a61d5330cacc6b0ea9986666258754cc332b12c3aa6619a98960d5330ce4c2b06a99854d7218e54cc2aab88c72a6610fdd95415330cb4c6b00a99854e72d5343cc2a6b96a9a1e61559c754d0f30aaae3aa6879854e72d5043cc2a6b96a821e61559c75410f30aaae3aa0879845f7655043cc38d2a4c021e61c69516010f308eee2b24a5984747159252cc237bb2a429661995496114b308ece332e85984757199742cc23bb8acaa16611d1c56550b30c38c92a2659854e7295132cc237b92c928e611b1c96494730c98c4992a3984777654451cc332b12a228e611b9ca65d07308dae532e839846f7259541cc236392caa0e6187192544c730aace32a263985547154931cc24e3a2c690e61361c16348730ac8e2a9243985647254521cc26cb98c090e6199d952108730ccaca908439861e5418d40cc21fbb2a82a4619658e6015230e34a9306871871a54583438c31caa0c0a1c61175db5410e30c38c821aa51846f76548528c23bb8acaa14611d1c56550a30c38c821aa31847776544518c237b92caa0c611b1c96550630c3ca8b1c811861e64953308c327b1ec4aa2618bd906255130c9ec6312a89865763d85544c333b16c2aa2619918b6155130c6ec830aa89865763185544c333b10c2aa261991886155130cd0c5b02a89867061d81544c21fbb2a82a2614b1c95415130a68e2aa0a89847771588544c23a38ac42a2611bdc961151308d8e4b08a89863854583434c2a7b92a9a1a61531c954d0d30aaee2aa6869855471553434c38c2a4c1a1a61369d660d0d30cb4eb306869865a54983434c32c2a4c1a1a61c615160d0d308beecaa0869854f72550434c2a6392a821a6155dc55410d30aa8e2aa0869861e64150434c26c382c421a61361c16110d308deeca90a49852c7454852
  | 13 => 0x5190540caac7a8c82a065663146415032ab18a320a819a14a6090540ce0a330482a066852582415022f3aec6a0a81179d463505408bceda9a82a045e7614d41502373aec4a0a8193d4f6250540c98a7b1282a046e751894150327a98c4a0a819314c62505408dceda9282a064f63d49415032631ea4a0a811b9d85250540c9ec629282a064c63149415032bb1ea2a0a819518f5150540ccec5a8a82a066462d45415032bb18a2a0a819518c5150540ccec428a82a066462145415032da9ec0a0a819614f6050540cd6a5b0282a066852d81415033828ec0a0a8196d4c6050540cb0a630282a066b521814150334290c0a0a819cd4460505408dee4b2e62a046c725973150237b92cb18a811b1c9658c5408dce5b2a62a046d72d953150237b92ca18a811b1c9650c540cb0a730062a066852980315033828cc018a819a149600c540ce0a2b0062a045f73597215022e39acb90a8117dcd65885408b8e6b2c42a045e73d95215022eb9eca90a81599c75248540acce5a8a42a045f73594215022e39aca10a81179cc65085408bae632842a045e7598c215022e3aac610a8117ddb53085408baeda9842a045f7614c215022ebb0a610a819398f5208540c9ac7a9042a062e641482150327318a410a819358c5208540acae229042a065663d44215032ab1ea210a818d9905108540cacc628842a06556314421502b2b90a210a81599d52108540ac8ea90842a066665484215033232a4210a81d1d4d2108540e88a690842a066852980215033828cc010a819a1496008540ce0a2b0042a055a75d0f40502ad3a887a0281d2d4c52d0140e90a629680a074b4314b40503a4218a5a0281d814b51d0140ea6a628e80a07505314740503b1a90a3a0281d814851d0140ea68628e80a075043147405032731ea5202819358f5290140c9cc629480a064d6314a4050386218a5202819598f5190140caac7a8c80a065663146405032ab18a320281c510c5190140e18a629480a0714531464050392290a32028117dd95314c40c9aa6b10a6206555358453102ccb84c821881179cc61548408bae630aa42046f765485210326b1aa429081995496114840e1886a90842069843580421023bb8aca990811d1c5654c8408ece232a6420475711953210316322a4990819654c604c840cd2a4302642045e73189511022eb98c4a88811ddd95114440caac6a88a22066562544511038a21aa220881a610d60104408dee4b2a622046c725953110237390ca988811b5c8654c440c68c8a8a6220659531813110338a88c09888117dcd65484408b8e6b2a422045e73195211022eb98ca90881591c55248440ac8e4a8a4220669521812110338a88c090881179cf65084408bae7b28422049c7458c2110333b2a4210881995952108440b48e8908422045d76d0e501022ebb087
  | 14 => 0xec29c84a064e63d4a4250326b1ea5212819398c5290940c9ac629484a066852982425022f3aec6a1281179d463509408bceda9a84a045e7614d4250327b1ea4a12819318f5250940c9ec629284a064c63149425023b3aec2a128195d4f6150940ca8a7b0a84a066752d854250332296c2a12811d9d46150940caea630a84a0654531854250333a90c2a1281991486150940cb6a7b0284a065853d814250334296c0a128196d4c6050940cb0a630284a066b52181425023bb8acb992811d1c565cc9408eee2b2c64a047471596325023b38eca992811d5c7654c9408eee2b2864a047471594325032c29cc0192819a14a600c940cd0a4b0064a045e7398b515022eb9cc5a8a81599ca53d4540acae529ea2a05677254f51502b2392a7a8a81559d743d4540aacea21ea2a074753d4b51503a229ea5a8a81d1d0f52d4540e8887a96a2a05567394b51502aab9ca5a8a8155dcd52d4540aa8e6a96a2a07475314b51503a2298a5a8a81d1d0c52d4540e8886296a2a055673d9351502aab9ec9a8a81599cb64d4540acae5b26a2a07167410f51502ab39cc5a8a81555ce62d4540ccec5316a2a05567390b51502aab9c85a8a811ddd942d4540aaee6a16a2a05547350b51502b9b8285a8a815c1c142d4540c9ea7314a2a064c5398a5150327a9ac528a819314d6294540c9cc7a94a2a064d63d4a5150327318a528a819358c5294540cacc7a8ca2a065563d465150333316a328a819958b51945408bceda9aa2a045e7614d5150327a9ec4a8a819314f6254540c9ea6312a2a064c5318951502373b6a4a8a8193d8f5254540c98c7a92a2a046e761495150327b18a4a8a819318c52545408eeeca88a2a05577354451502aa39aa228a8159dc95114540ac8e4a88a2a065665d4c515023abb4a628a81599ca5314540acae5298a2a04777654c51502b3b92a628a81591c95314540cacca298a2a055675d0c51502ab3a88628a81999975214540e8ea7a90a2a074453d4851503a3a1ea428a81d110f52145408eaed290a2a05567394851502aab9ca428a811ddd95214540aaee6a90a2a0554735485150333328a428a81d1d4c5214540e88a6290a2a07474314851503a2218a428a81559cf6414540aaae7b20a2a05717018c51502b93848628a815c5c24314540ae6e0a18a2a05707050c515038b3a08628a814d5d06214540aace6310a2a0555731885150332b10c428a815c5c06214540aace7210a2a05557390851502b93848428a815c5c242145408eeeca10a2a05577350851502aa39a8428a815cdc14214540ae0e0a10a2a0572700c851502b8b806428a8155dcd4014540aa8e6a00a2a05677250051502b23928028a81179d663905408b8eab1c82a045d76d4e415022ebb0a720a819398f5290540c9ac7a9482a064e6314a4150326b18a520a819598f
  | 15 => 0x6f76548529022ebacc72148117dd56390a408baed29c852045f7654e429022ebaec6a1481175d46350a408bced29a852045c7654d429032b29ec2a14819554f6150a40caca630a8520655531854290333290c2a1481995486150a40cb4a7b02852065953d81429032d298c0a14819654c6050a40cd4a4302852061c6454d32902a6392a6994811d9c7650ca408eae3b28652054d7294c329032d29ac0194819394e62d4640c9aa7316a32064e5358b5190326a9ac5a8c81599cb51946408bce6312a32045d73189519022ebb4a628c8117dd953146408eeeca88a32045d7598e419022fbaac720c81175da53906408beeca9c832045d75d8d419022eba8c6a0c81179da53506408b8eca9a832064e53d894190326a9ec4a0c819394c6250640c9aa63128320664629454190332312a2a0c819694f6050640cb2a7b02832065a53181419032ca98c0a0c819c9446050640c38c8a9a63205547154d3190237396ca18c811b5cb650c640aaae3298632065a53580319022f39ccb90c81175ce65c86408bce732c432045d73996219022f398ca90c81175cc6548640c3ec929a432061c6494d219022f39eca10c81175cf65086408bce7328432045d73994219022ebacc610c8117dd56308640938e8b18432045f7694c219022ebb4a610c8117dd953086408baeca9843205657194821902b2b94a210c8159dd52108640acaea90843205a47448421903a329a4210c81d154d2108640c3acb29e812061d6554f409032cb2ca7a04819659553d0240c9ea7314a6a064f5358a535032ba9cc329a8195d4d6194d408beeca98a6a054f7254c53502a6392a629a8155dc55314d40aa8e2a98a6a05597018853502acb80c229a819614e6090d40cb6a630286a045e73987525022eb9cc3a9281599c653d4940acae329ea4a05677154f52502b238aa7a9281539d743d4940a9cea21ea4a054e73d9352502a6b9ec9a9281599c764d4940acae3b26a4a070e7410f52502a739cc3a9281535ce61d4940ccec330ea4a064e63d4a5250326b1ea52928195d4e6194940ca8a730ca4a066752986525032ba9ac3292819514d6194940ccea4b0ca4a045e76d4d525022f3b0a6a928195d4f6154940ca8a7b0aa4a065753185525032a298c2a92811bdd95214940a9ee6a90a4a054c7354852502b3b8aa429281591c55214940c9ccba98a4a046d7694c52502b338ca629281595c653149408deeca98a4a05677154c52502b238aa629281939945314940a9ceba18a4a054e7510c52502a739ec829281535cf6414940ad2e0318a4a056a7090c52502b4b8486292815adc14314940ad0e0a18a4a070e7410c5250296ba0c229281539cc6114940a9ae6308a4a06656118452502b4b80c22928153dcd4014940a98e6a00a4a045e7598e425022e3aac721281175db53909408ba
  | 16 => 0x86733a4c89084359dd56448421b8ee6b224210dc47359121086f1b82c890843781c16448421d4ce83224210ce676d5121086e339ea890843715cf54484219c8ed2a24210ea4649512108673bb2a890843391d95448421d48c8aa24210dc77355121086e239aa89084378dc15448421bc0e0aa24210ce67615121086e3398a890843715cc5448421bc4e02a24210de17015121086b2bacc69084359dd56348421b4ee8b1a4210da47458d21086f1b82c690843781c16348421d8ac631a4210ce676d4d21086e2baca690843b1d965348421e8ecb29a4210dc67494d2108763324a690843b11925348421e8eeaa9a4210ec76554d21087a3b2aa690843711d15348421d8cc8a9a4210ec46454d21087a3aa2a690843d155153484219ccec29a4210dc67314d21086e3bae8690843715d74348421d8ecba1a4210f4765d0d21087633268690843b119343484219cced21a4210ce57690d21087523248690843719ce43484219ceeca1a4210ce47650d21086b33a88690843595d44348421d48c821a4210dc77510d21087a33a88690843715d44348421e8aea21a4210d457510d2108763b288690843d1d944348421b8ce821a4210f867410d21087c3b208690843b19904348421d88c821a4210f846410d21087423208690843595d66048421aceeab024210da77458121086d23a2c09084371dcd6048421b88e6b024210dc67318121086e2b98c090843b858060484219ceec90ea010ec6634875008762b1a43a8043d154d21940218bee6b24a010c5c73592500862f39ec8a8043175cf6454021c3ec821aa010e1c6410d500862ebb4a628043879925314021c3ac9298a010c5f7654c500870f322a6280438759153140219ceec908a010ea6644845008752b224228043b198d2114021d8ac6908a010f4553484500863dbb2a0280438e5915014021ec242a80a010c5f7654c53d022ebb68729681175d84394b408deeca90a5a047671d9732d023ab8ecb99681175db43947408baec21ca3a04777654451d0237396cb98e811b5cb65cc7408bce7b2e43a045d73d9721d022f39ecb10e81175cf65887408bce7b2a43a045d73d9521d022f39eca10e81175cf6508740970e0b2043a054e72d9253902a6b96c929c81559c76494e40aaae3b24a72064d6218a53902ab388c529c81555c46294e40ab4e0314a72054e7218653902a6b90c329c81955846194e40ab4e030ca72054e7218253902a6b90c129c81559c46094e40aaae2304a72054f7259153902a6392c8a9c8155dc56454e40aa8e2b22a72051f745895390326b10c4a9c8147dd16154e40caac230aa72045f7654c539032d29ac121c819654f6050e40caca730ea52065553987529032b29ac3a94819554d61d4a40acce3a94a52045e73185529022eb98c2a9481175da5314a408beeca98a5204
  | 17 => 0x1843175da6510c21a3ce83288610d4e7219443086ab388ca21843569c06510c21ab2e03288610c5d75990430862ebb6a82184317dda5410c218beecaa08610d5b7055043086ac382a821843179d85410c218baec2a08610d5a7015043086acb80a82184317dcd64948218b8e6b24a410d68705534208726b2aa7a1043535d743d0821a9aea21e8410d6575d87420862f39ecb21043175cf65908218baeb31c8410c5f7558e420862fbb4a721043175da53908218beeca9c8410c5d7654e420862f3b4a6a1043171da53508218bceca9a8410c5c7654d420872b29ec2a10439554f6150821cb4a7b028410e5953d81420872d298c0a10439654c6050821caaa73088410e55535844208637bb2a8210435a1c15410821e1aa92988410d4d75d0c4208726b2e8621043535d44310821c9aca2188410f0d5410c4208637baac22104339dd56110821cceeab088410ec6535844208762a9ac221043b1d0d6110821d8886b088410e55535863208726b2a64190439594d610c821d8a64b086410c5f73592510862e39ac9288435c1c154d0421caacaa9e8210d5575d0f41086aaba887a0843595d762d0421acaea2168210c5e73d96410862eb9ecb20843175d663904218beeab1c8210c5f7694e410862ebb4a72084317dd953904218baeca9c8210c5e7694d410862e3b4a6a0843179d953504218b8eca9a8210e4e53d894108726a9ec4a08439394c6250421c9aa63128210e5a53d81410872ca9ec0a08439694c6050421cb2a63028210c5e73994410862eb9cca20843179cc65104218bae63288210e4d539884108726a9ac4208431ddd95410421ae0e0aa08210e556594c410878aaa4a620843955955310421aaaeba188210e5565d0c41086aaba88620843955944310421e2aa82188210c77755884108673baac42084399dd56210421d8ca6b108210ec5535884108763a1ac420843b110d6210421ccacba108210d65751084108732b288420843e110c4210421c9aa6b146210e4e53588310872ab2a6218843b1589310c421a9aea21e4210ea664d072108636bb4a510843555d443884218eaed2944210ea664d0a2108636bacc89084393d965348421c9ecaa9a4210e4f65d0d21086a6ba8869084393d944348421d18c821a4210ea464d0521086733b48290843719ce4148421b8ae720a4210ce47650521086e3b9a8290843711cd4148421bc6e0a0a4210de070505210863abacc89084395d965348421caecaa9a4210e5765d0d21086aaba8869084395d944348421d28c821a4210ea464d0921086733b48490843719ce4248421b8ae72124210ce47650921086e3b9a8490843711cd4248421bc6e0a124210de0705092108732baeca90843399d36548421cccedb2a4210dc673d9121086e2b9ec890843595d664484219caeb3224210e6575991210
  | 18 => 0x210d219c8e2b108690c7475584434872a29ac221a43391c96110d21a3ce9b288690d5b7059443486ac382ca21a43479d06510d21ab4e03288690d5970194434868f3acc821a43175db5410d21a3aedaa08690e1d76d50434868f3a4a821a4317dd95410d21a9ee4aa08690d577155043486adb82a821a43561c15410d21a3cea2a08690d1f76150434868ebb0a821a43c31526210d21a98eab108690e4c6558843487862a2c421a43711c56210d21e28a93088690d5475584434872a32ac221a43c51516110d21b88e4b088690ec562584434870faa0c6a1243871506350921c68a9b0a8490e3b54181424871c2a0c0a12439514d61cc9218bee6b2a8290c5c73595414870faa0c6a0a43871506350521c58a9b128290e3b54181414871c2a0c0a0a439314d62cc52187ee8b2a6290c3c74595314878a2a08790a43c315043885218bee6b26a090c5c73593504863dbb2a0282434e1d15014121ab0e6a80a090c5f73590504862e39ac828243179d263141218b8e8b18a090e587058c504862fbb68628243175db43141218beec218a090c5d7610c504862f39cc12a043175ce60950218bee6b04a810c5c735825408727b18c4aa0439318c6255021caec630aa810e54631855408732310c2aa04396d8f6055021cb0c7b02a810e6862d81540873830ec0aa04396d8c6055021cb0c6302a810e68621815408738308c0aa0430fdd95415021c72a8b00a810e4d63988540872ab1cc22a0439698e6015021cb2c7300a810e3a64580540872d31ac02a0439658d6015021cd4c4b00a810e7261580540870f324a929843879915494c21ab6e0aa4a610d587055253086ad380a929843565c05494c21a9ce5b24a610d5671d9253086ad386c929843565c36494c21ab4e0314a610d597018a53086ad380c329843565c06194c21a9ce4304a610d5671182530872cb00c129843179db5454c21c38c92a2a610e1c6455153086adb82a8a9843561c15454c218bcec2a2a610d5a7015153086acb80a8a9843531c96454c21aa8e2b22a610d5b7059153086ac382c8a984347dd16054c21a38e8b02a610d4c7258153086aa38ac0a9843965806054c218beeca98a610c7a70197430863cb80cba1843479d365d0c21c3ce9b2e8610d1e7419743086ad380cba1843565c065d0c21ab6e0aa68610d587055343086ad380a9a1843565c054d0c218f4e1b2c8610c7970d964308636bacc521843395c66290c21c9ca6b148610c75759864308672b94c3218439594d6190c218bee6b2a8610c7b70595430863c382caa1843179da5350c21c9aa7b128610c6d751894308672b88c4a18439554f6150c218eaea30a8610ce5721854308637390ca218431d9c46510c218f4e03288610c7970194430862ebb6a621843175d85310c21a3ce9b288610c5e74d94430870f3a6ca2
  | 19 => 0x132a8790c797099543c863d380ca21e431e5c06510f21ab4e02988790d597014c43c872629ac421e43479d36510f21a3ce83288790d5a7019443c86acb80ca21e43175db5410f21ab4e1aa08790d5970d5043c862fbb2a821e43931956210f21ab2e029e6590c5e7614d32c86acb80a69964317dd9530cb21ae4e1aa68390e2e5418941c863abb6a820e435c9c35410721e2ea82188390e4d5318931c862fb9ac928643171cd64943218bce7b22a190c5d73d9150c863dbb2a0286439658d5014321cacc730ea910e55639875488732b14c3aa4439698e60d5221cb2c7306a910e6962983548873930cc1aa4439698d60d5221cb2c6b06a910e7261583548862f39cc12a443175ce6095221c9ec7b12a910e4c63d89548861fbb2a82a4439958a6115221ccac530ea710c5f7654c538872ca9ac029c439958a6114e21cd2c5300a710e5a63580538873930ac029c431e9c265d0e218f2e132e8710d5a7014f43886acb80a7a1c43479d365d0e21ab4e132e8710d5970997438868f3a0cba1c43569c354d0e21ab2e1aa68710c7a70196438863cb80cb21c431e9c26550e218f2e132a8710c7a70194438863cb80ca21c43569c05310e21ab2e02988710e5453584438868f3a6ca21c43479d06510e21ab4e03288710d5970194438862ebb6a821c43569c35410e21ab2e1aa08710c5f76550438872a32ac221c435a9c354d0a21c6ca830a8510c6d76d5042886b5386a821443c3d504310a21caaa630a6510d597014f318862f3b0a698c43565c0534c6218beeca986310c5f73592508862e39ac928443179cf64542218bae7b22a110c7b76540508872cb1aa028443179ce60951218bae7304a890e1f6418d5448727b1ec4aa2439318f6255121caec7b0aa890e5463d85544872db1ec0aa2439618f6055121cd6c5b02a890e7361d81544871db20c0aa24396d8c6055121cb0c6302a890e6b621815448739b08c0aa2430fdd95415121a38e6aa0a890d3870550544862fb9ac02a243171cd6015121c3ae7b22a690e1f73191534870e326c6a9a438b1936254d21c68c9b0aa690e3b64d81534871c326c0a9a438ed906054d21c70c8302a690e5b631815348735b10c0a9a439cd846054d218beeca98a690d1c7454c53486ac382a629a431e9c365d0d218f2e1b2e8690d5b7054f43486ac382a7a1a43479d365d0d21ab4e1b2e8690d5970d97434868f3a0cba1a4353dc954d0d21aaee2aa68690d5b7055343486ac382a9a1a431b5cb6590d218eae3b2c8690c7a70d96434863cb86cb21a43175ce6550d218dee4b2a8690c7771595434863db82caa1a431e1c16550d218f6e0b288690c7870594434863d380ca21a431e5c06510d21a3ae7aa08690c5d7694c434868eba4a621a4347dd15310d21ab6e0a988690d587054c43486363aac421a439314d6
  | 20 => 0xf72580544c636392c02a2638d15161d0d31a9ee4aa68698d4c72553434c6adb82a9a1a63561c154d0d31e28a930e8698cd675987434c72b3acc3a1a639595261d0d31ca8a930e8698f1454587434c62fbb2a821a6353dc95410d31a98e4aa08698d5b70550434c6ac382a821a63879905410d319a8e2b108698cd471580434c637bb2a4292634b1d15214931ad0e0a90a498c7b70590524c63c382c829263535c84314931c38a8b1c8498cd47158e424c63d384caa12631e5c265509318f6e0b288498c7870594424c63d380ca212631e5c06510931c9ac62908498e3454584424c732292c221263359c664cc931c3cc82a66498cd471583324c66b38cc899263539ca544c931c38c82a26498d4e75d89324c6a73b0a499263939d8524c931c9cc82926498e4c64149324c66b3a8c299263959d4614c931caca830a6498e5454185324c70e2a6c6a0a638bd506250531c58a83128298e3b54181414c71c2a0c0a0a6387990548c5318f6eca80a098d3874540504c6b4392a0282631bdc964141318d8e4b20a098d597010c504c63db82c52a0631e1c162950318dee4b04a818c6c72582540c61fbb2a82a0639398d6215031ccac5308a818e6a62980540c734b14c02a0639698d6015031cd4c4b00a818e6962580540c73930ac02a063539c854d0c31a9ae42a68618d5a70153430c6acb80a9a1863479d36510c318beecaa08618d1e74150430c78b2a4c22186317dd56110c31e2ca8b088618cd775584430c72bbaac221863959516110c31ca8a8b088618d6a70d4a520c6aab8886a90631bdd952148318f4e132c8418c7970996420c66ab8cc7210639398d52908318f6e0b2a8418c7870595420c72631ca4a1063999486150831ccaa430a8418e6a52181420c734a90c0a1063879934394431c3ca931c8218c5f7558c410c70f324a998863535c854cc431ab2e02a66218c5d7694e310c63abb4a718863179d3654c4318baeb3226218c5c76951310c70e324a898863179d8544c431a9ae42a26218d5970151310c6aabac8298863351d9414c431d28c8a0a6218dc472505310c6e83828298863359da434c431aaeeaa1a6218d55758c9310c6b5396a128063555c443540318f6eca80a018e4e6398b54c8726b1cc5aa6439998961d5321cb4c7306a990e596398354c8735314c1aa6439c58660d5321cb4c6b06a990e596358354c8735312c1aa643179ce60953218bae7304a990e5763d8554c872a31ec2aa6430fdd95415321cccc4b08a990e666258753c862fbb2a629e439654d6014f21cccc4b08a790e716198053c872d31ac029e439a9896014f218f4e132e8790c797099743c86ad380a7a1e43565c053d0f21a3ce9b2e8790d5a7099743c86acb84cba1e43479d065d0f21ab4e1aa68790d5970d5343c863d380cb21e431e5c06590f218f4e
  | 21 => 0x6ac39a84282835cdc54214141ae0e2a10a0a0d72710c850506b8b886428283d4d0f4114141ea087a08a0a0d5a7390450506acb9c8228283c610e4114141ab6e6a08a0a0d587350450506b5b9282282835a1c941141418beeca98a620e4d53588531072ca9ac029883655c66410c418bce6302a420c5d731815210637bb2a4290839358d5214841cd2a4b00a420f0c43548421074a21ac2210831edc1654c8418f0e0b2a6420c7a70195321063cb80ca990838b191524c841caaa630a6420e6552185321062ebb68728883175d8439444187aed2a48220c7576952411070fb2e86a088387d944350441d18863128220e9843181411070fb2ec6a088387d946350441c5ecbb128220e2f651894110746318c4a08838ed976050441c76ca3028220e98631814110754310c0a0883659cf6450441caecbb1a8220e576518d411066b3b686a088395d974350441b2ce721a8220cd67610d411072bb2886a0883659d84350441d2cec21a8220e976510d411078bb2886a088399d976250441f0887b128220e94431894110733b28c4a0883b1d8c6250441d88c63128220f844318941107532a0c4a0883b1d0c6250441d4c863128220ea4431894110762218c4a0883a110c6250441ce6cbb028220f9043d814110770316c0a0883a510c6050441ce6ca3028220ed3631814110768318c0a0883e410c6050441dc6c43028220ee06218141107592a0c0a0883b4d0c6050441d64863028220eb0431814110768218c0a0883a410c60504418bce6312a020c5d73189501063dbb2a0280839658d5014041cd2c4a80a020e4e6398b54cc72731ac5aa6639998961d5331cb4c7306a998e6a6298354cc734b14c1aa6639c58660d5331cb4c6b06a998e6a6258354cc734b12c1aa663535c86395331ab2e031ca998c3f7655054cc72b31ac22a663539cb54d0f31a9ae5aa68798d5a70d5343cc6acb86a9a1e63539cb5410f31a9ae5aa08798d5a70d5043cc6acb86a821e6317dd95410f31e2ca93088798f165458443cc63db82c9296631e1c16494b318deeca90a598e695258052cc63d384cba16631e5c265d0b318f6e0b2a8598c787059542cc70e324a899663539ca544cb31c3ca831a8398c6f7259250cc636392c9286639318932543318f6eca80a198e696254050cc61fbb2a82a4639558e6115231e2ca930e8718f1654587438c71aaa0c2a1c63175db5410e31c38c821aa518c6f76548528c63db82caa14631e1c16550a31c3ca8b1c8318e1e64953318c70e32086a84631edd95014231c9ec7b12a898e2f64189544c727b18c4aa2639918b6155131cb6c7b02a898e6b62d81544c734316c0aa2638ed906055131cb6c6302a898e6b62181544c734310c0aa2639cd84605513187eecaa0a898d2c72550544c69c382a82a2631edc162151318f0e0b10a898c6
  | 22 => 0x2839358c5290941cc8a530c84a0c5e75d8d425062f3a8c6a1283179db53509418bcec29a84a0e4f63d49425072631ea4a128393d8c5250941c98c629284a0e5753d85425072a29ec2a12839914b6150941caea630a84a0e54531854250733a90c2a12831e9d76050941cb6a7b0284a0e5853d814250735a96c0a12839a14b60509418f4ea30284a0e5b53181425072c298c0a12839ad486050941cd0a430284a0c7b70597325063c382cb992831edc1658c9418f0e0b2c64a0c7a70d95325063cb86ca992831edc1650c9418f0e0b2864a0e54539843250732294c21928399149610c941aaceba1e82a0d567510f41507a3a98a5a0a83d114c52d0541e8e8629682a0f444314b415072731ea520a839358f5290541c9cc629482a0e4d6314a4150786218a520a83c314c52905418bce7316a0a0c5d7398b50506b5394a7a82835a5ca53d4141ad6e4a9ea0a0d687254f50506ad3ae87a8283569d443d4141e96a7a96a0a0f4853d4b50507a5a1ea5a8283d210f52d4141ab4e7296a0a0d597394b50506adb9aa5a8283561cd52d4141e96a6296a0a0f485314b50507a5a18a5a8283d210c52d4141ec0a5a0ea0a0d5a73d9350506acb9ec9a82835a9cb64d4141ad2e5b26a0a0f1a7410f50506ad39cc5a8283565ce62d4141cd6c5316a0a0d5a7390b50506acb9c85a82831edd942d4141ab6e6a16a0a0d587350b50506b9b8a85a82835c1c542d4141ab4e720ea0a0d59739075050727a9cc5282839314e6294141c9ea6b14a0a0e4c5358a505072731ea5282839358f5294141c9cc6294a0a0e4d6314a505072d31ea1282839658f5094141cd4c5a84a0a0e6962d42505062f3b6a6a8283179d85354141c9ea7b12a0a0e4c53d895050727a98c4a82839314c62541418dceda92a0a0e4f63d49505072631ea4a82831b9d85254141c9ec6292a0a0e4c63149505063dbb2a02828356dcd5014141ab0e6a80a0a0d6b7254050506b4392a0282839699753141418f2ed298a0a0d6a7294c50506b4b94a6282831edd95314141ad6e4a98a0a0d687254c505072d328a628283569d74314141ab4ea218a0a0e6a65d4850507a5a9ea428283d214f5214141e9687a90a0a0f4843d48505063cbb4a428283569ce5214141ab2e7290a0a0c7b7654850506adb9aa428283561cd5214141cd4ca290a0a0f4b5314850507a4298a428283d2d0c5214141e9086290a0a0f5353d0450507a829e8228283d8d4b4114141ec0a5a08a0a0f185390450507942948228283569cf6414141ab2e7b20a0a0d717118c50506b938c86282835c5c64314141ae6e2a18a0a0d707150c505078d3a086282834e5d06214141ab4e6310a0a0d59731885050734b10c4282835c5c46214141ab4e7210a0a0d597390850506b938c84282835c5c642141418f6eca10a0a0d5b735085050
  | 23 => 0x94032a9ae421aa01947b76540500ca2fbb2a629e83175db4394b418baec21ca5a0c6f7654852d063d386cb996831e5c365ccb418baeda1ca1a0c5d7610e50d063dbb2a028683539cb6494e41a9ae5b24a720d5a70d9253906acb86c929c83935886294e41aace2314a720d5a7018a53906acb80c529c83539c86194e41a9ae430ca720d5a7018653906acb80c329c83539c86094e41a9ae4304a720d5671182539072cb00c129c8353dc96454e41a98e4b22a720d5b7059153906ac382c8a9c8347dd16254e41c9ac4312a720d1f74581539072cb00c0a9c8317dd95314e41caca6b0c8720e5553d85439072d29cc1a94839654e60d4a41cb4a6b06a520e595358352906b5386a529483179cc6054a418bae6302a520c5d7694c529062fbb2a6294831bdd95214a418baeb31c8520c5f7558e429062ebb4a72148317dd95390a418baebb1a8520c5d7518d429062f3b4a6a1483171d95350a41caca7b0a8520e5553d85429072b298c2a14839554c6150a41ccca430a8520e5a53d81429072ca9ec0a14839694c6050a41cb2a63028520e6a521814290734a90c0a148387191534ca41a98e4a9a6520c7a70d94329063cb86ca19483535ca530ca41caca6b086520e1d6594f419070eb2aa7a0c839559653d0641caacaa9e8320e4e5398b5090726a9cc5a84839394d62d4241c9aa6b16a120d6a72d42509062f398c4a8483175cc62542418baed298a120c5f7654c509063dbb2a02848393d4e6294d41c9ea6b14a6a0e5b53982535072da9ac129a8317dd95314d41a9ee4a98a6a0d4c7254c53506adb82a629a83561c15314d41aaae2310a6a0d5571180535072a29cc321a8395d4c6150d418bce7306a4a0c5d7398352506b5384a7a92835a5c253d4941ad6e0a9ea4a0d687054f52506a73ae87a9283539d443d4941a9ce7b26a4a0d4d73d9352506b5386c9a92835a5c364d4941e1ce821ea4a0d4e7398352506a6b9cc1a92839ad8260d4941c9cc7a94a4a0e4d63d4a525072da9cc1292839614e6094941cd6a5304a4a0e5b53582525072c29ac1292839ad4960949418bceda9aa4a0c5e7614d525072da9ec0a92839614f6054941cb6a6302a4a0e58531815250637bb2a42928353dcd5214941a98e6a90a4a0d6b7054852506b4382a4292839399753149418daed298a4a0d6a7094c52506b4b84a6292831bdd95314941ad6e0a98a4a0d687054c5250727328a629283539d74314941a9cea218a4a0d4e73d9052506a6b9ec829283595c46314941acce3218a4a0d657190c52506b3b8a8629283591c54314941e1ce8218a4a0d4f7350452506a639a82292834b5d06014941a9ce6300a4a0d4d7318052506b2b88c0292839a58060149418bceb31c84a0c5c7558e425062ebb6a721283175d85390941c9cc7a9484a0e4d63d4a4250727318a521
  | 24 => 0x30284216c8431814210b44218c0a1085179cc60544428bae6302a221477765445110b2ab1aa2288859c54560144428bce630aa02145d731855010a3dbb2a0280859658d5014042ce2c2a80a0216566398754ccb32b14c3aa6659598d61d5332cb4c7306a9996696298354ccb3930cc1aa6659c58660d5332cb4c6b06a9996726158354ccb38b0ac1aa665555c46395332ab2e031ca99943f7655054ccb2731ac42a665559c754d0f32aaae3aa6879955a70d5343ccaacb86a9a1e65559c75410f32aaae3aa0879955a70d5043ccaacb86a821e6517dd95410f32e1ca9310879970e5458843ccb0f2a0c6a16651edc164947328f0e0b24a3994777654451ccb38a8ac028e651ddc564943328e8e2b24a19947b7654050ccb38b0aa0286650fdd95415232c9ac7310a91970e5498b438cb872a2c5a1c658b5506250e328baedaa0871961e5458e428cb0f324a9994658719043546328eeeca88a31961c6410d508ca3dbb2a02846595d8f6155132c6ec830aa89965763185544cb33b10c2aa26596d8f6055132ce6c3b02a89967061d81544cb1db20c0aa26596d8c6055132cd6c4302a89967361181544cb38308c0aa2650fdd95415132a68e2aa0a89953870550544ca3db82c22a2651e1c161151328eee2b00a89947471580544cb162a2c5a1a6555dc554d0d32aa8e2aa6869955b70553434caac382a9a1a65c315262d0d3299ceb316869964e7598b434cb272a4c5a1a659315262d0d32e18a8b16869945f76550434caabb8aa821a65551c55410d32ab6e0aa0869955870550434cb0f320a821a65331c96110d32998e4b00869961c54d8d424cb1baa0c2a12658d1506150932c76a8302849963854181424cb0f320a9192651ddd95114532a68e8a88a29957070544514ca3db82c828a651e1c16414532aaae2218a29947b76540504ca9c3a2a0282655c1c550141328eee2b20a09947471590504caacb8086282651edc161950328f0e0b0ca81947771582540ca3a38ac12a0650fdd95415032cacc6b08a81966662584540cb3930cc02a0659c5866015032cb4c6b00a81966a62580540cb3930ac02a0659c5856015032aace22a6861955571153430caad380a9a1865565c054d0c32a3ce9b28861945f76550430ca8f3a0a821865c39526210c328beeab10861970e54588430ca67baac42186593dd56210c32c9ca8b10861964c54588430cb0f32687290658795263908328beeab18841961e64953320caaab88a999065565c054cc8328baed29c641946d7694e320ca2f3a6ca99065175d6644c8328b8ed2a2641961c64951320ca2f3b0a899065555c4544c832ab2e02a2641954d75909320ca663b28499065a3191424c832b88e2a1264195c870509320ca673b4869906553dd5434c832ae4e1a8ca21954d7210d510ca3bbb2a2288655c9c750
  | 25 => 0x75d0f5050aad3a887a8285d4d4f51d4142ea0a7a8ea0a175343d475050ba821ea3a8285569ce51d4142ab2e728ea0a155b735475050aac39aa3a8285d4d4c51d4142ea0a628ea0a1753431475050ba8218a3a8285d8d0851d4142ab4e7b26a0a155973d935050ab938ec9a82855c5c764d4142e34e821ea0a155a7390b5050aacb9c85a8285569ce61d4142ab2e730ea0a1673619875050b2ba9cc3282859514e6194142caea6b0ca0a1654535865050b2b31ea3282859558f5194142cacc628ca0a1655631465050b2d31ea1282859658f5094142ce4c3a84a0a167161d425050a2f3b6a6a8285179d85354142caea7b0aa0a165453d855050b2ba98c2a82859514c61541428eceda8aa0a165763d455050b2a31ea2a82851d9d85154142caec628aa0a1654631455050a3dbb2a02828556dcd5014142ab0e6a80a0a1573715405050ab838aa0282859699753141428f2ed298a0a15727194c5050ab8b8ca6282851edd95314142ae6e2a98a0a15707154c5050b2d328a628285569d74314142ab4ea218a0a174b53d085050ba429e8428285c614e4214142ce4cba88a0a175353d445050ba829ea228285d4d0f5114142ea087a88a0a176342d445050a3cbb4a228285569ce5114142ab2e7288a0a147b765445050aadb9aa228285561cd5114142ce4ca288a0a1753531445050ba8298a228285d4d0c5114142ea086288a0a1763421445050b99210a228285569cf6414142ab2e7b20a0a15697218c5050ab539486282855a5ca4314142ad6e4a18a0a15687250c5050b8d3a08628285d2d0f4214142e9087a10a0a155a739085050aacb9c8428285c610e4214142ab6e6a10a0a1558735085050ab9b8a84282855c1c54214142a72e8308a0a155a731845050aacb98c2282855a5c86114142ce2c2308a0a145f7654c5310b2aa9ac2298859654d6014c42b1ae5320862145d76d0e5210a2ebb087290850f5da54908428daed2a4842161f65d0d4210b0fb2886a1085a510c6150842d3086302842161f65d8d4210b0fb28c6a10858dd976150842c6eca30a8421694631854210b1db2ec0a10858ed946050842d30c630284216b0611814210ac739ec8a108593d976350842c9eca31a84214ce76d0d4210b27b2e86a1085639ce435084299cec21a842164f6510d4210ac73b086a1085a39d84350842d1eca21a842170f6510d4210b33b2ec2a1085e110f6150842d188630a8421667651854210b63b18c2a1085b118c6150842f088630a84216a6541854210b63a18c2a1085a990c6150842d488630a84216c4431854210b42218c2a10859ad976050842f1087b0284216e061d814210b46218c0a10859ad946050842d96c630284216c8631814210bc4218c0a1085b8d846050842dc0c230284216aa541814210b65a18c0a1085aa90c6050842d5086
  | 26 => 0x68b0ca02808717dd95014043c9ac4a80a021e55615405010e6dbb2a028087b25895014043da2c2a80a021d5b765405010f2dbb2a028087c69915014043e94c4a80a021e59625405010fa4b12a028087925895014043ea4c2a80a021e59615405010fa8b0aa0280879458550140438beeca98a7a145d76d0e51d0a2ebb08728e851ddd951147428baeda1ca1a145d7610e50d0a3dbb2a028685559c76494e42aaae3b24a72155a70d925390aacb86c929c85559c46294e42aaae2314a72155a7018a5390aacb80c529c85539c86194e42caac230ca72155a701865390aacb80c329c85539c86094e42aace2304a721555711825390b2cb00c129c8555dc56454e42aa8e2b22a72155b705915390aac382c8a9c8547dd16154e42caac230aa72151f745815390b2cb00c0a9c8517dd95314e42c9ca6b14872164d53d894390b0eb2ca7a14858759553d0a42c9acb29e852164d6554f4290b2d29cc1a8c859654e60d4642cb4a6b06a321659535835190ab9386a328c85179cc60546428bae6302a32145d7694c5190a2fbb2a628c851ddd95114642caca730ea121655539875090b2b29ac3a84859554d61d4242ae4e3a84a12145e731855090a2eb98c2a8485175da53142428beeca98a12147b765405090b2ba9cc329a8595d4d6194d42cb6a7304a6a165b535825350a2fbb2a629a8555dc55314d42aa8e2a98a6a155b7054c5350aac382a629a85535c86114d42a9ae4300a6a164c5398a4350b27a98c4a1a85539d743d0942a9cea21e84a145e739835150a2eb9cc1a8a855c9c253d4542ae2e129ea2a15737054f5150ab8382a7a8a85559d743d4542aacea21ea2a155673d935150aaab9ec9a8a855c9c364d4542ae2e1b26a2a17167410f5150aab39c85a8a85555ce42d4542aace7306a2a1555739835150b39b04c1a8a859598f5194542caac7a8ca2a165b539825150b2c29cc128a859cd466094542cb6a6b04a2a1658535825150b39a8ac128a85179db53545428bcec29aa2a165b53d815150b2c29ec0a8a8596d4c6054542cb0a6302a2a1477765445150aabb9aa228a85551cd5114542ae6e0a88a2a1570705445150b2b32ea628a851d5da5314542ae4e1298a2a15717094c5150a3bbb2a628a855cdc15314542ae0e0a98a2a16566514c5150aab3ae8628a85559d44314542e8ea7a10a2a174453d085150b8a29c8428a85559cf6414542aaae7b20a2a15657218c5150ab33948628a85595ca4314542acee4a18a2a15647250c5150b8b3a08628a85d1d0f4214542e8887a10a2a1556739085150aaab9c8428a85c510e4214542aaee6a10a2a1554735085150a9aba0c028a85559cc6014542aaae6300a2a1565721805150b38b00c028a85179ce61d41428bae730ea0a15727194f5050ab8b8ca7a82855cdc553d4142ae0e2a9ea0a155a
  | 27 => 0x14001000c0010008001001400000040050000001000000b000000200000010000003000000100040000008008001800000040000000002000000600040000004003000c000000400700000040000000002c001003000000080000028001000000000200010008005000000300080000000003000000000080000004003000400d8deeca90a5a1c777654451d0e3dbb2a028687535db5294b43c9aeda94a5a1f0e74d4a52d0e2fbb2a42968733dd95214b43c9cc5a96a3a1d5671d4b51d0eaabb6a328e87955db5194743e2ce9a8ca3a1c5f7654451d0e6bbb2a228e879398b52d4343ab4e1a96a1a1e5661d4750d0ead386a3a8687565db5094343cb2eda84a1a1f1a74d4250d0e2fbb2a02868736dd95014343acce3a94a521d6a70d4a5290e37bb2a429487599cb5194643ae4e1a8ca321c77765445190eb5396a1284875c9c750942438f6eca80a121c6f765485250eb238aa4292875a1c152149438eeeca88a2a1d64725445150eb8382a228a871edd95014143ad0e4a80a0a1d70715405050e1ebb4a921887175da5490c438deeca90a421e65525845210f34a92c0290871ddd95114443ccac4a88a221e71515805110e3dbb2a0280879a5895014043ce2c2a80a021e8d6218a5410f4ab08c32a087a65806095043a9ce52a2a421c5f765485210e67bb2a42908753dd95214843c9eeca90a421f0e645485210f4b324c229087d154a6114843d2ca9308a421e4d525845210f4b322c229087d15496114843d2ca8b08a421e57525845210f63292c229087955496114843d8aa4b08a421e45525845210f4d324c029087d254a6014843da4c3300a421ed1619805210f4d2a4c029087935496014843d34c8b00a421f49525805210f6930ac029087b45856014843d34a8b00a421e5b525805210f65292c029087965496014843d92a4b00a421e49525805210eab38ca8a8887931895254443aa8e2a92a221e8e649885110f472a4c428887a39916214443d1ca8b10a221e4d62d445110f62b14a22888717dd95114443c9ac4a88a221cd7765445110f62b12a22888755dd95114443caeeca88a221f16645445110fa3312a228887955895114443e8ac4a88a221e45625445110f4d324c028887b298a6014443d92c5300a221f51519805110f4d2a4c028887955456014443d34c8b00a221eca625805110f64b12c028887d45456014443d34a8b00a221e5b515805110f6928ac028887965456014443da2a2b00a221e51515805110ead384a8a8087931895254043ab0e0a92a021e54615455010eac382a2a8087a39926214043d1ca9310a021e8e645885010f472a2c428087a59926114043d8cc5308a021ec5629845010f4b2a4c228087a59916114043d8cc4b08a021ec5625845010f4b2a2c2280879358b5014043caac3a80a021ec9629405010f
  | 28 => 0x40040010001000000d0004000000c000000400000040060010000002000000080010008006000400000000050000000000000000000000000002000c00000040000000000000000000140010000004000800100180020000000000400500000040000000000000000000000004003000c000000400100000000000004000000600040010000000000400300000010004001000c00000040000018001000400200000000008004001400200000000010000002000100040000000001000400200100000020000000400300000000000007000000000040020000001000c00400140000004003000000300040030004003000000800040000000000000000a0004000000000000000000020003000000000000030004000000400000000060008003000c00300040020014001000000000000000004002000400000000000008001000000100000020048006000c00200000000000003000c009000c0020010002000000000000010004006000000000000020030006000c0010008000000000b000000200000010004001000c00000100000010007001c00100000000000001000000100140000000002001400400040010018009001800100000060000004000000200080000004001000000300000000000001000000200040080000000001400000100050008002000c000001c001000000000100030010003000c000000000100040010004000000000100000000000000000000100000000000000000800200000000008000000c000000400100080000004000000000100000000000001000400000040020000000000000100000000008000000c0000000001000000000080010008001000c00100080030000001000000000140000004000001400600000010000005000000100000000000000000c00000580000004000001800f0004004000800200040010000000000800300080000004003000c0020024005001000000000040000001000800000040000000001001400000000000010003005c001001400000000000000000001000100080030010000000000000000000000001000000a00080000000001001400200140010004002000400000080000000002000400000000030008001000000000180000018000001400000000080008001000c003001000100000060000002000c00000000000000000000000000000000000000000800000000000000000000001100000000000000000000000100000000000002c007000000000000000000002001000800100000018003000400b0008000000000000040000000003000c000000000400000010004003000000300000010018001000000000000010018000002c0030004001000400200000000014001000400100040010000003000c000002c002000000300000000008000
  | 29 => 0x60004000002400400000010008001000c002000400100000040008001000c004000000200040000004002000800000000000000001000000000040050004001000000600000000004000000400100080030004002002400000100060000001001000200000000000005000c004000400000000060000002001c0040004001000c00000080020008001000400000000010000000000400000080090000000000c00000140010000000000400000000000004000000000100140010000000000000600280000044003000000500000000008000000400000080040008000005800000040000000001001400100080020004001000400a000000000000010000003001400c000000100080000020002000c00300000000000000001000000080000000000000c00000000000000002000c00100080030000001000000000040020004006000800100040000004003002c00200080000004008003c00000080000000000001400000040000000001000000000000000008001001c000000000c0000000001800000080000014001001800100000010000001000000000000020004003000c00000000040004001000400300000000000004000800000080050004000002000000000060024001000400100000070000000000000100100010008003000000000000010000004000c013000c00300200010010008001c0070004001000000100000050000004002800000040000000000000c000000000000000030020003000000100000010000002000000000080000004000000400000200020008005000000000080010008002000000000000000000000000c003000400000000020000004000800000000050000000000000100080000000003000c0000008003000c00100200040014000000000400000030004008001c001000c001000800100080020008000000000100000020004000001800000000010008001000000100180000000002000400e00000000004000000000100080010000000001800000000050000009000000000000040010002000000100080000000000000c00f00180000000002000c001000400100040030000001000000000000010000002000c000000401300100010000001001c00100180000004000000400000100020000002001800400080000000003001c0080008002000800900040000008004000c0010028000001000000100000000003000000200000070000000000000100140010000000001400c0010000001c00100280000004000000000200040010000003001000000000000008000001400000080000000006000c00000180040008001000000000000030004001000000000000020014000000400000100000010000000400000000020004000000000000000030008000000c00300400010000001000
  | 30 => 0x169c77a0e6450d08bc3348be26a10e507948000000000054c800048480000000000619853090e00c000000001d206440000000000000065a9d54000223046122c81cf0c506c5a26a000084850b0000000000054080000000000000000000001f800000004c5164453b88120001cf24d580005d0082a34513ec434a10229d800056a0000045800000000002ce197c3539c040350aa283299824ad0000292827a39e22b661b0000000048c7f18f82000225235d88f200001740c817dc23302e48b8938a0fa80001c51970000031800001b839c8f200000bd606480000000000802241e3408d0c3109c9037a21d200017ac0000000484000039d00000958804638132e4a9800004c000000000000000efe00000003d11ec4211915e00014be1ec83f6000000000000000000000352992400012320000000000000069200002468000000000000000002e582267e99c9600000000000e96353216c54f0aac000073400000005ad000000000003ce1b927781e34000000007f99f015e00000000000000000027400004c481ba00004a4000000034993e600000000000f9a00000008b79154000013a000058638900000001be23b59034863936056613bc25d826e0000000000243e917000000011940b10000000000000003560001f7a3c205101ec00009108007000c0000008002000400000000000000000000000000080000010002001c000000000000000000000000000000300040000000000001c0010018000000c0000004001000c00600080050000001000800500000020004002000c004000400400000000004000000c00200100020000004001000000000000030000000800900040000000003000000000040010000000000c000000400000040000004000000000300080010004000000000000040010000000000800000000070030000000000000000030000000000000200000010010006000000c000c008000c0030000002000000000140000068000000c00000000000000000000000000000010010000000000000140000000005000000400000020000000000400100000000010002002000300000000000007001c00000180030000005000000200000000000000000000000080030014000000400000040020000002000c00000000050000000000800600040050000000001800600080030004004000000300180030014001000800500040000010001002c000003000c000000000000060004000000800000180000000002001400100040080014002000000200000000000000000000700000000010000000c008000400300040000008001000800200000060004001001800300000000000000000000000180030008000000800700040030004000000c0010010008000800100040010068000000400200000010018001000000
  | 31 => 0x224a000000000014687608c9234d000000000000000e867b311c2000228000007300000a3c000169e000000011816da00013e400000005b5000078614103e11c440001fac7fd96fc0000000000000082a800000000006a81036000000002d1d3c00000001d980000000000867800000000000000d7e0000000000025e00000005ee00004b0933200000000001d94029877a5b487ca398148816600001aa800042f000049290a40001d780001766000000000021967c209960fe1dc600000000000000000000000000007b916ae8218ce0000000000009fa0001fee47c8f1a2388c0c00000003fc80000000012188a0d20001d9e0000000000236600000007158272896204025989f41da00000000000134000000009a200010dc5368000000000000000000000000000000015f80006b100000001c0c0000000000000000020300001db4000046200000008bc011000000000000000000000058c878400021920e599fc2e800000001b5e00000005438604000000011a943a0000000368000000000000001bd846d1368454841688280001a981c867494a6281000000000004851698000000081ba31a32806e48e78974883850e3f5a21e1f68000000000000e9ad088480000001c5463d000000006ee0000000000089800000002dda1f2000000066300000000000000030c00002280000e426138000507955240200000000000626000001009d87da98ba70c9dd21b80000000002c0000000000000000000002e40bc8000000000023a81e48000000047400000006650000261851600001240000ed233f21308fc00006f78a060370f9e000112a0001832551941400000000000bbc02a800000000000000000000000000005aa59500000000000000000000000002df80003f109ea33380002c899da0001aaa0000c360000000000038c0000000000103c7ba8000000019e17a800008400000000000000000000000008bd000068ea1420001116000025a00a8000000000000019ae00000000000d1a00000000000a3a0550dfa27a00000001f1e16f8000000000086298ca6d080002c924163320aee82a0000000000026e800000000000000000000000000001020002364737987e4339fbe00003c00000000000000024280000001f46000236e42696ba00000e80332454000193800000008d18b827411692000047a000000086618d8000000075580000000000000000000000000000000000051c148000003c0e000258ca200000000001dd600000000001c9a689000000009220001cf41a1971000015aa7060caa0000000000000074600006f9800085900000001ba265517866911ae800006f47a214f04c980002fb960421f0c404b1224e0158bf6069217443c1f1a0000f18797000000000000b31972000000000000000000000000180600
  | 32 => 0x1a9c00000008a0800000013a804500de7d720200000fde80784e200000005441b0247508b82860ae48baa1e0000190a3e480002b80a4c000195c3b800007bc80001a80000000000000006dc4fe800051800001e5844c548a4447f202fa0001a348b5800086408f80c511628ef0000000000075e800000000000000000839000000016ca02a00000000000000000082c0000257000082d9c8e00000004e885d400000000000000746823e2d69d500000000890160a0000000000000091480008709bcc00000006f502120001c6e000000000001120000000678800000000007ed1f1c00011fc0000000478a08e0000be800000003ae000000000000000000000000000000000001e0e000000c000000075200005dc80002e981cc00018685b1823a0001b5a47b8c9604e0000000145800000000000bbe67b00a400007828498d2c84f8000000113665a18ae420212a0000c7a01f205e53a9346000000028da12e59706b256b000040a800075b0000000000084c8b7438e000086101c420f9a6e5fb99b00001c4e11f9f540001e240000000879160c000000000000005c3130800016e83610cc417880000000000083824a0000cfa2d500001cb00000001c647df00007bfa09a814167200000000000d9c634871013b0d244cd0000000000010700000001cfc43f00f400021506e41a8e46f17f400000008aa1592000028a000000019d00000000000000000000000000000000000000000000000000000339800000000001820000000000074a20c60000000000161c7b4998a8d00000451800000008d247b107024a8d1200000000000000788800000023c86b880001b38dc8169158a48e016c6e501be000000059a80005e10e10815800000980000001140000000000000007ba0000000000000000006f900000092290071800000000000000000000000000004880000c5a000000005d8000000000074c8000000000033f937455b00000000000283000000018203261aea4e3138272a80005a30dd41d7107800000004e48000722000000000002de959600000000001e6e000000000000ea79a8afa00000000001a9600000000000000000000000000001a006ca4d8800018a179800000002e6063652d0000022016a7a500000001cd885b8abe16896680000f2a0000000000191c3fb21886db86da00009984391d8e8c2a1ca3ec0ae27d021fc59d0000000000007080000000000000015245e8b6837000000001a8057e1d3e00000002279e38000000055000c21bf09901fb0000000000041a800081888688b9000067280007bf06b60001d9686f17827a58b8662c8bcc72d8000547a0022e20f6600016dc1428be0000000079a227636d079c87706c87b78662000020a0002176000000000022cc4b4800000000
  | 33 => 0x406000166c00000000000df82fe800057a8000275000043180000000a2c00003ce0ba121c000000002000008048000000000054522ca84484dc22191f000019040a617b60a7042677c8b8a0000000000000001296ec000000017d091e000191e00000000001e1449a80007c0059633715de8151ad257680000000f3000000001ba05040000e800cf000000009360002462130947c6541f8a000036a000025811980001f4800079009e4000000000000220b180000f800000810eb428017c03f915cc2f60d5a5cf0a020600000853011a00000f80000000000000007f122e43d93de000066e300907200000008f016346bb0af68119f880d895ae7620000000169a00000004ae0000000000000000008ff800000000004b680b08e185fa8f70000000000000019f8632000000000002aa000000000007dc96a8000234872b9f9a0001208000133000018ec00000007ac8f588821b9e8930000000000000000000000000000000000000001d3222600000002ed000000000004fd097a0001a7e00023960000000000069c00000006e281de000000028200000000000221000047e00005e4000000000000000e7600000001508000218000026f8000000000027f989a0638000000000014f000000005bc00000000001dfe0000000066800022f800027121c4000182404f8eee29fa1d600023e400000008298000000000057d1c1252c00006ad8ac80bc000000001862cba0cc00000000000000000000051c000000000000000ecc410203433b015883617c83ac1bc6000000081480007510fb8000167691221441fd908a00011f600000000002154000116e000000000000000000000000000000023ac00020067a7038888114d200000000000f6c0000000000191400015440001b7e09d000039e920e0001328000126e00000000000612245242a2f4178a0001b0603e800012b21d83f32010000087405b859a646a2247cf130e00000000001c86000000020080000000386282800000000000000000027000000000000001118000000000000000001b4457f9e903038e5a48089028e3993600012e400000002b58000000000000015e6000000000013187be800000000000001f6200020600000000000000000000000000c8e76c80000001a400000000000000047980000000000355800000000000001da800000000001a002ec1e98000129a60480000000b6e00000000001fd43589c72000000000005c60000000700800000000001731a6a716000035b91564c1800026c80000000d9e4c288c87b500007ab21482769d5e5540000000000000000002ca0000000232c6cb14aa85680000d80000678000000000000000fba0000acc00013865e806d854a052a000059054800000001dc4000000026304060000e0400000000338f02065000000004860
  | 34 => 0x8de97548ba093a33181d02d4904400009f62968d50000000000015d6000021e4b0000000019066f012f829c00005fb1e2e000015e0000b2600000000001e74000076e00000000000000855a2280001d2a00000000000000000000021391c800000003d28d4831a9cca6c29e9a73d910c000000000023a235800005a9800000000000000000000000051d80006f4800000000000000fae0001a0a05684c00000000000000000013365d6a00a3ef103a7bb8ff62620d28000081a0000000000000019d87a4000086e00000001710000000000071b07e60000000243832200016a400000006851616148800035b0000000110e000000080f000000000000000000000223a0000000000000000003342b3a1240000e30000000088c80008010000000000000000000000000000017c60600006be0000000000000000e20000000000000032b800000000000000e0e25a82c000016667f4989c7a31eca00000004350000897000028980000000000000000000000060001db6000053a000000000000000001e660000f98028841800020983a21ca60000a6c0000a880000000568000000000000000000000000000000009020000827000000000000000000000000080e0000000095082b1ee06f81420000000016e961e7178a5e000000020900002581c200001fae00000000000168000000031c14860c680008fa8000000141267d00001b5800000000005ed1f2c5a3800075006ba000000034298f600000005d22120000061a5e480004cb07cc000000000013b80000d1e000080a1bc07aa48c01d619693e000000fe000154e000000000013f20000eda456000017980000000fee729067e1f8800042d8000618000016296fa38d02480001f6600014e6147800000000000001eb80000000000000030d0000837800003f208a00000000001030000000048280001e9875063e1c3800000008f1000000018a8000202c000202a000000000021d41c2800000022ee0001438000000013e05f800000000001e764f09e06000000079b10646740c4a12380006db094c0000000000000000000000368a6600000007568c200000d368b68de0473000067c800028a8000107800000000000000000000081e00002bc6140000000000029e87ce2521b082e5107c61d00000001d74000142200000000eb0f2e763121e842800000015121f180000000000518882c5ff11a00c596cc00020ec5f580000001c40673800077d1c3600000000001e3661a800000000004041d1062a800079e0000273800000000002a90000741800000012f20000cf200000000000be6000000080e99623360000000000066f9f581a3101400008d80000000000000000000000001c267561c984ef8000000063200015ce00000000000000000028e5c08ad200018be154800068408720001
  | 35 => 0x13f80000000000167843800003f400000000000000000043e9f123ec8000000000027f0b40324142447910000160000747000038800b269c00000002286000128c0001a5000022a40000000000000000000000000000000188681f000062811de00004a05a2000000000000000000000000076700000000000000000000000001e3800000e000018800004230b9a00014440000a8e807000033a21fa00002b224a08400001a4a000000000002a400000000001ab231580000000bac00000000000af200005064760000489a17817080000000000000000000007be0000a4800000007ca80004e717780000e3e0000c040508000000000000020ea3a99e8400007d40001bdc8ac16f81c0000000000008b007a200003fc6d4a2368f4012e8a500002a49fea00008100000000000000000000000000ea400000000001b506c99fbc0530a1c00000000000fa4780800075c870e1d0199086800000000000000000000000005621ae08e22284000000000000005ab202849f000000000000ad0fe07b5a2ec00000006ab12fa71e000000000005c014f81bb0000605a0ae40f990033300000000000000238200006de0000000000000004300000000000000000000000007248000835981c12a0000000022400000005a197b044d0a566bc034677d92dc00000004ae85b885f8000000193e0000000000118a6bd98101560e5c83c8ef618d186448d16a02e78000000000000000003639c7e0000000414000015888a47690000000000000000007d9000000000ec1cd8b803a080006af20e8315209e2aa947200012d8000103200000000000000000000035d00340c900000000000000212861c00007ce93c64220000000000000000002d6146a4a104f00e4a2fc7ed80005a00000000000000000000000594000066c000000000000000000000000031c0000d5c00015d0000000000000002a092520000000652000087d00005920000000000000000002a700000b6800000010f20000000220800000001ea59f9a082c602d043099a8000000000000ca0001e7049387780000290201800000005ce070132a4a499c03a400000001e2a00000000000000000000000000000698000000000000008140040ff400023ae0000a3e0d1000000000007e50e560000b2a0000ce28e4800055992887390b4c23980006dd800000023e01840000000070c00023cc000061e8c31eda0000000000000000000000c9872223411ca40e0000000000082f00000081e443090066639074e00000004b1800007a1b86000000000018c60000000000206400a052e0000ec448d902200000000001a76090861400000000000000000000000017fa000007600021f8195136a7878000000000047020180000000000155e00000000000000000206a2a000006ed0d7a7b380000000000
  | 36 => 0x72880000d2186e37f909c0000000000000000000000000000000000030b80002721cda15282ba8b1000000000004c00000000000083d0000132995234b800000000008df074a58f800007c000011000000000000000000009f176a000238c6b300000001966000000000000000001dee03805ec00000001e400008dd800000012fc00000007f400d000000001701ac869b0ade323000033e0ac045c9f840001d8a0000a2464389628c912ca04b0000350000030c800000000008bd98d0000041a66f04ea82f836e000000000018b658c0dbe00000000000000000000a000000000007f200009c6000111a5f61a4e2a1000000000000000d20531a3b260c09ac0000aca000046e0000000000000000000000000e8e0000dd0000164223917ca6bd10201b98000000000000019d80520000000000089a243a0000b0e00020da77b1c8083c02ac3a11418000005a425000000000008b500003d400000000e920001e4a3350630000000036b03aa7f900001998ffa77390aa72c00000001c22099800000011d6000000000000000000000000000000016941fc16621c900000000000000000000012b0000000000000000000000675800000011a6000000015b00008dd00008cf13d22d900008999e7a00000005b2000024c1ef41579d4619e00001ff000051e800020f000000000000001dfc86980000001f8e00000000001baa783000000023f600000003f991a400000000001302374800054608ee37f06ea5058aec06712040b7800000008260001e4c3729f44000092e3d003fa000144e000162837a81340000e6275881567599a7464b10ea417965a0000000000021475a800063119b60000000000000061c80000000000000000023f89b80b09432000069e00012963f38a94506800016b0000000000000000000000000000000070700002350c8882e800000010d00002182000000000000003dc00d200000000000b1a00014dc00007b80000b325e590740000000000180c7f29cc2000000000000000db1ebc50004b2202068a03b8b8c520943c00000007d480009000ac44a2800000000005c60aba00000006e2000000000005e6a3f212f1d020fd13e258aa334299231401ba0ce00000a07f08df040617e8000000032700004b787ea000000016000000000ee40000000000012a7d080002c000006ef000000021ae0001180000000052b800000000006b900007068ca853380000001c8a0001d0e4d700002f1172a05900000de80000000db60000000128800042a0e1c4918000000000000000004c7000045b000000000000000000000000000002b03628830402866000003103bc06be329142e011951a0000000534143e71d811e0a218d6222178c0000000000000000000000000000739887e00000003e400000001b7839f09b4000
  | 37 => 0x23b441d80000001f1857500000170000062163600000003bf045865109de1a4800071280008951ddc08c1f2254f91be5c1000000000000000000000000065f9c9c000000000000000000000000000000000003301be800000000000000000075e26085f060983a005195f200000000000b5c00000002759a780000000000000000000006998000162000064411046c01ea04880000000153a00019168a58adc2548000000026c000001a32d00000000b0800010c0000029600000005d780004e691da000000053580009139bda11f000056c0000270108200003b20001b0458e00000000a9a529000044800003f480000000000000000000000007768000000046c00000000000000099000011e000000000000000000000000049100005028cc20fc043e3711a302a7952e362071639c0000000176e00010fe8c0974e264a1f631123a045a15868120892031000021517ce0e919e400000000001ea6000109e00000000000000612800000000002da80000000000000102871e80000000cb6318800000003540000000000000000000000000000000000455506d0000122490d0000000000000000000000000000000025e00005f08000000152a000000000018847d380003a7165200000007e6185c72e800000007e400015ca10081ee1be907e4bf8760000000000016f64bd84220000000000000000000002538000000000045408280001524000163a7a1964000000007798000039802e0000000000140856500003358000000175800017b20001bfa35a8000000180a00000000000000000049a000000000002b815f1f3800000001938000000234c000000000007e882505dc6a88000000000010c92220000c2a00000003f201002510f6400008a253d8368298a2921c18de25e900005f9063878485a60001c5256f0000000000000006bc79905ae1ff9b1255200001f818ce4f10000269800000000004059cee0000e9e4cf8fe25cb80000001f76407170882c87940001aa80000b7c00000009128000779000000000000a48d786d198fa52499ee7358af80f280000001276000000080f800000000d80000000000038000000000001ba400000000000000747893e0000f4228b906c5309b9c00006c6000000000000007f60000790a34e000000000002500000000000000062000003c7000052c8000000197638c80000108000000000023d000067d800022a81e28ec0000888008679880001d10bc00000b1227723507168000453800000000000000e08000000000000004df23328430000376055c186000000022620000000000000088d000043b0ff800000003b18000364000000000003cf98fc0001cce0111bb2000155c19e80007b098a486e208c0000bf8000000090100004e900004a616aa000000029c800000009f21940000000000
  | 38 => 0x61693962db0cda000047200000000000000753190c0000000000118c22c929c37d0d7000000004981b300b28000103800031e000000001268a222a61b100002f78030256091659f000000000007721006000000085a9f567c980008208000000001400000000001e0a000000007800002cb0e6c007800000000008fd0000000000000000000000000000000000000006e300004e980000a9a31200003ae8f50000000017a000000000000000000000000092061e8a225c780000000000000000000000004a0800042494cc8a600000001a7a0000eae0000000024088e00000001961b7c00004fc8c6000000011d005c159a00000000001bca6a1800018f8b487001d228ae9dca507004c7059d30351800000009d2000238a000000000000006858000000235415901a0397a23c0000000000079e611800043100003c180005bd07f40bf104c7ca17da000000038d92a85808df259400003de10a684398425d120e24d280000000000000000000000007db000010105c806d80001a680006e000000001b660000000000000090419ac176000000000000001d4265000005700000000000091009ae4eb8000000000000008ba000000066e0de600000002130fbe0000000000000029d23060000a546068752000009223380002d880006980000809800047aa2d25bc80000000000690800000000005270dde6b98dee0868540000049e78023563691ec00000000000000000000000000000000201a509889a00000006251f0674b0000000105600000000001a0658500000001ec687b800000000005a8800069c921a00000008f080008d613b20021b380000000000223818a82007e1994a0ef800069904440000c2c53900000000e1613795d265b0b6600019123ae800000000006830ddc0000ba400000006fe00003cc80004bb80000000000000000000000002f38a8a00000003e308d600005e8000000000000000001c3e00008ac000079a497860a014045e4ce059c00395d80dc00000001d90000145e00000000000cf035f07543e5800025580000000ab88e509f000000002a19fba03c8a78000000000001ca0001984000000048610f40002146499000076180000001aca709222c000214016c8000000045455680005b61f50000000000019fe0761428000193a4a50000000038e000225000000006961b400c000003cd8000000000085f0f34000087a0000d9657e80000001e1a00003f20001b2089b90900000000510000000005600f49c2800000005b598b8000000000006465ff80000000000000000000000000aa800000000007ad1fda00004764440c605d916f009300005b808340001c460000bfe8c580008528000000000000000007611a5e000000051480008e682b6547210019aa06c5bb84d24b9a1042d1000000589728b6000000
  | 39 => 0x440000000000000000000000f5c5140d1c0000aea0000000000017e528800060a23d610e888a000102614f9454000114a0001da01b4800064882d20aba2a048a00006c880000000000143227c22b8bba00000005d5800000003d063780000000cb8359000087980000001de26b0a0360d0211a4818de4026902c38098563a894c008a86a43439afc42d1ab400005260001fc015c80008e0000000000005ef00000001b54638800011200000001106381a3e80001a6888323ce6d380001250000000174c37180000000b3a2fa83e47c5962c4ab21b44fa0d000ce8c1000022061758b0a00000000002092000109646c800055b88fa0ba8f0a00000006209f0c19c8c8436883b46ff944267100007980000000173a0000000000000000000004658000000000010900be00016240000000000180400011b0000000010f0000000000000000005b08c1a0000282000000055a03900001d34000179e000040000003d6672000000015301511a285ce11dc12ba35c8c781203098e1800000007b40fa82b680002f4800081e8000000091254d8e9815d0d3a56d000000015907ea15b80001b4a0001daa3e000000001ada1138862916071e1a086cc304859e6038000206000000000003378f685bf807a0000000000000000000001451bf000000000000000000019800000003830000043800048f920c66711704530000000008c0000ac676c1d52190072001d1a987fe0af40000bb200009062b417ea0000000451102e00003c80000000000000000000004ed12e000000008350eb6000003e00019de000000026c000000000000000000000000000023607810234415000000014c458000723da9d4a75700007f81bc800008b000000001f08000000000069180004a41c6a00000000421c4c00000008ff000000011ae05108368e600004199a901541dae000000000004a6000150457d827615c2424000006a3a6800000000000000000000000091699dc04600002a5800000021720e88a902611fc42ea00005c900005191dea00000003de800000006241a600007fa105c0000bae5a40332811000000023be00000000000000000182c00018c08fe800000000000000000000000000005f200004e40000000000195e00000000000000000057613210e600021be0e1000061500000001d60000000001a1c68000000000000005b886b8000233a000087600000004d6087800000000000000000000000000000000000000000000023b659c000000003c2000000032011e05f815b200000002bf000000000008c118f20000000000000055ea4283b5028c8cf80000000000000177442b077e000000000000002ee000031c8000000000084600002f5135a2231f8c414a07215a943004f0f9c4451a124b2160e2c1a2be60b8000496000027804b0000031200000
  | 40 => 0x93800000006619fb08be0eca1c6875a24f000000000003d58000000000000017166a99b586668000775000000000000000000000000000000000002244000104e7e4800000000002650c5863a98402cf09a800000001c4924c00002f80000b0c0001c503421f0a3a31cc684b0dda816800000000f600000000000000000199e7b980020000000000000083094ba36c2122000000042e80004161dba0000d827dd0f1200000006b50ede000000000001ae03592167bd91244dc000000000000000000146000000000007b200000de16b63dc800078c11c67aa201481da0fe00004ce3999a5a00019980000000000000000000000000b780000000503000000020885d0800000022466cd00000000bfc015000034580004f713f06b7800000000ba00000001f00d306aea1aa4109bc4584862c00000004bc00983c9800000000000001eb68e41a1800000008c70000000000032f000000000003898c1400000000000d940000aa00001db841680008f287323f00000000000000000007de0df600006f67870000495876431a04f41448000000128622d80000000508000158e48a80000000000000000057a1bfc0f78000000000000000002f1800000009aa7e808a0000000025c072e20e80000001c2a00000007e59cc02381b6a5c280004e0135200000000000a983f62384000000000000006e120b8000216052517f8000140200015dc0000000000000000000000000000000000020000005f3145c0001d260001fdc00023680e600004e407081eb13ea3f712ae02f000000000007c91e265869a6285e800000009800000c1e00ca27200000000629a1c00015347ac10be0002310740000000000002169b9a08c98a24239e7286c0aae61623ee8578000466035c000198000004f200000000f500002f90000000218c77618ac00011324598d662490000000022e8c880000001d0a000000081a0642000135430e0000000000000000004f219261c998bc00000004679c3a0002426000072a000000000000000000000000096c67a00001dc0000177865e000000000004d673c1dc02bc0d5839a820c6258236412a34a000000030880000000bf00228000000000000015a40000000000000000000005b4096800000005fc89ca0001f14000000000010b834e1bf245d176c000000000000005818e2c0000000919000086a123a00002ec0000000000000073200000001a3c00000000001b28000015023c221c1871d088dc00003d69c0809516ce44785ee2d0a28c0001ffa44a12e2000000000000002161ba000023de34f0ac26a90000224193084580004fb80000001c824f6800000001e48139a5c64800000000000000200e7458000000000000000004b4000083014f487a1e5e60e000010800000001060834000000006f879380008df847000000008
  | 41 => 0x27e0000000000016a000000011fe00002e689d00000000f0413680ae89e9ea42af038a45f988a2c080007e8897e0c1000058f1b2a00000002179ab082880c800000002a98fa60001c8c000000000000000000000000000078f175207d10ca00003dc00000001408e1411a1c3c71083bc042a2e63329f8200000000d485002470000000000000013420d7873e00004420000000000000083e118e0000428000000000000005279e485a2837e00000000000a600dc8000000000000023784d30fda6808a4e000225a32ca3b878a00000001160000101a897800000008da50a9dc228e220000006fe000000077400000001c663549bf60001c625c8800000000000000000302000000000000001d2000000000001a385c8000087a800028500000000000230000015a075606594e088f8b56000000040100000002446000000000003e20001f5e163032c854800000000006839c6023a800000000000001a321921d7c00005280000000000000000000008c98000816000000000000001e3a07720781599bc238e84fe4aa978e3849f9c2508eb272a00ac00000007a48000237a2c63b082840000b703ce80000000000000000000000003dd8d06000127a2cd85ca000097c00000001680ee6000194c5e0000056981365f998ee0a7a3529081bae7448faa3d2024412080004ed82ee568881c0b2071c532139e8858000000195855f00000001afe00000006b70000000000000000008ee80004dd800000015060000000000000000000005cb000000000000000c0075b910a00000002431b2e00000004d20c3e000000000000001a3800041b80000af9b0c00000000001fa400000000000000000000025012ce89b00000001a2600000000000000000078683e9ef000006ac00013043c5000000020fc00000001e8000072b000000005d01899e1600000007a0878059315c600010b0000000000000b66d3000036a00000000f860000000000117c61309260000000000000000000000000000000129e0000000000000009722b200000000000000000000018e800000000000001a2c00015701f1091800000000001d9a000000000000000000d9a63c00007649f4c0000000000229a00000008ab133a3c3211e84f159e290876a87784be0000000000000000000000000538000000000000000000000000000055a800000000000001b5c00000001a41aae8090cea0000000000175c16390f838a8c6c000171a86e8000663908400020dc251a0001f40ba20000000000148400000002089d7028c80004968f161aba0b40000606312000006c148c000000019480004a0000065b89ee0000000321800000021c00cc0000812848a7e019fa0001b1049b00002708000558086461e000062d12740000dba000000000000005ee893406b000013101905200
  | 42 => 0xbca000000001e17344cf000000000000588000000000000000000000000000128e000054e31b8f0e0000000000000041a183e1f7878a737172832080000001a9223d9664000171420b9f5a00002d800000000000a8c000000045700000001b7a00014fc3e8800053e8000000000065688b4112805e1a5962e5a080000002422000000000000006008000000000073b0000000232a66586700060ee84f400002d78e4a5c48000000203290d80000000000727800044200000000000387800072f9c2e0001dcc0000374868800086180009070a166a2800088080000001f688af000000000003e500000001ad68470000000000001380008d680004ac80006d9000036e01aa52a1b6800011920001af24e600000b700001c116ea114204c4c792400000000000000000000000c217d40000000788000059e952c000000032c00006f4000030e9df028480000000000000039e77e00000001d244ff8000000100273a9e0800000000000000215800000000000a19ccc00000008cb90e800023d8000085c07ca08000000c67cb97a80001126000000000012001f5800000000000001eba7f980000000e447f88ec80002136000091036ba29e8cc068444e8f2c51d241a0ff9c0a6368d9866e800086b0a6e64a8798595900e0000000388957200008208d787468fe1f2060d086657f1b6000022b800021fe21c000082400006dd0d80617800000000005fd800000016bc07e800066c956200024660000f5e0000f24000000088a80000751d365b900002f700008bf9cd259280005b1080c5939cfe4d009a42ad800083d800000000000000000000155690c8b4a369821c00016b87be035a34c80000f6064a3410a5000012a400006e24509516000000000000000000128000000000000000748000000000000000000808fa0000000000000000000000000014a3fa158226809b600d816000000000001b1e8f68000000000000022780000000707800000000002cf80000000000000161060da2d0000000000000000002096000000037580003f08000000000029000006dc8338000179472c9bea5d1855a18b839a00000000000c5c0000000560000063980003e2800000000000000000000000000000000000c063c00000000216690600000000b160000f7e000000000000000000000000000069f00004f500005e993a08da83ba00014668c80000000031e80580002ba01e600000001b08000000219a00013784668000000138400000003a2800044b800069319321e200005dc00003951b4800001840000000000000022a11ba088989e000000000011f4000000005985365120000018240e5280000039000000004140000ae67cd030e2d39f90000000039b80005fc00006c3842e00000007ff800073e000000013ac000000000005d242c92e84d38fb4
  | 43 => 0x3dd138809a00003ab00000000000214800000000000002022000241423295640000000000000000000000fa0ab400000003b88b923a811aa16d228e00000005d40000000000000000000001ce23d50000000000000000008718d4234a92ea4f28fca11482d400000007db97c432ea29c0c18e7e4e51dbe6f591a200021b64fd8e48155a40652f00000000ebc0000000000000000000003bb00002ac0000563073a0000f8e6a7981e6c500006fb800000013220001fcc47a1cd471d11a831f00004ec03820d086643649ffc6408000307119c28a04360001cb4085853400019a40500c5e6088c0a3b3a1cc000000071709326cf01b253c80002c100007c380000000d8c8ab800052298b00000f52000200c75a140e10c0000000000000013d81ee980850d8a0e56703c68e99928000127009c0c767d280000000000000000000000004d1000000000002c7800000019c601f80000000f4c13e80000001fde27b084a2d19f362c4147e0001e3e0000000000000006f146c0000ca67b8a2ce000000007b000053a17e251b9876000000000000000000000000000062311ce00010ae00006d400000002309d3a0488bda10d0000000227e00000003190ffe00000000001a045cc89e63390000000095a5c394e209f818c3f50000000217071f1f607f58446525982a000187c1fb800025b800067999606be800024b0b1400000000001e560000000578243c428800070c000000000000000000000000016081325cc049037092d600015c232690e21ce22e01210000516800000000000000c4e193237213800000000000000245000018000000a1a2f0800000000000000000183800000000006e5a3a46cc89641ca113e1c087726241d3846092a008e00000001844000228a0000000000000000003a600000000001e800000000000000000000000000ad800003584331046000190812e97686fd0ab28b08000000000000022a23c7a3620d919a01ef0f2837b20c41530e68000000063f80007951c481521e5a8cd8000000000000000006c6188e000244c5ac9d9867a8742266a07000000003bc80001518000000000000000000000000131800000016c043b85e07fca25600000006ef81f61fe995635511b88c21dde000048010a8cf41f700004471098000137a000113000000006a5221456112a200000007ee00004079b3e5241ca000018e80000178000000045d87ae0001d7e90c21c85de9a565158f7c00024120000a2000008c45ef8718203947844b11b60001ba800016b000002a221089e20001e50000000006d09081ed1da25cd9e5810e02406509c8438691228d08000000000000000000000000000000000000000000d187aa8ffc0001abe0000000000000021100003bd0daa000015c000242c0001ce016c000029a000000000006cd837c000
  | 44 => 0x84014800045aa402000000000000000000c3c0000000000000000000000000db24bb0000000240a1b00c4685382ce0a01f103828000000057a56e80003930d864f0122c0000000000000083b80000000fac5710000440086c0000bec6a681a82629e463131a22440a1e270514468650b840000774000136e00000002ea800068f92661db0000000000000000000000b1c6e3973e29a83da00000006c900006b188320000000000000070392620001526000041219a136400000004d40a1e0001ebe000086a4c6808e19580000d980001d6056e00000002e380000bf832e00000000001f7e7c1113c0000c1677ea4568691ac04368e588f9849605c80000001b7000000007cc84087dc1e3230a0000000000038f221a47e930c18f00000000ad410300000000294734000000002f40001ed8229800000024600d305fc000000072e000000023284ee9f0272f000073121ec6309d6439180001a8800000005321271e9e0001b821790000842000000000000000000000194e000006200000000001bac00f00003cf039c000000000019787a380000d287a8000000055e000000007760000000501029a00000000001a1e000000000008c686000000000000000000000002a034f99cc0000ef80001a2e000098e4188cf633b9f300aa099c000000000015be0000000073962000000005421618155125c7f39186821125432780007fb0000000000059818924f59324000000000016be876800086c860270d12720000000000000000010d6000107a0000000867000018320e000004ee760178888602182911500000000000000000001ba6000000029f000000003cc9178f1000000000001f3e000000000012686c68000000165e0000000000000079f8000000000082923c600016088ad000000000000000a1008804d47a29ab81f600482dc8ea849410de28d0d5e12e07b60000efa10b1762000000063300000ee242e000065c000144c6ce8ec0119078c892032a000068814903ec0dd800023a1c06000000000000000000dce12a8a304ea8000000000000017aa7ea80000001b6227300004dca13479f00007b70c8a4df8000898138e00001063aa936c81f832889900943a5224231d00008b703b0000033e686800032b0762000000041212cc6b60cd089c131000000008aa949826793cc00018887e7800000014de1360000000000035a00007451a36393800000000005720816000022c54280008e712f42948b60094800074300000000fea2fd1f486c700000000000124a30e0b81a2016100000000000000176072500008c0199245e000000008380000ed03ba849800019aa093845c444811c2528f600f1000000000000000000000215c00011ac0001ea257b10a0000157681980004908000000177c04105f647119d42140f6e6ee80002e7000
  | 45 => 0x543009e000000065d0f620000000000193c0001964000000087410120001a520609dbc6a30000000000019f14d832500006a2000057c0d44091800013a0000000026a4b500007fc181423b0b34000040a000000052d94fe0001d2e00000000208000000000022597d26eda13a588a40c5918f220002338000000000014ac00009041fe00000000000614a3ec1648fb608195e43f182e28f492b600000003198d72884026201900000000a5c37303e600020e600000000000000000123c65e95b60000c5200009bc068a10613d8000000000000014d400014b80000000000000000000000000000456800000017c6000000000008dc6370000817194600007c87ec82f24219dac6ec052c000179c75395ee5c713200001ff40001bb88ea827818011380000000000000000000000000f8888880005528b2031f969600000004590000000114834880008d11c704f3954c0000e525dd97060000000000000087c000000000003d1895e076834e5f420c85789e2c1398394845162600000002bf800000000005d280008bc80000c093160000616000000000006b00000cbe00021383b60000000000000000000d4149a5b79c1000003b623f0d10000100c0001366000000000000003900000474800000000008108f4e000236c7ab851a0000000000154264b983a4ff166e76990246620000000000000003ee000000017f80b861200000000c180000b300001b560000000240000022518d438a02080000000000000068a9bec3fc000000000008560000000000000000000000c3000016e60000a5866d000088b80000000000000000000012bc1a50bf280b80001aa088000021ce0001eec11580000b580006e60b5075d991825503363b700004d784b41bc97ae00000000000000098077c64d000054e023c43206b400000000000000053968401b216200020740001ce8000030a00000006a098a652380008be800067092be0000000000000000017a2000000053b183c8f880000000000000000000000000000000784000000000000000000000045a00000004921a542ed85b6000000055d0e2e46200005f7800049f944a00000000070a4600000000000000000000085a000000020a000000000bd8000000000000000000ea157e36f10d85df8000000000073e80003af8000104165866980000000000176800000000000001c2c000000000000000000000000000000000006bb800000011901330000000000000018626f380005329558000000000017260000000000089c00012786b380000000000668807012d8000000000000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x15348421b40805515348421c25751904348421945879d44348421d0575d904348421c45759904348421a86849904348421c45751904348421d05751904348421c87751904348421e06751904348421c85751904348421e05751904348421c05751904348421945859cc6048421aa0845806048421ac0835806048421e056454d2114021e21644855014021c45625c46294e40c45725846194e40a458694d2108640d047494d2108640e804318b6150040e8043d886150040e80431886150040924845d52108430c88641c9404c030c90641c5404c030a458114d6210f20a45811956210f20b1281d504310320a518114d6010e20a51811956010e20b0681d504310a20a45811956210d20d08541c16210d20a51811956010d20d08541c96010d20a48855896010d20c48755896010d20e08545896010d20c14641c55454c20a14845846154c20b04815504310820a498510d6010820b10815504310020a498510d6210020b098510c4210020d097510c4210020e096510c4210020c0d751904348020c19751904348020949859cf6448020c88641cd5448020ca0641c55448020a888458c6348020ac08158c6348020c88741915348020a48865515348020d08745515348020e08645515348020b40815515348020c29751904348020949879d44348020d0975d904348020c49759904348020a8a849904348020c49751904348020d09751904348020c8b751904348020e0a751904348020c89751904348020e09751904348020c09751904348020949859cc6148020aa0845846148020ac0835846148020d097454c5148020d21745445148020949859ce4148020c88649ce41480208a8845d83148020a458214d6110f10a45821956110f10b0a82d504310310a498214d6010e10a49821956010e10b0682d504310610a45821956110d10d10541c16110d10a49821956010d10d10541c56010d10a50855856010d10c50755856010d10e10545856010d10c0c641c95454c10a0c845886254c10b04825504310410a518510d6010410b08825504310010a518510d6110010b118510c4110010d117510c4110010e116510c4110010c15751904344010c19751904344010951859cf6444010c90641cd5444010ca0641c95444010a908458c6344010ac08258c6344010c90741915344010a50865515344010d10745515344010e10645515344010b40825515344010c31751904344010951879d44344010d1175d904344010c51759904344010a92849904344010c51751904344010d11751904344010c93751904344010e12751904344010c91751904344010e11751904344010c11751904344010951859cc6244010aa0845886244010ac0835886244010d117454c5244010d21745485244010951859ce4244010c90649ce42440108b0845d83244010
  | 1 => 0x8a00164fe0015800000000000f0000005528005593550001cafce60b15020b800000d070000d8ec0000590687c00209d400610000000b5018390a5751800f6ad0784018050497d20ae0f84c8847199a092180f29d58846115486812f1acc8794d0c0e03c510847e2d1396800005d00000860000170005ca94f892031897a5b001386ea0020008a60200000016002ccd49c000c8f4af000880099000011c00000000000001286c002a000007e000000000278000000000a438004888c002f3700106000012000003b9a400005b0012c0031800745d000014cbc00000006f0025d6e001a8000000002a4b0464c1d004004e8000011412f814310000000000000000c100000ca015a23c0e004f908a287290500000600b0ac6c0e9c4da675822000804d898a00d00254407d12291542846000e40026048000029800008d00000001700000000000000008b331d91200498b800bb12ac496000ca853c3d00000010184006020000000060101c00030000014020400c0203030101a01000000405008182c0001000040600018020509800000501000020a008540405010240201008140000000080008c0d769d35294b43c15769d35194743c19769d35094343e41525866014843e41529856014843e41525856014843e41625466014443e42625456014443e41625456014443e41629855014043e42625855014043e41625855014043c51615c06194e42c51715806094e42e80431876050842e8043d846050842e80431846050842c84641c5424c832c88641c1424c832c49625c06294e41c49725806094e41e804318b6050441e8043d886050441e80431886050441c84641c9414c431c90641c1414c431a498014d6210f21a49801956210f21b1280d504310721a518014d6110e21a51801956110e21b0a80d504310a21a49801956210d21d04541c56210d21a51801956110d21d04541c96110d21a44855896110d21c44755896110d21e04545896110d21c18641c15454c21a18845806054c21b08805504310821a458510d6110821b10805504310421a458510d6210421b058510c4210421d057510c4210421e056510c4210421c0d751904348421c15751904348421945859cf6448421c84641cd5448421ca0641c15448421a848458c6348421ac08058c6348421c84741915348421a44865515348421d04745515348421e046455
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x1434a060d2e0088a3000758023043804861d15454d21087200e8402a8a9a4210e80190805515348421a02cbcea3208690843805861d253484219030110c3a2a8a9a40106401d0815515348020d0032102aa2a690041409979d46410d200830130a324e720a4010604218745515344010c803a104aa2a688021a00642095454d100428232f3a8c821a2008604614649ce4244010
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 42
  | 6 => 1899
  | 5 => 9841
  | 4 => 4660
  | 3 => 195
  | 2 => 15
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
  | 7 => packedAt gbK7 (770+((h/14+packedAt gbK7 (672+(h % 14)*7) 7) % 88)*7) 7
  | 6 => packedAt gbK6 (58869+((h/633+packedAt gbK6 (51273+(h % 633)*12) 12) % 2506)*12) 12
  | 5 => packedAt gbK5 (419878+((h/3280+packedAt gbK5 (373958+(h % 3280)*14) 14) % 15719)*15) 15
  | 4 => packedAt gbK4 (250082+((h/1553+packedAt gbK4 (228340+(h % 1553)*14) 14) % 9005)*14) 14
  | 3 => packedAt gbK3 (12285+((h/65+packedAt gbK3 (11700+(h % 65)*9) 9) % 311)*9) 9
  | 2 => packedAt gbK2 (1090+((h/5+packedAt gbK2 (1065+(h % 5)*5) 5) % 19)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc07ffe03ffffffc0fc1f83ff87ffffa238fff
  | 1 => 0xfff80fffc07ffffff001ffc1ff87fffc3c71ff
  | 2 => 0xfffff80fffffffe0001fff87fffc07e3f
  | 3 => 0xfffff0000000f01ffffffffe00007e07ff8038
  | 4 => 0xffffffffffff001fffffffffffff8007ffffc0
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x25506329850a124c02c8591a582a96ca2186db
  | 1 => 0x4832a54293142494b010ab48aa832b542c316d
  | 2 => 0x62a546850a264919555a021133304da6c05a36
  | 3 => 0x70c187162c5881de699d339c022271c7768038
  | 4 => 0x8306081830600e038e21c421c44400019b6d80
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfee88080fee88080fee88080fee88080fee88080fee88080fee88080fee88080fee88080fee88080fee88080fee88080fee88080fee88080fee88080fee88080, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12333
namespace PEqualNP.Outside.L_meta_12333
open PEqualNP.Outside.L_meta_12333.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 15 := bgb_2_0
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
theorem bgb_3_192 : Interval gbAtlas 3 192 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 195 := (concat (concat bgb_3_0 (concat bgb_3_32 bgb_3_64)) (concat (concat bgb_3_96 bgb_3_128) (concat bgb_3_160 bgb_3_192)))
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
theorem bgb_4_3904 : Interval gbAtlas 4 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3936 : Interval gbAtlas 4 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3968 : Interval gbAtlas 4 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4000 : Interval gbAtlas 4 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4032 : Interval gbAtlas 4 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4064 : Interval gbAtlas 4 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4096 : Interval gbAtlas 4 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4128 : Interval gbAtlas 4 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4160 : Interval gbAtlas 4 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4192 : Interval gbAtlas 4 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4224 : Interval gbAtlas 4 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4256 : Interval gbAtlas 4 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4288 : Interval gbAtlas 4 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4320 : Interval gbAtlas 4 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4352 : Interval gbAtlas 4 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4384 : Interval gbAtlas 4 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4416 : Interval gbAtlas 4 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4448 : Interval gbAtlas 4 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4480 : Interval gbAtlas 4 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4512 : Interval gbAtlas 4 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4544 : Interval gbAtlas 4 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4576 : Interval gbAtlas 4 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4608 : Interval gbAtlas 4 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4640 : Interval gbAtlas 4 4640 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 4660 := (concat (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)))) (concat (concat (concat bgb_4_288 bgb_4_320) (concat bgb_4_352 bgb_4_384)) (concat (concat bgb_4_416 bgb_4_448) (concat bgb_4_480 (concat bgb_4_512 bgb_4_544))))) (concat (concat (concat (concat bgb_4_576 bgb_4_608) (concat bgb_4_640 bgb_4_672)) (concat (concat bgb_4_704 bgb_4_736) (concat bgb_4_768 (concat bgb_4_800 bgb_4_832)))) (concat (concat (concat bgb_4_864 bgb_4_896) (concat bgb_4_928 bgb_4_960)) (concat (concat bgb_4_992 bgb_4_1024) (concat bgb_4_1056 (concat bgb_4_1088 bgb_4_1120)))))) (concat (concat (concat (concat (concat bgb_4_1152 bgb_4_1184) (concat bgb_4_1216 bgb_4_1248)) (concat (concat bgb_4_1280 bgb_4_1312) (concat bgb_4_1344 (concat bgb_4_1376 bgb_4_1408)))) (concat (concat (concat bgb_4_1440 bgb_4_1472) (concat bgb_4_1504 bgb_4_1536)) (concat (concat bgb_4_1568 bgb_4_1600) (concat bgb_4_1632 (concat bgb_4_1664 bgb_4_1696))))) (concat (concat (concat (concat bgb_4_1728 bgb_4_1760) (concat bgb_4_1792 bgb_4_1824)) (concat (concat bgb_4_1856 bgb_4_1888) (concat bgb_4_1920 (concat bgb_4_1952 bgb_4_1984)))) (concat (concat (concat bgb_4_2016 bgb_4_2048) (concat bgb_4_2080 (concat bgb_4_2112 bgb_4_2144))) (concat (concat bgb_4_2176 bgb_4_2208) (concat bgb_4_2240 (concat bgb_4_2272 bgb_4_2304))))))) (concat (concat (concat (concat (concat (concat bgb_4_2336 bgb_4_2368) (concat bgb_4_2400 bgb_4_2432)) (concat (concat bgb_4_2464 bgb_4_2496) (concat bgb_4_2528 (concat bgb_4_2560 bgb_4_2592)))) (concat (concat (concat bgb_4_2624 bgb_4_2656) (concat bgb_4_2688 bgb_4_2720)) (concat (concat bgb_4_2752 bgb_4_2784) (concat bgb_4_2816 (concat bgb_4_2848 bgb_4_2880))))) (concat (concat (concat (concat bgb_4_2912 bgb_4_2944) (concat bgb_4_2976 bgb_4_3008)) (concat (concat bgb_4_3040 bgb_4_3072) (concat bgb_4_3104 (concat bgb_4_3136 bgb_4_3168)))) (concat (concat (concat bgb_4_3200 bgb_4_3232) (concat bgb_4_3264 bgb_4_3296)) (concat (concat bgb_4_3328 bgb_4_3360) (concat bgb_4_3392 (concat bgb_4_3424 bgb_4_3456)))))) (concat (concat (concat (concat (concat bgb_4_3488 bgb_4_3520) (concat bgb_4_3552 bgb_4_3584)) (concat (concat bgb_4_3616 bgb_4_3648) (concat bgb_4_3680 (concat bgb_4_3712 bgb_4_3744)))) (concat (concat (concat bgb_4_3776 bgb_4_3808) (concat bgb_4_3840 bgb_4_3872)) (concat (concat bgb_4_3904 bgb_4_3936) (concat bgb_4_3968 (concat bgb_4_4000 bgb_4_4032))))) (concat (concat (concat (concat bgb_4_4064 bgb_4_4096) (concat bgb_4_4128 bgb_4_4160)) (concat (concat bgb_4_4192 bgb_4_4224) (concat bgb_4_4256 (concat bgb_4_4288 bgb_4_4320)))) (concat (concat (concat bgb_4_4352 bgb_4_4384) (concat bgb_4_4416 (concat bgb_4_4448 bgb_4_4480))) (concat (concat bgb_4_4512 bgb_4_4544) (concat bgb_4_4576 (concat bgb_4_4608 bgb_4_4640))))))))
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
theorem bgb_5_6656 : Interval gbAtlas 5 6656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6688 : Interval gbAtlas 5 6688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6720 : Interval gbAtlas 5 6720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6752 : Interval gbAtlas 5 6752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6784 : Interval gbAtlas 5 6784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6816 : Interval gbAtlas 5 6816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6848 : Interval gbAtlas 5 6848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6880 : Interval gbAtlas 5 6880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6912 : Interval gbAtlas 5 6912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6944 : Interval gbAtlas 5 6944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6976 : Interval gbAtlas 5 6976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7008 : Interval gbAtlas 5 7008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7040 : Interval gbAtlas 5 7040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7072 : Interval gbAtlas 5 7072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7104 : Interval gbAtlas 5 7104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7136 : Interval gbAtlas 5 7136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7168 : Interval gbAtlas 5 7168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7200 : Interval gbAtlas 5 7200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7232 : Interval gbAtlas 5 7232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7264 : Interval gbAtlas 5 7264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7296 : Interval gbAtlas 5 7296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7328 : Interval gbAtlas 5 7328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7360 : Interval gbAtlas 5 7360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7392 : Interval gbAtlas 5 7392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7424 : Interval gbAtlas 5 7424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7456 : Interval gbAtlas 5 7456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7488 : Interval gbAtlas 5 7488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7520 : Interval gbAtlas 5 7520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7552 : Interval gbAtlas 5 7552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7584 : Interval gbAtlas 5 7584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7616 : Interval gbAtlas 5 7616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7648 : Interval gbAtlas 5 7648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7680 : Interval gbAtlas 5 7680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7712 : Interval gbAtlas 5 7712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7744 : Interval gbAtlas 5 7744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7776 : Interval gbAtlas 5 7776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7808 : Interval gbAtlas 5 7808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7840 : Interval gbAtlas 5 7840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7872 : Interval gbAtlas 5 7872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7904 : Interval gbAtlas 5 7904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7936 : Interval gbAtlas 5 7936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7968 : Interval gbAtlas 5 7968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8000 : Interval gbAtlas 5 8000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8032 : Interval gbAtlas 5 8032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8064 : Interval gbAtlas 5 8064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8096 : Interval gbAtlas 5 8096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8128 : Interval gbAtlas 5 8128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8160 : Interval gbAtlas 5 8160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8192 : Interval gbAtlas 5 8192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8224 : Interval gbAtlas 5 8224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8256 : Interval gbAtlas 5 8256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8288 : Interval gbAtlas 5 8288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8320 : Interval gbAtlas 5 8320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8352 : Interval gbAtlas 5 8352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8384 : Interval gbAtlas 5 8384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8416 : Interval gbAtlas 5 8416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8448 : Interval gbAtlas 5 8448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8480 : Interval gbAtlas 5 8480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8512 : Interval gbAtlas 5 8512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8544 : Interval gbAtlas 5 8544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8576 : Interval gbAtlas 5 8576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8608 : Interval gbAtlas 5 8608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8640 : Interval gbAtlas 5 8640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8672 : Interval gbAtlas 5 8672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8704 : Interval gbAtlas 5 8704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8736 : Interval gbAtlas 5 8736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8768 : Interval gbAtlas 5 8768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8800 : Interval gbAtlas 5 8800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8832 : Interval gbAtlas 5 8832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8864 : Interval gbAtlas 5 8864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8896 : Interval gbAtlas 5 8896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8928 : Interval gbAtlas 5 8928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8960 : Interval gbAtlas 5 8960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8992 : Interval gbAtlas 5 8992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9024 : Interval gbAtlas 5 9024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9056 : Interval gbAtlas 5 9056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9088 : Interval gbAtlas 5 9088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9120 : Interval gbAtlas 5 9120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9152 : Interval gbAtlas 5 9152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9184 : Interval gbAtlas 5 9184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9216 : Interval gbAtlas 5 9216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9248 : Interval gbAtlas 5 9248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9280 : Interval gbAtlas 5 9280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9312 : Interval gbAtlas 5 9312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9344 : Interval gbAtlas 5 9344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9376 : Interval gbAtlas 5 9376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9408 : Interval gbAtlas 5 9408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9440 : Interval gbAtlas 5 9440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9472 : Interval gbAtlas 5 9472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9504 : Interval gbAtlas 5 9504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9536 : Interval gbAtlas 5 9536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9568 : Interval gbAtlas 5 9568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9600 : Interval gbAtlas 5 9600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9632 : Interval gbAtlas 5 9632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9664 : Interval gbAtlas 5 9664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9696 : Interval gbAtlas 5 9696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9728 : Interval gbAtlas 5 9728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9760 : Interval gbAtlas 5 9760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9792 : Interval gbAtlas 5 9792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9824 : Interval gbAtlas 5 9824 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 9841 := (concat (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 (concat bgb_5_384 bgb_5_416))) (concat (concat bgb_5_448 bgb_5_480) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))))) (concat (concat (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 (concat bgb_5_832 bgb_5_864)))) (concat (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024))) (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)))))) (concat (concat (concat (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)) (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)))) (concat (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632))) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792))))) (concat (concat (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952))) (concat (concat bgb_5_1984 bgb_5_2016) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112)))) (concat (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272))) (concat (concat bgb_5_2304 bgb_5_2336) (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432))))))) (concat (concat (concat (concat (concat (concat bgb_5_2464 bgb_5_2496) (concat bgb_5_2528 bgb_5_2560)) (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)))) (concat (concat (concat bgb_5_2752 bgb_5_2784) (concat bgb_5_2816 (concat bgb_5_2848 bgb_5_2880))) (concat (concat bgb_5_2912 bgb_5_2944) (concat bgb_5_2976 (concat bgb_5_3008 bgb_5_3040))))) (concat (concat (concat (concat bgb_5_3072 bgb_5_3104) (concat bgb_5_3136 bgb_5_3168)) (concat (concat bgb_5_3200 bgb_5_3232) (concat bgb_5_3264 (concat bgb_5_3296 bgb_5_3328)))) (concat (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 (concat bgb_5_3456 bgb_5_3488))) (concat (concat bgb_5_3520 bgb_5_3552) (concat bgb_5_3584 (concat bgb_5_3616 bgb_5_3648)))))) (concat (concat (concat (concat (concat bgb_5_3680 bgb_5_3712) (concat bgb_5_3744 bgb_5_3776)) (concat (concat bgb_5_3808 bgb_5_3840) (concat bgb_5_3872 (concat bgb_5_3904 bgb_5_3936)))) (concat (concat (concat bgb_5_3968 bgb_5_4000) (concat bgb_5_4032 (concat bgb_5_4064 bgb_5_4096))) (concat (concat bgb_5_4128 bgb_5_4160) (concat bgb_5_4192 (concat bgb_5_4224 bgb_5_4256))))) (concat (concat (concat (concat bgb_5_4288 bgb_5_4320) (concat bgb_5_4352 (concat bgb_5_4384 bgb_5_4416))) (concat (concat bgb_5_4448 bgb_5_4480) (concat bgb_5_4512 (concat bgb_5_4544 bgb_5_4576)))) (concat (concat (concat bgb_5_4608 bgb_5_4640) (concat bgb_5_4672 (concat bgb_5_4704 bgb_5_4736))) (concat (concat bgb_5_4768 bgb_5_4800) (concat bgb_5_4832 (concat bgb_5_4864 bgb_5_4896)))))))) (concat (concat (concat (concat (concat (concat (concat bgb_5_4928 bgb_5_4960) (concat bgb_5_4992 bgb_5_5024)) (concat (concat bgb_5_5056 bgb_5_5088) (concat bgb_5_5120 (concat bgb_5_5152 bgb_5_5184)))) (concat (concat (concat bgb_5_5216 bgb_5_5248) (concat bgb_5_5280 (concat bgb_5_5312 bgb_5_5344))) (concat (concat bgb_5_5376 bgb_5_5408) (concat bgb_5_5440 (concat bgb_5_5472 bgb_5_5504))))) (concat (concat (concat (concat bgb_5_5536 bgb_5_5568) (concat bgb_5_5600 bgb_5_5632)) (concat (concat bgb_5_5664 bgb_5_5696) (concat bgb_5_5728 (concat bgb_5_5760 bgb_5_5792)))) (concat (concat (concat bgb_5_5824 bgb_5_5856) (concat bgb_5_5888 (concat bgb_5_5920 bgb_5_5952))) (concat (concat bgb_5_5984 bgb_5_6016) (concat bgb_5_6048 (concat bgb_5_6080 bgb_5_6112)))))) (concat (concat (concat (concat (concat bgb_5_6144 bgb_5_6176) (concat bgb_5_6208 bgb_5_6240)) (concat (concat bgb_5_6272 bgb_5_6304) (concat bgb_5_6336 (concat bgb_5_6368 bgb_5_6400)))) (concat (concat (concat bgb_5_6432 bgb_5_6464) (concat bgb_5_6496 (concat bgb_5_6528 bgb_5_6560))) (concat (concat bgb_5_6592 bgb_5_6624) (concat bgb_5_6656 (concat bgb_5_6688 bgb_5_6720))))) (concat (concat (concat (concat bgb_5_6752 bgb_5_6784) (concat bgb_5_6816 (concat bgb_5_6848 bgb_5_6880))) (concat (concat bgb_5_6912 bgb_5_6944) (concat bgb_5_6976 (concat bgb_5_7008 bgb_5_7040)))) (concat (concat (concat bgb_5_7072 bgb_5_7104) (concat bgb_5_7136 (concat bgb_5_7168 bgb_5_7200))) (concat (concat bgb_5_7232 bgb_5_7264) (concat bgb_5_7296 (concat bgb_5_7328 bgb_5_7360))))))) (concat (concat (concat (concat (concat (concat bgb_5_7392 bgb_5_7424) (concat bgb_5_7456 bgb_5_7488)) (concat (concat bgb_5_7520 bgb_5_7552) (concat bgb_5_7584 (concat bgb_5_7616 bgb_5_7648)))) (concat (concat (concat bgb_5_7680 bgb_5_7712) (concat bgb_5_7744 (concat bgb_5_7776 bgb_5_7808))) (concat (concat bgb_5_7840 bgb_5_7872) (concat bgb_5_7904 (concat bgb_5_7936 bgb_5_7968))))) (concat (concat (concat (concat bgb_5_8000 bgb_5_8032) (concat bgb_5_8064 bgb_5_8096)) (concat (concat bgb_5_8128 bgb_5_8160) (concat bgb_5_8192 (concat bgb_5_8224 bgb_5_8256)))) (concat (concat (concat bgb_5_8288 bgb_5_8320) (concat bgb_5_8352 (concat bgb_5_8384 bgb_5_8416))) (concat (concat bgb_5_8448 bgb_5_8480) (concat bgb_5_8512 (concat bgb_5_8544 bgb_5_8576)))))) (concat (concat (concat (concat (concat bgb_5_8608 bgb_5_8640) (concat bgb_5_8672 bgb_5_8704)) (concat (concat bgb_5_8736 bgb_5_8768) (concat bgb_5_8800 (concat bgb_5_8832 bgb_5_8864)))) (concat (concat (concat bgb_5_8896 bgb_5_8928) (concat bgb_5_8960 (concat bgb_5_8992 bgb_5_9024))) (concat (concat bgb_5_9056 bgb_5_9088) (concat bgb_5_9120 (concat bgb_5_9152 bgb_5_9184))))) (concat (concat (concat (concat bgb_5_9216 bgb_5_9248) (concat bgb_5_9280 (concat bgb_5_9312 bgb_5_9344))) (concat (concat bgb_5_9376 bgb_5_9408) (concat bgb_5_9440 (concat bgb_5_9472 bgb_5_9504)))) (concat (concat (concat bgb_5_9536 bgb_5_9568) (concat bgb_5_9600 (concat bgb_5_9632 bgb_5_9664))) (concat (concat bgb_5_9696 bgb_5_9728) (concat bgb_5_9760 (concat bgb_5_9792 bgb_5_9824)))))))))
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
theorem bgb_6_1728 : Interval gbAtlas 6 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1760 : Interval gbAtlas 6 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1792 : Interval gbAtlas 6 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1824 : Interval gbAtlas 6 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1856 : Interval gbAtlas 6 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1888 : Interval gbAtlas 6 1888 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1899 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672))) (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800)) (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928))))) (concat (concat (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 bgb_6_1152))) (concat (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)) (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 bgb_6_1408)))) (concat (concat (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504)) (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 bgb_6_1632))) (concat (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760)) (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 42 := (concat bgb_7_0 bgb_7_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfee8fe80fee88080fee8fe80fee88080fee8fe80fee88080fee8fe80fee88080fee8fe80fee88080fee8fe80fee88080fee8fe80fee88080fee8fe80fee88080
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,9,41)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,9,41)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276682368 * 2 ^ 32 + 4276650112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12333.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,5]⟩,⟨.and,[0,2]⟩,⟨.or,[4,6]⟩,⟨.and,[3,8]⟩,⟨.or,[0,2]⟩,⟨.and,[8,10]⟩,⟨.or,[7,9]⟩,⟨.and,[1,11]⟩,⟨.or,[1,11]⟩,⟨.and,[12,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682368 * 2 ^ 32 + 4276650112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682368 * 2 ^ 32 + 4276650112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12333

open PEqualNP.Outside.L_meta_12333 in
theorem PEqualNP.Outside.L_meta_12333 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682368 * 2 ^ 32 + 4276650112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682368 * 2 ^ 32 + 4276650112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
