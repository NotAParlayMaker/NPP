import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12879.Model
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


end PEqualNP.Outside.L_meta_12879.Model

namespace PEqualNP.Outside.L_meta_12879
open PEqualNP.Outside.L_meta_12879.Model
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

end PEqualNP.Outside.L_meta_12879

namespace PEqualNP.Outside.L_meta_12879
open PEqualNP.Outside.L_meta_12879.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841fc41083fe62107f8c420fe98841fc31083fe42107f88420fe90841fc21082fca0107fd0020ff20041fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887dd0710ff20e21fd41c43f883887d10710ff98e21fe31c43ec63887f4c710fa98e21fc31c43fe43887f88710fb10e21fd21c43ea43887f08710ffa0621fe40c43fa81887f10310ff98621fe30c43fa61887f0c310ff90621fe20c43fa41887f08310ffaa4217f54843fca9085f95210df2a4213e54843faa9085f55210deaa4213d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff99421fe32843fa65087f0ca10bea8c21ff41843fc83087f50610fe20c21ff31843fc63087f4c610fe18c21ff21843fc43087f48610fe10c217e50843fe81087f90210fea0421fc40843fe61087f8c210fd18421fd30843f261087f0c210ff90421fe20843fa41087f08210ff88421f710843f621087fd5110bfaa221fe54442fca8887f55110beaa221fc54442f8a8887fd4d10bfa9a21fe53442fca6887f54d10bea9a21fc53442f8a6887fd0d10ff21a21fd43443f886887fd4910bfa9221fe52442fca4887f54910bea9221fc52442f8a4887fd0910ff21221fd42443f884887fcc910ff19221fd32443f864887fd0510fba0a21fe41443fa82887f10510fa20a21ff31443fc62887d8c510fe98a21f531443f862887fc8510ff10a21f621443fa42887d48510fe10a21ff40443fc80887f50110fe20221ff30443fc60887e8c110fe98221f930443f860887fc8110ff10221fd20443f840887fc4110fd88221fe10443ec20887fd5010bfaa021fe54042fca8087f55010beaa021fc54042f8a8087fd4c10bfa9821fe53042fca6087f54c10bea9821fc53042f8a6087fd0c10ff21821fd43043f886087fd4810bfa9021fe52042fca4087f54810bea9021fc52042f8a4087fd0810ff21021fd42043f884087fcc810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xe304c3bc60987fd5030bfaa061fe540c2fca8186f950309f2a061fd540c2faa8186f550309eaa061fc540c2f8a8185f94c30ffa1861fe430c3fa86187f10c30ffa9061fe520c2fca4187b94830b729061fd520c2faa4187b54830b6a9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830fe99061fc320c3fea2187f94430bf28861f6510c2eca2187f54430bea8861f5510c2eaa2187f14430ffa0861fe410c3fa82187f10430ff98861fe310c3fa62187f0c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7905f14f20ffa1e41fe43c83fa87907f10f20ffa1641fe42c83fa85907f10b20ff99641fe32c83dc65907f4cb20f699641fc32c83fea3907f94720bf28e41fd51c82faa3907f14720ffa0e41fe41c83fa83907f10720ff98e41fe31c83fa63907f0c720ff90e41fe21c83fa43907f08720ffa0641fe40c83fa81907f10320ff98641fe30c83fa61907f0c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ffa1c41fe43883fa87107f10e20bea9441ff42883de85107f90a20fea1441fc42883d885107fcca20ff19441fd32883f865107fd4620ff28c417e51883faa3105f54620fe28c41ff41883fc83107f50620fe20c41ff31883fc63107f4c620fe18c41ff21883fc43107f48620fe10c417e50883fe81107f90220fea0441fc40883fe61107f8c220fe98441fc30883fe41107bc8220fd90441ff54482fea8906fd51209faa241fe54482fca8907f55120beaa241fc54482f8a8906f151209e2a241ff53482fea6907f94d20bf29a41fd53482faa6907f14d20be29a41ff43483fc86907f50d20fe21a41ff42483fc84907f50920fe21241ff32483fc64907b8c920fe99241ed32483f864907fd4520bfa8a41fe51483faa2907f14520be28a41ff41483fc82907f50520fe20a41ff31483fc62907f4c520fe18a41ff21483fc42907f48520fe10a41ff40483fc80907f50120fe20241ff30483fc60907f4c120fe18241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041be540827ca8107f55020beaa041bd540827aa8107f15020be2a041ff53082fea6107f94c20bf29841de53082bca6107f54c20bea9841dd53082baa6107f14c20be29841ff43083fc86107f50c20fe218417e52083fe84107bd0820ff21041fd42083f884107b10820ff99041fe32083fa64107f0c820ffa8841fe51082fca2107d94420bb28841fd51082faa2107d54420baa8841fc51083fe82107f90420fea0
  | 2 => 0x3faa5205f54a40fe29481ff42903fc85206f90a40fea1481fc429037885207fcca40ff19481fd32903f865207fd4640ff28c817e51903eca3205d94640fea8c817d51903eaa3205d54640fe28c81ff41903fc83207f50640fe20c81ff31903fc63207f4c640fe18c81ff21903fc43207f48640fe10c817e50903fe81206fd0240fda0481ff53502fea6a07f94d40fea9a81fc53502f8a6a07fd0d40dfa1a81fe43503fa86a06f50d40fe21a81ff52502fea4a07bd4940b7a9281fe52503faa4a07f14940be29281ec52502d8a4a07fd0940dfa1281fe42503fa84a06f50940fe21281ff32503fc64a07f4c940fe19281ff51502fea2a07f94540fea8a81fc51502f8a2a07fd0540ff20a81be41503fa82a07f10540de20a81ff31503fc62a07f4c540fe18a81ff21503fc42a07f48540fe10a81ff40503f680a07f90140df202817e54103fea6207f94c40bf29881fd53102faa6207f14c40ffa1881fe43103fa86207f10c40ffa9081fe52102fca4207f54840bea9081fc52103fe84207f90840df21081fd42103f884206f10840ff99081fe32103fa64207f0c840ffa8881fe51102fca2207f54440bea8881fc51103fe82207f90440fea0881fc41103fe62207f8c440fe98881fc31103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9985fd5330ff2a6617e54cc3faa9985f55330fe2a6617c54cc3fe87987f90f30fea1e61fc43cc3fea5987f94b30bf29661fd52cc2faa5987f14b30ffa1661fe42cc3fa85987f10b30ff99661df32cc3fc65987f4cb30ee99661fc32cc3fea3987f94730bf28e61fd51cc2faa3987f14730ffa0e61fe41cc3fa83987f10730ff98e61fe31cc3fa63987f0c730ff90e61fe21cc3fa43987f08730ffa0661fe40cc3fa81987f10330ffaa4617f548c3fca9185f95230feaa4617d548c3f8a9185f15230bea9c61ff438c3fc87187f50e30fe21c61ff528c3fca5185f94a30fea94617d528c3f8a5187fd0a30ff21461fd428c3f885187fcca30ff19461fd328c3f865187fd4630ff28c617e518c3faa3185f54630fe28c61ff418c3fc83187f50630fe20c61ff318c3fc63187f4c630fe18c61ff218c3fc43187f48630fe10c617e508c3fe81187f90230fea0461fc408c3fe611877cc230fd98461ff544c2fea8987f95130bf2a261fd544c2faa8987f15130be2a261ff434c3fc86987f50d30fe21a61ff524c2fea4987f94930fea9261fc524c2f8a4987fd0930ff21261fd424c3f884987fcc930ef99261fe324c3fa6498774c930fe19261ff514c2fea2987f94530fea8a61fc514c2f8a2987fd0530ff20a61fd414c3f882987fcc530ff18a61fd314c3f862987fc8530ff10a61fd214c3f842987fd0130ff20261fd404c3f880987fcc130fd98261f
  | 3 => 0xa818df94c31ffa1863fe430c7fa8618ff10c31ffa9063fe520c6fca418fb94831b729063fd520c6faa418fb54831b6a9063fc520c7fe8418ff90831fea1063fc420c7fe6418ff8c831fe99063fc320c6fca218ffd0431fba0863fe410c7fa8218ff10431fa20863ff310c7be6218ff8c431fb18863fd310c7ba6218fd4c431ffa8063fe500c6fca018fe94031bd28063fd500c6faa018fe54031bca8063fc500c7fea990dfd5321ff2a6437e54c87faa990df55321fe2a6437c54c87fea790dfd4f21ff29e437e53c87faa790df54f21fe29e437c53c87fe8790ff90f21fea1e43fc43c87fe8590ff90b21fea1643fc42c87fe6590ff8cb21f719643fd32c87da6590ff0cb21ffa0e43fe41c87fa8390ff10721ff98e43fe31c87fa6390ff0c721ffa8643fe50c86fca190ff54321bea8643fc50c87fea910dfd5221ff2a4437e54887faa910df55221fe2a4437c54887fea710dfd4e21ff29c437e53887faa710df54e21fe29c437c53887fe8710ff90e21fea1c43fc43886faa510ffd0a21ff21443fd42887f88510ffcca21ff19443fd32887f86510df94621ffa0c43fe41887fa8310ff10621ff98c43fe31887fa6310ff0c621ff90c43ef21887ee4310ffd4221ff284437e50887faa110df54221fe28443ff54486fea890efd51219faa243fe54486fca890ff55121beaa243fc54486f8a890ef151219e2a243ff53486fea690ff94d21bf29a43fd53486faa690ff14d21be29a43ff43487fc8690ff50d21fe21a43ff42487fc8490ff50921fe21243ff32487fc6490fb8c921fe99243ed32487f86490ffd0521ff20a43fd41487f88290ffcc521ff18a43fd31487f86290ffc8521fb90a43fe21487dc4290ffd4121bfa8243fe50487faa090ff14121be28243ff54086fea810ff95021bf2a043fd54086faa810ff15021be2a043ff53086fea610ff94c21bf29843fd53086faa610ff14c21be29843ff43087fc8610ff50c21fe218437e52087fe8410ff90821fea1043fc42087fe6410ff8c821fe99043fc32086fca210ffd0421ff20843fd41087f88210ffcc421ff18843fd31087f86210ffc8421f790843fe21087ec4210ff48421f690843f521087fea010ff94021bf28043fd50086faa010ff14021ffa9e81fe53d02fca7a07f54f40bea9e81fc53d03fe87a06fd0f40ff21e81fd43d037a87a07f10f40ffa9681fe52d02fca5a07f54b40bea9681fc52d03fe85a06fd0b40ff21681fd42d037a85a07f10b40ff99681fe32d03fa65a07f0cb40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a07f90740df20e81fd41d03f883a06f10740ff98e81fe31d03fa63a07f0c740ff90e81fe21d03fa43a07f08740beaa481ff53903fca7205f94e40fea9c817d53903f8a7207fd0e40ff21c81fd43903f887207fd4a40ff294817e529
  | 4 => 0x7fcc832ef99065fe320cbdc64197f4c832ee99065ed320cbfea2197f94432bf28865fd510cafaa2197f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea7a0ff94f41bf29e83fd53d06faa7a0ff14f41ffa1e83bf43d07fc87a0ff50f41dea1e83fc43d07fea5a0ff94b41bf29683fd52d06faa5a0ff14b41ffa1683fe42d07fa85a0ff10b41ff99683fe32d07fa65a0ff0cb41ffa8683fe50d06fca1a0ff54341bea8683fc50d06faa920ffd4e41ff29c837e53907faa720df54e41fe29c83ff43907fc8720ef90e41fea1c83fc43907788720ffd4a41ff294837e52907faa520df54a41fe29483ff42907fc8520ef90a41fea1483fc42907788520ffcca41ff19483fd32907f86520df94641ffa0c83bf41907ee8320ffd4241ff284837e50907faa120df54241fe28483ff53506fea6a0ff94d41fea9a83fc53506f8a6a0ffd0d41dfa1a83fe43507fa86a0ef50d41fe21a83ff52506fea4a0ff94941fea9283fc52506f8a4a0ffd0941ff21283fd42507f884a0ffcc941ff19283fd32507f864a0ffd0541fba0a83fe415077c82a0ffd4141bfa8283fe50507faa0a0ff14141be282837e54107fea620ff94c41bf29883fd53106faa620ff14c41ffa1883fe431077c8620ff50c41fe21883bc43107fea420ff94841bf29083fd52106faa420ff14841ffa1083fe421077c8420ff50841fe21083bc42107fe6420ff8c841fe99083fc32106fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f541107fea020ff94041bf28083fd50106faa020ff14041ffaa6637f54cc7fca998df95331feaa6637d54cc7f8a998df15331ffa1e63fe43cc7fa8798ff10f31ffa9663fe52cc6fca598ff54b31bea9663fc52cc7fe8598ff90b31fea1663fc42cc7fe6598ff8cb31fe99663fc32cc7fe8398fdd0731ff20e63fd41cc7f88398fd10731ffa8663fe50cc6fca198ff54331bea8663fc50cc7fea918dfd5231ff2a4637e548c7faa918df55231fe2a4637c548c6faa718ffd0e31ff21c63fd438c7f88718ffd4a31ff294637e528c7faa518df54a31fe29463ff428c7fc8518ff50a31fe21463ff328c7fc6518ff4ca31fe194637e518c7fe8318ff90631fea0c63fc418c7fe6318f7cc631fb98c63ff508c7fca118df94231fea84637d508c7f8a118ffd5131bfaa263bf544c67ea898ff95131bf2a263fd544c6faa898ff15131be2a263bc544c678a898ffd0d31ff21a63fd434c7f88698ffd4931bfa9263fe524c7faa498ff14931be29263ff424c7fc8498ff50931fe21263ff324c7fc6498ff4c931fe19263ff414c7fc8298ff50531fe20a63ff314c7ee6298ff8c531ef18a63ff504c6fea098ff94131fea8263fc504c6f8a098ffd5031bfaa063fe540c6fca818ef950319f2a063fd540c6faa818ef550319eaa063fc540c6f8
  | 5 => 0xa43ff294877e5290fdca521db94a43fea94877d5290fdaa521db54a43fe29487ff5190ffca321df94643fea8c877d5190ff8a321ffd4243ff284877e5090ffaa121df54243fe28487ff4350fbe86a1ff90d43df21a87ff5250efea4a1ff94943fea9287fc5250ef8a4a1ffd4543bfa8a87f75150eeea2a1ff94543fea8a87fc5150ef8a2a1fd14543ba28a87ff5050efea0a1ff94143fea8287fc5050ef8a0a1df95043bf29887ff4310f7e8621ff90c43ef21887fd4310f7a8621f750c43ffa9087fe5210efca421ff54843bea9087fc5210ffea221ff94443bf28887fd5110efaa221ff14443ffa8087fe5010efca021ff54043bea8087fc5010ffea7a17f94f42bf29e85fd53d0afaa7a17f14f42ffa1e85fe43d0bfa87a17f10f42ffa8e85fe51d0afca3a17f54742bea8e85fc51d0bfea1a17f94342bf28685fd50d0afaa1a17f14342beaa485ff5390bfca7215f94e42fea9c857d5390bf8a7217fd0e42dfa1c85fe4390bfa87216f50e42fe21c857e5290bfe85216fd0a42f7a1485ff5190bfca3215f94642fea8c857d5190bf8a3217fd4242ff284857e5090bfaa1215f54242fe28485ff5350afea6a17f94d42fea9a85fc5350af8a6a17fd0d42ff21a85fd4350bf886a17fd0942f7a1285fe4250b7c84a17fd4542bfa8a85fe5150bfaa2a17f14542be28a85ff5050afea0a17f94142fea8285fc5050af8a0a15f95042ffa9885fe5310afca6217f54c42bea9885fc5310bfe86216fd0c42ff21885fd4310b7a86217f10c42bf29085ff4210b7e84217f90842f721085fd4210b7a84217b50842ffa8885fe5110afca2217f54442bea8885fc5110bfea0217f94042bf28085fd5010afaa0217f14042ffaa6657f54ccbfca9995f95332df2a6653e54ccbfaa9995f55332deaa6653d54ccbf8a9995f15332ffa1e65fe43ccbfa87997f10f32ffa1665fe42ccbfa85997f10b32ffa8e65fe51ccafca3997f54732bea8e65fc51ccbfea1997f94332bf28665fd50ccafaa1997f14332ffaa4657f548cbfca9195f95232feaa4657d548cbf8a9195f15232bea9c65ff438cbfc87197f50e32fe21c657e528cbfe85197bd0a32ff21465fd428cbf885197b10a32ff99465df328cbde65197fd4632ff28c657e518cbfaa3195f54632fe28c65ff508cbfca1195f94232fea84657d508cbf8a1197fd5132bfaa265fe544cafca8997f55132beaa265fc544caf8a8997fd0d32ff21a65fd434cbf886997fd0932f7a1265fe424cbfa84997f10932f621265ff324cbde64997f8c932ef19265ff514cafea2997f94532fea8a65fc514caf8a2997fd4132bfa8265fe504cbfaa0997f14132be28265ff540cafea8197f95032bf2a065fd540cafaa8197f15032be2a0657e530cbfe86197f90c32fea1865fc430cafca4197fd0832ff21065fd420cbf88419
  | 6 => 0x768ccc785320006ded8015e04a00018e95e9100000008c800200700600000000000600b00400700100100100200100200100100300000200e00000701201000200700100401000000200400d00401500000100601800400200200a00000100400000200700d00700000001700700c00700e00700700100500100f00400100000201500c00000001800100700a00102400601d00200701100001300000000000001201100f00a00100400100100000100700000100001300400700103a01100000203500000000000c02800103b00f00600a00000001b00000000d00200d00000100001500300d00f02e00700c00400200200700700000000400b00000000100000300000000700100100f00200100000600600600000100601100000400601300000000100000900000600200200000100100000501300001300000400500201200005001101300000600401b02100000300500000500000200000700201f00000900100001100000000101c00100f00700f00e00401400401e00001703100c00300101400000000000200000000100500700000000000500a00600500000f00100000300200000200400000500300e00300200400000000800000100900400500000600d01700a00000100100000e00c00200000201300a00000202000400000801b00600000500000300000000d00600200300801a00100000900000200200000502600400000100300600001500000700100000400100100000000000000c00000000300800600000900600001000000000000300e00b00001a00400000000e00b00900000500100000100c00200000000200800900700600201100400000200d00100000700300300100000100100300000b00500a00300100000000000000000400702d00000f00a01000000200000500300400000300000100101900601000900000600001100300600800001000401000900000500b00200202800100500500000000000b00900000200001300700400d00c00800100a00e00000502100700600000200300300000800b00700e00c00100a01700000000700401100d00600d01b01b00300300d00000900000001200100100000000100000100200100100200f01000300200400901101200300000300001e00001600300100000200000200d00000000200001300101d00300100200300b00602200000600700300700101300e00b00000000100100001200600200500100000000900000001700000100300000c00600200001100000600200200400100000600000f00100300100600000000400101802000100700a011002ffa9687fe52d0efca5a1ff54b43bea9687fc52d0ffea3a1ff94743bf28e87fd51d0efaa3a1ff14743ffa8687fe50d0efca1a1ff54343bea8687fc50d0efaa921df94e43ffa1c87bf4390fbe8721ffd4
  | 7 => 0xc458ba80d24b403a93e6880000003245e200000a0000002a4354000b981b04785949d2000b423f8b0431a07600026000027e00042a6fc000d782e05b2926000000942128a2288a0000000000000000007ea0000000000000007e60b000061a5c8a4c000a48000000d8a50e232a64c3c922038476780000b26d227da7a06aac14046b9a9b837ed8e602dd2e3882821c7a8d6257a000dd863a00c00000018a69e940000000538662c0e41e2e400061ce10b565280002bc5f85fa5b00080001cc950000d82000c907e2584000cda28ed5c702b4ac06bea0fc0b20f60003c88667349965daa4aa32146824808430000044cd62c8490ca48a01d20e694e8e6bf27b0a5805453cda8bc65a20a01d69febda80c000dae9c020c872bb6b6e0006a20006ac000da45822f443e4dcd6a42e14cbc80000000000008e298835e63c000bf41a0bb83502d8d44332056d70daa0b8cce0cecbe644b1674c5502aa6a8c46982314a349c4a564f668ccf67c0e5ca8c9fc3260e40000008b2914a0acfe10a7d225e5cad5ed9c8aea2a00054c4daac21d44f42702fc686d062cc666abe096876700b5ee3e01e5d4516a7ac68d7e726a7ccaa3b414a0001b200083c74a60ce126d83d07303ac9aec4800000052e5685f20ee3fa12c764ce04200d01be0002ce0005d0362962000000000a0882e000000000000aac0003c413ae5eb4025c00033e000000000dc4cc00008861a84f2000b1a000c26cb20e061227ca1e8fa0007620a87560000002745d26dc000000000d76802000448b76000000000e44d7c0005f01203f6000000dccafe098000000438000898000000010000410c9479c00066a8ca1680000008ec5eebdc00087039e358264e2c27aba6bbe0000000002e60000000006100023d4a900fe000000508ae8b5c09a9ecdc68c69ce58aca8424cccd8c81438c7a619e2f6a1a6ecada000ab41900280009bec664e40000000000006404a04c277000001a7de2ec000c400005ec00044c6541f0074600000714b887b2000ad4d966c077ee5a00029e0006600002bed7453e000000164ddc0005bc0000000002c6004000bc0b1275c90840e0009dc3cc8d20009c8cec7b87ae6300000000009166964aa242e34e3a3eec24a3ed2e0000ba000570a9a5441fc00000000000080a000000e06000e1802c0000004008302ea3a04429e4d4a000aec000368a8487849ee48af8a66000b50c6c0786a4ac898e65058c0c42d00c0000cde000206c70e2e2b80003b6000180000000000918e66000b600009ac47c2dc00087400016c6f27b60004f0e0087e17a5428ee3ae776928b22cc85e0000db69bca9c00072eaaab0e526d58dbe4cade84bcc5e41867059a97a9e02301de068b3e0222203da638c2cc7cdc80002169241eaae000015277c738ad60008c4b9e38edf20000c250a0009
  | 8 => 0x3a44a68ce63293c2fe000434000e404b80004920b4aeae0800000099a000e220a20006ae000000238000444000000000390684000ab00006226c4000000000cd48389e81f47ac000be4000c049f60003ecc642b40000001ee00054e53abaa0000345aa7ec0006b4000000df8d14000b62b8c23abaeaba162c8c000c9ee5881e31c000d1a2da018868cac5c465693811a0002b0000000468db8dc002482c000d860b6db0d5ac22000636deed048f616a60e0004d2000bf669ca3074030e0008005a8dda8fc4a4e264d83787e86ca00086e0009fad42b727dc00026e6d61745c2bf8404cfc00e7165041b600057c000b32530d0a0002fa96839a000132192c325868dcbca0003f2b382548eac607e47cce52d1caf2000000b20dd00007466fa000ac43b8088562d0e084480ba00f8a3a000836c58000b080aa3340000005c03724b269800051c000000be2634000000000388bd6000d92b2400004084e79025ab361161fe2724ecc1e2e80da8a20006baaa4c846dac9c0000260000004d632840ac507b4000000bd4b860000005200008560007961e4e62de698004e0bc8f40e87f67446fe4c893ad98892432c76552986d12398b4cc802281584284be3a622456a67eca6268052958a1c182694ae43fe3becb65906d0d20340bd07fa540ad0258a78000626b1449a9e67883e4d4ead8a9616e81c23c1c228870c0000000003b0000b2c72800022205c8c0c7eb9c10c0be75ebbab96310a60336804000000000346dea00000084a48e574248c7a00000000041c23600045ccfa00000000087a19447a0004e28bc994acc7cee02d902088febbcaee000bac56481a26c8dab1e6d40646b633ac72000850718d36000cb82a86b09f80f085aa1882a9721721c417cd382d41a6bb085ee1c9d478c408a2e2f8000c56000000cd8cdca121400007ee37a62875a000000d5637000003cc02000858524000000dce12e04837c000a724fec2e8d82b60dc82692c42c0003e89529443800000007e00004984a808eaf04945be1e0d666e076e7101ca8e8d6c0009d0d1ed8821a0008a80000003ba00059800000000000089468a6a6d0239600014436edf052a000000732d00b849b6a4eb00100e562866cc67a000000a5a3861acc10000dde000000000d9a00010e96ed50cd00000008e4000aa084c000000062000bee0003e2124a243020a4000a46000e609f259cc0c0001e2184cc4888db464cab677ade2cd2c36b7051097057260676a384446bce2c270ebf0e1e154678b6a85c6f8d30a00784a8845abd2000000c6a1ba0001f27c4692b28860dfc3e0072000a0c212000000b82000000000ce4166a7000055a00058e0004de156000cf20001363b23fc2024f81ae0007a45b400029075000000000086cb0c8060000009921fac2819ad7a60a766c9612669065a7c2bc
  | 9 => 0x1a616256000ba282046e188472774e32588c1a0000d8a10000a9e5a6000000d340000005d80007f400013c72c000dbc0000000000002ca000db2b02000576000d26d944fc1048847580006bc7d6932a0483471e8903645b8676c98d4c000d180006680427823d2c4c76c6f46149ee000ce200040c12ad727a299000041600006e62c284724502d46e0c1b80008de00094c06a5d6a404e6000000000978864000000000000000ab80f266c1348a60005b65a400000000074e0000000009ba49c2f0cf40000008f2000a54196ae244a43a374a687084c0b640004b06ea3d600027662acae78ea8600089c000a3c000000c44000a3843659600097c3a851a0000000000000004eaca0000394b440000003560004867bcb6899e000844266a8a94a000b7c9d62ee06090e000548240000a0651e960d324b61aa64606600000046234a30ab8e02a57ebb244ed3c6800c600000000000063e86ac160003e6652974d24d162809cc12272272065c4ee2a0d600ca554966dd4812dfa7ba0000007c80008b40004846a000034c0005f626ae4a54608a0003064061c05e635c2c0882a6eb901c6b480003cacf076055ea741b410645e0001864661122a613e00000002e8183ea0007789aa8b80009467f89b40c848c998130118278da6000482000c9200083e68232e6c20000828d0086da28167c60d6c3e5cc090000000c380004a200000001255c0005e479844000000000019c08c8806b233850c97e0007fcce6d2ce0a88e00098ca50000e0e1c8da08d63663c0a26080a8e03eb54000000000000b186e8000000c8e0000d4506cc290046c2d600033c512a2c142000d3a522948000000000c4ecee9ca4ccb46050000786000afa36cca299c000e3ce5474892002031e00022c00007ca92a6c60488c73aad2000b6c0ea000000acea20000ae652c95a66ebdedac0146e60009f4a520000000005de8d41bcc7400000021e292000000d5420a70600000005a0008c209ccbc24e0000000003d8aae4704d07f0dc2000c6200017e342a623aa1384e867471c36a0a696c016000e64d105c61ec5ac00073e8be840000000000000000d2a000e4229ce20160dca3de704000c3034e392a020004500009a89f00002520001ce0000000000000000006080000005ba35ac0800020e0000004602de0003484e04566c632a2a2c2092a308000000b5ade0be6000a14234672000aa2000ba456c0008320002d275218cd64214a82bec298000000cb0000000000ab27720005007940001a29a64c45fe030b66c42d0c304c885dc3dc7feb3a61e664ac0b521029b27aab7e64e1d0bd8b1c094bfa6be26265ed8406c5366cea443c20708a45fc148000bfe00028ac4aafc8aa71a7f2110036b109b0936902000488df43ceade454cea000bfc0002ba2e24642440008f03bc00091c0ae
  | 10 => 0xb3c000c54b92000b302c4dd690409ee146f605e87cc8a24c846556170b8a33023e1a4322954b78e36c1c4144220fad48a760ac79e6e445259e89a0000004ae000decac6d6e0000000009ea4ce000b4ee1ab2e000930d28e240006b86c8058852c6ebe8108204df669aa5c92ee28a1673c9c209282229ab34352312114e0490a00064aa94000178000b580008b68acd52c004028b09a23200000001f60006e29da98438aa287d4580032b74abc0000002182509c65ae67c000934412000c2a0000000e2000e4e000c0a72a0006187d047e00078a9e262e51498a5ceccad3e4c68ba5668e0cba00029600024a000000a0e0001d8000c9a5920007540003440006d2426dbaa6a00000091a000a980004fa0003a26200000009a4318382e16b0607ee4c3c6adcbb4e30af60de2461dc768000000b7a48aacacf870a79284880e89629404c83aa7e11c00000000091e4ba150000964b80000c340ec0000007361dad08000c5c9de5eabc264843c32ccb42105f417607ae2a3f028295600030c2f26eea36af4be0912d40000aa81987d8006854200dfe28c000de490c6240000008621e857868e9a014e9060009d81f8bc400000000000046a0008108f80000007ca96a2b279ac86a5e0004d400000071211e15c3f422e2ae5e8d687be53437674254ac5ac52aa601c0f456e518e46496e504acc12560cc6658a80b9400039c558c180003601e6000642000300b2a00022a4745a0c822ac226c3ad9ea4295c31600000084215ace889e0ccb0a6f04
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x6320427e658c8109f596320427c658c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810d794d320435d534c810db949320436d524c810bdd8532042f4614c810bed8132042f8604c8109fd94320427e650c8109f594320427c650c8109f992510427d64944109f98e510427d63944109f98a510427d62944109f597410437651d04109fd96410427d6590410cf952410433d5490410be98241042f960904109fd95410427f65104109f594410433e5410410cf55041043765110410be98041042f960104109f597310427f658c4109f596310435e538c410d754e3104376518c410be98231042f9608c4109fd9531042bf644c410af1913104376514c4109fd94310427d650c410af99031042bd640c410d794c310435d530c410bb98831042ed620c410f54c431042fa600c410be580310427d65c84109fd96210427d6588410db94a210436d5288410dd94621042fa6088410be582210427f6548410afd9121042bc6448410dd945210427f65084109f594210436e5208410db54821042fa6008410be580210427e6494010cf992500423e64940109f592500433d64940108f592500427e63940109f58e500427e62940109f58a500427d61940109f597400433f54d0010cf153400427f65900109f596400433e5490010cf55240042f66190010bd586400427f6550010cfd51400433c5450010bbd8940042ec62500109fd94400427e65100109f594400427c6510010cf950400433d5410010bd98440042f561100109f597300427f658c0109f596300435e538c010d754e30042f6618c010bd586300437a508c0109fd95300437a504c0109fd94300427e650c0109f594300427c650c010af99030042bd640c010d794c300435d530c010bb98830042ed620c010bd98430042f5610c0109f597200427f65880109f596200436e5288010db54a20042f66188010bd586200427f6548010afd9120042bc64480109fd94200427e65080109f594200427c6508010af99020042bd6408010b798c20042dd6308010db948200436d5208010bd98420042f56108010dd597100437654c4010dd153100437753c4010dd54f100437752c4010dd54b10042be6484010af59210042f56184010dd94610042f96584010de59610042796584010ee99210043b96484010ded4e10043795384010be586100437a5184010fc946100427f6544010bdd95100437765440109dd9510043765444010dd15110043775344010dd54d10043775244010dd54910042f76044010dd94110043f24044010fc50110043f23044010fc4c110043f32044010fc08110042fb6544010ded95100427b6544010ded4d10043795344010bed8510043f36144010de94510043f25144010fc90510043f14144010fc8c510043f13144010fcc8510043f02144010
  | 1 => 0x43f35084110fc8c210443f130841109f98f540427d63d50109f98b540427d62d50109f987540437661d50109d987540427e60d5010de983540427d6595010cfd52540427e63950109f58e540427e62950109f58a540433f64550109fd8d540427c63550109fd89540427c62550109fd85540427d61550109fd81540427d6055010cf55054042de6315010b758c54042ee6215010bb588540427e6415010cf990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427e6015010de980540427e64d4c109f593530427e62d4c109f58b530427e61d4c10dd987530427e60d4c10de983530427d6594c10d7d4e530427e6494c109f592530427e6294c109f58a530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c109fd81530427d6054c10af99053042bd6414c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530427e6214c10db988530426e6214c109f588530436d6214c109b588530427e6114c10dd98453042766114c109f980530437a6014c109e980530427f65d0c109f997430427d65d0c109f197430433e54d0c10cf553430427f6590c109f996430427d6590c109f196430435e5390c10d754e43042ee6290c10bb58a430427f6550c109f995430427d6550c109f195430433e5450c10cf551430435e5350c10d754d43042f76150c10bd185430427f6510c109f994430427d6510c109f194430427e64d48109f593520427e63d48109f58f520427e61d4810dd987520427e60d4810de983520427d6594810dbd4a520427e64948109f592520427e63948109f58e52042bf6454810af191520427f6454810cfd91520423f64548109f191520433c64548108f191520427f63548109f18d520436f62548109fd85520427d61548109fd81520427d6054810af99052042bd6414810b798c52042dd6314810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520427e6114810dd984520427661148109f980520437a60148109fd97420427e65d08109f597420427c65d0810cf953420433d54d08109fd96420427e65908109f596420427c6590810cfd52420433c5490810db94a420436d52908109fd95420427e65508109f595420427c6550810cf951420433d5450810db949420436d52508109fd94420427e65108109f594420427c6510810cfd50420433c54108109fd97320427e65cc8109f597320427c65cc810af99332042bd64cc810d794f320435d53cc8109fd9
  | 2 => 0x4310510ed10c41442f56210510ed90841443b44210510bd980414427e65cc510d7d4f314435c53cc510be98331442f960cc5109f99631442f6658c510dd99631442f6648c510bd19231442f5638c510dd94e3144374538c510bd58a31443f3608c510bd98231443f0608c5109f19531442bf644c510af191314435f534c510d714d31442fb604c510be1813144374654c5109d19531443b7644c510bd99131442f4644c510ed19131442b4644c510f5d8d31443d7534c510dd94d3144374534c510f514d3144354534c510bdd8931443f3604c510bd18131443f0604c5109f99431442be640c510af59031442ee620c510bb58831442f6610c510be980314427e65c8510dbd4b214436c52c8510be98321442f960c85109f99621442f66588510dd99621442f66488510bd19221442f76388510bd58e21442f56288510dd94a21443745288510bd982214427c6548510afd9121442bc6448510dbd49214436c5248510bed8121442f86048510dd19521442746548510edd9121442f66448510bd19121443b46448510ad19121442f76348510bd58d21443e76248510f9d4921443765248510dd14921443e45248510f98c921443e53248510fcd8121442f46048510fc18121442f060485109f99421442f661085109f997404433f54d0110cf15340442f661d0110bd58740443b441d01109f99640442f66190110bd586404427f65501109f595404427c6550110cfd51404433c5450110bbd8940442ec6250110bdd8540442f46150110ed105404427e6510110ee500404427e65cc110d7d4f304435c53cc110bd98730442f561cc1109f99630442fa658c110de99630442f9638c110de94e3044378538c110fcd8630442fa618c110fc18630443f3418c110fc10630443f2318c110fc4c630443f2218c110fc486304427f654c1109f595304427c654c110d7d4d304435c534c110bdd8530442f4614c110be1953044378654c1109e19530443db634c110f6d4d304437a534c110de14d30443d8534c110f6cc930443d9324c110fcd8530442f8614c110fc18530443f3414c110fc10530443f2314c110fc4c530443f2214c110fc485304427e650c110af99030442bd640c110bb98830442ed620c110bd98430442f5610c110be980304427e65c8110dbd4b204436c52c8110bd98720442f561c81109f996204427f65481109f595204427c6548110afd9120442bc6448110dbd49204436c5248110bdd8520442f461481109f99420442be6408110af59020442de6308110b758c20442f66108110bd58420443e92008110bed8f10442f963c4110fcd0710443f041c4110fc8c710443f131c4110fc88710443f121c4110af99210442bd6484110bd99210443b66484110ad99210443b56484110bd19210442f76384110bd58e10442f76284110bd58a104
  | 3 => 0xd109f588534436d6214d109b588534427e6114d10dd584534427c6114d109f98053443796014d109f180534427f65d0d109f997434427d65d0d109f197434433e54d0d10cf553434435f53d0d10d714f434427f6590d109f996434427d6590d109f196434433f5490d10cf15243442ee6290d10bb58a43442f66190d10bd58643442fa6090d10be582434427f6550d109f995434427d6550d109f195434433e5450d10cf55143442f76150d10bd185434427f6510d109f994434427d6510d109f194434433f5410d10cf150434435f5310d10d714c43442f66110d10bd58443442fa6010d10be580434427e64d49109f593524427e63d49109f58f524436f52949109f992524427d64949109f98e524427d63949109f98a524427d6194910dd586524427d6094910de58252442bf6454910af19152442df6354910b718d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109fd81524437b60549109f994524436d52149109f990524427d64149109f98c524427d6314910db988524427e6114910dd584524427c61149109f980524427c60149109fd97424427e65d09109f597424427c65d0910dbd4b424436c52d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910bd98642442f561909109fd95424427e65509109f595424427c6550910bdd8542442f46150910bed8142442f860509109fd94424427e65109109f594424427c6510910cfd50424433c5410910dbd48424436c5210910bd98442442f56110910be98042442f960109109fd97324427e65cc9109f597324427c65cc910af99332442bd64cc910dbd4b324436c52cc910bd98732442f561cc910be98332442f960cc9109fd96324427e658c9109f596324427c658c910d7d4e324435c538c910db94a324436d528c910bd98632442f5618c9109fd95324427e654c9109f595324427c654c910db949324436d524c9109fd94324427e650c9109f594324427c650c910d7d4c324435c530c910dbd48324436c520c910bd98432442f5610c910be98032442f9600c9109f997414433f54d0510cf15341442fa60d0510be583414437665d05109d997414437754d0510edd53414437554d0510ed15341442f563d0510dd94f414437453d0510edd0f41443b543d0510bd58b41442f660d0510fc98341442f260d0510fc583414427e6590510cf952414433d5490510bd986414427c6550510cfd51414433c5450510bed8141442f860505109f994414433e5410510cf55041443b54110510bd99441443766510510bd99041443b66410510ddd5041443b65410510dd55041443b55410510bd58c41443765310510dd14c41443b6
  | 4 => 0x54c431842f9600c610cf953218433d54c8610db94b218436d52c8610be98321842f960c8610cf952218433d5488610afd9121842bc6448610cf951218433d5448610db949218436d5248610bed8121842f86048610cf950218433d5408610cf953408433d54d0210cf952408433d5490210bd98640842f56190210cf951408433d5450210bbd8940842ec6250210cf950408433d5410210bd98440842f56110210ee500408433e54cc210cf553308433e548c210cf552308435e538c210d754e30842f6618c210bd58630842f9658c210de59630843ba548c210ee552308437a538c210f694e30843d9538c210de14e30842fa618c210fc98630843f1618c210cf951308433d544c210bed95308437b654c210ee95130843b9544c210f6d8d308437a534c210de14d30843db324c210f64c930842f8614c210af99030842bd640c210cf950308433d540c210d794c308435d530c210bb98830842ed620c210bd98430842f5610c210cf953208433d54c8210cf952208433d5488210db94a208436d5288210bd98620842f56188210afd9120842bc6448210cf951208433d5448210af99020842bd6408210cf950208433d5408210b798c20842dd6308210db948208436d5208210bd98420842f56108210fa480208433e54c4210cf55310842f565c4210dd597108437654c4210ed953108433654c4210ed553108437454c4210ddd4f108437553c4210ddd4b108437552c4210be597108437965c4210ee95310843b954c4210bed8f10842f963c42109f98f544427d63d51109f98b544427d62d5110dd587544433f54951109f992544427e63951109f58e544427e62951109f58a544427d6195110dd586544427d6095110de58254442df6355110b718d54442ef6255110bb189544433f64551109fd8d544435f635511097d8d544427c6355110d718d544425c63551109fd89544436f62551109bd89544427c6255110db189544426c62551109fd85544437761551109fd81544437b60551109f994544433d5415110cf990544427e63151109f58c544427e62151109f588544427e61151109f184544427e60151109f180544427e64d4d109f593534427e62d4d109f58b534435f5394d109f992534427d6494d109f98e534427e6294d109f58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af19153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109f99453442be6414d10af590534435d5314d10bb98853442ed6214d109f990534433e6414d108f990534427d6414d10cf590534423d6414d10d798c534427e6214d10db988534426e6214
  | 5 => 0x538427d6294e10de982538433e5454e10cf551538427f6454e109f191538435f6354e109fd89538427c6254e10af99053842bd6414e10cf950538433d5414e10d754c53842ee6214e10bb588538427e6414e10cf990538423e6414e109f590538433d6414e108f590538435e6314e109f988538436e6214e109b988538427d6214e10db588538426d6214e10dd584538437a6014e109fd97438427e65d0e109f597438427c65d0e10cf953438433d54d0e109fd96438427e6590e109f596438427c6590e10cf952438433d5490e10bb98a43842ed6290e10be98243842f96090e109fd95438427e6550e109f595438427c6550e10cf951438433d5450e10bdd8543842f46150e109fd94438427e6510e109f594438427c6510e10cf950438433d5410e10be98043842f96010e10af99352842bd64d4a10cf953528433d54d4a109f993528433e64d4a108f993528427d64d4a10cf593528423d64d4a109f98f528427d63d4a10dd587528437a60d4a10cf952528433d5494a10dbd4a528427e6494a109f592528427e6394a109f58e528433e5454a10cf551528427f6454a109f191528427f6354a109f18d528436f6254a10af99052842bd6414a10cf950528433d5414a10b798c52842dd6314a10db548528427e6414a10cf990528423e6414a109f590528433d6414a108f590528427e6314a10d798c528425e6314a109f58c528435d6314a109758c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10cf953428433d54d0a109fd96428427e6590a109f596428427c6590a10cf952428433d5490a109fd95428427e6550a109f595428427c6550a10cf951428433d5450a10bed8142842f86050a109fd94428427e6510a109f594428427c6510a10cf950428433d5410a10be98042842f96010a109fd97328427e65cca109f597328427c65cca10af99332842bd64cca10cf953328433d54cca10d794f328435d53cca10be98332842f960cca109fd96328427e658ca109f596328427c658ca10cf952328433d548ca10db94a328436d528ca109fd95328427e654ca109f595328427c654ca10cf951328433d544ca10d794d328435d534ca10db949328436d524ca10bdd8532842f4614ca109fd94328427e650ca109f594328427c650ca10cf950328433d540ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610cf952418433d5490610cf951418433d5450610bed8141842f86050610cf950418433d5410610cf953318433d54cc610d794f318435d53cc610be98331842f960cc610cf952318433d548c610afd9131842bc644c610cf951318433d544c610d794d318435d534c610bed8131842f8604c610af99031842bd640c610cf950318433d540c610bb98831842ed620c610f
  | 6 => 0x3b543d0710bd58b41c42f660d0710cf95241c433d5490710be98241c42f96090710cf95041c433d5410710ed50441c42fa6010710be58041c43756510710ed99041c43775410710ed95041c43755410710ed55041c42f56310710dd94c41c43745310710ed90c41c43b44310710bd58841c43b64210710ed10841c42f66010710fc98041c43f16010710d794e31c435d538c710be98231c42f9608c710dd59631c42f6648c710bd19231c4376538c710f594e31c43d5538c710dd14e31c42f5628c710bd98231c43f2608c710fc58231c42bf644c710af19131c42f7654c710ddd9531c43b7644c710bd99131c42f4644c710ed19131c42b4644c710f5d8d31c4376534c710dd14d31c42f7624c710bd18131c42be640c710af59031c435e530c710d754c31c42ee620c710bb58831c42fa600c710be58031c436e5288710db54a21c42fa6088710be58221c43756588710bd99221c42f46488710bdd8e21c42f56388710dd94a21c43e65288710f954a21c43745288710bd98221c43f26088710fc58221c42bf6448710af19121c42f76548710ddd9521c43b76448710bd99121c42f46448710ed19121c42b46448710bdd8d21c42f56348710f9d8921c43765248710dd14921c43e63248710f94c921c42f46048710db94821c436d5208710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310ed10740c42f66190310bd58640c433e5450310cf55140c42ef6250310bb18940c42f76150310bd18540c43b44150310d794f30c435d53cc310bd98730c42f561cc310d794d30c435d534c310bdd8530c42f4614c310af99030c42bd640c310bb98830c42ed620c310bd98430c42f5610c310db94b20c436d52c8310bd98720c42f561c8310afd9120c42bc6448310db94920c436d5248310bdd8520c42f46148310af99020c42bd6408310b798c20c42dd6308310bd98420c42f561083109f98f548427d63d52109f98b548427d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a548433f6395210cf98e548433d6395210cf18e548433f6295210cf98a548433d6295210cf18a548433f6195210cf586548433e6095210cf182548433f64552109fd8d548427c63552109fd89548427c6255210cfd95548433f6355210cf98d548433d6355210cf18d548433f6255210cf989548433d6255210cf189548433f6155210cf585548433e6055210cf181548433d5415210cf990548427e63152109f58c548427e62152109f58854843756115210de98054842be64d4e10af593538433e54d4e10cf553538427e64d4e10cf993538423e64d4e109f593538433d64d4e108f593538427e62d4e109f58b538437561d4e10de983538433e5494e10cf552538435f5394e109f992538427d6494e109f98a
  | 7 => 0x548020ded95200827b6548020eed9120083b86448020ee95120083b95448020f694d20083d95348020bed8920083eb6248020de94920083ea5248020fa90920083e94248020facc920083e83248020fc94520083f15148020fac8520083e92148020bb98b54c42ed62d53109f98f54c427d63d53109f98b54c436e62d53109b98b54c427d62d5310db58b54c426d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c433f64553109fd8d54c427c63553109fd8954c427c6255310dd18554c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c427e64d4f109f59353c427e62d4f109f58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f10dd98653c427f6454f109f19153c435f6354f109fd8953c427c6254f10af99053c42bd6414f10d754c53c42ee6214f10bb58853c427e6414f10cf99053c423e6414f109f59053c433d6414f108f59053c435e6314f109f98853c436e6214f109b98853c427d6214f10db58853c426d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10cf95343c433d54d0f109fd9643c427e6590f109f59643c427c6590f10bb98a43c42ed6290f10bd98643c42f56190f109fd9543c427e6550f109f59543c427c6550f10cf95143c433d5450f10bdd8543c42f46150f109fd9443c427e6510f109f59443c427c6510f10bd98443c42f56110f10af99352c42bd64d4b109f99352c433e64d4b108f99352c427d64d4b10cf59352c423d64d4b109f98f52c427d63d4b10dd98752c437960d4b10dbd4a52c427e6494b109f59252c427e6394b109f58e52c43766194b109fd9152c427c6454b109fd8d52c427c6354b10dbd8952c436d5214b109f99052c427d6414b109f98c52c427d6314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c436e52d0b10db54b42c427f6590b109f99642c427d6590b109f19642c433e5490b10cf55242c42f66190b10bd58642c427f6550b109f99542c427d6550b109f19542c42f76150b10bd18542c427f6510b109f99442c427d6510b109f19442c433e5410b10cf55042c436e5210b10db54842c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c42be64ccb10af59332c42f661ccb10bd58732c427f658cb109f99632c427d658cb109f19632c436e528cb10db54a32c42f6618cb10bd58632c427f654cb109f99532c427d654cb109f19532c436e524cb10db54932c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c42f6610cb10bd58432c42f565d0710dd59741c437754d0710dd55341c42f563d0710dd94f41c437453d0710edd0f41c4
  | 8 => 0x20afd9131082bc644c420cf951310833d544c420d794d310835d534c420bbd8931082ec624c420dd9453108375514c420bed8131082f8604c4209fd94310827e650c4209f59431082be640c420af590310833e540c420cf550310835e530c420d754c31082ee620c420bb5883108376510c420dd54431082fa600c420be580310833e54c8420cf553210835e53c8420d754f210837651c8420dd54721082fa60c8420be583210827d6588420cf952210833d5488420d794e210835d5388420dd546210827f6548420afd9121082bc6448420cf951210833d5448420d794d210835d5348420dd945210833e5408420cf550210835e5308420d754c21083765108420dd54421082fa6008420be580210827e64940209f592500827e63940209f58e500836f4294020db10a500827d65d0020cf953400833d54d0020d794f400835d53d0020ebd0b400837651d0020dd547400827f65900209f596400833e5490020cf552400835e5390020d754e40082ee6290020bb58a40083ac4290020bd98640082f56190020dd946400837551900209fd95400833e5450020cf551400835e5350020d754d40082ef6250020bb18940083af4250020dd945400837551500209fd94400827e65100209f594400827c6510020cf950400833d5410020d794c400835d5310020bb98840082ed6210020eb10840083765110020dd544400827d65cc020cf953300833d54cc020d794f300835d53cc020dd947300837551cc0209fd96300827d658c020cf952300833d548c020d794e300835d538c020bb98a30082ed628c020dd9463008375518c0209fd95300833e544c020cf551300835e534c020d754d3008376514c020dd545300827f650c0209f994300827d650c0209f19430082be640c020af590300833e540c020cf550300835e530c020d754c30082ee620c020bb58830082f6610c020bd5843008376510c020dd544300833e54c8020cf553200835e53c8020d754f200837651c8020dd54720082ee64c8020bb19320083ae54c8020eb553200836f53c8020f394f200836d53c8020f354f200834d53c8020f994720083e551c8020cf952200833d5488020d794e200835d5388020bb58a200836e5288020dd94620083755188020ee95220083b95488020f694e20083d95388020be58a200837a5288020fa94a20083eb4288020fa10a20083f25188020fc546200827f6548020afd9120082bc6448020cf951200833d5448020d794d200835d5348020dd94520083755148020bbd95200836f65480209bd9520083af6448020bb99120082ec6448020eb19120082ac6448020eb95120083ad5448020dbd4d20083ce5348020db54d20083cd5348020d354d20083e65148020f954520082ef6048020db94120083ea4048020fa50120083eb3048020fa0c120082fb6
  | 9 => 0x58042082e960108209f59732082be64cc820af593320833e54cc820cf553320835e53cc820d754f320827f658c8209f596320833e548c820cf552320835e538c820d754e320836e528c820be98232082f9608c8209fd95320833e544c820cf551320835e534c820d754d320836e524c8209fd94320827d650c820cf950320833d540c820d794c320835d530c820be98032082f9600c820af99351082bd64d4420cf953510833d54d4420b798f51082dd63d4420d794f510835d53d4420cf952510833d5494420d794e510835d5394420ddd46510827e64944209f592510827e63944209f58e51083775494420dd95251083b65494420cd95251083755494420ed55251083355494420dd15251083775394420dd94e51083d65394420d594e51083755394420f554e51083555394420dd14e51083e74294420f910a51083776494420dd99251083756494420dd19251083776394420dd98e51083756394420dd18e51083774394420dd90e51083754394420dd10e51083746294420ddd0a51083764294420dd50a51083744294420ddcca51083763294420dd4ca51083743294420dd98251083746094420cf951510833d5454420d794d510835d53544209fd91510827c64544209fd8d510827c6354420ddd9551083775454420dd95151083b65454420cd95151083755454420ed55151083355454420dd15151083775354420dd94d51083d65354420d594d51083755354420f554d51083555354420dd14d51083e74254420f910951083776454420dd99151083756454420dd19151083776354420dd98d51083756354420dd18d51083774354420dd90d51083754354420dd10d51083766254420ddd0951083764254420dd50951083744254420ddcc951083763254420dd4c951083743254420dd98151083746054420dd08151082be6414420af590510833e5414420cf55051082de6314420b758c510835e5314420d754c51082f66114420dd544510827f65d04209f997410827d65d0420cf953410833d54d0420d794f410835d53d0420dd947410837551d04209fd96410827e65904209f596410833e5490420cf552410835e5390420d754e41082ee6290420bb58a41083ac4290420dd94641083755190420be98241082f960904209fd95410827d65504209f195410833e5450420cf551410835e5350420d754d41082ef6250420bb18941083765150420dd545410827f65104209f994410827d6510420cf950410833d5410420d794c410835d5310420eb10841083765110420dd544410827f65cc4209f997310827d65cc420cf953310833d54cc420d794f310835d53cc420dd947310837551cc4209fd96310827e658c4209f596310833e548c420cf552310835e538c420d754e3108376518c420dd546310827f654c4209f595310827c654c4
  | 10 => 0x40827561150209f980540837a6015020af99353082bd64d4c20cf953530833d54d4c20bd98753082f561d4c209f993530833e64d4c208f993530827d64d4c20cf593530823d64d4c209f98b530836e62d4c209f987530837661d4c209d987530827d61d4c20dd587530827561d4c209f983530837a60d4c209f596530833e5494c20cf552530835f5394c209f992530827d6494c209f986530827d6194c2097596530835f5494c20d7952530839e5494c20c7952530835d5494c20e7552530831d5494c20d7152530835f6494c20d7992530835d6494c20d7192530835e6294c20d718a530835f6194c20d7986530835d6194c20d7186530835e6094c20d7182530833e5454c20cf551530827f6454c209f191530835f6354c209fd89530827d6254c209fd85530827c6154c20d7d95530835f5454c20d7951530839e5454c20c7951530835d5454c20e7551530831d5454c20d7151530835f6454c20d7991530835d6454c20d7191530835e6254c20d7189530835f6154c20d7985530835d6154c20d7185530835e6054c20d7181530835c2054c20af99053082bd6414c20cf950530833d5414c20b798c530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209798c530827e6214c20db988530826e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c20d794f430835d53d0c209fd96430827e6590c209f596430827c6590c20cf952430833d5490c20d794e430835d5390c20bb98a43082ed6290c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c20bbd8943082ec6250c20bdd8543082f46150c20bed8143082f86050c209fd94430827e6510c209f594430827c6510c20cf950430833d5410c20d794c430835d5310c209f992520827d64948209f98e520827d63948209f597420833e54d0820cf553420835e53d0820d754f42082ed65d0820db597420836f54d0820eb953420836d54d0820eb553420832d54d0820dbd4f42083ce53d0820db54f42083cd53d0820d354f42082ed60d08209fd96420827d6590820cf952420833d5490820d794e420835d5390820bb98a42082fa6090820be582420827f6550820cf951420833d5450820d794d420835d53508209fd94420827d6510820cf950420833d5410820d794c420835d5310820eb50842082fa6010820be580420836d65108209b59442082ee6410820eb990420836f5410820eb950420836d5410820eb550420836f5310820f394c420836d5310820f354c420834d5310820ebd0c42083ad4310820fa98042082ed6010820fa
  | 11 => 0x3f5410520cf15041482ee6210520bb58841482fa6010520be580414827e65cc5209f597314827c65cc520cfd53314833c54cc520bb98b31482ed62cc520ddd47314837451cc5209f996314827d658c5209f196314833f548c520cf152314835f538c520d714e314827f654c5209f995314827c654c520afd9131482bc644c520cfd51314833c544c5209f994314827d650c5209f19431482be640c520af590314833f540c520cf150314835f530c520d714c31482ee620c520bb5883148377510c520dd14431482fa600c520be580314827e65c8520cfd53214833c54c8520cfd52214833c5488520ddd4621483745188520be98221482f96088520afd9121482bc6448520cfd51214833c5448520ddd4521483745148520bed8121482f860485209f994214833f5408520cf150214827e65d0120cfd53404833c54d0120bb98b40482ed62d01209f996404833f5490120cf15240482f66190120bd586404827f65501209f595404827c6550120cfd51404833c5450120bbd8940482ec62501209f994404833f5410120cf150404827e65cc120cfd53304833c54cc120d7d4f304835c53cc120bb98b30482ed62cc120f34cb304827e658c120cfd52304833c548c1209fd95304827d654c1209f195304833f544c120cf151304835f534c120d714d30482ef624c120bb18930483cd324c1209f99430482be640c120af590304833f540c120cf15030482ee620c120bb58830482f6610c120bd584304833f54c8120cf15320483bb54c8120ee15320483ea32c8120fa4cb204833f5488120cf15220483af5488120db952204836c5488120eb152204832c5488120bbd8e20482ed6388120fad4220482de63d5020b758f54082f661d5020bd587540827e63d5020d798f540825e63d50209f58f540835d63d50209758f540827e62d5020db98b540827e61d5020dd987540827661d50209f587540837561d50209d587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540823d6595020eb18a540833f6395020cf98e540833d6395020cf18e540833e6295020cf18a540833f6195020cf986540833d6195020cf186540833e6095020cf182540833f64550209fd8d540827c63550209fd89540827d6255020db189540827f61550209f185540833f6555020eb189540833f6355020cf98d540833d6355020cf18d540833e6255020cf189540832c6255020cfd85540833e6155020cf585540833c6155020cf981540833c6055020cf08154082be6415020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf990540823e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f988540836e62150209f984540837661150209d984540827d6115020dd5845
  | 12 => 0x15120cfd8c544833e6315120cf58c544833c6315120cfd88544833d6215120cfd84544833e6115120cf584544833c6115120cfd80544833d6015120cf480544833f54d4d20cf153534827e64d4d209f593534827e61d4d209f58753482be6494d20af592534833f5494d20cf152534835f5394d209f992534833e6494d208f992534827d6494d20cf592534823d6494d209f98e534827d6294d20db58a534827e6194d209f586534827d6094d20de58253482bf6454d20af191534833f5454d20cf15153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534835f6354d209fd89534836f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209f994534833f5414d20cf150534835d5314d209f990534827d6414d20d798c534827e6214d20db588534827c6214d209f984534827d6114d209fd97434827e65d0d209f597434827c65d0d20cfd53434833c54d0d209fd96434827e6590d209f596434827c6590d20cfd52434833c5490d20bb98a43482ed6290d209fd95434827e6550d209f595434827c6550d20cfd51434833c5450d20bdd8543482f46150d209fd94434827e6510d209f594434827c6510d20cfd50434833c5410d20bb98843482ed6210d20be98043482f96010d209f997424833f54d0920cf15342482fa60d0920be583424827e6590920cfd52424833c54909209f195424833f5450920cf15142482fb6050920be181424827e6510920cfd50424833c54109209f99732482be64cc920af593324833f54cc920cf153324835f53cc920d714f32482fa60cc920be583324827e658c920cfd52324833c548c920bb996324836e658c920ebd52324836e548c920db15232483ac548c920cb15232482ed638c920db94e324836c538c920bb982324827c654c920cfd51324833c544c920d7d4d324835c534c920bed8132482f8604c920db195324826c654c920ebd51324836e544c920db15132483ac544c920cb15132483cf634c920f3d4d324836e534c920db14d32483cc534c920fad8132482ec604c920fa18132482e8604c9209f994324833f540c920cf15032482ee620c920f34c8324833f54d4520cf153514827e64d45209f593514827e63d45209f58f514836e32d4520db4cb51482be6494520af592514833f5494520cf15251483775194520afd9151482bc6454520cfd51514833c5454520b7d8d51482dc6354520cfd50514833c5414520dd544514827e64145209f590514827e63145209f58c514827e65d05209f597414827c65d0520cfd53414833c54d05209f996414827d65905209f196414833f5490520cf152414827f65505209f995414827c6550520cfd51414833c54505209f994414827d65105209f19441483
  | 13 => 0xbe98043882f96010e20cf953428833d54d0a20be98342882f960d0a20db597428836f54d0a20eb953428836d54d0a20eb553428836f53d0a20db54f42883ea60d0a20bb58342883e960d0a20cfd52428833c5490a20cf951428833d5450a20bed8142882f86050a20cfd50428833c5410a20eb50842882ed6510a20db59442883ae6410a20dbd5042883af5410a20db55042883ac5410a20dbd4c428836d5310a20ebd0c42883ad4310a20bb58042882be64cca20af593328835e53cca20d754f32882fa60cca20be583328835e534ca20d754d32882fb604ca20be18132882be64d4620af593518837751946209f992518827d64946209f98e518827d63946209fd91518827c64546209fd8d518827c6354620dd544518827f65d06209f997418827d65d0620dd947418837551d06209fd96418827e65906209f596418833e5490620cf55241882ee6290620bb58a41883ac42906209fd95418827d65506209f19541882ef6250620bb189418827f65106209f994418827d6510620cf950418833d5410620eb10841883765110620dd54441882fa6010620be580418827f65cc6209f997318827d65cc6209fd96318827e658c6209f5963188376518c620dd546318827f654c6209f595318827c654c620afd9131882bc644c620bbd8931882ec624c620dd9453188375514c6209fd94318827e650c6209f59431882be640c620af59031882ee620c620bb58831882fa600c620be58031883765188620dd54621882fa6088620be58221882bf6448620af19121883765148620dd54521882fb6048620be181218833f54d0220cf15340883af42d0220cf952408833d5490220bb98a40882ed6290220eb10a40882f66190220bd586408833f5450220cf15140882ef6250220bb18940883af4250220cf950408833d5410220bb98840882ed6210220eb108408835f53cc220d714f308835e538c220d754e30882ee628c220bb58a308835f534c220d714d30882be640c220af590308835e530c220d754c30882ee620c220bb58830882f6610c220bd58430882ed65c8220db59720882ee64c8220bb193208836f53c8220db54f20882f965c8220de597208827e63d51209f58f544827e61d51209f587544833f63d5120cf98f544833d63d5120cf18f544833f62d5120cf58b544833f61d5120cf987544833d61d5120cf187544833f60d5120cf583544833f54951209f992544823e64951209f98e544827d63951209f58a544836d62951209f986544827d61951209f58254483796095120cfd91544827f63551209f18d544827f6255120dbd89544826f62551209fd85544827c61551209fd81544837b60551209f994544833d5415120cf990544827e63151209f58c544827e62151209f188544827e61151209f58454482be6515120cf994544823e65
  | 14 => 0x4e32c82ee608cb20fa98232c83e9608cb20d7d4d32c835c534cb20bbd9532c836f654cb20db95132c836c544cb20f3d8d32c83cf534cb20db94d32c836c534cb20f314d32c82ec604cb20d794c32c835d530cb20f34c832c82fa600cb20be58032c837751947209f99251c827d64947209f98e51c827d6394720afd9151c82bc64547209fd9151c833f64547208fd9151c827c6454720cf19151c823c64547209fd8d51c827c6354720db8c951c836d3254720dd54451c827f65d07209f99741c827d65d07209fd9641c827e65907209f59641c833f5490720cf15241c82fa6090720be58241c827f65507209f59541c827c65507209fd9441c827e65107209f59441c833f5410720cf15041c82ee6210720bb58841c827f65cc7209f99731c827d65cc720bb98b31c82ed62cc7209fd9631c827e658c7209f59631c827f654c7209f59531c827c654c720afd9131c82bc644c720bed8131c82f8604c7209fd9431c827e650c7209f59431c82be640c720af59031c82ee620c720bb58831c82fa600c720be58031c837651c8720dd54721c82fa60c8720be58321c82bf6448720af19121c83765108720dd54421c82fa6008720be58021c833e54d0320cf55340c82ee62d0320bb58b40c833f5490320cf15240c82f66190320bd58640c833e5450320cf55140c82ef6250320bb18940c833f5410320cf15040c835e53cc320d754f30c82ee62cc320bb58b30c83cd32cc320d794d30c835d534c320bbd8930c82ec624c320f34c930c82be640c320af59030c82ee620c320bb58830c82f6610c320bd58430c82f661d5220bd587548827e63d52209f58f548836d62d52209f987548837661d52209d987548827d61d5220dd587548827561d5220de983548833f54952209f98e548827d63952209f986548827d6195220cfd91548827f63552209f18d548836f62552209fd85548827c6155220cf550548833e64152209f98c548827d6315220db588548827e61152209f584548837a60152209f993538827d64d4e20db58b538827e61d4e209f587538837a60d4e20d7d4e538827e6494e209f592538827e6194e209f586538827f6454e209f191538835f6354e209fd85538827c6154e20af99053882bd6414e20d754c53882f66114e20bd584538827e6414e20cf990538823e6414e209f590538833d6414e208f590538835e6314e20db588538827e6114e20dd98453882766114e209f58453883756114e209d584538837a6014e209fd97438827e65d0e209f597438827c65d0e20cf953438833d54d0e209fd96438827e6590e209f596438827c6590e20bb98a43882ed6290e209fd95438827e6550e209f595438827c6550e20cf951438833d5450e20bbd8943882ec6250e20bdd8543882f46150e209fd94438827e6510e209f594438827c6510e2
  | 15 => 0xc37551d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd6390030db94a400c36d5290030bd986400c2f56190030dd946400c37551900309fd95400c33e5450030cf551400c2ef6250030bb189400c36e5250030db549400c3765150030dd545400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c36e5210030db548400c3765110030dd544400c33e54cc030cf553300c36e52cc030db54b300c37651cc030dd547300c39e54cc030e7553300c3ce52cc030d754b300c3cd52cc030d354b300c3d651cc030f5547300c33e548c030cf552300c2dd638c030d794e300c36e528c030db54a300c376518c030dd546300c3ba548c030ee552300c2f9638c030de94e300c3da538c030fa94a300c3e9528c030fc946300c379518c030fc546300c371518c0309fd95300c33e544c030cf551300c36e524c030db549300c376514c030dd545300c2df654c030d7d95300c25f654c030e7951300c39d544c030f3949300c35d524c030f3549300c34d524c030f5945300c3d5514c030b7d81300c35e504c030f6901300c3d9404c030bed95300c37b654c0309ed95300c3ba544c030ee551300c2fb634c030f6d8d300c37a534c030f694d300c3da434c030f650d300c3ea524c030fa549300c3f2514c030de545300c3f1514c030dc545300c27e63d53209f58f54c836e62d53209f98754c827d61d5320de58354c833f54953209f98e54c827d63953209f98654c827d6195320cfd9154c827f63553209f18d54c827f61553209f18554c833d5415320cf99054c827e63153209f58c54c836e62153209f98454c827d6115320de58054c827e64d4f209f59353c836e62d4f209f98753c827d61d4f20de58353c82be6494f20af59253c835f5394f209f99253c833e6494f208f99253c827d6494f20cf59253c823d6494f20db98a53c827e6194f209f58653c827f6454f209f19153c835f6354f209fd8553c827c6154f20d754c53c827e6414f209f59053c835e6314f20db98853c827e6114f209f58453c83796014f209fd9743c827e65d0f209f59743c827c65d0f20cfd5343c833c54d0f209fd9643c827e6590f209f59643c827c6590f20bb98a43c82ed6290f209fd9543c827e6550f209f59543c827c6550f20cfd5143c833c5450f20bdd8543c82f46150f20bed8143c82f86050f209fd9443c827e6510f209f59443c827c6510f20bb98843c82ed6210f20cfd5342c833c54d0b20cf95242c833d5490b20be98242c82f96090b20cfd5142c833c5450b20cf95042c833d5410b20be98042c82f96010b20af99332c82bd64ccb20d7d4f32c835c53ccb20d794e32c835d538cb20be98232c82f9608cb20db59632c836e548cb20db15232c836e538cb20f394e32c83cd538cb20db1
  | 16 => 0x55494430cd552510c3745494430ddd4a510c3765294430f994a510c3665294430dd54a510c3e55294430d954a510c3745294430ddd92510c3766494430dd592510c3746494430dd18e510c3774394430dd90e510c3754394430dd10e510c3776294430dd98a510c3756294430dd18a510c3774294430dd90a510c3754294430dd10a510c3773294430dd8ca510c3753294430dd0ca510c3766094430dd182510c33e5454430cf551510c36e5254430db549510c27f64544309f191510c27f62544309f189510c3776554430ddd51510c3765454430ed951510c3365454430dd551510c3b55454430cd551510c3745454430ddd49510c3765254430f9949510c3665254430dd549510c3e55254430d9549510c3745254430ddd91510c3766454430dd591510c3746454430dd98d510c3774354430dd90d510c3754354430dd10d510c3776254430dd989510c3756254430dd189510c3774254430dd909510c3754254430dd109510c3773254430dd8c9510c3753254430dd0c9510c3766054430dd181510c3743054430af990510c2bd6414430cf950510c33d5414430bb988510c2ed6214430db948510c36d5214430bd984510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c36e52d0430db54b410c37651d0430dd547410c27f65904309f996410c27d6590430cf952410c33d5490430db94a410c36d5290430dd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c36e5250430db549410c3765150430dd545410c27f65104309f994410c27d6510430cf950410c33d5410430db948410c36d5210430dd944410c3755110430cf953310c33d54cc430db94b310c36d52cc430dd947310c37551cc430be983310c2f960cc4309f596310c33e548c430cf552310c36e528c430db54a310c375518c4309fd95310c2bf644c430af191310c33e544c430cf551310c36e524c430db549310c376514c430af990310c2bd640c430cf950310c33d540c430bb988310c2ed620c430db948310c36d520c430dd944310c375510c430f54c4310c2fa600c430be580310c27f65c84309f997210c27d65c8430cf953210c33d54c8430db94b210c36d52c8430dd947210c37551c84309fd96210c27e65884309f596210c33e5488430cf552210c36e5288430db54a210c3765188430dd546210c27f65484309f595210c27c6548430afd91210c2bc6448430cf951210c33d5448430b7d8d210c2dc6348430db949210c36d5248430dd945210c3755148430bed81210c2f860484309fd94210c27e65084309f594210c33e5408430cf550210c36e5208430db548210c3765108430dd544210c27e64940309f592500c27d65d0030cf953400c33d54d0030db94b400c36d52d0030dd94740
  | 17 => 0x50309f185540c33f6555030cf98d540c33c6355030cfd89540c33e6255030cf589540c33c6255030cfd85540c33e6155030cf585540c33c6155030cf981540c33c6055030cf0c1540c2be6415030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6415030cf990540c23e64150309f98c540c35e63150309f988540c36e62150309b988540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a60150309f992530c27d6494c309f597430c33e54d0c30cf553430c27f6590c309f596430c33e5490c30cf552430c2ee6290c30bb58a430c2fa6090c30be582430c27f6550c30cf951430c33d5450c30bdd85430c2f46150c309fd94430c27d6510c30cf950430c33d5410c30be980430c2f96010c30af993520c2bd64d4830cf953520c33d54d4830bd987520c2f561d4830cf952520c33d5494830dbd4a520c27e64948309f592520c27e61948309f586520c36f5494830db952520c3ae5494830cb952520c36d5494830eb552520c32d5494830db152520c36f6494830db992520c36d6494830db192520c36c6394830dbd0e520c36e4394830db50e520c36c4394830dbd86520c36e6194830db586520c36c6194830db982520c36c6094830cf951520c33d54548309fd91520c27c64548309fd85520c27c6154830dbd95520c36f5454830db951520c3ae5454830cb951520c36d5454830eb551520c32d5454830db151520c36f6454830db991520c36d6454830db191520c36e6354830dbd0d520c36e4354830db50d520c36c4354830dbd85520c36e6154830db585520c36c6154830db981520c36c6054830db0c1520c2be6414830af590520c33e5414830cf550520c2ee6214830db548520c2f66114830bd584520c27f65d08309f997420c27d65d0830cf953420c33d54d0830db94b420c36d52d08309fd96420c27e65908309f596420c33e5490830cf552420c36e5290830db54a420c27f65508309f595420c27c6550830cf951420c33d5450830db949420c36d5250830bed81420c2f860508309fd94420c27e65108309f594420c33e5410830cf550420c36e5210830db548420c2be64cc830af593320c33e54cc830cf553320c35e53cc830db94b320c36d52cc830be983320c2f960cc8309f596320c33e548c830cf552320c36d528c8309fd95320c33e544c830cf551320c35e534c830db949320c33e540c830cf550320c36e520c830db548320c2fa600c830be580320c2be64d4430af593510c33e54d4430cf553510c2ee62d4430bb58b510c36e52d4430db54b510c33e5494430cf552510c36e5294430db54a510c37751944309f992510c27d64944309f98a510c27d6294430ddd52510c3765494430ed952510c3365494430dd552510c3b
  | 18 => 0x9f984524c27d61149309f997424c27d65d09309f197424c36f52d0930db14b424c27e65909309f596424c27c6590930cfd52424c33c5490930b798e424c2dd63909309fd95424c27e65509309f195424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930dbd48424c36c5210930be980424c2f960109309f997324c2be64cc930af593324c2de65cc930d7997324c39e64cc930e7593324c35c52cc930b7983324c2dd638c930dbd4a324c36c528c930be982324c2f9608c930dbd49324c36c524c930bed81324c2f8604c930f3d89324c3cf524c930d7149324c3cc524c930f3d09324c3cc424c930f6d81324c2dc604c930f6181324c27e650c930b798c324c3cd320c9309f993514c27d64d45309f98b514c27d62d4530ddd46514c2bf6454530af191514c2ef6254530bb189514c37551145309f990514c27d64145309f988514c27d6214530de580514c27e65d05309f597414c27c65d0530ddd47414c37451d05309f996414c27d65905309f196414c33f5490530cf152414c2fa6090530be582414c27f65505309f995414c27c65505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c3775110530dd144414c2fa6010530be580414c27e65cc530ddd46314c374518c530be982314c2f9608c530afd91314c2bc644c530ddd45314c374514c530bed81314c2f8604c5309f994314c2be640c530af590314c2ee620c530bb588314c2fa600c5309f997214c27d65c85309f197214c2de63c8530b758f214c3cd32c8530ddd47214c37451c85309f996214c27d65885309f196214c36f5288530db14a214c2fa6088530be582214c27f65485309f995214c27c6548530afd91214c2bc6448530f34c9214c27e65085309f594214c27c6508530b798c214c2dd6308530dbd48214c36c5208530ddd44214c3745108530be980214c2f960085309f997404c33f54d0130cf153404c2de63d0130b758f404c27e6590130bd986404c2f561901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c2ef6250130bb189404c27e6510130f6ccb304c3d932cc130be587304c2dd628c130f6d42304c2ee62d5030bb58b540c2f661d5030bd587540c27e63d5030d798f540c27e62d5030db98b540c26e62d50309f58b540c36d62d50309b58b540c27e61d5030dd987540c27661d50309f587540c37561d50309d587540c27e60d5030de983540c27d6595030cfd52540c27e62950309f58a540c27e61950309f586540c23d6595030cf98e540c33c6395030cfd8a540c33e6295030cf58a540c33c6295030cfd86540c33e6195030cf586540c33c6195030cf982540c33c6095030cfd91540c27f63550309f58d540c27f62550309f189540c27f615
  | 19 => 0x1528c27c6454a30cf191528c23c6454a309fd85528c27c6154a30af990528c2bd6414a30db548528c2f66114a30bd584528c27f65d0a309f997428c27d65d0a30cf953428c33d54d0a309fd96428c27e6590a309f596428c33f5490a30cf152428c27f6550a309f595428c27c6550a30cf951428c33d5450a309fd94428c27e6510a309f594428c33f5410a30cf150428c2fa6010a30be580428c2be64cca30af593328c36e528ca30db54a328c2fa608ca30be582328c36e524ca30db549328c2fb604ca30be181328c2be64d4630af593518c37751946309f992518c27d64946309f98a518c27d6294630de982518c27f64546309f191518c27f62546309f189518c37551146309fd97418c27e65d06309f597418c37651d0630dd547418c27f65906309f996418c27d6590630cf952418c33d5490630be982418c2f960906309fd95418c27d65506309f195418c2df6350630b718d418c27f65106309f994418c27d6510630cf950418c33d5410630dd944418c3755110630be980418c2f96010630dd946318c375518c630be982318c2f9608c630afd91318c2bc644c630dd945318c375514c630bed81318c2f8604c630af990318c2bd640c630bb988318c2ed620c630f54c4318c2f9600c6309fd97218c27e65c86309f597218c27f65886309f996218c27d6588630dd946218c3755188630be982218c2f960886309fd95218c27d65486309f195218c2bf6448630af191218c2df6348630b718d218c3765148630dd545218c27f65086309f994218c27d6508630be980218c2f96008630cfd53408c33c54d0230cf952408c33d5490230b798e408c2dd6390230bd986408c2f56190230cfd51408c33c5450230bbd89408c2ec6250230cf950408c33d5410230b798c408c2dd6310230b7597308c35d65cc230d754b308c2f965cc230de597308c2f961cc2309f98b544c27d62d51309f987544c27d61d5130cfd52544c27e64951309f58e544c35d63951309f98a544c27d62951309f986544c27d61951309f582544c3796095130bbd89544c2ec6255130bdd85544c2f46155130cfd91544c27f6355130d7d8d544c27f6255130dbd89544c26f62551309f189544c36c62551309b189544c27f6155130ddd85544c27761551309f185544c37461551309d185544c27f6055130ded81544c27e6515130cf550544c33e64151309f98c544c27c63151309f988544c27d62151309f984544c27d61151309f997434c33f54d0d30cf153434c2fa60d0d30be583434c27e6590d30bb98a434c2ed6290d309f195434c33f5450d30cf151434c2f76150d30bd185434c2fb6050d30be181434c27e6510d309f993524c27d64d49309f987524c27d61d4930dbd4a524c2bf6454930af191524c2f76154930bd185524c36d52149309f990524c27d6414930
  | 20 => 0xc36f5294b309f99252cc27d6494b309f98652cc27d6194b309fd9152cc27c6454b309fd8552cc27c6154b30db54852cc27f65d0b309f99742cc27d65d0b30db94b42cc36d52d0b309fd9642cc27e6590b309f59642cc33e5490b30cf55242cc2de6390b30b758e42cc27f6550b309f59542cc27c6550b30bed8142cc2f86050b309fd9442cc27e6510b309f59442cc33e5410b30cf55042cc2de6310b30b758c42cc36e5210b30db54842cc2be64ccb30af59332cc36e52ccb30db54b32cc2fa60ccb30be58332cc39e64ccb30e759332cc35e52ccb30f394b32cc3cd52ccb30b798332cc3da60ccb30f658332cc2df654cb30d7d9532cc3cf624cb30f3d4932cc35e524cb30f314932cc3cf424cb30f310932cc2dc604cb30db94832cc36d520cb30f34c832cc2fa600cb30be58032cc37751947309f99251cc27d64947309f98a51cc27d6294730afd9151cc2bc64547309fd9151cc33f64547308fd9151cc27c6454730cf19151cc23c64547309fd8951cc27c6254730af99051cc2bd6414730bb98851cc2ed6214730dd54451cc27f65d07309f99741cc27d65d0730cf95341cc33d54d07309fd9641cc27e65907309f59641cc33f5490730cf15241cc27f65507309f59541cc27c6550730cf95141cc33d54507309fd9441cc27e65107309f59441cc33f5410730cf15041cc2de6310730b758c41cc37651cc730dd54731cc2fa60cc730be58331cc2bf644c730af19131cc2be640c730af59031cc2ee620c730bb58831cc376510c730dd54431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730b798f21cc2dd63c8730db94b21cc36d52c8730f34cb21cc27f65887309f99621cc27d65887309fd9521cc27d65487309f19521cc2bf6448730af19121cc36e5248730db54921cc3cd3248730bed8121cc2f860487309fd9421cc27e65087309f59421cc2de6308730b758c21cc33e54d0330cf55340cc2de63d0330b758f40cc2f66190330bd58640cc33e5450330cf55140cc2df6350330b718d40cc2ef6250330bb18940cc2f661d5230bd587548c35d63d52309f98b548c27d62d52309f987548c37661d52309d987548c27d61d5230dd587548c27561d5230de983548c33f54952309f98a548c27d62952309f986548c27d6195230bbd89548c2ec6255230cfd91548c27f6255230dbd89548c26f62552309f189548c36c62552309b189548c27f61552309f185548c33d5415230cf990548c35d63152309f988548c27d62152309f984548c27d6115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c2ee6290e30bb58a438c33e5450e30cf551438c2f76150e30bd185438c2fb6050e30be181438c36f5294a309f992528c27d6494a309f986528c27d6194a30afd91528c2bc6454a309fd91528c33f6454a308fd9
  | 21 => 0x6210840eb948421033d5210840eb54842103ba6010840af58042103b960108409fd97321027e65cc8409f59732102be64cc840af593321035e53cc840d754f321027f658c8409f996321027d658c840db94a321036d528c840eb10a321027f654c8409f595321027c654c840afd9132102bc644c840d794d321035d534c840db949321036d524c840eb10932102fb604c840be181321027f650c8409f994321027d650c840ddd46511027e63944409f58e511027e62944409f58a511033e4294440cf10a511027f63544409f18d511027f62544409f18951102de6314440b758c51102ee6214440bb58851103755114440dd947411037551d0440be98341102f960d04409f596411033e54904409fd95411033e5410440dd94441103755110440be98041102f960104409fd97311027e65cc4409f597311035e53cc440d754f311027f658c4409f996311027d658c440dd9463110375518c4409fd95311027d654c4409f19531102bf644c440af191311035e534c440d754d3110376514c440dd545311027f650c4409f994311027d650c440af99031102bd640c440bb98831102ed620c440be98031102f9600c4409fd97211027e65c84409f597211036e52c8440db54b211027f65884409f996211027d6588440af99221102bd6488440dd94621103755188440be98221102f960884409fd95211027d65484409f19521102bf6448440af191211036e5248440db54921103765148440dd545211027f65084409f994211027d6508440cf90a501033c4294040dd98650103756194040cf54f40102be62d0040cf54b401033e51d0040af592401033e5490040bd98640102f56190040be592401037a5490040ee95240103ba4290040ee10a40103f26190040fc586401027f6550040bbd8940102ec6250040afd95401033f65500408fd95401033d5350040ebd8940102bc6250040eb18940102ac6250040cf549401033e5150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103eb6250040fa18940103bb4150040ee50540102ee62d5330bb58b54cc35e63d53309f98b54cc36e62d53309b98b54cc27d62d5330db58b54cc26d62d53309f98754cc27d61d5330de58354cc33f54953309f98a54cc27d62953309f98654cc27d6195330bdd8554cc2f46155330cfd9154cc27f62553309f18954cc27f6155330ddd8554cc27761553309f18554cc37461553309d18554cc33d5415330cf99054cc35e63153309f98854cc27d62153309f98454cc27d6115330de58054cc33f54d0f30cf15343cc33e5490f30cf55243cc2ee6290f30bb58a43cc2fa6090f30be58243cc33f5450f30cf15143cc2f76150f30bd18543cc33e5410f30cf55043cc2fa6010f30be58043cc2be64d4b30af59352c
  | 22 => 0x5409f58c515027e62145409f588515027e65d0540dbd4b415036c52d0540dbd4a415036c5290540ddd4641503745190540be98241502f96090540af58e415033c5390540af58a41503af5290540cf14a41503ac5290540cb14a41502be6190540cfd4641503b75190540ed14641502be6090540ee98241502ba6090540ee582415036f5250540db14941503775150540dd14541502fb6050540be181415027e6510540dbd48415036c5210540ed50441502be6510540cf99441502bd6310540cf14c41502bd6210540ebd48415033c5210540eb148415032c5210540af98441503b66110540cfd4441503b65110540ed54441502be60105409f997315027d65cc5409f19731502be64cc540af593315036f52cc540db14b315037751cc540dd14731503b441cc5409f996315027d658c5409f19631502bf648c540af192315035f538c540d714e315036f528c540db14a315027f654c5409f995315027c654c540afd9131502bc644c540dbd49315036c524c5409f994315027d650c5409f19431502be640c540af590315035f530c540d714c31502ee620c540bb588315036f520c540db1483150377510c540dd14431503b4410c540be98031502f9600c5409f997215027d65c85409f19721502be64c8540af593215036f52c8540db14b215027e65885409f596215027c6588540afd9221502bc6488540dbd4a215036c52885409fd95215027e65485409f19521502bf6448540af191215036f5248540db149215027e65085409f594215027c6508540af99021502bd6408540dbd48215036c5208540be98021502f96008540dbd4b405036c52d0140eed0f40503b943d0140fad4b40503e852d0140eed0b40503b942d0140ee90740503b841d0140dbd4a405036c5290140bd98640502f56190140af58e40502bd6290140ebd4a405033c5290140eb14a405032c5290140af98640503b66190140ad98640503b56190140eed42405035f5394c409f98a531027d6294c409f986531027d6194c409fd89531027c6254c409fd85531027c6154c40d754c53102ee6214c40bb58853102f66114c40bd584531033e54d0c40d794f431035d53d0c40be98343102f960d0c409f59643102ee6290c40bb58a431027f6550c40cf95143102f76150c40bd185431035e5310c40d754c43102fa6010c40be580431036f52948409f98e521027d63948409f986521027d61948409fd8d521027c63548409fd85521027c6154840b798c52102dd6314840db54852102f66114840bd584521033e54d0840db94b421036d52d0840be98342102f960d08409f59642102bd6590840cf596421023d6590840cf54e42102be6290840cf54a42102bd60908409fd95421033e5450840db948421036d5210840eb50842102fa6010840be580421033d5310840af98842103ae
  | 23 => 0xe580219037651d0240dd54740902bd65d0240cf597409033d53d0240af98b409033d52d0240cf94740903b651d0240cd94740903b551d0240be597409037965d0240fc94740903f151d02409f98b535027d62d4d409f987535027d61d4d40d7d4e53502ee6294d40bb58a53502ef6254d40bb18953502f76154d40bd185535035d5314d409f988535027d6214d409f984535027d6114d409f99743502be65d0d40cf997435033c53d0d40af58b43502be61d0d40af98343502bd6490d40d7d4e435035c5390d40bb98a43502ed6290d40be98243502f96090d40d7d4d435035c5350d40bdd8543502f46150d40bed8143502f86050d40e7d8d435039f5350d40cf14d435039c5350d40afd8943503b76150d40af18543503b46150d40ad18543503bb6050d40af18143503b86050d409f99443502be6410d409f98f525027d63d49409f987525027d61d4940ebd93525036f53d4940db94f525036d53d4940db14f52503af43d4940eb50f525036f64d4940dbd8f525036e63d4940db58f525036c63d4940dbd0f525036e43d4940db50f525036c43d4940dbd87525036e61d4940db587525036c61d4940dbd83525036d60d4940dbd4a525036d52149409f98c525027d6314940cfd0c525033d43149409f984525027d6114940bb994525036e6514940eb590525036f5314940db94c525036d5314940db14c52503af4314940eb50c525036f6414940dbd8c525036e6314940db58c525036c6314940dbd0c525032f4314940db90c525036d4314940cb50c525036c4314940dbd84525036e6114940db584525036c6114940dbd80525036d6014940db500525027e65d0940db14b42502be65d0940cf997425023e65d0940af58f42503af52d0940cf14b42503ac52d0940cb14b42502be61d0940af98342502bd6490940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bed8142502f86050940afd8d42503af6250940ebd49425033c5250940eb149425032c5250940af18542503bb6050940af18142503b860509409f99442502be6410940dbd48425027e65cc9409f597325027c65cc940af99332502bd64cc940dbd4b325036c52cc9409f996325027d658c9409f19632502be648c940af592325036f528c940db14a32503af428c9409fd95325027e654c9409f19532502be644c940af591325036f524c940db14932503af424c9409f994325027d650c9409f19432502be640c940af590325036f520c940db14832502fa600c940be580325036f52d4540db14b515027e63d45409f58f515033f43d4540cf50f515027e62d45409f58b51502ee6294540bb58a515036f5294540db14a51503775194540b7d8d51502dc6354540bbd8951502ec6254540dbd49515036c5254540dbd48515036c5214540dd544515027e6314
  | 24 => 0x43902f46150e40bed8143902f86050e40bd98752902f561d4a40dbd4a529027e6394a409f58e529027e6194a409f586529027f6354a409f18d529027f6154a409f18552902de6314a40b758c529036d5214a40bd98452902f56114a40db94a429036d5290a40be98242902f96090a40cf54e42903ae5290a40cf54a42903ad5290a40ee98242902bd6090a40ee582429036e5250a40db54942902fb6050a40be18142903ad4210a40af594429033d6510a40cf54c42903ae6210a40ebd48429033d5210a40eb14842902bd6010a409fd97329027e65cca409f59732902be64cca40af593329035e53cca40d754f329027f658ca409f996329027d658ca40db94a329036d528ca40eb10a329027f654ca409f595329027c654ca40afd9132902bc644ca40d794d329035d534ca40db949329036d524ca40eb109329027f650ca409f994329027d650ca40be98032902f9600ca40ddd46519027e63946409f58e519027e62946409f58a519033e4294640cf10a51903775394640dd94e51903755394640dd14e51903775294640dd94a51903755294640dd14a51903b64294640ed10a51903776494640ddd8e51903766394640dd58e51903746394640ddd0e51903764394640dd50e51903744394640ddd8a51903766294640dd58a51903746294640ddd0a51903764294640cd90a51903754294640dd10a51903344294640ddcca51903763294640dd4ca51903743294640dd982519037460946409fd8d519027c63546409fd89519027c6254640ddd9551903775354640dd94d51903755354640dd14d51903775254640dd94951903755254640dd14951903b64254640ed10951903756454640ddd8d51903766354640dd58d51903746354640ddd0d51903764354640dd50d51903744354640ddd8951903766254640dd58951903746254640ddd0951903764254640dd50951903744254640ddcc951903763254640dd4c951903743254640dd98151903746054640dd544519037651d0640dd94641903755190640be98241902f96090640dd94541903755150640bed8141902f86050640dd544419027f65cc6409f997319027d65cc640dd947319037551cc6409fd96319027e658c6409f5963190376518c640dd546319027f654c6409f595319027c654c640afd9131902bc644c640dd9453190375514c6409fd94319027e650c6409f59431902be640c640af59031902ee620c640bb5883190376510c640dd54431902fa600c640be580319027f65c86409f997219027d65c8640dd947219037551c86409fd96219027e65886409f59621902be6488640af59221903765188640dd546219027f65486409f595219027c6548640afd9121902bc6448640dd945219037551486409fd94219027e65086409f59421903765108640dd54421902fa6008640b
  | 25 => 0x2ed6294f409f98a53d036e6294f409b98a53d027d6294f40db58a53d026d6294f409f98653d027d6194f409fd8953d027c6254f409fd8553d027c6154f40d754c53d035e53d0f40d754f43d02fa60d0f40be58343d033e53d0f40e794f43d039d53d0f40af58b43d02be61d0f40af98343d03ba60d0f40ee58343d02ee6290f40bb58a43d02f76150f40bd18543d02bf6550f40cfd9543d039f6350f40cf94d43d02bf6250f40edd8543d02bc6150f40ed18543d02b46150f40af18143d035e5310f40d754c43d02fa6010f40be58043d036f5294b409f98e52d027d6394b40cfd0e52d033d4394b409f98652d027d6194b409fd8d52d027c6354b409fd8552d027c6154b40db54852d036e52d0b40db54b42d02fa60d0b40be58342d02bd63d0b40cf94b42d03ae52d0b40eb54b42d02be61d0b40af98342d03ba60d0b40ee58342d02bf6550b40cfd9542d02bf6350b40ebd8942d033e5250b40af18542d02bc6050b40db94842d036d5210b40be98042d02f96010b409fd9732d027e65ccb409f59732d02be64ccb40af59332d027f658cb409f99632d027d658cb40af99232d02bd648cb40ebd0a32d027f654cb409f59532d027c654cb40af99132d02bd644cb40ebd0932d02fb604cb40be18132d027f650cb409f99432d027d650cb40af99032d02bd640cb40ddd4651d027e63947409f58e51d027e62947409f58a51d027f63547409f18d51d033f4354740cf50d51d027f62547409f18951d03755114740dd94741d037551d0740be98341d02f960d0740af59641d033d6590740af58e41d033e5390740af58a41d033e5290740cf54641d02be6090740dd94441d03755110740ed50441d02fa6010740be58041d02bd6310740cf94c41d02bd6210740cf94841d03b66110740ed94441d033d5110740ed54441d02be6010740ee98041d03b960107409fd9731d027e65cc7409f59731d02be64cc740af59331d03b441cc7409fd9631d027e658c7409f59631d02bf648c740af19231d027f654c7409f59531d027c654c740afd9131d02bc644c7409fd9431d027e650c7409f59431d02be640c740af59031d02ee620c740bb58831d03b4410c740be98031d02f9600c7409fd9721d027e65c87409f59721d02be64c8740af59321d027f65887409f99621d027d6588740afd9221d02bc6488740be98221d02f960887409fd9521d027d65487409f19521d02bf6448740af19121d027f65087409f99421d027d6508740af99021d02bd6408740bd98753902f561d4e40d7d4e539027e6294e409f58a539027e6194e409f586539027f6254e409f189539027f6154e409f185539035d5314e40bb98853902ed6214e40bd98453902f56114e40d794e439035d5390e40bb98a43902ed6290e40be98243902f96090e40d794d439035d5350e40bdd85
  | 26 => 0x315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e580540867e64d4c219f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530867f6454c219f191530875f6354c219fd81530867c6054c21af99053086bd6414c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6314c21d798c530867e6214c21db988530866e6214c219f98453087766114c219f980530877a6014c219e980530867d6014c21de58053086796014c219fd97430867e65d0c219f597430867c65d0c21cf953430873d54d0c219fd96430867e6590c219f596430867c6590c21d794e430875d5390c21bb98a43086ed6290c219fd95430867e6550c219f595430867c6550c21cf951430873d5450c21d794d430875d5350c21bdd8543086f46150c219fd94430867e6510c219f594430867c6510c219f992520867d64948219f98e520867d63948219f597420867f65908219f596420873e5490821cf55242086f66190821bd586420867f65508219fd94420867d6510821cf950420873d5410821bd98442086f561108219f59732086be64cc821af593320867f658c8219f596320875e538c821d754e320876e528c821bd98632086f5618c8219fd95320876e524c8219fd94320867d650c821d794c320875d530c821f34c832086f6610c821bd584320867e64944219f592510867e63944219f58e510867d65d04219fd96410867d6590421cf952410873d5490421bb98a41086ed62904219fd95410867f65104219f994410867d65104219f194410873e5410421cf55041086ee6210421bb588410867d65cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c4219fd9531086bf644c421af191310867f650c4219f994310867d650c4219f19431086be640c421af590310875e530c421d754c31086ee620c421bb58831086fa600c421be580310876f53c8421db54f21086ed6288421db94a21086f56288421dd94a21087e652884219fd9521086bf6448421af19121086ef6548421dbd95210866f6548421ebd9121087ac6448421dbd4d210876d5348421bbd85210876e5148421f990521087e54148421bdd95210877765484219dd9521087b76448421ed19121086f76248421f9d8921087765248421f994921087e64248421f9509210877b50940219f992500867d64940219f98e500867d63940219fd91500867c64540219fd8d500867c6354021dd88550087752154021af99050086bd6414021b798c50086dd6314021de540500875f5394f40bb98a53d0
  | 27 => 0x219fd97434867e65d0d219f597434867c65d0d21cfd53434873c54d0d219fd96434867e6590d219f596434867c6590d21cfd52434873c5490d21bb98a43486ed6290d219fd95434867e6550d219f595434867c6550d21cfd51434873c5450d21bdd8543486f46150d219fd94434867e6510d219f594434867c6510d21cfd50434873c5410d21bb98843486ed6210d21bd98443486f56110d219f997424873f54d0921cf15342486f661d0921bd587424867e6590921cfd52424873c54909219f195424873f5450921cf15142486f76150921bd185424867e6510921cfd50424873c5410921eb508424867e65cc921af99332486bd64cc921cfd53324873c54cc921d7d4f324875c53cc921bd98732486f561cc9219f996324873f548c921cf15232486ee658c921db99632487af548c921db952324876c548c921eb152324872c548c921bb58e324876e538c921db14e32486ee618c9219f195324873f544c921cf151324875f534c921d714d32486f7614c921bd185324876c654c9219b19532487af544c921db951324876c544c921eb151324872c544c921f3d8d32487cf534c921db94d324876c534c921f314d324874c534c921f9d8532486ec614c921f9185324867e650c921cfd50324873c540c921bb988324867e65d0521cfd53414873c54d0521bb98b41486ed62d05219f996414873f5490521cf152414867f65505219f595414867c6550521cfd51414873c5450521bbd8941486ec62505219f994414873f5410521cf15041487b541105219f997314873f54cc521cf153314875f53cc521d714f31486ee62cc521bb58b314867e658c521cfd52314873c548c5219fd95314867d654c5219f19531486bf644c521af191314873f544c521cf151314875f534c521d714d31486ef624c521bb189314867e650c521af99031486bd640c521cfd50314873c540c521bb98831486ed620c521f54c431486fa600c521be580314873f54c8521cf15321487b754c8521ed15321487e632c8521f94cb21486f560c8521cfd52214873c5488521ebd5221487ac5488521bbd8e21486ed6388521f9d46214873f54d4121cf153504867e64d41219f593504867e63d41219f58f504876e32d4121db4cb50486be6494121af592504873f5494121cf152504877b5094121afd9150486bc6454121cfd51504873c5454121b7d8d50486dc6354121cfd50504873c5414121de540504867e64141219f590504867e63141219f58c504867e63d50219f58f540867e62d5021db98b540867e61d5021dd987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf55054086de6315021b758c54086fa6015021be580540867e6415021cf990540867e6
  | 28 => 0x58053886796014e219fd97438867e65d0e219f597438867c65d0e21cf953438873d54d0e219fd96438867e6590e219f596438867c6590e21bb98a43886ed6290e219fd95438867e6550e219f595438867c6550e21cf951438873d5450e21bdd8543886f46150e219fd94438867e6510e219f594438867c6510e21bd98443886f56110e21cf953428873d54d0a21bd98742886f561d0a21cfd52428873c5490a21cf951428873d5450a21bdd8542886f46150a21cfd50428873c5410a21af99332886bd64cca21d794f328875d53cca21bd98732886f561cca21d794d328875d534ca21bdd8532886f4614ca21f34c8328873e5490621cf55241886ee6290621bb58a418873e5410621cf55041886ee6210621bb58841887b54110621d794e318875d538c621bb98a31886ed628c621afd9131886bc644c621af99031886bd640c621d794c318875d530c621bb98831886ed620c621f54c431886fa600c621be58031886ed65c8621db597218876f53c8621db54f21886f565c8621dd59721886f560c8621af99350886bd64d4221af99250886bd6494221ded42508867e6494221cf992508863e64942219f592508873d64942218f592508867e63942219f58e508867f64542219f191508867f63542219f18d508877950142219f98f544867d63d51219f983544867d60d5121cfd8f544873e63d5121cf58f544873c63d5121cfd8b544873d62d5121cfd87544873d61d5121cfd83544873e60d5121cf583544873c60d5121cfd52544867e64951218f992544867e63951219f58e544867d6295121db58a544867d6195121dd586544867e60951219f582544873f64551219fd8d544867c63551219fd89544876f62551219fd85544877761551219fd81544867c60551219f994544873d5415121cf990544867e63151219f58c544867e60151219f58054486be6515121cf994544863e6515121cfd8c544873e6315121cf58c544873c6315121cfd88544873d6215121cfd84544873d6115121cf484544873f6015121cf980544873d6015121cf180544873f54d4d21cf153534867e64d4d219f593534867e60d4d219f58353486be6494d21af592534873f5494d21cf152534875f5394d219f992534873e6494d218f992534867d6494d21cf592534863d6494d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d219f58253486bf6454d21af191534873f5454d21cf15153486fb6054d21be181534867f6454d21cfd91534863f6454d219f191534873c6454d218f191534875f6354d219fd89534876f6254d219fd8553487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f994534873f5414d21cf150534875d5314d219f990534867d6414d21d798c534876d6214d219f980534867d6014d
  | 29 => 0x3c86bd64d4f219f99353c873e64d4f218f99353c867d64d4f21cf59353c863d64d4f21db98b53c877561d4f219f98353c867d60d4f21af99253c86bd6494f21d7d4e53c867e6494f21cf99253c863e6494f219f59253c873d6494f218f59253c876e6294f219f98253c867d6094f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c875d5314f219f99053c867d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f219f19743c873f54d0f21cf15343c875e53d0f21d754f43c867f6590f219f99643c867d6590f219f19643c873e5490f21cf55243c86ee6290f21bb58a43c867f6550f219f99543c867d6550f219f19543c873f5450f21cf15143c86f76150f21bd18543c867f6510f219f99443c867d6510f219f19443c873e5410f21cf55043c875e5310f21d754c43c86ee6210f21bb58843c873e5490b21cf55242c86f66190b21bd58642c873e5410b21cf55042c87ad4210b21bd98442c86f56110b21af99332c86bd64ccb21d794e32c875d538cb21bd98632c86f5618cb21db59632c876e548cb21db15232c876e538cb21f394e32c87cd538cb21db14e32c86ee618cb21f998632c87e5618cb21bbd9532c876f654cb21db95132c876c544cb21f3d8d32c876e534cb21db14d32c86ec614cb21d794c32c875d530cb21bd98432c86f5610cb21cf95341c873d54d0721bb98b41c86ed62d0721cfd5241c873c5490721cf95141c873d5450721bbd8941c86ec6250721cfd5041c873c5410721d794f31c875d53cc721bb98b31c86ed62cc721afd9131c86bc644c721d794d31c875d534c721bbd8931c86ec624c721af99031c86bd640c721bb98831c86ed620c721be98031c86f9600c721ded4250c867e64943219f59250c867e63943219f58e50c867f64543219f19150c867f63543219f18d50c876e3254321db4c950c86be6414321af59050c86de6314321b758c50c87795014321be98354886f960d52219f98f548867d63d5221db58b548877661d52219f983548877a60d52219e983548867d60d5221de583548867960d5221cfd52548867e63952219f58e548867e60952219f582548873f64552219fd8d548867c63552219fd81548867c6055221cf550548873e64152219f98c548867d6315221db588548877661152219f980548867d60152219f993538867d64d4e21db58b538877661d4e219f983538867d60d4e21d7d4e538867e6494e219f592538867e6094e219f582538867f6454e219f191538875f6354e219fd81538867c6054e21af99053886bd6414e21d754c53886fa6014e21be580538867e6414e21cf990538863e6414e219f590538873d6414e218f590538875e6314e21db58853887766114e219f980538877a6014e219e980538867d6014e21de
  | 30 => 0xbc644c431cf951310c73d544c431db949310c76d524c431b7d95310c75f654c43197d95310c79f644c431e7191310c79e544c431e7551310c7ce524c431f3549310c6df614c431d7945310c7d6414c431f5505310c6f7654c431ddd95310c677654c431edd91310c6f6644c431bd191310c7b4644c431ad191310c7b6544c431ed551310c6f7634c431f5d8d310c776534c431f594d310c7d6434c431f550d310c7e6524c431f9549310c7d7324c431f54c9310c6be64d4031af593500c73e54d4031cf553500c6ee62d4031bb58b500c76e52d4031db54b500c73e5494031cf552500c76e5294031db54a500c77b50940319f992500c67d64940319f98a500c67d6294031ded52500c77a5494031ee952500c73a5494031de552500c7b95494031ce552500c7785494031ded4a500c77a5294031fa94a500c76a5294031de54a500c7e95294031da54a500c7785294031fcd06500c7f04194031f6cc6500c7f23194031f64c6500c7f13194031ded92500c77a6494031de592500c7786494031de18e500c77b4394031de90e500c7794394031de10e500c77b6294031de98a500c7796294031de18a500c77b4294031de90a500c7794294031de10a500c77b3294031de8ca500c7793294031de0ca500c7786194031ded06500c77a4194031de506500c7784194031decc6500c77a3194031de4c6500c73e5454031cf551500c76e5254031db549500c67f64540319f191500c67f62540319f189500c7774154031dd105500c7763154031dd4c5500c77b6554031ded51500c77a5454031ee951500c73a5454031de551500c7b95454031ce551500c7785454031ded49500c77a5254031fa949500c76a5254031de549500c7e95254031da549500c7785254031fcd05500c7f04154031f6cc5500c7f23154031f64c5500c7f13154031ded91500c77a6454031de591500c7786454031de98d500c77b4354031de90d500c7794354031de10d500c77b6254031de989500c7796254031de189500c77b4254031de909500c7794254031de109500c77b3254031de8c9500c7793254031de0c9500c77a6154031ded05500c7734154031de905500c7794154031de105500c7704154031decc5500c77a3154031dc8c5500c7793154031dc4c5500c7783154031af990500c6bd6414031cf950500c73d5414031bb988500c6ed6214031db948500c76d5214031be980500c7795014031b798f54c86dd63d53219f98f54c875e63d53219798f54c867d63d5321d758f54c865d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c867e63953219f58e54c867e60953219f58254c873f64553219fd8d54c867c63553219fd8154c867c6055321cf55054c873e64153219f98c54c867d6315321db98854c877561153219f98054c867d6015321af9935
  | 31 => 0x948319f992520c67d64948319f982520c67d6094831dbd52520c76e5494831eb952520c72e5494831db552520c7ad5494831cb552520c76c5494831dbd92520c76e6494831db592520c76c6494831db18e520c76f4394831db90e520c76d4394831db10e520c76e6194831db186520c76f6094831db982520c76d6094831db182520c73e5454831cf551520c67f64548319f191520c67f60548319f181520c76f6554831dbd51520c76e5454831eb951520c72e5454831db551520c7ad5454831cb551520c76c5454831dbd91520c76e6454831db591520c76c6454831db98d520c76f4354831db90d520c76d4354831db10d520c76e6154831db185520c76c3154831dbd81520c76e6054831db581520c76c6054831af990520c6bd6414831cf950520c73d5414831bb988520c76d5214831be980520c6f960148319fd97420c67e65d08319f597420c73e54d0831cf553420c76e52d0831db54b420c67f65908319f996420c67d6590831cf952420c73d5490831b798e420c6dd6390831db94a420c76d5290831bd986420c6f561908319fd95420c67d65508319f195420c73e5450831cf551420c76e5250831db549420c6f76150831bd185420c67f65108319f994420c67d6510831cf950420c73d5410831db948420c76d5210831af993320c6bd64cc831cf953320c73d54cc831db94b320c76d52cc831bd987320c6f561cc8319f596320c73e548c831cf552320c76d528c8319fd95320c73e544c831cf551320c76e524c831cf950320c73d540c831db948320c76d520c831f34c8320c6f6610c831bd584320c67e64944319f592510c67d65d0431cf953410c73d54d0431db94b410c76d52d0431bd597410c77565d0431ddd53410c7b654d0431dd553410c7b554d0431cd553410c6f563d0431dd94f410c7b743d0431ed50f410c7e652d0431f954b410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c76e5290431db54a410c6f661904319fd95410c73e5450431cf551410c76e5250431db549410c67f65104319f994410c67d65104319f194410c73e5410431cf550410c6de6310431b758c410c76e5210431db548410c7b54110431bd594410c77565104319d594410c6f66410431ed990410c7775410431ed950410c7755410431ed550410c7d66310431bd58c410c7d56310431b558c410c7765310431ed90c410c7b44310431f9948410c7e55210431ed908410c7b44210431cf953310c73d54cc431db94b310c76d52cc431e7953310c79d54cc431f394b310c7cd52cc431f5d07310c7d441cc431cf952310c73d548c431b758e310c75e538c431db94a310c76d528c431bd992310c6f4648c431ed952310c7b5548c431bd58e310c776538c431f594e310c7e6528c431f954a310c67f654c431afd91310c6
  | 32 => 0x19f197424c73f54d0931cf153424c67e65909319f596424c67c6590931cfd52424c73c54909319fd95424c67e65509319f195424c73f5450931cf151424c67e65109319f594424c67c6510931cfd50424c73c5410931b798c424c6dd6310931bd984424c6f561109319f997324c6be64cc931af593324c73f54cc931cf153324c73f548c931cf152324c76f528c931db14a324c6f6618c931bd586324c73f544c931cf151324c76f524c931db149324c6f7614c931bd185324c67e650c931cfd50324c73c540c9319f997414c73f54d0531cf153414c6de63d0531b758f414c67e6590531cfd52414c73c54905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c67e6510531cfd50414c73c5410531cfd53314c73c54cc531edd53314c77654cc531dd153314c7b454cc531cd153314c6f560cc531cfd52314c73c548c531e7d52314c79c548c531f5d46314c73f54d4131cf153504c67e64d41319f593504c67e62d41319f58b504c6be6494131af592504c73f5494131cf152504c77b5094131afd91504c6bc6454131cfd51504c73c5454131bbd89504c6ec6254131cfd50504c73c5414131de540504c67e64141319f590504c67e62141319f588504c6ee62d5031bb58b540c6fa60d5031be583540c67e63d5031d798f540c67e62d5031db98b540c66e62d50319f58b540c76d62d50319b58b540c67e61d5031dd987540c67e60d5031de983540c67a60d50319f583540c77960d50319e583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c63d6595031ed186540c73e6395031cf18e540c73f6295031cf98a540c73d6295031cf18a540c73e6195031cf186540c73f6095031cf982540c73d6095031cf182540c73f64550319fd89540c67c6255031dd185540c67f60550319f181540c73f6555031ed185540c73e6355031cf18d540c73f6255031cf989540c73d6255031cf189540c73e6155031cf185540c7346155031cf0c5540c73f6055031cf981540c73d6055031cf181540c6be6415031cf550540c6ee6215031bb588540c6fa6015031be580540c67e6415031cf990540c63e64150319f98c540c75e63150319f988540c76e62150319b988540c67d6215031db588540c66d62150319f984540c77661150319f980540c77a60150319e980540c67d6015031de580540c67960150319f992530c67d6494c319f597430c73e54d0c31cf553430c67f6590c319f596430c73e5490c31cf552430c6ee6290c31bb58a430c6f66190c31bd586430c67f6550c31cf951430c73d5450c31bdd85430c67f6510c319f594430c73e5410c31cf550430c6f66110c31bd584430c6be64d4831af593520c73e54d4831cf553520c6fa60d4831be583520c73e5494831cf552520c76f52
  | 33 => 0x8a548c67e60952319f582548c73f64552319fd89548c67c62552319fd81548c67c6055231cf550548c73e6415231d758c548c67e62152319f588548c77661152319f980548c67d6015231cf953438c73d54d0e31bd987438c6f561d0e31cfd52438c73c5490e31bb98a438c6ed6290e31cf951438c73d5450e31bdd85438c6f46150e31cfd50438c73c5410e31dbd4a528c67e6494a319f592528c67e6094a319f582528c6bf6454a31af191528c67f6454a31cfd91528c63f6454a319f191528c73c6454a318f191528c67f6054a319f181528c76d5214a319fd97428c67e65d0a319f597428c67f6590a319f996428c67d6590a31cfd52428c73c5490a31b798e428c6dd6390a319fd95428c67d6550a319f195428c67f6510a319f994428c67d6510a31cfd50428c73c5410a31bd984428c6f56110a31af993328c6bd64cca31db94a328c76d528ca31bd986328c6f5618ca31db949328c76d524ca31bdd85328c6f4614ca31f34c8328c73f54d0631cf153418c73e5490631cf552418c6de6390631b758e418c73f5450631cf151418c73e5410631cf550418c6de6310631b758c418c6dd65cc631d7597318c6f565cc631dd597318c77654cc631dd153318c6f560cc631af992508c6bd6494231ded42508c67e6494231cf992508c63e64942319f592508c73d64942318f592508c67e62942319f58a508c67f64542319f191508c67f62542319f189508c77950142319f98b544c67d62d51319f983544c67d60d5131cfd8f544c73d63d5131cfd8b544c73e62d5131cf58b544c73c62d5131cfd87544c73d61d5131cfd83544c73e60d5131cf583544c73c60d5131cfd52544c67e64951318f992544c67d6395131d758e544c67e62951319f58a544c67d6195131dd586544c67e60951319f582544c73f64551319fd8d544c75f63551319fd89544c67c62551319fd85544c77761551319dd85544c67f60551319f181544c67e6515131cf550544c73e64151319f988544c67d62151319f980544c67d6015131af994544c73e65151318f994544c73f6315131cf58c544c73f6215131cf988544c73d6215131cf188544c73f6115131cf584544c73d3115131cfd80544c73e6015131cf580544c73c60151319f997434c73f54d0d31cf153434c6f661d0d31bd587434c67e6590d31cfd52434c73c5490d31bb98a434c6ed6290d319f195434c73f5450d31cf151434c6f76150d31bd185434c67e6510d31cfd50434c73c5410d31cfd53524c73c54d49319f993524c67d64d49319f983524c67d60d4931af992524c6bd6494931cfd52524c73c5494931dbd4a524c6bf6454931af191524c73f5454931cf151524c6fb6054931be181524c73f5414931cf150524c76d52149319f990524c67d64149319f980524c67d60149319f997424c67d65d093
  | 34 => 0x1067d650c841afd9032106bc640c841cf90e511073c4394441cf90a511073c4294441af98f411073d53d0441af98b41106bd60d0441af592411073e5490441bd59241107765490441ed95241106f66390441ed90e41107b44390441ed90a41107b44290441bd582411067f6550441afd95411073f65504418fd9541106bc6350441cf54d41106bc6250441afd85411073e5150441afd8141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441bd18d41107b64350441ed10d41107b74250441ed50941106f76050441ded42501067e63940419f58e501067e62940419f58a501073e4294041cf10a501067f63540419f18d501067f62540419f18950106de6314041b758c50106ee6214041bb58850107795014041bb98b54cc6ed62d5331d798f54cc67e62d5331db98b54cc66e62d53319f58b54cc76d62d53319b58b54cc77561d53319f98354cc67d60d5331cfd5254cc67e62953319f58a54cc67e60953319f58254cc73f64553319fd8954cc67c6255331ddd8554cc67f60553319f18154cc73d5415331cf99054cc75e63153319f98854cc67d6215331dd58454cc67e60153319f58054cc73f54d0f31cf15343cc73e5490f31cf55243cc6ee6290f31bb58a43cc6f66190f31bd58643cc73f5450f31cf15143cc6f46150f31cf95043cc73d5410f31bd98443cc6f56110f31af99352cc6bd64d4b31dbd4a52cc67e6494b319f59252cc67e6094b319f58252cc67f6454b319f19152cc67f6054b319f18152cc76d5214b319fd9742cc67e65d0b319f59742cc76e52d0b31db54b42cc67f6590b319f99642cc67d6590b31cf95242cc73d5490b31bd98642cc6f56190b319fd9542cc67d6550b319f19542cc6f76150b31bd18542cc67f6510b319f99442cc67d6510b31cf95042cc73d5410b31b798c42cc6dd6310b31db94842cc76d5210b31af99332cc6bd64ccb31db94b32cc76d52ccb31bd98732cc6f561ccb31db94832cc76d520cb31bd98432cc6f5610cb31cf95341cc73d54d0731b798f41cc6dd63d0731bd59741cc77565d0731ddd5341cc7b654d0731dd55341cc7b554d0731f598f41cc6f563d0731f558f41cc7b743d0731ed50f41cc73f5490731cf15241cc73e5450731cf55141cc6df6350731b718d41cc73f5410731cf15041cc7b54110731bd59441cc7756510731ed99041cc7775410731edd5041cc7755410731ed15041cc6f56310731ed90c41cc7b44310731ed90841cc7b44210731ded4250cc67e64943319f59250cc67e62943319f58a50cc67f64543319f19150cc67f62543319f18950cc7774154331dd10550cc6be6414331af59050cc6ee6214331bb58850cc7795014331d758f548c67e62d52319f58b548c77661d52319f983548c67d60d5231cfd52548c67e62952319f5
  | 35 => 0x46150d41e7d8d435079f5350d41cf14d435079c5350d41edd8543506bc6150d41ed18543506b46150d419f99443506be6410d419f98f525067d63d49419f983525067d60d4941b798e52506dd6394941dbd4a525076d52149419f98c525067d6314941cfd0c525073d43149419f980525067d60149419f997425076f5290941db14a42506f66190941bd586425076f5250941db14942506f76150941bd185425067e6510941eb508425067e65cc9419f597325067c65cc941af99332506bd64cc941d7d4f325075c53cc9419f996325067d658c9419f196325076f528c941db14a325067f654c9419f995325067c654c941d7d4d325075c534c941dbd49325076c524c9419f994325067d650c9419f19432506be640c941af59032506f6610c941bd584325077453d0541edd0f41507b543d0541af58e415073c5390541cf14a41507b751905419f98f505067d63d4141cfd0f505073d43d41419f98b505067d62d4141ddd07505073e41d4141ded4250506df6354141b718d50506ef6254141bb189505077950141419f98c505067d63141419f988505067d6214141d7d4e531067e6294c419f58a531067e6094c419f582531067f6254c419f18953107746154c419fd81531067c6054c41d754c53106ee6214c41bb58853106fa6014c41be580531073e54d0c41d794f431075d53d0c41bd98743106f561d0c419f59643106ee6290c41bb58a43106bd6590c41cf596431063d6590c41af98e431073d5390c41af98a43107ae6290c41ab98a43107ad6290c41edd8643106bd6190c41ed18643106bd6090c419fd95431073e5450c41bdd85431075e5310c41d754c43106f66110c41bd58443106be6310c41e798c431079e5310c41cf54c431079d5310c41af98843107b66110c41af58443107b56110c41af580431076f52948419f98e521067d63948419f982521067d60948419fd8d521067c63548419fd81521067c6054841b798c52106dd6314841db54852106fa6014841be580521076e52d0841db54b42106f661d0841bd587421067d6590841af596421073d6590841af98e421073d5390841af98a421073d5290841af58642106bd60908419fd95421076e5210841db54842106f66110841bd58442106be6310841cf54c42106be6210841eb98842107ae5210841cf54842107ad5210841cb54842107b66110841af58442107b56110841ad58442106bd60108419fd97321067e65cc8419f59732106be64cc841af593321075e53cc841d754f321067f658c8419f996321067d658c841af99232106bd648c841db94a321076d528c841eb10a32106f6618c841bd586321067f654c8419f595321067c654c841afd9132106bc644c841d794d321075d534c841db949321076d524c841eb10932106f7614c841bd185321067f650c8419f99432
  | 36 => 0xf41d754c43d06f66110f41bd58443d076f5294b419f98e52d067d6394b41cfd0e52d073d4394b419f98252d067d6094b419fd8d52d067c6354b419fd8152d067c6054b41db54852d076e52d0b41db54b42d06f661d0b41bd58742d076e5210b41db54842d07ad4210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d06be64ccb41af59332d067f658cb419f99632d067d658cb41bd98632d06f5618cb419fd9532d067d654cb419f19532d06f7614cb41bd18532d067f650cb419f99432d067d650cb41af99032d06bd640cb41ded4250d067e63943419f58e50d067e62943419f58a50d067f63543419f18d50d073f4354341cf50d50d067f62543419f18950d07795014341d7d4e539067e6294e419f58a539067e6094e419f582539067f6254e419f189539067f6054e419f181539075d5314e41bb98853906ed6214e41be98053906f96014e41d794e439075d5390e41bb98a43906ed6290e41bd98643906f56190e41e794e439073d5390e41e754e43906be6290e41eb98a43906ae6290e41eb58a43907b66190e41af58643907b56190e41af582439075e5350e41d754d43906f76150e41bd18543906bd6510e41cf594439079e6310e41cf54c43906be6210e41af58443906bd6010e41be98352906f960d4a41dbd4a529067e6394a419f58e529067e6094a419f582529067f6354a419f18d529067f6054a419f181529076d5214a41db94a429076d5290a41bd98642906f56190a41af98e429073d5390a41eb94a429073d5290a41eb54a42907b66190a41af58642907b56190a41af582429076e5250a41db54942906f76150a41bd18542906bd6510a41cf59442906be6310a41cf54c42907ae6210a41cf54842906bd6110a41af580429067f65cca419f997329067d65cca41af99332906bd64cca419fd96329067e658ca419f59632906be648ca41af592329076e528ca41db54a32907ac428ca419fd95329067d654ca419f19532906bf644ca41af191329076e524ca41db54932907ac424ca419fd94329067e650ca419f59432906bf640ca41af19032906f6610ca41bd58432906bd65d0641cf59741906be63d0641cf54f41906be62d0641af58341906f565d0641dd597419077653d0641bb98b50906ed62d4241ded42509067e63942419f58e509067e62942419f58a509073e4294241cf10a509067f63542419f18d509067f62542419f18950907774154241de540509067e62d4d419f58b535067e60d4d419f583535075f5394d41bb98a53506ed6294d41d754c535067e6214d419f588535067e6014d419f580535067e65d0d41af997435073e65d0d418f997435073c53d0d41af98743506bd6490d41d7d4e435075c5390d41bb98a43506ed6290d41bd98643506f56190d41d7d4d435075c5350d41bdd8543506f
  | 37 => 0xaf590504caf66114132bd584504cb7950141329f990504cb3e64141328f990504ca7d6414132cf590504ca3d6414132dbd08504cb6c42141329f984504cb7661141329d984504ca7d6114132dd584504ca7561141329f98f540cb5e63d50329f98b540cb6e62d50329b98b540ca7e61d50329f587540ca7e60d50329f583540ca7d6595032cfd52540ca7e61950329f586540ca7e60950329f582540cb3f64550329fd85540ca7c61550329fd81540ca7c6055032cf550540caf66115032bd584540cafa6015032be580540ca7e6415032cf990540ca7e6315032d798c540ca7e6215032db988540ca7e6115032dd984540ca7661150329f584540cb7561150329d584540ca7e6015032de980540ca7a60150329f580540cb7960150329e580540ca7e6494c32cf992530ca3e6494c329f592530cb3d6494c328f592530ca7d65d0c32cfd53430cb3c54d0c329fd96430ca7d6590c32cf952430cb3d5490c32bb98a430caed6290c329fd95430cb3f5450c32cf151430caf76150c32bd185430ca7f6510c329f594430cb3e5410c32cf550430caee6210c32bb588430ca7e64948329f592520ca7d65d0832db94b420ca7f65908329f596420cb3e5490832cf552420cade6390832b758e420ca7f65508329fd94420ca7e65108329f594420ca7c6510832cf950420cb3d5410832b798c420cadd6310832db948420cabe64cc832af593320cb9e64cc832e7593320cadd638c832d794e320cb6e548c832db152320caed638c832db94e320cbce538c8329fd95320cadf654c832d7d95320ca5f654c832b7d89320cb5e524c832f3909320cbcd424c832bbd95320cb6f654c8329bd95320cb6e544c832db151320caef634c832f3d8d320cb6e534c832f394d320cbce434c832f350d320cb7751944329f992510ca7d64944329f982510ca7d6094432afd91510cabc64544329fd91510cb3f64544328fd91510ca7c6454432cf191510ca3c6454432db8c9510cb6d32544329fd81510ca7c6054432af990510cabd6414432dd544510cafa6014432be580510cb7b50940329f992500ca7d64940329f986500ca7d61940329fd91500ca7c6454032d7cc9500cb6e3254032d74c9500cb6d32540329fd85500ca7c6154032af990500cabd6414032bd984500caf56114032de540500cb5f5394f41bb98a53d06ed6294f419f98a53d076e6294f419b98a53d067d6294f41db58a53d066d6294f419f98253d067d6094f419fd8953d067c6254f41ddd8553d067f6054f419f18153d075d5314f41d794f43d075d53d0f41bd98743d06f561d0f41cf94f43d079e53d0f41e754f43d06be61d0f41ed98743d07b561d0f41bb98a43d06ed6290f41bd18543d06bf6550f41cfd9543d079f6350f41cf94d43d07b76150f41af18543d07b46150f41ad18543d075e531
  | 38 => 0x7428cb6d65d0a32dbd53428cb6d54d0a32bb98f428caed61d0a32bb583428cb3e5490a32cf552428cade6390a32b758e428cb3e5410a32cf550428cade6310a32b758c428cbad4210a32bb594428cb6d6510a32eb990428cb6f5410a32eb950428cb6d5410a32eb550428caee6310a32f398c428cbcd6310a32ebd0c428cbad4310a32bb584428caed6010a32af993328cabd64cca32b7597328cb5d65cca32e7993328cb9d64cca32bb597328cb6d65cca32bb993328cbae64cca32ab993328cbad64cca32bb193328caed61cca32bb583328cabe64d4632af593518cb7751946329f992518ca7d64946329f982518ca7d60946329fd91518ca7c64546329fd81518ca7c6054632dd544518cb7b50942329f992508ca7d6494232dbd0a508cb6c42942329f986508ca7d61942329fd91508ca7c6454232d7cc9508ca7f61542329f185508cabe6414232af590508caf66114232bd584508cb795014232db58b544ca7e61d51329f587544ca7e60d51329f583544cb3f54951329f992544ca7d6395132d758e544ca7d6295132db58a544ca7e61951329f586544ca7e60951329f582544caf76155132bd185544cafb6055132be181544cb3f64551329fd8d544cb5f63551329fd89544cb6f62551329fd85544cb7761551329dd85544ca7c6155132dd185544ca7461551329fd81544cb7b60551329ed81544ca7c6055132de181544ca7860551329f994544cb3d5415132cf990544ca7e61151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d329f996434caee6290d329f195434cb3f5450d32cf151434caef6250d32bb189434caf76150d32bd185434ca7e6510d32e750c434ca7e65d0932cfd53424cb3c54d0932b798f424cadd63d0932bb997424cb6e65d09329b997424cb6f54d0932ebd53424cb6d54d0932eb153424caee63d0932f398f424cace63d0932f358f424caed61d0932bb583424ca7e6590932cf952424cb3d5490932bb98a424ca7f65509329f595424ca7c6550932cfd51424cb3c5450932b7d8d424cadc63509329f994424cb3e5410932cf550424cbad4210932bb994424cb6e6510932bb990424cbae6410932dbd50424cbae5410932db550424cbad5410932bb98c424cbaf4310932eb50c424caed6110932bb580424cabe64cc932af593324caee64cc932eb993324caae64cc932eb593324caec64cc932bb587324caed60cc932f3d4a324cbcf428c932f310a324cadd608c9329f993514ca7d64d45329f983514ca7d60d4532ddd46514cabf6454532af191514cafb6054532be181514cb7551145329f990514ca7d64145329f980514ca7d60145329f993504ca7d64d41329f987504ca7d61d4132ded42504cabf6454132af191504caf76154132bd185504cabe6414132
  | 39 => 0xabf6250842cf9494210abc6150842af1814210aef6550842dbd954210a6f6550842bbd914210baf6450842db9514210bae5450842bbd8d4210baf4350842eb50d4210aec6050842ddd465110a7e63944429f58e5110a7e60944429f5825110a7f63544429f18d5110b3f4354442cf50d5110a7f60544429f1815110ade6314442b758c5110b755114442be9805110af96014442ded425010a7e63940429f58e5010a7e61940429f5865010a7f63540429f18d5010b3f4354042cf50d5010b3f4254042cf5095010a7f61540429f1855010ade6314042b758c5010af66114042bd5845010b795014042d798f54ccb6d62d53329f98754cca7d61d53329f98354cca7d60d5332cfd5254cca7e61953329f58654cca7e60953329f58254ccb3e6395332cf18e54ccb3f6295332cf58a54ccb3f6195332cf98654ccb3d6195332cf18654ccb3f6095332cf98254ccb3d6095332cf18254ccb3f64553329fd8554cca7c61553329fd8154cca7c6055332cfd9554ccb3e6355332cf18d54ccb3f6255332cf58954ccb3f6155332cf98554ccb3d6155332cf18554ccb3f6055332cf98154ccb3d6055332cf18154ccb3d5415332cf99054ccb5e6315332db58854cca7e61153329f58454cca7e60153329f58054ccb3e54d0f32cf55343ccb3e5490f32cf55243ccaee6290f32bb58a43ccb3e5450f32cf55143ccaf76150f32bd18543ccb3e5410f32cf55043ccb9d4310f32bb98843ccaed6210f32cf95342ccb3d54d0b32b798f42ccadd63d0b32cf95242ccb3d5490b32cf95142ccb3d5450b32b7d8d42ccadc6350b32cf95042ccb3d5410b32af99351ccabd64d4732cf95351ccb3d54d4732cf95251ccb3d5494732ddd4651cca7e64947329f59251cca7e60947329f58251ccb3e5454732cf55151cca7f64547329f19151cca7f60547329f18151ccabe6414732af59051ccb3e5414732cf55051ccb755114732be98051ccaf96014732af99350ccabd64d4332cf95350ccb3d54d4332cf95250ccb3d5494332ded4250cca7e64943329f59250cca7e61943329f58650ccb3e5454332cf55150cca7f64543329f19150cca7f61543329f18550ccabe6414332af59050ccb3e5414332cf55050ccaf66114332bd58450ccb795014332bd987548caf561d5232d758f548cb6e62d52329f987548cb7661d52329d987548ca7d61d5232dd587548ca7561d52329f983548ca7d60d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f6455232db189548ca7f61552329f185548ca7f60552329f181548cb3d5415232cf990548cb5d6315232db988548ca7e61152329f584548ca7e60152329f580548cb3e54d0e32cf553438caee62d0e32bb58b438caed6290e32cf951438cb3d5450e32bbd89438caec6250e32bdd85438caf46150e32bb59
  | 40 => 0x6194342dd58650d0a7561943429fd8d50d0a7c63543429fd8550d0a7c6154342de54050d0af661d4e42bd5875390b5f5394e429f9865390a7d6194e429f9825390a7d6094e429fd855390a7c6154e429fd815390a7c6054e42d754c5390abd65d0e42cf5974390b3e53d0e42af58b4390abe61d0e42af9834390b5e5390e42d754e4390aee6290e42bb58a4390b5e5350e42d754d4390aef6250e42bb1894390af76150e42bd1854390b9f6350e42cf94d4390b9e5350e42c794d4390b9d5350e42afd894390baf6250e42eb1894390bb76150e42af1854390bb46150e42ad1854390abc6050e42af5974290b3d65d0a42af58f4290abe61d0a42af9834290aed65d0a42db5974290b6d53d0a42b798f5190add63d4642ddd465190a7e63946429f58e5190a7e60946429f5825190a7f63546429f18d5190b3f4354642cf50d5190a7f60546429f1815190b755114642ded425090a7e63942429f58e5090b6f42942429f9865090a7d61942429fd8d5090a7c6354242cfd0d5090b3d4354242cfd095090a7f61542429f1855090ade6314242b758c5090af66114242bd5845090b7950142429f9875350a7d61d4d429f9835350a7d60d4d42d7d4e5350af76154d42bd1855350afb6054d42be1815350b5d5314d429f9845350a7d6114d429f9805350a7d6014d429f9974350b5f5390d42d714e4350aee6290d42bb58a4350b5f5350d42d714d4350aef6250d42bb1894350af76150d42bd1854350a7e6510d42e750c4350b6f53d0942cfd4e4250baf5290942af5824250a7e63d45429f58f5150a7e60d45429f5835150b775194542be9825150af96094542dd5445150a7e63145429f58c5150b3e42145429f9805150a7d60145429f98f5050a7d63d41429f9875050a7d61d4142bd9865050af56194142ded425050b7950141429f98c5050a7d6314142dbd085050b3e42141429f9845050a7d6114142d7d4e5310b6e6294c429f9865310a7d6194c429f9825310a7d6094c429fd855310a7c6154c429fd815310a7c6054c42d754c5310af66114c42bd5845310afa6014c42be5805310b5e53d0c42d754f4310aee62d0c42bb58b4310b3e53d0c42e794f4310b9d53d0c42eb98b4310abd62d0c42eb58b4310abe61d0c42af9834310a7d6590c42af5924310aed6290c429fd954310af76150c42bd1854310abf6550c42cfd954310b9f6350c42cf94d4310abf6250c42eb9894310bad6250c42edd854310abc6150c42ed1854310ab46150c42af1814310abe6410c42d794c4310b5d5310c42bb9884310aed6210c42cfd0e5210b3d4394842af58f4210abe61d0842af9834210abd6490842cf9524210aed6490842db9524210bae5490842bb58e4210baf4390842eb50e4210aee60908429fd954210abf6550842cfd954210a3f6550842afd8d421
  | 41 => 0xd439f9875250e7d61d49439f9835250e7d60d4943dbd4a5250ef66194943bd5865250ef76154943bd1855250efb6054943be1815250f6d52149439f9845250e7d61149439f9805250e7d60149439f98b5150e7d62d45439f9835150e7d60d4543edd935150fd743d4543ed90f5150f7752d4543dd94b5150f7552d4543dd14b5150f7764d4543ddd8f5150f7743d4543dd90f5150f7762d4543dd98b5150f7562d4543dd18b5150f7760d4543dd9835150f7560d4543dd1835150f775194543dd5445150f3e43145439f9885150e7d62145439f9805150e7d6014543bd9945150f766514543ed5905150fd74314543ed90c5150f775214543dd9485150f755214543dd1485150f776414543ddd8c5150f774314543dd90c5150f364314543dd50c5150f776214543dd9885150f756214543dd1885150f776014543dd9805150f756014543dd1805150f7751d4143dd1475050e7e62d41439f58b5050e7e61d41439f5875050ef66194143bd5865050f775194143dd1465050f7b5094143bbd895050eec6254143bdd855050ef46154143ddd455050f745154143ddd445050f745114143de5405050e7e62141439f5885050e7e61141439f5845050f6e6294c43db58a5310ebe61d0c43af5924310f3e5490c43bb98a4310eed6290c43b75924310f5e5490c43e79524310fce6290c43f358a4310e7f6550c43bdd854310ef46150c43afd954310f3f6550c438fd954310ebf6350c43cf94d4310fb76150c43af1854310fb46150c43ad1854310edf6550c43d7d954310e5f6550c43b7d914310f9f6450c43d79514310f9e5450c43f5d854310fd46150c43dbd4a5210f3f4394843cf50e5210e7e61948439f5865210e7e60948439f5825210e7f61548439f1855210e7f60548439f1815210f6d5214843bd9845210ef56114843be9805210ef96014843ddd465110e7e62944439f58a5110e7e60944439f5825110f3f4354443cf50d5110e7f62544439f1895110e7f60544439f1815110eee6214443bb5885110f755114443be9805110ef96014443ded425010e7e62940439f58a5010e7e61940439f5865010f3f4354043cf50d5010e7f62540439f1895010e7f61540439f1855010eee6214043bb5885010ef66114043bd5845010f795014043d7d4e53d0b6d6294f429f98653d0a7d6194f429f98253d0a7d6094f429fd8553d0a7c6154f429fd8153d0a7c6054f42d754c53d0b5e53d0f42d754f43d0aee62d0f42bb58b43d0aee6290f42bdd8543d0af46150f42d794c43d0b5d5310f42e750c43d0aee6210f42bb58843d0b7751947429f98e51d0a7d63947429f98251d0a7d60947429fd8d51d0a7c63547429fd8151d0a7c6054742dd54451d0af66194342bd58650d0b7b50943429f98e50d0a7d63943429f98650d0b7661943429d98650d0a7d
  | 42 => 0x4000400000000006000400000010000000400080030002000400000010002000400000010000000800000000018001400000000000001400080000000000000000000000000000000000000000000100000002000400280000000000c0000000000000000040000000000040000000000000000000001000000000018000000e00000018000000400000008001000000040000000000000000018000000000000000000000200000000000000000000008000000400000008000000000080000000000200000000000000000040000000000000000000000000200000000000000000040000001000000000018001000600000000000000000000000003000200040010003000000100018001000600000000000000000000008002000000000008001000200040000000000000080008000000200040000000000600040000001000600000010000000000000000003000000040008000000000000000003000000000008003000600076f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0ef66194343bd58650d0f7b50943439f98a50d0e7d62943439f98650d0f7661943439d98650d0e7d6194343dd58650d0e7561943439fd8950d0e7c62543439fd8550d0e7c6154343de54050d0ebd65d0e43cf5974390ebe61d0e43b75974390f5d65d0e43dbd4a5290f3f4394a439f9865290e7d6194a439f9825290e7d6094a43ebd0e5290fcf4394a43dbd925290f6c6394a43dbd0e5290f2f4394a43dbd865290f6e6194a43db5865290f6c6194a43dbd825290f6e6094a43db5825290f6c6094a439fd855290e7c6154a439fd815290e7c6054a43dbd955290faf4354a43f3d0d5290f6d6454a43db98d5290f6f4354a43dbd855290f6e6154a43db5855290f6c6154a43dbd815290f6e6054a43db5815290f6c6054a43db5485290eee62d4643bb58b5190f6e52d4643db54b5190f6e5294643db54a5190f7751946439f98a5190e7d62946439f9825190e7d6094643db9495190f6d5254643cfd0d5190e7f62546439f1895190e7f60546439f1815190eee6214643bb5885190f6e5214643db5485190f755114643be9805190ef96014643bb98b5090eed62d4243db94b5090f6d52d4243db94a5090f6d5294243ded425090e7e62942439f58a5090e7e61942439f5865090f6e5254243db5495090f3f43542439fd895090e7c62542439fd855090e7c6154243bb9885090eed6214243db9485090f6d5214243bd9845090ef56114243de5405090eee6290d43bb58a4350f9f5390d43af98a4350fae6290d43ab98a4350fad6290d43af5864350ebd6090
  | 43 => 0x6000000080010000000400080040002000000000000008000400080040000000000000000000000800000010006000000300000000000000100030000000000000000000000000000000000000000000000000001c00000010000000800000000004000000100000000000000080000006000000080020002000000080020000000000000030000000c0008002000000040020001000000040008005000200000010000000000000000002000600000000000000200040000002000a00040008000000a000400100010000000c0000000000000080018006000000000018000000c000000000000000000400100000004001800000000000000800000000000000400100030000000400000000000000000180010002000000180010004000000000030000000800000000000000c0008000000400000020001000000040000002000000040000001000000000008000000000000000000000a000000280000008000000180010006000000100010004000400080000000000800080040008000000000000000000000000030002000400180000004001000080000000000000080000008001400100000000000000080080002000000200020000000000300030000000800080000000000000200000000000000080020000000400100010000000400000070000000800000010006000c00000040000000000080000004000000000000002000800080000006000000080010000000c0000000000200080000000000000000008000000000080000000000000140000000000200000000004000400040010000000000000000000000200040010000000000000000001000600000000000000000040010000000200000000002000000000010001000000000010003000200100010005000000200000002000200000010001000000000018001000c000000080010000000000380030002000400080020002000800080000002000400080010000000000000020004000000000000004000000000000002000400000000004001400000000002000400000000002000800000000008000000080000000000800180000000000800000050000000000580000000000400000000002000800000000000000c00000020000000400000040000000000000000002000800080020002000400000000006000000000000000000800000020002000000000060002000800100040002000000080030004000000080010000000800000000004000800000030000000c00000020002000400000000000000000000040000000c0010003000200000000003000000000000003000000000030000000200000008001000000040000000000000000008000000000040008000000200000018000000600000000000000200040000003000000040000
  | 44 => 0x40000000000600100010000000000000010001000000000000000000000100000001000000000000005000200280000000000200080010000000600080018000000000080000000000200000000002000000040008000000200000010001000000000000000000200000000001000c00000000000000200040000002000000080000000000200000008000000000080018000000000000008000000000000000000000200000000005000200000010004000600000000001000000000000000000000100030000000000140000000000800000000000000000000010001000c000400000090000000800000000000000000000000002000400180000002000000000000000000000080000000000c00000020000000000000040004000800200020002000000280040000000000080000004000000000010002000000000050000000000000010000000400000010000000400100050000000800000010000000000200000002000000000000000000000100010004000c00300000002000c0008000000000040000001000000040000002000000000000001000200040008000000000000000000000000040000003000000040048003000200040000000000800000000003000200000010000000000000000003000000000008000000000000058000000a000000000010004000000280010000000000100040000000000000000002000000000030000000400280000000001000180030000000000000000000000000000020000000c00000000004000000000010008000000100010004000000000000004000000080050000000000380000002000000000000000000c00000030002000000000000000000400000000002000000080000000000000000010008000000000000000000000080000000000000000010000001c0000000000400000008000000000080000003000800040000001000200040010000000c000000000000000000800080000004000400080010000000000000010008000800180000000001400000000000000000280000006000000280000002000800000010000000400100010000000c00000020006000000000010000001800080010000000800080000006000000000020000000000000010000000800000000004001800100010002000400300020006000800000000008000400080050000000000100030002000400000000002000400080000000000000080030008000400300000006000000000010000000800000030004002400300030004000000000000000000000000030000000800000000000000800000010000000800100000004000000000000000000000000020004000400000060000000000000010004000000280030000001000000030004000800300010000000400180020002
  | 45 => 0x2000400200010004000400080000000000000000010000000000180000000000000100000000000000000000000000000100010002000000000000000000c0000000000c00000018002000400080000000000000000000000000600000008000000200000000000000000000000000000000080010000000400000000000000000000018002000000000000000000000000000000000200000000001000000000008000000200080018004000000080000002000c001000080000000000400100020000000000000000000000000000010008000000200020006000000000000002000000000050004000400000010000000000000020002000400000030000000400080010000000000000000000000000280000000000000080010004000000180010002000400280000000000400080000000000000080010002000c00000000006000000000010000000000000000000000000080000004000000000000004000000000000000000400000000000000000000000000001800000000000000000180010002000000580010002000800080010004001000000010000000400000050000000000000020002000400100000000000000000000000000800000010004000000280000000000000000040002000800080000002000000080000000000000080030000000000000020000000000000000000000000000010000000c000800000000000000800000000004002800a0000000000000030000000000080000000000000000000000000400000010000000000000000000000000100000000000000000000002000000000010000000000000010002000400080020000001000000000000000000000000000000000080000000000800000000000000000100010000000400000010006000400000000004000c00000000002000800000020002000000000030008000000080000000001c0000000000400000008001000400040000000000000040000001000000000010004000400000000008000000000008000000400000000000000000080000001000000000000000000200200000007000000000008000000000040000002000400080000000000200000008000000000000000000000000040000000000000000000000000200000000002000000000008002000400040000001000000000050001000c0000000000000040000001000000000008002000100020000000000200000018000000000060000001000000020000000800100000000000000000020008000800000060000000800000020000002000000000014000000000000000000800000020000000000000040004000000000080000001000000020004000800100060000002800000000000000800400020004000000000040014000000200020008000000000080000000
  | 46 => 0x400100000000000000080010000000000180000000000000000010000000000080000000000000080000000000000000040000000000000000002000000000000000000000200020002000400000000000000400000000000000c0008001000000000008002000000000010002000000080000001000000040000000000200000000002000400000008000000800000000000000000000008000000000000000001000200000000003000000100010000000200040000005000c000c0000001000000000010001000000080000002000400080000000000200140000000000000000000000000000000000000000000040008000000800000008000000000000000001000a000000180010006000800000000000000000080010000000000100000000000400000000000000000180010000000400000010000000400100000000000000080000000000400000020000000400080010000000000000010004000000080000000000400300000000000000000000000000000000000000000400000000002000000000000000000400000000002001000080000000000400000000000000400000020000000400000000000001000000020006000000180020000000400100010000000000000020008001400080010000000400000000002000c00000010000000000000020000001400000040000000000280000008000000000000008000000100010000000000000000012000000000020008000000000000000000c00080000000001000080000002000400080020002000000200000000000000080000000000000100000002000400080040000000400080000000000400080000000000400100000002000000100040002000800200010000000000080000008001000000000000000000080000002000000080050000000800080000000000000180000000000000300000004000800000000000000400100070004000000000010000000800080040000000400100010000000000000000008000000000000000000000000000000000800080000002000800000000006000000080030004000c0018000000000080000002000a000400000010000001000080000000000000000000002000400000000000000400000020000000000080000002000000080000004000400080000014000000180000000000000000020000000000000000006000000000000000000000000010000000400000050000000400000010002000000000000000000800000010000000800100000004000000300010000000000080010002000000000000000000800080000004000000000020000000000000000000000000100010002000400100010002000800280020000000000100000000000c0008000000200000000000000000000000000000
  | 47 => 0x6000400280000000000c00080060004000400000010002000000100010006000400180010000000000000000004000000000000000000000000000000000c0010001000c000400000000000000000000030002000000000000000000400300010000000400000000002000000080010002000000080010004000000000000000000400180000000000000000020000000400000000000000000000000000000400080000002000c00100020004000800000030000000000000000000000400000040004000400200000004000400200020004000000080020008000400280020002000400000000000000000100010002000000000000000000000080010002000000000010004000000000020000000400100000000000800000000000000000000000000000c00100000002002400000040002000c00080000002000400080020000000c0000001000200000000001000000040000000000200040000000000c000800080020002000000000000004000400080030000000400080000002000c00000000008000000000020000000400000020000000000080000000000c00000000000000000000020002000000000000000000000080010000000400000000002000800000000000000000100000004000400000000000000000080010000000400000000000000c0000004000a00040000000000000000000000000000080000003000000000010000000000000008000000000100010001000000000010001000000040008000000000000000001000000000000000000400080020001000000040000002000000000018001000000040018000000a000c0000001000000000000002000600000000003000000040000001000600040010001000800000000003000000040000000000000000000006000400000000001000000040008003000200000010000000000000018003000600000000001000000000000000000400080000000000000000000001000000000000000000000040000000000200080000000000600000000001000000000000000000000000000000000000000000000000000000010000000000040000000000200080000001000000140018000000200000000000000200000008002000e000000000020000000000000020000000400000000000000000000000002000000000000004000000000030002000000000000000000800000040000000000100000002000000000010000000c00000000000000c0000003000200000018005000600040000002000200040030000000000000010000000200040008003000000040000002000200000000000000800000018000000200000000002000000080018001000400000000002000800080000000000600000008000000a000000080000000000000000000000001000
  | 48 => 0xf808fe7280d0180000b32000000019672f9e1508000000000000000000033923ec00000000000000000000001ce403520000c1e000016dc0000fe694ce000000000000000000000000000000000000000000000000000011800000429e00010d280000000693000019bf00000000ef287eb08de354c00017a000000000b5180000000000117792910000000000007a612d200004850000000013ec047800000006f04000071f000016c400d955503fc000000011e4000000000000000201c00007218000000000000000000147800000000000000000011dc8000000027c019900000efc000000011c300000000000000000000000000000000000000000000027fa000000000000000000000000000000000088723aa0ecc52ec00000000000000000012d81d3c0000de480000000000000021ba00000000000000000000000000000011be000000003fa000000000000000243e33c800000000f7000005fd00003c3a000038a1674000000000000e3f46a200000001dee00000000000092c00000000000210f00000000000131b0000000000003e30000000000000000baa00000000000000000009bf956b00b0014c0e3206e44001a084dda1a20000514513f9a8d00008fa00001e3e12920000000197e000040e4000000000000000000000000000000000000001a81aa4000000000000000000000000005bd40a0104729b4419c0001ad40f5e65c0a97a22a1e4e00000000000000019d00000e5e0000000000014ea0000000000000000000000000011ba000070680000000000030081e59e2c3fdc00005f600000000000000005223cbe65e4000000000000000cf0801f3d620000e49800004000d940000000000000000000000000000000000000000032144ac1e86279c65580000000000000003f400000000771c4b89f3f0000000000000000056000000000003b96000016499e64130000000016813ce076c873e87a20000506c71002fb0fb8738c0000000380209600000000000036ecbe0164f0000000000000003d54000089300000000000000000001a140000000000000020000000000000000004000000000020000000000000000004000000000000000000400000030000000000000000002000400000040000000000000000000000400180000004000000000030000002000000040000000400000030002000c00000000000000000000000000000400000020004000800000000006000400000020004000c00680030000001000000000002000000100000002000c000000000000000000000100080000000000000000008000000000060004000000400000000002000000080000001000300020000001000000000000000000000020000000000400000004000000200000004000000300000010000000000000004000800000
  | 49 => 0x348447e0000080d0000000000016ee00000000000068c00006c7000000000000226000000000cb41bf0000103800000000000042c00008f840000000000000000000000000000000000242000000000000f1900000cd8000032a05b2000000000000000000000006770bc80000d7b8b0a1a5400000001fa52a1c51d00000aaf000000000000000000066a400000000000000043c8b2b336c000000003020000000000000000000000053880001f486fe80000000110e2764000000000000000000000000000000000000020bc00005dc99240000000094e800000001cac0000000000041d0000000000000000c6a800000001e68439864000007db8000000042100000f9880000000000100121d82dba3e14b6322a426e60000fc30000000000000000000204e0000c06a1bc0000000000000000000213c580800000000000000000039e232c000000e700000000fca8010000000000000000000059dc0000000000000010bf8000000000000000000000020980000000000000000d9000000006a9cafc0a5100000000bbb00000000000055e000000000000f298786000017740000000000000000001b4142360000b9c90263dd200001880b5b00000000000000000000000804000000007a1400014900000000105e800000000000000000000000000000000000004f00cbd97c7000000000000000000000000000000000000000000000000000000000ce500000000000000000000000000000000000000000000000000000000139200000000ce2800042e200000000000364c00000001d6800fc5354000000000000000cc1800000000000c3a800000dc610104f80000192000020400000000000031e0a4629b6000000016a7450483700000000000000000000000350242480000000000015cc0000000339c437874280000000000028600a5005205780001f090f9e1d6c0000000016800000001f8c00005a3c0000000000043dc00000000f8000000000fc600000000000000000b6000000000000000000000000000000000000010792398579c66fa35200000000000000000006bd00000000000000000000000156a0000a3797f8000009f8000000000003d9400000000000651c4db000000000000000000000000000ccf8000000000004582079191c47700000d1b000000000000781000000000000000000000000001c0d00006438000000000008f480001bd604381d600000000057800000000b58000000000000000109036240000000000031f824d1e2741920000c57800000000000000000000000000000000000000000f28000000000000000100f21fe0a500000000000000000a713af0000000000000000000000000002db271c20400000000003070d40000000000000000000e
  | 50 => 0xac41dae000096400000d62000036a9dfc255600000001557000000000000000117e0000000167d1194000028412763c76000000000000000000000000000000767482d0000000000000f100002b6a75e00000544045c4f4c9e397ac0000000000005b9440e2c343250000000024b400022d405187cd00000928000000000001b820ba000010fd80003ba834dc6d120e746ba62790f20747000000000000000000000000000f260000000000000bc00005b88d9e9f8b00003400000000030f2000038d8000285e00000000000000070ac00000000000000000000001f300000000000000001aa00000000000000000000e6200000000000000000002178113800000000000cd70000000000000000000000000000000000000000000000000000000006ed036633502afc00000001858000017180001a648394829a31b0cf4000000000000000000000000000abc0000c08000000000000000000000000dd0a170000164c000000000001c94000093c00000000000117289da199a00000000ef900005918c9c87dd0000077518f80d300004b2c0000fa50088028800010482ee400000000f680000000000000000000000000000000d1c0000c5f000024a00000a948000000000000850000115200000000000000089f8000000000005200cfd16030000000090d00003556000000012ad1ffa000000000000000541800000001ca28bdc320a2372ba400009ea1d7d0000481051b225e0000000025f00003e7a00000000000000088c8000000000004fe4918000000006e0065f80000000000000000000000838c9a3a36100000000f5c9f82000000000d60000000000000000c1e00005254000000016e4734cbb280000000000000014f000f44a500000000000054c0c4a800018500a34e2a80002d664e40a52000000002f8099d800000000000c93000000006400000000000000000ed30000000000011518000352000000001b9b00000000ebc8000000000000000dca0000518800013cc000000000002014140c000000000000000000000000000000000023e000000000000000000042b2000000000002d560000000000040ec0000000000000004f3439d2091293c3b6800000000000000000000003cb400000000000442a000000000000fe854cc000000000000000000215f0c1600000000a0d00000000000000000003fc424280000000000000000000f1a0000f070000390c00000000000000054a8d960000063c025cba2800000000000000000022000000000000000000000000000000000000000000000000000613000000000000d0980f500007ebc00000000cc86d3400000000000000000000000000742c000000000000000000000000008b1c0000edf44c01680c26000000003a74000010e00000000000160a00000000000000000000
  | 51 => 0x5cb400006e0000000000000000000030ec000000000000000da01b0215600000ed1800000000000c050000325e8db800000002ba000000000d69209e00000000000000000000000437000000002850000376c00005778ad20000000000000e62b84596400000003c8e00000001fb30000000000000000b24000000000001d180000000000019c600007180e92069a3b043f01c0a000000000000000000000007448000000000000ce800000000ac4000000000000000000000000000000ebd05a93f147f8c000000000005b6c00000000000000113500000dbe3708000000000000bd4c8c889a16e637c800020703a8e0000aa588422b0600000001fbd0000000020689b00000387c002a35c3f30000000000000000110400000000000000025300000c5639a80000000000080804cd806f0000325001a00db0000000000000003dd65bd8000200826062a7400000000000000011221cb00007ef00a8859a064400008380b822f6a09701318000000000000000000103a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008db0000000044a4000000000000000000047e951b153c39800000000000073b4000175f2d6e526400000000000000000000000000000061900c400000f981259e91041c38dc1ee80000f6200000000a1d000000008c18000030c000000006a30000127c000000000003c5c0001a8a0322000000000000000000000000000000000055e908f0000000000016783a687238000000000000bfcb6fa041000031c40000000000000006de8000000000000000000331a000000000000000000000009aa00000358000000000000000000000000000000a48800000000000fbd8000000000000000000000000000001d3a2b1c37b8000000000000000f6910f1000042ed162800014fa00000001c180000000000008ce00000000538000000000000e1e00000000528000000002f84000000005fe10dc45b400000000000000000000000000000000000003d9e7d948599c671f747b980000000261406d0fa08b0600004b0c0000000000000000000000000000000000da000001a280000000000084b0000000000001fa8000152002380c240000000000000002908000000000000000000053035fc2150000000053f03178a55000048280b8804209505c9800aa0d8000000000001ef200000000cd303b800005654000000000000000000174a05700000000000000000000000000000000000000000010340000000000000005af8000165800001fc8000000000001ea000000000000000000000000000000000009c500000000000000021d669fd0d4000011247a640000000000000000000d0b43300000df7800000007ce83330000215600000000000000000000000
  | 52 => 0x16f000000008cb80000000000075280000000000000000000000000000005d6800000000000000000000000000000000000003abc0000000000000005680000000080fc0000000000000007bf01ba00000000000000000a00000b2e80000000000000002ec26b0000058906e53b7a000000001340000000028300000000000000000000000000006900000000000000000000000000103880000000000000011a81ae000010ae8c0c00005c08000080a00000000000000000002ff800000000000319c0000b9812c8329c00000001bce3224000000032560000f08126a18ca64a800000000000000000000000000000000000000000000000000000000000000006dc0000000000007e918b60000a2f80000000539400000003dbe000000000000000778c000000000000000462000000000a900000000196200000fe86f0000000002ca818e0000000000000000e5200000000000123471740000000000084380000000000000000000000000058f4e79800006c2000100c00000000406cced800032240000000000000000000000011a0000000000000003214000000008c0000000011b68d033d8a26fcf76800024d04e6083d800000000000000000000000000000043200000000af58148000000001e380000000000000007e6000000000000823000000000000000000000002fb800000000000000000000000000000000021c80000000000000001458ef900000000000000000000000284470c811700003468000000000005f280000000304a72e46f18000000001c800000000000000068c8000328a00000000000000002bc9fb0000000002300001d961dd6228000000002a22000000000003e0600000001a123528000000000000000407c0002161383a1600bb9800038540000000000000000000000000000007054cb70000000004f8000000041a4000000022fb0000335400000000000000000000000000000000000000000000000000590d7200f05f88000000000001b980004530000108c00000000000000000000000000000000000000000094d000023a63dc4000000000004d04000000000004fcc0000f5b00000000000000034a00000000000000000000b5b200e314268ec000000000000000995800046ec6b5c000000000000000000000024263ea48f180000000000050180002fe825789cc80001302235c10a12850000774c28c00002b40860c000000000000000477800000008f44488016200005468000094400005218463a14a21aa0000000078400000000000000045be000000010ee00008b6800000000000000000000001226000000000004522000000000001c7a000094617813b78000000019dd000000010d822c200001f043b79a06116a0000743800000000b940000000000037ec00000000000
  | 53 => 0x58145a900002fce6f9c00000000000000000000002a5c0c980000000000000010b98c34176636ad165800000000000000000030c87fe0000000000000000000077100003ec400005f400000000000000000000000000000029a00000495000000000000000163600004cbc00000002ba86f0c00012f30b603ff827880000b0c00000cd800000004bf8000000001be0000000000000002f100000000142e0000a22875c0000000109580002c70000061e8000000032bc0000000000000000000ac1000000000000000337400008ec800000000000bc8a113000000000000000475c0000ca48a01000003f0c47800000005f4c00000002b9850ac0000000000052a8000162e00000000000000014260224f880bf329b836a4000000022e87ad4361800000001a3418b000000007b60000051f305c00003f2800000000000000000000000320000000036560000c7f800000000aa4bcc0000000004a800014c10000000000000000000000000006f40000000000006ef00000000000000000000000000187f000000003af84ca00005c650ab80002b7c00000000000000000003c780000000000000010fb000000000000af10000702c000000000000000000000000000000000000000000000eab0000000000000000dae00000000000000000000000000000000000000c37804a0000000000000002b22000113c03fc00000000000000003a84f9000000000000000000000000000000000007d246744c490fe00002eaa0000000000011a80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000038b8000067a8a34000000000000f37000075dc20c93a42008451c000000017b80000000000000000000000024a00000000000000000000fc400014df0000000079d0000000044640000b6f00007a2c98b8000000000007a2800030ee8b9c0000000000000000000000299e00005a9979912024d2000009a700000000ce0000000000000000000000000000000218e0fc60000000000035784ddc0680000000000004bc0000000000000000000000000011b8000000000000000000000008e649169fe517de54009518000000000000001ce000000000000018a00000000000000000000000000066100002f0800000003ce81e580001ab200000000000000000000000dbd8000000000000000fcb000000000000000241a000066f1f0d032636300000cf91cae00000000000000017b8000000036ba0000000000000000000a919bd30000000000000000000000000019bd000000000000000000082548739d5100000000000000000000000000000000000000942169e156c000000000000000000000000002fa4263430b000000000000000000000002b98000
  | 54 => 0x35c40000a3f19a53fee89e40000a8e42723b7423500000000000000000000000000000022c600000000000230439de76b08f700000000000000007f5267a000109000000000000000000000000000000000003fb45dbc0000c6c28000000000137c36aa76c40000000034000000000000338649b00000000000000000000000383e27444c49cb514f055103258000000000004988000000000009e780000000810c0000000000000000000000024c0000000000000000000dcc8000378c0000214000000000000000000015300000a06822d03345c94c4b800026dc00000001f591ef224dc00000000cf046f84ad1189000000000000000000000007a20000000052380000000055e00000000000338c87a8000000033c600006789a5700000458000217407880000000023f1f1e00011d5909500000000000000000008f70000000000001b1c000000000006064881800000000000000000000001de0a0c8000000000000000000000000000000000000000000000000000009540000000000000000000000000052e84870000000000000000000000000001b50000000000000000000000000000000000000000000000000000000002d2000000000000fb98000000000000000000000074b4000000008ea000000000001ccc4c10000000000000000000000000000070000000011ca3a34e990000000000000001c4700000000f1e0c740000000000000001042000000006f600000000122800000000000e8f80003d3e0000000194828ca0000000000000000000541000012320000fad00001bf80000fae800000006f9400000f43a2a1bfc000000000000000000000000000000000000000001a1cf320bdb380800000000000000000000000000273c4d94000000000000000000000000000000a1d000000000000000063212f483b80001f57341400009c3800000000c4c5729a050000000000016fd0000000082f800000000000fdc80000000000069b0000000000000000000000000000000000000000000000000000016582f680000000000000000002f140000000000000000000030a045000066f00000000000000003df800000000000a87800013f60000000000009ba89442798b950000000000000000000000000000003d844d9c3f6000000000000000000000000000e8f000008e2718000000000000000103f80000000000000000000000821ca2d80000000000000000000000000000000000000000056f00000a163a980000ece34600000000000019180000000000000000000000000000000000b448000000058fc000000000004fc919f19b0387e298830913a300000000b4a800000002d7000000000000000107e0000000019a83968d2826404570dfa8552000000000000cc20e7e818000012aa19ba7bf88f0800027b
  | 55 => 0x7bc6118ba9000000000000000000000000000f61418c00000000000000000000001ccc00000000000000001f4867c0000000000000011e1800000007ff8e7100002ed4000000002b7000078c0a39068400000000f4e80000000000000000001c700000000000000000000000000027ee0000fdd00000000000000017150000000000003d70000000000000003532000030100001e44479d15d000000000000000000005d61888d318d58000000002c4224c03c21a5000000000000000000005bf079868a832a973346c80000a0d0000000000000000000000000000000000000000000000000074686f86b79829120a000000002b200000000000000033381380000000000004788000000000000000d3e0000068200000000000017e000000000000000000000000000000000000019321c6a000000014c830ae15ac0000c780000000000000000c147bec0000000387200000000e1b13bc6ff00000b30000000000000000000089cc6dd163b03060000000000000000000af698e234740000000000000000000777000000000d9c6c18000052a0000000058b1e90000000003a901bc1f24f821615000022407eb00000000000101b000007643cc400000003bda0000000015730b60000d27000000000000b60000000000000000000000001b24a420da142840000000000000000000cca80003bb80000c7e000016840904000000000000000000000010360000ef104c700004198e7b80000000000036c000000000000000000000000000068a03e0ce21724b978b650000000000000003de800003789db400006d3c00000001a9800003952318000032dc00000000000000000000000000000020d8000000000000000c5f00005b951d68a2300000000d390a64000000000001fd0000006c0e62800000000000000000000000000000000000007a385c8192724f28d9c0000000000079080000000000056680001bf14500000000000e500000000b76800000000000000000019788edc0001eb010300000ecd0000000000000000000000010ec604000045160000000171100002bf40000000000010e116f1d460000000000000000000000038400000000000000000003d6c00002f800002be0000000000000000881000000003fd8000025700000000000000004d7000021fc00008e834ea0000000224a065a000000000000000000052c8358473c4a251298000188600000000000000074d518e8000000000000000000154a00000000000000000005d7029919fc00006be1c4f331468dc0208301324058cc0000000000000000000000317e7020000000000007df0000000000000000f2680002c3e00000000000000053fc59d80003920793116980000000000000000003ba078d80000000000000004e0824013a8501800
  | 56 => 0x820000000000000000000000000009c9800000003d4000000000000000000000000000000030480000000000000000000000000000000000000394c000064200003fd0000081e00001ecc3889c710abe299c34e06361c5c1d9c0001e9000002848000000000000000000000000002da82439e1742b05d60000128f065819e40000000312800008ba99d10000000000000001c680000ca680000000000000000000000070c1b6800000007c683ad038a00000000c830fd300000000000000000006a0c00001f721782e14000171235826f38000209d000062c488e869701007bf02e392700aa600000000e70210e0000000000000000000000000000000000000000000000000000000000000000000000000000000000124a239a3c8c0000aa70000000022300003e580000000205c00002f7c13115f5000000003b80000000000000001fef1db800000000000009800010aa0000033c0000000000017400000000000000000000000000000000000000000000000000000224e000000000000000000055180001f4300000000f53000039ba31dc0c00000000000000000000000000005a58000000000000000000276800005c680002fa257a000000001c4c1ed40000000174c8afc00011e504883dac000000000007f1000000000000000000016c70cba130c000000025f400000b00d14000000000000000000000003e39691447263d40000000443289c800007de000000000030f4f00000000a9d000000001ac0362020f000000007c58000000000000000817388a000000000000000630c000000013ea00007190000000086dc0000000021a000000021ec000000011b90000000000000000000000000000001c7a00000260000000000008d6000022c1000000000001d5d0000000000000000000000000015dd3f36355400023c2000047b48660000151872bc901000002607d70d2f14f100000000000000000000000cf489c600000000f8f8000000000000000000000000009f300000000000000000000000000000020d000000000000000000006874000000000000000b0a000030bc000074c80003b122580000000026d600009ca0000000017040001e82000000000001502397e00000000000000057680000000000000000000bbe000000000000000000000006af20150000739800022a00000000000006013e7c000000000000000000000000000000000000000002daa0000f0a800035ea000093086850000000118d16ad179a00000000000115854e40000a8929024ad03c60c7b00000000e66850e0000000000000000c4e2cd85c400000000000117a00000ada00000001e4b000000000000000000000000000000248a000000000001d04000000000000df46408000000000000000000000000000000fcd1e142000205509a00fb26
  | 57 => 0x13e800013b200000000000000042ce0000000098e00004d3826e00000000000065d92420d1200003f1000000000000000000000000000b1085be00000000000000000000000000201000000248000000000007fa000000000000000000000000000860414e113f187000000ad8000000000007d68000000000005ec2031396217c800020e800005ad43e196061f9e612805f21020000000015d800000000000000000044de000000000000000061496a80000ad40000bc18000000000000000000000000000000000000000004ee000000006c3c000108a38483bb00000dcc466a00000001ab302000000ecd8000000000000000000000030747ae8000000000000000000000000000001a460000000000000002d7a00000000c110000000077880000000415400000000000000000000000f587fccb181d5c00000000000168b26da00000000000280814f00000000000000008ce000000000000000141200001a78aae800000001abd1b31943470800000000000000000000001df90164067c0e88c0500000000000000005560000d3315e600004a5c3e62184000005b00000000259823b855b8c8814700000023180700000000b39000000000000000000000000000000056736cc0000600800d3d140000000000000000000000000000000000000000000000000000000015c23afc3eb8000365072a00000000000043e40000000336a000000020af0cb200007c6002319420000b5280000000000000000004462000092a00000000000014880000000000000014182806000000000000000257400000000000000000000002baa000000001f100000000000000004a200007c9800000000000cf8800000002d780000000079e000000011de383238f89cb20773ce600003c100000000000000000000000000000000002e060000000000000007bdc14f8000000000000000d0604d40000000000044b600584248bcf289000009049c9e00000000000000020e6000031e81460000000070500000000000039e0ea037240000edf00000000000049180000000000000000000000557cee68d290ca876a913e9d2c19e62f5000000000568695073e081123cc7a610688000000000002b1a0fd0000000000015502ffa00009881e130000000087a0000367800000000e9f000000000001521283c0000000000000000000e988000000000010a40000000005f40000000149a80c0000000000005260000000040680000e9f00002cac407000010d718de10b87078000056c563c00011760000000000000000000000000000000000000000000000000000000022f5249c02a400000000000000049c00000000000111800001e8e0000eb801c01c24000066d0000000000000000c7300000000b
  | 58 => 0x59700001708e7e000000000000000000010e400008de800011380000100984d00000000000000000007efc00000000000000000000001c420000000000000000000a46800000000000eff0000059601b40000000404434f40000000000017180000000000000000000000367c082cc878402412000007aa9d7e37f2377000000001b2e10940000d4b1cb000000000077457a0000726212500003b4d0241f6b000030d4543931900000000000214b000000000001488239600000000c270c5c0ad4a070000000022f4dd400001ace000000006280000138800012ec000000000001df810ec000000000000000591c00000000000271ccfb05260000659800020a4000059b80000000000000000000000000000002e000000000000000014dd0000000000000000bf6847800000002e14000000000000000408400014d200000000cb0a2620bf800010f4000000000000000000011ba0000bd8800000000000f879f4c000000000000000000008c4e56000046c680ac0daa261337c00007148a7a0158000000000000000000000000000000000000000000000000000008e400000000000000000000000000000020260000000000000005ba517e19b20a8c6144000141d408e10848d21a4d206049d00001e6d0000000000000000000000064d8000000000006288000000000000001c3e00000000844800000005f14c6613a600000000680800000000000cdc8000378000000000000000000000000000232a8f6c2f62046000000000000000000000000000000000077c400000000000000000000000000000000002d0262a00000000234000000009511e5d0000598d1e29914437a0000c60a34d43ea00011b7800000000000000000000002c5c0168000000000007c40a57095419b0b3683a400008df4c18067e3b6a00809eb00000000672400000000000000000000002b0400000000000368e67d4c840000000000000000000000000000000000000000002f3a25c0000171402f002a0000000000000001fb86f2000000000000177800000000000000000000000000000000000000000000000000000000000000006d308d0000000007f800000000102000017c60000000000000005cac0a78ac624743b64b078000000000000000000236800000001fa32c04000051a83aa341a00000a9000000004a28c3919fe0fe00000000000000000000bcf00000f960000ed3800000004f94adb19b7000000001b7908e12685820cc917ae320a00000000000000050a000000003a1c00000000000000019d800000000000000000000000000000000007e700006ee4000000000000000f7c00000000000015f8000000045e8000000000000000000071c000082504dc800000001c5ce379bb425401e5c00007f700005a8400000000
  | 59 => 0x6740c984310000061888d1000048ec855118d164a0000cbb018d000069d82d080001c0e000000000001146186c4218f3f2214000031d80003982556481682e8000000000001098000071e0f0d80000000000000000000000000000000000000000080b000000001bdc000147900008090510873029c400011b591053dc20000000000000000000000091c0000000000020f7295600007c000001352000000007ca000072440000000000000000000000000000000000000000065904a18874004a7338366800000000000000000015a28e702091cda3cd829d4a6180000000560010b18410000000107a89001dca8bf800000f308280000000000000002208000000003aa0000000000000000000b06000000000000b871bea0000000000000002efa0d58000000000000000000000000000000000000000000000000149600000000000171d00006a803da00001ba063e00000f760e240000d0c000000005aa07fe0000000000000000000000000000000000000080cc00000002d620000292059d11a600006a28e55247e000051f80000000000000020293b7069d000000000000000000001c43bd60000a0a0000423200000000e61000066ec00009f30b706cdc0a61d6745086548000000000000000382969f00000000000000000000000000187c41de000000000003a843b9c000000000000000000063f000000008d0800000000000000000000000000000000000000000000000000006ee8ded00000000000000000002dc0000000000000000000000014d30000291000000b30000000010380000000497000000000000393400010973a8a0000c708000000000011428000198e0000000064d000000100000fe40000636c000000000000000008a04a37bc86b0a3f8000427a000000000000000095cae3000014c000008748000000060f517c80000000000000015f725885e940000000000000003481e1f437e0b7059e8000385000000000d6623184818ce6127c00006e3000000003e2e000000000000000000000000b017800000000011100000000d1b000000007eb40000000000067e400022b233be86cc0000ace00006ec007c800044dc2550def800000002b2400022e21f6c0a00334000000004c180d2925336f400000000000359a8428770994b04f6000044b8000137c0000000147c0b0a80b4738a1331ae464c4a9e000000005e5ce818000000000000000cee0000334400021040000767c000000000000000f490000000000003ff0000000000000000000000000000000e1a1a12000026780000000000092b800000007c4c000000000000000f620bab00000000000000015be26500001a47000009dc00000000000000000015bd0000000057c935400005a603f2000000006ef00000000000044b0000000000000000
  | 60 => 0x4d8080001c880000000000000000000e898000356a23b40000000000000005a80e5a073a0000a1a0b931054000000000000000000000018a50000000000020bf0d942830a3a97300b762008000000000000000000000010ca2498000000014d60000f390ce60000000000000000d1e02646f10000118a000000000000000000000000003da6876c0000000396400000000000000015ec0000000123a0000b39800000000000f0493b700000000000000000008a6482ea146072a5214e468000103267a800000002b8e00011220000368821e0000000005165e990cd80000000000000000002cb80000000000000000000d0f1e800e66000000007981052000000000003bf637b076380dd000000000001d82300a0000000217c0000000000000002858000000020f900000f6066c13ca271200000000000154c000046d000000002050000163c00000000000000021460000c198000429c00000000000000000002bb860600005c1c00020f300000000000000000000000000000000000000b3d80000000000000021c20000000000000002c80725c0001a5b00000000967800000000000000000000000000454000038e00000000000000005dfc00000000000000000014e300000000bc40000178a000000000002f8c12907a0000000006b6c0000000000000000000000050e340800015ec0000035c3ec92012538823070683e8000000000000000000068fcac50000007a215c000235b10d6000033a986531e2000c00011881644000065d0c9200000000000000041980000000010417d437785d8800023e2000000000001a68000000000002134000000000000ea23beccb78115226e00000000000000024505d78c37000000000000e5226e224d400000000000000000000003cae5118000000040a2000080a8000000000000ef800000000000000000000000000000000028f66990fe087cd190848a00000000000000000000000000000000000000000035d00f40fde00000000000126f0000000000000002a062a581a3000000003f049101692000000000000000178c00000000000303423e8000000000000000000000000000000000000040f00000000000000000000000000002466afc000000000000c600000000000000000000000000000000000b3e0000000000f0000000033d800000000000000000000000000000000000000000000014b8000000028ccf5605682e7c67a0ec3008a0000464800023280000273800000000ab8000001619f7000000000000df443dc00000000000000000006ec0000000000008ed0000107a34c04818000293a5b240000000000037a40000000000068a400018c900000000000000000000000000000000000000e18800000005db80000000114e226400000001a86000000000001fbe666107901db
  | 61 => 0x3442000018d80000c664b390ee0000341200000000000000024e400000002bb600011770000000000009589345092a00000000182424e77247580000000000000001bf3000000000000000076a00000000f75000000000000cc602ec00000000000000000008859f021240088c000000000000000000000026aa000104e000002c20000000000000000000975078a00000000000083000000000000119b0000000000008b6000000005be8a1a01700000000145c27d64640cb8956c000081680000000000000000000278000000011828ee8190087e850a80001ea2426d09f1ea400000000000000000000000000081600000000000000000000000136032922720000e259b6813320000000166240bc0000d5e9cd2000000000000000000000005e9000000001b6d097000000003e1c02a000000000000000000000002fa4000000000000000000000000008dc50528000000000000001c7d1f1412411ba8725000000000001eff0000000000000000000000000002b3000019940000000000000000000000000000000000000000000000000000000000000001613000000000000000000062740000000000000003a28e8b00000000d83800016e8000057c00000000000000000000000000000003b3000000001ef000000000000000040c000000010aa800010a43710b6b000000000b190e78000443860d44af8a4e0000000000000000000000000002c70000000000000000000594400000000000000000017b7000063d80b6a22b000000000000000391639b008a00000000000000000000000870468600000000000000010cf088e020c0000000000000009d808ba000000000000000360c0000000000039d40000000000000000000000000000000000fda8b6435c2000033495de000000011048000000000000000aa030646d086ca8000000047dc000000021ba0000000121100006db4000000000000000fc9065245ac2e3000001221cc82ca00001adf00000000000000036be16e800000000aa054a000000002d82000115b1885000036d80000000000000000000000000000002ab052d000000000000000000074f400011971c6c0000000000000001db08d6800008968a850808a14229e60fc5e480000000000000000000000000000000003a320000000000009840b147cc85c300004800000000000000000fb306dd00003eac000053600000000f159fce00000000c4100002f0c00001f2800000007cb400023a1000000000000369013c5a387f500000000000000000001c620000a9680003d2c37c000005b240008e047b9a31200004898d95000000000000000000000000000000000000000000000000000000000000000000000000fe982cd15508e4502e8c91325c5ecc0139c143e66865413d099a2bfc0cf45619bff113c878
  | 62 => 0x41e0000225260240001d660000093c76220ea0d5a4b1d1b9a0ed00000000be801f417e054d40000000000000000000000000007385ba800000000884000000046b45684000188b0000000000000000000000000000000d6a64d000000000000000000021060000000000000000000353c2c39c3b00004fa48648000000062b00000000319c78cc000000000008740000000000000000000000000001ce000000000dd8000000008b7359253240000c6400000000000224500000000000105100000000000000000000000000186d06760000000000000000000338101100000bc08668000000000000000000000041b07208000263c00009f1000000000000000000000000000089000022c06368000000039846608de5000000002004000000026b80000974851500000fb0000000038b400009d514410000000000004c9000068380001c5b01da0000000000000000000b62000000000000fa2000000000000000000000000000000000000008b400001a3c000000000000000000075d8000000000000000380077200000000000000000000000000045200007d880000000308c486000005ae0000000000000003b8a0000b5100001dfa3d288e798b2000000000000000000000000000000263e424c73a000008aa00000000000000000000000000000046ac000000000000000ee91a92000000000000000072800000000000000000000000000000000011cc06112ace6e5000021280000831c00000001f2e35ec0000000296e00008658000000009200001f3c3aca000000000000000000000014ec0d3a3f94273000000006308cd880000000000027aa0b5395c000000000000000046c00011b30000000054d000004dc000000000000000734477980001fde0000000000022cc18a80000000000000000000000000001ac16e9c570000000000000000000307000000000000000000001ab2e305e8c49d00002d0e2530fb01c0e00000000000000000000000000000022e200000000000000000000001adc0a4e3124000231e09be7c1800000000000000052180000000000094f8000000021ec0001f0700000000000000003ce2094ae8908433548d0c88c0f1e1386000000004d0000007044be081c1c66000013c8000137a000000000002c5200000001c83000069b8000000014380000000000000000000eb7043100000000000000000000000000000000000000000219400000000ea180000000000000000002040328106e8311078c59149e1000019560000e5180003be000000000000000000000001c20258200000000000000001d80000000000046d400000000a5e0000000000020de00010fc00000000000000000000000000000021d2000017ac0000000000070c835d10c13088763c000000
  | 63 => 0x35444b804678082245c0000000219a0000000000000000c340000000000000000e9429e80002ef02bb8000000000000bdc9dc80000000000031a143b000000000000000000074a400000000000000000000000000000000000000dbc000013200000000000000000003cc200000000000000000011a80000000000000001afc41f42a14000158c00006a38000160409d2399cbb80775000000000000000000000000000000000000000000000000000005c7800000000000000000030a463c000000000000000000000000000000000000000000000000000000000000000000000000000044886380ae22f5c0000000073400007e0000000000000138841f040a000080680000000000000000000000000000003370000000000017630000100000000003f6e00000000d540000085cccb8000000071b47d9113035d687444c60000302a0e0841a0000000028a011000000000000036c8000349445ec000066e34d8000000017cc000000000000000000003540000000000058800001467000000011d880002db00000379000047b26ef80001e9b22340000e3e026030c2000000012c200000000000000000000000000000028dc0000ff300003c52408cb90800047763d906229e05370a3f880001aa30000000000000001e9a11dc0000000000000000000000000035cc0001e5800000000a03800010da0000000000000002ca800012370000000000000000e02000000002d704366e84e890c9f000048d8bc200000000000000000000000000000000002eea25ac3a3000000000000000000011b043f800000002ed82de4bb3000000000000000000019b872d000000000f788768c3892ee000000001c398980000000000022b000002aec0000000000000000c4800000000000000232c0000000000000000000000000000000000000000000000000000000019a020ca00000001d260000000000018c5261600004f2000028520000000000042f06020a361ea0000000000000eb70000303865a800000000000ca700000c3a00000000000000000007f180000000000000000004606000000000000000000000000003e305c787f0000000000000f5f0000000012f40000000000000000000d9b1da480791a3000022080000000164e0000000000013bd0c9812dc00000000000000000012660fe60000000000012820000000000000000000667800014c66d140000000000088b80000a583bac000070995e4000000000000000373c2e0c00000002f540000000000000000000000046500007048a8f8e9c000001e4000123417fa524c6c287a313d20000ef399fd38263dc0000000036525b911ab8000000061f800000000000000000000001fd80000b1f000000000000f8a0a1e015431484db92bc00000b982780000079c00
  | 64 => 0xb9d0000000000000000000163e00000001328474c70d80000000000000000001aae00004cd82c9800000000000000000017ec00003c380000000000000000000000000000014e9000000000000000258a4b651f101af000000000000000000000000002293000000000000000000000000000000000000000001ee321a80000000000000000000701000007c20000000000042ca00001c6800000001878000000000006be400000000000000000000001096000054c8000000000009b10000165a0000000014a0000000000014220fa0000095a80000000000024f23c80000000057e17da412c00000000000000000000000ae405da00000000000000000000000000000002c4b7c80000000235513698d73c6437800001d9e26f20000e62222d3a280000000158835ba00005d61b4e426e45cca3e813f00008e503e4000000000000a9880000f4e6dc915511770000000000000000000000000020b127f80000000000047ba1b140001709000051848839c5f0000000000000003b14365800000003614575c7509b6e333c67e03c580000000000000000003a20000000000000000588c0000c9a000000000001744000000000000000000051e0fca000000005100f638000375c0000993000000000000000127e467e00000000000149600000000000000000000000000000000000000000000000000000000394400000000000000000000000000000000002b480001ac0000068b0000000000000001e6e00000000cc40000187400000001dd70000000000000000000000116200000000000000016da12c27a110c5800000000000000195c00000000c0e81d23d765020ab88427364e0000000000005c800000001e4000000000000000000000000000000022ba0000000000000000000000000000002cdca27933500005ca400000001c10000071d000000000000000000015660008000000021cc000000016ea32ca000100f8000000069142e780003e3a22b486c80002066202c0000000000012e4000115a000000000000d570000000000000001914000000016c5047465b400000000a34000119e8000000000000001880053c50843098000469472140000000000000010698000055c02740001f0c23b00000000000000001780f498000000000000000000000062580001aa13f8e000089b000004b413680000000000029fc0000000000000003dc8000000000000000e05215a1c54cf60136000000000001bfb1f3429a4000000000002b7000000000000000000000000000281c000206300000000c178000000016080001a230a6a7f60000000000000000c6880001ea473e000001c713e86aa40000000019c0000d020000000062110f180001b58000000000ea1492000000009421728000000003900000000000016a00000000000000
  | 65 => 0xffa800000000000d080000000000003a79e3f0000000000000000000105800003e2322200000000000477082c80000084000000004b6912500000000bf500003d820000000038b0000000000000000000000000022b1000000001c790a91a240000ba813750a9e000085a86c2254886240000dd40172000000000000722344502a098623a8000000000000000000000000000000000000016bf1a7470dc00000000a6236909470482000000000000000036e239c00023010d400000cee0000000000000000000000000000000e0e0000000065a1ff4000042c8000235f22be542c2f08000000048c91888000000000000000ca5000010bc00006002a3a000000000000a7000000000af70000000000000000000000000000000000232c1dd800000005bd00000000000000000000000469600000000000407208c0f1100000000000000000000000000000000003e4000000000000000041f0950947a19f6000000020b900000000000179342a0447c2b100003ee20000bd4000003d400009d48000000000000000748438c00000001e6010d800000000000000032740000000176c00000000000000000000000000479867540000000000000009cb8000000000000000000261c000000000000000764cda8800000000000000000000000000000073600007e00000218200008ebcd601b6b177a3efc4e59acf218077449080ad40000493c00000000000000000000002cd24f20f2f0000000000000000371000000004198000000000000000000145a000000000001cd000000000d3c11360000e178c1b00000000d2080000702219c000000000000000000000000000000000000000000000000149a1c460000000000000000000ab209eb000080740000dbc14805ae00000000418041c800000001e0e000000004993db200002d28000000076e8000014b00000000000000021da00011958000126c0000000085b000000000000e0402a800005d41bed00004dec4440000470c0000b11000000000000e3a9dce00004da000000000000000000020051e760000000000000000a7400000000000656088899891d6800003cd8875437008f4a210f4300000000c5400000000000000000000000000013900000000000000022e1000000003c4000000000000000000042fc4ed827e000031d80000000000000004a18000000010a0000090a88462e848ee90321b170000701c00016f800007a7800000001b960000000000000005c8903f000014dc73fd17f80000000356cd2e00003b8200000000000000000007fa800000002e24000099d296400000ae9d6a00003fd8e83803f000000000000e763f48000000016f0000000000000000000000000000000000000006dc1e77000000000000000402e6a20000000000000000000000000000
  | 66 => 0x11e000000002b72000078c00000000880400009a23a800000de20000356000000000000000000000000000000034ac0000000000000005a2000000000000000000000000000000000020c8000037596dc047000000000ef60000000000000000000000048382280000000000000000000000115a00000000000018a05112d068f187e385403b02455c0001460184281d40000000000053d8000000004442d200000000000000000000000000000000001e68199855f00000000000000000000000000000000000000000083d8e3480000000000000000000000000004d851303c001f0cad898700000c700001fe1125e000000000003d740000000000000000000000000000004e7c29f1d23000040c80001cca37a0000000002ce000000000710eb600000000ecc000000000000000000000000000000000002040000000000000007a3095fa1b5000000000000000000029c899f800000005bc8000000000000000000115926460000c6200001bea0000000000000000000000000038ac1a480000572000000000000d25225609bc00000000000759000000000000000000000000000000000000003f440848741956e1d0c4420000013b208a0000ea0846603d20000000000038980000000000026ae0000b5e000037525e2c3bf952c0000269800002da00000000eff9a87000000000001bd43754108c0000000000000000000000000000000000a2242240000000000000000000422000016ae000000016cd120c0000caa9541000000005488000000000000000000000000007ed000008d6000000003ad000000000000000000000002da15ef000e88140000000000000000000000000000000000000101c46a8000000000000000000000000000000000000000004aa400000000000000000000000000000000019220000000000000000000000005a8c54123626e80000000000000000000000000000000000000000000000000000325800000000000000000000000000147c294c000000000002aa40000000295e0000000186b21d46ce481a21e51aee000066280000000000000000001a381ca0000085f0000000000000001ebc00011c8000000001c08000114d000000000000000249083b00001bc500004bd8633000000007c040000000000000000001212374800000000000000000010458b130000000090793e0063a361c00000000000000000000003710000000000000000000000000003a000000000000000008cd000000004648000000001c2000000003b2000000000000bad80002be48aa4000000000000000114800000000000000000000000000980924720fc790c000000003d6000000000000000125814403f846ac85811730991000047cc000000000007ea4dbf118f195a00007d7000000000000a8621f1000000000000
  | 67 => 0x800000002e38fa311c0000000000002269002642442589d30000000007ca0000000043e001780002b20000000009e100008bcc4ff00000000000000000000000220c000000034004188000000000000000000000000000000000000000000000000000039801170fc29f2e1d646bc9080211a00006a5400014b000000000ef0957e00006cd854e1f521c3a718c00000000000000000000004410000000000000000000000000000000000104700000000000000000000000000108b00001f70000000015c1000000000001e5b2ee2000000000000000000000011280000000112680000000000000003380000000000000001d9a429452f0000000000000000000000000001d40000000085b80001d4b0000747490c80000000000000000003c0200000000000227a000000005ce0000554800000000a580000000000000000000000018b000000001d60f2900000000000000000003824000000000000000aeb00001ae200008b28000194468b8000112e41360000000196900000ebc27b0ec91564000000000000000000000000002ec80000000000c073e14a8000000000000000000000000001a5800002fc000039500000000000017640001f450000000000010c300006168eac99e516aa54d8000000000000000000000000000000000226b000000000000000000076ac000000000002bb0000110100d01850d5284d81e8c000106f83be02584dd84b520a90000000088600001a8e0000000000026e000000a69f903b9e0000bb380000000000000000002d28000000000000c1e6288000000041340000f541efa39564cc4000000000008990000000000000000a348f2b06344ab8520915000007014000000034a600000000000000000004fd18832aea02f4000000000007b000000000000000000000000000036600000a793ab00000ba00e750d5c78b8c101e6200000f4498d000000006a4c7ab1ae70000000000000000000629cec91c95152a07d4fe8800000000000b16000000002f580001a691c3800000000000000000000000000000000000000000000000000000000000000000001e4f00000000efa80000000000110180350000000000000000000000000000000000000000000000d580000fb39dbf3aa000000000000399e0b10c1a0000000000000000a0a000033a82e6000000000000675800000000000000000000000000000000011e8000000000001f4e00000000000061400006e908e631fc0000b0b80003f5800000000000050c000000005d40000000066d8bd000000000000000000000000000226c00000000000000000000000c0c0000000008bc0000000000000000000000000000000000000000000000000d4d000017bc0001be206d60001094800000000000000000000000000000000000001c2c00000000000
  | 68 => 0x726cb21a259037e8f1c641000000007e3c0000000000004bc000000000000000505800029248289056940b000000000000000000000000940870000047080000b9b000000000000000000050e000005812e827b7886892c03e8e3b8c00021d9000000000000cca34e000007550000000000000000a6a0000000046e00000000000000000000000000103d800000002a4c078000000000000853000000000000ad7183e000063ec076133e00000000000067b00003888000133000000000000138b311834d48dc846926c20000000000000000000000000000000000aaa0000000000006968000000059a8000000000000000000175e000000000000000275883c4f6e853300000000000000000000000b55000000000000000000005840000000006245d431b8000000000002d2400000000ade0000dba8000000066e06b200003bbe00000000000000000003a680000000000042c00000000000000000000000139cdc700000000000000000000000791000000000000000000000000000000016c00b627440000000000000000000000000000000000000000000000000089a25f00000000000000000005610f680000170e6d8c000000008f43c44000000007ac00000000000355400000000000000000000001f841bae6df40000792000036b40000bf8317034bd17d0db00000000000000000000000000000000b7846bcd42800000005168276000037641514917800000000000000000000003e6c0000000000031c8000185c370604942f5000019c000000ed1f36000024fc0001fdf00006c94000000000000000000000034c081100000000401a000027c17f0015a474400000000000000000000002f0400000000000000000004f900000dcc1d80c5300000772729896d8000000000000000000000000000000000351e0000f670000000000003fe00000000000021e000000005d24000000000000000000000000000000000000000000000256000023d20000000000006464a6000000000000000000000000000000000000000e6e0000000000000000000000000000000000d2a917d0000000000011b139d85cec7c68086000000000000000000000007270000000000000000000000000000000000217e2500000000014e66668000141544b000007b10000000067480000c4b38dc489000000000000000012980000000000097b98763b440000000000011481f500000000000000000000000000020108178efa0000000000000002ac00c38000000000001a445a00000000000000000d8e00002f44000000000001be00000000188c1cc400004d500008b5468f00000000599cf8d894b000000000000e25123e0000000000028263ecc0000000000000000001afe000000010cb0000000000005dc0000000000000000000000027b4631
  | 69 => 0x68bc300000000000000000000a0c000000000000000000067207866264b4c981f000069b40000000000000000000000000000000000000000000001b416ae26d400004ab894f23fa7f2846f21fd0e4418811140000000076dc000000012ce00000001e8900000000000000000000000000000000000000000143900000000000000000000000ec000000000000000000000000000064e0c1500003b00000000000001698000000000000000000000000000000000000025bc0000000020d000000000000000017400000000000000000011a99395000000000000000000000000001b5900000000000000000000000000000000004d48000000000000000faa00000000000000000001f020000000000000000000000000000004ac8000112d00000000000112000000000000000000000000000000000000000b0b00000000000095d8000447617942620bfc1c0c000000001493a0200e8ecc80fe00007bc40000000158e35840000000000000000000000000000000000000000000002a600001b800000000091500003f0c00015a200000000000000000005bb00000f5311767fc4000122b00000000000011d3d10454400000000000000000009ad0000000000000000000256c000066b2bc05d6400000001c02683000000000000000000022eb26bc4d00000000000007be40001a8900000000000000000008454000000000000000000000000000000000000000005d8800000000000000000003bd4440000000007100000000000022c90000000000020f4000000000001c210000000010980001666155c0000000000000000de8000172200000000000000000000002122000013bc000000000000000000000000006a5c0001777000000000001901000089dc00000000000000000000001f7c000000000000000000000000002af4101400004d2000000000000000344c000000000001e3800000000000000000000000000040c00009e180000000000000000003f4e00000000000000000001c005b62a1000000000862000000000000e27000000007f58000000069e8000178000000000000000000000000aa522b304cc00000000000000000000001b38000054f4000000000000000000000000004b58000000000005c702a40000420600006f580001000482c0000000000005f0000000000001a6c000000000008384000000000000000a600000000022540000000000021007fb80000000000000000000d9668d000000000000201400000000000000107d8866115c6cec328000000000000f7281900b22773000000000f2069f8c210000000000006438000000000000000000000000000000000000000000000000000000000000a0f0000000000009301ad424580000000132418400000000000015386df000000000000abda2a7210
  | 70 => 0xa0015c000000000005604a32000013be7c5400000000cda1d10a450000000000007470000271e79e000000000000000000000000000000000000000000000000000000000000000000000000000000004102024075c00019ed00008d14baa000000000000000144c000000000000000000000006c500004246115800000000000000041b0ba51d56000000000000000000000006172b4c0000000000000000000000030c0000000031315340000000000000000000000000000000000000000000000adc000106b00000000000034c8000000000000000000032e2410000067c002e0000000000000000001108000000007e64621174d14980000000000000000000000000000000000e199113000000000000000000000008e4800000000000000000000000000ad28000000000000000000000000003848000060800010980ba313f00000fe786513d4e00000000000000000006ce800000003dfc95f1169000077a8000000000008adc0000000000000011490000000000000000e03000000000000000233c00000000c413a9e0000000103e0000000000000000000000114700000000828000000000000829800002fd1d8a0000226800000008d247aa1c77434c00005431b21000000010b50c60000015800000000000000000000df900000000cd113801f440a140000000000000008d3800009442db000016fa17ce0bbcfbf000000000000000000000b80174000008500000000dd1800014560000000113800003e751a61d2f00000000d1e800007b66e98000000036e8000000017ec3e9a00000000000000030bc4420f1039be45306c20000000000000000000000000000000000479e7d540000000000000000002378000000000000824000000002bf123d0000000000000002f740000000000000000000ff4800000000000d410976000000000002307028400009a31bdc39e40000000000000004fb8000000000000000ec880000000000111200003de045bc0000cac123000009ea80000000000000000002c4e000000011a200000fdc000151c01568b444f1801d00000000000000027b849000000000014c00002280d4e310c000000023b400000ff800000000000000000000002ff60000c51800000000000000000000007e04000000000000000000000025a076c10e688f800008ec0000080817f21304000000000000fc819e0bf2000000000000000037000010170196440c322c000000036ee00000b30000000000000000000000039f80000d6e2bfe00005a7000000004e08000000000000000ad9854b118400000a823380000000097320ae33b02e2c000126900000000000000000000000e1a0000000001e00000000000000000000000000000000000000000062684c4000008fc8cdcd65800035bc000000000003c8c0000d7
  | 71 => 0x6400005c9000000000000000000000001ef0000000017e30000000008f800011b6000000001cd32d678d400012e433ce00000001607000000000000000356c00000000000000000000000c681064000000012ca326c3ea822f0000000008f8daa15a40000000000009cf00000000000117000000798cd9800000001ec00001aac000000000000000106e12f0000000000004b70000178f30d85a4000000000000000000000001af2000000000000000000000011ac00000000000000000000000000000024620000000000013ae8a7c37e8000000000000000532127c0000000000000000000d86a33124da0000000000000000000000000008be2f98000000000000000000000000000000a1f800019f842e4f130000256000000000000000063c8000000000007b5c000103500000000000043f3bb48ccc000000009b600000000442000000000001fd5000088d000021f2352251544eb00003ad24dd002700000000000000000000000000058c8000000000000000c3300000000000000000000000e25000013980000000000000003434b9b8000000000003520000000000010ea20270ab40000e6f0a1608c8000000000000000000000000002f42181cbf31685000000000002339172c000000000001cb6000000020810000000083b0000000007fc0000000093800006df800000000000000000000004614000000000005e70e52000000000000000045d00000000000000000000000afe1b48136800000000000267000000000000000000009f0851c315a2b4c000000000000000000000000000000000074e0000639843d0000000000004da8a2600000000000000000000000000000000000000fe2833f00000000000000000004eac00008f90aa2122889980000000000000022c30f2a2d4400000000000000000000000b9600000001b640f40000000000000000000013980000000000000000001812111000000000000000071780003b52000000000003c3815d0000000000000001059896c1f6014ec00000000c180000000000000000000000000000000000000000016980000000000008b43b4400016fc0000000086d827f00000000000035a111a00011c48a8b35f000000000000000000000000218370e000000004f206bc00000000000000065ccef9800000000000664000000001aa80000000382c000000000000000000037519c23c725658556010800000001056000000007c201cc8000000000000000000000062c0000000021600000000000000008af8b758cf70000140000000000f0a0000437882e00000000e00065b22ac2a405f08000000000000000779207e000098980000000182000000000000000072c80000000000000022110000000000004fe2c4c000000000000000000023e98fa35aa4fbceaa0bbf30
  | 72 => 0x4060000f9400000000000000005d80fa20000de880000000000000000002d9e7248c9a8a180000490c44710e200008e7cb2f000000000000000000039ac87e40001df700000000000000000000000000000000000000000083a38a823d45b88000000000000000000000000000000000409a1238000000000000000000000000000000000000000008ec83a183fb45126bb900980000000000033f800000000000000229c35161b58d2400000000000038d000000000000000000000002aac1ce0407000000000000ad7000000010ff1654013e00000000000459a1c74c658000000000000002011000000000000000000000010a21510000000000001b160d7a695839e8000000000007c7063902e41884000000042627a0c00008b400006854000005a00000000ea9800000000000000000015ac6238000000000000000000000007f2000000000000f64000000009c000001c8c00002540000726497e0000000000000441c0600000000000172e360a00000001ccb0000000000000000000000014783cd238a0000000011000004e040000000277400000000000000018b000000000000000000000000ba40000f088000000000000000000000000000000000000000000000000000000000000000000000000001a1f00000000c060000000087ac00000002cc000000000000000000000000000140a00000000000000000000000000298a0a9481100000000000000008b30000000000000000000000035280eb000000011450b290048000000000000000700c0001e940000000000007ad000000000000000000000000000000234c000000000000000000065c800000004ca8e281a8032343e440ba80000000000000000000000000000000000000000113b000000000000000204c00004e6c000000000008724a01000017d0428000000000000000051607ba0000815838b049b3b5a11b87ca8000000023a40f200000000000000013b10000000000004cd25660e6c0000000000000011660000000000000000b3109120000000094a13260000000000000007138b5a10d00fb00720981000027d88a74e4f98e900003aa4000000000002ab8000000000000000b059e5200003fe00000000148449e8000191324e2000000006c100000000c150000063e54585d90d7d27da227c0000917007200000000000144a074d0eb000027224b50282800039e000000000000345e000000017b9076c315800001430000000099a000000008c40b658000000085c0ae50000345a04040000000000000008780000000077280000000000075810bc8a6d0c8e435807b030f44923df0000000000003ab80000000000088cc28f000037cc0000000000000000000000115500000000000000000003c1000000000000000023b000000000000000000046fe08740
  | 73 => 0xba7126300000000db080000fdc87b48af0000000000000001c9400000000000176002ac42580002083000000000000000000000000001ea2000079e45740000000000000000000149e000000000000000799c00000003cf83ae035580000000000000000000000879907f80000f8a0000000169b3530000000016393c1a1d001a70000000000000000000000000000000000000000000000000000055a0000056c13d0000000019a72fb60000d1383e40000000078a23650000010ce0b800000008e0c000129b22128aa0000000016cc00000000000384600000000000000000000000c293a0c0000000000000000000000000033ae28ec0001a7b000000001be04a900002de886e0000240a0000a7d11d2274e0000000000000000000000175a000000010ad800000000000000000000004b68d4f8000000052700000000000000008d4981200000000ba622250000000000000000000000000019ef0000000000000000cb00000000000036b60000000000000003ffc000019c2da22274000000000000000000179200000000000000000000000000008100004a3400009220000000000000000000000000000000000000000000000000000000023a800000000000000011166fad0b3000000000ab40001fc03886214c0001cfe00000000000000000003e84000013900000000000000006be000000000000000000036911eb000000000000000000022a8bcd065700005598000000000002224000000004d00000000000018fe000083000000000000113e0000000000009c50f28000000008c080001aac0000000180100000000f65079c10ee0000f5680002ad400007518000000000000001a710000618c00019e0000000010e291444778000000000003a0a000000000000000000057011bc00000000000000000000000000015910a20000000105712c40000d819ce9030e00010a39b53297e72a40001fe40d0c000060503ef0000000000011841a7e79ec6238da600000000000000039b800000000b090000000000001bc000000007b6000040d800000000000000047ed1979b5a2b0e0000000000000000000f5c0000000000000000b3800000000a93018f00007acc00000000000000000018810000000000000000000000086f80000000345400010e3342c049c0000000000087280000000000016a800000002cfe0000d8882f4000000002270000000028dc0000000282e000000000002ed2000000000002f6800011cb800027e200000000000000000011e0208800005d48e959cb61aa4000000000000000193d181000000005c50000000000000000000000000000000000000000000948fe6000000000000000000000000000000000000000380f76000000003d24000000000004650000000031ee4af4f6d1732425a82245880c360
  | 74 => 0x25e800000001d040000000000000002822000094c987435fe00000000000233a0000b9c2009000000000000dc500000000000000035e000000a2a1a4000000007479082000000000001e6b06500000779000000000114000000000000000000057f1d840000000000000000000000097300003cc86bf0000000047180000000000021a89458000472c0000d9682ac000085c8000000022ce10c0f2e00001b9a4d6400018ed00007c4400000001a888ea41c30000000026acc6300000000187c88b0000000000000000000000036c8da805032ff21afc000000000000000000000000000000e8c03b1000000000000000000000004ec000000000000484800029b20000000000035b400000001ff92f880000fb8198100000000000000030422b9c000000000004520000113200000000000000000000000c690000000000005f200002ea66778000076a2984000100080000000000025f9a08000042351c4000000000e30000000000000000ec8200c00000c9c0000000000000000000d1f00007d6c54080003892621ca3180003eda0000000000000000000401921b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ad00000000000000000008df055c88bc0000000000000002b460000ce4091e0000000000002cc00006ba400000000000000000000002c1c37240001ce50000000000014f51ba246dcfd9000034d600009e8000000006d70000000000000000000151700007538000000000000000000000000000000000000000002180ea2161d0000000001c221228a00000000000000002e68000000000000000d8a800000000000d460bb50000023400006931cac0cc4000000032b4000000000000000000000006b319da1c180001501021e00005b1800014a43440000000000000000000223f24d629140000000000000000001f0e000000006f4000000000000db88000000000000000000000000010410000000000001e4191f000000000000000028800000000000000000000000000000000000000549298c00000000000000000000000000000000000000fa6153e0000f5900000000000000021a31ff6000021a154700000000000000000000000000132d00004d086100000000000000000f5c00000000000000000000000000159700000000141000000000000000000033586a1800000003bcc0000000097e000000000000000000000010c7a0be000000000001944000000002168000000008547af8e6500000000000111e21320280bab82df3a5c1e847ab800000000000000000009400000e08800000000000000000000000000000000000000000000000000008c24000000036640000000237b0000000000000000000000000000000000000000001d000003d30
  | 75 => 0xb1d3ca26244000000029fc00000000c071b680958808076d0000000000022901ff488e000000000c925660d530000160634f84d4000000000000000000000000000000238d00000000000000019c2000000000000e640000259192500000000000033a2e6a1ce5062875200005dd00001eb400000000ec6000000001834d630000000003e06f204d600000000ca8800000000000000000000000000000000028023af8a6380000122000000022bb000049cc0000000000000000000000000054e000005bd3dfa46c00000000000018a513415430000000107c0000000000000000000018c00000000f9c0000335000000002b0c3f9c000000001c8000000010a10bb60000db39ba20000000000000002eba000000022d72c848be0000000007ce00000000000000000010748000000000004a70f3000000000000000000000000000000000000000000000000001af0000000000000000000000000004ab0c9b800022680000000000000000000000000000000000000000000000000108207a0000000000000000000000000012b800000000000000000000000000098a0000000000017e5000000000000000000063a000000000000000000001a3000000000000d9212165560000000000000000000000000001d3000000000b3000000000000000000000000000000047fc000159b00000000000000000000000d79800000000de4000000000000000000000000000000000000035b03c3c756203207b202dcc721a31228055dcad4000000000000000000000000000000000031ca06d800019181630046016180000000000000000002fee00000000000000057cccf70f06000054f8000000045800a2400018dc00000001050993c0000000000005e600000000e3900000000142479088af46fc61e0f150000000000007210000000000000000d2e0000000000013a500000000000000000000000000000000000000000000000008f58a19a20d2b2445acba400000000177c000000019a00000000000026305578000000005a2000003d800000000000e30800000002b68000000000000000000000000000000f548000000000000000c7500000000000000000008af0000000000005eb49bc0000435e00000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000001e160b5e00000000000000000000000000431a0000000000000004bbc0000000433c0000000000047ae4d90000000000000000000000000007bd40000000000000000b28dfe000000000000000000037d80000000197a00000b41aef285400000fe0000478800006920000000000001dd0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 76 => 0xd000000005bfa16f00002bd00000000000000000001f7429d6709400014f81d3400000001c272316000000000000000000000016613d1e00000b81b193bb662d5013000000000000000170d00000000000000000000000000000000000000000027600000000000000043be2c6c0002192000059040000000000060dc0000000371a131885a0000446a56c4f0d0000000076940000000096623801890000000000009838000000031300000000000000000000000159e000000000000000000000000003cd400008b72080000000000001290291e000000000000000000000003f00000000000000000000000000009a300000000000000000000000f2480000000129400000000000000021994f200007f70000082020b075b4000000000000000d39800000000000000000000000000000000031400000ab903550eac1a880000000000049580000000000000000000000000065500000e1e04147af0c380d4600000000901800000001d740001cd800008228000000000000000000000000001d0400003780000813ce1100000bea8d8800000000000000108f8b80307232cd0af158d2e2c0000d641f2f00000000000000000000000000110d366a0000373918a00000000f2b111700000000000101400000000b3f00000000627c000201600006710a2200000000000000000002d7416881d000000000000000000000000000000000001faa13203aa8000000000000000000000034100000000000000001a28000000000007598fd000000be4be6800000000000848000000000000000000000000000000000000002ae8f6480000000586c000000000004eec000000000000000dd2893c4342175c0001e5533f65040000000000000000000000032be61584061052000000000001d9c3902000055f1e412c242e9c0000000000000000000000000000000000000002800005ac8c9900005a5c000080746784d98d7d800000000000c9483440000711000015ac00000000000000030d24e200000c570000000000000000000000000000000000000000023df3f1c0000000000000000000170a267168e000000000000000855818a8c550000000000000000000000000000002bc200000001bac0000000000003512ce00000000193a00000000e46000000000000000000020d282a000000003e90000000001e32b560000000022608c600000000000000000000000ce40000000000005b33416523000000002254632800000000000000054680000000000027f80000000000000023170000000000000000000566493287200c468da800000000000000000000000000696000000001f20000000000001fb60314000000000000000000000000000000000000000000000f5f817b1388389000022d2267410740000000000000004c792490000000
  | 77 => 0x75fc0000bce00000000000000000005794130946639ce447000014f300000000000000000000000e288000000000000000000429200000000b0e00000000000000000002c78000000000000000000000000000000000000002f2000000023b300000000000000000000000000000000000000000182d00000000000000000000000d78885502f400000000afb32600000000000000000000587800036740000ff9040400003f100000000000066ac126000030a60000580000009961eac00000001eda47a00000000000000000000d0f00000000000000000000000000000000000000e3c9aaf00000000000000000000000000000000000000000000021fa000000021f0278c00000000000000000000000000000000000000000180600001d300000000886c00022020000000085400002dd0254cc701a1735b2000000000000000000000000000000000000000000000000000000002e6c0000000213a00002a3ce450000000062240000000000000000000f12000000000000000000000000000000339a0000000000000000000806109e025200003768000000000000000000000000002fc80001fdc7928fda1ae300002798000000000000000f09146a39f60000000000036ca000027b80000000000000000da00000000767800000000000000000000000fb400000003434612ca3b00000000000077e00000000000000023ca000012ac000000000000000e4c000000000000b299db63a4200000000000000000000000000000009f002400003b08000063e000037fc00000000a10000000011da90c805aa0000ee418d0000000000001f2a01d000000000000000032786baa0aa000025c000000000000802c0001d5b00000000000000000001768000000000000000c5e20bc000020d4828163a000000009ed000022440000450800000000000000000000000000f229513000000000001e9a00000000000000000000000000000000003b1800000002b4e00000001b340000000000006f30f2200007829cf60e5c0000ed400001ed21ae0000000000000000000000000000000000000000000000000000044ca244800000002088000090600003e6481380001a9a000000000000bff000000001b7233000005860a36800000000000000142727bc5b508d01b5200000001086000000000000d158000311439000000aa300001c980000000301e00000000000442c358caca08800b6a595c7e40f63372e00000000362084c448454180000362000000000000000835c000000000000000000170f00000000d3e9eae390e0000000000000000000000000020da0000ded800000000000000213b00007ba80000d6d0000000000000000000000000000000000000000000000000000000013323f60839891e079
  | 78 => 0x40c4000021480000000571004d00002f3a0000000000000003b880000ff20000000066b019200000000132800034700000000000014b800000000e45000000000000000253c000000000000000069000000f7000000008340b050000000000000000000000000000000000367c0000000000062dc385000000000000000000000006c808729e71181a00000000000000000000000000432e0000032800000000000000107a131653e4dcb000009c80000000041a00000000000000000000000e0d80000000000000000003d0e00005e58000117000010c01e3a2cde81cc2751b04064a00006960330183e645c00000003d8c55e0000089400000000000000000006578000000000007c88ada1ce100002780000019433e45e300000000000062d80000000000058dc0000f58000000009ad8000000000000000000000080f00000a3d000000000001903000000010fa20062d9c8ab0000000000000000a7380000000000106f029a00000000000000000000000000000006401550000000000000000c16216400004609088000000001dd8302000000003c909fa000000000000a7a19ca00000000000000000004ad8000000023460000000000000005c80fa7872105241e9000000003fda000006c8000000036500001feb01fa59f059a0000465a00000000ff304ce00000af80000000000000000000000000000000000000000053e11f00000693c883000000008434366000000000000000000034a20001178925e000000010a98000000000000000000000000000000769000000000000000000089c09150000000000000000000000000006368000000000011df000001466e24f51800000000000e5500000000645835b10ac0f3c17c400023e300001e0c4c280002ef4000000000000000000000000000000000000000003cfe000000000000000000000018550000400c00022e4000027f511b0c6b0d8c0000ae18000000000003fd000000000000000000010c60000000000000000000000234e00000000000000000008c5400000000000357c00019da07080000000000000000000000218a0000592000000002e860000000000000000000000000000004a0cf95a2660000472800015fd00003e1800000000000000000000000ff20000000000000003eb00001178000019bc0000000000000000000cff00006a100000000000000000001532332c7b2000000003d1a2d1800000002b9e00008c38000000000000000000000000004a89470019a0000000000000000000000000036d82cd40000ed500008364000000001207f88000000000000000be400000000347400018d60000000000000000000000000000000000000000000000d4e0000a118a24464470980000000000000000000d9c000000000000000000000000000589000000
  | 79 => 0xa8c1f9f15b254fc7159edc327a8e68000000000001d2cf98061500000000000167613a635400000000000000005660000332869a00fd8000456a0000b3d0000000000000000000091e00000001f1642a256ec000000000000000000000000000000000094d000000000001b910000000000000000000402c0000e7a000000000000000000000000000000000000000001abe0000000052d800040e80000c8f00000000000000000002c020000000000009fa00000000000057a000019700003c1400000000d8222a80000ca80000000000000000000000075340001f12000000000001f4900000000000000000000000000000033180000000000000000000a1200000000000042c80000b9a88e8000227a0000000000000000000000000000000000000000010b1000000000000000000000000000000000080d40238000000000000000000000000000000000000000000000000000000006570000000016b50f38000448470300000000000000000000000000000000000b2e093000005c31c6b000035291ec000000000000b7f8202000000000001c8432124cb89f4000000004d10000162a00000000000023b000000000001c0200000000000000000000000000053425e40000000000019525738fd000001890000000000000000470400015730c4a3bdcf931bf409ca160c000051b00000000000000000004ca400000000000000000000000000000000000002bbe000000000003e00000000000000000000000000000000000029c800000000000dbc8e6e3c0e4a540000000443e00000000000000000000000363087200000000c5800000000a2e8000000000008ad800000000000000000000001d78000000000000000000000006c033380000000000012bc000000000000dd400000000000000000000000000000000000003da2000000000003662000000000000000224c00018a92978618074b000000000000000231600007f584d89d52200e36cc00000000000000000023850000000000017eb000000000000000000000002ca229700000000000135f2a9a26406ac8b921b10000106091140000216800017e8000000000000000000000000000000000000000000000051c5a7114a000044ba000000000000000334c35f00000000000000000001e660000000000000007dfc000000037aa000000000002896000000009f1000000000000000000000007ac800000000000f168000000000000001311000000000000000000063340290e7f376a2ee8000000000000e8400000001d280000000212a18800000000000024a2000000000002e100000e3600000000000041c80000000000000000000000513420c00004322000009c0000000051dcc8e000000000000fe400000a52000088a90da0000000000019071cba819400000
  | 80 => 0xa19000005f8fce80000000000000000000000000000000001a0e000000000000000863000000002a3242b842600002c6400001bf000019025969114882b1648000000000000e7c0000000000037d07ce4000000000000000d8000000000895c00010ce00000000ec7208600000000c0a00004726000000000000000024c00000000000000000000000eca0000000000000000000000131c00000000be59a5a317600001ac879f00000000e580000000000000000000000008c892a9b1e427000000000000000000000000000000000000000f2f00000000000000000000000e8d8000000051240000ead00000000a92859b00000924000000000000000000000000007f0800000001ad00000000000038706d0c00015b00000000000000003ffe0000e1ea0fe00005dac3d480003e94000000000002a1429dc000000000000000000000000000000f3a80000000000000005e30000000000008f6000000000001384000034ecfe18da5208600009de00001e02028509300000000000000020ce0000000000000000000521d0a6229a00001590000110200000000cf1000000006f8400007df25da00000000000000000000000000000000000000000000000001df8000000000009a81d0a000000000000000000000000000000001600000000b160000000000000000000000000000000faa0000cb500000000483800014de1e26000000000002e9e0000000000036fe06850f480000000000000000000ab26b90000000000003ddc000000000000000b6600000000000000009950000000049d8575252600000000000000005e00000000000000000000000420e00000001fde4386856857100000f760c2c0000000000000010280000000000000000000000048e009d00320000000000000001d740000bd794a900004bc000016ac00000000c31000000000000cd7800020960000afb03fd000061388be000024dc000000018df000000000000000000000001d39fb8154200000000000270a00006fc0e781af00000000000000000000000000000000000000000000003e78000122200000000000000000000000000000000000000dee800000005f580001dc000fa0000000000000000000000000000000000588800000000000000000000000000000000016427c7821f000000003b6c2fd0000254a00000000000000000000000000000023480000d8600000000000000000000000000000000000000000000000000000014127d00000000000000030f489405328a5600001cb00000fbd0000000093a8000000000000000c0b00000000b3a8000154800000000000000000000001c6a3d4a093860b800000000000000000026780000000223d353a0000cb60000000000000000e4800000000f27035b06fe1728000000000000000000000000000
  | 81 => 0xd300000000000000000000d5c243c000000017f529c000002100000000000000000000000000000000000395a0000000000000000000000000000007af4c9400003ff600000000000000000000000000000011b4000000034f2275473b800041c40000000140f000013b40000000000000008b18bf725c406543de8aca299877bc578000010c200000000000000000005ab000000000000000205900000000000000028a422140001bfd000000004fb00000000000000000000000000000000003ede328c000000000000568000000007dc00005b400003efa00000000000209870b4000000030b0000000000002fd20000000000000000000000000025740000000162b00000000f4e000040d2000000010f2000000000000000000000000000000000000000000cd246b200000001dd903da3a88b088000000000000000000349200000000000000000000000000000078c4c2280000000000000002b9247c000000017f200000000000000024100000000075908a800000000000000000000000000000081840000000146200000001cbd000000000000000187e102421581ec00000000c9980000000000000000000000000109f800000007578000000000002b54000000000007ce00000000000000004948000000071cc00000000000354476a07b70000000021d107d0000000038980000000376c0000bde0000000000014d1000000000001bec151000000000000000000000001d7500003c5800016d9385c7494000122530ce81f08050000061a000000022e9000000000001fd223c00714000000000000000000000005a60000a1e89c80ba200000000fe900000000000000000005e345a5000000000000000000000000000000000000006f5c0000000000000000000000000079a4000000000003918000000000ac8504000000000004c20000098400000000987800000000000000000000000000b250000000000010f0000000000000000000000000a4000000002c961e0000016960000000053d8000000000000001c42000000004a383532efc0000b32913b184a0000000239d336830b8d200c2b108a00000000000264a30110640000199249480001214000000007a5a03b000055b40000000119800000000000000000000000000000000000000000000071980000000000014fc224928000002d04000000000000000a598000101e000000000000000000060a10a70000000000000003c7a00003bd000000000000000000000000000000010630d400000000000000000003a4a2552a448e00824905935cc8e3c000000026423304bf6a0cd00004bf40000520294a286c000237900006c2c38c082c37dc1e24000000000000000f5b800000000000fb4016e00000000000169a2a08000000000000000000000000000b1400000001
  | 82 => 0x4cb05bd83423ec22fb91ed1cfa3ff4138d1a0800000000000a7e8a840000017c000000000000000f558000152e3720c8d80001dd400011bb8baa00000000000000000000000000195900007a840000000000000006c7938300008c9c000000000006adc000000000000000000202c000078bc0000000000000000000000000000000540000000029b00000000391000005f10000000008205f580001f7800000000281202e00000000000000000004bf8000112c00000000000000014ac000000000005a4ca5c02ea0c60000000013d1000020180000000000000002ae800018b40000000000038a4000000008f2217c61a07b70acb2ab800004ed80000000000000000002d1400000000000000000000000000000000000001e1800000864000000000002660275a0bb06f649908211684213e00008270000000000000000000000018f8000088600007b6cff3800034647d7c9f50c2424ba1f10ccc9b762118000000000000000000000000001d2a00006dba3bd3c4200010fb04de2b3800002ce0799332621c4000000000000000112800000000000000000000003d04c9f0000069e000000000002cb65f50b9e8000000040640000000005c4b4400014fb20e237e8142084d0000213877780000282000087d000013480000000000040d40000dac00000000000000000000000000000000000000000000000000000000000000000000000000000000000651800000000da06c740000000000000000000000000000006001be015d429d81c4979f19702ce4411000000000000fcb800000000000000000034225b8ca6a01f600002f94000000000007ff474880000000209c0000d1846165fb8387a354000000000000000000045c800000000bfa00006d4000000000000b9f8000000000000001bf6000040781ae00000000564c0000000000008a8000000012a000000000000000008f11e6924b0000000000000000b1e00000000000000000000000000000000004d7800013660000000000000000000000000038520000db980002c5a3d8075e96ef1fb2000000000004428385512400000000000000000000000000000000002ac200000000000000072680000000000000011079b6f00000000000000000003d3800012f900001f3800000002c4823c40e4897222360000000000000006eac000000002b03cd40000000000009f51d2800000006320000000029c87f2d02b800000000000000000000003ea0000227100000000000000000005bdc1cf0000000032988f600002ab60000a7b800000003c0c000000000000000000000000000000eaf8000000000000000000099c00000000000000000000000000000000000001fa8000060a00000000000000000001666000015d80000a6100000000eea86630000
  | 83 => 0x59300001bcb000000000000000000000000001d4900000000000000000000000000000040be000000000000000000000000000000129c0000000000000007810fc9264400000000000378400000000000000077f40000c5d2f780f00f4a9d3600000000b861f4010820000000000000008ca800000000000000000000000000000000000001b9e0000000155300001d84000000000000000000000000000000ed000001c54000116c80003ff80000000217b1e2a000026980000466000000000cf00002800cf21f560e3200007a10eb900000000000228f17020000000094814600000000000000000000000000045e00000f0200003b1672584ce129626f48c94000070412180000a66952b0a460f50000000000006e2c0a99f6a00007abc0000000000000005aa000000007520fd880002afa00000000000369400000000000097400000000492297a0000fc380000000000115c80000000000000000003cca08240000000000000000b20000000000005ae800000000000000000000004d300000000000021747970000000000010ea896600000000000206b00000000000175c2c680000000057c048c661d04200000c5a3c38000000020765d581be8c18263a00000001ab90000000000000003cfc09c00000000000071908a309680000000062680000000780c85b80004194000000012591bb200480000f2a425e34c4000000000000000000000000000a8d123800000000000b128000000000000000000000000000000000000000000001a391c8e1ea8000000031d600000000000243a8a8818b9085057456c800000000000077015f0000000074900000eff00000000000000000000000000000000000000c1c000012220b009ec9153439c56dc010926700001cd0000000000000000000041300000000000227b441600002cf8000000000000000f82000036c51990de60fac000000017c9000000000000000000000000000000000000000000000000046580001b3f000000000e599cb00000000000000000000000a1b9652000000000000000000003fc00002b000000000f798000000071880001c7f00005840c239795000045610f1041100003ac400000000000000000000000000000000010e020580000000000018fa0000000203a00340000000000000000000000000020563b4000000951412000000000000d020000ba38000000004783600000000000000000c1600000000000016726fc0000000000040b000000000000000000003ff80003dc83bd40001b4909dc6690cb921dd00001788000000000000000af7157900002f1c5bb800000000000000000000004870000000000008b74786000010fa0000cc80000000000000078000000000000001dc331e8000075e000000000000000017f00000000000000000002cfc84e
  | 84 => 0x4264449c000000034c20000000007042d8190c000000013a080100001f27474e0000bcb0000239c0000cc78000000000000000000000000000000401000000000000000000000000000000000000007858000000000008440000000000000000000000000000001ee23ae800011c11b7c402400000000ec80000277498280000000511c0000000000000001281b9800004290b9a000000003dec1db88c300002b1400000000000000000001350f7c2ab40000000000000000000cbe000000000000000000000000000000000060890c991dd00000001143800000000000000000000004694000000000007b9c00000000000000000000000000000000000001820000027c96fe000017cc00016500cac41509ae80000000000079c000041c80000000000000004f9c0000000254e0e880000000000070401f4800000000000000000000000000000000000000000986000031800000a5c80001d104c58000000000001128d861fea2ffc0000000000007948a20000000000002e840001be300000000000000000004a20000000000007894000000000003704000230a1e7824f4a0280003ccc04240000000000000000000fed000000006a40acd000000011e9800000004b18000016900006704000222c31ba04f108e800017a600006901cf51cd233001650000000000000001d1c0000515c00005170000041516700002a800000874224f3976000000000000c8c00000000000000000000001be40000783c000125f0000009800000000000000000012eb00000000000000000008b8c0000000233e00ec4e103c50000000000000000000000000000001baa6c8c53f13df2bc60000b8b95510fec642c00000000000000000000001cbe1b8c000000000000000d0100000000000114a80093ae6000000000000ae000000000812302224b8000000000000000000000000000000000000000000000000000000000d90000000000000000ad480000000000108e145e0000000000021aa000010291f2a1ef0000000000000000000000000000004758000000000e900001dac6c00000347c00000000000000000011af00000000000000000000000350800000000000374c000000000008e1c000043d0000000079b1282000000000000b9d1604637842380000000000000016b217900000d66000023ae37b4000000036280000000022c00000000ff800003bc800002398000000055200000000000000000000000000043b0000220c42b882d8c9697f108b00000000000000001c300000000000000000000753000037180000000000000000398000000000000000000000000000000000000000000000000000000004710977000000000000000000000005dd80000000000000008c100000000000000020b65530cf80000000
  | 85 => 0xa62000000000000de780000176000000020a30000703c000000000006684dce16a92f7e000000000003ea66364000000000000000000138d06d84b844aa8000000000000000000000000000000000000031a800000000000000000002a23b0a8094000000000000000fed800000000000000000045c00000000000031740000000000014d00000c9c000000000000000000040de1ba0000000024420000248883118b8000000002a10000000000000000000000000015f43f5400000000000000000000000000434000005de0c952fbe5b9800000000000000000000000c385c9c4b28000000000000000d05000000000001ab800002e703720000000000006f08673000044f00001509000081f4000064400000f7c0000000000080e1011800000000000000000000003064dcf80000a50000022c80001824000000000000d9c00000000000143e00000000000000026e0000000000000000000000000006120000000000000000000000000000000000139a000000000000000000000005cba23e34500000000000000000000000000000d239c800000002cbe00000000e10039e0000000229b00000000000000000008e2c4c18000000000000000f1d0000000097880000000000000001630000000000000000000000000000000000000041c0a0211f83de80000000000000006c88000000048d400012b70000000000000000fe20000afd8000000000000000d6c30fa475400022540000000000000003e423ed4bea800035944ffcfbc0e0b2a48000013a000013f8000000000000000000000000000000091c000000035ec0000000000034ca23a8cfa0f091ed400008148000000000006eb202a2b1200000001c1c295c0000ec3902800007d08000000016780000000000000000000000000000000000ec4000000004fe80000000000000000000000082a000039380000000000110f0000269400000000f1a06f411d08419ac225f00c640000c96189e124cc9f90942d86000000002aa0000000000000000b085f800000000436400000000000000000010b180002c5e00000000000304c000000023230000000000014a2471c00000000000000000000000000000000000000000000000000000000061011c8574800028a684f0000000000000000000000000002d0c93000000afa0000000000000000000000000000000000000000028140000000000000000000ed780000000000000000003bba000093d9b860c6e000000013f8206e7a040000a32000000008bf0000000000000000000000000004c00000439070e8000000000000000000000000000000000000000007f5d1ea800000000000ae680000000000000000003f5c6dc00000000000075f00000000000072f09a58000054c25d100e00000000000000000000000000000
  | 86 => 0x198536985f702cf0ab439a03dd000000000000000000001d800000000e41000000000000000000000000000662000036d200000000000000000000000000442e000009880000000000000000000000000000000002e0c0000000000000008b6c00000002afe000000003eb00006638000000000001dcc00000001d9800005101e200000000000000000000000000000000000464cda5800000005eecc27854d13dc0000000000000007c14000048800000000000000000002a0000021b91f3e000000000000d100000000000000007da49a98ccb143200010d580000000000074c12231ff20000d21845300004d8c50423a02da400000000000000000000000000000000003d2800000000000000000000000000000000036c000011571c74198600011cd800000003574000050d0000434c00000000000000000000001494000000014ed0000000071c800000001b6800023553a980000000000000000000000167100002bb4926a14500006e68000000020ea0000d2e800000004cdc0000000000000000000000000032c800021a7000000000000000000000000001962000000008a5908100000000afd00000000000074086b7000087107f300000000576492c00a40000000000006fe000042e10258000000085000000000000060008a280000000000000000000000000000000002c9200000000000000000000000000000000000000000099886d800003d5296218141268000000000000278000000000000000000000000003c7197f1dd2000000000000000000000000000000520800017a9000021a4000000000005d2c000000000000000000000025c651a0000000000005c6c5ad14ca0000000091380000000145117684d13b2a0000000000000000000a7321861c2200000001df600003970ddb963500000000502195d3b721d5112b09ef000000000000000000028a400021cc3e1400002bd0000259a0000c1b00000000000000000000000000000000002502000000000002b0a00000000000000000000000000000000011f38000444c00000001c0922945cc400000000000000000006032d843df4de61b8f000000000000000000000000000000000000006c58000000000010858000000012000000000000000000000000000000200000000000021500000000000000000000000000000009fd80000000000000000003f7c30b4d2c80000000000000008f700008124000000000000000000000000003f740000aaa00001e4d02991fa20ee0000000000040420000000000000000000000000023220000000000000000000000087e00000000f0f0000000000000000000000000000001b2200000000000000000000000000000000008c4ce7a0695000000000360000000000000000000000000010fb858e25f63edc000000000
  | 87 => 0x2a500000000391e6d78000148b0000000000010410000000000000001f8400000fd00002c327d2c000000000000000fb20000222000007b380000000000020593a00fc20000000221800001eb85c20000000000000001ac40000000000017ff32f000000001ed5000012ec00020da000000000000000000000003ab8cef21c24170000000000008c700000b6b11b20000a8f23cb000000000000000000000000000000000000000000000000000001de0000000006210c382fa00000000aa100000000000000021bb12b200000000000000000000000cb6000000000000000000000000000a6f4006000000000000656000000000000000000000000001b3c00000000e7b250e0cd4ae409a03da81f6cd0e1b1b31680000000000000000000000000036f000004478000162a000000000000000000000000000000000000000000000415885b000030be0000000000000000000c8a800039120000000000000005358beb954532986b445611d71389a8f8070617e2000000000001e541fa48e900000000000079e85ed0000000000000000efe0000000000006d70000758cef4800000000000000000000000000000069a0000000000000ef000000000001f8d00006fc0f9d800006a86880000037745060000000000006860d2800018ab2aca00000000000444412d80000000000000000000000000047e50499cc700000000dfc13cb0af26e40674800026b40000000000040e43940e94000000000000e4e0000000000000000000000000000000000000038b40000b07000000000d98000000060705c51f35173e0000b82800000003ed003f98bd027a00000000d9a00000000459000000000000000000000000000000197500002c200000000301c0000f37800000000000000000009700000fc4800004d60d1c0000000000000002929b2f00000000000000028d60000eca04ad000045e400000000df240d80000000000000000000e6f11f600007ea03b4009200008351aba12ea13a0000000020fe000070a0000000000000000fce000000000000f08433200000000f3400006ad099c87ef0f6c0fcc0000000000000000000000000007b80000a66000087fc00004702f70735c3a1000010d04524000000000000000d8c0f2c136400001fa0370222445885fa97dd083c000000000e3191e13840001576200400000000000248c68cc108839626fa000000009bc3f220000e95000000005f60b4e8e9300000000000000034ce6360e9f800000000000cc20000117c3dbc78d8c3e19b200004630000000000002b0839200005b400000000275c00001e8015c000000000000000000000011a20000000036a80000000089e000081e800000000000000000000000000000093200000000000000000004fc00000000320800008fa8000000000000
  | 88 => 0x57d0000000037a88db0c06000000003ca00000000251800000000000000000000001e4a00000000000000000005da000000000000a1f0000000000000000000000000000000d17000000007c18000000000000000000000000000000963000016ac000065e270c402400000000000836c00000001be60000000000000000000000000000002b600000462000000000000000000000000000000000000000000000000000011579ba7000008dc000000000000000000000000000000000155600000000a2c80002958712064180001118000009984350000371c00000002a2860180000000000000000000000000000000000000000000000000000000000000000000000000000000ed6420a00010038000000000000000000000064740001bd9000053bc000000000005e6c00000000000000004700000000000034c1e340000000000000002cd837c515c1cba00006ba800000003c10000000000000000485c863000000008bc83e31a7800000000000000000000001121900600007634000000000000000000000017324c9000006e90dc40bc40000c2a000000000000000000000000000000000000000000000307600000000000000000000000000000000000000aeb352c3ce4a77168800000000000000000000000b0493c9000075c8000000014a000000000f200000000000000000000000000015bf000000000001e590000000000000000000000117b1a9b0000000000013ad249800004c100001c308f400000000000000000000000000041b86dc96fb0000000000000003a0449880000c69000074dc0000000000082789e08000090c47d05db86480000000000000003d980000000000000000000000000000000000000000000000000000000000000e3838700000000000104791863f100000a4b80000000000000000511f947e0ce9d8ab83b062d34e8600000b5000000000000000000000001bc70000343800015c900000000000185900000000e29800000007f180000000000000006ff871e00000000000119800008490a530000192e00001cb80001b020000455800000000000778000024720000000000041682de00000000000000000000a4733ac339c1ae8000000000002c613a135860000eaa80003bd8272400000000000000000000000000000000000003c7000000000121000082340000000000000000000000000000004e9000000000000000055b0000000000010c42bf20000000176811c20000ba8800044c60000000000000006ee0000000000000000000022b000000000000c0f000000000000707000000002b313c500001f4c0000d4900000000000046100007c9000000000a1e0000a0b00000ca6765c78000003b4885b400014b60000000000000003e9c0000000006a3d9600000eb00000
  | 89 => 0xe90000000007c8c000066000000000000000035d000001a808f000001088000000031d407e4e18012e0a0e5df000000003dd000009df800034d400000000000000000005918000000000000002162000000006fb9cbe32802da400000000000000000016e100aa55c0000000000000000000000000007718000183127700c00922000000000000000000000006c400001802000086a516c10bd20740f80c3980ee00000000000000000006b4cd70000034ee05bc70b058d0000000117e9b56000000000000000000060ac9c60000000031380000000203000000001be9254c00007480000000047a800011ae00000000000194f000000000000000000035ac0000ae300003b8107011ef0000000000000003ec600000000000000000009541454190c000000000000000000000000000000265cb8001980000000000000002dae348c000000008900000000000016c200000000000459e00004d60000000000000001fd90000000077a1cd40ee84b7c00000000000845c000000000000000cce8fbb12de00002db80000000000000000000000000061e00003eb053606498af600000000000127f000000003bd8000237600000cc800000000000000136c00000000aec000012a40000000131400000000000000012fa00000000000259200005b6849d00004274a6b8000000031780000000000000000001e48000050b4000000000000000e9c800000003d6800000000000000000000000000698800000000000000000020b7000082140000000000000008778c79340200000000000000000000000000000000000000000000000000001b95119a0000f140530363400011ea00001fc24ccc0001b2e399203c4000000044e82cc90c8000000000000000000000000000000000000000000000000000000000ebd80011a260000b9e000000000000ae000003bc000000000fa314a8608c12f029305ac0000000053700002f64000074a000000000000000000003087eb9baf08860000a189d62132c8700000000045940000000000000008d3c00000001c50000000018e300000000240800000000000000000000003aa0000000040800000b5ca2dc3c167dd4000025d00000000a39800000005fd803a8b6000000000000000006ec000046b0000060c00000000a392a6e567c00018b3000000000001cee00000b202508f92043e0000000023931100000000000047142d7c000000009a80000000000000008904079113500000000914800007820000000000000000000000000000002b6cbd90000000000008bf8000227c0000134800000000b48551178e00000730d6800002f9c7b35105000000000300000000027b600000000f6600000000596000000000000000000000000000
  | 90 => 0xebb00000000ad50000000000000000000000009d40000ddd0a5c0000e8b8d3300008b20bf7978900000f70000099e0d7630880000000000000000000000000000000c206a11d360000000168c1c9e0000fb61152368c884d0da0000000000002460000000000000000000472400000001b09081c0778000000000000000c219443091a00000000000000000000000000000000000000000211600000c6102400000000af4998000007dc80000000000000000000000102600000001ac50bfe86c400000003a2c0000000124100007d44d7d000000000000000000000000001055800000003fc0000000024580cccb9400000000000000000000000000006c046700000000e230000000000000000000242c000000018b9000043f000000000000000080d00000000000000000000000000000000000000000071d84c51536000000000001bca0000000000000003b780000000000000004bd8000363e0000000000035760000000000000000000000000000007bbc00014a832fa00000000000026427fc0002275000071d8060800000000000000154e0000000000000003bd00000000000000000000000000000000000000000000006f480001e2400000000000000000000000000008b000000010052227054e0000f0c8000000000000000000228284d80000000000077e80000000438e5dec4760000000024906bb12e80000471d1a10000000025707968000000068d404e065f00000000000000038bc0000c5700000000000000000000000000059006cf33160430ca985a72fe6377c0000000000000000000000000000004250000000000000000000000000000000000269267ace6c95633f2600000001957000000006a000001b4e00000001d0d261200000000000083811ec0000000000068880000b7000000480000000000000000000000000000000b5d89ea0000000000000000000639c00000cc124e0000000191041aa08787721dbb000000008510eca000000011a4000000000000000000000006ab40000000000000011118000000051600000000000000000000000000040f119d800021e6000000000000000125c179237a286a7c7000000000000000000000000a8e00010bd00000000000000000000000000077302c122d0000000015bc00001018f70199b069234200000000000000000000000000000000000000082e00000000000000000000001804000000000000c393e52000000000000000000039d800000004b9c0000bfb0000831067a00000000658c000000006e40000000000000005c4c000021a43bc318800000000000000000000000000606c0000ea500000000000000000000000000000047cc7c2c93b8d391b46000000000001a4e0000e208000000000002418000000024ac0000d3833a800000002111
  | 91 => 0x3550830c7619e06000039ac00021ae000046643fd800000000000000000000007c94000000000005a08c8600000000268442e10d800005f0c0000ea700000000000000000000000000000000000000000000002aa000094900000efa385c0000b0b000000000001b6a00000000b738881000000000000763000000000000000000000004f3a0b0000000011f2000000003cf4000000007308a04df900001cc679f4000000000002a482a513be00007488823000000000000000000000000000000000000000000cbe034b00000000000000000000000000000000004004000010b00000000464800036260000f7b1a242e1600000000000000000000000000000000008358000000000000000000000080bc000000000000000000000016c4000012c80002c1a000000000000a32861400000001f9a0000000000000001410e52800009b20000000012d00000000a04800041740000000000000004b4c00015ba000000000000eb51c9200000000000000037bc00000000000000000000000000000000000000000000000023290bd257c489d00001562000000000000bac00000000000261a0000000000000005b4c0000000000000000000ca442ea000000000000000000000018ee000000000000000167400000000000000046680001426000063bd01e800000000f484908000000000000000000000000007520000000000004d2800000003f300000000417000000000000000000003b7000000008e8c000000000000000000000000000000000000000005524000000000000000b5210050000000000000000000000000013b300008da000019fc00003dc8000070d00000000c49134f00000001014000016ce0000000000000000000000000000000000d670000000065e8000000000000000000159e0000000000000000000000000000000000000000000000000496c00000000000000000005ac0cce000000000000000000000006830000000000013a800002fd000000000000000000014cb06900000c05800000000000000219d000000000001233366000009f180000ab0000009b8000000000000000bdd00000000e64032f000000000000000000044bc0000000000053a000000000000000000000003aae0000000000016f811e4000000000004bfc00009ca000000000000fa00000000000000000000450d06780000000109096b9eee1f5e00001450000000000000000000000000000000a0e000088f000000000000000000011802f7c0000000000000000000487800000002c68ace9b3311620000000209700000000000224b27ba0000e53a3950a2400000001f5e00000000000000000000000000000000000000000000000000000000000042fa8c180000631000008d40000000302e12d034f80000000000
  | 92 => 0x451a05ccd840000000029200000f8400000000000000000000000000000000000000a5f09ec000024cc000000007ec0000000000000000000a8680003ab4000000000ae22d800002420000000000000000119000000008268000000000000000000000046c841d80000000000000000003a1000000000d210000000000000003e3200010a68000000018d4c1d0000107c00000000000000000000000000000000000000000000000000000000000000000d40000000000000001507000000011878000000063e51b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000023ac0000000000000000000000000000000000000000000003110000189011fc00000000daf0000318400019d900000e20000000009e86a70000000000005f9001b0000000033f51e71f7a0000312800019d30000000060d00000000448c0000d41219400000000fd100000000d0a0000294e00006c9914e00000000000110f0000189000018662fc20000000085600000000000000018a6000011b0ce20000520c0638000000000000000000164e0000000000029688c380001787240e00000000000000084840000000000000009a180000000000000000003bbc00000001ad200000000000000000000000000000000000fd40000b7e00000000000000000008a58dc996280000000095c8ba4453c57147cb1941168a000092d00cb00000000000000000006e0400000002c3400000000000218e000000000000000000000000000000000000014a30000000000016440000000030712af000000001368000273a0000c63863a00000000e6a800000000000000000000007f74000000000000000000000020f00000f118b04000000003531ad60a860000000000008c000000001fd40000000000000000000000000000000000000000000002c002b2057a8000000000006e71fb600000000000077c21745e9c0001dd81b1a0000cc319a30000874d0f98000000000000000000000000000000000000078dcc2e9a0f00007dd841f8000000000000000000000000000002347000026b804388f322d48f04000000026ac00008250000000000000000000000000000000000296a1c0c0000cfa313675bc00000000000612436880000000000000000000c8a56bc4048000000000000000000477e00000000000000000000000000000018600001d1a0000553c000238c0b4600000001505037c7b0c7450000401e0000fa80d6500000000e9c0000000000004510000000000000001e970000000000000000000000000000000000000000000000000370c00007622b5a0000a1000000bd0562c00000000000000037a800000000000d25872f0000000018185102ac40000000000000008f24000000
  | 93 => 0x7400000000000000000000000000000000000000000000000000000e160000000000000000000379a000000012721f120000b18800046421a000002326000000000000000000015e00000e800000000000000000000503000000000726000000012e532d0000000016792f283cf8000165547bc55681ed0fc500000a5800000000000000000019ad203a8ed8bde888a0000000000000000000000000000000000000000000002eda00000000000000000000000aff00002f04000003000000000000000019f04b749ce00000000806800000000000000017f0e000000000000009082f601938000000000001cd4a449aa400000000000000000000000000000023a00000000000000000000000000000000000000000013ca0000b0e003e28380000000000011fe2ec0e618000000000000000000000000000000000000000011b4800000000000000000000000000fbc8000000052500000000000000004fc80000000000012189250000671c0001131377a00cc66b8bed00005eac000168d33e6000000023a20000000000000000000000000014a111d6000000000000000000100c8a74000000000000000370800000001d6c000025580bb97900960000000000000000000030c80000000000000002f801c222e486121350000633c000000000007cdc000000000000000000053a00006078dd000001bfa5934a89144a31e629680000ba20000000000000000000000000008a637b0000065400000a82449069300003294000000017460344850cdc50c3042d600000eca1d7000000008ef8000461a0000b581bbf0000635003a1b1232420000000000003e0000000003c2000000000b59e000000000000000000aaa000000000000000003817385f800005c686c8000038f6000000000000000000000022460000000000000000000000000018a400000b80000000020c600000000000000000000000000028e35881d720a700440000000000000000000fd301aa0000000033e8000000000004bc800000006d5c0001d0f0b901d405ea80002a4e00000000000169e0000d92000000000000000000000000000000000007560258000000000000000000000000000000f0100000000197003897fc00004d34000000000007684000000016ec0000000000000140001033094500004dc80001f9e00000000a4f80000000000000000000bec297cdce80002f820000f6b0000435a0000000151540ce00001d80000215e6c380000000000000000002319394280dc00019d00fda72e078680001c78128c00000003488000000000000000418400000000d90000037707fd1ce636d47ec1cc6092800005cf000026a22190000234022c200000000000000000000000000000054ec000000000628154a2b1c1e15805138000000000005fe817483d3000000
  | 94 => 0x6ecc000000000000000000000038d063f40001d3c00000000000000000000000000000003e6000082000000000238c00000001d080000000000000000000000000036c4000000001a700000000000000000000000000000012dc00000000000000000000000000000000000000b140000000000000000000000057f02a800000000000157400000000000000030266eec7258a2e2f6c8c3000022ab04be000000006fb0b2000000000000000000008e200001c5850c0020000000000000000000000000b3c00000000000000000007da00005ca80001dc200000000d291cb31204806ca1b000000000000bef0000000000000000a270cc48148000068b00008c20000000000000328000082d0000000000000000000041c8ff00000000000000011c834be019c000000006687f806760000000000000000000441c0bb8000000000005c4097a8e6d32760000000000001b8000000020f00000000000005d300000000000000000000000000205b08d8648c033000021ec5384d729cb742ec681cefa10c52cc84218dd680001fd0000000015d3000000001c2800000000000000000000000000000149b000000000001d330000000106a000000002294ab4800000000000000000000000000000000000001c900001a2500000000e2c800000000000000000005a8824800010250000000000000000000000000016af000000000001432145e4d80c0b0c90321a00000000103284a0000ae580000000000000000000000000056e9d09000000000000000000000000001991067c00000000451231c7e701ff8eed07922cbc1710000000000000000403000000000002374000000008b21c4000000000000177900007fd8000000000008ab40000000081e000028100000000000000000000000000106100000000658000015e203720000000000000006ec400000000000012c18393d2000057a80001afd00000000000006300000000b6f11bf00003c7cfdd8000000000004e68000000000001ab800018f400000002109000000000000000000000000000000000000000000000000088846911ac72062000000016a6000000000000000000000000000000034c67fcd5880000000810800000000000000000000002e022a28000000000000000000000000000490fbba0eb00000000000000000000bcc0000000000069bc00000001d2e0000000025b2bb8000000000000000000051d0000000000000001db300005a18000000000008c80a568c7000001ddc00000000000000009580000dc28a300000000000000000000d5a0000000000001ca00000000f31800000005b200001fc9000000009ff08c844340bd80000000000062a85e500000000000000000000000000000007c20898000000001
  | 95 => 0x2f446bb036a00003ac20134000000000003664000081f000000011179785003275ac000000039d6000000000000000000000011b8000000008ed882f0000000000000000000025000000002e460000000000000008a94000161e00005bcc00022a614ba5c7cb3406b42ec250f0192216903f00000000000015e60a6c00000000000000000018030000000000000002de22c700000000000000004cf80003f560000b358000000000000000000000000000000000000000000000000000065dce93972c00004ed40000a2a15e40000000000000000000b40076803768bb0000000040d027dcc138000000047c917400000000000000013d7000000008170c7639fa1770fcb090d00004da40000000000047f0000000000000000000000018263b2c000000000000000000000000000000c12000000000000c3700000000122c0000caa0000000000000003a220000000000000006150bd200000000000000000000000000000000000b88000000000004628000022280003c1800000000000000000000000000353c1474000000006420000000000000000000000000010f800000000000000000000000f0a000000000001cdb0000000000000370000627000000004480116c2b297d9000076b81061ce8000000000000000443a000000000000000507c000187b000001800000000000000000000000000072740000000000000001c18c50000000000000000000085dc00000003284000026003ea00008450e4000000000000000020cb17980000adc000000000000c69800000000000000000000008cd8414000026de000000000000000000062c850100000000000000000000000e2c000000008a1800000001f724c9c6bd000000000000000209938ca4fd41a000c3000000000001a2c00004508000000013c40000f3b000000000000000000000000000000000000000000000000000003234c498b0c000085480001fa11db000000000000000000001500000000000000000000000000000000000000006b800014710000000000000000000000000012d200001ac800016ca00000001036902a44b477100001c7e000086701828e7911a043d4c468000343655bc000000000000000000000006a412d422b8181000033c00538000000005a80000436000000000000000000000000000000000000000000000000065d000013c40000000000019cf03e400000f29bf739f285a000010d200000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x863664984520431ab24c2290219598e6114810caac7308a40863964980520432cb1cc0290211d9c665d08108bce632e840845d73197420422f398cb21021175cc65908108ece232c840853671d52420428eb98a9210214b5c85490810a58e8a94840847671995420423d384caa10210fdd165508108bce632a840845d73195420421f3b4a8a1021179cc65108108bae6328840847671194420423d380ca210210f5db5410810a6ce3aa0840843d76150420428eb98a8210214b5c8541081087ce9b2e640843d74d97320421f3a0cb990210f5d065cc8108ece232e640847a70197320430eb24a7990218759153cc81087ce832c640843d74196320423b388cb190214b1d1528c81087ee8b2a640843c74595320421f3a0ca990210f5d0654c8108ece232a640852c74549320423abaec2990211d5d4614c8108f2ea302640866952181320421f3a0ca190210f5d0650c8108ece2328640847a701943204237396cb208211b5cb6590410c72a9304820847b75582310431a324a2988210f9d3650c41087ae9b28620846e72d943104236b96ca188211e5c1650c410c3ac9298620861d6454c310432729ac4188219354d620c410cb2a7300620843e74d96210421eba6cb108219a54a6088410c68c928a420853671d53400428eb98a9a00214b5c854d00108eae2b2c800863654986400431aaa4c3200214d9c75450010a74e1aa2800843e76151400428eb98a8a00214b5c85450010c5ea8312800862c54189400422f398ca20021175cc65100108dce4328800846d72194400421fbb2a8200211ddd5611001087ce9b2c600843d74d96300423bbaac3180210f9d3650c01087ae9b28600846e72d943004236b96ca180211d5c5650c01087ce8328600843d741943004237390ca180211b5c8650c010c3ac9298600861d6454c300432729ac4180219354d620c010caaa7308600843f74597200421e3a2cb900210f9d3658801087ae9b2c400852c7454a200423bbaac3100210f9d3650801087ae9b28400845e73d94200422eb9eca100211d5c5650801087ce8328400843d74194200422f398ca10021175cc6508010c5ac9290400864d6394820042963a2a4100218b5915208010c9ac6a90400866552984200423abb0a988021555cc54c4010acae42a6200847576d4f100423abb6a5880214d1d152c40108eaed28c200863664946100431cb2cc9080218e59564840108f2eda9c200847976946100423b3b0a888021555cc5444010acae42a2200847676d4d100423b3b6a4880214d1d15244010a6ce928220085717590110043982a28088021781c94044010ea2a718220085717508110042d8ba04088021745cc2044010ec2a4102200847a76d4d10042d8ba6c2880211e9da5144010ae6eaa0a2008751538c510042d9ba262880215c5d72144010
  | 1 => 0x3144358326c098a21acd90604c5109e4e1324428847675d8e214425b3a4c110a218b1935248510c58c8292428863465d91214423b3acc890a212d9d264485109e4e1322428863465191214423a3aac690a212d1d163485109e0e0b1a42886a464d49214423b3b0a490a21a91905248510d48c91924288564754c921443523226490a21ac1936048510d66c830242886b06418121442793a8c090a219c9d460485109e2e6302428845f73595404422e39acaa02211bdc965501108d8e4b2a808862f5418940443162a0c4a0221a91884150110b50e4a00808854d7214f304425a3a2c3982219514d61cc110b64e9b0c60885727518630442793b683182215c1d5318c110b60e898c6088750534c630442783b243182216c1d1218c110ba6e690c608843f74595304421e3a2ca982211bdc9654c1108d8e4b2a608854d7214d304423d3b0a698221725c8534c110ab0ea99260884f276d05304433832e82982219c194414c110ba2e620a6088670658c530442b83aa62982219c195314c110b60e898a60884f07648530442d83a24298221f04c9214c110968e8b0e408843f74595204421e3a2ca9022117dcd65481108b8e6b2a408862c64d492044316320a4902216a1d12008110d92c690040886d1638c710442d83a263882216c1d121c411096ce9b1c20884b674d8a1044359326a108221ac9923084110da2c718420886b2644c21044237394c72a0211b5ca63950108dee4b02a80846c72581540421fbb2a82a021875516315010c5aa8b10a80861e6458c540432731cc42a0219358e6215010c5cc8b10a80864e635885404326b1ac42a0219558e6115010ccac5308a808659639805404334b14c02a0210fdd162d4c10878e8b16a60843e74983530421eba4c1a98211d1c56494c1087ee8b0aa60843c74585530422fbb2a629821875915314c10c9aa6b10a60861d6498c5304317324c4298218b5926214c10c5cc8b10a60862d64588530432731ac4298218d9926114c10c6ac9308a608666629845304332b14c2298218e9926014c10c72c9300a60866a629805304334b14c0298211d9c665d0c108dce432e860846d721974304237396cb218211b5cb6590c108dce432c860846d72196430423b388cb218211e9c06590c10c9ca6b14860864d5358a430423b38ccaa18211ddc56550c108dce432a860846d72195430423aba8c2a18218d9506150c10c6aa830a8608656531854304278b80c2a18211b9c86510c108dae4328860847671194430423d380ca218210f9d260d481087ae9306a40843e7498e520421eba4c7290218b5c8645481087ee8b0aa40843c74585520421fba2c0a90210f1d160548108deeca90a40862d645485204326b1aa429021879926314810c3ac9318a40861e6458c520430eb22c6290218b5926214810c9ac7310a4
  | 2 => 0xcb21a211b5cb6590d108dce432c868846d721964344317aa4c521a218b1526290d108e8eab0c8688478755824344237b92caa1a211b1c96550d108eee2b2a868847471195434421f3b4a8a1a210f1d95450d10a38e6aa2868852c72551434423b3aec2a1a213c9c36150d10c6ca830a8688635541854344237b92ca21a211b1c96510d1087ce8328868846e721944344236b90ca21a210f5db5410d108e8eab08868865453584434423c3aac021a219614d6010d1087ce931ca48843d7498e524421fba2c3292210f1d16194910c3ec9b1aa48861c64d8d524430fb20c6a9221871906354910c9ae431aa48862c64d89524432631ec4a92219518f6154910cb0c7b02a48846f7654852442963a2a429221531cd521491087ce8300a48843d74180524422f398c029221175cc60149108bce7b2e848845d73d97424422f39ecb21221175cf65909108e8eab0c84884f070586424422fb9acaa1221171cd65509108ecebb0a848847a75d81424422fb9aca21221171cd65109108bce6328848845d73194424423a3aac2212218d1516110910cc8a4b088488478755804244334292c0212210f9d365cc91087ae9b2e648843e74197324421eba0cb992218b99352cc910c5cc8296648847475587324423c3aac1992210f9d3658c91087ae9b2c648854d7214e32442963a2a519221531cd528c9108e8eab0c64884f070586324421fba2ca992210f1d1654c9108eee2b2a648847b7059532442373b4a4992211b1d9524c910a58e8a92648854c73549324421fba2ca192210f1d1650c91087ce8328648843d741943244237390ca192211b5db520c9108e8eab0864884b474584324432a29ac2192211e1d5600c910aa8e6aa682884757694f414429aba0a7a0a21c514f43d0510a68eaa1e82884f27598341443393acc1a0a213c5ce60d0510a38e6aa4828852c72552414421f3b0a8a0a210fdd95410510a38e6aa0828852c7255041442d8b84a820a211ddd95410510aa8e6aa082884b77655041442ca39aa820a21691c95410510b66e0aa082884757614c414432ab18a620a212d5da4310510b4ce521882885b17090c414438a2988620a216c5c043105109e0e0b108288535751084144352b108420a216c5c0421051087ce932c628843d74996314425b3a4cb18a213c9c2648c510968e8b1462884f07058a314425b3a4c118a215c9d4608c510c38c9a9a628861c6414d314431a32ec898a211d9d6644c51096ce932262884f270991314431a328c898a21559d7634c510d28c9a9a62886346494d31442ab39ca698a211d9d8534c510c68c829a62886946414d31442ab3b0a698a21959d8534c510e2ce829a62887157414d314438bb20a698a2195990534c510ca8c829a62887146414d314430a320a698a21d19c8534c510e8ae429a62887517014d
  | 3 => 0xca5410a10c74a8b00850843e74d97328421eba6cb994210f9d265cca1087ae932e650843e74197328421eba0cb994210f5d664cca1087eeab26650843f76953328421ebb4a9994210fdd954cca1087aecaa6650843e74996328421eba4cb194210f9d0658ca1087ae832c650843e74995328421eba4ca994210f9d0654ca1087ae832a650863654d85328431b2a0c2994210f9d2650ca1087ae9328650843e74194328421eba0ca194218e552600ca10c72a8b00650863a54583418431caa6c0a0c210f5d7644c61087aea322630843e76951318421e3b2a898c210f5da540c61087eecaa0630862e549883184316aa4c418c218b951620c610c5aa8b106308715544c4318431d2a2c018c218e551600c61087aebb22430843d75191218421f3b4a890c210f1d95448610c6ca930c810863554986408431b2a2c3204218b9536250210c5aa9b12810862e541894084316aa0c4a04218d9526110210c6ca8b0881085a872500408431b2a4c3184218d951618c210c72cb2a4610863965552308423d3b0a6984210f5d6640c21087eeab20610843d76950308421fbb2a8184218b952620c210c5aa9310610862e545883084316aa2c4184219394d620c210c9aa6b10610863654984308431aaa4c2184218d951610c210c6aa8b08610865553584308431b2a4c3104218d951618821087ced2a2410843c76551208421ebacc8104210fdd5640821087aed2a0410843f76550208430f2a4c610421875526308210c3ca8b18410861d5458c2084326b1ca4104219358d5208210c6ca9308410863554984208431b2a2c2104218d5516108210ccaa4b0841085a8744802084394aa24010421b258d2008210c6acb2a6210863565553108429b3a6a7884214d9d352c4210c72cb2a62108639655531084237394c72a2211b5ca6395110c3ec831aa88864f63d89544432631ec4aa2218bd906255110c9ec6312a88864c63189544432a31ec2aa2210fdd95415110a38e6aa0a88852c725505444237b92c9a9a211b1c964d4d1087ee8b16a68843c7458b534421fba2c329a210f1d16194d10a68e8b0ca68861c64d8d5344317b26c4a9a218b1936254d10c5ec8312a68862c641895344327b18c4a9a218d1936154d10cc8c5b0aa68866862d81534422fbb2a629a21471d15314d10a98e4a98a68861c73590534431bb8ac829a218d1c56414d10c5cc9310a68862d649885344317322c429a218b5916214d10c6cc8b08a688635645845344333312c229a21995896114d1087ce8308a68843d741845344237390c229a211b5c86114d10c74c8b00a688639645805344335312c029a219a5896014d10ce2c2b00a68843e74180534421eba0c029a211b9c86014d108dae4300a68846e72d974344236b96cba1a21471cd54d0d10a58e4aa6868851d7414f4344237396
  | 4 => 0x68e2b20a78862e6498853c4316b24c429e218b9916214f10c5ac8b10a78863a6458053c431cb22c029e219a9896014f10cd2c4b00a7886726158053c4237394cba1e211b5ca65d0f108dce5b2c878846d72d9643c4237390cb21e211b5c86590f108dce532a878846d7299543c431b2a0c2a1e218d5506150f108dce4328878846d7219443c431d322c1a96219c98560d4b10a5ce9a94a58843e7498e52c421eba4c7296214b9d36254b108deeca90a58845e73d9642c422eb9ecb216218d5526190b108bce6328858845d7319442c421f3a6cb996210f5d365ccb1087ce832e658843d7419732c421f3a6cb196210f5d3658cb1087ce932c658843d7499632c421f3a4ca996210f5d2654cb10a98e6a9265884f17118132c421f3a0ca196210f5d0650cb10968e8b0865884757694f41c429aba0a7a0e218e95160107108eeecaa083886556314c41c425abb48620e21699ca4310710a6aea21083886a56210841c425a3a2c518e212d9d2608c710c6eca32263886346494d31c423b3b0a698e218d190534c710cb2a6b0063884b67498221c425a3a2c690e213c1c163487108ecec29243886a4648c921c43523226490e219a9496008710c5ca8312818862d5418940c435231082a06212d1d161cc310caaa630a61884b47458720c4316324a4906218b19152483108dce531ca90846d7298e5484297394c72a4214b5ca6395210a6ee2b1ca90853a7018e5484316b10c52a4214e9c06295210a3ce6304a90851d731825484297390c12a4214b5c86095210a5ce531aa90852d7298d548429d384c6aa4214ddc56355210a70e0b12a90862d62189548428fb9ac2aa421471cd6155210a5ee4b0aa90852c72585548421fbb2a82a4219c5866015210c6cc8b0ea70843e74d89538421eba6c4a9c210f5da5414e1087eecaa0a70845f7654c53843172a4c429c218b5526214e10c5ca8b10a70862d545885384326a9ac429c218b9926214e10c5ac9310a70862e645885384316b22c429c219398d6214e10c6cc8b08a708635645845384333312c229c21995896114e10ce2c3300a70846e72d964384236b96cb21c211b9c86590e108dae432c870862e5498a4384316aa4c521c218b9516290e10c5aa8b14870863954582438431b2a6c2a1c218d9506150e10c6aa830a870846e721944384236b90ca21c218e9516010e10c6cc8b0ea50867161983528421f3a4c7294210f5d26394a1087aed2a0a50843f76550528430f2a4c629421875526314a10c3ca8b18a50861d5458c5284237bb2a4294219358d5214a10c3cc9318a50861d6498c528430f322c629421875916314a10c9ac7310a50863664584528431ab22c2294219598d6114a10caac6b08a50845e73196428422eb98cb214214b1c95450a10c72a9b02850845e73194428422eb98ca214214b5
  | 5 => 0x4ae76d094008317b2e84a0041c354f4250020ccec528a8010664629454008333b12a2a00419918951500208bce7328801045d73994400822f398ca20041175cc6510020c9aa7310801062e545884008326a9ac4200414b5d44210020e1aa62108010666625444008332b12a2200419354e628c0208deeab1460104ac7458a3008326a9ac5180410f9d3650c02087ae9b28601043e74994300821eba4ca180410f9d0650c02087ae8328601043d75990300821fbaac8180410fdda540c02087aed2a0601043f76550300821ebb2a81804187992530c020c3ac9298601061e6454c300830eb22a6180418b952620c020c5aa9310601064d5398830083172a2c4180418b551620c020c9ca6b10601064d53588300823abacc2180418d952610c020c6aa9308601065653984300832aa9cc2180411ddd5610c020c6ca8b08601063554584300832b29ac2180419554d610c0208eaed288601063664944300831ab24a2180419998a510c020ccac5288601047776544300831b322a2180418d591510c020cccc4a8860106656254430083872a2a790041c355153c8020c9cc8a9e401064c6454f20083a2a9ca390041c955151c8020e8aa6a8e401046d7694a200838caa2a7100411e5da5288020e62a8a8c401075153546200821f3b4a8900410f1da544802087cecaa2401043c76551200830fb24a690041871925348020c3ec8a9a401061c6454d200831bb24a2900418d1925148020c6ec8a8a4010634645452008317ba6ca900418b1d36548020c5ecbb22401046d7599120082573a4c8900418bd946448020d52e032240104ac769512008317b2ca8900412b1d95448020c5ecaaa2401046e76d4d2008316326a690041535d65348020c9ecb29a401068c6494d2008316322a69004193d955348020d18c8a9a401070e5454d2008386aa2a690041c3d915348020c9cc8a9a401064c6454d2008386322a690041831915348020e90e0a9a4010667659452008352324a290041d154e5148020ccecaa8a40106a4645452008392aa2a290041d154d5148020c9aa7b02401062c6494120083543248090041d254e4048020bc2e320240104e87650120083a4a9a8090041aa1933048020e92a79824010569750c120082d4ba06090041aa1903048020bc2e2182401063b74d95200831c3a6ca900418ed976448020c76ca322401063b65951200831db2aa89004196d965348020cb6caa9a40107195454d2008354326c490041d254e52480209d4ed212401056975cc920082d4ba664900419cd965148020ce6caa8a40107315454520083a8a9aa2900416add12148020cd4c4b06a98852e72d5254c4237394c72a6211b5ca6395310a5ce5b22a98843f7655054c433930ac02a6211b9cb6454f108dae5b22a78843e74d8953c421eba6c4a9e2117dd95314f10c
  | 6 => 0x10829b3a040a88414d5d02054420aace6102a21055573081510821ebb4a8288410fdd95414420c3ca9318a21061d5498c510830f2a2c6288418755163144208baed298a21061e6494c510830eb24a62884117dd95314420c3cc8a98a21061d6454c510831b2a4c2288418d5526114420caca7308a21065553984510823bbb2a2288418d9915114420c6ac8a88a21065663544510832ab1aa228841179ce65d04208bae732e821045e73996410822eb9ccb208418b5526290420c9aa7314821062d5458a4108326a9ac5208414b5d44290420e1aa621482105a97010a4108332b14a3208418e5526090420cb2a730482106a842982410831caa2c1208419654d6090420ce4a2b04821045e73195410822eb98caa08418b5536250420c9aa7b12821064d531894108274b80c4a084199d8951504208bce7328821045d739944108296ba884208418b5944210420e1aa621082105a970108410821f3a4cb988410f5d265cc42087ce932c621043d74996310821fba2ca988410f1d1654c42087ce832a621043d74195310821ebaec8988410f5d4644c42087ced2a2621043c76951310821f3b2a8988410f1d9544c420c3ec929a621061c6494d310830fb22a69884187191534c420c9aa7b12621064d53189310831bb24a2988418d192514c420c6ec8a8a6210634645453108333b12a2988419654f604c420ce2a3b02621043e74d94310821eba6ca188410f9d2650c42087ae9328621043d75990310821fbaac8188410fdda540c42087aed2a0621043f76550310821ebb2a81884187992530c420c3ac9298621061e6454c310830eb22a6188418b952620c420c5aa9310621064d5398831083172a2c4188418b551620c420c9ca6b10621064d53588310831b324a2188418d592510c420cccc5288621066562944310831b322a2188418d591510c420cccc4a88621066562544310831d2a4c0188418e552600c420cb2a7300621067151980310831d2a2c0188418e551600c420cb4a6b00621065953580310833928ac0188419c545600c420ce2a2b06421043e76951210821e3b4a8908410f9d95448420878ecaa2421061f6494d210830e324a69084187d915348420c38c8a9a421063764945210831a324a2908418e5526008420cb2a7300421063954580210832ca9ac0108419c9456008420c5acba16801070d53d0b4008326a9cc5200418b5516290020c9aa6b14801052d7510a4008386a9885200416a5c042900208eaeb30c801063654986400831aaa4c3200419594e6190020caaa730c80106a442986400823bbaac3200418d9516190020c6aa8b0c801065653586400832aa9ac3200411d5da51900208eeeca8c801062e54d894008316aa6c4a00419394f6250020c9aa7b12801062e541894008316aa0c4a00419394c6250020c9aa6312801
  | 7 => 0x2a18419594c6150c20caaa630a861063954d81430832ca9ec0a18411e5d46050c208ece33288610475719944308237390ca218411d9c46510c208eae2328861047a70194430821f3a4c7290410f5d26394820a9ae7aa6841062d659534208296ba6a7a1041c355253d0820c9acaa9e841070e5454f4208386aa2a7a10419354d60d0820c72a8b04841062d655084208386a9a84210419654e6010820c74a8b008410659535804208354a12c0210418b5966410820a9ae7aa0841046f765504208317322a8210411b5db5310820a9aeb298841070e5454c4208386aa2a621041c39d15310820e1ae8a98841064e6454c4208387322a6210418b5974310820e1aa7a18841062d6550c4208386a9a8621041691c54310820b50e0a188410749539804208237baac0210419354d6010820e92a6b0084104eb755804208335baac021041aa9516010820d52a8b00841066b53580420836529ac0210419a54d6010820d92a6b008410649535804208355a1ac021041aa50d601082087eed2a6641043d76953320821fbb2a9990410f5d954cc820c3cc929e641061d6494f320830f322a7990418759153cc820cb2a6b04641063954980320831caa2c0190419694d600c820c3ca931ea21061d5498f510830f2a2c7a88418755163d4420c3cc929ea21061d6494f510830f322a7a88418759153d4420a6ce9a8ca21053574d4651082ab39ea328841555cf519442087ee8b1ca21043c7458e51082ab39ea928841555cf5494420e48e4aa4a2105567315251082aab98a9288414d9d35394420a6ae9a9ca2107165494e510838aaa4a728841c59515394420e2aa8a9ca2105367414e510829aba0a728841c95534294420e8aa7a14a2107455310a51082f0b808528841599cb6494420ae4e1b24a2105377458e510829a3a2c7288414d9d06394420a6ae831ca2105667218e51082b9380c728841599ca4394420acae521ca2104777650e510823a3b287288414d9d33294420a6ae9994a21053674982510829aba4c1288410f9d0635442087ae831aa21047676d5151082ab39ea8a8841555cf5454420e48e4aa2a2104767615151082ab398a8a8841555cc54544208eceda9aa21053674d4d510829aba6a6a8841c59525354420e2aa929aa2107165454d510838aaa2a6a88411d9d85354420a6ce829aa2105357414d51082b2bae84a8841c95534254420e8aa7a12a2107255410951083a2a9884a8841785c04254420ac8e4b22a2105377458d510829a3a2c6a8841591c96354420ae0e0b1aa2105367418d510829aba0c6a8841599c86354420ae4e031aa2105667290d51082b2b9486a88411ddd943544208e8eca1aa2107254210951082b938084a88415c5c04254420a6ce9992a21053574cc951082b938064a88415c5c03254420a6ce9302a210535749815
  | 8 => 0x76455020a5ce531aa81052c7258d540829bb8ac6aa0414d1c56355020a70e0b1aa81062f631895408316b18c4aa0414b9ca6155020c58c530aa81053a709855408296392c2aa0418b1886155020c58c5302a81053671981540829ab8cc0aa0418b188605502087eecaa0a81061d5498c540830eaa2c62a0418d5526115020c6aa8b08a81061e6498c540830f322c62a0419358e6215020c6cc9308a81065663984540832ab1cc22a0418d9916115020cacc6b08a810655635845408333312c22a0419658e6015020ce2c3300a81063654987530831aaa4c3a98418d95161d4c20c6aa8b0ea61062c72593530831b324c3a98418d59261d4c20c6cc8b0ea61063564587530828f3a6a729841475d35394c20aace3a9ca61055571d4e530823bb8ac9298411d1c56494c2087ee8b0ca61043c7458653082ab38ea929841555c75494c20e18e4aa4a6105567115253082aab88a929841539cb6494c20aaee2b24a61055471592530828fba2c329841471d16194c20a3ce830ca61051d7418653082a7390c329841569c06194c20a3ce8304a61051d7418253082ab388c129841555c46094c20a3ce9b1aa61051d74d8d53082ab38ec6a9841555c76354c2087ce9b12a61043d74d89530821f3a0c2a98410f5d06154c208bcedaa2a61055671d5153082aab8ea8a9841c31ca5454c20e18e4aa2a61045e7615153082ab388a8a9841555c45454c20a9ce5b22a61054c7259153082abb8ac8a9841551c56454c20ab0e0b22a61051f74585530828e3a2c2a9841531c96154c20ab0e0b0aa61051e74185530828eba0c2a9841539c86154c20ab4e030aa61051e74181530828eba0c0a9841559c46054c20aaae2302a61051e74081530828eba040a98410f5da5414c2087eecaa0a61061e5498c530830eaa4c62984117dd95314c20c3cc8a98a61061d6454c530831b2a4c2298418d5526114c20caaa7308a61063654584530831aaa2c2298419554d6114c20c3cc9318a61061d6498c5308317324c4298418b5926214c20c6cc9308a61063564984530832b31cc2298419998a6114c20c6cc8b08a61063564584530832b31ac229841999896114c20c72c9300a61067161980530823b38ccba18411d5c665d0c208ece232e861047571197430823b38ccb218411d5c66590c208dae4b2c861046e72196430823b388cb218411d5c46590c208daeb314861062e5498a4308316aa4c5218419354e6290c209d2e1314861062e5458a4308316aa2c5218419394d6290c20c9aa6b14861047671995430823ab8ccaa18411ddc56550c208e8e2b2a861047671195430823ab88caa18418b5536250c20c9aa7b12861046d751894308326a98c4a18411d5d76150c20c6ca9b0a861063554d85430832b29ec2a18419554f6150c208eaea30a861063654185430831aaa0c
  | 9 => 0x8a830a869047671194434823ab88ca21a418b1526210d208d8eab10869062c54588434831c2a4c021a411e1d56010d20c70a9306849063b54181424821f3acc9992410f1d564cc92087eedaa6649043d76d53324821fbb0a9992410f5d854cc920c5cca2a4649052e7494e32483162a4c1192418e153604c920c70a8302649046e7695132482973a4a899241539ce544c920e18a9b1a649070c54d4d32482973a4a6992411b9d8534c920e1ea829a649072854d8132483162a0c099241ca150604c9209d4ea302649066a7518132483553a0c099241aa5d0604c920d56a8302649066a5418132483342a0c099241aa150604c920c50a830264906e2711813248370b88c0992418b152620c920e1ea8990649043e7498f514821eba4c7a8a410f9db545452087cec2a2a29061f54d8d514830e2a6c6a8a4187d506354520c38a831aa2904777654451482aa39aa228a410fdd16314520878e8b18a29053671d51414822f398ca20a41175cc6510520a6ae22a0829062c5498841483162a2c420a418e1526010520c70a8b00829043f74597314821e3a2cb98a418b15262cc520c58a8b1662904e87058b314821fba2cb18a410f1d1658c52087ce9b2a629043d74d95314821f3a4ca98a410f5d2654c52087cebb22629043e75191314821f3b6a898a410f1db544c52087cec2a2629043c76151314821fba2ca18a410f1d1650c52087ce8328629043d74194314821f3acc818a410f1d5640c52087eedaa0629043d76d50314821fbb0a818a410f5d8540c520c5ea9310629062c549883148317aa2c418a418b151620c520c9ea6b10629066562d44314831daa4c018a418e152600c520c76a8b00629063854580314832da9ac018a419cd45600c520ce0a2b00629063854982214831c2a2c110a410f9d7644852087cea322429043e76d51214821f3b0a890a418b15262d0120c58a8b16809063754986404831a2a4c3202418dd516190120c68a8b0c809062c54d894048317aa0c4a02418b1506250120c58a9316609062c5458b30482a63aa6598241c315132cc120b90e0996609043e74d95304821eba6ca982410fdd1654c120878e8b2a609062c54d8930483162a0c498241531d5324c120e18a8992609043f76d50304821ebb6a8182410fdd8540c12087aec2a0609062f5498830483162a4c4182418bd51620c120c58a8b10609063754984304831a2a4c2182418dd51610c120c68a8b08609062c54d8e20483162a2c7102419358e62d5020cacc730ea81065563987540832b31ac3aa0419558d61d5020a3ce7aa4a81051d73d52540829b38ea92a0414d5c754950208dce531ca8104777158e540823a38ac72a0414b9ca6395020a6ee2b1ca8105347158e540829b38cc12a0414d5c66095020a3ce7b22a81051d73d91540829b38ec8aa0414d5c
  | 10 => 0x54e7395132c82e4b86a6996414b9d2534cb208dcec29a65904ce7614d32c822fbb2a619641b24c9600cb20c58c9192a39062c644c951c832631a64a8e411ddd95114720c76a930483905357115041c83162a2c420e410f9d365cc72087ae9b2e639043f7459631c821e3a2cb18e410fdd1654c720878e8b2a639043e74d9431c821eba6ca18e418dd526190320c68a930c819043e7695140c83172a0c4a06418b550625032087aedaa0819067161983548829b38ea92a4414d9c7645522087eecaa0a9106696298054882963a2c5a9c419a58a60d4e208eee2b24a71047471592538821fba2c329c410f1d16194e208beeca98a71062e645885388316b22c429c418d9926114e20c6ac9308a71066562984538831b322c229c418d5916114e20ccac4b08a71067161980538823b38ccba1c411d5c665d0e208ece232c871047571196438823b38ccaa1c411d5c66550e208eee2b2a871047471595438831b2a0c2a1c418d5506150e208ece2328871047571194438829b38ea9214410f9da5450a2087aedaa0851053671d504288236bb6a8214412b5db5410a20b4ce3aa085105aa70d5042882d5380a821441691c54310a20a6ce9a8ca31043e7418d518821eba0c6a8c411ddd951146208bee6b2a831045c7359541883173288420c41aa10a601062087ce932c631043d74996318821fba2ca98c410f1d1654c620c68c928a63106346454531882aa39aa298c410f9d3650c62087ae9b28631063464945218831a322a290c414d9c754d0220c6ca930c8110635549864088352214c3204414d9c7545022087cec2a2811062c5418940882573b684a04410fdd95410220958e8b14611045e7614d308822fbb2a6184419394d620c220c9aa6b1061104ac74597208829b38ec7aa2414d5c763d5120a5ae431ea89053671d8b544829ab8ec5aa2418dd8661d512087eecaa0a8904777158c544823a38ac62a2414b5ca6315120a6ee2b18a8905347158c5448296b90c62a2414d9c46315120a6ae2318a8905397018c544828f398c22a241475cc6115120a5ae4308a89063561184544829cb80c22a2411bdc964d4d2087ce930ea69043d749875348317322c529a410f9db5454d2087cec2a2a69063754d85534831a2a6c2a9a418dd506154d20c68a830aa69062c64d89534831bb26c2a9a418d1936154d20c6ec830aa69063464185534832bb18c2a9a4199d886154d20c70c9b02a69067061d81534822fbb2a629a41551c55314d2087ee8b08a69043c74584534823b38ecba1a411d5c765d0d208dae5b2c869046e721964348317aa4c521a418b1526290d208d8eab14869062c5458a4348274382c521a411d9c66550d208eae332a869046f72595434823bb8acaa1a411d1c56550d208f6e0b2a869063754d85434831a2a6c2a1a418dd506150d20c6
  | 11 => 0xc317b24a4988618b192524c430c5ec8a92621862c64549310c31bb24a2988618d192514c43087aeb320621843f75590310c21ebb4a8188610fdd9540c4308daeb310621862e54988310c316aa4c4188611bdd5620c430c5ca8b10621862d54588310c236bb4a4188618b992520c430c5ac9290621846f76548310c317322a4188618b591520c430c6cc9288621863564944310c333314a2188619958a510c430c6cc8a88621863564544310c333312a21886199589510c430b28e89886218715544c4310c3a2a9262188618e952600c430c72a9300621866a52980310c334a94c0188619c546600c430c74a8b00621863954580310c335292c0188619a549600c430ce4a2b00621843e74997210c21eba4cb908610f9d2658843087ae932c421843f74595210c21e3a2ca908610f9d0654843087ae832a421843d75d91210c21eba8c8908610f9da5448430878ed2a2421843e76551210c21e3b2a8908618bd925248430c58c9292421862f64549210c316322a49086193d8d5248430c98c6a92421863764945210c31a324a2908618dd915148430c68c8a8a421865763545210c334a96c0908619c5476048430ce2a2302421843e74994210c21eba4ca10861875516390030c9cc6a94801864d6354a400c23abacc3200618d9526190030c6aa930c801866652986400c332a94c3200611ddd56190030c6ca8b0c801863554586400c333292c3200619954961900308eaed28c801847776546400c3172a6c4a00618b5536250030c5ca8312801862d54189400c2373b4a4a00611b1da52500308dceca92801846c76549400c333b14a2a00619918a5150030ccec4a8a801866462545400c30f2a2c6200619398d5210030c9ac6a90801865663544400c32ab1aa220061c395152cc030e1aa8a96601874552947300c38aaa2a398061d154951cc0308baed29c60184797694e300c394aa2a518061cc951518c030e62a8a8c601876252546300c3b0a92a31806187d96544c030c3ecaaa2601864f65949300c327b2aa498061c3951524c030e1aa8a92601865765945300c3a2a94a29806195d95514c030e2aa8a8a601874552545300c3a4a948098061d2549404c030c76cb2a2601863b65551300c335b2ca4980619ad95524c030e52a8a92601874a53549300c339b2ca2980619cd95514c030e64a8a8a601873154545300c3b1292a298061d8549514c030ea6c6a8a601875243545300c3a8a1aa2980610fdd95415320cd4c4b00a99066a6258353c8317324c529e418b5926294f208beeca98a79043f7458453c821e3a2c229e411d9c66550f208eae332a87904777159543c823a38acaa1e41479cf5450f20c6ea830a87906345418543c823b388ca21e411d5c46510f2087cec2a2859043f7655042c82973a4a719641179d8534cb20a5ce9b2a6590
  | 12 => 0xa9061591c54354830ad4e021aa4185697010d520c297ba2c2a90614b1d16154830a98e6b0aa41856870585520c2973a0c0a90614b5d06054830acce2302a41856571181520c2973a060a90614b5d0305483087aed2a0a41843f76550520c3172a4c4290618b55262148308deeca90a41862e64548520c316b22a4290618d9526114830c6aa9308a41866552984520c31b2a2c2290618d5516114830ccaa4b08a41847671997420c23ab8ccba10611d9c665908308eae332c841847671195420c23ab88caa10618e5536050830cd2a5b02841847671994420c23ab8cca210610f5d664cc83087eeab26641843d76953320c21fbb2a9990618b99252cc830c5ac9296641862e6454b320c316b22a5990619a54960cc830c72a9300641863954580320c335292c0190618b95262d4430c5aa9316a21862e5458b510c316aa2c5a88618b99252d4430c5ac9296a21862e6454b510c316b22a5a88614d9d35194430a6ae9a8ca21856672d46510c2b2b96a3288610fdd16294430878e8b14a21856672d52510c2b2b96a928861599c85494430acae42a4a21853674d4a510c29aba6a528861c99525294430e4aa9294a2187265454a510c392aa2a5288614d9d05294430a6ae8294a2185367418e510c29aba0c728861599c86394430acae431ca2185667290e510c2b2b9487288611d1d94394430a6ee8b14a2185347458a510c29b3a665288614d5d33294430a6ce9304a21853574982510c23b3b6a8a8861599cb5454430acae5aa2a21847676151510c2b3390a8a8861595c854544308eceda92a21853674d49510c29aba6a4a8861c99525254430e4aa9292a21872654549510c392aa2a4a88611d9d85254430a6ce8292a21853574149510c2aa39ac8a8861599ca4354430acae521aa2185727090d510c2b8b8486a88611ddd94354430ae4e021aa2185717010d510c29bba2c4a88614d1d16254430aa8e6b12a21857070589510c2b9b8284a88615c1c14254430a6ce9992a21853574cc9510c2b938664a88615c5c33254430ae4e0192a218571700c9510c29b3a4c0a88614d5d26054430a6ce8182a218535740c1510c2b339060a8861595c8305443087aed2a0a21843f76550510c3172a4c4288618b5526214430c5ca8b10a21862d54588510c236bb4a4288618b9925214430c5ac9290a21846f76548510c317322a4288618b5915214430c6ca9308a21863554984510c333294c2288619954a61144308eeeca88a21863664544510c31ab22a228861999895114430ccac4a88a21846e72997410c236b94cba08611b9ca65904308dae532c821846e72195410c236b90caa0861875536350430c9ec6a92821864c63549410c32bb1aa2a08611b9ca65104308dae5328821867151583310c21f3b4a8988610f1da544c43087cecaa2621843c7655131
  | 13 => 0x5410630c68c928a631863464545318c2ca3a26218c61b44c5600c63087ce9b2c431843d74d96218c21f3a4cb10c610f5d2658863087ee8b2a431843c74595218c31a324a290c618d1915148630a6ce3aa6811852c72552408c31b2a4c3204618d5526190230a6ce3aa2811843e76151408c317aa0c4a04618b150625023087eecaa0811852c72550408c317b20c4aa26199d8b6155130cc8c5b0aa89863764185544c32bb18c2aa26199d886155130cc8c430aa89866862d81544c21fbb2a82a2614b1c95415130a68e2aa0a8984f171983434c31baa0c2a1a618d1506150d308deeca90a49852c74548524c2b238aa4292610fdd16114930878e8b08a49847771594424c23a38aca212611d9c465109308eae2328849861c5458c424c326b18a4212619a14960109309e2e2302649858e74d89324c2a73ae8499261725c0424c930ba2e2302649847776544514c29a3a2a228a61591c9511453087ee8b10a29843c74588514c237b92ca20a611b1c965105308dce4328829846d72194414c32ab18a220a618e1516010530ce0a2b00829863464d45314c31a320a298a610f9d2654853087ae932a429864c654c9214c3463226490a610fdd16508530878e8b28429843e74194214c21eba0ca10a619558c5108530cd0a4b0042984cd7298f404c317aa0c4a02618b1506250130c9cc6b16a81866662987540c332b14c3aa0619998961d5030ccac4b0ea81867161983540c297396a92a0614b5cb5495030a6ce3aa4a81853571d52540c297394c72a0614b5ca6395030a6ce3304a81853571982540c297396c8aa0614b5cb6455030a6ce3b22a81853571d91540c297394c6aa0614b5ca6355030a70e0b12a81851c73585540c29b38cc0aa0614d5c6605503087eecaa0a81862d54988540c316aa2c42a0618d5526115030c6aa8b08a81862e64988540c317322c42a0619398d6215030c6cc9308a81866662984540c332b14c22a0618d9916115030cacc6b08a81866662584540c332b12c22a0619a58a6015030ce2c3300a81846d7598a430c3172a4c5218618b5526290c308deeab14861862e5458a430c316aa2c5218618e5516090c30c6ca9b0a861863554d85430c31b2a0c2a18618d5506150c30c74a8b00861863654987520c31aaa4c3a90618d95161d4830c6aa8b0ea41852e74d4a520c296ba6a529061599c75294830acae3a94a41843f74586520c21e3a2c329061599c75494830acae3aa4a41856671152520c2b2b88a9290611b5da4394830acee2a1ca4185647150e520c297ba2c3290614b1d16194830a5ce8304a41852d74182520c2b3388c129061595c460948308dcedaa2a41856671d51520c2b2b8ea8a90611b9d85454830acce22a2a41856571151520c2b4382c8a90614b9d26354830a5ae931aa41846e7690d520c2b3b8a86
  | 14 => 0xe2a1e80a0667529864050332294c32028199d496190140cc8a4b0c80a062d6214a4050316bb0a5202818b58c5290140c58a530c80a0724529864050353a94c3202818d14a6190140d48a530c80a0624529864050392292c320281ac98750901408dce430aa62046d72185531022fbb2a6298819354d6214c40caaa6b08a620636541854310237bb2a4290819358d5214840ccaa4b08a42061e6454f321023bb8aca990811d1c5654c8408ece232a642047571195321021ebaec899081c354c424c840cb2a63026420669521813210354210c0990811b9c863544408dae431aa22047776544511032ab1aa2288819958951144408dce432a622046d72195311030e324a6988818d192514c440c68c8a8a622046e72d943110236b96ca188810fdd564884408bce632a422045d731952110316324a4908818d1925148440c68c8a8a422043d7610a501021fbb2a5a00818b98952d004087aed2a48020479769524010317b2ec4a00818bd946250040c5aea312802062d531894010316312a4a00818b18a5150040b62e3b22802066b65d894010335b28c4a0081aad906250040a76eaa0a802052e72d5254cc297396c8aa6618dd90615533087eecaa0a9985347155054cc32d31ac02a6614b9cb54d0f30a68e2aa4879862e5498a43cc316aa4c521e614b9cb5450f3087cec2a287986375418543cc31a2a0c2a1e610fdd95410f30a68e2aa0879852e74d4a52cc237bb2a4296611d9c76590b308eae3b2c85985347155242cc30eaa4c7216611ddc56550b308e8e2b2a85985347155042cc317324a5996618b99152ccb30b1ce9b12659858e74d4932cc2e4b86a499661339d8524cb30a9ceba1265986c93258032cc21fba2c528e610f1d162947308eeeca88a3985347454451cc237394cba0e611b5ca65d0730a68e2aa6839852e72d5241cc21f3b4a8a0e614d1c5545073087aedaa0839852e72d5041cc29a3a2a398e614d1d1510c730ce2a2b00639843e74d9721cc21eba6cb90e610f9d265c873087ae932e439843f7459521cc21e3a2ca90e618b1925248730c58c8a92439864c654c921cc3463226490e61b24cb6048730a68e2aa681984cd7298f40cc29a38aa8a06618b9506250330c5aa8312819853671d52548c29b38ec8aa4618bd90625523087eecaa0a91852c72550548c32cb1cc02a4614b1c954d0e309e2e3306871852c72551438c31b2a0c2a1c618d5506150e3087ee8b0ca51843c74586528c237bb2a4294614b1d15214a308ece332e851847571997428c296392a9a14614d9c75490a3087ced2a2851852c72551428c21ebb6a8214614d9c75410a30a58e8a94651852c74549328c278b88c0994614d9d351946308eeeca88a31846e72d96418c236b96cb20c614b1c95490630c72a9304831846f72595418c236392caa0c614b1c9
  | 15 => 0x4d6318c52502b3388c629281595c46314940ad2e0318a4a052d76d0c525038731e8629281c358f4314940a5ce3a18a4a052e70d0c5250236bb4862928159dc54314940ac8e2a18a4a056b7050c52502b438286292814bdd94314940e1ee6a18a4a07277150c525029638a8629281c91c54314940a48e2a18a4a072b7050c52502963828629281ca1c14314940a5ae9b08a4a052f745845250296ba0c229281539cc6114940a9ae6308a4a0569701845250317b94cba12818b99752d0940c5ac629684a062c52987425025d384c3a12818b14a60d094096ce330684a0668529824250335a90c0a12814b9d76250940a5cec29284a062e761494250317b18a4a12818b1486150940c5cc9a9664a062e6414b3250316b20a5992818b990528c940c5ac829464a052e75d0a325021f3acc8992812d1c5644c940970e0b2264a054e73d493250317320a4992818b590524c940a5ceba1264a062c65d09325023b388ca192811d5c4650c940c5cc829064a062d6414832502a6b98a4192819a14a600c9408dce531ea2a046d7298f515021fbb287a8a814d1c543d45408dceda92a2a064f63d49515032631ea4a8a811b9d85254540c9ec6292a2a064c63149515023bbb2a228a81551cd5114540cd0a530482a066852582415021ebb0a720a810f1d56290540c5ac429482a062d7614a4150316b18a520a81c91485190540c58a530482a072852982415025d3acc120a818e9d66090540d56a530482a0638529824150354294c120a818a14a6090540e50a4b0482a0727525044150316b10a420a814d5c45210540c5cca29082a062d761484150316b18a420a81c99c45210540e4ae229082a0724529844150392294a220a816c5c2511054096eeca8882a0594735444150393a92a220a816cdc15110540c58a530082a046f725973150236392cb98a818b99052cc540c5ac829662a0724521073150237b92cb18a811b1c9658c540974e1b2462a062f6414a3150316320a518a811b9cb654c5408dae5b2a62a062f64d493150316326a498a818bd90524c540c58c829262a046f725943150236392ca18a811b9c8650c5408dae432862a061d64d4c31502373acc418a811b1d5620c5408deeda9062a046d76d483150317326a418a818b593520c5408deec29062a046d761483150317320a418a818b590520c540c6ac9a8862a04b57610431502cab988218a81c514c410c540e48a420862a066b529803150334294c018a8196d4d600c540cd6a4b0062a0668525803150339a8ac018a819c145600c540d6082b0062a062e6414b2150316b20a590a812e9c3648854087cea32442a062f6414a2150316320a510a818b1935248540c5ec829242a062c64149215022f398ca10a81175cc6508540c5cc829042a062d641482150334294c010a819a1496008540b60
  | 16 => 0x2d5386a421481635cc5210a40b54e0290852047671997329023ab8ccb994818759153cca408ece332c652047571996329023b388ca994811d5c4654ca40e1aa6212652047671994329023ab8cca194818b5884294640acce429ca3205657214e51902ab398a528c81555cc5294640e4ca5214a3205357510a51903922908528c81599cb6494640acae5b24a3205377458e519029aba0c728c819558c6394640acce431ca3205657218e51902b9380c728c81599ca4394640acae521ca3204777650e519029aba6c528c814ddd16294640ae4e0314a3205357090a51903933908528c81c99884294640e4ac4214a3205357010a519029b3a66528c814d5d33294640e4885194a320537744ca519029a3a26528c81c91093294640aace6304a3205557318251902b3390c128c81595c860946408dce431aa32046d7218d519023b3b6a6a8c811d9d85354640acce429aa3205657214d519023b3b6a4a8c811d9d85254640aace6292a32055573149519029aba884a8c81c9d484254640aaee6b22a3205547359151902b3b92c8a8c81591c96454640a6ee8b1aa3205357418d519032ab18c6a8c81599c86354640acae431aa3205727018d51902b339486a8c81595ca4354640ae4e121aa3205717090d519023a3b286a8c814ddd16254640ae6e0a12a320570705095190392a1084a8c814d9d33254640a6ae9992a320572700c951902b8b8064a8c811ddd95114640ce4a2b04832067151d81419031bb24a298c818d192514c640c68c8a8a6320554735453190237396ca18c811b5cb650c640c6cc928863206356494431902aab9ca218c819998a510c640ccac5288632063664544319031ab22a218c8199989510c640ccac4a88632067151980319033928ac018c819c545600c640c6cc928c432063564946219031bb24a290c818d1925148640c68c8a8a4320672515802190317312a5a04818d59651d0240c6cc528e8120635655474090338b2ca3a04819c59551d02408dce530ea6a046d72987535022fbb2a629a81551c55314d40974e130e86a04b67198343502373acc521a811b1d56290d40caea630a86a065453185435021f3aec4a1a818d9d46150d40c6aea30a86a069753185435031a298c2a1a81a514c6150d40d60c3b0286a06b36118143502d338ec9a928159dc553d4940ac8e2a9ea4a070c5350f52502d238a87a9281599c764d4940acae3b26a4a064f6398f5250296ba0c7a92811b5da43d4940acee2a1ea4a05647150f5250296ba6c3a92811bdd95214940a5ae5a18a4a052f7250c525029a38a86292811b5da53149408deeca98a4a05677154c52502b238aa6292814b9d74314940e1ea6a18a4a05a47150c52502a739ec829281535cf6414940acce3b20a4a056571d905250296ba6c6292814b5d26314940a5ae8318a4a06
  | 17 => 0xa438bd506250521a68eaa088290e2c5498b31487162a2c598a439314d62cc52187ce9b2a6290c3d74d95314861fba2ca98a430f1d1654c52187cebb226290c3e75191314861f3b6a898a430f1db544c52187cec2a26290c3c76151314861fbb6a818a430f5db540c52187eec2a06290c3d761503148717aa4c418a438b152620c521c5ea8b106290e2c54588314878baa26218a438ed52600c521c70a93006290e3b54580314871c2a2c018a430f9d263d412187ae931ea090c3e76d51504861f3b0a8a824387d536354121c38a9b1aa090e1f5418d504870e2a0c6a82431edd95014121ab0e6a80a090c6e7298e540861fbb2a82a043875516315021c72a8b00a810e1e6458c5408726b1cc42a0439558e6115021cb4c7300a810e5963980540871d322c02a0439698d6015021cb2c6b00a810e6a62580540873930ac02a0430f9d06054c2187ae8302a610c5f7654c530870eb22a6298439654d6014c21c3ac9318a610e2e649885308716b24c4298438d5926114c21c74c9300a610e39649805308735314c0298438e9916014c21c72c8b00a610e5a635805308735312c0298439c9856014c218f4e032e8610c79701974308637390cb218431e9c06590c218f2e032c8610c6d7598a4308726a9cc5218431d9c66550c218f4e032a8610c7970195430863aba8c2a18438d9506150c21c6aa830a8610e5653185430872aa98c2a18431b9c86510c218ece23288610c7a70194430863cb80ca218430f9d2639482187ae931ca410c5e73d96420862eb9ecb210438d552619082187ce9b2c6410c3d74d96320872aa9cc3190438b55262904218bce63288210c5d731944108637baac5188430f9d3650c42187ae9b286210c3e74194310861eba0ca1884387592530c421c3ac8a986210e4d53988310872d29ac0188439654d600c4218daed2944210c757694a2108717b2ec8908438bd9464484218dceda9a4210e3765d91210871bb28c8908430f9d0635402187ae831aa010c7b76540500871cb22a0280439658d50140218beeca98a7a052e7294f43d021fbaac5a1e812d9c660d0f40a5ce529a87a06376518543d031aba8c2a1e818d94c6150f40d64e030a87a06b17018543d030f31a87296814d1c54394b408deeca90a5a04b67198342d023b38ecb196811d5c7658cb40968e2b2265a04b87059132d025cba0c099681aad08604cb4087ceda1aa3a05347150d51d023bbb2a228e814b9ca539074087aed29883a052e7294c41d021fbaac420e811b9cb65cc7408dae5b2e63a046e72d9431d0236b96ca18e81655cc410c740d6082b0063a045e73d9721d022eb9ecb90e812e9c36488740972e930443a045f7654c5390326a9ac429c819394d6290e40c9aa6b14872047575d85439023aba8c2a1c811bdd95214a40c9ac6a90a5204ad76d48429
  | 18 => 0x394f21c38e6b24a790e377159253c871a38ac929e438b9926294f21c5ac9314a790d1e74d8d53c861f3a0c0a9e430f5d06054f218beeca98a790d1e73d5343c868eba4a7a1e438b9526290f21c5aa93148790d1e73d5143c861f3b0a8a1e438dd506150f21c68a830a8790c7a7019443c863cb80ca21e430fdd95410f21c6ca8b088590d2e7494e32c86a739ca8996434b9d2534cb218dcec29a6590e565358432c868f39ea920e430f9da545072187aedaa08390d1e73d5041c870e324a698e4387191534c721c9aa63126390c7b7654050c8734b14c1aa4439c98560d5221a74e1aa4a910d3a70d91548861fbb2a82a4439958a611522187ce9306a710c3d74983538862fbb2a629c438b9916214e21c5ac8b10a710e3a64980538871cb24c029c439a58a6014e21c74c8b00a710e39645805388734b12c029c439c9856014e218f4e132e8710c7970997438863d380cb21c431e5c06590e218f4e132a8710c7970995438871b2a0c2a1c438d5506150e218f4e03288710c7970194438869d386a9214430f9da5450a2187aedaa08510d3a70d5042887172a2c420c439354d620c621a74e9a84a110e2f725925088716392c9284438e1c1649422187ce831aa110c3d7418d508863dbb2a0284434d5c763d5121a5ae431ea890d3a70d8b544869cb86c5aa243479cf61d5121a3ae7b0ea890d2d72d83544869ab88c1aa2430fdd95415121a5ae5318a890d377158c5448696b90c62a2434d5c46315121a74e0318a890d397018c544869ab8cc02a2434bdc96015121a3ce6300a890d1d731805448696b90c02a2434d5c4601512187ce9306a690c3d749835348717322c529a430f9db5454d2187cec2a2a690e3b54d81534871c2a6c0a9a438ed506054d21c70a8302a690e3464d85534871db26c0a9a438e1936054d21c76c8302a690e3864181534872db18c0a9a439ad886054d21ce6c2302a690e7171181534862fbb2a629a43561c15314d218f4e1b2e8690c7970d974348636b96cb21a438bd526290d21c58a93148690c6c7558a43487162a2c521a431ddc56550d218f6e0b2a8690c7870595434863b3aec2a1a438d1536150d21c6ea830a8690e3454185434863d380ca21a431e5c06510d21c58a93108690c6c7558843487162a2c421a438d1526110d218e8eab088690e3454987424871baa0c2a12434b1d5421092187ceb3266490c3c75593324861fbb6a9992430f5db54cc92187eec2a66490c3d7615332486973a4a7192438d153614c921c68a830a6490c6e7695132486973a4a899243539ce544c921a9cebb1a6490f0c54d8d32487862a6a6992434b9d2534c921a9ce729a6490c6e7614d3248787aa0a699243c3150534c921a9cec29a6490e4e7614d32486a6b80a699243c9153614c921e48a830a6490e2c5498832487162a4c5a
  | 19 => 0xa98ca018db0744c6500c6b938ec9280635adc96494031ad0e4b24a018d3a7418e500c69cba0c7280635a9c86394031ad2e431ca018d6a7290e500c6b4b9487280635cdc54394031ae0e2a1ca018d3b7458a500c69c3a2c5280634e9d06294031a72e8314a018d5a7318a500c6b9388c5280634e9d33294031a72e9994a018d3b744c6500c69c3a263280630f9d0625403187ae8312a018d5573105500c69a3a262a80631e9db5454031ad4e5aa2a018d6972d51500c79838ca8a8063cc1c554540318f4ec2a2a018d6a72151500c6b4b90a8a80631e9db5254031a74e9a92a018d3974d49500c7952a4a4a8063ca5525254031e54a8a92a018f2954549500c63d3b0a4a80634e9d05254031a72e8292a018d7175d05500c7992a682a8063cc5534154031ec4a5a0aa018f6152d05500c7992a082a8063cc5504154031ba2e620aa018f6252105500c7b0a9082a8063c65533154031e92a598aa018f32548c5500c798aa462a8063d894a3154031ec2a518aa018d5b754c5500c78caa262a8063d25493154031ae6ea98aa018db0744c5500c7992a262a8063cc5513154031ec4a498aa018f61524c5500c6b938ec8a8063561cd6454031ad6e4b22a018d6872591500c6b838ac8a80635a9ca4354031ad2e521aa018d727190d500c6b8b8c86a80635cdc54354031ae0e2a1aa018d727110d500c6b8b8886a80634edd16254031a70e8b12a018d5873589500c6b838ac4a80634e9d06254031a72e8312a018d5a73189500c6b9388c4a8063569ce4254031ab2e7212a018d7271909500c6b8b8c84a80635cdc54254031ae0e2a12a018d3a74cc9500c69cba664a80635c9c73254031ae2e3992a018f49320c9500c6b938864a80635c5c43254031ae2e7a0aa018f3343d05500c798a1e82a8063569cc4154031ab2e620aa018f3141105500c7993a082a8063cc9904154031e62c820aa018f5273105500c6b8b9882a8063d45cc4154031aa2e620aa018f3243105500c79821882a8063cc9084154031e608420aa018d72748c5500c6b83a462a80634edd13154031a70e898aa018f33744c5500c6b93a262a80635c1d13154031e60e898aa018d30744c5500c7a9b9a62a8063d490d3154031ea28698aa018f53324c5500c7a899262a80634e9d03154031a72e818aa018d6a720c5500c6b4b9062a80630f5da541403187eecaa0a018e2e54988500c716aa4c4280638b9516214031c5aa8b10a018c6d76948500c717324a4280638b59252140318deeca90a018e2e64548500c716b22a4280638e9526014031c72a9300a018e6a52980500c734a94c0280631edd95014031c74c8a80a018e3964540500c735312a0280639a5895014031c9ac7316a990e566358754c868f39ea92a643479cf645532187eecaa0a990e666258454c871b322c3a9e43479d35
  | 20 => 0xd74181520c6a7398c0a9063599c4605483187aed2a0a418c3f76550520c7172a4c4290638b55262148318deeca90a418e2e64548520c716b22a4290638e9526014831c72a9300a418e6952980520c71d2a2c0290638e5516014831cd2a4b00a418c7a70997420c63cb84cba10631e9c265908318f2e132c8418e1d5498e420c70eaa2c7210639358e5290831c6aa930c8418e3554586420c733292c3210631e9c065508318f2e032a8418e3554d85420c732a96c2a1063355cc61508318f4e13288418c7970994420c61ebacc9990630fdd564cc83187aed2a66418c3f76553320c717324a5990638b59252cc831c5cc8a966418e2d6454b320c732a92c399063c3551320c831c6aa93086418cb474584320c71aaa2c21906399949610c831d8a64b086418d7170d53410c71ab2ca9a08634d5d743d0431a6eeaa1e8218f255494b410c732b2aa5a0863c955152d0431c3aa8b1c8218e1e5458c410c72731aa4208639358d5210431c6acaa088218e9563504410c792a9282208638d5966410431ae2e1aa08218e3565950410c63bbb2a8208638d9915410431c6acaaa08218c777558c410c66bbaac62086395dd56310431d2ca8b188218e955458c410c65abb486208638d5964310431d2ac72188218da67290c410c71ab288620863995965210431d8ac72908218e6565548410c792aa2a420863b158d5210431c6acb2108218d9673908410c74ab1c84208634d5d44210431c6aca2108218e9563108410c786aa2a598863175da538c4318eaed29c6218f255454a310c61f3b4a8988630f1da544c43187cecaa26218c3c76551310c717b24a4988638b192524c431c5ec8a926218e2c64549310c70fba6ca98863871d3654c431c3ecbb226218e1f65191310c70fb2ca89886387d95544c431c9ecb2926218e4f65549310c786aa2a498863359da414c431c6ee9b2a6218e3474d95310c71bb2ec8988631d5d6644c43196ce93226218e3765191310c74ab98c8988632d1da544c431c6ecb2a26218cb476551310c71bb2aa8988638d192534c431d28c929a6218e946490d310c6e2b948698863351d9434c431ccecb2926218ea464949310c733b2aa498863a9191524c431e4aa8a926218d9574cc9310c74a3266498863a5191324c431c5ca9316a018e2d5498b500c7172a2c5a80638b55162d4031c5cc9296a018e2d6494b500c717322a5a80638b59152d4031a74e9a84a018d3974d42500c6b5396a1280635a5cb50940318dee4b24a018c6c72592500c61fba2c5280630f1d16294031ad4e5aa4a018d6972d52500c79838aa9280635a9c85494031ad2e42a4a018d3a74d4a500c69cba6a528063ca9525294031e52a9294a018f2a5454a500c794aa2a5280634e9d05294031a72e8294a018f3154d06500c6e8b98832806356dd53194031ae6e
  | 21 => 0x696392c02a263475cc6015131a5ce4300a898d2d72180544c69ab88c02a2638d15261d0d31c68a8b0e8698e2f5498a434c7162a4c521a638bd516290d31c58a8b148698e3454d85434c71baa0c2a1a638d1506150d3187ce9306a498c3d74983524c61f3b6a8a92630f9d85454931c76a9b02a498e3854d81524c71daa0c0a92638e15060549318deeca90a498d6870548524c61fba2c0292630f1d16014931a5ce5aa28498c7a70194424c63cb80ca212634b5c85410931c38a93188498e1c5458c424c71a2a4c2212638d151611093187eedaa66498c3d76d53324c61fbb0a9992630f5d854cc931c68a930c6498e3454586324c71a2a6c2992638d150614c931c38a931e8298e1f5418d414c71a2a2c198a630f9d262d413187ae9316a098c3e76d51504c61f3b0a8a82638bd536254131c58a9b12a098e2f54189504c7162a0c4a82631edd95014131ad0e4a80a098c3f74588504c61e3a2c4282639a98a60d5031cd2c5306a818e6a62583540c734b12c1aa0639c98560d5031a5ce5aa4a818d2d72d52540c69d386a92a0634e5c354950318dee4b04a818c6c72582540c697394c72a0634b5ca6395031a6ce3304a818d2f72582540c696392c12a0634b9cb6455031a5ae5b22a818d3a70d91540c69cb86c8aa0634b9ca6355031a5ae531aa818d1e73989540c69b38cc4aa0634d1c56255031c6cc630aa818e3463185540c71b310c2aa0638d1886155031c68c3b02a818d3671981540c68e39ac0aa0634bdc96055031a58e4b02a818d3471581540c61fbb2a82a0638b5526215031c5aa8b10a818e3954980540c71caa2c02a0638b9926215031c5cc8b10a818e4e63588540c732b14c22a0638e9926015031cd4c5300a818e6962980540c71d322c02a0639698d6015031cd4c4b00a818e6962580540c73930ac02a0631b5d66290c31c5ca93148618e2d5498a430c637baac5218638b9516290c31c5aa8b148618e3554586430c71b2a6c2a18638d5536150c31c6ca8b088618e3a54983520c71caa4c1a90638e95160d4831c72a8b06a418d2e74d4a520c696ba6a5290635a9c35294831ad2e1a94a418c3f74582520c61e3a2c1290635a9c35494831ad2e1aa4a418f2471552520c6b5380a9290635a5c05494831a9ce7b24a418d6671d92520c636bb4872906359dc54394831a5ee8b04a418d2c74582520c6973a0c1290634b5d06094831a9ce6304a418d6671182520c61f3a0c0a90630f5d060548318dcedaa2a418d6a70d51520c6b4b86a8a9063c91c554548318dcec2a2a418d6a70151520c6b4b80a8a9063591c56454831a5ce931aa418d2d7498d520c6373b486a906359dc54354831acce221aa418d657110d520c6973a062a90634b5d03154831a5ee8b02a418d2c74581520c6a639ac0a9063591c56054831a5ce8302a418d2
  | 22 => 0xa832d9d46150d41c6cea30a86a0e4d63d4a5250637bb2a4292834d1c54314941968e2b2664a0e1d64d4f325063d380ca192831e5c0650c94187ceb32064a0e1d6314e4150637394c7a82831b5ca63d4141a68e2a1ea0a0c5e7398b505062eb9cc5a82831edd950141418dce4302a620c6d72181531062fbb2a6298839354d6214c41cb2a6b00a620e3471596431065ab8cc5218838b5966290c41c5aa73148620ea67198a4310752b8cc5218838b5956290c41a6aebb0c8620e3565d864310752b16c321883a99886190c41b62e030c8620c5e73181521062eb98c0a90831bdd95214841c9ac6a90a420e6952580521070f31aa7210830f5d66310841c3cc6a988420d2d759884210697bb2a4210838bdd95210841a5ee6a908420d2c70548421065bbaac2210838ddd56110841968e6b088420e3553584421065bb82c2210838b549601084196ae33266420e1e6454f3210716b288519083695c4428c8418f6e0b2a6420c7870595321063d380ca990831e5c0654c841c58c8a926420e2d651093210786a988499083695c4424c841caaa630a6420e6552185321061ebaec8190832b9cb640c84196ae23206420cb970190321069739487288830f5d8439444195ce531e8220c3f7654f411070f31aa7a08830f5da54904418eaed2a48220e966390e41106d339487208838718d5350441a6aeb21a8220e946390d41106d2b9486a08832d9db425044187aec214a020d397010a5010637390c6a80831b5c863540418bce6312a020c5d73189501063dbb2a0280839658d5014041cd2c4a80a020e4e6358b54cc697396a92a6634b9cb645533187eecaa0a998e566358454cc697396a9a1e638b9526290f31c5aa93148798d2e72d5143cc61f3b0a8a1e638d1506150f3187eecaa08798d2e74d4a52cc61f3a0c0a96630f5d06054b318deeca90a598c7b7059542cc63c382caa16638b99252ccb31c5cc8a966598cb47458432cc697396a920e630f9da545073187aedaa08398d2e72d5041cc63abb6a820e632d5db5410731b2ce7aa08398da672d5041cc6cb398a820e632d5da4310731b4ce52188398d367510841cc6cb3988420e631bdc964943318d8e4b24a198c3f7458a50cc61e3a2c5286631edd9501433187eecaa0a918e5563984548c717aa4c521c638b1526290e3187ced2a28718e3654185438c71aaa0c2a1c630f5db5410e318deeca90a518e1f5498e428c696b90a8214638d1516110a31a58e8a946518d2c74549328c61f3b0a8a0c630fdd95410631a68e8b2e6318c7b76540508c717b14c5aa2634b9cb61d5131a5ae5b0ea898d2e72d83544c696b96c1aa2634d5c460d513187eecaa0a898c6f72580544c636392c02a263475cc6215131c5ac4310a898d3571188544c69d380c42a2634e5c06215131a6ae3300a898d2f72580544c
  | 23 => 0x5523287eecaa0a91964d63988548cb1b2a0c2a1c658d5506150e32c3ca8b18851946f76550428cb4731e8621465691c54310a32c3acb326651961d65593328cb16b2cc9994658b59564cca32a6ce9a8ca31943e74982518ca1eba4c128c651ddd951146328ece3b22a11947571d91508ca1f3a6c2a84650f5d361542328f6eca80a11947671982544ca3ab8cc12a2658dd906155132ce6c3b02a89967061d81544cb1db20c0aa2659ad886055132ce6c2302a89967061181544ca1fbb2a82a2654d1c55415132a70e0aa0a89963754185434cb1a2a0c2a1a65651c54310d32ad0e0aa684994ce7598f424cb273acc7a1265335c263d0932a68e2aa4849953870552424ca1f3b0a8a12650fdd95410932a68e2aa0849953870550424cac6b9ca8212651bdd95410932ad0e0aa084994af76550424cac7b9aa821265691c55410932b50e0aa084995a47150c424ca6639ac221265639d3528c9328eeeca88a29953474544514cab8382a228a651ddc564d41328e8e2b26a09943f74587504ca1e3a2c3a82651edd95014132a70e8a80a09957071540504cb17b92c8282658b1c96414132c70e0b20a09962d64d08504cab4b8084282658d9926114132c6ac9308a09963664584504cb1ab22c2282651d9c660950328eae3304a81943f76550540cb1aaa2c22a0658e5516015032c6cc8b08a81965663584540cb33312c22a0659c9866015032ce2c3300a81963a64580540cb2d31ac02a0659a9896015032ce4c2b00a81967161580540ca97396a9a18654d5c454d0c32a72e02a6861962e5498a430cb16aa4c521865479cf5450c32a5ce5aa2861943e76151430ca9ab88a8a18654e5c05450c32c6ea830a861963454185430ca1fbb2a8218651bdd56210c32c3aa931c841945d7694e320cab2b88a9190655a5c0548c8328daed29c641952e7494e320caa7baa84990651b9d8544c832acae22a2641956970151320ca973a4a699065635d2534c832a9aeb21a641970c5450d320cae238a86990650f9d2609443287ae9304a21963571191510cb1632464a88658b19132544328eeeca88a21963564544510cb38a8ac0288651edd95014032c72c8a80a01967161540500ca2fbb2a629e834b9ca53d0f41a5ce529a87a0e3765d8543d071b298c2a1e838798d4394b41a68e2a1ca5a0c6f7654852d069a38a86a86831edd950143418beeca98a720e2d5398a4390753314c321c839594c6150e41ad4e1a94a520c6f76548529061ebacc7214831e9c2658ca418f2e132c6520e2d6494a32906a639aa4994832d5c4640ca41972e03206520cb4745843290657394c7a0c838798d53d0641ad4e5a84a120c3d7690a509069cb8085284831b9c863542418dae431aa120c7b765405090727a9ac529a8317dd95314d41c9ea6b1486a0e4c5358a435072a29ec2a1
  | 24 => 0x30a8621e35751854310ec6b96c8a188795d976150c43caeca30a8621e97641854310e9a38a87290871d9c460548438eae2302a421c6f765485210f32a92c2290879a5496014843a6ce3a1aa221d347150d5110e3bbb2a228887995895114443ce2a2b00a221d347150d5010e3b388c4a80871d5c462540438f6eca80a021e69625405010f38b0aa02808717dd95314f428eeeca88a3a147b7654050d0aab38ea729c851d9c46054e428eae2302a72145f7654c5390a5b38cc1a1c859354e6290e42caca630a8721655531854390a8f3b4a6a1c85879da5350e42e2ca7b0a872161e531854390b8b298c2a1c85a91886150e42c6aea30a8721636531854390b4b298c2a1c858594c6150e42d2aa630a872143d751814390a5b38cc1a1485559cf5194642878eca1aa3215347150d5190a3bbb2a228c854d1c54354242a74e1a12a12147b765405090a3d384c3a9a851e5c261d4d428ece3306a6a1475719835350a2fbb2a629a8593d4d6290d42c3ccaa1886a1673515825150a3bbb2a228a859c58750941428f6eca80a0a1539709085050a3d380c2a98851e5c06154c428ece2302a621475711815310a2fbb2a6298859554d6114c42cb2a6b00a62143d759834310a5b38cc1a18854bdd56250c42b50e0b1286216a562d854310a56b90c2a18858dd946150c42d4cc430a8621635751854310b1b298c2a1885a99c86150c42d4ae430a86214b6719834210a1ebb4a9210851b5da5490842d1ac6a1c84215a47150e4210b47b1a86a108569dc543508428f4e031aa2214797018d5110a1f3b686a88854d1c543544428eeeca88a221655635445110b38a8ac0288851d9c463540428eae231aa0215347150d5010a9d38684a80854e1c142540428f6eca80a021659635405010b38b0aa0280851d9c660953328eae3304a9995367118e54cca9ab88c72a6654e9c06395332a72e031ca99951e7318654ccb1ab08c32a6654d9c66095332a6ae3304a99952f7258254cca8f398c12a6654ddc56255332a68e2b12a99953b7058954cca9c382c4aa665471cd6155332c6ac230aa99951e7398154cca9b38cc0aa6654d5c66055332a5ee4b02a99943f7655054ccb2731ac42a6658b9526290f32c5aa9314879962e5458a43ccb1b2a6c2a1e658d5536150f32c6ca830a87996355418543ccaca38a8621e658b9526210f32c5ca8b10879961e5458f42ccb0eaa6c6a16650f9d2609473287ae9304a39943d7695051cca1fbb2a828e651ddd95114732c74a9300a3996395498051ccb1d2a2c028e658e5516014732ce2a2b00a39943e74d8550cca1eba6c2a86650f5da541433287eecaa0a1996365498450ccb1aaa4c2286658d9516114332c6aa8b08a19947b7654050ccb38b0aa0286659558e61d5232a6ce3aa4a91947671982548ca3ab8cc12a4654d9c764
  | 25 => 0x4004000000803001400200a8000004002001801400c009000800000000c00000080080020010010008001001800c00c00b000800800200700000040000000000000004000000001c002004000800000200600100000120030000000000008000000000200700000380000070008010018004002805c00400e00000000040010050000012001000000000200100080000180000010004002003000000000001000080080060030010014000002000000000600e0058030000014004002800a00000180000020000000000000000002802c00200d001000000000a00000000060050000004002002000800800c001001000c02400100000140020000010024002005000000400a00000000180020000000000000000001001400a00200100100040000050000000008000800000c006000800000a0150030010002000001c6f7654852d0e3bbb2a228e871edd95014343a5aeba1ca521d4d75d0e5290eb338ec929487595c76494a43acce231ca521d657118e5290eb5380c7294875a5c06394a43a5ce3a1ca521d2d74d865290e97ba2c329487539cc6194a43a5ee8b04a521d2d741825290ea7398c129487599c46094a43acae2304a521e69601825290e3b388c0a94871d5c46054a43a5aeba1aa521d4d75d0d5290eb3b8ac8a9487591c56454a43ad6e0b22a521d68705915290e97ba2c2a94874bdd16054a43a5ae8302a521d4e731815290eb3388c0a9487595c46054a43cd2c0302a521c6f765485290e9b38e86a8c871b5da52146438deeca90a321c77765445190f35294c028c879a54a6014643cd4a4b00a321e69525805190f38a8ac028c871b5da52142438deeca90a121e66529845090f32a94c228487999496114243ccaa4b08a121c7b765405090f38b0aa028487a3d4e6290d438ece3306a4a1c75719835250e37bb2a4292875a1c15214943b4ce5b26a2a1da67290f5150eb9b82a5a8a875c1c152d4543acce5b26a2a1d6572d935150eb339487a8a87595ca43d4543a6ae9b16a2a1e73609835150e9aba0c1a8a871ddd95114543a5ce5218a2a1d357190c5150ed33948628a871d5da52145438eeeca90a2a1d73705485150eb8382a428a87599cb6414543acae5b20a2a1d7270d905150eb8b86c828a87599ca4314543acae5218a2a1d367290c5150f933948628a87499ca4314543e4ae5218a2a1d357090c5150e9aba6c428a874ddd16214543a6ae8310a2a1d55731885150eb9380c428a875c5c06214543a6ae9b00a2a1d35749805150e9aba0c028a87555cc6014543acce4300a2a1d65721805150f38b00c028a871d9c662d41438eae3316a0a1c7676d455050f33b16a2a82879918b51541438ecec28aa0a1e67621455050f32310a2a82871edd95014143ad0e4a80a0a1c3d769524310e2ebb4a9218878dd976150c43c6eca
  | 26 => 0x3000800000000100000280020000030004000001000004000000000100300000020008004000008002000c00e00300100000000040050014002008000800800a001000000400c001002000000000100080080000000000004002000016003c0080050048000010005000000c00000700080040020050020008010000000802400800d000802800a0000060000000000001000000c001000802402400100080080120010000008000000004800000c000001801c00c0010048000004005000001400200000180000120060058004002001000000c00200600080240000000008008000000002801001a000000000000e00200000000000000068000008000001002000400200300040000070030018002000001000001000200180040000000000014000002000006c00400000080100020000080000000001001800400a00100000240060010000008006002000001000400100000000120200058004006000000000400a0010000008000002000800c01800300000000060030008000000000003000400000000000080060040080004002000000001800200400500040040020040000000003001801400600000080100000000008044000000000801000a000001000c0000020090000006000002001c00600400880000000060000034008006000000800400600000180060010008000018002000804000400200100040060000018000016001000800000e0000000000016009000000000e0060008000000006000800000a002000000000200000080080080030030004000000001800800000200280040020010018008000001000000400200000000040140040000004002000000001c00a0070000010004003005000000a000000000c00a000000000000600300100040180050008010002021001800400200000100000000140020000002003004000400c00000000340000070020000002000001800403600100280000000020000030016000000802c02400200080000000000000008000009000000400800000000040020000000000010000001000c0100000008000000006002000000800200000040040020000000002000000000800000000000040020000008000004000000000000201300100000040000020008000000003000800c00100080040180000000004008001000000000200000000000120010018010000006001001400400b00500000000040040008000000000800401c010000000800200100500000080020000008000000002800404a012001000000e003001801001a008003800000600100380500020080060008018002000000401c006004000000000e00100000000000000010000002004002400800000100000000040010000000000003802c00600000000000140000008000004001001001000c000000000
  | 27 => 0xb312b61c48dde18917262b2000083680000000000000000000003505eb0000313196000011aa76d801c02800300080000030018008002003000800c00200200080140000000010020000006000000000c003007000c006004004003800a008000800400e005000800c0000040038000000000000002800200c000000800c007000800000000000080300060030000010012002000000800000700000100000110000004000003000000400000400000080080020010018006006000001400400700200000000030008000000000004801c00200000d000400600b000001800000100280000040010000010004004000001801600100200200120020000014000001003000c002005001802400200000180040000000000008002016000001800c000001800c0060050000014000001000001400600200380080320010000000000000003800800400600100080020000138000014000002800c00200300800080000000000000006000004000800000500180180040060048000008001000000000200600100000000010000000000004001000c008000002800000200400000000000010028014002000003002402a000002000000000100c802000600400000000000070080000004006000001c014000000001400000400000080000060000028008007000000000c0000000020000002006800800200900000040020080000000000002000802000600100580000000030058004000000003801c0020030040008010002000000000200100400080140040020000000001000001800000000080000000090068004008001005800800c0010010004004000000000c00200000000000020050030014000001004000800a000000800400a0000010030008003002801406200100000100080100090000020004002000000200000480000060030010000004000002000400000000080000020070000000000000000800c000001000000000400300000040060040048000008014001001401a00000100180020000000034000005002001000200500180000020000000008000003000000000c000001802c00000600180000080000050000000001000001000400100000100020020000000000000001000c0040050038000012001000800000e001001801c0020000028000000006006800800000000180040080020000000002001000000c0080000018000004005000801401a0020010008000003002000400000a004000000a000002801c00400000000000060140010000004001006800000000000000080160000010030002000005000c002004004801400000c0020004002000000000401c00200000040060020020008006000000000c010002000001000c007002001000000300200080060040000008000000000000c000000000000000000
  | 28 => 0xece66d85e84e68000044000014c92302208000564879a00010c45311d2027e874c63d1a3e5138dca27d000079d00000000000000000075b077c3d3927207f89940000a68728806235100000001b200001bce5ef000043a14801f61df20000000000170637a92dc000119c0000af07a200000338b6a70d0000000015800011f81811bb20000000000066c00005c00000000000000000000004ca894c00000000fd8adc0001cb40000a787a0800076f8000000073815190bc6d600003218fb600000001098000681936e038888c7fe006e7c19d5c8609eb05990d3679382be00000003d582e40000cfa00016cc6289fa4000051c2c90a344ed8000000053047380004f31a5e00000000002162062000000007782071ff40000000000000000012a257c1ace558033000019a2000209c00012a05420790000006a00000000001fe41560694407000026e8a3600000000000eb400001364c807f000012ba5a6800041e800000008180000d107c7118464c0ff00511ac658b94880000000769930c6f720542d797301ec04be27f981c00600002360baa000000000000004a3910c8511ab4000000000015c4829800058800d820105b600007b669d95e8000000034280001f1090a2ba800000011e6000000000000001068000000000026d80000001d4a000186876a000000006d400000001aa0446392800000000da00000000001c9237d0f7a00013f258280003ca88e677918b250a80f259e09ee000000000016b60001858620931e11e8f1800000000000000561934a33c20f2845071c00019405a603b84d892c621e95685801f8c23e1f443be155600000006cc00000000dc40000000833800066780000000e607168ee20000f9000000000000000000000000000000f700007fc992232e8a2215010aa05010f8000000061385b80000000135800027805860000000374883a78fa09a7979c3a26905ec0001100000000058e808200004564b5a02e00000000000000000157200000000000000000000079300005958dae39620420000a5c000186a0001d1018504ca0000012000000000000000490000425993c000000000000007c2848228000001438000000000027c8eb20001ce63f3894640920a0504800041f800023f0e3876b800009300004420000000089a12b1364505097a63410640a7203e3198bba6220ed214b800000012cc44e08e400011b67bc8c9c000030a00000002020b660001424332812e14e8d468149a6e7e00000000181a00015b40119e48000000000e8000767102e0c10ca662b00000001e726430000000174a00000007c214e4000187000008280000000000161215e800036516e000004f421812fa71115f200000000000000219148a000000000003be000093800000000b08000000096000016b4000141c729800071e188c2
  | 29 => 0x4c180001b38000000000000018b67bd0000000000000019c682c20926cd00004f003c85b50a244e717b416502603d30000055034e0001c2a00011860789de639a1032000000000000007b3013c5d40000612857c092064439b80003e094920000000000000000016fa00005d0517000000000000000118678000023780002f5800000001e084695965cc8a8a65484a200019fe71b80006cf8fc81090b9c539800085080003f180007b70ffe7be92c4453082200020ba1cb21682ba144a0001116000000027009b200006420001bd20000000000000048680000000000495124670287ac0000000728070600019ae52b89a27ee988606b828c423800026800000000000092994683d800013f02ea0b000001420b02000000000000000cd84660580000000097042206827b9849a4500e9808e8aee36f9b0c58b076c00019da000208a5c28dda1860a9a0000000327800000004de26580005568bac4d51ba62ed129a2841cdc85a800000a80004159382286000000000001d40b2800012404368cc24140000000000047313e80001bb409d100e000194a28580000001f9c61e005200000003a0800078c9dda00000001152060796135825a94aa1a28ddc3268c1683900005638000000000000006a60001e8c00013fe000104e1b000006a1800045703603419b6c000045259c0ce0000089200019821370ea26291dbc0001d8a777800040a00001e18fd45988d82759072200000000000000123000029780003d08f3413801d64f59b48195007240100006f9000070e000000017825e88000000000057b8000000000066f800023300000718cc885c86ee66c12d81b4983014319ea42a1b4620f933654618220b11d1c6a0000000013ac49587ae0701d90000000000000005a58fcc6e58cd40001fe208918e45f6166e723906c0a20e2e47a1fbc000010c4060afe4c2095272400004a21220000140a00000001b300000000f8e000000000000003a20e7a0000ba65cb8038319002e0000000000116629380003fa000000000001a7000055080003a40000000068c3fa909a79580000000044663000056a86c2000199634380000400000247000030d800062a98bc000072e772910e4db1eea656882a60b12f64831f5847b9f8a5938000000146a49e8000214924821f000062988587f784ea4f400005df9f644d0159c20b87b400000000000e105fb80001bd99d20000000680000018800580000000000000045b016200007f600000e82048e74000000000014a84ac9d525bd97f4462848054c014e1f48e180001b1e6ab8000000153853611d482b03982a1862663e1cbc444808c0000c1a668021e0000000000000000000000002064000000000000007bd93ec2c3948480f004201283564c50000341000000003280000000000000085220d83559
  | 30 => 0x1adc0c000001e21b6e000000000014700d70b3a6560000000000082a00003dc8e3a1ea8e3e2f195a61ca0c783508f2600013de27b000041e16bc00003085f6a1304408ebc74995b800010c2000000000000002d70000000000000019765db919a74580000001a32000209800297683ce80000001668380983c32f91f47a00000000000000009080000000000000000000004bf99ee0f600004cb00003eb006408f1f2a4a40000052130425e09660000000041212e000162400000000000000000211000000000000950000000000000766b88000000000062613240000000000000000000000000f7c00015ac00000000000492683800003000004a7800037c9a6a3cd85de4e1153a58180006d31dd61548000584149e1589e0464290fa02280006ae00000000000000000000000003a0156a5d000005e4800000000001a816e60000eac04a085a2c98000000000035716080b200000001cfa5ef80502229d8216c0000000202c642039240a8c90000000000000005e316c832888ca02703ca3cc000000000002b080008128000549000051e053e6b8000011b123c45500003a51350000092a000059800020000251cc63bb8b983eb9d3438200000000000000000000000005b61444494800071c00000000000766900200013b217800e000000002b79cca005124c0660dd45f491943fc93001dd00000000000000020c0000a0a000000000015b007200006e2800000014ec0bd80000000000000000000000007b81bec0e98000835000001e00004a51fb44759a280ce80001fb00002b98404000175403796c218d000026619ac0000bb863020bc000037000000000000c5a00000003839f661ad1f420001a7a00000c400305f4000000080902d2000002c64380002ae92e01ca828e0138be400000000540000224000000018f000009d400015441e816da390051400000000001652000000000000000001d126cc9fbe000168c0000000000000050a00003be86724bf000000000001e29b76294967e00004225a800003478000000000000000000000a3e5f9800020401c46eb059e79a0000326000015c000000a00000000ce400000000ab0cee80405f200000000000000000000050c0000000150a18880000800e6216b884a10b154c83483fa84a21664cf11a80001ac407f00ca500817e7cd800000001ba144019a1f8800000018dc000000000000000000314000019c6f6801c6fe827c1af9e160000bc82f01db44261a52321148e6929ab073f04624ee950200008360000000630979677090747da80007a29b60000075e000157608f82100000aec5b103cc00003c62a9800000000003b90d3e79b00000000000000000000017ae301863214980000001d3014e13785791e7c4489770000073c00000000000000514800000000000ea80000000000
  | 31 => 0x7d78d4a00000001c90000000021a00013ae00000008470d4e0199cde00000000001090687000028996547ad80004f9162a000000000009ea7271f0e4210ecc7980b7063180547f9838c43c98e277e9a647c0800044c0e2c55e0000000000000001462fb00000001c680001c5c0001bcc3b098264298de87720c2a000025a0000000665000000008f465d05423f91d6600003a00000ee00001c4e67d0a042cb85ce0c9122a02d1b162a814fc000000000000000000000465800046780000000000000103400004e61d20000000015a533842e00000000000000773800050f190653299ce4dd19925a11aba81f96fe00016580001f386a695225bd0b960000000623800000003c23e580004af966c0000d2c01f93fa2e7994473c94c26bd8000000000071293be6ff944c00014fa3a718f200019c02fd88864088d220919e30325077a6ca16c60000c3827982b41a4909e1f9074e4b980007f810f6344a13e04f834a41c9f50000029210096f82f610920000000416964209902e800017d64f9800000014a627601ca22d9bf8000036483884cc20b0b323659ee43359d6e0001b0a000141a081189a46989ac5ce914233195820000f4a0000da62940a56568083c0001b1c1ee9d926168c4a1dc0ac02b10cea0fa042a75c135c67a164c000000000000fa6400c6c14919981a3961e000121e6e308887a395a8000061a7b480001bd1bd4074a12c6050000363957c000000016280000000000000000073d000015a880a0000000000095a000000008d0dd00000b3e4f70a720a80fda31b906614197081d880003379f1e71013a86791d1a000000035b80000000c7400007266c1126400000a83e980000172096000000000000003540a82000178457a8f02000071600000000000d2e2e5000000000005c91f960001d1e74f00006b2131c00010b22348c7a23714320000b6000016d00f80000000000069314f20000000000211e26d0000000147e000000081380002ce1cb68100000508801a30b003477601347cf98423d894d211d961a7309a5a655136670480f480083f480503fe83a05bc0631d140002160701967a52c063e3208000627800000000006618c8e55193fc1db979a229a03039317ba57284988080f3e17920fe8610a9c26987087c104880bc838449f125a6820704246981873e0000555207800000005929674000000009b80000001bfc7e3812c26309d20000eb041187521110000000000000198385168fb23de03023aa075455380004c6000000000000000bf87a800005570dc208584a864c93d400000006b48000580800007917e406c88be5599a9255e800000018f6018064864d866616100003a29f5477800000b880007c816aa00006003d6829600000000000352000000000000008300000000178600000000000f0a0000d14000
  | 32 => 0x2033e096076a68e192a65f8b3c000000019901d80000990000000065a000000000004ce0a98000000000002420000a74000154a00000000cf00a0193800032a800072b911823c800006e00006a88c086901ef0000125c5ca93a60000db832317e8662977843d000000000d05fe9e9863312bc098a01800001a232b800000015be370129252800000001d2c0f69f4000000005bf0000459000045c834c000000039f0000182000039400003958000000013000000005368d34000074202a8000840000000016900d78d4813880006f780001338000767800002380000001aac7631380691000018f0ad4000000014f000000000007bb173620306f05740a940001f7600012e400000007ad1e0800000000000e5a0001b2c41f0a206de19b40001a6248c800053a97cc34000006b41660541000000000007a10000000179e50199f20000000000000070780000000eda0000bce00000007ca0c0479180000001788853000027295c6291800061b000028300000d6122c5c380003d980007d8875c5cb000000005a80000000566895e12702ce69200000438c8a570000000000000000dbc58a1c0c0d88d5e000000000018d400009c600006a40001fc4229000038c103c000026a33d000064ea0762db80003721b4e0000d88000188a7068000340888445a011e03c0c00000068613b1abc34f1a2e00001120001dac2e68000000167c83800005f08000000000000000001138e967c51bba71f0bde0ed9d8e85585a00db800021587584a282ee1ba000085c000000011c600000000000000380186661c80000001f0c00000000000000000158035a831c43300005ae00003bc0656000216400015947a1a05a0ac0000000212200010123b5800000000001f580000000d7200000000001fcc000000044d000037b85f05f80f0e7209ed01ae8b3671f97a025a0cac5c8191881587d043501ac45600001278bd26d688980000000000057e2ff91fc000070c171925800001ec8290ba2273800000007f4000218c0001b980000000000000013192864788d7c1e9177a5ff91f045f80000001c88000217e000000000000000000fa4000112e3f489566e400002dd80000000000000000000014a20001f3c80d80000000000000188019f800000000863600a80067929837d83e66d41ea2165878c4790cc060790e085b04e40000e16000000003b0000000206c000213a000000031200000001d3e0000f1e72900003e284ae000000019a8a2a3818eea4f380003e69a7800012a6000100c21980000000000804800079c11de6be00000081bc82e393307ab8fbe5db032e45109925fa9d4e0ff000000000002c7000000000001e59a7c10f00004e4218800019bc00012082969b687268eae00000002bc800024100000000fe64da0000000209049380000000000000000
  | 33 => 0xb60c98d2a7ed83323a394f0000120a2d599ec0a417341dc800050320ca353092800005f80001e0c6a8062a000139e36a1178000046e8619146000000069c990267e923a72f878000015ec187800058980003a81cba0eb0ace44c80001fa902c72780000c60ffa00015f83848f4600014bc00000000001970000003c0001f70699800029082982d50000818926c6d79e6254d0000000000078f00001af000000017d4000000000000004ea899c4291f9467f000002b9472000175a0001da209f89d00000fec29f0c58334968a1ee0000000185e00000007e111da000029e0000000000000036d8564000012600015400000000000000043380000000a6a0001b9a7c0000051a12026e80b7871d000001780002f0980c00000007e680000000000000000000007b24f6000010700000000fe22b4000000003101300684000000000005d27f401a02848e22569000000015f4152000078b18be485000081b921600000001c50000000059a15c8000537000000020b20000a2c08983128428bc400020ae2c58000000080e000086a7401ec883218a82201bb80be8f7028e000042b05dc20d044221c8a06286a07c51b87fe5c710f02ec1de20000000000129c60116327ba12ec3cf187c299000000007f2000120e4ba93281f3043e0b61a902bd0d7e25b97600000da04c58000000109446e8000000000063583666ad800030c16ba000000076e210426e000023180c83188f20175947c78a1c6a0000000084800000006e00001dee23a0a7600006f8000057400007e03fd161c17500000001aea0e39c207d30d66178806c6918ca07531c260de0fc073b8b5836105021a68de2000104224398565440550460935e79986ca0001416000000027900003b38ff651d128402c1dc600000000001124349a118000000034217160001fac0c5800024f800063693d20001dd400003f062500001b40b0015300d40001b18000000000004144810764322000033d8000624000020793884a580002170000000000000017220000000000141800013420ae89ae00000002e21b7400000007f2000000017fc6a780000fb21360ec8f7400000001c015fe8459bd652d00000000ec64c89ea600013320cd1a425208d1a0001d1800000001290000000040a065800000001644358aaa0000000000000048f800000000002400000052800000000000000000000000000019e6134943e7a7935685e8a581d1000027680000001d040000000000000068811a20000ce88208d683938000828800049c0000000000000005ba000000000003b4000098822d00000001a602fa114e41280000121494000000005700005a0029a8160000000000000014be17d8c6a00012d06e880005ac1b8e4aa8f867a700000000000000218a385174260401ce583000000000000011aee41612d274
  | 34 => 0x19b80e1a028000073e6b982f43ee0000000000000000000000d904c980001729b440001d567809b14273042800000005e62174000000000000000ea05203df8bca4040016040800000011b028c80008059d0c1cd8b1207e88e200000005e70000325800000009367010000201800022c00002be00005ee09740001302000156c00018de65880004fda0486d91ec6000000011300006d29afe003800000000000000000000125e4fc10b40001278000000019b8a9008180008130e9e000025c03b800080e80000001bc21ea000008a864c0000fd00001eaa84997c447e9a3426c08c20001c7a00000005e9906e81780001cd208e49b8000000000047f800000000000000000000000014d800070b8a70000116a20c98c4405984c0000d16000045c47a93c200000000001bb61180000000106009400000001180000000002e0dd87dc80007d2090239c169c7fb8000245000000014600d5000017a848405582ec1ac040646b8f081bf91d20091f32588822009012b475c800000da0847579f1068499c8373000058f80000000000596817a5448000000000000000000000ee634a11267588eec6cea0d60e50000000000054d8000358000069f99d8000000000c0de61c687c875e9640308800031f07945d703c017e867012299103d1183a369000024304ba50b896c00000004b51c724848000104a0260000f2c00000003da000000000000000000000000076c000000000000000000358800000000006b5997a0001e10000000001f1e4077493f80ab91047d488264e48000000081a4e6084e0000000000165c0000e6a794000000000001bb1b8415689e881a0088510973846d05927c91d2e0000000343187a4b880000000000000000000000004e18000000000064e032c40801e6025800014a88400fa93ea47088a20419618732075a4ce970c1489ae4000108048d80006c3800000000002cb0000000000000011ac0001008000096233680002551bea19e1eb2000000000006ac72b00000001f740f882f00001f9267e017200000003b61f180000dc60e7000042c000000000006d889241571df000000001c0a0f4000000000000000000f100db0b1407300000000000821959809380000001b72000031e000092000008f6557800062c0e5e00000000000000000108a0df1e6e000000000014f40000e3c68300005340000000009a000000006a0000000000084918464980390720000024b835a3f10e4800014482a1009e000103a69c1f1217983968201e426a707fa0000da215d974c5c085c840994ee00000982b600f82ae1ec00001af257f0814840969273c10e21bca00437c001e83f00006789cc45a90000000000000000008069b002a20b4e0000000000000000000000000068000065a1000e722e4800024f000057897c8000063a7ab0b
  | 35 => 0x18e14087f6800015280007f5000000002f8519845a5c10000431827a00005aa848000052e80004c3800080a80006e192c049f8f1c0001a1e5240000000206a5b280be0000000215036800011dc00020cc0001062481811400000000000cd0000000000011282109afc16700000001e6a70900005ec1436163118c77411a03f609f072c9b406861b0669b00000d000006709d5a00020e63549c766fd80000000b0420912b8000000010200004dd82aa45b8be2000000025900007df8f2e000000011f0efe000000085706ea3c003e458381745f8800074e887e00000000000d3273a00005b780007fa208800000002951aaa146000000008300d08000311800060591e065c8b2a730141e5731a8e32c000000009107d680000548000248897e60216ea298200a5c7830e0fb8e28062937c1f50cb26da9746666976466a05b400013ee0000fee0ee803e5b716a6128000066385805ba0e7e348111c298800000008c04341a045588b687f28d98000184400000000001ff063b00001ae0000361974e3f0a0380000ef40000d5a0000de00000a0e1ff000022e00000001d5015580000a980000000000000000000000005498862000169e80380006b508ec35b0986000000000000003d501862c800000f4000000000000000000789937a85f0000000000000016146e215bc0b30b64000000028f1c962b8021c19e80000000000000000005c007019d00007e400000000d8c000115e000040c84f084646417280a104b03d60f12315800000000000000fca51600000000abc09980007501d2800000007be101400007821b980000001daa1179fd66189ac000015d8526871e00005440000000000081600017947e9a18000000006180c0a00018ae55c0b0844a9a020349d0a55608d629f8db26600eba66c85fe0001e0034e21506fc1acc1ac8218610194874c908235e216e1b10e2a08e0c427691eee53d937228e81b66939ab20b70d9c11c000000018b434e80000000000000000013600000c80db4000115608d889e00000003a90000563028a008825e00000000000d5400000007fb0000000194c81d16942f698480001fd200000007339b3600000000001d7e69517b60e2800075a10546859ed82aa00000001e384bb800000019560000232292163c41208a000000007ff931a3cc800068a9f8280183222e31ade73f8766717945e70a1c1813a034818482da0000bbe81c8c202f700004569caa57700000948602570834400000000000d763b207200001bae00017662380a081e71be80000230000119267500005ac800000018966ea0000200942c5f401bc06000000000000831915000004205b48ba00001f2227e0c126ef1c322d486d800000000000f6e0000000000022e62e8000292909c00001d478700100000000000000000000000
  | 36 => 0x4111c2279e1f3075084bc608122265f052c00000000001b5c000000000000003ca0b4a083800000021460001d4803a952c64800004bd0c1e0001be60639152000000060d1c46000000000000000001e1818c0ede00007de59405ac787800000015b26a10b7213c981200000b25bb81a655499ca4cd1b7a5ea8b226499ce209b044a2809b3c1299462104031a22f04944ed1eda79e9c5000006763d000000001a140a888ba63297c611e08ea0429b7c01d00001b900004df81d007b975254500006ba04c87ee0f5c2a89e2213b8e5c830862839092802fa8e0c0df8c0260c977c53f8b4443980003ce14106a300002dd000030b89e23aa800000019f6576832a6f8a13800000003f581ea0000bf22611eba00017c000004d46d500000001fa05610850508134836b1d966740e4407d17ec3af9db235e9efe32916e40e9142637f918858c1f1668c1f2c1239b2418d80007418c264bc02a441c0cf22ac8e20000168e44680847c68000000147a00007e63e61bf405d80000001c8a2850000000000000000000000000000016a42d8dfc7b58e8c6141aa88449d4454a92f80000000000000024b0000000000058103c485000002de80000001114000000000016ec2930000000201c437182e29002bc12a8e9241d99500b5080042f8f92688998412415d2000207a5f7192e0000ba8000186e531a0f86af95e600000007a913ca1f096360000000000000014100005a2000049d000000015e00001c4c17f00000001ec427717487e180a223f9110387975622b800000007682f402683f800000308fa20000a9600010ae35015fa5c000000000c3c5ea17b2761903e7ec94e05cf8a285e4214e5a1800000000000ef108c7040000000000000000002c2800000006dc77a1b566b0800000015327db90de00000001e99ea84cf95207251b5202001324a9150c3111d8028c0aae3811c0e62e0b8661d091800015d631700000001a5c13e012a7188000000000016890a2573a15224986de00016a207d80000e093e222a0e3630e931221a138a000000078680002df86fa00012427f095d400000005478eb62b91b105591b9454a07840e000000000cec000000000000007ec0dd600000002e90e7645f060e837964683400007550000198000000000007e600001a005c40000000000000077e00000ec09160001ff617b837426a000000012ca36c00000000bf4659a032029199c3bc879e0fe04d0000000056214960f4913e5c682e000000004ba2132000000000000004f1800000017f8000000000000001928d180b9800084a80003b5000000000c6000000030a1c360000000000098083b88da4e804184ab9a8a1ce971854f000031514380000000000000000000000000b420001928000000024d000031a05a414007183bf00008561f7a000120082e00000000
  | 37 => 0x1136000156e0b4094247209060000000000000026280000000000277800000000006c995c800000006fb8000000126842e09f60001d780001e520390000000000000000000000000000043000002d60000d8a000041e4ab00000000c18131003263b800000002804b091be389800007a1e4a000013a11a870a71613da00000560000000000000007716760000000000121c0001a5005e20942a49b9c84d0cfe78d9224000000000011b200000007150000000000064511b80001cea7008b8a2f5193e00000001a4000056e952e40181da1640000116000056b96c000012447a6839a60291061bf20fa71820f02c1889611c865c00004b2000000060f9e20000084826f0000000000000015480001b9e00000006e00af62998000395196a02b000000000004b380000000f223e7000058d00007b09afa000000000009305999fc63389f466321506458210c44e9e1400004f600020b647c949c0000c4e03998fc31d800070205be777015e49a800000020dc02995744c400000a0843232007c6231000077f000000000001828abe5fd800078e80ba5910000000000000000008198c10157987e5cf0de470f016e4b21370263a1785f28000000143a521800082780001369682252099e74914f8000087000000006c68b463890000000094e0000dce000074a00013a20bfa05c1aa8000000000036684165fc000068980006a08afc000000024782943bd800048a1cb87cb8dba0e79da0000073206a80002b184fa0008f8000000000000000000000065b8b1e00016a83b280000c19cd261d8df80de945018702562ab06461308e3421d1a3a15e0f765678cb45d8982a2d892385039d0249d9bd81e60ab67071ada601924a38c89aa1d81ccc0001c6c00007f80000000000000052c8000000000041a097c6ef87da7af03a26f41aca0001d9400000000001b92000000000015de00000000000b1a00016ce31c10c809c8c4000019a436480000000000000000000000000000000000000000004b800011f600000005e90fa059a800075f0000000148c77a9f5c0001cb0452000055f80003d48d7032f00006151fa200000003e7811c24490364b78e8400020083f7000004800000001a367c98000000195e1df800000009580ac8f88417800000000000000bb27a48000000192454591a400019dc80d051e6f0000000016ac2c41774671134400000000001f4e60d8dfa0001c2c7620ea63c1000055400007ea88ee00000000000000000000079fa0be01300006ce0d58000000014a00007a50000000000029e8000000103006fa022000065e000000000000000001dba21318e02a387e80001cf60001fce51580fe000140000000000000d303d200002ac000001e94ac0f78ae246f1cd46a58c0c30c90fe2d680001b5800000000002e01cec000089c000060c
  | 38 => 0xa4e50c1c046853406402de0808b840888b3000019f000000003311174085044000019d6000056800007760000e9a0001a3c00010ee0dd800000000000000000000000000000005e388fa7e200004728000000000000000004d300000001f3400000000b280004ef135a000118e000000072a1ebe0d18bcc00000001fb8000000200c69d0000000105227082b81988c3e1f700003c50000386a050000051a0000000000000000000f62609ffa287000085680006ca82fc795147656401840001ba4070865800005886348e462b2800049980000001a5878d0e523c58a2e0000000000097221b0f6068280000000d9e719105c2be80000000000000000049880001ab97767ae000000001b000018d80001c5600002a84aa0a6c000000000000005f389325010ad6546817c1ef91ec181950e0e20faa4ec15005190c506f100000000f5e56880007148000000000000000000001fc00001360712217619004741e488ac2a78194000022c000192c562893a0000000413000032d9e760001df61b20000000000000008944e9020a2fc0000000000000015b6000000023c000078909be00012340021e443b0185200000000000f6400000000001e0600000004660fb01d181f01e3894a3b4100030d02448578838511888e75d800000000004e31772000000000000000001b12428000037b128c00008d42c6210e48b800083b11c400015f6318010869a1ffc0000be018b00000001f78624993400000000001c146b619de194182465705da000000027f0bae1b8802645892f244808c800000000000000000087839b00007560b824d48c7e2d4191625700001d5836a000165e00021542ff0f940000d6400006da2c30c0e048988400000006a99744000000000000000001fae0000000000000000000004741176662000054f849677d18e65d794e87358e0a796819225106960ad9c308310ff851b14c017619a62a910c07d813e0000145400000003c3000052e000000008aa02d994e6fc900a0001b827df00006000e78000000000016f20169e96112085e5da96e263a8000000000000005540000000000000009e000002400004ac00000dc80000001ede00000000001e2e1c38000000000036aa10809c0000000191c00000000000fbc29ba14a00000000000000644800008200006c88f6a7f613c80000000773000010e000000000000001d0e000000000017806c21b4200002c63ed14de627190475d0f243ae04344349a1a00003d67fa9e5c000000000009c4234022821b930a78288443d406980f50b7c31487300001c166dc1226751830c000000016c800011900fc399845000018285f787ce0000c1463e9c8600020aa76101b40000000000000071084f000000000000000000191e000111e66a9ce412187bc000018218580004ee11c004e1282000
  | 39 => 0x18642d316f03ff0cd81598c243e118e85291a942ad19784528000339800034710ec7da00000001346000069e10380006f1800000000002a3144032e000083a89762b4816800006684390000000000000000000000cf81c41c84000000000000001a20000734161600000000001bb03ee99640000e1c00000007711e0e6170000000000044f00001b180000000000535000000000003ea0cdc194800035d175815380004da80003db00000001dec000180e2721eca0001c8c6c099900001d3619f0000000000000000000001e6414280dc00000000000cce0001cda0000000436000078a81a40001d2a00008b25ab97146bd000000000005fc80006f28582000000033f00002f9901a00000000f380000002044646800031c8000033000000010ea2759fa8000000000004fe15b00000fc800005b134e72611d80001f3a39913f40eb8092748899a65b0000170800016999423b70000526000007e1a986bc06106df85126ea99cc7db06a232484b63330b6c68b02860950f1a0001c3e000000000016be3ba082010e800062800000000000000000059c80007d5932e7d28000000000000018022d2000000014c858e01de00008ce5c40000811843600013c4145827674e000000014e2000138e7b89e906a90ca863380002879a245359a5675a8d244219dc031781666a2178a3a1906a2fb90ba81c10ca2ef004048610fc7e780bc1730f8c2d00ec42e40000700000000020b466e811600007c049401f24079aec000000011f800000000000000000000000052d8000000000021d800011a16d60531396592117018b9fdc2cd151c40e1cd80000560050912c0ce00001ad87ca29100000000fde53300004b692107bf04b4684000063f80007661ed40001dfe0358ada000171200000000001ce015b8000000201e84180000000f067199e1200000001638940758117a6cba08c44287a21d000006d980006f814344100bf
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x14314940d23711c14314940c28529c261d0940c24529c660d0940a2481590524c940d20525c2511054092687d495110540d0473d495110540a2a80d90528c540a2586148410c540d0573148410c540a9183105600c540e2052105600c540e0953108604c840aa181d906250040a2682d906155330a24815526290f30a2682d506150f30a14815526390b30a3084545600c730a24815506250330a2681d906255230a24825506150e30a28825526090630a90844c5600c630a24825526190230a2681d50625023091487551310c430d0474549310c430a1683d506150f20a288458a60d4e20c14641cd514c620c15735846115120c28541c16290d20a2b87150604c920a2987150604c920e20549c4604c920ca1745c4604c920e20545c4604c920c28541c162cc520d08541c132cc120a248158c6255020a288058c6255020c28629c26155020c24629c66055020c49535c26290c20e09535096010820b04815d15310820b08805d15310820925851c54310820c25651c54310820d05531c54310820e0a5454d6010820e095454d6010820e0a8454d6010820e098454d6010820e0953d0d6010820e095350d6010820aa08150d6010820d41535c04294420d21545c04254420d41535c04254420d21425c04254420d09535c04290420e095310a6090420c49535c06250420c29655c04210420d09535c04210420d09535c04290020c257510a6190020e055310a6190020aa18010a6190020c0e7654f4250020c0c7454d628c020a0c869515348020a0c865515348020a0e849915348020e09801915348020b09841c15348020e08641c15348020b41811c15348020e046454e5148020a24865515148020e046454d5148020e086454e4048020ca0645c64048020d41535c64048020c487654d4048020e086454f30480208a9871903048020c29751903048020ca0645c430480208a8865d332480208aa86dd12148020a2880588625521091487551310c610928875512008210c887458d2008210e095458d2008210a14835506150d10a24825506150d10c147414d610c910d10535c043105108d1831c16210510914835d44210510aa0805884210510ca1625c04210510a1684990534c510a1787190534c510a1587190534c510e04649c8534c510d05745c8534c510e04645c8534c510d11745c0534c510e10645c0534c510d41725c0534c510c24751913248510c147414d61cc110d107414d318c110c50655cc414c110c30651d1314c110cc0764c9214c110b40854c9214c110d80744c9214c110c887458d2008110a2884548604c810a2681d506250010a2a80d506250010a0d83150625001082c875915208010c0c7458d5208010b11831514044010b21821514044010d20541c94044010b20845482044010d21745482044010d41735482044010
  | 1 => 0x24b8005fa5424286eae13cbb070d0d424000000000390fc62323437000a34415586ac600f4004c609a562014d2194e052798026004a1b87c17259d80039118b000596b14442d750079388b69369aade0c2dda0c604889187900000004d1e0d80026328016400060d41e5005040546b001112ecb331e0568d1706c009b2320000003e0016a002098d9200488019cb900000b0640a0dc00384e9e800aa00000b4840000000006a184ac00580019e1c002bd4885490003e026c10c00ba00138ae004836400d10ab3544a16636c00060e94880be239cc323a5999c1a20568ec222922950fa4a41264bed355858e270240b502c50010984c76421c4ebc6202d6ca50414c00a9021bcfeae5a1dcea6c12af4da832e80126034c01cc4a82f0685e74651ec668f45004000085406000101c0009000003404010041000028480e00008741202008580005008181401098240e02290003215010040003000040e042f0003a030d09c000304834320509864000c00000000b07800060892681dd16094a43924825d26014543c51735806014543c61725806014543a8582d906150c43aa08058b6150c428a5879886150c42c85631c54390842a148358461553328c9801cd6110932a31801506150c32b0581151434c832b0980151434c832d04541c5434c832a268294c6150f41c16631c54394b418a5879886190c41ca2625c06190c4190d831c152108418b1801cd6110841a2880594424c841984835c4424c841d05535c4424c841c84635ca4350441c29625c06215131a268298c615503183487551610c831c84744c9610c831e05544c9610c831e05635494110431925859ca4310431c25659ca4310431c85639ca4310431e055458d5210431c15659ce4210431c157558c4210431c84645ca434c431a2486551524c43189587193324c431d12545cc4154031d11545cc4154031d41739484154031d41735484154031930879513154031930875513154031d20749493154031d20745493154031951831c54254031930845c43254031d41325c43254031d11735044154031b10835904154031b20825904154031d12645cc4154031d11645cc41540319318790c4154031d117390c4154031b228290c4154031b12839084154031d11739084154031d11731084154031d11831d13154031d107490d3154031b418290d3154031b1184cc93154031d1074cc93154031d10744c93154031a1683d506150f2191687d51310c521a268294c6150f40c16631c54394b40a9183105600c740b0583148429464092682dd16394640a2686d484254640b20805084254640c14641cd514c640a5183945600c640a24825d46150d40d04531c543d4940d07531c54314940924815d26314940c45635c46314940c49635c0631494092a809c74314940926819c34314940d2071dc
  | 2 => 0x224609f3f298b696471
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x28c8800000a0206940aed2488c426000db0580004b1e4aa73ae0060638000108224300412a03202a0e2a1a6419460640835c4424c841a024baa8992c2190638058558e7290c410c720108992e2192a018d40249645cc4154031c80b9d0521882a80639007460a434c5500c6223303a66498aa018e0161973148410c540d00c18a420ac018a81421971517118132482c0122c22a6b0084104886548150d6010820d00a9902a1ac021041821756004298640083402a6c008530c8010482660641c15348020d0032302382a690041c006454d71901200828112eaa2c690041084a064c805884210510a02cb8c8b90a698a21411971917014d31443800c8b92e029a62886101d8854c9214c110c80428e8992429822150193150725011004224130ba2a41022008640211735482044010
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1844
  | 5 => 9193
  | 4 => 4295
  | 3 => 223
  | 2 => 30
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
  | 7 => packedAt gbK7 (718+((h/13+packedAt gbK7 (640+(h % 13)*6) 6) % 49)*7) 7
  | 6 => packedAt gbK6 (57156+((h/614+packedAt gbK6 (49788+(h % 614)*12) 12) % 2434)*12) 12
  | 5 => packedAt gbK5 (395294+((h/3064+packedAt gbK5 (349334+(h % 3064)*15) 15) % 26008)*15) 15
  | 4 => packedAt gbK4 (229058+((h/1431+packedAt gbK4 (210455+(h % 1431)*13) 13) % 6860)*14) 14
  | 3 => packedAt gbK3 (14046+((h/74+packedAt gbK3 (13380+(h % 74)*9) 9) % 268)*9) 9
  | 2 => packedAt gbK2 (2190+((h/10+packedAt gbK2 (2130+(h % 10)*6) 6) % 40)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfe0fffc1ffe3ff83c78ff1ff1f81fff831f33f
  | 1 => 0x1ff03ffe07fc7c7c07f1fe3fe3fe0e00ce7dcc
  | 2 => 0x1fffc3fff8007ffff801ffc7fc000fff0f8e0f
  | 3 => 0xe00003ffffff807ffffe0007fffff007f00ff0
  | 4 => 0xfffffc000000007ffffffff800000007fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x42a0804451041000818250490484a29010b115
  | 1 => 0x4425888c3240a0940290b213212c243046554c
  | 2 => 0x88431910a0c9482d48012486481849630b0e0a
  | 3 => 0x814a22210480094a5424000492514045a00aa0
  | 4 => 0x118c3039c7127273a749c92000618186fde000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfee8eea0fee8eea0fee8eea0fee8eea0fee8eea0fee8eea0fee8eea0fee8eea0fee8eea0fee8eea0fee8eea0fee8eea0fee8eea0fee8eea0fee8eea0fee8eea0, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12879
namespace PEqualNP.Outside.L_meta_12879
open PEqualNP.Outside.L_meta_12879.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 30 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_192 : Interval gbAtlas 3 192 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 223 := (concat bgb_3_0 (concat bgb_3_96 bgb_3_192))
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
theorem bgb_4_4224 : Interval gbAtlas 4 4224 71 := block_range (n:=71) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 4295 := (concat (concat (concat (concat (concat bgb_4_0 bgb_4_96) (concat bgb_4_192 (concat bgb_4_288 bgb_4_384))) (concat (concat bgb_4_480 (concat bgb_4_576 bgb_4_672)) (concat bgb_4_768 (concat bgb_4_864 bgb_4_960)))) (concat (concat (concat bgb_4_1056 bgb_4_1152) (concat bgb_4_1248 (concat bgb_4_1344 bgb_4_1440))) (concat (concat bgb_4_1536 (concat bgb_4_1632 bgb_4_1728)) (concat bgb_4_1824 (concat bgb_4_1920 bgb_4_2016))))) (concat (concat (concat (concat bgb_4_2112 bgb_4_2208) (concat bgb_4_2304 (concat bgb_4_2400 bgb_4_2496))) (concat (concat bgb_4_2592 (concat bgb_4_2688 bgb_4_2784)) (concat bgb_4_2880 (concat bgb_4_2976 bgb_4_3072)))) (concat (concat (concat bgb_4_3168 (concat bgb_4_3264 bgb_4_3360)) (concat bgb_4_3456 (concat bgb_4_3552 bgb_4_3648))) (concat (concat bgb_4_3744 (concat bgb_4_3840 bgb_4_3936)) (concat bgb_4_4032 (concat bgb_4_4128 bgb_4_4224))))))
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
theorem bgb_5_9120 : Interval gbAtlas 5 9120 73 := block_range (n:=73) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 9193 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat bgb_5_288 (concat bgb_5_384 bgb_5_480))) (concat (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)) (concat bgb_5_864 (concat bgb_5_960 bgb_5_1056)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1248 bgb_5_1344)) (concat bgb_5_1440 (concat bgb_5_1536 bgb_5_1632))) (concat (concat bgb_5_1728 (concat bgb_5_1824 bgb_5_1920)) (concat bgb_5_2016 (concat bgb_5_2112 bgb_5_2208))))) (concat (concat (concat (concat bgb_5_2304 (concat bgb_5_2400 bgb_5_2496)) (concat bgb_5_2592 (concat bgb_5_2688 bgb_5_2784))) (concat (concat bgb_5_2880 (concat bgb_5_2976 bgb_5_3072)) (concat bgb_5_3168 (concat bgb_5_3264 bgb_5_3360)))) (concat (concat (concat bgb_5_3456 (concat bgb_5_3552 bgb_5_3648)) (concat bgb_5_3744 (concat bgb_5_3840 bgb_5_3936))) (concat (concat bgb_5_4032 (concat bgb_5_4128 bgb_5_4224)) (concat bgb_5_4320 (concat bgb_5_4416 bgb_5_4512)))))) (concat (concat (concat (concat (concat bgb_5_4608 (concat bgb_5_4704 bgb_5_4800)) (concat bgb_5_4896 (concat bgb_5_4992 bgb_5_5088))) (concat (concat bgb_5_5184 (concat bgb_5_5280 bgb_5_5376)) (concat bgb_5_5472 (concat bgb_5_5568 bgb_5_5664)))) (concat (concat (concat bgb_5_5760 (concat bgb_5_5856 bgb_5_5952)) (concat bgb_5_6048 (concat bgb_5_6144 bgb_5_6240))) (concat (concat bgb_5_6336 (concat bgb_5_6432 bgb_5_6528)) (concat bgb_5_6624 (concat bgb_5_6720 bgb_5_6816))))) (concat (concat (concat (concat bgb_5_6912 (concat bgb_5_7008 bgb_5_7104)) (concat bgb_5_7200 (concat bgb_5_7296 bgb_5_7392))) (concat (concat bgb_5_7488 (concat bgb_5_7584 bgb_5_7680)) (concat bgb_5_7776 (concat bgb_5_7872 bgb_5_7968)))) (concat (concat (concat bgb_5_8064 (concat bgb_5_8160 bgb_5_8256)) (concat bgb_5_8352 (concat bgb_5_8448 bgb_5_8544))) (concat (concat bgb_5_8640 (concat bgb_5_8736 bgb_5_8832)) (concat bgb_5_8928 (concat bgb_5_9024 bgb_5_9120)))))))
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
theorem bgb_6_1824 : Interval gbAtlas 6 1824 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1844 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 bgb_6_576) (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)))) (concat (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344))) (concat (concat bgb_6_1440 bgb_6_1536) (concat bgb_6_1632 (concat bgb_6_1728 bgb_6_1824)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 40 := block_range (n:=40) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 40 := bgb_7_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 5 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfee8eea0e8e8a0a0fee8eea0e8e8a0a0fee8eea0e8e8a0a0fee8eea0e8e8a0a0fee8eea0e8e8a0a0fee8eea0e8e8a0a0fee8eea0e8e8a0a0fee8eea0e8e8a0a0
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,9,41)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,9,41)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276676840 * 2 ^ 32 + 4003504288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12879.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.and,[0,1]⟩,⟨.or,[0,1]⟩,⟨.or,[2,7]⟩,⟨.and,[0,2]⟩,⟨.or,[6,10]⟩,⟨.and,[5,9]⟩,⟨.or,[8,12]⟩,⟨.and,[1,12]⟩,⟨.or,[11,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 4003504288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 4003504288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12879

open PEqualNP.Outside.L_meta_12879 in
theorem PEqualNP.Outside.L_meta_12879 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 4003504288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 4003504288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
