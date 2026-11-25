import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12911.Model
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


end PEqualNP.Outside.L_meta_12911.Model

namespace PEqualNP.Outside.L_meta_12911
open PEqualNP.Outside.L_meta_12911.Model
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

end PEqualNP.Outside.L_meta_12911

namespace PEqualNP.Outside.L_meta_12911
open PEqualNP.Outside.L_meta_12911.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841fc31083fe42107f88420fe90841fc21082fca0107fd0020ff20041fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887f90710fb20e21fd41c43ea83887f10710ff98e21fe31c43ec63887f4c710fa98e21fc31c43fe43887f88710fb10e21fd21c43ea43887f08710ffa0621fe40c43fa81887f10310ff98621fe30c43fa61887f0c310ff90621fe20c43fa41887f08310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff99421fe32843fa65087f0ca10bea8c21ff41843fc83087f50610fe20c21ff31843fc63087f4c610fe18c21ff21843fc43087f48610fe10c217e50843fe81087f90210fea0421fc40843fe61087f8c210fe98421fc30843fe41087f88210fe90421fc20843fe21087dc4210fd88421ff54442fea8887f95110bf2a221fd54442faa8887f15110be2a221ff53442fea6887f94d10bf29a21fd53442faa6887f14d10be29a21ff43443fc86887f50d10fe21a21ff52442fea4887f94910bf29221fd52442faa4887f14910be29221ff42443fc84887f50910fe21221ff32443fc64887f4c910fe19221ff41443fc82887d90510fea0a21f541443f882887fcc510ff18a21f631443fa62887d4c510fe18a21ff21443fc42887d88510fe90a21f521443f842887fd0110ff20221fd40443f880887fcc110ff18221fd30443f860887fc8110ff10221fd20443f840887fc4110fd88221fe10443ec20887fd5010bfaa021fe54042fca8086f950109f2a021fd54042faa8086f550109eaa021fc54042f8a8087fd4c10bfa9821fe53042fca6087794c10af29821fd53042faa6087754c10aea9821fc53042f8a6087fd0c10ff21821fd43043f886087fd4810bfa9021fe52042fca4087b94810b729021fd52042faa4087b54810b6a9021fc52042f8a4087fd0810ff21021fd42043f884087fcc810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xe540c2fca8186f950309f2a061fd540c2faa8186f550309eaa061fc540c2f8a8185f94c30ffa1861fe430c3fa86187f10c30ffa9061fe520c2fca4187b94830b729061fd520c2faa4187b54830b6a9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830fe99061fc320c3fea2187f94430bf28861f6510c2eca2187f54430bea8861f5510c2eaa2187f14430ffa0861fe410c3fa82187f10430ff98861fe310c3fa62187f0c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7905f14f20ffa1e41fe43c83fa87907f10f20ffa1641fe42c83dc85907f50b20f6a1641fc42c83fe65907f8cb20f719641fd32c83da65907f0cb20ffa8e41fe51c82fca3907f54720bea8e41fc51c83fe83907f90720fea0e41fc41c83fe63907f8c720fe98e41fc31c83fe43907bc8720ff10e41fd21c83da43907f08720ffa0641fe40c83fa81907f10320ff98641fe30c83fa61907f0c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ffa1c41fe43883fa87107f10e20bea9441ff42883fc85107f50a20fe21441ff32883fc65107f4ca20fe19441ff51883fca3105f94620fea8c417d51883f8a3107fd0620ff20c41fd41883f883107fcc620ff18c41fd31883f863107fc8620ff10c41fd21883f843105f94220ffa0441fe40883fa81107f10220ff98441fe30883fa61107f0c220ff90441ef20883f641107fd5120bfaa241fe54482fca8907f55120beaa241fc54482f8a8907fd4d20bfa9a41fe53482fca6907f54d20bea9a41fc53482f8a6907fd0d20ff21a41fd43483f886907fd0920ff21241ee42483fa84907b50920fe21241ff32483fc64907b8c920fe99241ed32483f864907fd4520bfa8a41fe51483faa2907f14520be28a41ff41483fc82907f50520fe20a41ff31483fc62907f4c520fe18a41ff21483de42907f88520fe90a41ed21483f842907fd0120ff20241fd40483f880907fcc120ff18241fd30483f860907fc8120fd90241fe20483dc40907fd5020bfaa041fe54082fca8106f950209f2a041fd54082faa8106f550209eaa041fc54082f8a8107fd4c20bfa9841fe53082fca6107794c20af29841fd53082faa6107754c20aea9841fc53082f8a6107fd0c20ff21841fd43083f886105f94820ffa1041fe42083fa84107f10820ff99041fe32083fa64107f0c820ffa8841fe51082fca2107d94420bb28841fd51082faa2107d54420baa8841fc51083fe82107f90420fea0841fc41083fe62107f8c420fe98
  | 2 => 0x3fca3205f94640fea8c817d51903f8a3207fd0640ff20c81fd41903f883207fcc640ff18c81fd31903f863207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681207fd4d40bfa9a81fe53503faa6a07f14d40be29a81ff435037e86a07f90d40fea1a81bd43503f886a07fd4940bfa9281fe52503faa4a07f14940be29281ff425037e84a07f90940fea1281bd42503f884a07fcc940ff19281fd32503f864a07fd4540bfa8a81fe51503faa2a07f14540be28a81ff415037e82a07f90540fea0a81bd41503f882a07fcc540ff18a81fd31503f862a07fc8540ff10a81fd21503f842a07fd0140fda0281fe405037c80a05f95040ffa9881fe53102fca6207794c40af29881fd53102faa6207754c40aea9881fc53103fe86207f90c40fea1881fc43103fea4207f94840bf29081ee52102dca4207f54840bea9081ed52102daa4207f14840ffa1081fe42103fa84207f10840ff99081fe32103fa64207f0c840ffa8881fe51102fca2207d94440bb28881fd51102faa2207d54440baa8881fc51103fe82207f90440fea0881fc41103fe62207f8c440fe98881fc31103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9985fd5330ff2a6617e54cc3faa9985f55330fe2a6617c54cc3fe87987f90f30ef21e61fd43cc3ba87987f10f30ffa9661fe52cc2fca5987f54b30bea9661fc52cc3fe85987f90b30fea1661fc42cc3fe659877ccb30ff19661fd32cc3ba65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fea0e61fc41cc3fe639877cc730ff18e61fd31cc3ba63987f0c730ff90e61fe21cc3fa43987f08730ffa0661fe40cc3fa81987f10330ffaa4617f548c3fca9185f95230feaa4617d548c3f8a9185f15230bea9c61ff438c3fc87187f50e30fe21c61ff528c3fca5185f94a30fea94617d528c3f8a5187fd0a30ff21461fd428c3f885187fcca30ff19461fd328c3f865187fd4630ff28c617e518c3faa3185f54630fe28c61ff418c3fc83187f50630fe20c61ff318c3fc63187f4c630fe18c61ff218c3fc43187f48630fe10c617e508c3fe81187f90230fea0461fc408c3fe611877cc230fd98461ff544c2fea8987f95130bf2a261fd544c2faa8987f15130be2a261ff434c3fc86987790d30fea1a61dd434c3f886987fd4930bfa9261fe524c3faa4987f14930be29261ff424c3fc84987f50930fe21261ff324c3be64987f8c930fe99261dd324c3f864987fd4530bfa8a61fe514c3faa2987f14530be28a61ff414c3fc82987f50530fe20a61ff314c3be62987f8c530fe98a61dd314c3f862987fc8530ff10a61fd214c3f842987fd0130ff20261fd404c3f880987fcc130fd98261fe304c3bc60987fd5030bfaa061f
  | 3 => 0xa818ff55031beaa063fc540c6f8a818df94c31ffa1863fe430c7fa8618ff10c31ffa9063fe520c6fca418ff54831bea9063fc520c7fe8418ff90831fea1063fc420c7fe6418ff8c831fe99063fc320c6fca218ffd0431ff20863fd410c7f88218ffcc431ef98863fe310c7ec6218ff4c431ee98863f5310c7aa6218ffd4031ff280637e500c7faa018df54031fe28063ff54c86fea990ff95321bf2a643fd54c86faa990ff15321be2a643ff53c86fea790ff94f21bf29e43fd53c86faa790ff14f21be29e43ff43c87fc8790ff50f21fe21e43ff42c87fc8590ff50b21fe21643ff32c87fc6590ff4cb21fe19643ff41c87fc8390ff50721fe20e43ff31c87fc6390ff4c721fe18e43ff50c87fca190df94321fea86437d50c87f8a190ffd5221bfaa443fe54886fca910ff55221beaa443fc54886f8a910ffd4e21bfa9c43fe53886fca710ff54e21bea9c43fc53886f8a710ffd0e21ff21c43fd43887f88710df54a21ffa1443fe42887fa8510ff10a21ff99443fe32887fa6510ff0ca21bf28c43ff41887fc8310ff50621fe20c43ff31887fc6310ff4c621fe18c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fea690dfd4d21ff29a437e53487faa690df54d21fe29a437c53487fe8690ff90d21fea1a43fc43487fe8490ff90921fea1243fc42487fe6490ff8c921fe99243fc32487fe8290ff90521fea0a43fc41487fe6290ff8c521fe98a43fc31487fe4290fdc8521ff10a43ee21487fea090dfd4121ff28243fd50487f8a090df14121ffaa0437f54087fca810df95021feaa0437d54087f8a810df15021ffa98437f53087fca610df94c21fea98437d53087f8a610df14c21ffa1843fe43087fa8610ff10c21bf29043ff42087fc8410ff50821fe21043ff32087fc6410ff4c821fe190437e51087fe8210ff90421fea0843fc41087fe6210ff8c421fe98843fc31087fe4210fbc8421ff10843f621087fa4210fb48421fa90843e521087fea010ff94021bf28043fd50086faa010ff14021ffa9e81fe53d02fca7a07f54f40bea9e81fc53d03fe87a06fd0f40ff21e81fd43d037a87a07f10f40ffa9681fe52d02fca5a07f54b40bea9681fc52d03fe85a06fd0b40ff21681fd42d037a85a07f10b40ff99681fe32d03fa65a07f0cb40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a06fd0740ff20e81fd41d037a83a07f10740ff98e81fe31d03fa63a07f0c740ff90e81fe21d03fa43a07f08740beaa481ff53903fca7205f94e40fea9c817d53903f8a7207fd0e40ff21c81fd43903f887207fd4a40ff294817e52903faa5205f54a40fe29481ff42903fc85207f50a40fe21481ff32903fc65207f4ca40fe19481ff519
  | 4 => 0x7fd4132bfa8265fe504cbfaa0997f14132be28265ff540cafea8197f95032bf2a065fd540cafaa8197f15032be2a0657e530cbfe86197f90c32fea1865fc430cafca4197fd0832ff21065fd420cbf884197fcc832ef99065fe320cbdc64197f4c832ee99065ed320cb9a64197fd4432ff288657e510cbfaa2195f54432fe28865ff500cbfca0195f94032fea80657d500cbf8a0197fd4f41ff29e837e53d07faa7a0df54f41fe29e83ff43d07fc87a0ff50f41fe21e83ff52d07fca5a0df94b41fea96837d52d07f8a5a0ffd0b41ff21683fd42d07f885a0ffccb41ff19683fd32d07f865a0ffd4341ff286837e50d07faa1a0df54341fe286837d54907fea720ff94e41bf29c83fd53906faa720ff14e41ffa1c83fe43907fa8720ff10e41ffa9483fe52906fca520ff54a41bea9483fc52907fe8520ff90a41fea1483fc42907fe6520ff8ca41fe99483fc32906fca320ffd0641dfa0c83f741907fea120ff94241bf28483fd50906faa120ff14241ffa9a837f53507fca6a0ff54d41fe29a837c53507fe86a0ff90d41fea1a83fc43507fea4a0dfd4941ff29283fd52507f8a4a0df14941ffa1283fe42507fa84a0ff10941ff99283fe32507fa64a0ff0c941ffa0a83f741507fc82a0ef90541ffa82837f50507fca0a0ff54141fe282837c50506fca820ffd4c41ff298837e53107faa620df54c41fe29883ff43107fc8620ff50c41fe21883ff52107fca420df94841fea90837d52107f8a420ffd0841ff21083fd42107f88420ffcc841ff19083fd32107f86420df94441ffa0883bf41107fc8220fd90441fea0883bd41107ea8220ed50441ffa8083fe50106fca020ff54041bea8083fc50107fea998dfd5331ff2a6637e54cc7faa998df55331fe2a6637c54cc7fe8798ff90f31fea1e63fc43cc7fea598ff94b31bf29663fd52cc6faa598ff14b31ffa1663fe42cc7fa8598ff10b31ff99663fe32cc7fa6598ff0cb31ffa0e63fe41cc7fa8398ff10731ffa8663fe50cc6fca198ff54331bea8663fc50cc7fea918dfd5231ff2a4637e548c7faa918df55231fe2a4637c548c6faa718ffd0e31ff21c63fd438c7f88718ffd4a31ff294637e528c7faa518df54a31fe29463ff428c7fc8518ff50a31fe21463ff328c7fc6518ff4ca31fe194637e518c7fe8318ff90631fea0c63fc418c7fe6318f7cc631fb98c63ff508c7fca118df94231fea84637d508c7f8a118ffd5131bfaa263fe544c6fca898ff55131beaa263fc544c6f8a898ffd0d31ff21a63fd434c7f88698ffd4931bfa9263fe524c7faa498ff14931be29263ff424c7fc8498ff50931fe21263ff324c7fc6498ff4c931fe19263ff414c7fc8298ff50531fe20a63ff314c7ee6298ff8c531ef18a63ff504c6fea098ff94131fea8263fc504c6f8a098ffd5031bfaa063fe540c6fc
  | 5 => 0x1c0040140240bc00401002009c00800800001400800c0ac0400dc00018800800000004800001818407c0080b40180280040000580040180040a80200700b3fea5a1ff94b43bf29687fd52d0efaa5a1ff14b43ffa8e87fe51d0efca3a1ff54743bea8e87fc51d0ffea1a1ff94343bf28687fd50d0efaa1a1ff14343beaa4877e5390ffe8721efd0e43efa1c87ff5290ffca521df94a43fea94877d5290ff8a521ffd4643ff28c877e5190ffaa321df54643fe28c87ff5090ffca121df94243fea84877d5090ff8a121ffd0d43efa1a87fe4350f7c86a1ffd4943bfa9287fe5250ffaa4a1ff14943be29287ff5150efea2a1ff94543fea8a87fc5150ef8a2a1ffd4143bfa8287fe5050ffaa0a1ff14143be282877e5410efca621ffd0c43dfa1887fe4310fbc8621ff50c43dea1887dd4310f3a8621ffd4843ff290877e5210ffaa421df54843fe29087ff5110ffca221df94443fea88877d5110ff8a221ffd4043ff280877e5010ffaa021df54043fe28087ff53d0bfca7a15f94f42fea9e857d53d0bf8a7a17fd0f42ff21e85fd43d0bf887a17fd4742ff28e857e51d0bfaa3a15f54742fe28e85ff50d0bfca1a15f94342fea86857d50d0bf8a1a15f55242ffa9c85fe5390afca7217f54e42bea9c85fc5390bfe87217f90e42fea1c85fc4390afca5217fd0a42dfa1485ef4290bfea3217f94642bf28c85fd5190afaa3217f14642ffa8485fe5090afca1217f54242bea8485fc5090bfea6a15fd4d42ff29a85fd5350bf8a6a15f14d42ffa1a85fe4350bfa86a17f10d42ffa1285ef4250bfc84a16f90942ffa8a857f5150bfca2a17f54542fe28a857c5150bfea0a15fd4142ff28285fd5050bf8a0a15f14142bf2a085ff5310bfca6215f94c42fea98857d5310bf8a6217fd0c42ff21885fd4310bf886215f94842ffa1085bf4210bfc84217b90842fea1085bd4210bda84216b50842ffa8885fe5110afca2217f54442bea8885fc5110bfea0217f94042bf28085fd5010afaa0217f14042ffaa6657f54ccbfca9995f95332feaa6657d54ccbf8a9995f15332ffa1e65fe43ccbfa87997f10f32ffa1665fe42ccbfa85997f10b32ffa8e65fe51ccafca3997f54732bea8e65fc51ccbfea1997f94332bf28665fd50ccafaa1997f14332ffaa4657f548cbfca9195f95232feaa4657d548cbf8a9195f15232bea9c65ff438cbfc87197f50e32fe21c657e528cbfe85197f90a32fea1465fc428cbfe651977cca32f799465ff518cbfca3195f94632fea8c657d518cbf8a3197fd4232ff284657e508cbfaa1195f54232fe28465ff544cafea8997f95132bf2a265fd544cafaa8997f15132be2a265ff434cbfc86997f50d32fe21a65ff424cbfc84997f50932fe21265ff324cbde64997f8c932ef19265ff514cafea2997f94532fea8a65fc514caf8a299
  | 6 => 0x9b501d99f3362279bdb6887c8f1350a172300c19d20deadb2c8a6e00822391fa200f881183f256018000077116321a5536e2528782f9a3a0000db3010240a90d12c380029a9edafb80030e233132878828167b6aaef2c4a67a2fa970cf10da088000000b02d71b7af30c6b138000002f0b590480d99ba300150a0717ba6db0cb1d9d7b0d06d31d07b09b22f232908b61850a26283a741b301682e3082aa8928000f48002ab2f6287094b30a840002c78050000001aa84a13397100ac04c00002804002402002802c00800403404c00805c0040000080000540040000680000140040000800040000740400080a805807401400005405c03801006801000405400c00c0ec01400800800002000001007800000406801800800c01c00c00802808c02804c0200040000000e800c00c00801000c00805001404400003404000401000801400803400402001001002000001400002808c01800003000800002802800001801c00803415000403c00400000409c00401800406000001000000800007004806c07000c02400404002800000c00000000000001c00801400000c00800000403800c00400c00001403003807c0a400000001c00001803000400400003401000400c00000805806401800c00c08c0380000000000080100080bc02c00c09800c00409c00006403404c0040b00000001d002c00000800002c05409c06400802000c00000002c0380080580e40100040980140280980040080080380680180100000340000f80000040040000c400803c0000f400c01005800004c01003000400002401000001000400c00418000000000800800002400c01400c00400801802002c02400000c0100500580b400002401c00801400c00c00805c01801800800400400800c09800c01c00000801c00000800000000802005800800007400400001c00805400c00805404408004401000000401c00401c0000200100000540b400000400001c02400009401402800002800000400000c0000140040a001403c04800007400000004c02c08808c02000001000003001400011c03800c01c00c0dc00000000400000004800000002400400400001400c00402004801800400c0b00a00ac0a803406400000c05801c00802403c00805801c00803000403007000c0640000681000080001200280c405802400400006800001802407000403001800800404002c01800803401c00004400805801005008c03802000000004400c00400002002001400801800000400001803800003c03002402407c0000000480140dc00800007402000800400001402000400c00405c03402400000c01c0e000401401400004005801000407004c00000008400801400003000c00401800000002c03403c00000000000400007000002c00000800000000400003400800000001c0
  | 7 => 0xb627ea4d9b70002a580018ba3411801a0d930a1700d2053962b4c80000031a0002a48308e61d100c80000021f1b28001319c000b00020f29622b200ae72ed1de9d0a09163234835332ae500026f148233b770e4a158d41d629690d0450a6b2f21eb373228e097294d0cd1c31080032731668e38002eba1ab7b85911f2e297583934204da6b0000f182b264800000053168aeab77aac10c9f080009117908380015309e9fc0000001eeaa78001b134308d8fd23918a00029b8688001c515618b229a0199386bb13058a06b4da9f03887e95a1b991bb1701ba8c9fab5c91406680000012f01c2daad6b179e6a5f331ac728692d9369f9a0e9e213f9830b98ebb6f0439c2abf35f8642728c30652db9d2a92b538c8851b701c79ec8e82f38c799226a0a0b61241b26a808aaad7a0e0d633fa4c9c185b1c903a897319119b51acc2168b4a8580bb25294990b6018735402f149aae0c594aa28a1b28110b80295c34c38187d9a116cb028d0a9c80e8acb569969190ce8e9821abb8ea97a969a400d72c833203e08aa5392706118195828f9ef954b4e89d9dd81f9db1e0838278a8821033da3f1559ec11aa97a8c00021814090e0000000000001bea1d15a84e9a529e30d80001925e000082ab7b0682c33b0000ec08a00001e1b6a4b8001bb00000000015180012033b8000b688fa1fb0c0001b20d53348002422bfb0b3048dc1b0a2213d91205296418cb0912c80007601c92a97d819ac9a8e33c93223e00000d0000000002f880032788236900003000018f98c339012284ab20f535daf2aacae080e1b892380013b991b108000000740000fb1bcad00fe9042b68001799c428a8921f700029c0b7b6b00028331c95901737c2e58002aa1091f48001033180f032e80026fad300030701034d101380b76804b1280000031b80027f2702778002a60000108003511d48002941931e52cf1c72c2a381c39e616c00022b97502d09ca2c1a908404f8e6a5faa12e7aec1570b5800184084a8d84ab03b2100003f8bd3140000002ed8003649e01e19133811f00818e5000311b7a80017f3738000002818b233c26600036527495696635600a075b343790ed04d02a88134e1ad1c8acb9e8246a8d29d221203074a622a511da7e1a331aaa81dc0e8a572e60001fc92f9e999a288800135000000000073a241c48f23709b39fbb628001468000b90b08000000790559760001fb00000000f9ff10a05a833b5e8042d103a00023714400009595ba5c9428000e40e110f28f2408c91d880014f8671cca4c0c72d81418a4907adc0699a82eb0000001860000af00000000000000f0a78f32410002e135b265a588000000908000002bc0000ec9d30a31460c82bc81889b9c6a0f9ef2e0323a6424726922280020b0a21260002ccb549ed0000001fa0002fda5a305165afc91c
  | 8 => 0x80a93a2138b11f8865b2f9230fe341a36afe9852ca81aa98b552639a4896a5b8002f00000d38000002ff0001d71df8001d824d00000023200023c0002080df23780032301380589992880036200027700018e0000000128443478b732a1a39b5a129ab0228d7aba2d59bc3528c483c06199898aa3190c03e8a814f05c8ce00099e16d08091c0fc88d36c80034bad880000032d15e89c0001de00012e0000f431636ea51346122a5d2b480008011eac6375000020a1b80016b00036c32b8000001aa2c014136097a04786f938139a610002590001cd8000000001501613400898001c2000000000000375927ac332712a000160800000000207b71211a188fa8b401f1d40078499d180009833d08933a2c10150a18000d48002ba8000000000990408000002e417eaa91af91b0b2a990d197e05617fb2210b3718f633883493892193e99bb580fa1550270000001fe2f813099f9da8ef800329800260800289a5485480000002a00024f0000b800008f032a7c195afb000008a50ad2aa304cadf800110b438cc8000000000a0357800085b4ab0992b8b180021c00000000005992d16ba0b9348098001911d99cf00000010000035708512b0068e2000200106a6e8001cb04b16f8da8f284011a00000d80013c8d023526aa098002e88002532e822a8429c586307311688309500032592419613b1ae194800000063b491f31e424f95f04307f95e0b500026d2698001e48001971622de824a959df22a11514700029b00000022900037b00006e07f1a400007e2580342b81822ad0df8001f80aea0100022829180013a89ab2c07d28908e300a4485519a943a141449ca03329315130400036324e8e02e21838320d334680016f214b5a04c3732e9a358582d5000000037800045ada36406789a00029219d16d9769b4b6b8000000000bb9293483499ac2520001401a19a2affb489900c381b0f3b1032da9d9299db8fc31220a98995d290a98157af48cb1330c40aa32e0000a88602c223f80001417437a24395891e35aac5af780018e8728d5a519eba0da2d36d2a72451880af8a12f58701802bb130115a48b4523e945b530000000932b880000038218580001e80014e1dd16e1c11be33688c316af6814a3dacf997a2c8002b711880003b3248003378568003668ae2cb19c03585bb5b8f08ab8002b60579600369bfa5416a2e3b40afa0c088c871022013107026964b0180024a1a6a8b05f1af311037186a178e90202e48ea19ca8014c0ff9542b9aceb4f0902860002650eb324318b5221093715284e28532893405e33a82b97086f24920c0001bd086b3986a959b84b6a077aad85a24403993d17ca2320a20d2faa828b61721cf89431c2d411d00018d8862a9b5d1208ff1889249138f71d037f04931b359a7f99d91725c27d81d0469fea191eb1cd1
  | 9 => 0xac1f380006a2d0a2eb42841000000257a6180000032b00000009f902ab59f1800205345aa881600017c2040e72f72599ce279904893a15048a738c10001893829baa39aee1928720e7a38a3d35c2bd16a80930b94d9a0939103b838edb67076a673698bc3781312eea9f80021a182aca225ae69b1b842abab122e12e8000001e70003020001c08da2d91782252f50919bb8ba029111383247844b680001c824aa66a0606c87aad39fd378a6ca93977000098b589fda021e28002ae800335a3b8bf8000dd00033835f0002dc9739718e5a2da20800000026000271000199329000224b501da18d2b4054153b1e07a21c9021a733f1478cb8060c9b19b662dd06213f20395b2160318a737f8ca2502b027086828ea68aa209f12686b2e19f28418000000001e5a7d3441e12482a404f1f12822f1b4b1809ffa270662ce12c0ee00030636fa7905d2b91f580382c83c8002b18a98000001d3acd00007c1681a5abdb8005c14303ba9ea1326c2cd8708000000000000bb3148113078288a536d9e3a3b2ec80004614b01780037427b8cdaf11060dbaea0e30dc823ab28f58be00c2458ab2a2afe2b3a87aaf0a38f7928326001b4f827887b0e91480021223a96914a0ada111a0060a753332fd27803db3510f9b834700025aa7226bac0b0f06d8000001099d6b748000798e19651b900032c8002b0a569422ef8000871f91998001220000310001f41211ee23c9f500036382ea428c62760000a40511adb2aa461d50000000000ad0a2b0314eb762f41c60719849cc16eb338c529a0c20233559b40158fd96731f27185f9a627a8000d289e1051cb88b9813202b514b80000010580013e1f7ad60000000bd8d8aa68bc9a9a99888b7e9dc9a22a18523312dd88b02fa7a367b7d80000005eb4a1878212fc0fb8880002df0000000f6ac6a55ad22b320499b205800000344800243137b7c8de0000000001e928a00017333e93c1451e7aa0aafb1e9358073058000001ce8b31118979953658001e883600010a80017485019404702dad48570000cfb410c29bf3158258f986e80000000017d0eeb7e0001639ab8000002f919e80000027c9ea2beb150dda1e25eb7d000328202abe1d5b0aac52a3a49978961a311ca8b389618f2759b0112b5e12594c86c1a79e315fb089a88b8b721d92c91f69c98ef2f2101a4e2682632de148952219a0c80000021da360000d80000001ea800001000230b798002951490e28f809d1f20298020002d98002c19251f622195ca2690e80000007508e8d695d80000007bae91100a5917a9119804ba768001ae8bf17b0c027b0628a6100842177ae3290372aa026280000030f8f900000000013625b0000000000001ac8be80031fa8b85db3e2600cc02503d0ba8ca86486925dad1a4b3302c432
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc210435d5308410db948210436d5208410f948421042fa6008410be580210427e64940109f592500427e63940109f58e500427e62940109f58a500427d61940109f597400433e54d0010cf553400435e53d0010d754f400436e52d0010db54b400427f65900109f596400433e5490010cf552400435e5390010d754e400436e5290010db54a40042f66190010bd586400427f6550010cf951400433d5450010d794d400435d5350010db949400436d52500109fd94400427e65100109f594400427c6510010cf950400433d5410010b798c40042dd6310010d794c400435d5310010bb98840042ed6210010db948400436d5210010bd98440042f561100109f597300433e54cc010cf553300435e53cc010d754f300436e52cc010db54b300427f658c0109f596300433e548c010cf552300435e538c010d754e300436e528c010db54a30042f6618c010bd586300427f654c010cf951300433d544c010d794d300435d534c010db949300436d524c0109fd94300427e650c0109f594300427c650c010af99030042bd640c010cf950300433d540c010d794c300435d530c010bb98830042ed620c010db948300436d520c010bd98430042f5610c0109f597200433e54c8010cf553200435e53c8010d754f200436e52c8010db54b200427f65880109f596200433e5488010cf552200435e5388010d754e200436e5288010db54a20042f66188010bd586200427f6548010cf951200433d5448010d794d200435d5348010db949200436d52480109fd94200427e65080109f594200427c6508010af99020042bd6408010cf950200433d5408010b798c20042dd6308010d794c200435d5308010db948200436d5208010bd98420042f56108010cf953100433d54c4010d794f100435d53c4010db94b100436d52c4010dd597100437754c4010ed953100437554c4010ed553100433554c4010ddd4f10043d653c4010dd54f10043d553c4010d554f100437752c4010f994b100437552c4010f954b100436552c4010cf952100433d5484010d794e100435d5384010db94a100436d5284010bd58610043765184010be596100437965840109e59610043ba5484010ee55210043da5384010f654e10043ea5284010fa54a10042f96184010de94610043f251840109fd95100433e5444010cf551100435e5344010d754d100436e5244010db54910042f76544010ddd9510042776544010ddd5110043b65444010dd55110043b55444010cd55110043775344010f594d10043755344010f554d10043555344010ddd4910043e65244010dd54910043e55244010d954910042f76044010dd94110042fb6544010ded95100427b6544010ee95110043b95444010f694d10043d95344010fa94910043e95244010bed8510043f36144010de94510043f25144010
  | 1 => 0x433e64148108f990520427d6414810cf590520423d64148109f98c520435e63148109798c520427d6314810d758c520425d63148109f988520436e62148109b988520427e6114810dd984520427661148109f980520437a60148109fd97420427e65d08109f597420427c65d0810cf953420433d54d0810d794f420435d53d0810db94b420436d52d08109fd96420427e65908109f596420427c6590810cf952420433d5490810d794e420435d5390810db94a420436d52908109fd95420427e65508109f595420427c6550810cf951420433d5450810d794d420435d5350810db949420436d5250810bdd8542042f461508109fd94420427e65108109f594420427c6510810cf950420433d5410810d794c420435d5310810db948420436d5210810eb508420427f65cc8109f997320427d65cc8109f197320433e54cc810cf553320435e53cc810d754f320436e52cc810db54b320427f658c8109f996320427d658c8109f196320433e548c810cf552320435e538c810d754e320436e528c810db54a320427f654c8109f995320427d654c8109f195320433e544c810cf551320435e534c810d754d320436e524c810db54932042f7614c810bd185320427f650c8109f994320427d650c8109f194320433e540c810cf550320435e530c810d754c320436e520c810db54832043cd320c8109f992510427d64944109f98e510427d63944109f98a510427d62944109f597410433e54d0410cf553410435e53d0410d754f410436e52d0410db54b410427f65904109f596410433e5490410cf552410435e5390410d754e410436e5290410db54a41043765190410be98241042f960904109fd95410433e5450410cf551410435e5350410d754d410436e5250410db549410437651504109fd94410427d6510410cf950410433d5410410d794c410435d5310410db948410436d5210410ed50441042fa6010410be580410427d65cc410cf953310433d54cc410d794f310435d53cc410db94b310436d52cc4109fd96310427d658c410cf952310433d548c410d794e310435d538c410db94a310436d528c410dd94631042fa608c410be582310427f654c410cf951310433d544c410d794d310435d534c410db949310436d524c410dd945310427f650c4109f594310433e540c410cf550310435e530c410d754c310436e520c410db54831043d5310c410be98031042f9600c4109f597210433e54c8410cf553210435e53c8410d754f210436e52c8410db54b210427f65884109f596210433e5488410cf552210435e5388410d754e210436e5288410db54a21043765188410be98221042f960884109fd95210433e5448410cf551210435e5348410d754d210436e5248410db549210437651484109fd94210427d6508410cf950210433d5408410d794
  | 2 => 0x6254c109f189530427f6154c109f585530427f6054c109f581530435f6554c10d7d51530435e5454c10e7951530431e5454c10d7551530439d5454c10c7551530435c5454c10d7d91530435e6454c10d7591530435c6454c10d7d89530435e6254c10d7589530435c6254c10d7985530435c6154c10d7981530435c6054c10d704153042be6414c10af590530433e5414c10cf55053042de6314c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530425e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109d984530427e6014c10de980530427f65d0c109f997430427d65d0c109f197430433e54d0c10cf553430435e53d0c10d754f430427f6590c109f996430427d6590c109f196430433e5490c10cf552430435e5390c10d754e430427f6550c109f995430427d6550c109f195430433e5450c10cf551430435e5350c10d754d43042f76150c10bd185430427f6510c109f994430427d6510c109f194430433e5410c10cf550430435e5310c10d754c430439d4310c10af99352042bd64d4810cf953520433d54d4810b798f52042dd63d4810d794f520435d53d48109f993520433e64d48108f993520427d64d4810cf593520423d64d48109f98f520435e63d48109798f520427d63d4810d758f520425d63d48109f987520437661d48109f983520437a60d48109f596520433e5494810cf552520435e5394810d754e520436f52948109f992520427d64948109f98e520427d63948109b596520436f5494810db95252043ae5494810cb952520436d5494810eb552520432d5494810db152520436f5394810db94e52043ce5394810d394e520436d5394810f354e520434d5394810db14e520436f6494810db992520436d6494810db192520436f6394810db98e520436d6394810db18e520436f4394810db90e520436d4394810db10e520436e6194810db186520436e6094810db182520433e5454810cf551520435e5354810d754d520427f64548109f191520427f63548109f18d520436f62548109fd85520427d61548109fd81520427d6054810dbd95520436f5454810db95152043ae5454810cb951520436d5454810eb551520432d5454810db151520436f5354810db94d52043ce5354810d394d520436d5354810f354d520434d5354810db14d520436f6454810db991520436d6454810db191520436f6354810db98d520436d6354810db18d520436f4354810db90d520436d4354810db10d520436e6154810db185520436e6054810db181520436c1054810af99052042bd6414810cf950520433d5414810b798c52042dd6314810d794c520435d5314810bb988520436d52148109f990520
  | 3 => 0x1109f595404427c6550110cfd51404433c5450110bdd8540442f46150110ed505404427e6510110b798c40442dd6310110bb98840442ed6210110bd98440442f561101109f997304435f53cc110d714f30442f661cc110bd58730443d531cc1109f996304427f654c1109f595304427c654c110d7d4d304435c534c110bdd8530442f4614c110f54c5304427e650c110af99030442bd640c110bb98830442ed620c110bd98430442f5610c1109f997204436f52c8110db14b20442f661c8110bd58720443e521c81109f996204427f65481109f595204427c6548110dbd49204436c5248110bdd8520442f46148110f9485204427e6508110af99020442bd6408110b798c20442dd6308110bd98420442f56108110fc90710443f141c4110fc8c710443f131c4110fc88710443f121c4110bdd9210442f56484110bdd8e10442f56384110bdd8a10442f56284110fcd4210442de63d5010b758f54042ee62d5010bb58b540427e63d5010d798f540425e63d50109f58f540435d63d50109758f540427e62d5010db98b540426e62d50109f58b540436d62d50109b58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540427e63950109f58e540427e62950109f58a540423d6595010cfd8e540433e6395010cf58e540433c6395010cfd8a540433e6295010cf58a540433c6295010cf986540433c6195010cf982540433c6095010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540427f60550109f581540433f6555010cfd8d540433e6355010cf58d540433c6355010cfd89540433e6255010cf589540433c6255010cf985540433c6155010cf981540433c6055010cf04154042be6415010cf55054042de6315010b758c54042ee6215010bb588540427e6415010cf990540423e64150109f98c540435e63150109798c540427d6315010d758c540425d63150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109d984540427e6015010de98054042be64d4c10af593530433e54d4c10cf55353042ee62d4c10bb58b530427e64d4c10cf993530423e64d4c109f593530433d64d4c108f593530427e62d4c10db98b530426e62d4c109f58b530436d62d4c109b58b530427e61d4c10dd987530427e60d4c10de983530427d6594c10cf952530433d5494c10d7d4e530427e6494c109f592530427e6294c109f58a530425d6594c10d7d52530435e5494c10e7952530431e5494c10d7552530439d5494c10c7552530435c5494c10d7d92530435e6494c10d7592530435c6494c10d7d8a530435e6294c10d758a530435c6294c10d7986530435c6194c10d7982530435c6094c10cf951530433d5454c109fd91530427c6454c10d7d8d530427f
  | 4 => 0x7d8d52442dc63549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910db548524427e64149109f590524427e63149109f58c524436e62149109f984524437561149109f184524427e60149109f180524427f65d09109f997424427d65d09109f197424436f52d0910db14b42442f661d0910bd587424427f65909109f996424427d65909109f196424433f5490910cf15242442f66190910bd586424427f65509109f995424427d65509109f195424427f65109109f994424427d65109109f194424433f5410910cf150424436f5210910db14842443ad4210910bd98442442f56110910be98042442f960109109fd97324427e65cc9109f597324427c65cc910dbd4b324436c52cc910bd98732442f561cc9109fd96324427e658c9109f596324427c658c910d7d4e324435c538c910bd98632442f5618c9109fd95324427e654c9109f595324427c654c9109fd94324427e650c9109f594324427c650c910d7d4c324435c530c910dbd48324436c520c910f34c832442f6610c910bd58432442fa600c910be580324427e65d0510cfd53414433c54d0510be98341442f960d05109f99641442f66590510dd99641442f56490510dd95241443745490510bd58e41442f56290510bd982414427c6550510cfd51414433c5450510bed8141442f86050510dd19541442746550510edd9141443b75450510dd95141443745450510ed15141443345450510bdd8d41442f76250510fcd8141442f46050510fc181414427e6510510bd98441443b541105109f997314435f53cc510d714f31442fa60cc510be583314427e658c510bd9963144376658c510bdd9231442f5648c510bd58e3144376538c510dd14e31442f5628c510bd982314427c654c510d7d4d314435c534c510bed8131442f8604c510dd1953144274654c510bdd9131442f5644c510f5d8d31443d7534c510dd94d3144374534c510f514d3144354534c510bdd8931443f3604c510bd18131443f0604c5109f99431442f6610c510f54c4314427e65c8510dbd4b214436c52c8510be98321442f960c85109f99621442f66588510dd99621442f76488510bd59221442f76388510bd58e21442f56288510dd94a21443745288510bd982214427c6548510dbd49214436c5248510bed8121442f86048510dd19521442746548510bdd9121442f56448510bdd8d21442f56348510f9d8921443e75248510dd94921443745248510f914921443645248510fcd8121442f46048510fc181214427e6508510bd98421443e521085109f997404433f54d0110cf15340442f661d0110bd58740443b541d01109f996404427f6550
  | 5 => 0x318435e534c610d754d31842fb604c610be18131843d5310c610db94b218436d52c8610be98321842f960c8610db949218436d5248610bed8121842f86048610f9484218433f54d0210cf153408433e5490210cf55240842f66190210bd586408433f5450210cf151408433e5410210cf55040842de6310210b758c40842ee6210210bb58840842f66110210bd584408435f53cc210d714f308435e538c210d754e30842f6618c210bd586308435f534c210d714d30842be640c210af590308435e530c210d754c30842ee620c210bb58830842f6610c210bd584308436f52c8210db14b208436e5288210db54a20842f66188210bd586208436f5248210db14920842be6408210af59020842de6308210b758c208436e5208210db54820842f66108210bd58420842f565c4210dd597108437754c4210dd553108437753c4210dd54f108437752c4210dd54b10842f965c4210de597108427e63d51109f58f544427e62d51109f58b544433f54951109f992544427e63951109f58e544427e62951109f58a544427d6195110dd586544427d6095110de58254442df6355110b718d54442ef6255110bb189544433f64551109fd8d544435f635511097d8d544427c6355110d718d544425c63551109fd89544436f62551109bd89544427c6255110db189544426c62551109fd85544437761551109fd81544437b60551109f994544433d5415110cf990544427e63151109f58c544427e62151109f588544427e6115110dd584544427c61151109f980544427c60151109f993534427d64d4d109f98b534427d62d4d10d7d4e534427e6494d109f592534427e6394d109f98a534427d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10bbd8953442ec6254d109fd91534433f6454d108fd91534427c6454d10cf191534423c6454d10d7d8d534427f6254d10dbd89534426f6254d109f189534436c6254d109b189534427f6154d10ddd85534427f6054d10ded81534427e6514d10d754c534427e6414d109f590534435e6314d109f988534427d6214d109f98453443756114d109f184534427e6014d109f180534427f65d0d109f997434427d65d0d109f197434435f53d0d10d714f43442f661d0d10bd587434427f6590d109f996434427d6590d109f196434433f5490d10cf15243442f66190d10bd586434427f6550d109f995434427d6550d109f195434427f6510d109f994434427d6510d109f194434433f5410d10cf150434435f5310d10d714c434439d4310d10bd98443442f56110d10be98043442f96010d109f993524427d64d49109f98f524427d63d4910dbd4a524427e64949109f592524427e63949109f58e524427e62949109f586524437561949109f58252443796094910afd9152442bc6454910b
  | 6 => 0x2f46148310f948520c42be6408310af59020c42de6308310b758c20c42f66108310bd58420c427e63d52109f58f548427e62d52109f58b548437561d5210de983548433f54952109f98e548427d63952109f98a548427d6295210cfd91548427f63552109f18d548427f62552109f189548433d5415210b798c54842dd6315210bb98854842ed6215210cf990548427e6315210d798c548425e63152109f58c548435d63152109758c548427e6215210db988548426e62152109f588548436d62152109b58854843756115210de980548427e64d4e109f593538427e62d4e109f58b538437561d4e10de983538435f5394e109f992538427d6494e109f98a538427d6294e109fd91538427c6454e10d7d8d538427f6254e109f18953842be6414e10af590538435d5314e10bb98853842ed6214e109f990538433e6414e108f990538427d6414e10cf590538423d6414e10d798c538427e6214e10db988538426e6214e109f588538436d6214e109b58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438433e54d0e10cf553438427f6590e109f996438427d6590e109f196438435e5390e10d754e438427f6550e109f995438427d6550e109f195438433e5450e10cf551438435e5350e10d754d43842f76150e10bd185438427f6510e109f994438427d6510e109f194438439d4310e10be98043842f96010e109f993528427d64d4a109f98f528427d63d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528427f6454a109f191528427f6354a109f18d528436f6254a10af99052842bd6414a10b798c52842dd6314a10db548528427e6414a10cf990528423e6414a109f590528433d6414a108f590528427e6314a10d798c528425e6314a109f58c528435d6314a109758c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10cf953428433d54d0a109fd96428427e6590a109f596428427c6590a10db94a428436d5290a109fd95428427e6550a109f595428427c6550a10cf951428433d5450a10db949428436d5250a10bdd8542842f46150a109fd94428427e6510a109f594428427c6510a10eb50842842fa6010a10be580428427f65cca109f997328427d65cca109f197328435e53cca10d754f328427f658ca109f996328427d658ca109f196328436e528ca10db54a328427f654ca109f995328427d654ca109f195328435e534ca10d754d328436e524ca10db54932842f7614ca10bd185328427f650ca109f994328427d650ca109f19432843cd320ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610cf951418433d5450610bed8141842f86050610ed504418435e53cc610d754f31842fa60cc610be583
  | 7 => 0x3d4b10dd98752c437960d4b10dbd4a52c427e6494b109f59252c427e6394b109f58e52c43766194b109fd9152c427c6454b109fd8d52c427c6354b10dbd8952c436d5214b109f99052c427d6414b109f98c52c427d6314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c42f661d0b10bd58742c427f6590b109f99642c427d6590b109f19642c42f66190b10bd58642c427f6550b109f99542c427d6550b109f19542c427f6510b109f99442c427d6510b109f19442c43ad4210b10bd98442c42f56110b109fd9732c427e65ccb109f59732c427c65ccb10bd98732c42f561ccb109fd9632c427e658cb109f59632c427c658cb10bd98632c42f5618cb109fd9532c427e654cb109f59532c427c654cb109fd9432c427e650cb109f59432c427c650cb10f34c832c42f6610cb10bd58432c433f54d0710cf15341c433e5490710cf55241c42fa6090710be58241c43756590710dd95241c43b65490710ed55241c43745490710bd58e41c42f56290710bd98241c43f26090710fc58241c433f5450710cf15141c42f76550710ddd9541c43b76450710edd5141c43765450710dd15141c43b45450710cd15141c42f76350710bdd8941c42f46050710cf95041c433d5410710ed50441c42fa6010710be58041c435f53cc710d714f31c435e538c710d754e31c42fa608c710be58231c4375658c710bdd9231c42f5648c710dd94e31c43d6538c710f554e31c4374538c710bd58a31c42f6608c710fc98231c43f1608c710d7d4d31c435c534c710bdd9531c4377654c710bdd9131c42f5644c710f5d8d31c43d7534c710dd94d31c4374534c710f514d31c4354534c710bdd8931c42f4604c710d794c31c435d530c710f54c431c42fa600c710be58031c436f52c8710db14b21c436e5288710db54a21c42fa6088710be58221c43756588710bdd9221c42f56488710bdd8e21c42f56388710dd94a21c43e65288710f954a21c43745288710bd98221c43f26088710fc58221c436f5248710db14921c42f76548710ddd9521c42f76448710bd59121c42f76348710bd58d21c43e76248710f9d4921c43765248710dd14921c43e45248710d914921c42f46048710db94821c436d5208710f948421c42fa6008710be58021c433e54d0310cf55340c42f661d0310bd58740c43b541d0310cf95140c433d5450310bdd8540c42f46150310ed50540c42de6310310b758c40c42ee6210310bb58840c42f66110310bd58440c435e53cc310d754f30c42f661cc310bd58730c43d531cc310d794d30c435d534c310bdd8530c42f4614c310f54c530c42be640c310af59030c42ee620c310bb58830c42f6610c310bd58430c436e52c8310db54b20c42f661c8310bd58720c43e521c8310db94920c436d5248310bdd8520c4
  | 8 => 0x209fd95400833e5450020cf551400835e5350020d754d40083765150020dd545400827f65100209f994400827d65100209f194400833e5410020cf55040082de6310020b758c400835e5310020d754c40082ee6210020bb58840082f66110020bd58440083765110020dd544400827d65cc020cf953300833d54cc020d794f300835d53cc020dd947300837551cc0209fd96300827d658c020cf952300833d548c020d794e300835d538c020bb98a30082ed628c020dd9463008375518c0209fd95300833e544c020cf551300835e534c020d754d3008376514c020dd545300827f650c0209f994300827d650c0209f19430082be640c020af590300833e540c020cf550300835e530c020d754c30082ee620c020bb58830082f6610c020bd5843008376510c020dd544300833e54c8020cf553200835e53c8020d754f200837651c8020dd547200836f54c8020eb953200836d54c8020eb553200832d54c8020dbd4f20083ce53c8020db54f20083cd53c8020d354f20083e651c8020db54720083e551c8020d9547200833e5488020cf552200835e5388020d754e20082ed6288020db94a20083765188020dd54620083ba5488020ee55220083da5388020f654e20082f96288020de94a20083ea5288020fc94620083f151880209fd95200833e5448020cf551200835e5348020d754d20083765148020dd54520082ef6548020dbd95200826f6548020dbd5120083ae5448020db55120083ad5448020cb551200836f5348020f394d200836d5348020f354d200834d5348020f9945200836d5148020f954520083655148020bbd81200836e5048020bed95200837b65480209ed9520083ba5448020ee55120083da5348020f654d20082fb6248020fad89200837a5248020fa94920083f25148020fc545200827e63d53109f58f54c427e62d53109f58b54c437661d5310de58354c433f54953109f98e54c427d63953109f98a54c427d6295310dd98654c433f64553109fd8d54c427c63553109fd8954c427c6255310cf55054c433e64153109f98c54c427d63153109f98854c427d6215310dd98454c437960153109f99353c427d64d4f109f98b53c427d62d4f10dd98753c437960d4f10d7d4e53c427e6494f109f59253c427e6294f109f58a53c43766194f109fd9153c427c6454f10d7d8d53c427f6254f109f18953c435d5314f109f99053c427d6414f10d798c53c427e6214f109f58853c43766114f10de58053c427f65d0f109f99743c427d65d0f109f19743c42f661d0f10bd58743c427f6590f109f99643c427d6590f109f19643c42f66190f10bd58643c427f6550f109f99543c427d6550f109f19543c427f6510f109f99443c427d6510f109f19443c439d4310f10bd98443c42f56110f109f99352c427d64d4b109f98f52c427d6
  | 9 => 0x54e51083d55394420d554e51083745394420ddd9251083766494420dd59251083746494420ddd8e51083766394420dd58e51083746394420ddd0e51083764394420dd50e51083744394420dd18a51083774294420dd90a51083754294420dd10a51083773294420dd8ca51083753294420dd0ca51083766094420dd182510833e5454420cf551510835e5354420d754d510827f64544209f191510827f63544209f18d51083776554420ddd5151083765454420ed95151083365454420dd55151083b55454420cd55151083745454420ddd4d51083765354420f594d51083565354420dd54d51083d55354420d554d51083745354420ddd9151083766454420dd59151083746454420ddd8d51083766354420dd58d51083746354420ddd0d51083764354420dd50d51083744354420dd98951083774254420dd90951083754254420dd10951083773254420dd8c951083753254420dd0c951083766054420dd18151083742054420af99051082bd6414420cf950510833d5414420b798c51082dd6314420d794c510835d5314420bd984510837551144209fd97410827e65d04209f597410833e54d0420cf553410835e53d0420d754f410837651d0420dd547410827f65904209f996410827d6590420cf952410833d5490420d794e410835d5390420dd946410837551904209fd95410827d65504209f195410833e5450420cf551410835e5350420d754d41082ef6250420bb18941083765150420dd545410827f65104209f994410827d6510420cf950410833d5410420d794c410835d5310420dd94441083755110420ed504410827f65cc4209f997310827d65cc420cf953310833d54cc420d794f310835d53cc420dd947310837551cc4209fd96310827e658c4209f596310833e548c420cf552310835e538c420d754e3108376518c420dd546310827f654c4209f595310827c654c420cf951310833d544c420d794d310835d534c420bbd8931082ec624c420dd9453108375514c4209fd94310827e650c4209f594310833e540c420cf550310835e530c420d754c3108376510c420dd54431083d5310c420cf953210833d54c8420d794f210835d53c8420db94b210837651c8420dd54721082fa60c8420be583210827d6588420cf952210833d5488420d794e210835d5388420dd546210827f6548420cf951210833d5448420d794d210835d5348420db94921083765148420cf950210833d5408420d794c210835d5308420dd94421083755108420f948421082fa6008420be580210827e64940209f592500827e63940209f58e500827d65d0020cf953400833d54d0020d794f400835d53d0020dd947400837551d00209fd96400827d6590020cf952400833d5490020d794e400835d5390020bb98a40082ed6290020dd946400837551900
  | 10 => 0x30837a60d4c209f596530833e5494c20cf552530835f5394c209f992530827d6494c209f986530827d6194c2097596530835f5494c20d7952530839e5494c20c7952530835d5494c20e7552530831d5494c20d7152530835f6494c20d7992530835d6494c20d7192530835e6294c20d718a530835f6194c20d7986530835d6194c20d7186530835e6094c20d7182530833e5454c20cf551530827f6454c209f191530835f6354c209fd89530827d6254c209fd85530827c6154c20d7d95530835f5454c20d7951530839e5454c20c7951530835d5454c20e7551530831d5454c20d7151530835f6454c20d7991530835d6454c20d7191530835e6254c20d7189530835f6154c20d7985530835d6154c20d7185530835e6054c20d7181530835c2054c20af99053082bd6414c20cf950530833d5414c20b798c530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209798c530827e6214c20db988530826e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c20d794f430835d53d0c209fd96430827e6590c209f596430827c6590c20cf952430833d5490c20d794e430835d5390c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c20bbd8943082ec6250c209fd94430827e6510c209f594430827c6510c20cf950430833d5410c20d794c430835d5310c20e750c430827e64948209f592520827e63948209f58e520827d65d0820cf953420833d54d0820d794f420835d53d08209fd96420827d6590820cf952420833d5490820d794e420835d5390820db94a42082fa6090820be582420827f6550820cf951420833d5450820d794d420835d5350820db949420827f65108209f594420833e5410820cf550420835e5310820d754c42083ad4210820be98042082f960108209f597320833e54cc820cf553320835e53cc820d754f320827f658c8209f596320833e548c820cf552320835e538c820d754e320836e528c820be98232082f9608c8209fd95320833e544c820cf551320835e534c820d754d320836e524c8209fd94320827d650c820cf950320833d540c820d794c320835d530c820f34c832082fa600c820be58032082be64d4420af593510833e54d4420cf55351082de63d4420b758f510835e53d4420d754f510833e5494420cf552510835e5394420d754e510837751944209f992510827d64944209f98e510827d6394420ddd5251083765494420ed95251083365494420dd55251083b55494420cd55251083745494420ddd4e51083765394420f594e51083565394420dd
  | 11 => 0x7c658c520d7d4e314835c538c520bb98a31482ed628c5209fd95314827e654c5209f195314827e650c5209f594314827c650c520d7d4c314835c530c520bb98831482ed620c520ddd443148374510c520f54c431482fa600c520be580314827e65c8520bb997214836e65c8520bbd9321482ed64c8520bbd8f21482ed63c8520db14721482ee60c8520bb58a21483775188520dd14621482fa6088520be58221483775148520dd14521482fb6048520be18121482ef6448520bb59121482ef6348520bb58d21483e76148520f9d45214836c5148520f914521483645148520fad8121482ec6048520fa181214827e6508520bb98821483e521085209f997404833f54d0120cf15340482ee62d0120bb58b40483ad42d01209f996404827f65501209f595404827c6550120cfd51404833c5450120bbd8940482ec6250120eb509404827e6510120b798c40482dd6310120bb98840482ed6210120bd98440482f561101209f997304835f53cc120d714f30482ee62cc120bb58b30483cd32cc1209f996304827f654c1209f595304827c654c120d7d4d304835c534c120bbd8930482ec624c120f34c9304827e650c120af99030482bd640c120bb98830482ed620c120bd98430482f5610c120fa90b20483e942c8120fa8cb20483e932c8120fac8720483e921c8120bbd9220482ed6488120bbd8e20482ed6388120bb58620483eb5088120b798f54082dd63d5020bd98754082f561d50209f98f540835e63d50209798f540827d63d5020d758f540825d63d50209f98b540836e62d50209f987540837661d50209d987540827d61d5020dd587540827561d50209f983540837a60d50209f596540833f54950209f98e540827d63950209f986540827d61950208f596540833f6395020cf98e540833d6395020cf18e540833e6295020cf18a540833f6195020cf986540833d6195020cf186540833e6095020cf182540833f64550209fd8d540827c63550209fd89540827d62550209fd85540827c6155020cfd95540833f6355020cf98d540833d6355020cf18d540833e6255020cf189540833f6155020cf985540833d6155020cf185540833e6055020cf181540833c2055020af990540833d5415020b798c54082dd6315020bd98454082f561150209f990540833e64150208f990540827e6315020d798c540825e63150209f58c540835d63150209758c540827e6215020db988540826e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a6015020af99353082bd64d4c20cf953530833d54d4c20bd98753082f561d4c209f993530833e64d4c208f993530827d64d4c20cf593530823d64d4c209f98b530836e62d4c209f987530837661d4c209d987530827d61d4c20dd587530827561d4c209f9835
  | 12 => 0x551209d185544827f6055120ded81544827e6515120cf550544833e64151209f98c544827d63151209f988544836d62151209f188544827e61151209f584544827e64d4d209f593534827e61d4d209f587534835f5394d209f992534827d6494d209f98e534827d6294d20db58a534827e6194d209f586534827d6094d20de58253482bf6454d20af19153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534835f6354d209fd89534836f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209f994534835d5314d209f990534827d6414d20d798c534827e6214d20db588534827c6214d209f984534827d6114d209fd97434827e65d0d209f597434827c65d0d20d7d4f434835c53d0d20bb98b43482ed62d0d209fd96434827e6590d209f596434827c6590d20cfd52434833c5490d20bb98a43482ed6290d209fd95434827e6550d209f595434827c6550d209fd94434827e6510d209f594434827c6510d20cfd50434833c5410d20d7d4c434835c5310d20e750c43482ee6210d20bb58843482fa6010d20be580434827e65d0920cfd53424833c54d0920be98342482f960d09209f99642482ee6590920db99642482ed6490920db952424836c5490920bb58e42482ed6190920bb982424827c6550920cfd51424833c5450920bed8142482f86050920db195424826c6550920ebd9142483af5450920db951424836c5450920eb151424832c5450920bbd8d42482ef6150920fad8142482ec6050920fa181424827e6510920bb98842483ad42109209f997324835f53cc920d714f32482fa60cc920be583324827e658c920bb996324836e658c920bbd9232482ed648c920bb58e324836e538c920db14e32482ed618c920bb982324827c654c920d7d4d324835c534c920bed8132482f8604c920db195324826c654c920bbd9132482ed644c920f3d8d32483cf534c920db94d324836c534c920f314d324834c534c920bbd8532483eb604c920bb18132483e8604c9209f99432482ee620c920f34c8324827e64d45209f593514827e63d45209f58f51483775194520afd9151482bc6454520b7d8d51482dc6354520dd544514827e64145209f590514827e63145209f58c514827e65d05209f597414827c65d0520bb98b41482ed62d0520ddd47414837451d05209f996414827d65905209f196414833f5490520cf15241482ee6290520bb58a414827f65505209f995414827c65505209f994414827d65105209f194414833f5410520cf15041482ee6210520bb58841483775110520dd14441483b54110520be98041482f960105209f997314827d65cc5209f19731482ee62cc520bb58b314837751cc520dd147314827e658c5209f59631482
  | 13 => 0xd7d8d538827f6154e209f18553882be6414e20af590538835d5314e20bd98453882f56114e209f990538833e6414e208f990538827d6414e20cf590538823d6414e20d798c538836d6214e209f98453883766114e209d984538827d6114e20dd58453882756114e20de980538827f65d0e209f997438827d65d0e209f197438833e54d0e20cf553438827f6590e209f996438827d6590e209f196438835e5390e20d754e438827f6550e209f995438827d6550e209f195438833e5450e20cf551438835e5350e20d754d43882ef6250e20bb189438827f6510e209f994438827d6510e209f194438839d4310e20be98043882f96010e20cf953428833d54d0a20be98342882f960d0a20cf951428833d5450a20bed8142882f86050a20eb508428835e53cca20d754f32882fa60cca20be583328835e534ca20d754d32882fb604ca20be18132883cd320ca20ddd46518827e64946209f592518827e63946209f58e518827f64546209f191518827f63546209f18d51882be6414620af59051882de6314620b758c518837551146209fd97418827e65d06209f597418833e54d0620cf553418827f65906209f996418827d6590620dd946418837551906209fd95418827d65506209f195418833e5450620cf55141882ef6250620bb18941883765150620dd545418827f65106209f994418827d6510620ed50441882fa6010620be580418827f65cc6209f997318827d65cc620d794f318835d53cc6209fd96318827e658c6209f5963188376518c620dd546318827f654c6209f595318827c654c620d794d318835d534c620bbd8931882ec624c620dd9453188375514c6209fd94318827e650c6209f59431883d5310c620be98031882f9600c620dd94621883755188620be98221882f96088620dd94521883755148620bed8121882f86048620f9484218833f54d0220cf153408833e5490220cf55240882ee6290220bb58a408833f5450220cf151408833e5410220cf55040882de6310220b758c40882ee6210220bb58840882f66110220bd584408835f53cc220d714f308835e538c220d754e30882ee628c220bb58a308835f534c220d714d30882be640c220af590308835e530c220d754c30882ee620c220bb58830882f6610c220bd58430882ed65c8220db597208836f54c8220db553208836f53c8220db54f208836d51c8220be597208837965c82209f98f544827d63d51209f987544827d61d5120cfd52544827e64951209f98e544827d63951209f58a544836d62951209f986544827d61951209f58254483796095120b7d8d54482dc6355120bdd8554482f46155120cfd91544827f6355120d7d8d544825f63551209f18d544835c63551209718d544827f6255120dbd89544827f6155120ddd85544827761551209f185544837461
  | 14 => 0x8242c83ea6090b20fa58242c833f5450b20cf15142c82ef6550b20dbd9542c83af6450b20ebd5142c836e5450b20db15142c83ac5450b20cb15142c82ef6350b20bbd8542c82ec6050b20cf95042c833d5410b20eb50842c82fa6010b20be58042c835f53ccb20d714f32c835e538cb20d754e32c82fa608cb20be58232c836d658cb20bbd9232c82ed648cb20db94e32c83ce538cb20f354e32c836c538cb20bb58632c82ee608cb20fa98232c83e9608cb20d7d4d32c835c534cb20bbd9532c836f654cb20bbd9132c82ed644cb20f3d8d32c83cf534cb20db94d32c836c534cb20f314d32c834c534cb20bbd8532c82ec604cb20d794c32c835d530cb20f34c832c82fa600cb20be58032c837751947209f99251c827d64947209f98e51c827d63947209fd9151c827c64547209fd8d51c827c6354720dd54451c827f65d07209f99741c827d65d0720bb98b41c82ed62d07209fd9641c827e65907209f59641c82ee6290720bb58a41c827f65507209f59541c827c65507209fd9441c827e65107209f59441c82ee6210720bb58841c83b541107209fd9731c827e65cc7209f59731c82ee62cc720bb58b31c827f658c7209f99631c827d658c720bb98a31c82ed628c7209fd9531c827d654c7209f19531c827f650c7209f99431c827d650c720bb98831c82ed620c720f54c431c837651c8720dd54721c82fa60c8720be58321c82ef64c8720bb59321c82ef63c8720bb58f21c836e51c8720f994721c83e551c8720bb98321c83ea60c8720fa58321c82ef6548720dbd9521c82ef6448720bb59121c82ef6348720bb58d21c83e76148720f9d4521c836e5148720f914521c82ec6048720dd94421c83755108720f948421c82fa6008720be58021c833e54d0320cf55340c82ee62d0320bb58b40c83ad42d0320cf95140c833d5450320bbd8940c82ec6250320eb50940c82de6310320b758c40c82ee6210320bb58840c82f66110320bd58440c835e53cc320d754f30c82ee62cc320bb58b30c83cd32cc320d794d30c835d534c320bbd8930c82ec624c320f34c930c82be640c320af59030c82ee620c320bb58830c82f6610c320bd58430c827e63d52209f58f548836d62d52209f987548827d61d5220de983548833f54952209f98e548827d63952209f986548827d6195220cfd91548827f63552209f18d548827f61552209f185548833d5415220b798c54882dd6315220bd98454882f56115220cf990548827e6315220d798c548825e63152209f58c548835d63152209758c548836d62152209f984548837661152209d984548827d6115220dd58454882756115220de980548827e64d4e209f593538836d62d4e209f987538827d61d4e20de983538835f5394e209f992538827d6494e209f986538827d6194e209fd91538827c6454e2
  | 15 => 0xc36d5248430dd945210c37551484309fd94210c27e65084309f594210c33e5408430cf550210c36e5208430db548210c3765108430dd544210c3e521084309f992500c27d64940309f597400c33e54d0030cf553400c36e52d0030db54b400c37651d0030dd547400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c36e5290030db54a400c3765190030dd546400c27f6550030cf951400c33d5450030db949400c36d5250030dd945400c37551500309fd94400c27e65100309f594400c27c6510030cf950400c33d5410030b798c400c2dd6310030bb988400c2ed6210030db948400c36d5210030bd984400c2f56110030dd944400c3755110030cf953300c33d54cc030db94b300c36d52cc030dd947300c37551cc030d7d53300c39e54cc030d7553300c39d54cc030c7553300c3ce52cc030d754b300c3cd52cc030d354b300c3d651cc030d7547300c3d551cc030d5547300c33e548c030cf552300c2dd638c030d794e300c36e528c030db54a300c376518c030dd546300c3ba548c030ee552300c2f9638c030de94e300c3da538c030fa94a300c3e9528c030fc946300c3f1518c0309fd95300c33e544c030cf551300c36e524c030db549300c376514c030dd545300c2df654c030d7d95300c25f654c030d7d51300c39e544c030d7551300c39d544c030c7551300c3ce524c030d7549300c3cd524c030d3549300c3d6514c030d7545300c3d5514c030d5545300c2df604c030d7941300c2fb654c030ded95300c27b654c030ee951300c3b9544c030bed8d300c3db634c030de94d300c3da534c030fa949300c3e9524c030fc945300c3f1514c0309f98f54c827d63d5320db98b54c827e61d53209f58754c837960d5320cfd5254c827e63953209f58e54c836e62953209f98654c827d6195320cfd9154c827f63553209f18d54c827f61553209f18554c833d5415320cf99054c827e63153209f58c54c836e62153209f98454c827d6115320de58054c827e64d4f209f59353c836e62d4f209f98753c827d61d4f20de58353c835f5394f209f99253c827d6494f20db98a53c827e6194f209f58653c827f6454f209f19153c835f6354f209fd8553c827c6154f20d754c53c827e6414f209f59053c835e6314f20db98853c827e6114f209f58453c83796014f209fd9743c827e65d0f209f59743c827c65d0f20bb98b43c82ed62d0f209fd9643c827e6590f209f59643c827c6590f20bb98a43c82ed6290f209fd9543c827e6550f209f59543c827c6550f209fd9443c827e6510f209f59443c827c6510f20e750c43c82ee6210f20bb58843c833f54d0b20cf15342c833e5490b20cf55242c82fa6090b20be58242c836d6590b20db95242c83ae5490b20eb55242c836c5490b20bb58e42c82ed6190b20bb9
  | 16 => 0xe520c830db548320c3cd320c830be980320c2f9600c830af993510c2bd64d4430cf953510c33d54d4430bb98b510c2ed62d4430db94b510c36d52d4430cf952510c33d5494430db94a510c36d5294430ddd46510c27e64944309f592510c27e62944309f58a510c3775494430dd952510c3b65494430cd952510c3755494430ed552510c3355494430dd152510c3775294430dd94a510c3e65294430d994a510c3755294430f954a510c3655294430dd14a510c3776494430dd992510c3756494430dd192510c3746394430ddd0e510c3764394430dd50e510c3744394430ddd8a510c3766294430dd58a510c3746294430ddd0a510c3764294430dd50a510c3744294430ddcca510c3763294430dd4ca510c3743294430dd982510c3746094430cf951510c33d5454430db949510c36d52544309fd91510c27c64544309fd89510c27c6254430ddd95510c3775454430dd951510c3b65454430cd951510c3755454430ed551510c3355454430dd151510c3775254430dd949510c3e65254430d9949510c3755254430f9549510c3655254430dd149510c3776454430dd991510c3756454430dd191510c3766354430ddd0d510c3764354430dd50d510c3744354430ddd89510c3766254430dd589510c3746254430ddd09510c3764254430dd509510c3744254430ddcc9510c3763254430dd4c9510c3743254430dd981510c3746054430dd0c1510c2be6414430af590510c33e5414430cf550510c2ee6214430bb588510c36e5214430db548510c2f66114430dd544510c27f65d04309f997410c27d65d0430cf953410c33d54d0430db94b410c36d52d0430dd947410c37551d04309fd96410c27e65904309f596410c33e5490430cf552410c36e5290430db54a410c3765190430dd546410c27f65504309f595410c27c6550430cf951410c33d5450430b7d8d410c2dc6350430db949410c36d5250430dd945410c37551504309fd94410c27e65104309f594410c33e5410430cf550410c36e5210430db548410c3765110430dd544410c3b54110430cf953310c33d54cc430d794f310c36e52cc430db54b310c37651cc430dd547310c2fa60cc430be583310c27d658c430cf952310c33d548c430db94a310c36d528c430dd546310c27f654c430cf951310c33d544c430d794d310c36e524c430db549310c376514c430cf950310c33d540c430db948310c36d520c430dd944310c375510c430f54c4310c2fa600c430be580310c27f65c84309f997210c27d65c8430cf953210c33d54c8430db94b210c36d52c8430dd947210c37551c84309fd96210c27e65884309f596210c33e5488430cf552210c36e5288430db54a210c3765188430dd546210c27f65484309f595210c27c6548430cf951210c33d5448430b7d8d210c2dc6348430db94921
  | 17 => 0x50309f983540c37a60d50309f596540c33f54950309f98a540c27d62950309f986540c27d61950308f596540c33e6395030cf18e540c33f6295030cf98a540c33d6295030cf18a540c33f6195030cf986540c33d6195030cf186540c33e6095030cf182540c33f64550309fd8d540c27d63550309fd89540c27c62550309fd85540c27c6155030cfd95540c33e6355030cf18d540c33f6255030cf989540c33d6255030cf189540c33f6155030cf985540c33d6155030cf185540c33e6055030cf181540c33c3055030af990540c33d5415030bb988540c2ed6215030bd984540c2f561150309f990540c33e64150308f990540c27e6315030d798c540c25e63150309f988540c36e62150309b988540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a60150309f992530c27d6494c309f597430c33e54d0c30cf553430c27f6590c309f596430c33e5490c30cf552430c35e5390c30be982430c2f96090c309fd95430c33e5450c30cf551430c35e5350c309fd94430c27d6510c30cf950430c33d5410c30e750c430c2fa6010c30be580430c2be64d4830af593520c33e54d4830cf553520c2f661d4830bd587520c33e5494830cf552520c36f52948309f992520c27d64948309f986520c27d6194830dbd52520c36e5494830eb952520c32e5494830db552520c3ad5494830cb552520c36c5494830dbd92520c36e6494830db592520c36c6494830db18e520c36f4394830db90e520c36d4394830db10e520c36f6194830db986520c36d6194830db186520c36e6094830db182520c33e5454830cf551520c27f64548309f191520c27f61548309f185520c36f6554830dbd51520c36e5454830eb951520c32e5454830db551520c3ad5454830cb551520c36c5454830dbd91520c36e6454830db591520c36c6454830db98d520c36f4354830db90d520c36d4354830db10d520c36f6154830db985520c36d6154830db185520c36e6054830db181520c36c3054830af990520c2bd6414830cf950520c33d5414830bb988520c36d5214830bd984520c2f561148309fd97420c27e65d08309f597420c33e54d0830cf553420c36e52d0830db54b420c27f65908309f996420c27d6590830cf952420c33d5490830db94a420c36d52908309fd95420c27d65508309f195420c33e5450830cf551420c2df6350830b718d420c36e5250830db549420c27f65108309f994420c27d6510830cf950420c33d5410830db948420c36d5210830eb508420c33e54cc830cf553320c35e53cc830db94b320c36d52cc830be983320c2f960cc8309f596320c33e548c830cf552320c36d528c8309fd95320c33e544c830cf551320c35e534c830db949320c33e540c830cf550320c36
  | 18 => 0x9f997424c27d65d09309f197424c2de63d0930b758f424c36f52d0930db14b424c27e65909309f596424c27c6590930cfd52424c33c5490930b798e424c2dd63909309fd95424c27e65509309f195424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930dbd48424c36c5210930eb508424c2fa6010930be580424c27e65cc930b7997324c35e65cc930b7d93324c2dd64cc930d714b324c2dd61cc930b7983324c2dd638c930dbd4a324c36c528c930be982324c2f9608c930dbd49324c36c524c930bed81324c2f8604c930b7d91324c2dd644c930f3d89324c3cf524c930d7149324c3cc524c930d3149324c2df614c930f6d81324c2dc604c930f6181324c27e650c930b798c324c3cd320c9309f993514c27d64d45309f98b514c27d62d4530ddd46514c2bf6454530af191514c2ef6254530bb189514c37551145309f990514c27d64145309f988514c27d62145309f997414c27d65d05309f197414c2de63d0530b758f414c37751d0530dd147414c27e65905309f596414c27c6590530cfd52414c33c5490530b798e414c2dd63905309fd95414c27e65505309f195414c27e65105309f594414c27c6510530cfd50414c33c5410530b798c414c2dd6310530ddd44414c3745110530ed504414c2fa6010530be580414c27e65cc530b7997314c35e65cc530b7d93314c2dd64cc530b758b314c35c51cc530b7983314c2dd638c530ddd46314c374518c530be982314c2f9608c530ddd45314c374514c530bed81314c2f8604c530b7d91314c2dd644c530b7d89314c3d7614c530f5d45314c35c514c530f5145314c354514c530f6d81314c2dc604c530f6181314c27e650c530b798c314c3d5310c5309f997214c27d65c85309f197214c2de63c8530b758f214c37751c8530dd147214c27e65885309f596214c27c6588530b798e214c2dd6388530dbd4a214c36c52885309fd95214c27e65485309f195214c2de6348530b758d214c27e65085309f594214c27c6508530b798c214c2dd6308530dbd48214c36c5208530ddd44214c3745108530f9484214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d0130e750f404c27e65901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c39d43501309f994404c2de6310130b758c404c2ee6210130bb588404c2f66110130bd584404c3da43cc130f650f304c3db32cc130f64cb304c3db31cc130f64c7304c2df648c130b7592304c2dd628c130b7586304c3db508c130bb98b540c2ed62d5030bd987540c2f561d50309f98f540c35e63d50309f98b540c36e62d50309b98b540c27d62d5030db58b540c26d62d50309f987540c37661d50309d987540c27d61d5030dd587540c27561d
  | 19 => 0xa428c27f6550a309f595428c27c6550a30cf951428c33d5450a30b7d8d428c2dc6350a30db949428c36d5250a309fd94428c27e6510a309f594428c3ad4210a30be980428c2f96010a30db94a328c36d528ca30be982328c2f9608ca30db949328c36d524ca30bed81328c2f8604ca30f34c8328c37751946309f992518c27d64946309f98a518c27d62946309fd91518c27c64546309fd89518c27c6254630af990518c2bd6414630bb988518c2ed6214630dd544518c27f65d06309f997418c27d65d0630cf953418c33d54d06309fd96418c27e65906309f596418c3765190630dd546418c27f65506309f595418c27c6550630cf951418c33d5450630b7d8d418c2dc6350630dd945418c37551506309fd94418c27e65106309f594418c3b54110630be980418c2f96010630dd946318c375518c630be982318c2f9608c630dd945318c375514c630bed81318c2f8604c630f54c4318c27f65c86309f997218c27d65c8630db94b218c36d52c86309fd96218c27e65886309f596218c3765188630dd546218c27f65486309f595218c27c6548630b7d8d218c2dc6348630db949218c36d5248630dd945218c37551486309fd94218c27e65086309f594218c3e52108630be980218c2f96008630cfd53408c33c54d0230cf952408c33d5490230b798e408c2dd6390230cfd51408c33c5450230cf950408c33d5410230b798c408c2dd6310230bb988408c2ed6210230bd984408c2f56110230b7597308c35d65cc230d7d53308c35d54cc230d754b308c35d51cc230be597308c37965cc2309f98b544c27d62d51309f987544c27d61d5130cfd52544c27e64951309f58e544c35d63951309f98a544c27d62951309f986544c27d61951309f582544c3796095130bbd89544c2ec6255130bdd85544c2f46155130cfd91544c27f6355130d7d8d544c27f6255130dbd89544c26f62551309f189544c36c62551309b189544c27f6155130ddd85544c27761551309f185544c37461551309d185544c27f6055130ded81544c27e6515130cf550544c33e64151309f98c544c35d63151309f18c544c27e62151309f588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d309f996434c2de6590d30d7996434c2dd6490d30d7952434c35c5490d30b758a434c2dd6190d30b7982434c27c6550d30cfd51434c33c5450d30bed81434c2f86050d30d7195434c25c6550d30e7d91434c39f5450d30d7951434c35c5450d30e7151434c31c5450d30b7d89434c2df6150d30f6d81434c2dc6050d30f6181434c27e6510d30b798c434c39d4310d309f993524c27d64d49309f987524c27d61d4930dbd4a524c2bf6454930af191524c2f76154930bd185524c36d52149309f990524c27d64149309f984524c27d6114930
  | 20 => 0xc27d6194b309fd9152cc27c6454b309fd8552cc27c6154b30db54852cc27f65d0b309f99742cc27d65d0b30b798f42cc2dd63d0b309fd9642cc27e6590b309f59642cc2de6390b30b758e42cc27f6550b309f59542cc27c6550b309fd9442cc27e6510b309f59442cc2de6310b30b758c42cc3ad4210b30db94b32cc36d52ccb30be98332cc2f960ccb30b7d9332cc2dd64ccb30d794b32cc3ce52ccb30f354b32cc2dd61ccb30b798332cc3da60ccb30f658332cc2df654cb30d7d9532cc2df644cb30b759132cc3cf624cb30f3d4932cc35e524cb30f314932cc2df614cb30b718132cc36e520cb30db54832cc3cd320cb30be98032cc2f9600cb30ddd4651cc27e64947309f59251cc27e62947309f58a51cc27f64547309f19151cc27f62547309f18951cc37551147309fd9741cc27e65d07309f59741cc2de63d0730b758f41cc27f65907309f99641cc27d6590730b798e41cc2dd63907309fd9541cc27d65507309f19541cc27f65107309f99441cc27d6510730b798c41cc2dd6310730ed50441cc37651cc730dd54731cc2fa60cc730be58331cc2df64cc730b759331cc2dd62cc730d794731cc3d651cc730f554731cc2de60cc730f698331cc3d960cc730b7d9531cc35f654c730b7d9131cc2dd644c730b7d8931cc3d7614c730f5d4531cc35e514c730f514531cc2dc604c730dd94431cc375510c730f54c431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730b798f21cc2dd63c87309fd9621cc27e65887309f59621cc2de6388730b758e21cc27f65487309f59521cc27c6548730b798d21cc2dd63487309fd9421cc27e65087309f59421cc2de6308730b758c21cc3e52108730cf95340cc33d54d0330b798f40cc2dd63d0330e750f40cc33e5450330cf55140cc2df6350330b718d40cc39d4350330b798c40cc2dd6310330bb98840cc2ed6210330bd98440cc2f56110330d758f548c27e62d52309f58b548c27e61d52309f587548c37a60d5230cfd52548c27e62952309f58a548c27e61952309f586548c33f64552309fd89548c27c62552309fd85548c27c6155230cf550548c2ee6215230bb588548c2f66115230bd584548c33e6415230d758c548c27e6215230db988548c26e62152309f588548c36d62152309b588548c27e6115230dd984548c27661152309f584548c37561152309d584548c37a6015230cf953438c33d54d0e30be983438c2f960d0e30cf951438c33d5450e30bed81438c2f86050e30e750c438c36f5294a309f992528c27d6494a309f986528c27d6194a309fd91528c27c6454a309fd85528c27c6154a30af990528c2bd6414a30db548528c2f66114a30bd584528c27f65d0a309f997428c27d65d0a30cf953428c33d54d0a309fd96428c27e6590a309f596428c36e5290a30db54
  | 21 => 0x4110440be98041102f960104409fd97311027e65cc4409f597311035e53cc440d754f311036e52cc440db54b311037651cc440dd547311027f658c4409f996311027d658c440d794e311035d538c440db94a311036d528c440dd9463110375518c4409fd95311027d654c4409f19531102bf644c440af191311035e534c440d754d311036e524c440db5493110376514c440dd545311027f650c4409f994311027d650c440d794c311035d530c440db948311036d520c440dd9443110375510c440f54c4311027f65c84409f997211027d65c8440d794f211035d53c8440db94b211036d52c8440dd947211037551c84409fd96211027e65884409f596211035e5388440d754e211036e5288440db54a21103765188440dd546211027f65484409f595211027c6548440afd9121102bc6448440d794d211035d5348440db949211036d5248440dd945211037551484409fd94211027e65084409f594211035e5308440d754c211036e5208440db54821103765108440dd54421103e52108440d794f401035d53d0040db94b401036d52d0040dd947401037551d0040e794f401033d53d0040e754f401031d53d0040eb94b401033d52d0040eb54b401032d52d0040ed947401033d51d0040ed547401033551d0040af592401033e5490040d794e401035d5390040db94a401036d5290040dd94640103755190040be592401037a5490040ee95240103da5390040f654e40103ea5290040fa54a40103f25190040fc546401027f6550040d794d401035d5350040db949401036d5250040dd94540103755150040afd95401033f65500408fd95401039e5350040cf54d401039d5350040c754d40103ae5250040cf54940103ad5250040cb54940103b65150040cf54540103b55150040cd54540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040f694d40103d95350040fa94940103e95250040fc94540103f15150040d798f54cc27e62d53309f58b54cc27e61d53309f58754cc37960d5330cfd5254cc35e63953309f98a54cc27d62953309f98654cc27d6195330cfd9154cc27f62553309f18954cc27f61553309f18554cc33d5415330cf99054cc35e63153309f98854cc27d62153309f98454cc27d6115330de58054cc33f54d0f30cf15343cc33e5490f30cf55243cc2fa6090f30be58243cc35d6590f30d795243cc39e5490f30e755243cc35c5490f30b758a43cc2dd6190f30b798243cc3da6090f30f658243cc33f5450f30cf15143cc2df6550f30d7d9543cc39f6450f30e7d5143cc35e5450f30d715143cc39c5450f30c715143cc2df6250f30b7d8543cc2dc6050f30cf95043cc33d5410f30e750c43cc2fa6010f30be58043cc36f5294b309f99252cc27d6494b309f98652c
  | 22 => 0x840db90d521036d4354840db10d521036f6154840db985521036d6154840db185521036e6054840db181521036c4054840b798c52102dd6314840d794c521035d5314840bb988521036d5214840bd98452102f56114840cf953421035e53d0840d754f421036e52d0840db54b42102fa60d0840be583421027d6590840d794e421035d5390840db54a421027f6550840cf951421035e5350840d754d421036e5250840d794c421035d5310840db948421036d5210840eb50842102fa6010840be580421027f65cc8409f997321027d65cc840d794f321035d53cc840db94b321036d52cc8409fd96321027e658c8409f596321035e538c840d754e321036e528c840db54a321027f654c8409f595321027c654c840afd9132102bc644c840d794d321035d534c840db949321036d524c8409fd94321027e650c8409f594321035e530c840d754c321036e520c840db54832103cd320c840b798f51102dd63d4440d794f511035d53d4440bb98b51102ed62d4440db94b511036d52d4440d794e511035d5394440db94a511036d5294440ddd46511027e63944409f58e511027e62944409f58a51103775394440dd94e51103d65394440d594e51103755394440f554e51103555394440dd14e51103775294440dd94a51103e65294440d994a51103755294440f954a51103655294440dd14a51103746494440ddd8e51103766394440dd58e51103746394440ddd0e51103764394440dd50e51103744394440ddd8a51103766294440dd58a51103746294440ddd0a51103764294440dd50a51103744294440ddcca51103763294440dd4ca51103743294440dd98251103746094440d794d511035d5354440db949511036d52544409fd8d511027c63544409fd89511027c6254440ddd9551103775354440dd94d51103d65354440d594d51103755354440f554d51103555354440dd14d51103775254440dd94951103e65254440d994951103755254440f954951103655254440dd14951103766454440ddd8d51103766354440dd58d51103746354440ddd0d51103764354440dd50d51103744354440ddd8951103766254440dd58951103746254440ddd0951103764254440dd50951103744254440ddcc951103763254440dd4c951103743254440dd98151103746054440dd10151102de6314440b758c511035e5314440d754c51102ee6214440bb588511036e5214440db54851102f66114440dd544511033e54d0440d794f411035d53d0440db94b411036d52d0440dd947411037551d0440be98341102f960d04409f596411035e5390440d754e411036e5290440db54a411037551904409fd95411033e5450440d794d411035d5350440db949411036d5250440dd945411035e5310440d754c411036e5210440db54841103765110440dd54441103b5
  | 23 => 0xf99741502be65d0540cf99741502bd63d0540af58b415033c51d0540af98341502bd6490540ddd4641503745190540be98241502f96090540ddd4541503745150540bed8141502f86050540afd8d41502bf6250540edd8541503b75150540cf14541503b45150540cd14541503bb6050540af18141503b860505409f99441502be6410540ed504415027e65cc5409f597315027c65cc540af99331502bd64cc540ddd47315037451cc5409f996315027d658c5409f19631502be648c540af592315035f538c540d714e315027f654c5409f995315027c654c540af99131502bd644c5409f994315027d650c5409f19431502be640c540af590315035f530c540d714c3150377510c540dd14431503d5310c540be98031502f9600c5409f997215027d65c85409f19721502be64c8540af593215037751c8540dd147215027e65885409f596215027c6588540af99221502bd6488540dbd4a215036c52885409fd95215027e65485409f19521502be6448540af591215027e65085409f594215027c6508540af99021502bd6408540dbd48215036c5208540ddd4421503745108540f948421502fa6008540be58021503bb43d0140ee50f40503bb42d0140ee50b40503bb41d0140ee50740502bd6390140af58a40502bd6190140eed4240502ee62d4c40bb58b53102f661d4c40bd587531035f5394c409f98a531027d6294c409f986531027d6194c40d7192531035f6294c40d798a531035d6294c40d718a531035f6194c40d7986531035d6194c40d7186531035e6094c40d7182531027f6254c409f189531027f6154c409f185531035f6554c40d7991531035f6254c40d7989531035d6254c40d7189531035f6154c40d7985531035d6154c40d7185531035e6054c40d7181531035c4054c40b798c531035d5314c40bb98853102ed6214c40bd98453102f56114c40cf953431035e53d0c40d754f43102fa60d0c40be583431027d6590c40d754e431027f6550c40cf951431035e5350c40d794c431035d5310c40e750c43102fa6010c40be58043102de63d4840b758f521035e53d4840d754f52102f661d4840bd587521035e5394840d754e521036f52948409f98e521027d63948409f986521027d6194840dbd4e521036e5394840f394e521034e5394840db54e52103cd5394840d354e521036c5394840db192521036f6394840db98e521036d6394840db18e521036f4394840db90e521036d4394840db10e521036f6194840db986521036d6194840db186521036e6094840db182521035e5354840d754d521027f63548409f18d521027f61548409f185521036f6554840dbd4d521036e5354840f394d521034e5354840db54d52103cd5354840d354d521036c5354840db991521036f6354840db98d521036d6354840db18d521036f4354
  | 24 => 0x329027d650ca40f34c832902fa600ca40be580329037751946409f98e519027d63946409f98a519027d62946409fd8d519027c63546409fd89519027c6254640b798c51902dd6314640bb98851902ed6214640dd54451903765190640dd54641902fa6090640be58241903765150640dd54541902fb6050640be18141903b541106409fd97319027e65cc6409f597319035e53cc640d754f319027f658c6409f996319027d658c640dd9463190375518c6409fd95319027d654c6409f19531902bf644c640af191319035e534c640d754d3190376514c640dd545319027f650c6409f994319027d650c640f54c431902fa600c640be580319027f65c86409f997219027d65c8640db94b219036d52c86409fd96219027e65886409f59621903765188640dd546219027f65486409f595219027c6548640afd9121902bc6448640db949219036d5248640dd945219037551486409fd94219027e65086409f59421903e52108640be98021902f96008640af597409033d65d0240cf54f409033d52d0240cf54740902f965d0240de597409027e62d4d409f58b535027e61d4d409f587535035f5394d40bbd8953502ec6254d40bdd8553502f46154d40d754c535027e6214d409f588535027e6114d409f584535027e65d0d40af997435033e65d0d40cf14f43502bd62d0d40af58743502be60d0d40af592435035f5390d40d714e43502fa6090d40be582435035f5350d40d714d43502fb6050d40be181435039f6350d40e7d4d435033c5350d40e714d435031c5350d40afd8943502bf6150d40eed8143502bc6050d40ee181435027e6510d40af990435039d4310d409f98f525027d63d49409f987525027d61d4940dbd4a52502df6354940b718d52502f76154940bd185525036d52149409f98c525027d63149409f984525027d61149409f99742502be65d0940cf99742502bd63d0940cf14b42502bd61d0940af98342502bd6490940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bed8142502f86050940afd8d42503af6250940ebd49425033c5250940eb149425032c5250940afd8542503bb6050940af18142503b860509409f99442502be6410940eb508425027e65cc9409f597325027c65cc940af99332502bd64cc940dbd4b325036c52cc9409f996325027d658c9409f19632502be648c940af592325035f538c940d714e325027f654c9409f995325027c654c940af99132502bd644c9409f994325027d650c9409f19432502be640c940af590325035f530c940d714c325036f520c940db14832503cd320c940be98032502f9600c9409f98f515027d63d45409f98b515027d62d4540ddd4651502df6354540b718d51502ef6254540bb189515037551145409f98c515027d63145409f988515027d62145409
  | 25 => 0x2bf6550f40cfd9543d039f6350f40e7d4d43d033e5350f40e714d43d02bf6250f40afd8543d02bc6050f40d794c43d035d5310f40e750c43d02fa6010f40be58043d036f5294b409f98e52d027d6394b409f98652d027d6194b409fd8d52d027c6354b409fd8552d027c6154b40db54852d036e52d0b40db54b42d02fa60d0b40be58342d02bd63d0b40cf94b42d03ae52d0b40eb54b42d02bd61d0b40af98342d03ba60d0b40ee58342d02bf6550b40cfd9542d02bf6350b40ebd8942d03af5250b40cf94942d03ac5250b40afd8542d02bc6050b40db94842d036d5210b40eb50842d02fa6010b40be58042d027f65ccb409f99732d027d65ccb40af99332d02bd64ccb409fd9632d027e658cb409f59632d02be648cb40af59232d027f654cb409f59532d027c654cb40af99132d02bd644cb409fd9432d027e650cb409f59432d02be640cb40af59032d03cd320cb40ddd4651d027e63947409f58e51d027e62947409f58a51d027f63547409f18d51d027f62547409f18951d03755114740dd94741d037551d0740be98341d02f960d0740af58f41d02bd62d0740cf94741d03b651d0740ed54741d02be60d0740ee98341d03b960d0740afd9541d033f6550740afd8d41d02bf6250740edd8541d03b75150740cf94541d03b45150740af18141d03765110740dd54441d03b54110740be98041d02f960107409fd9731d027e65cc7409f59731d02be64cc740af59331d027f658c7409f99631d027d658c740af99231d02bd648c7409fd9531d027d654c7409f19531d02be644c740af59131d027f650c7409f99431d027d650c740af99031d02bd640c740f54c431d027f65c87409f99721d027d65c8740af99321d02bd64c87409fd9621d027e65887409f59621d02be6488740af59221d027f65487409f59521d027c6548740af99121d02bd64487409fd9421d027e65087409f59421d02be6408740af59021d03e52108740d7d4e539027e6294e409f58a539027e6194e409f586539027f6254e409f189539027f6154e409f185539035d5314e40bb98853902ed6214e40bd98453902f56114e40d794e439035d5390e40be98243902f96090e40d794d439035d5350e40bed8143902f86050e40e750c439036f5294a409f98e529027d6394a409f986529027d6194a409fd8d529027c6354a409fd85529027c6154a40b798c52902dd6314a40db54852902f66114a40bd584529036e5290a40db54a42902fa6090a40be582429036e5250a40db54942902fb6050a40be18142903ad4210a409fd97329027e65cca409f597329035e53cca40d754f329027f658ca409f996329027d658ca40db94a329036d528ca409fd95329027d654ca409f19532902bf644ca40af191329035e534ca40d754d329036e524ca40db549329027f650ca409f994
  | 26 => 0x14c219f58053087796014c219e580530867f65d0c219f997430867d65d0c219f197430873e54d0c21cf55343086ee62d0c21bb58b43086f661d0c21bd587430867f6590c219f996430867d6590c219f196430875e5390c21d754e43086ee6290c21bb58a43086f66190c21bd586430867f6550c219f995430867d6550c219f195430873e5450c21cf551430875e5350c21d754d430867f6510c219f994430867d6510c219f194430879d4310c219f992520867d64948219f98e520867d63948219f597420867f65908219f596420873e5490821cf55242086f66190821bd586420867f65508219fd94420867d6510821cf950420873d5410821eb50842086f66110821bd584420867d65cc8219fd96320867d658c821d794e320875d538c821bd98632086f5618c8219fd95320867f650c8219f594320875e530c821d754c32087cd320c821bd98432086f5610c8219f992510867d64944219f98e510867d63944219f597410867f65904219f596410873e5490421cf55241086ee6290421bb58a410867f65504219fd94410867e65104219f594410867c6510421cf950410873d5410421bb98841086ed6210421ed504410867d65cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c4219fd95310867f650c4219f994310867d650c4219f194310875e530c421d754c31086ee620c421bb58831087d5310c421bb58a210876e5288421bd58a21086e56288421dd94a21087e652884219fd9521086ef6548421dbd95210866f6548421bbd85210876e5148421f9d0521087e64148421f950521087e44148421f9cc521087e63148421f94c521087e43148421bdd95210877765484219dd9521086f76248421f9d8921087765248421f994921087e74248421f990921087e54248421f910921087e73248421f98c921087e53248421f90c921087e76548421b9d9521087676548421f9d9121087e66448421f959121087e46448421f9d5121087e65448421f955121087e45448421f9d8d21087e66348421f958d21087e46348421f9d4d21087e65348421f954d21087e45348421f9d0d21087e64348421f950d21087e44348421f9d8121087e66048421f958121087e46048421f948750087e52194021ded42500867e64940219f592500867e63940219f58e50087e521540219fd91500867c64540219fd8d500867c6354021dbc8550087762154021db48550087752154021d948550086be6414021af59050086de6314021b758c50087e52114021de540500875f5394f409f98a53d027d6294f409f98653d027d6194f409fd8953d027c6254f409fd8553d027c6154f40d754c53d035e53d0f40d754f43d02fa60d0f40be58343d033e53d0f40e794f43d039d53d0f40af58b43d02bd61d0f40af98343d03ba60d0f40ee58343d0
  | 27 => 0x219f582534867f6454d219f191534875f6354d219fd89534876f6254d219fd8553487776154d219fd81534867c6054d219f994534875d5314d219f990534867d6414d21d798c534867e6014d219f580534867f65d0d219f997434867d65d0d219f197434873f54d0d21cf153434867f6590d219f996434867d6590d219f196434875f5390d21d714e434867f6550d219f995434867d6550d219f195434873f5450d21cf151434875f5350d21d714d43486ef6250d21bb18943486f76150d21bd185434867f6510d219f994434867d6510d219f194434879d4310d21bb98843486ed6210d21bd98443486f56110d219f997424873f54d0921cf15342486f661d0921bd587424867e65909219f195424873f5450921cf15142486f76150921bd185424867e6510921eb508424867e65cc921d7d4f324875c53cc921bd98732486f561cc9219f996324867c654c921d7d4d324875c534c921bdd8532486f4614c9219f99432487cd320c9219f997414873f54d0521cf15341486ee62d0521bb58b414867e65905219fd95414867d65505219f195414873f5450521cf15141486ef6250521bb189414867e6510521ed504414867e65cc521d7d4f314875c53cc521bb98b31486ed62cc5219f996314867f654c5219f595314867c654c521d7d4d314875c534c521bbd8931486ec624c5219f99431487d5310c521bd58321487e75188521bb582214867e64d41219f593504867e63d41219f58f504877b5094121afd9150486bc6454121b7d8d50486dc6354121af99050486bd6414121b798c50486dd6314121de540504867e6414121cf990504863e64141219f590504873d64141218f590504867e6314121d798c504865e63141219f58c504875d63141219758c504867e63d50219f58f540867e62d5021db98b540867e61d5021dd987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf55054086de6315021b758c54086fa6015021be580540867e6415021cf990540867e6315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e580540867e64d4c219f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530867f6454c219f191530875f6354c219fd81530867c6054c21af99053086bd6414c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6314c21d798c530867e6214c21db988530867e6114c21dd984530867e6014c21de980530867a6
  | 28 => 0x59250c867e63943219f58e50c867f64543219f19150c867f63543219f18d50c86be6414321af59050c86de6314321b758c50c87795014321b798f54886dd63d52219f98f548875e63d52219798f548867d63d5221d758f548865d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548867e60952219f582548873f64552219fd8d548867c63552219fd81548867c6055221cf550548873e64152219f98c548867d6315221db588548877661152219f980548867d6015221af99353886bd64d4e219f993538873e64d4e218f993538867d64d4e21cf593538863d64d4e21db58b538877661d4e219f983538867d60d4e21d7d4e538867e6494e219f592538867e6094e219f582538867f6454e219f191538875f6354e219fd81538867c6054e21d754c538867e6414e219f590538875e6314e21db58853887766114e219f980538867d6014e219fd97438867e65d0e219f597438867c65d0e21d794f438875d53d0e21bb98b43886ed62d0e219fd96438867e6590e219f596438867c6590e21cf952438873d5490e21bb98a43886ed6290e219fd95438867e6550e219f595438867c6550e21bdd8543886f46150e219fd94438867e6510e219f594438867c6510e21cf950438873d5410e21d794c438875d5310e21e750c43886f66110e21bd584438873e54d0a21cf55342886f661d0a21bd587428873e5450a21cf55142886f76150a21bd18542887ad4210a21d794f328875d53cca21bd98732886f561cca21d794d328875d534ca21bdd8532886f4614ca21f34c8328873e5490621cf55241886ee6290621bb58a418873e5410621cf55041886ee6210621bb58841887b54110621d794e318875d538c621bb98a31886ed628c621d794c318875d530c621bb98831886ed620c621f54c431886ed65c8621db59721886f565c8621dd59721886f560c8621ded42508867e64942219f592508867e63942219f58e508867f64542219f191508867f63542219f18d508876f2154221af99050886bd6414221b798c50886dd6314221de540508867e63d51219f58f544867e60d51219f583544873f5495121b798e54486dd63951219f992544867e6395121d798e544865e63951219f58e544875d63951219758e544867d6295121db58a544867d6195121dd586544867e60951219f582544873f64551219fd8d544867c63551219fd89544876f62551219fd85544877761551219fd81544867c60551219f994544873d5415121cf990544867e63151219f58c544867e60151219f580544867e64d4d219f593534867e60d4d219f58353486be6494d21af592534875f5394d219f992534873e6494d218f992534867d6494d21cf592534863d6494d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d
  | 29 => 0x10c6de6310431b758c410c7b54110431b758e310c75e538c431bd58e310c6d5638c431dd94e310c7d6538c4319fd95310c6df654c431d7d95310c65f654c431b7d85310c75e514c431f5d05310c7d6414c431f5505310c7d4414c431bdd95310c777654c4319dd95310c6f7634c431f5d8d310c776534c431f594d310c7d7434c431f590d310c7d5434c431f510d310c7d7324c431f58c9310c7d5324c431f50c9310c7d7654c431b5d95310c757654c431f5d91310c7d6644c431f5591310c7d4644c431f5d51310c7d6544c431f5551310c7d4544c431f5d89310c7d6624c431f5589310c7d4624c431f5d49310c7d6524c431f5549310c7d4524c431f5d09310c7d6424c431f5509310c7d4424c431f5d81310c7d6604c431f5581310c7d4604c431f54c7500c7d53194031ded42500c67e64940319f592500c67e62940319f58a500c7d531540319fd91500c67c64540319fd89500c67c6254031d7cc5500c7763154031d74c5500c7753154031d54c5500c6be6414031af590500c6ee6214031bb588500c7d53114031de540500c6de63d5321b758f54c867e63d5321d798f54c865e63d53219f58f54c875d63d53219758f54c876e62d5321dd58754c867e60d53219f58354c873f54953219f98e54c867d63953219f98254c867d6095321cfd9154c867f63553219f18d54c867f60553219f18154c873d5415321cf99054c867e63153219f58c54c876e6215321dd58454c867e60153219f58054c86be64d4f21af59353c867e64d4f21cf99353c863e64d4f219f59353c873d64d4f218f59353c876e62d4f21dd58753c867e60d4f219f58353c875f5394f219f99253c867d6494f219f98253c867d6094f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c875d5314f219f99053c867d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f219f19743c875e53d0f21d754f43c86f661d0f21bd58743c867f6590f219f99643c867d6590f219f19643c873e5490f21cf55243c86f66190f21bd58643c867f6550f219f99543c867d6550f219f19543c86ef6250f21bb18943c867f6510f219f99443c867d6510f219f19443c873e5410f21cf55043c875e5310f21d754c43c879d4310f21bb98843c86ed6210f21cf95242c873d5490b21bd98642c86f56190b21cf95042c873d5410b21eb50842c86f66110b21bd58442c875e538cb21d754e32c86f6618cb21bd58632c875e530cb21d754c32c87cd320cb21bd98432c86f5610cb21cf95341c873d54d0721bb98b41c86ed62d0721cf95141c873d5450721bbd8941c86ec6250721ed50441c875e53cc721d754f31c86ee62cc721bb58b31c875e534c721d754d31c86ef624c721bb18931c87d5310c721ded4250c867e64943219f
  | 30 => 0x7d64149319f980524c67d60149319f997424c67d65d09319f197424c73f54d0931cf153424c67e65909319f596424c67c6590931dbd4a424c76c52909319fd95424c67e65509319f195424c73f5450931cf151424c6df6350931b718d424c76f5250931db149424c6f76150931bd185424c67e65109319f594424c67c6510931b798c424c6dd6310931eb508424c6f66110931bd584424c67e65cc931dbd4a324c76c528c931bd986324c6f5618c931dbd49324c76c524c931bdd85324c6f4614c9319f994324c7cd320c9319f997414c73f54d0531cf153414c6de63d0531b758f414c67e65905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c67e6510531ed504414c6f560cc531f5d46314c6dd608c5319f993504c67d64d41319f98b504c67d62d4131ded42504c6bf6454131af191504c6ef6254131bb189504c6be6414131af590504c6ee6214131bb588504c77950141319f990504c73e64141318f990504c67d6414131cf590504c63d64141319f988504c76e62141319b988504c67d6214131db588504c66d62141319f98f540c75e63d50319f98b540c67d62d50319f987540c77661d50319f983540c67d60d50319f596540c73f54950319f98a540c67d62950319f982540c67d6095031cfd91540c67f62550319f189540c67f60550319f181540c73d5415031bb988540c6ed6215031be980540c6f960150319f990540c73e64150319f98c540c75e63150319f988540c76e62150319b988540c67d6215031db588540c66d62150319f984540c77661150319f980540c77a60150319e980540c67d6015031de580540c67960150319f992530c67d6494c319f597430c67f6590c319f596430c73e5490c31cf552430c6f66190c31bd586430c67f6550c319fd94430c67d6510c31cf950430c73d5410c31e750c430c6f66110c31bd584430c76f52948319f992520c67d64948319f982520c67d60948319fd91520c67c64548319fd81520c67c6054831af990520c6bd6414831db548520c6fa6014831be580520c67f65d08319f997420c67d65d0831cf953420c73d54d0831b798f420c6dd63d0831bd987420c6f561d08319fd96420c67e65908319f596420c6de6390831b758e420c76e5290831db54a420c6f66190831bd586420c67f65508319f595420c67c6550831cf951420c73d5450831db949420c76d52508319fd94420c67e65108319f594420c7ad4210831db94b320c76d52cc831bd987320c6f561cc8319f596320c67f654c831db948320c76d520c831f34c8320c6f6610c831bd584320c67e64944319f592510c67d65d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd63904319fd95410c67f65104319f994410c67d65104319f194410c73e5410431cf5504
  | 31 => 0x10b31cf95042cc73d5410b31b798c42cc6dd6310b31db94842cc76d5210b31eb50842cc76e52ccb31db54b32cc6f661ccb31bd58732cc76e520cb31db54832cc7cd320cb31bd98432cc6f5610cb31cf95341cc73d54d0731b798f41cc6dd63d0731cf95141cc73d5450731b7d8d41cc6dc6350731ed50441cc77b50943319f99250cc67d64943319f98a50cc67d62943319fd9150cc67c64543319fd8950cc67c6254331af99050cc6bd6414331bb98850cc6ed6214331de54050cc6ee62d5231bb58b548c75d63d52319f98b548c76e62d52319b98b548c67d62d5231db58b548c66d62d5231dd987548c67e60d52319f583548c73f54952319f98a548c67d62952319f982548c67d6095231cfd91548c67f62552319f189548c67f60552319f181548c73d5415231cf990548c75d63152319f988548c67d6215231dd984548c67e60152319f580548c73e54d0e31cf553438c6f661d0e31bd587438c73e5450e31cf551438c6f76150e31bd185438c79d4310e31af993528c6bd64d4a31dbd4a528c67e6494a319f592528c67e6094a319f582528c67f6454a319f191528c67f6054a319f181528c76d5214a319fd97428c67e65d0a319f597428c6de63d0a31b758f428c76e52d0a31db54b428c67f6590a319f996428c67d6590a31cf952428c73d5490a31b798e428c6dd6390a319fd95428c67d6550a319f195428c6f76150a31bd185428c67f6510a319f994428c67d6510a31cf950428c73d5410a31db948428c76d5210a31eb508428c6f66110a31bd584428c76e528ca31db54a328c6f6618ca31bd586328c76e524ca31db549328c6f7614ca31bd185328c7cd320ca31cf952418c73d5490631b798e418c6dd6390631cf950418c73d5410631b798c418c6dd6310631ed504418c6dd65cc631d7597318c6f565cc631dd597318c6f560cc631ded42508c67e64942319f592508c67e62942319f58a508c67f64542319f191508c67f62542319f189508c75f3154231af990508c6bd6414231bb988508c6ed6214231de540508c67e62d51319f58b544c67e60d51319f583544c73f5495131bb98a544c6ed62951319f992544c67d6395131d758e544c67e6295131db98a544c66e62951319f58a544c76d62951319b58a544c67d6195131dd586544c67e60951319f582544c73f64551319fd8d544c75f63551319fd89544c67c62551319fd85544c77761551319fd81544c67c60551319f994544c73d5415131cf990544c67e62151319f588544c67e60151319f580544c67e65d0d31cfd53434c73c54d0d31bd987434c6f561d0d319f996434c67c6550d31cfd51434c73c5450d31bdd85434c6f46150d319f994434c79d4310d319f993524c67d64d49319f983524c67d60d4931af992524c6bd6494931dbd4a524c76d52149319f990524c6
  | 32 => 0x1be580531075e53d0c41d754f43106f661d0c41bd587431067d6590c419fd95431075e5310c41d754c431079d4310c41bd98443106f56110c41dbd4a521067e63948419f58e521067e60948419f582521067f63548419f18d521067f60548419f18152106de6314841b758c521076d5214841be98052106f96014841db94b421076d52d0841bd98742106f561d08419f596421067f6550841db948421076d5210841eb50842106f66110841bd584421067f65cc8419f997321067d65cc841af99332106bd64cc841d794f321075d53cc841bd98732106f561cc8419fd96321067e658c8419f59632106be648c841af592321076e528c841db54a32106f6618c841bd586321067f654c8419f595321067c654c841d794d321075d534c841db949321076d524c8419fd94321067e650c8419f59432107cd320c841af592411073e5490441bd59241106b56490441dd95241107b654904419fd9541106bf6550441cfd95411063f6550441afd85411073e5150441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141107b74350441ed90d41107b54350441ed10d41107b74250441ed90941107b54250441ed10941107b76550441add9541107376550441edd8d41107b66350441ed58d41107b46350441edd4d41107b65350441ed54d41107b45350441edd8941107b66250441ed58941107b46250441edd4941107b65250441ed54941107b45250441edcc941107b63250441ed4c941107b43250441edd8141107b66050441ed58141107b46050441ed50750107b54194041ded42501067e63940419f58e501067e62940419f58a50107b541540419fd8d501067c63540419fd89501067c6254041cfd0550107764154041cf50550107754154041cd50550106de6314041b758c50106ee6214041bb58850107b54114041de54050106ee62d5331bb58b54cc75e63d53319f98b54cc76e62d53319b98b54cc67d62d5331db58b54cc66d62d5331dd58754cc67e60d53319f58354cc73f54953319f98a54cc67d62953319f98254cc67d6095331cfd9154cc67f62553319f18954cc67f60553319f18154cc73d5415331cf99054cc75e63153319f98854cc67d6215331dd58454cc67e60153319f58054cc73e5490f31cf55243cc6f66190f31bd58643cc73e5410f31cf55043cc79d4310f31bd98443cc6f56110f31af99352cc6bd64d4b31dbd4a52cc67e6494b319f59252cc67e6094b319f58252cc67f6454b319f19152cc67f6054b319f18152cc76d5214b319fd9742cc67e65d0b319f59742cc76e52d0b31db54b42cc6f661d0b31bd58742cc67f6590b319f99642cc67d6590b31cf95242cc73d5490b31bd98642cc6f56190b319fd9542cc67d6550b319f19542cc6df6350b31b718d42cc67f6510b319f99442cc67d65
  | 33 => 0x8d50d067f62543419f18950d06de6314341b758c50d06ee6214341bb58850d07795014341bb98b53906ed62d4e41d7d4e539067e6294e419f58a539067e6094e419f582539067f6254e419f189539067f6054e419f181539075d5314e41d794e439075d5390e41bd98643906f56190e41d794d439075d5350e41bdd8543906f46150e41e750c43906de63d4a41b758f529076f5294a419f98e529067d6394a419f982529067d6094a419fd8d529067c6354a419fd81529067c6054a41db548529076e5290a41db54a42906f66190a41bd586429076e5250a41db54942906f76150a41bd18542907ad4210a419fd97329067e65cca419f59732906be64cca41af593329076e52cca41db54b329067f658ca419f996329067d658ca41af99232906bd648ca41d794e329075d538ca419fd95329067d654ca419f19532906f7614ca41bd185329067f650ca419f994329067d650ca41d794c329075d530ca41db948329076d520ca41f34c832906f6610ca41bd58432906bd65d0641cf59741906f565d0641dd59741906f560d0641ded42509067e63942419f58e509067e62942419f58a509067f63542419f18d509067f62542419f189509073f4154241b798c50906dd6314241bb98850906ed6214241de540509067e62d4d419f58b535067e60d4d419f583535075f5394d41bb98a53506ed6294d41d754c535067e6214d419f588535067e6014d419f580535067e65d0d41d7d4e435075c5390d41bd98643506f56190d41d7d4d435075c5350d41bdd8543506f46150d419f994435079d4310d419f98f525067d63d49419f983525067d60d4941b798e52506dd6394941dbd4a525076d52149419f98c525067d63149419f980525067d60149419f997425076f5290941db14a42506f66190941bd586425076f5250941db14942506f76150941bd185425067e6510941eb508425067e65cc9419f597325067c65cc941d7d4f325075c53cc9419f996325067d658c9419f196325076f528c941db14a325067f654c9419f995325067c654c941afd9132506bc644c941d7d4d325075c534c941dbd49325076c524c941bdd8532506f4614c9419f994325067d650c9419f19432506be640c941af59032507cd320c941bd98432506f5610c941bd58341507b75190541af582415067e63d41419f58f505067e62d41419f58b505077b5094141b7d8d50506dc6354141bbd8950506ec6254141b798c50506dd6314141bb98850506ed6214141de540505067e6314141d798c505065e63141419f58c505075d63141419758c505067e6214141db988505066e62141419f588505076d62141419b588505075f5394c419f98a531067d6294c419f982531067d6094c419fd89531067c6254c419fd81531067c6054c41d754c53106ee6214c41bb58853106fa6014c4
  | 34 => 0xcb5e63150329f988540cb6e62150329f984540cb7661150329d984540ca7d6115032dd584540ca7561150329f980540cb7a60150329e980540ca7d6015032de580540ca7960150329f992530ca7d6494c329f597430ca7f6590c329f596430cb3e5490c32cf552430caee6290c32bb58a430ca7f6550c329fd94430ca7d6510c32cf950430cb3d5410c32e750c430caee6210c32bb588430ca7e64948329f592520ca7d65d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd63908329fd95420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420cbad4210832b758e320cb5e538c832bb58e320cacd638c832db94e320cbce538c8329fd95320cadf654c832d7d95320ca5f654c832b7d89320cb5e524c832f3d09320cbce424c832f3509320cbcc424c832bbd95320cb6f654c8329bd95320caef634c832f3d8d320cb6e534c832f394d320cbcf434c832f390d320cbcd434c832f310d320cbcf654c832b3d95320cb4f654c832f3d91320cbce644c832f3591320cbcc644c832f3d51320cbce544c832f3551320cbcc544c832f3d85320cbce614c832f3585320cbcc614c832f3d81320cbce604c832f3581320cbcc604c832f34cb510cbcd3294432ddd46510ca7e64944329f592510ca7e60944329f582510cbcd32544329fd91510ca7c64544329fd81510ca7c6054432af990510cabd6414432f34c8510cb755114432be980510caf96014432f34cb500cbcd3294032ded42500ca7e64940329f592500ca7e61940329f586500cbcd32540329fd91500ca7c6454032d7cc9500cb6e3254032d74c9500cb6d3254032d34c9500ca7f61540329f185500cabe6414032af590500cbcd3214032bd984500caf56114032de540500caee62d4f41bb58b53d075f5394f419f98a53d067d6294f419f98253d067d6094f419fd8953d067c6254f419fd8153d067c6054f41d754c53d075e53d0f41d754f43d06f661d0f41bd58743d075e5310f41d754c43d079d4310f41bd98443d06f56110f41b798f52d06dd63d4b41dbd4a52d067e6394b419f58e52d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41db94842d076d5210b41eb50842d06f66110b41bd58442d067f65ccb419f99732d067d65ccb41db94b32d076d52ccb41bd98732d06f561ccb419fd9632d067e658cb419f59632d075e538cb41d754e32d06f6618cb41bd58632d067f654cb419f59532d067c654cb41afd9132d06bc644cb419fd9432d067e650cb419f59432d06be640cb41af59032d075e530cb41d754c32d076e520cb41db54832d07cd320cb41ded4250d067e63943419f58e50d067e62943419f58a50d067f63543419f1
  | 35 => 0xd6414332bd98450ccaf56114332de54050ccaf661d5232bd587548cb5d63d5232db98b548ca7e61d5232dd987548ca7661d52329f587548cb7561d52329d587548ca7e60d52329f583548cb3f54952329f986548ca7d61952329f982548ca7d6095232cfd91548ca7f61552329f185548ca7f60552329f181548cb3d5415232cf990548cb5d6315232db988548ca7e61152329f584548ca7e60152329f580548cb3e54d0e32cf553438caee62d0e32bb58b438cb3e5450e32cf551438caef6250e32bb189438cb9d4310e32cf952428cb3d5490a32b798e428cadd6390a32cf950428cb3d5410a32b798c428cadd6310a32eb508428cadd65cca32d7597328caed65cca32db597328caed60cca32af993518cabd64d4632ddd46518ca7e64946329f592518ca7e60946329f582518ca7f64546329f191518ca7f60546329f181518cb755114632ded42508ca7e64942329f592508ca7e61942329f586508ca7f64542329f191508cb5f32542329fd85508ca7c6154232af990508cabd6414232bd984508caf56114232de540508ca7e61d51329f587544ca7e60d51329f583544cb3f5495132bd986544caf561951329f992544ca7d6395132d758e544ca7d6295132db58a544ca7e6195132dd986544ca7661951329f586544cb7561951329d586544ca7e60951329f582544cb3f64551329fd8d544cb5f63551329fd89544cb6f62551329fd85544ca7c61551329fd81544ca7c60551329f994544cb3d5415132cf990544ca7e61151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d329f996434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d329f994434cb9d4310d329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e65909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424ca7e6510932eb508424caed60cc932f3d4a324cadd608c9329f993514ca7d64d45329f983514ca7d60d4532af992514cabd6494532ddd46514cb7551145329f990514ca7d64145329f980514ca7d60145329f993504ca7d64d41329f987504ca7d61d4132ded42504cabf6454132af191504caf76154132bd185504cabe6414132af590504caf66114132bd584504cb7950141329f990504cb3e64141328f990504ca7d6414132cf590504ca3d64141329f984504cb7661141329d984504ca7d6114132dd584504ca7561141329f98f540cb5e63d50329f98b540cb6e62d50329f987540ca7d61d50329f983540ca7d60d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3d5415032bd984540caf56115032be980540caf960150329f990540cb3e64150329f98c54
  | 36 => 0x45429f58f5150a7e60d45429f5835150ade6394542b758e5150b775194542dd5445150a7e63145429f58c5150a7e60145429f5805150a7e63d41429f58f5050a7e61d41429f5875050b7b5094142b7d8d5050adc6354142bdd855050af46154142b798c5050add6314142bd9845050af56114142de5405050a7e6314142d798c5050a5e63141429f58c5050b5d63141429758c5050a7e6114142dd9845050a7661141429f5845050b7561141429d5845050b5f5394c429f9865310a7d6194c429f9825310a7d6094c429fd855310a7c6154c429fd815310a7c6054c42d754c5310af66114c42bd5845310afa6014c42be5805310b5e53d0c42d754f4310aee62d0c42bb58b4310a7d6590c429fd954310b5e5310c42d754c4310b9d4310c42bb9884310aed6210c42af5924210b3e5490842bb5924210aad6490842db9524210bae54908429fd954210abf6550842cfd954210a3f6550842afd894210b3e5250842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210baf4350842eb90d4210bad4350842eb10d4210baf6550842abd954210b2f6550842ebd8d4210bae6350842eb58d4210bac6350842ebd4d4210bae5350842eb54d4210bac5350842ebd854210bae6150842eb5854210bac6150842ebd814210bae6050842eb5814210bac6050842eb50b5110bad4294442ddd465110a7e63944429f58e5110a7e60944429f5825110bad42544429fd8d5110a7c63544429fd815110a7c6054442b798c5110add6314442eb5085110b755114442be9805110af96014442eb50b5010bad4294042ded425010a7e63940429f58e5010a7e61940429f5865010bad42540429fd8d5010a7c6354042cfd095010b6e4254042cf5095010b6d4254042cb5095010a7f61540429f1855010ade6314042b758c5010bad4214042bd9845010af56114042de5405010af661d5332bd58754ccb5e63d5332db58b54cca7e61d5332dd98754cca7661d53329f58754ccb7561d53329d58754cca7e60d53329f58354ccb3f54953329f98654cca7d61953329f98254cca7d6095332cfd9154cca7f61553329f18554cca7f60553329f18154ccb3d5415332cf99054ccb5e6315332db58854cca7e61153329f58454cca7e60153329f58054ccb3e5490f32cf55243ccaee6290f32bb58a43ccb3e5410f32cf55043ccb9d4310f32bb98843ccaed6210f32cf95342ccb3d54d0b32b798f42ccadd63d0b32cf95142ccb3d5450b32b7d8d42ccadc6350b32eb50842ccabe64d4732af59351ccb7751947329f99251cca7d64947329f98251cca7d60947329fd9151cca7c64547329fd8151cca7c6054732dd54451ccb7b50943329f99250cca7d64943329f98650cca7d61943329fd9150cca7c64543329fd8550cca7c6154332af99050ccab
  | 37 => 0xd79524310f9e5490c439fd954310ebf6550c43cfd954310e3f6550c43afd8d4310f3e5350c43b7d954310f5f6550c4397d954310edf6450c43e7d914310f5e5450c43e79514310f9f6550c43a7d954310f1f6550c43e7d894310f9e6250c43e75894310f9c6250c43e7d854310f9e6150c43e75854310f9c6150c43e7d814310f9e6050c43e75814310f9c6050c43e750f5210f9d4394843dbd4a5210e7e61948439f5865210e7e60948439f5825210f9d43548439fd855210e7c61548439fd815210e7c6054843e750c5210f6d5214843bd9845210ef56114843be9805210ef96014843e750f5110f9d4394443ddd465110e7e62944439f58a5110e7e60944439f5825110f9d43544439fd895110e7c62544439fd815110e7c6054443e750c5110eee6214443bb5885110f755114443be9805110ef96014443e750f5010f9d4394043ded425010e7e62940439f58a5010e7e61940439f5865010f9d4354043cfd0d5010f5e4354043cf50d5010f5d4354043c750d5010e7f62540439f1895010e7f61540439f1855010f9d4314043bb9885010eed6214043bd9845010ef56114043de5405010ef661d4f42bd58753d0b5f5394f429f98653d0a7d6194f429f98253d0a7d6094f429fd8553d0a7c6154f429fd8153d0a7c6054f42d754c53d0b5e53d0f42d754f43d0aee62d0f42bb58b43d0b5e5310f42d754c43d0b9d4310f42bb98843d0aed6210f42b798f51d0add63d4742ddd4651d0a7e63947429f58e51d0a7e60947429f58251d0a7f63547429f18d51d0a7f60547429f18151d0b755114742ded4250d0a7e63943429f58e50d0a7e61943429f58650d0a7f63543429f18d50d0a7f61543429f18550d0ade6314342b758c50d0af66114342bd58450d0b795014342bd9875390af561d4e42d7d4e5390a7e6194e429f5865390a7e6094e429f5825390a7f6154e429f1855390a7f6054e429f1815390b5d5314e42d794e4390b5d5390e42bb98a4390aed6290e42d794d4390b5d5350e42bbd894390aec6250e42e750c4390abd65d0a42cf5974290aed65d0a42db5974290aed60d0a42b798f5190add63d4642ddd465190a7e63946429f58e5190a7e60946429f5825190a7f63546429f18d5190a7f60546429f1815190b755114642ded425090a7e63942429f58e5090a7e61942429f5865090a7f63542429f18d5090b3f42542429fd855090a7c6154242b798c5090add6314242bd9845090af56114242de5405090a7e61d4d429f5875350a7e60d4d429f5835350b5f5394d42bd9865350af56194d42d754c5350a7e6114d429f5845350a7e6014d429f5805350a7e65d0d42d7d4e4350b5c5390d42bb98a4350aed6290d42d7d4d4350b5c5350d42bbd894350aec6250d429f9944350b9d4310d42bb5834250baf5290942af5824250a7e63d
  | 38 => 0xa0004004003c00a0000000002800e003400000000000020001000800000000020028000000400c0000000002800300040000048014000000600680000018003000000c0000004000402400000050044012000400700000000014002000c0010000000002c00f00080000008000002400200040150000000000000200000020014007001000e00000030000000001c004002c007000c00000140010000003003c002000000000340020014000001c003002c00600080010020007000000000080000008006000400400280000004004001800e001c003000c003000c00b0010001002400000040020004000000800000200010004009000000200180040008006003c005002c0020004000000c0000008001000000100000010030005002000200140000000001000001f002c0000028001001000200000060014000000000000000000004006001c01300180270000001000c0020008003004c00100300010020001000000a00040010032f661d4b43bd58752d0f6f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0eee62d4743bb58b51d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0f7b50943439f98a50d0e7d62943439f98650d0e7d61943439fd8950d0e7c62543439fd8550d0e7c6154343bb98850d0eed6214343bd98450d0ef56114343de54050d0ebd65d0e43cf5974390edd65d0e43d75974390edd60d0e43bd9875290ef561d4a43dbd4a5290e7e6194a439f5865290e7e6094a439f5825290e7f6154a439f1855290e7f6054a439f1815290f6d5214a43bb98b5190eed62d4643ddd465190e7e62946439f58a5190e7e60946439f5825190e7f62546439f1895190e7f60546439f1815190f755114643ded425090e7e62942439f58a5090e7e61942439f5865090f3f43542439fd895090e7c62542439fd855090e7c6154243bb9885090eed6214243bd9845090ef56114243de5405090edd60d0d43e7d4e4350ebd6090d439f9875250e7d61d49439f9835250e7d60d4943dbd4a5250ef66194943bd5865250f6d52149439f9845250e7d61149439f9805250e7d60149439f98b5150e7d62d45439f9835150e7d60d4543bb98a5150eed6294543ddd465150f7551145439f9885150e7d62145439f9805150e7d60145439f98b5050e7d62d41439f9875050e7d61d4143ded425050eef6254143bb1895050ef76154143bd1855050eee6214143bb5885050ef66114143bd5845050f7950141439f9885050f6e62141439b9885050e7d6214143db5885050e6d62141439f9845050f7661141439d9845050e7d6114143dd5845050e756114143af5924310f3e5490c43b75924310e9d6490c43
  | 39 => 0x4400000000000008006001800900280000004003000800100000000004002000800300080000008000000400000000040004001000000000100020000002000400500200020004000002c015001c000001c000001c0060008005000000000440030000000006000000140000000001002000000300070004000000000000040010000003000000000000010038028000c0080008005002800200340070014002002000100080040028003002400200040010000001000001100240000008002000c003000c007000000400000010000000000800000080030000003004c0080074003001400200000060060000002c0030000002000000b00100010000006000400100100000004001000000000100000020000000c000000000b0010000000000a000400a003000100040030018002002400000040190018002004c00600040000008002000800c00000070004003000800000240000008009002c00000100030010005003001000140000014002001c00b000000900000080000001000400a0008000000800100000060000005001c001000c00b000c0000008001000000500100050020001002c00000800020034001000c00300040040034000000003f002000e000c0020004001001000300140020038001004001000080150008000002800300080010034009003400100200010014001004c001000c001000000b0000002004c000000000b001c016003c000002c006001400000000050004002000800700440020008000000c00000140000000002000000a001c011001000100000000034000000c007000000d0014002002c00000200000018001000400000000410008000001000100300030000003000c0010000000000c00300080000000002002800100080020008000000c008002000100080020038002001400200240060000004000c001000000100100120014012001800a001400000100140008005000400000040020000004001c004000c001001c000003000e001c0010004005001000500080030000003000400100100010000009000c0000000002002800000440050000001000000000000190018000000400200000000010002000800200000030008000002c0010000000000400e0010000003c001000c0010020000001000500080040004000000400500000000014000002c0000000000005c00100000030010005001c00000040000000002000000d000000500000110004002001000200080030000001000c01100000010000002000c004000000300000020008001000000700200000000003001800a000000500100020004007000c000002c01200080010014000000800500080000004000000000700000020000000002800000000010010002000400e00840000004020000400000140000008004002001d0068
  | 40 => 0xf000c00100000030004007000000500040120004001001c00100040020010000001800100600000000003000c000003800000f400000000000000006005400600140000010010000801a000c03000480000000001000400f00b4001003c0020008000003003d002c001000000500000030000002001000200040030000002000800800280000070000000c00000000000000000000401300000010000005000000a000000300000000000000000000a000000600040010008018000000000040060000000001000300380000004004000c005000800200200000004007000000600000000010000000800c004000100100000010001001400a0000034002c0050010000002800000040160000003000000400080000000000000c009003c00000000000010000000400c000400100000000040005002c000000c0040008001000800f004c00100000000000000000000400180030004000000000100000030008000000800d0000004005c00a0018006000800000140050014009000c0030018001000000100440000000002003000500180020000013000400200100020000003000000000000000008001000001a000c008000000100140040018001002000300000010048004004400b00040000018002000c00500080040020003001000700040010048007003801000100030000000000c0080008001001c009000000e00000090010000002000a0010005000000500200070000003004c00100000000008013000400500000060000000004c00000200010008000000000000000020010002000c0010004009000000800000070018001001400200100040000002000800e0008004003000500000000000001004c0010004000000000400000000004001000000e0020002001c001004000200080000000000000400300180000000004001800200000000014002000000300000090000000000000100040020040003000000900200000008002000000100040010000008005800300000000000009001c00000040020000008000000100000000054000000c00200100000018002000400000f000100dc002000c0020020001000000000000000000003002400e001000a0000000001c0070000003000000000040030000001000000a0000002000001a00280070000000000400a00040010000001000c00100000050004001000000000000010004003001000f00000000004000000001000000010024005000000500140070014001000c00200140040034002002c001000000200000050048003000c001000c0000018001001400000000030010004001801f0014001000c003001000000000010004001005c0010008006005800000980000014018001c00c0058006001c0000024000000000d00180000000000000c00400000010000004
  | 41 => 0x30010003000000000000010008001000400000000010028002000400100240020004000000c00200040020000002000800000000000008000003800000080000010000002c001000400500100000000000000c0000004010000000c000003f0000000006c00c0020005000400300140020000000001c000000c00f0000002002800100000120028000000c00000000000004003002400000080030004002000003200040100024004004000300100140000000000c01200080010008001002400c000000b009c0040028011000001400200040000000000000000440030010009005c00100140010018001000400000000010000000002c004001400000200020030000000c000000000000100020024000001c0020000002007400100140000008000000000a0004003000c000000c0020000000002c0010004007004c000001800300040030008006001c03400100000020007000000000000090004009000c00200280340078000000c0030004002000400700000000008000000800500040000014000000c000003800000140010008000000800700080050010000000800700080000000000000000000600010004006000c00300040020004005000c00500040000004005000400000080010000001000c000004801c003c000002000e00140000014001000400300040000014004001000000000060008001000800500040000090008000000000000070000000000000200040000000015001400c00000050074007000000100000050054003002800c00140110010003001000000040030008000009800d001c0250000009000c0130020001000800300000040004004000400200000010004001001400400000150008002000c00000000040010005003c00500040030000001000c0020000000000c0090000000001800000000010008000009c001000000d0008012000400300040010000000005c0020008000001400400000000000001000c00300000050010004000c014001000d00000000008003001000a00040020000003000400600000020000001000c000000c00100040000004000001c0000004009001c00500040020008000000000300180010000001002800000080000014008000000600380000004009000000200000000018004001400700040030004004000c010000c00000080080000000001400000280150000000000800900240100004000001800000080030024000002800a000400d00000010020002002000a000c000000000000180000004004000400200480000054001000c003000801600400050004000000000a0000000000000100000000004013001c000001800000b40040000000005000f003000c000800a00000000000002006c0070000001003c0010008004000c000007c00200000020000000000
  | 42 => 0x1c000000c00300000050004002000800a005c000001c01a00100030004000000000000080090000000000400600100000008000000800100000030000001001c0010004000000000300000000000002001c00000300000018006001800300040070004003001c0040004000001000c000c000000400e00000000024003006400100000100020000000c00500000020000001001c00000000020040002000400600000080014000000c00400080020000018000400100000080000002004400700000020000000000400d00100050000000000c00100080020014002003c0000010000001400100140020010006000c00000000050008005000c0010014005000000100040000004000000800400100090024000000000c001400100100000000002000800000000010000003000c004000c00e000001300000010000000000400200040010010000002400c005000000240080008009000000200000070060014000400100000000000002000000100000020000003000000600080020000004000000100100090008005002c00400100040000004000400100180040000002000000300040030000005000c001009000000000030004010006800900140000018009000c00100940000010001000000c000400b00000000008001001000400100050008000000c00b00000000020009001000000b00010000001006400d003c005001800000000220024000000800700040050008000000000b0000000001c0080000001000800e000c00000100090008001003000200040000004000000c000001800500080020000006000001b00040010008001009c000000c000000c002001c01a000c003001c0050018000002800d000000000080000008000001c000000c002000000100000010000001001800200000060008000000400500040040018008000c00700180170000005000002a000400a0008000000000100040070000000002c0000018001000c0040000010000400900080010000003001c00000000320000021001c000001000000140060000001003800000000040068006002800100040000004001000c00d0010000000c00100080000000000000800000080010000006000400000040020020004001c00000000040000000004400000000000004010000c005000c01500000010018000000400f000000500040010034001002800b001c005000c001000c002000000100100010014000001c0000038000001000e00000080020000000000000080010004000000c0010018006000800100040020014001004001b000400200040010024007001401300000040004000003800100100000000009001c00000040000004005000c00000040010008007000801500240040034000002400700240060008011000c00a00180020020003000000
  | 43 => 0x212c0e280002a144fcc3a61def17680c60000110805be5ddca1712b70000698400004e600000000e3b800000001b282728000000000002fc83fc22040ca4456927c2b9428f80001b36052e7d309360fa01ce0000068a1f2e0000348800014182f340000000131000004718c5890842b040000b8d0e6f1c626028fb716a92e681b68ff10000000080d0f2f20820000000000004482d3600009a106e7024465a01de9c31327c3d4085d0000384c608c0000f580acc5ae80da1137391c6f98d6b0cff2f1c57b442e000b38ec7cc44ff80000000181c000077114cc000000009e2000058cc82c17f1310c4be48d619022714094800b159528824970af420321198000000016f826e20000c328070174818800638000212050fcf629d17340e38fc000111034886a28b390d112d5e3d08000000000000c0800012420e4c000057f0c06365876a094f8c271b5a000000000003d0e00000ff959b2f3a42702041e78000000000001e0b2baa00607e21d0e1fbe20e04411fbe00000000e181f8022c636640001ad100003c04b6b176000000000ede961d130c04a434f9fb60000000039c9416112424005c7913a2f5e78846c100000000661c8e100000000000069b00000c0200007ad86fc24ca03000001ec027c24c300000f7c0e7a0000e5a852200006e1803a9b9212ba230864905ce1d8609680a317cc00005b38f1d95cf03ea2a90000000000003b840000000383e15040c99d3f2e5e000101f800000008010419060f332e6a4874284a000003ec068c20173ce01a1c000104c00001ff02b583a80e2c45c406880000fce0000f5f8da924e00000587186b3530782000009f63a8a000008789a93958283c3ca0edc00000014007001c00d001c0000004002007000000080050004003000c0030008000000000000000040000000002c0000038000000000100100020004004000000800000020000000000c000002c00b00040080004003001c00b00100020010000000c0000000002000c005003001700040020000002001c00300280000020000000800200040010058008001c0130000000001000a0030005001c001000c00000000030008011000000200000000004000000400800000000000000002800400000000040003000000100000000020016001000000000060014000000000000100000028001000800300080000000000000c000000400200140150004006001800300040010004001003000100000030000000003400000000100014000000000a0000000000000100040000000008001800100000010020001000000b00100090000000000400000340020000000000000200000040010004000400a000000000040010004001005800100140010008006000c000003000800240000018002001c000000c00c00140070000001000000100
  | 44 => 0x7f682bd17fc1f44adc119a38a000849da15f90ce27f80a57891e0c7416210119354338028289720743000079bcdd98000332a00005e81d030f220000edb892300004ab8000044c00cc1c410349bce0000000026406d52fe00e6c72798731ac61e28a4c055a36a22e28e25800000002cfcd2014a7000017d82bb0e2f04ec6068000000000006a340001f2320e647a0a47000000003d70000000000007f14000000019920000d5e10030000000000000000000000000002623fbc000069615c9295c0000c8a80000000000017714c613087d9894d800000005154ac017640c643320b458000085c694c73212562fb818d00000e8000000000236107b141a59643309f102fe84d94a2e84262950034884701a4350e34fc3cb01042ff4438ce4f18991efc2ef02881001000000004ef0878000039f800000000000000043d800015d6456400000001cfa127400000001d564020ecb800036d4707430d0cdf142a49e496d043b360e00c1004885300005cf060f0ef1000011a8000000037dc32749f381862b146a78fa084c434865bc400013ee0000603cd809597000000005800357242c7cbc7f289713ae8000040e0c662a9c000059700000ca213d893d80c10000000000009f538206e1c00004c221aa0ec0000000000004808c9f966115ec1ae41c4800000000000000122d00006ef45d39d3d0000792465d199e04902738537965007c0229048717233bc008e092813ac05fc5c14e998e971a428044a3381d9000007b4c84017100000000000204531ac00004a7000038f04a4842b800017180ba4e588d521c700000c2a80000000383491b0cf20aa0750871a84ad16bc00002808fa115825b548a6985300004b24ece865b243e0000000000027ca5cd4f7114400000533400000001e942560388800033207ba4a8c203824a46e0000002360000035022f9dc22ba80e040ee8a36128c5478d39134125d81f6885580000000006c0000fc600004fb000003221eb20000d1b865c0dea6d540001d88284c0000526203b2798000000000001d9a3c8c00019d40c1823b0f2c94b42668496081d0ea000000000000000034965e9cd3b8e9d39aa23a85d69b1c39722e840a2936f346241c0eb6025121ca7788055889e3de44b70653903d1b226e04b1a9ef92bd81baccfe8eb6314a72f4af01959311063f4ab70db912705dfc8569e6b02aa2b34e8a00003d080860fe198ad24da0f6cde40fd1285e6d8016b800032b66f8400010ce091400000d618b203a837e4000000000000000836000005b64eb800000000ca000000000000000000000000809022a5e0c000048d00002984da19461000000007488ce7240c689c00013bd287400000000000000047b4000000005040000000000000004c2800005ff000023e4e580000000035d48eb80000000000000014d60
  | 45 => 0x343c3d2cfda8a9c35801bdc2f311ad18a07ecc16796ac0f423b100001bb2000054ec5b884c5063e2adc00008a7122608000000281106c00e8b0f8000000000000001e7400000000000000031820000000000000000000ee580002aba010c00002a0000070d083a14c80566403095d9fe72e6c0eb08f61ddd000010ac00001821c667cc0494091020a800000000d51000a000000000fa0ae200000000be41e166f2825a07dc34b034ec9a99ec411124f7c214010e19fc1a704bb1c800fde00cc8570d90384629000229e7119c06248fec818e094a4ac03e4000017b639a03db94ff353841a01c39cfe2ee84d681ee8eeb0000387c0000a0325a615b8c6d000000000000ba11adb156838b824609da00fa000000001f236b20000c88824e24be3db8ca61879362a5d8811900001b3e30a4e5700003248000029a19f832c600007999822000071e899600001da20dd035383833c3e1a54000000003523b406a818f11dde170493893c2356a3cc8c179e892a385dc000a9eed192a7cdc729800000a824b41c78b2600007af848380000000000000000000000193823d8b65000070fc4a90880256835140000c01000000000000000000065bc00003f2300e20f865985003e285718d6d0000208e62ec8098167000072800ff15cc0ca600005be800000000a0c00013800c705aec6ee87f400001e400000a803a50246c5298b9104a02dd05e611b30000000022380000000000000000003c867dac00013600000366000001641a1c6470000052d000046f0dac026520dc298c69a000037800840ce68be80000000056803203b0c1e5c37983003da20000656992330e839e059487a240ea6d68c33963908fa74b802200000000000000000003a580000c740000000016344cc800000007b988e980000ce8706c1208fba0000470c0000bd2216c0cb45f806b72d8c2b2000018ec126a576400000003fb06ddd03c00002bc6267874503f700001d900a4106a317e0d3c1b718391b628004aba11a638c26388e0d1932000052dc0749ca3066a36c0801000000000000c5782d4000080c4d77000000005f600ae9a9a000000000001a7d0000000083c00000000000061d1dfe3944000033f87ca0c7c0000000000000000000d8d17eb1c4a26900001f911c464124f100fb6000007801ea8000000000003e0194807640b24585800000004b80000000000008054f6f88192afc30f0000038d2b020230000000037462a4ceb0000037ca00000988000354c0000be51303061e7728ad9017300003bc8aab166209360000a7b0b1400007470000155b0bae2384d8e8cef34fe36fc1b01c8f1ff04af0ba00e5418fa00003ab14c30000348c8b600002a321af800000002ce800000000000277409acd9583cc3d102fd873499ac1b6665e046c168f37626eb49149456177249dc
  | 46 => 0x4bed172411de2b00c1a1dd5354002701920fb2062a2198b75160f2e540f4c9ee88612fc6698ccc917952fc0286cf901ff329a855cc35800002d0c797cd7e0cd809ea688477e97b4280614480000be01bb800000e38dd1017c6280ae10efe048e51ec193000000006c3081999de00000000000173d0a6a08dc722819831840000df8800000007640f081d7f00000bc8d659eac00000a985170bfd10ea00002de000000004b04fe6800000001a18818911d0b5859940001c050f8e000000000dd2904791c000000000000000000000017521aa000000000000000000000000000000000002b70b560ca80000ef3000030b8000060300000000000000000000000b910d8417825b6c85c0000000038b0000000000000000e358e8129b0660c4868000302c5bd01b41552006222641b3829527d60f1c6650000004e7e40d1c01961e6233dc9a014d031c81cc8f64980c2b0e5a103fd1f7502b80000f7c000000000ac40000b3728ee00000000000000000000000000253200004e11bb9277e3ef8000036307d4420c1020000289c5324000072d00003468000000005b80000000075008d65d3800000000000000025f80002bf826a800009c937f2000000000003d8234f80001324285a4f0c17692a740f467b000a0c8d37c40000a94828e311e5b206fa0a9b00006c600001abd1ca4000000000002a9e185c00000002d50394429e03ab216e494c2d19a0a00901b44314032100fe751c760167a0718625cf3f800001b200000000000405e00000000afc0000000000000001c4e00000fe800016b066e80000035329e0000dee0000138a0000e3700ba22800d64d62000000000000d0681bd117614ec865867500000e1838080001fd8414c00008f400007d2051f80000b6a5f98000000000003c3ccb91ed60d5a3304c870d2009c82544e728ebf00004978f05037c297e332cf6a14f400007824000000009da1eb073390942eac0000000000000001ddce208b9500003e1cd7c0e6606d8000000000000000000000000000000315c000084c000000003d70000000015480000df8000074f0c0a00860694779800012c027c6814837f800000000000000206233b0000009e074218c400006cf00892a1a28ac6a2000000001740e7a80000000000000004213b8c000000000000000793c0000000134e00000000000031e07dc3a3000021d4000016380001e4451b0f2083a706b40000d1909ba29080000a700000158c00005c284c7000000001511119000069748b2000037ba47e02f10000196819a89d2000013c60ce000000000fe6000078306e300004e7020d8fc30608000000007d405de4e3858600002c7007f0d1e000000007a28616800000000000000000018580000b9387d0082c7f4cb3e19a42b4c5b509d680000d802a48000084005c06e547b591c9
  | 47 => 0x171b000024104db0000000000000000000246424200000000407400009fc04db2ce629640000888000000002a88d2606a600009870000403407ec00014b6000079b064f8d2531cc000000005d600000550e3888ed13ba4b3c0000000000000005d300000000000010e930100004094d07000000000c349549f9c000024b0000000000003b0807782d634ec38ac4d8857200000000a8580000ee6437c1840ded1774186c1079127162a74945b00f37081818a8fbe953307822ae4b748b1c254200006419fd50000000102c0b280fa600000210c5e1da876d8ae08000000077b4ed30ff72b2221041f29be815846c6497b85b900b629285b112e139ac691800014c00000302c00013a51f687ce4eaa0cbe00004e747888aaa16ee00002c30343122800000000000249047c00000c400000000000000001ea600007880886203c05bc6c3800020e26e78cb0816c00000000d1b06941a261478a6a8afd05fa521cddc1496000008bc52c04d500006f0c4399b6f1cf451c06ad000035a400001571d7105b403901f70f2100001c84c861f1911b620800000ebd33020000e1503f9000079d89458bc22f0e5b8c75d13b9000000000000c7e092800001eb0ce411fa4768b29854c2f580000459090612ee171c80c1bd0036a15e85f70f9014620000000164000006d3c9ab8d7a104c034000005e5000024f44e594ec21f600000000a5f019c22d4907198a000014f45e4123400007cb0c0f042200000000000171611421b7c98900000000062088e09970000000000010b0227e1cf0710944318b833c42f48f0d069c0000f02000000e22640ded000035840000d40155019c45dcc2409a062e7c47a4000000030ac28380df1ae31b825958000016211e40000000000007d014fc00000000000000000011221a186a0c67580003982701076c8659079411c902e0000376a2c8c09403ae39f04968d7114d324745084114801f0000685031a80001de00000000000016ec6b24b96000000002c68a47820b34225fdcecd83df25fe5810a518da534020460e31086000e80000d91813600004a0ca95000000002db000006081c4c55dc0000c43104a215000017fd238247c84a680003c0e0e3800018ab355c0000000000000000934d788000000053a40930000251a632495d019900004f543960dc03e7e000044d89f800000000000000034183ab0e569667358632fc00010621f4c0130adb9c7f311801b8123042f2a3e4298669816d004c3030c8c146a3950463026f84761bf43d94a1e88043728000038a0000000072346cd87b83b0655907af9ffe2eca5f406f5864114a02864f510d93349a000079d0000396e20181d483ba1b3435a83c41be72f2c2370cd10d3a3fae40d06df0c8707c65950674028d2f6a5ce469c17d40dfa59e432a92101fb4258
  | 48 => 0x7101e00001c0c0000e420712046a5fd4a0d00000000000012a90a7033c5f94e01800000000000ec20b8d0000250c0000000231408a886d0b3e01c436ec93387ea000034485fa1f3c000022fc39d8d100000000000003a135f400007511ee00000000000000000104000000000000fbc024c000000000001694fae00001f14478c8708000313e4930d8b008b3a486e6c11592df00000398000066b00007dc40000feb0000000000001fa343a00000000f99000000000000000000037c81cc942b0000726424006bf09543fc4c10839f31227414a91199a37440ddccee161522180668dd21ecd1466376d042153208c831d8fe01fb128fe11580d887b4059a4018b3200003a260a689b8019b133e391038605a80680000000000002430759c7a31a2639c4000049f0000139057005980000142023a49d40000038870ccc53852400000104cdc80003cfc000036f000013a844b4000179900004d109d880000000000000000000000554408d80002608735c0d18fd60a660000ba213cf1b0627f49cc08482a5c2f88b7016e2027669b40519000229275444f31e552e0814803c10000001c4740000109d352c68f40001b4b23be0000a1c86052f8400003771585000066dcb6d0000000000006e1887d000000001319600000000000001e05347e37080000ba33fee0000968932f0a4c7a6ced8154b24420000ab8839700003ad4da400003d8605e472e132b0af827340a59b6132a4333082e1c3c02f461700000e0c0000300000000001a320000000010300002b940000b6a17fe00000000caa1b560958e1781a727c80000000000022ca4cd82fc14b11b10780c50b000040bc3c6c0001b023c2e4b1c21f88c03e88000071b8add404800007728cb9000072f10350eb225623538af88fea2a5a727444192a51a6a3ac07fc8000396c1b0c000062c1078000003f1e1800002fa89de18111c6851f88a0864b3e7661bc53c998e178a24cc934010132ae3adc00000000558000000010601f7000000bb2056000016a40001286000000002aa000000000000fca0000000038ec00000000000127092e80003e04000000010be1a8011647ad0a8627f629904cc042c24cc4ca000000002d98139c9910000000025643b319340762796c816800018b059a44450c8209a84a587509c5d19a2000000009541a824f880001358085262e08dd8ab300007444ef99f96068230dce820fe33fd80000d9c931d08a844b85d805b4232e0000c4990f838900000dfe8509116246384fd99d936a663a8c0e8000395e000002980a4284a2b980000a5b000000000000000000000004e305d339e4731c387128922702c7c35b118301b636740001dfb2f6c61dc9c2940e3ba421e8c5a180100000000aa016c4000061b80000000005c6d300000000000014c4000119500002e10000000
  | 49 => 0x579814f00f43f9e40ec45598d300003790f1f8c980a2e217cd111bab218a3f98f158f6f21dc00006fb8085000012c442ea0720cb000001628f8e010800006c494ed2ece753c50416122f3c811820093753f6e149c4649d7e0b988020cf1800005462c1c1e191f6000000000679044000016d80000a553dd800000001ca50bea1fb48ac000012be62f020f1dfc3e081f0504014053ad645b428e96260000087806b8af03c6421a8fd39668161e4e3cba50a203c6e80184ed800000000000a33081f0000000014798d5305a1f3c792059d15427f8434017f30f88644c8c780003b14490c7891dcf0d140000d528000000000000001e303a9865340000221404280a01138691332c2794fb8010031b01a4c7aa97a938e66bd0000000015c80f848c9111430987bdc382800033c41c6ca28000000002334ba6054323fa40a08fd800009e667804c7987d3f501b604f39ad800003684aeb1af700000fd46f30000247c3a90000000003423680d9e86fe00000000c63000029026f60a08000000000000cff1fbf05323aa899e87fb29de592c27f8c5435825d5c000000004ea0000000000000004d74a978000000008f47de17a3031a32284921b7d057c1e481d30000000058c8beb800000007004d12800000001dbc4af1975158e0e6000019a6409400000000000000000000a9010d000000003f497ff000052e80368d0412927da40000293274e0b0492580000000000067a80001d3e00000000000000013348731c4305744e1c6f51eaf2ea011b895111c014c411bc76504bd0df2000074e02540bb00330cc8a00e0bce3ddc7648000105263c81750cec000000000000fe238f649cc884811a08627ac8edf000000006b744f080e5136400010010be7000004b5036010b351e22e000900002ada00002c9800009487fe07a29f3a0000598c1591c00000034cc49707ec143e61e846503450c4e33108610b0237c015b405e8000386c0000c768000000011f054200000ad800009fa0c1825a867cc0001e61146800006ef000000004bac17f8051000029d463f8f4c2b164778fce926400003a60c071a090656701c869028a14f80288f458a5e00005f3886480002b241e9400000003f760000000064f0000000040e8f0e000000000000000000000000000000000000000001954012019bc0fc8ae013a4431c5108000000000000001dec000065b88ce83b90000000000000000000308400017cf057625400001953000073e4ceb11e11b4842682ee9f1c3c5c0000f8886990552177c9cf94ab1cac1050000110f3fa41430f150bd806626d1472a8a942df46808b5884a813440000ee687e321507aa82e409941e7a0000000108f01fa32d4c2d00001d705304a3000082c305134424a07019d2000000000000000000000014f11c125244ee7180801d03f
  | 50 => 0x340a2a0000335a6d8cf728000000007acf26897402705fb058f000000000000000149f18d818fc000000023ba00000000000194c0000fe40ef800002a3cb1f85b02f4034dcfc380003d3040a455d9ffd3e7a0000de20c7400003a6800002e512183c7000003f3385c4a14dfd800036944d1c0000000000032943b60f8117e255700000bdc00003d1025d80000000000077a800000000000a6200002aaa00000000000000056fc78f80003798000092b9675084e1b749c1800000002d583b81444372208f800000002e766ad8a0c8b4e00007a380000ea521a8000000000001ab8000000013fc290c6a24999194b10064758e739cd300000580cfd907d31506d08a091a6412a6417896d8e0018e259e04468da720fe0000f1694b337ea7ec00000da6000065c4dc587cd1e58157410d9e2931421554d5789d62efc5974cb49f132dae0894dcf82c041025dc82bd90d904ee27b445e1f722e704b08e5f91a52e1c1884d92800024086010000088119a841f0bf381ee3316455c09a01f011e056c48dd167e305274c8e7e0000330c0bb005908ee000000000001cc33ed800007ba000030c26ed0000000000000000000075d17880000dfa157500002f4400002531ec457780001e1500006f140000ecf207e00006b71d650b18666026b8bf91154239cef2844d26220000c778000000000007630ec502560000ca38615063800004c280000000000056c9beb004878e82a7800025de4f647841df100004f6800012ed014266c0c450000056c00000001160000000000001cc0000023ac03b800000000000000000018f20000016800023024d24000000016e0000052b0000000032a0ecc02b940be4fbc4e21dff00003780000085b310e6ad011e05d5000079a4d0592190000377c122869e3df828b061f96290ec2000000001ea1c9258d05db177a34b2795800002b000005adc09f8e4823ee7f703989b8218e43a98802000022a417cc9b60000083069d0000047a10ca000015785d10e00674078d13943e2c00004b29c67000000000000d8614d87d800000d0d336c46800d8172e18766e584f2045534ae6a10d83052e013211e05c380ad359a46145771ceb22aa3a4874a1c74133a5b1c7931c592dd64aac6cb01f337065df46c298f413803ceced70a9919dc5c703f70cf42f364184ad21973244813c4698177130c82238aaf1d930fea56345571a91244400005750b680000027cd329495000000000001cf7338277103f20000029e0f0066d99e43ab6125c000000026161800e8c154528282a0cddf0dd3307600000001de901ec2938ecf1d8e094c6b3c68e04c01bc629ccdb117bf0efa346c4e196bd34383fc000000002f70000000019160f463fa0d09816e1bc46fcc7b1800000004370000000000000000be6800009321e0c54f096b2e1849c878980
  | 51 => 0x2fc20000000183c28da00000000000379a330800016d000000e58000000000001ea4b188ecc1ba413447e113f6308c7b18982870f00007050000000000000000e978fa705b275bcfc90000000000009ca96143dea64bc0001f29000000000001a1a00000000000010a2e8a2c100001c4400002db8000060626b6000055591b122ce23f8000000000000000a9d0000131200000001069000000007238f1730f042f059c800000043b803ac1e451e566d9c76b174323381de876f800019f26cb44528adf0f1819f0c2c0ed501da3fe8c8d9a7b000067e8f7988ce2d3c4b3400000002116307cca1800000002e58d3f19c3000010c8d5c16be28fa54dc7838f952d44592421b0e190f7e46d4759897935e42af822d97bb22680000c0f963b0dd40000f0d000000000000b998e4b21da46e4ae9800000002dccb438df1213211d0ffc80001b78203800006e600006cf0b1080003e066ae446e9566000000000001d312bba00007c001063b04000000020030000000000016c236a861b4cdd9f860d1c00000000000388a00000000000207c28105fd8303000000005d40000347600000000000000014ac0000000127657600001dc82b106400d820d5d2d6a41b4000000000000000a75863d000000000000f04000000007ff0a280000715400000001e6c000000000003f923ae401f80001d7879382f5800023d4184c000000022a600004ec9c1c2bc449f4aa08000295a000014481d300007f505b48000000050f0af09db83fe4000000005581c30755851d1c0b247850cc097000030d800004f88a8120224064f329c1900000000000115b000000000000fe136b656d02f19f0100003ecc000000000000000e1c14fb353a00009cd08e000007a681ec84eb07e0406c9bb97c716660000c980cf021b0000000004da0000000020280000000000000000002f8000004878000000019106e4000003900000b0b04430000000069e00000e50000000000000cbc000010c8000055a00000000000000053f89f01fd00f98000027c8bd518682280abe16892014462c42383e600004cb48f58000117a76342c11ebb1c825594f93052a279a342c000072e1d2a6e14ae7165c0000000c0000000000076147e98000130000010061d73355a5004e91985e12340000ec60000023c0cec0001a560ee87998efa800000000000000000007fa525000012fd09205bbcae28000222a00003ae00000000000000000000d2c25b402b9f4326a2000000015cb000009e8000000033cc4afc00019c500004af40000d1e07102914915846200006140d1c80000e4a45f429b1c16018668b40ab88913224507024f0c783606000050c1e22269e00000000000000000002b0800002d40000f8900003f1a23ccafea04000005268dbd80983b327e14c7d9b7f18dc4bc0000127f00006
  | 52 => 0x7c94000000000000000a2790ec00005cc800000000b54230400008a800000000a020000000000006230000173e00000000000000200000c582910e2e0000e1e905a1c14000049b0000355600000001a5c00006a9c00006a532e00d589d98dba00006dcc90e800000000000000054e00006b949e88aac3cce05007420ca400465a3000004ba0a8a0000c93800039945b3cbde897d000056ec21a9c7e00002fb4251000038ae2c74f50129c1d32343c55697060a0a00000000000351662c017e0000000026b035e039d2a0e7bec5ab80001cae000021a0000094600000001e911fa82a60a290f4024c400004aa9ba0000000007448faf112a00003ff000030f852f4b230973212202dc3c31baa2b6c09609e287892c7829348c8162b095e7d288e51e4b3fb64c5c000103036687bbcbd081c102207bf80ec000002e00000caf9d3b0ea42f9840a800035d800007d2800005c400000001dcc0000132c000136a1ab6000046b95ae00000de80000d032d24013c6a50c093b644cc4b7e00001c0478746fe8c5d10d02e703269d6830168190f6d00003c6230ac00017b003d02c4891e94ca0bb2097c41d99f50f1a74244bd94710f1e62cc6b6073a2d2681fc44d000000006858f588000170000000000ffc153400000001015000000687ca00000000000000000001186000079c1338302e56a000013fd1dec0000442000022fe0d780000000229e000000000001df85f200000000000076e40000af1144c0000e38000028e80000000145c0cb4746902b8e8f2f445288504985200004b64580800000001c7819b1d532ac25f583111e68207851ccba31be400005dbc000000000000000000000019d472844220a871b5000003b100000ef214a4b4b8795036e0000000000008743aa0000000004fc3a9c000060b04ce711ce7a1c87000006e09f9109b122e4ca809d1f8238ac00001fd00001482000065614300288206863d80e301c05a74a92800031fc12e4000000004c8000000008760000000047b93d400c400000000000000070b400009813a2a4fc400000000000000098c800040323ff46559dd701ac5284f281fa63ba2379c9b984d600000000000205b102c00009f80be90520000094c162d253a3e447e4826d1ef06c6d005175304b2190cc5a8e900ffe4f5800000eb28bc0000e930000277022cce0b881800003fcc0001838000000000000ab20000000000015ac1fa01d4c0000000297054b05ee939e00006aa80001d7c13e02d00601000020580ed4bef00003850000063d0000098c00000001b0f0000000044b844f00004c54684154900004c207da83551e7800002a10000385844340000000000032642010000000074000471f5e32cc0001032800019622d5488390a41116000099d0000000000003848f8d04f278640000000000000000000
  | 53 => 0x5069541ce000022d210e4a14000000005b98d859d7819b2736c000144233d272cce6e8000072615f855e1f3818c2534800008cb0000098000000001f3a2a2823c99d12ccc55ecaf296ed18840e10b28902e185e45bcfb396f505e662580001245219a000000010200fae60f866d04ae34c40180890070833ca428832f8d941d5c3db06d18b412070000000007bc000041400001d5200004be8ab40683000074e00000000245c000000008312bb65e28544912c09346e7012498661afe75d86eb86aa30046590dd30000135a08e41bf8cb20a9047c400018050af240884a29e1b10162b2902880001f520000485000000000000000000000006754a751d590000000098d800024260000a88800014f47488d9907692a60000049a032316562e0cdec8000000035c05f18000317c000076b90d106260e28205000000007fd4c6e081400000000065042315e40000000205417ea571c0001a05060c00004928e010000000000010bd201c387000015f822dc0000d30000000003e48738800006360d3081b17fc00001c18000053805a231d49a686ec00004050000005c2308075c18480a903765c80000186835bc2530c62090b241e59f40000000059657d03f58dd500005080f06000000002df8d97800040da15c0f7514070cf637506ec9356243808b002b1876029c686c2df800032402944000000000002d64ea6954c112074c00000596000078701b08000362809840001d060a340000000060d000014440000000000000000000000106a0000ac30d02306c2de48a590f1175c1420db70169003279f40000c9e19e62e88498068400000000f8a8fe700004300000012503b42b8c00008fa00000000a7703c43968642c7829ae600000000f4e053002fa3a7874d937f30d4481c0790000162c00000000d812f1e5c985bd1fb4124e77042f7056211e200002c58000135c6000ad10b3123b8048c90d18f636fc3a5844a07d83a020000b3800003f4000000001df900000000cc980000000237cd7d803600000000000058e07960000d9f800006da54d0000126000000000000000000004ec03178f20035468903d5006c00001fdcc6016a705c83648d6b847f2b2805f84f58d172e906a5000000002d1003200000ede17a60bc054a82572288000000000b8091e2bb00001aed288a804c55e9f2a05a43f6c00011c50fe00000e6a00000000000000000000a0400000af800000002d744c4000039d000009830000356e3520a9087f2000080dc71512140e94000033314cb000013b8000000018e00000596007a281044cc720022400003c540001e46000045d4000000034080000000000012c66a0405e00000f3c10641350000000028a400003a5148402686bb80003e8000000001526000053940998a1424160000fc487a0180e5ff800001122b9a
  | 54 => 0x472484381598037e1690d000f680e2633ec000000039d866f06fa80003a7400000001ce000004dd0e5d1a42143c779092c9e3e00000000e2d07e00b7a0000f4b800008ee00004a100000000000000005ec000000000001f761d16000060b93f90000397c0000000000000009d919b3162e000059e965507de000000000001dcc6ed8cfb80003ff84bc896e9c950000000102a8b2a3e1c26342d7999d0386080cc8a000030c07850b1382420000311ced0800000005ab89b3000022144c802d000000000709c00017190c1c72acd6c80003db279a89499c463252223c62b106500006024974971124105b90a3408b70b386eb8aff0000072800007e6145a0422621019a09cc00001dd4b17186200004a380f61d8100001170cc29b05365c0000000082e37ae0000b64800001be723053905461c86738c023991f00002138721171f2bb47fd8ef4183340de81846220b252a7e1a68a8a0dce1bfe80a46069cd10000000000000000000000000000003f8423680001b5e11fe0ccc0001f463f745c78d4f8fde190c7670e62985100007a0425b811400001b50d8f89d7349465d88a40ce3060e22b0000136106162d1097e05ea0000548000000003f020000000000000000000000000026be00004371a75337c00007e680003f9400009a18000000030100000000000072605118000000064b80001e3c13260000fa8069200264c5874386821b9466a8ad28d6b00000000d8b8000000039fc000184200003a18e8f92ca17800000d708000298a0000ee2970f254c80001c80b2216420ecc841111a0f764dc8aa301ae34de67a857d94fa0000693cb8a9e7519f843f4d149e160000019cd17800015b80000a6c8fc8012c0000243800031f064040000ad73eb01f84794911e204240bca3b0000000000000000000000000001af8b9d37d40cf4e1d1059000027a4730187e15521454000000000000be020b8000219800009e5898b00000eb469210873f3453840001aa4000000006a194d700001da015f8000000079dce4b8c5525047e4c00000002a50638cb2f165831044684557872900004a406b00000000075c0542891f00007c1c986860216f0357c7c4000031a232b800000003a240000704000003a212c8000000036e01cacb1d0e053d6a141819800000000799000016410000303c7dd98ce153e0164c86a02e0cdc00005ec80002eaa0000e3e80002514000001600003b920000ff40f52310a6a1842780000f6657c8000000000006ce0000063b0000000000019c6183a000000000001a5e555020f8000000001e451e80000000056c629000000000000c15a03000002e087d60000000020ac6c5800027a07364c75800000000eecc5311e72ed848ccdb20c6028a20728efd1bd4261e1370bfc197b229c7e78d98029615a6064887106d72ad87308b03
  | 55 => 0x89135000000006838b890dd269e000000a8000041acb2b93c10a5000008bc906f117c0798f1600d53b0e20f49090c1a00005e480001ce400000c94a1914090b76596c5b203a42f54493c0000000000000008e693ff118c7244f7592c400007ae80000b3825d400010081269177e000080b83f600004588db680002c882b248d40c1922942ec44849e8d125e29a8b1b9de100004e48961873729ea2a9c4fa051b05860000000004b118a051cc9d13c72a3448e00001ccd0bf40000c1f8f7d357400000001f0d0000000036c853a32883d24c85083f0e3e0f40265000000000000fef9562306064a8868000015200000000059a000065f4aad00f1036637b8a7b80000000000000014ce04042480d0c8bf82628000000013a900007df800018251eba0cb02e48a6b33b60000882800000000000c9680000000559c8950caf00000000be5800000000000000137b000002a8bf200003a1e5d84000000036b8380caab8ee20e4066acc2491170c1200006e78000349005c80000a003cdc00000f18000099c1438c8385a13e8e5e2c91f9203000009b8000055b20567ea8023198c01a651300de1a660ace00010299ee4289400006018000161429c04108d6f39b0000000000000000000067e9fae38482e18cbf10813a3c0000180800039123f2c000013d24145d040000000284e000000000001bfc077897a800000000000000000000000000000019d1f9e59340000c1511c800007980aa600000ffc4741826129e23500000000000025680001eee0000000000000000c8e55a400000000000090c9b41337000061100000000000000005ed0f281084000060a0150405a0000ff8803b1ec86ac400009ea063c00000000000143413646378000038c3cbc935800028927f18d2f9a41392600000000000000020e4fa88f850000000000007ce03060000624018a0000245400000000000000036701a000000000885800000001eb40000a7b000058f4baa00000000000061c000000004c780000000000042fc0000000000000000000c4f37a400002cd9f33161031f026794020e3059a8e32998908da2a94bed89d3000043f0000122f00001c7089293550b9e1ab83911b24311606bcf8586d3259841d83a21949379e12543af1ecb09a620a0db8962a0f864eac2c4800000000000000151500000000000000000002dc8000192529380000e909b520000000000004463c1a609c5900a8d1160550c000195c00007f582b5096822846bc02d10b9e27d0520c000000000006710000000000000000c6400da0b8a268400000001a501b88512a00500000000fc206f21570000000009e03c705ac8a5908f50ac665a851c8000000035780001b4d00000000a241363151c0138f598b52000037cc00000003350742888909120afa6bbc000000009d07108000045e0eb
  | 56 => 0x2c0000df91c8615607d5483c8298282e304c00017b3311a2b2c9a401cf29be00004db882c00005c00f5c00003e6c0000b271ea800004f6cc550a6816b4326876901a52ae43094bce12743a206b5011111e433e2000037d0ea30bd02320f4e80002c9403dc0000000082a000000000001c500000000000000003b200000000000000000af1180000056300001dd308400d6c0000000000000003ac80001df469e87c60000000064ecad59c6419f4564c00011fc00000838a721359000000004000d531cea00000001c322b7a000000016f200002980faf90b40000125804a96b4000052c000000001cd47b60b50178d308e000076720741cbc21c400000004088615059201320000675c00014aa0ea80464bea8a0b36664b881d780000000042400002e12d045d44e810b500000503c28a0000000079506e800000c600000000012139ec0000f428c2a2f3e23ec000000021a61220000000039960100fd08000095800000000000000000000000000202c77dcb010000000000001ae800018c6299c0000b93004420cc76c000024021c0c00005b20ce404c07a095fb0e9c48b0000081740fc1b9013887f6039c1f98063194026002844000000000007e2cf398000203878bc0ef94243b2800000001d4e00001fa00000dfc00006c204531c182fdc5710773973a00000000000000020ee0000dc4922606e217c0831845010ac0b8c3bd9c9f00002a30bdd0a012c987f30cac1c9403a4000072603c6411075a80000e582a7858901a88000198641d48b59729134a48dc000153824ec00006d900000000000079700000d107b28000000001fe44f40378f5e3f521cd8c5c924d000000006ca8b511ac46ea085480002b1e2bb45740d6900086ca807c80002d2a4148df606f82c7c10dc00010550b240000bae1a4c244640680000000320c26acc4c0dc92ed20000139146e2252659c000148000003a38bd91f683e360a9c0001acc22ac73e8a548000028200000000ae10b282a2c00005210000567000007a60000000000003c82ba41e9cb8e8f4723f42c24bc8000000003f14378206700006cc4ce6007c2194606027912a83d563b7405f994637766ffc94080000000752000000001ed20000bcc0855000000007ea800006780000000000026d67ae400012f40000000065b8f35267835e4b06000000000000000170a00007c28c7080002f08000017a0bf710a2000057480a600004b1415081972800481400014c707007c18000000033dc000000000003ab418e400000b5000050e0e53020701dc0610a661bba04967ef031588053f5863d4000122a00000000b0711ff0aa6074029f1bbc28f408ec54408d32e0456801a408e310362948a0984dd0d8e28e00bc1c51356666bc0000b3c2fda2814dab082a0c4a64840001d7b3a3a00001f69edc0ac852f81f
  | 57 => 0x46d0a7e1c0226f269789811e2718d205308200fc03e121e2c5a48c4c1b9815bc72318ee28c681cccf583dc0e4e372c5a680003c6a1f64c8e8c391f2c0534000000000001d1c00018f308fc00003cd041c1e6847cc00018723ea87e6c0000cbc12cc524800003700bc87decfd79f1f3d201ae8eb11198337042eca1b0b4f36921510000061f000006701f21c8b024e00005f611cf2cbe45e070580002c227fac0001b6c142471609ff1965067e208cfe38000079e54e49e984303e5611006eb161c319a0870b5c80000cd00cf829900001ae6378403994e21f0825fc93c00653af21ec850100003714204000003112df600000bb8000000022300000bbe0000582d023800026fc00003bf916a000025288a19b7a05a600000000000296a1988000000008b02b14bc294590ae634ac14a12110000000034c0000000045e848e8000000075908ae800000000000000052c000000006fd8000177600006691601077072a89599fef18483be43168aa2301a60b8413913e3e1800002c807022f26668421e82c605d616100000b43371075b8000102a00004db89e484681636000000000001f5c0000000047100003e9093f082240b252b000010e800006374000040417ca75d4fa91e2513ee22a4c9e93a32a907d740000000276e7cd480e8000000071780000000000000000000000299e0000000000000000000d9d0000025e543cdc98b920000000004d80000000567cb0c800000005678a731ea62c2e00000000214000000003598d4721ba7fa800000000000762c0001cc913503ad0b7280003f4a00008e585692bc810180308cce3b3e4ebc00000001da60000fad0a5d09b000010100000000000006ac8adb02b400006da1f9527407eb45e380001e2c3fd80000364112c0000000000000d44ac8d6e070b27d200000000c36000000000001ca4161a53781f4824f000000bc43611d121126af8cca0f0a00d000005c40f6d264a00000001e13000000005368000323c00006b204a123c400000000a2a000040341bd85cb090a0000a808e8c000028b400000000000000000000b900aa00000001a95000000008921ae700004a50b8680001b1a0000000000025a0807c57c84ea2a24000086782a429e612245191c15102241e8000000000006d388bb8996092641346b90000000028f08941fc4345c05a0f2e0c5113e45dd46b89a2821ec3ef456790e91e7e45a00eb10f20000817482500000000000020780002f0c0000000023039b8059816e844b0f0013a49c59e8000000000000000037820d40cdf800000001428ee19f240a1e48a000016a600006c840001e57000000000001057169654d800005a711300000000068b22a212cc54118b60000448ccb5944b221c0d089718fbf2e28633c00000002b08087caa3800000008120a2300003a
  | 58 => 0xf7200004ba9f78000000006ec00001546002800001020192803c00011e6018a5d48b61805e2ca40000000126f000011687a68000000025200001c682eba130c0001c8306e4490100b0000056a00009730286410a1a3400016ff053e0000e66129a000018c471200000000668c0001a120000328037799ed00000fe0b818000215800009c096df2bce00008ea800034745088cfa0c88384a0000000000036204be000012ac381a584c2318d61160c5508e1a98e90f842bcc000113938243934cd3800017ac0000000000000000000000131836ca27700000000000055340000000000000e40000fca00000000bc11974000078a0026800039700000000061600000000428040b00004e210139f9737a600009f6873400000000df48a7123f2138c0c0800005160000b59936411ec1708daf95ba2d3e4e580001c4900000000000176b00001db825c1780000000000000e74149e195c39f199c0000000030c1c9b0000703064b86a900000000000000000006d5c00000000000000102d1ff01d100000cbb992c0bfc0b1100f000000005ac0f8c02bc000078ccc911339329c539c96916802c1055610248daa35581ad01e68b13328a4aa885291e02e2400000001aa800000000000184d00000000000000013d824a80000c4d02c67d4c0001ba7136800000001d7a35040000be300000000000005a00fe0d7a002400011af000000000001f6a0000000000000000000650400007bd137600003cc8000039a0000000000015a41d801c109b333be673c0001f620cd82e406808000329403783af961e263810381e708b630b246e068003392b6a7b74f8791320ed4054c1e90f3e10b21f2457d14a430066b38ef712e83dbc62dcf73808315aa73a4b118000000073ec7311e0f11a03ec4aee0af82c3617bc0f28000235c3984000093734586709021038b03e245f837000003e8480d843c99600000221c0000d4f00005cc48631f5700006a64d100f7639dc7d383e5897e30500000920800025180370cc114bc0000000000016851eae496c20d0f543cba0de4b9fa0792ff200000000d2a39e600000001397152c476ca88044900000000e149c6c27b879f0ff693aa0eaa1c1c02e8f93000053c021c1721000063480000240053a436c7e7047500000000289800000000000000000000000000000131300007768fa292350eb62ec80000000000000000000000276c3edc88b01b23d3c0000000090216a800000001f4d1c0e0000139832e17ae1aec0001505000032380000000124238102ef073f0000000061e9cea000000007968e5a0018000031b8649000000009e21ddb35aa8180f8e98f91cb27878df680003cf655bc3df100b1af05b846580a2f2d021348ed5935e1ea2000000014e8000064c4000000000004d70bd5800017307c141bf0000087c3e080
  | 59 => 0x2c7924922e076a4dbca0870b0608a009604be1aaa129c2f91d5d401a000035892ce2bf424605b192200be20000ec00000000074800000000100200000000000081a24a4a9e953135a0310409a8000000000002a683d82eb6567403c16fd1ee61ae0c7f9d7d280c45c8f9f11a429840000571000009300040366000013f80000c25907e00006d04000000031e00f5cef195ad019a152487a876d00000000668072408221fe40001100132255107b90c6719763b0400012f63032456800018bd334a2fc8000204c2818572086404fd000000008e7000000003fa40128eee23ca000092380110ffa47f817400b13be8000000000000cba1b58000074f000000008d48000253c335ce3c83ec1e060000c3a97ae00000000f7b1d9209f0326c7f217e835360000e83946b014a2b58abe87511fc0072c8980000000012d843e17df00007928522000000005d249e5051c00000000880800000000000000000008cc47200000ccd000000006be893a2fb2663465480002be600000000d7c2f6e0b2095b0a7400007cd005012843a6e46d8c6b834d244e5664000115e2cf65624b7814e31a0a16140000c5b136a2eaca0580001f360000b6515ff2c4a41c89520c683c6c1b20bb691f41c521500cf780001ef4000000016b6000000005b58000091c1b1472e96a501ce746c372921b032a00004930000277c0000000104f0000798c5c5a0392d9a81f00001166345442a80000000000003c02700000059823985e3000039021dd8000062617960000000011d28364b2007c0000389c000000000001944000071e8e8d3aee24acd7b08343c90233d03884911c360d70d1806cd177013043bc062e07681410d548c3e2e507be81bc018701140000a8319ff00000831045027832f200007ff89d500000000bbc0000039800009b69db40a32498462510f028f8000092a800025fc0000d9f04f724942d20b6289413e5a000000000002f4c351864003f405ce3d0cb60000000003284e1100003fd20000a1482e62090273c0000000000049183741a672cee1a8423981ba00004a80000000025aa00002fe9ec73144000000000003c0c2e50000000000000000b2180002e60140c0000c9308c059d8ba5987b3eda57d46a4800013b0794ca4696ab00000000000080a000078e42fe05f4000052e400000003718719810999c833c226e44688000000078905e68000272200000000000000003610130f4e24001b104b4800000005cacf5a00003a5a71bcf740000260e0000000024c3208758cf580d7417a80000000138d0000743414e108802865e906c60f56024059200000000000006249b1000012c833700000000000052200001fd10efc69c000013a2000000000000a48000000004bd000025ac00000001ea400007258fdc995a375e4cd43f11ff42c6c77e04d180002
  | 60 => 0xe1400007d19aa2000000000000000000007700001f6500005a44b5c188324f431ccf50833a0fa456f100a039a0000631c00000003f700e1484600003920204c20805ca3a80353400000001840422853f9bd50000000078c87d63b623530f6413840a4a08d0000149e00000000000000000000000000000000001664000000037f800000001e120000000040f20502bde57a8f369f223d9e0d183d8174704d22afc5d51ebd2d1a3d8094796fe20ac80703788ce11928810482599033dfa2edc6d6000f3c005b044219dc719ca2e38000000000000000d4b9193066400000000000381200001e10eec309c0c746071c5f06fa00003a08b1100006ec0b4c15083872516048b1aa120b60000d159ca90e9681d858191a30000266c6c780001f300dacd5900000bb400003a28a5a31520000673000000000000f1a1c06293a36387101a330c52694087f81a800006468000199b242a56584b7000000000000adc853911bc7078dbc1b7c38262cb43919ba90c28000000000003f106edc0000000000044acf54886200000000f5e1d4a313a5ec4abc96d2047e000013e952300006290c081ed215ee3b8ceb906632f22000060b0000000000004ef8704115e1b24a461863409a36d85a38ba515fe0000000015800000000e5d9e7900001f6ce6415d1000032449c80f00371c25c004a00003b406c48117058021ae00006f818db1d5a5c60000000000003eac00018400b6e000018d013700001ce088f94991fae0000000067600000000963200738a4469c90f03141acc34c4000005a00004530000097c1920120c00000000000426000002ab0000000000000003a7245cc360800031ca6b4c0000c6a000020908588d6d188a147cbd29b8409e8718057a0b7b2ad6419c6e684701e3c45d0347830c1ee01f944e5016b3de207a4cf403a22072224c20188fc30865bd8edd101213e65db8897993c1ece722899f1e4c1fde59bc5b7800035fe00000001768236000006f297e90000431073b9abb00000000823050700000000000000000000000000170932f839d8b7b86460cce00006041b13292e2f3c43b97c900004894a801a690000000053495a71c3a6f2c39995020cac7908308190f000064ac53c1e23255a632c000080226f015940001988015c13f8fb2006426ec51a490b97c108ae6bccda21bc2148e6574000020918da2cbc17891261c2a5f14a390fb9018476940001b6b304008544a21fe511ca6e686948000312a73840000559000000003198c11022e59c40001c542ec6612800008d50000000059d8a4600006350dcc8108127e5b6424903bc364e0bd8000016122f662b8a871ed512f0763c000000009f804302d695eb0dec0000ffd03c900002e800fa0000000006148c484ab1c94714c5e48400108a33d892a09a02be03ea8
  | 61 => 0xed18c320b2a674904302a52b661528e938cbd214049a801900f53d286f24707800017f41f543ef839e35d60000db3133f00000140f410000000079c83409ee3007c7bc05621b400dc25c1c2b41ea51814000051389820ca420300ca11d9356012105cd00000000000000012f135900ff800000002b2003f05f78000306a001c7b301a23934165c00000000000000018b8000141800000000d5418460000dae91d83fc60da40000e1a231063e8134204f00005b44fd90812000000000000ac312b874300001df600000000651800018be718c84f857400007de84911435306e6c78000000031123fecd018f2a00004358a3794f800000000d85000000007a8ce6d09af0000020432a089d062400007ec05181cb644d901f025d1a5c3e2c1ca8000000034b44620000109a7100000000000004a005ba88370000000084f05db0ba85ef8118841d0000000000000001e18605400003da000000000001f1740d003b00709e26000026f4be219b12726691c000000000002d0887f0000113e7dd0ea814d10e340000000000018442c400000f7931ce202001007570ff033e02e0000000002ad4e3a886b33f267f0000078e00002d98646141100003ba4cd9000000000000a8d800020483c74b2380003b660ea8ef500003de80000000155f00002bd4000194200007214b16160d361c023c9c30de900000d1076d000000001ee47cf00003b780000000000035ea09f024f94780000256cd44067307c46d1cd2d8ada00000ca0e3683fb349c00004c5000018c8142c3dd00003048101c0001d5c33960000000201214607624c24207b23361578fc7151718506c243c9989b313c74acb048c4b0da440dc43a02d81f5080f43d78e39168a11280349a8c0b8c66f4642131f0b30322c3b29c7228687910bbe00003dae000071b18133ede6dd016a9e6006144c8cb8810b51b886dc80a50000286e0000a050000000054d4c9310a3000064a0fee876704fe5e505ae145b11b200003a418fc3e4200000000000373016cc00000002fde7758b50800000000000b9b80003ba00bec22703bf40306174000000004bc000002900290000000000000002bae091081300001bd032148e380002d7e00008599d91033e00005f080001dd00000000000000000160aef8e2229b40000000000000702558c189f732dce56a8640899c373a6c809f304ec08482ebc6e291bd038475606e3916115507a640e00c31144415580ba90050e925bb8fc615a31e4e6bf40838b4a13240600000134a3988161c9da983a07400d8800006191afc1ab049885f700002eb06f78000000000000000000000000000001fa432706240000149b29b800000000e6e000000000000f0900001a40e84000000003844000000000000000000206309520000000155300004198ffd9c5c00000be80001ae4
  | 62 => 0x39fe6a40b359cb20d6a5bcc04f08b4000000000001b28000020e800016d31e284ccc00013a1058400000000000000000000000ecb0000560c00000000000000001e1edb23dc4c68f66166e2b8628182660c770bb8465084986231af66dd826f00003e0076581b5069d29146e5c0560557000008b412e123b0f38000009c800038b61c64d248220000000007080000084a24c80000000164e63640000b352916593cdfc1e02000000000000000350a430501a800000000000caa86780a96424837d871d023e3fd4d6380000d8c6588c408d760d4800000000000189c56a40001f8f04463e3c4fc80000000511c00000002c40240c8c3975e32a0441882890eb0000755c9a5800000000cbcc4007401f2e0000bd6834902f600740f20ced26763f0490607a4000000004c19e010000000018280000188713c0001b290000000062d000013fc00000001ca71c282404a1d9eff184c2a449440c3001e61388f419182055469f0727012405362470d2286f40000132400013de096071348af913c2cb4606c0001fab2172218c000050d00000000abd156a00000000000000d0b7c2288bee9d550e2a00000000e6c0000365c000135009f40000000000000000000d868000000000009188441000034c8000000026122cc8bf902743352000000000000f3616e047c0c890ec64024000169400000000000011623ea7ddc0000000000033786601c20003c493874100000000000000018de284600000001d4139a07e7c0000000000000002b0000025703768a3c90fa152e000000018f72ba00000d288eff000027bcf67000008663bb40001a9300000000dff000020ba13ec00003eb1b6a0000f8416de3e9621480000000308a000000020830000746466a8000000059fc0000000000000004f4000000006b80f69969c00003d2000000000000342435011cc283c00007c30ff4215e000036590c31dc8515c0000000000064d400017fb2100000000001f623de74d444e0d653a96017c0000a3505a00000000000000000544a32138923322fcc4e0800000002b60adf0a7e03180000d470000000000000001f49059440c88e90669014e7ca10359d9501667a3c0000ec7059c5f0c000000039be00000000000000000007cd036500000000ef396d836d20724f1e8000214209bc403800000005528cb68111339242c8000066d00000000bfb1c7c00000dd85a9800034d41fc4b4d0ace0000467887005a61a2c00000000bde16f8687c4b10000000066100000000127200004b90000000062b00580eb127367a184cd120d0500076cf99000035f273c0bc0811c000069b8b8095780cf41dace05196c1b8c2ecc1ef017c2bdc56c04519d49327238f8d9b803d03221e7c1938e162bec231ce9b1f1a00381f74bc61111000000005ad9e9f00007a3033c800033e4000
  | 63 => 0xdc000000017940000f201ec200006c445fe0bdf1b5c00009a2959a3368000000000002c142c605b08b5f3d26685469c859e40dc407c1199fe63138733c5cc8e9300000000a9f108d00002d1845d0967069600000ab15e91fa435a08c89c2129120000da300000000018c00000000000359c0000efb2c8a00008be15a13be4783877b90960000000050b886400001ed4000101029400000792800000007d8c000104e31943628b7410de358a199400003d1000000000000000000000000001fee0000000000000001448802c7ee9bfa00007598d0413292a12000056a00000000750c000000003204f000001a0f2ef243d04e88e73160a720803594f22262000000012f337ac5a902e91d9a00000b78b17855f1a7a544c0a494db32bc1a9862c984f1f060000602800037c632e0eef1f8328be104cabf8097000040d4667800035940000b111b900000292443f00000000000084a9297015e217800000001c3c000000000000000000000000000b2264dc00000000000184434ba07d0b020000a1884b50bc2000018b0337208a0000f9380002c84000034da01b3eb20000000045300004a8c7318465000000009fd00000000514cce71deb2c0e00000000b36017600000000fad04e04abcdc7800000000000a8b00000d840d50d6301e134f25c4c0000b813f3205d0a820000403a0000edd8000000059b09372022000026f10150a7d04345a8c00007302f2e000015c14a602b2000000010e71ab0000093180001a3e42189c6180606cc000058c80000372355ce07800000001cd42bc1a350cfc167c7b88dec257235588079475237e6860dc68c530cc836bca1616ad07242b7825e1b6834a459800000ad13ca2617cf4a8000076e1ac800000001cf84190b4c8000000048e4000012a00000000000108534685a0c0001f7f00000dd48aa19050510000000006a31a9621280000000302474a8577870d00006eb08ea07b61bec122c00011c40000633014217d1000043e4943800018663474000119f30ae092800000760c140e8c221202b08c20c3811d036f22b80d60de38eea000076b40001ead0e54000035782f500003e70c4d00000ce01148a0e97663b8000003121ea7000028ec0000000000000002d7000039cc02487c498321c7800000001230000076bc0001dd81d527518ce380000aee16e80000000000000000000000000076d4000197a1e300000e44155933405a285e7172d0bda20bc9a9093c1cda7750e670e3012c0507c0001023000021fc41680000c8000006c01e62040200004ab8091268c00006d10b670d4473f40001bde0000252c000096c000026384711a73269c00000001c4c11a46dd4bac18a30b9a49440000000409c6cd4b8b978800000000a8e97a800001b70c9980000000463400003e7000049d40899b3b2ef60000558866
  | 64 => 0xdd1cca000009f0000000046ac000000000000000948885a305400000001e521c5a07e096c195128c438c82c5020a228c00002431eb600004e98222046710da50a84dc0fc71e725be4367997f347c2cd0bad170b18ca7d843e292fb06320000c1e8000000000dc00009ee0000023400006db000074d096f0000009400000000000182000000000d27000000000000000000000005bf80872fc40be451b800009041aac406817f00001cbcb369196000000000000000000064d800012be000038387bf8000000000000001cf100004e088bb1da4278c6a8c407a02500000000d2a000010de55d8fed1f5b000000000b28266264c000055b061e09e00000222803429fa77c02919fa3176a0000d749daa000000000001f9800003318d3403be00000000000199900007584e1b956012807378609000034e24b940001c6a000000009eb845d00000000000000014ae271cd2d169600560000000000000000000b0d078100000dcc000000000001a3000000002364667c000000000000000821800025ae151c00000003ef862e870b8000000000000000000000044840000000042e22b887b864533b40000000000021e600000000000336a1e1c4d3132e22260000000000037a200005f5800026fa52ec7cfa0891d7c2ae87ba8ebb281a27e8bf51e11236e54ac326150c381c769ced600000000000000006ed00006ba0624831007a81384709800011724e6400000000000000077a01050000104866b1e7a000038482d889b034464fdc000000021c87c788a38830000034280000fee377e0000735800000000000a81800000000000cc7800000001874000000000006fc08c3000000000000000000017865d640000000000000004e80000000000000000000050e2a80439000000000000ded82b400003abc0001dd93a1618f000000002bee21a482101ad0f8c6b7c1428000237c00000f78ae70000468817b8206311c7d3cda818c500000000000000000003d8407d9d5e20be01c848298413bbe8198dd0941519380ed899388d600000000003055c37ee00005cb9894000000000001d4437ec1340c0e1ddc00004fd4c6f8000000000000001e9200000000eb6800000000000eaf821230fe29940000b4c000000004c380002ed414dc53716ec33a61780977198038d261c042c077c406631ac02492950f0a56bc000000010ce000073c83470b8881dc54e8000000000000001eb700000200eb498e02d967e880001c3b00004df073903c5323261c49b39ee127d4000000007ab3fc80000d7f137a0000000060d91aa2b1c7960998051627a407880000000034c74f8488800000003508be98dbd0000000013600002f78000000009952f125af02978352149600008a8000030b600000000000000018d86dc0000000058c0e778642186a000084b9fc12c0636
  | 65 => 0x7e289a612cb37de4c840000000143854909b4896f30583b6c53b913b0000810c30e0798000072f89ec100725ce032cb550f4f0000000065b01ab07226f7c0000000398c1ea003d800000002ef40000a5400000000d9300000000000000000003cb41ec4d91000032ac5294368067d0c902464a9399ae0c082118de31fcb2790085832500b633e06afcf4b0c9608a21dc860e1041002e29702778b3a013a0754cf3820d387c0000113000033942874000000000000000000124400000000000074d16da73b400000000f3a00000000000000000006638000287c4ad4fe70f7b40584f38e250e3a2dba0000c849628198a72700001dbf28ca000000010ef000034540000a7600000000154094703ce440c000042d00005840000000033ec524ca7c80001e0461a4e041aea29ba281cc880000322e000073d8f6a0cee000000018c32d20096c000175f1d060814b9293bb3bfa704444280001f44290c0000e50085469acf571f5600005c206ce0ff21fb20000342911b01105a380000000000000001461fff00000000566000000005dd800000000afe7b4081384090f0825a800000002e9e17ec0000c8f000000a800000002db869b088c09bf3f7a685c0000000000000003449ba50c2476884df110438565f48e949209000011a44c602923ef25214000000000005d3450980000000000066e81b62ac6581413d9a101a0c03a80a11b00292073485cd85c3041015d4000000000004514ab800000878812c00000000000000000019
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x843d76950300421fbb2a8180210f5d9540c010c3cc9298600861d6494c300430f322a61802187591530c0108daeb310600862e549883004316aa4c4180219394e620c010c9aa7310600846f7558830043172a2c4180218b551620c010c9ca6b10600864d535883004237bb4a4180211b5da520c010c5cc9290600862d649483004237bb2a4180211b5d9520c010c5cc8a90600862d64548300431b2a4c2180218d552610c010caaa73086008666529843004332a94c2180218d951610c010c6aa8b08600865653584300432aa9ac21802199949610c010ccaa4b08600863554986200432aa9cc3100219954a61880108eeeab0c400863554586200432aa9ac31002199549618801087ce9b28400843d74d94200422f39eca10021175cf650801087ce9328400843d74994200422f39cca10021175ce65080108eae2b28400843e74194200421eba0ca10021179cc65080108bae6328400843d75990200421fbaac8100210fdda540801087aed2a0400843f76550200421ebb2a810021175d66308010c3ca9318400861d5498c200422fbaac610021879516308010c3aa8b18400845f7694c200422ebb4a610021879925308010c3ac9298400845f7654c200422ebb2a610021879915308010c3ac8a98400862e649482004316b24a4100219398e5208010c9ac7290400862e645482004316b22a4100219398d5208010c9ac6a90400863654984200431aaa4c2100219594e6108010caaa7308400866552984200431b2a2c2100218d5516108010caca6b084008655535842004333292c2100219954961080108eaedaa6200855573d5310042b2b96a9880211d5db53c4010a6ae9a9e200856572d4f100438aaa4a788021c595153c4010e2aa8a9e200847576d4b100429aba6a588021555cf52c4010e4aa929620087455394b10043932a2a588021c955152c4010e8ca6a9620087455354b100423abb4a3080218e5965484010c72caaa420086596594e100432cb2aa708021c65515384010cd2cb29420086696554a1004394aa2a508021d254d52840108f2ed28c200847676d5110042aab9ea888021595cb5444010a6aeb2a2200863765951100431bb2aa8880211d9db5344010a6ae9a9a200856572d4d10042aabaca68802195d965344010e2aa929a20086576554d100438b2a2a688021c555153440108eceda92200853574d4910042aab9ea488021595d65244010ccecb29220087255494910043a2a9ca48802199d955244010e4ca8a9220087255454910043a329aa488021d154d5244010c6aa9b02200865553d811004332a96c0880218ed965444010c76caaa2200865b6594d100432db2aa688021c65515344010cd6cb292200866b655491004394aa2a488021d254d52440108f4ed28a20087315494510043a8a9ca288021d854a5144010
  | 1 => 0x4204296ba4a4210214bdd54210810a5aeaa10840862f655084204316b2a8421021c394d4210810e1aa6a10840843e74997320421eba4cb990210f9d065cc81087ae832e640847671197320421f3a4cb190210f5d2658c81087ce832c640843d74196320423b388cb190210f9d2654c81087ae932a640843e74195320421eba0ca990211d9c4654c810a98e4a9a640854c73549320423abaec2990218d553614c810caaa7b0a640866552d85320423aba8c2990218d550614c810caaa630a640866552185320421f3a4ca190210f5d2650c81087ce8328640843d74194320423b388ca190211e9c0650c810a9ae5298640854d7394832042a7baa6419021535d5320c810c9eca990640864d654c832043872a26419021c3551320c810c72a8b04820853571550410431bb2a82208218d5954110410e2ca6a0882087155350441043932928220821c95494110410cb2a7300820866952980410431d2a2c0208219654d6010410cd2a4b0082086595358231042aab8aa61882195d95310c410caaca9886208716544c4310438aaa26218821d1949310c410e8aa49886208639549803104334a94c0188218e551600c410cb4a6b006208669525803104334a92c110821595c55208410cceca90842086656548421043932a24210821c95512108410e8ca6908420874553484210431caa4c0108219654e6008410c72a8b004208659535802104335292c0108218d5526190010caaa730c800866552986400423bbaac3200218d5516190010caaa6b0c800866552586400422f39eca20021175cf65100108dce5b28800846d72d94400422f39cca20021175ce65100108dce5328800846d72994400423ab8aca20021179cc65100108bae6328800846e721944004236b90ca20021175d66310010c3ca9318800861d5498c400422fbaac620021879516310010c3aa8b18800845f7694c400422ebb4a62002117dd953100108baeca98800846d7598840043172a4c4200218b5526210010c9ca7310800864d539884004237baac4200218b9516210010c5aa8b10800864e535884004326a9ac4200211bdda52100108daed290800864e639484004326b1ca4200211bdd952100108daeca90800864e635484004326b1aa4200218d5526110010caca73088008655539844004333294c2200219954a6110010c6ca8b08800863554584400432b29ac2200219554d6110010ccca4b08800866552584400431aaa4c3180219554e618c010ccaa530c600847775586300431aaa2c3180219554d618c010ccaa4b0c600843e74d94300421eba6ca180211b9cb650c0108dae5b28600843e74994300421eba4ca180211b9ca650c0108dae5328600847571594300421f3a0ca180210f5d0650c0108dce4328600846d72194300421ebacc8180210fdd5640c01087eed2a060
  | 2 => 0xcb218211b9c86590c108dae432c8608476711964304237394caa18211b5ca6550c108dce432a860846d72195430423b388caa1821471cd5450c10a38e8a9a860847575d85430431aaa6c2a18219554f6150c108eaea30a860863554185430432aa98c2a18211b9ca6510c108dae5328860846e721944304236b90ca218211d9c46510c108f4e0328860851d73950430428eba4a62182147dd54310c10a3aeaa18860861f6550c430430eb2a86218218795263d4810c3aa931ea40861e5458f520430eaa2c7a90218799253d4810c3ac929ea40861e6454f520430eb22a7a90218799263d4810c3ac931ea40861e6458f520430eb22c7a90218d59261d4810caac730ea40852e74d4a5204296ba6a529021539cf5294810a9ae7a94a40854e73d5252042a6b9ea929021539cc5494810a9ae62a4a40852e74d4e5204296ba6a729021c39525394810e1aa929ca40870e5454e5204386aa2a7290214b9d05394810a5ae829ca40862d641925204326b18c729021c350c4394810a5ce8304a40852d7418252042a7398c129021535cc6094810a5ce9b12a40852d74d8952042a739ec4a9021535cf62548108dcedaa2a40854e73d5152042a6b9ea8a90211b9d85454810a9ce62a2a40854d7315152042373b6a6a90214b9d35354810a5ae9a9aa40870e5494d5204386aa4a6a9021c39515354810e1aa8a9aa40846e7614d52042973a0a6a90214b5d05354810ac8e2b22a40862d6419152042b238ac6a90219358c6354810acee2a1aa4085647150d5204386a1886a90214b9d06054810a5ae8302a40854e7318152042a6b98c0a90214b9d01054810a5ae8082a40854e7304152042a6b9820a90210f5da541481087eecaa0a40861e5498c520430eaa4c629021879516314810c3aa8b18a40845d7694c520430f324a6290218759253148108beeca98a40861e6454c520430eb22a6290218b9526214810c5aa9310a40864e539885204326a9cc4290211bdd95214810c5cc8a90a40862d64548520432731aa4290219358d5214810c3cc9318a40861d6498c520430f322c629021875916314810c5cc9310a40862d64988520432731cc4290219358e6214810c6cc9308a40863564984520432b31cc2290219558e6114810c72c9300a40865963980520422f39ccba1021175ce65d08108bce632e840845d73197420423b388cba1021179ce65908108bae732c840845e73196420422eb98cb210211d9c465908108bce732a840845d73995420422f398caa1021175cc65508108ece232a840852c7255142042963a2a4a10211d5d76150810c6aa9b0a840865553d854204332a96c2a10211d5d46150810c6aa830a8408655531854204332a90c2a1021179ce65108108bae7328840845e73194420422eb98ca210211d9c465108108f4e0328840852d72950
  | 3 => 0xd8534c51096ae830262884e572181314423b3aec910a21355cf64885108ecebb1c42884b574d8e214423a3aac890a211d1d56348510accebb12428856672949214423b3b0a490a21599d85248510cccec29242884b574181214426ab98c090a218d15161d0110a68eaa0e808845f73595404422e39acaa02211bdc965501108d8e4b2a808853475505404431a32a82a02216c1c14150110ca8a6b0e6088554754c7304421fba2ca982210f1d1654c1108dee4b2a608846c7259530442aa3aa629822195195314c110ba0e098a60886645258720442b23aa43902210fdd16548110878e8b2a408845f73595204422e39aca90221591d52148110cc8ca90a40885e070485204432731cc5aa0219358e62d5010c9cc6b16a80864d6358b540432ab1cc3aa0219958a61d5010a3ce7aa4a80851d73d525404297396a92a0214b5cb5495010c3ac631ca80862d6218a540428f398c12a021475cc6095010a5ce4304a80852d72182540428f39ec8aa021475cf6455010a5ce5b22a80852d72d91540429a38ac6aa0218758c6355010a68e2b12a80862d62189540428f398c0aa021475cc6055010a5ce4302a80852d72181540421fbb2a82a021875526315010c3aa8b18a80862d549885404316aa2c42a021879926315010c3cc8b18a80862e64988540432731cc42a0219358e6215010c5cc8b10a80864e635885404326b1ac42a0219598e6115010caac7308a808666629845404332b14c22a0219658e6015010cd2c5300a80862e5498b5304316aa4c5a98218b95162d4c10c5aa8b16a60862e6498b5304316b24c5a98218b99162d4c10c5ac8b16a608635649875304332b14c3a9821479d35394c10a3ae9a9ca60854e72d4e53042a6b96a729821539cb5494c10a9ae5aa4a60854e7215253042a6b90a929821875906494c10c9ac4314a60851e74182530428eba0c129821539c86094c10a9ae4304a60851e74d8d530428eba6c6a9821539cb6354c10a9ae5b1aa60845e76d5153042a7396a8a9821535cb5454c108bcec2a2a60854e7215153042a6b90a8a9821551c56454c10c3ac8322a608554715895304326b10c4a9821479d06054c10a3ae8302a60854e7218153042a6b90c0a9821479d01054c10a3ae8082a60843d76950530421fbb2a829821879526314c10c3aa9318a60845f7654c530430f322a629821875915314c10c5ca9310a60862d549885304326a9cc4298218b9516214c10c5aa8b10a60864d53588530430f324c629821875926314c10c5cc9310a60862d64988530432731cc4298218b9916214c10c5ac8b10a60864e63588530431b324c2298218d5926114c10cccc5308a60866562984530431cb24c0298219a58a6014c108dce532e860846d729974304237390cba18211b5c865d0c108ece232e860846e729964304236b94
  | 4 => 0x98e6a92650843e74194328421eba0ca1942193d95320ca10c9aca99065086c932580328428eb98a9a04214b5c854d021087cec2a2810851d731514084296b90a8a04210fdd95410210c3ca8b18810861d5458c40843172a2c4204218b5516210210c6ca8b08810863554584408428eba0a798421535c853cc2108bcec29a610851d7414d30842a6b90a69842187592530c2108beeca98610861d6454c308432729ac4184219354d620c210caca6b086108655535843084296ba0a590421535cc52c82108dcec292410852d7414920842a6b98a4904218b5925208210c9ac7290410846f765482084316b22a4104219358d5208210ccca4b08410866552584208430fb20c6aa22193d8f6255110c98c7b12a88862f641895444327b18c4aa2219318c6255110ca8c7b0aa88866462d85544421fbb2a82a221471cd5415110a58e4aa0a88845e73180544422eb98c02a2211b9c860151108dae4300a88861c64d8d5344317b26c4a9a218b1936254d10c5ec8312a68862c641895344327b18c4a9a218d1936154d10cc8c5b0aa68845f7654c534428e3a2a629a21531c95314d1087ce8300a68843d741805344237390c029a211b5c86014d108dce5b2e868846d72d97434423a3aac3a1a211b9cb6590d108dae5b2c8688474755864344237b92caa1a211b1c96550d108eee2b2a868846f725944344236392ca21a211b9c86510d108dae4328868851d73150434428eba0a621a21479d54310d10a38eaa18868847475584434431a2a2c221a219514d6110d108f0eab00868869943580434430fb26c6a9221871936354910c3ec831aa48861c6418d5244316326c4a92219318f6254910c68c9b0aa48865463d855244237bb2a4292214b1d15214910a98e6a90a48843e74180524421eba0c029221179cc60149108bae6300a48845e73d97424422eb9ecba12211d1d561d09108bce7b2c848845d73d96424423a3aac32122117dcd65509108b8e6b2a848847771595424422fb9aca21221171cd65109108bce6328848845d731944244296b90a8212214b5d05210910a5ceaa10848852c75508424423a3aac2212218d1516110910cc8a4b088488478755804244354a12c0212210f9d365cc91087ae9b2e648847475587324421f3a6cb192210f5d3658c9108e8eab0c648843f74595324421e3a2ca992211ddc5654c91087ee8b28648843c74594324421f3a0ca192210f5d0650c910a9ae4298648854d7314832442a73aa6419221531d5320c9108e8eab086488654535843244332292c2192211e1d5600c910d9264b00648853675d91414429b3a4a8a0a211d9d85450510a6cec2a2828863676151414426ab98c0a0a21395c860505108ecebb2462884e572d92314423a3aac898a21559d7634c510aace729a62884767614d31442ab3b0a698a21959
  | 5 => 0x70d5454d2008333b2ca290041c95525148020e8aa728a40106676554520083932a2a290041c95515148020e8ca6a8a4010745535452008316aa6c0900419354f6048020c76cb2a2401063b65551200832db2ca69004196d955348020e32a8a9a40107295494920083a4a9ca4900419cd965148020ce6caa8a40107315454520083a8a9aa290041d8949514802087eecaa0a98845f7654c53c4237396cba1e211b5cb65d0f108dce5b2c878846d72d9643c4237394caa1e211b5ca6550f108dce4328878846d7219443c4237bb2a429621179cf65d0b108bae7b2e858845e73d9642c422eb9ecb21621179ce6550b108bae732a858845e7319442c422eb98ca216210f9d365ccb1087ae9b2e658843e74d9632c421eba6cb196210f9d2654cb1087ae932a658843e7419432c421eba0ca196210f9d85450710b62e1aa283884767615141c425b3b0a8a0e214d9d85450710c6cec2a283887317015141c426ab98c0a0e21395c8605071087eecaa083886b14158041c4272b96c918e21179d8534c710ba2e1a9a63884767614d31c426b3b0a698e21559d8534c710cacec29a63887517014d31c425aba0c098e21395c8604c7108beeca9863886d13158031c426ab9ec910e212d5d363887108dcec29243885e170d4921c423b3b0a490e21399d85248710accec29243886667614921c43b0b80a490e212d5d060487109aae6302438846f7654821c437090ac010e218d5506150310caaa630a61886655218520c421fbb2a82a421875516315210c5aa8b10a90861e6458c548432731cc42a4219358e6215210c5cc8b10a90864e635885484326b1ac42a4219598d6115210caac6b08a908666625845484332b12c22a42117dd95314e10c3ac8a98a70864d53588538430eb24c629c218b9926214e10c5ac9310a70862e645885384316b22c429c219398d6214e10c6cc8b08a708635645845384333312c229c21995896114e108dce432e870846d721974384237390cb21c211b5c86590e108dee4b2a870846c725954384237390caa1c211b5c86550e10a38e6aa2870851c7454d4384237390ca21c211b5c86510e10c3ecaa18870861d6550c438434ca1ac021c211bdd95214a10c5ac8a90a50864d63548528430f324c629421875926314a10c3cc8b18a50861d6458c5284316b24c4294219358e6214a10c6cc8b08a50863564584528432b31ac2294219558d6114a108bce632e850845d73197428422f398cb21421175cc6590a108bee6b2a850845c73595428422f398caa1421175cc6550a10a58e4aa2850852c74549428422f398ca21421175cc6510a10c5ecaa10850862d655084284354a12c0214210f9d065cca1087ae832e650843e74196328421eba0cb194210fdd1654ca10878e8b2a650843e74195328421eba0ca99421531c9534ca10a
  | 6 => 0x10821f3a4cb988410f5d265cc42087ce932c621043d74996310821f3a0ca988410f5d0654c420aa8e2a9a621046d75d893108316aa6c4988419354f624c420c5aa8312621064d5318931082aa39aa29884199d89514c420cc8c4a8a621043e74994310821eba4ca18841555c6530c420aaae72886210557754c431082aabaa621884195d95310c420caaca9886210716544c4310838aaa262188419c54560c8420e4ca890842107255448421083a329a4210841d154d2108420c72a9300421065953980210831caa2c0108419654d6008420ce4a2b00421062d5498a4008326a9cc5200411bdd56290020c5aa8b14801064d5358a4008333312a3200419958951900208bce7b28801045d73d94400822f39cca20041175ce65100208bce6328801045d73194400822ebacc620041879526310020c3aa9318801045f7558c400830f2a2c6200418755163100208beed298801045d7694c400822fbb2a620041175d95310020c5aa9310801064e539884008326a9cc4200418b9516210020c5aa8b10801064e535884008326a9ac4200411d5d66110020c6ca9308801063554984400832b29cc2200419554e61100208eeeab08801063654584400831aaa2c2200419594d6110020caaa6b08801047576944400832b31ca2200419558e5110020cccc5288801066562944400823bbb2a2200419598d5110020caac6a888010666625444008332b12a2200418b552628c020c9aa7314601046f7558a3008316aa2c5180419354d628c020cccc4a8c601066562546300821f3a6ca180410f5d3650c02087ce9328601043d74994300821f3a0ca180410f5d0650c02087aeb320601043f75590300821fbb4a8180410f5da540c02087eecaa0601043d76550300830f324a61804187592530c020c3cc8a98601061d6454c30083172a4c4180418b552620c020c9aa7310601062e545883008316aa2c4180419394d620c020c9aa6b10601047575984300831b2a4c2180418d552610c020caca7308601065553984300823bbaac2180418d951610c020c6aa8b08601065653584300832aa9ac2180411d5da510c020c6cc92886010635649443008333314a2180419958a510c0208eeeca88601063664544300831ab22a21804199989510c020ccac4a88601054d73d5320082b2b8ea9900414b5d353c8020acae3a9e401070d5494f20083872a2a790041c355153c8020e4aa928e40107455394720083932a2a390041c955151c8020e8ca6a8e4010745535472008236bb4a510041c655153880208f2ed29440107315454620083a8a9aa3100411b9db5448020a9ae7aa2401056571d512008296baca8900418bd965448020c5ecaaa2401046e76d4d2008296ba6a690041595c75348020a9aeb29a401064f6594d2008386aa4a69004193d955348020e1ca8a9a401
  | 7 => 0xba18411b9c865d0c208ece232e861047571197430823b38ccb218411d5c66590c208dce432c861047671196430823ab88cb218411d9c66550c208eae332a861046e72195430823b388caa18411d5c46550c20a38e6aa2861051c7454d4308236baec4a18418b5536250c20c9aa7b12861046d751894308316aa0c4a18419354c6250c208ece33288610475719944308237390ca218411d9c46510c208eae2328861047a70194430828eb9ca821841475d25310c20a3eeaa18861051d7550c430830fb2a8621841875954310c20c72a8b04841052d725504208317b2a84210418b5954210820e1ca6a10841070d53508420832ca9cc0210418e9516010820cb2a6b0084106595358232082a6b92a61904193d95320c820c9aca990641070e544c83208386aa264190418e552600c820c72a8b00641065a53580320830f2a4c7a88418755263d4420c3ca8b1ea21061d5458f510830f324a7a88418759253d4420c3cc8a9ea21061d6454f510829b3a6a3288414d5d35194420aace7a8ca21055573d4651082ab39ea928841555cf5494420aace62a4a21055573152510829b3a6a7288414d5d35394420e2ca929ca2107155494e510838b2a2a728841c55515394420a6ce829ca2105357414e510831ab20c9288419558c6394420e2a8621ca2107254210a51083a299065288414d9d06094420a6ae8304a2105567318251082aab98c1288411d9db5454420aace7aa2a21055573d51510823b3b0a8a8841559cc5454420aaae62a2a21047676d4d510829b3a6a6a88414d5d35354420e2ca929aa2107155494d510838b2a2a6a8841c555153544208ecec29aa2105367414d510829aba0a6a8841591c96454420c6ac8322a2105647258d510832ab18c6a884159dc94354420ac8e4a1aa2107154310d5108392a1084a88415c9c04254420ae2e0212a210745320c951082b938064a88415c5c03254420a6ce8302a2105357418151082ab398c0a8841555cc6054420a6ce8102a2105357408151082ab39840a8841555cc205442087aed2a0a21043f76550510830f2a4c628841875526314420c3ca8b18a21061d5458c510822ebb4a628841879925314420c3ac9298a21045f7654c510830f322a628841875915314420c6ca9308a21063554984510832b29cc2288419554e61144208eeeca88a21063664544510831ab22a2288419598d5114420caac6a88a21045e73997410822eb9ccba0841179ce65904208bae732c821045e73195410822eb98caa08414d1c554504208daebb12821062d54d894108326a9ec4a08418b5506250420c9aa63128210534745454108333b12a2a08419918951504208bce7328821045d73994410829ab8ca8208414d5d25110420a6eeaa08821053575504410831bb2a82208418d5954110420e2ca6a088210715535044
  | 8 => 0x95114520a68e8a88a29055473544514822fb9aca20a41171cd65105208bce6328829045d73194414829ab88a820a418b1516210520a6ae8288829066562144414829b3aa8220a414d1d54110520d6282b00829043f74594314821e3a2ca18a410f9d0650c52087ae832862905557114c314832629ac418a41555cc510c520ccac42886290556754c431482aa3aa6218a41b44c5600c5208dcebb2642904cd73d9321482373aec790a412b5d363c8520accebb0a42905667614521483333b0a290a412b5d0604852099ae6302429062c5458b40482963aa85a024117dcd65501208b8e6b2a809052c75509404831632a84a02416a1c14250120c98a6b16609054c754cb304821fba2ca982410f1d1654c120a98ea992609064c654c930482e438264982419358e62d5020cacc730ea81065563987540832b31ac3aa0419558d61d5020cccc4b0ea81051e73d52540828eb9ea92a0414d9c75495020a6ae3aa4a81061d6318e540831ab08c32a041479cc6095020a3ae6304a81053671182540829ab88c12a041479cf6455020a3ae7b22a81053671d91540829ab8ec8aa0414b1c96355020c3ac631aa81052c72585540831ab08c2aa041479cc6055020a3ae6302a81053671181540829ab88c0aa0410fdd95415020c3aa9318a81061d5458c540831aaa4c22a0418d5516115020c3cc9318a81061e6458c540832731cc42a0419358e6215020c6cc9308a81065663984540832ab1cc22a0419998a6115020c6cc8b08a81065663584540832ab1ac22a041999896115020cb2c7300a81067161980540831b2a4c3a98418d55261d4c20c6ca8b0ea610635545875308316b24c5a98418d99261d4c20c6ac930ea61063664587530831ab22c3a98419998961d4c20a3ce9a9ca61051d74d4e53082ab38ea729841555c75394c20aace3aa4a61055571d5253082ab388a929841555c45494c20c3ac8324a61065561186530828f3a0c129841475d06094c20aace2304a61055571182530828f3a6c6a9841475d36354c20aace3b1aa61055571d8d530822f3b6a8a9841559c75454c20aaae3aa2a61045e7615153082ab388a8a9841555c45454c20a98e4b22a61061d6419153082a6392c2a9841955846154c20a3ce8302a61051d7418153082ab388c0a9841555c46054c20a3ce8102a61051d74081530821ebb4a8298410fdd95414c20c3ca9318a61061d5498c530822fbb2a629841879915314c20c3ac8a98a61063654984530831aaa4c2298419554e6114c20c6ca8b08a61063554584530832aa9ac229841879926314c20c3ac9318a61062e649885308316b24c4298418d9926114c20c6ac9308a610656639845308333314c2298418d9916114c20c6ac8b08a610656635845308333312c2298418e5926014c20ce2c3300a61047671997430823ab8cc
  | 9 => 0xeeca9865906c93258032c823bbb2a228e41179cf65d07208bae7b2e839045e73d9641c822eb9ecb20e410f9d365cc72087ae9b2e639043e74d9631c821eba6cb18e41335cf64c872095ae9b1e43905e170d4521c82733b0a290e412b5d0604872099ae630243906e12158021c8316aa0c4a06419354c624c32087eecaa0a91061d5458c548831aaa2c22a441879916315220c9cc6b10a91064d63588548832b31cc22a4419558e6115220ccac5308a91063664584548832b31ac22a4419558d6115220ccac4b08a91045f7654c538830eb22a629c419554d6114e20c3ac9318a71062e645885388316b22c429c418d9926114e20c6ac9308a71066562984538831b322c229c418d5916114e20cacc6b08a71066562584538823b388cba1c411d5c465d0e208ece232c871047571196438823bb8acaa1c411d1c56550e208ece232a871047571195438828e39aa8a1c41471d15350e208ece2328871047571194438830fb2a8621c41875954310e20d3286b00871047776544518831ab22a228c419558d51146208bee6b2a831045c73595418822f398caa0c41175cc6550620a68e2aa2831053474545418831bb2a8220c418d5954110620d6282b00831043f74595318821e3a2ca98c410f9d0654c62087ae832a63105547154d31882aa39aa298c4195d95310c620caaca98863106d131580318828eb98a9a04414d5c454d022087cec2a2811051d73151408829ab88a8a04410fdd95410220c3ca8b18811061d5458c40883172a2c4204418b5516210220c6ca8b08811063554584408828eba0a798441555c453cc2208bcec29a611051d7414d30882aab88a69844187592530c2208beeca98611061d6454c308832729ac4184419354d620c220caca6b08611065553584308830fb20c6aa2419318f6255120caec7b0aa89065463d85544831bb20c2aa24195d8c6155120ca8c630aa89066762185544821fbb2a82a241471cd5415120a68e2aa0a89061c64d8d5348316326c4a9a418dd936154d20c68c9b0aa69063764185534831a320c2a9a4195d8c6154d20ccec430aa69045f7654c534828e3a2a629a41551c55314d208ece3b2e869047571d9743482363aac5a1a411d9c76590d208eae3b2c869046c7558a4348237b92caa1a411ddc56550d208e8e2b2a869047771594434823a38aca21a411d9c46510d208eae2328869051d73150434828eba0a621a41479d54310d20a38eaa18869046c7558843483162a2c421a419314d6210d208f0eab0086906994358043482973aec8a12414b9d254509208dcec2a2849052e7615142483173b0a8a1241335cc60509209cae2302849046e75d923248272b8ec9192411b1d5644c920a9cebb1a649054e7394d32482373b0a699241539d8534c920c9cec29a64904ad741813248272b88c0992411ddd
  | 10 => 0x65463545410c237394ca208611b5ca6510430a6ae32a0821853574944410c29bbaa82208614d5d54110430c6ecaa08821863565504410c3932928220861c95494110430ce2a2b066218716544c4310c38aaa26218861d1949310c430e8aa4988621863954980310c334a94c0188618e551600c430cd2a4b00621867251580310c21f3a4cb908610f5d265c843087ce932c421843d74996210c21f3a0ca908610f5d065484308baebb1a421861d54d8d210c30eaa0c69086193d8d5248430c98c6a92421856471549210c32bb1aa2908619518d5148430ac8e4a8a421843e74994210c21eba4ca10861595c65208430acae5288421856775484210c2b2baa421086199d952108430ccaca908421872654484210c392aa242108618755263900308beeab1c801861d5458e400c32731aa5200619358d5290030cacc6a8c801865563546400c30eaa4c620061879516310030c3aa8b18801846d75988400c3172a4c4200618b55262100308deeab10801862e54588400c316aa2c4200611b5da5210030c9cc7290801864d63948400c237bb2a4200619398d5210030c9ac6a90801847575984400c31b2a4c2200618d5526110030ccca5308801866552984400c23bbaac2200618d9516110030c6aa8b08801866652584400c332a92c2200611d5da5110030cacc7288801865563944400c333314a2200619958a51100308eeeca88801865663544400c32ab1aa220061999895110030ccac4a88801854d72d53300c2aab8ea998061c355252cc030e1ca8a96601870d5454b300c38aaa4a398061d154a51cc030e2ca8a8e601871554547300c3a3292a398061d154951cc0308baed29c60184797694e300c394aa2a518061cc551518c030ec2a4a8c601845e76d51300c2a6b96a898061555c7544c030a3aeb2a2601861f65951300c30fb2aa89806193d96524c030e1aa9292601864f65549300c3872a2a498061c3551524c030caecb28a601871554945300c3a2a94a29806195d95514c030e2ca8a8a601871554545300c3a3292a298061d1549514c030c3aa9b02601863b65951300c31db2aa898061c6552534c030cd6cb292601866b65549300c394aa2a498061d294d524c030ce6cb28a601867365545300c398aa2a298061d494d514c030ec2a4a8a601843f7655054c822fbb2a629e411d9c765d0f208eae3b2e879047671d9643c823ab8ecb21e411d9c66550f208eae332a87904767119443c823ab88ca21e410f9d85450b20b52e1aa2859046e7615142c82573b0a8a16414b9d85450b20c5cec2a285907297015142c8266b98c0a1641395c46050b2087eecaa085906a94258042c8272b8ec919641179d8534cb20b92e1a9a659046e7614d32c82673b0a699641539d8534cb20c9cec29a65907497014d32c8256ba0c099641395c4604cb208b
  | 11 => 0xc296ba0c129061599c46094830acae2304a41846e76d51520c2b338ea8a9061595c754548308dcec2a2a41856671151520c2b2b88a8a9061531cd6454830c5ac8322a41870d4310d520c2b538086a90615a5c04354830a98e6b0aa41866561185520c2973a0c0a90614b5d06054830acce2302a41856571181520c2973a060a90614b5d0305483087aed2a0a41843f76550520c3172a4c4290618b55262148308deeca90a41862e64548520c316b22a4290618d9526114830c6aa9308a41866552984520c31b2a2c2290618d5516114830ccaa4b08a41847671997420c23ab8ccba10611d9c665908308eae332c841847671195420c23ab88caa10614b1c954508308baebb1a841861d54d8d420c30eaa0c6a10614b1d15250830c9ec6a92841864c63549420c23b38cca210611d5c66510830a5ae52a0841852d74948420c297baa84210614b5d54210830c5ecaa10841862d65508420c334a92c199061c3951320c830e1aa8990641863954980320c31caa2c0190619a949600c830c5ca9316a21862d5498b510c3172a2c5a88618b55162d4430c5cc9296a21862d6494b510c317322a5a88618b59152d4430a6ce9a8ca21853574d46510c2b3396a328861595cb5194430acce5aa4a21856572d52510c2b3390a928861595c85494430a6ce9a94a21853574d4a510c3932a4a528861c95525294430e4ca8a94a2187255454a510c29b3a0a5288614d5d05294430c6ac8324a2187154310e510c332b10c528861c95084294430e8a64194a21853674182510c29aba0c128861599c86094430acae4304a21847676d51510c2b3396a8a8861595cb54544308ecec2a2a21856672151510c2b2b90a8a88611d9db5254430a6ce9a92a21853574d49510c3932a4a4a8861c95525254430e4ca8a92a21872554549510c23b3b0a4a88614d9d05254430a6ae8292a21855473591510c31ab20c8a8861c550c4354430ae4e021aa2185717010d510c2aa39ac4a8861995886254430aaee6a12a21855473509510c392a1084a8861d14c83254430ae4e0192a218571700c9510c29b3a0c0a88614d5d06054430acce4302a21856572181510c29b3a060a88614d5d03054430acce4182a218565720c1510c21ebb4a8288610fdd95414430c5ca9310a21862d54988510c3172a2c4288618b55162144308daed290a21862e64948510c316b24a4288611bdd95214430c5cc8a90a21862d64548510c31b2a4c2288618d5526114430ccca5308a21866552984510c23bbb2a2288618d9915114430c6ac8a88a21866662544510c332b12a2288611b9ca65d04308dae532e821846e72996410c236b94cb208611b9c865504308dae432a821853471551410c22ebaec6a0861875536350430c3aa831a821864f63549410c32631aa4a08614d1d15150430caec6a8a8218
  | 12 => 0x20c610fdd16548630878e8b2a431843e74195218c21eba0ca90c61591c55248630ac8e4a8a431866765484218c332b2a4210c61b84856008630a5ae42a6811853571153408c21f3b0a8a04614b5c85450230a6ae22a2811843f76550408c30f2a2c620461875516310230c5ca8b10811862d54588408c31b2a2c2204618d5516110230c5ec8312a89864f63189544c333b16c2aa2619918b6155130c6ec830aa89865763185544c333b10c2aa26199188615513087eecaa0a89852c72550544c29a38aa82a261479d76450d30a3ce92a2869845e76151434c28f3b0a8a1a61879d85450d3099ae430286984d571181434c237bb2a4292614b1d15214930ac8e2a90a49847771594424c23a38aca212611d9c465109308eae2328849852d72150424c30e2a2c6212614b5d05210930c9ac6290849852e75508424c2963aa8421261aa50960109308bcebb2664984d571d93324c2a73aec499261539d8524c930c9cec292649849d74181324c26ab88c0992611ddd95114530a68e8a88a29856472544514c237b92ca20a611b1c965105308dce4328829846d72194414c29ab88a820a61871516310530a6ae8288829865563144414c29b3aa8220a614d1d54110530d6282b00829845e75d93314c266b96c998a61559d7614c530aacec28a629865676145314c24eba0c098a61335c8604c5308bceb31a429849d7498d214c21fba2ca10a610f1d1650853087ce8328429843d74194214c326b18a410a61595c45208530caac6288429856572144214c2b33aa4210a61591d52108530dc242b00429861c5458f404c28e3aa87a0261471d54350130c38caa1a80985987050d404c32731ac5aa0619998a61d5030ccac530ea81865663587540c333312c3aa0619958961d5030a5ce5aa4a81852d72d52540c29b38ea92a0614d5c75495030c5ac4314a81863561186540c297390c12a0614b5c86095030a6ce2304a81853571182540c297396c8aa0614b5cb6455030a6ce3b22a81853571d91540c28e39ac4aa0618b5886255030a38e6b0aa81863561185540c297390c0aa0614b5c86055030a6ce2302a81853571181540c21fbb2a82a0618b5526215030c5aa8b10a81863554984540c31aaa2c22a0618b9926215030c9cc7310a81862e64588540c32731ac42a0618d9926115030cacc7308a81866662984540c332b14c22a0618d9916115030cacc6b08a81866662584540c332b12c22a0619a58a6015030ce2c3300a81863954582430c28eb9aa82186187d954310c30c3acaa18861863a54580430c31b2a4c3a90618d55261d4830c6ca8b0ea41863554587520c2973a6a5290614b5d35294830acce3a94a41856571d4a520c2b338ea929061595c75494830acce22a4a41856571152520c316b20c929061c350c4394830ccac230ca41852e7418252
  | 13 => 0x65cc4408dae532e622046e729963110236b94cb188811b9c8654c4408dae432a622043d75d91311030fb22a69888187191534c440aa8e2a9a622062f645493110316322a4988818dd91514c440c68c8a8a6220554735453110237394ca188811b5ca650c440aaae329862205557394431102abbaa6218881555d5310c440caeca9886220655654c431103a32926218881d1549310c4408bce732e422045d73997211022f39ccb10881175ce65884408bce632a422045d73195211021ebaec89088187d915348440c38c8a9a422062f645492110316322a490881591c55248440c6ec8a8a42206346454521102b2392a290881179ce65084408bae732842205657194821102b2b94a21088159dd52108440acaea9084220667654842110332b2a4210881d194d2108440e8aa6908422070d5394b401038729aa5a0081c354d52d0040e2aa728e802072552947401038b29aa3a0081c554d51d0040e4ca4a8e802072552547401021ebb4a9200811e5da5490040e92a6a9480207515354640103b0a92a32008187d965350040c3ecaa9a802062f659494010386a9ca4a00818bd955250040e1ca6a92802070d53549401031bb2ca2a0081c554e5150040e4aa528a802063765545401038b29aa2a0081c554d5150040e4ca4a8a802072552545401032db2ca6a008196d955350040e34a8a9a802066b659494010335b2aa4a0081ca9515250040e92a6a928020673659454010339b2aa2a0081cc9515150040ea2a6a8a802076152545401021fbb2a82a6610f9d85450f30b32e1aa2879845e7615143cc24f3b0a8a1e61479d85450f30c3cec2a287987197015143cc266b90c0a1e61355c46050f3087eecaa087986994358043cc237bb2a4296611d9c765d0b308eae3b2e859847671d9642cc23ab8ecb21661355c764ccb30b92e1a9265984ce7614932cc24eba0c099661355c4604cb30d9264b0065984777654451cc237396cba0e611b5cb65d07308dce5b2c839846d72d9641cc266b96c998e61745c3514c7309acec28a639849d7418131cc266b90c098e61b44c5600c73087ce9b2e439843d74d9721cc21f3a6cb10e610f5d3658873093ae931a439861d5418d40cc21fbb2a82a4618b5516215230c6aa8b08a91864d63988548c317322c42a4619358d6215230caac7308a91866662984548c332b14c22a4618d9916115230caac6b08a91866662584548c332b12c22a4611bdd95214a30c5ac8a90a51866552584528c23bb8acaa14611d1c56550a308ece232a851847571195428c296392a8a14614b1d15250a30c5ecaa10851862d65508428c354a12c0214611ddd95114630c6ac8a88a31866562544518c237b92caa0c611b1c965506308dce432a831846d72195418c29a38aa8a0c614d1d15150630c6ecaa08831863565504418c358a0ac0
  | 14 => 0xc631ca42070d4310e5210332b08c329081539cc6094840a9ae6304a4205667118252102b2b88c1290811b9db5354840acce3a9aa42056571d4d52102373b0a6a9081599c45354840acae229aa42052c7458d5210326b18c6a9081c350c4354840ad4e021aa4205697010d52102963a2c2a9081995846154840a9ce6302a42054d7318152102b3388c0a9081595c46054840a9ce6202a42054d73101521022ebb4a62908117dd95314840c9ca7310a42064d539885210237bb2a4290819398d5214840c9ac6a90a42065653984521032aa9cc2290819954a6114840caca6b08a420655535845210332a92c2290819a54960d0840e1ca6a10842070d53508421032ca9cc0210819654d6010840cd4a4b00842047671997321023ab8ccb990811d9c6658c8408eae332c642047671195321023ab88ca990810f5d7644c840c3ec8a9a642061c6454d32102a6392a6990818bd91524c840c58c8a92642054c73549321023b38cca190811d5c6650c840a9ae5298642054d7394832102a7baa6419081535d5320c840c9eca990642064d654c8321032729cc5a88819354e62d4440c9ca6b16a22064d5358b511032731ca5a88819358e52d4440c9cc6a96a22064d6354b51102ab39ea328881555cf5194440acce5a8ca22056572d4651102b3396a728881595cb5394440acce429ca2205657214e51102ab39ea528881555cf5294440e8ca7294a2207455394a51103a329aa528881d154d5294440aace6294a2205557314a511032ab18c728881c550c4394440ccac4314a2207254210a51103a29906528881559cc6094440aaae6304a2205667218251102b2b90c1288811d9db5354440acce5a9aa22056572d4d511023b3b0a6a8881599c85354440acae429aa22047676d4951102ab39ea4a8881555cf5254440e8ca7292a2207455394951103a329aa4a8881d154d52544408ecec292a2205567314951102aab98a4a88814d1d16354440caac631aa2207154310d51102b938086a88815c5c04354440a68e8b12a220665621895110392a1084a88815c9c04254440ae2e0212a220537744c9511029a3a264a8881d14c83254440aace6302a2205557318151102b3390c0a8881595c86054440aace6202a2205557310151102b339080a8881595c840544408baed298a22045f7654c511032729cc4288819354e6214440c9ca6b10a22064d535885110236bb4a4288819398e5214440c9ac7290a22046f76548511032731aa4288819358d5214440caca7308a220655539845110333294c2288819954a61144408eeeca88a22065663544511032ab1aa228881999895114440ccac4a88a22067151583411038b29a8220881c554d4110440e4ca4a08822072552504411032ca9cc0208819a54a6010440cb2a6b00822066952580411033928ac0208811b9ca
  | 15 => 0x9e7614d43d0256b90c0a1e812d5c46050f40d3286b0087a046f7654852d02d4b86a4a16812b9d85250b4093ae630285a04b57118142d0354a12c0216811d9c765ccb408eae3b2e65a047671d9632d023ab8ecb196812d5c6644cb408eeeca88a3a05b170d4541d025b3b0a2a0e81275cc605074095ae430283a06b14158041d0237396cb98e811b5cb65cc7408dce5b2c63a046d72d9631d0256b94c898e81179cf65c87408bae7b2e43a045e73d9621d022eb9ecb10e81275ce64487408beeca98a72064d53588539032aa9ac229c811bdd95214a40c9ac6a90a52066552584529023bb8aca994811d1c5654ca408ece232a65204757119532902a6392a699481531cd524ca40c9eca990652064d654c83290364992c0194811ddd95114640caac6a88a320665625445190237b92ca98c811b1c9654c6408dce432a632046d7219531902aa38aa698c81551cd514c640caeca9886320655654c4319036898ac018c8117dcd65486408b8e6b2a432045e73195219022eb98ca90c81591c55248640ac8e4a8a4320667654842190332b2a4210c81b848560086408beeca98a6a054c7254c53502aa38aa629a81479d76350d40a3cec29a86a061e7614d4350256b90c0a1a812d5c46050d408deeca90a4a054c7354852502b238aa4292814b9d76250940a5cec29284a062e76149425024eb98c0a12812d5c4605094087ceb32264a04b571991325023bb8aca192811d1c5650c9408ece232864a047571194325030eb20a619281535c8530c940c5ac829064a054d7314832502a73aa6419281531d5320c940d9264b0064a04777654451502aa39aa228a81591c95114540a6cebb0a82a053676145415031b3b0a2a0a81275cc605054095ae430282a043e759913150256b94c898a811bdc9650c5408d8e4b2862a046e721943150236b90ca18a8187590530c540aaae229862a06356414431502aab98a218a81559d5310c540aa8ea98862a06d131580315021f3acc890a81275ce64485408bee6b2842a045c73594215022f398ca10a81175cc6508540c5ac829042a056571148215031ab20a210a81595c85108540accea90842a056475484215037090ac010a81539cb5394c40a9ae5a9ca62055671d4e53102aab8ea729881935886294c40caac230ca62054e7218253102a6b90c129881559c46094c40aaae2304a62051c745895310326b10c4a9881471d16154c40caac230aa62054e7218153102a6b90c0a9881559c46054c40aaae2302a62045f7654c5310326a9cc4298819354d6214c40caaa7308a62065553584531032ca9ac1a18819694d6010c40caca730ea42065553987521032b29ac3a90819554d61d4840a9ce7a94a42054d73d4a52102b338ea529081595c75294840acce3a9ca42056571d4e52102b3388a729081595c45394840c9a
  | 16 => 0x868f3a6a6a1a431b9d76250d219cce3b128690c7675d854348673396c2a1a431e9c06510d218f2e03288690e1e6550c434870e32a8621a431b1d56210d219c8e2b108690c74755844348672392c221a438d15161d0921ca8a6b0e6490e2c5458b414862f39ecaa0a43175cf6550521c98a6b166290c3e74d95314861eba6ca98a43179ce64d41218bae7326a090c3e7498f504861eba4c7a82431edd95014121c3cc9318a090e1d6498c504870f322c6282438759163141218bce6302a810c5d73181540861fbb2a82a043875516315021c72a8b00a810e1e6458c5408726b1cc42a0439558e6115021cb4c7300a810e5963980540871d322c02a0439698d6015021cb2c6b00a810e6a62580540873930ac02a0430f9d06054c2187ae8302a610c5f7654c530870eb22a6298439654d6014c21c3ac9318a610e2d64988530871ab24c2298438e9926014c21c72c9300a610e3a64580530871cb22c0298439698d6014c21cd4c4b00a610e7261580530863d380cba18431e5c065d0c218daeb3168610ce57198b430863abacc3a1843395ca61d0c218f4e032c8610c79701964308636bacc521843395c66290c218eaeb30c8610ce5729864308637394caa18431d9c66550c218f4e032a8610c7970195430868e39aa8a1843471d15350c218dce43288610c7671194430863d380ca218431e5c06510c21c3ecaa188610e1d6550c430862f39ecb21043175cf6590821c6aa930c8410c3e74d96320861eba6cb190439554e618c8218bce7b2c8210c5d73d964108716aa4c520843179cc65104218bae63288210c3e74d96310861eba6cb188439354e628c42187ce83286210c3d741943108636bb4a5108431d5da5288421ccaebb2a4210e6676d9521086b2b86ca90843595d66448421b8ce73224210dc57399121086b3baac890843a959064484219ccedaa24210ce6761512108792aa0a890843719cc5448421b8ae62a24210de27015121086f0b80a890843595d66348421b4ce931a4210da57498d21086b3baac690843b158c63484219cceda9a4210ce67614d21086d33a0a690843695d05348421e8aa629a4210de27014d21086f0b80a690843399db43484219caeda1a4210ce67690d2108672bb4869084359dd54348421ac8eaa1a4210d667510d21086b2ba88690843e150c4348421acaeb3024210d677558121086d3ba2c090843691d16048421b8ee6b024210dc47358121086d33a0c090843695d06048421b8ce63024210dc5731812108673bb243a8043179cc64540218bae6322a010c3e7418d500861eba0c6a804399dd92154021cc8ec90aa010f637048550087b038242a804339dd92114021d4cc8908a010ea564484500876331a4228043b158d21140218f6eca80a010e3964540500872cb1aa02804317dd95314f40b32e1a9a87a04
  | 17 => 0xa0639a58a6015031c74c8b00a818e5a63580540c735312c02a0639a5896015031ce4c2b00a818e3554986430c61f3a0c0a90630f5d060548318deeca90a418e2d64548520c734a92c029063355c663d08319aae730e8418cd57198e420c66ab9cc3210631e9c065508318f2e032a8418d2c72551420c6963a2a4a10638bd954210831c5acaa108418e1d5498e410c62ebb4a7188631d5da538c431caaebb2a6218e5676d95310c6aab86ca98863555d6644c431b8ce53226218dc572991310c6abbaac898863a5590644c4319acedaa26218cd676151310c78aaa0a898863719c8544c431b8ae42a26218dd270151310c6e8b80a898863555d6624c431b2ce93126218d9574989310c6abbaac498863b1588624c4319aceda926218cd676149310c6cb3a0a498863655d0524c431e8aa42926218dd270149310c6e8b80a498863359db424c4319aaeda126218cd676909310c66abb4849886355dd5424c431aa8eaa126218d5675109310c6aaba88498863e1508424c431aaaeb3026218d5775581310c6cbba2c098863651d1604c431b8ee4b026218dc472581310c6cb3a0c098863655d0604c431b8ce43026218dc572181310c66bbb263a80631b9c864540318dae4322a018c3e74189500c61eba0c4a806395dd93154031ca8ec98aa018f53704c5500c7a838262a806335dd93114031d2cc8988a018e95644c4500c7633126228063b158931140318f6eca80a018e3964540500c734b12a0280639358e62d5321cacc6b0ea990e666258754c868f39ea92a643479cf64553218bce6302a990c5d7318154c861fbb2a82a643999896115321c5ac9316a790e366458753c8733312c3a9e43479d35394f21a3ce9b1aa790c3e7418153c861eba0c0a9e4317dd95314f21cccc4b08a790c7a7019443c863cb80ca21e43475ce5410f21a3ae92988790d1f7550c43c868ebaa8621e438d9516110b21caca6b086590e2d5418941c8726a98c498e431edd95014321c9cc6b16a910e55639875488732b14c3aa443479cf5495221a3ce7b22a910c5e73181548862eb98c0aa4430fdd95415221ccac5308a910e2e6458b538871ab24c3a9c439958a61d4e21a3ce9a9ca710d1e74d8d538861f3a0c0a9c430f5d06054e218beeca98a710e6562984538863d380ca21c431e5c06510e21a3ae72a08710d1d7494c438868fbaa8621c43475d54310e21c6aa830a8510e555318532887172a2c420c439394d620c6218f6eca80a110e1f5458e544872731ac52a2439598d61951218bce6302a890c5d73181544861fbb2a82a243475ce6415121c3ac9a9ca690e2e6458a534871b322c329a430f9d06054d2187ae8302a690c5f7654c534868eba4c629a431b5cb65d0d218eae3b2e8690c6d72d96434863ab8ecb21a431edc16550d218f0e0b2a8690d1e73d51434
  | 18 => 0x214141c9ac7310a0a0e4e635885050726b1ac4282831b9c86054c418dae4302a620c5f7654c5310726a9ac4298839654d6014c418bce6302a420c5d731815210637bb2a4290839358d5214841cd2a4b00a420cb571993321065aba4c3990832d5c6648c84196ae930c6420c7a70195321063cb80ca99083531c9534c841a98e6a926420e4f654c83210726b2a64190830f5da54904418eaed2a48220e3575d95411071b3b6caa08834d5c36550441a6aeb31a8220da67298d41106d2b94c6a08834ddd56350441d2ac631a8220cb676d4d411065b3b0a6a0883c554c5350441b4ce429a8220da57214d41106d9380a6a08836c5c05350441a6aeb3128220d967398941106cab9cc4a08834ddd56250441d4ac43128220cb676d49411065b3b0a4a0883659cc5250441b2ae62928220f255214941106d9380a4a08836c5c0525044196ced9928220cb576cc9411065b3b464a08832d5da3250441a6eea9928220d34754c9411069b3a864a08834d5d43250441f0a641928220d3575981411069bbaac0a088365dcd6050441b28e6b028220da77258141106d2392c0a0883659cc6050441b2ae63028220da67218141106d2b90c0a08832ddd941d40418dce431aa020c6d7218d501062f398c4a8083175cc6254041c6eeca0aa020e34765055010799b8282a8083cc1c1415404196eeca08a020e9663504501074ab1a8228083a99894114041d4ac4a08a020c7b76540501072cb1aa0280839a5895014041c9cc6b16a998e566358754cc733312c3aa6634b9cb5495331a5ce5b22a998c6e7218154cc636b90c0aa6630fdd95415331cacc6b08a998e365458443cc6973a6a5296630f9d06054b3187ae8302a598c6f7654852cc696b94a8216634b5d25210b31a5eeaa108598d2d7550842cc70eaa0c6a0e631edd95014331c9ac7316a918e5563987548c732b14c3aa4634b9cb5495231a5ce5b22a918c6e72181548c636b90c0aa4630fdd95415231caac7308a918e3554185438c6973a6a5294630f9d06054a3187ae8302a518c6f76548528c696b94a8214634b5d25210a31a5eeaa108518d2d75508428c70f2a2c620c631edd95014231c5ea8b14a898e4d6398a544c733312c32a2631b9c860551318dae4302a898c3f76550544c696b94c82a2638d15161d0d31c5ac9a94a498c6f76548524c697396a8a1263359c76350931a5ce9a928498cd673d85424c63d380ca212631e5c065109319a8e2b188498e2e65508424c71632a8421263351cd6110931c38a8b1e8298c6e72993504c636b94c9a82630f9d262d413187ae9316a098c7b76540504c717324c4282638b5926214131c5cc8b10a098e2d64588504c637390c0aa0631b5c8605503187eecaa0a818e2d54588540c71caa2c02a0638b9916215031c9cc6b10a818e6562984540c735314c02
  | 19 => 0x6b10a99962e5458843ccb0eaa0c6a16654d9d3519473287ce8302a39943d7418151cca3bbb2a228e651edd95014332c9ac7316a91965563987548cb33312c3aa4654d9c75495232a6ce3b22a91947671181548ca3ab88c0aa4650fdd95415232c9ac7310a91962d54189438cb0f2a2c6214654d9d3519463287ce8302a31943d74181518ca3bbb2a228c651edd95014232c6ea8b0ca89965563986544cb32b14c32a2651d9c460551328eae2302a89943f76550544ca9ab8cc82a2658b15162d0d32c38a8b1e849963564d46514ca3bbb2a228a651d9c664d41328eae3326a09943e74987504ca1eba4c3a82651edd95014132c6cc9308a09963564984504cb1b322c2282658d59161141328ece2302a81947571181540ca1fbb2a82a0658d5516115032c72a8b00a81963664584540cb2b31ac22a065999896115032ce4c3300a81967161980540cb1d322c02a0659698d6015032cd4c4b00a81967261580540cb38b0ac02a0658b5526290c32c3aa931c841945d7694e320ca36bb4a719065935d7654c832c9cedb2a641954d70d95320caa6bacc899065719c6644c832b8ae3322641954f75591320cb46b20c899065339db544c83299cec2a2641970d54151320cae3388a899065715c4544c832b94e02a264195c970151320caa6bacc299065639d2614c832b1ae930a641954f75585320cb62b08c299065535d6604c832a9eeab02641958f74581320cac63a2c09906571dc5604c832b88e2b02641958e74181320cac6ba0c099065719c4604c832b8ae230264194cf764cb510ca1f3a0c0a88650f5d0605443299eec990a21968e644c8510cb46b2264288651ddd95114432c6ac8a88a21974532544510cb64994c028865b24c96014432ce2a2b00a2194cf764cb500ca3b388c8a80651d5c46454032c9eec992a01964c764c9500cba5b8264a8065d21c1325403287ce830aa01943d74185500ca67bb26428065a39913214032d1ac8990a0196c532984500cb62992c2280651edd95014032c72c8a80a01967161540500caa7396a729e831b9c86054f418dae4302a7a0c5f7654c53d06a739ea529683179cc6054b418bae6302a5a0c6f7654852d06a6b94a619683535ce520cb41a9eea99065a0d4d754c832d063dbb2a028683539cb5394e418dce4302a720c6d72181539062fbb2a629c83539cf5294a418bce6302a520c5d731815290637bb2a429483535ca530ca41a9ae72906520d4f754c832906a6baa64194831edd95014241c9ea6b14a6a0c5f7654c5350726b1ea5292831bdd9521494196ce3b2264a0d4e72d4d32506a739ea4992832d9d3614c9418f4e032864a0c7970194325065a38ac81928393995320c941c98ca99064a0cb4745843250637394c7a82831b5ca63d41418bce7316a0a0c5d7398b505063dbb2a0282839398e6
  | 20 => 0xd70d954310e8ebacc4a1887659c66250c43b2ae33128621d1f755894310f46b10c4a1887475d66150c43b1ce530a8621d8d729854310e8fbaac2a1887a55846150c43a3aeb3028621d1f755814310ec7b92c0a1887631c96050c43b2ee2b028621d94715814310ec7390c0a1887635c86050c43b2ce23028621d95711814310e4fbb287a90871d9c460548438eae2302a421c9f7650c5210e37bb2a429087c350d5214843d2a87308a421e95435845210f32a92c229087a650e6014843d3286b00a421e69525805210e4fbb287a88871b9c860544438dae4302a221c9f7650c5110f46a1cc428887a350d62144438eeeca88a221f15435445110f32b12a228887a650e6014443d3286b00a221e71515805110e4fbb287a808787dd94354043c38eca1aa021f1b7050d5010f8c38286a80871d9c462540438eae2312a021c6e721855010e36b90c2a808727dd94314043d1a87310a021e8d435885010f4aa1cc228087a550d61140438f6eca80a021e69625405010f38b0aa028087559c75394f428ece2302a7a14757118153d0a2fbb2a629e85559cf51947428bce6302a3a145d7318151d0a3bbb2a228e851edd95014342aace3a9ca721476711815390a3ab88c0a9c8517dd95314e42aace7a8ca32145e731815190a2eb98c0a8c851ddd951146428f6eca80a121657535865350a2fbb2a629a859558f51945428eeeca88a2a14767198f5050a3ab8cc7a8285179ce61d41428bae730ea0a147b765405050b2b31cc2282859558e6114142cacc6b08a0a1655635845050a3b388c0a98851d5c46054c428beeca98a621655535845310b2ca9ac0298850f5da54908428daed2a4842162d75d954210b173b6caa10854b5c36550842a5aeb31a84215a67198d4210ad2b8cc6a10854bdd56350842d1ac631a84214ae76d4d4210a573b0a6a1085c354c5350842b4ce229a84215a57114d4210ad5380a6a10856a5c05350842a5aeb30a842158e739854210ac6b9cc2a10854bdd56150842d4ac230a842152d759814210a97baac0a108563dcd6050842b18e6b0284215a7715814210ad238ac0a1085639cc6050842b1ae630284215a6711814210ad2b88c0a10852bdd942d44428bce6302a22145d731815110a57bb28428885a398d4214442d1ac6a10a221477765445110b2ab1aa228885c95095114442d5285300a2216a9425805110b38a8ac0288852bdd942d40428ece231aa0214757118d5010b17bb284a80858b1d94254042e56e0a12a021728705095010a2f398c2a8085175cc615404295eeca10a02168e635085010b46b1a8428085a950a6114042d4a84b08a02147b765405010b2cb1aa0280859c5855014042c9cc6b16a9996656298754ccb2b31ac3aa6654d9c75495332a6ce3b22a9994767118154cca3ab88c0aa6650fdd95415332c9cc
  | 21 => 0x1000000400d00080000080010008018008000000000801200000480000000040040000000000002001000000000080180040020020004010006000800c0020000008018000003002000c0040000000000002000001800000000400080040180030000054008000004802c00400100280080020000090014000006000000c002000004800000400400600000020000010000006000000800c00c001001000c00200a000803800200300380040000040010004000001003005400200500000000040000028000008000000001400000000200040100040040000002000000001800c0010000018002000009000800800f00000080040000040048000001002000001400500000040000000050018002006001000400200000000100040090008008004008001000800200200100140000010000000000001000800000000000080000000040030028000009001800c0000000000008002002001800c000000004000000c0000008018000004002800c000001000002c00000000a8000006002000003c00c000009000400200b0000000000007002001000000600000000200010008010006000003000c000004000000400a0010020000010000000000000c000001000c000004000001c00c0010000004000004002800001200000000040000000028000014000000001c0000100000008000000005000c000001001802c00400100000140020000000000000002000000400200700080400000000000008004000001000c000008001000400600a001800001c0090030010010001000800401a0080008000018002000000400e00000000000000010010000000000007800c0000040000004000002007000000000a0010004004002004801c01600100080000260070038004002000000000000c00100000000000050038000002000000001c00000400400040140030008000000000008000c0000080000098002000000000801000000500000180010000000000000001800000400200200080000010068010002005000800400e00200c0014004000003800000c000001000401e005001000000400f00080140000000000008000000001001001c003001000000000f0018008000001003801ab338ea5296871d9c46054b438eae2302a5a1c6f7654852d0eb3396a328e871b9c860547438dae4302a3a1c777654451d0e3dbb2a028687599c75294a438ece2302a521c75711815290e37bb2a429487599cb51946438dce4302a321c6d721815190e3bbb2a228c871edd95014243ccea4b0ca4a1c6f765485250f32b16a328a871ddd951145438ece3316a0a1c757198b5050e37394c3a82871b5ca61d41438f6eca80a0a1e66629845050f32b14c228287999896114143ccac4b08a0a1c3d769524310e2ebb4a921887875d76550c43c3cedb2a8621d1
  | 22 => 0x2000200200040160020000000002009000800000e000000800c008001000800c002002001000800000400300440000000008000000000001800c000011001000c000002000000000800100000140020060010000000000000000000a0000008004004002004800001600000200d800000000300040040020028034002008000800c002000004801c0120000060028004000000000401000a00280000020030000008004000000002c00000000080000020010000000000003002800c00200100000480040020020000002004000000c0180020030010008000003000000c008000000400a001000000000a0000008018004001000000400a009001800000000600000040000020000010004002011800000a0000038078000002001000000c00000000140000070018000002006000000000a00700000040000040020008000001005000000200000200140000000000000006003001003400a00200180040000030000000002006000000c002000000800800c00c00080000000000060000002001003000401000c007000000000100080000040010008000002001001002401203900800140040080038004000002008800000800100000100000040018000000002000800400200100000080000000030004000000000003c00600100180000000000038000000001001000400000f00480040000010010008000003001000400000200080000000000028000014001000000000a00b0008008002002008000000800c0020008000006003800400000200080000120040000000008002000800400400100280000040000028000000003000000000200100100000080080008004014003000000c0060070080000000001000001c0000020010004016001000800000800500000000000070000014004000001000c00600000080080040040028004000000000800800600000080040000000008028000001000000000400000a80140000020020000000000006800c006000003800000000100000080080000078000000000000000c006004000800000000500180300000020018000002005004801800c0000018000006000001000c00a00100000180040150078000000008002800400a0000030000002003002800000c0070038000004000001000c002000000800801e0050040034002000000800000800e0000008002003000000400c00000080040060000000000010000000001001600300100040100060008004000004004000c01e007000000003c0000008008002000000000000000000100080020130000008000000000001c00600000000000020020000004008004000801400000000180080040000010004006009002000000000300380000060020008000016002001800000200d001800000c000000003400c00600000100000020
  | 23 => 0x7b237380004568773ea800000021212a00004a6c7f4ff82a800000059eb608252ba525b2b5d4f003c09908c869c44f1bf2b90b5a2d353a99fd5a6b7f5fb10a49c868e4c200005d24210002db98e230439598f42fe41c2da19017520000000000000000000053800000039300014d8c255ad1b2d81a7796cb8ab8000932285a380000618000188d26225f388b5f9a70a492540a81a0a0dc12c85248025d53f0a9c51127480c5a8350c28995a100003c0a46540af38000000000042d03800043a8a7400026054ba2ad01e48801287e80000003e8000000000000006880009d000000010f0a4d000137d088b055dd32e91540005b39585338461126b1dc498a1c545967136400068aa10021e0000000a7c06e00018e00000008cf4a5800000000044b07f80006e90001510000b286b1b4c400041727b207933e7b62ee982800091a0000f84de000000015a000000000033f00002cf22600000007f227f00005208b700014c0c64d6a03ea7bcff69135f504e4f2e66b291b50078a4950ea927877241908400016a4c52409ac59b3e0000049c84bac00035db0e8d26ad400000006284683371af856ac6412ea0498a60d5462a0e91d200057cb0380003fe00034ecf9c85d26f19cd108684000361961e14724c8000694b4524c0e71a4e0001e0000185270000000001c6000414800000000000036f80002a200000000000001daa85d1a29ee2012160e7ad8315d000000000000015715f60005b6a9740008413509ad5a7a00004d94d4b12cc252f0da47185b800000000000000000c34000c140000000000a1200000004da000000000000000000000000005c20002dd83b005c22a1af55e282e480adf434a6e0000000185c71002aad84d700000002658000000263996d20a43c296800034e9722e9b7118a26580000be0c8697950b00006a821438b2b1c00000000000000004ac00000000000000b4800057046400014700000cd000000000046600000acc22b180000001b902e637b3175b209df0011c18250a1900027740004d500000004065ab07685c5866a1100029800000000000e94f580006100000a2c0000000000000000521800000000027728b93b48436e4aa1d80e1c02ec8f20f4067a60c849c00080400023a1b6035900000010aa1e90002fb585070d0682dc8dbcaf80f70200d6e6eb050801cc324c10d60000de4c496df85b400030a1408bf554024f4250a984a01c61999a600008685bc09e8000387000000000000000000008a29ba486b3d0e721cf00004e8d228ea16d151c000b8825880000000002c30000000004000c020005000000000000000480000000070000018004001001800000000400900040060010058000000002000800c0000020018000000008002800401c004000000001c002003000800000000200100080040020000
  | 24 => 0x369909266d68180e000000000028250a62720000000e1c67b62a16d56e200017780016b20000000b240000005ec8000d8e00000026914e00002000d246a0cee46419f52186b13c28001a3a7a82362408fc40006958000000b1900000000000000002970b9ad574498000000af7000283c1ae0000000000d2a2213e5a63c36800000000008060f46e01b10000000000000084e0000000000000a1a3f30000000a9c00000017720000001eac0000003be800149e8153e3116800000038e1660000284000098c00000065320d8000bfc0000001028bf72d20000b920002c70000000000197928c000000172ad61b460001130e7880c6ea24e85500005eb0000dd937a5830000000000000688800000048e29a000058e3221f8aacda028b0119abbd98a43f6892c8020251800001c93fad521d99db4d0c00044080005dc6526c424ec42c98b615ae8d2787eb33b0ad96025584c30454af4b2d19c2370be687b0fc8001a7e27e2fb21bc45acc40af3330b867c93ac01b5a68b4322200f46eace646caf9800070b088a5689480004872598000b264ba08bd6a019b6a12448e1e609000078880a0004e126249c400040198a0000c4a0bb8394000b5500000000004722f200012ba82a000335000000000000017d80000001ffc000caa67e80000000000ec80003e6b17557800000002d000000000088862793e0c0c00019206580000002c2133540a2a302da3d000000022984306200c30003290b6472a3b030188b260467f0a30e602296ce1d044e6000000000142600057f000138a87e6ea93a800052543e9cd8fda9f146e9b24ec623b0000add9b60004438000000000000007d1ea40c0002f6d4f400061b26a4f10a760001c300005f061c80006760000a300001c492b00000000004c3011b43849c00566d0d6d96890a25eaa910da545345317d14871f00000000004110000000000aa713734589985135c911a800000000000014b400000000000000ff000000126c0000000829b7adaf17c92cc6e29f5670b37c00000004080000000000000aa19e06fd301a51d9201d75df896c0003f20002f90000cd80000000bdc000000058000000000014210340005709b2000000000026f8000c9100000000000000000000000000000084c00000051334718682d925c827d99ac942a9a6e0f601440fa8000ee21550002b3c00000024b00012100b13fe977c08c978000335c632daa6a0a50451003900019540000004e034d52cabf8332903800096c5011a7c0000004f400011bc000000245000096e67187a847000000001fc0002f60608000000b103f0047cc562b026035ad19c3d1000304437e25a02c9bed5784130001c0cb1600000000003d60000000cd9536c23000000000000000000000001c1000000043eb390002850a9e42e1d72cfc960
  | 25 => 0xa74d5118798f701940000000000000000302800091d5e627ac00000000029a80000002570001996c4800000005ac00041e88040000002a605ec4bc0000002a085a26fa0001d1cd9463965410bd4f83964ca8af88e69d61b3056c2e80864bbad6d656dcc5dd94a92b07cf36120b426c0000000dec0001800e284780001735650001150b2a38c134802e2f42cd85acfe83ef6d89230b24b4a00032640009a20000d8876800000009d8000000000000000065946a0000858074576000161c5d03362b64674bf0000135c0222b334380004b0000065325800000100022080001100f3a06c4ca0001e6a2b401e4b80000000000000000000037400016f32b4ddcbd219a84490d400000000002329823d49cec000a2100028000000000001784000af36352168e8000052a00000008f922e800000090341907a038ecef0d905f82ce208000328c22ca744d091ad29439308e0b180009b64282084d561b11be867d9944041a69ab8c620000001969ac003b0002aa400000028d083c0000005d68000000000000000000000063780000008c90181a040001a93920df10f85a26cf0484324667318339ca188bf11e83740005a94470a240000000b080000000001360000df20000001efcb460000001c68e36000000246400010007d84e03da3860002841b5a8f833aaa7c0000000002de80001b30003430b8c0005cc0dc000000060780000000004bd00000008b83968b049204a10b500016f683f22807d169aada52bab04df0af46260f100103776458af4d54ab800035a00000001dc30ed9ba0f0204b38000000067513089b642566712f000021b2c6b1c0000bc40000914dfc00000032600005bd0d08e7c00000000006a91d8ac30d591f4144bef46812c8000000000281948445859baac19c431e00000000001ec1ea13cc000bff067a180000000473800000000000000014fa000000000000000012e2d9818429b000263174e4360000e5d91a83866e00000006a217b9ce00c40790000b515546a364200000000d9000000000013b0002e44000ac50001f0c2ac1dd00000000000000001549032d8c06d273c00000000005f00000000b288140800000002cb80008fd289312c0000000000000690aea0d6800000025200a000137619c00000000000000002cf07648981118429a3e8b31e60001a1a7bd3170001ad848918a8d603bc1b50000000a8600013e00000000005d80ea8000c7900000013fc00000000000005fa21189d17ae591052000005400000000016d47a400009a1514b89147acc4ecc0004fa2a1926000018eb66c13455708c0000000000000000000000056895f0000000520a6bc2660f82a1000176e0002cab2f489c000288800040e0000002a64000000000366800000000000003606720830000be2000660a9cd4aa000000000030c078000
  | 26 => 0x28000db6b072b5188400000000000000002b931da8ec28a000000184800000052fa0395200004b386f97ca00000019a40000004da9ca521e49330580000000000000e4460e3785602e0556c463491af200007205e7ae752e22dd000044d2d460500000000007c70000000ccc000000000112e000000000000082768cae817d065454411e8c3a000000149d36696b56591058620040000000944000000000000099b0c98b4871ab1d5ba800055aac2000373400065c4ab000000000000000017666505a39e7500200000000003a287a00015014b000008b80d16ca45c0c2987c000000189b1712507b36e900000002cb30b800000019d00028e59a62e40fb8d45b840000000000cae00019886a061e7010000d54000000539000017c000000000000063300000010500000002c4d528625000322803447c3b080000000000000348000000546ae640001fd17592d4cee0004a71fd80000005a998b400059f32388d4308cb20af8001558000215a8880005e92fe1a74be8722000283800038b62c35e800000049e800172838900007480005cb4ad8c6d49855d0000000cba109000029564e000000000000016c00000000000005849fa8000be9000000061c00000005455a46e557f800000021500000000000001ae929c98a6164e30c098f800000002345d0acd00017dd3cc0000001b8c000099000000071000000010909b421145f00007a4651000211527207103b31e041c2ed5a7a4e0000b4b5f713ec8961585c99e980000f627934c0686446032af7c996075588903d64a0000002c90000120067193c0000004eda11c000bf500000010ce907030b584f283160000000e3cabb00000007760000001fdc00086500012a406460f1e18e5032a63a3ee000000000065ba35c0000b6600800044a807000072400000000035387ee8a50bb00013901526a61fbdaee00000031889b20004a632f877e69600000010141c80d200019ee0881fe81dcdbecc000f17155f80004d2a60008a6ec5d20000000399000000000054131213c4304db900032086780000001d787020f20b1a3b817ad5a0000d70000000000000154200000000000000002e60408a9c00000000000007173d1800180a000014804cd3c2dc38427c80004331b0800015a8f21f1800131c00027d238d1340e707400002341ca36024a80000000002ec4000b570a00d90a325560000001b6ad2437e2cec75e0005de0000fb63a367d13416808620000ec41b0c6c0c51c54000000168000012e8801800250000dc30001e3c5c60002eb9e440008100001b68320b4809108801d63d9000000007e0000002915b22737198000037800000000000005af21c07101c2aa50e1ac31a647b41ba28c17b806f0ef8378598bca66822f40323905eb1934000b7735300018aa94532533b0c369f00760b1406
  | 27 => 0x36c000d4f51a0b551f4dd11030ac9818d8f2b000014805b96a18000d640522e90178000aab00009881a60003f180008f27312df1b400001242f2885d8808ac5a300000000000002f78000000000000000056300000000000006b7971d7e4c6641888fd0c80004ea00001720000000000c0200000000009540001430001a140002c500001de0674a908796e03d36db1195b8a4926498a1c000b9b0139b60f1c91c3df08a99763d50000000000000060053446c0002972510000440000000037a00044e9e413408ca00006bc47800000017f800083b59080012e6ae26d2101c0000000f205b9a6e6685aa000000000040b11140000004be000000099e43fadb18420001e783300001040000ca4e5cb5d366359495a0004c380902f4bac00b32d4000975000000000022200020758fc000000000000000000000009063b646980000000003f21d38000d76000139c000585000000000000064402ec2e40006e380011780330000000000dbc2730000fe204b6c930b517479b00000000000005b98000000000423000000000029c800000013017000001f237a00000000005d1382984c000d9829900000008b54591e6400007b00003dc0a000000012dd0003e66d384c4b4250519398d40000000000000000c354e5155105ed551841dfc164bda2ac8ea4586b7923c03a5aea00050f1eed5749aa53bb0f4306a1d48f32f104a00000000009d06b34620fa573e0000002138000036000000000051000000014a60002bc000000049a0001b1800000026e9bb414c1b74a68f6800000051eb1ec00061029b242d49c9fa2d88000d0636b29b82cc00019a49b80009b000059c0a341ccb040e110e58ac72300019100005e00000fb817e4f51f28000a280000000000118ae8000000070400069087c81e609800000012c80000000c7cd2e00057aa08c0004f00a180000000000000000000b1c0000000a9a6f40aca61400011d11827a800001d0000000000b3a0000000000347000000000000040f92ad3d200055a8000aee0005498000000d5d3bd21c1aa09dc2818f040005bc00000000002f200000000006e1650000093613e0639d400008df48226b1a966d16b30fd518273300000004ce0000b80000da400058f000198600053f0001a44ae913aabb52ae0000000f190bcd3328781757ce00d1e3800127cd5e21d120053c0000002c7c45808754b0000f18000145068d0a40000000e000000000002948000000000307d6980001562c88000d170000e61a5c0002fab6a4e3a16629db6287c479e3e888601a8dd36192c0c000c8600000019e20000000000000bc200015c000000000000000000006a22e38480b344e180000240001578fec9281e10000000000248123acf98063e75c28fe4ce2da55c2287c0008790160cb0ae40003670000000ceb27
  | 28 => 0x5507c00001bb5e980012d221d3248834000a790002458000000000268d46223e3178fd9b26dd400026c40000690000000000000000000194ab690e580011aabd12e4298800046f40630fd5b8bbd10e28a437000000000008545fd0001698000727000186966cc08000373c000000000368913ea590002df031a04c1d21bbdafe3955859e6800032e0000c5c0002000000e84e8c0002e50000014d395d70dfc00000000019c00000006be000094c0512300bf80000f11ce8d7c00000023a80000000000000001a5ecbf000127c0000000001df80000000a40ca80000005dc3760000000405b5a4f9400054702240c800000000004f0b3500000002c40bc0c780009fa00000011fd524000325acbc1ea000000000092e00000030a92849906ab2b7c472ade5630b2994edba2cb81980000923f6027027a6ff19025fc000cb60000e9c0007933f3aea01561421c280000000003ff2230000c1a3d2b5cd5180003fe35ec5380000001cfc0c05010000001a5a0000371f10a1a5046940358b9c0000001eb8e5869a053978c00095e5400000000da80000000000a2d6929fe534c2ce000112000000000000015c0305691a3bce329f663917a115e0ba1fa1a00ec82853a2020c278b6b3e0000124a9f300035893b08720000000000b8c00000000000000002b5400000000000000001e5476ab98fac63e0002f8ce125c45039d28c8a74b572800178a000064316c0000005b180004e200000027e000092c00032accf00005b42e180003e454212d00002fb2f3000000095339d08900000006e72bf55620000001a9000070a00021a40003cb26228a8b581ff0ad2284d120a324311a4bd8dbb32f2e8953ad1b5640fa16fc00000000000007ad1fd327000010363414799f20000000000ef6b8700000015ce00000000000000003aa2fec050a0c0002ab99f65020000bccd040000d0298c000c8346036b0618c2c33c80000000000002890c90a9e2e092ec000c026460f5cb6e0001e714e8cc8d471f60fb4f042bb00000008bc00e1b51ebd11e00000036340000002c3800152a3f80cc8bd4ac4c8058a8f6048c00063a8000c106af000342008453f6563518a507de39f2ec84845826111a482de5b6000000065a2a546180000000001400954b4ebc70001d64b9e000000000000072569615a51ac15c0001380cc6a2b5da0db1b40d5f0cb80000000002871d713c0000000007000000050400e81d43a05c10000000b5e0000000000000161000000053e1ee80010300001f598d800000019900009ee75a17100000009cc6c48000784000000367502e00066902d515c0000001da95e451f484800066e6dd4c912700000fa00000010d800000037401fc0000b22455742c95026823831c3211c19918eec00000036140000000000000000c2f08a000050400049323c00
  | 29 => 0x8ee0002c635d06a61e300016580000004e980000000001c5095c000b6f000258168200000000000000000000000000000000000000091f3d3b5c400009d1600000000000000000190e63c1cd30f07b628310625455ba0004df8a4c4940004fd90a08be000124800000000000025c13bc7cc0bc8000a404ca062000085a949466822ce6488b00000000006dc6329c1d3d809635a33191060000000000000cff2beb72c0003b056d80014746e21a59ddc0064c80000000000c9b5c78000da84e954c1e7d48e00009aae6879400000036d00000004f3800000000000000000000002250001b2cc6b00023f8000575000000090ec9738100013b20000000000ad6a3500000010cc95034e35653c675f00004ac00000000028fc0be47400000000000002f783908e0b30533000000000068308dd6c002f19ea1086028a7413000157acd6000000026e0000001ba0e5ed3c3eea604542bc6537854c0000000001484a0c0854d8000000029136b8fcc000c1352896c14d600000005759aa2ea63980013ee4e1426000000000068807300c649136180000007c515a0000000be20001e598c0c810000e8800065f000000000043e40490508624ff5998bf02586742ef01100007f353422980005f200802a0c680001aba020dc868c00031100000002bd80000002025e5acb000047b29105a00000001b00001138a446792c506502562218000000954223af34000000000000144a00000025b400099a533800000000000000000007701a00000e265f800036058dc00064ea8c80000000000229314a8f0000840f2aa483f722c57e8000048800000000041b95bd43062947280019a2aa600020c19d05263ad91580000003c4a2a41c0948298800000081144d80001fa3ac33000009144ba571800000000000014f4ae800000000000006ba057215d3780002c806440006bc18184955462df68f0000f9a20462d2be800054b599000064ca855280f7c68acf53c0a1d11c8a653a11ee995c0b70002484a5600000016753288760000d09962b830002f000000000001621a40538502179db0e00000c000029800c00018a8adc00034c9c51a9a12a5cb000000000000000000000001a78eacf540845a4b41c00026b00000005526d663a00000000000000f592b20000000fa80009612c7800150677200000019d200049a800000028e0001f6584c00000000004fe000000000000000039a11b500a0a03f436380006b600000000000000561bc40000002b995e5306c5e1fe000120c000000000188400000000009a809e4101da09c60000000f4000000000024a595e24161c1d480005290001ed400096f00028e15dc0006e0b4d989a3120cf3118fd24af000275c0000000170000000a1b00000000000002a4876c24c4f91ee2f840000000002ea8c000000970001512d641
  | 30 => 0x4da22141dc00021d87bcfbe8fc69d00000000c600000000009340000000a2a581000000055667c00000000000001622aa15d629a1b780002ea0490000000000000000366400035a14c0d180009ae0ee0000000c095ae0000000a2f0000000cfc2d82852e349a67985ab19597aa0a924295680007840000000000000000000000083e0000db40000003541124ba85ed00024b922200049100000000006228000000000000000000000000017a938e00041113b10906531332ebc9ac00033500018ae5db4fe000084c9e4205b05c00000000027440000000000000c70acc0a80001a123a863080013a4d454db81618d208242c882d9da000672000074c780277a8284ee00000000000000003dc800012068b21a104000000000000019ec00055f0000000368000000156833400000000002953f29d3d7200950000000000d0b000000000007a4e223492c40476e5159c0000004902bd954400021900000000003ce1db0a900004e0afe4000000000106ca2e00000009ec00085f3069080000b9c35280000000002478000c18000000309c83c000000289d72e00000002d00000000001f4d7ba00000000015a00000000000000279299800117200051980004de0000002fac21cc63581000018a0000000000c04bd82bf80000001b63b3a674000cb048016b8000d2a0000b21acec7a23700004960000fe25ec86a0000002ed5a1e7655e821340000000002add9665ba42b1cf1b8cbab46c2c3457e7860002008000000000000000066100000016c80003d0a62000000022da2506300000fc2c20c980d16ca00018da3ad0dc90599b26a000000012b800000018540003560002788000000373089c00000000000001700000000000f240001ef15280007510c3ac8c00062737aa3dcfea0000000001a5200044ab5e110cd185a23320042c6745a2dd11e60002d99e340000000cc0000d6038400000010a89272d40dc80000003669e2c044d0019f9a6d76c00022a800187c5a5000000099c00049f8000acc0483c5000000017d276b33d1d68fb21bb528bb80002c99db80000003ab1e1d98e8da0c4800091a0000000000000000369837c00000033100000000153ab93acc383732aa813991ebbe14b1dcc6984c600012fd0b65bf1219a514960000000001aa20006a9800064aa5b54d1da40000004cc80000000000000001b0000000010202940000001294fae0002500000b76b0a303a80d90a00067c00c44fa84b0000c2c0fc00000025186f255102a0000eea97d11880000008cb09796a800000000582bc25a000000316400000000000000000006d5800000040d3ba1ae40000005568001bae0001308001230000000264c71c000000000131a31136780003e28903b7848c000a2800000000000004a19908ac80000000000b2894000027b400041255c8604
  | 31 => 0x80000000000000634db20000000b803060003408fa4c180c62e00a12c9f1959ec4ef8c002f128b00b47b75c59d30db200000009a8d4e0000000d7804c00000000014c20006ec8000c4091739400009b822e35f8001a925070001f683a05f9152000000000051b0001860db7173b10c3ec5464a7af5000000000029a53220003a183f0b32b9e4510b5d7e289e17f93d0c5855b69f00003a84fc36081ad35a0002b8800000000000025f8000000000214483a0001cd95b000024451e04153564226d99fe922040a17d14bc6a4000000000000051d4318000c9c66f0000000bf6d7000032685160004bb00000000004e72d886881d60002330eba23a226b02c0000000ab940000000000008240005762ed257c00061e1b180019ca0004d3824c0008e636a800000000014927e5972000000000000048b06580000004be0000000000b1a3821fe000060e14a04fc0000575a885e1ada000342a8f80004572689d4d89c00060e0ffce2414b00000000000000000000192b8a0000000fe0000000000000041800015f85b62bc0002c4994200053da5a000000011a000125a9e566f1d14d2099750ab5e4ada7a21b3b010f828b61c7a5544502f10000a5c000000000209000000000000000360000100edcc7e55020d356077a0000d304d12360003e4107c0f8ace2ffa80512400000020b0c4c0006d722810780000001189274000178001829e00000000008ce00000000015b00000000001494ac400000017f455e00006b8612bc968d073400006a41ca319b423ba00014b10dc0000000000000a915fe9d24000c370001bdc000c10583000072400008d8001146a6424092087780004198a9c21a6ad3e100014fed0464f00000001fb132012978659e00010f40000002af9d55248d130000001a280000839f600002510002ca40008db0000ce57c0ac900017610e20000341b1499e4153b127255e03f0000258d4acd5b020813d39a0003c19594884db81f011f8c82000406a9b40ac8ff39a8505aa8614470800039c68f000010c0000000002c6c68200000002c00000006eb00005d88c7000000000000049780014dc0000000ac400000056b3054000b95000000000000031109c0000000000000182c0006ca800000036e0001148000000354aafd396637439aac8b345a034400013c2b00170b140000d5c446b61146e00000022280000000000000000000000000000029900000000008f141a8000f782cd0000000000000000000099233e415a3099700000003239b160000002fcc00000047b01b192476b0ed2ff8d1a3c9000000077ccc923b22ed912073654a6a08e20706209ab1848a20047b3cca788e200000000009335afa6e40008340000000432ca20002e99adc00000021ad1220000001bcc0000006a427548600533ea000064603e4cc1de0434c1b
  | 32 => 0x100c52460f30740004845058001782000000213c00085c00035c98ec000000000188e580000074c0000006be8d94310c7d6930000a360000000000000c1200009a40000000002d3
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x261f05341d0024113228404500002d1b2e12022533300e2a000c46173e0d00004236370000004701002b181c29002c15430f2227070a354804233100001e1603493814003b443f0810212f133c413a0006000b4a20193d09001a390c04c80811218005280400b000c10008000830e40000e05435496114843e09435496014843e05435895114443e11435456014443b09821c14354043b11811c14354043d05535c45350842d09535c05350842e05635095114442e21425456014442b09831c14254042b21811c14254042d05545c4544c832d09545c0544c832e05644c95114432e41325456014432b09841c13254032b41811c13254032a4980195320c941d05535c85350441d11535c05350441d05735485250441d21525c05250441931801d53250441d05754c83250441b11831c14154041b21821c14154041a29801954210931d05545c8544c431d11545c0544c431d0574548524c431d41525c0524c431951801d5424c431d0575508424c431b11841c13154031b41821c13154031a19801954310d21d05545cc5448421d21545c05448421d057454c5348421d41535c05348421961801d54348421d057550c4348421b21841c12154021b41831c12154021a48854c9600c940a50854c5600c540a60854856008540c1a765c05450f30a28855096010930a30855056010530a60854856008530989821c14350130991811c14350130c2a765c05450b20c4a765c0534cb20a188550d6010d20a30855056010520a50854c5600c520989831c142501209a1811c14250120989841c1324c1209c1811c1324c120c32765c05450710c52765c0534c710c62765c05248710a188550d6010d10a28855096010910a48854c9600c910991831c141501109a1821c14150110991841c1314c1109c1821c1314c1109a1841c121481109c1831c12148110
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1802
  | 5 => 8331
  | 4 => 3546
  | 3 => 75
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
  | 7 => packedAt gbK7 (718+((h/13+packedAt gbK7 (640+(h % 13)*6) 6) % 49)*7) 7
  | 6 => packedAt gbK6 (55854+((h/600+packedAt gbK6 (48654+(h % 600)*12) 12) % 2163)*12) 12
  | 5 => packedAt gbK5 (355456+((h/2777+packedAt gbK5 (316578+(h % 2777)*14) 14) % 12096)*15) 15
  | 4 => packedAt gbK4 (189120+((h/1182+packedAt gbK4 (173754+(h % 1182)*13) 13) % 5663)*13) 13
  | 3 => packedAt gbK3 (4675+((h/25+packedAt gbK3 (4500+(h % 25)*7) 7) % 91)*8) 8
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff87fffc3fffffc0e38fc7ffc7ffffc08f1ff
  | 1 => 0xf07f83e3fc1f1f1ff03f1f8e1f8e1c3c774e93
  | 2 => 0x7ffc03ffe01fe3ffc01ff01ff01fc3878f1c
  | 3 => 0xff800003ffffe003ffffe0001fffe003f80fe0
  | 4 => 0xfffffffc00000003ffffffffe0000003fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x80000400000000000201200120400001025
  | 1 => 0x251128c488ca2a20b0190c844c8448b8334692
  | 2 => 0xea221949114654055640152095209389858b18
  | 3 => 0x430752922294064a6aaa40011a49c112d80dc0
  | 4 => 0x8c4463003b1898938d349a49c00102236ee000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeeaeaa8feeaeaa8feeaeaa8feeaeaa8feeaeaa8feeaeaa8feeaeaa8feeaeaa8feeaeaa8feeaeaa8feeaeaa8feeaeaa8feeaeaa8feeaeaa8feeaeaa8feeaeaa8, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12911
namespace PEqualNP.Outside.L_meta_12911
open PEqualNP.Outside.L_meta_12911.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 75 := (concat bgb_3_0 (concat bgb_3_32 bgb_3_64))
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
theorem bgb_4_3520 : Interval gbAtlas 4 3520 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3546 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160))) (concat (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)) (concat (concat bgb_4_288 bgb_4_320) (concat bgb_4_352 bgb_4_384)))) (concat (concat (concat bgb_4_416 (concat bgb_4_448 bgb_4_480)) (concat (concat bgb_4_512 bgb_4_544) (concat bgb_4_576 bgb_4_608))) (concat (concat bgb_4_640 (concat bgb_4_672 bgb_4_704)) (concat (concat bgb_4_736 bgb_4_768) (concat bgb_4_800 bgb_4_832))))) (concat (concat (concat (concat bgb_4_864 (concat bgb_4_896 bgb_4_928)) (concat (concat bgb_4_960 bgb_4_992) (concat bgb_4_1024 bgb_4_1056))) (concat (concat bgb_4_1088 (concat bgb_4_1120 bgb_4_1152)) (concat (concat bgb_4_1184 bgb_4_1216) (concat bgb_4_1248 bgb_4_1280)))) (concat (concat (concat bgb_4_1312 (concat bgb_4_1344 bgb_4_1376)) (concat (concat bgb_4_1408 bgb_4_1440) (concat bgb_4_1472 bgb_4_1504))) (concat (concat bgb_4_1536 (concat bgb_4_1568 bgb_4_1600)) (concat (concat bgb_4_1632 bgb_4_1664) (concat bgb_4_1696 bgb_4_1728)))))) (concat (concat (concat (concat (concat bgb_4_1760 (concat bgb_4_1792 bgb_4_1824)) (concat (concat bgb_4_1856 bgb_4_1888) (concat bgb_4_1920 bgb_4_1952))) (concat (concat bgb_4_1984 (concat bgb_4_2016 bgb_4_2048)) (concat (concat bgb_4_2080 bgb_4_2112) (concat bgb_4_2144 bgb_4_2176)))) (concat (concat (concat bgb_4_2208 (concat bgb_4_2240 bgb_4_2272)) (concat (concat bgb_4_2304 bgb_4_2336) (concat bgb_4_2368 bgb_4_2400))) (concat (concat bgb_4_2432 (concat bgb_4_2464 bgb_4_2496)) (concat (concat bgb_4_2528 bgb_4_2560) (concat bgb_4_2592 bgb_4_2624))))) (concat (concat (concat (concat bgb_4_2656 (concat bgb_4_2688 bgb_4_2720)) (concat (concat bgb_4_2752 bgb_4_2784) (concat bgb_4_2816 bgb_4_2848))) (concat (concat bgb_4_2880 (concat bgb_4_2912 bgb_4_2944)) (concat (concat bgb_4_2976 bgb_4_3008) (concat bgb_4_3040 bgb_4_3072)))) (concat (concat (concat bgb_4_3104 (concat bgb_4_3136 bgb_4_3168)) (concat (concat bgb_4_3200 bgb_4_3232) (concat bgb_4_3264 bgb_4_3296))) (concat (concat bgb_4_3328 (concat bgb_4_3360 bgb_4_3392)) (concat (concat bgb_4_3424 bgb_4_3456) (concat bgb_4_3488 bgb_4_3520)))))))
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
theorem bgb_5_8320 : Interval gbAtlas 5 8320 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 8331 := (concat (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 bgb_5_992))))) (concat (concat (concat (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120)) (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248))) (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 bgb_5_1376)) (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504)))) (concat (concat (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 bgb_5_1632)) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760))) (concat (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 bgb_5_1888)) (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))))))) (concat (concat (concat (concat (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 bgb_5_2176)) (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 bgb_5_2304))) (concat (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432)) (concat (concat bgb_5_2464 bgb_5_2496) (concat bgb_5_2528 bgb_5_2560)))) (concat (concat (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 bgb_5_2688)) (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 bgb_5_2816))) (concat (concat (concat bgb_5_2848 bgb_5_2880) (concat bgb_5_2912 bgb_5_2944)) (concat (concat bgb_5_2976 bgb_5_3008) (concat bgb_5_3040 bgb_5_3072))))) (concat (concat (concat (concat (concat bgb_5_3104 bgb_5_3136) (concat bgb_5_3168 bgb_5_3200)) (concat (concat bgb_5_3232 bgb_5_3264) (concat bgb_5_3296 bgb_5_3328))) (concat (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 bgb_5_3456)) (concat (concat bgb_5_3488 bgb_5_3520) (concat bgb_5_3552 bgb_5_3584)))) (concat (concat (concat (concat bgb_5_3616 bgb_5_3648) (concat bgb_5_3680 bgb_5_3712)) (concat (concat bgb_5_3744 bgb_5_3776) (concat bgb_5_3808 bgb_5_3840))) (concat (concat (concat bgb_5_3872 bgb_5_3904) (concat bgb_5_3936 bgb_5_3968)) (concat (concat bgb_5_4000 bgb_5_4032) (concat bgb_5_4064 (concat bgb_5_4096 bgb_5_4128)))))))) (concat (concat (concat (concat (concat (concat (concat bgb_5_4160 bgb_5_4192) (concat bgb_5_4224 bgb_5_4256)) (concat (concat bgb_5_4288 bgb_5_4320) (concat bgb_5_4352 bgb_5_4384))) (concat (concat (concat bgb_5_4416 bgb_5_4448) (concat bgb_5_4480 bgb_5_4512)) (concat (concat bgb_5_4544 bgb_5_4576) (concat bgb_5_4608 bgb_5_4640)))) (concat (concat (concat (concat bgb_5_4672 bgb_5_4704) (concat bgb_5_4736 bgb_5_4768)) (concat (concat bgb_5_4800 bgb_5_4832) (concat bgb_5_4864 bgb_5_4896))) (concat (concat (concat bgb_5_4928 bgb_5_4960) (concat bgb_5_4992 bgb_5_5024)) (concat (concat bgb_5_5056 bgb_5_5088) (concat bgb_5_5120 bgb_5_5152))))) (concat (concat (concat (concat (concat bgb_5_5184 bgb_5_5216) (concat bgb_5_5248 bgb_5_5280)) (concat (concat bgb_5_5312 bgb_5_5344) (concat bgb_5_5376 bgb_5_5408))) (concat (concat (concat bgb_5_5440 bgb_5_5472) (concat bgb_5_5504 bgb_5_5536)) (concat (concat bgb_5_5568 bgb_5_5600) (concat bgb_5_5632 bgb_5_5664)))) (concat (concat (concat (concat bgb_5_5696 bgb_5_5728) (concat bgb_5_5760 bgb_5_5792)) (concat (concat bgb_5_5824 bgb_5_5856) (concat bgb_5_5888 bgb_5_5920))) (concat (concat (concat bgb_5_5952 bgb_5_5984) (concat bgb_5_6016 bgb_5_6048)) (concat (concat bgb_5_6080 bgb_5_6112) (concat bgb_5_6144 (concat bgb_5_6176 bgb_5_6208))))))) (concat (concat (concat (concat (concat (concat bgb_5_6240 bgb_5_6272) (concat bgb_5_6304 bgb_5_6336)) (concat (concat bgb_5_6368 bgb_5_6400) (concat bgb_5_6432 bgb_5_6464))) (concat (concat (concat bgb_5_6496 bgb_5_6528) (concat bgb_5_6560 bgb_5_6592)) (concat (concat bgb_5_6624 bgb_5_6656) (concat bgb_5_6688 bgb_5_6720)))) (concat (concat (concat (concat bgb_5_6752 bgb_5_6784) (concat bgb_5_6816 bgb_5_6848)) (concat (concat bgb_5_6880 bgb_5_6912) (concat bgb_5_6944 bgb_5_6976))) (concat (concat (concat bgb_5_7008 bgb_5_7040) (concat bgb_5_7072 bgb_5_7104)) (concat (concat bgb_5_7136 bgb_5_7168) (concat bgb_5_7200 (concat bgb_5_7232 bgb_5_7264)))))) (concat (concat (concat (concat (concat bgb_5_7296 bgb_5_7328) (concat bgb_5_7360 bgb_5_7392)) (concat (concat bgb_5_7424 bgb_5_7456) (concat bgb_5_7488 bgb_5_7520))) (concat (concat (concat bgb_5_7552 bgb_5_7584) (concat bgb_5_7616 bgb_5_7648)) (concat (concat bgb_5_7680 bgb_5_7712) (concat bgb_5_7744 bgb_5_7776)))) (concat (concat (concat (concat bgb_5_7808 bgb_5_7840) (concat bgb_5_7872 bgb_5_7904)) (concat (concat bgb_5_7936 bgb_5_7968) (concat bgb_5_8000 bgb_5_8032))) (concat (concat (concat bgb_5_8064 bgb_5_8096) (concat bgb_5_8128 bgb_5_8160)) (concat (concat bgb_5_8192 bgb_5_8224) (concat bgb_5_8256 (concat bgb_5_8288 bgb_5_8320)))))))))
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
theorem bgb_6_1792 : Interval gbAtlas 6 1792 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1802 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)) (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792))))))
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
def fullWord : Sig := 0xfeeafeeafeeaeaa8feeafeeafeeaeaa8feeafeeafeeaeaa8feeafeeafeeaeaa8feeafeeafeeaeaa8feeafeeafeeaeaa8feeafeeafeeaeaa8feeafeeafeeaeaa8
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813546 * 2 ^ 32 + 4276808360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12911.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[0,2]⟩,⟨.or,[1,2]⟩,⟨.or,[4,5]⟩,⟨.or,[3,9]⟩,⟨.and,[3,9]⟩,⟨.and,[6,7]⟩,⟨.or,[0,11]⟩,⟨.and,[10,12]⟩,⟨.and,[8,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813546 * 2 ^ 32 + 4276808360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813546 * 2 ^ 32 + 4276808360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12911

open PEqualNP.Outside.L_meta_12911 in
theorem PEqualNP.Outside.L_meta_12911 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813546 * 2 ^ 32 + 4276808360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813546 * 2 ^ 32 + 4276808360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
