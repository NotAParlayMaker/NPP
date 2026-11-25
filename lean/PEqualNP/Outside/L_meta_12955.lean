import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12955.Model
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


end PEqualNP.Outside.L_meta_12955.Model

namespace PEqualNP.Outside.L_meta_12955
open PEqualNP.Outside.L_meta_12955.Model
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

end PEqualNP.Outside.L_meta_12955

namespace PEqualNP.Outside.L_meta_12955
open PEqualNP.Outside.L_meta_12955.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x41fd32083f864107fd4420ff288417e51083faa2105f54420fe28841ff41083fc82107f50420fe20841ff31083fc62107f4c420fe18841ff21083fc42107f48420fe108417e50083fe80107f90020fea0041fc40083fe60107f8c020fe98041fc30083fe40107bc8020ff10041fa20083fa40107b48020fc90041ff54c42fea9887f95310bf2a621fd54c42faa9887f15310be2a621ff53c42fea7887f94f10bf29e21fd53c42faa7887f14f10be29e21ff43c43fc87887f50f10fe21e21ff52c42fea5887f94b10bf29621fd52c42faa5887f14b10be29621ff42c43fc85887f50b10fe21621ff32c43fc65887f4cb10fe19621ff41c43fc83887f50710fe20e21ff31c43fc63887f4c710fe18e21ff21c43fc43887f48710fe10e21ff40c43f681887f90310fea0621fc40c43f081887fcc310ff18621fd30c43f861887fc8310ff10621fd20c43f841887fd5210bfaa421fe54842fca9087f55210beaa421fc54842f8a9087fd4e10bfa9c21fe53842fca7087f54e10bea9c21fc53842f8a7087fd0e10ff21c21fd43843f887087fd4a10bfa9421fe52842fca5087f54a10bea9421fc52842f8a5087fd0a10ff21421fd42843f885087fcca10ff19421fd32843f865085f54610ffa0c21f741843fc83087f50610fe20c21f441843fe63087f8c610fe98c21fc31843fe43087f88610fe90c21fc21842fca1087fd0210ff20421fd40843f881087fcc210ff18421fd30843f861087fc8210ff10421fd20843f841087fc4210fb88421fb10843fea8885fd5110ff2a2217e54443faa8885f55110fe2a2217c54443fea6885fd4d10ff29a217e53443faa6885f54d10fe29a217c53443fe86887f90d10fea1a21fc43443fea4885fd4910ff292217e52443faa4885f54910fe292217c52443fe84887f90910fea1221fc42443fe64887f8c910fe99221fc32443fe82887f90510fea0a21fc41443fe62887f8c510fe98a21fc31443fe42887f88510fe90a21fc21443fe80887f90110fea0221fc40443fe60887f8c110fe98221fc30443fe40887f88110fe90221fc20443fe20887ec4110ff08221f610443fea8085fd5010ff2a0217e54043faa8085f55010fe2a0217c54043fea6085fd4c10ff298217e53043faa6085f54c10fe298217c53043fe86087f90c10fea1821fc43043fea4085fd4810ff290217e52043faa4085f54810fe290217c52043fe84087f90810fea1021fc42043fe64087f8c810fe99021fc32042fca2087fd0410fba0821fe41043fa82087f10410fa20821ff31043fc62087f4c410fe18821ff21043fc42087f48410fe108217e50043fe80087ed0010ff20021fd40043f880087e10010ff98021fe30043fa60087f0c010ff90021fe20043fa40087f08010ff88021f710043fc20087e84010fe88021f510043f220087c44010
  | 1 => 0xf324c3fc64987f4c930ee99261fc324c3fea2985fd4530ff28a61fd514c3f8a2985f14530ffa0a61fe414c3fa82987f10530ff98a61fe314c3fa62987f0c530ff90a61fe214c3fa42987f08530ffa0261fe404c3fa80987f10130ff98261fb304c3fc6098778c130ffaa0617f540c3fca8185f95030feaa0617d540c3f8a8185f15030bf29861ff430c3be86187f90c30fea1861fc430c3b886187fd4830ff290617e520c3dca4185b94830fea90617d520c3daa4185b54830fe29061ff420c3fc84187f50830fe21061ff320c3fc64187f4c830fe19061ff510c3fca2185f94430fea88617d510c3f8a2187fd0430ff20861fd410c3f882187fcc430ff18861fd310c3f862187fc8430ff10861fd210c3f842185f94030ffa0061fe400c3fa80187f10030ff98061df300c3fc60187e8c030fe98061dd300c3f260187fd5320bfaa641fe54c82fca9907f55320beaa641fc54c82f8a9907fd4f20bfa9e41fe53c82fca7907f54f20bea9e41fc53c82f8a7907fd0f20ff21e41fd43c83f887907fd0b20ff21641fd42c83f885907fccb20ff19641ee32c83fa65907b4cb20fe19641ff51c83fca3905f94720fea8e417d51c83f8a3907fd0720ff20e41fd41c83f883907fcc720ff18e41fd31c83f863907fc8720ff10e41fd21c83f843907fd0320ff20641fd40c83f881907fcc320ff18641fd30c83f861907fd5220bfaa441fe54882fca9107f55220beaa441fc54882f8a9107fd4e20bfa9c41fe53882fca7107f54e20bea9c41fc53882f8a7107fd0e20ff21c41fd43883f887105f54a20ffa1441ef42883fc85107f50a20fe21441ec42883fe65107f8ca20fe99441fc32883fea3107f94620bf28c41fd51882faa3107f14620ffa0c41fe41883fa83107f10620ff98c41fe31883fa63107f0c620ff90c41fe21883fa43107f08620bf28441ff40883fc81107f50220fe20441ff30883fc61107f4c220fe18441ff20883de41107ec8220ffaa2417f54483fca8905f95120feaa2417d54483f8a8905f15120ffa9a417f53483fca6905f94d20fea9a417d53483f8a6905f14d20ffa1a41fe43483fa86907f10d20ffa1241fe42483fa84907f10920ff99241fe32483dc64907f4c920f699241fc32483fea2905fd4520ff28a41fd51483f8a2905f14520ffa0a41fe41483fa82907f10520ff98a41fe31483fa62907f0c520ff90a41fe21483fa42907f08520ffa0241fe40483fa80907f10120ff98241fe30483fa60907f0c120ff90241fb20483fc40907b88120ffaa0417f54083fca8105f95020feaa0417d54083f8a8105f15020ffa98417f53083fca6105f94c20ef298415e53083faa6105f54c20eea98415d53083f8a6105f14c20ffa1841fe43083fa86107f10c20bf29041ff42083de84107f90820fea1041fc42083d884107fcc820ff19
  | 2 => 0x3f865a07fd4740ff28e817e51d03faa3a05f54740fe28e81ff41d03fc83a07f50740fe20e81ff31d03fc63a07f4c740fe18e81ff21d03fc43a07f48740fe10e817d54903fea7207f94e40bf29c81fd53902faa7207f14e40ffa1c81fe43903fa87207f10e40ffa9481fe52902fca5207f54a40bea9481fc52903fe85207f90a40fea1481fc42903fe65207f8ca40fe99481fc32903fea3207f94640bf28c81fd51902faa3207f14640ffa0c81fe41903fa83207f10640ff98c81fe31903fa63207f0c640ff90c81fe21903fa43207f08640bf28481ff409037e81207ed0240ffa9a817f53503bea6a057d4d40ff29a81fd53503f8a6a05f14d40ee29a815c53503fe86a07f90d40fea1a81fc43503fea4a05fd4940f7a92816f52503fca4a07f54940fe292817c52503d8a4a05b14940ffa1281fe42503fa84a07f10940ff99281fe32503fa64a07f0c940ffa8a817f51503eea2a05dd4540ff28a81fd51503f8a2a05f14540fa28a817451503fe82a07f90540fea0a81fc41503fe62a07f8c540fe98a81fc31503fe42a07f88540fe90a81fc21503fe80a07ed0140ff20281be40502fca8207fd4c40ff298817e53103faa6205f54c40fe29881ff43103fc86207f50c40fe21881ff52103fca4205f94840fea90817d52103f8a4207fd0840ff21081fd42103f884207fcc840ff19081fd32103f864207fd4440ff288817e51103faa2205f54440fe28881ff41103fc82207f50440fe20881ff31103fc62207f4c440fe18881ff21103fc42207f48440fe108817e50103fe80206fd0040ff20081fa40103fa80206f50040fca0081ff54cc2fea9987f95330bf2a661fd54cc2faa9987f15330be2a661ff43cc3fc87987f50f30fe21e61ff52cc3fca5985f94b30fea96617d52cc3f8a5987fd0b30ff21661fd42cc3f885987fccb30ef99661fe32cc3fa6598774cb30fe19661ff51cc3fca3985f94730fea8e617d51cc3f8a3987fd0730ff20e61fd41cc3f883987fcc730ff18e61fd31cc3f863987fc8730ff10e61fd21cc3f843987fd0330ff20661fd40cc3f881987fd5230bfaa461fe548c2fca9187f55230beaa461fc548c2f8a9185f54e30ffa1c61df438c3fc87187f50e30fe21c61dc438c3fea5187f94a30bf29461fd528c2faa5187f14a30ffa1461fe428c3fa85187f10a30ff99461fe328c3fa65187f0ca30ffa8c61fe518c2fca3187f54630bea8c61fc518c3fe83187f90630fea0c61fc418c3fe63187f8c630fe98c61fc318c3fe43187f88630fe90c61fc218c2fca1187fd0230ff20461fd408c3f881187fcc230ef98461fb308c3fea8985fd5130ff2a2617e544c3faa8985f55130fe2a2617c544c3fe86987f90d30fea1a61fc434c3fea4985fd4930ff29261fd524c3f8a4985f14930ffa1261fe424c3fa84987f10930ff99261d
  | 3 => 0x8698ff10d31ffa92637f524c7fca498ff54931fe292637c524c7fe8498ff90931fea1263fc424c7fe6498f7cc931ff19263fd324c7ba6498ff0c931ffa0a63fe414c7fa8298ff10531ff98a63f7314c7fc6298f78c531ffa82637f504c7fca098ff54131fe282637c504c7fea818dfd5031ff2a0637e540c7faa818df55031fe2a0637c540c6fca618ffd0c31efa1863fe430c7fa8618ff10c31ee21863ff520c7fca418df94831f7290636e520c7faa418df54831f6a90636d520c7f8a418ffd0831ff21063fd420c7f88418ffcc831ff19063fd320c7f86418df94431ffa0863fe410c7fa8218ff10431ff98863df310c7fc6218fd8c431fe98863dd310c7ea6218ffd4031ff280637e500c7faa018df54031fe28063ff54c86fea990ff95321bf2a643fd54c86faa990ff15321be2a643ff53c86fea790ff94f21bf29e43fd53c86faa790ff14f21be29e43ff43c87fc8790ff50f21fe21e43ff42c87fc8590ff50b21fe21643ff32c87fc6590fb8cb21fe99643ed32c87f86590ffd0721ff20e43fd41c87f88390ffcc721ff18e43fd31c87f86390ffd4321ff286437e50c87faa190df54321fe28643ff54886fea910ff95221bf2a443fd54886faa910ff15221be2a443ff53886fea710ff94e21bf29c43fd53886faa710ff14e21be29c43ff43887fc8710ff50e21fe21c437d52887fe8510fbd0a21ff21443fd42887f88510fb10a21ff99443fe32887fa6510ff0ca21bf28c43ff41887fc8310ff50621fe20c43ff31887fc6310ff4c621fe18c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fea690dfd4d21ff29a437e53487faa690df54d21fe29a437c53487fe8690ff90d21fea1a43fc43487fe8490ff90921fea1243fc42487fe6490ff8c921f719243fd32487da6490ff0c921ffa0a43fe41487fa8290ff10521ff98a43fe31487fa6290ff0c521ff90a43f721487fc4290fb88521ffa82437f50487fca090ff54121fe282437c50487fea810dfd5021ff2a0437e54087faa810df55021fe2a0437c54087fea610dfd4c21ff298437e53087bca610d794c21fea98437d53087baa610d754c21fe298437c53087fe8610ff90c21fea1843fc43086fca410ffd0821f7a1043fe42087fa8410ff10821f621043ff32087fc6410ff4c821fe190437e51087fe8210ff90421fea0843fc41087fe6210ff8c421fe98843fc31087fe4210fbc8421ff10843f621087fa4210fb48421fa90843ff50087fca010df94021fea80437d50087f8a010ffd4f40ff29e817e53d03faa7a05f54f40fe29e81ff43d03fc87a07f50f40fe21e81ff52d03fca5a05f94b40fea96817d52d03f8a5a07fd0b40ff21681fd42d03f885a07fccb40ff19681fd32d
  | 4 => 0x7f10d32ee21a65ff424cbde84997f90932fea1265fc424cbd884997fcc932f799265fe324cbbc64997fd4532bfa8a65fe514cbfaa2997f14532be28a65ff504cafea0997f94132fea8265fc504caf8a0997fd5032bfaa065fe540cafca8197f55032beaa065fc540caf8a8195f94c32ffa1865fe430cbfa86197f10c32bf29065ff420cbfc84197f50832fe21065ff320cbbe64197f8c832f719065fd320cbba64197b4c832e699065ff510cbfca2195f94432fea88657d510cbf8a2197fd4032ff280657e500cbfaa0195f54032fe28065ff53d07fca7a0df94f41fea9e837d53d07f8a7a0ffd0f41ff21e83fd43d07f887a0ffd4b41ff296837e52d07faa5a0df54b41fe29683ff42d07fc85a0ff50b41fe21683ff32d07fc65a0ff4cb41fe19683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9c83fe53906fca720ff54e41bea9c83fc53907fe8720ff90e41fea1c83fc43907fea520ff94a41bf29483fd52906faa520ff14a41ffa1483fe42907fa8520ff10a41ff99483fe32907fa6520ff0ca41bf28c83ff419077e8320fdd0641ffa8483fe50906fca120ff54241bea8483fc50907fea6a0dfd4d41efa9a835f53507fca6a0ff54d41fe29a837c53507b8a6a0d714d41ffa1a83fe43507fa86a0ff10d41ffa92837f52507dea4a0dbd4941ff29283fd52507f8a4a0df14941f6292836c52507fe84a0ff90941fea1283fc42507fe64a0ff8c941fe99283fc32507fe82a0fdd0541ff20a83be41507fea0a0dfd4141fda82837b50507fca0a0ff54141fe282837c50507f0a0a0de14141bf2a083ff53107fca620df94c41fea98837d53107f8a620ffd0c41ff21883fd43107f88620ffd4841ff290837e52107faa420df54841fe29083ff42107fc8420ff50841fe21083ff32107fc6420ff4c841fe190837e51107fe8220efd0441ff20883f641107fa8220ef50441faa0883ff50107fca020df94041fea80837d50107f8a020ffd5331bfaa663fe54cc6fca998ff55331beaa663fc54cc6f8a998ffd0f31ff21e63fd43cc7f88798ffd4b31ff296637e52cc7faa598df54b31fe29663ff42cc7fc8598ff50b31fe21663ff32cc7be6598ff8cb31fe99663dd32cc7f86598ffd0731ff20e63fd41cc7f88398ffd4331ff286637e50cc7faa198df54331fe28663ff548c6fea918ff95231bf2a463fd548c6faa918ff15231be2a4637d538c7fe8718f7d0e31ff21c63fd438c7f88718f710e31ffa9463fe528c6fca518ff54a31bea9463fc528c7fe8518ff90a31fea1463fc428c7fe6518ff8ca31fe99463fc328c6fca318ffd0631ff20c63fd418c7f88318ffcc631ef98c63f7318c7fea118ff94231bf28463fd508c6faa118ff14231ffaa2637f544c7fca898df95131feaa2637d544c7f8a898df15131ffa1a63fe434c7fa
  | 5 => 0x2c00c00800001000801006406c00000005801c00000c00000001c00c05c00c00c02000800400000000000c00000000800000000000400000400c03000400004001002c018038000038014003fea5a1ff94b43bf29687fd52d0efaa5a1ff14b43ffa8e87fe51d0efca3a1ff54743bea8e87fc51d0ffea1a1ff94343bf28687fd50d0efaa1a1ff14343beaa4877e5390ffe8721efd0e43efa1c87ff5290ffca521df94a43f7294876e5290ffaa521df54a43f6a94876d5290ff8a521ffd4643ff28c877e5190ffaa321df54643fe28c87ff5090ffca121df94243fea84877d5090ff8a121ffd0d43efa1a87fe4350f7c86a1ffd4943bfa9287fe5250ffaa4a1ff14943be29287ff5150efea2a1ff94543fea8a87fc5150ef8a2a1ffd4143bfa8287fe5050ffaa0a1ff14143be282877e5410efca621ffd0c43dfa1887fe4310fbc8621ff50c43dea1887dd4310ffea421ff94843bf29087fd5210efaa421ff14843ffa8887fe5110efca221ff54443bea8887fc5110ffea021ff94043bf28087fd5010efaa021ff14043ffa9e85fe53d0afca7a17f54f42bea9e85fc53d0bfe87a17f90f42fea1e85fc43d0bfea3a17f94742bf28e85fd51d0afaa3a17f14742ffa8685fe50d0afca1a17f54342bea8685fc50d0afaa9217fd4e42ff29c857e5390bbca7215794e42fea9c857d5390bbaa7215754e42fe29c85ff4390bfc87217f50e42fe21c857e5290bfe85216fd0a42f7a1485ff5190bfca3215f94642fea8c857d5190bf8a3217fd4242ff284857e5090bfaa1215f54242fe28485ff5350afea6a17f94d42fea9a85fc5350af8a6a17fd0d42ff21a85fd4350bf886a17fd0942f7a1285fe4250b7c84a17fd4542bfa8a85fe5150bfaa2a17f14542be28a85ff5050afea0a17f94142fea8285fc5050af8a0a15f95042ffa9885fe5310afca6217f54c42bea9885fc5310bfe86217f90c42fea1885fc4310afca4217fd0842dfa1085fe4210bdc84217f50842dea1085ed4210bfea2217f94442bf28885fd5110afaa2217f14442ffa8085fe5010afca0217f54042bea8085fc5010bfea9995fd5332ff2a6657e54ccbfaa9995f55332fe2a6657c54ccbfe879977d0f32ff21e65fd43ccbf887997710f32ffa1665fe42ccbfa85997f10b32ffa8e65fe51ccafca3997f54732bea8e65fc51ccbfea1997f94332bf28665fd50ccafaa1997f14332ffaa4657f548cbfca9195f95232feaa4657d548cbf8a9195f15232bea9c65ff438cbfc87197f50e32fe21c657e528cbfe85197bd0a32ff21465fd428cbf885197b10a32ff99465df328cbde65197fd4632ff28c657e518cbfaa3195f54632fe28c65ff508cbfca1195f94232fea84657d508cbf8a1197fd5132bfaa265fe544cafca8997f55132beaa265fc544caf8a8997fd0d32efa1a65fe434cbfa8699
  | 6 => 0x4907da2c00027e8fb1452998002720b400008aaf89128002a2196b3031f93ca9c8a1a7280008704eb3d17914606a19100025c0cea3e0dba331549290a2b2100228e00029700f00007f800170a97aab294b010d20198002e5b53a47a259ecab5216100b6700031180004e13125d829000331334a280001dab63a4811e8003321b69b91aa8bc34880026aa2a8000000002e0aaab7d20eab60000002142e18da14e9e501c8f62a81ccae10000001888000788001939ae0f39cd9330002d72a1800000000000219000000001002000800401400003000c00801800003800401400002800c00c01c0a800400001008c01003800001c00c00400000800002800000400003401c00000800000c00400c00000800401408801800001801002400c02400c01000008400000c00c00c0040500040000c402c00402000803800806400001004002800400001800c00400802402002001400000c00c04804801402402000400800000c00405000400802c02001801000c05c07803800000001000800000000001005402000c01000800000002000401c00001400c00401800000003005c02c01401c02400c00801400000001000401804c00400000002804000c00001801002800400402000400400800000004800801000000c01800800401000000403003c00400400400000400400000400000c0000040080280000240000bc00000c03c00400c00c01802000005c02800000005c0100f800000000001402800000801c00800c00005000400001000002000000000c01401c02000000000802802c0340200100040000440000040c400003000000006001c00007000009c00400800408c00006000400003804401002400400800002802c02c00c00000c00000400801000000001400001000000c00012403006002802001800000801401c05800400803805400403000401401401401000000400800803c01000402000803001002c00800803002000c00804801401407400800401403c00000800000001c01400001401800000000000400006000c02409000000400c05003400402404c00004401000c01001403c06800000400400c02402000000001002400c0000000080740240000000100240080000080400280280380000000000040580000dc00000401800000001001800400002001406400000c00400000402400801c00000002000401004000800008002c00404c01803800403c00000402c00001000000000000000800c00c00001400801800000000000000800401803401000000802002402401001000006400802401000004400000800001c00000000000400004c05000001c01400000c02002400c00000000400000400400800002c00401800000000000c00403400001000012401c00803400000806404005800801400000005c00004000c0000
  | 7 => 0x158000000000002d2986b201f580000027fa68959a7b8000001d527f2ed81b82c14fa66a9e087a6100023428e80014f0002bc3631bd06780019f2dfad921780290116c9c40e1b2ea962d693229f8e4180866082a20906045b229c51770fd843901a3c34434505e9fea692862e2af784d1e3a7a8eb81130a2abb3a89f08c0b224f95e8003501080002f800000000025a93a9fa8a01ea80006c15bb08af225781817a9dc1b79c19af2b59e18c285c14c9fb185263b7f2a98160ea8618df21b23c8f5182a673720002b68331078b2af300013b0002068000002de0000001f00a9b658d9add8000000948001651d1000125a199af9e117e80000f8d61c215a913b1397e000340117aaf0e8000000001a9da920000000ab800000000125023b291500a69340000001582d31cf896ab3ab29440499339b49b20001f48739fe33e8539bc02d37fa64a56b23b1b85f2459cba8b19fb810002719d637326fa0b2f725704b29a81f12c800109800000000000202abb00400000022f00000030e2838002bbadb80032d8038c390203786211f2fa9849761900cc9ee00000000006a8808002ee88d9a619e80000011212714b00030fa00ab02ce9088003448d580034c06d8a38d40798000000aa0000c20000f68002c800016734599900028834a09b80000037da238002e30000f10c98d71a880012635690582a1b18228000002e000000000016980016016ba80832aea88800028ca8591ba628a235200035f9308a11161cb281a81381800000222b6782bafb8aa97181680000000000020c8eeb5629b2acaa601422a2de85f8000000afb0d2038f0213000245355b180518e00dd08a123a0501e000328893238b542339e21b51de9ebb0b86989fb18b1d08327c0732a4291b0f00011c1bf0af0a0b1308ba0b8002fc80a2c00f7220138ab09f80c306b918b6d2e8153aa3a8785236f000000000000253b1c8482968001192df00016a21ab140002902ad07e8000001be93e800364800000000000193000377aa58001a680c0003680000edb3cb5884a00017c80019423831d8000f31d6813ae713a0000b49468fea5fb788002468cfb5934da51aaa26d95d80036914bb6ea3a8fa00006037413531f0000312cf0209490002588f59de0088b11522cca5800000015f00037732830ab759f0999b17a2bac8b109d72591c08dd90e9e28001972ca28f8dc1ab80034a8002221659df800173acf8000002410000ba83180025b8d2a1f0e3152828800119891b220002158b024283d0000000000001a1b668fb800365071b481dd2890000488000000d698a0d79210001c92ee0000f21bf9b9a9882a8000000001a288109e22e8000ad92c36a9f793f98110b87a2d889225f0000001b29170001d388880000028da8f14892b0723708000000002ad8682cc1b61b318ba46135add
  | 8 => 0xd300000004d979800000158b12123262380a402f6b380003148001cf0000369a50000550cd000000000240a048b99a98ba03416e1f71431861841f980008229ea928000000001ef9ec2522f499a30c10f84a8002fa2bc8000b5252ab401ea73b3b1c81f11c898f2d83020b60418003581fc357af00000001a928a8be0fe00017880009b14380022da86af400000016e897aa687700600017b8e5a39335a4a819074b248ee00024912d04413c3510e7278a5993b96d18f88580023982d97f8000cf12a0bd0000c0aeb8b080000000010680000030e80000015e15725105ab5b3601f8a2680017a316000243a1c1e82b9833b5a9ceb611c00a431291d02b006b4d06c8d836e0002850000001141820ce0000001ab0003168960e2b32b39a84ad20a89ffa1032710c80d0001b586e31c08e1e93752e62af8003411240000000000000000001950000000000000cb000000097306ad78001d89b73531b380021d9540002872061aa07400c83825b16810c050b2d0003660ad0000000000988002d52d008b19c1029d780037190d36b80000003f2770951a701706b2dc35e80010f14700035db1ea7d8002c78c0000290b5f1048000eca5e00005b03a36c00000026b33ba7500036080000026080005e000187a430000001201948000a7b700e12761ed1ca932b0400028281a1c61208240569fc95c8853278001298ef2c499b23eaf09fa31727100ea020002262e22f50ed0560da8002da940b21aca922a5d0000002f10000b708d00000000007b1da2002183432b7ad1030b02a7837295d18ca0f2bd953180044abe3008001c6a8a16797d8158e600014d94000d8000048000000001b800017c1920c600000000000000000000000000016c17300000025000016080036b1f318c0ff9e080031532500aa5eac58f085d9d903c98900000009104f8ae2a4b2cb5980010a9e5a44aa03208450000000fc91f8000710002889f900000004332b0000000002fd9151348001bd8002c40000002550000940000db03495503500021a0a4a0323580000017437c3762019422b721b80009d90b276847a6a0003498000e4ae412819187d038af1af297d2e89bb3071d48a63428d925a10318e33a0f8b0c89800032f0d114a8000002759b8a4737c83fb1a92b8992249038758002ae283141116ace00000001b2b823d87504b8000000ab0000ff1288b382fb5183a95584c80019883c18d1c48000d8a708e520da800000001c3026277a2500013e0ac8659ad0001e31c5b19a5cb0b2ec0000000000001e6a0a8ea000093a8c0002ea2c9921a0f98a91cb298000001e795f8a30002c6350b5c095a4417216d85bb5b8000901b40283090e9a0e09d1d195a1a300033c33e0250fc0118002650001f183707cae487000030380019db6f81d27000037ab26303021b04800054b
  | 9 => 0x2cd8bb00013180019580000000000000000032b800000000000000000197b6200000012e998077aac2618cc00980000035d2e99c9835a8422b1bc8bf87e02100036a10e34b02f2d58002289713368001ba9070000000d48908000278001378002ef35e1b098583e000000000214870aa32d08000000001102509a805c8b7a7cb7988000b15094182c8002112ff2d38002558002320001248c40000c6ae92c3099a32ada2c288f9041ea08c80027d1a000020418d8e207606fa37af9886a082bab3929312d86724c32e0d180024e97b21fa091f380129c1ef12e3828ec2ef8000c880019e218800000000000083b418000000130f980019b80006d2278000790000000530408c595c16f3268ca1f280026e94e1222d180026c118063a95295a0a0001ad8002b1a2f9d20001ddaba13d8083018f837e0001752a88000000bf00332a80003b0003100002108001c399c963b3400000028985d174b82189800054023192a6603998816b24baa911e2422c38f48bb80bb0521223f8002c68f4000368ad48000598b93438002cb00037380000000023080005280000000000022100029b80000016409c1ca0c1964a540609ff181b7ba1c8002d99c78cbafe8001f507bb6c81d80000010a012b420001b02370000000e3800338a4d8578a503e81224e1481688faa6b8002349aeacbb1a1390eb2982f935c86411aab1254a640c50f79fb9610d01768421963190aea098002c1b3fabf2db0000001f413f11b18705103b807000000081a8d11d9562a5346127b492f38001be02591480023f16905a16ab4c95b0222990090b829107822e0efb4712a8dea4f0d0b7832c1ac22434f3230c717f17596f911032111b571dc81894c2c71eb1ba0001c72530ac30780024b09c80018b0648000610001369bbae38000001ac9d0846a368628c928b87c00020d0001728002630c10002ed2a104603622d0000e780010d92f00000031e352b6d80009aa08892a9a26590012f8412b880013713037a2a0a31a078000000729d5a3a0001a1157ac50000000fd00024d37480010921711a0002292299a200000000000000029380000000008409a0000b58000588000002c20001fd0769448002682f5a67a1500020100027b0000002f600001f80033f212ae7a9f2119909830d380030813d34f8000100002793098000000000c78581362a734ba1e126b000650a80558270268f18f90b698380014d2ae9db147a3b2230202740631d00beb7e9a7affa821eea2cb5a346abf800000274a3b945b062e68109d82bd1619703478b196680010500000027a005a360429c10000000000000000000003408c80000000002a2800249a16a6d20c0000001db8a5b1b2fd2b90a726cb36066b05a070078848cd8de24a0001a40e880005900011587a8bd8dc9fd9d30000df80000000032400
  | 10 => 0x891a4afe2b487f1660000a9029800230068ac08862139e4ac90ca8150001630001a58000148000001f60000002ec80027337682eab20001e880013805000000000019d03d800a941d419ab372b32dcb0d80034e8001e9a6f1df2fb0003640898001e023129d22725627e02e2e532594285737b221b351f6977a698400e908f2beb2f8178691f200032a248b61a352798bcaa78e084f0000003710001a3a4cb7913986f18eb69b378f282484701c15133d8c49cc00e1ce1d2b30959113151b33a6e16221ead63318d51e61780e6a3d04c2d401a910962a6008e86e9cd0390b30000000b89e70002eb38034e1d98001e40002fc0001a0a1d156b550001c280009e800311149b62a058003331ed8052418303549b114a0000000002c12cd
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x31042f9600c4109f597210427f65884109f596210436e5288410db54a21042fa6088410be582210427f65484109fd94210427d6508410b798c21042dd6308410db948210436d5208410f948421042fa6008410be580210427e64940109f592500427e63940109f58e500427e62940109f58a500427d6194010ddd06500437441940109f59740042f965d0010de597400437b54d0010de55340043f361d0010be58740043f061d0010de94740043f341d0010fc107400427f65900109f596400433e5490010cf55240042f66190010bd58640042fa60900109fd9540042df6350010b718d40042ef6250010bb18940042f76150010bd185400427f65100109f994400427d65100109f194400433e5410010cf55040042f66110010bd58440042f96510010de59440042796510010be99040043ba6410010ded5040043ba5410010de55040043b95410010ce55040043f26110010be58440043f16110010bc584400437a5110010fcd0440043f041100109f597300427f658c0109f596300435e538c010d754e30042f6618c010bd586300427f654c0109fd94300427e650c0109f594300427c650c010d794c300435d530c010bb98830042ed620c010bd98430042f5610c010f64c0300427d65c80109fd96200427d6588010db94a200436d5288010bd98620042f561880109fd95200427f65080109f994200427d65080109f19420042de6308010b758c200436e5208010db54820042f66108010bd58420043e92008010dd59710042f664c4010bd19310043f340c4010fc10310042f56184010dd94610042f96584010de59610042796584010be99210042f86484010be58610042f16184010de94610043f25184010fcd0610043f041840109fd9510042f76544010ddd9510042776544010bd99110042f46444010bdd8110043765044010fcd0110043f24044010fc50110043f04044010fccc110043f23044010fc4c110043f03044010fcc8110043f22044010fc48110043f02044010bed95100437b65440109ed9510042fa6444010be19110042fb6144010fcd85100437a5144010fc94510043f34144010fc90510043f14144010fc10510043f33144010fc8c510043f13144010fc0c510043f32144010fc88510043f12144010fc08510043f36544010bcd9510043736544010fcd9110043f26444010bc99110043f16444010fc19110042f06444010fcd5110043f25444010fc55110043f05444010fcd8d10043f26344010fc58d10043f06344010fcd4d10043f25344010fc54d10043f05344010fcd0d10043f24344010fc50d10043f04344010fcd8910043f26244010fc58910043f06244010fcd4910043f25244010fc54910043f05244010fcd0910043f24244010fc50910043f04244010fccc910043f23244010fc4c910043f03244010
  | 1 => 0x427e65d0c109f597430427c65d0c10cf953430433d54d0c10d7d4f430435c53d0c109fd96430427e6590c109f596430427c6590c10d794e430435d5390c10bb98a43042ed6290c10bd98643042f56190c10be98243042f96090c109fd95430427e6550c109f595430427c6550c10cf951430433d5450c10d794d430435d5350c10bdd8543042f46150c10bed8143042f86050c109fd94430427e6510c109f594430427c6510c10d7d4c430435c5310c109f993520427d64d48109f98f520427d63d48109f987520437661d48109f983520437a60d48109f596520436f52948109f992520427d64948109f98e520427d63948109fd91520427c64548109fd8d520427c6354810dbd89520427f61548109f585520427f60548109f58152042be6414810af59052042de6314810b758c520436d52148109f990520433e64148108f990520427d6414810cf590520423d64148109f98c520435e63148109798c520427d6314810d758c520425d63148109f988520436e62148109f984520437661148109f980520437a60148109fd97420427e65d08109f597420427c65d0810cf953420433d54d0810dbd4b420436c52d08109fd96420427e65908109f596420427c6590810b798e42042dd6390810db94a420436d5290810bd98642042f56190810be98242042f960908109fd95420427e65508109f595420427c6550810cf951420433d5450810db949420436d5250810bdd8542042f46150810bed8142042f860508109fd94420427e65108109f594420427c6510810dbd48420436c52108109fd97320427e65cc8109f597320427c65cc810d794f320435d53cc8109fd96320427e658c8109f596320427c658c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810d794d320435d534c810db949320436d524c810bdd8532042f4614c810bed8132042f8604c8109fd94320427e650c8109f594320427c650c810f34c832042f6610c810bd58432042fa600c810be580320427e64944109f592510427e63944109f58e510427e62944109f58a510427d65d0410bd597410437565d0410ddd53410437554d0410fcd8341042f560d0410fc183410427f65904109f596410433e5490410cf55241042f66190410be98241042f960904109fd9541042df6350410b718d41042ef6250410bb18941042fb60504109fd94410427d6510410cf950410433d5410410be98041042f96010410dd59441042756510410bd99041043b66410410ddd5041043b65410410dd55041043b55410410cd55041043f26010410bd58041043f16010410bc580410427d65cc4109fd96310427d658c410d794e310435d538c410be98231042f9608c4109fd95310427f650c4109f594310435e530c410d754c31042ee620c410bb58831043d5310c410be98
  | 2 => 0x650c9109f594324427c650c910d7d4c324435c530c910dbd48324436c520c910f34c8324427e65d0510cfd53414433c54d0510be98341442f960d05109f996414427c6550510cfd51414433c5450510b7d8d41442dc6350510bbd8941442ec6250510bed8141442f860505109f99441443b541105109f997314435f53cc510d714f31442fa60cc510be583314427e658c5109f195314435f534c510d714d31442fb604c510be181314427e650c510bb98831442ed620c5109f997214436f52c8510db14b21442fa60c8510be583214427e65885109f195214436f5248510db14921442fb6048510be181214427e6508510b798c21442dd63085109f997404433f54d0110cf15340442f661d0110bd587404427e65901109fd95404427d65501109f195404433f5450110cf15140442df6350110b718d40442ef6250110bb18940442f76150110bd185404427e6510110ee500404427e65cc110d7d4f304435c53cc110bd98730442f561cc1109f996304427f654c1109f595304427c654c110d7d4d304435c534c110bdd8530442f4614c1109f99430442ee620c110bb588304427e65c8110dbd4b204436c52c8110bd98720442f561c81109f996204427f65481109f595204427c6548110dbd49204436c5248110bdd8520442f461481109f99420442de6308110b758c204437a54c4110de15310443765484110dd15210443f350841109f98f540427d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d6295010b7d8d54042dc6355010bbd8954042ec6255010cfd91540427f6355010d7d8d540425f63550109f18d540435c63550109718d540427f6255010dbd89540426f62550109f189540436c62550109b189540427f61550109f585540437461550109fd81540427d6055010de181540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150109f98c540435e63150109798c540427d6315010d758c540425d63150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109f980540437a60150109f993530427d64d4c109f98b530427d62d4c109f987530437661d4c109f983530437a60d4c109f596530435f5394c109f992530427d6494c109f98a530427d6294c109fd91530427c6454c10d7d8d530427f6254c109f189530427f6154c109f585530427f6054c109f58153042be6414c10af590530435d5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f98c530435e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109f980530437a6014c109fd97430
  | 3 => 0x1109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427761551109fd81544437b60551109ed81544427e6515110cf550544433e64151109f98c544427d63151109f988544427d62151109f984544427c61151109f980544427c60151109f993534427d64d4d109f98b534427d62d4d10d7d4e534427e6494d109f592534427e6394d109f98a534427d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10bbd8953442ec6254d109fd91534433f6454d108fd91534427c6454d10cf191534423c6454d10d7d8d534427f6254d10dbd89534426f6254d109f189534436c6254d109b189534427f6154d10ddd85534427f6054d10ded81534427e6514d10d754c53442ee6214d10bb588534427e6414d109f590534435e6314d109f988534436e6214d109b988534427d6214d10db588534426d6214d109f984534427c6114d109f980534427c6014d109fd97434427e65d0d109f597434427c65d0d10d7d4f434435c53d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d10bb98a43442ed6290d109fd95434427e6550d109f595434427c6550d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10d7d4c434435c5310d10bd98443442f56110d10be98043442f96010d109f993524427d64d49109f98f524427d63d4910dbd4a524427e64949109f592524427e63949109f58e524427e62949109f586524437561949109f58252443796094910afd9152442bc6454910b7d8d52442dc63549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910b798c52442dd6314910db548524427e64149109f590524427e6314910d798c524425e63149109f58c524435d63149109758c524436e62149109f984524427c61149109f980524427c60149109fd97424427e65d09109f597424427c65d0910dbd4b424436c52d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910b798e42442dd63909109fd95424427e65509109f595424427c65509109fd94424427e65109109f594424427c6510910cfd50424433c5410910dbd48424436c5210910bd98442442f56110910be98042442f960109109fd97324427e65cc9109f597324427c65cc910d794f324435d53cc910dbd4b324436c52cc9109fd96324427e658c9109f596324427c658c910d7d4e324435c538c910db94a324436d528c9109fd95324427e654c9109f595324427c654c910d794d324435d534c910db949324436d524c9109fd94324427e
  | 4 => 0xd98643842f56190e109fd95438427e6550e109f595438427c6550e10bdd8543842f46150e109fd94438427e6510e109f594438427c6510e10d794c438435d5310e10be98043842f96010e109f993528427d64d4a109f98f528427d63d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528427f6454a109f191528427f6354a109f18d528436f6254a10b798c52842dd6314a10db548528427e6414a109f590528427e6314a10d798c528425e6314a109f58c528435d6314a109758c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10db94b428436d52d0a109fd96428427e6590a109f596428427c6590a10b798e42842dd6390a10bd98642842f56190a109fd95428427e6550a109f595428427c6550a10bdd8542842f46150a109fd94428427e6510a109f594428427c6510a10db948428436d5210a10be98042842f96010a109fd97328427e65cca109f597328427c65cca10d794f328435d53cca109fd96328427e658ca109f596328427c658ca10db94a328436d528ca109fd95328427e654ca109f595328427c654ca10d794d328435d534ca10db949328436d524ca10bdd8532842f4614ca109fd94328427e650ca109f594328427c650ca10f34c832842f6610ca10bd584328433e54d0610cf55341842fa60d0610be583418437565d0610ddd5341843b654d0610dd55341843b554d0610fc98341842f560d0610fc583418433e5450610cf55141842df6350610b718d41842ef6250610bb18941842fb6050610be18141842f56510610dd59441843b66410610ddd5041843755410610bd580418435e53cc610d754f31842fa60cc610be583318435e534c610d754d31842fb604c610be18131842ee620c610bb58831843d5310c610db94b218436d52c8610be98321842f960c8610db949218436d5248610bed8121842f86048610b798c21842dd6308610f9484218433e5490210cf55240842f66190210bd58640842df6350210b718d40842ef6250210bb18940842f76150210bd185408433e5410210cf55040842f66110210bd58440843b94010210d794e308435d538c210bd98630842f5618c210d794c308435d530c210bb98830842ed620c210bd98430842f5610c210db94a208436d5288210bd98620842f56188210b798c20842dd6308210db948208436d5208210bd98420842f56108210bd597108437565c4210bd99310842f464c4210be597108437965c4210de953108437854c42109f98f544427d63d51109f98b544427d62d5110cfd52544427e64951109f98e544427d63951109f98a544427d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f6355
  | 5 => 0x42c436e52d0b10db54b42c427f6590b109f99642c427d6590b109f19642c42de6390b10b758e42c42fa6090b10be58242c427f6550b109f99542c427d6550b109f19542c42fb6050b10be18142c427f6510b109f99442c427d6510b109f19442c436e5210b10db54842c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c435e53ccb10d754f32c427f658cb109f99632c427d658cb109f19632c436e528cb10db54a32c427f654cb109f99532c427d654cb109f19532c435e534cb10d754d32c436e524cb10db54932c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c43cd320cb10be98032c42f9600cb10cf95241c433d5490710be98241c42f96090710b7d8d41c42dc6350710bbd8941c42ec6250710be18141c433e5410710cf55041c43b54110710be98041c42f96010710d794e31c435d538c710be98231c42f9608c710d794c31c435d530c710bb98831c42ed620c710be98031c42f9600c710db94a21c436d5288710be98221c42f96088710b798c21c42dd6308710db94821c436d5208710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310be59740c437965d0310ded5340c43ba54d0310de55340c43b954d0310fc98740c42f961d0310fc58740c433e5450310cf55140c42df6350310b718d40c42ef6250310bb18940c42f76150310bd18540c42f96510310de59440c43ba6410310ded5040c43795410310be58440c435e53cc310d754f30c42f661cc310bd58730c435e534c310d754d30c42f7614c310bd18530c42ee620c310bb58830c43d9300c310db94b20c436d52c8310bd98720c42f561c8310db94920c436d5248310bdd8520c42f46148310b798c20c42dd6308310fa48020c42de63d5210b758f54842ee62d5210bb58b548427e63d5210d798f548425e63d52109f58f548435d63d52109758f548427e62d5210db98b548426e62d52109f58b548436d62d52109b58b548437561d5210de983548433f54952109f98e548427d63952109f98a548427d6295210cfd91548427f63552109f18d548427f62552109f18954843776155210cf550548433e64152109f98c548427d63152109f988548427d6215210dd584548437a60152109f993538427d64d4e109f98b538427d62d4e10dd587538437a60d4e10d7d4e538427e6494e109f592538427e6294e109f58a538427f6454e109f191538435f6354e109fd89538427c6254e10d754c53842ee6214e10bb588538427e6414e109f590538435e6314e109f988538436e6214e109b988538427d6214e10db588538426d6214e10dd584538437a6014e109fd97438427e65d0e109f597438427c65d0e10d794f438435d53d0e109fd96438427e6590e109f596438427c6590e10bb98a43842ed6290e10b
  | 6 => 0x2f461500209fd94400827e65100209f594400827c6510020cf950400833d5410020d794c400835d5310020bb98840082ed6210020ee500400827d65cc020d794f300835d53cc0209fd96300827d658c020d794e300835d538c020bb98a30082ed628c0209fd95300835e534c020d754d300827f650c0209f994300827d650c0209f194300835e530c020d754c30082ee620c020bb58830083d9300c020d794f200835d53c8020bb99320082ec64c8020dbd4f20083ce53c8020db54f20083cd53c8020d354f200835e5388020d754e20082ed6288020db94a20083da5388020f654e20082f96288020de94a20083ea5288020fad0a20083e842880209fd95200835e5348020d754d20082ef6548020dbd95200826f6548020bb99120082ec6448020dbd4d20083ce5348020db54d20083cd5348020d354d20082ef6048020db94120083ea4048020fa50120083eb3048020fa0c120082fb6548020ded95200827b6548020f694d20083d95348020bed8920083eb6248020de94920083ea5248020fa90920083e94248020facc920083e83248020fa88520083e82148020b798f54c42dd63d5310bb98b54c42ed62d53109f98f54c435e63d53109798f54c427d63d5310d758f54c425d63d53109f98b54c436e62d53109b98b54c427d62d5310db58b54c426d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c433f64553109fd8d54c427c63553109fd8954c427c6255310ded8154c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c427e64d4f109f59353c427e62d4f109f58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f109fd9153c427c6454f10d7d8d53c427f6254f109f18953c435d5314f10bb98853c42ed6214f109f99053c427d6414f10d798c53c427e6214f10db98853c426e6214f109f58853c436d6214f109b58853c43766114f10de58053c427f65d0f109f99743c427d65d0f109f19743c435e53d0f10d754f43c427f6590f109f99643c427d6590f109f19643c42ee6290f10bb58a43c42fa6090f10be58243c427f6550f109f99543c427d6550f109f19543c42fb6050f10be18143c427f6510f109f99443c427d6510f109f19443c435e5310f10d754c43c42f66110f10bd58443c427e64d4b109f59352c427e63d4b109f58f52c437661d4b10de58352c436f5294b109f99252c427d6494b109f98e52c427d6394b109fd9152c427c6454b109fd8d52c427c6354b10dbd8952c42de6314b10b758c52c436d5214b109f99052c427d6414b109f98c52c435e6314b109798c52c427d6314b10d758c52c425d6314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f197
  | 7 => 0x510c209f594430827c6510c20d794c430835d5310c209f992520827d64948209f98e520827d63948209f597420835e53d0820d754f42082ed65d0820db597420836f54d0820db553420836f53d0820f394f420836d53d0820f354f420834d53d0820bb583420827f65908209f596420833e5490820cf55242082de6390820b758e420835e5390820d754e42082ee6290820be98242082f960908209fd95420835e5350820d754d420827f65108209f594420833e5410820cf550420835e5310820d754c42082fa6010820be580420836d65108209b59442082ee6410820eb990420836f5410820eb950420836d5410820eb550420836f5310820f394c420836d5310820f354c420834d5310820fa98042082ed6010820fa58042082e960108209f597320835e53cc820d754f320827f658c8209f596320835e538c820d754e320836e528c820be98232082f9608c8209fd95320835e534c820d754d320836e524c8209fd94320827d650c820d794c320835d530c820f34c832082fa600c820be58032082de63d4420b758f510835e53d4420d754f510835e5394420d754e510837751944209f992510827d64944209f98e510827d6394420dbd0a510836c4294420d794d510835d53544209fd91510827c64544209fd8d510827c6354420af99051082bd6414420b798c51082dd6314420d794c510835d5314420dd544510827f65d04209f997410827d65d0420cf953410833d54d0420d794f410835d53d04209fd96410827e65904209f596410835e5390420d754e41082ee6290420bb58a41083765190420dd546410827f65504209f595410827c6550420cf951410833d5450420b7d8d41082dc6350420d794d410835d5350420bbd8941082ec6250420dd94541083755150420bed8141082f860504209fd94410827e65104209f594410835e5310420d754c410827f65cc4209f997310827d65cc420d794f310835d53cc4209fd96310827e658c4209f596310835e538c420d754e310827f654c4209f595310827c654c420d794d310835d534c420bbd8931082ec624c420bed8131082f8604c4209fd94310827e650c4209f594310835e530c420d754c31082ee620c420bb588310835e53c8420d754f210837651c8420dd54721082fa60c8420be583210827d6588420d794e210835d53884209fd95210835e5348420d754d21082de6308420b758c210835e5308420d754c21083765108420dd54421083e52108420be98021082f960084209f992500827d64940209f98e500827d6394020dbd0a500836c42940209f597400835e53d0020d754f400827f65900209f596400833e5490020cf552400835e5390020d754e40082ee6290020bb58a400827f6550020b7d8d40082dc6350020d794d400835d5350020bbd8940082ec6250020bdd854008
  | 8 => 0x20d714e314827f654c5209f995314827c654c520f34c9314827e650c5209f594314827c650c520d7d4c314835c530c520bb98831482ed620c520ddd443148374510c5209f99721483775188520dd14621482fa6088520be58221483775148520dd14521482fb6048520be181214827e6508520b798c21482dd63085209f997404833f54d0120cf15340482ee62d0120bb58b404827e65901209fd95404827d65501209f195404833f5450120cf15140482df6350120b718d40482ef6250120bb18940482f76150120bd185404827e65101209f997304835f53cc120d714f30482ee62cc120bb58b30483cd32cc1209f996304827f654c1209f595304827c654c120d7d4d304835c534c120bbd8930482ec624c120f34c9304827e650c120bb98830482ed620c120fa8cb20483e932c8120db952204836c5488120bbd8e20482ed6388120fad4220482de63d5020b758f540827e63d5020d798f540825e63d50209f58f540835d63d50209758f540827e62d5020db98b540827e61d50209f587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540833f64550209fd8d540827c63550209fd89540827d6255020db189540827f61550209f185540833d5415020b798c54082dd6315020bd98454082f561150209f990540833e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f988540836e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a60150209f993530827d64d4c209f98b530836e62d4c209f987530827d61d4c209f983530837a60d4c209f596530835f5394c209f992530827d6494c209f986530827d6194c2097596530835f5494c20d7952530835d5494c20d7152530835f6494c20d7992530835d6494c20d7192530835e6294c20d718a530835f6194c20d7986530835d6194c20d7186530835e6094c20d7182530827f6454c209f191530835f6354c209fd89530827d6254c209fd85530827c6154c20d7d95530835f5454c20d7951530835d5454c20d7151530835f6454c20d7991530835d6454c20d7191530835e6254c20d7189530835f6154c20d7985530835d6154c20d7185530835e6054c20d7181530835c2054c20b798c530835d5314c209f990530827d6414c209f98c530835e6314c209798c530827e6214c20db988530826e6214c209f984530827d6114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20d794f430835d53d0c209fd96430827e6590c209f596430827c6590c20d794e430835d5390c20bb98a43082ed6290c209fd95430827e6550c209f595430827c6550c20d794d430835d5350c20bbd8943082ec6250c20bed8143082f86050c209fd94430827e6
  | 9 => 0xd8554482f46155120cfd91544827f6355120d7d8d544825f63551209f18d544835c63551209718d544827f6255120dbd89544826f62551209fd85544837761551209dd85544827c6155120dd185544827461551209fd81544837b60551209f994544833d5415120cf990544827e63151209f58c544827e62151209f188544827e61151209f584544827e64d4d209f593534827e61d4d209f587534835f5394d209f992534827d6494d209f98e534827d6294d20db58a534827e6194d209f586534827d6094d20de58253482bf6454d20af19153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534835f6354d209fd89534836f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209f994534835d5314d209f990534827d6414d20d798c534827e6214d20db588534827c6214d209f984534827d6114d209fd97434827e65d0d209f597434827c65d0d20d7d4f434835c53d0d209fd96434827e6590d209f596434827c6590d20cfd52434833c5490d20bb98a43482ed6290d209fd95434827e6550d209f595434827c6550d209fd94434827e6510d209f594434827c6510d20cfd50434833c5410d20d7d4c434835c5310d20bb98843482ed6210d20be98043482f96010d209f997424833f54d0920cf15342482fa60d0920be583424827e6590920b798e42482dd63909209f195424833f5450920cf15142482fb6050920be181424827e65109209f997324835f53cc920d714f32482fa60cc920be583324827e658c920bb996324836e658c920db952324836c548c920bb58e324836e538c920db14e32482ee608c9209f195324835f534c920d714d32482fb604c920be181324836c654c9209b195324836e544c920db15132483cf634c920f3d4d324836e534c920db14d32483cc534c920d314d32483cf434c920f310d32483eb604c920bb18132483e8604c920ba181324827e650c920bb98832483cd320c9209f993514827d64d45209f98f514827d63d4520db8cb514836d32d4520ddd4651482bf6454520af19151482df6354520b718d514837551145209f990514827d64145209f98c514827d63145209f997414827d65d05209f197414837751d0520dd147414827e65905209f596414827c6590520cfd52414833c54905209fd95414827e65505209f19541482df6350520b718d41482ef6250520bb18941482fb6050520be181414827e65105209f594414827c6510520cfd50414833c5410520bb98841482ed6210520ddd4441483745110520be98041482f960105209f997314827d65cc5209f19731482ee62cc520bb58b31483cd32cc520ddd47314837451cc520be98331482f960cc5209f996314827d658c5209f196314835f538c5
  | 10 => 0x48825f63552209f18d548835c63552209718d548836f62552209fd85548827c6155220cf550548833e64152209f98c548827d6315220db588548827e61152209f584548837a60152209f993538827d64d4e20db58b538827e61d4e209f587538837a60d4e20d7d4e538827e6494e209f592538827e6194e209f586538827f6454e209f191538835f6354e209fd85538827c6154e20d754c538827e6414e209f590538835e6314e20db588538827e6114e209f584538837a6014e209fd97438827e65d0e209f597438827c65d0e20d7d4f438835c53d0e209fd96438827e6590e209f596438827c6590e20bb98a43882ed6290e209fd95438827e6550e209f595438827c6550e20bbd8943882ec6250e209fd94438827e6510e209f594438827c6510e20d7d4c438835c5310e20be98043882f96010e20cf953428833d54d0a20be98342882f960d0a20db597428836f54d0a20eb953428836d54d0a20eb553428836f53d0a20db54f42883ea60d0a20bb58342883e960d0a20b798e42882dd6390a20cf951428833d5450a20bed8142882f86050a20bb594428836d6510a20eb990428836f5410a20db550428836f5310a20db54c42882ed6010a20d794f328835d53cca20be98332882f960cca20d794d328835d534ca20bed8132882f8604ca20f34c8328837751946209f992518827d64946209f98e518827d6394620dbd0a518836c42946209fd91518827c64546209fd8d518827c6354620dd544518827f65d06209f997418827d65d06209fd96418827e65906209f59641882ee6290620bb58a418827f65506209f595418827c6550620b7d8d41882dc6350620bbd8941882ec6250620bed8141882f860506209fd94418827e65106209f59441882fa6010620be580418827f65cc6209f997318827d65cc620be98331882f960cc6209fd96318827e658c6209f596318827f654c6209f595318827c654c620bbd8931882ec624c6209fd94318827e650c6209f59431882ee620c620bb58831883765188620dd54621882fa6088620be58221883765148620dd54521882fb6048620be18121882de6308620b758c21883e52108620cf952408833d5490220bb98a40882ed6290220b7d8d40882dc6350220bbd8940882ec6250220bdd8540882f46150220cf950408833d5410220bb98840882ed6210220d7d4f308835c53cc220d794e308835d538c220bb98a30882ed628c220d7d4d308835c534c220d794c308835d530c220bb98830882ed620c220bb597208836d65c8220bb99320882ec64c8220dbd4f208836d53c8220be597208837965c82209f98f544827d63d51209f987544827d61d5120cfd52544827e64951209f98e544827d63951209f58a544836d62951209f986544827d61951209f58254483796095120b7d8d54482dc6355120bd
  | 11 => 0x7960d4f20d7d4e53c827e6494f209f59253c836e6294f209f98653c827d6194f209fd9153c827c6454f20d7d8d53c827f6154f209f18553c835d5314f20bd98453c82f56114f209f99053c827d6414f20d798c53c836e6214f209f98453c83766114f209d98453c827d6114f20dd58453c82756114f20de58053c827f65d0f209f99743c827d65d0f209f19743c835e53d0f20d754f43c827f6590f209f99643c827d6590f209f19643c82ee6290f20bb58a43c827f6550f209f99543c827d6550f209f19543c82fb6050f20be18143c827f6510f209f99443c827d6510f209f19443c835e5310f20d754c43c82ee6210f20bb58843c833e5490b20cf55242c82de6390b20b758e42c82fa6090b20be58242c833e5410b20cf55042c82fa6010b20be58042c835f53ccb20d714f32c835e538cb20d754e32c82fa608cb20be58232c836d658cb20db95232c836c548cb20db94e32c83ce538cb20f354e32c836c538cb20bb98232c83ea608cb20fa58232c835f534cb20d714d32c82ef654cb20dbd9532c836e544cb20db15132c83cf634cb20f3d4d32c836e534cb20db14d32c83cc534cb20d314d32c83cf434cb20f310d32c82ec604cb20d794c32c835d530cb20f34c832c82fa600cb20be58032c837751947209f99251c827d64947209f98e51c827d63947209fd9151c827c64547209fd8d51c827c6354720db8c951c836d3254720b798c51c82dd6314720dd54451c827f65d07209f99741c827d65d0720dd94741c837551d07209fd9641c827e65907209f59641c827f65507209f59541c827c6550720b7d8d41c82dc6350720bbd8941c82ec6250720bed8141c82f860507209fd9441c827e65107209f59441c82ee6210720bb58841c83765110720dd54441c827f65cc7209f99731c827d65cc720d794f31c835d53cc720bb98b31c82ed62cc720f34cb31c827f658c7209f99631c827d658c720dd94631c8375518c7209fd9531c827d654c7209f19531c835e534c720d754d31c83cd324c720dd94531c8375514c720bed8131c82f8604c7209fd9431c827e650c7209f59431c82ee620c720bb58831c837651c8720dd54721c82fa60c8720be58321c82de6308720b758c21c83765108720dd54421c82fa6008720be58021c833e54d0320cf55340c82ee62d0320bb58b40c833e5450320cf55140c82df6350320b718d40c82ef6250320bb18940c82f76150320bd18540c83b94010320d794f30c835d53cc320bb98b30c82ed62cc320f34cb30c835e534c320d754d30c82ef624c320bb18930c83cd324c320bb98830c82ed620c320f64c030c827e63d52209f58f548836d62d52209f987548827d61d5220de983548833f54952209f98e548827d63952209f986548827d6195220b7d8d54882dc6355220cfd91548827f6355220d7d8d5
  | 12 => 0x14430af590510c2ee6214430bb588510c36e5214430db548510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c36e52d0430db54b410c27f65904309f996410c27d6590430b798e410c2dd6390430db94a410c36d5290430dd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c2ef6250430bb189410c36e5250430db549410c3765150430dd545410c2fb6050430be181410c27f65104309f994410c27d6510430db948410c36d5210430db94b310c36d52cc430dd947310c37551cc430be983310c2f960cc4309f596310c36e528c430db54a310c27f654c430db949310c36d524c430bb988310c2ed620c430db948310c36d520c430dd944310c375510c430f54c4310c2fa600c430be580310c27f65c84309f997210c27d65c8430db94b210c36d52c84309fd96210c27e65884309f596210c36e5288430db54a210c27f65484309f595210c27c6548430b7d8d210c2dc6348430db949210c36d5248430bed81210c2f860484309fd94210c27e65084309f594210c2de6308430b758c210c36e5208430db548210c27e64940309f592500c35f4394030d710e500c27d65d0030db94b400c36d52d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd6390030db94a400c36d52900309fd95400c2df6350030b718d400c2ef6250030bb189400c36e5250030db549400c2f76150030bd185400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c36e5210030db548400c3b94010030db94b300c36d52cc030b7993300c2dc64cc030f394b300c35d52cc030f354b300c34d52cc030b758e300c35e538c030db94a300c36d528c030be58e300c37a538c030f694e300c3db438c030f610e300c3ea528c030fa54a300c27f654c030db949300c36d524c030b7d95300c35f654c03097d95300c2de644c030b7191300c3ce524c030d7549300c3cd524c030d3549300c2df604c030d7941300c3da404c030f6501300c2fb654c030ded95300c27b654c030bed8d300c3db634c030de94d300c3da534c030f690d300c3d9434c030fa949300c3e9524c030f68c9300c3d8324c030f68c5300c3d8314c030b798f54c82dd63d5320bd98754c82f561d53209f98f54c835e63d53209798f54c827d63d5320d758f54c825d63d5320db98b54c827e61d5320dd98754c827661d53209f58754c837561d53209d58754c837960d5320cfd5254c827e63953209f58e54c827e61953209f58654c833f64553209fd8d54c827c63553209fd8554c827c6155320cf55054c833e64153209f98c54c827d6315320db98854c827e61153209f58454c837960153209f99353c827d64d4f20db98b53c827e61d4f209f58753c83
  | 13 => 0xbdd85404c2f461501309f994404c3db32cc130f64cb304c35e548c130d7152304c2dd628c130f6d42304c2ee62d5030bb58b540c27e63d5030d798f540c27e62d5030db98b540c26e62d50309f58b540c36d62d50309b58b540c27e61d50309f587540c27e60d5030de983540c27d6595030cfd52540c27e62950309f58a540c27e61950309f586540c33f64550309fd8d540c27d6355030d718d540c27f62550309f189540c27f61550309f185540c33d5415030bb988540c2ed6215030bd984540c2f561150309f990540c33e64150309f98c540c35e63150309f988540c36e62150309b988540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a60150309f992530c27d6494c309f597430c2dd65d0c30d7597430c35f54d0c30d7553430c2dd60d0c309fd96430c27d6590c30cf952430c33d5490c30b798e430c2ee6290c30bb58a430c2fa6090c30be582430c27f6550c309fd94430c27d6510c30cf950430c33d5410c30be980430c2f96010c30d7594430c25d6510c30b7990430c39e6410c30d7d50430c39e5410c30d7550430c39d5410c30f6980430c2dd6010c30f6580430c2d96010c30dbd4a520c27e64948309f592520c27e61948309f586520c36f5494830db952520c36d5494830db152520c3cf4394830f310e520c36f6494830db992520c36d6494830db192520c36c6394830dbd0e520c36e4394830db50e520c36c4394830dbd86520c36e6194830db586520c36c6194830db982520c36c60948309fd91520c27c6454830d7d0d520c35c43548309fd85520c27c6154830dbd95520c36f5454830db951520c36d5454830db151520c3cf4354830f310d520c36f6454830db991520c36d6454830db191520c36e6354830dbd0d520c34f4354830db90d520c36d4354830db10d520c34c4354830dbd85520c36e6154830db585520c36c6154830db981520c36c6054830db0c1520c2ee6214830db548520c27f65d08309f997420c27d65d0830db94b420c36d52d08309fd96420c27e65908309f596420c2de6390830b758e420c36e5290830db54a420c27f65508309f595420c27c6550830b7d8d420c2dc6350830db949420c36d5250830bed81420c2f860508309fd94420c27e65108309f594420c36e5210830db548420c35e53cc830db94b320c36d52cc830be983320c2f960cc8309f596320c36d528c8309fd95320c35e534c830db949320c36e520c830db548320c3cd320c830be980320c2f9600c830bb98b510c2ed62d4430db94b510c36d52d4430db94a510c36d5294430ddd46510c27e64944309f592510c35f4394430d710e510c27e62944309f58a510c36e5254430db549510c27f64544309f191510c27f62544309f189510c2be64
  | 14 => 0x85544c2f46155130cfd91544c27f6355130d7d8d544c25f63551309fd89544c36f62551309bd89544c27c6255130db189544c26c62551309fd85544c37761551309dd85544c27c6155130dd185544c27461551309fd81544c37b60551309f994544c33d5415130cf990544c27e63151309f18c544c27e62151309f588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d309f996434c2ee6290d30bb58a434c27c6550d30cfd51434c33c5450d30bed81434c2f86050d309f994434c27e64d49309f593524c27e61d49309f587524c36f5294930afd91524c2bc6454930bdd85524c2f46154930db548524c27e64149309f590524c27e61149309f584524c27e65d09309f597424c27c65d0930dbd4b424c36c52d09309f996424c27d65909309f196424c33f5490930cf152424c2de6390930b758e424c27f65509309f995424c27c65509309f994424c27d65109309f194424c33f5410930cf150424c2de6310930b758c424c36f5210930db148424c2fa6010930be580424c27e65cc930b7997324c35e65cc930d7953324c35c54cc930d714b324c2de60cc930b758e324c36f528c930db14a324c2fa608c930be582324c36f524c930db149324c2fb604c930be181324c35e544c930d7151324c3cf624c930f3d49324c35c524c930f3149324c34c524c930f3d09324c3cc424c930f6d81324c2dc604c930f6181324c2d8604c9309f994324c2de630c930f34c8324c27e64d45309f593514c27e62d45309f58b514c35f32d4530d74cb514c3775194530afd91514c2bc6454530bbd89514c2ec6254530dd544514c27e64145309f590514c27e62145309f588514c27e65d05309f597414c27c65d0530ddd47414c37451d05309f996414c27d65905309f196414c33f5490530cf152414c27f65505309f995414c27c6550530b7d8d414c2dc6350530bbd89414c2ec6250530bed81414c2f860505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c3775110530dd144414c2fa6010530be580414c27e65cc530ddd46314c374518c530be982314c2f9608c530ddd45314c374514c530bed81314c2f8604c5309f994314c2ee620c530bb588314c27e65c85309f597214c27c65c8530b798f214c2dd63c8530f34cb214c37751c8530dd147214c2fa60c8530be583214c27e65885309f596214c27c6588530dbd4a214c36c52885309fd95214c27e65485309f195214c3cd32485309f994214c27d65085309f194214c2de6308530b758c214c36f5208530db148214c3775108530dd144214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d01309f996404c27f65501309f595404c27c6550130cfd51404c33c5450130b7d8d404c2dc6350130bbd89404c2ec625013
  | 15 => 0xcc3755148730bed8121cc2f860487309fd9421cc27e65087309f59421cc2de6308730b758c21cc33e54d0330cf55340cc2de63d0330b758f40cc33e5450330cf55140cc2df6350330b718d40cc2ef6250330bb18940cc2f76150330bd18540cc3b94010330d758f548c27e62d52309f58b548c27e61d52309f587548c37a60d5230cfd52548c27e62952309f58a548c27e61952309f586548c2ef6255230bb189548c33f6455230d7d8d548c27f6255230dbd89548c26f62552309f189548c36c62552309b189548c27f61552309f185548c33d5415230cf990548c35d63152309f988548c27d62152309f984548c27d6115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c35d65d0e30d7d53438c39e54d0e30d7553438c39d54d0e30f6983438c2dd60d0e30f6583438c2ee6290e30bb58a438c33e5450e30cf551438c2fb6050e30be181438c2dd6510e30d7594438c39e6410e30d7d50438c35d5410e30b7580438c36f5294a309f992528c27d6494a309f986528c27d6194a309fd91528c27c6454a30d7d0d528c35c4354a309fd85528c27c6154a30db548528c27f65d0a309f997428c27d65d0a309fd96428c27e6590a309f596428c2de6390a30b758e428c27f6550a309f595428c27c6550a30b7d8d428c2dc6350a309fd94428c27e6510a309f594428c2fa6010a30be580428c36e528ca30db54a328c2fa608ca30be582328c36e524ca30db549328c2fb604ca30be181328c3cd320ca30ddd46518c27e64946309f592518c35f4394630d710e518c27e62946309f58a518c27f64546309f191518c27f62546309f189518c37551146309fd97418c27e65d06309f597418c27f65906309f996418c27d6590630b798e418c2dd63906309fd95418c27d65506309f195418c2df6350630b718d418c2ef6250630bb189418c2fb6050630be181418c27f65106309f994418c27d6510630be980418c2f96010630dd946318c375518c630be982318c2f9608c630dd945318c375514c630bed81318c2f8604c630bb988318c2ed620c630f54c4318c27f65c86309f997218c27d65c8630be983218c2f960c86309fd96218c27e65886309f596218c27f65486309f595218c27c6548630b7d8d218c2dc63486309fd94218c27e65086309f594218c2de6308630b758c218c33e5490230cf552408c2de6390230b758e408c2df6350230b718d408c2ef6250230bb189408c2f76150230bd185408c33e5410230cf550408c2de6310230b758c408c2dd65cc230d7597308c2de64cc230b7193308c35d52cc230be597308c37965cc2309f98b544c27d62d51309f987544c27d61d5130cfd52544c27e64951309f58e544c35d63951309f98a544c27d62951309f986544c27d61951309f582544c3796095130bbd89544c2ec6255130bdd
  | 16 => 0xa61900409fd9540102df6350040b718d40102ef6250040bb18940102f76150040bd18540102bf6550040cfd95401023f6550040e7d8d401039c6350040ebd8940103ac6250040edd8540103b46150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103db6350040f618d40103ba4350040ee10d40103eb6250040fa18940103ba4250040ee10940103f36150040be18540103f06150040bc18540103bb4150040ee50540102ee62d5330bb58b54cc2f661d5330bd58754cc35e63d53309f98b54cc36e62d53309b98b54cc27d62d5330db58b54cc26d62d53309f98754cc37661d53309d98754cc27d61d5330dd58754cc27561d5330de58354cc33f54953309f98a54cc27d62953309f98654cc27d6195330cfd9154cc27f62553309f18954cc27f61553309f18554cc33d5415330cf99054cc35e63153309f98854cc27d62153309f98454cc27d6115330de58054cc33e5490f30cf55243cc2ee6290f30bb58a43cc2fa6090f30be58243cc33e5410f30cf55043cc2fa6010f30be58043cc36f5294b309f99252cc27d6494b309f98652cc27d6194b309fd9152cc27c6454b309fd8552cc27c6154b30db54852cc2f66114b30bd58452cc27f65d0b309f99742cc27d65d0b30db94b42cc36d52d0b309fd9642cc27e6590b309f59642cc2de6390b30b758e42cc27f6550b309f59542cc27c6550b30bed8142cc2f86050b309fd9442cc27e6510b309f59442cc2de6310b30b758c42cc36e5210b30db54842cc36e52ccb30db54b32cc2fa60ccb30be58332cc35e54ccb30d715332cc35e52ccb30f394b32cc3cd52ccb30b798332cc3da60ccb30f658332cc2df654cb30d7d9532cc35e544cb30d715132cc3cf624cb30f3d4932cc35e524cb30f314932cc3cf424cb30f310932cc2dc604cb30db94832cc36d520cb30f34c832cc2fa600cb30be58032cc37751947309f99251cc27d64947309f98a51cc27d62947309fd9151cc27c64547309fd8951cc27c6254730d7cc951cc35d3254730bb98851cc2ed6214730dd54451cc27f65d07309f99741cc27d65d0730dd94741cc37551d07309fd9641cc27e65907309f59641cc27f65507309f59541cc27c6550730b7d8d41cc2dc6350730bbd8941cc2ec6250730bed8141cc2f860507309fd9441cc27e65107309f59441cc2de6310730b758c41cc3765110730dd54441cc37651cc730dd54731cc2fa60cc730be58331cc2ee620c730bb58831cc376510c730dd54431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730b798f21cc2dd63c8730db94b21cc36d52c8730f34cb21cc27f65887309f99621cc27d6588730dd94621cc37551887309fd9521cc27d65487309f19521cc36e5248730db54921cc3cd3248730dd94521
  | 17 => 0x8540d714d215036f5248540db14921503775148540dd145215027e65085409f594215027c6508540af99021502bd6408540b798c21502dd6308540d7d4c215035c5308540dbd48215036c5208540ddd4421503745108540be98021502f96008540d7d4f405035c53d0140dbd4b405036c52d0140ddd47405037451d0140f6d4f40503d853d0140fad4b40503e852d0140fcd47405037851d0140fc147405037051d0140d7d4e405035c5390140dbd4a405036c5290140ddd4640503745190140e7d4e405039c5390140ebd4a40503ac5290140edd4640503b45190140eed42405035f5394c409f98a531027d6294c409f986531027d6194c409fd89531027c6254c409fd85531027c6154c40d754c53102ee6214c40bb58853102f66114c40bd584531035e53d0c40d754f43102fa60d0c40be583431027d6590c40bb98a43102ed6290c409fd95431035e5310c40d754c43102fa6010c40be580431036f52948409f98e521027d63948409f986521027d61948409fd8d521027c63548409fd85521027c6154840b798c52102dd6314840db54852102f66114840bd584521036e52d0840db54b42102fa60d0840be583421027d6590840b798e42102dd63908409fd95421036e5210840db54842102fa6010840be580421027f65cc8409f997321027d65cc840d794f321035d53cc8409fd96321027e658c8409f596321036e528c840db54a321027f654c8409f595321027c654c840afd9132102bc644c840d794d321035d534c840db949321036d524c840bed8132102f8604c8409fd94321027e650c8409f59432103cd320c840ddd46511027e63944409f58e511027e62944409f58a511027f63544409f18d511027f62544409f18951103786054440b798c51102dd6314440bb98851102ed6214440dd544511037651d0440dd54741102fa60d0440be583411027d65904409fd9541102df6350440b718d41102ef6250440bb18941102fb6050440dd94441103755110440be98041102f960104409fd97311027e65cc4409f597311035e53cc440d754f31102fa60cc440be583311027f658c4409f996311027d658c440dd9463110375518c4409fd95311027d654c4409f19531102bf644c440af191311035e534c440d754d3110376514c440dd54531102fb604c440be181311027f650c4409f994311027d650c440bb98831102ed620c4409fd97211027e65c84409f597211036e52c8440db54b21102fa60c8440be583211027f65884409f996211027d6588440dd946211037551884409fd95211027d65484409f19521102bf6448440af191211036e5248440db54921103765148440dd54521102fb6048440be181211027f65084409f994211027d6508440b798c21102dd6308440af592401033e5490040be592401037a5490040ee95240102f
  | 18 => 0xdb14832503cd320c940be98032502f9600c940d7d4f515035c53d4540dbd4b515036c52d45409f98f515027d63d45409f98b515027d62d4540ddd4f51503d753d4540d5d4f515037653d4540dd54f515037453d4540f514f515035453d4540ddd4b51503e752d4540d9d4b515037652d4540dd54b515037452d4540f914b515036452d4540ddd93515037763d4540dd98f515037563d4540dd18f515037743d4540dd90f515037543d4540dd10f515037762d4540dd98b515037562d4540dd18b515037742d4540dd90b515037542d4540dd10b515037732d4540dd8cb515037532d4540dd0cb515037760d4540dd58351502de6394540b758e515035f5394540d714e51502ee6294540bb58a515036f5294540db14a51503775194540b7d8d51502dc6354540d7d4d515035c5354540bbd8951502ec6254540dbd49515036c5254540d7d4c515035c5314540dbd48515036c5214540dd544515027e63145409f58c515027e62145409f58851502f66514540dd99451503775314540f5d4c51503575314540dd94c51503755314540dd14c51503d45314540d514c51503775214540f9d4851503675214540dd94851503755214540dd14851503e45214540d914851503776414540ddd8c51503766314540dd58c51503746314540ddd0c51503764314540dd50c51503744314540ddd8851503766214540dd58851503746214540ddd0851503764214540dd50851503744214540ddcc851503763214540dd4c851503743214540ddd8051503756014540dd500515027e65d0540d7d4f415035c53d0540dbd4b415036c52d0540dd147415035f5390540d714e415036f5290540db14a41503775190540dd14641502fa6090540be58241502df6350540b718d415035f5350540d714d41502ef6250540bb189415036f5250540db14941503775150540dd14541502fb6050540be181415027e6510540d7d4c415035c5310540dbd48415036c5210540ddd4441503b541105409f997315027d65cc5409f197315035f53cc540d714f315036f52cc540db14b315037751cc540dd147315027e658c5409f596315027c658c540d7d4e315035c538c540dbd4a315036c528c540ddd463150374518c5409fd95315027e654c5409f195315035f534c540d714d315036f524c540db1493150377514c540dd145315027e650c5409f594315027c650c540af99031502bd640c540d7d4c315035c530c540bb98831502ed620c540dbd48315036c520c540ddd443150374510c540be98031502f9600c5409f997215027d65c85409f197215035f53c8540d714f215036f52c8540db14b215037751c8540dd147215027e65885409f596215027c6588540d7d4e215035c5388540dbd4a215036c5288540ddd46215037451885409fd95215027e65485409f195215035f534
  | 19 => 0x4319027d650c640d794c319035d530c640bb98831902ed620c640be98031902f9600c6409fd97219027e65c86409f597219027f65886409f996219027d6588640db94a219036d52886409fd95219027d65486409f19521902bf6448640af191219027f65086409f994219027d6508640b798c21902dd6308640db948219036d5208640be98021902f96008640af597409033d65d0240be597409037965d0240de947409027e62d4d409f58b535027e61d4d409f587535035f64d4d40d7d8b535035e62d4d40d758b535035c62d4d40d7d87535035e61d4d40d7587535035c61d4d40d7d83535035d60d4d40d7d4e53502ee6294d40bb58a53502f66194d40bd58653502ef6254d40bb18953502f76154d40bd185535035d5314d409f988535027d6214d409f984535027d6114d40b7994535035e6514d40d7d90535035f6214d40d7988535035d6214d40d7188535035f6114d40d7984535035d6114d40d7184535035f6014d40d7580535035d4014d409f997435035c53d0d40d7d4e435035c5390d40bb98a43502ed6290d40be98243502f96090d40d7d4d435035c5350d40bed8143502f86050d409f994435035f5310d40d7d4f525035c53d49409f98f525027d63d49409f987525027d61d4940dbd4f52503cf53d4940d3d4f525036e53d4940db54f525036c53d4940f314f525034c53d4940dbd93525036f63d4940db98f525036d63d4940db18f525036f43d4940db90f525036d43d4940db10f525036f61d4940db987525036d61d4940db187525036f60d4940db58352502de6394940b758e525035f5394940d714e525036f5294940bd98652502f56194940b7d8d52502dc6354940d7d4d525035c5354940bdd8552502f46154940d7d4c525035c5314940db548525027e63149409f58c525027e61149409f58452502ee6514940db994525036f5314940f3d4c525034f5314940db94c525036d5314940db14c52503cc5314940d314c525036f6414940dbd8c525036e6314940db58c525036c6314940dbd0c525036e4314940db50c525036c4314940dbd84525036e6114940db584525036c6114940dbd80525036d6014940db500525027e65d0940d7d4f425035c53d0940db14b42502de6390940b758e425035f5390940d714e425036f5290940db14a42502fa6090940be582425035f5350940d714d425036f5250940db14942502fb6050940be181425027e6510940d7d4c425035c5310940dbd48425027e65cc9409f597325027c65cc940d7d4f325035c53cc940dbd4b325036c52cc9409f996325027d658c9409f196325035f538c940d714e325036f528c940db14a325027f654c9409f995325027c654c940d7d4d325035c534c940dbd49325036c524c9409f994325027d650c9409f194325035f530c940d714c325036f520c940
  | 20 => 0x2de6394b40b758e52d036f5294b409f98e52d035e6394b409798e52d027d6394b40d758e52d025d6394b409f98652d027d6194b409fd8d52d027c6354b409fd8552d027c6154b40db54852d036e52d0b40db54b42d02fa60d0b40be58342d02de6390b40b758e42d036e5210b40db54842d02fa6010b40be58042d027f65ccb409f99732d027d65ccb409fd9632d027e658cb409f59632d027f654cb409f59532d027c654cb40bed8132d02f8604cb409fd9432d027e650cb409f59432d03cd320cb40ddd4651d027e63947409f58e51d027e62947409f58a51d027f63547409f18d51d027f62547409f18951d037b6054740dd54451d037651d0740dd54741d02fa60d0740be58341d02df6350740b718d41d02ef6250740bb18941d02f86050740dd94441d03755110740ed50441d02fa6010740be58041d027f65cc7409f99731d027d65cc740be98331d02f960cc7409fd9631d027e658c7409f59631d027f654c7409f59531d027c654c740bed8131d02f8604c7409fd9431d027e650c7409f59431d02be640c740af59031d02ee620c740bb58831d027f65c87409f99721d027d65c8740be98321d02f960c87409fd9621d027e65887409f59621d027f65487409f59521d027c6548740bed8121d02f860487409fd9421d027e65087409f59421d02be6408740af59021d02de6308740b758c21d035f5394e409f98a539027d6294e409f986539027d6194e409fd89539027c6254e409fd85539027c6154e40d754c53902ee6214e40bb588539035e5390e40d754e43902ee6290e40bb58a43902fa6090e40be582439035e5350e40d754d43902fb6050e40be181439036f5294a409f98e529027d6394a409f986529027d6194a409fd8d529027c6354a409fd85529027c6154a40b798c52902dd6314a40db54852902de6390a40b758e429036e5290a40db54a42902fa6090a40be582429036e5250a40db54942902fb6050a40be181429027f65cca409f997329027d65cca40d794f329035d53cca409fd96329027e658ca409f596329036e528ca40db54a329027f654ca409f595329027c654ca40afd9132902bc644ca40d794d329035d534ca40db949329036d524ca409fd94329027e650ca409f59432903cd320ca40be98032902f9600ca40b798f51902dd63d4640bb98b51902ed62d4640ddd46519027e63946409f58e519027e62946409f58a519027f63546409f18d519027f62546409f18951903755114640dd94641903755190640be98241902f96090640b7d8d41902dc6350640bbd8941902ec6250640dd94541903755150640bed8141902f860506409fd97319027e65cc6409f597319027f658c6409f996319027d658c640d794e319035d538c6409fd95319027d654c6409f19531902bf644c640af191319027f650c6409f99
  | 21 => 0x5390821d754e42086ee6290821bd98642086f561908219fd95420875e5350821d754d420867f65108219f594420873e5410821cf550420875e5310821d754c42086f66110821bd584420876d65108219b59442086ee6410821eb990420876f5410821eb950420876d5410821eb550420876f5310821f394c420876d5310821f354c420874d5310821f998442086ed6110821f958442086e561108219f597320875e53cc821d754f320867f658c8219f596320875e538c821d754e320876e528c821bd98632086f5618c8219fd95320875e534c821d754d320876e524c8219fd94320867d650c821d794c320875d530c821f34c832086f6610c821bd584320867e64944219f592510867e63944219f58e510876f4294421db10a510867d65d0421d794f410875d53d04219fd96410867d6590421cf952410873d5490421d794e410875d5390421bb98a41086ed62904219fd9541086df6350421b718d410875e5350421d754d41086ef6250421bb18941086fb6050421be181410867f65104219f994410867d65104219f194410873e5410421cf550410875e5310421d754c41086ee6210421bb58841087b541104219f597310875e53cc421d754f310867f658c4219f596310875e538c421d754e31086ee628c421bb58a310867f654c421d794d310875d534c4219fd94310867e650c4219f594310867c650c421d794c310875d530c421bb98831086ed620c421f54c4310875e53c8421d754f21086ee64c8421bb193210876f53c8421f394f210876d53c8421f354f210874d53c8421d794e210875d5388421bb58a210876e5288421f594e21087d55388421bd58a21087765288421f994a21087e74288421f910a210867f6548421d794d210875d5348421bbd95210876f65484219bd9521086ee6448421bb191210876f5348421f394d210876d5348421f354d210874d5348421bbd85210876e5148421f990521087e54148421f9cc521087e43148421bdd95210877765484219dd9521087d65348421f554d21086f76248421f9d8921087765248421f994921087e64248421f950921087e73248421f90c921086de63d4021b758f500875e53d4021d754f500875e5394021d754e500877b50940219f992500867d64940219f98e500867d6394021dbd0a500876c4294021d794d500875d53540219fd91500867c64540219fd8d500867c6354021af99050086bd6414021b798c50086dd6314021d794c500875d5314021de540500875f5394f40bb98a53d02ed6294f409f98a53d036e6294f409b98a53d027d6294f40db58a53d026d6294f409f98653d027d6194f409fd8953d027c6254f409fd8553d027c6154f40d754c53d035e53d0f40d754f43d02fa60d0f40be58343d02ee6290f40bb58a43d035e5310f40d754c43d02fa6010f40be58043d
  | 22 => 0x521bb18941486fb6050521be181414867e65105219f997314875f53cc521d714f31486ee62cc521bb58b31487cd32cc5219f996314867f654c5219f595314867c654c521d7d4d314875c534c521bbd8931486ec624c521f34c9314867e650c521bb98831486ed620c521f98cb21487e532c8521db952214876c5488521bbd8e21486ed6388521f9d46214867e64d41219f593504867e63d41219f58f504876e32d4121db4cb504877b5094121afd9150486bc6454121b7d8d50486dc6354121de540504867e64141219f590504867e63141219f58c50486de63d5021b758f540867e63d5021d798f540865e63d50219f58f540875d63d50219758f540867e62d5021db98b540867e61d5021dd987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c6355021db189540867f60550219f181540873d5415021b798c54086dd6315021be98054086f960150219f990540873e64150219f98c540875e63150219798c540867d6315021d758c540865d63150219f988540876e62150219f984540877661150219f980540877a60150219e980540867d6015021de580540867960150219f993530867d64d4c219f98b530876e62d4c219f987530877661d4c219f983530867d60d4c219f596530875f5394c219f992530867d6494c219f982530867d6094c2197596530875f5494c21d7952530875d5494c21d7152530875f6494c21d7992530875d6494c21d7192530875e6294c21d718a530875e6194c21d7186530875f6094c21d7982530875d6094c21d7182530867f6454c219f191530875f6354c219fd81530867c6054c21d7d95530875f5454c21d7951530875d5454c21d7151530875f6454c21d7991530875d6454c21d7191530875e6254c21d7189530875e6154c21d7185530875c2154c21d7d81530875e6054c21d7581530875c6054c21b798c530875d5314c219f990530867d6414c219f98c530875e6314c219798c530867e6214c21db988530866e6214c219f98453087766114c219f980530867d6014c219fd97430867e65d0c219f597430867c65d0c21d794f430875d53d0c219fd96430867e6590c219f596430867c6590c21d794e430875d5390c21bb98a43086ed6290c219fd95430867e6550c219f595430867c6550c21d794d430875d5350c21bbd8943086ec6250c21bdd8543086f46150c219fd94430867e6510c219f594430867c6510c21d794c430875d5310c219f992520867d64948219f98e520867d63948219f597420875e53d0821d754f42086ed65d0821db597420876f54d0821db553420876f53d0821f394f420876d53d0821f354f420874d53d0821bb587420867f65908219f596420873e5490821cf55242086de6390821b758e420875e
  | 23 => 0xb98841886ed6210621d7d4f318875c53cc621d794e318875d538c621bb98a31886ed628c621d7d4d318875c534c621d794c318875d530c621bb98831886ed620c621bb597218876d65c8621bb99321886ec64c8621dbd4f218876d53c8621bd597218877565c8621ded42508867e64942219f592508867e63942219f58e508876f4294221db10a508867f64542219f191508867f63542219f18d508877950142219f98f544867d63d51219f983544867d60d5121cfd52544867e64951219f98e544867d63951219f58a544876d62951219f586544877561951219f982544867d6095121b7d8d54486dc6355121bed8154486f86055121cfd91544867f6355121d7d8d544865f63551219f18d544875c63551219718d544867f6255121dbd89544866f62551219fd85544877761551219fd81544877b60551219ed81544867c6055121de181544867860551219f994544873d5415121cf990544867e63151219f58c544867e60151219f580544867e64d4d219f593534867e60d4d219f583534875f5394d219f992534867d6494d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d219f58253486bf6454d21af19153486fb6054d21be181534867f6454d21cfd91534863f6454d219f191534873c6454d218f191534875f6354d219fd89534876f6254d219fd8553487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f994534875d5314d219f990534867d6414d21d798c534876d6214d219f980534867d6014d219fd97434867e65d0d219f597434867c65d0d21d7d4f434875c53d0d219fd96434867e6590d219f596434867c6590d21cfd52434873c5490d21bb98a43486ed6290d219fd95434867e6550d219f595434867c6550d219fd94434867e6510d219f594434867c6510d21cfd50434873c5410d21d7d4c434875c5310d21bb98843486ed6210d21bd98443486f56110d219f997424873f54d0921cf15342486f661d0921bd587424867e6590921b798e42486dd63909219f195424873f5450921cf15142486f76150921bd185424867e65109219f997324875f53cc921d714f32486f661cc921bd587324867e658c921bb996324876e658c921db952324876c548c921bb58e324876e538c921db14e32486ee618c9219f195324875f534c921d714d32486f7614c921bd185324876c654c9219b195324876e544c921db15132487cf634c921f3d4d324876e534c921db14d32487cc534c921d314d32487cf434c921f310d32487e7614c921bb18532487e4614c921b9185324867e650c921bb98832487cd320c9219f997414873f54d0521cf15341486ee62d0521bb58b414867e65905219fd95414867d65505219f195414873f5450521cf15141486df6350521b718d41486ef6250
  | 24 => 0x42c873d5490b21b798e42c86dd6390b21bd98642c86f56190b21cf95042c873d5410b21bd98442c86f56110b21d7d4f32c875c53ccb21d794e32c875d538cb21bd98632c86f5618cb21db59632c876e548cb21db15232c876e538cb21f394e32c87cd538cb21db14e32c86ee618cb21f998632c87e5618cb21d7d4d32c875c534cb21bbd9532c876f654cb21db95132c876c544cb21f3d8d32c87cf534cb21db94d32c876c534cb21f314d32c874c534cb21f3d0d32c87cc434cb21bb18532c875e530cb21d754c32c87cd320cb21bd98432c86f5610cb21cf95341c873d54d0721bb98b41c86ed62d0721cf95141c873d5450721b7d8d41c86dc6350721bbd8941c86ec6250721bed8141c86f86050721ed50441c875e53cc721d754f31c86ee62cc721bb58b31c87cd32cc721d794d31c875d534c721bbd8931c86ec624c721f34c931c86ee620c721bb58831c87d5310c721ded4250c867e64943219f59250c867e63943219f58e50c867f64543219f19150c867f63543219f18d50c876e3254321db4c950c86de6314321b758c50c877950143219f98f548867d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548867e60952219f58254886df6355221b718d548873f64552219fd8d548875f635522197d8d548867c6355221d718d548865c6355221dbd89548867f60552219f181548873d5415221cf990548867e63152219f58c548876d6215221dd984548867e60152219f580548867e64d4e219f593538876d62d4e21dd987538867e60d4e219f583538875f5394e219f992538867d6494e219f982538867d6094e219fd91538867c6454e21d7d8d538867f6054e219f181538875d5314e219f990538867d6414e21d798c538876d6214e21dd984538867e6014e219f580538867f65d0e219f997438867d65d0e219f197438875f53d0e21d714f438867f6590e219f996438867d6590e219f19643886ee6290e21bb58a438867f6550e219f995438867d6550e219f19543886ef6250e21bb189438867f6510e219f994438867d6510e219f194438875f5310e21d714c43886f66110e21bd584438873e54d0a21cf55342886f661d0a21bd587428876d65d0a21dbd5342887ae54d0a21db55342887ad54d0a21dbd4f428876d53d0a21f998742886ed61d0a21f958742886de6390a21b758e428873e5450a21cf55142886f76150a21bd18542886ed6510a21db59442887ae6410a21dbd50428876d5410a21dbd4c428876d5310a21bb584428875e53cca21d754f32886f661cca21bd587328875e534ca21d754d32886f7614ca21bd18532887cd320ca21cf952418873d5490621bb98a41886ed6290621b7d8d41886dc6350621bbd8941886ec6250621bed8141886f86050621cf950418873d5410621b
  | 25 => 0x76d52cc831bd987320c6f561cc8319f596320c76d528c8319fd95320c75e534c831db949320c76e520c831db548320c7cd320c831bd984320c6f5610c8319f992510c67d6494431d7d0e510c75c43944319f597410c76e52d0431db54b410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c76e5290431db54a410c67f6550431b7d8d410c6dc6350431bbd89410c6ec6250431db949410c76d5250431bed81410c6f860504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431db948410c76d5210431ed504410c76e52cc431db54b310c6de64cc431b7193310c7ce52cc431d754b310c7cd52cc431d354b310c6dd638c431d794e310c76e528c431db54a310c6f5638c431dd94e310c7d6538c431f5d0e310c7d4438c431f994a310c7e5528c4319fd95310c76e524c431db549310c6df654c431d7d95310c65f654c431b7991310c6dc644c431f3949310c75d524c431f3549310c74d524c431b7d85310c75e514c431f5905310c7d5414c431bdd95310c777654c4319dd95310c6f7634c431f5d8d310c776534c431f594d310c7d6434c431f550d310c7e6524c431f9549310c7d6324c431f50c9310c6ee62d4031bb58b500c76e52d4031db54b500c76e5294031db54a500c77b50940319f992500c67d6494031d7d0e500c75c43940319f98a500c67d6294031db949500c76d52540319fd91500c67c64540319fd89500c67c6254031af990500c6bd6414031bb988500c6ed6214031db948500c76d5214031de540500c6de63d5321b758f54c86fa60d5321be58354c867e63d5321d798f54c865e63d53219f58f54c875d63d53219758f54c876e62d5321dd58754c867e60d5321de98354c867a60d53219f58354c877960d53219e58354c873f54953219f98e54c867d63953219f98254c867d6095321cfd9154c867f63553219f18d54c867f60553219f18154c873d5415321cf99054c867e63153219f58c54c876e6215321dd58454c867e60153219f58054c867e64d4f219f59353c876e62d4f21dd58753c867e60d4f219f58353c875f5394f219f99253c867d6494f21db98a53c867e6094f219f58253c867f6454f219f19153c875f6354f219fd8153c867c6054f21d754c53c86fa6014f21be58053c867e6414f219f59053c875e6314f21db98853c87756114f219f98053c877a6014f219e98053c867d6014f21de58053c86796014f219fd9743c867e65d0f219f59743c867c65d0f21d794f43c875d53d0f219fd9643c867e6590f219f59643c867c6590f21bb98a43c86ed6290f219fd9543c867e6550f219f59543c867c6550f21bdd8543c86f46150f219fd9443c867e6510f219f59443c867c6510f21d794c43c875d5310f21bb98843c86ed6210f21cf952
  | 26 => 0x14c9319f994324c6de630c931f34c8324c67e65d0531cfd53414c73c54d0531b798f414c6dd63d05319f996414c67f65505319f595414c67c6550531cfd51414c73c5450531b7d8d414c6dc6350531bbd89414c6ec6250531bed81414c6f860505319f994414c7d732cc531f54cb314c75e548c531d7152314c6dd628c531f5d46314c67e64d41319f593504c67e62d41319f58b504c75f32d4131d74cb504c77b5094131afd91504c6bc6454131bbd89504c6ec6254131de540504c67e64141319f590504c67e62141319f588504c6ee62d5031bb58b540c67e63d5031d798f540c67e62d5031db98b540c66e62d50319f58b540c76d62d50319b58b540c67e61d5031dd987540c67e60d50319f583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c73f6455031d718d540c67f62550319f189540c67f60550319f181540c73d5415031bb988540c6ed6215031be980540c6f960150319f990540c73e64150319f98c540c75e63150319f988540c76e62150319b988540c67d6215031db588540c66d62150319f984540c77661150319f980540c77a60150319e980540c67d6015031de580540c67960150319f992530c67d6494c319f597430c6dd65d0c31d7597430c75f54d0c31d7553430c6dd61d0c319fd96430c67d6590c31cf952430c73d5490c31b798e430c6ee6290c31bb58a430c6f66190c31bd586430c67f6550c319fd94430c67d6510c31cf950430c73d5410c31bd984430c6f56110c31d7594430c65d6510c31b7990430c79e6410c31d7d50430c79e5410c31d7550430c79d5410c31f5984430c6dd6110c31f5584430c6d56110c31dbd4a520c67e64948319f592520c67e60948319f582520c76f5494831db952520c76d5494831db152520c7cf4394831f310e520c76f6494831db992520c76d6494831db192520c76c6394831dbd0e520c76e4394831db50e520c76c4394831db986520c76c6194831dbd82520c76e6094831db582520c76c60948319fd91520c67c6454831d7d0d520c75c43548319fd81520c67c6054831dbd95520c76f5454831db951520c76d5454831db151520c7cf4354831f310d520c76f6454831db991520c76d6454831db191520c76e6354831dbd0d520c74f4354831db90d520c76d4354831db10d520c74c4354831db985520c76c6154831db0c5520c76f6054831db981520c76d6054831db181520c6ee6214831db548520c67f65d08319f997420c67d65d0831db94b420c76d52d08319fd96420c67e65908319f596420c6de6390831b758e420c76e5290831db54a420c67f65508319f595420c67c6550831b7d8d420c6dc6350831db949420c76d5250831bdd85420c6f461508319fd94420c67e65108319f594420c76e5210831db548420c75e53cc831db94b320c
  | 27 => 0x31e7953438c75d54d0e31e7553438c7d661d0e31b7587438c7d561d0e31bb98a438c6ed6290e31cf951438c73d5450e31bdd85438c6f46150e31b7594438c75d6510e31e7990438c75f5410e31d7550438c6dd6110e31dbd4a528c67e6494a319f592528c67e6094a319f582528c67f6454a319f191528c75f4354a31d710d528c67f6054a319f181528c76d5214a319fd97428c67e65d0a319f597428c67f6590a319f996428c67d6590a31b798e428c6dd6390a319fd95428c67d6550a319f195428c6df6350a31b718d428c67f6510a319f994428c67d6510a31bd984428c6f56110a31db94a328c76d528ca31bd986328c6f5618ca31db949328c76d524ca31bdd85328c6f4614ca31f34c8328c73e5490631cf552418c6de6390631b758e418c6df6350631b718d418c6ef6250631bb189418c6fb6050631be181418c73e5410631cf550418c6de6310631b758c418c6dd65cc631d7597318c6de64cc631b7193318c75d52cc631bd597318c77565cc631ded42508c67e64942319f592508c75f4394231d710e508c67e62942319f58a508c67f64542319f191508c67f62542319f189508c77950142319f98b544c67d62d51319f983544c67d60d5131cfd52544c67e64951319f58e544c75d63951319f98a544c67d62951319f586544c77561951319f982544c67d6095131bbd89544c6ec6255131bed81544c6f86055131cfd91544c67f6355131d7d8d544c65f63551319fd89544c76f62551319bd89544c67c6255131db189544c66c62551319fd85544c77761551319fd81544c77b60551319ed81544c67c6055131de181544c67860551319f994544c73d5415131cf990544c67e62151319f588544c67e60151319f580544c67e65d0d31cfd53434c73c54d0d31bd987434c6f561d0d319f996434c6ee6290d31bb58a434c67c6550d31cfd51434c73c5450d31bdd85434c6f46150d319f994434c67e64d49319f593524c67e60d49319f583524c76f5294931afd91524c6bc6454931bed81524c6f86054931db548524c67e64149319f590524c67e60149319f580524c67e65d09319f597424c67c65d0931dbd4b424c76c52d09319f996424c67d65909319f196424c73f5490931cf152424c6de6390931b758e424c67f65509319f995424c67c65509319f994424c67d65109319f194424c73f5410931cf150424c6de6310931b758c424c76f5210931db148424c6f66110931bd584424c67e65cc931b7997324c75e65cc931d7953324c75c54cc931d714b324c6de61cc931b758e324c76f528c931db14a324c6f6618c931bd586324c76f524c931db149324c6f7614c931bd185324c75e544c931d7151324c7cf624c931f3d49324c75c524c931f3149324c74c524c931f3d09324c7cc424c931f5d85324c6dc614c931f5185324c6d46
  | 28 => 0xd95411073f65504418fd95411079f6350441e718d41107af6250441eb18941106bf6150441cf94541107bb6050441ee18141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441f5d8d41107d46350441ed90d41107b44350441f9d8941107e46250441ed90941107b44250441fcd8141106f46050441fc18141106f06050441ded42501067e63940419f58e501067e62940419f58a501067f63540419f18d501067f62540419f18950106de6314041b758c50106ee6214041bb58850107795014041bb98b54cc6ed62d5331be98354cc6f960d5331d798f54cc67e62d5331db98b54cc66e62d53319f58b54cc76d62d53319b58b54cc77561d53319f98354cc77a60d53319e98354cc67d60d5331de58354cc67960d5331cfd5254cc67e62953319f58a54cc67e60953319f58254cc73f64553319fd8954cc67c62553319fd8154cc67c6055331cf55054cc73e6415331d798c54cc67e62153319f58854cc77561153319f98054cc67d6015331cf95243cc73d5490f31bb98a43cc6ed6290f31bd98643cc6f56190f31cf95043cc73d5410f31bd98443cc6f56110f31dbd4a52cc67e6494b319f59252cc67e6094b319f58252cc67f6454b319f19152cc67f6054b319f18152cc76d5214b31be98052cc6f96014b319fd9742cc67e65d0b319f59742cc76e52d0b31db54b42cc67f6590b319f99642cc67d6590b31b798e42cc6dd6390b319fd9542cc67d6550b319f19542cc6f76150b31bd18542cc67f6510b319f99442cc67d6510b31b798c42cc6dd6310b31db94842cc76d5210b31db94b32cc76d52ccb31bd98732cc6f561ccb31d795332cc75c54ccb31d794b32cc7ce52ccb31f354b32cc6de61ccb31f598732cc7d561ccb31b7d9532cc75f654cb31d795132cc75c544cb31f3d8932cc7cf524cb31d794932cc7cc524cb31f3d0932cc7cc424cb31b718532cc76e520cb31db54832cc7cd320cb31bd98432cc6f5610cb31cf95341cc73d54d0731b798f41cc6dd63d0731cf95141cc73d5450731b7d8d41cc6dc6350731bbd8941cc6ec6250731bed8141cc6f86050731ed50441cc77b50943319f99250cc67d64943319f98a50cc67d62943319fd9150cc67c64543319fd8950cc67c6254331d7cc950cc75d3254331bb98850cc6ed6214331de54050cc75d63d52319f98b548c67d62d5231dd987548c67e60d52319f583548c73f54952319f98a548c67d62952319f982548c67d6095231bbd89548c6ec6255231cfd91548c75f63552319fd89548c76f62552319bd89548c67c6255231db189548c66c62552319fd81548c67c6055231cf550548c73e6415231d758c548c67e62152319f588548c77661152319f980548c67d6015231cf953438c73d54d0e31bd987438c6f561d0e31d7597438c75f54d0e
  | 29 => 0x1507ac5290541edd46415075f53d4141d714f505076f52d4141db14b505067e63d41419f58f505067e62d41419f58b505077b53d4141f6d4f505075b53d4141de94f505077953d4141de14f50507d853d4141d614f505077b52d4141fad4b505076b52d4141de94b505077952d4141de14b50507e852d4141da14b50507f341d4141ee907505077b64d4141ded8f505077a63d4141de58f505077863d4141ded0f505077a43d4141de50f505077843d4141ded8b505077a62d4141de58b505077862d4141ded0b505077a42d4141de50b505077842d4141deccb505077a32d4141de4cb505077832d4141ded87505077b41d4141de90750506de6394141b758e505075f5394141d714e50506ee6294141bb58a505076f5294141db14a505077b5094141b7d8d50506dc6354141d7d4d505075c5354141bbd8950506ec6254141dbd49505076c5254141d7d4c505075c5314141dbd48505076c5214141de540505067e63141419f58c505067e62141419f58850507774114141be994505077a6514141ded4c50507db5314141d6d4c505077a5314141de54c50507785314141f614c50507585314141ded4850507eb5214141dad48505077a5214141de54850507785214141fa14850507685214141fcd0450507ba4114141ded90505077b6314141de98c50507796314141de18c505077b4314141de90c50507794314141de10c505077b6214141de98850507796214141de188505077b4214141de90850507794214141de108505077b3214141de8c850507793214141de0c8505077b6114141ded0450507734114141de90450507794114141d7d4e531067e6294c419f58a531067e6094c419f582531067f6254c419f189531067f6054c419f181531075d5314c41bb98853106ed6214c41be98053106f96014c41d794f431075d53d0c41bd98743106f561d0c419f59643106ee6290c41bb58a431067f6550c41d794c431075d5310c41bd98443106f56110c41dbd4a521067e63948419f58e521067e60948419f582521067f63548419f18d521067f60548419f18152106de6314841b758c521076d5214841be98052106f96014841db94b421076d52d0841bd98742106f561d08419f59642106de6390841b758e421067f6550841db948421076d5210841bd98442106f561108419fd97321067e65cc8419f597321075e53cc841d754f321067f658c8419f996321067d658c841db94a321076d528c8419fd95321067d654c8419f19532106bf644c841af191321075e534c841d754d321076e524c841db54932106f7614c841bd185321067f650c8419f994321067d650c841f34c832106bd6490441cf95241106f56490441dd95241107b65490441bd982411067f6550441b7d8d41106dc6350441bbd8941106ec6250441bed8141106f86050441af
  | 30 => 0x7565d0641b798f50906dd63d4241bb98b50906ed62d4241ded42509067e63942419f58e509067e62942419f58a509077741942419fd8d509067c63542419fd89509067c6254241de540509067e62d4d419f58b535067e60d4d419f583535075f64d4d41d7d8b535075e62d4d41d758b535075c62d4d41d7d87535075d61d4d41d7d83535075e60d4d41d7583535075c60d4d41d7d4e53506ee6294d41bb58a53506fa6094d41be58253506ef6254d41bb18953506fb6054d41be181535075d5314d419f988535067d6214d419f980535067d6014d41b7994535075e6514d41d7d90535075f6214d41d7988535075d6214d41d7188535075f6114d41d7584535075d4114d41d7d80535075e6014d41d7580535075c6014d419f997435075c53d0d41d7d4e435075c5390d41bb98a43506ed6290d41bd98643506f56190d41d7d4d435075c5350d41bdd8543506f46150d419f994435075f5310d41d7d4f525075c53d49419f98f525067d63d49419f983525067d60d4941dbd4f52507cf53d4941d3d4f525076e53d4941db54f525076c53d4941f314f525074c53d4941dbd93525076f63d4941db98f525076d63d4941db18f525076f43d4941db90f525076d43d4941db10f525076f61d4941db587525076f60d4941db983525076d60d4941db18352506de6394941b758e525075f5394941d714e525076f5294941be98252506f96094941b7d8d52506dc6354941d7d4d525075c5354941bed8152506f86054941d7d4c525075c5314941db548525067e63149419f58c525067e60149419f58052506ee6514941db994525076f5314941f3d4c525074f5314941db94c525076d5314941db14c52507cc5314941d314c525076f6414941dbd8c525076e6314941db58c525076c6314941dbd0c525076e4314941db50c525076c4314941dbd84525076d6114941db504525076f6014941db980525076d6014941db180525067e65d0941d7d4f425075c53d0941db14b42506de6390941b758e425075f5390941d714e425076f5290941db14a42506f66190941bd586425075f5350941d714d425076f5250941db14942506f76150941bd185425067e6510941d7d4c425075c5310941dbd48425067e65cc9419f597325067c65cc941d7d4f325075c53cc941dbd4b325076c52cc9419f996325067d658c9419f196325075f538c941d714e325076f528c941db14a325067f654c9419f995325067c654c941d7d4d325075c534c941dbd49325076c524c9419f994325067d650c9419f194325075f530c941d714c325076f520c941db14832507cd320c941bd98432506f5610c941d7d4f415075c53d0541dbd4b415076c52d0541f5d4f41507d453d0541f9d4b41507e452d0541d7d4e415075c5390541dbd4a415076c5290541e7d4e415079c5390541ebd4a4
  | 31 => 0x4c832f390d320cbcd434c832f310d320cbcf654c832b3d95320cb4f654c832f3d91320cbce644c832f3591320cbcc644c832f3d51320cbce544c832d3951320cbcd544c832f3151320cb4c544c832f3d85320cbce614c832f3585320cbcc614c832f3d81320cbce604c832f3581320cbcc604c832f34cb510cafa60d4432be583510cbcd3294432ddd46510ca7e64944329f592510ca7e60944329f582510cbcd32544329fd91510ca7c6454432d7cc9510cb6e3254432d74c9510cb6d3254432d34c9510ca7f60544329f181510cbcd3214432dd544510cbcd32d4032bd987500caf561d4032f34ca500cb7b50940329f992500ca7d64940329f986500ca7d6194032f34c9500ca7f64540329f191500cb5f3254032db8c9500cb5d3254032db4c9500cb4d32540329fd85500ca7c6154032f34c8500cb795014032d7d4e53d06ee6294f41bb58a53d067e6294f41db98a53d066e6294f419f58a53d076d6294f419b58a53d067e6094f419f58253d067f6254f419f18953d067f6054f419f18153d075d5314f41d794f43d075d53d0f41bd98743d06f561d0f41bb98a43d06ed6290f41d794c43d075d5310f41bd98443d06f56110f41b798e52d06dd6394b41dbd4a52d067e6394b41d798e52d065e6394b419f58e52d075d6394b419758e52d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41b798e42d06dd6390b41db94842d076d5210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d067f658cb419f99632d067d658cb419fd9532d067d654cb419f19532d06f7614cb41bd18532d067f650cb419f99432d067d650cb41f34c832d077b50943419f98e50d067d63943419f98a50d067d62943419fd8d50d067c63543419fd8950d067c6254341de54050d075f5394e419f98a539067d6294e419f982539067d6094e419fd89539067c6254e419fd81539067c6054e41d754c53906ee6214e41bb588539075e5390e41d754e43906ee6290e41bb58a43906f66190e41bd586439075e5350e41d754d43906f76150e41bd185439076f5294a419f98e529067d6394a419f982529067d6094a419fd8d529067c6354a419fd81529067c6054a41b798c52906dd6314a41db54852906de6390a41b758e429076e5290a41db54a42906f66190a41bd586429076e5250a41db54942906f76150a41bd185429067f65cca419f997329067d65cca41d794f329075d53cca419fd96329067e658ca419f596329076e528ca41db54a329067f654ca419f595329067c654ca41afd9132906bc644ca41d794d329075d534ca41db949329076d524ca419fd94329067e650ca419f59432907cd320ca41bd98432906f5610ca41af597419073d65d0641bd59741907
  | 32 => 0x2d7550434cbcf6210d32b7988434cbcc6210d32b7584434cadd6010d329f997424cb3f54d0932cf153424cade63d0932b758f424caee65d0932db997424ca6e65d0932dbd53424cbaf54d0932db553424cbac54d0932bb98f424cbce63d0932b398f424cbcd63d0932f3d0f424cbcc43d0932bb587424caed60d09329f996424cade6390932b758e424caee62909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424ca7e6510932bb994424cb6e6510932bb990424cbae6410932dbd50424cb6d5410932f3d8c424caee6310932f318c424cbcf4310932f310c424caed6110932bb580424caee64cc932bb193324cbcf43cc932f310f324caed61cc932bb583324cade648c932b7192324cbcf528c932f3d0a324cbcc428c932b7586324cadd608c9329f993514ca7d64d45329f983514ca7d60d4532ddd46514cabf6454532af191514cafb6054532be181514cb7551145329f990514ca7d6414532d7d0c514cb5c4314532dbd08514cb6c42145329f980514ca7d60145329f993504ca7d64d41329f987504ca7d61d4132ded42504cabf6454132af191504caf76154132bd185504cb7950141329f990504ca7d6414132d7d0c504cb5c4314132dbd08504cb6c42141329f984504ca7d61141329f98f540cb5e63d50329798f540ca7e62d5032db98b540ca6e62d50329f987540ca7d61d50329f983540ca7d60d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3d5415032bd984540caf56115032be980540caf960150329f990540cb3e64150329f98c540cb5e63150329f988540cb6e62150329f984540cb7661150329d984540ca7d6115032dd584540ca7561150329f980540cb7a60150329e980540ca7d6015032de580540ca7960150329f992530ca7d6494c329f597430cb5e53d0c329fd96430ca7d6590c32cf952430cb3d5490c32bb98a430caed6290c329fd95430ca7f6510c329f594430cb3e5410c32cf550430cb5e5310c32e750c430caee6210c32bb588430ca7e64948329f592520ca7d65d0832db94b420ca7f65908329f596420cb3e5490832cf552420cade6390832b758e420ca7f65508329fd94420ca7e65108329f594420ca7c6510832cf950420cb3d5410832b798c420cadd6310832db948420cbad4210832d7953320cb5c54cc832b758e320cb5e538c832db952320cb6c548c832bb58e320cacd638c832db94e320cbce538c8329fd95320cadf654c832d7d95320ca5f654c832d7951320cb5c544c832b7d89320cb5e524c832f3d09320cbce424c832f3509320cbcc424c832bbd95320cb6f654c8329bd95320cb6e544c832db151320caef634c832f3d8d320cb6e534c832f394d320cbcf43
  | 33 => 0x5043ccb1d5410f32b798843ccbce6210f32f358843ccadd6110f32b758043ccb3e54d0b32cf55342ccade63d0b32b758f42ccade6390b32b758e42ccb3e5450b32cf55142ccadf6350b32b718d42ccbad4210b32ddd4651cca7e64947329f59251ccb5f4394732d710e51cca7e60947329f58251cca7f64547329f19151cca7f60547329f18151ccb755114732ded4250cca7e64943329f59250ccb5f4394332d710e50cca7e61943329f58650cca7f64543329f19150cca7f61543329f18550ccb795014332d758f548cb6e62d52329f987548ca7d61d52329f983548ca7d60d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f6455232db189548ca7f61552329f185548ca7f60552329f181548cb3d5415232cf990548cb5d6315232db988548ca7e61152329f584548ca7e60152329f580548cb3e54d0e32cf553438caee62d0e32bb58b438caed6290e32cf951438cb3d5450e32bbd89438caec6250e32e750c438caed65d0a32db597428cb6f54d0a32db553428caee63d0a32bb587428caed60d0a32cf952428cb3d5490a32b798e428cadd6390a32cf950428cb3d5410a32b798c428cadd6310a32bb594428cb6d6510a32eb990428cb6f5410a32eb950428cb6d5410a32eb550428cb2d5410a32bb98c428cbce6310a32f358c428caed6110a32bb580428cadd65cca32d7597328cb5e54cca32d7153328caed65cca32db597328caee64cca32bb193328caed61cca32bb583328cb7751946329f992518ca7d6494632dbd0a518cb6c42946329f982518ca7d60946329fd91518ca7c6454632d7cc9518ca7f60546329f181518cb755114632ded42508ca7e64942329f592508cb6f4294232db10a508ca7e61942329f586508ca7f64542329f191508cb5f32542329fd85508ca7c6154232de540508cb5d63d5132db58b544ca7e61d51329f587544ca7e60d51329f583544cb3f54951329f992544ca7d6395132d758e544ca7d6295132db58a544ca7e61951329f586544ca7e60951329f582544caf76155132bd185544cafb6055132be181544cb3f64551329fd8d544cb5f63551329fd89544cb6f62551329fd85544cb7761551329dd85544ca7c6155132dd185544ca7461551329fd81544cb7b60551329ed81544ca7c6055132de181544ca7860551329f994544cb3d5415132cf990544ca7e61151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d32d7997434ca5e65d0d32d7d53434cb9f54d0d32d7553434cb9c54d0d32b798b434cbce62d0d32b398b434cbcd62d0d32b7587434cadd60d0d329f996434cade6390d32bb98a434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d329f994434cade6510d32d7994434cade6410d32e7990434cb5f5410d3
  | 34 => 0x90b5d53d4242bd9875090af561d4242d794e5090b5d5394242ded425090a7e63942429f58e5090b6f42942429f9865090a7d6194242d794d5090b5d53542429fd8d5090a7c63542429fd855090a7c6154242b798c5090add6314242d794c5090b5d5314242de5405090a7e61d4d429f5875350a7e60d4d429f5835350b5f5394d42bdd855350af46154d42bed815350af86054d42d754c5350a7e6114d429f5845350a7e6014d429f5805350a7e65d0d42d7d4e4350b5c5390d42bb98a4350aed6290d42d7d4d4350b5c5350d42bbd894350aec6250d429f9944350b6f53d0942b798e4250add6390942e798e4250b9d6390942ebd4a4250a7e63d45429f58f5150a7e60d45429f5835150b775194542b7d8d5150adc6354542bed815150af86054542dd5445150a7e63145429f58c5150b6f42145429f9805150a7d60145429f98f5050a7d63d41429f9875050a7d61d4142ded425050adf6354142b718d5050af76154142bd1855050b7950141429f98c5050a7d6314142dbd085050a7e61141429f5845050b5f5394c42db98a5310a7e6194c429f5865310a7e6094c429f5825310a7f6154c429f1855310a7f6054c429f1815310b5d5314c42bd9845310af56114c42be9805310af96014c42d794f4310b5d53d0c42bb98b4310aed62d0c429f5964310aed6290c429fd954310b5e5310c42d754c4310b9d4310c42bb9884310aed6210c42d798e5210b5d6394842af5924210b3e5490842b798e4210add6390842bb5924210b6e5490842eb9524210bce6390842bb58e4210bcd6390842b358e4210aee6190842bb9824210a7f6550842afd954210b3f65508428fd954210abf6250842cf9494210aef6550842dbd954210a6f6550842bbd914210baf6450842db9514210bae5450842bbd8d4210bae4350842eb10d4210aec6150842bb1814210b7751944429f98e5110a7d63944429f9825110a7d60944429fd8d5110a7c63544429fd815110a7c6054442b798c5110add6314442dd5445110afa6014442be5805110b7b50940429f98e5010a7d63940429f9865010a7d61940429fd8d5010a7c63540429fd855010a7c6154042b798c5010add6314042bd9845010af56114042de5405010b5e63d5332db58b54cca7e61d53329f58754cca7e60d53329f58354ccb3f54953329f98654cca7d61953329f98254cca7d6095332cfd9154ccb5c63553329fd8554cca7c61553329fd8154cca7c6055332cf55054ccb3e6415332d798c54ccb6d62153329f98454cca7d61153329f98054cca7d6015332b759743ccb5d65d0f32d7d5343ccb5d54d0f32b798b43ccadd61d0f32b758343ccb3e5490f32cf55243ccaee6290f32bb58a43ccb3e5410f32cf55043ccaee6210f32bb58843ccb5d6510f32e799043ccb5f5410f32e795043ccb5d5410f32e75
  | 35 => 0xe62145439f5885150e7e60145439f5805150e7e62d41439f58b5050e7e61d41439f5875050f7b5094143bbd895050eec6254143bdd855050ef46154143de5405050f5f43141439f9885050e7d62141439f9845050e7d6114143db98a5310f6d6294c43af5924310f3e5490c43bb98a4310eed6290c43b75924310f5e5490c43e79524310fce6290c43b758a4310fcd6290c43b358a4310ede6190c43b79824310e7f6550c43afd954310f3f6550c438fd954310ebf6350c43cf94d4310edf6550c43d7d954310e5f6550c43b7d914310f9f6450c43d79514310f9e5450c43b7d894310edc6150c43b71814310f6f52948439f9865210e7d61948439f9825210e7d60948439fd855210e7c61548439fd815210e7c6054843db5485210ef66114843bd5845210efa6014843be5805210f7751944439f98a5110e7d62944439f9825110e7d60944439fd895110e7c62544439fd815110e7c6054443bb9885110eed6214443dd5445110efa6014443be5805110f7b50940439f98a5010e7d62940439f9865010e7d61940439fd895010e7c62540439fd855010e7c6154043bb9885010eed6214043bd9845010ef56114043de5405010f5f5394f42db58a53d0a7e6194f429f58653d0a7e6094f429f58253d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42d794f43d0b5d53d0f42bb98b43d0aed62d0f42bb98a43d0b5e5310f42d754c43d0aee6210f42bb58843d0b7751947429f98e51d0a7d63947429f98251d0a7d60947429fd8d51d0a7c63547429fd8151d0a7c6054742dd54451d0b7b50943429f98e50d0a7d63943429f98650d0a7d61943429fd8d50d0a7c63543429fd8550d0a7c6154342de54050d0b5f5394e429f9865390a7d6194e429f9825390a7d6094e42d7d925390b5e6294e42d718a5390b5f6194e42d79865390b5d6194e42d71865390b5f6094e42d79825390b5d6094e42d71825390a7f6154e429f1855390a7f6054e429f1815390b5f6554e42d75915390b5e6254e42d71895390b5f6154e42d79855390b5d6154e42d71855390b5f6054e42d79815390b5d6054e42d71815390b5d5314e42d794f4390b5e5390e42d754e4390aee6290e42bb58a4390b5e5350e42d754d4390aef6250e42bb1894390b5d5310e42e750c4390b5e53d0a42d754f4290abd65d0a42cf5974290b9e53d0a42e754f4290aed65d0a42db5974290bce53d0a42db54f4290bcd53d0a42d354f4290ade63d4642b758f5190b5e53d4642d754f5190afa60d4642be5835190b5e5394642d754e5190b7751946429f98e5190a7d6394642dbd0a5190a7e60946429f5825190b5e5354642d754d5190a7f63546429f18d5190a7f60546429f1815190ade6314642b758c5190b5e5314642d754c5190b755114642b798f5090add63d4242d794f50
  | 36 => 0x8001000400100340040004000001400b0000029001002a000000e003c00400840030018001001c00700000030000004000400d0004000000004f00500220060006006c005000c00200080090014000004000c00080030064004001000b00680000004005000800000c0017000800b000c00000040020010000002c0010000008003400100080050028000000c0360020000004000100200000014004000400000300030000000001401b002401a000001d0018004000000000000080098008001400d0080004000000300040010010005000400400000000000001000800b000000300a400900180120000009000000000700030008002000c005001800f0008003000c002001c0000000008000801b000000f000000a000000100000040058000000b6f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0f7b50943439f98a50d0e7d62943439f98650d0e7d61943439fd8950d0e7c62543439fd8550d0e7c6154343de54050d0ebd65d0e43cf5974390edd65d0e43d75974390f6f5294a439f9865290e7d6194a439f9825290e7d6094a43ebd0e5290fcf4394a43dbd925290f6c6394a43dbd0e5290f6f6194a43db9865290f6d6194a43db1865290f6f6094a43db9825290f6d6094a43db1825290f5f4354a439fd855290e7c6154a439fd815290e7c6054a43dbd955290faf4354a43f3d0d5290f6d6454a43db98d5290f6f4354a43d3d0d5290f6f6154a43db9855290f6d6154a43db1855290f6f6054a43db9815290f6d6054a43db1815290f6d5214a43bb98b5190eed62d4643db94b5190f6d52d4643be9835190ef960d4643db94a5190f6d5294643ddd465190f5f43946439f98a5190e7d62946439f9825190e7d6094643db9495190f6d52546439fd895190e7c62546439fd815190e7c6054643bb9885190eed6214643db9485190f6d5214643dd5445190eee62d4243bb58b5090f6e52d4243db54b5090ef661d4243bd5875090f6e5294243db54a5090f7b5094243d7d0e5090e7e62942439f58a5090e7e61942439f5865090f6e5254243db5495090e7f62542439f1895090e7f61542439f1855090eee6214243bb5885090f6e5214243db5485090f795014243bb98a4350eed6290d43e7d4e4350fae6290d43eb58a4350f5f43d49439f9875250e7d61d49439f9835250e7d60d4943dbd4a5250ef76154943bd1855250efb6054943be1815250f6d52149439f9845250e7d61149439f9805250e7d60149439f98b5150e7d62d45439f9835150e7d60d4543ddd465150eef6254543bb1895150efb6054543be1815150f755114543d7d0c5150e7
  | 37 => 0x10002c00a0014001000c00700500000008005000000f001c010010c01e000800900000000000003002400e01140000000007002c001003c003001000c008c000002c0000014002000806600000010020001002400000280050060004000004400a40090000000000c01a001c010000c007003c001002800100640260010000000000e00080060024005000000e000c000000000600180110000006001c0000000003008c0240004008001c024000c00000040040000007000c00200400030030001000c0100054002003800100000010004004000c010000c00d0000011000000100000010000000000800f0000000000000100340000038020000000100b800100040000000003003c0020028000001000c003000300140050070085000c0190034035000400300040050024003000800600a4000000401600040060074001001002000c4009009c0050024001005c0020060000000c00b0004003003802f0018007000c01a005c00101680000000000000802a0004009011800900000030010018000c00000080000010052005c003000c00100fc000000c00500380080074000000000700000020000006002000100000030040028000001f000000300000000000003003003f002c000000c007000400700480040034017000c0000000002000808300080020018009000400300080160008004003001e000400d0000009002001e0024002001800000340000084008001800a0040003000c013000000e00000070018000000003a0070000008400b00d800900480000000005000801900680060000002002000100000000060000001c00000380010000002000c0000004053000800f001400100040030014000000c002003800e000000300040020100002000c00800000070014000006800200340010024000003004a0014006005001000ac054003c00100300000018002000000e001800000500000018000002c005000000500300080054009004c0180008000000c001000802300240010008002002400b00000000028000003c0010004005007800c003401000880000014005000400100140140020000000c00100440020010000000400e00080060024007002c03b0020005001000000380000060003000000d0030006000c000003800100000040020005002c028001c000000c00d000800000100010000000000c00c0008006000000200b4031001000200000020000001000000100100010034029000802f004c004000c00a008402b000c011000c00200080100020005000c000001c00500040000004008000000c000c0000020004001400300000070020011006c00e001800600d8000000c00d0068000001003f001c00c00080010028002000c0090000002001001e00080000000015000000a001800300fc00d001c00a00140030
  | 38 => 0x1c001008800600340130000004000c000002800a0024035000c00200000050008001002400000440140000000000800800040030018001000c001000000400080000000002008c00000000160004000000c01f001c0130004001000000000240000004078003c0040008000000400d000c00000340280004029000000100300030030002005c007000000000a405900400020000000001000400080000008004001c004001000000100000000014000800700440170004003001c001006c00f00400140008046000c000004400500280050004001000c0100004012002c0000018002000c001007c007000c0050004001002000000000030034003000c0140080001005c00c00080000000000000000f000000f0000002000001101c0003002000100040030000000000c00c00140060004000001801a0034014000c00300000000004003003c004003c01300000020004000001801b00040040008021002c00200b0000001c004000000100c4015000000000100030000005003c000007c0000000000000400000240030000014000000000180010030005003800600900020008000008c0030018006000000000040050004004001c00000480170024000000000b0010001000000c00100070000002000000e000000200ac0010020000000000300100000018005003c000001c00000000090020003000000100180010004002000000e001c006001c00200440000000002002000401d8002000c0110004000001c02e001802e000800600000110004001001c007000c006002000300000060018003000000600080000020001000000800080030014027002c007002000a002c001000800a00000000004000005c0060078003000001b0030006001c0200000008001c049005800e00ac0000054012001000f000000000bc01e0000004012000a000c00c00e000c00000000008012000000201040020004006009403c00dc0090038005001000400000070004000000000f00100020004000000000000100030014001006400700040040024000000c005005c00000000030004019000800000040020060000004001600440080050005000400700040050010000004c0000024000001800500180060000009007c00c00080040024001001400d000000000e800000200000004040007c01000000010058000000000200240010088002006c000000000e00000180014008001000200040000028002008c00000100040044007000001000000060000000000400e002000200440010008003000c0010000017001800200740000008001000000400bc00500200000000000000c0030018001000000000a80000008000000000000a00070030005001001f0008008002c00000100040004000002c000001c017000800200200090000000016c00d0018
  | 39 => 0x8001000000e002c00000400040014000000801300000050078000002c00d0008004006800200200000000010000000d0008005001001a00000030004006001000a00100050020002003c027002000500840090060002002800c0010003000000e00200000008009000800900040170000002001c00400080090040006000400a0000024004400d00180150114004005c005000c000000c00700040060004018003800000000020030002004400b0008016000800000440010044007000c003000400f0004000001800000480150000000002800300c8004000800000040010000001003400000080000024004000004300280000000001000400800040040010001008c000000400d0008000001402f00b80020000000000000500000000008002002c000001800e000800800000010004006007400000f800400100000098000001c00200fc0030030008005000a00d0008000000e0020014000400100180000010006000c007008800f01480060000007002800000000240034000000800100480010004019001c0040004009000c01700000290010001003c01a0074001021c009001c00e00e40000014008000000300700120000010001c00b0018004000400d0000001000000a00440030048000000401f002000e00000020044006001c00700000030010000003c0040010008000c002000c0020000001000400400140090020000000400a00000000054036003000000080020000005009c0020024000002c00e00940000010000000000000040010014000002400000700150000000001400100b801a0058007000000b0018000000000100080070000009002c000002c00e001800e0000001002000500140000014011000800400900120004004000000e002c000003801c0000002002400000100000000011002c001000400900240010038005006401000000050000009000000000040010000000003c00000000280010000006000100a80000014000000800e000400c0024004000402000100010000006009403700740030000000000400d00000010000000002c001001800b00540000000003003800a0040001003800200500040014004004800200280210010000001800500080020004004003c000004403d00000190004000004400200400040080000001405100280120054017001000000100110000006001c00b00080000008000001800d0148017000000e0008022001c0010008003001c0000030002002800e000c004003403500080040004000003400000300060000005000800200180010014004007400a002400200200030000000004405c005c002000c00000000000050006000400c000c00000140040034015001403a0004013000400f00140090008011000000400000010030006000c023000000400200000008010
  | 40 => 0x1001401f0004009005400600340000000025000801800200030020003000000300500000010002002c000002c00100140010038002001c022000001a000c0010018000006c00800500160000007000c002007c000003c02d0040004000800800100080004001002c005000401900540030020000000000500680000004000001400001340000078000007000101c400501e0004006c0200000002002000300000050008004006c00700a0012005803f0008006002c0000074011000002100100100034004005400d00000000028005000000400380060008009000400d00040570038005000000100100590044000000c00000040000004003000400000180000000007003001d00200220008008000001400e0013000c000001800000080010184000000c0010000003000400d000000d00000050010008000800100100000004001001c018003000900180020000000000000200000000054007009c004000003d00180170004000000c0010004008002001400000000044009005c00000040040044037000c0030020001000000b0008000000000000080000010003000400000000060004001000c0000018000000801e0024001001c0090004004000800b002400400100000050005000c00e000000300080010000000002c0060004000001000f001400000300070020002002c00000000130004021008c001000000b0008000000000300080040010019003c0060000005000000300f801a014400300080060004003004c002004c00a004c0080000010001001d002000000b00000050001003c002000400500d0000000000100000150004003000c016002000300000000008008000800300000110010006000400100080000000007000000900080140064000000000700240040000005001c075000400e00680100000003001000000100020008009000800000080000000005005000200cc000000000100000060098004000c010001000a003800000c0001000401f001c008002400c00080010020001005c000000001f00bc01b0000001000000500000020004001000000b0010006000c000006001d00e800e00200000004012001c0130004008002c005000401d0000015001000000080040000002009400100100080044003000800000880470000001007402100180080040000000000d00080040010000000c00600780040060000002800600000130010000005000000140210028013000c000001c0050064005002000f00000220040000004c00e0094015025802000e800e00000070000012000401100100070000000001c0030004056001400c0014007000c003003400100040c8004800100040060000000003c00100240070000003000c00400200080000001000c0080004002005400a0020000000001b011801d001401a001
  | 41 => 0x51fda7690000b0d096691c80001d91ad8f1c1f4801a2a3aa8483628cd073e0f6979882135f8000000000032260003a6a3aeacd60e0b812000013c0c2151a37192062bc800084200000630bdc0122ef64f20a9c0c4a70630e092e018a92469725ca4cd1c5459db4369b800009a38000000177400000008672b2e82b821a16e8000ca300000000eda57a25500ff00005dd8000000216af230cf861c17380000a5c1530ffcf350322cef195ea1395d6c6612d2250a4b0acd1da84c8a11a0001b50cda911403ba4c40001db8cb104fadd70000d1b066260a917682c2256f4e80000b6170e000000005727248db39f8000005e00000003d08000c852ebea7a95180000000bb328a007200007c42cd26168000a71817c00014ca0000000d81000078300001b780003db18720001654000000038bb38e0000000a5bb0668a62b380000a8213d2a720000df2e8e1e52adf0064af083980000000658b8c0000278ef1335a6972308800011460000000cf81658c0029a6000046000015aa59b800009b0f908263dc800001c619133ae3631ef60539128cdea49e832b744f72b5d86af11486c7800019f8000ad616266f18050ac01c52d30223e286800020b9e62e8f0000aa180000f2b6b800020944df3bc6066bb98e8cb49e15a1a4ad7b2db60000eec772ac809b2990e68c2c3627c00000000000c14963cb4c87acce5354436e0d28be61db60000ac84b82046320000019b9e80777b7c4000000076a800025ea31a52fbbcc00026064f287721049d40a3111ae336000000504ee00036d40a230cc04a85d62b4a47e2cba9c0aa28ad400015f80000f6a9342742e1600009023650573acb60000e1a0000d3a0003530cf63b94d10aeece382512000000047b800000015c889b16326da1d16904800000024188fcb4dc108adea208000025ba686000298e89c22c8130ab0a03e2784e6532f6e0688aa9d5bc84ccb9166cec90f000018ba00024ca097bab00d80f9e1afbba8c07224c6b022003538000af2ac6c96535621fa96b600792a029c0510274236e57c80002e68000e77914c7c5bc98248279cb9599de2d018d2391097ce22b11256097f6c23804213c1bac56b93261e300000040001000800200a4000002802700000000050008001400d0030058002c000006c00300dc001000000000140020010004000400c0054006000800000180010000006000000e000800f000c0000000000004800000200000004000000001b000400d00040030000004000000d001c00100100020000003004c0060034001000800000580000014005000000d00000010000008000001200040080008000004001400380110010000000c00101480310028003000c00900000070064006009800801080020024002002800000040060000000003003600240360028000009c000000000
  | 42 => 0x3a01e981655a9c14b37bd960941866e3a2140e0894161d491849ab9e5631722b27198000308363ec13bcd6f0829d042c3872ac710f28aa3c1c167b1a6402add2ea2a06e50407a431dbc36600a8d00a829781dfab3a1e416484d18c8e04e28da36a9f5a0591f760791048d0a23ba4f70000d35000034daf80a17000000000000ecb036d3600009ac80004b99cf84bb80d86d7bc768742af41a82b16ae20c483d1016c17cb3c63428b7c6be00001013366c85ac06058acc47e59568ea699f26b6a3aa819b96eab5144c27f24f202c2e9c585266e12439d0000375000026d200000000001352ab680000000000b7380000002c3c00026fc9b71c3a4ad3c9a59e9f44a471790246843cc7c9a26b0335ce31cad4406b136ee7480009570be800036d2a1686062b326f2dbba97057ab35e300b4a6d0280005da292e7218000cb3b7c0cd839586cca69427b915e68710423f73288a730000e168c82f45ac8408900005828c3c0001caeea0b1e40fb8ed25340000291b2e6a020588e9b0d8a0d60000d30bafe4bdabec6fc0e3c3ee98a8a2400728bbaf2254982e8b2232a60b02e02da000009f9aa58d9f2da6db1083a7ce0000ad191dea7cb654a21a6e200001e8984ad263990b224a307a85988a8415600000001dfad2b0e2000035e89fa28cc196b48ed09bbae000340cb219890210af768a785de35e000056e0000c3d0ae4aee0b6804e800085980003ae239e46e1a6cb0e2f382258330c8c16f073d8ea685f9d6ccdf26bee3a98a4da2bd9cc440a126e2bb9cb4f953c2c5945837c12aa5eca5aa133158cbdc040a24a991ace01af4b0e9a58f331b28577a34a4ff336c1bb1d9e8a72f445f337a83369d0035b9f2a6530146c803754c890ab09be31a2696a18a3e2293437fb12cd918b76649a8a8cf78b64230183858584dcac50bf6f2a9dc6056a4c0357b64a190a0a6e859cea78c8000000000070fa21422236449b09f2270f0000c1b80005db0f04eb7056c00039c20372afe71b07c26689f00a5c9420321b07aa2d901a8a9363cc65aa2ee490000c1d36b04918000cd395a8192a2b4e57126c18eab36bf80898ef121ae0001990000263e8fd86e8f2f994216380008dc3598f5228f21500000561000063c99769420ef0264ba80eb0b0ea0002a56000224800025580000e800000eb20000000963369e67a1058041000067fa9e0258098018b3c3000000000000550b9b92f034900009e6a79655f3d9848596e80003dac9d3b64871200006122dd46be8a9a0b22f96a66a12ac2e80001c100000000ca25d2a5f25e88448aa9393400011f08678376840ba7a0133d3441780dee4233627a70706a372372aeeb5da54a198a000000070cbc46130043a06834fe0000e78af204b6a31b39600000003448b0ce2f1e9e6ff00008b92d224cdbd1c70c0000f0291a226
  | 43 => 0xe88c34a860a7eb691e6ccf311be7643860f5f121c67c2dbccf3b85c183116833bb15810b32c06c9ab565669e6e215114adee242095f056ab5f31902270000f5e0000e09202265d046652aa356e82b9367901914b8a000050290946c1924abab27467998000e0d2eaeb3300007b7164ced8bb3233c8000a0fb662e250b26d9923a274f2e1abe480bec579c1c680907699183a2e8c221ab768e10d0e1f7cd37927e00012201c210709391446b3d07106289c7edcd16b04119992bcc84a6d1a33da9cbb578b919fc8d252b4845824c89efa5be430b17c920805268caf903cb99101b3b270bfe88fee5c06c6f6fa5f007d88ca2e930d6a2f8b208661adc2a90000019a426c3c3b16249b1f09d33616c949bc8232000044480003138e6e000317400000000003144000044400008e0000000000000000000000f4100002910000831a398c7880008ed0000b4103ae520823a74780a08c0215c26a1ca8b28a9a000e2dae8f00d485a5875c9ec21fc595b0a637986b4149a368cbba15e0002306a569256f17aa96c712d104f888180000ff06913b720003d469a81c942520f920600f3e31f2a447fe95400c32a94354132c7951c0eecaa04ca609972346b840ccb0000d0c0f1ea2d30d4d5ead122d8877c05c0678373397e00000000002ee8f4200000000cba72591720002c544fb00002c0b4da0000000f3f0718f70ad2c0001cba55b3d6c2992ad8d903ad0b6c902ef288762c6b2fb43fcb008efc1d8401d800016fb7aa00032685c700007460b389413b1c88e8fb206f80005a180007fb340e4dc8ce472c0000bc980005bf38a095330f209db476f710b280f6000014e1a5444bb81e00007bae8eb414c4022d678084f84841b442f592b2d5baac65510de219c0494dc9b1da52cb2402b2b4a46599ea209e9e040a2abfa51d2d880000000e35800028b0000000326e2b1b2862ef31b21a62bea3da1f56ebc863c43a20d49dc27e4026213601d10042b1399ae752eb63a50dbe0950696a7e37ac1a8bc90d3eac68acb39ca8b799ca07487c81f889a0897b2327a1ad7aad10bf049632107e88bb0e87a3d0a688e240001bba62d8aa8c49996e5c1bb544e439fa26db870806abb6de48000a09b0c43ed00000003ba00003d82a4f0632caa01920501c1a5708760ecd000042b0be265f00105010c0a2a1889e5f700fc4538000b420000a80800063580000003d8c7ce8000d41aaf21b900004540000c7833fc7cb242c8ca972a83d997ebb60000c6eb1365911548a54800072cb0c21bd2e4e3be31a400038ca72d3ad4c15800047f00000b1a6bcabc19684d20838a7f9b2c13b2de8dff002072e15dca8faecaaf49f88bca0000dd30c96ed010a410a9c228f491a046903247e292a232b28fc7eba03a2a597a4d7193ba4b780000001520023adfabcc2598a902218699a3
  | 44 => 0x5180000000a3605960be31b80002858a0024aa6a4000000000000000000519b5bea5d907ac702e7480fac4c99e034c863053e88c2260a3bb42450f83c8f219a2c716b134d5088609ad8282d6e8000239af5800000008f098fa624a1e0d9dbc7a00038042c615d4dce85a2685155252a0972c3db38c85ea8041d10c000003c0c55400001f2800055d000000026ecbea316630211f8eb31c9a9ae3a5ceca00000002816020119420f303ab09a1acdfa000000007aeb138c8c5448000b98800040a06c8b38a2643b18d9c5fb8cea00000004cab7f622133b05180c58b811cf464f0fbc580030e08fa40cf12a8141148000711a424436b668121228ceed13025d5a5fe5238000db6baca9e9019e9292a80e312b66f3bb4beba002d6050805ace727323af3034ef28df678216e0ed7b13a12180005f90000d0f80008391fa45f21a682dc38b25273398c538264f7010c0bb92e18593b78880a0cc6752a5f816b3120c3f96b28c6253a0c0b5ca000000037400000002262000000000012e4ee48428e1bb5de0002a1400039d65c63d4092d07e60609b980000000a1d80008bca9ecf34bc140002f5a38f8c22d6d81b845c0e4697bbd4234ba06cdd0a72c00006203839f0e7f537d21b403405e590bc807974211bb58c970b0ae032880a7ff00000000000ce1904eb000000b208000ba0a986b7b85bcddc8000d25b3ea33b117a8b824e0aa3baa67b68000efc88a400000000feb3ac48500000003cf289d0000e1b05f0ecc08eae2880940001660bff1982c969b1c0000000328147eea300001ecb35a0003566ea80000b8e802e0002c6ac600ed8d650650000048e00003948a8126600000007868000d38174ce2905ecd999cc603c00000003a60cd08000e6618680d6ba9cd4fb3fe9c02c56c730bb6bf7a1566a598b8b282e4c0002490ba380009e31f9287ab38ae42a9567ad88000003b243f60000aeab882f339d3ea2680005638d5a5d739b63b894e8b53b7dc930871e2052cca24624da43283a8000075400024ea0001c76612a9b83433756c2f3a0284129843b0b5740398cc891794703299b0476c9a246050c7e061ae1cafa129400003f87bc137e0b928d60802c1a00000000000dc212b324263b2632e438000372b17827018ce0ca3bec765334a00007d00002e5a2ee00004f5a6a60000000802014c0270978dc4957600036a80000000f090000a2cbaee000290af2a000072fa282571268c7a6981ced5800035c866ac6d0ffe172918c912ae7c9933808b8590ce0000000c38aab267432a2a4c80000e90824d4b000000031bec3228e4078828e7d50bd2a93bb7400000004c1062a00000004e800008d422463d7a044b0c309c890b018dfd2bf827a0e32242126a9b68bde353261eada24760c5009a799159c3f828786bc8d566d0ad620810722edfbb50b
  | 45 => 0x2cf8958a216ec60536a94204e00000c0a0e2a04e262aa6e5d247ce991a9a5129d5262c9d48651915ccba1d684ecad06e902eea87c28ca44d9c4c0760b08c4e1dc0ce48ed0a220188cfb825c8af2344d4bb0ee6c936ec2dd0a9e7a82a26d8d9f9e0000ccef1880003fa3a740003d187ffa24a5f603d6073290001f90247042e303eb20debfd1a007d0b2920bc9fe8e3bbd3cde2b8aeac4b82a0003044de53348d8300b61f39b6ca7209408e08796e041b3ee430f7ef49315a3110d46171a53074717b85d232468680c74e0ebd5e000395230b071200019586940de4f5b8000b1d08b0635025a9d420606d21bb400022dcb72acda484ade0ccf87382c11bd8382a2fcf6780daf1a2bb2eee8000d573d7e000359c000080669580005de3902ae9a7d2b5a00009a400002d60cb68f913c2b9c83800003c345eb82acf4c0a58cadb7e0f5688027aeaf1443b34d2f6c9b3c84d0400b4b83ba5979e1eeae1e2019e9228aa0b782f160a0861d13d84b609b298d878a1073d506f31c92eef31ee046a0f84c1b43ac31b8920002578e47bbc85f7a62addbb4e82ff0036000071a00012c4f4b2fb0723800063a0dc0352a12eb7c1a1aa588000d5a96f68e5176e29dbbdc6788000263016000012f2d55b4e244604425c02f346c09a2e4b1a21c5c0977060982de5d6241e002b6f400004ba0000000c432b720000000e3d0000d1d00000be9e7a0002d5409129de993a1905830000780000000025a22b68758bbc3bb00001fa087d9860c3e9d8242e8dd8214000059d00000000000dd9200c000000066c33d467200000001b862ce851a340253cab78a94a8206b2338b2e405a00000ff83e64fd30320b48bc4f22000032d2c5e1c982ead8293de077243c00034cea9a2590ecf159678e00001581aecbae000010fa13e0f3827476880000001ce0000000000027bc49016b4000000092998427c7392a889901c19200002c4800055191ea49316bee6b3dd2b8e0778a570294aa1084038a0000d4e20240001e7233e8000d1000000000e7280500002070a4200013b400029669b924807b2a3489558000435a7aa0cf80000001262dbf197a00008b4000073a2a38000dc8324432420bc4c6a5f600011e80003168ef500001dd800062c000000000000000000e822f8e39aa11c8be9c00f38bb00cd31856559105cce9388e262b9121fe9b5ae36372eea61ba001a9fd87a606305a323dee4e1b10112ac3258f946e8a69880c1f11fe407a8022bea50c0ab9ef464fa4f08ac3564cde396491a1fdee111c2c9509d8082b100cebe290287a208206602bec1f88ba2313ab463737785aabd0ab07a0882b63336c9390688380000bcb12fe8c42f3a0002a3c0001a3a20c00004812fbc00000000000a147330b6ad410fc8c8310cce99aee6f05942acbb21c800026923c0b7de85da
  | 46 => 0x106e6a9049c749ba84518a9924bb370000000000d4b47267b147241d0af86318000255000000032a04628000d289e240ef8b5cb4e8916d31108a1983c942e000008e1b2b200022b6b26ab2a4e8931237a9fba000073c0ea8582b79047481d033881f9f8cf5394323fab420c3820683bca95e1fdb23ebf08e02b1927b8b5d0000bb3b482a5f00000003a1a9a2b524191b43285b80001aaa1bc96e00004b2b9669238482875256ee6c8364ae398e2000172e21ba2ac0db9ba455510e4ab2b3587e68000c399f1e4772cc24efac9063807fc00003661dc01563a1ab962242150c6c27decb496d800000006032cba0000522000288c3e991c4d4aba26145a010d47a9e49870152ed32cf07eb225abaa8000514b25e00010802e280007228000a8b24f69f7205a00028360d535dc00025203f300d4cb1af8241f960253f00004980000456971a47420d6df33a14ece0000000040e5810e34c62992859e000096d9f4e0002fd8c99a37a93395ecd9b9538cf21b22e0e31d000019566472ed2bd5b96c88e20060002cee98d23fe34f8000675858a0002d7e48d0000863800036980c29e287b615d09b47ed12fc000172c2b7000034d3bea08c3294ec2000060b9dfe0000a52f368000c761d86f4c8000b3a0000d163d88d4a202600024e6d8e8000ad82a6c30da8524b500003efb77000d2e0a0000d740000dde00000009153042d5183963370788b830000254bc125fe2f160000d8e3f98000f08b0a809c0000000350e6a1ae9200000000000000000000007109de1ae1fc0000000088d39100000000f0e01d60fc1f6c000256a24b0000eec8c6e000341a636bcb25e0afee0000000c012da0f59a13827b32760001320b9927621a9bd546580000000000046e8aa6a1c899aa94a5d07de24f80001e36324b58200027c83cd1a600001386000162a0000a7a0002dd622994020b6a4141f605a0bdcb0587c13d9ab6b038600033e845d14b0e58039037e919214198781e7978e0002332b83945600000ea0002f3600008f0dfab7eca1c000000005b4a51000000013a462380000003a48aed0000a2c0bea00000008af80005c5bb123e5a70e000263053a9d1ab911d6a9833920164285e3773adae1d022c11191a814c293edf68292d6899a60000000dc933840000a3a3f698a64f190001990ab4000224e9c516822e105441d5888cbf3a59c6f9a72a8ee1c4002b052a21c3a121d31d6e0d5a5c06160f700703b9a1aa2776174090ebf59f98a74800000000000000e6610800009211932000326400000009f32252ece800002980000000a6a0b120a4dd6829869f100865680003e39e6a2cc11ac12293ccd282e2e3398b4ecb898c0193adcc25c0e7e0d22e9a021bb6e5fd0c1298131d6000203cd6b1ac27ea9b58b76028c8e73a288dd0000901a02c473a894029337e
  | 47 => 0x64922860f3a0194095a2c448e14f27bcadf87c633461ee3800c06a4fe4362392abe11e05e3261a9ea17da000234caf42576b278518b341cc4bdf12261d08656c0fb550d2f22dada327ca39028ec0001d204de800029d393e5060000bf2b6841438f7c3ad80000000000000394a7a580006b7a41c40c15caa9d000016e3cb0a1102aa5662d8e0000000000398aeb48000ee900000000634a1a80000b8800079c235200028c09190f54d8abcca3fbb22cade1d121fa0000708173447008a849402f67721d04c07921a13606fa3f8a7a07f9a0aa313000078a23e6c8700005641d5a044a376529190696d2188b4d3b1a7ef0b1e0001e1c9e7a0901f9141e203117eb06000007f15f40871a4800004560001a12db70000c9d122c81dbd94da72efa000329e0002258ed81f808cf319ee83b26ce8daa46000000029c8f3a911ad8ce2e992a00000000001fd2d888000c118334000232e74b8964cc50b9242736149df800047195f6b1e957e22d80000001bec208a26aebc12c20001ca6253271a0001a102bbb2f4849b1de16900007f33a4200039e437e2da26e315d2000000050882785c211d60003a5e2938db6b0b2dbac6187c0a530ee6900b1325ccb10e541000000026c67c68a2400015a2ed48000f5c3d8a0002032000260a959977ca03016a000150a357069cb6a985ec37b256f0f85b20000d94e2d320a43e8000757972200000009c600003c8000094900000000000230b87c0000000253800000031c8a6b23626a3a444cfc3bfa97d2bf6d6a80009e88bb4db9adc0e9a36247b025ec25d23dab198e9e6a48fa09d2bcba00011321403c2c0001754d703048726148cc6a1c2ee0c246c69b8a5a4fe8000ecf80787b0a82a1d280009c998a0ee1a9a4bd92ea8b82005ccd01c34e1590c89fea27839c3ce0db40aea67100005ab99080000d60e8400001fc8efe11a315c9c28d626678ad017d80008148dd200000000000b06ab0a06400017e60000bda87735b07a3a3247010000000000000024340002ace8df98b496b9ce828a2b22b2280000001ceca9300000002ab800008d00003b5a78180005c80fca0000000ad713640002e8847b37fae9c367aa1436e8b401ef80001b7a271a7d0000000032f8000000113e36ea0023a4085e7d48da4e961f58c8e2c98678109000017b6e622da8d2c1310aef89a6a9f8b3c4ab00002978232b71a6764b70828a658096e46b148000176414f123cec0b79c000000046db776000362600000000003312e3c05e60001d9a8072d028bdab3057901d41ca0b9cd1c26e6e2e0a6843bbd103c93454deca1be4f8365a87e045800014640000000e63159400039865b111c88c7a2840000000b8812a653135fa0002c525509e102ac9c7a0000000b18294e76389fad420000154998069d271017f9fd000000000000000000
  | 48 => 0x32780a841f3485a3d14b072d6e34b0a601812e3cdc0827e965bb906701672a55388440e8ae0bd390d4dc7087a8fead76b1ba5343bbb18c67db400b5c8938e030a3678fb9566eb9a4cbdd14243ce0d14a29817ea079506b529022d390000cae21969ff20a016d913c0003304c6aab0e88b28c2341bbd8f340f365900000ba815b07ec2778543908c0230000ade916e1e9800084e872c3c1aaeede180000cc80006f3a7fe7e18000000362e000000023e2fa61cb953ad8002ee95533887c9b00a0cbb00e6ae3dba00021fab4f30fc00000006bba03000000000002f5091e95e6e98b1707b1bb2c00000007360b348f838cc000342cd581ea60cf388c006ad1c99d34b4a5a0a560e72e765110000c6105fceb0057c1329a46ca43b8a0f0adf4ac7a14a2d0809087b810211922085e2b80e72334f21c5a66264e3ad6332a7c2c6519ee3f91c26a99378eb24b688b6d0000ad68000b578000cdda3a05e02bced6f0d0e76b141abaeb8ceec437965c42928ed20592750b8289b3bb22b16903c2e31a06a1b9eec71c80009faaaac000314a44680007f91378b66000012200000000306a3e91d821da80e5819fc6a7d9b36ab5ba5a99984bc41e000480a8768b11b4ca9c3179a9a0ab5082385a8ebd345c41c8c184c00f98e57800080600000000b367750000f5ca5d8bc938f64ba999429425e26d58000cb0bacea871b6200019fce7b2f9e000000050200000003d92e4b8000dcdaf88eb1b6069da10c4022085664b27828d938467db99183820000d908c3e8fc0edca5d0c9ee77249a96c396a0aeaef42560e003e51b3000028f86b9276edcc36c88f5bd0e0001496f378a921721a8ae60125a7920666c3e1122df1a926000380a0000000df5800066a8fc0820020a647961e1a5011ca073156792986e368251a4288ddaaf1aeb0a27099c74297baae8147a0b435921d1810c30a14da53d00006510000c04000082d8c9c558090000010b6edf06723e2ab10cb7362c0002e96b6414f6d18aaa22d20750a86ba7ed610000f1b80c423b98ee94794dc7efacc8427b52215c083eb9239e0b6f9de822f2f84e49962c96829643bd3ac4a7694b415e10640002a383079b0cab80cc400009ac84321121952a5ad4601f0e2b0000cd590c61b515ee054165c745209a592aca83198e74e7f84e4918aa782c2b7147748b1a2d8351cb0b8b8e7530d08b530aaa0002272000151c0c606167320000ac68aba0002d2049a091400032d4c7a80006e680000000000f4182143190dfc0001822027a5b2bd50f847c90450812361cba40000000355a8c10000a19958a3c8bc42af69484bfe1d629ab00008ae3618ae7ae9e6431bbe93ebb961b037a23512e86d6c9bdcb238a32e9100008d8199c000205c076b84e69c80000000000169ab24a9b9f8e3142222dfe30d25b78f64ea79d3
  | 49 => 0x20000000849161a93f2266c7a000021f2b52000387eb7101105a81dea11fa8226f2bc186b80baca12a65012e01a2aff1ea4baca3ee420b114f01910ca890bba5bb82d49043be419dac0a8d98c4a796ab20871b8f822e04ae1493090aa326a495930a0a3f99363ccb02ab77a788ae103f40000aceda52106797229642ca0500000262d553cc47d80f0018080007cd800042821180bf896c0000000e720000c7f3d62e6882024faa1a8a500496db7aa20000119e5731188b70868c5f2b8d4b5b1a200001f40038121e2f81d344dab5b80003984e46000074092b840606cc2ba00004fe1cd21d780000000000a4b081ee799a0a8001f4c26fb8dc00007b0c9eb940a7600e29102cfc4e3222071c3ca480d35ccce8ad823648000f1f02b05648000f10377cae31106995acac28faf6211e8000398bc667aa1e4e0001532c7d3a500460b4a540b6fa922ba2eb679d3a063988600e86260001f462d12544ed9000085813b856f1b2a5f1bbaa81e0000275093e33d15fa00008265200378e690cc2f573cac69f8cd645623c48480000a4e26eea81bcae50a2d0a5a13150c928000af839004bd20dac3900005602152aff83f2204a794dad2aecf73820ed8cae6c9f3983c40e3568b5727acd9d2fb82e9ac728f2ad1476ba30246f14762a2966cc7b2748b1f97bef549964788b76a1c3a5522e09cc2dac800000007000000000b3c9c50ae91ebe0289b380002d5a5692474874b9b81fe2574e5e843051432faf71bca64753b6c967a6726188feca4abbf8abe8e38671931edb2bdb07570000645800038591f2bdf98be39f2b62bb0275a1842d388bfab6e06d95c69fb2186e3912c80d3af7a79a0f66f6db0daef8b630d018684c88328ee69bc322543b1e0cb32aa1fb2f8a6a712ce7af0bee5dc9e3cc45855a4861ab03d485f88039ddad842fccda82caade902c25402fe6184b4c66b33c74de138889cd2a0ce551de499201442bd0058dec175e4d7afb2df2b12ae471788ad52202115223c630b222bd2111c6b3acb8b9e89aae5d8eb43ec341c14c8000ddf9342d7cb19200001d00002f200000b0e00000000001b12d7228f0000046c000212c503ba88459059c0000c32e0fa336348b5025c780009bdb94e0903da0000000046710b4b7d95d0a9993ee000267ef16b758bc20000eb225eaae197f062700a894b0e12c362c4a8fd216cf6b86dcb173aaa48a9c06e6739a88d081a6622288ebd2bcc87782ea40e2b752234a2e6c4c039a1f5b8aaa1a373cd3320dc18d803c76731e67fc3350241943c14793387cb9f4adaab01227d84925821356e811a6a3303634a478c62e2036aee2a1dbe414341079fa1109c22ee097921b06d49b9c478a7a68df389c30997ac99f33f6ccaa498ba8a730306b710af5ab70906a016838aede779b0a407fb58637a0c0e7ca051219
  | 50 => 0x8aa20a2d5348013c982013d822044037b40ee2be474b0000ad3bbda6f5009200014ba00000000a98000966af12efb892290e076c047916ad95a8548aaa1226a62d927e53c041ca8a263afb09200020c2000380654f955800003ec470a9ba0000e9671b800000026209e1a9bc3150a3c0002950e7f2a9c00023085ab071c82d353601b0000e418d1c2b78f62cea8082be509d24a238367138000dfb86c400009b8000000048ba9c46638c0c2db21da3b1190052f000070795086aa1498cc428e85a900004fc28e2d5f989600031640001406c4734228650000187b33c5b6b520b4a10be4b02e328339c185b9000200012e8000344a6110000e9304a000025720a69c120728b5600026f0128aeb40001108a7700008a99df200000001bf8000e7dac7800030866a78000dffb01694732780000d9ed46a3e8d80a8348e2978454c2e14d2ea8f661fb2cc7172fa4bc6b84a1738dec7d789a2e9f2232ec1817400019dc0002c501ab8000c050a4a0002096000024aa8cba4608e1c6200032f8e6c2a3658d9b606b48372a82a84055c0fc6500000007ea1f4ef780001f81ac447e8000ba2988c47db3caef3bda2ca6b2f2c7500000001ece5531af0a2e32628eb8480712bad8c4a3532ceda9b48510c14326b9bab0a28ae2040000e642f8c3b32a983a688368ef348c9609e8a0000586aea30b4405b57c0002f66679141200027daab7000026e80008b331180001060ec336700c105027918000a20a8204f9aad200013f677b0ee000000000003334c2c91860e8323c278169a00035b400020c87fd18f6000000093d33a600017a87ee0000d93800042a3638062a9944e60000de8000023699347b8116c00b1d58b7f000081c90def300c24000305cf603bf624db182000215412cb7cea79bda485e0c60226b3209e436acae297302b09276ab438b0a1907de2838000be70000c6b80000001d7ee00800000035a8000125e0002798e530000000023c000000077700005d69b167278000f0a000000031600002ab000000007b7bc2e5bcb3f2ed3946aa709aa6602895cbb51f7a57637e205505e482735eef6185d88162204cfd05e218e2fc4c5c80000002c42b7b0000000333ab950c7a12d2ba2b08142e00004ceb4d85c40000000c32800083b1224763102c9deb8eca018246a430e5ecc193820000bf8ddd0000d00b97c000000000038faf3b00001cca42e4729a76894366068d858cbcf9b800000000c921828f1a931cadb000011689aebcf000070323a68c5aab657c35ea0002b2667abaec4f381ba00019f80000000639800000018c4084800086d8f0a0003a722e58000c1a0b140000000000393a0000000db09aba23d1360effa4880001a08000330e75389a4334b732000345a0018000bde39c45f132a486a95667759a0c3981002000381c67d282c0003d
  | 51 => 0x2f0abf0000796169000000000000858924bc8a88d9b082e1acd806c2b92622abf00000000d708a2e6aa86bce15106af1cabf471ab746ab30d26da880006d38e0c0001a7a66b091ef14b87800027ae00000005250e92c1d800084c9c7cc18909a4f68000f180368000210a00000000002460650000000009e4883984ced094c079d06d800c2d96f74000000017fe0000b323dd8000e760b9e10daf5cf2726ba8ec19789348ce829f000000009c46360000000000032f00007fe2fdc1daac4065aa32234e0b3e00000005bf8000742019cbc38eac45081666daa906000000000033ece0ca44c9fc024e033b1060003928e1a3652bb08000000269e07b04de3d2175000014ccb35238edcf80002f29a4e0ed27c07f8a1006c68000c0a0bd8000000016037e46fe21b823180440002a340000bcc5c117f2cfe2dc8e6492423342638f3980006f7a08c06b998ca7d27f283a8f40000242ac0c341683400001a3a47868634f63920ae266e08d604a0136e34000085327d40000a1e00023f8000000000000000000000cf9b6e459a8000c808000b390000607b658d3f35e654d37f00000930bb6b0ac0003bd013fb6e29a695be5568a90385085c35f013e101987c2af21e2d5c9ab6cba9162c4100001749ed07cf1ba200018469458c6acf4bb145a7940c0000000d87827228080f48de2358e5a3b8e000135cf0e82b456206eee6ba62e02b904400a051c085a0923d824b81b08d04f3d9fd6a92973660c0b10a520b661c936d69408f1c1a4b5264f10c5649d2ac05d49c9016b93743a80f3076f1cca727190a44837169990374206a3a8d4f1638543273e00029b2d8a0fa44afbc08077a6963ea03843889aca5deb3685c302a4dda358af00b59a150a6b40003bbe3c20e5062b0000e0b8000d52a1820001fa615195b44e2bb82bbf97aa418ae5c9a893c0003264200011244a900000000d20000394444d347c936388615ca27c9c5b8f29d9b89090c9442f07a1724168f6eaad1b207828000cf09ec49fd919ab05a65eae50dc4637a35eae60caa40c9c60b79b48407b8bfa1170000764bbc22ae3760a2f084e7a22c022720880aa21bb83f401f88891cac9758ec80df1e607d8b0209fe233837807be0003dd4b23040c041a07acc8b5aec9705aa702262c89db1ce4098f8cc1799a47dc2824d7424704f91a22b8011380960652ae41b9e3d63c789b5bc4ef638ba23aab7483b29afc8080afceaa39c05070440a67b71a51a0d2ac878e68cbc3da615999049cf311e2609db08600e5687025c4e05bc9e41f00d6b43123e00011b460fb78c872afa066b8932a43b4e633f23ea000217ccd53dbc98f0000f20800091b8000ed1bb4a70935100f5198463fb77a54b10e2ecd8804bb8b18e3a30d8492b2fe292f878e944277cef02914256a4482df95a672f19124a1a3122
  | 52 => 0x4a69650031a640e5e093a9d12abeb55989a12c133ef402bbc61b0872ec100126e39b76614196c925049808d2c0e0f7344624f168019d00002811800995125c000168e000176609a870c412b64cbf91d10877aa6200020ee04d2618f363a7895c3d4ac868794caf80eca040000408276493580004ac1f08b501670a25b22e737008400c892430c35fc1520866abd829e00037d40002fbaef80000e13199aa48898eea51f9cbd0000000018102bb344c2250efa00024661f19ed236c0000a9e87bc000129e53b0b5000008e2d1e80006d280008d69ed46212c3e0003c48eaf192ec680faa83d1c5836bb70ab9000005f800006d01e12983857e1578564901000000000fac0e3a920002f520000060ab9a57a4c6273ac19222ee178000bd834f47850e84048bb5822f873014a1fc46f480001d23c92000235c83c38c6a73a5066a510d20001a780001eae9578c98d2a0000e7c110a000000012683b66f8b4780b3a97a80e10ea463847c9d83afcc821eb091700006bda48cce8139c18922c64a5858412300000bc300ce19017a13f0a20c3a3142524000010cbd64dc2342a00026f45c9098635e800000007861861ee480bb02253600000000000000000000000001060504e4c1ee610e38a62c728e0d9b1b18f6a1e420000000b2d000055cb6f2ce400000000178c13024270a2280d5c1cce2121f74ec989027cc8b2a8c33382000000038c25a41700000000000009b8000e08000000003d200000000000a9883a0000000000000000000002a480003ba6bb1031c9f106ac89000000002b5e3e884a497a11540003996ee889626f81beeb111d7019f033aefd24cc15b87cc35011268cb01f21278000931bb202f9937695fb1548950d426f08000a8a00003dd00008a234d0447b282000012e0e9b328916302e31e15fea601dbaa6717a0b56000014d11a626781000ad80005df8a883720792000100eda6a3300002fc6283000049e11f400000009a02380000000033780000000000000077af15a7928fb0000c2e366a99700000001930000168acb6b826000000044ebb7a7931b3a00008d800028ac0000000b0100001dbb44800035d200900008ef8000b8488fc23b03ac962a684049354e460abcc4298dee1bd9eb827e18e44ef0d58cf0230e00002260000000000000067380000dc1a1600004ea6b1b3720878000000033626f05e8937284c000351271a225c02f24a2e958d186afac2214b933040d0ea2ae0b5964600000223af680001d789ee8a385172ceca45b43c0003dcc2391836dc180000d183b0f5e9b000001ceeaa81996edabb78bf48000479800000001aa19b00006023aeae831caa003af42c4f328482c80e80000bec7663464f4d9920e6380005e1865839da4303f0b4b24d63be618292bcae039bca95286cb94bc64c8394e00001a62f562
  | 53 => 0x7e113b01f52b42991143808b88f20001fb6d9c9f644e59eb49b21aa0000053a2a000009038000d450cb8c5da0702e40db4c2a80009d500005e7a920482080e000000000000007bba1e6000200a4c596d65b235f459f2830f4a205491692d0b3ea14e1b9a722989038e5ce8000aeb20625ed17a6a88a9d60138f2861489b0a20331ecfeb16e50d2670000031a06f266006cb002f171d2a000000049c0e36af7269c00007f4ad28bc88c8090a83f09d642a9a0498ea4e8d21920ee348000c81ad24530ab7ed020c5292e89dcb0a9e5e183b05a91402e680125924e99f5c21a98f44fca6105fe861c6620268f06ad8a00035e2751800065437d086e800000000000002486ed7358e8abad604888e1eca014266ef1e949258000389a2ce01528180002622000077400006da3e1b6be876167e5cf0c049428eaedc30b6e61ab87abea9c389a215b652e0df47738000778800000000000001c36d56350a46cac489603d4c0000000d1b8c84f1106080003332e7ab1fa0000000d502652e1a8e3a1973942d2b82ccb290b2c553800020b0000081800048da930a83bcfe2d1847210d0998661b5fe7343450ebda4a829e1f506f6a17050e95e07581198c2100003f49894700b740ba6206a0003bb639732ca02e1e26c8d9f66440bcfa42618f89edadf2a9db500010128a13127e02a306400fa012c8be069eb29a89e5da90f85fb3ca08a18c944a3a17439283009b78ee807380000000832107aae8a39b13ead30000b02160e273a7e2cc0000000019da0001f20c4bab04c9626ea00001581ea80f639b00004b300000000000d6836ba6e9af6eca617b0316a752dca2fe8b45a75ee8016882bfa15a04c0f12e73800023e97d4000000073c81c2cc900000000000a1d2d18f20181aeee14489d60556db19bf45d89bc43aa246aa9f0bfe63323ce68a2012f1fb1ca8a2932e71d3d20cac3798de00ce0c2c3a868e9163ae93a340da1997020abb9ebb70d96533b8425d12bd46a08c460420000f4aab6ad27356c2613a2ce18983a0000b78cb80000a9a8d7ef641818b4c09fe55e000088180000000f5cd9f8b887732ce056837bededb302e39aef81318000e4118bc4b897600aa2be26dd000000013b6d3b0000bbf3cb4000088a8e5a07cb1886e24e686ba0c5a58eaaf0af0a0a13e892c9ad0042a84631c0a181ed2422aec30823fe8ee4f0f1a0e3d6af023c6b9a0b7716f85b701b4e198f9ad430f7a1770f18e8d0d64f448b982769aaee279ae6615069aa7b891c6d71b788bb193a7fa8514521a12821133beccc115221b2f04edc35165bb015ebd3002627086f82372f0cb399812465b4448610eead83afbe735253e0af2bde77c020800f910ee520834eb99902b302fae2f525364769e3a9529c16de99b84317b4043fd1ff2293050896236ea7df99bc07d16d2
  | 54 => 0x2175037a9d725fc56b00aa9518414548966833f8000cf59f060000e520002988d07b41253780002c01b906662bd82ea1d500f40000c48b3d04db03c6a6b800030e96345cf96c62442b0ce6a9d564e125da6baa162423b54877da0b857012322fcb72285618fc0798326c74a738a378000e48afd0088ab4077e34f0b5a80003e0240a6f435d65862a5cb5e1e0ec0925e6a0ba6980002caeaf12f9a450353a32c3ae000008744c2372c6fd962053bbd74a6dab283a299b26edb39e87f8c10599028650d8e06e4527ee93b210e0932e5ec5ab79e2d78e18e4c9292ec2ab0800000003d3b61a4a13c6c40aa42800008ae7ab1b72868af064ea070a000306aea59dc4738ae2a3ca8190b54adb000039cc1e68af6000354cf25abaec1c2fd40002436000385227d3c5000038becce18aa78b80001ff82607698ca4dc3a9f0b962dfe60b3b6687c8000f2e03bc0001b0e78c1efc7bf80007b8bcdc2d4a8d40000b7a0002ef206908ac28880009daaebcb543698022b17ad9728a43f5a05eed100005348000105aa300000000b7400000002f2e0000000d793576099951435db456958336e73c1ac800012986190f0c3f52d1e8d1b1b6b5c13aeaab8d70e120bd00001d7cb2facfe2762f5e815800018a276c51f00000002cb20000296524ae84975000000000003ac00005f00342000000000010b87192ac46a8b146aae9200d2dadb851380001a02628000041a969a9b06ea22d8078126e3c9b0400860ccca049d2826403e4b318000d1a961c0000d52e0b022a0002fec0060598bf216f4278ae4a1b8249c92836a4cc98614dc7a4ae11c29ca94baf00743878200016100000554ea8a0c0516b5f6596989e49500c8770962ef3d195c094bade42205ee00034ee415a720a44084c53533523de3cf0d6906d6b9c000000026fa00033ba0002d8031038c8d3e1272360b690cf8987a0002a92d601d66791264ab0923b2875af1e83333dc53e9746049b75e36ca2ca1a08a163d28e82c9a9728ac0ad943661f6ac4680002410b24d2a92ae2281f823739d7a60cb094beb018400000000000000c4913806c28046000300687b32de000087e3a714fe00021e40000a34c5f98828e68000d2400005fabb807c3063ed7116c2c7700008b000003e739e827cb04a5f580000840000da0b0d099a000066eb2c87c5148a7fb9f68233806ed75330a59990dca3a9cfec9cb8b62d30da23c4231cc2282dca660f825beab7432c994e38116286fa08b200000004dc2ec80002c12ba51ed8e3f1b9240f800000007202f0ba06000000008a00006db800013512f835b19d885204d600585b0632a04a1d39c0a16690840000ae64c90000bda970a1b4ac708f21e18ca583505c98000000000002d117c228aed60000000b160ba00002a90cc61740b982a42a18bcbc000000017aabe6000
  | 55 => 0x4b218e3093fe4e239827c093d4db82d0e5ef21cc2511ca03642a9e11e3d1e000227eae6a2eab591cda0003a76340894619a045e000000089132283b0000073f3a2296a151e61025221528000224af1ca2ebd5663a9ae84e500000003916c54aac8e863a204d396247743cc66ffae26dce3b2ea4606cadbe3ab6f5a302c3bd9c5645e2f0adf09252a50a4bc88408cc4e4b35c3550120000000000026c06750e8ec66933c3b39a5e0d2929c79e004a35a3c2683616220001cb6f4f8fce29b93284ada93ae3faec6e25b2502f18dd40392ed049114aeb613b689d0055ce7d38e28da8886142a5de415101036219541320fb62eb912a46abd84c288a625b3b2bc8d399d232b969cdd2912c008b2b46343054d2e2a1ec9311040db0a305a4bb8cf2388deb78a1b485907a20ae1a34c70b7f2bdb266a118a8aa6ac85da000136602eb3c420200004b6904017320d24c39ab44a4372ab1d9a4013996b8f46a314c278e98a6307dc51e1a80d249cde02c9e82ef4b79a0000000000000018ba6168b501968d51bb26fc832acb584d2df6296012f9e84a7a20e6c141202dadab3e2f384d0e891da0dc63d26464000000000000002d48905a83ceacb6780000000a51b06c1a4031001c355ebe19e2a219030a00010f4e78a7b4e1dae68c261d386c53ae49fd26aaa5fa65a3dcafc095a309a09f1be40000ab6e76a500c1c9a84e0517c203336ce3908bf43eb87da000325489a0402632213c8f5000021e19a034f256c2b5a0a20003374bc40248473151000020fe0000968748a528f48b76c0001ca40000000dd980006cd00008a533641a1a14600016e65298000218934ac4200009780000000281a2b00000000284800000005fa0000a468816c719dee000250e5b2a3ccf5a8284989acced0605c2690a912299839e06a2eee1cd9bb0cdc1332ee209cadd3b47e56e8c0617816ea5b016a61482c104c5233e0f326d07b2376203fa22a0002a000000000cea28322af99faf30a3c63931362a751d060e4a5321f12e8c1c50e1c8eda4d4d620e2a165294a0000e880000c8a00000004510cf6b250000c25ab767b300009b61b9454d8000def002a1c0800001580008450000cb4000000000006df0000a1f800000020360000000b05000055700007a4146c0c7ba2a31b2f2a8eb111642b957a404ae3e5a880000002ae235aa898a6f800075dbbe824a000015e80000002e228bd2aa82aba8f4aa6906c87087669c100001bc000000039721e822281022142b598000214bc0ef3ababa56c80006bf80001e6095e914afb6531ad468c28000673314000014140001c827dc89341ba9b54c40b45ed2622e20000976b9a85fa50b244e0003d0c887b6929ec88e898085f466f9c8413a23dc679ad9a5b88000c980000b9fa43adb032d800019520000e7a5908000e56bce46cba2d
  | 56 => 0x78212a88a6e21df45b52b0660924b60faa9fcd82194a52b1898cbf1a2a8102e3411320faee10bb2eff3afaa15a6c432a1e8c1fbacdc0d10e54f0a885a10b8114869000000032349f18dd6a788000e0603f6bc611d20002a2a5e49fca3d19714b9e1586cd122906e5a8d2ce6b65e687938e000296c0001794538a93660d2a70000111000000000f815246d93a3e00016cc00000000003db80000000c6f21c43c5a5acc2000007510ea4cab0d109850ed495006f2ced0b94a640a1c361aff231a34885f8935a8c9a884af000003b5a4de3ee0688b8da3e2b3aa292601ae6600015fc78b1dd86d18000000127a7c280008a8bd2e424a6a84aa34c8000000000000009cda390daf1efa00018f066a00001cd0000aba800073e96a874c87d2db600007b580000000000e718000c2319b4a1f320474c22c20003cb60001aac53c290436008827aaa9aa49917fc00013d2113b6cc421800875c9698419a388c098fc4567b8de39601ea845800000000008ca00000000000000000000031f87e400000001bc07858000f0000001a2800094e0a0a00002903d5a9a87288000ac61b4c11d837ec9fbaaed848000b819c5e00022e861d924e425890c36b36f0a1092faf581baa0b280006e0920cd19814838b2d1a366a96a8ff2a16e269eb2f6d16528b421b2510074048c00003fdb99e54580000002608000014aacf0c2e96ea5ce000280a48e97d2f4e37e6e54267af5da7d69c78000755104c4cea4e20002ae40000f3cedd80000340280000054e000348a7ea00003599ce682e80005d3bc1000000000001ee810414b619790fcea3801c1e700000002cbc00028c85af39f270ab0609c4900605ba042b878622915af4647915e20c800004eb1630526b30cb25800072232baa42343400004260002fdaeba0b72000329c00037c80000000da3b0b6864ba5215d8000cc6a98acbf9e7c7a4bc5400037900000c16f5100008698000000000025f8000211a27a55b984e0a88000000000036a00005358000000145e79417d0c3000003bf0780000020c396abeec3730ecb841922d181350000156200000009801d24b90b9628479d889dd1dfc46c0c2ae36939e00019c2a24b4eac84800043d94e4cab8000515000079d8fde000000000026584ae852c3350a482a800004a000003459bfa0e200002ea800000000006038000000010e6df8000ec38000000266c00000000001fce873a5264a09ad604c99484c2b6968f624ee00022ba9618000a5600000002d42ba99b66da980008e134d61e13bac765a09e7eca9fabfc0000265ba6e97700003d40000b8b14f80e3000090000001ac02e0884abf2a2880002842d2ab1f20f23d3243e7cc0d306a20a06ca2b0be000000000025bc1bf1a8ce92b3160001a3c0002ffe2a8bbd60000000c620000d548bc066d817278d02f47c
  | 57 => 0xe6f93401588bbe138a7723c525842449fdc143134c28020a83fe3ae2c67342ed78254833c283a4ea82fccc709ea76d136894a8b5a6fa8988576ab32821b83cdeba54e2799bd6d269a3e71e1b70b672442bfa8f2cc8aacb0dbf84e069c1eea0f12a60539b03c7593a54c5b096af6a903623da26ecf9287ab941d0c9b5075a4b5b93c75d271c4f410d0d13b27ce4b31fe186b14c21a1a64d640a540f89a38a338aac11a99249b309cc54b8c429bf8be49f618ae252979c0ac8e4e0daa0be8a380002902514762bcf8d1484245281cc05f3954a0001014000219a9c0a20ce8700000000000000000054a80005918a6c000130c0bb0000414b3b87111f3ed8800f20000ede6b51c4243800000002ff6d6780005221430000000005d9fc21fc00000a704a800000000f0000000002360000000d4d08d45c4a5fa180238c72025cce141612034b6f600016d0e6d00009748000557a728ea9323a694949ec7d86b643990fe3c394a2e51aa5e735a6b09ba3a90000310a9569ce4b270000617115644c2b9c4d5035e0002b64000035c7f83704eab20c41a90dbc7fdb0ceaaa807cc5896ba255a5c60002d8649f1556cc22e241368c88e7b8d3260101165a5208a4828d1e0f7b5f053237ba6b8babe84c2cf64d104aa30730
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x864d635482104362b1a42108215c5d761d00108f2ed28e8008571751074004398aa083a0021179cf65900108bae7b2c800846e72d964004236b96cb200218d55261900108eee3b2a800845e73194400422eb98ca200211b9c865100108dae4328800853975990400429cbaca8200211edd95410010a76ecaa0800863b76550400438db9aa820021c61cd5410010e56e4aa0800872872550400439838aa8200211edd561100109e6eab088008673755844004338b2e8220021cc5534110010ae2ea2088008671651044004237396ca180211b5cb650c01087ce8328600843d741943004237390ca180211b5c8650c010c9ca6b10600864d535883004364b126018021179cf65080108bae7b28400843e74194200421eba0ca10021179cc65080108bae6328400864d639482004326b1aa410021b258d20080108eaea32620086b264d03100423abb4a3080211e5d464840108f2ed28c20086b264d06100423abacc888021ac19340440109e4ed20220084f07650110042e9b9a8088021741cd4044010bc6e4a0220085e07250110042f13906088021785c83044010ba4e610220085d173081100423cbacc8880211e9da5144010d60c9a0a20084f27690510042783b2828802174dcd4144010ba0e6a0a20085e37250510042f03928288021789c83144010bc2e418a20085d27308510042e8b9842880219c5d765440109e4e9b2a200857276d9510043393b6ca880215c5d664440109e2eb32220086717599110042793a4c8880215cdd56444010ba6e6b2220085d07359110042f1b92c888021781c96444010d64e832220084f276d5110042783b4a888021ac19254440109e6ecaa220084f0765511004358322a88802174dcd5444010ba0e6aa220085e37255110042f0392a8880213c9d85444010e62a82a220085d27315110042e8b98a888021789c85444010bc2e42a220085717598d10042b9baac6880216cdd16344010b60e8b1a20085e37258d10042f0392c688021b458c6344010bc4e431a20085e17218d10042793b6a6880213c9d85344010b64e829a20085b17414d10042f1390a688021785c853440109e4ed21a20084f17690d10043583248688021789ca4344010bc2e521a20084f37650d10042783b286880215c9d44344010ae2ea21a20086b06410d10042b8bacc4880215cdd56244010b66e8b1220085b07458910042e9b9ac488021741cd6244010ba4e631220085d1731891004370b10c4880213c9db52440109e4ec29220085b27414910042d8ba0a488021749cc5244010ba2e629220084f2769091004278bb48488021ac1924244010ba4e721220085d1739091004279bb284880213c1d94244010ae4ea212200857175109100435832084880213cdd932440109e0ec99220084f2760c91004278bb06488021f04c83244010
  | 1 => 0x5404338308c0aa0210fdd95415010c3aa8b18a80862d54588540430f322c62a0219398e6215010c9ac7310a80862e64588540432731ac42a0219358d6215010caac7308a80866562984540432cb1cc02a0219a58a60150108dee4b26a60846c72593530422fbb2a629821875915314c10c9aa6b10a60861c73590530430eb24c6298218b9926214c10c5ac9310a60862e645885304316b22c4298219398d6214c10c6ac9308a608639649805304237390cba18211b5c865d0c10a38e6aa6860851d7414f43042a6b90a7a18211b9cb6590c108dae5b2c860846e721964304236b90cb218219394d6290c10c9aa6b148608475759864304278b84c3218211e5d66090c109e2e3304860845f735954304237b92caa18211b1c96550c108dce432a860846d72195430422f3b4a6a18211d5d46150c10c6aa830a86084f170185430423cba8c0a18218e5506050c109e2e2302860846e721944304236b90ca218211d9c46510c108f4e0328860845d76d4c430422ebb0a621821475d05310c10a9ae4298860845f73593520422e39ac9a90211bdd95214810c5ac8a90a40864d635485204316392c829021879926314810c3ac9318a40861e6458c520430eb22c6290218b5926214810c9ac7310a40863564984520431cb24c029021179cc65d08108bae632e840852c725534204296ba0a5a1021535cc52d08108bce7b2c840845d73d96420422f398cb21021175cc6590810c9ac7294840864d6354a420423abacc3210213c5c261908108f2eb30484084f171982420422fb9acaa1021171cd65508108dee4b2a840845e73195420422eb98caa10211b9da52508108eaea30a8408635541854204278b80c2a10211e5d46050810c72a830284084f171181420422f398ca21021175cc65108108ece2328840847a701944204236bb6a4210211b5d85210810a5ae8290840854d73148420421f3a0cb990210f5d065cc81087ce832c640843d74196320421fba2ca990210f1d1654c81087ce832a640843d7419532042a6392a699021531cd524c8108eaea30a6408655531853204332a90c2990213c5c0614c8108f2ea3026408659531813204334a90c0990213c5c4604c81087ce8328640843d741943204327b2a641902193595320c8108eaeb30864084f1709843204362992c2190211e5d6600c8109e2e330064086c93258032042b8baec1a0821179cf65904108bae7b2c820846e72d964104236b96cb208218e5526090410a6aeb320820853575950410423bbb2a8208214ddd95410410c6eecaa0820871773550410438a39aa820821c9dc95410410e48e4aa0820873070550410423bbaac0208213cdd56010410ce6eab00820846e72d943104236b96ca188219394d620c410c9aa6b1062086c5624c4310422f39eca10821175cf6508410c9ac729042
  | 2 => 0xcba1a21535c853d0d108dce5b2c868846d72d96434423ab8ecb21a211e5c36590d108dce432c868846d721964344317aa4c521a218b1526290d108dee4b2a868846c72595434423bb8acaa1a211edc16550d108dee4b28868846c725944344237390ca21a211b5c86510d10a9ae4298868847475584434432a29ac221a213c1c16110d108f0eab00868865853580434427838ac021a2117dcd64d49108b8e6b26a48861f64d8d524430e326c6a922187d906354910c38c831aa48864d7218d5244316326c4a92219318f6254910c68c9b0aa48865463d85524431c326c0a92219618f60549108deeca90a48852c7454852442a639aa4292219358d5214910c98e4b18a48864d63988524422f398c229221175cc61149108bce6300a48845d73180524422f39ecba1221175cf65d0910a9ae6296848845e73d96424422eb9ecb212211d5c765909108f2e1b2c848845e73196424422eb98cb2122187d526390910c38a931c848845f73595424422e39acaa12211ddc565509108f6e0b2a848845f73594424422e39aca21221179cc65109108bae6328848854d73148424423a3aac2212219914961109109e0e0b088488478755804244334292c0212213c1c5601091087ce9b2e648843d74d97324428e3a2a799221531c953cc910a9ae6296648843e74d96324421eba6cb19221535c8538c910a58e8a94648854c7354a324421fba2ca992210f1d1654c9108eee2b2a648847b70595324422f3b4a699221171d9534c910a38e8a9a648854c7254d32442373b4a4992211b1d9524c910a58e8a92648854c73549324423ab8eca192211e5c3650c91087ee8b28648843c74594324422f398ca192211b9c8650c9108baeda98648854d7214c3244236bb6a419221535cc520c910a9cea990648854c754c83244327b2a641922193595320c910c3ea831a828861c5418d4144317aa0c4a0a218b1506250510c70a9b02828854d7214f314432c29ac198a21535c8534c510a9ae629642886685258321442a6b98a490a2117dcd65501108b8e6b2a808846f725954044236392caa022187d506350110c38a831a808862f5418940443162a0c4a02218d1536150110a9ae429e608865453587304421fba2ca982210f1d1654c1108dee4b2a608846c7259530442a6b90a698221535cc52c8110cc8a4b0e408843f74595204421e3a2ca9022117dcd65481108b8e6b2a408854d731492044237394c72a0211b5ca63950108bce7314a80845d7398a5404327b1ec4aa0219318f6255010c9ec6312a80864c63189540422fb9ac2aa021171cd61550108dee4b0aa80846c72585540432bb18c2aa0219518c6155010ccec430aa80866462185540422fb9ac0aa021171cd60550108dee4b02a80846c72581540432db18c0aa0219618c6055010cd6c4302a80866862181
  | 3 => 0x856015310ce4c2b06a78846e72d9153c4236b96c8a9e2117dd95314f10c9aa6b10a78864e6358853c4332b14c229e219c9856014f108dce532e878846d7299743c4237396cb21e211b5cb6590f108dce432c878846d7219643c4237394caa1e211b5ca6550f108dce4328878846d7219443c433930ac1a9621179cf6454b108bae7b22a58846f7654852c4326b1aa4296219358e6214b10caac7308a5886726158052c422f39ccba1621175ce65d0b108bce7b2c858845d73d9642c422f398cb21621175cc6590b108bce732a858845d7399542c422f398ca21621175cc6510b1087ce932a658843d7499532c42a6392a699621531cd524cb10c9eca990658864d654c832c4364992c0196218e9516010710c9ca6b10638864d5358831c4326b1ca410e219358d5208710c6ca830a818847976d5040c432aa98c298621b2589300c310ccaa430a41886c96348020c432731cc5aa4219358e62d5210c9cc6b16a90864d6358b548432d31cc1aa4219658e60d5210cd4c5306a908669629835484338b0cc1aa4211b9ca63952108dae531ca90845e7398a548422eb9cc52a4210fdd95415210ce2c3300a908671619835384237396c8a9c211b5cb6454e108beeca98a70864d53588538432731ac429c219a58a6014e10ce2c3300a70846e729974384236b94cba1c211b9cb6590e108dae5b2c870846e721964384236b90cb21c211b9ca6550e108dae532a870846e721944384236b90ca21c219c58660d4a108bce7b22a50845d73d915284237bb2a4294219358d5214a10c9ac7310a508659639805284338b0cc029421179ce65d0a108bae732e850845e73d96428422eb9ecb21421179cc6590a108bae632c850845e73995428422eb9ccaa1421179cc6510a108bae6328850843e74995328421eba4ca99421531c9534ca10a98e6a92650864f654c83284326b2a6419421b14c9610ca10c74a8302830847576d50418432ca98c098c21b1589310c610cd2a430243086c563484218431b2a2c2204219394d620c210c9aa6b10610864d639482084326b1aa4104211b9ca63951108dae531ca88845e7398a544422eb9cc52a22187d906355110c9ec7b12a88864c63d895444317b20c4aa22193d8c6255110c98c6312a88865763d85544432a31ec2aa22199d8b6155110cc8c5b0aa88865b63d81544432c31ec0aa2219ad8b6055110cd0c5b02a88843f76550544428e39aa82a2214b1c954151108dee4b26a68846c72593534430e326c6a9a218bd936254d10c58c9b12a68862f641895344316320c4a9a2193d8c6254d10c68c9b0aa68866462d85534431c326c0a9a219a18b6054d108beeca98a68851c7454c53442a6392a629a219354d6214d10c9cc6b10a68846e721845344236b90c229a211b9c86014d108dae4300a68846e72d974344236b96
  | 4 => 0xbae7b2c841045d7598e420822fbaac72104117dda53908208baed29c841045f7654e420822ebb2a7210419654e6010820cb2a6b00841054d73d504208237bb2a8210411b5db5310820a5ae9a98841054d7594c4208386aa4a621041c39515310820c9cc8a98841070e6454c42083a4a9cc0210411bdd56010820c9aa6b008410749535804208275baac0210419add56010820cd6a6b0084106ca535804208334a9ac021041b254d6010820c92a6b0084106595358232082a6b92a61904193d95320c820c9aca990641065a53580320822fb9ac928841171cd64944208baed298a21061e6494c510830eb24a62884117dd95314420c3cc8a98a21061d6454c510823bbb2a2288418d59151144208bce732e821045d73997410822f39ccb20841175ce6590420c9aa731482104e97098a4108326a9ac52084117dcd65504208b8e6b2a821045e73195410822eb98caa0841175d763504208baea31a821045e7694d410822e3b4a6a0841179d953504208b8eca9a821064e53d894108326a9ec4a08418b9506250420c9ca6312821064d531894108332314a2a08419694f6050420cb2a7b02821063a54181410832d298c0a08419654c6050420ce4a2302821067151181410822f39cca20841175ce651042087ee8b2a621043c7459531082aa38aa6988419354f624c420c9aa6312621065953d81310832ca98c098841555c6530c420c9aa731062104e970988310832729ac4188419354d620c420cb2a7306421065953583210822ebacc61084117dd563084208baed298421045f7654c21083a329a421084117dcd64940208b8e6b24a01064d5398a4008326a9ac520041179da53500208b8ed29a801045e7654d400822e3b2a6a00419394f6250020c9aa7b12801064e531894008326a98c4a00419594f6150020caaa7b0a801065653185400832aa98c2a0041179ce65100208bae7328801045e73194400822eb98ca200419354e6210020c9aa6b10801071a535004008326a9cc5180411bdd5628c020c9aa6b14601064d53988300832729ac4180419354d620c020cb2ca980601064e6454f2008326322a7900411b5da52880208f2ed294401046d7599120082373b6a690041535d65348020c9ecb29a401064f6554d2008327322a690041931915348020e90e0a9a401064d53d8120083a4a9c80900413a1d94048020d50c8a0240105c87350120083a4a9a8090041781c54048020e92a79824010569750c1200832db2ca69004196d955348020e92a729240104ea7690920082e539c84900415a5d73248020b94e610a401064e6398b54c4326b1cc5aa6219398d62d5310c9ac6b16a9886566398754c432ab1cc3aa6219998a61d5310ccac530ea9886726158354c4237394c72a6211b5ca63953108bce7314a98845d7398a54c421fbb2a82a6219c9
  | 5 => 0x53471550544822f39cc42a241175ce62151208bee6b08a89045c735845448237b92c9a9a41871936354d20c58c9b12a69063764d85534831a326c2a9a418dd906154d20c68c830aa690657631855348333b10c2a9a418e1936054d20ce0c3b02a69045f7654c534828e3a2a629a41551c55314d208ece3b2e869047571d974348236b96cb21a411d9c76590d208eae3b2c869046e7219643482363aac521a418b1516290d209d0e0b14869046f72595434823bb8acaa1a411d1c56550d208f6e0b2a869047771594434823a38aca21a411d9c46510d208eae2328869046c75588434832629ac421a411e1d56010d20c70a8b00869065853580434831c2a2c1a12419614d60cc9208dced2a2649054e7395132482a73aec699241539ce534c9208dcec29a649054e7614d32483273b0a699241539d0534c920a9ae229a649054e75d0d324832632e8699241531d4434c920c98ca21a649070c5410d32482e4b8086992413a9d4604c920cd4ea302649066a5418132483342a0c099241b2d0c604c920d9086302649047776544514829a3a2a228a41551cd51145208bee6b20a29045c73590514822f39ccaa0a41175ce65505208bee6b28829045c73594414822f398ca20a41175cc6510520ccac4288829063854580414833828ac020a419319532cc520e8a65a8e62906c932583314832632a6498a410fdd1650c520878e8b28629064f53588314832629ac418a413a1c1620c520ccac5a886290665621443148266b9cc5a024117dcd65501208b8e6b2a809061f5418d404830e2a0c6a02418b1536250120c6ea830a809063454185404832629ac598241531d532cc120b90e0996609043f74595304821e3a2ca98241531d5324c120c98ca99260905c8704c93048326b1cc5aa0411b9ca63950208bee6b0ca81045c73586540821fbb2a82a0418d5516115020c9ac7310a81065663984540832ab1cc22a0418d9916115020cacc6b08a810655635845408333312c22a0419658e6015020ce2c3300a8105567115253082aab88a929841539cb6494c20aace2314a6105557118a53082a7390c329841955846194c208bcedaa2a61045e7615153082ab388a8a9841555c45454c20a9ce5b22a61054c7259153082abb8ac8a9841551c56454c20ab0e0b22a61051f74585530828e3a2c2a9841531c96154c20ab0e0b0aa61054e72185530832ab08c2a984117dd95314c208ece232e8610475711974308236b92cb218411b9c86590c208daeb314861064d5398a4308274b84c5218419394d6290c20c9aa6b14861047771595430823a38acaa18419354f6250c208daea312861064d53189430832ca9ec0a18411e5d46050c208dce4328861047671194430823ab88ca218411e9c06510c20a9ae7aa6841064d6554f4208326a9ac1a1041179cf65908208
  | 6 => 0x10c334a92c1988611b5d6620c4308deeab10621846d76948310c237bb2a418861d1949310c43087ee8b2a421843c74595210c327b1aa4908619318d5248430ac8e2a92421866952d81210c334a90c090861365c26308430c9ac7290421856571948210c32731aa4108619358d5208430c9cc6a94801864d6354a400c2373b4a4a00611b1da5250030c9ec7292801864c63949400c2373b2a4a00611b1d95250030c9ec6a92801864c63549400c333296c2a00619954b6150030ccca430a801866552185400c32731aa4200619358d5210030e54a4a00801864e6454b300c326322a598061175da538c0308f2ed29c601845d75991300c327b2ca49806193d95524c030c9cc8a92601864c64549300c3a4382a498061d254a404c0309b0eca02601869864501300c2e43928098061d2549404c030ba0e2a0260184da7690d300c2e539486980619ad96524c030cd6caa92601874a53549300c2acbac6498061729c8314c030c9cc7316a99064d6398b54c832b31cc3aa6419558e61d5320cccc530ea9906566358754c832ab1ac3aa6419998961d5320ce4c2b06a99043f7655054c82a6b9cc42a6419a9896015320cd4c4b06a79045f7654c53c832aa9ac229e419598d6114f20cccc4b08a7906726158053c823b38ccba1e411d5c665d0f208ece232c87904757119643c823b38ccaa1e411d5c66550f208ece232887904757119443c82aab88a799641595c4538cb208bcec29a65905557114d32c82a739ca899641725c3534cb208dcec29a65905657114d32c82673b0a699641715c4534cb20a9cec29a659064e7614d32c82a73a0a699641d19c4534cb20a9ae229a65907457114d32c82a2b88a699641d25c0534cb20a9ceba1a659054c7510d32c822fbb2a619641b24c9600cb208bee6b24a39045c7359251c832631a64a8e411ddd95114720caac6a88a39045e7399741c822eb9ccba0e4117dcd65507208b8e6b2a83905357494441c832632a6498e41d14c9514c720d9265b0263906556394421c832ab1aa210e41335ce62d0320c5ca8312819064d5318930c82e43826498641b2589300c320c9ec7b12a91064c63d89548821fbb2a82a4419a58a6015220cd2c5306a71045f7654c538823b38ccaa1c411d5c66550e208ece2328871047571194438828eba0a621c419614d6010e20a9ee6aa68510639541814288236bb6a82144153dcd5410a20a5ee8a98851065953181328823bbb2a228c41179cf65906208bae7b2c831045f73595418822e39acaa0c41179d8534c2208beeca98611064e535883088326a9ac41844187d906355120c9ec7b12a89064c63d89544832bb1ec2aa2419518f6155120ccec5b0aa89063764185544832bb18c2aa2419518c6155120ccec430aa89065863d81544833830ec0aa2410fdd95415120a38e6aa0a89
  | 7 => 0xa212611d9c465109308eae2328849864d63148424c31c2a2c0212619a1496010930a9ce52a2649854e75d89324c2a73b0a499261939d8524c930a9ce8292649854d71149324c2a73ae8499261531d4424c930e18a821264985c970109324c26d3a8c099261969d4604c930cb4a8302649865854181324c365a10c099261b2108604c9308eeeca88a29853474544514c2b2392a228a611bdc964145308d8e4b20a29846e72995414c236b94caa0a611bdc965105308d8e4b28829846e72194414c236b90ca20a619558c5110530c70a8b00829867051580414c32632a6590a61d14cb51c8530d9264b06429864c654c9214c21fba2ca10a610f1d165085309b0e0b18429864d63d48214c326b18a410a619558f5108530caac628842984cd7298f404c30e2a6c6a02618bd506250130c58a8312809863754185404c31a2a0c2a02619398d62d50308dee4b0ca81846c72586540c21fbb2a82a0618d5516115030c9cc6b10a81866662984540c332b14c22a0618d9916115030cacc6b08a81866662584540c332b12c22a0619a58a6015030ce2c3300a81854d72d53430c236bacc5218611bdd56290c30a9ae5aa0861845f76550430c22fbaac02186136dd56010c30cb6eab00861856671152520c2b2b88a929061c35504394830b92e021ca41854e73d92520c2b3388c729061595c463948308daed21ca41854e73186520c332b08c329061565c043548308dcedaa2a41846e76151520c2b3388a8a9061595c45454830a9aeba1aa41870e5410d520c2e4b8086a9061539cf6454830a98e6b22a41856771591520c2b238ac8a90615a1c16454830a9ae1a1aa41846e7690d520c2b538086a90615a5c04354830e1ce821aa41874a7010d520c2a6b8086a9061d25c04354830a92e021aa41852f74585520c2963a2c2a9061531cd6154830ad0e0b0aa41854e73185520c332b08c2a90611bdd952148309b2e131c841864d6394a420c32731aa5210619358d52908308eee2b2a841847471595420c327b1aa4a10619318d5250830cd2a5b02841866952583320c335292c0190611bdc964944308d8e4b24a21846d76948510c317324a4288618b59252144308deeca90a21862e64548510c316b22a4288611ddd95114430c6ac8a88a21846e72997410c236b94cba08611b9ca65904308dae532c82184d97098e410c32731aa5208619358d52904308dee4b2a821846c72595410c237390caa08611b5c86550430c3ca831a821846d75d89410c236ba8c4a08611b9da52504308d8ed292821864f63949410c32631ca4a08611b9d952504308d8eca92821864f63549410c32631aa4a08619518e5150430cd4a5b02821866952d81410c31d2a0c0a08619a9486050430cd2a4302821867251181410c338a88c0a08611b9ca65104308dae53288218669529833
  | 8 => 0xc52d0140ea6a628e80a07505314740503b1a90a3a0281d814851d0140e18a629480a0714531464050392290a3202811b9c86154c408dae430aa62045f7654c5310326a9ac4298819554d6114c408bce630aa42045d731855210237bb2a4290819358d5214840ccaa4b08a42047771595321023a38aca990811d9c4654c8408eae232a642061c6454d32102a6392a6990818b191524c840a98e6a926420659531813210334a90c09908193d95320c840c9aca990642046e7218d5110236b90c6a8881179cc62544408bae6312a22047776544511032ab1aa228881995895114440972e9306622046f725953110236392ca988811b9c8654c4408dae432a622063464545311032ca98c0988819c544604c4408dce5b28622046d72d94311025cba4c19088117dcd65484408b8e6b2a422045e73195211022eb98ca908818d1915148440cd2a4302422067151181211022f39eca10881175cf650844087aed2a4802047976952401030fb2ec6a008187d946350040c5ecbb12802062f651894010346318c4a00818dd976150040c6eca30a8020694631854010352310c2a008196d976350040cb6ca31a80205aa7290d4010335b2ec4a00819ad946250040d90c6312802059a739094010339b2ec2a00819cd946150040da6c630a80206d0631854010371b10c2a0081b81886150040d64a830a80206b2431854010358218c2a0081ac9086150040d608430a80206b061d0540102cc39a82a00816a1c94150040c9cc7316a99864e6358b54cc32b31cc3aa6619998a61d5330ccac530ea9986566358754cc333312c3aa6619958961d5330ce4c2b06a99843f7655054cc2a6b94c62a6619698d60153308deeca90a5986655258452cc23b38ccba16611d5c665d0b30a9ce52a265985c970d4932cc2673b0a499661715c4524cb30a9ceba1265986c93258032cc237b92c928e611b1c96494730c98c4992a3984777654451cc332b12a228e611b9ca65d07308dae532e839846f7259541cc236392caa0e614d5d25110730ccac528863986656254431cc32632a6490e61d14c95148730d9265b0243984cd7298f40cc30f2a0c6a066193d8f6255230c9ec6312a91843f76550548c32cb1cc02a46153dc954d0e30c72a8302871845d76d50438c2a7b92a821c6187d904354a308deeca90a51847776544518c237396cb20c611b5cb65906308dee4b2a831846c72595418c327b1ec4aa2618bd906255130c9ec6312a89865763d85544c333b16c2aa2619918b6155130c6ec830aa89865763185544c333b10c2aa261991886155130cd0c5b02a89867061d81544c21fbb2a82a2614b1c95415130a68e2aa0a89846f72584544c236392c22a2618e15160d0d308deeca90a49852c74548524c2b238aa4292618715163909309b0e0b1c849847771594424c23a38ac
  | 9 => 0xcc7a94a2a064d63d4a5150327318a528a819358c5294540cacc7a8ca2a065563d465150333316a328a819958b51945408bceda9aa2a045e7614d5150327a9ec4a8a819314f6254540c9ea6312a2a064c5318951502373b6a4a8a8193d8f5254540c98c7a92a2a046e761495150327b18a4a8a819318c52545408eeeca88a2a05577354451502aa39aa228a8159dc95114540ac8e4a88a2a065665d4c515023abb4a628a81599ca5314540acae5298a2a04777654c51502b3b92a628a81591c95314540cacca298a2a066665d4851503a3a9ea428a81d114f52145408eaed290a2a05567394851502aab9ca428a811ddd95214540aaee6a90a2a0554735485150333328a428a81d1d4c5214540e88a6290a2a05357418c51502b3390c628a81595c86314540ae2e0318a2a05667290c51502b2b948628a815c9c24314540ae2e1218a2a05737050c51502b83828628a814d5d06214540aace6310a2a05557318851502b8b80c428a81559ce4214540aaae7210a2a05727090851502b8b848428a815cdc14214540ae0e0a10a2a0745320c851502b93806428a815c5c03214540aaee6a00a2a05547350051502b3b928028a81591c94014540ce0a330482a045e75d8d415022f3a8c6a0a81179db53505408bcec29a82a046e75d894150327a9ec4a0a819314f62505408dcea31282a064f531894150326298c4a0a811b9db5250540c9ec7a9282a064c63d4941502373b0a4a0a8193d8c5250540c98c629282a065763d45415032a31ea2a0a8199d8b5150540cc8c5a8a82a065763145415032a318a2a0a8199d885150540cc8c428a82a065b53d81415032c29ec0a0a819ad4b6050540cd0a5b0282a067051d81415032da98c0a0a819614c6050540cd6a430282a0668521814150339a88c0a0a81c514d4110540e48a4a0882a046f725973150236392cb98a811bdc9658c5408d8e4b2c62a046e72d953150236b96ca98a811bdc9650c5408d8e4b2862a046e721943150236b90ca18a8187990530c5408dceb31062a064f53988315032629cc418a811b1d5620c540c9ea6b1062a064c535883150237bb6a418a811b5db520c5408deec29062a046d761483150333316a218a819958b510c540c6cc828862a0666621443150332b10a218a819614e600c540ce0a330062a067051580315022fb9acb90a81171cd65c85408bee6b2c42a045c73596215022f39eca90a81175cf65485408bee6b2842a045c73594215022f398ca10a81175cc65085408bceb31842a045c7558c215022fbb6a610a81175db53085408beec29842a045d7614c215032731ea410a819358f5208540c5cc829042a064e631482150326b18a410a819598f5108540caac7a8842a063664144215032b318a210a819558c5108540cd0a530042a067051980215033828ac010a81d214
  | 10 => 0x64d654c83290364992c0194811b9c863546408dae431aa32045e73189519022eb98c4a8c811ddd95114640ce4a2302832046e729963190236b94cb18c811b9cb650c6408dae5b2863205557194c319032729ac418c819354d620c6408bce732c432045d73996219022f39eca10c81175cf6508640c9ac72904320565719482190326b1aa410c811b9ca61d4d408dae530ea6a064f6298b53502a7394c3a9a81535ca61d4d40c9ea7314a6a064f5358a535032ba9cc329a8195d4d6194d408beeca98a6a054f7254c53502a6392a629a8155dc55314d40aa8e2a98a6a054e72d9053502a6b96c829a81935886214d40ab2e0310a6a051d7418453502a7390c229a81535c86114d40ab2e0308a6a046e7598a4350327a9cc521a819314e6290d408d8eab1486a064f5358a435032629ac521a819614e6090d40cb6a630286a045e73987525022eb9cc3a9281599c653d4940acae329ea4a05677154f52502b238aa7a928193d8e63d49408daed21ea4a054e7398752502a6b9cc3a92819398f5294940c9ac7a94a4a065753986525032a29cc32928199d4a6194940caea6b0ca4a0654535865250333a92c329281179db53549408bcec29aa4a065753d85525032a29ec2a928195d4c6154940ca8a630aa4a046f7654852502a7b9aa429281531cd5214940acee2a90a4a056471548525032732ea6292811b5da5314940acce3298a4a05657194c5250237bb2a62928159dc55314940ac8e2a98a4a064e6514c52502a739ec829281535cf6414940c9ac6318a4a05697018c5250236bb486292815adc14314940ad0e0a18a4a052d7418452502a7398c229281535cc6114940ad2e0308a4a054f7350052502a639a8029281179d663909408b8eab1c84a045d76d4e425022ebb0a7212819398f5290940c9ac7a9484a064e6314a4250326b18a5212819a14a6090940cb0a7b0284a0658531814250335a90c0a12811ddc565cc9408e8e2b2e64a047771596325023a38acb192811d9c7654c9408eae3b2a64a054e72d4d32502a739ea4992811ddc5650c9408e8e2b2864a054d7214c32502a6b98a419281539d5320c940a98ea99064a064e654c8325032632a64192819614e600c940cd0a530064a04b8745803250364992c0192811b9ca63d45408dae531ea2a045e7398b515022eb9cc5a8a81599ca53d4540acae529ea2a05677254f51502b2392a7a8a81d1d4f52d4540e88a7a96a2a05567394b51502aab9ca5a8a8155dcd52d4540aa8e6a96a2a07475314b51503a2298a5a8a81559cf64d4540aaae7b26a2a056672d9351502b2b96c9a8a81599ca63d4540acae531ea2a05667290f51502b2b9487a8a81559ce62d4540aaae7316a2a05567390b51502aab9c85a8a81d14c832d4540c9ea7314a2a064c5398a5150327a9ac528a819314d6294540c9
  | 11 => 0x86a7396c8a9843531c96454c21aa8e2b22a610d5b7059153086ac382c8a984347dd16054c21a38e8b02a610d4c7258153086aa38ac0a9843539c86054c21cb2c0302a610c5f7654c530863d380cba18431e5c065d0c218dce432c8610c6d7598a4308726a9cc521843395c66290c21c9ca6b148610e4d5358a430863db82caa18431e1c16550c21c9aa7b128610c6d751894308726a98c4a18439554f6150c218eaea30a8610c6e72194430863b388ca218431e9c06510c218f2e03288610d4d73d534208726b2aa7a10439354d61d08218bce7b2c8410c5d73d96420862ebacc72104317dd563908218beed29c8410c5d7694e420862fbb2a721043175d95390821caaa73088410e555358442086a6b9ea8210431bdd954108218daeda988410d2d74d4c42086a6baca621043c35525310821e1ca8a988410e4e6454c4208787322a621043d154e61108218deeab088410e4d5358442087a2a9ac22104339dd56110821cceeab088410e6753584420876329ac2210439954d6110821d8aa6b088410e4553584420872aa9ac31904393d95320c821c9aca9906410e5653584320862fb9ac928843171cd6494421c9aa73148210e4d5358a410862f3b4a6a0843171da53504218bceca9a8210c5c7654d410872729ec4a08439354f6250421c9ca63128210e4d53189410872d29ec0a08439654f6050421cb4a63028210e5953181410862f39cca20843175ce65104218bce63288210c5d731944108726a9cc4208439354d6210421e2ca6a088210e4d5398a3108637baac5188439354d628c421c9aa73106210e4e535883108726a9ac41884395595310c421c9cc8a9e4210e4c6454f2108636bb4a5108431d5da52884218daeb3224210c6e76d4d21086a6baca69084393d965348421c9ecaa9a4210e4e6454d2108726322a690843d11c55348421c9aa7b0a4210f455390521086723b28290843a91914148421b88e6a0a4210f455350521086f03828290843d154f3148421acaea18a4210e576594d210872bb2aa690843d154e52484219cced2124210dc67390921086b2bae649084317dcd64940218b8e6b24a010c5d7694c500870f324a6280438759253140218beeca98a010e1e6454c500870eb22a6280431edd95014021c72c8a80a010e4f5358a53d022fbb2a629e81535ca53d0f40a9ae529887a064d63d4a52d0237bb2a429681535ce52d0b40a9ae729085a064e654c832d023bbb2a228e816c1c141107408dce5b2e63a046d72d9731d0237396ca18e811b5cb650c7408bce7b2e43a045d73d9721d022f39eca10e81175cf65087408beeca98a72064d53588539032729ac521c819354d6290e408deeca90a52064d635485290326b1ca5214819358d5290a40a98e4a9a652054c73549329023b38eca194811d5c7650ca40c9eca9906520
  | 12 => 0x99643539d8534cb21c9cec29a6590d4e7414d32c87a2b88a699643d29c0534cb21a9ae029a6590f497014d32c86a4b80a699643539d7434cb21a98ea21a6590c5f7654c32c8762992c219643335ce62d0721c5ca83128390e4d5318931c86e238a6498e43b1589310c7218bee6b24a190c5c7359250c872631a64a86431edd95014321cb2c6a80a190e4f63d89548872631ec4aa4430fdd95415221ccac5308a910e6562987538862fbb2a629c431e9c26550e218f2e132a8710c7a70194438863cb80ca21c43475d05310e21ca8a6b088710d4f73553428871aaa0c2a14431b5db5410a21a9ee6aa08510d2f7454c428872aa98c299443179d8534c6218beeca986310e4e535883188726a9ac418c431edd95014221c3ec831aa890e4f63d89544872631ec4aa2439518f6155121cb6c7b02a890e5863d815448735b16c0aa2438ed906055121cb6c6302a890e58631815448735b10c0aa2439cd84605512187eecaa0a890d1c73550544869c382a82a24317dcd60151218b8e6b00a890c6f72593534870e326c6a9a438b1936254d21c68c9b0aa690e3b64d81534871c326c0a9a438ed906054d21c70c8302a690e5b631815348735b10c0a9a439cd846054d218beeca98a690d1c7454c53486ac382a629a431e9c365d0d218f2e1b2e8690c6d72d96434863d386cb21a431e5c36590d218d8eab148690e2c5458a434867238ac521a431bdc96550d218eee2b2a8690c7b70595434863c382caa1a431edc16510d218f0e0b288690c7a70194434863cb80ca21a431b1d56210d21c98a6b108690c7475584434871a2a2c221a439514d6110d21c68a8b0e8490e545358732486373b4a899243539ce544c921a9cebb1a6490d4e7394d32486373b0a699243539d8534c921c9cec29a6490d4e7414d32486a6b80a699243539d7434c921c98cba1a6490d4c7510d32487263288699243c3150434c921b8ae221a6490ce67518532487333a8c29924399950614c921cc8a830a6490ec7431853248762218c299243335ce62d05218bee6b2a8290c5c73595414870faa0c6a0a43871506350521c58a9b128290e3b54181414871c2a0c0a0a439314d62cc521a98ea9966290dc4714cb314861fba2ca98a430f1d1654c521a98ea9926290e4c654c931486e238a6498a431edd95014121a70e8a80a090d5873540504862fb9ac828243171cd6414121c9ac7316a810c6e7298e540862fb9ac12a043171cd609502187eecaa0a810e39545805408726b1cc42a0439558e6115021cb4c7300a810e5963980540871d322c02a0439698d6015021cb2c6b00a810e6a62580540873930ac02a043569c05494c21ab2e02a4a610d4e72d9253086ad380c529843565c06294c21a9ce4304a610e5960182530862f3b6a8a9843179d85454c21ab4e02a2a610d597015153
  | 13 => 0x63d0531c38a9b1a8298e2f54189414c7162a0c4a0a638ed506050531c70a83028298c7b76540504c69c3a2a0282635a1c950141318dee4b20a098c6c72590504c72731ac5aa0631bdc960950318d8e4b04a818c3f76550540c71caa2c02a0639398d6215031ccac5308a818e6a62980540c734b14c02a0638e9916015031cb4c6b00a818e6a62580540c734b12c02a0639c9856015031a9ae5aa68618c6d7598a430c637baac521863535cb5410c318beecaa08618c5f75584430c66bbaac22186395dd56110c31ad4e02a4a418d6970152520c786aa08729063715c44394831a9ce7b24a418d6a7018e520c6b4b80c7290631b5da4394831a9ce6304a418e6960182520c6aab8886a90631b9db54548318dcec2a2a418d6a70151520c6b4b80a8a9063535d74354831e1ca821aa418dc57110d520c6a739ec8a9063531cd6454831ac8e2b22a418d6b70591520c6b4382c8a9063535c743548318dced21aa418d667110d520c6b2b8886a9063c39d04354831e8ce221aa418d4d7110d520c7a2b8886a9063515c44354831a5ee8b02a418d2c74581520c6a639ac0a9063591c56054831a9ce6302a418e6960181520c637bb2a429063355c66390831c9ac72948418e4e6354a420c726b1aa5210631edc165508318f0e0b2a8418e4f63549420c72631aa4a10639954b6150831ccaa4b0e6418e6652584320c72731aa5208639358d52904318dced2928218c6c76949410c727b1ca4a08639318e52504318dceca928218c6c76549410c727b1aa4a08639318d5250431cd4a5b028218e6952d81410c735290c0a08639a5486050431c9cc6a908218e4d63548410c79329282208639399152cc431c98c8a966218c5d7694e310c63abb4a718863175d6644c431c9ecb2926218e4f65549310c727322a49886393191524c431e88e2a926218f4552905310c66a3b28298863a5191414c431b88e4a0a6218f4552505310c6e83828298863359da434c431b8ce521a6218e6765949310c733b2aa498863d194d524c431aaaeb1926218c6f72592500c636392c9280631b5da5214031c5cc9290a018e2d64948500c637bb2a4280638b9915214031c5ac8a90a018c7b76540500c71cb22a0280639398e62d5321c9ac7316a990e5a6398354c872cb1cc1aa6439a98a60d5321ce2c3306a990e5a6358354c872cb1ac1aa6439a98960d532187eecaa0a990d4d7398854c8733312c22a6439998961d4f218beeca98a790e595358053c8738b0cc029e439698d6014f21cd4c4b00a790c7a7099743c863cb84cba1e431e9c06590f218f2e032c8790c7a7099543c863cb84caa1e431e9c06510f218f2e03288790d597014f32c86b4b80a719643179d8534cb21ab2e029a6590d4e7395132c86e2b8ea6996431b9d8534cb21ad2e029a6590cce7614d32c86e4b80a6
  | 14 => 0xe5218a0a0d697290c50506b938c86282835c5c64314141ae6e2a18a0a0d707150c505069cba0c428283569cc6214141ab2e6310a0a0d717118850506ad39c8428283565ce4214141ae4e3210a0a0d717190850506b9b8a84282835c1c54214141e9264190a0a0d72710c850506b8b88642828356dcd4114141ab0e6a08a0a0d6b7250450506b439282282831b9c86054c418dae4302a620c5f7654c5310726a9ac4298839654d6014c418bce6302a420c5d731815210637bb2a4290839358d5214841cd2a4b00a420c7b70595321063c382ca990831e9c0654c8418f2e032a6420e1c6454d32106a6392a6990838b191524c841a98e6a926420e55531853210732a90c29908393d95320c841c9aca9906420c3d76952411063abb4a92088387d976350441c3eca31a8220e2f65d894110717b28c4a0883a318c6250441c76cbb028220e3b65181411074c318c0a0883aa1886050441caecbb1a8220e576518d41106d339486a088399d976250441cceca3128220ec46318941106cb39c84a08839cd976050441ce6ca3028220ed3631814110768318c0a0883b8d886050441dc0c43028220eb2541814110759218c0a0883ac10c6050441d64843028220eb0421814110637390c6a80831b5c863540418bce6312a020c5d73189501063dbb2a0280839658d5014041cd2c4a80a020e4e6398b54cc72731ac5aa6639698e60d5331cd4c5306a998e696298354cc738b0cc1aa6639698d60d5331cd4c4b06a998e696258354cc61fbb2a82a663535ca6315331cacc6b08a998c6f7654852cc734a92c0296631e9c265d0b318f2e132e8598d4e7295132cc6e2b8ea499663339d8524cb31b92e02926598d4e75d0932cc762992c219663335ca63d0731c3ca831a8398c6f7259250cc636392c9286639318932543318f6eca80a198e696254050cc727b1ec4aa46393d8c625523187eecaa0a918e5563984548c6a7b92a9a1c638d5506150e318baedaa08718d4f72550438c70fb2086a94631bdd95214a318f6eca80a118e4f63d89544c717b20c4aa26393d8c6255131cc8c5b0aa898e5b63d81544c735b16c0aa2639a18b6055131c76c8302a898e5b63181544c735b10c0aa2639a1886055131ce6c2302a898c3f76550544c696392a82a2634e1c154151318dee4b00a898c6c72580544c71a2a2c3a1a631bdd95214931a58e8a90a498d6870548524c70e2a2c721263351c563909318f6e0b288498c7870594424c63d380ca212631e5c06510931c9ac62908498e3454584424c732292c221263539ca544c931a9cebb126498d4e76149324c7273b0a499263539d0524c931a9ae02926498d4e75d09324c6a63a88499263c3150424c931b8ae22126498cd675185324c72b3a8c29926395950614c931ca8a830a6498ec742185324c762210c299263335ca
  | 15 => 0x687054f5250727b1cc7a92831b5da43d4941a9ce7306a4a0d4d73983525072731ea5292839358f5294941cb6a7304a4a0e58539825250735a94c12928396d4d6094941cb0a6b04a4a0e6b52582525062f3b6a6a9283179d85354941cb6a7b02a4a0e5853d81525072da98c0a92839614c60549418deeca90a4a0d4f7354852506a639aa4292835adc15214941ad0e0a90a4a0e4e65d4c5250636bb4a6292835a9c25314941ad2e1298a4a0c6f7654c52506b5b82a6292835a1c15314941c9cca298a4a0d4e73d9052506a6b9ec8292839358c6314941acae2318a4a0c6d7690c52506b3b8a8629283591c54314941a9ee6a08a4a0d4c735045250696ba0c029283539cc6014941a9ae6300a4a0d6571180525062f3acc721283171d563909418baeda9c84a0c5d7614e425072731ea5212839358f5290941c9cc629484a0e4d6314a4250732294c3212839514f6150941ca8a630a84a0e6752185425063db82cb992831e1c165cc9418f6e0b2c64a0c7870596325063d386ca992831e5c3654c941a9ce5a9a64a0d4e73d49325063db82ca192831e1c1650c941a9ae429864a0d4d7314832506a73aa6419283531d5320c941c9cca99064a0e4c654c8325072a29cc2192839914a610c941968e8b0864a0ec53258432507a2298a5a0a83c314c52905418dce531ea0a0c6d7298f505062f39cc5a8283175ce62d4141ad4e529ea0a0d697294f50506b5b92a7a82835a1c953d4141e96a7a96a0a0f4853d4b50506ad39ca5a8283565ce52d4141ab6e6a96a0a0d587354b50507a5a98a5a8283d214c52d4141ab4e7b26a0a0d5973d9350506b5396c9a82835a5cb64d4141ad4e531ea0a0d697298f50506b539487a82835a5ca43d4141ab4e7316a0a0d597398b50506ad39c85a8283565ce42d4141e9264196a0a0e4f5398a505072629cc52828393d4d6294141c98a6b14a0a0e4e63d4a5050726b1ea5282839398c5294141c9ac6294a0a0e5a63d42505072cb1ea1282839a98b5094141cd2c5a84a0a0c5e76d4d505062f3b0a6a828393d4f6254141c98a7b12a0a0e4f531895050726298c4a82831b9db5254141c9ec7a92a0a0e4c63d4950506373b0a4a828393d8c5254141c98c6292a0a0c7b7654050506adb9aa028283561cd5014141ad6e4a80a0a0d6872540505072d32ea6282831e5da5314141ad4e5298a0a0d697294c505063dbb2a6282835adc95314141ad0e4a98a0a0e5a6514c505073532ea428283d2d4f5214141e90a7a90a0a0c797694850506ad39ca428283565ce52141418f6eca90a0a0d5b7354850506ac39aa4282839a9945214141e96a6290a0a0f485314850507a9a9e8228283d414f4114141ec6a5a08a0a0f6052d04505078c29c8228283ca14a4114141a72e8318a0a0d6a7218c50506b4b90c6282835c5c46314141ad4
  | 16 => 0xcb38b0ac02a0658b9526290c32a3ae9298861951f7550c430ca37baac4218658795263908328beeab18841952d74948420ca97baa8421065555c454cc832ab2e02a6641945d7694e320cab2b88a9190655a5c0548c8328daed29c641945e76151320caaab88a899065565c0544c832a9aeb212641954f75509320cb872a084990651b9d8544c832acae22a2641956970151320caa6bac869906553dd5434c832e1ca821a641964d75d95320cb273b6ca99065539d3654c832a9ae3b2a641954d70d95320caa6bacc89906553dd5644c832b8ee2b2264195c471591320cae5b82c899065721c1644c832d1ac832264194ce76d51320caa73b4a899065531da544c832a9ce92a2641970f64951320cb86324a899065535c6544c832a9ae12a264194ce76151320cae3388a899065715c4544c832b94e02a264195c970151320caa73b0a899065939d8544c832a9ce82a2641970e74151320cba3388a899065535c4544c832e8ae22a2641954571151320cba5380a899065535c0544c832e92e02a2641954970151320caa6bacc29906553dd5614c832b1ee8b0a641958c74585320cae5b82c299065721c1614c832d8ac230a641954d75981320caa7baac09906563dd1604c832b18e8b0264195c771581320cae238ac099065b2580604c83299eec996a2196c932983510cb64992c1a88655c9c35194432c9eec992a21964c764c9510cb2632264a8865d1dc53254432e88e2992a21964d32d81510ca67bb264288651ddd9511443299eec996a0196c532987500cb62992c3a80655c9c75094032c9eec992a01964c764c9500cb2632264a8065d2dc13254032e90e0992a01964d32d85500ca67bb264280651edd95014032c9ea6b14a7a0c5f7654c53d06a6b94a7a1e83535ca5310f41c9ac7a94a5a0c6f7654852d06a6b9ca5a1683535ce5210b41c9cca99065a0c7b7654050d062fbb2a629c839354d6214e41c9ca6b148720e4d5358a4390637bb2a4294839358d5214a41c9ac72948520e4d6354a42906a6392a699483531cd524ca418f4e1b286520c7970d943290727b2a641948393595320ca41d8a64b086520c6e7218d5090636b90c6a8483179cc62542418bae6312a120c7b765405090637394c1a9a831b5ca60d4d41c9ec5316a6a0d4e7298353506a6b94c1a9a8393d4e6294d41c9ea6b14a6a0e5b53982535072da9ac129a8317dd95314d41a9ee4a98a6a0d4c7254c53506adb82a629a83561c15314d41a9ce5b20a6a0d4d72d905350726b10c429a83555c46214d41a3ae8300a6a0d4e7218053506a6b90c029a83555c46014d418dceb31486a0e4f5398a435072629cc521a831b1d56290d41c9ea6b1486a0e4c5358a435072a29cc321a8395d4c6150d418bce7306a4a0c5d7398352506b5384a7a92835a5c253d4941ad6e0a9ea4a0d
  | 17 => 0x8685559c46294e42aaae2314a72155a7018a5390aacb80c529c85539c86194e42caac230ca72154e721825390b2cb00c129c8555dc56454e42aa8e2b22a72155b705915390aac382c8a9c8547dd16154e42a9ce430aa721655611855390a8fba2c0a9c85539c86054e42cb2c0302a72145f7654c5390b26a9cc521c859394d6290e42c9aa7b12872161d6594f4290b0eb2aa7a14859359653d0a42c9acaa9e852165a539835190b2ca9cc1a8c859694d60d4642cb2a6b06a32157270d465190a2ebb4a628c8517dd953146428eeeca88a321656539875090b2aa9cc3a84859594d61d4242caaa6b0ea12157271d425090a2ebb4a62848517dd953142428f6eca80a12145f7654c5350aaa38aa629a85561c15314d42c9ea6b1486a1477765445150aaa39aa228a855c1c151145428f6eca80a0a1558735405050ab838aa02828517dd95314c42caaa6b08a621659535805310a1ebb4a9210851b5da5490842d1ca8b1c842158e73d914210a3bbb2a2288859558d5114442ce2a2b00a22147b765405010b2cb1aa0280859c5855014042c9cc6b16a99943f7655054ccb2731ac42a6658b9516290f328beecaa0879951f7655043ccb0fbb2a821e65875506350b328eeeca88a39947b7654050ccb26b1cc5aa4650fdd95415232c9ac7310a91962d54189438cb0f2a2c7214651bdd95410a32a5eecaa0851962f76550428ca3bbb2a228c651edd95014232c9ac6b16a89963764185544cb2bb18c2aa26599d886155132ce6c3b02a89967061d81544cb1db20c0aa26596d8c6055132cd6c4302a89967361181544cb38308c0aa2650fdd95415132a68e2aa0a89953870550544ca3db82c22a2651e1c161151328eee2b00a89947471580544cb162a2c5a1a65551c554d0d32ab0e0aa686994ce7598b434cb273acc5a1a65335c662d0d3299ae1316869945f76550434caaa38aa821a65561c15410d32a9cea31086995c571188434cae4b80c421a65331c96110d32998e4b00869961c5458f424cab238aa9a12655a1c154d093299ceb31e849964e7598f424ca66b8cc7a1265335c263d0932a9ceba1e849964e65d0f424cb87aa687a12659399443d09328deecaa0849956471550424cab4382a821265539d46310932b8ae231884995c97018c424caa73ae8621265c35504310932998e6b0884994cc73580424cb473208799265a3990428c9328eeeca88a29953474544514cab8382a228a651edc164145328f0e0b20a2995557110c514cab2b888428a651edd95014132a70e8a80a09957071540504ca3bb8ac8282651d1c56414132ab2e0218a09956970108504ca3db82c32a0651e1c161950328eee2b04a81947471582540ca1fbb2a82a0659598d6115032cccc4b08a81967261980540cb38b0cc02a0659698d6015032cd4c4b00a81967261580540
  | 18 => 0x1400000000000500001c00000400602901100400200b00900600100000c00100000000e00600301e00100200000a00000001100400200000300600a00500200d03202200404f00000001b00000300000200000600c00800000000200100100000001500600100100003200100200600000001500003201e00200100b00000000000200300000000100300800002300b01900500401200200400000100000100900300800100400a00000000001400000600101300400700200800300600501600100200f00e00100300c00100001300300500a00c00500000100400c00500100000600a00001b00000d00300d00c00000700000201200100b00000400603700100601c00100800500500100d00100000000400000100000000400000100300000600100100101200400400100c00000000100100402500700200300601202700800400a00600000500200100400000200301200000400a01400400000800000700100100000000300100c00001800300300800000300000100c00306f00000201100400300300001b00900100d00c00602000900300700200a00000000100a00000200800000500000001800000602e00101900100400d00300000100000200300002300000400000c00300401700300200300100200000000000200100200100200001100400800000200100300200000b00000501200200200f00100201400002200500200201200100700200500900000600201400700000f00000500200000000100a00200c00401c00600b00400100000500400001900600c00400500000400000000100000101101000000100b00200302600000100000900401303c0000000170008deeca90a5a1c777654451d0e3dbb2a0286874b5d74394a43a9aeba1ca521d667118e5290eb2b88c7294875a9c06394a43ad2e031ca521d4e731865290f32b08c329487539cc6094a43cd2c0304a521d2d75d0d5290ea6bae86a948759dc56454a43ac8e2b22a521d6b705915290eb4382c8a94874bdd16154a43a9ce630aa521e65611855290e97ba2c0a9487539cc6054a43cd2c0302a521c6f765485290f35294c1a8c879a54a60d4643cd4a4b06a321e69525835190eb9386a328c871b5da52146438deeca90a321c77765445190f33294c3a84879954a61d4243ccca4b0ea121e65525875090eb938ea1284871b5da52142438deeca90a121c7b765405090e37bb2a429287591c55214943ad0e0a90a4a1c77765445150eb2392a228a875c1c151145438f6eca80a0a1d68725405050eb838aa0282870f5da5490c438baed2a48621e8e5458a4310ec7396c8a18871bdd95214843ccaa4b08a421e69525805210e3bbb2a228887995895114443ce2a2b00a221c7b765405010f34b12a0280879c58550140438beeca98a7a14777654451d0a3dbb2a02
  | 19 => 0x6e164a1930000ba53449755f49848e026cd4f403fce3462c5b0a274836bd03ed0000a460001c4000164c0000000000eec21c5f200000006f34b2000137c58621d8000e7ea1e000092ccac29e0aa06c070a143043aa493105873bf1edc92a6400548d1877600200100000000000000000f00200500001300100600100000000200a00000000101c00000600000000800300800100000d00001e00100503400500000000000900000300200000100600a00800101000100300100000600100400903600104700300a00400600200e00600200001d00100603900400200b00000700300000501800d00000000000400000200100300000400200000200400000801700100000202100100000000b00100003700600f00300000000400300401700100000000601802001d00000400200000600100f00c00000000101200200e00600200e00000400200104c00000200000200000100000000b02c00a00000003000a00300200d00800300500400000000200500000401000000300f00300100a00500d00000200100b00000000a00101900800000000001800600001400200100600102900500000200001000400300200101100100000400300200300b00000200100000500200000400200000200400500200800601901c00500000600700500200e00101200300000702100800500300400300a02900900701400000000a00000501900000400001901000401700800601e00300f00300b00e00400000300f01100600100400b00b00000300500600300000000a00800000800400300b01400900100400000000000301e00000801b00900200000000b00300200600200000000000800300100301e00300000000300000001700000500300600002000000401300400000100000500001200500700000400300600800500000200000200100200800600400100800000800000500100000300300700300000e00200000000900a00000000000000200100500000700900e00100000500100e00c00200500800500400c00000100000d00900000000000700000000000400000000500100500b01200000000500000100000400000600700800000000000400901000100300000100900000d00000201000100100000001200000800900000000100c00500400000000500000200600600100600600400600f01300300b00800200b00301b00300500300100000300300600100000000000300700800d00100a01700100100000000100400600100501f00f00700700300200a00300300000001e00b00000500400a00000600200100000100300100000000000100a00000800800000400100100100200400501500800000300a01500400301d00000000a00100b00701201000000300400300d01b00400600100000400100300300300000300000400000
  | 20 => 0xad000020500c3e325d00313385520002fb95a477002b8b6d4be00040d80005b4000034addc0000200002a4c0000000000f708ca00000021f0000b805168000a1c0000000000ae80000578000000aff00000009480000000d64da82de00001c875a2ce2f300013260000000590994a64346187011e71b00000002ae8ca22b90943220981d988e8c70b974af23200fe48f1a9a02451268036580c12f01d926b14b81668fb000001c0000003ef80007de1020000000ba800000029780000003882dc435830c0000cdc00088900000001929030000000cc23a55702614f1087f28318a48426f809d2b9d02cae854100014de2cc0001ef92fa0000000000ab8acc0000018d8430123aa96d634966472200c34243f0000000000ac017b1f112d40004e78000b4400000000000000005000895534b114c5135c5c849e00013311d002b363a234c5cb7e29893945b87f72cb2e857c0b521b098f40000002798160b720e8455800000030958a1854de2874477885116a04800015689260002460280000000000225176a3bd270acdcee690f471223ca1e0001010dad3a858f49f8000e562070001ec085638d478ad58de00004892ed80000d400023306a828a4b900003968f700000002b08c40000920620a2e049a9a89247e631092945201691f729a10ca9d85380050d34090107269d2dc000569a2e95e60001eb27d542616f0ba11d8fde0000912de43e835a333a32c0007d70a6800023a7f454382685ee85c10f17bc0720000001d8cf2876d4c301bcf387b44aca9400006ea3de1b1014600026f8e4c0009ce5d48eb09005a320e2ae48905e72e50000f8c84d3d7805891c2c71b12fe462890b52c869c6646480960000f1613050c8ff95443af17f97800000000e600000000000002cf800000000019e57581fd2ae88653fa2420ef0aa000070921f23940000000000000c263250000e6466070e519a354712af200012710ba000000000000008000000010ce000285800000009c0000cbca9499a0da83948320bd3502ffc00039c0002ad8a0a9405580ed16e05b05109cecf7e6e25ea83480007e923802100004e01b500000000a709881281b08c509e81e866808e12c27e4d7225b59c27a945490c23e2b441a024c0ab000000099059e292cac000014e863cefa6954fd00001f475745d87e00000000168ea400031b00000000000003b0a04c4b2509025a3e40000000000000a8a00034a277c94e1a300007bd68440502385756088fe000235859400a3918c002362393ab114d2b079959a80000000004b8800124e4070b38aac78cbfb2f10000e5430b00009cd7c6000358077d44eb9f555172420c6d23701008e380004d19d444ce05d49085e8f0c49638f9b28dfe84f11a92983081144059ec41d4bed37d2e408846340001fa8c6a12721b2cb844eb7d0
  | 21 => 0x55580008d42861821eecc9c7b9090a6d55403c51d0018c45c88600000000000000000001794000452000122292a1cb8000f1455032c0b8c0000000f308d85c06aa0888acc9402dd0000001786afa52b00003060005d7194c00014a00000000006920001894000b4f00005f8a242ae038120472800051595c077060e42b80d4cbabb145f0fb0bd0b8553c99ed028b280999f942d49dd0b880243b639a2e5940cf084c308d11405f8ae241f9e84bb029313019bcc0433125116555f874146f8df5614bfc4182d3000010957f1cc97fa63f2e709b115e4ac5c5098c8b452d2951fb809c75f19a831028a0000002ee800000000000001ce00021c9a0864c1f22b69224016b471b71e9c9dc6882c72b3c1424b33cd8940e980000000000640000000131c000000278173000000000008d0874bbb44fa474f1a95142727e00001ca000000020238c55790f0f489794f700000003e042315b0000000000000005800028c80010d8000000000000070859d04704784fd00000010c647a00000bc3f88a707000009cc0000001ec93044cd3939d48000923422a3f13f68d12aa30087a092843c8fb40003bc3629998350b0237d800140442e1d30f6800000000000016b83e517ea8ec000a470000000dd25655da1c0cbf048317896f939200020f1a2c7220000001944a6400043680003c8b9d4d2af5809a00005a0b00d9c5da5b116d0cf856719d9ac4ea86e51002fe800000005d9a4497a2a4000000000004f000000037854e5149fd8d52b6700f9c1400006a50b05ac57242206a8000eb800012e00011140005029628000000000000000030d14601111f0000485152000083a5f12f0178e95f00019c52f89e1435adb02ee0004e32ee129e00006ba798f0e5920000f282401b234293b40000000002f607a444b32d80000000002262364000824000000169238444009f44ae0000e49620bf84184e0ae049783d84cb99c9468a6506b000000015252a80003304f91441eb816e54400020c4f9089b1bc000057400032594793844641ab00012c29bc00028110ee855000000137eb6e2eaacc0c303c22ab91345b298c2d300000000000f414a507ca8829c2ad458a2bc00017441b400014280000008480002d604dc08500023811fab3d000000000000021ea54c17e0005d81a61056a44000290c73600000000010b02b2007157d03e7f852b82d52929094dd1cbcfb066a015121000000000000014f825f000102c81c21700000009ce0000000aed1ec6de5ed82c800000029a0000144000008194927200051a9a1d72c6dc4d01e3d7c26c01fc9d4ccbe6640f82ce479e140460288c00000052d03440006db1560000000000356000174ab3435f2b204300942452468540907000000100e1f546d9268d70153374127c000a833910f2146241659000008a879e41a0000
  | 22 => 0x46d04b94fc269456a1508de19c3c0800132400000000007568a213d18c10140f157d8aa92105f658d9de11165a51e48524c980004d4a5040000002de800000000056c00000008470000000000b6f0cca7bc3ac5210322764c748912b505200004c82eca830e8a35b2cf800017c95d1b9b0007f033a000000000094e40d0e74000ae4000047803a1fe5be26c832848b36f800034a9b642d10917a69f03a1800124000002600000002e54b410d446634c2da814c00013c0f49e7c3d88dd00005ec00089000008800009955afac3ce0039f3e289f150249d0ba98b547c69d0da164132c3cb364a03cd1eb232189ab46c693e40080003046332800000ed4b7450e0dd4852128000009d7a400049d02e08a217c54689980000001c5800142e5614d5966c00090626c8c54aec2ee44aae98008989339ad28bd2a4e1f42d0036c24a28d262d6268a900015000005d34a308a115c00000002ac00000000029d80009b40000000000a841392e2400005400000014ce63700c800039a0001e0198c0000005d1000000031f000000174e4d322383d95c275a4ff0814a6c0002a61a401620e95c317c06ee63c37900016440002c5869164e00011529b000056e53d9824bbc2680000fcc8888b00001e5433c0d3000112889c18a0000001106a450000000b703bf30d0c4400031835a84ac68233800000440005ac4e38e4085400000000000f87202c8a4c00000005780088b6651d0b7125c0008b849b9b5939a0000228000d5688530e88982267fe15c2ef00008711a6a1a4066b1e00000000009c4196902519e46300000000004da3c901640005635fb287c6c000000000012a00ec0000000ab06d13d40000e4232847300011845ec0000cad6d08a300000004425aa0001bf40004bf41797c46bc00000000006964b711b800000075d4588000822853000000072ab2d3771cd00000000e1814800000040a80004ba000406000000065a000000085abc1530a81ca603f1525151d3227c20c483bc06c9630001e99574b5d0f710a00c4a102789ded3d2945241186c6ce5a115a259c0000000d9aa654447c05058950980aec0001e2565465e2f9800000000029986e8de8a5c11e9600c165772e185703821e01a19a943fe8380b98a39078b9200007c403806c55f8000252a730002d1142a85b4088000b56bd7000000169064f121875c44858114e126d6169e50ed190cc024ae0c2838554a95435e9f50b8e3a34262c5436e92d00013080009d14140ca8000000007800000053d00004d000000055d86692fe3271610e1d2768fa000065538a08d318a1588da0000002a4000091b453000000010f3d1800125c89900000015b83de4f895251e80000002dd56860005d52d5c000537260a9d04206a60001b6479a89600000004ec67f0000001248b174380000fc0654
  | 23 => 0x45c80000004e21a1000070c2010000178b9e0000000f7c0b87024d20df886000000006f95f242f2a89e397ce0002ee0f50030abd0ce9e4c53637126584647e400055400011c681d0a88000f9a0001cf20b08149af27f1b4ca765104300124cd24a100000017260001df0000a380003f08d1c0000000000a488340001ae1f54eb09e755180003a62080002230000ada17920f56643453e712d961c5ed0522bd80dc107147aba578c25a40900000000003962f3c9540000000000000000000000120275e221abb53ee6052cc93a00007b53a000000000000000000000000109a98c0d0b5143c0000f965782af25488189f23431cb80000000001fe4e4a0001db26ec00000039a9f0d17e000120800000000000006482c6082097800045e55b00000000001cf1d700002640005b51d94a2c8ea18e221c0aa00000003d544a2820000618ca02f813581053e6bc455317757961eb00000010a23dd00000000f09d71c78f100002c4000057d48000056529b8b044980002960000b5e5a298d80007d141100014300371edaa500008420be800081a0ce00028e4c4e0002b4087570486f0aa9c4c57c000556209cc7c00000005b523c79d0d5a34c5cc2a62fa84900007ff0002014e241f914c1b9c9f44d1256800137000014000000000004a62f98000000000000000000000005c853e1c445b00000007980000000cd64d53c885e00e68ed00008885d866c1c127ac12ab8b0ea800080c5d206f97fd58e00014b0000f82b9a3408cf0fd81d81160fc15482d500009a97a80002671e684e04882548ea8ac44265402de06580715b68a1c000888000074970600000010800004d800009012b800048fa5bcbe848d39b86047c49d206522dc0002151a908ecaf8000388800035e0000001ae8c227d3000000167600000000000006205019b90d320cf5a6894400089c1f3a11044620b141a8347a654f0129310ab23654c20d2821a93515f800056e2383b30b406e80893999928c4600010b00000b44135aa1afc82ab030e28d7cae65f73c2a294f0400058419a0106b4b4d89a341e67fa03091540000000001f780261003a3980d6180dc0fd1f300007715cd953466c0003c600000002ef00000002f2b63176a3fc00074e44f0454000be500002485a47c74b680009ea2560000000000a1206c85940000000001d080e87290000e485442d40b10000ed000052980008c22d65101ff0e9a70b5ee8f0c8ba84a5deae786f669f5802f3124abab0a6121562c37c43a87517462032db8ff01bc3d73b91350fd684959f8ab4ece9cc07bade848e1e30619c3c67c9760e7266cafe14212f1db89627555078810000a521c01988d38a1b4b9981cf74a2c25902651245fa2df9374000396597993400066d442000137200013c800054eac202fab592acae303e8a34000000000189
  | 24 => 0x6126650858480009725265b4997000015a0001454b1282300004584e800000013140000000000430180a894ea9ecceb2b0d32121cd78434917a8e8522808831da9c91401c23baa3ad73896c18127400101ed5430d5d032a112bda7d87aa33d474a9ad29a4404ff80000c068e0bb041432e441466a52c67287603380045860004e196817ee5022f22ff92c4a3c35d946d30690201493416c00f42dd9bf13547d243419240000000e300003000001ae9f88ade09f38200011ae0002850000d6c00000025d00786441631c545608411088ad4c64bbf37baef939030800000006800230002e2171c9cb3329784c3c4e45d2000000000037781acaf242723101d510400054c0c7400071e0000d600700170002b245d60003c18f9975e41d0001a58c1a0c14071dd000021258faa5570e9420758ed4000a084081554418aee21b9a4ca865c41909fb40ee4001a7abd000067a57a80005a276b0002164b06bde2c200000007a5000049849aa7a0d50d986068ee456066c62e90e5cc9180be46454a18e0c2548400001ddc8bc9ac45a1f74ef2714323916ca6ab5036b9abc0fc8de08510d0000a370011f916581c73968000508000000244c6a28f0183a51d464716072000137a1bd4308dc0ef897b0000000000aad3f980000004f62360b3d4ea9e02092698df2a2f1bd0ac483e5ba12913e0b84b731b20b4d2ae9b3437258048c3442d92b15498639545044953c00054e12d0c1e23f5e72d945c200006380000008b246726016200004540a04c50b76000187c97c19643306b97e6bd92cf03f4ad6b8f18b24b147eacd1921d8024647e56083350be24f18500695b2a85001a12c3ce4c610d2b55040a9641a94301ba401000000105ca6000000011a40002eb00c80845074b480013b65d030b050548c0400000000116a3d1299a280009ca0a2178c00003b01d1c980000001f4a2f4cc04330b091fc000000000086c8205b121c2a6c7d602625a867cacc5a74e9800036261400012ecb1a74b00008340000f80001c30afcb1250a2188ec400043200005e673a2902b6ca22a2806583e5542000148800000027717ca25d41c00005807ec67e015092936c00000055480008b2ab75d424f4a743684d72788d36a6937a9d20b8a9e3000230400022b00015c469c19040e000012c33349914115860000001460000852002a76800048640400009d64b01c500a095697a2a98dbcd4ea1d3d48278bd472835a2d541741172cc1cd88ee7f13021669186ab41892ac49ee66e07dadfd6307a058c8000fe41ad0f086980241a913080005f66eb00000000003552392f145e06b300021787fa3230001d2800097e00023b152e26449329095d40003ed8af49f83762648795102684032abad4a80fc1faaa7c00000058319d800000030325548d600023ca410000000000000000000
  | 25 => 0xda5788a684fc00052e80011b09ad60180001e0adf13c2b744882620000de423e00038b80000000000001eb4000466000195400012d42194ac6d80005958000aac000000000000000049104f9142000000000054200000000000003055d9800180280245e1c645c49a117a000133253e2b208a4a283fb3f1a66000000035105b0ea0b211910078fac7b80002988a8237228faa2c2b60004c780000f620614ca0114a2ad024387ccb3a13b1bf89c427e5ad000143437600048b2e34b18b1d06d8f0540cb6409c0b340001dc01fa9b47c87964282638d9e1603f400001cc917000111933c18754e80013bc2fa2ed8000b48a0100016a00000000001e011e400000000007c2000054000047c53c00000005d40000a78b04b5ebc81659ead0fa000000275800045c08706348dc42c0001ab8a025fe2b49f7133a01b2a300d0fce98100024c4000ab81ff9de9232bb92e30000db095b00019d000000058280014701d13590000000b293de80000000002cbab5caea00027da6dca5e7d015480009c600058e24715782300001e880007464a50000000000000000149a2af000000175a38e1271020702ade30402e4bfa99410499d4c560002a11c74a58ac43f8105c0009382eb84d4afa9e40eea3182728320001b04a720e2524000088a0000001898d0615911913c95de09100000000004a32021cc52ee0000880c1966cae600000000006a34c38ba007a1040fb97eca500002e0a2a8ede622254239d2b4000187251103009b00000017de6a4291051c0000500000000000000000293d16641457b92e00009650e0224d2002d70840b20000000000100d2d66f6000021913000000000010f60000002a9c00040f2e400000000003448e8903c69714a82b80002a30000540cee0ac1f500000000003680d200004cf3630000c8c00017f0001360b33559ad181786e1406952cfea00000000016b63d154600000000000dfa4d83d43ce48a82a8b9a000413000148200035e0fe8cf098d0001f3c4fe4d2495afc4000b911cc20ed7d8000000226919247b548ab2d44cb721d92e103ec73022f9864d86bea46386380006a141cafc80ecbc907f28e96b22551a806308e675b4708c3cfb2749079289076216829387409bc20f3d6009151c14b538ab500cc00018cae54a487aa1fa0000e0c0002bd292400000000000000008f51fb8000bd6b7b1d3a0b4e4805623eadacdda7c913680b8c544af1649e5c198a0a0001add43467d23c0ad8e0e2d85a091a077265700023cc76e0a500004d97401880218a5cf6c3b01ecac902bc11803c8144dcc9702fca05c89e10317399c0892b8c53e80015640004ee115969c82a43d237029c36d5ef95c8efe49414a24a4c5e00027628d8d3c73e0001fec6343c700019648e26da0000000c142455d9042d79a0001e6164c2e045239e91
  | 26 => 0x43e6000188c7845a8005632084bcaabe2ce24bc65c82900000004cab6600000014127ca000000000051746816d8cfc8d43b21ce093200000000017ea0c22ca0000e9e53f2e029992201c8277a1f86521374f621c8dd800006324d14ee82500010c8c186cc57c2520516739124800135006d00000002fe0461050a9576e0005f59c28190bf0518000000046911880001c63f62d4a7b412e0005ee2b94bbe4e930b82994fe03e00000009d4525000119c4f64f4371803559c00039e02d884608c5570000e3099f1b48000ed24910c58ea000070d00027016b40210a327f0b786dd3640688b0a6105e88e9037200024803144ea88e48c00000000000b30788bdcafd00000000000ee3a200003400005fc1ff56a60003b620dc1140000002e605be47404e80009fe00002daa3cd50a78320a0cc0008365988c4d7e89f40000000f20b0136a93700000ed482a4f172800000021a84de90d2898000b5cbe81dd1bf960eb
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x544c832d41719c0544c832d42715c0544c832d41715c0544c832a8484584614c832ac080584614c832a8884580604c832ac081580604c832a4980d95320ca41c45625c46214d41c45635c46314941a44854c9610c941c84744c9610c941930845c43214141d41325c43214141aa28290c6050441a92839086050441a458298d6115331949809d7424cb31949801d4424c931d04545c4424c931e0454108614c931a28845806054831a458198d5290831c84641c9414c43194487549414c431e0464549414c431c90641c1414c431d41521c1414c431945859ca434c431a45839896115321c46765c4534cb21d41719c0534cb21949809d7434cb21949801d4434cb21949801d4434c921944855c4434c921c44655c4434c921d04545c4434c921e045410c614c921a18845806054c21c45535c66290c21c84641cd41484219448754d4148421c447654d4148421e046454d4148421ca0641c14148421d41531c14148421945859ce4248421a4581d95320ca40a458194d620c640c45635c65208640c49625c06214d40c49635c06314940a48854c9600c940c88744c9600c940930845c03214540d41325c03214540aa28290c6150040a92839086150040a498298d6015330945819d7424cb30945811d4424c930d08545c0424c930e0854108604c930a24845846154830a498098d5290830a498098d5290430a4586949310c430c45635c65208430a498098d5208430c88641c9404c03094887549404c030e0864549404c030c90641c5404c030d41521c5404c030949859ca434c030949859c8314c030a49839896015320c4a765c0534cb20d42715c0534cb20945819d7434cb20945811d4434cb20945811d4434c920948855c0434c920c48655c0434c920d08545c0434c920e085410c604c920a14845846154c20c49535c26290c20c49535c26290420c49535c2620c420a458194d620c420a458694d2108420c88641cd40480209488754d4048020c487654d4048020e086454d4048020ca0641c54048020d41531c54048020949859ce4248020949859cc2148020a0c8454d6214d10a458214d6110d10a498214d6010d10c0c7458d5214910a45831496110910a49831496010910a4581d95320c910a4980d95320c91084c87595320c910a0c84595320c910a498214d60cc510a498314960c8510a458214d61cc110a458314961c8110d04731c95410410d10731c15410410d20721c15410410d08731c95410010d10731c55410010d20721c55410010c90641cd5444010ca0641c95444010d11545cc5444010d21545c85444010a908458c6344010ac08258c6344010cc1635c86344010ca0649ca4344010aa0845886244010ac0835886244010cc1735886244010c90649ce42440108b0845d83244010ac0864c83244010cc1764c83244010
  | 1 => 0x371651c810e9680000000006a0a04044e40c011841c03440dc7e10268000000000005a6300024282a1a124246510210d2513a8686c002f08c2e254395cac8540004982e00060e83b2e9c0160d21000386f3e03c00002a90c4254001fc7a7632234003013814da5c30120cc003d14d0c89250a52082221a1141f19000a0792d9dc00003f000584b000ac003a1119c003c00000c4584601c8c8f000548a71270c4d847458902c523e811064113000be333c06c722f14018806b3500000133993c3c380c9ec7c00190201091209030903000107080a000703010400050002000101010208000014031103020303000301080500030400b04815504310932b0880550431093294b805c7654c832947815c3654c832a8481590644c832a8880590644c83294b805c6544c832947815c2544c832c0e769d
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x4804000060501e00040b7200069c002140c018010080c02428e8992c219283900844c9710c8505070090e322a4a0a6218f00191521c1414c431c02438c8a9a8290843c006454c70505210870110a3a264b0064a0640211325c03214540c04438c8a928098061c006454871501300c30110e322a6a024010700191531c54048020a404a2c6b90c688021880845cd621891004218130bb2641922008520251764c83244010
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1798
  | 5 => 7915
  | 4 => 3076
  | 3 => 145
  | 2 => 16
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
  | 6 => packedAt gbK6 (55734+((h/599+packedAt gbK6 (48546+(h % 599)*12) 12) % 2373)*12) 12
  | 5 => packedAt gbK5 (337702+((h/2638+packedAt gbK5 (300770+(h % 2638)*14) 14) % 9499)*14) 14
  | 4 => packedAt gbK4 (163024+((h/1025+packedAt gbK4 (150724+(h % 1025)*12) 12) % 4061)*13) 13
  | 3 => packedAt gbK3 (9084+((h/48+packedAt gbK3 (8700+(h % 48)*8) 8) % 175)*9) 9
  | 2 => packedAt gbK2 (1161+((h/5+packedAt gbK2 (1136+(h % 5)*5) 5) % 30)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3ffe03ffffffff03f07e1ff87fffff40e3fff
  | 1 => 0xfc07ffc07fffffffc007fe1ff87ffff871c7ff
  | 2 => 0x7ffff80f01ffffff8001fff8fc1ff81f8c7
  | 3 => 0xfff8000000ffe03fffffffe0000ffe0ffe00f8
  | 4 => 0xffffffffff00003ffffffffffff0000fffff00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa83129850a1244900b2160a58292d294061b5b
  | 1 => 0x1952429314248922c042aa0aa825652830c5ad
  | 2 => 0x52a3850a2641d235556808933309b1cd8168c6
  | 3 => 0x60c3162c588903b9a674ccc0220e398eda00f0
  | 4 => 0x83041830600e1c0e3887111c444000036db600
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfee88880fee88880fee88880fee88880fee88880fee88880fee88880fee88880fee88880fee88880fee88880fee88880fee88880fee88880fee88880fee88880, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12955
namespace PEqualNP.Outside.L_meta_12955
open PEqualNP.Outside.L_meta_12955.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 16 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 49 := block_range (n:=49) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 145 := (concat bgb_3_0 bgb_3_96)
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
theorem bgb_4_3072 : Interval gbAtlas 4 3072 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3076 := (concat (concat (concat (concat (concat bgb_4_0 bgb_4_96) (concat bgb_4_192 bgb_4_288)) (concat (concat bgb_4_384 bgb_4_480) (concat bgb_4_576 bgb_4_672))) (concat (concat (concat bgb_4_768 bgb_4_864) (concat bgb_4_960 bgb_4_1056)) (concat (concat bgb_4_1152 bgb_4_1248) (concat bgb_4_1344 bgb_4_1440)))) (concat (concat (concat (concat bgb_4_1536 bgb_4_1632) (concat bgb_4_1728 bgb_4_1824)) (concat (concat bgb_4_1920 bgb_4_2016) (concat bgb_4_2112 bgb_4_2208))) (concat (concat (concat bgb_4_2304 bgb_4_2400) (concat bgb_4_2496 bgb_4_2592)) (concat (concat bgb_4_2688 bgb_4_2784) (concat bgb_4_2880 (concat bgb_4_2976 bgb_4_3072))))))
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
theorem bgb_5_7872 : Interval gbAtlas 5 7872 43 := block_range (n:=43) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 7915 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 bgb_5_576) (concat bgb_5_672 (concat bgb_5_768 bgb_5_864)))) (concat (concat (concat bgb_5_960 bgb_5_1056) (concat bgb_5_1152 (concat bgb_5_1248 bgb_5_1344))) (concat (concat bgb_5_1440 bgb_5_1536) (concat bgb_5_1632 (concat bgb_5_1728 bgb_5_1824))))) (concat (concat (concat (concat bgb_5_1920 bgb_5_2016) (concat bgb_5_2112 (concat bgb_5_2208 bgb_5_2304))) (concat (concat bgb_5_2400 bgb_5_2496) (concat bgb_5_2592 (concat bgb_5_2688 bgb_5_2784)))) (concat (concat (concat bgb_5_2880 bgb_5_2976) (concat bgb_5_3072 (concat bgb_5_3168 bgb_5_3264))) (concat (concat bgb_5_3360 (concat bgb_5_3456 bgb_5_3552)) (concat bgb_5_3648 (concat bgb_5_3744 bgb_5_3840)))))) (concat (concat (concat (concat (concat bgb_5_3936 bgb_5_4032) (concat bgb_5_4128 (concat bgb_5_4224 bgb_5_4320))) (concat (concat bgb_5_4416 bgb_5_4512) (concat bgb_5_4608 (concat bgb_5_4704 bgb_5_4800)))) (concat (concat (concat bgb_5_4896 bgb_5_4992) (concat bgb_5_5088 (concat bgb_5_5184 bgb_5_5280))) (concat (concat bgb_5_5376 (concat bgb_5_5472 bgb_5_5568)) (concat bgb_5_5664 (concat bgb_5_5760 bgb_5_5856))))) (concat (concat (concat (concat bgb_5_5952 bgb_5_6048) (concat bgb_5_6144 (concat bgb_5_6240 bgb_5_6336))) (concat (concat bgb_5_6432 bgb_5_6528) (concat bgb_5_6624 (concat bgb_5_6720 bgb_5_6816)))) (concat (concat (concat bgb_5_6912 bgb_5_7008) (concat bgb_5_7104 (concat bgb_5_7200 bgb_5_7296))) (concat (concat bgb_5_7392 (concat bgb_5_7488 bgb_5_7584)) (concat bgb_5_7680 (concat bgb_5_7776 bgb_5_7872)))))))
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
theorem bgb_6_1728 : Interval gbAtlas 6 1728 70 := block_range (n:=70) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1798 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)))) (concat (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 (concat bgb_6_1152 bgb_6_1248))) (concat (concat bgb_6_1344 bgb_6_1440) (concat bgb_6_1536 (concat bgb_6_1632 bgb_6_1728)))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfee8fee8fee88880fee8fee8fee88880fee8fee8fee88880fee8fee8fee88880fee8fee8fee88880fee8fee8fee88880fee8fee8fee88880fee8fee8fee88880
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,3,35)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,3,35)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276682472 * 2 ^ 32 + 4276652160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12955.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.or,[2,3]⟩,⟨.or,[1,7]⟩,⟨.and,[2,3]⟩,⟨.and,[1,7]⟩,⟨.or,[9,10]⟩,⟨.and,[6,11]⟩,⟨.or,[6,10]⟩,⟨.and,[8,13]⟩,⟨.or,[0,12]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682472 * 2 ^ 32 + 4276652160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682472 * 2 ^ 32 + 4276652160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12955

open PEqualNP.Outside.L_meta_12955 in
theorem PEqualNP.Outside.L_meta_12955 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682472 * 2 ^ 32 + 4276652160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682472 * 2 ^ 32 + 4276652160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
