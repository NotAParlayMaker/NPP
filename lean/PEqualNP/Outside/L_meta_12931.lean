import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12931.Model
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


end PEqualNP.Outside.L_meta_12931.Model

namespace PEqualNP.Outside.L_meta_12931
open PEqualNP.Outside.L_meta_12931.Model
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

end PEqualNP.Outside.L_meta_12931

namespace PEqualNP.Outside.L_meta_12931
open PEqualNP.Outside.L_meta_12931.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x28010341539912513183c909070088021180001c007c00b06089a82e1149d10007801c58a800034d80008088000192814600004e00b04009018244bff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x41fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87886fd0f10ff21e21fd43c437a87887f10f10ffa96217f52c43fca5885f94b10fea96217d52c43f8a5885f14b10ffa1621fe42c43fa85887f10b10ff99621fe32c43fa65887f0cb10ffa0e21fe41c43ec83887f50710faa0e21fc41c43fe63887f8c710fb18e21fd31c43ea63887f0c710ff90e21f721c43fc43887f48710fe10e21f421c43fe81887f90310fea0621fc40c43fe61887f8c310fe98621fc30c43fe41887f88310fe90621fc20c43fea9085fd5210ff2a4217e54843faa9085f55210fe2a4217c54843fea7085fd4e10ff29c217e53843faa7085f54e10fe29c217c53843fe87086fd0e10ff21c21fd438437a87087f10e10ffa94217f52843fca5085f94a10f7294216e52843faa5085f54a10f6a94216d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff99421fe32843fa65087f0ca10bea8c21ff41843fc83087f50610fe20c21ff31843fc63087f4c610fe18c21ff21843fc43087f48610fe10c217e50843fe81087f90210fea0421fc40843fe61087f8c210fd18421fd30843f261087f0c210ff90421fe20843fa41087f08210ff88421f710843f621087fd5110bfaa221bf544427ea8887f95110bf2a221fd54442faa8887f15110be2a221bc5444278a8887fd4d10bfa9a21fe53442fca6887f54d10bea9a21fc53442f8a6887fd0d10dfa1a21fe43443fa86886f50d10fe21a21ff52442fea4887f94910bf29221fd52442faa4887f14910be29221ff42443fc84887f50910fe21221ff32443fc64887f4c910fe19221ff41443fc82887d90510fea0a21f541443f882887fcc510ff18a21f631443fa62887d4c510fe18a21ff21443ee42887f88510fe90a21fc21443e842887fd0110ff20221fd40443f880887fcc110ff18221fa30443fa60887e4c110fe18221ff20443fc40887f48110fe10221ff10443f620887f84110fb08221ff54042fea8087f95010bf2a021fd54042faa8087f15010be2a021ff53042fea6087f94c10bf29821fd53042faa6087f14c10be29821ff430437e86087f90c10fea1821bd43043f886087fd4810bfa9021fe52042fca4087f54810bea9021fc52042f8a4087fd0810ff21021fd42043f884087fcc810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xe520c2fca4187b94830b729061fd520c2faa4187b54830b6a9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830fe99061fc320c3fea2187f94430bf28861f6510c2eca2187f54430bea8861f5510c2eaa2187f14430ffa0861fe410c3fa82187f10430ff98861fe310c3fa62187f0c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7905f14f20ffa1e41bf43c83fc87907f50f20dea1e41fc43c83fe85907f90b20f721641fd42c83da85907f10b20ff99641fe32c83dc65907f4cb20f699641fc32c83fea3907f94720bf28e41fd51c82faa3907f14720ffa0e41fe41c83fa83907f10720ff98e41fe31c83fa63907f0c720ff90e41fe21c83dc43907f48720fe10e41ec21c83fe81907f90320fea0641fc40c83fe61907f8c320fe98641fc30c83fea9105fd5220ff2a4417e54883faa9105f55220fe2a4417c54883fea7105fd4e20ff29c417e53883faa7105f54e20fe29c417c53883fe87106fd0e20ff21c41fd438837a87107f10e20bea9441ff42883fc85107f50a20fe21441ff32883fc65107f4ca20fe19441ff51883fca3105f94620fb28c417651883faa3105f54620faa8c417551883f8a3107fd0620ff20c41fd41883f883107fcc620ff18c41fd31883f863107fc8620ff10c41fd21883f843105f94220ffa0441fe40883fa81107f10220ff98441fe30883f461107f4c220fc98441fc30883fe41107bc8220fd90441ff54482fea8906fd51209faa241fe54482fca8907f55120beaa241fc54482f8a8906f151209e2a241ff53482fea6907f94d20bf29a41fd53482faa6907f14d20be29a41ff434837e86907f90d20fea1a41bd43483f886907fd0920ff21241ee42483fa84907b50920fe21241ff32483fc64907b8c920fe99241ed32483f864907fd4520bfa8a41fe51483faa2907f14520be28a41ff41483fc82907f50520fe20a41ff31483fc62907f4c520fe18a41ff21483fc42907b88520fe90a41fc21483d842907fd0120ff20241fd40483f880907fcc120ff18241fa30483fa60907e4c120fe18241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041fd54082faa8107f15020be2a041ff53082fea6107f94c20bf29841fd53082faa6107f14c20be29841ff430837e86107f90c20fea1841bd43083f886105f94820ffa1041fe42083fa84107f10820ff99041fe32083fa64107f0c820ffa8841fe51082fca2107f54420bea8841fc51083fe82107f90420fea0841fc41083fe62107f8c420fe98841fc31083fe42107f88420fe90841fc21082fca0107fd0020ff20
  | 2 => 0x3faa6a07f14d40be29a81ff435037e86a07f90d40fea1a81bd43503f886a07fd4940bfa9281fe52503faa4a07f14940be29281ff42503fc84a07f50940fe21281ff32503fc64a07f4c940fe19281ff51502fea2a07f94540fea8a81fc51502f8a2a07fd0540ff20a81fd41503f882a07fcc540ff18a81fd31503f862a07fc8540ff10a81fd21503f842a07fd0140fda0281fe405037c80a05f95040ffa9881fe53102fca6207794c40af29881fd53102faa6207754c40aea9881fc53103fe86206fd0c40ff21881fd431037a86207f10c40ffa9081fe52102fca4207b94840b729081fd52102faa4207b54840b6a9081fc52103fe84207f90840df21081fd42103f884206f10840ff99081fe32103fa64207f0c840ffa8881fe51102fca2207d94440bb28881fd51102faa2207d54440baa8881fc51103fe82207f90440df20881fd41103f882206f10440ff98881fe31103fa62207f0c440ff90881fe21103fa42207f08440bf28081ff401037e80207f90040fd20081fd401037a80207e50040ffaa6617f54cc3fca9985f95330df2a6613e54cc3faa9985f55330deaa6613d54cc3f8a9985f15330ffa1e61bf43cc3fc87987790f30fea1e61bd43cc3ba87986750f30fe21e61ff52cc3fca5985f94b30fea96617d52cc3f8a5987fd0b30ff21661fd42cc3f885987fccb30ff19661fd32cc3f865987fd4730ff28e617e51cc3faa3985f54730fe28e61ff41cc3fc83987f50730fe20e61ff31cc3fc63987f4c730fe18e61ff21cc3fc43987f48730fe10e61ff40cc3fc81987f50330fe20661ff548c2fea9187f95230bf2a461fd548c2faa9187f15230be2a4617d538c3fe87186fd0e30ff21c61fd438c37a87187f10e30ffa9461fe528c2fca5187f54a30bea9461fc528c3fe85187f90a30fea1461fc428c3fe65187f8ca30fe99461fc328c3fea3187f94630bf28c61fd518c2faa3187f14630ffa0c61fe418c3fa83187f10630ff98c61fe318c3fa63187f0c630ff90c61fe218c3fa43187f08630bf28461ff408c3fc81187f50230fe20461ff308c3be61187ecc230ffaa2617f544c3fca8985f95130feaa2617d544c3f8a8985f15130ffa1a61bf434c3fc86987790d30fea1a61bd434c3ba86986750d30fe21a61ff524c2fea4987f94930fea9261fc524c2f8a4987fd0930ff21261fd424c3f884987fcc930ff19261fd324c3f864987fd4530bfa8a61fe514c3faa2987f14530be28a61ff414c3fc82987f50530fe20a61ff314c3fc62987f4c530fe18a61ff214c3fc42987f48530fe10a61ff404c3fc80987f50130fe20261ff304c3f660987f8c130ef18261ff540c2fea8187f95030bf2a061be540c27ca8187f55030beaa061bd540c27aa8187f15030be2a0617e530c3fe86186fd0c30ff21861fd430c37a86187f10c30ffa9061f
  | 3 => 0xa990ffd4f21bfa9e43fe53c86fca790ff54f21bea9e43fc53c86f8a790ffd0f21dfa1e43fe43c87fa8790ef50f21fe21e43ff42c87fc8590ff50b21fe21643ff32c87fc6590fb8cb21fe99643ed32c87f86590ffd0721ff20e43fd41c87f88390ffcc721fb98e43fe31c87fa6390ff0c721fa18e43ff50c87fca190df94321fea86437d50c87f8a190ffd5221bfaa443fe54886fca910ff55221beaa443fc54886f8a910ffd4e21bfa9c43fe53886fca710ff54e21bea9c43fc53886f8a710ffd0e21dfa1c43fe43887fa8710ef50e21fe21c437d52887fe8510ff90a21fea1443fc42887fe6510fbcca21ff19443fd32887f86510fb0ca21bf28c43ff41887fc8310ff50621fe20c43ff31887fc6310fd8c621fe98c43f531887f86310ffc8621f790c43f721887fea110ff94221bf28443fd50886faa110ff14221ffaa2437f54487fca890df95121feaa2437d54487f8a890df15121ffa9a437f53487fca690df94d21fea9a437d53487f8a690df14d21ffa1a43bf43487fc8690ff50d21dea1a43fc43487fe8490ff90921fea1243fc42487fe6490ff8c921f719243fd32487da6490ff0c921ffa0a43fe41487fa8290ff10521ff98a43fe31487ec6290ff4c521fa98a43fc31487fe4290fdc8521ff10a43ee21487fea090dfd4121ff28243fd50487f8a090df14121ffaa0437f54087fca810df95021feaa0437d54087f8a810df15021ffa98437f53087fca610df94c21fea98437d53087f8a610df14c21ffa1843bf43087fc8610ff50c21dea1843fc43086fca410ffd0821ff21043fd42087f88410ffcc821f799043fe32087fa6410ff0c821f6190437e51087fe8210ff90421fea0843fc41087fe6210fdcc421ff18843fd31087f86210fd0c421ff90843ef21087fc4210fd88421fe90843ed21087ea4210f948421ffa8043fe50086fca010ff54021bea8043fc50087fea7a07f94f40bf29e81fd53d02faa7a07f14f40ffa1e81bf43d03fc87a07f50f40dea1e81fc43d03fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681fe42d03fa85a07f10b40ff99681fe32d03fa65a07f0cb40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a07f90740fea0e81fc41d03fe63a07f8c740fe98e81fc31d03fe43a07f88740fe90e81fc21d02faa9207fd4e40ff29c817e53903faa7205f54e40fe29c81ff439037e87207f90e40fea1c81bd43903f887207fd4a40ff294817e52903faa5205f54a40fe29481ff42903fc85206f90a40fea1481fc429037885207fcca40ff19481fd32903f865207fd4640ff28c817e51903faa3205f54640fe28c81ff41903fc83206f90640fea0c81fc419037883207fcc640ff18c81fd31903f863207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681207fd4d40bfa9a81fe535
  | 4 => 0xefd0e41ff21c83fd439077a8720ff10e41ffa9483fe52906fca520ff54a41bea9483fc52907fe8520ff90a41fea1483fc42907fe6520ff8ca41fe99483fc32906fca320ffd0641dfa0c83f741907fea120ff94241bf28483fd50906faa120ff14241ffa9a837f53507fca6a0ff54d41fe29a837c53507fe86a0efd0d41ff21a83fd435077a86a0ff10d41ffa92837f52507fca4a0ff54941fe292837c52507fe84a0ff90941fea1283fc42507fe64a0ff8c941fe99283fc32507fe82a0fdd0541ff20a83be41507fea0a0dfd4141ff28283fd50507f8a0a0df14141bf2a083ff53107fca620df94c41fea98837d53107f8a620ffd0c41dfa1883fe43107fa8620ef50c41fe21883ff52107fca420df94841fea90837d52107f8a420ffd0841ff21083fd42107f88420ffcc841ff19083fd32107f86420df94441ffa0883bf41107fc8220fd90441fea0883bd41107ea8220ffd4041ff280837e50107faa020df54041fe28083ff54cc6fea998ff95331bf2a663be54cc67ca998ff55331beaa663bd54cc67aa998ff15331be2a663ff43cc77e8798ff90f31fea1e63bd43cc7f88798ffd4b31ff296637e52cc7faa598df54b31fe29663ff42cc7fc8598ff50b31fe21663ff32cc7fc6598ff4cb31fe19663ff41cc7fc8398ff50731fe20e63ff50cc7fca198df94331fea86637d50cc7f8a198ffd5231bfaa463fe548c6fca918ff55231beaa463fc548c6f8a918df54e31ffa1c63bf438c7fc8718ff50e31dea1c63fc438c7fea518ff94a31bf29463fd528c6faa518ff14a31ffa1463fe428c7fa8518ff10a31ff99463fe328c7fa6518ff0ca31bf28c63ff418c7fc8318ff50631fe20c63ff318c7be6318fdcc631ffa8463fe508c6fca118ff54231bea8463fc508c7fea898dfd5131ff2a2637e544c7faa898df55131fe2a2637c544c7fe8698efd0d31ff21a63fd434c77a8698ff10d31ffa92637f524c7dea498dbd4931ff29263fd524c7f8a498df14931f6292636c524c7fe8498ff90931fea1263fc424c7fe6498ff8c931fe99263fc324c7fe8298ff90531fea0a63fc414c7fe6298fdcc531ff18a63de314c7fea098dfd4131ff28263fd504c7f8a098df14131ffaa0637f540c7fca818df95031df2a0633e540c7faa818df55031deaa0633d540c7f8a818df15031bf29863ff430c77e8618ff90c31fea1863bd430c7f88618ffd4831ff290637e520c7dca418db94831fea90637d520c7daa418db54831fe29063ff420c7fc8418ff50831fe21063ff320c7fc6418ff4c831fe190637e510c7fe8218ff90431fea0863fc410c7fe6218f7cc431ff18863f6310c7fa6218f74c431fa98863ff500c7fca018df94031fd280637a500c7faa018df54031fca806379500c7f8a018ffd5321bfaa643fe54c86fca990ff55321beaa643fc54c86f8
  | 5 => 0xf42fea1e85bd43d0bf887a17fd4742ff28e857e51d0bfaa3a15f54742fe28e85ff50d0bfca1a15f94342fea86857d50d0bf8a1a15f55242ffa9c85fe5390afca7217f54e42bea9c85fc5390bfe87216fd0e42ff21c85fd4390b7a87217f10e42bf29485ff4290b7e85217bd0a42ffa8c85fe5190afca3217f54642bea8c85fc5190bfea1217f94242bf28485fd5090afaa1217f14242ffa9a857f5350bfca6a17f54d42fe29a857c5350bfe86a16fd0d42ff21a85fd4350b7a86a17f10d42ffa1285ef4250bfc84a16f90942ffa8a857f5150bfca2a17f54542fe28a857c5150bfea0a15fd4142ff28285fd5050bf8a0a15f14142bf2a085ff5310bfca6215f94c42fea98857d5310bf8a6217fd0c42dfa1885fe4310bfa86216f50c42fe218857e5210bfe84216fd0842ff21085ee4210bfa84216f50842f6a1085ff5110bfca2215f94442fea88857d5110bf8a2217fd4042ff280857e5010bfaa0215f54042fe28085ff54ccafea9997f95332bf2a665be54cca7ca9997f55332beaa665bd54cca7aa9997f15332be2a665ff43ccb7e87997f90f32fea1e65bd43ccbf887997fd0b32ff21665fd42ccbf885997fd4732ff28e657e51ccbfaa3995f54732fe28e65ff50ccbfca1995f94332fea86657d50ccbf8a1997fd5232bfaa465fe548cafca9197f55232beaa465fc548caf8a9195f54e32ffa1c65bf438cbfc87197f50e32dea1c65fc438cafca5197fd0a32ff21465fd428cbf885197fcca32ef99465ef328cbfea3197f94632bf28c65fd518cafaa3197f14632ffa8465fe508cafca1197f54232bea8465fc508cbfea8995fd5132ff2a2657e544cbfaa8995f55132fe2a2657c544cbfe86996fd0d32ff21a65fd434cb7a86997f10d32ffa1265fe424cbfa84997f10932ff99265ef324cbfc6499778c932ffa8a657f514cbeea2995dd4532ff28a65fd514cbf8a2995f14532fa28a6574514cbfea0995fd4132ff28265fd504cbf8a0995f14132ffaa0657f540cbfca8195f95032df2a0653e540cbfaa8195f55032deaa0653d540cbf8a8195f15032bf29865ff430cb7e86197f90c32fea1865bd430cbf886195f94832ffa1065fe420cbfa84197f10832ff99065df320cbfc64197b8c832fe99065dd320cbda64197fd4432ff288657e510cbeca2195d94432fea88657d510cbeaa2195d54432fe28865ff500cbfca0195f94032fd280657a500cbfaa0195f54032fca806579500cbf8a0197fd4f41ff29e837e53d07faa7a0df54f41fe29e83ff43d077e87a0ff90f41fea1e83bd43d07f887a0ffd4b41ff296837e52d07faa5a0df54b41fe29683ff42d07fc85a0ff50b41fe21683ff32d07fc65a0ff4cb41fe19683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9c83fe53906fca720ff54e41bea9c83fc53907fe8720
  | 6 => 0xe00001000002602c00005001800002e03e00000800200000e00a00201400000803401401400401400000003a01a00200000207800600201a00000800801802600000001c00400c00000400000200600000800a00200600a03c00400801000000400002a00802400c00201000000200600402000200c01600000400600200006000200402200400200600800a00801800401000600000000200200800000e00c00000e05000400a00400201401801201400000800200800600602001800600800400000600000003c00000000400800000802400002200600200800c00800001000000800200c00803402001203800400400800400c00000002402002000400600000600800200000803600000000400202600000800000603202000400202a00000800600000000000000401001400a00000401c00200800400000000200203000c01a00400600200000001000004600400001000600400001a00005800400400600000000000600c00200601600600001800200000000601800200000401400800400000000000601000400600a00200200001602000600001200000000200000402e00400000200201400800000000802202400000802000601a01602600400200400400200400200000e00001600200000000000000000200400000603a00802600200400c01a00800e00200e00400001600400e01a01800a00000601001400800600000202c00000004000a01602403e00000601200000000200200000202a00001c01000200000000401c02000400200800608000201400800800e004002000002000000018004002002002006000002003ff52d0ffca5a1df94b43fea96877d52d0ff8a5a1ffd4743ff28e877e51d0ffaa3a1df54743fe28e87ff50d0ffca1a1df94343fea86877d50d0ff8a1a1efd4b43df29687bd52d0f78a5a1efd4743df28e87bd51d0f78a3a1efd4343df28687bd50d0f78a1a1df552439eaa4877e5390ffe8721efd0e43efa1c87ff5290ffca521df94a43fea94877d5290ff8a521ffd4643ff28c877e5190ffaa321df54643fe28c87ff5090ffca121df94243fea84877d5090ff8a121ffd0d43efa1a87fe4350f7c86a1ffd4943bfa9287fe5250ffaa4a1ff14943be29287ff5150efea2a1ff94543fea8a87fc5150ef8a2a1ffd4143bfa8287fe5050ffaa0a1ff14143be28287bf5350f3ea6a1efd4943df29287bd5250f78a4a1efd4543df28a87bd5150f78a2a1efd4143df28287bd5050f78a0a1df950439f2a0877e5310ffe8621efd0c43ff21887de4310ffa8621ef50c43eea1887ff5210ffca421df94843fea90877d5210ff8a421ffd4443ff288877e5110ffaa221df54443fe28887ff5010ffca021df94043fea80877d5010ff8a021ffd4f42ff29e857e53d0bfaa7a15f54f42fe29e85ff43d0b7e87a17f90
  | 7 => 0x1c600001374e8c001984b01030bf00001d4040000a094b45f5cb4ec82acf551a86e1af5ad4d69320001d28a7495cbd9d38000000b58000de434597196d3540017444389a5d041d0a8838da70e51c1db75de93f11ac00028c9d0000e3db3101822c0017d0ce0ce8000001a68001a98710ae05d80000013c591c000001d4dafc000000db16b5a05ca97980011795e000067c001bd13a986c3c000115800000000087c0000992680002f000194853ccec60c000ac0c112d40006b87c5a28cd0cd8e2575ce018414797652000000000000000019f84a839cd488912f8000001ce40016180000000018b86500009dc58d7182e40008306d890c000b9ca6d1e80000019e84d8000235d50e818dc0015a00000011e4e04c3000016db65db086db10a10e485e008d3b4ca18fd1209c0e893f4fc5324001e204b818de14844a340106941a400135c18800000150936c0002443116841600001a1ba0b2c001458000f79bc406cc78789cc0000405c24e417bdacc2d93ad034e15dddbf1548a0da58001781195818001328000419124db8879b58b855940008a49988d46480ed06c0000d4000dddb453591040345840002b8d71a18015af0449390c2001950c7e883497862dad0cb1b3cf7c1787a9adc175189570525a217412b4628001dd49a0b20c456295f0f90db57840000003f8330000000001d019a0d08281475b91c2d4cd1811502595d400025d610000000dcc001d3c0016ecc08001d49e48aed998001350c2cd6001dd340000000003d40000dd2b9bdd8c4000bac000000519bd8ff0ff41f803c609524e9daf9c0d240441298000000c509d80c4b6132c9cc00166c1854b03910c9be56599882740740846e88742600019b18588a02d118c000c6c414180cf9d40599d75d91a0945000c01002c04800801200200000000600001201a00000400801000000601000000000a00200200800200e00000c00000201200002000800000006400602c00c02000000200000200000600c00200200202401201200000000200800200a00000002e00000000801a01a00c00c00601a00000401e01e00001c00000400000c00a00c01000405200000801600004600000c00400200202e00600c00400000c00000800c00000000600000c04601a00202600601200a00000800000000800000201800000000e00c00200000800600400201400001400200000000e01200200000800000000400000000a01200800200800601801400200000400604c00000000202000600a00000c00200802200000601a01200e00200800c00200800602c00c01200001200000600000400200200600800200002200009000201000002600000200000400801a00200200000a00000200000000000800600e00000000000800800000000000c01601000801a00401000600000a00000000200a
  | 8 => 0x8459bb47745015b8ad4d20000000530f01585b9c000aac0003b11846c4a4000013056400153863c00021923137c000ae97f12a4fa9cbce18ac83ccfe03a43d0f50d01379d9544c8896203502a88c80000004801e17b1a40af8000f100d0d7527c0bc2518383e5b5c318decfe90b93d43e9281a48000b94470000000de8000001c384cc00000000010c93cecc001600965c44000c951cc6400008610f406590d6fd23c4946eda144e07bd264994c5d4f11292cc4c0addab50f1cb0f5861832cea91003b8d6517c3bdd997c4001b95bb9528ca88bc000000f984f0911440c88ef8f84cc17495d1b48a907f19194e0000001b040000002b0001e5cf3c00115c000a600011c97a0000ff8000cdcce40018690616cda78f615e56b0b5d420d8db6ca814240c9de00016c49b07ccdd0f800004d400000043c00151cc417698f987c00089c69d7009ec8e92ed4dcae4ec03c4094f38590c9da0d0000f4b487312bc3594907283c8091924ccc324cd569c7950045d00012880016316340019f41c4001df0001340000e5dac1ba8424000001e452946699f15c8a94e949340002e00019d1aa0000540c7c000210000a1c2dcb68d95254000848001674000000000a7122478559cd4dcec0003752d9bf85f8f94b552840001094ed5980004dc1e40014d4c680014600a8001a4571c4341c8ca54bc000d3c000001c800000000013e8ba1e64225b2d8e040154cb280283410b1481a95248b2578cf1542c89859da555dcbc57c0bb4b080014380000018743fc0013bcb9939980d108a7c0000000005bc8c40008390497056880000000000000000019b8a205388ac00026d1540c000000113cd6d4f47a40009fcf6400000174c720b1153d5bdce19cc7185207fd428d4547d03cfac21dcd576c110001a2435400005051d9a9db524c00171400042c000000e1c0017b5668d05d10ba9c30dd5b1d8d9bbc00000031c0000008107c045c868cfd6e9038135a849e09c4d5c0009b87553ec384000b38000001a6c29d6e40000016818c193129d8bc660001010b15cadabc000da56bc6742984f910ce390cd01400121c000f208a945cc74c645512d12347d9c8d33000139c48572d654c340001a91b11b58d1914001bac0017e1a9d804ad1b99ae0475811650759068000a2c4a000004c000fdc0f8bb00003ad5ec5680013800000011c4a483a998c0000016940000000007c80009513cd854859de492813c778001b617d80cd9e40000008040009315e80000000000000019edcfc00000143d8091a0000000d3420519800035c8292a015c03109d2606a46388dcec5a10001d0da51494f4cdfc410df0080d784c8921ce8918f0c5ccfb8328c28060dd8000000001208a3d058000001c5c800001334000000a30954c900005e58495cc68c895098278bf5851900c485c1860e090
  | 9 => 0x404c59779bd4000119e4c00030ca195b40000017746100000000000006d41905ed14c0a099d4c55a400000098948c0012c0ba5364001d44001c4c000000000000001e000019b516084dc112ad5180018a9a00e988b9d2c000eedc7d921a381fc208a9c57c00014d2a81cc7e1dad83c2ecb30dc170c1288811d872465c71c4684080008f1d140006ad244d29c989e40015a87f8000001e04001211d85d6c001e407d4698000c1995c819e2c750000d1d954000001aac001ac8e648d0001bcd568574808001608001b556390bc1d9484e35b28000001c74b3400000014012dcb84fc0013e1a91e3440c528000fe4b80c04fec001e60001448025754d88454d101558005b0001d1c000be1c201ec001190a54231c0100c61da601980007ec000000e0c19d444f19d714187440016f04656f8000001db9e100018c99091f8e7592c1ac0019c9020fd826973107400034c52c00000007d46894c001c64658000fd0000001a880000017e4701df4000000b71141b212fc9c8194f897c877d3699c0d14630d817f4ffc5a8ebc86565c6b00000001008140000000018156f4000efc0002c969802c6c9589640238fd45fd8cc771070001d7d6c16a99447f40015213e4000381a74fcd93d4b8000fb1554000001169734a589400000458a51300000017dced80000000000000009f000000027000000024966000000048930540d6706205d50ad055530001834000afcead065cc48fdbc8fa03ec000d7da3c00097c001d540015fc291c28498e10bd46bdd80a057a90d95f8001bc134885d0b54018f49e82fc00173d84ce71d9dac49910086881508b52f0f286d134c8c0000a14760558840bfcc60001c51dc4388000671cf8709c48d996a4ac50a92c53615500000000004f483c000c84ef54c138c1b073c000000dad1d0cbc001871e18798001e38b783a1b01979825218d91c14001d78000cc4b440015412dc9f82007b105c8b0c0130d6c800179047d6d4420dbd6d00007050a44a4001e3da4d27000155c149d5800126c0017ec0001250449a8960cc80000000000000008cc0013f800048d46dd8904111c981be00000004bd97c00000108c00156c000000000904000da1845be9751dec23dcd0a8400163d505ab9171c7846cc80000938f74ee50a1488000000000000000000000001e098ec055bfce7d3c1b8979c17000000000000177dda888d0c1d611f160ca00ea4aa8001b68ed0b04371088d58900069e50fc966496db71c9400078d110048000001345464000e2133d3d0001bf594c0007dc5802a0000001911e1c0017286cc0794f8e7800000000181d2b0000f680000010ecb0c0000000002b4001e253b9148001514428da91f4294105b247ac0013fca7977000000054d1394d00a54d8740000000579c9c001a8cf342c400000000005c000bc8a4592
  | 10 => 0xbc6f18908e4000430d2d7601bce29d18af456c000e2d19db0c0012055ac3e01b83dcb198e4000fb48f9b40001a7c0000000000008d83f0bf8000e580000014ac0019059748709f40001dd2919adc41c6879000075c908001229e680f0214e6d68ce85ad8000e4caf00adc604b5b391a400000053479d0843d876d864301b15d21e548200000004ecd41bb031403902c5114c931c00000024da80001b78089ba4cb800da2c0011647806f8d9c0006a00000008ec0019699340017107b4000000bec00050d25cedc139aa98d5795da4cf0850c700000018302852f400000064c0004e96d90819393a0e619dc0019400d8000000000000001aecbb9965708001b352140e567d251414000ab8f485a4c24cb5b814349b40000002d40e000098c001a1c85562400162c334d247640018a0b880014715903685dd574c38e311ec41c0016440015c000016816504ddd0000000000000000395d8c82c74cef027c0000015d88f40007496b80000002540000007a00005b80000b59d40019911e0b1c0000018297e844c81c0000000000583f4c4c000000aa0000e695b0ee000161d220bd0001821238b65c3c000000001c197fc2cc001e0c000445b180010509d44b092d1dc588924bdc30949c0017f90e4001d08000f089851450e82a40013a4000b8cf1c0014a059420d3b1544914000000c1c0000000000000005150f80000000011b8949ae4bc0a4c634ee891cf30000000000000dc40001149446b5c09cf4548be436516c7e5b4ccf433c971981a354e40015584501f4eb8b7cbbcf4120cad9dc907d6dcaa4d550d0eb0f8ddf8c15b7d5644618aced43b4678021aa57250d4ea1604001d640b0144715d5cb4000000000000080c0000012e40013007393d98e80000006240013852794a8001dfd07817c958000001648f24d841e86e4a240000016a0264001ae9dbc00000030400000122dc6cd0c00022928c5098f0b6d6144d07b9690000001a31d240005e8001578000158001135738a50000000df4000001c88000000000e451fcc987d0001d69960000a6585d025388fa55346544c4000a280e85611c13086a8b4c3485ac0010e18b10dc0000000019e19c5b511d5c84f0437c665ab00000000017ac001788dc88e141c570ab4fbc55400188588c000df9ccc000000220f2db85094001da00000009bc6919bc001ca40015616acd307354111bc1c13dcd1943072cbcc0005c49680b8000e546052c8be800000000112c0004917cc00036da645a189c769895b08c0c0000019d80010900fc09cc3dc59174f9cf5c88552d1185b46c0acc0057b8008a68a99c915f52757d4644000ab06811150c58792592e00013100000000019945f19a4a5db8d7a5500c8c6f5dd8c54f701b5d3182c00199d4fc614b759fc121e58478f6d5100000000002f811d4989742e9
  | 11 => 0x1cd8001a5c4e49ac6fca393943202896e12e90285053706dd8b5c55bece91338b514a4545e288254082c1881c70a8d88849ccac70cb900710fc0015c5318b3d959679dcd951580eb5721cddc35454fc04ac1f1e306853c8000240000d383782f54e9dc1315ca033958d64dcc8f44de0361c04398d5000157dcf0abc55c5c800175800066d8982
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x32042f9600c8109f992510427d64944109f98e510427d6394410cfd0e510433d43944109f98a510427d62944109f597410427f65904109f596410433e5490410cf55241043765190410be98241042f960904109fd95410437651504109fd94410427d6510410cf950410433d5410410be98041042f960104109f59731042be64cc410af593310427f658c4109f596310435e538c410d754e3104376518c410be98231042f9608c4109fd9531042ef624c410bb1893104376514c4109fd94310427d650c410af99031042bd640c410d794c310435d530c410bb98831042ed620c410be98031042f9600c4109f597210437651c84109fd96210427d6588410db94a210436d5288410be98221042f960884109fd95210427f65084109f594210436e5208410db54821043765108410f948421042fa6008410be580210427e64940109f592500427e63940109f58e500433f4394010cf50e500427e6294010db98a500426e62940109f58a500436d62940109b58a500427d61940109f597400427f65900109f596400433e5490010cf55240042f66190010bd586400427f65500109fd94400427e65100109f594400427c6510010cf950400433d5410010b798c40042dd6310010bb98840042ed6210010bd98440042f561100109f59730042be64cc010af593300439d43cc0109fd96300427d658c010d794e300435d538c010bd98630042f5618c010de942300427f654c010e750d300437a504c0109fd94300427e650c0109f594300427c650c010af99030042bd640c010d794c300435d530c010bb98830042ed620c010bd98430042f5610c0109f597200436f52c8010db14b200427f65880109f596200436e5288010db54a20042f66188010bd586200427f6548010afd9120042bc6448010dbd49200436c52480109fd94200427e65080109f594200427c6508010db948200436d5208010bd98420042f56108010dd597100437754c4010dd553100437753c4010dd54f10043b743c4010ed50f100437652c4010dd14b10042ee6284010bb58a10042f56184010dd94610042f96584010de59610042796584010ded4e10043795384010eed0e10043b94384010fa98a10043e96284010be586100437a5184010fc946100427f6544010afd9110042bc6444010bdd95100437765440109dd9510043b76444010ed19110043775444010dd55110043775344010dd54d10043b74344010ed50d10043765244010dd14910042f76044010dd94110043f34044010fc10110043f23044010fc4c110043f22044010fc48110042fb6544010ded95100427b6544010eed9110043b86444010ded4d10043795344010eed0d10043b94344010bed8510043f36144010de94510043f25144010fcd0510043f04144010fc8c510043f13144010fc88510043f12144010
  | 1 => 0x433e6494c108f992530427d6494c10cf592530423d6494c109f98a530427d6294c109fd91530427c6454c10d7d8d530427f6254c109f189530427f6154c109f585530427f6054c109f58153042be6414c10af590530435d5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f98c530435e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109d984530427e6014c10de980530427a6014c109fd97430427e65d0c109f597430427c65d0c10cfd53430433e54d0c10cf553430433c54d0c10cfd97430433e65d0c10cf597430433c65d0c10cfd4f430433e53d0c10cf54f430433c53d0c109fd96430427e6590c109f596430427c6590c10af592430435e5390c10d754e430427f6550c109f995430427d6550c109f195430433f5450c10cf951430433d5450c10cf151430435e5350c10d754d43042f76150c10bd18543042fb6050c10be181430433f6550c10cf995430433d6550c10cf195430439f6350c10cfd4d430433e5350c10e794d430431e5350c10cf54d430439d5350c10c754d430433c5350c10edd8543043b46150c10eed8143043b86050c109fd94430427e6510c109f594430427c6510c10af990430427e64d48109f593520427e63d48109f58f520433f43d4810cf50f520427e61d4810dd987520427661d48109f983520437a60d48109f596520436f52948109f992520427d64948109f98e520427d6394810cfd0e520433d43948109fd91520427c64548109fd8d520427c6354810cfd0d520433d4354810dbd89520427f61548109f585520427f60548109f58152042be6414810af59052042de6314810b758c520436d52148109f990520433e64148108f990520427d6414810cf590520423d64148109f98c520435e63148109798c520427d6314810d758c520425d6314810cfd0c520433d43148109f988520436e62148109f984520437661148109f980520437a60148109fd97420427e65d08109f597420427c65d0810cf953420433d54d08109fd96420427e65908109f596420427c6590810db94a420436d5290810bd98642042f56190810be98242042f960908109fd95420427e65508109f595420427c6550810cf951420433d5450810db949420436d52508109fd94420427e65108109f594420427c65108109fd97320427e65cc8109f597320427c65cc810af99332042bd64cc810d794f320435d53cc8109fd96320427e658c8109f596320427c658c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810d794d320435d534c810db949320436d524c810bdd8532042f4614c8109fd94320427e650c8109f594320427c650c810af99032042bd640c810bd98432042f5610c810be98
  | 2 => 0x5450110bdd8540442f461501109f994404433f5410110cf15040442de6310110b758c40442ee6210110bb58840442f66110110bd58440443b64110110ee500404427e65cc110af99330442bd64cc110cfd53304433c54cc110d7d4f304435c53cc110e750f30442f661cc110bd587304427e658c110cfd52304433c548c110be996304437a658c110eed5230443b8548c110be58e304437a538c110de14e30443bb438c110ee50e304437b528c110de54a30443f3618c110be98630443f0618c110fc90630443f1418c110fc8c630443f1318c110fcc8630443f0218c1109fd95304427d654c1109f195304433f544c110cf151304435f534c110d714d304439d434c110bdd8530442f4614c110be1953044378654c1109e19530443bb544c110ee15130443db634c110f6d4d304437a534c110de14d30443d8534c110eed0d30443da434c110ee50d30443d9434c110e650d304437b524c110de54930443f3614c110be18530443f0614c110fc90530443f1414c110fc8c530443f1314c110fcc8530443f0214c1109f99430442be640c110af590304433f540c110cf15030442ee620c110bb58830442f6610c110bd58430442fa600c1109f997204433f54c8110cf153204436f52c8110db14b20442f661c8110bd58720443e421c81109f996204433f5488110cf15220442f66188110bd586204427f65481109f595204427c6548110afd9120442bc6448110cfd51204433c5448110dbd49204436c5248110bdd8520442f46148110f9085204427e6508110cfd50204433c5408110fa480204433f54c4110cf15310443bb54c4110ee15310442fb63c4110be58f10443bb43c4110ee50f10443f241c4110fc50710443f231c4110fc4c710443f321c4110fc087104433f5484110cf15210442ee6284110bb58a10442f76484110bd59210443b75484110ed15210442f76384110bd58e10443b74384110ed50e10442f66284110f998a10442e66284110f958a10442f46284110fcd4210443f23084110fc4c2104427e63d50109f58f540427e62d50109f58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540427e63950109f58e540427e62950109f58a540433f64550109fd8d540427c63550109fd89540427c62550109fd85540427d61550109fd81540427d6055010cf55054042de6315010b758c54042ee6215010bb588540427e6415010cf990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427661150109f980540437a60150109f993530427d64d4c109f98b530427d62d4c109f987530437661d4c109f983530437a60d4c109f59653042be6494c10af592530435f5394c109f992530
  | 3 => 0x910bdd8532442f4614c9109fd94324427e650c9109f594324427c650c910af99032442bd640c910cfd50324433c540c910d7d4c324435c530c910dbd48324436c520c910bd98432442f5610c910be98032442f9600c9109f997414433f54d0510cf15341442fa60d0510be583414427e6590510cfd52414433c5490510bd99641443766590510bd59241443b75490510dd95241443745490510ed15241443345490510bd58e41443b74390510ed50e41442f66290510bd982414427c6550510cfd51414433c5450510bed8141442f86050510dd19541442746550510edd9141443b75450510dd95141443745450510ed15141442f76350510edd0d41443b54350510bd18941443f36050510bd18141443f06050510bc181414427e6510510cfd50414433c5410510bd984414427e65cc510af99331442bd64cc510cfd53314433c54cc510d7d4f314435c53cc510be98331442f960cc5109f996314433f548c510cf15231442f6658c510dd99631442f7648c510bd59231443b7548c510ed15231442f5638c510dd94e3144374538c510edd0e31443b5438c510bd98a3144377528c510dd54a31443f3608c510bd98231443f0608c5109f195314433f544c510cf151314435f534c510d714d31442ef624c510bb18931442fb604c510be1813144374654c5109d19531442f7644c510bd59131443b7544c510ed15131443d7634c510f5d4d3144376534c510dd14d31443d4534c510edd0d31443b5434c510f9d8931442f4624c510f918931442e4624c510ddd493144375524c510fcd8131442f4604c510fc181314427e650c510af99031442bd640c510cfd50314433c540c510bb98831442ed620c510bd98431442fa600c5109f997214433f54c8510cf153214436f52c8510db14b21442fa60c8510be583214437665c85109d99721442f764c8510bd59321443b754c8510ed15321442f763c8510bd58f214437653c8510dd14f21443b743c8510ed50f214437752c8510f9d4b214437552c8510f914b21443e632c8510f94cb21442f660c8510fc98321442f260c8510fc583214427e6588510cfd52214433c5488510db94a214436d5288510bd986214427c6548510cfd51214433c5448510dbd49214436c5248510bed8121442f860485109f994214433f5408510cf150214436e5208510db54821443e52108510bd99421443766508510bdd9021442f56408510edd5021443b45408510bdd8c21442f56308510dd94c21443745308510edd0c21443b54308510bd98821443e66208510ddd4821443e65208510dd54821443e55208510d954821443e73208510f90c821442f660085109f997404433f54d0110cf15340442f661d0110bd587404427e6590110cfd52404433c5490110ed906404427f65501109f595404427c6550110cfd51404433c
  | 4 => 0xf988534436e6214d109b988534427d6214d10db588534426d6214d109f98453443756114d109f184534427e6014d10de580534427c6014d109fd97434427e65d0d109f597434427c65d0d10cfd53434433e54d0d10cf553434433c54d0d10bd98743442f561d0d10cfd9743442be65d0d10cf997434423e65d0d10cf59743442bc65d0d10cf197434423c65d0d10cfd4f434433e53d0d10cf54f434433c53d0d10ed98743443b561d0d109fd96434427e6590d109f596434427c6590d10af592434433f5490d10cf15243442f66190d10bd58643442fa6090d10be582434427f6550d109f995434427d6550d109f195434433f5450d10cf951434433d5450d10cf151434433f6550d10af995434433e6550d108f995434433d6550d10af195434433c6550d108f195434439f6350d10cfd4d434433e5350d10cf54d434433c5350d10ed98543443b56150d109fd94434427e6510d109f594434427c6510d10af990434433f5410d10cf15043442f66110d10bd58443442fa6010d10be580434433f54d4910cf153524427e64d49109f593524427e63d49109f58f524433f43d4910cf50f524437561d4910af99252442bd6494910cfd52524433c5494910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e63949109f58e524433f4394910cf50e524427e62949109f586524437561949109f58252443796094910afd9152442bc6454910cfd51524433c5454910b7d8d52442dc63549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910cfd0d524433d4354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910cfd50524433c5414910db548524427e64149109f590524427e63149109f58c524433f4314910cf50c524436e62149109f984524427c61149109f980524427c60149109fd97424427e65d09109f597424427c65d0910cfd53424433c54d0910bd98742442f561d09109fd96424427e65909109f596424427c6590910cfd52424433c54909109fd95424427e65509109f595424427c6550910cfd51424433c5450910bdd8542442f46150910bed8142442f860509109fd94424427e65109109f594424427c6510910cfd50424433c5410910bd98442442f56110910be98042442f960109109fd97324427e65cc9109f597324427c65cc910af99332442bd64cc910cfd53324433c54cc910dbd4b324436c52cc910bd98732442f561cc910be98332442f960cc9109fd96324427e658c9109f596324427c658c910cfd52324433c548c910d7d4e324435c538c910db94a324436d528c9109fd95324427e654c9109f595324427c654c910cfd51324433c544c910db949324436d524c
  | 5 => 0x30843da538c210f654e3084378538c210eed0e30843b9438c210ded4a30843ea528c210de54a30843e9528c210da54a30842fa618c210fc98630843f1618c210e750d308436e524c210db54930842fb654c210ded9530843db634c210de94d3084378534c210eed0d30843da434c210ee50d30843d9434c210e650d308437b524c210fa9493084379524c210fa5493084369524c210be18530842be640c210af590308435e530c210d754c30842ee620c210bb588308436e520c210db54830842f6610c210bd584308436e52c8210db54b208436e5288210db54a20842f66188210bd58620842bf6448210af191208436e5248210db549208436e5208210db54820842f66108210bd58420843e92008210db94b108436d52c4210bd597108437565c4210ddd53108437554c4210ddd4f108437553c4210edd0f10843b543c4210dd94b10843e652c4210d994b10843e552c4210dd14b10842f965c4210de59710842fb63c4210be58f10843bb43c4210ee50f10843ea52c4210fa54b108427e63d51109f58f544427e62d51109f58b54442bd63d5110edd87544433f63d5110cf98f544433d63d51108f58f544433c63d5110cfd8b544433e62d5110cf58b544433c62d5110cfd87544433d61d5110cfd83544433d60d5110cfd52544427e64951108f992544427e63951109f58e544427e62951109f58a544427d6195110dd586544427d6095110de582544433f64551109fd8d544427c63551109fd89544427c62551109fd85544437761551109fd81544437b60551109f994544433d5415110cf990544427e63151109f58c544427e62151109f588544427e6115110dd584544427c61151109f980544427c6015110af994544433e65151108f99454442bd6315110ed584544433f6315110cf98c544433d63151108f58c544433c6315110cfd88544433e6215110cf588544433c6215110cfd84544433d6115110cd584544433f6015110cf580544433d1015110cfd53534433c54d4d10cfd93534427e64d4d109f593534433c64d4d109f98b534427d62d4d10af99253442bd6494d10cfd52534433c5494d10d7d4e534427e6494d10cf992534423e6494d109f592534433d6494d108f592534427e6394d109f98a534427d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10cfd51534433c5454d10bbd8953442ec6254d109fd91534433f6454d108fd91534427c6454d10cf191534423c6454d10d7d8d534427f6254d10dbd89534426f6254d109f189534436c6254d109b189534427f6154d10ddd85534427f6054d10ded81534427e6514d10af99053442bd6414d10cfd50534433c5414d10d754c53442ee6214d10bb588534427e6414d10cf990534423e6414d109f590534433d6414d108f590534435e6314d109
  | 6 => 0x36c6394a10dbd0e528432f4394a10db90e528436d4394a10cb50e528436c4394a10dbd86528436d6194a10db982528436c6094a109fd91528427c6454a109fd8d528427c6354a10cfd0d528433d4354a10dbd89528436f6554a10dbd51528436e5454a10db551528436c5454a10dbd4d528436e5354a10db54d528436c5354a10ebd0d52843ad4354a10dbd91528436e6454a10db591528436c6454a10dbd8d528436e6354a10db58d528436c6354a10dbd0d528432f4354a10db90d528436d4354a10cb50d528436c4354a10dbd85528436d6154a10db981528436c6054a10db548528427e6414a109f590528427e6314a109f58c528433f4314a10cf50c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10db94b428436d52d0a109fd96428427e6590a109f596428427c6590a10db94a428436d5290a10bd98642842f56190a109fd95428427e6550a109f595428427c6550a10db949428436d5250a10bed8142842f86050a109fd94428427e6510a109f594428427c6510a10db948428436d5210a10be98042842f96010a109fd97328427e65cca109f597328427c65cca10af99332842bd64cca10db94b328436d52cca10be98332842f960cca109fd96328427e658ca109f596328427c658ca10db94a328436d528ca109fd95328427e654ca109f595328427c654ca10db949328436d524ca10bdd8532842f4614ca109fd94328427e650ca109f594328427c650ca10af99032842bd640ca10db948328436d520ca10bd98432842f5610ca10be98032842f9600ca10cf953418433d54d0610db94b418436d52d0610be98341842f960d0610cfd52418433c5490610db94a418436d5290610cf951418433d5450610db949418436d5250610bed8141842f86050610cfd50418433c5410610db948418436d5210610af99331842bd64cc610d794f318435d53cc610db94b318436d52cc610be98331842f960cc610db94a318436d528c610d794d318435d534c610bbd8931842ec624c610db949318436d524c610bed8131842f8604c610af99031842bd640c610bb98831842ed620c610db948318436d520c610be580318436e52c8610db54b21842fa60c8610be583218436e5288610db54a218436e5248610db54921842fb6048610be181218436e5208610db54821843e52108610db94b408436d52d0210cf952408433d5490210db94a408436d5290210bd98640842f56190210db949408436d5250210cf950408433d5410210b798c40842dd6310210bb98840842ed6210210db948408436d5210210bd98440842f56110210ee50040842be64cc210af593308439d43cc210db94b308436d52cc210d794e308435d538c210db94a308436d528c210bd98630842f5618c210be5963084379658c210de94e
  | 7 => 0x210310bd98440c42f56110310ed90440c42be64cc310af59330c435e53cc310d754f30c439d43cc310bd98730c42f561cc310d794d30c435d534c310e750d30c42f7614c310bd18530c42be640c310af59030c42ee620c310bb58830c42f6610c310bd58430c436e52c8310db54b20c42f661c8310bd58720c43e421c8310bd98620c42f56188310afd9120c42bc6448310db94920c436d5248310bdd8520c42f46148310f908520c42ee62d5210bb58b548427e63d52109f58f548427e62d5210db98b548426e62d52109f58b548436d62d52109b58b548437561d5210de983548433f54952109f98e548427d63952109f98a548427d6295210cfd91548427f63552109f18d548427f62552109f189548433d5415210b798c54842dd6315210bb98854842ed6215210cf990548427e6315210d798c548425e63152109f58c548435d63152109758c548427e6215210db988548426e62152109f588548436d62152109b58854843756115210de98054842ee62d4e10bb58b538427e64d4e109f593538427e62d4e10db98b538426e62d4e109f58b538436d62d4e109b58b538437561d4e10de98353842be6494e10af592538435f5394e109f992538433e6494e108f992538427d6494e10cf592538423d6494e109f98a538427d6294e10de982538427f6454e109f191538435f6354e109fd89538427c6254e10af99053842bd6414e10d754c53842ee6214e10bb588538427e6414e10cf990538423e6414e109f590538433d6414e108f590538435e6314e109f988538436e6214e109b988538427d6214e10db588538426d6214e10dd584538437a6014e109fd97438427e65d0e109f597438427c65d0e10cfd53438433e54d0e10cf553438433c54d0e10cfd97438433e65d0e10cf597438433c65d0e10cfd4f438433e53d0e10cf54f438433c53d0e109fd96438427e6590e109f596438427c6590e10d794e438435d5390e10be98243842f96090e109fd95438427e6550e109f595438427c6550e10cfd51438433e5450e10cf551438433c5450e10d794d438435d5350e10bdd8543842f46150e10cfd95438433e6550e10cf595438433c6550e10e7d8d438433f5350e10cf94d438439e5350e10c794d438433d5350e10e754d438431d5350e10cf14d43843b76150e10ed185438427f6510e109f994438427d6510e109f19443842fa6010e10be580438427e64d4a109f593528427e63d4a109f58f528433f43d4a10cf50f528437561d4a10de983528436f5294a109f992528427d6494a109f98e528427d6394a10cfd0e528433d4394a10dbd52528436e5494a10db552528436c5494a10dbd4e528436e5394a10db54e528436c5394a10ebd0e52843ad4394a10dbd92528436e6494a10db592528436c6494a10dbd8e528436e6394a10db58e5284
  | 8 => 0x10cfd0d52c433d4354b10dbd8952c43746154b10db54852c427e6414b109f59052c427e6314b109f58c52c433f4314b10cf50c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10db94b42c436d52d0b10bd98742c42f561d0b109fd9642c427e6590b109f59642c427c6590b10cf95242c433d5490b10be98242c42f96090b109fd9542c427e6550b109f59542c427c6550b10bdd8542c42f46150b109fd9442c427e6510b109f59442c427c6510b10cf95042c433d5410b10db94842c436d5210b10bd98442c42f56110b109fd9732c427e65ccb109f59732c427c65ccb10af99332c42bd64ccb10bd98732c42f561ccb109fd9632c427e658cb109f59632c427c658cb10db94a32c436d528cb109fd9532c427e654cb109f59532c427c654cb10db94932c436d524cb10bdd8532c42f4614cb109fd9432c427e650cb109f59432c427c650cb10af99032c42bd640cb10bd98432c42f5610cb10be98032c42f9600cb10cf95241c433d5490710be98241c42f96090710dd59641c43765490710ed95241c43b55490710dd15241c42f56390710edd0e41c43b54390710bd98a41c42f66090710fc98241c43f16090710bdd9541c43776550710edd9141c43765450710dd15141c42f76350710edd0d41c43b54350710bd18941c42f46050710cf95041c433d5410710be98041c42f96010710af99331c42bd64cc710d794e31c435d538c710be98231c42f9608c710dd59631c42f7648c710bd59231c4376538c710f594e31c43d5538c710dd14e31c43b7438c710ed50e31c42f6628c710ddd4a31c4375528c710bd98231c43f2608c710fc58231c42ef624c710bb18931c42f7654c710ddd9531c42f7644c710bd59131c43d7634c710dd94d31c4374534c710edd0d31c43b5434c710f9d8931c42f4624c710f918931c42e4624c710ddd4931c4375524c710bd18131c42be640c710af59031c435e530c710d754c31c42ee620c710bb58831c42fa600c710be58031c42f565c8710dd59721c42f764c8710bd59321c42f763c8710bd58f21c437653c8710dd14f21c43b743c8710ed50f21c437752c8710dd54b21c43e632c8710f94cb21c42f660c8710db94a21c436d5288710be98221c42f96088710db94821c436d5208710f948421c42fa6008710be58021c43756508710bdd9021c42f56408710bdd8c21c42f56308710dd94c21c43745308710edd0c21c43b54308710f998821c43775208710f994821c43755208710f954821c43655208710f9cc821c43e43208710bd98021c43f26008710fc58021c433e54d0310cf55340c42f661d0310bd58740c433f5490310cf15240c43b64190310cf95140c433d5450310bdd8540c42f46150310cfd5040c433c5410310b798c40c42dd6310310bb98840c42ed6
  | 9 => 0x98430082f5610c020dbd53200836d54c8020dbd4f200836d53c8020ebd0f20083ad43c8020db94720082ed6288020db94a20082f66188020bd586200837b5388020de54e20083bb4388020ee50e20082f96288020de94a20083ea5288020fc98620083f161880209fd9520082bf6448020af19120082ef6548020dbd95200826f6548020ebd9120083ac6448020dbd51200836d5448020dbd4d200836d5348020ebd0d20083ad4348020db94520082ef6048020db94120083eb4048020fa10120083ea3048020fa4c120082fb6548020ded95200827b6548020eed9120083b86448020ded4d20083795348020eed0d20083b94348020bed8920083eb6248020de94920083ea5248020fad0920083e84248020fa8c920083e93248020fac8520083e92148020bb98b54c42ed62d53109f98f54c427d63d53109f98b54c436e62d53109b98b54c427d62d5310db58b54c426d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c43766195310cfd9154c427f63553109f18d54c427f62553109f18954c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c427e64d4f109f59353c427e62d4f109f58b53c437661d4f10de58353c42be6494f10af59253c435f5394f109f99253c433e6494f108f99253c427d6494f10cf59253c423d6494f109f98a53c427d6294f10dd98653c427f6454f109f19153c435f6354f109fd8953c427c6254f10af99053c42bd6414f10d754c53c42ee6214f10bb58853c427e6414f10cf99053c423e6414f109f59053c433d6414f108f59053c435e6314f109f98853c436e6214f109b98853c427d6214f10db58853c426d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10cfd5343c433e54d0f10cf55343c433c54d0f10bd98743c42f561d0f10cfd9743c433e65d0f10cf59743c433c65d0f10cfd4f43c433e53d0f10cf54f43c433c53d0f10ed98743c43b561d0f109fd9643c427e6590f109f59643c427c6590f10bd98643c42f56190f109fd9543c427e6550f109f59543c427c6550f10cfd5143c433e5450f10cf55143c433c5450f10bed8143c42f86050f10cfd9543c433e6550f10cf59543c433c6550f10e7d8d43c433f5350f10cf94d43c433d5350f10cf14d43c43b66150f10ed58543c43bb6050f10ee18143c427f6510f109f99443c427d6510f109f19443c42f66110f10bd58443c42be64d4b10af59352c427e64d4b10cf99352c423e64d4b109f59352c433d64d4b108f59352c427e63d4b109f58f52c433f43d4b10cf50f52c437661d4b10de58352c436f5294b109f99252c427d6494b109f98e52c427d6394b10cfd0e52c433d4394b109fd9152c427c6454b109fd8d52c427c6354b
  | 10 => 0x30833f5450c20cf951430833d5450c20cf151430835e5350c20d754d43082ef6250c20bb18943082fb6050c20be181430833f6550c20cf995430833d6550c20cf195430839f6350c20cfd4d430833e5350c20e794d430831e5350c20cf54d430839d5350c20c754d430833c5350c20ebd8943083ac6250c20eed8143083b86050c209fd94430827e6510c209f594430827c6510c20af990430827e64948209f592520827e63948209f58e520833f4394820cf50e520827d65d08209fd96420827d6590820cf952420833d5490820db94a42082fa6090820be582420827f6550820db949420827f65108209f594420833e5410820cf55042082fa6010820be580420827d65cc820af99332082bd64cc8209fd96320827d658c820d794e320835d538c820db94a32082fa608c820be582320827f654c820db94932082f7614c820bd185320827f650c8209f59432082be640c820af590320835e530c820d754c32082f6610c820bd58432082fa600c820be580320837751944209f992510827d64944209f98e510827d6394420cfd0e510833d43944209fd91510827c64544209fd8d510827c6354420cfd0d510833d4354420af99051082bd6414420b798c51082dd6314420dd544510827f65d04209f997410827d65d0420cf953410833d54d04209fd96410827e65904209f59641082ee6290420bb58a41083765190420dd54641082fa6090420be582410827f65504209f595410827c6550420cf951410833d5450420dd945410837551504209fd94410827e65104209f594410827f65cc4209f997310827d65cc420af99331082bd64cc420d794f310835d53cc4209fd96310827e658c4209f5963108376518c420dd546310827f654c4209f595310827c654c420d794d310835d534c420bbd8931082ec624c420dd9453108375514c4209fd94310827e650c4209f59431082be640c420af59031082ee620c420bb58831082fa600c420be580310837651c8420dd54721082fa60c8420be583210827d6588420db94a210827f6548420db94821083765108420dd54421083e52108420be98021082f960084209f992500827d64940209f98e500827d6394020cfd0e500833d4394020dd986500837561940209f597400827f65900209f596400833e5490020cf55240082ee6290020bb58a400827f65500209fd94400827e65100209f594400827c6510020cf950400833d5410020b798c40082dd6310020bb98840082ed6210020bd98440082f561100209f59730082be64cc020af593300839d43cc0209fd96300827d658c020d794e300835d538c020bb98a30082ed628c020de942300827f654c020e750d300837a504c0209fd94300827e650c0209f594300827c650c020af99030082bd640c020d794c300835d530c020bb98830082ed620c020bd
  | 11 => 0x7a538c120de14e30483bb438c120ee50e30483eb628c120be98a30483e8628c120fa90a30483e9428c120fa8ca30483e9328c120ded4630483ea218c120fa086304827f654c1209f595304827c654c120cfd51304833c544c120d7d4d304835c534c120e750d30482ef624c120bb18930482f8654c120de1953048278654c120eed5130483b8544c120f6d8d30483db534c120de94d3048378534c120f614d30483bb434c120f690d30483b9434c120f650d3048399434c120fad8930482f8624c120fa18930483ea424c120fa50930483ea324c120fa4c9304837b514c120fa88530483e8214c1209f99430482be640c120af590304833f540c120cf15030482ee620c120bb58830482f6610c120bd58430482fa600c120cfd53204833c54c8120eed5320483b854c8120bed8f20482f963c8120eed0f20483b943c8120fa90b20483e942c8120fa8cb20483e932c8120fa88720483e821c8120cfd52204833c5488120bd98620482f56188120bbd9220482ed6488120ebd5220483ac5488120bbd8e20482ed6388120ebd0e20483ad4388120bb98620483e66188120b998620483e56188120fad4220483ea3088120fa4c2204827e63d50209f58f540827e62d5020db98b540827e61d50209f587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540833f64550209fd8d540827c63550209fd89540827d62550209fd85540827c6155020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf990540827e6315020d798c540825e63150209f58c540835d63150209758c540827e6215020db988540826e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a60150209f993530827d64d4c209f98b530836e62d4c209f987530827d61d4c209f983530837a60d4c209f59653082be6494c20af592530835f5394c209f992530833e6494c208f992530827d6494c20cf592530823d6494c209f986530827d6194c209fd91530827c6454c20d7d8d530827f6254c209f589530827f6154c209f18553082be6414c20af590530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209f988530836e6214c209b988530827e6114c20dd98453082766114c209f58453083756114c209d584530827e6014c20de980530827a6014c209fd97430827e65d0c209f597430827c65d0c20cfd53430833e54d0c20cf553430833c54d0c20cfd97430833e65d0c20cf597430833c65d0c20cfd4f430833e53d0c20cf54f430833c53d0c209fd96430827e6590c209f596430827c6590c20af592430835e5390c20d754e430827f6550c209f995430827d6550c209f1954
  | 12 => 0x4c9209f99432482be640c920af590324833f540c920cf15032482ee620c920bd98432482f5610c920be980324833f54d4520cf153514827e64d45209f593514827e63d45209f58f514833f43d4520cf50f514836e32d4520db4cb51482be6494520af592514833f5494520cf15251483775194520afd9151482bc6454520cfd51514833c5454520b7d8d51482dc6354520cfd50514833c5414520dd544514827e64145209f590514827e63145209f58c514833f4314520cf50c514827e65d05209f597414827c65d0520cfd53414833c54d0520bb98b41482ed62d05209f996414827d65905209f196414833f5490520cf152414827f65505209f995414827c6550520cfd51414833c5450520bbd8941482ec6250520bed8141482f860505209f994414827d65105209f194414833f5410520cf15041482ee6210520bb58841482fa6010520be580414827e65cc5209f597314827c65cc520af99331482bd64cc520cfd53314833c54cc520bb98b31482ed62cc520ddd47314837451cc520be98331482f960cc5209f996314827d658c5209f196314833f548c520cf152314835f538c520d714e314827f654c5209f995314827c654c520cfd51314833c544c520bbd8931482ec624c5209f994314827d650c5209f19431482be640c520af590314833f540c520cf150314835f530c520d714c31482ee620c520bb5883148377510c520dd14431482fa600c520be580314827e65c8520cfd53214833c54c8520cfd52214833c5488520ddd4621483745188520be98221482f96088520bbd9221482ed6488520ebd5221483ac5488520bbd8e21482ed6388520db94e214836c5388520ebd0e21483ad4388520bb986214836f5188520f9d4621483e45188520f98c621483e53188520bb98221483ea6088520ba98221483e96088520cfd51214833c5448520ddd4521483745148520bed8121482f860485209f994214833f5408520cf15021483e52108520bb994214836e6508520bbd9021482ed6408520ebd5021483ac5408520bbd8c21482ed6308520db94c214836c5308520ebd0c21483ad4308520bb98421483e66108520dbd4421483e65108520f954421483e73108520f90c421482ee60085209f997404833f54d0120cf15340482ee62d0120bb58b404827e6590120cfd52404833c5490120eb90a404827f65501209f595404827c6550120cfd51404833c5450120bbd8940482ec62501209f994404833f5410120cf15040482de6310120b758c40482ee6210120bb58840483ae4210120bd98440482f56110120ee500404827e65cc120af99330482bd64cc120cfd53304833c54cc120d7d4f304835c53cc120e750f30482ee62cc120bb58b304827e658c120cfd52304833c548c120be996304837a658c120eed5230483b8548c120be58e30483
  | 13 => 0xcfd51534833c5454d20bdd8553482f46154d209fd91534833f6454d208fd91534827c6454d20cf191534823c6454d20d7d8d534827f6254d20dbd89534827f6154d20ddd8553482776154d209f18553483746154d209d185534827f6054d20ded81534827e6514d20af99053482bd6414d20cfd50534833c5414d20d754c53482f66114d20bd584534827e6414d20cf990534823e6414d209f590534833d6414d208f590534835e6314d209f988534836d6214d209f188534827e6114d20dd98453482766114d209f58453483756114d209d58453483796014d209fd97434827e65d0d209f597434827c65d0d20cfd53434833e54d0d20cf553434833c54d0d20bb98b43482ed62d0d20cfd9743482be65d0d20cf997434823e65d0d20cf59743482bc65d0d20cf197434823c65d0d20cfd4f434833e53d0d20cf54f434833c53d0d20eb98b43483ad62d0d209fd96434827e6590d209f596434827c6590d20af592434833f5490d20cf15243482ee6290d20bb58a43482fa6090d20be582434827f6550d209f995434827d6550d209f195434833f5450d20cf951434833d5450d20cf151434833f6550d20af995434833e6550d208f995434833d6550d20af195434833c6550d208f195434839f6350d20cfd4d434833e5350d20cf54d434833c5350d20eb98943483ad6250d209fd94434827e6510d209f594434827c6510d20af990434833f5410d20cf15043482ee6210d20bb58843482fa6010d20be580434827e65d0920cfd53424833c54d0920be98342482f960d09209f996424833f5490920cf15242482ee6590920db99642482ed6490920ebd52424836e5490920db15242483ac5490920cb15242482ed6390920ebd0e42483ad4390920bb98642482ee60909209f195424833f5450920cf15142482fb6050920be181424836c65509209b19542483af6450920ebd51424836e5450920db15142483ac5450920bbd8d42483af4350920eb50d42482ec6150920fad8142482ec6050920fa18142482e860509209f994424833f5410920cf15042482ee62109209f99732482be64cc920af593324833f54cc920cf153324835f53cc920d714f32482fa60cc920be583324827e658c920cfd52324833c548c920bb996324836e658c920bbd9232482ed648c920ebd5232483ac548c920bb58e324836e538c920db14e32483af438c920eb50e32482ee618c920fad8232482ee608c920fa182324827c654c920cfd51324833c544c920d7d4d324835c534c920bdd8532482f4614c920bed8132482f8604c920db195324826c654c920bbd9132482ed644c920ebd5132483ac544c920f3d8d32483cf534c920db94d324836c534c920f314d32483af434c920eb50d32483e7614c920bb18532483e4614c920b918532483eb604c920bb18132483e860
  | 14 => 0x94318827e650c6209f59431882be640c620af59031882ee620c620bb5883188376510c620dd54431882fa600c620be580318837651c8620dd94621883755188620be98221882f96088620dd94521883755148620bed8121882f86048620dd54421883e52108620dd947408837551d0220cf952408833d5490220bb98a40882ed6290220dd94640883755190220dd94540883755150220cf950408833d5410220b798c40882dd6310220bb98840882ed6210220bd98440882f56110220dd94440883755110220ee50040882be64cc220af593308839d43cc220dd947308837551cc220d794e308835d538c220bb98a30882ed628c220dd9463088375518c220be5963088379658c220de94e30883da538c220f654e3088378538c220eed0e30883b9438c220be98a30883ea628c220fa58a30883f2518c220de54630883f1518c220dc546308839d434c220dd9453088375514c220bed95308837b654c220f6d8d308837a534c220de14d30883bb434c220f690d30883b9434c220f650d3088399434c220be18930883f2514c220de54530883f1514c220dc54530882be640c220af590308835e530c220d754c30882ee620c220bb58830882f6610c220bd5843088376510c220dd544308837651c8220dd54720882ed65c8220db597208836f54c8220db553208836f53c8220db54f20883af43c8220eb50f208836e51c8220f9947208836651c8220f954720882f965c8220de59720882fb63c8220be58f20883bb43c8220ee50f20883f251c8220fc547208827e63d51209f58f544827e61d51209f58754482bd63d5120ebd8b544833f63d5120cf98f544833d63d51208f58f544833c63d5120cfd8b544833d62d5120cfd87544833e61d5120cf587544833c61d5120cfd83544833d60d5120cfd52544827e64951208f992544827e63951209f58e544827d6295120db58a544827e61951209f586544827d6095120de582544833f64551209fd8d544827c63551209fd89544836f62551209fd85544827c61551209fd81544837b60551209f994544833d5415120cf990544827e63151209f58c544827e6215120db588544827c62151209f984544827d6115120af994544833e65151208f99454482bd6315120eb588544833f6315120cf98c544833d63151208f58c544833c6315120cfd88544833d6215120cb588544833f6115120cf984544833d6115120cf184544833f6015120cf580544833d2015120cfd53534833c54d4d20cfd93534827e64d4d209f593534833c64d4d209f987534827d61d4d20af99253482bd6494d20cfd52534833c5494d20d7d4e534827e6494d20cf992534823e6494d209f592534833d6494d208f592534827e6394d209f58a534836d6294d209f986534827d6194d209f58253483796094d20afd9153482bc6454d2
  | 15 => 0x8827c65d0e20cfd53438833e54d0e20cf553438833c54d0e20cfd97438833e65d0e20cf597438833c65d0e20cfd4f438833e53d0e20cf54f438833c53d0e209fd96438827e6590e209f596438827c6590e20d794e438835d5390e20be98243882f96090e209fd95438827e6550e209f595438827c6550e20cfd51438833e5450e20cf551438833c5450e20d794d438835d5350e20bbd8943882ec6250e20cfd95438833e6550e20cf595438833c6550e20e7d8d438833f5350e20cf94d438839e5350e20c794d438833d5350e20e754d438831d5350e20cf14d43883af6250e20eb189438827f6510e209f994438827d6510e209f19443882fa6010e20be580438833e54d0a20cf55342882fa60d0a20be583428833f5490a20cf152428833e5450a20cf55142882fb6050a20be181428833f5410a20cf15042882be64cca20af593328835e53cca20d754f32882fa60cca20be583328835e534ca20d754d32882f7614ca20bd18532882fb604ca20be18132882be640ca20af59032882f6610ca20bd58432882f9600ca20ddd46518827e64946209f592518827e63946209f58e518833f4394620cf50e51883775494620dd95251883755494620dd15251883775394620dd94e51883755394620dd14e51883b74394620ed50e51883776494620dd99251883756494620dd19251883776394620dd98e51883756394620dd18e51883774394620cdd0e51883764394620dd50e51883354394620dd10e51883776294620ddd0a51883764294620dd50a51883744294620ddcca51883763294620dd4ca51883743294620dd982518837460946209fd91518827c64546209fd8d518827c6354620cfd0d518833d4354620ddd9551883775454620dd95151883755454620dd15151883775354620dd94d51883755354620dd14d51883b74354620ed50d51883776454620dd99151883756454620dd19151883776354620dd98d51883756354620dd18d51883774354620cdd0d51883764354620dd50d51883354354620dd10d51883756254620ddd0951883764254620dd50951883744254620ddcc951883763254620dd4c951883743254620dd98151883746054620dd544518827f65d06209f997418827d65d0620dd947418837551d06209fd96418827e65906209f59641882ee6290620bb58a41883765190620dd546418827f65506209f595418827c6550620dd94541883755150620bed8141882f860506209fd94418827e65106209f59441883765110620dd54441882fa6010620be580418827f65cc6209f997318827d65cc620af99331882bd64cc620dd947318837551cc620be98331882f960cc6209fd96318827e658c6209f5963188376518c620dd546318827f654c6209f595318827c654c620bbd8931882ec624c620dd9453188375514c6209fd
  | 16 => 0x960907209fd9541c827d65507209f19541c82ef6250720bb18941c827f65107209f99441c827d6510720cf95041c833d5410720bb98841c82ed6210720dd94441c837551107209fd9731c827e65cc7209f59731c82be64cc720af59331c82ee62cc720bb58b31c827f658c7209f99631c827d658c720dd94631c8375518c7209fd9531c827d654c7209f19531c82ef624c720bb18931c8376514c720dd54531c827f650c7209f99431c827d650c720af99031c82bd640c720bb98831c82ed620c720be98031c82f9600c720dd94721c837551c8720be98321c82f960c8720bb59621c836d6588720bbd9221c82ed6488720bbd8e21c82ed6388720db94e21c836c5388720ebd0e21c83ad4388720db54621c83e63188720f94c621c82ee6088720dd94421c83755108720f948421c82fa6008720be58021c82ef6408720bb59021c82ef6308720bb58c21c836e5308720db14c21c83af4308720eb50c21c83e66108720f994421c836d5108720f954421c83655108720f9cc421c83e43108720bb98021c83ea6008720fa58021c833e54d0320cf55340c82ee62d0320bb58b40c833f5490320cf15240c83ae4290320cf95140c833d5450320bbd8940c82ec6250320cfd5040c833c5410320b798c40c82dd6310320bb98840c82ed6210320eb90840c82f66110320bd58440c82be64cc320af59330c835e53cc320d754f30c839d43cc320bb98b30c82ed62cc320d794d30c835d534c320e750d30c82ef624c320bb18930c82be640c320af59030c82ee620c320bb58830c82f6610c320bd58430c82f661d5220bd587548827e63d52209f58f548836d62d52209f987548837661d52209d987548827d61d5220dd587548827561d5220de983548833f54952209f98e548827d63952209f986548827d6195220cfd91548827f63552209f18d548827f61552209f185548833d5415220b798c54882dd6315220bd98454882f56115220cf990548827e6315220d798c548825e63152209f58c548835d63152209758c548836d62152209f984548837661152209d984548827d6115220dd58454882756115220de98054882f661d4e20bd587538827e64d4e209f593538836d62d4e209f987538837661d4e209d987538827d61d4e20dd587538827561d4e20de98353882be6494e20af592538835f5394e209f992538833e6494e208f992538827d6494e20cf592538823d6494e209f986538827d6194e20de982538827f6454e209f191538835f6354e209fd85538827c6154e20af99053882bd6414e20d754c53882f66114e20bd584538827e6414e20cf990538823e6414e209f590538833d6414e208f590538835e6314e20db588538827e6114e20dd98453882766114e209f58453883756114e209d584538837a6014e209fd97438827e65d0e209f59743
  | 17 => 0x5320cfd9154c827f63553209f18d54c827f61553209f18554c833d5415320cf99054c827e63153209f58c54c836e62153209f98454c827d6115320de58054c827e64d4f209f59353c836e62d4f209f98753c827d61d4f20de58353c82be6494f20af59253c835f5394f209f99253c833e6494f208f99253c827d6494f20cf59253c823d6494f20db98a53c827e6194f209f58653c827f6454f209f19153c835f6354f209fd8553c827c6154f20af99053c82bd6414f20d754c53c82f66114f20bd58453c827e6414f20cf99053c823e6414f209f59053c833d6414f208f59053c835e6314f20db98853c827e6114f20dd98453c82766114f209f58453c83756114f209d58453c83796014f209fd9743c827e65d0f209f59743c827c65d0f20cfd5343c833e54d0f20cf55343c833c54d0f20bb98b43c82ed62d0f20cfd9743c833e65d0f20cf59743c833c65d0f20cfd4f43c833e53d0f20cf54f43c833c53d0f20eb98b43c83ad62d0f209fd9643c827e6590f209f59643c827c6590f20bb98a43c82ed6290f209fd9543c827e6550f209f59543c827c6550f20cfd5143c833e5450f20cf55143c833c5450f20bed8143c82f86050f20cfd9543c833e6550f20cf59543c833c6550f20e7d8d43c833f5350f20cf94d43c833d5350f20cf14d43c83ae6250f20eb58943c83bb6050f20ee18143c827f6510f209f99443c827d6510f209f19443c82ee6210f20bb58843c833e5490b20cf55242c82fa6090b20be58242c836d6590b20db95242c83ae5490b20eb55242c836c5490b20bb58e42c83af4390b20eb50e42c82ee6190b20bb98242c83ea6090b20fa58242c82ef6550b20dbd9542c83af6450b20db95142c836c5450b20bbd8d42c83af4350b20eb50d42c82ec6150b20bb18142c833e5410b20cf55042c82fa6010b20be58042c82be64ccb20af59332c835e538cb20d754e32c82fa608cb20be58232c836d658cb20bbd9232c82ed648cb20db94e32c83ce538cb20f354e32c836c538cb20ebd0e32c83ad438cb20bb98632c82ee608cb20fa98232c83e9608cb20bdd8532c82f4614cb20bbd9532c836f654cb20bbd9132c82ed644cb20f3d8d32c836e534cb20db14d32c83af434cb20eb50d32c83e7614cb20bb18532c83e4614cb20b918532c82ec604cb20af99032c82bd640cb20d794c32c835d530cb20bd98432c82f5610cb20be98032c82f9600cb20af99351c82bd64d4720ddd4651c827e64947209f59251c827e63947209f58e51c833f4394720cf50e51c827f64547209f19151c827f63547209f18d51c833f4354720cf50d51c836e3254720db4c951c837551147209fd9741c827e65d07209f59741c82ee62d0720bb58b41c837651d0720dd54741c827f65907209f99641c827d6590720cf95241c833d5490720be98241c82f
  | 18 => 0xbe983310c2f960cc4309f596310c33e548c430cf552310c36e528c430db54a310c375518c4309fd95310c33e544c430cf551310c2ef624c430bb189310c36e524c430db549310c376514c430af990310c2bd640c430cf950310c33d540c430bb988310c2ed620c430db948310c36d520c430dd944310c375510c430be980310c2f9600c4309fd97210c27e65c84309f597210c33e54c8430cf553210c36e52c8430db54b210c37651c8430dd547210c27f65884309f996210c27d6588430cf952210c33d5488430db94a210c36d5288430dd946210c37551884309fd95210c27d65484309f195210c33e5448430cf551210c2df6348430b718d210c36e5248430db549210c3765148430dd545210c27f65084309f994210c27d6508430cf950210c33d5408430db948210c36d5208430dd944210c3755108430f9484210c27e64940309f592500c33f4394030cf50e500c27d65d0030cf953400c33d54d0030db94b400c36d52d0030dd947400c37551d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd6390030db94a400c36d5290030dd946400c37551900309fd95400c33e5450030cf551400c36e5250030db549400c3765150030dd545400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c2ee6210030bb588400c36e5210030db548400c2f66110030bd584400c3765110030dd544400c3b94010030af993300c2bd64cc030cf953300c33d54cc030e7d0f300c39d43cc030db94b300c36d52cc030dd947300c37551cc030e7993300c39d64cc030d7d53300c39e54cc030d7553300c39d54cc030c7553300c3ce52cc030f354b300c3d651cc030f5547300c33e548c030cf552300c2dd638c030d794e300c36e528c030db54a300c376518c030dd546300c3ba548c030ee552300c2f9638c030de94e300c3da538c030eed0e300c3b9438c030fa94a300c379528c030fa54a300c369528c030fc946300c379518c030fc546300c371518c0309fd95300c33e544c030cf551300c39f434c030e750d300c36e524c030db549300c376514c030dd545300c2df654c030d7d95300c25f654c030d7d51300c39e544c030d7551300c39d544c030c7551300c3ce524c030f3549300c3d6514c030f5545300c2df604c030d7941300c2fb654c030ded95300c27b654c030ee951300c3b9544c030bed8d300c3db634c030de94d300c3da534c030eed0d300c3b9434c030fa949300c379524c030fa549300c369524c030fc945300c379514c030fc545300c371514c030bd98754c82f561d53209f98f54c827d63d5320db98b54c827e61d5320dd98754c827661d53209f58754c837561d53209d58754c837960d5320cfd5254c827e63953209f58e54c836e62953209f98654c827d619
  | 19 => 0x5420c27c6550830cf951420c33d5450830db949420c36d5250830bed81420c2f860508309fd94420c27e65108309f594420c33e5410830cf550420c36e5210830db548420c2be64cc830af593320c33e54cc830cf553320c36e52cc830db54b320c2fa60cc830be583320c27d658c830cf952320c33d548c830db54a320c27f654c830cf951320c33d544c830db949320c2f7614c830bd185320c2be640c830af590320c33e540c830cf550320c36e520c830db548320c2f6610c830bd584320c2fa600c830be580320c2be64d4430af593510c33e54d4430cf553510c2ee62d4430bb58b510c36e52d4430db54b510c33e5494430cf552510c36e5294430db54a510c37751944309f992510c27d6494430cfd0e510c33d43944309f98a510c27d6294430ddd52510c3765494430ed952510c3365494430dd552510c3b55494430cd552510c3745494430edd0e510c3b54394430ddd4a510c3765294430f994a510c3665294430dd54a510c3e55294430d954a510c3745294430ddd92510c3766494430dd592510c3746494430dd18e510c3774394430cdd0e510c3764394430dd50e510c3354394430dd10e510c3776294430dd98a510c3756294430dd18a510c3774294430dd90a510c3754294430dd10a510c3773294430dd8ca510c3753294430dd0ca510c3766094430dd182510c33e5454430cf551510c36e5254430db549510c27f64544309f191510c33f4354430cf50d510c27f62544309f189510c3776554430ddd51510c3765454430ed951510c3365454430dd551510c3b55454430cd551510c3745454430edd0d510c3b54354430ddd49510c3765254430f9949510c3665254430dd549510c3e55254430d9549510c3745254430ddd91510c3766454430dd591510c3746454430dd98d510c3774354430cdd0d510c3764354430dd50d510c3354354430dd10d510c3776254430dd989510c3756254430dd189510c3774254430dd909510c3754254430dd109510c3773254430dd8c9510c3753254430dd0c9510c3766054430dd181510c3743054430af990510c2bd6414430cf950510c33d5414430bb988510c2ed6214430db948510c36d5214430bd984510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c36e52d0430db54b410c37651d0430dd547410c27f65904309f996410c27d6590430cf952410c33d5490430db94a410c36d5290430dd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c36e5250430db549410c3765150430dd545410c2fb6050430be181410c27f65104309f994410c27d6510430cf950410c33d5410430db948410c36d5210430dd944410c3755110430af993310c2bd64cc430cf953310c33d54cc430db94b310c36d52cc430dd947310c37551cc430
  | 20 => 0xc27561d50309f983540c37a60d50309f596540c33f54950309f98a540c27d62950309f986540c27d61950308f596540c33e6395030cf18e540c33f6295030cf98a540c33d6295030cf18a540c33f6195030cf986540c33d6195030cf186540c33e6095030cf182540c33f64550309fd8d540c27d63550309fd89540c27c62550309fd85540c27c6155030cfd95540c23f6355030cf98d540c23d6355030cf18d540c33f6255030cf989540c33d6255030cf189540c33f6155030cf985540c33d6155030cf185540c33e6055030cf181540c33c3055030af990540c33d5415030bb988540c2ed6215030bd984540c2f561150309f990540c33e64150308f990540c27e6315030d798c540c25e63150309f988540c36e62150309b988540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a60150309f992530c33e6494c308f992530c27d6494c30cf592530c23d6494c309f597430c33f54d0c30cf953430c33d54d0c30cf153430c2bd65d0c30cf597430c23d65d0c30cf94f430c27f6590c309f596430c2bd6490c30cf952430c33d5490c30d794e430c2fa6090c30be582430c27f6550c30cfd51430c33e5450c30cf551430c33c5450c30d794d430c2bf6550c30cfd95430c23f6550c30e7d8d430c33e5350c30c794d430c27f6510c309f594430c2be6410c30cf950430c33d5410c30be980430c2f96010c30af993520c2bd64d4830cf953520c33d54d4830bd987520c2f561d4830cf952520c33d5494830dbd4a520c27e64948309f592520c33f4394830cf50e520c27e61948309f586520c36f5494830db952520c3ae5494830cb952520c36d5494830eb552520c32d5494830db152520c3af4394830eb50e520c36f6494830db992520c36d6494830db192520c36c6394830dbd0e520c32f4394830db90e520c36d4394830cb50e520c36c4394830dbd86520c36e6194830db586520c36c6194830db982520c36c6094830cf951520c33d54548309fd91520c27c6454830cfd0d520c33d43548309fd85520c27c6154830dbd95520c36f5454830db951520c3ae5454830cb951520c36d5454830eb551520c32d5454830db151520c3af4354830eb50d520c36f6454830db991520c36d6454830db191520c36e6354830dbd0d520c32f4354830db90d520c36d4354830cb50d520c36c4354830dbd85520c36e6154830db585520c36c6154830db981520c36c6054830db0c1520c2be6414830af590520c33e5414830cf550520c2ee6214830db548520c2f66114830bd584520c27f65d08309f997420c27d65d0830cf953420c33d54d0830db94b420c36d52d08309fd96420c27e65908309f596420c33e5490830cf552420c36e5290830db54a420c27f65508309f59
  | 21 => 0x5490930e750e424c2fa6090930be582424c27f65509309f995424c27c6550930e750d424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930e750c424c36f5210930db148424c2fa6010930be580424c27e65cc930af993324c2bd64cc930e750f324c39d438c930dbd4a324c36c528c930be982324c2f9608c930e750d324c36f524c930db149324c2f7614c930bd185324c2fb604c930be181324c27e650c930af990324c2bd640c930e750c324c2f6610c930bd584324c2fa600c930e750f514c27e64d45309f593514c33f43d4530cf50f514c27e62d45309f58b514c39d4394530ddd46514c2bf6454530af191514c39d4354530bbd89514c2ec6254530e750c514c37551145309f990514c27d6414530cfd0c514c33d43145309f988514c27d6214530de580514c27e65d05309f597414c27c65d0530b798f414c2dd63d0530e750f414c37751d0530dd147414c27e65905309f596414c27c6590530cfd52414c33c5490530e750e414c2fa6090530be582414c27f65505309f995414c27c6550530e750d414c27e65105309f594414c27c6510530cfd50414c33c5410530b798c414c2dd6310530e750c414c3775110530dd144414c2fa6010530be580414c27e65cc530af993314c2bd64cc530e750f314c39d438c530ddd46314c374518c530be982314c2f9608c530e750d314c2ef624c530bb189314c377514c530dd145314c2fb604c530be181314c27e650c530af990314c2bd640c530e750c314c2ee620c530bb588314c2fa600c5309f997214c27d65c85309f197214c39d43c8530ddd47214c37451c8530be983214c2f960c85309f996214c27d65885309f196214c39d4388530dbd4a214c36c5288530be982214c2f960885309fd95214c27e65485309f195214c39d43485309f994214c27d65085309f194214c2de6308530b758c214c39d4308530dbd48214c36c5208530ddd44214c3745108530f9484214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d0130e750f404c27e6590130cf952404c33d5490130e750e404c27f65501309f595404c27c6550130cfd51404c33c5450130b7d8d404c2dc6350130e750d404c27e6510130cf950404c33d5410130b798c404c2dd6310130e750c404c2ee6210130bb588404c2f66110130bd584404c2be64cc130af593304c39d43cc130ee993304c3b964cc130eed0f304c3da43cc130ee50f304c3d943cc130e650f304c2f962cc130be587304c39f438c130e750e304c2df648c130b7592304c3db508c130bb98b540c2ed62d5030bd987540c2f561d50309f98f540c35e63d50309f98b540c36e62d50309b98b540c27d62d5030db58b540c26d62d50309f987540c37661d50309d987540c27d61d5030dd587540
  | 22 => 0x630dd545318c2fb604c630be181318c2be640c630af590318c2ee620c630bb588318c2f9600c6309fd97218c27e65c86309f597218c37651c8630dd547218c2fa60c8630be583218c27f65886309f996218c27d6588630db94a218c36d5288630be982218c2f960886309fd95218c27d65486309f195218c2df6348630b718d218c27f65086309f994218c27d6508630db948218c36d5208630dd944218c3755108630f9484218c2fa6008630be580218c33f54d0230cf153408c33e5490230cf552408c2de6390230b758e408c33f5450230cf151408c33e5410230cf550408c2de6310230b758c408c2ee6210230bb588408c2f66110230bd584408c2be64cc230af593308c39f43cc230e750f308c2dd65cc230d7597308c39e64cc230e7593308c35f54cc230d7553308c2f965cc230de597308c3ba64cc230ee593308c3bb43cc230ee50f308c2f962cc230be587308c27e62d51309f58b544c27e61d51309f587544c33f54951309f992544c27d6395130d758e544c27e62951309f58a544c27e61951309f586544c27d6095130de582544c2ef6255130bb189544c2f76155130bd185544c33f64551309fd8d544c35f63551309fd89544c36f62551309bd89544c27c6255130db189544c26c62551309fd85544c37761551309dd85544c27c6155130dd185544c27461551309fd81544c37b60551309f994544c33d5415130cf990544c27e6315130d758c544c27c63151309f988544c27d62151309f984544c27d61151309f997434c33f54d0d30cf153434c2fa60d0d30be583434c33f65d0d30cf997434c33d65d0d30cf197434c3ba60d0d30ee583434c27e6590d30af592434c2de6590d30d7996434c2dd6490d30a7592434c35e5490d30d7152434c2de6090d309f195434c33f5450d30cf151434c2fb6050d30be181434c33f6550d30cf995434c33d6550d30cf195434c39f6350d30eed81434c3b86050d30d7195434c25c6550d30e7d91434c39f5450d30d7951434c35c5450d30e7151434c3db6050d30b7181434c3d86050d30e7d95434c31f6550d30e7195434c31c6550d30e7d89434c39e6250d30e7589434c39c6250d30e7d85434c39e6150d30e7585434c39c6150d30e7d81434c39b6050d30e7981434c39d6050d30e7181434c3986050d309f994434c2be6410d30b798c434c39d4310d30e750f524c27e64d49309f593524c33f43d4930cf50f524c27e61d49309f587524c39d4394930dbd4a524c2bf6454930af191524c39d4354930bdd85524c2f46154930e750c524c36d52149309f990524c27d6414930cfd0c524c33d43149309f984524c27d6114930de580524c27e65d09309f597424c27c65d0930b798f424c2dd63d0930e750f424c36f52d0930db14b424c27e65909309f596424c27c6590930cfd52424c33c
  | 23 => 0xd54621cc27f65487309f59521cc27c6548730cf95121cc33d5448730e750d21cc36e5248730db54921cc3765148730dd54521cc27f65087309f99421cc27d6508730cf95021cc33d5408730b798c21cc2dd6308730e750c21cc3e52108730cf95340cc33d54d0330b798f40cc2dd63d0330e750f40cc33e5490330cf55240cc39d4390330cf95140cc33d5450330b7d8d40cc2dc6350330e750d40cc33e5410330cf55040cc2de6310330b758c40cc39d4310330bb98840cc2ed6210330bd98440cc2f56110330ee50040cc35d63d52309f98b548c27d62d52309f987548c27d61d5230de983548c33f54952309f98a548c27d62952309f986548c27d6195230cfd91548c27f62552309f189548c27f61552309f185548c33d5415230bb988548c2ed6215230bd984548c2f56115230cf990548c35d63152309f988548c36e62152309b988548c27d6215230db588548c26d62152309f984548c37661152309d984548c27d6115230dd584548c2756115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c33e65d0e30cf597438c3ba60d0e30ee583438c33e5450e30cf551438c2fb6050e30be181438c33f6550e30cf195438c39f6350e30eed81438c3b86050e30bd987528c2f561d4a30dbd4a528c27e6494a309f592528c33f4394a30cf50e528c27e6194a309f586528c37a6094a30afd91528c2bc6454a309fd91528c33f6454a308fd91528c27c6454a30cf191528c23c6454a30cfd0d528c33d4354a309fd85528c27c6154a30db548528c27f65d0a309f997428c27d65d0a309fd96428c27e6590a309f596428c33f5490a30cf152428c36e5290a30db54a428c2fa6090a30be582428c27f6550a309f595428c27c6550a30db949428c36d5250a309fd94428c27e6510a309f594428c33f5410a30cf150428c2fa6010a30be580428c2be64cca30af593328c36e528ca30db54a328c2fa608ca30be582328c36e524ca30db549328c2f7614ca30bd185328c2fb604ca30be181328c2be640ca30af590328c2f6610ca30bd584328c2f9600ca30bb98b518c2ed62d4630ddd46518c27e64946309f592518c33f4394630cf50e518c27e62946309f58a518c37a6094630afd91518c2bc64546309fd91518c33f64546308fd91518c27c6454630cf191518c23c6454630cfd0d518c33d43546309fd89518c27c6254630dd544518c27f65d06309f997418c27d65d06309fd96418c27e65906309f596418c33f5490630cf152418c3765190630dd546418c2fa6090630be582418c27f65506309f595418c27c6550630dd945418c37551506309fd94418c27e65106309f594418c33f5410630cf150418c2fa6010630be580418c2be64cc630af593318c376518c630dd546318c2fa608c630be582318c2ef624c630bb189318c376514c
  | 24 => 0x43cc39e6050f30e758143cc39c6050f30cf95043cc33d5410f30e750c43cc2fa6010f30be58043cc2be64d4b30af59352cc33e54d4b30cf55352cc39d43d4b30cf95252cc33d5494b30e750e52cc36f5294b309f99252cc27d6494b30cfd0e52cc33d4394b309f98652cc27d6194b30cf95152cc33d5454b30e750d52cc2f76154b30bd18552cc27f6454b309f19152cc33f4354b30cf50d52cc27f6154b30ddd8552cc2776154b309f18552cc3746154b309d18552cc2be6414b30af59052cc33e5414b30cf55052cc39d4314b30db54852cc2f66114b30bd58452cc27f65d0b309f99742cc27d65d0b30cf95342cc33d54d0b30b798f42cc2dd63d0b30e750f42cc27f6590b309f99642cc27d6590b30cf95242cc33d5490b30e750e42cc27f6550b309f59542cc27c6550b30cf95142cc33d5450b30e750d42cc2fb6050b30be18142cc27f6510b309f99442cc27d6510b30cf95042cc33d5410b30b798c42cc2dd6310b30e750c42cc2be64ccb30af59332cc33e54ccb30cf55332cc39d43ccb30db94b32cc36d52ccb30be98332cc2f960ccb30cf95232cc33d548cb30e750e32cc33e544cb30cf55132cc39d434cb30bdd8532cc2f4614cb30af99032cc2bd640cb30cf95032cc33d540cb30e750c32cc36e520cb30db54832cc2f6610cb30bd58432cc2fa600cb30be58032cc2be64d4730af59351cc33e54d4730cf55351cc39d43d4730cf95251cc33d5494730e750e51cc37751947309f99251cc27d6494730cfd0e51cc33d43947309f98a51cc27d6294730cf95151cc33d5454730e750d51cc2ef6254730bb18951cc27f64547309f19151cc33f4354730cf50d51cc27f6254730dbd8951cc26f62547309f18951cc36c62547309b18951cc2be6414730af59051cc33e5414730cf55051cc39d4314730bb98851cc2ed6214730dd54451cc27f65d07309f99741cc27d65d0730cf95341cc33d54d0730b798f41cc2dd63d0730e750f41cc27f65907309f99641cc27d6590730cf95241cc33d5490730e750e41cc27f65507309f59541cc27c6550730cf95141cc33d5450730e750d41cc2fb6050730be18141cc27f65107309f99441cc27d6510730cf95041cc33d5410730b798c41cc2dd6310730e750c41cc2be64cc730af59331cc33e54cc730cf55331cc39d43cc730dd94731cc37551cc730be98331cc2f960cc730cf95231cc33d548c730e750e31cc33e544c730cf55131cc39d434c730bbd8931cc2ec624c730af99031cc2bd640c730cf95031cc33d540c730e750c31cc2ee620c730bb58831cc376510c730dd54431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730cf95321cc33d54c8730e750f21cc36e52c8730db54b21cc27f65887309f99621cc27d6588730cf95221cc33d5488730e750e21cc3765188730d
  | 25 => 0x3765188440dd54621102fa6088440be582211027f65484409f595211027c6548440afd9121102bc6448440d794d211035d5348440db949211036d5248440dd945211037551484409fd94211027e65084409f59421102bf6408440af190211035e5308440d754c211036e5208440db54821103765108440dd54421103e52108440cfd0e501033d4394040cf90a501033c4294040cf906501033c4194040d794f401035d53d0040db94b401036d52d0040dd947401037551d0040af58f401039e53d0040cf54f401039d53d0040c754f40102be62d0040eb94b40103ad52d0040af98740103b651d0040ed54740102bd6490040cf952401035e5390040d754e401036e5290040db54a40103765190040dd54640102f96490040de95240103ba5490040f694e40103d95390040eed0e40103b94390040fa94a40103e95290040ee90a40103b84290040fc94640103f15190040ee90640103b841900409fd95401035e5350040d754d401036e5250040db54940103765150040dd54540102bf6550040cfd95401023f6550040afd8d401039e5350040cf54d401039d5350040c754d40102bc6250040eb94940103ad5250040af18540103b65150040ed54540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040f694d40103d95350040ee90d40103b84350040fa94940103e95250040eed0940103b94250040fc94540103f15150040eed0540103b94150040d798f54cc27e62d53309f58b54cc27e61d53309f58754cc37960d5330cfd5254cc35e63953309f98a54cc27d62953309f98654cc27d6195330e798e54cc33e6395330c798e54cc33c6395330cfd8a54cc33e6295330cf58a54cc33c6295330cfd8654cc33e6195330cf58654cc33c6195330cfd8254cc33d6095330cfd9154cc27f62553309f18954cc27f61553309f18554cc33f6555330e798d54cc33e6355330cf18d54cc33f6255330cf98954cc33d6255330cf18954cc33f6155330cf98554cc33d6155330cf18554cc33f6055330cf58154cc33d5415330cf99054cc35e63153309f98854cc27d62153309f98454cc27d6115330de58054cc33f54d0f30cf95343cc33d54d0f30cf15343cc2bd65d0f30cf59743cc33e5490f30cf55243cc2fa6090f30be58243cc35d6590f30d795243cc39e5490f30e755243cc35c5490f30b798243cc3da6090f30f658243cc33f5450f30cf95143cc33d5450f30cf15143cc2bf6550f30cfd9543cc39f6350f30b7d9543cc35f6550f30e7d9143cc39f5450f30d795143cc39e5450f30c795143cc39d5450f30d715143cc39c5450f30b718143cc39f6550f30a7d9543cc31f6550f30e7d8943cc39e6250f30e758943cc39c6250f30e7d8543cc39e6150f30e758543cc39c6150f30e7d81
  | 26 => 0x294440dd58a51103746294440ddd0a51103764294440dd50a51103744294440ddcca51103763294440dd4ca51103743294440dd98251103746094440d794d511035d5354440db949511036d52544409fd8d511027c6354440cfd0d511033d43544409fd89511027c6254440ddd9551103b46454440ddd4d51103765354440f594d51103565354440dd54d51103d55354440d554d51103745354440edd0d51103b54354440ddd4951103765254440f994951103665254440dd54951103e55254440d954951103745254440ed90951103b44254440dd99151103776354440dd98d51103756354440dd18d51103774354440cdd0d51103764354440dd50d51103354354440dd10d51103776254440dd98951103756254440dd18951103774254440dd90951103754254440dd10951103773254440dd8c951103753254440dd0c951103766054440dd18151103744054440b798c51102dd6314440d794c511035d5314440bb98851102ed6214440db948511036d5214440bd98451103755114440d794f411035d53d0440db94b411036d52d0440dd947411037551d0440be98341102f960d04409f596411035e5390440d754e411036e5290440db54a41103755190440af596411033d6590440af58e411039e5390440cf54e411039d5390440c754e41102be6290440eb94a41103ad5290440af98641103b65190440cf54641103b55190440cd54641102bd60904409fd95411035e5350440d754d411036e5250440db54941103765150440d794c411035d5310440db948411036d5210440dd94441103755110440be98041102f96010440af58c411039e5310440cf54c411039d5310440c754c41102be6210440eb94841103ad5210440af98441103b66110440ed944411033d5110440ed54441103ba6010440af58041103b96010440ae580411027f65cc4409f997311027d65cc440af99331102bd64cc440d794f311035d53cc440db94b311036d52cc440dd947311037551cc4409fd96311027e658c4409f59631102bf648c440af192311035e538c440d754e311036e528c440db54a3110376518c440dd546311027f654c4409f595311027c654c440afd9131102bc644c440d794d311035d534c440bbd8931102ec624c440db949311036d524c440dd9453110375514c440bed8131102f8604c4409fd94311027e650c4409f59431102be640c440af590311035e530c440d754c31102ee620c440bb588311036e520c440db5483110376510c440dd54431102fa600c440be580311027f65c84409f997211027d65c8440af99321102bd64c8440d794f211035d53c8440db94b211036d52c8440dd947211037551c8440be98321102f960c84409fd96211027e65884409f59621102be6488440af592211035e5388440d754e211036e5288440db54a2110
  | 27 => 0x40d394e521036d5394840f354e521034d5394840db14e52103af4394840eb50e521036c6494840dbd8e521036e6394840db58e521036c6394840dbd0e521032f4394840db90e521036d4394840cb50e521036c4394840dbd86521036e6194840db586521036c6194840db982521036c6094840d794d521035d53548409fd8d521027c6354840cfd0d521033d43548409fd85521027c6154840dbd9552103ac6454840dbd4d521036e5354840f394d521034e5354840db54d52103cd5354840d354d521036c5354840ebd0d52103ad4354840db991521036f6354840db98d521036d6354840db18d521036f4354840cbd0d521036e4354840db50d521032d4354840db10d521036f6154840db985521036d6154840db185521036e6054840db181521036c4054840b798c52102dd6314840d794c521035d5314840bb988521036d5214840bd98452102f56114840d794f421035d53d0840db94b421036d52d0840be98342102f960d08409f596421035e5390840d754e421036d5290840af596421033d6590840af58e421039e5390840cf54e421039d5390840c754e42102be6290840eb94a421033d5290840eb54a421032d5290840af98642102bd60908409fd95421035e5350840d754d421036e5250840d794c421035d5310840db948421036d5210840be98042102f96010840af58c421039e5310840cf54c421039d5310840c754c42102be6210840eb98842103ae5210840cf54842103ad5210840af98442103ba6010840af58042103b96010840ae580421027f65cc8409f997321027d65cc840af99332102bd64cc840d794f321035d53cc840db94b321036d52cc8409fd96321027e658c8409f59632102bf648c840af192321035e538c840d754e321036e528c840db54a321027f654c8409f595321027c654c840afd9132102bc644c840d794d321035d534c840db949321036d524c840bdd8532102f4614c840bed8132102f8604c8409fd94321027e650c8409f59432102be640c840af590321035e530c840d754c321036e520c840db54832102f6610c840bd58432102fa600c840be58032102de63d4440b758f511035e53d4440d754f51102ee62d4440bb58b511036e52d4440db54b511035e5394440d754e511036e5294440db54a511037751944409f98e511027d6394440cfd0e511033d43944409f98a511027d6294440ed19251103775394440dd94e51103d65394440d594e51103755394440f554e51103555394440dd14e51103b74394440ed50e51103775294440dd94a51103e65294440d994a51103755294440f954a51103655294440dd14a51103b64294440ed10a51103746494440ddd8e51103766394440dd58e51103746394440ddd0e51103374394440dd90e51103754394440cd50e51103744394440ddd8a51103766
  | 28 => 0xd8142502f860509409f994425027e65cc9409f597325027c65cc940af99332502bd64cc940dbd4b325036c52cc9409f996325027d658c9409f196325027f654c9409f995325027c654c940bdd8532502f4614c9409f994325027d650c9409f19432502be640c940af590325036f520c940db14832502f6610c940bd58432502fa600c940be580325027e63d45409f58f515033f43d4540cf50f515027e62d45409f58b51502ee6294540bb58a51503775194540dd544515027e63145409f58c515033f4314540cf50c515027e62145409f588515027e65d0540ddd4641503745190540be98241502f96090540ddd4541503745150540bed8141502f860505409f994415027e65cc5409f597315027c65cc540af99331502bd64cc540ddd47315037451cc5409f996315027d658c5409f196315027f654c5409f995315027c654c540bbd8931502ec624c5409f994315027d650c5409f19431502be640c540af59031502ee620c540bb5883150377510c540dd14431502fa600c540be580315027e65c85409f597215027c65c8540dbd4b215036c52c85409f996215027d65885409f19621503775188540dd146215027f65485409f995215027c6548540dbd49215036c5248540ddd45215037451485409f994215027d65085409f19421502be6408540af59021503e52108540be98021502f96008540eed0f40503b943d0140af58e405033f5390140cf14a405033c5190140eed4240502ee62d4c40bb58b53102f661d4c40bd587531035f5394c409f98a531027d6294c409f986531027d6194c40e7992531035c6494c40d7d8a531035e6294c40d758a531035c6294c40d7d86531035e6194c40d7586531035c6194c40d7982531035c6094c40cf991531027f6254c409f189531027f6154c409f185531035f6554c40e7991531035e6454c40c7991531035f6254c40d7989531035d6254c40d7189531035f6154c40d7985531035d6154c40d7185531035e6054c40d7181531035c4054c40b798c531035d5314c40bb98853102ed6214c40bd98453102f56114c40cf953431035e53d0c40d754f43102fa60d0c40be583431033e53d0c40e794f431033d53d0c40e754f431031d53d0c40af98b43102be61d0c40ee98343102bd60d0c40ee58343102b960d0c409f59643102bd6490c40d754e431027f6550c40cf951431035e5350c40afd95431033f6550c40e7d8d431033e5350c40e794d431031e5350c40e754d43102bc6250c40af18543102bf6050c40af990431035e5310c40d754c43102fa6010c40be58043102de63d4840b758f521035e53d4840d754f52102f661d4840bd587521035e5394840d754e521036f52948409f98e521027d6394840cfd0e521033d43948409f986521027d6194840eb192521036f5394840db94e52103ce53948
  | 29 => 0x2902fb6050a40be18142902bd6510a40cf59442902bd6310a40cf54c42903ae6210a40cf54842902be6110a40af580429027f65cca409f997329027d65cca40af99332902bd64cca409fd96329027e658ca409f59632902bf648ca40af192329036e528ca40db54a329027f654ca409f595329027c654ca40afd9132902bc644ca40db949329036d524ca40bdd8532902f4614ca409fd94329027e650ca409f59432902be640ca40af59032902f6610ca40bd58432902fa600ca40be58032902ee62d4640bb58b519037751946409f98e519027d6394640cfd0e519033d43946409f98a519027d62946409fd8d519027c6354640cfd0d519033d43546409fd89519027c6254640dd54451903765190640dd54641902fa6090640be58241902bd6390640cf54e41902be6290640ed946419033d5190640ed54641903ba6090640af58241903b96090640dd94541903755150640bed8141902f86050640af594419033d6510640af58c419033d5310640af98841903b66110640cf54441902bd60106409fd97319027e65cc6409f59731902be64cc640af593319027f658c6409f996319027d658c640afd9231902bc648c640dd9463190375518c6409fd95319027d654c6409f19531902bf644c640af19131902ef624c640bb1893190376514c640dd545319027f650c6409f994319027d650c640af99031902bd640c640bb98831902ed620c640be98031902f9600c6409fd97219027e65c86409f59721902be64c8640af593219037651c8640dd547219027f65886409f996219027d6588640af99221902bd6488640db94a219036d52886409fd95219027d65486409f19521902bf6448640af191219027f65086409f994219027d6508640afd9021902bc6408640db948219036d5208640dd94421903755108640f948421902fa6008640be58021902bd65d0240cf59740902bd63d0240cf54f40902be62d0240af98740902f965d0240de597409033f64d4d409f98b535027d62d4d409f987535027d61d4d40d7d4e53502ef6254d40bb18953502f76154d40bd185535035d5314d409f988535027d6214d409f984535027d6114d409f99743502be65d0d40cf997435033c53d0d40af98343502bd6490d40d7d4e435035c5390d40be98243502f96090d40d7d4d435035c5350d40bed8143502f86050d40e7d8d435033f5350d40e7d4d435031f5350d40cf14d435039c5350d40eed8143502bc6050d40ee18143502b86050d409f99443502be6410d40e750c435027e63d49409f58f525033f43d4940cf50f525027e61d49409f587525036f5294940bd98652502f56194940db548525027e63149409f58c525033f4314940cf50c525027e61149409f584525027e65d0940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940be
  | 30 => 0x7d6294f409f98653d027d6194f40cf99153d027f6254f409f18953d027f6154f409f18553d035d5314f40d794f43d035d53d0f40be98343d02f960d0f40cf94f43d039e53d0f40cf54f43d039d53d0f40c754f43d02be60d0f40ee98343d03b960d0f40afd9543d033f6550f40e7d8d43d039f5350f40cf94d43d039c5350f40af18143d035e5310f40d754c43d039d4310f40be98043d02f96010f40dbd4a52d027e6394b409f58e52d033f4394b40cf50e52d027e6194b409f58652d027f6354b409f18d52d033f4354b40cf50d52d027f6154b409f18552d036d5214b40db94b42d036d52d0b40be98342d02f960d0b40db94842d036d5210b40be98042d02f96010b409fd9732d027e65ccb409f59732d02be64ccb40af59332d027f658cb409f99632d027d658cb409fd9532d027d654cb409f19532d02f7614cb40bd18532d02fb604cb40be18132d027f650cb409f99432d027d650cb40af99032d02bd640cb40bd98432d02f5610cb40be98032d02f9600cb40ddd4651d027e63947409f58e51d033f4394740cf50e51d027e62947409f58a51d027f63547409f18d51d033f4354740cf50d51d027f62547409f18951d03755114740dd94741d037551d0740be98341d02f960d0740dd94441d03755110740be98041d02f960107409fd9731d027e65cc7409f59731d02be64cc740af59331d027f658c7409f99631d027d658c7409fd9531d027d654c7409f19531d02ef624c740bb18931d02fb604c740be18131d027f650c7409f99431d027d650c740af99031d02bd640c740bb98831d02ed620c740be98031d02f9600c7409fd9721d027e65c87409f59721d02fa60c8740be58321d027f65887409f99621d027d6588740be98221d02f960887409fd9521d027d65487409f19521d027f65087409f99421d027d6508740af99021d02bd6408740f948421d035f5394e409f98a539027d6294e409f986539027d6194e40cf591539027f6254e409f189539027f6154e409f185539035d5314e40bb98853902ed6214e40bd98453902f56114e40af597439033d65d0e40cf94f43902be62d0e40af98743902bd60d0e40d794e439035d5390e40be98243902f96090e40d794d439035d5350e40bed8143902f86050e40e7d8d439033e5350e40e794d439031e5350e40cf54d439039d5350e40c754d43902bc6250e40af18543902bf6050e40eed8143903b86050e40bd98752902f561d4a40dbd4a529027e6394a409f58e529033f4394a40cf50e529027e6194a409f586529027f6354a409f18d529033f4354a40cf50d529027f6154a409f185529036d5214a40db94a429036d5290a40be98242902f96090a40af58e429033d5390a40eb94a429033d5290a40eb54a42902be6190a40ee98242902bd6090a40ee582429036e5250a40db5494
  | 31 => 0x94421db0ca510867d65d04219fd96410867d6590421cf952410873d5490421bb98a41086ed62904219fd95410867f65104219f994410867d65104219f194410873e5410421cf55041086ee6210421bb588410867d65cc421af99331086bd64cc421bd597310877565cc4219d59731087b664cc421ed593310877753cc421dd54f31087b743cc421ed50f31087e762cc421bd58b31087e462cc421dd94b31087e732cc421f90cb31086f560cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c421bd9863108776518c4219fd9531086ef624c421bb1893108776514c4219fd94310867e650c4219f594310867c650c421af99031086bd640c421d794c310875d530c421bb98831086ed620c421be98031086f9600c421bd5943108775650c4219d59431087b6640c421ed59031086f6630c421f598c3108777530c421f594c3108775530c421f554c31087b7430c421ed50c31087e6620c421bd58831087e5620c421b95883108776520c421f9cc831087e4320c421fc98031086f5600c421fc58031086f1600c421bb98f21086ec63c8421dbd4f210876d53c8421ebd0f21087ad43c8421f9cc721087e431c8421bb58321086ed6288421db94a21086f66388421bd18e21087775388421dd54e21087b74388421ed50e21086f56288421b958a21087765288421f994a21087e73288421f90ca21086f560884219fd9521086ef6548421dbd95210866f6548421bb98d21086ec6348421dbd4d210876d5348421ebd0d21087ad4348421bbd85210876e5148421f9d0521087e64148421f950521087e44148421f9cc521087e63148421f94c521087e43148421bbd8121086f76548421ddd9521086776548421bd98d21086f46348421ddd4d21087755348421edd0d21087b54348421bdd8921087e76248421dd94921087e65248421f9d0921087e64248421f950921087e44248421f9cc921087e63248421f94c921087e43248421bdd8121087e76548421b9d9521087676548421f9d9121087e66448421f959121087e46448421f9d5121087e65448421f955121087e45448421f9d8d21087e66348421b998d21087e56348421f918d21086e46348421f9d4d21087675348421f994d21087e55348421d954d21087e45348421f9d0d21087a74348421f990d21087e54348421e950d21087e44348421f9d8121086e76048421f998121087e56048421f918121087e521d4021f9486500877b50940219f992500867d64940219f98e500867d6394021cfd0e500873d4394021afd9150086bc6454021f9485500867f6454021cfd91500863f64540219f191500873c64540218f191500867f63540219f18d500873f4354021cf50d50086be6414021af59050086de6314021b758c50087e52114021de540500875f5394f409f98a53d02
  | 32 => 0x19f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e580540867e64d4c219f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21af99253086bd6494c21d7d4e530867e6494c21cf992530863e6494c219f592530873d6494c218f592530867e6094c219f582530867f6454c219f191530875f6354c21db18953087746154c219fd81530867c6054c21af99053086bd6414c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6314c21d798c530867e6214c21db988530866e6214c219f98453087766114c219d984530867e6014c21de980530867a6014c219f58053087796014c219e580530867f65d0c219f997430867d65d0c219f197430873f54d0c21cf953430873d54d0c21cf15343086ee62d0c21bb58b43086f661d0c21bd587430873f65d0c21cf997430873d65d0c21cf197430873f53d0c21cf94f430873d53d0c21cf14f43087ae62d0c21eb58b43087b661d0c21ed587430867f6590c219f996430867d6590c219f19643086bd6490c21d794e430875d5390c219fd95430867e6550c219f595430867c6550c21cfd51430873e5450c21cf551430873c5450c21d794d430875d5350c21bbd8943086ec6250c21bdd8543086f46150c21cfd95430873e6550c21cf595430873c6550c21e7d8d430873f5350c21cf94d430879e5350c21c794d430873d5350c21e754d430871d5350c21cf14d43087af6250c21eb18943087b76150c21ed185430867f6510c219f994430867d6510c219f19443086be6410c219f992520867d64948219f98e520867d6394821cfd0e520873d43948219f597420867f65908219f596420873e5490821cf55242086f66190821bd586420867f65508219fd94420867d6510821cf950420873d5410821bd98442086f561108219f59732086be64cc821af59332086ed65cc821db597320866d65cc821eb99332087ad64cc821dbd4f320876d53cc821ebd0f32087ad43cc821f9d8732086ed61cc821f918732086ed60cc8219fd96320867d658c821d794e320875d538c821bb98a320876e528c821bd98632086f5618c8219fd95320876e524c821bdd85320867f650c8219f59432086be640c821af590320875e530c821d754c32086f6610c821bd58432086fa600c821be580320876d650c8219b59432087ae640c821eb59032086ee630c821f398c320876f530c821f394c320876d530c821f354c32087af430c821eb50c32087e6610c821bb58432087e5610c821b958432087ea600c821bb58032087e9600c821ba580320867e64944219f592510867e63944219f58e510873f4394421cf50e510876f32
  | 33 => 0x95434873e6550d21cf595434873c6550d21e7d8d434873f5350d21e7d4d434871f5350d21cf94d434873d5350d21cf14d434879c5350d21c714d434867f6510d219f994434867d6510d219f19443486be6410d21bb98843486ed6210d21bd98443486f56110d219f997424873f54d0921cf15342486f661d0921bd587424867e65909219f195424873f5450921cf15142486f76150921bd185424867e6510921eb508424867e65cc921af99332486bd64cc921d7d4f324875c53cc921bd98732486f561cc9219f99632486ee658c921db996324866e658c921bb58e324876e538c921db14e32487af438c921eb50e32487e7618c921bb98632487e4618c9219f195324875f534c921d714d32486f7614c921bd185324876c654c9219b19532487cf634c921f3d4d324876e534c921db14d32487cc534c921ebd0d32487ad434c921f9d8532486ec614c921f918532486e4614c9219f99432486be640c921af59032486ee620c921bd98432486fa600c921be580324867e65d0521cfd53414873c54d0521bb98b41486ed62d05219f996414867f65505219f595414867c6550521cfd51414873c5450521bbd8941486ec62505219f99441487b541105219f99731486be64cc521af593314875f53cc521d714f31486ee62cc521bb58b314867e658c521bd9963148776658c5219d99631486f5638c521dd94e3148774538c521edd0e31487b5438c521f9d8a31486f6628c521f918a31487e6328c521f94ca314867f654c5219f595314867c654c521d7d4d314875c534c521bbd8931486ec624c521bd1953148774654c5219d19531487d7634c521f5d4d3148776534c521dd14d31487d4534c521edd0d31487b5434c521f9d8931486f4624c521f918931486e4624c521f98c931487e5324c5219f99431486be640c521af59031486ee620c521bb58831486f6610c521be98031486f9600c521bdd8f21486f563c8521dd94f214877453c8521edd0f21487b543c8521f98cb21487e532c8521bbd8e21486ed6388521db94e214876c5388521ebd0e21487ad4388521f9d4621487e63188521f94c6214867e64d41219f593504867e63d41219f58f504873f43d4121cf50f504876e32d4121db4cb504877631d4121dd4c7504877721d4121db887504877b5094121afd9150486bc6454121b7d8d50486dc6354121de540504867e64141219f590504867e63141219f58c504873f4314121cf50c504867e63d50219f58f540867e62d5021db98b540867e61d5021dd987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf55054086de6315021b758c54086fa6015021be580540867e6415021cf990540867e6315021d798c540865e631502
  | 34 => 0x886ed600ca21fa58032886e9600ca21cf952418873d5490621bb98a41886ed6290621cf950418873d5410621bb98841886ed6210621ed50441886be64cc621af593318875e538c621d754e31886ee628c621bb58a31886f5658c621dd5963188776538c621f594e31887d5538c621dd14e31887b7438c621ed50e31886f6628c621f998a31887e5628c621f9cca31887e4328c621bbd8931886ec624c621bdd953188777654c621f5d8d3188776534c621dd14d31887b7434c621ed50d31887e7624c621bd18931887e4624c621b918931887e7324c621f90c931886be640c621af590318875e530c621d754c31886ee620c621bb58831886fa600c621be58031886ed65c8621db59721886ee63c8621bb18f218876f53c8621db54f21887af43c8621eb50f21886ed60c8621bd597218877565c8621bdd8f21886f563c8621dd94f218877453c8621edd0f21887b543c8621af99350886bd64d4221ded42508867e64942219f592508867e63942219f58e508873f4394221cf50e508867f64542219f191508867f63542219f18d508873f4354221cf50d50887763154221dd4c550887772154221de540508867e63d51219f58f544867e60d51219f583544873f5495121b798e54486dd63951219f992544867e6395121d798e544865e63951219f58e544875d63951219758e544867d6295121db58a544867d6195121dd586544867e60951219f582544873f64551219fd8d544867c63551219fd89544876f62551219fd85544877761551219fd81544867c60551219f994544873d5415121cf990544867e63151219f58c544867e60151219f580544867e64d4d219f593534867e60d4d219f58353486be6494d21af592534875f5394d219f992534873e6494d218f992534867d6494d21cf592534863d6494d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d219f582534867f6454d219f191534875f6354d219fd89534876f6254d219bd89534867f6154d21ddd8553486776154d219fd81534867c6054d219f99453486be6414d21af590534875d5314d21be98053486f96014d219f990534873e6414d218f990534867d6414d21cf590534863d6414d21d798c534876d6214d21dd584534867e6014d21de980534867a6014d219f58053487796014d219e580534867f65d0d219f997434867d65d0d219f197434873f54d0d21cf953434873d54d0d21cf153434873f65d0d21cf997434873d65d0d21cf197434873f53d0d21cf94f434873d53d0d21cf14f434867f6590d219f996434867d6590d219f19643486bd6490d21d7d4e434875c5390d21bb98a43486ed6290d21bd98643486f56190d219fd95434867e6550d219f595434867c6550d21cfd51434873e5450d21cf551434873c5450d21d7d4d434875c5350d21cfd
  | 35 => 0xa600c721be58031c86f5650c721dd59431c87b6640c721ed59031c87d6630c721ddd4c31c8775530c721edd0c31c87b5430c721f998831c86f5620c721f958831c86e5620c721f98c831c87e5320c721fc98031c86f5600c721fc58031c86f1600c721af99350c86bd64d4321ded4250c867e64943219f59250c867e63943219f58e50c873f4394321cf50e50c867f64543219f19150c867f63543219f18d50c873f4354321cf50d50c876e3254321db4c950c87795014321be98354886f960d52219f98f548867d63d5221db58b548877661d52219f983548877a60d52219e983548867d60d5221de583548867960d5221cfd52548867e63952219f58e548867e60952219f582548873f64552219fd8d548867c63552219fd81548867c6055221cf550548873e64152219f98c548867d6315221db588548877661152219f980548867d60152219f993538867d64d4e21db58b538877661d4e219f983538867d60d4e21af99253886bd6494e21d7d4e538867e6494e21cf992538863e6494e219f592538873d6494e218f59253887766194e219f982538867d6094e219fd91538867c6454e21d7d8d538876f6254e219fd81538867c6054e21af99053886bd6414e21d754c53886fa6014e21be580538867e6414e21cf990538863e6414e219f590538873d6414e218f590538875e6314e21db58853887766114e219f980538877a6014e219e980538867d6014e21de58053886796014e219fd97438867e65d0e219f597438867c65d0e21cfd53438873e54d0e21cf553438873c54d0e21bb98b43886ed62d0e21cfd97438873e65d0e21cf597438873c65d0e21cfd4f438873e53d0e21cf54f438873c53d0e21eb98b43887ad62d0e219fd96438867e6590e219f596438867c6590e21bd98643886f56190e219fd95438867e6550e219f595438867c6550e21cfd51438873e5450e21cf551438873c5450e21bbd8943886ec6250e21cfd95438873e6550e21cf595438873c6550e21e7d8d438873f5350e21cf94d438873d5350e21cf14d43887af6250e21eb189438867f6510e219f994438867d6510e219f19443886f66110e21bd584438873e54d0a21cf55342886f661d0a21bd587428873e5450a21cf55142886f76150a21bd18542886be64cca21af593328875e53cca21d754f32886f661cca21bd587328876d65cca21eb99332887ad64cca21dbd4f32887ce53cca21db54f32887cd53cca21ebd0f32887ad43cca21f998732886ed61cca21f958732886ed60cca21d794d328875d534ca21bdd8532886f4614ca21af99032886bd640ca21bd58432886fa600ca21be58032886ed650ca21db59432887ae640ca21eb59032887ce630ca21dbd4c328876d530ca21ebd0c32887ad430ca21f998432886ed610ca21f958432886e5610ca21fa98032
  | 36 => 0x4031bb588500c76e5214031db548500c6fa6014031de540500c6fa60d5321be58354c867e63d53219f58f54c876e62d5321dd58754c867e60d5321de98354c867a60d53219f58354c877960d53219e58354c873f54953219f98e54c867d63953219f98254c867d6095321cfd9154c867f63553219f18d54c867f60553219f18154c873d5415321cf99054c867e63153219f58c54c876e6215321dd58454c867e60153219f58054c867e64d4f219f59353c876e62d4f21dd58753c867e60d4f219f58353c86be6494f21af59253c875f5394f219f99253c873e6494f218f99253c867d6494f21cf59253c863d6494f21db98a53c867e6094f219f58253c867f6454f219f19153c875f6354f21ddd8553c867f6054f219f18153c86be6414f21af59053c875d5314f21be98053c86f96014f219f99053c873e6414f218f99053c867d6414f21cf59053c863d6414f21d798c53c876e6214f21dd58453c867e6014f21de98053c867a6014f219f58053c87796014f219e58053c867f65d0f219f99743c867d65d0f219f19743c873f54d0f21cf95343c873d54d0f21cf15343c86f661d0f21bd58743c873f65d0f21cf99743c873d65d0f21cf19743c873f53d0f21cf94f43c873d53d0f21cf14f43c87b661d0f21ed58743c867f6590f219f99643c867d6590f219f19643c86ee6290f21bb58a43c867f6550f219f99543c867d6550f219f19543c873f5450f21cf95143c873d5450f21cf15143c86f76150f21bd18543c873f6550f21cf99543c873d6550f21cf19543c879f6350f21cfd4d43c873e5350f21cf54d43c873c5350f21edd8543c87b46150f219fd9443c867e6510f219f59443c867c6510f21bb98843c86ed6210f21cf95242c873d5490b21bd98642c86f56190b21cf95042c873d5410b21eb50842c86f66110b21bd58442c86be64ccb21af59332c875e538cb21d754e32c86f6618cb21bd58632c876d658cb21db94e32c87ce538cb21f354e32c876c538cb21ebd0e32c87ad438cb21bb98632c87e6618cb21f958632c86f4614cb21bbd9532c876f654cb21f3d8d32c876e534cb21db14d32c87af434cb21eb50d32c87e7614cb21bb18532c87e4614cb21b918532c86be640cb21af59032c875e530cb21d754c32c86f6610cb21bd58432c86fa600cb21be58032c873e54d0721cf55341c86ee62d0721bb58b41c873e5450721cf55141c86ef6250721bb18941c86be64cc721af59331c875e53cc721d754f31c86ee62cc721bb58b31c86f565cc721dd59731c87b664cc721ed59331c877753cc721f594f31c877553cc721f554f31c87b743cc721ed50f31c87e662cc721bd58b31c87e562cc721f98cb31c87e532cc721bd58331c875e534c721d754d31c86ef624c721bb18931c86be640c721af59031c86ee620c721bb58831c86f
  | 37 => 0xdb94b310c76d52cc431e7993310c79d64cc431e7953310c79d54cc431f394b310c7cd52cc431cf952310c73d548c431b758e310c75e538c431db94a310c76d528c431ed952310c7b5548c431bd58e310c776538c431f594e310c7b7438c431ed50e310c6f6628c431f994a310c775528c431f954a310c765528c4319fd95310c73e544c431cf551310c79f434c431e750d310c6ef624c431bb189310c76e524c431db549310c6df654c431d7d95310c65f654c431e7951310c79d544c431f3d89310c7cc624c431f3949310c7cd524c431b7d85310c75e514c431f5905310c7d5414c431bdd95310c777654c4319dd95310c7b6544c431ed551310c6f7634c431f5d8d310c776534c431f594d310c7b7434c431f590d310c7b5434c431f550d310c795434c431f9d89310c6f4624c431f9189310c6e4624c431f9949310c775524c431f9549310c765524c431af993500c6bd64d4031cf953500c73d54d4031bb98b500c6ed62d4031db94b500c76d52d4031cf952500c73d5494031db94a500c76d5294031ded42500c67e64940319f592500c73f4394031cf50e500c67e62940319f58a500c77b5494031de952500c7ba5494031ce952500c7795494031ee552500c7395494031de152500c7bb4394031ee50e500c77b5294031de94a500c7ea5294031da94a500c7795294031fa54a500c7695294031de14a500c7db3194031fc8c6500c7d93194031fc4c6500c77b6494031de992500c7796494031de192500c7786394031ded0e500c73b4394031de90e500c7794394031ce50e500c7784394031ded8a500c77a6294031de58a500c7786294031ded0a500c77a4294031de50a500c7784294031decca500c77a3294031de4ca500c7783294031de186500c77b4194031de906500c7794194031de106500c77b3194031de8c6500c7793194031cf951500c73d5454031db949500c76d52540319fd91500c67c6454031cfd0d500c73d43540319fd89500c67c6254031dd8c5500c7753154031ded95500c77b5454031de951500c7ba5454031ce951500c7795454031ee551500c7395454031de151500c7bb4354031ee50d500c77b5254031de949500c7ea5254031da949500c7795254031fa549500c7695254031de149500c7db3154031fc8c5500c7d93154031fc4c5500c77b6454031de991500c7796454031de191500c77a6354031ded0d500c73b4354031de90d500c7794354031ce50d500c7784354031ded89500c77a6254031de589500c7786254031ded09500c77a4254031de509500c7784254031decc9500c77a3254031de4c9500c7783254031de985500c77b4154031de905500c7794154031de105500c77b3154031de8c5500c7723154031de4c5500c7713154031de0c5500c6be6414031af590500c73e5414031cf550500c6ee621
  | 38 => 0x6430c67d6590c31af592430c73e5490c31cf552430c6f66190c31bd586430c67f6550c31cfd51430c73e5450c31cf551430c73c5450c31afd95430c73f6550c318fd95430c79f6350c31cf94d430c67f6510c319f594430c6be6410c31cf950430c73d5410c31bd984430c6f56110c31af993520c6bd64d4831cf953520c73d54d4831be983520c6f960d4831cf952520c73d5494831dbd4a520c67e64948319f592520c73f4394831cf50e520c67e60948319f582520c76f5494831db952520c7ae5494831cb952520c76d5494831eb552520c72d5494831db152520c7af4394831eb50e520c7e46194831dbd92520c76e6494831db592520c76c6494831db18e520c76f4394831cbd0e520c76e4394831db50e520c72d4394831db10e520c76e6194831db186520c76f6094831db982520c76d6094831db182520c73e5454831cf551520c67f64548319f191520c73f4354831cf50d520c77461548319fd81520c67c6054831dbd95520c76f5454831db951520c7ae5454831cb951520c76d5454831eb551520c72d5454831db151520c7af4354831eb50d520c7e46154831dbd91520c76e6454831db591520c76c6454831db98d520c76f4354831cbd0d520c76e4354831db50d520c72d4354831db10d520c76e6154831db185520c7646154831db0c5520c76f6054831db981520c76d6054831db181520c6be6414831af590520c73e5414831cf550520c6ee6214831db548520c6fa6014831be580520c67f65d08319f997420c67d65d0831cf953420c73d54d0831b798f420c6dd63d0831db94b420c76d52d0831bd987420c6f561d08319fd96420c67e65908319f596420c73e5490831cf552420c76e5290831db54a420c67f65508319f595420c67c6550831cf951420c73d5450831db949420c76d5250831bdd85420c6f461508319fd94420c67e65108319f594420c73e5410831cf550420c76e5210831db548420c6be64cc831af593320c73e54cc831cf553320c76e52cc831db54b320c6f661cc831bd587320c67d658c831cf952320c73d548c831e750e320c76d528c8319fd95320c73e544c831cf551320c76e524c831bdd85320c6be640c831af590320c73e540c831cf550320c79d430c831db948320c76d520c831bd984320c6f5610c831be980320c6f9600c8319f992510c67d6494431cfd0e510c73d43944319f597410c73e54d0431cf553410c76e52d0431db54b410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c76e5290431db54a410c67f6550431cf951410c73d5450431db949410c76d52504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431db948410c76d5210431af993310c6bd64cc431cf953310c73d54cc431e7d0f310c79d43cc431
  | 39 => 0xc67e65909319f596424c67c6590931dbd4a424c76c5290931bd986424c6f561909319fd95424c67e65509319f195424c76f5250931db149424c67e65109319f594424c67c6510931b798c424c6dd6310931dbd48424c76c5210931bd984424c6f561109319f997324c6be64cc931af593324c79d43cc931db14b324c76f528c931db14a324c6f6618c931bd586324c79d434c931dbd49324c76c524c931bdd85324c6f4614c9319f994324c6be640c931af590324c76f520c931bd984324c6fa600c931be580324c67e65d0531cfd53414c73c54d0531b798f414c6dd63d0531dbd4b414c76c52d05319f996414c73e5490531cf552414c76f5290531db14a414c67f65505319f595414c67c6550531cfd51414c73c5450531b7d8d414c6dc6350531dbd49414c76c52505319f994414c73e5410531cf550414c76f5210531db148414c6be64cc531af593314c76f52cc531db14b314c7b664cc531ed593314c7b743cc531ed50f314c6f562cc531f9d4b314c77452cc531f914b314c76452cc531bd583314c79f438c531e750e314c76f528c531db14a314c7cf528c531f314a314c7d7518c531dbd4b504c76c52d41319f993504c67d64d4131cfd0f504c73d43d41319f98b504c67d62d4131bb98a504c6ed6294131dbd4a504c76c5294131ded42504c6bf6454131af191504c6ef6254131bb189504c76f5254131db149504c76f5214131db148504c77950141319f990504c67d6414131cfd0c504c73d43141319f988504c67d6214131bb98b540c6ed62d5031be983540c6f960d50319f98f540c75e63d50319f98b540c76e62d50319b98b540c67d62d5031db58b540c66d62d50319f987540c77661d50319f983540c77a60d50319e983540c67d60d5031de583540c67960d50319f596540c73f54950319f98a540c67d62950319f982540c67d60950318f596540c73e6395031cf18e540c73f6295031cf98a540c73d6295031cf18a540c73e6195031cf186540c73f6095031cf982540c73d6095031cf182540c73f64550319fd89540c67c62550319fd81540c67c6055031cfd95540c73e6355031cf18d540c73f6255031cf989540c73d6255031cf189540c73e6155031cf185540c73c3155031cfd81540c73e6055031cf581540c73c6055031af990540c73d5415031bb988540c6ed6215031be980540c6f960150319f990540c73e64150318f990540c67e6315031d798c540c67e6215031db988540c66e62150319f588540c76d62150319b588540c67e6115031dd984540c67e6015031de980540c67a60150319f580540c77960150319e580540c67e6494c31cf992530c63e6494c319f592530c73d6494c318f592530c67d65d0c31cfd53430c73e54d0c31cf553430c73c54d0c31af597430c73d65d0c318f597430c73e53d0c319fd9
  | 40 => 0x528ca31db54a328c6f6618ca31bd586328c76e524ca31db549328c6f7614ca31bd185328c6be640ca31af590328c79d430ca31bd584328c6fa600ca31be580328c73f54d0631cf153418c73e5490631cf552418c6de6390631b758e418c73f5450631cf151418c73e5410631cf550418c6de6310631b758c418c6be64cc631af593318c79f43cc631e750f318c6dd65cc631d7597318c79e64cc631e7593318c6f565cc631dd597318c7b664cc631ed593318c7b743cc631ed50f318c6f562cc631dd94b318c6f560cc631bb98a508c6ed6294231ded42508c67e64942319f592508c73f4394231cf50e508c67e6294231db98a508c66e62942319f58a508c76d62942319b58a508c6bf6454231af191508c67f6454231cfd91508c63f64542319f191508c73c64542318f191508c73f4354231cf50d508c67f62542319f189508c77950142319f98b544c67d62d51319f983544c67d60d5131cfd52544c6ee6295131bb58a544c67e64951319f58e544c75d63951319f98a544c76e62951319b98a544c67d6295131db58a544c66d62951319f586544c77561951319f982544c67d6095131bbd89544c6ec6255131bed81544c6f86055131cfd91544c67f6355131d7d8d544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd85544c67f6055131ded81544c67b60551319f181544c77860551319e181544c67e6515131cf550544c73e64151319f988544c67d62151319f980544c67d60151319f997434c73f54d0d31cf153434c6f661d0d31bd587434c73f65d0d31cf997434c73d65d0d31cf197434c7b661d0d31ed587434c67e6590d31af592434c67c6550d31cfd51434c73c5450d31bdd85434c6f46150d31cfd95434c73e6550d31cf595434c73c6550d31e7d8d434c7b76150d31ed185434c67e6510d31af990434c67e64d49319f593524c73f43d4931cf50f524c67e60d49319f583524c76f54d4931db953524c76d54d4931db153524c7af43d4931eb50f524c7e761d4931dbd93524c76e64d4931db593524c76c64d4931dbd8f524c76f43d4931cbd0f524c76e43d4931db50f524c72d43d4931db10f524c76f61d4931db587524c76f60d4931db983524c76d60d4931db183524c76f5294931db548524c67e64149319f590524c73f4314931cf50c524c77561149319f980524c67d6014931bb994524c76e6514931dbd50524c76e5414931db550524c76c5414931ebd0c524c7ad4314931f9584524c76f6414931db990524c76d6414931db190524c76f6314931dbd0c524c72f4314931db90c524c76d4314931cb50c524c76c4314931dbd84524c76d6114931d9584524c76d3114931dbd80524c76e6014931db580524c76c60149319f997424c67d65d09319f197424c76f52d0931db14b424
  | 41 => 0xf31cf15343cc6bd65d0f31cf59743cc73e5490f31cf55243cc6f66190f31bd58643cc73f5450f31cf95143cc73d5450f31cf15143cc6bf6550f31cfd9543cc79f6350f31cf95043cc73d5410f31bd98443cc6f56110f31af99352cc6bd64d4b31cf95352cc73d54d4b31cf95252cc73d5494b31dbd4a52cc67e6494b319f59252cc73f4394b31cf50e52cc67e6094b319f58252cc73e5454b31cf55152cc67f6454b319f19152cc73f4354b31cf50d52cc7776154b319fd8152cc67c6054b31af99052cc6bd6414b31cf95052cc73d5414b31db54852cc6fa6014b31be58052cc67f65d0b319f99742cc67d65d0b31cf95342cc73d54d0b31bd98742cc6f561d0b319fd9642cc67e6590b319f59642cc73e5490b31cf55242cc67f6550b319f59542cc67c6550b31cf95142cc73d5450b31bdd8542cc6f46150b319fd9442cc67e6510b319f59442cc73e5410b31cf55042cc6de6310b31b758c42cc6be64ccb31af59332cc73e54ccb31cf55332cc79d43ccb31db94b32cc76d52ccb31bd98732cc6f561ccb31cf95232cc73d548cb31cf95132cc73d544cb31e750d32cc6f4614cb31af99032cc6bd640cb31cf95032cc73d540cb31db94832cc76d520cb31bd98432cc6f5610cb31be98032cc6f9600cb31cf95341cc73d54d0731b798f41cc6dd63d0731cf95241cc73d5490731cf95141cc73d5450731b7d8d41cc6dc6350731cf95041cc73d5410731af99350cc6bd64d4331cf95350cc73d54d4331cf95250cc73d5494331ded4250cc67e64943319f59250cc73f4394331cf50e50cc67e62943319f58a50cc73e5454331cf55150cc67f64543319f19150cc73f4354331cf50d50cc67f62543319f18950cc6be6414331af59050cc73e5414331cf55050cc6ee6214331bb58850cc7795014331d758f548c67e62d52319f58b548c77661d52319f983548c67d60d5231cfd52548c67e62952319f58a548c67e60952319f582548c73f64552319fd89548c67c62552319fd81548c67c6055231cf550548c73e6415231d758c548c67e62152319f588548c77661152319f980548c67d6015231cf953438c73d54d0e31bd987438c6f561d0e31cf997438c73d65d0e31ed987438c7b561d0e31cf951438c73d5450e31bdd85438c6f46150e31cfd95438c73c6550e31e7d8d438c7b76150e31ed185438c76f5294a319f992528c67d6494a31cfd0e528c73d4394a31dd986528c67e6094a319f582528c67f6454a319f191528c73f4354a31cf50d528c67f6054a319f181528c76d5214a319fd97428c67e65d0a319f597428c6de63d0a31b758f428c67f6590a319f996428c67d6590a31bd986428c6f56190a319fd95428c67d6550a319f195428c67f6510a319f994428c67d6510a31bd984428c6f56110a31af993328c6bd64cca31e750e328c76e
  | 42 => 0xf58b50506ee6294141bb58a505077b5094141de540505067e63141419f58c505073f4314141cf50c505067e62141419f588505073e4114141d7d4e531067e6294c419f58a531067e6094c419f582531073e6454c419fd89531067c6254c419fd81531067c6054c41d754c53106ee6214c41bb58853106fa6014c41be580531073e54d0c41d794f431075d53d0c41bd98743106f561d0c41cf94f431079e53d0c41cf54f431079d53d0c41c754f43107b661d0c41af58743107b561d0c41af983431067d6590c41af592431067f6550c41cf95143106bf6550c41cfd95431079f6350c41cf94d43106bf6150c41af18143106be6410c41d794c431075d5310c41bd98443106f56110c41dbd4a521067e63948419f58e521073f4394841cf50e521067e60948419f582521067f63548419f18d521073f4354841cf50d521067f60548419f18152106de6314841b758c521076d5214841be98052106f96014841db94b421076d52d0841bd98742106f561d08419f596421067f6550841db948421076d5210841bd98442106f561108419fd97321067e65cc8419f59732106be64cc841af593321075e53cc841d754f321067f658c8419f996321067d658c841db94a321076d528c8419fd95321067d654c8419f195321075e534c841d754d321076e524c841db54932106f7614c841bd185321067f650c8419f994321067d650c841af99032106bd640c841bd98432106f5610c841be98032106f9600c841cfd0e511073d4394441af58f411073d53d0441af98341106bd6490441cf95241106f56490441dd95241107b65490441edd0e41107b543904419fd9541106bf6550441cfd95411063f6550441afd8d411073d5350441afd85411073e5150441af18141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441edd0941107b54250441ded42501067e63940419f58e501073f4394041cf50e501067e62940419f58a501067f63540419f18d501073f4354041cf50d501067f62540419f18950107764154041dd50550106de6314041b758c50106ee6214041bb58850107795014041d798f54cc67e62d53319f58b54cc77561d53319f98354cc67d60d5331cfd5254cc67e62953319f58a54cc67e60953319f58254cc73e6395331cf18e54cc73f6295331cf98a54cc73d6295331cf18a54cc73f6195331cf58654cc73f6095331cf98254cc73d6095331cf18254cc73f64553319fd8954cc67c62553319fd8154cc67c6055331cfd9554cc73e6355331cf18d54cc73f6255331cf98954cc73d6255331cf18954cc73f6155331cf58554cc73f6055331cf98154cc73d6055331cf18154cc73d5415331cf99054cc75e63153319f98854cc67d6215331dd58454cc67e60153319f58054cc73f54d0f31cf95343cc73d54d0
  | 43 => 0x539067c6254e419fd81539067c6054e41d754c53906ee6214e41bb58853906fa6014e41be58053906bd65d0e41cf597439073e53d0e41af58743906be60d0e41d794e439075d5390e41bd98643906f56190e41d794d439075d5350e41bdd8543906f46150e41e7d8d439073e5350e41e794d439073d5350e41e754d439071d5350e41afd8543907b76150e41ed18543906bc6050e41be98352906f960d4a41dbd4a529067e6394a419f58e529073f4394a41cf50e529067e6094a419f582529067f6354a419f18d529073f4354a41cf50d529067f6054a419f181529076d5214a41db94a429076d5290a41bd98642906f56190a41db949429076d5250a41bdd8542906f46150a419fd97329067e65cca419f59732906be64cca41af593329067f658ca419f996329067d658ca41db94a329076d528ca419fd95329067d654ca419f195329076e524ca41db54932906f7614ca41bd185329067f650ca419f994329067d650ca41af99032906bd640ca41bd98432906f5610ca41be98032906f9600ca41af597419073d65d0641af58f419073d53d0641af98341906f565d0641dd59741906f560d0641bb98b50906ed62d4241bb98a50906ed6294241ded42509067e63942419f58e509073f4394241cf50e509067e6294241db98a509066e62942419f58a509076d62942419b58a509067f63542419f18d509073f4354241cf50d509067f62542419f18950907795014241cfd93535067e62d4d419f58b535067e60d4d419f583535075f5394d41bbd8953506ec6254d41bed8153506f86054d41d754c535067e6214d419f588535067e6014d419f580535067e65d0d41af997435073e65d0d41cf14f43506be61d0d41af592435075f5390d41d714e43506f66190d41bd586435075f5350d41d714d43506f76150d41bd185435079f6350d41cfd4d435079f5350d41c7d4d435073c5350d41e714d43507b76150d41af18543507b46150d419f99443506be6410d419f98f525067d63d4941cfd0f525073d43d49419f983525067d60d4941dbd4a52506fa6094941be582525076d52149419f98c525067d6314941cfd0c525073d43149419f980525067d60149419f997425076f5290941db14a42506f66190941bd586425076f5250941db14942506f76150941bd185425067e6510941eb508425067e65cc9419f597325067c65cc941af99332506bd64cc941dbd4b325076c52cc9419f996325067d658c9419f196325067f654c9419f995325067c654c941bdd8532506f4614c9419f994325067d650c9419f19432506be640c941af590325076f520c941db14832506f6610c941bd58432506fa600c941be58032507b743d0541ed50f41506f560d0541af58e415073f5390541edd46415067e63d41419f58f505073f43d4141cf50f505067e62d41419
  | 44 => 0xb7b5194032de946500cbf25194032dc946500cb795194032fc546500cb715194032de146500cb7b6494032de992500cb796494032de192500cb786394032ded0e500cb3b4394032de90e500cb794394032ce50e500cb784394032de18a500cb7b4294032de90a500cb794294032de10a500cb7b3294032de8ca500cb793294032ded86500cb7a6194032de586500cb786194032cf951500cb3d5454032dd945500cb7551540329fd91500ca7c6454032cfd0d500cb3d4354032db8c9500cb6d32540329fd85500ca7c6154032ded95500cb7b5454032de951500cbba5454032ce951500cb795454032ee551500cb395454032de151500cbbb4354032ee50d500cbdb3254032fa8c9500cbd93254032fa4c9500cb7b5154032de945500cbf25154032dc945500cb795154032fc545500cb715154032de145500cb7b6454032de991500cb796454032de191500cb7a6354032ded0d500cb3b4354032de90d500cb794354032ce50d500cb784354032de989500cb7b4254032de909500cb794254032de109500cb7b3254032de8c9500cb6a3254032de4c9500cb693254032de0c9500cb7b6154032de985500cb796154032de185500cabe6414032af590500cb3e5414032cf550500caf66114032bd584500cb765114032dd544500cafa6014032de540500caee62d4f41bb58b53d075f5394f419f98a53d067d6294f419f98253d067d6094f41cf99153d067f6254f419f18953d067f6054f419f18153d075d5314f41d794f43d075d53d0f41bd98743d06f561d0f41cf94f43d079e53d0f41cf54f43d079d53d0f41c754f43d06be61d0f41ed98743d07b561d0f41afd9543d073f6550f41e7d8d43d073e5350f41af18543d075e5310f41d754c43d06f66110f41bd58443d06de63d4b41b758f52d076f5294b419f98e52d067d6394b41cfd0e52d073d4394b419f98252d067d6094b419fd8d52d067c6354b41cfd0d52d073d4354b419fd8152d067c6054b41db54852d076e52d0b41db54b42d06f661d0b41bd58742d076e5210b41db54842d07ad4210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d06be64ccb41af59332d076e52ccb41db54b32d067f658cb419f99632d067d658cb41d794e32d075d538cb419fd9532d067d654cb419f19532d06f7614cb41bd18532d067f650cb419f99432d067d650cb41af99032d06bd640cb41d794c32d075d530cb41db94832d076d520cb41bd98432d06f5610cb41be98032d06f9600cb41ded4250d067e63943419f58e50d073f4394341cf50e50d067e62943419f58a50d067f63543419f18d50d073f4354341cf50d50d067f62543419f18950d06de6314341b758c50d06ee6214341bb58850d07795014341d7d4e539067e6294e419f58a539067e6094e419f582539073d6454e419fd89
  | 45 => 0x3908329fd95420cb3e5450832cf551420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420cabe64cc832af593320cb3e54cc832cf553320cb9f43cc832e750f320cb9e64cc832e7593320cb9e54cc832e7553320cb3e548c832cf552320cadd638c832d794e320cbae548c832eb552320caed638c832db94e320cbce538c832ebd0e320cbad438c832bb986320ca7f654c832cf951320cb3d544c832e7d0d320cb9d434c832bdd85320caf4614c832b7d95320cb5f654c83297d95320cb9e544c832e7551320cadf624c832d7949320cbce424c832f3509320cbd7614c832f5185320caef654c832dbd95320ca6f654c832eb951320cbad544c832bbd8d320cbcf634c832db94d320cbce534c832ebd0d320cbce434c832eb50d320cbcd434c832e350d320cbe7614c832bb185320cbe4614c832b9185320cabe64d4432af593510cb3e54d4432cf553510cafa60d4432be583510cb3e5494432cf552510cb7751944329f992510ca7d6494432cfd0e510cb3d43944329f982510ca7d6094432ddd52510cb765494432ed952510cb365494432dd552510cbb55494432cd552510cb745494432edd0e510cbb54394432f918a510cbd73294432f98ca510cbd53294432f94ca510cb776494432dd992510cb756494432dd192510cb746394432ddd0e510cb374394432dd90e510cb754394432cd50e510cb744394432dd18a510cb774294432dd90a510cb754294432dd10a510cb773294432dd8ca510cb753294432ddd82510cb766094432dd582510cb746094432cf951510cb3d54544329fd91510ca7c6454432cfd0d510cb3d4354432db8c9510cb6d32544329fd81510ca7c6054432ddd95510cb775454432dd951510cbb65454432cd951510cb755454432ed551510cb355454432dd151510cbb74354432ed50d510cbe46254432f5cc9510cbe63254432f54c9510cbe53254432ddd91510cb766454432dd591510cb746454432dd98d510cb774354432cdd0d510cb764354432dd50d510cb354354432dd10d510cb766254432ddd09510cb764254432dd509510cb744254432ddcc9510cb763254432d98c9510cb753254432d94c9510cb743254432ddd81510cb766054432dd581510cb746054432af990510cabd6414432cf950510cb3d5414432bd984510cb755114432be980510caf96014432af993500cabd64d4032cf953500cb3d54d4032bd987500caf561d4032dd947500cb7551d4032cf952500cb3d5494032dd946500cb755194032ded42500ca7e64940329f592500cb3f4394032cf50e500ca7e61940329f586500cb7b5494032de952500cbba5494032ce952500cb795494032ee552500cb395494032de152500cbbb4394032ee50e500cbdb3294032fa8ca500cbd93294032fa4ca500c
  | 46 => 0x32dd90b514cb7542d4532dd10b514cb7732d4532dd8cb514cb7760d4532dd983514cb7560d4532dd183514cb775194532dd544514ca7e64145329f590514cb3f4314532cf50c514cb6f32145329f980514ca7d6014532bd994514cb766514532ddd50514cb765414532dd550514cb745414532edd0c514cbb54314532f9588514cbe73214532f58c8514cb776414532dd990514cb756414532dd190514cb776314532ddd0c514cb374314532dd90c514cb754314532cd50c514cb744314532ddd88514cb774214532dd908514cb754214532dd108514cb773214532d9cc8514cb763214532dd4c8514cb776014532dd980514cb756014532dd180514cb7751d4132dd147504ca7e64d41329f593504cb3f43d4132cf50f504ca7e61d41329f587504caf66194132bd586504cb775194132dd146504cb7b5094132afd91504cabc6454132bdd85504caf46154132ddd45504cb745154132ddd44504cb745114132de540504ca7e64141329f590504cb3f4314132cf50c504ca7e61141329f584504caf661d5032bd587540cafa60d5032be583540ca7e63d5032d798f540ca7e62d5032db98b540ca7e61d5032dd987540ca7661d50329f587540cb7561d50329d587540ca7e60d5032de983540ca7a60d50329f583540cb7960d50329e583540ca7d6595032cfd52540ca7e61950329f586540ca7e60950329f582540ca3d6595032cf98e540cb3c6395032cf98a540cb3c6295032cfd86540cb3e6195032cf586540cb3c6195032cfd82540cb3e6095032cf582540cb3c6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3f6555032cf98d540cb3c6355032cf989540cb3c6255032cf0c9540cb3f6155032cf985540cb3d6155032cf185540cb3f6055032cf981540cb3d6055032cf181540cabe6415032cf550540caf66115032bd584540cafa6015032be580540ca7e6415032cf990540ca3e64150329f98c540cb5e63150329f988540cb6e62150329f984540cb7661150329d984540ca7d6115032dd584540ca7561150329f980540cb7a60150329e980540ca7d6015032de580540ca7960150329f992530cb3e6494c328f992530ca7d6494c32cf592530ca3d6494c329f597430cb3f54d0c32cf953430cb3d54d0c32cf153430cabd65d0c32cf597430ca3d65d0c32cf94f430ca7f6590c329f596430cabd6490c32cf952430cb3d5490c32bb98a430caed6290c329fd95430cb3f5450c32cf951430cb3d5450c32cf151430cabf6550c32cfd95430ca3f6550c32e7d8d430cb3e5350c329fd94430ca7d6510c32af990430cb3e5410c32cf550430caee6210c32bb588430ca7e64948329f592520cb3f4394832cf50e520ca7d65d0832cf953420cb3d54d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd6
  | 47 => 0x98b438caed62d0e32cf997438cb3d65d0e32eb98b438cbad62d0e32cf951438cb3d5450e32bbd89438caec6250e32cfd95438cb3c6550e32e7d8d438cbaf6250e32eb189438cb3f54d0a32cf153428cb3e5490a32cf552428cade6390a32b758e428cb3f5450a32cf151428cb3e5410a32cf550428cade6310a32b758c428cabe64cca32af593328cb9f43cca32e750f328cadd65cca32d7597328cb9e64cca32e7593328caed65cca32db597328cbae64cca32eb593328cbaf43cca32eb50f328caed61cca32bb583328cb7751946329f992518ca7d6494632cfd0e518cb3d4394632dbcca518ca7e60946329f582518ca7f64546329f191518cb3f4354632cf50d518ca7f60546329f181518cb755114632bd986508caf56194232ded42508ca7e64942329f592508cb3f4394232cf50e508ca7e6194232dd986508ca7661942329f586508cb7561942329d586508cabf6454232af191508ca7f6454232cfd91508ca3f64542329f191508cb3c64542328f191508cb3f4354232cf50d508ca7f61542329f185508cb7950142329f987544ca7d61d51329f983544ca7d60d5132cfd52544caf66195132bd586544ca7e64951329f58e544cb5d63951329f58a544cb6d62951329f986544cb7661951329d986544ca7d6195132dd586544ca7561951329f982544ca7d6095132bdd85544caf46155132bed81544caf86055132cfd91544ca7f6355132d7d8d544ca7f6255132dbd89544ca7f6155132ddd85544ca7761551329f185544cb7461551329d185544ca7f6055132ded81544ca7b60551329f181544cb7860551329e181544ca7e6515132cf550544cb3e64151329f984544ca7d61151329f980544ca7d60151329f997434cb3f54d0d32cf153434caee62d0d32bb58b434cb3f65d0d32cf997434cb3d65d0d32cf197434cbae62d0d32eb58b434ca7e6590d32af592434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d32cfd95434cb3e6550d32cf595434cb3c6550d32e7d8d434cbaf6250d32eb189434ca7e6510d32af990434ca7e65d0932cfd53424cb3c54d0932b798f424cadd63d09329f996424cb3e5490932cf552424ca7f65509329f595424ca7c6550932cfd51424cb3c5450932b7d8d424cadc63509329f994424cb3e5410932cf550424cabe64cc932af593324cbae64cc932eb593324cbaf43cc932eb50f324caed61cc932bb583324cb9f438c932e750e324cbcf528c9329f993514ca7d64d4532cfd0f514cb3d43d45329f983514ca7d60d4532ddd53514cb7654d4532dd553514cb7454d4532edd0f514cbb543d4532f9d8b514cbe732d4532f58cb514cb7764d4532dd993514cb7564d4532dd193514cb7763d4532ddd0f514cb3743d4532dd90f514cb7543d4532cd50f514cb7443d4532ddd8b514cb7742d45
  | 48 => 0x210a3f6550842afd8d4210b3d5350842afd894210b3e5250842af1814210aef6550842dbd954210a6f6550842bbd914210baf6450842db9514210bae5450842ddd465110a7e63944429f58e5110b3f4394442cf50e5110a7e60944429f5825110a7f63544429f18d5110b3f4354442cf50d5110a7f60544429f1815110ade6314442b758c5110b755114442be9805110af96014442ded425010a7e63940429f58e5010b3f4394042cf50e5010a7e61940429f5865010a7f63540429f18d5010b3f4354042cf50d5010b6e4254042db5095010a7f61540429f1855010ade6314042b758c5010af66114042bd5845010b795014042d798f54ccb6d62d53329f98754cca7d61d53329f98354cca7d60d5332cfd5254cca7e61953329f58654cca7e60953329f58254ccb3e6395332cf18e54ccb3f6295332cf58a54ccb3f6195332cf98654ccb3d6195332cf18654ccb3f6095332cf98254ccb3d6095332cf18254ccb3f64553329fd8554cca7c61553329fd8154cca7c6055332cfd9554ccb3e6355332cf18d54ccb3f6255332cf58954ccb3f6155332cf98554ccb3d6155332cf18554ccb3f6055332cf98154ccb3d6055332cf18154ccb3d5415332cf99054ccb5e6315332db58854cca7e61153329f58454cca7e60153329f58054ccb3f54d0f32cf95343ccb3d54d0f32cf15343ccabd65d0f32cf59743ccb3e5490f32cf55243ccaee6290f32bb58a43ccb3f5450f32cf95143ccb3d5450f32cf15143ccabf6550f32cfd9543ccb9f6350f32cf95043ccb3d5410f32bb98843ccaed6210f32cf95342ccb3d54d0b32b798f42ccadd63d0b32cf95242ccb3d5490b32cf95142ccb3d5450b32b7d8d42ccadc6350b32cf95042ccb3d5410b32af99351ccabd64d4732cf95351ccb3d54d4732cf95251ccb3d5494732ddd4651cca7e64947329f59251ccb3f4394732cf50e51cca7e60947329f58251ccb3e5454732cf55151cca7f64547329f19151ccb3f4354732cf50d51cca7f60547329f18151ccabe6414732af59051ccb3e5414732cf55051ccb755114732be98051ccaf96014732af99350ccabd64d4332cf95350ccb3d54d4332cf95250ccb3d5494332ded4250cca7e64943329f59250ccb3f4394332cf50e50cca7e61943329f58650ccb3e5454332cf55150cca7f64543329f19150ccb3f4354332cf50d50cca7f61543329f18550ccabe6414332af59050ccb3e5414332cf55050ccaf66114332bd58450ccb795014332d758f548cb6e62d52329f987548ca7d61d52329f983548ca7d60d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cf550548cb3e6415232d758c548cb6e62152329f984548ca7d61152329f980548ca7d6015232cf953438cb3d54d0e32bb
  | 49 => 0x7f6154e429f1855390a7f6054e429f1815390b5d5314e42bd9845390af56114e42be9805390af96014e42af5974390b3d65d0e42cf94f4390abd62d0e42af9834390b5e5390e42d754e4390aee6290e42bb58a4390b5e5350e42d754d4390aef6250e42bb1894390b9f6350e42cf94d4390b9e5350e42cf54d4390b9d5350e42c754d4390abf6250e42ebd894390bac6250e42af1814390abd65d0a42cf5974290abd63d0a42cf54f4290abe60d0a42bb5974290b6d65d0a42bb5834290afa60d4642be5835190b7751946429f98e5190a7d6394642cfd0e5190b3d43946429f9825190a7d60946429fd8d5190a7c6354642cfd0d5190b3d43546429fd815190a7c6054642dd5445190af661d4242bd5875090af66194242bd5865090b7b50942429f98e5090a7d6394242cfd0e5090b3d43942429f9865090b7661942429d9865090a7d6194242dd5865090a7561942429fd8d5090a7c6354242cfd0d5090b3d43542429fd855090a7c6154242de5405090b3f64d4d429f9875350a7d61d4d429f9835350a7d60d4d42d7d4e5350af76154d42bd1855350afb6054d42be1815350b5d5314d429f9845350a7d6114d429f9805350a7d6014d429f9974350abe65d0d42cf9974350b3c53d0d42af98b4350abd6490d42d7d4e4350b5c5390d42bb98a4350aed6290d42d7d4d4350b5c5350d42bbd894350aec6250d42e7d8d4350b3f5350d42e7d4d4350b1f5350d42cf14d4350b9c5350d42ebd894350abc6250d42eb1894350a7e6510d42af9904350baf43d0942eb50f4250aed60d0942af58e4250b3f5390942ebd4a4250a7e63d45429f58f5150b3f43d4542cf50f5150a7e60d45429f5835150b775194542be9825150af96094542dd5445150a7e63145429f58c5150b3f4314542cf50c5150a7e60145429f5805150a7e63d41429f58f5050b3f43d4142cf50f5050a7e61d41429f5875050af66194142bd5865050b7b5094142de5405050a7e63141429f58c5050b3f4314142cf50c5050b3e42141429f9845050a7d6114142d7d4e5310a7e6194c429f5865310a7e6094c429f5825310b3e6454c429fd855310a7c6154c429fd815310a7c6054c42d754c5310af66114c42bd5845310afa6014c42be5805310b3e54d0c42d794f4310b5d53d0c42bb98b4310aed62d0c42cf94f4310b9e53d0c42cf54f4310b9d53d0c42c754f4310bae62d0c42af58b4310bad62d0c42af9834310a7d6590c42af5924310a7f6550c42cf9514310abf6550c42cfd954310b9f6350c42cf94d4310abf6250c42af1814310abe6410c42d794c4310b5d5310c42bb9884310aed6210c42cfd0e5210b3d4394842af58f4210b3d53d0842af9834210abd6490842cf9524210aed6490842db9524210bae5490842ebd0e4210bad43908429fd954210abf6550842cfd954
  | 50 => 0xd4143e7d4f5050ebe62d4143af58b5050ebe61d4143af5875050f9d6394143e7d4e5050ebe6294143af58a5050f3e5294143cf14a5050ebe6194143af5865050f3e5194143cf1465050ebe6094143cfd425050fbb5094143e7d8d5050f9f5354143afd895050faf6254143abd895050ebc6254143eb1895050eac6254143afd855050fb76154143add855050ebc6154143ed1855050eb46154143eed415050f3e5054143af9945050f9d6314143cfd4c5050f9f5314143af9885050fae6214143ab9885050ebd6214143eb5885050ead6214143cf9485050f3c5214143af9845050fb66114143ad9845050ebd6114143ed5845050eb56114143cf9445050f3c5114143cfd405050fba5014143cf5405050fb95014143ce5405050f3e6295043cf58a5410f3e6195043cf5865410f3e6095043cf5825410ebd6490c43cf9524310edd6490c43d79524310f9e5490c439fd954310f3e5450c43afd954310f3f6550c438fd954310ebf6350c43cf94d4310edf6550c43d7d954310e5f6550c43b7d914310f9f6450c43d79514310f9e5450c43c79514310f6f5294843cfd0e5210f3d43948439f9865210e7d61948439f9825210e7d6094843cfd0d5210f3d43548439fd855210e7c61548439fd815210e7c6054843db5485210ef66114843bd5845210efa6014843be5805210f775194443cfd0e5110f3d43944439f98a5110e7d62944439f9825110e7d6094443cfd0d5110f3d43544439fd895110e7c62544439fd815110e7c6054443bb9885110eed6214443dd5445110efa6014443be5805110f7b5094043cfd0e5010f3d43940439f98a5010e7d62940439f9865010e7d6194043cfd0d5010f5e4354043cf50d5010f5d43540439fd895010e7c62540439fd855010e7c6154043bb9885010eed6214043bd9845010ef56114043de5405010ef661d4f42bd58753d0b5f5394f429f98653d0a7d6194f429f98253d0a7d6094f42cf99153d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42d794f43d0b5d53d0f42bb98b43d0aed62d0f42cf94f43d0b9e53d0f42cf54f43d0b9d53d0f42c754f43d0abe62d0f42eb98b43d0bad62d0f42afd9543d0b3f6550f42e7d8d43d0b3e5350f42af18943d0b5e5310f42d754c43d0aee6210f42bb58843d0ade63d4742b758f51d0b7751947429f98e51d0a7d6394742cfd0e51d0b3d43947429f98251d0a7d60947429fd8d51d0a7c6354742cfd0d51d0b3d43547429fd8151d0a7c6054742dd54451d0b7b50943429f98e50d0a7d6394342cfd0e50d0b3d43943429f98650d0a7d61943429fd8d50d0a7c6354342cfd0d50d0b3d43543429fd8550d0a7c6154342b798c50d0add6314342bd98450d0af56114342de54050d0b5f5394e429f9865390a7d6194e429f9825390a7d6094e42cf5915390a
  | 51 => 0x3b75834390f6f5294a43cfd0e5290e7e6194a439f5865290e7e6094a439f5825290f3f4354a439fd855290e7c6154a439fd815290e7c6054a43db5485290ef66114a43bd5845290efa6014a43be5805290f775194643cfd0e5190e7e62946439f58a5190e7e60946439f5825190f3f43546439fd895190e7c62546439fd815190e7c6054643bb9885190eed6214643dd5445190efa6014643be5805190f7b5094243cfd0e5090e7e62942439f58a5090e7e61942439f5865090f3f43542439fd895090e7c62542439fd855090e7c6154243bb9885090eed6214243bd9845090ef56114243de5405090edd60d0d43e7d4e4350ebe6290d43af58a4350ebe6190d43af5864350ebe6090d43af5824350e7e61d49439f5875250e7e60d49439f5835250f6f5294943bdd855250ef46154943bed815250ef86054943db5485250e7e61149439f5845250e7e60149439f5805250e7e62d45439f58b5150e7e60d45439f5835150f775194543bbd895150eec6254543bed815150ef86054543dd5445150e7e62145439f5885150e7e60145439f5805150e7e62d41439f58b5050e7e61d41439f5875050f7b5094143bbd895050eec6254143bdd855050ef46154143bb9885050eed6214143bd9845050ef56114143de5405050e7e6214143db9885050e6e62141439f5885050f6d62141439b5885050e7e6114143dd9845050e7661141439f5845050f7561141439d5845050ebe62d4d43af58b5350ebe61d4d43af5875350ebe60d4d43af5835350f9f62d4d43e798b5350f9d62d4d43e718b5350f9f61d4d43e79875350f9d61d4d43e71875350f9f60d4d43e79835350f9d60d4d43a75835350f9c60d4d43cfd4f5250f9f53d4943af9875250ebd61d4943af9835250ebd60d4943e758e5250f9f5394943af98a5250f3f5294943ebd4a5250ebe6194943af5865250ebe6094943af5825250f9f6354943e7d4d5250faf5254943cf9495250ebf6154943edd855250eb76154943af1855250fb46154943ad1855250ebf6054943eed815250ebb6054943af1815250fb86054943ae1815250ebe6514943cfd4c5250f9f5314943cfd485250fae5214943cf5485250fad5214943af9845250ebd6114943af9805250ebd6014943cfd4f5150f9f53d4543af98b5150ebd62d4543af9835150ebd60d4543e758e5150f9f5394543af98a5150ebd6294543af9865150f3f5194543edd465150ebe6094543af5825150f9f6354543e7d4d5150ebf6254543ebd895150eaf6254543af1895150fac6254543ab1895150fb75154543cf9455150ebf6054543eed815150ebb6054543af1815150fb86054543ae1815150ebe6514543cfd4c5150f9f5314543af9885150ebd6214543cfd445150fb65114543cf5445150fb55114543af9805150ebd6014543e7d8f5050f3f53
  | 52 => 0x6006c009000c0220000000006400000000090004000000c00a006800600080050010001000403d000000000040070028008001c000000000c000401f0004000000800200540000000017000000c007c0010024000002800300000000000000000000200080030004085000c0020084003000c000003400f000800100400030000006004c001010001a003400000000000010007000c0000020000000000d0000000001001d01340140010000000c01e0048001001800000140010034004000000e000000c003c0010004007002c002003400300080050008024000400000300000000000000000400040060004001000001d001001100b401000000020000001000000000180000004016000000c0018019000c0000044010008006e0000002016c03e000000000040090100022007c004000c000008800e0000002003400000000000094000000c00a00080030002f661d4b43bd58752d0f6f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0eee62d4743bb58b51d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0f7b50943439f98a50d0e7d62943439f98650d0e7d61943439fd8950d0e7c62543439fd8550d0e7c6154343bb98850d0eed6214343bd98450d0ef56114343de54050d0f9d63d4b43af98752d0fb661d4b43ad98752d0ebd61d4b43ed58752d0eb561d4b43af98352d0ebd60d4b43cfd4a52d0faf5294b43af98652d0ebd6194b43af98252d0ebd6094b43ebd4952d0f3e5254b43afd8552d0ebc6154b43afd8152d0ebc6054b43e758c52d0f3f5214b43eb94852d0f3d5214b43eb54852d0ebe6114b43af58452d0ebe6014b43af58052d0f9d63d4743af98b51d0fae62d4743ab98b51d0ebd62d4743eb58b51d0ead62d4743af98351d0ebd60d4743af98a51d0ebd6294743cfd4651d0fb75194743af98251d0ebd6094743afd8951d0ebc6254743edd4551d0f3e5154743afd8151d0ebc6054743e758c51d0ebe6214743af58851d0f3f5114743ed94451d0f3d5114743ed54451d0ebe6014743af58051d0f9d63d4343af98b50d0ebd62d4343af98750d0ebd61d4343af98a50d0ebd6294343cf94a50d0f3c5294343af98650d0ebd6194343cf94650d0f3c5194343cfd4250d0fbb5094343afd8950d0ebc6254343afd8550d0ebc6154343eed4150d0f3e5054343e758c50d0ebe6214343eb98850d0eae6214343af58850d0fad6214343ab58850d0f3e5214343cf14850d0ebe6114343ed98450d0eb66114343af58450d0fb56114343ad58450d0f3e5114343cf14450d0f3f5014343ee94050d0f3d5014343ee54050d0f395014343af5974390f3d65d0e43b75974390f5d65d0e4
  | 53 => 0x4003000c0020004000000800000000100000003016001f002402c0008000006400200100060094013014c0190000005000000400140090000002000000c000400f0028001000400000040000048005003000a00080010004004000000300280020000002000801f003400400d00140004020000c0150004001006400900040050080000000c006000001c0020000000000100000010024008000000e012401700000070068008000000b002c0040058000002400100000010004001000400c0000002000000c00040020004017000000400c0000000000000000050014000000c002002000400240220008000006400100780010030000001401f0054000002c028009c013000000800c400a003c00a000800500180000018001002801900200010074035001402d00040000000008000000500e00000024000004c006001000d0008000011000b0004000000c0050080000000800500a0008001c014005800100080210010007002800500000000000005008c00c000c0010000008001c009002c0020000008000800b00040000020000000c004008c00b002c0000018009000800e0004006000c0300010001000c00e000c00d00e00000004008000c000000c0000014002000400000000000004000000400c0024007002c0000008012002000000080090008002006800d004800100ec000000001200000000030001000c003004c0040008003000400800080070020008001000d00040210034000000001a00180010020000002000000780020000000016803200080040024001000002200140030018001000000100ac00e0004019000000c00080070000007000800000700020088005000c00500380160000008000c02f0000004000c00300000000028000001401e009003d0000002000400a0000024001c0130008001000401d00040000000005000000000180340028001004c00b0090005000400200080880070003001001000bc036002c04400080080024005009c001000000000000030004004000002100040000034004007c00a00000070004035001005800580020004000000400500000330010009008c004000c0090010002000001b007000f001c0000024014000000a00000000000009010800b0008008000000000040000008023002000600ac0100048004002c00d0004000009c00900000030008003001400300100030000007000c003000000000000020014007000403a0018004002c021000c000001000a000000700100030058006000000000080000000004000400b0008001002800100000040024008004400100400010000002007800c000400c0000004001000300200090000002000c003006400c000c012000000000000000038006004c000001c00400400000010011000000e001400700300000004013000c
  | 54 => 0x4025000c00300000250000007000000a0000020000000200080050000002000c000000401d0038002000c0020004002004c0000018017000000e0028000002c0010024001000000100180050024015001c027001c0050014012000000600580090038001001800c00000070004000000800200180000000008003c002007c00c0040000000000200100030000004001000000040000008004001800d000c000000c0070024002005c010005c00400140040008000001000100000020004000001c007003c002005000600400050008006002c0390034014000001e000001d00080060000000000002b0008000005c007001400200b4001001400301400090018003000401700040010004043001000d0000000000000f018c005000c0010018008001c00100ec000009c000004c02c0020001002401e001c03400140010020008000802f0008000001c0070000000000800400100000120003000800600d8003008c0020034025003c007006801c00dc000000000b0020009001c0000000003006800100000030000010000001b0008004001c01a002805f0070000000000c0054044001400c0000007001c0020014004000000300000120008004000c001005c000000000b00100030074000002400100ec006001c002004400000600000000015000801700340030000005004c004000000c000c00000280370000008000c02b0050003005000a004400600100010030000000000000040080000007000400400ac003000c000000c006001401b004000600080020014000003400000000010000001000800c0000002000c001000400000180000028007008000b00080000004003000000000880090060018002c01c0000000000000b00000070024002003000b001000c0020002007c00200140190088004002001b0020008002000000540070000005000400300040090000005000400900040030050006004c000001400700040000000015001800101f0001001c003001c00200100200010027002000e000800400180060014003008800f0010000000800b000001700b000600a4002009c000001c007000c0000110004001c011000000200100030040008001400100200000018000001001b0008007000c00400bc00b001000300140030004001000801100200000000002005800000340150080000000400a0060002000000600380050024022000c0000018010000000f002400100100020000038000c000004c000008800600100000004001000000b0000013000000b008401b000400c002c003008001f006c005013c019001000100100020000014001c000000800e0004001004000900000080008001016c0040024004000800e000400200c0002000802b00100000024002000c0040004016004800000140010020015002000b0084004
  | 55 => 0x10000000000c0020000000000c004009c008001400800180000008000000000a004400e000c000000800e002400000100080050002000003400180000008000005c00100b000101bc0290004000007c000001400100840100008000010400200280160010006001400400040000024008000c0040004007001400b002800e0018016000c000000400000600070004000000400a000400200300040040008003000c004400600000010178001000002a002400a0000010001c01b000c002000c0040004012000000000000010030000002801200000000008005001000a0004010001401d00080030000006000800c000000000080010120013001401d0004030002400000040010008003003800b000400200800040008004008803c0000000001000300740640004000005c000000000300000000058004000800b0078001008c0000008003001400000080030074000006401d0010000000000900c4002002c02e000800000a800100000060008000002c004000c000001c015009001400000020004007003400400000030004012000000a0040017000000200300080000000001c0020040001000000400000000000030000000c0024002001400c0008002000400400780020230002005c01001140000034000002000000000000030005000003c001800900dc0000004006001801300000000010008000800000040020014018000c00a001800700180000008000001400200240050018000002400b003c00200f40080004003000000e00780130124002002c00400080010000001000000400000040000000002800300000000028002003402301040050010000008800100340050028001000800400f000100280070008002000c05300080010020000000c0350004003000000600040050014013008c000001000b011001a00080010000002000000000000010000002004802700000140000012001800000140000000001000800500000060004005001001100d000f000c0140008000001000000000080010005001c000000400b0008000000001c0060004003c006000400500000110000015001c000000400b00080020014009006c000000800100180200004012000400100100020004015003400700d800700140020020000003400400000010000000002800700b0005000400100080050000000008c00b00000020190007000c000000000000200200028008007800100000030018000003800c0008000002800201bc0010034007001400000180020000000001c0010038005000801e000000300040020000002000000400340100008000002801c0008002000400c00100030004005001401a000005c000000f000000c00040030018014000800000180120034027001800e00040070000000000001e000c0090050021001800b000
  | 56 => 0x1c007000c01200200000014024000400a00000000000003001000b000400300180010038007004000300080000010018008c01300000000048000000c0000018017005802500040130020000001800400000000028008000c006000000100400010010004001c000000c0000024003002c0060048005007c017001c0000000012000800a0000000000c004001c00500140010020008000800a00180010020005000800f00000350080011000006e000400200380010064007000800a000c000000800300140000004002009c00b0000000000400b0088008001000d000000000000000000007001000000040020004011000c010000401a0060009000000300b0014002c0000000000000c0000018008000800000140050028000000c00200180090008002000400600600060000002000000100000060028001001c00a000c000000000000ec01c0004020000c0080008000000c00a0000000000c0010000002007c0000010011001000000900160004004000800a000800c00000000014006000000c003000400300010024014003c0020064000000400e0048002000000300000080038013000c01a00080030008013001000b00080000010000000800f0004001002000f00140000168007005801c000400100000050040003000002100000060008007001c00a00040020000000001000b000c0010000003000c000001400100f800e0000006000000000040050000000002000c003c0150000029008000500000030000024006801e002c000003c00100280010048000000800200bc078005800c000801f000400100140340000006000800000a4000002000f000403c000000000000050000007004804500000000000000004401e0028012004c0000018000000000200980160008000000400a0010008000c003001400300000050004003000c020005c0060040023000000a00a0004000800100140070008000001c0000000000006c0000028003000000400cc001000c001000800a001c0060020005001400100000020008000002c02b0064001006800a000000100b4001000c005000400d000800c015000b00000030000018001c00000000160000001000000f00040110014003003000f000c00d000400300240070028000000000100000020014000005c0160004028000c018000000000100390074000000400700440070078017000c0200000002000800c000000000200010000006000803700080010000019000400100600250018025002c004001400000400010064012000002c00000110000002000c00300000010010004000400b0004006001000a000c06900440020008000000000000bc000000000000000080044002000c00000000000004001003000100e00760000000000800500380000024000000c0020030012001800
  | 57 => 0x2003400101c000b008c00000200070020002000000c0004003000000700280050030003008803c00d001d000c013000800c00200080024002000c001007c00600a800000140040000002000c00e0014001000800600b40190198010000800000000040054000000c00000080040008009000401800500150004005000c00e0020000000400000380000004002000400000000000024002003000b0018019000000a0108009002c01000800070050000002000000680000090005002400200280010008015002c00d00000010008003000c0160090016002401a0084003000c0030080009003c000000000200140020034001001c0160020014003c011000c0430000002001400700c40120038005003800900080090000000002c02300040120000002000800b0020005001800700040030000006007c0000018002000003a00200110004000000800500f000000100000104017000800a0014000000000100ac00400040050010004001c000000400000140060030000001801a000000000b4006005c02f000400900000010074001004c000000c00400000070070001000403c012c008000c001005c00000000030014018001403c001c00a0000049000001a000000e00040080000004006800800000020000025002002b0038004000801400040000010000001c005000800c008c00100040030168000005401000280000044000002000900440130044019000000200140090004004000c00c00040050038000000c00f00640070030007003c0030104007004400700dc008000000f0000011000401b001000000400020004000005000700000510008009002801f00140000000008003c00200000110008000000400200ac0310000004000801900000000018000000400e000001e000400f002c000001401d00080050000000000001e0000001006800100000000000000000c008000c000000002b0024001000800100000070000016000c000001c01f0004000009000200180010004004000800a000c002000000a00000010000007000401400200330040012000800c000001200600060084008000800500f8007002000800040140020010001c00400040010004006000c000000402101f800000000090064001002800400280090000006000000400880000030011000400f0090000000002e00d80040054005009c000000802c0128017000001b00080040018000002c0000024000000c010000c00e0010000002c0010000020002802e0000001002c03800000010024006003c0010014004000c0080008000008c00100100010000037000000000000000000005001400400dc01f003c0000024003003c00f000403f000402700200060054000000000b003403b0008000000000700140010000000001000100bc093000800d000c00c00
  | 58 => 0x1300040000001008c00600040040008001006400000000020008002000400a001400a0000000000400600440090014002001c0090090044003800d0000001005c0160008006003402c000c0020004006000000c0000024000c004000000100280290034007000401100c80000000009000800c00040030008000000c0000058003000802a00c00080000004004c002000002100b800b001c00000080210010000001c000000c00d002c021001000d00000200000001005400100000000014002001c0220068000000000e00c8009000c00b002c002000000f014001e00080090014001002400300000030000002000c000001800000a00000034021003000e0020000002c03f006800101b0005000c002000002f0008001001400f000400f0000000004c0070160000004c0000000001002c0020020017000000b0000018000001c0058014000002000200170014000000c001000c01300000000000000002400500180000000004003c01a002400900e400a000c0010030001000c00500440000024000000000400080000078007000000c006c006000000000400000004001002400600140010000008000000100000000034004000c007000001900140050028017002400000480060000013007c00b009c0030008000002000e00440090000004000000a000800d000000f001800d00140010018000003c003000802300040060000000000c0180008000000000000340170000000001400200000010000002000c008000000600100010010000003002e000401000040020000000000c00b0004027001c002000c0030170000012c00e0000000001c000000000a00200180008003002000000200060000015000c0000078047000c01c0008001000800000080300000000001c0070000018001400000000020004001001400b00380000020002002c00000400020008002000000000040140000008000c00000000150028003000c013000c0100050001006800c0000001002c018000400100940020040012001001200240020010009002800f00a4031001c0200014006000800300080310044001000c0000000004005c0060010000001000300980000070017006c00b000004800c000b00040120180004002400000040070018004000000100a4000000400600100000000012009c002000000b003c045001c000002000a0000001001400a0034001002000c000000800300000000001001000100040000008008002001700000090000012000c0010004038000000100440150004002000000000300030010000000000000140010008002002c010003c0060020000002000c0008007000c001005c01c004c0020018003003c00500a000900040020004006001000a001c000001404f0010000000800900240010014003001400000100a600000
  | 59 => 0x43f9097b50c5852c0e9e9cc000000003d122df40000000397458e020784264e08306c2bd10f6403e62992eb899422ba0000e850d160000000031c17a932b22e08e97070929369a48b511db34fea000151e00c03e5482200000000495000000001ab100005e4510916f00a0e0c8c000096e29282f3002e157f00005aa4f3a0000000028dc000276b3800000077201d700f00cb80001928383612dcbcc05b922c48b1400023aa0000a220000172725aa000000000000bf014480000000000060a13559660163e00000001ac700001cb107512e52dca00006b900fd4d2a8e8c010099c000000000001a4a11b08194e70000041841d106b61c880b0c2850f0b000016ba30281fd100617a00000167a98726325610469037b48300000e8ea45c000004700000c891d982ff508393aa0aee4bf83d7817854a03f5d1a4a06d51e61fa4ba8995f022a4b4048f1c3052ea82e085700000158053c4a081b749b2a73800000004b2a0dd49a9a4fa179a34b897724780874af9136c97d50b68001c2889aba4fa6ae6cb07a016261c1a7c17402f02788000125fa4c0350c8afca3d229f1b202c5c820a11051f659bd40b19433bfa303c47a80361ec89514dca079f0dee7a98000057354dc9df537188b7081a0000402922649a499a000001ed00000000b48800026182b6c00002b149fc00003bb000015900001445a1761ee20d7009c062c393a00000002b8135045bd0f5b021423249ea80001c5c3bca794043500000000000000001f33b1659214a718b11b7e6b5485f8000044a00014e812c25530acc0c480901557aa9c0b010b3d25627d2d1ea15c80000000153d00000d247f785af18841ebc3c880000000113c1b78c9200002e321bd8b7c9508430eb05127391154662589c62d0cfb30fa3c149a521a02c8e64bce5f000000007b610c4a1984a0c0000f5d830353f4000078b17e10ac8000000000004b3c6d7161184a71db226147a30d8f00e277b440208a000209d84000143400000000ce1195500009eacd128000000000002001df62ada9bc10da92d9351652b5011a362269e88cc2be0dd414524d7c00017290bac049927da6a6000000003b48c76170c000000027734a7aa7303561b6e112ea6593e81fff0f6a8cc90ca951e0252338c2421172319a6d292191b7c36bc7334c788000133a7b410aa207045fe5f302b087f041246ab8e71240414b0146813e8e6753d8a83800010df46080000001000c02b005400200540030000004005c003000002e007400d0014010000c00100180050000002000002f000400b001c008000000a0000012000c000000c00c0000001006400b000000000040100034009002400d000800b0140048006400a00ac000003c01a0000000000c00100d4002000000100880050000002000000000180000028007002001000640000
  | 60 => 0x6cb11800034b6000155c073500003b2d2c68b272ca2000144f8fba34082ef14449ebf0000943000000002d4e80b14db04991f9c9ffd266ab164122792c0be1bae4dc2519010d899b2c54515d4c50e99312839840001a90535873d46b5a169126a67481a523e301da66ccd7007c146f4199520e05a116a68544000125d1d380000f9c95670dd240ecee9056a1ec633c089d0ba00b20334c2489aa41a4cab3ce9b830145de8924292a82936ee5ce01882ad42de447dd1242b1113ce12942298442325a1360916801e430c00000cc1929030a85c8f742c1f26122b7c32f8000469a29082e62a673e8c0000000053e0488301027188a500d829bce101f470f7e000158593bf1bb632b84a9a114115e86acf7baa0f01e0ac815d90b030000175075997ca18860001071205347f495c4f1408b9275e0bf5493011b444263f93408000535471614d0854e00000fa91790000336466bc10503740000630855da53a1d0618483ac9b38000000006cd94244722160859807f842da6190ee880003a400000b6903dd28cc3d246d32bca52b08bf40001099000082244c500292b1c4ccd61babc31d3e98340001951415c1b1cff42621000006509bf2c3f3af60000728204a000075f1232279744b813f0dd117d4563a7be4b50001f4fc4304ce65000000003b0c000054417147a7c00000000000aed50d19de6088e224853800002bde00000000db311a88a215d18e9b57569f5000004f548a40c6109c8fa504726d391e804673cbe842830c29e81c30000004f8f9a03ce1b75095800018a4000137e91a4272626e8b72102e2f7800009e78320278248b00000bc358902c10ea90000283c603c0002111341400000002235000095e4f8592c802c02cdc37a179c269a0000a6884711b7a3678deb1e7f010089dc082891f1ff648a5064921d405c3cccf6480004c541a713d09a7645d84aed3098959099c3ec48ce1f61535c56c931da2dc465660e80001eb54a8e872c80c1fa643385d54440238800000000000000055f600001a317b5000008b83528b1321a2000041c9aa0046c00001b8960732fc4af8c87aad7000029489d802900a861b6d60094fb114208ecf439f5b043a2c30e4480001b48202074612e0193c9cb049b0000140c847c3dc18063fbe42750e98d520bce00010be06680b5e5b80813a05a00007c1d2f925504afc953439d91280000afe8b3503c4556819789a1845f06e63eac00021d9000010d948f1e961b56789d3a9a1f057d000009d0800000001f604ee8b7138f46a48f430a5503ca000001a0c8407a084551af1f1031c200013f495a8033a9120aeb8ad029b000006900000090468e800024de1e3e0000000000000009fb453f80002f3e540062c8e0c383897885ffa5e3106050050e4027029d897ccf099e3200000000000000035be0000dd5843
  | 61 => 0xaf0e62074cfaa00000000796c00000000000330c3c58920000000000000eef000018c0b611d582d0a00015e92bbf0a9265c49d20b094c569df04220ca53610000000005403b4e3b50f6890d8098ca1c400028f12d8c537c979288d07ee63dc41698bd00002965372800052e683101cf1697488c326d1b9962f0000000000000001a383d346fb80003f30468c6af012b26e6015412780681d0e1dc003a18ff256038380f306462fb834c00002be232ea8ad52da2ba937544b015fe00000000000108c966200004b9c9d380000000000110e28b008448a94c3b0000064e433d62905003c3600006770000388c611c566993952ee6c592cc8c870a525e846ada9c60f120d385aa03ef00004b30000000003d000005f99a432efa76503cb1ae2290600008fb07c8000000014ba0000123442150c991f02956abe016581ae1eca14583362c44015413e06a6283a3a480034000159f4302000039227db027e3e08f658000293477a8419a68600000e94ab12c0a1ace93c52750fe34ae0301c8240ef408f240e9441991d485a58e955017d1542214106c4985b1dee7c953b19613326e7214e501afd0a309768d33a113383eab7150d0b870bfa66f09b5844c4fe63b18899800031263ad00000b450fd45f913b70c74547400008051e3a554a00005c20000000024e060a09a116641de10e32860045e7608dd386732eee00013521bdf317e000000000002ff03ab8324164642ae221c585800000008a004248766000014083970edc0e22198c3bf0f5f508600000000c2e14ba3a8138d15265260af1c2c20fbd4ede0000ad8800007ac72a13b10c11000000000000d3153a621945159897143a3d60a549dba3c5a5f6d33b22f9000059ccfd899a82ed200245b6162940a851a4fe616eb302aabf4d4e99020b5a1db53259d6741b800000001c18000024a400000001bd06f08101223126c843d0cc426be56fa0000410a23d4ae84499480988b00009b250050991189a22c1462817f3ac66f481ee1fac014282d4d9492250de423e0f1f00181e2e9a78dcb8b7918c42994b8121dd415e23ec85609fe000057793a4163252e2233000010a3000073b05831b6300004950000030812161ffc8900000000045b47a218f00000000000000003d7400000000000571aa0f42460000213000013fe21e857d45d7c27700004e725f5ceb99b1e49c0131c09b106b0000361c8b0800000009ef8a28174800000000093800018980000243a6f753328bd800022852e54879c000000026820000a0f80002e2600000000d4e0d1e0260da29d354fce5d800002b6809e600014bb1a0c240a00008a4835a0000506438ea9b200001fc48c027c915c45f00f372ae6318c04dcacd9db00d7203ac39b059818a08ecc4a712de1fb492f45dbaaf000004bac000000000001e84e7e800000004f
  | 62 => 0xe2d58a279e4c4889a94742a0634986a154e90a8528baa3f8f7c1cfc0bbe58c04b5a2b84fb22a802372c4e00004f1d22c975337ee5c6c63ea9360ab2917400023232e781a5152f1aa20000375c9fd81ce291e6db112f16c500000000cdc034424c238d091c093c3c5843ed5dc17bd477c53a412ba1182dec4c151ac07e329840e64be491594b900ccc0000000356a7de000013b94b128780000024946b6047c91ba99e369e94248ed0c051c1e9dfd2758117394e0444ba526b74b9e25f90a588c6309e6814d3c1b3519883c113c5207601d0a604ccf09770a4214251181380206c1a354bca88c127a79c80000000000081c851e9f8600000000d4618fb00000000d508000000000004e3ab4c18ca13583e112081df800010d3a02b13ec0e7c4a388f64f506be07dda5fe3a7c3c242ff20dd00160a045e5113254fa5580c1e01892b18b11817fa7111f424785304ab371c2e7d5cdf411d52d3a9960ab29297294230e07109b91265010144a29a8a448c81f5395958724d65729387800021de761113c9e754d60486c21403f603341da01828541271815b55ae0000297c9c646da80001b821258baa1a7345922ecc8cb936c47be3e640a100000000a8485ce0000153086440000ffd1ff053250b80c9c13f8000140f2b9219e60abc07f85701a502fa104b041234a46214ae69c993f36029c0b208de0b128c311a32986371c3038cb6879223522a38c010d290a6e8cfc5400a30000000010c0139b000034d8b2a00000000000018d001c227c4c180000af30000398155d8be7577639e0813232255ba7c640061f3f3c3e45b0f5e12671bd638ad2b78fee2a8a488515b0fa700000324fe1800000006e053511757449e0cc00638dc200008748d3aaa7e044242e512ea26844c25558ed18000503655a809117ed171a22a80000d78225241594970dc03b2600016128ccd067033542c68ce90fa8ace878c1c4556765eb4000111c3b4c7dad38a153a105e4d2d115000000009184954800045f010a94aa87a92a684c10fe291d20000908909a2b9c1c3460b8f931b56025459983a71512083e66485f48cdf000015f910119a60dbe0000000038f00000c84040800020fa0000000000052746e94587812119fa8b690e380000ade00013b9000000f44e954bfa9a53d5e60884b0111d0000291400012e84a8600004d72b1f1ea46650a63169f3ba09bac0aea6ff0148000030f805b1fb042a800022e619c0a170d5b22a355908b9068385dd00003c1cd2d051b000030bc0001bbd08d45538cf093a8000069ac875808d27ec7d4c63b9fb64eac95d8db300001e2826a039a000043101f30a8b863d558a35202700224149a3e3805d2b412d306fd00290c1747d63de45d58e8e4a228eb501505ff381e099400010c552ac7fdd1051bf24e620f146db84d24fb00000e6200
  | 63 => 0x4a11c8c8e89265128b0eb695501192ae406a40fc13cf961f3ec816a4000000036806dd8aa911061a701344b1a846b4bb272d0635a6f235ea66acc4082bf161c96907260f8c21c20000000112f0000000111b98740000336d212a9190000000000000004e7e00011438e3a3d14607cb508000000082355789b8638d49ca4000099e0c10088c9ec80000ab0000026100002f06153530a0ff1385a609c7d79249000068754a394cd000000000002898144a605859c955f20b4000000020c0000012f49f92962000000015ed998233da1decf1fa6ec1f2aa85500c8ce734ca6fecfdeab6b0b82987cbe90da92012379120b82e206ae98fd443274d31f0728ce84223c53e0682d54396124dc859089c505c8298a27653d1a9063e820000fd784b6091c19a954c935a33f838080ee1e3942b467515748b931aae6f6065d11363fe42c844c7283f3d3a47c8cbc2040455088b829aa0db53228534708092835e813e829d000000001c6d31000004f9401647e08000548446acc90102339621184f8e042518ae35c4773a80144363d6926982b32f4e41f000019d700004f511d297b7191aab6113c0ebd32f855c147e10023a5658140729eb4157c46c8b3926ca2e8cb0b8ff615f256807f8d2b28a232630099ca26a663404890f0000270c10f01a14b1405b1355eae24d9621ef000000006f11d7631ce5e011ae1c814c8435080002937282a0000000000002cc2224de41ec013e227500000000000012280000a0903425dc408400000f6c827047500005182a14558b9f2e559c0001327800049623a100f5906457d600003f6928346ce9b18f66a40739aa000000028c254a22040c7a195d28e445f4000244e49540000c0180460000a8814eb800008e800010291a1255d484311710b5900004890181042b02e06f3800027c64a644a54a2aa00208660000345816307dc0001200a95b2e9c0000abc8000046035800000000546c0000d36000049fa27d00000a16000057440002b2200009a30000292b1d7248e40d180001832a9ec000136e06b64f90000000041ae964107b0000000001f0eb810d43d1a000145f217b03445a1000013c0000050e879723ec331889495f9a95d0f803cb556194130d625ca03f5905c42b870f00001a29053032d538915c00000514c4611bcd01a200004928000232600010cd9ee000000ba9079027c4ed4a3789cf0bbe50b67a10fd027c7178eab88f27818c00003d88ab081ee3a740000c4d8811390e80e8e14055c0996a2dd020a7a515c600014938a0200009e400001b85389c00002e880000000432d41c1bfa00008824f318b0a0000557800009e100007eed3a49fc13f5c3634000000001227884000079b030c00003408e7000000000a7c9d5c4c68a7c43e7908953cc0af146f8fec24c817c44f7a64120b256b0000000005d22
  | 64 => 0xe0047aa1300fee00001056a0d0000007e4eb05a91108abb611c80d9561a800527621955554133a4bdc9e1878880004a369f780000db01bda292000025c6525294b493922cf3fdc40b4fd6a04f2df075402e5013400000ce80001ac51cd24780ed09d18428c2fe14688000151044fc40380002d4c2888817a1431bfe70e85b12c2952c681b0a5186b84ba6240838d168a3f3c8a54e480dbc0a029341072088c23eaaf3541097664e1c5340653225604c6540541692850ef83b0076098e5583a274910c0aeb2698674d302159825a41ec4414267d0b062840278116b408c2ca0577852329de833c6210e29297492b424e0d5627da11f4f7e1af006c4a2281dc0ad51ce64d14c868fbc2b061c3c63fa84f41fe5c947eb0a7c4cf09f448fca6234c06180c4ae8e76331c00001a29cf41aaa6a1c7900e9a13980bb42648114539e6838f459c74000007a47ef28a35462a5a0a7f860a2ee045c4c201286132a32208f415bd07248df44dda8535688ac64eec80530d226d843621cd605a41674c52ab912a220c9400027450b2e0ac80001c732340481118d8ad2585006bd59a27ef047c5f34f1b8c3b1f26373cd310c081a7408395a884652106328412518664f96792818580000cfca328c7211664e943d0c44b1057341a9954b0e05f431129d487bf9a09178283b052f8877217c00012492b9705040000db591742aaa000046026bb54100000c1000000600490c4f588a20e6400000000000000066c10b318524c0e72285b800001b2a511c4d38000336e0000c7b000000000000000000058b00000c2a8d8a426a00009c407600000943800000000000619548aaaf5219aa67104603b100002768000257f4c383ed547c00000000199ca998000542c32b550629700e0e7a5d29095e22e748c0117da792145a7b64aa5821941c000009cb1ff30000000000004da483c88a55eb257348f8a7cceb29c0c3bd00000271000010041c0460d1c051ad23a913bb069a0dfa36a147201e0251c89f52c910522268714018daab11a7e616523b0c70451218e48b38c8a13dc9bd0fc786e841dc1aad516aa2e0f0e1b409bf80001a6630612fb9a99523ea7c89de8f73582e85310a42223148290f80002b242e72000000017f44604a06140b8444522e2a4c543a7915862000081f000029100000ca72c3d3d503a2400003f2245c0a984fc80000000000000020a2469e000016800001ab20000fba8000000000010fe0e320000521c000290c0000000149a000047fa40781912b2a3fac20042089a711c5009712c00554297e83e009e1f0919641d0860f080b267255089fc1b650b9c04f84518000017880c400000000000640c0000000494888b00001c722cc20000000002a00001d600002a4f000091b116180000ad600012ac93821d9c789000026a826b62ae4293a
  | 65 => 0xa64802ee4e640000000000087d8d4d1cea36ae5e94a2593a606a862a00000c7917e4000000026ad000000000002c2d2cbc1a614b5a2af000006a4db8998524be04593771a5c1946a8780f814f028da1c00e5b2251000000007e684fd13fa61408aa8a6249406e540fe9bca4e06652cbee933700003d581ec23163698000010f91e6056e9a64000155820b0400513580001b546a508e49bba098890a032c000056b4388cd2b00003fc47634a9c901058164b8c2749ec2422e000000011ba04f4684cb3b21f50fa23c4c563249909fe8dfce219cc518b89b5c56e29954236adb0dad252c339c820c212227a273e14c13c126910d640001513233608c00000ba290d9467c0308b060b63000062a80001d7419180001392000010de18746588000000005040002153000026c91ce2bfd39b46a4caf493fe29da00005ad126245e267207b40cf749c63b088fea8bd538eac3936ea0ef10d82220cb7927e528a2a5c0000b9600000000b558f8b2f603d20000192b432026c42df11b11d748cb040c20bb525ea5490008f3a2ef8ae689878b5b3804513ccc306510c52a2d1318278f512226e000016d425883308ed5995802208458dce284d0000013922b05132bda3f882d40000000000005e10cec47709651136809e3e58123c2c38406105881543bd166c0ee411f941796243eac0db8fc5aa6a4be81ec89272a94437498b0b7d881a1cd6aa3d48100003b986c7000000000000000000012d73c3a51f88a78ad936746344000000017d82c0060494992a1c2ff8458a3701ae818ec00006221f9e43f158f00003dea410069213170870384ce378bac00008ec1086a61b26c00000000280d270c72dd2c98563460e25f45f8135732c0237d33d80000b5480f55e89219118611f07749d9c0740ad5839f101700006f303a8a46b08344818eeda15500000000a1ca7cf56ca758081901ab17c61fb8abe880f3a1240fcd26a86d12b876f853b95d441f247a4bf2a50f00006ec4a792bf00da4176800000000b6e0ed800000000d9e000000016b3414a000035a8957000073312d8aa962edc60785679189404c021c31b178f08a469fc0bc80000000adb48f88fe501d25a414a182a30000a1980002a7c0f8826954b68000000000010f28149211408dc3b604754d8e000007d231948aa7b4934d000029a49ce8e6406594c100b304ad22d22d800069192a82717004208f41222b296267fc7f301db2d5a718400017fb56e23c9000008ab2f7c000000024580f5a56709928a0c424e6c3c94c81f917769d081e88d0c33225d481521a0711027bb43cbabbe5288aee8aa094b70d0c5b042270b194380958944e17b228e82924103825e3ee267744a8943e40e86d64d902c07527c00000000000250e069486b0000000028c80001442143000014e5800008940000a5e00000000
  | 66 => 0x2bd83caa76c0a94347931420b347e080a550c18b040d037bc29125780d8229100159d570000208931d00004cc000002738af9000077b014e865a280c7b14e5f8aab053678555a42b1a535064155708c4555040381383a02f1fa47aacd9e8000054a00000002042520637e86881e2a00003c0863f0eeb0fb459a0e18a4c21e5ea32c21a8ad6310e964459f13030000ae094088aaf149c555073e8d91000080b445d800000000000ddf800049f80000f0080005170a594bb680001c8838186ae83db3ebca8c8e7396b9247452e02a901952aecb10d5d8299d1cf4401cebf81fb255a000121c859900000000e460ba32ee60000000241d0fc219b80000dc944a82ed00001eb13edc4d3857f24700a84601d2618000000092447c000000000000081e912d0c0a3274d2c1402049607bc52b0000000000000001c4c369600011672c212cb82a8cacd298f229690f47ec821c1a8686902c8838a031c0000baea0f400000000e8d80000a541e78d1fa137340682c4818204c006a9fdd09f88c51c4093b400024f937c200000001f7700003904b1880001d4a5bf01d0841500006d34e6815b51b5a55280002ae843aa265803b00000000000000000003dd6000046e00004d3a00007930000000065105a906c30e8c8ea4b2e800030d688782f8115343d25878ae620375436a010807908b016870d46672175066419bc0a305f615487c78f50a0a9286290e029fa5be336aa8f8a560e521b8856950909f3616d6471c586a44d07264ae0b29219d43dc7ca552315c43788a8fc7128e3b000098452302a4d5758810c35388bd37d24dbc00026ce00000000afe0815353e0001042800026588804fb91d4a46ae8e39606951c35003b40ab7137939a849a81079a1c549214656130e3d16e811591a99e11236a84b52be1ee72a80158855406993fc0653425d21f34dbe348463a98fa31a0947cc84ac5500c42d19047942a1d5e3328a19a9be2d90080d0389ff145ba871424829e9282c001157f952f16fc1a88c5a22b757bc4254a1a9c2f4832826837086433e88532c169a9f8411c12181c0101d37c06a8ca9523333bc00bec90494a514ce0e601941a910000ab652ec0ae9000091c80cc9f59486220a8e4a1a2304c28254000000052ce79e5566195b49080000b8a8000014c7dd0c5380001ecc87accdb0c261ce2000151d8000198c80e48971e3000000000470088a11d2000114f000051c40000000131e000084f0dba038400002b6000002cd18ce3e181db98dd2bec960848b000031be867c85d950f000018b8a60800027ae00000bd00000000000000019f000002b2c3ef8f9249103978e3e106000000000a2c123d51e896149ac1b0112c27660b4f0c1537f83fc09cc17a833e42834e4da03e00007b68c181293383a763d10712462786453800025b5000013c834a
  | 67 => 0xaa32109724c74a540640337a40a0ff3960842d45a386ef82c62c56043099a93870272a54c1f5944a35ac631c05e886b059c6f047088ccc572052b923f11e43c14860877100001a080000000000054c067593400000338c74500002bd500009830fe580001a26000019f1fb003e804a0df6927306323da548a1cf7138623215e494c0534c0000000219432dc45bc77905680000a74537e2a9a406c02fc000000000002d1cae491bd2bb843dc0001cfe0f08000043000000000913c0002126389a078d14080d43e660000ce8a4e8257800006f8a81d1e7600008ef20ac286e4468f1184d306aa00000c4197b520000001430c341d103b10000238b3fde5df8000000000000000000000041ca4c2d53f82e33d543374cf10ebe36c061dc8ed8a5e2ba664b94859e2f2cfe13bc0e8238632ac4b3c23f948907b2017400000000990000021e84231b380000071a55c461c60100ff215837ca22108232bb43216999087181e400a20e200000000177260e4389102c48821a5d20f800004400c4d09f000034e89fe4a9693083e3a2398df5049f3f489c60db506fb4f0e9bbc5eb272e3bae19a4bf70000324c39d12aa9c1600005674000154301bc4881492976b26ca3d1ca46a9ed0b1605391b293d2499031a800010134622a7711979d212be21b4512c046913fe39a03cc80ef03a2257ca5a9941231c5b70cc193bb15ba000114180003c9a9d685d1006f474cacf8abe0cf22816324c0000517549c98400e482be50248b08675081e583284204f48b34135263714c69732356678f527c00001b724fc400026c342c692a43750b6f3a68a4889a322ed53ea00011b200004b9800002da800033e819b4a1580003ede77c00000000244e64c80001a0822d267ccbcc9e0c0a0c3a8800019ea0000a1ec8720fc30000a1ac2581ce606240000204000040a2000126f878800004a484c82b2f00005628a28a2a20dac74580000000300073cd35b0f8524b0000000001b60bae46ec1ca800000009a34a24abbd451a5b3d3e4172f4a6038492049124409a98b83a986b430e21da8966a4690e387808cee23f1301c8801458a64a2b548890efe196b0d980f8911c11770dc462acd54a2c8084e65cc000242146de94cd35c800000000000af5a63d17368f6c00028c300000000df327ac21520000000162017c05abc00000002f3456fc00005c70000b080b000da03e263afc000168124787b211b70b1115629e00b958b2f42402ceca7eaada36284d40e6012d1106e94509e9949f55608095536a044113a68c093c224446be2039043138f46d85a4895628d04d66a2fd324a0ab298e08154160e2c520eb040ec010b14bbc26cd009a1924c166cc544798131a1a5e3499f1cef2a9e5bdcec398122fd07a05292817156b60a9c51a1c8b4da671a08a42ab700001a10f582546000
  | 68 => 0xdc6a35342800010122a340001d6d565a87288ec817533b60000836279a00000000000000000006878000244a37ea0ef80c78b5753948708af32a5f0000571450f8e2e4e1600006bd0e2a285e000004d038714e2439828e0ede0534727934b0fe409ee3dec2bc2b53183a3eb9434818a3e0455c8096800018f496314ec08750000a6c4f302bc142ac17d42ae80001f46393c70c937c256e31500002baf0b7869b4000289d0b24a1f49e8078103265665344800049b86bac000287600001b500000410025ca200ec8081c0f5000000000102000000012e7003000003c711b480002e6c0000f05977b00005c3118f0000000010dc1bf1f1211b2474084da8e100003c8468700003a8c85c40000f53150200011751d6616283fe5434182c00000000c83a9e057fc62e87ff960b476859595ab960931a465302de9e0e42de80403159d8a4a6c3008b0ea06648167cdd3748e7f0f9c9708ed123af00002e90b6d93a0467202d4c108f0e1ade00002661fe900000000a1697353cb45dbd1b69fa856503a34000000000000000000211c145496e91e5ab4200008c5c3f216e10fa6433800005b043a8a104efa00170000646000018540000498cfec8000000454952a8aa2703a8000033a06d84182000153180003922379c00023cd0cee000111b07570dcaafc8fae287731fa7144b9ba5cd2f708b280000b943d28000139a9ff60b568010e6300000000a804b8e80004c8e0000f5c80003b92924c000000035a80000000039c55f2000125d00000d7a42a0e470d4118549a940000000000000000000000000000000002850033600010e484a256964f591250d3d0000a258412abad374c96bc842184b4bd6000021787a40000076962987fe1fc00000f980a04404e8a70523037a00007e002c61ffb12389e2000003b4000051ac0000db23b9c8638377132e000000000000bd21706000128ba6881bf8a8f457d866623680ebc6ef2516371049c135e07b4115c983cad49e0507825b288071199075479181ca0000000086f8a0c13ab0388a4cc37e03f135c675e029c080a1c48419cc8b26013f4a3adc77b074920c2693d2d017750b88439c4f29afe2ee8259c7b0847a50b411bcd7f874a2a3259110bc180b0ec206b0e2992744092ada43858a502e2e86fc6b9a71511ac0b449868d4d460279f804200003ecc091d17b948b52120001004026629e29ab0f789d45330871dcc1491df27ee67b098d024528acac1ca07898929140110423abdc0000000000019d91c0e94c51fb8fc7042c7565145982d4f6a0bf800000003e2c18e80002b9800000000dc392e4123096f55d2095800007c5400000004a460000eaa01c7140a9f30cbf88e533140ff483ba778075219e43d81ea20afe089c91aa7e00eca218cd4418c941da29707db841e45402d551de0da54a1467dd31
  | 69 => 0xc893363bb8abdc00000001a105328fcd2aaa3104a7acdcb0a6c573a7c100e51c552e448868719a3784fbe1f9401c258e08d838252d6a1af50e60d9834425cb30469dc406e1c14042e054cf7d23245450334961c91214e7c2e9ca8d0b8e47c288193851c7d0dda1eb894f03e71e146a5c42e8f6038ae6eb15ee9ee94a9631200721c0d23541cbd5579a2250884cfc65e2a0904507cc89b8119d4308231c4ad85f237de0000de31327476c1268024034700000000f591213000077e55af9e612ab400001b4010a399c52f4adc9710178c78b8b43131c47800000f208645000096880b280001cb0273439318c523349cec52d9119359a29ec04e92511df684bc00000002ab27094a3a8000000000000001dca0000000000011562d78000011d1b82187800000002220000000000002b640000000000011220000000000000003ef46ea03a3a9e525684ce0c0490b712c84f2904b850f238c0000d19a14000000d6090ba6f902de31608d780003134134030d830946ee42845d70abf5006a1e013ba7c44ebca0a0a8d9b323c6265c042b8000000000012fa976257e26b0cf6a14a435ae00009520c28097c48f913282871a323ad8e7b00be3ed00000000000052b21e1464c149600008d1c0002b8b29ee0c98b2528a53c56af9c377949d00005070083800000000000d61000000005e5c0000000000000002f600002a5c00006b688cf00007d291f7197436b06d0c9ef800000001ac0aba15370000101c00015e14a501ee8b9a2b8e4fe4223808e945f2fea00000f90000396681cc29b1d0211968ba5302885a2d260c5000007a2308ca64051aa10944c4afe53f8a2d445ac0730881a6a91528a95cf1a85cf39f265c876297d000001edc1a58d964d64174ca1d81d22d763cc91ca018d36726c9900880fc1cc83b2831f9f003dde5298ad0907148ae8b040000b5101ce8d01222100b04d832e493796ae38d22e3073112e6488e8164d5285eb06ec062c0c38f9730de70a500d852847f82dd4f3784682e6266e54ea0000457a210cc8a17df019011448e19c1355e4a3bc0dc1f9724cc77a530e9e33000009c8fa4ab02267633f961e07e233ce3b8cb6c991721feaa384f183482b766e742720bcb22943da907894620288000073a8d8334be29d00000aa64d161d5806c0378360e31115328a333ba61818f561cdb4eae838c011a3813944711cb021bfd360a3e74a8b1b8a472a1ef878a90c005d604f46a217b10baa38706eca3e409bc64d8cfa84ae48cc000038fa8ae348ea580c4e2726540a1e306f70dbe05c8397c19b1edb0000a3b4c9a2b3c4f780dfc44c81324bdea7fce581e8c012851b93e71ac8346a74e45d083de016047001090cdc12760a551f992030000a9900000dd0111608c4adb96790efa30a49b928fd4ef40000dcf836f3c7035140d404af1d
  | 70 => 0x8e580001d3f00480be49a4800038dc8ac924500002f1024643908e9114d21cccc5a93f31ea8a3b83d5929b45724c443c98be13472127541828e0048257a048891543f1a12a08c31cb91c2848a0bbd29a31c7e9ebcfea9ae94714ae9d00a136903480e741b1886e1260000155394c42f7427b53e29e19471e0000000220530ce32a800013b425b44e50000000045e800005699667000000005a117004bb603ec000159500005c48000218c01405c3ccab97fa000014b8b6c1d6e00000001619a90a2da208a48461b6454f26a551e30eab391e8cb53aa07f2580003dca4e176c3bfc9109626068c2b8e157ca26222602a4a5303129baf129419ec93d8ce20f1e4aacf4d9340231a7e4512d170e1aa8abad0af1ed5000083ed49a979e34a00b84d7608c114162f7888fab7738705864ffc8a3900009714b2f85ee4a728348f481c621654883d1ab016736f0831d166864c0ea44e4540e221324ec2e48b6808d3000053780000e0506861168f2a96be1be600003ad2a581682245c3d98000480a000000012ea460c84140818000445a21887731e730c12a2e507f1fb53d9403a92a51bf14cee1cf000014e44b4a000002108594e780000c6c8000553a652944700754b4c18dc00000004cae21190060000254aa0b8f5ea7fd071800015b7800047ac0000b7500000000104c8df11dc04de3e0c35f90e915e200000002c120000803425d80003a1600014f1a1e62eac4b18150127f0f40935ca6400003f0e169894e960e16341840500800000006984e1d937d132e62cc00024080c00000155480005456aeb80000000000000007ba84ac21d40788996828300009a093f2861a2184a7f4387000000000f84000017b1882a6680001d971d2449e800010c3000000001c11ea000003c00000185c0f4e76b00d30a1a2a200000cd497161c6a3d6d6211bb5000076f47022563268e05a52ee133c24ee4a20ddc1f1f0000000049912b50000af6449589a33e6a622903f1dc2154a0fd059d256633687f500000d5834c0772016f1fd71aec2d8136c08b411dc7654b370b7733325898d569ee23f725544d852b6a3ad6a5bc3c51a6f1c783a98c830aaa136e7fa87b3a03b3458a62ca6e8bbd5226874161800e626b208e08b725193c849e9d2959dc0534451e49caa0eb242a484450f1a68253e75dc8f683b22ad25049201a03f04dc0e44bd6087234e42dc87d690a72bf614c52ce1d8838882f3d16308fa173a0d7427da7cd553ca7dc9ee9a194de210b0000231d1e16593415c15d9399e6494961a86300001f1c967107e4cbc36840000ac900005c8cc5f2a3820960a3867409374cd46388f97829412f40ff076c018429ca0e98ffc00003a649c94c0e800002b86f8cc3c80fe22029eb9556242e12de4c0800029d94936aafd410044646148a84663a55a1dc22ab03
  | 71 => 0xd017cb0000a8cc0001d9d00000000000294f000000008c380000000043ce772512115a122106807cb000048084c01c5b22f266952a0a4f61ccc6998d409d5e47d2357cd17000004be7d8cb7628ea277400003fa06e42dde7f455b1141a00d295086c91044215e827c000037052584b147e6000030c6000043080000f3a000043c84802d8e53f887408c416b89f74422800000000000000033f000099488db1d7d00002a100000b2054727c1401682783f9a2b2840ba5fa1e7c62d82a297503022aa4d3911d83424a4b5880fa1032ffe64011cc08fd000005b400000493dc600001b51daa532644a91a8804f24a6ad38b208969198a568c71381c60000000096c222222c60020888867d42642050c9d22c729682c05395193124dc615c08227003dc20000fb4800058360050c778e6a00004bd9087902a521a000151b84fe34bc00000001092000000001e9257b4a7000008d70000387a90195442ab90840a7247cb152900000000000148c179cac255a30bfb21a439448b400001770a5b86cc005f000000000001bad2baaa11cb3880004cb60000b998e57322264047f903f53f08723465114812c2c0001350964c481c179840fa9a01b283528fd3981c4ba2ab3463c17582c281dbc65b1ef02a6c7dc0105a228332e26bc8e2a25b50f406f0d7291642434130c11f875e248496b8fe380000592278951525e90000483c32111411e58b024f95a4711732000129786af0968a905187aa3044ae000086480d30000a2488479d300a481c614f3a04500000000371983b328e3c0ca3e025500000000b981c9600007104b3a22b100008138a14842929ac2d6145a9a3d26488c0c030a80c420207154f78dd84a0a8efcee1969c06a61788b6b07f719963aa89a89d06200600005a782854130000068b97063dbe273ce2a1db4221c3fa000013420f1a7dcc6fa07e60d84191c83d9a1619608dd8ecd034c368c604056195881358580cced1c9825e655a0cce897210a63100e10881b4f7260913f3230d25de6bd936620cb0d128a642e28dd13b0a521941ba3ba56ea103857a006e04e890ac21e1dc525027c18dbaa1e33ec44f190738da337865fa8e61298237e0b03d14b14ce4e6ca3492462be6436c08ad03c9e3b03909e24c8d9c0a0000043406da1a6190214ecbd7800021742f4c136a6da239c6be4eff92f9052e55353990b4d4732a714517055544b208445fe21774208386c12c1033337e1f7018b142213f0375867ca42a3ba800007d10000000037a4000105d28b606f916a8e4306eea35c0000cb347840000c7314cc508a1bb1314a4c51f5047b8e7f82d654ea02494888bda000008888c502ee0c1c82f4944914d001c6cdc0762144093000014c48000178871b0ade0654000051e135a8000085aac054c70c83000000015f7246d4ce27788bfe00000
  | 72 => 0x4da4000021fa939072c042caa4835600000000a13800047820de4a8a24f23802a458bf6234414ae759000003c307fc561843f000000005c34ec0800000007878c3fa96a055200009ba18d706c802b8f919f551c848e68b4a93cb43680000000000000002a44000226c48ca752485e991e1006000000000002d547a38e2013103732612800799f906d886c91e4991f443aa54041aa2fe0c2ca320c50a058000000000001aa7326a37940001d693fe00000886922f56b219380002141000000002f517a44ed2798901a0daf40de3c8d49083a325640000cf218861218ab2800000004a44663540313202d289e7160e09495646451d21a1cab0000940c0000d79524094900000be421107bf424a9de7419c752cc3800000d26922c7249fca2aa67024d4d800047002bd447f8fe1184e6d1c00021db54c253853aa90e220dc8b5c576a5831ee8000078e800009e885255228963364680e000000000f8c00004c183ec545e93b800010742db4327c628800055da39e48c186a90000076019a000042a4914c000257a0000000143220d43dae1af85ef9ace000033d00000c104b6c408800027bf18da2f5c1f6a7a609b648c420a003d192409e55f18a4c52706598d978d012eb62e94b8d0aff03f884a027b280f34eea1d400009d037460000a1c00000000a3acc90800002400000000000000005bb8629a12e000000000000b660000a6cc0001b3b0000904c0f880003760000074097e93a440000000000058066e100c8a06300003034aa3a341171e560070180002582705d58a86ff0000771c3ae9744573c60e09fd052b22464e0d31b088608aa4f3877424a237a2129017e04d426529a4c5eca7e81f8405a8bdf8000536e93d00001d2518d2000016e192c106ca8283a68000481a000000000002514b104000000056206d048ea038d2cf8000120d800044be8da80001fd22366a8853ee00005234010c11e829654de3e2067e097c24022160970800017ee4240983a644427452d9370083e2822781125d98d6096498c400021ac4c6e3bc0c700672086262743c00000220e3674000000020b6000000000004c809e043958f3c48f200004da003711ae7ff07a5a00f44062b14a8e8dca25960ec049f8196348c7b3016029e1000091b8b83a62231d4590cd8181df49280e0c12c9d4224f8a2e841d0ed34f304841158000040d643b84f519f8000049789ef1efb0000000000005c953244934e400908331e2e60ffa15dd1cb4a61000017fe42466c60aed82d5535a49804d81117289c87a8a89800044dc0000938812300001cdd31c0000396a000000000000cec22e800015052200442c563926d2f0c000016fa83e0000779035b80000000000013886c000000000f9f279900005f1c000076705742f14000000026f622d8e2f000045548a100ba2b2954d80000
  | 73 => 0x82bb206a4a883a7405b0c8f4a2064fc092001342fcacc5389a3294bfe90fcc1511b84c04000113880004a928ee489800001a5a5ecc09600002a420001582000057b0000000001b50000aa550fd9e120fd826305d316c9216c1770dfb0000526241d890580004bfa3b6c187a8540b80000150ca4b74eca6dc94390ae52378adc92820000000013a81860d14440e84ecb732273129a4581237a7330576af1408000000000a6acf90000056e00000cdd000043f400002d2aa141cdc23d0ba7ab944ad856144878000000000000001b894f2800006818000306a41d4d7b962d00004ef8e382337000000000001e9e4fd600000000000000086f09c696f555647bfd1ee12fa58ac627cad3800000009e755240000000017493d8101502a88204eec20b24bc000011a814300000b0c800000004bbe0000000164b4db667f87b800003c8814501e3a3ac00004888000000000000000058800034969bf8000000041008dd4a10800002621f782900fc44798000126d9e5900007c3029995231a04467c0000000000082903c1000056ba31f0e5694fc544a28647f3836b08f659f8cf710da0e204198fac1c8600004c9800000003d323238000000024b80000b61a92d1d5064407e30c4f377c9d0c8abaa5a215625a800025f800000000b2000034f5221f4e8299800806a48d0798c9a5868a96ccea97ef29c0336932b201210a02ad47989b1700007390000256d00006cb4a38122a09e26248c1921a910da19846e617c6207831750e180003cb00944000258f1d62469934da0b74e9e6f6925aa86e2cfa217d4dda67447487e7d5e610e554984a8c0fa8fdf3db8af7d4bc010627d20758106163f1d2e0218b27195415644cf47180aa956249e8132a084a3b4a4ddcdaa1a7b2ba42fc53138d2f35566a0c0ff80001f7061a0f9c251c4b3494f89850e4700000001453293b5156965cc4b28091caa4650b3a8b7b44e8543411e1bbc1c7c219820c0df02646356800015fd1d76a36c82f00001f2816680002334053c556d25f2b7f29b651d92eb0000067a69f0ebc8ed6454c6f7544da3920e7079b06be992a0a7aad98cdd82643f04966c8d6171f2092329c000078633be09f8903896c0fce99704480f1b192ea0d424691fa000016b837382b400000000add267f34b235a000000004d4e0000cf4a0df16c271e007a969a315c48606b326aa0648ab78c20a924490c6658c18866b30da2b5ca36273d52788f807a798ec0e3c74a40b1104a037ab0bccf29c323a766dccfb38fd427f8413d3b017f04d209e542be80002b5c5fcc26696f32bce000000010f50eee0000e1300001e6e6ed000001cb000000002a78bed18583ed81a7a41100000bcce15850e00000b753a82ba204ea2fe90e725e7201a4048c600caf4e8c0000454180a211aa768c91196333fa7df400014e2
  | 74 => 0xa470aa6c02fb800036da0000000000000003db14a0045800006b4c60619c42288387504f1ff500004ba447b89b54ee85119131800051b017a12b49ccb328455204b99ec624a071655bca65107be0a28000000013ea18508cc00000fb6000017382f45084410865c23050d50617d42318334db896fc0001d0315cc5e8c00014fa216465a00000ef11eae58d93b69ffa49de62312800a7a560a1fa00000000000000001440000000059ec000000000003350b1d8be6000027dc00002d901960000000058553aa0f502a995f943e82778350953c35985bf4775228600008af953b0a3e09d029a85cb8f4e475c16b02b9235d1b0000003eb16d73f44824026e9b0d3fa6668c70a898147128df80448c46000013b53d88d3245c0a788ed6a4d80e8a77e9546ab3f40122134cb6256a2cc678713fd936a2a88000116f00004ab0000000029f9113072ed336a4a529cc11b4b7694c338cc21a43a082990af2275d2f413c5561454192dd800043f296f0194a7770000209c00022d90000a77cd6e838e575465710f6287907d084f55391a244b4682b441a06ba2e144d988ad00b9111e74547c38da7243c94805a72312504c3518eeb05e01f7c4ad8e8e2bb148e63e114fd9f0e27927754c390b310c9a65dc18e1e060d8c654c9f39ced10b6af5c9652a234e5aa398f34175e431e37986a88c73212c2a18abd9f8333e224846c285665830a3548fd806413cc6bbc2f09d9f147440c4a7b0acc52969520000166d2fb06b1909880002fe4aa40092960d138a9b2024d9b02066a4421500034d00004fd46d6135249c212b41c2800035b28784000149e040064f503b98ed00001a408af9cd7004c90cd5b9806a557c5f6800011d7104630d8fb2a0a723428acc03f80ee3e9e5648f8a0581211cab9503083cf324e2a6cda2256b136c490529ba86a18c03bf8bbc03c63eda7ee04e2191c4aac6e84224a7440a5a000010428fa000060f816380004cca701800021e247624bdcf8406344aea3f240002670176016e8000207800005030c470000563629cc1230c352bb406fd4cb80003efe472d3909625000016c90b00000556c0000b1e800029640000000000000005f88dcd9a0f3aa600e4000000000008e7907aa8b20c9600013739ec42af077dce319b0b00009fd0000000024940000f3b048110e890495af2c470000887c31199d8000083445b380004dbc319944c89e0213e93dcb889a362e860000efa9181484c092032ea8570058124cfa280000000729800006d5000053b94242247561e5c2400002d44d2815ed4f200003efc857c4dea9c130a60c7d4c01c15357e83f41e68ad43e4e7e84d5e9639464c11dc047897f58ae000029a00005818000072000000d921ff4f922ba849e03cfc58b089a1a6e80d4cd206572882700c000080630b0a138097a0874fc8925
  | 75 => 0xd4592830407f6000000000000000000080a00002d60667107480004676000020e148e42487530f5224cc10bc000048384a3239e000000028bb4030000051f84a900000000bda07cd34200000d7891cd3b8c000029911900ca600014eb214e48526bec00000002b4c00015020a3119826168000000000000000b71ab52158021086fb05560000000139a16e800000000b65a57d0970394c46d8dec4376a8705be1845338227c849a02c214c0270415ca98845d610b81c329c358a20000541231f4044000162d0000491e0000c06a16400004440000069b00001064fe1284b000097c094011133a220520ea219651dae1d30d62118f4640095800029b4413289fca7a8b64065e6124e549ab826a8903c0001e294c9a28d91b080000000535ca0506da4eea79dc0000000398e0000ab193ad28c60b10b3c18014834269952b03311ed662ec000008300009a0ce41800000000000000000040ce000054a9cf200000000e0900000324446d0bea31800006aa800000003f2687fc3fb0a9a2a14000000017c43cb800000000fdb086000015c3004a1624560496f83670000496c66f00000b70000079c0000300a9eb400000000000ae30bcd98b948e805b138e8e8b092e000152a80002b2e00012e0800058a8000085293fd000000012ad892f124e000000019de512068c4810918c400a00000000000473e84194fb20b4153e0000fbe000054b2000054187ca4bf24e40cb521734ff000000002b95232292e4f492aa61308a5501d98a0f25da7994c272bff154e751c135020640ae142c129913857ee389837c014b02c25e3800028d9284600ed6258000000043b4b0da4a3470680712060e2d423400000001c3e000000000002bf526f46954a0180002e3887787e993ef29b874695a2800023de008933d2b9940f623e4000083c067667300000000000073e8000187a4fb45c0d54180001e80397457d00002428000117994851f384f30c54ab6e0000a90d1f1249815423fd8a5524c111e24d710b582b626e2b0451f41b2532c44aa124e87030ca4325542497590df4695073f1b802eb84268bc292402f080a003e18e4a3f5299187d9131f2dfea8b0fe2146f00ca9ecc4bb01a7030435d4d1415b34b4e135400b229801982158677a85213304e145948e2f3a2600002c51fce2df49d2c17b21b14b64b1649238c1247e4353cb4599c503209bd82f9981b48968e1d01927412f821d0cd690e6c0b4841cd39ba18a26447b380d993b72bbe5590ec921ed492a8d289571d9b0000000002622cb2b600000c7a8f7d4d302ac0f2a27ba200a92ac33f95e30680a014f6e83890d000000fec209d00006df4a9e810100006640d2115a01c8a000132821d83ad0000000005fc40c8986868007ef000029d4000254e00ae630c74c1f31056a152d36b28d3334e965959999c
  | 76 => 0xce0c1807786ee91a520dead1c94208bf148e9fd88ad88fc0b84b078d580ced000000008e100000916935546011393aa2139429e1043276aa4a04a5a1da53d437689291be4474e7044019000024b20000419000051c61b64000253f2e96ae84f57266123f89e0d3f08c3f3f560000f69800037a0250800028a8518e7958b7100000000ad0d596087a335a0000b4c8000000000000000e56000004e8000000020a2000000000000e4e000133a80000924056013b0b5615e40001152028937ae7088000243a262420e065b9a45070264392d823d340ba613086f0000000062f11de800026aca778f28870239a611655ac1a70173ea2a941d86f1076aae993eb9029233c1c34205127d16d43c6484bab2b210c00014870d93449c739460f96591208000084e00003cf8a33089e1be24d840f4c000264c3de8506d4521d5d5192a700cc990110e744570000081251269620f9da36343823e9083406704720791d1841fc9000024400000bc804e6195856100cf088602883011e7044cc347c5a418ce1904a8342f49a1102fa0a8407904a153f82d295f2a7bb0b3e55f8000000017dca1c107e15ce46608d505db14600a5e648c5288e6d16989ed8bc0891313543f200e09a152bf096ad279a5ca00002290f0c084e2caa345492592a01eba5af48a02485344e3fe8a758000549472708a625d449d83c20704035e3e0641c08eb19131b08000065480000756000000000000280805c00000000c401de4ede1b5113f66c8800005b35426324438412ff089001811ac8454490650fc978892a3684a988de4800000005dc8cd5271f2d700000ff696a832340000f2000002b8c668144d1ab900000000000014a230a00000000000362008413348ff324240000d9b12b957de00011e892bf17ba2059523888537206b60d899b302ad6920930925d53eec14346a597fd4c142598e1613ff0eea7c612439b93203611d92c20b7f486050a1568091d53520044f7b0a7d3276056562822165672799138303724df615b156202aa2aee0aa006315d614c28398a4ba7091e7a5f0818382502a7eaa6c255815a3106a0a91ec1c4b578cb0214311d7221f4262c58409780b4eb04c0fb80000000a064769019f44a000000dd8d2751444bd0ecca11e0000000049880003608000000000001d0c0a30e1b0a3800000000fa000002ad800cc76f800000002f50496800007c06da400009141f02aa155dcab61287a91240001eec000043f483ca3f523c6507464018b744640a10e8b85f9280aa87c77d118b1be42588bb50ae726907c3c79428cf12369240753878e27c42080ba1000011a01a3800021b031f8941c00020f0144033e15e01ecf42608170b1f17eb515252445098c0609061250000062a026a46dcb5601cf1a460000f38804129aa7974017000000003cd0c4c0000000093
  | 77 => 0x5f922d0876051a84cc616ab96114e0c352ee983f0bda3a15137a18352d22190f271b534f16646559c098f14504f210bc9443177e875c37827270faa7cf46dc1f92271684a80d680010e1805b832da31a35bcac4d06c965323942620231a0cc2ed0017917a8dcd0aa04cd07d6253456f47d30acf08ca03ec694514706353c4aa5986911eb3224a1940c3d962e151e4bed3ff187c093c42800b4044b3978413902f804b20f42b4496e20bf56f0812c81c860b428a0700e242a8c2bee8b8c8681b0e08b62bb0cc39afa1fa07168d7209ca0fa43b80ba0a58a30f04c5960d0ee505569d0055e14e3499c7cf15930b6e3ed836204dca83c364e74e083696b23b6456504829f5f128802e0de2a2a923506a58069087f4f6eb10129e231c329e9898d8a8dd2000076e000006eb1a683524fca000000007440bc605cb3c4073ac638800023883fdc0a68000292a00000001c64416c493d1c99062000064548cd93d14f2c78d151aa856182c7cb4000000005940000000161017d6000028e8b5010000cb0000000031960000af995ec00000000307ac2215c299b0af7208a1d7095752a98c7b125821508b29d5a11582b780001cfb3d8ea9104c300004b6e0000000275f01c2866860598884178a2850dc0e804f7a210000006d32f2c32807dc876333ec4accf112a7800003d6508ea34850bc04cc0001f1b49b429c848a915258042be03de80002fbc00007318000000000015cfa78c00009fb02ec8e7c00009b40ccc23f4412863a0d77006b55be00009ce9ac1000000009fc80003de49decbe2a59f21e45704f29215021440000116aa402fb200187be0f1a162a79e95e2276614c6378c2380ccf07c609fc0001e9a2d046a38512000003640000daa80003cfa87c800021673558666cc3f147b47ca156c0000000018217ed5de1862000000755801bcb55008ca06101705315a7a140000bdb363232fc65e8d7b000076186dd13152caea5050d41f7916489a38000110408089a5ceb62a03155c33d43ca0fcb28d09e350370faa572678207b7a8b64616713c86e023447f26cfcbdb0b3f496c1a2812a15af0000046805292820b7e03880000000000098c84d200000d962a643b218440e7a9b4489399c923c4aa109bc036905c099e44c3a1d63ae26c48018887125745a3d1e7939249023938000044d558476d905d07a622188f641f2929c1b8a9f0d551918400001cc0bf1a6ea2a646dbc0001bbb38fc5c50e4d2833271c0df04e01509559298791f3132b0000aacd13906151aa61db935e9cac23fe418cfae8b2b163a022000019a14cf8abf8e3a8d1b1dd8b0906db18da4d7e266408c9fba31b02a2d19d059c44a601c8ce78de045b6280c6be000053904fa09b0a39d13c89f5533f1bc72636af2c42a99e047ec9df946b0ac133a000652012ba5164444d526a09
  | 78 => 0x47f0188370c7bc269f428477115111b2a5094af514a106d74d8879b45d6800042000f24a240aee43f02dd8d178e1e270252cc9dc12a6349200015c51def36c4000053410250df200011ff00000c5e87340000aad35962c8d43f153811a281201fc80004cba6de4dcd000000005d34eb10f011e6c54a0fc50cab127475e894d283239b0a3dc3dca2ad0eaa0001539927900007da8ddb04dc00000000084a94a000067ad08700003cf000000000000186400012cc0000000036c40000e0a1e4e00004e8879c00005364f8089dc1eb800004ba028f000067a000023d70000a3a515a0000008e00000001db9367c8b9c32782db22868ab042921362f2a164c5d5102b01ac6f7853f018025a800004a8087c53708fa8a9a952049bab0ec46d0c2b000010588238d6a31941f645c8232e176449a0d1d9d400db8000062d9db5000093a49c2000056a00001172a7a21bc200013b4000050aa51940001a1841ee610d4c6089c2d6200009f188e111de3a3d272a6e84c2a000002d037d55e865400001dae288a76ed56a9f4d30d8b0148a81eea35384a84cbb0d99580c0000ef704850000000022815d0280e42d0d34ac4d33628f28a5da29b523a6f4cb2d26254eb887f54af8b9556ce22447392b743a5a19702ec0da20132028c22b9c2a1a2474989f286ad4ece77695798b1e0bc86e2c0280ed512ea47449ba9ef321025afc9711c760c265cfcfdf265f012a747862b19cd15d40000eaa84ec38848af1335a50b12864da0178a0d54eb6a9acec899c03a661074f5b83cb520a56e088113ac18947d80177a6d53fcaa948e69000035c25164000036000008080f49a81300000000e571a3807940eb0d2e80001a16168c776a96c11c60000e7c1ab425a60000000197a15c8a3945cf12f54e1051109349ab24526927d5bf0d2c25448894aae14ea07fe7a94fa1a10225f020c4c3a94004bc25eec59e0a5400002091514abce3bba15800000e37237e929c373014c23603c3c7bb237b4bd81f2411aa9b512d05cece91800047ba022c9aea6f34a022a295c293310d3c382d058057131b6690125814044cb200000002985387e959c000271c10766904000268451e034a8119a84c2c78102cc9e12c74c7c92cd195000000000eb90619b344e985a2430c97e718d800000000d70218882e4aba9f8c561862c8a798ba849ac20a523da4632e5c6868f6f10f35496919c81a800019ae61440569776000012240000b4433345b305b2921f383c0000dcf000018dc974028f2afa1a8e90908a1000039bc8fbcaa30d9f000000002a324af0286000079ca4b82ae200008060000000000005fa00003a4e4f5400019ac0c08472113d80000000293c00008fe21e207e000000004a1057fc7569b8d00009b044790000066e01984241b5f24680000000000000005b9c3121ad14beca
  | 79 => 0x135d476130117b83ca80000dc6073400e80002be90000105c0dc8c5e1baa47cd36280004b88000000000400000000089ea86100000000000280b1e0c00004e100002ce029912f5136d0000000094680001496635437aa1a22b6c3320915a1df4ec80000000000051e4a9740001a63000000000000d7f40ea00012c39bff145e2cb46199f281e4a57954408a8900000ea0b90000030ba0000fc72423255e000000028f553fc03281c82882190c02c8ca01e83060c00000001b7a45806a101870a2c411637a80540d113d4600000001ac044824969216070400000000c84223a527a4ed86c596c41f1e25952c0ab4f13e6773d1ba110f28ee29e4c4c8e4d40168a3d0ad882e3642af8523a8a6b582aaecd391ab7c01a0318d16c09fa51a8239d5b181c2000000009cb8000570890809a21ee50e807180e9623433970660443d816b01269e9070f82ad0ea09794116238d552e0000dfca617000075d51be0e16109888d02109de338f6132961b007b0000706404118cf314800001f311f41e3c000115728dc2bea454400008b811260000ed21df338162adc6fe970b48204914764a6d40d8a0000e1217c331f28aad44290934e8e541c10f00001896015843415962712a04113491b92e3c3bd523e94f81f526ca0bfb0baf4ea2130458281970000533c38a818343546c687328ce500005e28d22000034ae0000d800478170a541000011055578b0391e190532e08000134516180b2a9114087007016923b74d84884b3d0000008e0932f18d0457800024b444763214a421a8921fc434c87c000046e422a4000000000da79789f615ea00004760e9781cd1ee44518b0d12c93a8681fd2b7089f19b25888078800000000000f260867381053a1549000004f6000140f809641940000000000015742da0475aa7421f2431ca58297a2c9e090ca0b850839d21dd115d280800001af0dec8af714dc5e4c000025d534849d40000f5100007d440000000000080cc5dd028b2f56953c00010ca579060dc5000c642f723b1d10b809c43ee8678919233c1cf655304e313623ffa570d54e26660e44aab85139adb2b563360654000a47048ce03b98ce635e49c58000129617b012f0df3a0cd514e9f0054f1a4e22625fc41e603e43a5030dc4bca90f19a0057d5639182448a90d51e7131345a06e0c000007d01f01dc40001f3a37dc0bdc0000000241cac2000028391fd2000000000f600006a3c000000021ae10c8000000055426d20e5508133ac29ae00000000232c00015690c9904b400006e989093cd205f90698ae03e42638c0000000000000011b023150000000101e1beb51fe68003088be500008361293173d311e000033013000000000091b0000128c000000018c827c075bd20a940e50041d5080d0a781a782f009f71fda099e2b3800012f0033c2fa8172a
  | 80 => 0x166900000000000095247500af40f51b8f007c7aa51a6055a0000abf075a80002fa668040000000240072bd205254038948fec5c4141453360fe13941dcb3e9c31bc22025aa22f46bf03898cbe4c329bb4ea08fd53bf60ee42229deb45a648ccbbf9d5b0d9c74351301d9e19283000a0481dd2f24613461802522344ad554af162c579ea1fc02695220f0681811a101812e1050805972c4f4a544ea4d860fef096219f11a90cac2224ae1d1b8a4893a1c00851059e0f2bc02898310ab7b1356ab9cf1b201e05ae7a9d5b02a1743668a6914a1a984b585e0802c1c8247b45bf92138a3b1f8032908f58b1c3a1e23b10cc88f0135a913130c156622d4a9c5343a52924d8573c1e4003f4be261b8a2f1a534a5c152089d85392418300472d9cf149a227a120b122308c8308ce74253544286aa120a0df552e442448229c6d5388871074a21292cb03e7877e8662563000015038afd00ee63a5505a028286c000067d1170000048280000ddc19ac2a700002acb00008840f4aa62f25202c1c4ab1d00000069900001f0d008ab124d5e1e1400000000000000000001ca537d1a1b327c0000fde000049c870413c200003c900000810000027b04d553cdabda38a400009f3166542ba27585d8a49712aa826d22d80003f6e3be0109a197519c8b451d0a64e000078005f7800002a25c6096d94da39b27324d03008c0a149b2c57801131bfc81a4da49ba449340000afd1b52519a689806c964951ec39dc2cf00a9189c51f48b986c851280e895f69f8544ea743103117494a261aa80b98000353c821000000f44c0c6af806d1f9c2e5a717c35027ee2fee1ea85219c2352f61b2800020472c6ea25c07980000000492114e9d01000047a8446a3c41f3692387d3044f3764a518c56043929443fd47aa80ab39c29c5d11785b61aee51fc09d8df9019a0a44e32843e0e4aa99922803bb0ebe6c4439fa64334d4000054b295c120600013901573000000008f389d8476e8e30000231321705d00d76860127b475340000a1b0ace777862a87fa01863ca4f9100003cae4a3149f900856060000cc5a50242c200000002c2a0000343c2f2ac3a1ff800001b0840950469178000080c0000737491804b5075a0000748150c0e2e6bcc68d001b2e5858cc3fa80001d2c82f8a1306b3366600000001d8c1e2097250bf9d6a54d05a34c2b20da39420000000000014380000f0b840237b66f7158e18a30000b0f86e5a74e1544a55c8020f89380e892c71b14b944c880742ca16d53fd64d9ccc48dce0eb8176c639098d359e63c95aa20a6000044acabd0c5f385c070cd0f98af0f78aa2498a00000bbc1681339182b228a05c88c40473354c3db8a49a7c12a767cd006e9024019c46b416d2a1d187c25c020625c34498524802a227e08e4a9a51f39c840a0677e0f3596a50d9a
  | 81 => 0x4851d2dc00001ab821047861c9738f24a603a4237901763094c6999be15b42434e498f7a119c2a40529a29135942d0c8269948314484b0000072d0b8677c945e1f8952387bf818a924c4b0c00000ce210b0d3a757c0000ecf00000ca88632bd31ca80215264800056ec91dc0001c3300000000b69a5a81d583474ef8845c45d0520841300d70de6a0554d7a8651992009cfdf9cdf27382fd5062861e4e0a9de43138a122858617867fa5a94410768035321224df023cd25925b33b5eabbce8c8f411fba800ce9ea3bb1aca307143a09d52ece41c81cd8895005e3f4531c9eb8434a25000ad95f4134000014b209932c2e00014ca00002128816cf2292ec4b3a54b120003ba132426f800028ac00007b912631c37206e86849cd000034fa0001592aad352b41c5930700000000118924f28842cb641fc9fa0000053ea5f4f29a1bd0000a051357145a222c5a6c82a051521008a9cdf622043fa07d406da061712982324fd1958f0c7c2af53f803bf107a413072581ba41d0ac3455c16ce04d072f541b21f135ce529cdd0242f202ca73559728221a12155c6a81bc0588a852850b8933063a0cb49bb059b30841298e9890bc3a3e25c47a81cb21a1468c877996151e249ee01499e03472e74a80d509ec57f00c784891e3c558212fcbe41b98173429b4e1c9d3c04080bd42880ba90abc7e7530002ae560c9e1499808ed4190933cb66a7b43576b0e14890cc0450404c0b3d234542e83ed0cb090ad27446b68bc81c1a2e0263b8bc48a3c44e01c64588033942d859dc2b7218d00006ecc162a58b31827248b4398eb400c1c8c343867a1f40a76d14ba9102b1657090cb0c472dd224b8000121655143a2921b2b491b0419100001bf3000023740a3800020700000c0a1a6e3e2200000001f524b720000bb19ee600000000a9f0000002a2968000135e44aa0000f6b1bfe46d098cc1ea800038ce0000000195e000000000001a020402b0ac7ff00004484000000017a6000033914cc00003d1eabb8fc8180c45c237e01a8800001145a200000d8c2b046200000063308bcaad426fa9dd41bc10ec559980852a2000111f9e6755c0502017600df529a68506b199a200000cf0d731440000076fc00014e713442669188251800007a7049c83d7184467e800018c40000000000000000000429000000000000248c000090628cea6fcdfc17e606da51cc0f097640bf4ab5800000001a304bf1450287c12a881f0000000003aa59900000f2b0d2c71fc000000041540000000132a000000000001f0a0000000128f0f4200000000a3080000000790cf5f0bf900000000870083f00006d4117715150000000054e80002d6a000000000002bb05d31257151840423d28000000013be06c4a2a0d06292055bc000000050d81c803d62ac0116673440000d8e18629f8cdc9
  | 82 => 0x590cc281aa6e41cba20d0bc6acf40000f9f02bcae0d48211a7515e2a49599243700001bf8a7a000000006c18b35996700002b1042e081d3752627935d28da57406184c3006e00ce2aa44e2b0bc942c435b894a0c3a0c923df8fd9a5721c623888f35020d1480a5f0a698b4b33c6557472ca3d200003ec000027d64938a16012610dd016660d8d168fed11d019e000024bc1c9060f492a93ae35d05e80ed4a33550148791271194520ca1eec0a815930cea00004278000110487f903d0000415045f92b2000043b815d00000000000025ec0001d481e60915000000001d522f54a5000000000000135a0eb236568aed4fa20a100000354bbc8fc53f9e6c9045f15cb53dc9f482208000000040710a7a55720d45ea92b00f9028d46e30164000034420000aa8000020bead343e802f209cc5a0d28a93e12f282da407c990c0000aa90cf31ac92ca00000f8ba51a4cdc1fec30e270119e245fc0001952000085b8b78807900008614c50060d4060a038ce1803c0fae609884382e636ce7a2023326b100005688bfc800022f05ae800007c53aac000152a24c741ac99cc7bbabfb38ba9b340ab00000000542ccf7893e5292685c5c484aa2a043fa88fc01d931988fb47fa1ec327841a0c16c2050537a1e405c099381f222cd89f801573c3443c0e4a86283e907a6155582f80e722388f330000398265f4062800000008a29070800000004794250215916700f381e0142e2a480b0551a246a4fd4a090ac48bb551880b0ca12860711286f3c27c800001203090485000000000000000173e12bc68d0c17a6cf3c1a6f5080c826b34788bf000000001136a69c581120d42240000ff088a6449a7624bb28e380f467f6ccb4a56848800000012a16512906b70a93868221b6000114625c73a2495781150ae845be99680000ecd14425d1c7411d3658584c84610943c55ec000134780000000a58433207284d40a4a8b05040120005add0e61114401c00000000350121c0ef061e99330d480000428a7103d2207b0b2282fa1b760f08395000045f465186b100001ac22c989d9912c52640d7cfda29ba0ff28e6d1491a2b494c671cdbfa01a10e0000067b0a4a23d8a6f000028070748000071ca61650627ec8bc5876b584e9cbc2b48cb423fc3e285b997a248a2828d2938e0110e60d095db9904533e563554f80000b76a2cd000226741f400005042a5347400a485fb172600007decb5b000002ec16582e6a082513c0000bad1fe60b008d3800000004480acd8000111800003f293fd2b8f0ff834e4c488ceb07b400010038000478e00004e9a1d100003af00000000491aa52087609f03f10712464808d5304aa254692a3c8555a4cc8ff200002fac430527323663f806cf0b031bb91afc1ab85bc15fe332a890cfa126e247bcae0000023b5142a52600001dc14ba
  | 83 => 0x12bba759000093fd02b0a762b5a00012d08000247e414000020931a7618980000000192c38353ae8000000000003a58ab41ac81ad8fcc894f000065250bd00002a3e6dece3580001e1a1e684590ea11bf64af457e0922180680550d68d2b00000e2c319051f57849200ed895b41390979906303a7365c738cd7505472212000156da2762522a1643f00d9708ba54ad5432b4a24ae0000c7997cf00000000f8d0f8d0000000000003e93d5a30e458c251d4432a3e4f772c0443728bc09de2309347c12cc76d00004c5a0825162246846966568af21d4f4d5e0d0523d15f022b0765931e0e95119a00a0d1b88bc03f4aa2c00012aa398664280001ca52f0ea60c3ee89bc312a580414e1611043470102d11069439e0049456a3f8103254c412685651f664bf4e838cd10b10174133381123f0201cc3d29fdd2dbe606540001b000ce5a8d50823ff4a1aa97138d80633bbe22d542e93ea012e5884cfda33d0e141544493286f571061a469aaa8125ba0000ec70ec82166ab449ee1d4e32c852bd415a55f4ac28dad1aa94d419162d0018893b20136709cfd51de12b2246549e68b6d28e2163c89b98d41dfeab18dad9b1d3f8c73c08ee926534900000d1500004a7600001ac8d812d6835008bd84eb57e81fcc4c104d93b504910fff0505133e88e52561c0e557463793310000062e555c00014323d8200010b41e7b4cde000000002ac46b48f14624800041403b440000e6f30e6789959a9ca4487606d028605ef42705a58adf279309c2994c1510000140e71c4d3f223e2c685e7472e270d04c46068318a8dd0c78a094d6826e600006add39c0dc83b9a4a9d5f60215000056400001b5d376e09a46309bd53c0e9b011938f981e8a66b87b6800000000c28a08246200000000a29000000000000853271e00002cb07580000101a08980001078120000013811f952dbc75f838306bb508000012e004c5141c6da0000181700003cd51d900001d3c6234000110a00007e5800000003260093858d8dae1b0c25b4f0480001e9800013b8088357c00460c1a1db71d26a4602c724c45448000140d00000c5a00008e989bf470834145e8948015181d8800013630000000000000000000af4055b0d9a510e34f891d903400003fac0000000444e000153ba90850ce45d800000000a4c885562500002160000086a8705393e688012017212438517150109db07e670d00001a7a1b8e0ef42e30260000042d53228924564e47300aa98b855d82cd4cbca1ae219095493d9168000009a8c65d8ef951ce9a7038a28c60c825f811d58a11309097ed55115034f84784092b2c16083605149f59b7e30303a8d2659d040aea6c7c7df877f52366dc05f1227c4bf80cacb6e854c000008611662b2150be4a3c00015a420aa5d8400024434dea9e38121117c17222724ce
  | 84 => 0x1148011e16f486dc15813a31fb81a8c84f25e44628644902f245f3eb4ab8cccfa9c2139661a8d8da54c0f30afd888f0ce10000096d106008e00000d245af9cdc14cc69e4bd71e492d1800003250000000054c050517ce2e4802dc599917500
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x843d74d97320421f3a0cb990210f5d065cc8108ece232e640847a70197320430eb24a7990218759153cc8108ece332c640843e74196320421eba0cb190211d9c6654c8108eee2b2a640843e74195320421eba0ca990211d5d4614c810caca630a6408666521853204332a90c2990213c5c0614c81087ce9b28640843d74d94320423ab8aca190211e5c1650c81087ce8328640843d74194320423b388ca190211e9c0650c8108eaeb308640847975980320421f3a4c7288210f5d263944108dce5b2c820846d72d96410431caa4c1208211edd5608c410cc8c528a620843e74d94310421eba6ca188211b9cb650c4108dae5b28620847970594310430eb24a61882187591530c410c9ca6b10620864d53588310432ca9cc0188210f9d3658841087ae9b2c42086695298221042b2b8aa410821595ca5108410aceea908420843e7498e500421eba4c7280218798d4394010c3ac6a1ca00862f4398a5004316a1cc5280218bd0d6294010c5a86b14a00843f74586500421e3a2c3280211b9cb65900108dae5b2c800847775586400422f39eca20021175cf65100108dce5b28800846d72d94400423ab8aca20021179cc65100108bae6328800846e721944004236b90ca20021879516310010c3aa8b18800862e545884004316aa2c4200218d5526110010c3acaa1e600846e72d963004236b96cb180211ddd5618c010ad2e5284600861f6550d300438ca1ca0980215a5ca504c01087ce9b28600843d74d943004237396ca180211b5cb650c0108eae2b28600843e74194300421eba0ca180211b9c8650c0108dae4328600861d6494c300430eb22a6180219394d620c010c9aa6b1060086555398430042b338ea5900214b5d052c8010a9ae62964008475715962004333294c3100219954a6188010acce3a92400856a70d4920042373b0a4900214b5d05248010a9ae6292400843e74194200421eba0ca10021179cc65080108bae6328400846f76548200423bbaac2100211d5db54c40108eaeda9e20087155350f100423abb0a5880214d5d052c4010aaae62962008475769461004333314a3080211e5db5384010c72cba1c20086396550e100438ca9a87080219a5966284010cd2cab14200847976946100431bb2ec8880218dd9464440108ecedaa2200847676d4d100431bb2e86880212d1d94344010c6ecaa1a20087155350d100423b3b0a4880214d5d05244010aaae629220085667294110042b8ba88088021cc5504044010ba2e620220085e17210110043a8a9c6088021e450d3044010ae2eb10220085b07448110043b029240880218ed976444010c76ca322200847a76d4d100431db2e86880212e1d94344010c76caa1a20087195350d10042f0b96c2880211e9da5144010ae2eba0a2008751538c510042f1b9262880215cdd52144010
  | 1 => 0x540432b31cc22a0219558e6115010cccc5308a80866562984540432cb1cc02a0219a58a60150108dce5306a60846d72983530430f39cc9298211d1c56294c1087ce8312a60843d74189530421f3a6c2a98210f5d36154c108dee4b0aa60846c72585530421f3a6c0a98210f5d36054c108beeca98a60861d6454c5304326a9ac429821875926314c10c5cc9310a60862d649885304317322c4298218b5916214c10c9cc6b10a60863664984530431ab24c2298219998a6114c10ccac5308a60863a64980530431cb24c0298219a98a6014c10cd2c5300a60846e721974304236b90cba18211d9c465d0c10a5ce42a6860852d72153430429b388a9a1821475cf65d0c10a3ae632e860852e721974304296b90cba18214d9c465d0c10a5ce429e860852d7214f430429b388a7a18214e9c053d0c108dce432c860846d72196430423b388cb218211e9c06590c108dee4b2a860846c725954304237390caa18211b5c86550c108ece232a860843e76d51430428f39ea8a1821479cc5450c10a5ce42a2860852d72151430429b388a8a1821479d25350c108eaebb0a860847575185430423cba8c0a18218e5506050c10a3ae732a860851f735954304297b92caa18214b1c96550c10a5ce432a860852d72195430429b388caa1821475d76350c1087ced29a860851d7594d430428f3b4a6a1821879da5350c10a3ceca9a860851c7654d430428fb82a6a1821475c15350c1087cec29a860851e7314d4304297390a6a18214b5c85350c10a6ce229a860853a7014d430429abaec2a1821c554f6150c10a6aea30a860871553185430438ca9ec0a18214e5d46050c10c72ca3028608719531814304358308c0a18210f9d36510c108dce4328860846d72194430423b388ca218211e9c06510c1087ce931ea40843d7498f520430f31a87a90218758d43d4810c6e8730ea40863543987520421f3a4c7290210f5d2639481087ce831aa40843d7418d520423b388c6a90211e9c0635481087ee8b02a40843c745815204237bb2a4290218b5915214810c9ac6a90a40843d73990520421fb9ac8290210f9d2631481087ae9318a40861e6498c520430eb24c629021879d26314810c3ae9318a40861e6458c520430eb22c629021879d16314810c3ae8b18a40843f76d0c520421ebb686290218798f4314810c3ac7a18a40843f7650c520421ebb286290218798d4314810c3ac6a18a40862d649885204326b1cc4290218d5926114810caac7308a40863964980520432cb1cc029021179cc65d08108bae632e840847671197420423b38ccb21021179cc65908108bae632c840847575986420423bbaac3210211e5d660908108ece332a840847a70995420422f398caa1021175cc65508108bce6328840845d73194420423b388ca210211e9c0651081087ce9b2e64
  | 2 => 0x6410a21785c332085109caec1904288565750c821443a22986410a21785c03208510c68a930e808863665906404431baa0c2a022187d526310110c38a9318808861f5458c404430e2a2c6202218bd526210110c58a9310808862f5458840443162a2c4202218dd526110110c68a9308808863754584404431a2a2c2202218d9964110110d2ac7208808853875500404434cb1a80202216c1c5401011087ceb326608843c75593304421fbb6a9982210f5db54cc11087eec2a6608843d76153304428eb98a998221475d053cc110a3ceaa1e608851c7550f3044272392c3982218e994548c110ad2e429c608853a75d0e304429c3aa8718221561cd528c110bc4e5b0c60885727518630442783b283182215c1d5318c110bc0e498c60884f276c8630442b93ae4318221d8548218c11087ce9b2a608843d74d95304421fba2ca982210f1d1654c1108dee4b2a608846c72595304428eb98a898221475d0534c110a3ceaa1a608851c7550d304431a2a6c2982218d150614c110c70cbaa260886386515130442ccb98a8982211e9d8534c110ad2e429a60885997414d304429d3ae86982218e197434c110b32e921a60885387550d304431c32a8698221c6dd5434c110b34eaa1a60885987550d304438c3aa8698221c6d95434c110e30caa1a60887927150d30443c8b8a8698221c650f524c1108f0eca9260887194354930443c8a1ec298221e450c614c110f228720a60884f07650530443c8a1a82982219c196314c110f228718a6088570754c5304433832a6298221e450d314c110bc0e498a60884f276c8530442b93ae42982219c197214c110f228790a60886706508530442e8b984298221e450c214c110ec2a410a608843f76d50304421ebb6a8182210fdd8540c11087aec2a0608862f5498830443162a4c4182218bd51620c110c58a8b10608863754984304431a2a4c2182218dd51610c110c68a8b08608863454987204431a2a2c3902219914961c8110c6ea930c408863454986204431baa2c3102218d151618811087ce9b2a408843d74d95204421fba2ca902210f1d165481108bee6b2a408845c73595204421f3aec8902210f9d4644811087cedaa2408843c76d51204421f3b0a8902210f1d85448110ccaca10a408872854480204429c3aa8788221b458e31c4110bc0e498e208862f5498a10443162a4c5082218bd516284110c58a8b1420884e672d921044273396c7082214d1d54384110d2ac6a1c20886a75498a10443522a4c508221a9d0e6284110d4a8731420886e262d421044368b1c6108221b898a3084110f228698420886e2624c21044237394c1aa0211b5ca60d501087eecaa0a80861d5458c5404316aa2c42a021879916315010c3ce8b18a80864e639885404326b1cc42a0218b9916215010c9cc6b10a80864d63588
  | 3 => 0x4d610c910ccea4b08648866452584324431daa4c0192218e152600c9108f0eab00648863b54580324431c2a2c01922196d4d600c910cd6a4b00648866852580324431c2a4c1a0a218d9975490510a68eaa1c82886956350e4144279384c520a21399ca6090510c76a8302828863465d91414423b3b0a8a0a218d1974350510a68eaa1a82886346550d414434bb1a86a0a213c9d46050510ce4ea30282886b35418141443582a0c0a0a213c5cc6050510d668630282886b143181414431a2a4c220a210f9d664cc510878eab26628843f76d53314421ebb6a998a210fdd854cc51087aec2a6628846e729963144236b94cb18a21475cc548c5109cce532c628856572996314423b3aec918a213c1c1648c510c6cca2a462885957315231442b2b90a718a214d9d7438c510a68eaa1c62884f27098a314423abb6a518a211ddd9528c510aa8e6a9462884e67298231442b93a8c118a218bd53624c510c58a9b12628862f5418931443162a0c498a2193d4c624c510c98a6312628863854d81314431c2a0c098a211d1d5644c5109c8e4b2262884f070591314423b3b0a698a21595c8534c510e2ea829a628853675d0d314431a32e8698a214d1d5434c510c68caa1a62887145350d314433232ec498a2199194624c510cccea3126288665751893144353aa0c498a21a9150624c510d8ea63126288666531893144332298c498a21b114c624c510d4e8631262886a543189314423b3b6a498a219918b524c5108e8eca926288554735493144332312a498a21b818b604c510dc6c4302628843f76d50314421ebb6a818a210fdd8540c51087aec2a0628851d731503144317aa4c418a218b152620c510c5ea8b10628862c54588314431daa4c018a218e152600c510c70a9306428863854583214423b3aec990a213c9c364c85108ecebb1e42884f270d8f214423abb4a790a211d5d853c8510acae429e428853675d0f214431b32e8790a214d1d543c8510c6ccaa1e42885547354b21443a229c6590a21591d532c85109e4eb3064288672759832144359aa4c190a21ac15260c85109e2e730642886b3439832144358a1cc190a21531cd52885108dcec2924288565719482144237bb2a410a21531cd5208510e4ea8908428872454484214423b3aec810a213c1c16408510c6cca2a042884757694c214423abb0a610a21595c85308510a6ceba1842885347550c214434ab1a8610a21785c252085108eeeca904288554735482144273bb2a410a21c9d515208510e48a8a9042885c47354821442f1b82a410a2159dd95208510cceeca9042887277454821443923a2a410a21d1dcd5208510ac8e6a9042887447354821442a239aa410a2199d8d5208510ccac6a904288727435482144392a1aa410a2159dc15208510ec6e0a9042884e576cc821442b3bae
  | 4 => 0x78ecaa2868843e75995434428eb9ccaa1a210f5ce6550d10c3ae732a868851f735954344297b92caa1a214b1c96550d10a6ee2b2a868853b70595434431ab88caa1a210f9da5350d1087eeca9a868843c7654d4344297b92a6a1a214b1c95350d1087cec29a868852e7214d4344296b90a6a1a214d9d66150d10c68cb30a868853475585434431a32ac2a1a21691c96150d10b60e0b0a868843e741944344237390ca21a211b5c86510d1087ceb320868843d76d50434421fbb0a821a218d1526110d108e8eab08868863854980434423c3aac021a210f9d263d491087ae931ea48843d73992524421fb9ac9292210f9d2639491087ae931ca48843f76d0e524421ebb687292210fdd9439491087aeca1ca48863664586524431d322c1292210f9db545491087cec2a2a48861f54d8d524430e2a6c6a922187d506354910c38a831aa48843d73d91524421eb98c8a922187d936354910c38c9b1aa48861f74d8d524430e3a6c6a92210f9d0635491087ae831aa48861f6418d524430e320c6a9221879d06354910c3ae831aa48864d7218d524432ab88c6a9221965c0635491087ceda1aa48843c76d0d524430fb1e86a92218718f435491087ceca1aa48843c7650d524430fb1a86a92218718d4354910c98c7b12a48865463d855244237bb2a429221531cd521491087ce9318a48843d7498c524430f31a86292218758d43149108bce7b2e848845d73d97424431a2a4c3a12211d1d561d09109e0e0b0e848847571d96424423cb86cb2122117dcd65509108b8e6b2a848847675d85424431baa0c2a12211e9d76050910c76a8302848845e73194424422eb98ca212218d15261109108e8eab08848863454584424431c2a4c0212211e1d56010910c70a8b00848843e74d97324421eba6cb992210fdd165cc910878e8b2e648843e74197324421eba0cb992210f9d664cc910878eab26648843f76d53324421ebb6a9992210fdd854cc91087aec2a6648851d73153324423a3aac3992211e1d560cc91087ce9b2c648843d74d96324421fba2cb192210f1d1658c910a9ae429c648854c7354a324421f3a6ca992210f5d3654c91087ee8b2a648843c74595324423bb8aca992211d1c4654c910a3ae62a2648846e7694932442363b2a499221531cd524c9108ecebb0a648863754d85324431a2a6c2992213c9c3614c910c6ea830a6488634541853244333290c29922199548614c91087ce9b28648843d74d94324423ab8eca192211e5c3650c91087ee8b28648843c74594324421f3a0ca192210f5d0650c9108dce4328648847671194324423d380ca192210f9d6640c910878eab20648843f76d50324421ebb6a8192210fdd8540c91087aec2a0648846d76d48324431baa4c2192218d152610c9108e8eab08648863754584324431a2a2c21922195d
  | 5 => 0x871a5350d308438dbaa8698421c61d5434c210d36caa1a610871b6550d30843c9b8a8698421e41c5434c210e3287a92610878943949308438ca1aa498421e250d524c210e96c6a92610872b4354930843a521aa498421ca50d524c210e9286a92610870943549308430eb24a61842187591530c2108daeb310610846f755883084236bb4a4184218b992520c210c5ac9290610846f765483084317322a4184218b591520c210ccca5308610866552984308432aa9ac21842199949610c210ccaa4b086108666529862084332a94c310421999496188210c5ec9292410862c649492084317b22a4904218b1915248210ccca530841086665258420842b3396a988421599cb53c4210e2aa6a1e21086656594b1084393a1ca588421c950e52c4210ccacaa9621086696594b1084334b2aa588421699cb61d5110a5ce431ea88852d7218f544429ab88c7aa2214e5c063d5110a6ae3b16a88853970d8b5444297396c3aa2214b5cb61d5110a5ce5b06a88852d72d83544421fbb2a82a221179cc60151108bae6300a88846e721805444236b90c02a2214d5c76315110a5ce4318a88852d7218c544429ab88c62a2214e5c06315110a6ae3b10a88851e73188544428eb98c42a2214d5c46215110a72e0310a88851e73d84544428eb9ec22a2214b9cb6115110a5ae5b08a88863763584544431ab1ac22a221475cf64d4d10a3ae6326a68843e7498b534421eba4c5a9a210fdd162d4d10878e8b16a68846f725865344236392c329a21591c96194d1087cedaa2a68843e761515344317aa6c4a9a218b1536254d10c5ea8312a68862c541895344317b26c4a9a218b1936254d10c5ec8312a68862c641895344327b18c4a9a218d1936154d10cc8c5b0aa68863864d81534428eb9ea829a21475cc5414d108beeca98a68854c7254c5344317aa4c429a218b1526214d10c5ea8b10a68862c545885344317324c429a218b5926214d10c5cc8b10a68862d645885344333b8ac429a21991c56214d10c6cc8b08a688635645845344333312c229a21995896114d1087ce8308a68843d741845344237390c229a211b5c86114d10c74c8b00a688639645805344335312c029a219a5896014d10ce2c2b00a68843e74180534421eba0c029a211b9c86014d108dae4300a68846e72d974344236b96cba1a218d15261d0d108e8eab0e8688634545874344278382c3a1a21475cf65d0d10a5ce5b2e868852d72d97434428eb98cba1a21875cc65d0d10c6ae232e868852f7254f4344296392a7a1a214b9c853d0d10a5ae429e868863465987434429a3aac3a1a218d19561d0d10b60e0b0e868846e721964344236b90cb21a218dd526190d108e8eab0c868863b54982434423c3aac121a211bdc96550d108d8e4b2a868847771595434423db82caa1a210f9da5450d108
  | 6 => 0x2842a6b98a9294214b9d25394a10a5ae929ca50852e7414e5284296ba0a729421c394d4394a10e1aa6a1ca50856571d9252842b5380c9294214b9d26394a10a5ae931ca5085677158e52842973a0c7294214b5d06394a10acae231ca50856a7018e52842b3b8a8729421591c54394a10e1ee6a1ca5087277150e528439238a87294214b9d36194a10a5ae9b0ca50852e741825284296ba0c129421539cc6094a10a9ae6304a50843e7418d528421eba0c6a94211b9db5454a108dcec2a2a50854e7315152842a6b98a8a94211b9db5354a10a5ce929aa50852d7494d52842373b0a6a94214b9d05354a10a5ae829aa50870e5350d5284386a9a86a94215a1c16454a10a5ce931aa50852d7498d52842b5384c6a942159dc56354a10a5ce831aa50852d7418d52842b2b88c6a94215a9c06354a10ad4e121aa5085697090d5284387b9a86a94215a9c04354a10ad2e021aa50852f7458552842963a2c2a942153dcd6154a10a98e6b0aa50846f76548528421f3a4c6294210f5d26314a10c3cc6a18a50861d6350c5284338b0cc029421179cc65d0a108bae632e8508666529864284333292c3214219a54b6050a10cd2a4302850845e73194428422eb98ca214219a9496010a1087ce9b2e650843d74d97328421f3a0cb994210f5d065cca10c5cc9296650862d6494b3284317322a5994218b59152cca10cd2a53066508669525833284333296c29942199948614ca10ccaa430a650843e74d94328421eba6ca194210f9d0650ca1087ae8328650862e649483284316b24a4194218b991520ca10c5ac8a906508666529843284332a94c21942199949610ca10ccaa4b086508669529803284335292c0194219a549600ca10a3ae62a4830843e769514184334a96c0a0c219a548605061087aedaa0830851d73150418430eb24a798c218759153cc610c5cc9296630862d6494b3184317322a598c218b59152cc610cd2a53066308669525833184236baec498c211b5d4624c6108dced292630846c765493184236bb4a418c218b992520c610c5ac9290630846f765483184317322a418c218b591520c610cd4a4b006308669525803184335292c190c219a54b6048610ccca530c810866652586408430f2a2c6204218755163102108daeb310810846f755884084236bb4a4204219398e5210210c9ac7290810846f76548408432731aa4204219358d5210210ccca5308810866552984408431aaa2c220421999496110210ccaa4b088108699635004084394a9280204218b99252cc210c5ac9296610870d4394b3084317322a5984218b59152cc210e1a86a966108666529863084333292c3184215a5c8538c210cd2cb29461086696554a30843a4a9aa518421cad0d528c210e5286a94610870d439493084386a1aa4984211e9d8534c210ad2e429a610
  | 7 => 0xb996210f5d065ccb1087ce932c658843d7499632c421f3a4ca996210f5d2654cb10ccca430a65886655218532c421f3a6ca196210f5d3650cb1087ce8328658843d7419432c434ab1a8720e216c1c143907109cce530483884767615141c434bb1a86a0e218e9516010710acae429c63884777654a31c4273394c118e21391c9644c7109e0e0b2263884767614d31c42b2b90a698e21c514d434c710cceca31263886657518931c4333298c498e219914c624c710d4e8631263886a54318931c4371380c498e21b85c0624c7108eceda92638866462d4931c423a3b2a498e2199189524c710cb2a6b0063884f270d9321c423abb4a790e211d5d853c8710acae429e438866a5258021c423abb4a610e21595c85308710d2ac6a1843884777654821c42b3bb2a410e2199dd95208710ac8e6a9043886676354821c4332b1aa410e21c9d0d5208710e4a86a9043884e576cc821c42b3bae6410e21595d43208710bc2e0190438852e72d5240c421f3b4a8a06210f5db5410310a5ce5aa0818861f5458c40c430e2a2c620621a558e4110310a3ae929e61884e47258730c428eba4a6986218b1925248310c58c8a9241886655218520c4333312c3aa4219a58a60d5210ce2c3306a90843f76550548430eaa2c62a421879916315210c3ce8b18a90864e639885484326b1cc42a4219398d6215210c9ac6b10a90865663584548432ab1ac22a421999896115210ccac4b08a90866662587538430f39cc929c218e9926094e10c72c9304a70845f7654c538430eb22a629c21875926314e10c5cc9310a70862d649885384317322c429c218b5916214e10c6cc8b08a708635645845384333312c229c21995896114e10cd2c5300a708671619805384237394cba1c211b5ca65d0e108dce432e870846d721974384297396a9a1c214b5cb54d0e10a5ce42a6870852d72153438428eb9ecba1c214b9ca65d0e10a5ae532e870851d731974384297390cba1c214b5c865d0e10a5ce5a9e870852d72d4f4384297390a7a1c214b5c853d0e108dce532c870846d729964384237390cb21c211b5c86590e108dce532a870846d729954384237390caa1c211b5c86550e10a3ce7aa2870852e72d514384296b96a8a1c21479cc5450e10a5ce42a2870852d72151438428f3a4a6a1c21475ce6550e10a5ce532a870852d72995438428fb9acaa1c214b9c86550e10a5ae432a870851d75d8d4384297396a6a1c214b5cb5350e1087ced29a870851e7694d438430f3b4a6a1c21c69c25350e10a3ceca9a870851c7654d438421f3b0a6a1c214b9c85350e10a5ae429a870871553d85438438aa98c2a1c211b9ca6510e108dae5328870846e721944384236b90ca21c210f9d263d4a1087ae931ea50861e6350f528430eb1a87a94210f9d26394a1087ae931ca50854e731525
  | 8 => 0x63544208eeeca88a21063564544510832ab1aa2288411bdd562904208bce632a821045d73195410821f3a6cb988410f5d365cc420c3ac929e621061d6454f310821f3a0ca988410f5d0654c420c9ca631262104e9701893108332314a29884199189514c42087ce9b28621043d74d9431082b3baa42108410f9d2639402087ae931ca01061e6350e500830eb1a87280411bdd562900208bce7b28801045d73d94400822f398ca20041175cc6510020c3ca8b18801061d5458c4008316aa4c4200418d9516110020c6aa8b08801061d6550f3008237baac51804187d95434c020e3287282601043e74d94300821eba6ca180410f9d0650c02087ae8328601061d6494c300830eb22a6180419354e620c020caca6b086010655535843008386a9a87900411b5da5288020e32a6a1c40104797694a2008317b2ec8900418bd9464480208dcedaa2401046e76d4d2008317b2e86900412b1d94348020c5ecaa1a401070d5350d20082b4ba88090041ca5504048020b92e620240105e17110120083a4a9c6090041e250d3048020c76cbb22401063b65191200823d3b6a6900418ed974348020970eca1a401063b6550d200838ca9a8690041785c76248020ad2eba124010749538c920082f1b8a64900415add52148020ccac530ea98866a6258354c433930ac1aa6214b9cb5495310a5ce5b22a98843f7655054c431b324c329e218d5926194f1087ce9b12a78843d74d8953c422fbb2a629e218b9926214f10c5ac9310a78862e6458853c4316b22c429e21991c56214f10ccac5308a78863a6458053c431cb22c029e219a9896014f10cd2c4b00a7886726158053c4237396cba1e211b5cb65d0f108dce532e878846d7299743c4297396a9a1e214b5cb54d0f10a3ae7b2e878852e72d9743c4296b96cba1e214b9ca65d0f10a5ae532e878851d7319743c4297390a7a1e214b5c853d0f108dce432c878846d7219643c4237394caa1e211b5ca6550f10a5ce5aa2878852d72d5143c431daa0c0a1e213c5c46050f10a3ae732a878852e7299543c4296b94caa1e2147dcd6550f1087ced29a878843e7614d43c4297390a6a1e214b5c85350f10b48e4b0a87885b07058543c431d328c0a1e216c5c46050f10d64c2302878846e7219443c4236b90ca21e210f5ce64d4b1087ee6b26a58843e7498f52c421eba4c7a96210fddb43d4b1087aeda1ea58843f7650f52c421ebb287a96218e99160d4b10a5ce9a94a58843e7498e52c421eba4c7296210f9d06354b1087ae831aa58861f6350d52c430e31a86a96214b9d36254b108deeca90a58843e7498c52c421eba4c6296218798d4314b10c3ac6a18a5886726158052c422f39ecba1621175cf65d0b10ccaa530e85884f17198242c422f398ca21621175cc6510b1087ce9b2e658843d74d9732c421f3a0c
  | 9 => 0xcb1926090789438c930482b43aa64982419a195324c120f128699260905e0714c9304838ca1ea2982413a9da214c120cd0cb10a60907894388530483343284298241725cc214c120f128610a609043f76d50304821ebb6a8182410fdd8540c12087aec2a0609062f5498830483162a4c4182418bd51620c120c58a8b10609063754984304831a2a4c2182418dd51610c120c68a8b0860905387550f2048364b1c6590241781c532c8120c6ea930c409063454986204831baa2c3102418d15161881209cce3b2440904e671d8e20482963aa8710241a358d4388120d4ea930c40906a4549862048353a1cc310241a950e6188120dc4c3a8440906c9638c2204837130c6110241e250d3088120dc4c2984409043f76550540830eaa2c62a0418d5516115020c3cc8b18a81061e7458c540832731cc42a0419358e6215020cacc7308a810655639845408333314c22a0418d9916115020cacc6b08a810655635845408333312c22a0419658e6015020ce2c3300a81061e73992530821f3a6c4a98410f5d36254c2087ce830aa61043d74185530822fbb2a629841875915314c20caaa6b08a61061d6498c5308317324c4298418b5926214c20c6cc9308a610635649845308333314c2298418d9916114c20c6ac8b08a610656635845308333312c2298418e9926014c20c72c9300a610672619805308338b0cc0298411b9c865d0c208ece232e8610475711974308297390a9a18414d9c454d0c20a6ae22a6861051d73d97430828eb98cba18414b9c865d0c20a6ce232e8610535711974308297390a7a18414d9c453d0c20a6ae229e861053a7014f4308237390cb218411d9c46590c208eae232c861047a70196430823bb8acaa18411d1c56550c208dce432a861047671195430823ab88caa18410f9db5450c20a3ce7aa2861051e731514308297390a8a18414d9c45450c20a6ae22a2861051e7494d4308236baec4a18411b5d46250c208f2ea302861063954181430828eb9ccaa184147dcd6550c20a6ee2b2a8610534715954308297390caa18414d9c46550c20a6ae232a861051d75d8d430821f3b4a6a1841475d65350c20a3ced29a861061e7694d430828f3b2a6a1841471d95350c2087cec29a861051e7314d4308297390a6a18414d9c45350c20a6ae229a861053a7014d4308296baec4a1841c354f6250c20a5aea312861070d53189430838ca9ec0a18414e5d46050c20c72ca3028610719531814308354310c0a18410f9d36510c208dce4328861047671194430823ab88ca218411e9c06510c2087ce931ca41043d7498e520831caa4c1210411edd5608c820ccca430a641043e74d94320821eba6ca1904187592530c820c3ac8a98641065653584320832aa9ac2190419654e600c82087ce931ca21043d7498e510821f3a0c6a88410f5d
  | 10 => 0x45e73194414822eb98ca20a418b1526210520c58a8b10829063854980414831c2a2c020a410fdd165cc520878e8b2e629043e74197314821eba0cb98a410f9d664cc520878eab26629043f76d53314821ebb6a998a410fdd854cc52087aec2a6629051d73153314821fba2cb18a410f1d1658c520aaae229c629043e74d95314821eba6ca98a41475cc544c520c5ea9b12629062c54d893148275386c498a418bd50624c520c58a8312629043f74594314821e3a2ca18a410f9d0650c52087ae8328629043e75990314821e3aac818a410fddb540c52087aedaa0629043f76150314821ebb0a818a418bd52620c520c58a9310629062f5458831483162a2c418a4193d4d620c520ccac5a88629066562144314831daa4c018a418e152600c520c76a8b00629063854580314832da9ac018a419cd45600c520ce0a2b00629063854982214831c2a2c110a413a9c364885209d4e1b1c429046d7614e21482b2b88a710a414b9d74388520a58eaa1c4290744538c621482b23aa6310a413a9d66088520cd4eb30442906ab5498221483542a4c110a413a5ce6088520d568730442906a9439822148393aa24210a41c915121085208dcebb2042904e8705902148317328a810a411b5da53085208daec29842905657114c21482973ae8610a414b1d54308520d1ac6a1842905e1709442148273bb2a210a41c9d515108520e48a8a8842905c47354421482f1b82a210a41395db3108520bc2e198842904e5760c421482b2ba86210a41d114c3108520bc2e0188429062c5498b404831732c85202418bd506250120c3ea9318809061c5498c404830faa2c620241871516310120c5ea9310809062c549884048317aa2c4202418b1516210120c5ccb210809068d63908404831baa4c2202418d1526110120c6ea8b08809063454584404829c3aa8020241a658d4010120b50e4a00809043e75993304821e3aac9982410fddb54cc12087aedaa6609043f76153304821ebb0a998241475cc54cc120a3ae829e609051e7550f304828e3aa8798241391c562cc120c74ca2a460905717114e304829d3ae87182414e1d5438c120bc4e3b14609056a7518a30482743b285182415a1d5328c120bc0e299460904ea76886304821f3a6ca982410f5d3654c12087ee8b2a609043c74595304828eb98a898241475d0534c120a3ceaa1a609051c7550d30483162a6c4982418b150624c120c70cbaa260906386515130482ccb98a8982411e9d8534c120ae2e229a60905997414d304829d3ae86982418e197434c120b32e921a60905387550d304831c32a8698241c6dd5434c120b34eaa1a60905987550d304838c3aa8698241c6d95434c120e30caa1a609078a7250d30483c4b928698241e250f624c120f128631260907894390930482743b28498241e250d424c120cd
  | 11 => 0x48274382c5a1a41475cf65d0d20a6ce3b2e869053571d97434828eb98cba1a41875cc65d0d20c5ae432e86905377154f434829a38aa7a1a414d9c453d0d20a6ae229e869062c6598b43482963aac5a1a418b19562d0d20b50e0b16869047671196434823ab88cb21a418bd526290d208d8eab14869063b54982434823c3aac121a411bdc96550d208eee2b2a869047471595434823db82caa1a410f9da5450d20878ecaa2869043e75995434828eb9ccaa1a410f5ce6550d20c3ae732a869051f735954348297b92caa1a414ddc56550d20a68e2b2a869053b705954348316b90caa1a410f9da5350d2087eeca9a869043c7654d434829bb8aa6a1a414d1c55350d2087cec29a86905367114d434829ab88a6a1a414b9d66250d20c58cb312869052c75589434831632ac4a1a41691c56250d20b50e0b12869043e74194434823b388ca21a411d5c46510d2087ceb320869043d76d50434821fbb0a821a418b1526210d208d8eab10869063854980434823c3aac021a418e15260d0920c5ccbaa4849052c7550e4248346b1a87212413a9c261909209cce3304849063b54181424831632ec8a12411b9d85450920c58cba1a849052c7550d424831632a86a1241a3d8d43509209d4ea302849066a751814248355aa0c0a1241aa15060509209d2e630284906ab431814248354a18c0a12418b152621092087ceb326649043c75593324821fbb6a9992410f5db54cc92087eec2a6649043d76153324823b38ccb192411d5c6658c920a3ae62a464904e67199632482b2b8ccb192411b9d7648c9209d0e0b24649062e6515232482c6b98a919241595c4538c920a5ceba1c649052c7550e3248275384c319241399c6608c920ad4ea304649063754d85324831a2a6c2992418dd50614c920c68a830a649065753185324832a298c2992418e153604c920c70a8302649046c75591324827238ac8992413a1c1644c9208dcec29a64905657114d3248387aa0a6992414b9d7434c920c58cba1a649052c7550d324831632a8699241c314d434c920cc8cbb0a64906646518532483333a8c299241995d4614c920d4ea830a64906a4541853248363a98c2992419994c614c920cc8a630a64906c4531853248353a18c299241a950c614c920dc0c3b0264906e361181324821fbb6a8192410f5db540c92087eec2a0649043d76150324828eb98a8192418dd52610c920c68a9308649063754584324831a2a2c2192418ed52600c920c70a9300649043e7498f514821eba4c7a8a411bdd932d4520ac8e2996a29043e76d51514821f3b0a8a8a4187d536354520c38a9b1aa29061f5418d514830e2a0c6a8a411ddd95114520aa8e6a88a29043e7498c514821eba4c628a418798d4314520c3ac6a18a29062c5498b4148274382c5a0a418bd506250520c76a83028290
  | 12 => 0x18c419998a510c620ccac5288631063664544318831ab22a218c4199989510c620ccac4a88631067151980318833928ac018c419c545600c620ce4a2b04431067151d812188333314a3204419958a5190220c3ca8b18811061d5458c4088316aa2c4204411d5d661102208eeeab08811047576944408832b31ca2204419558e5110220cccc5288811066562944408823bbb2a2204419598d5110220caac6a888110666625444088332b12a220441a658d4010220e62a2a00811063664947308831ab24a398441c550e51cc220c6cc8a8e611063564547308838aa1aa3984419998a518c220ccac528c61105717114e3088338b2ca3184419c595518c220ea2a6a8c6110733435463088398a1aa318441c550e514c220e2a86a8a611047a7614d30882b8b88a698441c694d434c220e36eaa1a61107187550d308834db2a8698441c6d95434c220f16e4a1a61107887250d30883c8a1ca298441c650d514c220f2286a8a6110753635453088399a1aa298441d490d514c220e6286a8a6110751435453088388a1aa29844187592530c220c3ac8a98611064d53588308823abacc2184411ddd5610c2208eaed288611063664944308831ab24a2184419998a510c220ccac5288611047776544308831b322a2184418d591510c220cccc4a8861106656254430882b338ea990441599c753c8220e1aa6a1e4110665659472088393a1ca390441c950e51c8220ccacaa8e4110671659472088338b2aa390441699c762d5120a5ae431ea8905367118f544829ab88c7aa2414e5c063d5120a6ce3b16a89053571d8b5448296b96c3aa2414e5c361d5120a6ce3b06a89053571d83544821fbb2a82a2414b5cb6315120a5ae4318a8905367118c544829ab88c62a2414e5c06315120a3ce7b10a89051d73d88544829b38ec42a2414d5c76215120c5ec6b10a89062d635885448296b96c22a241479cc6115120a3ae6308a89052d72184544829cb80c22a241475cf64d4d20a3ae6326a69043e74987534821eba4c3a9a410fdd161d4d20878e8b0ea6905647158a534821f3b6a8a9a410f9d85454d20c6ea9b0aa69063454d85534831baa0c2a9a418d1506154d20c58c9b12a69063764d85534831a326c2a9a418dd906154d20c68c830aa690657631855348333b10c2a9a418e1936054d20a3ae7aa0a69051d73150534822fbb2a629a41551c55314d20c6ea9308a69063454984534831baa2c229a418d1516114d20c5cc8b10a69062d64588534821f3a0c429a410f5d06214d20c6cc9308a690635649845348332b14c229a418d9916114d20c6ac8b08a690665625845348333b92c229a41991c96114d20c74c8b00a690639645805348334b12c029a419c9856014d20ce2c2b00a69047671d97434823ab8ecba1a418b15262d0d208d8eab16869062c5458b43
  | 13 => 0x6114e20ccac4b08a710669629805388338b0cc029c411d9c665d0e208eae332e871047671197438823ab88cba1c414d9c754d0e20a6ae3aa6871053671153438829ab88a9a1c41475cf65d0e20a6ce332e871053571997438828eb98cba1c414d9c465d0e20a6ae232e871053671d4f438829ab8ea7a1c414d9c453d0e20a6ae229e871047671996438823ab8ccb21c411d9c46590e208eae232c871047671995438823ab8ccaa1c411d9c46550e208eae232a871051e73d51438829b38ea8a1c414d5c75450e20a3ce62a2871053671151438829ab88a8a1c41479d25350e20a3ae732a871053671995438829ab8ccaa1c4147dcd6550e20a6ce232a871053571195438828ebaec6a1c414d9c75350e20a6ae3a9a871043e7694d438828f3b4a6a1c41879da5350e20e34e129a871051e7654d438828e3b2a6a1c410f9d85350e20a6ce229a87105357114d4388386a9ec4a1c41c354c6250e208ece3328871047571994438823b388ca21c411d5c46510e20a3ae62a4851043e76951428821ebb6a821441475cc5410a20c3ac929e651061d6454f328823abaec2994411d5d4614ca2087ce931ca31043d7498e51882ab398a928c41555cc5494620a6ce929ca3105357494e518829b3a0a728c414d5d05394620e2ca6a1ca3107155350e51882b2b96c928c415c9c06494620a6ce931ca3105357498e51882b3b92c728c414d9d06394620a6ae831ca3105657218e51882b9380c728c4159dc94394620ac8e4a1ca3107177350e5188393b928728c41c91c94394620a6ce9b14a31053574d8a518829b3a66528c414d5d332946208eeec994a310536740ca518829aba06528c415c5c03294620a6ce8304a3105357418251882ab398c128c41555cc609462087ce831aa31043d7418d518823b3b6a8a8c411d9d85454620aace62a2a31055573151518823b3b6a6a8c414d9d25354620a6ae929aa3104767614d518829b3a0a6a8c414d5d05354620e2ca6a1aa3107155350d51882b8382c8a8c414d9d26354620a6ae931aa3105727098d51882b3b92c6a8c414d9d06354620a6ae831aa3105657218d51882b9380c6a8c415c9c24354620ae2e121aa3107177350d51882b938086a8c415c5c04354620a6ee8b12a3105347458951882abb9ac4a8c41551cd6254620ae6e0a12a31057070509518829b3a664a8c414d5d33254620ae4e1992a31057170cc9518823a3b264a8c414d9d03254620a6ae8192a310571700c9518823bbb2a228c419998a5190620ccac528c831067151d814188338a88c0a0c419c945601062087ce9b2e631043d74d97318831b324a398c418d59251cc620c6cc8a8e6310635645473188338a8cc198c419c54560cc620ccec528a6310664629453188332312a298c410f9d3650c62087ae9b28631063664944318831ab24a2
  | 14 => 0xcaa8a601873254545300c398aa2a298061d8949514c030ec2a4a8a601875363545300c399a1aa298061cc50d514c030cccc4b0ea99066a6258354c833930ac1aa6414d9c75495320a6ce3b22a99043f7655054c8317324c529e418b5926294f2087ce9b0aa79043d74d8553c822fbb2a629e418d9926114f20c6ac9308a7906366458453c831ab22c229e41999896114f20cc8e4b08a79063a6458053c831cb22c029e419a9896014f20ce4c2b00a7906716158053c823b38ecba1e411d5c765d0f208ece332e87904757199743c829b38ea9a1e414d5c754d0f20a3ae7b2e879053671d9743c829ab8ecba1e414d9c665d0f20a6ae332e879051d7319743c829b388a7a1e414d5c453d0f208ece232c87904757119643c823b38ccaa1e411d5c66550f20a6ce3aa2879053571d5143c831daa0c0a1e413a5c86050f20a3ae732a87905367199543c829ab8ccaa1e4147dcd6550f2087ced29a879043e7614d43c829b388a6a1e414d5c45350f20b48e2b1287905a87058943c831d328c0a1e416a5c86050f20d54c430287904767119443c823ab88ca21e41a358d4390b20b50e0a1c85904e67198242c82373b0a8a1641a3d8d4350b20c74a8b0085905657114e32c827338cc119641391c5644cb209d0e0b22659046e7614d32c82b2b88a699641c314d434cb20cceca30a65906657518532c8333298c2996419914c614cb20d4e8630a65906a54318532c8371380c299641b85c0614cb20cb2a6b00659053674d4651c821f3a4c728e410f5d2639472087ce831aa39043d7418d51c830fb1a86a8e418718d43547208dced192a390564714c951c823bbb2a228e41179cf65d07208bae7b2e83906666254741c8274b94c120e410f9d365cc72087ae9b2e639043e7499631c821eba4cb18e419918a514c720cc8c4a8a639043e74d9431c821eba6ca18e413a9c364887208daed29c439046d7614e21c82b2b88a710e411b5da5308720acae2298439068d6350c21c82b3bb2a210e4199dd95108720ac8e6a8843906676354421c8332b1aa210e41c9d0d5108720e4a86a8843904e576cc421c82b3bae6210e41595d43108720bc2e0188439053671d5240c821f3b4a8a06410f5db5410320a6ce3aa0819061f5458c40c830e2a2c620641a358e4210320a3ae929e61904e47158b30c828eba4a6986419958a61d5220cd2c5306a91067161983548821fbb2a82a441875516315220c3cc8b18a91061e7458c548832731ac42a4419358d6215220cacc7308a910655639845488332b14c22a4419598d6115220caac6b08a910665625845488332b14c3a9c41879ce6494e20c74c9304a71063964982538822fbb2a629c41875915314e20c3ac9318a71062e645885388316b22c429c418d9926114e20c6ac9308a71066562984538831b322c229c418d591
  | 15 => 0x6d75988310c3172a4c4188618b552620c4308deeab10621862e54588310c316aa2c4188611b5da520c430c5cc9290621862d64948310c237bb2a4188618b991520c430c5ac8a90621863664944310c31ab24a2188619998a510c430ccac5288621863664544310c31ab22a21886199989510c430ccac4a88621863a54980310c31caa4c0188619a94a600c430cd2a5300621867151980310c31d2a2c0188618e551600c430cd4a4b00621866952580310c33928ac0188610f9d265c843087ae932e421843e74996210c21eba4cb108610f9d0654843087ae832a421861d54d8d210c30eaa0c69086193d8d5248430ac8e2a92421865763545210c2b2392a2908610f9d2650843087ae9328421856571948210c2b2b94a21086159dd52108430acaea908421866765484210c332b2a4210861c99512108430e4aa890842185c473484210c30eaa4c72006117dd56390030c3aa8b1c801861d5498c400c30f2a2c6200618755163100308daeb310801862e54988400c316aa4c4200611bdd56210030c5ca8b10801862d54588400c236bb4a4200619398e5210030c9ac7290801846f76548400c32731aa4200619358d52100308eaeb308801863654984400c31aaa4c2200619994a6110030ccaa5308801847775584400c31b2a2c2200618d5516110030ccca4b08801866552584400c23abb4a2200619598e5110030caac7288801866662944400c332b14a2200611ddd95110030cacc6a88801865563544400c333312a220061995895110030c72caa00801872952500400c398a8a80200610f5da54cc03087eecaa6601862e6494b300c316b24a598061c350e52cc030c5cc8a96601862d6454b300c386a1aa5980618d99251cc030c6ac928e601871543947300c31b322a3980618d59151cc030e2a86a8e601851f76553300c386aa4a598061c355152cc030e2aa928e601871554547300c3a2a92a398061175da538c0308f2ed29c601853975d0e300c29dbaa8718061ca951528c030e52a8a94601872b4354a300c394a1aa518061d854a518c030e64a8a8c601873154546300c3b1292a318061d8549518c030e6686a8c601873143546300c28ebae869806187d97434c030c3ecaa1a601870d43949300c386a1aa498061c550e514c030e2a86a8a601845e76d51300c28ebaca89806187d96544c030c3ecaaa2601864f65949300c386aa4a49806193d95524c030e1aa8a92601865765945300c38aaa4a29806195d95514c030e2aa8a8a601874552545300c30eaa6c0980618ed96544c030c76caaa260187195494d300c29cbae86980618ed97434c030a76eaa1a601863b6550d300c38d29a86980619ad96524c030cd6caa92601872a54549300c394aa2a498061d2d8d524c030e5686a92601872943549300c339b2ca298061d854a514c030ce6
  | 16 => 0xc31b2a2c2190618d551610c830ccca4b08641866552584320c31d2a4c0190618e552600c830cd2a5300641863a54580320c31caa2c0190619a949600c830c5ca9316a21862d5498b510c3172a2c5a88618b55162d4430c5cc9296a21862d6494b510c317322a5a88618b59152d4430a6ce9a8ca21853574d46510c2b3396a328861595cb5194430acce5aa4a21856572d52510c2b3390a928861595c85494430a6aeba1ca2185377550e510c29b3a6a5288614d5d35294430e4ca9294a2187255494a510c393a1ca528861c950e5294430e4ca8a94a2187255454a510c393a1aa528861c950d5294430a6ce8294a2185357414a510c29b3a0c7288614d5d06394430acce431ca2185657218e510c38bb9a8728861995886294430a6ce9994a21853574cca510c23a3b265288611d5d83294430a6ce8194a218535740ca510c2b938065288615c5c03294430acce5304a21856572982510c23b3b6a8a8861599cb5454430acae5aa2a21847676151510c2b3390a8a8861595c85454430a6aeba1aa2185377550d510c23b3b6a4a88614d9d35254430a6ae9a92a21872654949510c392aa4a4a8861c9d0e5254430e4a87292a21872654549510c392aa2a4a8861c9d0d5254430e4a86a92a21847676149510c29b3a0a4a88614d5d05254430ae0e0b22a2185367498d510c29aba4c6a88615c9c24354430ae2e121aa2187177350d510c2b938086a88615c5c04354430aa8e6b12a21866562189510c2b9b8284a88615c1c14254430a6ce9992a21853574cc9510c2b938664a88615c5c332544308eeec992a218476760c9510c29b3a064a88614d5d03254430ae4e0192a218571700c9510c2b3394c0a8861595ca6054430a6ce8182a218535740c1510c2b339060a8861595c8305443087aed2a0a21843f76550510c3172a4c4288618b5526214430c5ca8b10a21862d54588510c236bb4a4288618b9925214430c5ac9290a21846f76548510c317322a4288618b5915214430c6ca9308a21863554984510c333294c2288619954a61144308eeeca88a21863664544510c31ab22a228861999895114430ccac4a88a21846e72997410c236b94cba08611b9ca65904308dae532c821846e72195410c236b90caa08618e5536050430cd2a5b02821867151d81410c334a90c0a08619c54460504308dce5328821846d72994410c21ebacc9988610fdd564cc43087aed2a6621843f76553310c317324a5988618b59252cc430c5cc8a96621862d6454b310c31b324a3988618d59251cc430c6cc8a8e621863564547310c334a94c1988619a54960cc430ce2a2b06621862e54d89310c316aa6c4988618b950624c430c5aa8312621846c76949310c2373b2a49886199d8a514c430cc8c528a621843d75990310c21fbaac8188610f5da540c43087eecaa062184
  | 17 => 0x82613adc961cc130cccc530ea81866562987540c333312c3aa0619958961d5030cd2c5306a81867161983540c297396a92a0614b5cb5495030a6ce3aa4a81853571d52540c297390c12a0614b5c86095030a6ce2304a81853571182540c297396c8aa0614b5cb6455030a6ce3b22a81853571d91540c29c382c4aa0614e1c16155030a5ce4302a81852d72181540c29b388c0aa0614d5c4605503087eecaa0a81862d54988540c316aa2c42a0618d5526115030c6aa8b08a81862e64988540c32731cc42a0618b9916215030c9cc6b10a81863664984540c32b31cc22a0619998a6115030ccac5308a81863664584540c32b31ac22a061999896115030ccac4b08a81866962980540c338b0cc02a061879ce6494c30a5ce5aa6861852d72d53430c29b38ea9a18614d5c754d0c30a5ce42a6861852d72153430c29b388a9a18614d5c454d0c30c72a8b04861851e73d51430c297396a8a18614b5cb5450c30a6ce3aa2861853571d51430c21f3b0a8a1861479cc5450c30a5ce42a2861852d72151430c29b388a8a18614d5c45450c30a3ce929a861851f73d95430c28f3b4a6a18610fdd95410c30c74a8b00861863654987520c31aaa4c3a90618d95161d4830c6aa8b0ea41852e74d4a520c296ba6a529061599c75294830acae3a94a41856671d52520c2b2b8ea929061599c45494830acae22a4a41852d75d0e520c297baa87290614b9d06394830a5ae831ca4185667118e520c2b2b88c729061c3dcd4394830ccac230ca41856671982520c2b2b8cc1290611b9db5454830acce3aa2a41856571d51520c2373b0a8a9061599c45454830acae22a2a41852d75d0d520c297baa86a90615a1c16454830a5ce931aa41852d7498d520c2b538486a90615a5c24354830e1ee6a1aa41856a7010d520c2b4b8086a9061531cd6154830ccac230aa41856671981520c2b2b8cc0a90614b9d03054830a5ae8182a41843d76950520c21fbb2a8290618b9526214830c5aa9310a41846f76548520c317322a4290618b5915214830c6ca9308a41863554984520c332a94c2290618d9516114830c6aa8b08a41866552584520c23b38ccba10611d5c665d08308ece332c841847571996420c23b388caa10611d5c46550830c72a9b02841866952d81420c334a90c0a10611d9c665108308eae3328841843d75993320c21fbaac9990610f5da54cc83087eecaa6641862e6494b320c316b24a5990618b99152cc830c5ac8a96641866952583320c31b2a6c2990618d553614c830ccca5b0a641863654185320c31aaa0c29906199948614c83087aeb320641843f75590320c21ebb4a8190610fdd9540c830c5cc9290641862d64948320c317322a4190618b591520c8308eaeb308641863654984320c31aaa4c2190619994a610c830ccaa5308641847775584320
  | 18 => 0x550d30a3ae1b2a869871970d95434c28f3acc4a1a61871966250d30b34e1312869859970989434c28e3aac4a1a6165dc56250d30b28e2b12869859b70589434c2cc382c4a1a61871946250d30b34e0312869859970189434c28f3acc2a1a61871966150d30b34e130a869859970985434c28e3aac2a1a6163dc96150d30b18e4b0a869859b70585434c2cc382c2a1a61871946150d30b34e030a869859970185434c30e32ec0a1a61a61976050d30b32e5b02869859971d81434c28f3acc0a1a61669c26050d30d36c1302869858f72581434c2c6392c0a1a6165dc56050d30b28e2b02869851e75181434c2c7390c0a1a61635c86050d30b2ce2302869859571181434c2cd3b0c0a1a61a69d86050d30b34ea302869871a75181434c3c5390c0a1a61665c86050d30f12e4302869858972181434c3c9388c0a1a61665c46050d30f22e2302869859171181434c34aa1ec2a9261a550c61549308deeca90a49852c74548524c386a1aa429261591c55214930a38eaa1c849861d6550e424c34ca1cc1212613c5c66090930d3286b04849861f6550d424c23bb8aca212611d1c565109308ece2328849847571194424c28e3aa86212619358c5210930d3287300849863854580424c34ca1ac021261a650e608c9309e2e3304649869943582324c386a18a499261a550f614c930d2a8630a649866752185324c332290c299261a650f604c930d2a87308649869543584324c34ca1cc019261a350f6254530d1a86312a29847776544514c29a3a2a228a61c550d5114530ac8e4a88a29851c7550e414c30eb2a8720a61a650e60905309d2e5304829869943582414c30fb2a86a0a611bdc965105308d8e4b28829846e72194414c236b90ca20a61471d54310530caac6288829869943980414c31c2a2c020a61a650d6010530d328730462984e972982314c34ca1ac118a61a350f624c530d1a86312629866462d45314c38aa18a298a6199188514c530d3287b02629868d43988314c346a1ac418a61a650e600c530d3287306429869943583214c34ca1cc110a61a650d6088530c3ecaa1a429861c6550d214c21fba2ca10a610f1d1650853087ce8328429843d74194214c24eba4c610a61879954308530c3acaa18429856571148214c2b2b90a210a61599d52108530ac8ea90842986c563484214c3c2a1a4210a61a650e6008530d3286b00429866852580214c33828ac010a61471d543d0130a58e4aa4809853471552404c30f32a87202610f9d85450130a38eaa1a809861f6550d404c2cc38286a02614e5c2541013087eecaa0809852c72550404c29a38aa820261879516310130c3aa8b18809861e6550c404c346a1cc420261a350d6210130d2a87308809869543584404c2cdbb28798261a6dd943cc130d3286b1660984f37158b304c34ca1ac39
  | 19 => 0xcaa0639862e5498831cc316aa4c418e61a350e620c730c5ca8b10639862d5458831cc346a1ac418e619958a510c730e2a86a8863985647254431cc332b12a218e618e952600c730c72a9300639863a5458031cc31caa2c018e61a650d600c730ce2a2b00639843e7499721cc21eba4cb90e61591c552c873087ce932c439843d7499621cc2b2392a310e610f9d0654873087ae832a439861f6550d21cc30e32a8690e61591c55248730ac8e4a8a439843e7499421cc21eba4ca10e61275d26308730c3aa9318439861d5458c21cc30f32a8610e61875954308730ac8ea90843986676548421cc332b2a4210e61c99512108730e4aa890843986c56348421cc3c2a1a4210e618795163d0330c3aa9b1a81985987050d40cc30eaa4c620661879516310330c3aa8b18819862e5498840cc316aa4c420661a350e6210330c5ca8b10819862d5458840cc346a1ac4206618d9526110330c6aa930881986954398440cc31b2a2c2206618d5516110330d2a86b0881986996350040cc21fbb2a82a4619358e6215230c9ac6b10a91865563984548c333314c22a4619958a6115230caac6b08a91866662584548c332b12c22a4618e5506050e309d2e430287184f171181438c297390caa1c614b5c86550e30a6ce232a871853571195438c2d4b90c0a1c616c5c46050e30acce3a94a51862d72191528c21f3b686a94610f1d94354a308deeca90a51847671d96428c23ab8ecb214611d9c66590a308eae332c851852d72152428c2963a2a5214613c5c66090a30c70a8b0085184f171982328c333290c29946199548614ca30acce5a8ca31863571191518c21f3b686a8c610f1d943546308eeeca88a31846e72d96418c236b96cb20c611b9ca65906308dae532c831853571152418c29a3a2a320c613a5ca6090630c70a8b0083184e972982318c332314a298c6199189514c63087ce9b2e431843d74d97218c338a8cc190c610f9d3658863087ae9b2c431866952982218c21fba2ca90c610f1d165486309b2e031a431843f74594218c21e3a2ca10c61595c65208630acae5288431856775484218c2b2baa4210c61711cd210863087cec2a2811843f76550408c30f2a2c620461875516310230c3acb326611861d65593308c31cb2cc9984618e59564cc2309e6e2b1661184eb72587308c317b20c4aa26199d8b6155130cc8c5b0aa89863764185544c333b10c2aa261991886155130cd0c5b02a89867061d81544c21fbb2a82a2614b1c95415130a68e2aa0a89863854583434c28eb9ecba1a614bdc965d0d30a58e4b2e869853771597434c29a38acba1a618e19560d0d309d2e430286984f171181434c28fb9acaa1a61479d76350d30c38cbb1a869863965181434c2d4b90c0a1a616c5c46050d308bcec2a286985c972181434c2e8b88c0a1a61665c36
  | 20 => 0xe7318a54cc28f39ec32a6614b9cb6195330a5ae5b0ca99851e7318654cc297394c6aa6614b5ca6355330a6ce331aa9985357198d54cc29bb8ac4aa6614d1c56255330a76e0b12a99852f7258554cc296392c2aa6614edc16155330a5ee4b02a99852c7258154cc29bb8ac0aa6614d1c5605533087eecaa0a9986395498243cc21f3b0a8a1e61665c35450f30c3ecaaa2879845e7615143cc24f3b0a8a1e61475d66250f30a3eeab1287985977158943cc2ca38ac4a1e6166dc16250f30b30e0b12879851d7598543cc28fbaac2a1e6163dc96150f30b18e4b0a879859b7058543cc2cc382c2a1e6187d976050f30c3ecab02879858f7258143cc2c6392c0a1e6165dc56050f30b28e2b02879858e7218143cc2c6b90c0a1e61659c46050f30b2ae230287986996018143cc21fbb2a821e618e9526010f30d3286b00879849f7650f52cc31b2a6c2a96618d5536154b30d2a87b0aa5986365418552cc31aaa0c2a9661a550c6154b30c6e87b0aa59863543d8552cc31ba18c2a96618d50c6154b3087aed2a0a59843f7655052cc24fbb286296611bdd95214b30e1a86a90a5985647154852cc31b2a4c2296618d5526114b30d2a87308a5986365458452cc31aaa2c229661a550d6114b30ccaa4b08a59847671d9742cc23ab8ecba16618795163d0b30c3acaa1c85984777159542cc23a38acaa166187d954350b30d3287b0285986395418142cc30f2a2c6216610f5d664ccb3087eeab26659843d7695332cc21fbb2a999661591c552ccb30d3286b06659863654d8532cc31aaa6c299661a550f614cb30c6ca830a65986355418532cc34aa18c2996610f5d6640cb3087eeab20659843d7695032cc21fbb2a819661c350d520cb30ac8e2a9065986365498432cc31aaa4c219661a550e610cb30c6ca8b0865986355458432cc34aa1ac21966199949610cb30ccaa4b08659863a5498032cc31caa4c0196618e951600cb30c72a8b0065986994358032cc334a92c01966127dd943d4730c5ca9b12a39862d54d8951cc346a1ec4a8e618b9506254730c5aa8312a39868d4318951cc317a1ec4a8e618b50f6254730c5e86312a39862d4318951cc21ebb4a828e610fdd9541473093eeca18a39862e5498851cc316aa4c428e61a350e6214730c5ca8b10a39862d5458851cc346a1ac428e611ddd95114730e2a86a88a3985647254451cc332b12a228e611b9cb65d07308dae5b2e839861e5458f41cc30eb2a8720e611bdc965507308d8e4b2a839861f6550d41cc34ca1ec0a0e618e5506050730c3ca8b18839843d7599331cc21fbaac998e610f5da54cc73087eecaa663985647254731cc34ca1ac198e618b953624c730c5aa9b12639868d43d8931cc3172a0c498e618b550624c730d1a86312639843d7599031cc21fbaac818e610f5da540c73087ee
  | 21 => 0x237394cb188811b5ca658c440972e0324622061c6454e311031bb22a3188811bdc9654c4408d8e4b2a622046e721953110236b90ca9888187d91534c440c38c8a9a622046d75d89311032729ec4988819354f624c4408daea312622064e531893110326a98c4988811b9da524c4408d8ed292622046e7654931102363b2a49888199d8a514c440cc8c528a6220637645453110333b12a29888199189514c440cb2a7b02622067151d813110237396ca188811b5cb650c4408dce5328622046d72994311030eb24a61888187991530c440c3ac8a98622046d75988311032729cc4188819354e620c4408deeab10622064e535883110326a9ac4188811bdda520c4408daed290622062e649483110316b24a4188811bdd9520c4408daeca90622062e645483110316b22a4188818d992510c440c6ac92886220666629443110332b14a2188818d991510c440c6ac8a886220666625443110332b12a2188819654e600c440cd4a53006220669529803110338a8cc0188819694d600c440cb2a6b00622066a525803110334a92c0188819c945600c440ce2a2b00622045e73997211022eb9ccb908818799153c8440c3ac8a9e422062d6494b211031b322a3908818d59151c8440cb2a7306422067151983211032ca9ac1908819a94960c8440ce2a2b06422045e73996211022eb9ccb10881879915388440c3ac8a9c422062e6454a2110316b22a5108818d5925188440cb2a7304422066952982211032ca9ac1108819a5496088440ce4a2b04422045e73195211022eb98ca908812e5c06448440c3ec8a9a422061c6454d2110317b22a490881591c55248440c6ec8a8a422056472545211022f39cca10881175ce650844087aebb20422049d73190211025cb80c81088187d915308440c38c8a9842205657194821102b2b94a21088159dd52108440acaea9084220667654842110332b2a4210881d194d2108440e8aa6908422061d6354f401030ea9cc5a0081c354e52d0040e1aa6a96802061d53987401038aa9ca3a0081c554d51d0040e4aa4a8e802043d76952401023cbb4a920081d254d5290040ea2a6a8c802076152546401021eb9ecaa008187d96535004087ceca9a802061f6354d401030fb2aa6a0081879d95350040e30e0a9a802061d531894010317b2ca4a0081c354e5250040c5ecaa92802070d53549401030ea98c2a00818dd965150040e2aa728a802063765545401038aa9aa2a0081c95495150040cb6cb29a802065b6554d401038d2a2a6a00814e5d64350040974ec21a802066b659494010335b2aa4a0081d254d5250040974eda128020673659454010339b2aa2a0081d454d5150040ec2a4a8a80204ba76d054010297390c72a6614b5c86395330a6ce231ca9985357118e54cc28f39ec52a6614d9c76295330a6ae3b14a99851
  | 22 => 0x8811ddd932944408e8ec994a220476760ca511023abb065288814d9d03294440a6ae8194a220572700ca51102b8b806528881599ca6094440acae5304a22046e7218d5110236b90c6a88814d9c743544408eceda9aa22056672d4d51102b2b96a6a8881c59d25354440e28c929aa2207167454d511038a322a6a88811d9d85354440acce429aa2205657214d511038aa9e86a88816c5c34354440e2ca6a1aa2207155350d511023b3b6a4a8881559cf5254440aaae7a92a2207465394951103a2a9ca4a8881c91925254440e4e87292a2207254394951103a329aa4a8881d154d5254440e48e8a92a220724645495110393a1aa4a8881c950d52544408ecec292a2205567314951102aab98a4a88814d5d64254440e2aa7212a22072552909511038aa9884a8881c95484254440b62e0212a2205367498d511029a3a2c6a888159dc96354440ac8e4b1aa2205707058d511029b3a0c6a8881599c86354440acae431aa2205727018d511029b3b686a88814d1d94354440e2ee6a1aa2205727010d51102b8b8086a88814d9d26254440ae4e1312a220534745895110332b10c4a88815c9c04254440ae2e0212a22053674cc9511029aba664a88811ddd932544408e8ec992a220476760c9511023abb064a88814d9d03254440a6ae8192a220572700c951102b8b8064a8881599ca6054440acae5302a2205567310151102aab9880a8881599c84054440acae4202a22045d7694c511022fbb2a6288819394e6214440c9aa7310a22064e535885110326a9ac4288811b5da5214440c9cc7290a22064d639485110237bb2a4288819398d5214440c9ac6a90a22065653984511032aa9cc2288819994a6114440ccaa5308a22047776544511032b31aa2288819558d5114440cccc4a88a220665625445110338a8ac1a08812edc16390440c3ac6a9c822061d6554e411030ebb2a7208818754e6290440972e1314822070d5394a4110316b2aa520881c354d5290440c6acb28c822071553946411038b29aa320881c554d5190440e4ca4a8c822072552546411031ab1aa3208818754d6090440cb2a7300822066952980411032ca9ac0208819a5496010440ce4a2b00822061d6354c411030f3b2a620881875d95310440c3aa7310822070d539484110386a9aa420881c554e6110440e2aa72888220715535444110392a92a220881c654e6010440c3aa6b00822071953580411025dbaac0208818edd56010440d34a6b00822063953580411034ca9ac0208818654d6010440d54a4b0082206a952580411035928ac020881ac54560104408dce532e622046d72997311025cb84c9988818759253cc440c3cc8a9e622061d6454f3110317324a5988818b59252cc440c5cc8a96622062d6454b311031b324a3988818d59251cc440c6cc8a8e6220635645473110
  | 23 => 0x54840acce3302a4205657198152102a739880a9081535cc40548408baed298a42045f7654c521032729cc4290819354e62148408deeca90a42064e635485210326b1aa4290819594e6114840caaa7308a42066552984521032b29ac2290819554d6114840ccaa4b08a42066952583421025db82c7210818758d5390840c3acaa9c842061d7654e4210316b2ca521081c354e5290840e1ca6a94842070d5354a4210316b1aa5210818754e6190840972e130c842061d53582421032ca9cc0210819654d6010840cd4a4b00842061d6354c421030f3b2a621081875d95310840e1aa7310842070d539484210386a9aa4210818754e6110840e32a7300842061d53580421038ca9ac0210812edd56010840c76eab00842069a53580421031ca9ac021081a654d6010840c32a6b0084206aa525804210354a92c0210811d9c665cc8408eae332e64204b970993321030eb24a7990818799153cc840c3ac8a9e642062e6494b3210316b24a5990818b99152cc840c5ac8a96642047671996321023ab8ccb190812e5c0648c840c38c8a9c642062f6454a321023bb8aca990811d1c5654c8408ece232a642047571195321030fb22a69908187191534c840c5ec8a92642047575d85321032b29ec2990819554f614c840ccca5b0a642066552d85321023aba8c2990819594c614c840caaa630a6420666521853210332a90c2990819654f604c840cd2a5b02642047671d94321023ab8eca190811d9c6650c8408eae3328642061d6494c321030f322a61908187591530c840c5cc9290642062d649483210317322a4190818b591520c8408eaeb308642065653984321032aa9cc2190819994a610c840ccaa5308642047775584321032b29ac2190819554d610c840ccca4b08642066552584321032ca9cc0190819a54a600c840cb4a6b006420659535803210335292c0190819a549600c840c9ca7316a22064d5398b511032729ac5a88819354d62d4440c9cc7296a22064d6394b511032731aa5a88819358d52d4440aace7a8ca22055573d4651102b3396a328881595cb51944408dee4b1ca22046c7258e51102b3396a728881595cb5394440e2ce929ca2207167454e511038a322a728881599c85394440acae429ca22071553d0e51102d8b868728881c594d4394440e2aa6a1ca22055673d4a51102aab9ea528881d194e5294440e8aa7294a2207274394a5110392a1ca528881d194d5294440e8aa6a94a2207247454a5110393a1aa528881c950d5294440aace6294a2205557314a511038aa9c8528881c954a4294440e2aa6214a2205b17010a511029b3a4c72888159dc96394440ac8e4b1ca2205367418e51102b3390c728881595c86394440ae4e031ca2207177350e511029b3a6c5288815c9c36294440ccac4314a22053674cca511029aba66528
  | 24 => 0xb18a2a05387050c5150237b92cb98a811b1c965cc540970e0b2662a0635641473150237394ca98a811b5ca654c5408dce432862a046d72194315031ab26a218a819958b510c540ccac428862a067351580315033828ac018a81599c75248540acce5a8a42a045e73194215022eb98ca10a810f9d66408540cccca90842a066465484215030eb1ea720281539cb5394c40a9ae5a9ca62055671d4e53102aab8ea7298811ddc56294c408e8e2b14a62046f725865310236392c329881479d36294c40aaee2b14a6205547158a531028f3a0c529881559c46294c40aaae2314a62055a7018a531028f3a6c32988153dc96194c40a98e4b0ca62051e7418653102a7390c329881535c86194c40ab4e030ca62054e7218253102a6b90c129881559c46094c40aaae2304a62047671189531023ab88c4a98811b9c86154c408dae430aa62051e72991531028f38cc8a9881c65c26454c40a3ce9b12a62051c7458953102abb8ac4a9881551c56254c40ab0e0b12a62051e7418953102ab388c4a9881555c46254c40ab4e0312a62051e74d85531028e3a2c2a988153dc96154c40a98e4b0aa62055870585531028f3a0c2a9881539c86154c40a9ae430aa62055a7018553102a7390c0a9881535c86054c40aace2302a62055571181531022fbb2a6298819354e6214c40c9aa6b10a62065553984531032aa9ac2298819654d60d0c40c3aa7316862061d53987431038ca9cc1a18818754d60d0c40e32a6b0686204bb75583431031dbaac1a1881a694d60d0c40c72a6b06862069953583431030ca9ac1a188187d955350c40972e031286204b970185431032d29ac0218819594e61d4840caaa730ea42065653587521032aa9ac3a9081539cf5294840a9ae7a94a42056671d4a52102b2b8ea5290811ddc563948408e8e2b1ca42056671d4e52102b2b8ea729081c39d25394840e1ce8a9ca42070c6454e52102b3388a729081595c45394840e1aa7a1ca4205a970d0e521038729a8729081c354d4394840a5ce931ca4205677158e52102b238ac7290814b9d06394840acce231ca4205657118e52102b5380c729081c3dcd4394840a5ce9b0ca42056a70d865210332b08c329081599c66094840acae3304a4204767118d521023ab88c6a90814b9cb43548408dceda9aa42056671d4d52102b2b8ea6a9081c39d25354840e18c929aa42070e7454d5210386322a6a90811b9d85354840acce229aa4205657114d5210386a9e86a90816a5c34354840e1ca6a1aa42070d5350d52102973a4c6a90814b1d16354840acee2b1aa4205647158d52102b4382c6a90814b9d06354840acce231aa4205657118d52102b5380c6a90814b9db4354840a58eca1aa42070f7350d52102b538086a90815a5c04354840a5ce930aa42056a7098552102963a2c2a90819958461
  | 25 => 0x6350d210875331a8690843a918d4348421f08c6a1a4210e846350d2108793a9a8690843e194d4348421e4aa6a1a4210f855350d2108782a9a8690843599d44348421acaea21a4210da67410d210867339ec09084399d4f6048421ccaa7b024210ea743d812108752a1ec090843595d66048421aceeab024210da77458121086d23a2c09084371dcd6048421b88e6b024210ce7764875008673bb2432804378dc1219402187ce931ca010c3d7498e500870f31a87280438758d439402193ae6322a010ce7764855008753b2242a8043a91912154021bc6e090aa010c3d73d91500862f398c8a8043175cc6454021a3ae6322a010e1e73191500861eb98c8a8043875cc645402183ae6322a010e2e721915008716b90c8a80438d9c46454021c6ae2322a010e3970191500861f3a0c6a80430f5d0635402187ceda1aa010c3c76d0d500861f3b286a80430f1d943540219ceec908a010ea6644845008752b224228043b198d2114021d8ac6908a010c7b76540500871cb22a0280439658d5014021ec242a80a010c5f7654c53d038ca9cc1a1e81c654d60d0f40b32e1a9a87a049e7614d43d034ca1ac021e818758d4394b40c3ec6a1aa5a046f7654852d023bb8aca996811d1c5654cb408ece3b2865a047571d9432d030eb1a8728e8187d8d43547408eeeca88a3a046f7259531d0236392ca98e811b9cb650c7408dae5b2863a04777158a539023a38ac529c811bdc96194e408d8e4b0ca72052c72591539029a38ac8a9c8117dd95314e40a3ced29a872061e7694d439038ca9ec0a1c81c654c6050e40acce3a94a5204767118d529023ab88c6a94811bdd95214a40c3ac6a98852047671996329023ab8ccb194811ddc5654ca408e8e2b2a6520666521853290332a90c2994811d9c7650ca408eae3b28652056672d465190237390c6a8c811b5c863546408eeeca88a32061d6354c4190237394cb18c811b5ca658c6408dee4b2a632046c725953190332314a298c8199189514c6408dce5b28632046d72d94319022fb9aca90c81171cd654864093ae632043204b97019021902b2b8ca410c81595ca5108640aceea908432056575484219025c3a2c010c818758d53d02408ece3316a6a04757198b5350237394c3a9a811b5ca61d4d408beeca98a6a071b53d81435038da98c0a1a812e9d46050d40c74ea30286a063b531814350355390c0a1a81aa5c86050d40d64e230286a06b171181435030f32a8621a8199d4961949408deeca90a4a04777158c525023a38ac6292814e1c143149408eee2b2e64a047471597325025c382c9992818b59052cc9408ece332a64a047571995325023b388ca192811d5c4650c940c5ac9a9064a0667525843250332292c2192819ad49600c940cd0a4b0064a066562d46515023bbb2a228a811bdc963145408d8e4
  | 26 => 0xc2a186418843785c0320c421ce2cb3006210ee1629803108738b2ac018843ac991600c421d62c8b006210ee2625803108770b12c0188439cd4d600c421da4a6b006210e71535803108768a9ac018843acd0d600c421d6286b006210ee2725803108770b92c018843b8cc9600c421dc064b006210ce97018f2108637bb2a7908439398d53c8421e1aa6a1e4210ec663cc721086b2ba86390843785c031c84218daed2944210cf17018e210863bbb2a7108439598d5388421e2aa6a1c4210c757694a210876331e6510843595d43288421bc2e01944210c6d7598d2108674b80c6908431b9db53484218d8eca9a4210e4c6354d2108717b2e86908438bd954348421d18c6a1a4210f0d5350d21086b2bae6290843699d33148421b4ae998a4210ec463cc521086733b46290843d154e31484219c8ec98a4210d65750c521086d33a06290843695d03148421bc4e018a4210de1700c5210863abacc6908433c5c063484218eceda9a4210c747654d210872a31aa6908438dd974348421c6ecaa1a4210e946350d210878aa9a8690843595d73248421b4ce99924210da574cc9210876231e6490843399da3248421e8aa71924210ce4764c921086b2ba86490843699d03248421b4ae81924210de2700c921086f0b806490843995d765484219cce7b2a4210ce570d9521087333b6ca90843595cf6548421acaeb3224210dc67399121086e2b9cc89084359dd564484219ccedaa24210ce6761512108792aa0a890843719cc5448421b8ae62a24210de27015121086f0b80a890843595d66348421b4ce931a4210da57498d2108672bacc690843995d66348421d4ce931a4210ea57498d210867339cc690843395c26348421aceeab1a4210da67418d21086d2ba0c690843789c06348421bc2e031a4210e657518d21087533a0c690843a95d06348421d8ce631a4210ee27018d2108672b80c690843b85c063484219c2e031a4210ce676d4d21086b33b6a690843999db5348421cccc7a9a4210e6463d4d21086723b4a690843595d65348421b4ce929a4210da57494d210876231ca69084339dd953484219c8eca9a4210ec46354d21086b33b2a690843591d95348421cc8eca9a4210c647654d21087a3b9aa690843d1d8d5348421cccc6a9a4210e646354d21087a231aa690843399d85348421accea29a4210da67414d21086d2ba0a690843789c05348421bc2e029a4210ce676d0d2108672bb68690843a99db4348421d4aeda1a4210ea765d0d2108793b2e8690843a998f4348421d48c7a1a4210f2753d0d2108792a9e8690843599d64348421acaeb21a4210da57490d210876231c8690843d154e43484219ceeca1a4210ce47650d210876231a8690843d154d4348421d4eeca1a4210ea47650d2108753b2a8690843c9d954348421f0ee6a1a4210f87
  | 27 => 0x43479cc5450c21a74e02a28610d3970151430868f3a4a6a18431b5d46250c21c5aa83128610ce571189430863aba8c2a18438d5506150c219cae430a8610d1d73995430868fb9acaa18434edc16550c21a70e0b2a8610d3a70195430869cb80caa1843475d76350c2187ced29a8610d1d7594d430868f3b4a6a1843879da5350c21a3ae129a8610d1e7654d430868e3b2a6a1843c31c95350c21e28e2a9a8610d1f7054d430861f3b0a6a1843479cc5350c21a5ce429a8610d367114d430869d380a6a18434e5c05350c21e1aa7b128610d2d751894308716b28c4a1843c354c6250c21b4ae23128610f1553d85430869aba8c2a18438d5946150c21e2aa630a8610da572185430861f3a6ca218431b9c86510c218ece23288610c7a70194430863cb80ca218430f9d2639482187ae931ca410e3554986420873238acb990438b59664cc821c5acab266410e2d65d0f3208716b2a8799043c354d43cc821acaebb0e6410e6565d873208753326c399043a959361cc821bc2e030e6410ce771583320863bbaac3190430f9d3650c82187ae9b286410e1d6494c320870eb22a6190439554e610c821cb4a6b006410e59535803208716b2cc8190438b595640c8218deeca986410cad76d0c3208716b2e86190432bdd9430c821c5acaa186410f0d5350c3208732b2cc2190431bdd5610c821ccacab086410ea6645843208752b22c21904339dd5610c821cceeab086410e67535843208732a9ac219043a9d0d610c821d4a86b086410ce7705843208734b2cc019043b8586600c821cd2cab006410eaa645803208754b22c019043b8985600c821dc2c2b006410e6b53580320876529ac0190439a54d600c821d92a6b006410eab435803208754a1ac019043b89c5600c821dc2e2b006410c3e7498e510861eba4c7288431b5d83294421acae2194a210e2d5498a410862f398ca20843175cc6510421cc8e4b2e6210e3565993310871ab2ac9988438d59743cc421c6acaa1e6210f155350f31086b2baec5988439959762cc421d4cc9b166210ea564d8b31086f0b80c598843595d732cc421ccacb9966210f8543ccb31086b2ba865988439959432cc421bc2e01966210ce7725833108637baac5188430f9d3650c42187ae9b286210c3e74194310861eba0ca1884387592530c421c3ac8a986210e4d53988310872d29ac0188439654d600c421c6acb3206210e3565590310863bbb2a6188432d5db430c421c6acba186210cb77650c310871ab2a8618843c554d430c421ccacb3106210c77755883108732b2ac418843a9991620c421d4ac8b106210ce7755883108733baac41884399d4d620c421ccaa6b106210ea7435883108752a1ac41884339dc1620c4218eaed2906210e656294831086b2bae641884399597320c421acaea1906210e65650c831087
  | 28 => 0xd21a6ee2a9a8690c3e7614d434869d380a6a1a434e5c05350d21a3cea29a8690d997014d434868f3b0a6a1a43879d85350d21e1ae429a8690f157114d434878d380a6a1a43475c05350d21e32e029a8690d197014d434861f3a0ca21a431e9c06510d218f2e03288690c6c75588434867238ac421a431d1d56110d219c8e4b088690e1d64d4f324870eb20a799243995c6658c921ad2e029c6490e2e65d0e324871732a8719243c314d438c921accea30c6490e6665186324872a29ec2992431b9d8534c921ad2e029a6490e2c65d0d324871632a8699243c314d434c921cc8cbb0a6490ce67518532487333a8c2992439994c614c921cc8a630a6490ea7431853248752a18c299243179cf65505218bae7b2a8290e1d64d4f314870eb20a798a43995ca658c521ae2e029c6290e3665d0e314871b32a8718a43c514d438c521accea3146290e666518a31486b33ac6518a4399996328c521f0a871946290d64754ca314873332a6518a430f9d3654c52187ae9b2a6290e4c53d89314863b3b0a698a435c5c0534c521c68cba1a6290e346550d314878a29a8698a4399197624c5219ccea3126290e66751893148733298c498a439914c624c521d4e863126290ea54318931486b33ac6498a4399196324c521ac8ea9926290e64654c931487c2a1a6498a439558c53c8521ae2e029e4290f145350f2148762b1c6590a439358c5388521ad2e029c4290f0c5350e2148762b1c6310a43179ce64d41218bae7326a090c3e7498f504861eba4c7a8243591c532d4121ac8e498ea090c7b76540504861f3a4c6282430f5d26314121c3cc6a18a090e1d6350c504862f398c0aa043175cc605502187eecaa0a810e1d5458c540871caa2c02a043879916315021c3ce8b18a810e4d63988540872ab1cc22a0439698e6015021cb2c7300a810e3a64580540872d31ac02a0439658d6015021cd4c4b00a810e7261580540861fba2c1a98430f1d160d4c21c3ce7324a610e6462185530861f3a0c0a98430f5d06054c218beeca98a610e1d6454c530872ca9ac029843875926314c21c5cc9310a610e2d64988530871b324c2298438d5926114c21c74c9300a610e39649805308735314c0298439c9866014c21c74c8b00a610e3964580530872d31ac0298439a9896014c21ce4c2b00a610c7a70197430863cb80cba18434e9c054d0c21a72e02a68610c6d7598b4308672b8cc5a18431d5d661d0c219cae530e8610d1d73d97430868eb98cba18434e9c065d0c21a72e032e8610d2e7214f430869b388a7a18434e9c053d0c21a72e029e8610d2d7598b43086d2b8cc5a18434d5d661d0c21b4ae530e8610c6e72196430863b388cb218431e9c06590c218f2e032c8610c7b70595430863c382caa18431e9c06550c218f2e032a8610c3e76d51430868f39ea8a18
  | 29 => 0x8a910e6562987538871b324c329c438d5926194e2187ce9b02a710c3d74d81538862fbb2a629c438b9916214e21c5ac8b10a710e6562984538871d324c029c438e5926014e21cd2c5300a710e3a64580538871cb22c029c439a5896014e21ce4c2b00a710c7a70997438863cb84cba1c434e9c354d0e21a72e1aa68710e2e5458b438868eb9ecba1c434e9c265d0e21a72e132e8710d1d73197438869d380a7a1c434e5c053d0e21c5ecab168710c7a70196438863cb80cb21c431e9c26550e218f2e132a8710d3a70d51438869cb86a8a1c43475ce6550e21a74e132a8710d3970995438868fb9acaa1c430f9da5350e2187cec29a8710d3a7014d438869cb80a6a1c431e9c06510e218f2e03288710e2d659933288716b2ac9994439594c614ca21c5acb3206510e2d655903288636bb6a6194432b5db430ca2195eeca186510f0f5350c3288732b2cc219443a9991610ca21d4ac8b086510e67535843288732a9ac219443a9d0d610ca21d4a86b086510e69659803288770b0cc0194439a595600ca21d54c8b006510ea964580328877130ac019443b8585600ca21cd6a6b006510e69535803288755a1ac019443aa50d600ca21c5ca8b108310d717014e31887c2a186518c43785c0328c6218ecec29a6310d717014d318878a29a8698c4399d97624c621ccca63126310e64531893188753a18c498c43a950c624c6219cced9926310f8543cc931886733b06498c43785c0324c621c9aa6b106310ce97018f2188637bb2a790c439398d53c86218eaed29e4310e556394f21886b8b80a790c434e9d3509422187ce931ca110c3d7498e508870f31a87284438758d439422187ce831aa110c3d7418d50886b239262a84431edd95014221c3ea8b1ca890e1e7458e544872731ac52a2439598d619512187eecaa0a890d1d73990544861fba2c1a9a430f1d160d4d21c3ac9a9ca690c5f7654c534870f39cc829a43475d26314d21c5cc8b10a690e2d64588534871b322c229a438d5916114d21ccac4b08a690e3a64980534871cb24c029a439a58a6014d21ce2c3300a690e3a64580534871cb22c029a439a5896014d21ce2c2b00a690c6d72d97434863ab8ecba1a43475cf65d0d21a5ae5b2e8690d3571d97434868eb98cba1a434bdc953d0d21a6ee2a9e8690d3a7014f434869cb80a7a1a431e9c06590d218f2e032c8690d597014e43486363aac521a43391c56290d218e8eab0c8690ce4725864348637b92caa1a431ddc56550d218f6e0b2a8690c7870595434868f39ca8a1a430f1d95450d21a38e6aa28690d1e7414d43486acb80a6a1a43475ce6550d21a3ee6b2a8690d2f72595434869bb8acaa1a434edc16550d21a70e0b2a8690d1e75d8d434868f3b6a6a1a43471db5350d21a3ae1a9a8690c3e7694d434868f39ca6a1a434bdc9535
  | 30 => 0x1cc9500c78ca1c64a80635cdc532540318f4ec192a018d3a740c9500c69cba064a8063c650c3254031ae4e2192a018d71710c9500c6ad39882a8063565cc4154031a74e998aa018d3974cc5500c78ca1e62a8063ccd0e3154031e628718aa018d72728c5500c78ca1a62a80635adc93154031ad0e498aa018f53734c5500c799a1a62a8063d490d3154031e628698aa018f51434c5500c788a1a62a8063d8dc93154031ae0e498aa018f60724c5500c6b039262a80634e9d03154031a72e818aa018d6a720c5500c6b4b9062a80630f5da541403187eecaa0a018e2e54988500c716aa4c4280638b9516214031c5aa8b10a018c6d76948500c717324a4280638b59252140318deeca90a018e2e64548500c716b22a4280638e9526014031c72a9300a018e6a52980500c734a94c0280631edd95014031c74c8a80a018e3964540500c735312a0280639a5895014031cccc4b0ea990e716198354c8738b8cc1aa6439a98960d5321a74e1aa4a990d3a70d9154c861fbb2a82a643999896115321cccc4b0ea790e2e6498a53c8716b24c529e430f9d36054f2187ae9b02a790c5f7654c53c871b322c229e438d5916114f21cccc4b08a790e3a6498053c871cb24c029e439c5866014f21c74c8b00a790e396458053c8735312c029e439c5856014f218f4e132e8790c797099743c869d386a9a1e434e5c354d0f21c6ca8b0e8790d1d73d9743c869d384cba1e434e5c265d0f21a3ae632e8790d3a7014f43c869cb80a7a1e438dd9561d0f218f4e032c8790c797019643c863d384caa1e431e5c26550f21a74e1aa28790d3970d5143c868eb9ccaa1e434e9c26550f21a72e132a8790d1f7359543c861f3b4a6a1e430f9d85350f21a74e029a8790d397014d43c863d380ca21e431e5c06510f21c6ca8b088590d697014e32c86373b0a6996435a5c0534cb21e18a6a1a6590e6765d8532c8733298c2996439914c614cb21d4e8630a6590ea54318532c872aa9ac2196438d59664cc721c6acab266390f85434cb31c8727298c498e438d596640c721c6acab206390c7576d4c31c865abb68618e432ddd9430c721e2ea6a186390e656598831c8753322c418e43a9591620c721ccea6b106390e655358831c8753a1ac418e43a950d620c7219caed1906390f85438c831c8673bb26418e439c596600c721dc2c53006390e716558031c8759322c018e43ac591600c721dc4c4b006390ee16258031c8739a9ac018e439c54d600c721d6686b006390eb14358031c8771192c018e43b84c9600c721a74e9a84a190c3e7498e50c861eba4c7286438798d4394321c3ac6a1ca190c3e7418d50c861eba0c6a8643591c532543218f6eca80a190e65629875488734b14c1aa4439a5ca60d5221ce4c2b06a910d3a70d52548869d386c8aa4430fdd95415221ccac53
  | 31 => 0x3b2ec498863e150f624c431d2a863126218e6765189310c7c2a18c498863995d4624c431d4ca83126218ea554189310c763298c498863a9d0c624c431d8c863126218ea543189310c762a18c498863a150c624c4319c8ed2926218e6765949310c7c2a1ca498863c550d524c431cc8c4a926218ce476549310c733b2aa498863c9951524c431e4aa8a926218f8543549310c6b33b2a498863591d9524c431cc8eca926218f4763549310c793a1aa498863d190d524c431e4a86a926218f4543549310c782a1aa4988638b95262d4031c5aa9316a018e2e5458b500c716aa2c5a80638b99252d4031c5ac9296a018e2e6454b500c716b22a5a80634e9d35094031a72e9a84a018d6a72d42500c6b4b96a1280630fdd16294031878e8b14a018d6a72d52500c6b4b96a9280635a9c85494031ad2e42a4a018d3975d0e500c69dbaa87280634e9d35294031a72e9a94a018f2a5494a500c794aa4a528063cad0e5294031e5287294a018f2a5454a500c794aa2a528063cad0d5294031e5286a94a018f607154a500c69d3a0a5280634e5d05294031ec2a518ca018d5b754c6500c6b9baa6328063e450d3194031bc0e498ca018f61524c6500c6ad398c9280635a9c86494031ad2e4324a018d7271192500c69d3a0c7280634e5d06394031ad4e431ca018d697218e500c78db9a87280635c9c76294031a76e8b14a018d387458a500c69d3a665280634e5d33294031ae6e2994a018c79760ca500c69d3a065280634e5d03294031ae4e2194a018d71710ca500c69d3a663280634e5d33194031ad6e498ca018d68724c6500c637390c8a80631b5c86454031e2a8698aa018d64724c5500c63d3b6a8a80635a9cb5454031ad2e5aa2a018c7a76151500c6b5390a8a80635a5c85454031a72eba1aa018d3b7550d500c63d3b6a4a80634e9d35254031a72e9a92a018f2a54949500c794aa4a4a8063cad0e5254031e5287292a018f6071949500c7952a2a4a8063ca5515254031e5686a92a018f2943549500c7b038aa4a80631e9d85254031a74e8292a018d3974149500c78caa662a8063d254b3154031e64a918aa018f31548c5500c7b129462a8063d854a3154031ab6ea98aa018f19544c5500c7a4a9262a80635cdd53154031e64a898aa018f31544c5500c7c8a1a62a8063781c93154031ec4a498aa018f61524c5500c6b838ac8a8063569cc6454031ad4e4322a018d6972191500c6b9388c8a80634e9d26354031a72e931aa018d727190d500c6b8b8c86a8063c6dcd4354031e34c6a1aa018d727110d500c6b8b8886a80635c9c76254031a76e8b12a018d3874589500c6ac39ac4a80635c1c56254031ab4e7a12a018d5973d09500c6b938e84a80635c5c74254031ae6e2a12a018d7071509500c69d3a664a80634e5d33254031ae4e3992a018d717
  | 32 => 0x35a9c05494831ad2e02a4a418d2d75d0e520c697baa87290634b9d06394831a5ae831ca418d6a7018e520c6b4b80c729063c3dcd4394831acce3304a418d2f74582520c6963a2c1290631b9db5454831ad4e1aa2a418d6970d51520c6373b0a8a90635a9c05454831ad2e02a2a418d2d75d0d520c697baa86a9063c99506154831e4aa830aa418d4e73991520c6b338cc8a9063591c56454831a5ce931aa418d2d7498d520c6b338c86a9063595c64354831e1ee6a1aa418d667110d520c6b2b8886a9063c9d0c6154831e4a8630aa418d2e740c5520c696ba062a9063991876054831acce3302a418d2f74581520c6963a2c0a9063531cd6054831ac8e2b02a418c3d76950520c61fbb2a8290638b9526214831c5aa9310a418c6f76548520c717322a4290638b5915214831c74a9300a418e3954980520c734a94c0290638e9516014831c72a8b00a418e6952580520c63d384cba10631e5c265d0831c3ca8b1e8418e4e6354b420c726b1aa5a10639954a61d0831c6ca8b0e8418e6552587420c63d384cb210631e5c265908318f4e032a8418c7970195420c71aaa6c2a10639954b6150831ccaa430a8418c7a70994420c63cb84ca210630f5d664cc83187eeab266418c3d76953320c61fbb2a9990638b99252cc831c5ac92966418e2e6454b320c716b22a5990639954961cc831c3acaa1c6418f0d4354a320c71b2a6c2990638d553614c831ccca5b0a6418c3d75990320c61fbaac8190630f5da540c83187eecaa06418e2e64948320c716b24a4190638b991520c831c5ac8a906418f0d43548320c71b2a4c2190638d552610c831ccaa53086418e3654584320c71aaa2c219063a550d610c831ccca4b086418c7975980320c71d2a4c0190638e552600c831cd4a53006418e6952980320c63dbaac0190638e951600c831c72a8b006418e9943580320c735292c0190639a549600c831c3aa8b1c8218e1e5458c410c72731aa4208639358d521043187aed2a66218c3f76553310c717324a5988638b59252cc431c5cc8a966218e2d6454b310c786a1aa598863c355152cc4318baed29c6218c757694e310c69abae87188634ddd5438c431cccc4a946218f265454a310c792aa2a518863c9d0d528c431e4a86a946218e1f65d0d310c70fb2a86988638b953624c431c5aa9b126218e2e54189310c716aa0c498863a350c624c4318d8ed2926218c6e76549310c786a1aa49886393dcb654c431c98e5b2a6218e1f65951310c70fb2aa89886393d97624c431c9eca3126218e4f65949310c727b2aa498863c3551524c431ccee5b2a6218e6472d95310c71bb2ca8988638dd95544c431b2ae929a6218d3575d0d310c71bb2e8698863655d2434c431a6eeaa1a6218e376550d310c6cbbaa8698863c5dd5434c431d2ecaa1a6218f176550d310c73
  | 33 => 0x931a5ce9b06a498d2d74d83524c735b04c1a9263595c460d49318deeca90a498c3f74580524c61e3a2c0292631b5da54149318deecaa0a498d6b70550524c6b4382a829263595c76414931a9ae6320a498d6571190524c6b5380c8292635a5c06414931acce3a18a498d6571d0c524c79338e8629263c95c74314931acee2a18a498d647150c524c787b9a8629263c9dc54314931e48e2a18a498d2e74d84524c696ba6c2292635a9c36114931ad2e1b08a498f2743584524c792a1ac22926359dc16114931acae3b00a498d6571980524c697ba2c0292634b1d16014931a5ce8300a498d2d74180524c6a6b98c029263595c46014931cd2c0300a498e6452986424c732292c3212631e9c065109318f2e03288498e4e63148424c726b18a4212639914a6110931cc8a4b088498e1e6550f324c717320a5992638b59052cc931e1a862966498e6452986324c786a18a4992639914b614c931d2a8630a6498e6752185324c717326a4192638b593520c931ccea53086498e6b52980324c735a92c0192639398c52d0531c9ac62968298d3870552414c61f3b0a8a0a630fdd95410531a70e0aa08298e2e64d4b314c716b26a598a638b99052cc531c5ac82966298e656214b314c793320a598a63c959052cc531e4e862966298f254314b314c732292c198a63c350c528c5318dce5326a098c6d72993504c6373b6a4a82638bd935254131c58c9a92a098c6e76149504c717b20a4a82638b19052541318f6eca80a098d3874540504c732b14c3aa0639a98a60d5031cd2c5306a818e6a62583540c734b12c1aa0639c98560d5031a5ce5aa4a818d2d72d52540c69d386a92a0634e5c35495031a3ce7b14a818d3671d8a540c68f398c12a0634b9c86095031a5ae4304a818d3671182540c697396c8aa0634b5cb6455031a74e1b22a818d3970d91540c637390c0aa0631b5c86055031a68e2b12a818d3471581540c68f398c0aa0634b9c86055031a5ae4302a818d3671181540c61fbb2a82a0638b5526215031c5aa8b10a818e3954980540c71caa2c02a0638b9926215031c5cc8b10a818e4e63588540c732b14c22a0638e9926015031cd4c5300a818e6962980540c71d322c02a0639698d6015031cd4c4b00a818e6962580540c73930ac02a0634b9cb54d0c31a5ae5aa68618d3a70d53430c69cb86a9a18634b9c854d0c31a5ae42a68618d3a70153430c69cb80a9a18638d5516190c31a5ce5aa28618d2d72d51430c69d386a8a18634e5c35450c3187cec2a28618d2e72151430c696b90a8a18634e9c05450c31a72e02a28618c3f76550430c71b2a2c2218638e95260d4831c72a9306a418e3a54583520c71caa2c1a90634b9d35294831a5ae9a94a418d6a70d4a520c6b4b86a5290630fdd16094831878e8b04a418d6a70d52520c6b4b86a92906
  | 34 => 0xa6420e6552185321063d386ca190831e5c3650c841c3ac6a9e8220c3d76952411063abb4a9208830f5cf655044187ceca9a8220e1f6354d411070f31a87280838758d43940418dce431aa020c6d7218d501069c38286a80831edd95014041cb2c6a80a020e69625405010697390c72a6634b5c86395331a74e031ca998d397018e54cc69ab8ec52a663479cc6295331a5ce5b0ca998d2d72d8654cc68f398c12a6634b9c86095331a5ae4304a998d357118254cc71cb00c12a6631b9c860553318dae4302a998d2e7298d54cc696b94c6aa6634e9c26355331a72e131aa998d377158954cc69db82c4aa6634e1c16255331a5ee4b0aa998d2c7258554cc69db82c2aa6634e1c16155331a5ee4b02a998d2c7258154cc69bb8ac0aa663479cc6055331a5ce4302a998d2d7218154cc69ab88c0aa6638e580605533187eecaa0a998e566358454cc71aaa4c321e630f9d85450f3187eecaa08798e365498443cc61fba2c1296630f1d16094b3187aed2a0a598c3f7655052cc637bb2a4296638e9526014b31c72a9300a598e3a5458052cc71caa2c0296639a5496014b31c6ca930e8598c7b7059542cc63c382caa16638d5506150b31c3ca8b188598c3d7599332cc61fbaac9996630f5da54ccb3187eecaa66598e365418532cc71aaa0c299663a550c614cb3187aeb3206598c3f7559032cc61ebb4a8196630fdd9540cb31c6ca93086598e355498432cc71b2a2c2196638d551610cb31ccaa4b086598e3a5498032cc71caa4c0196638e951600cb31c72a8b006598e6a5258032cc734a92c0196638795163d0731c3aa9b1a8398c3f7458a50cc61e3a2c5286630f5da541433187eecaa0a198e2e5498850cc716aa4c4286638b9516214331c5aa8b10a198c7b7654050cc734b12a0286631b9ca60d52318dae5306a918c3f76550548c72ab1cc22a4631bdd95214a318f4e1b2c8518c7970d96428c733290c299463a550d610ca31d3286b006518c3e76151418c61fbb2a820c638759664cc631c3acab266318ce772597318c6b2392cb98c638d59664cc631c6acab266318e656294b318c717a1cc5284638b50e6294231c5e86b14a118e2d4358a508c68eb98c8a8463879cc6454231c3ae6322a118e3671191508c71ab88c8a84630f9db4354231878eca1aa118c7b76540508c637394c1aa2631b5ca60d5131c9ac7314a898e6662586544c732316c2aa2639ad8b6055131cd0c5b02a898e3b64181544c735b10c0aa2639a1886055131ce6c2302a898e7171181544c61fbb2a82a2634e1c15415131a3ae7b2e8698d2f72597434c696392cba1a634edc165d0d31a70e0b2e8698d2e72d95434c696b96caa1a6347dcd6550d31a3cebb1a8698e1c65d8d434c6cb38ec6a1a635adc154d4931ad0e0aa6a498f0f7350f524c6973a6c3a92634b5d361d4
  | 35 => 0x545500cba8992a2a8065d84c951540328f4ec28aa01953a74145500ca9cba0a2a80655a1c96454032ab4e6322a01956a72191500cab9388c8a80655c5c46454032a74e931aa0195397498d500cab539486a80655a5ca4354032e36e6a1aa01971a6350d500cab539086a80655a5c84354032ab4e6212a01955973109500ca9d3a664a80654e5d33254032e3287992a01972b438c9500cb94a1c64a80655a9c63254032e3286992a019573714c9500cab838a64a8065d2dcd3254032e5686992a01974a434c9500cb94a1a64a8065d250d3254032e1286992a019763714c9500cab438a64a8065d81c53254032ac0e2992a01953a740c9500ca9cba064a80655c9c43254032ae2e2192a01956a72d85500ca9dba2c2a80654e1d16154032ab0e6b0aa01956872585500ca1ebb4a8280650fdd95414032c6ca9308a01963554984500cb1b2a2c2280658d55161140328eaed288a01963664944500cb1ab24a2280651ddd95114032c6cc8a88a01963564544500cb1d2a4c0280658e5526014032ce4a3300a01967151980500ca3dbb2a0280658e9915014032c72c8a80a01967261540500cb38b0aa028065539cb5394f418dce4302a7a0c6d7218153d062fbb2a629e83c554e61d0f41e2aa6b0e87a0d4e73d4a52d070eb1a87296831bdd95214b41c5cc929665a0c7a70d9432d063cb86ca1968387991530cb41c5cc8a9065a0e565358432d072aa9ac21968399949610cb41ccaa4b0865a0e5a5358032d072ca9ac0196839a949600cb41cd2a4b0065a0e1e6350e50d070eb1a87286831edd95014341a70e0b22a720c5f7654c539068fb82a6a1c83c554f6150e41e2aa630a8720cb57118143906b5386a5294831e9c06354a418f2e031aa520c6f76548529063d384cb194831e5c2658ca41ccca430a6520e6552185329063d386ca194831e5c3650ca41c3ac6a9e8320d6a72d42509070f31a87284838bd0e6294241c5a87314a120e2f7458a50907163a2c5284838bd0d6294241c5a86b14a120c6e7218d5090636b90c6a84831edd950142418f4e1316a6a0c797098b5350637394c1a9a831b5ca60d4d418beeca98a6a0d1d70d4d435078ba9ec2a1a83c5d4c6150d41cd6a4b04a4a0c6f76548525063db82cb992831e1c165cc941c5ac829664a0c7a70194325063cb80ca192838b593520c941ccea4b0864a0e64525843250735a92c0192839a149600c941c3ac7a9c82a0e6962d42505063dbb2a0282838798d43141418f4e0312a620c79701895310637390c0a98831b5c86054c418beeca98a620e4d53588531072ca9ac029883c554e61d0c41e2aa6b0e8620c7a7018d521063cb80c6a908387d8d43548418deeca90a420e4d635485210734a92c0290838799153cc8418f4e032a6420c7970195321072b298c2990839554c614c841ccca430
  | 36 => 0x394c1288654ddd16094432a68e8b04a219566718c9510cb86a1a64a8865591c532544328ecedaa2a21957270d51510cab8b86a8a88651d9d85454432ae4e02a2a21957170151510ca9abae86a88654ddd54354432e4ca8312a21972554189510cb8aaa664a8865c99523254432e4aa9192a219557754c9510cb8aaa264a8865391d93254432aceea992a219726544c9510cb92aa264a8865e150d3254432aace7322a21956672991510cab2392c8a88654d9d26354432a6ae931aa2195667290d510cab2b9486a8865c5dcd4354432acce421aa2195657210d510caab39884a8865555cc4254432a6ce9992a21953574cc9510cb8aa1e64a8865c9d0e3254432e4a87192a219477764c9510cb8aa1a64a886599dd93254432ac8ec992a219664764c9510cba3b9a64a8865c9d0d3254432e8c86992a219725434c9510cba2a1a64a8865c150d3254432a6ce8192a219535740c9510cab3394c0a88654ddd16054432a68e8b02a21955473581510cab2392c0a88650f5da541443287eecaa0a21963654984510cb1aaa4c2288651ddd95114432c6cc8a88a21963564544510cb1d2a4c0288658e5526014432ce2a3300a21963a54580510cb1caa2c0288659c5456014432c6ca930ea01963554987500cb1b2a2c3a80658d55161d4032c6cc928ea01963564947500cb1b322a3a80658d59151d4032a74e9a84a01953974d42500cab938ea1280655c5c7509403287ee8b0ca01943c74586500cab938ea9280655c5c75494032ae4e22a4a01957171152500ca9cbae87280654edd54394032ab6ea994a01956b754ca500cbc4a1a6528065781c53294032a74e9a8ca01953974d46500cb992a4a328065cc5525194032e668728ca01973143946500cb992a2a328065cc5515194032e6686a8ca01973143546500cbb0392a328065d88c95194032ec264a8ca01953a74146500ca9cba0a328065569cc6494032ad4e4324a01957271192500cab8b88c9280654e9d06394032a72e831ca0195727118e500cab8b88c728065c6dcd4394032a74e9994a01953974cca500cab9b8a65280655c1c53294032ad4e5b0ca01953b74586500ca9c3a2c3280651d9c464540328eae2322a01970d434c9500cab238a64a80651e9db5454032ae4e3aa2a01957171d51500ca3d3b0a8a80655c9c45454032ae2e22a2a01953975d0d500ca9dbaa86a8065c65533254032e54a9192a019729548c9500caadbaa64a8065c65513254032ad6ea992a01972a544c9500cb94aa264a8065e250d3254032bc0e2992a01947a76d45500ca9d3a6a2a80654e5d35154032e64a928aa01973154945500cb99a1ca2a8065cc50e5154032ec0e528aa01976232945500cbb0994a2a8065cc9515154032e62a8a8aa01973343545500cb98a1aa2a8065d81c95154032ea664a8aa01976232
  | 37 => 0xc99d33214532e4ae9990a29972743cc8514cb92a1e6428a65595c33214532e2a87190a29956572d80514cab2b94c028a654ddd16014532a68e8b00a29953674180514ca9aba0c028a65555cc6014532acae4300a29967160180514ca3b38cc9a82651d5c664d41328eceda8aa09963764d45504cb1a326a2a82651d9d85154132c6ec828aa09963464145504ca3dbb2a0282654e1d15014132cccc4b0ea81967261983540cb38b0cc1aa0659a98960d5032ce4c2b06a81967161583540ca9b38ea92a0654d5c75495032a74e1aa4a81953970d52540ca8f39ec32a0654b9cb6195032a3ce6304a81952e72182540ca9b388c12a0654d5c46095032a6ce3b22a81953571d91540ca9d386c8aa0654e5c364550328ece2302a81947571181540ca96392c2aa0654b1c96055032a3ce6302a81952e72181540ca9b388c0aa0654d5c4605503287eecaa0a81963554984540cb1aaa2c22a0658e5526015032c72a8b00a81963664984540cb1b322c22a0659598d6115032cccc4b08a81963a64980540cb3930cc02a0659c5866015032c74c8b00a81965a63580540cb35312c02a0659c9856015032ce2c2b00a81953671d53430ca9ab8ea9a18654e9c354d0c32a72e1aa6861953671153430ca9ab88a9a18654e9c054d0c32a72e02a6861962d5458a430ca9b38ea8a18654d5c75450c32a74e1aa2861953970d51430ca1f3b0a8a18654d9c45450c32a6ae22a2861953a70151430ca9cb80a8a18650fdd95410c32c5ca8b10861961d5458e420cb0f2a2c6210650f5da54cc83287eecaa6641945d7694e320ca36bb4a7190654b5d7438c832a5eeaa1c641961f65d0d320cb0fb2a86990658d953614c832c6aa9b0a641963654185320cb1aaa0c299065a550c614c832caee3b2a641965471d95320cb0fb2ca89906587d95544c832caecbb0a641965765185320cb33b8eca99065991c7654c832c5ecb2a2641962f65551320cac6ba4a6990654b5d7434c832c5ecba1a641958d7490d320ca97baa86990658bd95434c832b1eeaa1a641970f7550d320cb47b2a8699065c3d95434c832ccecbb0a641978543d85320cb46a18c29906599d94614c832f0a8630a641966575185320cb532a0c299065a9550614c832d8ca630a64196a743185320cb63218c299065a950c614c832d8a8630a641968543185320cb1d2a4c1a88658e55260d4432c74a8b06a21963954583510ca9b3a6a3288654d5d35194432ae4e1a8ca21957170d46510ca1fba2c1288650f1d16094432ae4e1aa4a21957170d52510cab9380a9288655c5c05494432a6aeba1ca2195377550e510caabbaa6528865391d93294432aceea994a219785434ca510ca9b3a0c7288654d5d06394432ae4e031ca2195717018e510cb8bb9a87288654d9d33294432a6ae9994a219474764ca510cab3
  | 38 => 0x42ce2a2b00a22161e6350e5010b0eb1a87280851d9c463540428eae231aa0215387050d5010a3dbb2a0280859658d5014042ce2c2a80a0215367118e54cca9ab88c72a6654e9c06395332a72e031ca99953671d8a54cca9ab8ec52a6654b5cb6195332a3ce630ca99951e7318254cca96b90c12a6654d9c46095332a6ae2304a9996396018254cca3b388c0aa6651d5c46055332a6ce331aa9995357198d54cca9d384c6aa6654e5c26355332a6ee2b12a9995347158954cca9db82c4aa6654e1c16255332a5ee4b0aa99953b7058554cca9c382c2aa6654bdc96055332a6ee2b02a9995347158154cca8f398c0aa6654b5c86055332a6ce2302a9995357118154ccb1cb00c0aa6650fdd95415332c9cc6b10a99962d5498a43cca1f3b0a8a1e650fdd95410f32c5ca9310879961e5458f42ccb0eaa6c6a16650fdd16094732878e8b04a39943d7695051cca1fbb2a828e651ddd95114732c74a9300a3996395498051ccb1d2a2c028e658e5516014732ce2a2b00a39943f7458650cca1e3a2c3286650f5da541433287eecaa0a1996365498450ccb1aaa4c2286658d9516114332c6aa8b08a19947b7654050ccb38b0aa0286651d9c660d52328eae3306a91943f76550548cb26b1cc42a4650f9d85450a3287eecaa0851961d65993328cb0eb2ac99946539dc565cca32ac8e2b2e651962d65993328cb16b2ac999465595c732946328eeeca88a31963743986508cb1aa1cc3284658dd0d6194232c6a86b0ca11951d73191508cb0f398c8a8465875cc6454232c5ce4322a11962d72191508ca1f3b686a84650f1d943542328f6eca80a11947671983544ca3ab8cc1aa2659558e6195132ccac530ca89966762185544cb39b0ec0aa2659c1876055132c76c8302a89966b62181544cb39b08c0aa2659c1846055132cd2e4302a89943f76550544ca9c382a82a265475cf65d0d32a6ee2b2e869953471597434ca9db82cba1a654e1c165d0d32a6ce3b2a869953571d95434ca8fb9acaa1a65479d76350d32c38cbb1a869958e72d8d434ca9c382a9212650f9d8545093287eecaa0849953870550424cab9b82a9a8a655c1c154d4532e2ee6a1ea29953674d8b514ca9aba6c5a8a654d9d332d4532a6ae9996a29953674d83514ca9aba6c1a8a659cd8260d4532acae4306a29947776544514cab2b8e6428a650fdd16014532878e8b00a29947576950514ca3bbb2a828a655cdc15414532ae0e0aa0a29956572d90514caaab98c828a65595c86414532ae4e0320a29957170190514cab33968628a65595cb4314532e4ce5a18a29972572d0c514cab3b928628a65591c94314532e2ee6a18a2997277250c514cb923928628a654d9d36214532a6ae9b10a29957270d88514cab8b86c428a65559cf4214532aaae7a10a29953674cc8514ca9aba66428a65
  | 39 => 0xa2a1e9b63d815150f55b16c0a8a87aa18b6054543d36e7b02a2a1e9b53d815150f4db18c0a8a87aad886054543d50c4302a2a1e99731815150f4da98c0a8a87acd446054543c74a2302a2a1c3f765445150e9c382a228a872ddd95114543b48e4a88a2a1db0705445150eccb86a7a82872ddc562d4143968e2b16a0a1caf725875050e56392c3a8287a3d8f6254143d1ea7b12a0a1e8f631895050f47a98c4a8287a5d8f6154143d4ec5b0aa0a1ea462d855050f4ba9ec2a8287a5d8c6154143d4ec430aa0a1ea4621855050f4ba98c2a8287aa18b5054143d60c3a82a0a1e2c629415050f1a30ca0a82874e5c35314143b32e1a98a0a1e8d639885050f17a9cc428287a3d4e6214143d1ac6b10a0a1e2f535885050f47a9ac428287aa1c16214143c5ac5290a0a1d39701485050f4ab1cc228287a998a6114143d4ac5308a0a1e37539845050f4ba9cc228287a558d6114143d4cc4b08a0a1ea5625845050f1ba9ac228287a5d4d6114143d60e0b08a0a1e35619445050e9cb80a2282870fdd95014143a58e4a80a0a1d34715405050e5dbb2a0282876a1c95014143b60e2a80a0a1d3b765405050f1dbb2a028287c6dcd5014143e32c6a80a0a1f2b725405050e9c392a028287ca1c95014143a50e4a80a0a1f2a625405050f94b12a028287ccdc55014143a70e2a80a0a1f30715405050e9838aa028287cc9855014143e62c2a80a0a1c3d769524310e2ebb4a9218871d9c660948438eae3304a421c6f765485210f32a92c2290879a54960148438dce5304a221c6d729825110e3bbb2a228887995895114443ce2a2b00a221c7b765405010f34b12a0280879c5855014043aace3a9ca7a14767118153d0a3ab88c0a9e8517dd95314f42e1aa731687a170d5358b43d0aab39ea328e858758d43947428eeeca88a3a161e6350e50d0b0eb1a87286851edd95014342a70e0b22a72145f7654c5390a8fb82a6a1c85c354f6250e42e1aa631287214ad721814390b0eb1aa7a14855c9c351946428f4e031aa3214797018d5190a3bbb2a228c855c9c75094242c3cc6a1ca121637439865090b1aa1cc3284858ddd16194242c68e8b0ca121637435865090b1aa1ac3284851d9c463542428eae231aa12147b765405090a3d384c3a9a851e5c261d4d428ece3306a6a1475719835350a2fbb2a629a85475c35350d42e1ea7b1286a170f531894350b0eb1ea7212859cd4560945428eeeca88a2a167161d425050a3dbb2a0282858798d43141428f4e030aa621479701855310a3b388c0a98851d5c46054c428beeca98a621655535845310b2ca9ac029885c354e62d0c42e1aa6b16862161d6354f4210a1ebb4a9210851b5da549084287ae7b2a842143e7654d4210b0fb1aa6a10851e9c063544428f2e031aa22161f6350d5110a3bbb2a2288859558d51144
  | 40 => 0x10000001000c0030000001000c000001c0000004000000000200000000008000000000f000c000002000000000000000000001000000000070034001001400300000020004000001000400080020004000000000300100040004000000800000240000008002001c009000c0000000000000c0010010002000000100000000004008001400000080000008003000400f00000040000002004000500000020000002001000000040040000001000001d000400300000110004000000000500000080010004000800000000000008000000c002000000000080020014000000c001002400400000000000000acce3a94a5a1c767198252d0e3ab8cc1296871bdd95214b43acce5a8ca3a1c6e7298251d0e36b94c128e871ddd951147438ece3b12a1a1c7571d8950d0e37396c2a86871b5cb61543438f6eca80a1a1e956398752d0f4ab1ac3a9687699c75294b4396ce3304a5a1cb57198252d0ed338ea4a96870fdd95214b4395eeca90a5a1e8d6398b51d0f46b1ac5a8e87699cb519474395ce5304a3a1cad7298251d0ed3396a2a8e870fdd9511474396eeca88a3a1cb671d8950d0e5ab8ec4a86872b9cb615434395ae5b0aa1a1e8d6398850d0f46b1ac4286878b58a5214343a72e0290a1a1e956398450d0f53314c228687a958a6114343d2ac6b08a1a1ea66258450d0f52b12c2286878d5865114343a72e0288a1a1c3f7654050d0e5dbb2a0286874edd95014343c76eca80a1a1f196354050d0f95312a028687ca5895014343e64c2a80a1a1f316154050d0e3b38cc1294871d5c66094a438deeca90a521e65525845290f34a92c0294871b9ca60946438dae5304a321c77765445190f32b12a228c879c54560146438f6eca80a121e69625405090f38b0aa0284871bdd95214943ac8e2a90a4a1d68705485250e3bbb2a228a87591c95114543ae0e0a88a2a1c777158b5050e3a38ac5a82871bdc961d41438d8e4b0ea0a1c7b765405050eb4392a0282875c1c55014143c5ee8b10a0a1e2c745885050f33314c2282879958a6114143cccc4b08a0a1e65625845050f1bba2c2282878d1d16114143b2ce3b16a6a1d9571d8b5350f47b14c5a9a87639cb61d4d43b1ae5b0ea6a1e97619875350ec7390c1a9a87635c860d4d43b2ce2306a6a1d95711835350e5b38cc1292872d5c66094943d2ec7b0aa4a1e9753d855250f4bb18c2a9287a5d4c6154943d4ea430aa4a1e9b63d815250f59b0ec0a9287ac1876054943d36e7b02a4a1e9b53d815250f4db18c0a9287acd846054943d60c2302a4a1e99731815250f4da98c0a9287aad486054943c74a4302a4a1c3f765485250e9c382a4292872bdd95214943b48e2a90a4a1da8705485250e57394c128a872b5ca6094543d1ec7b12a2a1e8f53d895150f47b18c4a8a87a3d4c6254543d48c5a8a
  | 41 => 0x40080000001000000000040000014000004800300200000000007000400a001c00300580000030000000c0070000004000c00500000010000000000800b00000020000000000000600000010004000000000100000000008000001000200000030010003000c001000000600000000024003000800400000000008000000000100040000000000000000300000010000002001c0000008000002c00300000010004001001400f000c004000c0040000002006000100080000000000000000000000000000000000400000000010010000000400200140200000002000800500240010000001000c00000000050014007000800100400010000001000c000000400100000030010000001000000540000010005000800200000000024006002000500140010014000000c0000008000000000200140000000003000000100080020028004000400300000020000000000000100040000008002000800400040010004009000000100080030004007000000900000030004004000400b000c0020000001000000b0000000000000b00040000000000000000400040080004002001c003000000500000000000008002c000000000000340030004002000c00000280000004004000c00000040010040000000000100100000008000000400a0000002000400400000000000003000000000180010014003000000000040010030000000400300000020000001000c002000000200000000010001003800a0014002003400100100000008004001c00200080000000005000c00000000000000000000000100040020008000003400000040030014001001400000000030010000000800400180000024001000c00000000000008001000000f00040010004003000c00300000010008000000000e00100000000000000400100000030000001000000200080060018002002800100000030000000002c003000800000100010000003000000000080000000001000400000140000000001000000200040010000000000400000080000000001000000100000040000004000800a0044004000000100040030004002002000000080000010002000001600000020010003000000100100010000004000800200040010020006000c00100000020000000000000200000000000000000400100040010000002000400100100010008004000000000000030010003000000e000c0050010000001800300000010000000000000000100020004000000400000000030004000001400000040060010000000c0040008005002000400040060004000000000d00000030020000000400a0018000000400a000c0000008001002c004000c001000001200040020000001001400200340000004003000000000080010004003000c0030014001000000200140020004
  | 42 => 0x40020004008000400e000000100000010000007000000000280020000000001c0000028000000000000040010004001000000000100050000006000400100080000010000000800200380000038000000000200180010014001000400a00080000000001000000500100000004000000c002001c003001c00700000000004001001400e0000000001c001001c0010004000006400300000020048001001000600000040000000002400d00000010004003000c0030050009000000a001400000080000004001000c000001000000000010004006000000b00040000004009000000000040010000002000000000300020014003000000600000020008000000000100000000000000001c009000801100000050000002000000000000080000005000400300000030010003000000100280020020003000000100000000008001000000000040000000000000400100140100004000001000000000010020000000000100040010000005000000d00000000008000000c000000400000080000004002000400500000010010000000400700000030008010001c0010000000000401a000000100140010000000001400000040020008003000400000200000000001000400300000030008002000000100000010000000000c000001c00000080020008000000000000040000004004005800000000000000005000800d000000000000000030001001c00000180070008000000400000100030008001001400000000020010006000400200080000020000000400a00000180054000001c001000801a00000000014004002000400000010000000000400300040000008001001c0000000000003000400040050000001003c001000000100180000000001000c006000000100000010000000002801c00040000000006000000200040010004001000000f002800000000020000000000000a000800400180000004000000000100140000014001000000400000000010008001000100040050008000002c00600000020010003000c001000000000000030004001000800000100000000003000c0000000004000400b000800b0058002000400000000000004000000000400000030000000000400000000000000001000000100000060010000000400100000080010001000000000000010000002000000000000000004009000000f00000000000004002800300040020000001002000b00240010008000000000000000030000001000800f000c00300000000000005004800200080020000003000000200000000004004000000000000000000012000000000180010000002000000300180050008007000000600180070000000000000600000050000000000400000100000000007001c00200140000004000001c002000800000040050000001
  | 43 => 0x1001400000000010000000000000000040000000000000400100000000000000000800100200090000001000400000040010010008000c002001000100000040000004000c00f001000100040050004000000000200000030014002000800c00000010000002000000400300040000005000400000000030034000000c002001c004001c01500180090004000000c006001c001000400900080000000002003800300000000008001000400100080060004000000400000000000004003000c0060004005000000200140010050001000000000040030000000001c000000000000080000004007000c00500040000004001000400000040000000002000400100080040004000001000700000000000004000000300000000000000001400000000010000003000c002000400000080010048001000400100000030000000000000000000050000000000c00100000010000007000000000000020014000000400000040050010002000c0000004002000000000080000000000004000c0000000000400300080030000003000c015002400200040000008003001800b0004000000c00000080000000002000800000040000004004000000800040000000000000c0000014002004c004000000700080030000000000000d0000002000c002000000a0008000001000200000060000001000001300340040000001000800000640000000006000000500000000018002000000300000010020001001800700000000008001000c00000100000004009000800000040000000004000800300080000000000000000300000000000000001800400280000008000000000000000020018003000000100040030000000001400000040010000000001000100080000014005000800a003c0010008001000800c0028000002400100140030000006000400200380010000007000800200180000010007000400000100000000000000c00000240080000000000c0020010002001000000000010000001001c00100000000000009000c000002000000240000010002000c008001401200400010000001000000100000000000000001400100000000004003001000000000010018004000c001000800000000000000001000c001000000e0004000000000000000000004002000001500000010000002001c0000008000000000e00000000000000000400100040000000001000800300080010004000000000100000000000001000000000080020000000000000700080030004003000c00100180000004004000800800000000000002000c004000c00100100010010000000c001001c00100040040000001002000100000000014003001c00200040000000000000c005001400500080040010000000000000040000000000000000700000000000001000
  | 44 => 0xe3400000000000000558a28651780001218000a14857c00033249d98000672000000000006468d7ebc70dc40002162c3c24f891d0c103fa000000020be04497f800000002e380008b680000000000bc48000000262624300002458c9800000000001b5001c8000ab08fb4091917a00007046bd96189a0a7a46848d0600000000dc2a600002756cb5b2ca000219a54715520002d5600025520000000000000000000005f8a28a00000006e6000000000009908b0c14b80000000000c868d30000000012b000000034900001e580000000000105600023c4000000000000002a6000000000000000000131a3f436a2d32413800000000000002f5a0002c1a277000000000000001f6c00000006b7030a6d30000000119676980006999e5e272a70eaeeb46a00000000b48000c3a000011523e6a1f00000002b98766970c2ca2a462fc1f9c49b23f800000007cdab523e3000095f99ba00033602238000a0581181a51956000c0000000000000000600000000004004000800100040000000004000000100100000008001000000300100030000004000c002000000000040000000007000c0010000000000c0000004001000400300040020014003000000000000010000001004c005000400e001c002000000000040010004001001800100000000000002000000100000000028000002800000040080004000000c00000080000014000000401a000800b000c001000400b00040000004001000800200040000018001000c00000000000000000001c001000400000040010008000000800800100020014000000c0010018000000000000000040008000000400700000000008000000400000080030000007001c0010000000002000000140000004000000800000000000000001000000000000000010002000000000040050014000000c0010004003000000800140030008002001800b000000000100060028000000400d00140030000005001c0000014001000400200000030030005000000000080030038000001c00000080000004000001000000280020000000000c00000040020000002000800000540030028000000c000001c000000400100000000004000000c000000400000000000004002000400100000000004007000400100040050028003000000200200000008002000000100200000000003003400300080030024000000000000340050008001000000300000030004007000001f0000003000400000000010000003000000300000000004001002c00000000000018002000c0020000004000800000080010008001000000400040050014001000000000000000008000000800c000c01100080020004000000000100000040000004005800500140000008001000000100040020014000000000400040000000007000c00
  | 45 => 0x54000000031580008820000000031a00015e20002c1600028c03b796e200001649758000cc60000000000000021da000343c705af1600000000002eb86ea893416b000099e083600000000003510c530c600000000c980000b3c0000b4aa81a00000000000000000000098e800000000000001c680002f244f109c800030a481b025a99900000000a7ea0800004170d4e000218c0000770000000000000002de8000000000000000000001ef219c80000000000b99adb479a111800000000000b780000000000203e99f8360aa529a8000000000013a00000000000343800000003150000bd0a016000092497f00000000f120002cdc000136290b99da00013860000000000000000000000000000b811f7400000001d6818a9d410f60000c6a04f9324793b03661baeb22cb92ec000021a76d0000aa723d204b1356d1d2dda0faa9ec97d9e4643f249c3658000bcf2c8234218c410d80000002c8c000352070600008db1fb400024d2c938ad80002a9ec70064ed0dac6e8db800040c0098a16aa66a6c902800000000001a58ca2330e0000000000152e26a139c16300002909f400000196160935ed3fafb4282b1780003338000000061d800094c33cc00018e6b110000a8720ca000162c0000618a14000000000000000000c110bbc73181a0bf480000000000000000000007c200000000000000a9d85fe00033d40001a90a510000402306e4790a6c287a76a19d0a9c3270940cb9a5180001c40000000044684ee2b7afec000000021e8000196ab2249680000000b8cb6d80000000f94214000052bb2f4af6000000021221f4000000022127972bf6000046c53205a400000006de000000028b00002cf40000000c030000581000063780000138f26c4b00000000f0ac719f924b7271c00004aa00005aad3600003b8b52e0001a6e24b81c8b5c12162d21b6e0000000000315200000000000000000282e6ce00009c18000000000063c08da0000000000000000000002fd9eb80000000000073e00000007d6b2be053abe4a43b3be00000000000000000251ed3a000000016505cd924a5c08000000000030c800000032f6000239c0001c96c2e80000000000000070e2ec00000002e827ee06a661a07e6000000000005925ea1cf400009fa5ada082274a4b67138d7a00000005ab2e980000c187c701d0000233605880009f880005a98000cc5968000000008c22b766118000c0fa2ea00000002cf054e3e219ae662adbe9b380000001d1ac800bb4b7a000000000000000000000000000032b60000000000000000000000001106a4f021e6020000000000056400009639a4e00000000002c9a3bbaef6cfd875800000001670000000000000021d45a6800000000000002bca50d80007350794c0231120002c5a1b232a60001f180000000000000000
  | 46 => 0xd400cb1b18d430000b5a8000572000084a932a0000000000000000000002cc80007f598ee622085a00000002e880008348000454ac868760000b7900000000938000141a5799c00d4e2df600016420001e4478880005498000c57971abbc8c62a1086ba4f680008c4a748000190a100800021380005d4270200000007ef8000000031e0000000000000000000000000000afb8e7c53e800099880002bfb05c5b40778323921c000131034b05520001e821960000141a4de5a50de25511b1472f1f4455b919ed418de45c384ba22483fc31600002c987a6c3c80002190fb20000000620a26abf706b8662000000034fcd0a0000c3ba69461ea56eb510000300000000000006d9824e00018780000000b60972859c000099024b80000000190800000000007230b3e9440000000287278823cc39d80000001424d310000000000000000001a21054276142c05f0b7600000000000b0600000008d40dc6c650b62a7996f699c924c000000040e000047b82bc0000000000297cbaab03200000000002f30000072830e800000000000001b72000000000000000000000a1a80009aa8000000000000032105ce80002769f4a83e0e64c508000000000000000000000000000081c00006704f9000000007060001f165b80cfcc34a71800000000000000000312440ba8d00000d429a00a8e2479a8ec13800000000000001d5e00000567b3b2249b804be000000000006007701964935324865d80003942fa081e0000a3b17d6b62af8cd44800048e862a7f624440000000ce29fe419f1ada00000007c0207a0000000ae699fe03f8000000000000000004501d58b6ea6327b180000001c886e800004060532a118000000131c77c30ea22d8000000000000000000000f180001048a8da4769f980008e68928000000000029340000000095000000000005c80000c8200009b980002f4b02c0000b1c00020b0000000000000000000000000000000030cc65faf4aa628fd07baa4dc73e92760b322742cd1c5a6ca000000000000000b9c94b0000000000000000006b21ea055c00000000000000000059898a800030e6000092a2da00008ff00002818000c0c0ece74d1b5e00027bc000124031c0000000000000000007c1909868eb1209322102c7b0adca26310400000009dbaa0213b000000000008ea00000002596000000000017b8045a9c0000294c47c000002300000000d8c000000000000000002a720a104d26710d8a01daa14304800000000000000000000162800000005a800000000000c5d80000002cda78217a211287a48c600000002e86569330c0000c04bdf00001100000d2800000000bea7099774000112a41e965c9f808e8ab000003930000a0a014c5fb0000ad58aac00000008bb00001ed00006be204600032a200000000d4800000023
  | 47 => 0x10200020000000bc0442000000000006082e3e52a800087a80000cb882682328ca20f0c4a96f94b670426b065514261ecb0b40000b3819000000000000000000000015c000015b6702000026205e8000000000022800002358000000059e07d8d090ff673104d60000a081a1a17e0000ab886c000053b2c12809a7d8000000000028020002a521b9327400031408978f6017c8000b450d9c6b88000afd322085493ea35911fa6c58000b65a8b4683b2fca87b1aa491000018ba5f200012240000ceab44a176a71abd60001e9c0000000b32846e0002c3600007803f628beb849ed862190660000000000000021e000049f00000001176720800000000000000000bbd00000001dd85e7935440992f09b092a2c12af7e82700329d7151a9b886ecbf880a26cf0b18d38933e74e94de0001704c329d8cbfb80000002c926562c749d89ef6000194eadab0ec2301aca238800000000000000000a8e000095280002220000000093694a8000000000000000000b880006bb08480d2893a0000000c7d80000002a4012e000000000000000000c5c00000001666803027e0001b320000dd800005bacd90000166323e0002836b4b894e8dc8aae6180a681289ca099b00000000000017992a04398be000049c000000000000000000000000271450f804800000002a280009e48000abf00000b0800000032802f38798203a5280581bf800014da0000000ba301ea5d91b0600000006f22a563db0000c6e0000bd42ba000000000c38d6247d8000000000000012860000000000011e000000025b2a5a00000004009e424c0a92683616144a08000000110e00030860000000000304000025460001e1e000000001a30ac000000000029ce8b4174e210af280001d2c1a8139419f9cfe000000009280000000000000000000000000000000000000033f80004bb9e4c856219c00000000000000acb8000000000000000004e9a28e76c87240000000000000000000008d32d580001b0a000000000000000000946a6eb0900002e420000000000139e7d5a290200b0780000000bae800000000006ca8000242000000000000000ae800034be118800000000000000000000000078e9762000000000018140a980000000000000055ec190000000284800000000000000000323a2e1800000000000000000000000000033400002c1c946913c260832a1321c2825b8000b20000086b80009e326b68b3800072e800022c8000028012ebfc1eac000030c000075e897293e0000000000000030aad0a90300000000d700b5256400028d800006f2109296c44e2b3c5991aa422b86ae03caf5834680000000000000214e00007763528000b1700000000000000000000000000001d4400007aa77900000002bea089183e00000004c820e251406fc00000003c3050a93580000
  | 48 => 0xb2c000000000001399a7e00030c600000000000cba000000000000000000c02000000000032e4000000000000004fe0000000125000015a63d480002a33094c2b8000000000000000000000cc459f00009120000277977a00029f821d000000000000002d2864b12061c726bca7428da63c9e3ccb100007cc2f5e25c800000796ca0000dac0e8164c8470000000072c0000000af5075000000000000392ae9000000000000001a60000000000000009b4b2789141f806e39dfccba80007de80009ae1d4886223603d11f6283c8000000000000015d40001556c8e22b6000346000032f20000000000000000000002210000000000000000000001f9e000000023cb39a0000000ad400004c9b34620d3046749243624980000000000000000000000000001e5685e80005bc1f540002b6600000000000000017100c4640a740102bac7aa266e187b4724d00000000025067b000000000000002f600001178000283a600808ac9880006671faecdaa2680000000b490bd00002b0a512800000015f60000000be01aa2a10019a00013c800029c891497c40002e4ca05279a76a80000000000000000000019d600006064d6858ebdd9bce6ae8000603800098600008ba08c65af9e401c625e66af9134b78000000000000001428000258a0a7a446000000075d0896c4f80000000000c5100000001a8cb5295b44ad2f089282c9c00000000000000000039c8ee00001de80003032f721fa1a100001b4400000008d880005c88000000000000012cc574800000017f25e70000c4180022fb84423e4935869180006709b820d423760001f5c0000000c97185200000000001f4231434fac2580000000000000000000000005088000950929e9a40b9e3ff185c39583e23f51574b6180004a4800043000001ff92980000000000337e00002c8244a316000000000000000000000cec80000000000000000000006d4000000000021ca15300005b4a9b01fb0000742922200000000000000545800000027b6d2b8000000000039e00000000ae40000000000256877f8000000313a3ef89a0b091fc8a319024075000000014bec772f6e0002ed6871b34c1b600004ea800001d00001b7800071e0dc81cd13e63ad88d471a80003eb309e6f8b01ebab33eed2d1dde9c80000000189ea02147a0000092aff150243cb1c296914c41d00d6a458af40000001a54ea2726f980008121b3a00027b881c08280000000a569f8c05080000000d443ac000000003b400000000000000000000016e000000020765b916c2697901c000000000000000d000001ac16ea000000000031360000000bd72784833a15aa002dcc0000bc800000000000a4c2a20c7a000000026c196e000000000014967360f0259a30221dca786000285884b97ae000000000000000000e58236026e0003
  | 49 => 0x800029103c20000000000000000033ac28ab394000000000000000000000778960c222800000000003ff94f20001c2a98daa5c0000d020e98000000091a000247e4cd80009b42d38000000068580002ee14e400021a66690376cca31f80b1316a00000000002ee420e0000000347a00027ee0002f66cc480002f82974140aab83a78760ab69520000294ecd780008ef0c6c11e00000c42fd801c0000000000036880000003098a2e2900000000000000009d280000000a0cacc80000000000bfe2e448311db043524f67b49a5469700006111d040d722984430000ab90000000000000000000002032561000000027901bfa5703fc8000000084000000008892b80a5c000000000000001e1a00000000000000000146600000009ff0e8000025987b680003ee80006ee26be719000000000007c2800000000000002a2a00000000000000bec85d4000202cc90800000000000002b264d805dcc4516926fc8016885000091e241c000000041d00009b5229c996b3c6982b27a3a1936a1058cb0bb0837253e000000000001022fda0000aca38895d6b55000000007d200021380001c902218ec80002276952093e3b92fb89fd0f425a780000002fd000000009708000c288000c60315a00000008812ee0b4f0e0463696366b80f5a4beb092000215ca409b8a20185fa568a97e60684dac1da912a75000000000000000dfa0000000af22696000000095010c213d9550b8a2d08c8399a6a5780001822a7a7b10f8493e8f6200000000000000145b3c800000000001d7000000004e62142000000000023f0367ac6c5d58db0cdcaaa23b4978c00000000002346aefa39200024a447880001ff0000000000062e2c345768cec4408000b75aaa60001d1e00000008a9800000000000ba8fda000000023f80000a20000b1c00000000f565c70c42a5d859e0001a1ec4ba0cc3b50000000111200023047fa049043fa2d85828000ba700001ceb50076fa2a2ace000067825ae0000000000000000000000000000000000000000000000000ae200000001a300000a7684697ca00000002c88000000000033c8000ab332407078000a671418000300e000000000000000000000000000000003fe0001cf00002b1c1fe00003bc000074721c0b80ac727a5a7c800026502d800007a10000bb7000000000005a1000000012bc00000000003042000023e00006bc65c800000022100002c68b8d8000000000004189f473733786010cac74c3518c1c8482289831623300e64b5a72ab2a27d62668000000000000010dc00018740889e0e00000000002e1c0000000000143c8fb800034e99f4000000060c9a32000133000000000000000b890000411000000000008b480000000000000173eb749fa40000000d0f800000000008a08000bc11708000351ebdd00000000000
  | 50 => 0x40001ce07920000000000035b85be13080000000000000000068b8000d4116cc0000000ad3000004c1f383522e70a7303868b98a6a607a48200032825059594ba9871a00000000000fcc00000000002f4cbd3800000010121fd80000000000000000042480000000000000000000000000000000a34800000000000000000b5e000000028eacab80000000000197a7940001b1200017d876701ec000325632f0000c7280002418000302800000018800000f2c4d1158800032c03bd210c4e493fc1c800000000a7a8371cacbce2e142ff000000000000000b1e0000000000325ecb70560b3100008260702ce091aa05d000000000000000c5c8c700002be80000002266000000000000000000fb0000000000000000000000000000000000000000000448800000014ac00000000000e3a00000000000000000114269f2bde00000000001feaacd9a8212117a4000000000000007132ace0000000576000000008b8000000083e80008d2233400000000000000000000031481400000000095a5940000d7800008a20000000000000056a15f800000000000f960000000000000000000002c423b01070000b2811d830580000000000000044c000314e66ca9d28418a720000000b8222b20001e9a00023b20002230a84b4b0a8c315c7eea64cb9c9d0c62602b63ad17904b42a708ca80003e980000000cc6bccb47e232aa3400017f6bfc9c4200015c215c0000000000000000002a5198c5c2800098b80000000ef876e00001ce1a26aaf80002378000a59b46e00024ae000240200000002f6aaba6ef800000000004908000000115e000000000017ee267af36000000000027e49d6000000000000000000be40e2c0002d4e7c6a0a00000a642b034520002d5e905800000000000000000000000040d8ce22cda65894baef04aa306a1a321bc00028fc00b0a5647a0f281e309480000cdc76b80002e9146e8df8dbe741952c499000003380001181460000000000000000002da4c498000d2686c60000bbe0002a7ca07800064200002340c4400024b05581458000000000026b200000000000000000000000002900001478000000000000000000000000129a3a700000001c5200000006a280000000000000258cb032d42000000000000000001fcc0001cd63858000ce6000000000000001c5830f990c0000000000333400022060000000cf732f8000000041e0000000201234900000002932bea2c4c0000000ad78000b160000000049e4c8800037bb4920ce0512cd48cc07ffa8c2000000065a9968000000043e83360001ae800033c466691b20000000a88882c0002ade72c000039818dc73e00000002020000000000000008100e424a80000be10000ceb800092f8000c1f0000ceda01800003be0bda8940000000000000000000005ff800051d
  | 51 => 0xb588b825d21d10000255000050797be38ba83400025b600000000910000b3c92a40000f06cfc000090f826c332000000004e4ab800000000ce448f226ea2486ee5ed32d8000338c6418000000171217a800014d078e0000000c8622646f32c300000000c0994eac678000a441514ae30000c028b3a0000000000000000000000529eec0e124306542ec4b149506c300000a96186a564922e271828294c9ebc0000000000000000000000000000a9a8000733aa906d496c0cfd0e1a8ee8eea00000008e1b4680001dc24b0803e7ea9ffac4613420002a0a00000000000000be60000bbb00000000000000000000000002a40000000000033080000003354000000000000002a88a4aafe00004399998355989063f8000af19064000225a0003230b74273800000004441166be18a54000000097394426018000000000000000000000ff41af8eac00000000000102000206e07e000000034e60000000000199612bae7e65e931a000000000033a83998000d0c00000000000000000000014a400000005b590626850000000000064c800038700000001c44a2c935200000000bc00001e880007a908f41970000a152f10adc112cd22a0b2580033485789a20da00aecf425e09c899c600020149b680007e989d480282ec591087ca540f8aa6b8ad65979bc0079b2ba0702cc26e19dc800000541c503c0000269e0000000000000000000da10c0000a430000000158659b8000000000000027be0002e92d110f22ba580003b1000000000008520b7e000000000009e4aed0000c6ca60000031886b0ad167c90d005d10366941901e97e800006722705b522a0433000000001840002c988068000000000000013faa241576bdaa8a894d3284b61251c0df9b7c000298e08c2b129c11f0e942018084d8000b6bb4ac468afc28200000c911b6200000000000604098000000000000001084000000000000004d2000005521b49a8163222b1104c310000000000000000000002ec60003484635a9de1efa666c6f32fa69c2554b402248c5c80005b100004dd27708d6a1180000000858000026016b80000000000051a000000000020240ed8000000000000012b23a2000078134d60002cd083a80000000000d420f9c4b1a396cce80000000000c2ca962b1000004f5021400029da0000000019a058bf202e0c7500000000000aa189ce0000000000000000000000000000000000030db4e4000147c0000e520e900000000c7641f83820002fa226e1b9a000000000000005e1190225880000dd04880f287b86f7ad0e9fc8ec00001ed600000004a10ccc010922a18800009ca30e42fe98aec1809cc8c91f9a6d632a40002550000177e9e8800021780006bf0e0a00000003768000000000000000000000000000000000000000000000b6a1bd
  | 52 => 0xb4b00000002f1400000000000d66c76000000000000be00b4000000000005a60ba0d349a8b1966a80000227000056019cc02380000b380000000000343000069c8000c4a3350279877e2079536000069c0b5a77200000001ec17bc962000054c8000b3300000000636000000039a0000166b1822a18ab6728807e5c50000ccf000000000000000000000000000000009b18a96cd7000006c944084200000000ea0256075c550843a0d0a3740000000000081000000000002b2439bb30a14000c200012f2ccaac6637e31fc89f089048380000c91d623cc00001d38000d1c0e8496f0406420aa6800016c800000000000de800014800c80d127beaa781ef22a4b0600006400000000000000000006be80000000b1a4db920072907cac7896a4c2e2b7c2d0800000000004e1002a0000000a09040e0001610c3e31a00a80000a759eca00020860002fbc0001a9e5132e10000053a00000e000000000001a520001300abd00000000000b6a80004a50000664149200009f26619ab68eb0000a3700002a105500000000000000038300002c0000037733566002f8800006dc000000000032ce2dd1c80311827600000009e0000071d94c256c22cc085800000009c0000000000000000000000000351689180003f9800024085c600020c2000000000000001a786d69e58db400000004b50000000000000000000002fde5260c9a00000000000000000000000023025e280441dba418000000000023a20002ad6553209e0000000000009e0000000afa0c4c96a800002b10b244a10100000a1a00009ae000000044720602fd090455a90901fb859689832ee000086842780003e917c62be16f400013f6214800053f8000064a47a1be0000000000000007da0f1000000012f840b21be000000000000001eb00000000000c76800060300000000d50ad291ae00000005980000000000093000007da00000000000000000074e0000c9486480002d36a2999300000c14000064400000000002e380000e5a38f0b563ee0ea83e8944e80f2abcb66850400000000000000a19800000000009b60000b581d6a056b41c00000000000aba00000000002aa400028ee000336cb9581d22db80006e906c4555000000000009ea0a220000000cc00420966959842fa8bcbca8100cad34023751f8400000000000cca2f913ba00004e800007fa0000e92000278e79ab44c656ac945bb940400000005ab9a923608000bf998f84f49dba03211c600018e200000007be242019523ec0c893bec9d800000001ce609000045a0000b470a6e2c094489d815f41e112261b9914a0a3197851711d68a6a48ca8a00000000000ca734104b280001f88ae00001ed00000018927b1ae000000000014d82b1026400008e64832a3ec07000080c000000000000000d5abdc0000cfa2bae00
  | 53 => 0x1f4618e8f2a39380000000000a7880007450000000002e00006c200000000002074596800041b800000000000000000000000067a03e400012563578a0438aadc20000000a3d000000000000000000000075200014e2000000000022a89fb06344550f8257b8cf06fd871650c1f5090f000069900009ab00002638000000000062b17308e29770000000064a0000375916496700004d9000000f000000018fa0000000b390000c3d04640001cc2d3280002d324bc0000000abe000000000009d4827c00000000002ba82c5849875280001d1b1be00016da72684a07c780007ff0000ada1b308a580003fe00000000000ba91ce8049127a30900000000000343800084400000001be0ccdadee0001b4a62f24c60000128000000000014bcabea58286b000000000000000000000340c0000000ca601c600000000d58000000000000000000000000958910ab728000c87ab105072fb6b4c0fc20001ef443c0ca64cd220220f9e6c0002cfe0001efe00023b40000000a7e91b402e92181e6a32e7569ff68a227e800010ca00021a87549a3ca4db368a642cec672ab3e97d00002ea0a4604f22b0b3521d05c98000b97815e0000b5a000088c000000083580005eea4fc93face039000003d1affe00000000002ea00001e8cc5900004da000041b322871b2044cc980005ac118c0001c0c87f277cd1f2a2e0001ace690800080a80000002d6e00010ec00021740000c8c94983cc00000000000000000000000017549cf2d0ca9314d60002c503222a0c7fc87e45ff2facb0c960850b8dae16520667519e28553800011200008e0000000000000001bae00020b68ef80000000000a11068e00029cabb89e164220cb2b3e16c6732b15813134a4a04172a8321bb6a6d34ceaf3148a0002b467182e884d19bb007f000000010804948000a939e78000168a44b8000000275a8932768b2c9fe64bd9b2c00019261eeaf9a6bc0000000087e30780000f6a2c6b81b42c906aaac00026ca62380c69ce8f2029697dc04321fa5f3919869018cec2f9e741e49456b17800099da9043abaab08130000c748000613ab9000033ca8f59c3600000000002faa000000000031900ae0000657a13c26f26208d780005b726f800016a2a3e000000000007f280001c408d2c61b12a2bcb38808ea9144b8946400034f83d4287a7a38198674800049a8000000060c0372b6095e30742d3b23635605da000000037a93e8aac829c00003aa270a7da1c00344000000000032542e280009818000000137200000005fa800028d0f14b928000339928e0de999400015b20002ab6000223c3c714f600013b827b800000026a68fc93120002052ccc80000000000a648000000034c0002c2a0000000000229406209ea1cc80004c60000a0fb1c8000000023b00008498000cfe80
  | 54 => 0x13e1bfa3a9800041c0000143800000005a2137280a0001d326bc800000000008be000027f8000051000049d00000aa8000c228f788b20c2ea2932c2930b2680001f663d61688651221cbabaa8c0000fea00000000001eae0001b229c68000000244200000008f380000bf000000000e45ec0000628b16800032f083b83542a09d7cd1b1f72b5cae8e5d3000013e8f4e34a0126a61000098a8b9400000000000000000000000027360000000000130a00019eab298014000279867629c217592780000b521710000cde80001c29ab000000006db20fc16230d8000000000000000000000b7180009eb06fa7642ad00090bdc2068a36552983058c08dca978000c638efecdb82daaa6b47800000009df80001489992686015c2e2285c8252a6456700000000c940000000000000000018e018b000040eac2c58d01b000017e486c80000002cf6afb0000b800000a3c80000000ce827da2587638000bb20000000000020600000002a320001da245c12eaa191ef08eb8caa5728000000000000022d6794800000000000000000c3380007860000187319a4ca2ea208380000000ee01ca81780001cf600000007158766cdf1942c9c80003210000000000088d80000002eee0000000c2980006d2316c98124626b59c2e0000000a468a3e00019fa2850a12000203aaa231d619320e6924000095312965f82d64d07a13491c000010f2168094a1563a899aa000062600000000000000a3100006829938b83800017280003c10cda00022425571f3c00000000002d1a5e60000a6980000000000000000000019800000a9a0000c0600033900000000a4e06282f500003d700006fc3380000000000000009b2167e0001f100000000cb50318cc0a5601c78108000000000014a084c13d000010b84c380000e60000c431184000000000000007448000000000070ea954758037c372b4984280a0000000000000000000000000006765cd1db61a09dca39ca46ab1200000af8240d2a040c00019f00000000130000000028de397ad20d3d253e000096a70280001c200000001de0b7e8d6c6570ecccf614843ae9f880a009b673334d427f05a0d019674a15b0fe5679dec57723980000d4682aa34a8989b468738000c17934c83800006210c2034500aa61015040000000000348e8041d3600012de00000000001568000208a000000000000007ac908cca58000000350a000000097101a68c00894afc0910b9721fe9f10c1a10b32667891c6273f12a6b8eaa1a5741e64d4b25accfb0000000259276600000002ad800000001a621a472a000092591d05730546521a85ed1180000000000000103400000004d280000001f0421a9d7a00024f400011fe00000000000000b3f000000029a2000000000000003f211b6000000062c80000000000239000000000000
  | 55 => 0x82e25ec28c800000000005e214cc0002f3e0000000b588000098acea14e18ec55e1fc636908307b802c000000000002b7800000000001ac0000000000012480001c7c2661fb000000000003404000000000000000000000a1b29fe0001e363af8a2e00000006ed051e74f95a039d3028861b110c199042631add8000000069100000000aa09a4800047a9dead178000000223eb00800000016f20000e300000a48a681bc2bc0800000029468b11c6e0000000a478000904000060f007c0001b94000237c76500000002f9e0001a0c0c700000001c8e68d25dccfa8000c0690c657f8000581b3de000000000000460638000734800086d8c48ba6af6ca070000cd287967d910ac2021fee00012b69de8000a1814e67320000185a0ae000000000000000000bba00000004e30e7ab07800000034f2000000092280000000000000000052433f800000000002ff60002e90000074ac148000000234eb52217c9298fdca7c2a0000018d200000000002c3a000073c00022e266106d24532bb85ac82e60000d841928000b5d80000a51b1e66da9b619480000000000c0d0be60000000000000069200000000000229a00851695ba6988000b1526b443e000000004d8000205c15100000000000a271f5e000000032e0000bc7800000000000000000000000000000004e209ec00014a60b7800000000003f1097e4388000000310800e1a2a00000009180000048b2ac1f100005891ed4cdc00003dd0000c1522de00005f07a20036b0a1b420000000af10dc00001f8600003bc60d8000ca80bac0000000000000000017b20000000ccc0000283800016180007388000000000000034f6c0480002f60190b9e18589980000000193a53c000000000000000000d0e85b40000ec6c7fa2200be800000000f6000000090c80008b00000b338ffa00026c4af980002fc85721e782d019aa17200000006f4a8840002586ad0800000002348b9341809c1350a910b9a3f8800000021120000000000105a58f12d29741de600000000002cd82281e6262a80003292c84924aa4a11c0dbcc4d02cac781cb20002fa602c8b5e31f0a400002f228d0328a449238e93c0000000274c6fa80000d180009db00000000000c6b2d92c00055687ca1667c2085800000000002af600001948be80008b286e20001f200000efc919a19823c0000aecb21689132cc4b92e620001ede0002b62000323c3fb8ab25e580000000000077b2b835497a005f8000000000000027f003000000000000cef048a0001fec000000000000000001e2eb8f041000003485628468b751000cff90160000000000000000000000000022c20b1f225f053c41800000002d1000029b80002c00be4abce0000000c4e30da1e800000000000ad6000000000000000862173000000002b29b3335a8ea80000000
  | 56 => 0x1b1004e976c77e06ac00031f48190000392b45c7659a6a0002b5441a80000002072000016a000187e0001cded2e272603a80000000000000000000000000000000679800000000000000000b9b2d986f5800000000000000000000000007a00000000fd2cb48000abc0cf4000000000009be60611a6000000000000008bf2da06f29f3207cb0a088626020da817a00007ea4b20f7c000000050391dc000000055ca78a7a8b4e069d152407c000014a894200001c483400000001d0e2998f546b313908dc13d65900d360002ddc9f71b1c6d918eac529b0806180000002b3400000000001ddc000050c016000057c0f38000188c8542caa00011f471f8000775232600024c40002b3aab99f26000000000000000001caac873004641060200000000000bca36400009491e100e533fc78b04e00000000d2880007e2b0dcd23313c00032c83c0090a00000000000000000107200000002b1aea813f2ad4bde000075385407ef204ea08ade20000000000000017b8d7c0001c220002cae48530e20000a2000003e600005d84c7800a3898c5e000000092500000001fda0000000051800050a800000020360000f9a00000000000000000000000000002d10baec83181c00000000000000000000000025b800000000001d68ccb8000000279c000000000000000788b98000054a4ed82280eb042ed2783b2252800000012e0000090ec5808fc00000000000000000000000000000a92980c0500100000a3a000117288000009fd9aa6be914b23ea80000000a2c99e92b8439095234402100039014000270a62525847950736b71063200017da34ca73e208322c38c8000aa0828e161189c9979bd09f2b13000000000002d9ca0c8000828a88a00000008aa9afe2bb000000000000002e4e0000000000000000000006b100000000e44293b3760000a2853495fc0a480000002cde87b00009d3800000000000000000aa6000000000000002b48a7a889e00029786a10000aaa0aa4867aeb4000111ec81800060d00002981f3a5950000000000000023d4347b19c0000000000000067e32dea7d0000000205a6df800000000000000ca80000000349800000000000001c0643a0000000000092e947e89380000000000000327c0000000b489cc020919a800000009f1800012680005f000009fe329e953a06a0002b0c00d03eeaa480000000ba6000164abdea92447c8ac25f4870ca4e80005a0800000000000001fe20bd26842e580007211a9800015288c781aa000302ebf5000000000008cb00000000000b1a90ae000000000009440001c2cce798260002764149000000000000000000943328e9bd1ce4bcba710c9189ba9428be2a1332341292edea8233e21b3098ab2d0000acb14c6a6914e8610915803ba0902c2156651c843ec6e8876a9b98c20000000
  | 57 => 0x1e2677400000000000000057800001700000000000322628c000025682e40000000c80ac7640f800000024a80000cb600000009faa0ec0000000000000000000000000a584e90c40c968000ce580000000f3416c80000000000b7a805000000007608f1a00000009959c7a44c800081400000000eb252d1c4800021f8c92800003d325053530fc1a4055aa581bdc1ad8e6ab6c9f7ca6f97ac2f300005bb18280002ba60000882b119b2e0db326a6e11edc14602742b88000a4200004f38c8a8fd961e65f0a50d2a800000008f862e800017812e6d29b26496a287e05b80000001a508a305480000000000266a000000020117467da8000000098c00000000000000000000055e800061580003ef0f3acdd116a646005a000000015d161611f136c0002b0ebb4ace8bd2304c6fb0000b2d800000010d000000000000000904802000028b60000000000000000025a0bf380000000000aab8000000000096880004ce8000000047215b226c0001144b3020e8000121a0001d9e30e000000000004c100a412a0000037800000016ceb7c88ba000000074f0000000021c0000000c321e508f0173cbb3000000000009d78000c1f800087100002cb000048a146c000000038200002af11cc00000009c33006a1d920a00000007c320c05d6234250e000000000009a70450d12a3688e92a3a135210e000289e000000000000000002efe00009d00000000aad000070d10b67c50c808481b9c24504320d8846a00000000001cb8913913e000176a00000001fc9ec81f58000000227a000000022d1efc736ab82502ad8e000000009a8088000000000016584bd0000000000003480000000000000282600000000002b8a4f2ab1a6b983060f4a40400022d400031d06e300003c9204219e0000589a3c60001cee000000000034f057b214600014e080a000070c2a500000000cee8000c040970431000000000001a880005d833b400000009439a00c2119b4000000018380000001b7a00028740bfae2200034ee9a61f2c00025e4000066e000034e83f822c259a7a04ff8ad40000000b1280000000a160000fde000055cb9a80001bd1396d4d061a46482b02d40000000000000000000001a4a000229200000000211f2e9021a2836180009b58000b2f00008c389904e28f6e38d9a960cea9169cb040420c9b26000000000014baaf0a17003322404600e48000000000008c4c3e800cbf305f8092173800eb32c62991203deb0d4ae5000079293f26aa8000b0997aab5f829a00000000001ae400015120000000125a8e200000009d08000000000030d182e0000000000198e3fc000097c000000008a4000000010a3016000000037ca2227fe000044c0000159ae5ad270000c468b2000000000001e860000000c9fa72400000002202aaa000
  | 58 => 0x22be00000000000000000000052680000000000ca680006d512080002e1e000318aa880000462331cd1905e6633000097300000002bc064492c0b72250023b917c755267c58880003a09aa8000166a00003ce00026dcd18800091a2d040000996a502178bac0af00000000cbf8000000000046925028f400000002f0a00033aa6891a9400013ee0000000000000034b80006ba99ac6581e00458242aba5312200000008c510767db8b8400017c80000cf60fd978e00000000000000b0fad4697e0000000000063d320400013f4b632d9e0000000000000000002a800000008f8a25687d800013880000fa3068000000000000000000000000000000000000000000a54800000000000000b5458e8000995284a04c9f2a0000a700000000d3b14d0000000055231fa00000620001e340000e1200000004c3033cd4eb304afeb1e400026ec000282c3020aeec9325c60000000000000000000000000000000038a00020a48b0800000025da17d80002b3a31ac9b1b24029a1e42f180009ae99d00410000000000000000004ba074c00000006290000c090cd088aa1cccb6991e0000000000000000034880000000a32000079d823c6e9a8781e200000000000000000000000001cc2c90000296ac0f1400000000046a28ceb9e80000000000c9b8000aef0000000153e4f017a66ee9dce8cf06462ad121e0000dba00026108a1283c0000000000000000012be31e00007e816bc97b80003e600000000000000296e00000ca800b3b0000000000027469dd1bac0001b1a000000057c80000000684557851000000003280000c84800000034b695c9848067900a8ca29e0776988a3d00000ad3927e117131666e2e60000000000000005a1838800032b27a78e703c22d068de104a00027ded2c81e0ad900003df80002e82e325e48000000000000030aa2c280000000d6026c98646040000000000000004fe36dad6c8d98000045179a0000f7611d06b2d088ea40000d923a2ae541741dc4cf5866800000004102c9eb3899e400012aa0000000c55000000000000848000000224a000000000000000001032107a124d050000565a01c0000d1c0000d685f50000000000000000000000000c598af42a780001f20000b8c193438a00009752fea8af28ac3aa86103a68000add0000235a8e433e00000001c200000f4c178a182000000095b16e697283b02540000000013643a8000be5b3e6000233e00000007f4800000018380001ec00000000000000000000000e596fe000000075900120001f780002c06000288891b80009a215401a000001b69d7e00009a4261833e00000000002aca51194c00000000000000071c00000000f86000000091c80002c526460000c2cd2595be0000aeaaca0900000145400000000000000cd210a600000000000000000000
  | 59 => 0x60000000000308e6882f62cb800005778a5279bb1ee0002e745018000c6d000018c0000a4880002a006aa0001dc6c1422fe000000000000009ee913a21c98ca7248000678ab0842593c20218480000000099d311ea1b80008e8264400008b0b73892252c2cc80000db875b0000bb2ae9e000022e000000000000000000e460fc0e8c00015c4983a7b4a908000000000078c240e00032e20002e2e0000bb290980000002d3a0000bde7051ab400033e4abf8eca2c4800047520de0cc800055689842af800000000000000000000000077a0f7238813b20351c0e0cc2e46ae89a1c13d0000d331c6683d19664628dec00003d40c2223298b044e44d9eaa000268a374227e00006ea0001e2aa4a9a68ad700d603eb502116800002f800022624e4594a9560ca0d381d920620000000c7a82000000000070800000014f48c41a8090b0000bda241e0c98000af71ebe4c200005b6311c10e2a48000292e6c80400000000079f012047b00000000e541a90cfa4938000542956c00000001eba71277300000000eb80000f0e21586f695e9270211b116a711752a6508e02dc000000000001ad24ec9700000619800000000005669a08a660000000269a0002fd60000000bba00005c1ab722cc000099703de4650f1eac02948cc40ee8000000000000000001f4e88686920000000bd5b10eca1800000021947e097d07342e58000000000000000000000000000090e8000847ae681b29510155185e0fca44a25d838e0000000578000051c255c559016c7a4a6f29e79b684ddac884a21fde639041800000828feaac6c1880008f7800000000000001c469bf1020aba0000000000000000009ec21640001e0240f34de00010bc764b22ec7983c646f9cf285bb3a627a000000000000000000bb50000000192e0000000000000000000000001d6e463800082f25900002df8052000000000000000fd60000000000000000000000002a7e000000000002ba0000000000000000000000002f440000c6e00000000002f2097a99221df0000000078200000b8000164e000000009330dea60ac0800000c47ca260c000000000000000001d2643380000002c1479c000000004cc12c00e2204852c0000000000000000000007d48000be09eba00012388429c3277dab6c00000000001aee000000042d0000000000000025d84cc989a199123e00000003b9994c54d21e200000001fc0000d490000b9ba920d1531f05fe978088b000070933e0115976e000053e72d115c00000001da0000000000000030807270000a0e00003989768a6a9272476968e088172c000000000000000000000000000000021160002c20000000061411565aeaff42c10a02000000000005420000a183f01518ba0000045180000002e2c0000000000000000000004a01778000063800008bc00
  | 60 => 0x1aabb000000000001e90230800045b9e8000000a87f5146200034660002dfe6cd2184000000096c80002fe24ee05c800070700003b68ab000013f098a00009cc8000000050863000000000000cd080000000000000345000000008c88000883233a000072e00000000002ed80000afc5d080007e400008f6ad40383a612000000000000000000000bfa0000000000000017c20000000000316e00000008ad0000cd8800038180003198000000000000006a898680000000f6600011c46b1996caba9370000000000000000002114c38000000000000001e8a0000000000000000005fc46c0f9ed4d8000147000000001524d3858aae7000000000000001d7288d334e097876a58b80007cf8000000213e739800038019a20000000b7f0000b182c0eb1f0b6ac15800012f0000d09800000000000000000000307a34100000000000d160000000000046818543682d50233a652c8a800090a0000a7c800001e25e800033b800000009cd33a003f1c8ac272eea48dae2070f9910a620000cc7800031906ce000000000000000d780007871202000000014d800000000009bba8f0453b0b000011fc2d008000002be29be800012304b20000000caa8000bf000000000000000000000000007618000000000047780000002f0c00024aa3600000000000067db53e00024880a28358b920cd4019015667c8000c3d9b566e799749ec8000a472d4c000000036a800077ba99a00026240001eb600006d0000240608133a4548800016025c80001d005d700008f29e6600009742782a06b83111639f975ac0e1e9819b00007fc2b2a2463528c26b14881a193600021eec6c00000b1a2f64ae8a5e000000058f8000bad94ca000000057e883a3f80000bf18b82824800004400004b6082eb2e0000b5a0000bfe8000000000000027081590000d3a82264eba4006750c5a2e40c86a4a00000000d72673a330000200e000000000000005232a26a4c261c0000cee0000bec000000000026c00000514d1206e8000271e41300008940fec1048000000000011faf3474621b80000b80000160e00024e61dd194a00000000000000628299e000000000000002470000000000064580086490000000092ca038000000036e07b80001d580960000000c7a230c6d68722000000000005b00000000334800050d30c28e21ad80001b74000000000000000002fba0002baa48c0f801e285c8000000070497e66daa97a14a167a9de3366c612a800000000000000037780000000000000000018f000000000006d031920000242000342a000000000000000000000000026681face6a529c54000214400000006520000000000015e8000000000000000000000000000006e3b09ba80000000b35a45a932856e1b800006ae000000000005790000ab21378b869fc0b2f80005d02f
  | 61 => 0x303a75723ea026868a0000844cf39eb4d03aaf223e8000000000000009aa9512cac37d92b063d800000000003af000000000000001f1200000000001488bf10000000000000011e66451eee0000000000000000000000001fdc91b0b2a09e8000000161a000000000005ae3f38db2a2000005048c1c000000000029ee67000000bc9d5069e2382079000003c23dc88a00005ba2ed00000b4a0000000bbf28ae086288c2db2d7ad4c8000b4980002fa000000000001998000cb4000019e8000745800000000000001c9442c0c2800000000000000000000049a0000000272e95983c8000000000009c474a18c800020a89cc00000003416cbb117e072869a0003412bf297e81d5000092185900000000c68a00487a21c274b932e7d21432472143a0000000a79029805a2eda000149c0000aaa9698e3816f19ee4980000967800024c229e00001bc2a48c3c09600000000da60000000d48b1a6a25a7a600011caa2e9bc6938b5300001004cfc80003550c9677e80000000c680000000000000000000000000000000132c00000006680f3c53b969c0000000000000035708c8d2188ea64800bc0000000000000000014a2000000063f00009330f5e00000000001d56000000000000000001d22000000000000001888000000000000000000001ab200000b6c161e32000000059b0000000000077d015800000000000000c2a1c9e000116cbeb8000a382bd2a8f2ee600026700000c9006d268ece703dc8de94525e1a05631d00006868000926000001a930632faf0e00006503ea21282a9957c7b984521339b60b7b0b641b0290a00003ecc7394a8bc01b02c542a841c9a516000261491721f003611bc72980006f6a958caa0426abb0000000283000027765aa800074813a209a00000000000000000000000007f39fb600021a215f8000b478000ae799dc81f0dd20001a8800000000c000000002622a7f00000f40000000305a1db0000abbae2a00020d4bbe8e1ea3f839a68196986ffad02712a648001b4bc000095695f1f02a5a1fac00015ac00023320000000000000071400000000000753171e5870e940000e247980000a760000bbe2a8a9d132220002338000000008213ac40a81fa0000000adb800000000007ac0000b9480000001e380002a7400000001a58c26000000079e8000000000073b00000000000b85800080b82dc0000f2e6a703f4c58a3e01e18000068977c6e580009f391480003358000100600022f0c73056a00024e0000255e2b6940ccaf1ecc22fa1bab08a2b842ea20e432016687212c40a8a4340000f647748000000000000004b44f88b7cab4880a00020ac00000000ea000041782ac437926246b0150009a9968c280000000458000000008a80000001982000174800000000de33066c10000000185a00000005
  | 62 => 0x36603a2000000039b2ae224c80005849ee2000000000000008410000b902520278906800024da000286870680007dc0eec65c135c000000000028cc8f2150000000000000000bf80000000000093cb02a0000000000000000000000000000000039e0000000000000000000004bf87ce7e591ba5ad2a960002f8e00000009f513b0bc610a894e189692680007eca16c6a6a55ab4d000000000001700000affb50e000085c00026f0000000000032147e500004e0ae1800028d6b7780000000d18000000000000000000e140000c0e173a6a413c00002d700000002db818500008bc80000002c3876a18e8000099cbcb0000a85800000000009b780ec5a4253cd15b20a2f100000002e6419834dc00000e8af80000000129c1c485d200000000000000421a64ad022b025c5940880e00000003392a2083d60002ca4d0c8000205a4e8b9f2a2442381d6c23047a0000000000000000005b64f1a21eb6b092004e0312000186200000000000000000125800018b075e00000271c380000c7e0000000000327082d0df4b62146842887de26b093c000119a0002c04000251289e193c20321dc0000272cd1190e00000000002422000000021b8000000175e0002e845920000000218a00035262d9a82ad0b800000000008f600000002cfa3b730706e003043780000000000083922ba000000000013dec69168ca7a00004ea00000002b14000000000004460000000000223874204ea0000000a280000a18800000000000000000a398e103338000910172e34f32945c020f60000000ca4a0880f8000006e80000000000411800000a0968cf000009f432b0525000000000000b60efa00000000002384000138006e00000000000000000000001a4d138000000000000000000972cd292b000054391c2a1c00000000d7400034403c5800000000007170000bb00978363a964c5e8000000000000011266812f5469583ba00034204fb12661791f4cb15a804b4628d43da31b64bf0000328886600000003249abc9eb8e02b25a89ab318e8e56f00000000000b60181640898d49559ee834830b6a6f157eae4aa04ce180006f6048e855123203e1ad4b7d2306488208e0000000076000067f0000b798060000223a0000000000216a00000004c52d94c343146000000011d800075080000000000cf48bd6000310a000000032b9c3c000000000002b400000000000000000000091780000001aae00000000001872000256a00000002ea9420a838000000000000016469778000ac10d0aadf8000ad6823660e8cd6b54acee00003024e393dc2bd97943e39f5800015301d08000d251dd6226a6feaf6afb0b2eb4765bf23e874a901aa0316a80e0000057a158c91580000003156ca40000c5f97cc000000080880000000000bf9000088995085c41f8e00020f00000
  | 63 => 0xa7c00013b4024301800027d200000000000000000000000032c6a7d9538826800098fb31a26985de00000004840b467dd800000000000340000000000047e00009f32f460002e8a00006240002a540000000815000000000000001d8a1561822863b5146dc08f60000000b8284f25fd20da28e000066c2c7e00000000000e9000014fca6b0e3e007148eaf4000017d0ae6137ad740000000d4f0000077020a0831aac78495468748fe496e907cade80000003100000343400029dc000000000007a830880000002c0a7b907b645413cc8d1000065480000000000cc51732a13aa103d22b86a4b2ffc6fd261e00000000000000461800000000000002d7c9d0000000000004a401da5b7b3c200000006e8ac7a750100e0001ff41f01cea0000000cc800009e080001198bb6000000057a9e3ebe524b4000294200000009789af400001f4c08040a98c27fe9d5172496d0000ac62e5084b22eed06ac100002f640000000000000000023b60000000000000000000003798000d029b8888280000000000be712ac1481e5a34a9bfc6e40568297000009e0000ab70df0d46800049780008f0928a3dc04d066fa43850407907ea02961e71a760000000000304800000000000000000000094e8b92a060000bd48000d0033082c9115a0001b4e02c1a5a27e225215880003f1823800000000000d220001c861d880003a6000000016724ab8aa882ea6f64df80004d980004ce0000000000000000004452b4000022aeca31d800003482c9600002f0895e6932c425d291ce8c80dfc7829ec2275a454a860dce9c59b7659d958e491800000019bc000120404a9656500807a46e1c5e0000000c710ef6000160263600000002b30000000041417763f2800000013bc3e40000aa39c7284000000001d661f32536000000000000000000000b2881be511204a00034c81bc04b695624141828a624cf11c0014a39e00034d208c800000000000000000000000000000000000000000000000000000000a2400018b43cc8d1621810dab898b723eb9fc2b239ade00000003b580005562fbe56b8000000011a667a36400000000000000000000000000000000000000235c000000000000006c334c00002f26000096400000000002dbc000000049700000000000000000044021d60000000be280000000000000000095d0000cc89f7e000084a9ba26389c014b802005765f7b0bc91921aa688a4d04380000000000000000000001940533800076821f458a8000373000449500000001b00000000029e000052780006b42bb6000000000000000000000c6600009aa00006519d8854a8bfec4c80000001f22000221600003900fe00000000000ce3a140000010a00000000001a860000000d318000000000006b0000d16800000022f4337a4ea00010d200009f08f90000
  | 64 => 0x92380000001f602130000000000000000008e3020600023a600001cc000225400000000a198b60000000000176600000000000000000344279fa084000000000034d00000ac80000000000191c61b1fa2000061200000000000000000000060a9cbe588257600000001708000000049400004340000a106f10fb6474b33e68d8000265000000008a80000000000193e0001bb2b640000ac78c822648ed80002394b57000032d27aa00030884252b440002c2e00000000608000520800000000001088000b56b23242a80000002352000318c00000009f000000d9000048b1ea605d800091f21e051d0000000000000005267a50000744000000000000001fe013280000000000920150c1f180005a580003139b0e30c163800000000000000000041a0000000000109a56a8000000252268b004a0001c0261f0094afca5040000492b1e000022aae769f08000000153c6fbb0d650500005fc000000016fa573b1743c40e181fd288e781aa2c985ac4e21b1d844f61d020ee151e49b908a0001b920000fa01f70e964b680000fe8000bce835a06b80006fa038ca989bbc7f42da20000ce000000008602dc000034c2366a5fe0000000000000000017b604d0000a5c9b5c000000000026e4933800079c99620000d940000000000000000000009a1b002000268cbb38000bc696f80000000000000000014dcce8a4a2829800076b00000000ad272d8000000000098f10d8000222e00000001f5244c14c0000000240a00031a8000018c0000000a46000000026ae00000000000000000281210aaaa099a182c677896069e8000208ac628da9870c1b00004df000025734ba8530d4c0000000000000000009b4000000075d80002b401f606a2034000011c77c919c1d224d84162b9600002ee2050c7218f8000a2880000000000000000032782aeb8d180a72612128e400000000000000000000000009822c8a0000000b4f8a1c0000000000000087782020000000d472c3c0000000000000000000000000000612b3da00010a400010ee0001f9800000000002b20000128c7832c64b6c317c000003000007e001b094c83180005dc9182909000043d1f348658000000288600025b0879800000015c60001a3e0002b8ea570000000082a000000000012ce3cd8cd825e80000130000000000000034da4f803ae801800056e00003d284a662495828d59a6cd4a90d676f01b6cba20960000000864800000011e000000006b4aa6c96005eca3a00000000f6a00004145c633849ba8000000000000000002c3800000000006cd85a8117ad669e20000613298c00027fa0000000000000000000000000e5c00000000002ebc0001b3e0001a025e080007851be4ac1800034f8ed028f28fa71d000060480008ab0854000000000031de42706620002b849939da4000
  | 65 => 0xd20123400000007f124b270128060000d7684e98d0b6980004de80000f625143cfa8f6a418acc8640000414800068e00004e68000ab122dc0002b16a2aa05e00021323708314852a4841959cae0000dfe3bca9868682ebe000000021c044445d00000000d888ff81fe807a6349162df
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x86254430c45651cd2108430d05541cd2108430a3281d506050f20a32819946050f20b058114d434cb20e045350c614cb208648758d5108720d047350d5108720e056350d5108720a1681d516310320e11635454010220b11811d5434c220a15831516114d20a0d8319662d0d20c24651c56250d20c28651c16250d20a288550c6050920c0e655cc548c920b058114d434c920e075414c614c920a2685d0c614c920a248550c614c920e045350c614c920a1583151610c920a0d83150624c520a458614e3188520a288550e6088520c897350e60885208c9831c16408520d07541cd5108520d04541cd5108520c187558d4010120c89631c94010120a0d83150624c120c18655cc544c120b0a859c9434c120a88865c9434c120b08855c9434c120d08755c9434c120b80815c9434c120b088550d324c120e086550d324c120c60651c5324c120d81431c5324c120c0c7558d4388120a248550e6188120b088550d3088120e81439853088120a30815946050c20a29851886050c20e09531886050c20c0c7654d4348020d09545cc4048020d21545c44048020c187654d4348020a2a82d506050f10a2a829946050f10b058214d434c710e045350c624c7108648758d5208710d047350d5208710e056350d5208710a0e82d516310310e09635494010210b09821d5434c210a0d831516214d10a158319661d0d10c24651c96150d10c30651c16150d10c19745c06354910a1583150614c910a4483548614c910a308550c6050510c16655cc548c510b058214d434c510e075414c624c510a2685d0c624c510a248550c624c510e045350c624c510c4473189524c510a0d83151620c510a458614e32c8510a308550e60c8510c917350e60c85108d1831c16408510d07541cd5208510d04541cd5208510d07741cd5208510d04741cd5208510c45861cd5208510d06841cd5208510d05841cd5208510d41801cd5208510c4473d8d52085108648758d520851092687d0d5208510d0473d0d52085109248750d5208510d047350d5208510e056350d5208510c187558d4010110c91631c54010110b4083548218c110a1583150614c110c18655cc544c110b12859c5434c110a90865c5434c110b10855c5434c110d10755c5434c110b80825c5434c1109188750d524c110c187650d524c110b108550d314c110e106550d314c110c60651c9314c110d81431c9314c110d127550f214c110a6086548214c110d4173548214c110f0143548214c11081d831d85448110a44835942148110c147558d4384110a248550e6284110b108550d3084110e81439893084110a28825946050c10a31851846050c10e11531846050c10d09435ca504c010c147654d4344010d11545cc4044010d21545c84044010b21841492044010b41831492044010c187654d4344010
  | 1 => 0x1c857418f3248421d05545cc5448421d21545c05448421c25759d06348421c25755d06348421a85849cc6348421c61759c06348421c61755c06348421ca2745c06348421ca1745c06348421a618018f53484218e1801da5348421c857418e5348421ac18018e5348421ac18018d53484218668798d53484218668718d5348421a618018d5348421b058418d5348421b418018d5348421aa18018f4348421a248654f4348421e046354f4348421c457518e4348421ac18018e4348421a448654e4348421ac18018d4348421a448654d4348421c447654d4348421a8686dcd43484218a68798d4348421a868398d43484218a68718d4348421aa18018d4348421b818018d4348421a868718d4348421c868718d4348421e058518d4348421e828018d4348421a858018d4348421e818018d4348421a818018d4348421e0463d4d4348421a848694d4348421b058594d4348421a248654d4348421a848654d4348421e078654d4348421b068654d4348421b048654d4348421e048654d4348421a048654d4348421e077654d4348421e047654d4348421e055350f6048421a85831912154021c0d739c86454021c0d735c86454021c15739c46454021c15735c46454021c19735c06454021e21644855014021e41634855014021944835d52108640ca1725c46050d40a45831952108540d09535c34394840d09535c34354840a1b805d95390840c19535c26190840e09539496010840e09535496010840a198099153cc840a1980191538c840d11535c34394440d11535c04294440d11535c34354440b2180d0d5254440d11535c04254440d21525c04254440a1b805d95390440c19535c26290440e09539496010440e09535496010440e11539456010440e11535456010440e21525456010440a198099153cc440a1980191538c440a19801915348440a19801915308440b09821c15350040b11811c15350040a88825806050f30a90815806050f30d05431c55214b30e05435496114b30d05431c5520cb30e0543549610cb30e0943549600cb30a6081549600cb30d05431c95114730e05435895114730d05431c9510c730e0543589510c730e1143545600c730a6082545600c730864875952108730e055458d2108730d047550d2108730e056550d21087309c1801cd2108630991819c26250d30c18655c06250d30989829c26150d30c18655c06150d30993815cb6050d3098b825c76050d30d81729c46050d30d82725c46050d30d81725c46050d30d05431c55214930c91435c66090930c91435c6608c930e0543148614c930d05431c95114530c89435ca6090530c89435ca608c530e0543188514c530d047550d2108530a19809516310130a0c825516310130a14815516310130c9143dc562cc130c8943dc961cc130a44835846154830a448358
  | 2 => 0x806014532c51735806014532a858494c614c832a2585d0c614c832a278550c614c832a878550c614c832e078550c614c832e057550c614c832c847650d3294432d05431c53254432c24769513254432c24765513254432c847650d3254432e077650d3254432d047650d3254432e047650d3254432d81431c53294032960874c95194032f01434c95194032d05431c53254032d0b7550d3254032d22541c53254032d21541c53254032d81431c53254032960874ca5154032f01434ca5154032960874c95154032f01434c95154032d11431c53254032f0143dc53254032d09431c53254032f01431c53254032d23431c53254032d42431c53254032d21431c53254032d41431c53254032d01431c53254032a28825806055331c15739c46454231b0681dcd431493190d831d16014931c29745806014931c49735806014931e0943549600c831a858494c624c431a2585d0c624c431a278550c624c431a878550c624c431e078550c624c431e057550c624c431c847650e524c431e0543189524c431c2476951524c431c2476551524c431c847650d524c431d067650d524c431d047650d524c431e047650d524c431d81431c93194031960875493194031f01435493194031d05431c93154031d137550d3154031d22541c93154031d21541c93154031d81431c93154031960879493154031f01439493154031960875493154031f01435493154031d11435c43254031d09431c93154031f0143dc93154031d11431c93154031f01431c93154031d23431c93154031d42431c93154031d21431c93154031d41431c93154031d01431c93154031b098014d434cb21a618014c614cb21e045350c614cb21e075350d620c721c857650e320c721e135350d600c721e81438c9600c721e075350d610ca21e0b5350d600ca21d81435c0328c621b118014d434c621a618014c624c621e045350c624c621c867650f324c621d05725c45350d21d09725c05350d21d11715c05350d21b098014d438c921b098014d434c921a618014c614c921e045350c614c921b118014d438c521d067550e328c521e066550e328c521b118014d434c521a618014c624c521e045350c624c521d047550d324c521e046550d324c521b118014d43c8521b098014d4388521d04721c55350c21a28805946250c21d05535c46250c21a30805946150c21d05535c86150c21e055350d610c821e095350d600c821ac0835c5600c821d057550f32cc421e056550f32cc421c61655c032cc421e055350d620c421d057550c320c421e056550c320c421d81435c0320c421e115350d600c421ac0835c9600c421a6185cc9600c421e81430c9600c421a498018d5348421a898018d4348421a0c8654d4348421c857418f3148421a518018d5348421a918018d4348421a148654d434842
  | 3 => 0x2a800001ae1f800c500058000769980000000b2a00320b9800bb8003db520000000000001884317a00122aba62d80c4983069f8f89f34c0000000000ae8007c1b2918be7f13c231bcb7ab07ba7262b669a800723020011a000007a0000025a6e136d9000400865500091000a91a025800001307100000000000004e02a9003c0b1aa36252002fe0000000194608006c1760000000008002a6a235c0000044904a0094558ea0024a000000003200000b000000000640000000000000000000d1e0000a83580000076db000000000005c288000033c0000013800000d0000000000004000972d00020a70800000000013a1980000158b20000000030a42a3000000000029a002843e8009daec3b0007d9f8b4836c2a2ea19e20c34ac206a00000000003c054bf31287000000000000000344002e42d80000362178000020000000282be000745480000000269800025000214000000004099800ce000da28e000000020c000000027800000000ca1a00000000000000000000000000000000097800000004a000000720000002800000000000029b180000000000002f6b3908000005a000002d800000001d80995c15964c403a2e800002d6000ee69800ac8000014a002e2000000019e00000a70000000005800002b6000007482e8c8000000085800d6a04000000000042a2488a3c878bc63258a400084af400322000008d0006a0f2000008db400000000000129267924e002286e90e950e6000000631abe27a1e248cb9ce492f06180067000000000016e83a926480000000002180003e0016cba0c08e020d380000000aa838000e2000000011e779c60240300000004040000101c0200006000000000000011020000040000000000070000100008000090000300001028020240600000004000140e00c060001002800018000000100000000030000100c0e00c02000020000100c0303800004000000602c0301c0002802018010140000000014000000400401000010000100403004000040300003004030140000001000010000a00006008010000a03c0d04c000340102403004000000003c0301000000060000300c00e09639895014343e09635895014343e11639855014343e11635855014343e21625855014343a8681d8a62d4d43a8682d8661d4d43a89831c16214143a91831c16114143c1b7658d5014143d09631c95014143928879895014143928875895014143e09635895014143d2072dc55014143d23721c55014143d20721c55014143d11631c55014143d22621c55014143d21621c55014143930879855014143d20729855014143930875855014143e11635855014143d20725855014143e21625855014143a30815806055332c0d739c86454232b0682dcd4314532915831d16014532c31745
  | 4 => 0xb4c3800da97851b36000000000000000270000023ec700000000000000011c000008c000cc0000021a00000002104ca06b70ce2b2823693e2408e7517445ab80197c000b0351a26106e3215ea8064538001401a0007a7318e51000770005205a0028a6f800cc8000000000000ce8005000000000001f23733eb68e84617e0001ea5000cd0000034600000200466d90600000212c200000130006906c728000013400000002f265800000621488ac5acc01000540280029800000000000000012000222d40000000000568000012c9b00000098d2060000000000000000248000000c331ec451d01100000000001eaaf1d600000002260000000000000000023a59800c792eb2800000009b8004a87caa00000000700000000000000000000000000268000000000079800000000024cd6000000000032600000d0800a8ae0a780050800001acdbb50390125aa640880000000001205c000038007f81c40b2cb1800000002b80044000000007d000278b2c3000c00dec9000108d20022abeb56002ac8b0005c800669b4000fc050c6000002e25600082000248080016000a58005300000000ba800000009d0e0d51faca220b1162820703d0a43fb049c2b4d78
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x2c0215444100028cba73a7cd183600a96141cf04100d68d00016300000e141e64005440071012312a656bc02024189ae50914800618808059520460261e004060221d635895014143e00b1ac438aa0282878108758d615405050f802c6392c2a80a0a1d0825d625855014143c1043ac4b0aa0282879008750d32546500cb2010ea1a6528aa01964021d434c95154032c8043a86a9263280639008750e524c5500c72010ea1aa498aa018d806405350c614cb21b00c80a6a18c498c436019014d4318532486c032029a863126290e205d18018e5348421b00c80c6a9e8690843841756006390d210874030b400c6a1a4210e806158018d4348421b00c80c7a9a86908432819021a5350d2108680d2fc32a6a1a4210c81a637654d4348421d00a1902a92c019661a01432095158031cc28092eb2a86908439850125d6350d5108720c0442ae6a1cc110a41808861d57250d30483200ea40ae4a1a6090540255431c5324c120e0032a8638a64982416009550e614c2204828092eb1a86a9043886042157350e60c8510c02c330839aa410a2184186600735482144320308c00e6a90428850125d6350d5208510c0243ac6a1aa410a21810861d57150d30443200ea412e2a1a6088540255431c9314c110e0032a8639262982213009850d52085304434010ca1aa410a6088580255439893084110
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 42
  | 6 => 1947
  | 5 => 11355
  | 4 => 6816
  | 3 => 440
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
  | 5 => packedAt gbK5 (484480+((h/3785+packedAt gbK5 (431490+(h % 3785)*14) 14) % 13627)*15) 15
  | 4 => packedAt gbK4 (365792+((h/2272+packedAt gbK4 (333984+(h % 2272)*14) 14) % 11974)*14) 14
  | 3 => packedAt gbK3 (27860+((h/146+packedAt gbK3 (26400+(h % 146)*10) 10) % 849)*10) 10
  | 2 => packedAt gbK2 (3575+((h/16+packedAt gbK2 (3479+(h % 16)*6) 6) % 59)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff87fffc0f8f8fc38e3fc7fff1c1c1fc23f49f
  | 1 => 0x7f83e3ff00ff1fc0fc7f8e07e01fe1cdcc8e7
  | 2 => 0x7ffc03ffff001fff007ff007ffe001f1f0f07
  | 3 => 0xf800003ffffffe3ffff800007fffffe3e00ff8
  | 4 => 0xffffffc00000003fffffffff80000003fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x30b08404611110008208c123304444c401548b
  | 1 => 0x51138848a326028c0643484552089c484cc8a5
  | 2 => 0xa2211c91460325159005920a649c0891170d06
  | 3 => 0x442122080800222890001009212102a00250
  | 4 => 0xc44630038c4c49bb4d26249c00303103faa000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeeafe80feeafe80feeafe80feeafe80feeafe80feeafe80feeafe80feeafe80feeafe80feeafe80feeafe80feeafe80feeafe80feeafe80feeafe80feeafe80, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12931
namespace PEqualNP.Outside.L_meta_12931
open PEqualNP.Outside.L_meta_12931.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bgb_3_384 : Interval gbAtlas 3 384 56 := block_range (n:=56) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 440 := (concat (concat bgb_3_0 bgb_3_96) (concat bgb_3_192 (concat bgb_3_288 bgb_3_384)))
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
theorem bgb_4_6720 : Interval gbAtlas 4 6720 96 := block_range (n:=96) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 6816 := (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_96) (concat bgb_4_192 bgb_4_288)) (concat (concat bgb_4_384 bgb_4_480) (concat bgb_4_576 bgb_4_672))) (concat (concat (concat bgb_4_768 bgb_4_864) (concat bgb_4_960 bgb_4_1056)) (concat (concat bgb_4_1152 bgb_4_1248) (concat bgb_4_1344 (concat bgb_4_1440 bgb_4_1536))))) (concat (concat (concat (concat bgb_4_1632 bgb_4_1728) (concat bgb_4_1824 bgb_4_1920)) (concat (concat bgb_4_2016 bgb_4_2112) (concat bgb_4_2208 (concat bgb_4_2304 bgb_4_2400)))) (concat (concat (concat bgb_4_2496 bgb_4_2592) (concat bgb_4_2688 bgb_4_2784)) (concat (concat bgb_4_2880 bgb_4_2976) (concat bgb_4_3072 (concat bgb_4_3168 bgb_4_3264)))))) (concat (concat (concat (concat (concat bgb_4_3360 bgb_4_3456) (concat bgb_4_3552 bgb_4_3648)) (concat (concat bgb_4_3744 bgb_4_3840) (concat bgb_4_3936 (concat bgb_4_4032 bgb_4_4128)))) (concat (concat (concat bgb_4_4224 bgb_4_4320) (concat bgb_4_4416 bgb_4_4512)) (concat (concat bgb_4_4608 bgb_4_4704) (concat bgb_4_4800 (concat bgb_4_4896 bgb_4_4992))))) (concat (concat (concat (concat bgb_4_5088 bgb_4_5184) (concat bgb_4_5280 bgb_4_5376)) (concat (concat bgb_4_5472 bgb_4_5568) (concat bgb_4_5664 (concat bgb_4_5760 bgb_4_5856)))) (concat (concat (concat bgb_4_5952 bgb_4_6048) (concat bgb_4_6144 bgb_4_6240)) (concat (concat bgb_4_6336 bgb_4_6432) (concat bgb_4_6528 (concat bgb_4_6624 bgb_4_6720)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 5 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfefefefefeeafe80fefefefefeeafe80fefefefefeeafe80fefefefefeeafe80fefefefefeeafe80fefefefefeeafe80fefefefefeeafe80fefefefefeeafe80
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124266 * 2 ^ 32 + 4278124160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12931.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,2]⟩,⟨.or,[1,6]⟩,⟨.and,[1,2]⟩,⟨.and,[0,5]⟩,⟨.or,[4,9]⟩,⟨.or,[0,5]⟩,⟨.or,[3,10]⟩,⟨.and,[7,12]⟩,⟨.and,[6,11]⟩,⟨.and,[8,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4278124160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4278124160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12931

open PEqualNP.Outside.L_meta_12931 in
theorem PEqualNP.Outside.L_meta_12931 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4278124160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4278124160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
