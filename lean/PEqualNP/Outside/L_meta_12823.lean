import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12823.Model
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


end PEqualNP.Outside.L_meta_12823.Model

namespace PEqualNP.Outside.L_meta_12823
open PEqualNP.Outside.L_meta_12823.Model
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

end PEqualNP.Outside.L_meta_12823

namespace PEqualNP.Outside.L_meta_12823
open PEqualNP.Outside.L_meta_12823.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x60001dc0e49c0000862023a2003276a7c0404a6e08c4ab9740303ac04a2149ad61a78558800e080041040210223ff43fe43fd43fc43ff41fe41fd41fc41ff31fe31fd31fc31fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x861ff410c3fc82187f50430fe20861ff310c3fc6218778c430fe98861fc310c3b862187f88430fe90861fc210c2fca0187fd0030ff20061fd400c3f880187fcc030ef98061fe300c3f460187f4c030ee98061f9300c3fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5887f94b10bf29621fd52c42faa5887f14b10be29621ff42c43fc85887f50b10fe21621ff32c43fc65887f4cb10fe19621ff41c43fc83887d90710fea0e21f541c43f883887fcc710ff18e21fd31c43f863887fc8710ff10e21fd21c43f843887fd0310ff20621fd40c43f881887fcc310ff18621fd30c43f861887fc8310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5087fd0a10ff21421fd42843f885087fcca10ff19421fd32843f865085f54610ffa0c21f741843fc83087f50610fe20c21f441843fe63087dcc610ff18c21fd31843f863087d0c610ff90c21f721843fc43087f48610fe10c21f421842fca1087fd0210ff20421fd40843f881087fcc210ff18421fd30843f861087fc8210ff10421ff10843ee21087ec4210ffaa2217f544437ea8884fd5110ff2a2217e54443faa8885f55110fe2a2217c5444378a8884f15110ffa9a217f53443bea68857d4d10ff29a217e53443faa6885f54d10fe29a217c53443b8a6885714d10ffa1a21fe43443fa86887f10d10ffa92217f52443dea4885bd4910ff292217e52443faa4885f54910fe292217c52443d8a4885b14910ffa1221fe42443fa84887f10910ff99221fe32443fa64887f0c910ffa0a21fe41443ec82887f50510faa0a21fc41443fe62887f8c510fe98a21fc31443fe42887f88510fe90a21fc21443fe80887f90110fea0221fc40443fe60887f8c110fe98221fc30443fe40887f88110fe90221ff10443f620887f84110fb08221ff54042fea8087f95010bf2a021fd54042faa8087f15010be2a021ff53042fea6087f94c10bf29821fd53042faa6087f14c10be29821ff43043fc86087f50c10fe21821ff52042fea4087f94810bf29021fd52042faa4087f14810be29021ff42043fc84087f50810fe21021ff32043fc64087f4c810fe190217e51043fe82087dd0410ff20821fd41043f882087d10410ff98821f731043fc62087f4c410fe18821f431043fe42087dc8410ff10821fd21043f842087d08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xd21087ea4210f948421ffa8043fe50086fca010ff54021bea8043fc50087fea7a07f94f40bf29e81fd53d02faa7a07f14f40ffa1e81fe43d03fa87a07f10f40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a07f90740fea0e81fc41d03fe63a07f8c740fe98e81fc31d03fc43a07f48740fe10e817d54903fea7207f94e40bf29c81fd53902faa7207f14e40ffa1c81fe439037c87207f50e40fe21c81bc43903fea3207f94640bf28c81fd51902faa3207f14640ffa0c81fe419037c83207f50640fe20c81bc41903fe63207f8c640fe98c81fc31903fc43207f48640fe10c817e50903fe81206fd0240fda0481ff53502fea6a077d4d40afa9a81fe53503faa6a07f14d40be29a81dc53502b8a6a07fd0d40ff21a81fd43503f886a07fd4540bfa8a81f751502eea2a07f94540fea8a81fc51502f8a2a07d14540ba28a81ff41503fc82a07f50540fe20a81ff31503fc62a07f4c540fe18a81fe21503fa42a07f08540ffa0281fb40503fc80a06f90140bf2a081ff53103fca6205f94c40ef298815e53103faa6205f54c40eea98815d53103f8a6207fd0c40ff21881be43103fa86207f10c40de21881ff51103fca2205f94440fb288817651103faa2205f54440faa88817551103f8a2207fd0440ff20881be41103fa82207f10440de20881ff31103fc62207f4c440fe18881fe21103fa42207f08440bf28081ff401037e80207f90040fd20081fd401037a80207e50040ffaa6617f54cc3fca9985f95330feaa6617d54cc3f8a9985f15330ffa1e61fe43cc3bc87987f50f30eea1e61fc43cc3fea3987f94730bf28e61fd51cc2faa3987f14730ffa0e61fe41cc3fa83987f10730ff98e61fe31cc3fa63987f0c730ff10e61fd21cc3f843987fd0330ff20661fd40cc3f881987fd5230bfaa461fe548c2fca9187f55230beaa461fc548c2f8a9185f54e30ffa1c61df438c3fc87187f50e30fe21c61dc438c3fea3187f94630bf28c61fd518c2faa3187f14630ffa0c61fe418c3fa83187f10630ff98c61fe318c3bc63187f4c630fe18c61dc318c3fc43187f48630fe10c617e508c3fe81187f90230fea0461fc408c3fe611877cc230fd98461ff544c2fea8986fd51309faa261fe544c2fca8987f55130beaa261fc544c2f8a8986f151309e2a261ff434c3fc86987790d30fea1a61dd434c3f886987fd4530bfa8a61f7514c2eea2987f94530fea8a61fc514c2f8a2987d14530ba28a61ff414c3fc82987f50530fe20a61ff314c3fc62987f4c530fe18a61fe214c3fa42987f08530ffa0261fe404c3fa80987f10130ff98261fb304c3fc6098778c130ffaa0617f540c3fca8185f95030feaa0617d540c3f8a8185f15030bf29861ff430c3be86187f90c30fea1861fc430c3b886187fd4430ff288617e510c3faa2185f54430fe28
  | 2 => 0x7fea020ff94041bf28083fd50106faa020ff14041ffaa6637f54cc7fca998df95331feaa6637d54cc7f8a998df15331ffa1e63fe43cc7fa8798ff10f31ffa9663fe52cc6fca598ff54b31bea9663fc52cc7fe8598ff90b31fea1663fc42cc7fe6598ffd0731ff20e63f641cc7fa8398fd50731fe20e63ff50cc7fca198df94331fea86637d50cc7f8a198ffd5231bfaa463fe548c6fca918ff55231beaa463fc548c6f8a918df54e31ffa1c63fe438c7bc8718ff50e31eea1c63fc438c7fea518ff94a31bf29463fd528c6faa518ff14a31ffa1463fe428c7fa8518ff10a31ff99463fe328c7bc6518df94631ffa0c63fe418c7fa8318ff10631ff98c63df318c7ee6318ffd4231ff284637e508c7faa118df54231fe28463ff544c6fea898ff95131bf2a263fd544c6faa898ff15131be2a263ff434c7fc8698ff50d31fe21a63ff524c6fea498fbd4931b7a9263fe524c7faa498ff14931be29263ec524c6d8a498ffd0931ff21263fd424c7f88498ffcc931ff19263fd324c7fe8298ff90531fea0a63fc414c7fe6298fdcc531ff18a63de314c7fea098dfd4131ff28263fd504c7f8a098df14131ffaa0637f540c7fca818df95031feaa0637d540c7f8a818df15031bf29863ff430c7fc8618f790c31fea1863dd430c7f88618ffd4831ff290637e520c7faa418df54831fe29063ff420c7fc8418ff50831fe21063ff320c7fc6418f78c831fe99063fc320c7b86418df94431ffa0863fe410c7ec8218ff50431faa0863fc410c7fe6218f7cc431ff18863f6310c7fa6218f74c431fa98863d5310c7fea018ff94031bf28063fd500c6faa018ff14031ffaa4437f54887fca910df95221feaa4437d54887f8a910df15221ffa9c437f53887fca710df94e21fea9c437d53887f8a710df14e21ffa1c43fe43887fa8710ff10e21bea9443ff42887fc8510fb90a21fea1443ed42887f88510ffcca21f799443fe32887fa6510ff0ca21f6194437e51887fe8310ff90621fea0c43fc41887fe6310ff8c621fe98c43fc31887fe4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fea690dfd4d21efa9a435f53487fca690df94d21fea9a437d53487f8a690df14d21ee29a435c53487fe8690ff90d21fea1a43fc43487fe8290ff90521fea0a43fc41487fe6290ff8c521fe98a43fc31487fc4290fb88521ffa82437f50487fca090ff54121fe282437c50487fea810dfd5021ff2a0437e54087faa810df55021fe2a0437c54087fea610dfd4c21ff298437e53087faa610df54c21fe298437c53087fe8610ff90c21fea1843fc43086fca210ffd0421ff20843f641087fa8210fd50421fe20843ff31087ee6210ff8c421fe98843fc31087e86210ff88421fb10843f
  | 3 => 0x400800400800000400006400800000000400000800c00400800400401400001802800c00400000800000800401000000000000400800c00400000000400000c00401400000000c00800000800800c00801001001000000000000800000000c00c00001c02401401400001801c01800c00000801400400400000002400000400000c00001000c02801803000000000806c00000001000000000001800000800400000000400403400000000400000000003001002000c03000c00c01801000c00400003800000000400000000000c00403000003800000000402800c00c00401800c00800c00400401c00003c00400000800800000003c01800c01000800000000000001400002c01802000000000000400404400404000400000801000c01800400402801004c02002c0040580100000040100040200000080000040000a800001800800800801000001000000002c00800c00400400c03003c00000000c01000400802400c00000000c000004014008010020010000004000018014004004004000004038003fea3a1ff94743bf28e87f651d0eeca3a1ff54743bea8e87f551d0eeaa3a1ff14743ffa8687fe50d0efca1a1ff54343bea8687fc50d0efaa921df94e43ffa1c87bf4390fbe8721ffd4643ff28c877e5190ffaa321df54643fe28c87ff5090ffca121df94243fea84877d5090ff8a121ffd0d43efa1a87fe4350f7c86a1ffd4543bfa8a87fe5150ffaa2a1ff14543be28a87ff5050efea0a1ff94143fea8287fc5050ef8a0a1df95043bf29887ff4310f7e8621ff90c43ef21887fd4310f7a8621f750c43ffa8887fe5110efca221ff54443bea8887fc5110ffea021ff94043bf28087fd5010efaa021ff14043ffa9e83fe53d06fca7a0f794f41af29e83fd53d06faa7a0f754f41aea9e83fc53d07fe87a0ff90f41fea1e83fc43d07fea5a0ff94b41bf29683ee52d06dca5a0ff54b41bea9683ed52d06daa5a0ff14b41ffa1683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9c83fe53906fca720ff54e41bea9c83fc53907fe8720ff90e41fea1c83fc43907fea520ff94a41bf29483fd52906faa520ff14a41ffa1483fe42906fca320ffd0641dfa0c83f741907fea120ff94241bf28483fd50906faa120ff14241ffa9a837f53507fca6a0ff54d41fe29a837c53507fe86a0ff90d41fea1a83fc43507fea4a0dfd4941ff29283fd52507f8a4a0df14941ffa1283fe42507fa84a0ffd0541fba0a83fe415077c82a0ffd4141bfa8283fe50507faa0a0ff14141be282837e54107fea620ff94c41bf29883fd53106faa620ff14c41ffa1883fe43107fa8620ff10c41ffa9083fe52106fca420ff54841bea9083fc52107fe8420ff90841fea1083fc42106fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f5411
  | 4 => 0x50cf500014400008304800016000012397302f12f00002b5e58b79a908b2230c5c001b418f13700000000000012000009a5fa1b692519bdcbc0005ec2e8c4c000000000000000491994001740001c984940000000000000009a0000000dd00017386d05f8339dba240c58000000000c640001c83584c9f2093da6c4a8cb8b5130c002110000c54000364001e386a40000000017a05e4000ebc0700015f4000000000000000000000c4848400000000112da38088000c600000000015404d0c2800000000035c001a58cc11445a8bf11c00002e00b00019e80016912a01b91c8000000000001230001f100000000004f1860d00001271eb0c500000000020d01c5289da8001128000b2000000000000000046935c4fde210c92540013518280000006916215a19800021882000000000000000000000000020d91e0d20d80000000001260145b000017a6140000000001c040010f00000007280000012c96554442a4510000c69bf53580001d44e0408eb4d1d450680001f680000009b9fc0000000000d598090ec000a61990000000000000300000000f8000005c000000000d3dcf11384386297e000000000144c0013a191400000110e064001571644694000000939345488000001a10029fb016a17800000000000000146c000000000001651e18508ac05903c1be49d0fa0ae40005c8f11678000d1a1a0000000001bc0000000000000000000000000c6c72d825fe9a480310e99580000021141196800021d00016b800000144a0fc599ce85800000008c8000000ad0001224000000000000061bb9640b480013c0000ef8000000000af00000000003f1244000c08001110000000dc80000002a80002114d17c8000000b90000588000e4176800218c7202c00000000000000000005e931402000400800001000000401000400400002001c00000400400800000402800000401400001000001800001801001001400000001000400001c00000c03000c00400000800000800800800400c00001c00000001000800000000001400800001000001400000800400001000000400000400c00401000002000003000000003400400002400000402c03801000000001000800401002000001800000400004001802000401400c00401400800000400800000800003000800401800000000800000400801c01c00400400c00000400000800001000400000000001c00400000000c00001000000000000000000400000002405c00000000002000003c01c00000800c00001000c00400000002000401000000c00401001000400c01800002000401800800000400001000400004400400000000800002801000000801000801001400000000800402000400804400400800000401000000000401801c00000802001400800400000400003
  | 5 => 0xc09180003b21912b0001f70cc82ec000000001de8001ba89b000020c001eb80004100000019f1838e8d430000001a5da28c2221c000000000000000000000000280002118001148000000000001f18000fc5082038020b40880cd0000000000000000000c44000000000001edc000000000c18001cba075cf800027a2340000011a82413d9e30001aa9390000c259384345dc380000000d60000000000001d60ffc001ff0c3c0a19185614c00000000013e8818908c14000002079ed9b985210a8000180354000000001eec000056214000000e66124000000000b1816c0000000010240005500a9891090e00000568dd9e018750c00007501d8000065c518e05b16a182096cd480019311693f0000adc0000015319a9851e4912201082990ca800000007e0001d20001845eea1385596894780018885b8b61ef80000000016a4c2c001df1309b296946e8000b300010510143c80000006545e09691d800000000000000081d9061f85046640000000000000840022280000000008c051c0000000000006600015483f5c49088000000001310898000248000000fc00006a82ae0f9b385440000000007a50780006440000018400000000005480000002c60f1060001306238000000f080012e0de00009c800000082c0002dc000259584001e1000136181c8f1b303e40021f000000133407cc040000000012f9fd8001a806ec0000d00000000000000015f80000000000012ec838000091f80e600020198a9d082606b9f90b381b179e07c001db1e602300008a40000000c0770000f2015c0000000000001a0df0001b180d9834000001300120b800009f80017f80018c099db08001be98d00009348e86314080002209e80005786c8000000001d0c0000000ca24477a120154001ff8001d18001ac9d903901f0000000000000001fbc000128f721c800000100d8c8aa1dd8001ac40001500000002d11f00000009590199080000000000000020c8000001bf94100000000000000000000004255de2240014f19204e467a029e79d1d1ec0000000005fdae0c818f8000000000000b584f40001ac950019add229fcc06c0b932180194000135495d3b00020c120c0000007d828d5e4000974fe0374000000001558008000f594d8c007c4651778bd1dfd51000000000000000094c0005017b029e15000210819101dc600000003d8000000000518000c98daa1940000000000000000000011896340000011e8010ca8540000e299111600005155516c00000018788900008d19b0641580000000000000001af1badc09c70e8a06de0d5900000020980000004500017c40000017892356d8000ef40002bd509950cb00e8d71171668d089793800012e896400152a101281c59f29b1db482c95899840016e9c00001b60001c800000015c80000000000010d8
  | 6 => 0x80004019c0000000000000000000000f1800000000000178182cd249102a1de0ce86c2249a50001248000ed84307ca070e219250700001c0000000000781035e900000000000000000010f4000001c68000000001454038e48369d1000000210cff8aacf00000c1111a020000d420e0000001164000000a01d1580ceea1982680000e1fe06707894b07ea201420eedd5a210001970c0c848aec8a9e69bf15e9099a694706d8ad88686f1aed2681d0001008d39d00aa897c0008355685a0000b10000000d457180959a0fecb05109298002220000a11fc4058d5cae087147581911e0b914c001439150001ad54696708011f8000b70000d349d813e001be113ceb800000110524ced0001340000348e39d044d927800164d48ddd0d8c710998000000fe80016b1728ee60411b06e0901fb5fb9639464c880021c00007cca49ab5031becba9022160000ec98fcee1830000174001348000e9c2848b95ec6f4bc0d6cacc00000000069800217c000000be14c8000d7de061e09898e893165c000000000000000001068d4d901040c780000001f800000102c0000006d5648709fc9125cc17cceac000e99c88000798000000001bfc92400053c0000006880000cc00147c001bd9814000554000a40714971539df495622ceb1ba0a30000a7c00159800085000000076898c0000000000008080002d5b71c90000002054399b20000f480000000000014e03e8000001658111b11dc9240000000a980016f156198c760ec004400205800220c000000d2dec0001b787b80011400009210452d0e1000000170800000125800070cfbd0fdcc523c0002f87d125de98de9ac0a9088892d759d884203f80019d145c14dca8a9c1307a8049fd0001218c3597c21c0016c9a74000002051abd928000001c34fd93a8840ab47bd8b800211d0288a16d4ca1615f40afca8c000860290000000000040001760000000001880000001d986f8b68000f2a171ad8c30000fd0208000000000e5cdf9f50000f400005240000000000000007b561ce18fdc000000000000a287f8001038000000000949f300000012900000007c1da0ff4000001d40e811d0458fcddb45cc001b9cc402cd7bc0000000000021318689440013c9e50000000000da0aa54284b00000010061e80001ccc90000000344a08e70002204001f011805300740000000000010b00006206060680017b4bb95b8000e8408d9880014980000000000004886fc000d29a9a0909f20e8000ea49e0001e289940b4e6d4183184421b90f90d1d3903c5381bcdb9b5800000037d4f8001e40fe4499cb18a07a0a1945800000119800000061991c9c20312fd9796f9c780003a215855c0008e03208f9cc9698001d8000219ca854a8bb047223d15de89a660b000132c000000b980000017e8bfc001518001b903b40012
  | 7 => 0x12200000000000000000000003e0000b002d8ece0095d8600000001ad0a59626049df8000081710d307492a91580993285d9771acd115e9cd89e71338050165810001100000001ec9f08000000000000001ea8000000a7823a24c0000000007400018d946000000000000000150162c000000001ab00000000004f800079000000133172064c001e807b1520001cd0a7417933de08f980000012b9ba4000e94001f49628000ba0724ab0078100000961364000000d68000000a94f68139d485f0fb95d03ec0000013240000005d5ef00014b892a14800000000000000139800079c4c0000738000ec4db0d64610000c7000000065c0f15c0108e91f791a19b80a5155f38bd8fb4cf834d190001898e30370ac5f88ff0329ea0a713d00014a00004ecab80000000011f4fd48647d4d100003fc0000000000000020a00000010b80f80013e1791210000668d901dce590e216815827042934d179a705d0294f39ae81703303d0d76209610000000000ea8000000000ac80000017013f8529c28d85dc1490e54148298000fb1750001d69968ae8e097f0f6000000024d1b8744ea00000000007580019ac0012080017d5a32218e74cd8000000000b89c4116d215ab9c20000a8899006960d9980000015fc000001a00001748000afa10522dd70001a89204000000000000001ca0f780000017b8ce0ef1c182282b931d9d9b940001a82880018b0000edc001960e501601e00000017d15e07f16040004b9ee4d79a421806396609817a8000198001b800000000016d1c10d54000f31d30bc97d8000a21ccc219ce1b8a1d8af4fc94e8001134000941bb07ae05c5f55b136d578e78879949f58000bf9ed48206480001e80014842b1d50449a7e12a061ee070121c0000000021a4d504a004c34036c000985000000d987199e1664000b280000000015a8001131aa0250beca385703a96e07317c2089c39608310e7dd28811bd0140a504790a0c39480e698706a0608001631011cd9859ed0c1c6597aced6080abc0015f0000a693680021b03b80000000004180021a9c30b080000000003080000000000004e9401379dbc001af9bc8704001058001a09a20000ad4001f98360cf00ac825fa84608740001891fcbe88d85340000c5b50000000f880020a8000000f90378000001319f61d7871c6b0dc03505c0000000fa8bf40019f8734001a188597980000000010498493899c80012d9a613b83889a96188161856a8000000001a7
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc31043d5430c410bd9883104376520c410dd14831043d6320c410f50c831043f2600c410bd58031043f1600c4109f59721042f565c8410dd59721042f664c8410bd193210437754c8410dd55321042f663c8410bd18f210437653c8410dd14f210437752c8410dd54b21042f560c84109fd96210427d6588410db94a210436d5288410bd98621042fa6088410be582210427f6548410b7d8d21042dc63484109fd94210427d6508410db948210436d5208410f948421042fa6008410be580210437565084109d59421042f66408410bd19021043775408410dd55021042f66308410bd18c21043765308410dd14c21042f66208410f998821043775208410f994821043755208410f954821043655208410f990821043e54208410f9cc821043e43208410fc98021042f56008410fc580210427e64940109f592500427e63940109f58e500427e62940109f58a500427d6194010ddd0650043744194010ddcc650043743194010ddc86500437421940109f597400427f65900109f596400433e5490010cf55240042f66190010bd58640043b441900109fd9540042df6350010b718d40042ef6250010bb18940042f76150010bd185400427f65100109f994400427d65100109f194400433e5410010cf55040042de6310010b758c40042ee6210010bb58840042f66110010bd58440043b441100109f597300427f658c0109f596300435e538c010d754e30042f6618c010bd58630043d4318c0109fd9530042bf644c010af19130042ef624c010bb18930042f7614c010bd185300427f650c0109f994300427d650c0109f194300435e530c010d754c30042f6610c010bd58430043d4310c0109f597200427f65880109f596200436e5288010db54a20042f66188010bd58620043e421880109fd9520042bf6448010af19120042df6348010b718d20042f76148010bd185200427e65080109f594200427c6508010bd98420042f56108010f9084200437565c4010bd99310042f464c4010ddd53100437554c4010bd98f10042f463c4010bd98b10042f462c4010bd58610043765184010be596100437965840109e59610042f96184010de94610043f25184010fcd0610043f04184010fccc610043f03184010fcc8610043f021840109fd9510042bf6444010af19110042df6344010b718d10042ef6244010bb18910042f76544010ddd9510042776544010edd9110042f66444010bd19110043b46444010ad19110043775444010dd55110043d76344010bd98d10042f46344010f518d10042d46344010f9d8910042f66244010bd18910043e46244010b918910042f76044010dd94110042fb6544010ded95100427b6544010eed9110043b86444010f6d8d10043d86344010fad8910043e86244010bed8510043f36144010de94510043f25144010
  | 1 => 0x427e64d48109f593520427e63d48109f58f520437661d4810de983520427d6594810dbd4a520427e64948109f592520427e63948109f58e52042df6354810b718d520427f64548109f191520427f6354810d7d8d520425f63548109f18d520435c63548109718d520436f62548109fd85520427d6154810dd18552042be6414810af59052042de6314810b758c520436d52148109f990520433e64148108f990520427d6414810cf590520423d64148109f98c520435e63148109798c520427d6314810d758c520425d63148109f984520437661148109f980520437a60148109fd97420427e65d08109f597420427c65d0810cf953420433d54d0810b798f42042dd63d0810bd98742042f561d08109fd96420427e65908109f596420427c6590810db94a420436d5290810bd98642042f561908109fd95420427e65508109f595420427c6550810cf951420433d5450810db949420436d5250810bdd8542042f46150810bed8142042f860508109fd94420427e65108109f594420427c65108109fd97320427e65cc8109f597320427c65cc810d794f320435d53cc810dbd4b32042f661cc810bd587320427f658c8109f996320427d658c8109f196320435f538c810d714e320436e528c810db54a32042f6618c810bd586320427f654c8109f995320427d654c8109f195320435e534c810d754d320436e524c810db54932042f7614c810bd185320427f650c8109f994320427d650c8109f194320435f530c810d714c320436f520c810f34c8320427e64944109f592510427e63944109f58e510427d62944109f59741042de63d0410b758f41042ee62d0410bb58b41042f565d0410dd597410427565d0410ddd53410437554d0410bd98f41043d663d0410b598f41043d563d0410bd98b41043e662d0410b998b41043e562d0410bd583410427f65904109f596410433e5490410cf55241042f66190410dd94641042fa6090410be582410427f6550410dd945410427f65104109f594410433e5410410cf55041043b54110410be98041042f96010410dd59441042756510410bd99041043b66410410ddd5041043b65410410dd55041043b55410410bd98c41042f66210410fc98041042f56010410fc580410427d65cc410bd597310437565cc410bd99331042f464cc410ddd53310437554cc410ddd4f310437553cc410bd98b310437652cc410dd14b31042f560cc4109fd96310427d658c410d794e310435d538c410bd98631042fa608c410be582310427f654c410bbd8931042ec624c4109fd94310427d650c410d794c310435d530c410f54c431042fa600c410be5803104375650c4109d59431042f6640c410bd1903104377540c410dd55031042f6630c410f598c3104377530c410f594c3104375530c410f554c3104355530c410f590
  | 2 => 0x654c110afd9130442bc644c110cfd51304433c544c110d7d4d304435c534c110bbd8930442ec624c110dbd49304436c524c110bdd8530442f4614c1109f994304433f540c110cf150304435f530c110d714c304436f520c110db148304427e65c8110cfd53204433c54c8110d7d4f204435c53c8110dbd4b204436c52c8110bd98720442f561c8110cfd52204433c5488110d7d4e204435c5388110dbd4a204436c52881109f595204427c6548110cfd51204433c5448110d7d4d204435c5348110bdd8520442f46148110cfd53104433c54c4110d7d4f104435c53c4110dbd4b104436c52c4110eed5310443b854c4110f6d4f10443d853c4110fad4b10443e852c4110fc90710443f141c4110cfd52104433c5484110d7d4e104435c5384110dbd4a104436c5284110bdd9210442f56484110edd5210443765484110dd15210443b45484110cd15210443d75384110dd94e10443745384110f514e10443545384110f9d4a10443765284110dd14a10443e45284110d914a10443f350841109f98f540427d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d6295010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540437461550109fd81540427d6055010cf55054042de6315010b758c54042ee6215010bb588540427e6415010cf990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427661150109f980540437a60150109f993530427d64d4c109f98b530427d62d4c109f987530437661d4c109f983530437a60d4c109f596530435f5394c109f992530427d6494c109f98a530427d6294c10bbd8953042ec6254c109fd91530427c6454c10d7d8d530427f6254c10dbd89530426f6254c109f189530436c6254c109b189530427f6154c109f58553043746154c109fd81530427d6054c10af99053042bd6414c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530427e6214c10db988530426e6214c109f588530436d6214c109b588530427e6114c10dd984530427e6014c10de980530427f65d0c109f997430427d65d0c109f197430433e54d0c10cf55343042ee62d0c10bb58b43042f661d0c10bd587430427f6590c109f996430427d6590c109f196430435e5390c10d754e43042f66190c10bd586430427f6550c109f995430427d6550c109f195430433e5450c10cf551430435e5350c10d754d43042f76150c10bd18543042fb6050c10be181430427f6510c109f994430427d6510c109f194430
  | 3 => 0x910d714c324436f520c910db14832443cd320c910bd98432442f5610c9109f997414433f54d0510cf15341442de63d0510b758f414435f53d0510d714f41442ee62d0510bb58b414436f52d0510db14b41442fa60d0510be583414427e6590510cfd52414433c5490510d7d4e414435c5390510dbd4a414436c5290510bd996414437665905109d99641442f56490510edd5241443765490510dd15241443b45490510cd15241443d75390510dd94e41443745390510f514e41443545390510f9d4a41443765290510dd14a41443e45290510d914a41442f660905109f195414433f5450510cf151414435f5350510d714d414436f5250510db14941442fb6050510be181414437465505109d19541443b76450510edd5141443765450510dd15141443b45450510cd15141443d75350510dd94d41443745350510f514d41443545350510f9d4941443765250510dd14941443e45250510d914941443f36050510bd18141443f060505109f994414433f5410510cf150414435f5310510d714c414436f5210510db14841442f661105109f997314433f54cc510cf153314435f53cc510d714f314436f52cc510db14b31442fa60cc510be583314427e658c510cfd52314433c548c510d7d4e314435c538c510dbd4a314436c528c5109f195314433f544c510cf151314435f534c510d714d31442ef624c510bb189314436f524c510db14931442fb604c510be181314427e650c510cfd50314433c540c510d7d4c314435c530c510dbd48314436c520c510f54c4314433f54c8510cf153214435f53c8510d714f214436f52c8510db14b21442fa60c8510be583214427e6588510cfd52214433c5488510d7d4e214435c5388510dbd4a214436c5288510cfd51214433c5448510b7d8d21442dc6348510d7d4d214435c5348510dbd49214436c5248510bed8121442f860485109f994214433f5408510cf150214435f5308510d714c214436f5208510f9484214427e65d0110cfd53404433c54d0110d7d4f404435c53d0110dbd4b404436c52d0110bd98740442f561d01109f996404433f5490110cf152404435f5390110d714e404436f5290110db14a40443b641901109fd95404427d65501109f195404433f5450110cf15140442df6350110b718d404435f5350110d714d40442ef6250110bb189404436f5250110db14940442f76150110bd185404427e6510110cfd50404433c5410110b798c40442dd6310110d7d4c404435c5310110bb98840442ed6210110dbd48404436c5210110bd98440442f56110110ed904404427e65cc110cfd53304433c54cc110d7d4f304435c53cc110dbd4b304436c52cc110bd98730442f561cc1109f996304433f548c110cf152304435f538c110d714e304436f528c110db14a304427f654c1109f595304427c
  | 4 => 0x7d4f524435c53d49109f993524427d64d49109f98f524427d63d4910dbd5352443af54d4910cbd53524436e54d4910db553524436c54d4910eb153524432c54d4910dbd4f52443cf53d4910d3d4f524436e53d4910db54f524436c53d4910f314f524434c53d4910dbd93524436e64d4910db593524436c64d4910dbd8f524436e63d4910db58f524436c63d4910dbd0f524436e43d4910db50f524436c43d4910dbd87524436d61d4910dbd83524436d60d4910af99252442bd6494910cfd52524433c5494910b798e52442dd6394910d7d4e524435c5394910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e6394910d798e524425e63949109f58e524435d63949109758e52443756194910de58252442bf6454910af191524433f5454910cf15152442df6354910b718d524435f5354910d714d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524437761549109fd81524437b60549109f994524433f5414910cf150524435f5314910d714c524436d52149109f990524427d64149109f98c524427d6314910db988524427c6114910bb994524436e65149109b994524436f5414910ebd50524432f5414910db950524436d5414910db15052443ac5414910cb150524436f5314910f3d4c524434f5314910db94c524436d5314910db14c52443cc5314910d314c524436f6414910db990524436d6414910db190524436f6314910db98c524436d6314910db18c524436f4314910db90c524436d4314910db10c524436f6114910dbd80524436d6014910db440524427f65d09109f997424427d65d09109f197424433f54d0910cf15342442de63d0910b758f424435f53d0910d714f424436f52d0910db14b42442f661d0910bd587424427f65909109f996424427d65909109f196424433f5490910cf152424435f5390910d714e424436f5290910db14a424427f65509109f995424427d65509109f195424433f5450910cf151424435f5350910d714d424436f5250910db149424427f65109109f994424427d65109109f194424433f5410910cf150424435f5310910d714c424436f5210910db14842442f66110910bd584424427f65cc9109f997324427d65cc9109f197324433f54cc910cf153324435f53cc910d714f324436f52cc910db14b324427f658c9109f996324427d658c9109f196324433f548c910cf152324435f538c910d714e324436f528c910db14a324427f654c9109f995324427d654c9109f195324433f544c910cf151324435f534c910d714d324436f524c910db14932442f7614c910bd185324427f650c9109f994324427d650c9109f194324433f540c910cf150324435f530c
  | 5 => 0x544425d63951109f98a544436e62951109b98a544427d6295110db58a544426d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f63551109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427761551109fd81544437b60551109f994544433d5415110cf990544427e63151109f58c544427e62151109f588544427e6115110dd584544427c61151109f980544427c6015110af994544433e65151108f99454443b56115110cfd8c544433e6315110cf58c544433c6315110cfd88544433e6215110cf588544433c6215110cfd84544433d6115110cd584544433f6015110cf580544433d1015110cfd53534433c54d4d109f993534427d64d4d109f98b534427d62d4d10d7d53534439f54d4d10c7d53534435e54d4d10d7553534435c54d4d10e7153534431c54d4d10d7d93534435e64d4d10d7593534435c64d4d10d7d8b534435e62d4d10d758b534435c62d4d10d7d87534435d61d4d10d7d83534435d60d4d10af99253442bd6494d10cfd52534433c5494d10d7d4e53442ee6294d10bb58a534427e6494d10cf992534423e6494d109f592534433d6494d108f592534427e6394d109798e534427e6294d10db98a534426e6294d109f58a534436d6294d109b58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af191534433f5454d10cf15153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109dd85534427f6054d10ded81534427e6514d10cfd50534433c5414d10d754c534427e6414d109f590534435e6314d109f988534427d6214d109f984534427c6114d109f980534427c6014d10b7994534435e6514d1097994534435f5414d10e7d50534431f5414d10d7950534435d5414d10d7150534439c5414d10c7150534435f6414d10d7990534435d6414d10d7190534435f6214d10d7988534435d6214d10d7188534435f6114d10d7584534435f6014d10d7580534435d1014d109fd97434427e65d0d109f597434427c65d0d10cfd53434433c54d0d10d7d4f434435c53d0d10bb98b43442ed62d0d10bd98743442f561d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d10d7d4e434435c5390d109fd95434427e6550d109f595434427c6550d10cfd51434433c5450d10d7d4d434435c5350d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10d7d4c434435c5310d10bd98443442f56110d10cfd53524433c54d4910d
  | 6 => 0x2de63d0610b758f41842ee62d0610bb58b41842fa60d0610be583418437565d0610ddd5341843b654d0610dd55341843b554d0610bd98f41843d663d0610b598f41843d563d0610bd98b41843e662d0610b998b41843e562d0610fc98341842f560d0610fc583418433f5490610cf152418433e5450610cf55141842fb6050610be181418433f5410610cf15041843b54110610bd59441843756510610ed99041843775410610edd5041843755410610ed15041842f66310610bd98841842f56010610d794f318435d53cc610be98331842f960cc610dd59731842f664cc610bd193318437754cc610dd553318437753cc610f594f318437553cc610f554f31842f662cc610dd94b31843f260cc610bd58331843f160cc610d7d4e318435c538c610d794d318435d534c610bbd8931842ec624c610bed8131842f8604c610d7d4c318435c530c610f54c431842f5650c610dd59431842f6640c610bd1903184377540c610dd55031843d6630c610ddd4c31843d7530c610d5d4c3184375530c610f514c31843d6430c610f550c31842f6620c610dd94831843d6320c610f50c831842f5600c610db94b218436d52c8610be98321842f960c8610bd99321842f464c8610ddd53218437554c8610bd98f21842f463c8610dd94f218437453c8610f994b218437552c8610f954b21843f260c8610bd58321843f160c8610dbd4a21842df6348610b718d218436e5248610db54921842fb6048610be18121843e52108610bd59421843756508610bd99021842f46408610ddd5021843755408610bd98c21842f46308610dd94c21843745308610f998821843775208610f9d4821843675208610dd54821843e45208610f990821843e54208610f9cc821843e43208610bd580218433e5490210cf55240842f66190210bd58640843b44190210b7d8d40842dc6350210bbd8940842ec6250210bdd8540842f46150210cf950408433d5410210b798c40842dd6310210bb98840842ed6210210bd98440842f56110210ed104408435e538c210d754e30842f6618c210bd58630843d4318c210afd9130842bc644c210bbd8930842ec624c210bdd8530842f4614c210d794c308435d530c210bd98430842f5610c210f50c430842f66188210bd58620843e42188210bd597108437565c4210bd99310842f464c4210ddd53108437554c4210bd98f10842f463c4210bd98b10842f462c4210be597108437965c42109f98f544427d63d51109f98b544427d62d5110edd87544433f63d5110cf98f544433d63d5110cf18f544433f62d5110cf98b544433d62d5110cf18b544433f61d5110cf587544433f60d5110cf583544433f5495110b798e54442dd6395110bb98a54442ed62951109f992544423e64951109f98e544435e63951109798e544427d6395110d758e
  | 7 => 0x4d0310bd98740c42f561d0310cfd5240c433c5490310ed90640c433e5450310cf55140c42df6350310b718d40c42ef6250310bb18940c42f76150310bd18540c433f5410310cf15040c42de6310310b758c40c42ee6210310bb58840c42f66110310bd58440c43b64110310d794f30c435d53cc310bd98730c42f561cc310d7d4e30c435c538c310afd9130c42bc644c310d794d30c435d534c310bbd8930c42ec624c310bdd8530c42f4614c310d7d4c30c435c530c310bd98720c42f561c83109f98f548427d63d52109f98b548427d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a548433f64552109fd8d548427c63552109fd89548427c6255210ddd85548433d5415210b798c54842dd6315210bb98854842ed6215210cf990548427e6315210d798c548425e63152109f58c548435d63152109758c548427e6215210db988548426e62152109f588548436d62152109b58854843756115210de98054842ee62d4e10bb58b538427e64d4e109f593538427e62d4e10db98b538426e62d4e109f58b538436d62d4e109b58b538437561d4e10de983538435f5394e109f992538427d6494e109f98a538427d6294e109fd91538427c6454e10d7d8d538427f6254e109f18953843776154e10d754c538427e6414e109f590538435e6314e109f988538427d6214e10dd584538437a6014e109fd97438427e65d0e109f597438427c65d0e10bb98b43842ed62d0e10bd98743842f561d0e109fd96438427e6590e109f596438427c6590e10d794e438435d5390e10bd98643842f56190e109fd95438427e6550e109f595438427c6550e10d794d438435d5350e10bdd8543842f46150e109fd94438427e6510e109f594438427c6510e10b798f52842dd63d4a109f993528427d64d4a109f98f528435e63d4a109798f528427d63d4a10d758f528425d63d4a10de983528436f5294a109f992528427d6494a109f98e528427d6394a109fd91528427c6454a109fd8d528427c6354a10dbd89528436d5214a109fd97428427e65d0a109f597428427c65d0a10b798f42842dd63d0a10bd98742842f561d0a109fd96428427e6590a109f596428436e5290a10db54a42842f66190a10bd586428427f6550a109f995428427d6550a109f195428436e5250a10db54942842f76150a10bd185428427f6510a109f994428427d6510a109fd97328427e65cca109f597328427c65cca10db94b328436d52cca10bd98732842f561cca109fd96328427e658ca109f596328435e538ca10d754e32842f6618ca10bd586328427f654ca109f995328427d654ca109f19532842f7614ca10bd185328427f650ca109f994328427d650ca10d794c328435d530ca10db948328436d520ca10f34c8328433e54d0610cf5534184
  | 8 => 0x109f18954c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c42be64d4f10af59353c42ee62d4f10bb58b53c427e64d4f10cf99353c423e64d4f109f59353c433d64d4f108f59353c427e62d4f10db98b53c426e62d4f109f58b53c436d62d4f109b58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f109fd9153c427c6454f10d7d8d53c427f6254f109f18953c435d5314f109f99053c427d6414f10d798c53c427e6214f109f58853c43766114f10de58053c427f65d0f109f99743c427d65d0f109f19743c435e53d0f10d754f43c42ee62d0f10bb58b43c42f661d0f10bd58743c427f6590f109f99643c427d6590f109f19643c433e5490f10cf55243c435f5390f10d714e43c427f6550f109f99543c427d6550f109f19543c435f5350f10d714d43c42fb6050f10be18143c427f6510f109f99443c427d6510f109f19443c433e5410f10cf55043c435e5310f10d754c43c42f66110f10bd58443c42be64d4b10af59352c42de63d4b10b758f52c436f5294b109f99252c427d6494b109f98e52c427d6394b109fd9152c427c6454b109fd8d52c427c6354b10db54852c427e6414b109f59052c427e6314b109f58c52c43766114b10de58052c427f65d0b109f99742c427d65d0b10b798f42c42dd63d0b10db94b42c436d52d0b10bd98742c42f561d0b109fd9642c427e6590b109f59642c427c6590b10cf95242c433d5490b109fd9542c427d6550b109f19542c42fb6050b10be18142c427f6510b109f99442c427d6510b109f19442c433e5410b10cf55042c436e5210b10db54842c42f66110b10bd58442c427f65ccb109f99732c427d65ccb10db94b32c436d52ccb109fd9632c427e658cb109f59632c427c658cb10d794e32c435d538cb109fd9532c427d654cb109f19532c42f7614cb10bd18532c427f650cb109f99432c427d650cb109f19432c435e530cb10d754c32c436e520cb10db54832c43cd320cb10bd98432c42f5610cb10b798f41c42dd63d0710bb98b41c42ed62d0710cf95241c433d5490710be98241c42f96090710dd59641c43765490710ed95241c43b55490710dd15241c43765390710dd14e41c43765290710dd14a41c42f66090710fc98241c43f16090710bdd9541c43776550710edd9141c43765450710dd15141c43765350710dd14d41c43765250710dd14941c42f46050710cf95041c433d5410710be98041c42f96010710d794e31c435d538c710be98231c42f9608c710bbd8931c42ec624c710d794c31c435d530c710f54c431c42fa600c710be58031c436e5288710db54a21c42fa6088710be58221c42df6348710b718d21c436e5208710db54821c43e52108710be98021c42f96008710cf95340c433d5
  | 9 => 0x189510c26c6254430af990510c2bd6414430bb988510c2ed6214430dd544510c27f65d04309f997410c27d65d0430cf953410c33d54d0430b798f410c2dd63d0430bb98b410c2ed62d04309fd96410c27e65904309f596410c2de6390430b758e410c3765190430dd546410c27f65504309f595410c27c6550430cf951410c33d5450430b7d8d410c2dc6350430dd945410c3755150430bed81410c2f860504309fd94410c27e65104309f594410c37651cc430dd547310c2fa60cc430be583310c27d658c430b7596310c35d658c430b7992310c2dc648c430d7d52310c35d548c430b798a310c35e528c430b7986310c35d518c430b7582310c27f654c430bbd89310c2ec624c430dd944310c375510c430f54c4310c2fa600c430be580310c2de640c430b7190310c35f540c430d7550310c2de620c430d7948310c2de610c430f5984310c3d6510c430d7544310c3d5510c430d5544310c3d6410c430f5504310c3da600c430b7580310c3d9600c4309fd96210c27e65884309f596210c2de6388430b758e210c3cc3288430dd946210c37551884309fd95210c27d65484309f195210c2df6348430b718d210c3765148430dd545210c27f65084309f994210c27d6508430b7d8c210c2dc6308430f50c4210c3e521084309f992500c27d6494030d7d0e500c35c4394030d78c6500c35c31940309f597400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c39c43900309fd95400c2df6350030b718d400c2f76150030bd185400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c39c4310030bd984400c2f56110030b7993300c2dc64cc030d7d53300c35d54cc030b7987300c2dd638c030d794e300c2f9638c030de94e300c3da538c030f6d0e300c3d8438c030f68c6300c3d8318c0309fd95300c2bf644c030af191300c2f7614c030bd185300c2df654c030d7d95300c25f654c030e7d91300c2de644c030b7191300c39c644c030a7191300c35f544c030d7551300c3d7614c030b7185300c3d4614c030b5185300c2df604c030d7941300c2fb654c030ded95300c27b654c030eed91300c3b8644c030bed8d300c3db634c030de94d300c3da534c030fcd85300c3f0614c030b798f54c42dd63d5310bb98b54c42ed62d53109f98f54c435e63d53109798f54c427d63d5310d758f54c425d63d53109f98b54c436e62d53109b98b54c427d62d5310db58b54c426d62d5310dd98754c437960d5310cfd5254c42de6395310b758e54c42ee6295310bb58a54c427e6395310d798e54c425e63953109f58e54c435d63953109758e54c427e6295310db98a54c426e62953109f58a54c436d62953109b58a54c43766195310cfd9154c427f63553109f18d54c427f62553
  | 10 => 0x14c33c5410530b798c414c2dd6310530dbd48414c36c5210530ddd44414c37451105309f997314c33f54cc530cf153314c36f52cc530db14b314c37451cc530cfd52314c33c548c530dbd4a314c36c528c530ddd46314c374518c530be982314c2f9608c530cfd51314c33c544c530bbd89314c2ec624c530dbd49314c36c524c530ddd45314c374514c530bed81314c2f8604c5309f994314c33f540c530cf150314c36f520c530db148314c377510c530f54c4314c27e65885309f596214c27c6588530cfd52214c33c5488530dbd4a214c36c5288530ddd46214c37451885309fd95214c27e65485309f195214c33f5448530cf151214c2df6348530b718d214c3775148530dd145214c27e65085309f594214c27c6508530cfd50214c33c5408530b798c214c2dd6308530ddd44214c3745108530f9484214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d0130ddd47404c37451d01309f996404c33f5490130cf152404c39e4390130ddd46404c37451901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c2f76150130bd185404c3775150130dd145404c27e6510130cfd50404c33c5410130b798c404c2dd6310130e790c404c2f66110130bd584404c3775110130dd144404c33f54cc130cf153304c37751cc130dd147304c3bb54cc130ee153304c3da43cc130f650f304c3f351cc130fc147304c33f548c130cf152304c377518c130dd146304c2df648c130b7592304c39f548c130d7952304c35c548c130e7152304c31c548c130f5d46304c35c518c130f5146304c354518c130f6d42304c27e63d5030d798f540c27e61d50309f587540c27e60d5030de983540c27d6595030cfd52540c27e61950309f586540c33f64550309fd8d540c27d6355030d718d540c27f61550309f185540c33d5415030bd984540c2f561150309f990540c33e64150309f98c540c35e63150309798c540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c309f592530c27d65d0c30bd987430c2f561d0c30b7597430c35d65d0c3097597430c35f54d0c30d7553430c2de61d0c30f5987430c2d661d0c30f5587430c2dd60d0c309fd96430c27d6590c30cf952430c33d5490c30b798e430c35e5390c30be982430c2f96090c309fd95430c35e5350c309fd94430c27d6510c30cf950430c33d5410c30e750c430c2fa6010c30be580430c35d6510c3097594430c2de6410c30e7990430c35f5410c30e7950430c35d5410c30e7550430c2de6110c30f6980430c2dd6010c30f6580430c37751944309f992510c27d64944309f98a510c27d6294430bbd89510c2ec62544309fd91510c27c64544309fd89510c36f62544309bd89510c27c6254430db
  | 11 => 0x7e6195130dd986544c27661951309f586544c37561951309d586544c27d6095130de582544c2f76155130bd185544c33f64551309fd8d544c35f635513097d8d544c27f6155130ddd85544c27761551309f185544c37461551309d185544c27f6055130ded81544c27e6515130cf550544c33e64151309f98c544c35d63151309f18c544c27e61151309f584544c2be6515130cf994544c23e6515130e758c544c33f6315130cf58c544c31d6315130cfd84544c33e6115130cf584544c33c6115130cfd80544c33d6015130cf4c0544c27e65d0d30cfd53434c33c54d0d30bd987434c2f561d0d30be983434c2f960d0d309f996434c33f5490d30cf152434c2de6590d30d7996434c25e6590d30b7592434c39f5490d30d7952434c35c5490d30e7152434c31c5490d30b7982434c27c6550d30cfd51434c33c5450d30bed81434c2f86050d30d7195434c25c6550d30e7d91434c39f5450d30d7951434c35c5450d30e7151434c31c5450d30f6d81434c2dc6050d30f6181434c27e6510d30cfd50434c33c5410d30b798c434c33f54d4530cf153514c27e64d45309f593514c27e62d45309f58b514c37754d4530edd53514c33754d4530dd953514c37554d4530dd153514c3b454d4530cd153514c3d643d4530f550f514c37752d4530f9d4b514c36752d4530ddd93514c37664d4530dd593514c37464d4530ddd8f514c37743d4530dd90f514c37543d4530dd10f514c37762d4530dd98b514c37562d4530dd18b514c37760d4530dd583514c2be6494530af592514c33f5494530cf152514c2ee6294530bb58a514c36f5294530ddd46514c2bf6454530af191514c33f5454530cf151514c2ef6254530bb189514c36f5254530cfd50514c33c5414530dbd48514c37551145309f990514c27d6414530d790c514c35d43145309f988514c27d6214530bd994514c3766514530ddd50514c3b75414530cdd50514c3765414530dd550514c3745414530ed150514c3345414530f590c514c3d54314530ddd48514c3e75214530d9d48514c3765214530dd548514c3745214530f9148514c3645214530ddd90514c3766414530dd590514c3746414530ddd8c514c3774314530dd90c514c3564314530dd50c514c3554314530dd10c514c3776214530dd988514c3756214530dd188514c3776014530dd580514c37530145309f997414c27d65d05309f197414c33f54d0530cf153414c2de63d0530b758f414c2ee62d0530bb58b414c36f52d0530db14b414c37751d0530dd147414c27e65905309f596414c27c6590530cfd52414c33c5490530dbd4a414c36c5290530ddd46414c37451905309fd95414c27e65505309f195414c33f5450530cf151414c36f5250530db149414c3775150530dd145414c27e65105309f594414c27c6510530cfd504
  | 12 => 0xd0330b758f40cc33f5490330cf15240cc39e4390330cf95140cc33d5450330b7d8d40cc2dc6350330bdd8540cc2f46150330cfd5040cc33c5410330b798c40cc2dd6310330e790c40cc2f66110330bd58440cc35d63d52309f987548c27d61d5230de983548c33f54952309f986548c27d6195230cfd91548c35f63552309fd85548c27c6155230cf550548c2f66115230bd584548c33e6415230d758c548c27e6115230dd984548c27661152309f584548c37561152309d584548c37a6015230cf953438c33d54d0e30bd987438c2f561d0e30be983438c2f960d0e30d7597438c35f54d0e30e7953438c35d54d0e30e7553438c2de61d0e30f5987438c2d661d0e30f5587438c3da60d0e30b7583438c3d960d0e30cfd52438c33c5490e30cf951438c33d5450e30bed81438c2f86050e30cfd50438c33c5410e30e750c438c2dd6510e30d7594438c39e6410e30d7d50438c39f5410e30d7550438c39c5410e30b7984438c2dd6010e30bb98b518c2ed62d4630ddd46518c27e64946309f592518c27e62946309f58a518c27f64546309f191518c27f62546309f189518c37551146309fd97418c27e65d06309f597418c2de63d0630b758f418c2ee62d0630bb58b418c27f65906309f996418c27d6590630b798e418c2dd6390630dd946418c37551906309fd95418c27d65506309f195418c2df6350630b718d418c3765150630dd545418c27f65106309f994418c27d6510630dd946318c375518c630be982318c2f9608c630b7992318c2dc648c630d7d52318c35d548c630b798a318c35e528c630f5946318c35d518c630f5546318c3da608c630b7582318c3d9608c630bbd89318c2ec624c630dd945318c375514c630bed81318c2f8604c630f54c4318c2dd650c630d7594318c2de640c630b7190318c35f540c630d7550318c2de620c630d7948318c3d6610c630f5d44318c35d510c630f5144318c3d6410c630f5504318c2dd600c6309fd96218c27e65886309f596218c2de6388630b758e218c36e5288630db54a218c3cc32886309fd95218c27d65486309f195218c2df6348630b718d218c27f65086309f994218c27d6508630b7d8c218c2dc6308630dd944218c3755108630f50c4218c3e52108630cf952408c33d5490230b798e408c2dd6390230e710e408c2df6350230b718d408c2f76150230bd185408c33e5410230cf550408c2de6310230b758c408c39c4310230bd984408c2f56110230b7597308c35d65cc230b7993308c2dc64cc230d7d53308c35d54cc230b7987308c2f965cc230de597308c27e61d51309f587544c39f63d5130cfd8f544c33d63d5130cfd87544c33e61d5130cf587544c33c61d5130cfd83544c33d60d5130cfd52544c2f66195130bd586544c27e64951308f992544c27d6395130d758e544c2
  | 13 => 0xdd94521103755148440bed8121102f860484409fd94211027e65084409f59421102bf6408440af190211035e5308440d754c21103765108440dd54421103b64108440f9484211033e4394040cf10e501033e4194040cf106501035e53d0040d754f401037651d0040dd54740102be63d0040e794f401039d53d0040af98740103b651d0040ed54740102bd6490040cf952401035e5390040d754e40103765190040dd54640102f96490040de95240103ba5490040f694e40103d95390040ee90e40103b84390040fc94640103f15190040ee90640103b841900409fd9540102df6350040b718d401035e5350040d754d40102f76150040bd18540103765150040dd54540102bf6550040cfd95401023f6550040e7d8d40102bc6350040e718d401029c6350040e794d401039d5350040edd8540102bc6150040ed18540102b46150040ed94540103b55150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103db6350040f618d40103da5350040f654d40103f36150040fc18540103f25150040fc54540102f661d5330bd58754cc35e63d53309f98754cc37661d53309d98754cc27d61d5330dd58754cc27561d5330de58354cc33f5495330bd98654cc2f56195330d798e54cc27e6195330dd98654cc27661953309f58654cc37561953309d58654cc33f64553309fd8554cc27c6155330cf55054cc33e6415330d798c54cc27e61153309f58454cc3796015330bd98743cc2f561d0f30cf95243cc33d5490f30be98243cc2f96090f30d759643cc35e5490f30e795243cc39d5490f30d715243cc2de6090f30f698243cc3d96090f30b7d9543cc35f6550f30e7d9143cc35e5450f30d715143cc2dc6050f30cf95043cc33d5410f30be98043cc2f96010f30af99351cc2bd64d4730bb98b51cc2ed62d4730ddd4651cc27e64947309f59251cc35e4394730d750e51cc27e62947309f58a51cc27f64547309f19151cc27f62547309f18951cc37551147309fd9741cc27e65d07309f59741cc2de63d0730b758f41cc2ee62d0730bb58b41cc37651d0730dd54741cc27f65907309f99641cc27d6590730cf95241cc33d54907309fd9541cc27d65507309f19541cc2fb6050730be18141cc27f65107309f99441cc27d6510730cf95041cc33d5410730b798c41cc2dd6310730dd94441cc3755110730dd94731cc37551cc730be98331cc2f960cc730bbd8931cc2ec624c730dd94431cc375510c730f54c431cc2fa600c730be58031cc27f65887309f99621cc27d6588730db94a21cc36d52887309fd9521cc27d65487309f19521cc2df6348730b718d21cc27f65087309f99421cc27d6508730b798c21cc2dd6308730dd94421cc3755108730f948421cc33e54d0330cf55340cc2de63
  | 14 => 0x4e51103765394440f594e51103565394440dd54e51103d55394440d554e51103745394440ed90e51103b44394440ddd4a51103765294440f994a51103665294440dd19251103776394440dd98e51103756394440dd18e51103774394440dd90e51103754394440dd10e51103776294440dd98a51103756294440dd18a51103766094440dd182511035e5354440d754d511036e52544409fd8d511027c63544409fd89511027c6254440ddd9551103b46454440ddd4d51103765354440f594d51103565354440dd54d51103d55354440d554d51103745354440ed90d51103b44354440ddd4951103765254440f994951103665254440dd54951103e55254440d954951103766454440ddd8d51103766354440dd58d51103746354440ddd0d51103764354440dd50d51103744354440ddd8951103766254440dd58951103746254440dd98151103746054440dd10151102de6314440b758c511035e5314440d754c51102ee6214440bb588511036e5214440db54851102f66114440dd54451102de63d0440b758f411035e53d0440d754f41102ee62d0440bb58b411036e52d0440db54b411037651d0440dd54741102fa60d0440be583411027d6590440d794e411035d5390440db94a411036d5290440dd54641102bd6590440cf59641102be6390440e794e411039d5390440af98a41103ae5290440eb54a41102be6190440ed946411033d5190440ed54641103355190440af582411027f6550440d794d411035d5350440db949411036d5250440dd945411035e5310440d754c411036e5210440db54841103765110440dd54441103b54110440be98041102f96010440af98c411039e5310440e754c41102be6210440eb94841103ad5210440af98441103b66110440ed944411033d5110440ed54441103ba6010440af58041103b960104409fd97311027e65cc4409f59731102be64cc440af593311035e53cc440d754f311036e52cc440db54b311037651cc440dd54731103b641cc4409fd96311027e658c4409f59631102be648c440af592311035e538c440d754e311039e438c440db94a311036d528c440dd9463110375518c4409fd95311027d654c4409f19531102bf644c440af191311035e534c440d754d31102ef624c440bb189311036e524c440db5493110376514c440dd54531102fb604c440be181311027f650c4409f994311027d650c440afd9031102bc640c440d794c311035d530c440e790c311036e520c440db5483110376510c440dd54431103b6410c440f54c4311027f65884409f996211027d6588440af99221102bd6488440d794e211035d5388440db94a211036d5288440eb90a21103765188440dd546211027f65484409f595211027c6548440afd9121102bc6448440b7d8d21102dc6348440d794d211035d534844
  | 15 => 0x503645214540ddd9051503776314540dd98c51503756314540dd18c51503774314540dd90c51503754314540dd10c51503776214540dd98851503756214540dd18851503776014540dd580515037540145409f99741502de63d0540b758f415035f53d0540d714f41502ee62d0540bb58b415036f52d0540db14b415037451d0540d7d4e415035c5390540dbd4a415036c5290540ddd4641503745190540be98241502f96090540d7d4d415035c5350540dbd49415036c5250540ddd4541503745150540bed8141502f860505409f994415035f5310540d714c415036f5210540db148415037751105409f997315027d65cc5409f197315035f53cc540d714f315036f52cc540db14b315037751cc540dd147315027e658c5409f596315027c658c540d7d4e315035c538c540dbd4a315036c528c540ddd463150374518c5409fd95315027e654c5409f195315035f534c540d714d31502ef624c540bb189315036f524c540db1493150377514c540dd145315027e650c5409f594315027c650c540af99031502bd640c540d7d4c315035c530c540dbd48315036c520c540ddd443150374510c540f54c4315027e65885409f596215027c6588540d7d4e215035c5388540dbd4a215036c5288540ddd46215037451885409fd95215027e65485409f19521502df6348540b718d215035f5348540d714d21503775148540dd145215027e65085409f594215027c6508540af99021502bd6408540d7d4c215035c5308540ddd4421503745108540f9484215035f53d0140d714f405037751d0140dd14740503db53d0140f614f40503f351d0140fc147405035f5390140d714e40503775190140dd146405039f5390140cf14e405039c5390140c714e40503b75190140cf14640503b45190140cd14640503bb5090140bd98753102f561d4c40d7d4e531027e6194c409f586531039c6494c40d7192531035f6194c40d7986531035d6194c40d7186531035e6094c40d7182531027f6154c409f185531035f6554c40e7191531035e6454c40d7d85531035e6154c40d7585531035c6154c40d7981531035c6054c40d710153102de6314c40d754c53102f66114c40bd584531035e53d0c40d754f43102f661d0c40bd58743102fa60d0c40be583431027d6590c40d754e43102bd6590c40cf59643102be6390c40e794e431033d5390c40e754e431031d5390c40af98643102bd6090c409fd95431035e5350c40d794c431035d5310c40e750c43102fa6010c40be58043102be6310c40e798c431039e5310c40cf54c431039d5310c40af98443103ba6010c40af58043103b96010c40b798f51102dd63d4440d794f511035d53d4440bb98b51102ed62d4440d794e511035d5394440ddd46511027e63944409f58e511027e62944409f58a51103b46494440ddd
  | 16 => 0xd63946409f98a519027d6294640b7d8d51902dc6354640bbd8951902ec62546409fd8d519035f635464097d8d519027c6354640d718d519025c63546409fd89519036f62546409bd89519027c6254640db189519026c6254640dd54451902de63d0640b758f41902ee62d0640bb58b41903765190640dd54641902fa6090640be58241902be6390640af98a41903b65190640cf54641903b55190640ee98241902bd6090640ee58241903765150640dd54541902fb6050640be18141903b54110640af594419033d6510640af98c41902be6210640ed98441903b75110640cf54441903b45110640af580419027f65cc6409f997319027d65cc640af99331902bd64cc640ed907319027f658c6409f996319027d658c640af99231902bd648c640e790e319027f654c6409f595319027c654c640afd9131902bc644c640bbd8931902ec624c6409fd94319027e650c6409f59431902bf640c640af190319039e430c640ed90431903d5310c6409fd96219027e65886409f59621902be6488640af59221903ae42886409fd95219027d65486409f19521902bf6448640af19121902df6348640b718d219027f65086409f994219027d6508640afd9021902bc6408640ed90421903e52108640af597409033d65d0240af98f40902be61d0240be597409037965d02409f987535027d61d4d40d7d93535035f61d4d40d7987535035d61d4d40d7187535035f60d4d40d7583535035f5394d40bd98653502f56194d40bdd8553502f46154d40d754c535027e6114d409f58453502de6514d40d7994535035f6414d40d7d84535035e6114d40d7584535035c6114d40d7d80535035d6014d40d7500535027e65d0d40d714f43502f661d0d40bd587435035f5390d40d714e43502fa6090d40be582435035f5350d40d714d43502fb6050d40be181435027e6510d40d7d4c435035f53d4540d714f515027e63d45409f58f515027e62d45409f58b515037753d4540f5d4f515035753d4540dd94f515037553d4540dd14f51503d453d4540d514f515037752d4540f9d4b515036752d4540ddd93515037763d4540dd98f515037563d4540dd18f515037743d4540dd90f515037543d4540dd10f515037762d4540dd98b515037562d4540dd18b515037760d4540dd58351502de6394540b758e515035f5394540d714e51502ee6294540bb58a515036f5294540ddd4651502df6354540b718d515035f5354540d714d51502ef6254540bb189515036f5254540d7d4c515035c5314540dbd48515037551145409f98c515027d63145409f988515027d6214540bd99451503766514540ddd4c51503d75314540d5d4c51503765314540dd54c51503745314540f514c51503545314540ddd4851503e75214540d9d4851503765214540dd54851503745214540f914851
  | 17 => 0x8421bd18d21087d46348421b518d21086f76248421dd94921087e65248421f9d0921087e64248421f950921087e44248421f9cc921087e63248421f94c921087e43248421bd18121087e76548421b9d9521087676548421f9d9121086e76448421f999121087e56448421b959121087e46448421f9d5121087e65448421f955121087e45448421f9d8d21087c76348421f998d21086e66348421f958d21087e46348421b918d21087c46348421b118d21087e75348421f994d21087e55348421f914d21087e74348421f990d21087e54348421f910d21087e76048421f998121087e56048421f918121086e46048421f948750087e52194021ded42500867e64940219f592500867e63940219f58e50087773194021dd0c650086bf6454021af19150086df6354021b718d50087e521540219fd91500873f64540218fd91500867c6454021cf191500863c64540219fd8d500875f635402197d8d500867c6354021d718d500865c6354021dd90550087754154021af99050086bd6414021b798c50086dd6314021f948450087795014021bd98753d02f561d4f40d7d4e53d027e6194f409f58653d027f6154f409f18553d035d5314f40d794f43d035d53d0f40bd98743d02f561d0f40be98343d02f960d0f40d794c43d035d5310f40be98043d02f96010f40b798f51d02dd63d4740bb98b51d02ed62d4740ddd4651d027e63947409f58e51d027e62947409f58a51d027f63547409f18d51d027f62547409f18951d03755114740b798f41d02dd63d0740bb98b41d02ed62d0740dd94741d037551d0740be98341d02f960d0740dd94441d03755110740be98041d02f960107409fd9731d027e65cc7409f59731d037651cc740dd54731d027f658c7409f99631d027d658c740d794e31d035d538c7409fd9531d027d654c7409f19531d02ef624c740bb18931d02fb604c740be18131d027f650c7409f99431d027d650c740af99031d02bd640c740d794c31d035d530c740dd94431d0375510c740f54c431d027f65887409f99621d027d6588740db94a21d036d52887409fd9521d027d65487409f19521d02df6348740b718d21d02fb6048740be18121d027f65087409f99421d027d6508740af99021d02bd6408740dd94421d03755108740f948421d035f5394e409f986539027d6194e40bdd8553902f46154e409fd8553903776154e409dd85539027c6154e40dd18553902746154e40d754c53902f661d0e40bd587439035e5390e40d754e43902fa6090e40be582439039e5390e40cf54e439039d5390e40af98643903ba6090e40af58243903b96090e40d794d439035d5350e40bed8143902f86050e40e750c43902bd6510e40cf594439039e6310e40e7d4c439033d5310e40e714c43902be6110e40af580439037751946409f98e519027
  | 18 => 0x9f58c540867e6115021dd984540867e60150219f58054086be64d4c21af593530867e64d4c21cf993530863e64d4c219f593530873d64d4c218f593530867e61d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530867f6454c219f191530875f6354c21dd185530867f6054c219f181530875d5314c219f990530867d6414c219f98c530875e6314c219f98453087766114c219f980530867d6014c219fd97430867e65d0c219f597430867c65d0c21d794f430875d53d0c21bd98743086f561d0c219fd96430867e6590c219f596430867c6590c21cf952430873d5490c21d7d4e430875c5390c219fd95430867e6550c219f595430867c6550c21d7d4d430875c5350c21bdd8543086f46150c219fd94430867e6510c219f594430867c6510c21cf950430873d5410c21d794c430875d5310c21bd98443086f56110c219f992510867d64944219f98e510867d63944219f59741086de63d0421b758f41086ed62d04219fd96410867d6590421cf952410873d5490421bb98a41086ed6290421bd596410877565904219d59641086f56490421dd95241087b65490421ed55241087745490421bd98e41087765390421dd14e41087e66290421bd58a41087e56290421b958a41087765290421f990a41086f660904219fd9541086f76550421ddd9541087b76450421dd95141087745450421bd18d41087765350421dd14d41086f76250421f998941087e56250421dd94941087e64250421f950941086f460504219fd94410867e65104219f594410867c6510421cf950410873d5410421bb98841086ed6210421bd984410867d65cc421bd597310877565cc421bdd9331086f564cc421ddd53310877554cc421ddd4f310877553cc421f9d8b31086f562cc421f918b310877652cc421f990b31087e542cc421f9ccb31086f660cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c421bd986310867f654c421bbd89310867f650c4219f994310867d650c4219f194310875e530c421d754c31086ee620c421bb58831087d5310c421bd5943108775650c4219d59431086f7640c421bd5903108777540c421dd55031086f6630c421f598c3108777530c421f594c3108775530c421f554c3108755530c421f590c31087d5430c421f998831086f5620c421f958831086e5620c421dd94831087e6420c421f950831087e7320c421f58c831087d4320c421f90c831087c4320c421bd98031086f76488421bd59221086f66388421bd18e21086f56288421b958a21087765288421f994a21087e64288421f950a21087e73288421f90ca21086f660884219fd9521086df6348421b718d21086f76548421ddd9521086776548421bdd9121086f56448421f5d8d21086f6634
  | 19 => 0x5544877761551219fd81544877b60551219ed81544867c6055121de181544867860551219f994544873d5415121cf990544867e63151219f58c544867e60151219f580544867e64d4d219f593534867e60d4d219f583534875f54d4d21d7953534875d54d4d21d7153534875f64d4d21d7993534875d64d4d21d7193534875f61d4d21d7587534875f60d4d21d7983534875d60d4d21d7183534875f5394d219f992534867d6494d219f98e534865e6394d219f58653487756194d219f982534867d6094d219fd91534867c6454d21d7d8d534867f6154d21ddd8553486776154d219fd81534867c6054d219f994534875d5314d219f990534867d6414d21d798c534867e6014d219f58053486de6514d21d7994534865e6514d21d7d50534875e5414d21d7550534875c5414d21d7d90534875e6414d21d7590534875c6414d21d7d84534875d6114d21d7484534875f6014d21d7980534875d6014d21d7180534867f65d0d219f997434867d65d0d219f197434875f53d0d21d714f43486f661d0d21bd587434867f6590d219f996434867d6590d219f196434875f5390d21d714e43486f66190d21bd586434867f6550d219f995434867d6550d219f195434875f5350d21d714d434867f6510d219f994434867d6510d219f194434875f5310d21d714c434867e65d0521cfd53414873c54d0521b798f41486dd63d0521d7d4f414875c53d0521bb98b41486ed62d05219f996414875f5390521d714e414867f65505219f595414867c6550521cfd51414873c5450521d7d4d414875c5350521bbd8941486ec62505219f994414875f5310521d714c41487b541105219f997314875f53cc521d714f31486ee62cc521bb58b314867e658c521d7d4e314875c538c5219fd95314867d654c5219f195314875f534c521d714d31486ef624c521bb189314867e650c521d7d4c314875c530c521f54c4314875f5388521d714e214876f5488521db55221487cf5388521db94e214876c5388521f314e214874c5388521f9d46214875f53d4121d714f504867e64d41219f593504867e63d41219f58f50486de6394121b758e504875f5394121d714e504877b5094121afd9150486bc6454121b7d8d50486dc6354121d7d4d504875c5354121d7d4c504875c5314121de540504867e64141219f590504867e63141219f58c504876e2114121b798f54086dd63d50219f98f540875e63d50219798f540867d63d5021d758f540865d63d50219f987540877661d50219f983540867d60d50219f596540873f5495021b798e54086dd63950219f98e540875e63950219798e540867d6395021d758e540865d6395021dd986540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf550540867e6415021cf990540867e6315021
  | 20 => 0x875f5394e219f992538867d6494e219f982538867d6094e219fd91538867c6454e21d7d8d538876f6254e219fd81538867c6054e21af99053886bd6414e21d754c538867e6414e21cf990538863e6414e219f590538873d6414e218f590538875e6314e21db58853887766114e219f980538867d6014e219fd97438867e65d0e219f597438867c65d0e21cf953438873d54d0e21bb98b43886ed62d0e21bd98743886f561d0e219fd96438867e6590e219f596438867c6590e21d794e438875d5390e21bd98643886f56190e219fd95438867e6550e219f595438867c6550e21cf951438873d5450e21d794d438875d5350e21bbd8943886ec6250e219fd94438867e6510e219f594438867c6510e21bb98843886ed6210e21cf953428873d54d0a21b798f42886dd63d0a21bd98742886f561d0a21bb596428876d6590a21db952428876c5490a21bb98e428876e5390a21db14e42886ed6190a21bb982428873e5450a21cf55142886f76150a21bd185428876f6550a21ebd91428876e5450a21eb951428872e5450a21eb551428876c5450a21bb18d428876e5350a21db14d42886ef6150a21f9d8542887e46150a21bb181428875e53cca21d754f32886f661cca21bd587328876d65cca21bbd9332886ed64cca21dbd53328876d54cca21dbd4f32887ce53cca21db54f32887cd53cca21f998732886ed61cca21f958732886ee60cca21d7d4e328875c538ca21d794d328875d534ca21bdd8532886f4614ca21d7d4c328875c530ca21f34c832886ed650ca21db59432886ef640ca21bb590328876f540ca21db55032887ce630ca21dbd4c32887cf530ca21d3d4c328876d530ca21f314c32887ce430ca21f350c32886ed610ca21bb98032886de63d0621b758f41886ee62d0621bb58b418873e5490621cf55241886ee6290621bb58a418873e5410621cf55041886ee6210621bb58841887b54110621d794e318875d538c621bb98a31886ed628c621f30ca31886ef624c621bb189318875e530c621d754c31886ee620c621bb58831887cc320c621f54c431886f565c8621dd597218877754c8621dd553218877653c8621dd14f21886be64d4221af59350886de63d4221b758f508877b50942219f992508867d64942219f98e508867d6394221dbcca508876c3294221ddc86508867f64542219f191508867f63542219f18d508876e4254221db509508877950142219f98f544867d63d51219f983544867d60d5121cfd5254486de6395121b758e544867e64951219f98e544875e63951219798e544867d6395121d758e544865d63951219f586544877561951219d586544867e60951219f58254486df6355121b718d54486fb6055121be181544873f64551219fd8d544875f635512197d8d544867c6355121d718d544865c63551219fd8
  | 21 => 0x6390431b758e410c6f56590431dd596410c6756590431bd592410c7765490431ed952410c7b55490431dd152410c7d66390431bd58e410c7d56390431b558e410c7765390431f590e410c7d54390431bd98a410c7765290431f58ca410c7d43290431bd982410c67f6550431bdd95410c7776550431edd91410c7765450431dd151410c6f76350431f598d410c7d56350431dd94d410c7d64350431f550d410c6f46250431dd949410c7d63250431f50c9410c6f460504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431bd984410c6df64cc431b7593310c6de62cc431f5907310c7d541cc431b7983310c6dd638c431d794e310c6f7648c431bd592310c6f5638c431b558e310c776538c431f594e310c7d6438c431f550e310c6f6628c431f58ca310c7d4328c431bd982310c67f654c431bbd89310c6ec624c431b7d95310c75f654c43197d95310c6df644c431b7591310c7cf624c431b7189310c7cc624c431b3189310c6df614c431d7945310c7d7414c431f5905310c7d5414c431f5105310c6dc604c431bdd95310c777654c4319dd95310c6f7644c431bd591310c6f7634c431f5d8d310c776534c431f594d310c7d7434c431f590d310c7d5434c431f510d310c7e7624c431bd189310c7e4624c431b9189310c7d7324c431f58c9310c7d5324c431f50c9310c6f4604c431f5d95310c6d7654c431d5d95310c7d7644c431b5d91310c7d6644c431f5591310c6d5644c431f5191310c7d7544c431f5951310c7d5544c431f5151310c7d7624c431f1d89310c7d6624c431f5589310c7d4624c431b5189310c7c4624c431b1189310c7d7524c431f5949310c7d5524c431f5149310c7d7424c431f5909310c7d5424c431f5109310c7d7604c431f5981310c7d5604c431f5181310c6d4604c431f54c7500c7d53194031ded42500c67e64940319f592500c67e62940319f58a500c75e3294031d70ca500c6bf6454031af191500c6ef6254031bb189500c7d531540319fd91500c73f64540318fd91500c67c6454031cf191500c63c6454031d790d500c75d43540319fd89500c76f62540319bd89500c67c6254031db189500c66c6254031dd905500c7754154031af990500c6bd6414031bb988500c6ed6214031f54c4500c77950140319f98f548867d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548876d62952219f982548867d6095221cfd91548867f63552219f18d548867f60552219f181548873d5415221b798c54886dd6315221cf990548867e6315221d798c548865e63152219f58c548875d63152219758c548876d6215221dd984548867e60152219f580548867e64d4e219f593538876d62d4e21dd987538867e60d4e219f583538
  | 22 => 0x531f9d4b314c77452cc531f914b314c76452cc531dbd4a314c76c528c531d7d52314c75d548c531f3d4a314c75c528c531f314a314c74c528c531f5d46314c76f52d4131db14b504c67e64d41319f593504c67e62d41319f58b504c6ee6294131bb58a504c76f5294131db14a504c77b5094131afd91504c6bc6454131bbd89504c6ec6254131dbd49504c76c5254131dbd48504c76c5214131de540504c67e64141319f590504c67e62141319f588504c7773114131d78c4504c6ee62d5031bb58b540c67e63d5031d798f540c67e62d5031db98b540c66e62d50319f58b540c76d62d50319b58b540c67e61d5031dd987540c67e60d50319f583540c67d6595031cfd52540c6ee6295031bb58a540c75e63950319f98a540c76e62950319b98a540c67d6295031db58a540c66d6295031dd986540c67e60950319f582540c73f64550319fd89540c67c62550319fd81540c67c6055031cf550540c67e6415031cf990540c67e6315031d798c540c67e62150319f588540c67e6115031dd984540c67e60150319f580540c67e6494c319f592530c67d65d0c31bb98b430c6ed62d0c31bd587430c67f6590c319f596430c73e5490c31cf552430c6f66190c31bd586430c75d6590c3197596430c6dd6490c31d7952430c79e5490c31e7552430c75c5490c31b798a430c7d66190c31b7586430c7d56190c31b5586430c6de6090c319fd95430c6df6550c31d7d95430c79f6450c31d7951430c75c5450c31b7189430c6df6150c31f5985430c7d56150c31b7181430c67f6510c319f594430c73e5410c31cf550430c6de6310c31bd984430c6f56110c31af993520c6bd64d4831dbd4a520c67e64948319f592520c75e4394831d750e520c67e60948319f582520c67f64548319f191520c77461548319fd81520c67c6054831db548520c67f65d08319f997420c67d65d0831b798f420c6dd63d0831db94b420c76d52d0831bd987420c6f561d08319fd96420c67e65908319f596420c73e5490831cf552420c67f65508319f595420c67c6550831b7d8d420c6dc6350831bdd85420c6f461508319fd94420c67e65108319f594420c73e5410831cf550420c6de6310831b758c420c76e5210831db548420c6f66110831bd584420c76e52cc831db54b320c6f661cc831bd587320c67d658c831b7596320c75d658c831b7d92320c6dd648c831d7d52320c75d548c831b798a320c75d528c831f5d86320c6dd618c831f5186320c6de608c8319fd95320c6f7614c831bd984320c6f5610c831d7d50320c75d540c831f5984320c6dd610c831f5584320c6d5610c8319f992510c67d6494431d790e510c75d4394431d78ca510c75c32944319f597410c6de63d0431b758f410c6ee62d0431bb58b410c67f65904319f596410c73e5490431cf552410c6de
  | 23 => 0xf552418c6de6390631b758e418c73e5410631cf550418c6de6310631b758c418c7b54110631b7597318c75d65cc631b7d93318c6dd64cc631b798b318c6de60cc631bd597318c77565cc631ddd53318c77554cc631dd94b318c6be64d4231af593508c6ee62d4231bb58b508c77b50942319f992508c67d64942319f98a508c67d6294231d78ca508c77731942319fd91508c67c6454231d790d508c75d43542319fd89508c67c6254231de540508c67e62d51319f58b544c67e60d51319f583544c73f5495131bb98a544c6ed62951319f992544c67d6395131d758e544c65d63951319f98a544c76e62951319b98a544c67d6295131db58a544c66d62951319f586544c77561951319d586544c67e60951319f582544c6ef6255131bb189544c6fb6055131be181544c73f64551319fd8d544c75f63551319fd89544c76f62551319bd89544c67c6255131db189544c66c62551319fd85544c77761551319fd81544c77b60551319ed81544c67c6055131de181544c67860551319f994544c73d5415131cf990544c67e62151319f588544c67e60151319f580544c67e65d0d31cfd53434c73c54d0d31bb98b434c6ed62d0d31bd987434c6f561d0d319f996434c67c6550d31cfd51434c73c5450d31bdd85434c6f46150d319f994434c79d4310d319f993524c67d64d49319f983524c67d60d4931dbd53524c76e54d4931db553524c76c54d4931dbd93524c76e64d4931db593524c76c64d4931dbd8f524c76f43d4931db90f524c76d43d4931db10f524c76f61d4931db587524c76f60d4931db983524c76d60d4931db183524c76f5294931db548524c67e64149319f590524c67e60149319f580524c6ee6514931db994524c76f5414931db950524c76d5414931db150524c76f6414931db990524c76d6414931db190524c76f6314931dbd0c524c76e4314931db50c524c76c4314931dbd84524c76d3114931dbd80524c76e6014931db580524c76c60149319f997424c67d65d09319f197424c6de63d0931b758f424c76f52d0931db14b424c6f661d0931bd587424c67e65909319f596424c67c6590931b798e424c6dd6390931dbd4a424c76c5290931bd986424c6f561909319fd95424c67e65509319f195424c76f5250931db149424c67e65109319f594424c67c6510931dbd48424c76c5210931db14b324c76f528c931db14a324c6f6618c931bd586324c6f7614c931bd185324c67e65d0531cfd53414c73c54d0531b798f414c6dd63d0531bb98b414c6ed62d0531dbd4b414c76c52d05319f996414c76f5290531db14a414c67f65505319f595414c67c6550531cfd51414c73c5450531b7d8d414c6dc6350531dbd49414c76c52505319f994414c76f5210531db148414c7b54110531dbd4b314c76c52cc531ddd53314c77554cc
  | 24 => 0x43cc6f66190f31bd58643cc73e5410f31cf55043cc79d4310f31bd98443cc6f56110f31dbd4a52cc67e6494b319f59252cc67e6094b319f58252cc67f6454b319f19152cc67f6054b319f18152cc6be6414b31af59052cc76d5214b319fd9742cc67e65d0b319f59742cc73e54d0b31cf55342cc6de63d0b31b758f42cc6f661d0b31bd58742cc67f6590b319f99642cc67d6590b31b798e42cc6dd6390b31db94a42cc76d5290b319fd9542cc67d6550b319f19542cc73e5450b31cf55142cc76e5250b31db54942cc6f76150b31bd18542cc67f6510b319f99442cc67d6510b31bd98442cc6f56110b31bd98732cc6f561ccb31cf95341cc73d54d0731b798f41cc6dd63d0731bb98b41cc6ed62d0731bd59641cc7756590731dd95241cc7745490731bd58e41cc6f66290731dd94a41cc6f66090731cf95141cc73d5450731b7d8d41cc6dc6350731bdd9541cc7776550731edd9141cc7765450731ed95141cc7365450731ed55141cc7745450731bdd8d41cc7d76350731f518d41cc6f46250731dd94941cc6f46050731af99350cc6bd64d4331bb98b50cc6ed62d4331ded4250cc67e64943319f59250cc67e62943319f58a50cc67f64543319f19150cc67f62543319f18950cc7764154331dd50550cc7795014331d758f548c67e62d52319f58b548c77661d52319f983548c67d60d5231cfd52548c75d63952319f98a548c67d62952319f982548c67d6095231cfd91548c67f62552319f189548c67f60552319f181548c73d5415231bb988548c6ed6215231cf990548c75d63152319f988548c76e62152319b988548c67d6215231db588548c66d6215231dd984548c67e60152319f580548c73e54d0e31cf553438c6ee62d0e31bb58b438c6f661d0e31bd587438c6dd6590e31d7596438c75e5490e31d7152438c6de6290e31b7586438c6de6090e31cf951438c73d5450e31bdd85438c6f46150e31d7d95438c79f6450e31d7951438c79e5450e31c7951438c79d5450e31d7151438c6dc6250e31b7d85438c7d76150e31f5185438c6dc6050e31dbd4a528c67e6494a319f592528c75e4394a31d750e528c67e6094a319f582528c67f6454a319f191528c67f6054a319f181528c6be6414a31af590528c76d5214a319fd97428c67e65d0a319f597428c73e54d0a31cf553428c6de63d0a31b758f428c6f661d0a31bd587428c67f6590a319f996428c67d6590a31db94a428c76d5290a31bd986428c6f56190a319fd95428c67d6550a319f195428c73e5450a31cf551428c6df6350a31b718d428c76e5250a31db549428c67f6510a319f994428c67d6510a31b798c428c6dd6310a31bd986328c6f5618ca31d7d52328c75d548ca31f5986328c6dd618ca31f5586328c6de63d0631b758f418c6ee62d0631bb58b418c73e5490631c
  | 25 => 0x75f5390d41d714e43506f66190d41bd586435075f5350d41d714d43506f76150d41bd185435067e6510d41e750c435067e63d49419f58f525077561d49419f983525067d60d4941dbd4a52506df6354941b718d52506fb6054941be181525076d52149419f98c525067d63149419f980525067d6014941b798f42506dd63d0941bd987425076f5290941db14a42506f66190941bd58642506f76150941bd18542506de63d0541b758f41506ee62d0541bb58b41506f663d0541f598f41506d663d0541f558f41506f662d0541f998b41506e662d0541f958b41506f560d0541edd46415067e63d41419f58f505067e62d41419f58b505077b5094141b7d8d50506dc6354141bbd8950506ec6254141de540505067e63141419f58c505067e62141419f58850507774114141cf904505075e6395041d758e541076e6295041db58a54106ee62d4c41bb58b531075f5394c419f98a531067d6294c419f982531067d6094c419fd89531067c6254c419fd81531067c6054c41d754c531075e53d0c41d754f43106ee62d0c41bb58b43106f661d0c41bd587431067d6590c419fd95431075e5310c41d754c43106f66110c41bd58443106de63d4841b758f521076f52948419f98e521067d63948419f982521067d60948419fd8d521067c63548419fd81521067c6054841db54852106de63d0841b758f421076e52d0841db54b42106f661d0841bd587421067d65908419fd9542106f66110841bd58442106de63d0441b758f41106ee62d0441bb58b411079e63d0441e758f41107ae62d0441eb58b41106be60d0441af592411073e5490441bd59241107765490441ed95241107765390441dd94a41106f660904419fd9541106bf6550441cfd95411063f6550441afd85411073e5150441af18141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441dd94d41107b74350441ed50d41107765250441edd0941107b54250441bd181411077b50940419f98e501067d63940419f98a501067d6294041b7d8d50106dc6354041bbd8950106ec62540419fd8d501075f635404197d8d501067c6354041d718d501065c63540419fd89501076f62540419bd89501067c6254041db189501066c6254041dd90550107754154041b798c50106dd6314041bb98850106ed6214041de540501075e63d53319f98b54cc67d62d5331dd58754cc67e60d53319f58354cc73f54953319f98a54cc67d6295331dd58654cc67e60953319f58254cc73f64553319fd8954cc67c62553319fd8154cc67c6055331cf55054cc6ee6215331bb58854cc73e6415331d798c54cc67e6215331db98854cc66e62153319f58854cc76d62153319b58854cc77561153319f98054cc67d6015331bb98b43cc6ed62d0f31bd98743cc73e5490f31cf552
  | 26 => 0x110f41b798f52d06dd63d4b41d794f52d075d53d4b41d794e52d075d5394b41dbd4a52d067e6394b419f58e52d067e6094b419f58252d076f5394b41db94e52d07ce5394b41d394e52d076d5394b41f354e52d074d5394b41db14e52d076c6494b41dbd8e52d076e6394b41db58e52d076c6394b41dbd0e52d076e4394b41db50e52d076c4394b41dbd8652d076f6094b41db98252d076d6094b41db18252d075e5354b41d754d52d067f6354b419f18d52d067f6054b419f18152d076f6554b41dbd4d52d076e5354b41f394d52d074e5354b41db54d52d07cd5354b41d354d52d076c5354b41db99152d076f6354b41db98d52d076d6354b41db18d52d076f4354b41db90d52d076d4354b41db10d52d076d6154b41dbd8152d076e6054b41db58152d076c6054b41b798c52d06dd6314b41d794c52d075d5314b41db54852d075e53d0b41d754f42d06f661d0b41bd58742d06de63d4341b758f50d075e53d4341d754f50d06ee62d4341bb58b50d076e52d4341db54b50d075e5394341d754e50d076e5294341db54a50d077b50943419f98e50d067d63943419f98a50d067d6294341d794d50d075d5354341db94950d076d52543419fd8d50d067c63543419fd8950d067c6254341b798c50d06dd6314341d794c50d075d5314341bb98850d06ed6214341db94850d076d5214341de54050d075f5394e419f98a539067d6294e419f982539067d6094e41bbd8953906ec6254e419fd89539076f6254e419bd89539067c6254e41db189539066c6254e41dd185539067f6054e419f181539075d5314e41bb98853906ed6214e41bb98b43906ed62d0e41bd587439075e5390e41d754e43906f66190e41bd586439075e5350e41d754d43906f76150e41bd185439076f5294a419f98e529067d6394a419f982529067d6094a41b7d8d52906dc6354a419fd8d529075f6354a4197d8d529067c6354a41d718d529065c6354a41dd185529067f6054a419f18152906de6314a41b758c529076d5214a41b798f42906dd63d0a41bd58742906f66190a41bd58642906de63d0641b758f41906ee62d0641bb58b41906bd65d0641cf597419079e63d0641e758f41907ae62d0641eb58b41906be60d0641bd597419077565d0641bd98f41907d663d0641b598f41907d563d0641bd98b41907e662d0641b998b41907e562d0641bd58341906de63d4241b758f50906ee62d4241bb58b509077b50942419f98e509067d63942419f98a509067d6294241ddd06509067f63542419f18d509067f62542419f189509077950142419f98b535067d62d4d41dd587535067e60d4d419f583535075f5394d41bbd8953506ec6254d41bed8153506f86054d41d754c535067e6214d419f588535067e6014d419f580535067e65d0d41bb98b43506ed62d0d41bd9874350
  | 27 => 0x43f954951d0f655254743dd99151d0f756354743ddd8951d0f766254743dd58951d0f746254743ddd8151d0f766054743dd58151d0f746054743bb98851d0eed6214743db94851d0f6d5214743dd54451d0ef661d4343bd58750d0f7651d4343dd54750d0f765194343dd54650d0f7b50943439f98650d0e7d6194343dd94550d0f7551543439fd8550d0e7c6154343bd98450d0ef56114343dd94450d0f755114343de54050d0ef661d0e43bd5874390ebd65d0e43cf5974390fb661d0e43ed5874390ebe60d0e43b75974390f5d65d0e43b79874390fd661d0e43b59874390fd561d0e43b75834390f7751946439f98a5190e7d62946439f9825190e7d6094643bbd895190eec62546439fd895190f6f62546439bd895190e7c6254643db1895190e6c62546439fd815190e7c6054643bb9885190eed6214643dd5445190ef661d4243bd5875090f7b5094243d7d0e5090e7e61942439f5865090e7f61542439f1855090f795014243bd9874350ef561d0d43b79874350fd661d0d43b59874350fd561d0d43b75834350f9f5390d439f98b5150e7d62d45439f9835150e7d60d4543ddd465150eef6254543bb1895150efb6054543be1815150f7551145439f9885150e7d62145439f9805150e7d60145439f9875050e7d61d4143ded425050ef76154143bd1855050f795014143d7d0c5050f3e43141439f9845050e7d6114143dd9865410f756195043bd9874310ef561d0c43ed9874310fb561d0c43af9834310ebd6490c43cf9524310edd6490c43d79524310f9e5490c43b79824310e7f6550c43afd954310f3f6550c438fd954310ebf6350c43cf94d4310ebc6050c43b7d954310f5f6550c4397d954310edf6450c43e7d914310f5e5450c43e79514310edc6050c43bb98b5110eed62d4443ddd465110f5e4394443d750e5110e7e62944439f58a5110e7e60944439f5825110e7f62544439f1895110e7f60544439f1815110f755114443ded425010e7e61940439f5865010ef76154043bd1855010f5e4354043d750d5010e7f6154043ddd855010e7761540439f1855010f7461540439d1855010ef66114043bd5845010f795014043bb98b53d06ed62d4f41d7d4e53d067e6294f419f58a53d067e6094f419f58253d075c6494f41d7d8a53d075e6294f41d758a53d075c6294f41d7d8653d075d6194f41d7d8253d075e6094f41d758253d075c6094f419fd8953d067c6254f419fd8153d067c6054f41d7d9553d075e6454f41d7d8953d075e6254f41d758953d075c6254f41d7d8553d075d6154f41d7d8153d075e6054f41d758153d075c6054f41d754c53d06ee6214f41bb58853d075e53d0f41d754f43d06ee62d0f41bb58b43d06f661d0f41bd58743d075d5390f41d794d43d075e5310f41d754c43d079d4310f41bd98443d06f56
  | 28 => 0x60004015002000f001000b0000006002801000000020010004004000c0090001000c002000000000300000048000000c011000c00c000801d001400300000000010047000000c000c000004400a00000100038000001400e00040020054006010001500140050024020009800100700010038006004800f000c00700140460004009002401b00000030010002000c001004c009000000d0004016008000b002000100240010000007004c0000014007000003500100040050000001c0070004027000800300040000004005002c000000000000340040000006000400800000090020004003000c001000600ac008003800e001c0000064035001401f000000200340000080006004c008000000100e4058004c000002c000004c00300000060004002001400e005400a00080030014000006c07a016000800280000018004001800e0000012000c00001a400d001c00a010c00600440020008006000400100000030000000000400000380080038010000001f00400130008001001c006000c01e0038001000c000007c0050000003006c00100000000080029005c008000c000001400000000000070002000000000040000004001000800000140000044004007000000240030000001000800c00c4000001801900400010000014000c0240090007003c00700000000000001001000000080200000004001c0020008006003400300200140000099002c010004c0000010005004400d000801600300020000008000c00100300050034006000c008000800900e4014003400400040070000011003000d00100210004006003c006001001f0014000001400d001800500180030038008001000a001c0000000003004c01c000c0390048008000c001001801300240110124015000000700a400200d80020034004000001a00140060004001011c00e000400a00000010024006000000300400030004006001800000ec00001ec008000800700440000000000000c005004001101580000000014004400e00000110000007001800b001800000040010008000000400300000000008009000000f006800c000000000080020018020003400201240200010000001002800bc0020004002002c000000800f0020009000c00c0040022001c0030010002001c00d0004012000800d0034000007801c002c004000402800080150000003005c003002800b000c04cbb98b51d0eed62d4743ddd4651d0e7e62947439f58a51d0e7e60947439f58251d0f775294743dd94a51d0fe65294743d994a51d0f746494743ddd8e51d0f776294743dd98a51d0f756294743dd18a51d0f776094743dd98251d0f756094743dd18251d0f6e52547439fd8951d0e7c62547439fd8151d0e7c6054743ddd9551d0f775254743dd94951d0fe65254743d994951d0f7552547
  | 29 => 0x400a000800e003c0010004003000000b00000110010000005c00700180050028003009000301080080030000001800100cc001000000000000020010002002000000000030008003001000000140010010001002801b000000200000130040005008800600040040004002005400000180010004003002c01a0014000001c0010004008001000900100030008000000c006001400400e8001007000000100000010004004800000040090004001003800a003404200000270000001000400b002c008002800100200010004009001c0160010001000800200040000008013003c00c0004002005400b000800b0008000001400100580000000001000400b0000002003801400380000000001000c01a000000000100010000007000c00500100000000018001c003005400900a800200040090000000003800e00a400a000801c00040000008000000400700c40000000001000000700080000004003000003c00100030020000014c00a002400c001000200240060000031000000c000c02b0018000000c006000800e000c000001c0100000001002c0060034000001000000040000030004000000100480130058004000c00400000000000001003801e0004002001400c000c0090010001000800b006800d0000005001c00100140000010000004c002002002f002c011014800b0008000001800a006800800340000054002001c0160028000000c00a000400c004c0050008009005000900080080010000002400000140050070002004001a0008001003000300080120024003000c000001400a0060005000400101d4000001c0490014000000c000004c00f0004008000000700080000000015000c00a000c00101740060000001002000b000c00100040050070000000000400080070054004002c005000802c000c005008400300040020014008000000000080050000032000800100300000004001007400600200080010005004401b000800e0008000002800e00700070000004000c00900140500018001000000e000400e00000000000001000400200b80010044001000400a002c000003c005009800400000000028003000c00500180080060003002c00000b8010002c0020000033000000800080140034003001400200040000034002006800d0008022000c0050000002004c006001c002000c00500380030000004001002f000c00e001c00100680030010000000c000001800e001400100a0003006c00000780010008000000000100cc0080010007003800000040020000000000800f001400b000800b0010001002400d004400000040070054000002c00e019c003001000c00f400500440200018004004c00b00900090008001000400100200000004009002c0110008028000000000f401b003c00a007800b00040090004
  | 30 => 0x2000400300040040008022000c004001000c0000002009000100080030044008000800000140040038002002c01c0008000000c000007c003003400000a4000003800000000010014000004000500000020040000001800a008c0020030000000c002000000400000010090000002c0060024013000000200000000014001000c00100080270004012001c004001c02000000010028013001400a001c009000000001a80050008000000001000140010008003000400500180000004003000c0050000007000400300ac02b002c002003800f00000000068003000c00000cc0020088000004c0020020010002402d009400c009c000000000000000020024002000401c0000002002c00000180140000007000000001a4000000402a000c004002800400080000008005005400c000000b0058003000000000000060014005001c00100100020000004000c0010018002000000000080160020002000001f0014002000800a00000020000006003c00b0028003001400a00140010000000000000b0000003002000b004c027002c0010088002000c011001000000640030000000000c002000800400840070038009000c00700240100014008006800000040110000011000402a005000600040180004009000002100b8004000400000080020000012001c00e001c002000400000000010004000001000f00ec00e000c0040050003001800800880000000012008c004006400700000020000001004403e00280040064002004c00a0000000000000600040090030001000c006001001d0028006000800b01700040000000000000400340010000049000c005003801900400010010003000000e0040001001c009002c00c00140020014003003c018000c002005000400000020018004002400c0014008000001e00000020018013000c006002000100000000008001000000200200020000000000c001000c003019c000000c01b000000f002c0000090002000000600040000040004009c00200200030008008009800100180040038004000800b002002e0004002000400000080140004000000001d002800c00600140018013001400b001000b00000010028001017801f00000060014009002800b00040070004016000803400000000008002000000000140000000000000c0010000010001400700300050034008000401f0004018000000100000110010004002001f00080010000007000c024007c011002c00100c400400140240004000000400d0000004000800f0000006000004b00000020000003000000100000290000000001c01d000400400f400200c8005005c004001000000040050018000003c0010014008001000000480030008007002c000000000200640000000007000000c00180160010005000800100040000038001
  | 31 => 0x1402d0028000005c011000c011000000e0010002001000b00240000014002002000000000030044000001c0000018000015000700080120010009000001e001c00c000006a0068002001c00000340000004014004400900f4004003c000000c003007c0090000005005800d00000000000058002800800100130000003000400a001c01600180070034001000800000000070054000000c003000400500000030000000001400000e000000280000010000000c000000c008012400200cc04000080000010000002c0030014006003c001003800300040000008038000000f002400000100000034006000000c00a0010000000000080010000000000804c002000500b00000000005000000f001000700000050014000000000d0070001003400f000000a001c00700a00080004000003000a0010008002000000000000028000000000100000030018009000401f00a000900000050020002000c001000000000040000074000003c008000400f00400060000000000401900100010000003000000d00000000040025002400300100000008007004800b0050004002401b0008018000400f0040008000001c0000001001c003000000800000060000007000000a0008000000400b002c07c00000000000000003800000680220004004000400400040120000011003001000100100028000000c0060024007000800300080000000000004c0580040003001c010001c00d001800000280010004006000800100040030010008003000200000030010017003001e00480100000005000000c000000400140020010004000400f00000130008007001c00100000050004000000001000cc002002c0000018021000c0080080003001c01c0018000000000400280000078000000800500040460004002000400000000190090000000000f00000000020000000c003000000000280050000012003004f0004002001c008000000a00440070018002003400100480070004018000000d0010000000c000009c00100000010030002000801b0058009002800a0038002000c006006800000000020004010000c0030008009001000c00400030004001003800000040000084000000401e00000090000001000800300180010000002000800300040020024001003400800280010040003000800800000070000008000000000240000004001000400f00080490000000001401c004c0020004000000001c004c0080044000001400a00040070008016003c003000800100000080008000000c002001000a007800a0000000010400c0000003001c000000000600c800000fc01b00480010004015004c0000010000001c00100800000000001000801c001c005000400500c0000001400000180030010005001c00600240060054006003c0020014002000
  | 32 => 0x2f1c130ed3c541918a0002723711873e00000000aa8f1c4b3558f0000d653798daa1112acc00021ec2c2c9a630180009fd01d86994ae84a1e0c8b9a18054b6eac88fa1bacb359da7429e8dd98907920f32eed13795a12b6117e0bc95b081e2f56338ad00513ad686b3a112000000000015388d292f932b22dfa611d94305a82c9b983de983c4ca0ec96d000d2d2ab3623761b60000000000047787f20a701b0acd8000668a6403480000660edaab57a4889ca000000024040002d2679f40006e704489310000a405742b5f0000000226d71280004d819b80001ed011080710001b07359c0001bc8de807f253eba1400015c000000000000001f7c35aa93e000000010e9c4e0002c58b2800009b6e3a2671a188ab403507c79a44000000000025d44831422000000008504943aaa098984a2e144919ff5be2a7891b0a4856b18dd91aa3b4599a6ce40aaaa21a2a903000000007b24a672d254e6aae5c27ad8000acb93ec4cc118020b8000a458a7c9a30e2037aa96495b4b666bc0dcb17797a66081da4b6babb66bee14823300004d6501c4700036000000073500007a0162f023282a9aa9f0c0e391302c3ef0a19a16af1cb017f1ad21c40ba9e20813185200019dcac961c070d0c58aae00008b8e44800018b41242ecd27e00005508000a2bc0005b2800062295e400005a2ae28000000000000000000000000000154800000004248b8800000000000e4e6fb027c17018ef0000bf80000000002800a00800150004008001800100100080000000000c00e013c0050048006000400000a001a000000900240030004016000000100000030010029000c006000c0000000028000403c000801c000c000003c0000054000002000000d400001180000008000008400300140010018000008c002000801700000000000004000801a008c001000400000000000024001000401a00080000004000002c001001801f00cc0010000000003c002000000000040390010001000c0410024000000003700340080000000000000a0008000003c000000000f0010002002000300100070000026001800100000030008001004400200000010004006004c00600040000000005001c0050004001001800200000060014025000004b0034002003802b0004000000800000040040010027000000e0048003002000c0008001001801d00000080000001001c004007c0110060022000800a0000000000c003009800c002400100240000014000001400700cc0220014000000000600000430054000000000c006800100080080004000000801500200070000005001800f0040000003401a000000000040410020001002001e000800000200010000000006000100080020000000000400d0018000000800c00cc000000400100080000008000000401c0008000000000
  | 33 => 0xb41118d0f585c84a8958058095c324380008688180052c00000a80007fd9e9b1b22f127470d548f61fd896e01448e4135c35995c0aa6a6386ea2abe609e29a7ca22c56dcdffe6cac3341ee850907900008c2aa9684a28343b48fb600024ce00013e9aef035c7c3e8765aa504085c00009d922d57fe1e396fd00000eb16eb3ce0ee058a94a00cc000089328de8af888348616dc8305e1605599aa68d6708086022009fa00a648046840b10489e80c6881ca018401a92c00000008c5000000000000002b4c008088c00000002bb990e1b7256c20322f12b4654f9d783f059f14c779ae6a218224c647111d992fdf0094957d98f8800e85d1cd964c81d605091663d40dce000184a9c600007e1000017cc000764000048480006459e22792a67698280002d02ab64622058000298a0000d0ca5695bd88980008508db38e586e6a20a2cf7aa400080cec787478bdbb1f9b4f00005308a293940891e876545dca95c18748c1420c4d3a9de27f801889387457b8e6f078b2e4f4995b944fa2e04a40a6dda4c0ec19225ec90000000000000000000c47bc929d288800031000004c482b05420000000176c5a503775f38fc8000188e02343a00001606973aed2000089a8180155a949b323d581867198680b2895ed8496c084489eaa07391ab10300001b88000000210d307de3a00000008f2088089406c660c12ea6df14f0b4380e5673942b00020f80d109a895d594e4978af6bbf0d2e5a20bb8991047a0b1596cba4ce6aa8e95d03928ff2a1a0154574a61dabb97d353dc28a45426fe19a87aa9930504a5ba578b7cd28a21b9a7619317ea63fa6d4000212c000029e79e080404de83c0002a0a7921012479a7fc5bb4b864230ff4725000636e80006cea77b31e9a5021e132a14a9e76412aa64000154e90c829998262de00000002b725b678d87b6bd28e989371883331a02455285fe0de2c5a74a00004691746192047073e18065ba0aca05e2ef8a461fd28011ca95ce593d51e182c7d283aa33b12454d023402470e5083b82f6b9624fab05acea9a7110205810d27d7412c3a4c9eabab16b845624b87b8800005d000051182b595815d4025c00000011e200015c576716a27d35f5750e9f157aca8d83f10b7201280002c02e9800018785b8dd40945800016a5210bbec00075806720000efe07ea8041442900abacb8c729a732981288a68a00be295aaaea29acd479fa1cc35184e858b1dd82de979a91529db271037b3b90ca43a5a19478c0be32ae13299978a820000000ac3044e0e20000703895c0002e8a000000081a00001ff957eba816ce54c0000358cb946a2690f8b05e3e0001877581ede85eea6c8ba22864b560856250166e2d08b3e0f11f5a5a680460000d94942a4f400008c807a40003b290a39dca1b279b800089a0d825db92c3a641cca1c
  | 34 => 0x45a2ee1d20af304226ba1c2d05075420802801ecf94a001cba1ae44b94d942000000016d9c11464000014c800036824560002f40905277400022540002ea12ca899681f67ceae60000a98001e00024f2117a90493512d821b2c9c8cf019c89640e976b816816cd00e0000dd874a80000002bc4b5b16c52bddedeb2baa3404181485eb952e9a58a5e4de42707219c1785104d699a18e0b1f5b0b8b22d4c6e10a92b21981950d1e344015f780e9a458127163c70a27d099b008709485fc100da34619af0451a148aa2f87f337ea7ff4590d5a10003e0b052b443af01b2b730c262bc64b0349a99c47dd7e5a8888e4507805499f1f9427a2ae282844f64eb12bab5b8d0a80c52404c0a9bc7e7286a29a16f0aef9f0e0a5a0227d5231f8fe24be7ce04a2b8eadd8621e9125598d5266d241eb672d0654022852448cf41a583c0033195a33315540001a9ab3382af00002e60000000746ae34aa30a849544af4a1018aa805ad6a8699bf08f1874236c8422a4a82e28211c6837895924b18add04caae45f780001f9800036d2c18668d2e3aec253b32f2b802f787a4741047886d8150ad18a3242624ac0d9c0000000000000255051cadf770b89f01e99b716ea625251240000002c288332eda684a15a81882ca64b8e9784f000078f00008d91f8aa970c8d72114d23418c3a84410f862a253f9bf4c623afaab44bfae781bfa6592ad1fcb01b233463b2cb8b0aa11a0169b0d04911bc51047d80bb6af011b9cc72d1a1e8669ad70a22c6c4bb2ec1c641eb484da8b3c1b592c80dd10f01c8145a7d648aa3ec1333616e5da6f00ede1fe1f4805f933d2701a4b4cd07b4ae0a36225da1c69b4a8244cf9174084a4ec97e02fc42d1b288a3a94e55d9f711b14ab243925a804592640000b9ea1dd30a00019981b000001d4000000028e4602209a17500006950584b5c80008d8c00047d10280002c3fb08077886bdee089100002ec97e8b3b0b5890a081e5a196c0188918681feca83822568a5f0cee9caab843028ef89852c02ab001c8475d976a68915297c816c7f5145822d02a260edadf60eac2cafc8a8372f156098c8beaae7213e0000254766982487e8944a240e5e1056213786800033f28184db800050f9bdc0001c360002e7ebbd84d51550a88089aa2a64f83c860d99da90400007d31e924ec1d455b6438217405800000e580000000aaca9ea000018500022553578004a4ca03c5aa9a993580f7c47a9af66c958f19502b92450d5223d08ad63869d3205014cc1bb87329568000a5989ccaa1151a858417ca216c2eb7e1ef4100883a8ec04b283a8b1692027508a6c59087e18c24e040000000d3f1e400001caaaf230407187a99a338a08c3e77e800068c611e0faab508679f2a9668a10ad800008baa69ea1fa43abc91288bcfa5485c08a52977800044980
  | 35 => 0x59994aa8660b1cb3009cc68638310738d7828845660d10000012656c00000008242ef013a90f93c2270aebe000018c6af000000000005f4993a0000be179810803981a961a900000000830af3556c6fe20003342e3cb3018a00d2185170b050061422da9c80bda00019db11d18d0000000000019060002eef24280006b8e090abd000094864e600000000000ea09320000000087444f9c2a6cf09c86de1c1ab3e988c02b12cc0002ef27618c7938c84289ba86bea0fa394ad79bc88d59b2ea78d0d437fd1723d3946c4b69aa28ffa86c73a47564c9c7497b09e527cfa7367a6185fa450ed06a80914590077e3bd1cb696d0c486b18fc23b5adfa4358658897137da05050c8ed917a13e26e01f2989434027845e896dd6590fda8dbd457a7b226e31f876e2328a3467d9f1c5d606605dc01a60b3832c8886cca67e1f0289b2881a58142631c257a69c2788786016168ea4bb12e272b4950ea349a631a57591a082b20528faae1a4ae69d90b78c002d698e8024c09d32193f69bb28e292788d409c8a760000bf66548d8155599d86105de473fa74800018dab3d15a0bbaa0e0b012ef102106026aa209414bac3ab4086385de16bf533c0c39f717ac55181a334425050002cde616a2d2a4980000000c180001510000000097000000000cd21c59492035000044b9bd6303c0004bd4b28204882a2a74735000008f24c139a9c840944752a4867e8d1848d66ee0001c6a000000072e800059e935e000073a72ba55f2b08b06000000054ca94c3614844837ccc203a8f5e3a88644768800077761fe7292cf637d2547298af3a2021a1452a27f800000004d2000041e62c0795aa4652b24e54a9608c6469d0630a430e8c72f4c38792068a48def3511d2428b1bea54fa3800a0e4fc2b5d752370913c00000000000000957a2ba4c6800001d87680000a72000272c2160b0a8fc9b5382dc000b7c800034780dc16a982662123ae32e1fd6abb08e21cd83c20000c6da2a84bb5815b6a421aeb26041b044f50eb31bc58a65800f0a8750ea426a8000b26800035a4bf28bc8000716980ea5010467d78f320fe9ce74c38be63c8999eb9214180001fba113000000025aeb94515100000001a11c7c1a524a231300009c7137191f80006e64d3e0f1800002ac0001f90b447ee000000000003ab4000862800059c8972031996a23b82fa5fe80005898c2078b8e1c00015aaa5211ca82e171438a2c001e884e24e626883e4d15452457942f3a4bd316998a91410e81ac158a557a01769c828275e00009e9997a33296e400012332db802800000000002e180002dce00000a300000006ce000068b9fa70000b4c8f71aee5fb80007df94e268b0b1256b42fd9e618b68f5922622600009950fe260e0000a809e8d0e4c000a5a1dc80002d304090000b10157d593065f56a2ae05
  | 36 => 0x69629f1695a9548a31f05694abd61b9189b76e2717486a2f09f696e50429528b0c0abe1be8d5561c1fccbba0238228cb043392c6c93c170000003d80229b1a00005eca752ede0001aac5b1c00000005be8389338201870856dc0009719ebeb460fd41d2a6c258b926f6e20000bd423380fe2d100001bb28c32f14b83a3fc76dc23a0002d368b1c0000002aef46b518c0000eeca73e58495f92ee08690f258d608379b439679252986622a40988810493a1fbb705296c1b493585a79d4f1f512511bd870db331d2e8d102dabaa9c325cb97e44ee9a62a112a100568d802361ddb7442b2089de1fc54a841e90dc476000000000017860000e379c0966c6ee820e8daa1569b880000fb81287301c04a219996bbfd430898ac9400000007fe80008e6281277100000000ee605b577e0001362bb5909e5925892933198e66025397910000613ab669f8a90a00000002d400001e60000416db090f72f4456a62340d000f02a646ce46dc00069e52f702d0fbb79f011754b2c908ad9ebd0f38d987f299392b7a7900ff8b07b621544138061425a1f3604808262c15cee0d544ff2cd8baa728aaea2812a748f6a48bb6e8436bbd40009bddda5a9b00005d39c1c40c2e7200020cb3198bf500000000000cbe0000b322b000ba459472660111aeba3d31f7018cdaa371b5a2bf275417a2354bb91dbeadc01ba5982b0e2862586108187e774847e0122b2218f21ac7e60000a2d9ae62568000000119c930d293ad2a93400000009ee000015b011c0001bd1b55865e374800044e08e084e022c4e2d17686d238c2c461140002afcaf29e022f598ca5066d0a9d9800000000000ab656646a80000002d94000181a00024e0009072276a884c5019708b84ab16000000000028e82cb18be35a2742027e3ac00018460001b2d0000761a886358b6b21188acd85807d031e6fe8e2267590708a8ad8a48e96baa30160e07ad1fcb8bad5c75a97902ac1498acb227c4c5c11e35c1f3055704b60e1928023b15a6a24c15c490adf568de70e000000096902787a8c7a08bd1e4795053577b54000000261e61a19562df08daac100001119898a758d2b9ed415e0001eb4607533c2a38000835c5681732c7641a8404308a13237189183924a360000a0b02a93e20cfa4460001a385f24dde3409d446e9036a58280000001dd600022cc00022a87d08d7891cac3eade00006d31a8c35b110eaf300000000000a1b914e6dbca3c020a1cea799a909780fc6a12000008787c800000b00000f9625783060ae40000001fac000198243a82c47a240007249e4d385461c8db879a3da09ee57aad9a689152474c000026490565fb6e4248c9135627809800000008b19413000000000000001511ba001a40007ec000000013740000b3a0001e8e0001dd4694699834a11462d49f6917706b21249
  | 37 => 0x80bc0000f9259718b700002105b7d82a00000009859f685c9a5be3a6d01f78221531bd27f613052ca49f68bd0000e4d79a4d161d31db551f946f81d0f28ba7a0a5105865c81700003c0135b8df19fc453d0bc634a40ebaf00d05745d96b97ae842bc000000008d62b7dc9e77c24b640f2c54825e756bc5a97425f0002127a16c00cab6e00020f215156784f78c2f7730da24579d2091281e81c38fe4a4e957268f0e245de8000000000000018de1ec800000000003b100000000000000000003021a45a40bb0000139066b993543e80009360000000000000008d042f9d98666e9b712d00000c598ea0000000bcb843871d23b261b93099c1285c4d080008e2881a000265824c8066279ac74940ac4a39687966dd1972bb501922c88f746c3abdc2e880000000e309834000372926605a800030c4bfc00005ca000285e85e400005f4e8e3990dcc82f68307916038b0d10aa07556d2a28544f52c124a91489aea5128791749c90a230fa617ca45c07d82979ec8f1a20cad46b9d0f9a16080008544f1000014e4000194c000000000020fc0001eed000093ea4d9cdd0001cc692f0b6c031c99a5b050fca3e19d55ae4000000151401d0000000285652aedf40001c7604b9812000000064f000030cd7cf5f8af6487a8000973d2dd45dd738834a87d48e1b346eb8894596e044b201bd2111556a9748000bc8a94a93680000e5084a2fa159c4079db27ab2c68059c00000018fc0002c3637b42d56c600003d1ad7da2912a9207158804dab3096a92e20040d5d8892c482bf9c10ac8e8b8930818ab63972c63b65efb6d1bc2699886871e172a5710626bc2d4426004b849cc0a8c1fb093ab13c00000012f00001fce00020f01fd02a79ef18a9150ae807bf8cba58927b496e9a6010f0772574d5d830216363420a789490cdcb148d1a34129929f10f86a788324b0e126034d20d8028862e03605f829f96fe5c46289bd62f57a721902b642286a3b2942390243c24693f2bd51d1909e6eeb66f19ac3ee113a94d90842280c128cc01352efa74c00998b87110a1a6156e30ad01a367a18f0656bac220b1a69021922a09564bba41987a8950c7ac74f50c05c10f908d817322c30534629519825e0922ab09d42b948000b24a4387bbe460592800056e1f507d70000aa7425a836a716000128631180005c40c5c7ea8b9000005ba0c326304ea089216ae738964400000000003aac000a35000096c180c79d000050502ba17d1cea00008167b2ace83d9a13000000001171be2116800000000007cb81587a302ab4cb61021a0a43023f21e46f3424a000292000013540d18a5c0708000285852c0000000000000026c2a5453d9bd304c50a092a1fbc0000b2624b81389ac28330001ce60b052c407000004c449703ad8af5aa728b4364af0000ba8cc5668dc0bbd0c96
  | 38 => 0x54d8d7394ba6a844b23166b289742942e9a2badeb05328c1113392920002d242e38000588a49889e99a548f25141362256826c50f1ddaa1247d92247a84e3ca5196a867ba7ee67c00000cf00910cc9273738acc887da3087871c2708acc1e91116a076d05bfaaf159631a54ce15d1ab24f107ea7560f025c609e0686891e80b11949e19d746fd8cf69822e967d8a75c828d54c9becf806d287ee9f51acc6ac29244c9a9d8a860aad380c2f008aa522a73a880385965e6e960425638134851a23249d90346d50000b850fbc6b914c4a6a80005729e9c955125962c6d7457bc68e78f6b3e5a1020a1ce16ae2b0436300019e3000000000020fd3c382d23b6946d422a06622b99e2a4e22f62bb19f2a4227605d446c99f59cec5b5808e00001127d913189d003b66f11cd00001dde0000412191a56b5c4970e603ebb1687007e0000fde00015150001170a7c8000000145f954e276bce1d9e897e4ea0000000b9e90c25a7000090d85b83589882463dab89e6852219c2ce0169a60e94c4000764cc28790de88000191d2530248ba400006e68a9c9808000057e8fa2171f5287498d83a20000a6b18e91b820fe0d7eda282e99c991c17600002780200a5ea000288e00000006a28000000000085f18f47a95e3f00027764e1a2700bd0ebf2e282755634000808171a345019505928cabc80f5a879929715a815219f131c8481eccb9f00008baedca5c2d9c2687a2aa8192f3da02a1a80001f2c48211ce86e1e265b21793a380cf060c800000008142d90000000000087c80000364000a6bae8b00001211a810187dd0000a6d400000000009c90000093030a6b5800046c800032daece5938000a67abea258a32e591a13a97e63e60000000a46816e42886cd00012483269000000000027864e73e8a0a0b771a98bb311828fea2d6480000002da684bbe80581928c303565f861ae9ea878c903851314f52af2ae600000004ff400000000001880000000000000000001f680007a792670002eae3084e1fa7900000940000aa20000a2693805911d39886a9760a3c0000002a9836424d0000187cbd6523f075c7fc5a300001a980000001fe50001ca0a0e800006b0000000000000000000000956299800007e2a4c000122c0001cc28420d380001c8ca169ac80002a668da0000000000031f506000019b539ca8507a289b46191e1e42e80003a2aaf34c88d5051f00004ff2b3c51ea3741ad8b702b6c0009f6c0000000000792c6ac3db84bd2ea18934ea8ad2000051800000003b8a006bb2400062f06a838100005336de750fc1febc201965302888359085eb98c0002288c98b970000000199c0001af900029d28d3000000021587ad57af5f29f10302d25a872827667486984e3031a82ac0002eb00006aa87128272ea6ab58000a5780002dd26262b3e9c673e
  | 39 => 0xf53eeb2980007529a80000000064ddf82892a59843d11f0a6e57d838196e2a0692856240c6e8858e560bb2eec6ba87d659211b94509a7e926801a00316287a08759672acd041383280218000000000058e1888000137c00000000000c9989e40005d103006b0102658482f82e712aaa70060c35d13100002532b91c00010c9c3800015500001ed49388e449a193da4cb1c24000000000000000000fd538a8000b794000000000061023e41c90000aba00000000000000000000000000000a94795cca2000218e2581d1128e8000512dda60020000615a3f402a0fcba28861e722a55b6c168942990f763e56178000000065216bb5d694a60002c606a9a5f63c511488e21a868818c7473ad2208a0c0000000307000014a6060000b781454ae980002169f96b53a2cd6e980000dca4ee61d65c41f0cc970fc800006900008598000437ac5e61e806aaf0a07e00000003989e2a00013e75ef00000001141bd1a64628091c619080003ae85115cd25a667e40001599e37a9b88ea52729ca15397d60001d8000011185a58ece8a942d470f814ebb0910a35e855033a06aa65b91b61f49de236901da4f947f68c7419e51a854a600dcd80b75157166873086f0528b048d760001cd2703130d19d1f4f0000c34168ea862150ecb00000000002e50876974f94188ce8239f7ab6a22221021d08590a656bae0be43c78d589bf08f47438c2c035a33262b13ca68c251209dcf406b514f992125817d5800000008fe9969d137cf22eca002722909800038e6e4e0000000566cb1001491f8bbb8df14d4a5569315c3c2c78000196a2bc3d7055e8500f790b71370b0ed3054c91cc85ecde7776221cf8371fea3501880414a572997000014f957b2b405240000000424208d9fb0000000035a632c145a0309da3aa26f50ba0dfe51880003ab8000307210c22ea84694d6ced0000b0d0002618a7d9236767604e49f20e690b000053982e9521a7a8000000080ea538735d50a6318fec45a1c961e3161800000000002be43faa5faa9f28ce5c25b6ba8a0c7c0b0acd2429219a7400a40ac089f60e6e21c3a992685e444ec898258a2d52c1aaca09de7dcd90457b823246a00006c707c6699230613ea0c00da2f523db2680b1f0b1c56748180aa23150e3024135fca289bfe2e756d0e1801a20cfacd1ac45f01adc17c2e4dbcd170656fd2b60f6945c291898656d5ef7b6909ce20a2cf000000008278000048ecee00008c698f10fe32b9f5b6350b18553d11e1e20ad41370e9ab220de450d40008fc20b333e8f704db00e6aac2d1e3fba55d6428702833ab582aa4fd734d4b4aaf01f4e266053d5c3252729c40a77b680007d4d5cc842dcb295ba5d94fc0bd068c83703be800000013780000aab0c080000c1507800000000001b2a9eb29068b754fc9df119abb017a8000000
  | 40 => 0x39f80001a48bc4a8b03e85f80a740000000b7b5c6c000150416c0000bb408b20000c4e00000d20002e3881ba7701ec090fb22ab86329a0c324a80008a866f80002c10000171ead09a5c967c1815c9edb04791fa6688026a7718000b8c8da84458c028a78b147ac4000b4d048eaeb89b6000000061bc00030d9ebf7b70342670222a00000004324000000233a00004a600025000d397aa5e7082c00024ae14805ae98a000064e1ec6459e57d74f2302595a2e25ff654207c21cd68a9b762f1800005becfc4a32a4a218241858c043e23c148cae68000651977b0000ec669f107b0000000000036c00001bc315271927d2b7ebb12a9287c1d8e7179dc050b15e600009ac00018ba14793a0a86a79e277116bb779b97390890800000004beaba2000021c63aca2e00003540cace3b0000a544299d340002c26920aef0a340000986800067799419c2a036055c8e634d82694f70fac663014606a9c0a2f220cd39f050a3c8175600008b70000dfc00026a00000000062278c5ad948f45805ee59a214c524cd96000130857ea84c6a491bf9440c89000000037d8bc07e96a1e80409503adc5f65d7eb149248000000000000000000001ef1000000041f41145b315de00000000002a141c85ff237c94e8a255f459840d2c453119e737d10673f2d4289cdefc8d09ee642d94dc6afe31830e64e45b78c2e4c598168c40b8289f5ac11044000000000079429dc554a54a4dfc0009032b8b249a24000016fcadb16d5000106e12e9abe00013566ba00000000ff8a2e800000000001d500000000000018806e44cd860b5e8000502951e05a400000026dc000133a0000000799013c97880000001bd470f691e0000ad5a8f06666cc10c68e093285ec800067992dc0000af2520000053e00000000fb40001345b7080009e500006c4917c5b11ad097994ea5058f8ca089a8b3d11e941572cdc8038624a3d218400004666b1ca0c66daeb4bb2aa2014728f231c95823630d7e05e84527b16712767cc8c7d1def6046973a1d340de6a39837490e07c38cc96e01f054c12c06f843e5aa42c5da6868208a60000e261e19a263ee80009e700c594e80005f300005da83a20002014682a78a00013d73fea3c2b7f99e4794d03a7e78d3019019e001081b49d89f6d00022c20001b9e7fc125000019f72b392ff76805c616528ac0e72d82361c53c3e90c421b42c640000b2099b90ca4fac8f3b92cc17a2ae5cd0001b90b389ddca91172999e184c5020000000000000000000440440000122d00000000a858b065a04ac0001bbd9070000a9e80002a1c000000085200012a724f01729e89a94099875704093508ca6e765dd8000415e84abc3961e0de8000a272700416abc60002298781800000013a40001a0cb390fe03e79320636c00000019e822a2dda3672852170908e5d
  | 41 => 0x285a5c950298b26c673d519376dac9ea489bb9a2c538200000000000aac0002b0086e84c400000009ba04567550258000047c0000a9a4ebaaf80002896000267a40409c953d0000000175d350c0001959b1f7be869a7aaedd60fd0000000126203d172b6bd174c9a69fec635990c7bb85bc1f780000001ce4485de843cc1641b6e000088280000001bc70002efe2b0dd0ab3c9b3b46c0d485fd66e4000000053fa71e158128e1221b10287a1ee0455d21000000000019440000000bb84c8e0001da1a6ed1c82f60000a7e1e67000070a000000019fade45dc4000504a8b314690134fd2cf14306a8a661a23ead397b650916fa65e09be0000000000000000000000000000a0d800000000003e200001949d6cba48000b6ca0bfa3c43527571b210000000000000000000000001e280000000000000000000000000000204132b4588eb27be18f82b95b507c1cb9a4614369a9094a96b8096600023920001b756f2596620f28b59b314faaf6a29fac78cf29301b7e6c80834af7837c57d80000000000000147688e0000221800083186b800012c5b1587c497b0000ae580000001f2542a000000029106f800001e9c00077f000042c127123a03800000f8200016342b699199219d560b24070bae81cc3ff06afbb643b479047ae9a9a552738d22e41f282600000e70000ff002ed18e3cba21ea781b56ac4165846e9b4401c81b80889b2c8d70260615178ca602a6279d595869694943a19b8a7e140aeb6195ecbc321de02e01330a6900a0e2d2349ef9d5e416055713c0988967963e156479489ae4084cc9dfe494c4d499fae82a3f97660545a7863d6a245f098a47b5e9df52e11e012f9574841a6b80002ee7101a504ae38e0a29390933a9c9fa51016eea5587e26215afe91682300001b64000074636191a3000172d937a2e98048b5e00000007d0699a7fd1fe401020870298e000001ed9627000034a40001c400006eaabee958c12200025ac18fa98c9532476098920e70080000001cda95f18e466cc64b3f31de0ba50aaf85dd38eb5980008ef00000001579a2a15403ee5828157ee064e100000000000baa1f9a4dddd702da218232211ec2758b4eb4a1dbab881f04b636a302fb826458823ec1ee046c64b1fdc3010906a7314b72142dd0134a2fab4b9b7f0249fb9b55186a8072f5e3ab0acc000000091e2a7ea8f800000019f4000000097281dc07480004a5400061785b400000008dc80000001d4c0002ade2560000322a1806712294637000034f40003a403ec81ee7fb8881c8232080000001e9a283a5465cf05789641cb04871e4e22e12286aeaba07b6000046b27c67b6e2b805d800000005487f9a66459fad5a22d94eca05800056194331da60e42962d32576a0c46002ae7025800049d0000296929e0002c980bb8cfe0001b986ecc0
  | 42 => 0x8e57951a06a39da7556891c2b6fa02e0001590b45133500004605470c9e02797507e89b16807807a2de034a440232a5068000532c00000005e26398abfb8228b213b960c631107500028986668f7e3a7937b00004800002ae94904e7427f1e5aa5a800000009ba9c42596b88a66670899f161b69c3748ac8cba26a702e9ab5271e8c3806689d43d308c006421d8bcbebb7606e744800a828bd98c5613f19b01499caa9fc1cbe2fb5da82278dda1051d72585827f4b85d0c324a350bcb50319cd28383140d9a79c2214000107e4b40000647270b3ded6b2000041c66a27c085502682119ab68400eb02552a4e8849ac98d68e3429aa752aca8000b7aec7258e81ef0c49b559bd11046f2942f78cdce88a1dc524dcd75b4ec8a985ac2253b4599905fac67a9069415a8e0a26038d70a3e52b3a18dadbc75888209800ac47b4e7cc73c00000634df013417922b18c1a05240f803da526288127e00000001d7219249fc0008a01ce070c1c9a000018b754800099c2518000147b5c4ea0682561c2b521a1d6b49deeb83debc8e6a7ae0000000419004c5d79f5f21fde3b05c2f4e61d9c3a83e8c5e0001bb0918901487705764d293666566eb0bb71953000084200013a2b47000000020af3252a5eb6603ae2eb9d3a7c91881aaa103e7ff2b0673beddf8b3876c3381f358cd9f2227916e67098bdc3f022d015927b08a9862c59d850b68392b81a417bd6ab93e68288faf99aa7467ed14c824b22c48cb00fe00b16c66176054000000029bab87899a026b2399ec00000000a7c8b07590a9094680e44c300008f819d94aba5d83a124685e29444b4880ca65294525b6a9da298045032c80001c68000b02ae8e136936483d939c62595a4166149aa28d97093d93d254617ec2966dee0f406129bc9bfc6fc8f3e488907460feaa04a51131993813eabb61aa6eec000503dd3f00f1509afa1f21b2f264816b00000d7a324b7e53fe0f9a48e2c225dc91b99cd7598782631db142df88f894700007bb2dc42cbacf87f42802a8219246541155bc2529a49593046f2c00007a8f7839c058e000061a08fca2a98f96809516d6084582809512464000000000000000001a8852d9d5a99294383190000000277e34f00000a52afa82180006c3ce027b3963d4b492780af2082b8400005dcaf3c7dbe293a6daa1c59acaa623d8000417a1273839a4e4c04aa447a5d149b59a7abcb259222ad35aa6e20ad00000000ce800051baf301e3a37e0002bec00015f000019c748c406b12590b28a2c6a211506103ea0d5b8c10dd4388dbd9000147db9b089c18580007850000000000035f5ec08e852fb339800024401be0001b35b8b1bbe7f6a15e0000c05a03800033e12a4ba340b24bc9af800012b200017cb858c000b9880004b96e60826593400000000000000000000010999050
  | 43 => 0x158831053c92890000e480001dda0002bb8049400091f2c7000019605e09ffb9ad9d9b45b6ee93270000b832d7e09ea5e4a398e6100000005811396071c159bc7aad47c0dcb860518537d607e80000e257e1ed800bbde6c6cf8000927019157f9b8c5a9071d5f8c00071c9bbf45b1dc20970d418e3a29d5481b6c6a127826c183625b357be4e992c026e2820165a14a20d9296b890000222800033207c26d216aba8597742870f6035c5002690239c1acd1f26e9ee1e6800b1a4c797d168619feb0c8b9655c182218d2f3132d2126b018e7aa445a4285397f03fac0009c9a48ab4300000ac800058c890202dc0007d2d78e0001f5100018e223c8e520002ecf524099400002f11cd0586b2a8d221758cea000000060f00000000000000022db8f83a911c80c800000008a5dbb600000009560d376bdc000899000095d80007109c582101c56a941bce9715d2c167022e8c002f3158565a28c26b26c9940e6809e0e8340000b58ae5d563000000019cca6e8d120a314ae4152e6e000259c482a1be25204c218a800024598598ac053612bac0e6dea0c583ec60e69225801e11b810002672b2b17697c58e948811f177dda62e5f2288770366c4adf2cb031280bd8822272b104fe85c34a7a1b322aeb7f11d3281818281a85581501b6683a20ec6c001aea072a2e4d180904f2125251d0e4656513365179ba246589528cc536d00021d0bc168a000014598a645c40000d84485208fac4955a000117846f80009f79ea2000252052929a4077820840ecc2a66483f6899616a63ca3a063e8c3c36f992660e593127c972420e03d9b10e6ca3c11f6e4815d7c1938000618845800019ef0001ee80001d6e66fa62a0002cb252e915c021400000002467e4036014e291c00000309f0a0b679c8e6628480008e107800610d8eb9a9f806426d9e77a893d1ef223000012ac8afc0f3271add20be5ae5337a29c82c959e6ad0390af62a11bbf62287c82e612b8070cbca28fd46464b48841bb8b5e25a20002e5bafe03d79870fd65f98e2c7000000ad915126d7000019e1b6801115c61b863a60ff2b884030a865cfe76a3fb499c000000000002e00028d7c599142ebc1aec89a6000003880008fbaf02000000096a648c3b500008920000b4b1b2482d52309091802000042c886428e69cd70f9be6a8e0000d2f00016cf3841a1b43215be569d26e3cf2bfc38da3228bd67786c09e42835116e000256569c5ca803d4f99960a7a1430d5647630318988207954995ce90a85ea6d7a37a52208902b9d8c026900008aa5babb5280001b687ce00006e84ba0e6800009a0578857a4251e6215ace0730fc39254d000059c0000000042e0000e2e093924c5ed00005e2131454e8b241df000018a04aa2a6c00089e2d76132c0007448443000071c84d20bc0002b563e7205a515a
  | 44 => 0x2e4796299415189a2355c4c8b8701b647a02cbb808d2aa7f97ab223c68c8549bde637de6ab449f88309235208599ba4b914204a81dacbcd96ea19a69a8bc6800089d4f5222b216e6add1207d268428f1252d6ad4ec7b9006139ccc1d47fb83be760a2ca44682ac0400bdf5bb00ff1cf0d325b0de5122f856e43b1940aee9c5c3848f1852b52df49128f677d2494000000000027e0b7522e6213800047f9f27944c0000001698219813955ddad10142085ae42b9348bd9082b905a44b3a1f47060000bd2000042691400001c40000112a1a20893b71aa72bcac00021895dc40ca73500008f1095a8067e387748d1800044700000002e0082489dd485824457f21620c51e128ba0f0c8cf823453c592fba1deba00004346ae4c0c7c50fdc9b787c91041a095660f62746000026300007db14505bc8000135d584a3216bc469514467856e99d393d006a1de87dc8b5c86c253d85401c4b59142db1080004b1d7988c040000000fa03110000ae54e923f285a0ac226fa2fb0000000000072601e257800009de9dec000000000014d6558809ab96a76c0000000000069e00018c864880000002eb60ab96622829a390000cd60000286829c00087204f20000cc04df97b83cd9bfe3310ec000027e4439a5cc0002afe0002124325658d8119cdc410887e00021ad00029a0a6993b400004a800000000001ef3ba880000afa2460002b978384000a1fd89598e8eea8f01c802714d5c57a2de69ffa89eb0327397971d9297d0228000000047e8e788031ce59178a9f0db84635352320a5625089c514046a09f6673580004a72d3e16c89383dc8f97000162d7e480000000cce69a9cce6bb1d8a4b58bfa2ab812f2e02b8c000107a97c6bc845aaa0e5ad0d3a5fe29709c1ade3000260c19d8a2400019940000000b1e80005f180005d9c1879e39f185ca211c0e1000076f02df5dbc000b3f8e8c77e00005f3400012699a00291c8e068ae4c6c4c0000000e383d282cc3e11754a0783d43d9287a000058f6cf4cb09ab00003bc000031b2dc05b6c51642e0d89a248ba4018023e1c79fc600013e0896138876c08fab170b01a4a0000b0f4afab290bb67f025798ea0efc4fee4b29949d91639577c272842400891a289a988684da9f44a1126b61112bc000210a902ad4051802fe385098e64a96c982582a62dd98f6285202a015a6d96794b38682de9946e2e5697402b443d90e064d9b231d68a4488e9a9c00000000000118ad8820400026ae079a68a0001fe840b9bd800007058801d8400010ae4209796bd705120f2ae280f91c7e069cdac15597d43ad0000bbde0300001b802432f62b11971621c80006c8af2a051c000a2b8db84c1c9ec41302d02788000605c9644b0a0dd5cf622e7b4800000024aa8d9adea47040005ab1f0a6122b8f4af8c2d7b954e02f29402
  | 45 => 0x250da7e80651b40abe487c73d039eb9292ab18c5b70436870603bd6c288f28bc44bc000000000000005da2e48728701e642167858a6b686b16c2a2a4672cbfb000034c000161a00011c300000003bb80008f4850e000027494d10881bc1f0631d860680d000000010dc3950a6f1395674ae2498a88325337ce98e71f32122bb89417b9998c562755337ab600890b80006e580c20001fa09c9d56820280001391d3e57e0bd4b1399c194562d866fe9b42be1b8e6c7a682674cfb19b02b747c98000b5104980000da6401c0006aa65ee0a9227e04c12823721e381365fde2be4e3a26c80eca3690960002bf67a91b65935aa5a1fd4000b85ae54a7a00002f30000418a2cb0001597ac613d50e5522a2761f127e9000019b88bc00029fc00000005cc21e099d2bfe3f980002a280001f821cb00013ea3d519183d62e4618e9d464b800000002e49a8100006858000a9a00001128000ab3a1a0000253013d2ea4000009c000098473da87b452abe60001b5100020910000000000197e9b400004b99b0ca1f22d364b4848a572d84ab2ac447d11f08590eef385caaba20025bc5a39b722b363d05e026da00f8ee8a1c2c7f82a07641b0a71ab20a75a19923ba1862aaa1d9993f93f9d2602054112e615b21f00aea90e67ea000000016741caa5ea98e713000000021989c6eb262f3cdd68292cb64ed8000714176405983564730e0579a14aab8da5fc2c3abaa475a4b93a8536f6f31be45721e4fb4e2792b3acd881799c9c11927ca0002b5a70c58e352c96e747aef60b210aa0aa98e823c99a109da07047152e458c783b814fd431703d0591d62aacab4960d13a9df2810287262bd4664761c085f1cffe10a8308aa901932ba53684a99ffdab1869c0e6800000016d869dc0000b59b4e2a0273e6b79d48b3092fc2ae9f1a15f1e8f6b08fae0b620894be27962372e951d8840a05893c052786ec4d75b862239e0c3bd9f46817937670788886cd850260724a08a2246625b23df80a00007eb8000ba5c000b18a0b08f51c489a917dc000087628e2b6a66c69e5a3c1ef0913000066dc900910a636a1d1ad813989460000293900aba8ae36ba44864dec32a020011aa2d4000180a00000000000ae241b021d00000005d2217625a8cd4820625791d06547d824a44768b131e71d689eea57f0000edca1e28ee0a629b032a80a185f8000b3104cc07c8a6ca7e9068a7b894ea9609d2209608aa3191c54f1a386a70957c567d42a81b10d022ed8ee8ab51089cb50d8a2c04c003f48a4b2d157a3a76cbe64cd9170000b1b613ca8118c048a000009503ec00000022424f919842cd0d4c00012588c4625e4e2a9e7677e01a49199545850d2d15ca36c32117363a007d0406997484a800015f90760002cc631aad929651ed68e793004e3458c95aa3489bda9e9203940c587
  | 46 => 0x129000048f9423a1611f56d4800039b1ae20002b7a000000000025d646d195ea1500000000f7a2ada400000000057d000000028834dc88a9414510c64780002259d7a9a480009edc7fa21c12a8bb951d562ca4ca7eda1558ab1d4e4c18000a3f218c3471cac043934c250a76e0001bbc4f61ce1bd6836432740000000000314a574000127a7b12de10001de62e814b42529d235d2a9d08dc066c61096b1000000056d9a9e14e9e0050404a02088000a3aaa6a0000000053054768f80004c743872af69889af1e106e4a51e481c5a8b6dae0a1de8de0543886a1ba8df8071a3f6bc040000000000000121e5d008c2a54a2e069b0000ad7191b69b9c70170ce5b3ea84625360000799a9b26ed093408da07064498ae02015bcba7c0004bf4fce15a5720081a81017e932e0adadec06612b463c00000000000056e7d8962097a0c9866264512f47ae2ec60000aa80001e9fa54076aa801f34038000080fa22f1801136b421bc671bac24af3d81e5e90bf97f806ae57087520c1032e1d799b27a416f6367995c0002a80a5f9eb397a1cc400002844441c64543259303f2c1e3ce831c6d618a735b9c165002e2a8158abb9af97f6981837e1210a4c460c0000eea7d24adc00069d0000000299600e9b423f48000ac901d000007445ffa27b0680a3e053e0ae4a42290640083e0000000b1b80003ae0000408800000000008c3ab687c2ed3a5340be271820de60f98e16ff51844011e4681e855a1d3a3beb3691d078d6b9e49c00008aac0000001e042ffa190525800052f2c96ace2104000000073c800075f80000002de25e11a85722243475d9a83af513f81d2e2b5474a5371791c62a9da599019244e85a10ce56bed523e2a2ed9630ddc86b8f6a1bf1f3f6bfed8c8c495ba42de72e4e481e067221e27f21fbe519173b0000592650edc86a1df40000172200018f30000000022220eb7d800044d13133c21af5a71623682213448309470154aaf15211a5d0138ed88ad25dd000156e0cd8db63711e859019204696c00001720a6966ce9c26780002bbc000000000000000001fc00007f891320002b541b52a5669791a6b2e8ae64f380009fe8000b1980001810f2a994171c58209289f2000000000002348000af80f16033abce00022028c9415d54940009a394a2260975c000125c74b4000005ab1a354d1922a59bd09089ee109022b282ecd566b86d9600000c98b91ea09b60126000038a00022af5fc80000002af700004fe74dac5037b94c66fb9e7a5070be08de005e2aaa7a4b69a2c3a608bf44ab46507adce5ca8d915a0002263698c00093e00009430ef2320000017397791829ec15ec568268127e6000126c39d93bc843897e7ba848688600003051a4a29283d2af4a55c83282d98bfa58e5f69c2018ca562943ad8b4f59aa75369aa596c8d7
  | 47 => 0x787330000000252f000270cbcc92f60001df630caa328580f346268000000100800024ba4c3c0005e7800062880008c9ac6a0001be6080ae1143b800050c8000530aac44451021427216497940000446a94a210000444817735096101ad6bb212322817f09b6e31e018eafd03a80f88f1242b013babda2dca4b999da6fd7a03efa04a26f28c400009247408b6a5af8000000000000002c800000000001af24efa25a0d6000059404c67bfd48e6db43b06bf548200023aa0000000264289b22114de0282440633800049a8000227e5a02f48000617000094f17c45da059f6919910aa412d48116694aa0942824d9a47ac29a456c20b560000000bd0a1d655601638bde5f06fa2634ba6524ea4f12de91e9fb267a9ee46806f297cc80008354e6e00026b440806bcb3bdf6b4ee0000000000000025fe00005081208c9000016923d200000002f260001072594982e0002df0bc4039f00016a6a6194ee6d8257b1dc29be38f9afa03c99301706bfabb810442379b030000366417025e975c0000c824900ae06ca4059e8b220a19632828627ab9dd03f4168a0001f6a7f8d8727b2032f4771b46692674aacc9f7082d29787901be37a5878a77396e012f23ce1450000af422690dd8d24414e3b80000db05134a9e6e0ae9c00018c968896d794b1303ae50000737ae70aeb1c1214180da7ea0b0236b97629ed96541061a4c2d8a22c9591a93708c4fd64a10e2b899a9749d4ec845e45e059b487a6a55fc40a4a2a79048000a021b675cf9a698d3879e3f60ff631819a42b2000000023cc9fc90cc16205d8ab6215c3a7c1eeb0f0714b54000000019d010c29c4797a8d20000000795690c0002032000284e0002edf0000dbc12e4f244dd4e4f2fc1448000000000000000caa17abb600000000fb2659cd4e78287dc0909f1f8ca0bb44d0dbb5000125b50946cb30383a49982be20c88351b46810100022fc0a40a700002ce600017fc0002b723e6098003b80149ce80006d8a9624284d0e6bf1e4c8a5a7584ac193b57c97f484b9e24b7a440e00000005b5010cac7009961c60d62822274a8306f5242d7ada0c8b60a0b80008120a420002ada0000ec200012ecaed041a74e000000020f4454ea26b682bf03cb1e710002f18bb980003954000b482e8c998a4960a819d4a180aa20ef072e08f23a45f411287a74760b9920be2faeadc8be1ced8f29abba439962905839850f00fa86194beadd97ff5bd0bc20ce2ed736298cc81420aa54f28c22a148c4bc0d29963dc9d059aa4d2000273c04a800043100006da4dd00b02a9e09b0740336137a9720000000130b00022845128000a88c03824800007e3186c40d983481d8000395d39e00000009081bda8f78000000157865f000000007be00017b01b7826e000000000011ee0000e4c000000000029f04fea8d600
  | 48 => 0x3b327aa867000073dc0e800013cc0000b480000d4a000090449cac4c000115612fcf8e0000000745920200000006c040
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x84b67418f210423abb0a7908214d5d053c8410acae429e42085547354b210421f3a6cb108210f5d365884108bce7b2c420845d73d9621042a639aa510821531cd5208410acae2a9042085c473484210423abacc810821359ce64084108eaea320420847576d5021042b2b96a8108218d99154084108eaea31842084757614c210429aba0a610821595c85308410acaeb310420856575948210423bbb2a410821551cd5208410b88e6a904208567765482104333bb2a41082159dd15208410e8ee6a9042085647354821043a239aa410821511cd52084109caed2104208565759082104332b2c8410821595d54208410ccacaa1042087255450821042f0382841082159dd73208410e8ca79904208565750c821043a229864108211ddd56008410968e8b0042084d473580210421fba2c3280210f1d161940108bee6b0ca00845c7358650042ab39e8328021599cb41940108eaec20ca00847775586400426a39ac320021391c96190010a6aea20c800847771d95400422f39eca20021175cf65100108dce5b28800846d72d94400423ab8aca20021179cc65100108bae6328800846e721944004236b90ca20021879516310010c3aa8b18800862e545884004316aa2c4200218d5526110010a6aea20880085b1701044004237396cb180211b5cb658c010a98e4a9c60086555398630042aaba8631802195d94318c0108eee3b2a600843e74194300421eba0ca180211b9c8650c0108dae4328600854c7254c3004272392c218021555d4310c010caaca188600845e73d96200422eb9ecb10021531cd5288010ccaa530c400866765086200423bb8eca900210f9d0650801087ae8328400845e73194200422eb98ca10021351cd6108010ccaca10840084d6739931004273394c9880211d5d464c40108eaedaa6200847776553100431b322a9880211d5d463c40108eaea316200847576946100423cbb4a308021749cf4184010bc4e5a0c200863765d91100423abacc8880212d9d264440109ace732220084e672991100431bb28c8880218d5d464440108ecedaa2200863464d51100423a3b2a8880218d1915444010caecbb1a200869464d8d100423abacc6880212d9d263440109ace731a20084e67298d100432bb28c688021a5d906344010d28c831a20086575418d100432aaa0c68802199d976244010d48c9b1220086c463d89100423abacc4880212d9d262440109ace731220084e6729891004333b28c488021a9d906244010d48c831220086c7631891004362318c48802199d506244010ccaa8312200863464941100432a31ca0880219918a5044010c76cbb22200863b65191100432db2ec68802196d946344010d30c831a200866b65d891004335b28c488021aa1906244010d60c9b0a20086d063d851004370316c2880211e9da5144010
  | 1 => 0x4304272392c3218211bdc96550c108d8e4b2a860846e721954304236b90caa1821531c95350c108eaea30a860865553185430423cba8c0a18211b9c86510c108dae4328860847671194430422f39cc929021175ce6494810c9ae431aa40864c63d89520422fb9ac2a9021171cd6154810caec630aa408654631855204237bb2a4290218b5915214810a98e6a90a40864d63548520430f324c629021875926314810c3cc8b18a40861d6458c520432a38ac6290218d5926114810caac7308a40845e73d97420422eb9ecba10211d5c565d08108bce632e840845d73197420430f2a2c7a10218755163d08108eaeb30e840863554987420422f398cb21021175cc6590810a98e6a9484084d473586420422fb9acaa1021171cd65508108bce632a840845d7319542042a639aa4a10211d5d46150810ccaa430a840847975181420422f398ca21021175cc651081087ce832e640843d7419732042a6392a7990211d5d661cc81087ce832c640843d74196320428eba0a719021535c8538c810a98e6a94640845f735953204237b92ca990211ddc5654c81087ce832a640843d74195320422f3b4a699021531c9534c810a98e6a92640847575185320432b298c2990219554c614c810ccca430a640866552185320421f3a0ca190210f5d0650c8108baeda98640845d7614c320428eba0a619021535c8530c8108daeda90640854e754c832042a63aa641902193d95320c810c9aca99064085c4714c8320422f39cc928821175ce64944108dce5324a20846d72992510432ab2cc7a082195d5263d0410caaa931e82086556558f4104332b2cc5a0821b198e62d0410d8ac731682086675498b4104332aa4c5a08219959562d0410d8cc6b16820845e73d96410422eb9ecb208211b9cb65904108dae5b2c820847776550410423bbaac020821351cd60104109c8e4b008208475751933104273390c9988211ddd954cc410c6cc8aa662085647254f310423abb0a5988214d5d052cc410aaae6296620843e74d96310421eba6cb188211b9cb658c4108dae5b2c620854c7254e31042a6392a618821555c5530c410b88e49886208475759903104273394c8188211d5d4640c4108eaedaa0620855573d50310431b322a818821555d6630c410aaaeb29862084777654c31042b2392a618821711c9530c410aaeeca9862086577654c31042abba2a618821d1dc9530c410aa8e4a9862087447254c31042a2392a618821355da430c410aaaeb21862086556590c31042aabaa861882195595430c410e2aa8a1862085d07050c310423abb0a4188214d5d0520c410aaae62906208557758c831043a32946418821555d4320c410e88a4190620847775580310425a3a2c018821391c9600c4108eaea32642084d673193210423bbb2a9908218d99154c84108eaea31e42
  | 2 => 0x82202218d9964110110e28a7208808872452904404431a2a4c3982219514e61cc110cc8a530e608863454587304432a29ac3982219914961cc11087ce9b2a608843d74d953044236b96ca982210fdd1654c110878e8b2a608846f72595304421f3aec8982210f9d4644c11087cedaa2608843c76d51304421f3b0a8982210f1d8544c110c3ec9a9a608861c64d4d304430fb20a69822187190534c1108dcebb12608862f54d8930443162a6c49822193d4f624c110c98a7b12608846e751893044317aa0c4982218b150624c110c9ea6312608864c5318930442373b6a4982211b1db524c110c5ec9a92608862c64d4930442373b0a4982218bd90524c110c58c8292608863754d85304431a2a6c2982219514f614c110ccea5b0a608866452d85304431baa0c2982218d150614c110caea630a6088654531853044333a90c29822199148614c110c68a930e4088654539872044332294c3902218d15161c8110ca8a6b0e408866452587204421fba2ca902210f1d165481108bee6b2a408845c73595204421f3b6a8902210f1db544811087cec2a2408843c76151204422f3b6a690221171db5348110c3ec9a9a408861c64d4d204422f3b0a690221171d85348110c3ec829a408861c6414d204431baa6c2902218d1536148110caea7b0a408865453d85204431baa0c2902218d1506148110caea630a4088654531852044333a90c290221991486148110e30a829e20887285414b10442ab39ca908221599ca5484110c6ac82a4208863676152104431abb0a908221c51535384110a6ce929c20885667294e104438baa0a708221c51505384110caec829c20886556414e10443922a6a508221d114f5284110a6ce929420885567394a1044393aa0a508221c91505284110e8ea629420887445314a1044333b20a5082219959052841108dee4b1ea80846c7258f540422fb9ac5aa021171cd62d50108bce7b0aa80845d73d855404237396c2aa02117dcd60550108b8e6b02a80843f76550540430eaa2c62a0218b5516215010c3cc8b18a80864e639885404326b1cc42a0218b9916215010c9cc6b10a80864d63588540432b31cc22a0219558e6115010cccc5308a808665629845404237394c9298211b5ca6494c108ece3324a60864f631895304236392c2a982199d886154c10cc8c430aa60843f74581530421e3a2c0a982117dd95314c10c3ac8a98a60854c7254c5304326a9ac429821875926314c10c5cc9310a60862d649885304317322c4298218b5916214c10c9cc6b10a60866471588530431ab24c2298219958a6114c108dce5b2e860846d72d97430423ab8acba18211b9c865d0c108dae432e86084767119743043172a2c5a18218b55162d0c108eaeb30e8608635549874304237390cb218211b5c86590c10a98e4a9c860847575986
  | 3 => 0xd25450510aace72a2828856672951414423b3b0a8a0a214d9d85450510c6cec2a2828871454d4d414423b3b4a6a0a214d9d25350510aace729a82885667294d414438baa0a6a0a21c51505350510e2ec829a828872454d4941443a229ea4a0a214d9d25250510aace729282887275414941443922a0a4a0a21d1d4c5250510e88a629282887276414941443a829ec0a0a21d814b6050510c68a83028288654531814144332290c0a0a21acd906050510ea0a6302828876052181414431a2a4c220a219514e6110510cb0a7306628846e75d893144317aa6c498a218b153624c510c9ea7b12628864c53d8931442373a8c498a218bd50624c510c58a8312628864f531893144326298c498a211b9db524c5108d8eda92628846e76149314431c2a6c098a218e150604c510cb6a63026288554754c4314438baa26218a21c5151310c510b88e49886288747524c431443a22926218a219a14a60c85108bcebb1a428861f54d8d214430e2a6c690a21179d46348510c3ea831a428861c5418d214422f3b6a690a21179d85348510c9ec7a92428864c63d492144327b18a490a219318c5248510c70a9b024288638541812144335a90c090a21c9d512108510e48a890842885c47348421443a3a9a4210a21d114d2108510c68a930e8088654539874044332294c3a02218d15161d0110ca8a6b0e808866452587404429b3ac83202218d9964190110e28a720c808872452906404422f39ecaa0221175cf65501108dae5b2a808845f73595404422e39acaa02211bdc965501108bcebb1a808861f54d8d404430e2a6c6a0221179d46350110c3ea831a808861c5418d404422f3b6a6a0221171db53501108bcec29a808845c7614d40442373aec4a02218bd536250110c58a9b12808864f53d89404432629ec4a02211b9d46250110c5ea8312808862c541894044327a98c4a02219314c62501108dceda92808846c76d494044327b1ea4a02219318f52501108dcec292808864f631494044326318a4a02218d1536150110caea7b0a808865453d854044333a96c2a02219914b6150110c6ea830a808863454185404432ba98c2a02219514c6150110ccea430a808866452185404430faa4c620221871526310110c3ea8b18808861c5458c404422fbb6a620221175db53101108beec298808845d7614c4044317aa4c4202218b1526210110c9ea7310808864c539884044317aa2c4202218b1516210110c9ea6b10808864c535884044237bb6a4202211b5db5210110c9cc7a90808864d63d484044237bb0a4202211b5d85210110c9cc6290808864d63148404431baa4c2202218d1526110110caea73088088654539844044333a94c2202219914a6110110c6ea8b08808863454584404432ba9ac2202219514d6110110ccea4b08808866452584404429b3ac
  | 4 => 0xcae2218a48852f7458052442963a2c02922153dcd6014910a98e6b00a48852f7444052442963a2202922153dcd1014910a98e6880a48845e73d97424422eb9ecba122117dcd65d09108b8e6b2e848845e73197424422eb98cba1221179d663d0910c3ea931e848861c5498f424422e3aac7a122187d5163d0910c38a8b1e848845f76d4f424422ebb6a7a122117dd853d09108baec29e848864e63d4b4244326b1ea5a12219398c52d0910c9ac6296848863754987424431a2a4c3a122195d4e61d0910ca8a730e8488667529874244332294c3a12218dd5161d0910c68a8b0e848865753587424432a29ac3a12219914961d09108bce7b2c848845d73d96424422fb9acb21221171cd65909108bce7b2a848845d73d95424422fb9acaa1221171cd65509108f6e0b2a848845e73d94424422eb9eca2122117dcd65109108b8e6b28848847675984424431a2a4c2212219514e6110910cc8a5308848863454584424432a29ac22122199149611091087ce9b2e648843d74d97324421fba2cb992210f1d165cc91087ce9b2c648843d74d96324421fba2cb192210f1d1658c91087ce9b2a648843d74d95324421fba2ca992210f1d1654c910a9ce5a9a648854e73d49324431baa6c2992218d153614c910caea7b0a648865453d853244333a96c2992219914b614c910c6ea830a648863454185324432ba98c2992219514c614c910ccea430a648866452185324421f3a6ca192210f5d3650c91087ee8b28648843c7459432442a6b90a619221535cc520c910a9cea990648854c754c8324432732a641922193195320c910e1ea8990648870c544c832442e238a64192211d9d6610c910c68a93086488654539843244332294c2192218d151610c910ca8a6b08648866452584324422f3acc7a0a2187d5263d0510c38a931e828845c7558f414430faa2c7a0a218715163d05108beeda9e828845d76d4f414422fbb0a7a0a21175d853d05108dceb316828862f5498b41443162a4c5a0a2193d4e62d0510c98a7316828846c7558b4144317aa2c5a0a218b15162d0510c9ea6b16828864c5358b4144237bb6a5a0a211b5db52d0510c9cc7a96828864d63d4b4144236bb0a5a0a219398c52d0510c9ac6296828863854983414431bba4cb20a218d9975490510aace72a4828856672952414432b32ea720a21c515353905108eaed29c82885367494e41442b3394a720a21959945390510e2ea829c82887145414e414433332ea520a21c91535290510e88a7a9482884757694a414429b3a4a520a21559ce5290510cccca29482887275414a41443922a0a520a21d1d4c5290510e88a6294828863454982414432a29cc120a219914a6090510cb0a7b02828866852d81414431daa0c0a0a219614c6050510cd0a4302828853675d91414431a32ec8a0a214d9
  | 5 => 0x851f74580534428e3a2c029a2153dc96014d10a98e4b00a68851f74440534428e3a22029a211b9cb65d0d108dae5b2e868847571d974344237b92cba1a211b1c965d0d108dce432e868846d72197434423b388cba1a211b9d662d0d10c5ea9316868862c5498b4344327a9cc5a1a219314e62d0d108d8eab16868862f5458b43443162a2c5a1a2193d4d62d0d10c98a6b16868863754987434431a2a4c3a1a2195d4e61d0d10ca8a730e868847475587434431baa2c3a1a218d15161d0d10ca8a6b0e868846e72d964344236b96cb21a211d5c76590d108dee4b2c868846c725964344237396caa1a211b5cb6550d108dee4b2a868846c72595434423bb8acaa1a211edc16550d108dce5b28868846d72d944344237b92ca21a211b1c96510d108eee2b28868847675984434431a2a4c221a219514e6110d108e8eab08868863454584434432a29ac221a21539ce54d4910a9ae72a6a48854f7355352442a639aa9a9221c95c454d4910e1ea9a9ea48870c54d4f52442973a4a7a92214b5d253d4910a5ee8a9ea48852c7454f5244387aa0a7a9221c315053d4910a9ce6326a48854d7319352442b2b88c9a9221595c763d4910c9ec731ea48846e76d0f5244236bb687a9221599c743d4910acae3a1ea48854e73d8752442a6b9ec3a92214b9d360d4910a5ae9b06a48854e73d8352442a6b9ec1a922187d526394910c38a931ca48861f5458e524430e2a2c729221879935394910c3ac9a9ca48861e6414e524430eb20a7292218b9935294910c5ac9a94a48864e63d4a5244326b1ea5292218d5c66494910c3cc931ca48861d6498e524430f322c729221875916394910c6cc8b0ca48865663586524421f3b6a8a92210f9d85454910c3ea9b1aa48861c54d8d524430faa0c6a92218715063549108bceda9aa48861f64d4d524430e326a6a9221179d85354910c3ec829aa48861c6414d524430fb26c6a9221871936354910c3ec831aa48861c6418d524431bb26c2a92218d1936154910caec7b0aa48865463d85524431c326c0a92211bdd95214910a5ee8a90a48852c7454852442a7b9aa429221531cd52149108bce7320a48845d7399052442973a4c4292214b5d26214910a9ce7310a48854d73988524431732ea829221c9dc754149108daed2a0a48854e7395052442a6b9ca8292211bdd95414910a9ee6aa0a48854c735505244317328a829221c95c45414910c9ccba98a48870f54d4c52443862a6a6292211b5da5314910a5ce9298a48852d7494c5244237bb2a6292214bdd15314910a58e8a98a48864e6514c5244387aa0a629221c31505314910a9ce7320a48854d7399052442b2b8cc829221595c46414910acee2b18a48864d6318c52442b2b88c6292211b9db43149108daeda18a48856671d0c52442b2b8e8629221599c44314910a
  | 6 => 0x1842f1380a410c21599d64208610acceaa10430856475cc821842b33a86410c21d194c3208610968e8b0043084d473580218426a39ac320421391c96190210c6aa8b088108656535843084272392c218421359ce64c42109cce5326210847776553108431b322a9884211bdc963d51108d8e4b1ea8884777158f544422fb9ac5aa221171cd62d5110a5ee4b1ea88852c7258f544429bb8ac7aa22147dcd62d5110a38e6b16a8885377158b544428fb9ac3aa221471cd61d5110a5ee4b0ea88852c72587544428f39ec1aa221475cf60d5110a5ce5b06a88852d72d83544430faa4c72a22187d516395110c5ea9314a88862f5458a544432731cc52a2219358e6295110c9cc6b14a88864d6358a544432b31ac32a221999896195110c3ec9b1aa88861f6418d5444317b26c4aa22193d8f6255110c98c7b12a88862f641895444327b18c4aa2219318c6255110caec7b0aa88865463d855444333b16c2aa2219918b6155110cb0c7b02a88866862d81544421fbb2a82a22147dcd5415110a38e6aa0a88852f725505444296392a82a221479ce6415110a3ae7320a88852e729905444296b94c82a221179cc60151108bae6300a88852e72d8c5444296b96c62a2214d5c76315110a6ae2318a88851e73d88544428eb9ec42a2214d5c76215110a6ae2310a88851e73d84544428eb9ec22a2214b9cb6115110a5ae5b08a88851f73580544428e39ac02a2214bdc96015110a58e4b00a88854e7295353442a6b94a9a9a2153dc954d4d10a98e4aa6a6887157115353442a7390c9a9a21535c864d4d10aaae2326a68855571d8b5344327b14c5a9a21539cb61d4d10a9ae5b0ea68851e74d83534428eba6c1a9a21539cb60d4d10a9ae5b06a68861e64d4e534430eb26a729a218bd526294d10c58a9314a68864f5398a5344317aa2c529a218b1516294d10c9ea6b14a688635719925344317324c529a218b5926294d10c5cc8b14a68862d6458a534431b322c329a21999896194d1087cedaa2a68843e761515344317aa6c4a9a218b1536254d10c5ea8312a68862c54189534430fb26c6a9a21871936354d10c5ec9b12a68862c64d895344327b1ec4a9a218bd906254d10c58c8312a68864f63189534431bb26c2a9a218d1936154d10ccec5b0aa68866462d85534431c326c0a9a2117dd95314d10a3ee8a98a68851c7454c53442a7b92a629a21531c95314d108dce5320a68846d72990534428f3a4c629a21475d26314d10a9ce5318a68854d7298c534430f32ea829a21c5dc75414d108baed2a0a68854e7295053442a6b94a829a2117dd95414d10a9ee4aa0a68854c72550534430f328a829a21c55c45414d10a9ce5320a68854d7299053442aab8cc829a21555c46414d10aaee2b10a68864d6218853442aab88c429a2153dc96114d10a98e4b08a68
  | 7 => 0x8a0621879506350310c3aa831a818862e5418940c4316aa0c4a06218d9506150310c6aa830a818843d76d5040c428f39ea8206214b9cb5410310a3ce9a9c618854e72d4e30c422f3b4a69862187192534c310c38c8a9a618864e5318930c4326a98c4986219594c614c310caaa630a618845d76d4c30c428f3a6a618621539cb530c310aa8e6b0ea908564725875484237396c6aa4211b5cb63552108bce7b12a90845d73d89548421fbb2a82a4219398e6215210c9ac7310a90864e635885484326b1ac42a4219598d6115210caac6b08a908666625845484332b12c22a4219998961d4e10a9ce5a9ca70846e729925384236b94c929c21539cb6354e108beeca98a708564725845384237396cba1c211b5cb65d0e108dce432e870846d721974384237396cb21c211b5cb6590e108dce532c870846d72996438432b29ac321c21391c96190e108dce532a870846d72995438428e3a2a6a1c211b9c86510e108dae4328870854e73d4a528422f39cc929421175ce6494a10a9ce7b12a50846f76548528422f39ecba1421175cf65d0a108bce632e850845d73197428422f39ecb21421175cf6590a108bce732c850845d73996428426a39ac321421999496190a108bce732a850845d7399542842963a2a4a14210f9d365cca1087ae9b2e650843e74d96328421eba6cb19421535ca530ca10a9ae7290650854f754c832842a6baa6419421711c5320ca10caacb31e83086575498f418432aaa4c7a0c219559563d0610ccacb31683086c66398b4184362b1cc5a0c2199d5262d0610ccaa931683086656558b418436331ac5a0c21b498e60d0610dc4c5306830843e76951418421ebb6a820c211d5db541061096aedaa083085b270d5041842d9380a820c21351cd60106109c8e4b008308475759933184273390c998c218d99354cc610acce5a9e630854e72d4e318422f3b4a698c219394c624c610c9aa6312630845d76d4c31842a7396a618c21711c9310c6109cce532063084777655031842abb9aa818c211d5db530c610acce5a9863084d576d4c31842e3396a618c21749c3530c610aaaeda98630865576d4c31842aaba6a618c21559cb530c610e8ce5a98630854672d4c31843a2b96a618c21d49c3530c610ba4e029863085567590c31842ab3aa8618c21555ce520c610aacea1906308746520c8318425a3a2c018c21391c9600c6108eaeb32643084d673193218431b326a990c212d9d063c8610a9ce7a94430864c63949218432631aa490c21711cd21086109ace732043084777655021842b3b92a810c21595ca53086108eaec298430847576d4821842ab39ea410c21395db5208610b8ce7a9043085e270d4821842b2bb6a410c21995db5208610acae9a90430856673d4821843a339ea410c21519cf5208610e8ae7a90430876270d482
  | 8 => 0x1410c430938e8b0062184cc72580310c327b286510861d10ca5188430ac8e4a8c421843e74195210c21eba0ca908619518e5148430ca8c6a8a421856472545210c22ebaec610861279d36308430caaca188421856475484210c333b2a4210861995952108430b88e6908421855671d0e500c22ebb0872806117dd563900309a8e2b1c801851d7510e400c30eaa4c620061475d44310030b32e0218801863654584400c31aaa2c220061359c664cc0308beecaa6601861e64553300c22ebb4a7180611e5da538c030ba4e3a1c601861f65d91300c22ebacc898061279d2644c0309ace3322601861f65191300c30eba8c898061179db544c030c38c9aa2601845c76551300c30e322a89806195d97614c030d28c9b0a601865765185300c34bb20c298061a5190614c030d8ec430a60186c462185300c32baa0c29806195550614c030c38c9282601863b65d91300c31db28c898061a6193634c030ce6cbb0a601867365185300c358320c298061b4d8c614c030c9cc7316a98864d6398b54c432731ac5aa6219358d62d5310cacc730ea9886556398754c4333314c3aa6219958a61d5310a3ce7aa4a98852e72d5254c432731cc52a6219358e6295310c9cc6b14a98864d6358a54c432b31cc32a6219558e6195310cccc530ca9886656298654c428f39ec8aa6214b9cb64553108dce5b1aa98846d72d8d54c422f39ec4aa621175cf625531087eecaa0a98861d7399353c4317324c5a9e218b59262d4f10c5cc8b16a78862d6458b53c431b324c3a9e218d59261d4f10cccc530ea7886656298753c428f3a6a729e21539cb5394f10a3ce9b1aa78854e72d8d53c422fbb2a629e211b9ca6414f108dae5320a78846e72d9743c4236b96cba1e211b9c865d0f108dae432e878864e5398b43c4326a9cc5a1e219594e61d0f10caaa730e878846e7219643c4236b90cb21e21475ce5490f10a3ce9a9c878854e72d4e43c4237394caa1e211b5ca6550f10a3ce9a9a878854e72d4d43c422f3b0a6a1e211b9cb6510f108dae5b28878846e7299443c4236b94ca21e2117dd95310f10a5ce9a94a58854e73d4a52c4237bb2a429621179ce6414b108bae7320a58845e73d9742c422eb9ecba16219398e52d0b10c9cc6a9685886665298742c4332a94c3a1621179cc6590b108bae632c858852d7295242c422f39eca21621175cf6510b108bce7328858845d7399442c421f3a0cb196210f5d0658cb1087ce9b28658843d74d9432c421f3a4ca196210f5d2650cb10a9ae5298658854d7394832c42a7baa6419621535d5320cb10b88e299065885567395241c42b3394a920e21559ce5450710acce52a283884767615141c429b3a4a6a0e211d9d85350710a6ce929283884767614941c42e23926218e21711cd2108710a3ce7aa4818852e72d5240c421f3b4a
  | 9 => 0xceda92629846e76149314c333b16a298a619918b514c530ccec428a629866462145314c31c2a6c098a618e150604c530ce6a23026298717544c4314c38a2a26218a61711c9310c530e8ea49886298744524c4314c21fba2cb10a610f1d1658853087ce9b2a429843d74d95214c30faa6c690a61871536348530c3ea831a429861c5418d214c32bb1ea290a619518f5148530acce5a8a429865763145214c32a318a290a610fdd16508530878e8b28429845e7598c214c30e2a4c610a61871516308530cacc6288429865563144214c2b2b90a210a61599d52108530ac8ea908429866665484214c33232a4210a61c9d512108530e48a890842985c473484214c30e2a4c7a02618715163d0130cacc628e809865563147404c28f3ac8720261879964390130e2c8628c809861c54d8d404c30faa0c6a02618715063501308ecebb0a809863754d85404c31a2a6c2a02611d9d46150130c6ea830a809863454185404c23b3b6a2a026195d8f5150130ca8c7a8a809866762d45404c332316a2a02611d9d85150130caec628a809865463145404c333b10a2a0261991885150130c3ea9318809861c5498c404c30faa2c620261871516310130a3ceb218809861e6590c404c31baa4c2202618d1526110130c6ea8b08809863454584404c23bbb6a2202611d5db5110130cacc7a88809865563d44404c333316a2202619958b51101308eeec288809847576144404c32b318a2202619558c5110130e2c86288809866662144404c332b10a220261cc15051cc130aace32a4609861d64152304c30f3b0a918261875d8548c130e28a9a8c609871754146304c38a2a0a318261d1d48518c130e88a428c609865764146304c32ab20a3182611bdc961d50308d8e4b0ea81843f76550540c31aaa2c22a0619598e6115030cccc5308a81863664584540c32b31ac22a061999896115030ccac4b08a81865565987430c363314c3a186195d5261d0c30caaa930e861865565587430c363312c3a186117dd95410c308beeab0086184d471580430c237394c9288611b5ca64944308eeeca88a21863564544510c2b2392a2288619958951144308dce5b2e821846d72d97410c30eaa4c7a08618b95162d0430c5aa8b1682184cc7258e410c2b2392a3208611bdc965504308d8e4b2a821846e72195410c236b90caa08619518d5150430ac8e4a8a821856472547310c22eba8c918861339c8648c4308beecaa4621861e64552310c2a6392a318861591c9510c430b88e4988621845d75990310c267394c818861555c7540c430c3cc8aa0621855575984310c2a6392a218861711c9510c430aaeeca88621865776544310c2abba2a218861d1dc9510c430aa8e4a88621874472544310c2a2392a218861355da410c430aaaeb208621855575504310c38aaa28218861741c
  | 10 => 0x61e65d52434c2ab38ca921a61871526090d30c76a8302869851e75d91434c30e32ec8a1a61479d25450d30aace32a2869845e76151434c28f3b0a8a1a61879d85450d30c38a8302869869b64181434c30e2a4c621a61599ca54d4530acae52a6a29856772553514c2b2392a9a8a61c55cc54d4530aaceb21ea2987145490f514c38a2a287a8a61c9d5352d4530e48a9a96a29855573193514c2b3390c9a8a61595c864d4530acce5b1ea29856572d8f514c23abb687a8a61599cb43d4530acae5a1ea29855573d8b514c333b14c5a8a614d9d360d4530a6ae9b06a29856672d83514c2b2b96c1a8a618bd526294530c58a9314a29862f5458a514c3162a2c528a618b9935294530c5ac9a94a29863664d46514c31ab26a328a619998b5194530ccac5a8ca29843e76d51514c21f3b0a8a8a618bd536254530c58a9b12a29862f54189514c3162a0c4a8a618bd935254530c58c9a92a29847776544514c29bba2a228a614d1d15114530acee4a88a29856472544514c237394c828a611b5ca6414530c6ccbaa0a29871773d50514c23abb4a828a61599ca5414530acae52a0a29847776550514c2b3b92a828a61591c95414530c6cca2a0a29871573150514c2ab3ac8628a61c5d524314530e28a9218a2987175450c514c38a2a28628a61999975214530e4ea9a90a29872454d48514c3a321ea428a61d150f52145308eaed290a29853674948514c29aba4a428a611ddd95214530a6ee8a90a29853474548514c393aa0a428a61c91505214530e8c86290a29874543148514c2aab9cc828a61599ca6414530acae5320a29855573190514c23abb68628a61599cb4314530acae5a18a2985567090c514c2b9b828628a615c1c14314530e2ee8a18a2987537050c514c2aa3828628a61d41c14314530aaee6b10a29855573188514c332b10c428a614ddd16014530a68e8b00a29856772580514c2b2392c028a614ddd13014530a68e8980a298567724c0514c2b23926028a611bdc965d05308d8e4b2e829846e72197414c236b90cba0a6187d5263d0530c38a931e829861f5458f414c30e2a2c7a0a611b9d662d0530c5ea9316829862c5498b414c2363aac5a0a618bd5162d0530c58a8b16829846f76d4b414c236bb6a5a0a619398f52d0530c9ac7a96829846f7614b414c236bb0a5a0a619398c52d0530c9ac6296829865663d47414c333316a3a0a619958b51d0530cacc628e829865563147414c333310a3a0a619958851d05308dee4b2c829846c72596414c237396caa0a611b5cb65505308dee4b28829846c72594414c22f3acc620a61871526310530c38a8b18829864e63148414c326b18a420a619598c5110530caac6288829867051982314c2373aec498a618bd53624c530c58a9b12629846e75189314c317aa0c498a618b150624c5308d
  | 11 => 0x10339b28c2a0081acd906150040da0c630a80206e0621854010339b2ca2a00819cd955150040cacc730ea9986666298754cc32b31ac3aa6619998961d5330ccac4b0ea99853671d5254cc32b31cc32a6619998a6195330cacc6b0ca9986666258654cc332b12c32a6614d9c764553308dce5b0aa99846d72d8554cc21fbb2a82a661559c65490f30aace32a2879845e7615143cc29b3a6a328e61599cb5194730c3cc8a1ca3984777654451cc237396cba0e611b5cb65d0730cacc728e83986666294741cc32b31aa3a0e619998951d0730a6ae32a4839846e72d9441cc236b96ca20e611b9ca65107308dae532883985c4724c431cc21f3a6ca10e610f5d3650873087ce9328439843d7499421cc2b2b94a210e6159dd52108730acaea90843985c47348421cc29b38ea9206610f9da5450330c3ca831a819861d5418d40cc31b2a0c2a06618d550615033087aedaa0819853671d5040cc2aa38ac7aa4611b9cb61552308dae5b0aa91843f76550548c32ab1cc22a4619998a6115230caac6b08a91866662584548c332b12c22a4619559661d0e30d8cc530e871865754987438c32aaa4c3a1c619559561d0e30d8cc4b0e87186d261983438c21f3b4a8a1c610f5db5410e308baedaa0871849d76d50438c2cd386a821c61669c05410e309a8e2b00871856672d46518c237394c928c611b5ca64946308eeeca88a31846e72d97418c236b96cba0c611b9cb65906308dae5b2c831846e72996418c236b94cb20c61331c96390630caac728c831853474545418c22ebacc918c61339c8648c630c3cc9aa4631866462945318c332312a298c61711c9310c63099ce5320631845f76550318c2abb8aa818c61555c6520c6309aaeda8863185c672d44318c2e9386a218c61749c0510c630aaceb208631849c74580318c266392c018c610f9d3658863087ae9b2c431849e74d8c218c2b2b94a210c61959943108630e8ca4188431856775484218c2b2baa4210c61711cd21086309a8e2b1c811861d5458c408c26b38cc99846117dd954cc230c3cc8aa6611846f72587544c236392c3aa2614ddc563d5130a68e2b1ea89851f73587544c297b92c3aa2614b1c961d5130a6ce3b06a89853571d83544c31baa4c32a2618dd516195130caac730ca89866662986544c333312c32a261995896195130c6ec9b0aa89865763d85544c333b16c2aa2618dd906155130caec630aa89866762185544c332310c2aa2619c187605513087eecaa0a89853771550544c29a38aa82a2614d9c66415130a6ae3320a89853671d8c544c29ab8ec62a261475cf6115130a5ce5b08a89852d72d84544c28eb98c22a2614ddc56015130a68e2b00a89847675987434c31baa4c3a1a618d15261d0d308e8eab0e869863754587434c31a2a2c3a1a618e15260d0d30c3ee932c8698
  | 12 => 0x208818d5965190440e2ca6a8c8220715535464110393292a320881c95495190440e2aa6a08822072552504411033928ac020881c354d5210440e2aa6a88822072552544411024e39ac0208812b1c96010440d64c2b00822046e729973110236b94cb988818759253cc440c5cc8a96622062d6454b311031b322a3988818d59151cc4408dce532c622046d72996311030f322a71888187591538c440c5cc8a94622062d6454a311031ab24a3188811bdc9654c4408d8e4b2a622046e721953110236b90ca9888187d91534c440aa8e2a9a622046d75d89311032729ec4988819354f624c4408daea312622064e531893110326a98c4988811b9da524c4408d8ed292622046e7654931102363b2a49888199d8a514c440cc8c528a62206376454531102aa39aa29888199d89514c440cc8c4a8a622065953d813110338a8ec0988811b9ca650c4408dae5328622043d75d903110257396c818881555c6530c440c3acb218622055573944311031ab2c821888155dd5310c440aaaea9886220657654c4311032ab2a621888165dd1310c440b88e49886220746524c431103a2a926218881741c1310c4408bce732c422045d73996211030f322a710881875915388440c5cc8a94422062d6454a211031ab24a31088117dcd65484408b8e6b2a422045e73195211022eb98ca90881175d763484408baea31a422045e7694d211022e3b4a690881179d953484408b8eca9a422065763945211032a31ca2908818dd915148440caec6a8a42206546354521102b2392a2908819c54760484408bce7328422045d73994211021ebaec810881279cf6408440acae528842206356590421102b3baa4210881595d52108440cceca90842206656548421102d3ba24210881711cd2108440e8ca690842207455348421102f03824210881c554d51d0040e4aa4a8e802043d76952401023cbb4a920081171da53500408bceca9a802065653d85401032aa9ec2a00819594c6150040caaa630a802047476945401032bb1ca2a00819518e5150040ccec528a802066462945401023b3b2a2a008195d8d5150040ca8c6a8a8020667625454010332312a2a008187dcf6550040c38e7b2a802063771d95401031a38ecaa008187d976350040c3eca31a802049c7694d401030fb2ca6a0081271d95350040c3ecaa9a802063765d85401034a31ec2a00818dd946150040d2ec630a8020694631854010353b10c2a0081a91886150040d2ca630a802069553185401025a3b4a2a00818dd965150040d28c728a80206a462945401025a3b2a2a00818dd955150040d28c6a8a8020715535454010352312a2a0081c95495150040cb6e7b2a802065873d954010339b8ecaa00819c1c76550040cb6cbb1a802065b6518d401034db20c6a008196d965350040cb6caa9a802067365d8540
  | 13 => 0x2108540b88e690842a07475348421503a229a4210a81d414c51d0140ec0a428e80a071453d46405038ba98a320281c514c5190140e4ea428c80a07245214640502ab38ea729881555c75394c408dee4b0ca62046c72586531028f3a6c32988153dc96194c40a98e4b0ca6206556118653102ab38cc8a9881555c66454c40a3ce930aa62051c7458553102a7b92c2a9881531c96154c40ab0e0b0aa62065561185531022fbb2a6298819554e6114c40caaa6b08a62047575987431032b29cc3a18819554e61d0c408eeeab0e862065653587431032aa9ac3a18819654d60d0c40c3acb29c862065a53580431025a38ac021881a698d6010c40c9ca7316a22064d5398b511032729ac5a88819354d62d4440aace7a8ca22055573d4651102b3396a328881595cb51944408dee4b1ca22046c7258e511022fb9ac528881171cd6294440acce5a9ca22056572d4e511038a3a2a728881599c85394440acae429ca2207155390e51102ab39ea528881555cf5294440e8ca7294a2207455394a511029b3a6c72888159dc96394440ac8e4b1ca2206556318e511023abb68728881599cb4394440acae5a1ca22053674d8a51102abb9ac528881551cd6294440ccac4314a22047676d4d51102b3396a6a8881595cb5354440e28c929aa2207147454d511038a322a6a88811d9d85354440acce429aa2205657214d511029abac86a8881c554e4354440e2aa621aa22055673d4951102aab9ea4a8881d194e5254440e8aa7292a2207246494951103a329aa4a8881d154d5254440e48c8a92a22072643549511039221aa4a8881559ce6454440aaae7322a2205667299151102b2b94c8a88814d9d26354440a68e8b1aa2205677258d51102b2392c6a88815c1c16354440caac631aa22047676d0d51102b339686a8881595cb4354440e2a8621aa22053674989511029a3a2c4a888155dcd6254440aa8e6b12a220570705895110332b10c4a8881559cc4054440aaae6202a22056572101511022ebb4a62888117dd95314440c9ca7310a22064d53988511032729ac4288819354d62144408daed290a22064e639485110326b1ca4288811bdd95214440c9cc6a90a22064d63548511032b29cc2288819554e6114440ccca5308a22066552984511023bbb2a2288819598d5114440caac6a88a220666625445110332b12a228881175d663d04408beeab1e822045d7694f411022fbb2a7a08811b5d662d0440c9ca7316822064d5398b4110237baac5a08819394d62d0440c9aa6b16822046d7694b411032731ca5a08819358e52d04408deeca96822064e6354b4110326b1aa5a08819598e51d0440caac728e8220666629474110332b14a3a08819598d51d0440caac6a8e8220666625474110332b12a3a08819c54560d0440c3acaa9c822062d6554a4110386a9aa5
  | 14 => 0xe5a1ea2a055673d8b51502aab9ec5a8a8199d8a62d4540aace7b06a2a055573d8351502b3396c1a8a81595cb60d4540c9ea7314a2a064c5398a5150327a9ac528a819314d6294540c9cc7a94a2a064d63d4a515032b31ea328a819558f5194540cccc5a8ca2a066562d46515022f3b6a6a8a81179d85354540c9ea7b12a2a064c53d895150327a98c4a8a819314c6254540c9ec7a92a2a064c63d49515023bbb2a228a8155dcd5114540aa8e6a88a2a05677254451502b2392a228a811bdc963145408d8e4b18a2a045f73588515022e39ac428a819599753145408eaed298a2a05667294c51502b2b94a628a811ddd95314540acee4a98a2a05647254c515032b328a628a81999975214540e8ea7a90a2a074453d48515023abb4a428a81559ce5214540aaae7290a2a04777654851502abb9aa428a81551cd5214540e8ea6290a2a07445314851502b3b92c628a81591c96314540a6ae8318a2a06556318c515023b3b68628a81599cb4314540acae5a18a2a05737050c51502b83828628a8155dcd6214540aa8e6b10a2a0535741885150332b10c428a8155dcd6014540aa8e6b00a2a05677258051502b2392c028a8155dcd4014540aa8e6a00a2a05677250051502b23928028a8117ddb53d05408beec29e82a064f5398b415032629cc5a0a8193d4d62d0540c98a6b1682a046f76d4b415032731ea5a0a819358f52d05408deec29682a064e6314b4150326b18a5a0a819598c51d0540caac628e82a0666621474150332b10a3a0a819c1466090540cb0a7b0282a066852d81415032c298c0a0a819a1486050540ce6a230282a046f725973150236392cb98a811bdc9658c5408d8e4b2c62a046e72d953150236b96ca98a811b9ca654c5408dae532a62a055671d4d31502373aec498a8193d4f624c540c98a7b1262a046e751893150327a98c498a819314c624c5408dceda9262a046c76d4931502373b0a498a811b1d8524c540aace7a8a62a066762d453150332316a298a8199d88514c540cc8c428a62a046f725943150236392ca18a810f9d6640c540c3cc829862a061d6414c31502aab88a618a818b990520c540c5ac829062a063664144315031ab20a218a81555cc510c540aacea98862a0554754c4315032b32a6218a8195195310c540b88e498862a0747524c431503a22926218a8117dcd65885408b8e6b2c42a045e73d95215022eb9eca90a81179ce65485408bae732a42a045e75d8d215022f3a8c690a81179db53485408b8eda9a42a045e7614d215022e3b0a690a8195d8f5148540ca8c7a8a42a056672d45215032bb18a290a819518c51485408bee6b2842a045c73594215021f3acc810a81879905308540c3ac829842a063664144215031ab20a210a81595c85108540accea90842a056475484215033332a4210a8199195
  | 15 => 0xe5741812108673398c09084339dd921d4021b88e690ea010ce47648650086e239a4328043781c121940218bee6b24a010c5c73592500861fba2c7280430f1d16394021e886418ca010ce4764855008753b2242a8043a91912154021b88e690aa010ec763485500876231a42a8043781c12154021c6ce2322a010e3571191500870fb26c6a8043871936354021c3ec831aa010e1c6418d500863b3b482a80438d1924154021ca8c720aa010e3464505500872a31a82a804339dd92114021d4cc8908a010ea56448450086e239a4228043b198d2114021d8ac6908a010c7b7654050086ab38ea729e811bdc96194f408d8e4b0ca7a045f7654c53d032b29cc3a1e819554e61d0f40aace7a8ca3a056672d4651d0237b92c728e811b1c963947408bee6b14a3a045c7358a51d023bbb2a228e819598e51d0740cccc528e83a06566354741d0333312a3a0e811bdc9654c7408d8e4b2a63a046e72d9431d0236b96ca18e811b9ca650c7408dae532863a05557194c31d02aab9ca218e8155dd5310c740aaaea98863a05c4724c431d02e83826218e8117dcd65487408b8e6b2a43a045e73d9421d022eb9eca10e81179ce65087408bae732843a05657294421d02b3baa4210e81595d52108740b88e690843a05e07048421d0333b16c2a9c8199d886154e40cc8c430aa72045f7654c53902aa38aa629c81551c55390e40b28e2a9c87205547154d439025a38aca21c81275db5310e40b34e1a98872059a7014c439025a38ac021c8193d8f6254640c98c7b12a32064f631895190326318c4a8c811ddd95114640aa8e6a88a3205647254451902aa39aa320c81591c95190640b28e6a8c83205a47254641902aa39aa2a0c81591c95150640938e6b2883204ac72594419025abb6a220c816c9c35110640b64e0288832049c735804190256392c020c811b9cb65cc6408dae5b2e632046e72d963190236b96cb18c811bdc9654c6408d8e4b2a632046f725943190236392ca18c812b9cb640c640aa8ea9886320597744c431902e23926218c81179cf65886408bae7b2c432045f73595219022e39aca90c8117dcd65086408b8e6b28432049e73d9021902b23aa4210c8169dd12108640b88e6908432049c73597409025a38acba0481539cb61d4d40a9ae5b0ea6a06576198753502ab38ec1a9a81555c760d4d40caea730ca6a065753586535022fbb2a629a8155dc55314d40aa8e2a98a6a046f725845350236392c229a8153dc96114d40a98e4b08a6a051d74184535032ab08c229a8155dc56014d40aa8e2b00a6a065453987435032a29ac3a1a819614e6090d40cb6a630286a05667294f51502b2b94a7a8a8159dc953d4540ac8e4a9ea2a074753d4b51503a229ea5a8a81599cb63d4540acae5b1ea2a06576398f515023b3b687a8a81599cb43d4540aca
  | 16 => 0x86abbac641884395596320c421b8ce51906210ec5628c831086aaba8641884395594320c421ccaca1906210f46650c83108762b286418843d1594320c421c8aca1906210ec7640c83108762b206418843d1d50320c421e8aa81906210ec432980310865aba0c7108431d5da5288421d4ac8a144210ec663cca210876231865108431ddd564484219a8e6b224210cf070591210872bb2ec6908431d5d663484219ace731a4210e576518d2108763b90c690843b15c86348421ca8c72924210ec46394921086733b68490843719cf4248421b8ae7a124210ec463d09210876231c8490843a9d914248421d88c6a124210ce67610921087623188490843b118f32484219cced1924210ec4638c921086723b26490843b118d3248421d88c61924210e6575d952108672ba6ca90843399cf65484219cce1b2a4210e6676d95210867339ec890843399c36448421acaeb3224210dc67399121086e2b9cc89084359dd56448421b8ee6b224210dc47359121086f1b82c890843781c164484219ceeab224210e67755912108753ba2c890843b1dcd64484219c8e6b224210ec473591210866239ac890843b8dc164484219c8e0b224210ee0705912108670382c890843399d864484219ccedaa24210dc673d5121086e2b9ea890843399da5448421d4ec92a24210dc67395121086e2b9ca890843399d954484219caecaa24210ea76455121086733b0a890843c95505448421d8ecbb1a4210f4765d8d2108763b26c690843b15936348421acaeb31a4210dc67398d2108672bacc690843995d663484219cae931a4210ce67398d210866339cc690843399c26348421aceeab1a4210ec56318d2108672ba0c690843b19cc63484219cce031a4210dc67618d21087633b0c690843b1d946348421e8eca31a4210ec76418d2108763320c690843b15906348421d88c831a4210ec77518d2108762ba8c690843b1dd06348421d8ce831a4210ec57418d21087623a0c690843b1d506348421d8ca831a4210ec55418d21087622a0c690843b1dc06348421d8ce031a4210ec57018d2108762380c690843399db5348421b4ce9a9a4210da574d4d210876231ea690843391da5348421d88c729a4210ce77654d21086723b2a690843b118d53484219ccec29a4210ec46314d21087a2a98a690843399db43484219caeda1a4210d6675d0d21086b2bae8690843b118f43484219ceed21a4210ce47690d21086b33ac8690843595d64348421d88c721a4210ce77650d21086723b28690843b118d43484219ccec21a4210ce57610d21087623188690843b118f6048421acaeb3024210dc67398121086e2b9cc090843b1d8e6048421d88c73024210d677558121086d3ba2c090843691d16048421b8ee6b024210dc473581210876231ac090843b1d8c6048421d88c63024210c
  | 17 => 0x1a431d9d66190d21ca8a730c8690c7475586434872a29ac321a43391c96190d218eee2b2a8690c7b70595434863c382caa1a43479d35350d218eae3b288690d1d7414c434862f3acc7a0a43171d563d05218beeda9e8290c5d76d4f414862fbb0a7a0a43175d853d0521c9ea73168290e4c5398b4148717aa2c5a0a4393d4d62d0521c98a6b168290c5e73d95414862eb9ecaa0a4317dcd65505218b8e6b2a8290e4c53d894148726298c4a0a438d9954110521e2ea6a088290e4c5398b314872629ac598a439314f624c521c9ea63126290e4c5318931486aa3aa6218a43711c9310c521a98e6aa44290d6870552214862f39cc9a8243175ce64d41218bceda9aa090e1f64d4d504870e326a6a8243179d85354121c3ec829aa090e1c6414d504863dbb2a0282434e1d150141218bee6b20a090c5c73590504872a38ac7aa0439558e61d5021a3ce7aa4a810e5663986540872ab1cc32a0439998a6195021a3ce7b22a810c5e73181540862eb98c0aa0430fdd954150218bee6b00a810c5c73580540870eb9cc9a98438d59261d4c21a3ce9a9ca610d1e74d8d5308732310c2a984317dd95314c2187ee8b00a610c3c74580530863b388cba18431d5d661d0c21caca730e8610e55539874308672b94c3a18431d9c46590c21a3ae72a48610d1e74d4e430863db82caa18431e1c16550c218bceda9a8610d1e74d4d430862f3b0a6a18431d5d46150c219cae430a8610c5e73d94430863d380ca218431e5c06510c218beeca988610c75759844308672b94c2218438b5526290421998e6b148210d5673952410863abb0a7208431ddd562904219a8e6b148210dc47358a4108673baac52084399dd56290421d8ee6b148210ce47358a410876239ac520843311cd62904219c8e0b148210e656590a41086ab39ca8a08431d9d854504219cae431a8210d367494d410863b3b0a6a084359dd56250421b88e6b128210de070589410869b3a4a4a0843595d64250421e48a8a128210ce572181410862f39eca20843175cf65104218bce73288210c5d73994410863abaec99884339dc964cc4218eaedaa66210d5573d53310869aba6a798843595d762cc421b4ae83166210ce67690b31086e339c8598843a959142cc4219cae53066210e4d5398a310861f3a6ca188430f5d3650c42187ce93286210c3d74994310863abaec818843395cb640c4218eaedaa06210d5573d5031086aabacc6188434d5d3530c421aaaeb2986210c777654c31086abbb2a61884395dd9530c421aaee8a986210f447254c31086aa382a618843555d6430c421e2aa92186210d557550c31086e239286188431ddd5620c4219ceeab106210e67755883108673ba2c418843391c1620c4219caed2106210ea5649083108672bb28418843711cd420c421ccacb9906210f4553cc8310
  | 18 => 0x4c4319aeec98ea018dc4724c7500c66a3b26328063711c93194031ba0e098ca018c6f72592500c636392c9280630fdd16294031878e8b14a018cd4764c5500c74bb2262a8063a51913154031b88e498aa018ec7624c5500c76231262a8063741c13154031c3ce6322a018e1d73191500c71b388c8a80638d5c464540318bced21aa018e1c6490d500c70e32286a80638bd936254031c58c9b12a018e2f64189500c716320c4a80639390c6254031c9a86312a018c7676905500c71a32482a80639918a4154031c68c8a0aa018e6462505500c66bbb26228063a59913114031d2ac8988a018dc4724c4500c7633126228063b158931140318f6eca80a018d4c7358b5488732b14c3aa44317dcd60952218b8e6b04a910c3f76550548870eaa2c62a443879916315221c9cc6b10a910e5663984548872ab1cc22a4439958a6115221ccac530ea710c3f74582538861e3a2c129c4317dd95314e21c3ac8a98a710e2d72990538870eb24c629c438b9916214e21c6ac9308a710e656298453887172a2c5a1c438b55162d0e21c6aa930e8710ce472586438863d384caa1c431e5c26550e21c3ca8b1e8510e1d5458f428871aaa4c3a1443539cc5490a218daec29c8510d2e7414e428866639ac3214431b9da5450a21a5ced2a28510e2e7695142886a7398a8a14434b9d05350a21c5ca83028510d1d7414e328862f3b4a6994439594c614ca21caaa630a6510c5d76d4c328868eba0a619443395c7640ca218daedaa06510d4f735503288636bb6a619443335db530ca21b8ce3a986510d4d76d4c3288726bb6a619443535d3530ca21e8ce3a986510d4e70d4c32886c6ba0a619443719c4530ca21a9ceb2186510dc67190c32886a73aa8619443c3551430ca21998e6b148310e2e54588418872729ac418c43715c4320c621b88e49886310d357414f2188726b186528443179cc64542218bae6322a110c6c76509508863dbb2a0284431ddc563d51218bce7306a890c5d73983544872b31ac32a2439558d6195121ca8c7b0aa890e5b63d81544872c31ec0aa2438ed906055121cb6c6302a890e58631815448739b08c0aa2430fdd95415121a70e0aa0a890c5f73580544862e39ac02a24356dc154d4d21ab0e0aa6a690e1f6499353486aab88c9a9a43479d360d4d21a3ae9b06a690d5571d83534862fbb2a629a431d5c66414d2187ee8b00a690c3c74580534862ebb4a829a4317dd95414d21ab6e0aa0a690d587055053486aab8ec829a43555c66414d21c3ac8320a690d1e74d84534868eba6c229a4347dd16014d21a38e8b00a690d5771580534868f3a0c029a43475d06014d21aaae2300a690c7571d97434872ba9cc3a1a439514e61d0d218e8eab0e8690e5753587434872a29ac3a1a43391c961d0d218f4e1b2c8690c7970d96434863bb8acb2
  | 19 => 0xc2a28218d577558d410c6e2392c6a0863741c16350431a6ce929a8218d557590d410c78a2a286a0863355cc6250431a6ce92928218d95748c9410c66abb064a0863b118832504319aae63028218e9564507310c62ebb4a7188631d5da538c431d2ac8a1c6218ec6628ca310c62fbaac898863331c9644c4319b0e0b226218e4f65d89310c727b28c498863b1dc4624c431d8ae23126218cd676d05310c6e33968298863715cb414c431d88c5a0a6218ec462905310c74bb228298863b1189414c4319acec20a6218ec462105310c63bbaac898863391c9644c4319e0e0b226218cd676d0d310c6e33968698863715cb434c431d2ec8a1a6218cd67610d310c733b2ec49886399d94624c431d8ec63126218ec773189310c763298c498863b1d0c624c431d8c863126218ec543189310c762218c498863359db324c431d88c59926218ec4628c9310c7623126498863955d7654c4319aae9b2a6218cd672d95310c66b386ca98863959db654c4319ace5b226218cd670d91310c6aabacc898863719ca644c431b8ae53226218d5775591310c6e3b92c898863711c9644c431ba6e0b226218dd070591310c66bbaac89886395dd5644c431d2ee8b226218ec772591310c66a392c898863b11c9644c431988e4b226218ed370591310c66a382c898863b41c1644c4319a0e0b226218cd676191310c66b3b6a898863719cb544c431b8ae5aa26218cd676951310c74bb24a898863719ca544c431b8ae52a26218cd676551310c66abb2a898863a5d91544c4319acec2a26218f1554151310c763b2ec498863d1d97624c431d8ec9b126218ec564d89310c6aabacc498863719ca624c431aaeeab126218ec562189310c66aba0c498863359c0624c431b8cec3126218ec676189310c763b28c498863d1d94624c431d8ec83126218ec664189310c762b20c498863b1190624c431d8eea3126218ec575189310c763ba0c498863b19d0624c431d8ae83126218ec474189310c763aa0c498863b1950624c431d8aa83126218ec454189310c763b80c498863b19c0624c431d8ae03126218ec470189310c66b3b6a498863659d3524c431b2ae9a926218ec462d49310c66a3b4a498863b118a524c4319a8eca926218ec462549310c66b3b0a498863b1188524c431e8aa42926218cd676d09310c66abb68498863559d7424c431aaaeba126218ec462d09310c66a3b48498863559d6424c431aaaeb2126218ec462909310c66bbb28498863351d9424c431d88c4a126218cd676109310c66abb08498863b1188424c431d88c5b026218d5575981310c6e3394c098863715ca604c431d8ec53026218ec462981310c6abbaac09886365dd1604c431b28e8b026218dc772581310c6e2392c098863b1189604c431d8ec43026218ec462181310c66aba0c098863359c86
  | 20 => 0xd73d83524c6b2b8ec1a92631bdd9521493187ee8b00a498c3c74580524c636bb4a8292631bdd95414931ad6e0aa0a498d6870550524c6a6b9ec829263595c76414931a9ae7320a498d6571990524c716b20c8292634b9d36314931a5ae9b18a498c6d76d0c524c6b338e8629263595c74314931acee2a18a498d647150c524c6973a6c2292634b5d36114931a5ee8b00a498d2c74580524c6a7b9ac02926359dc56014931a5ce8300a498d2d74180524c6a6b98c029263595c460149319a8e2b1e8498e4e63d4b424c726b1ea5a12639398c52d0931c9ac62968498e6752987424c732294c3a1263351cd61d0931ccea4b0e8498e6452587424c66a38ac7212639398c5290931c9ac62948498e6452986424c66a39ac321263991496190931a5ce9a928498d2d74148424c732294c31926399d48614c931c3ea8b1e8298c6e7598b414c6363aac5a0a631b5db52d0531c9cc7a968298e4d63d4b414c636bb0a5a0a639398c52d0531c9ac62968298e4f63149414c726318a4a0a638d9954110531e4ea4a088298d6472553314c6b8382a998a63531c9548c531ab0e0aa46298c6e72993504c636b94c9a82631b9db5254131c5ec9a92a098e2c64d49504c6373b0a4a82638bd905254131c58c8292a098c7b76540504c69c3a2a0282631bdc964141318d8e4b20a098e4e6358b540c72639ac5aa063991c562d5031ccac530ea818d2e72d52540c72731cc52a0639398d6295031cacc730ca818e6662986540c732b14c32a0634b9cb64550318dce4302a818c6d72181540c61fbb2a82a0631bdc960150318d8e4b00a818e3554986430c672392c321863539ca5490c318beeab0c8618ccc72586430c6e2392c32186335dd56190c31caeeab0c8618ec772586430c66a392c321863b11c96190c31988e4b0c8618cd470586430c6a7394a8a1863179d85450c319aae23128618d5775585430c6e2392c2a1863741c16150c319aae23028618d2e74d4a520c70f32287290631bdd952148319aae331e8418e4e6394b420c72731aa5a1063355ce61d0831ccca530e8418e6552987420c696b94a9210631edc165508318f0e0b2a8418cd57118d420c66ab98c2a1063355c663108319aae73088418c5d75d92320c66bb8ac919063175db548c831a9ae5aa46418d5575d86320c6caba0c319063355c6608c831a9ae5aa06418cd775584320c72bbaac21906335dd1610c8319a8e0b086418e1e6450e510c70eaa4c720863331c96390431acce52a48218c777558e410c672392c720863711c963904319aeeab1c8218e577558e410c763b92c720863351c96390431d88e4b1c8218cc47258e410c66a382c720863555d64390431caacb21c8218f165490e410c72ab2a872086335dda3290431d8cc51948218cd5760ca410c6caba06520863599ca54504318ece
  | 21 => 0x62fbb2a629a83531c95314d41ab0e0a98a6a0c6f725805350636392c029a83391c96190d418deeca90a4a0d4c7354852506b4382a42928317dcd60149418b8e6b00a4a0cd473586425076331cc5a0a83b158e62d0541d8cc6b1682a0d9673d4641506d3396a320a831edd95014141ab0e6a80a0a0d68725405050637b92c6282831b1c963141418bee6b10a0a0c5c7358850506ab39e8228283599cb4114141ae2e1a08a0a0e4e6398a5410726b1cc52a0839398d6295041c9ac6b14a820d4e72d4e531062fbb2a6298839394e62d0c41c9aa73168620e565398743106a739ea5290831bdd95214841c9cc72968420e4e6354b4210733294c3a1083a358d62d044187aed2a48220c757695241106cab9ca8a0883695ca5450441b4ae5a1a8220d9573d094110637b92c7280831b1c963940418bee6b14a020c5c7358a5010727b1ec4a80839318f6254041c9ec6312a020e4c63189501072a31c82a80839918a4154041ae4e120aa020e5463505501073231282a80835c1c141540418f6eca80a020e566358754cc6b2392c3aa6631bdc960953318d8e4b04a998c3f7655054cc716aa2c42a6639398e6215331c5cc8b10a998e4e6358854cc72b31ac22a6639998961153319c8e4b0c8798e365458443cc61fba2c1296630f1d16094b318deeca90a598e2d6454852cc70eaa4c7a16638d95161d0b31c6aa8b0e8598cd47158e42cc70eaa4c7a0e638b95162d0731c5aa8b168398d667215241cc672392c720e631d9da5450731a6ced2a28398e367695141cc6b3390a8a0e638d95060507318dce4322a198c6d7219150cc63a3b282a86631edd95014331a98e4b1ea918e5563987548c637b92c12a4631b1c9609523187eecaa0a918e2d54588548c726b1cc42a4638b9916215231caac7308a918e6662984548c732b14c22a4638b95162d0e31c5aa8b168718e3554987438c6a7390a921c63331c96190e318bced2a28718d1e76951438c70f3b4a8a1c63539c85450e31c3ca83028718c3f74582528c61e3a2c1294631bdd95214a31c5ac8a90a518e1e5458f428c70eaa2c7a14638d55261d0a319a8e6b0c8518ccc7258e418c70f2a2c620c631b9c864542318dae4322a118c5c7650d508c63dbb2a0284631b9ca60d51318dae5306a898e4d6398a544c726b1ac52a263999896195131ccac4b0ca898e4f63189544c732316c2aa2639ad8b6055131cd0c5b02a898e3b64181544c72db18c0aa2639ad886055131cd0c4302a898e7361181544c61fbb2a82a2634e1c154151318dee4b00a898c6c72580544c6373acc5a1a631b1d562d0d31c6ea8b0e8698e1e6550c434c6b5b82a9a92635a1c154d4931c5ec9326a498d4d73193524c6b2b88c9a92631b5db43d4931acce3a1ea498d6571d0f524c786a1887a92634b9d360d4931a5ae9b06a498d4
  | 22 => 0x87995896195043d4ac4b0e8621c3d769524310e2ebb4a921887655c65450c43acce5a8ca221c77765445110e37b92c3280871b1c96194043ab4e121aa021d587050d5010f33b16c2a808799d886154043cc8c430aa021e56431855010f2aa18c2a80871edd95014043a9ce5a9ca7a0d4d72d4e53d0637b92c129e831b1c96094f41a3ce9b14a7a0d577158a53d0726b10c529e83555c46294f41a9ee4b0ca7a0d4c7258653d06aab8ec129e83471d16094f41a9ee4b04a7a0d4c7258253d06abb8ac129e83479d06094f41a9ce5322a7a0d4d7299153d068f3a4c4a9e8355dc56254f41c9ac4312a7a0d4f7258553d06a6392c2a9e8356dc16154f41ab0e0b0aa7a0d1c7458153d06a7b92c0a9e83531c96054f41aaee2b02a7a0c5f7654c53d0726a9cc429e839354d6214f418daeb31687a0e4e5398b43d0726a9cc5a1e831bdd562d0f41c9ca6b1687a0e4d5358b43d072aa9cc3a1e839594d61d0f41caca730887a0d4e73d4a52d06a6b9ea52968317dcd6094b418b8e6b04a5a0d2e74d8e52d06b3b8ac7296839358c6394b41acae231ca5a0c6d76d0e52d06b338e8729683595c74394b41acce221ca5a0d657110e52d06b2b8ec1296834b1d16094b41a9ee6b04a5a0d4c7358252d06b3b8ac1296834b9d06094b418dceda9aa5a0c6e7614d52d06a739cc8a9683535ce6454b41a5ce931aa5a0d677158d52d0726b18c6a96831b9db4354b41acce3a1aa5a0d6571d0d52d0786a1886a968353dcd6154b41a98e6b0aa5a0d6b7058552d06b4382c2a96834b1d16054b41a9ee6b02a5a0d4c7358152d06b3b8ac0a9683175da5314b418beeca98a5a0c6f7654852d072731aa4296839358d5214b418baed29e85a0c5f7654f42d072b29cc3a16839554e61d0b41caca6b0e85a0e555358742d0733292c3a16839394e62d4341c9aa7316a1a0e4e5358b50d0726a9ac5a86839398e52d4341c9ac7296a1a0e4e6354b50d0726b1aa5a86831bdc963943418d8e4b1ca1a0c5f7358a50d062e39ac528683175da53143418beeca98a1a0e4e5398850d0726a9cc4286839394d6214341c9aa6b10a1a0c6d7694850d072731ca4286839358e52143418deeca90a1a0e4e6354850d0726b1aa4286831edd950143418dee4b04a720c6c725825390733b10c2a9c83991886154e418beeca98a720d4c7254c5390726a9ac429c83531c95390e419c8e4b0c8720d4c7254d439062fb9ac129483171cd6094a41caec630aa520e54631855290637bb2a429483531cd5214a41c9ac6a90a520cd473586429070eb2cc7a0c838759563d0641c5acb3168320e2d6558b4190746b1ac5a0c839559663d0641caacab1e8320e656598b419076331cc5a0c83b158e62d0641ccacab168320ec66358b41906ab39e8328483599cb4194241ae2e1a0ca120c7b765405090
  | 23 => 0xc001000000000200a0028010006004000003c00400000500100100060000020002001003000800a003002000c00200800200040160000028084000001000000c01e0050038024000000002800c00000600300040000050010000000001000005c00400a005800000400300b00000080000030000000014002800801000900a002000600c0008000000000001801c00c002003800c01800000200040000070048004006006001004c00400000080000040010038008006000003000000a000002000800600a00a001c000000000000401a01c0020028006000000000400c0000000010000000000000000e0000000000006002001801801e0010018080004000000002c00000100000140000110000014002002002800c034005003003400000500080040080010010020000000002000000c001000800004e001003000000c00300a800400c00d0000000006019000000c00801200400040000040060018010000000800800e00000000600060000060000002001004800400200000180040040080000004010001003001001000200300100380010058000000006000001401400d00200000240030008010018001000000c00e00c00600000000050008000000001000000400800b005800c004006000800800400400500140000060008014010000000007801e001003000000000000280140000000088018040001000802401a000000801000c006000000c00600000480ac008000000003c01e004005800400000000200000020010048000023599cb5194743acae5a8ca3a1c6f7258251d0e36392c128e874d9d36294743aaee6b14a3a1d557318a51d0f32b10c528e87555cf6094743a68e8b04a3a1d577358251d0eb3b92c128e87591c96094743a6ce8304a3a1d667299151d0eb2b94c8a8e8759dc96354743ac8e4b1aa3a1d737058d51d0eb8382c6a8e874d9d26254743aaee6b12a3a1e656218951d0e9a3a2c0a8e8755dcd6054743acee4b02a3a1d647258151d0e36bb4a428e871bdd952147438eeeca88a3a1e666254451d0f32b12a228e879998a51d4343ccac528ea1a1e666254750d0f32b12a3a86871bdc961943438d8e4b0ca1a1c757694450d0f33314a2286879958a51143438eeeca88a1a1e666254450d0f32b12a2286871edd95014343c6acb30e8721e35655874390f52b12c3a1c879559661d0e43d8cc530e8721e55655874390f63312c3a1c871bdc960946438d8e4b04a321c77765445190eb2392a228c87995895114643aace3a1ca121d5970d0e5090e3dbb2a028487b198a61d0d43d8cc4b0e86a1d9671d4e4350e3bbb2a228a87591c95114543ae0e0a88a2a1c6f725805150e36392c028a871edd95014143ae0e2a80a0a1d5671d0c5050eacb8686282871bdc961141438d8e4b08a0a1e66629865410f33312c32a
  | 24 => 0x140000000018014000002001808c01e0020048000004002002800000000a0098020000003000800000a00b02c000001c004003803c0020000000008008004001002800600c01000140000010048008008001000002000000d000800c016006002800001a00500400100200070008000002000000001c00a000002005c0000080008088000000008802c00400400300040080000040014000006001802c000009001800800200a000800002400000180000060080018014050001006003c0120000010018010007000000401c0050000018004002004007000c009027000401e000000801c072007002001c008000000002c012001000000000200a0058004016004001000c000000012001800a007008000000000100100000020070000000022000002002800a001001800c01c000000801c0000000008008006028005801400a00600300200000030040000014003004001000403400000480080060040020006000000000002800200080080080010008034014001007801000602b0030000000000000800000400000b000801a00f000000000200000200080000020010000000001005000002a000000017c00400200080100020010008014036005003800c026009002000000c003000000000a0080008000010002000001000e00600000080000010068004000015000800000a0000008018002005000000000a0000008040000014000000001c0020008018000000017000800a00100000000780010018044000000009808000001100000040040050018000008001000800000e0000028004000001012000001e00a0050000008000007001c0000020018008010001002000407601200100c00320090008000000000000800000001f009800400800000d001000000300000140000210008000004009014800000e00200380080120010000004000000000000401800200b0000000001000802400a001003003400602202200100040060048004002000002000000200900200340120140068004000024000000000a0000020004000000005804003600d000800c002000000000800201500c000400200000880140000010030000036000000000000801100d000000000100d800c02a001003000400200900680240080020028010000004001800c00200c004804400600100280040000130008004002000006003000e000001005c0060030048008000004003003400c000004806003800600080480000000000004000003000001c006000000000000200101600c0002003000800000400d00000040000020000008000008001800400800000200000020060020000028000005002c00000100000080020000030004012000001002800e015003000c00a002004002000a00100a0004006005003801c0020010000000004008003005c0
  | 25 => 0x8b40006ef3a365fd3cc0005f58001be60002e51d4e0ea47804287e40006737172c880008eb000000000090f41800006a06e280000000710000b580014a0b6371f14c0000633ec280000009813c8001400000200080000090050000008002000803800400c000002400c0000028018002000004801000601300b8000000012003800000200900c00140020000018004056031006000800200c00000f0000009003809800000400000000020010048004046009000000400e003000000400000100000400000130038004002000008005c006000000004000a003001000401a00200100000040000088010004000002000001e00200180000ba010006000001e01200000c000600a0088010006005001800000600000a000002600a00400080000110008000004025002000000c0000000034004008009005000000b009000c00602e0010000000001003801000000b005801c0020160198000018002019000800000600080000020010030008002004000000001800100a80040080050248000002001004000c05000a000002001000000000000000010000010000000000000800201000400080000010038048008008001000003200300000180000010000000002006002001400800f000000400c00100500580260010000004004000004801800a000007000c0080020008008014006000001000000100100240000050000004004005001800c00a009001800401200d0000000002005000005401200500080200000060058000000002000000001c01b000000000800a000000400600b0000010000001001800400600a00080000000210020008002000000001c00a009002800400000000080500180010000010002001001000400000000100000060030000018002029000806c00000100080080020000008000000001000000c00a0360008000012004004001c0020010010000072002000001c000009000801400000d0038014002000000000400000b003002400a000008000002800900000000000020070034000007000001000000b00100180000000138040000002001000800e004001802c000003002800c006006000000c00a00200200000000110048014000001000800c0000000018000010000001800401a001003801c000002000803800605f008800000400700180dc0000000000000004000000002c00c00400080b400200000b803800a0010070010008019008001000000000100000040060008000004005000000400c002000800400a0080018000000001001000c048000001000000600100f003c006006000800800201200180080460000008000000002000000c004006000800c000003001800002e0000088018010000000000000000200080040060000000028000012001803c02000c000800000c000002000401c0010
  | 26 => 0xaff79192780000000001c6a9760000a927300000000864000000c9d00000000000005a4b03591c00059eebf20b1c217460000172a4d00036adbb0cee0002ed4f8a0000000000f2133b09343900000000003a4025e0005e5c000db51afba80000b1a9b603b39f8c100003532ceacde667bc77a8c00000000000017b0d144c77ba40006bc5780000404123000000000000036b9e88e567ba648000119bb57000283564076204f8e05b948d012e35482b48f600003100000002d791312c25b67662225a0b28000000017aa0003549abd8431d879ab5a936a6caadf221c00024c2708000000bca1c500000000783d50d8400075ff2c0000000c368000000a5600022e92d87e489a38e416489a000000171325400008c933c00000040e1927dd4000000244c00052828701025d8f0f0779f614fae81069924d665e765fd00004ab00077b08e83e20004b1ac248528d2799b8fc0008360000000b3c1dd62f8000f990002f41d93743000000378d9b95c83e3c0016ed8fe3c1873101c4f467c0343826b3c73027920000484f680000000006aaaac5b2aede248a30041e2506f9240b8b282f3209fd9c32000494b710ce39ac2aa22918f400000035880d70000000000000000000000049e00023128283d3d3b05fa0480009d336288311db373a35afa8000802e000df8b60d3220608006e90001150f489d4ebd20aadd20001de5d263242dcf0233680000007cd17000000002a30000001b542a71528000da400027ab4da00002d151079054800020800005280003625575292c684761b32000b880001be40006a11418001cde5b4752a764848ec400019399a270e000000175c00000000012319467148b20fd3301000344c0f30004dba09a00000000001540006150000000000000794ded160b46043d80e8b500000db95c44ea639aee0f3832040976e995fe32e496848191a989a039111b837062f07f210172c03e468c6d59ef0705f9ab30cc000019920e46431c8000000069e4b1059229e00067400000006468b8a910001e451c60002a41e4c07e0420024642a2372935f82a800000000000002582a9302e096da76258001ace0f05489614c6c501588dfb40000000000be000000000000003da2f1000199c00000000000000000002b7b09c000befde3b3003d80000e9c00185a0000000034777cf4376400000000011eab0c000d2f1490000d1c3650d12fa601853c75d234387eeae5e11c5d43a0b171791116204543a563a9e4b81736535b434000049337d8f1423f06a04a1a6373f8000000000b79800000161e272000000199a62947d141c0007348d562dde8000000000014ab0004f9382af5caeff738e6c000a1f800000000000056e8000000000086cfbcf7a1470b9a1284560bc13c2c9d9605d62cba54cb8031e0000000c4f00004b6fd519659607e0
  | 27 => 0xc0000006266c99f0114971300016ca000ae80000000efa00004c40002d8e570001a018470006d88001aa653ee9a5de40006ff6a4bcedb8641350d2d414bd5470002ce9c4053cb4ba891bac00046200015f2e52c7d96b2000a772a313b091c73a37da6401ae84413da4ddd5e34b1f329e0420e8d0798400000b742b200009a4d9e251c3ec00000019f279c00004f8003b3c25a5260a6000119800042d80003a4de185696fecf605e000382eb6e22810b824ee1f6332a692e4c6100000026451b00006f7a34b3f4000667b0f8000e166e98001e2a70800028189d2dbc0002384000161000061400000026c00000000000000001793b065a3b64fbfc0004c5218c53658c3cf80018c6c4e0da288346894f04a0f5dbf0742a360f8c000126121aee40002883d480000000000000000207cb22ed15f000000000000002f20002f100006f89b133e0000fc00000fe8000b0e000753a0ec00011b01312422fecf60000c35b6879423d8c54b547484a221d1c54dd000020e818ed7b6f0ac65278ba5000237e03800077c0000000ec3000268800061c0000000d1e00068c03790180005a84001e60b6a33cacad8063345c90000000792a52c000fb40000003a690687de2c00104cfac704ba80281c200057a9af2bd65d886d8950a2e00028c95f48100000668000ea5c200000e780cb8464e0800061e00003a79ace6214a00000edd0e156c4192be00000060e0bc800000071c19955088114160381b76e4e475400112e5097279644f419256a7aa806549d9d9c525c4cec2b62400d9d960d79598b4c8fdcb14034000a8aef595504e99a04653e8b5d0de87d084b3c4c568ca455e8ec10cc62a6ea07a4446b6d633119da1a09ac8bb61c5ead76026a7a4a54af2b80373c259b7136409cc5560ba55582a03c295a3680fcc0945a505573698d8ed605282254335c710909592a0b2ad0388a44647dcbd8ac9463e90550494d0d3a000085150577796a3aaaa490a45b204d1d3845cdc14da0e9400028e25240000eb3b246f860e9283933f4969d814cfd0000001304a5f8900000eaf37500000017b44aaf64224487e9595a96c5800042d75894b864c1ca0fd14197c605bdaa316d6f05ac0001decef06c5c63c0004be0000000001492000000043148e0000000000d750d4c9a0000b61b840000c6dd6e4060e10dd8cdb00034d00011a6b850001ca038034c1a99c919749106c680005f81804c392216c4bf09d236a5bee13e487000062c8e765604acc60f116d9a4d24841bc6d20a5499429c000019a76c000000186400000009c162459687f0d2af8134b153c773a4db0b7842659b788e2b268000b5c000878419b30c840055eefd8be0000006d32db3034a6668100019da7db74925058348920002771836afb5138d3828298fbaeba551a20728000e6840e9f91fd9c35354
  | 28 => 0xe0e500026640009380000288d580002ea1d01c1c000000000134dd630110eacdc80000461781b34375f9380009524e075098c4c02a48256352800071b8000000000d590f51da4eb1bcd71a800078c92d0e70000358dda0000000c96911d3f11654567cf96512540008ac3c8c1ad0dac0c70f89d800000001dc4fc00000019625e0000da544980004b7af5fa711c8f70dc900003455f00005a44000b0465b0000e8cc236e8e8788d519f998dc500006855a68001b7f0b00003668000000b0a0000000000db658a36e1956e7c76d80003aa0006d0ad4de4d0002dd86e5b500000f40000be68c20002fd0c6800000032600008228002643a0ca1db0d5f4688404400000002d200000000006aaeaa000128c84c00041280000000000002c6393c824c910458406cc86970001b7e00023bb4560000005c780180000003a78589aa2eeb58df6bca1822416c9ec8ea300000000017a2000000189bbbc0006529c2400000074cc0016f1a5e0000bbc000e1760f1a815ccc5c14d2751c0a6283c0a8717740003282650000f1c53023d418a8b6119aeac26ea1760400000000001733a61e980003462c3be2400034a0000000ee03cb6eb5a6b21421a0000000c8a5c64001082113000029de12000000357d7c3cf000000000000000000001b38c96723390c2f0731bb8848565c03552b0000c1ee1e2bc8001c1bdee000301800000037e90f40000005920dfdbea000656acf800031cbf98e1d54828c5d517e51caa570b6ef3c9781b341e00000006ad00000ad4d800005361c411e0000000c29b0625512940003c6000680ae833ab143000190c412744d168000000000076bbe30be7190fba4e8c98ed76eba38d0f24350870000000bc3254679e0004e5409935927ac1c8001f3d5f7a1b4a12e011e688b1182c3e81cc05000079a2da9cbc69d205298ce2353828d8a20903125cf617c99365c03d4ac6dd502f887457838cc39ac6da347202321388e0c0005c603d100cd4e603b7080000006826cced22000000332800012c01c8000000a040002dcd73003cf9e82d9926f2152a34ee00000051d90bc263acf04915d52a40002c18db406837a0308374f2e0664bb9a1586c0656c90b0cf0432e1b714d78f676d2b71f71740bbc6803c58bba8e8d9e8000f425d343bb00b452ded0002dc000062b88200019ba00031c80000000003eadf4e0003fc4ed223124ed8c7859e34b4c00056d0000000bb4501b928a960001b20001bf60175b1400182b9982829ce0dd72de0e29f4000000059cb2652620004108b740006d6baf34fd07a8963a4adac3a231752303b03b27fc17a4000e78d3431b9ae4a280001d4a4ec314558000290cd91bf0082b91dbd41831e3821d0359cd2d2dac4175d0716721d400099260b00011733d9000211d17066230ed68c0000000002701a06f2947e
  | 29 => 0xf06ec26a25d1da8000000b9c0000000ce40000000d0c37468903fd18c5f48c3255b4657de76c370f4f2000000323c2cf96c8d40001af54de0801602971a620d8ccb8001e6c9e68002079584cc25f48000060e0400018000000000000000000c4c0000000870b54c32344e0000002abaac0000bfc6b9800000000063e1441426dc53d5993f69e9733408000b56bdb29f87803572c51d72dd88920000000001aea48deb298744429ae08f89adbc86615a70518c7627941957b082209724328f50c0e107031249a580000000000000d2d733851e8de0007989918000b7e5bc9e81248d7d7018d440003ed5d933140000002fa800191ac1980000000000002f08d20692d33ec82e9d2fab0c522b9958825fa1a50c65a446c25fb0f9cdaacdc03486fcdb2b9ebdb032071e6e4b34975fa1811a4b70ab015244a195a8bda7076169a82dce761106a38fd4eeaad54f88b944962197353bc14e869b47641a94966b420b01b449462d5785ea0f0ce830001c430fc000568ae2bdfed11eb40fe46ee00000018c769baf21de000196a34200021f14d4af88000878d0872c57b68fcdb8d9100000000d58dd0f787c05b87c933b81e573c00076aaca8000cb90a684618200001bc2218fac85a34c816d6c39a30003c00000225050683c360f4f768843af7f15d55e233c5c606e4cf76b59de52565fb984a246497a41a711d265bdd5c514276efd06aa4c35b041b260b2f820e82949188d975b4663eb6c999a40005c6c0009080004ce295fc889cb130a0611c1ed825c2bba5dd38412720882f6c4300004c000000069f0451ca00001053b640000001268000354c4907ce0900000f73be07f811bcd52f2800000000049f80015d61fc4f6024b70100000031b400000000036360004217a2ab8115f8c61350000000cf12b2a760042b0d58e1e671405a0000000002ac574ce51618e69e81936200000a5a63c1458c292824e3aeed13a3fe24f6b3956caffb904813d3a28163a1a89d76a6515716280ed4ba6026f9858ca5136edb840006470000e20000f0e012223ccaa3da424822c0009d70000000000a596f01cd165300065b8e0c00004e294ded400000015c0000000be25ad9d34dfc98e0000001242b8e41f8000000000245523d78c00000000012fc57700006acdd8000000188c0003c25fb81c40003975e56c7488c0003ad8fd065072dae5bd40478e8a748a93d7504cc0b8018d594f144edbc831d763ba993474ee14ed4801a0c6b8b289e0bbb95742f636b0c50c7abb06b70eb12dec3a59907d1a464b717a2ee19d4eb95e58001b2f00046a869c0000882ac83d8fd50004ee848811de4b2f213b9908000029c000000f2d0001d58000788241959844c7647a4aaccff500000038940001956b8833252042a69fe67fe8400000033a431a4d400005588aa28978280006b
  | 30 => 0x5a7e708a65819283023173835a10bdc50603f40000003b50001aba144772afe4d601d703d0000000bc962c00012bc9c36020000000c62000162c0009ab0282d217acb7b1fc3bc4f5abec3fcfc0cb388d731b5cfca6e8544eb336cfd7e6937ab0d6000a26000030c9a22d800024ccd8fbfe0000001a3c0000001e75ba46bb0002b1546ab134390d1d3a200002e8bda0000000000000d4835b6371e64e4205c325100056c0000001ab80003de49f1470000000762a7946ac9338000660000d36000000199c15e19f80010e939c75c05f80007c70000000b74000162fcbd66cdac10d80000000005602ec616a0000000838000f060000001146792000326dc6b0004de8abae0211249b00019760005ac00010eca023a580006a88d8c4a2a0895300014bab7c4d0c7245056d4b361750001e593d63cc5cee77200037b0ad80000000002619bbec0c04c598901c7869bf1b780000a25b840d9dcc3362154a521640e61dc0000f7cff000000039b8000e30000000020d000743072d49bb419a069041420000790c442b0c1412d9900a1e0e826837830a60000002e9800091d800262c0500005181825e0103c78f0000c2d0002fe996800046a30d2b213c6abb27dc0bc000a4a551800000038b0000001c42c61565800056a30c0578000024c4a15f0001b23485361a1b128acfe7650c2de6174d90200000b000011dafb92725f00001ddddeee324ab89b955a9885ee75ac1c400072e9a094c263dbe9a95bdd87d500000000006468000000000c380000001323b04252266b32c3d44f084f56cc49c50a0000f9b000000002057ac0e64e03615440003b80000000842000000000a0000608a800b400000036d4000a3a73c000000000003e19105e0ac614f8bb841a0000b3a63c000efc0002637e8e1a853c80000000001c7080517e9d21e480000000000602d80aa0000046a94c13a000000197dd32a163700cb53ad7f577139b4f16d451d398ba0000002d9f054ce14370191bc08ea82a4c494e581f6381eecf8a1ce0a9aa109c400060d0002209e364250002de8000a9f085a4309fa0005b3400000000000000000000001f70001a8400022d0b240000000b2000178d9ad42a97f0000aec36394f44de31c4e29ba989e69f00020b800076039baad400052c18e9240e16d77180076d9ae8ce2c81f0851ad1211600009ec8dc35ba6c8a3e6d3000188141066a24f8001a4aee404fde1e9d0b4c0151ae167633627780c5d7c33364898d5c841f851b1e3d8d60000000001506807ee387d9d6c4f8673000003678e4dc2732c16825c1900006e28a802180015ace3c47c38ac61c74700000005f28af418b4f1abc2c173a000000048a569198de7200017e800000000034c30c4c3e4275710cff52e704206983800000048c2e4ce46293000129e93a4f32a40efd3746e711
  | 31 => 0x74e9f00006255b04001500dec7671d0d9b0e0b24cbb51040c2f120556d50cc5238eebe90de4c63d2957963c5f739eae056ce3075df74dcb4f8a971320229440742918c4943c97b4e81ba0e30e135efab050d00000ed29e9e179f80284a1c0003244ad95fcf268b044f23e5ae0735ba875fc56e3c186700004c060a1331028ba07681cf91c11de00000029c4ab400051c0000000000745850ae38cec73100000000000000000000f0121f17c8000d1500fb8dcff293000026980005ff00004b8000000000004c2e20000002f90fe100019bba14e71b75000000000000031f8f20f4c99e511183020c7120d180007d2b05262a26102119f3f740016dce093e5400000088500000000001bd8cf1300000a8e32280018ac56d3838f54fc80005198000fa97e32a9937c42250b597ec2c0008b314c99c57a93310000340560d12e1ec000aec2d10aca4340000d98000001a61000000366cb3e0000002ca400061700000001923953a08000000a5200000018cad542d48000000d3a21727d490e0004638001e275840001a54000c7e4993174fcc0006ac3c7a30e000228352da0a000228a0ac964b35a739aef76e3868be0000daf12f8000000444c810000cbc6b20003ddb49853090639388c4440cde49060156d2df129ab2f4e3e52425fa002e52320d9415edb04d40404a93177f5f871c84056de000682257de1581603ec00090427d0002e50000b68388131c00000000000000000006742708000f0457b2908722bc8e3522d475a0005c81d941ed02e404c8dde300621429999138a010bb8000ae62845533d0400079a0000e30000368000000068047e00025f0fd49c63a44000b9d2438002d8400055153720e06e0c5300000000004cd02640000000001dbc4540164316441e00c7c0d92727a7c0000cf485929c000bf80000a8414c7b3428200408a13447409920000000002b787723092e239bae4c2f33b1e67dd9d30803b8000000b4c80000000000000000facca40004b75b380005ee00c37e83d60000c705001e209c0003bf90414410002b7000000032d6afceecdf4792b951a820000000000e227ef800305c9bc0002229f7460addf16a21a8f94d285089c7e0000000003ad59fe15132944940008b080010e915a2741f000006406f75bbdae92335604508b11a7dbbf22900000fe49ad4626bd50e7f700036047a0000000268a0000007920000000b15891400122400004c8001ceee4c0eb000094c000117a589762d965a0bbdafb2418313a788da26594b38ee8ff626c5f685bfe3a5b4c8e610de2f6932eda9897a0e0700000013d3b150001f4894a91451900015c80002e5c7ec9e376344800000000b00000e50e3acf73f262d010c0195a28000f7c0f2eb90d6178fafa8e68b40b7e7e83f1d8b77040007860000ba400068e000187685c58080009
  | 32 => 0x8071550083bbcd5626d0001f3000001a43ec000b630004cda7d0a626e372a8001a29000000232800000000000017e9a6b04180000000006f83c21cb80000003cbb78acf25b240007fec0113d0001a5499dc1680008fa00048eac3800e000000159d8e2000000000097a0040000001352000458a075a4095852c000000095c402c00096a0007140000a9e5dd80006ba55a2910002bb3bb60000001dfd80f76f094aa4c24880d2a19f11e3e28a63faa59182e972e687880009166a831800002381c6808cabe6deb6fb788912414033d6891c8c0b4c1c70d06e00000b1e7670000061eb66400000000031192a2ef500000000006562ad6c137126c694aced06c6e5e3bd103c8be637d8cdbc8ffeecd00000000006a559f9b98652bf1ec767bca0884f00000013e02cc5ef2cfa2b3d442ca891d752745239a6354420005c8a464000a3e2ca0001516afd50c9d0376f246312c00000061b0002a155e3da05be1db8c0e8bb0003b84d820000001691d2cf4d6b7800190600000025c813d8023d780000000004fd8000000a2e3cf22b837c5afe47ae8800017200000009f4000000083386868b71da3643051bd47a1edc48a25aaf48000af466e000000154e08e0002ff400011cc50cc1800000070e0000678e665aa80002a03180001c307b8000000000000000076e000000040400000018aaa4000018508a641d5d98b8775e44e264a4785f6d941e745f53a721c10d16ee2060b4d4f2d70b100aa2e11e96000c1196d99160008810002c600002e414e8b680000000002c0d3aa74c4080f45114234403b4b2940642367800123d000797fb7c32edb244436136ca0001b000010c46eb2dca601737000000000021e3a629f2ba8000000250988800074fe120b097ce86108b8c0d9ce6cc6c52e6b2ba0b33f474cd3727e7d7ece880000000002c09534c896c20000000d9f7228f91d667e168bc965e4000000014ec00065d4b483cee0aef431219e0db3e7000028dcad649d80016c5c8000067d00000003bb00000000000003d8000154a0004c24b3c3be0006959e700002d2000000153ab00000164c4a25110340000e14c293aee0001d6999a7229a1a1c0001784000ba24f137d0cd4a2644700000000008670cd0000000bd40c1184e00064f13200006e40006bd0000ccd00000000000000000001862080000000000000041c00009007b0f3c61e2b10cd80000001bd8c304b36ae30d551ab24e43b9fd22126315db218d2c0033d2052c32c03f6c780007d85e70000d7435a000522308c000d288000aa11b6b408001c69bb89048002520d6a0000001b18f2200067e079914c4960f2b3257488eeb3aa315098000000000119a7ff8002c6a000ce500000018b40006c58d9c000f3e42b0ef8c242fe40203e8000e724cd332ca8f47f0000c406f20ca0a400015646bf3
  | 33 => 0x5a21bb966aeab6ffac69424d6c1b95a2080aed3716af0530ce8206921a40005c58000000000ef24019ee56a3000387baa400089eda14000fc300006d2bcdb13a24d0f8000000bc5800000000057e00024175de000000252c00000026d39ed83200057a000000026ff6380001ac0001752939240a8a0000000866a8100029634aa7c8538193ad6c4280000001c24d0b1be8000000c790000000000073dc18f953fa205000287a00063a63794cc990000000000067ab384793990000747b5900000c511c524e3f1e5400011c800042c9ff301b19036cc443cd8001e0e0006630001d4c06c446abde000b9b4e6d8580004af67a9fb78542ff69800006080000000000a528cbd88a4bdc146585070000c42ec05c580000000003011b502544db5cd00019c21424e7281433a90883bdb60bd4dcc4711b258674d55be9bf0d147362278ebd3503b10c5b64291848d35980005d09e449ab3cc000000768000172a45b5d19b6e000cf95de9500dc79fe2162db1b8cb4d0a700008ecaaf00000017e20e95508000000e4805e922f0fa96c00036215a60004d442d7e4792c0000e8000000000019addf63cb1328000fde64bde0c0000000002b90d144929b34edc648000000779832d713000596a50da5b4ff00000017320005c380011440000003ac83109012ab3cac000cc44ab338c2e877252d80004827331fe8000000b0adf0894c0007163a5e2f5b1c1278163114b5c0000000e4003a000000000012ab080e9b9f54d24173f2ac4387200f4ddb30400056c425ba70170cae00024ade514d9591b07643e2a9176a05123849b31af390f82dcb1ee96680000000002c9f6be6e6b2f01f4c890000000ac89f8eac00000011b300069cb653673d244024a9902acaa58a69cdb9a7983a9145566e7594d2b8681bec776e00ce4f89d570f9852578851b40519515f37fd47ea80195e67f00007c88161b22d2429000071444cba240005610000245accd4833f0287a4e94e4551511851de63990988d5481f613000191622a8001b7501586b71d33fa9ee5210718001af811d2e1ab1d11c1d03377a6c34c1a1aef2e5c3220000003618780872bf59724000c8c66a227d20f7f180000002c000020f00000000004e78c948021c9782ea54000e8e1dbac4f7ba7c0f002c5d661b645eac0002665e376d0d5c490b334bb09784a4491f089fc98a03a13f883a92e071e07f854cc788da2793d108b80000002534e94e7931d7820f3d8847442f4c00046942880000000000000f14e7d1ee5f90f6c0009f700013992377f2e90ba8097c045f86800000064c8e85665b300002938000e3300e2c32bb959200000000000006228002a2583e5980000001da3f34000184b30a4400d239e800000000f35915da75815cb8542c696d1c48000574d0a7941761cacc9a00000001b80001cc1841
  | 34 => 0xd0ca2080009eb13becd34078650a1a02741f327d6579150c0b7acffb8ed2f8a4a000000066b06300f65c13600000ea83ca54d908c00076710331507324577583890fc441937299a009236a19d00000000000000000000ca6000000000012764a8b1c0000003482d014c88be6a182d00000000003a89e5bbc0f11a554f9c8a5754251c00000023d15d000000028000000000002b800000000003fd37f00000004240000766000269a08ed960004b896b60000720d79469942c4728c2098f93000000297caf0037c5900014620000000000000000072660a0000003a32ffc0000000003ba13b578c0003674ea273929b112cab84360002d29e965c6c77f6f9a3e4d768882783a8059f319d092d0c129f53b2445f00000000005eeb566d72ed80aecb30e7ac0f658ca34ceb8d1e14db96f295a55fc00037c0044000bac000044469a1083ff0000dcf7ec5a89cdedddb07beb928a4880ab5815d7d82400068b00002f4bc82b40001e6410580017300005c54f98a59308f2c00032499b3e9409c9009b120000000000e7cad40ce03ea0003d34703043e949c90003b993f8000397a2f0000bd259a19912124e348f8001ac2ca0480c20e90096616b020560d373157a6c1884b00e2698104d25cf69eb7e542a7cb5a18dd19f65ce2853037443b569e693e42d43661a0d1d1829c255aae98d6421322622d2642667a68825e4ecc2772a515395ae4a84642f3a1366cbf3610c86c4c5e5561814efc63cc1392d00520462458fd947238555481c325c4eb4c6183ae885ed56c98b0a100826f3847831e6113e1adddc4432734328a1684954397303c0000006dba174b3a0000000000eb800000010ec4e000036d800002dae900021c01986762ff3934c4300000009f15a0c018002e355c60005d34206000ebf4059e3e26ca6d0e3ba00b426c9afd82b8f2f15c24d0c88d3cc9771b678e000ceb51521e8ac425a00660d4000d5a5e728b0e659ea6512dfcad40006a6a17909ce84693e7a3c820bb315a021af2d1b79d37a15e74300cc8c4de2e5493ba11e5e69c023ca5f7cc904ce51e25e82ecafc5d9e7101c7c4057a6d2c51e1f54d1eb851367e2eb490ad9b2000000104804a0001431bcc000000000000077000000006840009ca4d086a40000001b597d12550001a20000e4aa1807f7cdc0006d8e04814c0840005ec96f0bb2181bb5a1b8000dd1000057a29d53800004f1530c1100036c0c69d780000000b5a000174800133700005c6ae400000027f297565e9a1d75e33a57eaf7619b764ca60005e006c4a407bf3f8282d1ee130da30000fdc68700000008863f700029d5d487300e21aa0000ab427d8fc4cb818438d8000ffde1b58e5f510ae929f3aaa65e20e0c573800123458e4cabc680003a801b819ddf4ae55ef6c7cdd2d648730000d1a4561668424bb94b0
  | 35 => 0x29ed57c00024c29fc7910000a79e544ae0004f705bc000c2bc6b00017428a700000014cee0200000000005e48100000e540c679c2e7d59ae3d0000db06340a001e80013c090300000508f8e593d0d06895410d10c179998ea206948000000b306ab0000dcbaae6663cb877ab9d3c4a895864f3f6429b111e05033256bb6b1e0ac5d66ef6000e734ea6594ba78ccc840000000ca84f6e4c76b269220f9fd0000a48c3c4f5800000030e4000b7a157000365d94e00002b1ef13788234fb36e9b9cf433e366917caf460002e19a2e0004ba351ef4ee0f5eb8001904e360002d69bbac7600000000007870000e580000003ad3b05cbee710278000000da34df000112ab0d877195c0000006b016cd1d300022f2dc8000000065f8b0000a8f1589b69c6246d6deac975b670300030b85c43e17341d07cb651e763319cce035a36e71f46608ff6e42f309ba803f5e1af956e6131af025f5545c619c0fe81849a77478000a98098481356d42091b13f975d77cc306d1000185858177c8000000e5353b0f3c4fc00070e80000008b90002ae070fca91a320060006510002590f0a43c000000162400063ab1a5e3b0000002410fcd0475ae82297d005420190e4bbeb5e173b89d850a940812c1c984eed2111c9fe6b06f3a9b41b9c0845640000000072d00000019be0001d537a49b800000035180001c100011a0c64a881a0b850724e014ef1f77c66000328c34e0001312eab86000036978960a0a3a00061b86182ca90a5393b8d16f03372d14b47d0a9c38100000000004268e089e00f97691d5c00016800011200008ab75a32d0becc22000000000000000037f40000000002aa000029e1ce8e185163c438aa60c1263f03165bb583a7c65788b84b248e60c9b6003127351f120657f6cbc16aba78c3c55507c18660c0461371089d390b52030f9443ce03845d082de447a3483a35ae3d1ae3788000a5e1ff16f99342be8de29d3ab52d6c181a900082cc0524a01a8d1e20002813b0895c9112f78ba
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x661d4d40a44825846114d40a4682d8e63d4540a4683d8a62d4540a448258c6314540a44835886214540a4681d4c624c540c467318b514c540944825c4530c540944825cc510c540946829d5310c540946851c9310c540c46651c9310c540c44651c9310c54094687d49310c54094487149310c540c44639cb5148540944835c85108540946839d52108540946851cd2108540c46651cd2108540c44651cd210854094687d4d21085409448714d2108540a44825846194c40a44825846154c40a50805846154c40a448258c6394440a44835886294440a448258c6354440a508058c6354440a44835886254440a60805886254440a448154c624c440c4473189514c440944825c6530c440944825ce510c440944825d5310c440c1565dd1310c440945851c9310c440c47651c9310c440c45651c9310c44094487949310c44094487549310c440c44631c95148440944835ca5108440944835d52108440c2565dd12108440945851cd2108440c47651cd2108440c45651cd21084409448794d21084409448754d2108440a148654d5150040c147654d5150040e05531895150040c24765495150040e04635495150040a448258e519063094682dc5540c630946829d6410c630a1a85d906050d30d13741c14314530946851c9310c530d07541c9310c530d04541c9310c53094687d49310c530c44639cb5148530c46651cd2108530c44651cd2108530d07541cd2108530d04541cd2108530c25641c95114430c44631c95150430944825c7540c430944825d5410c430c44631c95148430925841d52108430864875952108430c47651cd2108430990815c04310030c46531c96190e10c44739496190a1094682dcd540c610946829d6430c610946829d5430c61094683dc95408610946839d64208610946839d54208610c46531c9610c210a4682d4c614c910a4683d48614c910c46651c5320c910c44651c5320c910d07541c5320c910d04541c5320c910a3285d906050510e136414c6050510e23641486050510946851c9310c510d07541c9310c510d04541c9310c51094687d49310c510946851cd2108510d07541cd2108510d04541cd210851094687d4d2108510c0d641c95314c10a448254c6150c10a44815c86354810c0d641cd5214810c44721c56314810a44835486150810a448254c614c810a4483548614c81090d841d5320c81084c87595320c810c47651c5320c810944825c5530c410944825cf540c410944825d5430c410951851c1430c410a4586148320c410b0584148320c410944835c55208410944835cb5408410944835d54208410961851c142084109458714c3208410a458614c3208410b058414c3208410990835c041100109a0825c04110010a448254e618c010a4682d94318c010a448354a6188010a4683d942188010
  | 1 => 0x1a8684dcc624c431a8584dcc624c4318c587d0c624c4318c4825d3654c4318c6829c3654c4318c6829c3644c431c1775dd1644c431cc072dc1644c431c53751c1644c431c93741c1644c431cc3721c1644c431cc0721c1644c4318c4865ca544c431ac080593624c4318c587990624c431a4585990624c431ac380590624c431ac080590624c431a8684dd4624c431a8584dd4624c431a4585dd0624c431a45859d0624c431c85741d0624c4318c687d50624c4318c587d50624c4318c687950624c4318c587950624c431e0554150624c431a47855c0624c431a87845c0624c431a84845c0624c431a45851c0624c431a86841c0624c431a85841c0624c431c867418b524c431c857418b524c431895841da524c431c467518b424c431c457518b424c431854865d6424c431c467518a424c431a8584188424c4318c687189604c431c4775189604c431c8774189604c431c8474189604c4318c4825d0604c4318c6861c93154031c87641c93154031c84641c931540318c687d8931540318c4871893154031c90641c13154031c86641c93114031c85641c931140318c48798931140318c4875893114031a448358a61d522194a809d5430ca21c44531c961d0d21c44531c96190d21c44721c563d50218c4835c86050421950805d5430c421945851c9430c4218e0805d9420c421b0584994320c421a4585d90320c421a4586d50320c421a858418c3288421a8684dc86348421a8584dc863484218c4865cf42484218c78718f42484218c58718f42484218c4835d365484218c6839c365484218c6839c36448421cc073dc16448421c63751c16448421ca3741c16448421cc3731c16448421cc0731c164484218c4865ce5448421ac08059363484218c5879906348421a45859906348421ac3805906348421ac0805906348421a8684dd46348421a8584dd46348421a4585dd06348421a45859d06348421c85741d063484218c687d5063484218c587d5063484218c68795063484218c5879506348421e05541506348421a47855c06348421a87845c06348421a84845c06348421a45851c06348421a86841c06348421a85841c06348421c867418f5348421c857418f53484218a5841da5348421a448654c5348421c467518f4348421c457518f43484218e280dda4348421864865d64348421c467518e43484218c58718c4348421a858418c43484218c68718d6048421c477518d6048421c877418d6048421c847418d60484218c4835d060484218c6861cd2154021c87641cd2154021c84641cd21540218c687d8d21540218c48718d2154021ca0641c12154021c86641cd2114021c85641cd21140218c48798d21140218c48758d2114021944825c6530c740944825ce510c740944825d5310c740944835ca5108740944835d52108740a4682d8
  | 2 => 0xca2480055044519bc228f4271e074c00870258821a741f088995429f85b1c61f1b205a44210000285b4ba280006e1813200198581506317c00144014324786a2f0866b800508ae0f0954121e8f9f46519a2a1be6582c141e83c0460460690898848e82d1ce48896158fa4a89e75c5d2e1ac6223a75000191b6710206084043022000c66a98f1e00059940000005b800001ba3f8ac800005c9b44e0a3449281c000480006c06618800858000014e000008ba0c8ee2664c000012c000006809a0001c5e8385708e03dc23a800301566e000398da0005a39000690a7000ba4690653000840000000065c3e7881e8f13e440a45f800914005680045162610a609012001d800000778c88100000000002140000000830000002840000000000d61a000459643782700118000b62fa36000a2001801d05c8c100152240008217a39069af5296863880689a1000e200000748c464578001ee790880007e1d8ec420d2759f60a800000f80015e72a3800000000280001400000768005a84e1c40e330006700035000061a8030007c80016158020000020a7a8523b8dc490fc68c4a0743a1c8420b5c0000362aa320bc00000ce2411c635860d0a03d8268222c8a9c80b87a1b2407f19979a340104c66d8a809fa7b1fe4d0b00022f7713000000000c2520005c1524393c001a6839744d8e00000000000001cc000b24089423057341908600001976648f23619e4e8480400000126000000301000020080004070100020070080414160001802060001c12090a0544a1403008100a0180c1a02000101a010a8047e09000000a090080800080881400010a80400090200408000000814040400406020880000020081c00000000018010200c0e0f0504c00090301000000082c0600020080e04030040604a508050c6154043c50631c14154041c60621c14154041c46631c961d5331a448258e61d5231a448158c52d0931c447314961d0931a448158c5290931c44731496190931c44731c562d50318c4825c46050c318d0805d832504318c4825cc6050431a8684dc4624c431a8584dc4624c4318c4865cb414c4318c58718b414c4318c4865cb434c43
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 27
  | 6 => 1098
  | 5 => 6068
  | 4 => 3921
  | 3 => 291
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
  | 6 => packedAt gbK6 (35670+((h/502+packedAt gbK6 (29646+(h % 502)*12) 12) % 2404)*12) 12
  | 5 => packedAt gbK5 (266032+((h/2532+packedAt gbK5 (230584+(h % 2532)*14) 14) % 9117)*14) 14
  | 4 => packedAt gbK4 (212370+((h/1557+packedAt gbK4 (192129+(h % 1557)*13) 13) % 6168)*13) 13
  | 3 => packedAt gbK3 (18432+((h/108+packedAt gbK3 (17460+(h % 108)*9) 9) % 427)*10) 10
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffffffffffffffe07fffffffffffffe1fffff
  | 1 => 0x1fc07f03f81fffff83e0f83e03f07ffe9323f
  | 2 => 0x1fff8003ffe07ffffc00ffc003ff83ff1c3c7
  | 3 => 0xfe0000003ffff81ffffff000003fffc1fe03f8
  | 4 => 0xffffffffc000001fffffffffffc00001fffc00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xc0450a00084104000c61184238b08420254db
  | 1 => 0x54a93146591ca28e581a86a3449546b4e9322d
  | 2 => 0xa930a26aaa287516ab410b690926d23971c346
  | 3 => 0x31a2c58d345141db35ada0421238e711be03b0
  | 4 => 0xc1c3060e3861861dc631cc739c008421dda800
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeaaaa880eaaaa880eaaaa880eaaaa880eaaaa880eaaaa880eaaaa880eaaaa880eaaaa880eaaaa880eaaaa880eaaaa880eaaaa880eaaaa880eaaaa880eaaaa880, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12823
namespace PEqualNP.Outside.L_meta_12823
open PEqualNP.Outside.L_meta_12823.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bgb_3_288 : Interval gbAtlas 3 288 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 291 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 (concat bgb_3_96 bgb_3_128))) (concat (concat bgb_3_160 bgb_3_192) (concat bgb_3_224 (concat bgb_3_256 bgb_3_288))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 5 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xeaaaa880a880a880eaaaa880a880a880eaaaa880a880a880eaaaa880a880a880eaaaa880a880a880eaaaa880a880a880eaaaa880a880a880eaaaa880a880a880
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,17,49)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,17,49)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3936921736 * 2 ^ 32 + 2862653440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12823.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,5]⟩,⟨.and,[2,4]⟩,⟨.and,[0,7]⟩,⟨.and,[3,6]⟩,⟨.or,[2,4]⟩,⟨.or,[8,9]⟩,⟨.and,[3,10]⟩,⟨.or,[6,12]⟩,⟨.and,[0,13]⟩,⟨.and,[7,11]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936921736 * 2 ^ 32 + 2862653440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936921736 * 2 ^ 32 + 2862653440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12823

open PEqualNP.Outside.L_meta_12823 in
theorem PEqualNP.Outside.L_meta_12823 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936921736 * 2 ^ 32 + 2862653440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936921736 * 2 ^ 32 + 2862653440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
