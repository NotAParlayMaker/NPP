import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12891.Model
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


end PEqualNP.Outside.L_meta_12891.Model

namespace PEqualNP.Outside.L_meta_12891
open PEqualNP.Outside.L_meta_12891.Model
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

def mirrorSteps : List Move := [swapRows 50]

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

end PEqualNP.Outside.L_meta_12891

namespace PEqualNP.Outside.L_meta_12891
open PEqualNP.Outside.L_meta_12891.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x247282b70007753b0ce0340d8099000bb00c40246122d23239b8f69f58085800052a000c9e0003120b80000420020442d11820cbff42fe42fd42fc42fe32fd32fc32ff41fe41fd41fc41ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xa41fc31483fe42907bc8520ff10a41fd21483da42907f08520ffa0241bf40483fc80907f50120dea0241fc40483fe60907f8c120fe98241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041be540827ca8107f55020beaa041bd540827aa8107f15020be2a041ff53082fea6107f94c20bf29841de53082bca6107f54c20bea9841dd53082baa6107f14c20be29841ff43083fc86107f50c20fe218417e52083fe84107f90820fea1041fc42083fe64107bcc820ff19041fd32083f864107b0c820ffa8841fe51082fca2107d94420bb28841fd51082faa2107d54420baa8841fc51083fe82107f90420fea0841fc41083fe62107f8c420fe98841fc31083fe42107f88420fe90841fc21082fca0107fd0020dfa0041fe40083fa80106f50020fe20041ff30083fc60107f4c020fe18041ff20083de40107f88020fd10041fd20083da40107e48020ffaa6217f54c43fca9885f95310feaa6217d54c43f8a9885f15310ffa96217f52c43fca5885f94b10fea96217d52c43f8a5885f14b10ffa1621fe42c43fa85887f10b10ff19621fd32c43f865887fd0710ff20e21fd41c43f883887fc8710ff10e21f621c43fa43887d48710fe10e21ff40c437e81887f90310fea0621bd40c43f881887fc8310ff10621fd20c43f841887fd5210bfaa421fe54842fca9086f952109f2a421fd54842faa9086f552109eaa421fc54842f8a9087fd4a10bfa9421fe52842fca5087f54a10bea9421fc52842f8a5087fd0a10ff21421fd42843f885087f8ca10fe99421fc32842faa3087fd0610ff20c21fd41843f883087fc8610ff10c21fd21843f843085f94210ffa0421bf40843fc81087e90210fea0421bd40843f281086e50210fe20421ff20843fc41087f48210fe10421ff10843ee21087ec4210ffaa2217f54443fca8885f95110feaa2217d54443f8a8885f15110ffa92217f52443fca4885f94910fea92217d52443f8a4885f14910ffa1221fe42443fa84887f10910ff19221fd32443f864887fd0510ff20a21fd41443f882887fc8510ff10a21f621443fa42887d48510fe10a21ff404437e80887f90110fd20221fd404437a80887e50110dca0221fc40443fe40887f88110fe90221fc20443fe20887ec4110ff08221f610443fea8085fd5010ff2a0217e540437ca8084f95010feaa0217d540437aa8084f55010fe2a0217c54043fea4085fd4810ff290217e52043dca4085b94810fea90217d52043daa4085b54810fe290217c52043fe84087f90810fea1021fc42043fc64087f4c810fe190217e51043fe82087f90410fea0821fc41043fe42087f88410fe90821fc21042fca0087fd0010dfa0021fe40043fa80086f50010fe20021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xe32d037a65a06f0cb40dfa8e81be51d037aa3a06f14740df90e81be21d037a43a06f08740beaa4813d54903fea5207f94a40bf29481fd52902faa5207f14a40ffa1481fe42903fa85207f10a40ff19481fd32903f865207fd4640ff28c817e51903faa3205f54640fe28c81ff41903fc83207f50640fe20c81ff21903fc43207f48640fe10c817e50903fe81206fd0240fda0481ff52502fea4a07f94940fea9281fc52502f8a4a07fd0940dfa1281fe425037c84a07f50940dea1281fc425037884a07f8c940fe99281fc32503fea2a05fd4540ff28a81fd51503f8a2a05f14540ffa0a81bf41503fc82a06f90540fea0a81bd41503f882a06f10540ff90a81fe21503fa42a07f08540ffa0281fb40503fc80a06f90140dfa9281be525037aa4a06f14940df19281bd325037864a06fd4540df28a81bd5150378a2a06fc8540df10a81bd215037842a06fd4140dda82817e541027ca8207fd4840ff290817e52103faa4205f54840fe29081ff42103fc84207f50840fe21081fe32103fa64207f0c840ffa8881fe51102fca2207f54440bea8881fc51103fe82207f90440fea0881fc41103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9905fd5320ff2a6417e54c83faa9905f55320fe2a6417c54c83fea7907f94f20bf29e41fd53c82faa7907f14f20be29e41ff43c83fc87907f50f20fe21e41ff42c83fc85907f50b20fe21641ff32c83fc65907b8cb20fe99641ed32c83f865907fd4720ff28e417e51c83faa3905f54720fe28e41ff41c83fc83907f50720fe20e41ff31c83fc63907f4c720fe18e41ff21c83de43907f88720fe90e41ed21c83f843907fd0320dfa0641fe40c83fa81906f50320fe20641ff30c83fea9105fd5220ff2a4417e548837ca9104f95220feaa4417d548837aa9104f55220fe2a4417c54883fea7105fd4e20ff29c417e53883faa7105f54e20fe29c41ff43883fc87107f50e20fe21c417d52883fe85107f90a20fea1441fc42883fe65107bcca20ff19441fd32883f865107b0ca20ffa8c41fe51882fca3107f54620bea8c41fc51883fe83107f90620fea0c41fc41883fe63107f8c620fe98c41fc31883fe43107f88620fe90c41fc21882fca1107fd0220dfa0441fe40883fa81106f50220fe20441ff30883fc61107fc8220f790441fb20883fea8905fd5120ff2a2417e54483faa8905f55120fe2a2417c54483fea6905fd4d20efa9a415f53483fca6905f94d20fea9a417d53483f8a6905f14d20ee29a415c53483fe86907f90d20fea1a41fc43483fe84907f90920fea1241fc42483fe64907f8c920f719241fd32483da64907f0c920ffa8a417f51483fca2907f54520fe28a417c51483fe82907f90520fea0a41fc41483fe62907f8c520fe98
  | 2 => 0x7fe8320efd0641fba0c83ff50907fca120df94241fea84837d50907f8a120ffd4941bfa9283fe52507faa4a0ff14941be29283ff42507fc84a0ff50941fe21283fe32507fa64a0ff0c941ffa0a83f741507fc82a0ef90541ffa82837f50507fca0a0ff54141fe282837c50506fca820ffd4841ff290837e52107dca420db94841fea90837d52107daa420db54841fe29083ff42107fc8420ef90841fea1083fc42107788420ff8c841fe99083fc32106fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f541107fea020ff94041bf28083fa50106f4a020ff54041bea8083f950106f2a020ff14041ffaa6437f54c87fca990df95321feaa6437d54c87f8a990df15321ffa9e43fe53c86fca790ff54f21bea9e43fc53c86f8a790ffd0f21ff21e43fd43c87f88790ffd0b21ff21643ee42c87fa8590fb50b21fe21643ff32c87de6590ff8cb21fe99643fc32c87d86590ffd0721ff20e43fd41c87f88390ffcc721ffa8643fe50c86fca190ff54321bea8643fc50c87fea910dfd5221ff2a4437e54887faa910df55221fe2a4437c54887fea710dfd4e21ff29c437e53887bca710d794e21fea9c437d53887baa710d754e21fe29c43ff43887fc8710ff50e21fe21c437d52887fe8510ff90a21fea1443fc42887fe6510ff8ca21fe99443fc32886fca310ffd0621ff20c43fd41887f88310ffcc621ff18c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121dfaa2433f54487fca890df95121feaa2437d54487f8a890df15121de2a2433c54487fea690dfd4d21ff29a437e53487faa690df54d21fe29a437c53487fe8690ff90d21fea1a43fc43487fe8490ff90921f721243fd42487da8490ff10921ff99243ef32487fc6490ff4c921fe19243ec32487fe8290ff90521fea0a43fc41487fe6290ff8c521fe98a43ff21487ee4290ff88521f710a43ff50486fea090ff94121fea8243fc50486f8a090ffd5021bfaa043fe54086fca810ff55021beaa043fc54086f8a810ffd4c21bfa9843fe53086fca610ff54c21bea9843fc53086f8a610ffd0c21ff21843fd43087f88610df94821ffa1043fe42087fa8410ff10821ff99043fe32087fa6410ff0c821bf28843ff41087fc8210ff50421fe20843ff31087fc6210ff4c421fe18843ff21087de4210ff88421fb10843fd21087da4210fd48421ffa8043fe50086fca010ff54021bea8043fc50087fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681bf42d03fc85a06f90b40fea1681bd42d03f885a06f10b40ff19681fd32d03f865a07fd4740ff28e817e51d03faa3a05f54740fe28e81ff41d037e83a07f90740df20e81fd41d037a83a07f10740de20e81ff21d03fc43a07f48740fe10e81bf52d037ca5a06f54b40de29681b
  | 3 => 0x10150060000c0020160400000c00a0780280900402c000000120080580e016004008000760000000000a00c0080003e0080880601204c0081200804004801012020010050000500200500801404804014000098010000bc04001000010010020000080082a01206c0182400a0240a80d050068010010940080000701a0141580000a0000001402a034018010280000080a00400402000000018010000000240000000e0900080100a00c02800000004018050100000100200002000806002020050010380340100200802c010080040000000f0000080300000a030018000000040400208201000002006004040020280340080004804c04812000014058080480040980c0000400880001c01ffea7a17f94f42bf29e85fd53d0afaa7a17f14f42ffa1e85ff51d0bfca3a15f94742fea8e857d51d0bf8a3a17fd4342ff286857e50d0bfaa1a15f54342fe286857d5490bfea7217f94e42bf29c85fd5390afaa7217f14e42ffa1c85fe4390afca5217fd0a42dfa1485ef4290bfea3217f94642bf28c85fd5190afaa3217f14642ffa8485fe5090afca1217f54242bea8485fc5090bfea6a15fd4d42ff29a85fd5350bf8a6a15f14d42ffa1a85fe4350bfa86a17fd0942f7a1285fe4250b7c84a17fd4542bfa8a85fe5150bfaa2a17f14542be28a85ff5050afea0a17f94142fea8285fc5050af8a0a15f95042ffa9885fe5310afca6217f54c42bea9885fc5310bfe86217f90c42fea1885fc4310afca4217fd0842dfa1085fe4210bdc84217f50842dea1085ed4210bfea2217f94442bf28885fd5110afaa2217f14442ffa8085fe5010afca0217f54042bea8085fc5010bfea9195fd5232ff2a4657e548cbfaa9195f55232fe2a4657c548cafaa7197fd0e32ff21c65fd438cbf887195f94a32ffa1465fe428cbfa85197f10a32ff99465ef328cbfea3197f94632bf28c65fd518cafaa3197f14632ffa8465fe508cafca1197f54232bea8465fc508cbfea8995fd5132ff2a2657e544cbfaa8995f55132fe2a2657c544cbfe84997f90932fea1265fc424cbfc6499778c932ffa8a657f514cbfca2997f54532fe28a657c514cbfea0995fd4132ff28265fd504cbf8a0995f14132ffaa0657f540cbfca8195f95032feaa0657d540cbf8a8195f15032bf29065ff420cbfc84197f50832fe21065fe320cbdc64197f4c832f699065cd320cbfea2197f94432bf28865fd510cafaa2197f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea5a0ff94b41bf29683fd52d06faa5a0ff14b41ffa1683fe42d07fa85a0ff10b41ff19683fd32d07f865a0ffd4341ff286837e50d07faa1a0df54341fe286837d54907fea520ff94a41bf29483fd52906faa520ff14a41ffa1483fe429077c8520ff50a41fe21483bc42907fc6520ff4ca41fe194837e519
  | 4 => 0xbfa058990e39535e3dbf40f07fdd6d7c4299d7cfe14a07b4d10001ce0000002348000000a78c48000608984c04b14979359cf952d960e2cda18d8248001f50000000000000eb1350e3437d0a826df700e1e159b9dc1709134c2964811cf2a1582c4000c21db95994ec021ab0ab11b9eb21602886f8d6c4f1c9d08c3ec5cd30c929b68000ffdb906b9645419040a685313381822519999a1aa8aa8ea86049b01a0b61990df93c4e00000b4926c00102000114cb740022f1b3df19701c20000494f51c492ac0017b1ff00010693bc0010f0000901038265ee0e50f49a08591af57a8001d298707a83398f97d61d4001944000001c0d508ad88d11e8001d982400017a0dd1635d5c300dd87a00461f80007284f82f5bd0001501d09c1dcac390a191480011a1070001bec8100021dcb2c002011420001245744000e89738000479ed0ef9159ca918dcd5be8ba4ec9371da02056d80545bca118411d81462a14e9181140000ff9c146adb458c86e0b70f597300003e8b3c72d5b0049f41b05bf09f2360000f304a96d0001ca01642c93111c40009e8381888001fb98311302c01700009d17d15b890c631cc632046cb95fb11b00a81c13d11180000014b5b000020fc001c980000011900001e00013c15d8771af9c81ad860dcc89c8002005c042b03b8a896e85a00000000018a88405096580016c9ffdaf17e56519e1f996292e84183d01d8cf030cf60cea3507621302f08c87218b51856bcf0cb009756e1d38cc1fe0000bc0000fec616091808f9415c808b3516e0f06c47b9d548f81d06511980fc0000102c044078030000440081602c0280080a0120000501c000000020010000000c04e00400c000000040780501401e014010060000000d81201200c0002200002801008000000188020140000080200c00c0280201c0dc0500200e00407000006050018000000000280900a0080300700400800032000024040000060140980000e0a4008040040000880e00e02805029006000010110000200000a00c0380000700006c030170020240081100c0500c801006020080190020100a80000c00c038000040000100c002004000100000180000300400000800002000040050080040901100600c0d8180140000b0250060000000204a04003006046000040160360a40200000202c000000000180000500403c0280300600c0a003002000168100280340680e0040000c00900000c00004004000000000000080c00d00c07005808002004000000000000900102a0080080c03e014008000a00280300300001c03004006000008040360000080000c014030000000100281402c0100000f032004008050120680200100e000000030120041380401a00c00002000034058040000000202b006054020050360000000100202c008130000200c8060660040
  | 5 => 0x2bc7d0b20001009f307a4de98594ad078d847b1b6447d00049800000000013da211f8420de11c0ee9ad0d99c40250000001361e1db1592e148e28558b98000378ed00000000000020b80000005f14a800033165c000510a620312f8af0002188000980000fc5931590000000000aa00014f0000001424e09450000b7d459748e10b1c002319538d40001170c94bc8190a02139691fa93412c93cd2605399c80009f81b22c0000000501095325109970a4003ded8599ccd229560ea0c091d513c27d7195101e8becad09ac31d7415196880005fcc00000f817dc001120c606a125c001d20094161480549be5680a208ce2d0480faca29cb4001711155969c882b92b5de83c1f480000004b0f78d950b0fa5ba1661c01b602744762315bce482d62891a89586b52f05885c62d8f683f1151e206b056c3997cc7c4ba8000001a994791600019b53e4001188002009cb82d1cb1ae0114001d70891e60c80681b1a1d9890089a615a82d9b71a30305fe99410913f0b44001a49e193e1d64091b0ce80798319b122607082799ad42887103d67d7d9581b24051f58566109ec15722e85fa200d5a0393d9271e01b08a80611bd44045408b195ddf8351e692b04305e4715cdc2e91ce1a190000097e10610c001f0c27000158cad57886a63693c9238ea4001838465ce89157c96c40404d99196260a2078aea17051d6cc4a5bb9d4c4c14981180000008800012553b1c310d021a1818d0970000800000d64ac412c001c600000013000003d80000000000006c0000000cfd6f86cce61390c0ca91b980000012517fc5c8744000b59258001a803400020209e56540698441f4e98a507390844c8001610b1800000183da69ab96f00c1bb0ac85c00117686e91c927dfc88883206dcc550e1e894ccf092c0cd121025e1e8000c4c5b142d2a449007a1d0d28ca11795217608f2249a88371608dcdfc2279d6a080008468736302101a06331d761b939a1b08680b22383fdb89d3c93cb85d84601c25f04be94bc8a9ee9f680000000f61c0b8a0d04407ca070be0001f6105c3698187c0c58660c51280ff009cbe46196b8d099520e000177194992045d4300000020c89405ecce4d24f98f853a0000000000000d89f01c088782099c0001812118000eb9bfa1106d5290000cc9f08000b418c0000000458000d180000005162684616380000000018800000001540710817f8002191b560a87494c8f193321f13052a00011bc0000009203f9208259e70000e19e24fb8d79cf0fb1674002358000198a0c000001899dfc1f85240009a00001b8001ea800100502800000000104404db38001df000115c000930d600017993dd2fe0290182e58a0000001e78b81f28519679bc0805b597914b94390c8a44df4231549b29671288580f75935b481695280000f9d8ca30000a4c3a
  | 6 => 0x283492d05289959102012d90e8489878000000d000016680ec8393fe0d8d1d268f04ba1e805610980d0f88315100bf4000328000000758d7d8b000038d734000000000f720c0d808616c0b39938001530a38280000fe9a58c385aa0b1dd1e39588f8d402141e505e19296a1de1a71ef12b9ef96995f14d4451fa0c7944874c91861dd80b9069818a1e1fb555a3285860696a97f4001a1a04092e2400c9a340000014c0b79d186593885dcf904381a8038000e40999601e104499751460e962d9aa208f017295f8711550df0141e09e2c360150002000000bd9e982cdca4d148e80000002295ea0140000017200005508314d80010c1e413d5440da8000000001a2932c0007900000012862110b8b30a3d4f9e29e31219a01e58135a780019bc2e00013b9ba98e19c4000310001ea0290000000001f791d1afca09bfcfaa298780bd00013ecb0a3390a00017f0000b8df20d91e488a13497c13e800082112cfa1408a3400000069014c000859b5daa1851125f90e2457c2ec00127871c9f46885b84e06bd94dc94ff53f95695a00019d1579bdd80d010c18bb1d79d10c6928c384098e1d4d132816d5d01780586f0ab9c8c2bda914a62201c862163c8c124c9b89a92f45e8ae1988ef45745d4ddd780000dc0001060001980c103e0750000000000670000394001aed57c0004e80022a9ff80019786692000004d19e98695c8c88bf00000010d8221ae6049b8038882a3085d010d4e47ac0011e05d80014118546c99d840184c788000b240d995800048c001c682a0fd9fd80006e40018b80ac57a2c8ac229c851138471fd07410521c81f1a397b9309368000d38000898000bb8000ce0b9c00077a290138d31c580006d8002310cf864012923e0f8e588198007f0000002120571378fbc01a051ac0000001128e90001470000001848904081efc0009d9d44000000fb4732280ef1be1c91f1131c001b207f830800164d8215c146a27196d46012471940c9510584562b9b51031bd82fdd91b323400018288b8cb09497e8000dc83b098c910000001b40000002044d70000000000111194001b78c30e30628b11bc96f4db800000050d088000e740014e11f0000001f804102380a5da8000001908ec09c1ae8d74031c11ff6229274000cd86d1640fc0000268445cc07cc55cb6a0612a94b1ec8f21298000d21c28e79cd89e0210c9098802954105491dfec0e98e8e69b4c8494fd415ac8bac4280005f5318000a48261db0ed80009ec000105cd0ca86a98f1d89eec001174fc800000080d6b1631ee400104e259a41221110c7109d165d49c7881493941db34f1099c2f9a1000000212a2b22e10f8101c702a8f7c7d8dd4109618648d053f4c4015993d53c7242855440005219b0efdeb82ddcedd40149d31405c51cbd5e12e0d6a0883a80a0a70000000001
  | 7 => 0x86dce59f0d5cdb18e6150060af9ef4ee040975873dd016b5e0c3581313204b9264f4049cd51248001f3867844dd59e90120d4a178f39315d50a580b9665a509094c49260987e8cb87e117ce71954484b503f4fd00004a0a85778a980009a4002199c39e34c462f88e01fd241b2cd0d7e17500010480009362194900020180000000008d8f9c000000700001489380001b1c3ca1a9d61231dc9c19168969f88c9887d86020d9f8e216209613a856a169dd8d8cc3c768639334b
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa210436d5288410dd94621042fa6088410be582210427f6548410afd9121042bc6448410cf951210433d5448410d794d210435d5348410db949210436d5248410dd945210427f65084109f594210433e5408410cf550210435e5308410d754c210436e5208410db54821042fa6008410be580210427e6494010cf992500423e64940109f592500433d64940108f592500427e62940109f58a500427d61940109f597400433f54d0010cf953400433d54d0010cf153400436e52d0010db54b40042bd65d0010cf597400423d65d0010cfd4b400433e52d0010eb94b400432e52d0010cf54b40043ad52d0010cb54b400433c52d0010cf947400433e50d00109fd96400427d6590010af592400433e5490010cf552400436e5290010db54a40042f66190010bd586400437a50900109fd95400433f5450010cf951400433d5450010cf151400436e5250010db549400437a5050010afd95400433f65500108fd95400433f5250010cf94940043ae5250010cb949400433d5250010eb549400432d5250010cf149400433e5150010eed81400433e5050010ce941400427f65100109f994400427d65100109f19440042be6410010cf950400433d5410010db948400436d5210010bd98440042f561100109f597200433e54c8010cf553200435e53c8010d754f200436e52c8010db54b200427f65880109f59620042be6488010af592200433e5488010cf552200435e5388010d754e200436e5288010db54a20042f66188010bd586200427f6548010cf951200433d5448010b7d8d20042dc6348010d794d200435d5348010db949200436d52480109fd94200427e65080109f594200427c6508010af99020042bd6408010cf950200433d5408010b798c20042dd6308010d794c200435d5308010db948200436d5208010bd98420042f56108010cf953100433d54c4010db94b100436d52c4010dd59710043b654c4010ed553100437752c4010f994b100437552c4010f954b100436552c4010edd0310043b540c4010af99210042bd6484010cf952100433d5484010db94a100436d5284010bd58610043765184010eed0210043b94084010be596100437965840109e59610043ba6484010ee592100437b5484010ee95210043795484010ee55210043395484010fa94a10043e95284010be586100437a5184010fc946100427f6544010cf951100433d5444010db949100436d5244010eed0110043b94044010bdd95100437765440109dd9510043b65444010ed55110043775244010f994910043755244010f954910043655244010bdd8110043765044010edd0110043b54044010bed95100437b65440109ed95100437b5444010ee95110043795444010ee55110043395444010fa94910043e95244010bed8510043f36144010de94510043f25144010
  | 1 => 0x426d6594810dbd52520436e5494810eb952520432e5494810db55252043ad5494810cb552520436c5494810dbd4e520436e5394810f394e520434e5394810dbd92520436e6494810db592520436c6494810dbd8e520436e6394810db58e520436c6394810db986520436c6194810db982520436c6094810cf951520433d5454810d794d520427f64548109f191520427f63548109f18d520436f62548109fd85520427d61548109fd81520427d6054810dbd95520436f5454810db95152043ae5454810cb951520436d5454810eb551520432d5454810db151520436f5354810db94d52043ce5354810d394d520436d5354810f354d520434d5354810dbd91520436e6454810db591520436c6454810dbd8d520436e6354810db58d520436c6354810db985520436c6154810db981520436c6054810db04152042be6414810af590520433e5414810cf55052042de6314810b758c520435e5314810d754c52042ee6214810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520426e62148109f984520437661148109d984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420435e53d0810d754f420436e52d0810db54b420427f65908109f996420427d65908109f196420433e5490810cf552420435e5390810d754e420436e5290810db54a420427f65508109f995420427d65508109f195420433e5450810cf551420435e5350810d754d420436e5250810db54942042f76150810bd185420427f65108109f994420427d65108109f194420433e5410810cf550420435e5310810d754c420436e5210810db548420427f658c8109f996320427d658c8109f196320433e548c810cf552320435e538c810d754e320436e528c810db54a320427f654c8109f995320427d654c8109f195320433e544c810cf551320436e524c810db54932042fb604c810be181320427f650c8109f994320427d650c8109f194320433e540c810cf550320436e520c810db54832043cd320c8109f992510427d64944109f98a510427d62944109f597410433e54d0410cf553410436e52d0410db54b410427f65904109f596410433e5490410cf552410436e5290410db54a41042fa6090410be582410427f6550410cf951410433d5450410db949410436d52504109fd94410427d6510410cf950410433d5410410bb98841042ed6210410db948410436d5210410ed50441042fa6010410be580410427d65c8410cf953210433d54c8410d794f210435d53c8410db94b210436d52c84109fd96210427d6588410cf952210433d5488410b798e21042dd6388410d794e210435d5388410db94
  | 2 => 0x6190110fc88640443f121901109fd95404427d65501109f195404433f5450110cf15140442f76150110bd185404433f6550110cf995404433d6550110cf195404433f5250110cf949404433d5250110cf14940443b76150110ed18540443b62150110ed48540443bb6050110be195404437865501109e19540443bb6450110eed51404437a5450110de15140443b85450110eed0940443ba4250110ee50940443b84250110fcd8540442f86150110fc18540443bb4150110ee90540443b94150110ee10540443f22150110fc48540443bb6550110ced9540443b86550110ce19540443bb6250110ee98940443b96250110ee18940443bb5250110ee94940443b95250110ee14940443ba3250110ee4c940443b83250110eed8540443b36150110ee98540443b96150110ee18540443b06150110eec8540443ba2150110ec88540443b92150110ec48540443b821501109f99440442be6410110be98040443b940101109f997204436f52c8110db14b20442f661c8110bd58720443e521c8110ee503204427e6588110af99220442bd6488110ee502204427f65481109f595204427c6548110b7d8d20442dc6348110dbd49204436c5248110bdd8520442f46148110f948520443b940481109f99420442be6408110af59020442de6308110b758c20442f66108110bd58420443b94008110eed0310443b940c4110bed9310442f964c4110fc88710443f121c4110af99210442bd6484110ee50210443b66484110ed59210442f76284110bd58a10443f35084110edd0210443f24084110ed50210443f14084110ec50210442ee62d5010bb58b540427e62d5010db98b540426e62d50109f58b540436d62d50109b58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540427e62950109f58a540423d6595010cfd8a540433e6295010cf58a540433c6295010cf986540433c6195010cf982540433c6095010cfd91540427f62550109f189540427f61550109f585540427f60550109f581540433f6555010cfd89540433e6255010cf589540433c6255010cf985540433c61550108fd81540433e60550108f581540433c6055010cf04154042be6415010cf55054042ee6215010bb588540427e6415010cf990540423e64150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109f980540437a60150109e98054042be64d4810af593520433e54d4810cf55352042de63d4810b758f520427e64d4810cf993520423e64d48109f593520433d64d48108f593520427e63d4810d798f520425e63d48109f58f520435d63d48109758f520427e61d4810dd987520427e60d4810de983520427d6594810cf952520433d5494810dbd4a520427e64948109f592520427e63948109f58e520
  | 3 => 0x110bb189544433f64551109fd89544436f62551109bd89544427c6255110db189544426c62551109fd85544437761551109fd81544437b60551109f994544433d5415110cf990544427e62151109f588544427e61151109f184544427e6015110de580544427c60151109f993524427d64d49109f98f524427d63d4910dbd4a524427e64949109f592524427e63949109f58e524427e62949109f586524437561949109f58252443796094910afd9152442bc6454910b7d8d52442dc63549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910db548524427e64149109f590524427e63149109f58c524436e62149109f984524437561149109f184524427e60149109f180524427f65d09109f997424427d65d09109f197424436f52d0910db14b42442fa60d0910be583424427f65909109f996424427d65909109f196424433f5490910cf15242442f66190910bd586424427f65509109f995424427d65509109f195424427f65109109f994424427d65109109f194424433f5410910cf150424436f5210910db14842442f66110910bd58442442fa6010910be580424427f658c9109f996324427d658c9109f196324435f538c910d714e32442f6618c910bd586324427f654c9109f995324427d654c9109f195324427f650c9109f994324427d650c9109f194324436f520c910db14832443cd320c910bd98432442f5610c910be98032442f9600c9109f997414433f54d0510cf15341442fa60d0510be583414427e6590510cf952414433d54905109f195414433f5450510cf15141442fb6050510be181414427e6510510cf950414433d5410510bb98841442ed6210510be980414427e65c8510dbd4b214436c52c8510be98321442f960c85109f99621442de6388510b758e21442f66588510dd99621442f76388510f598e21442f56388510f558e21442d56388510bd58a21443765288510dd14a21442f660885109f19521442bf6448510af191214436f5248510db14921442fb6048510be181214437465485109d19521443b76448510ed19121442f76348510bd58d21443e76248510f9d4921443765248510dd14921443e45248510f990921443e54248510f9cc921443e43248510fcd8121442f46048510fc181214427e6508510bd98421443e521085109f997404433f54d0110cf15340442f661d0110bd587404433f65d0110cf997404433d65d0110cf197404433f52d0110cf94b404433d52d0110cf14b40443b661d0110ed58740443b621d0110ed487404427e6590110af59240442fa6590110de99640442f96490110ae592404437a5490110de15240442fa
  | 4 => 0xdd8542842f46150a109fd94428427e6510a109f594428427c6510a10cf950428433d5410a10be98042842f96010a109fd96328427e658ca109f596328427c658ca10cf952328433d548ca10d7d4e328435c538ca10db94a328436d528ca109fd95328427e654ca109f595328427c654ca10cf951328433d544ca10db949328436d524ca109fd94328427e650ca109f594328427c650ca10cf950328433d540ca10dbd48328436c520ca10f34c832842fa600ca10be580328433e54d0610cf55341842fa60d0610be583418433e5490610cf552418433e5450610cf55141842fb6050610be181418433e5410610cf55041842ee6210610bb58841843b54110610be580418433e54c8610cf553218436e52c8610db54b21842fa60c8610be583218433e5488610cf55221842de6388610b758e21842bf6448610af191218433e5448610cf551218436e5248610db54921842fb6048610be181218433e5408610cf550218433f54d0210cf953408433d54d0210cf15340842bd65d0210cf597408433f52d0210cf94b408433d52d0210cf14b408433e5490210cf55240842f66190210bd58640842f96590210de596408437a5490210ee95240843b95490210de15240842fa6190210fc98640843f16190210cfd51408433e5450210cf551408433c5450210afd95408433f6550210cfd49408433e5250210cf549408433c5250210eed8140842fb6550210ded9540843bb6450210eed51408437a5450210ee951408433a5450210ee55140843785450210ee15140843bb4250210ee90940843b94250210ee10940842f86150210eed0540843ba4150210ee50540843b84150210eed9540842bb6550210ced9540843bb6250210ee98940843b96250210ee18940843bb5250210ee94940843b95250210ee14940843ba3250210ee4c940843b83250210eed8540843ba6150210ee58540843b86150210eec8540843ba2150210ee48540843b82150210cf950408433d5410210bd98440842f56110210ee500408433e54c8210cf553208436f52c8210db14b20843b940c8210af99220842bd6488210cf952208433d5488210db94a208436d5288210bd98620842f56188210ee502208433e5448210cf55120842df6348210b718d208436f5248210db14920843b94048210af99020842bd6408210cf950208433d5408210b798c20842dd6308210db948208436d5208210bd98420842f56108210ee500208433e54c4210cf55310843bb40c4210ee50310842f565c4210dd59710843b654c4210ed553108437752c4210dd54b10843b740c4210ed50310842f965c4210de59710842fb64c4210be59310843ba54c4210ee553108427e62d51109f58b544433f54951109f992544427e62951109f58a544427d6195110dd586544427d6095110de58254442ef6255
  | 5 => 0x41c433c5450710cf95041c433d5410710bb98841c42ed6210710be98041c42f96010710dbd4b21c436c52c8710b798e21c42dd6388710db94a21c436d5288710be98221c42f96088710dd59621c42f76388710f598e21c42f56388710f558e21c42d56388710dd94a21c43e65288710f954a21c43745288710bd98221c43f26088710fc58221c42bf6448710af19121c436f5248710db14921c42f76548710ddd9521c43b76448710ed19121c42f76348710bd58d21c43e76248710f9d4921c43765248710dd14921c43e45248710f990921c43e54248710f9cc921c43e43248710bd18121c436e5208710db54821c43e52108710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310cf99740c433d65d0310cfd4b40c433e52d0310cf54b40c433c52d0310ed98740c43b561d0310ed88740c43b521d0310cf95140c433d5450310bdd8540c42f46150310cfd9540c433c6550310cfd4940c433e5250310cf54940c433c5250310edd8540c43b46150310ed88540c43b52150310eed8140c436e52c8310db54b20c42f661c8310bd58720c43e521c8310af99220c42bd6488310b7d8d20c42dc6348310db94920c436d5248310bdd8520c42f46148310f948520c42be6408310af59020c42de6308310b758c20c42f66108310bd58420c427e62d52109f58b548437561d5210de983548433f54952109f98a548427d6295210de98254843ba6095210cfd8a548433e6295210cf58a548433c6295210cfd86548433d6195210cf982548433a6095210cf182548433f64552109fd89548427c6255210cfd9554843ba6055210cfd89548433e6255210cf589548433c6255210cfd85548433d6155210cf981548433c6055210cf550548433e64152109f988548427d6215210dd584548437a6015210af99352842bd64d4a10cf953528433d54d4a109f993528433e64d4a108f993528427d64d4a10cf593528423d64d4a109f98f528427d63d4a10dd587528437a60d4a10cf952528433d5494a10dbd4a528427e6494a109f592528427e6394a109f58e528433e5454a10cf55152842df6354a10b718d528427f6454a109f191528427f6354a10d7d8d528425f6354a109f18d528435c6354a109718d528436f6254a10af99052842bd6414a10cf950528433d5414a10b798c52842dd6314a10db548528427e6414a10cf990528423e6414a109f590528433d6414a108f590528427e6314a10d798c528425e6314a109f58c528435d6314a109758c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10cf953428433d54d0a10be98342842f960d0a109fd96428427e6590a109f596428427c6590a10cf952428433d5490a109fd95428427e6550a109f595428427c6550a10cf951428433d5450a10b
  | 6 => 0x33d54c8020d794f200835d53c8020dd947200837551c8020eb95320083ad54c8020bb98f20082ec63c8020dbd4f20083ce53c8020db54f20083cd53c8020d354f20083e651c8020db54720083e551c8020d954720083af40c8020eb50320082be6488020af592200833e5488020cf552200835e5388020d754e20082ed6288020db94a20083765188020dd54620083bb4088020ee50220083ba6488020ee59220083ba5488020ee55220083da5388020f654e20082f96288020de94a20083ea5288020facca20083e83288020fc94620083f151880209fd95200833e5448020cf55120082df6348020b718d200835e5348020d754d20083765148020dd54520083bb4048020ee50120082ef6548020dbd95200826f6548020eb95120083ad5448020f3d8d20082ee6348020bb18d20083cc6348020b318d200836f5348020f394d200836d5348020f354d200834d5348020f9945200836d5148020f954520083655148020bbd81200836e5048020ebd0120083ea4048020eb50120083e94048020ea50120082fb6548020ded95200827b6548020ee95120083b95448020f6d8d20083d86348020f694d20083d95348020bed8920083eb6248020de94920083ea5248020fa90920083e94248020fc94520083f151480209f98b54c427d62d5310dd98754c437960d5310cfd5254c427e62953109f58a54c433f64553109fd8954c427c6255310cf55054c42ee6215310bb58854c433e64153109f98854c436e62153109b98854c427d6215310db58854c426d6215310dd98454c43796015310b798f52c42dd63d4b109f99352c427d64d4b109f98f52c435e63d4b109798f52c427d63d4b10d758f52c425d63d4b10dd98752c437960d4b10dbd4a52c427e6494b109f59252c427e6394b109f58e52c43766194b10afd9152c42bc6454b109fd9152c433f6454b108fd9152c427c6454b10cf19152c423c6454b109fd8d52c427c6354b10dbd8952c436d5214b109f99052c427d6414b109f98c52c427d6314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c427f6590b109f99642c427d6590b109f19642c433f5490b10cf15242c436e5290b10db54a42c42f66190b10bd58642c427f6550b109f99542c427d6550b109f19542c436e5250b10db54942c427f6510b109f99442c427d6510b109f19442c433f5410b10cf15042c42f66110b10bd58442c427f658cb109f99632c427d658cb109f19632c435e538cb10d754e32c42f6618cb10bd58632c427f654cb109f99532c427d654cb109f19532c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c436e520cb10db54832c43cd320cb10bd98432c42f5610cb10cfd5341c433c54d0710cf95241c433d5490710be98241c42f96090710cfd51
  | 7 => 0x4cc420cf553310835e53cc420d754f31083cc32cc420dd947310837551cc4209fd96310827e658c4209f596310833e548c420cf552310835e538c420d754e31082ee628c420bb58a3108376518c420dd546310827f654c4209f595310827c654c420afd9131082bc644c420cf951310833d544c420d794d310835d534c420bbd8931082ec624c420f30c93108376514c420dd54531082fb604c420be181310827f650c4209f994310827d650c420cf950310833d540c420d794c310835d530c420dd9443108375510c420cf953210833d54c8420d794f210835d53c8420db94b210837651c8420dd54721082fa60c8420be583210827d6588420cf952210833d5488420b798e21082dd6388420d794e210835d5388420dd546210827f6548420afd9121082bc6448420cf951210833d5448420d794d210835d5348420db94921083765148420cf950210833d5408420d794c210835d5308420dd94421083755108420be98021082f960084209f992500833e64940208f992500827d6494020cf592500823d64940209f98e500827d6394020dbcca500836c32940209f597400833f54d0020cf953400833d54d0020cf153400835e53d0020d754f400837651d0020dd54740082bd65d0020cf597400823d65d0020cfd4f400833e53d0020e794f400831e53d0020cf54f400839d53d0020c754f400833c53d0020cf94b40083af32d0020eb0cb400833e51d0020ed947400833651d0020cf54740083b551d0020cd547400833e50d00209fd96400827d6590020af592400833e5490020cf552400835e5390020d754e40082ee6290020bb58a40083765190020dd546400827f6550020cfd51400833e5450020cf551400833c5450020d794d400835d5350020dd94540083755150020afd95400833f65500208fd95400833f5350020cf94d400839e5350020c794d400833d5350020e754d400831d5350020cf14d400833e5250020ebcc940083ac3250020cf94540083b65150020cd945400833d5150020ed54540083355150020eed81400833e50500209fd94400827e65100209f594400827c6510020af990400833e5410020cf550400835e5310020d754c40082ee6210020bb58840083765110020dd544400827d65cc020cf953300833d54cc020d794f300835d53cc020f3ccb300837651cc020dd54730083b940cc0209fd96300827d658c020af99230082bd648c020cf952300833d548c020d794e300835d538c020bb98a30082ed628c020f30ca3008376518c020dd546300827f654c020cf951300833d544c020d794d300835d534c020bbd8930082ec624c020f3cc93008376514c020dd545300827e650c0209f594300827c650c020cf950300833d540c020bb98830082ed620c020f30c83008376510c020dd54430083b9400c020cf9532008
  | 8 => 0x20dbd4f32083ce53cc820db54f32083cd53cc820d354f32082ed60cc8209fd96320827d658c820cf952320833d548c820d794e320835d538c820bb98a320836e528c820be98232082f9608c8209fd95320833e544c820cf551320835e534c820d754d320836e524c8209fd94320827d650c820cf950320833d540c820d794c320835d530c820f34c832082fa600c820be580320836d650c8209b59432083ae540c820eb55032082ee630c820f398c320836f530c820f394c320836d530c820f354c320834d530c820fa98032082ed600c820fa58032082be64d4420af593510833e54d4420cf55351082de63d4420b758f510835e53d4420d754f510833e5494420cf552510835e5394420d754e510837751944209f992510827d64944209f98e510827d6394420ddd5251083765494420ed95251083365494420dd55251083b55494420cd55251083745494420ddd4e51083765394420f594e51083565394420dd54e51083d55394420d554e51083745394420f9cca51083e43294420ddd9251083766494420dd59251083746494420ddd8e51083766394420dd58e51083746394420ddd0e51083764394420dd50e51083744394420dd18a51083774294420dd90a51083754294420dd10a51083773294420dd8ca51083753294420dd0ca51083766094420dd182510833e5454420cf551510835e5354420d754d510827f64544209f191510827f63544209f18d510836f3254420db0c951083776554420ddd5151083765454420ed95151083365454420dd55151083b55454420cd55151083745454420ddd4d51083765354420f594d51083565354420dd54d51083d55354420d554d51083745354420f9cc951083e43254420ddd9151083766454420dd59151083746454420ddd8d51083766354420dd58d51083746354420ddd0d51083764354420dd50d51083744354420dd98951083774254420dd90951083754254420dd10951083773254420d9cc951083763254420dd4c951083743254420d90c951083766054420dd18151083742054420af99051082bd6414420cf950510833d5414420b798c51082dd6314420d794c510835d5314420bd984510837551144209fd97410827e65d04209f597410833e54d0420cf553410835e53d0420d754f410837651d0420dd547410827f65904209f996410827d6590420cf952410833d5490420d794e410835d5390420dd946410837551904209fd95410827d65504209f195410833e5450420cf551410835e5350420d754d41082ef6250420bb18941083765150420dd545410827f65104209f994410827d6510420cf950410833d5410420b798c41082dd6310420d794c410835d5310420bb98841082ed6210420dd94441083755110420be98041082f960104209fd97310827e65cc4209f597310833e5
  | 9 => 0x585540833c6155020cf981540833c6055020cf08154082be6415020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf990540823e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f988540836e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a6015020af99353082bd64d4c20cf953530833d54d4c20bd98753082f561d4c209f993530833e64d4c208f993530827d64d4c20cf593530823d64d4c20db98b530827e61d4c20dd987530827661d4c209f587530837561d4c209d587530837a60d4c209f596530833e5494c20cf552530835f5394c209f992530827d6494c209f986530827d6194c2097596530835f5494c20d7952530839e5494c20c7952530835d5494c20e7552530831d5494c20d715253083cc6294c20d7d92530835e6494c20d7592530835c6494c20d798a530835c6294c20d7d86530835e6194c20d7586530835c6194c20d7982530835c6094c20cf951530833d5454c209fd91530827c6454c20d7d8d530827f6254c209f589530836c6254c209fd85530827c6154c20d7d95530835f5454c20d7951530839e5454c20c7951530835d5454c20e7551530831d5454c20d715153083cc6254c20d7d91530835e6454c20d7591530835c6454c20d7989530835c6254c20d3189530835f6154c20d7985530835d6154c20d7185530835e6054c20d7181530835c2054c20af99053082bd6414c20cf950530833d5414c20b798c530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f988530836e6214c209b988530827e6114c20dd98453082766114c209f58453083756114c209d584530827e6014c20de980530827f65d0c209f997430827d65d0c209f197430833e54d0c20cf553430835e53d0c20d754f43082ee62d0c20bb58b43082fa60d0c20be583430827f6590c209f996430827d6590c209f196430833e5490c20cf552430835e5390c20d754e430827f6550c209f995430827d6550c209f195430833e5450c20cf551430835e5350c20d754d43082ef6250c20bb189430827f6510c209f994430827d6510c209f194430833e5410c20cf550430835e5310c20d754c430827e64948209f592520827d63948209f597420833e54d0820cf553420835e53d0820d754f420827f65908209f596420833e5490820cf552420835e5390820d754e42082fa6090820be582420827f6550820cf951420833d5450820d794d420835d53508209fd94420827d6510820cf950420833d5410820d794c420835d5310820be98042082f960108209f597320833e54cc820cf553320835e53cc820d754f32082ed65cc820db597320826d65cc820eb95332083ad54cc8
  | 10 => 0x14836d54c8520bbd8f21482ed63c8520f3d4f214836e53c8520db14f21483cc53c8520d314f214836c51c8520bb98321482de6388520b758e214835f5388520d714e21482ed6288520ddd4621483745188520be98221482f96088520afd9121482bc6448520d7d4d214835c5348520ddd4521483745148520bed8121482f86048520ebd9121483ac6448520dbd51214836d5448520bbd8d21482ed6348520f3d4d214836e5348520db14d21483cc5348520d314d21483e76148520f9d45214836c5148520f914521483eb6048520bb18121483e860485209f994214835f5308520d714c21482ee6208520f9484214827e65d0120cfd53404833c54d0120d7d4f404835c53d0120bb98b40482ed62d0120cfd97404833e65d0120cf597404833c65d0120cfd4f404839f53d0120c7d4f404833e53d0120cf54f404833c53d0120e714f404831c53d0120eb98b40483ad62d0120eb8cb40483ad32d0120cfd47404833c51d0120ebc8740483ad21d01209f99640482bd6490120d7d4e404835c53901209fd95404827d65501209f195404833f5450120cf151404835f5350120d714d40482ef6250120bb189404833f6550120cf995404833d6550120cf195404833f5350120e7d4d404831f5350120cf94d404833d5350120cf14d404839c5350120c714d40483af6250120eb18940483ae3250120eb4c9404833f5150120cf14540483af2150120eb48540483bb60501209f99440482be6410120d7d4c404835c53101209f997304835f53cc120d714f30482ee62cc120bb58b30483cd32cc120af99230482bd648c120d7d4e304835c538c120f38ca30483b9408c1209f595304827c654c120bbd8930482ec624c120f34c930483b9404c120d7d4f204835c53c8120eed0320483b940c8120f6d4f20483d853c8120fa8cb20483e932c8120fac8720483e921c8120af99220482bd6488120d7d4e204835c5388120eb99220483ad6488120bbd8e20482ed6388120f3d4e204836e5388120db14e20483cc5388120d314e20482ed6188120fad4220483af4088120eb50220482de63d5020b758f54082f661d5020bd587540827e63d5020d798f540825e63d50209f58f540835d63d50209758f540827e62d5020db98b540827e61d5020dd987540827661d50209f587540837561d50209d587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540823d6595020cfd8e540833e6395020cf58e540833c6395020cf98a540833c6295020cfd86540833e6195020cf586540833c6195020cf982540833c6095020cfd91540827f63550209f18d540827f62550209f589540827f61550209f185540833f6555020cfd8d540833e6355020cf58d540833c6355020cf989540833c6255020cfd85540833e6155020cf
  | 11 => 0x7e6514d20d754c534827e6414d209f590534835e6314d209f188534827e6114d209f58453482de6514d20d7994534825e6514d20d7d50534835e5414d20d7550534835c5414d20f3588534835f6414d20d7990534835d6414d20d7190534835f6214d20d7d84534835e6114d20d7584534835c6114d20d7d80534835d6014d20d7480534827f65d0d209f997434827d65d0d209f197434835f53d0d20d714f434827f6590d209f996434827d6590d209f196434835f5390d20d714e43482ee6290d20bb58a434827f6550d209f995434827d6550d209f195434835f5350d20d714d434827f6510d209f994434827d6510d209f194434835f5310d20d714c43482ee6210d20bb58843482fa6010d20be580434827e65d0920cfd53424833c54d0920d7d4f424835c53d0920be98342482f960d09209f996424833e5490920cf552424835f5390920d714e424827c6550920cfd51424833c5450920d7d4d424835c5350920bed8142482f860509209f994424833e5410920cf550424835f5310920d714c424835f53cc920d714f32482fa60cc920be583324827e658c920d7d4e324835c538c920bb996324836e658c9209b99632482ed638c920f3d4e324836e538c920db14e32483cc538c920d314e32482ed618c920bb982324835f534c920d714d32482fb604c920be18132483cf634c920f3d4d324836e534c920db14d32483cc534c920d314d32482ef614c920fad8132482ec604c920fa181324827e650c920d7d4c32482ee620c920f34c8324835f53d4520d714f514827e64d45209f593514827e63d45209f58f51482de6394520b758e514835f5394520d714e51483775194520afd9151482bc6454520b7d8d51482dc6354520d7d4d514835c5354520d7d4c514835c5314520dd544514827e64145209f590514827e63145209f58c514827e65d05209f597414827c65d0520d7d4f414835c53d0520ddd47414837451d05209f996414827d65905209f196414833f5490520cf152414835f5390520d714e41482ee6290520bb58a414827f65505209f995414827c6550520d7d4d414835c53505209f994414827d65105209f194414833f5410520cf15041482de6310520b758c414835f5310520d714c41482ee6210520bb58841483775110520dd14441482fa6010520be580414827e65cc5209f597314827c65cc520d7d4f314835c53cc520bb98b31482ed62cc520f38cb314827e658c5209f596314827c658c520d7d4e314835c538c520bb98a31482ed628c5209fd95314827e654c5209f19531482bf644c520af191314835f534c520d714d31483ce324c5209f994314827d650c5209f194314835f530c520d714c31482ee620c520bb58831482fa600c520be580314827e65c8520d7d4f214835c53c8520bb997214836e65c8520dbd532
  | 12 => 0x106209f594418833e5410620cf55041882de6310620b758c41882ee6210620bb58841882fa6010620be580418827f65cc6209f997318827d65cc620cf953318833d54cc620d794f318835d53cc620f30cb318827f658c6209f996318827d658c620cf952318833d548c620bb98a31882ed628c620dd9463188375518c6209fd95318827d654c6209f19531882bf644c620af191318833e544c620cf551318835e534c620d754d31882ef624c620bb18931883cc324c620dd9453188375514c6209fd94318827e650c6209f594318833e540c620cf55031882fa600c620be580318833e54c8620cf553218833e5488620cf55221882de6388620b758e21883765188620dd54621882fa6088620be58221882bf6448620af191218833e5448620cf55121883765148620dd54521882fb6048620be181218833e5408620cf550218833f54d0220cf953408833d54d0220cf15340882bd65d0220cf597408833f53d0220cf94f408833d53d0220ebccb40883ac32d0220cf947408833d51d0220cf952408833d5490220bb98a40882ed6290220cfd51408833e5450220cf551408833c5450220afd95408833f6550220cfd4d408833e5350220cf54d40883af3250220eb0c9408833e5150220cf54540883bb6050220cf950408833d5410220bb98840882ed6210220cf953308833d54cc220f3ccb308833e548c220cf55230882ee628c220bb58a30883cc328c220ee502308833e54c8220cf55320883bb40c8220ee50320882ed65c8220db59720883ae54c8220eb55320882ee63c8220bb18f208836f53c8220db54f208836d51c8220ebd0320883ad40c8220be597208837965c8220ee95320883b954c82209f98f544827d63d51209f987544827d61d5120cfd5254482de6395120b758e544827e64951209f98e544835e63951209798e544827d6395120d758e544825d63951209f58a544836d62951209f986544827d61951209f58254483796095120b7d8d54482dc6355120bdd8554482f46155120cfd91544827f6355120d7d8d544825f63551209f18d544835c63551209718d544827f6255120dbd89544827f6155120ddd85544827761551209f185544837461551209d185544827f6055120ded81544827e6515120cf550544833e64151209f98c544827d63151209f988544827c62151209f984544827d61151209f993534827d64d4d209f987534827d61d4d20d7d53534835e54d4d20d7553534835c54d4d20f3d8b534835f64d4d20d7993534835d64d4d20d7193534835f62d4d20d758b534835f61d4d20d7987534835d61d4d20d7187534835f60d4d20d7583534835f5394d209f992534827d6494d20db58a534827e6194d209f58653483796094d209fd91534827c6454d20dbd89534827f6154d209f185534827f6054d20ded8153482
  | 13 => 0xeb8c940c83ad3250320cf94540c833d5150320ebc8540c83ad2150320eed8140c82ee62cc320bb58b30c83cd32cc320ee50330c827e63d52209f58f548836d62d52209f987548827d61d5220de983548833f54952209f98e548827d63952209f986548827d6195220cfd8e548833e6395220cf58e548833c6395220cfd8a548833d6295220cfd86548833e6195220cf586548833c6195220cf982548833c6095220cfd91548827f63552209f18d548827f61552209f185548833f6555220cfd8d548833e6355220cf58d548833c6355220cfd89548833d6255220cfd85548833e6155220cf585548833c6155220cf981548833c6055220cf550548833e64152209f98c548827d6315220db588548827e61152209f584548837a6015220af99353882bd64d4e20cf953538833d54d4e209f993538833e64d4e208f993538827d64d4e20cf593538823d64d4e209f987538827d61d4e20de983538833e5494e20cf552538835f5394e209f992538827d6494e209f986538827d6194e20cf951538833d5454e209fd91538827c6454e20d7d8d538827f6154e209f18553882be6414e20af590538833e5414e20cf550538835d5314e20bd98453882f56114e209fd97438827e65d0e209f597438827c65d0e20cf953438833d54d0e20bb98b43882ed62d0e209fd96438827e6590e209f596438833e5490e20cf552438827f6550e209f995438827d6550e209f195438833e5450e20cf55143882ef6250e20bb189438827f6510e209f994438827d6510e20cf950438833d5410e20be98043882f96010e20cf953428833d54d0a20be98342882f960d0a20cf952428833d5490a20cf951428833d5450a20bed8142882f86050a20cf950428833d5410a20cf953328833d54cca20d794f328835d53cca20be98332882f960cca20eb95332883ad54cca20f394f328836d53cca20f354f32883ea60cca20bb58332883e960cca20cf952328833d548ca20d7d4e328833e544ca20cf551328835e534ca20d754d32882fb604ca20be181328833e540ca20cf55032883cd320ca20bb594328836d650ca20eb95032883ad540ca20f398c328836f530ca20f3d4c328834f530ca20db54c32883cc530ca20bb58032882be64d4620af593518833e54d4620cf553518833e5494620cf552518837751946209f992518827d64946209f98e518827d6394620cf951518833d54546209fd91518827c64546209fd8d518827c6354620dbcc9518836c3254620af99051882bd6414620cf950518833d5414620b798c51882dd6314620dd544518827f65d06209f997418827d65d0620cf953418833d54d06209fd96418827e65906209f596418833e5490620cf552418827f65506209f595418827c6550620cf951418833d5450620bbd8941882ec62506209fd94418827e65
  | 14 => 0x8454c827d6115320de58054c835f5394f209f99253c827d6494f209f98653c827d6194f209fd9153c827c6454f209fd8553c827c6154f20d754c53c827e6414f209f59053c836e6214f209f98453c827d6114f20de58053c827f65d0f209f99743c827d65d0f20be98343c82f960d0f209fd9643c827e6590f209f59643c827c6590f20bb98a43c82ed6290f209fd9543c827d6550f209f19543c827f6510f209f99443c827d6510f209f19443c82ee6210f20bb58843c833f54d0b20cf15342c833e5490b20cf55242c82fa6090b20be58242c833f5450b20cf15142c833e5410b20cf55042c82fa6010b20be58042c835e538cb20d754e32c82fa608cb20be58232c836e538cb20f394e32c83cd538cb20db14e32c82ed618cb20bb98232c83ea608cb20fa58232c82ef654cb20dbd9532c83cf634cb20f3d4d32c836e534cb20db14d32c83cc534cb20d314d32c82ef614cb20bb18132c835e530cb20d754c32c83cd320cb20be98032c82f9600cb20b798e51c82dd6394720ddd4651c827e64947209f59251c827e6394720d798e51c825e63947209f58e51c835d63947209758e51c82bf6454720af19151c827f6454720cfd9151c823f64547209f19151c833c64547208f19151c827f63547209f18d51c837551147209fd9741c827e65d07209f59741c827f65907209f99641c827d6590720cfd5241c833c5490720bb98a41c82ed62907209fd9541c827d65507209f19541c827f65107209f99441c827d6510720cfd5041c833c5410720b798c41c82dd6310720bb98841c82ed6210720be98041c82f960107209fd9731c827e65cc7209f59731c82ee62cc720bb58b31c83ce32cc7209fd9631c827e658c7209f59631c82ee628c720bb58a31c827f654c7209f59531c827c654c720afd9131c82bc644c720f38c931c82fb604c720be18131c827f650c7209f99431c827d650c720bb98831c82ed620c720dd94721c837551c8720be98321c82f960c8720dbd5321c836d54c8720bbd8f21c82ed63c8720db94f21c836c53c8720db94721c83e651c8720f954721c82ee60c8720fa98321c83e960c8720b798e21c82dd6388720afd9121c82bc6448720bbd9521c836f6548720ebd9121c83ac6448720dbd5121c836d5448720bbd8d21c82ed6348720db94d21c836c5348720f9d8521c83e75148720db94521c83e45148720bb18121c83765108720dd54421c83e52108720be98021c82f96008720cf95340c833d54d0320bb98b40c82ed62d0320cf99740c833d65d0320cf94f40c833d53d0320cf14f40c83ae62d0320eb58b40c83ae32d0320eb4cb40c833e51d0320cf54740c83af21d0320eb48740c833e5450320cf55140c82ef6250320bb18940c833f6550320cf19540c833e5350320cf54d40c833c5350320ebd8940c83ac625032
  | 15 => 0x503b72148540eb88521502bf6048540af18121502bf6508540af99421502bd6508540af19421502bf6308540af98c21502bd6308540af18c21502be6208540ebd4821503ac5208540af98421503b75108540ed14421503af2108540ed88421503ad2108540ed48421502be6008540ee98021502ba6008540af58021503b96008540ae58021502be62d4140af58b505033f52d4140cf14b50502be61d4140af587505033f51d4140cf14750503bb62d4140ee98b50503b962d4140ee18b50503bb52d4140ee94b50503b952d4140ee14b50503ba32d4140ee4cb50503b832d4140eed8750503ba61d4140ee58750502b961d4140ee18750503bb51d4140ee94750503b951d4140ee14750503bb21d4140ee88750503b921d4140ee087505033e6295040cf58a541033e6195040cf586541036f52948409f98e521027d63948409f986521027d61948409fd8d521027c63548409fd85521027c6154840b798c52102dd6314840db54852102f66114840bd584521033e54d0840db94b421036d52d0840be98342102f960d08409f596421033e54908409fd95421033e5450840cf950421036e5210840db54842102fa6010840be580421027f658c8409f996321027d658c840cf952321036e528c840db54a321027f654c8409f595321027c654c840cf951321036e524c840db549321027f650c8409f994321027d650c840cf95032103cd320c840ddd46511027e62944409f58a511027f62544409f18951102ee6214440bb58851103755114440cf953411037651d0440dd54741102fa60d0440be583411027d6590440cf952411027f6550440cf951411033e5410440bb98841102ed6210440dd94441103755110440ed50441102fa6010440be580411027f65c84409f997211027d65c8440cf953211036e52c8440db54b211027f65884409f996211027d6588440cf95221102de6388440b758e21103765188440dd546211027f65484409f595211027c6548440afd9121102bc6448440cf951211036e5248440db54921103765148440dd545211027f65084409f994211027d6508440cf950211033e52d0040cf54b401033e51d0040cf54740102bd6490040cf95240102f96490040de95240103ba5490040de546401027f6550040cf95140102bf6550040cfd95401023f6550040cf949401033d5250040cf945401033d5150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee951401033a5450040de54540103bb4150040ee505401027e63d53209f58f54c836e62d53209f98754c827d61d5320de58354c833f54953209f98e54c827d63953209f98654c827d6195320cfd9154c827f63553209f18d54c827f61553209f18554c833d5415320cf99054c827e63153209f58c54c836e62153209f9
  | 16 => 0xc5288540be98221502f960885409fd95215027e65485409f19521502bf6448540af99121502bd6448540af19121503ae4248540eb509215027e65085409f594215027c6508540afd9021502be6408540af59021502bc6408540dbd48215036c5208540ddd4421503745108540be98021502f96008540eed0b40503ba42d0140ee50b40503b842d0140be58740503bb41d0140ee90740503b941d0140ee10740502be6290140af58a40502be6190140af58640503bb5090140af98f52502bd63d4940af98752502bd61d4940af98e52502bd6394940af98a525033f5294940ebd4a52502be6194940af58652502bd6094940ee58252502b96094940afd8d525039f6354940a7d8d52502bc6354940e718d525029c6354940ebd49525033e5254940afd8552503b76154940add8552502bc6154940ed18552502b46154940afd8152503bb6054940aed8152502be6514940af98c52502bd6314940cfd4852503ae5214940cf54852503ad5214940af98452502bd6114940afd9632502be658c940af59632502bc658c940af58e325039f538c940e714e32502be628c940ebcca32502be618c940af58632502be608c940af58232502bf654c940af99532502bd654c940af195325039e324c940afd8532502bc614c940afd8132503bb604c940aed8132502bc604c940ee18132502b8604c940afd9432502be650c940af59432502bc650c940af98832503af520c940eb14832503ae320c940eb4c8325038d320c940af98432502bd610c940af98032503ba600c940ae98032502bd600c940ee58032502b9600c940af98b51502bd62d4540eed8351502be6294540af58a515033e5294540cf14a51502be6194540cfd4651503b75194540af58251503b96094540ae58251502bf6254540ebd8951502af6254540af18951503ac6254540ab18951503b75154540cf94551502bf6054540eed8151502bb6054540af99451502be6214540eb98851502ae6214540af58851503ad6214540ab588515033e5214540cf148515033f5114540ed944515033d5114540ed54451503355114540ee58051502bf65c8540af99721502bd65c8540af19721502be63c8540af58f21502bc63c8540eb94b21503ad52c8540ebccb21503ac32c8540edd4721503b451c8540af98321502bd60c8540afd9621502be6588540af59621502bc6588540afd8e21502be6388540e798e215029e6388540af58e215039d6388540a758e21502bd6288540ebd4a21503ac5288540af98621503af2188540edc8621502be6088540ee98221502ba6088540af58221503b96088540ae58221502bf6548540cfd95215023f6548540af99521502bd6548540af195215033c65485408f19521502bf6348540af98d21502bd6348540af18d21503ae5248540eb54921503af3248540eb0c921
  | 17 => 0x86409f19521902bf6448640af191219036e5248640db54921903765148640dd545219027f65086409f994219027d6508640be98021902f96008640af597409033d65d0240cf94b409033d52d0240cf947409033d51d0240be597409037965d0240be587409027e63d49409f58f525027e61d49409f587525036f5294940b7d8d52502dc6354940bdd8552502f46154940db548525027e63149409f58c525027e61149409f584525027e65d0940af997425033e65d0940af98f42502bd63d0940cf14b42502be61d0940af58742502be60d0940af592425036f5290940db14a42502fa6090940be58242502be6390940af58e42502be6290940cfd4a42503af5290940eb14a42502be6190940af58642502be6090940ee98242503b96090940dbd49425036c5250940bed8142502f86050940afd8d42502bc6350940ebd8942503af5250940cf14942503ac5250940afd8542502bc6150940eed8142502bc6050940ee181425027e6510940af99042502be6510940cf99442502be6310940af58c42502be6210940eb988425033f5210940af98442502bd6110940af980425027e658c9409f596325027c658c940afd9232502be648c940af59232502bc648c940d7d4e325035c538c9409fd95325027e654c9409f19532502bf644c940af99132502bd644c940af19132502fb604c940be181325027e650c9409f594325027c650c940afd9032502be640c940af59032502bc640c940dbd48325036c520c940f34c832502fa600c940be580325027e62d45409f58b51503775194540bbd8951502ec6254540bb98851502ed6214540dd544515027e6214540db988515026e62145409f588515036d62145409b588515033e4214540cf108515037960145409f99741502be65d0540cf99741502be62d0540af58b415033c51d0540eed8341502be60d0540ee18341502bd6490540ddd4641503745190540be98241502f96090540af98a41502bd6290540cf14a41502be6190540cfd4641503b75190540ed14641502be6090540ee98241502ba6090540ee58241503775150540dd14541502fb6050540be18141502bf6250540af18941503b76150540edd45415033c5150540ed14541503345150540eed8141502bc6050540ee181415027e6510540af99041502ee6210540bb58841502fa6010540af994415033e6510540af98841503ae6210540ab98841502bd6210540eb58841502ad6210540cf14841502be6110540ed984415033f5110540af98041503ba6010540ae98041503b960105409f997215027d65c85409f19721502bf64c8540af99321502bd64c8540af19321503ae42c8540eb50b215037751c8540dd147215027e65885409f596215027c6588540afd9221502be6488540af59221502bc6488540b798e21502dd6388540dbd4a215036
  | 18 => 0xafd8552d02bc6154b40af98c52d02bd6314b40cfd4852d03ae5214b40cf54852d03ad5214b40af98452d02bd6114b40af58052d03b96014b40ae58052d02bf658cb40af99632d02bd658cb40af19632d039e538cb40e754e32d03af328cb40af98632d02bd618cb40af98232d02bd608cb40afd9532d02be654cb40af59532d02bc654cb40e78c932d02bf614cb40af18532d02bf604cb40af18132d02bf650cb40af99432d02bd650cb40af19432d03ae520cb40eb54832d03ae320cb40eb4c832d038d320cb40af98432d02bd610cb40af98032d02bd600cb40af98b51d02bd62d4740af58351d03b960d4740ae58351d02be6294740af58a51d033e5294740cf14a51d033f5194740edd4651d02bf6254740af18951d03b75154740cf94551d02be6214740eb98851d02ae6214740af58851d03ad6214740ab58851d033e5214740cf14851d033f5114740ed94451d033d5114740ed54451d03355114740af58051d03b96014740ae58051d02bf65c8740af99721d02bd65c8740af19721d02be63c8740af58f21d02bc63c8740eb94b21d03ad52c8740ebccb21d03ac32c8740af98321d02bd60c8740afd9621d02be6588740af59621d02bc6588740afd8e21d02be6388740e798e21d029e6388740af58e21d039d6388740a758e21d03af2188740edc8621d02be6088740af58221d02bf6548740cfd9521d023f6548740af99521d02bd6548740af19521d033c65487408f19521d02bf6348740af98d21d02bd6348740af18d21d03ae5248740eb54921d03af3248740eb0c921d03b72148740eb88521d02bf6048740af18121d02bf6508740af99421d02bd6508740af19421d02bf6308740af98c21d02bd6308740af18c21d03af2108740ed88421d03ad2108740ed48421d02be6008740af58021d036f5294a409f98e529027d6394a409f986529027d6194a409fd8d529027c6354a409fd85529027c6154a40b798c52902dd6314a40db54852902f66114a40bd584529036e5290a40db54a42902fa6090a40be582429036e5250a40db54942902fb6050a40be181429027f658ca409f996329027d658ca40db94a329036d528ca409fd95329027d654ca409f195329036e524ca40db54932902fb604ca40be181329027f650ca409f994329027d650ca40f34c832902fa600ca40be580329037751946409f98a519027d6294640de982519027f62546409f18951902ee6214640bb58851903755114640dd94641903755190640be98241902f96090640dd94541903755150640bed8141902f86050640bb98841902ed6210640ed50441902f960106409fd97219027e65c86409f597219036e52c8640db54b219027f65886409f996219027d6588640b798e21902dd6388640dd94621903755188640be98221902f960886409fd95219027d654
  | 19 => 0x2500867e63940219f58e500867f64540219f191500867f63540219f18d500876f2154021dd885500876d2154021dd48550086be6414021af59050086de6314021b758c50087795014021b798f52d02dd63d4b40dbd4a52d027e6394b409f58e52d027e6194b409f58652d027f6354b409f18d52d027f6154b409f18552d036d5214b40db94b42d036d52d0b40be98342d02f960d0b40af98f42d02bd63d0b40cf94b42d03ae52d0b40eb54b42d02be61d0b40af58742d02be60d0b40ee98342d03b960d0b40af59642d033d6590b40af98e42d02bd6390b40cf54a42d02be6190b40af58642d02be6090b40afd9542d033f6550b40afd8d42d02bc6350b40ebd8942d033e5250b40afd8542d02bc6150b40af18142d036e5210b40db54842d02fa6010b40be58042d02be6310b40af58c42d03ae6210b40eb94842d033d5210b40eb54842d02be6110b40af58442d02be6010b40ee98042d03b96010b409fd9632d027e658cb409f59632d02bf648cb40af99232d02bd648cb40af19232d035e538cb40d754e32d027f654cb409f59532d027c654cb40afd9132d02be644cb40af59132d02bc644cb409fd9432d027e650cb409f59432d02bf640cb40af99032d02bd640cb40af19032d036e520cb40db54832d03cd320cb40ddd4651d027e62947409f58a51d033e4294740cf10a51d027f62547409f18951d02ee6214740bb58851d03755114740dd94741d037551d0740be98341d02f960d0740af98b41d02bd62d0740cf94741d03b651d0740ed54741d02be60d0740ee98341d03b960d0740af59641d033d6590740af98a41d02bd6290740cf94a41d033d5190740af98241d02bf6550740cfd9541d02bf6250740af18941d03b76150740cf94541d02bc6050740bb98841d02ed6210740dd94441d03755110740be98041d02f96010740af98841d03ae6210740ab98841d02bd6210740eb58841d02ad6210740cf94841d03b66110740ed94441d033d5110740ed54441d03355110740af98041d03ba6010740ee58041d027f65c87409f99721d027d65c8740afd9321d02be64c8740af59321d02bc64c8740db94b21d036d52c8740eb90b21d03ad42c87409fd9621d027e65887409f59621d02bf6488740af99221d02bd6488740af19221d02de6388740b758e21d027f65487409f59521d027c6548740afd9121d02be6448740af59121d02bc6448740db94921d036d5248740eb90921d03ad42487409fd9421d027e65087409f59421d02bf6408740af99021d02bd6408740af19021d02be63d4b40e798f52d029e63d4b40af58f52d039d63d4b40a758f52d02be61d4b40af58752d02bd60d4b40ee58352d02b960d4b40af98e52d02bd6394b40cfd4a52d03af5294b40af98652d02bd6194b40afd8d52d02bc6354b40ebd4952d033e5254b40
  | 20 => 0x875e63150219798c540867d6315021d758c540865d63150219f988540876e62150219b988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e580540867e64d4c219f593530876e62d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530867f6454c219f191530875f6354c219fd81530867c6054c21af99053086bd6414c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6214c21db988530867e6114c21dd984530867e6014c21de980530867a6014c219f58053087796014c219e580530867f65d0c219f997430867d65d0c219f197430873e54d0c21cf553430867f6590c219f996430867d6590c219f196430875e5390c21d754e43086ee6290c21bb58a43086f66190c21bd586430867f6550c219f995430867d6550c219f195430873e5450c21cf551430875e5350c21d754d430867f6510c219f994430867d6510c219f194430867e64948219f592520867d63948219f597420867f65908219f596420873e5490821cf552420876e5290821bd98642086f561908219fd95420876e52508219fd94420867d6510821cf950420873d5410821bd98442086f561108219f597320876e52cc8219fd96320867d658c821d794e320875d538c821bd98632086f5618c8219fd95320867f650c8219f594320875e530c821d754c320876e520c821f34c832086f6610c821bd584320867e64944219f592510867e6394421d798e510865e63944219f58e510875d63944219758e510867d65d04219fd96410867d6590421cf952410873d5490421bb98a41086ed62904219fd95410867f65104219f994410867d65104219f194410873e5410421cf55041086de6310421b758c41086ee6210421bb58841086fa6010421be580410867d65cc421d7d4f310867f658c4219f596310875e538c421d754e31086ee628c421bb58a310867f654c421afd9131086bc644c421d7d4d310867e650c4219f594310867c650c421bb98831086ed620c421dbd53210876d54c8421db94f210876c53c8421b798e21086dd6388421bb58a210876e5288421f598e21087d56388421bd58a21087765288421f994a210867f6548421afd9121086bc6448421bbd95210876f65484219bd9521087af6448421eb191210876f5448421db551210876e5348421db14d21086ef6148421db94521087e74148421f910521087e63148421f94c521086f76548421ddd9521086776548421edd9121087b46448421bdd8921087e76248421dd94921087e65248421f9d0921087e44248421f98c921087e53248421af99250086bd6494021ded42500867e6494021cf992500863e64940219f592500873d64940218f59
  | 21 => 0x5490921db15242487ac5490921cb15242486ee6390921bb98642486ed60909219f195424873f5450921cf15142486f76150921bd185424876c65509219b19542487af6450921ebd51424876e5450921db15142487ac5450921bb18d42487e76150921bb18542487e46150921b918542486ef60509219f994424873f5410921cf15042486ee6210921cfd53324873c54cc921d7d4f324875c53cc921bd98732486f561cc921db99732486ef64cc921bb59332487af54cc921eb153324876f53cc921f3d4f32487cc53cc921bb98732487e661cc921b998732487e561cc921bb583324867e658c921cfd52324873c548c921d794e324875d538c921bb98a324873f544c921cf151324875f534c921d714d32486f7614c921bd185324867e650c921cfd50324873c540c921d794c32487cd320c921bb994324876e650c921bbd9032486ed640c921ebd5032487ac540c921bb98c32487ce630c921dbd4c32487ce530c921db54c32487cd530c921d354c32486ee610c921bb580324867e65d0521cfd53414873c54d0521bb98b41486ed62d05219f996414873f5490521cf15241487ae42905219fd95414867d65505219f195414873f5450521cf15141486ef6250521bb189414867e6510521cfd50414873c5410521b798c41486dd6310521bb98841486ed6210521eb90841487b54110521be98041486f960105219f997314873f54cc521cf153314875f53cc521d714f31486ee62cc521bb58b31487cc32cc521cfd52314873c548c521bb98a31486ed628c5219f595314867c654c521cfd51314873c544c521bbd8931486ec624c521f30c9314873f54c8521cf15321487b754c8521ed15321487e642c8521f950b21487e732c8521f90cb21486f560c8521cfd52214873c5488521b798e21486dd6388521bbd9221486ed6488521ebd5221487ac5488521bb98e21487ce6388521b398e21487cd6388521f9d4621486ed6088521cfd53504873c54d4121cfd93504867e64d41219f593504873c64d41219f98f504867d63d4121af99250486bd6494121cfd52504873c5494121ded4250486bf6454121af191504873f5454121cf15150486df6354121b718d50486be6414121af590504873f5414121cf15050486de6314121b758c504877950141219f990504873e64141218f990504867d6414121cf590504863d64141219f98c504875e63141219798c504867d6314121d758c504865d6314121dbcc8504876c32141219f98f540867d63d50219f98b540876e62d50219f987540877661d50219f983540867d60d50219f596540873f54950219f98e540867d63950219f982540867d6095021cfd91540867f63550219f18d540867f60550219f181540873d5415021b798c54086dd6315021be98054086f960150219f990540873e64150219f98c540
  | 22 => 0x621d794f318875d53cc621bb98a31886ed628c621d794f218875d53c8621bb597218876d65c8621dbd53218876d54c8621db94f21887ce53c8621d394f21887cd53c8621bd597218877565c8621f594f21887d553c8621bd58321886de63d4221b758f508875e53d4221d754f50886be6494221af592508875e5394221d754e508877b50942219f992508873e64942218f992508867d6494221cf592508863d64942219f98e508867d6394221d794d508875d53542219fd91508867c64542219fd8d508867c6354221dbc8550886be6414221af59050886de6314221b758c508875e5314221d754c508877950142219f98f544867d63d51219f983544867d60d5121ebd8b54486bd60d5121cfd8f544873e63d5121cf58f544873c63d5121cfd8b544873d62d5121cfd87544873d61d5121cfd83544873e60d5121cf583544863d60d5121cf183544873f54951219f992544863e64951219f98e544867d63951219f58a544876d62951219f586544877561951219f982544867d6095121cfd91544867f63551219f18d544867f6255121dbd89544867f6155121ddd85544867f60551219f181544867e6515121cf550544873e64151219f98c544867d6315121db588544867e60151219f58054486be6515121cf994544863e6515121eb58854486bd6015121cfd8c544873e6315121cf58c544873c6315121cfd88544873d6215121cb588544873f6115121cf584544873d2115121cfd80544873e6015121cf580544863d6015121cf180544873f54d4d21cf153534867e64d4d219f593534876d62d4d219f983534867d60d4d21af99253486bd6494d21cfd52534873c5494d21d7d4e534867e6494d21cf992534863e6494d219f592534873d6494d218f592534876d6294d21dd586534867e6094d219f58253486bf6454d21af191534873f5454d21cf15153486fb6054d21be181534867f6454d21cfd91534863f6454d219f191534873c6454d218f191534876f6254d219fd8553487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f994534873f5414d21cf150534875d5314d219f990534867d6414d21d798c534867e6014d219f580534867f65d0d219f997434867d65d0d219f197434873f54d0d21cf15343486ee62d0d21bb58b434867f6590d219f996434867d6590d219f196434873f5490d21cf152434867f6550d219f995434867d6550d219f195434873f5450d21cf15143486ef6250d21bb18943486f76150d21bd185434867f6510d219f994434867d6510d219f194434873f5410d21cf15043486ee6210d21bb58843486f66110d21bd584434867e65d0921cfd53424873c54d0921bd98742486f561d09219f996424873f5490921cf15242486ee6590921db99642486ed6490921ebd52424876e
  | 23 => 0xf95341c873d54d0721bb98b41c86ed62d0721cfd5241c873c5490721eb90a41c873e5450721cf55141c86ef6250721bb18941c873f5410721cf15041c86de6310721b758c41c86ee6210721bb58841c87ae4210721be98041c86f96010721bb98b31c86ed62cc721f30cb31c86be6494321af59250c877b50943219f99250c873e64943218f99250c867d6494321cf59250c863d64943219f98e50c867d6394321dbcca50c876c32943219fd9150c867c64543219fd8d50c867c6354321af99050c86bd6414321b798c50c86dd6314321de54050c86de63d5221b758f548867e63d5221d798f548865e63d52219f58f548875d63d52219758f548876d62d5221dd987548867e60d52219f583548873f54952219f98e548867d63952219f982548867d6095221cfd91548867f63552219f18d548867f60552219f181548873d5415221b798c54886dd6315221be98054886f96015221cf990548867e6315221d798c548865e63152219f58c548875d63152219758c548876d6215221dd984548867e6015221de980548867a60152219f580548877960152219e580548867e64d4e219f593538877661d4e219f983538867d60d4e21d7d4e538867e6494e219f592538867e6094e219f582538875f5494e21d7952538875d5494e21d7152538875f6494e21d7992538875d6494e21d7192538875f6294e21d758a538875e6194e21d7186538875f6094e21d7982538875d6094e21d7182538867f6454e219f191538875f6354e219fd81538867c6054e21d7d95538875f5454e21d7951538875d5454e21d7151538875f6454e21d7991538875d6454e21d7191538875d6254e21d7985538875c6154e21d7d81538875e6054e21d7581538875c6054e21d754c538867f65d0e219f997438867d65d0e219f197438875e53d0e21d754f438867f6590e219f996438867d6590e21d794e438875d5390e21bb98a43886ed6290e219fd95438867e6550e219f595438867c6550e21d794d438875d5350e21bdd8543886f46150e219fd94438867e6510e219f594438875e5310e21d754c43886f66110e21bd584438873e54d0a21cf553428875e53d0a21d754f42886f661d0a21bd587428873f5490a21cf152428875e5390a21d754e428873e5450a21cf551428875e5350a21d754d42886f76150a21bd185428873f5410a21cf150428875e5310a21d754c428875e53cca21d754f32886f661cca21bd587328875e538ca21d794d328875d534ca21bdd8532886f4614ca21d794c328875d530ca21f34c8328875e53d0621d754f418873e5490621cf552418875e5390621d754e41886ee6290621bb58a418875e5350621d754d418873e5410621cf55041886de6310621b758c418875e5310621d754c41886ee6210621bb58841887b54110621be98041886f96010
  | 24 => 0x501077b5294041de94a50107ea5294041da94a50107795294041fa54a50107695294041de14a50107ba4294041ee10a50107bb4194041fc90650107b94194041fc50650107786494041ded8a501077a6294041de58a50107786294041ded0a501077a4294041de50a50107784294041de8ca50107793294041de0ca50107786194041ded06501077a4194041de506501076e5254041db549501073e64540419fd89501067c6254041cf909501073c4254041cfd05501073d4154041ded9550107ba6454041ded49501077a5254041fa949501076a5254041de54950107e95254041da54950107785254041ee90950107b84254041eed0550107f24154041ee50550107f14154041de991501073a6454041ded89501077a6254041de58950107786254041ded09501077a4254041ce90950107794254041de10950107384254041de8c950107793254041de0c9501077a6154041ded05501073b4154041de90550107794154041ce50550107784154041bb98850106ed6214041db948501076d5214041be98050107795014041b798f54c86dd63d53219f98f54c875e63d53219798f54c867d63d5321d758f54c865d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c867e63953219f58e54c876e62953219f98254c867d6095321cfd9154c867f63553219f18d54c867f60553219f18154c873d5415321cf99054c867e63153219f58c54c876e6215321dd58454c867e60153219f58054c86be64d4f21af59353c875f5394f219f99253c867d6494f219f98253c867d6094f219fd9153c867c6454f219fd8153c867c6054f21d754c53c867e6414f219f59053c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f21d794f43c875d53d0f21bb98b43c86ed62d0f219fd9643c867e6590f219f59643c867c6590f21cf95243c873d5490f21bd98643c86f56190f219fd9543c867d6550f219f19543c86ef6250f21bb18943c867f6510f219f99443c867d6510f219f19443c873e5410f21cf55043c875e5310f21d754c43c86ee6210f21bb58843c873e5490b21cf55242c86f66190b21bd58642c876d6590b21db95242c87ae5490b21eb55242c876c5490b21bb98e42c86ee6190b21f998642c87e56190b21bb58242c86ef6550b21dbd9542c87af6450b21db95142c876c5450b21bb18d42c86ec6150b21bbd8142c873e5410b21cf55042c86f66110b21bd58442c86ed65ccb21db59732c86ef64ccb21bb59332c876d53ccb21bb98732c86ed60ccb21d794e32c875d538cb21bd98632c86f5618cb21d794c32c875d530cb21f34c832c86f6610cb21bd58432c86ef640cb21bb59032c87ce630cb21f394c32c876d530cb21f354c32c874d530cb21bb98432c87e6610cb21f958432c86ed600cb21c
  | 25 => 0x6f76150941bd185425067e65109419f996325067d658c9419f196325076f528c941db14a325067f654c9419f995325067c654c941dbd49325076c524c9419f994325067d650c9419f19432506be640c941af59032507cd320c941bd98432506f5610c941cf14a41507b75190541af582415073f64d41419f98b505067d62d4141cf907505077b5094141bbd8950506ec6254141de540505067e62141419f58850506de63d4841b758f52106fa60d4841be583521076f52948419f98e521067d63948419f982521067d6094841eb192521076f5394841db94e52107ce5394841d394e521076c6494841dbd8e521076e6394841db58e521076c6394841db986521076c6194841dbd82521076e6094841db582521076c6094841d794d521067f63548419f18d521067f60548419f181521076f6554841eb191521076f5354841db94d52107ce5354841d394d521076d5354841f354d521074d5354841db991521076f6354841db98d521076d6354841db18d521076e6154841db185521076c4154841dbd81521076e6054841db581521076c6054841b798c52106dd6314841d794c521075d5314841bb988521076d5214841be98052106f96014841d794f421075d53d0841db94b421076d52d0841bd98742106f561d08419f596421075e5390841d754e421076d5290841af596421073d6590841af98e421079e5390841e754e42106be6290841eb94a421073d5290841eb54a421072d5290841af58642106bd60908419fd95421075e5350841d754d421076e5250841d794c421075d5310841db948421076d5210841bd98442106f56110841af98c421079e5310841e754c42106be6210841eb98842107ae5210841cf54842107ad5210841ed98442106bd6110841ed58442106b56110841af580421067f658c8419f996321067d658c841af99232106bd648c841d794e321075d538c841db94a321076d528c841bd98632106f5618c8419fd95321067d654c8419f19532106bf644c841af191321076e524c841db549321067f650c8419f994321067d650c841afd9032106bc640c841db948321076d520c841f34c8321073e4294441cf10a511076e52d0441db54b41106be62d0441eb94b41107ad52d0441af58341106bd6490441cf952411076e5290441db54a41106f56490441dd95241107b65490441f994a41107e55290441ed90a41107b442904419fd95411076e5250441db54941106bf6550441cfd95411063f6550441af18941107ae5250441eb54941106bf6150441cf94541106bf6050441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141107e65250441f954941107b74250441ed50941106ee62d4041bb58b501076e52d4041db54b501076e5294041db54a501077b50940419f98a501067d6294041ee992
  | 26 => 0x54c8329bd95320caef634c832db94d320cbce534c832f3d0d320cbce434c832f350d320cbcc434c832bbd85320caec604c832f3d95320cacf654c832d3d95320cbcf644c832f3991320cbcd644c832f3191320cbcf544c832f3951320cbcd544c832f3151320cbcf614c832b3d85320cbce614c832f3585320cbcc614c832f3d81320cbce604c832f3581320cbcc604c832b3181320cbcd32d4432f34ca510cb7751944329f992510ca7d64944329f982510ca7d6094432afd91510cabc6454432f34c9510ca7f6454432cfd91510ca3f64544329f191510cb3c64544328f191510ca7f60544329f181510cabe6414432af590510cbcd3214432dd544510cafa6014432be580510cbcd32d4032af992500cabd6494032f34ca500cb7b50940329f992500cb3e64940328f992500ca7d6494032cf592500ca3d64940329f986500ca7d6194032f34c9500ca7f64540329f191500cb6e3254032db4c9500cb4d32540329fd85500ca7c6154032af990500cabd6414032f34c8500caf66114032bd584500cb795014032dbd4a52d067e6394b419f58e52d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41db94842d076d5210b41bd98442d06f56110b419fd9632d067e658cb419f59632d06f6618cb41bd58632d067f654cb419f59532d067c654cb419fd9432d067e650cb419f59432d06be640cb41af59032d07cd320cb41ded4250d067e62943419f58a50d073e64543419fd8950d067c6254341de54050d06de63d4a41b758f529076f5294a419f98e529067d6394a419f982529067d6094a419fd8d529067c6354a419fd81529067c6054a41db548529076e5290a41db54a42906f66190a41bd58642906be6390a41eb94a429073d5290a41eb54a42907b66190a41af58642907b56190a41af582429076e5250a41db54942906f76150a41bd18542906bd6510a41cf59442906be6310a41eb988429073d5210a41af58442906bd6010a419fd96329067e658ca419f59632906be648ca41af592329075e538ca41d754e329067f654ca419f595329067c654ca41afd9132906bc644ca419fd94329067e650ca419f59432906bf640ca41af190329076e520ca41db54832907cd320ca41bd98432906f5610ca41af597419073d65d0641af98b41906bd60d0641bd597419077565d0641ded42509067e62942419f58a509073d64542419fd89509067c6254241cf909509073c4254241cfd0550906ee6214241bb588509077950142419f98f525067d63d49419f983525067d60d4941b798e52506dd6394941dbd4a525076d52149419f98c525067d63149419f980525067d60149419f997425076f5290941db14a42506f66190941bd586425076f5250941db1494250
  | 27 => 0x32cf550548cb3e6415232d758c548cb6e62152329f984548ca7d61152329f980548ca7d6015232cf953438cb3d54d0e32bb98b438caed62d0e32cf951438cb3d5450e32bbd89438caec6250e32cf952428cb3d5490a32b798e428cadd6390a32cf950428cb3d5410a32b798c428cadd6310a32eb508428caed65cca32db597328cabe64d4632af593518cb7751946329f992518ca7d64946329f982518ca7d60946329fd91518ca7c6454632dbcc9518ca7f60546329f181518cb755114632af992508cabd6494232ded42508ca7e6494232cf992508ca3e64942329f592508cb3d64942328f592508cb6f32942329f986508ca7d61942329fd91508ca7c6454232d7cc9508ca7f61542329f185508cabe6414232af590508caf66114232bd584508cb7950142329f987544ca7d61d51329f983544ca7d60d5132cfd52544cafa6095132be582544ca7e64951329f58a544cb6d62951329f986544ca7d61951329f982544cb7a60951329e982544ca7d6095132de582544ca796095132cfd91544ca7f6255132dbd89544ca7f61551329f185544ca7f60551329f181544ca7e6515132cf550544cb3e64151329f984544ca7d61151329f980544ca7d60151329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e65909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424ca7e6510932eb508424cbcf528c932b7582324ca7e64d45329f593514cb5e32d45329f983514ca7d60d4532ddd46514cabf6454532af191514cafb6054532be181514cb7551145329f990514ca7d64145329f980514ca7d60145329f993504ca7d64d41329f987504ca7d61d4132af992504cabd6494132ded42504cabe6414132af590504caf66114132bd584504cb7950141329f990504cb3e64141328f990504ca7d6414132cf590504ca3d6414132d78c8504ca7e6114132dd984504ca7661141329f584504cb7561141329d584504ca7e62d5032db98b540ca7e61d50329f587540ca7e60d50329f583540ca7d6595032cfd52540ca7e61950329f586540ca7e60950329f582540cb3f64550329fd85540ca7c61550329fd81540ca7c6055032cf550540caf66115032bd584540cafa6015032be580540ca7e6415032cf990540ca7e6215032db988540ca7e6115032dd984540ca7661150329f584540cb7561150329d584540ca7e6015032de980540ca7a60150329f580540cb7960150329e580540ca7e64948329f592520ca7d65d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd63908329fd95420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420caed638c832b358e320cb6e538c832f394e320caed618c832bb982320ca7f654c832bbd95320cb6f6
  | 28 => 0x98e50d0a7d63943429f98650d0a7d6194342cf99150d0a7f63543429f18d50d0a7f61543429f18550d0b795014342bd9875390af561d4e42d7d4e5390a7e6194e429f5865390a7e6094e429f5825390a7f6154e429f1855390a7f6054e429f1815390b5d5314e42bb98a4390aed6290e42af5974290b3d65d0a42af9874290abd60d0a42bb5974290b6d65d0a42bb5874290ade63d4642b758f5190ade6394642b758e5190b7751946429f98e5190b5e63946429798e5190a7d6394642d758e5190a5d63946429f9825190a7d60946429fd8d5190a7c63546429fd815190a7c6054642dd5445190b7b50942429f98e5090a7d63942429f9865090a7d6194242cf5915090a7f63542429f18d5090b3f42542429fd855090a7c6154242b798c5090add6314242bd9845090af56114242de5405090a7e61d4d429f5875350a7e60d4d429f5835350b5f5394d42bd9865350af56194d42d754c5350a7e6114d429f5845350a7e6014d429f5805350b5f5390d42d714e4350aee6290d42bb58a4350aef6250d42bb1894350aed61d0942ebd4a4250abd60909429f98f5150a7d63d45429f9835150a7d60d4542b798e5150add6394542ddd465150b7551145429f98c5150a7d6314542cf9085150a7e60145429f5805150b3f64d41429f98f5050a7d63d4142cf90b5050a7e61d41429f5875050b7b5094142b7d8d5050adc6354142bdd855050af46154142de5405050a7e63141429f58c5050a7e61141429f5845050b5f5394c429f9865310a7d6194c429f9825310a7d6094c429fd855310a7c6154c429fd815310a7c6054c42d754c5310af66114c42bd5845310afa6014c42be5805310b5e53d0c42d754f4310aee62d0c42bb58b4310a7d6590c429fd954310aee6210c42bb5884310abe61d0842af5834210abd6490842cf9524210aed6490842db9524210bae54908429fd954210abf6550842cfd954210a3f6550842afd894210b3e5250842af1854210abf6050842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210baf4350842eb50d4210b7751944429f98e5110a7d63944429f9825110a7d60944429fd8d5110a7c6354442db9095110b6d42544429fd815110a7c6054442b798c5110add6314442dd5445110afa6014442be5805110b7b50940429f98e5010a7d63940429f9865010a7d6194042cf9915010a7f63540429f18d5010b3f4254042cf5095010a7f61540429f1855010ade6314042b758c5010af66114042bd5845010b795014042bd987548caf561d5232d758f548cb6e62d52329f987548cb7661d52329d987548ca7d61d5232dd587548ca7561d52329f983548ca7d60d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c60552
  | 29 => 0x800a000c000000c0000000003000000a0008004000c0070000001000400a000000c000000600280070010001001c00000040000024000000000600340000004007000000c0000001000c00600100000014000001000e0004003000c00300000000008000000400100140010048000001400e001400300280060004000000400700040000000000001800a000000000340030000002000400000200000050001001800500000010000001000c0060024000000000b000400200400100000009000c005001000d00040060000001001c00a001c00000000000010001000000d00080000004004000000c00200010024005004000000040000010000000800000000000028002000800400080050000016005800000000010000001002c00200000020000007000400a000400000000130014002000000a00040010038000001c00100040080000000000000200080000008000001c0030000000001c000000c0000008000001801000140110014001003800000040000004000000000f0004000000000100000000000014001000000000000014000004800600080000044002000000400000050000001000c00000000130040002000400000280020008004001800a0000000001800100000140024001000800000080010010000000400f0004003000000600000000008003000000000000000000006000000000600000004000000c000003800000000020000000000801f0000002000800700080000020000000000d0014000000c003001000000040000028009000000200180020004000000000000540010000000000800000080070018007001400200000000000000000000200240000008002001800300280000004005000400c000c005004800100040050014001000000400180000000001001000100000040000003001c001001c00000000000000001000800d0014002000000300340000038000001c000008000600000000000005001400100000010004009000800b00140000000017001800200000060000002000400000040010034000001000000040050004000001c00200000050004000004c000000c00500080000008002001000000000000000006000c000003c000001c000000000000000010044000000000000200010000000001c00000000010004002000400000000000000004002400100000020014004000c00200640000004000001efa60d4f42be58353d0b5f5394f429f98653d0a7d6194f429f98253d0a7d6094f429fd8553d0a7c6154f429fd8153d0a7c6054f42d754c53d0aee62d0f42bb58b43d0b7751947429f98e51d0a7d63947429f98251d0a7d60947429fd8d51d0a7c63547429fd8151d0a7c6054742b798c51d0add6314742dd54451d0afa6014742be58051d0ade63d4342b758f50d0b7b50943429f
  | 30 => 0x2000000c0034001001000100100000054003000000200180000000000001c003001c0090008000000400000000010008001002c00000000000000005000001b00000040008000003000a00080000008002000c0000008000000c000000800100000060008000001c00000040080004002000000000000000024006000c00000000080014003000000000000020000000001400100040000008002000000100000000008001000000000180030004009002c00000000020010003000000000080010004000000000500000000000002000c00d00d000600040020004006000400c000000300000000008006000400000000020010001000c00000080060004004000000000040080020007000c006002006400000000040000000400100140070000000003c00200040020000000000c00000100000000000000c008000400100380020030001000c003000c0000024003001400400000010034001000c003000c017000000d000c000001800200000010010002000c002000400000400060000001000c0160000000000000300100000000002000800700000050004001002400000040020000000002801400000040010001000000100140000000001000000b000c0050000000000000000080010000000001000b00200010000000002000000280020000001001c001000400000040110000001000001e00140000000004000800000040040000006000401700000000000000001000300000000000005003c007000400100a80040034007002c0000000000000c00400000000008000000000400000010000004000800200040000000003000800300180040000001001c000002800100180010004002003000200080010000002000400500000010000012004400f000800100040000000004000400600040000004007001000400100050004002000c000000000000040000000000000c0100000004000000100100000000001000c001002000900480000038001000000400100040028003000c000003c0040000006000000000000000014000000000200080000008010004000b00080000000000001c002000800000080050004000002000a000c005000000a000000400000030000005000c003000800000000000000000000000300140010004002000400400340000004002000c012000c0010000002000c00000480040044003003c0020000008000000000080030008001000800d0020000000c0000000008000400000040000004027002800400080020004000000000100280020000001002800600000010008003000000b00000000010001001000800000030000006000400300040020028000000400a00000020014000000000000100050000003000000700480000004000000c000000000300040040014000007c002003c00300
  | 31 => 0x3c001000000100000020000000000000600400020008004000800b0010001000000100180070010001000400200000010004004000c00000080080008018000000c0004003001400000240030000008001000200040020010007001000200040010000005000400100000000000009000800600000000018000000400a000c00b0014002004c0010000001001800100000000018004000000900000010000000000000600080000000000000001500140020000000000800700480000000000000000200040060008005000400b0010002001000d00080030000019001800e00140220000000001c0010010000000400100000010004019000000000000030000002000c00000180000000003002800c0018007001400e000c0060000000000801a000c003000c0010000000000c0000004004003400000100040008002000800300280030010002000400700040000004000001c0010018007000c0050000001000c010001c005005000000000090004002002c0030000001001c002002400000000020000005002401c0004002000000000000050004003000000c000c000000000c00140050008001000800300040000010001001c003000000500080020008001000000100100050000006000400000000140000001003c001000c00000040030024002001000400000030004003001c010000c00000000030034003000400000a40100020000002000400240000000000000c0000010012000000000000020008000000c0000034003000c0070000002000800400200050010005000c00b00040040000004004400300180070000005000800b0008001000c003000000300000010010000000400100000010000014001c000001c003007c00500180010008014001800200000000000000003800900000050004003000c00200000010004000000c0010010007002c000000400800040000000001000000200000000004003000000000000020000000000400a000000400080000018000001c003001c001000800500000000010000001400000040020000000002c000000400c000802700340000000001000c0130000002000001c0054004000000000040120004003000c003005800800240040034003000400700100200020003000c000002400100000020004000000c00600100060000009003000100180010004005003c00200000030014000000000000000000004002000000b00000050000002000000000000050008004000c002000400a00080000008002000c001000800200040050008008000000000000000004003002800000140020000003001400000040010034002000000200080020000004000000100000070018001000c0030000000000000000000040020002000400000040040008006003000000000010004006001c0
  | 32 => 0x5001000200040030014002002000100040170018003000c000000000000000000000000000c00200040010000002000001500040000018004000400b000800000140050000001000000e002000100000010010001002800000040020000000001000700080000014001000400000000000010001000c00000040130014000001c00000080000000000002c009000001b000800100100030004001001400500040020038004003c0020000000002402b00180010000001000000f00040000004000002800d00100040000003000800100000000000000001000000000010008000000400100200000008004000000d0020001000c005004c000000c006000800200040000000002000c0000018001000800c001800000140010024003003000200040010000002000000100040000040001000c0000004006000000100180000010000000800100100010000000005400300000010004004005c00000140000000000000001c00000000000000000000000100010000000000800800280010004003001000700040030000000000c006000000000040000000004000000700040010000000000800b001c0010008003000400400100000000011000c0060004000001800100000120008003000c000003000000080000000005000800200180020008000000400700040030040003000000c001c002000000a00100000010000000c01300100010014002000c00000000030010005000000a0008001003400000000060028007000400200040000018001000000000200040004000000000000240000000001002800500100010000000000400600000040008001000400200040000004004000000000040000004001000000000000010000001000c000000800800600010000001001000c000000000040000010004005c0050000000001400300000020000007002c00200040000018003000000000200000028001004c004000800300000020000006000c004000400500000040000002000c000000400300040010000001000c000000400100040030000000000800c0024000004000100080010004000000c001000c0000008003001000600200020000004000c000000000300380000010004000400100000030000000000c0000014000000c0080018001000800000040010000002000000000280050000000004000d000c001000c00300040040000000000400200000070000002001800b00180000000002003000000000010000000000800000040010000003000000000240020004000000c0030000000000400000200000064004000000600000120000006000800000000040014001000c0000000002000000100000000008004001400800000020018000000000d00040040024001002000c00100010004003000c003000000300040020
  | 33 => 0x1b468ee000078d8000470939800006489bc000000000007e50f650d9abec00000009eca034000129c000000000000000000000000000017f80000003035000000079053ba000177e55d1a789ada8769bac3196440000190af8a73400006f6a0020000fe6000000000000008da0000000122e8301698000000000030ca00000007c014e29bf8000c1d00003260c3d7b523caa10e57c569efc68960000796c000bd100002622dc889d82447902af1824c0006ce43f234e160072dcb8a670b04802b0000a2f000000005e20000086000000000000000000000000000063c8000ab3871864604da0001a4500003fa1b00000ba3008400000000000000000000000000000000000000000020406000001a3cbb8966d3d58000000279c042c00000000000448904000239a2a680002d515b8a3509969319d7056d6dad51a0000000000000000006d2ee98000000000000006b70104b5a0e0c9e188ff388983866c94a86c207e6c108000000000029a8870000000000000004cd9752ab1069a78fb0c40000000076902e3128000013c00039a2a7b8c59bc5071968644223b4495991e0002f9c468107c125978c00029077158e1067a02bc00015fe00016ba00000009058000002c0030008000000c000000000700180000004001001400100000010000000000000100180020074000000000100200000008001000400b00000070000001000000a0050001000000000000010008000000000000000080038000000c001000800000000010008000001400000000030000003000400100400060014000000c006001c002009c000000800100080020008001001400000140030000001000000000140010004000001400100000020000000000400000680000000014000800100000000014000000000000180000000034005000000000010000005000c0070008002000c002000c000001001800040000000000001800b000000000040010000003000400100100000000000001400000000000008003000c0020038000000c005000c0000000000000c006000c00d001800a0010000000400500100000004000000000000000000000000000c0020008003000800900000020024001001400000040020004014000400f0000004000c00500340000000000000400000140150008002000c00500000150000001001c011000400200140010038000000c00000200010000005001000a00080000004018000000900180000000004001c0010020001001c00000180030000001000c0010000000000800300040010000005000400500140000008003004c00b00040020004000001000000080150000001000c0030018001001c002000001a00040000010000000c001000c00600340010004002000c003001001100000060000007002000000000000000
  | 34 => 0x3fea8540000002dba000198657a0000000000000029b000000000000000a5186f8afe81c90000527baecf88b782dde7191edc87c8000809155817f0000611800053c12f4000083000026a2000140ca8a4000b54b0cc00000001758b760000f08964adf714b53a02be09628b8800000000000430e44000212aa7b84a97e6a8fa078223aa578c395d500007216c18000000091669db0000d6985801541688ce00001a7f135b06289b5b3000012aa610c00064e000000000fa00000000d780002ed069b000276600000007a988ca1c14000bf20000000027329bc000a481e203d4ab9230500000002e5e39580000000d18000000000000000000000b0b08050000f27000000000000003020ecc000283e8275818b3280b400002ca00000000000000000000000000000000000332b050a65e1100001c8400022c2000000022a15fd07900000000000b1a800000026270000c1c0000d2000011993dc800049c000000000006c8c0001ea9b7e8e81bf60000000aecc3949481b4963fa6d476da22505d931e7029724596800000017005be8a820002b648b5943c0001f855170000228248c0001fe500000000001634000260c00000005f81148000000000000008218000bf8a414ae5000024e00004db70780000000000145a54322ea0000c3696f8efe000000000007780000c5a84613340140000000000000000002740000664000000000003b7ce3288ac0009ea0fda0000000b944faf000000000019bab719ddea18271e0000000b96c0003d000006af2fd300000008489c7259c56825cb97420000518000016483c8b7a000000000000005b98000779000023e8000000000000000000000000000000000019fa00000000000000c24000016314f144e8000173c00044c80006a39dc2c0ce2751c8b00c8668b64b9840000000b7c00000001a70000a1c40000000000000276473f15999c68da800022b013be1bc00000000000bd000010feb38814266e02f03c985d10978000a71c9c06a1266014200000000000762000000000000002b950c4000000000003002b66bf10909648109c305c93cc231b5e4ef2745b5a98aa0b3143a000000000000000002a5e00015b000018122df80000308000000109e00000002f6000000014c60001b10b4ca873000103e5c5000014c81ea98895a00000000000000015f00000002098834abb28ce000040b000000022c446d00003e1aac0849015c0002dfa121c0000001c368b41bfa50281d86a0a4a60000834000283ab71d1ce9279ecc66f80000135e565100000189800021b00000711ac800029aa00029f649f08f23dd2c34000070015b20315af1eb64d861eec3ca9be000000059c8c0c86628927d9400000000000000000000198044710be0e79de889fca2c4cf021a7b484606e280000000350935800021cceb6
  | 35 => 0xe9aa9faa3fa8000b300000876800000000001aba6301f8d130000124e97f8000be91bf0000062b748c0003078b061e6c5ae0002f1100000003488d24b6083980001aa9000000082685c40000e047610a65b09a2fa00000e627f926e0000000a6194ec00029a44f1945296d197e6279cae2520362462eeea0fb2e408d41a5a000000000026d2000000000000004dd80000001b8402cd5640000000029b0d60000b1c353e486000304400010a000000000000000409993400000000000fb4000000038b1dc40000000c1f800028d800000027680db4fd80000000000000000003b8000145e991800046c000000000000001ff2b39277c923de3a399264eace000061b705e16c03030002ba2000151a5a500000000edd0000000000016f00000007c6820eac3a36e48f259a00003dc941192a2b9562c00014bc1cb630a000000059a2f4800000001d18f3c0a5647d000255b000000000020b70002dac0000000b470f369820000954aa112394000a3384e30001f5c0000000a932c1a3a89bc39b580001128000af5a438745000004b00000e1a8782fa40002b86496b99800000015de8188000360c0003c29d62000063b0001b946a8596e00006781d62cf0000000000000000002ebcabfa8ba359a526000062890ac0004b005ec23100004710000000045400015358619c3000017166e4285a00000003309d542d1aef4b66a5da92b2f046038d3c602a2f885a0bda73c00000001a708c3aaa85720000790c0004a50000000225064e9a1870f2770000000021c800000030662c8800000000000000000000000000028b600015e60000ee1a2696a2000182a37d82a46829005a97c706ac4000000000000002b2900000005e700006cd8d48000032e50905a0ab8a16e78a8000b8898687e28fc0aff1bc40001b2600014010002caa70a800060309781e12aaca7145d24bca6004300000000000064f00007b2845e274b06800002ad37f800019a90b02a70000379000086d1b9a55e2a7786e9eb4040286c000299900000007601a0e3eea0ce1ccc05a51d2faa8720000a011a341fea03700000000d34000ac0ab3f0001878775a29f5b1ad72222c00000006f785e827e00006e09e12da2b170000aa5400072180000001774000033c0000000334889e0c1ac0f6882e30aa000000269f9c6ec1f0608fa33c3e91624bde00005922256ae10a5e0c71ac62fd91fc92284082aa2b5c580837423580000002d1a87424fca400000b740000000248e1b1000000000002dc2ada68d8000b3f9d4e00023725e5800000015f100000000000000aaf00009e3265c0001348b07594e3b68aa20001ba5077001634a0a0c00001204d9e88a8c3000013423b00000e4ea31000000000005288f6626885040001f3e00015ba698000000000000000000000029100000000000000000
  | 36 => 0x11580005da8ffc14480008058000000000000000000000000bca290f835050290dc0000000000a35c0000000000000000000000005da0000a621a1c76f91fa3ce00002ec229e5af80003eedbe057813a93aa1fc800013e01f8000069297e4b1d8000b9da69671b11866f281fa000000000000007f8119f4da4000000082c000000000000000002d850000526ba99ccc8969e5a0d1a72213d93c883613f40f61dee79d829700000006a615ca11b00001e2871e62cc80a400aabe000000000008f043a2960000025a57ea1f4000000000012a60000c4c0000000646ed6b0000000a1f800090eee64000000000000000000000000000000000000002810000108a717800019d80000000000000000000000001134000000000000000000001c93819001e0000000a81db501010000bc9800083091e30000755595800055fadb65ce00000000a6e8a39d725a80d4a17200000000000b5d000000025c9ba6c0006eac00057621a001d8a5b00000003151528af9808300008cc000000007fdea826404e66a04000a2e0a3ab69d2b2000247f6ad92368c508ee242c0000000de600000000000000000000000000006fa800000000000001d66000000000015297d41f2e7ef00007cd25247f60000000098e2990000ba65abea2a19448ad25a600000000000ba20000000000242e0002ca0589aa8e67980001d8de72c2f96cb000198a460811800027d2b5e80009b29f642d8a27daa140001612d3635304d8bc40000000000000000000000000000000000009be0001362369965c09fc000be203587d7d8ff958950278120910000f0f5d621be04c02c8000074314580003c32da3ac5155245f8928000000073140005d580000002d345f95ba6000124aaa0401400006da00000985bf2bbf0002148000000000000000002ee6000000006fc00000018649ed174c9969c765284cb330e000000000000001c226db6546253400000000005569a4484725282ce182f34284628e0800090417ac7681324705253d1a09f389f8800000000000001e1400000008b52e2a6ff80000002e1221351800002cec0002172a121854bc000008b22e2060c8000b01a736000062e607a1ac0000000000000000000000000000000002200000000000000a2a8d147bf49a00a3c00048901b89ef82163cbaa4a0002ac200016d5a8d42748c6ac469132bfb52c800000016183fdd592000020100000000001a900001a0d79940001548000198a754000000000000004110000000163a0000c2010c2c8800000006c317b00ba8000246cc0e531000000000007069b2a466b084000000047a00002790e58613d28cb7621f6497075b0000000297c17e000284679a80000001d3000010d00001ee86269fde00008200000000000014e875245200012957dd00001e71ce
  | 37 => 0x100c351240000000000000020ca9540000000000000064f800000000001ea173e0000000bf51bf740204a118227370000a8c62b6886ad60bdb22e4fb27a6980871c25d28e10000389a9c30002e4c3aa84c90002a5200000000000000000255990bc0006d08000075e4cb6c380000000000034cbe8b21990a10b8000875a14272bc5ea86a0e12782ab7022e88e693c8158b5d583624dd9c700000004ad8000607c0000001bbf888a1545e62eee6769a941f1dc346a71a7e2ea299843d80000920000235c000000037018861e00002bf800021b2206800000000001df8ef90001bdc0000000000000052e995a7458000000037800015040001a105822676057c34e0000d50970b0d000000003ef02d33690f1e6632dca00009ea00000000924546000065c0001b060000000acd000001c30023228000842c39c56406fc8e725e8b0780005e011f087711f50000cfc00030e804795c61fbc000b1615c3000003e330ef460001d07b965f1200022af00008fe00000000001a9b0000000ad214825d3832c0000000000030e00004a60001f32000000035a000010d8f874b8ce9642da4a30b68000b590a469610000325902d0f4595200005f15ff1ee053389b24109786c0d8fce00015270001db700020d7102c0001d28d0871d491a913800006da92c31010688010b260b10000561909842a83577ac800000000000000000957800000000000000000b31000041580000000000c2a46b43bbc066328c6960000000a8b1dd267780000000000000000000000000002f326a8c000aeb80006b3114a98f96ee000000000000000000000000000000000007988f580c8a8f797f1f1e1e3a684472ad7c6c2a28410d2304bda8232243a0a826d8748411800000027526249d93ba29d2ec1288c60c6efee7de1b640000b5e00028a0000000000007c40000000000234e8629e74a4a02fd1395c42b0e800062c8000738cd9e00000006930000000302600000006fb0dc80002b9c00025d6000000012d12b3000000e00000000000000000000019780009348000058400000000006e1d6a800000006d5ab2a00000007941b000000b180000000b671d59000002d66521ec5b280a20002574973aeaa4c8157676d08a6abd17781a980001b918205d68dce22b93c041330aa3b580000ac0d5800000000002602685000000000009cf6ef88112cde5759e5900012e400024763e2478241cdba2bd32578a23a0ac916000046caaba121aece87606c62c7891477faa59b35007f47b00004b94c1600026f600000000000d620002fac000208d16703bc7b6a5802c9169600000009cd054c9f4055c009400000003eea97303e4fc6b8d00010af00000004e3a7a60001eac0001c8a0002b540002c9ca7ac4b793a000059a80007eb18425cf20061a0241a08bafd830ce6162da000000
  | 38 => 0x134b420000dec000000000017820001a66a11000088fa46600016160000d6e46f20c9b821dec2230d945dc012a5b6912a0000000000000000000000000000b5c000004f85860001d0eb35800000003041f40000838d91c06800000002b6e51c80005d2a2ba616d7c800000000000bf400018400000000bec00009d6800080518888420efd3f3000000000000000000a668d76947aae16761fe200007655aded98000003c0000484000135e000213a0a080000001ec0383826e000246ab7b932c8882a90520e2a29389d183b81942ab656666c68d9294fc2c20000000b1c859090f0fca9910a8e06d0000703aee834da12eaea905c00030e66072eae66d800000000000390000000000000000001c700002b6ae7c00000003b700000001500392800012e400000006c90000000000000000000000000000a9ca4260002a2a000018b6dd429200022fcb4a966208d25c46dd0620c0ba48d105aa3e8e8aec86ff059600015bc8f400002d70000000000000000000df800028488940001d9500000005a3a06e000198237e8000000000000000001f500000001cca9899bb200013100b7af0bbe829e250aa9bf9f9863a5b4968898626284782b620001a56000000042c80006cf000021200000000000000027a000000000000002062a750000000a172a6228fa7bcb4607a436040004b3d18900000000000bde0bd80006ea400008eae67132c0004de000000023ee80812b88480dd01ec0412b5e21628e91824aa4e38a2eda0c4b16844481fa6bf72b0ec068cc5dc0001b0989012a5a8bef228170cbc8f120be2f9ca3cba38000b3d8000000279a27680000002ec45ab98b6c3a8bd966e6b4400029a24c2950e6074000a468b860755ab9bfa8000ba68000000000095280005f2875714240003d26b261ef1be83592ad80002f760000000000289eb34000092f05f6a860cc481ea54100025ad71201f0bbf00427c58000000031614a80000002eb651197d8000000000000009de8000000000000019bc049000000004380002adb14b2c2a0001b6e000261c5f0e32401113ea0ac96c07aa9f02b89000000000000002a0f1d6400000000be0000000000000000000004f940001dc800000013281ca0000000000000000483bfe4067b9a2b500000006d1c00066fcf4ba8740000002a2b7b1800000000000002a270002d8a6400000000000008a800085a85f200014d8a7f0000892d492b67c0009d1800044380002fa80000000000000000000000009ad27ee295400000000003fd000061b81480002c5400007450002a9c1200000000000019a0000000000000000009078e206759f6671b5f9ebcd82522ae827cbe7a0d60002bdcb6400000001a5c862000000005f874e0f8300000000000ffe61256580bf2534a9f9580000023c0000000bbd84c215f88030001e
  | 39 => 0x2ee0001168a9a876c7e0f03900000000a2467a0000000000047000000000000000a64c0005e79d480ce211216900000002046c3e80005b88000000233100020e2000079a00006ec00008c0bf01ff600000000000bc200a000095209c28f318d44bb568a1e20747b6b80000000000000000002ec0007dfc5ca674e13486e0000000000093d80000000000000000000007c061cc000000010f0000000a3d61e6000000000016b8a72800000003b70000dc01f68000a05a55c0002010a87ac300002b9a6a58bc80001915000000000000000001a9e0002df224ec00012c94324bdad9559263f40000000be42239000114e0001a1640f0000000205218b0000220e0961931ab78b5ea38bf7a4ea48624395440c10af29cf451b0ca12bfa35871a2d1ea4f84783a408784a1a49a22b2f6691018ee2e2049f42b0000b3a3106000004a0000000b2a21c2925e6404a087267a88388822cfd5213120867aa72e617c000a6d40000002d8899e03e292627c40dc8a5d2f800001294000000231092d000004e0a8614a000000011dcb2b0155331800040580004a9000019d2ce0b43907a0000000000182e3709b736720000000000004729190001b025359b711f392fa87788064e2de922095f0500004288c166f9b56a60e1ca8000bd61280b2d152100003a681a42136a2a964a759fc786383aa4a4cc8e00008867ff01b0000000083300000002dc02b996eb37889c600000004c3a8fc0002a6c357045a29feb5a1fec1227e1abb8b63d54e0a81911b98defe3b46c5668546040002e00033000000000005518000566c000683eb42000097900012be397000069c800000019d4a8cda460002d300001ca6000000000000000000000000000000000000000efc0002800000000000027c2ab7c1150000000bde800096d8983220800000000001e4afce0000000028000000000000000fab6e78b7400020e5000053000000000000000b3d2e850e83058000235e71e1e5131200000000000000236246e0000a1500000000000000000000000006de800000000002f30000000000078e19226bc00000000000000000000000000001f2090282e60000000038a8900000e6a20dc0005ac2a9a000000000022d270b98f00000000bee8000bcb958a090e8809728000910800000000006bd25d4acc80003988000b7d169c0b90cc90001aaa0002bbe00024be810c000749a87d29f83302841ddc0000ed2000000058a0000000290500000007838000767400012f8f5e6270b010589b0b0000000752c64e0000c6e4469d760002b826660054428b000456adf88400d865df054800012783c52a3a2de0a9e0002be8a30af098d28000000000000000000000000a3a00000002762899c0009eb1d92a9822cb000000032d8000543e22fa104000090a9c8a38821506cab0c00028266
  | 40 => 0x23417664adc0850002e4e00012132b7d45f78b8000a8b800000009367c6c0003f4dfb0000000094faed2000144b00000009c2000085b00006620000000000000000008de000000015bf737a46c00000002f4400000018720d90000000266e8455e160002b467c4400021e6ce9a1582505d900000000db24f843ca407075f00000000000000000000077d000000009bc273000082d00001cb166042e007d3c76d400000000000000000000000002c0a0001ff450c173a7d6800000000000ec13de41e00000000136984144e0001d06000000000014e888bac8e723800017c00000000000afc24a494191d0b1e000000000000000246c09000000010501186f0600000002b825185699e5e4d4c00000000000001428a8304fe00002d079f80000000000327ee782ca80000000152000000000000000001b6b2fba4aa5ed1d9a000000087300000001d4424c80000000000000082800007ee0000000bf80a16bbb000072900009d02b4a000000000009a30002774a5d2a486ad516491bdbc872680ca8af0cc83200aca000000069b8a208c7000938500000000442000096caab80004d319f09129cdd000150d57b27f0885834480b00005be102a3d914acb9c952a92d557c3af80c39c5800000011cdbfb000000000000001df0000006f464a20a000158c095992e0e493aa140142e000093a0000000103c000000169ea7c00000000000a028a92000007a0000000000243496e0e3872093840002c94bca91ee000000000014800002af2000000000029ea1ac000028a000000000000000c843e5800022d0000a429cb8476ad4a0000000000000039d1ce49640e8a5f407323c6de6f4a6097c4b88f604f0c0000000000bfe201e522000072ea86300000000000000a75555005e2a573f7000000000004b78f16ae428f69011eff00026e79cc0000a5d9a7b0000000abe1beea4d9a5e1390a6650e0ad271ba3ba000000018d43af000000004f1cc010080000000f9e00003ad1b498c478c8f280000cae465d38d000000015122922b9227207892c827d000072c40001fe0b98c16a61a00022302c4a9020002c356e368473658000a22000000014450001c4c0000094820a5ba6b38000a8480000000000000038e0002d009f816b6b7915c08b91a041469d2a716c798abe8e5eb96043127e8840a14c5de24d0000c3f4f7100005821f0ec4e35e256502b5e5815ca6ac1e52cbc1de93170aa08b269b2d922fb5d2500017852b1200003029ce002c000035051c40391d80000719b8e00009bc406044980001d50000b28814f0002330000060c4531c5d000000067c8ef451c19cd000229134301e80000eec0002ba8142e0c6000208000000000002accae3dd6f000299b000000040a4000a9182a600001db1f158e826b858e2d38000000166468185c200000008068
  | 41 => 0xb36838019600023dc0001e5c00000000a3961c00006b600009025081aa030f0a6c30eef2467ba1061c800000002ffa5298f44459800055b8baebda0257c2da67e9541dd88a5018c57920cb8ca9ad1692000000000002b583ed57b80004edb0f83de043393d2b1e73c400021bcbf80531f0f2dc800048800000001c40000119468c80000e566a6bb700007b217c40000410000202810680002350000bc5000031f8000408a85275740000000a5861280009631bde3c640000000000760a234276157a544c0000000000a3b5d6e00025940001ca230112c3000149e22a891d6ed8a080648bd460a654091dc0003fa000067d0e3e095400000002fa46a2dab94531080000fbe0c2cb826cd00a44ac043da44ad123df8000000000000000000001c607a28000000118312e000054d13e600000001bea99465ea49200023fe00000009e4a558a7c47ba0000000260147600019df000000000006f400000000000269b4f967400000000000000ae7e662677000021fa08eb18000080300008a580000001ee29e92e92461000000000000000000000111483a1e6c880ac7c00000000000708a390000c2780003e80000000294c9dfb0b00000f2a9eb84501450000000160a0a4c0005b58000000049e0000000000000000000008bbd98e5e92c8c7a08000366000000013542c0ceba350d6d83c7298a8bc2a6822909a4adb1bd2be6af4da2302900000f3a0a74ade000264a78c0000089c7d82a4126a4d8090a9e08ee9317843e000141a5dba9e68108939479a6be2470896000191451897f60002aa202399500001de200024b7000000020d5b04bb7923000000000000000afb80002b51b927e8011a0002c4056200000002adc9af55128e9898223d0924093a42c00015449bb4aa08aa8000314b0c800100000000000000302c6380ef634394e600019ad9e140000002c8b00000001dec00000000000d70000423960600000000002b88c06885f000000088d8d3900000000000000b050f80b6a11360000000000000000000000002c624588000a71af21168e2687db800067908497da91ea00001844b61d1a0d540001ed0e9a0000000000042237c2f0d6251178000269c00012c4000000031b2246613ae061aee06866ac00071f034a00000009e7800059e25a000012028529a74370c00000029bd000000000000000001040752531425ec00000000007f6400000014140002d06a560000ad59b5800000000001094000000000000008b542511d800000000b3e000000000005640000000000075000006378ce87441a900002f2a03e4d64390491144a000000026c29f789e42fb0001d9043c00b9000112c2f4800000015260000000c13000058400000000000212ddfc7d325f000004ca000044e000179a01b6a0b0030000000000000000007d510d20000229
  | 42 => 0x12aeea2333c3d47e8c00000030886cb84f81dd87b88f680000000000000045c0ef83110002ae80000b32b190981738000007e00000000000000129627b000000000babeca2b29792c3c02c0000bb9066cb9143a21214000b8ea97f33441e79ea93cc11e8000000177200018bc2b1869e84b0a440001b6c03c870a674a0c886a9a1a000277848380000001f7090f70a000023e200019b70001d583b9800026ead460000000b32026700000009f2000067940008ac40004f26d7ec208cf600022fe2614bec3af1fbe214871b0f4e2880000000751800000000000000ba600000000002336000273a82a800000000000000000000247aacda150000149800000000000000000000000019b444d1a257d200000000000000000038c0ff2000000000014a0000081600000000000000905c00000009f600000001b300000000000349a9f80002072767ace6c39000000000000f0ab3c6acce6c06793f900000008700e240bc9c8c20e0b442be583a825262c837034200000003289e060002652942294a00000000230a600fc0000655a0bc00000003645bae000000026e10f223480000001a237ca00009dc9857000302834b0e942171882632800073e18a68712a793da9357320aac8b3aa95c281a84c0001172000000000018c27e4e2246d2a2f4bd085c66a18000638800000000002051490898a206000167a0c517e6af40ede1bc120d0000fa60002ecc5d72b22469835b421086a3e30a4b00000000f680000003060000000000000000001b3800011c800026e07399054176816a00003e6000202b0002f82000000006080000000000000281818c40004258b4a00014541c9400047a4ca800022330374000b5b518f0cd0300c1b80007021bc282cd2ab6c916122e59f1800023464998000883ae5c2758000000000000000000002d71633ae62000000095a0000804a25e419026d00028660d499720000a52a08800048e80000000000649a4cd000000000006a86ceaeba0002b1a707851e0002b1c6a90000a0d01f4000000000000000000000a3ad9460002a827d7824fa2c895493253ed4ad628a2e79a0c7751fe80bd1a2e0000d3e4942f1742d04062141d3c11ac7e40002e100000650b594000000237c0000000a5f272c4e000002770174451048a8fb1a1266c2ea8a9100000002ffca75000024d6d620000e60a2b2b533b50c0a7ec60880001c200001984000000000000000000000a21c000000000000022f20a7a0ea7928a569216cce5e504d2000000000000000248bb97cc000031a0b28364dd6dc408000000000073e80c8630196015fd64b0a716c95b3000048013e433aa01800000fe3998f029cfa9d277012b4a58aa4d2c82802437800092be9343640000000000000000000002cd200000008122b40c2d13ee8610afc7f6d5ea6390000000
  | 43 => 0x30ee597cb6a38719d036a8ccd4a693b800e856e180c0290cca23d95f903004209f2159b0340002c6ea6e586c94ed9e2742868432c80007eba9f2a88a4880dd89de0001d400000000000181460acd333869acabd521e4192970e9bddf4492d84230c4acf837a0c1b00000001238000000000000003070000000000000000000000000d2e0c81706c1c80000000000affc000b8d1908000000047783010001cd60001efa00000003db1c988d10000000000090204151dd125a0000000412155c00000002bc1f84be12445000282028113da6c49e1c1b46f8e89e8000000000000030dc000000000012ac6c88970b225a08000054397ea204bc6a34f7bb1760c34a1f800015b698e80000000c0dab2411940a2499ab2d05a0002c6c642c0001ab4fc29f023e400014120002b8695e931ca60b112a3c8c66c0e8be28569cc630b2f8c02000005cb17b2356a28292800002108a2a1828000666a9ba000000000013ae0000000742400096919b500018a976e04ed49821f000000007a2140804d2480640df996e180001d06efe714220c4c12ab08519af69d59de96bca3f02c01aee8b4d7d42e8010d80ba1a494b877c23b2d6c4f40000936137c0000000000000000003a57448c58aff9db0633c0f6bf4ae0caaaec4a2bd861c0000000bdb867eadbc5ff0001bcc00000000000000ab1800000000007060000a8100000000000035830800000008b70000143900689d272a8cb93d88cc93740f34000bed99402460000944000007c97f0000136a0000ae885c188c0000c7aa1b80002cb23e800029e85c0a99c289000002e00000000000a092b8c000000059d8000a8900005040acc5b3800056a4351000036a9b70c3e0000000079699268ea70200000000000000000000078d104e5a8c000000116a00000000d2ca1e000147e4e4a22361d98d29b986e80001788a7b00003c100004cf800075e8000000053616a83f15fb0601a3d1cc290648903d52f626f6142c711a96a4cc1d02736cc94b4f17e1ab2a57b25081fca600a8a54ee4470764b8ea4a9d1e259ad736459d5b5830b105f68000756892cc0f000000022c089f041879dc00045d00003d1b0b2a74c0001fa10c43c3a5c85795f975c69c6f884231272a6acd000165000000000002eb06ee0f3583847d7c2a118c1275344465ae9ea1141943baea2075a17b37f395d5600303291c21c600000000000888a7000001868000916c000843885a9aa000000023fa8a00000b1d2906b7a9859000219e0001fee508473e62b1efc6926dec6730113a379ada36e8ca0b080000b6c91c358c284a6155d651d492c248a10620000cce577050a30180001d880000830fae13ea3a872a800000000000000df2ad384a25308000505800000000000001f722e100000000d521c48000000119e532000093384a4000000
  | 44 => 0xab0002e54bb0827272d0000bcc00005b151461db800052f80000000000932a6cd00000000001c03000218c4a200001da817c00000007f9abce0001a88758c0000000000b78aa6360c000092c69e47ae8cf4ae3a9d027513d1027e81a8d9a270a25c75d4cb8e089d82d4e817c60dc22953ebdf8000375000047da24448d00000001a262088000af82bc8000026c10c9da400016839536b7c38a97c2b79812870ea5de64c000075d000092500000000bfd0001ef03d8dd5f0000e886d5c0d80df000083780006f99cd8a7e80000001d007638000ae7895ab2be3e60000000000245ea47854f0001708900ae500001831857a4b800021d278a17260001a420002b410002cba4ce196a18784c0752a7ec9e6297016e1c065ac40028b3284211929786e8440986c30b80000ee2000000048111a2c07800000000009faaf700000000000000000000000002dfc3a38846180aa3600026d8b07162a0000000000000081e00003c8af80519a6da680883e0000000590000000000000001cb900000007f001061b1dce8bb68000a6758b112240001ce800085d00000000000488adfe000002a1c58f8a0001b96324452e0000000027841c0ca80000000dc44050bac581df8276980000000000203a6c1a942450921cb8c4fe0000000000000005a15f799cb2b8d8dc39680000001b2842e8000608ec16bd007de7a727ca500000051325dc00000000000fe40000000000000058d8000000266a00008fd00021580002c440000000720c0000000bbc89a42b43b08000000000000000000001f2a00001508198000052400000009c883b986a0001302be9886e00019c40000000000040e00000000001d910000144be6000000000009af1ef8a63a9fea3f800000011008ab09271350000a3aa88238589527d4e6ec9c400008fe1784b00c0007032bf200004a0000252a036800058100006ae1b4430840003271b8992740009c98000000225f5ab00000000000000000078b189680380000001d3400000004d42e1cb9208b05eb915600000000000abe0000c463bead8900014aa000038c7b600000000494b85000000000000b700000001ce77e5a2270000000bce000089f80008920906414a67c000221e000000001000000ea00008a60000a5e800000000000000a5009906bd77de522c2b0ce86e2c000b2080000000000000000000000003bcc00095093a8000025c725a5325b727e892c000018c800000009120000eae7990000000184c9d11b9800002e25839388be5c97a0000b604c001eea1b400000000000002dda0000000000000043800005c60000000229d000000000000f0c170da06a9d4fa8510d6a8291f081240000aaa400079f2b5298aa1fe99614424202690b298000bb180000000000000232098f273800022da1b20f760002fc984d80c643c400000
  | 45 => 0xaa918a00000000e10ee40000578000000000004b0000012e0001d2800000000000000000000000016700000000000000000000000000a7600008e7000000000016ab31c00000001f777128000000000000000004950000a54800000007fe7e92d2c000000000000000001eeea59aa6d4e72e460fbc3df000000000000000000a84000000000000000a698e6000019300004e000022770000000000000040694ee9390468b600000b5beae600003590000aed0000a85000113e445800058e05680002c2830a868c0b240007df2aa000002091d300000000000780800059b854dbd38000000002600000000001b82bb02ab8b4a178300000000000000886c000000211a475000098e30920000dda0000000a290bbec3ed9489e41a50bd829a335f8000000000000018fa35c0bd71aa8e7c1440000872800000000001fcafc20002b7e00000000000000000000000012760000000b4500002090000b6d00000000e7e0002a9800012bf0001aa25292735bc780001eb10ce1b7800091fa90886407354ff0000497814ab9ba87f0001dda00000000002446b74aa7a6de40106ba9b77593256a01724548e380006331b761ff21947cf112039d8000029c0006be26ae00011ba8eda672000000088b26a42829c9973380002190a680000000ac600003c6234062c2d960000000000000000000004e9800051200000000000366c00000028950000000000000000028c69b2c0000000000b5729a56168a700000000382ae5200008d8000082638d80003edabb60002dbe1a20000000264226194566cc85706a94eb08436a08000000000000000000000000000000006549bbc000b7e4d4eabc072e4e319a44ff92830ed1e8f4b51a54670026221859af7c517dc7d443ce12b406213aebd200000e50138a7a54d92f025727cc0fd800094281c20000000a77ac02000106aa69800053d8000000000000018ba2fec000000270c00012c7000000042422f613c6bba00000007af5e78a92e82e000252c00026349a380007df4000bdf0b6c0002b3a4cc8000000000000c1df8b8780000001318253800032b0b6e100107e36b0116ba419ce000000088e000000000001d92d69000000068880000000000000021e4c18db8462214e00003e1000000000d800053507308ce400000000000001b7000016af00017fe000000000000000000000000000000000000002e5700000000119cef000000000000000002ff60b580004d180000001a3e1c1c0006e328ec75440000001d500001d9600000008c996f084f8000b508000a9f084a3f5adf60001d9c00025cc000000000000002d31655b0105385bb2728b664ce4aa200003ac809c16f0556284c52b000000000000008178000b9a8000000000040e0000000309c00006e21c321020001f7e00008ea000000095b0f4e9e525
  | 46 => 0x3486b5800033411e1000000000000000000000000000016d800002586a27d88b346c580006d300000002aa6000031e6d21b2046441320001bf235f564e8e20000000000000000007e3000070900000000851000108243322ec0000000227224e0000000000223b28b800028000000000d4600029ccafa80000000ecf8f5299e96353f237b80a853422bf0000000af0302a00028efa76ab16000098c00029f300000000000ac20001ce5c3f80000001a39490a0a2709876800022a099c2ae49f517c00000c6486da5353779f364692ffe9f719a097426a00002e83000054200000000002b43334d64a000243645019f600028513ee25270000000827019f4db82e06026bcc8ad8d9c418cc61056ae1622d80002face3c2180000aff5f2722109440fd2df077db10e88de51cb0495407f5953893e924630891525e280004ba9b2c1f24000a1c1e1e000239600006b383fac7053e0abc3a1162200002d4a9740001bd86141331c745d79ed691700006a30000000097220f0000a84e69e00017ce17b80004f3a058c36016c2202a099a69ae15731806000049c00003c04f04000261000005c247815280b225064ee000000070a15abc2198b5213ed480000000949400000000000000000000270a00000007fe00e35bd804c1560a7b000000000000000700000000000000024ec44c6682335a872ac1a8dc07b11f260104ba566178e00000001df40004e599f30001e7587f0000b8c81a660e40009ac8000b8d8bba94a4000000135c9d7891f2be9aa84c22ef000029b2000000028996f200000c124b8034a5a2cdc00001109cc4f4a81295117ec8000000000067b00000001bba186ec0883d8fe0617051f00000000000000122c8dc10800009590000b3b8a3296629900eb00dc000000000000000002b7abad0000000000000000000000168a770610000000008f4000000056a00013a44048000000000000000000c3c00032e00009e815da00011b61f950a4802ab6888640009088000682c2db7f280005a00000555ced039530ae00013649cca996b2592063fe992c0000f985ca9f2215780000002fd10000000000184800000006a7400000000000000000a4887040000000b038000827800000000000002322000000043a80000000000000000090c000004ea9a1530db6200000004840c1a0000e8600000000002fbe2030d1e5edafcc0000000000000000000009315032955a95600000000001444000000069900006bfa91c00000005ef8f309d1c0009556d0c574c09d96f28e01b088e854f1f42a7ecdb4209cad800016420003020a4f0b3c749c994066c0000000000436000050d94da5fa1b5403a400068c04662226de848500000000000523000099d28a23004056000000000000000728000aad159e18913a20001d4f35740000001d4d72f00d20
  | 47 => 0x9028507f10000c440002b300c9dbaa7c7000000010ae00029a0aa180005552b989b10000000000000000000001bce000000056d0000000000065280000000000000000000000000000af1000306a000047e34d30f09621df2a1600004aa18660000c5100000008dc0d420192070a328200000182d3f5c62a34fdad8b4e2d50ad7a0e647d07f6b2480009a6087c4a786ce00000009038cdcc0c09250001c5400021a27a58bd513340008f7893e3e9c0007420000082169a9f68000779af5a0002ae00628bdc3878000000211e000000000000000000000000000024582700000000000000006cc00000000817fb07960e4e038a15516e000000009821ea00003cf0000414a490fa200000008b998a4446000060dc00000026b029340000000000000000000000003f78000c31800061486e3a3590d4243000074b0000b9580000000000049581a00003b20000000000156800020b8000000020d8000000152000000000000854596c000000224a094da6a0c15704b6440005644ab6000271c000063000000000000000000300a0000000126052212209a6a9fd72812a29d79ee0000000288400000000001cc8103400081d8000724987400006ba00001ab7f18bfc08ed71ca4526c0b1226041a391aa57d0000bc48ace24c003d4f8dbe4abf1d360002b1b84319ca0000de0327987e0000000000000000000004930000897034833300002a0000000000000001ce1bf680000000786aa900000000908162800000000003dc00749bf0000000000000000000001bbc00013d213a1e48000204500000008c08000000000083c0c8b000000000027180000000411cd4d19c1f58bcb1326a9c000000000000000000129c0000002bf90000000698800055285b20002f5e3298000aca000026b000000000000002d6669d92727a00b16000000011a9be229085980001ba4000000024430c2000000000029ac000059200000005b21b8f7f400000818000808ace70001d22bd48000acf4000552d34a000000000018413eaa8088950000a13c000714a3be7ba8d5ba2581992e90cfe000000000003d62e48000c11aba4000092a3a800009e204ea8a70000b33015698b800038d19a88a68cd4c3d11e21b728380000000c0700009d0a42300000004670000000000000019123cf80004a3a04c00002c600000001b28f346e46dbc44e18632e51402621aed87b90000000264c9f18000b69a06f0d3d38200020dd70f8f4cae596c2b0fafb80072d585b500000001822000000025293d44029e8e0000000000000026a2f1699980002bdc00062d2560000000000000000000000bb41d7842200000000000c158000000000000fc000a0ca6de40e8e827a3492200028cc4160b662b21464860963f0000241360834c0000230b5d8ad06ad0336c3b233e93ce
  | 48 => 0x18d00002fae63200000000000000000000000008a400000000000000285000000000002806ad400000000000000239206c4900000270e690141e000000000c8ddc00012326d380000d800009adc0007e840000000eeebaf8bb864ca1662198000768a10a6f1e0e41d71dfa50d00008d4800072c000000000000aea2e02a1c0000000000350000026a8000b10800091100000000c6ab6e031507da4d0034000000000000001f811318000000000075b07b29031ca0309a3347848bb2000000000000003669379000059a59b2f20000000000000005ea000062a303b0000000000134262e0000aada7a20000000000000000000000b380002ce8c723731b7c0000000bc22d6e7d59cd25ac9afa930149400004ee0002e262499cb200005405cc8bce95daaff9be800048e164610b2e4a00007dc000300813c0000000000000011cf239000022e02fe00000000000000318a2ae0001a9200000000cae8d80001e4600022639c19f4e2d40af39608bfa0000000000000000000000000000000000081640000000000bb28000000000094f1b29562510a4bf0000b2c1e4e1a514964fd80000001a1335800009061fafa5021e726fd2f9a20c0005e8800008117ba93c019c94d8000c298cdaa49800046608934905b4500000006288638042acaea53aa6683b4ea625a1fc27af28c800000000000000000000000000002928a40893000000001a25c4a31ebfa2f0c9b0a97212baa84262994c000000000008fc0000ab8000272766a800000000000002421000039600000000000c3206eda3800000004f1c000000166f42316f40002c8000026ee000177618d2bda000000000000000000e5200000000000b1a64d80000000082000000000020a729f000000029f500029b62ab1c7770cb10c72719744010000bd5a6680000e800002ab200000007e8a4ae0000000659a0b2179c0000000000557800000012d2000105e00000000000a11a612bb0bfca12663e4c18464d5490080d1c772800095c00006954c9296280bc09aea06b2c88bb9d6217cb29000063189e877a81d061e88f80a18b561e640000000000000138a000000000017300000000000204bba72da01d38fc4110185049d000075710a60c0a76e89b14b65baab012969ae618f27953ad2b607bd2a610001390ae24000a90a78a02a846e048c36bc1f00000000c3a5a90fc80002729b981a11000000043d1562236597c0002eb87fa83e400021520002f4a4a80000207236489080000000000000221a0640446000188046baf0200011b346a4000000000000000003b1800000000000cf8000000000093100000000000148400068a8000823c00000000004f89fd20002bb4ac65b60104c00000015420001b680001b1ea2040001b3ecc200020f800000000000e0031c4b08
  | 49 => 0x2213a85e0ce9f0cb80adc941c85881e80000000000000000005708000865800085e00000002dc4c2e9d7c0000d800001970523aa9454718bb72feb970000b520002d046f84919772186200000002e680007f32e049408000c3500007c400006b9000000000000002868533066034e80008532e8082da0ebab588082d62a0d6112a1f83b152c71ae65000000ee0001366000287a000152400000000000000000096a5cdabd89568000a1d1aae33000009b4000083d0000a894add00000006dc80000000278128c000376000000000000000cf2000086200007fd17a42988ca299fa4e89e60000eed00022d800014184dc2bb100002387442620000190eb08a2b870b208788a90927a5c3ea13d0f4867c5fdda852d220000bd634485740000000000131200000000000c8f000000039b8940adda1567951d5ebf92bf547f8000059800000014f3000000056a00002c38000577400000000f890a81d625d987c9aec6a05582a2817d10e6a274aaa90712ce1a1800000000008945ec4bf1e96c400c0000002cb600000000000000ad300004ae8000000000000000000000000559a5121c3a92e0db97c612680006e714b431dc000b22a9c101f89bd12a9c91c1e80006b8c000000000029f69b79322132071c2a955c8482694a67a457002482baf0a8870e7804996a63c68e4c646845843f2e7e7a1ae0a571059e9959b3f04decd81d84a2f23824da132165d8f3864676188047138000937af945038e9800000000000b143f1a26e0001a7a000253a0002da41ae000000000000000000000000003d2f740002266be18000604089a0000000000000000000005de95300000506b211ae200000000000e8c0000191000000093f964400030761120710000000019c9d3b0002da1149000041ba49c3b2210f5c3301800015f60a588bc0000000118c000000000091f0fd06c610601e897a64cab0ab7d2903b033a03645512f83dba2ca0000000836d06600030de00000000000000000036871a4fec4e1c000537b0370002f1c80714583cc835600000008b7ac32000240000029387a4400062408921f4ae68000000076f000096b92ae0000000000123e082c000000290116e8000000000000000002379e440000000b481dc66ed00000f4187900000000003096c36a0567d2c0009d711040000c124bb8000000000076b9f95345a3d8498800000002f853fab80000256660a000040623aaa9ac0000000dd60000000a968a1c000042a4ed000037a8a880000000000000069e405e6e7c75ab0d8ae21d5ad9ea63159d5372e28184a4d40000e480001cc43eb00000000ed863d08001af01fe2d6956aaf8a4120000db0000000002218ea00007380001a247820000ae1ecf2000000005827b094b4000b42297e04e605a9b907a66a6aee0a93c43a19b80fc3510000b51
  | 50 => 0x79c0020a9c7e8d329108ef18a01fc22430001ac08b3800023d800000012e8000183cac22e447a3212800000000c60000000000008d86529c516e800000002ac80001c5d0f87a5400000013520000000400071a6960000893c3f800018fc000047c01e18d8219d1ac50fd88a81d4f065882a3478c47c61f0800000026f4c01282800000000000000b1e980f000000000020b545795ae0de88c8000000048680007b0860f00013165f5800019001d4023c0002581e3300000000000000372800000000000001e60000091e0ee400000000000001e680000aee611400054b99689b22cfc00011220000ec40000f62000000008506af0bb140406b80000001cb6530131a7e4826a447800000001c50f3116c53d073400001409a4a07c80c9c447c900009f3a2e80a8ad600002e4235780000002dd68d4cc5c57e120c1601fb86e21c5c2a34000000000000000008dd80001ef80001f200009ae80008af8daf0000d320000000b6513c48861070062000073529a853480000001da80001dd000000000000f5c43bc00000006d4a5ec00000006b1000000029895f2000060e000111000000002078000000014d00005e400022ee3c48fee54c842500025a8a2c0000930c79500000000001142000000043595fc06a9d600002b200000000000000000000000002a74ba1800058fb0100002dce0002a0a00000002f3d04a0000000044510c03800004b164201c900007188000000028069dd00c891659c0ea6a9200000000000d8e000000000000000ca2a8aac280001e5ee74000030c0000be40000240bea2ab529d09920c900002a9800040780000e9c000bf430640001cf20000aec00000007e2156c022800011480000001d9856a89c491a0000000000010980005211f6800021ce35d1d4221d40007250000ab5094b0b6000000000004878b04ade11f813125f64feaad00000bf016f800000000002b701deabd800000000000001eb800000000ad8000000000090900006490000b551ba86b4e664000000058f2a3c0001a001f29076a8000000002c1b000268a000069d7b3a1409f780009b8af3a000270462ae2a60000000a8380001baacbe0000000072ca180000000c148000000063609740006de10ec6570000576da7cb14800005780000000c7cb23c9438d0800049fa96e0001ca800018d602c40000000868979aa26636800073b0995375400037f00000000a5409c40007b782104758000a22e0505f300009ad40000000c4f1702ddc5d184815182dd467e0000737c000c100000054d41c0001dba0002f5c117d1c6133899f4dca61500003b6321800000000005ad0000326b01478892483ec41171ab1fe4a0b094c456d4817fe887a928a4642738b48878aa30ab48e3a6ab28e713b1bd08f0835d31d1aa697a8e06a9da7762e4079e0001fb6456080
  | 51 => 0x3b9c950bf70000000000038b8000bf2c39ac2917f2857273c7af800000000004ab4ff03024f84b59eaee0000000000096e0000000039ccbeaa3021206b27f2293000080a8eac6e026b8000000078f0000014a3984f080004b72596a2d11020721f2603a9c5a1998000599c0000000956000261206fae7a4f1626a00010bc9ba8da200281980001240158000091c6a5800025ec6578690265c9740001bd672408be000000000000004c30ce6000150ab4ea6065a32b24a348f9c19f582c7f72fcfc23a58628e300651e96e45d415484b994ca3c90a963361c02a21559685900009a014220001522176000079b840717517d20000000000198f00017bca85a1381924d7c00023c6a07000046044ac44a17480e006440000353000000000000004b55e4c95bae883230aa43718d30436a8da98c8cec0002894000000000000000002d1666993680ab00de0a06cfaa7d01f521da08ab7084f20000000bfd190400009e26635d4c000000015400000000e7000013acb8f80000000000c3380005fea8362a601022ba9cbe0000bf2c1b03f9470000000022d90a225e000000000001ab02308e929d39386000000000000003418d5676c8ef2a9f5bf30002e1a00000000000a4f00006b2000000000000000002daa66596140000f7a000044cc4521a6a569928c40157000014ea3ea20a6810000090b521227f1034605af13196a780bab279600010c600004bc2edc0000002226000000047912e000000000000000000088d7cb040c1ed80a514eae84846e58e6d02d2e2cb8ae70002fe600010a89469020a5201ba08621141c3689c7e353220000bfe00025380000b300002a328db12ca066afb491c85cc7f7d3f0716079047449981e015ce21d204e6cf9aff0ae0000000021cb2680006f0000000000003220a4e0881e000000000000000000000000000000000185800028ee918800000000000001d9b59fb022023400000020082f1ac05390260a6bd6c689159160000208955315d44a4120f6e816de5479e8bb7303fc6588cb496b29954d600005a41ed09a5087b731c53cadc5d2400025540f480006d4a55d7631a4e1a6185e5d124e61bf8d71437000025fab72bf340000001c6600019250000a5c000000080c29b4000000005c8000000142660d0b9c3fe0000000000000001ce000000000000008de80e80001e0c29e000048718ae0000000000000000b800000000008242252000000000000000618000b1f97922bac00031340000000114818134097ba944af7802c541a6888e4078c494a3948850f2c96a800097000000ba19760000000000000000000000000000000000000000000001fd470545208a31e520002f960ebaade261c0000000e180001ad0ba800000000c76000206ab63853ec3f000009f40000000000000000009d81cc87a005863
  | 52 => 0x17f40d502d50000ac020e84cf33bad56b4099095a8400000000001a48000000000000000000000a31af0807200020ca000000006f000039400004f2ac9ec261e1aacb8000a8c59786238000000000000006ee426a86aa7b55be65500000000000542148aadd179f08fc00000017ee5c299a258ba39e59fc0000002b8a0000a724f5400021799c658680005fe036c0001e840001c7d00000008f498f68c02c915cd000036d800000000004fa0cba573c0007071fb50000c56a6ec0000002e0e3df00000002e2e000172200008580000000000000084f0000000000000000000001afc195a54c000000000000002f9800000000f140daa1aa7770e04a4a59ea7e45ce4d591d208a18ec36f0f5a00000001d00222215c0000000000b42af3c96c23eac0e000021b4c901eb8727704ad5ea1f000013892d0bcfaefa0000f108a900008c2165e000000000029c2158911261bc00052c000016b0000a3c00000000000000280e0000000000000000008ce0930000000106c876c19d000209f00016e000000009db0d547558c28992000000000004d39cdc5a4acb800002ff000126cb368d8c95ca75b51babc6107927a9a300003e49ffe4af00006f05c048a3f0a245c0cf00001e267f1077764182d20001f790000000004800000000009788000790a4280002f926c7000000020fc8e3ee556d7417a00013ec7e98000a366a1900684720aba28db9b09b48dd1f25a2f8d721bc9f40929d1be5e800d14e3d35500000008d5ac0c0002bac00000000002aea00000000000ce25450cf855580008aa000000000000000000560999c0000000000150b137800000012dabdb2429000000000000005392fd62671c6a000000000027e47a527fe4b300000000af200030540000000751ea560962bd4bd9000030d0000c38ae949a18000b0cd96c0002c2e45e800074f6a1c85d9dac1960000a26278e0000e420b34000aef0000945800000025c60001fba89cc10e1249af300007d64ec2c106f1800039c800001b88447aad0241d78000000000003cd9aca840fe2a1be4a8000139a8c180000000616a0f00000000000000000000000006b3da1e00000001b6107400025f4b695eadacb241b000284e20b800000000003a7800083680000c2650e16500000001b8e000171e7a8063e69a1f60748027b15528129c483820000cb00001f8e5672448a9381f33e5d902251850c59f40000002e690000000217650c000274a000187000024c70000a02c4400000d24000267958728c0f8e92ceeb2bb5800016a00000000000329147c00025d80001a2c0001ac26fe5d1c6b654ae01a1b6a0002db0000235cc4100000a100000001ce290c86188eb2e180000000000000000012450001d550001d5388446be06a10c25c4143e02ba6c67549e6675a8000000127d1b597ea00000
  | 53 => 0xc8000000000000000af1000000ad9fc00000000000000000000000024dc45d80003a70dae4f712681d99eae8bad12e00000000002ff0b0fd5e20634474000286100000008d50f9a93fdfa8814c2261cf0294000310a0000f2000018f7727800056b0000afccd00000000000000005ee00000000000000000073d800000024a513f00000002d864e7800018ce6f2a5e6b0d6ba2f1800021807bd90ca49600000000000000243a70429d80545bfd6e8d4b882c25b29ff024ab24000000003a4481457a00000009950000bf29b6f1538af463e2d240002386664a3f68ec976c4859d8a0be40009be10c827e290e45f0000545a0542c0a7001dc1f908412544561000010286b500019176fe2f0e8f212ec84585b433e937e8eb9f3a48b0534b198018563a7d8000000000000000000c42a078ef07a60898789067c3412d8c26753098232c243b3ae7006014e00001594000000000023800002ba000000006780000acf800000000cf0002ed400000000002e2c3e09f040f80000abcca6d2c2a66cb140e027e2cff61569cfe00003c800000004d2c00028d0000afd00000002a7856dc4831ade2cf88ca19209a0d3737e0000c0592d600017915e1d83d0ee9f6c1b4300e3c001a46a0006aa0a80000000000a85e0d01f3110676519640002c008d689a174f82cb4a664e06b81dad36280003efce7a27813d63918000313800000007d90000000c2f254ea7bc000000000000000000000ed3000088a3a900001d088e20000d8401b29b83ba309a420dc7a3d0a7b60002950a9902be00015b2000000030900004ec86172f11c380002b0052196849c920fa08b000000029a7000203a7e020d911d83c61fb0eca3e419d93f5220889e28644a10000b612aaab1780000000d6c00000008f01b5c000231852680009da80009d21e9e94000008281195ac3c0000000000000000093e0c2e626122a81d081287e80000000609ac49f46259025421f5b5a76a83262838c0b7432b179689e455f8807c1fd1ad24730c026fd1d3a000000094e400006268c00001f528ff0fad00000008f5a490c04800031e1ea42e00baa0a300008cb00000000a1aa6b8000186647418897620000000000149caa788a26f5222800024c2bbc8000466d6d048296aa00027f6a410000a809fda0001f980000be127b94f259509588249de0a6f2a40000099a9d3043c7d163f20f7a530568aa9643ba4823378d10ada80d5469559a0fa0d1a57407793e51bac89926e85b100000002af5000070230fdc4700012260000000000304e0d0000051a80000001860000092088f26240000000000246ea188000000297da88d518be880004d68a94ae984dc00200000000000000222100003c41f8a38c0002d4c082800000000005948c503ae00000000b403546797a100ab040410e40000d4198da8f80
  | 54 => 0x5180b63f4a9c400018029fe1264b9ac171736800000000000000000a4610e200001e64ce9f7a5879ef2a2992d31fa80000001e7a3d4038a2ad28148da85faa0c14350000000000252b722000000000000002f7230c0000000188475f8eea00000004de800000000002159a288210c113408000a2b848c92c8df44db13bea3980000003094a4ca484000000099784240001a99089000000000000eac00000000000ca5d32000018e4df400000000000000000000000000005e6c1c2b4500019ae00000000001f0a000203c00017205d01aba27c13940312aec5690027104466477310fac2029d19b3a74f67fa7ba880015793305e8061e7207411aec080a0a930d5b6615dac988d8190c6c5028a92e9450288a19c8f825f275916feba586e582eac4c3be088ea9bae3cb319cea00e2f3479c1632b49a22d837d2a1b0e2a87292000014a617e169a6ccac122c64a89e908dfa1ae6ef9a9f1cda46088481b90fccc607ac28d000181d2690c0000c5c0000001f0e0000000052de18ba080ec0000bc04638caab81cb0c0c68000454291600027d64a2ad1057c00000001a7d84c00003748000a4c000000000000000000987999e000000000005eb0000000464000000000000001ade0000000000000000026147fc0000000035a0000aae000153a00000009fe80000000000574800000000000000000174016e181a80c8c0dae900020260c29958afd9fb3905628625783f70000000c301ac40000d7a42189ca17806e6000275000029e00002942000068a7ed14fc2ffc00000002837dd92fe51e167cba90000bd42fbc000000000018561c50f937dece2800022600000fb034a80005e402c0000000012d9406000000000000005eaa5f8609826644f22e39bf4f6800000004b18000a952d8d609d2979fd1c160da5ab2236a06c3622a2da26c0000000000000155d0002e5a62f8000773abe490f9ad40000dbe60fb0f6a43245a00000000001
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x846e729944004236b94ca200211b9c865100108dae4328800843f765504004317324a4200218b9915210010ccaa53088008636545844004332a92c2200210f9d3658801087ae9b2c400843d75992200421fbaac9100210fdda548801087aed2a4400843f76552200421ebb2a910021879925388010c3ac929c400861e6454e200430eb22a7100218b9925288010c5ac9294400862e6454a2004316b22a5100219554e6188010ccaa530c400847775586200432aa9ac310021995496188010c3ca9b1a400861d54d8d200430f2a0c6900218755063480108bced29a400845c7694d200422f3b2a690021171d95348010c9ec7292400864c639492004327b1aa4900219318d524801087ce9b28400843d74d94200422f39eca10021175cf650801087ce9328400843d74994200422f39cca10021175ce65080108eae2b28400843e74194200421eba0ca10021179cc65080108bae6328400843d75990200421fbaac8100210fdda540801087aed2a0400843f76550200421ebb2a810021175d66308010c3ca9318400861d5498c200422fbaac610021879516308010c3aa8b18400845f7694c200422ebb4a610021879925308010c3ac9298400845f7654c200422ebb2a610021879915308010c3ac8a98400862e649482004316b24a4100219398e5208010c9ac7290400862e645482004316b22a4100219398d5208010c9ac6a90400863654984200431aaa4c2100219594e6108010caaa7308400866552984200431b2a2c2100218d5516108010caca6b084008655535842004333292c2100219954961080108eaeda96200855573d4b10043932a2a588021c955152c4010e8ca6a9620087455354b100429abae8188021c954b40c4010a6eeaa06200872552503100421ebb4a9080210fdd95484010c5cc9294200862d6494a1004317322a5080218b59152840108eaed28c200872a525021004394a9281080218e9d16584010c72e8b2c200863965992100431cb2ac9080211e5db5484010c72cb2a4200863965552100429dbb2a9080214e5d95484010cd2cb29420087295494a1004334b2aa508021ca5515284010e92a6a94200847976946100429cb82a8880214e5d74044010c76cba02200863b6550110043952928088021ca5494044010c6ecb2a2200863765551100423b3b6a488021555cf5244010acaeb2922008667659491004333b2aa488021c99515244010e4aa8a9220087465354910043a2a9aa4880219954b6044010a6aeba02200863765d011004392a9680880214ddd54044010c6ecaa02200872552501100439928280880211e9db5444010a72eb2a2200863b65951100431db2aa8880219ad965244010e52a9292200866b655491004394aa2a488021d254d5244010c72a9b0a200873154d85100423d3b4a288021d854a5144010
  | 1 => 0x420422eb9ccb21021179cc65908108bae632c840847671196420422f39ccaa1021175ce65508108bce632a840845d73195420431aaa6c2a10219554f6150810ccaa5b0a840847575185420432aa98c2a10219954861508108bce7328840845d73994420422f398ca21021175cc65108108ece2328840847a70194420421f3a4cb190210f5d2658c81087ce832c640843d74196320423b388cb190210f9d2654c81087ae932a640843e74195320421eba0ca990211d9c4654c810a98e6a92640863954d813204334a96c0990211e5d4604c810c72a8302640843e74994320421eba4ca190210f9d0650c81087ae8328640847671194320423d380ca19021535ce520c810a9eea990640854d754c83204327b2a641902193595320c810e1ca8990640870d544c832042e438264190210fdd16294410878e8b14a20863954982410423dbaac1208218e55160904108dce5b28820846d72d94410423cb82ca208211b5d66210410c5ca9310820862d549884104237baac4208218b9516210410c5aa8b10820846f769484104236bb4a4208219398e5210410c9ac7290820846f765484104236bb2a4208219398d5210410c9ac6a908208635655044104392a9282208218e5526010410cd4a5300820866952980410431d2a2c0208218e5516010410cd4a4b00820866952580410422f39ecb10821175cf65884108baeb31c420861e5498e210430eaa4c71082117dd56388410c3ca8b1c420861d5458e210422fbb4a710821175da53884108beeca9c420845d7654e210432731ca5108219358e5288410c9cc6a94420864d6354a210432ab1ca3108218e5526088410c72a8b04420866952582210421f3b4a8908210f1da544841087cecaa2420843c76551210430fb24a690821871925348410c3ec8a9a420861c6454d2104317b24a4908218b1925248410c5ec8a92420862c64549210431caa4c0108219654e6008410c72a8b004208659535802104335292c0108218e9c264940108bee6b14a00845c7358a5004297396a9a00214b5cb54d0010a5ce42a6800852d72153400421ebb6a5a0021479cf52d0010a3ae7a96800862d6594b400438729ca5a00218b59552d0010e1ca6a96800870d5354b400421ebb0a5a0021479cc52d0010a3ae629680085367114b4004332a94c3200218d5516190010ccaa4b0c800852e72d514004296b96a8a00214e9c3545001087cec2a2800852e721514004296b90a8a00214e9c05450010a74e9282800853b70d95400421f3b6a4a0021479cf5250010a3ae7a92800853a70d494004296baca4a00218bd965250010e1ca7292800862f65549400438729aa4a0021c354d525001087cec292800851e73149400428eb98a4a00214b9c85250010a6ce2292800853a701494004395296c0a0021ca54b6050010a74ed28280
  | 2 => 0x42a02214e9d42150110b64e210a80887a121085404426ab9cc390221591d521c8110c74caa0640886b2615032044358b0a8190221e848540c811087ee8b2a408843c74595204422fb9aca90221171cd6548110c98c7a92408864c6314920442b23aa4290221b118d2148110c70caa02408869b63501204434c31a8090221ca1494048110d66c2a0240887a121501204434d31a8010221a658d4008110d64c2a0040886b16150020442e8b9c438822135dcd6284110b66eca0420886b3765021044359b128108221ac5894084110c9cc7316a80864e6358b5404326b1ac5aa0219958a61d5010a5ce5aa4a80852d72d525404297390c32a0214b5c86195010a5ce5b22a80852d72d91540429a38ac4aa0214b9c86155010a5ae430aa80843f765505404316aa4c42a0218b5516215010c5cc9310a80864e639885404317322c42a0219398d6215010c9ac6b10a808665629845404335314c02a0219a58a6015010c3ca931ea40861d5498f520430f2a2c7a90218755163d4810c3cc931ea40861d6498f520430f322c7a90218759163d4810caac730ea40843e74983520421eba4c1a90218e59260d4810a5ce9a94a40852d74d4a52042a739ea529021535cf5294810a9ce7aa4a40854d73d5252042a7398a929021535cc5494810a5ce9a9ca40852d74d4e52043872a4a729021c35525394810c9ac631ca40854e7398652042a6b9cc3290214b9d26094810a5ae9304a40852e741825204296ba0c129021539cc6094810a9ae6304a40852e74d895204296ba6c4a9021539cf6254810a9ae7b12a40843f74585520421e3a2c2a902117dcd60548108b8e6b02a40846e76d5152042a739ea8a9021535cf54548108dcec2a2a40854e7315152042a6b98a8a90214b9d35354810a5ae9a9aa40870e5494d5204386aa4a6a9021c39515354810e1aa8a9aa4085647159152042b4382c6a90219358c6354810a9ce730aa40854d7398552042973a4c0a90214b5d26054810a5ce8302a40852d7418152042a7398c0a9021535cc6054810a5ce8082a40852d7404152042a6b9820a90210f5da541481087eecaa0a40861e5498c520430eaa4c629021879516314810c3aa8b18a40845d7694c520430f324a6290218759253148108beeca98a40861e6454c520430eb22a6290218b9526214810c5aa9310a40864e539885204326a9cc4290211bdd95214810c5cc8a90a40862d64548520432731aa4290219358d5214810c3cc9318a40861d6498c520430f322c629021875916314810c5cc9310a40862d64988520432731cc4290219358e6214810c6cc9308a40863564984520432b31cc2290219558e611481087ce9300a40843d74980520431cb24c0290219658e60148108bce732e840845d73997420422f398cba1021175cc65d08108f4e032e840845e73996
  | 3 => 0xd1650c910878e8b28648843e74194324421eba0ca19221535cc520c910a9cea990648854c754c8324423a3aac21922199149610c910972e93006488478755803244364992c0192214b1c9549051087cec2a2828853571950414421fbb2a820a214b1c95410510972e9306428862c64d492144316320a490a212e5d06048510c68cbb2242886346519121442d8b80c890a211d1d56348510b8ce7b1242884767614921442b23aa8490a21599d73248510cc8cb9924288664650c92144362b186490a21785c032485109aae630242885b174181214426ab9cc210a218d15161d0110a72e1b2e808852f725974044296392cba02214b9c865d0110a5ae432e808843f7654b404421e3b2a5a022147dcd52d0110a38e6a9680886346558740442cab9c43a02212ddd921d0110a68ea90e80885d1738864044237b92caa02211b1c965501109cae430a808852f725954044296392caa02214edc1655011087eeca92808843c76549404428fb9aa4a0221471cd5250110c6aca30a80885a57218540442cab9c42a02216c9c22150110968ec90a808853475485404429d3aec0a02218e19760501108f4ec2a280886386590940442d938c84a02216c5c64250110c70ca21280885b27110940442d8b8884a0221785c86150110c70cba0a808853a75905404431c32a82a02214e9d44150110b54e420a80885a97210540442e8b9c42a0221e89092150110f428490a80885b171d95404429cb8ecaa0221cc5c76550110c74ec32a808853a75989404429cbacc4a02218e1966250110b64e331280885b171989404429dbaac4a02214e1d56250110b36e6b1280885987358940442d9b8ac4a02216c1c56250110c70ca31280885b27118940442d8b88c4a02212e1d95250110b36e6a928088598735494044394a90a4a02216c9c63250110b62e3192808853b754c9404429c3aa64a02214e9d43250110a72ea1928088789320c940442d938864a02216c5c43250110c70cbb0a80886b065d8540442d8b96c2a02214e9d66150110b64e330a80886b361985404429dbaac2a02218e1956150110b56e4b0a80885a872585404429d3a8c2a02216a9c86150110b52e430a80885b27618540443593b0c2a02216c9d46150110e64ea30a80887a27218540442d8b90c2a0221e85c86150110b42e430a808853a7588540442cd39c42a0221665ce2150110b64ed10a80885b07688540442d93ac42a0221cc9d62150110b66e710a80887927388540442d8b9c42a0221e45ce2150110b22e710a80885b17288540443d1b1442a0221e818a2150110976ec90a80884b8764854044359bb242a02216c9d92150110b60ec90a80886b07648540442d9b9a42a02216c5cd2150110f46e490a80887a26248540443d0b1242a0221e8d492150110f40a490a80887a33248540443d0192
  | 4 => 0x3ca931c430861d5498e218430f2a2c710c2187551638861087aebb22430843d75191218425cb80c890c210f9da5448610878ecaa2430854c73549218425cba0c090c210f5db52d0210a3ee6a96810851c7354b408421ebb0a5a0421479cc52d0210a3ae6296810863554986408431cb2aa9204210f9d8545021087ceda92810851f73549408428e39aa4a04210f9d85250210a3ce6292810851d7314940842d8b8ea8a04218ed9554502108f4ec2a281084ba76151408429cbac84a04214edd54250210b66e2a1281086b06150540842d539082a04216a5c84150210a72eb312810853b7558940842cdb9ac4a0421661cd6250210b66e2b1281085b071589408425d3b6a4a042166dcd5250210b30e6a9281084ba7614940842cd398a4a0421665cc5250210e52a4292810853b754c9408429c3aa64a04214e9d43250210a72ea1928108789320c9408431db2ec2a04218ed956150210b56e4b0a81085a87258540842d5390c2a04216a5c86150210d62c230a810859a7388540842ccb9c42a04212edd92150210970ec90a810843f76550408431b2a4c220421ac5854010210a9ae6296410843d75992208421fbaac9104210f5da548821087eecaa4410854c7354a2084358b0a8110421879536348210c3aa9b1a410861e5418d208430eaa0c6904219318f52482108dcec292410854d731492084326318a490421a6d8d4048210d30c6a02410872852501208421ebacc8104210fdd5640821087aed2a0410843f76550208430f2a4c610421875526308210c3ca8b18410861d5458c2084326b1ca4104211bdd95208210a98e6a90410864d63548208431b2a4c2104218d5526108210c6ca8b084108635545842084333292c210421995496108210d34c6a004108699635002084394a928010421ac5854008210c6acb2a621086356555310842abb9aa5884218e59654c4210c72caaa6210864f63d895444317b20c4aa22193d8c6255110c98c6312a88866462d85544421fbb2a82a2214b1c954151108dce4308a88846d72184544421fba2c3292210f1d16194910c3ec9b1aa48861c64d8d524430fb20c6a9221871906354910c58c9b12a48864c63d89524431a326c2a92219618f60549108deeca90a48852c7454852442a639aa429221179ce61149108bae7308a48843e74980524421eba4c0292210f9d0601491087ae8300a48845e73180524422eb98c029221179cf65d09108bae7b2e848847875583424422f39ecb21221175cf65909109aae730c848847475586424422fb9acaa1221171cd65509108eee2b2a848845f73594424422e39aca21221179cc65109108bae6328848847475584424431a2a2c2212211e1d56010910cd0a4b00848843e74d96324421eba6cb192211d1d5618c91087ee8b2a648843c74595324423db82ca992210fd
  | 5 => 0x864d6358854c4335312c02a6219a5896015310a9ce7a94a58862d7219152c42a739ec4a96211bdd95214b108bce632e858845d7319742c422f39ecb21621175cf6590b108bce732c858845d7399642c4296b90a9216214b1d15290b109aae730c858845e7399542c422eb9ccaa1621179cc6510b108bae632885886345458442c421f3a6cb196210f5d3658cb10caaa730c658843f7459532c421e3a2ca996213c5c4604cb1087ee8b28658843c7459432c421f3a0ca196210f5d0650cb10a9ae7290658854f754c832c42a6baa6419621721c1320cb1087cec2a2838843f7655041c431d2a2c020e218e5516010710a9ce7a96438864e6394a21c432731aa510e21955966388710caacab1c43886d16358221c42a739ea490e211b9d85248710c6eca32243884f07058d21c42e339ec490e21719cf5248710bc2e1a9243884767614921c42733b0a490e21591d54248710acceb99243886c5630c921c426ab98c090e211bdd95208710dc242b00438851e73d4b40c428eb9ea5a06210fdd952d0310b2ae710e81884b77648740c431aaa0c2a0621395c86150310a5ce432a818852d7219540c428f39ea4a0621475cf5250310878eca9281885a57218540c42cab9c42a06212d1d921503109aae730e418864c6394920c432631aa490621b118d2148310a3ce7b14a90851d73d8a548429d386c52a4214e9c06295210a5ce4304a90852d72182548428fb9ac4aa421471cd6255210a6ee2b12a90852f725855484296392c2aa4214b9ca6055210a5ae5302a90843f76550548430f2a6c6a9421875536354a10c3ca831aa50861d5418d528432631ec4a94210f5da5414a1087eecaa0a50861e5498c528430eaa4c629421879516314a10c3aa8b18a50846f7654852842a639aa4294219358d5214a10c3cc9318a50861d6498c528430f322c629421875916314a10c98e4b18a50864d63988528431b322c2294218d5916114a10cacc6b08a50865563584528422f39ecba1421175cf65d0a10c74a8b06850845e73196428422eb98cb2142117dcd6550a108b8e6b2a850863554185428422f398ca21421175cc6510a10c74a8b00850843e74996328421eba4cb194210f9d0658ca1087ae832c650854d7214e32842a639aa5194210f9d2654ca1087ae932a650843e74195328421eba0ca994211b9da524ca10a98e6a92650843e74994328421eba4ca194210f9d0650ca1087ae8328650846d76d4832842a6b98a419421539d5320ca10a98ea990650864f654c83284326b2a6419421c3951320ca10e1aa899065084b974980328431caa4c0194218e551600ca10d9264b00650863a54583418431caa6c0a0c218b9526210610c5aa9310830862e545884184316aa2c420c218e9516010610c72a8b0083086b14158041842a639aa590c212e5d260c8610c
  | 6 => 0x831b324a2180418d592510c020cccc5288601066562944300823bbb2a2180418d991510c020c6ac8a886010666625443008332b12a218041d10c9510c020c72caa0060106a96250030083c41928018041cc545400c020acae3a9e401046f7654f200832731aa790041c395153c8020e1aa8a9e401064f7654f20083263b2a790041d154e51c8020e4ca8a8e40107255454720083a329aa390041d154d51c8020cccc6a8e4010664635472008296bae8190041c354f40c8020e4aa3a06401052f755032008386a9a8190041c954540c802087aed2a4401043f76552200830f324a710041875925388020c3cc8a9c401061d6454e2008236bb4a5100418d9925188020c6ac928c401063664546200831ab22a310041c654d4088020e62a2a0440107195454e200823cbb4a510041cc5515188020ea2a6a8c401061e54d8d200830eaa6c690041879506348020c3aa831a401045e7694d200822e3b4a690041179d95348020caec728a401065463945200832bb1aa2900419518d5148020c76cba02401063b65501200834c31a8090041c654d4048020e62a2a02401064f73d95200832639eca900418bd965448020c5ecaaa2401064f65d8d2008236bacc690041339ce6348020c9eca31a401064d7518d20083472a0c690041a355063480208dceda9a401064c63d4d20082b2b8ea690041331da5348020a9aeb29a401064f6594d20082363b2a6900419318d5348020998eca9a401064f6554d20083872a2a690041c35515348020c9eeca9a401054e7654d20082a63b2a690041931d95348020898eca9a401066765945200836231ca290041d154e5148020c98c6a8a40106676554520083932a2a290041c95515148020d88c6a8a40107465354520083a2a9aa290041d1d8d5148020cccc6a8a40106646354520083a231aa2900419118d5148020c9aa7b02401064c639412008296bae80900418bd974048020d18c7a02401070d53d012008392a8e80900416a5d24048020d90c720240107495390120083b0a8c80900414bdd54048020c5ecaa02401068c635012008386a9a8090041c95454048020d90c6a0240107495350120083b0a8a80900416add54048020e56eaa0240106ab655012008395b2a8090041e2d8d4048020d54c6a0240106a86350120083c431a8090041a218d4048020e56a6a02401078a535012008394a9a8090041e254d4048020e12a6a0240107a2515012008394a8a8090041e85454048020e42a2a02401065b73d95200832c39eca900418ed965448020c76caaa2401065b65d8d200832db28c69004196d965348020cb6caa9a40107195454d20082d4ba6c490041b218f6248020e92a72924010673659452008339b2aa290041cc5515148020ea2a6a8a401076252545200821fbb2a82a6219398e6215310c9cc6b10a98
  | 7 => 0x8908410f1d95448420c3ec929a421061c6494d210830fb22a690841871915348420c6ec928a421063464945210831caa4c0108419654e6008420c72a8b00421065953580210833928ac0108411b5d83294020a3ce7aa6801051d73d53400829b38ea9a00414d5c754d0020a3ce62a6801051d73153400829b388a9a00414d5c454d002087aeda9e801053671d4f400829ab8ea7a00418759653d0020c3acaa9e801070c7254f400821ebb0a7a00414d9c453d0020a6ae229e801052d75ccb4008316b2e65a0041c354f32d0020a5aea196801062d650cb4008386a9865a00418d59651d0020e2ca728e801071553947400831ab2aa3a0041c594d51d0020e2aa6a8e8010727325474008392192a3a00419354e6290020c5aa8b14801064d5358a4008333312a320041995895190020a3ce7aa2801051d73d51400829b38ea8a00414d5c7545002087cec2a2801051e73151400828eb98a8a00414d9c45450020a6ae22a2801043e76d4d400829b38ea6a00414d5c75350020a3aeb29a801061f6594d400830fb2aa6a0041c31c95350020e30e0a9a801043e7614d4008297390a6a00414d9c45350020a6ae229a801053a7014d4008296bae64a00418bd973250020e1aa7992801052d750c94008317b2864a0041c354c3250020b52e0192801063765945400838b29ca2a0041c554e5150020e64e128a801063765545400838b29aa2a0041c554d5150020e4e64a8a8010724325454008399382a2a0041c694f6050020e32a7b02801073251d814008398a8ec0a0041179ce65100208bae7328801045e73194400822eb98ca200410fdd95410020c3cc9298801061e6454c4008326a9cc4200418b9516210020c9aa6b108010666625444008332b12a220041535d732cc020c9acb996601074732547300831cb2a8198041c654d40cc020f1664a06601073151503300821f3a6cb180410f5d3658c02087aeb324601043f75592300821fbb4a9180410f5da548c02087eecaa4601043d76552300830f324a71804187592538c020c3cc8a9c601061d6454e3008326a9cc5180411bdd5628c020c9aa6b14601064f650ca300831b324a3180418d592518c020c6cc8a8c6010635645463008333312a31804199589518c020e8864a8c601062e54d893008316aa6c4980419394f624c020c9aa7b12601062e541893008316aa0c4980419394c624c020c9aa631260104ce76cc930082a6bae649804193d97324c020ccec528a6010664629453008333b12a29804199189514c020e8e64a8a601043e74994300821eba4ca180410f9d0650c02087ae8328601043f76950300821ebb4a8180410fdd9540c02087aecaa0601062e549883008316aa4c4180418b951620c020c5aa8b10601064e535883008326a9ac41804193594320c020b92e01906010475769443
  | 8 => 0xb6354420a6ee8b1aa2105347458d51082b2392c6a88415c1c16354420acce5a1aa21056572d0d51082b938686a88415c5c34354420acee4a1aa2105647250d51082b938084a88415c5c04254420acae1992a210745320c951082b938064a88415c5c03254420e8ce6192a210746630c951083a2b1864a8841d89c03254420acae0192a210761700c9510829b3a4c0a88414d5d26054420a6ce8302a2105357418151082ab398c0a8841555cc6054420a6ce8102a2105357408151082ab39840a8841555cc205442087aed2a0a21043f76550510830f2a4c628841875526314420c3ca8b18a21061d5458c510822ebb4a628841879925314420c3ac9298a21045f7654c510830f322a628841875915314420c6ca9308a21063554984510832b29cc2288419554e61144208eeeca88a21063664544510831ab22a2288419598d5114420caac6a88a21045e73997410822eb9ccba0841179ce65904208bae732c821045e73195410822eb98caa08418b5536250420c9aa7b12821064d531894108333b12a2a08419918951504208bce7b28821045d73d94410822f39cca20841175ce65104208baeb318821061e5498c410830eaa4c62084117dd56310420c3ca8b18821061d5458c410822fbb4a620841175da53104208beeca98821045d7654c41083172a4c4208418b5526210420c9ca7310821064d5398841083172a2c4208418b5516210420c9ca6b10821064d53588410832b31ca2208419558e5110420ccac5288821065663544410832ab1aa220841999895110420ccac4a88821063954980410832d29cc0208419654e6010420ce2a3300821063a54580410831caa2c0208419694d6010420cb2a6b008210672515804108338a8ac0208410f9d265cc42087ae932e621054d750cb3108326b286598841d10c951cc42087ce932c621043d7499631083172a4c5188418b552628c420c9ca7314621064d5398a31083172a2c5188418b551628c420c9ca6b14621064d5358a3108332b14a31884199989518c420ccac4a8c621043f74595310821e3a2ca988410f9d0654c42087ae832a621043d75d91310821eba8c8988410f9da544c420878ed2a2621043e76551310821e3b2a89884187d92534c420c38c929a621061f6454d310830e322a6988411b5d7624c420c9aa7b12621064d5318931082a6ba8649884193594324c420c6ec928a621063464945310831bb22a2988418d191514c420ccec4a8a62106646254531083a2192a2988419654f604c420ce2a3b0262106c832181310821f3a4ca188410f5d2650c420ce2a2b06421061e5498e210830eaa4c710841879516388420c3aa8b1c421045f7694e210822ebb4a71084117dd953884208baeca9c421065663546210832ab1aa3108412e5c0644842087ced2a2421043c76951210821f3b2a
  | 9 => 0xaed2a0a61043f76550530830f2a4c629841875526314c208beeca98a61061e6454c530830eb22a6298418d9526114c20c6aa9308a61065553984530831b2a2c2298418d5516114c20caaa6b08a61062e649885308316b24c4298418d9926114c20c6ac9308a61066662984530831b322c2298418d5916114c20cccc4b08a61043e74980530821eba4c0298418e5926014c20ce2c3300a61047671997430823ab8ccba18411d9c465d0c208eae232e861046d7598b4308326a9cc5a18418b95162d0c20c9aa6b16861047975983430832ca9cc1a18418e95160d0c20cb2a6b06861047671996430823ab8ccb218411d9c46590c208eae232c861047671995430823ab8ccaa18411d9c46550c208eae232a861062d54d894308326a9ec4a18411b5d46250c20c9aa6312861047671994430823ab8cca218411d9c46510c208eae2328861047a70194430831caa2c1210419654e6010820c74a8b00841065953580420832739acb990418b59654cc820c5acaaa6641056571d4f3208326b2ca799041c395153cc820e1aa8a9e641064d53583320832ca9ac119041535c9530c820c9eca990641064d654c832083872a26419041c3551320c820c72a9300641063954580320832d29ac019041535d6630c820c9acb318641056571d4c32082a6baca6190411bdd9530c820c9cc6a98641070e5454c3208386aa2a61904153dd9530c820c9eeca98641054f7154c3208237baac0190419354d600c820d94c6b00641061e5498f510830eaa4c7a88418795163d4420c3aa8b1ea21061e6494f510830eb24a7a88418799153d4420c3ac8a9ea21053674d46510829aba6a328841559cf5194420aaae7a8ca21043f7458e510821e3a2c728841559cf5494420aaae7aa4a2105567315251082aab98a9288414d9d35394420a6ae9a9ca2107165494e510838aaa4a728841c59515394420e2aa8a9ca2107447254e510829b3a0a7288414d5d05394420acaeb994a21074553cca51083a2a986528841559cc6494420aaae6324a2105667219251082b9380c928841599cb6394420a6ee8b1ca2105347458e51083a299065288414d9d26094420a6ae9304a21053674182510829aba0c128841559cc6094420aaae6304a21045e73191510822eb98c8a88411d9db5454420aace7aa2a21055573d51510823b3b0a8a8841559cc5454420aaae62a2a21047676d4d510829b3a6a6a88414d5d35354420e2ca929aa2107155494d51083a2394a6a8841c59515354420e2aa8a9aa2107447254d510823b3b0a6a88414d9d05354420a6ae829aa21056575cc951083932a664a8841c95533254420e8ca7992a21074553cc951083932a064a8841c95503254420e8ca6192a210745530c951082b2392c8a8841559cc6454420aaae6322a2105667219151082b9380c8a8841599c
  | 10 => 0x70c534cb404838629e43a02412bdd921d0120e18a690e809045d73d95404822fb9acaa02419314f6250120c98a6312809051e73d95404828eb9ecaa024147dcd6550120a38e6b2a809053771595404829a38acaa02414edc16550120a76e0a9a809051e7514d404838cb80a6a0241c314f6250120e18a6312809052e758c9404838629c64a0241c314d3250120b50e0992809070c53c8540482563b242a0241c314d2150120b50e090a809053a75d81404831c32ec0a0241c6d4f6050120e30a7b0280905aa72d81404830f326a6202419314e62cc120c98a6b16609061e64d4e304830eb26a71824187990538c120c3ac829c609054e758ca304838c29a8118241e28c9408c120c9ea6312609064c53189304832632a6498241721c1324c120c70caa0260906a86250130483c49928098241c614d40c8120c3cc9a9c409061d64d4e204830f320a710241875905388120c9ac629c409064d7614e2048387320a710241c35905388120c98a6b0c409070c53d02204838629a81102419358e62d5020cacc730ea81065563987540832b31ac3aa0419558d61d5020cccc4b0ea81051e73d52540828eb9ea92a0414d9c75495020a6ae3aa4a81052e72d8e540829d386c72a041479cc6195020a3ae630ca81052e72186540829d380c32a041479cf6455020a3ae7b22a81053671d91540829ab8ec8aa041179cc61550208bae630aa81052c7258d5408296392c2aa041479cc6155020a3ae630aa81052e72185540829d380c2aa0410fdd95415020c3aa9318a81061d5458c540831aaa4c22a0418d5516115020c3cc9318a81061e6458c5408326b1cc42a0418d9926115020cacc7308a81065563984540831b322c22a0419598d6115020caac6b08a81066662584540832cb1cc02a0419c5866015020c6ca930ea61063554987530831b2a2c3a98418d55161d4c20c6cc930ea61063564987530831b322c3a98418d59161d4c20cccc4b0ea61051e74d4e530828eba6a729841559c75394c20aaae3a9ca61043f74586530821e3a2c329841559c75494c20aaae3aa4a6105567115253082aab88a929841539ca6194c20a3ee8b0ca61051c74586530828f3a4c129841475d26094c20a3ce8304a61051d7418253082ab388c129841555c46094c20a3ce9b1aa61051d74d8d53082ab38ec6a9841555c76354c208bcedaa2a61055671d5153082aab8ea8a9841179d85454c20aace22a2a6105557115153083872a0c4a9841c35506254c20a9ce5322a61055a7099153082a6392c8a98419318b6154c20a9ce530aa61051f74585530828e3a2c2a9841531c96154c20c98c4b0aa61055870585530828f3a4c0a9841475d26054c20c98c5302a61051e74181530828eba0c0a9841931886054c20aace2302a61055571181530828f3a040a9841475d02054c2087
  | 11 => 0x482ab388c829a41555c46414d20ab2e0320a69051e74d88534828eba6c429a41559c76214d20aaae3b10a69054d72d8453482a6b94c229a4147dd16114d20a38e8b08a69051e74184534828eba0c229a41535c86114d20caac2308a69055970184534823cb86cba1a411d9c76590d208eae3b2c869064c5398a434832629ac521a411ddc56550d208e8e2b2a869047671194434823ab88ca21a419314e6210d20c98a6b10869065853980434823c3aac021a419614d6010d20cb0a7306849065853583424829a38aa9212410f9d8545092087eecaa0849053471550424832c29cc19924193dce658c920c9ccba9c649064c53586324832629cc11924196d4c604c920a9cebb1a649046e7614d32482a73b0a699241939d8534c920c98a7b0a64904e5711813248365b18c099241179ce64d45208bae7326a29045e76d4d514830fb26a6a8a418719353545208bcec29aa29061f6414d514830e320a6a8a411ddd95114520a68e8a88a29045f73597414822e39acba0a4117dcd65905208b8e6b2c829064c5398a414832629ac520a41179cf65505208bae7b2a829045f73594414822e39aca20a41179cc65105208bae6328829045e7598c414822e3aac620a4117ddb53105208baeda98829045f7614c414822ebb0a620a4193d4e6210520c98a7310829062f545884148327a9ac420a419314d6210520ccac5a88829065b53980414832c29cc020a418ed516010520c70a8b00829065b53580414832c29ac020a419cd456010520c98a7316629064c5358b31482a73ac6598a4193d4e628c520c98a7314629064c5358a314821f3a4ca98a410f5d2654c520972e0322629061f64d4d314830e326a698a41559c7534c520c3ec829a629061c6414d31482a73ac6498a4193196324c52087ce8328629043d7419431482aab88a618a419314e620c520c98a6b106290658539803148237bb2a990a41531cd54c8520ac8e2aa6429046e75d8f2148326b18a790a419399453c8520c9cec29e429064d7614f21483a3388a790a41d15c453c8520c98a7306429045e7598e214822e3aac710a41175db53885208baec29c429061f64d4d214830e326a690a4187d905348520c38c829a429063464d45214831a320a290a419614f6048520cb0a6302429054c7355121482b238aa890a411b9d763485209d0e0b1a42905667194d2148327b18a690a419358c5348520c9cec29a429070f6414d2148386320a690a41d114f6148520e88a7a8a42907475314521483a429ec090a41335cc6048520c98a630242906ab6418121483a4298c090a41d1d4d2108520c98a7316809064c5358b404828f39ecba0241475cf65d0120a72e1b2e809051f73597404828e39acba02414ddc565d0120a68e2b2e809070c5398b404838629ac5a02414b9d632d0120e18a71968090
  | 12 => 0xaa441475cc6155220a5ae430aa91063561185548829d380c2aa441479ce6055220a3ae7302a91053671981548829ab8cc0aa4410fdd95415220cd2c5300a91063964983538821fba2c329c410f1d16194e2087aed2a0a71043f76550538822fbb2a629c418d9526114e20c6aa9308a71063654584538831aaa2c229c419554d6114e20c5ca9316871047771595438823a38acaa1c418b5506250e20c74a8b00871063a54583428831caa6c0a14418e553604ca20c72a8302651070e544c83288386aa264194418b596540ca20c5acaaa0651046d76d4c3288266bb6a619441c3953530ca20e1aa9a9865105ca70d4c32882a6bb6a619441935db530ca20e1ce9a98651070d74d4c32882a6b8ea619441d29c3530ca20b8ae229865105ca7014c3288327a9ac0194410fdd16394620878e8b1ca31064f630c9518821ebb4a828c410fdd95414620c3ca9318a31061d5498c518830f2a2c628c418755163146208eeeca88a31065563544518822fb9acaa0c41171cd6550620a68e2aa2831062d54189418822f39eca20c41175cf6510620a6ae32a0831061e5498c418830eaa4c620c41879516310620c3aa8b18831062e549884188316aa4c420c418b9516210620c5aa8b10831063954980418831d2a2c020c418e551601062087ce932e631043d7499731883273286598c410f9d2658c62087ae932c631062e5498a3188316aa4c518c418b951628c620c5aa8b146310665629463188332b12a318c410fdd1654c620878e8b2a631043e74195318821eba0ca98c410f5d7644c62087aea32263104b970191318821f3b4a898c410f1da544c62087cecaa2631043c7655131883a2192a298c410f9d2650c62087ae9328631063954980318831caa2c018c41879526388620c3aa931c431061e5458e218830eaa2c710c419558e5188620caac6a8c431063954982218831caa2c110c410f5d7644862087aea322431043e76951218821e3b2a890c410f5db53d0220e1ea6196811062d5498a408821f3b0a8a04410f9db5350220e1ea619281105a9700c9408821fbb2a8204418b952621022087aed2a4611043f7655230883c41928118441331cd65c8220a9ee6b2e411062d659532088316b2aa9904419318f53c8220c9cc6a9e411063965953208831cb2aa990441179ce61d51208bae730ea89064e6358a544832d31ac12a2419318f6255120caec7b0aa89065463d85544831bb20c2aa24195d8c6155120ca8c630aa890667621855448332b90c2aa2410fdd95415120a68e2aa0a8905577155353482aa38aa9a9a41479d362d4d20a3ae9b16a69051e74d87534828eba6c3a9a4195d8661d4d20a9ae430ea69045f7654c534821fba2c229a410f1d16114d208baed2a0a69045f7655053482abb8aa829a41551c55414d20a9ae5b20a69054d7219053
  | 13 => 0x6008540d60a2b0042a06ab21580215035910ac010a81aa4856008540d6242b0042a052e721475050296b90a3a82818d58451d4140b34e7b16a0a059973d8b5050355b14c5a828166dcd52d4140b30e6a96a0a05b37154b50502d838aa5a82812edd932d4140970ec996a0a04ba760cb505025cbb065a8281e24c832d4140b54e430ea0a05a9721875050358b0ea3a82816adc951d4140b50e4a8ea0a05aa7214750502d4b90a3a8281ac58451d4140974ed10ea0a04b97688750502cd39c43a8281665ce21d4140974ec10ea0a04b976087505022f39cc329081175ce61948408deeca90a42064d635485210332a92c2290811d9c4654c8408eae232a642054c735493210327b2a641908193595320c840e1ca89906420477765445110332b12a2288818b9526210440c5ca8b108220665629444110332b12a2208814ddd54110440ce2a3300822045e73d96211022eb9ecb10881879526388440c3ca8b1c422065563946211032ab1aa310881179cc65484408bae632a422043d75d91211021f3b4a8908818b1925248440c68c928a422043d76952401023cbb4a920081cc5474150040a76eaa0a802045e7398754c822eb9cc3aa6410fdd95415320cd4c4b00a99045f7654c53c821fba2c229e410f1d16114f208ece3b2c879047571d9643c823b388ca21e411d5c46510f2087cec2a2859043f7655042c82e4b86a6996411b9d8534cb2099cec29a659054e7614d32c83273b0a699641d25c0534cb20c98a7b0a659064c5318132c8272b88c099641b24c9600cb20a72e0322a39062e7219151c8316b90c8a8e418e9c06454720c72e0322a3904777654451c822f39ecb20e41175cf65907208bce7b28839045d73d9441c829ab88a820e418bd516210720c70a8b00839043e74d9731c821eba6cb98e410fdd1654c720878e8b2a63904e97218131c8365190c098e411bdd563c8720c9ac629e439054e7394721c825cb80c890e41335cf6548720a9ce7b2a439062f6519121c82d4b80c890e411b9db5448720ac8e2aa243904e87058d21c82b338ca690e419358c5348720bc2e1a8a439054e7394521c82733b0a290e41335cc6048720dc242b00439070c534cb40c828f39ca3a0641475ce51d032087eeca8e81904af7648740c838629a64a06416a1c13250320a3ce728a819051d7394540c821e3b2a2a06412b1d92150320f1264a06619052d72d8e548829d380c72a441479cf6295220a3ae7b14a91051e73186548828eb98c32a4414b5c86195220c6ac230ca91053a70186548828f398c12a441475cc6095220a6ce2304a91053571182548822f398c2aa441175cc6155220a5ee4b1aa9105377158d548829a38ac6aa44147dcd6255220a38e6b12a91053771589548829a38ac4aa44147dcd6155220a38e6b0aa91052f72585548828f398c2
  | 14 => 0xe629064a058d738c83250257bb264192816a1c1320c940b1eec99064a068f764c832502c73aa6419281631d5320c940b1ee299064a078b704c832502c63826419281e21c1320c940b10e099064a04ba70984325025cb84c2192810fdd5610c940878eab0864a078932980325025d3acc0192818e9d6600c940972e330064a068d3258032503c4992c0192812e1d5600c940d56a4b0064a06a8525803250355192c019281aa4c9600c940d1264b0064a04bb71580325025cb84c5a8a8127dcd62d4540938e6b16a2a04bb7058b5150359a8ac128a81a3d8f6254540d1ec6312a2a068c631895150352316a2a8a818b18a5154540d56c5b02a2a06a862d815150359a8ec0a8a81a398e6214540d1cc6b10a2a068d63588515035238ac428a818b58a5214540a6ae2290a2a05b170944515021fbb2a228a814b1c9511454096eeca88a2a05a47254451502d9b82a228a814ddd95114540c6eeca88a2a072772544515029a392a228a81c91c95114540a48e4a88a2a0726625445150392b12a228a814ddc15114540e66e0a88a2a06aa625805150354b12c028a81cc545601454093ce7b2e42a049d73d97215025cb86cb90a812edc165c8540976e0b1e42a04b87058f215025d380c790a812e5c063c8540b52e129642a058c7354b21502d238aa590a816adc152c8540d1ac619642a05a9700cb215031bb28a390a81695c851c8540e4ca428e42a049e73d96215024eb9ecb10a812e5c36588540976e0b2c42a049e73196215024eb98cb10a812e9c36388540972e1b1c42a068e63d4a2150347318a510a81a398f2188540d34c730442a069963982215025d3acc110a818e9d66088540d34c6b0442a069963582215025c3aac110a81aad496088540d50a4b0442a06ab21582215025cb86ca90a818e5c3654854087ceb32a42a049f73595215024e39aca90a812edc16548540c5ae432a42a043e7598d215021ebacc690a810fdd56348540878eab1a42a04bb7058d215025c382c690a812e9c06348540972e031a42a04ae76949215031632ca490a816a5c25248540958eca9242a062c6554921502c639aa490a81691c55248540b56e0a9242a062c65cc921502d338e6490a818b1943248540d1ac619242a05a9700c9215031a32e4290a818b1962148540b1ce710a42a05a970885215024f398c090a81275cc6048540972e1b2842a049f73594215024e39aca10a812edc1650854093ce632842a049d731942150257390ca10a812e9c36308540972e1b1842a043e7518c215021eba8c610a812e9c06308540972e031842a04ad76d48215024f39cc210a81275ce6108540c6aca28842a0724521442150257bb24210a814b1d5210854096eec90842a053475484215025d3acc010a818e9d66008540970eab0042a06ab525802150354292c010a81acd45
  | 15 => 0x5e73d96219022eb9ecb10c819558e5188640caac6a8c432045e73195219022eb98ca90c818bd925248640c6ec928a432046f7654852502a639aa429281591c55214940974e130e84a049e73986425024eb9cc3212812e9c26190940974e030a84a04ba70984425025b38ec9192812d5c7648c940974e132264a04b870591325025d3a0c0992813c5c4604c9408eee2b2864a047471594325023b388ca192811d5c4650c940974e1b2064a04b671190325025ab88c8192812e9c0640c940c5ac829064a054d7314832502a73aa6419281531d5320c940b90e099064a04ba749803250364992c01928117dcd62d45408b8e6b16a2a04777654451502b2392a228a819398e6214540c9cc6b10a2a064d635885150317ba2c428a818b1d16214540c5ac5210a2a0535711085150335312c028a819a5896014540a74ea30682a04ba75982415031d3acc120a814d9d76150540a6cec28a82a0636761454150393390a2a0a81c95c85150540c68c428a82a073170145415034731cc420a81a398d6210540d1ac6b1082a062c75588415029ab88a420a81aa98a6010540d52c530082a063a655804150355312c020a81aa589601054093ce7b2642a049d73d93215031bb20a390a81595c851c8540e4c8428e42a045e73196215022eb98cb10a81279cf648854093ae7b2442a04ba70d92215024f398c910a81275cc6488540974e032442a064e63d4a2150327318a510a812e9d2608854087ceb32242a062c6590921502563b28490a818b1954248540b48e2a1242a045f73594215022e39aca10a81179cc65085408bae632842a04ba70d90215024f398c810a81275cc640854095ce432042a04ba70190215031ab20a210a812e9d26008540d62c3a0e80a05aa7210740502d4b9083a02812e5c263d4940972e130ea4a049e73986525024eb9cc329281aad496094940976e2b04a4a068c63d49525034bb1ec2a9281a518f6154940d66e1b0aa4a069763185525034a318c2a9281a9d486154940c6ca430aa4a06b170185525034db1ec0a9281a618f6054940d66c3b02a4a06b061d815250355a96c0a92812e5c76054940976e0b18a4a05a970948525021fbb2a4292814d1c5521494095eeca90a4a058c7354852502d238aa4292816adc15214940972e1308a4a04b671d96325025ab8ecb192812e5c3658c940976e0b2c64a04ba70986325025cb84c3192812e5c3654c94096ee2b2a64a04b471595325025db82ca992812e9c0614c940972e030a64a04ba75d81325025cb8ec0992812d9c4604c94096ae230264a05b171181325025d3a8c0992818e9d4604c940d346430264a06b271181325025cb88c099281ac5c4604c940962e230264a04b970d94325025bb8aca192812d1c5650c940976e0b2864a04b671194325025ab88ca192818b594520c940b1a
  | 16 => 0x23b38ecb196811d5c7658cb4096ce3b2465a04b571d9232d030f322a7196812d9c4640cb4096ae232065a054d7394832d02a7baa6419681535d5320cb408bce7b12a3a045d73d8951d023bbb2a228e819c5456010740d1cc731083a068e6358841d0346b1ac420e818bdd56210740c58eab1083a062d6294841d029bbb2a220e818ddd95110740e4cc4a8883a07256254441d0398a8cc020e81aa9896010740d52c4b0083a07315158041d022f39ecb90e81175cf65c87408bce732e43a045d7399721d024f39ec990e81275cf64c87408bce7b2c43a045d73d9621d024f39ec910e81275cf648874093ce632443a049d7319221d0316324a490e818b1915248740ac8e2a9243a05a47150921d024f398c810e81275cc6408740d34c6b06a5a06996358352d02c739ea5296816a5c35294b4093ce730ca5a049d7398652d02c739ea4a96816a5c35254b4087eeca90a5a04af7654852d0355292c029681aa5496014b4096ce3b2c65a04b571d9632d025cb84cb196812e5c0658cb40c3ccaa9c65a04b97099532d025cb80ca996812d9c4604cb4096ae230265a04b97099432d025b388ca196812d5c4650cb40972e032865a058d7394832d0257bb2641968163dd9320cb40d1eec99065a058f754c832d02c6baa641968163dc5320cb40b18e099065a043f7558432d021e3aac219681a34c9600cb40b62e1a8ca3a049e73d8951d024eb9ec4a8e816c5c35154740d1cc7310a3a068e6358851d0346b1ac428e818b58a5214740a6ae2290a3a043f7654451d025bbb2a228e814ddd95114740c6eeca88a3a07266254451d0392b12a228e818d5456014740d54c4b00a3a06a96258051d0398a8ac028e818e9496014740d64a2b00a3a06395158051d0358a8ac028e818c545601474093ce7b2e43a049d73d9721d024f39ccb90e81275ce65c8740972e132e43a04b97019721d0346b186590e81279cf658874093ae7b2c43a04b97099621d024f398cb10e81275cc6588740972e032c43a068e63c8621d024f39cca90e81275ce6548740972e132a43a04b97019521d0316b90ca90e818e5c0654874087ceb31a43a043d7598d21d021fbaac690e810f1d56348740976e0b1a43a04b87058d21d031632ca490e818b1955248740b48e2a9243a062f65cc921d02d338e6490e818bd943248740d1ac619243a058e7388521d024f398c090e81275cc6048740972e132843a049e7319421d024eb98ca10e812e5c0650874087cea31843a043d7518c21d025d380c610e812e5c0630874095eec90843a04b77648421d022f39cc329481175ce6194a408deeca90a52064d635485290332a92c2294811d9c4654ca408eae232a652054c735493290278b88c09948193d95320ca40c9aca99065205c8704c83290364992c0194811ddd95114640ccac4a88a3204
  | 17 => 0xa438b15262cc521c58a8b166290e4c5358b3148717aa4c518a438b152628c521c5ea8b146290e2c5458a314861fba2ca98a430f1d1654c52187cedaa26290c3c76d51314861f3b0a898a430f1d8544c521c9aca1926290e1f5498e214870e2a4c710a4387d516388521c38a8b1c4290cce73d922148747aa4c710a43a31526388521d8cc7a8c4290d3970d93504869cb80c9a82430f9d263d412187ae931ea090c3f7458f504861e3a2c7a82430f9db545412187cec2a2a090e1f54d8d504870e2a6c6a824387d506354121c38a831aa090d3970d50504869cb80a82824387d526314121c38a9318a090e1f5458c504870e2a2c6282431edd95014121ab0e6a80a090e1e6498c504870eb24c628243879916314121c3ac8b18a090e4f7258c5048726392c628243961c163141218daed990a090e4d63cc85048726b186428243175ce61d502187eecaa0a810e1d5458c540871caa2c02a043879916315021c9cc7310a810e4d63988540872ab1cc22a0439698e6015021cb2c7300a810e6a62980540871d322c02a0439698d6015021cb2c6b00a810e6a62580540873930ac02a0438e9d1601502187ce9306a610c3d74983530861f3a4c1298430f5d26094c2187ce8302a610c3d74181530862fbb2a629843875915314c21cb2a6b00a610c3d70990530861fb82c8298438b5926214c21c6ac9308a610c3e74980530861eba4c0298438e9926014c21c72c9300a610e3a74980530871cba4c0298438e9916014c21c72c8b00a610e6a62580530873930ac0298438e9d16014c21c72e8b00a610c7a70197430863cb80cba18431b9ca6590c218f4e032c8610c79701964308637baac5218431d9c66550c218f4e032a8610c7970195430863b388ca218431e9c06510c218f2e03288610c5e73d96420862eb9ecb210438d552619082187ce9b2c6410c3d74d96320872aa9cc319043535ce520c821a9eea9906410c5e73d96410862eb9ecb208431bdd562904218bce7b288210c5d73d94410862f398ca20843175cc6510421c3ca8b188210e1d5458c4108716aa4c4208438e9516010421c72a8b008210e4e5398a3108726a9cc5188430f9d0650c42187ae83286210c6f755883108696ba0a7908435a5c053c84218daed2944210e4e6394a210863abb4a5108438bd976448421c5eca3224210c6e76d5121086373b0a6908434b5d05348421ad2e029a4210d4e7394521086b2ba88290843c95504148421b8ae620a4210de17010521086b2bac6290843691d13148421e88a698a4210e3765d91210871bb28c890843715cf6248421acaeba124210d67754c9210871d384c9280430f9d0635402187ae831aa010c7b76540500871cb22a0280439658d5014021a9ce7a94a5a045e7398652d022eb9cc3296811bdd95214b4093ce730c85a049d7398642d
  | 18 => 0x10621c72a8b008310e5a53580418872ca9ac020c43ac5056010621c9ca73146310e4e5358a31886a739ea990c439359653c8621c9acaa9e4310e556594f218872ab2aa790c43879925394221c3ac929ca110e1e6454e508870eb22a7284438e9c264942218baed298a110e1e6494c508870eb24a62844317dd95314221c3cc8a98a110e1d6454c508863dbb2a0284438e5915014221b1ce7b16a890d2d72d8f544869ab8ec7aa243479cf62d5121a3ae7b16a890d1e73d87544868eb9ec3aa243479cc60d5121a3ae6306a890d2d72183544869ab88c1aa2430fdd95415121a5ae5b18a890d2d7218c544869ab88c62a2434e9c06315121a72e0318a890d1e73d88544868eb9ec42a2434e9c36215121a72e1b10a890d2d72d805448716b12c02a243479cc6015121a3ae6300a890d2d72180544869ab88c02a2430f9d260d4d2187ae9306a690c3d70992534861fb82c929a438b9916294d21c6cc8b0ca690c3e74982534861eba4c129a430f9db5454d2187cec2a2a690e3b54d81534871c2a6c0a9a438ed506054d21c70a8302a690c3d70d91534861eb80c8a9a438ed936054d21c70c9b02a690e3b74d81534871c3a6c0a9a430f9d06054d2187ae8302a690e3b64181534871c320c0a9a439ad886054d21c74e8302a690e39741815348738b88c0a9a4317dd95314d21ab0e0a98a690c3e74980534861eba4c029a431e9c365d0d218f2e1b2e8690e2c5498b434867238ac5a1a431edc16550d218f0e0b2a8690e2f54189434863b3aec2a1a438dd506150d218f4e03288690c797019443487162a4c421a438b1516210d21c68a93088690c7475584434871a2a2c221a438d15261d0921c5ccbaa48490ce67198e424866739cc3212438dd506150921c58cbb228490c6e761514248753b20c2a1243399d46150921cccea30a8490ea75418542487522a0c2a1243395c06150921c58a93108490e3454987324871a2a2c399243399c764cc9219cceb30e6490e66759873248753aa4c399243a915261cc9219cae130e6490d587054e324862f3b0a699243c3d51320c921e18a89906490c6e75d90324867238ac8192438b994540c921b8ae32986490c6f7654c32486b4382a61924333dd9530c921e1ea8a986490f0c5454c32486e3b8aa619243721c1530c921a9eeca986490e4f7654c3248787ba2a619243c31d1530c921a9ee2a986490f477154c32487a5b82a619243531c1530c921e90e0a986490d487054c3248726a9ac0192438b15262d0521c5ccb2148290e2f54189414870faa4c620a43871526310521c3ea8b188290e1c5458c4148717aa4c420a438b1526210521c5ea8b108290e2c54588414871732c8420a434d1d54110521b48e4a088290e3b54980414871c2a4c020a438ed516010521c70a8b008290eaa425804148758a0ac02
  | 19 => 0x6312a020d597318950106b9388c4a80834e5da4254041a74e7212a020d397190950106b938884a80835c5c44254041a76ec212a020d3976109501069d39884a8083ca9c84254041e64e2212a020d39711095010798b8884a80834c5c44254041a74e9192a020d39748c950106b938c64a80835c5c63254041a76e8992a020d38744c9501069dba064a80834e1d03254041e9264192a020d3a72d05501069dbb282a80834e1c94154041e66e2a0aa020d6a7210550106b4b9082a80831b5da5214041c9cc7290a020e4d639485010637bb2a4280839398d5214041c9ac6a90a020e6a529805010734a94c0280831edd95014041cd4c4a80a020e69625405010726b1cc5aa6439598d61d5321cccc4b0ea990d1e73d5254c868f39ec8aa6430fdd95415321a3ce9a9ca790c3e7498253c861eba4c129e430f9d06054f2187ae8302a790c5f7654c53c861f3a4c029e430f5d26014f218f4e1b2e8790c7970d9743c8726a9cc5a1e43395ca6190f218f4e03288790c797019443c866739cc3216431b9d85450b21c6ca8b088590ce671d9332c872b29ac21964353dd9530cb21c9eeca986590d4c7054c32c8726a9ac019643479cf549072187ced2a28390c3d76d5041c868f39ea820e438ed516010721c70a8b008390eaa4258041c8636bb065286430f9d3635432187ae9b1aa190c7b7654050c872731ac5aa4439558e61d5221ccac530ea910c3f76550548871caa2c02a4439398d6215221c9ac6b10a910e5a63980548872cb1cc02a4439a58a6015221c74c8b00a910e5a63580548872cb1ac02a4439a5896015221c74e8b00a910c3e74983538861eba4c1a9c430f9d26094e2187ae9304a710d5a7015253886acb80a929c43535cb6494e21aace2324a710d1e74d8a538868eba6c529c43479d06194e21a3ae830ca710d5a7018653886acb80c329c43479d26094e21a3ae9304a710d4f72582538868f3a0c129c43475d06094e21a9ae4304a710d5671182538861f3a0c0a9c430f5d06054e218bcedaa2a710c5e7615153886ad380a8a9c43565c05454e21aa8e2b22a710d1f74589538868e3a2c4a9c4356dc16254e21ab0e0b12a710d1e74981538868eba4c0a9c43559c66054e21a9ee4b02a710d1e74181538868eba0c0a9c43535c86054e21aace2302a710c5f7654c538863d380cba1c431e5c065d0e21c9ca73148710e4e5358a438872aa9ec2a1c439554c6150e21caca6b088710d3970152428861f3b4a8a14439554f6150a21caaa630a8510c3d76d50428869cb80a8214439594d61cca21caaa7b0a6510e4e5398a418872729ac520c43175d663106218beeab188310c5d7694c418862fbb2a620c439394e6210621c9aa73108310e2d54588418872729ac420c439354d6210621e2aa6a088310e5a53980418872ca9cc020c438e9516
  | 20 => 0xd7318152106b5386a6a90835a5c35354841e18c929aa420f0c6454d52106973a4c6a9083599c66354841a58e8b1aa420e4d6318d52106a739cc2a9083535ce6154841a9ae620aa420d2e7498152106963a2c0a908353dcd6054841a98e6b02a420d647158152106973a0c0a9083539cc6054841a9ae6302a420d6671181521062ebb4a62908317dd95314841c9ca7310a420e4d539885210637bb2a4290839398d5214841c9ac6a90a420e5a53980521072ca9cc0290839a54a6014841cb4a6b00a420e59535805210734a92c0290839954961d084196ae331c8420e1d6554e4210716b2ca521083c394d5290841e1aa6a948420e2d52582421065bb8ac1210839554e6110841caaa6b088420e66525844210786a9aa421083a9989611084196eeab088420e3775584421074b29ac221083a554d6110841d4ca4b088420ea552584421063d384cb190831e5c2658c841c3cc8a9c6420e1d6454e3210716b24a5190839554e618c841caaa6b0c6420e6652586321063d380ca990831e5c0654c84196ae23226420e2f6454932106a639aa4990831e9c2650c8418f2e13286420c3d75d90321065ab88c8190832e5c0640c841a9ae72906420d4f754c832106a6baa641908393d95320c841c9aca9906420f0d5354b411061ebb4a9208831d5da5490441e8aa6a948220c3d70d954110717b2ca4a08838bd955250441e1aa6a928220e67659494110733b2aa4a0883d154d525044196ceda128220e4e6394b5010726b1ca5a80839398d52d4041c9ac6a96a020d6a72d4250106b4b96a12808317dcd62940418b8e6b14a020d5a73d4a50106acb9ea528083d294e5294041e54c9294a020f4a5354a50107a4a9aa528083ca1d15294041e54c8a94a020d5a7314a50106acb98a528083ca54a4294041b62e2214a020d3b7550650106b9baa83280834e9d36294041ab6e6b14a020d587358a501069d3a0c528083569cc6294041ab2e6314a020d727118a50107a499065280835a9c86194041ad2e430ca020c5e73189501062eb98c4a80834e5c24254041a6ae2212a020d3970109501069cb8682a80830fdd94154041a76e0a0aa020c7a76d4950106ad39ea4a8083565cf5254041e94a7292a020f28749495010795324a4a8083d294d5254041e92a6a92a020f28745495010795322a4a80831e9d85254041ab4e6292a020d5973149501069cbac84a8083c694e4254041e32a7212a020f2a529095010794a9484a8083c694c4254041e32a6212a020f2a521095010794a9084a80836c5c44254041e54a5a0aa020f2952d0550107b0a9482a80834edd54154041e54a4a0aa020f295250550106b9baa82a8083d85494154041a74e5322a020f3171991501069d3a6c4a80834e1d16254041ab6e6b12a020d587358950106b838ac4a80834e9d06254041ab4e
  | 21 => 0xb1aaa2c22a0658e5516015032c6cc8b08a81966662584540cb3930cc02a0659c5866015032c74c8b00a81966a62580540cb3930ac02a0659c5856015032c74e8b00a81961d5498e420ca36bb4a719065395c4604c832c9aebb2a64194cd71d95320ca67386ca99065939db654c832a9ae1b2a641954d75991320cae5384c899065725c2644c832a9eeab2264194ce76d51320ca673b0a899065c3550544c832b8ce22a264195c571151320cae5380a899065725c0544c83299ce1b0a641954d75985320caa7baac29906563dd1614c832b18e8b0a64195cb70585320cae4382c299065535d6604c832b1ce9302641958d74981320caa7baac099065639d0604c832b1ae830264195c671181320cae2b88c099065935d4604c832d1ce8302641968d74181320cb63388c099065335c4604c832d8ae230264194c571181320ca67bb265a886533dd93294432b8ee2994a21943e74982510ca1eba4c1288652e5c0645443299eec992a21968f644c9510cb4632264a886571dc5325443287ae1b22a21947a70191510ca3cb80c8a88654e5c06454432c5ce4322a21962d72191510cb1ab88c8a88658e9c0645443287ae0322a21963970191510ca1cb80c8a88650f9d0605443287ae8302a2194cf764c8510cb473226428865a359132144328eeeca88a21963564544510cba2992a228865b24ca6014432d9264b00a21967151580510ca67bb265a8065331d93294032d1cc8994a01968d644ca500cae438265280658e9c26494032998ec992a0195c8704c9500cab538464a80655a1c13254032c9eec992a01954c764c9500cb263b264a806553dc53254032e96e0992a01954c704c9500cba438264a8065521c1325403287ce830aa01943d74185500ca67bb26428065a39913214032d1ac8990a0196c532984500cb62992c2280651edd95014032c72c8a80a01967161540500ca37bb2a4296831edd95014341a9ce7a94a520c5e73181529062eb98c0a94831bdd95214a418f6e0b2a6520c7870595329065ab88c8194832e5c0640ca41a9ae72906520d4f754c832906a6baa64194832d1d1610ca418bee6b14a120c5c7358a5090696392c8a84834e5c04254241a72e1a0aa120c7b765405090726b1ea5292831bdd952149418bee6b00a4a0c5c7358052506a739ea4992831e9c0650c9418f2e032864a0c3e75990325072732a641928393195320c9418bce7316a0a0c5d7398b505069cb8483a82831edd95014141a9ce7a94a420d4d73d4a52106b5386a5290835a5c352948418bee6b04a420c5c7358252106b5386a7290835a5c35394841a5ce9b1ca420d6671d8e5210726b18c729083539ce6194841a9ae730ca420d2e7498252106a7b9ac129083531cd6094841a5ce8304a420d4e7318252106a6b98c129083599c460948418bce6302a420c5
  | 22 => 0x400180000040000008010000014003001000a05200000000180020010018002002008800000000100280000180250058004002003000800400a00101900000060070000004000000000800c00a006000006400000700380040000030030018000005001800c012000000000003c003001803400c00100700040000020000000006000008002400a00a00080000060020030004000008000800800400400000040000030010004000000002000c000000000003000c0040000014018004000001000c024001800c0040030000044000009001800806c0020010000004003005002c004001004800000201d001000800c002001002000001b000002800000200400240060040030004000000001000c00600300e00000000000000000000001001002000600600380000920000000020000001000001c000009002000c00800000480240040070050030016001000801c016005002000400200e0008000000010000001400800000180000020030060020004000000001000e003000000c0040050018010004000001800800a01300380100040040008000008001000002c012000001000003a001ab4e1a9ca7a145f7654c53d0a3bbb2a228e85569cf50943428bce630aa1a145d7318550d0a3dbb2a028685559c75394e428ece2302a721475711815390a2fbb2a629c85559cf5194642c3ee8b1ca32161c7458e5190a2f398c0a8c85175cc60546428eeeca88a321534715915090a9cb8684a84851edd95014242caea6b0ca6a145f7654c5350b2ab1ea328a851ddd951145428ece331ea0a14757198f5050a9cb8485a8285179ce61d41428bae730ea0a147b765405050a3b388c0a98851d5c46054c428beeca98a621655535845310b2ca9ac0298850f5da54908428daed2a4842143d70d954210a2f398c0a8885175cc60544428eeeca88a221655635445110b38a8ac0288851d9c463540428eae231aa02153970d095010a1fbb284a80854edc142540428bce630aa02145d731855010a3dbb2a0280859658d5014042ce2c2a80a02164d6398b548cb2ab1cc3aa465955ce61d5232cccc4b0ea91953671d52548ca9b38ec8aa4650fdd95415232c9ac7310a91961e5458c428ca9b3a6a328c650f9d2609463287ae9304a31943e74181518ca1eba0c0a8c651ddd95114632ab4e1992a11943e74d85508ca1eba6c2a84651edd95014232c76a8b04a89966962982544cb1d3a2c12a2650fdd95415132a72e1320a89947a70993514ca3cb84c9a8a650f9d260d453287ae9306a29947776544514ca1f3a4c028a650f5d2601453287ee8b0ea09943c74587504cb1cb26a1282651edd95014132c74e1320a099559708c8504cb1b324c2282658d5926114132c6cc8b08a09963564584504cb2b192c2282651e9c061550328f2e030aa81943f76550540c
  | 23 => 0x401600200a8000004004002803c0060020080008002005001000801a00600200400040020000054002002004000400a001000004c0020010000000010001002802c014005000001801c004001000001400500600040000010010000002007008000000e003004800000000200200a800c000000001801a00200280000000080028064000000000800000a0030010000016001002000c00c00000400040340060000000006000000000400a0000008020002002003000c014006001803c006002003000001600600080100100010000008002000008000000200a0008000004002000000c00000300000040020000060014000004000000402a00300f0008004000004000c0080010000010000000000801c01a00500000000040010048014004007000000800a00d00080000040030088004014003004800000a000003004401400100000140040070008004038011000003400000300300040060010000010000005000800402000000200000280010000000002010001000c004014007000c0000020000010010004009000400a01e000000c00200100000000100020000008008001008001000800000000340040220020004002004002801c00c00500280000220000020020014000003800001a0020000000000000001802000000a00080240000010120000000009000801400000000080640100040058000006015007000c0000000048010002000000000c0000030000008004000000000000400100500080080070000008006001000800000000000000100020080088000002000000800c004000003802805201b00080240000060008010000001000001001000600300000020020000014000000000808800000100800180020000008004000000000800400201a000000800600b00200040320010000004022002002000000801000000100380030038018000023000004c004000002000c0020010010010000001002001c00000700000080100040080000002001000800002000100080140000020000000000001003800001a002000000800800f000800c026000001001c02c001001806800a00000280380020010038028000000003001000e003000000401800800c805404400100080240100010000000002003000001c000002001800000a0010040010016000004800c00400000e002000200400400000020000000004000002000000c00200100c80000000060028014006000000000c00000000080280000020010014000001000000000e0010038000000000000000000400200000000200020058018008003003802000c002000000000000000000000000020088000000003001800c00400600680000000020098004000007002003800200100000040020010008038004006000000c00800500000080000000000000000
  | 24 => 0x854ea7f1684000eda00068609a97b2b5651f30889f20000000b15bf030acf0233400073f00032f51fea0900024a477e1ff2eb800000093772200007c285d11d89e00bb64f262d88960a8704768000000a2b00031104aed334d3c0000000005dd030000000039b29b800000035600003fa16600011d4000000000000106e000000000000000000080020240030000006000000002000a00500280100100010028000016000000003c002001002000400a0000000024004000002000c000010000000000a000000801800c0000008014004002001002c00201f0028000022000000002400e000000800800a000000000400c0000050008032000005001000200e001800002c000000000c03800a0000010008001005000c00e00100600140000070018018000000000003001e0000098024000007003002400c0070000008004007006000c000003008800400200200100340180030020000000009001800000200100400000200000010024010003000802000000b0008000000009003002c0060040020030012021000002c00802900100040000010020024004000002002c00000900080000000260008004006003000001c00000200b000000802900100000100000000000004002001801001e002000000000000f001000002a001000004000c001000000400000100200080160020030000000000000801800200400180000020080000018000003006001400200900c800c00200000000000020000048004004003001003800000800200000160000008010032000008001000e001001000000c0000008008006008000000800e0010028000004003009004c00201400880000020020000014004000005800c00a01d000000800c00a00100340020000000014006001001000c0060010050000014000012000001a0130000010000001002008c01a0200018004002000000002c00000300100180060000000018004002002801400400d0000000002003000000000a00000000f801c000001001000201000000400000000030044000013000001001a00000000000020030018004004001000001c01601500000980060050010018002006002002000e01100280340000020000000010001000001002a003009000801000900100000160020008008000004000800c00a00000180180180000000000000018001002c00200000700100040000010000002001000811c00a002000000000000200480000000010008004000000000800000000c00080a0002003002004c0040000008024008005001801c012000000800400200000480000060010038018012000002800400e001004002c0040010018020000004002003c008002004800c00c0000000000004003007000800400e0008000004009000000800000300000000500030010018000000001
  | 25 => 0xe02a8000000d62800000101853c581e78414cc7604ea0d4f444fb07f4ac8c62a101020e3e3ce3425e81718990e726dfb9b87e02bcb698cf97f8b428000000000cd22901974fb0a203c400008aa6af000000150205a180119486e0c200013780009650002cf20000000000580000c130000000000e7700029f92469318000ffc00086c30280000000366dac00000040e5cb9120f3a000605a9c8000bd6381e3993b40000001f000003f50002f246a4000000000000024b2a118f52c000051b860c000adc12ab24400000000000000621d10ba076814d416604145576639a0b7ebe92b073c741362c818ce24f180004d10006a90001afc8f42b90000000000000000065edab00037a4000e76135830ac780006b9825c000e046a499e4028b013810a3da1a9476bc0a02c4e87606c2b58794d055b717f4230bc500c4996087a6a410992c3e498eda85b94f223442200000a32a3307d00002c40006ed0a3439db4daf9aa718361c33d90ec445a0a501f15204dcdcd000147047c0910df662c0e21bd80022540000004f79499573ad00000e711c862b5068df46f636d5a4aeb8000922000000000074e000000129a00000036981820000bb22f8a285f816776909140005f700015e00000000000000000000066c38c9a5a1e14a5cfa2ab448a6dd422da9000000000000033ea165132eba5319c1835702f01043d9bf600037b8000000d0170da73c00000000000018fe00000033120001ccc8504b8000aa8216207c00055b64f99d9a427220000282cbe82700005398f0000037b1e20000002f2a1300000002359d7400000007acf68f840004a125997b64cda5bb5885ba34c62c190dc8cce15670a50000e195b2243c0000000001d3d606bcc14302b400000000000005be53b1368000b324ca00025d80000000002870000000000270d00a82a3de03acfe8cef01d64b82ac87300014bc0a689d4a8843148a55a15e28580378d76559a2487a0a5940179d262a880520deee1e5e3000000000000047ca05d4a68ebbee00019ee3ef3090b6933200033380000003dc4e440001b223626a0000000970007400165a93e46180000000c1800000008651e05f0000f48088000000152c3111b72f080e03de2b880000009fb678f42400000000000000000005f537f40001aa80033ac0cce280001259292000000153c00000000000000000000003a4c5f2b2c8008f097ba17067309e62e4a2c8571e4c000a250002d48000000000000022d3750ddb51488a00000000e73d40004b880000005820b78e24d151d661a1548e800331b6000000000007100e11de00000000003223a680026e400000000039a910847d80000000000004dd0001a228f8000000000016cc3e8bc40000000818c6400086843bb718724b9d7490000000d1423f37f8000d9869d0001980bad0002a7
  | 26 => 0x5113e00003a00019726ca3ad2cac00000023800012a418b0fe0000140000204b6f843e0000000000caaa676ca26ce1972263d800000000000000570000d2713b347079ca8a62d000016eb6a293b80d518dc904fc00162e0000000001624df00a9000000086900010bd52e31e2698000f4d0005f980000008ae3959515cf7cd02b736d8a7e25c487ed73a475bf682187c077019800406c1c828514b0f459e509934820b457c1335c4331dafad8a58c18543044b01ca89ed962ac412f83c537e49180b6041c6ed3673f00000001aa00009040007e1000000000049a2c1a9e145bce02b080380005bc2840333bb2b6f6e180341adbc011a98bc76e000304800087e3be0001f2070200000000003c8000000147bcc4a80000000085c07b0c6691c56e040a6d6ad038900025603740000e60ae80000002e62a000000000000001620000686000105400000010ac000000222722ac340000003bb267c00000028d00000000003f9000005600000000000000000003018c8c8b20002fb0a1e80441600019e8b5a1c800000721d32514b4956ccfa4820c2e85021c985118c00000006f0001a524c545b40000000000561cf80000002ac2955cf8bcf48f7149732333696a0b6c9c0006b70001528d4748b9c30000cd7338995c0000004d4069400000065006393ae7450003289154839599f0a400000021d8fac0000cb000000108000000003f4b68000000041e000000000000000013580000010cc7690000001c9a2490002ab80004a70001d111700005482d0c000e2257010740000000000b090c6390a7b269070e000000116b29685f00000008473a50000d5dd5e6663d60001270b6d23e8d7472324be282b540c800004a800000000002f3aa87908457219ea040600065600592f21250002f05d2a00010c8000dd810d66480000009914fc297c000dd75d2a3d294c0001f392400001cf3837654588a6c66aa20000091900006748f68c4117000000000000024d00000000e90000daee4e1c78414000e0b0d1aaded17451000138131f6700cb817dcd8cf24d82fbe00000014a86b506484a2bca5d17e42fc00612a06f408cda4de086bebbf56d8000c106520d100015b400064480000000000000000bf2000000325c708000516800086800042980002d4000279b3180006191c98dc00002000000000db8a990000001ab900047969518600000002326b3883c562a381226d930e7eb9c00000000032a440a00000000003a5000454acb81660005cb2660b940001838f998c60004d10000d6a1be00000013470000000000ba295019e0481184e244a32a940000000000000832000000011400027a4a4000000000000026546740003b3800000099215a959f6d009000000000000006fbb3046990000000000000d8721c87b8dd6b48000000169463a3a485253ba1c
  | 27 => 0x7a80032080009f62c6831c59e9e219eb56e00029c5e39de9cbae856e993c80004848000000e3800014c90188f0d181900001598be2524e6b978c000647b8e1b5047273200019be8a200030b40002c822603a04019a600036c800006900000009c221135a37a899f00030a263c33e01180037b095500067f97fc0009b50400bfdb3a996e8d4ae43ecb8c0001c9ccda109476124c00036b0ca000000089300003520000000000001d0e0d313f8000626000683d9f0810e8f0001094000b300000001abde3000021bc00000000022514ca4e332ca53c7c471b38f00000000001aa800000000060b98455223cd000127908400000000000000000000000dde0004942bff3994a98640095d7888f5d49694db00ff800381400078e0000dc58fc0003d3848d69de5800000000680006e89688b5cb0f4b48a6c9b0b4167e14b1d3856fd96ec91a3a22000008f5d0f0000000000aac0002a68001804000139c0000006600001dcd4768d30001a0ce55afb000000000056b2baa6f4f720000001c69a7cbcd143800000000034425260006280002188c3a000000000106282b160870e000e3b275ba796d20002010000000d1e000169c0005e44f215045c6281651917c0007ab00000008227ff02b8868eb8d5a023c1953687bb07e1c2da4063b97e80000000005d300019740006a200015f2ca815b67c0611570000290913800025eb717365000250a5ea000e2f60c83f9c343436eec00180abb16c7a7a108c3a438c8e5d7ead642bf0cece3b0000f4e650f026c327ab5580000000279218000000000000000014c00022e8000de722200017e016e46da6438f80006640ab0758d130000000000b3f6d08000126ca600000004d3d27d65b5f03842680003518b90d9eafb8aea00000011e3770000523000000000000042a284d6abded0000001384d68105000000095d61786e581a00000000001c603200000000002651335ce851c39b0ca9e9423cbeed1a0340d34075d37b9ec0001ab01d00000006ad9bb80a327418730b07a40431d48002c8c28a569450a980000000000000174ecdd5a9ec1901c82037d98056f60a4887cf909b30002db2b0ce9a000050c00153e22f6e2b6e9562d6d3f6ace887f90e11bdf7d7d02ce0eac0017da67a8bf29ad044339228000003026136a8fc43880004b082fb5541f367492d8cf63d74a63940fd639d000144c0000c440501f4d1996c5dd8235b96b930003748ee4eb73c38001a72006cd28000f3600022a21c50b800022f0ec00000007440228bda87e00005784524071d9c0013fab488e480016f200000000003d80006140c203e000054d39e8e982f03971ac54830000003004000a2f754a220764e3104f15d1158b623bb520a0005d800022580400000002d8400000000007f80005ba15a28c85daa766eaa62a00016c346f1
  | 28 => 0x400000d5700000009f4c51000171d4100004900000d88a1400030000000001b2154c000000027000027a963719a2a1c000772d99724db2e5c4e298e000000068d859c0001782ee800000000000000000005d0000193483400030f130c73c00000000012767a31bf026150a11280010d86c1c6d000116400000880000000000000000001473000000257c29ed7b80035313a45cd59af40c68ed2306f8a780000db5f4a2ce0000000000000000b3600037e400003b00019a8a9500011fa2abc6a00028d90a97340e023bac006d00280959ef5882000104885a5863f6427800143e78f0000000000d2f70935fa54000000030a98d2cf6800000199c21200011a80000000001d19a2400000006a57a600027bef996840f8165000126ca4a2f503349e040300023f0000d5e000215a00026200013f0000d5b0002d4c0000000002ad40000000002de000035100010906cd000414800025e0003f18000035a194cba1948d24ea3470e08c262d96959de0c20c8a000200a0000f30ee1dd400c00000000000001040000600ce600000000008f4b6b71e9bf400000020bafb60000000000001ced000000232da504a1bca13583f20000000000aa08d85b28000000d52800000036e623576033a580af265f0404c1e00074e89f000000000000000000001e980012300d50000000fec0000001784ef600000006fcf7caa30000000c5c000000000188e2f7000069f49ee1f3a3a3b2ed81ac0000c54000be1b2d233cdceb2c4ea027ce5430937c9da8bea576637a22ca7a5cb07ec2ca0000000001f100006542078c9cb026e24c100000000000000000cd55e05f2358d430e171b50ff122000024b5a980005db3db8065b323c3098907c000a0c60b35ad8560000001c942220000003a81ce065b303a191d6cc660001b3000007c0003408f666533d727e4e4c21ee73a826ede45c42b09c41abb772c480000008ad2e2a93951e6cb3a10c3d95e4385940000fd0112556000059a76b06614b45a3275884c0b45de489394c4840980004ebed2a12c8bb5a82c2498e664085dc93d445944520a60cf32e55e88118e22e3223024543349e925fa20929f9850200fb920610a07e5f98cd84b30cf295d5de13502c8b9c10e49c29a09212f600008aa64d69e0001060c091c251606a27617fc27d22c0000000c2fc1a35609983e89484000ac64a2571a7cc00080961e9660000eb80000000000c200000c0d5da0001121b84b1e1f7000000187600075432cc9fa000096cf30472a484a357040003b45de16a4f9e00000034ece905930000001d5600026ddd400000000001b997244cbb9a25103e80000000001a7085a6c100000000000001fe93fe4913df80000004c44d0204cd82c1d1c88000000b702729ca0725db42ab906d4e070e0003a40ced8ca62016bc0000006930000b241
  | 29 => 0x18b9c8e000a0a800261c00000000013d714cb8c942056145081810fc87902c69f0590d3950cc755118584e58ae1261039cf1698d8de4001acc9ec32418c24acd2da52b01182a81e000088d81800013aac284edcb209a142599bd220a225e00009db22100008466c54d8c0005a20001a333a1a2e0001c2800026cc863318000eeeb1646900000000005fdb8f942e988518b700000000000110c374731119ad98780cf600015257ca63330c3a99222083f4c80008e23940000636000c7b26e00000009cc5cf1290000b312458000520000069f26cb9c0c3ef009c000000044e5eb400016bc09281120c57d206b1f50e89594d9b2d50f8aa24338000d849bb64931b8a0ec232851a602b248531c6c405ac4c91211dfc87b7961e79a6cc52cda0002ec9088a890b1b6585eae395bea1e92d4b8f07f802999a0003b42b6583000042aa0200000470002b2400000015100000000004b7a1343f40ee2fb1a91c56c745ac27580e4aba55d81e2b145445f8a0ed99481c67226c99dc6f374b04b497f0006aec3b11805e916800018f20ab00000013e4000521b24c00018431f800060a473000108a000af6648366da640000000000e2a00000032dd492abf0002004cdc00000032c0e971961a785f534e3a8d50b6cc8741e866798bf6aa31c00000017c017a0001809bec0004c6833c006d1b8e6800107c000425904d32c49816e06261d4ddb00000000000005600000000bb60001ed00003a28000000882c5e13032f0000a2a0000001b1060b653ae08c8a76209500015a45cf3ec80008da000000007d4963d22320000000000000000010ad1654da3788ba397950ae84000dae5db8001d28a0a0003834bd800068500000380000003624000c4a58053740000000000044692ca14d5800090800045580016bc08f503356404c62556f037056007f6a7800118c00034b80001360543500001be80002ae05196720000000ed80006851fa18100000000000001c1eb3d0000c896b2000624000130c0006a4023083c00000000000449b13f801120002db6a80000000000474239516c00063b9e286ca10e621369c000c6000032380f200001080014ac87f0000141256000000319c88c0003ef00000000001dd8a48000abd3e5a8082e22ae14986995ca000435a3041420000000001272d9c0f9ec4c6deceb99592239767dd1af2dd110c1170e452001347703f60ae7d4e91f337aef86709e54999675ca84611f5ed2ca083db1d42961b208e74131ba93be1386c6315851681a4b21242151a6924ca3c0778be79d38395ce26a818695ec06eddd4ff04416766a54c1b7bcaaa46862c864c276452353862f5e2de54e680aa3122cce950e89325ac24c81445a680006ad40000009ee2a58eb94a2b447339bc11a8562324803d71cc0a65524b4000e1101e28855c84eea739
  | 30 => 0xd3aed5ca4600009308dcb9139c25156e6e75751b47ad32b25513845990add805c82ed2ae576dc4a1605660e952d0422e2cc981d33788e723ea71080006c006c2b44000000e9b0a435d9570d6100026780008300251fa80000004c7208c00024d46d29001381b65531df869400026879ad6448dd58123d979421b8f440017d3e1670d6d2e397114054ef840000000000c40d149fc31d8021d1a29a6b2400031a9892b7b8b400089226e469aaa89d03890896000a0548ef91d6e473b1bfb3b0eae00036b18b440d9c80459bfc0000000000f7c000aa93b28358bbe1b56d880000000004470110000d3d039edf8000d898000000dba00000028dee6e7f35342a4c00000012c159c000c0d80036399005220ce03dc57e0000000bb03948b000024c8000e207240cb4ac000055b40000000003d333bafdc1d72f90fec5d011781ea6c2bb82cc133c6c13da9eb31bb43d578ba319fa70042a0006628000000000000386000b0000000000a8e000000000000000000000008b61512881cf40000003688000d22318500000015025e80032b4000000277800000000000000000000001c7000000000058e80000340006190aa04f93a78cc9d850f65b01518a20df4e026a095020fc90c0000000c680000001220000b3200016d43d60005dc00000007d217d8000d7c0c580005cce2f1958000001d343aa00016dc0004e800033a78620ce0000965a48000000364800000009b8000000000000000128600000000006b800000000017feb4c10d80013007d070aabf58860000d786f0a6ad860001eb20001e26d81eaa0001c500010d5a60a2fed1b3ed032bc358d0c9523a1f515d805f03adf32d0a16c0ce70d20903e4340373363346441c1caf3010c4a1c7af000396400000000016a80003485dead191203b557f09f91680006ff80018d00005ba800154800013baf7c00000048e04645c06c00002d387009676c6a4c13526b000019639a95fe0000000b1800000017c0000c64000394846217528597899cfe7f27101051e28b7380800055e71f39193400c4ac610e9a4d448e8e1d7baec4ce991b1933642362b58172121a78ccc1161748e60ead58c83cb91a0000bf80000000b4d48d12cd7667862badc20000005312505aa8ca54db0000000000485400000025e0000000e71be3556b67830200000000009f7b94092000140e00058f96159109d50000000000d0000000019e6ad30f7a34000000000027d000015a4280001be45953ff00000003a0000000000000051a400152a6ee75231c80009f50001c120004aa0fc23e926a6a1000000144c3ad2ecb57c00000043692f0e5e70a32c0ad917ee08158b13981c11a26bdb1c00000062300000000000002cbd2e40006cd2d4a0a448cbaa9e414881061fbb7905f05d5467091097c0000002d34c427436278b4c000
  | 31 => 0xdeb03b0000183c00007900000002fe05e80000006f10000001bdc0006db8001ae80000000000ada0005fc8509bc2448800005ca864793ac226862403f0002d000006fec85e74d4448a73bbf5947661c1c74a2f10ea69d2f4000830a1685ab4c7c0000000f506521e000000000014e20007489c85c3c0000118000a3eba4583855093654c5c830509720003fe00000000610000b84000d600001fd4000639d8a094d984b8429934a24386f81fd2a09b3ea6400008040007090003170e3dcfe000342000070cac3000077240a24b8203caad7f000000123ce5a9ad29ed6c100035e800048a00019a0000000cf134a28d4000000000064e0002b7cbcf82400057700035e5508d06626a6b4f8200000014a1d7200000000002d6cc380000014cccdb13a0000000d071de80014589160e040000000005cf908558500000013b8000000000000089c14726173c0000de868a914d1ace073cc800000002466b06c90920001360785c5cba200000000000ed0001dce0006420000aa57e948100906a200062a58417795e66da5418000d0800028be450dec000292b3d39060006b38001af600048680008920001d0bac4000d31f285fdc0000006752178974000051e56d8ef0000002b50000d9100000000b0c9c71e20e1cd0b8d374800063abfd2bfb30d302e0136a02f64046ab4fbb686fa635016a123015460349522280008c56b5200d20aa300000f400000003c49ab478cb5f00000001b47db0000000fe200000000000000000002ca470cab95b3b1548fe000671b61107a64117580010664d2000009cdea28ceeb050d68ab543c2a975ce838a61c22cc00030e06ba84967d5590099aa5716e51638853400013a083acf8e004b40001b24480e3a3fc9f890a2e2c2cb9b816385ef22530cd10a0fb6a10c8d45223453d3463b2eddf1289474d90a40b9cc00000032e04102e939200073c8000398320980a83849490e800000109d000366a38da49521543b0944b60c33e6b63e0000764960001d06e4f61b98c023a43341213b486070a80022d4cee8f30d21c213130a20648b5c20500031316c85ec0000c31799c7ec3e19499a517acbf59ba96cabc0001b0a4bc000753000161000000000000000000004e300000000005e904a4d7ec94559274537c42025921b99ca1e018d318b87e0001ac80000000000001f5901e766000202c260720000373c000000106af70ce7e690af800000018c483800000000000000000000000002aea92a063000000000000070de33167893c35e1e300000000000000d77da26d9400000000000017ec00000051ea770a834626420fcc97700073334779ea00000000000001cb0001000000340070800115e0000002670000a0b00015e0f860006dc1a3c8b4deb24ea2ee95cc3c1ccb33af70887015225c00000069892a54786b60e6
  | 32 => 0x6ce000000370549800028093d0278752557b8d86432100000ee170a304306397c46093f000271c7168fd6e82ac055a14a25f4a0d84c0006da6d1c0001c71218218b364aff130a4400080d40d80011d6b763329ec60009ac000000078e00000014152bc5a611d0742f3e54a6fd1e5c01650d0002bdc0000001ea35c8000000014dbf8000e5a63100000003fd57aa66cca00000003984d1d3580001cd40000000001c14000000000000000066200002a4000353737b52c16b0000000de0000000588800151aac8756000000000000000000003d600012bc000a5e0d711b00dfe5293c8408f8ea7d400135b5be68d65b23c8000000000395a69300028615ae00000056393f80003242b3000000025d29c891cbd6bac00015e8000b0ac4c0aee000a3815236d47ba10cf0725fd2f40003ea012cc38ae94cd101400029483cc000000c8b00000006c43455d58000fde4ab3c200005aa3160000001a9f2186bd109858e213c6c829c6d200059a000176acb80ee800025892710a0001d16930800000000000000000000003e0241940da3fa015e22498000d810000000000000000000000000059d4001cc64d700020b89f0b5d07a2aad06c4470000001c4a9555d78000000000000197800081e8000d04000af4233000000011f1077085d0000000021e000000000029cc0007040f6b205824366574360c310da0be897e9754ad700000000007516b2c0000000000000000000cb442d40000000000885945b88530464559137829731b0000000217000000173600044611d14eae9f2c8a49400f63e02420bcf307e42d4170caa27d54bb80000007aa0fac9517210000e0a7c5d66d800fd8821b843214f300008cebf82269ae4bf85c46f3000148f00022b800000085216c17681060004c600000000003ad80000000002959f240001c58000000d000001710000000000577122e000000000000024e0006b880000004cf4cfc000000062b948000000cf936700018c900000ea904f52141468afdc0000000000000000889000076d8720002502b34124b8326d80007d275600000000000006765a1c0008b5b2e191d8d61d54d79c90982000174b18400021300035293144df3740a2418c0000001d90a6c7ca0003310a0c000000254c0000000000c30000bd424340005dc53a05a1910000000205800000abef539c001569bde1ff3afd8340006de85e400000058208c80009ca4bf1ed99d505c00000016f83c930b81a94f2be755397b96a2e1d1656fd854c77d69a80000000000003a600008ee15532900004e601aefd0160cd44140e3104b000137800000000000000015f0a3080000003707132110a9400048f50cc28c00000027fa589ce60000001fec00068b0002c986ecd1f06281b82aa00009f800000014b30db1cc8207d70000001ad800000000016c
  | 33 => 0xa200006886612dadc848407980f02c669f8001d5ce570001390000c1cacf043a49e4ce70e1ac800000000019f81dbba062db1b064c5686a7373866e11c568b88c000c496972f07c2616980029353ce000430800048132a7409e188080602f8ab89bbc25049cc7799df5a41d4b6b4000000347c000774a9257e00000000005cc23f800000000000db7687630589bb43ca42b3be325800000072b0000000d690000000c340003510000dbe00000030b143434b1322f54000d0e0941ec559e8d5000232428000008780005bc1d80000bcc000000164a5f4828cdc0d881a100475f3ac8238000000000000000000012b4000c480005ec00005975d37328be872d00000022e40000004639901d7cb7100000000000000000001aa688d00000000000000000000000a3a000000046e0000c8d248000ad83da8001654000507e3c7c8460e0fb4fa79a25d43ca9b418485962df098cd6ec7a2eb1234f3827f9be0fc81124b863501583c60000001f140000000de8001a7f0002c580013424cd34b00012b80001752e1c2f813e0000000d9e000085a970d463d901a96b588a8f5243a4328ace064ef0000cc26682b50d6c000dac1c68000000b57485959561cadd5bfa10473043e75eb2746e89843aa237d812e535c08c2dd187ce58f2a2d2ea86a0898884d247e76170f2d9b07fd099252800047601c4000000273692800000004d5b01cb46ac03055037307c62720002b04000cf80d0ace1d126064128000d5400015c40000000006acc0012040006fe2490b5600000012c4000e784800e20000e4967e80018ca00000000000000000001928178000646000000000002133b400078060780000000000ef8000a700000000cc8000e0c000000000096864c9834658c100000000000000000071e0001909e08ca0cea1b3517069c00073217a29f0c98ba837e34b0000c7030005b4e96a9805fa964dc800024f9f800004ad29f054ce8200019b00000000002fa000000000074b8001cbc000000286dae00000800648000df1000000000000000000012e69d9000000000000000039057ae0004e71b8cb0e0001cfac9cc582538e81e84ee2e4a64d18f7d645cc28c168c00017be987a95a6e0007368000000000107accab580000000c512b400031c80000000000000000cac206184d0c80002748000b2c0000006882af96d8cde0002294000be6d5993b1c9607352928e37003d56aeb34d074682298a94e000e2a3e330478741b45e5b5bd5cc42d00018de9960004d51a4e000a0f09123d6a2400034f000000089e35c000000057c408b61400025a0082a392420004e58001d08000000000000028c0001ae84297cc0d42181146a3609336f0450da04d18fe52f88830841c1c0008b126c909cabab953dd040e78a0000c75668000e4c0000001cb641c75a0a7c00000000
  | 34 => 0x79a295001000000000000009280002d000000003723c6b09d594e340000000000a030d4d539760000000000000007a028a6924544181e210a42f648e7451bd0272635082d5cdb76cae03aa44840e59055b8c6c3159c10385fe18985c238eb89dbea37947b80000000001254328000000251835e49c0001293a2a00006d0a8055c00000000005905e400007a80017385bb29200000000000000cc11027e900023cf028b3480000ae0007e564381247d8c1f05c23ece940000000001c8000058602bca5c6db1c1a46896ace6b3fa018e1389b33d37121a4c30c0aa321cc38795ed19c933a00060e1b480007a04b5a46c000d773790204b62000056745f453000035b2780000000000000b7200046840000000150778000b702380c80d3400000036f0f94a8c8a03052de800000062e882c00066b000089d09c22570513a5b4a0000000001996000000000057400039985ca000045a7bb50c60c642ed52426000bb917201d200075e381a1c8000bc834a80000000003cf00000005370000af5a3416546e2663666e1002d96f4edca5000002d813b009471268a8f870db3a1c600000006258001c2800000000006970000001e0c0000290000fb43e2007000063c32dd7547516000000005858ae000083f0b48001388b1b1aa0f600000005ae35daa2ed538bbb586c40d4d26d01757d61c8134b554abe7da128610cef202c14102d5d6a792058e9dd2a8d4014e80015fec5f38b80000000000ec955600000042bac54314b5b1332f38695d0b26ab0d560544f281250000068c0ea00014c20002b60000000000000000000000000000017cb956000000000039650f00017147144dc00000003350000000000d5c61b1a7000000000013198220005fd1a040000004a7000097600051f80000000006298eac2b6db900009180000004fd0079642a744b70a2800000059a80016c6084255c0000002a08000700000d408000001c52014998800142ac0754ea11c0000000000e8c227000000300c000a39403b25579d0d280037500006b300036bc0000002998000456dc700013e200048248091bdaa2b3dac700fa00093d50eaba800000000029b5d424013ba2424b3e0002e0000170c00038800001283f86e51ab2980de300008580004f11f400015d6e8659000006c600000000009
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xd21d01209a1811c13250120c0c7614d2150120989831c12150120d08531c12150120d08539cb6050120b0a858c9408c1209c1811c1324c120e0853189404c120e08654c9404c120c48621c16154c20c44625c46054c20a498598d600c820b408058c3254420d42735c03254420a19801915348420d08721c15350020b11811c15350020d09535c03250020b21800c95150020b0985cc940cc020e0965cc940cc020f033254540cc02084f87d97324c020a4686cc9514c020c49655c0320c020b41800c9510c020e0953589400c020e09650c9400c020e2162545400c020f0032545400c020e10635454048020c44635c75348020c0c769515348020c0c76551534802084e869d95348020a448654e5148020e065418d5148020e055418d5148020a448694d5148020a448654d5148020c0d7518f4048020a0c8654f4048020e04635474048020a488654e4048020e40635464048020c0f7518d4048020a0c8654d4048020e04635454048020a488654d4048020e40635454048020a8a8398d4048020e098518d4048020c8b7518d4048020e0b7518d4048020e0863d4d4048020b2181d4d4048020a888694d4048020b098594d4048020a288654d4048020a888654d4048020e0b8654d4048020b0a8654d4048020b088654d4048020e088654d4048020a088654d4048020e80639454048020f01539454048020e08635454048020e23655454048020e80635454048020f02535454048020f01535454048020f03635454048020e22635454048020e20635454048020f00635454048020e00635454048020c897418f62480209c1811c1320cb10ac08058c324871084c87595320ca10a48854c9600ca10e09544c9600ca10b08835485250210d09735485250210b08854c83250210d09754c83250210aa0825846150210b09831494048210e0863149404821084c8758d5208210a44835496108210b08835494008210e09635494008210e21525854008210a48854c9600c910c30655c06448510a448558c3248510cc1635c03248510a24825946150110991839c64250110c30655c44250110a31819d86550110991839c66250110c30655c46250110a28865485250110b08835485250110838865d43250110b08854c83250110993835cb6150110c28651c96150110d82735c86150110d81735c86150110991831da21501108b0865cd2150110930855cd2150110ca076dc92150110b8283dc921501109a28798921501109a0875892150110ca0765892150110b20855892150110b80835892150110d81730c92150110991839c42150110a918398540c8110c447518d2148110e086314940481109a0874854048110b20854854048110e80634854048110a93835894084110a488058c6354810949851c1320c810c49651c1320c810d09541c1320c810
  | 1 => 0x2b09841c13254032b41811c1325403294a861c13254032c4a861c13254032d0a841c13254032d09841c13254032d42811c13254032949811c13254032d41811c13254032941811c13254032948805d5320ca41a4980195320c941e05535496110841d12535c44254041d11535c44254041d22525c44254041d21525c44254041933815da4254041931819ce4254041d22725c44254041931811d13254041931811d03254041a488054d600cb21a1a83d516010721e11535056010621c31745c46054d218e1801c5640c921d0b541c1530c921d08541c1530c921d0b741c1530c921d08741c1530c921c49861c1530c921d0a841c1530c921d09841c1530c921d41811c1530c921a488054d600c921aa0825056010521a19801516314121d05545cc4148421d21545c04148421b058414d3148421b418014d3148421e05635895110740e22625456010740e21625456010740985811c1320cb40a88804c9600cb40e05635895114740e22625456014740e21625456014740a29801965248740a0f8558c3248740a888058c3248740c49651c1320ca409c1811c1320ca409c1811c1320c940a48854c9600c940d05735c85150540d21725c05150540a1683d9051c8540c24651c54248540c92325c4604c940a2481594520c9409a1811c1320c940985811c1320c940b81811c1320c940c89861c1320c94098a851c1320c940d0a851c1320c940d82811c1320c940989811c1320c940d81811c1320c940981811c1320c940988874ca600c940a88804c9600c940988874c9600c940a8983149600c940c8b874c9600c940a88874c9600c940c88874c9600c940a8a854c9600c940a88854c9600c940a8b814c9600c940aa1801c56214540d07731c95114540d04731c95114540924879895114540d04739895114540924875895114540d04735895114540e05635895114540a33865456014540b20825456014540e21625456014540a888058c32c8540c89635c032c8540a1683d9451c8540c0c651cd5248540c24651c55248540c24659c732485409a1809c73248540a0c8558c3248540a888058c3248540c89635c03248540c0c659ce2148540c28655c22148540a14835945108540e20521456008540a28854856008540a30854856008540a8a83d8a62d4140a8b864c832d4140c4a765c0534cb20c44535c4604cb20c2a725c06454720a318115160107208c9878c8604c720c2b655c06448720a488058c5348720d08531c132503209a1811c13250320a14835846155220d09549c3530ca20c49769c3530ca20d09749c3530ca20a31819516010620a0d86d4c32d0220a0e86d4c3250220d0b535c03250220919801d16114d20c15745846114d20c51615c06114d20a4a85d8c604c920a1980190534c52084d8714c6048520e0b6414c6048520c0f7614
  | 2 => 0x1bf2500000000000120000000000150104696c63931848c248158478c4728de578b00a00000000001b80e1e00012c00000000004c033399a53018c00000000005bc061c0006d80000000001dc8c182410684e10c00216000da249607c1ce7582600000000000005270244000a2000000011c00000388f1001843e9760b0000000000000210ac000a000000000000000091800828000019e00042000e70000041962001fc0aa266720e000005c8648e0d62a20207000000000003c8f22a000000000005c723705c269590021400062000314d23500122000743b800354245a552100002d00088800000002580022800001244509b648206a89c0210200000000007d000000047e00033a323b0610000053800000005a9a27b40000000741543ec00000000009d2f0004e8f43a43650916110002180000078051a81f20c725a3000006f830001442987e6f00c4146612a3e5e0005d00000000000007c936000a4000e00021800000000ea6197c6b40266800718004c800000000000000000000000000059ce400090001ea000000000000000000000000000000001ee0007a12034651460010f0000036000000820021c000000000000000001703e2344a8000015a73000058003bc003493c00000810be00000789d40000042000001500021a1594c570c6000000018a000000008e601e887973068b879000000001b000001e63214803800428ca0c8ba3f080000005e4f60000007939000004f85b330d0000ed441c42c8e8029c800046000dd3c9cb17888499d24b800841907d800000009086e4497a6d08c0fa37000ab001c15b996660d400208130aa000006e8004600000000438008b80027a247b1ac7685a0002e680585580000000001c20004e1416600000000002b8002623a62164000000000000000690001a94a0022800000001d88b1de7f800000005a022000f03f5a7002400e8001240069a00401b0000003f800000007ea0650000000768d8606c975000b6920185fa20085286b805000030040800c01018030040000c02000010000001802018010000500403000050000000c0000003004040000401c000000000000014000080100007004010040000803000000080000000004090140001c0200000004000000000001028010140c0000300002000000180700001018050100100c0800c02000000040800c0300003008000000100801d05545c4544c832d09545c0544c832c0d759d0604c832c0d755d0604c832c45759c4604c832c45755c4604c832c86745c4604c832c85745c4604c832a89801913254432c2a725c06454432c29725c06454432c31715c06454432e05644c95114432e413254560144328c5811d93294032c89641c132940329c1811c132940329c1811c13254032961811c13254032945811c1325403
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xc8034509000034600210049d0088180000120000000001c6c99000844d10000e231454f8b0818b07405ac0f2e080003100405027840210c084f100802802620591811c13294032c814230238264a806590184604704c9500cb0130cc20e0a986490e10619811c1530c921c80c2302382a619243281912013258032d03082cac08e0990652062061a811c1320c940c40c330238264192811819121d32980325025032240264b0064a060121d6358951145409104c2c4a8ac028a81a00835895158051503040cac04e399242a0502255635c03248540c8029b0238264a064140a96d4d700c94088221330298e090a80906401c9811c15350020d0031b03a9a809004120a96a195350120082c012ca9ca2a02401058025a535454048020b004b2a6a8a8090041108985d5320c94084241130b1aa4a00410858024d525854008210a204aac6b806490a2188076a0f7248540443040ec42ac490a80886201d8835892150110a404b2e619242a0221500955cc32485404431010e31a42a024088680214634854048110
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 29
  | 6 => 1134
  | 5 => 6283
  | 4 => 3776
  | 3 => 293
  | 2 => 37
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
  | 7 => packedAt gbK7 (548+((h/14+packedAt gbK7 (464+(h % 14)*6) 6) % 56)*6) 6
  | 6 => packedAt gbK6 (36338+((h/520+packedAt gbK6 (30618+(h % 520)*11) 11) % 1874)*12) 12
  | 5 => packedAt gbK5 (274902+((h/2582+packedAt gbK5 (238754+(h % 2582)*14) 14) % 12372)*14) 14
  | 4 => packedAt gbK4 (203731+((h/1439+packedAt gbK4 (185024+(h % 1439)*13) 13) % 6270)*13) 13
  | 3 => packedAt gbK3 (18690+((h/111+packedAt gbK3 (17580+(h % 111)*10) 10) % 586)*10) 10
  | 2 => packedAt gbK2 (2705+((h/13+packedAt gbK2 (2627+(h % 13)*6) 6) % 60)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7f83fe3c7fffffc1e38fc7e071fffffc19c1ff
  | 1 => 0x87fc3fff81f1f1fe03f1f8fffe38383c667e93
  | 2 => 0x7ffc03ffe01fe3ffc01ff007fc03fc3878f1c
  | 3 => 0xf800003ffffe003ffffe00007fffc003f80fe0
  | 4 => 0xffffffc00000003fffffffff80000003fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa000441080800041028124004a0a2008c025
  | 1 => 0x11088c080c2222060090484332109098221692
  | 2 => 0x621194912465405aa401520954812589870b18
  | 3 => 0x305b2922494064ad2aa4001269258112f00dc0
  | 4 => 0x4462300371898931d349a49c000606235de000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeeceaa8feeceaa8feeceaa8feeceaa8feeceaa8feeceaa8feeceaa8feeceaa8feeceaa8feeceaa8feeceaa8feeceaa8feeceaa8feeceaa8feeceaa8feeceaa8, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12891
namespace PEqualNP.Outside.L_meta_12891
open PEqualNP.Outside.L_meta_12891.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_32 : Interval gbAtlas 2 32 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 37 := (concat bgb_2_0 bgb_2_32)
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
theorem allgb_4 : Interval gbAtlas 4 0 3776 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)) (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 bgb_4_416)))) (concat (concat (concat bgb_4_448 (concat bgb_4_480 bgb_4_512)) (concat (concat bgb_4_544 bgb_4_576) (concat bgb_4_608 bgb_4_640))) (concat (concat (concat bgb_4_672 bgb_4_704) (concat bgb_4_736 bgb_4_768)) (concat (concat bgb_4_800 bgb_4_832) (concat bgb_4_864 bgb_4_896))))) (concat (concat (concat (concat bgb_4_928 (concat bgb_4_960 bgb_4_992)) (concat (concat bgb_4_1024 bgb_4_1056) (concat bgb_4_1088 bgb_4_1120))) (concat (concat (concat bgb_4_1152 bgb_4_1184) (concat bgb_4_1216 bgb_4_1248)) (concat (concat bgb_4_1280 bgb_4_1312) (concat bgb_4_1344 bgb_4_1376)))) (concat (concat (concat bgb_4_1408 (concat bgb_4_1440 bgb_4_1472)) (concat (concat bgb_4_1504 bgb_4_1536) (concat bgb_4_1568 bgb_4_1600))) (concat (concat (concat bgb_4_1632 bgb_4_1664) (concat bgb_4_1696 bgb_4_1728)) (concat (concat bgb_4_1760 bgb_4_1792) (concat bgb_4_1824 bgb_4_1856)))))) (concat (concat (concat (concat (concat bgb_4_1888 (concat bgb_4_1920 bgb_4_1952)) (concat (concat bgb_4_1984 bgb_4_2016) (concat bgb_4_2048 bgb_4_2080))) (concat (concat bgb_4_2112 (concat bgb_4_2144 bgb_4_2176)) (concat (concat bgb_4_2208 bgb_4_2240) (concat bgb_4_2272 bgb_4_2304)))) (concat (concat (concat bgb_4_2336 (concat bgb_4_2368 bgb_4_2400)) (concat (concat bgb_4_2432 bgb_4_2464) (concat bgb_4_2496 bgb_4_2528))) (concat (concat (concat bgb_4_2560 bgb_4_2592) (concat bgb_4_2624 bgb_4_2656)) (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784))))) (concat (concat (concat (concat bgb_4_2816 (concat bgb_4_2848 bgb_4_2880)) (concat (concat bgb_4_2912 bgb_4_2944) (concat bgb_4_2976 bgb_4_3008))) (concat (concat (concat bgb_4_3040 bgb_4_3072) (concat bgb_4_3104 bgb_4_3136)) (concat (concat bgb_4_3168 bgb_4_3200) (concat bgb_4_3232 bgb_4_3264)))) (concat (concat (concat bgb_4_3296 (concat bgb_4_3328 bgb_4_3360)) (concat (concat bgb_4_3392 bgb_4_3424) (concat bgb_4_3456 bgb_4_3488))) (concat (concat (concat bgb_4_3520 bgb_4_3552) (concat bgb_4_3584 bgb_4_3616)) (concat (concat bgb_4_3648 bgb_4_3680) (concat bgb_4_3712 bgb_4_3744)))))))
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
theorem bgb_5_6272 : Interval gbAtlas 5 6272 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 6283 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)))))) (concat (concat (concat (concat (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824)) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))) (concat (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304))))) (concat (concat (concat (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400)) (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496))) (concat (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592)) (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688)))) (concat (concat (concat bgb_5_2720 (concat bgb_5_2752 bgb_5_2784)) (concat bgb_5_2816 (concat bgb_5_2848 bgb_5_2880))) (concat (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 bgb_5_3104))))))) (concat (concat (concat (concat (concat (concat bgb_5_3136 (concat bgb_5_3168 bgb_5_3200)) (concat bgb_5_3232 (concat bgb_5_3264 bgb_5_3296))) (concat (concat bgb_5_3328 (concat bgb_5_3360 bgb_5_3392)) (concat bgb_5_3424 (concat bgb_5_3456 bgb_5_3488)))) (concat (concat (concat bgb_5_3520 (concat bgb_5_3552 bgb_5_3584)) (concat bgb_5_3616 (concat bgb_5_3648 bgb_5_3680))) (concat (concat bgb_5_3712 (concat bgb_5_3744 bgb_5_3776)) (concat bgb_5_3808 (concat bgb_5_3840 bgb_5_3872))))) (concat (concat (concat (concat bgb_5_3904 (concat bgb_5_3936 bgb_5_3968)) (concat bgb_5_4000 (concat bgb_5_4032 bgb_5_4064))) (concat (concat bgb_5_4096 (concat bgb_5_4128 bgb_5_4160)) (concat bgb_5_4192 (concat bgb_5_4224 bgb_5_4256)))) (concat (concat (concat bgb_5_4288 (concat bgb_5_4320 bgb_5_4352)) (concat bgb_5_4384 (concat bgb_5_4416 bgb_5_4448))) (concat (concat bgb_5_4480 (concat bgb_5_4512 bgb_5_4544)) (concat (concat bgb_5_4576 bgb_5_4608) (concat bgb_5_4640 bgb_5_4672)))))) (concat (concat (concat (concat (concat bgb_5_4704 (concat bgb_5_4736 bgb_5_4768)) (concat bgb_5_4800 (concat bgb_5_4832 bgb_5_4864))) (concat (concat bgb_5_4896 (concat bgb_5_4928 bgb_5_4960)) (concat bgb_5_4992 (concat bgb_5_5024 bgb_5_5056)))) (concat (concat (concat bgb_5_5088 (concat bgb_5_5120 bgb_5_5152)) (concat bgb_5_5184 (concat bgb_5_5216 bgb_5_5248))) (concat (concat bgb_5_5280 (concat bgb_5_5312 bgb_5_5344)) (concat (concat bgb_5_5376 bgb_5_5408) (concat bgb_5_5440 bgb_5_5472))))) (concat (concat (concat (concat bgb_5_5504 (concat bgb_5_5536 bgb_5_5568)) (concat bgb_5_5600 (concat bgb_5_5632 bgb_5_5664))) (concat (concat bgb_5_5696 (concat bgb_5_5728 bgb_5_5760)) (concat bgb_5_5792 (concat bgb_5_5824 bgb_5_5856)))) (concat (concat (concat bgb_5_5888 (concat bgb_5_5920 bgb_5_5952)) (concat bgb_5_5984 (concat bgb_5_6016 bgb_5_6048))) (concat (concat bgb_5_6080 (concat bgb_5_6112 bgb_5_6144)) (concat (concat bgb_5_6176 bgb_5_6208) (concat bgb_5_6240 bgb_5_6272))))))))
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
theorem bgb_6_1120 : Interval gbAtlas 6 1120 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1134 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 29 := bgb_7_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 5 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfeeceaa8eaa8eaa8feeceaa8eaa8eaa8feeceaa8eaa8eaa8feeceaa8eaa8eaa8feeceaa8eaa8eaa8feeceaa8eaa8eaa8feeceaa8eaa8eaa8feeceaa8eaa8eaa8
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,18,50)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,18,50)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808392 * 2 ^ 32 + 4004162184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12891.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.or,[3,4]⟩,⟨.or,[6,7]⟩,⟨.and,[2,5]⟩,⟨.or,[1,6]⟩,⟨.and,[1,6]⟩,⟨.and,[0,8]⟩,⟨.or,[10,12]⟩,⟨.or,[0,11]⟩,⟨.or,[9,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4004162184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4004162184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12891

open PEqualNP.Outside.L_meta_12891 in
theorem PEqualNP.Outside.L_meta_12891 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4004162184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4004162184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
