import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12927.Model
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


end PEqualNP.Outside.L_meta_12927.Model

namespace PEqualNP.Outside.L_meta_12927
open PEqualNP.Outside.L_meta_12927.Model
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

end PEqualNP.Outside.L_meta_12927

namespace PEqualNP.Outside.L_meta_12927
open PEqualNP.Outside.L_meta_12927.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841fc21082fca0107fd0020ff20041fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887f90710fb20e21fd41c43ea83887f10710ff98e21fe31c43ec63887f4c710fa98e21fc31c43fe43887f88710fb10e21fd21c43ea43887f08710ffa0621fe40c43fa81887f10310ff98621fe30c43fa61887f0c310ff90621fe20c43fa41887f08310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff99421fe32843fa65087f0ca10bea8c21ff41843fc83087f50610fe20c21ff31843fc63087f4c610fe18c21ff21843fc43087f48610fe10c217e50843fe81087f90210fd20421fd40843f281087f10210ff98421fe30843fa61087f0c210ff90421fe20843fa41087f08210ff88421f710843f621087fd5110bfaa221fe54442fca8887f55110beaa221fc54442f8a8887fd4d10bfa9a21fe53442fca6887f54d10bea9a21fc53442f8a6887fd0d10ff21a21fd43443f886887fd4910bfa9221fe52442fca4887f54910bea9221fc52442f8a4887fd0910ff21221fd42443f884887fcc910ff19221fd32443f864887fd0510ff20a21f641443fa82887d50510fe20a21ff31443fc62887d8c510fe98a21f531443f862887fc8510ff10a21f621443fa42887d48510fe10a21ff40443fc80887e90110fea0221f940443f880887fcc110ff18221fd30443f860887fc8110ff10221fd20443f840887fc4110fd88221fe10443ec20887fd5010bfaa021fe54042fca8086f950109f2a021fd54042faa8086f550109eaa021fc54042f8a8087fd4c10bfa9821fe53042fca6087794c10af29821fd53042faa6087754c10aea9821fc53042f8a6087fd0c10ff21821fd43043f886087fd4810bfa9021fe52042fca4087b94810b729021fd52042faa4087b54810b6a9021fc52042f8a4087fd0810ff21021fd42043f884087fcc810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xc430c3fea4187f94830bf29061ee520c2dca4187f54830bea9061ed520c2daa4187f14830ffa1061fe420c3fa84187f10830ff99061fe320c3bc64187f4c830fe19061dc320c3fea2187f94430bf28861f6510c2eca2187f54430bea8861f5510c2eaa2187f14430ffa0861fe410c3fa82187f10430ff98861fe310c3fa62187f0c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7905f14f20ffa1e41fe43c83fa87907f10f20ffa1641fe42c83dc85907f50b20f6a1641fc42c83fe65907f8cb20f719641fd32c83da65907f0cb20ffa8e41fe51c82fca3907f54720bea8e41fc51c83fe83907f90720fea0e41fc41c83fe63907f8c720fe98e41fc31c83fe43907bc8720ff10e41fd21c83da43907f08720ffa0641fe40c83fa81907f10320ff98641fe30c83fa61907f0c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ffa1c41fe43883fa87107f10e20bea9441ff42883fc85107f50a20fe21441ff32883de65107f8ca20fe99441fc32883d865107fd4620ff28c417e51883faa3105f54620fe28c41ff41883fc83107f50620fe20c41ff31883fc63107f4c620fe18c41ff21883fc43107f48620fe10c417e50883fe81107f90220fea0441fc40883fe61107f8c220fe98441fc30883fe41107bc8220fd90441ff54482fea8907f95120bf2a241fd54482faa8907f15120be2a241ff53482fea69077d4d20afa9a41fe53482fca6907f54d20bea9a41fc53482f8a6907714d20ae29a41ff43483fc86907f50d20fe21a41ff42483fc84907b90920fea1241ed42483f884907fcc920ff19241ee32483fa64907b4c920fe19241ff51482fea2907f94520fea8a41fc51482f8a2907fd0520ff20a41fd41483f882907fcc520ff18a41fd31483f862907fc8520f790a41fe21483fa42907b48520fe10a41ff40483fc80907f50120fe20241ff30483fc60907f4c120fe18241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041be540827ca8107f55020beaa041bd540827aa8107f15020be2a041ff53082fea6107f94c20bf29841de53082bca6107f54c20bea9841dd53082baa6107f14c20be29841ff43083fc86107f50c20fe218417e52083fe84107f90820fea1041fc42083fe64107bcc820ff19041fd32083f864107b0c820ffa8841fe51082fca2107d94420bb28841fd51082faa2107d54420baa8841fc51083fe82107f90420fea0841fc41083fe62107f8c420fe98841fc31083fe42107f88420fe90
  | 2 => 0x3f681207fd4d40bfa9a81fe53503faa6a07f14d40be29a81ff435037e86a07f90d40fea1a81bd43503f886a07fd4940bfa9281fe52503faa4a07f14940be29281ff425037e84a07f90940fea1281bd42503f884a07fcc940ff19281fd32503f864a07fd4540bfa8a81fe51503faa2a07f14540be28a81ff415037e82a07f90540fea0a81bd41503f882a07fcc540ff18a81fd31503f862a07fc8540ff10a81fd21503f842a07fd0140fda0281fe405037c80a05f95040ffa9881fe53102fca6207794c40af29881fd53102faa6207754c40aea9881fc53103fe86207f90c40fea1881fc43103fea4207f94840bf29081ee52102dca4207f54840bea9081ed52102daa4207f14840ffa1081fe42103fa84207f10840ff99081fe32103fa64207f0c840ffa8881fe51102fca2207d94440bb28881fd51102faa2207d54440baa8881fc51103fe82207f90440fea0881fc41103fe62207f8c440fe98881fc31103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9985fd5330ff2a6617e54cc3faa9985f55330fe2a6617c54cc3fe87987f90f30ef21e61fd43cc3ba87987f10f30ffa9661fe52cc2fca5987f54b30bea9661fc52cc3fe85987f90b30fea1661fc42cc3fe659877ccb30ff19661fd32cc3ba65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fea0e61fc41cc3fe639877cc730ff18e61fd31cc3ba63987f0c730ff90e61fe21cc3fa43987f08730ffa0661fe40cc3fa81987f10330ffaa4617f548c3fca9185f95230feaa4617d548c3f8a9185f15230bea9c61ff438c3fc87187f50e30fe21c61ff528c3fca5185f94a30fea94617d528c3f8a5187fd0a30ff21461fd428c3f885187fcca30ff19461de328c3fa65187f0ca30ee19461ff518c3fca3185f94630fea8c617d518c3f8a3187fd0630ff20c61fd418c3f883187fcc630ff18c61fd318c3f863187fc8630ff10c61fd218c3f843185f94230ffa0461fe408c3fa81187f10230ff98461df308c3f661187fd5130bfaa261fe544c2fca8987f55130beaa261fc544c2f8a8987fd0d30ff21a61de434c3fa86987750d30fe21a61ff524c2fea4987bd4930b7a9261fe524c3faa4987f14930be29261ec524c2d8a4987fd0930ff21261fd424c3f884987fcc930ef99261fe324c3fa6498774c930fe19261ff514c2fea2987f94530fea8a61fc514c2f8a2987fd0530ff20a61fd414c3f882987fcc530ef98a61fe314c3fa6298774c530fe18a61ff214c3fc42987f48530fe10a61ff404c3fc80987f50130fe20261ff304c3f660987f8c130ef18261ff540c2fea8187f95030bf2a061be540c27ca8187f55030beaa061bd540c27aa8187f15030be2a0617e530c3fe86187f90c30fea1861f
  | 3 => 0x6218ff8c431fb18863fd310c7ba6218fd4c431ffa8063fe500c6fca018ff54031bea8063fc500c7fea990dfd5321ff2a6437e54c87faa990df55321fe2a6437c54c87fea790dfd4f21ff29e437e53c87faa790df54f21fe29e437c53c87fe8790ff90f21fea1e43fc43c87fe8590ff90b21f721643fd42c87da8590ff10b21ff99643ef32c87fc6590ff4cb21fe19643ec32c87fe8390ff90721fea0e43fc41c87fe6390ff8c721fe98e43fc31c87fea190ff94321bf28643fd50c86faa190ff14321ffaa4437f54887fca910df95221feaa4437d54887f8a910df15221ffa9c437f53887fca710df94e21ef29c435e53887faa710df54e21eea9c435d53887f8a710df14e21ffa1c43fe43887fa8710ff10e21bea9443ff42887fc8510ff50a21fe21443ff32887fc6510ff4ca21fe194437e51887fe8310ff90621fea0c43fc41887fe6310ff8c621fe98c43fc31887fe4310fbc8621fb90c43ff50887fca110df94221fea84437d50887f8a110ffd5121bfaa243fe54486fca890ff55121beaa243fc54486f8a890ffd4d21bfa9a43fe53486fca690ff54d21bea9a43fc53486f8a690ffd0d21ff21a43fd43487f88690ffd0921ff21243ee42487fa8490fb50921fe21243ff32487de6490ff8c921fe99243fc32487d86490ffd0521ff20a43fd41487f88290ffcc521ff18a43fd31487f86290ffc8521fb90a43fe21487dc4290ffd4121bfa8243fe50487faa090ff14121be28243ff54086fea810ff95021bf2a043fd54086faa810ff15021be2a043ff53086fea610ff94c21bf29843fd53086faa610ff14c21be29843ff43087fc8610ff50c21fe218437e52087fe8410ff90821fea1043fc42087fe6410ff8c821fe99043fc32086fca210ffd0421ff20843fd41087f88210ffcc421ff18843fd31087f86210ffc8421f790843fe21087ec4210ff48421f690843f521087fea010ff94021bf28043fd50086faa010ff14021ffa9e81fe53d02fca7a07f54f40bea9e81fc53d03fe87a06fd0f40ff21e81fd43d037a87a07f10f40ffa9681fe52d02fca5a07f54b40bea9681fc52d03fe85a06fd0b40ff21681fd42d037a85a07f10b40ff99681fe32d03fa65a07f0cb40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a06fd0740ff20e81fd41d037a83a07f10740ff98e81fe31d03fa63a07f0c740ff90e81fe21d03fa43a07f08740beaa481ff53903fca7205f94e40fea9c817d53903f8a7207fd0e40ff21c81fd43903f887207fd4a40ff294817e52903faa5205f54a40fe29481ff42903fc85207f50a40fe21481ff32903fc65207f4ca40fe19481ff51903fca3205f94640fea8c817d51903f8a3207fd0640ff20c81fd41903f883207fcc640ff18c81fd31903f863207fc8640ff10c81fd21903f843205f94240ffa0481bf409
  | 4 => 0xffd4b41ff296837e52d07faa5a0df54b41fe29683ff42d07fc85a0ff50b41fe21683ff32d07fc65a0ff4cb41fe19683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9c83fe53906fca720ff54e41bea9c83fc53907fe8720ff90e41fea1c83fc43907fea520ff94a41bf29483fd52906faa520ff14a41ffa1483fe42907fa8520ff10a41ff99483fe32907fa6520ff0ca41bf28c83ff419077e8320fdd0641ffa8483fe50906fca120ff54241bea8483fc50907fea6a0dfd4d41ff29a83fd53507f8a6a0df14d41ffa1a83fe43507fa86a0ff10d41ffa92837f52507fca4a0ff54941fe292837c52507fe84a0ff90941fea1283fc42507fe64a0ff8c941fe99283fc32507fe82a0fdd0541ff20a83be41507fea0a0dfd4141ff28283fd50507f8a0a0df14141bf2a083ff53107fca620df94c41ef298835e53107faa620df54c41eea98835d53107f8a620ffd0c41ff21883fd43107f88620ffd4841ff290837e52107dca420db94841fea90837d52107daa420db54841fe29083ff42107fc8420ff50841fe21083ff32107fc6420ff4c841fe190837e51107fe8220efd0441ff20883f641107fa8220ef50441faa0883b541107fea020ff94041bf28083fa50106f4a020ff54041bea8083f950106f2a020ff14041ffaa6637f54cc7fca998df95331feaa6637d54cc7f8a998df15331ffa1e63fe43cc7bc8798ff50f31eea1e63fc43cc7fea598ff94b31bf29663fd52cc6faa598ff14b31ffa1663fe42cc7fa8598ff10b31ff99663fe32cc7bc6598ff4cb31fe19663dc32cc7fe8398ff90731fea0e63fc41cc7fea198ff94331bf28663fd50cc6faa198ff14331ffaa4637f548c7fca918df95231feaa4637d548c7f8a918df15231bea9c63ff438c7fc8718ff50e31fe21c63ff528c7fca518df94a31f7294636e528c7faa518df54a31f6a94636d528c7f8a518ffd0a31ff21463fd428c7f88518ffcca31ff19463fd328c7f86518df94631ffa0c63fe418c7fa8318ff10631ff98c63df318c7ee6318ffd4231ff284637e508c7faa118df54231fe28463ff544c6fea898ff95131bf2a263fd544c6faa898ff15131be2a263ff434c7fc8698f790d31fea1a63dd434c7f88698ffd4931bfa9263fe524c7faa498ff14931be29263ff424c7fc8498ff50931fe21263ff324c7fc6498f78c931fe99263fc324c7b86498ffd0531ff20a63fd414c7f88298ffcc531fb98a63fe314c7bc6298ffd4131bfa8263fe504c7faa098ff14131be28263ff540c6fea818ff95031bf2a063fd540c6faa818ff15031be2a0637e530c7fe8618ff90c31fea1863fc430c7fea418ff94831bf29063fd520c6faa418ff14831ffa1063fe420c7fa8418ff10831ff99063fe320c7fa6418ff0c831bf28863ff410c7fc8218ff50431fe20863ff310c7be
  | 5 => 0x943bfa9287fe5250ffaa4a1ff14943be29287ff5150efea2a1ff94543fea8a87fc5150ef8a2a1ffd4143bfa8287fe5050ffaa0a1ff14143be282877e5410efca621ffd0c43dfa1887fe4310fbc8621ff50c43dea1887dd4310ffea421ff94843bf29087fd5210efaa421ff14843ffa8887fe5110efca221ff54443bea8887fc5110ffea021ff94043bf28087fd5010efaa021ff14043ffa9e85fe53d0afca7a17794f42af29e85fd53d0afaa7a17754f42aea9e85fc53d0bfe87a17f90f42fea1e85fc43d0bfea3a17f94742bf28e85fd51d0afaa3a17f14742ffa8685fe50d0afca1a17f54342bea8685fc50d0afaa9217fd4e42ff29c857e5390bfaa7215f54e42fe29c85ff4390bfc87217f50e42fe21c857e5290bfe85216fd0a42f7a1485ff5190bfca3215f94642fea8c857d5190bf8a3217fd4242ff284857e5090bfaa1215f54242fe28485ff5350afea6a17f94d42fea9a85fc5350af8a6a17fd0d42ff21a85fd4350bf886a17fd0942f7a1285fe4250b7c84a17fd4542bfa8a85fe5150bfaa2a17f14542be28a85ff5050afea0a17f94142fea8285fc5050af8a0a15f95042ffa9885fe5310afca6217f54c42bea9885fc5310bfe86217f90c42fea1885fc4310afca4217fd0842dfa1085fe4210bdc84217f50842dea1085ed4210bfea2217f94442bf28885fd5110afaa2217f14442ffa8085fe5010afca0217f54042bea8085fc5010bfea9995fd5332ff2a6657e54ccbfaa9995f55332fe2a6657c54ccbfe87997f90f32fea1e65fc43ccbfe85997f90b32f721665fd42ccbda85997f10b32ffa8e65fe51ccafca3997f54732bea8e65fc51ccbfea1997f94332bf28665fd50ccafaa1997f14332ffaa4657f548cbfca9195f95232feaa4657d548cbf8a9195f15232bea9c65ff438cbfc87197790e32fea1c65dd438cbf887195f94a32ffa1465fe428cbfa85197f10a32ff99465df328cbde65197fd4632ff28c657e518cbfaa3195f54632fe28c65ff508cbfca1195f94232fea84657d508cbf8a1197fd5132bfaa265fe544cafca8997f55132beaa265fc544caf8a8997fd0d32ff21a65fd434cbf886997fd0932ff21265fd424cbf884997fcc932f799265fe324cbbc64997fd4532bfa8a65fe514cbfaa2997f14532be28a65ff504cafea0997f94132fea8265fc504caf8a0997fd5032bfaa065fe540cafca8197f55032beaa065fc540caf8a8195f94c32ffa1865fe430cbbc86197f50c32eea1865fc430cafca4197fd0832ff21065ee420cbfa84197b50832fe21065ff320cbbe64197f8c832f719065fd320cbba64197b4c832e699065ff510cbfca2195f94432fea88657d510cbf8a2197fd4032ff280657e500cbfaa0195f54032fe28065ff53d07fca7a0df94f41fea9e837d53d07f8a7a0ffd0f41ff21e83fd43d07f887a0
  | 6 => 0x401400803c06000402c00801801c00c05004000804802c00000001400000401001400001000c00001402000000001404001002401004409402c00004800802006800800800403c0180080f400800000001001400000c03400003406403c00000000002000400400005000400000400000800801400000404c02400401402001c00000c01400000801402401c00000000400402001801c03011c00800000000001800000001c01400001c00802c00001400000000400800000402801001002001c08c00000000000000000000000000000002400000006800000400801800402400400401802000000000800000800c0740040340a001000002801000404400c00c01c01800008800400002000000400000001400c00001400400800001003000002c00401c01000400000001007000806000400407c02c00800c02002401c01000801c00001804400800000000801000c03800400001000400000801803400006404403400001000c0000a400000806000001c00000805c00403003400002400c07000400000000000001800000005000006000401803400000c00c00000002804400800405000003400000800401000000002001403c01003401407c01000000c01c00000c00001800003c00c04400401400c00001000400002000000400000800000400800c00400000400004006400001800007801800001400400400400000000402400000000801000c01400400800c02400401c02400c04402400802800402402000001400404002800000804802004800402c00404405400800000807001001000401000800001000800408800000c00c00401002801803402400c00c00c00c00400002c00001400000001400c03401802400000801000000c00800002c02001401000000400c00400802004c03c07801803000000402400400401000407400004800000c00000c00000800400800000401800800001400c02400002000000404c01000405c00c05800400000000000006000404c01c00c00800001404c00800400800c00404002801808c01400c01c00400801001802003400800000c02000400800801001000800002400800000c07c03400400c02800c00001001000400400c00400002c00000401000000002800400000000c02403000400002400000002c00401800402c01402400406000400000000000402bfea5a1ff94b43bf29687ee52d0edca5a1ff54b43bea9687ed52d0edaa5a1ff14b43ffa8e87fe51d0efca3a1ff54743bea8e87fc51d0ffea1a1ff94343bf28687fd50d0efaa1a1ff14343beaa4877e5390ffe8721efd0e43efa1c87ff5290ffca521df94a43fea94877d5290ff8a521ffd4643ff28c877e5190ffaa321df54643fe28c87ff5090ffca121df94243fea84877d5090ff8a121ffd0d43efa1a87fe4350f7c86a1ffd4
  | 7 => 0x8500003f061a61aa40fb042a3328922230310f8338488e12230002f700019b0fc2bb8000509a90000002508000869ad0158e180000000019f17c04432413900000000033cb0d8bfa6100000000a8000000000002c18000503308000000240000002bd9573a398cb5912680018a22793b80011724aaaab8487e26986a1aa327a9e39603b800340af200027491a37f8f52a9160b2d8001be27433105e0420000f831295db7d82580000000022e84f0cc9a08002f2853a542a80b51813808000002c2b35a2f347ab30000daa031b3b6609e3468000c6ad88001ae3792ab93c0a10078ab9beb8194d2dca108b6afe00016ca85ba4ac40028002f406b8001b4264b6d8dd8003760952ad80080000011ab9580013601781c8003099008000002652cb164aa304597eabaab082020c27823b987b5730805829a34d10aa3d8001d602980000006405680000039e8001770e50b38000000002a70001750001860000d295280fa1b90c0000000821fd0448de1d1ae6b51065a96b34939b9110e81b0001110ee2099c58000cd9fb12d000205988a8d21c0000000000fd00026d8001080001370d300000025b8e880011780000000005d2072668f00b235000031ea1d37f1b00000000000ce11037e0002f9a2b00000010926e97f94b9e7b8900c19080023880000001307280019e0001ef80002f8002151420001d02fa0cb081ac69ba21eb1b8002130db20218e813a82950a52a2035f0002cf14d944a9b0fa9e822c0000000ba93325191f9dc0f13130000000003020d6a9aad49a78003748002392e000000016800012f80018d8002122ca84a0000000000b000000011593d8000000000a29bdaf19d736ca0c92c04cab394900527229c21a0d71b72c0aed356040a26ba0b23193b5e1590250e3122b4b99200008b1a50779b2000000075a7d8ecba2aec14996b11c22b9b2ad9928b698333269ac035185819b972900d4a941bf0000003918001a72a62b91a69b4a6406319a22a026a0a80012904b0000000000002818dd0c11cb8000001c100000037a8b31db2f6a30a258ad0281ec3480c60d51f41e706d0df9430bb0c1a760ea19d3343450f6a42b7a0c4a9b89012510d853310b7207d27fb93b49382236a73a49866822a8503a9a3af59728eab052f815f1bb0f638c31a258b1f26b8000000000000000000000062400000c515f8003610001599d9b900000001d200001e35cb5380023e29cafb9d80001ae8939c710725d1349f8a7a0000a000580022d0000002f0a69000000000000000358a3400017ca8a9e60000d8800107b3032b8102081aba05000000312000400800001c0080040bc00c01006800001400c00002405c00c00c02c07004803c00400000800801801402000000000c00c0100000040000200180240000040200100b000001800406403801400
  | 8 => 0x400035fa298001768002fc2a680024b0d18001fe1108c79f1000000062ae780000009cad19fe80034c16d32e2882b58000000000000000f58000ed0002730a8000000295800000318a2400022e0d20000f90143518e7ab726000032f1e00001438e68a180000025d96580000019280007216e2d20d7b5e9201eb083851a60a0f02e9c021619da972e2b6c0000003140089530990002c600000000000026fa1680000031a8a5a569a48559b8a92a8da808001ebac59ef396ae315000036f8000d0b83248b9a8001742372be9ceb548000000a6170103800277a6c0ff80014a24f92e8b4a322093983a43802f130180011407cb0f0af373a7d32489dafeb010a083a0d131c14c0000e596e9f2085ac019893a904800000194843129b3b8f99000562ae9b5b5d1951748b5a4214e0000000000920ee80038580e80039908980032cb4a2838091dd9c486635414536187fa52034ad811881a18d33188100f3172451fa24d020b43877270b393038cf80000397082733eb200eb03d000326102a07a638f0a5106c8000ba1fb8000000002f8b6f1f724e35330e849aa0b9fadb3579208803a50001d380026d0002b8acc8000d033a05203d901aaa0dc20e0232412ee0001bc8002c3363b9da9104d1413049720000000b1b71287068a7f000028b8c8f1800158800224a1ab8135a80038b14193b0000000001231ac91e80027b1839910000fc80000006f80023500001691f02c33f89325f087956b8faa4906888b3784aad391925c89f1a31c9a5fabc0c725380037285b1899cb3a680000035b9b189280b9d88e22a5003333ad117a9bf864b8737c8d58003629f51ea28332b0013988122f3abc8001870f30e38001c6ae22c8191874b29b601da060912a000afb759aa8e29a18dca13b2a2c7ace2a10e60a52398000d6000206000000032342800185091345a5834e9b305793d2e705e9c20002de0feb9c98bb68aca3609d2ac90ff291aa8b370001760c59149818001b901528780013522fa7e27538e2ea2289138e407080005f0002d600000d82d2181df0189f81483119fcb0084018222aa039e0b56ba59f011b8002758b2a1f00e3a115387004bba32af2302042d78000998aca8214b02c9640001278a780025a80025989824400016a0002b200004f9f29f38000000002688002e89e68eba3f00000000000012a1e90000000f787f091a4c03c8698a912e2d0030214b7021c97b0670df06f1a5b380ab24c8000001968b10002100e91f982ba8c9400001408022e108c8fa00037b342119a1da2901e8ef24088db743000a3807323b38a6813e0000001978000478f289f91da4d80000000023e9c630e11e2208000001d580000000000000000039533980000a16a80000003580012388a80030b1e58b89f9078245b3b2791bd02199e94ea4f22c9551930760
  | 9 => 0x18805ca560730000000000002cb8000000b9b169022788962b132a81f9ca17f0002328c309c000000000306830a069d3000000000215b6b0000000000000000002c9a62132800189379a0180000010580000000032d0ce800000000000000000000000158000001b9b8002a9b8680000028499800000013a000307800000000000124b6300000031caa580010e0c21c3860000184a448cf08921f9181f794c8001c50172bd0002281620000cc3a216100000025e80012bb7321984108b80033e28c25a18b24799407b19a9cc00036aa18b4480000024820f8389cc878ad0839a7000032210432e9600739dfa5b39c18331787c03616c1e99bab160dbb4a9a88311211ee800098ae18c98be80023a06e0000000000001388000000000a498682a9a60aeb2f81080005f8000002c70001a98caa4300035080016280000020a19b982b9080028b8002dd95c9618000aa18f80019c86929fb3f2981afa228a73640248540000002961672219dd0000000870001a12049428882b40000000002b49731679b78001b1288a532b68190001c08000bc00009d0001e18000552a02841478000001e20000b70000000000001c8b212ec89aab79458002f78002eb000168a8f0002dea5e2b19c31e42f000009b36b8ae38f1ad8769638278000003a19cfa1e03400000412580002a1f0adaa4b80007eb1b000241b8d00028f8002b50f71ee00003c0002e40001f58f405a1b9b36b88b1d36926a2cc2f93432b03a016320d0611c91540f3a57979a86359b4105483fac497a05a86381f39e13faf4b0596d97b89e9738e700690d29d26281db461eab5204e298a99355b191ff00027bb6686dac22dc0000fe34f09408e98c0799de30615a00000019f8000471ff8b8133a468000002438003198c380000036a2a39f48970222d324700003700030707a37d20b00d0000e4abf80030a8000002bb03798f0000000b7955a270001dab9a33db6532510b02f217310169016302896a773092590001380000002d5a3192180000000012aac11de90500000000000000000020bb14a1788c1a82f321100000036e88d0c880030bb138000000978001169160b629e81bb7185700000039b28686b04d8a42e981114f17d30faac8c90292261ce05da9d975b27349b9d07193f2fa83e82608a1d937b98092429f02e304255a978ca299ab2966a6e34d8002009958000efa029fc0da2a787435811d389969b8b87a800265b8a2b8190267385031931af50001962fc951ba60000381b626f0bf000000000199a3fa1187bb330000cba3c0bd0aa8948001ca884b64a920180392e533501d2ad28e8b09d400000000005900010caf617d859946ae60e08cd2a2a14111b401b6b0880013039307515d2ce80021b38797896b9d48418329f331f97915baed9971f608f2df1e49262d69098529a
  | 10 => 0x2bf38826ab67a7aa949e128b30c37685bb65a3486eb5a352800000000012affaa1a3a96f00004c2c880000009a000290804b97b670c81af2b9b4194a8be000108a6c8000a98f20001842d7276a5712db9202b263000000137b5c0003288000000fdacd2e827c915000223a12b83b229e29d69f1846acf9120fb90a0000000001fa8000002711e8800329014b940002ff08e0000a895c1991560f48712e0aafaac39f02da6b28e13400016614890b80cadfb20b623778a305c00b01a84800018e0d98ad91300016f8002ea9800a233d00000022500038ab1d97e3788000000000000001280000001d50000c024601c2dd10620eb110000d90620000ac0790000000368c080020100000000012b0000000000001edb680491548000001220000000000001510003751d0a3b2930000000000001442da011a3d14fb2194600000995e0000e980013e97130d0001b50001dcb6d13cafb0002fd95e97813138627c1c40000862500001c1b470000b420880025534404380012f21911cb3c2db95207db7084ea4a11b231000000000289b5da8a348a4908fb182d283b0000b93928000000002548000001308000e000030c9a2aeeb8db7e8679d79b09321ec9472e3b32a799cf3360002e90841ed2728bb9bba338a6b4b1cd0000002fd2380ec0510000000001718deb4e2d91cd800266000165000000157a359bc1c7ad5135b4c92710f0d83948d39a02c50958c42c38ed8239a219c2ab1ab1db8002eb800293ab60000000002ef32815a9f6abe0002a20461d12802950003158002ba000058a678bc800090800382b5500000000000037c06c20db5b0e80829779c2b258000bd80031e27ea2db8e8f880036e00039980012ca360000000d400000000010125c2e4a71aef8450003321fd9b80002810001c81e5080b2c38415b136aae34fa37b7824e9031e32cd8080830c2ae586530a03e00006a80033aad40682210001e389b98ab1523cb77021
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x3400435e53d0010d754f400436e52d0010db54b400427f65900109f596400433e5490010cf552400435e5390010d754e400436e5290010db54a40042f66190010bd586400437a50900109fd95400433e5450010cf551400435e5350010d754d400436e5250010db549400437a50500109fd94400427e65100109f594400427c6510010cf950400433d5410010b798c40042dd6310010d794c400435d5310010bb98840042ed6210010db948400436d5210010bd98440042f561100109f597300433e54cc010cf553300435e53cc010d754f300436e52cc010db54b300427f658c0109f596300433e548c010cf552300435e538c010d754e300436e528c010db54a30042f6618c010bd586300427f654c010cf951300433d544c010d794d300435d534c010bbd8930042ec624c010db949300436d524c0109fd94300427e650c0109f594300427c650c010af99030042bd640c010cf950300433d540c010d794c300435d530c010bb98830042ed620c010db948300436d520c010bd98430042f5610c0109f597200433e54c8010cf553200435e53c8010d754f200436e52c8010db54b200427f65880109f596200433e5488010cf552200435e5388010d754e200436e5288010db54a20042f66188010bd586200427f6548010cf951200433d5448010b7d8d20042dc6348010d794d200435d5348010db949200436d52480109fd94200427e65080109f594200427c6508010af99020042bd6408010cf950200433d5408010b798c20042dd6308010d794c200435d5308010db948200436d5208010bd98420042f56108010cf953100433d54c4010d794f100435d53c4010db94b100436d52c4010dd597100437754c4010ed953100437554c4010ed553100433554c4010ddd4f10043d653c4010dd54f10043d553c4010d554f100437752c4010f994b100437552c4010f954b100436552c4010cf952100433d5484010d794e100435d5384010db94a100436d5284010bd58610043765184010be596100437965840109e596100437b5484010ee95210043795484010ee55210043395484010f694e10043d95384010fa94a10043e95284010be586100437a5184010fc946100427f6544010cf951100433d5444010d794d100435d5344010db949100436d5244010bdd95100437765440109dd9510043775444010ed95110043755444010ed55110043355444010ddd4d10043d65344010dd54d10043d55344010d554d10043775244010f994910043755244010f954910043655244010bdd8110043765044010fc90110043f14044010bed95100437b65440109ed95100437b5444010ee95110043795444010ee55110043395444010f694d10043d95344010fa94910043e95244010bed8510043f36144010de94510043f25144010fc90510043f14144010
  | 1 => 0x427d65d08109f197420433e54d0810cf55342042de63d0810b758f420435e53d0810d754f420436e52d0810db54b420427f65908109f996420427d65908109f196420433e5490810cf552420435e5390810d754e420436e5290810db54a420427f65508109f995420427d65508109f195420433e5450810cf551420435e5350810d754d420436e5250810db54942042f76150810bd185420427f65108109f994420427d65108109f194420433e5410810cf550420435e5310810d754c420436e5210810db548420427f65cc8109f997320427d65cc8109f197320433e54cc810cf553320435e53cc810d754f320436e52cc810db54b320427f658c8109f996320427d658c8109f196320433e548c810cf552320435e538c810d754e320436e528c810db54a320427f654c8109f995320427d654c8109f195320433e544c810cf551320435e534c810d754d320436e524c810db549320427f650c8109f994320427d650c8109f194320433e540c810cf550320435e530c810d754c320436e520c810db54832043cd320c8109f992510427d64944109f98e510427d63944109f98a510427d62944109f597410433e54d0410cf553410435e53d0410d754f410436e52d0410db54b410427f65904109f596410433e5490410cf552410435e5390410d754e410436e5290410db54a41043765190410be98241042f960904109fd95410433e5450410cf551410435e5350410d754d410436e5250410db549410437651504109fd94410427d6510410cf950410433d5410410b798c41042dd6310410d794c410435d5310410bb98841042ed6210410db948410436d5210410ed50441042fa6010410be580410427d65cc410cf953310433d54cc410d794f310435d53cc410db94b310436d52cc4109fd96310427d658c410cf952310433d548c410d794e310435d538c410bb98a31042ed628c410db94a310436d528c410dd94631042fa608c410be582310427f654c410cf951310433d544c410d794d310435d534c410db949310436d524c410dd945310427f650c4109f594310433e540c410cf550310435e530c410d754c310436e520c410db54831042fa600c410be580310427d65c8410cf953210433d54c8410d794f210435d53c8410db94b210436d52c84109fd96210427d6588410cf952210433d5488410b798e21042dd6388410d794e210435d5388410db94a210436d5288410dd94621042fa6088410be582210427f6548410cf951210433d5448410d794d210435d5348410db949210436d5248410dd945210427f65084109f594210433e5408410cf550210435e5308410d754c210436e5208410db54821042fa6008410be580210427e64940109f592500427e63940109f58e500427e62940109f58a500427d61940109f597400433e54d0010cf55
  | 2 => 0x6254c10d7985530435c6154c10d7981530435c6054c10d704153042be6414c10af590530433e5414c10cf55053042de6314c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530425e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109d984530427e6014c10de980530427f65d0c109f997430427d65d0c109f197430433e54d0c10cf553430435e53d0c10d754f43042ee62d0c10bb58b430427f6590c109f996430427d6590c109f196430433e5490c10cf552430435e5390c10d754e430427f6550c109f995430427d6550c109f195430433e5450c10cf551430435e5350c10d754d43042f76150c10bd185430427f6510c109f994430427d6510c109f194430433e5410c10cf550430435e5310c10d754c43042be64d4810af593520433e54d4810cf55352042de63d4810b758f520435e53d4810d754f520427e64d4810cf993520423e64d48109f593520433d64d48108f593520427e63d4810d798f520425e63d48109f58f520435d63d48109758f520427e61d4810dd987520427e60d4810de983520427d6594810cf952520433d5494810d794e520435d5394810dbd4a520427e64948109f592520427e63948109f58e520426d6594810dbd52520436e5494810eb952520432e5494810db55252043ad5494810cb552520436c5494810dbd4e520436e5394810f394e520434e5394810db54e52043cd5394810d354e520436c5394810dbd92520436e6494810db592520436c6494810dbd8e520436e6394810db58e520436c6394810dbd0e520436e4394810db50e520436c4394810db986520436c6194810db982520436c6094810cf951520433d5454810d794d520435d53548109fd91520427c64548109fd8d520427c6354810dbd89520427f61548109f585520427f60548109f581520436f6554810dbd51520436e5454810eb951520432e5454810db55152043ad5454810cb551520436c5454810dbd4d520436e5354810f394d520434e5354810db54d52043cd5354810d354d520436c5354810dbd91520436e6454810db591520436c6454810dbd8d520436e6354810db58d520436c6354810dbd0d520436e4354810db50d520436c4354810db985520436c6154810db981520436c6054810db04152042be6414810af590520433e5414810cf55052042de6314810b758c520435e5314810d754c52042ee6214810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520426e62148109f984520437661148109d984520427e6014810de980520427f65d08109f997420
  | 3 => 0x1109f99430442be640c110af59030442ee620c110bb58830442f6610c110bd584304427e65c8110dbd4b204436c52c8110bd98720442f561c8110f9487204427e65881109fd95204427d65481109f19520442df6348110b718d204436f5248110db14920442f76148110bd18520443e521481109f99420442be6408110af59020442de6308110b758c20442f66108110bd58420442fb64c4110be59310443f241c4110fc50710443f231c4110fc4c710443f221c4110fc48710442f76484110bd59210442f76384110bd58e10442f76284110bd58a10443f35084110fc90210443f14084110b798f54042dd63d5010bb98b54042ed62d50109f98f540435e63d50109798f540427d63d5010d758f540425d63d50109f98b540436e62d50109b98b540427d62d5010db58b540426d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d62950108f596540433f6395010cf98e540433d6395010cf18e540433f6295010cf98a540433d6295010cf18a540433e6195010cf186540433e6095010cf182540433f64550109fd8d540427c63550109fd89540427c62550109fd85540427d61550109fd81540427d6055010cfd95540433f6355010cf98d540433d6355010cf18d540433f6255010cf989540433d6255010cf189540433e6155010cf185540433e6055010cf181540433c1055010af990540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150108f990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427661150109f980540437a60150109e98054042be64d4c10af593530433e54d4c10cf55353042ee62d4c10bb58b530427e64d4c10cf993530423e64d4c109f593530433d64d4c108f593530427e62d4c10db98b530426e62d4c109f58b530436d62d4c109b58b530427e61d4c10dd987530427e60d4c10de983530427d6594c10cf952530433d5494c10d7d4e530427e6494c109f592530427e6294c109f58a530425d6594c10d7d52530435e5494c10e7952530431e5494c10d7552530439d5494c10c7552530435c5494c10d7d92530435e6494c10d7592530435c6494c10d7d8a530435e6294c10d758a530435c6294c10d7986530435c6194c10d7982530435c6094c10cf951530433d5454c109fd91530427c6454c10d7d8d530427f6254c109f189530427f6154c109f585530427f6054c109f581530435f6554c10d7d51530435e5454c10e7951530431e5454c10d7551530439d5454c10c7551530435c5454c10d7d91530435e6454c10d7591530435c6454c10d7d89530435e6254c10d7589530435c
  | 4 => 0xd58432442fa600c910be580324427e65d0510cfd53414433c54d0510be98341442f960d05109f99641442f66590510dd99641442f56490510dd95241443745490510bd58e41442f56290510fcd8241442f66090510fc182414427c6550510cfd51414433c5450510bed8141442f86050510dd19541442746550510edd9141443b75450510dd95141443745450510ed15141443345450510bdd8d41442f76250510fcd8141442f46050510fc181414427e6510510b798c41442dd6310510bb98841442ed6210510bd98441443b54110510be980414427e65cc510d7d4f314435c53cc510be98331442f960cc5109f99631442ee628c510bb58a31442f6658c510dd99631442f7648c510bd59231442f5638c510dd94e3144374538c510f998a31442f5628c510f958a31442e5628c510bd982314427c654c510d7d4d314435c534c510bed8131442f8604c510dd1953144274654c510bdd9131442f5644c510f5d8d31443d7534c510dd94d3144374534c510f514d31443d6434c510f550d31442f7624c510f58c931443d4324c510fcd8131442f4604c510fc181314427e650c510bd98431443d5310c5109f997214436f52c8510db14b21442fa60c8510be583214427e6588510b798e21442dd6388510bd99621443766588510bdd9221442f56488510bdd8e21443d66388510bd58e21443d56388510b558e21442f56288510dd94a21443745288510bd982214427c6548510dbd49214436c5248510bed8121442f86048510dd19521442746548510bdd9121442f56448510bdd8d21442f56348510f9d8921443e75248510dd94921443745248510f914921443e64248510f950921443e73248510f90c921443f36048510bd18121443f060485109f99421442f66108510f9484214427e65d0110cfd53404433c54d0110bd98740442f561d0110ed507404427e6590110be996404437a6590110be592404437a5490110de15240443f36190110be98640443f06190110fc90640443f14190110fc8c640443f13190110fc88640443f121901109fd95404427d65501109f195404433f5450110cf15140442f76150110bd18540443b54150110be195404437865501109e19540443bb6450110eed51404437a5450110de15140443b85450110eed0d40443b94350110eed0940443b94250110fcd8540442f86150110fc18540443bb4150110fc90540443b94150110fc50540443b14150110fc8c540443f13150110fc88540443f121501109f99440442de6310110b758c40442ee6210110bb58840442f66110110bd58440442fa6010110ee500404427e65cc110d7d4f304435c53cc110bd98730442f561cc110f54c7304427e658c1109fd95304427d654c1109f195304435f534c110d714d30442ef624c110bb18930442f7614c110bd18530443d5314c
  | 5 => 0x544436e62151109b988544427d6215110db588544426d62151109f984544437561151109f184544427e6015110de580544427c60151109f993534427d64d4d109f98b534427d62d4d10d7d4e534427e6494d109f592534427e6394d109f98a534427d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10bbd8953442ec6254d109fd91534433f6454d108fd91534427c6454d10cf191534423c6454d10d7d8d534427f6254d10dbd89534426f6254d109f189534436c6254d109b189534427f6154d10ddd85534427f6054d10ded81534427e6514d10d754c534427e6414d109f590534435e6314d109f988534427d6214d109f98453443756114d109f184534427e6014d109f180534427f65d0d109f997434427d65d0d109f197434435f53d0d10d714f43442ee62d0d10bb58b43442f661d0d10bd58743442fa60d0d10be583434427f6590d109f996434427d6590d109f196434433f5490d10cf152434435e5390d10d754e43442f66190d10bd586434427f6550d109f995434427d6550d109f195434435e5350d10d754d434427f6510d109f994434427d6510d109f194434433f5410d10cf150434435f5310d10d714c43442f66110d10bd58443442fa6010d10be580434427e64d49109f593524427e63d49109f58f524436f52949109f992524427d64949109f98e524427d63949109f98a524427d6194910dd586524427d6094910de58252442bf6454910af19152442df6354910b718d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109fd81524437b60549109f994524436d52149109f990524427d64149109f98c524427d6314910db988524427e6114910dd584524427c61149109f980524427c60149109fd97424427e65d09109f597424427c65d0910b798f42442dd63d0910dbd4b424436c52d0910bd98742442f561d0910be98342442f960d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910db94a424436d5290910bd98642442f561909109fd95424427e65509109f595424427c6550910db949424436d52509109fd94424427e65109109f594424427c6510910cfd50424433c5410910dbd48424436c5210910bd98442442f56110910be98042442f960109109fd97324427e65cc9109f597324427c65cc910dbd4b324436c52cc910bd98732442f561cc9109fd96324427e658c9109f596324427c658c910d7d4e324435c538c910bd98632442f5618c9109fd95324427e654c9109f595324427c654c9109fd94324427e650c9109f594324427c650c910d7d4c324435c530c910dbd48324436c520c910f34c832442f6610c910b
  | 6 => 0x36e5250a10db54942842f76150a10bd185428427f6510a109f994428427d6510a109f19442842fa6010a10be580428427f65cca109f997328427d65cca109f197328435e53cca10d754f328436f52cca10db14b328427f658ca109f996328427d658ca109f196328435f538ca10d714e328436e528ca10db54a328427f654ca109f995328427d654ca109f195328435e534ca10d754d328436e524ca10db549328427f650ca109f994328427d650ca109f194328435f530ca10d714c328436f520ca10db14832843cd320ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610cf951418433d5450610bed8141842f86050610b798c41842dd6310610bb98841842ed6210610ed50441842f96010610d794f318435d53cc610be98331842f960cc610bb98a31842ed628c610d794d318435d534c610bed8131842f8604c610db94b218436d52c8610be98321842f960c8610b798e21842dd6388610db949218436d5248610bed8121842f86048610cfd53408433c54d0210cf952408433d5490210bd98640842f56190210be59640843796590210de95240843ba5490210ee55240843785490210be98640843f26190210fc586408433f5450210cf15140842fb6550210ded9540843bb6450210eed51408437a5450210de15140843b85450210eed0d40843b94350210eed0940843b94250210be18540843bb4150210ee505408433e5410210cf55040842de6310210b758c40842ee6210210bb58840842f66110210bd58440843b94010210d7d4f308435c53cc210d794e308435d538c210bd98630842f5618c210d7d4d308435c534c210bbd8930842ec624c210af99030842bd640c210d794c308435d530c210bb98830842ed620c210bd98430842f5610c210dbd4b208436c52c8210db94a208436d5288210bd98620842f56188210b7d8d20842dc6348210dbd49208436c5248210af99020842bd6408210b798c20842dd6308210db948208436d5208210bd98420842f56108210bd597108437565c4210ddd53108437554c4210ddd4f108437553c4210ddd4b108437552c4210be597108437965c4210bed9310842f964c42109f98f544427d63d51109f98b544427d62d5110cfd52544427e64951109f98e544427d63951109f98a544427d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f63551109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427f6055110ded81544427e6515110cf55054442de6315110b758c54442ee6215110bb588544433e64151109f98c544435e63151109798c544427d6315110d758c544425d63151109f988
  | 7 => 0x310310bb98840c42ed6210310bd98440c42f56110310d794f30c435d53cc310bd98730c42f561cc310f54c730c435e534c310d754d30c42ef624c310bb18930c42f7614c310bd18530c43d5314c310af99030c42bd640c310bb98830c42ed620c310bd98430c42f5610c310db94b20c436d52c8310bd98720c42f561c8310f948720c42df6348310b718d20c436e5248310db54920c42f76148310bd18520c43e52148310af99020c42bd6408310b798c20c42dd6308310bd98420c42f561083109f98f548427d63d52109f98b548427d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a548437a6095210cfd91548427f63552109f18d548427f62552109f189548433d5415210b798c54842dd6315210bb98854842ed6215210cf990548427e6315210d798c548425e63152109f58c548435d63152109758c548427e6215210db988548426e62152109f588548436d62152109b58854843756115210de980548427e64d4e109f593538427e62d4e109f58b538437561d4e10de983538435f5394e109f992538427d6494e109f98a538427d6294e10bbd8953842ec6254e109fd91538427c6454e10d7d8d538427f6254e10dbd89538426f6254e109f189538436c6254e109b18953842be6414e10af590538435d5314e10bb98853842ed6214e109f990538433e6414e108f990538427d6414e10cf590538423d6414e10d798c538427e6214e10db988538426e6214e109f588538436d6214e109b58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438433e54d0e10cf55343842ee62d0e10bb58b43842fa60d0e10be583438427f6590e109f996438427d6590e109f196438435e5390e10d754e438427f6550e109f995438427d6550e109f195438433e5450e10cf551438435e5350e10d754d43842f76150e10bd185438427f6510e109f994438427d6510e109f19443842fa6010e10be580438427e64d4a109f593528427e63d4a109f58f528437561d4a10de983528436f5294a109f992528427d6494a109f98e528427d6394a10b7d8d52842dc6354a109fd91528427c6454a109fd8d528435f6354a1097d8d528427c6354a10d718d528425c6354a10dbd8952842be6414a10af59052842de6314a10b758c528436d5214a109f990528433e6414a108f990528427d6414a10cf590528423d6414a109f98c528435e6314a109798c528427d6314a10d758c528425d6314a10db98852843756114a10de980528427f65d0a109f997428427d65d0a109f197428433e54d0a10cf55342842de63d0a10b758f42842fa60d0a10be583428427f6590a109f996428427d6590a109f196428436e5290a10db54a428427f6550a109f995428427d6550a109f195428433e5450a10cf5514284
  | 8 => 0x109f59252c427e6394b109f58e52c43766194b109fd9152c427c6454b109fd8d52c427c6354b10dbd8952c436d5214b109f99052c427d6414b109f98c52c427d6314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c42de63d0b10b758f42c42f661d0b10bd58742c427f6590b109f99642c427d6590b109f19642c436e5290b10db54a42c42f66190b10bd58642c427f6550b109f99542c427d6550b109f19542c436e5250b10db54942c427f6510b109f99442c427d6510b109f19442c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c436e52ccb10db54b32c42f661ccb10bd58732c427f658cb109f99632c427d658cb109f19632c435e538cb10d754e32c42f6618cb10bd58632c427f654cb109f99532c427d654cb109f19532c427f650cb109f99432c427d650cb109f19432c435e530cb10d754c32c436e520cb10db54832c43cd320cb10bd98432c42f5610cb10cfd5341c433c54d0710cf95241c433d5490710be98241c42f96090710dd59641c43765490710ed95241c43b55490710dd15241c42f56390710bd58a41c42f66090710fc98241c43f16090710cfd5141c433c5450710bdd9541c43776550710edd9141c43b75450710dd95141c43745450710ed15141c43345450710bdd8d41c42f76250710bd18141c433e5410710cf55041c42de6310710b758c41c42ee6210710bb58841c43b54110710be98041c42f96010710d7d4f31c435c53cc710d794e31c435d538c710bb98a31c42ed628c710be98231c42f9608c710dd59631c42f7648c710bd59231c4376538c710f594e31c43d5538c710dd14e31c43e6628c710bd58a31c43e5628c710b958a31c42f6608c710fc98231c43f1608c710d7d4d31c435c534c710bdd9531c4377654c710bdd9131c42f5644c710f5d8d31c43d7534c710dd94d31c4374534c710f514d31c43d6434c710f550d31c42f7624c710f58c931c43d4324c710bd18131c435e530c710d754c31c43d5310c710be98031c42f9600c710dbd4b21c436c52c8710b798e21c42dd6388710db94a21c436d5288710be98221c42f96088710dd59621c42f76488710bd59221c42f76388710f598e21c42f56388710f558e21c42d56388710dd94a21c43e65288710f954a21c43745288710bd98221c43f26088710fc58221c436f5248710db14921c42f76548710ddd9521c42f76448710bd59121c42f76348710bd58d21c43e76248710f9d4921c43765248710dd14921c43e45248710f990921c43e54248710f9cc921c43e43248710bd18121c436e5208710db54821c43e52108710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310ed50740c433e5450310cf55140c42f76150310bd18540c43b54150310b798c40c42dd6
  | 9 => 0xd94300827e650c0209f594300827c650c020af99030082bd640c020cf950300833d540c020d794c300835d530c020bb98830082ed620c020f30c830082f6610c020bd5843008376510c020dd544300833e54c8020cf553200835e53c8020d754f200837651c8020dd547200836f54c8020eb953200836d54c8020eb553200832d54c8020bb98f20082ec63c8020dbd4f20083ce53c8020db54f20083cd53c8020d354f20083e651c8020db54720083e551c8020d9547200833e5488020cf552200835e5388020d754e20082ed6288020db94a20083765188020dd54620083ba5488020ee55220083da5388020f654e20082f96288020de94a20083ea5288020facca20083e83288020fc94620083f151880209fd95200833e5448020cf55120082df6348020b718d200835e5348020d754d20083765148020dd54520082ef6548020dbd95200826f6548020dbd5120083ae5448020db55120083ad5448020cb55120083cf6348020bb98d20082ec6348020f318d20082cc6348020dbd4d20083ce5348020db54d20083cd5348020d354d20083e65148020db54520083e55148020d954520082ef6048020db94120082fb6548020ded95200827b6548020ee95120083b95448020f6d8d20083d86348020f694d20083d95348020bed8920083eb6248020de94920083ea5248020fc94520083f151480209f98f54c427d63d53109f98b54c427d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c43766195310cfd9154c427f63553109f18d54c427f62553109f18954c433d5415310b798c54c42dd6315310bb98854c42ed6215310cf99054c427e6315310d798c54c425e63153109f58c54c435d63153109758c54c427e6215310db98854c426e62153109f58854c436d62153109b58854c43766115310de58054c42ee62d4f10bb58b53c427e64d4f109f59353c427e62d4f10db98b53c426e62d4f109f58b53c436d62d4f109b58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f10dd98653c427f6454f109f19153c435f6354f109fd8953c427c6254f10d754c53c427e6414f109f59053c435e6314f109f98853c427d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10bb98b43c42ed62d0f10bd98743c42f561d0f109fd9643c427e6590f109f59643c427c6590f10d794e43c435d5390f10bd98643c42f56190f109fd9543c427e6550f109f59543c427c6550f10d794d43c435d5350f109fd9443c427e6510f109f59443c427c6510f10bd98443c42f56110f10b798f52c42dd63d4b109f99352c427d64d4b109f98f52c435e63d4b109798f52c427d63d4b10d758f52c425d63d4b10dd98752c437960d4b10dbd4a52c427e6494b
  | 10 => 0x1083754254420dd10951083773254420d9cc951083763254420dd4c951083743254420d90c951083766054420dd18151083742054420af99051082bd6414420cf950510833d5414420b798c51082dd6314420d794c510835d5314420bd984510837551144209fd97410827e65d04209f597410833e54d0420cf553410835e53d0420d754f410837651d0420dd547410827f65904209f996410827d6590420cf952410833d5490420d794e410835d5390420dd946410837551904209fd95410827d65504209f195410833e5450420cf551410835e5350420d754d41082ef6250420bb18941083765150420dd545410827f65104209f994410827d6510420cf950410833d5410420b798c41082dd6310420d794c410835d5310420bb98841082ed6210420dd94441083755110420ed50441082fa6010420be580410827f65cc4209f997310827d65cc420cf953310833d54cc420d794f310835d53cc420f30cb310837651cc420dd547310827f658c4209f996310827d658c420cf952310833d548c420d794e310835d538c420bb98a31082ed628c420dd9463108375518c4209fd95310827d654c4209f195310833e544c420cf551310835e534c420d754d31082ef624c420bb18931083cc324c420dd9453108375514c4209fd94310827e650c4209f594310833e540c420cf550310835e530c420d754c3108376510c420dd544310833e54c8420cf553210835e53c8420d754f210836e52c8420dd947210837551c8420be98321082f960c84209f596210833e5488420cf55221082de6388420b758e210835e5388420d754e210837551884209fd95210833e5448420cf551210835e5348420d754d210836e5248420dd945210833e5408420cf550210835e5308420d754c21083765108420dd54421082fa6008420be580210827e64940209f592500827e63940209f58e500836f3294020db0ca500827d65d0020cf953400833d54d0020d794f400835d53d0020dd947400837551d00209fd96400827d6590020cf952400833d5490020d794e400835d5390020bb98a40082ed6290020dd946400837551900209fd95400833e5450020cf551400835e5350020d754d40083765150020dd545400827f65100209f994400827d65100209f194400833e5410020cf55040082de6310020b758c400835e5310020d754c40082ee6210020bb58840082f66110020bd58440083765110020dd544400827d65cc020cf953300833d54cc020d794f300835d53cc020f3ccb300837651cc020dd547300827f658c0209f596300833e548c020cf552300835e538c020d754e30082ee628c020bb58a30083cc328c020dd9463008375518c0209fd95300833e544c020cf551300835e534c020d754d30082ef624c020bb18930083cf324c020dd9453008375514c0209f
  | 11 => 0x7e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c20bbd8943082ec6250c209fd94430827e6510c209f594430827c6510c20cf950430833d5410c20d794c430835d5310c209f992520827d64948209f98e520827d63948209f597420833e54d0820cf55342082de63d0820b758f420835e53d0820d754f420827f65908209f596420833e5490820cf552420835e5390820d754e420836e5290820be98242082f960908209fd95420833e5450820cf551420835e5350820d754d420836e52508209fd94420827d6510820cf950420833d5410820d794c420835d5310820be98042082f960108209f597320833e54cc820cf553320835e53cc820d754f32082ed65cc820db597320826d65cc820dbd5332083ae54cc820db55332083ad54cc820cb553320836f53cc820f394f320836d53cc820f354f320834d53cc820bb583320827f658c8209f596320833e548c820cf552320835e538c820d754e32082ee628c820db94a32082fa608c820be582320827f654c820cf951320833d544c820d794d320835d534c820db949320827f650c8209f594320833e540c820cf550320835e530c820d754c32083cd320c820be98032082f9600c820db594320826d650c820dbd5032083ae540c820db55032083ad540c820cb55032082ee630c820f398c320836f530c820f394c320836d530c820f354c320834d530c820f390c32083cd430c820fa98032082ed600c820fa58032082be64d4420af593510833e54d4420cf55351082de63d4420b758f510835e53d4420d754f510833e5494420cf552510835e5394420d754e510837751944209f992510827d64944209f98e510827d6394420ddd5251083765494420ed95251083365494420dd55251083b55494420cd55251083745494420ddd4e51083765394420f594e51083565394420dd54e51083d55394420d554e51083745394420f9cca51083e43294420ddd9251083766494420dd59251083746494420ddd8e51083766394420dd58e51083746394420ddd0e51083764394420dd50e51083744394420dd18a51083774294420dd90a51083754294420dd10a51083773294420dd8ca51083753294420dd0ca51083766094420dd182510833e5454420cf551510835e5354420d754d510827f64544209f191510827f63544209f18d510836f3254420db0c951083776554420ddd5151083765454420ed95151083365454420dd55151083b55454420cd55151083745454420ddd4d51083765354420f594d51083565354420dd54d51083d55354420d554d51083745354420f9cc951083e43254420ddd9151083766454420dd59151083746454420ddd8d51083766354420dd58d51083746354420ddd0d51083764354420dd50d51083744354420dd98951083774254420dd9095
  | 12 => 0xd50209f98f540835e63d50209798f540827d63d5020d758f540825d63d50209f98b540836e62d50209f987540837661d50209d987540827d61d5020dd587540827561d50209f983540837a60d50209f596540833f54950209f98e540827d63950209f986540827d61950208f596540833f6395020cf98e540833d6395020cf18e540833e6295020cf18a540833f6195020cf986540833d6195020cf186540833e6095020cf182540833f64550209fd8d540827c63550209fd89540827d62550209fd85540827c6155020cfd95540833f6355020cf98d540833d6355020cf18d540833e6255020cf189540833f6155020cf985540833d6155020cf185540833e6055020cf181540833c2055020af990540833d5415020b798c54082dd6315020bd98454082f561150209f990540833e64150208f990540827e6315020d798c540825e63150209f58c540835d63150209758c540827e6215020db988540826e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a6015020af99353082bd64d4c20cf953530833d54d4c20bd98753082f561d4c209f993530833e64d4c208f993530827d64d4c20cf593530823d64d4c209f98b530836e62d4c209f987530837661d4c209d987530827d61d4c20dd587530827561d4c209f983530837a60d4c209f596530833e5494c20cf552530835f5394c209f992530827d6494c209f986530827d6194c2097596530835f5494c20d7952530839e5494c20c7952530835d5494c20e7552530831d5494c20d715253083cc6294c20d7d92530835e6494c20d7592530835c6494c20d798a530835c6294c20d7d86530835e6194c20d7586530835c6194c20d7982530835c6094c20cf951530833d5454c209fd91530827c6454c20d7d8d530827f6254c209f589530836c6254c209fd85530827c6154c20d7d95530835f5454c20d7951530839e5454c20c7951530835d5454c20e7551530831d5454c20d715153083cc6254c20d7d91530835e6454c20d7591530835c6454c20d7989530835c6254c20d3189530835f6154c20d7985530835d6154c20d7185530835e6054c20d7181530835c2054c20af99053082bd6414c20cf950530833d5414c20b798c530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209798c530827e6214c20db988530826e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c20d794f430835d53d0c20bb98b43082ed62d0c209fd96430827e6590c209f596430827c6590c20cf952430833d5490c20d794e430835d5390c209fd9543082
  | 13 => 0xd714c514837551145209f990514827d64145209f98c514827d63145209f997414827d65d05209f197414835f53d0520d714f41482ee62d0520bb58b414837751d0520dd147414827e65905209f596414827c6590520cfd52414833c5490520d7d4e414835c5390520bb98a41482ed62905209fd95414827e65505209f195414835f5350520d714d414827e65105209f594414827c6510520cfd50414833c5410520b798c41482dd6310520d7d4c414835c5310520bb98841482ed6210520ddd4441483745110520ed50441482fa6010520be580414827e65cc5209f597314827c65cc520d7d4f314835c53cc520bb98b31482ed62cc520f38cb314827e658c5209f596314827c658c520d7d4e314835c538c520bb98a31482ed628c5209fd95314827e654c5209f195314835f534c520d714d31483ce324c5209f994314827d650c5209f194314835f530c520d714c31482ee620c520bb58831482fa600c520be580314827e65c8520d7d4f214835c53c8520bb997214836e65c8520bbd9321482ed64c8520dbd53214836d54c8520bbd8f21482ed63c8520f3d4f214836e53c8520db14f21483cc53c8520d314f214836c51c8520bb98321482de6388520b758e214835f5388520d714e21482ed6288520ddd4621483745188520be98221482f96088520d7d4d214835c5348520ddd4521483745148520bed8121482f86048520bbd9121482ed6448520dbd51214836d5448520bbd8d21482ed6348520f3d4d214836e5348520db14d21483cc5348520d314d21483e76148520f9d45214836c5148520f914521483eb6048520bb18121483e860485209f994214835f5308520d714c21482ee6208520f9484214827e65d0120cfd53404833c54d0120d7d4f404835c53d0120bb98b40482ed62d0120eb50b404827e6590120d7d4e404835c53901209fd95404827d65501209f195404833f5450120cf151404835f5350120d714d40482ef6250120bb18940483ad42501209f99440482de6310120b758c404835f5310120d714c40482ee6210120bb58840482f66110120bd584404827e65cc120d7d4f304835c53cc120bb98b30482ed62cc120f34cb304827e658c120d7d4e304835c538c120f38ca304827f654c1209f595304827c654c120d7d4d304835c534c120bbd8930482ec624c120f34c9304827e650c120af99030482bd640c120d7d4c304835c530c120bb98830482ed620c120f38c830482f6610c120bd584304835f53c8120d714f20483db53c8120f614f20483ea42c8120fa50b20483ea32c8120fa4cb20483eb21c8120fa487204835f5388120d714e20482ef6488120bb59220482ef6388120bb58e20483cf5388120db94e204836c5388120f314e204834c5388120bb58620483eb5088120b798f54082dd63d5020bd98754082f561
  | 14 => 0x93534835c64d4d20d7d8b534835d62d4d20d7d87534835e61d4d20d7587534835c61d4d20d7d83534835d60d4d20d7d4e534827e6494d209f592534827e6394d209798e534827d6294d20db58a534827e6194d209f586534827d6094d20de582534827f6454d209f191534835f6354d209fd89534836f6254d209bd89534827f6154d209f185534827f6054d20ded81534827e6514d20d754c534827e6414d209f590534835e6314d209f988534836d6214d209f188534827e6114d209f58453482de6514d20d7994534825e6514d20d7d50534835e5414d20d7550534835c5414d20f3588534835f6414d20d7990534835d6414d20d7190534835f6214d20d7588534834d6214d20d7d84534835e6114d20d7584534835c6114d20d7d80534835d6014d20d7480534827f65d0d209f997434827d65d0d209f197434835f53d0d20d714f43482ee62d0d20bb58b434827f6590d209f996434827d6590d209f196434835f5390d20d714e43482ee6290d20bb58a434827f6550d209f995434827d6550d209f195434835f5350d20d714d434827f6510d209f994434827d6510d209f194434835f5310d20d714c43482ee6210d20bb58843482fa6010d20be580434827e65d0920cfd53424833c54d0920b798f42482dd63d0920d7d4f424835c53d0920be98342482f960d09209f996424835f5390920d714e42482ee6590920db99642482ed6490920db952424836c5490920bb58e42483cf5390920db94e424836c5390920f314e424834c5390920bb58642482ee60909209f195424833f5450920cf151424835f5350920d714d42482fb6050920be181424836c65509209b19542483af6450920ebd51424836e5450920db15142483ac5450920bbd8d42483cf5350920db94d424836c5350920f314d424834c5350920bbd8542483eb6050920bb18142483e860509209f994424835f5310920d714c42482ee6210920eb508424827e65cc920d7d4f324835c53cc920be98332482f960cc9209f996324835f538c920d714e32482ee658c920db996324826e658c920bbd9232482ed648c920bb58e32483cf538c920db94e324836c538c920f314e324834c538c920f390e32483cd438c920bb58632482ee608c9209f195324835f534c920d714d32482fb604c920be181324836c654c9209b19532482ef644c920bb59132483cf634c920f3d4d324836e534c920db14d32483cc534c920d314d32482ef614c920fad8132482ec604c920fa181324827e650c920d7d4c324835c530c920bb98832483cd320c920d7d4f514835c53d45209f993514827d64d45209f98f514827d63d4520db90b514836d42d4520b798e51482dd6394520d7d4e514835c5394520ddd4651482bf6454520af19151482df6354520b718d514835f5354520d714d514835f531452
  | 15 => 0x8835c538ca20d794d328835d534ca20bed8132882f8604ca20d7d4c328835c530ca20f34c832882ed650ca20db594328836f540ca20db55032883ce630ca20dbd4c32883cf530ca20d3d4c328836d530ca20f314c32883ce430ca20f350c32882ed600ca20ddd46518827e64946209f592518827e63946209f58e518827f64546209f191518827f63546209f18d518836f3254620db0c951882be6414620af59051882de6314620b758c518837551146209fd97418827e65d06209f597418833e54d0620cf553418827f65906209f996418827d6590620dd946418837551906209fd95418827d65506209f195418833e5450620cf55141882ef6250620bb18941883765150620dd545418827f65106209f994418827d6510620b798c41882dd6310620bb98841882ed6210620ed50441882fa6010620be580418827f65cc6209f997318827d65cc620d794f318835d53cc620f30cb318827f658c6209f996318827d658c620bb98a31882ed628c620dd9463188375518c6209fd95318827d654c6209f195318835e534c620d754d31882ef624c620bb18931883cc324c620dd9453188375514c6209fd94318827e650c6209f59431882fa600c620be58031882de6388620b758e21883765188620dd54621882fa6088620be58221883765148620dd54521882fb6048620be181218833f54d0220cf153408833e5490220cf55240882ee6290220bb58a408833f5450220cf151408833e5410220cf55040882de6310220b758c40882ee6210220bb58840882f66110220bd584408835f53cc220d714f30883cf32cc220d794e308835d538c220bb98a30882ed628c220f30ca308835f534c220d714d30882ef624c220bb18930883cf324c220af99030882bd640c220d794c308835d530c220bb98830882ed620c220f30c830882f6610c220bd58430882ed65c8220db597208836f54c8220db55320882ee63c8220bb18f208836f53c8220db54f208836d51c8220be597208837965c82209f98f544827d63d51209f987544827d61d5120cfd5254482de6395120b758e544827e64951209f98e544835e63951209798e544827d6395120d758e544825d63951209f58a544836d62951209f986544827d61951209f58254483796095120b7d8d54482dc6355120bdd8554482f46155120cfd91544827f6355120d7d8d544825f63551209f18d544835c63551209718d544827f6255120dbd89544827f6155120ddd85544827761551209f185544837461551209d185544827f6055120ded81544827e6515120cf550544833e64151209f98c544827d63151209f988544836d62151209f188544827e61151209f584544827e64d4d209f593534827e61d4d209f587534835f54d4d20d7953534835d54d4d20d715353483cf62d4d20d7d93534835e64d4d20d75
  | 16 => 0xd654c7209f19531c835f534c720d714d31c83ce324c7209fd9431c827e650c7209f59431c82ee620c720bb58831c837651c8720dd54721c82fa60c8720be58321c82ef64c8720bb59321c836f54c8720db55321c82ef63c8720bb58f21c836e53c8720db14f21c836e51c8720f994721c83e551c8720bb98321c83ea60c8720fa58321c82de6388720b758e21c82ef6548720dbd9521c82ef6448720bb59121c836f5448720db55121c82ef6348720bb58d21c836e5348720db14d21c83e76148720f9d4521c836e5148720f914521c82ec6048720dd94421c83755108720f948421c82fa6008720be58021c833e54d0320cf55340c82ee62d0320bb58b40c83ad42d0320cf95140c833d5450320bbd8940c82ec6250320eb50940c82de6310320b758c40c82ee6210320bb58840c82f66110320bd58440c835e53cc320d754f30c82ee62cc320bb58b30c83cd32cc320d7d4e30c835c538c320f38ca30c835e534c320d754d30c82ef624c320bb18930c83cd324c320af99030c82bd640c320d7d4c30c835c530c320bb98830c82ed620c320f38c830c82f6610c320bd58430c827e63d52209f58f548836d62d52209f987548827d61d5220de983548833f54952209f98e548827d63952209f986548827d6195220cfd91548827f63552209f18d548827f61552209f185548833d5415220b798c54882dd6315220bd98454882f56115220cf990548827e6315220d798c548825e63152209f58c548835d63152209758c548836d62152209f984548837661152209d984548827d6115220dd58454882756115220de980548827e64d4e209f593538836d62d4e209f987538827d61d4e20de983538835f5394e209f992538827d6494e209f986538827d6194e209fd91538827c6454e20d7d8d538836f6254e209fd85538827c6154e20af99053882bd6414e20d754c53882f66114e20bd584538827e6414e20cf990538823e6414e209f590538833d6414e208f590538835e6314e20db588538827e6114e20dd98453882766114e209f58453883756114e209d584538837a6014e209fd97438827e65d0e209f597438827c65d0e20cf953438833d54d0e20bb98b43882ed62d0e209fd96438827e6590e209f596438827c6590e20d794e438835d5390e209fd95438827e6550e209f595438827c6550e20cf951438833d5450e20d794d438835d5350e20bbd8943882ec6250e209fd94438827e6510e209f594438827c6510e20be98043882f96010e20cf953428833d54d0a20b798f42882dd63d0a20be98342882f960d0a20cf951428833d5450a20bed8142882f86050a20d794f328835d53cca20be98332882f960cca20db597328836f54cca20db553328836f53cca20f394f328836d53cca20f354f32883ea60cca20bb58332883e960cca20d7d4e32
  | 17 => 0xc030fc545300c27e63d53209f58f54c836e62d53209f98754c827d61d5320de58354c833f5495320b798e54c82dd63953209f98e54c835e63953209798e54c827d6395320d758e54c825d6395320db98a54c827e61953209f58654c833f64553209fd8d54c827c63553209fd8554c827c6155320cf55054c833e64153209f98c54c827d6315320db98854c827e61153209f58454c837960153209f99353c827d64d4f20db98b53c827e61d4f209f58753c837960d4f20d7d4e53c827e6494f209f59253c836e6294f209f98653c827d6194f209fd9153c827c6454f20d7d8d53c827f6154f209f18553c835d5314f209f99053c827d6414f20d798c53c836e6214f209f98453c827d6114f20de58053c827f65d0f209f99743c827d65d0f209f19743c82ee62d0f20bb58b43c827f6590f209f99643c827d6590f209f19643c835f5390f20d714e43c82ee6290f20bb58a43c827f6550f209f99543c827d6550f209f19543c835f5350f20d714d43c827f6510f209f99443c827d6510f209f19443c82ee6210f20bb58843c833f54d0b20cf15342c82de63d0b20b758f42c833e5490b20cf55242c82fa6090b20be58242c836d6590b20db95242c83ae5490b20eb55242c836c5490b20bb58e42c836e5390b20db14e42c82ed6190b20bb98242c83ea6090b20fa58242c833f5450b20cf15142c82ef6550b20dbd9542c83af6450b20ebd5142c836e5450b20db15142c83ac5450b20bbd8d42c836e5350b20db14d42c82ef6150b20bb18142c833e5410b20cf55042c83ad4210b20be98042c82f96010b20d7d4f32c835c53ccb20d794e32c835d538cb20be98232c82f9608cb20db59632c82ef648cb20bb59232c836e538cb20f394e32c83cd538cb20db14e32c83ce438cb20f350e32c82ed618cb20bb98232c83ea608cb20fa58232c835f534cb20d714d32c82ef654cb20dbd9532c82ef644cb20bb59132c83cf634cb20f3d4d32c836e534cb20db14d32c83cc534cb20d314d32c82ef614cb20bb18132c835e530cb20d754c32c83cd320cb20be98032c82f9600cb20b798e51c82dd6394720ddd4651c827e64947209f59251c827e6394720d798e51c825e63947209f58e51c835d63947209758e51c827f64547209f19151c827f63547209f18d51c836e4254720db50951c837551147209fd9741c827e65d07209f59741c82ee62d0720bb58b41c827f65907209f99641c827d6590720bb98a41c82ed62907209fd9541c827d65507209f19541c827f65107209f99441c827d6510720b798c41c82dd6310720bb98841c82ed6210720ed50441c82fa6010720be58041c827f65cc7209f99731c827d65cc720d7d4f31c835c53cc720bb98b31c82ed62cc720f38cb31c827f658c7209f99631c827d658c720bb98a31c82ed628c7209fd9531c827
  | 18 => 0x9f594410c33e5410430cf550410c2de6310430b758c410c2ee6210430bb588410c36e5210430db548410c3765110430dd544410c3b54110430be980410c2f96010430cf953310c33d54cc430d794f310c36e52cc430db54b310c37651cc430dd547310c2fa60cc430be583310c27d658c430cf952310c33d548c430bb98a310c2ed628c430db94a310c36d528c430dd546310c27f654c430cf951310c33d544c430d794d310c36e524c430db549310c376514c430cf950310c33d540c430db948310c36d520c430dd944310c375510c430be980310c2f9600c4309fd97210c27e65c84309f597210c33e54c8430cf553210c36e52c8430db54b210c3cc32c8430dd947210c37551c84309fd96210c27e65884309f596210c33e5488430cf552210c2de6388430b758e210c36e5288430db54a210c3765188430dd546210c27f65484309f595210c27c6548430cf951210c33d5448430b7d8d210c2dc6348430db949210c36d5248430f30c9210c3765148430dd545210c27f65084309f994210c27d6508430cf950210c33d5408430db948210c36d5208430dd944210c37551084309f992500c27d6494030d78ca500c35c32940309f597400c33e54d0030cf553400c36e52d0030db54b400c37651d0030dd547400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c36e5290030db54a400c3765190030dd546400c27f6550030cf951400c33d5450030db949400c36d5250030dd945400c37551500309fd94400c27e65100309f594400c27c6510030cf950400c33d5410030b798c400c2dd6310030bb988400c2ed6210030db948400c36d5210030bd984400c2f56110030dd944400c3755110030cf953300c33d54cc030db94b300c36d52cc030dd947300c37551cc030d7d53300c39e54cc030d7553300c39d54cc030c7553300c2de62cc030f394b300c35d52cc030f354b300c34d52cc030f5947300c35d51cc030f5547300c35551cc030cf952300c33d548c030b758e300c35e538c030db94a300c36d528c030dd946300c375518c030ee952300c3b9548c030be58e300c37a538c030f694e300c3ea528c030fa54a300c3da328c030f60ca300c3f2518c030fc546300c27f654c030cf951300c33d544c030bbd89300c2ec624c030db949300c36d524c030dd945300c375514c030b7d95300c35f654c03097d95300c35f544c030e7951300c35d544c030e7551300c31d544c030f3d89300c2dc624c030f3189300c2cc624c030f3949300c35d524c030f3549300c34d524c030f5945300c35d514c030f5545300c355514c030b7d81300c35e504c030bed95300c37b654c0309ed95300c3ba544c030ee551300c2fb634c030f6d8d300c37a534c030f694d300c3eb624c030fa189300c3ea524c030fa549300c3f2514
  | 19 => 0x9420c36d52508309fd94420c27e65108309f594420c33e5410830cf550420c36e5210830db548420c33e54cc830cf553320c35e53cc830db94b320c36d52cc830be983320c2f960cc8309f596320c33e548c830cf552320c36d528c830b7596320c35d658c83097596320c35f548c830e7952320c35d548c830e7552320c31d548c830b798a320c3ce528c830d754a320c3cd528c830d354a320c2dd608c8309fd95320c33e544c830cf551320c35e534c830db949320c33e540c830cf550320c36e520c830db548320c3cd320c830be980320c2f9600c830d7d50320c39e540c830d7550320c39d540c830c7550320c2de620c830f3988320c3ce520c830d7548320c3cd520c830d3548320c3ce420c830f3508320c3da600c830b7580320c3d9600c830af993510c2bd64d4430cf953510c33d54d4430bb98b510c2ed62d4430db94b510c36d52d4430cf952510c33d5494430db94a510c36d5294430ddd46510c27e64944309f592510c27e62944309f58a510c3775494430dd952510c3b65494430cd952510c3755494430ed552510c3355494430dd152510c3775294430dd94a510c3e65294430d994a510c3755294430f954a510c3655294430dd14a510c3d63294430f50ca510c3776494430dd992510c3756494430dd192510c3746394430ddd0e510c3764394430dd50e510c3744394430ddd8a510c3766294430dd58a510c3746294430ddd0a510c3764294430dd50a510c3744294430ddcca510c3763294430dd4ca510c3743294430dd982510c3746094430cf951510c33d5454430db949510c36d52544309fd91510c27c64544309fd89510c27c6254430d78c9510c35c3254430ddd95510c3775454430dd951510c3b65454430cd951510c3755454430ed551510c3355454430dd151510c3775254430dd949510c3e65254430d9949510c3755254430f9549510c3655254430dd149510c3d63254430f50c9510c3776454430dd991510c3756454430dd191510c3766354430ddd0d510c3764354430dd50d510c3744354430ddd89510c3766254430dd589510c3746254430ddd09510c3764254430dd509510c3744254430ddcc9510c3763254430d58c9510c3753254430dd0c9510c3543254430dd981510c3746054430dd0c1510c2be6414430af590510c33e5414430cf550510c2ee6214430bb588510c36e5214430db548510c2f66114430dd544510c27f65d04309f997410c27d65d0430cf953410c33d54d0430db94b410c36d52d0430dd947410c37551d04309fd96410c27e65904309f596410c33e5490430cf552410c36e5290430db54a410c3765190430dd546410c27f65504309f595410c27c6550430cf951410c33d5450430b7d8d410c2dc6350430db949410c36d5250430dd945410c37551504309fd94410c27e6510430
  | 20 => 0xc35c528c130f314a304c34c528c130b7586304c3db508c130bb98b540c2ed62d5030bd987540c2f561d50309f98f540c35e63d50309f98b540c36e62d50309b98b540c27d62d5030db58b540c26d62d50309f987540c37661d50309d987540c27d61d5030dd587540c27561d50309f983540c37a60d50309f596540c33f54950309f98a540c27d62950309f986540c27d61950308f596540c33e6395030cf18e540c33f6295030cf98a540c33d6295030cf18a540c33f6195030cf986540c33d6195030cf186540c33e6095030cf182540c33f64550309fd8d540c27d63550309fd89540c27c62550309fd85540c27c6155030cfd95540c33e6355030cf18d540c33f6255030cf989540c33d6255030cf189540c33f6155030cf985540c33d6155030cf185540c33e6055030cf181540c33c3055030af990540c33d5415030bb988540c2ed6215030bd984540c2f561150309f990540c33e64150308f990540c27e6315030d798c540c25e63150309f988540c36e62150309b988540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a60150309f992530c27d6494c309f597430c33e54d0c30cf553430c2ee62d0c30bb58b430c27f6590c309f596430c33e5490c30cf552430c35e5390c30be982430c2f96090c309fd95430c33e5450c30cf551430c35e5350c309fd94430c27d6510c30cf950430c33d5410c30be980430c2f96010c30af993520c2bd64d4830cf953520c33d54d4830bd987520c2f561d4830cf952520c33d5494830dbd4a520c27e64948309f592520c27e61948309f586520c36f5494830db952520c3ae5494830cb952520c36d5494830eb552520c32d5494830db152520c3cc6394830dbd92520c36e6494830db592520c36c6494830db18e520c36f4394830db90e520c36d4394830db10e520c36f6194830db986520c36d6194830db186520c36e6094830db182520c33e5454830cf551520c27f64548309f191520c27f61548309f185520c36f6554830dbd51520c36e5454830eb951520c32e5454830db551520c3ad5454830cb551520c36c5454830f318d520c36f6454830db991520c36d6454830db191520c36e6354830dbd0d520c36e4354830db50d520c36c4354830dbd85520c36e6154830db585520c36c6154830db981520c36c6054830db0c1520c2be6414830af590520c33e5414830cf550520c2ee6214830db548520c2f66114830bd584520c27f65d08309f997420c27d65d0830cf953420c33d54d0830b798f420c2dd63d0830db94b420c36d52d08309fd96420c27e65908309f596420c33e5490830cf552420c36e5290830db54a420c27f65508309f595420c27c6550830cf951420c33d5450830b7d8d420c2dc6350830db94
  | 21 => 0x608c930be582324c36f524c930db149324c2fb604c930be181324c2df644c930b7591324c3cf624c930f3d49324c35c524c930f3149324c34c524c930b7d85324c3db604c930b7181324c3d8604c9309f994324c2de630c930dbd48324c3cd320c930dbd4b514c36c52d45309f993514c27d64d4530d790f514c35d43d45309f98b514c27d62d4530bb98a514c2ed6294530dbd4a514c36c5294530ddd46514c2bf6454530af191514c2ef6254530bb189514c36f5254530db149514c36f5214530db148514c37551145309f990514c27d64145309f988514c27d62145309f997414c27d65d05309f197414c2de63d0530b758f414c36f52d0530db14b414c37751d0530dd147414c27e65905309f596414c27c6590530cfd52414c33c5490530b798e414c2dd6390530dbd4a414c36c52905309fd95414c27e65505309f195414c36f5250530db149414c27e65105309f594414c27c6510530cfd50414c33c5410530b798c414c2dd6310530bb988414c2ed6210530dbd48414c36c5210530ddd44414c3745110530ed504414c2fa6010530be580414c27e65cc530dbd4b314c36c52cc530b7997314c35e65cc530b7d93314c2dd64cc530d7d53314c35d54cc530b758b314c3cf52cc530d714b314c3cc52cc530d314b314c35c51cc530b7983314c2dd638c530bb98a314c2ed628c530dbd4a314c36c528c530ddd46314c374518c530be982314c2f9608c530dbd49314c36c524c530ddd45314c374514c530bed81314c2f8604c530b7d91314c2dd644c530d7d51314c35d544c530b7d89314c3cf524c530d7149314c3cc524c530d3149314c3d7614c530f5d45314c35c514c530f5145314c3db604c530b7181314c3d8604c5309f994314c2de630c530dbd48314c36c520c530f54c4314c27e65c85309f597214c27c65c8530b798f214c2dd63c8530dbd4b214c36c52c8530f3ccb214c27e65885309f596214c27c6588530b798e214c2dd6388530dbd4a214c36c52885309fd95214c27e65485309f195214c2de6348530b758d214c36f5248530db149214c3cf32485309f994214c27d65085309f194214c2de6308530b758c214c36f5208530db148214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d0130e750f404c36f52d0130db14b404c27e6590130dbd4a404c36c52901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c39d4350130dbd49404c36c52501309f994404c2de6310130b758c404c2ee6210130bb588404c36f5210130db148404c2f66110130bd584404c36f52cc130db14b304c3da43cc130f650f304c3eb52cc130fa14b304c3db32cc130f64cb304c3db31cc130f64c7304c36f528c130db14a304c2df648c130b7592304c2dd628c130f3d4a304
  | 22 => 0x230b798e408c2dd6390230cfd51408c33c5450230cf950408c33d5410230b798c408c2dd6310230bb988408c2ed6210230bd984408c2f56110230b7597308c35d65cc230d7d53308c35d54cc230b798b308c35d52cc230d7547308c2f965cc230de597308c27e62d51309f58b544c27e61d51309f587544c33f5495130bb98a544c2ed62951309f992544c27d6395130d758e544c27e6295130db98a544c26e62951309f58a544c36d62951309b58a544c27e61951309f586544c27d6095130de582544c2ef6255130bb189544c2f76155130bd185544c33f64551309fd8d544c35f63551309fd89544c36f62551309bd89544c27c6255130db189544c26c62551309fd85544c37761551309dd85544c27c6155130dd185544c27461551309fd81544c37b60551309f994544c33d5415130cf990544c27e6315130d758c544c27c63151309f988544c27d62151309f984544c27d61151309f997434c33f54d0d30cf153434c2ee62d0d30bb58b434c2fa60d0d30be583434c27e6590d30b7996434c35e6590d30b7592434c35e5490d30d7152434c2dd6290d30b7586434c2de6090d309f195434c33f5450d30cf151434c2fb6050d30be181434c35c6550d3097195434c39f6450d30e7d51434c35e5450d30d7151434c39c5450d30b7d89434c2df6150d30f6d81434c2dc6050d30f6181434c27e6510d30b798c434c39d4310d309f993524c27d64d49309f987524c27d61d4930dbd53524c36e54d4930db553524c36c54d4930f3d8f524c3ce43d4930f350f524c36f64d4930db993524c36d64d4930db193524c36f63d4930dbd0f524c36e43d4930db50f524c36c43d4930dbd87524c36e61d4930db587524c36c61d4930dbd83524c36d60d4930dbd4a524c36d52149309f990524c27d6414930d790c524c35d43149309f984524c27d6114930bb994524c36e6514930dbd50524c36e5414930db550524c36c5414930f358c524c3ce4314930f350c524c36f6414930db990524c36d6414930db190524c36f6314930dbd0c524c36e4314930d390c524c36d4314930d350c524c36c4314930dbd84524c36e6114930db584524c36c6114930dbd80524c36d6014930db4c0524c27e65d09309f597424c27c65d0930b798f424c2dd63d0930dbd4b424c36c52d09309f996424c27d65909309f196424c2de6390930b758e424c36f5290930db14a424c27f65509309f995424c27c6550930dbd49424c36c52509309f994424c27d65109309f194424c2de6310930b758c424c36f5210930db148424c2fa6010930be580424c27e65cc930db14b324c2de65cc930d7997324c25e65cc930b7d93324c2dd64cc930f3d4b324c35c52cc930f314b324c34c52cc930f390b324c3cd42cc930b7587324c2de60cc930b758e324c36f528c930db14a324c2fa
  | 23 => 0xf55340cc2de63d0330b758f40cc39d43d0330cf95140cc33d5450330b7d8d40cc2dc6350330e750d40cc2de6310330b758c40cc2ee6210330bb58840cc2f66110330bd58440cc35d63d52309f98b548c27d62d52309f987548c27d61d5230de983548c33f54952309f98a548c27d62952309f986548c27d6195230cfd91548c27f62552309f189548c27f61552309f185548c33d5415230bb988548c2ed6215230bd984548c2f56115230cf990548c35d63152309f988548c36e62152309b988548c27d6215230db588548c26d62152309f984548c37661152309d984548c27d6115230dd584548c2756115230de980548c33e54d0e30cf553438c2ee62d0e30bb58b438c2fa60d0e30be583438c33e5450e30cf551438c2fb6050e30be181438c36f5294a309f992528c27d6494a309f986528c27d6194a309fd91528c27c6454a309fd85528c27c6154a30af990528c2bd6414a30db548528c2f66114a30bd584528c27f65d0a309f997428c27d65d0a30cf953428c33d54d0a30b798f428c2dd63d0a309fd96428c27e6590a309f596428c36e5290a30db54a428c27f6550a309f595428c27c6550a30cf951428c33d5450a30b7d8d428c2dc6350a30db949428c36d5250a309fd94428c27e6510a309f594428c2fa6010a30be580428c36e528ca30db54a328c2fa608ca30be582328c35f548ca30d7552328c3ce528ca30d754a328c3cd528ca30f6982328c2dd608ca30f6582328c36e524ca30db549328c2fb604ca30be181328c3cd320ca30b7594328c35d650ca30d7d50328c35d540ca30f3988328c3cf520ca30d7548328c3cc520ca30f3908328c3cd420ca30b7580328c37751946309f992518c27d64946309f98a518c27d62946309fd91518c27c64546309fd89518c27c6254630d78c9518c35c3254630af990518c2bd6414630bb988518c2ed6214630dd544518c27f65d06309f997418c27d65d0630cf953418c33d54d06309fd96418c27e65906309f596418c3765190630dd546418c27f65506309f595418c27c6550630cf951418c33d5450630b7d8d418c2dc6350630dd945418c37551506309fd94418c27e65106309f594418c2de6310630b758c418c2ee6210630bb588418c3b54110630be980418c2f96010630bb98a318c2ed628c630dd946318c375518c630be982318c2f9608c630dd945318c375514c630bed81318c2f8604c6309fd97218c27e65c86309f597218c36e52c8630db54b218c3cc32c86309fd96218c27e65886309f596218c2de6388630b758e218c3765188630dd546218c27f65486309f595218c27c6548630b7d8d218c2dc6348630db949218c36d5248630f30c9218c3765148630dd545218c27f65086309f994218c27d6508630be980218c2f96008630cfd53408c33c54d0230cf952408c33d5490
  | 24 => 0x54cc36e62953309b98a54cc27d6295330db58a54cc26d62953309f98654cc27d6195330cfd9154cc27f62553309f18954cc27f61553309f18554cc33d5415330cf99054cc35e63153309f98854cc27d62153309f98454cc27d6115330de58054cc33f54d0f30cf15343cc2ee62d0f30bb58b43cc33e5490f30cf55243cc2fa6090f30be58243cc35d6590f30d795243cc39e5490f30e755243cc35c5490f30b758a43cc2dd6190f30b798243cc3da6090f30f658243cc33f5450f30cf15143cc2df6550f30d7d9543cc39f6450f30e7d5143cc35e5450f30d715143cc39c5450f30b7d8943cc2df6150f30b718143cc33e5410f30cf55043cc39d4310f30be98043cc2f96010f30dbd4a52cc27e6494b309f59252cc35e4394b30d750e52cc27e6194b309f58652cc27f6454b309f19152cc27f6154b309f18552cc36d5214b309fd9742cc27e65d0b309f59742cc2de63d0b30b758f42cc27f6590b309f99642cc27d6590b30b798e42cc2dd6390b309fd9542cc27d6550b309f19542cc27f6510b309f99442cc27d6510b30b798c42cc2dd6310b30db94b32cc36d52ccb30be98332cc2f960ccb30b7d9332cc2dd64ccb30d794b32cc3ce52ccb30f354b32cc3ce42ccb30f350b32cc2dd61ccb30b798332cc3da60ccb30f658332cc2df654cb30d7d9532cc2df644cb30b759132cc3cf624cb30f3d4932cc35e524cb30f314932cc2df614cb30b718132cc36e520cb30db54832cc3cd320cb30be98032cc2f9600cb30bb98a51cc2ed6294730ddd4651cc27e64947309f59251cc27e6294730db98a51cc26e62947309f58a51cc36d62947309b58a51cc27f64547309f19151cc35e4354730d750d51cc27f62547309f18951cc37551147309fd9741cc27e65d07309f59741cc2de63d0730b758f41cc27f65907309f99641cc27d6590730b798e41cc2dd63907309fd9541cc27d65507309f19541cc27f65107309f99441cc27d6510730b798c41cc2dd6310730bb98841cc2ed6210730ed50441cc2fa6010730be58041cc37651cc730dd54731cc2fa60cc730be58331cc2df64cc730b759331cc35f54cc730d755331cc2dd62cc730d794b31cc35e51cc730f594731cc3d551cc730b798331cc3da60cc730f658331cc2ee628c730bb58a31cc2df654c730d7d9531cc2df644c730b759131cc35f544c730d755131cc2df624c730d794931cc3d7614c730f5d4531cc35e514c730f514531cc2dc604c730dd94431cc375510c730f54c431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730b798f21cc2dd63c8730f3ccb21cc27f65887309f99621cc27d6588730b798e21cc2dd63887309fd9521cc27d65487309f19521cc2de6348730b758d21cc3cf32487309fd9421cc27e65087309f59421cc2de6308730b758c21cc33e54d0330c
  | 25 => 0x3746054440dd10151102de6314440b758c511035e5314440d754c51102ee6214440bb588511036e5214440db54851102f66114440dd544511033e54d0440d794f411035d53d0440db94b411036d52d0440dd947411037551d0440be98341102f960d04409f596411035e5390440d754e411036e5290440db54a411037551904409fd95411033e5450440d794d411035d5350440db949411036d5250440dd94541102de6310440b758c411035e5310440d754c41102ee6210440bb588411036e5210440db54841103765110440dd54441103b54110440be98041102f960104409fd97311027e65cc4409f597311035e53cc440d754f311036e52cc440db54b311037651cc440dd547311027f658c4409f996311027d658c440d794e311035d538c440bb98a31102ed628c440db94a311036d528c440dd9463110375518c4409fd95311027d654c4409f19531102bf644c440af191311035e534c440d754d311036e524c440db5493110376514c440dd545311027f650c4409f994311027d650c440d794c311035d530c440db948311036d520c440dd9443110375510c4409fd97211027e65c84409f597211035e53c8440d754f211036e52c8440db54b211037651c8440dd547211027f65884409f996211027d6588440b798e21102dd6388440d794e211035d5388440db94a211036d5288440dd946211037551884409fd95211027d65484409f19521102bf6448440af191211035e5348440d754d211036e5248440db54921103765148440dd545211027f65084409f994211027d6508440d794c211035d5308440db948211036d5208440dd94421103755108440d794f401035d53d0040db94b401036d52d0040dd947401037551d0040e794f401033d53d0040e754f401031d53d0040eb94b401033d52d0040eb54b401032d52d0040ed947401033d51d0040ed547401033551d0040af592401033e5490040d794e401035d5390040db94a401036d5290040dd94640103755190040be592401037a5490040ee95240103da5390040f654e40103ea5290040fa54a40103f25190040de54640103f15190040dc546401027f6550040d794d401035d5350040db949401036d5250040dd94540103755150040afd95401033f65500408fd95401039e5350040cf54d401039d5350040c754d40103ae5250040cf54940103ad5250040cb54940103b65150040cf54540103b55150040cd54540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040f694d40103d95350040fa94940103e95250040fc94540103795150040fc54540103715150040eed0540103b94150040d798f54cc27e62d53309f58b54cc27e61d53309f58754cc37960d5330cfd5254cc2ee6295330bb58a54cc35e63953309f98a
  | 26 => 0x394840d394e521036d5394840f354e521034d5394840db14e521036c6494840dbd8e521036e6394840db58e521036c6394840dbd0e521036e4394840db50e521036c4394840dbd86521036e6194840db586521036c6194840db982521036c6094840d794d521035d53548409fd8d521027c63548409fd85521027c6154840dbd95521036f5354840db94d52103ce5354840d394d521036d5354840f354d521034d5354840db14d521036e6454840dbd8d521036e6354840db58d521036c6354840dbd0d521036e4354840db50d521036c4354840dbd85521036e6154840db585521036c6154840db981521036c6054840db10152102de6314840b758c521035e5314840d754c52102ee6214840db54852102f66114840bd584521033e54d0840b798f42102dd63d0840d794f421035d53d0840db94b421036d52d0840be98342102f960d08409f596421035e5390840d754e421036d52908409fd95421033e5450840d794d421035d5350840db949421035e5310840d754c421036e5210840db54842102fa6010840be580421027f65cc8409f997321027d65cc840d794f321035d53cc840db94b321036d52cc8409fd96321027e658c8409f596321035e538c840d754e321036e528c840db54a321027f654c8409f595321027c654c840d794d321035d534c840db949321036d524c8409fd94321027e650c8409f594321035e530c840d754c321036e520c840db54832103cd320c840b798f51102dd63d4440d794f511035d53d4440bb98b51102ed62d4440db94b511036d52d4440d794e511035d5394440db94a511036d5294440ddd46511027e63944409f58e511027e62944409f58a51103775394440dd94e51103d65394440d594e51103755394440f554e51103555394440dd14e51103775294440dd94a51103e65294440d994a51103755294440f954a51103655294440dd14a51103746494440ddd8e51103766394440dd58e51103746394440ddd0e51103764394440dd50e51103744394440ddd8a51103766294440dd58a51103746294440ddd0a51103764294440dd50a51103744294440ddcca51103763294440dd4ca51103743294440dd98251103746094440d794d511035d5354440db949511036d52544409fd8d511027c63544409fd89511027c6254440ddd9551103775354440dd94d51103d65354440d594d51103755354440f554d51103555354440dd14d51103775254440dd94951103e65254440d994951103755254440f954951103655254440dd14951103766454440ddd8d51103766354440dd58d51103746354440ddd0d51103764354440dd50d51103744354440ddd8951103766254440dd58951103746254440ddd0951103764254440dd50951103744254440ddcc951103763254440dd4c951103743254440dd9815110
  | 27 => 0x40b7d8d51502dc6354540bbd8951502ec6254540b798c51502dd6314540bb98851502ed6214540dd544515027e6314540d798c515025e63145409f58c515035d63145409758c515027e6214540db988515026e62145409f588515036d62145409b588515037960145409f99741502be65d0540cf99741502bd63d0540af58b415033c51d0540eed8341502be60d0540ee18341502bd6490540ddd4641503745190540be98241502f96090540ddd4541503745150540bed8141502f86050540afd8d41502bf6250540edd8541503b75150540cf14541503b45150540cd14541503bb6050540af18141503b860505409f99441502be6410540b798c41502dd6310540bb98841502ed6210540ed50441502fa60105409f997315027d65cc5409f19731502be64cc540af593315039d43cc540ddd47315037451cc5409f996315027d658c5409f19631502be648c540af592315035f538c540d714e31502ee628c540bb58a31502fa608c540be582315027f654c5409f995315027c654c540af99131502bd644c540e750d315027e650c5409f594315027c650c540af99031502bd640c540d7d4c315035c530c540ddd443150374510c540be98031502f9600c5409f997215027d65c85409f19721502be64c8540af59321503ad42c8540ddd47215037451c85409f996215027d65885409f19621502be6488540af59221502de6388540b758e215036f5288540db14a21502fa6088540be582215027f65485409f995215027c6548540af99121502bd6448540eb509215027e65085409f594215027c6508540af99021502bd6408540dbd48215036c5208540ddd4421503745108540be98021502f96008540eed0f40503b943d0140eed0b40503b942d0140be58740503bb41d0140ee50740502bd6390140af58a40502bd6190140eed4240502ee62d4c40bb58b53102f661d4c40bd587531035f5394c409f98a531027d6294c409f986531027d6194c40d7192531035f6294c40d798a531035d6294c40d718a531035f6194c40d7986531035d6194c40d7186531035e6094c40d7182531027f6254c409f189531027f6154c409f185531035f6554c40d7991531035f6254c40d7989531035d6254c40d7189531035f6154c40d7985531035d6154c40d7185531035e6054c40d7181531035c4054c40b798c531035d5314c40bb98853102ed6214c40bd98453102f56114c40cf953431035e53d0c40d754f43102ee62d0c40bb58b43102fa60d0c40be583431027d6590c40d754e431027f6550c40cf951431035e5350c40d794c431035d5310c40be98043102f96010c40b798f52102dd63d4840d794f521035d53d4840bd98752102f561d4840d794e521035d5394840dbd4a521027e63948409f58e521027e61948409f586521036f5394840db94e52103ce5
  | 28 => 0x58c51902ee6214640bb58851903755114640dd94641903755190640be98241902f96090640dd94541903755150640bed8141902f86050640b798c41902dd6310640bb98841902ed6210640ed50441902f960106409fd97319027e65cc6409f597319035e53cc640d754f319027f658c6409f996319027d658c640bb98a31902ed628c640dd9463190375518c640be98231902f9608c6409fd95319027d654c6409f19531902bf644c640af191319035e534c640d754d3190376514c640dd545319027f650c6409f994319027d650c640be98031902f9600c6409fd97219027e65c86409f597219036e52c8640db54b219027f65886409f996219027d6588640b798e21902dd6388640dd94621903755188640be98221902f960886409fd95219027d65486409f19521902bf6448640af191219036e5248640db54921903765148640dd545219027f65086409f994219027d6508640be98021902f96008640af597409033d65d0240cf54f409033d52d0240cf54740902f965d0240de59740902f961d02409f98b535027d62d4d409f987535027d61d4d40d7d4e53502ef6254d40bb18953502f76154d40bd185535035d5314d409f988535027d6214d409f984535027d6114d409f99743502ee62d0d40bb58b43502be65d0d40cf997435033c53d0d40eb98b43502bd62d0d40eb58b43502ad62d0d40af58743502be60d0d40af592435035f5390d40d714e43502fa6090d40be582435035f5350d40d714d43502fb6050d40be181435039f6350d40e7d4d435033c5350d40e714d43502bf6250d40afd8543503bb6050d40af18143503b86050d409f99443502be6410d40e750c435027e63d49409f58f525027e61d49409f587525036f5294940b7d8d52502dc6354940bdd8552502f46154940db548525027e63149409f58c525027e61149409f584525027e65d0940b798f42502dd63d0940af997425033e65d0940e798f42502bd63d0940e758f425029d63d0940cf14b42502bd61d0940af98342502bd6490940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bed8142502f86050940afd8d42503af6250940ebd49425033c5250940eb14942502bf6150940eed8142502bc6050940ee181425027e6510940af99042503ad42109409f997325027d65cc9409f19732502be64cc940af593325036f52cc940db14b32503ad42cc9409f996325027d658c9409f19632502be648c940af592325035f538c940d714e325039d438c9409fd95325027e654c9409f19532502be644c940af591325027e650c9409f594325027c650c940af99032502bd640c940d7d4c325035c530c940e750c325036f520c940db14832503ad420c940f34c832502fa600c940be580325027e63d45409f58f515027e62d45409f58b515037751945
  | 29 => 0x2d02bd648cb40d794e32d035d538cb40e750e32d027f654cb409f59532d027c654cb40af99132d02bd644cb409fd9432d027e650cb409f59432d02be640cb40af59032d035e530cb40d754c32d039d430cb40db94832d036d520cb40eb50832d03cd320cb40ddd4651d027e63947409f58e51d027e62947409f58a51d027f63547409f18d51d027f62547409f18951d02de6314740b758c51d02ee6214740bb58851d03755114740dd94741d037551d0740be98341d02f960d0740af58f41d02bd62d0740cf94741d03b651d0740ed54741d02be60d0740ee98341d03b960d0740afd9541d033f6550740afd8d41d02bf6250740edd8541d03b75150740cf94541d03b45150740af18141d02de6310740b758c41d02ee6210740bb58841d03765110740dd54441d03b54110740be98041d02f960107409fd9731d027e65cc7409f59731d02be64cc740af59331d035e53cc740d754f31d039d43cc7409fd9631d027e658c7409f59631d02be648c740af59231d02ee628c740bb58a31d027f654c7409f59531d027c654c740af99131d02bd644c740d794d31d035d534c740e750d31d027f650c7409f99431d027d650c740af99031d02bd640c7409fd9721d027e65c87409f59721d02be64c8740af59321d036e52c8740db54b21d03ad42c87409fd9621d027e65887409f59621d02be6488740af59221d02de6388740b758e21d027f65487409f59521d027c6548740af99121d02bd6448740db94921d036d5248740eb50921d027f65087409f99421d027d6508740af99021d02bd6408740d7d4e539027e6294e409f58a539027e6194e409f58653902ef6254e40bb189539027f6254e40dbd89539026f6254e409f189539036c6254e409b189539027f6154e409f185539035d5314e40bb98853902ed6214e40bd98453902f56114e40bb98b43902ed62d0e40d794e439035d5390e40be98243902f96090e40d794d439035d5350e40bed8143902f86050e40dbd4a529027e6394a409f58e529027e6194a409f58652902df6354a40b718d529027f6354a40d7d8d529025f6354a409f18d529035c6354a409718d529027f6154a409f18552902de6314a40b758c529036d5214a40bd98452902f56114a40b798f42902dd63d0a40db94a429036d5290a40be98242902f96090a40db949429036d5250a40bed8142902f86050a409fd97329027e65cca409f597329035e53cca40d754f329027f658ca409f996329027d658ca40db94a329036d528ca409fd95329027d654ca409f195329035e534ca40d754d329036e524ca40db549329027f650ca409f994329027d650ca40f34c832902fa600ca40be580329037751946409f98e519027d63946409f98a519027d6294640de982519027f63546409f18d519027f62546409f18951902de6314640b7
  | 30 => 0x5e538c821d754e32086f6618c821bd586320867f654c8219fd94320867d650c821d794c320875d530c821db94832087cd320c821bd98432086f5610c8219f992510867d64944219f98e510875e63944219798e510867d6394421d758e510865d63944219f597410867f65904219f596410873e5490421cf55241086ee6290421bb58a410867f65504219fd94410867e65104219f594410867c6510421cf950410873d5410421b798c41086dd6310421bb98841086ed6210421ed50441086fa6010421be580410867d65cc421d7d4f310875c53cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c4219fd95310875f534c421d714d310867f650c4219f994310867d650c4219f194310875e530c421d754c31086ee620c421bb588310876f54c8421db553210876e53c8421db14f21086de6388421b758e21086ed6288421db94a21087d66388421f558e21086f56288421dd94a21087e652884219fd9521086ef6548421dbd95210866f6548421dbd51210876d5448421db94d210876c5348421bbd85210876e5148421f9d0521087e44148421f98c521087e53148421bdd95210877765484219dd9521086f76248421f9d8921087765248421f994921087e74248421f910921087e63248421f94c9210877b50940219f992500867d64940219f98e500867d63940219fd91500867c64540219fd8d500867c6354021dbc8550087762154021db48550087752154021af99050086bd6414021b798c50086dd6314021de54050086ee62d4f40bb58b53d035f5394f409f98a53d027d6294f409f98653d027d6194f409fd8953d027c6254f409fd8553d027c6154f40d754c53d035e53d0f40d754f43d02ee62d0f40bb58b43d02fa60d0f40be58343d033e53d0f40e794f43d039d53d0f40eb98b43d02bd62d0f40eb58b43d02ad62d0f40af58743d02be60d0f40ee98343d03b960d0f40afd9543d033f6550f40e7d8d43d039f5350f40cf94d43d039c5350f40afd8943d02bf6150f40af18143d035e5310f40d754c43d039d4310f40be98043d02f96010f40b798f52d02dd63d4b40dbd4a52d027e6394b409f58e52d027e6194b409f58652d027f6354b409f18d52d027f6154b409f18552d036d5214b40b798f42d02dd63d0b40db94b42d036d52d0b40be98342d02f960d0b40e798f42d02bd63d0b40e758f42d029d63d0b40cf94b42d03ae52d0b40eb54b42d02bd61d0b40af98342d03ba60d0b40ee58342d02bf6550b40cfd9542d02bf6350b40ebd8942d03af5250b40cf94942d03ac5250b40afd8542d02bc6050b40db94842d036d5210b40eb50842d02fa6010b40be58042d027f65ccb409f99732d027d65ccb40af99332d02bd64ccb40db94b32d036d52ccb40eb50b32d027f658cb409f99632d027d658cb40af9923
  | 31 => 0x10521b798c41486dd6310521bb98841486ed6210521ed50441486fa6010521be580414867e65cc521d7d4f314875c53cc521bb98b31486ed62cc521f30cb314867e658c521bb98a31486ed628c5219fd95314867d654c5219f195314875f534c521d714d31486ef624c521bb18931487cc324c5219f99431487d5310c521f990b21487e542c8521f9ccb21487e432c8521bd58321486de6388521b758e21486ef6488521bb59221486ee6388521f398e21486ce6388521f358e21486ec6388521f9d4621486ed60885219f993504867d64d41219f98f504867d63d4121db90b504876d42d4121ded4250486bf6454121af19150486df6354121b718d50486be6414121af59050486de6314121b758c504877950141219f990504873e64141218f990504867d6414121cf590504863d64141219f98c504875e63141219798c504867d6314121d758c504865d6314121dbcc8504876c32141219f98f540867d63d50219f98b540876e62d50219f987540877661d50219f983540867d60d50219f596540873f54950219f98e540867d63950219f982540867d6095021cfd91540867f63550219f18d540867f60550219f181540873d5415021b798c54086dd6315021be98054086f960150219f990540873e64150219f98c540875e63150219798c540867d6315021d758c540865d63150219f988540876e62150219b988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e580540867e64d4c219f593530867e62d4c21db98b530866e62d4c219f987530877661d4c219f983530867d60d4c219f596530875f5394c219f992530867d6494c219f982530867d6094c219fd91530867c6454c21d7d8d530867f6054c219f18153086be6414c21af590530875d5314c21be98053086f96014c219f990530873e6414c218f990530867d6414c21cf590530863d6414c219f98c530875e6314c219f988530876e6214c219f98453087766114c219f980530877a6014c219e980530867d6014c21de58053086796014c219fd97430867e65d0c219f597430867c65d0c21cf953430873d54d0c21bb98b43086ed62d0c219fd96430867e6590c219f596430867c6590c21d794e430875d5390c21bb98a43086ed6290c21bd98643086f56190c219fd95430867e6550c219f595430867c6550c21cf951430873d5450c21d794d430875d5350c219fd94430867e6510c219f594430867c6510c219f992520867d64948219f98e520867d63948219f59742086de63d0821b758f420867f65908219f596420873e5490821cf552420876e5290821bd98642086f561908219fd95420876e52508219fd94420867d6510821cf950420873d5410821eb50842086f66110821bd584420867d65cc821db94b320867f658c8219f59632087
  | 32 => 0x1d794c508875d5314221de540508867e63d51219f58f544867e60d51219f583544873f5495121b798e54486dd63951219f992544867e6395121d798e544865e63951219f58e544875d63951219758e544867d6295121db58a544867d6195121dd586544867e60951219f582544873f64551219fd8d544867c63551219fd89544876f62551219fd85544877761551219fd81544867c60551219f994544873d5415121cf990544867e63151219f58c544876d62151219f980544867d60151219f993534867d64d4d21db58b534867e60d4d219f58353486be6494d21af592534875f5394d219f992534873e6494d218f992534867d6494d21cf592534863d6494d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d219f582534867f6454d219f191534875f6354d219fd89534876f6254d219fd8553487776154d219fd81534867c6054d219f994534875d5314d219f990534867d6414d21d798c534867e6014d219f580534867f65d0d219f997434867d65d0d219f197434873f54d0d21cf15343486ee62d0d21bb58b434867f6590d219f996434867d6590d219f196434875f5390d21d714e434867f6550d219f995434867d6550d219f195434873f5450d21cf151434875f5350d21d714d43486ef6250d21bb18943486f76150d21bd185434867f6510d219f994434867d6510d219f19443486ee6210d21bb58843486f66110d21bd584434867e65d0921cfd53424873c54d0921b798f42486dd63d0921bd98742486f561d09219f99642486ee6590921db99642486ed6490921db952424876c5490921bb98e424876e5390921db14e42486ee6190921bb582424867c6550921cfd51424873c5450921bdd8542486f46150921db195424866c6550921ebd9142487af5450921db951424876c5450921eb151424872c5450921bb18d424876e5350921db14d42487e76150921bb18542487e46150921b918542486ef60509219f99442486ee62109219f997324875f53cc921d714f32486f661cc921bd587324876e65cc9219b99732486ef64cc921bb593324876f54cc921db553324876f53cc921f3d4f324876d53cc921f314f32486ee61cc921f998732486e661cc921f958732486ed60cc9219f996324875e538c921d754e32486ee628c9219f195324875f534c921d714d32486f7614c921bd185324867e650c921d794c324875d530c921f34c832486ee650c921db99432486ef640c921bb590324876f540c921db55032486ee630c921f398c324876f530c921f394c324876d530c921f354c324874d530c921f390c32487cd430c921bb98432486ed600c9219f997414873f54d0521cf15341486ee62d0521bb58b414867e65905219fd95414867d65505219f195414873f5450521cf15141486ef6250521bb189414867e65
  | 33 => 0x8d548867f60552219f181548873d5415221b798c54886dd6315221be98054886f96015221cf990548867e6315221d798c548865e63152219f58c548875d63152219758c548876d6215221dd984548867e6015221de980548867a60152219f580548877960152219e580548867e64d4e219f593538876d62d4e21dd987538867e60d4e219f583538875f5394e219f992538867d6494e219f982538867d6094e21d7d52538875e5494e21d7552538875c5494e21d7d92538875e6494e21d7592538875c6494e21d7d8a538875d6294e21d7986538875c6194e21d7d82538875e6094e21d7582538875c6094e219fd91538867c6454e21d7d8d538867f6054e219f181538875f6554e21d7d51538875e5454e21d7551538875c5454e21d7d91538875e6454e21d7591538875c6454e21d7d89538875d6254e21d7985538875c6154e21d7d81538875e6054e21d7581538875c6054e21d754c538867e6414e219f590538875e6314e21db58853887766114e219f980538867d6014e219fd97438867e65d0e219f597438867c65d0e21d794f438875d53d0e21bb98b43886ed62d0e219fd96438867e6590e219f596438867c6590e21d794e438875d5390e21bb98a43886ed6290e219fd95438867e6550e219f595438867c6550e21d794d438875d5350e21bdd8543886f46150e219fd94438867e6510e219f594438867c6510e21d794c438875d5310e21bd98443886f56110e21cf953428873d54d0a21b798f42886dd63d0a21d794f428875d53d0a21bd98742886f561d0a21d794e428875d5390a21cf951428873d5450a21d794d428875d5350a21bdd8542886f46150a21d794c428875d5310a21eb508428875e53cca21d754f32886f661cca21bd587328875e538ca21d754e328875e534ca21d754d32886f7614ca21bd185328875e530ca21d754c32887cd320ca21d794f418875d53d0621cf952418873d5490621d794e418875d5390621bb98a41886ed6290621d794d418875d5350621cf950418873d5410621b798c41886dd6310621d794c418875d5310621bb98841886ed6210621ed50441886fa6010621be580418875e53cc621d754f318875e538c621d754e31886ee628c621bb58a318875e534c621d754d318875e530c621d754c31886ee620c621bb58831887d5310c621d794f218875d53c8621bb597218876d65c8621dbd53218876d54c8621db94f21887ce53c8621d394f21887cd53c8621db14f21886f565c8621dd59721887d653c8621f554f21886f560c8621b798f50886dd63d4221d794f508875d53d4221d794e508875d5394221ded42508867e64942219f592508867e63942219f58e508875e5354221d754d508867f64542219f191508867f63542219f18d508876f2154221af99050886bd6414221b798c50886dd631422
  | 34 => 0xc876e62953219f98254c867d6095321cfd9154c867f63553219f18d54c867f60553219f18154c873d5415321cf99054c867e63153219f58c54c876e6215321dd58454c867e60153219f58054c86be64d4f21af59353c867e64d4f21cf99353c863e64d4f219f59353c873d64d4f218f59353c876e62d4f21dd58753c867e60d4f219f58353c875f5394f219f99253c867d6494f219f98253c867d6094f219fd9153c867c6454f21d7d8d53c876c6254f219fd8153c867c6054f21d754c53c867e6414f219f59053c875e6314f21db98853c87756114f219f98053c867d6014f219fd9743c867e65d0f219f59743c867c65d0f21d794f43c875d53d0f21bb98b43c86ed62d0f219fd9643c867e6590f219f59643c867c6590f21cf95243c873d5490f21d7d4e43c875c5390f21bd98643c86f56190f219fd9543c867e6550f219f59543c867c6550f21d7d4d43c875c5350f21bbd8943c86ec6250f219fd9443c867e6510f219f59443c867c6510f21cf95043c873d5410f21d794c43c875d5310f21bb98843c86ed6210f21b798f42c86dd63d0b21cf95242c873d5490b21bd98642c86f56190b21db59642c876e5490b21eb95242c87ad5490b21db15242c86ee6390b21db94e42c876c5390b21bb98642c87e66190b21f958642c86ed6090b21bbd9542c876f6550b21ebd9142c876e5450b21db15142c86ec6350b21db94d42c876c5350b21bb18542c86ef6050b21cf95042c873d5410b21bd98442c86f56110b21bb59732c876d65ccb21bbd9332c86ed64ccb21dbd5332c876d54ccb21dbd4f32c876d53ccb21bb98732c86ed60ccb21d794e32c875d538cb21bd98632c86f5618cb21d794c32c875d530cb21f34c832c86f6610cb21bd58432c876d650cb21bbd9032c86ed640cb21dbd5032c876d540cb21f398c32c876f530cb21f394c32c876d530cb21f354c32c874d530cb21f390c32c87cd430cb21bb98432c87e6610cb21f958432c86ed600cb21cf95341c873d54d0721bb98b41c86ed62d0721cf95141c873d5450721bbd8941c86ec6250721b798c41c86dd6310721bb98841c86ed6210721ed50441c86fa6010721be58041c875e53cc721d754f31c86ee62cc721bb58b31c87cc32cc721bb98a31c86ed628c721d794d31c875d534c721bbd8931c86ec624c721f30c931c877b50943219f99250c867d64943219f98e50c867d6394321dbcca50c876c32943219fd9150c867c64543219fd8d50c867c6354321db90950c876d4254321af99050c86bd6414321b798c50c86dd6314321de54050c86de63d5221b758f548867e63d5221d798f548865e63d52219f58f548875d63d52219758f548876d62d5221dd987548867e60d52219f583548873f54952219f98e548867d63952219f982548867d6095221cfd91548867f63552219f1
  | 35 => 0xc32141319f98f540c75e63d50319f98b540c67d62d50319f987540c77661d50319f983540c67d60d50319f596540c73f54950319f98a540c67d62950319f982540c67d6095031cfd91540c67f62550319f189540c67f60550319f181540c73d5415031bb988540c6ed6215031be980540c6f960150319f990540c73e64150319f98c540c75e63150319798c540c67e6215031db988540c66e62150319f588540c76d62150319b588540c67e6115031dd984540c67e6015031de980540c67a60150319f580540c77960150319e580540c67e6494c319f592530c67d65d0c31bb98b430c6ed62d0c319fd96430c67d6590c31cf952430c73d5490c31d794e430c6f66190c31bd586430c67f6550c31d794d430c67f6510c319f594430c73e5410c31cf550430c79d4310c31bd984430c6f56110c31dbd4a520c67e64948319f592520c67e60948319f582520c67f64548319f191520c67f60548319f181520c6be6414831af590520c76d5214831be980520c6f960148319fd97420c67e65d08319f597420c73e54d0831cf553420c6de63d0831b758f420c67f65908319f996420c67d6590831b798e420c6dd6390831db94a420c76d5290831bd986420c6f561908319fd95420c67d65508319f195420c73e5450831cf551420c76e5250831db549420c67f65108319f994420c67d6510831db94b320c76d52cc831bd987320c6f561cc8319f596320c75e538c8319fd95320c75e530c831db948320c76d520c831f34c8320c6f6610c831bd584320c67e64944319f592510c76e6294431db58a510c67d65d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd63904319fd95410c67f65104319f994410c67d65104319f194410c73e5410431cf550410c6de6310431b758c410c6ee6210431bb588410c7b54110431be980410c6f96010431d7d53310c75d54cc431d794b310c6dd638c431d794e310c6ee628c431bb58a310c6f5638c431dd94e310c7d6538c431f998a310c7e5628c4319fd95310c6df654c431d7d95310c65f654c431d7d51310c75d544c431d7949310c6df614c431d7945310c7d7414c431f5105310c6f7654c431ddd95310c677654c431bdd8d310c7d7634c431dd94d310c7d6534c431f5d0d310c7d4434c431f5cc9310c7d5324c431ded42500c67e64940319f592500c67e62940319f58a500c67f64540319f191500c67f62540319f189500c75f3154031dd8c5500c75d3154031dd4c5500c6be6414031af590500c6ee6214031bb588500c7795014031b798f54c86dd63d53219f98f54c875e63d53219798f54c867d63d5321d758f54c865d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c86de6395321b758e54c867e6395321d798e54c865e63953219f58e54c875d63953219758e54
  | 36 => 0x51319f992544c67d6395131d758e544c67e6295131db98a544c66e62951319f58a544c76d62951319b58a544c67d6195131dd586544c67e60951319f582544c73f64551319fd8d544c75f63551319fd89544c67c62551319fd85544c77761551319fd81544c67c60551319f994544c73d5415131cf990544c75d63151319f988544c67d62151319f980544c67d60151319f997434c73f54d0d31cf153434c6ee62d0d31bb58b434c6f661d0d31bd587434c67e6590d31b7996434c75e6590d31b7592434c75e5490d31d7152434c6de6290d31b7986434c6dd6090d319f195434c73f5450d31cf151434c6f76150d31bd185434c75c6550d3197195434c79f6450d31e7d51434c75e5450d31d7151434c79c5450d31c7151434c6dc6250d31f5d85434c6dc6150d31f5185434c6d46150d31b7d81434c67e6510d31b798c434c67e64d49319f593524c67e60d49319f583524c6be6494931af592524c76f5294931db548524c67e64149319f590524c75e4314931d750c524c67e60149319f580524c67e65d09319f597424c67c65d0931cfd53424c73c54d0931b798f424c6dd63d09319f996424c67d65909319f196424c76f5290931db14a424c67f65509319f995424c67c6550931cfd51424c73c5450931b7d8d424c6dc6350931dbd49424c76c5250931bdd85424c6f461509319f994424c67d65109319f194424c6de6310931b758c424c6f66110931bd584424c67e65cc931dbd4a324c76c528c931bd986324c6f5618c931b7d92324c6dd648c931d7d52324c75d548c931b798a324c75f528c931f3d4a324c7cc528c931b7986324c7d6618c931b5986324c7d5618c931b7582324c76f524c931db149324c6f7614c931bd185324c67e650c931f34c8324c6de650c931d7994324c6df640c931b7590324c75f540c931d7550324c6de620c931f3988324c75f520c931f3948324c7cd520c931f3908324c7cd420c931b7984324c6dd600c9319f997414c73f54d0531cf153414c6de63d0531b758f414c67e65905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c67e6510531b798c414c6dd6310531bb988414c6ed6210531ed504414c6fa6010531be580414c7d643cc531f550f314c7d632cc531f50cb314c6f560cc531bb98a314c6ed628c531b7d92314c6dd648c531b798a314c7ce628c531b398a314c7cd628c531f5d46314c6dd608c5319f993504c67d64d4131d790f504c75d43d41319f98b504c67d62d4131ded42504c6bf6454131af191504c6ef6254131bb189504c6be6414131af590504c6ee6214131bb588504c77950141319f990504c73e64141318f990504c67d6414131cf590504c63d64141319f988504c76e62141319b988504c67d6214131db588504c66d6214131d78c8504c75
  | 37 => 0x9fd8950cc67c6254331af99050cc6bd6414331bb98850cc6ed6214331de54050cc6ee62d5231bb58b548c75d63d52319f98b548c76e62d52319b98b548c67d62d5231db58b548c66d62d5231dd987548c67e60d52319f583548c73f54952319f98a548c67d62952319f982548c67d6095231cfd91548c67f62552319f189548c67f60552319f181548c73d5415231bb988548c6ed6215231be980548c6f96015231cf990548c75d63152319f988548c76e62152319b988548c67d6215231db588548c66d6215231dd984548c67e6015231de980548c67a60152319f580548c77960152319e580548c73e54d0e31cf553438c6ee62d0e31bb58b438c6f661d0e31bd587438c73e5450e31cf551438c6f76150e31bd185438c79d4310e31dbd4a528c67e6494a319f592528c67e6094a319f582528c76f5494a31db952528c76d5494a31db152528c76f6494a31db992528c76d6494a31db192528c76f6394a31dbd0e528c76e4394a31db50e528c76c4394a31db986528c76c6194a31dbd82528c76e6094a31db582528c76c6094a319fd91528c67c6454a319fd81528c67c6054a31dbd95528c76f5454a31db951528c76d5454a31db151528c76f6454a31db991528c76d6454a31db191528c76d6354a31dbd0d528c76e4354a31db50d528c76c4354a31db985528c76c6154a31dbd81528c76e6054a31db581528c76c6054a31db548528c67f65d0a319f997428c67d65d0a31b798f428c6dd63d0a31db94b428c76d52d0a319fd96428c67e6590a319f596428c6de6390a31b758e428c76e5290a31db54a428c67f6550a319f595428c67c6550a31db949428c76d5250a31bdd85428c6f46150a319fd94428c67e6510a319f594428c76e5210a31db548428c6f66110a31bd584428c76e52cca31db94a328c76d528ca31bd986328c6f5618ca31db949328c76d524ca31bdd85328c6f4614ca31db548328c7cd320ca31db94b418c76d52d0631cf952418c73d5490631b798e418c6dd6390631db94a418c76d5290631db949418c76d5250631cf950418c73d5410631b798c418c6dd6310631bb988418c6ed6210631db948418c76d5210631ed504418c6fa6010631be580418c76e52cc631db54b318c6dd65cc631d7597318c75f54cc631d7553318c75e52cc631f394b318c74e52cc631f354b318c6f565cc631dd597318c7e652cc631f954b318c6f560cc631bb98b508c6ed62d4231db94b508c76d52d4231db94a508c76d5294231ded42508c67e64942319f592508c67e62942319f58a508c76e5254231db549508c67f64542319f191508c67f62542319f189508c75f3154231af990508c6bd6414231bb988508c6ed6214231db948508c76d5214231de540508c67e62d51319f58b544c67e60d51319f583544c73f5495131bb98a544c6ed629
  | 38 => 0x950107695254041de14950107bb4154041fc90550107b94154041fc50550107b14154041de991501077b6354041de98d50107796354041de18d501077b4354041de90d50107794354041de10d501077b6254041de98950107796254041de189501077b4254041de90950107794254041de109501077b3254041de8c950107793254041de0c9501077a6154041ded05501073b4154041de90550107724154041de50550107394154041dc50550107314154041de10550106de6314041b758c501075e5314041d754c50106ee6214041bb588501076e5214041db54850107b54114041be98050107795014041bb98b54cc6ed62d5331d798f54cc67e62d5331db98b54cc66e62d53319f58b54cc76d62d53319b58b54cc77561d53319f98354cc67d60d5331cfd5254cc6ee6295331bb58a54cc75e63953319f98a54cc76e62953319b98a54cc67d6295331db58a54cc66d62953319f98254cc67d6095331cfd9154cc67f62553319f18954cc67f60553319f18154cc73d5415331cf99054cc75e63153319f98854cc67d6215331dd58454cc67e60153319f58054cc6ee62d0f31bb58b43cc73e5490f31cf55243cc6f66190f31bd58643cc75d6590f31d795243cc79e5490f31e755243cc75c5490f31b798a43cc6de6190f31f598643cc7d56190f31b758243cc6df6550f31d7d9543cc79f6450f31d795143cc75c5450f31b718943cc6dc6150f31b7d8143cc73e5410f31cf55043cc6f66110f31bd58443cc6be64d4b31af59352cc76f5294b319f99252cc67d6494b31d790e52cc75d4394b319f98252cc67d6094b319fd9152cc67c6454b319fd8152cc67c6054b31db54852cc67f65d0b319f99742cc67d65d0b31b798f42cc6dd63d0b31db94b42cc76d52d0b319fd9642cc67e6590b319f59642cc73e5490b31cf55242cc6f66190b31bd58642cc67f6550b319f59542cc67c6550b31b7d8d42cc6dc6350b319fd9442cc67e6510b319f59442cc73e5410b31cf55042cc6de6310b31b758c42cc76e5210b31db54842cc76e52ccb31db54b32cc6f661ccb31bd58732cc6dd658cb31d759632cc6df648cb31b759232cc75f548cb31d755232cc75d528cb31b798632cc6dd608cb31db94832cc76d520cb31f34c832cc6f6610cb31bd58432cc6df640cb31b759032cc75f540cb31d755032cc7ce620cb31f394832cc75d520cb31f354832cc74d520cb31f390832cc7cd420cb31b798432cc7d6610cb31f558432cc6dd600cb31cf95341cc73d54d0731b798f41cc6dd63d0731cf95141cc73d5450731b7d8d41cc6dc6350731b798c41cc6dd6310731bb98841cc6ed6210731ed50441cc6fa6010731be58041cc77b50943319f99250cc67d64943319f98a50cc67d6294331d78ca50cc75c32943319fd9150cc67c6454331d790d50cc75d4354331
  | 39 => 0x67e65cc8419f59732106be64cc841af593321075e53cc841d754f321076e52cc841db54b32106f661cc841bd587321067f658c8419f996321067d658c841af99232106bd648c841d794e321075d538c841db94a321076d528c841bd98632106f5618c8419fd95321067d654c8419f195321075e534c841d754d321076e524c841db549321067f650c8419f994321067d650c841d794c321075d530c841db948321076d520c841f34c8321075e53d0441d754f411076e52d0441db54b411079e53d0441e754f41107ae52d0441eb54b41106bd6490441cf952411075e5390441d754e411076e5290441db54a41106f56490441ad59241107765490441ed95241107d65390441f554e41107e65290441f954a411067f6550441d794d411075d5350441db949411076d5250441afd95411073f65504418fd95411079e5350441e754d41107ae5250441eb54941106bf6150441cf94541106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441f594d41107d55350441edd0d41107b64350441ed50d41107b44350441f994941107e55250441edd0941107b64250441ed50941107b44250441edd9541106b76550441cdd9541107b76350441ed98d41107b56350441ed18d41107b75350441ed94d41107965350441ed54d41107955350441ed14d41107b76250441ed98941107b56250441ed18941107b75250441ed94941107a65250441ed54941107a55250441ed14941107b73250441ed8c941107b53250441ed0c941107b76050441ed98141107b56050441ed18141106de63d4041b758f501075e53d4041d754f50106ee62d4041bb58b501076e52d4041db54b50107b541d4041d794e501075d5394041db94a501076d5294041ed506501077b50940419f98e501067d63940419f98a501067d6294041ded4e501077a5394041f694e501075a5394041de54e50107d95394041d654e50107785394041ded4a501077a5294041fa94a501076a5294041de54a50107e95294041da54a50107785294041eed0650107f24194041ee50650107f14194041ec50650107786494041ded8e501077a6394041de58e50107786394041ded0e501077a4394041de50e50107784394041ded8a501077a6294041de58a50107786294041ded0a501077a4294041de50a50107784294041decca501077a3294041de4ca50107783294041de186501077b4194041de90650107794194041d794d501075d5354041db949501076d5254041ed505501067f63540419f18d501067f62540419f189501073f4154041dd905501073d4154041dd50550107354154041ded95501077b5354041de94d50107da5354041d694d50107795354041f654d50107595354041de14d501077b5254041de94950107ea5254041da94950107795254041fa54
  | 40 => 0x5250941db14942506f76150941bd185425067e65109419f997325067d65cc9419f197325075f53cc941d714f325067e658c9419f596325067c658c941dbd4a325076c528c9419fd95325067e654c9419f195325075f534c941d714d325076f524c941db149325067e650c9419f594325067c650c941af99032506bd640c941f34c832506f6610c941bd58432506f560d0541edd4641506bd60905419f98f505067d63d41419f98b505067d62d4141ded4250506df6354141b718d50506ef6254141bb18950506de6314141b758c50506ee6214141bb588505077950141419f98c505075e63141419798c505067d6314141d758c505065d63141419f988505076e62141419b988505067d6214141db588505066d6214141bb98b53106ed62d4c41be98353106f960d4c41d7d4e531067e6294c419f58a531067e6094c419f582531075c6494c41d7d8a531075e6294c41d758a531075c6294c41d7986531075c6194c41d7d82531075e6094c41d7582531075c6094c419fd89531067c6254c419fd81531067c6054c41d7d95531075e6454c41d7d89531075e6254c41d7589531075c6254c41d7985531075c6154c41d7105531075f6054c41d7981531075d6054c41d718153106de6314c41d754c53106ee6214c41bb58853106fa6014c41be580531075e53d0c41d754f43106ee62d0c41bb58b43106f661d0c41bd587431067d6590c41d754e431067f6550c41d794d431075e5310c41d754c431079d4310c41bd98443106f56110c41b798f52106dd63d4841d794f521075d53d4841be98352106f960d4841d794e521075d5394841dbd4a521067e63948419f58e521067e60948419f582521076f5394841db94e52107ce5394841d394e521076d5394841f354e521074d5394841db14e521076c6494841dbd8e521076e6394841db58e521076c6394841dbd0e521076e4394841db50e521076c4394841db986521076c6194841dbd82521076e6094841db582521076c6094841d794d521075d53548419fd8d521067c63548419fd81521067c6054841dbd95521076f5354841db94d52107ce5354841d394d521076d5354841f354d521074d5354841db14d521076e6454841dbd8d521076e6354841db58d521076c6354841dbd0d521076e4354841db50d521076c4354841db985521076c6154841db105521076f6054841db981521076d6054841db18152106de6314841b758c521075e5314841d754c52106ee6214841db54852106fa6014841be58052106de63d0841b758f421075e53d0841d754f421076e52d0841db54b42106f661d0841bd587421067d6590841d794e421075d5390841db54a421067f6550841d794d421075d5350841db949421075e5310841d754c421076e5210841db54842107ad4210841bd98442106f561108419fd97321
  | 41 => 0xf41d794c43d075d5310f41bd98443d06f56110f41b798f52d06dd63d4b41dbd4a52d067e6394b419f58e52d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d076d5214b41b798f42d06dd63d0b41db94b42d076d52d0b41bd98742d06f561d0b41db94842d076d5210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d076e52ccb41db54b32d06f661ccb41bd58732d067f658cb419f99632d067d658cb41d794e32d075d538cb41bd98632d06f5618cb419fd9532d067d654cb419f19532d067f650cb419f99432d067d650cb41af99032d06bd640cb41d794c32d075d530cb41db94832d076d520cb41f34c832d077b50943419f98e50d067d63943419f98a50d067d62943419fd8d50d067c63543419fd8950d067c6254341b798c50d06dd6314341bb98850d06ed6214341de54050d06ee62d4e41bb58b539075f5394e419f98a539067d6294e419f982539067d6094e419fd89539067c6254e419fd81539067c6054e41d754c53906ee62d0e41bb58b439075e5390e41d754e43906f66190e41bd586439075e5350e41d754d43906f76150e41bd185439079d4310e41b798f52906dd63d4a41dbd4a529067e6394a419f58e529067e6094a419f582529067f6354a419f18d529067f6054a419f181529076d5214a41b798f42906dd63d0a41db94a429076d5290a41bd98642906f56190a41db949429076d5250a41bdd8542906f46150a41eb508429067f65cca419f997329067d65cca41af99332906bd64cca41db94b329076d52cca419fd96329067e658ca419f59632906be648ca41af592329075e538ca41d754e329067f654ca419f595329067c654ca419fd94329067e650ca419f594329075e530ca41d754c329076e520ca41db54832907cd320ca41bd98432906f5610ca41af597419073d65d0641bd597419077565d0641bd583419077b50942419f98e509067d63942419f98a509067d62942419fd8d509067c63542419fd89509067c6254241cfd0550906de6314241b758c50906ee6214241bb58850907795014241bb98b53506ed62d4d419f98b535076e62d4d419b98b535067d62d4d41db58b535066d62d4d419f983535067d60d4d41d7d4e53506ee6294d41bb58a535075d5314d419f988535067d6214d419f980535067d6014d419f99743506ee62d0d41bb58b435075f5390d41d714e43506f66190d41bd586435075f5350d41d714d43506f76150d41bd185435067e6510d41b798f52506dd63d49419f98f525075e63d49419798f525067d63d4941d758f525065d63d49419f983525067d60d4941b798e52506dd6394941dbd4a525076d52149419f98c525067d63149419f980525067d60149419f99742506de63d0941b758f425076f5290941db14a42506f66190941bd586425076f
  | 42 => 0x7552430cb5c5490c32f398a430cadd6290c32f358a430cacd6290c32b7586430cade6090c329fd95430cadf6550c32d7d95430cb9f6450c32d7951430cb5c5450c32b7d89430cbce6250c32f3589430cadf6150c32b7181430ca7f6510c329f594430cb3e5410c32cf550430cade6310c32bb988430caed6210c329f992520ca7d6494832d790e520cb5d43948329f597420cade63d0832b758f420ca7f65908329f596420cb3e5490832cf552420cade6390832b758e420caed6590832db596420ca6d6590832bb592420cb6e5490832eb952420cbad5490832db152420cbce6390832bb58e420cbcd6390832b358e420cb6e5390832f390e420cbcd4390832bb586420caee60908329fd95420caef6550832dbd95420cbaf6450832db951420cb6c5450832bbd8d420cbce6350832f358d420cb6e5350832f390d420cbcd4350832bbd85420caec60508329fd94420ca7e65108329f594420ca7c6510832cf950420cb3d5410832b798c420cadd6310832bb988420cadf64cc832b7593320cbce42cc832f350b320cadd61cc832b7983320cadd638c832d794e320caef648c832bb592320caed638c832b358e320cb6e538c832f394e320cbce438c832f350e320caed618c832bb982320ca7f654c832b7d95320cb5f654c83297d95320cadf644c832b7591320cadf624c832d7949320cbcf424c832f3909320cbcd424c832f3109320cadf614c832b7181320caef654c832dbd95320ca6f654c832bbd91320caed644c832bbd8d320cbcf634c832db94d320cbce534c832f3d0d320cbce434c832f350d320cbcc434c832bbd85320caec604c832f3d95320cacf654c832d3d95320cbcf644c832b3d91320cbce644c832f3591320cacd644c832f3191320cbcf544c832f3951320cbcd544c832f3151320cbcf614c832b3d85320cbce614c832f3585320cbcc614c832f3d81320cbce604c832f3581320cbcc604c832b3181320cbcd32d4432f34ca510cb7751944329f992510ca7d64944329f982510ca7d6094432f34c9510ca7f64544329f191510cb5e4354432d750d510cb6e4254432db509510ca7f60544329f181510cabe6414432af590510cbcd3214432dd544510cafa6014432be580510cbcd32d4032f34ca500cb7b50940329f992500ca7d64940329f986500ca7d6194032f34c9500ca7f64540329f191500cb5e4354032d750d500cb6e4254032db509500cb5f3254032db8c9500cb5d3254032db4c9500cb4d32540329fd85500ca7c6154032af990500cabd6414032f34c8500caf66114032bd584500cb795014032bb98b53d06ed62d4f41d7d4e53d067e6294f419f58a53d067e6094f419f58253d067f6254f419f18953d067f6054f419f18153d075d5314f41d794f43d075d53d0f41bb98b43d06ed62d0f41bd98743d06f561d0
  | 43 => 0x428cb3e5490a32cf552428cade6390a32b758e428cb3e5410a32cf550428cade6310a32b758c428cbad4210a32b7597328cb5d65cca32b7d93328cadd64cca32b7587328cade60cca32bb597328cb6d65cca32dbd53328cb6d54cca32bb583328cabe64d4632af593518cb7751946329f992518ca7d64946329f982518ca7d60946329fd91518ca7c6454632d790d518cb5d4354632dbcc9518ca7f60546329f181518cb755114632ded42508ca7e64942329f592508cb6f32942329f986508ca7d61942329fd91508ca7c6454232d790d508cb5d4354232d7cc9508ca7f61542329f185508cabe6414232af590508caf66114232bd584508cb7950142329f987544ca7d61d51329f983544ca7d60d5132cfd52544ca7e64951329f58e544cb5d63951329758e544ca7d6295132db58a544ca6d62951329f986544ca7d61951329f982544ca7d6095132cfd91544ca7f6355132d7d8d544ca7f6255132dbd89544ca7f61551329f185544ca7f60551329f181544ca7e6515132cf550544cb3e64151329f984544ca7d61151329f980544ca7d60151329f997434cb3f54d0d32cf153434caee62d0d32bb58b434ca7e6590d329f195434cb3f5450d32cf151434caef6250d32bb189434ca7e6510d32e750c434ca7e65d0932cfd53424cb3c54d0932b798f424cadd63d09329f996424ca7f65509329f595424ca7c6550932cfd51424cb3c5450932b7d8d424cadc63509329f994424cbad4210932dbd53324cb6d54cc932bb583324cb5f548c932d7552324cbcf528c932b7582324ca7e64d45329f593514cb6f32d4532d78cb514ca7e60d45329f583514cb775194532dd544514ca7e64145329f590514ca7e60145329f580514ca7e64d41329f593504ca7e61d41329f587504cb7b5094132af990504cabd6414132bd984504caf56114132de540504ca7e6414132cf990504ca3e64141329f590504cb3d64141328f590504cb6f3214132d78c8504ca7e6114132dd984504ca7661141329f584504cb7561141329d584504ca7e63d5032d798f540ca7e62d5032db98b540ca7e61d50329f587540ca7e60d50329f583540ca7d6595032cfd52540cb5e6395032db98a540ca7e61950329f586540ca7e60950329f582540cb3f64550329fd85540ca7c61550329fd81540ca7c6055032cf550540caf66115032bd584540cafa6015032be580540ca7e6415032cf990540ca7e6315032d798c540ca7e6215032db988540ca7e6115032dd984540ca7661150329f584540cb7561150329d584540ca7e6015032de980540ca7a60150329f580540cb7960150329e580540ca7e6494c329f592530ca7d65d0c32bb58b430ca7f6590c329f596430cb3e5490c32cf552430caee6290c32bb58a430cb5d6590c3297596430cadd6490c32d7952430cb9e5490c32e
  | 44 => 0xb9d63d0842af5924210b3e5490842bb5924210b6e5490842eb9524210b6e53908429fd954210abf6550842cfd954210a3f6550842afd894210b3e5250842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210b6e5350842ebd0d4210bad4350842ddd465110a7e63944429f58e5110a7e60944429f5825110a7f63544429f18d5110b6e4254442db5095110a7f60544429f1815110ade6314442b758c5110b755114442be9805110af96014442ded425010a7e63940429f58e5010a7e61940429f5865010a7f63540429f18d5010b3f4254042db9095010b3d4254042db5095010a7f61540429f1855010ade6314042b758c5010af66114042bd5845010b795014042bd98754ccaf561d5332d798f54ccb6d62d53329f98754ccb7661d53329d98754cca7d61d5332dd58754cca7561d53329f98354cca7d60d5332cfd5254ccb6d62953329f98654cca7d61953329f98254cca7d6095332cfd9154cca7f61553329f18554cca7f60553329f18154ccb3d5415332cf99054ccb5e6315332db58854cca7e61153329f58454cca7e60153329f58054ccaee62d0f32cf95243ccb3d5490f32bb98a43ccaed6290f32cf95043ccb3d5410f32e750c43ccaee6210f32bb58843ccb3e54d0b32cf55342ccade63d0b32b758f42ccaed6590b32db59642ccb6e5490b32db15242ccaed6390b32bb58642ccaee6090b32cf95142ccb3d5450b32b7d8d42ccadc6350b32bbd9542ccb6f6550b32ebd9142ccb6e5450b32eb95142ccb2e5450b32eb55142ccb6c5450b32bbd8d42ccbcf6350b32f318d42ccaef6150b32bb18142ccabe64d4732af59351ccb7751947329f99251cca7d64947329f98251cca7d60947329fd9151cca7c6454732db90951ccb6d42547329fd8151cca7c6054732dd54451ccb7b50943329f99250cca7d64943329f98650cca7d61943329fd9150cca7c6454332db90950ccb6d42543329fd8550cca7c6154332af99050ccabd6414332bd98450ccaf56114332de54050ccaf661d5232bd587548cb5d63d5232db98b548ca7e61d5232dd987548ca7661d52329f587548cb7561d52329d587548ca7e60d52329f583548cb3f5495232d758e548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cf550548cb3e6415232d758c548cb6e62152329f984548ca7d61152329f980548ca7d6015232cf953438cb3d54d0e32bb98b438caed62d0e32b7596438cb5d6590e32d7952438cb5c5490e32b758a438cadd6190e32b7982438cb3e5450e32cf551438caef6250e32bb189438cb5f6550e32e7d91438cb5e5450e32e7951438cb1e5450e32e7551438cb5c5450e32b7d89438cbcf6250e32f3189438cadf6150e32b7181438cade63d0a32b758f
  | 45 => 0x3d4742d794e51d0b5d5394742ddd4651d0a7e63947429f58e51d0a7e60947429f58251d0b5e5354742d754d51d0a7f63547429f18d51d0a7f60547429f18151d0ade6314742b758c51d0b5e5314742d754c51d0b755114742be98051d0af96014742b798f50d0add63d4342d794f50d0b5d53d4342d794e50d0b5d5394342ded4250d0a7e63943429f58e50d0a7e61943429f58650d0b5e5354342d754d50d0a7f63543429f18d50d0a7f61543429f18550d0ade6314342b758c50d0b5e5314342d754c50d0af66114342bd58450d0b795014342bd9875390af561d4e42d7d4e5390a7e6194e429f5865390a7e6094e429f5825390b6c6254e429fd855390a7c6154e429fd815390a7c6054e42d754c5390aed62d0e42d794e4390b5d5390e42bb98a4390aed6290e42d794d4390b5d5350e42bbd894390aec6250e42b798f4290add63d0a42af5974290b3d65d0a42e798f4290b9d63d0a42bb5974290b6d65d0a42bb98f4290bce63d0a42b398f4290bcd63d0a42bb5874290aed60d0a42b798f5190add63d4642b798e5190add6394642ddd465190a7e6394642d798e5190a5e63946429f58e5190b5d63946429758e5190a7e60946429f5825190a7f63546429f18d5190a7f60546429f1815190b755114642ded425090a7e63942429f58e5090a7e61942429f5865090a7f63542429f18d5090b3f42542429fd855090a7c6154242b798c5090add6314242bd9845090af56114242de5405090b6d62d4d429f9875350a7d61d4d429f9835350a7d60d4d42d7d4e5350af66194d42bd5865350b5d5314d429f9845350a7d6114d429f9805350a7d6014d429f9974350aee62d0d42d7d4e4350b5c5390d42bb98a4350aed6290d42d7d4d4350b5c5350d42bbd894350aec6250d429f9944350b9d4310d42b798f4250add63d0942bb98f4250bce63d0942b398f4250bcd63d0942bb5874250aed60d0942ebd4a4250abd60909429f98f5150a7d63d45429f9835150a7d60d4542b798e5150add6394542ddd465150b7551145429f98c5150a7d63145429f9805150a7d60145429f98f5050a7d63d41429f9875050a7d61d4142ded425050adf6354142b718d5050af76154142bd1855050ade6314142b758c5050af66114142bd5845050b7950141429f98c5050b5e63141429798c5050a7d6314142d758c5050a5d63141429f9845050b7661141429d9845050a7d6114142dd5845050a756114142d798e5410b5d6395042d7d4e5310a7e6194c429f5865310a7e6094c429f5825310a7f6154c429f1855310a7f6054c429f1815310b5d5314c42bd9845310af56114c42be9805310af96014c42d794f4310b5d53d0c42bb98b4310aed62d0c429f5964310a7f6550c42d794c4310b5d5310c42bb9884310aed6210c42b798f4210add63d0842e798f4210
  | 46 => 0x43db5485290eee62d4643bb58b5190eee6294643bb58a5190f7751946439f98a5190f6e62946439b98a5190e7d6294643db58a5190e6d62946439f9825190e7d60946439fd895190e7c62546439fd815190e7c6054643dd5445190f7b50942439f98a5090e7d62942439f9865090e7d6194243cfd0d5090e7f62542439f1895090e7f61542439f1855090eee6214243bb5885090ef66114243bd5845090f795014243bb98b4350eed62d0d43b798b4350fce62d0d43b398b4350fcd62d0d43b75874350edd60d0d43e7d4e4350ebd6090d439f9875250e7d61d49439f9835250e7d60d4943dbd4a5250ef66194943bd5865250f6d52149439f9845250e7d61149439f9805250e7d60149439f98b5150e7d62d45439f9835150e7d60d4543bb98a5150eed6294543ddd465150f7551145439f9885150e7d62145439f9805150e7d60145439f98b5050e7d62d41439f9875050e7d61d4143ded425050eef6254143bb1895050ef76154143bd1855050eee6214143bb5885050ef66114143bd5845050f7950141439f9885050f6e62141439b9885050e7d6214143db5885050e6d62141439f9845050f7661141439d9845050e7d6114143dd5845050e756114143db98a5410f6d6295043bb98b4310eed62d0c43eb98b4310fad62d0c43af5924310f3e5490c43b75924310f5e5490c43e79524310e7f6550c43afd954310f3f6550c438fd954310ebf6350c43cf94d4310edf6550c43d7d954310e5f6550c43b7d914310f9f6450c43d79514310f9e5450c43dbd4a5210f5e4394843d750e5210e7e61948439f5865210e7e60948439f5825210e7f61548439f1855210e7f60548439f1815210f6d5214843bd9845210ef56114843be9805210ef96014843ddd465110e7e62944439f58a5110e7e60944439f5825110f5e4354443d750d5110e7f62544439f1895110e7f60544439f1815110eee6214443bb5885110f755114443be9805110ef96014443ded425010e7e62940439f58a5010e7e61940439f5865010f3f4354043d790d5010f3d4354043d750d5010e7f62540439f1895010e7f61540439f1855010eee6214043bb5885010ef66114043bd5845010f795014043d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0b5c6494f42d7d8a53d0b5d6294f42d7d8653d0b5e6194f42d758653d0b5c6194f42d7d8253d0b5e6094f42d758253d0b5c6094f429fd8553d0a7c6154f429fd8153d0a7c6054f42d7d9553d0b5e6454f42d7d8953d0b5d6254f42d7d8553d0b5e6154f42d758553d0b5c6154f42d7d8153d0b5e6054f42d758153d0b5c6054f42d754c53d0b5e53d0f42d754f43d0aee62d0f42bb58b43d0b5d5390f42d794d43d0b5e5310f42d754c43d0b9d4310f42bb98843d0aed6210f42b798f51d0add63d4742d794f51d0b5d5
  | 47 => 0x4401100000030024002007c0020000014000c03300180210064008000c0030058000001c002001c003006c006000800d000001400000000004005001400100000010004013001c007007400500040000000013000400100040060000000003400a000c0020034018006001100380030004005000800100040020008000000000000000070008002000c0000004006000003b002c00001f00040008000001400001ec0010060004001002e000001a0008005000401400080000000035005c0000020001000400d000c007000001a000000b001c0020038001000400b006c00a002c00100700140008000000000a00bc00400ac002000000401f0023000c0080010000001800700040000000000000000000a8025000003c0010000001800a0040002003000700000050008011001c0000040001000c016004801b00000070010003003800c0010075007c01500040110004002000802d001000200000040008009004c01600680160050001002400000000090004020008401b0014000000800900100000014002000800000c00040038016001c0030000000001c00d00e4002001c03f0018002000400c0020000000c001001c003001c0050008015000c002002400000000000000019005400000100000014004002800b0034001001800d0000007000c001003000100000030198004006000f0000007000c0030044000000000e000000d001c0070008000004c0120000000dbd4a52d0e7e6194b439f58652d0e7e6094b439f58252d0f6c6494b43dbd8e52d0f6f6194b43db98652d0f6d6194b43db18652d0f6f6094b43db98252d0f6d6094b43db18252d0e7f6154b439f18552d0e7f6054b439f18152d0f6f6554b43db99152d0f6d6354b43dbd8552d0f6e6154b43db58552d0f6c6154b43dbd8152d0f6e6054b43db58152d0f6c6054b43db54852d0eee62d4743bb58b51d0f6e52d4743db54b51d0f6e5294743db54a51d0f7751947439f98a51d0e7d62947439f98251d0e7d6094743db94951d0f6d52547439fd8951d0e7c62547439fd8151d0e7c6054743bb98851d0eed6214743db94851d0f6d5214743dd54451d0efa6014743be58051d0eee62d4343bb58b50d0f6e52d4343db54b50d0f6e5294343db54a50d0f7b50943439f98a50d0e7d62943439f98650d0e7d6194343db94950d0f6d52543439fd8950d0e7c62543439fd8550d0e7c6154343bb98850d0eed6214343db94850d0f6d5214343bd98450d0ef56114343de54050d0eee62d0e43bb58b4390ebd65d0e43cf5974390fae62d0e43eb58b4390edd65d0e43d75974390ede62d0e43f398b4390ece62d0e43f358b4390edd61d0e43b75834390ef661d4a43bd5875290f6f5294a439f9865290e7d6194a439f9825290e7d6094a439fd855290e7c6154a439fd815290e7c6054a
  | 48 => 0x18000c0030008000000800b00040050040002002400e003003a002c00000180000048015000c00100040060000030000c002005401400180060010030000000d000400e000c000004c0000030001003c000003800e0014002002000d001000100b000200d4000000000200800030008005001400100100100008002004400b00000120000000023c013000402e000c0000008000002000400000010010001004c000000001800040000000000002800800100000054000000000f000800f0074002000c00100000000020053002c0040000004000c0000048000001c0020138008000c0000008006000000d000401a00000010000002000000a002000400000000010001002802100100000000000002c0000000000000c00000000030084039000400100080210000004000000000980080010016000000a00200000000000000c008000800000600200008002002400000100000018000001000100640040064002000c011001c01b00200180020004004800201680000010013001002100840070000017001c00000d400000780000010000001000c000400100140150000000001000301300000004003001800000000060000000000000b0000027002c0020054001008c006004000700480020010008000001b0020002000400100e0009002800800400080014000000401100000170010003000400c001000700600030000012007c00400700000010002001000000400010000001001800c000400100040020004010000c00e00400030034014002001e0000009009800100040040034000001800b0018001000000a0020005000400400800000014001001802000a800f003400300000020008000002000900000040010025000c00000000050038001003c0180000001000000000580080010003004000f0038003000001b0058009000c03d00280010000003006800200240000024049000800000000000018006001400300000040020003006c000006001a002c00800040050004000008c012000000b006c000000800000040360028000000c0090008000000c008000401d00700010000000000000700040000004012000c005002c010002001900100040080003002402e006000e00c4019002000a000000000c000800b0003016001500100060000001004c0000014002000400000000060078001001401300b8061006802e000800c0000006000c0000054005000c00e0010001000c02b00000190000002003c000001400900100030098004001000d000800000300000024000000800000080090008000000000c003c01f002402501bc00000b8019000400000100000000040000c0030004001001c004006400300e8001008c00300300070018012001000b008c00000600040038001000c06f00c000600000010004008000001800
  | 49 => 0x5802b0018007002000c002c002000002a00000020000009000c00e001c000000003d0000001001000f0004002001c004000005d000000800280040000001001403a000c003006800000000080004008007c002000000000180050008031005800100000030008000000c02300b400000080090040006007000d0030007001800d000c01800000010220013000001b008400600c4019002400000240320000034002000800a0000000006f00080230010000001000c000c008002800800040000014010003c00a00d0000000c000001c002001000000580090014001001c05b001800000b402800100010004000000401d000000300280300008003000000500000020004009000800000080020018004006400f000000000040000020010000400b000001e0028001000800000840060020004002400400040260054013003c00b001400a00040020058032000c01601fc00000000010004004000000100100010014008015400500f4000002000000140000004009001800a000c00100000010054019001800100a00120000000007400200b4001001c001000800c003800400000020030001000000200100000020000000c0050018002001400000040000008005001400b009400500000010008000000400300100000000009004000700140070000012001c00000000070008001001400000000000004000000400000b8006002000000100040014003003c00e002c004000800c00000020014003000c00000a000000000300034000000400e0010005000c00400300c300740080044003000c001004c00000100020024006001001d0018000000400000dc0010010024007801c00100050000009001c00000480130038000000003100000050010000000c00c0020000003c00100280260008011000000500a001d01c0006003c0060010001006000b000c00e0000003000000b0000000004c01c001400000000010000016000000a00e400700040050004001000003300080020008065001c007004800300000000000000001c000000c01c0030000001c016003c00d003400000080300030005002c002006c004000c007000003d0000002000c00c002000000500030048016001000000000050008005011c00100b00090078003000000b002001a004400b001000500000020040003002c000000401500340000024000000000e004c012000400200200250008002000c000008800000180230014035001404200100020000003000c001003800b000802202a400700080310048001000000e0028000004400400040520000025005000200080000008000000002c0000006004c00500a000200040000000006000400000180030014002009c0010008014005402200000180004000002c00b000400201ec008000800000000160004004000c0
  | 50 => 0xc0010008001002c000004802600000010004002000000000580060004000002804400000000008013006800000180060040004004c0000024008000400100000020008002006800a0000002000c0020000000017400000340000028000000400000900a80080014001c014004c00d000c0000000005001000300200090018000004800200000160028000000000600e800000080120000006000c0160024000002002700080010000000003001b000002b0008001002402b0000017003c000000400000180000004064000000e002000100040000014001000400d002800e008000200080000004009000000a0000005005c00100e0003001400b000c000004400700f400500a00120000004001000000000070000000002c002000000200080160108008005000000280000008005000000300040590020000000401c000000b00bc00d00000150010002002800800000010000013001c02600ac012000c0000004004000000300100110010003006c00600100000000002003c000001c000005c000000400b00000170014000003000000000020014009001401800080020030005000800400040090000001004c012003c01100000060044000000000a003c001000008e003400200a000500040140054012000000500640070000003001c00100ec0b0009400200040020018001000c002003400b002400a002400d004c00d000000200300220004030000400300440170000019000c0000008007004c00200000010008002000400600380000000000000000b000802d0000002002800000980010000001003c01e00400000008004003c000002400a0000009000c00000180330004000001800b0024031007800000080010024000002800000b00110010000000000700000000000000000400200000040000004000c01400000000088006003800b0038007002c00e002c042001800000100010000002001400000140000004000000c001003c0060010001004c0170060001000000f0000000002800200000030014009000800000d400e000000000740040040000000c0070010000000000d000400b0010003000001400c40170000003001803100340210038004001c00d00540000008000003001d002400d0004035000000100040010004001001c00000040000028000001c0030008006001400800180010004003000c00c000800400700100018005001c00400000040054000000000c0004001000400f005806f0008014003801300b00000038001000400c000001200200030028014002400900a000700640010000000004800000180390028023000c00200200180050002005800100000030084008004408b004402e00080050000002001c01d002002d0044000004401c00b40000030000007001f0000029003c000000c0810
  | 51 => 0x2402a001c01c001400100ac03f0008008001c00400e001d001002e000004300340060010010002000000000030024000004c02200940000010025002400700d00000000009001400300200010020004000c000002800000640010008017000401600000080044000009c0040000001001c0000004000002c0000010012002802a000000c0000018000c00100300040000011002c03a00040060000009003c0020000009001000a00080320000000003c0000000011006c000001c000002c004000000c00040120008000000c0050160000001800200500000074000001c00a0000003000000700540000000002000800b000c00300000b20000000000001b000000f00180080068004004c001001400000000000000002001000000000040000003000c03a001c00700040010014059000800e0004001002c000001c0000080018000c003004c00400080010000001008c00300d4063014c000000000000080010004002000001c001c000000003f000000d00040060000014001000c005400a006000600040100000005001c002000401200080060064002007c00200000000070010006c01200040000014002000007700040000000001000000000300130004000000000c012800000040000034007000c007000c000000000401d4000000800d0000008001401500040020124002006800301200070000000001c02e0008003000c00300040000000002000c005005c00c0018011000401d00980000050005000801f00b801d000002b000c0040008007001008301f400b02c0000003400a00ec06700080000004008001c01e00100000020007000c003003c0000024000000800100000290148014001c00000140290000019000400100380040034000002c0060014005000000d003001c000402f0000000004c002001400c003000c0000009000000100040020014006000000800040000004006004002e000001a001800b001400100000000004000002c002001800c002000300200020008000001400a00040040000007005c007000c00b00000060010000004c002003400100100040018009000000300140040004001005c03b000800b00000000004000000800000000000000013018000d002c0030004001002000e001400f02e00000014000000000000040020000006000000600480010000000002000a004400c00040000000012002c00c0018000001c0850000014000000c002c0050008004000c000000c00200000030004014003001700900010024000004800000280090000004002802900000000000010000c00900000010184000000000000b802c00080030050017000c0060008012001c000004c00300e0005009001600e40010010021000401f00240000000002001c000002000c00000630008002002c00300000080008
  | 52 => 0x100040030000005000001e000400000040070000033003004b006c0330068000002c00400780010080001000c00000240070010004001400b00280000004032004800300000000010004001400100000060008000005000b0000000000000800140020004004000c004005c0020000001000003000240040000011001c00100540000000005006800600700010008000000000100b80090010004002801d00180050030003000000200200000000000017c0000010000000401100bc00c000c0030000040005001e004c0000000004006800f0030001000000400800030004000000c008003c002001c00e0004020012800000000020000000008c006001801100580000008017003c01c005c00200180010000007001400300100170010003001000e001c00d007c000000c0000020001000000000240000004006001c00e006800300a4003000000c003402c004800c002001e0000004000802d0008000005c00d00040020014000005800400200000018009006c013008000c00000000008000005000d002c00300c401f0000005004802100180000004008005c000000c0030050009000400000000130084000002400200f4003004c01c00000010040000000000500000000028001000c005002800000300000000000004800000140000008000003c001000400500280010020000000c04400000040034006000000400000010008004001c0080248004000000000040030000001004800000000000010004001c001013c02c000000402d0000001c003003000600c400f002800e0000012007400d000404c000400500280160000007002c02a0018001001800c000000000040240000003000800f001c00700380070030003006c01900000020034000002000000040020000005000c0050030004001000b0010001005c002001c004000400200500000000000001c000000001d000000000040150020004002c00300080030014007004000600000090000004001400300a400b00080000000000001c0050014000001c0010038004000000100480010000000000000400140020008002000000000100050000002005c0170014000001c00000000050000004004c00400200000010004002400d001400f0014000000c0020000004006c000000000000000000008000000000b003c01b000800c0000000000c0030024004002c0090084006000000000000040104001001802800080020034003002c0000000023001000000240010040000000401d007400100600260084003000800600080010028007000c0000098003007000a00080000004000001c0090040008000401a000404800000310020053000800400180000124001019c001000000100080150000000001c002002403500a000800b000200a4000002001700000060000000
  | 53 => 0xf40000b3836b8149cca880000d82240c68f800020ba82107d827910d6c1994000000010e47ed400000004b2666f45cb22743af8000000027a108d6608865a800035ce771800022c91bee00003e705a0000010d0bac80002c2e97f4a640a05000000013620f99475688849fb00000c2a7a1c9b100eb43f054f466c0000000081c8890941c000072100d58f663eb227580001a1826604dc400016e0000000012bc9c05073a567921a04dc197667b12c285e400002c713c20d3d25a065641ef83651b069ba03a911a826c244dc8e28f15348a000000005ab10985d8509900003af60f949b8232625dc19301d49b2400005d449f3221607f01a54abf89db15e892381ad869f2c1c0af46908efc1308483061692382e1c9ebc548943b475c6284780a0fb1c227e94a2b0c9a1a0c2ed81ee80c73ca06f20c7d18f647d20d3d1de9ab105d097451e68000000096d88bd14ed0000730400025f200002a94c690639000072f427a0000418a4204afc8a77261057a4b3008032d9e92d800a043b00006370c2b00022f8052dc7e0a7b83eb66f540001bdd208052e80a086a54eb484d43c699c74e580d192e586883ed68ea44050df6369008cc0000f363f66313c00000003e763d3497e96d64f049760000165942d03030eda862514b423611800c8f11545c282e3095c22be076c47a27772c1876784a095861ff42d9831d07cf160a39d8000039322f8000000000001a545fc40000000000019f444f978a1a24959c5c19ace112000000000cd64958866929f25ec48b44a6ce4085ef30e00a4866800003db85b0466a939623aa64681988556082400005ff07ef30508cd807b9a9e11f698e43d3119d3ff64e7ca960000000000000001aa21e92372003c1b1026c882f1000a0820bdc9e20a2b800029980000c17a5be4f500000000000000000614ad8a7e44a322a8435800f90eb4479055711561056034d0c580002a8006c8744a17b000000a00040058005008c001000000300e00040000049026c00000340010030007000000b00100000008002002c00300b0000002c002011c00b0024000001000600340220004010000c004004800200d00010028015000000c000005a000800c003000000140030010000000000100440000008017001000c000400b005c001003c0000004000000000d0004002000000b0024010003403100040060000004001c0060040000005800c0008002000400200000220008000000807600280350068000000002800100090004000000c02400040000044000004c004000002600040060000001000000100040010004000001401e000c0020008005008000000080010010000000800400340020010001000800a0008006003c003000800a0010000000000200800110000008002000400140020020004001c01e01440010038000000
  | 54 => 0x2a200000d6b078900000000be70000219000002bda6952df80000000003e4e426df00001f7300003a1400027862e107ffc0000000350c0000afb1dab14e6952c080869a14546d3830b91780000534c0000000000046bcc8a83c5000076b02f31e6f4e0c27c01b39a342fbe7f091a10000357000007629bbe1f2e699cfc59da70f0e3f6079ca4112ef80000000000000007460f3501dd2f24040c13f80002fcc95d8f43024a4c2c8f693eca2150b642c28006992d27c0070800021151cbe20b13e29ce44222435c000023623f22330cbba01e2dd23098e0221a84aa0000069e072b3438170c17f1598230e3efc2a1218f341e84c442200000000395cbfb000017d81d40cae8000000070740000000399833b91aaa3f11db0605c0e927380000283400014ae000000009151ee10c440000cd999ab2c3c2e886d085772bdc72e0775000000006f6cd54a781186a72d8b280196165e93fc0001c78378c602c333141921fc0000000009a42560828f2c0b46147c2a4829ca09400009ceccd300002ce820d02d899fe25e051010df09d7448c7c1074e8019000000000000c20269a273ccbc247533dc6e453649cab45e60000b4e1de13f92330c000252e2f6c7a692b7984f142078dc88c1faa125c954882b132b48bc42accb00ef8191a8064bba8d4305700078bcb84fe28b0000000009dc03941de000011ed371682412eb965202aa27443bb00002ec48d602c8875e4a0600009409e8b455684340001b6e46249ec00001605000089208b723784c5c11e06c8059e26663534000093a4ab80000c8c1921161c1178a0594ab3a6e9d400319ffd3b9870ac42a07b00b4617f4aa720d1203a000000022db00002ad4d0224cd000000000000000290c41d89f1193d00009ab4718000033521f14ee983ce15c20714c4e8fc408b09f30e78178f26a874100af15cf2996971cbfc8a5b298e9778d35800000000000c5182190a2c9ae93530000491a3600e4f000000002478a8393b100003380bac1acb4a408124f3e843c00000000379135c19e62e1405c25fc47f2013d339037326540580e69000003a210bcc6881c100001ee82cc8000056200004ba228e405e346d03ca11c3aae8714ca20d4527b62738c698f65026493bc7e311040e4c7ae40001c5e15f08d3089f8e2c12402b44a6d0c0a4a347b48e359be03d181384ca6a2021a5e0ddd33d0209002079f02f011d73b160000f068f8b3eda7c18276000000008b806bb8417016c062453aa7c408e813c470b078e24b4941525f80d700008b94526000000008e080000128388c000000010e126208274a2500004aea3a0c55b9d613b5c8b1d1ae1a96370e614825e17a600008a943e4023237e623a4f44a4a448ca021c3ff86501a643bdcd4d223d226491ac0000000385e00000000000000061e0c7180001b1e43
  | 55 => 0xdacd13a4720000751032f000000007c380001e76130c8ba400012e43b50407d36190612a744b448be8bd4463e01243b114540000000135b13532dda68e4d8e8b784c9445f8dad8000494e000000000003ec24764b5b800043388b7892b114e37542e18cdb81d747d6471026c1a853bee64d800000004f8c65e8fe880001bde7f209e78000060c5ad8499004e4de63068d52a7f906e4855d29093dc0e18318071fa341194e7d4c0bb8000000054c0d1a8a7b18ae512c5ba8e7523360e7c7e7091f3e78000065900000000839c0001a8c3f482c20ebd000009b6489c25123480000000080a042e000000010c20cc400009d90f2395cd18ec3e94ad0219614ae73a8c511064365c63d4e2a8b6f4c663cc003a0cde1208879c91a10cd395e6a3c10f89c2207c45710c70f0a0b9e9dd05550925146c429d1ab04ca41824acd3932364128e421824b10ad1a2a6e881b31a644d007af5350a58a2c8e306437482f61a2048d8e128b884ec686fd1a30f6c07729bf8b2b8c561aa26dbcb1e093748840f4cf1802f31928494520003ff42fa493c35d12be4cb6128135c20854c700b9c6391dd24254447c000056b094e8548ba3a1c72182000120680001464897923d22493a4a00000000fc71fa694f4000000018c8051400001304ce21eed017055a3d78659012b12d4498c3d0c0eaa7a504569d74005014f41a47b2c2a6a5b903066168628247e337615000000000448601b8f21800045f62aac1f98f8c4f327c253891bf82a160000d630af008be19dc0000db90000000016917e400000d389c41f8a000072a8f940d2d28240000807099a4c4600000001b18269c9ae400000004f86000021508231bd29cbc3f1000045663cd0f7600002b206250c5a800042808048673038f34ae44303f50dd22d0889093211fb239b22fc5204a34a19541d181928ec0118063f01e5816844da54cd1cc1c97400c6fa105014974d6887bc70815b02c142731309940024e844d8da8956d3b4691fcf13920121d802480000000465044a80001963428618dc0000000169400006558fab1b78171422b186f06ac81f41b4158a2dca49340001ae51b2a0000bb5816a0000106c5b18e994f2413311e2134f473442c000002f500000000d8f000047263424d6014c00d140d206a0864800002c9c7daa4930000987896d8f7044d270487950f1c0e3c83307f41f161ef235c436406ff03960c30e5f9e0600008fd4b97104f3012807537a0370000089fd0191b7d3fd8258826303c801d029e8fb806d243fe9c8c5f30bac0bea1b140dc871105028cb000006aa00004a4939f93be4774939400001ef4cc862a80789aa709ee000114d0f1f000000008f6244800003ae80570dad40880000000011b0f421cb8a5400001f04000135e800000000cf1149183f1a4c78a400014ee000063e120b00
  | 56 => 0x65324c013b800024153e0e88c4000158f0664630ce66a7151bca73ec00001e43502723c00015f73c5e939902fa4894cba1980f2122da2eba52e0f9f9e8d150827cc10624ce2d9a9f9854d9fd41fd63df01640d4f46d85a6d07404a928fe6c143ce8aef4d623670000000044a849e4d102724220680d800021e62e126fc0a061601000088400a1a0311770965800011a900009a3ce070da0000058980000e3c20d6000000000000a608ff93dd1537000020a0f880763000000007c408de49648654e7c19c219e2277c000236346d605cc000102c4598000058f800023b49bc8000000042be163400000004b740ab4f688c331e4800002d80297000074344f7826a2748000138e813c16584e744e48000010007a8fcaa2f22fba097d02ba39d20144a44d2a13f138d2560875914d040d409a50711da236509198a82872239ea18805bf06e604c27a3c00025c92a486780c36212f4eb0291c70f245200000000cd80082200e90885f8000028e096c400010f11dda5fe860886d527e800011228e6f2e6800000001380000012940001a093d061ec41f11f4c22e2000103b05203dee20483b3893900005b5c00026af1de0000103fa507280251303dca06f0e66446c0000c1b24b23dfc3e1089a4b5c928cc660e5217b429801b78aa608e06c98ca71600328498b0b82869c00000000000000021645ed447c80004cac973c23f8c2740b60000ace1c4508322cd44170000000005247aaa79c13aa089ccc11dc20d262b39223259e000089c44309916144664500c1000038b4000000000000000952800022ff0000000000000004562004856b8732343c0000f88827500000000ba9800025ba0741067800000009fdcf269cf200002e44000104900000000dd7800000000000cf11f87434673611a991b0000065490a390a43dfa1ea80328fe3000000005159e21327e04e06cc80b50000000c000198432f281a0e5808d60ee4663d2220edc36c68740000055502a60324126932734cc32e4d6f18b91d9e4e805ab9a37061452c4fe723061f963e24e818e820abe618c30493fb35226798c62022e30322ad885a07d04b60048d11710730a0410a0b33953144d02abd0448ac11b8e9ef887a05f20ac26cc867e829a37c84bbc4c986f72d906820be4896e2c3801152cd0a8f0d6e044cf04a37b3a5847f0e5706762c6c9f7cd8ca370074486c8d2219e41b9e8ec0a7111c92fd62764b2ea06440343934a4ea41e390e67602d1215413a00454c87907b457c6410e1725ce4b422ecccfe846307d02f9cecb01fc4bca11e8a21915b00006b48cb388261a442524d01000000000000e6d0b562cc40000e5e27d14d4e95a4ec182471fe4672caa6996a447094d488a27301b1c7ef4340175a00000000633058500000000d8b02fa22e4379124393954bfe4b04c4480004efe3
  | 57 => 0x5becfb025413af00fec3ff08f82c06131537386fc2f34316c78425f31c5c8dbc64483ac01120060046946c4452751c51821e5410e464c6b4a0d0165a46fd077023a4ca62e609340d8747127f1c3da8de2400802182b020304eda5bb8cc584243e0200ccf0e8dba42d893c423b8dfe0b4215f400023d115b6617c7c800353a6200013a1050114386b80e9c8c0917ba00011dba4dd00008eb427200000ba600005db9ee53ad000010e48744075a085d3dc9ac2071000013da9c8a3c0e68a41bf83e119da133400020450e1400007f200ea000000013c69f3a0a744e3803e981c02c8857883a0a1e30462b8800007d50000000000001bf13a617a06861595486e0000157a6e216f600909e9227e2aa25bc4aa3800033a20000b50201447707d00ae6042600000a089b1800037c63118e77935715989360207961932a619a4c3320df3c562a581ca045536141fd520e0a722d4865c91590d2749e819044d09e8248c236f427513fd0bf007c457a800000002a60b1380004e1c9e1cd5993cd40ee000139e8e8848d80dd8c9c025b0f3238040ce11c20c5e764880a85b610ea4f9c5f693ef398e9970e920896163a231853595b71c44193816804f91646131cb6a122f40ac4b7047412f518e0486041e9ca217b622180cf27b33dd26f4c4d29fc5104089a914ca1451fb6162c29c08bb284200008aa11ee33906040f8a800018386e90826a3df0f5a0000658113529581e450061b29385425181c8a34f000033d4aef936d0e164c5495e08bd4ef02b7031908c141527eac34318d422a23d30ad68f00196815e08f58884394a15f0fc28fc52a5c5610066018f2cd2578c4d59d2807fc0000587996b0000415419a062b1fba082c07b230c2abc0aa40002125068e9accddd06f0076a232803b9b0411860338051023c2b167dc5040871f2fa000001e1881f000063c4000099d1e323b48fd014882e1e15a8f22a24e423280f000005d603a800012ff24e9000000009cb8000335000000000daa488e00007a28e081c425de82de00a400006c1c01480002744000128000000b2a00000001bfa47e85a98f3c0dc500008c70000002b133e0000c28000000002490000003d29c01ae4ce5000005a63a4800015520f803a2cbcf8b81000033e5324098334bc86940000f1e38140000c72262800001c2119ea5e2270c82f8ff3859b1cca1db0ec310282d2a1b0800017a029f8000000000004a10086c000000030822f2d39b19431d689ce4a4480003ede000000014ea3b7002811a91d9526220000757a1db0bd64110d7e1dee000000005e1972700002d7800002ab1c409af02008da71d508750000152d0000385017b82b328dc3f7c0002373106c7280ac18ad613e23421315170b40a268312a3a58c4fce0000d1d00000f6e0e60df911e508da592000000001ca000011110
  | 58 => 0x805d2e6e90a097b235e3e7c86f02190b19130a4180f63a48a21be8c348d00ada260641c82c403201368148c9308885000031f40000000000064bc0001c0935f432208b6a65500e035b0ab50ed40d7a0000299a5c6104248e47460a480c18040000011d143c46b6522fa6fb000000012aa0b9e36585df4000000000002d60cd621a421a055cc5b6a6ff0d7e26783b8022f0000544c594a2ee4ad42f5cf680b3a3bf23c74c2f11021ebc2a7532c10aa225067d0d1c177324ba5014ee41a5f47320c3c3ec92bf1fa450ad0b582cb114e88f850c111a35dc2c9472984e51f2a86800001b41264a3af4be0a4de01bc6a2538f81c34b504b2d28e94741484000113c93782a2a8a24f18938d4f2c4da8e9a2396350621f80000545216a1c60525215d08ba3d88dcc9d460d367270ac99b61210814d010e0000000014189a40000183a9ec4ca5000048aa7680000040e0da095dc0000cc016864c24cc41763283653ad22b8fa913765e50c0103441820258113787f918260000b908aba0b90826c1ac800042145e887450fb246fa015c28388f00568000073c9dad0c3c11093fd8fa039045ce113d16f500003d907940f2f002e000004c831c00003ddc000110540009a64fdb800021d227c802c94bf1ae400000000756441085382a70e0b279265a52b10b3e10da1e080001d69126c23c8000000048ce3bf89ce0d492b0024f0268a6841dc06ed4b149bfb031443882309159025c0360b1a8eca2efe30b0dd085d14a4a05382fb1a16445021203f01025332e2c68b5c05501664753896380000000716486a98ca4b5e68890c80c99042211e52e4088041da1c7005821dd39ec59c12c084e24fb82ab0adf096a3c549324a9e010a1ff8106876694f2355a0fb10079666000030f4c3b80000b940000dcf000048e012640000b6e1ffe8f600001b4342b64284ef69c6608b2439d2b28601052c311106c000002ba8f982399fcd02182c34d4813d642c007ace9e192c32443e683a5a6b208960000c3a93a91cf800007c2a03f051c55d866523c341a84b48d8a983e2c1a749888e275335c27a74c7e8543495c5bbcb61800049e400012910f6744120b8cb3b1145000079dc00001ac33447a84a20a7a3437a03f1382a6790b4e09b4edd961229fc659419b972b46ba6ecc2d990673ef089f12f212482e246e6094c9b3b2e66905d0a9839b2fa228f088824e7246401ec71e824306b893153a7843322663620719085a0cae29046af260d27ca6bfc9791ae62df2777c732126402c632d88c612cf100283cd39f1b01192c2a001979b6c4c362eb9310a26217728cbcfb38fb71bf811d516a994123783c50ee00cc717f87ad12cca04f277e1e512530119150259708029bc543e64a98c4ba4040c7e9b90a88a3273218088cf85060202b4936caba8142111470e0e0f9fbc0ef4
  | 59 => 0x44ca119d95a82d50176434c953b08ec8c103b207270f58491c9a290ce17be98980000000017e5af47d780001bc651f400024270d50477519e000007b23a5c000065d3eb827dd2dd857304e645b01f2249c14a8000000000474da468a12368d9200007e4922a07403b9c20345b5909041ea3da529b0f2309f80000d0905280738000042f259c000016b0000242045e2000000018551ea434a400020864454024d21a80002d1265f53ea988c09bc56bcae500001030000068b9b492892574400026d8000060c00001546265c4a5474d252925c41c644c4971017460ca479297ed11b8181cb8627a01580795016126fd0000771d3031e8447da3f58e2012710000000028d9859413251ac3f29a93304028893b0000000005f6429b8706215800006420c7500001f3008200e516688f78aae828500001b4c0001b6b225a96012e1855d01dc12103e68000104461d0000032a0ab69930fc3187e28a6744c4c8800000009e38d6820ea391292f0000000000000000818000044263c24055a5d4000000003be18b34e942e1c00000000e1222d83c6265446b670980000ef5239e1ea00000000000025e46ae93ca4e0000000de000029e25f08cf680000000000000014f800000000bd0800047ac73c40000000247c80d40000000370a3b18829137d0000962caee1bed00003308e1081cc30a29f5914a18de4354000007d0a3931b081202540bd80f68944835583f60c940000c4c038e04ca95a0f071c8c14e054ac57f06f600004e1c49e84b60000255085e8000000059610cd95f100000000be2a3cb389c00010d0a69c0c106aa83e31f6e001060dc00023372a187b38f301f94466a04ccb329b64105431310368a1d11683afc768928312c249fc21e802128c493b833a82e6106a3fed2f0000026260ce86920fca1d36400443292ff087060290730c633cf63e18ef880000804000000010f7201a0000000163a274c94780000ff0000060e8e33800036844e8d2f6a52622de03fc0001db92d429f04eb00000066054580b38c811fb20e0c6488de600905d0000007341d8600001d9232d452c90b80c996d33022000136b1d3d0e7470b400024910000000090898bc28c82eacc35143f1e6e000000010a503b812bc0002481366000003bf00003e324800beb21d8113014f4f0e000030f20000bf8000028648e48a7322a1000000004d11b62000054d8160000010721b2822219a700009c24000276c36e4504ce1f0eac09ce000054413c0228240302f81bc311a0099c786069202c294a01d1800044829a5c4d208bc26ca06e896a89fc02f804193ed00541076591510d9dfc184845d0d9103b10f086248f7011c729f647c08baa649360010dc4610c2b41e41754e0d923c0e507ab01101ca721f647d93db05e90e760000ba0907048f884d8364881702fc948c12b
  | 60 => 0xc0000424e791878d261f349c1d1465f8da631de0000fcf92a0211678d400024053f604aa8ab486db2f7a190d1370e8f2e0607d8ef595b608a29fb83c184fd47a00088260846503200180c7386ee0b6e802ca5b000039928ef83181c0c10aa94b0f399572188486aca18256333f460ccb18a5702868609c44b8a59000027a82c61b0b000050a80001b53115864cc5d2800022c86ea422480002fc602d00000e03189c2d543fd99132c40775888f0ff82ed0393c5e01b670e1e9bf0e2881202b6a64a133e09ec0000000098700002db0406400004641a2c8fcc55c0000000085f904020dc115c00000002652000015e4d4c8ea0000051a09d51cdc0b0000000000f584892294c021001126302c5000000001d2c00011121e3823d22ee91fe8987000094d0028a2f9314004e403f8000000025cc0001bb749001a90de61b71471e54940000000471c1c7441d234e3aec05510489b83049c3938b02232a0f30631cf7589ff22e60f710a21ef133f09fc8eff177400001990602851521d000000000000138862b114419e343da744051a8bd540980000d1e2186239c00006500c9d000027b8fcb1b8407e88c7828e1fc6408430a000021fa1406000017c846c11ea620c8c713f938e231cca4b267b2bc252a8a2ca113205458c0725800028da99dd09813601aae26a08f318a90ede8d1c6e8842c377e26283289f89282e07f53c4a53c39fc03741df0df339da1d5c31626e3000042a4f27166f34d86f44d6400000e0609c80001dbc13cc39b10d48000396a0000000193b403017680000000294216f84c900000000000054990ca01788b21378140224ca3060913169900009de853700004a7e4d2518106cd00004ddc8dc9a15123a22c449996cb1cee0000e1c92f812ae000000000e10e9400008e181de478e0000c9f000004547c80470188b455e26a83071a001c909b440000c7f45be58080480bb4063000004cc9bc702482c5848a8600000043313e412161688801ce619ee71b3c299114680003f3031e8c16928824282e4933c0000000032dc000000042940000522800100000000e65273100007a5400012ec02cc8d2c22918ab241e10e8000050d0000245c61c9c570b7e4988b08a7130000118031e000041f46448bc38000000000000001bff3504000061484be11ba0000000272d4e8c74e000025aa49040ad800000001a7213bc0001ddd2e2204486baa12c27c64671376975711e20fdc1c515e8433052c80000891000000000000a6900003a340ab9c6000000000000128c000014786f894670a9e67ec721215a053a625870c0c4038fc5ee516502ba44ae89d908c025302d6195476a800034e60000f6783ae179413a08448906266e00000000305274207e49fe0e38000044b8a8b80000000411c00008793fcc3f949f21be11e0694ece758da2091
  | 61 => 0xd657e12a317db071631a09d91ac541381be02b9000007420000c4a80000da800000000f04238000000000ea2336200002c800883b642a782691fdb342229b0412a3511d3c04b50e08d6d32b498a4107270f000000000001a5900005280000093031be0000a97895a02da00000bc225806285508019000000006d780001041180e0000d639c6d17006264f92a3842f100a285aea6680000478cd5407900db224583d4847e4a48967c0000125458c0e9cbaf89a91c482594c6b093404b83824b899acc25f409c40f4972a03e674b4e08924c49940000000206c20d295c8f9c086e4e9c7910808978d2a4e250cde6800046309830c3e21d105303d1cc358f5d28f0556c1aa05594bee0000d28257f1ab02fecd879c0327bc94e832e067404201468a9f9b9c2a4000007f0000039aa571895381c039ba9a6c5ac852c00004938e1e82d600000000e5d8000000006d40000d3300004da0000224000000e1124b95e23cce00008f12170147e000000000003306307c7790b330b4c203c00005c2000000012de0000455c16f4d5d118300000000aca051805f66bd00cd87750ea657640000000430a00004500cdb12b672582479bdc000095e1109244a21008020274894f21da87b072200002366000125282ec000080ed3cf8eb9000000011ad0031157a0000fd7800010ec1ebc8e927e849c2752c4671fe9000000000000083084a9c0c56f12c2129a804c000000043d64ac8e198000000000000001b2029601ecc91887101cb81268801921b3dde956800022820000000019f80003d3695b00841fb12bb4126c00000001d604edcf0019dd2d60761cad7000000007ac400001da1550000006100cb000000004028e1a00006b2936c80002bfc72a0565000006c203d50d317c320f83a61153934c00000000ae8035f00000000000007645e811c8000233e00007868e79800001424a84000059c26240000e8400c400007c9800000003a386384320000032602068000078500000000963000018bc0000b4a0c3600000000000275900002631028144600001df4f530c0834a21bf867c12f14dd676d93418028388637b4ef11c6e25302cad3f824940c705e94849974927708da89989b030c508430efaa1482e740000e6f1c19152890e1305168a00000000000112000000000000119008448be032d9d164a1e65c114300000a1803f80ada425000084840001fef473e5724a8524130ce078d921f800006200000fbb101e00004250000000000009b7d09c80000d3c145d0ce91ea2f1c0000a7e81ed0bf41ef013b8a8b4e3219602d481ad151a4b2892b9b4a00000000d1f8224000000000000000067600009f582603d1c0aa0b8115fd000077ecdf621fb34289eb4790919a1f785a382c191073b624288000003a3abc062d36f263a21f4675515f8bd2022c3ccc1b
  | 62 => 0x7dc000121480002ade7a6022e19d044a26ba429d9e7f12521340f979ac9198297c0c54169a142c25286bea4580000135c5291f340000509c000145e3dcc717c000120b253e2488db69cd00000000000018c1180867bcd290efb19443b4c0000000000089ed295103c0000113001e0000321c18640000000000024511f08d6e000000000000000376200000000d1d05ba5f8400000b300002da0d8d84402f008c400000127270a55b041f8c5816543a84e7c99100000000117307fa28c2069c6869a700d28171d14399394aac0ff0bdd85e70f2a08f42d4000027a02278f5f8e35067c5d7805b90261cb43770ecc0000000057789960129317e7bf800005694c6400007c70d4b3b1c0c48cce808e00004a783569a8b000099cc67792e325466f049e980370c2c2da892018ec1a6293312341a8e0d5e1a2c0f70fc03196480cd119de70ef6200806d8b024d3e0bb405e95a632620d9074319233aea2cc44cb9f55419c96186bd82c6278a1f44a9512e90000185017c17ea050e5884ded199c2d8a83f46900d8d3e52519937780003c5a4b946241f54281457fc46b9ff533347e6505510500c3a01580002667000065fcaeea7ab0f7e5c741fe911d00007b4c07e9d6738a488e46e09daf2bd63ea000000004610596c000030933280910a041d8900f82ea128804bd34b804fc163994b4ff4508052fa7020bee00004b48c344458000049600001f62611cd1f09ad3b4286c48ff1ab700006584a6b8000000088c87bb1f2100007600de7800048f0877d1a28f270f108ea92038000016274043a69864046000006ff9be94f3027acf1e110a0000960c524a3b2000029e400000004e14370845683f9000014946e9819f36e800000f180004d16000126980004f7a9e5501f0ac7021275e4bf916421b6c3e4439c1b603d94165859d98e200a4081c309a05e41162d30ca61e7907981f8c5ce966d28f660545caa02d4e10292c19e879c44c07b75177a6ce47b800ec16486632f3219fc7b917363c8279d420c1f022d787be925c8a8342407a20e84963e45445a149fc15644b04530c10d12a5359e0d144dc15cb3a3a823cc668d6132de50c4c43a0670a069be484102f2436649ecdcba74334988e0d2d580cf4e88974c454131c0910699419a839e18b8641cc7324bd1790362c632a769355e9240a80830d01282238b3c1ef9059490f0629279329ea6dd40880a001b860decc002754080e3cf4e378970232a216c05282b24a362fd84c6931e232494c840f000047003a98c4f9677292293cd08903d81e1e26001f9206300002530f2e99e7389a08ed102213a20660cb89af11a30000569530382c140d63d40637264d3bfa00b0c471d6d2c1249f0b8a999231844198862909e46286138da205d4489a000130a8f9e2e8852d4b1997aa3a1449d4b3e01f500
  | 63 => 0x1ac000125d12bd00000001242800000000a78cc380003136000000022fd000099bcedd12b14e566bbc00003da000000000000000000052a438b83aa08b40000cc000002e2e7218a3a85dd097e14d4e6120c4000000010440000000000000000c55000000009cc0d4000000000cef8bd13f448e54d0d00003d3e37392ce981f4b247520f9716811d840df485f817f277836ccaf207ae4d126b5000001c644cc989c97d800000001d0427000001828555400021d23c726108cb100000000000000000004c7663e4dce9edf247670e88b197ec14869d2018584ab0000217400015c53a826de4a8f8e514a625410dbf027c4e7879b400000004b7a2c18ce917dc004647791ee929a05d626703f40afc1a500000e489a941f0e618919a09e14a2a1dc51c40ff12e461c4808f0f5920bc1fb0cd680001c368a00e7a13bd238c7fac6439ff21fc2903c12786e7250a88fc276930f377610d4ca38ea319923a1000b18444982601cf0ca0bd2f566a5430e1f032e847090c5f0be1195a0000000130d18b4507cc2687424e4022e800018c6375a61b497305c400008c2d00b10e43b0231f085726db3f723d6cf6627ce341418986519fba0ab8591000008bf47ae5e1016a866f000043f129392e000002d249c198534c203ab468d0546429e59fc44121b7290e000057d81bd49aa71093c58bd90cce3984e7007dc2e7676dc17520db16c470d461d01620fe496402c907d3164c201c20e05d212627188343a1064f20636528a094b2f960bf53e110883d3c5b54fdb0a262e947058daf8e812330756d14c0000000000006bc80000000814c0000a2438643ce85030000012e8934000000023f428a110c00001d8e0000da39eb600000000bff95f42ec00000000000000b41080000000000000001382181a00000000b8e058122800000000198e29180000f99a77304b20000fec276e4b5200007330dec0b0410e505b80000000000000024d000007f2c0000000013672d0000269e00002f140001be62b84773cf299d5f232c9ab0c78149536387455008a47d1c5e25011c6000000008aec0001bbc31c06d34584a20f0b3e6210b70966a0c7a3d7c000102116b6237ca941fbf4d18707126892672f88695908e810d28fc26c0e1801b8226025d88dd91e022566ccce32230e4bec130094ba6460540487905d09082f360b8092c279a2b66723865706c31e587aa11f215b21bc285d48f41dca23e8797131122033efc00983b091be29b0832d1fb12c9146619140000e23210e96fc90280d51c940cb51e30be533e44828000048e1ce86d180c3941507920000d7600003a760c443279485184a95f42f0a24c08f805ec4938cea44882850e4c80002f986ce928502804e1a8c4cba91566452e51c8d44249b3dfe806c738a4c80dba1f50d39193a029a1548d988d94121800000
  | 64 => 0xc30897e373401186d815783ae200000000c220cf87c5c0000a273dda000000018d50516526c7d61fd506fc6ed1001861215969b3538e18760646231d283208347623b40000000000007558f6a202741305c0065e8f4b0dc821048a915a700007d587bd0000498e3ee0cfc9d521ad43d04497927800004e68cc82609304a144d14a83d63c285ec44658c9008900000754876e1e6230fcd1e8447387e210c510999f45062828bb7841f42665b652858000052a0000000254800000000c5798314b1c00000001168000021ac38d832637b05aa515a8b474e9a21d102ea6632210776c91d21d93f8220b4cdb0d3f395805b86da062415aa86b02648ff43c0a8e981710a0c00001a140000000335c8e1c7a3049201221f2912f80001e9c23b52db80000000552c7a1000000006d3d3209344233c271418f010732bc0000b080e59211c9740d8b80000000656cb518ba700007b249218ee8264296d45c81b962da40c002a5a2fa2e081d38846971a125000688098c153a36214d21527752c988f9c4849d841b2c41c45981a323cd009e0dc697f74056839118d0000263e808c50aa63447162fd05e30000280c1550d030e800000233400000003714000016a1634257292645aa24d71dc442c47e88bf5000028dc403257e22784ad89c980003080138d0ab1632000091004a2848b00080e6436f1e1b49a49dc800013f3249698141419af72b7e69a0e0a254f45843ee8e70969f28ca6a1ce2227c942ce39cca5388700e4043692b71b251cd6080127d8dcd4ebe00800b620ef3b9257580d5243b20ee15209802367000079850e98d54168a16292259e0c00001b18e328a1a03fe26c8bab092d283c000000014a5074c00000000510000000010c3a09e0000225129821f643ae1e9c0001376000090ac00013244bd4339cb0400004cea7d9800000000000689055488d20000000000007371204945c5af966c3f882b7c85c00001dbc7594000156300004599328921d1fec55151c091ad1936027c80ba4ed28b87acce671316149a04dc9a898bb268e00e13aa9f9e01c43d4c5341aab111659044f4075f00da15949bf15a2491e86e92759b4b426e2df449d9c6c00005704848884700007d6047e8c03190c3f310080000159241bd357185b39f85a887c027bb4a308a4000003b72b186a287f680003e8c000005c811100de993860b8c411e4c0fc12091253000029e0390858f3006029d3950fae2c3073a0dca81c7271436bc255000000000000ceb800049106a349e10a08000046b84200336000000000000c74089c88391001eb516b43fbc0d98a7f395a427c08292963a6a176cd688d590ade59ed1e2852d2fb42e388d21e9717601028cfa800000000000883144200006724000107e2bb64fd4e2c0000000093a01161de420ea536c000195419260000000097c4
  | 65 => 0xac41bbd1b697bc000043506fe800020640000025197147c455dcc1e1d5a00006ad42858a5d3b2646241c492ed23f65a60892a62f197c3a7ccbd9def246a2b2131e000000007254398a6cb26be345000010e33d5e17b03e20381184283d0928011f1f3a480800015792a889a8000014c12cbc26fd18a866c45742058a8d9ec2000002111b881e0083a0b3d09e135b49b800bcc7f9d0744168bdcb8b14901de80b94000040000003ce000026d425209afcea280002f2055700000000490c4cd440e96920000003d3548000000000009f800004bbe29bc66a04163c5c01412a20000341a8a784e0800009cc0000e0a800047a600007e819371b225d392bd207c0670750000020b63164000000022cf470c76a4129211600005c78be30b7406aa7a8000018904632000000018f203c47d24000000027360000714830800002b8c0000208411a698d08a143d41c6722ce0300002ea886013a5800004ba0000ec61707265e2a6481a8000000091405d8800044a66e049b58beb06bc00010509e5b05b220c05d31b27322214a430f8df4000079480ae084b381e7d0882ba5ee1c720000195800016206654318800000008d5c9a18bc700000000ae70c4a11320000687a42f1f240000000000002e4110d06a80000000000000002481900550ca1e0a8a061c75b0000000033a869d13a923fb0000000000001742cfc8b90000000000008cad3b0a61240a46d14b6311c81a8c75553ca1add00004f38ee580002ee42e282a39abc00005de40000000383055a12e0118b232e7664000000020983f705f5208a2b54000099f121f4cfe8bad12c8eda15a4787800001f72ae21ff4114a3e8231e7dd00609f084a1844bca5a162e0000607439214164ddc0000a148d7c29b8000100e17ca0bbe0000b28a7d73bd28c8919f80001ad0698516c0bc420049aac3f986cc095c23245e6a1c80776825408b91490e269c5c2409fe430e48e34a721b374d8e694cbdd1b3e0634773409a25e94b9a79b83cd80002dfe1fd00001d2a49e020cc6740eb544a42dcc483815130760000fed1a7c3018000012598a7000076f4d27838520707c68824014800007888f8a13ae37f2019c0451a6a026c28b119d0895195e3668cd09f1234544f5c17f800000006268ee200004dba6498cc2800000001818a800000000019b80000a553a180000162963f12be16680a50234088a0000b1682da340a9c680000000398c00000000000116449c93860a0700002dc858aa0a609727d7525c1ca63e3652b400001a309848ae00000b7f0cb400009521bef46362b100000000224678280299bc41ac09d240001efb00000000a11116b0000324870e229d45024bcc0fd1b6533b816b4fb21dd412a49dad130a6c104c6347800e85cb000099b53481e510c961d20f381ef845527a411f024ec13a89978
  | 66 => 0x44c824a0280825d42040d7422748b0020f0e40109c22ac00014281c688324dac86ac448e0ab909fa234017c2e6c4ef1221264c89c13db90be36b44d084e911c14b127020e68a19e05be303c5a10462245c30f832c9998403e7524b72087a218859240000c380000000091480004cc05ac4e1d80001b5888c0000000048180000000000021c095443468000040c72dc15291850000000000000001dc26bd916880004d549f94a8409c643d200000590a311488000061521712f2a44353d6231d024c00002c9884d47487820d2e8000041e9988c5b969e1566220c1530519264476280000000192e692d1580000366c84691089d213f520681270126d3aa68f488fe8d5c03308c3d1050b3d35085f4c4e4276a12f040d85230a5e345644ec446943802746298d0e8ba91e402c8413ea2783bc63dd0feb87290f464cec3ed0f964a800b70a7412ba4d3a17891d98d8126d830f0d171f7f32066d6107011173df84c04c921dd524dc74fc42291dc05583bb81708f8a01d271700540b030fcc79c4490955a210a58bc4440f6349c685fcd57100f2fa456f1161a59106981b58da8161b4aba65f13859ff92b4814282b8929c3dea0340a7f896633e29288000267010d246341ad11d61cfe0000d4e97464546357c5b220eb46606a6c8bca597409680b0053258726cc37e0d75a68741f816d53df99d90352234c24e13b438ba57546b20e452f2c5abc3ac0000440c0a40a38847100007408b638e7b119000013f6214d00001be467119053c22000063604fa218c59ccc171a1f349a6478421058712247bc93058000000099d097425ac1bbe189cf2b802d2ac06bd4af51b022ee050393408649404c57ecca78a0b440e389887c88d53c1e33a42a087f60b2825ad34a0bad48146dd811b9320009a767d1498bfa25ae2d8492f8f131bc04970fd09bf60000878cc40957e3ae053d919c02893f460000000125b00006234181141d4d8420380001946255e543c00021d61a00459c6828b8f35b60000536960b4b3097e80001789380036c4b8f8000000000004de9c8009465b38702896d142455648e58c6b092201a133491531a744b100000000240c8e9c7140494386c676ce95a6360b804728f52212d3b4822dc000198641fe2f7067d000000000ecc58381ec00000000f710000000057bc06280af241c784cccf00002d9221980799f0f1f3614f0dc721631eb8931000018c800009439261807e00003a940000000418010c000015ed00009b690bd264520244dbcbe400003052737c827143e1f7c0b38cdc1b524742802400000001fcc00002dc80002fc08dd000014820f0c17a83449639000033b0e4407b616444ebd0cf9948000069d497ba43d30d02c90ffd105847465138958065242062c30f2004c40f2e5348a3c9ca93f80490883716fd086c2f78947a3f2
  | 67 => 0x4db8bb23f9423500c90cf40000143c8319c940000550483c80001dde30c039e800013b08ea0fa519560000381820817a345ec00002cc00003de002612e60000000093910e6000000000000000159d41d84128fee0f162fd076a80ca06a04c7c12c4d86896c000013fc739136e490637244020000000000005c1189c0d5274d92a6828822702b1818b158929ce1c3400024fc3816555ccf5800034626960e8885ed13ce52e4fa18000039e523d1f70095236a6084c601e3e23424664f8583e34a565d34405968c24f4978cb3922a03f0088747911925040273588c09df62010016c77d1374185e240537b8000143670a4b7c137946c0338c68500364ee08ee4d9a9d9c4e28888c00002e40000231515b800029282394a468380267a059500b991b0000000133f1a5a144a6e6c25d251606da00006672776070c5148000000017089d440cca7e013584454fab9bde017437c0fec94e51b4695785f2000000000000fba8fd72a9094bc7e48a6a07a200003e5a727217636080001e8a45581484000225b2e909690473a1fd0d8e3008c99012a16f2922c0001ae4000000002d51dc1000013d467b983500002bac62297d40fda0000000000000001084fbb80003ea000013d513ea10d80a84f1d96a546625ef8bbda0701dfa2a900871f231c04238cfe60cd702583924d0186ce2aac0000a5d82d84e0e8a70b14135831ae29f428492b538408b8c00000004fe25d991540000000019880000ea42cb49654f95a0ae0bc600000000f540c7c1a0c0001e74000000008fc00000000188c00000000a0a0c041ea9d7300000000000000009b4844055825f44c286524b1222773cca2700f01982400001e490da268516a274bc8c0084649a8675845100001e7c61b8c841ede149e02581be23c00e924a4cb8680002bc062208d389c337ae8dfca760a200000032081590541cb6000014600003e7a7560f391f13000052611ca16ec1b5c66d0c0f0abc050c18a82568c714bf2000000000003eca878000018c9284a1278b259d6f2c9e4f54000000043bc00000000b1300000e688b50fb6000000000001dfa000000006379c2c00000000e948f1b00006180f5da181000043c920c8db538c60000000031b000051a42a98e9c28f44230000000035ae1b890c60a0f47f41cbc1141f880d1c4c2860f023e48584ad0567816f3d5a055815b93401d9603e0eee0b8c1eda430d261022d0000317c44495fc3d2c92f826b16a73d7450e8e67821415dc01e52e0a1c20bb09fcc548008f2a92691d219025000006e7c27da3bf00002b741f4a060089a41e85e08747425034ac000063610204fb116a0000000023dc000048625e800e4ab39f9318f2090517e04b5042c80e8e872069236e0e3400000002ae097087d21ce542e84188a7089f80aae28f482984534640325
  | 68 => 0x8c30000000071e8c750c594d2c88cd31b86ec248a4be4a630d763fd44370c8e976d24aa0001038800000002cfc45317980000000045200001dd6299c7ed1b703ea469280000e5838e6713c0db213429941d448f08d5b2cd67fe02fc9562321a15d433999f70f64597c73485d021b62b80e8c887b16966fc4e9001444a720c54611a48c4c8e0ebd1c50a9c27744d9c04f0c0d074809c13a29f2d239a6bc40000c1643960d48d9e10423a280810b41a0211734503c16f019a246e811cc1b14770c6a35682b7230706828850ab5a77d10fa0854b9227b4359a3508cda9d8f1a22494800026dc2d941bcd1d00d7a2eee3bc4a1c92df2ae83b8c2f889553d90319cc1323ce04a80000a57800036561f0c70c8000080c00000002406157c4374b2002bb07d436c80000000068650b116b0000074a0000a2d02a40df429450538d6644ac1810fce01022e28893c90492ce4c227924e9d20f6493a2574000266e0bfc0000f010000000087c1370210500002440bd7800000004620000000000000000000015803fc56e41781beb0f441778531000036805748bdf9f3015045a353188dab05b6620000000002f0a6b54caf8ae62be60000fdd83512cf426580002414084e31251f2905c22240000dfa1f1d49f459181d0150223980000e4e948b32b81918018000016c073b800000003d460000b5d96fe00005c180000000353013c928e273400000000c5ea5fb207a9be0000226c06f2000101b829c0856039028916ab050887e4f0800001d546cbc8218f6a0afe9020d75033949f0432cf1209c7179c1fc020297764d2673b0ea80bcf0ec003b50dc88292afa8de505687654ab2753d12a8dd73e887694302806901545eb0a5e1e4c01cc95243d2878a147458e060584b83064765ce1397ad3e1a9aa068205ff3acc99a87d08b1800382f24e4f8cbc450860146a400ef4fe859c43f094f321a2571098321764bba4e3c267a3163fc274cccbf036a441a02b00001b3d28122be8c9012d637a48d64e7b96ae45d472e4000151e24d2408c7a219e811187cb053f1ff34ef27f0c42b8bf924a87ac8922168f00001474dca15a31a0e416c9bf800003006b8803613292eb6333107b80000f2c9434b2b069d37923540ef28000094291746ce845700007a65185000028be7c7c5f720432f228c952a121da38f60c9cbb488590774000026e8cdd000e000021f17d73fdc73f41f8a19301380000000202500002ea82b8045b1fea14981d5a3a51f8458ec13b222f070e06909e18a740fb0417c0afa54c4f6481ec80b032c3ae47fd9228903b38d052f4c2c11f300129bd82279ce23ad4993c305187a000061ecd58261829ee120c2c4829121d40e58ebf000000000000b740000000000012270000205e000000000000368584c02e00000b689e0c000000047d80001374800
  | 69 => 0x4432aa6061046076b17c63af93ce844121a6068885185241f7a4a0124f0ef6134c41b04e598014c402a8808a19292dbe87dc2b42797417e33ac75b22ec0000074c2d78a9f35861cf11919119310a4760bec08d910186408c58912417c44c6c35087ab2b1055509be078b48d276f8ad48c8b24081770a8e8f9c207449f866313382b1a89d422502f416e2000088595c3000000000000d2522ca22f8dc98c82207267d914784f831488bb4f9ca4b711b646b02ba2146000046ac00013b91f547768652872a36f0216031d8000258a46444620e3135e00000eef25ef29e869f93f69996000048904438df50e286bc86bc000028ec3ed018b80004f0010b47b9a46412a68f2811291821a606ca849f1af84ba400007bc0f292d100000e2512873fc069c48faa5a738049fe12508e942294785ce481c3c38ec8034f2b10f500be651435a1c103dec268081203ed45fc872802616dc2e5a431caa50027180223ad06107be1c2610501662317431042e455695b80f7a7c90131078139f44a50912836e23146eb87968413092a9a9433099661b50246c030921925987f413040ccf3ed219e475e0e623f047488aaf8121169e43bc2cb9bce023a25f462e804115ca2d38d79a2c143ea18cca8a017113302864e3aa37514ec47c88aa891c4e6494045071b770ed05350cb9a4392a3869b8c2526c812ac6118d7f21cf0c529f60166a08e30280fe86c28ad810c423b8daaa09a19b29c047670f48377032b06fd18c5320270890a10567357a792ca2806e51aac0ed84d38264193c11ec3bb953517ee63ac1e68a5805367fc13d2004342c82578000243a3796268cdb5024600002190000000000003c60cd2a61c24ee45ec0001dd10000000000000002776775cc9a15b44d4627d00001e332d98000000021b831f65afd05aa40248060c7c7d68dda339e00005a69d8221ac000092300001e6400000001eda000016907168480000080890e68bc22c9c00002c304a60d228c852e28fb94b3669eca931782452293d8d5213a54ccc695515515291ef60d8ca08907f40f42984e0f060d16a652681a4916236d211f4473060b3f5851340a3a1ce41b204ed1bb24d91e1a80a45eb150320b235390ac07f744a053104a8992b120a24982c20e7018c25ec0a7d01bb0a98326115ca58835a67978a780a8726343fa921b1c7435fa6e24a3e097b26e42a5d325a71e31d227682338b8d1bb01bf4970a31147ee2e90a4189f9400a8a144878bbf41ae93a8000236524e012dd3360a56315a0000cc607351a88313484c000031d076fd3661fed2b36642c00000002460372843f9eaa4c864c300001fd600009170000000000005ab4d1823ea000000008d5269a2bea27ed0838169326a758800000000000467cf4008ff00004fe8ad58000127e01c8000133a36ae000000000001bd400
  | 70 => 0x1c00790a71208c2da4d3d023f0e0e000000022dd2f3889c8580a5db2de068b064198ae15d2980c39618ce11e65cf8000097a00007d793b29bd64bea98d400020970000000072094e33c7e425850883b446e400005bd0fe2396239580000c4740cc30c51cd9848205a7a4ca8902c30bae453c0001ed63fba154496d1d271f0816b908b8000000032a42af000041a680d014980003d880000000000000000000f98a09f00003da0561109c149c6f9c4898ff90000956c0fa220c456c7b8d15a0e3e02b232cc00025ca2a12785939293f20da222d4000000000003b5c0000c3235402d7000000000dd000000f09d74000093880000c43058888d8000000000001da8bdb89ca27c29d6c000000000005f94853035d46fc9f000001020166c0000000279b419a46e07c78000280e14bc78718e500000000d058d8900002ad03f4a3db078c22c000011ef054627e9299926a4d9e5eb8190a25c203415980001ab43afe98c025d80004f1800000ef800006d27d20680812f26ba8b7067b211e3d28736c00000002722000000019af13c618d0d8a00004a9c5238ddb0081021e6e30dc78d7f08d2000072623bc10ce85b48e819064950387400021260d183ff49e3a441137875289ff1f000000000090a8bbd018c647c96f1d23455a6ff8cf48a401d625460b3409e5000000008b0167541e034e0634818e1b4a7d152811f274f9e4f7c828a51f461220708a19fd34fbc3b94b8c04c8114a829124a8000437600fcb759ae32af4000054319e5000048407f391471e808ce43ba162b4866000043e000028c08410ab09cb221786e20b03961a000091d84c100000000930136b80000000214800000004c7a0000109a1004d60158c0000ee737ca00000000000000031ec00000002be400002dc0000000000007151c5b0000312c63680004790685ccba196e000089ccc8e137b000055401a10a021ca89074894817508625d54000000000003b74b2a9ef33bfe2ac4d7c91613ef62044db9a47b0dbe25607a50d9f20d000010b483d036702fbc6b1985c47224d580001f35000000009090075000071c865c19a022ae00011a0000000000604e7396f234206894ef989f527da4c2cc938be930700000a4e0a1f2faa36e0000138b4fd22a3910c800039360000000223a31740c641ba9b1100008f083510696220000005680d5319a27e3c00025042ea01d3cc49961d41ba48cd2d90c511d5600009f403b800009e2938d9282000091304858d7e40501030c399d90338694b474707fc424698387ca00001bb60000e6585f400000000e2602d727587a890271d17000000000001148000000000000fa6000027a4000069800000000ffb8f3f02345a08f559f8147383d852d108b827088b148b49de8091a75f52f083584dd82ce4d8f8d9302967d7c21188081124065c0bd14
  | 71 => 0xbb4e828710ac280003b289554ab7034d44ce25c4095a36118d4064434813ab47a82ba0a31a2f50ea89dc53cf00003d2449785de257100009d710d3800048de0001312951a000048b40000d4c000070c522d8000270200005f000004fc26e8cfd6928a00001010b438f02208a4bacddc849f15d47644b3e964a000049b03f70d624b4028d0b7d228c0c4240b820582bc4e8e5ea52ed000002f24d28d6c0aff1e2e06185a4180e3e6e2d4103f00d407d60001242247322ec3370fe797e93bb20054d2082ee354c4ed8eb202392a7081513729fe500000000146800000000000b900411414685948328e0741660620dd91a623d220000a278deb2a686d7406b20af4a8a0000579000024ec2e2d05288ef115281d0d5188153bb08bc10910e122f664e486e000001e160000cdf88f642e60000ccd9fa7011800006ef0ef3000000008a3139e00007de4fa680003b66258cc32913147fe1a5cd3e8d4a21800c10000246045a40a3c1b000000b9c7b90fb40b652ffa00d0c79a11b19e080a800005c14d4864647ad0e274f4e5cfc375952148ee5cc116b884f4962681c3f59dec135c571c9d683d73312933c00012e71bac6209259a68e03b00000b9401a61cd48770f991e4f24e64a3800027ea0b4a53380000000101231dc68c800013fa3adc39c93b043c89f3400022010d787adc00000003500522806e09b50000111933e866800008ed80d40fc8200020f094300002e8a9b1907c176e0e4a00000001b062668718446d1f72380288dca499ba83868409ce5206b1137c000006f8d3b00009a8800014181cce0000000177e05f8444d3a00000398000000000000191895840000000425c9890af3000000000000000169343dc6f0132d2102348648b0a4f14354bb27e30b93168000006d98000000000004d64f538ebb43e87db0000000013ec06740000bcc0000000115ea61d12fe00000650755000000008ea00c000001f040000000265a0000000159200000001049271014a00000000000000001a9cec42039092e04f80000c9c001c3e6070680002e4416e90619e251d204f50ce09bea353800000001dc531da0de800000f4409a66f8000232e19b400006b384c3285a5f88a68a3f016801d706508466256e48203c00118285c67000a0272e3d0a72150f50000268c9994e3f88682d6892ec0000a653a8457212b01bbd2d2e944cde800cd2b34686c8111506345e610c6f4000000000000000000000004cf11ec8000000039b4bb6162c00000000adda64400000000fda18b003f0248ce598dcc32d09be872180a33ec40f98ea8952207785aa91bd01e836ac6b684318fd51572242848701e6301a57c0d0c86ed2e5e4f044ac852b48dc531467e0ae404fc2180246038244b400a841f1d8d0fe22e7caea109523b6824c5788bf20cf68eb0b4880000f267
  | 72 => 0x95f000002ef384633f80001fe31c1c71a8ecd86ae3c3040190809d3e39ae2620b9e91701dd276984b900004c8028100001743313c48fc96021c300003e0ce2b1fd234fe226c000000b3fc40f6c0000e6e21cc000000004290a287c610d69adf0000900410f157c23622fcc9110d84293200013be197638f80914418a16e000006dd05820b41b36892c0d78d0326828188b4e8fb3000000012d69ac115468f3d0328995113a173400024740650645c9140000079e0758bf9800002fa8b6458000000e8691893ee96e7493e8fe0111182a0eba8ebcb4807a003902e4d369a0610de2612c0f3a1084d6e3548b5907f80a1c6e982fe1f9007de065400019bc1b0c74787d11a6d000036dc00022c414122774c33800042e44349218a13e27b48a91394200a31226afc8ae8dfb33148ed412d1c9a459a74148d9064d330219509251e9c224e4361346908f1dac7d2d06323ef3a246af8a1b0b1b255287f0631203809b2246120d1df242a078d080215ba1db29fd8f5808b9142673a4f548f4f15181f1c0c60258172837652da0cff1d2a965034115d33c3e7fd01e1162303e43fa49ad219938a81dcc61703c10e005d9c4688ecc110237c88ef857e3ef82d051c284f6046a5ae91e090e524cc4a1004e92b82d6a4f188758e0a3bc01f48f7514df49566dec73c192a1dd828e052e0b7c36a89e148f381c94e443cacbd41c130c349c58dd2a0ca43fc1b5d3d7249235243bfc6a38415336445790f0974b237a19b510e1fde191c2590f8294480c063cd5092235f1a6c908cdd00cf22720038c14a14b34bce366099ca2640e7c8b8436598dd41f265b4068909d3b349e9911e0ad401d8906059b99b907ea7df4aa796f40d1e601897e0f6e1f86000038094c2431a533c9ca0a853114585430da35411c402a50f41e32135e9cd509d80002bce7804500a1a200b011a03ef1c532ab000b8c07935515b26f0922c80002344000000000000000000076480000000000000018f70ce42b34bcf1a3b000044f80000508000060f400021b6136c84a4def8715353e83a400005763a341b3cc85113903604ecc550000026d218b81ba10ba0c1e0738a86a5a33d807e38b7b8b7700003e8ca7ca557172e6664ca81c8d08d409005ff981b090e6368135a16133fe40250be128d000098040000e47165c17cc3f2161400003cb8b4300061284365c1d4166e13c82a54f2a9a7723ee9260ab2a14137204c6400020b11732828800016de35d0664c0858000417279accdd0f810000996441200004b1e3fb825900003c169694323a0c827dc677815516c22fe86500b218e4613284a886b58c54151273503719cba0e080a6535aa49637a886c03b68f112cf244593bf0170213228bd10f133f0d669c609ec000017426ad87ab9c3742c41bd122b0000468819acf9b1664241a2be4dd38
  | 73 => 0x9dea063a537409aa68637fa2124d8487300a54957c3d21d304f8e34dd02ca4630d0218b42988fa71c087b0d32b946f3ff882b10ea815245163b6c2bd17fe0fba831ca01824c000084e04280ca8053e5200fa78be800000000eda242400d4000101e94371f9a5ff01de9db038927de8000256b13620e412fc18f40000712c41386181c564b602e607163a6436a4fad0d65127039802561df80fac9a08fb516d1131623841ab9f9b09a682a0b26a7d21e20416871b91a516ce9634aec1c7d00003ab8a9907e7038800000f8000048f21d6cef825743b3a00012f889000000383c43780000e5a4498000236916a4000011c000511d83830dc11cbe4e6675b884d8b890000420c387066a06668d9908480003fe2913cbc1921c054e2a9c0fda68a1a46898c0001a424cd682ac773074c42160c4c6ea04ce00000c0c0000000000000000df00000000000002f06110a94604873f06b223089f6cc5a00001824504090d078f2ca637b87640c002a464b0cf62800025fc00003ac86dc00000000000000035768f253b39f8d07184c50f2d02551d6687c41370564147612141e3992e364608752ac06bb2de68e409ff8ccb16e050504f013a700008f8c68582d12e0200001b5800000004dd4dd5811c32b000012bd98573fbe31e0f6a988600000e548f88b9c23743eec0000b111cba000037a8da413020ad49fb887833a6000013604cb285e0000d2427372f64000002006c409d688946450bd0196228b479d8d1c00000000000000017f000000000c3b3f704c14a0d210e45ce0000e0b973132ea0000a4924aa37588a6cb3085fb0000485c1e200003a98000000da4b53ccc000068c14264e7401cc6c51e7a15ce0000fc1800000005e30903974f000048f454d11091c2a6b10000242d0000564400007d70a0019e8d2480d24eae81d4e238b1e1b96422828f9e7e3ec645610c8a3cc432866443220392290842bd0c119fc2c3e85311451bd90a083b9030827d4129c37e53021d5429d20610b92a4a92a32528c000106a46dc1444fa7000019c221a8e8017ee4ec486d5222959f1bce54e47b88dd02992088400000e700007e1098b834a275085e000009ed09a8565c297145d03622ac86df865f2608906c00008af4ada6424299014601e00c904b4150e00007e5cbef10cf000043d927ba42639fe3e7d3b307054cc2021515e00000000137c056a7cb2096985c48d0ce501b4605885b00714fea60200000000276a000024827a900007e44000000000006ff040c808b00003cf0b7525d640dc0f0067d800021dc0f80c528b7609267e98000204100000000df700001f9e4aad11d97f833b44530133045000006884f6d9df43d8c0000c6d800044d66c3917116253ac69ba920fa430346c860d34c221a057220dcc67931d13745e18ac08948495e5e90000046f4dea
  | 74 => 0xe9b2815f800048160000bb2800024404698a5100003c7a5298ea6928b00004510bc5a49a139a3754f360a661fa8604c7ff1ce300267ba11d11d7700009f4c35a80002c1e20503708b2000008080000034004de00011be000041769c4480d96dd286653593601cc528aa80ccbf380001d0e5290d562350000041b4719979340804f30b5ca0242ed495981a5a509341c0000c7f13d940b896cc4398c0619be7928bb222203ad6000075387b8255061fd27a8d13000000013788ddd34d293e46628e7d33c2398c000134b01c0000000000000000333520720e5000000000000ca64c1e8cc800016542d58000073425dc42aa85e40000000041a7c70425244341fc012cb1ea5532db472840129afb2aa644b0b8ca6bb3ddc1da421f879a47aa6e010e306c01c76623c6b981761c2e9590e41a5c425b25204ba6000000000000a28937a2bd8000000010c2000000000001b7a00008128f2c800c10a27104fd71f41093066340000919288a474c24e9e692c0c5fbc0000000000088b4ce2000012ce78e8d4b867136729dbcf10234d221e50350d7a6c5044c4378f6b89b942cc8ddc98388cf0f3e78b09318f063e8e98fc8da17b82af609a07baa2e83e546738ce28d701cf4671908782e9288e6c4d3e5058e0a7c43c1167126f176a43e0a4f913d3bcc53bc81fa6be205267346071b86076013ccf6c938929aa9ca456295e53542404077ca5e606c415b4cb622264eac6f8880e0055133699d844e162a3466553000011b642b262d86810ce42b0e0190eaea18a2c6e950cb9c8f0736181bed10b88563a1619586dd83534b4c2db025a27d0253a00010a5820527a2701c00005c926a469e4f132688284610246299a2d3c0820e0d6e1622111e05311fe01e52e646ae4ae0025e24920a8911a881b11f483685171e2807bc8b2c09109e2495a1150f1195d722fe327d27e87662e586918b68059d482044881b89d8537ea0000a9f1a0139269fbd3168702161600000001b080f92224c000173c06d80000cf824df402a42cc41908fc057c39780220000116644381e9093521e6000026a92132eb8798d09e9a403d5c91c4f40903742ee94dc000000004927e741a821924c00000000026912f3a4ba800000003d704324dd80cd32db60000d37a24a00000001153114d072e0000000000036fe33480000800000036f881a06420000533532806ea04f281e05d025383642000025988a300004650b4b17cd10262bccacb1b6817766c48d591bca3ab2217d30c800025767d44000000033540000cab8d0e0000000113e8d5531dc613127f000000003e341df825100004f74fff000015da0bc40000af600008384b3181312f8e33210d725d514f8000057b800040e66cb4cd220580000914c00007df02a000007b01382190a08c410185e53e3c8b4c76200fb08dc3e4c944
  | 75 => 0x80803d0e364652847c782800014524248b710e934776887d14f92c838509e3cb9a95ac473c2b0d25a1e4840aa62e0f60910100004cd812116e30d4614d870fa4b02b7a8e5c39189440000000000003072f6834d05940e250000148912e9c1a3ba06fdcb5f22651c0083c45fe856c0d709ef1102a00e105e52f895708e430d234b0acc9e1234ec98090b796c0284872608bb87db20f025bc000133200002aed19210310000298c13d9d1f00009decf5f048245a07a9400023053200000105c0b0423fe0000000215c0cf07e6842e07794b7016ec8501ed830685dc4c229a2600001cfcbe7a51125a637180000000255a7b3413d0000226800000000000000078540000000000006948a59c920f3c3df40000b124768000000000000912063400000003b8600007f61e642e524dcc0000d2e39a67310d9a14de000074b86b7800043e408488ad158e15d82ebcc3e9c504e9800010b5209628b60000000111127d251a8dc9000030ba48ac5df091121b23fdce8308fe4cbe1b684869b1a4daa88ad3f10ca4460238e8c021fa82dec007c1ea161639cc402d315a6d012544904e068e554312285c4c7138c0dc07bd0c68006204e871e4000168b487c57e80ec9d4320309868f9104f024fa000087f86840ab03ae000003e73cc40c88eae0000259a34f800021492ef0488ccd190971d8260b02a4a5734004935855f840d3f7c01988a814d926a000000000cba216e61253af215134c0000000020b22dcc3b7cc38a05a0e3408600001cc834b6568400024da15fa25dc09e80004ed000004ff19f31366797c00000000db000008a10bd346d09b99210a6e10d7c5b10000185400003d44000139900000000d768950000019f8c9e1781215023a91b10c3703424f213d101cd000097ad2f400000d4c0ac0a398f124d245fecda60dc4432e00007ef1fe834f00000000000039467120061a30321345fd46c61f0c25588d0d26584b0000060e469a8ff30efe49ac0001a130000000000013cb035c3d5856980000e6c03640000c7e0a889faccf50e91260491a8d9f84a446663dbc45083ca2e36889d0e0040300002c5d023098f000071dc000092b4b084c8ce87907d2f4e000000019cc00008d24438800041bc3df829f96b34fc660ac59e13c410e
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x863554584300432b29ac2180219554d610c010ccca4b08600866552584300431aaa4c3100219554e6188010ccaa530c400847775586200431aaa2c3100219554d6188010ccaa4b0c400861e54d8d200430eaa6c690021879506348010c3aa831a400845e7694d200422e3b4a690021179d953480108b8eca9a400864f63949200432631ca49002193d8d5248010c98c6a92400843e74d94200421eba6ca10021179cf65080108bae7b28400843e74994200421eba4ca10021179ce65080108bae7328400847571594200421f3a0ca100210f5d065080108bce6328400845d73194200421ebacc8100210fdd5640801087eed2a0400843d76950200421fbb2a8100210f5d954080108baeb318400861e5498c200430eaa4c61002117dd56308010c3ca8b18400861d5458c200422fbb4a610021175da5308010c3cc9298400861d6494c200422fbb2a610021175d95308010c3cc8a98400861d6454c2004317324a4100218b5925208010c9cc7290400864d639482004317322a4100218b5915208010c9cc6a90400864d63548200431b2a4c2100218d5526108010caca73084008655539842004332a94c2100218d9516108010c6aa8b08400865653584200432aa9ac210021999496108010ccaa4b08400847576d5310042aab9ea988021595cb54c40108eaeda9e200853574d4f10042b2b96a788021c555253c4010e2ca8a9e20087155454f100423abb6a5880214d5d352c4010aaae7a9620087255494b10043a2a9ca588021c995152c4010e4aa8a9620087465354b10043a2a9aa5880211d5da51840108f2edaa4200863965952100431cb2aa908021965965384010e32a929c20086596554e100438caa2a7080219a5965284010e52a929420086696554a1004394aa2a508021d254d52840108f2ed28c200847676d5110042aab9ea888021595cb5444010a6aeb2a2200863765951100431bb2aa888021cc9c154440108eceda9a200853574d4d10042b2b96a688021555d65344010caecb29a20087155494d100432bb2aa688021c59515344010e2aa8a9a200847676d49100429aba6a488021555cf5244010acaeb2922008667659491004392aa4a488021d154e5244010ccecaa922008726545491004392aa2a488021d194d5244010e8aa6a92200863554d81100432aa9ec0880219954b6044010e62a920220087515390110043b0a948088021cc5514044010ea2a6a02200876152501100423d3b6a8880214e5d65444010c76cb2a2200863b65551100439938aa88802196d965344010e32a929a200865b6554d100438caa2a6880219ad965244010e52a9292200866b655491004394aa2a488021d254d5244010c72a9b0a200873154d85100423d3b4a288021cc5525144010ea2a728a2008761529451004398aa48288021cc5514144010
  | 1 => 0x3104237bb4a5188211b5da528c4108deeca94620846d7654a3104332b14a3188218e552608c410c72a8b04620865953582310431caa4c0188219a54a600c410c72a8b00620865a535803104334a92c018821179cf65884108bae7b2c420845d7598e210430f2a4c7108218755263884108beeab1c420861e5458e210430eaa2c71082117dda53884108baed29c420845f7654e210422ebb2a7108219398e5288410c9ac7294420864e6354a2104326b1aa5108219558e5188410c72a93044208639545822104334a92c1108218e5526008410cb2a7300420863954580210432ca9ac0108219a94960084108dee4b1ca00846c7258e500422fb9ac528021171cd6294010c6aa930c8008655539864004332a94c3200211ddd56190010c6aa8b0c8008655535864004332a92c320021179cf65100108bae7b28800846e72d944004236b96ca20021179ce65100108bae7328800846e729944004236b94ca200211d5c565100108bce6328800845d731944004237390ca200211b5c865100108baeb318800861e5498c400430eaa4c62002117dd56310010c3ca8b18800861d5458c400422fbb4a620021175da53100108beeca98800845d7654c4004236bacc4200218b9526210010c5aa9310800864e539884004326a9cc4200211bdd56210010c5ca8b10800862d54588400432729ac4200219354d62100108deed290800846d76948400432731ca4200219358e52100108deeca90800846d76548400432731aa4200219358d5210010c6aa9308800865653984400432aa9cc2200219994a6110010ccaa5308800863654584400431aaa2c2200219594d6110010caaa6b088008666525844004332a92c2200218d552618c010caaa730c600866552986300423bbaac3180218d551618c010caaa6b0c60086655258630043172a6c4980218b553624c010c9ca7b12600864d53d8930043172a0c4980218b550624c010c9ca6312600864d5318930042373b4a4980211b1da524c0108dceca92600846c76549300421f3a6ca180210f5d3650c0108dce5b28600846d72d94300421f3a4ca180210f5d2650c0108dce5328600846d72994300423ab8aca180210f9d0650c01087ae8328600846e721943004236b90ca180210f5d6640c01087eeab20600843f76950300421ebb4a8180210fdd9540c01087aecaa0600861e6494c300430eb24a61802187991530c010c3ac8a98600846d7598830043172a4c4180218b552620c010c9ca7310600864d539883004237baac4180218b951620c010c5aa8b10600864e535883004326a9ac4180211bdda520c0108daed290600862e649483004316b24a4180211bdd9520c0108daeca90600862e645483004316b22a4180218d952610c010c6aa93086008655539843004333294c2180219954a610c010c6ca8b0860
  | 2 => 0xa6290218b9526214810c5aa9310a40864e539885204326a9cc4290211bdd95214810c5cc8a90a40862d64548520432731aa4290219358d5214810c3cc9318a40861d6498c520430f322c629021875916314810c5cc9310a40862d64988520432731cc4290219358e6214810c6cc9308a40863564984520432b31cc2290219558e6114810c72c9300a40865963980520422f39ecba1021175cf65d08108bce732e840845d73997420422f398cba1021175cc65d08108ece232e840847a70197420422ebacc7a10218795263d0810c3aa931e840845f7558f420430f2a2c7a10218755163d08108beed29e840845d7694f420422fbb2a7a1021175d953d0810c9cc7296840864d6394b420432731aa5a10219358d52d08108bce732c840845d73996420422f398cb21021175cc65908108ece232c840845e73995420422eb9ccaa1021179cc65508108bae632a840847671195420423abaec2a10218d5536150810caaa7b0a840866552d85420423aba8c2a10218d5506150810caaa630a840866552185420422f39cca21021175ce65108108bce6328840845d73194420423b388ca210211e9c0651081087ce932e640843d74997320421f3a0cb990210f5d065cc8108ece232e640843e74996320421eba4cb190210f9d0658c81087ae832c640847671196320421f3a4ca990210f5d2654c81087ce832a640843d74195320423b388ca99021531c9534c810a98e6a92640843e74994320421eba4ca190210f9d0650c81087ae8328640847671194320423d380ca19021535ca530c810a9ae7290640854f754c832042a6baa641902193d95320c810c9aca990640870e544c83204386aa264190218e55260904108f6eab04820863954582410422f39eca20821175cf65104108dce5b28820846d72d94410423cb82ca208214d5c554104108baeb318820861e5498c410430eaa4c62082117dd56310410c3ca8b18820861d5458c410422fbb4a620821175da53104108beeca98820845d7654c4104236bacc4208218b9526210410c5aa9310820864e539884104326a9cc4208211bdd56210410c5ca8b10820862d54588410432729ac4208219354d62104108deed290820846d76948410432731ca4208219358e52104108deeca90820846d76548410432731aa4208219358d5210410c6ecaa08820863565504410438b29a8220821c554d4110410e4ca4a08820872552504410431caa4c0208219694e6010410cb2a7300820866a529804104334a94c0208218e9516010410c72a8b00820865a53580410432ca9ac0208219a9496010410cd2a4b0082086b1415804104237396cb188211b5cb658c4108daeb314620862e5498a3104316aa4c5188219394e628c410c9aa7314620846f7558a31043172a2c5188218b551628c410c9ca6b14620864d5358a
  | 3 => 0xd06054c10a9ce4302a60854d72181530428f3a020a9821475d01054c1087aed2a0a60843f76550530430f2a4c629821875526314c108beeca98a60861e6454c530430eb22a6298218b9526214c10c5aa9310a60864d5398853043172a2c4298218b5516214c10c9aa6b10a60861e6498c530430eb24c6298218b9926214c10c5ac9310a60864e639885304317322c4298218b5916214c10c9cc6b10a60863664984530431ab24c2298219998a6114c10ccac5308a608639649805304334b14c0298211b9cb65d0c108dae5b2e860846e729974304236b94cba18211b9c865d0c108dae432e860847671197430423d380cba18211b5d662d0c10c5ca9316860862d5498b430432729cc5a18219354e62d0c108deeab16860862e5458b4304316aa2c5a18219394d62d0c10c9aa6b16860846e729964304236b94cb218211b9c86590c108dae432c8608476711964304237394caa18211b5ca6550c108dce432a860846d72195430423b388caa18211d5d76150c10c6aa9b0a860865553d85430423aba8c2a18218d5506150c10caaa630a860846e729944304236b94ca218211b9c86510c108dae4328860847671194430423d380ca218218795263d4810c3aa931ea40861e5458f520430eaa2c7a90218799253d4810c3ac929ea40861e6454f520430eb22a7a90218799263d4810c3ac931ea40861e6458f520430eb22c7a90218d59261d4810caac730ea4086396498352042973a6a5290214b5d35294810a9ce7a94a40854d73d4a520422f39cc929021175ce6494810a9ce7aa4a40854d73d5252042a7398a929021535cc5494810a5ce9a9ca40852d74d4e52043872a4a729021c35525394810e1ca8a9ca40870d5454e52042973a0a7290214b5d05394810a9ce7324a40854d739925204326b18c7290211b9db43948108daeda1ca40854e7398652042a6b9cc3290214b9d06094810a5ae8304a40854e7318252042a6b98c1290214b9d36254810a5ae9b12a40854e73d8952042a6b9ec4a902117dcd60548108b8e6b02a40846e76d5152042a739ea8a9021535cf54548108dcec2a2a40854e7315152042a6b98a8a90211b9db5354810a5ce9a9aa40852d74d4d52043872a4a6a9021c35525354810e1ca8a9aa40870d5454d52042373b0a6a90214b9d05354810a5ae829aa40854e7399152042a6b9cc8a9021591c56454810c9ac631aa40846e76d0d5204236bb686a902159dc54354810ac8e2a1aa40854e7398552042a6b9cc2a90214b9d06054810a5ae8302a40854e7318152042a6b98c0a90214b9d01054810a5ae8082a40854e7304152042a6b9820a90210f5da541481087eecaa0a40861e5498c520430eaa4c629021879516314810c3aa8b18a40845d7694c520430f324a6290218759253148108beeca98a40861e6454c520430eb22
  | 4 => 0xe0cb20a80885b174905404431c32a82a02215c1d54150110ce0caa0a8088730755054044399b2a82a0221ac1954150110e60caa0a80886306550540442d9b9a82a02216cdc94150110b62e918a80885e1728c540442d8ba262a0221e450d3150110b62e910a80885d17388540442d8ba242a0221e85092150110d32c6a0080886a9625004044358b0a8020221395ca61cc110aa8ea98e608843f74595304421e3a2ca982211bdc9654c1108d8e4b2a608864f531893044326298c498221551d5314c110d88c498a60885d0704c5304426ab9cc390221591d521c811087ee8b2a408843c74595204422fb9aca90221171cd6548110c98c7a92408864c6314920442b23aa4290221b118d2148110bc0e090a40886b1649071044359b228388221785ca31c4110ba2e710e20884e77258e104426bb9ac508221ac5924084110d66c8a04208864e6398b5404326b1cc5aa0219398d62d5010c9ac6b16a808655639875404332b14c3aa021479cf5495010a3ae7aa4a80852e72d525404296b96a92a0214b9cb6395010a5ae5b1ca80851e73d8a540428eb9ec52a021479cc6195010a3ae630ca80852e721865404296b90c32a021479cc6095010a3ae6304a80852e721825404296b90c12a021479cf6455010a3ae7b22a80852e72d915404296b96c8aa0211b9cb63550108dae5b1aa80845e73d89540422eb9ec4aa0214b9cb6355010a5ae5b1aa8085347158d540428f39ec4aa021475cf6255010a68e2b12a80851e73185540428eb98c2aa0214b9c86155010a5ae430aa80851e73181540428eb98c0aa0214b9c86055010a5ae4302a80843f76550540430eaa4c62a021875516315010c5aa9310a80862d54588540430f324c62a021879916315010c5cc9310a80864e639885404326b1cc42a0218b9916215010c9cc6b10a80864d63588540432b31cc22a0219558e6115010cccc5308a80866562984540432d31cc02a0219658e6015010cd4c5300a8086696298054043172a4c5a98218b55262d4c10c5ca8b16a60862d5458b5304317324c5a98218b59262d4c10c5cc8b16a60862d6458b530431ab24c3a98219958a61d4c10c72c9306a60851e74d4e530428eba6a729821539cb5394c10a9ae5a9ca60846e729925304236b94c929821539cb5494c10a9ae5aa4a60854e7215253042a6b90a929821539ca6494c10a9ae5324a60864d6218a53042a7394c329821535ca6194c10a3ce8304a60851d7418253042a7390c129821535c86094c10a3ce9b1aa60851d74d8d53042a7396c6a9821535cb6354c108dee4b02a60846c72581530422f3b6a8a9821539cb5454c10a9ae5aa2a60845e7615153042a7390a8a9821535c85454c10a9ce5322a60854d7299153042aa38ac8a9821935886254c10a9ce530aa60854d72985530428f3a0c0a9821475
  | 5 => 0x846c72595434423bb8acaa1a21179da5350d108b8eca9a868851c7454d43442a6392a6a1a211bdc96510d108d8e4b28868845e731944344237390ca21a211b5c86510d108baeda98868847475584434431a2a2c221a211e1d56010d108bce7324a48845d739925244316b90c8a922187d936354910c38c9b1aa48861f6418d524430e320c6a92218b1936254910c98c7b12a48863464d855244237bb2a4292214b1d15214910a98e6a90a48845e73984524422eb9cc2292210f9d0601491087ae8300a48845e73180524422eb98c029221179cf65d09108bae7b2e848845e73197424422eb98cba12219398f52d0910c9cc6296848847475587424423c3aac1a1221179cf65909108bae7b2c848852d7215242442963a2a521221531cd52909109aae730c848847475586424422fb9acaa1221171cd65509108eee2b2a848846e7694942442363b2a4a12214b1d15250910a98e6a92848845f73594424422e39aca21221179cc65109108bae6328848846e721944244236bb6a4212211d1d56110910c68a8b08848847875580424421f3a6cb992210f5d365cc9108e8eab0e648843e74d96324421eba6cb192211d1d5618c91087ee8b2a648843c74595324421fba2ca192210f1d1650c91087ce8328648843d7419432442a6b90a619221535cc520c910a9cea990648854c754c8324423a3aac2192219514d610c910cc8a4b086488478755803244364992c0192215c9d46090510a6cebb22828853674951414423b3b0a8a0a214d9d85450510c6cec2a2828871673151414438ab98a8a0a21c99c85450510e4ae42a28288731701514144272b96c6a0a21355cf62505109aae630282884e572181414423b3aec918a21395cb648c510972e830262884747559131442e3396c698a211d9d8534c510aa8eaa1a6288556758c9314432a32c6498a2195194324c510ba2e019262884b5741813144272b90c098a216c5d0604c5108ecebb2442884d573d92214425cba0c090a211d1d564485108e8eab1a42884f07058d21442e339ec490a211d9d85248510ac8eaa1242884e676cc921442b33ae6490a21991973248510cc8ca19242886c5630c921442f0b806490a212d5d060485109aae630242885b174181214426ab9cc210a21475cc54d0110a5ae42a6808863454587404429a3aa83a02215c9d46190110ba2e630c80885e17218640442b83aa8320221cc1514190110bc2e518c80885b3744c640442e8b9c43202216cdd121901108bee6b2a808845c735954044237b92caa02211b1c96550110a3ae62a2808852d72151404426ab98c2a0221395c86150110a68eaa0a808863465505404423d3b0a8a0221665cc5450110b52e42a280885a972d0d40442d8b8e86a0221665cf4250110b62e3a1280885d17318540442f0b90c2a02218e1974150110c
  | 6 => 0x28422eb98ca214210f9d065cca1087ae832e650854c7254f3284296ba0a599421535cc52cca1087ce832c650843d74196328428eba0a719421535c8538ca10a98e6a94650843e74195328421eba0ca99421179da534ca10a98e4a9a650846e7694932842a639aa4994210f9d0650ca1087ae8328650845d76d4c328428eba0a619421535c8530ca108daeda90650852d7414832842a6b98a419421539d5320ca10a98ea990650864f654c83284326b2a6419421b24c9600ca10d6282b00830854c7254f31842a6392a698c212e5d0604c610a98e6a96430854c73549218425cba0c090c21475cc54d0210a5ae42a6810843e76151408428eb98a8a04214b5c85450210b62e3aa2810847a76151408425d3b0a8a0421665cc5450210b52e42a281085a972d0d40842d9b8a86a0421665cf4250210b66e2a1281086b061505408421fbb2a820421879516310210c3aa8b18810862e545884084316aa2c4204218d9516110210c6aa8b088108699635004084354b128020421ac5854010210a3ae829e610854d7214f30842a6392a718421179d8534c210a3ae829a610854d7214d3084327a98c4984219314c624c210c3ac9298610845f7654c308430eb22a618421531c9530c210c9ca6b10610864d53588308432b29ac2184219554d610c210a5ae8296410854d7314b20842a639aa5104219318f52482108dcec292410852d7414920842a6b98a4904219318c5248210c5ac9290410864d639482084237bb2a4104218b5915208210a98e6a90410864d635482084333292c210421995496108210acee4a9e21085577354b1084237b92c7aa2211b1c963d51108bee6b16a88845c7358b544430fb20c6aa22193d8f6255110c98c7b12a88862f641895444327b18c4aa2219318c6255110ca8c7b0aa88866462d85544421fbb2a82a221471cd5415110a58e4aa0a88864e639885444326b1cc42a2219398d6215110c9ac6b10a88865663584544432ab1ac22a221999896115110ccac4b08a88845e73184544422eb98c22a2211b9c861151108dae4308a88865a63580544432cb1ac02a2219a9896015110cd2c4b00a88867161580544422f398c02a221175cc60151108dce4300a88846d721805444237394c929a211b5ca6494d10c3ae6322a68861c64d8d5344317b26c4a9a218b1936254d10c5ec8312a68862c641895344327b18c4a9a218d1936154d108beeca98a68851c7454c53442a6392a629a211b9ca6114d108dae5308a68843e74180534421eba0c029a211b9c86014d108dae4300a68846e72d974344236b96cba1a211b9c865d0d108dae432e868864f5398b434432629cc5a1a211d1d561d0d108f0eab06868846e72d964344236b96cb21a21475cc5490d10a38e8a9c868854c7254e4344272b94c321a211d1d56190d108dee4b2a868
  | 7 => 0xb996210f5d365ccb10ccaa530e658843e74d9632c421eba6cb196219554e618cb1087ce8328658843d7419432c42a6b94a619621535ce520cb10a9eea990658854d754c832c421f3b0a8a0e216c5c354507108ecec2a283884b67615141c429b3b0a8a0e218d9d85450710e2ce62a283887157315141c4393390a8a0e21c95c85450710e62e02a283884e572d8d41c426ab9ec4a0e21355cc60507109cae4302838843f7655041c431d2a2c020e218e5516010710d6282b00838854e72d4f31c432729cc518e219354e628c7109cae5b2463886656598a31c4332b2ac518e21b8589608c710a9ce5a9a638845e7614d31c42e3396c698e21719cb534c710ba2e1a9a63884767614d31c426b3b0a698e21551d5434c710aaceb19263884b57418131c4272b90c098e2117dd9530c710da262b00638854e73d4b21c432731ca510e219398d52887109aae7b2443886556598e21c432ab2ac710e21b458d6088710a9ce7a92438846e7614921c42e339ec490e21719cf5248710bc2e1a9243884767614921c42733b0a490e21591d54248710acceb99243886c5630c921c425aba0c090e21355cc60487108deeca9043886e12158021c431aaa0c2a0621355cc61503109cae430a81884e57298730c4327298c4986219354c624c310d88c498a61884d57398720c432631ca4906219318d5248310d88c690a418846f7258f5484236392c7aa42117dcd62d52108b8e6b16a90843f76550548430eaa2c62a4218b5516215210c3cc8b18a90864e639885484326b1cc42a4218b9916215210c9cc6b10a90864d63588548432b31ac22a4219558d6115210cccc4b08a908665625845484338b0cc02a4211b9ca6494e108dae5324a70864f63189538422fbb2a629c21875915314e10a98e4a98a70864d53588538430eb24c629c218b9926214e10c5ac9310a70862e645885384316b22c429c219398d6214e10c6cc8b08a708635645845384333312c229c21995896114e108dce5b2e870846d72d974384237390cba1c211b5c865d0e10c5ca8b16870862d5458b4384237390cb21c211b5c86590e10a98e4a9c870846f725954384236392caa1c211b9c86550e108dae432a870854c7254d4384237390ca21c211b5c86510e108bce7324a50845d739925284326b90c6a94219318f6254a108deeca90a50862d6454852842a639aa4294219358d5214a10c3cc9318a50861d6498c528430f322c629421875916314a10c98e4b18a50862d649885284326b1cc4294218d9916114a10c6ac8b08a50865663584528432ab1ac229421179cf65d0a108bae7b2e850845e73197428422eb98cba14218795163d0a10c3aa8b1e850845e73196428422eb98cb21421531cd5290a108bee6b2a850845c73595428422f398caa1421175cc6550a10a98e6a92850845e731944
  | 8 => 0xf54c8020acae3aa6401062d5498f2008316aa0c7900414b5d353c8020acae3a9e401070d5494f2008237bb2a7900419398d53c8020e1ca8a9e401070d5454f2008327bb2a790041931d953c8020e4aa928e40107455394720083932a2a390041c955151c8020e8ca6a8e401074553547200833331aa3900419918d51c80208daed29440107195454e200823cbb4a510041cc5515188020ea2a6a8c401061e54d8d200830eaa6c690041879506348020c3aa831a401045e7694d200822e3b4a690041179d953480208b8eca9a401065763945200832a31ca29004195d8d5148020ca8c6a8a401064f73d95200832639eca900411b9db5448020a9ae7aa2401056571d512008296baca8900418bd965448020c5ecaaa2401064f65d8d2008386aa6c6900411b5d66348020c5aa931a40104ce7398d2008316aa0c69004193d946348020e1aa831a401064d7518d2008327aa0c690041a39506348020c9aa831a401068d5418d2008306aa0c6900411b9db5348020a5ae9a9a401064c63d4d20082b2b8ea690041331da5348020a9aeb29a401064f6594d2008386aa4a6900411b1d95348020c98c6a9a40104cc7654d2008327b2aa690041c39515348020e1aa8a9a401064f7654d20082a73b2a690041531d95348020c98eca9a401044c7654d2008333b2ca290041c95525148020d88c728a401074553945200832631aa29004199d955148020e4ca8a8a401072554545200836231aa290041d194d5148020e8aa6a8a401074763545200833331aa2900419918d5148020e88c6a8a4010644635452008316aa6c0900419354f6048020c98c7282401065b73d95200832c39eca900418ed965448020c76caaa2401065b65d8d200832db28c69004196d965348020cb6caa9a40107195454d200836431ec490041ca5525248020e92a72924010673659452008339b2aa290041cc5515148020ea2a6a8a4010762525452008237396c6aa6211b5cb63553108bce7b12a98845d73d8954c421fbb2a82a6219398e6215310c9ac7310a98864e6358854c4326b1ac42a6219698d6015310cb2c6b00a98866a6258054c4334b12c02a6219c9856015310a9ce5a9ca78846e7299253c4236b94c929e21539cb6354f108beeca98a78846e72d9743c4236b96cba1e211b9c865d0f108dae432e878846e72d9643c4236b96cb21e211b9ca6590f108dae532c87884e57298643c4237394caa1e211b5ca6550f10a38e8a9a878846e7219443c4236b90ca21e21539cf5294b108bce7324a58845d7399252c42a739ec4a96211bdd95214b108bce7b2e858845d73d9742c422f398cba1621175cc65d0b108bce7b2c858845d73d9642c422f39ccb21621175ce6590b109aae730c858845e7399542c422eb9ccaa16214b1d15250b108bce6328858845d7319442c421f3a6c
  | 9 => 0xcc4a8c621066562546310821f3a0ca988410f5d0654c4208daebb12621062d54d893108326a9ec4988418b550624c420c9aa6312621054d750c93108326b286498841c3550324c420ccec4a8a62106646254531083a2192a2988410f9d2650c42087ae9328621067151583210830f2a4c710841875526388420c3ca8b1c421061d5458e210822fbb4a710841175da53884208beeca9c421045d7654e210832b31aa3108419558d5188420c72a9300421065953980210831caa2c0108419654d6008420ce4a2b00421046d760ca5008316aa4c5200419354e62900208deeab14801062d5458a400826639ac5200419354d6290020cccc4a8c801066562546400822f39eca20041175cf65100208bce7328801045d73994400822f398ca20041175cc65100208baeb318801061e5498c400830eaa4c62004117dd56310020c3ca8b18801061d5458c400822fbb4a620041175da53100208beeca98801045d7654c4008316aa4c4200419394e6210020c9aa7310801062e545884008316aa2c4200419394d6210020c9aa6b10801047575984400831b2a4c2200418d5526110020caca7308801065553984400823bbaac2200418d9516110020c6aa8b08801065653584400832aa9ac2200411d5da5110020cacc72888010655639444008333314a2200419958a51100208eeeca88801065663544400832ab1aa220041999895110020ccac4a88801054d75ccb3008326b2e6598041c355332cc020e8e64a8e601062d5498a3008326a9cc5180411bdd5628c020c5aa8b14601064d5358a30082a6ba8651804193d94328c020e1aa81946010666625463008332b12a318041d10c9518c020c5ca9b12601062d54d89300832729ec4980419354f624c020c5ca8312601062d541893008327298c4980419354c624c02099ced992601054d75cc93008327b2e6498041c3553324c020ccec528a6010664629453008333b12a29804199189514c020e8e64a8a601043e74d94300821eba6ca180410f9d2650c02087ae9328601043e74194300821eba0ca180410f5d6640c02087eeab20601043f76950300821ebb4a8180410fdd9540c02087aecaa0601061e6494c300830eb24a61804187991530c020c3ac8a98601062e549883008316aa4c4180419354e620c020c5ca8b10601062d54588300832729ac4180419354d620c020a9aea190601064d650c83008346b206418041c3550320c020b92e0190601047575984300831b2a4c2180418d552610c020caca7308601065553984300823bbaac2180418d951610c020c6aa8b08601065653584300832aa9ac218041b10c9610c0208eaed288601063664944300831ab24a2180419998a510c020ccac5288601047776544300831b322a2180418d591510c020cccc4a8860106656254430083a2192a218041535c
  | 10 => 0x45d73191510823b3b6a8a8841559cf5454420aaae7aa2a2104767615151082ab398a8a8841555cc54544208eceda9aa21053674d4d510829aba6a6a8841c59525354420e2aa929aa2107447294d510838b2a2a6a8841c55515354420e88e4a9aa2104767614d510829b3a0a6a88414d5d05354420acaeb992a21072654cc95108392aa664a8841d194f3254420e8aa7992a210726540c95108392aa064a8841d194c3254420e8aa6192a21056472591510831ab20c8a8841559cc6454420aaae6322a2105667219151082b9380c8a8841599cb6354420ac8e4b1aa21056672d0d51082b2b9686a884159dc94354420ac8e4a1aa21055673d0951082aab9e84a88415c9c04254420ae2e0212a21056570cc951083a299064a88415c9c03254420ae2e0192a210746730c951083a331864a8841d158c3254420e8c86192a210745430c951083b138064a8841595c03254420ec2e0192a21053674181510829aba0c0a8841559cc6054420aaae6302a21053674081510829aba040a8841559cc2054420aaae6102a21043d76950510821fbb2a828841879526314420c3aa9318a21061e5458c510830eaa2c628841175da5314420c3cc9298a21061d6494c510822fbb2a628841879915314420c3ac8a98a21063654984510831aaa4c2288419594e6114420caaa7308a21047776544510831b322a2288418d5915114420cacc6a88a21065563544510822f39ccba0841175ce65d04208bce732c821045d73996410822f398caa0841175cc6550420a68e2aa2821046d75d894108316aa6c4a0841339cf6250420c9aa7b12821062d541894108326a98c4a08414d1d15150420ccec4a8a821066462545410822f39eca20841175cf65104208bce7328821045d73994410829ab8ca820841175d66310420c3ca9318821061d5498c410822fbaac620841879516310420c3aa8b18821045f7694c410822ebb4a62084117dd953104208baeca98821062e549884108316aa4c4208419394e6210420c9aa7310821062e545884108316aa2c4208419394d6210420c9aa6b10821053574944410832b31ca2208419558e5110420cccc5288821066562944410832b31aa2208419558d5110420cccc4a88821066562544410829bbaa82208414d5d54110420c6ecaa08821063565504410838b29a8220841c554d4110420c72a9300821065a53980410832ca9cc0208419c5466010420c74a8b00821063954580410832d29ac0208419654d6010420ce4a2b008210671515804108358a0ac0208410f9d265cc42087ae932e621054d750cb3108326b286598841c355032cc420e8864a8e621043e74996310821eba4cb188418b952628c420c5aa9314621064e5398a3108326a9cc5188418b951628c420c5aa8b14621064e5358a3108326a9ac5188419958a518c420cc
  | 11 => 0x830f324c629841875926314c20c5cc9310a61062d64988530831b324c2298418d5926114c20cacc7308a61066662984530831b322c2298418d5916114c20cacc6b08a61066662584530831cb24c0298419c5866014c208ece332e8610475719974308236b92cba18411b9c865d0c208ece232e8610475711974308236bacc5a18418b55262d0c20c9ca7316861064d5398b43083172a2c5a18418b55162d0c20c9ca6b16861064d5358b430823b38ccb218411d5c66590c208dce432c861047671196430823ab88cb218411d9c66550c208eae332a861046e72195430823b388caa18411d5c46550c208daebb12861062d54d894308326a9ec4a18411b5d46250c20c5aa8312861064d53189430823b38cca218411d5c66510c208dce4328861047671194430823ab88ca218411e9c06510c208bce7324a41045d73992520830f2a4c7a10418755263d0820c3ca8b1e841061d5458f420822fbb4a7a1041175da53d08208beeca9e841045d7654f420831caa2c1210419654e6010820c74a8b00841065953580420832739acb990411b5db54cc820a9ae7aa6641056571d533208316b2ca9990418b59554cc820a5ae9a9e641056571d4f3208326b2ca799041c355253cc820e1ca8a9e641070d5454f3208316aa2c1990419354d60cc820cb2a6b04641054d7254c3208327b2a641904193595320c820e1ca8990641070d544c8320831caa4c0190418e551600c820cb4a6b00641046d76d5032082a6b9ea819041595c7540c820a5aeb2a0641070e735503208386b9aa8190418b552630c820a9aeb318641064d6598c3208386aa4c6190414b5d3530c820acae3a98641054d7594c3208386aa4a6190411bdd9530c820c9cc6a98641070e5454c3208386aa2a61904153dd9530c820c9eeca98641054f7454c32082a7b8aa619041535d6430c820c9acb218641070d5490c32082a6baa861904193595430c820e1aa8a186410729549803208237baac0190418b551600c820c9aa6b00641072954580320836531ac0190418795263d4420c3aa931ea21061e5458f510830eaa2c7a88418799253d4420c3ac929ea21061e6454f510830eb22a7a88414d9d35194420a6ae9a8ca21055673d4651082aab9ea328841559cf5494420aaae7aa4a2105567315251082aab98a9288414d9d35394420a6ae9a9ca2107165494e510838aaa4a728841c59515394420e2aa8a9ca2107447254e510829b3a0a7288414d5d05394420acaeb994a21072554cca51083a2a9e6528841c95503294420e8aa6194a2106356419251082ab398c928841555cc6494420acce4324a2105727019251082b3396c728841599cb4394420acae5a1ca21055673d0a51082aab9e8528841d14c83294420a6ce8304a2105357418251082ab398c128841555cc60944208bce6322a210
  | 12 => 0x2024193d4d6210120c98a6b10809065753984404832a29cc22024195d4d6110120ca8a6b08809064c5398b304832629ac598241531d532cc120a9ceb194609064e658ca304832629ec49824193d4c624c120c98a6312609054c754c9304832632a6498241721c1324c120c3cc9a98609061d64d4c304830f320a61824187590530c120c9ea7310609064c539883048327a9ac4182419314d620c12099aed190609054e758c8304832732c6418241a3592320c120caea7308609065453984304832ba9ac2182419514d610c120d8c64b08609064d6314e20483273b0a710241935d85388120c9ec829c409064d6414e204832629ac310241931c963d5020c9ac7316a81065663987540832ab1cc3aa0419598d61d5020caac6b0ea81066662587540828f39ea92a041475cf5495020a6ce3aa4a81053571d525408297396c72a041479cc6195020a3ae630ca81052e72186540831ab08c32a0414e9c06195020a3ce6304a81051d73182540829b388c12a0414d5c46095020a3ce7b22a81051d73d91540829b38ec8aa0414d5c764550208bce7b12a81045d73d89540822f398c2aa041175cc6155020a5ce5b1aa81052c7258d5408296392c2aa041479cc6155020a3ae630aa81052e72185540831ab08c2aa0414e9c06155020a3ce6302a81051d73181540829b388c0aa0414d5c4605502087eecaa0a81061d5498c540830eaa2c62a0418d5526115020c6aa8b08a81061e6498c540830f322c62a0419398e6215020c9ac7310a81063664984540832b31cc22a0419558e6115020cccc5308a81063664584540832b31ac22a0419558d6115020cccc4b08a810659639805408338b0cc02a0418d95261d4c20c6aa930ea61063654587530831aaa2c3a98418b59262d4c20c6cc930ea61063564987530831b322c3a98418d59161d4c20cccc4b0ea61051e74d4e530828eba6a729841559c75394c20aaae3a9ca61046e7299253082ab38ea929841555c75494c20aace22a4a610555711525308386aa0c529841539ca6494c20a9ce530ca61051e74182530828eba0c129841559c46094c20aaae2304a61051e74d8d530828eba6c6a9841559c76354c20aaae3b1aa61045e76d5153082ab38ea8a9841555c75454c208bcec2a2a6105567115153082aab88a8a9841c39506254c20e1aa8312a61054e7299153082a6392c8a984193d906254c20c9ac8312a61064c62d8553082a7394c2a9841531c96154c20c98c4b0aa61064c62981530828f3a0c0a9841475d06054c20c98c4302a6105567118153082aab88c0a9841479d02054c20a3ae8102a61043d76950530821fbb2a829841879526314c20c3aa9318a61045f7654c530830f322a629841875915314c20c6ca9308a61063554984530832aa9cc2298418d9516114c20c6aa8b08a6106555358453
  | 13 => 0x5350920a5ce929a849054e7394d4248327b18a6a1241c3d505350920c9cec29a849064d7614d4248387b20a6a12419314f615092099ae6302849064c531814248272b88c0a12419314e6210920e1ea6a108490658539833248327b9ccb192411b9d7648c9209cae3b24649064e65d4e3248327b20a71924193590538c920c9ccb21c649054c7550e324832732a87192419314d618c920c98a7304649065b5318132482363aac899241539d7634c920c98cbb1a649054e7394d32482373b0a699241539d8534c920c9cec29a649064f6414d3248326b20a6992419314f614c92095ae8302649064c531813248272b88c099241b2d8c604c920c98a7310649054c754c8324822f39cc9a8a41175ce64d45208bceda9aa29061f64d4d514830e326a6a8a41179d85354520c3ec829aa29061c6414d514823bbb2a228a414d1d151145208bee6b2e829045c73597414832629cc5a0a419314d62d05208bee6b2c829045c73596414832629cc520a419314d62905208bce7b2a829045d73d95414822fb9aca20a41171cd65105208bce6328829045d73194414829ab88a820a41179d663105208b8eab18829045f76d4c414822ebb6a620a4117dd853105208baec298829064f53988414832629cc420a418bd516210520c9ea6b10829064c535884148332b16a220a414d5d05110520a6ceaa08829053475504414838ba9a8220a41c514d4110520cb6a7300829065853980414831daa2c020a418e1516010520cb6a6b008290658535804148339a8ac020a419c1456010520d6282b00829064c5398b314832629ac598a41539d632cc520c9ea7314629064c5398a314832629ac518a41559c7534c520a9ceb192629064c658c9314821f3a0ca18a410f5d0650c520aaae2298629064c53988314832629ac418a419614e600c5208dcebb2642904cd73d932148237bb2a990a41531cd54c8520ac8e2aa6429046e75d8f2148256ba6c790a411b5d853c8520c9ac629e429064e6514f21483273b0a790a41935d853c8520c9ec829e429064d6414f21483a3388a790a41d15c453c8520c98a7306429045e7598e214822e3aac710a41175db53885208baec29c429054c7355121482b238aa890a411b9d76348520a9ce729a42905667194d2148327b18a690a419358c5348520c9cec29a429064d7614d2148327b20a690a41935905348520e88a7b0a429074453d4521483a3a98a290a412b5d0604852099ae6302429064c53181214832629cc410a41d1d4d2108520c98a7316809064c5358b40482963aa85a0241c314d42d01208bce7b2a809045d73d95404822fb9acaa0241171cd6550120c98a7b12809064c5318940482963aa84a0241c314d4250120b50e0a12809045f76d4c404822ebb6a62024117dd853101208baec298809064f53988404832629cc4
  | 14 => 0xe6aa0651046d76d4c3288266bb6a619441729c3530ca20a9aeda98651064d76d4c32882a6ba6a619441535c7530ca20e94e1a98651058d7414c32882e2b88a619441729c0530ca20a9ceb218651054e7550c3288386aa2861944193d4d600ca208bce6322a31045d731915188327b1864a8c411ddd95114620c6ac8a88a31065563544518822fb9acaa0c41171cd65506208bce632a831045d73195418829a38aa8a0c41339cf6250620a68e8a8a831045e73d94418822eb9eca20c418dd954110620c6acaa0883106b14158041883273286598c419958a518c620ccac4a8c631043f74595318821e3a2ca98c410f9d0654c62087ae832a631074432545318832ab1ca310c419558d5188620a3ae62a6811053571153408826639ac5204410f9d85450220a3ae62a2811053571151408821fbb2a820441879516310220c3aa8b18811062e545884088316aa2c4204418d9516110220c6aa8b08811051d7414f30882aab88a798441179d8534c220a3ae829a61105557114d3088326298c498441339db324c220c3ac9298611045f7654c308830eb22a6184419394d620c220c9aa6b10611068d640c8308832b29ac2184419554d610c220d8864b0861104cc7359720882a7b9acb904419318f53c82208deeca9e411064e6354f2088237b92c7aa241179ce61d51208bae730ea89064e6358a544832631ec4aa24195d8f6155120ca8c7b0aa89063764185544832bb18c2aa2419518c6155120ccec430aa89066572185544821fbb2a82a2414d1c55415120aaee2aa6a69055471553534830fb24c9a9a41535c864d4d20caec330ea69054d72187534822fbb2a629a41175da5414d208beecaa0a6905577155053482aa38aa829a41535cb6414d20a9ae5320a69061d6419053482a6b90c829a41559c46414d20aaae2320a69055970190534828f3a6c429a41475d36214d20aace3b10a69055571d8853482a7ba2c429a4153dc56214d20a9ae5b08a69054d72984534828f3a0c229a41475d06114d20a9ae4308a6906556118453482acb80c229a419358b6014d20c9ac4b00a69046d72d974348237390cba1a4193d4e62d0d20c98a7316869046c7558b434832629ac5a1a411d9c76590d208eae3b2c869064c5398a43482363aac521a419314d6290d208dee4b2a869047771595434823a38acaa1a41479d35350d208ece2328869047571194434828eba0a621a419314e6210d208d8eab10869064c53588434832c29cc021a411e1d56010d208bceb31e849045c7558f424822fbb6a7a1241175db53d09208beec29e849045d7614f42482a739ca9212411b5d85390920c9ac629c849064e6514e4248326bb0a721241c39d05390920e1ae829c849064c53586424832629cc121241539ce54509208dcec2a2849046e75d8d42483862a6a6a12411b9da
  | 15 => 0x4552545300c3a3b12a29806195189514c030e88c4a8a601864462545300c30eaa6c0980619adcb654c030cd0e5b2a601863b65951300c31db2aa898061c6552534c030cd6cbb12601866b65189300c365b18c4980619ad96524c030cd6caa92601872954549300c3a529aa4980619cd96514c030ce6caa8a601873154545300c3a929aa298061d8549514c0308bce730ea99045d7398754c832731cc52a6419358e629532087eecaa0a99045f7654c53c823b38ecb21e411d5c76590f20c98a6b1487904767199543c823ab8ccaa1e41479d35350f208ece232887904757119443c82a739ca9216411bdd56390b20c9ac629c859043e7615142c8266b9ecaa1641539cf6550b20b52e1aa2859054e7395142c82373b0a8a16412b9d85450b208dced29a859052e7494d42c8266b98c0a1641395c46050b2087eecaa085906a94258042c8272b8ec919641179d8534cb20b92e1a9a659046e7614d32c82673b0a699641539d8534cb20c9cec29a659064f6414d32c8326b20a699641d25c0534cb20c98a7b0a65904ad7418132c8326298c099641395c4604cb208beeca9865906c93258032c831632284a8e411ddd951147208bce7b2e839045d73d9741c822f39ecb20e41175cf65907208bce7b2a839045d73d9541c822f39eca20e41175cf6510720d6282b00839043e74d9731c821eba6cb98e419314d62cc720aace3a9a63904cd73d9321c8256ba6c790e411bdd563c8720c9ac629e439054e7394721c8266b9eca90e41539cf65487208dcedaa243905647155121c82373b4a690e41599c65348720c9ac629a43905e170d4521c82a739ca290e41399d8514872095ae830243904cd7318121c837090ac010e41475ce54d0320a3ae72a2819045e7694d30c8327298c4986419354c624c3208baeda98619061d64d4c30c830eb20a61864193d4d620c32099aed190619068d648c830c832ba9ac2186419514d610c320d8c64b08619054c7358b548822f398c2aa441175cc615522087eecaa0a91061d5458c548831aaa2c22a441879916315220c9cc6b10a91064d63588548832b31cc22a4419558e6115220ccac5308a91063664584548832b31ac22a4419558d6115220ccac4b08a91067161980548822fbb2a629c41875915314e20caaa6b08a71061d6498c5388317322c429c418b5916214e20c6cc9308a710635649845388332b14c229c418d9916114e20c6ac8b08a710656635845388332b12c229c411d9c465d0e208eae232e871062e5458b4388316aa2c5a1c411d9c46590e208eae232c871047771595438823a38acaa1c411d9c46550e208eae232a871047671194438823ab88ca21c418795163d0a20c3aa8b1e851051d7414e32882aab88a719441179da534ca208baeda98651051d7414c32882aab88a6194411b5db540ca20a9e
  | 16 => 0xc31caa2c0208619a9496010430cd2a4b00821867251580410c338a8ac020861ac5056010430ce2a2b06621862e5498a310c316aa4c5188618b951628c430c5aa8b14621846f7694a310c236bb2a51886199989518c430ccac4a8c621863954980310c334a94c0188618e551600c430cd2a4b00621867251580310c21f3a4cb908610f5d265c8430c9aca196421870d540cb210c3a2192a3908610f9d2658843087ae932c421861e5498e210c30eaa4c710861879516388430c3aa8b1c421864e6394a210c326b1ca5108619398d5288430c9ac6a94421865563946210c32b31aa3108619558d518843087ce832a421843d74195210c22ebaec690861875536348430c3aa831a421864f63549210c32631aa490861935943248430e1aa8192421865763545210c32a31aa290861d10c9514843087ce9328421843d74994210c22ebb065280618755263900308beeab1c801861d5458e400c266392c7200619398d5290030c9ac6a94801865663546400c32ab1aa320061875526310030c3ca8b18801861d5458c400c236bacc4200618b9526210030c5aa9310801846f75588400c3172a2c4200618b55162100308daed290801864e63948400c326b1ca4200611bdd95210030c9cc6a90801864d63548400c23abacc2200618d9526110030c6aa9308801866652984400c332a94c2200611ddd56110030c6ca8b08801863554584400c333292c2200619954961100308eaed288801865663944400c32ab1ca2200619998a5110030ccac5288801847776544400c32b31aa2200619558d5110030cccc4a88801866562544400c2a6b96a998061555c754cc030c3aa9316601870d5494b300c22fbb2a5980619398952cc030e1ca8a96601870d5454b300c327bb2a598061c555251cc030e8aa528e601871654547300c38aaa2a398061d194951cc030e8aa4a8e601865662547300c22ebb4a7180611e5da538c030e52a8a94601873154546300c3b0a92a3180618b953624c030c5aa9b12601862e54189300c316aa0c4980611b1da524c0308dceca92601866762945300c332314a29806199d89514c030cc8c4a8a601864f72d95300c326396ca98061179db544c030a9ae5aa2601855571d51300c28ebaca89806187d96544c030c3ecaaa2601864f65d89300c386aa6c49806187550624c030c9eca312601870d54189300c326ba8c49806193d50624c030d1ca8312601864d54189300c346aa0c49806183550624c030998ed292601864f65949300c386aa4a49806193189524c030998eca92601864f65549300c3872a2a498061c3551524c030a9ceca92601854c76549300c3263b2a49806195d96514c030e2aa928a60186c462945300c3a2a94a29806193189514c030caecaa8a601871654545300c38aaa2a298061b1189514c030e8ca4a8a60187
  | 17 => 0x88614d9d05294430a6ae8294a218555758ca510c38aaa46528861d154a3294430e2aa8194a218745520ca510c31ab20c928861559cc6494430acce4324a21856572192510c2b9380c928861599cb4394430acae5a1ca21855673d8a510c2ab39e8528861555cf4294430e8a64194a21853674182510c29aba0c128861599c86094430acae4304a21846e72191510c236b90c8a88611d9db5454430acce5aa2a21856572d51510c23b3b0a8a8861599c85454430acae42a2a21847676d49510c29b3a6a4a88614d5d35254430e4ca9292a21872554949510c3a239ca4a8861c99515254430e4aa8a92a21874473549510c23b3b0a4a88614d9d05254430a6ae8292a218555758c9510c38b2a464a8861c55523254430e8ca5192a218745528c9510c38b2a064a8861c55503254430e8ca4192a218745520c9510c2aa39ac8a88618d5906454430aace6322a21856672191510c2b2b90c8a88615c9c06454430acce5a1aa21856572d0d510c2b938086a88615c5c04354430aace7b12a21855473589510c2ab39e84a8861555cf4254430aaee6a12a21855473509510c2aab8464a8861d14c83254430ae4e0192a218571700c9510c3a339064a8861d19883254430e8ac4192a218746420c9510c3a2a1064a8861d49c03254430aaae0192a218751700c9510c29b3a0c0a88614d5d06054430acce4302a21856572181510c29b3a060a88614d5d03054430acce4182a218565720c1510c21ebb4a8288610fdd95414430c5ca9310a21862d54988510c3172a2c4288618b55162144308daed290a21862e64948510c316b24a4288611bdd95214430c5cc8a90a21862d64548510c31b2a4c2288618d5526114430ccca5308a21866552984510c23bbb2a2288618d9915114430c6ac8a88a21866662544510c332b12a2288611b9ca65d04308dae532e821846e72996410c236b94cb208611b9c865504308dae432a821853471551410c22ebaec6a086187553635043099ce5b1a821861d5418d410c327b1aa4a08619318d5250430a68e8a8a821865763545410c32a31aa2a08611b9cb65104308dae5b28821846e72994410c236b94ca208614d5c65410430c3ca9318821861d5498c410c30f2a2c6208618755163104308daeb310821862e54988410c316aa4c4208611bdd56210430c5ca8b10821862d54588410c237bb4a4208611b5da5210430c9cc7290821864d63948410c237bb2a4208611b5d95210430c9cc6a90821864d63548410c29aba4a2208619598e5110430caac7288821866662944410c332b14a2208619598d5110430caac6a88821866662544410c332b12a2208614ddd54110430a6aeaa08821863765504410c31ab2a8220861c99494110430e4aa4a08821863954980410c335294c0208619a54a6010430ce2a3300821863a54580410
  | 18 => 0x155030a5ce4302a81852d72181540c29b388c0aa0614d5c4605503087eecaa0a81862d54988540c316aa2c42a0618d5526115030c6aa8b08a81862e64988540c32731cc42a0618b9916215030c9cc6b10a81863664984540c32b31cc22a0619998a6115030ccac5308a81863664584540c32b31ac22a061999896115030ccac4b08a81866962980540c338b0cc02a0618b95262d0c30c5aa9316861862e5458b430c316aa2c5a18618e5516090c30c74a8b00861863654987520c31aaa4c3a90618d95161d4830c6aa8b0ea41852e74d4a520c296ba6a529061599c75294830acae3a94a41856671d52520c2b2b8ea929061599c45494830acae22a4a41870d5418e520c2a739cc9290611b9db4394830a9ce730ca41852e74182520c296ba0c129061599c46094830acae2304a41846e76d51520c2b338ea8a9061595c754548308dcec2a2a41856671151520c2b2b88a8a9061c39506354830e1aa831aa41854e73991520c2a639ac8a90611b5db4354830ad4e021aa4185697010d520c2a739cc2a9061531cd6154830a5ce8302a41852d74181520c2b3388c0a9061595c46054830a5ce8182a41852d740c1520c21ebb4a8290610fdd95414830c5ca9310a41862d54988520c237bb2a4290618b9915214830c5ac8a90a41863654984520c31aaa4c2290619954a6114830c6ca8b08a41863554584520c332a92c2290611d9c665d08308eae332e841861d5498f420c30f2a2c7a10618755163d0830c9cc7296841864d6394b420c32731aa5a10619358d52d08308ece332c841847571996420c23b388caa10611d5c465508308baebb1a841861d54d8d420c30eaa0c6a106193d8d5250830c98c6a92841847671994420c23ab8cca210619a54960cc830c9ce4b2c641845d76d52320c2a6b96a919061555c7548c830c3acb2a4641861d65552320c326b2ca519061c3552528c830e1ca8a94641870d5454a320c30eaa2c11906193549608c830e1ca8990641870d544c8320c31caa4c0190618e551600c830cd4a4b00641854d72d50320c2aab8ea819061475d6540c830e1ce4aa0641870d72550320c30eaa4c419061535d6620c830e1aa9310641870d54948320c3872a2a419061c3551520c830a9eeca90641864f76548320c2a7ba2a41906153dc5520c830a9aeb210641870d54908320c2a6baa8419061c3551420c830e32a9300641861d54580320c38caa2c019061b2989600c830c5ca9316a21862d5498b510c3172a2c5a88618b55162d4430c5cc9296a21862d6494b510c317322a5a88618b59152d4430a6ce9a8ca21853574d46510c2b3396a328861595cb5194430acce5aa4a21856572d52510c2b3390a928861595c85494430a6ce9a94a21853574d4a510c3932a4a528861c95525294430e4ca8a94a2187255454a510c3a239aa52
  | 19 => 0x8292649864d64149324c326296c299261275d0604c9309aae230264986cb62181324c237394c9a8a611b5ca64d45308dceda92a29862f64d49514c316326a4a8a611b9d85254530c5ec8292a29862c64149514c23bbb2a228a614d1d151145308dee4b2e829846c72597414c327318a5a0a619358c52d05308dee4b2c829846c72596414c327318a520a619358c52905308dce5b2a829846d72d95414c237b92ca20a611b1c965105308dce4328829846d72194414c29ab88a820a6187d5163105308dceb310829846c75588414c237bb6a420a611b5db5210530c9cc7a90829864d63d48414c237bb0a420a611b5d85210530c9cc6290829864d63148414c32ab1ea220a614d5d05110530a6ceaa08829853475504414c393a928220a61c91494110530cd6a5300829866852980414c31daa2c020a618e1516010530cd6a4b00829866852580414c339a8ac020a619c1456010530d6282b00829845e75d93314c266b96c998a6117dd954cc530a98e4aa6629855471553314c326b10a598a619399452cc530c9aec296629864f6414b314c326b20a598a61d19c452cc530e8ae2296629864c52983314c2373acc518a611b1d5628c5308daeda94629846d7614a314c2a6392a898a61551c5544c5308bcebb12629864f62149314c3273b0a498a6193d90524c530c9ac8292629874452d85314c3a2296a298a61d1d48514c53093ae830262984cd72181314c326290c098a61d1d49310c530c9cc6296429864d6314b214c2a73ae6590a619398f5288530c9cc6294429864d6314a214c22f3acc690a61275d26348530acce3a92429864e63149214c326b18a490a61539d73248530c98cb992429843e74194214c21eba0ca10a619398c5208530c9ac6290429856571148214c334294c010a61471d543d0130c9cc6296809864d6314b404c386a18a5a0261471d54350130b30e0a1a809864f63149404c326318a4a0261c350c52501308deeda90809846d76d48404c32731ea4202619358f52101308deec290809846d76148404c327318a4202619358c5210130ccea5308809866452984404c333a92c220261991496110130c9ac4294609864d7614a304c327b20a51826193590528c130c98a4b0c609864e6358b540c32639ac5aa0619998a61d5030ccac530ea81865663587540c333312c3aa0619958961d5030a5ce5aa4a81852d72d52540c29b38ea92a0614d5c75495030a3ce7b14a81851e73186540c297390c32a0614b5c86195030c6ac230ca81853a70186540c297390c12a0614b5c86095030a6ce2304a81853571182540c297396c8aa0614b5cb6455030a6ce3b22a81853571d91540c237390c2aa0611b5c86155030a3ce7b12a81851c73589540c28e39ac2aa061479cc6155030a5ce430aa81852d72185540c31ab08c2aa0614e9c06
  | 20 => 0x563984548c333314c22a4619958a6115230c6cc8b08a91865563584548c333312c22a461995896115230ce2c3300a91862e5458b438c316aa2c5a1c611bdd95214a30c5ac8a90a51866552584528c30f2a2c7a14618755163d0a308eee2b2a851847471595428c23b388caa14611d5c46550a308baedaa0651854f72550328c266bb6a419461729c3520ca30b1ae829065185c571148328c2e5380a419461539d6420ca30e1aa8a10651846e72191518c236b90c8a8c6193d8832546308eeeca88a31863564544518c332b12a228c611bdc965506308d8e4b2a831846e72195418c236b90caa0c614d1c5545063099ce5b1a831853474545418c237396ca20c611b5cb6510630c6ecaa08831863565504418c358a0ac020c619958a518c630ccac4a8c631864e650cb218c32ab1ca310c619558d518863087ee8b2a431843c74595218c21f3a0ca90c610f5d06548630e8864a8a431852d72153408c29ab88a9a0461331c9639023087cec2a2811852d72151408c29ab88a8a04610fdd95410230c3ca8b18811861d5458c408c3172a2c4204618b5516210230c6ca8b08811863554584408c266392cb9846153dc965cc230c9cc4a96611846e72987544c236b94c3aa2619358e6295130c9ec6312a89866762d85544c332316c2aa2618dd906155130caec630aa89866762185544c332310c2aa261955cc615513087eecaa0a89853471550544c2373acc5a1a611b1d562d0d30a9ce52a4869854e72951434c22f3b0a8a1a61179d76250d3099ae430286984d571181434c2b3b8aa9a9261591c554d4930e18a8a1ea49862f64993524c2a6b98c9a92611b5db43d4930e1a8621ea49866761987524c2a6b98c3a92611bdd95214930a9ae5218a49854f7250c524c236bb4a8292611bdd95414930acee2aa0a49856471550524c2a73ac8629261c3d514314930a9ae7b20a49854d73990524c316b20c829261535cc6414930acce2320a49856571190524c2b4b80c8292614b9d36314930a5ae9b18a49856671d8c524c2b2b8ec6292611b5db4314930a9aed218a49870e6490c524c386b248629261535c64314930a9ce1218a49854f7650c524c387ba2862926153dc54314930a98e0a18a49854d73d84524c2a6b9cc2292614b9d06114930a5ae8308a49854d73184524c332b08c2292615a5c06114930c9cc7a96849864e6314b424c326b18a5a12619398c5290930c9ac6294849852e74d49424c23b388ca212611d5c46510930a5ae8290849864e63148424c326b18a4212619a14a6010930c9ee532e649845e75d93324c26ab8ec9992619399752cc930c9ec8296649864d6414b324c32732c8599261531d542cc930c9ccaa16649864c52587324c326294c1992619a14a608c930cd6a4302649854e75d89324c2a73b0a499261939d8524c930c9ec
  | 21 => 0x326a9ac5188811bdda528c4408daed294622046f7654a3110236bb2a5188819998a518c440ccac528c6220666625463110332b12a3188811b9c8654c4408dae432a622043d75d91311030fb22a69888187191534c440c5ec8a92622062c64549311031bb22a2988818d191514c4408dce5328622046d72994311022f39ccb90881175ce65c84408bce7b2c422045d73d96211022f39ccb10881175ce65884408baeb31c422045f7558e211022fbb4a710881175da53884408beeca9c422045d7654e211032731ca5108819358e5288440c9cc6a94422064d6354a211032b31ca3108819558e5188440cacc6a8c422065563546211022f398ca90881175cc654844087aebb22422061f6454d211030e322a6908818bd915248440c58c8a92422063764545211031a322a290881179ce65084408bae7328422070d5394b401038729aa5a0081c354d52d0040e2aa728e802072552947401038b29aa3a0081c554d51d0040e4ca4a8e802072552547401021ebb4a9200811e5da5490040e92a6a9480207525354640103a8a9aa320081d89495190040ec2a4a8c802061f6594d401030fb2aa6a00818bd965250040e1aa7292802062f65549401038729aa4a0081c354d5250040c6ecb28a8020715539454010392a94a2a00818dd955150040e2ca6a8a8020715535454010393292a2a0081c95495150040e64e0a8a802065b6594d401032db2aa6a0081c69515350040cd6cb292802066b6554940103952a2a4a0081d254d5250040ce6cb28a80206736554540103992a2a2a0081d494d5150040ea2a6a8a80207625254540103b0a92a2a0081cc9d15150040e66c8a8a802073151d054010237394c3aa6611b5ca61d5330c9cc7314a99864e6358a54cc21fbb2a82a661539ca5490f308beeab14879843e7615143cc266b96caa1e61539cb6550f30b32e1aa2879854e7295143cc22f3b0a8a1e61279d85450f3099ae430287984d57118143cc21fbb2a821e61a650d6010f30c3cc8a1ca59846f7654852cc23b38ecb216611d5c76590b309aae3b2665985c970d4932cc2673b0a499661275d0604cb309aae230265986c93258032cc30e32286a8e611ddd951147308dce5b2e839846d72d9741cc237396cb20e611b5cb65907308dce5b2a839846d72d9541cc237396ca20e611b5cb6510730d6282b0083984cd72d9331cc22fbaac598e61539ca51cc73099ae5b2a639854e72d9531cc22f3b6a898e61551c5544c730aace329263985d170d4531cc2a7394a298e61359d8514c73093ae830263984cd7218131cc36898ac018e610f9d365c873087ae9b2e439849d7498d21cc296b94a9a06614b5ca5450330a98e4b1ea91846e72185548c236b90c2aa4610fdd95415230c5aa8b10a91863554584548c326b1cc42a4618b9916215230c9ac6b10a91865
  | 22 => 0x811d5c6650c840a9ae5298642054d7394832102a7baa6419081535d5320c840c9eca990642064d654c8321032729cc5a88819354e62d4440c9ca6b16a22064d5358b511032731ca5a88819358e52d4440c9cc6a96a22064d6354b51102ab39ea328881555cf5194440acce5a8ca22056572d4651102b3396a728881595cb5394440acce429ca2205657214e51102ab39ea528881555cf5294440e8ca7294a2207455394a51103a329aa528881d154d5294440aace6294a2205557314a51102ab398c928881555cc6494440acce4324a2205657219251102b3396c728881595cb6394440acce5a1ca22056572d0e51102ab39ec528881555cf6294440aace7a14a22055573d0a51103a29906528881559cc6094440aaae6304a2205667218251102b2b90c1288811b9cb63544408dae5b1aa22045e73d89511022eb9ec4a88811d9db5354440acce5a9aa22056572d4d511023b3b0a6a8881599c85354440acae429aa22047676d4951102ab39ea4a8881555cf5254440e8ca7292a2207455394951103a329aa4a8881d154d52544408ecec292a2205567314951102aab98a4a8881599cb6354440acae5b1aa2205347458d51102b339686a8881595cb4354440ae4e1a1aa22057170d0d51102b938086a88815c5c04354440aace7b12a22055573d89511029a3a2c4a8881559cf4254440aaae7a12a22057270d0951102b8b8684a88815c9c04254440ae2e0212a220745320c951102ab398c0a8881555cc6054440acce4302a2205657218151102ab39880a8881555cc4054440acce4202a22056572101511022ebb4a62888117dd95314440c9ca7310a22064d53988511032729ac4288819354d62144408daed290a22064e639485110326b1ca4288811bdd95214440c9cc6a90a22064d63548511032b29cc2288819554e6114440ccca5308a22066552984511023bbb2a2288819598d5114440caac6a88a220666625445110332b12a2288819c54560d04408baeb318822045f7558c411022ebb4a62088117dd953104408daeb310822064e539884110326a9cc4208811bdd56210440c9ca6b10822064d535884110236bb4a4208819398e5210440c9ac7290822046f76548411032731aa4208819358d5210440cacc72888220655639444110333314a2208819958a5110440cacc6a888220655635444110333312a220881995895110440e2ca6a0882207155350441103932928220881c95494110440cb4a73008220659539804110335294c0208819a54a6010440ce2a3300822065a53580411032ca9ac0208819a9496010440cd2a4b008220672515804110358a0ac0208811b9ca65cc4408dae532e622046e72d963110236b96cb188811b9ca658c4408dae532c622046d7598a311032729cc5188819354e628c4408deeab14622064e5358a3110
  | 23 => 0x14540c9cc6b10a2a064d63588515032d31ac028a819658d6014540cd4c4b00a2a066962580515029d3a8c1a0a812b5cb635054093ae7b1282a053675d85415029b3b0a2a0a818d9d85150540e2ce628a82a0715731454150393390a2a0a81c95c85150540e62e028a82a049d731814150256b90c0a0a812b5ca64cc540aaae628e62a046e721963150236b90cb18a8193d4e628c540c98a731462a043e759913150256b94c898a8187195434c5408dee4b2862a046c725943150237390ca18a811b5c8650c540c6ac828862a049d7399321502b2b90a390a81179cc65885408bae632c42a064e63d4a2150327318a510a810f9d6644854093ae732242a062c65509215022fb9aca10a81171cd65085408bce632842a045d73194215031ab20a210a816a5cb43d0140b32e7a1680a06b161d074050257b92c72028127dcd6290140a9ce5a9ca62054d72d4e53102ab38ea729881555c75394c408dce530ca62046d729865310326b10c529881539ca6194c40a9ae530ca62054e7218253102a6b90c129881559c46094c40aaae2304a62054e7299153102a6b94c8a9881935886254c40a9ce530aa62054d72985531028e3a2c2a9881539c86054c40a9ae4302a6205567118153102aab88c0a988117dd95314c40c9aa7310a62064d53588531032aa9cc2298819554d6114c408daeb316862064e5398b4310326a9cc5a18811bdd562d0c40c5ca8b16862064e5358b4310326a9ac5a18819654d60d0c40cb4a6b00862065653987521032aa9cc3a90819594d61d4840caaa6b0ea42054e73d4a52102a6b9ea529081599c75294840acae3a94a42045e73986521022eb9cc329081599c75394840acae3a9ca4205667114e52102b2b88a7290819358c63948408daeda1ca42054e7398652102a6b9cc329081539cc6094840a9ae6304a4205667118252102b2b88c1290811b9db5354840acce3a9aa42056571d4d52102373b0a6a9081599c45354840acae229aa42054e7399152102a6b9cc8a90819358c63548408dceda1aa42056a7010d52102b4b8086a9081539ce6154840a9ae730aa42052c7458552102a7398c0a9081535cc6054840acce2302a4205657118152102a739880a9081535cc40548408baed298a42045f7654c521032729cc4290819354e62148408deeca90a42064e635485210326b1aa4290819594e6114840caaa7308a42066552984521032b29ac2290819554d6114840ccaa4b08a42045d7598f421022fbaac7a10818795163d08408baed29e842045f7654f421032731ca5a10819358e52d0840c9cc6a96842064d6354b4210334a92c1a10819654e6010840cb2a6b00842066a52580421023b38ccb990811d5c665cc8408ece332c642047571996321023b388ca990811d5c4654c840a98e4a9a642054c73549321023b38cca19
  | 24 => 0x31687a064d5398b43d0354b12c1a1e81639cb6350f40b1ce5a9a87a059970d4d43d024f3b0a6a1e812b5c86050f4096ae230287a06994358043d02a739ea529681179ce6194b408bae730ca5a046f7654852d032731ca5a16819398d52d0b40d32c6b0685a058e73d8942d02c739ea4a16816a5c35250b4095cec29285a049d7318142d025ab88c0a1681aa5096010b408ece3b2e65a047571d9732d0317322a5996818b99542ccb408ece3b2c65a047571d9632d030f322a71968187995438cb40a9ae529865a054d7394832d02a7baa6419681535d5320cb40b1ae899065a046e72d8d51d0236b96c6a8e81179cf62547408bae7b12a3a04777654451d0256b96c6a0e81275cf6250740b62e1a8a83a04b67614541d024eb98c0a0e812b5c86050740ce2a2b0083a06b14158041d0237396cb98e811b5cb65cc7408dce532e63a046d7299731d0256b94c998e811b9cb658c7408dae5b2c63a04ad7299131d02aa38aa698e8187195434c7408bce7b2e43a045d73d9721d022f39ccb90e81175ce65c874093ae732643a045e73d9621d022eb9ecb10e81275ce6448740ac8e2a9243a062c6550921d0237394c329c811b5ca6194e408beeca98a72054c7254c5390326a9ac429c819554d6114e40a98e4a9c872054c7254d4390278b88c0a1c81179ce6194a408bae730ca52046f7654852902a639aa4294819358d5214a40ccaa4b08a52054c7354a42902a639aa4a14813c5c46050a40a98e4a9e652054c7354a329023b388ca994811d5c4654ca40a98e4a9a652054c7354932902a63aa641948193d95320ca40c9aca99065206c932580329023bbb2a228c819558d5114640ccac4a88a3206b14158041902a6392a798c811b9cb658c6408dae5b2c6320665629463190332b12a318c811bdc9654c6408d8e4b2a632046e721953190236b90ca98c81531c9534c640a98e6a96432045e73d96219022eb9ecb10c819558e5188640caac6a8c432045f73595219022e39aca90c81179cc65486408bae632a432054c735492190297b92a7a048147dcd52d02408beeca98a6a054c7254c53502aa38aa629a813c5c46050d40b1ce5b1a86a04ad72181435025ab88c0a1a816c5c46050d408deeca90a4a054c7354852502b238aa4292813c5c46050940b1ce7b1284a049d73181425025ab88c0a12816c5c46050940c5ccaa1664a061e6550e325024eb9cc8992812b5ca644c940970e0b2264a047771594325023a38aca192811d9c4650c9408eae232864a061d6414c32502a6b90a6192818b590520c940a9ae629064a054e754c832502a63aa6419281635d1320c940d3286b0064a06a9425803250364992c0192811bdc963d45408d8e4b1ea2a045f7358b515022e39ac5a8a811ddd95114540aa8e6a88a2a056472544515032731cc428a819358e62
  | 25 => 0x7494c32486e2b8ca6192431bdd9530c92199eeca986490dc77154c32486a7bb2a61924393dd9530c921a9ee8a986490d4f7154c32487a3b8aa619243531c1530c921a9aeb2186490d4d7550c3248787aa2861924371dc5430c921c9aa6b006490e2c5458b414862f39ecaa0a43175cf655052199ce7b128290eb141580414872629ac598a430f9d3654c52187ae9b2a6290e4d650c9314866739ec910a43b198f51885218bce7326a090c5d73993504861f3a4c7a82430f5d263d41218f6eca80a090e1e6498c504870eb24c628243879916314121c3ac8b18a090e4f7258c5048726392c6282431b5db3214121c5ac9990a090e4d63cc85048716b2064282439358c32141218bce730ea810c5d739875408637396c6aa043179cc60550218bae6302a810c3f76550540870eaa2c62a0438e5516015021c3cc8b18a810e4e639885408726b1cc42a0439558e6115021cb4c7300a810e59639805408735314c02a0438e9916015021cb4c6b00a810e59635805408735312c02a0439c98560150218dce5324a610c3e74181530861eba0c0a984317dd95314c21c3ac8a98a610e5953580530870eb24c6298438b5926214c21c6ac9308a610e3a64980530871cb24c0298438e9916014c21c72c8b00a610e5a635805308735312c0298439c9856014c218dce432e8610c7a70197430863cb80cba18431b5d662d0c21c5aa93168610ce57198b4308637394cb218431e9c06590c218f2e032c8610c6d7598a4308637baac5218431d5d66190c218dce532a8610c7671995430863d380caa18431e5c06550c218dce43288610c7671194430863d380ca218431e5c06510c218bce7324a410c5d73992520862f39ecb21043175cf6590821c6aa930c8410c3e74d96320861eba6cb190439554e618c821a9ae72906410d4f754c8320862f39ecb20843175cf65904218deeab148210c5e73d94410862eb9eca20843179cc65104218bae63288210e1e5458c410870eaa2c6208438b5526210421c74a8b008210e39545804108758a0ac020843539cb53cc421a3ae829e6210d597014f310872729cc5188439354e628c421a9ce5a9a6210d5671d4d310862f3b0a698843475d0534c421ab2e029a6210c3e74194310861eba0ca1884317dd9530c4218deeab106210d2d7414f21086b4b80a7908431b5da5288421c9cc72944210c757694a21086373b6a8908431b9d85348421a5ae829a4210d697014d21086a739ca290843595d44148421e4aa820a4210dc57310521086f0b808290843595d63148421e88a698a4210dc573d8921086b2bae8490843715cf4248421aceea9924210c5e73191500862eb98c8a80430f9d0635402187ae831aa010c7b76540500871cb22a0280439658d5014021a9ce5a9ca7a046e7298653d0236b94c329e8117dd95314f40c9ca7
  | 26 => 0x3930ac02a443569c05494e21ab2e02a4a710d4d72d9253886a6b94c929c43875906494e21aace2324a710d1e74d8a538868eba6c529c43479d06194e21a3ae830ca710d5a7018653886acb80c329c4353dc96094e21a3ce8304a710d1d7418253886a6b90c129c43559c46094e2187ce8302a710c3d74181538862f3b6a8a9c43179d85454e21ab4e02a2a710d597015153886a6b94c8a9c43551c56454e21c3ac8322a710d567198153886a7b92c0a9c43479d06054e21a3ae8302a710d4d7218153886ab388c0a9c4317dd95314e21ccac5308a710c7a70197438863cb80cba1c439394e62d0e21c9aa73168710e4e5358b4388726a9ac5a1c439394e6290e21c9ca6b148710d1c7454d438872aa9ec2a1c439554c6150e218f4e03288710c7970194438868eba4a621c439594d6110e218baeb31e8510c5f7558f428862ebb4a7a144317dd953d0a21caaa7b0a8510e3554185428872aa98c2a1443c354d4210a21caca6b0e6510e5553d85328872729cc520c439394d62906218baeb3188310c5f7558c418862ebb4a620c4317dd95310621c9ca73108310e4d539884188716aa2c420c439394d6210621c9aa6b108310f1653504418878aa9a8220c439694e6010621cb2a73008310e3a54580418871caa2c020c439694d6010621cb2a6b008310eb141580418872729cc518c439354e628c621c9ca6b146310e4e53988318872729ac418c43539cf54c8621c9acb29e4310e4d6554f218872ab2ca790c439559553c86218bce6322a110c5d73191508862ebb4a628443879925314221c3ac9298a110c5f7654c508870f322a6284438759153142218f6eca80a110e3964540508870faa2c72a2439398d62951218bce7b12a890c5d73d8954486a739ec4aa243179cc60551218bae6302a890c3f76550544868eb9cc82a243875935394d21c5ae5324a690e2e6458a534871b322c329a430f9d06054d2187ae8302a690c5f7654c534868eba4c629a431b5cb65d0d218d8eab168690e2f5458b43487162a2c5a1a43391c562d0d218dae5b2c8690c7571d96434863db82caa1a431e1c16550d218dcebb128690c7675d85434863d380ca21a431e5c06510d218d8eab108690c7475584434870faa2c7a12438715163d0921c68a8b0e8490d4e73952424867338cc7212431b5da5390921a5ce929c8490cce7398642486973aec8a12434b9d25450921a9ce72a28490c6e7615142486973b0a8a12438b9d85450921a5ae02a28490c6e7694d42486973a4a6a1243399d46150921cccea30a8490ce57018542486373aec999243399c764cc9218deecaa66490ce67598732487333acc399243395c261cc921a3ae929c6490c5e7614d324868eba4a619243535ca530c9218beeca986490c6e75d90324867238ac819243535cf540c9218deecaa06490d8d
  | 27 => 0x631e5c065109319ace3b246498cd675986324c72b3acc319263355c2618c9318bcebb206498cd471590324c6a6b96a81926317dd9540c931b1ae92906498dc571948324c667bb2a41926371dc5520c931a9aeb2106498f0f54508324c6e3b8a84192638715163d053199ce5b1a8298eb141580414c667396c918a63b198b518c5318dce5326a098c6d72993504c61f3a4c5a82630f5d262d41318f6eca80a098e2e64988504c716b24c4282638b9916214131c5ac8b10a098e4f73588504c72639ac428263175da3214131c3ac9190a098e4d628c8504c70eb2064282639358832141318dce4302a818c6d72181540c61fbb2a82a0638b5516215031c72a8b00a818e4e63988540c717322c42a0639398d6215031ccac5308a818e5a63980540c735314c02a0639a58a6015031c74c8b00a818e5a63580540c735312c02a0639a5896015031ce4c2b00a818e3554986430c61f3a0c0a90630f5d060548318deeca90a418e2d64548520c734a92c0290638755263d08319aae331e8418c5f7558e420c63d380caa10631e5c06550831a9eea9906418c5f7558e410c70eaa4c6208638b9516210431c5aa8b108218e3a54580410c71caa2c020863ac50560104318baed29c6218c757694e310c62f3b6a898863555d4414c431e2aa820a6218dc572105310c6e8b808298863715cb634c431aaaeba1a6218dc572d0d310c6abbaa64988631b9c864540318dae4322a018c3e74189500c61eba0c4a80631edd95014031c72c8a80a018e6962540500c726392c7aa6439358e62d5321cacc6b0ea990e666258754c868f39ea92a6439398e6295321c9ac7314a990d1e73d9154c862f398c0aa643175cc605532187eecaa0a990e1d7399353c8716b24c5a9e438d99161d4f21a3ce9a9ca790d1e74d8d53c861f3a0c0a9e430f5d06054f218beeca98a790e666258453c872729cc5a1e439354e62d0f21a3ae72a48790d1e74d4e43c8672b94c321e43479d35350f218bcec29a8790c7a7019443c863cb80ca21e4317dd95310f21a9ce72a48590cce7398642c86a739ca8a16431b9d85450b21a5ce929a8590c6e7614d42c871b2a2c221643399c764ccb218daedaa66590d4d73d5332c8696ba6a7996439594d610cb21a9ae7aa06590d2d74d4c32c8637bb2a61964353dd9530cb21c9eeca986590d4f7454c32c86a6382a619643535d6430cb21e1aa92186590dc57190c32c86a6baa86196439354d600cb2199ce7b128390e2d5418941c8758a0ac020e439354c624c7218daec194a190c7b7654050c872731ac5aa4439558e61d5221ccac530ea910c5e73181548862eb98c0aa4430fdd95415221c72a8b00a910e4e635885488726b1ac42a4439698e6015221cb2c7300a910e6962980548871d322c02a4439698d6015221cb2c6b00a910e696258054887
  | 28 => 0x5331a9ce52a48798cce7298643cc6a7394a8a1e63179d85450f31c6ca8b088798d2e74d4a52cc70f32287296630f9d06054b3187ae8302a598c6f7654852cc72731ca5a16639398d52d0b31a5ae52a48598cd57398642cc66b38ec919663175db548cb31a9ae5aa46598d4d72d5032cc6a7bb2a41966393dd9520cb31a9ee8a906598d4c7054832cc6a6bac8419663c3552420cb31b8ae32106598d4d7550832cc726a92c019663339cb6350731c3aa831a8398eb14158041cc62ebb065286631edd95014331c9ac7316a918e5563987548c732b14c3aa4631b9c860552318dae4302a918c3f76550548c71caa2c02a4639358e6215231c9ac6b10a918e5963980548c735314c02a4639a58a6015231c74c8b00a918e5963580548c735312c02a4639a5896015231ce4c2b00a918c6d7598b438c637baac5a1c638d5506150e31ad4e02a4a518d6970152528c6a6b9ec929463535ce6494a31c5ac8324a518d6671192528c6973a6c7294634b5d36394a318daeda1ca518d2e74186528c696ba0c3294635a9c06194a31ad2e030ca518d4f73582528c6973a0c1294634b5d06094a31a9ae6304a518d6671182528c61f3a0c0a94630f5d06054a318dcedaa2a518c6e76151528c6b5380a8a94635a5c05454a31a9ae7322a518d6471591528c716b20c8a94631b9db4354a31acee2a1aa518d647150d528c786a1886a9463599c66054a31a9ee6b02a518d2e74181528c696ba0c0a9463535cc6054a31acce2302a518c6f76548528c72731ca5a14639358e52d0a31c9cc6a968518e4d6354b428c72731ca5214639358e5290a31a58e8a928518e6552d85428c732a90c2a14634b5d25210a31ccca4b088518e6652586328c732a96c2994639398e5290631c9ac72948318e1d5458c418c636bacc420c631bdd562106318daed2908318e4e63948418c726b1ca420c631bdd95210631c9cc6a908318e4d63548418c7932928220c63c95494110631cd4a53008318e6952980418c71d2a2c020c638e5516010631cd4a4b008318e6952580418c758a0ac020c63539cb54cc631c9acb2966318e4d6554b318c732b2ca598c639959552cc6318dce4322a118c6d72191508c636bb4a4284638b9925214231c5ac9290a118c6f76548508c717322a4284638b59152142318f6eca80a118e3964540508c717aa2c52a2639358e6295131a9ce5b1aa898c6e72181544c636b90c0aa2630fdd95415131a5ae5320a898e2f5458b434c7162a2c5a1a638d15161d0d31a9ce52a48698cd67198a434c667394c321a63479d76450d31a3ce92a28698d4e72951434c62f3b0a8a1a63479d85450d31c3cec2a28698d1d70151434c66b3a8c2a1a63959d46150d319aae030a8698e2d64d4a524c637bb2a42926387d5163d0931c38a8b1e8498cd47158f424c63d380ca212
  | 29 => 0x9aa020d697214d501063d3b6a4a8083569cf5254041ab2e7a92a020f4a5394950107a4a9ca4a8083d294d5254041e92a6a92a020c7a7614950106ad398a4a8083565cc5254041e34a7a0aa020f1953d05501079529682a8083ca54b4154041ea4a720aa020f515390550107b129482a8083d854a4154041a76eaa0aa020f1a53505501078ca9a82a8083ca9494154041e52a4a0aa020d737550550107a929a82a8083d454d4154041ec4a4a0aa020f615250550106d9baa82a8083ccdd54154041e66caa0aa020f3353505501079929a82a8083e494d4154041e24a6a0aa020f315350550107c8a9a82a8083c454d4154041e60a6a0aa020f3352505501079929282a8083e89494154041e44a4a0aa020f315250550107d0a9282a8083c85494154041e60a4a0aa020d387458d50106b5b92c6a80835a1c96354041ae0e2b1aa020d3a7418d50106b5390c6a80835a5c86354041ae4e231aa020d6a72d0d50106b4b9686a80835c9c74354041ae2e3a1aa020f194310d50106b938886a80835c5c44354041a70e8b12a020d5b7358950106ac39ac4a80835c1c56254041a74e8312a020d5a7318950106acb98c4a80835c9c46254041ab4e7a12a020d5973d0950106b938e84a80835c5c74254041e5284212a020d727110950106b8b8884a80834e9d33254041a72e9992a020d7271cc950106b8b8e64a80834e9d23254041a72e9192a020d72718c950106b8b8c64a8083d24c83254041e66e2a0aa020f32615055010799ba282a8083cc9914154041e6686a0aa020f32435055010798a1a82a8083cc10d4154041e6684a0aa020f32425055010798a1282a8083cc1094154041e66eca0aa020f32765055010798bb282a8083cc1d94154041e66e6a0aa020f32735055010798b9a82a8083cc1cd4154041e66c6a0aa020f32635055010798b1a82a8083cc18d4154041e66e4a0aa020f32725055010798b9282a8083cc1c94154041e66c4a0aa020f32625055010798b1282a8083cc1894154041e6664a0aa020f3232505501079899282a8083cc0c94154041ab4e620aa020d597310550106b539082a80835a5c84154041e628220aa020c5d7694c501062fbb2a6280839394e6214041c9aa7310a020e4e535885010726a9ac4280831b5da5214041c9cc7290a020e4d639485010637bb2a4280839398d5214041c9ac6a90a020cb776504501074b31a8228083a558d4114041d4cc4a08a020ea562504501072d29cc0280839654e6014041cd4a5300a020e69529805010758a0cc0280831edd95014041cb4c6a80a020e59635405010735312a0280839a5895014041e6282a80a020e4e6358b54cc72639ac5aa6639598d61d5331cccc4b0ea998d2e72d5254cc72731cc52a6639398d6295331a5ce5b22a998c6e7218154cc636b90c0aa6630fdd9541
  | 30 => 0x554941107a2a9aa4a0883659cf4250441b2ae7a128220e3575d95411071b3b6caa08834d5c36550441b4ce5b1a8220da572d8d411069abacc6a0883699ca6350441b4ae531a8220d377558d411074ab18c6a08832d9db5350441b4ce5a9a8220da572d4d41106d9386a6a08836c5c35350441b2aeb29a8220e976594d411078bb2ca6a0883c5dd55350441d2ecaa9a8220f176554d411065b3b0a6a0883659cc5350441b4ce429a8220da57214d41106d9380a6a08836c5c05350441b2ce7b128220d9573d89411069abacc4a0883659ce6250441b2ae73128220d37755894110752b10c4a08832d9db5250441b2ce7a928220d9573d49411078aa9ea4a08836c9c35250441b62e1a928220da5759494110753b2ca4a0883c9d965250441f0ca72928220f8553949411078aa9aa4a0883c9dd55250441d4ecaa928220f27655494110793a9aa4a0883e194d5250441e4aa6a928220f85535494110782a9aa4a08832d9d85250441b2ce62928220d957314941106d3390a4a08836c9c05250441b62e02928220cb676cc9411065abb664a08832d9da325044196aed1928220d36750c9411069aba864a0883e14c83250441a6aeb3028220d377558141106cbb9ac0a0883651cd6050441b4ee4b028220da47258141106cb398c0a0883655cc6050441b4ce43028220da572181411072729cc5a80839354e62d4041c9ca6b16a020e4d5358b501072731ca5a80839358e52d4041c9cc6a96a020e4d6354b501065bbb283a8083a598d41d4041d2ac6a0ea020f1653507501078aa9a83a8083a998941d4041d4ac4a0ea020f26525075010792a9283a8083569cf5094041ab2e7a84a020d6a72d4250106b4b96a1280831bdc963940418d8e4b1ca020c5f7358a501062e39ac5280835a9cb5394041ad2e5a9ca020d6a7214e50106b4b90a728083569cf5294041ab2e7a94a020f4a5394a50107a4a9ca528083d294d5294041e92a6a94a020d5a7314a50106acb98a5280834edd54194041ae6eaa0ca020db3755065010799baa8328083e494d4194041f22a6a0ca020fa25250650107d0a928328083569cc6494041ab2e6324a020d6a7219250106b4b90c9280835adc96394041ad0e4b1ca020d3a7418e50106b5390c7280835a5c86394041ae4e231ca020d6a72d0e50106b4b96872808356dcd6294041ab0e6b14a020d3a7418a50106ad398c528083565cc6294041ae4e2314a020d5a73d0a50106acb9e8528083d24c83294041ab4e630ca020d597318650106b5390c3280835a5c86194041e2ca6a0aa020f1553505501079329282a8083c954941540418dce431aa020c6d7218d501062f398c4a8083175cc6254041c6eeca0aa020e34765055010799b8282a8083cc1c141540418f4eda9aa020d6a72d4d50106b4b96a6a80831e9d85354041ad4e42
  | 31 => 0x7394c329883535ca6194c41a9ee4b04a620d4c72582531068f3a0c129883539c86094c41a9ae4304a620d56711825310637390c0a98831b5c86054c41a9ce5322a620d4d72991531068f3a4c4a9883559c66254c41c9ac4312a620d4e7298553106a6b94c2a9883471d16054c41a9ee4b02a620d4c7258153106aa38ac0a9883479d06054c41a9ce4302a620d4d7218153106ab388c0a988317dd95314c41c9aa7310a620e4d53588531072ca9cc0298839654d6014c418daeb3168620e4e5398b4310726a9cc5a18831bdd562d0c41c9ca6b168620e4d5358b431072aa9ac3a18839594d6110c41d2a86b088620e5a53983521072ca9cc1a90839694d60d4841cb2a6b06a420d4e73d4a52106a6b9ea5290835a9c35294841ad2e1a94a420c5f73582521062e39ac1290835a9c35394841ad2e1a9ca420d6a7014e52106b4b80a7290834b9d36394841acce3b1ca420e4d6318e5210636bb68729083539ce6194841a9ae730ca420d4f7358252106a639ac1290834b9d06094841a9ce6304a420d4d7318252106b3388c129083179cc60548418bae6302a420c6e76d4d52106b5386a6a90835a5c353548418dcec29aa420d6a7014d52106b4b80a6a9083539ce6454841a9ae7322a420d2e7498d52106b338cc6a90839358c63548418dceda1aa420f0d4310d52106b338886a9083595c44354841a9ce730aa420d4d7398552106a739882a9083535cc4154841a58e8b02a420d4f7358152106a639ac0a9083591c56054841a5ce8302a420d4e7318152106a6b98c0a9083599c460548418baed298a420c5f7654c521072729cc4290839354e62148418deeca90a420e4e635485210726b1aa4290839694e6014841cb2a7300a420e6952980521072d29ac0290839654d6014841cd2a4b00a420c5d7598f421062fbaac7a1083175da53d08418beeca9e8420e4e6394b4210726b1ca5a10839398d52d0841c9ac6a968420e65525874210786a9a84210839554e6110841caaa6b088420e66525844210752a12c2210831e9c265cc8418f2e132e6420cb571993321070eb24a7990838b99152cc841c5ac8a966420cb5749873210732a94c3990839594d61cc841ccaa4b0e6420c7a70996321063cb84cb190832d5c6648c841c3cc8a9c6420e1d6454e3210716b24a5190832d5d2618c841caaa730c6420e55535863210733292c3190831e9c0654c8418f2e032a6420d4c7254d32106a639aa4990831e9c2650c8418f2e13286420d4d7294c32106a6b9ca41908353dd5320c841a9aea9906420e4f654c83210726b2a6419083c354d52d044187aed2a48220c757695241107a2a9aa52088387d965350441c3ecaa9a8220e2f659494110717b2aa4a0883c354d5250441caecb29a8220e576554d41106d339686a0883695cb4350441ccecb2928220e676
  | 32 => 0x5331c1644c83299cec32264194ce76d51320ca673b4a899065a3d92544c83299cecaa264194cd76551320cb47b22a899065339d8544c832e1aa82a264195c671151320cae2b88a899065729c0544c832b92e02a264194cd74d85320ca67386c299065535d6614c832a9eeab0a641954d75981320caa7baac099065639d0604c832b1ae830264195c671181320cae2b88c099065935d4604c832d1ce830264194cd74181320cb46ba0c099065235d0604c832d8ce230264194cd71181320cb62b88c099065315c4604c83299eec996a2194cf764ca510cae3b8a652886533dd93254432b8ee2992a21947a70191510ca3cb80c8a8865871914354432c58c8a12a21943e74181510ca1eba0c0a886533dd93214432d1cc8990a21968d644c8510ca3bbb2a2288658d5915114432e8a64a88a2196c932980510cb64992c0288659c545601443299eec996a0194cc764ca500cae43826528065331d93254032b90e0992a01947671191500ca3ab88c8a8065535ca4354032a9ae7212a01955a70cc9500cab538464a8065561c13254032ad0e0992a01964f764c9500caa63b264a8065931d93254032a9ee8992a01954d744c9500caa7b8a64a8065d2dc13254032a98e0992a019748704c9500caa438264a80650f9d0615403287ae830aa0194cf764c8500cb473226428065a35913214032d8a65308a0196c532584500ca3dbb2a0280658e5915014032ce2c2a80a01954e72d4e53d0637390c0a9e831b5c86054f418beeca98a7a0e4e5398b43d0726a9cc5a1e83539cf5294b418bce6302a5a0c5d7318152d0637bb2a4296839398e52d0b41c9cc6a9685a0d4d7294c32d06a6b9ca41968353dd5320cb41a9aea99065a0c6f7258e50d0636392c72868317dcd62943418b8e6b14a1a0c7b7654050d06a7396a729c831b9c86054e418dae4302a720c5f7654c53906a739ea529483179cc6054a418bae6302a520c6f7654852906a6b94a619483535ce520ca41a9eea9906520d4d754c83290637b92c7284831b1c963942418bee6b14a120c5c7358a509063dbb2a028483539cb5394d41c9ea6b14a6a0c5f7654c5350637b92c029a831b1c96014d41a9ce5a9c86a0d4e72d4d43506a739ea5292839358f52949418deeca90a4a0c5f73580525062e39ac029283539cf5290941a9ce7a9284a0d4e72d4f32506a739ea519283539cb534c941a9ce7a9264a0c7a70194325063cb80ca192832d1c5640c941a9eea99064a0e4e654c8325072632a64192832d1d1610c9418dce531ea0a0c6d7298f505062f39cc5a8283175ce62d41418f6eca80a0a0e4e639885050726b1cc4282839398d6214141c9ac6b10a0a0d4e72d4e53106a6b96a729883569c35394c41ab2e1a9ca620c6f725825310636392c129883479d36294c41aace3b14a620e4d6218a53106a
  | 33 => 0x428bae630aa02147b765405010b2cb1aa0280859c5855014042c9cc6b16a9996656298754ccb32b94c3aa6659598d61d5332a6ce3aa4a99953671d9154cca3b388c0aa6651d5c4605533287eecaa0a99964e6358854ccb172a2c421e658755263d0b328dced2a2859952e7695142ccb173b4a8a16654b5c25450b328daea30285994cd7318142cca72b88c0a16654d9d3519473287ce8302a39943d7418151cca3bbb2a228e651edd95014332c9ac7316a91965563987548cb2ab9cc3aa4659998961d5232a6ce3aa4a91953671d91548ca3b388c0aa4651d5c4605523287eecaa0a91964d63988548cb16aa4c5a1c65179da5450e32a3ced2a2871961e76951438ca8eb84a8a1c65175d46050e3299ae430287194d571181438cb0f2a2c621465355c764cca32acae3aa6651953674d46518ca1f3a0c0a8c650f5d060546328eeeca88a31956970cca508caad38664a84651edd950142328ece2302a89947571181544ca1fbb2a82a2658bd5162d0d32c3ccaa18869961f5458f424cb1732a84212651ddd951145328f6eca80a09962d64cc8504cab4b866428265875923214132ab2e1190a09963664984504cb1ab24c2282658d9916114132c6ac8b08a09966732584504cb2b192c2282659398e62950328f4e030aa81947970185540ca3b388c0aa0651d5c4605503287eecaa0a81963554584540cb1caa2c02a0658d9916115032cacc6b08a81966662584540cb3930cc02a0659c5866015032c74c8b00a81965a63580540cb35312c02a0659c9856015032ce2c2b00a81962d5498a430caaab88a921865565c05490c328beeab1486194cf7558a430cb27baac52186533dc56290c32998e0b14861945d75982430ca2f3b0a8a1865555c45450c32ab2e02a286195c571989430caa7baac4a1865335cb6150c3299ae430286194d571181430cb0f3228729065875526390832acae22a4841956970152420ca37baac72106533dd56390832c9eeab1c84194cf7158e420ca66382c721065535d64390832c9acb21c841970e5490e420cb26b2a87210651b5d660908328dcec2a2841956571151420cab4b80a8a1065715c66350832a9eeab1a841952e7494d420caa6bac86a1065c3151435083299ae7b0a84194cd73181420ca72b88c0a1065355c764cc832d1ac8a16641945d7694e320ca72b8ec9190651b5da538c832d1ac8a1c641945f75591320ca673b68499065a3d91424c83299cec212641949d74181320ca6ab88c0990651bdd5644c83299ceda1a641968f6450d320ca673b086990652b5d0604c8329cae2302641964d75d95320ca66ba6ca99065335c7654c83299ce1b2a641964e76d95320caa6b86ca99065335c7644c83299ce1b22641954d75991320caa7baac89906533dd5644c832c9eeab22641968f74591320ca67b8ac89906
  | 34 => 0x2a5a1d657118152d0e37bb2a4296871b9c860547438dae4302a3a1c6d7694851d0e37bb2a428e871ddd95114743cd4a5300a3a1e695298051d0f35292c028e879a5496014743ce2a2b00a3a1c6e7218550d0e36b90c2a86871b5da52143438deeca90a1a1e665298450d0f32a94c228687999496114343ccaa4b08a1a1c7b7654050d0f38b0aa0286878b59662d0e43c5acab168721e4d6598b4390f26b2ac5a1c87599c75294a438ece2302a521c75711815290e37bb2a429487599cb51946438dce4302a321c6d721815190e3bbb2a228c871edd95014243b1ce5a9c86a1e67525865250e37bb2a4292879958b51945438eeeca88a2a1c767198b5050e3ab8cc5a82871b9ca61d41438dae530ea0a1c7b765405050f27b9ac428287931cd6214143cccc5308a0a1e65629845050f33312c22828799589611414387aed2a48621c5d769524310ec6b94a8a18871d9c460548438eae2302a421c6f765485210f32a92c2290879a54960148438dce4302a221c6d721815110e3bbb2a228887995895114443ce2a2b00a221c76711895010e3ab88c4a80871b9c861540438dae430aa021c7b765405010f34b12a0280879c5855014043aace2324a7a15557119253d0aad380c929e85565c06494f42aace3b14a7a155571d8a53d0aa6b96c329e85535ca6194f42a3ce830ca7a16556118653d0aa7b92c129e85479d06094f42a9ae4304a7a15567118253d0aaab88c129e851d9c46054f428eae2302a7a154d7298553d0a8e3a2c2a9e85955846154f42a3ce9302a7a154f7258153d0a8f3a0c0a9e85535c86054f42aace2302a7a15557118153d0a2fbb2a629e859354e62d0f42c9ca6b1687a164e5398843d0a2f398c0a8e85175cc60547428baed298a3a145f7654c51d0a3bbb2a228e859694e6014742cb2a7300a3a165a5358051d0b2ca9ac028e859c54560147428bce630aa1a145d7318550d0a2ebb4a62868517dd95314342caca7308a1a16555398450d0b2b29ac2286859554d61143428f6eca80a1a16716154050d0aab38ea729c851d9c46054e428eae2302a72145f7654c5390b0eb2cc7a14858759563d0a42c9acb31e852164d6558f4290aab39ea328c85179cc60546428bae6302a321477765445190a3dbb2a02848595d4d6194d428beeca98a6a158e73d4a4250b2ab1ea328a851ddd951145428ece331ea0a14757198f5050a2f39cc3a8285175ce61d41428f6eca80a0a164f7258c5050b26392c6282859598e6114142caac7308a0a1656635845050b2ab1ac2282851d9c46054c428eae2302a62145f7654c5310b2aa9ac2298859654d6014c42c9ca7316862143d769524210a36bb4a921085635ce54508428bce6302a22145d731815110a3bbb2a2288859558d5114442ce2a2b00a2214767118d5010a3ab88c6a8085179cc6154
  | 35 => 0x4012000400100140000004004000000200080020000002000800300200000018000000401d004c000001401200280010008000000000400180190004000000c00b000c00600100000000003001400000040040008001000c01f00000000008004000000300040010004002000400c000400400780010024003001400d000c0140004002003c00000000010010013001c001000000100000000000005000400500080020000003000000000080150008036000000100000080030000000c00100080010000005000c002000c00b0000002001800a0010000001401000080040004008000800400140030000001000000b00080000000001003c0000000000000000200040120004004003400000000050010001000c0000004000003000c003c005000801100000020010001000c00c001c0130008000001800600140020004009000000400040000000005001001800380010000007000800c00240060028001001c00e00600000014002000400600500040004009000000200000030028004000c00000040010000000000800100140000014000001800200000010018000008400400000040004006001c00000040010014004000800100000090004000000000000000000010002000c0060000014001c002003c01d00580020018000002400b00100040000000001c0010004005002c0010004002005000300040050048006000000a000000000000010038006002800300000000048004000000d000000e0020000000001a001800300080000000004000400d00040090000001001c001007c003001400800100020008007000000e0024008000800d000800e000000e000800400040040004001000c00200080010000001001c0010000006001c0000000000000000100000000004000001c00200100030000007000c0000000000000000b00000020000006000000100000000000004000000100000070040000000000500000090000012000c013000000a0008004001000a003c00f001800200080020000004000c008000000300080000030000001000800080000008009000000200000050004000000000200140010034003000400000040000000003002c0010020008001000f0048005000000200240010004003000000000040000000014003000000000040018009000c00d0014001000c01300280060018000000000000380000010000000001aacce2324a5a1d657119252d0eb5380c9296875a5c06494b43acce3b1ca5a1d6571d8e52d0ea6b9ec329687535ce6194b43a5ce830ca5a1e656118652d0ea7b9ac1296874b9d06094b43a9ae6304a5a1d667118252d0eb2b88c1296871d9c46054b438eae2302a5a1d4d7398552d0e963a2c2a9687995846154b43a5ce9302a5a1d4f7358152d0e973a0c0a9687535cc6054b43acce230
  | 36 => 0x100020000000000c0030000000003c00100040000090001000800400340000004002000800200000020004000003000900000010000003000000a0018009000000100000010018001000c008003c013000c01f00000000004009000401600000050010005001800000340120000000003c01b0000003005800000000000000000000000700000010020008001000000200020004000000000000080000004000001000800100140008000000400d0000001000c0040004000000800100040020000000002c0020000010001400100000070028001000000300240010004000001800000000000000001000000000040070020008000c003002c0000000000006800c0000000001000c002c000001400400180000004008000002a00000000010002001800b0014001000000100040030008000005c00e000401a00200030000006002c001002c0010008000001400900000000070009000c0020000001000000700000000000000001000400000070000000000800f00080000034001003c008002000000000030008000001400e00780040000000000400600000010000000000800200080000034003000000400000040000001000001000000030000001002800000000000028004006c000001801c000c000000c00500400040000000000000a0000001002400d0000001000400c000000900200010008000000800100080010000001001c000000c00100140080010000008c000001400600000030008005003c0050010021003000000000040018000000000300140060000001000000000080000020002000800100000000010005003c000000000b0014000000000500000190000000000400000040000000001000c000000800100000010010013001000800100040020002000402900040000018000000c00100040000000005000c00d0010015002c0050008000000c006000c00000000000064002003c002001800000080030008004000c000002000c000800600080040018005001400d00280000004002000400100a800400100000010007000c002000400400000000000000000400400000000008012001000c0000000000400500300000014000002800000140020000003000000000040050000003003c000000800f0004002000400500100130000001006c0010000008000001200040030004001002c00000000000004000000400c00180090020000000000100000010014000000802c0070000001c00000140080000002001c0040010010000c000000c0070004000000002000100000044002000001a00000020000007000400500040010000009004c00c004800c00000160010001000400a0000000001c003002c00000000000024008000801400180040000001000800300240000004009000c00300100180000006000
  | 37 => 0x200440060008000000000000100040000002000800f00000010004004000c0020044002000000d0070007001800700040040008000000400000000040000002000c0010020000000000200100010048000000c00100140080004000008800c000000d000c00500040080000001006c000000001e0008005003000e000c001001000b00000000004001000c002000400200000000008004000c00000000130008001000c00a0014000000800400280230014001001800500080010018004000400c0000001000000200000050000000001800000180000060000001c000000400100100000008000000000200000040004006001400300280020018002003c007000c006000400500000070008005002c0070008016000000500100060004000000400000000020018001000000400380190004003000400700040010004006004000300000010004009000400d000000000100030004001000400200000010008007000c0020004000001c008001800800000050008012000c00b000800400240020000023000c00000080030004000004c0030058000003000e004000000040000004000003000200000000008005000000400000020000000000c002000400000780020000000001c0000020002000400c0000006000800200180100004012000000f002c00100080030004001001000800040020000004001000b000c0020000000000400000000000000007000000000000030010002001c003001800100000000038001002001e0000000000400e000800a000c003000c0050000000000c005004400d000000200140030004006002c0020020002000000300000020000000001c00000000000018004001c0040024001000400500040070008028001800a00040040040001001c0030000005006000000040040024002000000100080170000008002400e0008005000400400000050078008000000000040080000003001c00900080000004004001c00000000060018005000400c00380000000005005c00e00500010004005000400300100000004001000c000000000000000010010000000400600000000004000001400a0000004000c0060028000001c002000c005000800600040010008001002c0060010002000000c002000000000040000014002c0000060003000c0000000001002000100000000008000001000400000000000003001c00000000090018002003c01f0068000002800d0030000000800400100020000000000800600480000000000000000b006400e00040040008005007c00a000400000000000000000000000d000400e0000008000000800040010010000008c000005c00700000060008002002c000000c001000c0000000001000c0020010021000800b0000012000400c001400a002c0020004001000000
  | 38 => 0x840000000ab108a8aa400006242b580001ff410507da7cf13e83ae800090e00208639680b03800068d9190000295e00021c83818000a9e1aa28f1a0d65dc800000000009c900007de232cb591218000164e318899c0000680ab280009a507d89b68000a88a5bc6c50738000206259e0000000000017da2c2000281a1498000000124a3a78ab6000241418916563e100000001aec00000003159e14b2a800000000920c80aaa9f026c673ba0420c22b9e41820be18b1d6a63ea20c218a5dc2338d3e6f00000000000000000008ba000000000000000548000082000000007ebabd0000017a4471f26013000075d000000012a01a2ac1eaa28db0000000097b90e88961efcabf8f0600006c082480000000000b4d800053f0000000208e96008880000c3600014a200690c803613a8b700dd20002d3a0000000224940621d800041a134a0001bc856f1fa89d7821865b0e3a4c40c5a3fc171e852aa304991804a552bfe5721f042c383ee0dcaa12805ab3c68917cc8088c2000018f402ca7222b39bfa37d89ba067800036f00004f180001110ef261a863ea6522d210580226e08000888145e00008e029aa29a0000000035a3683ab87b6ad28000b2705860000000a5203a0b2620806f407cc694800011780006dba2308a780005890000b570f4e67004fc000000000028729bf09e690a2958000052a0ff28e241da40817c800083804741421816000000800280000004009003000000000010010000000c00f0024007000401000000010004005000000800080000004012000401300080010048003000000000780010004001000400400000020004000000c00000080000004002000800700000020008002000c00500040020004005000400000000000010003002800a0014000000400c002000300000070008000003c0070028000001c006003c00000040020004030000c001000c0020000000002c00000180000000005001800b0000000000400a0024001000c0030000000005001000080050010003002c00000000000000003002c004000000a0004003000c0080000001001c00100040060000012001c00e000400300300000000013000000000000030038001000000300100020018003001000100040010018020002000100000000000009000400000180040000001000000000080000008004001c003000400000000060014007002c002000400100040010028004000c0030004001001c00100080180010001000803b001400a000c00200040010000006004000b0008002001000500000040004004009c0000044015001c004000000300140050014006001400100000000018004001800000040000000000000c00400000000004000000800900180080000005000400000600020004004000c000009400000180010000004000001000
  | 39 => 0xa82a9494318aa77b03f616802d0ac4ab806faad32697149200027da2bc038c59e88c42bf00006c080007680928a86ab363128b86b548000aff000032680000002be800011020001ece0001aae000000075223d40001de85190da2a142470b5d854494923fe15605b0ac300989a7a66a04182329bc9ae492b8882040000006a188c1bd20dc00000000220000afb24f8910800000000000001fe48a6168c00020ce0000000000000071900008c3255a08a0702293000072596981fb15940000a967e90ca63260f6e36d00b801ea5a89b0894635ca45421a86a4432800012500000000000000000043fa5a60000000b750976af81e5600006b8b372c160000d4809e80000000b2c0002450a82298e42a00005d726d6000000000000000001ef04bf882a000000000006a02e595a0a9a280a000120e00000004ff0000000000000018c016fa35e67900002c685780640000a8900000000d709f6077e000000087c8000673800000007160c2a1563ab00008668000000000000514ca445a56000000000001e625321e0c3db060250382c658705ba00027067e30000000230800007d400000004d30938767000000001fa1c10b1200000ca00000000001c42051a0b2ac200000420f300000d08000136400007ca4b6abaa0001d4c3d080000000000b481de405891560002960711a16200001e48f618060001612a5680006758b707ad80000549e86000228c843000061ea4f40c38d5a9c4082eb3d84d44d7000097b0b520001970000000091f10e62e7142c7800000668818a00018ccac692e8407939e2bc88c812f8000000113600000001372440000000000027ae2ea039e000000000010460001e8851480001fa89562938000000265a97d0d42b5b1b927c182742ff0b363ce02a6ab00d06463a6845db2508000000095280007a5299c673080e79b06e40c10000384000000000001a7000085e25a2000000000000000001fc600013b6b1e8000ab4a64caf78d50427800094ea4220000000000000000000005291c2c4b9a0fc00010fa1f18e9012080000000000000000000000005ab80008b70bfa0002c7600024bc000294623f0fe459418be61c24ba4e3876ea8193dc0000000b411c2607d097a7e799d4140800004a967c0000000a0480008489b883f99cc42a500003d10d58000241c59627740490e82102000016b00002219b2c000060a60880007b211b20389a2827425c6042883c73e0a3067b0d1ab6e8c166f9800002184ca5ac9f2c1cb1a001168ed40000cf8b5eaa3a0001274000070e0000000635a68000004a269891fe000172c000089089409fab1a00000001c1481f0b3400028a61f4197c00000005fd00000001eb2231a98000000000000000821177c0000f3a0652d3c7b4a64e00025e43b3800000003a411f8e402ea8932000000000023
  | 40 => 0xc8a00000004ab83b87ce0000000022616599e600024fe0000000000000000000a2000000000000009a280001818000567845400023f02550000a9300003338000000000099f00000001a3e000130200028ae3760c609648000a1a857a16900009260000000286400000003559ebe03980007170e2012f00004f424960000000000000000025dab0723746d694002818c809f0800098c1e446ad021e17f9c760000000000214c1958000000140a536a112786896646200003e28b4a86804fa11309c61971dce4e2a3de7689a781d7157642e2546000049a702a93caf223782fb9c7200000000000b6856b90d064b800094f80008cf130a7e0879a498000062d05c83e710bc0002040000011604a213600013163d695808d100000000000000000000000000000aa20000000573009c3e69fd667d9d3600012d2000000026400009e213460002bce6b7000000024fc0000000b728c703331c62639964c6c4848aa70a3c035d87c00c727e016a816e072000074696725aa000000000002be80000001230b1480003f3000055c800005929a4a0600006bb96540000cfc6a9284a235103a978a0c226180006be039857f8000000000000000008ed00004b20000000018c00019e078d2daa000207a01f00002d100000001006000000008a8e5c4fa80000002dbe2df926c0002a3c23c8a984770af400023940000000a0e8000000282e35b000022280004f592c0000000000000003ef93caa6b1c7400021020000bc40000000225990e0001ea46b598f80ab1dbc62ca77c000000000000000000000a36800035e22ee52807800001a1a017204eaacad66a022d5618009aab6480000001c700002690000266c00000000000f8c8bc000000000009e180004dca8cc0000000944078e90591209840000a6a096a0a500007ee000000010fc6fc0f2c9439d38000150e000148a00000000002d1266e0a7a0001e8e00000000000000aaa00006f7800000000000000000206000038f9bd862b0ee2000000000001f285480000000000107a03800029ceafe90b459f82366f8800000000006b0ad462da9b56af0167600000000000000000000059180000000ec000016d49a2000000019f400013f48fa23cc51183b646d20e64be8cf20779844676255092505465ad17de5899daa572938c54b2a38a1f09141dc06e6812800024ea0826f3893e6c5a9e4138a8b21ef87f826d9cdab25a77200321de000000000000009e8211829ba38a0000b2a75e800081d80005fd8000000000000012440000af6b5a146caf708443d289b210c23060000fde1c48000a2aab14944917000022c654d105263dabba14912049de0000755037c8e4046e3ee968e00021640a404c284b267a82907de0f9835a00000007a68000a6a80004a9969a9aa00003142ada75180000001ac400012ee5
  | 41 => 0x8402a540000000adf90027d72a0c44f091034b99a8181295c14622c400000006c39f6c869240e37124b8000220800018764bd800001a9d980001fda1aa1ec23f404ea00021d400002b63629c3275a0f82000000000000000001d880001dc89700000002000066780000000000000074630f2d9a0c19ffa52720fe4cd901a42e8b049d49c8658080002fe22542768d8e00000000000000000000000025d64351d0c20016048929d1800010d27c08f7a00021ba84a108a6aa95b042f8d00000047873807728ec8ce66ca2d38b1f031a2832dac96e00000000efc1be9f200001c4a30e8620000000020e97da1df160eafd9d10a3d09e85f48eb4311078493a80f288b039a0582a6246f14302b81e7c00018ae6bf246a7caab72640872e83a9f0cb3aa32040c8000a461c5a6f70bb23788e3c5f580000000000000074a0000000000111a00000000000000000144e000167433b89189ef9ad43329ae615f29c06cea9c85e8aadc1578b46230227e6a60000a1b000000000001290000000000000012e200000008659c5800000000000c4200016fc40028e88e1a5486ee9bccb200000b0028166362bb27a70f4ca698de0a5280d291716f2b50980a0000e4e0001b8ca4516145fea4720000000000090a00016c85f3800079296aa000154a000000058c2c22914a350934a5180000000541000038a800081a253655385b20000000000000000014e4b341324000000072c1b4813f826009ba1ce0002aea451a4766c2800048b950000000002f792b80001c384f79f0e2b283e20001dca7bd00000001a1653c9d62a962c3400000000001ed800013d400000003c600009c39226453a2f83280be8b2dab10000135e8ee00000000000000268e000000000007743e918a200000007450e286a200000001e0e00000002c90000238800018c8c54000184e0000bdc0d8000079a1c4c00000000000df094789d60000000000000000000003028000a7a23929ec800000000000002b26000288a6298000a3d80005a88be644b1bfe64d003846a1178000000000001cc02c012e18200780881846195174a0000000800800092a2ce26de02bc2e100000000dca47a1a66a0c9fd843783be39c00000001a4a87280002091dd60818e627f100d42160ae25d6a0526c80eaa0002b4682b118c21d0c0400a182668527704dc0000a8027c47b78e50b06889eacb80000000ef80000000757054a000079c96d0000000266232c852269a000018500009111fe02ba070c36400000001b328870d2201093c01b325340002bd49c30d044388000a8a000000009dc0e88000000000000027340000a16acf82f630c92b62c0800099f80000000000000000000000001ca8b76323149eb2f88a4000000031a00e02e2a2f60000d96566923800007dc0000acc81b80000000710000000064d9
  | 42 => 0x8000000290c0000000740001802f8dec360958430a20747080c340001c92af1174087700000000000000000000000006cb8000000000051b9bc200010926c980005c5000000002ea000000073f01e889b1be033d279a987178c49c905e00010d6000105c0000000a622cee73c00000000eda0000000000000027b0000456a87434829e263b06da0001128000000000000003ada29400000008440000000000000023b00000c2a99c000041f922889922261b883b0525166800012c29c2a3d68c29eda9d12cb28ea8000000000000027d636800001ec92aa00028921082b7a907a78e00000004201f0072315364c6130e843800000000000000f226742640307238c32f88fa2cf812ca20acf0210814c7ee9aac7ce8a20a96a9f83af800099a1ada000000000021eca7f95420000000000000000021bc0001ffe000215c9f70000000225254e815613e00003c4a8c6a0d020200026ce5a798020e49c406629da610c9f5e08026b2106988297e29be634000038ca1206d70000b3b26481ab214e0000000a2780000000000a280000000000086b0e486a710402bba8a848d9b9a0fc9172adb14d854e13f60f58fc451fa7bc8e09386173283c7ba003e5b2880800024008fe15460000000b182b60460a44c5309342304ab961ba9892540953c0ec8bc87f32dd600008c26d401980bc83e838c15a20fe1e5e239800026222a8b2b182a0000000000050c00012349f517a80001ff89b7a5d200000005e61bf8083832633c10742ee289a000018e7b100000000310000103e55f0dda4e900000000c960002b8c134898a9550a8a456067e76e1d0a5f00a0e41eaa1822e8464b5119c86a58d9e4251ffc5eb1874000274870300009720000a7ca33e7ef246201c9efa2c58c0c067179a7dea5de9db248097f913e5b0211e04724b418d03aa6551912353800004fa78000004f661599166df80000001bd238680005c41f4a000000034da03e87d21daa448f24701800043826a604c80001d3800000000005b6000035b8000b39990a0001012a8c800000011e26aca0eca3c000000017ba58016a439a21700001a1277d181e00000000002686000030c0000318000242e75416b83fb8caa16d88eab698a1c9711e80b34a1b487188282b7204881a82d433da0e817c11006c3147a78912109c9acd46bca6ba73a05de22014626d5104c96b809a3a20cea190000082b8000000000000021c4364aa5642385da0000b788a9968887322624fc025a1fba8d047f2d7e76d000000000000000a18419a784931016ab1200009cb80000002050071808e0002bb85d328661602dda000000000000000002432816129e000000000023462ab98e800000000000000000000000004400000de896900001858000000179417500004e48c5e4f21dfe0ce8000289a3148f229340a29268
  | 43 => 0x67138fbc0e38000000000000014c438997440281fc0000151c7ef800000001362512884074a52a00000006c009946710bda2438000aea2338000192c0000000000000041b00000000e583d88c0600000007692cba000000040a8c58000000066506c802020b009401049e40be4289011aae29cb297c8000000152400000008620000000107200000008d48000000115cab60000538899800000006d300000000000a630000548a69c1749e708ca9d760000000000262eb32a2b648494840002bbe15a14241da9610a87831e36b80007a483823b293e68980000551000058300009d80242381216c2cc023a23280005a18130184a8427f7a48a9fc000000002084059fe6731926a2638fae027907c26d000000023348d69f1c5921508b36a104000000044c9c3c7b8219c0002036a098000000084c0002db095488f40f70750233141ea07867ab5f09b05e79bbcb568b5c9fe8000766a45e97d80000000000a810a62995a2660000f0a01114b4490946895f80000002c9a2f283c66e000000001d4009b154866717a44830ae687b94ee05d82f82b18f961ef01966251526473954c0888d029619f368d6000053aa4e28bf958a9c5883481e2ad04c7275400000002c00000aaf8000078068253e0000591223a0000000a6297aa00021b2000000033180007c496060000000a900b4212580000000d9ca7d00006bd84f453d800000000000000f3e81b225e65800003041a6aa28995c70b91d60eb0ab468c073a00018e25eb992a000021a34c80001cf865e000219400000000d480000000a92000250069c000070404b211c1e6655aa1d80002174ae4000000004ee6140516aa3805a00000009048000806a758874000066c00005a9a63a00000000001ace2db800000000000eea2344a082a41d100060001b045b680005208000b7080dca3cacc495720c83e8856406c0f020001a442049d040d09fee87c1d7079b9932a91226e78ba54e6fd800031d095a20ca81c7df09ac5ae8c6c000150669f9d02545166a07627f400000000001c82b42a7149ad00002af8f5e71593cc044ac320000000b280daa00000000f785a60000ac88168628a6e800000027668a580009e70a6c0001cfe93b97d034588fe000000005c29e600000000000000add991e00029241ee079000024c82e880004eb836406e1be85cca28e42411c27aa91f82f8a4ac00000008800bccab78e9801f80000002acc5c7231254f8aec1571b623f1aa4866b84f07e810502100ec4641211c52b2910896871e98b00aa3450e4a87d8588650ab86b1b28d62739ed0b0b9c2a87e2b421eba838a339e7e0000000b4180008e5a3dc1f889580000000280000074e97c8217957a1a616dc804297439b230031badd00fc2abc15003d41c811345dd0a88614a5eab0295b86c7010e0702b0e9340000403
  | 44 => 0xb0a4a9bb91a420c0e163978000986800030205c0a4c00000001e420000f685ef25fa84f000014d00001da2210a2626368d0a160897000000000000000000763ad4ca9f2434a4b072600026b63b58dd4036993e0dc0000000000077317e824000008fc8000000000019121be6f182623fc80009a80000000000040b80000000000705800057d0b4000000009f392ba0002d10269800043d93084b12ba05068134520227ca7c0e562b58658abd891aa2d800024a9c66a5e12064c49cec6c8848e1d99ba4000000000000000150000b140000000000056b1cbc43c9d2a00000007b910a62c81d2e6ae0000000000000000000000000000000067e90180000000000259850600000001e900001038184000074700000250fdc00000007d5800000000000000f340000b5015c800079021c2000000098e00000001f8ea852c8618d87420000000a5b2b5023c2cfe2f4000074881f60000348000067c0000000aed80004ec0000000001e000000092d800085fa63454a1cfa1f5ad882868c0e63c9afe3d9aaec78814ba42914ec06d0d9495a06ec14c112a0000000921997e2eb8d868a4a992000103653413fa0000000000173aae8955863500008060eee00007f60f8156c61f0000000182c00000000001d8471b937e85f000000028787068ce2000000095780008678000b710000000297600000000000000000065a7ac0ffa000000036b051a57c806c0001088000000052982a00002a2606f0d305ba922a70094b2ab8ada200000006c69ce400d8000000128c012a27a00017b853c12886b4a6440001af002e878a85780003802b3829f970a000139000003c203f000003c1e464cc800074a0000a3f0c4eaf994fe00000c630e1f9ca3809d82139058000000094e00ec35f056e0000000b53800000011067b00000928223837a800000009680002d165d19eee000035e652292a2ed9f1e8b3a57ca688378000056c5c48664000203449f29c434300006308cfe000000003d13d200000003601b525e42b9c00000000001ed41f828860000000000000028d8000000111e00004d80a1a27600000009bc15923778ade237aa2e24d11b69ff8b2231000000001cc09fb000037ca13a75e271a20e22901f9a4dc000000000000006e7925c05222b800013400000ed075b278c2f0000068126c05bda22a05fa75cb249c6c5f8a1e669d25e66e396e6121821045a1fb40000a8659c21901cd80003320000479000000001549c621e40000000ac297b472f92805f281a2000002c000000022c80007a7800000000007e5214400000000000706000000000003aeadb863a3cb83c40001290a9e961600013149861f1612b000098a89400001c5000003da7e5993a29914c6547961e3c5123228a9a0a0001bec000000000027fc3572dd8000195652e0404537aa5c80a857
  | 45 => 0x3960002c20b5023ae4b61c3e000000014500007ae04725e226785c58000890a77e000209c751000000000003df962eabba8146d8029c4021458a4110f80c0861e000000000000004c02c6e00000348dd804878b000000010b2686061c0b49e7481f80000000cb800000000001d6629d13b20648c5200017c243d0090173a33a33b0000b79829ab02000000000000000a8e268800098f800061015203c01d4a437007445505ae236057ea728cde7e6a6dc526963aa408000000146a0000cd21e594e0000000000018367fda59a1ad8ab86f29b3e0dd8fdab16800000000009488974b4b120295e1db0b78a5be77e8d280000000000000000011be0000674000095e0002a4a99500001a1083e443800062a00007ec8ada00000002728000a2f8000000251c344845c48681ba6c900000000a04ad38efe000287e0002642a178794000286ea151d604460b80661ac583a70000b11000081c000000000000000000000000000024d40000e781bb96e0add0000000000085211523bd80000002bac0680fec60b89246d1202645999f23af13ec67c2134a6d00000000bfe000249a2e980000000000af90000000242000000007762c026621f920ef2ce0991846200000009de82c807080000d110ec737990c81700e88959f7651693485c9a8e68bd10a282300c00000c925fc01024f6070aa0906ce00000001aa95da5c121240000000a99800031226f400000001a525701de9cb4aa180003d219ac5a5800000000003221ef80000cc2817a6925bc00000000000235a302661000000023800000000000000000012963fa000083e800078780009d08000000000022f2402000100477c8c90a242cb41b0800011f23b600028ac4e02c94000000062e1fec0001ca8a13985aa71a8fa000000027b8e6e000243a00000004da000000000a4696a26a1530000000206400020a24718c861de2b666e58000004a1fc85aa7a81bf97c4ae98a568c9148c2e482643ca27ccace82a80000a0286e02b84e2049c172a31a053902093980000002c5e000104e32c00006b614103a89cac88c80007df80000000000b779a3c00011ea0000a8c1b28e42000237a0002ac806000000000158000142a0000000000032ab61250a000000000000007cd016600000009960000000000000029ec60c040a20987a29628f1050d18c64e6800038ba09669e851098125c28bc900c6eb800000004465c8228aa3e081e000042200004b8000043cb62ac640001c446e50000000244e15c0f505882544b10204642080000000000a23800067ba4846adaa725dda77600000c23f486460001e4eae918b60001a1e8f6a69a4532202000049000000000000000ab900001330000976004e4caa9b600017640002a7e0001b9870480700001a8e0000000a508e929c480005b
  | 46 => 0xdc00008f80e6ab172b6a73d8ee85be93209cead508b314968c98000734ad8c8cc000000000000000000973ad8000000005fa9abc8cc90da4cb1f602752244567125e3dc074c5c39da8155859c49989cc03ba732994989e579108437f835671a8000a66ab0404300003ea1b30000125200000000002672a54a6d200000005da000017b000096b0ea8000000000000000000d268568630000092666c81a41c91e3a018a88000000007651360000282c00000008031fdc0002bf28e906b40002a50a7700000000000282a88c000000000022b08ac80000000000707800007f00001988000ac00ef085e8010069800000026a40000000000000092c800011988b6a1194560001dd2a321af46491c940cdaa420002088000110a8e8259e57421e00798000ad480009f2917c12795d6a782172469a5203f00deeb5785a20001bda1ab8e7a1b5ab8e0000000a531cf44dbac8c80e99fcb22a1c010a16f4254a3f41b5181a0000000066800000000004f389fea489e1622880005f814dc000000000007fa664a3e6000000000000003199510aec03ce0e4000052d80009bf96d002b80003da8904a8f80000f482cc000000012d992600000000000bbc0d6000000000000000000000000000000008a89f5400014cc6680000000000095600001f080008b2000000000008d309a00000000832a0f8736119421c80008f41f088a900003e980009640728000000043112989d382129daa2d40001180000000018b9a0800000009e780007579f5a2f59ea2a4dad90000000094f0f904a298a425ba32e8e98000206800094180004db00002969eba00022ae0000fe2000000000000000000fd8000293e000000053380003ed27a400000000000000793216e00021fe5d0836e0000ff688f995e55d24560001eae000263200012860001c90092927e0001c2256a0b822be05927d01bac5e390640001c8802b2da4a4807d20000000000157ea872bca9031f24162a96428f20040001f640000000b58104a40900002430000000198c00007e400015964a91b7c00007b03e7ad4a8c616c407c034a00000fa2a1251a0000000a4e8000a5b80002d51b7400000003a180003eb04482572b4800002c27cb850eabe80009d4121660728305c8826a000080c83c919a0091bb67d216401fa19d262c100a9d31ec6acd2ac28a81a8a4af14982e221eab33aa1669f071c955800000000000000000000024082f0000000000000000004d594be08c00ea22518086aa24189fe000000013be6f90a9e7e4131a6a805e6a740000616224800019805349bc40001efe3e00a1037e9d7e83d14bc0001c040001a4600014c000000001791fac8341998415a0e20001c680000000000197871f00006219532000000001a053e5cf1f6ab2901726e8021c14f0d740001f801f205fc0000d9a00000
  | 47 => 0x8e451402f012600000000e74aa585f481100006ac15889f90000311a6d4000162ca16832c03da9865be18a00000000b1380005549a1052c000054a8c843e207f065325cc37906485f912cc78098668fb00007f38000000124c5a42d700000f869d2a4905d7a268444901c732a7b63d000000002b5cb7925288d3972e000243c0299ae296824fa5c19e064bd000046c09c0b01800000021d20002228a0dacb8000024c9ac12a20000fd622d00001b600006fca7c824f1e58000177e7968a4800000008c588ae00f0590a8d8f5235818808bb0000aa82cc8137985c5170000074008239900008618c149af8e5a44e80000000fea0bf28bc7fa93441b78afe7ca290e7121cb8891a46e2118000258811410980524e08000af31a0e0a580000001b9c95999180000e2c0be82da66417bead50000000272c9c787fc54ba1408ba9e1055c2184666932eb4996282f829842e6800095916de8e38d4c90c2d6e7ad092c0002d726cf000000000009780000646800000000000001bee0000ee04920e8e6ff00002fa9b4a0000f56007223c0e1a696570aae680f000017400000002280000000000011960001de20000000afd2c4a000221647000000000584a65a0da0002d22574a59c0000a9a0000000000000000000006da8e600001f10577800000000006b7a68216e276200000000000000ad105389a3048c000242aae124f6acb1dc08468424b2c1354106005079220b800000008e6800000000000001b063358000b1f80000000000000000000027b832e80000002d540000df863c00000002582a36201400022ac000202e12b9fe8637000047d142000008be000073ca6800000002c260c580000b615aaa00044e6b3000005788225131f861cd0930abc83ca4712bc23fe09f84b296ee000000000025760000000000033e0f90a600001d1261f84e475b84a692096c2075159863b80008b291e60001fd07b999461ae80008d29666308800065c9f5241c145400005c6b7220a0929260c4cf2b4000000001a6800039100003a2800000000002c700005d5000000024740000b8c0002940000000081c8d2c77f2c6a00000000000000000073000008360e70916b58a5722a99f3278aa90683baab0000183200000000000c1eb718000b77000000000001e80000000000042a800000013ee5350e1434f121e00022b400028d25fc8000958927a0000a54112867214c8000000069077500007bb1a846c600003312af88550f0465aada83f3973e00000009eb1dda4d49f464881ef60002822794ad28000000051c8554000240649b8864a6e0254a3b247e03fac360002c040228dd0802986815d03cc50c878c176033014483d034e978ab1316e877182e41e7a86070d891e7ba92ec74c98000a8aa2c96ca39898480000001d242a080000000f6000018ce5ed9664a
  | 48 => 0x349218069317e638315b4941155677c00009ec00002d5800000028062cf00008a7000032d0b74093aa64560956427912d05cd1bbe63820209850becb30185e6ed155ea9b916e1cc841c98215eea8387a425819089ca86a6ac09304b3080000000e8c08917825ec000000015c66c2122282d0000000000000010cc3ec8d6a61b22c00001b36856000000001420000ee621f800038d2aba00000000002b248fb80001ea80008f49c8e17ea3665d600001a18000000000000000009b40d0a3732ce86b200000002b22138000072000000000332b6b89646e2a80425f258c7ed871a476000048521fa62100005d2110445f9cdc8beab1651d0ac4b0a132665298c45c0842c815ad864540000096237e0000d680000000383800000000008888000b6c98241bf0efa5e4800000022de0000000000013c009a1929b915be00001c44e600005d89f1894094fa8391d8249d800048b28d40002b18b0e00007e600165d4a7e865d2bae000000028d025c0000000229917a00000000001d340000000000000009a17f800018de42580008f3ada06ee2b644ab0da80000000b40121c9230f08ade000000002d62b6131e0000204841a2728e894908fa999667780003df000017b85a853a000043b80000da1e606d904f253580847538252b43ab689e28000544a4de00000000000000000000000012c629d80000000000a1da79453d01ca76ea9004900abc3951f1a886ab2a42182b227802b00100a2e799069600024cc11e93b8950000000000000000e22af592dc66d00003b482be10e00000828b580bd000098900006af80000002792212000042319100f007fe3a9818832b00f814b914a000246873c91ec0000000000000082d80000000a800001a766e1a6640c8800093a16428789176373800094b267400000006cd2364aaaa00e0002ae00001ddc6f5000000019e800022fc178221841883500d8800015401ac6120000b39000097a000000007922789f5866d8cd084c832e26680007c292b034d18344dda738b0f80000001c3000000000001436000000000027c600000005b480000002dd210d889a270800018a81f80002240099915e09f0714aed11600000cbc458869280a0000114800084f80002540e0246b16fe4d88b1e1d821a2b11894a000000000028fe00000008d00000078980c1dd80000000ca416d0850748000009f800000000003c7a75a00000000000000000000000006528499a2a00008706a500004eb0e3848f05dc22726022878c3e64e0ca2284a6228b8837e000000000000006a08d62755a0c632700005098ee4000000095b81aa2e92a4683791ee9fc91da00019dc7a118546051cae0002b628f280000001a5e2f6228604615685e820aa32d9e3c90986780f6162a78c2d6a8e78bf205b11389d91f6230c2d0858c8c8e9c81b660ad0
  | 49 => 0xd54a2c18ea18f0fe05a2920006180006180000000000029180000000cd45e59694426000043380043ec2bee83dad9c0e500d04bf02fe0a3ad3491b0ec200017240b380008608000000000057380000001a922900000882800056402ba5fb00000001d5a0000b908d5800022a90e47f204e67b59c0012a05f8af49778b2986beb0600001d5a41029a2cf877100000000f2618e0492000000000010488c79c7a00011ca000000047c2ab80002c2c09d84580000ce083c00002b900001d48000033899e000144400018bc00000002a900006320e9a69623c219282dc0000552b479b4200024ec8020000929a6760000434980087a74f000050580000002d780000f929cc0000354a6c82610000000076c000000068b93ba845a02ca132ac61d780000000a08592ad24512a2be2199e0423e1e5c59b12620002424a730000b73051e70ea6980000000a6600000002a5234e00002de80000000c7266e800050e14aa59480008e2197a821aa4e0000a3882400000001d8643c0000000260e2dc80000000a7c26f0cc0000000002300000002574997a8480002a8454588544cc0dba3ba85422d80912663a61e82a00009be8ff4b3600001ba27364918000495032800025d40b10b2803780000000000000000014da92862e8c024ce2a9291807a89362cde4a486c45b90d5e50200004308fb82ce8b6410f81b21be2d1432b80004ce9b7a1202828945800068997b2831000095e80003f0925a5f600000002168000000071e00009b311300000d180002d9600019280000000b4f9a9e00000001ac2142416a8ba08500000000f8e0a023ba0000000a77ac241c000000001a90000060c00007a6a31000086da4ce826000078616c642c22d8729297200000000002b5a8af24c000000000001e546ea0b26adf1ad01b1890696c0506000194008d2d8207f9e08869904447c8000000148e0000fc80c0005e66090eaa159f227f899ea15aa31076411ae8b985d61661fb00ab8dd657c19a6a2e2c0c64c1a804de1278b0426f8436011e5f70a660cf000000e96ac000000031a80e40000000167a1e80000da468823725b301ce00000003b78000992a60a00008680000000000066031f80000000000a1013da140000000000000002dce1b811fa23b210a000020c000000000028ca000000000012500001b580e9a5420000000695000000008600000e4c0000000972800027a80000001c9e6390000abf17feb3d0edcaa302927d41c9c0da9b1025ca3c458d11c83d622da07b80002ae88dc0000c2600000002d9a4f05500c7ca7600002f3864e00000566d38000abc1684884800092707483ae144070a0000426a5f000021142ec0898000000016080002b4800000000000000000aca2c3c50e9faa86a1a56462a22e6ec89a480786f655e00009ba91444b79de60001c24
  | 50 => 0x57a2b1e819a284916a6e855813c45d984006e894144e59b843590f1a77b8e460000000acc15f6000287a00013941789b9000028de7d0800061c8000000000000015ec0001dea000210860e03247630a4476f92e0a5404e895aa9388352c9e000000050498fea808b48813006612d000000000003f50000721141c764a5b60000000b651ea60000e7c69c83460000000000000000000000001df6000191c6ba00000002aa6234916c000062247324462fd017800010b600000006dd8000274ac424670000000243e20127d000016e275490c00511ce2a27000008b000072e89fca98129456e80005710000056aa206871edcb521ff254c00003171078a4ca62859ba92e0b80b1400004882df000015680007bc8150000000000000000000a140000c24000224c0002c129b2881c9f79a380002704000276e44212f029e11241908dfc00011140000d880001e3e00016be44ba6e20002466000120a0000a2265413f2622000098180304ca000002d00008938bc640404ce00016623b1800021b1ba6a5f23be28e9f1460614762c400001d6800058f800013b000000023e400000000000000000000048f8000000000000022d000026c4b6388844612c88000000000000008ea0000a499b2a3ff03fa804800050b9c3447429682282cfa06da73ca512478a8405281d910542a80ce827da4c276289deaa92c3a825192012129fc45018d27b28000949813a14b26aa07686f022e0ed8ab5000092c15503ca8ab031912247dc116400008d010a80001d6194424d9d0e4509e6a4f09e969898000000272876b1736a53abe200000000002054b1c0000217086e1a78000000000085d8b6c5b5942877812d69fba982a9b0a7046e2702a038db606f9784000000090b125660f000000001207da27d26da00bc74b2beaad319227600000aa21e765798992512147c35e96b6a0f890226a0f468c70dc20d981402ed0246ae2297a29782de5b3a336b15a30e671a34800005606dc8000000023e1f100001e18000aa7a5fc0000000000085a51c29ae56196385218000577040c8000f1600004427dc98ca0001a32b31800e1931b38a1606189122a742658000000000000005624d680008838000000031437000000000b187b30a9c3de1350095800088528c200022360001aca6d78d2a00019004d9a54c0000000204139c0001e361899d1600004c03e600007e8800093817084de8ce4ac82ccc000291600002ec00000000d0286823a0eb2555092e26312ea60a0f543a01c180001e32000014a000000055b8000aad1126000102c01d80005a082882c19e7a060834ca6780002018064163979c0000f7646600002d880000000000000000000015b65630000000002a0000db8519aa2aa640000586a852205974e4aa0978559946050880001d8a2aa0118f1c11aaa6ab4c
  | 51 => 0x592f86561ff083300000001ca69e89a3a000050a5dc00007418216000066c0000000b288000759000028f83806548000000177a76c813868b01d66939e7200000960000000000000039d8000881800016f1ac00001bb0000266068180000000c760002a8200019aab18800000000006262708467a36c6b802484fe2b1c6a184503dca3280000000000000031306f28da829e4a100001c88f3c290800000017a69390aea000091c000290851e059a52b815c1fd29b0000134e9ae1caa000000000011de4a38b5e7708000337111042708026599ca2787027847d9ca071823e22489a0c9fd9eacae6ac829d582440002bbc93cab9493296bc0001862a58ab8208f24c6b241afa4aca01c6538c9492f93a0a74a5965978e9637d0ddcb23a30400008567cfa2ba77e15d87f28c7a35283a8a2504c4118150c86c000086a80000002db673200000001f3000028ee8ef20320000c8a53980000fa882c50f181265a0000000150a97400009ee8000170aaae7f49404461828489c13bcb1993fe7f500583369f74b6d1a2230b0e5236604761318b320320eb026e14028018000569a12a2b092580ba0000236956200023700cd00002e824da945140c000237c8c8a85c98f286242b00000000ffe965058cb40806eb4b97c6af68cfa1598ad400027e622c000091607b4af602e600001ea27c8de6ac180000000000829800075f00002ee8000000066a5ce0000859800089e2a3440f2bf83698000000184a8e70000000000035184da4cf80002d68000000196430b97860002b324b3983e0000000a0819da86300000000dc63cc80002e78000000136a597000000002722fc0000000247a272028c3598f64000240469913b40000000703a1d60f215eaa39045657ea6ae2421f884e9a18a74f83fe097a4aa0002cae25c094c0001d9e3510000a75800000020ba0000000000000000011d241aad9e00000000d5000045aacbc000068c00000000000000408a82a38700008d7000000000004648e1212c2c5410b8000000066e000222400000000000b943a123fa4a69810044023871f9a8c02a1a42a7d9a3465d90143a50cd84a700000de8718000088c0d70814a29094234783ec00001ec17aa436104000010199e22efa2e04f8000028c951a12820c08dba7a6902800057000000001e289e0800062591a0000000073a80000002d1800011e07d300009ab0b0c00006709068bd2147000021e000000001843c395e20000000569000000000000000000a7a800000022746ea860e99b90340001030563a7404dd0f203470000000000000000002ac800011a00000000eec260a13869200000b8955a2949322aa619fe02d99066228a589bda58838788f65c317ee9610000a3a92b47af175056c960895b24d69cfaa8069403f4a00aab66268ac059808ee1a2000a37202c
  | 52 => 0x6981730000000064f0000223868e0db000000011aa6db000099710a00000000000000080c00006708000361000000000003828bac65880000000000000000034400005e0000021f20d200007ce00004d6690000000000000002362a5fa6e62aa06d02c28bf67d38000a9d80000000000000000045d000000000001b7248825b0000b5d0000a5a9e385c68aacb1d00000000000000000092780000000126726a91c294244a9248000636a198000094800000000000dbe7260f5c1fca8960002b5e3e829fa61b984cb471cc2789827084c1e98a75000000007540000000afc00000001dde0001e8c00000004f88ad0a5989ae8ff16b070713840002768000000038214a80000000aa899bc0001db60b2a71c00015189fa800085406b236ca4a27742d1a6b1800000017005a70000141000000006d27a8000000000000000d8c0000f74a3029da000124e14e98200bb80007e1281010094881538f94714800048e8d7e00017fc9af2b985d828dc000000000000001e200000000000000114804880000001b4627c0b9800000003ed9d580e11e1239f9b70000000066f9a0200026e000022d63279c5e000143e00000000001a9a0001bd64d600003a90d4060ea0608d80b0800000006ba8ea010393e45d58668b560000000000000011d400000001d0000072d8388000000022b212e00ca09e2f0a7e225f86bc623ac72000000042b9e82b3c8a5c0aa8c78000000088120d808b80000002db800026a2abd1cce00000004319fc261e17d40002288aab0000000000094b8000000029800000cc000000058280006a98e2400000005c6165a7d99442260084a57f0000ad5937c8fd9e78000000027100000002666963acfc9b6000000000004bca5aa0dd000000000000c499caa9791ba00000002e3a146a030d0ea1115d4a1c2c840ed0000a6c80007aa00005a495e07a29636ae4834e69b04aaaf19cd0749976e8091e22b050282104a7983cd8f0cb7809207e9933444324647422c78409963c000265000001740002956186adbc00025bab0aaca830607ba00000003999a6e887a09a1a8878200011a20000e1817a00000002a700001d42202ad981480000ab3800021487086190c1a00083381342d0c6690bd400000000000a72199996e822800038da9bc0001d720001e0a0001208000291a00000006d012d494c9ee200009f47022d2a0001028000094e00000007332a0a000290a61099f80000b2e76b838a000000000027aa0001bf45da8ec8b35a3545571d969c00ecc8a080009bb00003bd1306000112211b002e5860000aba2888735800000000006272a9a0000000000000000001ae320930c4e893aa28b15f8588817c3f28b4e30004baaa70b38a5c1f6eab5a6208b9000041b9cd426f87ac4b907983ea8ca849c000005a05c428a23ac5ca26169e
  | 53 => 0x63f1e505ca980e715248e7398b4c0312c309ed0000a7b8650000291e6ae843a4af8a907e2a1ae07710420001914000195a6c7859494c000013200000001d3074786769d1806039ca8b47d100
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x56010430a33855056010430a31855056010430e22525056010430e21525056010430c0d541c96390030a448258d5190030a4581d50624c030c0c76552524c030c0c76951524c030c0c76551524c030e055418a514c030a448654a514c030e0654189514c030e0554189514c030a4486949514c030a4486549514c030c4a765c0534cb20c0d7414c604cb20c44535c4604cb20c49769c3530ca20a0d8414c624c220a458114c624c220c15645c46414d20c19645c06414d20c15745846114d20c51615c06114d2084d8714c6050920c44535c46050920a4581d90538c920c0d7414c604c920c44535c4604c920a4a85d8c604c920a158614d4110520a31811516010520a31841456010520a32855056010520e13535056010520e10535056010520a0d849d853c852084d87d9053c852084d8714c6048520c0d7414c6048520989831c14250120d08531c142501209a1811c14250120989841c1324c1209c1811c1324c120c0e75592320c120a46858c9610c120c0d741886054c20c44625c46054c20a498598d600c820e095498d600c820d42735c03254420c0d549cf625042084f8754f6250420a4683d895150420a31819516010420a31849456010420a33855056010420a31855056010420e12535056010420e11535056010420c0d541cd629002084c8754d6290020a4483589519002084f87d97324c020c0e76553324c020a4686cc9514c020c0d75590320c020a0d86550320c020c49655c0320c020c89645c0320c020d09545c0320c020e05540c9610c020ac1800c9610c020e05640c9510c020b41800c9510c02084d87d506348020a4581d506348020a0d859506348020c0d7418f5348020c44635c75348020c0c765525348020c0c769515348020c0c76551534802084e869d95348020e055418e5148020a448654e5148020e065418d5148020e055418d5148020a448694d5148020a448654d5148020d05735c85450710d12735c05450710d11735c05450710d22725c05450710d21725c05450710c0d641c95314e10c0d641cd5214a1090d841d5320ca1084c87595320ca10a48854c9600ca10a0d8414c624c210c0d641c9530c210a448254d610c21084d8718c5248210c0d7418c5248210c0d641cd520821084c8758d5208210a44835496108210a48854c9600c910d05735c85450510d12735c05450510d11735c05450510d22725c05450510d21725c054505108b1841c16348510a448558c3248510ac08058c3248510cc1635c032485109a182dcd415011099183dc94150110c4475189314c110991841c1314c1109c1821c1314c110cc0621c1314c110c447518d21481109a1841c121481109c1831c12148110cc0631c12148110a31815516010410e12535056010410e11535056010410e22525056010410e21525056010410
  | 1 => 0x1e056354941d4041f01535494194041b12831c14154041b11831c14154041b22821c14154041b21821c14154041b2282d4d4154041b2182d4d4154041d137554d41540419328714d4154041b228214d4154041b218214d4154041b1283d494154041b1183d494154041f02539494154041f01539494154041d23755494154041f02535494154041f01535494154041932871494154041b12831494154041b11831494154041d11435c44354041d21425c44254041931819d33254041931849c73254041931819d23254041931849c63254041b2282d0d4154041b2182d0d4154041b1283d094154041b1183d094154041b13835d94154041b10835d94154041b23825d94154041b20825d94154041b12831d94154041b11831d94154041b22821d94154041b21821d94154041b2282dcd4154041b2182dcd4154041b22829cd4154041b21829cd4154041d11731cd41540419308758d4154041b238258d4154041b208258d41540419328718d4154041b228218d4154041b218218d4154041b1283dc94154041b1183dc94154041b12839c94154041b11839c94154041d21721c94154041930875894154041b13835894154041b10835894154041932871894154041b12831894154041b1183189415404193287cc9415404193187cc94154041932878c94154041931878c94154041f01320c94154041d12735044154041d11735044154041d22725044154041d21725044154041e12635055014041e11635055014041e22625055014041e2162505501404190d841c1520cb31a4880549600cb31e22525056010631e215250560106318d1801c5640c931d05545c8414c431d11545c0414c43190d841c1530cb21a488054d600cb21e12535056010621e115350560106218e1801c5640c92190d841c1530c921948805d5430c921a488054d600c921d05545cc4148421d21545c04148421b058414d3148421b418014d3148421a448254d6114e40a44835496114a40945811d5320ca4084c87595320ca40a48854c9600ca408b1811c1644c940988805d1320c940a48854c9600c940a89844c9600c940d05735c85150540d12735c05150540d11735c05150540d22725c05150540d21725c05150540e12535056010440e11535056010440e22525056010440e21525056010440c25645c46414930c29645c06414930945811c14314930c25745846114930c61615c06114930a4581d9052cc930a4a85d88604c930a25861494110530a31811516010530a31841456010530a32855056010530e23525056010530e20525056010530c0d74148604c530a0d8498c5248530989821c14350130991811c14350130b088050c5250130a4985989600c830e0954989600c830d42725c03254430c0d549cb6350430a4682d8d5150430a31819516010430a318494
  | 2 => 0xf40018c0010428000ee46421000b650cba210af000e739400001153bcda0014c000002a0c5144001d8000011f07d0e2e4fa06cd9130000000200000000000e80000067000c12cc6a344600003d125340000043400000004b0940014d1d047000de2f8d8000cc0e04b138fe3f4b430844000954f0f5380373494606800000002b80021c004e00f0b8c0000cd1700000000000001b0860312914800094ab3fd0824400194003980017d01000340000d3c8700c4e904c56000a916868384004c52e1e120424c811800325263e000000000004d0000000102108001cc7a1bd441ac81374e32640000050000004740000000388002140628539000cf23d4b0001145d283c47e4c84f28cfc048001c832001070649c35435184eb1b8293d8c72793e351100f075188ec4293f42d052b024488d33cd1c2206924c660393a25820248431c4bc0e5214ac9d5213746857328a54f42a4193b1dc080600048c3b010b83ec3f00014000540009f000001f0002301c0011e4494725d2744cd62a93500000000d74507d3dd422ed180f85846cdf0b0263b490054363c00032cbf400820b4ea1ec550880004059000b03188d0049a444794c000010240d0183820030508c02020000c08080303000060003c0000068000a000402c021c0385408010082000000101000030002802000003c00000100814010001400001b8107a0101008020d030000804020040e030000402011b8000601050000a020201c00010380422020281818020200424030280404040082402008c5811c16290c328c5811c16390832b05811514350832b09801514350832c0f75dd1644c8328c5811c1644c8328c5819d9544c832d05545c4544c832d09545c0544c832c0d759d0604c832c0d755d0604c832c45759c4604c832c85749c4604c832c45755c4604c832c86745c4604c832c85745c4604c83288d84dd93254432a19801914354432a29801914254432e05644c95114432e4132545601443288d841d932940328c5811d93294032989841c132940329c1811c13294032989841c132540329c1811c13254032948805ca4354032948805ce4254032919841c13254032951811c13254032929841c13254032961811c13254032948805d1325403290d841c13254032945811c13254032b09841c13254032b41811c1325403294a861c13254032c4a861c13254032d0a841c13254032949841c13254032d09841c13254032909841c13254032d42811c13254032949811c13254032d41811c13254032941811c132540328b1801c5640c94184e87995320c941a4980195320c9418b1801d1610c941d05435c44354841e05535096110841925859cb6350441915859cf6250441d11535c35250441b2180d4d5250441b058594d5250441931809d43250441d05754c83250441e055358941d404
  | 3 => 0x3710f4cd4900000000d040c7f29d25000db1288a45840504c3410c40012a514e819030000a4000830008e01cb200c8914c000014e000b70ac800010c4b400000004bc45490172c45d028ce2989b07416260a00246d2888b000003e433390f4178480bc1e0145b2d4270000b0014a500ad000004d8232
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xa805008106060166ac00a88000048298ea0c21e904700004605801141912017290d500ca28322402e7212a019450644805d13254032c80c250238264a806590284604704c9500cb20308c08e0992a01948265080549600cb31904ca100a9ac0196432099420153580324864832242a64b006520460644805d1320c940980c8900a18a4a02611099814c7050940483200a6c08e0a128090502659545c0320c020d00aa300192c218041a016460032544300824132842a64b0065084a06508058c3248510a204aac6b806490a2188184188704c53044218330318e090a4088620610631c12148110
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1870
  | 5 => 10236
  | 4 => 5876
  | 3 => 335
  | 2 => 23
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
  | 6 => packedAt gbK6 (57966+((h/623+packedAt gbK6 (50490+(h % 623)*12) 12) % 2469)*12) 12
  | 5 => packedAt gbK5 (436736+((h/3412+packedAt gbK5 (388968+(h % 3412)*14) 14) % 12284)*15) 15
  | 4 => packedAt gbK4 (315336+((h/1958+packedAt gbK4 (287924+(h % 1958)*14) 14) % 8532)*14) 14
  | 3 => packedAt gbK3 (21099+((h/111+packedAt gbK3 (20100+(h % 111)*9) 9) % 443)*10) 10
  | 2 => packedAt gbK2 (1668+((h/7+packedAt gbK2 (1633+(h % 7)*5) 5) % 30)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe1fe1ff1fc7ffffe0e31f1f83f1ffffe0931ff
  | 1 => 0xfe1fe1fe3f83c78ff03e3e3fc7e3870e36ce93
  | 2 => 0x1ffe003ffc07f1ffc03fc007fc07f1c70f1c
  | 3 => 0xffe000003ffff801ffffc00007fff801f80fe0
  | 4 => 0xffffffffc0000001fffffffff8000001fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x20020002040000000000404800048100001025
  | 1 => 0x4444446048188910301212118321122c124692
  | 2 => 0x1d888ca491299602d6403482954824e4c70b18
  | 3 => 0x88c1d949225303256ab4800526927049780dc0
  | 4 => 0x11111180036224498d29292630004081ada000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeeeeaa8feeeeaa8feeeeaa8feeeeaa8feeeeaa8feeeeaa8feeeeaa8feeeeaa8feeeeaa8feeeeaa8feeeeaa8feeeeaa8feeeeaa8feeeeaa8feeeeaa8feeeeaa8, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12927
namespace PEqualNP.Outside.L_meta_12927
open PEqualNP.Outside.L_meta_12927.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 23 := bgb_2_0
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
theorem bgb_3_288 : Interval gbAtlas 3 288 47 := block_range (n:=47) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 335 := (concat (concat bgb_3_0 bgb_3_96) (concat bgb_3_192 bgb_3_288))
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
theorem bgb_4_5856 : Interval gbAtlas 4 5856 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 5876 := (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_96 bgb_4_192)) (concat (concat bgb_4_288 bgb_4_384) (concat bgb_4_480 bgb_4_576))) (concat (concat (concat bgb_4_672 bgb_4_768) (concat bgb_4_864 bgb_4_960)) (concat (concat bgb_4_1056 bgb_4_1152) (concat bgb_4_1248 bgb_4_1344)))) (concat (concat (concat (concat bgb_4_1440 bgb_4_1536) (concat bgb_4_1632 bgb_4_1728)) (concat (concat bgb_4_1824 bgb_4_1920) (concat bgb_4_2016 bgb_4_2112))) (concat (concat (concat bgb_4_2208 bgb_4_2304) (concat bgb_4_2400 bgb_4_2496)) (concat (concat bgb_4_2592 bgb_4_2688) (concat bgb_4_2784 bgb_4_2880))))) (concat (concat (concat (concat bgb_4_2976 (concat bgb_4_3072 bgb_4_3168)) (concat (concat bgb_4_3264 bgb_4_3360) (concat bgb_4_3456 bgb_4_3552))) (concat (concat (concat bgb_4_3648 bgb_4_3744) (concat bgb_4_3840 bgb_4_3936)) (concat (concat bgb_4_4032 bgb_4_4128) (concat bgb_4_4224 bgb_4_4320)))) (concat (concat (concat (concat bgb_4_4416 bgb_4_4512) (concat bgb_4_4608 bgb_4_4704)) (concat (concat bgb_4_4800 bgb_4_4896) (concat bgb_4_4992 bgb_4_5088))) (concat (concat (concat bgb_4_5184 bgb_4_5280) (concat bgb_4_5376 bgb_4_5472)) (concat (concat bgb_4_5568 bgb_4_5664) (concat bgb_4_5760 bgb_4_5856))))))
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
theorem bgb_5_10176 : Interval gbAtlas 5 10176 60 := block_range (n:=60) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 10236 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat bgb_5_288 (concat bgb_5_384 bgb_5_480))) (concat (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)) (concat (concat bgb_5_864 bgb_5_960) (concat bgb_5_1056 bgb_5_1152)))) (concat (concat (concat bgb_5_1248 (concat bgb_5_1344 bgb_5_1440)) (concat bgb_5_1536 (concat bgb_5_1632 bgb_5_1728))) (concat (concat bgb_5_1824 (concat bgb_5_1920 bgb_5_2016)) (concat (concat bgb_5_2112 bgb_5_2208) (concat bgb_5_2304 bgb_5_2400))))) (concat (concat (concat (concat bgb_5_2496 (concat bgb_5_2592 bgb_5_2688)) (concat bgb_5_2784 (concat bgb_5_2880 bgb_5_2976))) (concat (concat bgb_5_3072 (concat bgb_5_3168 bgb_5_3264)) (concat (concat bgb_5_3360 bgb_5_3456) (concat bgb_5_3552 bgb_5_3648)))) (concat (concat (concat bgb_5_3744 (concat bgb_5_3840 bgb_5_3936)) (concat (concat bgb_5_4032 bgb_5_4128) (concat bgb_5_4224 bgb_5_4320))) (concat (concat bgb_5_4416 (concat bgb_5_4512 bgb_5_4608)) (concat (concat bgb_5_4704 bgb_5_4800) (concat bgb_5_4896 bgb_5_4992)))))) (concat (concat (concat (concat (concat bgb_5_5088 (concat bgb_5_5184 bgb_5_5280)) (concat bgb_5_5376 (concat bgb_5_5472 bgb_5_5568))) (concat (concat bgb_5_5664 (concat bgb_5_5760 bgb_5_5856)) (concat (concat bgb_5_5952 bgb_5_6048) (concat bgb_5_6144 bgb_5_6240)))) (concat (concat (concat bgb_5_6336 (concat bgb_5_6432 bgb_5_6528)) (concat (concat bgb_5_6624 bgb_5_6720) (concat bgb_5_6816 bgb_5_6912))) (concat (concat bgb_5_7008 (concat bgb_5_7104 bgb_5_7200)) (concat (concat bgb_5_7296 bgb_5_7392) (concat bgb_5_7488 bgb_5_7584))))) (concat (concat (concat (concat bgb_5_7680 (concat bgb_5_7776 bgb_5_7872)) (concat bgb_5_7968 (concat bgb_5_8064 bgb_5_8160))) (concat (concat bgb_5_8256 (concat bgb_5_8352 bgb_5_8448)) (concat (concat bgb_5_8544 bgb_5_8640) (concat bgb_5_8736 bgb_5_8832)))) (concat (concat (concat bgb_5_8928 (concat bgb_5_9024 bgb_5_9120)) (concat (concat bgb_5_9216 bgb_5_9312) (concat bgb_5_9408 bgb_5_9504))) (concat (concat bgb_5_9600 (concat bgb_5_9696 bgb_5_9792)) (concat (concat bgb_5_9888 bgb_5_9984) (concat bgb_5_10080 bgb_5_10176)))))))
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
theorem bgb_6_1824 : Interval gbAtlas 6 1824 46 := block_range (n:=46) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1870 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 bgb_6_576) (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)))) (concat (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344))) (concat (concat bgb_6_1440 bgb_6_1536) (concat bgb_6_1632 (concat bgb_6_1728 bgb_6_1824)))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfeeefeeefeeeeaa8feeefeeefeeeeaa8feeefeeefeeeeaa8feeefeeefeeeeaa8feeefeeefeeeeaa8feeefeeefeeeeaa8feeefeeefeeeeaa8feeefeeefeeeeaa8
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075694 * 2 ^ 32 + 4277070504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12927.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,3]⟩,⟨.or,[2,3]⟩,⟨.or,[4,5]⟩,⟨.or,[1,5]⟩,⟨.or,[0,6]⟩,⟨.or,[1,10]⟩,⟨.and,[9,10]⟩,⟨.and,[0,7]⟩,⟨.or,[8,13]⟩,⟨.and,[11,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075694 * 2 ^ 32 + 4277070504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075694 * 2 ^ 32 + 4277070504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12927

open PEqualNP.Outside.L_meta_12927 in
theorem PEqualNP.Outside.L_meta_12927 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075694 * 2 ^ 32 + 4277070504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075694 * 2 ^ 32 + 4277070504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
