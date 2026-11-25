import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12857.Model
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


end PEqualNP.Outside.L_meta_12857.Model

namespace PEqualNP.Outside.L_meta_12857
open PEqualNP.Outside.L_meta_12857.Model
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

end PEqualNP.Outside.L_meta_12857

namespace PEqualNP.Outside.L_meta_12857
open PEqualNP.Outside.L_meta_12857.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x3923815400005939a4098a1e189001b1c0800a0085480065caa3321059f12006800060000003ce80108898022188014a00004220004d08218208bff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x41ff30083fc6010778c020fe98041fc30083b860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43bca7885794f10fea9e217d53c43baa7885754f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887f90710fea0e21fc41c43fe63887f8c710fe98e21fc31c43fe43887f88710fe90e21fc21c43fe81887f90310fea0621fc40c43fe61887f8c310ef18621fd30c43f86188770c310ff90621fe20c43fa41887f08310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff99421fe32843fa65087f0ca10bea8c21ff41843ee83087f90610fea0c21fc41843e883087fcc610ff18c21fd31843f863087fc8610fb90c21fe21843fa43087f08610fa10c217e50843fe81087f90210fea0421fc40843fe61087f8c210ef18421fd30843f86108770c210ff90421fe20843fa41087f08210ff88421f710843f621087fd5110bfaa221bf544427ea8887f95110bf2a221fd54442faa8887f15110be2a221bc5444278a8887fd4d10bfa9a21df53442bea6887f94d10bf29a21fd53442faa6887f14d10be29a21dc53442b8a6887fd0d10ff21a21fd43443f886887fd4910bfa9221ef52442dea4887f94910bf29221fd52442faa4887f14910be29221ec52442d8a4887fd0910ff21221fd42443f884887fcc910ff19221fd32443f864887fd0510ff20a21fd41443f882887fcc510ff18a21fd31443f862887fc8510ff10a21fd21443f842887fd0110ff20221fd40443f880887fcc110ff18221de30443fa60887f0c110ee18221ff20443fc40887f48110fe10221ff10443f620887f84110fb08221ff54042fea8087f95010bf2a021fd54042faa8087f15010be2a021ff53042fea6087f94c10bf29821fd53042faa6087f14c10be29821ff43043fc86087f50c10fe21821ff52042fea4087f94810bf29021fd52042faa4087f14810be29021ff42043fc84087f50810fe21021ff32043fc64087f4c810fe190217e51043fe82087dd0410ff20821fd41043f882087d10410ff98821fe31043fa62087f0c410ff90821f721043fc42087f48410fe10821f421042fca0087fd0010ff20021fd40043f880087fcc010ff18021de30043fa60087f0c010ee18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xd310c3ba62187f0c430ee18861ff210c3fc42187f48430fe108617e500c3fe80187f90030fea0061fc400c3fe601877cc030ff18061fa300c3fa6018774c030fc98061df540c3bca8187755030ee2a061df520c3bca4187754830ee29061df420c3bc84187750830ee21061df510c3bca2187754430ee28861df410c3bc82187750430ee20861df210c3bc42187748430ee10861de500c2bca0187694030efa0061de400c3ba80187710030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20ef29e415e53c83faa7905f54f20eea9e415d53c83f8a7905f14f20ffa1e41fe43c83fa87907f10f20ffa1641fe42c83fa85907f10b20ff99641fe32c83fa65907f0cb20ffa8e41fe51c82fca3907f54720bea8e41fc51c83fe83907f90720fea0e41fc41c83fe63907f8c720fe98e41fc31c83fe43907f88720fe90e41fc21c83fe81907f90320fea0641fc40c83fe61907f8c320ef18641fd30c83f86190770c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ffa1c41fe43883fa87107f10e20bea9441ff42883de85107f90a20fea1441fc42883d885107fcca20ff19441fd32883f865107fd4620ff28c417e51883faa3105f54620fe28c41ff41883fc83107f50620fe20c41ff31883fc63107f4c620fe18c41ff21883fc43107b88620fe90c41fc21883d843105f94220ffa0441fe40883fa81107f10220ff98441fe30883bc61107f4c220fe18441dc30883fe41107bc8220fd90441ff54482fea8906fd51209faa241fe54482fca8907f55120beaa241fc54482f8a8906f151209e2a241ff53482fea69077d4d20afa9a41fe53482fca6907f54d20bea9a41fc53482f8a6907714d20ae29a41ff43483fc86907f50d20fe21a41ff42483fc84907f50920fe21241ff32483fc64907f4c920fe19241ff51482fea2907dd4520bba8a41fe51483faa2907f14520be28a41f451482e8a2907fd0520ff20a41fd41483f882907fcc520ff18a41fd31483f862907fc8520ff10a41fd21483f842907fd0120ff20241fd40483f880907fcc120ff18241de30483fa60907f0c120ee18241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041fd54082faa8107f15020be2a041ff53082fea6107f94c20bf29841fd53082faa6107f14c20be29841ff43083fc86107f50c20fe218417e52083fe84107bd0820ff21041fd42083f884107b10820ff99041fe32083fa64107f0c820ffa8841fe51082fca2107f54420bea8841fc51083fe82107f90420fea0841fc41083fe62107f8c420fe98841fc31083fe42107f88420f710841fd21083f842107b08420bf28041ff40083fc80107f50020fe20
  | 2 => 0x3f842a07fd0140fda0281fe405037c80a05f95040ffa9881fe53102fca6207f54c40bea9881fc53103fe86207f90c40fea1881fc43103fea4207f94840bf29081fd52102faa4207f14840ffa1081fe421037c84207f50840fe21081bc42103fe64207f8c840fe99081fc32103fea2207f94440bf28881fd51102faa2207f14440ffa0881fe411037c82207f50440fe20881bc41103fe62207f8c440fe98881fc31103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9985fd5330ff2a6617e54cc3faa9985f55330fe2a6617c54cc3fe87987f90f30fea1e61fc43cc3fea5987f94b30bf29661fd52cc2faa5987f14b30ffa1661fe42cc3fa85987f10b30ff99661fe32cc3fa65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fea0e61fc41cc3fe63987f8c730fe98e61fc31cc3fe43987f88730fe90e61fc21cc3fe81987f90330fea0661fc40cc3fea9185fd5230ff2a4617e548c3faa9185f55230fe2a4617c548c2faa7187fd0e30efa1c61fe438c3bc87187f50e30eea1c61fc438c3b887187fd4a30ff294617e528c3faa5185f54a30fe29461ff428c3fc85187f50a30fe21461ff328c3be65187f8ca30ef19461fd328c3ba65187f0ca30ee19461ff518c3fca3185f94630fea8c617d518c3f8a3187fd0630ff20c61fd418c3f883187fcc630ef98c61fe318c3bc63187f4c630ee98c61fc318c3b863187fc8630ff10c61fd218c3f843185f94230ffa0461fe408c3fa81187f10230ff98461df308c3f6611877d5230ef2a461dd548c3b8a91877d4a30ef29461dd528c3b8a51877d0a30ef21461dd428c3b8851877d4630ef28c61dd518c3b8a31877d0630ef20c61dd418c3b8831877c8630ef10c61dd218c3b843185794230efa0461de408c3ba81187710230ffaa2617f544c3fca8985f95130feaa2617d544c3f8a8985f15130ffa1a61fe434c3fa86987f10d30ffa92617f524c3fca4987f54930fe292617c524c3fe84987f90930fea1261fc424c3fe64987f8c930fe99261fc324c3fea2985fd4530ff28a61fd514c3f8a2985f14530ffa0a61fe414c3fa82987f10530ff98a61fe314c3fa62987f0c530ff90a61fe214c3fa42987f08530ffa0261fe404c3fa80987f10130ff98261fb304c3fc6098778c130ffaa0617f540c3fca8185f95030feaa0617d540c3f8a8185f15030bf29861ff430c3be86187f90c30ef21861fd430c3ba86187f10c30ee21861ff520c3fca4185f94830fea90617d520c3f8a4187fd0830ff21061fd420c3f884187fcc830ef99061fe320c3bc64187f4c830ee99061fc320c3b864187fd4430ff288617e510c3faa2185f54430fe28861ff410c3fc82187f50430fe20861ff310c3be62187f8c430ef18861f
  | 3 => 0xa190df94321fea86437d50c87f8a190ffd5221bfaa443fe54886fca910ff55221beaa443fc54886f8a910ffd4e21bfa9c43fe53886fca710ff54e21bea9c43fc53886f8a710ffd0e21ff21c43fd43887f88710df54a21ffa1443fe42887fa8510ff10a21ff99443fe32887fa6510ff0ca21bf28c43ff41887fc8310ff50621fe20c43ff31887fc6310ff4c621fe18c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fea690dfd4d21ff29a437e53487faa690df54d21fe29a437c53487fe8690ff90d21fea1a43fc43487fe8490ff90921fea1243fc42487fe6490ff8c921fe99243fc32487fe8290ff90521fea0a43fc41487fe6290ff8c521fe98a43fc31487fe4290fdc8521ff10a43ee21487fea090dfd4121ff28243fd50487f8a090df14121ffaa0437f54087fca810df95021feaa0437d54087f8a810df15021ffa98437f53087fca610df94c21ef298435e53087faa610df54c21eea98435d53087f8a610df14c21ffa1843fe43087fa8610ff10c21bf29043ff42087fc8410ff50821fe21043ff32087fc6410ff4c821fe190437e51087fe8210ff90421fea0843fc41087fe6210ff8c421fe98843fc31087fe4210fbc8421ff10843f621087fa4210fb48421fa90843e521087fea010ff94021bf28043fd50086faa010ff14021ffa9e81fe53d02fca7a07794f40af29e81fd53d02faa7a07754f40aea9e81fc53d03fe87a07f90f40fea1e81fc43d03fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681fe42d03fa85a07f10b40ff99681fe32d03fa65a07f0cb40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a07f90740fea0e81fc41d03fe63a07f8c740fe98e81fc31d03fe43a07f88740fe90e81fc21d02faa9207fd4e40ff29c817e53903faa7205f54e40fe29c81ff43903fc87207f50e40fe21c81ff52903fca5205f94a40fea94817d52903f8a5207fd0a40ff21481be42903fa85207f10a40de21481ff32903fc65207f4ca40fe19481ff51903fca3205f94640fea8c817d51903f8a3207fd0640ff20c81be41903fa83207f10640de20c81ff31903fc63207f4c640fe18c81ff21903fc43207f48640fe10c817e50903fe81206fd0240fda0481ff53502fea6a077d4d40afa9a81fe53503faa6a07f14d40be29a81dc53502b8a6a07fd0d40ff21a81fd43503f886a07fd4940bfa9281ef52502dea4a07f94940fea9281fc52502f8a4a07b14940b629281ff42503fc84a07f50940fe21281ff32503fc64a07f4c940fe19281ff51502fea2a07dd4540bba8a81fe51503faa2a07f14540be28a81f451502e8a2a07fd0540ff20a81fd41503f882a07fcc540ff18a81fd31503f862a07fc8540ff10a81fd215
  | 4 => 0xffd0a41ff21483fd42907f88520ffcca41ff19483fd32907f86520df94641ffa0c83bf41907ee8320ffd4241ff284837e50907faa120df54241fe28483ff53506fea6a0ff94d41fea9a83fc53506f8a6a0ffd0d41ff21a83fd43507f886a0ffd4941bfa9283fe52507faa4a0ff14941be29283ff42507fc84a0ff50941fe21283ff32507fc64a0ff4c941fe19283ff41507ee82a0ff90541df20a83ff50506fea0a0ff94141fea8283fc50506f8a0a0df95041ffa9883fe53106fca620f794c41af29883fd53106faa620f754c41aea9883fc53107fe8620ff90c41fea1883fc43107fea420ff94841bf29083fd52106faa420ff14841ffa1083fe42107fa8420ff10841ff99083fe32107fa6420ff0c841bf28883ff411077e8220ff90441fb20883fd411077a8220fd50441daa0883ff50107fca020df94041fea80837d50107f8a020ffd5331bfaa663fe54cc6fca998ff55331beaa663fc54cc6f8a998ffd0f31ff21e63de43cc7fa8798f750f31fe21e63ff52cc7fca598df94b31fea96637d52cc7f8a598ffd0b31ff21663fd42cc7f88598ffccb31ef99663fe32cc7fa6598f74cb31fe19663ff41cc7fc8398ff50731fe20e63ff50cc7fca198df94331fea86637d50cc7f8a198ffd5231bfaa463fe548c6fca918ff55231beaa463fc548c6f8a918df54e31ffa1c63fe438c7fa8718ff10e31ffa9463fe528c6fca518ff54a31bea9463fc528c7fe8518ff90a31fea1463fc428c7fe6518ff8ca31fe99463fc328c6fca318ffd0631ff20c63fd418c7f88318ffcc631ef98c63f7318c7fea118ff94231bf28463fd508c6faa118ff14231ffaa2637f544c7fca898df95131feaa2637d544c7f8a898df15131ffa1a63fe434c7bc8698ff50d31eea1a63fc434c7fea498dfd4931ff29263fd524c7f8a498df14931ffa1263fe424c7fa8498ff10931ff99263df324c7fc6498ff4c931ee99263fc324c7fe8298ff90531fea0a63fc414c7fe6298fdcc531ff18a63de314c7fea098dfd4131ff28263fd504c7f8a098df14131ffaa0637f540c7fca818df95031feaa0637d540c7f8a818df15031bf29863ff430c7fc8618ff50c31fe21863ff520c7fca418df94831fea90637d520c7f8a418ffd0831ff21063fd420c7f88418ffcc831ff19063fd320c7f86418df94431ffa0863fe410c7fa8218ff10431ff98863df310c7fc6218fd8c431fe98863dd310c7ea6218ffd4031ff280637e500c7faa018df54031fe28063ff54c86fea990ff95321bf2a643fd54c86faa990ff15321be2a643ff53c86fea790ff94f21bf29e43fd53c86faa790ff14f21be29e43ff43c87fc8790ff50f21fe21e43ff42c87fc8590ff50b21fe21643ff32c87fc6590ff4cb21fe19643ff41c87fc8390ff50721fe20e43ff31c87fc6390ff4c721fe18e43ff50c87fc
  | 5 => 0x443ff288877e5110ffaa221df54443fe28887ff5010ffca021df94043fea80877d5010ff8a021ffd4f42ff29e857e53d0bfaa7a15f54f42fe29e85ff43d0bfc87a17f50f42fe21e85ff51d0bfca3a15f94742fea8e857d51d0bf8a3a17fd4342ff286857e50d0bfaa1a15f54342fe286857d5490bfea7217f94e42bf29c85fd5390afaa7217f14e42ffa1c85fe4390bfa87217f10e42bf29485ff4290b7e85217bd0a42ffa8c85fe5190afca3217f54642bea8c85fc5190bfea1217f94242bf28485fd5090afaa1217f14242ffa9a857f5350bfca6a17f54d42fe29a857c5350bfe86a17f90d42fea1a85fc4350bfe84a17bd0942ff21285be4250bfea2a15fd4542ff28a85fd5150bf8a2a15f14542ffa82857f5050bfca0a17f54142fe282857c5050afca8217fd4c42ff298857e5310bbca6215794c42fea98857d5310bbaa6215754c42fe29885ff4310bfc86217f50c42fe218857e5210bfe84216fd0842ff21085ee4210bfa84216f50842f6a1085ad4210bfea2217f94442bf28885fd5110afaa2217f14442ffa8085fe5010afca0217f54042bea8085fc5010bfea9995fd5332ff2a6657e54ccbfaa9995f55332fe2a6657c54ccbfe87997f90f32ef21e65fd43ccbba87997f10f32ffa1665fe42ccbfa85997f10b32ffa8e65fe51ccafca3997f54732bea8e65fc51ccbfea1997f94332bf28665fd50ccafaa1997f14332ffaa4657f548cbfca9195f95232feaa4657d548cbf8a9195f15232bea9c65ff438cbfc87197f50e32fe21c657e528cbfe85197f90a32fea1465fc428cbfe651977cca32f799465ff518cbfca3195f94632fea8c657d518cbf8a3197fd4232ff284657e508cbfaa1195f54232fe28465ff544cafea8997f95132bf2a265fd544cafaa8997f15132be2a265ff434cbfc86997790d32fea1a65dd434cbf886997fd0932ff21265fd424cbf884997fcc932f799265fe324cbbc64997fd4532bfa8a65fe514cbfaa2997f14532be28a65ff504cafea0997f94132fea8265fc504caf8a0997fd5032bfaa065fe540cafca8197f55032beaa065fc540caf8a8195f94c32ffa1865fe430cbfa86197f10c32bf29065ff420cbfc84197f50832fe21065ff320cbbe64197f8c832f719065fd320cbba64197b4c832ffa8865fe510cafca2197f54432bea8865fc510cbfea0197f94032bf28065fd500cafaa0197f14032ffa9e83fe53d06fca7a0ff54f41bea9e83fc53d07fe87a0ff90f41fea1e83fc43d07fea5a0ff94b41bf29683fd52d06faa5a0ff14b41ffa1683fe42d07fa85a0ff10b41ff99683fe32d07fa65a0ff0cb41ffa8683fe50d06fca1a0ff54341bea8683fc50d06faa920ffd4e41ff29c837e53907faa720df54e41fe29c83ff43907fc8720ff50e41fe21c83ff52907fca520df94a41fea94837d52907f8a520
  | 6 => 0x1600a00201203c04000200200001e01600200401007600000601600001200607000c00003000602c00802604800c01603a00007003e00000801004800000802604000603201400001a00201400201a05e00200201800000c00e02200001802a03200000800000004602c01401001000000e03800200202400200400001c00200c00200000800400000c00600000000000c00a00003e02c00a00000201e00c00200400400200401600600000800000600400004000006a03401600000204c00a02000c00000400800401400002400000000600400001e00200000003600001a03400200000202800e00000c02401404604600000800400001000400002402200600000001402601000400000600200e00202e00a00200800800000800200000000800000204a01805c00601603202000402200004802602600000004c00400e01801005a00600200800c00601600000600800400a01200400a04000400000200200e00200c01a00001404600001400200001000600a00200203400402203000201a01601000200400000000200003200402a00800800202001c00001c00600c00000000601400200001800802400000201202403e03400000400000a00400401004200c02000200a00201200c02e00000000001000600204604400200000400402e00201001008402800200e03a00600203a00600204201200801e00600201201800200000800800000001803e01200c00001001c00a02c00200000000202600200201000000200600000000001a00000002600601c00a02407803600201800001800402400000400000600200c00601800001400800200e00a02000005600000201a01200800400000200001204000801400000a01202000a00600000a00005600600001800600200000c00000200201e00e00400200000400000a03400205c01802000000800000400800002c00800a07e00001800602000000000c00000001803200800e00c00200800800400200600804a09200800e01408800000000004606c00800a01c00201000000000c00400001c006000025ff52d0ffca5a1df94b43fea96877d52d0ff8a5a1ffd4743ff28e877e51d0ffaa3a1df54743fe28e87ff50d0ffca1a1df94343fea86877d50d0ff8a1a1df55243bf29c87ff4390f7e8721f7d0e43ffa9487fe5290efca521ff54a43bea9487fc5290ffea321ff94643bf28c87fd5190efaa321ff14643ffa8487fe5090efca121ff54243bea8487fc5090ffe86a1f7d0d43ff21a87be4350ffea4a1dfd4943ff29287fd5250ff8a4a1df14943ffa8a877f5150ffca2a1ff54543fe28a877c5150ffea0a1dfd4143ff28287fd5050ff8a0a1df14143bf2a0877e5310ffe8621efd0c43ff21887de4310ffa8621ef50c43eea1887ff5210ffca421df94843fea90877d5210ff8a421ffd4
  | 7 => 0xd8000000e9c784635249184001cd4001bd0000cd5894c85b5400049145452d41d9540019f90b9174001a914689b09f93ad7dd7f9b34bc0294be86d581469d8e94ed79c34c244c0ca95d00fc14c938cb859318b02a0520001888874d704b047c1ac750ba4501621a951cd0d9b45b0c13c5a0dd8e951180f92080ccc900c9ce0000aec91ca845b1a144c02397b587cec82200009d10c8001cfd4d40f020467173d538de0258564be52dc2e89b8c5000c725974074744001d081452c0c74f095f40016ad5d4000548c78000ac43300006bc0008c80014e4a0d4888dc9940006e4914150cc4facd1965d7e0001d64a6405cf500004200014400014107b879c224408001a4494cdb0640feda79625a9896cf5d964000265ad8868c095303cc000f0d4096744f081c00119000175108c1090e8d883b8bf51780d95c8fd92f58757a99fc119b740e01e0b598c04f53d8ab5300d35c0cf7d8493815841b800002c00000065c8417fcea10c4000001840001a5400000000000057d5a8001614714005691505bb5160001360000000c3c981cf0d6905cd01c29081d857287185b5bec8f00a042c000290da88bc2d8390000f657600004783380005688d8541d89da8b98d7d280988b8ca41acccb9238414dacf40614aa91ad1e4d218f1340f2c8383250242c4d556dca893b0fb44a0585b8d890cd1458001638000000000154a54000000ca8eb0d5c3eda000014357c18a5c8980dc3553cef5c456cda891d4000001405d3d9d07c4d156680c41d8fcc011badc9c040dfd3695d84e0c48be1851b180f46c4765770cc96a88b132127917ce846b837035575453cb7441c04d7b9b212f1a21719c401ec0eda64da540c65882c5f96015708a93cd37c2a47bcb38b00db4e18a78c9426db50a38379b99449d506499bd6457e8f9c3b02018ddd7570c7603a4c81870f14dbc604580705244acd7d8c5d700a7c001a4d26d5494d8e6cd05b3c094b600dc19848c8a4001b242c000186c9640000000008449dce59b70884ee0efc2acca52315c0f29b691c58ad4b40005d99280001052c85898c9ba97b0000000bd43180d5b800c10595001c0c71005d6135c115a112109a859c3e52b9a04b09be0b28428b20ea9491c800012a42994a8c591b16b11b8411129b9c68c00000142d3c061000205202400000601201e01400e00200000800000002a00000000e01a00a00800001e00c00402400a00400200000400400c04600000600400000000a00e04000000400200c00c03c02001603200c00601000400003400001e00c01400a01c00200c0000000a000a01602000000600001e01800400002c01a02000402c00203e00400000c00c00200a00a00201200000200408202001a00000402600602402400e03a0480a600201605604600a01a03001200800200001a00201402000600a
  | 8 => 0xcb40c445358118d0de80e80011a80891317cc6a8854001ba5ce81a164c7c0001c990bcd2d2c41f4595105d91835cd8e60000ed40000000017f00b91700010a4000ffdbdca511999ad065229ab91808a1c912b4cb02d01dd509085a6d39c3dc000758f38e2cf341359792edbe9c78434000001420000cb4cd883557800000167c000000001298880000000fa1bc40018040605bc904001d288d4529c581e80009d503c000c185f40012a916400040400131134800166194ce54655a6188d884e1dba152087d354c00de4b340015615fcead2d92745e4c558d8498251c18fddcf53e0af0c65864bdcfc474d6715f95b96c83bc15d339591d4c27c1958edac57d4d91905148dd536cd48af81853d4e040001fc9c8b955ec0a80007d51947e121db28bb53c800177c0004a8edc678020c4092ca98001a255581d4df4000000000000ddc000000b65d10a300002b878993ca90e450ac598bf800163403922504959c001cf8fa85d185d4fdc3c000a2c85009c30808c3f404800102c6ccf24000c69d1c0090cd9cd4dc8152e8ca0384b698b4cf98a0d6dc49c08538000f8cef0000898bc80000000009e9021514829ab4ab83e0b1d5681c93297817f500189c39c0019000006b455c0008ed4ac5e01703e86994c0bd00015ace79cac0011381100014f8b313b4138e3160dcbc001a1c97475c50cbec000000ed191dcd03ac7a106926844dd94e81315829295115bf53bd31dbc09d8000000000001af8001b148ccab0d0dd80180000000000000dc5a740005c512c4ac079481b315819a507162ce40681800001ae8001291a08864000329935b4185845c0015cc07c000e69c70f3cd98210000000000b109280010f1c300007d0db800171c000a04000858000808000000000ff00001646d08f40000000007803d0ff4000a9c000d5037597d3987f800048970595d5e434060c935c50c7c000000ad00d00003d4000da1afdad42c8668c249bc37c88ca3515453125d8e176c00166423000130478ccac2b1689044560bad460f699e9cb11c8abc76cc99d24f306b171451129dbc80013097380000284fc559da59d4000000001c14001144fd0f1dbd5a813ecd851f524c23cd09159d9c00000000075400000025db2c0007e59d88c5b85d70d80f1166c89431c0016c52ac9e4448eb96fc5443342ed9854749414b872038c9ec77c2800b56508c0000fd40011c0d1cfbd8f40640009e0620af5bfc218990fb0a1812da8c4d87a5d0c8b8799a0d1110e554c00150c00000000155c00036800063da403644247680007f40000000000002f43580015a563d06cce410cafcfe0459039abc000740ee43c0d40b550a80010918bcd296d040c4014a0f71c04001b086fd84c0017a5b48001b64961720685d41c957853340001b53d00008e9c859c4000000ac92d09fc0000007
  | 9 => 0x83c5a947c9593780000fd14c0017c8279881790cdc0019b09f1948128d61ca8455654001a7c2856e4f48dec0000003a9d555242089386dd818ccc00127c7cc321c748306e86188108887dc2d5778e119dc791a48945cb850414854cb0ce24ae57589500015109300005dc574644b7d4f5d14d759980014d0ad9af4001264b5d7880014e1958eec439bd8228f95b890742a867557cb2c6617e4c3030450946d4cc0018c4cf43507296d96f0891271c65694c1d9087716818797ad3fcaad2b0924e3c1c417c1bdae5d7800175d0dc998a0113cf849a111c468f9800134ce20480ea4fc800000000000000149c000ecd3e4000000098000001d2d838e7c0008000007b000000000000121910c0ad19dd0400090ce0cc10aa44d1d21391108000911749678fa44404b56bc268804a153759b52cd7340018fc0004f98248e19e4e6400143c000289c5c6952e5b585540000010b4000001255220001c7ca4c09000071c0019900017113dc2bca58001c206f5629b7820c4e9a9c000a259a13f55418099686d9030f184517c490877898c00199d98d259cec0000003f95895dc67c579ac1c39b016a19207a8001c691dc0a493dc8c9f5a7121586983000000148c01c0005e8a117748d000070c00060932d951618a8d769aad6a59c00007940017bc5d55a1028ae022c8f9d4858c5149701f12bd0f90ec4c94c5980870bbc2dc124820919478380e881894718600243f16b91bc33d44cc217ece48f88d252e115c000ec0001a58b81684cbd0e0031b0486c664b24738dcc7f1b60f44848fb9bb13a8174e353e8651cb4215ab0080819324001d7d73030cb78cfc9cc6ad1885ad3884e46ece71424000001c4c000eb47b4311a28b44388730690f00d10c4c00199400000123c9559f0464f918d49a5ca432c0017d03940002b57094a41f9289bf1744ed99409b48e46318540000b00014b0344dc0a44c9c70814c00161d914000000f204bca8000000196061c00145c8b53f8ae81a98a83fc0016f8968001465c1d08800000103582cd39798c04001d6c000000a700016d55f11ed0d1bbc0012340001d0b4c000000000d94ad4000adc5902759880000146e11f0e911d80010d4001ad0000001cc9b111b47ad2f85182fcd4d9a8000949094c6d9100014f0001c000351fd564001330000000000cec5c000143800000109c0005ccf78000629c116058e565897c068cc02e028da39121b91c542f1204bd8ce09858cc7fd385d58234b886f08acc61b7ca5c130399cc16b4b6d74cec4495c2c51cf6dd99da0b1829d358f4c0007e81600006019f5bf8dd149916952cc8dd4416d4184ccf053c425473c21c00000181da5168c36c64ce28c29ce5d351e00015c5c60460000a2800196c35dc24a6c66d6e9aed9c93710b0735b94d4578d69da3122cba92514453f0ba1a3c2c
  | 10 => 0x1284000000001b4c178bb8c89844000000d590513192d50fd054000e38361364000e1400133cac07c941507d9ec00000000000156d5181cc000000001aa4000c2c000000638474bf0121099018000001151d198b8aa00016115b000124148403c62c1010f4084419765544a684ed0a1ae13a0001a5c0e4878d9cdf856cc14c34f5501d6eda848fd9185b96990117a05fd5e00003145a44d5945ccc071c6c0011241401b0b9cbfcbb11a164972c3d8000054000ff8001060e985c84303a163034916c71089c24099d794a1cb3c261141430c381a4fe8158001d311a5924000d64e8c19cdc9aa89799e0551575a356c06f86250c174080c9c4b15cc43c885d8f8e5c00000000016800130dd384a400095db1c0011e8b71345594000e08000000001aa13955d13a51355359b8d3c84d0792fc9200506889acb51939bcd20dac8ef843c018e0072d6e049cb90775d5d400f58301ca05ec5252a14945f183ca3d58c6c8cf17256f5261200d8c824a08f815e904100846c2e592cee80007ecbccdf1529100d780bdd6806d6404851d11f8bc5cdc3b551c6a504db6c001a680006a15b528c6c000159818c059a2c749898570000000d315bd4bdbb8000e4d5544dcfe5970a75609b384710141909c02f8001a181e590c271350a20b49d8c000ce8ebdb5ce500015504b83c404582118dadc4453b8901af0f7400024900cf60a48e7486000000024c0004c4000000000b05429be411c700001450a614e8
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x421042fa6008410be580210437565084109d59421042f66408410bd19021043d66308410f558c21042f66208410f998821043775208410f994821043755208410f954821043655208410fc98021042f56008410fc580210427e64940109f592500427e63940109f58e500427e62940109f58a500427d6194010ddd0650043744194010ddc86500437421940109f59740042de63d0010b758f400427f65900109f596400433e5490010cf55240042f66190010bd58640043b441900109fd9540042df6350010b718d40042ef6250010bb18940042f76150010bd185400427f65100109f994400427d65100109f194400433e5410010cf55040042f66110010bd58440043b441100109f597300427f658c0109f596300435e538c010d754e30042f6618c010bd586300435f658c010d7996300435d658c010d7196300435f548c010d7952300435d548c010d7152300435f528c010d794a300435d528c010d714a30043d6618c010f5586300435e518c010f5d0630043d4418c010f5c8630043d4218c010b7982300435e508c0109fd95300427f650c0109f994300427d650c0109f194300435e530c010d754c30042f6610c010bd584300435f650c010d7994300435d650c010d7194300435f540c010d7950300435d540c010d7150300435f520c010d7948300435d520c010d714830043d6610c010f5584300435e510c010f5d0430043d4410c010f5c8430043d4210c010b798030043da600c010d794030043db400c010f6100300427d65c8010b798f20042dd63c8010f60c3200427f65880109f596200436e5288010db54a20042f66188010bd58620043e421880109fd9520042bf6448010af19120042df6348010b718d20042f76148010bd185200427f65080109f994200427d65080109f194200436e5208010db54820042f66108010bd58420043e42108010f60c020042de63c4010b758f100437565c4010bd99310042f464c4010f598f10043d563c4010bd98b10042f462c4010f58c310043d430c4010bd58610043765184010f68c210043d83084010be596100437965840109e59610042f96184010de94610043f25184010fcd0610043f04184010fcc8610043f021840109fd9510042bf6444010af19110042df6344010b718d10042ef6244010bb18910043da3044010f60c110042f76544010ddd9510042776544010edd9110042f66444010bd19110043b46444010ad19110043d76344010f518d10043e76244010bd98910042f46244010f918910042e46244010bdd8110043765044010fccc110043d63044010f50c110043f03044010f40c110042fb6544010ded95100427b6544010eed9110043b86444010f6d8d10043d86344010fad8910043e86244010bed8510043f36144010de94510043f25144010fccc510043f03144010
  | 1 => 0x427d6550c109f195430433e5450c10cf551430435e5350c10d754d43042f76150c10bd18543042fb6050c10be181430427f6510c109f994430427d6510c109f194430427e64d48109f593520427e63d48109f58f520427e61d4810dd987520427e60d4810de983520427d6594810dbd4a520427e64948109f592520427e63948109f58e520427f64548109f191520427f63548109f18d520436f62548109fd85520427d6154810dd185520427f60548109f58152042be6414810af59052042de6314810b758c520436d52148109f990520433e64148108f990520427d6414810cf590520423d64148109f98c520435e63148109798c520427d6314810d758c520425d63148109f988520436e62148109f984520437661148109f980520437a60148109fd97420427e65d08109f597420427c65d0810cf953420433d54d0810bd98742042f561d08109fd96420427e65908109f596420427c6590810db94a420436d5290810bd98642042f561908109fd95420427e65508109f595420427c6550810cf951420433d5450810db949420436d5250810bdd8542042f46150810bed8142042f860508109fd94420427e65108109f594420427c6510810b798c42042dd6310810eb508420427f65cc8109f997320427d65cc8109f197320435e53cc810d754f32042f661cc810bd587320427f658c8109f996320427d658c8109f196320436e528c810db54a320427f654c8109f995320427d654c8109f195320435e534c810d754d320436e524c810db54932042f7614c810bd18532042fb604c810be181320427f650c8109f994320427d650c8109f194320427e64944109f592510427e6394410d798e510425e63944109f58e510435d63944109758e510427e62944109f58a510427d65d0410bd597410437565d0410ddd53410437554d0410bd98b41042f560d04109fd96410427d6590410cf952410433d5490410bd98641042fa6090410be582410427f65504109fd94410427d6510410cf950410433d5410410b798c41042dd6310410ed50441042fa6010410be580410437565104109d59441042f66410410ed99041043775410410ed95041043755410410ed55041043355410410f598c41043d56310410bd98841043f26010410bd58041043f160104109f597310435f53cc410d714f310427f658c4109f596310435e538c410d754e31042fa608c410be582310427f654c410d7d4d310435c534c4109fd94310427d650c410d794c310435d530c410be98031042f9600c4109f59721042f565c8410dd59721042f664c8410bd193210437752c8410dd54b21042f560c84109fd96210427d6588410db94a210436d5288410bd98621042fa6088410be582210427f65484109fd94210427d6508410b798c21042dd6308410db948210436d5208410f948
  | 2 => 0x540c110d7d4c304435e530c110d754c304435c530c110dbd48304436c520c110b7994304435e650c11097994304435f540c110e7d50304431f540c110d7950304435d540c110d7150304439c540c110c7150304435f520c110f3d48304434f520c110d7948304435d520c110d714830443cc520c110d314830442de600c110f6980304427e65c8110cfd53204433c54c8110b798f20442dd63c8110d7d4f204435c53c8110dbd4b204436c52c8110bd98720442f561c81109f996204433f5488110cf152204435f5388110d714e204436f5288110db14a204427f65481109f595204427c6548110afd9120442bc6448110cfd51204433c5448110b7d8d20442dc6348110d7d4d204435c5348110dbd49204436c5248110bdd8520442f461481109f994204433f5408110cf150204435f5308110d714c204436f5208110db148204433f54c4110cf15310442de63c4110b758f104435f53c4110d714f104436f52c4110db14b10443da30c4110f60c310443bb54c4110ee15310443da63c4110f658f10443db53c4110f614f10443eb52c4110fa14b104433f5484110cf152104435f5384110d714e104436f5284110db14a10443b75484110dd95210443745484110ed15210443345484110f5d4e10443d45384110f9d4a10443765284110dd14a10443e45284110d914a10443f35084110f58c210443d430841109f98f540427d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d6295010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540437461550109fd81540427d6055010cf55054042de6315010b758c54042ee6215010bb588540427e6415010cf990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427e6015010de980540427e64d4c109f593530427e62d4c109f58b530427e61d4c10dd987530427e60d4c10de983530427d6594c10d7d4e530427e6494c109f592530427e6294c109f58a530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c109fd81530427d6054c10af99053042bd6414c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530427e6214c10db988530426e6214c109f588530436d6214c109b588530427e6114c10dd984530427e6014c10de980530427f65d0c109f997430427d65d0c109f197430433e54d0c10cf553430427f6590c109f996430427d6590c109f196430435e5390c10d754e43042f66190c10bd586430427f6550c109f995430
  | 3 => 0x9109f995324427d654c9109f195324433f544c910cf151324435f534c910d714d324436f524c910db149324427f650c9109f994324427d650c9109f194324433f540c910cf150324435f530c910d714c324436f520c910db14832442f6610c910bd584324427e65d0510cfd53414433c54d0510d7d4f414435c53d0510dbd4b414436c52d0510be98341442f960d05109f996414433f5490510cf152414435f5390510d714e414436f5290510db14a414427c6550510cfd51414433c5450510d7d4d414435c5350510dbd49414436c5250510bed8141442f860505109f994414433f5410510cf15041442de6310510b758c414435f5310510d714c414436f5210510db14841443b541105109f997314433f54cc510cf153314435f53cc510d714f314436f52cc510db14b31442fa60cc510be583314427e658c510cfd52314433c548c510d7d4e314435c538c510dbd4a314436c528c5109f195314433f544c510cf151314435f534c510d714d314436f524c510db14931442fb604c510be181314427e650c510cfd50314433c540c510d7d4c314435c530c510dbd48314436c520c510f54c4314427e65c8510cfd53214433c54c8510d7d4f214435c53c8510dbd4b214436c52c8510be98321442f960c85109f996214433f5488510cf152214435f5388510d714e214436f5288510db14a214427c6548510cfd51214433c5448510d7d4d214435c5348510dbd49214436c5248510bed8121442f860485109f994214433f5408510cf15021442de6308510b758c214435f5308510d714c214436f5208510db14821443e521085109f997404433f54d0110cf15340442de63d0110b758f404435f53d0110d714f404436f52d0110db14b40442f661d0110bd587404427e6590110cfd52404433c5490110d7d4e404435c5390110dbd4a404436c52901109fd95404427d65501109f195404433f5450110cf15140442df6350110b718d404435f5350110d714d40442ef6250110bb189404436f5250110db14940442f76150110bd185404427e6510110cfd50404433c5410110d7d4c404435c5310110dbd48404436c52101109f997304433f54cc110cf153304435f53cc110d714f304436f52cc110db14b30442f661cc110bd587304427e658c110cfd52304433c548c110d7d4e304435e538c110d754e304435c538c110dbd4a304436c528c110b7996304435e658c11097996304435f548c110e7d52304431f548c110d7952304435d548c110d7152304439c548c110c7152304435f528c110f3d4a304434f528c110d794a304435d528c110d714a30443cc528c110d314a30442de608c1109fd95304427d654c1109f195304433f544c110cf151304435f534c110d714d304436f524c110db14930442f7614c110bd185304427e650c110cfd50304433c
  | 4 => 0x7d4c434435c5310d10bd98443442f56110d10cfd53524433c54d4910d7d4f524435c53d49109f993524427d64d49109f98f524427d63d4910dbd5352443af54d4910cbd53524436e54d4910db553524436c54d4910eb153524432c54d4910dbd4f52443cf53d4910d3d4f524436e53d4910db54f524436c53d4910f314f524434c53d4910dbd93524436e64d4910db593524436c64d4910dbd8f524436e63d4910db58f524436c63d4910dbd0f524436e43d4910db50f524436c43d4910dbd87524436d61d4910dbd83524436d60d4910af99252442bd6494910cfd52524433c5494910b798e52442dd6394910d7d4e524435c5394910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e6394910d798e524425e63949109f58e524435d63949109758e524427e62949109b98a524427d6194910dd586524427d6094910de58252442bf6454910af191524433f5454910cf15152442df6354910b718d524435f5354910d714d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109dd85524427f6054910ded81524427e6514910cfd50524433c5414910d7d4c524435c5314910db548524427e64149109f590524427e63149109f58c524436e62149109f984524427c61149109f980524427c6014910bb994524436e65149109b994524436f5414910ebd50524432f5414910db950524436d5414910db15052443ac5414910cb150524436f5314910f3d4c524434f5314910db94c524436d5314910db14c52443cc5314910d314c524436f6414910db990524436d6414910db190524436f6314910db98c524436d6314910db18c524436f4314910db90c524436d4314910db10c524436f6114910db584524436f6014910db580524436d10149109fd97424427e65d09109f597424427c65d0910cfd53424433c54d0910d7d4f424435c53d0910dbd4b424436c52d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910d7d4e424435c5390910dbd4a424436c52909109fd95424427e65509109f595424427c6550910cfd51424433c5450910d7d4d424435c5350910dbd49424436c52509109fd94424427e65109109f594424427c6510910cfd50424433c5410910b798c42442dd6310910d7d4c424435c5310910dbd48424436c5210910eb50842442f66110910bd58442442fa6010910be580424427f65cc9109f997324427d65cc9109f197324433f54cc910cf153324435f53cc910d714f324436f52cc910db14b324427f658c9109f996324427d658c9109f196324433f548c910cf152324435f538c910d714e324436f528c910db14a324427f654c
  | 5 => 0x544433f5495110b798e54442dd6395110bb98a54442ed62951109f992544423e64951109f98e544435e63951109798e544427d6395110d758e544425d63951109f98a544436e62951109b98a544427d6295110db58a544426d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f63551109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427761551109fd81544437b60551109f994544433d5415110cf990544427e63151109f58c544427e62151109f588544427e61151109f184544427e60151109f18054442be6515110cf994544423e6515110cfd8c544433e6315110cf58c544433c6315110cfd88544433e6215110cf588544433c6215110cfd84544433d6115110cfd80544433d6015110cf440544433f54d4d10cf153534427e64d4d109f593534427e62d4d109f58b534435f54d4d10e7d53534431f54d4d10d7953534435d54d4d10d7153534439c54d4d10c7153534435f64d4d10d7993534435d64d4d10d7193534435f62d4d10d798b534435d62d4d10d718b534435f61d4d10d7587534435f60d4d10d758353442be6494d10af592534433f5494d10cf152534435f5394d10bb98a53442ed6294d109f992534433e6494d108f992534427d6494d10cf592534423d6494d109f98e534425e6394d109f98a534436e6294d109b98a534427d6294d10db58a534426d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10cfd51534433c5454d10bbd8953442ec6254d109fd91534433f6454d108fd91534427c6454d10cf191534423c6454d10d7d8d534427f6254d10dbd89534426f6254d109f189534436c6254d109b189534427f6154d10ddd85534427f6054d10ded81534427e6514d10cfd50534433c5414d10d754c534427e6414d109f590534435e6314d109f988534427d6214d109f984534427c6114d109f980534427c6014d10b7994534435e6514d1097994534435f5414d10e7d50534431f5414d10d7950534435d5414d10d7150534439c5414d10c7150534435f6414d10d7990534435d6414d10d7190534435f6214d10d7988534435d6214d10d7188534435f6114d10d7584534435f6014d1097980534435d6014d1097180534435d1014d109fd97434427e65d0d109f597434427c65d0d10cfd53434433c54d0d10d7d4f434435c53d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d10d7d4e434435c5390d109fd95434427e6550d109f595434427c6550d10cfd51434433c5450d10d7d4d434435c5350d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10d
  | 6 => 0x35c53cca10bd98732842f561cca109fd96328427e658ca109f596328427c658ca109fd95328427e654ca109f595328427c654ca10d7d4d328435c534ca10bdd8532842f4614ca109fd94328427e650ca109f594328427c650ca10cf953418433d54d0610be98341842f960d0610dd597418437754d0610ed953418437554d0610ed55341842f662d0610fc98341842f560d0610fc583418433f5490610cf152418433e5450610cf55141842fb6050610be181418433f5410610cf15041842de6310610b758c41843b54110610bd59441843756510610ed99041843775410610edd5041843375410610dd55041843b45410610f598c41843d56310610bd98841842f56010610d794f318435d53cc610be98331842f960cc610d7d4e318435c538c610d794d318435d534c610bed8131842f8604c610d7d4c318435c530c610db94b218436d52c8610be98321842f960c8610dd59721842f664c8610bd193218437752c8610f994b218437552c8610f954b21843f260c8610bd58321843f160c8610dbd4a218436c5288610db949218436d5248610bed8121842f86048610b798c21842dd6308610dbd48218436c5208610f948421842f56508610dd59421842f66408610bd19021843d66308610f558c21843e66208610ddd4821843e75208610d9d4821843755208610f914821842f56008610b798f40842dd63d0210cf952408433d5490210bd98640842f56190210ed10640842df6350210b718d40842ef6250210bb18940842f76150210bd185408433e5410210cf55040842f66110210bd58440843b44110210d794e308435d538c210bd98630842f5618c210d7996308435d658c210d7d52308435e548c210d7552308435c548c210d7d4a308435e528c210d754a308435c528c210f598630843d5618c210f5d0630843d4418c210f5c8630843d4218c210d794c308435d530c210bd98430842f5610c210d7994308435d650c210d7d50308435e540c210d7550308435c540c210d7d48308435e520c210d7548308435c520c210f598430843d5610c210f5d0430843d4410c210f5c8430843d4210c210f698030842de63c8210b758f208436e5288210db54a20842f66188210bd58620843e42188210afd9120842bc6448210b7d8d20842dc6348210bdd8520842f46148210db948208436d5208210bd98420842f56108210f908420842de63c4210b758f10843da30c4210f60c310842f565c4210dd59710842f664c4210bd19310843d663c4210f558f10842f662c4210bd18b10843d630c4210f50c310842f965c4210de59710843da63c4210f658f108427e63d51109f58f544427e62d51109f58b544433f63d5110cf98f544433d63d5110cf18f544433f62d5110cf98b544433d62d5110cf18b544433f61d5110cf587544433f60d5110cf583
  | 7 => 0x250310bdd8540c42f46150310cfd5040c433c5410310d794c40c435d5310310d794f30c435d53cc310bd98730c42f561cc310d7d4e30c435e538c310d754e30c435c538c310b759630c435d658c310d7d5230c435e548c310d755230c435c548c310d7d4a30c435e528c310d754a30c435c528c310d794d30c435d534c310bdd8530c42f4614c310d7d4c30c435e530c310d754c30c435c530c310b759430c435d650c310d7d5030c435e540c310d755030c435c540c310d7d4830c435e520c310d754830c435c520c310f698030c43db400c310f610030c42de63c8310b758f20c435e53c8310d754f20c436e52c8310db54b20c42f661c8310bd58720c43d830c8310d794e20c435d5388310dbd4a20c436c5288310afd9120c42bc6448310b7d8d20c42dc6348310d794d20c435d5348310db94920c436d5248310bdd8520c42f46148310d794c20c435d5308310dbd4820c436c5208310f60c020c427e63d52109f58f548427e62d52109f58b548437561d5210de983548433f5495210b798e54842dd63952109f98e548435e63952109798e548427d6395210d758e548425d63952109f98a548427d6295210cfd91548427f63552109f18d548427f62552109f18954843776155210cf550548433e64152109f98c548427d63152109f988548427d6215210dd584548437a60152109f993538427d64d4e109f98b538427d62d4e10dd587538437a60d4e10d7d4e538427e6494e109f592538427e6294e109f58a538427f6454e109f191538435f6354e109fd89538427c6254e10d754c538427e6414e109f590538435e6314e109f988538427d6214e10dd584538437a6014e109fd97438427e65d0e109f597438427c65d0e109fd96438427e6590e109f596438427c6590e10d7d4e438435c5390e10bd98643842f56190e109fd95438427e6550e109f595438427c6550e10d7d4d438435c5350e10bdd8543842f46150e109fd94438427e6510e109f594438427c6510e109f993528427d64d4a109f98f528427d63d4a10dd587528437a60d4a10b798e52842dd6394a10dbd4a528427e6494a109f592528427e6394a10d798e528425e6394a109f58e528435d6394a109758e528427f6454a109f191528427f6354a109f18d528436f6254a10ddd85528436d5214a109f990528427d6414a109f98c528427d6314a10db98852843756114a10de980528427f65d0a109f997428427d65d0a109f19742842f661d0a10bd587428427f6590a109f996428427d6590a109f19642842f66190a10bd586428427f6550a109f995428427d6550a109f19542842f76150a10bd185428427f6510a109f994428427d6510a109f19442842de6310a10b758c42843ad4210a10be98042842f96010a109fd97328427e65cca109f597328427c65cca10d7d4f3284
  | 8 => 0x109fd9743c427e65d0f109f59743c427c65d0f10d794f43c435d53d0f109fd9643c427e6590f109f59643c427c6590f10d794e43c435d5390f109fd9543c427e6550f109f59543c427c6550f10d794d43c435d5350f10bed8143c42f86050f109fd9443c427e6510f109f59443c427c6510f10d794c43c435d5310f10bd98443c42f56110f10af99352c42bd64d4b10b798f52c42dd63d4b10d794f52c435d53d4b109f99352c433e64d4b108f99352c427d64d4b10cf59352c423d64d4b109f98f52c435e63d4b109798f52c427d63d4b10d758f52c425d63d4b10dd98752c437960d4b10d794e52c435d5394b10dbd4a52c427e6494b109f59252c427e6394b109f58e52c435e5354b10d754d52c427f6454b109f19152c427f6354b109f18d52c436f6254b10b798c52c42dd6314b10d794c52c435d5314b10db54852c427e6414b109f59052c427e6314b10d798c52c425e6314b109f58c52c435d6314b109758c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10d794f42c435d53d0b10db94b42c436d52d0b109fd9642c427e6590b109f59642c427c6590b10cf95242c433d5490b10d794e42c435d5390b109fd9542c427e6550b109f59542c427c6550b10d794d42c435d5350b10bed8142c42f86050b109fd9442c427e6510b109f59442c427c6510b10cf95042c433d5410b10b798c42c42dd6310b10d794c42c435d5310b10db94842c436d5210b10eb50842c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c435e53ccb10d754f32c427f658cb109f99632c427d658cb109f19632c435e538cb10d754e32c427f654cb109f99532c427d654cb109f19532c435e534cb10d754d32c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c435e530cb10d754c32c42f6610cb10bd58432c435e53d0710d754f41c433e5490710cf55241c435e5390710d754e41c42fa6090710be58241c435e5350710d754d41c433e5410710cf55041c42de6310710b758c41c435e5310710d754c41c43b54110710be98041c42f96010710d794f31c435d53cc710d794e31c435d538c710be98231c42f9608c710d794d31c435d534c710d794c31c435d530c710f54c431c42fa600c710be58031c435e53c8710d754f21c435e5388710d754e21c436e5288710db54a21c42fa6088710be58221c435e5348710d754d21c42de6308710b758c21c435e5308710d754c21c436e5208710db54821c43e52108710be98021c42f96008710cf95340c433d54d0310b798f40c42dd63d0310d794f40c435d53d0310bd98740c42f561d0310cfd5240c433c5490310d794e40c435d5390310cf95140c433d5450310b7d8d40c42dc6350310d794d40c435d5350310bbd8940c42ec6
  | 9 => 0x98a30082ed628c020d7d96300835e658c020d7596300835c658c020d7d52300835e548c020d7552300835c548c020f398a30083cd628c020d794a30083cf428c020f310a300835e518c020d754630083ce218c020f308630082de608c020d7942300827f654c0209fd94300827e650c0209f594300827c650c020d794c300835d530c020bb98830082ed620c020d7d94300835e650c020d7594300835c650c020d7d50300835e540c020d7550300835c540c020f398830083cd620c020d794830083cf420c020f3108300835e510c020d754430083ce210c020f308430082de600c020f6980300835e500c020f6d0030083d8400c020b798f20082dd63c8020bb99320082ec64c8020f398f20083cd63c8020bb98720083ce30c8020f30c320082ed6288020db94a20083da3088020f60c220082f96288020de94a20083ea5288020fad0a20083e84288020fa88620083e821880209fd9520082bf6448020af19120082df6348020b718d20082f76148020bd18520083da3048020f60c120082ef6548020dbd95200826f6548020ebd9120082ee6448020bb19120083ac6448020ab19120083cf6348020f318d20083e76148020bb18520083e46148020b918520082ef6048020db94120083eb3048020f38c120083cc3048020fa0c120083c83048020bed95200837b65480209ed9520083bb6448020ee19120083db6348020f618d20082fb6248020fad89200837a5248020fa94920083eb3248020fa0c920083f36148020fc18520082de63d5310b758f54c42ee62d5310bb58b54c427e63d5310d798f54c425e63d53109f58f54c435d63d53109758f54c427e62d5310db98b54c426e62d53109f58b54c436d62d53109b58b54c437661d5310de58354c433f54953109f98e54c427d63953109f98a54c427d6295310cfd9154c427f63553109f18d54c427f62553109f18954c433d5415310b798c54c42dd6315310cf99054c427e6315310d798c54c425e63153109f58c54c435d63153109758c54c427e62153109f58854c43766115310de58054c427e64d4f109f59353c427e62d4f109f58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f10d7d5253c435e5494f10d755253c435c5494f10d7d9253c435e6494f10d759253c435c6494f10d7d8a53c435e6294f10d758a53c435c6294f10d798653c435c6194f10d7d8253c435d6094f109fd9153c427c6454f10d7d8d53c427f6254f109f18953c435f6554f10d7d5153c435e5454f10d755153c435c5454f10d7d9153c435e6454f10d759153c435c6454f10d7d8953c435e6254f10d758953c435c6254f10d798553c435c6154f10d7d8153c435d6054f10d754c53c427e6414f109f59053c435e6314f109f98853c427d6214f10dd98453c43796014f
  | 10 => 0x3082ec6250c20bed8143082f86050c209fd94430827e6510c209f594430827c6510c209f992520827d64948209f98e520835e63948209798e520827d6394820d758e520825d63948209f59742082ed65d0820db597420836f54d0820db55342082ee61d0820bb583420827f65908209f596420833e5490820cf55242082ee6290820be98242082f960908209fd95420827f65108209f594420833e5410820cf55042082de6310820b758c42083ad4210820be98042082f96010820db594420826d6510820bb99042083ae6410820dbd5042083ae5410820db55042083ad5410820cb55042083ce6310820f358c42082ee6110820fa98042082ed6010820fa580420827d65cc820d7d4f320835c53cc8209fd96320827d658c820d794e320835d538c820be98232082f9608c8209fd95320835f534c820d714d320827f650c8209f594320835e530c820d754c32082fa600c820be580320837751944209f992510827d64944209f98e510827d63944209fd91510827c64544209fd8d510827c6354420af99051082bd6414420b798c51082dd6314420dd544510827f65d04209f997410827d65d0420cf953410833d54d0420bb98b41082ed62d04209fd96410827e65904209f59641082ee6290420bb58a41083765190420dd546410827f65504209f595410827c6550420cf951410833d5450420bbd8941082ec6250420dd94541083755150420bed8141082f860504209fd94410827e65104209f59441082de6310420b758c41083b541104209fd97310827e65cc4209f597310835e53cc420d754f31082ee62cc420bb58b310827f658c4209f996310827d658c420dd9463108375518c4209fd95310827d654c4209f195310835e534c420d754d31082ef624c420bb1893108376514c420dd54531082fb604c420be181310827f650c4209f994310827d650c420dd947210837551c8420be98321082f960c84209f59621082ed6588420db59621082ee6488420bb19221082ee6188420db54621082ed60884209fd9521082de6308420b758c21083765108420dd54421083e52108420be98021082f96008420bb99021082ec6408420f398c21083cd6308420bb98421083e66108420f9944210836d5108420f954421083655108420fa98021082ed6008420fa580210827e64940209f592500827e63940209f58e500836f4294020db10a500836e2194020db086500827d65d0020b798f40082dd63d00209fd96400827d6590020cf952400833d5490020bb98a40082ed6290020eb10a400827f6550020b7d8d40082dc6350020bbd8940082ec6250020bdd8540082f461500209fd94400827e65100209f594400827c6510020cf950400833d5410020bb98840082ed6210020eb108400827d65cc0209fd96300827d658c020d794e300835d538c020bb
  | 11 => 0x7e658c120cfd52304833c548c120d7d4e304835e538c120d754e304835c538c120ddd463048374518c120b7996304835e658c12097996304835f548c120e7d52304831f548c120d7952304835d548c120d7152304839c548c120c7152304835f518c120f5d463048357518c120d714630483d4518c120d514630482de608c1209fd95304827d654c1209f195304833f544c120cf151304835f534c120d714d30482ef624c120bb1893048377514c120dd145304827e650c120cfd50304833c540c120d7d4c304835e530c120d754c304835c530c120ddd443048374510c120b7994304835e650c12097994304835f540c120e7d50304831f540c120d7950304835d540c120d7150304839c540c120c7150304835f510c120f5d443048357510c120d714430483d4510c120d514430482de600c120f6980304833f54c8120cf15320482de63c8120b758f204835f53c8120d714f204837751c8120dd14720483da30c8120f60c320483bb54c8120ee15320483da63c8120f658f20483db53c8120f614f20483f351c8120fc147204833f5488120cf152204835f5388120d714e20483775188120dd14620483af5488120db952204836c5488120eb152204832c5488120f3d4e20483cc5388120f9d46204836c5188120f914620483645188120fad4220483ce3088120f30c2204827e63d50209f58f540827e62d5020db98b540827e61d50209f587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540833f64550209fd8d540827c63550209fd89540827d6255020db189540827f61550209f185540833d5415020b798c54082dd6315020bd98454082f561150209f990540833e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f988540836e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a60150209f993530827d64d4c209f98b530836e62d4c209f987530827d61d4c209f983530837a60d4c209f596530835f5394c209f992530827d6494c209f986530827d6194c209fd91530827c6454c20d7d8d530827f6254c209f589530827f6154c209f18553082be6414c20af590530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209f988530836e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c209fd96430827e6590c209f596430827c6590c20d794e430835d5390c20bb98a43082ed6290c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c20bbd894
  | 12 => 0x54520b718d514835f5354520d714d514833f5414520cf150514835f5314520d714c514837551145209f990514827d64145209f98c514827d6314520bd99451483766514520ddd5051483b75414520cdd5051483765414520dd55051483745414520ed15051483345414520ddd4c51483d75314520d5d4c51483765314520dd54c51483745314520f514c51483545314520ddd9051483766414520dd59051483746414520ddd8c51483766314520dd58c51483746314520ddd0c51483764314520dd50c51483744314520ddd8851483774214520dd90851483754214520dd10851483773214520dd8c851483753214520dd0c851483776014520dd580514837520145209f997414827d65d05209f197414833f54d0520cf153414835f53d0520d714f414837751d0520dd147414827e65905209f596414827c6590520cfd52414833c5490520d7d4e414835c5390520ddd46414837451905209fd95414827e65505209f195414833f5450520cf151414835f5350520d714d41483775150520dd145414827e65105209f594414827c6510520cfd50414833c5410520b798c41482dd6310520d7d4c414835c5310520bb98841482ed6210520ddd4441483745110520ed50441482fa6010520be580414827e65cc5209f597314827c65cc520cfd53314833c54cc520d7d4f314835c53cc520ddd47314837451cc5209f996314827d658c5209f196314833f548c520cf152314835f538c520d714e3148377518c520dd146314827f654c5209f995314827c654c520cfd51314833c544c520d7d4d314835c534c520ddd453148374514c5209f994314827d650c5209f194314833f540c520cf150314835f530c520d714c31482ee620c520bb5883148377510c520dd144314827e65c8520cfd53214833c54c8520d7d4f214835c53c8520dd147214833f5488520cf152214835f5388520d714e21483775188520dd14621482fa6088520be582214833f5448520cf151214835f5348520d714d21483775148520dd14521482fb6048520be181214827e6508520cfd50214833c5408520b798c21482dd6308520d7d4c214835c5308520ddd4421483e521085209f997404833f54d0120cf15340482de63d0120b758f404835f53d0120d714f40482ee62d0120bb58b404837751d0120dd147404827e6590120cfd52404833c5490120d7d4e404835c5390120ddd46404837451901209fd95404827d65501209f195404833f5450120cf15140482df6350120b718d404835f5350120d714d40482ef6250120bb18940482f76150120bd18540483775150120dd145404827e6510120cfd50404833c5410120d7d4c404835c5310120ddd44404837451101209f997304833f54cc120cf153304835f53cc120d714f30482ee62cc120bb58b304837751cc120dd14730482
  | 13 => 0x9798e534827d6294d20db58a534827e6194d20dd98653482766194d209f58653483756194d209d586534827d6094d20de58253482bf6454d20af191534833f5454d20cf15153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534835f6354d209fd89534836f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209f994534833f5414d20cf150534835d5314d209f990534827d6414d20d798c534827e6214d209f188534827e6114d209f58453482de6514d20d7994534825e6514d20d7d50534839f5414d20c7d50534835e5414d20d7550534835c5414d20e7150534831c5414d20d7d90534835e6414d20d7590534835c6414d20d7d88534835d6214d20d7d84534835e6114d20d7584534835c6114d20d7d80534835d6014d20d7480534827f65d0d209f997434827d65d0d209f197434833f54d0d20cf153434835f53d0d20d714f434827f6590d209f996434827d6590d209f196434833f5490d20cf152434835f5390d20d714e434827f6550d209f995434827d6550d209f195434833f5450d20cf151434835f5350d20d714d434827f6510d209f994434827d6510d209f194434833f5410d20cf150434835f5310d20d714c43482ee6210d20bb588434827e65d0920cfd53424833c54d0920d7d4f424835c53d0920be98342482f960d09209f996424833f5490920cf152424835f5390920d714e424827c6550920cfd51424833c5450920d7d4d424835c5350920bed8142482f860509209f994424833f5410920cf15042482de6310920b758c424835f5310920d714c42483ad42109209f997324833f54cc920cf153324835f53cc920d714f32482fa60cc920be583324827e658c920cfd52324833c548c920d7d4e324835c538c9209f195324833f544c920cf151324835f534c920d714d32482fb604c920be181324827e650c920cfd50324833c540c920d7d4c324835c530c920f34c8324833f54d4520cf153514835f53d4520d714f514827e64d45209f593514827e63d45209f58f514837754d4520edd53514833754d4520dd953514837554d4520dd15351483b454d4520cd153514837753d4520f5d4f514835753d4520dd94f514837553d4520dd14f51483d453d4520d514f514837764d4520dd993514837564d4520dd193514837763d4520dd98f514837563d4520dd18f514837743d4520dd90f514837543d4520dd10f514837762d4520ddd0b514837642d4520dd50b514837442d4520ddccb514837632d4520dd4cb514837432d4520ddd83514837560d4520af99251482bd6494520cfd52514833c5494520b798e51482dd6394520d7d4e514835c5394520ddd4651482bf6454520af191514833f5454520cf15151482df63
  | 14 => 0x4521883755148620bed8121882f86048620b798c21882dd6308620f948421882ed6508620db59421882ee6408620bb19021883ce6308620f358c21883e66108620f9d44218836d5108620f914421882ed6008620b798f40882dd63d0220cf952408833d5490220bb98a40882ed6290220eb10a40882df6350220b718d40882ef6250220bb18940882f76150220bd185408833e5410220cf55040882ee6210220bb58840883ac4210220d794e308835d538c220bb98a30882ed628c220d7996308835d658c220d7d52308835e548c220d7552308835c548c220f398a30883cd628c220f3d0a30883cc428c220d7946308835d518c220f388630883cc218c220d794c308835d530c220bb98830882ed620c220d7994308835d650c220d7d50308835e540c220d7550308835c540c220f398830883cd620c220f3d0830883cc420c220d7944308835d510c220f388430883cc210c220f698030882de63c8220b758f20883da30c8220f60c320882ed65c8220db59720882ee64c8220bb19320883ce63c8220f358f20882ee61c8220f38c320883cc30c8220be597208837965c8220f698f20883d963c82209f98f544827d63d51209f987544827d61d5120cfd8f544833e63d5120cf58f544833c63d5120cfd8b544833d62d5120cfd87544833e61d5120cf587544833c61d5120cfd83544833d60d5120cfd5254482de6395120b758e54482f66195120bd586544827e64951208f992544827e6395120d798e544825e63951209f58e544835d63951209758e544827d6295120db58a544827e6195120dd986544827661951209f586544837561951209d586544827d6095120de58254482df6355120b718d54482f76155120bd185544833f64551209fd8d544835f635512097d8d544827c6355120d718d544825c63551209fd89544836f62551209bd89544827f6155120ddd85544827761551209f185544837461551209d185544827f6055120ded81544827e6515120cf550544833e64151209f98c544827d63151209f988544827c62151209f984544827d6115120af994544833e65151208f994544833f6315120cf98c544833d6315120cf18c544833f6215120cf588544833f6115120cf984544833d6115120cf184544833f6015120cf580544833d2015120cfd53534833c54d4d209f993534827d64d4d209f987534827d61d4d20d7d53534839f54d4d20c7d53534835e54d4d20d7553534835c54d4d20e7153534831c54d4d20d7d93534835e64d4d20d7593534835c64d4d20d7d8b534835d62d4d20d7d87534835e61d4d20d7587534835c61d4d20d7d83534835d60d4d20af99253482bd6494d20cfd52534833c5494d20d7d4e53482f66194d20bd586534827e6494d20cf992534823e6494d209f592534833d6494d208f592534827e6394d2
  | 15 => 0xc82ef624c320bb18930c835f530c320d794c30c835d530c320d714c30c82dd650c320d759430c835f540c320d795030c835d540c320d715030c835e510c320d754430c83da600c320f6d0030c83d8400c3209f98f548827d63d5220db58b548827e61d52209f587548837a60d5220cfd5254882de6395220b758e548827e6395220d798e548825e63952209f58e548835d63952209758e548827e61952209f586548833f64552209fd8d548827c6355220dbd89548827f61552209f185548833d5415220cf990548827e63152209f58c548836d62152209f984548827d6115220de980548827e64d4e209f593538836d62d4e209f987538827d61d4e20de983538835f5394e209f992538827d6494e209f986538827d6194e209fd91538827c6454e20d7d8d538827f6154e209f185538835d5314e209f990538827d6414e20d798c538836d6214e209f984538827d6114e20de980538827f65d0e209f997438827d65d0e209f197438827f6590e209f996438827d6590e209f196438835f5390e20d714e43882ee6290e20bb58a438827f6550e209f995438827d6550e209f195438835f5350e20d714d43882ef6250e20bb189438827f6510e209f994438827d6510e209f194438833e54d0a20cf55342882fa60d0a20be583428836d65d0a20dbd5342883ae54d0a20db55342883ad54d0a20bb98742883ea60d0a20bb58342883e960d0a20cfd52428833c5490a20cf951428833d5450a20bed8142882f86050a20cfd50428833c5410a20b798c42882dd6310a20eb50842882ed6510a20db59442883ae6410a20dbd5042883af5410a20cbd50428836d5410a20eb15042883ce6310a20f358c42882ee6110a20bb580428835e53cca20d754f32882fa60cca20be583328835f538ca20d714e328835e534ca20d754d32882fb604ca20be181328835f530ca20d714c32882de6394620b758e518837751946209f992518827d64946209f98e518835e63946209798e518827d6394620d758e518825d63946209fd91518827c64546209fd8d518827c6354620dd544518827f65d06209f997418827d65d0620bb98b41882ed62d06209fd96418827e65906209f59641882ee6290620bb58a418827f65506209f595418827c6550620bbd8941882ec62506209fd94418827e65106209f59441882de6310620b758c41883b54110620be98041882f960106209fd97318827e65cc6209f597318835f53cc620d714f31882ee62cc620bb58b318827f658c6209f996318827d658c6209fd95318827d654c6209f195318835f534c620d714d31882ef624c620bb189318827f650c6209f994318827d650c620dd94621883755188620be98221882f96088620bb99221882ec6488620f9946218836d5188620f954621883ea6088620bb58221883e96088620dd9
  | 16 => 0xf6054f20d758153c835d5314f209f99053c827d6414f20d798c53c836e6214f209f98453c827d6114f20de58053c827f65d0f209f99743c827d65d0f209f19743c835e53d0f20d754f43c827f6590f209f99643c827d6590f209f19643c835e5390f20d754e43c827f6550f209f99543c827d6550f209f19543c835e5350f20d754d43c82fb6050f20be18143c827f6510f209f99443c827d6510f209f19443c835e5310f20d754c43c82ee6210f20bb58843c835e53d0b20d754f42c833e5490b20cf55242c835e5390b20d754e42c82fa6090b20be58242c835e5350b20d754d42c833e5410b20cf55042c82de6310b20b758c42c835e5310b20d754c42c83ad4210b20be98042c82f96010b20d794f32c835d53ccb20d794e32c835d538cb20be98232c82f9608cb20d794d32c835d534cb20d794c32c835d530cb20f34c832c82fa600cb20be58032c82be64d4720af59351c82de63d4720b758f51c835e53d4720d754f51c835e5394720d754e51c837751947209f99251c827d64947209f98e51c827d6394720d794d51c835d53547209fd9151c827c64547209fd8d51c827c6354720b798c51c82dd6314720d794c51c835d5314720dd54451c827f65d07209f99741c827d65d0720d794f41c835d53d0720dd94741c837551d07209fd9641c827e65907209f59641c833e5490720cf55241c835e5390720d754e41c827f65507209f59541c827c6550720d794d41c835d5350720bed8141c82f860507209fd9441c827e65107209f59441c833e5410720cf55041c82de6310720b758c41c835e5310720d754c41c82ee6210720bb58841c83765110720dd54441c83b541107209fd9731c827e65cc7209f59731c835e53cc720d754f31c827f658c7209f99631c827d658c720d794e31c835d538c7209fd9531c827d654c7209f19531c835e534c720d754d31c82fb604c720be18131c827f650c7209f99431c827d650c720d794c31c835d530c720bb98831c82ed620c720d794f21c835d53c8720dd94721c837551c8720be98321c82f960c8720d794e21c835d5388720d794d21c835d5348720b798c21c82dd6308720d794c21c835d5308720dd94421c83755108720f948421c82fa6008720be58021c833e54d0320cf55340c82de63d0320b758f40c835e53d0320d754f40c82ee62d0320bb58b40c833f5490320cf15240c835e5390320d754e40c833e5450320cf55140c82df6350320b718d40c835e5350320d754d40c82ef6250320bb18940c82f76150320bd18540c833f5410320cf15040c835e5310320d754c40c835e53cc320d754f30c82ee62cc320bb58b30c835f538c320d794e30c835d538c320d714e30c82dd658c320d759630c835f548c320d795230c835d548c320d715230c835e518c320d754630c835e534c320d754d30
  | 17 => 0x4030d7992500c35d6494030d7192500c35e6294030d758a500c35f4294030d790a500c35d4294030d710a500c35e6194030d7586500c35f4194030d7906500c35d4194030d7106500c35f2194030d7886500c35d2194030d7086500c35a6094030f6596500c3db6494030f6992500c3d96494030f6192500c3db5494030f6952500c3d95494030f6152500c3db6294030f698a500c3d96294030f618a500c3db5294030f694a500c3d95294030f614a500c3db4294030f690a500c3d94294030f610a500c3db6194030f6986500c3d96194030f6186500c3db5194030f6946500c3d95194030f6146500c3db4194030f6906500c3d94194030f6106500c3db2194030f6886500c3d92194030f6086500c2dd65d0030d7597400c25d65d0030b798b400c2dd62d0030b7987400c2dd61d0030d7943400c3da50d0030b7d96400c2dd6590030b7592400c39e5490030e7552400c2de6290030b758a400c39e4290030e710a400c2de6190030b7586400c39e4190030e7106400c2de6090030d7942400c3da5090030e7d02400c3db4090030b7d95400c35f655003097d95400c2df6250030f3d89400c2cf6250030b7189400c3cc6250030b3189400c2df6150030f5d85400c2d76150030b7185400c3d46150030b5185400c35e5050030f6941400c3db4050030e7901400c2df6510030b7994400c2dd6510030b7194400c2de6410030e7950400c39d5410030b7988400c2dd6210030e7908400c39c4210030b7984400c2dd6110030e7904400c39c4110030b7980400c35e5010030f6940400c39f4010030f6900400c39d4010030f6500400c3994010030b798f54c82dd63d5320bd98754c82f561d53209f98f54c835e63d53209798f54c827d63d5320d758f54c825d63d5320db98b54c827e61d5320dd98754c827661d53209f58754c837561d53209d58754c837960d5320cfd5254c827e63953209f58e54c827e61953209f58654c833f64553209fd8d54c827c63553209fd8554c827c6155320cf55054c82de6315320b758c54c833e64153209f98c54c835e63153209798c54c827d6315320d758c54c825d6315320db98854c827e61153209f58454c837960153209f99353c827d64d4f20db98b53c827e61d4f209f58753c837960d4f20d7d4e53c827e6494f209f59253c827e6194f209f58653c835f5494f20d795253c835d5494f20d715253c835f6494f20d799253c835d6494f20d719253c835e6294f20d718a53c835f6194f20d798653c835d6194f20d718653c835f6094f20d758253c827f6454f209f19153c835f6354f209fd8553c827c6154f20d7d9553c835f5454f20d795153c835d5454f20d715153c835f6454f20d799153c835d6454f20d719153c835e6254f20d718953c835f6154f20d798553c835d6154f20d718553c835
  | 18 => 0xb7181420c3d86050830b6181420c2df6510830b7994420c35e651083097994420c2dd6510830d7594420c25d6510830b7194420c2de6410830b7988420c39f4210830f3908420c39d4210830f3508420c38d4210830b7984420c2dd6110830b7980420c2dd6010830b7993510c2dd64d4430d7d53510c35d54d4430b798b510c2dd62d4430d7d4b510c35d52d4430b7983510c3da60d4430b6983510c2dd6594430b7992510c2dd6494430b798a510c2dd6294430d7d46510c3d75194430b7d91510c2dc6454430d7d51510c35d5454430b7d89510c2dc6254430d7d49510c35d5254430f5d45510c35e5154430b7990510c39e6414430a7990510c2dd6414430e7590510c29d6414430b7988510c3ce6214430b3988510c2dd6214430f3588510c2cd6214430b7984510c35f5114430f5944510c35d5114430f5544510c3555114430b7980510c3da6014430b6980510c2df65d0430b7997410c2dd65d0430b7197410c39e54d0430e7553410c2de62d0430b758b410c2de60d0430b7583410c2df6590430b7996410c2dd6590430b7196410c2dd6490430b798a410c2dd6290430b7986410c3d65190430f5546410c39f4190430f5d06410c2de6090430b7582410c2df6550430b7995410c2dd6550430b7195410c39e5450430e7551410c2df6250430b7189410c3d65150430f5545410c3d74150430e7905410c2df6050430f6d81410c2db6050430b7181410c3d86050430b6181410c2df6510430b7994410c35e651043097994410c2dd6510430d7594410c25d6510430b7194410c2de6410430b7988410c2dd6210430b7984410c39f4110430f5904410c39d4110430f5504410c3954110430b7980410c2dd6010430b7d97210c2de65c8430b7597210c2dc65c8430b7d93210c2de64c8430b7593210c2dc64c8430f394b210c3cd52c8430b7983210c2dd60c8430b7d96210c2de6588430b7596210c2dc6588430b7d92210c2de6488430b7592210c2dc6488430b758a210c2de6188430f5946210c3d55188430f3c86210c3d72188430b7982210c2dd6088430b7d95210c2de6548430b7595210c2dc6548430b7d91210c2de6448430b7591210c2dc6448430f3949210c3cd5248430f5945210c3d55148430f5c85210c3ce2148430b7d81210c3db6048430b6d81210c2dc6048430f6181210c2d86048430b7d94210c2de6508430d7994210c25e6508430b7594210c35d650843097594210c2dc6508430b7d90210c2de6408430b7590210c2dc6408430b7988210c2de6108430f3c84210c3d62108430f3484210c3d52108430f1484210c2de6008430b7580210c2de6494030b7592500c35f5494030d7952500c35d5494030d7152500c2de6294030b758a500c35e5294030d754a500c2de6194030b7586500c35e5194030d7546500c35f649
  | 19 => 0x4210c2df6308430b798c210c2dd6308430b718c210c3e521084309f992500c27d6494030d7d0e500c35e4394030d750e500c35c4394030d7cca500c35e3294030d74ca500c35c3294030d7cc6500c35e3194030d74c6500c35c31940309f597400c2de63d0030b758f400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c27f6550030b7d8d400c2dc6350030bbd89400c2ec6250030bdd85400c2f461500309fd94400c27e65100309f594400c27c6510030cf950400c33d5410030b798c400c2dd6310030ee500400c2df64cc030b7993300c2dd64cc030b7193300c2de62cc030b758b300c2de61cc030b7587300c2dd638c030d794e300c2f9638c030de94e300c3da538c030f6d0e300c3da438c030f650e300c3d8438c030f6cca300c3da328c030f64ca300c3d8328c030f6cc6300c3da318c030f64c6300c3d8318c0309fd95300c2df654c030d7d95300c25f654c030b7d91300c2de644c030b7591300c2dc644c030b7d89300c2dc624c030b7d85300c2dc614c030b7d81300c35e504c030bed95300c37b654c0309ed95300c2fb634c030f6d8d300c37a534c030f694d300c2de62d5030b758b540c2de61d5030b7587540c2de60d5030f6983540c2da60d5030b7596540c35f5495030e7d52540c2de6295030b758a540c2de6195030b7586540c39f5455030d7951540c2df6255030b7189540c2df6155030b7185540c2de6415030d7d50540c39e5415030d7550540c39d5415030c7550540c2de6215030f3988540c2ce6215030b7588540c3cd6215030b3588540c2de6115030f5984540c2d66115030b7584540c3d56115030b5584540c2de6015030f6980540c2da6015030b7993520c2dd64d4830d7d53520c35d54d4830b7987520c2dd61d4830b7983520c3da60d4830b6983520c2dd6594830b7992520c2dd6494830d7d4a520c3cf5294830b7986520c2dd6194830b7d91520c2dc6454830d7d51520c35d5454830f3d49520c35e5254830b7d85520c2dc6154830b7990520c39e6414830a7990520c2dd6414830e7590520c29d6414830b7988520c35f5214830f3948520c35d5214830f3548520c34d5214830b7984520c3d66114830b5984520c2dd6114830f5584520c2d56114830b7980520c3da6014830b6980520c2df65d0830b7997420c2dd65d0830b7197420c39e54d0830e7553420c2de61d0830b7587420c2de60d0830b7583420c2df6590830b7996420c2dd6590830b7196420c2dd6490830b798a420c3ce5290830f354a420c39f4290830f3d0a420c2de6190830b7586420c2de6090830b7582420c2df6550830b7995420c2dd6550830b7195420c39e5450830e7551420c3ce5250830f3549420c3cf4250830e7909420c2df6150830b7185420c2df6050830f6d81420c2db6050830
  | 20 => 0xc3ad4210830db94b320c36d52cc830be983320c2f960cc830b7d93320c2de64cc830b7593320c2dc64cc830d7d53320c35d54cc830d794b320c3ce52cc830f354b320c2de61cc830b7587320c3da60cc830b7583320c3d960cc8309f596320c2dd638c830b7596320c35d658c830b7d92320c2de648c830b7592320c2dc648c830b798a320c35d528c830b7986320c2dd618c830b7582320c27f654c830b7d95320c35f654c830b7d91320c2de644c830b7591320c2dc644c830d7d51320c35d544c830f3d89320c35e524c830b7d85320c2dc614c830b7d81320c2de630c830db948320c36d520c830be980320c2f9600c830b7d90320c2de640c830b7590320c2dc640c830b7988320c3ce620c830f3948320c35d520c830f3548320c34d520c830b7984320c2dd610c830f6980320c2dd600c830f6580320c37751944309f992510c27d64944309f98a510c27d62944309fd91510c27c6454430d790d510c35d43544309fd89510c27c6254430d7cc9510c35d3254430af990510c2bd6414430bb988510c2ed6214430dd544510c27f65d04309f997410c27d65d0430cf953410c33d54d0430b798f410c2dd63d04309fd96410c27e65904309f596410c2de6390430b758e410c3765190430dd546410c27f65504309f595410c27c6550430cf951410c33d5450430b7d8d410c2dc6350430dd945410c3755150430bed81410c2f860504309fd94410c27e65104309f594410c2de6310430b758c410c3b54110430dd947310c37551cc430be983310c2f960cc430b7d93310c2de64cc430b7593310c2dc64cc430d7d53310c35d54cc430b798b310c2dd62cc430d754b310c35e51cc430f5947310c3d551cc430f6983310c2dd60cc430f6583310c27d658c430b758e310c2dd658c430d7596310c2df648c430b7992310c2dd648c430b7192310c2de628c430b758a310c2de618c430d7546310c2dd608c4309fd95310c2df654c430d7d95310c2df644c430b7991310c2dd644c430b7191310c35f544c430d7551310c2df624c430b7189310c35d524c430f5d85310c35e514c430b7d81310c2de630c430dd944310c375510c430be980310c2f9600c430b7d90310c2de640c430b7590310c2dc640c430b7988310c2dd620c430b7984310c3d6610c430f5944310c35d510c430f5544310c355510c430f6980310c2dd600c430f6580310c27f65c84309f997210c27d65c8430b7d8f210c2de63c8430b758f210c2dc63c8430db94b210c36d52c84309fd96210c27e65884309f596210c2df6388430b798e210c2dd6388430b718e210c3765188430dd546210c27f65484309f595210c27c6548430b7d8d210c2de6348430b758d210c2dc6348430db949210c36d5248430dd945210c3755148430bed81210c2f860484309fd94210c27e65084309f59
  | 21 => 0x608c530ddd45314c374514c530bed81314c2f8604c5309f994314c3d5310c5309f997214c27d65c85309f197214c37751c8530dd147214c27e65885309f596214c27c6588530dbd4a214c36c52885309fd95214c27e65485309f195214c27e65085309f594214c27c6508530b798c214c2dd6308530dbd48214c36c5208530ddd44214c3745108530f9484214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d01309f996404c27f65501309f595404c27c6550130cfd51404c33c5450130b7d8d404c2dc6350130bbd89404c2ec6250130bdd85404c2f461501309f994404c35f548c130d7952304c35d548c130d7152304c35f528c130d714a304c35f518c130d7146304c3db508c1309f98f540c35e63d50309f98b540c27d62d50309f987540c27d61d50309f983540c37a60d50309f596540c33f5495030d798e540c27e62950309f58a540c27e61950309f586540c33f64550309fd8d540c27d6355030d718d540c27f62550309f189540c27f61550309f185540c33d5415030bb988540c2ed6215030bd984540c2f561150309f990540c33e64150309f98c540c35e63150309f988540c36e62150309b988540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a60150309f992530c27d6494c309f597430c2dd65d0c30d7597430c35f54d0c30d7553430c2de62d0c30b758b430c2de61d0c30b7587430c2dd60d0c309fd96430c27d6590c30cf952430c33d5490c30b798e430c2fa6090c30be582430c35d6590c3097596430c2dd6490c30d7952430c39e5490c30e7552430c35c5490c30b798a430c2dd6290c30b7986430c2dd6190c30f6982430c2dd6090c30f6582430c27f6550c30b7d95430c35f6550c30e7d91430c35e5450c30d7151430c2df6250c30b7189430c2df6150c30b7185430c2df6050c309fd94430c27d6510c30cf950430c33d5410c30b798c430c2fa6010c30be580430c35d6510c3097594430c2de6410c30e7990430c35f5410c30e7950430c35d5410c30e7550430c31d5410c30b7988430c2dd6210c30b7984430c2dd6110c30f6980430c2dd6010c30f6580430c36f52948309f992520c27d64948309f986520c27d61948309fd91520c27c6454830d790d520c35d43548309fd85520c27c6154830af990520c2bd6414830db548520c2f66114830bd584520c27f65d08309f997420c27d65d0830cf953420c33d54d0830b798f420c2dd63d08309fd96420c27e65908309f596420c2de6390830b758e420c36e5290830db54a420c27f65508309f595420c27c6550830cf951420c33d5450830b7d8d420c2dc6350830db949420c36d5250830bed81420c2f860508309fd94420c27e65108309f594420c2de6310830b758c420
  | 22 => 0x630d7994218c25e6508630b7594218c35d650863097594218c2dc6508630b7d90218c2de6408630b7590218c2dc6408630f3c84218c3d62108630f3484218c3d52108630f1484218c2de6008630b7580218c2dd65d0230d7597408c2de62d0230b758b408c2de61d0230b7587408c2dd6590230e7952408c39d5490230b798a408c2dd6290230e790a408c39c4290230b7986408c2dd6190230e7906408c39c4190230e7d02408c3db4090230b7d95408c35f6550230b7d89408c3cf6250230b3d89408c2dc6250230f3189408c2cc6250230b7d85408c3d76150230b5d85408c2dc6150230f5185408c2d46150230f6d01408c39e4050230b7594408c39e5410230e7550408c2de6210230b7588408c39e4210230e7108408c2de6110230b7584408c39e4110230e7104408c39f4010230f6900408c39d4010230f6500408c27e62d51309f58b544c27e61d51309f587544c33f54951309f992544c27d6395130d758e544c25d63951309f98a544c27d62951309f986544c27d61951309f582544c3796095130bbd89544c2ec6255130bdd85544c2f46155130cfd91544c27f6355130d7d8d544c25f63551309fd89544c36f62551309bd89544c27c6255130db189544c26c62551309fd85544c37761551309dd85544c27c6155130dd185544c27461551309fd81544c37b60551309f994544c33d5415130cf990544c27e63151309f18c544c27e62151309f588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d309f996434c27c6550d30cfd51434c33c5450d30bed81434c2f86050d309f994434c39d4310d309f993524c27d64d49309f987524c27d61d4930dbd4a524c2bf6454930af191524c2f76154930bd185524c36d52149309f990524c27d64149309f984524c27d61149309f997424c27d65d09309f197424c36f52d0930db14b424c27e65909309f596424c27c6590930cfd52424c33c54909309fd95424c27e65509309f195424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930dbd48424c36c5210930eb508424c27e65cc930dbd4a324c36c528c930be982324c2f9608c930dbd49324c36c524c930bed81324c2f8604c9309f994324c3cd320c9309f993514c27d64d45309f98b514c27d62d4530ddd46514c2bf6454530af191514c2ef6254530bb189514c37551145309f990514c27d64145309f988514c27d62145309f997414c27d65d05309f197414c37751d0530dd147414c27e65905309f596414c27c6590530cfd52414c33c54905309fd95414c27e65505309f195414c27e65105309f594414c27c6510530cfd50414c33c5410530b798c414c2dd6310530ddd44414c3745110530ed504414c27e65cc530ddd46314c374518c530be982314c2f9
  | 23 => 0x7951548c2df6255230b7189548c2df6155230b7185548c35f5415230e7950548c35d5415230e7550548c2de6215230b7588548c2de6115230b7584548c2de6015230f6980548c2da6015230b7993528c2dd64d4a30d7d53528c35d54d4a30b7987528c2dd61d4a30b7983528c3da60d4a30b6983528c2de6494a30b7592528c35f5294a30f3d4a528c34f5294a30b7986528c2dd6194a30b7d91528c2dc6454a30d7d51528c35d5454a30f3d49528c35e5254a30b7d85528c2dc6154a30b7990528c2dd6414a30d7d48528c3ce5214a30d7548528c3cd5214a30b7984528c2dd6114a30b7980528c3da6014a30b6980528c2df65d0a30b7997428c2dd65d0a30b7197428c2de61d0a30b7587428c2de60d0a30b7583428c2df6590a30b7996428c2dd6590a30b7196428c39f4290a30f3d0a428c2de6190a30b7586428c2de6090a30b7582428c2df6550a30b7995428c2dd6550a30b7195428c3cf4250a30e7909428c2df6150a30b7185428c2df6050a30b7181428c2df6510a30b7994428c35e6510a3097994428c2dd6510a30d7594428c25d6510a30b7194428c39f4210a30f3908428c39d4210a30f3508428c38d4210a30b7984428c2dd6110a30b7980428c2dd6010a30b7993518c2dd64d4630d7d53518c35d54d4630b798b518c2dd62d4630d7d4b518c35d52d4630b7983518c3da60d4630b6983518c2de6494630b7592518c2de6294630b758a518c35f5194630f5d46518c3575194630b7d91518c2dc6454630d7d51518c35d5454630b7d89518c2dc6254630d7d49518c35d5254630f5d45518c35e5154630b7990518c2dd6414630b7988518c2dd6214630d7d44518c3d65114630d7544518c3d55114630b7980518c3da6014630b6980518c2df65d0630b7997418c2dd65d0630b7197418c2de62d0630b758b418c2de60d0630b7583418c2df6590630b7996418c2dd6590630b7196418c2de6290630b758a418c39f4190630f5d06418c2de6090630b7582418c2df6550630b7995418c2dd6550630b7195418c2df6250630b7189418c3d74150630e7905418c2df6050630b7181418c2df6510630b7994418c35e651063097994418c2dd6510630d7594418c25d6510630b7194418c2de6210630b7588418c39f4110630f5904418c39d4110630f5504418c3954110630b7980418c2dd6010630b7d97218c2de65c8630b7597218c2dc65c8630b7d93218c2de64c8630b7593218c2dc64c8630b7983218c2dd60c8630b7d96218c2de6588630b7596218c2dc6588630b7d92218c2de6488630b7592218c2dc6488630f3c86218c3d72188630b7982218c2dd6088630b7d95218c2de6548630b7595218c2dc6548630b7d91218c2de6448630b7591218c2dc6448630f5c85218c3ce2148630b7d81218c2dc6048630b7d94218c2de6508
  | 24 => 0x328c36e528ca30db54a328c2fa608ca30be582328c2df648ca30b7992328c2dd648ca30b7192328c3ce528ca30d754a328c3cd528ca30b7986328c2dd618ca30f6982328c2dd608ca30f6582328c36e524ca30db549328c2fb604ca30be181328c2df644ca30b7991328c2dd644ca30b7191328c35f544ca30d7551328c3cf624ca30d7949328c3ce524ca30d3949328c3cd524ca30b7d85328c2dc614ca30b7d81328c3db604ca30f6181328c2dd650ca30d7594328c2df640ca30b7990328c2dd640ca30b7190328c3ce620ca30d7548328c2de610ca30b7584328c2dd600ca30ddd46518c27e64946309f592518c27e62946309f58a518c27f64546309f191518c35e4354630d750d518c27f62546309f189518c35f3254630d74c9518c37551146309fd97418c27e65d06309f597418c2de63d0630b758f418c27f65906309f996418c27d6590630b798e418c2dd63906309fd95418c27d65506309f195418c2df6350630b718d418c27f65106309f994418c27d6510630b798c418c2dd6310630ed504418c2dd65cc630d7597318c2df64cc630b7993318c2dd64cc630b7193318c35f54cc630d7553318c2de62cc630b758b318c35d52cc630d7947318c2dd60cc630dd946318c375518c630be982318c2f9608c630b7d92318c2de648c630b7592318c2dc648c630b798a318c2dd628c630f5946318c35d518c630f5546318c3da608c630b7582318c3d9608c630dd945318c375514c630bed81318c2f8604c630b7d91318c2de644c630b7591318c2dc644c630d7d51318c35d544c630b7d89318c2dc624c630d7549318c3d7614c630d7945318c3d6514c630d5945318c3d5514c630b7d81318c3db604c630f6181318c2dd650c630d7594318c2df640c630b7990318c2dd640c630b7190318c2de620c630b7588318c3d6610c630d7544318c2dd600c6309fd97218c27e65c86309f597218c2df63c8630b798f218c2dd63c8630b718f218c27f65886309f996218c27d6588630b7d8e218c2de6388630b758e218c2dc63886309fd95218c27d65486309f195218c2df6348630b798d218c2dd6348630b718d218c27f65086309f994218c27d6508630b7d8c218c2de6308630b758c218c2dc6308630f9484218c2de63d0230b758f408c33e5490230cf552408c2de6390230b758e408c2df6350230b718d408c2ef6250230bb189408c2f76150230bd185408c33e5410230cf550408c2de6310230b758c408c2dd65cc230d7597308c2df64cc230b7993308c2dd64cc230b7193308c2de62cc230b758b308c2de61cc230b7587308c2f965cc230de597308c2de62d5230b758b548c2de61d5230b7587548c2de60d5230f6983548c2da60d5230d7d52548c39f5495230c7d52548c2de6295230b758a548c2de6195230b7586548c39f5455230d
  | 25 => 0x2f960ccb30db94832cc36d520cb30f34c832cc2fa600cb30be58032cc2be64d4730af59351cc2ee62d4730bb58b51cc37751947309f99251cc27d64947309f98a51cc27d62947309fd9151cc27c64547309fd8951cc27c6254730dd54451cc27f65d07309f99741cc27d65d0730dd94741cc37551d07309fd9641cc27e65907309f59641cc33e5490730cf55241cc27f65507309f59541cc27c6550730bed8141cc2f860507309fd9441cc27e65107309f59441cc33e5410730cf55041cc2de6310730b758c41cc3765110730dd54441cc3b54110730dd94731cc37551cc730be98331cc2f960cc730dd94431cc375510c730f54c431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730dd94721cc37551c87309fd9621cc27e65887309f59621cc36e5288730db54a21cc27f65487309f59521cc27c6548730bed8121cc2f860487309fd9421cc27e65087309f59421cc2de6308730b758c21cc36e5208730db54821cc3765108730dd54421cc3e52108730cf95340cc33d54d0330b798f40cc2dd63d0330cf95140cc33d5450330b7d8d40cc2dc6350330bbd8940cc2ec6250330bdd8540cc2f46150330ee50040cc35d63d52309f98b548c27d62d52309f987548c27d61d5230de983548c33f5495230d758e548c27e62952309f58a548c27e61952309f586548c33f6455230d7d8d548c27f62552309f189548c27f61552309f185548c33d5415230cf990548c35d63152309f988548c27d62152309f984548c27d6115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c35d65d0e30d7d53438c39e54d0e30d7553438c39d54d0e30b798b438c2dd62d0e30b7987438c2dd61d0e30f6983438c2dd60d0e30f6583438c2dd6590e30d7596438c35e5490e30d7152438c2de6290e30b758a438c2de6190e30b7586438c2dd6090e30cf951438c33d5450e30bed81438c2f86050e30d7d95438c39f6450e30d7951438c39e5450e30c7951438c39d5450e30d7151438c2df6250e30b7189438c2df6150e30b7185438c2df6050e30f6d81438c3d86050e30b7594438c35d6510e30e7990438c35f5410e30d7550438c2de6210e30b7588438c2de6110e30b7584438c2dd6010e30dbd4a528c27e6494a309f592528c27e6194a309f586528c27f6454a309f191528c35e4354a30d750d528c27f6154a309f185528c36d5214a309fd97428c27e65d0a309f597428c2de63d0a30b758f428c27f6590a309f996428c27d6590a30b798e428c2dd6390a309fd95428c27d6550a309f195428c2df6350a30b718d428c27f6510a309f994428c27d6510a30b798c428c2dd6310a30eb508428c2dd65cca30d7597328c2df64cca30b7993328c2dd64cca30b7193328c35f54cca30d7553328c35e52cca30b7987328c2dd61cca30b7583
  | 26 => 0x10440be580411039e6310440e758c41102be6210440af98441103b66110440ed944411033d5110440ed54441103355110440ee98041102bd6010440ee580411027f65cc4409f997311027d65cc440af99331102bd64cc440d794f311035d53cc4409fd96311027e658c4409f5963110376518c440dd546311027f654c4409f595311027c654c440afd9131102bc644c440d794d311035d534c440dd9453110375514c440bed8131102f8604c4409fd94311027e650c4409f594311027f65c84409f997211027d65c8440af99321102bd64c8440db94b211036d52c84409fd96211027e65884409f59621102be6488440af59221103765188440dd546211027f65484409f595211027c6548440afd9121102bc6448440db949211036d5248440dd94521103755148440bed8121102f860484409fd94211027e65084409f59421102bf6408440af19021102de6308440b758c21103e52108440cf90a501033c4294040cf906501033c4194040b798f40102dd63d0040e798f401039d63d0040af98b40102be61d0040af592401033e5490040be592401037a5490040ee95240103ba4290040ee10a40103ba4190040ee106401027f6550040b7d8d40102dc6350040bbd8940102ec6250040bdd8540102f46150040afd95401033f65500408fd95401039f6350040e718d40103af6250040af18940103ac6250040ab18940103b76150040af18540103b46150040ad18540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040f6d8d40103d86350040ee90d40103b84350040fad8940103e86250040fcd8540103f06150040bb98b54cc2ed62d5330bd98754cc2f561d5330d798f54cc27e62d5330db98b54cc26e62d53309f58b54cc36d62d53309b58b54cc27e61d5330dd98754cc27661d53309f58754cc37561d53309d58754cc37960d5330cfd5254cc27e62953309f58a54cc27e61953309f58654cc33f64553309fd8954cc27c62553309fd8554cc27c6155330cf55054cc33e6415330d798c54cc27e62153309f58854cc27e61153309f58454cc3796015330cf95243cc33d5490f30be98243cc2f96090f30cf95043cc33d5410f30e750c43cc2fa6010f30be58043cc2be64d4b30af59352cc2f661d4b30bd58752cc36f5294b309f99252cc27d6494b309f98652cc27d6194b309fd9152cc27c6454b309fd8552cc27c6154b30db54852cc27f65d0b309f99742cc27d65d0b30db94b42cc36d52d0b309fd9642cc27e6590b309f59642cc33e5490b30cf55242cc27f6550b309f59542cc27c6550b30bed8142cc2f86050b309fd9442cc27e6510b309f59442cc33e5410b30cf55042cc2de6310b30b758c42cc36e5210b30db54842cc3ad4210b30db94b32cc36d52ccb30be98332cc
  | 27 => 0x409f994315027d650c5409f19431502be640c540af590315035f530c540d714c315036f520c540db1483150377510c540dd144315027e65c85409f597215027c65c8540d7d4f215035c53c8540dbd4b215036c52c8540ddd47215037451c85409f996215027d65885409f196215035f5388540d714e215036f5288540db14a21503775188540dd146215027f65485409f995215027c6548540d7d4d215035c5348540dbd49215036c5248540ddd45215037451485409f994215027d65085409f19421502be6408540af59021502de6308540b758c215035f5308540d714c215036f5208540db14821503775108540dd14421503e52108540be98021502f96008540b798f40502dd63d0140d7d4f405035c53d0140dbd4b405036c52d0140ddd47405037451d0140f698f40503d963d0140f6d4f40503d853d0140fad4b40503e852d0140fcd4740503f051d0140d7d4e405035c5390140dbd4a405036c5290140ddd4640503745190140e7d4e405039c5390140ebd4a405033c5290140eb14a405032c5290140edd46405033c5190140ed14640503345190140eed42405035e6395040d758e541035f5394c409f98a531027d6294c409f986531027d6194c409fd89531027c6254c409fd85531027c6154c40d754c53102ee6214c40bb58853102f66114c40bd584531035e53d0c40d754f43102fa60d0c40be583431027d6590c409fd95431035e5310c40d754c43102fa6010c40be580431036f52948409f98e521027d63948409f986521027d61948409fd8d521027c63548409fd85521027c6154840b798c52102dd6314840db54852102f66114840bd584521036e52d0840db54b42102fa60d0840be583421027d6590840af596421033d6590840af98a421033d5290840af98642102bd60908409fd9542102de6310840b758c421036e5210840db54842103ad4210840be98042102f96010840e798c421039d6310840af98842103ae6210840eb948421033d5210840eb548421032d5210840af98442103ba6010840af58042103b960108409fd97321027e65cc8409f59732102be64cc840af593321035e53cc840d754f321027f658c8409f996321027d658c840db94a321036d528c8409fd95321027d654c8409f19532102bf644c840af191321035e534c840d754d321036e524c840db54932102fb604c840be181321027f650c8409f994321027d650c840ddd46511027e63944409f58e511027e62944409f58a511027f63544409f18d511027f62544409f18951102de6314440b758c51102ee6214440bb58851103755114440dd947411037551d0440be98341102f960d04409f59641102bd6590440cf59641102be6290440af986411033d5190440af582411027f6550440b798c41102dd6310440dd94441103755110440ed50441102fa6
  | 28 => 0xd4d425035c5350940dbd49425036c5250940bed8142502f860509409f99442502de6310940b758c425035f5310940d714c425036f5210940eb508425027e65cc9409f597325027c65cc940d7d4f325035c53cc940dbd4b325036c52cc9409f996325027d658c9409f196325035f538c940d714e325036f528c940db14a325027f654c9409f995325027c654c940d7d4d325035c534c940dbd49325036c524c9409f994325027d650c9409f19432502be640c940af590325035f530c940d714c325036f520c940db148325035f53d4540d714f515036f52d4540db14b515027e63d45409f58f515027e62d45409f58b515037753d4540f5d4f515035753d4540dd94f515037553d4540dd14f51503d453d4540d514f515037752d4540f9d4b515036752d4540dd94b515037552d4540dd14b51503e452d4540d914b515037764d4540ddd8f515037663d4540dd58f515037463d4540ddd0f515037643d4540dd50f515037443d4540ddd8b515037662d4540dd58b515037462d4540ddd0b515037642d4540dd50b515037442d4540ddccb515037632d4540dd4cb515037432d4540ddd83515037560d4540b798e51502dd6394540d7d4e515035c5394540bb98a51502ed6294540dbd4a515036c5294540ddd4651502df6354540b718d515035f5354540d714d51502ef6254540bb189515036f5254540db149515035f5314540d714c515036f5214540db148515037551145409f98c515027d63145409f988515027d6214540bd99451503766514540ddd4c51503d75314540d5d4c51503765314540dd54c51503745314540f514c51503545314540ddd4851503e75214540d9d4851503765214540dd54851503745214540f914851503645214540ddd9051503776314540dd98c51503756314540dd18c51503774314540dd90c51503754314540dd10c51503776214540dd98851503756214540dd18851503774214540dd90851503754214540dd10851503773214540dd8c851503753214540dd0c851503776014540dd580515037540145409f997415035f53d0540d714f415036f52d0540db14b415037451d0540d7d4e415035c5390540dbd4a415036c5290540ddd4641503745190540be98241502f96090540d7d4d415035c5350540dbd49415036c5250540ddd4541503745150540bed8141502f860505409f99441502de6310540b758c415035f5310540d714c415036f5210540db14841503775110540ed504415027e65cc5409f597315027c65cc540d7d4f315035c53cc540dbd4b315036c52cc540ddd47315037451cc5409f996315027d658c5409f196315035f538c540d714e315036f528c540db14a3150377518c540dd146315027f654c5409f995315027c654c540d7d4d315035c534c540dbd49315036c524c540ddd453150374514c5
  | 29 => 0x1903b55190640ee98241902bd6090640ee58241903765150640dd54541902fb6050640be18141902de6310640b758c41903b54110640af594419033d6510640e798c419039d6310640af98841903b66110640edd44419033d5110640ed14441902bd60106409fd97319027e65cc6409f59731902be64cc640af593319027f658c6409f996319027d658c6409fd95319027d654c6409f19531902bf644c640af191319027f650c6409f994319027d650c6409fd97219027e65c86409f59721902be64c8640af593219027f65886409f996219027d6588640af99221902bd64886409fd95219027d65486409f19521902bf6448640af191219027f65086409f994219027d6508640afd9021902bc6408640b798c21902dd6308640f948421902fa6008640be58021902de63d0240b758f40902bd65d0240cf597409039e63d0240e758f40902be62d0240af98740902f965d0240de59740903da63d0240f658f409027e62d4d409f58b535027e61d4d409f587535035f64d4d40d7d8b535035e62d4d40d758b535035c62d4d40d7d87535035e61d4d40d7587535035c61d4d40d7d83535035d60d4d40d7d4e53502ee6294d40bb58a53502f66194d40bd58653502ef6254d40bb18953502f76154d40bd185535035d5314d409f988535027d6214d409f984535027d6114d40b7994535035e6514d40d7d90535035f6214d40d7988535035d6214d40d7188535035f6114d40d7984535035d6114d40d7184535035f6014d40d7580535035d4014d409f997435035c53d0d40d7d4e435035c5390d40be98243502f96090d40d7d4d435035c5350d40bed8143502f86050d409f994435035f5310d40e750c435035f53d4940d714f525027e63d49409f58f525027e61d49409f587525036f53d4940f3d4f525034f53d4940db94f525036d53d4940db14f52503cc53d4940d314f525036f64d4940dbd8f525036e63d4940db58f525036c63d4940dbd0f525036e43d4940db50f525036c43d4940dbd87525036e61d4940db587525036c61d4940dbd83525036d60d4940b798e52502dd6394940d7d4e525035c5394940dbd4a52502f66194940bd58652502df6354940b718d525035f5354940d714d52502f76154940bd185525035f5314940d714c525036d52149409f98c525027d63149409f984525027d6114940bb994525036e6514940dbd4c52503cf5314940d3d4c525036e5314940db54c525036c5314940f314c525034c5314940dbd90525036f6314940db98c525036d6314940db18c525036f4314940db90c525036d4314940db10c525036f6114940db984525036d6114940db184525036f6014940db580525036d40149409f997425035f53d0940d714f425036c52d0940d7d4e425035c5390940dbd4a425036c5290940be98242502f96090940d7
  | 30 => 0x7d654cb409f19532d035e534cb40d754d32d02fb604cb40be18132d027f650cb409f99432d027d650cb40af99032d02bd640cb40d794c32d035d530cb40b798f51d02dd63d4740d794f51d035d53d4740bb98b51d02ed62d4740d794e51d035d5394740ddd4651d027e63947409f58e51d027e62947409f58a51d035e5354740d754d51d027f63547409f18d51d027f62547409f18951d02de6314740b758c51d035e5314740d754c51d03755114740d794f41d035d53d0740dd94741d037551d0740be98341d02f960d0740d794e41d035d5390740d794d41d035d5350740b798c41d02dd6310740d794c41d035d5310740dd94441d03755110740ed50441d02fa6010740be58041d027f65cc7409f99731d027d65cc740d794f31d035d53cc7409fd9631d027e658c7409f59631d035e538c740d754e31d027f654c7409f59531d027c654c740d794d31d035d534c740bed8131d02f8604c7409fd9431d027e650c7409f59431d02be640c740af59031d035e530c740d754c31d027f65c87409f99721d027d65c8740d794f21d035d53c8740dd94721d037551c87409fd9621d027e65887409f59621d035e5388740d754e21d036e5288740db54a21d027f65487409f59521d027c6548740d794d21d035d5348740bed8121d02f860487409fd9421d027e65087409f59421d02be6408740af59021d02de6308740b758c21d035e5308740d754c21d036e5208740db54821d03765108740dd54421d03e52108740d7d4e539027e6294e409f58a539027e6194e409f586539027f6254e409f189539027f6154e409f185539035d5314e40d794e439035d5390e40be98243902f96090e40d794d439035d5350e40bed8143902f86050e40b798e52902dd6394a40dbd4a529027e6394a40d798e529025e6394a409f58e529035d6394a409758e529027e6194a409f586529027f6354a409f18d529027f6154a409f185529036d5214a40db94a429036d5290a40be98242902f96090a40eb94a429033d5290a40eb54a42902be6190a40ee98242902bd6090a40ee582429036e5250a40db54942902fb6050a40be18142902de6310a40b758c42903ad4210a40af594429033d6510a40e798c429039d6310a40eb98842903af5210a40cf54842903ac5210a40af98442902bd6010a409fd97329027e65cca409f59732902be64cca40af593329027f658ca409f996329027d658ca409fd95329027d654ca409f19532902bf644ca40af191329027f650ca409f994329027d650ca40b798e51902dd6394640ddd46519027e6394640d798e519025e63946409f58e519035d63946409758e519027e62946409f58a519027f63546409f18d519027f62546409f18951903755114640dd94641903755190640be98241902f96090640af98a41903b65190640cf5464
  | 31 => 0x88421db94a21087d65388421f554e21086f56288421b958a21087765288421f994a21086f660884219fd95210875e5348421d754d21086ef6548421dbd95210866f6548421f394d21087cd5348421bbd85210876e5148421f9d0521087e64148421f950521087e44148421f9cc521087e63148421f94c521087e43148421bb18121086f76548421ddd9521086776548421f594d21087d55348421bdd8921087e76248421dd94921087e65248421f9d0921087e64248421f950921087e44248421f9cc921087e63248421f94c921087e43248421bd18121087e76548421b9d9521087676548421f9d9121087e66448421f959121087e46448421f9d5121087e65448421f955121087e45448421f9d8d21087e66348421f958d21087e46348421f9d4d21087e65348421f194d21087e55348421f154d21087e45348421f9d0d21087e64348421f950d21087e44348421f9d8121087e66048421f958121087e46048421b918121086de63d4021b758f500875e53d4021d754f50087e521d4021d794e500875d5394021f9486500877b50940219f992500867d6494021d7d8e500867e63940219f58e500875c6394021afd9150086bc6454021b7d8d50086dc6354021d794d500875d5354021f9485500867f6454021cfd91500863f64540219f191500873c64540218f191500867f6354021d7d8d500865f63540219f18d500875c63540219718d50086be6414021af59050086de6314021b758c500875e5314021d754c50087e52114021de540500875f5394f409f98a53d027d6294f409f98653d027d6194f40d719253d035f6294f40d798a53d035d6294f40d718a53d035f6194f40d798653d035d6194f40d718653d035f6094f40d758253d027f6254f409f18953d027f6154f409f18553d035f6554f40d799153d035f6254f40d798953d035d6254f40d718953d035f6154f40d798553d035d6154f40d718553d035f6054f40d758153d035d5314f40d794f43d035d53d0f40be98343d02f960d0f40d754e43d035e5350f40d794c43d035d5310f40e750c43d02fa6010f40be58043d02de63d4b40b758f52d035e53d4b40d754f52d02f661d4b40bd58752d035e5394b40d754e52d036f5294b409f98e52d027d6394b409f98652d027d6194b40d794d52d035d5354b409fd8d52d027c6354b409fd8552d027c6154b40b798c52d02dd6314b40d794c52d035d5314b40db54852d035e53d0b40d754f42d036e52d0b40db54b42d02fa60d0b40be58342d035e5390b40d754e42d035e5350b40d754d42d02de6310b40b758c42d035e5310b40d754c42d036e5210b40db54842d03ad4210b40be98042d02f96010b409fd9732d027e65ccb409f59732d035e53ccb40d754f32d027f658cb409f99632d027d658cb40d794e32d035d538cb409fd9532d02
  | 32 => 0x1de980540867a60150219f580540877960150219e580540867e64d4c219f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530865d6594c21d7d52530875e5494c21d7552530875c5494c21b7982530875f6494c21d7992530875d6494c21d7192530875e6294c21d718a530875e6194c21d7186530875f6094c21d7982530865e6094c21d7582530875c6094c219fd91530867c6454c21d7d8d530867f6054c219f181530875f6554c21d7d51530875e5454c21d7551530875c5454c21b7181530875f6454c21d7991530875d6454c21d7191530875e6254c21d7189530875e6154c21d7185530875c2154c21d7d81530875e6054c21d7581530875c6054c219718153086de6314c21d754c530867e6414c219f590530867e6314c21d798c530865e6314c219f988530876e6214c219f98453087766114c219f980530867d6014c219fd97430867e65d0c219f597430867c65d0c21d794f430875d53d0c219fd96430867e6590c219f596430867c6590c21d794e430875d5390c219fd95430867e6550c219f595430867c6550c21d794d430875d5350c21bbd8943086ec6250c21bdd8543086f46150c219fd94430867e6510c219f594430867c6510c21d794c430875d5310c21bb98843086ed6210c21bd98443086f56110c219f992520867d64948219f98e520867d63948219f597420875e53d0821d754f420867f65908219f596420873e5490821cf552420875e5390821d754e42086f66190821bd586420867f6550821d794d420875d53508219fd94420867d6510821cf950420873d5410821b798c42086dd6310821d794c420875d5310821eb50842086f66110821bd584420867d65cc821d794f320875d53cc8219fd96320867d658c821d794e320875d538c821bd98632086f5618c8219fd95320875e534c821d754d320867f650c8219f594320875e530c821d754c32087cd320c821bd98432086f5610c8219f992510867d64944219f98e510867d63944219f597410875e53d0421d754f410867f65904219f596410873e5490421cf552410875e5390421d754e41086ee6290421bb58a410867f6550421d794d410875d53504219fd94410867e65104219f594410867c6510421cf950410873d5410421b798c41086dd6310421d794c410875d5310421bb98841086ed6210421ed504410867d65cc421d794f310875d53cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c4219fd95310875e534c421d754d310867f650c4219f994310867d650c4219f194310875e530c421d754c31086ee620c421bb58831087d5310c421d794f210875d53c8421f394f21087cd53c8421bb983210875e5388421d754e21086ed62
  | 33 => 0x81544867b60551219f181544877860551219e181544867e6515121cf55054486de6315121b758c544873e64151219f98c544875e63151219798c544867d6315121d758c544865d63151219f980544867d60151219f993534867d64d4d219f983534867d60d4d21d7d4e534867e6494d219f592534867e6394d219f58a534876d6294d219f58653487756194d219f982534867d6094d21afd9153486bc6454d21bed8153486f86054d219fd91534873f6454d218fd91534867c6454d21cf191534863c6454d21d7d8d534867f6254d21dbd89534867f6154d21ddd85534867f6054d21ded81534867b6054d219f18153487786054d219e181534867e6514d21d754c534867e6414d219f590534875e6314d219f980534867d6014d219fd97434867e65d0d219f597434867c65d0d21d7d4f434875c53d0d219fd96434867e6590d219f596434867c6590d21cfd52434873c5490d21d794e434875d5390d21bb98a43486ed6290d21bd98643486f56190d219fd95434867e6550d219f595434867c6550d21d794d434875d5350d219fd94434867e6510d219f594434867c6510d21cfd50434873c5410d21d7d4c434875c5310d219f997424873f54d0921cf15342486f661d0921bd587424867e65909219f195424873f5450921cf15142486f76150921bd185424867e6510921b798c42486dd6310921eb508424867e65cc921d7d4f324875c53cc921bd98732486f561cc9219f996324867c654c921d7d4d324875c534c921bdd8532486f4614c9219f994324867e65d0521cfd53414873c54d0521bb98b41486ed62d05219f996414867f65505219f595414867c6550521cfd51414873c5450521bbd8941486ec62505219f99441486de6310521b758c41487b541105219f997314875f53cc521d714f31486ee62cc521bb58b314867e658c5219fd95314867d654c5219f195314875f534c521d714d31486ef624c521bb189314867e650c521f9d4621486de63d4121b758f504867e64d41219f593504867e63d4121d798f504865e63d41219f58f504875d63d41219758f504877b5094121afd9150486bc6454121b7d8d50486dc6354121de540504867e64141219f590504867e63141219f58c50487772114121db88450486de63d5021b758f540867e63d5021d798f540865e63d50219f58f540875d63d50219758f540867e62d5021db98b540867e61d5021dd987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf55054086de6315021b758c54086fa6015021be580540867e6415021cf990540867e6315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e601502
  | 34 => 0xc86ed62cc721d794d31c875d534c721bbd8931c86ec624c721f54c431c86be64d4321af59350c86de63d4321b758f50c877b50943219f99250c867d64943219f98e50c867d6394321b7d8d50c86dc63543219fd9150c867c64543219fd8d50c875f635432197d8d50c867c6354321d718d50c865c6354321de54050c867e63d52219f58f548876d62d5221dd987548867e60d52219f583548873f54952219f98e548867d63952219f982548867d6095221cfd91548867f63552219f18d548867f60552219f181548873d5415221b798c54886dd6315221cf990548867e6315221d798c548865e63152219f58c548875d63152219758c548876d6215221dd984548867e60152219f580548867e64d4e219f593538876d62d4e21dd987538867e60d4e219f583538875f5394e219f992538867d6494e219f982538867d6094e219fd91538867c6454e21d7d8d538867f6054e219f18153886be6414e21af590538875d5314e219f990538873e6414e218f990538867d6414e21cf590538863d6414e21d798c538876d6214e21dd984538867e6014e219f580538867f65d0e219f997438867d65d0e219f197438873e54d0e21cf553438867f6590e219f996438867d6590e219f196438875e5390e21d754e43886f66190e21bd586438867f6550e219f995438867d6550e219f195438873e5450e21cf551438875e5350e21d754d43886ef6250e21bb189438867f6510e219f994438867d6510e219f19443886ee6210e21bb588438873e54d0a21cf55342886f661d0a21bd587428873e5450a21cf55142886f76150a21bd18542886de6310a21b758c42887ad4210a21d794f328875d53cca21bd98732886f561cca21d794d328875d534ca21bdd8532886f4614ca21f34c8328873e5490621cf55241886ee6290621bb58a418873e5410621cf55041886de6310621b758c41886ee6210621bb58841887b54110621d7d4f318875c53cc621d794e318875d538c621bb98a31886ed628c621d7d4d318875c534c621d794c318875d530c621bb98831886ed620c621bb597218876d65c8621bb98321886f565c8621dd59721886be64d4221af59350886de63d4221b758f508877b50942219f992508867d64942219f98e508867d6394221ddc8650886df6354221b718d508867f64542219f191508867f6354221d7d8d508865f63542219f18d508875c63542219718d508877950142219f98f544867d63d51219f983544867d60d5121cfd52544867e64951219f98e544867d63951219f58a544876d62951219f586544877561951219f982544867d6095121b7d8d54486dc6355121bed8154486f86055121cfd91544867f6355121d7d8d544865f63551219f18d544875c63551219718d544867f6255121dbd89544867f6155121ddd85544867f6055121ded
  | 35 => 0xd6510831cf950420c73d5410831b798c420c6dd6310831db948420c76d5210831eb508420c75e53cc831db94b320c76d52cc831bd987320c6f561cc8319f596320c67f654c831d794d320c76e520c831db548320c7cd320c831bd984320c6f5610c8319f992510c67d64944319f597410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c67f65504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431ed504410c75f54cc431d7553310c75d52cc431b7983310c6dd638c431d794e310c6f5638c431dd94e310c7d6538c4319fd95310c6df654c431d7d95310c65f654c431d7d51310c75d544c431d7549310c6df614c431d7945310c7d7414c431f5105310c6dc604c431bdd95310c777654c4319dd95310c6f7634c431f5d8d310c776534c431f594d310c7d7434c431f510d310c7d6324c431f50c9310c77b50940319f992500c67d6494031d718e500c67e62940319f58a500c75f3194031d74c6500c67f64540319f191500c67f62540319f189500c6be6414031af590500c6ee6214031bb588500c77950140319f98f54c867d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c867e63953219f58e54c867e60953219f58254c873f64553219fd8d54c867c63553219fd8154c867c6055321cf55054c86de6315321b758c54c873e64153219f98c54c875e63153219798c54c867d6315321d758c54c865d6315321db98854c877561153219f98054c867d60153219f99353c867d64d4f21db98b53c877561d4f219f98353c867d60d4f21d7d4e53c867e6494f219f59253c867e6094f219f58253c867f6454f219f19153c875f6354f219fd8153c867c6054f21af99053c86bd6414f21d754c53c867e6414f21cf99053c863e6414f219f59053c873d6414f218f59053c875e6314f21db98853c87756114f219f98053c867d6014f219fd9743c867e65d0f219f59743c867c65d0f21cf95343c873d54d0f219fd9643c867e6590f219f59643c867c6590f21d794e43c875d5390f21bb98a43c86ed6290f219fd9543c867e6550f219f59543c867c6550f21cf95143c873d5450f21d794d43c875d5350f21bdd8543c86f46150f219fd9443c867e6510f219f59443c867c6510f21bd98443c86f56110f21cf95242c873d5490b21bd98642c86f56190b21cf95042c873d5410b21b798c42c86dd6310b21eb50842c86f66110b21bd58442c875f53ccb21d714f32c875e538cb21d754e32c86f6618cb21bd58632c875f534cb21d714d32c875e530cb21d754c32c86f6610cb21bd58432c873e54d0721cf55341c86ee62d0721bb58b41c873e5450721cf55141c86ef6250721bb18941c86de6310721b758c41c87b54110721d794f31c875d53cc721bb98b31
  | 36 => 0xd319f993524c67d64d4931d790f524c75d43d49319f983524c67d60d4931dbd4a524c6bf6454931af191524c6fb6054931be181524c76d52149319f990524c67d64149319f980524c67d60149319f997424c67d65d09319f197424c6de63d0931b758f424c76f52d0931db14b424c6f661d0931bd587424c67e65909319f596424c67c6590931cfd52424c73c5490931b798e424c6dd6390931bd986424c6f561909319fd95424c67e65509319f195424c67e65109319f594424c67c6510931cfd50424c73c5410931b798c424c6dd6310931dbd48424c76c5210931eb508424c67e65cc931b7997324c75e65cc931b7d93324c6dd64cc931d7d53324c75d54cc931d714b324c6de61cc931b7983324c6dd638c931dbd4a324c76c528c931bd986324c6f5618c931dbd49324c76c524c931bdd85324c6f4614c931b7d91324c6dd644c931d7d51324c75d544c931f3d89324c7cf524c931d7149324c7cc524c931d3149324c7d7614c931b7185324c7d4614c931b5185324c6dc604c9319f994324c6de630c9319f997414c73f54d0531cf153414c6de63d0531b758f414c67e65905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c67e6510531b798c414c6dd6310531ed504414c7d643cc531f550f314c7d732cc531f54cb314c6df648c531b7592314c6dd628c531f5d46314c6de608c5319f993504c67d64d41319f98b504c67d62d4131ded42504c6bf6454131af191504c6ef6254131bb189504c77950141319f990504c67d6414131d7d8c504c75e4314131d750c504c67e62141319f588504c75f3214131d74c8504c75e3114131bb98b540c6ed62d50319f98f540c75e63d50319f98b540c76e62d50319b98b540c67d62d5031db58b540c66d62d50319f987540c77661d50319f983540c67d60d50319f596540c73f54950319f98a540c67d62950319f982540c67d6095031cfd91540c67f62550319f189540c67f60550319f181540c73d54150319f990540c73e64150319f98c540c75e63150319798c540c67e62150319f588540c67e6115031dd984540c67e60150319f580540c67e6494c319f592530c67d65d0c319fd96430c67d6590c31cf952430c73d5490c31d794e430c6f66190c31bd586430c67f6550c31d794d430c67f6510c319f594430c73e5410c31cf550430c79d4310c31bd984430c6f56110c31af993520c6bd64d4831dbd4a520c67e64948319f592520c67e60948319f582520c67f64548319f191520c67f60548319f181520c76d52148319fd97420c67e65d08319f597420c76e52d0831db54b420c67f65908319f996420c67d6590831cf952420c73d54908319fd95420c67d65508319f195420c6df6350831b718d420c6f76150831bd185420c67f65108319f994420c67
  | 37 => 0xb718532cc6dc604cb31db94832cc76d520cb31bd98432cc6f5610cb31cf95341cc73d54d0731b798f41cc6dd63d0731cf95141cc73d5450731b7d8d41cc6dc6350731b798c41cc6dd6310731ed50441cc6be64d4331af59350cc6ee62d4331bb58b50cc77b50943319f99250cc67d6494331d718e50cc75e4394331d750e50cc67e62943319f58a50cc75f3294331d74ca50cc67f64543319f19150cc67f62543319f18950cc7795014331d758f548c67e62d52319f58b548c77661d52319f983548c67d60d5231cfd52548c67e62952319f58a548c67e60952319f582548c73f64552319fd89548c67c62552319fd81548c67c6055231cf550548c73e6415231d758c548c67e62152319f588548c77661152319f980548c67d6015231cf953438c73d54d0e31bd987438c6f561d0e31cf951438c73d5450e31bdd85438c6f46150e31e750c438c76f5294a319f992528c67d6494a319f982528c67d6094a319fd91528c67c6454a319fd81528c67c6054a31db548528c67f65d0a319f997428c67d65d0a31bd987428c6f561d0a319fd96428c67e6590a319f596428c6f66190a31bd586428c67f6550a319f595428c67c6550a31b7d8d428c6dc6350a319fd94428c67e6510a319f594428c6de6310a31b758c428c7ad4210a31db94a328c76d528ca31bd986328c6f5618ca31db949328c76d524ca31bdd85328c6f4614ca31f34c8328c73e5490631cf552418c6de6390631b758e418c73e5410631cf550418c6de6310631b758c418c7b54110631b7597318c75d65cc631d7d53318c75d54cc631d754b318c6de60cc631bd597318c77565cc631ded42508c67e64942319f592508c75f63942319f98a508c67d6294231d7cc6508c67f64542319f191508c67f62542319f189508c77950142319f98b544c67d62d51319f983544c67d60d5131cfd52544c67e64951319f58e544c75d63951319f98a544c67d62951319f586544c77561951319f982544c67d6095131bbd89544c6ec6255131bed81544c6f86055131cfd91544c67f6355131d7d8d544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd85544c67f6055131ded81544c67b60551319f181544c77860551319e181544c67e6515131cf550544c73e6415131d758c544c67e62151319f588544c67e60151319f580544c67e65d0d31cfd53434c73c54d0d31bd987434c6f561d0d319f996434c6de6590d31d7996434c6dd6490d31d7952434c75c5490d31b758a434c6de6190d31b7982434c67c6550d31cfd51434c73c5450d31bdd85434c6f46150d31d7195434c65c6550d31e7d91434c79f5450d31d7951434c75c5450d31e7151434c71c5450d31b7d89434c7d76150d31b7185434c7d46150d31b5185434c6dc6050d319f994434c6de631
  | 38 => 0x5411073e5150441af18141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441f594d41107d55350441edd0d41107b64350441ed50d41107b44350441edd0941107b64250441ed50941107b44250441bd18141107b76550441add9541107376550441edd8d41107b66350441ed58d41107b46350441edd4d41107b65350441e594d41107b55350441e554d41107b45350441edd8941107b66250441ed58941107b46250441edd4941107b65250441ed54941107b45250441edcc941107b63250441ed4c941107b43250441edd8141107b66050441ed58141107b46050441ad18141106de63d4041b758f501075e53d4041d754f50107b541d4041d794e501075d5394041ed506501077b5094041d7d8e501067e63940419f58e501075c63940419f98a501067d6294041b7d8d50106dc6354041d794d501075d5354041bbd8950106ec6254041ed505501067f6354041d7d8d501065f63540419f18d501075c63540419718d501067f6254041dbd89501066f62540419f189501076c62540419b18950106de6314041b758c501075e5314041d754c50106ee6214041bb58850107b54114041de540501075e63d53319f98b54cc67d62d5331dd58754cc67e60d53319f58354cc73f5495331d798e54cc67e62953319f58a54cc67e60953319f58254cc73f64553319fd8954cc67c62553319fd8154cc67c6055331cf55054cc6ee6215331bb58854cc73e6415331d798c54cc67e6215331db98854cc66e62153319f58854cc76d62153319b58854cc77561153319f98054cc67d6015331cf95243cc73d5490f31bd98643cc6f56190f31d759643cc75e5490f31e795243cc79d5490f31d715243cc6dd6290f31b798643cc7d66190f31f558643cc6de6090f31b7d9543cc75f6550f31e7d9143cc75e5450f31d715143cc6df6250f31b718543cc6dc6050f31cf95043cc73d5410f31bd98443cc6f56110f31dbd4a52cc67e6494b319f59252cc67e6094b319f58252cc67f6454b319f19152cc75e4354b31d750d52cc67f6054b319f18152cc6be6414b31af59052cc76d5214b319fd9742cc67e65d0b319f59742cc73e54d0b31cf55342cc6de63d0b31b758f42cc67f6590b319f99642cc67d6590b31b798e42cc6dd6390b31db94a42cc76d5290b319fd9542cc67d6550b319f19542cc73e5450b31cf55142cc76e5250b31db54942cc6f76150b31bd18542cc67f6510b319f99442cc67d6510b31b798c42cc6dd6310b31eb50842cc76e52ccb31db54b32cc6f661ccb31bd58732cc6df64ccb31b759332cc75f54ccb31d755332cc75e52ccb31f394b32cc7cd52ccb31b798732cc7d661ccb31f558732cc6de60ccb31b7d9532cc75f654cb31b7d9132cc6dd644cb31d7d5132cc75d544cb31f3d8932cc75e524cb31
  | 39 => 0x65e63149419f58c525075d63149419758c525067e60149419f580525067e65d0941dbd4a425076c5290941bd98642506f56190941dbd49425076c5250941bdd8542506f461509419f99442506de6310941b758c42507ad42109419f997325067d65cc9419f19732506be64cc941af593325076f52cc941db14b32506f661cc941bd587325067e658c9419f596325067c658c941d7d4e325075c538c9419fd95325067e654c9419f195325067e650c9419f594325067c650c941d7d4c325075c530c941dbd48325076c520c941edd4641506de63d4141b758f505067e63d4141d798f505065e63d41419f58f505075d63d41419758f505067e62d41419f58b505077b5094141b7d8d50506dc6354141bbd8950506ec6254141de540505067e63141419f58c505067e62141419f58850507774114141cf904505075f5394c419f98a531067d6294c419f982531067d6094c41b7982531075c6494c41d7d8a531075e6294c41d758a531075c6294c41d7986531075c6194c41d7d82531075e6094c4197982531075d6094c41d7182531067f6254c419f189531067f6054c419f181531075f6554c41b7181531075e6454c41d7d89531075e6254c41d7589531075c6254c41d7985531075c6154c41d7105531075f6054c41d7981531075d6054c41d7181531065c6054c41b798c531075d5314c41d794f431075d53d0c41bd98743106f561d0c419f596431075d5390c419fd95431075e5350c41d794c431075d5310c41e750c43106f66110c41bd58443106de63d4841b758f521075e53d4841d754f521075e5394841d754e521076f52948419f98e521067d63948419f982521067d6094841d794d521075d53548419fd8d521067c63548419fd81521067c6054841b798c52106dd6314841d794c521075d5314841db54852106fa6014841be580521075e53d0841d754f421076e52d0841db54b42106f661d0841bd587421067d6590841d794e421075d53908419fd95421075e5350841d754d42106de6310841b758c421075e5310841d754c421076e5210841db54842107ad4210841bd98442106f561108419fd97321067e65cc8419f597321075e53cc841d754f321067f658c8419f996321067d658c841d794e321075d538c8419fd95321067d654c8419f19532106bf644c841af191321075e534c841d754d32106f7614c841bd185321067f650c8419f994321067d650c841af99032106bd640c841d794c321075d530c841bd98432106f5610c841d794f411075d53d0441e794f411079d53d0441af98341106bd6490441cf952411075e5390441d754e41106f56490441ad59241107765490441ed95241107d65390441f554e41106f660904419fd95411075e5350441d754d41106bf6550441cfd95411063f6550441e794d411079d5350441afd8
  | 40 => 0x6054f419f18153d075d5314f41bb98853d06ed6214f41d794f43d075d53d0f41bd98743d06f561d0f41d794c43d075d5310f41bd98443d06f56110f41dbd4a52d067e6394b419f58e52d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d06de6314b41b758c52d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41b798c42d06dd6310b41db94842d076d5210b41eb50842d06f66110b41bd58442d067f65ccb419f99732d067d65ccb41af99332d06bd64ccb41d794f32d075d53ccb419fd9632d067e658cb419f59632d076e528cb41db54a32d067f654cb419f59532d067c654cb41d794d32d075d534cb41db94932d076d524cb41bdd8532d06f4614cb419fd9432d067e650cb419f59432d06f6610cb41bd58432d06de63d4341b758f50d06ee62d4341bb58b50d077b50943419f98e50d067d63943419f98a50d067d6294341b7d8d50d06dc63543419fd8d50d075f635434197d8d50d067c6354341d718d50d065c63543419fd8950d067c6254341de54050d075f5394e419f98a539067d6294e419f982539067d6094e419fd89539067c6254e419fd81539067c6054e41d754c53906ee6214e41bb588539075e5390e41d754e43906f66190e41bd586439075e5350e41d754d43906f76150e41bd185439079d4310e41dbd4a529067e6394a419f58e529067e6094a419f582529067f6354a419f18d529067f6054a419f18152906de6314a41b758c529076d5214a41db94a429076d5290a41bd98642906f56190a41db949429076d5250a41bdd8542906f46150a41b798c42906dd6310a41eb508429067f65cca419f997329067d65cca41d794f329075d53cca41bd98732906f561cca419fd96329067e658ca419f596329076e528ca41db54a329067f654ca419f595329067c654ca41afd9132906bc644ca41d794d329075d534ca41db949329076d524ca419fd94329067e650ca419f59432906be640ca41af59032906bd65d0641cf59741906be60d0641bd597419077565d0641b798f50906dd63d4241bb98b50906ed62d4241ded42509067e63942419f58e509067e62942419f58a50907774194241b7d8d50906dc63542419fd8d509075f635424197d8d509067c6354241d718d509065c63542419fd89509067c6254241de540509067e62d4d419f58b535067e60d4d419f583535075f5394d41bbd8953506ec6254d41bed8153506f86054d41d754c535067e6214d419f588535067e6014d419f580535067e65d0d41d7d4e435075c5390d41bd98643506f56190d41d7d4d435075c5350d41bdd8543506f46150d419f994435067e63d49419f58f525067e60d49419f583525076f5294941b7d8d52506dc6354941bed8152506f86054941b798c52506dd6314941db548525067e6314941d798c525
  | 41 => 0xd32d7195434ca5c6550d32e7d91434cb9f5450d32d7951434cb5c5450d32e7151434cb1c5450d32f3d89434cadc6250d32f3189434cacc6250d32b7d85434cadc6050d329f994434cade6310d329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e65909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424ca7e6510932b798c424cadd6310932eb508424cbce43cc932f350f324cadf648c932b7592324cbcf528c932b7586324cade608c9329f993514ca7d64d4532d790f514cb5d43d45329f983514ca7d60d4532ddd46514cabf6454532af191514cafb6054532be181514cb7551145329f990514ca7d64145329f980514ca7d60145329f993504ca7d64d41329f987504ca7d61d4132ded42504cabf6454132af191504caf76154132bd185504cb7950141329f990504ca7d6414132d7d8c504cb5e4314132d750c504cb5e32141329f984504ca7d6114132bd987540caf561d50329f98f540cb5e63d50329f98b540cb6e62d50329f987540cb7661d50329d987540ca7d61d5032dd587540ca7561d50329f983540ca7d60d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3d54150329f990540cb3e64150329f98c540cb5e63150329798c540ca7e6215032db988540ca7e61150329f584540ca7e60150329f580540ca7e6494c329f592530ca7d65d0c329fd96430ca7d6590c32cf952430cb3d5490c32d794e430caee6290c32bb58a430ca7f6550c32d794d430ca7f6510c329f594430cb3e5410c32cf550430cb9d4310c32bb988430caed6210c329f992520ca7d64948329f597420ca7f65908329f596420cb3e5490832cf552420cade6390832b758e420ca7f65508329fd94420ca7e65108329f594420ca7c6510832cf950420cb3d5410832b798c420cadd6310832eb508420cb5f54cc832d7553320cade60cc832b758e320cb5e538c832bb58e320cb6e538c832f394e320ca7f654c832b7d95320cb5f654c83297d95320cb5f544c832d7551320cadf624c832d7949320cbcf424c832f3109320cadc604c832bbd95320cb6f654c8329bd95320caef634c832f3d8d320cb6e534c832f394d320cbcf434c832f310d320cabe64d4432af593510cb7751944329f992510ca7d64944329f982510ca7d60944329fd91510ca7c6454432d7cc9510cb5d32544329fd81510ca7c6054432dd544510cb7b50940329f992500ca7d6494032d718e500cb5f3294032d74ca500ca7e61940329f586500ca7f64540329f191500ca7f61540329f185500cabe6414032af590500caf66114032bd584500cb795014032d7d4e53d067e6294f419f58a53d067e6094f419f58253d067f6254f419f18953d067f
  | 42 => 0xf55054ccaf66115332bd58454ccb3e6415332d798c54ccb6d62153329f98454ccb7661153329d98454cca7d6115332dd58454cca7561153329f98054cca7d6015332cf95243ccb3d5490f32bb98a43ccaed6290f32d759643ccb5e5490f32e795243ccb9d5490f32d715243ccade6290f32f398a43ccbcd6290f32b758643ccade6090f32b7d9543ccb5f6550f32e7d9143ccb5e5450f32d715143ccadc6250f32b7d8543ccadc6050f32cf95043ccb3d5410f32bb98843ccaed6210f32cf95342ccb3d54d0b32b798f42ccadd63d0b32cf95142ccb3d5450b32b7d8d42ccadc6350b32b798c42ccadd6310b32eb50842ccb7751947329f99251cca7d64947329f98251cca7d60947329fd9151cca7c6454732d790d51ccb5d43547329fd8151cca7c6054732af99051ccabd6414732dd54451ccabe64d4332af59350ccaf661d4332bd58750ccb7b50943329f99250cca7d6494332d718e50ccb5e4394332d750e50cca7e61943329f58650cca7f64543329f19150cca7f61543329f18550ccb795014332d758f548cb6e62d52329f987548ca7d61d52329f983548ca7d60d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cf550548cb3e6415232d758c548cb6e62152329f984548ca7d61152329f980548ca7d6015232cf953438cb3d54d0e32bb98b438caed62d0e32cf951438cb3d5450e32bbd89438caec6250e32e750c438cb3e5490a32cf552428cade6390a32b758e428cb3e5410a32cf550428cade6310a32b758c428cbad4210a32b7597328cb5d65cca32d7d53328cb5d54cca32b7983328caed65cca32db597328cb7751946329f992518ca7d64946329f982518ca7d60946329fd91518ca7c6454632d7cc9518ca7f60546329f181518cb755114632ded42508ca7e64942329f592508cb5f6394232d7cca508ca7e61942329f586508ca7f64542329f191508ca7f61542329f185508cb7950142329f987544ca7d61d51329f983544ca7d60d5132cfd52544ca7e64951329f58e544cb5d63951329f58a544cb6d62951329f986544ca7d61951329f982544ca7d6095132bdd85544caf46155132bed81544caf86055132cfd91544ca7f6355132d7d8d544ca7f6255132dbd89544ca7f6155132ddd85544ca7761551329f185544cb7461551329d185544ca7f6055132ded81544ca7b60551329f181544cb7860551329e181544ca7e6515132cf550544cb3e6415132d758c544ca7e61151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d329f996434cade6590d32d7996434cadd6490d32d7952434cb5c5490d32b798a434cadd6190d32b7982434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250
  | 43 => 0x5050a7d61d4142ded425050adf6354142b718d5050af76154142bd1855050b7950141429f98c5050a7d6314142dbd085050b3e42141429f9845050a7d6114142d7d4e5310a7e6194c429f5865310a7e6094c429f5825310ade6094c42d71925310b5e6294c42d718a5310b5f6194c42d79865310b5d6194c42d71865310b5f6094c42d79825310a5e6094c42d75825310b5c6094c429fd855310a7c6154c429fd815310a7c6054c42d7d955310adc6054c42d79915310b5e6254c42d71895310b5c4254c42d7d855310b5e6154c42d75855310b5c6154c42d7d815310b5e6054c42d75815310b5c6054c42971815310ade6314c42d754c5310b5e53d0c42d754f4310aee62d0c42bb58b4310a7d6590c42d754e4310a7f6550c42d794d4310b5e5310c42d754c4310b9d4310c42bb9884310aed6210c42d794f4210b5d53d0842e794f4210b9d53d0842af9834210abd6490842cf9524210b5e5390842d754e4210aed6490842ab5924210b6e5490842eb9524210bce5390842f354e4210aee60908429fd954210b5e5350842d754d4210abf6550842cfd954210a3f6550842e794d4210b9d5350842afd894210b3e5250842af1814210aef6550842dbd954210a6f6550842bbd914210baf6450842db9514210bae5450842f394d4210bcd5350842ebd0d4210bae4350842eb50d4210bac4350842bb1814210baf6550842abd954210b2f6550842ebd8d4210bae6350842eb58d4210bac6350842ebd4d4210bae5350842e394d4210bad5350842e354d4210bac5350842ebd854210bae6150842eb5854210bac6150842ebd814210bae6050842eb5814210bac6050842ab1814210ade63d4442b758f5110b5e53d4442d754f5110bad42d4442d794e5110b5d5394442eb50a5110b7751944429f98e5110a7d63944429f9825110a7d6094442d794d5110b5d5354442eb5095110a7f63544429f18d5110a7f60544429f1815110ade6314442b758c5110b5e5314442d754c5110bad4214442dd5445110afa6014442be5805110ade63d4042b758f5010b5e53d4042d754f5010bad42d4042d794e5010b5d5394042eb50a5010b7b5094042d7d8e5010a7e63940429f58e5010b5c63940429f9865010a7d6194042b7d8d5010adc6354042d794d5010b5d5354042eb5095010af76154042bd1855010a7f6354042d7d8d5010a5f63540429f18d5010b5c63540429718d5010a7f6154042ddd855010a7761540429f1855010b7461540429d1855010ade6314042b758c5010b5e5314042d754c5010bad4214042bd9845010af56114042de5405010b5e63d5332db58b54cca7e61d53329f58754cca7e60d53329f58354ccb3f5495332d798e54cca7e61953329f58654cca7e60953329f58254ccb3f64553329fd8554cca7c61553329fd8154cca7c6055332c
  | 44 => 0xe5f6550c43b7d914310f9f6450c43d79514310f9e5450c43b71814310ef661d4843bd5875210f6f52948439f9865210e7d61948439f9825210e7d6094843d790d5210f5d43548439fd855210e7c61548439fd815210e7c6054843db5485210eee62d4443bb58b5110f7751944439f98a5110e7d62944439f9825110e7d6094443d790d5110f5d43544439fd895110e7c62544439fd815110e7c6054443dd5445110f7b5094043d718e5010f5e4394043d750e5010e7e62940439f58a5010e7e61940439f5865010e7f62540439f1895010e7f61540439f1855010eee6214043bb5885010ef66114043bd5845010f795014043d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42bd98453d0af56114f42d794f43d0b5d53d0f42bb98b43d0aed62d0f42d794c43d0b5d5310f42bb98843d0aed6210f42ddd4651d0a7e63947429f58e51d0a7e60947429f58251d0a7f63547429f18d51d0a7f60547429f18151d0ade6314742b758c51d0b755114742b798f50d0add63d4342bd98750d0af561d4342ded4250d0a7e63943429f58e50d0a7e61943429f58650d0adf6354342b718d50d0a7f6354342d7d8d50d0a5f63543429f18d50d0b5c63543429718d50d0a7f61543429f18550d0b795014342d7d4e5390a7e6194e429f5865390a7e6094e429f5825390a7f6154e429f1855390a7f6054e429f1815390b5d5314e42bd9845390af56114e42d794e4390b5d5390e42bb98a4390aed6290e42d794d4390b5d5350e42bbd894390aec6250e42e750c4390abd65d0a42cf5974290abe60d0a42bb5974290b6d65d0a42ddd465190a7e63946429f58e5190a7e60946429f5825190a7f63546429f18d5190a7f60546429f1815190ade6314642b758c5190b755114642b798f5090add63d4242bd9875090af561d4242ded425090a7e63942429f58e5090b6f42942429f9865090a7d6194242b7d8d5090adc63542429fd8d5090b5f635424297d8d5090a7c6354242d718d5090a5c63542429fd855090a7c6154242de5405090a7e61d4d429f5875350a7e60d4d429f5835350b5f5394d42bdd855350af46154d42bed815350af86054d42d754c5350a7e6114d429f5845350a7e6014d429f5805350a7e65d0d42d7d4e4350b5c5390d42bb98a4350aed6290d42d7d4d4350b5c5350d42bbd894350aec6250d429f9944350baf52909429f98f5150a7d63d45429f9835150a7d60d4542ddd465150adf6354542b718d5150afb6054542be1815150ade6314542b758c5150b7551145429f98c5150b5e63145429798c5150a7d6314542d758c5150a5d63145429f9805150a7d6014542b798f5050add63d41429f98f5050b5e63d41429798f5050a7d63d4142d758f5050a5d63d41429f987
  | 45 => 0x10008000000c004000800700000060000000001400400000000004007001800100000070000000002800700100080010001000c0090004005000400100040000004001000000000080000000002000c0010000007008800100000040000000000c0070004000000c00e000c000001400100100000004000005000000240000000005000000000040060004000000c008000800800000110008000000c00d0018000000400200040030000004000400000100010008007000c000001000400000290010000000c000000400c0000007000000100000020010003000000100040010000003003400000040000004004000000900100000004003001c00400180070004004000c0020018000000000c0008002001400100000040060014001c00b0000001004401200240010010000001400400180000000000000400000080040000001000000000000000000000000000200000010048000000c0050008000001400f0008008001b6f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0f7b5094343d7d8e50d0e7e62943439f58a50d0e7e61943439f58650d0e7f62543439f18950d0e7f61543439f18550d0f795014343af5974390f3d65d0e43b75974390f5d65d0e43b758b4390edd61d0e43b79834390f6f5294a439f9865290e7d6194a439f9825290e7d6094a439fd855290e7c6154a439fd815290e7c6054a43db5485290ef66114a43bd5845290f7751946439f98a5190e7d62946439f9825190e7d60946439fd895190e7c62546439fd815190e7c6054643bb9885190eed6214643dd5445190eee62d4243bb58b5090ef661d4243bd5875090f7b5094243d718e5090f5f43942439f98a5090e7d62942439f9865090e7d61942439fd895090e7c62542439fd855090e7c6154243de5405090edd62d0d43b75874350ede60d0d43e7d4e4350e7e61d49439f5875250e7e60d49439f5835250f6f5294943bdd855250ef46154943bed815250ef86054943db5485250e7e61149439f5845250e7e60149439f5805250e7e62d45439f58b5150e7e60d45439f5835150f775194543bbd895150eec6254543bed815150ef86054543dd5445150e7e62145439f5885150e7e60145439f5805150e7e62d41439f58b5050e7e61d41439f5875050f7b5094143bbd895050eec6254143bdd855050ef46154143de5405050f5f6314143d7d0c5050e7e62141439f5885050e7e61141439f5845050ebd6490c43cf9524310edd6490c43d79524310f9e5490c43b79824310e7f6550c43afd954310f3f6550c438fd954310ebf6350c43cf94d4310edf6550c43d7d954310
  | 46 => 0x80000044004000c0020010003002c00000000020004002000c0130000005000000500040020008000000c000002c0000008002000800300000040000002000000c0060003000000a000802200140040024004000400c000000100080030000000001400100040000004001001000200000000000001000000300040000004001000000b0010000000000c00080030050000002000600500000000000001000200000000000007001000000000000008000000000000140000000003000000000180020000007001c00100380000020000000400000000010014003000000100140010044004004c0020010006000000100000000004002001800500200070014001000c0030014001001c001001800800200000000000001c00100000110000009000400000200000018000003400100000020000000000400000000000008003001c0000000000000000b000c00000000000000004001c011000c0010000005001c011000400000040000000000009000000140000004000000000100080040010000002400600400020000007000400200000080004004000800000100010000000000400400040020000002000400100240000000006003c006000c001000400c00040010030007005800000140000000000000c001000000000000010000004000c0000000000002800000280030008001000400200040000020001000400000000010000003000400200200060004001000000100000000010001000000000180040004000005000d000400100000020000000000400e001000000180000000003003800100000000004003000c0080008000000c000000c0010008006000800300080010000001000400100040080000000000000b0018008000c0010004001008c0030008005000000d0000000004c0110004007000c001000000200140020024002001000d0000004001800000000000000003000000600180130004010001000000180000014005000c0050000000001000100040070028000003c00300000030004000002400f000400500600000004000001400800000040004003001000100000030098009004c00500340000010003000c004000400200540000014000002800a00340070000000000400e000000300380000000000000c01b00000060004000000c004000c005000c00a0000003000400600080000000000002000000140040000006002000100000020000000001000000080000014000004c001000000c000400000280000010004000000200240020010000002000000180080000009000c000000400200000250000002001c000000000100040000028002000400000100110008000000c001000c0000004000000800000040080014000000c0000014004000401500000040014008000000100280010004003000400
  | 47 => 0x10000006000000400000000000004000800300000020004000000c0100014002000000e00000060000000000c00000100030000003000400000080000000000000000300080000000001000000000300000004001000c0000000016000400400000010010003000400c00080000000001000000e00100070000006001c00b0000000003800200000000038006000400e000c0000008001002401100040010004011003800000000010000001000800300240030008000000000700000000034000000000100080000000003000000a006c0000000006000400000180020000000000c00100200030008005006c00200040000000005000400000080010000000001400000100000004005002c0000008002001000200040000000011000c0000004003002400900400020024005000000500100000008010000000000000000004001002000000300030008000000c00100000000000008001c0080000000000000200040000018012000000b0000000000800e00180080004006000400000200010010004000400a00000090008000000400200000010000002000000d0010009001c0070010002000c00000100010018008001400400000010000000005400100080010014005003400000140050000001000c00000000080000005000000100040030000008000800000040020028000000c00100000010000001000c0000000000000c00d0000002001c0030024000000400500040000028013000000000040000008000002400400180070000002000400000000000000000000400300040040004002000c0000000000000400600040000000000001000000380040000007000000800000000094000000c00000740050000000000400900200010004000000400000000010004000000400000040040028002000000c0004001000000b000400100000010004001000000100040170004000000000a00100020004000000c0010000001000c0000004003000000000200030000006000800000000010004006002800100000010008001000c000002800000000000000005005000c0030012003800000080000004004000000000040020018002000c00000000020018002000800e001400300040000004010000800e004c00300080000020003003c000000c0010000001000c00100000000000000005c003000000200000000044000000000400000010008000000400200040090000000000000000000000000004001400200400080008004000000a0000006000400000080000008000000000400040000008000000400600180000000005000000000000010008000000000800100010000003000c001001400400000010008005000400300100020000004002802b0028004000800200280060000003000000000040000000000000800300
  | 48 => 0x2c00200000010018000000000500100010008000000400000080090008000003400000000000008000000400000040000004000001c009002400f00040050024002002c00200040050020009000000000080040044001000400200240010000001000800000100050008000000c0000030004001c002000400900000000008000000000000040020000000002000000100030004002002c0000024000000000100680030018000000c0010024001001c001001000400000050014004000c000002400100040080000000000000b000000800000020004002000400000040000004002000000400340000000008000400200240000004000000400200000050018002000c00e00140000008001003c00100200040008002000400600000020004001000000b0000000000000600280030008006005400000040010000003003000500000050030008000400200140160004005000800d000000000000030008000000800100280020050000004c00000000030008003001800100000010008000002c0000000001001401000080040004006000800100100030008001000800d00000070004001000000e000400000380030000000000400400000050008000000000900140030008000004800000040020000001000c0000000000001800000000000004000000400a0008005000000000180010000003007400200040010000000000400200000000008003002400400000000000004000c00100040020014000000000000180000000005000800000000000000007000000100280000000000000800000080000010003001400300080000000005000400a0000004000000000040030000007001c002003400000000000000001005400200000010000000000c0040004001000400500300000000003005c000000000300300050024003000000000000070004000000000100040040000000000c002001800300140000000000000c00700000020000003000c02300000050000001001000000080000010002001c00200040000008000000c0000000005000c000009c003000000400040030008001002400000000020004004001400200000000018002000c00e000c0070000000000c00500040000010001000400000040000000000000000700000030004000000000b001000000000000004003000400000000050000003000000b000400000000020014000000000d00040000020005002000400100010000000000000000000150000001001400d000000400080050000001004400e0000006000c00d000c0020000001000000200100000030000002000800000020000007000000000040090008002000000a0000000000000000000150000001000c001001c0000004009001000000600000000000003800000240010000004000000000140
  | 49 => 0x4010001800600000020018002004c00100140000000004000c00000080020000001000400b0004000000800300080000008001000800200000000054001001400900080120008001000c00000240300000000001000000000010008000003c001000000000200010000003000400100000000000000000400500000000010000000c001001000000280020004004000000300000000024001000c0000000000000800500040040068000000000e000000b0010000001400300000010000000000000600140000004000003800900180020000004000400100000000000000000000700080000004001000000900000040024000001000400000000000000004c003000c000005400200080020000001000000200000010014000002c002000c00100000040000001000000100140170014003000400100000010004000001000600540000000002000800000040000004007001400400180010014001000c0010000006001800200000010008002000c0010018000000c000001c00000080000004006002000100140000014006000000000040030000001000000900200000000000000000200000000000001000c000000000300000000004005002c00000000000008001003401b00040030004004003c00000100040048001002400000000010040001003c00c000c00000240000000001000c00200040000004003003c00000040000004000001800000040020000001000400100200030014021000c00700080060000002003400000180020000002000000000080020000005001000200040000000004000c00000080000008000001400000080010028000000000b0018002000c0230008000000800300000020000000003000000140010000003000400f0020003003c00000100030018000000000000000060004009001400200100000000000001c0050048000000c004000400000080010000000005c00000000000000007001000100100000030007001401f0000002000800700040010000003003c0070000001001c005000c002005c000002000f0008003000000300000010004000000c0090000000001000100000000034003000c0020008002000000100000010010000001400300080010008000000c00a0008004000c002000400b0000001001000a00000000000000000400000040000000002004800000000080030001000000000000040000000002c0030000001001000100000060000002002000700040100008003000000100040120000009000000100000020008002000400000180180000000000c000000000000080000010002003800000080020008003001800000000000020001000000600000120048004000c0000068006000800400180000000000000401c008800200040010004002000400200040000
  | 50 => 0x800a00000010000000000000200000000000004000400900100010000001000000000200010000000000000300000000028001000c00d000000100500050000003000c003001c000000800300040010028000001c001002c001000000000040000000000003c00000000020018000000c000000800400080030000000000c000000000000000000000001000800000000060000000000000100540020020000001c004002000100040180000000000400200040040000001000400100000040008001001800400280020000001001000000000020010004000001f0018002001c008002000100100010000005001801c0000001000400c000800400040010014000002000200080010004005000000000140000000000000000000040090038001001400800080090000002000400000000000008011002c0010010001002c006000000100000010004000000800000100020020000004000200040000000001000000400000030018000005800700040010024001005000700000030000005000c00000000070000003002400000000000018000001000000200010000001000000000000020010000001800c006c000002400100000020024001000000f00240000008006000400e000800000080060014007000400800140010010006002400000000020008002001c00000180050000002000000600040020000001002c007000400f00040000028011003400000040020000002000400500000000004000001000000000050000004000c00000080010000006000800500000050054005001800500000000000000000000100080030028001000c0010014001000000d0000001000800500680000000004001800400000000000000001c00300080030014006000c00700000050000000000c0000004000000c001001001f0034003000c0050000000003800500000010000002000000700000030000009000800000140020000001000c001001c00400000090000003000800000040000008001003c008000000000040020018005001400000000000014001000c002000000000040000020001000400c000000000040000014000003c006003800100000020000002000800d00000130020002000400000140000000001000000200080000004000000000100140020000002000c00200000060008000002400200000030014006000c0010000000000400000000020018002001c000003400100000020010003000000000000060008000000800600000060000005000000f0024002003401a00080010014007000000400000030000004000000100200000000003000c000000000900100000010016002400000080010000003000000500300010008001000c002000400200000010024000004c00000000000000000000000300180010000
  | 51 => 0x3a3279c806b01a2262037c02dd8db8000021191f20000297874f094f062049404275337813b4b309601072a0e100008524496977400000000000000000004dbc000000008ec00000c3000003965c3cf85836e000000540000f3700000000870000000000348d510215371a00000389d36098026ed0588000000032dc000000000006c785979f0f00005c70e3514401182427000003410000236c0000c5100009664c939214283a47d8f2282252f186f1c47591eb1580700c0001fd2056407587de00004b22763103d19d3000000003108000432a820900a81e700000000000000000000000edc80003ff092e82d900000000000116110b204fe8848000000000000000f4aa1240000000115b91e608de12a4000188c00000000000243941a200d800000000000000056da1572d26000109500000000000000000000000632113300003e3c8fa0ee20671000000008988000192800000000b2a0000975000003d5000e00010e3000000000000d7d9f92000000007351a7200000000000030a1344000000013a40000959c00000002ff488a800000000f8c30049731ced1768340518823df11107e40ab20000347000004f413b5000080140001f4c00000000329800000007e78e70094600004e588ad106944f243ac000191800000000000000000004cf8000000000000fd8df89389000068940000000068a508931a1b18445c669d1da08602eba00003df92f8306400002c980d70000596078a06892afc7b989930a00000000013250dd5169c1e991648000311492750f0255e492c2294337800000000000ef480002fd8000049886442e1c7af9129123e00000000afa8000040c51e4b3ca3490000000000006352ca84c58000000047d60000000000000004fd46c8040901465314000000000000000000237a00000000000000011b25d1800013420000000000000000032405c5d700000000000128fa514000020100000000390451e00c400000000655824ca067418079e8d440da539608fecab413a812d60c1d0718a3e3eec90c831985180d9a1de8b7e95a53c2600000000002000000000040000010000000000700140010020002001000200100000000002000c0020000001000c0010014000002000200000000018013000c0030000002001400b0020001002800100100020014009000000400000080000002000c000000000000000020080003001000300140000004000005c003000800e00000010000014001800c0000000001400000200020000000000000900100070000006000400f000400300000030008002002c000000000d00040010004000000000200040040000002002000100000040000004000401a00000000008003000800400040050000003001c0040014000000400000140040018000002c00a000800000100020018006
  | 52 => 0xab7800000000000e4c00000000220000000000000095c71d00000000849cee31c50270e038800000000108939c39680003ecc03386521c0500003338e3b0c1c11dc00001621430000000000000000000018400001a6335b000a40000000000009e8abe96940000000000003a41fbe00000000000000085cc0000000000038e4b02000042ea3b4438480000000000068e1ad30000264c00000000000000000000001270514491689e4241a8d7476e800000002834e9c10f0000000009ea9d150000000097d013f4ccc57e516e94fd419c16bcecd9ce2045219f117980001fa664c00001c2b247622740f29ebc16e8000023180000000000000005020000324c000135448e2137024d103a000061d0000160100000000f24000004782b5000005c23890883c21b94384a800000abb1d1806ae000093101af4ad62d588dfa3033a4e9230be811372e6a06e4be586cb0000360915d800000008224de211130000000000022674a6259bc35c03650e4834f065880000000636c00010912cb20000000000021846848ff0000019e80000000000000004e7000011aa3386000000020db00006e202620c9531a00000b4d8000000000000000000256c834c6619022000000003e90000371620a51fea54e1b2e34d0f39800001d48420cbc0000331a5fcd12d000000007430000000037c8000003e0000080c00000000469160a54242ac8000000083accad0abe1b5600006749614000071d000000000000000000001e800000000000000014de00011a9901f2dee009d2df099a000000004819a9e419611f800000001e18867c2f20fff2f761b050a9000009b4444092986c3127660585d9841a44aa000125ca1a02d3e67e843e216f3e5e6608c84800000000955174a38c075800007be0de6000099590a51b66321854000001d5d00006a1807a8c78000000010ec921300003bd8000000019a672a000018cc07767b7c2431b0d21105a847408c0e0000000125899c70000443c000000041943f6ca2f08b146240000ac98000431410bd1b1a45b2bc822a40000a9c27a88b70000211c4ba2783c14a035200008f3866e8c3744483d0c000017400000d549bb8000000000000000000283200012688838430c7a04000256800005b44f9486e8420c96a50f99c5c3f3a01a03aa0743416e0000f2b0000000017e400014fb090054c478218ca34640000408800000006db80000000194a2eb4200800000000000dba875e142c000000009e500000000000000028843bec000129300006538b631f6907ba000000000002d68146825a04a605c24e5c000056a00000000806800023040000b5f171909b2982061418030cd42740a588a5a01de00000001f2807824a38000262000a26dec7698f271e34027c8651cde0e22147d12799c03efc0028000133d000000000001a19
  | 53 => 0xf00008dc47a51e261506786cd41800000000000fd683920000000000000000000442d0b2983514e872f4000000000000000000142d00005880d2d89a6314e423c992a56d00004954000000038da19f89d19e4e1df4000060c000000002620000217e00000c184e6000002bc35dc000000032b0932000000000000000000000001c2a453c000145030007c1103e0000373000006f0921c0000000068e8aad000000000000000000038d40001c89196a0be400000003406000116400003cb60000aff0000107c0000000211e0000000000016a300003158b2f954524180000000053c21720000ae285da19d0000007280021eaa0000951800005fe00009388000000016dcc45800001fe878c15a223c09ee5bec7b7000029da000005ba6150c5a64a40000ca90000000078f1d673e9200000000bb514540000000000000000000000088f0ec030b88d5925030ee6304ee90000000000005c5000000009824948162c260496ac8af800000000000ef20ebb000000006bf831401e0000036d10dc000092641c780001a2812205c71e66000065000000f6000002c901dea1540422961c1d580004cdc21442978eae15ec24e4a270000487a0368000023f19a80000e8820d8152c0000000000000000000000126c0000000000008190a5400011aa053e00004d1400008cf000000000001e8c29a00000cc180000000685cc478baf1378000001724d53a2c29ac109a4b630ba409887920cc4c32000017b1808115c27790191785490891ace65120b05a67b10a5b1e9f3062595c00012594ce08ad8e8680002b1e000000000003bb44a1108796d43de800004fa00004ba65faca7700001c420e711d29d6900005c186a40000000000003ba245606442108b7b1b39493e6c4c00013af000000006929fe949f802a4c77857028ac6cd40000c1b2bca7b3c2f9a38f3090000117c8000273a000109e8000000061c44e305920000000000000001e60000000000000000000000006bd00000000165888720480f1872600001616000000000000000932448c000041d40000de50000495e000031f000000000000fb91bb71a5e0000e3020e60000318c31792e84512389c0e69625326404c466080001666000000022e50000000041d00000b960000961080e000000006f20000270800000000dc60000000000000002ef80f781f08000000000f4ab5809d258e706075a80000000396893a139e2e161894eb797d2231242240b20fbe2c2496a006c97900000740000000000000000088c8000000000007e307390000000000002412e2a077400000001a6200008c98be4000000000001084000045e000019f71896000000010f719ce0000fd804bb2c8e5778efc03990000000053991b700004ed000000000afc000000000000244351c3dc00004a7a642920682b003ee3cd
  | 54 => 0x18f20a10000779cc548000274e0000000000004f0000000000000000000000006e40000000050f8000021807ac533067841f4000032b07ba31960000b8000000cbe3d047db023749524a04f0883d118f807e043d92b80da20f0c9469bf81cec2cb8f8c8d7a32c200013108000000073100000dda249090105930000000000000001fda000006f8d6100000000000000000000000000123f0000000000000000a9b000000000000000000043d93130f48471600000000b571b0a6d201e500001a1e5e240002259203815000000289137c22808300ae5010000004f024bb002600011218000000020b41f800082410447408b983f469e176c00013b21cfe0000000094f266c64e0b30000042ba0000000000000000000bff00003c1002480000000000043e4d5880004224110400000000000000007b000000002e34d66847d000035e000015c0044200000001fef41fe255c530965d00002c1808310b7127a36040000950000000005b7842a38261a7ca12863b00000000000090215726df90db10a838985d300001a6b337c86a85c313041aa400012db0000000045d0aca8000000014701ee0000018252605c99760000008c8a729475392c5ea851b800049c000004b180000000251129516fa081a758c00019870000000063b800019aa7d48024913f107802ad0fd868416801a5c00000000000000000000002bda4e180000000000000000a11f5e41741938b088000039c00009c2876a0000000000015830000000000000000000000015f00003dc400001f1800000004604195028640c600000000000412a222d19a85b0000000000000000000080d92c5072800006640000000000006825236217c0e0a149800000961fca8b5cc6b090f17cc7e943a486d241c081141f70308000095a44ea172a000059380319abc10540000aeb80003ec20000000126d00001014bc1a236395282c0b8088712b1a00000000000309400000000000000067d4fe38006000088141fa8000310a00005b9131d00000000c5e800038a63b580002539000090147340e7745187b1cc1b83682848925c15300001dca99a05aa142716bc91fc129800023e28d64e741bec37c60a60b0e84a1090a7f6c9ad008704f83d60006109530de74c40000a7722820c94d5424724800524c05e0f53000000000000e3d00000000000000000000000d1b00000000000118780002c5e5d1cdfc800009926978c3e0000425e00008de9cd1000044985189bb0261800000000000060400010358000040600010b41a52056e6724a1b82bb06fe1a50000045b48d462fc42916f205020000d0a23d834505ba0f6a110534e800006a8846515502bac000090432580000e7b977a26e807fcff6145309ca54d0dc90000000026389d81cb900006a8ce4080001ccc0000eab00002e2000008430a4
  | 55 => 0x2544000053280002b6055c0c56963b3dfa5900000178b02286ef80000a1b0000000012f00004036000000019ba0000000008408f40d18220c00000003326643442222b400002fb531c800000001ebd1d8a63707f898a0a86149122a85b5cef800000000393400011c6000051ac00000001c2c7320423848736160588c070353000083d47cfa30425ee037479e09b53ec85c1489b0dbd25662b141a81a0b03e812044ce9270199432ec000023d00001ea52732337453262b12ab85684afc24e852519b426ec4f580e61d25346a000000000001e5c49e8000000003c000000e8092140c202807f825ce000053e8227034347de7cc0000218436da15d512f949931860000b3a1aa6287e782cdaa10d2023a824ceeba35727980000000194520d0297c00012b9000075b51cc1ffc00004434df01ba31d780000de11bf6000004c01cc13e145643c20e1e000000005475267868a18d8473424122df2c660448aaa800032365ca000004a200000000a6c800015ba31248f008a42f66559419600003ffe63c4000112b3542000109900000000000022300002fce91e82f401de263220703b3024b068003d036b045805866170ca5156906b818889570d3d3daa284400022564a82030800005fc235a59487d3045c495000001b38000003859846ae80000000000000000000000000000000000000000025180001702064cfe80bd30000712c0000756457273e060992dd1ce60000000259a25287ce04701c17000000012c093a22f98000000000000000000000000001646156027720fb232a3e74f3e8f1d3b421bf82dc8037130845348b2000000000000742800013946b38c1c80000ec410445d324fd0000565841880000f5c55680000d3a431e2cf4b068aa400008f54c78023b02967d540001b2e1ee600000000ef745fa60482e211882ada1fe81e5800003c46524a6ba3501ea08ef4cca0fe0000000005d21f98386421a05f787200da86d343f099f11f6851991ef0d62000000005130000264e2b18d6609ee033e23cc62a0c800a0c871ca0a8ef309b641c102e041000000000df522070804416c000000000000000e778000000098d848405fb131440580001dee00007f5c0002427000001bc00000002e3c00004b98000482e000043c0000000022fc000000000008750ce5921b42c463a11f4800034e08790bd29eef000028ac0001ad0000033ed21280001aec94486451752279c1fc4000000000000000c51982f00205f680000a7e00005d7ced1000000007ee4ab52076000000005d39eab3612000000000003ec441180000e43000068f0e090000000065a400001853bee00012680000418467906e008c62fc6319c1d99721130448a8bb508f82f0c80b0000222700002e88e1b96d043f26bf468700002d4c5d1426a1ede18761a9c8dc8000016600
  | 56 => 0x260000000000011bb80003f68000084a0591368688ad02c000000001d90df98ab5000000000001a370e2800000001a8c4be01be8ff70000249a7d608a2170a4b381f2800000d50000529435522e229c4800800000003e6a000093f93e5086000012be954e12be6ab80001bdf241255840000000000000009e38000000000000000470000000000000300000064f8aed80002d2200006ef175c00000ad4492a209099c358c00019440e9c66a4c0a85694b6a10f51f0972337065edc8889ac3442a9724dab955731803428e888b8c361400000000000410271588f6800011902970ad6800000007fa0c6e17551cc00000000000020f00000000197e356000000000000266a0000b9702ba394600001c81d6e050068780000000446640c43e69d472ece6474e9a92330000000000004b8094e00000000b4500000000b7c800000000000716a669025c00000001a6700007e54000140c2718019ca56981c000000007b3991140ba488101086cc061a000080d24a125122a1d0020c350000000017e0000245c5f84d76061245d867280000f782a5a27005be80003df872c400000001bd2559817b882e198c77b400017d833666bb45a613c20a0e00008f10e9a06a2000087c0000000000000000bcb000000000000126000000009ad829d4c6627092a60c9749d04bfcc580e8733428d982449c514744040c36b81a10a2852244ae1b4b00404fd0924971713667f08cd1a51146706668a2520f3230e8c94dce17ce1f8e51ed04a143516ea089c03ea4da2192583c97e020e0b52876c67e966912502670000000010ca0dcc1d904320000000000002fb134a0655084800000000bf85810181000027e8f468000284c00003eb000000000acc00015273b3a000041ba3a3070e3a5000000000cdc30e40000000142e87f062f042003a293bc20f164d2f94951ceca0eb3298400005590ad7399644240000a24000051a8b718000100c14dc00009ec0000000087a9b41000000000000000000061ec000000028140000bdca647000049cc35d09a900000e3800000000d8c7a74e0e80003dea0a8c824266d0000641000019021ae05bd4f0f80000e5460d8cde8d2800000000000000000000000cefa00d000029f404490d92bce69280001aaa0fb094cc9dc1f78053443408740bea3db48ac11770eaa35ca74889dd1711159a80fc000031929748405171a447170e0e691931cad4bc08468591000025ae0000000000000000bd40000000068c00000000c9a452c80d022b0bc900001cf4a438000000037dccb122a63df61ff81119c0d1ab6000000024c502480000000000049264738000000032d400008fa8000000000000000a0500000b1c0001a6d000075700001ae2279a4b9028a91bc000000006b68c4d0bc00000daf8000000066909bc19220d5097352f100
  | 57 => 0x646631912a00001cc60e9529f9c270000879c3518000000000001be0d4e2e7e1b6465905c900000000876a0980000336429880002f268ee0964996e110265c40000000000092c06e681dc00005d4c000015c37e879bd12600000d6098704100f4c254a41901d494a3000014b87b5011b000000002a91be100006bc84781ce33e841838f2e952c00007f84000167518a00000000136e00002f3400010d40000588800009af2804690c00025460c701f7000019b536ec257910c800000002024a5a029f09165898d9f8577269e7804efc800000000000db00000000000000000000000000000000000485c09612ce9e47000061c80faa216259e00003e4976d26f413c40000fb10000000000000004bae0000e639d9c0a2c0000000244b265a34a87ac8c7f1be600002a502d146fe4dfc0001f091f26060c85a059a2c9e6f044f099661a5621741198dfa338c252898e165a38821f09062a0592e06137513b95924bf45174c3b1e5800007e0884d9485064039b0fd30acb4b36428c00001b305ac63cc00000001b820000000000000004fe4000131a00000514000000000000000f13875133f672ac3840000000000012310af01ebc000119697e620606100fa891df07e684fc8b89e6c0000973d2ad9a3130d444e0912906d49ac75c4d7c0000000004c800020bb00000000b2889160000000090200000000566c7c8a6324bf255611df835425dc3aac2e0a20d16ce4584000005a159403308eb8000000000012410000000071fc000000000005a54fc5000002160000e3c86bc1b528a90290930b29e40558ec00c522a2a1c288a1a04000005d340001adf3eca00000000000000000000000f260000000000000000e306d44cdf800000005278f4c010f00001d1800000000000000000000002f560df516315a740d40000ae400001cdc8a540000000000090d43de082c2f42000070d0fb7452800000000000000000009fb00000000869c0000426347c0000bc000003b9630b00000000009066a8f1d215e00005628cf48000000094e001a22a30d1e0000000000017040548e1600001cf06bcc92f80244500000105a8bfc4b4800000002629046220580b30ee228526654f4e1e17211656d000023702ff00000fcf82bc00003c0076a8000000000005a5828231225cdc69900000000000000016343ba800000001bfa1cd60000beb8000000000008bc87c82a08000000000d34c8a92ac4650000000034e40000ea32ff61610b7f938f28e64a0d1fd22023acc60b8f150ffc0d4800008f1862b00000000c4c20744b589130ae195460000000132f000049c816806968cc816d83e600000d7e355e000085d80000000526d166015800000000055000000007cc8b07017b15fc607409e889440ac380c2d29c9a20ba1e74bbb86ca384c0000000000011ae0
  | 58 => 0xa650d080000c480ee41db90202a6609984f19b5d31760000db487f51efa0000bf0000045b200012d999da1df024f042190001bea4458400000000000728f1701c200005a300000000000034080001d4a00007c60000041202740000000000027ee000051e14d11ce4000108f9e7526664d10f16800006880000f049b89294056505a697fd06d88784b8c18ed00008d94ddd9af70000489c0000000379800000000000380042d8545048e26242ff4ba885bf4a68888800024490bec9364000165c18941a0c14a819a1d685f7d165020d375e00004809a9a2f6a000000026610000000117d25420b321b380001ee537fe00000000000441c00000000000000000000000000447406652b3000004405310bed90633e1a2158cc60a530a4a38e00000fb22d02000026680004bd222a0000262e33c4000019400000000000000003fb000000040000000376c00008a000001c580000c07800028060000bc889a100000000e1a8000000036f914e00000000000000000002e3400010c9800000007af414880df351c00000000cbe000000007b300000000000058c800000006d8c00000000000000045c00000000000037a88f600000000f658aaf0000000000000000000000000000001ac865c0000000000000810229a3da34487acc24d9a64143c7438ec308b2294e859c03080004bf00000eff85dd089800980000fab3ca662c4efb000032a45cd0f3c178a329a35084b7a43b40aa5e0820e800000005630000000000001ec071890e401b80b807c1810d0000000000007e40a8600003cd00002a480000000000049c46e9c158983e1c6e0000e10834210d6000053d13ec437a7a80ad486363e2044d0bda1a65039e59f467694ac28202be450098cf00305860af510db48e642cc20b186e122e4c9022201ab477481946200b8b2cfe3a2d0ce000044c801100000000117a00003e8834a36c200008e4202b00006f5800016cf0000340c00013ff00003764000000000000000000000000005d2d0a80e11339a0000000000000000000325000000000000000018b1d7a6e55018a5bb00000000000000037d60000000000000000000a6980000000000000000000df000008c7199c096c5ea532d09612d348050b481052249882d0aa122f613aa8b2c5e717793cb80000e1d1c9d000051700001db7000000013219598312a7468a898e46000001380001d3f3aa000000000000000000010208000000038ac000000000000410d7300000000000086214e1248c8324000078b0000000000000000000000002080002e1203cc0000e0a4c582e780000000439659400000bc20000000091782d415fe000070d9bef000000010ac8000075411c8dcb800000000c14a95950f44362da4ad09482156612708fb90c100003e8c24b166e0a8e3e90734905631be00000000
  | 59 => 0x1151000045dd2f61e8007fa000052c0000323e6d14000100e273461fc7d500000e8800011d706bb2e7c1dcc23c8dbb077e44f476d05f42d807994f25a3740000315c51d0bc840888218f6b00000daa0000000000017c42d3c000000000006a402460c4245a800007b18f22320c2a60fd5800000000000dbe8000000000011f718e51510761400021b728fc29791a000002d0c689800013c000001b401c5810000000000000196c1ff200000001fdd3b347c8c0000ebe1c1c0000a6704ae1372000000000000000000059c0492003426c4e6902541a7e99491e680001d887c5cfc680000000000008b00000000358000000000dfa00012ec00000000000000000000000000112d800000000000000000000001924f3f09fe3dd430cc000000013204bace83800009aa8a6d2ff044a0c18280c8db0000213211b80000a9f26580001296800033e80000817000000001d842c10000000090700002552086a3830604000010c200000000000000010b8000000000002468ee800000000811d03f0f9b294200000000000399e69587929d7d01146dd0c761cac4046000022f83f119ea9890add9a5c1196000066c000018d291e03ae85e2000056002249b3745546fdc281800026ac2b9800000000000000090b9a7119c00000c0583d21d2a814cd93a31d3c4a00000001b0400000000de180003b6c00007cb25a7000000000000000000096e0f5480001db600005e821182ae88c645df1ff61f084ef800001360000263000000000cee0000000117f405a742023a00003f50125c0000000000084ece2380001d720000d0f800005e618280000c3e18787bb1220120647064aec58e93601fac662c00003941d2c02a000022710160000067780003e7672800000000031a1ff443c8000000000008570000320e383487a01d7000000000000000000067f4000000041501ab82f0800019ca4ad08099ce900000000d2d24553eb25148a8c800028260000be40edf000000000cb00000bd87054e0f1adb1d4c0000000179b3d865ec92209f6d280060a8879a4dd000040f44b39184000022b43fc9b6a19a020988158000000081cca930000180a000125f800009067a9c0001ee314aa0000000000000000a2125b80001f607094f218e3318180890cb690394cb666c53281b78302000001e20000428c9700d180d2601ce98f40001a5700000000000000000005d0c2f280883f9e000082b80000000000000023b7000082a40f8800010984b28000079926a23001279a18e00000000a00a327460080ecde788550000495d23a1f4348c20f2493a8c1033d6199c74301da275600012060c5c38282760196800000004b71328a2e6000000003ba9a94000000005258a4200008ea00000bc513fa0e9800019f000000000000238136e40000d981bf245d4914cfb50ffb17e4
  | 60 => 0xbd01781000090dc1c40000000000003028000193c562c0000000142a000009a00002a6c70d02118ebf05e8226906418960bce3ac000008d200003c4d17080000f7c00000000a94299895e4000000000ca3e0400013902bcc49f91cd16d60c8e90acc13914b3cbe252cea082e800001a080000000349e00000002413492053cc999091e0cc86069111a4b525e40000d4c12d10d366ed4000000036040000703000044fe17c8000000023d80000068000008287f700001b170000000016910ac28741b74bfca1d8000068b8b5c000013ce000000009ad10ea000000000000000000018d18c717ba00000001f362b9c000000000000000000000000001f70271400003214a6c8804ff597d90f0e59cc0000000340800012458000401c76c80001aff2ef03d013269cfd426a00000001b1000000000000000000000000000000000000001118800000000000b1c0000000012fc0000000000031d032800000faa81b400000002fda982c000056000000000c020efe000000001c28e6100008f108ae000049ea00008370f181664000000005df0000000000024093e9a000000010a139f20000cbe000006240000a3fa00900002514000067200008e744d4000000002400d498e4430cc00000000000000000008a98000447623f4000000000004bd401a9a44000076c42e7a5c4242070280000000000000007fb800000005f240000933455040ecd8d93f82e64589c790909a06e053a80000acf00002f708929c9b0000646822d00000b00000000000000a8a0000000221d20b200009f41f832c520000ed806ac000000003e788d44cbe879818b800000004e3423390250c2e000000000004a3689200000b83456261ac3ad0c24321c304929f204e0e7c7b801681884343640a53129bac21144144e0818e6227641ac6049adc05801cb863ca316437e1e5912b85d3261487590d8800029f83c5c0000e6f000024a8dae1190000065acf1914dd30363248b7f00000000853ce6b86f03926225526a031f0b6a8d909f89df2388a4b00345962829bc2d446719f1a0000000000000000000000000025db2e3a00011f30a0826120000a950000000070d8000218b282895800000000000096e4fc7800000002f54000137c4ac651f40019a1a23a4000000012b5290696b87400f2a0d0e02700bc17f7000000000000000415a14a402f23e7486c402800f1dcd3ca48df00000000139c0000e98000000006200d4389ac46e65bc4bd115e302b417d46861ba20000394c5288000167e2f81161923a1f4027c0d100b73462a2a98aec02b933a4000000023a1091429b800005c72ebc5dd4f37116c2982214c72aa5f1392e78e0000153800000000b258d6127b26168c7d936d00007070832800037ae3cd928691300000273c02a0f9900000000a6002ec0000061c000
  | 61 => 0x8800013b200012979b150000626c149934149c6000111c864508da0000000146200001304a619ad200000000000000000000000000000000006c8c0000a4d39703a8488d80000a08000000000000000000061388bb30f200002ff80000000000000013d02b5016f475c19850000423045b10153b9c74b00000000000000000001ec500008afc000089c09e83bfc3e0000000000000000188e00003274c8c962b380283a07310000000035011d6909016a400000000000000000000000000065200002d70000000000000001b710000360d12f03fa0000000100816fc00000000000203c00002aac000232e1bc41d2022b974e24ac3154e1c8e2a388c5e6081fa14816d691b40001b3242cc000056c80000000000073396440000659cfb01cbe26e01c70037000004d2084000a11b4000000000001e4000008b4400000000000000000011831e58000000000000000000000021ac34445d04e2696bb000015b8105181f38f80660c558000009481c8843993f0000640c00000001b28571c0000d6f43642a0400020ee181600000000cab000000000000000000000000000046000064a003d81e6478411dce9595d300000000b639856000069246a294f000000000fe5800000006778000137b000062f89e298f731f41b6c85500000000000000005d60dfe0000ad700000000000064c93a100000000000075f01647b648c900000000000000014a403823880a2781a0000029c0186124549681820c84000037b033e000000000000000066b00000000070cca08000000048e00001135000000009c08000087c6c31178023a00001a389981a2d000000000001c0e21264ac00001a100000157c0001d1200005fd80001d3b04106290387223f027c6271216857c000057c90fd04b305d478185faa58200000000000000000001968f6113f2435a0c9c00000003f460000000165b39b42218a4f800032a8000000010b500000000000000023e6507112c1e37283e175400007132bde00003148fa1265452a437ca10d00009099315182909ce000000017400000615461a00000000851000022b300004e480001748000000002590769339e5328000033e48c64b8859d8000000068284860db4000061a40000000000000011c300000000000000008122ab87d407281e142f4c786501d1fb64668093ca2496392d001fb4040966b03a67eecbd20aba2aa400012fb926a00003df89208cad000091b8b94800010685d087e4000013f80ed90a00b35000000f0d3d1dc8455200000000000000018190bf8fa20bfa0000f73864c00005704f1a81691ba65274e34840f11a27c850291e8446ea8fe51701e1018a68d5901213ad1432778cc9e128503e445581bd820b1c1014e4aaa123d000000000df800000000000fae012b11ee4cb8a0c00002144000058f8000000
  | 62 => 0x9a8dac456014f0f3c16600000000000000008b78000000042f434a80003fb2000072f0082000000000000000000000000001750043a0594f3222042bec6f3833f950504b848b07d782cf177a463066b815f130a75ec331207d00365800e850000000012104cb80000000723c000000038f0940c0471ea11c7c31a89aea126000074b400024f2425a2f00ebc800019d62b1000023331ea88128000000000000000473168500007b6ce3393b1467a78f0ebd185b112e5270f18053300005dad1cc8ba50b286d781c180f92b04508413580e3424636304098000069c0000966800040cc35d400000002dc800000000e5b151c54c000000000000000000000001a9a7080000050006c872641d682180000000060a8337404e6ab40000000031e3cc800011fa159c0000767800033b0250000010fb00000000f00242f0000000003a0000381e8e28000207f000040d1318000011a60000000000017744238e2b946d00003bb497b0a7f40dc6e9078e25a64460681cc11a5c8097825312dd07ce314c567d085203733d027a827400000ad830fc2529e1e0000208800000000000573c0001a9f0000000000000000000000000014c90000937d0a893fc307a000000000000000000000015630000866488b800022f481789180000000076443c3000047c08a34000144b0000000000000000000000000000000f5a00000001c840fcc00006488000000021606328000000069540001822490623a482086b9274c1c752940a931f006c48c3d00001b6e3f287f20f2d2a945ae4fea80a51b14005c7bf8d9f459a05c0145003200805d285200f44331c00000000000000000000000000012a00000000000387018612ec8b5d00000000caf8000495a34150de000049440000386162e000000000000000413e8590bd421f82a2083685198fe1004400011ac23cf100a105c00020c4420096186ec148e1c4c83483340cc0165a00003510b2100000000000000000005200e15057d473c2bd0000000007a034e08261d2f24346b2ce8a000013a42db50c8a1b9000077042878f7a35125530867800000001abcf5a9a781d5a8e900001008021c8bb40000e7c3f6200002968000000000000000ce62d4e0000c30874d282e300834d000000005b14000251534006eb48d60d3310b636c531799f604e0000000000002cc600000000000136c567803491123ac47ef86f9245d47900f5027100002ea86f1800000002a3e0f6d15d000037567c9cdc7172b45240000f41a0a3000000000001ad50000433821c0955127e00000000000000085e4000000045c851c0000000019ee0000c92800000006b68000000000000000301a08d000000006638d20000000010e700002dd61d4c327800000004188fe701401ee411780000d2e00004a7c000000000000000000000000a0341c1d
  | 63 => 0x3f00002c12277c000007800000440000095a1898292099b80001ee0610c4370a6745e4519c1cf179d0d2c28812be1a4b00000000aea0e3c182c0000000000000000000000000016820000ef88000322610383c90000000000000ce0000097c94850031d373ea84da0000074732de2650ea9000048227b90000215338ca00008b380004970835cf83a61825ac2a14000000020326a00b2280000f6e7c751301ee821c43c24d160b583b52000067b00000000239c000000000004e94000000000000001156000023fc000033b1aee0000000000000001434063821080000b8a0000000055400005e690a180c405200000c2c8fea1750659400010352c360000f4b8f8a00009394b700c5900000e18000111800000000000000008367d041d41d28209622a8da3800046947c7068881d245f68244c05189904600abc5310af207e43f2c6ed80910c822238aafa0be0b562bd40000802000000b400024b24a0258c062d1a9633ac05650ad0e4b0278000106f800000003d1800006393b4000009ee8490000024dc00018c20c3a45883db109607780000f7f80001d26891c0000be50000000000012ce243000012400000000097580001bc937662c511058bf4380c7a5800019393b860000000081b3984981c00013f3309e1490000000000000000d93000000000c60000000000007f98000000000000000f808000000000000000000000000004dc09533fe00000000036d3ce20000a8a000000006c6427200000000000001780000000000000001a913d266d80000000263e5f90000000000007c8808c11e70000000000000002f626f7129e00001f522c6c000000000007f0c60c8000000066047958e521f1c0a71023132f1b5c5ce42a219d50a3293c00669c6f0370823ceee078c156248151e5a103187a00000001d1b1a8883786df87331390326128e177e391c000080618900000174426b0000160882700000db200007638f92a156000091e456493bb0000965ca890aa200000000000000000000000495814707080000000084a000000000000000000000005af81d9000092f01932659489c00000000ad5000000002ae0000000029248410000000000000000dec4c6a000050e800024ec9814d2102ac36d047608ffa1ed2af07f1400008fc273200000001fae000000010f500000000000087fa39000000000b1694460000000000010470000659133120750e2084cc51902c9000000000000000000022404a1036a24d0000000000000000386000021a80000000000000000000000130d0df900000000af4865d062c2bf40001d213a4c07d8c6f1e3900007a2c000000000000000000000015d800006b900004b1a1b9d110961a000000008850000054a00011ca00000000000000010df0000000094880000000000030580000000000000000000b
  | 64 => 0x55447e48000406a06a036f2612000000000001f7c00003f340000000079c9148000225c00001de400024660000000120508591312000000003ec2e92000000000000000000070f80002d4435ed0e60000000031c400011d000003504615000039e063249f58000000045d8bd380003d10000089006983978964d00e8e98465430b400013b34baa6db10dc25ea000000006179e122e3e2ea800000000620000000001a546aa578927519050e8200003d89ea500000000cb017e826e683040000f120000786917b83f43344676d0d788c43e0440c928401684366186495584b544341ca4d649597240463d400018fe47e67f1016f0b2844a01554b29952200ac000096f800000007bb40000b470000435c2ff11a23c884cc4c2706bf00004fa4000000009f458900001aa048a0350d012800000000000d5580001d9c000025d0be3365e00005fb8755000000003e80e1d0000000000000000000333480098da00003aa000001bd17600000e819b20000000000000000036e3e94d27000024cc000004297de0000000085f80000000000000000000000000000000000000000000004ec261c0000000142029ac047c000000000003e200000000437c3db040d073f1dae00000000000345e8534000200c000081b0000181300005e6443998f206de82e4c55242a42da04b459d11331970000000000003ee685c49a516ea0000000000000000000431c0001af0000019090d823b60000239013a83ea286437bc00000003c920001306800007da404800000000000000000000004698018800000000000953c000000000002368853000040f67d9c4410bf11c688c906b299332c6c22148cd007f36986be8000212b44a621243c81ff5251e1d412f98000000000000849ab418fa8b4128d000000005aa0c181ca72aac000000000000000944000019b0117c000000019d9368c27d85a184ac0000000000014bd4902289c26ba2141764868ccc8a448228e43843e389f141c41c0c2de03e50000000000000001aac1dc821b00000000000000000000f3000006501b08476a284c2e70000229200002fb905f000035a429a93d30fb200007f380000000000000000000000000013d8000454278ecee280000000000066200000aca2c5461b17d637b6000111b8a5b087871e80001c42000032b9105000000000000c7222db2812503517c21ef00d60a84a9a96af09864e28000000010c80000000000044ea3a7468b206f00002c94446027232b200000001e7449dc76b0332a0ec2a1a748c7212573000024b800002922a80000000020aa190e8494747081520f28229244046400000000000228a480e50f070f148c101874a4289850d35ac5218a8e000033302eaca1723d2000049dc1c08f79000000004de80000000503c000000048888150b76000000000000b
  | 65 => 0x96611a01b1081dc88184d127dc767c55720a70000000055b16e900003c8c000000040c000000001be242fa649073299dc0000000000017b02e7450780002553000a0000000004500000000000000000000b2800007210000634c0000000000000008dd00000f46000000014d80000000000006b7102e75ac000000011a000000aa98600d3c000129d90553de250a0c028000000036910668e564bb858080d2000041b26b000000000000025580001ca6196890b044f18650d5659c07b1241a2d88207923b008300007e04f6e1ab542d40000c3f025200007250de009a73c1400000000e0200003ce41b4880804ee9458b6c8cda000099187bd80000d9089f00000000000000006e1a06200004f8c00025a04c80979cafa000000008944b449168191e2598386961500000f3081523bb433a3dd07c39d3d0000553483d0000000000000000000000024d4763000003d433c40000000360a7cc4000000000000df8000159a375c5ee0064a1780000718c42095b3012e0000756000000000000000000000000dc4000016a16fc00000001d390000000088323410000101045994e63d6800000000000341e000078500002fb81cc800006e2469c6ab0ed522450c507f1819f8f19000000008e21e850000000000016dd00000000c5aa1550d6a0000d6099c100005e8c2551e4f3fa60f60006810100005d3c00001493e561054000045919509074b731fc134987d5c00018ea3c4490e80002314000000006ac00312950871400000bf00007abc5bb0000172e480c000000038b06570000000000000000000024d00000000000179748623a88a0b000000008d8839b800000760b708c28f4b1a30541d1859fe4250400000001bdd25ca00000000f652ae61f1000000003abc00008d40f354b5e13c8561204930d031b42301c0c342a7648cbb800000000000b9e8daa05560000ec3929626b267400e2149a01e200000000000000000001bc9d4c23b216912181ae81060333c000000000000000415800020284f882cf00000f5077b02bc8000207c1b80f829a6f000000000000000000012608738000000009209220000000052bc8fc8000000076a03f7100b00008cb0f350893062604dc000071f3572219c9af1be91a4400000000000000000000002328000000000000de53d44000000000000000756c0001d3200000000000000000007ab8efd000f3bac0000000000018de5e7c0b6850102fc23089690a34118e1fec0000b9a4a4c45ac46c07b500002d9421d00002710000129112291b8a7ebc0001e540bd400000001c0b477871c4000132b21d886780a6800045d603180001b77348e1a48bf28000000026009e780001a328d78748935023e875645a117ad000052545b50a102a0600006b700003a54000056980002d3271642b1000000005db0c3125bf0
  | 66 => 0x21c800000000000000000020d62a9e638800025b0000000000001550091a000000016104a520000e7b000004e26b281ad9d9500000000000000000000000000000000000000f9b95e800000000d330000000063e40000000276e0000000000000000000378846c00004c60d9f000037b4000123808b712fe7dd03fc0c88084e70b4491800000001d300000000476020a10418ecc0f2a22c000000001d4e0000000000000000000a340000000000000001f2d09ea00011a38000338800011e024ac000000010cb1142058c952d2ac800000004a00d08a36f36ac87480000dfd42f40001248800019e41e140001e870b6209b512005e9000000000fe1d4500005be0593905a139661111398000000000000001f8e0000000095f1d5a00002e640000e144c0677a918690c3106a157409600001bc067942631d464c7c48f04bc229f314a7b44abba15c30ea559ce7d17d4024621c030a104300b69020f8980002a342470000001245400000a7395914a0a00002f68b853e2a4b540001ccc000000000001a34000069e4a1601c000008a0c0000000000097b432c800000007dd400000000000000000000002eb47c00262a36c00000e9cb4223d4162c25d40001608148805cc0000517000023f92da233c0000000121126220000000039d80002c168c445638d4a000000000002183262220904a48000439a6b64b32800032866e785a49fa7000065200000d24422a275cc4d1c86224400000001e3e1904009400000003a9c000057080000ada570808100002dc4000097183ba44587ad821580003ac224d80000000345491d461107d400000000000000003004a846cd000000008fd08e0895800003a5c000104e0000000000015c40000000124289592aa61d4849783b403e61a20f7b02f1046c00007dc89db00000000ed3979c1b9800000001fc9200c1c4800000000000000075b80000000000000000000000985ca8b00a2330c0000e22011900000000000000015ee5018000245400000000000000000008bf8000000031067e2cf0e00000000656c0001da600000000ec989a01e1a0000000000011b835786340583000000001b58d1e49543b990c0a1ec230c000000003c500008ea40001eb80000492ce2f06c930128b1c3d500a4152e00005390000479200007450000269231180001e5000002eb00000000194e000000005ef26023744d22800000002b2000010bc4604294897a00001f2e000106e0000000094808d3185f1a9e835008d0d5922fc6c1c95f865b3c6200000000000205a2b9cb36a385000000003a78afa00000000363a5c607fe531c88f000000000000000000044dc64d1088000014f04838a8da4ce0000548c000000007600a5ca8b847100006ca80000b34000000002f721fe00000000000000014607f50000000000003990
  | 67 => 0x47b09e8f11d489ec000000000000000691915d172a650800018c400002d8400000003c828e1cd7b042c3a8400001bc143100a40000188a39b000000000000000115e6f5086689871282085cdd090e5147a4b9c05b0144000063d000002e2118a0000000000000001e88000000026722fb00000000000000007c68000000049e0ff9800000006064000000008ea28d800000001fe815900000b8915166160d2a23db0000000067700000000124cd5e9b2c0922000087d0000053c77bc0000000000000000001cd9269c0000e08800000000000000000046348b780000000000020e400020fc15dc354c0ef894700004be45718000000054943c00000000092cc0000ee3190c95680000000000000006bca172000000000000b03000046600000419381013840001d72000097ad1b5000000002f04000000000000000c6a1dd900006d88000000000000000bcf14b9000070682ec13fb0c74361055e09dd2efa1a0476280000a7e00012789c9f000095c8000000030843d709a58000000000005ea00000000000058f0e000000000000025371a6e00011bc00001b5a0000490166a000068087118de30000000000000000000382d2cfa6601d80000020525701b7267fc7e61ae00e0438fc4e6a1e247da3d080001cc5000001b0000177204ba6a440000ac300006ad8f9e9ed0167c00000001d4d154a40840dd00002d3c58300000000061e0000f4a0f203f362d70e8280003ed60000000000000008a5c000000000005f7400000001f246ce014d80000b98475893e9e2101d088b400000003e5c241800000002336000122d10ef231a0000817800004a000006eb1b49000000001a78cfc000000006da80000000000000000000dcc000129a802c0000000094c0000000000000000000000089240000c142d063d382d6000000000000000204f294c96dcb6c15f8414400000000000000000000001db8000073f883ba5cb00000000b920000333a32880000000000047b858022760d382e5920f9f112e080000000180d218c65a03241e55235c42b4a389aa73be8000039a8000371469189f8215f1178000001fa63b0000625d23219c500000000911897a00000000000000000000000d7e000000000000d240000000000000000000000000003c7800000000000778000000721eb113c025a44820000000189300000d6800007591eda77f4000221741102c4c0000000000025f4000083300000000b050000014e0000000000038be62809e180000000000000004fb38f6000000006b31e760000000000036447788000006a0fe89650526054617ac498120a00001f2029d89cc000000006bac99e00004bb49678ff3800006981f683219a210d5a638c3c493df25887c2800004342d1a5404000000000007774816227e0000747501c8968000000000001faa
  | 68 => 0xfc400001d8e4f7897d8000420e3bd4def124a00001e905169bd344ca5784952005d2c2e0000ea41a9500004e508730425461015d832b9da54002742d19880003cb22a64ec18ed803fa00012ba878d4af628084f794b32dc200002d0900748be5368ea4997a000000000001cf24b844555209090e00000000dfe80000000653c8d883a200006ff8bea8c290066213c00003fe3f5204a8000000000000000e51170d13483b2c000030b42c253e00e30c9b000000000000000471c0000fa4000025c255e8000136200008a74d94800033e40dd8bbf800000003184301000024d63c2c0000000447000011dca554247e0000cea260f00000000aad800000000000000000012e800000000194310400012f4000000000000caa80002ac400000001c2217ae2c491faa63a00003e2ced720b339e27e10d63071e038a29a5114800000007d112e5018446642888000058e00002f101328e2407ac0000953800017dc00008ba800000000000c03061530fa7394000228f162e0000000000036760000d361b1d00001e6cb331b031bd039200000000000000000001ad7494e15310f4972c29b63cfc00007e0000000000000c62000095b800008920000000075d000048861060076108516b45bcc313824e029c57fc921000013f6030cd1d80000a761db41d184d311c40000000000000000000b659c5b00007f29053000000007c0cbf8000000000000000182b18900001160000000000000000249c40d02860d310d043d0c32d881b8bda129a93e000000000a7009292c60600000000012530ff309fa4ef0000000034a0000000000000000000001800001e9e6125276037a15602990000000020040000000000004fc00000001c7d10d85e5100d031c2e8800004e18094307400000000000136400000638c382d5a00007c4964200000000000000000000000dc3206900003974c5d071b15c007f800002e62a7416b4000147c3042575400000002a4221340000000000000000001be50000000079f0000043400000001bb100007cfcb5e100f0000000115c1152000000002b59fe32834192d131800016602374000000013020000000116e11f4490c0001395000005bc000000000005cf11360000123e00007da91c713c4640432a00000872290c000000000000000000000000004bc13009a9c085265cc4858f76067855f02e4129500003fd40000c21220801f8000000000003f0400015ab0f66000000000003c0600001ca94050000984c0000abd0000000099a24c10000000047a98e016b6736000008f90ba06fb400000000b9409309af84e6313a19d42210000000005d400000ba3b3268a4a7b9ef70000000082e0000000037c4c9e800019b85774eba137d40a033a8f7911460c800c542dc045d3a0c8de4d03000033103fb400001130000957
  | 69 => 0x408000000008659f9905ce85086530468133269d4000211d38049040aa09c540492827483f08994050056c9ec0b2b1ba097d8dcea0bd3fe87d1c0001bfb1dbc7799139000000000000067804f15a4487c68d238000c869648698000314200009b09714334c761000006e1213e90a01c116ef3f9a8eb00001c64380e000035a1f4f0cd80390000061c40865f3cce70000267413a8c8f000017fe0000ca980000000000000013c90fe4365400000002d6000000000000384809640000000357c3a480000c76016800000001ae1121a0000dc89d34074000011fb800000000000b6983741c6c158509e000000006c040000c7a00000b046b98000000000010100736000072ccddd07932b940000a51045531102bcc0a88a5600003eb8903908d063a101cc06011e00006400e42800048c00d2d27a10de023854f01b1009e0c363da0b3c0797066a0000ccd800000003a3cc5425df05b4942516c000024de730c78380000000345cd49096200000000000000000000000c491e18000071f911f0000488472a93061f702582000000001e3361e45f51bf010a1d1a1b7cef5a434000030780001a8f42ec0000a320cde10060000672179600001dc0d1f9fd111720cc42c6800040164e0000025a5225a87c0049982827da7ccc9789ddb43ee0000000000030043dd4ea99b96078000000000000130c1fcc72fa33f00000000cff22620d8a000123b84ef024e0000bb2a45e1ad497fc7d4000000000000e4e00000000349c0000000476600000000000280e8340cd29e2b00001bbcdc600000cbc000113a00002f80447c5fc847a0000000089d03974984310cecc25022d2e50d86f696dc138240f10470a6c08f608e4720161e45300000000000000005d6c000000000008eac2a58ec937700000b3d8000453400002d10000148e6ec8be31fe51c444f6800000000000355531f9f7f17bc115101e911c09480000c8a04de036813b5123214c10b840406e48556000000000000ad1000000010820c0600002afc3f5057f3a02926c6d18fd51e52733483624651fb013e4af0166210963b04d720000181a4490be099f300004fbc0000d1500001bec0059ffa19a409f40d38000461820d8d1580000000294024f00000c5800000000fac0000871000011f0284683d91b9226d27ae71b000006263da64cfcf7485f10e80000000019b90ac6000000015430c023bbc000000000001b3c00000004a007c9000010a5000018f40000000000000006e39f1600000000f8d8e840000000000000001020000000000000b686578000000000000000fdf80004ad49428ef0000042b00000a5700003688000000022bc0d7c00009b8800014528b111e39c751778537cdf803f90df88a40e14a0510000965817592da15be4bf85e180002c645dd84f9800000000f345c8000
  | 70 => 0xb341580000639000015c80000f5680000000791817900004a880000d070b8432204d200000000000067bc000150e0000781c0000a750000000064e000018220b1400020b80000000004c0000000084e8000159004381bd86021f0622da5420220000000ae65d000026542328000000021700000000000018530000301d0989305000000000000000292c19e4e278a4500000000bdf00002c38142c0000070199646705a982fd000069f900b8aa000005aa527d9b310d8413f81e112f34312000000000003aae000124511e8253604542588000313e0000000055000da6814fef9445000000008660000000060f0000000000002448b58800014461f04d3b800000000320000000013228e340001e8e39e895e000006a5046a7b18641896e2bb486140000d57051c6c7c9b38d870000313c64080003d362ae07df8000250c825c000000020ea000095900001f8400010480182489e00012c913db00000000eb80000360c00000001c55055a41a824f9725000074800000000150408b8177a2ae295445a8b47839d2e440000000000038868db400000fb24e41c3c00017d100007ecd26f058b000053e47c31f2a000000008f907b40000456c000000000000000000000000000000000000000005758000222f05986aec607a1371de871c12e91733377a11cc80f00001e2242600001a5f4c9c0bb42500000268e69a057e12163d7600000000000000014f52c406f4214e00012ae20af197290fcaf88000000000000828aa900008a780ec200f000063e00000000000000011ada1f546300000000000000000000689146c00005864c9d8146498e000000009b0209400002df000034a647e00000000000000002db14d5282400012ef0000000000000001ce700000000c0b94ef0000354003c80004c9e0000cc2159900000000aec8000278841c40a8000017001188f54178f09f0000000017e92ee600000000000000000000000000000073ac00011290000338412110a00000000097e825b16025b6c00018ee1bb873380000000000083c088024f6000000010e980003ce00000000230a00003fe8000000000000000bac800000003ecc0000000000042007dd20a445021ad88f516da26f2000000000000d3a00000001b9948f6000000011db087600000000000000000000000b780000842c33a191700006a14000000034d420fc00005850cb828bc1a69b7f0000100000015cd27900000000230605ba00000000000467c0000ebb800000007a8c00000000000000000002961f3c00008dc052c20a000012c58000392a0001291800041fc2450350000000009134afd9ca4000032340d311ef2abc2de844b0e9900000000ebb1f8628686a2899190e90af00000000091b4bc86934568000000000b7c410a5a2000000010cd1c30303c2f188d280002d1000
  | 71 => 0x92210ee53f8000000000000000000000048a200000000000014200000cda3f60000355000015bc400e420473d84fc3afc4b40b6102cd1da02ce4a5d9b5344e07fb41f00cf3233c00000002235000016e800008ff00000000fcb86700e0016751470701190a37ad0870a41326200001f41e0e24b8000050e000000007744ef98000024218248b480000f9865fc65e8000000000000001448178e4b2cc6c800030bc0f900000000017c385c000000000002fc039e0a5900000000a2ca1193eb60fe00001dca000020600001b1a0ae600006fa1e4c000000000000000000062d8cd9202e3f12751057d80e146966104000222516109494cf301f90000000000000000000653072e265d1ffa000069a95a30000000083300001a6068cc88a22440ef000000000000000082b851c8000000044b8862800000001f9c00000000f3e000010126483ef20afce751fc0000026e86949f2c2d041df40001343050e4f18000000036000000000000000e644e4000000000000000db5800000000000b4580000000351800010ba2bee0000530130f391826540001b7c36a0000000003be474e8cd8ff90ff1000047540000e8800000000000226a000000007f188762d38000000004af261000003dd80000000000132a80000f1c06b483f8000164000004b8060700003c3800000003d14000000004780e70000080880000000625000000000000000012b1c8848b225dc56b201e00000000000017700000000b3614cd193e36880000000000000006869d6c000088442a0880d00000cbc00000000000469c0000000000000000000000261a9224e99800000007d6904599c81fb28da0759000017f00000ff1104f02e400008d0a0f84c2097bcdb78000435600003c40e9b11300000000051112227340000000000c00000000027400003b20000000000000000bd70303000000000be1a4000000ae1043800000000fbc00019a8000000009f52078373e0000ada97f500002fcc000256243822a692858b6e331e00000000000000011a8e27000000000000cb19528000094c80001b3c000068f467fa15b33128480a40800000001140bb4800000002a4127c8000000075e00001f63000000000000000249c50f8c7e9d7f3c6800002a403932ee25c9ce19a10c2b107934000000016128938000221e000000001421b8f289a3840605211108386080c2b809021061810bdb08a6246e6f14c9096432234175c000000043e20d74a4689260ace6cac47da01345a466b893d80001d0635f124a192f000000000000000000000000000c8e14182004ef09ba5000000010d318d5000028b1013012900000000000257436c8000017d0000031275a09b324920000796830d1353000000000001e6700008a94a32873a0000000000020b23a800000000000003da000000005
  | 72 => 0xf851e740000dd024980000880c00000000f028190227800049960000000054e000086946898a0b123200006e50e0447987c3066f9a7f00000000000000000000ba40000000430400000001c832ba40000000000004c620f45538000043283c800000002e700000000000012523fa0cfe09831ad6000062fa60029d8000000000000000472880280000f060000000134c00001598c32044814ae561094d0b92282203b80e4869028760000223800000007c7ce2d0000422e2244b729ffe48300000fc3a61b1fa4000043111a32d4036e8b9b00000000000000003c700000cf40000000409a0b6c67f067a3a9e0000b560000101e161d18480003de697d0d1ca13843207678000261d332c4d347b581f000005c80a34815d3b8090cc00000000000458006f008f041e000000013ac29a800000000e5100002ec40001e91161400004db96ee3a1e071c5741560000000010c00a2e20066e6c7651e7c173e26591a3249e15e25520058a2ce0e441c9c00003a13b8e28fc00000003e24227c00000001c5c864800000004a0800006cb00003c6c0000000000000000000000000029b800000000000472e25f0de41fba00000001183800005c882685468000000000005df800000007c980000000000000000000000000000000000000000060600000000000000000001ac41d62000000000000000000115100eb000000000000000296468747c60bdb27f41348faf8f492ff80000000000033da39c0000000000004b64775a330000062351b096060000443030b0731444c53483ef1ff7000059c80000dea0b1430c0a47a3c13b6a23b0e6e163746400ce800015be000000000000000483c41107520a382552000000023f80b8c0000c130df600000000507233b49349058d2880002e26875c2ad800022c651c92c200002c06000000019d100000000000000000003748000000018d60000ec5096a12140000fd025fd2400970c16c80000000276910000002d82381cafd00000000000027016cd15b4000089f0c96197e3915018237d2c460000bb30000000000005ce9e7f118673fc00016ca3b5628952ac1ecc17fc2c6900b15b23b1243f500e000000b200007ab800013da00003769d60000037e00000000242486ec96c0efd306641001231a69250e249c0000f1f1dc20000cf38d3e00008248000007a00000000000000000000154000016b3c7a00012d50e32047000000000000000021208e480000000000000000002f8e000000014ab000009e4000000000003e1400000000000795c000000000000000830a033000087f4b249795000000004a4171b4a56119819580000000467406c0000000000000000cdb000000000001cb500006a94000000000005b200001f9a000056dc0000de7000000003c5160725168d10000163f47ba0000000110724320
  | 73 => 0x9ae0000000000000001322000000000001267370e27ac94e112f0000870cff519b7409083bc7f3063f1bfe0000da703600b20877c9df8e571e5e49481998efc044c000038b9cae458203f87a384bd09e612a000000002d2417e88641a3a00002ad10cc05d411da70bca7b1c3e29c676f4b108000000000000000c2000002b700001edd116a1c54068800000000000000248d0000000000013ca00000000fec00002180734c63f00000d8864b520d841f0000283cf101dfe000000000000ee4000000007818000000000001da869900000000f2f00000000000026f80002d2c00002651cba0c8c000052706ee00006b3ce3b9eb90000000127d00002558000000000002fd40000000000000007358000000005440bc129d248600000000a8f112800000000000000035483638ddf8e050d6466b0c00800038cc00007f480003b2e587c7f12641000037501300ce24c4604a09a0022a47e01e8400015ec0000008c000000030a800005561f9c14148264e6300002f7e08484bd8704153a065cf3d80003d3264acea88a71000000000000f4d000073910a292c6000001dc00024ca380862d0000000001e46bbcb9da66a000043610382468000000000000000000051b8000173022f61cb00001e51246a370858724c400000001144000047ca0000000000011ca377400025dd1b243e9c0001265439e00000000000119c363400014b834460000eea9f9142d233e400000003f6464b902b800000000000ae8800030c69084d590907028261147ce02c207d20000fa518a20000518090e800000002e8c0000000335e00002ca857b0a4e000000001570000448c54f00004ad8226c0000b91456a00000001cfc260600013298b0d00000000000236900008728000000010fc83dc8cb261e00000000983000000000d1c43a000021ba6c44d5f90ee03de2d10e459c28118018c8eba86e52d560e3000000000000316c0000000000000003f5881400002ba4000190b00005a6014180003aca8708536826800000000000072627fa031406d882f46360bb8969800025748ef8000000000000000000164a17c200009f3893e0000000000016163240000133580000000689c0001a1334ec085800000000000000000000002eac00000000000000051bc85798c520508af8000026a2704017c4b2a22003584134ed20a862c980000000000000000000cc900002ec879280001cc01a363400ccc81db0a746d9c1f3125125861d2c2641d54253a12b520aa48748ce0000e45149012207a240000c5d2b74825800021740eec5ad40000f8233f25a386a6063736683f5d332826c21f85c088e6129716a0574076103d74cce00011d500004a1e6cd909b03f73d5400002060cc51ae24d5d2c800004a860000f48083b010c342407011fd2f8a1cd0fa723c50f4000005489
  | 74 => 0x23227fe4444963c3d6e0a30fbe80ed3b68992cc1c202a47b200000000000000000000000000000082809f3066300000000000000021e28484e4f239623f6425c000250719e030ac85582674b643a7c000071a1fb440d83188e010c781a9800015fd055278fc0000000189c0000e6a262d00008f4c11600000000000028600000000000049824db43fe1ee48ab8bca4832000000000002908000000012400000026809c122600008bd40001fd60000000092786f347fe0000fdb91c03ee24da400009320000670806a0d063b840000026800000004c5c0000000000000000c9000011565ae8000000035162fec00000000c9a00007a2a649000089e880da614000097400000000198456a8000000000000000405228742825fc4d7f13380000000000018780eae62f000015a400009818d41195000000000484a3c300005318000000000007d4c000000000004abc688125d23b815240000954000006b800017070984762072c0aaa000000000001baa0000000052a086f0cc2216800011af000099b11ff18dd00000044f5600003ed0188c000079c2b120000f30945a3d260000714800000008e2047099bb0ae8267c000000000006f98aa58da73b5e0b38000000000000000bdea39100006e4c28d9b24337016980000fc30000000000000003eee614800021ae0000148c000000022b06b14000211b43283a3000014e800004114e3980000000000007d21773e740000000205b000031106c9a2130000307c0000000000000000000000000039252b20f641a424dac5f4907302f251d0000000026d854440000000000000012f91ab3488a95bc4368a7c263c941864203df13369438f759a7c0bb28aacd73800007c45d6087f2518000048ad11a00004a4e00001eca33a000056c4eb9800000004714f31800000000000fbd800024220a9c00005283ed88fb0000002a000000007ee800039dc323000000f706c676580001d040ed096b482f14770000707c19b1a0d2f9a2810bc4000000003c152de1814026a00008d495eb00001c1c3468000494a00000000000000058a80000a5d20460000899000000000000c1d800000000000000063000000000000000000008f2800012c54b061d1407e19463f000000000085e00000000278121e0000148000000000000000025b80000000000130b000000008c04216976e450887c800024c3000050f46ad0b942d928b540000b664aac1ddc4eb129200000000792000046dc00004e98000000010c41ac062e41f23ba80000000000000000000000025e156872c89ab00005105042800027c00000000000000006b7800015722c900000d4200000000502d2d18c750a1400000001a6e0000000000000001b3c0000dca1be70000215cca391504c222ea4c1607b239aa5c2070e1cfb0000655c00011b004de
  | 75 => 0x6b3000000003ddd0bd8000370032a800009f800000000000000000002d64b690cfa4000000000017c2000000002660000111a1b705cc004b49ae000032a80001b0c000000000000000000000200002d6e00011f880000000000000023fc367a0000000188932740000656000024140000e31000045163c40ae5a14e1ddc21a462c000006e46094a5f8ea5463e59e80000000000000008ed0a3b257a0000e6f9ff149da298c0c892a63f2854808ee9cf50000305c057892c392400007dd9d02000003e000000001a580a800000000061200000001ce1151269cd269817d246809d8000000000008ba0b979dd8000064dc41399720dc63ce1094800000004d540b88e0f0fd0000000012a84c1c2fac0000000000000002cb800035c60000abf91c200004b812e6077b3d3400011eb8d9d17980000000203e00000000000000044d200004bb02e54a2e13fd2ca9c902a5c636000013750eb80584727a577000000000001e2f1b1662780000b9c38d00000fc98a0600008a9c00000001ae84074b438111000000000001add3f7a1f0c49205c312fc6b200ea2576463c000000004cb0000000000000000000000000018eb000094c000018b33abe2d541311e28000000012a68e820000000119100003ba6496c000000000000001322000000000cecf6b800006cc67a842705a74b122d28ae489430f284c1d214a469015a178cfb7800013542660e8e21c90298310509a04b9472a267806594581cf49119321078404be1f94de685720d627730a67a35c09ec8a14000101818c018d06459e8235a251300000e1300003a8000000000000000013980000000000000020ab000054bc83e0000000000000000b60297c000000021600000000000019a04526652c5dc80002b4c8e80e52968a0a2491703d393cb2b3a4e6ccde0a8406bc2f612a517700d524f492632524000066ac147a5b10000000126c0000000036d88908000285618448b994e9000048c4445232f040a613068f8b0f08f882fc3b615c61b120b5451a990f43ca72c80001dbb055c00000002663174253ac00000001d12000000018e7045e944c2ef0000000039b4875110118348774000000000007b34171822800000c909748000000054fcb5f8aed31d200000cf25fc3d6288a0000000000000000104859b000027244fb8e2548462b780001ad438ba7bb8000000013a2000059e00664946112cda101aa2ad86ba80000aa34bf600e104d8000000045380000000000000000000ea946a454c80001a5d1b4c00003de90092b7e710127f1ddf0f562df0e578b3612a4000000018ff100e00002c406801e500ce46fd800000000000dac800000007b2853c98cd0000959400012bc00000000000208011d0000028f114a1f344d910e002a40cda000076c8db045b44d8c000000040220000000
  | 76 => 0xbe7000000e8000058600000000000000000000000571061f000050e444220033894000000000000cf63fc8000038a12e45e34720800000000000000192a02c0102cd7a0cb0176e0000b5200000000000000011592a8e86347ca1a1828100000000265833c05d5ce6da14736f4000000000004ae28fc8fe400003df000000000000000000004d180001f80277000018fc0fbe78910e818d2000000006be800000002a54a020da10000952400000001f1e00003918cec25a839286579e680000091c00000000000414c85f000000006f5493080001c76462c02c000043b807e8ad79668000000000000000093a3d4800025bd0e600000f78193607a66f6400015cc000080202ee09642996300c00001b6460a4a644df8000000054a4000000000007608d2c00000000011c000000010c600000000e09497c4eb877615bd236622e917a0dac242a52dc100800024bc4108e8f135208060000b3e00000000892800004e925da43688a28000281c7e84000000000008108374800023323dbc93492ec42dc0000000138e00008f447e887e200000000d87109206be0000914000000001bdcddc9ec1066400009ee25482562000121f076e25540000000107430ce76fcdac06ec00005fbc04c8e5428c200000000f330a1c000000000000b12542ca458000425c3240773800000000000b2a800007d6706c2c087ec3a744df800019ad00b839390fa000000000000d7480003ef438641dc153b000000000000bbb000067e0f3000001268363d21e0244401465747e71f9641da28a06de000004a27a48fd124eb20b032e80d189f224020000000000000000000000000004440000000000000005eb0e8b971636660001104000000005da0000186c0000000109123e331720000e971e16000000000000000000049e40000850000000000a195a03cd66e4092399ee33001cbc03b255500001dbc0002403495c6ae8b78213000000000d3e8be811bc89a08e795873d4c00000000ad8000069840000cbc48fa6a5c00000001ab800008ef032e260013406ef80002b0c0e34fab00004c3e8c5ca83000000007eb00aa071600007e906e2018c385c0000df40000114e0000000021f138e470c4b89f3e4070787481c000000001d61302000036429794c7b08250012138c2e90f950db02b0400014f529282a85026000013f26ed00001ffd000000011a2963e0000644843f83da0efc72848b91ee12c82000000025f53aaa00006a5800046a23198ea59575144296380001761429629a00900bfa4a589970f160a1401180000fa30dfe27c81a1883b18b7470414d8405800038d600012af8ecd000007200001a8d0b460ebc247800025180000000008d0a10000000001e42c7495fc000000000000000000026400000000000118a0000783000024ff16e000000000000000
  | 77 => 0xbe0547831b00006774306815326d403280000000000041bc000260a37a4539000000000000665cc2800003bca0000000000000000000f3b08f1230000008e8800000003f108f4a25d03623fb0a9f000000000000b66000018f60000000000000003661143000000000038000172d302266786688000000017c0000065824645604000000028b6687009c8f5138765dbccf600004c980000000229137f874900001bd1000000000001a8140240850334a02f216034ed1cf800016f23b5020980002a300000000000000000d240001aa91cf2022c00000000000000069b22ef3b1631900001502251000000001d1f00000000b1a8000000094300000bb616fe000000010720000110c00000000a9a0000c43800000001d092bd0000000030e80001b3a0d420000000000000006c70a7f8000000000000001a99000046d400021390fec0000f590000000000000000000000000000000000481e207c00011e10bf08414000258f00002c7124a80003d74364400014922c26000000e800032ec1dc474e059c43520a2c0000163459e0000000000029e280646e4055324422ddc00020e900004ca4ad113140ece00000001a60333e4d610720000000090e01cd9d6400001dfc00002a82cec98c49e09c09322c0000000144400004354000231304560000000117c000000000002071000000006d99e423b5a253803a80003e8a5f4cd06144339ba52c0000000000004adccf09b2d246c3c58bdd1454000000007ff000039768dec7d68000059035a0000000048b061b4000000000000000c168000191200000001c8d37787634000000046be83f48ea000000005428000000000001f5c000000008fe75a800021ba2a7a38c000009c447080000ad6000032f28b15195800000424b200001cb72be60000a179807171000000001544000057c05778000000000005e78dcf00004150000205f0000946424a09130000367000009b4000037b800024bd000000007f700000000000045197630180000000000000000708c588809b0000000000000001080861c2a10c310f4a91f05988000047c71b81cb00003796902c0001ebf1a100000cf1800035f20000ace067d0dd400012f087821316892cb6f0fde43681254b1889f512f200000001d4346ce1c2c0001c490294000000000002bbe00006380000000017992e3a35a26408d351d31f083a7c03f476e1ea4061c647125200001fd628485bd97c411be874520700b801cc51e829a1b810a9e0109332061e1eba4420b9300b91b3688c89c8800047a01c9529712ef3a120298000000000000000f149b520fa669ec0000000000077ec0000000000000006c0036100000000b3380000000000019a0000000000006660000000044a8c59087d2914000000000003e4000000f08f69362c45c11d785962af2000000
  | 78 => 0x558f3d000000000000fd40000000000011662d9c43580000000322a000000009051e022fd859606853e28467d1f50000000000acfef184b000000000000e9e36b61fa419800002e620000000001f000005e9260000000003ba528f15dc1fec39d00928000043644385b416aa1eac4990000170c16c41544c408000000000006228000000040ccde81b79232e000131e021e01d2831d2e0895d36b4552517891d3308c788c3830e7d00004e809a30f0600004454000211628be3bc4000000000000000000139f00000000b6a857a079e581400004cf0000000005a9ec9413c00006eb956e12d2183c58396b3443e000130100000fb6483cb61a21816e20000bd7926e3f9849f0ef4187344fa0d64c68a34800001ffc9110fd00dd6000109413720f96000000000003dfc21509940e7136e60dd400001fb000085b0000069337527c38182081d2c7a518d190a1e80c2661447ad8ef93b745e482c624f711ac5ef00000000000010fcf36800000006d3c45080000000000000015b6122a6338dc281b21690845089602bd3bea7e30000000000000a147141c803b660000f670fef33980000d928028236400012e288ef32f60000000216b463800005401537131a5b9cb6f93a92c8c30c82af00001d2007b80dd800034021bc8a7a17ee3ff6062896f000000004960dc122bd26ca000000000002514281c000000002ec73cc2d422610fba0001108074a40960000000000000000000000000046529514000000000000000774000000000eb8000000000000000a2a9cbf0866511c2f5896d373410880000992000093842b79b1400008e2400006c030680000000000000005ad80000000436a00008f28e4700002b30c9a83381e040000871a40244380e7c575116542c66e106af8356000000006d014e04c5600000000000000062e115780003edc00002d51393020e3f3c9de955947b81df0000224200000000fdc00003e96000000000000000000028295712fc43284c709b5545f84c6c05704c71d860c0400000000000877800020e7286682100001bf5414a0ad8000000000009614000065132ea0000e6481e93c1a00006e700000a442f442e00000007c9348bc38000000070f4000000000000e240000461194681e4000000000000000000000007900000214000045048e48b3b9b7000008060000107b0000000000000001ee200000eaa1f6000000000000f5f00000e44000000000000000000000015f00000000000000000000000000000002adc000000011440001135800000003c3c0000000000000000001dbc036a8688c6ba424108a0a34000201f449a09b83488ff8309a07b122b8cc9168c0000000052b24a825b00001d81008600007e2872b4b421360f7c969d01762330c1221d5315e308c000133b0000000015500000480000075b022d00
  | 79 => 0x9681d6ce39083223961dac0000a8c2d4a923c0000167041898e08c79da339d82d9073aa26f000000000000000262a995c0001e9e0000000043312390f8a88180002376000000003698000089a005800025e300004a80e0c96bd0fde2324000000000007810000000018dc44f0d5b895b000000011e3016e14d44578ca88510148c000000020220fe00000e48a1ee0000000013080002ffe00010f58451000000003b1800000005c4926686603f7800000001e3316528ec87ee13fe28365d88b57165e0ca44290000138b42044c4d1b008d51412954106e91a42706014cc238000000029ec85c044510be51d829914971f7a000000015390000937000014880fee0000ee78c1d0a120000000000000005e382120000382c46ec000000049d28ce4c432627000000000000000000000000001c610000000016c0000000049680000000000027fc8a61cc1000056e4000000000003b491060000000056140000000224e5f0c000000000007b480000000000065f455d9dfc0000409c33993211bf84b6c3331457000000000000ee000002a482b895fc369414c03fe25613cd283c4e4380003df400012008000174075f025820d521a200000000207491c2cdc12296b200000000e2920c32b70000073f11be00000000a15000000008b58b388000275400000002420040030991871f3c43b48e700000000000000011f10000000091bc9e88d49276c000000000001a1600000de00000000167cd78800000000000d04000000000000e189ab83cee2e6cbc220c600007b205b188f2324c7ed4757846b2b1c000104600001e2a8f583c8800000000000000000006ee00004a88000116842c4c918000171e6e98d2081b020920000d7a9e62188e000000022d302fe79e4f01000000000000000051d396c0000000000037dc8d0d2a880000fc693307179f3409d600009dc80002cac5fd0000000000000000ee48daf000061c05ec9a16315c78540000c25433600000000e12000084b00001d130aae8d08e730b10447a84f901499d724c63c6c00010040000366400022ff00001c641f38000000000000ce82d700000000b321d900000844c0001b2817be000107a11e412c06d00000000000002c3000000002290000000011020000000000000000000372ceac0bd2000052d4aae800000001d942c7977b353a6628a64062a015805204d70b1820fa31cd28ea0b6489404cd17392ea3b1e901800022ad000000011c98000119a064000008e3000042a4000232300e486207791dde02d897b884f0243439008d000020cf000000008338000196678146b61eb000000d200000f31387e00004f3000000000000000000000000000db2866b3b7c21a8bf90bb810467d74b7a25e600000000000157b070082f10c600002dda11484c780002bdc3d689568000000000002
  | 80 => 0x2f502d1f391b506a6c91200003e800000d639ed83d8024746b3a1a4432e6ea043d11fc3
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x874563548210423bbaac0108212d1d16008410da4c6b00420845e73992500422eb9cc928021179ce62940108bae7314a00843f74586500421e3a2c32802117dcd61940108b8e6b0ca00846f725865004236392c3280218d5526190010a6aea20c800863765106400423bb8ecaa0021179cc65100108bae6328800846e721944004236b90ca200214d5d44110010c6aca208800865553986300428f3a4cb18021475d2658c010a9ce532c600854d7299630042ad380cb18021179d8548c0108baec2a4600854e7215230042a6b90a918021179d8528c0108baec294600851e7414a300428eba0a51802195d96618c0108baed28c60084d57610630042aaba88318021c5550418c0109aaec10c60085557508630043a2a9043180210f9d0650c01087ae8328600846e721943004236b90ca18021479d0650c010a3ae8328600854e7219430042a6b90ca18021569c0650c0108bcec2a0600845d7615030042a7390a818021535c8540c0108bcec290600845d76148300428f3a0a418021475d0520c010ca8cab08600845d76944300426abb08218021555d4410c010e2aa820860085d170104300426abb04218021555d4210c010e8aa410860085d17008430042acbacc01802196596600c010ba2e3300600855975100300438caa08018021745c4400c010f208220060086655298620042b2ba8431002199d9421880108eee3b2a400843e74194200421eba0ca10021179cc65080108bae63284008565750842004332b284210021965943008010e92a418040086d1610c020043e010860100211d5d464c4010caacb31e20086556558f100423aba8c5880211d5da5184010cb6e6b2c200865873596100423cbb4a30802196d963044010cb6ca1822008698640c1100436431060880218dd9764440108eaeb32220084b6749911004273394c8880218dd946444010caecbb1a200869464d8d100432bb28c688021a51906344010ccecbb1220086a464d89100423abacc4880212d9d262440109cce53122008667651891004353b20c488021a91906244010d8ec631220086c463189100431a324a0880219918a5044010d60c998220086e062cc1100426b3b4608802195d963044010d28c918220086c4628c110042e93846088021359d83044010caeca1822008694640c110043623106088021ac1903044010dc0c418220085d2760c110043693b06088021b4d943044010ea6ca1822008793640c110043693206088021b41903044010f20c81822008690640c110043e1b106088021b49883044010da0c418220087c0620c1100436031060880218ed976444010c76ca322200865b65d8d100432db28c688021a61906344010cd6cbb12200866b651891004354320c488021b218c6244010d60c9b0a20086e062d85100423d3b4a288021749ce5144010
  | 1 => 0x10443a22946108221559d43084110e28a81842088744520c2104422f39cc3aa021175ce61d50108bce6312a80845d73189540422f39ec0aa021175cf60550108bee6b02a80845c735815404237b92c0aa0211b1c9605501087eecaa0a80861d5458c5404316aa2c42a021879916315010c9cc7310a80864d639885404317322c42a0219398d6215010c9ac6b10a808655639845404332b14c22a0219a58a60150108beeca98a60861d6454c5304326a9ac429821875926314c10c5cc9310a60862d649885304317322c4298218b5916214c10c9cc6b10a608635649845304332b14c2298211b9c865d0c108dae432e860846e721964304236b90cb218211d5d66190c108dee4b2a860846c725954304237390caa18211b5c86550c108eaea30a860863554185430432aa98c2a18211e5d46050c10c72a8302860846e721944304236b90ca218211d9c46510c108bce730ea40845d73987520422f398c8a9021175cc64548108bce7b02a40845d73d81520421fba2c0a90210f1d160548108bee6b02a40845c735815204237bb2a4290218b5915214810c9ac6a90a40861e6498c520430eb24c629021879916314810c3ac8b18a40862d649885204326b1cc4290218d5926114810caac7308a40863964980520422f398cba1021175cc65d08108eaeb30e840845e73196420422eb98cb210211d5d661908108bee6b2a840845c73595420422f398caa1021175cc6550810a58e4aa2840852c74549420423aba8c2a10218d5506150810ccaa430a840847975181420422f39eca21021175cf65108108bce6328840845d73194420423b388ca210211e9c065108109b0e0b18840862f655084204316b2a84210216a1c1421081087ce832e640843d74197320423abacc3990210f9d0658c81087ae832c640843f74595320421e3a2ca990210f9d0654c81087ae832a640847575185320432aa98c29902199548614c8108f2ea302640866952181320421f3a0ca190210f5d0650c8108ece2328640845e73d96410422eb9ecb208211b9cb65904108dae5b2c820845e73d94410422eb9eca208214d5c55410410c3ca8b18820861d5458c410429abacc8208214d5d654104108eeecaa0820853776550410431bbb2a820821955966310410e2aa931882086556558c410438aaa2c6208211ddd560104109c8e4b0082086d263580410428eba0a798821535c853cc410aace3a9a620845e7614d310428eba0a698821535c8534c4108beeca98620847575193210421f3a6cb108210f5d365884108bce7b2c420845d73d96210422f39eca10821175cf6508410c9ac7290420864d6354821042b2b8aa4108211d5d464084109e2e032042086556598c210432ab2ac610821595d66208410acaeb29042084777654821042b3bb2a41082199dd95208410e8cc6a9042
  | 2 => 0xa91822117dd9548c110a9ee4aa4608854c7255230442abb8aa91822187994548c110c9ccba94608870f54d4a30443862a6a518221175da528c110a3ce9294608851d7494a304422fbb2a51822147dd1528c110a38e8a9460885577154a3044327328a518221c3d50528c110e18a8294608843e74d95304421eba6ca982211b9cb654c1108dae5b2a608843f74595304421e3a2ca982211bdc9654c1108d8e4b2a608845e7614d304431a2a6c2982219914b614c110c68a830a6088657531853044332290c298221479d2530c110a3ae9298608854e7294c30442a6b94a61822117dd9530c110a3ee8a98608851c7454c30442a7b92a618221531c9530c110ab0e1328608861e65d50304422ebb4a818221479d2540c110a9ce52a0608854d72950304422fbb2a81822153dc9540c110a98e4aa060885577155030442adb82a818221479d4540c110c3cca2a0608864e65d483044387aa6a418221c3153520c1108baed290608851e74948304428eba4a418221539ca520c1108beeca90608851f74548304428e3a2a41822155dc5520c110ab6e0a90608854e751483044327328a418221c3d50520c110e18a8290608861f54980304430e2a4c01822193d4a600c110c98a5300608871b54980304438c2a4c018221d2d4a600c110e90a5300608845e7598f204430faa4c7902218715263c81108b8eab1e408861f5458f204430e2a2c79022117ddb53c81108baeda9e408845f7614f204422ebb0a7902219398f52c8110c9ac7a96408864e6314b2044326b18a5902218d15261c8110cc8a530e4088634545872044332292c3902210f9d3654811087ae9b2a408845e73d95204422eb9eca902210fdd16548110878e8b2a408845f73595204422e39aca902210f9d7644811087cea322408843e76d51204421e3b6a8902210f9d85448110878ec2a2408845e75d8d204430faa6c6902218715363481108bcea31a408861f5418d204430e2a0c690221179db53481108b8eda9a408861f64d4d204430e326a690221179d853481108b8ec29a408861f6414d204430e320a6902218bd935248110c58c9a92408864f63d49204432631ea4902218bd905248110c58c8292408864f631492044326318a4902218dd536148110c68a9b0a408865753d85204432a29ec2902219914b6148110c6ea830a408863454185204432ba98c2902219514c6148110ccea430a408866452185204430faa4c7882218715263c4110c3ea8b1e208861c5458f104432731ea5882219358f52c4110c9cc6296208864d6314b104438c2a06188221d214830c4110e30a829e20887285414b10443a4298a588221599ca5484110e28a9a9c20887145414e10443922a6a5082214d9d25284110e4ea829420887245414a10443a3a98a508221d114c5284110aaceb1842088714548c2
  | 3 => 0x516110910cc8a4b088488638549804244334294c0212211e1d5601091087ce9b2e648843d74d97324423ab8ecb992210fdd165cc910878e8b2e648843e74d96324421eba6cb192210fdd1658c910878e8b2c648843e74d95324421eba6ca992210fdd1654c910878e8b2a648847771595324423db82ca992210f9d3650c91087ae9b28648843f74594324421e3a2ca192218d152610c910ca8a7308648866452984324423a3aac2192218d151610c910cc8a4b08648863854983414432c29ec0a0a219a14b6050510c76a83028288658531814144334290c0a0a2187d526310510c38a9318828861f5458c414430e2a2c620a2117ddb53105108baeda98828845f7614c414422ebb0a620a219398f5210510c9ac7a90828864e631484144326b18a420a214d1d54110510e2ea6a088288714535044144393a928220a21c91494110510cb0a7306628863854d813144334296c098a218e150604c510cb6a630262886685218131442aa3aa6218a21c5151310c510e88a498862885d0704c43144334294c190a218e1536048510cb0a7b02428863854181214432c298c090a219ad486048510c3ea9318428861c5498c214430faa2c610a218715163085108beeda98428845d76d4c214422fbb0a610a21175d85308510c9cc7a90428864d63d482144327318a410a219358c5208510ac8ea90842887275448421443922a24210a21d1d4d2108510e88a6908428845e7598f404430faa4c7a02218715263d01108b8eab1e808861f5458f404430e2a2c7a022117ddb53d01108baeda9e808845f7614f404422ebb0a7a02219398f52d0110c9ac7a96808864e6314b4044326b18a5a02218d15261d0110cc8a530e8088634545874044332292c3a0221179cf65501108bae7b2a808846e72d954044236b96caa022117dcd65501108b8e6b2a808846f725954044236392caa0221179d76350110c3ea9b1a808861c54d8d404422f3a8c6a022187d506350110c38a831a808845e76d4d404422e3b6a6a0221179d853501108b8ec29a808846e75d894044317aa6c4a02218b1536250110c9ea7b12808864c53d8940442373a8c4a02218bd506250110c58a8312808864f531894044326298c4a02211b9db52501108d8eda92808864f63d49404432631ea4a02211b9d852501108d8ec292808864f631494044326318a4a02218d1536150110caea7b0a808865453d854044333a96c2a02219914b6150110c6ea830a808863454185404432ba98c2a02219514c6150110ccea430a808866452185404431a2a4c3982219514e61cc110cc8a530e6088634545873044332292c398221479d2538c110a3ae929c608854e7294e30442a6b94a71822147dd1538c110a38e8a9c608854f7254e30442a6392a71822187997548c1108baed2a4608854e7295230442a6b94
  | 4 => 0x9ae72a6a48854f7355352442a639aa9a9221c3d5353d4910e18a9a9ea48852e7494f5244296ba4a7a92214bdd153d4910a58e8a9ea48870f5414f52443862a0a7a92218bd9264d4910a9ce7326a48854d7399352442973a6c1a92214b5d360d4910a9ce7b06a48854d73d8352442a7b9ac1a9221531cd60d4910c3ea931ca48861c5498e524430faa2c729221871516394910c3cc9a9ca48861d64d4e524430f320a729221875905394910c5cc9a94a48862d64d4a524432731ea5292219358f5294910c3cc931ca48861d6498e524430f322c729221875916394910c6cc8b0ca48845f73582524422e39ac1292210f9db545491087cec2a2a48861f54d8d524430e2a6c6a922187d506354910c38a831aa48845e76d4d524430fb26a6a92218719353549108bcec29aa48861f6414d524430e320a6a922187d936354910c38c9b1aa48861f6418d524430e320c6a92218bd936254910c58c9b12a48864f63d89524432631ec4a92218dd936154910c68c9b0aa48865763d85524432a31ec2a9221179cf60549108bae7b02a48863864d81524432c31ec0a92211bdd95214910a5ee8a90a48852c7454852442a7b9aa429221531cd5214910a5ce9310a48852d7498852442a739cc429221535ce62149108bce6308a48845d73184524431732ea8292211b5da5414910a9ce72a0a48854d739505244237bb2a82922153dcd5414910a98e6aa0a48862e65150524432732ea629221c3d535314910e18a9a98a48846d7694c52442973a4a6292214b5d253149108deeca98a48852f7454c52442963a2a629221939945314910e1ea8298a48870c5414c5244316b20c829221539cc6414910a9ae6320a4885657119052442b4b80c829221595c46314910acce2218a4885657110c52442a739ec029221535cf6014910a5ee8b00a48852c7458052442a7b9ac029221531cd6014910a5ee8880a48852c7444052442a7b9a2029221531cd10149108bce7b2e848845d73d97424423ab8ecba122117dcd65d09108b8e6b2e848845e73d96424422eb9ecb212211d5c765909108bee6b2c848845c73596424422f39ecaa1221175cf65509108bee6b2a848845c73595424423bb8acaa12211edc16550910a5ce5aa2848852e74d49424422f39eca21221175cf65109108bee6b28848845c73594424423bb8aca21221179cc65109108bae6328848852d72150424422f3acc62122187d526310910c38a9318848845c7558c424430faa2c6212218715163109108beeda98848845d76d4c424422fbb0a621221175d85310910c9cc7a90848864d63d484244296ba0a4212219398c5210910c9ac6290848852e7550842442963aa84212218b9954210910c58caa10848870f53508424438629a84212211d9d66110910c68a9308848866452984424423a3aac2212218d1
  | 5 => 0x874563d4821843b1386a410c21789c05208610968e8b00430863654584408422ebb4a918421175da528c2109aaec20c610871754106308426abb04318421d1d48218c210caca6b08610845d76950308422ebb4a418421355d8410c210e2ea820861084d57608430843a3a904218421999496108210caacb31e21086556558f108432cb2cc7884219659563c42108bce7316a88845d7398b544428f39cc5aa221475ce62d5110c5ec5316a88851e73d83544428eb9ec1aa2214b9cb60d5110a5ae5b06a88851f73583544428e39ac1aa22187d526395110c3ea8b1ca88862f5498a5444317aa2c52a2219398e6295110c9ac7314a88864e6358a5444326b1ac52a2219998961951108bee6b04a88845c73582544430fb26c6aa22187d906355110c5ec9b12a88864f63d89544432631ec4aa2218bd906255110c9ec6312a88864c63189544432bb1ec2aa2219518f6155110ccec5b0aa88866462d85544422f39ec0aa221175cf6055110cb0c7b02a88866862d81544421fbb2a82a22147dcd5415110a38e6aa0a88852f725505444296392a82a221479ce6415110a3ae7320a88852e729905444296b94c82a221179cc61151108bae6308a8885357118c544428f398c42a221475cc6215110c5ac4310a88853571188544429cb80c42a221479cf6015110a3ae7b00a88851f73580544428e39ac02a2214bdc96015110a58e4b00a88854e7295353442a6b94a9a9a2153dc954d4d10a98e4aa6a68861e64d4e534430eb26a729a218bd526294d10c58a9314a68864f5398a5344317aa2c529a218b1516294d10c9ea6b14a68862e6498a5344316b24c529a218b9916294d10c5ac8b14a688636645865344333312c329a210f9db5454d1087cec2a2a68862f54d8953443162a6c4a9a218bd506254d10c58a8312a68861f64d8d534430e326c6a9a218bd936254d10c58c9b12a68864f63d895344317b20c4a9a218b1906254d10c9ec6312a68863464d855344332316c2a9a218e1936054d10cd0c5b02a68845f7654c534428fba2a629a21471d15314d10a9ee4a98a68854c7254c534428f3a4c629a21475d26314d10a9ce5318a68854d7298c534430f32ea829a21175da5414d10a9ce52a0a68854d72950534422fbb2a829a2153dc95414d10a98e4aa0a68861e6515053442aab88c829a21555c46214d10a3ee8880a68851c744405344237396cba1a211b5cb65d0d108dee4b2e868846c725974344237396cb21a211b5cb6590d108eae3b2c868846f725964344236392cb21a211b9cb6550d108dae5b2a868846f725954344236392caa1a211ddc56550d108f6e0b2a868846e72d944344236b96ca21a211bdc96510d108d8e4b28868863454984434432a29cc221a211d1d56110d10c68a8b08868845e73993524422eb9cc9a9221539ce54d4910a
  | 6 => 0x2c426c382c62162117dda5310b108baed298858845f7654c42c422ebb2a6216214b5d25210b10a5eeaa10858852d7550842c438729a8421621c354d4210b10b50e0a10858843e7419732c421eba0cb996210f9d2654cb1087ae932a658854c7254d32c432ca98c0996210f9d3650cb1087ae9b28658854d7294c32c432b29ac219621175d663107108beeab18838845d7694c41c422fbb2a620e21c594d4110710e2aa6a0883886595398231c432d29cc018e21175d663087108beeab18438845d7694c21c422fbb2a610e21d194d2108710e8aa6908438845d7598f40c422fbaac7a0621175da53d03108beeca9e818852e72d5240c421f3b4a8a0621175d763503108baea31a818845e7694d40c422e3b2a6a06219394f6250310c9aa7b12818862e5418940c4316aa0c4a06219394c6250310c9aa6312818865653d8540c432aa9ec2a06218d9506150310c6aa830a81886565318540c432aa98c2a06210f5db5410310a5ce5aa081886565358730c422ebb6a918621539cb548c310a9ae5aa4618845d7615230c422ebb6a518621479d3528c310a3ae9a94618845d7614a30c422f3b4a6986219554f614c3108baeda98618845d76d5030c42a7396a818621535cb540c3108baec2a0618845d76d4830c428f3a6a418621475d3520c3108baec290618871b5410030c422ebacc79062117dd563c83108baed29e418845f7654f20c42973a6a510621175d763483108baea31a418845e7694d20c430fb24a6906218719253483108b8eca9a418861f6454d20c430e322a6906211b9da5248310c58c9292418862c6454920c432b29ec2906219554f6148310caca630a41886555318520c4333290c2906219954861483108daeda90418852e74d4820c43a5a906010621179ce62d52108bae7316a90843f765505484338b0cc1a9c2117dd95314e108dce5b2c870846d72d964384237394caa1c211b5ca6550e10a3ce9a9a8708657531854384237390ca21c211b5c86510e108bce7326a50845d739935284237bb2a429421179cf65d0a108bae7b2e850845e73d96428422eb9ecb21421179cf6550a108bae7b2a850845e73995428422eb9ccaa1421179cf6510a108bae7b28850845e73194428422eb98ca214213c1c56010a1087ce9b2e650843d74d97328421f3a4ca994210f5d2654ca10a9ce5a9a650865753185328421f3a0ca194210f5d0650ca1087ced2a2830843d76d50418423abb6a820c212d5db5410610b64e1aa0830853576d50418431abb6a820c21cc9c35410610b64e02a083087175498c418432ab2ac620c21c5d5163106109c8e4b00830845e7694d318422ebb6a618c211b9da52486108daeda9043084f170190218432ab2ac610c211d5db52086109caeda9043085e270d4821842b2bb6a410c21995db5208610e8cc7a90430
  | 7 => 0x218041d1544210c020b92e0108601055975980300832cb2cc018041725ca600c020ab2ea20060107195410030082e4b908018041e2108400c0208daed29440104797694a200832db2c609004196d943048020d30c818240106d0610c12008317b2ec8900411b5d6644802095ce932240104e6719912008317b28c89004193d976348020d18c9b1a401064f6518d2008346320c69004199d976148020d48c9b0a4010667651852008353b20c290041a91906148020d8ec630a40106c4631852008316324a090041aa1933048020dc0c398240104ce768c12008327b2c6090041a31923048020d88c318240105ca708c120082673b0609004193d943048020d18c818240106c4610c120083543206090041b81843048020b94ec18240106ca760c12008365b286090041d2d943048020f16c818240106ca640c120083643206090041e21903048020d10c818240107c3610c120083643086090041f01843048020d80c2182401063b65d91200831db28c89004196d976348020cb6ca31a40106986418d2008354326c490041729ce5248020ce6cbb0a4010673651852008358320c290041b418c6148020dc6c430a401064e6398b54c4326b1cc5aa6219398d62d5310c9ac6b16a9886566398754c432ab1cc3aa6219998a61d5310ccac530ea98852e72d5254c4297396c8aa621179cc62553108bae6312a98843f7655054c433930ac1a9e21539cb5494f10a9ae5aa4a78861d6419253c42a7390c929e21535c86494f10aace2324a78851e7418a53c428eba0c529e21935886294f10aace2314a78851e7418653c428eba0c329e21539c86194f10a9ae430ca78851e74d8253c428eba6c129e21539cb6094f10a9ae5b04a78845e76d5153c42a7396a8a9e21535cb5454f108bcec2a2a78855b7059153c430eb20c8a9e2156dc16254f10c9ac4312a78851f7458153c428e3a2c0a9e2153dc96054f10a98e4b02a78845f7654c53c4237390cb21e211b5c86590f108dce532a878846d7299543c428e3a2a6a1e219654c6050f108dce5b28878846d72d9443c428eba4a621e219594d6110f10c3cc929ea58861d6494f52c430f322a7a96218759153d4b10c3cc931ea58861d6498f52c430f322c7a96218759163d4b10c6cc930ea5886356498752c432b31cc3a96219558e61d4b10a5ce9a94a58845e7319152c422eb98c8a96214b9d36254b108baed298a58845f7654c52c4237bb2a429621179ce65d0b108bae732e858845e7319742c422eb98cba1621179ce6590b108bae732c858845e7319642c422eb98cb21621179ce6550b108bae732a858845e7319542c422eb98caa16219694f6050b10cb4a6302858845e73d9442c422eb9eca21621179ce6510b108bae7328858845e7319442c422eb98ca216214b5ca5410b108baeb318858845f7558c4
  | 8 => 0x53c8120e60a828e40907505314720482b338ca910241c31535388120e18a829c409072454d462048393aa0a310241c91505188120e8ea628c40907445314620482a73ac6110241c31523088120e88a3184409054e750c220483862a06110241d114430881208bce7316a81045d7398b540822f398c2aa041175cc615502087eecaa0a81061d5458c540831aaa2c22a041879916315020c9ac7310a81065663984540832ab1cc22a0418d9916115020cacc6b08a810655635845408333312c22a0419c58660150208beeca98a61061d6454c530832aa9ac229841875926314c20c5ac9310a61063664984530831ab24c2298418d9916114c20c6ac8b08a610656635845308333312c2298411d9c465d0c208eae232e861047671196430823ab88cb218411b5d66290c208eee2b2a861047471595430823b388caa18411d5c46550c208daea312861062d541894308326a98c4a18411e5d46050c20c72a8302861046e72194430823b388ca218411d5c46510c208bce7b2c841045d73d96420822f39eca21041175cf6510820a5ae4aa0841061e5458c420830eaa2c6210414b5d66410820a5aeb2a0841046f765504208297bb2a8210418bdd95410820c9acb318841070d5498c4208326b2ac621041c355163108208deeab0084104e471580420836531ac021041475d053cc820aaae229e641054e72d4d320822f3b0a699041475d0534c820aaae229a641045f7654c320822f398c8a8841175cc64544208eeeca88a21063564544510832ab1aa22884117dcd65504208b8e6b2a821045e73195410822eb98caa08414d1c55450420c5aa83128210534745454108332312a2a0841179cf65104208bae7b2882104d87058c410831bb2a82208418d5954110420b60e0a08821043f74595310821e3a2ca988410f9d0654c42087ae832a621064d531893108332312a2988419c544604c4208daea324421065563944210832ab1aa2108413a5c06408420acaeb3084210567765442108333bb2a210841d198d5108420e8ac6a8842104ac74580210836531ac010841179ce64940208bae7324a01062d5498a4008296ba885200418bd9442900208bce6328801045d731944008296ba884200418b5944210020c9aa7314601051e74996300828eba4cb18041559c6658c020aaae332c601055a70196300822f3b0a918041175d8548c020aace22a46010555711523008327b2cc518041175da528c02099aec214601054d7510a3008386aa08518041335d8218c020e8aa210c601043e74194300821eba0ca18041479d0650c020a3ae832860105567119430082aab88ca18041569c0650c0208bcec2a0601045d7615030082ab388a818041555c4540c020c98cab10601045d769483008266bb08418041535d4420c020e1aa821060105c9701083008266bb04
  | 9 => 0xee8b28629043c7459431483162a4c418a419314e620c520c58a8b106290666621443148332b10a218a419c1466088520c70a9b02429065853d81214831c2a0c090a419614c6048520ce6a2302429061f5498c214830e2a4c610a4187d516308520c38a8b18429045f76d4c214822ebb6a610a4117dd853085208baec298429065663d44214832ab1ea210a41c9d512108520e48a890842907475348421483a229a4210a41179d663d0120c3ea931e809061c5498f404822e3aac7a024187d5163d0120c38a8b1e809045f76d4f404822ebb6a7a024117dd853d01208baec29e809062c5498b40483162a2c5a02419598f51d0120caac7a8e809065663147404832ab18a3a02419998851d0120ccac428e809045e73d95404822eb9ecaa024117dcd65501208b8e6b2a809045e75d8d404830faa6c6a02418715363501208bcea31a809061f5418d404830e2a0c6a0241179db53501208b8eda9a809045e7614d404822e3b0a6a02418b1536250120c9ea7b12809064c53d894048317aa0c4a02418b1506250120c9ea6312809064c53189404823b3aec2a02418dd536150120c68a9b0a809065753d85404832a29ec2a02411d9d46150120c6ea830a809063454185404832ba98c2a02419514c61501208eceda8a809065763d45404832a31ea2a024199d8b5150120cc8c5a8a809047676145404832bb18a2a02419518c5150120ccec428a80906646214540483162a4c5982419314e62cc120c58a8b166090666621473048332b10a398241479d2538c120a3ae929c60905567194e30482aab8ca71824147dd1538c120a38e8a9c60905577154e30482aa38aa71824187997548c1208baed2a460905567195230482aab8ca91824117dd9548c120a9ee4aa460905577155230482aa38aa91824187994548c120caccba8c609071754d46304838a2a6a31824195994518c120e2ea828c609071454146304821f3a6ca982410f5d3654c12087ee8b2a609043c74595304822f3b0a6982418b153624c120c58a8312609064f531893048333b10a29824199188514c120a3ce9298609051d7494c30482ab38ca618241555c6530c1208beeca98609051f7454c304828e3a2a61824155dc5530c120aa8e2a98609061e65d50304822ebb4a818241479d2540c120aace32a0609055571950304822fbb2a81824153dc9540c120aaee2aa060905547155030482adb82a818241479d4540c120c3cca2a0609065665d44304838baa6a218241c5153510c120cacca288609071754144304838a2a0a21824187d52600c120c38a9300609071b54980304838c2a4c018241d4d46600c120ea0a3300609061f5498f204830e2a4c79024187d5163c8120c38a8b1e409065663d47204832ab1ea3902419598c51c8120caac628e4090718540c320483a82886190241c615
  | 10 => 0x65853181424830faa4c621241871526310920c3ea8b18849061c5458c424822fbb6a621241175db53109208beec298849045d7614c42482963aa8421241c3d4d4210920e18a6a10849065853983324831c2a6c0992418e150604c920cb6a6302649054c754c832483862a26419241721c1320c9208bce7326a29045d7399351482ab39ca9a8a41555ce54d4520aaee6aa6a29055473553514838baa6a7a8a41c515353d4520a6ce929ea2905357494f514829bba2a7a8a414d1d153d4520e2ea829ea2907145414f514831bb24c9a8a41559ce64d4520aaae7326a2905567310b51482aab9885a8a41c950842d4520a6ce9b06a29053574d8351482ab39ec1a8a41555cf60d4520aaee6b06a29055473583514830faa4c728a41871526394520c3ea8b1ca29061c5458e514830f326a728a41875935394520c3cc829ca29061d6414e514831b326a328a418d5935194520cacc7a8ca29065563d46514821f3b6a8a8a410f9d85454520c3ea9b1aa29061c54d8d514830faa0c6a8a418715063545208bceda9aa29061f64d4d514830e326a6a8a41179d85354520c3ec829aa29061c6414d514823bbb2a228a414ddd15114520a68e8a88a2905577354451482aa39aa228a418d99754145208eaed2a0a2905567395051482aab9ca828a411ddd95414520aaee6aa0a29055473550514831b328a828a41959975314520e2ea9a98a29071454d4c514823abb4a628a414d9d25314520a6ae9298a2904777654c514829bba2a628a414d1d15314520cacca298a2907175414c514838a2a0a628a418d5906414520aace6320a2905557319051482b2b90c828a415c5c06414520acae4318a2905667210c51482b2b908628a415cdc14214520ae0e0a10a2905567310851482aab988428a41c95084214520ae6e0990a290570704c851483a29906428a41559cf6014520aaae7b00a29053774580514829a3a2c028a4155dcd6014520aa8e6b00a29053774480514829a3a24028a4155dcd2014520aa8e6900a29045f73597414822e39acba0a4117dcd65905208b8e6b2c829045e73d95414822eb9ecaa0a414d9c75450520a6ce9a8a829045f73594414822e39aca20a41179cc65105208bae6328829053571150414822f3acc620a4187d526310520c38a9318829045c7558c414830faa2c620a418715163105208beeda98829045d76d4c414822fbb0a620a41175d853105208dceb310829062c5498841483162a2c420a419598f5110520caac7a88829053574144414832b318a220a419558c5110520cccc4288829066562144414829b3aa8220a414d1d54110520c6ccaa08829063465504414838ba9a8220a41c514d4110520c70a9300829067051980414821fba2cb98a410f1d165cc52087ee8b2c629043c74596314821f3a6ca98a410f5d3654c52087
  | 11 => 0x88327a98c498c413a5c06408620c9acab1843104e576d4421882f1386a210c41789c05108620958e8b00431062e54588408822ebb4a918441335d8428c220e1ea8214611045d769463088266bb043184419394d620c2208baed2a061104cd761083088387aa08418441175da510c22099aec108611064d6598f2088326b2ac7904419659663c8220cb2cab1e411045e73987544822eb9cc3aa241479ce61d5120a3ae730ea89063761987544828f39ec1aa241475cf60d5120a6ce3b06a89053571d83544828fb9ac1aa241471cd60d5120c3ea931ca89061f5458e544831baa4c32a2418dd516195120cacc730ca890655639865448332b14c32a2419598d6195120caac6b0ca89045f73582544822e39ac12a24187d936355120c3ec831aa89064f63d89544832631ec4aa2418dd936155120caec7b0aa89065463d855448333b16c2aa2418dd906155120caec630aa890654631855448333b10c2aa241179cf60551208bae7b02a89065863d81544833830ec0aa2410fdd95415120a3ee6aa0a89051c73550544829bb8aa82a2414d1c55415120a3ce7320a89051d73990544829b38cc82a2414d5c664151208bce6310a89045d731885448296b90c62a241479cc6115120a3ae6308a89052d72184544831ab08c22a2414e5c06115120a3ce7b00a89051d73d80544828fb9ac02a241471cd6015120a6ee2b00a8905347158054482ab38ca9a9a41555c654d4d20aaee2aa6a69055471553534830f326a729a41875935394d20c6ea930ca69063454986534832ba9cc329a418dd516194d20c68a8b0ca690657535865348317322c529a418d9926194d20c6ac930ca69066562986534831b322c329a418d5916194d2087cedaa2a69043e76151534831baa6c2a9a418d1536154d20c6ea830aa69063454185534830fb26c6a9a41871936354d20c58c9b12a69063764d85534831a326c2a9a4195d8f6154d20c6ec830aa69063464185534832bb18c2a9a4199d886154d20c70c9b02a69067061d81534822fbb2a629a4147dd15314d20a38e8a98a6905577154c53482aa38aa629a41479d26314d20a3ae9318a6905567198c53482aab8cc629a41879975414d208baed2a0a6905567195053482aab8ca829a4117dd95414d20aaee2aa0a69055471550534830f328a829a41535c86414d20a9ae4308a69051f74480534828e3a24029a411d9c765d0d208eae3b2e869047771597434823a38acba1a411b5cb6590d208ece3b2c869047571d96434823bb8acb21a411d1c56590d208ece3b2a869047571d954348237b92caa1a411ddc56550d208e8e2b2a869047b70595434823b38eca21a411d5c76510d208eee2b2886904747159443483162a4c421a419314e6210d208d8eab10869062c54588434831c2a4c1a12419614f6050920c76a83028490
  | 12 => 0x29e41559c46294f20aaae2314a79051e7418653c828eba0c329e41539c86194f20caac230ca79051e74d8253c828eba6c129e41559c76094f20aaae3b04a79045e76d5153c82ab38ea8a9e41555c75454f208bcec2a2a79055b7059153c830eb20c8a9e4156dc16154f20caac230aa79051f7458153c828e3a2c0a9e4155dc56054f20aa8e2b02a79045f7654c53c823b388cb21e411d5c46590f208ece332a87904757199543c828e3a2a6a1e419654c6050f208ece3b28879047571d9443c828eba4a621e419394d6210f208baeb318859045f7558c42c822ebb4a62164117dd95310b20e1ca6a10859070d5350842c832ca9cc1196419694e600cb20c3cc929ea39061d6494f51c830f322a7a8e418759153d4720a6ce9a8ca39045e7319151c822eb98c8a8e41175da53147208beeca98a3904777654451c822f39ccba0e41175ce65d07208bce732c839045d7399641c822f398caa0e41175cc6550720cb4a7b02839065a5318141c822f39eca20e41175cf65107208bce7328839045d7399441c829ab8ca820e41175d663107208beeab1883904d87058c41c822fbb4a620e41175da53107208beeca98839045d7654c41c829aba4a220e414ddd54110720a6aeaa0883907165350441c838aa9a8220e416c1c14110720aa8e2a9a63906595318131c821f3a6ca18e410f5d3650c720aaae3298639064e5358831c822ebacc610e4117dd563087208baed298439045f7654c21c83a329a4210e41d154d21087208baeb31e819045f7558f40c822ebb4a7a064117dd953d0320a6ce3aa4819043e7695140c822ebaec6a0641175d463503208bced29a819045c7654d40c832729ec4a06419354f6250320c5ca8312819062d5418940c8327298c4a06419354c6250320caca7b0a819065553d8540c831b2a0c2a06418d5506150320caca630a81906555318540c821ebb6a8206414d9c75410320c9ca6b16619045d76d5230c82ab38ea918641555c7548c3208baec2a4619045e7694d30c8326a9ec498641175db530c3208baedaa0619055671d5030c82aab8ea818641175d8540c320e36a8200619045e73987548822eb9cc3aa4410fdd95415220cd2c5306a71045f7654c538823b38ecb21c411d5c76590e208ece332a871047571995438828f3a6a6a1c4193d4c6250e208ece2328871047571194438821f3b4a8a14410f5db5410a208daedaa085104ad76d5042882d5386a8214414b5db5410a20c5aedaa0851072a70d5042882d5380a821441c3d526310a20c9acab18851070f5458c428827238ac021441179da534ca208baeda98651047776544518822f39ecba0c41175cf65d06208bce7b2c831045d73d96418822f39ecaa0c41175cf65506208bce7b28831045d73d944188274392c020c410f9d365cc62087ae9b2e631055671d4d31
  | 13 => 0x5148430e8aa4a8a42184d975d81210c32cbaec090861365d46048430d94a430242186c952181210c369288c090861b45446048430da64230242186ca21181210c26d384ca10861175da6508430cb4e1328421849e74194210c24eba0ca10861369c065084308bcebb20421845d75d90210c26db82c810861361c164084308bcea320421845d75190210c26d380c810861365c06408430c9acb908421865565884210c2e2b94421086133dd92108430c9aca90842185c870484210c26bbb24210861955952108430ba0e090842185c776484210c363bb24210861b1d952108430e8cca90842186c565484210c3a2b2a4210861915952108430f86e090842185c470484210c3e03824210861701c1210843093ee8b00421849c74580210c30f322a928061539c85494030a9ae42a4a01855671152500c2aab88a928061939895294030cacc2a8ca01861f64992500c22ebb08528061c350842940308baec20ca01871541106500c22ebb04328061d14842194030d32c8324a0185ca72152500c2e4b90a928061749c45494030ba2e22a4a0186c96218a500c2cd3a0a528061665d05294030ba4e2294a0185d17114a500c26dbb28528061361d94294030f1284214a0186d161186500c2cd3a0a328061665d05194030b94e428ca0185c972146500c26dbb28328061361d94194030f228220ca0184db76486500c26c3b24328061f048421940308beeab24801845d7598a400c28eba88520061175d66190030a3aea20c801865965942400c28ebae812006193d976250030c9eca312801865765d85400c363b16c2a0061b118b6150030caeca30a80186c762185400c362310c2a0061b2d8a5050030d90c528280186d361941400c36830ca0a0061b218b4050030da0c3a02801861f65901400c34631480a0061a5186405003099ce432880184cd72194400c26b388ca20061355c465100309b4e0328801845d75990400c30e32aa820061475d44210030d1ac4210801859970108400c28eba88220061a55844110030b32e020880184d976940400c32cb2ca020061665d25010030a3aeba00801859974900400c24fbb2802006147dd54010030b18e4a00801859471500400c26dbb28020061721c94010030ba0e2a00801859b76500400c34dbb2802006166dd54010030e36eaa00801878b72500400c2cc3928020061e21c94010030b10e4a00801879371500400c2cc38a8020061e41c54010030b20e2a00801864e6398b54c8326b1cc5aa6419598e61d5320caac730ea9906666298754c832b31ac3aa6419558d61d5320cccc4b0ea99053671d5254c829b38ec8aa641179cc61553208bae630aa99043f7655054c8335312c1a9e41559c75494f20aaae3aa4a79061d6419253c82a7390c929e41559c46494f20aaae2324a79051e7418a53c828eba0c5
  | 14 => 0xe1328841845d76994420c32d384ca21061359c465108309aae232884184da70194420c30eb2e8421061935964210830b1ae9210841849f76508420c30eb2a8421061661c1421083099eeca10841864d65508420c2e4382842106163dd94210830d1eeca10841868f65508420c38732a8421061a35954210830e1acaa10841860d65508420c3c5b828421061631c14210830f10e0a10841858870508420c26db82c221061361c161108309aee2b0084184d471580420c26c382c928861361c16294430ba4e1a8ca21861c64551510c2aa38aa8a8861931895254430aa8e2a92a2185d270d45510c347324c428861a35926214430d1cc8b10a21868d64588510c30eb26a2288619358b5114430d2ac9288a2186c562944510c22fbb2a228861875915114430c9ac4a88a2184d776544510c34ab22a228861b15895114430aaeeca88a21865776544510c38b322a228861955915114430e2ac8a88a21861564544510c3a3312a228861955895114430e8ac4a88a21864562544510c32aa8cc028861a69926014430d32c9300a2186ca62980510c364b14c028861d45466014430da4a3300a2186d151980510c26d384cba0861339c865d043099ae432e82184da70197410c30e32aa9a0861369c2659043099ce432c82184cd72196410c26d380cb208619519551904309b4e132a82184cf72595410c266392caa0861339c8655043099ae432a82184da70195410c30e32aa8a0861651c554504308bcea312821845d75189410c32a32aa2a0861651d15150430e2aa8a8a82184d975d81410c32cbaec0a0861365d46050430d34a8302821869954181410c369288c0a0861b45446050430da682302821869a41181410c26d384ca20861175da6510430cb4e132882184ce72194410c266b90ca20861369c065104309b6e0b1082184d870588410c30eb2e8220861955964110430b2ae9208821849f76504410c30eb2a8220861661c141104309aeeca08821865565504410c2e8382822086165dd94110430d2eeca08821869765504410c38b32a8220861a55954110430e2acaa08821861565504410c3c9b828220861651c14110430f20e0a08821859070504410c267b92c020861331c960104309b4e132e421849e74197210c24eba0cb90861369c065c84309b4e1b2642184d970d93210c22f3a8c990861175d464c8430c98caa9642184da70996210c24f3a0cb10861275d065884309b4e032c42184da70d92210c26cb86c910861179d464884308baea324421865465546210c26d384ca9086127dd16548430938e8b2a421849e74195210c24eba0ca90861369c065484309b4e132242184d970991210c22fbaac890861171d564484309b6e0b2242184d870591210c22f3a8c890861175d46448430c98caa9242185c471549210c32a32aa290861711c9
  | 15 => 0xb070504410c26cb86c998861339c864cc43099ae4326621861c64553310c22eba8c91886133dc9644c430998e4b2262184db70591310c22e3b2a89886187191544c430aa8e2aa2621864c62549310c2aa38aa498861339cb640c43099ae5b20621855575984310c2abbb2a21886195dd9510c430caec8a88621865564544310c32ab12a218861279d063c843093ae831e421864c6354b210c24f3a0c710861275d06388430ca8c6a8c421843f74595210c21e3a2ca908610f9d0654843087ae832a42184d97098d210c24fba2c690861271d163484309b6e0b1a421864c63549210c2b238aa4908619518d5148430ac8e4a8a42184d973d81210c22ebaec61086199d952108430ccaca90842185e070484210c30f3228728061875526390030b50e4a0080185b071500400c267396c998061335cb64cc0309ace3b2660184d571d93300c22ebb4a7180611e5da538c0308baeb322601845f75591300c267b92c898061331c9644c0309aee2b2260184d471591300c2cd386a92a061361c162950309b0e0b0ca81859a70d51540c22fbb2a82a06127dd95415030a3eecaa0a81861f76550540c386aa4c42a061875516215030e1aa8b10a81864f54588540c3472a2c42a061935516215030d1aa8b10a81860d54588540c38aaa4c22a061b198a6115030d8ac5308a81861d54584540c38aaa2c22a061b19896115030d8ac4b08a81865754584540c34b2a2c22a061955516115030d2aa8b08a81861554584540c30eaa4c02a061c65526015030d94c5300a8186c962980540c36930cc02a061b45866015030d34a9300a81869954980540c26c382c929061729c352948309b0e0b0ca41861c64551520c2a6392a8a9061729c35254830c3ac9a90a41868d64948520c22fbb2a42906187591521483099eeca90a41868d64548520c2a7bb2a42906193dd95214830e1cc8a90a41864d64548520c386b22a429061835915214830d2cc9308a41869564984520c3a2a94c229061935496114830d2cc8b08a41869564584520c3a2a92c22906195d496114830d8ca4b08a41865552584520c362a92c229061915496114830c9aa5300a41869a64980520c34cb24c029061d254a6014830da4c3300a4186d161980520c365294c029061b254a60148309b4e132e84184d671197420c26ab88cba1061369c065d0830c38caaa684184da70996420c26b388cb21061355c465908309b4e032c841864c6554a420c26d384caa106135dc565508309a8e2b2a84184d671195420c26ab88caa1061369c06550830c38caaa2841858c72551420c32632aa4a1061631d15250830e1aa8a92841845e75185420c22eba8c2a1061365d76050830cb2ebb0284184d975181420c34d2a0c0a1061a65506050830d94a430284186c952181420c365a10c0a1061a690860508309b4
  | 16 => 0xc3a2b2a4210c61711c1210863093ee8b00431849c74580218c22ebacc520461475d442902308baeb30c811851d75106408c327b2ec4a046193d946250230caecbb0a81186c762d85408c362316c2a046195d946150230d8ec430a81186c462185408c34631480a0461a51864050230a3aea210811868d62108408c28eba88220461a5584411023093eeca00811858c72500408c2ca38a802046136dd94010230c9ec7b12a89862f64189544c327b18c4aa26195d8f6155130ccec5b0aa89866462d85544c31bb20c2aa26195d8c6155130ccec430aa89866462185544c334316c0aa2619c187605513087eecaa0a89852c72550544c29a38aa82a2618e15160d0d30c3ccaa18869846f76548524c2963a2a429261591c552149308eee2b28849847471594424c296b90a821261179d66310930c3ea8b18849864d63d48424c296ba0a4212614b9d54210930a58eaa10849864e654c8324c23bbb2a228a614d1d15114530ac8e4a88a29846f72594414c236392ca20a614d5c454105308bceb318829861f5458c414c32ab1ea220a614d5d05110530a6ceaa08829853475504414c32b32a6218a610fdd16508530878e8b28429845e7598c214c326b1ea410a61595c45208530caac7a88429856572144214c2b33aa4210a61591d52108530c3ea8b1e809861c54d8d404c317aa0c4a02618b1506250130c6ea830a809863454185404c2a7b92a918261531c9548c130aaee2aa4609855471552304c21fbb2a82a0618b5516215030c6aa8b08a81862e64588540c32731ac42a0619998a6115030ccac5308a81863664584540c32b31ac22a061999896115030ccac4b08a81854d72152430c2aab88a92186117dd56090c308bcec2a2861854d72151430c2aab88a8a1861475d66410c30a3aeb2a0861845f76550430c28fbb2a82186187dd95410c30c3aa8b10861861d54584430c22fbaac021861871914354830a98e4a1aa41846f76548520c316b22a4290619954961148308eee2b2a841847471595420c23b388caa10611d5c46550830a58e4aa2841861d5418d420c2963a2a4a10619318d52508309b2e7b02841862f65508420c316b2a84210616a1c142108309b2e1b2664184d671193320c26ab88c9990618719154cc8308baea32464184d771591320c26a38ac89906136dc1644c8308b8ecaa2641861c64551320c2a6392a899061359c7640c8309aae3b20641854d75988320c2a7bb2a41906193dd9520c830c9ec8a90641864d64548320c326a92c219061871914354430aa8e2a1aa21864c624c9510c2aa38a64a88611ddd95114430c6ac8a88a21866562544510c237b92caa08611b1c965504308dce432a821846d72195410c29a38aa8a0861875506350430a68e8a8a821865463545410c26cb9ec0a08618dd954110430c6acaa0882185
  | 17 => 0x946187193544ca30a9ce5aa2651854e76949328c3273b4a499461359c7640ca309aae3b20651847776544518c237396cba0c611b5cb65d06308dce5b2c831846d72d96418c267390c998c61335c864cc6308beecaa663184cf72591318c266392c898c6187193544c630aace3aa2631855676945318c32b3b4a298c61339cb640c63099ae5b20631843e74d97218c21eba6cb90c61279d063c863093ae831e431843e74d96218c21eba6cb10c61279d0638863093ae831c431849f7458d218c24e3a2c690c6187951631023099ce5b2661184cd72d93308c26b38ec998461355c764cc230b34e1aa4a91851d76d52548c30ebb6a92a461479c35495230e34e1aa4a91859a70d51548c22fbb2a82a46127dd95415230d34a9300a91869954980548c30f326a9a9461539cb54d4a30b94e1a94a51854d76d4a528c326bb6a529461539c35294a30e94e1a94a5185ca70d49528c22fbb2a42946133dd95214a30d94a5300a5186c952980528c26b38ecba1461355c765d0a309b4e132e85184da70197428c26b38ecb21461355c76590a309b4e132c85184da70196428c26b38ccaa1461355c66550a309b4e132a85184da70195428c22f3a8c2a1461175d46150a309b4e1328851865a70994428c26b388ca21461355c46510a309b4e0328851849f76508428c267bb2842146163dd94210a30d1eeca10851870e65508428c386b2a8421461631c14210a309aee2b0085184d471580428c30f326a9a8c61559c754d4630c9cc5a96a31855671d4b518c2e9386a328c61555db5194630caaeda8ca31855670d46518c3a9386a328c61749c351546308beeca88a3184d776544518c36928cc028c61b4546601463099ce5b2e83184cd72d97418c26d384cba0c61369c065d063099ce5b2c83184cd72d96418c26d384cb20c61369c0659063099ce532a83184cd72995418c26d384caa0c61369c065506308bcea312831845d75189418c26d384ca20c61969c2651063099ce432883184cd72194418c26d380ca20c6127dd941106309aeeca08831859776504418c34bbb28220c61c59954110630e2acaa08831859470504418c267b92c020c61331c9601063093ce9b2e431849d74d97218c26d384cb90c61369c065c86308bcea326431845d75193218c24f3a6cb10c61275d365886309b4e132c43184da70196218c22f3a8c910c61175d4648863093ce932a431849d74995218c26d384ca90c61369c065486308beeab22431845c75591218c26db82c890c61361c164486308bcea322431845d75191218c26d384ca10c61969c2650863093ce8328431849d74194218c26d380ca10c61179d764086308baebb20431845e75190218c22eba8c810c61369c064086309b2e032043184cf76484218c26bbb24210c6171dd92108630d8eec908431874665484218
  | 18 => 0x2d0140ea0a628e80a0760521474050387a98a520281c314c5290140e48a5a8c80a071753146405038a298a320281c9d485190140e48a428c80a045f7654c5310326a9ac4298819554d6114c408bce630aa42045d731855210237bb2a4290819358d5214840ccaa4b08a42064d639484210326b1aa4210814b5d66210840a5eeca90842062f76548421038731aa421081c358d5210840968e2b00842069a63580421023bb8aca990811d1c5654c8408ece232a642047571195321030e322a6990818b191524c840cd2a4302642045e73189511022eb98c4a88811ddd95114440caac6a88a22066562544511032ab1ca2208819558d5110440a6aeb308822053776544411031bbb2a220881c598d5110440e2ac6a8882204ac72580411034d31ac0208811bdc9654c4408d8e4b2a622046e721953110236b90ca9888187191534c440c68c8a8a622067151181311022fb9aca90881171cd65484408bce632a422045d731952110316322a490881591c55248440c68c8a8a422056472545211022f39eca10881175cf650844087aebb2042204b970190211026c382c61088199d952108440ccaca90842205e070484211021ebb4a9200811e5da5490040c3ecbb1a802061f6518d4010317b2ec4a00818bd946250040d1ec6312802068c63189401031bb2ec2a0081a918b6150040c6eca30a802069763185401034a318c2a0081a9d886150040d48c430a802059a73951401032db2ec6a008196d946350040cd6cbb12802066b651894010355b20c4a0081b218c6250040ce6cbb0a8020673651854010359b20c2a0081b418c6150040dc0c430a802064e6398b54cc32731ac5aa6619598e61d5330cccc530ea9986656298754cc32b31ac3aa6619998961d5330ccac4b0ea99852e72d5254cc29b38ea92a6614b9cb6455330a6ce3b22a99843f7655054cc2973a6a529661599c75294b308deeca90a5984767199442cc23ab8cca216614b5ca5410b30c3aa9318859852d7494842cc32731aa4216614bdd54210b30a5aeaa1085985a87050842cc29b3a6a328e61599cb51947308eeeca88a39846e7299441cc236b94ca20e614d5c65410730c3aa931883985357494441cc32b31aa220e614ddd54110730a6aeaa0883985b07050441cc21f3a4ca10e610f5d26508730acae3290439864e6354821cc2b2b94a210e619598d5108730aceea90843985657548421cc2f03824210e618755263d0330c3ca831a819862e5418940cc316aa0c4a06618d9506150330c6aa830a81985a87250040cc2d838a80206610fdd95415230c72a8302871845e76951438c28f3b4a8a1c61879da5450e308baedaa0871846f76548528c23b38ecba14611d5c765d0a308ece3b2c851847571d96428c26b388c999461355c464cca308beecaa665184d771591328c26a38ac89
  | 19 => 0x7316a2a05557398b5150333b14c5a8a81559cc42d4540aaae6216a2a07254210b51502ab39ec1a8a81555cf60d4540acce5b06a2a056572d8351502abb9ac1a8a81551cd60d4540c9ea7314a2a064c5398a5150327a9ac528a819314d6294540c9cc7a94a2a064d63d4a5150327318a528a819358c5294540cacc7a8ca2a065563d465150333316a328a819958b51945408bceda9aa2a045e7614d5150327a9ec4a8a819314f6254540c9ea6312a2a064c5318951502373b6a4a8a8193d8f5254540c98c7a92a2a046e761495150327b18a4a8a819318c52545408eeeca88a2a05577354451502aa39aa228a8159dc95114540ac8e4a88a2a065665d4c515023abb4a628a81599ca5314540acae5298a2a04777654c51502b3b92a628a81591c95314540cacca298a2a066665d4851503a3a9ea428a81d114f52145408eaed290a2a05567394851502aab9ca428a811ddd95214540aaee6a90a2a0554735485150333328a428a81d1d4c5214540e88a6290a2a05357418c51502b9b828628a815c1c14314540e2a86218a2a05357418851502ab398c428a81555cc6214540ccac4310a2a05717018851502b9b828428a815c1c14214540aace6210a2a0555731085150392a108428a814d9d03214540a6ae8190a2a055673d8051502aab9ec028a8155dcd6014540aa8e6b00a2a05677258051502b2392c028a8155dcd4014540aa8e6a00a2a05677250051502b23928028a819c1466090540cb0a7b0282a066852d81415032c298c0a0a819a1486050540ce6a230282a045f76d4c415022fbb0a620a819398f5210540c9ac7a9082a064e631484150326b18a420a819598f5110540caac7a8882a071753504415038a29a8220a81c9d494110540e48a4a0882a046f725973150236392cb98a811bdc9658c5408d8e4b2c62a046e72d953150236b96ca98a811bdc9650c5408d8e4b2862a061e6414c3150317320a418a818b590520c540c6cc828862a063564144315022fb9acb90a81171cd65c85408bee6b2c42a045c73596215022f39eca90a81175cf6548540acce3a9242a056672d45215022fb9aca10a81171cd65085408bce632842a045d73194215021f3acc810a81179d663085408b8eab1842a045f76d4c215022ebb6a610a8117dd853085408baec29842a064e63d482150326b1ea410a818b9905208540c5ac829042a064e631482150326b18a410a81595c45208540cacc7a8842a065563d44215031b320a210a818d5905108540cacc628842a06556314421502b2b90a210a81599d52108540ac8ea90842a066665484215033232a4210a81d1d4d2108540e88a690842a066852980215033828cc010a819398f52d0140c9ac7a9680a064e6314b4050326b18a5a02819598f51d0140caac7a8e80a065663147405032ab18a3a0281d214c5
  | 20 => 0xd6494c31d02aab8ca618e81179ce65c87408bae732e43a045e7399621d022eb9ccb10e81179cc65487408bae632a43a065a53d8121d032d298c090e81179cf65087408bae7b2843a045e7399421d022eb9cca10e81175d663087408beeab1843a04d87058c21d022fbb4a610e81175da53087408beeca9843a045d7654c21d02b2b8ca410e81595ca5108740aceea90843a05657548421d03a329a4210e81d154d2108740bc0e090843a045f7654c5390237bb2a429481875956310a4095aeda9085205aa70d4842902d5380a4214812d1c56010a408ece3b2e652047571d97329023bbb2a228c8187595631064096aeda8883205b270d4441902d9380a220c812b1c960106408dce5b2e632046d72d97319022f39ecb90c81175cf65c86408bce7b2c432045d73d96219022f39eca90c81175cf65486408bce7b28432045d73d94219025cb80c810c812e1d16008640c3acb31e812061d6558f409032cb2cc7a04819659563d0240c9ea7314a6a064f5358a535032ba9cc329a8195d4d6194d408beeca98a6a054f7254c53502a6392a629a8155dc55314d40aa8e2a98a6a051d74188535028eba0c229a819614e6090d40cb6a630286a05987050c435022f39cc3a9281175ce61d4940acce329ea4a05657194f52502b3b8aa7a9281591c553d4940a9ce730ea4a054d739875250333b0cc3a9281539cf60d4940a9ae7b06a4a056671d8352502b2b8ec1a928153dcd60d4940a98e6b06a4a064e63d4a5250326b1ea52928195d4e6194940ca8a730ca4a066752986525032ba9ac3292819514d6194940ccea4b0ca4a045e76d4d525022f3b0a6a928195d4f6154940ca8a7b0aa4a065753185525032a298c2a92811bdd95214940a9ee6a90a4a054c7354852502b3b8aa429281591c55214940c9ccba98a4a046d7694c52502b338ca629281595c653149408deeca98a4a05677154c52502b238aa629281939945314940a5ae8318a4a056b7050c52502b43828629281c350c4314940a5ae8308a4a054e7318452502a6b98c229281995846114940ad2e0308a4a054e73d8052502a6b9ec02928153dcd6014940a98e6b00a4a05677158052502b238ac02928153dcd4014940a98e6a00a4a066852982425032c29ec0a12819614c6050940cd6a430284a045f76d4c425022fbb0a6212819398f5210940c9ac7a9084a070f53508425038629a84212811ddc565cc9408e8e2b2e64a047771596325023a38acb192811d9c7654c9408eae3b2a64a047771594325023a38aca1928187990530c940c5cc829064a062d64148325022f39cc5a8a81175ce62d4540acce529ea2a05657294f51502b3b92a7a8a81591c953d4540e8ea7a96a2a074453d4b51502ab39ca5a8a81555ce52d4540aaee6a96a2a05547354b51503a3a98a5a8a81d114c52d4540aace
  | 21 => 0x7333b6ca90843595d66448421aceeab224210dc77359121086e239ac89084378dc16448421bc0e0b224210ea56419121086e3398c890843715cc64484219ccedaa24210dc673d5121086e2b9ea890843399d85448421e4aa82a24210dc67315121086e2b98a890843789c05448421bc2e02a24210d657598d21086b3baac69084369dd16348421b48e8b1a4210de37058d21086f0382c690843b158c63484219cceda9a4210dc57594d2108763b2ca690843d1d965348421b8ce129a4210f477554d2108763b2aa690843d1d955348421e8ca8a9a4210f445454d21086e2382a690843399d85348421b8ce629a4210d667590d21086b2bac869084339dd943484219c8eca1a4210ce67610d2108672bb08690843719cf6048421b8ae7b024210d657598121086b3baac09084369dd16048421b48e8b024210dc77358121086e239ac090843b194c6048421d8aa63024210ce776487500876331a43a8043b158d21d4021e8aa690ea010ce47648650086f03824328043179ce64940218bae7324a010c5f73592500862e39ac928043569c36394021ab4e031ca010e1f6494d500870e324a6a8043569c25354021c3ec8a9aa010e1c6454d50086ac382a6a8043391d92154021d4ec890aa010ea4644855008763b1a42a8043b118d2154021e8aa690aa010de070485500871cb80c8a804387d936354021c38c9b1aa010e1f6418d500870e320c6a8043175da5314021c3cc9298a010e1d6494c500862fbb2a628043879915314021c3ac8a98a010ce77648450087533224228043a95912114021d8cc6908a010ec563484500863dbb2a0280438e5915014021a9ce4324a7a054d7219253d02ab388c929e81555c46494f40a3ce8314a7a064d6218a53d02ab388c529e81555c46294f40a3ce830ca7a054e7218653d02a6b90c329e81955846194f40a9ce5b04a7a054d72d8253d02ab38ec129e81555c76094f40ab6e0b12a7a064d6218953d02adb82c2a9e81955846154f40a9ee4b02a7a054c7258153d02abb8ac0a9e81551c56054f408beeca98a7a06595398343d032d29cc021e819594e61d4b40caaa730ea5a06565358752d032aa9ac3a9681599c75294b408bce630aa5a045d7318552d022ebb4a62968117dd95314b408deeca90a5a045d7598c42d022fbaac621681175da5310b408beeca9885a070e5350842d0386a9a8421681531c9534cb40cb2a630265a047671d9432d023ab8eca1968187592530cb40a9ae529865a064e5398b51d0326a9cc5a8e819394d62d4740c9aa6b16a3a056672d4651d022f398c4a8e81175cc62547408baed298a3a045f7654c51d023bbb2a228e81175d663107408beeab1883a045d7694c41d022fbb2a620e81c594d4110740e2aa6a0883a05547154d31d032ca98c098e811b9cb650c7408dae5b2863a061
  | 22 => 0xa43561c15390d218d8eab148690ce47158a434863a3aac321a43391c96190d218dee4b2a8690c7771595434863db82caa1a431e1c16550d218bced29a8690c5c7654d434868e3a2a6a1a43561c15350d218dae5b288690c7571d94434863db82ca21a431e1c16510d218bce63288690c5d76d4c434871a2a2c3a12439514d61cc921c58a8b168290c5f73595414862e39acaa0a439314d62cc52187ee8b2a6290c3c74595314872db82c7a82431edd95014121a70e8a80a090d5873540504862fb9ac828243171cd64141218bce131ea810c5c7058f5408726b1cc5aa0439558e61d50218bee6b06a810c5c73583540862fb9ac12a043171cd60950218bce7b02a810c5d73d81540861fbb2a82a0438e55160150218bce1318a810c5c7058c540872d31cc02a0439658e6015021cb6e7300a810e5873980540862fb9ac02a043171cd6015021c74c8b00a810e5a63580540872cb1ac02a0439a9896015021ce4c2b00a810e5b73580540872c39ac02a0439a1c96015021ce0e2b00a810d5a7015253086acb80a929843875906494c21a9ce4324a610d5671192530868f3a0c529843475d06294c21a3ce830ca610d1d74186530868f3a6c129843475d36094c21a9ce5b04a610d5671d82530862f3b6a8a9843179d85454c21ab4e02a2a610d597015153086a6392c8a9843551c56454c21ab6e0b22a610d5870591530870eb20c8a984347dd16054c21a38e8b02a610d4c7258153086aa38ac0a984317dd95314c218f4e032e8610c79701974308637390cb218431d9c46590c218f6e0b2a8610c7870595430868e3a2a6a18439354f6250c218daea3128610e4d531894308672b88c4a18439554f6150c218eaea30a8610e55531854308672b90c2a18431e9c06510c218f2e03288610d1d7494c4308636bacc421843395c66210c21c9ca6b108610c75759844308672b94c2218439594d6110c21c6aa930c8410e5553986420872aa9ac321043179cf65108218bae7b288410c5d7598c420862fbaac62104317dda53108218baed2988410c5f7654c420862ebb2a621043c394d4210821e1aa6a108410e5553586320861f3a6ca190430f5d3650c821c9aca9906410e56535843208762992c2190438b5526290421c9aa73148210e4d5358a410862f39eca20843175cf65104218bce73288210c5d73994410862f398ca20843175cc65104218baeb3188210c5f7558c410862fbb4a620843175da53104218beeca988210c5d7654c410878b29a8220843c554d4110421c9aa6b146210c3e74d94310861eba6ca188439394d620c421caaca9886210ec5624c43108636bb4a5108431d5da5288421c9ecb29a4210e4f6554d21086e33988290843715cc4148421caecb29a4210e576554d21086e33988490843715cc4248421ccaebb2a4210ce670d952108
  | 23 => 0x14131878e8b10a098d5a70cc8504c6aa38a6428263561c13214131ab4e1188a098e4e6358b540c732b14c3aa0634b9cb5495031a5ce5b22a818c3f76550540c71aaa4c3218634b9d352948318deeca90a418c7b70595420c63c382caa1063175d76350831a5ae52a08418e1d5498c420c66ab8cc6210634b5d25210831c9cc6a908418d2f75508420c696baa842106317dd56390431c3aa93188218d4d72d53310c62ebb4a7188631d5da538c4318bce1b2a6218c5e76d51310c6a6b96a898863555d4414c431e2aa820a6218d5575d0d310c6aabac64988631bdc964940318d8e4b24a018c3f7458a500c61e3a2c528063569c331940318b8ec98ca018d58704c6500c63dbb2a0280639998961d53218bee6b06a990c5c7358354c862fb9ac12a643171cd60953218bce7b02a990c5d73d8154c861fbb2a82a6438755163153218bce1318a990e1e6458c54c862e382c62a6439358e6215321cccc4b08a990c5f7358054c862e39ac02a6439998961d4f218beeca98a790e1d6454c53c870eb24c629e438b5926214f21c6cc8b08a790e666258453c863d384caa1e431e5c26550f21c3ca8b188590e1d5458c42c871b2a2c221643475d053ccb218bcec29a6590d1d7414d32c862fbb2a6196438b5506250721c9aa63126390c5e7399250c862eb9cc9286431edd95014321ccac530ea910c5f73583548862e39ac1aa44317dcd60952218b8e6b04a910c5e73d81548862eb9ec0aa4430fdd95415221c3aa8b18a910c5e7098c548870f322c62a443171c16315221caac7308a910e6562984548862fb9ac02a443171cd6015221ccac530ea710c5f7654c538870eb22a629c43875926314e21c5cc8b10a710e35649845388732b14c229c431e9c26550e218f2e132a8710e3554185428872aa98c299443879516310621c3aa8b188310e2e54588418868eba0a798c43179d8534c621a3ae829a6310c5f7654c318862f39cc928443175ce64942218f6eca80a110c5f73583544862e39ac1aa24317dcd60951218b8e6b04a890c5e70d8d544870fb20c6aa243179c06355121c98c7b12a890e5463d85544862f39ec0aa243175cf6055121cb6c7b02a890e5863d81544872d39ec0aa243965cf6055121c76c8302a890e5b63181544872c318c0aa2439ad886055121ce6c2302a890e5b73181544872c398c0aa2430fdd95415121a38e6aa0a890d3870550544862f384c62a243171c163151218bee6b00a890c5c73580544870eb98c8a9a43871936354d21c58c9b12a690e3464d85534871db26c0a9a438e1936054d21c76c8302a690e3864181534872db18c0a9a439ad886054d21ce6c2302a690e5b73181534862fbb2a629a43471d15314d21ab0e0a98a690c7a70d97434863cb86cba1a431e9c36590d218f2e1b2c8690d1d73152434868e3a2a721
  | 24 => 0x9928220cb4764c9411065b3b064a08832d5d83250441b2ce7b028220d9573d81411069abacc0a08834ddd56050441b2ee6b028220d947358141106d3b92c0a0883691c96050441d2ca63028220e9553181411065bbb283a8083a598d41d4041d2ac6a0ea020f1553507501065a3b283280836c1c14194041ab4e1b1ca020d5a7018e501062f39cc528083175ce62940418bee6b14a020c5c7358a50106ad384a6a8083561c15354041c9ca7b12a020e4d53d895010727298c4a80839354c6254041968eca0aa020e9763505501074a31a82a8083c554d4154041d4ec4a0aa020ea46250550106d838282a808393d8f6254041c98c7b12a020e4f631895010726318c4a8083175da53140418beeca98a020e4e539885010726a9cc4280839394d6214041c9aa6b10a020cb776504501074b31a8228083a558d4114041d4cc4a08a020ea562504501063dbb2a0280839a5895014041cacc6b0ea998c6f7258254cc636392c12a6630fdd95415331c5aa8b10a998e2e6458854cc72731ac42a663999896115331a9ae42a48798c5e7615143cc6a6b90a8a1e638d9516110f3187ee8b04a598c3c7458252cc70e32286a96631bdd95214b31c5ac8a90a598d2c7255142cc6963a2a4a1663355cc6150b31c5ecaa108598e2d6550842cc66a38ac899663361c1644cb318bcedaa26598d4c7255132cc70eaa0c6a0e63475d06394331a9ae431ca198e1e6450e50cc6ac3828728663939893294331ab0e0994a198c7b7654050cc72ab1cc3aa4630fdd95415231c6aa830a8718c6f76548528c70eaa2c620c63569c331942318f6eca80a118e2f64189544c727b18c4aa263935cc6255131cc8c5b0aa898e6b62d81544c734316c0aa263965cf6055131c76c8302a898e5b63181544c735b10c0aa2639a1886055131ce6c2302a898e5b73181544c61fbb2a82a2634b1c95415131a70e0aa0a898c6f72580544c636392c02a2638d15161d0d319a8e2b148698cd671982434c68f3aec8a1a63479d25450d318bcec2a28698d1e76151434c70f3b0a8a1a63359d46150d31cacea30a8698e1c54181434c637bb2a4292634b1d15214931ad0e0a90a498c3f74580524c61e3a2c0292631edc165109318f0e0b288498d2d72150424c70faa2c6212638715163109319a8e2b188498e4d63d48424c696ba0a4212639358c5210931a5ceaa108498d2c75508424c62f3aec999263351c564cc9318beecaa66498d4c72553324c6ac382a999263359c660cc9319a8e2b226498cd870591324c6a6392a899263561c1544c931a9cebb126498d4e76149324c7273b0a499263359d4614c931cacea30a6498e4c52181324c70e2a2c7a0a631edd95014131a70e8a80a098d6872540504c637b92c8282631b1c96414131ab4e1218a098d547150c504c6ac38286282630fdd162
  | 25 => 0x54109320caa6bae86990654d9d351944328eeeca88a21947771592500ca3a38ac928065569c332940328b8ec994a019558704ca500ca1fba2c3280650f1d161940328f6eca80a01945f7654c53d0726a9ac429e8317dcd6094b418b8e6b04a5a0c5e73d8152d062eb9ec0a96831bdd95214b41c9ac6a90a5a0e4d6394842d0726b1aa421683179ce62943418bae7314a1a0c7b7654050d062fbb2a629c839354d6214e418bee6b04a520c5c73582529062f39ec0a9483175cf6054a418deeca90a520e4d63548529062f39cc528483175ce62942418f6eca80a120c5f7654c53506a6392a629a83561c15314d418bee6b06a4a0c5c735835250637bb2a429283531cd5214941ad0e0a90a4a0c5e7098c525062e382c62928317dcd60149418b8e6b00a4a0cb47159332506a6b98a5992832d1d161cc9418f6e0b2864a0c7870594325063dbb2a028283561cd5014141ad0e4a80a0a0c5f73588505062e39ac428283539c86494c41a9ae4324a620d1e7418a5310726b10c529883559c46294c41a9ce430ca620d4d72186531068f3a6c129883539cb6094c41a9ae5b04a620d5671d82531068e3a2c4a9883551c56254c41ab6e0b12a620d58705895310726b10c4a9883471d16054c41a9ee4b02a620d4c7258153106aa38ac0a988317dd95314c41caaa6b0e8620e5653584431074aa1ac22188317dcd60948418b8e6b04a420c5e73d81521062eb9ec0a9083175da53148418beeca98a420c6f76548521072d29cc0290839654e6014841cb4a6b00a420e59535805210734a92c0290839554e61d0841caaa6b0e8420c5d7598c421062fbaac621083175da53108418beeca988420f0e535084210786a9a84210831edc1654c8418f0e0b2a6420cb571191321070fb22a69908387191534c841a98e4a9a6420e5553d85321065aba0c2990839554c614c84196ae33206420e1d6494c32106a6b94a6190832d5d2610c841caca6b086420c3d76952411063abb4a92088387d965350441c3ecaa9a8220e576594d411072bb2aa6a0883659cc4250441b2ae62128220e3575d95411065b386caa08838d9db6550441a6aeb31a8220d377558d41106d3b92c6a0883691c96350441b66e0b1a8220db07058d411074ab18c6a08832d9db5350441b2aeb29a8220e976594d411078bb2ca6a0883659c25350441e2eeaa9a8220e976554d411078bb2aa6a0883651c1535044196cec29a8220d967314d411069abacc4a08834ddd56250441b2ee6b128220d947358941106d9b82c4a08836c1c16250441b2ce63128220d95731894110752b10c4a08832d9db5250441b2ce7a928220d9573d49411078aa9ca4a08832d9d85250441b2ce62928220d9573149411078aa98a4a0883c95485250441b64e02928220db170149411069b3ae64a08834d5d7325044196eec
  | 26 => 0x52b08c2a1085639cf6050842b1ae7b02842152d759814210a97baac0a108563dcd6050842b18e6b0284215a7715814210ad238ac0a1085a394c6050842d1aa630284214af7650b5110b4731a85a8885a358d42d4442e1aa6a14a22145f735825110a2e39ac128885179cf60544428bae7b02a22145d7694c5110a2fbb2a6288852bdd94214442d1cc6a10a22168d635085110b86a9a84288851ddd95114442e4a84a88a22165a539805110b2ca9cc028885aa50a6014442cb4a6b00a221659535805110b54a12c0288859c545601444295eeca16a02168e6350b5010b46b1a85a8085c354d42d4042958eca14a0215a87050a5010aad386c728085569c063940428bce730ca02145d739865010a2fb9ac328085171cd6194042ab4e129aa0215587054d5010a563b284a8085a3d8d4254042d18c6a12a02170d535095010ad438284a80859594f6154042caaa7b0aa0216a542d855010b2b298c2a80859554c6154042d4a8430aa02165763d855010b2a31ec2a808595d8c6154042ca8c630aa02145d7694c5010a2fbb2a6280852bdd94214042d1cc6a10a02168d635085010b2b29cc2280859554e6114042d4a85308a021656535845010b2aa9ac228085a950961140428f6eca80a021671615405010b2731ac5aa6651ddc560953328e8e2b04a99943f7655054ccb1aaa2c22a6659958a6115332c6cc8b08a9996566358454ccaaab88a921e65179d85450f32aaae22a2879962e5458843ccb0eaa0c6a16650fdd16094732878e8b04a39961c6450d51cca3bbb2a228e658d5915114732a3ae831ca1995557118e50ccb0f3228728665561c143943328f6eca80a19964d6398b548ca1fbb2a82a4658b5506250e32c3aa8b18851947776544518caad38665284651edd95014232c6ec830aa89965763185544cb33b10c2aa265955cc6155132ce6c3b02a89967061d81544cb2cb9ec0aa2658ed906055132cb6c6302a89966b62181544cb39b08c0aa2659c1846055132cb6e6302a89943f76550544ca9a38aa82a2654e1c154151328eee2b00a89947471580544cb162a2c5a1a65331c96190d3299ce5304869951e75d91434ca8f3a4a8a1a65179d85450d32a3cec2a2869961e76151434ca673a8c4a1a65939d46250d32c38a8302869961c5458f424ca3bbb2a228a654d1d15114532ae0e0a88a29943f74580514ca1e3a2c028a651edd95014132a70e8a80a09957071540504ca3bb8ac8282651d1c56414132ab4e1218a09954c7250c504caac3828628265569c2321413287ee8b08a09943c74584504cb2b31ac3aa0659998961d5032a6ce3aa4a81953671d91540ca1fbb2a82a0658b5526290c328beeab1c841961d5498c420caaab8ea999065175da538c8328daed29c641945e70d95320ca2f3b6a899065555c7544c832a9aea212641970d
  | 27 => 0x1400000600680000000200000010012000000000000400c00000040040000000014000002000001000a00b005001c0040210000010000002000000802a002000800401000200100140160000000000006016002000400000000080040000070000024006000002800000a009002000400200400c800002200000c806c0020008deeca90a5a1c777654451d0e3dbb2a0286871ddc56094a438e8e2b04a521c6f765485290f32a92c2294871bdc960946438d8e4b04a321c77765445190f32b12a228c87535c86394243aaae231ca121d5a70d0e5090e3dbb2a0284871bdd95214943ac8e2a90a4a1d68705485250e3bb8ac0292871d1c560149438eeeca88a2a1d64725445150eb8382a228a871bdc960145438d8e4b00a2a1c7b765405050eb4392a0282875c1c55014143ab4e1a18a0a1c77715885050e3a38ac4282871bdc961141438d8e4b08a0a1c3d769524310e2ebb4a921887179c36550c43acce3a94a421c6f765485210eb3396a3288871ddd95114443ab4e121ca021c5c7650e5010eac38287280871ddc562940438e8e2b14a021c6f725865010e36392c3280871edd950140438beeca98a7a16555358453d0a2fb9ac128e85171cd60947428bce7b02a3a145d73d8151d0a3bbb2a228e859558d51147428bce730ca1a145d7398650d0a3dbb2a02868517dd95314e42caaa6b08a72145f735825190a2e39ac128c85179cf60546428bae7b02a321477765445190b2ab1aa228c85179ce61942428bae730ca12147b765405090a2fbb2a629a85551c55314d42ab0e0a98a6a145f735835150a2e39ac1a8a851ddd95114542aa8e6a88a2a1570705445150a2f384c628a85171c163145428bee6b00a2a145c735805150a3dbb2a028285561cd5014142ae0e2a80a0a145f735845050a2e39ac228285559c46494c42aaae2324a6215567118a5310aaab88c529885479d06194c42a9ce430ca621655611865310a8f3a6c129885539cb6094c42aace3b04a62155571d825310a8e3a2c2a9885531c96154c42ab6e0b0aa621558705855310b2ab08c2a9885471d16054c42a98e4b02a621557715815310aaa38ac0a988517dd95314c42c9aa6b16862164e535884310b46a1ac4218850f5da54908428daed2a4842161f6594d4210b0fb2aa6a108593d965350842c9ecaa9a842162d75d954210a57386caa10858b9db6550842a5aeb31a842152f7558d4210ad3b8ac6a1085691c56350842b56e0b1a84215a87058d4210b46b18c6a10852b9db5350842b1aeb29a842168f6594d4210b87b2ca6a1085639c25350842e1eeaa9a842168f6554d4210b87b2aa6a1085631c1535084295cec29a842158e7314d4210a96bacc2a10854bdd56150842b1ee6b0a842158c735854210ad5b82c2a10856a1c16150842b1ce630a842158d731854210b
  | 28 => 0x34021003000400000000000140040040060008000005000000403e00100680040000020070000038003002000400200000000080080000000014000001000801c0000050000000016002001002c00200500100000040080060028000001000003400400b0000018000002000000000200100000180020000008004000004000005800e00100600000000010008000014000000800c01000200380240040000000004020000000000400800700280300000000050000028001001001400600100000140000000000008018000002002c000000005000800000100380000160040000000012002005800c000000001000c03c00b0018040028006000000001001a000000001a0000028004000007000800000a010000000800600400100000020030008004014001005001c000000003800c0100000010004004000001000002a0040020024008001006800001400f0028014002002001000400400500000340060010000024000004001800000400f000000400000100280540160000030000002005000001800e007001800800a018001001c014007000001800a00c0008020000000002807400200c0028004010001000803000a001000000c0040000060010004001003000c006001000000001e00b00600000040010008004002003000000400a01d000801801200d00d002800000c003800003a0000048014000013000004400200700100100160000018014008000002800000e000000000c0020060000014000017000005000400200000000100000018014008012007000400200000080000100010058004000001002803000e000000804800c000000005c004011000000000000d0020010000006002000c0080000048000000000000000000400400180000140010158000034000004000000a0000000000004003002802c01200b0030034000000001008400e0000000000012000000000000c0000010000006004007000c000001001800001400200500180080010000008002000000000000c00100000000000030050014000005010801802400c0080000000000001000c0080070008008018000006004800400d0010000000000000800002e001001000002200400080000020090000004000003004000800e003003000000000200100380000070010004004000002000000200c001800803000000100100020130078014002009002000402600a001802400000000080000000060010000002002000000c00c0070048000002001005800800201300200000160000008010000000012000000000100000180000090028000000006000000001e0000008018002000002000000401e0008000004000000000000200000280040000130030000008003008800000a0010080008014003003006c006001000001000e00100000000020080
  | 29 => 0x200200000000020018002002000806800200100880300060000030004006000009800801c00300280100080020010024018000000800801c003008000000c0000018000000000002804804c0010020000002006000002c0040040010010002000001807001e00600780040020000008000000000001000000600200200240000050008024002004003800c00200300c000000a0050160000000000002800400200e00600000060010008000002000000804c01c0000028000000002000000400c017000800c000003000800800000200000000140000028008006009000801000000d003800800400c000000000000d005000000000100000200760000038008002000001800800000c0040004042000001000000a00100080380000060010054004000000801000001c001001800400f004800402a000002800000400f0000020002002005002c0020060030020002002008801000200100100100020050008008006000001000400000400400100020020048004006000000000c00c0080020010002000000800400000500d800000000200180040080000008008014004000801c00600100000200000000010008002003001800401a0020018004002018000000000e00000000000020010048034016009000800800200901080000060020000004002001001000800000700080180100000030000000004005800c002002002800c0000000008008000004000000402600000a8000002000000800400a000000800400000c00480000060120010000002003001000000401b001000001600d00180100000010000010000000000800c01c00000380000040000000000002006002802c00e002001805800401c0010010002001000000400e00100400180020010008004000001000000400c0010000074008005001000000e0000030010004008006800000200000080140020020018004014004001000c0080000010008004002005000000a000002001000c0190018000000000000800000c020000000400c002000801800c00300580000080080008014016004000802c0000030020000000001005803000400c005000000400000000080020020000008000000000000000c002002001400e01e0000000000001001807c00400000700580000020000000000006000002400000000280000020020048030006008002000800800000080000000000020008000003002805c00a003007800800c03a0000000000000003000400400c0000004000001005001400000000000000040020000010000001000001403a002000000001400400000000000000010000006000000800400000201a800800200200080240000010028000004003009001400400000080180000170008038000000004000000000300a000001e00101080100000000008018
  | 30 => 0x154c00040e48800000000000087a40ac000074490e00000000000000000000000000002dfc0000000c05443cb5b000000000000001328242366c0000000d3a000083c0000000314800000000001bf800032fc0002590000061c04a3bc4f1704d03251bbcf320c0883830600002dcc0003440b7b09000004120c942ec806a1a4c000000041e10901f1441ceba47801a91d58d2f3f5cd8b28bc08f00010dd3fb4230450c0003714d3100011420000a114171146465c000000000000000000000e3a00007a83088ec40dd102a00000000000cc8000000000006bb30f44b700000000000c320d9c0000000000000098400010631a0cfd31e380000020f0e2db4000163000000000002d4c58b380113e00011c4217800014380002a00000000083900000003728eee086800000005cc21900003d380a83344dc003a070839b8f0f26785691f591850000af730b086b0000eb530249853be87a731106d7156000015440002654f390000b7d30483da26fce1707f0a4507204ef27a0983411c0001864c8c42b515300011fd000001130a10190000b3300010d118fc0000000000000000028241da00000000000e842c54ae907c093e14802ea13d881305e4000000000000010913e9c0000000300000000006cc71b00000001da8b8f000022a0000000338cfd50000000000000000001f3413d123100c00000000502a1866a2a240001ec050100007f6384010b26900002b3800000002b70c34000000000015880001e680000d4521f000081b2fc8762427889a2a90e9e00009e01110aa01ac477831fc61e2a942c94048000000018015945092c4cf2007a8c300f4113614e4ad62e00cc90be121213c465f16140000000ac53f206411d900001f440003fb022d000000000001a13bbc694225087c00010bd00000000000aa73dcc00013c00003d0800035086780000004000000000200d011000402a0050008000002002002000000200700400040000050000000000002002801800000500e0000004008001000c0040070028014000008002001c01c003000001400e000016001c0040010000034006000001000000201d001800000000b000001c00a00500000080000020018004000001008000801200200000040000110098000000012003800800200e0010004000004000000c00000e0000024002017000000000a000000801400c001000001000c001000000800600300000040040070078004004002001803400a0080018028012001000002c00600d00800100040010000060000000002800000400100300040020000000000000005000000400000300100040020000010024014007000000000400f001001800000000280100080050008008020003000000800000700000180000000030010000007000000c01c00400000700080000020018012007
  | 31 => 0xd9a00000002ed02ec1f942550344000165c00002f85e028b0c532034a4211bcf7944106c10000e430560000000097c000007a391110e000000028880000000ed6000c22e222c21c00000001c4069d000112a256cf8000000f11c5c000039800035c8000000052b29544330000ec80eacf60000122300000002514aab0000eab486d13d0000d1413440000000000244411e00011d10000000467c2c1068000007fc1932f080dd29f482c00d80000a14bc61cf4a19241000044dc000000000038a4d9622ccc5948850df123c4532f5c402148c0d932a835d2d004a9129cf471c58a7c2a1c3a320d80000f3ca94127c000300ce4b16800003c6484318e0a8500009ad2d6418f00010ea26e0f440000ff518ac0000000000129400001c00002bd800016447ef2e28c9d24a83e329f90a02728000000111642300001d700003f7cb9c0cd40000000afb43e40fb251c00000006361704b4537f4000164000000005e4000058f23a033332251fa20c452d00001a33da80001a34787290ce06484c000026000035f0bc1134c1cb2c845bb0b082a415503962ca05ad2a1000016d400000000003aa00000000d152a7c7330000b3f0a9511b26b04ea34a045429110cd2e08210208103019f060729e121a000000000000003c24fb2000000012152030000e1d000000003000000000077149c00015bc5d7049c00000000001e050f10000c8d0dec8c600000004629224000000000002d506500ae1adc0000c9118c00000000000c7c26d045b264877e00000000d6c0002b100000000000000067100000000000ea621d477421201d24538db10000ac63bd8e9408040000814000253c9ec38c4d8c1a3d0bc3c0400004e417d000000001082ab012c76d000023810687020cf85df3e14bd40428637000000022ac00034f108e00000002094d6600002f5412cefc1f00000000062a0000066000000021080003730386271400024340a900000000d140000000000000000000000004440f590000000050c00046f91aa00008221c68442166483b00003630000000059107f1d5c1f4345903f28dc0001634000253878c246c3043dec43201540000a6c8f22b8c39b0000d3000000ff0000f4000000000000408000000000010673ff400039bc05400000000000000000000019b4c8f4888e6d0ea800038dc45d11a80f512ac00013ec000000055b11982e30000239138800000000000000d4345442a03704fc22bf08cc0544b2529980000448000118400043e88b200000db00002cc15e03de2ca49021aac01b1b55130320c30f000021f329420900009d82b2000012e80000000000120c0ea2834fcc130c00036208741578000000071900000000000a10128d1173c9865209d4bd603891d435fc29e0000f8b00000000000f8f19640eb3c302bb00d093a2f8c00
  | 32 => 0x892ea8b4c18390ac25280ac40d40d431840d604ac9e73ae40000f9ce3c29b400037a400037747cb2b648f73f6091e426800000003713de800043f8adb00000000000e7d000000000010e6452c7be0000000028400508a4e65171cc0a0e0462e0000f1b0000db70000000000070c040870017b828700009b023150b100004d70b790b516ac0000e1c73114cd07140cc000000000000000001520000000000001fc000489c0004420000453000024bc2110000000479000000000000d900000000000207c3c63cec0000d590792b4c8843f745a921d81b643f449e3b1cf5c16109784568d1704c401700000000000566000000000007e10394000387c9c7000056836d0afa36043db1b48f311dc87f81d4cfb6000039a05cc32840006e63528c6d000027f2e585d515d0a69217c82d0000954052c25a356064535249ab249cb6a00008581bd48d100004dd44242282bbc00000011b70ffcc45007c0003c20000046000017e022f00011df3b1472c0000000376cc6428740000c442180fecef8000016a0000c3545dcb0a00007580000000292c0000000c602cacc56000098913242a6471c72129006422850f6c27b400001790402548b5f3b08c0e38bc3522098a650d1cb6b2b7007b30e0655000097f000050000000001320a4a00000000f74fac00004780239097327800046989ba04108d6367849315d8f413fac63b00005d92310f633de00000c6c02235e87b1294039704e07d8410c44627e120b0000a0b1d7cf3a386c282018800002cc44a09785f931248d400000004841156097ce271e80e7212c82614124b5040a00ed0000e2a073000037e8f6500fc750276516017a08e31f507410574d1117485c03edc3290f982063f188ca2354deb143012c02883c22ee50e71ce0ab718607c742a46e002189a14740d8a00000000e9c4751c50e26000000034b11b40000249054cf921f9cd943bfca8e150c3650000a1345ec000355c7f400005a83e606c23a741fb331ce7542ac22126f809504dcbf828ac46b41cc7b23eecb7a3d6c9e609f90d24320c4c01a4b04082c01210b868a2b500000000071180c000000000000001fa00007990ce80002fbc0003d48000098c26600000000000c5f3c48000000023628906e300000003e94b0700008822644ee62fb03d144c40003b280000000ea543b800022d06281044e933b3c0000000000000000010840000000000000023b2c680000000000000000000006391dfc000122c83f234c24c28b8daa11e42af00000001b940001340000000000002040d734381bf000000025b00000000c9b32b0393000000012f89e237450ff1bb4abe3100c271fdc1de1b306e924884d41b74de02b40ccb4250133219800047b85f31024b2a1dbc6d810a074224200b400000001cac047219c00000000000000000000000000
  | 33 => 0x83c3731fe8ebb0438ab9033c00000002b90c8c5ec00000001998cb1091c2d6210443a0bdd0323760c764548e320000edf000000028f4bde244053b09e8dec00000b23804d7e1fac00003806a3000000000004da000002f00000003b180000000b8d3674fbe23d44f500003460000fa23db41150bc051f085400000000000a18000000000029380001da51e52b2d1e9100115838389dc25583170000ae02afc70715b40002dd00000000000205cd212240da3359d13b3bc120e000000047389d4101c4b843e000005dc2a700003ed0e7400000003ca00011cf090c09234dc5133d508621fd400034a437e00000000000dbf0ef40000c04c8106d00002380d6436a400023780000000000000000000000c4289800000000000fd800037c4f9342c861106bccc2108d02e0ac41dd0cc0000000000034991c206b4828000026c20e89e93904b7147f00003f680000000a8247609151a3039400006b20000965077050318e86b800000000000a0827d8e0f1c2c00018404920000e742630fe2260853d33944813fa8dab0000dc90000a971f700001eb0000029457231dcacc13346131494edb41490260eb511c1aa813e23f0be72bb026219109993a9c2c4422d0681a880002958beb462d19c16e832a00011ed0550000142854734945451cd4f340b7c1c6014400000000c9301915f2364000000000000000000000000113c0001cfc7670000000179463000000003468df94720c3c1e244e5072449b3b88ed110a46a625051ae0894d824408c043ca886d0c50b95081cef72ebc587417cf11000000028a877c000000029b8000000049400000c50000bcc466c000199c000000022200001961c60000395d1e63c68e90069014f00c4a253fc8a510114b9b2b28ae5375117019b8b012540531000000018b40e92e444713314000000025d00000003c784fc00000000000c10000000000000002468441000000022589d1000051a01d053530acbbd2b08594164cfe70e2511e04751110f5c3b80bcc439106469f0354b4e05ed1bd11a01e146940003bf8e5e000000022e80000000000137031c000000000000003dc80002720b4900010f30000000000000000000d342fc0000000256185c1810000000084c0002c180000000000000000000000003a5454b0000b64093832b00000000000bd908380000000000000002c25ec0000000b261a64000185000000007fb4008b552e611b50f2067e3d7504a0fe10a21e90f3500006fa41b8a981c24b1f3c4c35502f4c6c0d5d07e45bc0002024c6f020c00008cc3793390ab23a1c49c18b084f3ed0f5302c48e11f54d6b42a8a6317840000000c6914b8340000080a3c745260f540000810b5e1de4dd62f146a5000108f0000a77018cb023a7cc8a3af0b2f00000002b4400039303dc094c100303c0a629acfe92c2d0
  | 34 => 0xd7927ec0003d9ca4900003910000000000012e13588a10000ddf00000002bc834200000000000f38067c6be23a880400006cf30dc0841f74a312a7899005940b83e78be040446db1e5cf62236832041842fa2e2014c3ea842c051caee0000c1c0dd82772a8c000336000047b0da507a4759005000000006800aa8d44381c9aa4534000304400008fcfc93a480003828000041c53e0eec11601c82b21b1c97422640002b2474b0000e8a000000009b4e62000000000000000000000046402a32ec000024000000000001df42fe0a2024800000001ba000034900001e5800040a50cf00008fa46ccb2c2c64d89409d1921930db606f004648b80003fd904d000037800007850fcc38c16b11554088bbf440c00000011a7047c6c0000073b18f8ce20000ae6000000000011f30000f5f00002760000000000000000000001fe40003504cee000000000000000000000200c000069ce133efc000111400000004401ae88323414000000000000004130000000092c000174472547a84b01e9888503f508800000001e408b8399c0000634000000037003e8000000000000000e347680000000000335ca04000000040680002f60f0400000041e28f8900008450a6000000000000000a4f3eb436f00000002db00000c84f7d1ddc1aa15400fc0bec960185400000000000000000438cf910000ff1318890000009062ee8f9638b07750000b3401587a513e89e51a04690281ce9607f87841574e7100003192224e8d0000cbe00006620000d3300006771d8c6c8010c0004718d0606e000033580000000000000000028c095e1a78e2515f800032e80000000000476c0000ff000037f8fde19c0000461c00031204310794ccc19205600001140000000009f4b200d68f4a000041600011d900000003d3096716c4b360750fe10848344096465300011a100004fe427c32200006402b548010000ee03b94e3b0000bff27f4d612cf41c036b4000003c00000007d00000ac3407cb660850000000000036d45f1442c25c21b08b9000016800000000000000000000000009f30174db907e00e7000000046c46cb353c03213e45b93e700000fd40002bd465e35651731ad0c931c18cdb00000000000811000057c08ac9a320d0f9f1ef0e47000000045e115736980003fbce730db019947ac94629d4c650000000044c00025dc0002c70000000000032140001a6cbcf223c000000091f00000000000ae1000080b0c1c9f003dc4a4478cab302c0fab2d70fa6000000000009bc31e841204940000000d4e000000000000003d5c9940000f6b000000021c0000000079334c8bcd1ea800000011452e800002fe4d3800009710588f4506881fd00009211660d3d04d8cb91dec844294ca643b640003f0113930941b7000000000004a248ac0000
  | 35 => 0x4730833000100925710cc3f9893f3d68b9448190af0a303ea4728d344354dcd256427b10d109c3fec7110c983313ee088811302c71ff459215709931eac2443fe11482c38d861f6455a2e5c0003e390ae105026f10310ec401ce9833c025b000000000003ce0e880000f301e000001b10000000299d1f8000000000000000000cea00006f1302d19a000400035300000c2c0000000465000100b289c00007a0dae000000034f87ea14e8cf2285cd2b447400004d47d319ed16200006022050a5c0f100002c40e7c425400000003e233182ce32980ec00007b73d9000023744c700000000f50000455117d0000b46428c0000728f870000000000118f000014e00000000000a9000000000008000000000006a0966000028f1f800000000024000000026dc350367c00017c000043f08fe36840000000000000045100000002b5c40b38582ef000081a369000038787f102ec05b27e800000005de2ab0c1e27300003cac0000e9000023980000000b9e000002b30e411725548db009cc2f32451b01734acd34710e91ebca3c1f7c00021f828b0c9c000110c65044487391a587fc269c52a0ff400010b4861159000040e0e5d000000000010a12c3466100004a00000b232a743bc000111f1804e521c4890f43d4de70000ba138691283e043594204ced330c0004030d0d000000000000003cf000000001b224700002aa4bf61360f0045d4edd000051b000076c07e4f2c0000dce000000021b800041d404000000000000000077c00000002ca2dd40003b485a20000a2307bc59544e0000339c00000004f700009c31cb80f817a8000365437d1ab88b70cd87c90000000000046c0000000280021627d01842d48000000115d438037a106c2ac3fe800000000001bac2c600ec7650c0c83e4464b7812b8000000000004f499600000000000000313800008300002ac0000000000000000001a14000017c00009d0d2a112c00010ac2be00000001894000022800002080000000f480000000357c5100000000000057012ecc1d0fdc19b000090100005b300000004070477075cd0c44004c43d4441d0000c171ed46fc19e83c136cc74a2494000000082a0000e5023c40000000887063800019b09ef0138203027ce021a68f702628b510000d1e1fb0000000000000011990000000028c23748007d704a4c632b1ceec283ca410000b3c168c0003e5400038510580000bed0e3c957018485619451c300000002974000417447b38804cf36610d727ac09d45291440b9868e25a06d039b0ff913a46760488d04107034a10fca5f233c16928fcb052c7880510388d74578dda2bc02d8057c0000000e4817d50d400000003cb4000382d05636e883035ec00036885121cc10e4403c34e170cab6453c7c10000000000071f3a3c0000000cd00000d7700010900000
  | 36 => 0x40002a6843d286107017b4ffc0000000198ccd51534305071cd933ba8d712e1c7a233a01be462500d35bd07223fc78d00f800045b000047a00000000ebd0000893000025021a01061500e5340ed02d24e40001aa05f61e8400000003b7000004147ec8a6076c13a40d8e893e68000095c18200011181c4cfe31b585b4000000030000000000000000000000009b3404c0003c287321b4423d338400032bc9cd1f6cb813814362000093200b49ce0000e080a8cc4a0000000108000043acbda00001e6000092e031836b1f38d9c3bec8600000af10a403ef37d02f445d80000000e23000000000000000b949620000000180109d2d740000d0409b00007ee13a019826941e32e38f23343c000000000003780751d740000d249de0148000030800000000000000bf31ee00002fd446000003990000f0b400cabc432c145000041523011274190516000000048c8000263800000000001708c5719506911880d230d210233f8031012cc2e722f46af181400000000000000ed8000084c0000000370cd5100000000000ae713185d80fc8de64404f103f5093046ac5c41e4489712c4a6211600a0156438222c401907d411c0b845571a2ca9b229cd4d3e8d00a00000000000f7f257c9a83c58b923348aa81e50c75000056a1f1000009f00000000000000000026d45ce3f100000000c5d000053425245e61e2d12439a45e7021c47f3280b770528a5e32b4b143fcd1c51bccd4734e493529c051d456c2bc360c00000000ca17f04e1468803900004760f6000026c400030cc34d00000000000490485907b2154ed72e880001ee4166132ca4c2cec0642fd0000000079f3e40000083400028a0a4600e0b4b00000001e4897215b0b6103d80000000b58109c00021a4be2000046722b40d000005113e80d4b1b4c36a10100df0b6849a26e408d4388ffe24ac6c606ec6720000a3317f82e80b50a6a2700cbc2f2800046d80000000d0a37d4d62415d05e141c8bf07650f4000039f2eb416b21f51a31b0c80025d487b00000001a485050000000000006c000079e36f9159150800044a4000000000039340003918f241e745a70000fca0000114182116e277c7e400000000000a990f34a203df8bf0000000000000003334e55057057a3ac8818000010303c80000000000000007e2c449260cf04b4000048e0000000248c00b208c11b1f3080e043c4370dfc99c41a89e102242f21d14b0c0f2c97d4724000000072a0584000000000000000000000b3a18900002eac00020a400040183ec3ccc00000002791628fd2000007c358c00047fcc4616f853c39d800011585bd0000af400000000034e61431c85b1724d1b000000000006d900000002ec4000104000000003d600000003ba0489099400000000001274b1710d8c6b0f1c235448830e000035e377024a
  | 37 => 0x123d87471f0c76b00000000a3400046a4a320000e880000859016000041e0cfc2d680002bb4000000000019ac00030d894c48740000338fff0000c0840c40f3000000000000002f7c7ae13ccc54000000000000003da00001304f4b0000c583380000029c08b1330dee00950600fa00003b780000000000341c000000000000000c12f0c52200000000a44000000000000000001720ef50000e403bac79c20bcd6c390800000012173090a73000000000001280cec734000119027081ed0000b18168499a057825135204f848bc000424ceb40000fe400000000db8a5905180090000000441913c01e015b000000000000000ae000036a000000000001b88000000000023e4cdf0000cb4000000031a000000000880000000000000016951ad075800033bcdc6121c9d33b344502270000000027100007d200000000000fdc33f429a2560000000000000005d43da49c633a4b08058c6432fdc0000000a5b1ff8000000000047742fc0000000000000000000001c3c000000000000005c6000000039a8000000091244cc0000cb80000e38ada420c00031540003a90f8621e02dd303044e31443060000c3e02700001f280001bb800019cc2582680eaf0c600003ac40003cf400023a455500011f1000057737883614360f031678000344c000000000000011f63cf909900000cc2774a063708bfc460c00027d504e1af00ef1c9cc970b14eda059c00006ac16f00011d500000003a8caad0290df801940000fd00000000c5a000000000000001c981c32fed04500011dc088d149295c000062453640e800000006ac1f210c200000001d50000000000010f8bd03e10ee31408438465458300009424188000080118d0cf46c439acd1233d058e16044de43151322020000337856338a047d1528a2113fd11a06b8ae202a81b033ccdb823f46160484ea01fa071e22748a5396c82e33b060d25a8c6630fcb09000000042e8000004c000000000000005ca3944d53242c6f80000000031c186000040a3964d762ec051e46e4190479c0002e140000000000000000019d12150e9426a276ca7b43780000d0c95a1bec5a4406cfee36bc2ae38d46ca0000795048113a2984f1f0258000186cdbc02d4bbe3fdce112e4c5db00786043dd019a22c0d560e2ca053dd404f3284c1f00a4195000107c4704000188c0002ce0000301c00000000002dc01d000006a4000000000000000110d8524151d60000786044418c000000000000000000de110c00002ae80001d1000002d80001eb4000142065d0000000000000000000000000000119013b45a48831e8cbac2d5c000245010d41d8000385400000000000694c960000c7e2b7c000116899f130883d46e119327a8000431800000001263ac05181d840002da0a740ec01710934cc13e6c3a111d03fa11c8000167
  | 38 => 0xf073e3288544292107d0a7093c21cc91d0c540181a200000000000024c00047dcd84251000032685b23b50dd546440000000d6e4324aa60a389280d80c31426045232dc98b02645fb0644b243d341b93f3c9a92b040cb25e82973f40cf5458d1983cdc8350d98a3927107511fc018a055c00043642db0fe48e50000000371078f457117220190f725e416019f46652458ba800dd21e0070f8c0e2817e09043fe0ed4d54372081518d106b45e51fe07881b52360000286840d00007552f84aff0e40bf1000000034d40000b211742f4c0000a7cb843b70ff40000000266009e2574000000116538b406f38f848812b4000000110d463800043b518646586b90000e8015840cd478823e0000000342c000000034c000000036b00000001004000030922a000000003b612f4afe24a5054239c8b63d409f7445026e15cc86f0000b8328289da0f0cd003aa901734d83be30e8b6721407ed1918a8c3290c8229e8bc943411883c700000000057000012d1014df638840003e289173270000048c0001b50827216850f1b7cdf300280490ddc00001ccb600a58b3942e472f0b0c0002e940000a4c0000000d2240b000046f000048649690000e8e300518145b400009e0cce06b01ba00000000000eac00000000000e9b0f0000032d51de0f94c733be4a1e0890a9500000000000c7d11e80001b70b9945e92141670ee941d0ea93fc000033000000000bb70000f8837900002a2c0001ef46de000106f45fc4e623d0aae373cee41f343ba23b0226474d13f19bc000115c00018cc1bd45c4bd513f4d020000ad20000fe5000000000000000001180103c3882fa8000000000000000000001014052059b3b04c41443010c223000048b0cfe00000791bfc38d000000043a0000000110a193800000000000000a8f00003b226ec19236005ff39ec00044985150000f073accb1b35d40bc4118000483c00017411e127546f413b4cb20000e4e000058623b400000000003638907214482b380c47c3ebc5ae0e0d0bb0f64b3541e8bb33b2470d0000b9a17e82fd3ec06cd296019c0efcc5b13ac98612a00000000bc7364501532f4000014c00046bc00042e00003d54ecb1d18d0910f0fcd34fd03e410831e2d10000201c8d20000b9f0000b473fa08812480c1924dc0003210d6a37c800012d920a142c32c0b48cb613d07f22338dbd4144ab10c48df7215c9e32d5865c0000d52036000002b50181de8b9d1f8c0000c68b8600000000000000459c0000000000000061a00000001a5c2b302fc26b2f98f30000060f2234e9114fc24f05d40000dd49b21c8c57b3df0f064700000319c6322f7015600000210000cff000069500004b929fc10838b849800c07c213b090a00d4a0208c4549361ce5813b849105e91a82c0069c27581011dc03371958281273d21145a83f
  | 39 => 0x5e2f4868905fc96e0dc86bd3d3c80c2b7409a00006f0356c00032488e4340d22d1548a381608f5800000000e1512b0000000000016e00009802aec00600000001210e0931c86a905680001418c1a1e2000017dc0003e5c3b30000fb30000de3000000020904d22ba00001698e45167c000000000040407bf09510ca000092c0bac0000000c2d30500001f68cdc00000000000afd3e7400000000000000892000060900000000fc0530347cf4617bc71d3ec447e1b144630000a0e46103800000e7e0030e83086c2d002acd193b384db481c0001c54f0235a06a1000084e231c45900000c332ac75a2a284e014bd105000027011540150000fdb1eece5f0d505563d9806b00010f000008b5000023a000000004251f40000a8d0b2d04c37f07480e54000398cbe5474836d0d7cb27217400022ece9c13380004104924189c0004894e4f38480001e60dd31cdd1f02abc6ad2968bcb00010214394000425800043583082d8d0012c88e392100f770aa42ad43040ba1d78e4a43843e116c108515b80da38881832dd82673b400003664684240c2453f0c00021948be3568f0d0510e360ce00fe2e40a7215e40003328bb62d050a63d84ed30000c4f227c1c50490ab400000000000447280c14d39803ae308c000000044d1e08f8306980001ac021d4168b892ed401a0000000187c5e90000dd7150400005f000000006e442cc0003a8921c0000c2a480439c0a48c133a04cd339686f60000149437007d363d02026885b823888ae00980000000f490000de500005883080000320045f287c00017f519e363445c25d8d4519d49c116246ec09a06fd4208e54008031614dc79b00000001dc48df00007661770a6c2cb4be92ee054c27480ee07090050000a93349cb12159c62122f10b616fcf431e0cfc522289810ad8679125459a00007490001069000000000000000c2813042012283a090d30214eb601d91cb23ec246000047329e400000000003e640000000f1818a46860000e180000fa82cf800000000002544dff3b300004368ce6000000000004d9000065b000000000005af3dd836834ec57d105c0f43764cb8310c2ee0000d90407404d0000000000000000012311d6c819228088e131505000000000000000000000000006b51714fb905c80000000000000093b45902021518bae0bc480f42dcd7000000000000094000000000000000000000000016d0000000073c0003e350a438cc5f435800b9153813228a523300000000000000430c000000000003e48120000b0f1464000000009746e8000000046d1188000192800002dc84900000001b68e492858dcb3b0c3df198018507542bf0f48e9a0b88000000000048a80000000334000116632191940000c7b39e0b4f43ec0000d4c2893f2c6821f880000710ef30000000000093348c022c18
  | 40 => 0xda5087085d1823c54000000000024d80001354000005872900a0cfb00005aa10a8cf91018000195c0000000a680504e990000000000033f488084b37405e2138c00000011ef3d58a1b48351f90f1464f0000000449400000000482f74a522df80000000c8e3ef0000175800029d8ee7000000020dcee11d480002de4af30b9000001b43eb218c8c919a0b7234603d30000fce12300001d38ca31a600003af82c020406470e10ae4275d0db2e90000000112e00007e6213423c11a44700d2c6e710980000b80000269800000008aa0b3434f0000e24073800035a40000000000000053218c400040dc2a122b111500004970000c02000071c000003d0f901cd4814f82024509200004963261044312c70543011f20000000037000037ec5172ae0cb02ea42952e9d0a82a889bd0000dd20e985eb15fcd2e40200591390000237035c369d0f2250d03419340c81d0c760000060625ccfba000039e12b08cb293400045840000170000414c5dd28b496f252c2d127fc0000bd8b7c00009342620f2e0ed000000011cd25acf3f4484c4d01a000040f40000000000000000039900001bc8d2021fc0001470703226c140089c1052b600003865066212831d070400045a04aa3adca1241b40002d5102400006c92be40002290000000004c00000000e48197000000000000001ad80003574e2b00002d700010b407c836936c0a6f2058269139c0003cd8000123400000000000000cf600007280000cd92af40000000ceb0a0000000000000180000000000037bc9f20000000000122903c089e00004c025b400045ac0000000f283c9c0002a0450424e0ef43c144a638d0000351886a0790000000067f00000004164cf1199121837b48d03c949cb000099d00004b500007e900004df0000000000063500000003afca921c04e3d074c2523ea47cf0fa4cae2c0c0003a180000000ac000000000000d1d00002ff000000028d0d6d00012091120bd10000000252105512fc000019cb4836c8000467400000000003a151ac37c000031c457123c0c5e2980d7d30540000ee41760b64023143400019686261ce80000000398034860a3b00bc81a1c1523578a01187087707b081d27e400000005e30000d012a2028446902603f58bc01b38c780880a3e00b8cda3ae0b1d3c84528291c17400000003310953265c7402424d73000000000000001c90c79285452c2aa85b7082889124608c8153cfa125c07202f3805a1cf033910d4be83cbcf14000000009cc8a90000ab52a4400000008c336ecda01cb41d80d60e7a000000035e0d9200006e127f0000211c1f61ed90be2b78c873f64eed0000449000003c09c80000000c74000000015ac000149000039dc000000042546ec00004fc000000000000000002e9800000010161c88c26000000038c11133ca400000404
  | 41 => 0x38fc0002f90a830000000079cc0d2584ea10aa08a2000000000000000000b8c0ba40000540000000000000000002cc06490000283468088632a432d45f89194228fae00010a50b4ce8c08783af00005cb0000a712b3c0000000000000000038700003a2c7a90000a360000c1608d0c9523b82081830fc1000000000000003ef4000000000031c0c21000000000006a00000000208429412640000ad098700010861ffcdc72150000128400000000002ef05f231a80002a70000000070e3f1c8f322bc00019a400000000002be043b00002ed00004f200e800014e00002d0c00021480000a2800000000002ff88793ab80801ed07730f24418023000014503ac0000b4a00011500000000000000022540002430000062d1203778000000105b11b8e68000060b07accf7000080200009d03dbc0002ff51410a88898311cc8b000000000003b100000002db906c3c881593830c5c48982b000000002f1000046fca9646c88a3000057500011350000000000102f000048200007f32eec0000000000000074d04a8ead0000000000074f1ecc0001be4fb53570000000000000000002308e0400002ba0000299475c1ee38e108412185da2334bee0ad4000365ca3b1bdc7c5482031308c8219250092d32a0a1c37a0e5607dcc1b483000039fd0f6327ca0c2118d55333c9e43540bfa06740001ba837c2dbc41f00007de43102f9266c000337430c1da081e31b8c293bf4bdb0000000000029d3db862223e05d30b3c59600000003dc4c90122800000000002e8c5bc29505b621c426412bc61d0f81065173cb3227242bd1c101423f44c9924f485328e89fe359485c0000736000117c0c7c00041dcb4d05540000e800000000000000016c100502505e000028d4e6600000000cbcb2e44b4cfa000000000ccb65000011a4038fa42cc501e21c811000012021d300000000000000000004bc332192d12f18bd09b33e0aa12cdcaea12000001db800026b85211c280001ee8000108800025f83a932209b600010b004f0c3b23ac63d000000035d10ef39c11f534b51340678913263c1700000e0d16000000000000000000000380e43a5c00002bc0003420e5c27c50a71f189ee23bc6123bc88c120710ce10bcc342e2ce7919606bf24c46b337a908d0000000350098d2bac0000000c500000000000078001b855f26bc000000094d3108188329c52932cc0e12d882dc2c580000000f940ea03ee258ced5000000044b0c2e40f000000006a7451c4bc0000000001cf5e2d0920433500001dd801d2
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xc4314940b108050c4314540c19769c35495230c49769c35294a30c51769c35194630c29651c14210830a158119154cc830a4581d91520c830c31651c14110430a0d8219154cc430a4582d91510c430a0d8418d52c8430a158418d5188430c61651c12108430e055458a6115030e05549896115030e05545896115030e056454a6114830e06645496114830e05645496114830a158119554d0830a45811955290830a15811955450830a45811955250830a88825506050830a88845486050830e09545486050830c19651c14210830c49651c14210830a0d869954210830e0965dc14210830c0d651c14210830e09651c14210830c8b651c14210830d0a651c14210830c89651c14210830d09651c14210830c09651c14210830e05649895114430e06645895114430e05645895114430a0d8219554d0430a45821955190430a0d821955450430a45821955150430a90815506050430a90845446050430e11545446050430c19651c14110430c51651c14110430a15869954110430e1165dc14110430c15651c14110430e11651c14110430c93651c14110430d12651c14110430c91651c14110430d11651c14110430c11651c14110430a0d8419552c8430a15841955188430a0d841955248430a15841955148430ac0815486048430ac0825446048430e41525446048430c49651c12108430c51651c12108430a45869952108430e4165dc12108430c45651c12108430e41651c12108430cc3651c12108430d42651c12108430cc1651c12108430d41651c12108430c41651c12108430a0d821955410030a15811955410030c0d755884210030990815c04210030c15755844110030988825c04110030d8072dc54010030d83721c54010030d80721c54010030c15645c46494f20c15745846194f20a158694d4110720d12531c14110720b1281d50400c320c0d76d50420c220d08541c1320c920b40804c83214520a0d84195620c020a4581195620c020c0d76550420c0209c0815c0420c020c4576544210c020988845c0210c020a8986108400c020b0985108400c020d0975108400c020a8a849903048020ac2819903048020e8064d843048020e83641843048020e80641843048020c0d645c86494f10c0d745886294f10a0d8694d4210b10d0a531c14210b10b0a82d50400c310b0a84d483008310c1576d50410c210c4576d48210c210d10541c1310c510d40521c1310c510a1584195610c010a4582195610c010c1576550410c0109c0825c0410c010c4576548210c010990845c0210c010a9186104400c010b1185104400c010d1175104400c0109c1870843008010b41850843008010e41650843008010a92849903044010ac2829903044010e8064d883044010a92849883044010ac2829883044010e83641883044010e80641883044010
  | 1 => 0x2a00000002942200218011810078c12a005b2e8002a5e274ee93111ad7a473e8d00000398640000002d160971aae0000a5899000002a800ae921eaac00805215058174e2dce8002f1e4000034958f60040a34020041800c2004d974e28b4410966600a9b0162b0181842982f8000084069c03aa20028c00000000000400a29c50091b19c245b1f8b434ad4d250008500228005127000080800130f0002080000000d80000663100000aa340e0c63c002a4b0ac0026542004f00038163a8dc8ca617a444800001b8b80057038a03b57b0474003e0c800c006128f47f138f8ca6d290c48a02000017623148cc96001000090bf000b8d4005a93426590f07c007e00224ecc213001400000000004f4300092723780000b20021c0e9f478011cb912860a600000012c00480008800000000a001ca080000000017c00001680000800000c038000005000b00c00028040c060280418040500c0000000180002038400000000080804018040004010300001008042400008040208000080004038000006000000400a50805846154c42a848158c6350842a888058c635084290d859cc6150842a84835846150842aa080584615084290d859cf6050842a888054c6050842e09535096014442e21425456014442c0c7654d4254042b088054d4254042c88631c14254042d09531c14254042a508054c6154042e05535086154042aa0805086154042a48805886254c41a848258c6350441a908058c6350441915859cc6250441a84835886250441aa0805886250441d11535c05250441d21525c052504418b0805d83250441915859cf6050441a908054c6050441a488054c6254041c147654d4154041b108054d4154041e05531894154041c90631c14154041d11531c14154041ca0621c14154041928805d54210831a18805906454c21a84835906448421aa0805906448421945859cc6448421d21545c05448421a848458c6348421ac08058c6348421b418015153484218e0805d84348421945859cf6048421ac08054c6048421c18641c15354021c447654d2154021e046454d2154021b408054d2154021ca0641c12154021cc0631c12154021d41531c12154021c45625c46294f40c45725846194f40a458694d2108740d42531c12108740b088050
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x61c0a215ab0892e01803400b000580876201535095010ac0120a9a8430aa02168054c805086154042c083b100a9a82a80836009054c6250550107802a6310e0a0aa020e101d88054d2154021d0032100a9a42a8043c006454c70485500868832d298e090843a050465a531c14110720c04c32ea21080180414099694c7050842c430230cba882200600861061d650843008010
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
  | 7 => packedAt gbK7 (756+((h/14+packedAt gbK7 (672+(h % 14)*6) 6) % 56)*7) 7
  | 6 => packedAt gbK6 (58869+((h/633+packedAt gbK6 (51273+(h % 633)*12) 12) % 2279)*12) 12
  | 5 => packedAt gbK5 (419878+((h/3280+packedAt gbK5 (373958+(h % 3280)*14) 14) % 15719)*15) 15
  | 4 => packedAt gbK4 (248529+((h/1553+packedAt gbK4 (228340+(h % 1553)*13) 13) % 6767)*14) 14
  | 3 => packedAt gbK3 (12285+((h/65+packedAt gbK3 (11700+(h % 65)*9) 9) % 283)*9) 9
  | 2 => packedAt gbK2 (1090+((h/5+packedAt gbK2 (1065+(h % 5)*5) 5) % 19)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffe03ffffffffffc0fffffe07ffffff8f8ffff
  | 1 => 0xfffc07ffc07fffff03f07ff87fe0fff471e3f
  | 2 => 0xfffff80fff80fffffc007fff87ff07f87e3c7
  | 3 => 0xf0000000fffff01ffffff800007fff87f803f8
  | 4 => 0xffffffff0000001fffffffffff800007fffc00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x6029850a0491224002cb096008961088186cdb
  | 1 => 0xa54293144872448cb01542aa852a8d5343162d
  | 2 => 0x49850a269120e915554084d3504da46585a346
  | 3 => 0x8d162c58e24481de69a6d01a4471ce47e803b0
  | 4 => 0xe183060c3870e1b8e38e71c66010806f6d800
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeae8a880eae8a880eae8a880eae8a880eae8a880eae8a880eae8a880eae8a880eae8a880eae8a880eae8a880eae8a880eae8a880eae8a880eae8a880eae8a880, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12857
namespace PEqualNP.Outside.L_meta_12857
open PEqualNP.Outside.L_meta_12857.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xeae8eae8eae8a880eae8eae8eae8a880eae8eae8eae8a880eae8eae8eae8a880eae8eae8eae8a880eae8eae8eae8a880eae8eae8eae8a880eae8eae8eae8a880
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,3,35)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,3,35)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3941133032 * 2 ^ 32 + 3941116032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12857.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,3]⟩,⟨.or,[2,3]⟩,⟨.or,[4,5]⟩,⟨.or,[0,2]⟩,⟨.or,[1,8]⟩,⟨.or,[6,10]⟩,⟨.and,[1,9]⟩,⟨.and,[8,12]⟩,⟨.and,[7,11]⟩,⟨.and,[0,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941133032 * 2 ^ 32 + 3941116032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941133032 * 2 ^ 32 + 3941116032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12857

open PEqualNP.Outside.L_meta_12857 in
theorem PEqualNP.Outside.L_meta_12857 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941133032 * 2 ^ 32 + 3941116032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941133032 * 2 ^ 32 + 3941116032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
