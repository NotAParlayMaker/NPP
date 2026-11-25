import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12943.Model
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


end PEqualNP.Outside.L_meta_12943.Model

namespace PEqualNP.Outside.L_meta_12943
open PEqualNP.Outside.L_meta_12943.Model
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

end PEqualNP.Outside.L_meta_12943

namespace PEqualNP.Outside.L_meta_12943
open PEqualNP.Outside.L_meta_12943.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x41fd32083f864107fd4420ff288417e51083faa2105f54420fe28841ff41083fc82107f50420fe20841ff31083fc62107f4c420fe18841ff21083fc42107f48420fe108417e50083fe80107f90020fea0041fc40083fe60107f8c020fe98041fc30083fe40107bc8020ff10041fa20083fa40107b48020fc90041ff54c42fea9887f95310bf2a621fd54c42faa9887f15310be2a621ff53c42fea7887f94f10bf29e21fd53c42faa7887f14f10be29e21ff43c43fc87887f50f10fe21e21ff52c42fea5887f94b10bf29621fd52c42faa5887f14b10be29621ff42c43fc85887f50b10fe21621ff32c43fc65887f4cb10fe19621ff41c43fc83887f50710fe20e21ff31c43fc63887f4c710fe18e21ff21c43fc43887f48710fe10e21ff40c43fc81887f50310fe20621ff30c43fc61887f4c310fe18621ff20c43f641887f88310fe90621fc20c43f041887fd5210bfaa421fe54842fca9087f55210beaa421fc54842f8a9087fd4e10bfa9c21fe53842fca7087f54e10bea9c21fc53842f8a7087fd0e10ff21c21fd43843f887087fd4a10bfa9421fe52842fca5087f54a10bea9421fc52842f8a5087fd0a10ff21421fd42843f885087fcca10ff19421fd32843f865085f54610ffa0c21fe41843fa83087f10610ff98c21fe31843fa63087f0c610ff90c21f721843fc43087f48610fe10c21f421842fca1087fd0210ff20421fd40843f881087fcc210ff18421fd30843f861087fc8210ff10421fd20843f841087fc4210fb88421fb10843fea8885fd5110ff2a2217e54443faa8885f55110fe2a2217c54443fea6885fd4d10ff29a217e53443faa6885f54d10fe29a217c53443fe86887f90d10fea1a21fc43443fea4885fd4910ff292217e52443faa4885f54910fe292217c52443fe84887f90910fea1221fc42443fe64887f8c910fe99221fc32443fe82887f90510fea0a21fc41443fe62887f8c510fe98a21fc31443fe42887f88510fe90a21fc21443fe80887f90110fea0221fc40443fe60887f8c110fe98221fc30443fe40887f88110fe90221fc20443fe20887ec4110ff08221f610443fea8085fd5010ff2a0217e54043faa8085f55010fe2a0217c54043fea6085fd4c10ff298217e53043faa6085f54c10fe298217c53043fe86087f90c10fea1821fc43043fea4085fd4810ff290217e52043faa4085f54810fe290217c52043fe84087f90810fea1021fc42043fe64087f8c810fe99021fc32042fca2087fd0410ff20821fd41043f882087fcc410ff18821fd31043f862087fc8410fb90821fe21043fa42087f08410fa108217e50043fe80087f90010fea0021fc40043fe60087f8c010fe98021fc30043fe40087ec8010ff10021fd20043f840087e08010ff88021f710043fc20087e84010fe88021f510043f220087c44010
  | 1 => 0xc424c3fe64987f8c930fe99261fc324c3fea2985fd4530ff28a61fd514c3f8a2985f14530ffa0a61fe414c3fa82987f10530ff98a61fe314c3fa62987f0c530ff90a61fe214c3fa42987f08530ffa0261fe404c3fa80987f10130ff98261fb304c3fc6098778c130ffaa0617f540c3fca8185f95030df2a0613e540c3faa8185f55030deaa0613d540c3f8a8185f15030bf29861ff430c3fc86187f50c30fe21861ff520c3fca4185f94830fea90617d520c3f8a4187fd0830ff21061fd420c3f884187fcc830ff19061de320c3fa64187f0c830ee19061ff510c3fca2185f94430fea88617d510c3f8a2187fd0430ff20861fd410c3f882187fcc430ff18861fd310c3f862187fc8430ff10861fd210c3f842185f94030ffa0061fe400c3fa80187f10030ff98061df300c3fc60187e8c030fe98061dd300c3f260187fd5320bfaa641fe54c82fca9907f55320beaa641fc54c82f8a9907fd4f20bfa9e41fe53c82fca7907f54f20bea9e41fc53c82f8a7907fd0f20ff21e41fd43c83f887907fd0b20ff21641fd42c83f885907fccb20ff19641fd32c83f865907fd4720ff28e417e51c83faa3905f54720fe28e41ff41c83fc83907f50720fe20e41ff31c83fc63907f4c720fe18e41ff21c83fc43907f48720fe10e41ff40c83fc81907f50320fe20641ff30c83fc61907f4c320fe18641ff54882fea9107f95220bf2a441fd54882faa9107f15220be2a441ff53882fea7107f94e20bf29c41fd53882faa7107f14e20be29c41ff43883fc87107f50e20fe21c417d52883fe85107f90a20fea1441fc42883fe65107f8ca20fe99441fc32883fea3107f94620bf28c41fd51882faa3107f14620ffa0c41fe41883fa83107f10620ff98c41fe31883fa63107f0c620ff90c41fe21883fa43107f08620bf28441ff40883fc81107f50220fe20441ff30883fc61107f4c220fe18441ff20883de41107ec8220ffaa2417f544837ea8904fd5120ff2a2417e54483faa8905f55120fe2a2417c5448378a8904f15120ffa9a417f53483bea69057d4d20ff29a417e53483faa6905f54d20fe29a417c53483b8a6905714d20ffa1a41fe43483fa86907f10d20ffa1241fe42483fa84907f10920ff99241fe32483fa64907f0c920ffa8a417f51483eea2905dd4520ff28a41fd51483f8a2905f14520fa28a417451483fe82907f90520fea0a41fc41483fe62907f8c520fe98a41fc31483fe42907f88520fe90a41fc21483fe80907f90120fea0241fc40483fe60907f8c120fe98241fc30483fe40907ec8120ff10241ee20483fea8105fd5020ff2a0417e54083faa8105f55020fe2a0417c54083fea6105fd4c20ff298417e53083faa6105f54c20fe298417c53083fe86107f90c20fea1841fc43082fca4107fd0820ff21041fd42083f884107fcc820ff19
  | 2 => 0x3fc65a07f4cb40fe19681ff51d03fca3a05f94740fea8e817d51d03f8a3a07fd0740ff20e81fd41d03f883a07fcc740ff18e81fd31d03f863a07fc8740ff10e81fd21d03f843a05f55240ffa9c81fe53902fca7207f54e40bea9c81fc53903fe87207f90e40fea1c81fc43903fea5207f94a40bf29481fd52902faa5207f14a40ffa1481fe429037c85207f50a40fe21481bc42903fe65207f8ca40fe99481fc32903fea3207f94640bf28c81fd51902faa3207f14640ffa0c81fe41903fa83207f10640ff98c81fe31903fa63207f0c640ff90c81fe21903fa43207f08640bf28481ff409037e81207ed0240ffa9a817f53503fca6a07f54d40fe29a817c53503fe86a06fd0d40ff21a81fd435037a86a07f10d40ffa92817f52503fca4a07f54940fe292817c52503fe84a07f90940fea1281fc42503fe64a07f8c940fe99281fc32503fea2a05fd4540ff28a81fd51503f8a2a05f14540ffa0a81fe41503fa82a07f10540ff98a81fe31503fa62a07f0c540ff90a81fe21503fa42a07f08540ffa0281fb40503fc80a06f90140bf2a081ff53103fca6205f94c40ef298815e53103faa6205f54c40eea98815d53103f8a6207fd0c40ff21881fd43103f886207fd4840ff290817e52103faa4205f54840fe29081ff42103fc84206f90840fea1081fc421037884207fcc840ff19081fd32103f864207fd4440ff288817e51103faa2205f54440fe28881ff41103fc82207f50440fe20881ff31103fc62207f4c440fe18881ff21103fc42207f48440fe108817e50103fe80206fd0040ff20081fa40103fa80206f50040fca0081ff54cc2fea9987f95330bf2a661fd54cc2faa9987f15330be2a661ff43cc3fc87987790f30fea1e61dd43cc3f887987fd4b30ff296617e52cc3faa5985f54b30fe29661ff42cc3fc85987f50b30fe21661ff32cc3fc65987f4cb30fe19661ff51cc3fca3985f94730fea8e617d51cc3f8a3987fd0730ff20e61fd41cc3f883987fcc730ff18e61fd31cc3f863987fc8730ff10e61fd21cc3f843987fd0330ff20661fd40cc3f881987fd5230bfaa461fe548c2fca9187f55230beaa461fc548c2f8a9185f54e30ffa1c61fe438c3fa87187f10e30ffa9461fe528c2fca5187f54a30bea9461fc528c3fe85187f90a30fea1461fc428c3fe65187f8ca30ef19461fd328c3f86518770ca30ffa8c61fe518c2fca3187f54630bea8c61fc518c3fe83187f90630fea0c61fc418c3fe63187f8c630fe98c61fc318c3fe43187f88630fe90c61fc218c2fca1187fd0230ff20461fd408c3f881187fcc230ef98461fb308c3fea8985fd5130ff2a2617e544c3faa8985f55130fe2a2617c544c3fe86987f90d30ef21a61fd434c3ba86987f10d30ffa92617f524c3fca4987f54930fe292617c524c3fe84987f90930fea1261f
  | 3 => 0x8698ff50d31eea1a63fc434c7fea498dfd4931ff29263fd524c7f8a498df14931ffa1263fe424c7fa8498ff10931ff99263fe324c7fa6498ff0c931ffa0a63fe414c7fa8298ff10531ff98a63f7314c7fc6298f78c531ffa82637f504c7fca098ff54131fe282637c504c7fea818dfd5031ff2a0637e540c77ca818cf95031feaa0637d540c77aa818cf55031fe2a0637c540c6fca618ffd0c31ff21863fd430c7f88618ffd4831ff290637e520c7faa418df54831fe29063ff420c7fc8418ff50831fe21063ff320c7fc6418f78c831fe99063fc320c7b86418df94431ffa0863fe410c7fa8218ff10431ff98863df310c7fc6218fd8c431fe98863dd310c7ea6218ffd4031ff280637e500c7faa018df54031fe28063ff54c86fea990ff95321bf2a643fd54c86faa990ff15321be2a643ff53c86fea790ff94f21bf29e43fd53c86faa790ff14f21be29e43ff43c87fc8790ff50f21fe21e43ff42c87fc8590ff50b21fe21643ff32c87fc6590ff4cb21fe19643ff41c87fc8390ff50721fe20e43ff31c87fc6390ff4c721fe18e43ff50c87fca190df94321fea86437d50c87f8a190ffd5221bfaa443fe54886fca910ff55221beaa443fc54886f8a910ffd4e21bfa9c43fe53886fca710ff54e21bea9c43fc53886f8a710ffd0e21ff21c43fd43887f88710df54a21ffa1443fe42887fa8510ff10a21ff99443fe32887fa6510ff0ca21bf28c43ff41887fc8310ff50621fe20c43ff31887fc6310ff4c621fe18c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121dfaa2433f54487fca890df95121feaa2437d54487f8a890df15121de2a2433c54487fea690dfd4d21efa9a435f53487fca690df94d21fea9a437d53487f8a690df14d21ee29a435c53487fe8690ff90d21fea1a43fc43487fe8490ff90921fea1243fc42487fe6490ff8c921fe99243fc32487fe8290ff90521fea0a43fc41487fe6290ff8c521fe98a43fc31487fe4290fdc8521ff10a43ee21487fea090dfd4121fda82437b50487fca090ff54121fe282437c50487f0a090de14121ffaa0437f54087fca810df95021feaa0437d54087f8a810df15021ffa98437f53087fca610df94c21fea98437d53087f8a610df14c21ffa1843fe43087fa8610ff10c21bf29043ff42087fc8410ff50821fe21043ff32087fc6410ff4c821fe190437e51087fe8210ff90421fea0843fc41087fe6210ff8c421fe98843fc31087fe4210fbc8421ff10843f621087fa4210fb48421fa90843ff50087fca010df94021fea80437d50087f8a010ffd4f40ff29e817e53d03faa7a05f54f40fe29e81ff43d037e87a07f90f40fea1e81bd43d03f887a07fd4b40ff296817e52d03faa5a05f54b40fe29681ff42d03fc85a07f50b40fe21681ff32d
  | 4 => 0x7f90d32fea1a65fc434cbfe84997f90932fea1265fc424cbfe64997bcc932ff19265de324cbfea2995fd4532ff28a65fd514cbf8a2995f14532ffa82657f504cbfca0997f54132fe282657c504cbfea8195fd5032ff2a0657e540cbfaa8195f55032fe2a0657c540cafca6197fd0c32ff21865de430cbfa86197750c32fe218657e520cbfe84197f90832fea1065fc420cbfe641977cc832ff19065ee320cbfa6419774c832f699065ff510cbfca2195f94432fea88657d510cbf8a2197fd4032ff280657e500cbfaa0195f54032fe28065ff53d07fca7a0df94f41fea9e837d53d07f8a7a0ffd0f41dfa1e83fe43d07fa87a0ef50f41fe21e83ff52d07fca5a0df94b41fea96837d52d07f8a5a0ffd0b41ff21683fd42d07f885a0ffccb41ff19683fd32d07f865a0ffd4341ff286837e50d07faa1a0df54341fe286837d54907fea720ff94e41bf29c83fd53906faa720ff14e41ffa1c83fe43907fa8720ff10e41ffa9483fe52906fca520ff54a41bea9483fc52907fe8520ff90a41df21483fd42907f88520ef10a41ff99483fe32907fa6520ff0ca41bf28c83ff419077e8320fdd0641ffa8483fe50906fca120ff54241bea8483fc50907fea6a0dfd4d41ff29a83fd53507f8a6a0df14d41ffa1a83bf43507fc86a0ff50d41dea1a83fc43507fea4a0dfd4941ff29283fd52507f8a4a0df14941ffa1283fe42507fa84a0ff10941ff99283fe32507fa64a0ff0c941ffa0a83f741507fc82a0ef90541ffa82837f50507fca0a0ff54141fe282837c50506fca820ffd4c41ff298837e53107bca620d794c41fea98837d53107baa620d754c41fe29883ff43107fc8620ff50c41fe21883ff52107fca420df94841fea90837d52107f8a420ffd0841ff21083be42107fa8420ff10841de21083ff32107fc6420ff4c841fe190837e51107fe8220efd0441ff20883f641107fa8220ef50441faa0883ff50107fca020df94041fea80837d50107f8a020ffd5331bfaa663fe54cc6fca998ff55331beaa663fc54cc6f8a998ffd0f31ff21e63de43cc7fa8798f750f31fe21e63ff52cc7fca598df94b31fea96637d52cc7f8a598ffd0b31ff21663fd42cc7f88598ffccb31ff19663fd32cc7f86598ffd0731ff20e63fd41cc7f88398ffd4331ff286637e50cc7faa198df54331fe28663ff548c6fea918ff95231bf2a463fd548c6faa918ff15231be2a4637d538c7fe8718ff90e31fea1c63fc438c7fea518ff94a31bf29463fd528c6faa518ff14a31ffa1463fe428c7fa8518ff10a31ff99463fe328c7bc6518ff4ca31fe19463dc328c6fca318ffd0631ff20c63fd418c7f88318ffcc631ef98c63f7318c7fea118ff94231bf28463fd508c6faa118ff14231ffaa2637f544c7fca898df95131feaa2637d544c7f8a898df15131ffa1a63fe434c7bc
  | 5 => 0x2002c02000000001000406c09000000005c05c00400c00000000c00804c02000800401400400000c00001000400001400000000001c00001c01808400c00001002000404000400002401800bfea5a1ff94b43bf29687fd52d0efaa5a1ff14b43ffa8e87fe51d0efca3a1ff54743bea8e87fc51d0ffea1a1ff94343bf28687fd50d0efaa1a1ff14343beaa4877e5390ffe8721efd0e43efa1c87ff5290ffca521df94a43fea94877d5290ff8a521ffd4643ff28c877e5190ffaa321df54643fe28c87ff5090ffca121df94243fea84877d5090ff8a121ffd0d43efa1a87fe4350f7c86a1ffd4943bfa9287fe5250ffaa4a1ff14943be29287ff5150efea2a1ff94543fea8a87fc5150ef8a2a1ffd4143bfa8287fe5050ffaa0a1ff14143be282877e5410efca621ffd0c43dfa1887fe4310fbc8621ff50c43dea1887dd4310f3a8621ffd4843ff290877e5210ffaa421df54843fe29087ff5110ffca221df94443fea88877d5110ff8a221ffd4043ff280877e5010ffaa021df54043fe28087ff53d0bfca7a15f94f42ef29e855e53d0bfaa7a15f54f42eea9e855d53d0bf8a7a17fd0f42ff21e85fd43d0bf887a17fd4742ff28e857e51d0bfaa3a15f54742fe28e85ff50d0bfca1a15f94342fea86857d50d0bf8a1a15f55242ffa9c85fe5390afca7217f54e42bea9c85fc5390bfe87216fd0e42ff21c85fd4390b7a87217f10e42bf29485ff4290b7e85217bd0a42ffa8c85fe5190afca3217f54642bea8c85fc5190bfea1217f94242bf28485fd5090afaa1217f14242ffa9a857f5350bfca6a17f54d42fe29a857c5350bfe86a17f90d42fea1a85fc4350bfe84a17bd0942ff21285be4250bfea2a15fd4542ff28a85fd5150bf8a2a15f14542ffa82857f5050bfca0a17f54142fe282857c5050afca8217fd4c42ff298857e5310bfaa6215f54c42fe29885ff4310b7e86217f90c42fea1885bd4310bf886215f94842ffa1085bf4210bfc84217b90842fea1085bd4210bda84217fd4442ff288857e5110bfaa2215f54442fe28885ff5010bfca0215f94042fea80857d5010bf8a0217fd5332bfaa665fe54ccafca9996f953329f2a665fd54ccafaa9996f553329eaa665fc54ccaf8a9997fd0f32ff21e65fd43ccbf887997fd0b32ff21665fd42ccbf885997fd4732ff28e657e51ccbfaa3995f54732fe28e65ff50ccbfca1995f94332fea86657d50ccbf8a1997fd5232bfaa465fe548cafca9197f55232beaa465fc548caf8a9195f54e32ffa1c65fe438cbbc87197f50e32eea1c65fc438cafca5197fd0a32ff21465fd428cbf885197fcca32ef99465ef328cbfea3197f94632bf28c65fd518cafaa3197f14632ffa8465fe508cafca1197f54232bea8465fc508cbfea8995fd5132ff2a2657e544cbfaa8995f55132fe2a2657c544cbfe8699
  | 6 => 0x22c29a8003308fb07d80027e80000014500008a93c800245197913aa42732032f70000000b207fb3d97908706b04f9460d0b1f23e0dc800154a8e09fb2092929d8022980000d425b226970a98a33019aff8102948000003550003659e9a17100ae636900000000004e800029310000331b3500025c80000024680033291e9b5a6a9300003482a91da8ba1b82ab9a8ae02b4210b7d0000000000788000db14f9e401c8f63181cbae0ae100022a8000001958001ac0f39cc9320002d718baa380021a000000000000000001000000402800002400003001800003c04800400404001000801004800c0000100bc01002000001001000000002400006402800400c04403800c00c01800000c01c00005002402006c01400001c00400c00c02402c00005c00c00000403000000800800402007400800408000407400801800002404002800800803001800c01002c00c00409003c00000c03401400c00402400801000000c00400000000800002c00402400c05802800800800001400800400400001001803000400002800c00005001c00400000001000001400002c03403405400002406c03001800800003003001c00402010000000003c03801400007000802400403000400403000c00000008002000c00001400404001000401800800400000401801400400401000400c00000800000c00801400000000002c00000005000402400000000c00014801400000003405800800000001801400000000800000405800001400400002005001400000c00401c01805000800000800001c02000005c00400003c00000008c00004800000800403c01801800006c06c0080040680000000000d802c0480040440440180080340180300140000040000100000140080040040000040140d400001403806004000c00000001c01001002801000404000001402401800000c00000000400001400405803c00400c01802c06803401400001400800800800801003c01c00800000000c00000c00000001c01c02401000c01400000000000000002c00c00400000402802406c00801403800c05c00c00400800401406000c0100040080300380000bc01802800400003c00805004000000000803c00400400408003801000006400000000800c00000400001803800000400000c03800403000c0c800001001c00000401800800401000000001801400402c00001800800802000406c01800000000400400802c00000000000001000001401402800000000000000000001400400803c01000003000800001001401000005400002c0000300480140b800000000800000000c00005c0b400400000c00004000c00004c00000001000000400000c00003400401002400000000c00003400001400c01800c00804400000402c00c0000340100000300c40000100080000
  | 7 => 0x54b258000001d1800188b1fb7a800000000302959a7b8003652689d52d180002c2ee296800087a8ea611ec9ef2ba00023401ba18aa28001c3002adf2d916c8682669012a00e2b2f2a10e519e2218829312d6a571063221c40fd84597730885e901a3c066043af69fca692850000000ec9e280004d811ae208c33b3459b68af24f95e8001081bc306a7ab4f8001e7b0725993a89e00006c94d8001c08000000180001f89ad0002f29dc17a95b85c2639f90000e0181aaab7f06198601623c8f521c183a670330c3ab4b741078eb8afaf313b0000000000000000001ee2088a6800000367800094add9640da9d1000125a1a9ad8003121e0a9e8d81c117f11480017e15aaae3409168e931980000029f8b48018000a88003299251330238a3800150800000000272ad28000969328001cf8499b38000539fc28b15802d33f2649f399f073ab29b01bb05f1d637f80038131b1ca8001cea70a0d32312caf625681f04b201944202909a9b8000000000002b90048c4a920002828ceb0c8000002b9adba2f32e00391f2f91020000620379859761930001eb0000000001a408d800000000000080aaf00000019d94c11330e1ff800108acd8000a70d780034b8d60a087980006d8001270c30f6a882ef0002c734600000000034999a16600012609ab7d82a1a68002e28f22248cb9af800168b580000b41058000001602dfa2a02280022380000016b98003288835180028c800284b5289f119b61a9c12f9ca2808002eb262a8038180036982b8002fa0a791b0168000ef80000020e800357aa72ac9718140de20485f800000123b0b8f10000e10000523570000ac80030a08a214a0623386a800093238b291de9e1291a7c2a50733559e8b1608331c9b40ac11a01e30da879f71be09ea2108ba0d800311afb2bf0f736f2870482b01389538c42de06c0000002e8a07052b7100000000000000031c000253ade917800000297a1bb1280007e80016913e8001bd8002ad169b6680019500d80029036a2a69a484a00c80000000000033d2380eeb7797c80000000013a31e8d19d68002e78b2b78813946949a5fb752458feb4d35a94ca518002ab36b31d000060370acb8fa35a26e95d93400003102080023aace32714a2578f580915230f00015f0ae1de3770002c91ee8002c7b1599aa2b8deb09164b2828fa581d710eb4a1e18001bf9980dd0003218001a9a232200000000001738000000b8a4222e831b4400025a8d4b672bc2ce8e4000091828800152a168ad2438d883d1180000001dd368800000071b478fb8002890488000d91c80000001210000001be82a98d1b8aeea9980000009d00025e8811a192c1160aa87a36c93f8000002d8a5f10b8921821f68000000001d39349b08001ef88887214912b372a8f2cb0000001b18490691b513518ea8daadadd
  | 8 => 0x28d50000002a0979800338a4131092326238087aaf58003130003239589cf0369a30000550cf0000000b7a41a0598703410f9f616e0001881a78b81430002522a18820003009851eda5284a9e92f8b0aad81102b30002ba8000001c780001e9fa2740bc1f01921c733b8b30b53598bd041b590002f097b8001a728a80033600017880009a143800285897aa7af416e80007722da3900713ba478e6a488000fe0190440000ef12d27887480013c00028432425896d08599280002da399808bb0000d112a0000e830d0bf8adaec00035095e000106ad11ec000362227ad385ab5c8001ce17a1cd00000015721d25124aab7833b5c3630079bf0a100000011c00000037002b1fd8000d9b111a90000d01830000a58961a032686e0000e3b3a283b4cb331fea1231490c80e00031bae69b488e1e60000001243418002ae8000000000000000001962862770000003548000cd09730400021ead79b60001d89671b21542868743539a820800d03825a19c0000000000000518aa36800000000037390d2d508b32d90280000035e90c00010f36d83f1a536080006b817095000104acf2dc26b35fb1e1d780027da90b610000002c6800147362a5d00003a36e0eda6bb3c05b00026080000027518980005e0bf18a8000003721200a4a761c9a8195caf10e21209318001ea00001a23f1c50242011fa9f8000056a3e929b1519b2c3a4a0850f02f1b2780fa022f4a722e18560ee0000db800321140800227122ada80000008d0000b61ff0000002c9b4487b1c5ab5a5c219374b01030a7818fad015d1da1811532bb966abcaff17da8a0000c68158448e729594e94000e8002b100000000021100017c1b70c80050000001940000001730ff9e0160a5d96c36d00005083c9f200025018f00000005db13b2480025e18c0f180a9d92c4a4480011d0002a58ab09132d10a80035b1e48000000000450fc80000007100032011fa888001f7afc00000004332b8001339151bca550000002c30000000000940000a1955034835000000200800204235b760dc21b37c09c9741422b521cb42a7690b000047a6a00000024cae3a590e587d349038af212817d3179ba2e90a31d4b43b0480b80019130b103277b3ab2f8980f88000d337c94103fa7594b9b792ba46103a25abd898a3da820000b0b512cd0000ff04bab60c60758751288a801b00000000002f91bb5203a95599984c80027180031903c1900e61c3a7f8da00020fa2602613e20c8000000a99ab0000003171c48659e21c22ec80000025b800121b098eb18d893ac8a8c2ea9e5a1021191a9b300000600000015f96d8a0000350095ac524435d89032a00000030202800030785b89c02535d15a0eaae42650fc33c9a20668002e49721f087c80000007027f301b3e83737180027118781d24c0218001501f4b140
  | 9 => 0x2cc80000000000000000000013080000028300032c0000000000c287e00000000019892e1992ac0002ea1968778ce1c8a07b6c2618359071bba2b0be80004d02f10e34a80a0212d5800228b643370001b997e937b5f0d68908001710278000000001aea931868002cfaefb6003e070a1319e951215a7c91080000005cad21a637980014188027d02c80008fafdad320b25580b2320000000c52da2c1ae98001e70002c209931a0c890423299f8002f81ed2051908e3237924876086a0a06fab8b3992200024b00032e86780024e88ca2092d97b00129d00006d0000ed2f02508cab8299d2198d38001f2800000083b420000130f999ba280cc0000000c78000791172b1840a9526fa6cb2616f00000000014f0002d095c0638002960c22b800020c2129d226d0001f18001dd80022f93d8f81abb7e3000001750000030be32b00003b2a980030e80005d19c8003348001c280011e00038200028982303985424018ca6618b19496b0598002aa243249b032c580c174ac28b98f4a408f40000002d48000c0aca3450002308b736a8000000000000001fd0000000000532221c900037ba03a9c8c196389b2541630609fe182b2890a1c69f40cd80007bafd36e9ae01dad980000014821d8e480034323701280000033905793924d9679bd2afa4e1488a20faa6c234b188ec2caaf783ea9920b9acb5e0641f9ab0a54a640f09610d217683b8f78421893168001970c72c0b402be2db0001f3068a5311900818a000081a9702596a2a611c8ab9561b901228d2f3b2c927b4893f23f96824f22e16a80995b34c02229129a0b687811234692ab4e9aa16f8d2b780df85a2251e832281897f8c9112832175b5894d1dc9baac60003051d08a91c600009ba490001368000000648610000001aa98e0002e323680020f0c00468cb00000000007c000062b531728c10460000002a326322d0362eda8b80010d8000e880035431da0a80036f80026580009293710000004129b12f12eab6a318001d5a09b7a0000728000002c4000157a3a0fd0000b180024d0001090002181188002292299a10000002938000000000000000000840000998588000b38000000000001fb144ac1000000267af500027b0768d5b4f00021600026801f8000002142e82a2213b3f98430593580013d010936279375993b080c98a50581b12a82feb0634b126afe0558650272240bc8f90b58f280018494e00034721f23b147b7e8200268631d00bd8001a5a001db28122cb5b9c02be800000274a3b9459d81702e71ebabb1618110000ae96580000010527a2360000068428000000000000000000000000000ca0000000002a4a0e00021780031a8003412b726e11da093038a426d9db8673368e08088cfafb8df2480000848e98590000b10000a28bb9159fb9d304f0dd84e00000000029
  | 10 => 0x890002fcab3a1500002987f0862301650152bf8000a61e3ac80698cc8000001629f50149a38000000000000002738000000000002ed13802eb769b280000029e03daf9a940510009d42dca312b20002e53378001e680030c27034e1df37b3359dfb2529f00000002e2562e5889b662229778000000401429f5a6980027e01786a0ea2473301f12a8b2a80024b8000e188f2798000571cd8503730ba9a2939a3501c363991b6b8040f306f04733137933e0c59cb00f2bd2d63383341591111d2a6f1e521f91423d3320d7178151a6003902481a911ad416208e84c0e78000b01cc0000000000001a0b802eb8001d99e306eafab649c180021e00000000035689d80030fb56333a06b4d95694a80580014b1ea8302428002c02cc1af0b9
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x4210427d6508410db948210436d5208410be98021042f96008410dd59421042756508410bd98821043e66208410ddd4821043e65208410dd54821043e55208410d954821043f26008410bd58021043f16008410bc580210427e64940109f592500427e63940109f58e500427e62940109f58a500427d6194010ddc86500437421940109f597400427f65900109f596400433e5490010cf55240042f66190010bd586400427f65500109fd94400427e65100109f594400427c6510010cf950400433d5410010b798c40042dd6310010bd98440042f56110010ee500400427d65cc0109fd96300427d658c010d794e300435d538c010bd98630042f5618c0109fd95300427f650c0109f994300427d650c0109f19430042be640c010af590300435e530c010d754c30042f6610c010bd58430043d9300c0109f59720042f965c8010de597200437b52c8010de54b20043f361c8010be58720043f061c8010de94720043f321c8010fc087200427f65880109f596200436e5288010db54a20042f66188010bd58620042fa60880109fd9520042bf6448010af19120042df6348010b718d20042f76148010bd185200427f65080109f994200427d65080109f194200436e5208010db54820042f66108010bd58420042f96508010de59420042796508010be98820043ea6208010ded4820043ea5208010de54820043e95208010da54820043f26108010be58420043f16108010bc584200437a5108010fcc8420043f02108010dd59710042f662c4010bd18b10043f320c4010fc08310042f56184010dd94610042f96584010de59610042796584010be98a10042f86284010be58610042f16184010de94610043f25184010fcc8610043f021840109fd9510042f76544010ddd9510042776544010bd98910042f46244010bdd8110043765044010fcd0110043f24044010fc50110043f04044010fccc110043f23044010fc4c110043f03044010fcc8110043f22044010fc48110043f02044010bed95100437b65440109ed9510042fa6244010be18910042fb6144010fcd85100437a5144010fc94510043f34144010fc90510043f14144010fc10510043f33144010fc8c510043f13144010fc0c510043f32144010fc88510043f12144010fc08510043f36544010bcd9510043736544010fcd9110043f26444010fc59110043f06444010fcd5110043f25444010fc55110043f05444010fcd8d10043f26344010fc58d10043f06344010fcd4d10043f25344010fc54d10043f05344010fcd0d10043f24344010fc50d10043f04344010fcd8910043f26244010bc98910043f16244010fc18910042f06244010fcd4910043f25244010fc54910043f05244010fcd0910043f24244010fc50910043f04244010fccc910043f23244010fc4c910043f03244010
  | 1 => 0x427c6550c10cf951430433d5450c10d794d430435d5350c10bdd8543042f46150c10bed8143042f86050c109fd94430427e6510c109f594430427c6510c10e750c43042f66110c10bd58443042fa6010c10be580430427e64d48109f593520427e63d48109f58f520427e61d4810dd987520427e60d4810de983520427d6594810dbd4a520427e64948109f592520427e63948109f58e52042bf6454810af19152042df6354810b718d520427f6454810cfd91520423f64548109f191520433c64548108f191520427f6354810d7d8d520425f63548109f18d520435c63548109718d520436f62548109fd85520427d6154810dd185520427f60548109f58152043786054810af99052042bd6414810b798c52042dd6314810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520427e6114810dd984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf55342042de63d0810b758f42042f661d0810bd58742042fa60d0810be583420427f65908109f996420427d65908109f196420433f5490810cf152420436e5290810db54a420427f65508109f995420427d65508109f195420433e5450810cf551420436e5250810db54942042f76150810bd18542042fb6050810be181420427f65108109f994420427d65108109f194420433f5410810cf150420427f65cc8109f997320427d65cc8109f19732042be64cc810af593320435e53cc810d754f32042f661cc810bd58732042fa60cc810be583320427f658c8109f996320427d658c8109f196320435f538c810d714e320436e528c810db54a320427f654c8109f995320427d654c8109f195320435e534c810d754d320436e524c810db54932042f7614c810bd18532042fb604c810be181320427f650c8109f994320427d650c8109f194320435f530c810d714c320427e64944109f592510427e63944109f58e510427e62944109f58a510427d65d04109fd96410427d6590410cf952410433d5490410be98241042f960904109fd95410427f65104109f594410433e5410410cf55041042de6310410b758c41043b54110410be98041042f960104109f597310427f658c4109f596310435e538c410d754e31042fa608c410be582310427f654c4109fd94310427d650c410af99031042bd640c410d794c310435d530c410f54c431042fa600c410be580310427d65c8410bd597210437565c8410ddd4b210437552c8410fcd8321042f560c8410fc183210427f65884109f596210436e5288410db54a21042f66188410be98221042f960884109fd9521042bf6448410af19121042df6348410b718d21042fb60484109fd9
  | 2 => 0x530c910d714c324436f520c910db14832442f6610c910bd58432442fa600c910be580324427e65d0510cfd53414433c54d0510be98341442f960d05109f996414427c6550510cfd51414433c5450510bed8141442f860505109f99441442de6310510b758c414427e65cc510d7d4f314435c53cc510be98331442f960cc5109f996314427c654c510d7d4d314435c534c510bed8131442f8604c5109f99431442be640c510af590314427e65c8510dbd4b214436c52c8510be98321442f960c85109f996214427c6548510afd9121442bc6448510b7d8d21442dc6348510dbd49214436c5248510bed8121442f860485109f99421443e521085109f997404433f54d0110cf15340442f661d0110bd587404427e65901109fd95404427d65501109f195404433f5450110cf15140442f76150110bd185404427e6510110b798c40442dd63101109f997304435f53cc110d714f30442f661cc110bd587304427e658c1109fd95304427d654c1109f195304435f534c110d714d30442f7614c110bd185304427e650c110af99030442bd640c1109f997204436f52c8110db14b20442f661c8110bd587204427e65881109fd95204427d65481109f19520442bf6448110af19120442df6348110b718d204436f5248110db14920442f76148110bd185204427e6508110fa480204437a52c4110de14b10443765284110dd14a10443f350841109f98f540427d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d6295010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540427f60550109f581540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150109f98c540435e63150109798c540427d6315010d758c540425d63150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109f980540437a60150109f993530427d64d4c109f98b530427d62d4c109f987530437661d4c109f983530437a60d4c109f596530435f5394c109f992530427d6494c109f98a530427d6294c109fd91530427c6454c10d7d8d530427f6254c109f189530427f6154c109f585530427f6054c109f58153042be6414c10af590530435d5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f98c530435e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109f980530437a6014c109fd97430427e65d0c109f597430427c65d0c10cf953430433d54d0c109fd96430427e6590c109f596430427c6590c10d794e430435d5390c109fd95430427e6550c109f595430
  | 3 => 0x1109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427f6055110ded81544427e6515110cf55054442de6315110b758c544433e64151109f98c544435e63151109798c544427d6315110d758c544425d63151109f988544427d62151109f984544427c61151109f980544427c60151109f993534427d64d4d109f98b534427d62d4d10d7d4e534427e6494d109f592534427e6394d109f98a534427d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10bbd8953442ec6254d109fd91534433f6454d108fd91534427c6454d10cf191534423c6454d10d7d8d534427f6254d10dbd89534426f6254d109f189534436c6254d109b189534427f6154d10ddd85534427f6054d10ded81534427e6514d10af99053442bd6414d10d754c534427e6414d10cf990534423e6414d109f590534433d6414d108f590534435e6314d109f988534427d6214d109f984534427c6114d109f980534427c6014d109fd97434427e65d0d109f597434427c65d0d10cf953434433d54d0d10d7d4f434435c53d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d10d794e434435d5390d109fd95434427e6550d109f595434427c6550d10cf951434433d5450d10d794d434435d5350d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10d7d4c434435c5310d10e750c434427e64d49109f593524427e63d49109f58f524436f52949109f992524427d64949109f98e524427d63949109f98a524427d6194910dd586524427d6094910de58252442bf6454910af19152442df6354910b718d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109dd85524427f6054910ded81524427b60549109f994524436d52149109f990524427d64149109f98c524427d6314910db988524427e61149109f184524427e60149109f180524427f65d09109f997424427d65d09109f19742442de63d0910b758f424436f52d0910db14b424427f65909109f996424427d65909109f196424433f5490910cf152424427f65509109f995424427d65509109f195424427f65109109f994424427d65109109f194424433f5410910cf150424436f5210910db14842442f66110910bd58442442fa6010910be580424427f65cc9109f997324427d65cc9109f19732442be64cc910af593324436f52cc910db14b324427f658c9109f996324427d658c9109f196324435f538c910d714e324427f654c9109f995324427d654c9109f195324427f650c9109f994324427d650c9109f194324435f
  | 4 => 0x754d43842f76150e10bd185438427f6510e109f994438427d6510e109f194438439d4310e10bd98443842f56110e10af99352842bd64d4a10b798f52842dd63d4a109f993528433e64d4a108f993528427d64d4a10cf593528423d64d4a109f98f528435e63d4a109798f528427d63d4a10d758f528425d63d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528427f6454a109f191528427f6354a109f18d528436f6254a10ddd85528436d5214a109f990528427d6414a109f98c528427d6314a10db98852843756114a10de980528427f65d0a109f997428427d65d0a109f19742842de63d0a10b758f42842f661d0a10bd587428427f6590a109f996428427d6590a109f196428433e5490a10cf552428427f6550a109f995428427d6550a109f19542842f76150a10bd185428427f6510a109f994428427d6510a109f194428433e5410a10cf55042842fa6010a10be580428427f65cca109f997328427d65cca109f19732842be64cca10af59332842f661cca10bd587328427f658ca109f996328427d658ca109f196328435e538ca10d754e328427f654ca109f995328427d654ca109f19532842f7614ca10bd185328427f650ca109f994328427d650ca109f194328435e530ca10d754c32842fa600ca10be580328433e54d0610cf55341842fa60d0610be583418433e5450610cf55141842fb6050610be18141842de6310610b758c41843b54110610d794f318435d53cc610be98331842f960cc610d794d318435d534c610bed8131842f8604c610af99031842bd640c610f54c4318436e52c8610db54b21842fa60c8610be583218437565c8610ddd4b21843e652c8610dd54b21843e552c8610fc98321842f560c8610fc58321842bf6448610af19121842df6348610b718d218436e5248610db54921842fb6048610be18121842f56508610dd59421843e66208610ddd4821843755208610bd580218433e5490210cf55240842f66190210bd586408433e5410210cf55040842de6310210b758c40842f66110210bd584408435e538c210d754e30842f6618c210bd58630842be640c210af590308435e530c210d754c30842f6610c210bd584308436e5288210db54a20842f66188210bd58620842bf6448210af19120842df6348210b718d20842f76148210bd185208436e5208210db54820842f66108210bd58420843e92008210bd597108437565c4210bd98b10842f462c4210be597108437965c4210de94b108437852c42109f98f544427d63d51109f98b544427d62d5110cfd52544427e64951109f98e544427d63951109f98a544427d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f6355
  | 5 => 0x42c427c65d0b10b798f42c42dd63d0b10be98342c42f960d0b109fd9642c427e6590b109f59642c427c6590b10cf95242c433d5490b109fd9542c427e6550b109f59542c427c6550b10bed8142c42f86050b109fd9442c427e6510b109f59442c427c6510b10cf95042c433d5410b10bd98442c42f56110b109fd9732c427e65ccb109f59732c427c65ccb10af99332c42bd64ccb10be98332c42f960ccb109fd9632c427e658cb109f59632c427c658cb10d794e32c435d538cb109fd9532c427e654cb109f59532c427c654cb10bed8132c42f8604cb109fd9432c427e650cb109f59432c427c650cb10d794c32c435d530cb10bd98432c42f5610cb10cf95241c433d5490710be98241c42f96090710cf95041c433d5410710b798c41c42dd6310710be98041c42f96010710d794e31c435d538c710be98231c42f9608c710af99031c42bd640c710d794c31c435d530c710be98031c42f9600c710db94a21c436d5288710be98221c42f96088710afd9121c42bc6448710b7d8d21c42dc6348710be18121c436e5208710db54821c43e52108710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310cf95140c433d5450310bdd8540c42f46150310b798c40c42dd6310310ee50040c435e53cc310d754f30c42f661cc310bd58730c435e534c310d754d30c42f7614c310bd18530c42be640c310af59030c43d9300c310db94b20c436d52c8310bd98720c42f561c8310be59720c437965c8310ded4b20c43ea52c8310de54b20c43e952c8310fc98720c42f961c8310fc58720c42bf6448310af19120c42df6348310b718d20c436e5248310db54920c42f76148310bd18520c42f96508310de59420c43ea6208310ded4820c43795208310be58420c427e63d52109f58f548427e62d52109f58b548437561d5210de983548433f54952109f98e548427d63952109f98a548427d6295210cfd91548427f63552109f18d548427f62552109f189548433d5415210b798c54842dd6315210cf990548427e6315210d798c548425e63152109f58c548435d63152109758c548427e62152109f58854843756115210de980548427e64d4e109f593538427e62d4e109f58b538437561d4e10de983538435f5394e109f992538427d6494e109f98a538427d6294e109fd91538427c6454e10d7d8d538427f6254e109f18953842be6414e10af590538435d5314e109f990538433e6414e108f990538427d6414e10cf590538423d6414e10d798c538427e6214e109f58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438433e54d0e10cf553438427f6590e109f996438427d6590e109f196438435e5390e10d754e438427f6550e109f995438427d6550e109f195438433e5450e10cf551438435e5350e10d
  | 6 => 0x27e63940209f58e500827d65d00209fd96400827d6590020cf952400833d5490020bb98a40082ed62900209fd95400827f65100209f994400827d65100209f194400833e5410020cf55040082de6310020b758c40082ee6210020bb588400827d65cc0209fd96300827d658c020d794e300835d538c020bb98a30082ed628c0209fd95300827f650c0209f994300827d650c0209f19430082be640c020af590300835e530c020d754c30082ee620c020bb58830082ed6288020db94a20082f96288020de94a20083ea5288020be986200827f6548020afd9120082bc6448020b7d8d20082dc6348020bdd8520082f46148020bbd95200836f65480209bd9520083af6448020eb19120083cf6348020f318d20083e76148020f918520082ef6048020db94120083eb4048020fa10120083eb3048020fa0c120082fb6548020ded95200827b6548020eed9120083b86448020f6d8d20083d86348020bed8920083eb6248020de94920083ea5248020fad0920083e84248020facc920083e83248020fcd8520082f86148020fc18520082f06148020fac8520083e921480209f98f54c427d63d53109f98b54c427d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c433f64553109fd8d54c427c63553109fd8954c427c6255310cf55054c42de6315310b758c54c433e64153109f98c54c435e63153109798c54c427d6315310d758c54c425d63153109f98854c427d6215310dd98454c437960153109f99353c427d64d4f109f98b53c427d62d4f10dd98753c437960d4f10d7d4e53c427e6494f109f59253c427e6294f109f58a53c427f6454f109f19153c435f6354f109fd8953c427c6254f10af99053c42bd6414f10d754c53c427e6414f10cf99053c423e6414f109f59053c433d6414f108f59053c435e6314f109f98853c427d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10cf95343c433d54d0f109fd9643c427e6590f109f59643c427c6590f10d794e43c435d5390f109fd9543c427e6550f109f59543c427c6550f10cf95143c433d5450f10d794d43c435d5350f10bed8143c42f86050f109fd9443c427e6510f109f59443c427c6510f10e750c43c42fa6010f10be58043c42be64d4b10af59352c42de63d4b10b758f52c427e64d4b10cf99352c423e64d4b109f59352c433d64d4b108f59352c427e63d4b10d798f52c425e63d4b109f58f52c435d63d4b109758f52c437661d4b10de58352c436f5294b109f99252c427d6494b109f98e52c427d6394b109fd9152c427c6454b109fd8d52c427c6354b10dbd8952c437b6054b10db54852c427e6414b109f59052c427e6314b109f58c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f597
  | 7 => 0x1150209f990540833e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f988540836e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a60150209f993530827d64d4c209f98b530836e62d4c209f987530827d61d4c209f983530837a60d4c209f596530835f5394c209f992530827d6494c209f986530827d6194c209fd91530827c6454c20d7d8d530827f6254c209f589530827f6154c209f18553082be6414c20af590530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209f988530836e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c209fd96430827e6590c209f596430827c6590c20d794e430835d5390c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c20bbd8943082ec6250c20bed8143082f86050c209fd94430827e6510c209f594430827c6510c20e750c430827e64948209f592520827e63948209f58e520827d65d0820b798f42082dd63d08209fd96420827d6590820cf952420833d5490820be98242082f960908209fd95420827f65108209f594420833e5410820cf55042082fa6010820be580420827d65cc820af99332082bd64cc8209fd96320827d658c820d794e320835d538c820be98232082f9608c8209fd95320827f650c8209f594320835e530c820d754c32082fa600c820be580320837751944209f992510827d64944209f98e510827d63944209fd91510827c64544209fd8d510827c6354420de18151082be6414420af59051082de6314420b758c510837551144209fd97410827e65d04209f597410833e54d0420cf55341082fa60d0420be583410827f65904209f996410827d6590420dd946410837551904209fd95410827d65504209f195410833e5450420cf55141082ef6250420bb18941083765150420dd54541082fb6050420be181410827f65104209f994410827d6510420b798c41082dd63104209fd97310827e65cc4209f597310835e53cc420d754f31082fa60cc420be583310827f658c4209f996310827d658c420dd9463108375518c4209fd95310827d654c4209f195310835e534c420d754d31082ef624c420bb1893108376514c420dd54531082fb604c420be181310827f650c4209f994310827d650c420af99031082bd640c420dd947210837551c8420be98321082f960c84209f596210827f6548420afd9121082bc6448420b7d8d21082dc6348420bed8121083765108420dd54421082fa6008420be580210827e64940209f5925008
  | 8 => 0x209f594414827c6510520cfd50414833c5410520b798c41482dd6310520d7d4c414835c5310520bb98841482ed6210520ddd4441483745110520be98041482f960105209f997314827d65cc5209f197314833f54cc520cf153314835f53cc520d714f314837751cc520dd147314827e658c5209f596314827c658c520cfd52314833c548c520d7d4e314835c538c520ddd463148374518c5209fd95314827e654c5209f195314833f544c520cf151314835f534c520d714d3148377514c520dd145314827e650c5209f594314827c650c520af99031482bd640c520cfd50314833c540c520d7d4c314835c530c520bb98831482ed620c520ddd443148374510c520be98031482f9600c5209f997214833f54c8520cf153214835f53c8520d714f214837451c8520cfd52214833c5488520d7d4e214835c5388520ddd4621483745188520be98221482f96088520afd9121482bc6448520cfd51214833c5448520b7d8d21482dc6348520d7d4d214835c5348520ddd4521483745148520bed8121482f860485209f994214833f5408520cf150214835f5308520d714c21483775108520f9484214827e65d0120cfd53404833c54d0120d7d4f404835c53d0120bb98b40482ed62d0120ddd47404837451d01209f996404833f5490120cf152404835f5390120d714e40483775190120dd146404827f65501209f595404827c6550120cfd51404833c5450120d7d4d404835c5350120bbd8940482ec6250120ddd45404837451501209f994404833f5410120cf15040482de6310120b758c404835f5310120d714c40483775110120dd14440483b940101209f997304833f54cc120cf153304835f53cc120d714f30482ee62cc120bb58b304837751cc120dd147304827e658c120cfd52304833c548c120d7d4e304835c538c120ddd463048374518c1209fd95304827d654c1209f195304833f544c120cf151304835f534c120d714d30482ef624c120bb1893048377514c120dd145304827e650c120af99030482bd640c120cfd50304833c540c120d7d4c304835c530c120ddd443048374510c120f64c0304833f54c8120cf153204835f53c8120d714f204837751c8120dd14720483bb54c8120ee15320483db53c8120f614f20483f351c8120de14720483f051c8120dc147204833f5488120cf152204835f5388120d714e20483775188120dd14620483af5488120eb15220483cf5388120f314e20483e75188120f914620483eb50881209f98f540827d63d50209f98b540836e62d50209f987540827d61d50209f983540837a60d50209f596540833f54950209f98e540827d63950209f986540827d6195020cfd91540827f63550209f18d540827f62550209f589540827f61550209f185540833d5415020b798c54082dd6315020bd98454082f56
  | 9 => 0xd4e434835c5390d209fd95434827e6550d209f595434827c6550d20cfd51434833c5450d20d7d4d434835c5350d209fd94434827e6510d209f594434827c6510d20cfd50434833c5410d20d7d4c434835c5310d20e750c43482fa6010d20be580434827e65d0920cfd53424833c54d0920b798f42482dd63d0920d7d4f424835c53d0920be98342482f960d09209f996424833f5490920cf152424835f5390920d714e424827c6550920cfd51424833c5450920d7d4d424835c5350920bed8142482f860509209f994424833f5410920cf150424835f5310920d714c424827e65cc920af99332482bd64cc920cfd53324833c54cc920d7d4f324835c53cc920be98332482f960cc9209f996324833f548c920cf152324835f538c920d714e324827c654c920cfd51324833c544c920d7d4d324835c534c920bed8132482f8604c9209f994324833f540c920cf150324835f530c920d714c324833f54d4520cf153514835f53d4520d714f514827e64d45209f593514827e63d45209f58f514837754d4520edd53514833754d4520dd953514837554d4520dd15351483b454d4520cd153514837753d4520f5d4f514835753d4520dd94f514837553d4520dd14f51483d453d4520d514f514837764d4520dd993514837564d4520dd193514837763d4520dd98f514837563d4520dd18f514837743d4520dd90f514837543d4520dd10f514837762d4520ddd0b514837642d4520dd50b514837442d4520ddccb514837632d4520dd4cb514837432d4520ddd83514837560d4520af99251482bd6494520cfd52514833c5494520b798e51482dd6394520d7d4e514835c5394520ddd4651482bf6454520af191514833f5454520cf15151482df6354520b718d514835f5354520d714d514833f5414520cf150514835f5314520d714c514837551145209f990514827d64145209f98c514827d6314520bd99451483766514520ddd5051483b75414520cdd5051483765414520dd55051483745414520ed15051483345414520ddd4c51483d75314520d5d4c51483765314520dd54c51483745314520f514c51483545314520ddd9051483766414520dd59051483746414520ddd8c51483766314520dd58c51483746314520ddd0c51483764314520dd50c51483744314520ddd8851483774214520dd90851483754214520dd10851483773214520dd8c851483753214520dd0c851483776014520dd580514837520145209f997414827d65d05209f197414833f54d0520cf153414835f53d0520d714f414837751d0520dd147414827e65905209f596414827c6590520cfd52414833c5490520d7d4e414835c5390520ddd46414837451905209fd95414827e65505209f195414833f5450520cf151414835f5350520d714d41483775150520dd145414827e65105
  | 10 => 0x882ed620c220f64c030882ed65c8220db59720882f965c8220de597208837a51c82209f98f544827d63d51209f987544827d61d5120cfd8f544833e63d5120cf58f544833c63d5120cfd8b544833d62d5120cfd87544833e61d5120cf587544833c61d5120cfd83544833d60d5120cfd5254482de6395120b758e54482f66195120bd586544827e64951208f992544827e6395120d798e544825e63951209f58e544835d63951209758e544827d6295120db58a544827e6195120dd986544827661951209f586544837561951209d586544827d6095120de58254482df6355120b718d54482f76155120bd185544833f64551209fd8d544835f635512097d8d544827c6355120d718d544825c63551209fd89544836f62551209fd85544837761551209dd85544827c6155120dd185544827461551209fd81544837b60551209f994544833d5415120cf990544827e63151209f58c544827e62151209f188544827e61151209f58454482be6515120cf994544823e6515120cfd8c544833e6315120cf58c544833c6315120cfd88544833d6215120cfd84544833e6115120cf584544833c6115120cfd80544833d6015120cf480544833f54d4d20cf153534827e64d4d209f593534827e61d4d209f587534835f54d4d20e7d53534831f54d4d20d7953534835d54d4d20d7153534839c54d4d20c7153534835f64d4d20d7993534835d64d4d20d7193534835f62d4d20d758b534835f61d4d20d7987534835d61d4d20d7187534835f60d4d20d758353482be6494d20af592534833f5494d20cf152534835f5394d20bd98653482f56194d209f992534833e6494d208f992534827d6494d20cf592534823d6494d209f98e534825e6394d209f58a534836d6294d209f98653483766194d209d986534827d6194d20dd58653482756194d209f58253483796094d20afd9153482bc6454d20cfd51534833c5454d20bdd8553482f46154d209fd91534833f6454d208fd91534827c6454d20cf191534823c6454d20d7d8d534827f6254d20dbd89534827f6154d20ddd8553482776154d209f18553483746154d209d185534827f6054d20ded81534827e6514d20cfd50534833c5414d20d754c534827e6414d209f590534835e6314d209f988534827c6214d209f984534827d6114d20b7994534835e6514d2097994534835f5414d20e7d50534831f5414d20d7950534835d5414d20d7150534839c5414d20c7150534835f6414d20d7990534835d6414d20d7190534835f6214d20d7588534835f6114d20d7984534835d6114d20d7184534835f6014d20d7580534835d2014d209fd97434827e65d0d209f597434827c65d0d20cfd53434833c54d0d20d7d4f434835c53d0d209fd96434827e6590d209f596434827c6590d20cfd52434833c5490d20d7
  | 11 => 0x5c538c320d794d30c835d534c320bbd8930c82ec624c320af99030c82bd640c320d7d4c30c835c530c3209f98f548827d63d5220db58b548827e61d52209f587548837a60d5220cfd52548827e63952209f58e548827e61952209f586548833f64552209fd8d548827c63552209fd85548827c6155220cf55054882de6315220b758c548833e64152209f98c548835e63152209798c548827d6315220d758c548825d6315220db588548827e61152209f584548837a60152209f993538827d64d4e20db58b538827e61d4e209f587538837a60d4e20d7d4e538827e6494e209f592538827e6194e209f586538827f6454e209f191538835f6354e209fd85538827c6154e20af99053882bd6414e20d754c538827e6414e20cf990538823e6414e209f590538833d6414e208f590538835e6314e20db588538827e6114e209f584538837a6014e209fd97438827e65d0e209f597438827c65d0e20cf953438833d54d0e209fd96438827e6590e209f596438827c6590e20d794e438835d5390e209fd95438827e6550e209f595438827c6550e20cf951438833d5450e20d794d438835d5350e20bbd8943882ec6250e209fd94438827e6510e209f594438827c6510e20e750c43882fa6010e20be580438833e54d0a20cf55342882de63d0a20b758f42882fa60d0a20be583428833f5490a20cf152428833e5450a20cf55142882fb6050a20be181428833f5410a20cf15042882be64cca20af593328835e53cca20d754f32882fa60cca20be583328835f538ca20d714e328835e534ca20d754d32882fb604ca20be181328835f530ca20d714c32882be64d4620af59351882de63d4620b758f518837751946209f992518827d64946209f98e518827d63946209fd91518827c64546209fd8d518827c6354620dd544518827f65d06209f997418827d65d06209fd96418827e65906209f596418833e5490620cf552418827f65506209f595418827c6550620bbd8941882ec62506209fd94418827e65106209f594418833e5410620cf55041882de6310620b758c41882fa6010620be580418827f65cc6209f997318827d65cc6209fd96318827e658c6209f596318835e538c620d754e318827f654c6209f595318827c654c620bbd8931882ec624c6209fd94318827e650c6209f59431882be640c620af590318835e530c620d754c31882fa600c620be58031883765188620dd54621882fa6088620be58221882bf6448620af19121882df6348620b718d21883765148620dd54521882fb6048620be181218833e5490220cf55240882ee6290220bb58a408833e5410220cf55040882de6310220b758c40882ee6210220bb58840883b94010220d794e308835d538c220bb98a30882ed628c220af99030882bd640c220d794c308835d530c220bb9883
  | 12 => 0x4c030e7951300c35d544c030e7551300c31d544c030b7189300c2df604c030d7941300c3db404c030f6101300c2fb654c030ded95300c27b654c030ee951300c3b9544c030bed8d300c3db634c030de94d300c3da534c030f6d0d300c3d8434c030f6cc9300c3d9324c030f68c5300c3d8314c0309f98f54c827d63d5320db98b54c827e61d53209f58754c837960d5320cfd5254c82de6395320b758e54c827e6395320d798e54c825e63953209f58e54c835d63953209758e54c827e61953209f58654c833f64553209fd8d54c827c63553209fd8554c827c6155320cf55054c833e64153209f98c54c827d6315320db98854c827e61153209f58454c837960153209f99353c827d64d4f20db98b53c827e61d4f209f58753c837960d4f20af99253c82bd6494f20d7d4e53c827e6494f20cf99253c823e6494f209f59253c833d6494f208f59253c827e6194f209f58653c827f6454f209f19153c835f6354f209fd8553c827c6154f20d754c53c827e6414f209f59053c835e6314f20db98853c827e6114f209f58453c83796014f209fd9743c827e65d0f209f59743c827c65d0f20cfd5343c833c54d0f209fd9643c827e6590f209f59643c827c6590f20d7d4e43c835c5390f209fd9543c827e6550f209f59543c827c6550f20cfd5143c833c5450f20d7d4d43c835c5350f20bed8143c82f86050f209fd9443c827e6510f209f59443c827c6510f20e750c43c82de63d0b20b758f42c833e5490b20cf55242c82fa6090b20be58242c833e5410b20cf55042c82fa6010b20be58042c82be64ccb20af59332c835e538cb20d754e32c82fa608cb20be58232c835e530cb20d754c32c82fa600cb20be58032c837751947209f99251c827d64947209f98e51c827d63947209fd9151c827c64547209fd8d51c827c6354720ded8151c837551147209fd9741c827e65d07209f59741c82fa60d0720be58341c827f65907209f99641c827d65907209fd9541c827d65507209f19541c82fb6050720be18141c827f65107209f99441c827d6510720b798c41c82dd6310720bb98841c82ed62107209fd9731c827e65cc7209f59731c82fa60cc720be58331c827f658c7209f99631c827d658c7209fd9531c827d654c7209f19531c82fb604c720be18131c827f650c7209f99431c827d650c720af99031c82bd640c720bb98831c82ed620c720dd94721c837551c8720be98321c82f960c8720afd9121c82bc6448720b7d8d21c82dc6348720be18121c83765108720dd54421c83e52108720be98021c82f96008720cf95340c833d54d0320bb98b40c82ed62d0320cfd5240c833c5490320cf95140c833d5450320bbd8940c82ec6250320cfd5040c833c5410320b798c40c82dd6310320d794f30c835d53cc320bb98b30c82ed62cc320d7d4e30c83
  | 13 => 0x9f195420c33e5450830cf551420c2df6350830b718d420c2fb6050830be181420c27f65108309f994420c27d6510830cf950420c33d5410830af993320c2bd64cc830cf953320c33d54cc830db94b320c36d52cc830be983320c2f960cc8309f596320c33e548c830cf552320c2dd658c830d7596320c35f548c830e7952320c35d548c830e7552320c31d548c830b798a320c35d528c830b7582320c27f654c830cf951320c33d544c830cf950320c33d540c830db948320c36d520c830be980320c2f9600c830d7d50320c39e540c830d7550320c39d540c830c7550320c2de620c830f3988320c3ce520c830d7548320c3cd520c830f6980320c2dd600c830f6580320c2d9600c830af993510c2bd64d4430cf953510c33d54d4430cf952510c33d5494430ddd46510c27e64944309f592510c27e62944309f58a510c35e3294430d70ca510c33e5454430cf551510c27f64544309f191510c27f62544309f189510c2be6414430af590510c33e5414430cf550510c2ee6214430bb588510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c27f65904309f996410c27d6590430cf952410c33d54904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c2fb6050430be181410c27f65104309f994410c27d6510430cf950410c33d5410430b798c410c2dd6310430cf953310c33d54cc430dd947310c37551cc430be983310c2f960cc4309f596310c33e548c430cf552310c27f654c430cf951310c33d544c430af990310c2bd640c430cf950310c33d540c430dd944310c375510c430f54c4310c2fa600c430be580310c27f65c84309f997210c27d65c8430cf953210c33d54c8430db94b210c36d52c84309fd96210c27e65884309f596210c33e5488430cf552210c2de6388430b758e210c3765188430dd546210c27f65484309f595210c27c6548430afd91210c2bc6448430cf951210c33d5448430b7d8d210c2dc6348430db949210c36d5248430dd945210c3755148430bed81210c2f860484309fd94210c27e65084309f594210c33e5408430cf550210c27e64940309f592500c35e3294030d70ca500c27d65d0030cf953400c33d54d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd63900309fd95400c33e5450030cf551400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c3b94010030cf953300c33d54cc030d7d53300c39e54cc030d7553300c39d54cc030c7553300c2de62cc030cf952300c33d548c030b758e300c35e538c030ee952300c3b9548c030be58e300c37a538c030f694e300c3da328c030f60ca300c27f654c030cf951300c33d544c030b7d95300c35f654c03097d95300c35f54
  | 14 => 0x97414c27c65d0530b798f414c2dd63d0530e750f414c37751d0530dd147414c2fa60d0530be583414c27e65905309f596414c27c6590530cfd52414c33c54905309fd95414c27e65505309f195414c39d43505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c3775110530dd144414c27e65cc530ddd46314c374518c530be982314c2f9608c530ddd45314c374514c530bed81314c2f8604c5309f994314c2be640c530af590314c27e65c85309f597214c27c65c8530ddd47214c37451c85309f996214c27d65885309f196214c36f5288530db14a214c27f65485309f995214c27c6548530afd91214c2bc6448530b7d8d214c2dc6348530bed81214c2f860485309f994214c27d65085309f194214c2de6308530b758c214c36f5208530db148214c3775108530dd144214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d0130e750f404c27e65901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c39d43501309f994404c2de6310130b758c404c3da43cc130f650f304c2df648c130b7592304c35c528c130f6d42304c27e63d5030d798f540c27e62d50309f58b540c27e61d50309f587540c27e60d5030de983540c27d6595030cfd52540c27e62950309f58a540c27e61950309f586540c23d6595030cf98e540c33c6395030cfd8a540c33e6295030cf58a540c33c6295030cfd86540c33e6195030cf586540c33c6195030cf982540c33c6095030cfd91540c27f63550309f58d540c27f62550309f189540c27f61550309f185540c33f6555030cf98d540c33c6355030cfd89540c33e6255030cf589540c33c6255030cfd85540c33e6155030cf585540c33c6155030cf981540c33c6055030cf0c1540c2be6415030cf550540c27e6415030cf990540c23e64150309f98c540c35e63150309798c540c27e62150309f588540c27e61150309f584540c27e6015030de980540c27e6494c309f592530c27d65d0c30cf953430c33d54d0c309fd96430c27d6590c30cf952430c33d5490c30d794e430c2fa6090c30be582430c27f6550c30cf951430c33d5450c30d794d430c27f6510c309f594430c33e5410c30cf550430c39d4310c30be980430c2f96010c30af993520c2bd64d4830cf953520c33d54d4830cf952520c33d5494830dbd4a520c27e64948309f592520c27e61948309f586520c33e5454830cf551520c27f64548309f191520c27f61548309f185520c2be6414830af590520c33e5414830cf550520c36d5214830bd984520c2f561148309fd97420c27e65d08309f597420c33e54d0830cf553420c2de63d0830b758f420c27f65908309f996420c27d6590830cf952420c33d54908309fd95420c27d655083
  | 15 => 0x8c27f65906309f996418c27d65906309fd95418c27d65506309f195418c2df6350630b718d418c27f65106309f994418c27d6510630b798c418c2dd6310630dd946318c375518c630be982318c2f9608c630dd945318c375514c630bed81318c2f8604c630af990318c2bd640c630f54c4318c27f65c86309f997218c27d65c86309fd96218c27e65886309f596218c2de6388630b758e218c27f65486309f595218c27c6548630afd91218c2bc6448630b7d8d218c2dc6348630bed81218c2f860486309fd94218c27e65086309f594218c2fa6008630be580218c33f54d0230cf153408c33e5490230cf552408c2de6390230b758e408c33f5450230cf151408c33e5410230cf550408c2de6310230b758c408c2dd65cc230d7597308c35f54cc230d7553308c2de62cc230be597308c37965cc2309f98b544c27d62d51309f987544c27d61d5130cfd52544c27e64951309f58e544c35d63951309f98a544c27d62951309f986544c27d61951309f582544c3796095130bbd89544c2ec6255130bdd85544c2f46155130cfd91544c27f6355130d7d8d544c27f6255130dbd89544c26f62551309f189544c36c62551309b189544c27f6155130ddd85544c27761551309f185544c37461551309d185544c27f6055130ded81544c27e6515130cf550544c33e64151309f98c544c35d63151309f18c544c27e62151309f588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d309f996434c2de6590d30d7996434c2dd6490d30d7952434c35c5490d30b7982434c27c6550d30cfd51434c33c5450d30bed81434c2f86050d30d7195434c25c6550d30e7d91434c39f5450d30d7951434c35c5450d30e7151434c31c5450d30f6d81434c2dc6050d30f6181434c2d86050d309f994434c2de6310d30e750c434c27e64d49309f593524c27e61d49309f587524c36f5294930afd91524c2bc6454930bdd85524c2f46154930db548524c27e64149309f590524c35e4314930d750c524c27e61149309f584524c27e65d09309f597424c27c65d0930b798f424c2dd63d0930dbd4b424c36c52d09309f996424c27d65909309f196424c33f5490930cf152424c39d43909309fd95424c27e65509309f195424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930e750c424c36f5210930db148424c2fa6010930be580424c27e65cc930af993324c2bd64cc930dbd4a324c36c528c930be982324c2f9608c930dbd49324c36c524c930bed81324c2f8604c9309f994324c27e64d45309f593514c35e43d4530d750f514c27e62d45309f58b514c3775194530afd91514c2bc6454530bbd89514c2ec6254530dd544514c27e64145309f590514c27e62145309f588514c27e65d05309f5
  | 16 => 0xd5410b30b798c42cc2dd6310b30e750c42cc2be64ccb30af59332cc36e52ccb30db54b32cc2fa60ccb30be58332cc36e520cb30db54832cc2fa600cb30be58032cc37751947309f99251cc27d64947309f98a51cc27d62947309fd9151cc27c6454730d790d51cc35d43547309fd8951cc27c6254730af99051cc2bd6414730dd54451cc27f65d07309f99741cc27d65d0730cf95341cc33d54d0730b798f41cc2dd63d0730e750f41cc27f65907309f99641cc27d6590730dd94641cc37551907309fd9541cc27d65507309f19541cc33e5450730cf55141cc39d4350730dd94541cc3755150730bed8141cc2f860507309fd9441cc27e65107309f59441cc2de6310730b758c41cc37651cc730dd54731cc2fa60cc730be58331cc2be640c730af59031cc376510c730dd54431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730dd94721cc37551c87309fd9621cc27e65887309f59621cc27f65487309f59521cc27c6548730afd9121cc2bc6448730b7d8d21cc2dc6348730bed8121cc2f860487309fd9421cc27e65087309f59421cc2de6308730b758c21cc3765108730dd54421cc33e54d0330cf55340cc2de63d0330b758f40cc39d43d0330cf95140cc33d5450330b7d8d40cc2dc6350330e750d40cc2de6310330b758c40cc3b94010330d758f548c27e62d52309f58b548c27e61d52309f587548c37a60d5230cfd52548c27e62952309f58a548c27e61952309f586548c33f64552309fd89548c27c62552309fd85548c27c6155230cf550548c33e6415230d758c548c27e62152309f588548c27e61152309f584548c37a6015230cf953438c33d54d0e30be983438c2f960d0e30cf951438c33d5450e30bed81438c2f86050e30e750c438c36f5294a309f992528c27d6494a309f986528c27d6194a30afd91528c2bc6454a309fd91528c33f6454a308fd91528c27c6454a30cf191528c23c6454a309fd85528c27c6154a30db548528c27f65d0a309f997428c27d65d0a30b798f428c2dd63d0a309fd96428c27e6590a309f596428c33f5490a30cf152428c27f6550a309f595428c27c6550a30b7d8d428c2dc6350a309fd94428c27e6510a309f594428c33f5410a30cf150428c2fa6010a30be580428c2be64cca30af593328c36e528ca30db54a328c2fa608ca30be582328c35f548ca30d7552328c3ce528ca30d754a328c3cd528ca30f6982328c2dd608ca30f6582328c36e524ca30db549328c2fb604ca30be181328c2dd650ca30d7594328c35f540ca30d7550328c3ce620ca30d7548328c2dd600ca30ddd46518c27e64946309f592518c27e62946309f58a518c35e3294630d70ca518c27f64546309f191518c27f62546309f189518c37551146309fd97418c27e65d06309f597418c2fa60d0630be58341
  | 17 => 0x440b758c411035e5310440d754c41103765110440dd54441103b54110440be98041102f960104409fd97311027e65cc4409f597311035e53cc440d754f311027f658c4409f996311027d658c440d794e311035d538c4409fd95311027d654c4409f19531102bf644c440af191311035e534c440d754d31102fb604c440be181311027f650c4409f994311027d650c440af99031102bd640c440d794c311035d530c4409fd97211027e65c84409f597211035e53c8440d754f211036e52c8440db54b211027f65884409f996211027d6588440af99221102bd6488440d794e211035d5388440dd946211037551884409fd95211027d65484409f19521102bf6448440af19121102df6348440b718d211035e5348440d754d211036e5248440db54921103765148440dd54521102fb6048440be181211027f65084409f994211027d6508440d794c211035d5308440cf90a501033c4294040d794f401035d53d0040e794f401033d53d0040e754f401031d53d0040af98b40102bd6490040cf952401035e5390040d754e40102f96490040de95240103ba5490040f694e40103d95390040ee90a40103b842900409fd95401035e5350040d754d40102bf6550040cfd95401023f6550040e794d401033d5350040e754d401031d5350040af18940102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040f694d40103d95350040ee90d40103b84350040eed0940103b94250040ee90540103b84150040d798f54cc27e62d53309f58b54cc27e61d53309f58754cc37960d5330cfd5254cc35e63953309f98a54cc27d62953309f98654cc27d6195330cfd9154cc27f62553309f18954cc27f61553309f18554cc33d5415330bd98454cc2f56115330cf99054cc35e63153309f98854cc27d62153309f98454cc37661153309d98454cc27d6115330dd58454cc2756115330de58054cc33f54d0f30cf15343cc33e5490f30cf55243cc2fa6090f30be58243cc35d6590f30d795243cc39e5490f30e755243cc35c5490f30b798243cc3da6090f30f658243cc33f5450f30cf15143cc2df6550f30d7d9543cc39f6450f30e7d5143cc35e5450f30d715143cc39c5450f30c715143cc2dc6050f30cf95043cc33d5410f30e750c43cc2fa6010f30be58043cc2be64d4b30af59352cc2f661d4b30bd58752cc36f5294b309f99252cc27d6494b30d790e52cc35d4394b309f98652cc27d6194b309fd9152cc27c6454b309fd8552cc27c6154b30db54852cc27f65d0b309f99742cc27d65d0b30b798f42cc2dd63d0b309fd9642cc27e6590b309f59642cc33e5490b30cf55242cc39d4390b309fd9542cc27d6550b309f19542cc2fb6050b30be18142cc27f6510b309f99442cc27d6510b30cf95042cc33
  | 18 => 0x9f997215027d65c85409f197215037751c8540dd147215027e65885409f596215027c6588540dbd4a215036c52885409fd95215027e65485409f19521502bf6448540af19121502df6348540b718d21502fb6048540be181215027e65085409f594215027c6508540af99021502bd6408540dbd48215036c5208540ddd4421503745108540be98021502f96008540eed0f40503b943d0140af58e405033c5290140eed42405035f5394c409f98a531027d6294c409f986531027d6194c40d7192531035f6294c40d798a531035d6294c40d718a531035f6194c40d7986531035d6194c40d7186531035e6094c40d7182531027f6254c409f189531027f6154c409f185531035f6554c40d7991531035f6254c40d7989531035d6254c40d7189531035f6154c40d7985531035d6154c40d7185531035e6054c40d7181531035c4054c40b798c531035d5314c40cf953431035e53d0c40d754f43102fa60d0c40be583431027d6590c40d754e431027f6550c40cf951431035e5350c40d794c431035d5310c40e750c43102fa6010c40be58043102de63d4840b758f521035e53d4840d754f521035e5394840d754e521036f52948409f98e521027d63948409f986521027d6194840d794d521035d53548409fd8d521027c63548409fd85521027c6154840b798c52102dd6314840d794c521035d5314840db54852102f66114840bd58452102de63d0840b758f421035e53d0840d754f421036e52d0840db54b42102fa60d0840be583421027d6590840d794e421035d5390840af596421033d6590840e794e421033d5390840e754e421031d5390840af98a421033d5290840af582421027f6550840d794d421035d5350840d794c421035d5310840db948421036d5210840be98042102f96010840e794c421033d5310840e754c421031d5310840af98842103ae6210840eb948421033d5210840eb54842103ba6010840af58042103b96010840ae580421027f65cc8409f997321027d65cc840af99332102bd64cc840d794f321035d53cc8409fd96321027e658c8409f596321035e538c840d754e321027f654c8409f595321027c654c840afd9132102bc644c840d794d321035d534c840bed8132102f8604c8409fd94321027e650c8409f594321035e530c840d754c32102de63d4440b758f511035e53d4440d754f511035e5394440d754e511037751944409f98e511027d63944409f98a511027d6294440cf90a511033c4294440d794d511035d53544409fd8d511027c63544409fd89511027c6254440b798c51102dd6314440d794c511035d5314440bb98851102ed6214440dd544511035e53d0440d754f411037651d0440dd54741102fa60d0440be583411027d6590440d794e411035d53904409fd95411035e5350440d754d41102de631
  | 19 => 0xa519033c42946409fd8d519027c63546409fd89519027c6254640dd54451903765190640dd54641902fa6090640be58241903765150640dd54541902fb6050640be18141902de6310640b758c41903b541106409fd97319027e65cc6409f59731902fa60cc640be583319027f658c6409f996319027d658c6409fd95319027d654c6409f19531902bf644c640af191319027f650c6409f994319027d650c640af99031902bd640c6409fd97219027e65c86409f597219027f65886409f996219027d6588640af99221902bd64886409fd95219027d65486409f19521902bf6448640af19121902df6348640b718d21902fb6048640be181219027f65086409f994219027d6508640be98021902f96008640af597409033d65d0240cf54f40902be62d0240be597409037965d02409f98b535027d62d4d409f987535027d61d4d40d7d4e53502ef6254d40bb18953502f76154d40bd185535035d5314d409f988535027d6214d409f984535027d6114d409f99743502be65d0d40cf997435033c53d0d40af98343502bd6490d40d7d4e435035c5390d40be98243502f96090d40d7d4d435035c5350d40bed8143502f86050d40e7d8d435039f5350d40cf14d435039c5350d40c714d43503bb6050d40af18143503b86050d40ae181435027e6510d40af990435039d4310d409f98f525027d63d49409f987525027d61d4940dbd4a52502df6354940b718d52502f76154940bd185525036d52149409f98c525027d6314940cfd0c525033d43149409f984525027d61149409f99742502de63d0940b758f425036f5290940db14a42502fa6090940be582425036f5250940db14942502fb6050940be181425027e65109409f997325027d65cc9409f19732502be64cc940af593325036f52cc940db14b325027e658c9409f596325027c658c940d7d4e325035c538c940e750e325027f654c9409f995325027c654c9409f994325027d650c9409f19432502be640c940af590325035f530c940d714c325039d430c940dbd48325036c520c940be98032502f9600c9409f98f515027d63d4540cfd0f515033d43d45409f98b515027d62d4540ddd4651502df6354540b718d51502ef6254540bb189515037551145409f98c515027d63145409f988515027d62145409f99741503775190540dd14641502fa6090540be58241503775150540dd14541502fb6050540be181415027e6510540b798c41502dd63105409f997315027d65cc5409f19731502be64cc540af593315039d43cc540ddd47315037451cc540be98331502f960cc5409f996315027d658c5409f196315035f538c540d714e315027f654c5409f995315027c654c540e750d315027e650c5409f594315027c650c540af99031502bd640c540d7d4c315035c530c540ddd443150374510c540
  | 20 => 0x33e5350f40e714d43d02bc6050f40d794c43d035d5310f40e750c43d02fa6010f40be58043d02de63d4b40b758f52d02f661d4b40bd58752d036f5294b409f98e52d027d6394b40cfd0e52d033d4394b409f98652d027d6194b409fd8d52d027c6354b409fd8552d027c6154b40db54852d02de63d0b40b758f42d036e52d0b40db54b42d02fa60d0b40be58342d036e5210b40db54842d02fa6010b40be58042d027f65ccb409f99732d027d65ccb40af99332d02bd64ccb409fd9632d027e658cb409f59632d035e538cb40d754e32d039d438cb409fd9532d027d654cb409f19532d02fb604cb40be18132d027f650cb409f99432d027d650cb40af99032d02bd640cb40d794c32d035d530cb40e750c32d037751947409f98e51d027d63947409f98a51d027d62947409fd8d51d027c6354740cfd0d51d033d43547409fd8951d027c6254740b798c51d02dd6314740dd54451d037651d0740dd54741d02fa60d0740be58341d02de6310740b758c41d03765110740dd54441d02fa6010740be58041d027f65cc7409f99731d027d65cc740af99331d02bd64cc740d794f31d035d53cc740e750f31d027f658c7409f99631d027d658c740dd94631d0375518c7409fd9531d027d654c7409f19531d035e534c740d754d31d039d434c740dd94531d0375514c740bed8131d02f8604c7409fd9431d027e650c7409f59431d02be640c740af59031d027f65c87409f99721d027d65c8740dd94721d037551c87409fd9621d027e65887409f59621d027f65487409f59521d027c6548740afd9121d02bc6448740b7d8d21d02dc6348740bed8121d02f860487409fd9421d027e65087409f59421d02be6408740af59021d03765108740dd54421d035f5394e409f98a539027d6294e409f986539027d6194e409fd89539027c6254e409fd85539027c6154e40d754c539035e5390e40d754e43902fa6090e40be582439035e5350e40d754d43902fb6050e40be181439039d4310e40dbd4a529027e6394a409f58e529027e6194a409f58652902df6354a40b718d529027f6354a40d7d8d529025f6354a409f18d529035c6354a409718d529027f6154a409f185529036d5214a40b798f42902dd63d0a40db94a429036d5290a40be98242902f96090a40cf54e42903ae5290a40cf54a42903ad5290a40ee98242902bd6090a40ee582429036e5250a40db54942902fb6050a40be18142902bd6510a40cf594429033d5310a40eb988429033d5210a40af580429027f65cca409f997329027d65cca40af99332902bd64cca409fd96329027e658ca409f596329027f654ca409f595329027c654ca40afd9132902bc644ca409fd94329027e650ca409f59432902fa600ca40be580329037751946409f98e519027d63946409f98a519027d6294640cf90
  | 21 => 0x6054c21af99053086bd6414c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6314c21d798c530867e6214c21db988530867e6114c21dd984530867e6014c21de980530867a6014c219f58053087796014c219e580530867f65d0c219f997430867d65d0c219f197430873e54d0c21cf553430867f6590c219f996430867d6590c219f196430875e5390c21d754e430867f6550c219f995430867d6550c219f195430873e5450c21cf551430875e5350c21d754d43086ef6250c21bb18943086f76150c21bd185430867f6510c219f994430867d6510c219f194430879d4310c219f992520867d64948219f98e520867d63948219f59742086de63d0821b758f420867f65908219f596420873e5490821cf55242086f66190821bd586420867f65508219fd94420867d6510821cf950420873d5410821bd98442086f561108219f59732086be64cc821af593320867f658c8219f596320875e538c821d754e32086f6618c821bd586320867f654c8219fd94320867d650c821d794c320875d530c821bd98432086f5610c8219f992510867d64944219f98e510867d63944219f597410867f65904219f596410873e5490421cf55241086ee6290421bb58a410867f65504219fd94410867e65104219f594410867c6510421cf950410873d5410421b798c41086dd6310421bb98841086ed62104219f597310867f658c4219f596310875e538c421d754e31086ee628c421bb58a310867f654c4219fd94310867e650c4219f594310867c650c421af99031086bd640c421d794c310875d530c421bb98831086ed620c421bb58a210876e5288421bd58a21087765288421f994a21086f660884219fd9521086bf6448421af19121086df6348421b718d21086fb6048421be18121086ef6548421dbd95210866f6548421ebd9121087ac6448421f3d8d21087cc6348421bbd85210876e5148421f9d0521087e44148421f9cc521087e43148421fad8121087e86048421bdd95210877765484219dd9521087b76448421ed19121087d76348421f518d21086f76248421f9d8921087765248421f994921087e74248421f910921087e73248421f90c921087f36048421bd18121087f06048421bc181210877b50940219f992500867d64940219f98e500867d63940219fd91500867c64540219fd8d500867c6354021af99050086bd6414021b798c50086dd6314021de540500875f5394f409f98a53d027d6294f409f98653d027d6194f409fd8953d027c6254f409fd8553d027c6154f40d754c53d02f66114f40bd58453d035e53d0f40d754f43d02fa60d0f40be58343d033e53d0f40e794f43d039d53d0f40af98343d03ba60d0f40ee58343d02bf6550f40cfd9543d039f6350f40e7d4d43d
  | 22 => 0x521cf153214875f53c8521d714f21487b754c8521ed15321487d753c8521f514f214873f5488521cf152214875f5388521d714e21487af5488521eb15221487cf5388521f314e21487e75188521cfd53504873c54d4121d7d4f504875c53d41219f993504867d64d41219f98f504867d63d4121ded5350487bb54d4121ced53504877a54d4121de553504877854d4121ee153504873854d4121ded4f50487db53d4121d6d4f504877a53d4121de54f504877853d4121f614f504875853d4121fcc8750487ea21d4121ded93504877a64d4121de593504877864d4121ded8f504877a63d4121de58f504877863d4121ded0f504877a43d4121de50f504877843d4121ded8b504877b42d4121de90b504877942d4121de10b504877b32d4121de8cb504877932d4121de0cb504877b61d4121ded07504877a41d4121de507504877841d4121decc7504877a31d4121de4c7504877831d4121dec87504877a21d4121af99250486bd6494121cfd52504873c5494121b798e50486dd6394121d7d4e504875c5394121ded4250486bf6454121af191504873f5454121cf15150486df6354121b718d504875f5354121d714d504873f5414121cf150504875f5314121d714c504877950141219f990504867d64141219f98c504867d6314121ddc8450486fa6514121de994504877b5414121eed50504873b5414121de95050487795414121de15050487b85414121ce150504877b5314121f6d4c504875b5314121de94c50487795314121de14c50487d85314121d614c50487f32114121fa884504877b6414121de99050487796414121de190504877b6314121de98c50487796314121de18c504877b4314121de90c50487794314121de10c504877b6214121ded08504877a4214121de50850487784214121decc8504877a3214121de4c850487783214121ded84504877b4114121de90450487794114121de104504877b3114121de8c450487793114121de0c4504877b2114121dcc84504877a2114121de484504867e63d50219f58f540867e62d5021db98b540867e61d5021dd987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf55054086de6315021b758c54086fa6015021be580540867e6415021cf990540867e6315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e580540867e64d4c219f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530867f6454c219f191530875f6354c219fd81530867c
  | 23 => 0xf592534863d6494d219f98e534865e6394d219f58a534876d6294d219f58653487756194d219f982534877a6094d219e982534867d6094d21de58253486796094d21afd9153486bc6454d21cfd51534873c5454d21bed8153486f86054d219fd91534873f6454d218fd91534867c6454d21cf191534863c6454d21d7d8d534867f6254d21dbd89534867f6154d21ddd85534867f6054d21ded81534867b6054d219f18153487786054d219e181534867e6514d21cfd50534873c5414d21d754c534867e6414d219f590534875e6314d219f980534867d6014d21b7994534875e6514d2197994534875f5414d21e7d50534871f5414d21d7950534875d5414d21d7150534879c5414d21c7150534875f6414d21d7990534875d6414d21d7190534875f6214d21d7588534875f6114d21d7584534875d2114d21d7d80534875e6014d21d7580534875c6014d219fd97434867e65d0d219f597434867c65d0d21cfd53434873c54d0d21d7d4f434875c53d0d219fd96434867e6590d219f596434867c6590d21cfd52434873c5490d21d7d4e434875c5390d219fd95434867e6550d219f595434867c6550d21cfd51434873c5450d21d7d4d434875c5350d219fd94434867e6510d219f594434867c6510d21cfd50434873c5410d21d7d4c434875c5310d21e750c43486f66110d21bd584434867e65d0921cfd53424873c54d0921b798f42486dd63d0921d7d4f424875c53d0921bd98742486f561d09219f996424873f5490921cf152424875f5390921d714e424867c6550921cfd51424873c5450921d7d4d424875c5350921bdd8542486f461509219f994424873f5410921cf150424875f5310921d714c424867e65cc921af99332486bd64cc921cfd53324873c54cc921d7d4f324875c53cc921bd98732486f561cc9219f996324873f548c921cf152324875f538c921d714e324867c654c921cfd51324873c544c921d7d4d324875c534c921bdd8532486f4614c9219f994324873f540c921cf150324875f530c921d714c324867e65d0521cfd53414873c54d0521d7d4f414875c53d0521bb98b41486ed62d05219f996414873f5490521cf152414875f5390521d714e414867f65505219f595414867c6550521cfd51414873c5450521d7d4d414875c5350521bbd8941486ec62505219f994414873f5410521cf15041486de6310521b758c414875f5310521d714c41487b541105219f997314873f54cc521cf153314875f53cc521d714f31486ee62cc521bb58b314867e658c521cfd52314873c548c521d7d4e314875c538c5219fd95314867d654c5219f195314873f544c521cf151314875f534c521d714d31486ef624c521bb189314867e650c521af99031486bd640c521cfd50314873c540c521d7d4c314875c530c521f54c4314873f54c8
  | 24 => 0x438867c65d0e21cf953438873d54d0e219fd96438867e6590e219f596438867c6590e21d794e438875d5390e219fd95438867e6550e219f595438867c6550e21cf951438873d5450e21d794d438875d5350e21bbd8943886ec6250e219fd94438867e6510e219f594438867c6510e21e750c43886f66110e21bd584438873e54d0a21cf55342886de63d0a21b758f42886f661d0a21bd587428873f5490a21cf152428873e5450a21cf55142886f76150a21bd185428873f5410a21cf15042886be64cca21af593328875e53cca21d754f32886f661cca21bd587328875f538ca21d714e328875e534ca21d754d32886f7614ca21bd185328875f530ca21d714c328873e5490621cf55241886ee6290621bb58a418873e5410621cf55041886de6310621b758c41886ee6210621bb58841887b54110621d794e318875d538c621bb98a31886ed628c621af99031886bd640c621d794c318875d530c621bb98831886ed620c621f54c431886ed65c8621db59721886f565c8621dd59721886be64d4221af59350886de63d4221b758f508877b50942219f992508867d64942219f98e508867d6394221ddc86508867f64542219f191508867f63542219f18d508877950142219f98f544867d63d51219f983544867d60d5121cfd8f544873e63d5121cf58f544873c63d5121cfd8b544873d62d5121cfd87544873d61d5121cfd83544873e60d5121cf583544873c60d5121cfd5254486de6395121b758e54486fa6095121be582544867e64951218f992544867e6395121d798e544865e63951219f58e544875d63951219758e544867d6295121db58a544867d6195121dd586544867e6095121de982544867a60951219f582544877960951219e58254486df6355121b718d54486fb6055121be181544873f64551219fd8d544875f635512197d8d544867c6355121d718d544865c63551219fd89544876f62551219fd85544877761551219fd81544877b60551219ed81544867c6055121de181544867860551219f994544873d5415121cf990544867e63151219f58c544867e60151219f58054486be6515121cf994544863e6515121cfd8c544873e6315121cf58c544873c6315121cfd88544873d6215121cfd84544873d6115121cf484544873f6015121cf980544873d6015121cf180544873f54d4d21cf153534867e64d4d219f593534867e60d4d219f583534875f54d4d21e7d53534871f54d4d21d7953534875d54d4d21d7153534879c54d4d21c7153534875f64d4d21d7993534875d64d4d21d7193534875f62d4d21d758b534875f61d4d21d7587534875f60d4d21d7983534875d60d4d21d718353486be6494d21af592534873f5494d21cf152534875f5394d21be98253486f96094d219f992534873e6494d218f992534867d6494d21c
  | 25 => 0x67c6254031af990500c6bd6414031cf950500c73d5414031bb988500c6ed6214031de540500c67e63d53219f58f54c876e62d5321dd58754c867e60d53219f58354c873f5495321b798e54c86dd63953219f98e54c875e63953219798e54c867d6395321d758e54c865d63953219f98254c867d6095321cfd9154c867f63553219f18d54c867f60553219f18154c873d5415321cf99054c867e63153219f58c54c876e6215321dd58454c867e60153219f58054c867e64d4f219f59353c876e62d4f21dd58753c867e60d4f219f58353c86be6494f21af59253c875f5394f219f99253c873e6494f218f99253c867d6494f21cf59253c863d6494f219f98253c867d6094f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c875d5314f219f99053c867d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f219f19743c873f54d0f21cf15343c867f6590f219f99643c867d6590f219f19643c875f5390f21d714e43c867f6550f219f99543c867d6550f219f19543c873f5450f21cf15143c875f5350f21d714d43c86f76150f21bd18543c867f6510f219f99443c867d6510f219f19443c879d4310f21b798f42c86dd63d0b21cf95242c873d5490b21bd98642c86f56190b21cf95042c873d5410b21bd98442c86f56110b21af99332c86bd64ccb21d794e32c875d538cb21bd98632c86f5618cb21d794c32c875d530cb21bd98432c86f5610cb21cf95341c873d54d0721bb98b41c86ed62d0721cfd5241c873c5490721cf95141c873d5450721bbd8941c86ec6250721cfd5041c873c5410721b798c41c86dd6310721d794f31c875d53cc721bb98b31c86ed62cc721d7d4e31c875c538c721d794d31c875d534c721bbd8931c86ec624c721af99031c86bd640c721d7d4c31c875c530c721ded4250c867e64943219f59250c867e63943219f58e50c867f64543219f19150c867f63543219f18d50c877950143219f98f548867d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548867e60952219f582548873f64552219fd8d548867c63552219fd81548867c6055221cf55054886de6315221b758c548873e64152219f98c548875e63152219798c548867d6315221d758c548865d6315221db588548877661152219f980548867d60152219f993538867d64d4e21db58b538877661d4e219f983538867d60d4e21d7d4e538867e6494e219f592538867e6094e219f582538867f6454e219f191538875f6354e219fd81538867c6054e21af99053886bd6414e21d754c538867e6414e21cf990538863e6414e219f590538873d6414e218f590538875e6314e21db58853887766114e219f980538867d6014e219fd97438867e65d0e219f597
  | 26 => 0x3150319798c540c67e62150319f588540c67e6115031dd984540c67e60150319f580540c67e6494c319f592530c67d65d0c31cf953430c73d54d0c319fd96430c67d6590c31cf952430c73d5490c31d794e430c6f66190c31bd586430c67f6550c31cf951430c73d5450c31d794d430c67f6510c319f594430c73e5410c31cf550430c79d4310c31bd984430c6f56110c31af993520c6bd64d4831cf953520c73d54d4831cf952520c73d5494831dbd4a520c67e64948319f592520c67e60948319f582520c73e5454831cf551520c67f64548319f191520c67f60548319f181520c6be6414831af590520c73e5414831cf550520c76d5214831be980520c6f960148319fd97420c67e65d08319f597420c73e54d0831cf553420c6de63d0831b758f420c67f65908319f996420c67d6590831cf952420c73d54908319fd95420c67d65508319f195420c73e5450831cf551420c6df6350831b718d420c6f76150831bd185420c67f65108319f994420c67d6510831cf950420c73d5410831af993320c6bd64cc831cf953320c73d54cc831db94b320c76d52cc831bd987320c6f561cc8319f596320c73e548c831cf552320c6dd658c831d7596320c75f548c831e7952320c75d548c831e7552320c71d548c831b798a320c75d528c831b7586320c67f654c831cf951320c73d544c831cf950320c73d540c831db948320c76d520c831bd984320c6f5610c831d7d50320c79e540c831d7550320c79d540c831c7550320c6de620c831f3988320c7ce520c831d7548320c7cd520c831f5984320c6dd610c831f5584320c6d5610c8319f992510c67d6494431d78ca510c75c32944319f597410c73e54d0431cf553410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c67f6550431cf951410c73d54504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431ed504410c73e54cc431cf553310c75f54cc431e7953310c75d54cc431e7553310c71d54cc431b798b310c73e548c431cf552310c6dd638c431d794e310c7b6548c431ed552310c6f5638c431dd94e310c7d6538c431f58ca310c7d4328c4319fd95310c73e544c431cf551310c6df654c431d7d95310c65f654c431d7d51310c79e544c431d7551310c79d544c431c7551310c6dc624c431b7d85310c75e514c431f5d05310c7d4414c431bdd95310c777654c4319dd95310c7b6544c431ed551310c6f7634c431f5d8d310c776534c431f594d310c7d7434c431f510d310c7d7324c431f54c9310c6be64d4031af593500c73e54d4031cf553500c73e5494031cf552500c77b50940319f992500c67d64940319f98a500c67d6294031d78ca500c75c3294031cf951500c73d54540319fd91500c67c64540319fd89500c
  | 27 => 0x319f98a544c67d62951319f586544c77561951319f982544c67d6095131bbd89544c6ec6255131bed81544c6f86055131cfd91544c67f6355131d7d8d544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd85544c67f6055131ded81544c67b60551319f181544c77860551319e181544c67e6515131cf550544c73e6415131d758c544c67e62151319f588544c67e60151319f580544c67e65d0d31cfd53434c73c54d0d31bd987434c6f561d0d319f996434c6de6590d31d7996434c6dd6490d31d7952434c75c5490d31b7986434c67c6550d31cfd51434c73c5450d31bdd85434c6f46150d31d7195434c65c6550d31e7d91434c79f5450d31d7951434c75c5450d31e7151434c71c5450d31f5d85434c6dc6150d31f5185434c6d46150d319f994434c6de6310d31e750c434c67e64d49319f593524c67e60d49319f583524c76f5294931afd91524c6bc6454931bed81524c6f86054931db548524c67e64149319f590524c75e4314931d750c524c67e60149319f580524c67e65d09319f597424c67c65d0931b798f424c6dd63d0931dbd4b424c76c52d09319f996424c67d65909319f196424c73f5490931cf152424c79d43909319fd95424c67e65509319f195424c67e65109319f594424c67c6510931cfd50424c73c5410931b798c424c6dd6310931e750c424c76f5210931db148424c6f66110931bd584424c67e65cc931af993324c6bd64cc931dbd4a324c76c528c931bd986324c6f5618c931dbd49324c76c524c931bdd85324c6f4614c9319f994324c67e65d0531cfd53414c73c54d0531b798f414c6dd63d0531e750f414c67e65905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c79d43505319f994414c6de6310531b758c414c7d643cc531f550f314c6df648c531b7592314c75c528c531f5d46314c67e64d41319f593504c75e43d4131d750f504c67e62d41319f58b504c77b5094131afd91504c6bc6454131bbd89504c6ec6254131de540504c67e64141319f590504c67e62141319f588504c67e63d5031d798f540c67e62d50319f58b540c67e61d5031dd987540c67e60d50319f583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c63d6595031cf98e540c73c6395031cfd8a540c73e6295031cf58a540c73c6295031cf986540c73c6195031cfd82540c73e6095031cf582540c73c6095031cfd91540c67f62550319f189540c67f60550319f181540c73f6555031cf98d540c73c6355031cfd89540c73e6255031cf589540c73c6255031cf985540c73c6155031cf0c5540c73f6055031cf981540c73d6055031cf181540c6be6415031cf550540c67e6415031cf990540c63e64150319f98c540c75e6
  | 28 => 0x55043cc79d4310f31bd98443cc6f56110f31af99352cc6bd64d4b31be98352cc6f960d4b31dbd4a52cc67e6494b319f59252cc75e4394b31d750e52cc67e6094b319f58252cc67f6454b319f19152cc67f6054b319f18152cc76d5214b319fd9742cc67e65d0b319f59742cc6de63d0b31b758f42cc67f6590b319f99642cc67d6590b31cf95242cc73d5490b31e750e42cc67f6550b319f59542cc67c6550b31bdd8542cc6f46150b319fd9442cc67e6510b319f59442cc73e5410b31cf55042cc6de6310b31b758c42cc79d4310b31af99332cc6bd64ccb31db94b32cc76d52ccb31bd98732cc6f561ccb31db94832cc76d520cb31bd98432cc6f5610cb31cf95341cc73d54d0731b798f41cc6dd63d0731e750f41cc73e5450731cf55141cc6df6350731b718d41cc79d4350731b798c41cc6dd6310731ed50441cc77b50943319f99250cc67d64943319f98a50cc67d62943319fd9150cc67c6454331d790d50cc75d43543319fd8950cc67c6254331af99050cc6bd6414331de54050cc75d63d52319f98b548c67d62d5231dd987548c67e60d52319f583548c73f54952319f98a548c67d62952319f982548c67d6095231cfd91548c67f62552319f189548c67f60552319f181548c73d5415231cf990548c75d63152319f988548c67d6215231dd984548c67e60152319f580548c73e54d0e31cf553438c6f661d0e31bd587438c73e5450e31cf551438c6f76150e31bd185438c79d4310e31dbd4a528c67e6494a319f592528c67e6094a319f582528c6bf6454a31af191528c67f6454a31cfd91528c63f6454a319f191528c73c6454a318f191528c67f6054a319f181528c76d5214a319fd97428c67e65d0a319f597428c6de63d0a31b758f428c67f6590a319f996428c67d6590a31cfd52428c73c5490a319fd95428c67d6550a319f195428c6df6350a31b718d428c67f6510a319f994428c67d6510a31cfd50428c73c5410a31bd984428c6f56110a31af993328c6bd64cca31db94a328c76d528ca31bd986328c6f5618ca31d7d52328c75d548ca31f394a328c75d528ca31f354a328c7d6618ca31b7586328c7d5618ca31db949328c76d524ca31bdd85328c6f4614ca31b7594328c75d650ca31d7d50328c75d540ca31f3988328c75d520ca31b7584328c73f54d0631cf153418c73e5490631cf552418c6de6390631b758e418c73f5450631cf151418c73e5410631cf550418c6de6310631b758c418c6dd65cc631d7597318c75f54cc631d7553318c6de62cc631bd597318c77565cc631ded42508c67e64942319f592508c67e62942319f58a508c75e3294231d70ca508c67f64542319f191508c67f62542319f189508c77950142319f98b544c67d62d51319f983544c67d60d5131cfd52544c67e64951319f58e544c75d63951
  | 29 => 0x21076f52948419f98e521067d63948419f982521067d6094841d794d521075d53548419fd8d521067c63548419fd81521067c6054841b798c52106dd6314841d794c521075d5314841db54852106fa6014841be58052106de63d0841b758f421075e53d0841d754f421076e52d0841db54b42106f661d0841bd587421067d6590841d794e421075d5390841af596421073d6590841e794e421073d5390841e754e421071d5390841af98a421073d5290841af586421067f6550841d794d421075d5350841d794c421075d5310841db948421076d5210841bd98442106f56110841e794c421073d5310841e754c421071d5310841af98842107ae6210841eb948421073d5210841eb54842107b66110841af58442107b56110841ad584421067f65cc8419f997321067d65cc841af99332106bd64cc841d794f321075d53cc8419fd96321067e658c8419f596321075e538c841d754e321067f654c8419f595321067c654c841afd9132106bc644c841d794d321075d534c841bdd8532106f4614c8419fd94321067e650c8419f594321075e530c841d754c321073e4294441cf10a511075e53d0441d754f411079e53d0441cf54f411079d53d0441c754f41106be62d0441af592411073e5490441d794e411075d5390441bd59241107765490441ed95241107d65390441f554e41107b64290441ed10a411067f6550441d794d411075d5350441afd95411073f65504418fd95411079e5350441cf54d411079d5350441c754d41106bc6250441afd85411073e5150441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141107d65350441f554d41107b64350441ed10d41107b74250441ed50941106de63d4041b758f501075e53d4041d754f501075e5394041d754e501077b50940419f98e501067d63940419f98a501067d6294041cf90a501073c4294041d794d501075d53540419fd8d501067c63540419fd89501067c6254041b798c50106dd6314041d794c501075d5314041bb98850106ed6214041de540501075e63d53319f98b54cc67d62d5331dd58754cc67e60d53319f58354cc73f5495331d798e54cc67e62953319f58a54cc67e60953319f58254cc73f64553319fd8954cc67c62553319fd8154cc67c6055331cf55054cc6fa6015331be58054cc73e6415331d798c54cc67e62153319f58854cc77561153319f98054cc77a60153319e98054cc67d6015331de58054cc6796015331cfd5343cc73c54d0f31cf95243cc73d5490f31bd98643cc6f56190f31d759643cc75e5490f31e795243cc79d5490f31d715243cc6de6190f31f598643cc7d56190f31cfd5143cc73c5450f31b7d9543cc75f6550f31e7d9143cc79f5450f31d795143cc75c5450f31e715143cc71c5450f31b718543cc73e5410f31cf
  | 30 => 0xf46150a41af594429073d6510a41cf54c42907ae6210a41cf54842906bd6110a419fd97329067e65cca419f59732906be64cca41af593329067f658ca419f996329067d658ca419fd95329067d654ca419f19532906bf644ca41af191329067f650ca419f994329067d650ca41bd98432906f5610ca41af597419073d65d0641cf54f41906be62d0641bd597419077565d0641ded42509067e63942419f58e509067e62942419f58a509073e4294241cf10a509067f63542419f18d509067f62542419f189509077950142419f98b535067d62d4d419f983535067d60d4d41d7d4e53506ef6254d41bb18953506fb6054d41be181535075d5314d419f988535067d6214d419f980535067d6014d419f99743506be65d0d41cf997435073c53d0d41af98743506bd6490d41d7d4e435075c5390d41bd98643506f56190d41d7d4d435075c5350d41bdd8543506f46150d41e7d8d435079f5350d41cf14d435079c5350d41c714d43507b76150d41af18543507b46150d41ad185435067e6510d41af990435079d4310d419f98f525067d63d49419f983525067d60d4941dbd4a52506df6354941b718d52506fb6054941be181525076d52149419f98c525067d6314941cfd0c525073d43149419f980525067d60149419f99742506de63d0941b758f425076f5290941db14a42506f66190941bd586425076f5250941db14942506f76150941bd185425067e65109419f997325067d65cc9419f19732506be64cc941af593325076f52cc941db14b325067e658c9419f596325067c658c941d7d4e325075c538c941e750e325067f654c9419f995325067c654c9419f994325067d650c9419f19432506be640c941af590325075f530c941d714c325079d430c941dbd48325076c520c941bd98432506f5610c941edd0f41507b543d0541af58e415073c5290541edd46415067e63d41419f58f505073f43d4141cf50f505067e62d41419f58b505077b5094141b7d8d50506dc6354141bbd8950506ec6254141de540505067e63141419f58c505067e62141419f588505075f5394c419f98a531067d6294c419f982531067d6094c41d7192531075f6294c41d798a531075d6294c41d718a531075e6194c41d7186531075f6094c41d7982531075d6094c41d7182531067f6254c419f189531067f6054c419f181531075f6554c41d7991531075f6254c41d7989531075d6254c41d7189531075e6154c41d7185531075c4154c41d7d81531075e6054c41d7581531075c6054c41b798c531075d5314c41cf953431075e53d0c41d754f43106f661d0c41bd587431067d6590c41d754e431067f6550c41cf951431075e5350c41d794c431075d5310c41e750c43106f66110c41bd58443106de63d4841b758f521075e53d4841d754f521075e5394841d754e5
  | 31 => 0xcc832e7993320cadd64cc832e7593320ca9d64cc832b7987320cade60cc832b758e320cb5e538c832bb58e320cb6e538c832f394e320cbce438c832f350e320ca7f654c832b7d95320cb5f654c83297d95320cadf644c832b7591320cadf624c832d7949320cbcf424c832f3109320cadc614c832b7181320caef654c832dbd95320ca6f654c832bbd8d320cbcf634c832db94d320cbce534c832f3d0d320cbcc434c832ddd46510ca7e64944329f592510ca7e60944329f582510ca7f64544329f191510cb5e4354432d750d510ca7f60544329f181510cabe6414432af590510cb755114432be980510caf96014432ded42500ca7e64940329f592500ca7e61940329f586500ca7f64540329f191500cb5e4354032d750d500ca7f61540329f185500cabe6414032af590500caf66114032bd584500cb795014032d7d4e53d067e6294f419f58a53d067e6094f419f58253d067f6254f419f18953d067f6054f419f18153d075d5314f41be98053d06f96014f41d794f43d075d53d0f41bd98743d06f561d0f41cf94f43d079e53d0f41e754f43d06be61d0f41ed98743d07b561d0f41afd9543d073f6550f41e7d8d43d079f5350f41cf94d43d079c5350f41af18543d075e5310f41d754c43d079d4310f41bd98443d06f56110f41b798f52d06dd63d4b41be98352d06f960d4b41dbd4a52d067e6394b419f58e52d073f4394b41cf50e52d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d076d5214b41b798f42d06dd63d0b41db94b42d076d52d0b41bd98742d06f561d0b41db94842d076d5210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d06be64ccb41af59332d067f658cb419f99632d067d658cb41d794e32d075d538cb41e750e32d067f654cb419f59532d067c654cb41bdd8532d06f4614cb419fd9432d067e650cb419f59432d06be640cb41af59032d075e530cb41d754c32d079d430cb41ded4250d067e63943419f58e50d067e62943419f58a50d067f63543419f18d50d073f4354341cf50d50d067f62543419f18950d06de6314341b758c50d07795014341d7d4e539067e6294e419f58a539067e6094e419f582539067f6254e419f189539067f6054e419f181539075d5314e41d794e439075d5390e41bd98643906f56190e41d794d439075d5350e41bdd8543906f46150e41e750c439076f5294a419f98e529067d6394a419f982529067d6094a41b7d8d52906dc6354a419fd8d529075f6354a4197d8d529067c6354a41d718d529065c6354a419fd81529067c6054a41db54852906de63d0a41b758f429076e5290a41db54a42906f66190a41bd586429073d5390a41eb94a429073d5290a41eb54a42907b66190a41af58642907b56190a41db949429076d5250a41bdd8542906
  | 32 => 0x2bd185544cafb6055132be181544cb3f64551329fd8d544cb5f63551329fd89544cb6f62551329fd85544cb7761551329dd85544ca7c6155132dd185544ca7461551329fd81544cb7b60551329ed81544ca7c6055132de181544ca7860551329f994544cb3d5415132cf990544ca7e61151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d329f996434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d329f994434cb9d4310d329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e6590932cf952424cb3d54909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424ca7e6510932cf950424cb3d5410932af993324cabd64cc932eb993324cbad64cc932d7d52324cb5d548c932f3d4a324ca7e64d45329f593514ca7e60d45329f583514cb775194532afd91514cabc6454532bed81514caf86054532dd544514ca7e64145329f590514cb5e32145329f980514ca7d60145329f993504ca7d64d41329f987504ca7d61d4132ded42504cabf6454132af191504caf76154132bd185504cb7950141329f990504ca7d6414132d78c8504ca7e61141329f584504ca7e63d5032d798f540ca7e62d5032db98b540ca7e61d50329f587540ca7e60d50329f583540ca7d6595032cfd52540cb5e63950329f986540ca7d61950329f982540ca7d6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3d5415032bd984540caf56115032be980540caf960150329f990540cb3e64150329f98c540cb5e63150329f988540cb6e62150329f984540cb7661150329d984540ca7d6115032dd584540ca7561150329f980540cb7a60150329e980540ca7d6015032de580540ca7960150329f992530cb3e6494c328f992530ca7d6494c32cf592530ca3d6494c329f597430cb3f54d0c32cf153430ca7f6590c329f596430cb3e5490c32cf552430caee6290c32bb58a430cb5d6590c3297596430cadd6490c32d7952430cb9e5490c32e7552430cb5c5490c32f398a430cadd6290c32f358a430cacd6290c32b7986430cade6090c329fd95430cb3f5450c32cf151430cadf6550c32d7d95430cb9f6450c32e7d51430cb5e5450c32d7151430cb9c5450c32c7151430cadf6250c32b7185430cadc6050c329fd94430ca7d6510c32cf950430cb3d5410c32b798c430cb9d4310c32bb988430caed6210c329f992520ca7d6494832d790e520cb5d43948329f597420cade63d0832b758f420ca7f65908329f596420cb3e5490832cf552420cade6390832b758e420cb9d43908329fd95420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420cb9d4310832eb508420cabe64cc832af593320cadf64
  | 33 => 0x8154ccb3f6555332cf98d54ccb3c6355332cfd8954ccb3d6255332cfd8554ccb3e6155332cf58554ccb3c6155332cfd8154ccb3e6055332cf58154ccb3c6055332cf55054ccb3e6415332d798c54ccb6d62153329f98454cca7d61153329f98054cca7d6015332cf95343ccb3d54d0f32cf95243ccb3d5490f32bb98a43ccaed6290f32cf95143ccb3d5450f32cf95043ccb3d5410f32e750c43ccaee6210f32bb58843ccb3e54d0b32cf55342ccade63d0b32b758f42ccb3e5490b32cf55242ccb3e5450b32cf55142ccadf6350b32b718d42ccb3e5410b32cf55042ccbad4210b32af99351ccabd64d4732cf95351ccb3d54d4732be98351ccaf960d4732cf95251ccb3d5494732ddd4651cca7e64947329f59251cca7e60947329f58251ccb3e5454732cf55151cca7f64547329f19151cca7f60547329f18151ccabe6414732af59051ccb3e5414732cf55051ccb755114732af99350ccabd64d4332cf95350ccb3d54d4332bd98750ccaf561d4332cf95250ccb3d5494332ded4250cca7e64943329f59250cca7e61943329f58650ccb3e5454332cf55150cca7f64543329f19150cca7f61543329f18550ccabe6414332af59050ccb3e5414332cf55050ccb795014332d758f548cb6e62d52329f987548ca7d61d52329f983548ca7d60d5232cfd52548cb5d63952329f986548ca7d61952329f982548ca7d6095232cfd91548ca7f61552329f185548ca7f60552329f181548cb3d5415232cf990548cb5d6315232db988548ca7e61152329f584548ca7e60152329f580548cb3e54d0e32cf553438caee62d0e32bb58b438cadd6590e32d7596438cb5e5490e32d7152438cadd6290e32b7986438cade6090e32cf951438cb3d5450e32bbd89438caec6250e32d7d95438cb9f6450e32d7951438cb9e5450e32c7951438cb9d5450e32d7151438cadf6250e32f3d89438cbcc6250e32b7185438cadc6050e32e750c438cade63d0a32b758f428cb3e5490a32cf552428cade6390a32b758e428cb9d4390a32cf950428cb3d5410a32b798c428cadd6310a32e750c428cabe64cca32af593328cadd65cca32d7597328cadf64cca32e7993328cadd64cca32e7593328ca9d64cca32b7987328cade60cca32bb597328cb6d65cca32eb993328cbad64cca32ddd46518ca7e64946329f592518ca7e60946329f582518ca7f64546329f191518cb5e4354632d750d518ca7f60546329f181518cb755114632ded42508ca7e64942329f592508ca7e61942329f586508ca7f64542329f191508cb5e4354232d750d508ca7f61542329f185508cb7950142329f987544ca7d61d51329f983544ca7d60d5132cfd52544ca7e64951329f58e544cb5d63951329758e544ca7d6295132db58a544ca7e61951329f586544ca7e60951329f582544caf7615513
  | 34 => 0x90b755114642ded425090a7e63942429f58e5090a7e61942429f5865090a7f63542429f18d5090b3f4354242cf50d5090a7f61542429f1855090b7950142429f9875350a7d61d4d429f9835350a7d60d4d42d7d4e5350af76154d42bd1855350afb6054d42be1815350b5d5314d429f9845350a7d6114d429f9805350a7d6014d429f9974350b5f5390d42d714e4350aee6290d42bb58a4350b5f5350d42d714d4350aef6250d42bb1894350a7e6510d42e750c4350ade63d0942b758f4250bce63d0942f358f4250b3f5390942ebd4a4250a7e63d45429f58f5150a7e60d45429f5835150b775194542b7d8d5150adc6354542bed815150af86054542dd5445150a7e63145429f58c5150b3e42145429f9805150a7d60145429f98f5050a7d63d41429f9875050a7d61d4142ded425050adf6354142b718d5050af76154142bd1855050b7950141429f98c5050a7d6314142cf9085050a7e61141429f5845050b5e6395042d758e5410b5f5394c429f9865310a7d6194c429f9825310a7d6094c429fd855310a7c6154c429fd815310a7c6054c42d754c5310af66114c42bd5845310afa6014c42be5805310b5e53d0c42d754f4310aee62d0c42bb58b4310b3e53d0c42e794f4310b9d53d0c42eb98b4310abd62d0c42eb58b4310aad62d0c42af9874310abe60d0c429f5964310abd6490c429fd954310abf6550c42cfd954310b9f6350c42e7d4d4310b3e5350c42e714d4310abf6250c42af1854310abc6050c42af9904310b5e5310c42d754c4310b9d4310c42bb9884310aed6210c42cfd0e5210b3d4394842b798f4210add63d0842e798f4210abd63d0842e758f4210a9d63d0842af9874210abe60d0842af5924210b3e5490842bb5924210b6e5490842eb9524210baf4390842eb50e4210a7f6550842afd954210b3f65508428fd954210abf6350842afd894210b3e5250842af1854210abc6050842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210bae4350842eb10d4210b7751944429f98e5110a7d63944429f9825110a7d60944429fd8d5110a7c6354442cfd0d5110b3d43544429fd815110a7c6054442b798c5110add6314442dd5445110afa6014442be5805110b7b50940429f98e5010a7d63940429f9865010a7d61940429fd8d5010a7c6354042cfd0d5010b3d43540429fd855010a7c6154042b798c5010add6314042bd9845010af56114042de5405010b5e63d5332db58b54cca7e61d53329f58754cca7e60d53329f58354ccb3f54953329f98654cca7d61953329f98254cca7d6095332cf98e54ccb3c6395332cfd8a54ccb3d6295332cfd8654ccb3e6195332cf58654ccb3c6195332cfd8254ccb3e6095332cf58254ccb3c6095332cfd9154cca7f61553329f18554cca7f60553329f1
  | 35 => 0xd4394843dbd4a5210f3f4394843d790e5210f3d4394843d750e5210f1d43948439f9865210e7d61948439f9825210e7d6094843e750d5210e7f61548439f1855210e7f60548439f1815210f9d4314843db5485210ef66114843bd5845210efa6014843be5805210f9d43d4443be9835110ef960d4443e750e5110f7751944439f98a5110e7d62944439f9825110e7d6094443e750d5110f3f4354443d790d5110f3d4354443d750d5110f1d43544439fd895110e7c62544439fd815110e7c6054443e750c5110f755114443e750f5010ef661d4043bd5875010f9d4394043ded425010e7e62940439f58a5010e7e61940439f5865010f9d4354043cfd0d5010f5e4354043cf50d5010f5d4354043c750d5010e7f62540439f1895010e7f61540439f1855010f9d4314043de5405010f5f5394f429f98653d0a7d6194f429f98253d0a7d6094f42d719253d0b5f6294f42d758a53d0b5f6194f42d798653d0b5d6194f42d718653d0b5f6094f42d798253d0b5d6094f42d718253d0a7f6154f429f18553d0a7f6054f429f18153d0b5f6554f42d799153d0b5f6254f42d758953d0b5f6154f42d798553d0b5d6154f42d718553d0b5f6054f42d798153d0b5d6054f42d718153d0b5d5314f42d794f43d0b5d53d0f42bb98b43d0aed62d0f42d754e43d0b5e5350f42d794c43d0b5d5310f42e750c43d0aee6210f42bb58843d0ade63d4742b758f51d0b5e53d4742d754f51d0afa60d4742be58351d0b5e5394742d754e51d0b7751947429f98e51d0a7d63947429f98251d0a7d6094742d794d51d0b5d53547429fd8d51d0a7c63547429fd8151d0a7c6054742b798c51d0add6314742d794c51d0b5d5314742dd54451d0ade63d4342b758f50d0b5e53d4342d754f50d0af661d4342bd58750d0b5e5394342d754e50d0b7b50943429f98e50d0a7d63943429f98650d0a7d6194342d794d50d0b5d53543429fd8d50d0a7c63543429fd8550d0a7c6154342b798c50d0add6314342d794c50d0b5d5314342de54050d0b5f5394e429f9865390a7d6194e429f9825390a7d6094e429fd855390a7c6154e429fd815390a7c6054e42d754c5390abd65d0e42cf5974390b3e53d0e42af58b4390abe61d0e42af9834390b5e5390e42d754e4390aee6290e42bb58a4390b5e5350e42d754d4390aef6250e42bb1894390b9f6350e42cf94d4390b9e5350e42c794d4390b9d5350e42afd894390baf6250e42eb1894390abc6150e42af1814390b9d4310e42b798f4290add63d0a42af5974290b3d65d0a42e798f4290abd63d0a42e758f4290a9d63d0a42af9874290abe60d0a42bb5974290b6d65d0a42f398f4290bcd63d0a42ddd465190a7e63946429f58e5190a7e60946429f5825190a7f63546429f18d5190b3f4354642cf50d5190a7f60546429f18151
  | 36 => 0x40020048000001000d001400100400030000003001000100100010010001000000000080000024009000800c000000e0000004000800d00140000000041000c004002c0110000005000000000140150004012000c002000c000001400500140050008009000000a0014004003c00900240040024005000000700040010000001003400000440040000001000c0130020030000c0020020004002000d000400100600000048000001c000001000a0000001000000a000000000100030000007001000900cc002000c0200000025000c000000000100040000024011000c0010054019001c016000401f000400100240020014025000c0070000000000400000040000050002001c001000c004000000c000c002001800500080010014002001c00400036f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0f7b50943439f98a50d0e7d62943439f98650d0e7d61943439fd8950d0e7c62543439fd8550d0e7c6154343de54050d0ebd65d0e43cf5974390edd65d0e43d75974390ede62d0e43b75874390edd60d0e43dbd4a5290f3f4394a439f9865290e7d6194a439f9825290e7d6094a439fd855290e7c6154a439fd815290e7c6054a43db5485290f7751946439f98a5190e7d62946439f9825190e7d6094643cfd0d5190e7f62546439f1895190e7f60546439f1815190f755114643ded425090e7e62942439f58a5090e7e61942439f5865090f3f43542439fd895090e7c62542439fd855090e7c6154243de5405090ede62d0d43b75874350edd60d0d43e7d4e4350ebe6290d43af5864350ebd6090d439f9875250e7d61d49439f9835250e7d60d4943dbd4a5250ef76154943bd1855250efb6054943be1815250f6d52149439f9845250e7d61149439f9805250e7d60149439f98b5150e7d62d45439f9835150e7d60d4543ddd465150eef6254543bb1895150efb6054543be1815150f7551145439f9885150e7d62145439f9805150e7d60145439f98b5050e7d62d41439f9875050e7d61d4143ded425050eef6254143bb1895050ef76154143bd1855050f7950141439f9885050e7d62141439f9845050e7d6114143af5924310f3e5490c43b75924310e9d6490c43d79524310f9e5490c439fd954310ebf6550c43cfd954310e3f6550c43afd8d4310f3e5350c43b7d954310f5f6550c4397d954310edf6450c43e7d914310f5e5450c43e79514310f9f6550c43a7d954310f1f6550c43e7d894310f9e6250c43e75894310f9c6250c43e7d854310f9e6150c43e75854310f9c6150c43e7d814310f9e6050c43e75814310f9c6050c43e750f5210f9
  | 37 => 0x3000000400000030004002000400c00040000010010006c01b000c00f000800800000030000002001801f000000c001000000000040000000006000a002c0000000001008c0180000001001000e0020002007c002004c00000200030034001006c00b002400e00000050024014000000000400010004004001000500080020000006000000100240130004001002000600040000004001001400b00040000000002001000a000c0050008000000c003000400a003c003002c0020010000000400000040000008002001c002001000a0018008000c000001c008000400000000000014000000000800080020000000003800000b802b000c00900000000010015000c0030034001009c00e00040050004002000800000000030004002004c00b000000100000000004009000c00d0014001000c000001001b0018004000c001002c00e0020001000000600080000000002000c00000040050018001000002a004c0000014001000c0080028002008c002000400300040000000006001c000001400800000120004002004800000000050014008000400000200010098000004c0020000006004400e0000009000400e0004002000400f0008000000c001000c0020020001000400500000080000001001400800100110020000000400c0000000000c02a0000000004c006000c009003400a000800c000c01000080070000001001800e0004012005400a0000001001400700000000008001004800400240050030000002c00000000030000002001000000000000024000000000000180020044000003001f0004001008400000200060008012000c0000004002001800d0000012003403b00000010014005003000300080050000004000c00e0000001000c0280008000001000000140000004000001000100000100010002003c0040000008001c002002800a00080060000000001400600000020008003001c0000008000000c008000c0010008001000801b005c00200040090014000001400000680030010000000002700140050008003001401300400000004011000c00000b80030000002001c013001c003000c00100200050000000000000100140000024005001800000040010000002001000000300050000017002800200000140004001000c0020000005004000900140110004015000400f00000060000001003000f005c00000140100008001007400000080030004004000800000a00050018005000000000040010000002000800900000020000005003400000140070000001000000e0000000000c0020000003001800b00000010008009000000100140020004005002c007000400000040080000000000c00000000010008001000400000b000e0034000000800a00040000000002001c00300000070020000001001100040030
  | 38 => 0x80010004000000400000180080010004000400b00080320028000004000e0004001002c0000000006000400100dc00000040010014001001c0020000002000c001001800d0008000000000b001405f0000008000c0070000042006400100800030010014003400700000140014000000800000000000004001003000100000000040012000c00000a000100180020000004000001d0060020001400000240010008001000400000000020008005000000500180010010000000c001000c0000008003000400c001000f000000000000010000003000000600280060024002004800300740000014002002800200080050004000000001d000400200780000030000000000400000000018008000000000080060004005000000000080070000002000000a0000001000801300080010020002000400b001c0030000001002800200000020028001000000000140050004008005400000000020024002001c00300000000000030001c0000000005000c00f0000001003800a000800000240040000000000800000000050000011000001000040000008003000c0050000007002000000340030004004001000b00000010028007000c0180014012004c0010010000000400000040100038000000800a002000e0004010000c00d001000000080010008001000000500000030000000000000f000400000000040000003000c0010000009000000300300000054002000400700000000004000003002300300090004018000800a003000000000090000000003000d0024002004c001000000f000800200080000000000002400700040090004001006c0010098000000c00100040020000000000000e00000020000001000401f00000040018002001001300180320020007000c00000080150004001001000000000000000000000c000000000000000090018016000c006000400400380090000006004400f001c00000040010000012003c000000000600200020000003001400000100010014002000001d001c006001400000080120044000009c00000040010008002003c0140004002004800b0000000002000500280000000000000c005002800700380050014000000000a0094009000c008001400000080090010009000800000000020034000000c001000000000300000014001003c0470000000001401b0014004002000000000000000007000000a005c01000000020000000000000000080040014006001c00300000060004001000400000080000008000002c0020000003001c00e003800f009c0000048000000000100040000004000003c0020008001000801f000400100440070020001000c0010000000000c00000140020024022005c0000004000001c0030044000002c016001c002000000c0048008003400b0000001000c
  | 39 => 0x400400100080004010002400000040010008000000800800080090000001001c0030000004001400000000190038001000c00d0004000000000500140000008005006000c000c00300140000004000001002200080000024007001c00100040100004001000800f00580190000002000c0090004001000400400040110048007000c0010010009000400800a800000340450000001000c00c000c000000000d002c000001000400000030004000002001a0004001000000000180020000000001c00000040000008008002800400240010000003000800100080000000001000000000380000040000003800000080030004002000c0010040007011000800080080008001000000000080000000006001800c00400010018000002c00500000000008006001c003000000200200000010000000c000000c0000018002001c00000680000000002000c00a0004002002800600040010000007000c0080004005000800e0000001000c0000014000000000000a400300000020004000000c002000c00f0004008000c00f000400500000190024005000000000000020028000003c005001c0540000000000400e005000b000c00a000c0040000000000801c000800f00100040000001000001300280040004003000001d00000000014018001400200000010000000009800a009800100040000000012000c00600000040018005001c003001000000080040000001002000000a000100200300000001005c0050020007003400200000000010002006400400200000010000000000a00000050008002000c004005c0140094000003c001000000300100010008002001000e002c0030008002000000d000c007000c01700000000054002003c00f003000000000080014001000001300000000008000004c001000000300040000018014003c00400280000070003004400100000060000022003400000880000040002001000e0050006000000400200090018009001c00000040010030011000000a0008005000000000040020078006002c00b001000200840010028000000c000001000400040000040006000c005003c00100180110008020000000600b8002001400100000010018004000000600540040014000001800e003400700080000090002004400100480010078000000001000000080060001001c0160004004000000100000010000001006c00d0050011002c000000000b0030000001c0080000000000c001006801c000c000004c002000000000040080098016002400900040000020000001000e00000020000000000c000001c000000c00b00080000010006001c01700140000008002005401300080060004010000c00300080090008001002000100040000004006001c00100000040010006004000c0030004001400a0034007
  | 40 => 0x400040160000010000401000040090000010008000100340020018005000c014000c00000e8003000400000480060004003003c000003000000100120008006000c00200000030008001001000000300180000001000800000040000000004001c0050020001001800100a40000038001000c004002000000200000004005000001b0008000000c00e0004003013402c002c005000403100040330000000002801000c0006000800e002c0180020003000000c0008004002400e0000000000400b0008009001c00b00140000004000000400100100030008003000000c00240080008000000c0000004002000401c000c00400300000058009007800f0000001000000500000060008003002000600040000000003000000300100010000000001002b007000200800230068003000c0000008004000c0050000012000c0010038002001001f0008019000000300040000008000000c003002c0060014001000000000080000010007000c0000000006000c0000000002000000900180010034000002c01a000c001007c000000000100080000020008000c0070078001000000300400060024001000c01a0000002000400000080010000000009000400000040000009002c0020034000000401e000800200000060008002000000400000010010007001401000200020010000003c001000000b00080030004003002800700140030050002002c00200100060018000000003100080000068006005c0080000006002c002001c00b003c000000401900000040028002002000d0014008009000500000030004000004001f001000100a802d004c00b00000040000002000000a000400000780010010013001000500100010020015000000100000070004017000c0160000003000000b000000000040000000000001000800000000044000001400a0008003008001e00100080084000002000d000400000000020000000000001e000000200000010000000000000000300040000008000000300000030018019002800000100050020002000000100140010004002002800700000000038000000c0130004003002000100000010060006004000300000000000002000001e00000040000000000000200140010020002000400600000000000003000000c0014000000c00c00080050008000005c01700040010054001000400e00000060004000001000100080150004000000400000340050018008003800e00000020004000000c0100024000003c000000800c007000e00300050004000000401000140000004004001002c003c0060034003000400a004800000080020000000003c0080094004000c000001400300080010004004002801f00040040014001000000400580140000002003000e0008000002801600080020038008003c009000
  | 41 => 0xe33400002b2af64aeaec300c1e4760000088222213c80000003182ce3000040b8000a0c00000000000bce11986f714866fd2fdcf71181236d985ad9285867b633ecd74bbc4000168605b0bbc1e009d40003484753a5c600008ce9faa9324e412f400009d20720e90d4d000040c049ab9b0000000000000000000001f82000000080c00c20003216e753dce8f4aca473c149200007d86f6ae94608b2e6b783602928a8cc000065c0870000d6b0414bbd800000000000003a4e3c2ba541760438b45a80ce84baec2d895be0003b1497a07cae7102b8000382e00019fab841cecab40122dfd85d60958814efc92ba2ca1ff47178a8865d28c0cb29bb6872924edbc800000000005bf8fd4000336e9891f288e7362c6279a8c7ed18c80000000e1e0000000041e0001b0c000000000024f22640000645a0320001ba00001c4c0000000f6580000002dce0002b12ec1a43e498a1ea00035c40002de8000257405fb122000000082fbc0a0003ab032380009a2870e6273c9ebf29e081251c0aa700000d3eb936000236600036b0076393000023b8d16ab6c0000000000015c99a01245750000bf48000000000001f802c31132f20000000ad708ae000000000004de000000008b8000000186a43eae421c080000002e1cc62000086eb374c07800083635b8f7029e65f7862e032993e16c90624fb8bee000000012d00003e384540002b7e0001b6619683ae8d511d6e0e875cc0f0dac3928000a223da672696de00016a400000001f525f23598000abda842a6927fce461f22c22000021837940000000f2014ded8cb2480000000000000000033780001e8ab35000085600001b09c327648000569084200020de0001bd892d990c2303beeb2f80004b1245c0001dfa0002d323f880000000000433000015c8000f59230a00016f4723b48c2af97f81cf957899300000000000091adfe22096e41e400000373c6a000000060d355400000001e8800000001420002c800000d0a68a388c0000000bd0196000031be00031f00003b9e7cf800000000000000c10df58000000000000038bc312122458c8000000000000021fe6b60aae20c9986000218600000000001034a038000000000300040000000000000000500000020008001000800300040000000002004c0000000006000000600100040000000001000e001c000000000200000040000001002801a003000700200060008004000000000140000004000000400600000010010001000c007000c0050004006000001100000010014013000000900240020038000000400900180080000000006c00a000c00b00000000010003001800600000010014000000800900180010000008002c001000800000580070044005000c006000c00100000000010004001c0010044004000c0000008000000c000000400
  | 42 => 0xd20001fbc52b00aadd2b00262aba52f682bda019a828000000077935a0aeb14fa5bf0bac3bf0e92b518000c8b83ce3350000000177a0000000bef00329b3000000000009469caa0000000225b94ed4b0e3c0c9016600000003b0855cb7f34069788000d6a975094236964f7aedc49d345807b317c8bf3b5243b8144ac90000c0900000003bf6e6b2c92000037464ba468a6809404ac8b88abf902274d8ff4f1b1b5079f8d06102809eed608f229dafce5b4993c0000000dc52f080000000e2d924cd0c2594ed224c01279182de08bcc98380000002650721b3467a992dc0c51e5e000391403f26d600021d00082fb4c78b94200001f616300000000000000059c3a22b2cd5c87f22949d9e7548b36b5f80000001374879b67c629167eb4a30f8c9f00009200000f22b80c00000000002fb00000000013b9cea23b47ebff308cb4125a80f480006e200005a480008ce0000d5205c60003d148c7000026c000000000000001f1600000003b32bc022792a687027840780898344b7fc9398caeb4828ea4aa0caa13b97da03a35c0cc5903c6f80c983e52c7a478b988a1690989949b8ae809720000306ae3b99ca896bcf0ac29c5a15f17be8c438a60001a18c90967af40bdb200000000fea188df8394a8de3b1e3d01ff05d3a4767fe36a8e5729580000f7ea9e83fe693090a00020c2000000000007a6a2700002d7396223a1592000000000033aa864b54c00000000003630ad6800000032560000000be20ffea593052e0ab79027302bce900000798000031e204ae2b821814388024070000000059200000000001b0e7f599c61fa1a2a1e4ba3edeb39e8b920000000083eccf8ca66e72dae95b304c5c30df494f19c89f3b160683076eb8f94583d294ae4c91612ba287005b0a5b264e87fe2a788b68759c584bda3d03dc35803170b8adc2198ee98b6fa5eda712bb492a0bb40c3c3d6bd2249a80001f42364000081600039de39904dc0000000360937eb318f3466a0000000100000000004d2b1a0cb9398600000e4000020022900006ca9d6847aa8f600017860688000e04800053c028a9a1800075239c8b1f8664440b49ce19a370e371d745ba9ca008a800000000005c896700000f38000000000003e60c485263d521bed9c33e27801e1e6193cb423580004531e240000ef6b25865606a000000002787d28698000365692e80005d02734537317a00005ec0002e76535acc40000000e44b1267b4283e154362896d15e40000000b2881f2251800000013f03940d4259c80bc1219208b2c1b2216a04e2f1e0000d57ab3e31c0000e7000009ab311c22c8eb6c4bacfe24c0000acd92d658e10a84b983bc8b8b6863ef9968f1d9fa20002ce44dc3528a53a3a6539b59a3aa8d944dd80000002a72b9832f0da00000e02897a8ab1d1c6c20000bde0b7a4e
  | 43 => 0x93580001332d4e00004b812b91a4b1c19ee3028758ab88000e87871600000009bd8ddceb08f50e580000edb800000025003eb3836d798ac0b943a84739b0ee0fa97b0ee9000000032a600000b02da29689aa91b41b3369a000070c00038d2e79a16e0000000916b372cb69c680000000a250fa641f80c44ec800045d27ae43b125c7c400000001500011135aacca490ccd2f60df3a8e465095f008f2b044aab0bce3e0062ed3198a435800004094720000000e3399ea00000004372d74ceb0000000000074ca59c0001eb0804a1bc273a1782771f460c72948365a216dcc19c200000000003dae1e58000000042e378800000400000000000207000070f19587f980007a40d5079400000000000d72b2849e18000829019200024be000384869e3090958800050bb49e8bb98148f50000df117fab8aab020002cf05382790ec48366bab0f6600000000001f8ed3d80009388000ad00d44a5086e6e7f300c48100009dc82600003c1c44118680003d167a58c1a72629f2c2b3b5a415000000000000002e9cae9800000000003c9b87c00032ee3e4022ceaf98a802934d8bc09698d25a0d6cff1fa80000370882a618d2db5c89b19de6af2a5decee861e7d236b22822bf8293aad4b0016aad3a1fdcaa11d302459e52d02b6c45ef0eca9e21bbe6e680003c20000bfa8000db290b8c62893e86107c8be41f08f180286232a10a00004fe075a4cc4581890b99149c492b3a200000005da356c00021b00001782cee17e01a019d85878cd625583101599b44c7f2fa01e62d80000385419a9cca0000dd00f5822296eb6c6b57a974ef70adc94db24eb94bb4400017082ce0858f44bd5c3c62fd0000000000000000001498cd89dee9a0197a0001504605828e0002f280000000c01ae0e00000e26021e2000021360000000d6d9c6000000002468382000000043200007079f4c000171800027de33a172e000221c09c26327a3a4088668cd2ea42a744e2800000013d40000000000000077c06c6e9592689c68000000000000000001610000000129a66580001c43d8422436600000000000000016f80000000174000303e00032ce97d0000f04aff8ea88540f6e00003908000a8e00001f91b3a0003a92000232a000133e00030461290000bc380000001b1a00000005dc8000ba880008a43402310000054daa7c5c9195465c2496ee98eb0e6fa646e3fb0f6c618696a792086000000000011f46b202725e60000ccb2cca4f180007f43a240002c9000007ce0002ddcc6b81b0000194400028da00017c063f00009d226e66ee96ca15d000000022000002edab7b00000d69e86af4b8b07f6874244c000007a9e6ccb88b7c00007320002982cf19066b4f11fade69f6400025507170000be6985ceab96fa3bcb39cca8334ab061648000000057ca7609ba2a
  | 44 => 0xb2812800047479f12be28000a1c16000002e2800000000528af200029d636cba7489b000000000009342b9e0002c54d54207e757a35aeae3970a4e00000002a0ed7727d6e472dd4e540cf214235fc1da00000001db0000000000000004b83d24790877293087c043a85e835037368029392bcf0f80c65b0580001fec08280a80001c3000031360002e3200013b69b91304dc815e69b78c4c000286265928b66882a9c0d78146db0a94a1ef0000769382200024b00003a4427c000000037d2611000075f0000c4b0000eec0aa2a2580007a6258c000221207180001da80008c1015075406a411d9e0ce1f9824281ad26e53000000015d6271bc968939de20000cf8423800070b277a0001552730b482936b85241d20924ce99f81e3226a88980003e1286800031ac5b104309d5b746b132d38ce6a4c679508561ac82240003b24d758678a599f3200023fc39cb244d84b0b2dbe2724543b4c62f625607e9823044ba61aade8dea000000000039d8000000011a00000000000000279a18a376400000003a02ba20003958e6e9784ba43a462603d3200024fc00017ba0003bc600029b800014780000496d7c8000d7080000002684d83aa24e660000ca2000000000000000a4a4d52f0c6da8000523384e0000e82417b0fc5761f028b18f48ed0ad2a0002e2666b9cfe00000000003dc6000305a3d82cdaa679f04000002ebdf0000de729ba04d160caaeaaf87818c76b93339e4493a1a61f8000d0412b40003afc0002f9e083871e4e01218e68bc7c02da7b88b981dc0798822da48000000092877c8a14833966e13a0000f262782735a9fedbb800041b9cbc00f8000da72e0a000000038b080ea0031c85d0a8caf1fb390948800034c800000008b800031a26ee2328000067e00015861b7807c2d7a87c0002322c5e271cb1480000fa377e9ea800055da7402c58c9aae435860000000000000071d0000eb027980000000ddea218e1881104570000c8b2112748a5445cf05300001ade3930a7c4b1a63a179208cba6960209a334c500b94678b35e0577afc4e520b748a90336b6d8cc42bb25e62411b5c0001c9ca95af1e8c5aec01a6b63adb737f8533a9124c01fc240e8000d8922c8f472b527401d029c4042c4c80f864eeb1067b028d6f4c1f18cb41f2600000000001d3a0000000b8926ae00003c27de23d6699069264919827fa8b7eacf26fae16aeeec82890e46408923072edeb5138aa58bbd6ca6db768a7a8a8673abb00000312aba98868d032d7c00009c2ed58000eb580000003264000000000017a800000001981efe72796b2397032ab1ab1e4000020c18717a418d0000520a1a65a7000006534803c0a86c66200007eb047499f254c0008c58d950000bb3a13a7f50000cfe8424acb92120001eb400033daafe8000e180c86a7731aa000046c0
  | 45 => 0xcfbb9a682d201aaadb724000097e000197c90a000043e00008f88aee44616bac178000b1418c64fc829e3acab94479145a2789f367be2324c5d83a49418000be89e0e0002bf4c631e3c658a70076f345e0002654638327a1848924000101e5330000cc0a170e0739000d2a62673c80001703cfe71b08003cf225862c1b2ea901dc412f8000000000003a80001850000e5d32c0000177ef0dac26aba1b4ecbf81be8788000ef980000000000b790000000278c528a18000000000000e5800000000001200bf5800000000000001d66bfa288081681840000000dd60000b810000e8b81389113aca8b38000550aa82a07a09800000005e3217a99c96c8844050069baa7e0003aea1d5acfaa361f624033826a9c1cd0c9a8bdacab2ed4c3e84489229f58c45b0b845e8dd8ee3b24087a2d10758001200000006923b80d2fa1461530af400000001d894e84db0a5c332848000003a095234fe67913ea5d901fc0be01d4000102800014e4b0b96644b2a77cf4f2ea4efd2c34b502c7417aa41a19135608cc9d8a000000052412320003d609dbaac05cb2330b0387fc628b8648e233a876e100275fadaa2841e32dca87ba86a8b42000113cb919a1cdfa000000023c2bc99c2eb6ebcb051280003a71466ead000e29fa286845b8946d60000f67800000038ec00028980058000b78a2cc42f212cc8db3c2bd60000000117e0000a3a4ccb170d3b80005fa07128b10000000241ebc8b0e434e0280a2e0196f62a8a027ebca0d6c8c82000000096d921482d800090f1446136800011c0000608056cbd7a43678b83b2d049850f250000cbd8f8a2fb01f060116b60002742ab60000000000002baa5a29e0000bc480000003a66429034619980009568000c67848c0fe3c48d0a800000016ecddc800000031ee9b125d40003c920001e4ee2823440003cb60001d2eb7c038450224ec9140a244c68f28b221f767fca18c0001d4a3892dc20000d56944274a150978e643af0656a8ae8cc3911c5fc929c066a2060000d86b4c2204f06a5eea0d3648000342229e872c6409cc40000000562000000026b0a8eb0cc00013aa1021ee698a9ba68a8366c2fd3168baa0130f038000c438b12542b09af4b198c0000ae4000163c9bf0000a7b06ea00037d03733b0a2ff2c9a0000f626033c180000000352350400028d4596158a00008b015e964a1cb843a21180000000000f29b2620003000000000014d12e20a880000000e12c4827a8000358aa10236c4ed2ff4000000000038443a5b2b4ebe3184b2a2a8862e05eed768000b0d8e00e2790a0dad00004d13c169b3920e1692eaab3313720001c880002a6214705d0beb9052bc5bd06791800074f00000000000d329f3073910f6e873b7c553a0144a1b404aa6adf66e1b93a7d688863d586aa103a926298324c8a2113667a3
  | 46 => 0x23b02f1368250b000014a35563473cc2c8100240002c1481480000a73d7e0002bd05ba13180000bc800000008598f68354a9f802b119271ea028a2f8000b0714e2d44a8c42be979641e92024c5b97a08516f0bf79bfc9e3973add7adbe98280005e722521730df805c8870bd230223a68e0edb620e273491ec4ab0d0c2a91488d990418e3ab1dc5891a38eb411d46f18e5e08f982c03fa874d54b0785c3952a07a26eccb59b3c9248000a2d000034ebb7625abaa6b3bab265aa3a1614d97b2dc59a3000031f200024dcce500001a99c16009800039499724c200000000000cba38a28d49d8ed14800032b32180000dde0000ce6000343625baff2a5d86aec0ba80449b8b220003872db8bd523c400006a827d468b0000e343658000090892909a20001656e20a57a000000000000000000c220003dc246b3bb4b4e9992e9db5a46340000e090000b9e8000bbcb448104ae204100000000256600029c8d5d81807593ab248c2b388af000021b000097da65a25b13da6f890d86651b10b60bb8a4829bd0000118a17084f05d23daa0001480901138c0b98000000000044a0170b541db46692d02e5daab200029f400016c677d000000000006558000bea800000000000001990c4c109caef827e0000c3442d000000020fe0000000ebba7780000000000320c7dabd0e00011320002832d33000045f3a0a89a282e0000000000201800020049158000904ae300002644af20b2e77530b430eb8581d2227a060ab6400000000000000000000000023fa0000ada031a9e8ba005b0c6c05e0250a9b0cf434e4071327252a331c094a162737000021fa8c85278de6a73047e000000000010867baa3a400000000000000000331a0000000f6d25140622cb8cf913a4192238c000000031c9ddaa930c089d314d828310c4a938000000000000029bebbf8000bdb8f06f518000e7a8000702078a14e000000019ba000000000000001cc258ac271c700002ff607b93b00000000000000083480000003ab63391b8c808bcc40001a3a37028bcb7300007288000984aacc1b4000020d800058b16544880000ce59b56a1983780002c10c100000374bdca0000a94b7580008b680004cf232000015b80000000e4f8000000000000016804f200003fcae547aa1cd4000046e00021640001d0c86880006d7af74ca19bf2cae0000f60af9400021b200000008fb2ebad078078e0f80000000000a1e9f6e0003cf62213cd2877a55278aa1482870d9c00033e096780005b834400002738000000000026be0f00b7091b33984c1a4d400008266f9a69ea8b3384a02350015c000029605a0caebae01189cfc5940000000055e0128828b30a5a66ba30b023db80e413211c445a4546ec085cc31a82aa1489ca00033e8a13292224d209caee2a54695392eb9580004f8044c2813486
  | 47 => 0xe8c080008110fd2b198000d98b192c929bc24cd2d3e719800000030ca000000000000000001f9680d296e000186640d9c9023181ca85696ce8be9af65a28000e830000385060200000000002f50000000086580002618000000000092ba30800030341562e828ff8652000158438080009ff8f6a0002736315a8f04cc256800000002678000dd8173233f2d4c2e50000ecf80000001b6e4ab80000002cd2a4928a40000000dce8000f7436de0000000000000000008ac000063eb7a80004e180000002cc8000000000000000938000f4a185e3b40428095019c615031e081939cc1cb76aa7826ee0000000b5aad880001700d29800000000001110fc42330000bc92b10813a0f625f2a004f98000000008ee6f2e0c000359c238079e96080008c31a5eb191c92de1b4fc0003344000000000000000000000000302af46276688821fa01315184ff8fda819841cdf6398c33200004ca80004d885324630f1e0000ab4be980000000000cabb546d7380000003b2ac978000000000049f8c163edb99c000000013480000001c7600009d62a30000e3504a80000000000238e8b80b840003bbe00001b25cdafdaee09b54ec6800032700007deaade00033140000b985650000000175443c9eca0001e7682b800032c327800000008431b26a0725d09bfb5180000000aaf000070db2528971ddce9e3366000023a8ed2f543251574affb1b84f6314a0000060000216a00034941988000d971c14d10800033d9fcc0001b362a2ae5c8d4285637b08fe71cb0b6db207dc8460000c9f800027d000023c000045e2f6a00000009b6ad0e000000000017c45bdac021dc153289036ae87c20d04778d0279d0b92c1ba1ee2b081186c002f204eaf5a4498df08e6147e6ff9c6200004c0ae18000cb8000000029fa0640008e860000d42814e6428000ed380000002dd01e180007b68000caa853ec9a33427a0086a1fc3666000282000000007a7976ed4f83b65070a4439213fc4341f70d2b0a640002a8e00027a00000a90ea80b6430391863f218760000d3c8aa80004bb2b543b72d5acd49b02a1900008510000786818c000143800038860000000000279e57d06ce409000041c3190000000094e148ee3038f400008660002e98e9f00000001aa2bd899ecece874640e371c770ab600000a127beb56a29d00ee5280ca4256341a4ca2890d228000da426a0a2a0000634999a68080008d2b6980001fd8eeb37c03128baa00033b49d9250c48babaa34b3234873add816b0e1c10f31a68b08ed2ebe978a3bd2b7c9ec31e09e2800000007e29700000c229dbe2e0bbe40e20000c56922cb2d09b81bda122e259a902450000d7324347550a9a07030148f6159a6469de80000efeda20000a2e9b1608c9dc6008b7406d8000030c00000001414000375c0000000f4f8ab8cd4
  | 48 => 0x280003ab983ea611d0400012a2d933060f3500000003d7027418c0637bd50333b57a0001ff60002d1e0001f0e7320000000206e000000042ca1ae4d1a89e000000000005fa00038de0000000d51140642504ce00036385c58000000207400035bacb4934c73605baa432b28e272078000000058d80006000000d240bd4f03000097f2c44a8f80006e60000964154c56b0000d7ea3362a382bae11a6f0211000022297dc52f15f8b2b3cd6f04094a2d6075a00015c251d800057a80000000f0e000239a0000000d2f17f4000044e80200001a18000d8b96dcbd2afcc8e18000e058000a11272800025f82b336260001920cda2aaea88adf22049c28eb9813edf7941266d1c200000000f1e9f342c515ccdf224862372768000142aa80955827dba10f6a00008851c0ed322e9655f0000000368c0330000bcf86badef8e984060000d778a6ccb138faa5f94d48f92f987c9227e7e1b944e66b4081e39e3e06d0ce03eb98cee9c09e00bdad64ac38fca1f826922f01a9ed0000002dd800000030f4a2c9a6a7c339323cc035c46d800014ab292e22a85c85b0cfa976b35872c97feb92a2020000456000262200019da000000066980001e700000001dfc00035ec00014ba0001ac64feb540ef8bd7853f00009fe8000b12aa1400007cc682b1000000458c820000deda4de00025046501c1863e131e00000000000000bba17c60260000055352eaf93a8e2862d146cfa0204170b0605e9e829ee95b08140068dfd0000c76800039a343e674975ee38253e000347a7a83ca46479df8aa02cd834a8f76000000079e8f7435e9dd630a8000ddb8000000141ace39ae20001a34ecd00007ae2e8c090ae12a7498ca0001aea000000000004c4e390000b6c27e00bf3b0c3b53b22559992c7c028ae2d104d09e89d6af19af103a9a2b0cfd16460790524a028c206c63a4a3ee20ea2cb37fa256809626839524ac3cda2400a341ee22b44c28daee8a80002168a9806b00000001a009c831b20000000dd3a3487a3000000000000000000c251af8f2aab8ed63a53047289d88dca532f3d234caafa18a000080c00000003d1a32e0b0395400005bc0000fde6a480001de3cae0000000af1000040802c4000000000018dc0002dc017e0000000221a63ea7ac15b86c01f1968e0002bc65718000761a13200008aa9eca30e91f884888786fc0000000000092a57f3620b358cb41178000f268000dff8000edc959857e80006c2851882298e4f620964df50e26034109eb2617aa572064c00016a200000001148000a831142d158e360000000945a5805a5096874e3da2a8c8d166b2b96eda8b0ba7d598e612a80002e68000000233c0002d4256580008a5b36c0000c907829fdeb710f5287480000000000704b97268f91dc83d2aec2fa0050aab266e36f05f21e118fe29bac3
  | 49 => 0x842f0a8c20a8112cc142124063aada000206072031ec1e839080000000000000000000009621936e8f27bc0001fee000087c00027228e5800086e3b02000000000035820000000000304a4a0158cc46ae660001cba9f932b270694748d586009c580005818e5a2e4000000015eeeb1900ef30326cc7e97d87568f78041838c53b02c29fe01a08a7a142c759f74f4004343e5bdb63b1bcbced4353c34ba1069cab814ca0800000009f85d30000d39800000019a28d39d6cc17359e00000000001e5693e851292a00000001d703768000cbd238a000000000000000000000470a5fe836800000000007381c46000293445ab02cea720a200000000002392993901428b0000e71a3e6ee100009adb7a69d8bdcc433a06a000000000000004442f3a8d8a3a03debd86d43b9ecf4d86b6d2e12c879881e25b00e444c3000030092d0b9887be1b734188f037c6435341cad136da15a07820da91aa2f7bd8e82515502de252c2012a86450113eb749704b1f0684e8d0070624ad86854800066f047c2db90b04b4a998cd7ab6e551a89af5880000000000000317400013f6e170000ababcdebf180002179adcba480008ed86e22ffb9260001d2450e8000c03800003c81ba0000000e2e0000c4f1378b418000b102c32bcb3aa81cd9ad2deaa198b1c9a60c108000000208000030e80001874000279c00033f800039165c78000f46bceab179906a571e58c1b186200008500001a7a31380003588ac4db3104200000000ad869c8c609ea04b295200013e4913000000023ce0000fd60000000132000064c367825c00004998058000383cf430000ae3290460a31badb5ba585cf84202ac3694e88af1a00000000001e7c09d2754b6b00008d737b83ea364426a8000000387a0001bac2042fe2b2f03da0003cce127058e7b7a62e0002ae6000274687f0eee745b44abefbcca69f00000001d56d2a800087e38f02133a5af14b23a00016f23eaa394494b7ee00000c88c4905a000309eb8e0c92373b3f04eb8e3872d00000002242e5b000076bad00000000000011b23c737cc651800057a23b2f39092691e0cbe38d00004713ccceaa9ba4c533cba61babce8008000ac7a8b000016840001d9477a80001af2d900001a40d4db8b441a2b769ad08bc8483b5c207a17c07d0f827da3718a3ca7045dd8000c4089c07973afe00000d2588800056f24b231436acd03ab62b0a37f0609afd4cebb6ce00035f400000006b300000000cf099e293c4b685d2dd59fe066c8cccc6dba422fc003c3c8a0cc2cf970204abc5076a31c278633640a3328ea15291c7111a94a008114ce0ace02fca07a51593e21bd3abc6670dc2f3e36ea000095200017c200000000000000000384200005940000360ed9000026fa90eb378ed893fa28cf3635746133a72000246274801aa0003d38e3
  | 50 => 0x4e3ad24e83226531a7580000e7c00031c4000264aea6ace885726b29fd1c380abb3240000e102d0000075cbb4a5fb00003581a44695800000025926f3a5c218ca7020ccbd4c52a80000212c867e7988c37f80000000676000000000036f4000000000011da35e00004bcb1340000000dc49e14066209ebc032ec00026000000c6e63b20ca9e480002e9b3600001d76cd5800019d0000ab38cf4000000060629ce773a910109a7966bc19520002bcc0003828bbc0ad2226bd4e48a0cbce7d17ce6fd8d36d56b7a242a84669ae1766e47b622f0e912aa709084ee832c209298484d795806c7344eef4071c244b968cf519ce60d800047b854679b82381042e74ae683587a6800071f237a8402a52ec7000000011885c1b50800036501350000c8f80cef092410933952e000263600018c42e5944cb0900000000000bea29547d49a500018db89873c5cac1800000037883fe31c047435e800011661d3bbbaa829ea4e64887a796bc72f4ebbde390168c96f3d7af241a4aa6f214af3b0b8c2a8307cef20564299ae580961fb65349d120002f34158b2deef6b832d650b54d90000000000002c9229217d80be0a48d240001ca800010c2000386abeb3380efeb11200023687ab00007b089748e8a4a60002e167e9248e0003c880000000d4500000003d72ea025ac277800051a139a82e0714dbf395a2f91e448ea115ee39a51c24b1aec3f82e840000bd0aac000037a1dd8817bd5a0af977093dbc060001e48139abea0000000000116449412d4bee08060000000026bbe84953aa44f1262809715dad1a026a0878c268cb30aa1cf113a9f0000000000004d21ad06ca3164420b9f269722ae2353c14bad204026b8000f010efa3cb05dcc94187cab58b1ede4a498ca4190480306eed3d262000000000000e760001e4a2f39b70531102a0001fca95ab476c5718700003c4c1b1082ab17009079a94f62550000000000000003c611ea43aeb722a6ee4a75000000000002beef372a9400023841b90d08aa90a0209f1b76bbe8f6e90a8000042800094b88f89148000d190f9cd3034a041b3d762622694cc29064a06a9a60208000c420708a670948b8789100c8b70475325981088000ef824260000000b9014f2000229c9fb08d8597b7b2685293e4872a08301060415811c8e9a00fac5b064edbfb0ea668000000018100002126c9d0576e72a0c6a2893cabfe8b864049516e8e89020002f4ebc6032e0730000e41346edf93c54733000000031ea4140ea2000076c0000000f50ac0800a0000054894cd9d00001608d540002e360002960d2eaec43f396169c78000502b8cc3b780006798000000384cbfc000072daaf0000000074f84d600000000001c9400000009c200001ed2f1cf2f800093c18e80eea7f600000000cc21c824cad2ce6d9714699811c00025
  | 51 => 0xd05800000000001c1237687c800042ba03600016a0000093c00000000000000952928a00023c6af508526ad036c0000d8c000000035700000001ce80000000dbb00000002e5ac0a0726a5eab46d26a62c6e433ea00036680002a26a6abb9ccbe00000d38000936010c0002f4ca42800000000000000000700000000031bc47da578f0aae7c2d1ac4813e06a0000257e00037a4c668000290874a52d00b26d8a2a8debb5a62349ca600019c0000044a00021c60000000b79800073e9f94e7c015e46580008b7ba48eaebd4401cbb9abed8000a6380005d63610404000032e000000039b80000000c7a0000f52b00838aa730cdf9e2800000000b72cd080f1256b8b109600020dcddf08e41ab048a7ab9aa46dcbc62e640cc2f1a0000310b884e0e17d635f0c2c000047200000008531b8e4d43c44a501d7a2d40000197af720000000e15813cf162a1edcfac38061b92c000049800039aa7efb614285862411718d426b000094ab754000000011e2d782cab5622d6b4dad378000000054a00000002b78000000249a25780003afb3360000522c970d7651a939e182a42cb82385e84d1e888f828e2903008ad64158251ea99a00020a600c0fe4000021a00009a85d58a4c00000000000396000173847f800000023800002f6c00000000000000d1e179482ea7c27933578741bd04caf2ba472c08a828993820ca1ab260eab6a1e232d47aeb3d21513a8cbbf39dc0e7000041d80000001170ab90000000058859e00004f08000d8329f035294b22f70000963aeea1c684884f4800000000006c800003a3980e288b97e48a800098c248c3cd80003cc9c3a85a00004d08f4e8920000022374400018e2223027a17d05b489c800005a220e6d1a89235f8b9e6abac586f930107f00c666ec8000000197e00022b20219b40362000031a9b9ed813d6e6ea1a0ebb1bd68d6f341403d800002528365e99bde7b5a696568a2be6751dd000000001960000c29b5ee00000002ec32dc685b354a9211206470000551147c6b535689c28000a510a3e00007288790000d8f000047c2246c24a4ea93a01bc269bc64d11a8e07e2a9c4ca58b4e0002e6895c1b32caa159000008fae8c0000000166051418ae38190e6c5cb618aee80003aa150ca9a0eb8d2d2a5cc4929b40000b30e369a68bfb92ead762244000156222fa68ebd5ad58ed183549a416d60000738cb639f8b030e224c5335ad4e939681594ea649a744d7c048e38f89f20f402965d188c2b13975c5e00a0e508a6a44e3800000003343ba86f0628361c88c8a3c0ac8cee6b380000002826d9bb00a4b0011ec7e066ec9500003440288bac000000008f400013d04a38000e8c8a6a4d6181cb718ad4409a92c731b8b2f168e6e7b8365280918ac179a488422989a3578da0ac52a8c9272e149f896763388e308
  | 52 => 0x393b9e08a0000035c8000b8b80000001f88b209b78951aa924013700db93a8a0002bd895798940001c02cc005160002dee000374c4f33752152242e1288000bd080002e8bc4e7100dfc75b8000000354e000329c00000000920000a348cdc1b4918e91ea4e052c3bce68936e6a1b97b8d0e2fc29a8a84e7ec119edfc87ec96e05f000015ba83b34200000000b4734aef6f80000000000000000000024d2d57149a162937a687800018334b099800347eb891c90c92b618c1a4e3300abcebd39c2911a2286ac0e08b0f16b49282c6e54e0ff67cea9469bd1aa6d743db000017e6d23a8848c51326d441d9c000255400000000000e6602d29a21168352110186c1f69e923c1063a000000000018d6000050c99d30f05eb0e741f9b8020003d34522800030a0baec7d890c39e2a2e16ab3ca57426f8e67825a4ea1a0600021b4dcd1fe816883fc00000007848a5e93b866c3b200008a880009db1ebc0001556c7d0ca00000000000322a7098000429a44e42020b000036be89591be29537969e525aa5fc0dc8edd37ba8f736ba613a26004b99b62aeb22255291b8e12968206e3a96bda1856bb985deabd23f259d2e4e696abb6ef09faa12c0b487f38000e76bb04000000082b25ea0413770bde80004ef8000ab12e00f09b8927e128864c889a48be001463a94c802018a60003bb2f1280000002d8c40f8000b3020f873d2970311b1fe80798f480395487e01cf6c520000c51bd949002a6e0000aa66b119fc684a91a0003bfcaa891e6000283c7bf15646a3800066f80000000000ced9b7acce80000003a388c998f616e0000dea3cb2ce8129671939d2000000000025fa00000004b7b6067682d1200000000000000000359200000000000000af88000000166241239cc0001ee22c68000ae00c621bb381a0361dcc6bfa0fab3883e00000000c1dacf61820e54b2eb86ee4680003ab084e0000000ebd9284d5980005010bba2ee00006df00001d32ce695938c6b231c6e9e9a2b6c5fa47c0000000a55abe0afa000000038086781eb6b4934f8a340b720001f9c62d9c42d9c9a84e97853aedf90bacc9b0d0a990920a5ca5d6f49b62a00002aacdd8c84d96a872b9c800045880000001bbc47a0000b0c0000000000073680004f390781411abe1ec886e00000000000d74d661258be180007a88000e75b4f0000385078734ecebcab6600030206fa800000002643bc000000031d0f66364ebf200000000162000141e88aae3c00027b6ccb8bfa52d800094a373832e82842c81d5c1c88fb4336af820db803a55b8000d52a74eeb38dbe00010beb1a000061e00007c78000ee89a9c43296424bfa75a0002d7a31d2d9438e80000d3033eb188000dec16a6309356ea4a0ba8035ac9422032764a903dea232ccea460000eb126660002f20cbe80000000
  | 53 => 0xb45403c3a6aae5ac04630a9a84e89e366feb888652800035b8000968030e000000081da2100002d5c0002c5a00000000000000000171a8130bf66821b3000000000000000000285091924429dc371e00017f6000228e0001d8c0002bdc9ed166c8678d70055ab74ef5b2cc53e12b87903b8ce5f1e94000000098180004018000e6caafc1f7ba261e6a92a7bd1f407f1a6ea00024ca9b48aacd87b93cdcca2dc00034d20ab1ebed9da980dd20de4aecb50225da48242317cc0289360ac80ec0ea5203ad1cb8c431915f6abc8e7005638987120000f2883beb1d8176b46272e315000028bbc22000000000000003d6360a9978074036988e5702e340c200000000e7eda803726b936a6532b1cc00025245862bf60001fc4a97b156a11b21411ab206557000000039ee000368e00005aeda92eccba802d0e8834e208a000049caa444bc23ea49b0046090179a8ba0000e29000000012422ec80000298776000000000000000000000000068e0000610f389ca412caf8edb4b154bb2217297480005712ed828a9a9ae500000607a0826949760860b51aaa424ac29409c4263000000005804b380de3db291e5b329f60a41b6ce6c3b668dbb8ac1308000c15b93404489e8000000000000000001da2f102a1c0000a0a0070000077840658a8fd80172e9e7ba35a2d6c1a26525925a772abb00001a74709030684525f0a4800007e48d580001f5c17f050aca500001d8062c0000000a9aa1d400000000000cfe2cd132c4300c321d0000000019f0000152600000002b5ac1e769b232c33ad9a00039780000c3e644000000014f41eb0c7a0001d5800013f8000055435681a600000000000000000030c0b2a2d80001f2cd1816d453baa2a1df8d84a42123aa99a93000039a0c8e30040da1d8050602042bf8000cb205a6f0c29780000000d6100180000000000000000030f288d84c66ed233a69c2c2a8a50bc63e6049000000000000d6c0003ce667c80000000000000000000003b00000000995b778df6ad84e62a4945ae01a400002c60000000db0000000024bc00000000002f14e442bf25b409e66963b96cac351cdc33a820000e5629c2b08b80a460de004ba3e23adec96a09010faf8c0003032f2124705df1948950bdd43a29f206b582e2f108000d110000cadba640003bd80aa0d980001bca4488b0e66c0c061de8ae2839956c49811f2987a05869c956075e29008bb1c6a0000b0c0109df6f4b800059f0000a2080000530dd6a0e2f92dba0766cdc3634266000022395ce3f1aaa07a117ca99206f2823bbea3b680b83be000000001360002262000151446c00007c18000000329aa180fa21ec29900002c8e96196080000404667bc321c2901a7f92d768f2236aee2301a8fd2b34e07916c83a34d688f8000167bcb80e426887150f7cb280000865084a
  | 54 => 0x8d4929021c829ca2ed951055786400c69e66d4e00002e91a3c6ce15a03183dacc4c8ca80808dd4e8dbbf8982361688c0b00ad4015a089a85e9a9854e0b684ea0000f64e102ba03ecbd58b05b72200002c8a751d886f206e00582f30097a6d4000000000000007eea35e0003834ac633a6019294c65700006c9000070a9aeee0030d4000250a547a2f419a098e9b2a4f800009dac98151200029b20003ae8de12174e559726000000000000006731fe206295e265a852c5e780000000000b11b492cc8800000000000000d28ca7b07000015a631fa67e981124800007f600036d00000000ba18000c2b8e8427b83043918000d1a80009279c7850d9fa00001c964f01092f3ebc2c6aea6bc79e00000000f8c0002c0a0000000c4517a2000224ae81110ad33900ac7539800003b62a8d2b5e4a0b2249770b8083c8eb4a9b3accbb2981a0000b56c312d620000872ca93c82a1a923eca62d360001b047452ab4614b88e95dbb2c9739f5e0d080000c28250adc005654b2ebc0000d344e61b52f523b6c3e782a4546b10acf7b3ce5a780006d21d1adbc2a462aa9bf00101ab6bc2a54eb08a7180a60000e94370a35326f20ddb3d85899998c2929060468f4200019800000000000000033b00006d08c367cbb8f6c8f00007b9345000000000f882b0cbf000000035640000000000197800001fe1b280000002bbc00021b66fa0294cfd8ae08bc0000789b78e7d100002c0aebe386b0c8d4a8000000276a00000007d800000000364761000010680001c632664ba2cec8a100003cba9e200000001fe0aea98f80000002a1a0001a325f493362c111120000000e35b86c000109a000315e0001922ee400000001bd4d1700008f10000e241bd240c800006db982cb183c4905bb9830b8000b68a23a4c38460839099a810a1cc00000000002bae0b58e0c00039fea7b86420002d08876902c765bb789781410452040c7e43c5e434afe435a3ce063c23bc9b4255c24d8000c121238aff16e605b8502317b4d4eebb37c04a2d9862c8874ad394260b7944e0002adc895273eddd0000000000037d8a92622b0363b98e9470f8c9635aa31ef6729d80000338d1b1f0aaaab76649eb4880000000ca30a829501ba230333bcb6c92764901fd27df9afab7297b400016b05fa9c842320ea4be7240a9960c68000000048424f44e12430e639840ada00007088000ea20000ecf00003340000e7418841d7b110b2b98880002d4a0002dda3fb33c08978000882000000023ae413800000016ac0001f1a20ea93a84213dc0f91cb899c0a9c3f038be44d082027f800078c27a40000000478000010c97785a68cb21c904fa0003c381df19c43b8adf80001016000292e2e38000ce4881800020c8530acf2f0b8000c25a5be5880c88000000043a0000540859a0003332000091869d
  | 55 => 0xa38189d7aed64d002767138000567194c0001a2e71fafb260199f64738cdea0b224ccc4000041ca7be67411aea61ab9c19522ca2daac60f4233b018aa6e058e9e02de600000001ef01af982ec6530d6def0000dc680000001a22000000000000009d48000000125e5ff1144241ba6e349b7420b4b18edae2f84b862822c849146a37ab78f3ca0062f9a3822543a4cd508fb030e03501442726ef2995e2adaca677b06d4bfb03f6d482c2c9f62b8248d1790cafb1ce454192a36906b0777a70608da20cec208a0454b28a6ebb11841a99fe2f49244c9c0000f0fab00183973491a91d29b700000000fe8bb8a9fc0520590ec9963e931364685403dc5d6ac8ac881788a8620ee1a42994eda964c31f1d445c4a5d862033cc9438d9a1ce85feeb22b720b905ce919b4f290883f028cb82029cab560281b06bffb9841b5a98c4650ec4f3b93523d324726b9a1a8000165a20207508df000055694842629c8a2a589928ae9a8accab79e00000000000000000184a00028eee8a0bbe60e04ac3e69056bb8000000000009a71e70000005e1cd0000be5800000010de0000622b0480000000e60000200080b272c00000008b42992cc603a254e800048f0da20003810000000000011a000000007498aa800027ca000096648184d851b8000e0101d0a3d35d4b42a81800000000003066bd707d202334c42cc864a843aacaf2b24205032dbc4cb9eec9df953cef023e87db36e0c368de014f100809121a000033c4a1f8dba2a038307cab3c8aa5800000016d800020380000000e20000022998329f3000022d196e0000f1a0c08b3a704110ca04a7ee00013bc14bb8fc9f19a4632db5e25480000766000000008fc0000000351a11a0000c6c4a6009c9f20000306115aa8c11fc7300000043a15e436b7ec684201c48d81d2b97b806a980000000357052f81080000000000033c0000000a8f3ada0001246bc1000000017ae00000001713a6000000000000000000001e3203d4020b0132364000000000f4000000000000001fd00000bb00009a68000ccf000000000000003bb66fb8000a12af2a000038a00000008b591f8f218000f4780003a182fa5938000b5b968834800000001b68b59800000018f200028c6c202eec003000045506fe91602a69c33044ece31520c00eecc2883261b60af0c15334858c2e8e412811611092fa99e896287b1db6d4c067a7ff921e00019ac6181e38900a51800006e862d140088b8ceaf5f2130286bbf00002f804671d10effa0e0f63031884bbc9cd130000a85a66c58a00007990000000110e0000e321be8ad0cf70000ad616ee5900000b5c000094488e2da2a234bb92fe0ab836845840f16c6a373c09994940000000353800083f14c0c8c24b82489cbeeb891a2e83b4287bd800000008c4640000000007941b2206caa2afd
  | 56 => 0x3836d26e20000000ae63cc80e3b608000000043c32800000000621a8ac8f322f66779fb882a8000b62ba6c7d080000001b12d9a8340afc00006ea800000020d42958000c5380001482a9800026160001daa00022b800003942b2a3ee9831de089e108854d3320cc3000007688ee7018fc20b38000a452068f59ad480381872ad219aa2670000c0c3906df99a1a81c0e284dbb4d0b5b03f2e8528e80e6abec8210b602922e70dbd99e239b367a327b532742026200e31cad6b8af64e9b728ac32da632880ecc05a7dc1d4b064df29e722f8ad96c540e7a45d9b34a4d814020f3874ecc0acee43971c8479db26f00316b2cb202e2a08de87d206200032280000000e480000d1d342ec3087ae555068c5d494401861d2c347ab3abdc33120bbaa58cef800060a80006aa80000000000af7b90a0000000000333000003ece592c3a646202e7f20000b91268cd5f2140bdf8e16a62940e0000f3a00018daf0d358c0000daa3698000c0eb43a98e10ace3888247df1b14000099601221a487092e43ff18cc8173c6e7d98e04194006cd8f9464189863c0df0eba2ed00f80002bc23b3bdba00000002c433b2000084000010607b526027842448e972c061418000ecb9d2a9e02b1a6a1ba7a65994da0001ab8b68118449f2d9e253bbec178b0be0b61c5682231426bc80009ae92be1452664a58a298a04347cdb51932907006e5dd116ee690ed6c5607d634c2a78df08a400a0a816c77a0f0d6fa0c0812089c87137508cd12700000b4a387943e87608340000000030213e91d2f2e0000fbc258000050802fe7e6b506c673cd08fc0dca7dc80001ae26c00002ac298f000000003b85f421905111cac00000003c51afc0000000000234054882e055a9524000000000006a820695ae261000070706daacc000000000000001470000342c1a89976bbe0348d8003d83cf945e00008945473062360213c0001dbaab180000000b9c4dab924de82a5019f185809bbd548b494a60003086d0cb58813f000005e35226d29644da7910837ea27026f2c789c38a5ad71851a85835ea23aa3dad090d04ae2baacbf9a3aa3860cd8b3d229a00014320e61802f020c12382966a5173b68c512cb6610a67689f000092d0000af9a98837b9af47c71710912b16a599b0fe23b08d00e7a83ad9fbd10cce29966fb1b94c13ad22af5823455c259a7b4921ac74a2d40002b4258d19348ee9e689713996488b52634f9728a3eaaee1a08f243fa90e0c6d19f4ae4805a26d2a12093296af230a6200008a2daa803600024e40001c0c49900005cc10fc3e49b64b67000000006460000b0a1c180007b30000bd4bda421e11589f689ec15a8a84b278ee4c4fadf4000332800000002802c205c280005678000172115650a02f40849d0e84092906e5bbb8000000021933f2cf9800000028fe9a
  | 57 => 0x89829a3a79dacb1b3bd246f3b0e00006062791f3c7bc91a6ac5895c0820000c262390371b928bee862089db65ec39910000034a20001a6c000000000016f8f64000037cb95e9cf00007509a7e3149a42f00ba9e291b7020002c1a51084a64fb39b475014a410a9b742b99b80ded07541858638e43093ad7900002e800006259302b5c82eaf0780000002b88c062614a5430260000000f6f2358000000000001aee7936bc9d73bbcc84000015580004af0386cffb7103402d5434630846208f0c07e0be0766a7f00003bd4cf580009f415b63ca88387721d18ca8acdc0000dc4d7f8a360738000a719b820000000000253a00007b66b800003e900002b600009a0b70e4b6203ed5fb5f61f133a4b88943c0000000dfab37a74d0436d198000878072a00000005838000c3814620ce80544d5bd0a1478b66990222c5749434c762d0c0000598eb5307a85f80000000000e363a001a23d6a6b08000bac868a7389c34aed2a4a0000000322bc3c00000002f2800089928ec00000000003868cc10000e7da01600020a000034dc1ea12c20002aa600007c27c52774b7e8fba2222a36b210774ce21d825d89a82541ba0612daf64ec434c2751800046680006ab000028a06b400000006fe03620000ea002e8000265000000000e68df994e0b5045044e131c359266a0000af8dd89f986a605528fda55820ba80650c165c87d9ada57826c2f31800098d3ca854f9394ee500001be000000aa7f2000389a5aba34662f240695f1366c5ba0960000000b55b4260001ffa000214e070bdd2a909914c04961a4f5a46e6e10000e488b08000320ea228000c6600000003140c1a1a88ddb09b69499ac0a16000000030ec6a58d1a13d03ac3fb8392585307e0003a2c0e0000000015284c423003d10446ed01216000000000037e2000230600018ba00000004d70000000000000013e800000008040000b9e0000de311c08313a0851b000000000007a700007d38d8e0000f5e0001bccac725e4000000a0000000d3a83b40000000815000019ca3604240092f4a8e8c00023de000000000000000e9a31ab6900000000e62a2a80000ba338ae3a00000c80a6896896526cb2e0601481265a59dc060c00008dd2814611861ac8700007b127c4f4814243c496040002d5200016da0ea3498b6380002c980001008000f5d1180000026c00015ec00003aa8a2a45e46a00000df8000bddbc56316a418000174a067b0d2cc192ccbd1297cc2832ea6773c00c4e331e51538ba08590a268daac873e09ba0002a760002d92a33995a7810000441b706000000010580005caa4380003a989731e3a1a7b43400004f60001cae6420cc661e80003f709829a62848000259600004004390000ecd8b1800000006d30944b7200000000000c1d0744972000085596be00011cc7ac9ffc00030
  | 58 => 0xec232310f497b3258a3e310c362b4a495caa9ee4e093843fb75a972bb2086b04824fd00009cc97e22fa80000f21cee25c8000176800055a016489d14b8202907c0003d80bae19b8c360000000392a000251e7748694534000000000006d6ab4c00012eeae1338600039e2c3780000bc000092100009841c824d900000000ffa0401c50a0912922fe04e000015a8ebc03eeb4b89fc0002c569f480009b60000000000000039a8c91bb600000000d6a0000000000000025348b928e600007ea0000636000250284a0fd0542361a4a50e2082689783b80c008b00b6cc9bb72c81926c87888484eb919505b891c66e4a4aad65bd56be923ca8550db04df20260000000000059696c00008cfa0bc7bb85d474280000000000000346255e800064a19d6b10b96657fa5aecda9984f57ab4a0002db400000009dd9c049f9800000029166f105b66c79ec8572b4b26af335c5e80076006800065b0c14c0718be0003a7e2c71d62ec622fe0003ce8de2a6428998000000000060f223819c000056c8f5c0000000ee1800000000004be2ab800039ae20c16bc82a3162d8d80000003bcc0002eb68fe1338156911e5870ac604828a6811a95e42dad34c87976a5db0000edc0fcc00000000002556132ae7e903892e5503c8e15fad604539f380001ece0001416eea8000e65000000037dcc690000000032c3ba120c00000000f51aa81d90000000006ac4e8000d7e0000aea00001e90d1400030a87640000733acf8eb62ef43e8396aa6b1c4ab8e9f50eea2e6a446b4a812f18d8bf0256e6dfbb5480ab8c200029de2721744a8422ea4160da88d08ab226c87faa3711140000e2eb9bb5169480000f1d29d0582800084100002152f46a81b21a81f000043180000003180dddbdc8e7e83ccc37320054c20b2e0b00007b1b4e0bccacea00035b428e38f21391edc8941448bcd849256382cc3fc22829320578a88128c910271488f1690698a9da4eb3c46a56834456d114aa1e2d1a4c488e6905128889b82b439aadb813b1d285f93cfc2188a3000000000002dde0000000000000045c8000d9080000000000d0f31c6c798000abe9cdec5997eea1d80000d5bb162cf10e2b5a0b4c3c80d9e00008ba0001c528772a047e300008ef92fc00010444118000ea180000002da80002424e1d8000000000000025a400000000000fe605a8000b86800053f95dc00007ee21da3aca6b85ca0000000f66a1762bf2c9c49e36b6d479388aaa15727d53558e1c02100003726c4a1452ac88d920002f661eaa39e34883ca00028fc0001bd60002a2800017922b23b7a3dc9fb2000212aba2017c46e993824780000000464000134e55f8000d43218e0000000e40a22445a34700000a20681273acd39e160003b5eecc8b52000000007e8000000000059a3082cc20bd67231dfe9fa00004
  | 59 => 0x3c70236b0e286700004da1a8081c8000f0a0f008bcb11e00000000352caa0003c20c41308e000265ce32037a64480004a78d0e0fd17c878d18983af296cb3f17d428798ee602b72e00014607aaa66201ea
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x84f3755802104339baac010821179cf65100108bae7b28800845e73194400422eb98ca200211b9c865100108dae4328800861e5458c400430eaa2c620021a658d401001087ce9b28600843d74d94300421f3a0ca180210f5d0650c0108dce4328600846d72194300430eb24a61802187591530c010d32c8980600857175d87200423cbb4a3900215c5d421c8010ec2a410e400843e74d96200421eba6cb10021179cf65880108bae7b2c400866552986200423bb8eca900210f9d0650801087ae8328400845e73194200422eb98ca100215a5d66208010ad2eb290400847b7654820042b5bb2a4100219add95208010e56e8a9040087287454820043a5b9aa410021d21cd5208010ec0e2a90400847b755842004279baac2100219cdd56108010ce2cb908400876152c8420042b8ba842100219c59421080108eaea31620086e262c83100423abb4a3080211e5d462840108f2ed28c20086e262c86100423abacc488021749cc4044010ba2e620220085b2740c110042d8ba06088021b818b20440109e4ed10220084f07648110042d9ba240880216c1d12044010ba6e690220085d073481100423cbacc4880211e9da5144010ba4e620a20085d17310510042d93a062880216c5d03144010dc0c590a20084f27688510042783b242880216cdd12144010b60e890a20085d37348510042e839a42880219c5d765440109e4e5b2a200857276d9510043393b6ca880215c5d66444010ae6eab2220085d37359110042e839ac88802178dc96444010bc0e4b2220086b16419110042e9398c888021745cc64440109e4edaa220084f27615110042e9398a888021745cc5444010bc4e42a220085e17215110042b8bacc6880215cdd56344010b66e8b1a20085b07458d10042f1b92c688021781c96344010b64e831a20085b17418d1004368b18c6880213c9db53440109e4ec29a20085b27414d10042d8ba0a688021789c85344010bc2e429a20084f37650d10042783b286880213c9d843440109e2ec21a20087914310d10042b8bacc4880213c5d66244010ce2eb31220084f27298910042b9baac4880216cdd16244010b60e8b1220085d37358910042e839ac488021b89c862440109e4eda9220084f0769491004370314a4880213cdd952440109e0eca9220085b37454910042d83a2a48802174dcd5244010ba0e6a9220086e06254910042793b0a4880216c9d05244010b62e829220085d27314910042e8b98a488021d854852440109e4eda1220084f176d0910042e939e8488021745cf4244010dc0c5a1220084f37650910042783b284880215c9d44244010ae2ea21220086e06210910042793b664880213c5db3244010b64e999220085b174cc9100437031664880213cdd932440109e0ec9922008572750c910042b8ba86488021b81883244010
  | 1 => 0x5304332b14c2298219a58a6014c108dce432e860846d721974304237390cb218211b5c86590c108dee4b2a860846c725954304237390caa18211b5c86550c10a38e6aa2860851c7454d430423aba8c2a18218d5506150c10caaa630a86084f170185430423cba8c0a18218e5506050c10cb2a630286084f1711814304237390ca218211b5c86510c10c3ecaa18860861d6550c430423abacc2218213c5c26110c10d2a86b088608479759804304278b8cc021821a650d6010c108bce7324a40845d73992520421f3a4c7290210f5d26394810c5ae4322a40861f64d8d520430e326c6a902187d906354810c38c831aa40864d7218d520421fba2c2a90210f1d161548108bee6b0aa40845c73585520431bb20c2a90218d1906154810caec630aa40865463185520421fba2c0a90210f1d160548108bee6b02a40845c73581520431db20c0a90218e1906054810cb6c6302a408658631815204338308c0a90211bdd95214810c5ac8a90a40864d63548520430f324c629021875926314810c3cc8b18a40861d6458c5204316b24c4290219358e6214810c6ac9308a40865563984520431cb24c0290219658e60148108bce7b2e840845d73d97420422f398cba1021175cc65d0810c3ca8b1e840861d5458f420423abacc3a10213c5c261d08108f2eb30684084f171983420422f398cb21021175cc6590810a3ae62a4840852d7215242042963a2a5210210fdd165508108bee6b2a840845c73595420422f398caa1021175cc655081087ced2a28408475751854204332a90c2a10213c5c061508108f2ea3028408669521814204278b88c0a1021179cc65108108bae6328840847671194420423d380ca210210f5db541081087aec2a0840851d731504204296b90a8210210f9d365cc81087ae9b2e640843e74197320421eba0cb990218759253cc810c3ac8a9e6408475759873204278b84c3990211e5d660cc8109e2e3306640843e74196320421eba0cb19021475d0538c810a9ae429c640854c7354a320421fba2ca990210f1d1654c8108bee6b2a640843e74195320421eba0ca99021179da534c8108eaea30a6408665521853204278b80c2990211e5d4604c810cd2a430264084f171181320421f3a0ca190210f5d0650c8108ece2328640847a70194320422ebb6a619021175d8530c810a3ae8298640854d7214c320422f39eca20821175cf6510410c3ca8b18820861d5458c410434ab1a82208210f9d3650c41087ae9b28620861d6494c310430eb22a618821a5591310c410ae2ebb06420843e74d96210421eba6cb10821179cf65884108bae7b2c42086695298221042b2bacc410821595d652084108eeeca904208567765482104333bb2a410821c9dd15208410e48e8a9042087477354821043a239aa410821d81c152084108eeeab0042
  | 2 => 0xc029a211b9cb65d0d108dae5b2e868851c735534344296392a9a1a21475d053d0d108dce5b2c868846d72d96434428eb98a921a21471d15390d10a98e4a9c868846f725954344236392caa1a211ddc56550d108f6e0b2a868843e76951434421e3b2a8a1a21471cd5450d10a58e4aa2868845e7694d434422e3b2a6a1a21471d15350d10a98e4a9a868847571d94434423cb86ca21a211bdc96510d108d8e4b28868843e74194434422f398ca21a210f5db5410d10a3ae62a0868845d76d4c434428eba0a621a21479d54310d10a38eaa18868861f6550c434430eb2a8621a21179ce64949108bae7324a48843e7498e524421eba4c72922187d936354910c38c9b1aa48861f6418d524430e320c6a92218b1936254910c98c7b12a48863764d85524431a326c2a922195d8f6154910ca8c7b0aa48863b64d81524431c326c0a922196d8f6054910cb0c7b02a48846f7654852442963a2a429221531cd52149108bce7b2e848845d73d97424423ab8ecba12211e5c365d09108bce632e848845d73197424432731ea5a12219398c52d09108bce7b2c848845d73d96424428eb98a92122117dcd65509108b8e6b2a848847771595424423db82caa122117dcd65109108b8e6b28848845e73194424422eb98ca21221475cc54109108e8eab088488634545844244278382c2212211e1d56010910c70a8b0084884f071580424421f3a6cb992210f5d365cc9108eae3b2e648847970d97324421f3a0cb992210f5d065cc910c5cc9a96648862e6414b324421f3a6cb192210f5d3658c910a3ae829c648843f74595324421e3a2ca992211ddc5654c9108f6e0b2a648843f74594324421e3a2ca192210f9d0650c91087ae8328648851d7414c324423a3aac2192219514d610c9109e0e0b08648847875580324432c29ac0192213c1c5600c910a3ae62a6828863854583414428eb98a8a0a21475d053cc510cb0a6b06628851d7414d3144316326a490a219318f5248510c58c8292428864c631492144334296c090a21475cc54d0110c68a8b0e808845f73595404422e39acaa02211bdc965501108d8e4b2a808851d73151404428eba0a7982219514d61cc11087ee8b2a608843c745953044237b92ca982211b1c9654c110a3ae829a608843f74595204421e3a2ca9022117dcd65481108b8e6b2a408862c64d49204432631ea4902218b1905248110c98c6292408866452d85204422fb9ac5aa021171cd62d501087eecaa0a80861d5458c5404316aa2c42a021879916315010c9cc7310a80864d639885404317322c42a0219398d6215010c9ac6b10a808665629845404334b14c02a0210fdd162d4c10878e8b16a60845f7654c530430eb22a6298219354d6214c10c3ac9318a60862e649885304316b24c4298218b9916214c10c5ac8b10a60864e63588
  | 3 => 0x926114f10ce4c2b00a78846e7299543c4236b94caa1e21471cd5450f10a38e8a9a878861f6550c43c430eb2a8621e21a650d6010f10c3cc931ea58861d6498f52c430f322c7a96218759163d4b10c6cc930ea5886356498752c432b31cc3a96219558e61d4b10ce4c2b06a58845e7399252c422eb9cc9296210f9d26394b1087ae931ca58846f7654852c433930ac029621179cf65d0b108bae7b2e858845e7319742c422eb98cba1621179ce6590b108bae732c858845e7399542c422eb9ccaa1621179cc6510b108bae6328858843e74d9732c421eba6cb996210f9d065ccb1087ae832e658843e7499632c421eba4cb196210f9d2654cb1087ae932a658843e7419432c421eba0ca19621879516310710c3aa8b18838861d6494c31c430eb22a618e219a9496008710c6aa830a81886996350040c432aa98c298621a6591300c310ccca430a418847976d4820c4338b0cc1aa421179cf62552108bae7b12a90843f76550548430eaa2c62a421879916315210cb2c7300a908671619805484338b0cc1a9c210f9d36254e1087ae9b12a70845f7654c538430eb22a629c21875926314e10c72c9300a708671619805384237394caa1c211b5ca6550e10a38e6aa2870851c7454d438430fb2a8621c21875954310e10d2a86b08870861e6498f528430eb24c7a94218799163d4a10c3ac8b1ea50863a64983528431cb24c1a94219698e60d4a10cb2c7306a50867161983528422f39cc929421175ce6494a1087ce931ca50843d7498e5284237bb2a4294219c5866014a108bce7b2e850845d73d97428422f398cba1421175cc65d0a108bce732c850845d73996428422f39ccaa1421175ce6550a108bce6328850845d73194428421f3a6cb994210f5d365cca1087ce832e650843d74197328421f3a4cb194210f5d2658ca1087ce932a650843d74995328421f3a0ca194210f5d0650ca10c72a8302830869563504418432ca98c098c21a5591310c610cd4a4302430847576d48218430f2a2c620421875516310210c3ac9298610861d6454c3084333292c21042117dcd62d51108b8e6b16a88861f6418d5444327b1ec4aa2219318f6255110c5ec8312a88864f631895444326318c4aa2219518f6155110cc8c5b0aa88865863d815444334316c0aa2210fdd95415110a38e6aa0a88852c72550544430eaa2c62a2218799163151108bce6308a88845d73184544422f398c02a221175cc601511087ee8b16a68843c7458b534430eb98c8a9a21871936354d10c5ec9b12a68862c64d895344317b20c4a9a218b1906254d10c9ec6312a68863464d855344332316c2a9a218e1936054d10cd0c5b02a68845f7654c534428e3a2a629a21875915314d10a98e4a98a68861c73590534430eb24c629a210f9d06114d1087ae8308a68843e74180534421eba0
  | 4 => 0x3cc9a98609061d64d4c304830f320a61824187590530c120c6cc9a88609063564d44304831b320a2182418d590510c120ab0ea9806090699644c0304838c2a26018241721c9300c120ea0a298060907185414f2048399aa0a390241cc15051c8120ea6a628e40907505314720483862a0a710241c91505188120e88a628c409045e73d89540822eb9ec4aa041179cc61550208bae630aa81043f76550540830eaa2c62a0418d5516115020c3cc8b18a81065663984540832ab1cc22a0418d9916115020cacc6b08a810655635845408333312c22a0419658e6015020ce2c3300a81043e74d89530821eba6c4a98410f9d06154c2087ae830aa61045f7654c530830eb22a6298419554d6114c20c3ac9318a61063664984530831ab24c2298418d9916114c20c6ac8b08a610656635845308333312c2298418e5926014c20ce2c3300a61047671197430823ab88cba18411d9c46590c208eae232c861047771595430823a38acaa18411d9c46550c208eae232a861051c73551430828e3a2a6a18411b5d46250c20c5aa8312861064d53189430823cba8c0a18418e5506050c20cb2a6302861047671194430823ab88ca218411e9c06510c20c3ecaa18861061d6550c430822f39cc929041175ce649482087ce931ca41043d7498e520831caa4c1210419654e608c8208bce6322a21045d73191510821f3a0c6a88410f5d063544208eeeca88a21063564544510832ab1aa2288413a5ca60d04208bee6b2a821045c73595410822f398caa0841175cc6550420cc8c4a8a8210639541814108338a88c0a0841179cf65104208bae7b2882104e972983310821fba2ca988410f1d1654c42087ce832a621043d741953108332312a2988419654c604c420ce2a2302621043e74d94310821eba6ca18841179cf65100208bae7b28801045e73194400822eb98ca20041879516310020c3aa8b18801043e74d94300821eba6ca180410f9d0650c02087ae8328601061d6494c300830eb22a6180411b5da52880208f2ed294401062f65d912008317b28c89004193d976348020c9eca31a401068c6418d2008333b2ec29004199d946148020d48c830a40106c46318520082e539880900416a9d03048020c76cbb22401063b65191200832db2ec69004196d946348020d30c831a40105ca73d0920082d53a664900419cd976148020ce6ca30a40106b3641852008358320c290041b4d8c6148020da0c630a40106e2521852008371a10c290041b81086148020dc66430a40106e032185200837030e42900416a1d12148020b90e690a40106726158354c422f39ec4aa621175cf625531087eecaa0a98861d5458c54c430f322c62a6219558e6115310ce4c2b00a9886726158353c421f3a6c4a9e210f5d36254f108beeca98a78861d6454c53c430eb24c629e218d5
  | 5 => 0x5347454c514832b328a628a41c5d505314520e28a8298a2905567319051482aab98c828a41595c86414520ae2e0320a2905367418c514829aba0c628a41595c86314520ae2e0318a2907154310c51482b93808628a415c5c04314520aace7a10a29055573d0851482b93868428a415c5c34214520ae6e0a10a29057070508514829b3a66428a414d5d33214520ae4e1990a29057170cc851482b9b826428a415c1c13214520a6ee8900a2905347448051482abb9a4028a41551cd20145208bee6b2e829045c73597414822fb9acb20a41171cd65905208bce7b2a829045d73d95414822fb9aca20a41171cd65105208bce6328829045d73194414822f3acc620a4187d526310520c38a9318829045c7558c414830faa2c620a418715163105208beeda98829045d76d4c414822fbb0a620a41175d85310520c58a9310829065663d44414832ab1ea220a419598c5110520caac6288829066662144414831c2a4c020a419c1466010520ce0a2b00829043f74597314821e3a2cb98a410fdd1658c520878e8b2c629043e74d95314821eba6ca98a410fdd1650c520878e8b28629043e74194314821eba0ca18a410f9d6640c520878eab20629043f76d50314821ebb6a818a410fdd8540c52087aec2a0629061e64d4c314830eb26a618a4187990530c520c3ac8298629064c53988314831b326a218a418d593510c520c6cc82886290635641443148333310a218a419614e600c520ce0a3300629067051580314833828cc110a410f9d7644852087cea322429043e76d51214821f3b0a890a41179d76348520c3ea9b1a429061c54d8d214822f3a8c690a4187d506348520c38a831a429045e76d4d214830fb26a690a418719353485208bcec29a429061f6414d214830e320a690a418dd935148520c68c9a8a429065763d45214832a31ea290a418dd905148520c68c828a429065763145214832a318a290a418ed536048520c70a9b02429065b53d81214832c29ec090a419c1476048520c76a8302429063854181214832da98c090a419614c6048520ce6a230242907245448421483a229a4210a418b15262d01208bce7b2a809045d73d95404822fb9acaa0241171cd6550120c98a7b12809062f541894048326298c4a024199d885150120cc8c428a809061f5498c404830e2a4c62024187d516310120c38a8b18809045f76d4c404822ebb6a62024117dd853101208baec298809065663d44404832ab1ea2202419598c5110120caac6288809053875500404834cb1a8020241c614d4010120b50e4a00809073051500404832629cc5982410f9d3654c12087ae9b2a609043f74595304821e3a2ca982418b153624c120c58a8312609064f531893048333b10a29824199188514c12087eedaa0609043d76d50304821fbb0a8182410f5d8540c120c
  | 6 => 0x34832bb1ec2a9a418dd906154d20c68c830aa690657631855348333b10c2a9a418e1936054d20ce0c3b02a69045f7654c534828fba2a629a41471d15314d20aaee2a98a6905547154c534828f3a4c629a41475d26314d20aace3318a6905557198c534830f32ea829a41175da5414d20aace32a0a69055571950534822fbb2a829a4155dc55414d20aa8e2aa0a69061e65150534830eb20c829a41565c06414d20a3ce9b10a69051d74d88534828f3a0c229a41475d06114d20a9ae4308a69055970184534828fba24029a41471d12014d208ece3b2e869047571d97434823bb8acba1a411d1c565d0d208ece3b2c869047571d96434823bb8acb21a411d1c56590d208ece3b2a869047571d954348237b92caa1a411ddc56550d208e8e2b2a869047b70595434828f39ea8a1a41479d35350d208ece3b28869047571d94434823bb8aca21a411d1c56510d20a3ae62a0869051d7414c434828f3aa8621a41471d54310d20c3ccaa18869061c6550c434831c2a4c021a419614e6010d208f0eab008690699435804348274392c021a41179d663d0920c3ea931e849061c5498f424822e3aac7a124187d5163d0920c38a8b1e849045f76d4f424822ebb6a7a124117dd853d09208baec29e849063854983424832c29ec0a12418ed506050920cb0a6302849043e75993324821e3aac9992410fddb54cc92087aedaa6649043f76153324821ebb0a9992418799353cc920c3ac9a9e649061e6414f324830eb20a7992419614e60cc920c70a9b02649063854181324832da98c099241179ce64d45208bae7326a29043e7498f514821eba4c7a8a41559ce54d4520aaae72a6a2905577355351482aa39aa9a8a41c5d5353d4520e28a9a9ea2905367494f514829aba4a7a8a414ddd153d4520a68e8a9ea2907175414f514838a2a0a7a8a41559ce64d4520aaae7326a2905367498f514829aba4c7a8a41c550c43d4520a6ce9b16a29053574d8b51482ab39ec5a8a41555cf62d4520aace7a16a29055573d0b514829b3a665a8a414d5d332d4520c3ea931ca29061c5498e514830faa2c728a41871516394520c3cc9a9ca29061d64d4e514830f320a728a41875905394520c6cc9a8ca29063564d46514832b31ea328a419558f519452087cedaa2a29043e76151514830faa6c6a8a41871536354520c3ea831aa29061c5418d514822f3b6a6a8a4187d935354520c38c9a9aa29045e7614d514830fb20a6a8a418719053545208eeeca88a29053774544514829a3a2a228a4155dcd5114520aa8e6a88a29063665d50514823abb4a828a41559ce5414520aaae72a0a2904777655051482abb9aa828a41551cd5414520c6cca2a0a29065665d4c514838baa6a628a41c515353145208eaed298a2905367494c514829aba4a628a411ddd95314520a6ee8a98a29
  | 7 => 0xa1e411d9c46510f208eae2328879061e6550c43c830e32a8621e41475ce5490b20a3ae72a0859063a5458042c828eba4a719641475d2530cb20cb4a6b0065904777654451c822f39ecba0e41175cf65d07208bce7b28839045d73d9441c821f3a6cb98e410f5d365cc72087ce9b28639043d74d9431c82f03824210e41475ce54d032087ced2a2819051d7395140c821ebb6a82064187d516310320c38a8b18819051d7494f30c822f3b4a698641475d2534c3208baeda98619061d64d4c30c830eb20a6186419a58a60d522087eecaa0a91061d5458c548830f322c62a4419a58a60d4e208beeca98a71061d6454c538830eb24c629c411d9c66550e208eae332a871051c73551438828e3a2a6a1c411d9c76510e208eae3b28871061f6550c438830eb2a8621c41a650d6010e20c3ca8b1e851061d5458f428828eb98a9214410f9da5450a2087aedaa0851051d73150428830eb24a7994418759153cca20a3ae829c651045e7694d328822ebb6a619441475d0530ca208bce6322a31045d73191518821f3a0c6a8c410f5d063546208eeeca88a31045e73996418822eb9ccb20c41179cf65106208bae7b28831053571950418830f2a2c620c4187551631062087ce932c631043d74996318821f3a6ca18c410f5d3650c620c3ac929863105557194c318830eb22a618c419c9446048620c3ca8b18811061d5458c408834cb1a802044187592530c220c3ac8a986110699644c0308822f39cc3aa241175ce61d5120c3ec731ea89051f7358b544828e39ac5aa241479ce61d5120a3ae730ea89061f5498e544830faa2c72a2418dd526195120c6ea8b0ca89065663986544832ab1cc32a2419598d6195120caac6b0ca89067261582544830fb26c6aa24187d906355120c98c7b12a89063764d85544832bb1ec2aa2419518f6155120c6ec830aa89065763185544832a318c2aa24199d886155120cb0c7b02a89067061d81544821fbb2a82a24147dcd5415120a38e6aa0a89053771550544829a38aa82a241479ce6415120a3ae7320a89053671990544829ab8cc82a2418758c6315120a72e0318a89051e73d88544828eb9ec42a241479cc6115120a3ae6308a89052d72184544829cb80c22a2410f9d261d4d2087ae930ea6905567195353482aab8ca9a9a4155dc554d4d20aa8e2aa6a69061f64993534828fba2c5a9a41471d162d4d20a3ce930ea69051d74987534830f326a729a41875935394d20c6ea930ca69063454986534832ba9cc329a418dd516194d20c68a8b0ca69065753586534831b324c329a418d5926194d20c6cc8b0ca69063564586534833930ac129a410f9db5454d2087cec2a2a69063754d85534831a2a6c2a9a418dd506154d20c68a830aa69061f64d8d534830e326c6a9a418b1936254d20c6ec9b0aa69063464d855
  | 8 => 0x54350130b30e0a1a80985367118e540c29ab88c72a061479cf6295030a3ce630ca81863561186540c28f39ec4aa061471cd6255030a6ee2b12a81853471589540c29c382c4aa061471cd6155030a5ee4b0aa81852c72585540c29c382c2aa061479cc6155030c6ac230aa81843f76550540c31caa2c121861475cd5410c30c3ecaa18861861d6550c430c31d2a2c0218610fdd16194830878e8b0ca41843d76950520c21fbb2a8290611bdd95214830c6ca9308a41863554984520c31b2a2c2290618d5516114830ccaa4b08a41861d5498f420c26cb84c7a10618795163d0830c3aa8b1e841847771595420c23a38acaa1061875536350830c3aa831a841863954d81420c21ebacc9990610fdd564cc83087aed2a6641843f76553320c30eb2aa91906187551608c830c72a9300641863954580320c2a6b96a819061475d6540c830c3aa9310641870d54988320c386aa4a419061c3951520c830e32a9300641861d54580320c38caa2c01906136dd5600c830cb6eab00641865b54580320c34d2a2c01906196551600c830d32a8b00641861954580320c21fba2c5288610f1d1629443087aed2a0a21843f76550510c3172a4c4288618b5526214430c5ca8b10a21862d54588510c23bbb2a2288619958951144308dee4b2a821846c72595410c29a38aa8a0861875536350430c3aa831a821863954d81410c31caa0c0a08614d5c65410430c3aa931882184d97098c410c30f2a2c620861875516310430c72a9306621863954583310c21ebacc8188610fdd5640c43087aed2a0621843f76550310c38b2a262188610f9d265c843087ae932e421843e74996210c21eba4cb108618755263884309b2e131c421861d5458e210c21fba2ca908610f1d1654843087ce832a421843d74195210c21ebaec8908610f5d4644843087ced2a2421843c76951210c21f3b2a8908610f1d95448430c3ca9b1a421861d54d8d210c30f2a0c690861875506348430c98c7292421865463945210c31d2a6c0908618e5536048430c74a8302421863954181210c335290c0908619c9446048430ce2a2302421843e74994210c21eba4ca108618755263900308beeab1c801861d5458e400c30eaa4c620061879516310030c3aa8b18801863965500400c30eaa4c598061175da538c0308f2ed29c601845e76d51300c28ebaca89806187d96544c030c3ecaaa2601871870551300c30eaa0c49806187553604c030e32a9a02601855975101300c31db2ca8980618ed95544c030e32a929a601855975d0d300c26d3b66498061669d3324c030b34e818a601866a6258354c830faa2c72a6410fdd95415320a3ae7320a99066a6258353c830eb26a729e4117dd95314f20a3ae9318a7904767199543c823ab8ccaa1e41479cf5450f20a3ce9a9a879063b5418143c832da98c
  | 9 => 0x8c8a9a422062c64949211031a324a2908819694f6048440cb2a7b02422065a53181211032ca98c0908819a9486048440ce4a2302422067151181211022f39cca10881175ce6508440c3aa7316802043d76952401023cbb4a92008187d965350040c3ecaa9a80207187054d401030ea98c4a008196d965350040cb6caa9a802071a5454d401029cbac86a00812e9db4250040b34e7a12802059a73105401032d31ac1aa6610fdd95415330c6aa8b08a9986366458454cc32b31ac22a6619c9856015330a6ae22a687985557115243cc21f3b0a8a1e614d5c45450f30b32e1aa2879845e7615143cc2aab88a8a1e61279d85450f30b2ae22a2879851e7615143cc30f3b0a8a1e61479c85450f30e2ce22a2879851d7115143cc38ab88a8a1e61455c45450f30e32e02a2879843f7655043cc34ca1ac021e61879914394b308deeca90a5984767199642cc23ab8ccb21661879954390b3087ee8b14a39843c7458a51cc30e32286a8e611ddd95114730c6ac8a88a39861c6550d41cc38aa1aa2a0e61a650f6050730c6ac928863986356454431cc21f3a4cb90e610f5d265c873087ee8b2a439843c7459521cc2b2b94a210e61875506350330b30e0a1a81986996350040cc32cb1cc1aa4610fdd95415230c72a8302871846f76548528c296b90a8214618e1516010a30a3ee8a94651854f72550328c28fba2a4194611ddd9511463087ce9b2c431843d74d96218c21fba2ca90c610f1d1654863087cec2a2811843f76550408c30f2a2c620461875516310230c5ec8312a89864f63189544c333b16c2aa2619918b6155130c6ec830aa89865763185544c333b10c2aa261991886155130cd0c5b02a89867061d81544c21fbb2a82a2614b1c95415130a68e2aa0a89863854583434c28f3aec8a1a61479d25450d308bcec2a2869851e76151434c30f3b0a8a1a61479c85450d30a3ae22a286984da75181434c32d3a8c0a1a611bdd95214930a58e8a90a49856471548524c2ac38286292610fdd16114930878e8b08a4984d87058f424c326b18a5a1261471d54390930c3ccaa1c84985987050e424c23bb8aca212611d1c565109308ece2328849847571194424c30e2a2c621261471d54310930c38caa1884985987050c424c386a18a4212618e1516010930d3286b00849866852580424c23bbb2a228a614d1d15114530ac8e4a88a29843f74588514c21e3a2c428a618719543d0530e2a87a8e829869943583414c30e32a86a0a611bdc965105308d8e4b28829861f5458c414c30e2a2c620a61361c16310530caac7a88829865563144414c21f3a4ca90a610f5d2654853087ee8b28429843c74594214c21f3a0ca10a610f5d06508530caac6288429866852580214c33828ac010a618715163d0130a38eaa1e80985987050f404c28e3aa86a02618719
  | 10 => 0x45e73d96219022eb9ecb10c8117dcd65486408b8e6b2a432045f7654c53502a6392a629a81551c55314d40a3cebb1a86a051e7614d435030f3b0a6a1a81479c85350d40a3ae229a86a04ba75181435031d3a8c0a1a811bdd95214940a98e6a90a4a056471548525029c382862928117dcd61149408b8e6b08a4a04b8705933250316b20a59928187995438c940b30e0a1c64a047771594325023a38aca192811d9c4650c9408eae232864a061d6414c325030e32a8619281661c1430c940e1a8629064a065853580325034ca1ac0192819a149600c9408eeeca88a2a05547354451502b2392a228a8117dcd62145408b8e6b10a2a061c6550f315038aa1ea398a81a650d60cc540c38caa1a62a046f725943150236392ca18a812e1c1640c540c3ac9a9862a061d6414c315031ab26a218a818d590510c5408bce732a42a045d73995215022fb9aca10a81171cd65085408bce632842a045d73194215031ab20a210a819a1496008540ce0a2b0042a05567119253102aab88c929881479d36294c40a3ce830ca62065561186531028f3a6c4a9881471d16254c40aaee2b12a6205547158953102ac382c4a9881471d16154c40a9ee4b0aa62054c7258553102ac382c2a9881479d06154c40caac230aa62045f7654c531032ca9ac1a18819694d6010c408bee6b0ca42045c73586521022ebb4a62908117dd953148408deeca90a42065653984521032aa9cc2290819594d6114840caaa6b08a42066552584521022ebacc7a108117dd563d08408baed29e842045f7654f421030eb2aa7210818754d6090840cb2a73008420659535804210386a9cc421081c354e5210840e1ca6a90842071953980421030ea9ac021081c654d6010840976eab00842063b75580421034d29ac0210818e54d6010840d32a6b00842061953580421025cb84c9990818759253cc840c3cc8a9e642061d6454f321023bb8aca990811d1c5654c840c3ec8a9a642061c6454d321032ca9ec09908117dcd62944408b8e6b14a22045d7694c511022fbb2a6288819394e6214440c9aa7310a22064e535885110326a9ac4288811ddd95114440ccac4a88a22065953983411032ca9ac1a0881175d663104408beeab18822045d7694c411022fbb2a620881c594d41104408dee4b2a622046c72595311030fb22a69888187191534c440aa8e2a9a622065953d81311032ca98c0988812e5c2640c440c3ac929862205557194c311030f322a61888187591530c4408bce732e422045d73997211022f39ccb10881175ce6588440972e1324422061e6454e211030eb22a71088117dcd65484408b8e6b2a422045e73195211022eb98ca90881175d763484408baea31a422045e7694d211022e3b4a69088187d925348440c38c929a422045e7654d211022e3b2a69088187d915348440c3
  | 11 => 0x486b8b88c628243c650c4314121ae4e2218a090d717110c50486ad39e8428243565cf4214121ae4e3a10a090d7171d0850486b9b8a84282435c1c54214121a74e9990a090d3974cc850486b938e64282435c5c73214121ae6e2990a090d70714c850486b5b9282282435a1c94114121ab4e6208a090d59731045048798a0882282435adc93114121ad0e4988a090d3a740c4504869cba06228243d44c43114121a76e8908a090d387448450486adb9a4228243561cd21141218bce6302a810c5d73181540861fbb2a82a043875516315021c72a8b00a810e1e6458c540872ab1cc22a0439698e6015021cb2c7300a810e3a64580540872d31ac02a0439658d6015021cd4c4b00a810e7261580540861f3a0c0a98430f5d06054c218beeca98a610e1d6454c530872ca9ac029843875926314c21c6ac9308a610e3a64980530871cb24c0298438e9916014c21c72c8b00a610e5a635805308735312c0298439c9856014c218f4e032e8610c7970197430863d380cb218431e5c06590c218f6e0b2a8610c7870595430863d380caa18431e5c06550c21a38e6aa28610d1c7454d4308636ba8c4a18438b5506250c21c9aa63128610c7575185430871aaa0c2a18439554c6150c218ece23288610c7a70194430863cb80ca2184387d954310c21c3acaa188610c5e73992520862eb9cc9290430f9d2639482187ae931ca410e3554986420872aa9cc319043179cf65104218bae7b288210c5e73194410862eb98ca20843879516310421c3aa8b188210c3e74d94310861eba6ca188430f9d0650c42187ae83286210e1d6494c310870eb22a6188431b5da52884218eaed2944210e2f65d912108717b28c89084393d976348421c9eca31a4210e8c6418d21086e33988290843699d03148421cd6cbb024210e6b651812108754320c090843b218c6048421c6ecbb224210e3765191210872bb2ec69084395d946348421d28c831a4210dc673d0921086d33a664908439cd976048421ce6ca3024210eb3641812108758320c090843b4d8c6048421da0c63024210ee2521812108771a10c090843b81086048421dc6643024210ee032181210862f398c8a8043175cc645402187ce831aa010c3d7418d500863dbb2a0280438e5915014021cb2c6a80a010c5f7654c53d032aa9ac229e81665c35350f4093cec29a87a05957114d43d034ca1ac021e818798d4394b408deeca90a5a04767199632d023ab8ccb1968187995438cb408bee6b14a3a045c7358a51d030e31a86a8e811ddd95114740caac6a88a3a06556394441d032ab1aa220e8187195434c740e2a86a8a63a069943d8131d022f39ccb90e81175ce65c87408bee6b2a43a045c7359521d02b2b94a210e8117dd95314e408deeca90a52051f7354a4290297b92a62148147dcd5210a408eeeca88a320
  | 12 => 0x21a43a550d6110d219c8e4b088690c5e7598f424870faa4c7a12438715263d09218b8eab1e8490e1f5458f424870e2a2c7a124317ddb53d09218baeda9e8490c5f7614f424862ebb0a7a12438d15261d0921ca8a7b0a8490e3754185424872a298c2a12430f9d664cc921878eab266490c3f76d53324861ebb6a9992430fdd854cc92187aec2a66490e1e64d4f324870eb26a7992438799053cc921c3ac829e6490e5453987324871a2a6c2992438d150614c921caea630a6490e2c5498b414862f39ecaa0a43175cf65505218bee6b2a8290c5c73595414872629ec4a0a438bd506250521c98a63128290e1f5498c414870e2a4c620a4387d516310521c38a8b188290c5f76d4c414862ebb6a620a4317dd853105218baec2988290d3475504414874ab1a8220a43c514d4110521b48e4a088290e4c5398b314861f3a6ca98a430f5d3654c52187ee8b2a6290c3c7459531487162a6c498a438b150624c521c9ea63126290c3f76d50314861ebb6a818a430fdd8540c52187aec2a06290e1e64d4c314870eb26a618a4387990530c521c3ac82986290d54754c4314874ab226218a43c5151310c521b88e49886290f145414f21487862a0a710a43179ce64d41218bae7326a090c3e7498f504861eba4c7a8243569ce54d4121ab2e72a6a090d5b7355350486ac39aa9a8243c6d5353d4121e30a9a9ea090d3a7494f504869cba4a7a82434edd153d4121a70e8a9ea090f1b5414f504878c2a0a7a8243569ce64d4121ab2e7326a090d3a7498f504869cba4c7a8243c650c43d4121a74e9b16a090d3974d8b50486ad39ec5a8243565cf62d4121ab4e7a16a090d5973d0b504869d3a665a82434e5d332d4121ab4e620ea090d5973107504869d3a063a82434e5d031d4121c3ea931ca090e1c5498e504870faa2c728243871516394121c3cc9a9ca090e1d64d4e504870f320a728243875905394121c74c9a84a090e3964d42504872d31ea1282439658f509412187cedaa2a090c3e76151504870faa6c6a8243871536354121c3ea831aa090e1c5418d504862f3b6a6a824387d935354121c38c9a9aa090c5e7614d504870fb20a6a82438719053541218f6eca80a090d3b74540504869c3a2a02824356dcd5014121ab0e6a80a090e3a65d50504863cbb4a828243569ce5414121ab2e72a0a090c7b7655050486adb9aa828243561cd5414121c74ca2a0a090e5a65d4c504878daa6a628243c615353141218f2ed298a090d3a7494c504869cba4a6282431edd95314121a76e8a98a090d387454c504872d328a628243c6d505314121e30a8298a090f3354c8450487982a64228243d4d4f2114121ea0a7908a090f285488450487a429c4228243569cc6414121ab2e6320a090d697219050486b8b88c8282434e9d06314121a72e8318a090d697218c50
  | 13 => 0x4310e21d2a86b088710e1e5458f428870eaa2c7a1443475cc5490a2187ced2a28510c3d76d50428868eb98a8214438759253cca21c3ac8a9e6510d1d7414e328862f3b4a699443175db530ca21a3ae82986510e1e5458c418870eaa2c620c43a558d4110621c3ac92986310e1d6454c318874ab226218c43179cc64542218bae6322a110c3e7418d508861eba0c6a84431edd950142218bce7306a890c5d73983544870fb1cc7aa24347dcd62d5121a38e6b16a890d1e73983544868eb9cc1aa24387d526395121c3ea8b1ca890e3b54982544871daa2c12a2439698e6095121cb2c7304a890e7161982544872d31ac12a2439658d6095121c3ec9b1aa890e1f6418d544872631ec4aa2439518f6155121c76c9b02a890e5b63d81544872c31ec0aa2438ed906055121cb6c6302a890e58631815448735b10c0aa2439cd84605512187eecaa0a890d1f73550544868e39aa82a2434edc15415121a70e0aa0a890d1e73990544868eb9cc82a2434e9c26415121a72e1320a890e1d6318c544869ab88c62a243479cf6215121a3ae7b10a890d1e73180544868eb98c02a2434b5c86015121a6ae2300a890c3e74983534861eba4c1a9a43569c254d4d21ab2e12a6a690d5b7055353486ac382a9a9a4387d9264d4d21a3ee8b16a690d1c7458b534868f3a4c1a9a43475d260d4d21c3cc9a9ca690e1d64d4e534871daa4c129a438e1526094d21cb6a7304a690e3b54582534871c2a2c129a4396d4d6094d21c74c9304a690e39649825348738b0cc129a438e9916094d21c72c8b04a690c3e76d51534861f3b0a8a9a438ed536054d21c70a9b02a690e3b54181534871c2a0c0a9a4387d936354d21c38c9b1aa690e2c64d89534871a326c2a9a438ed936054d21c70c9b02a690e5b63d81534871db20c0a9a438e1906054d21cb6c6302a690e6b621815348739b08c0a9a4317dd95314d21a3ee8a98a690d1c7454c53486adb82a629a43561c15314d21a3ce9318a690d1d7498c53486ad384c629a43565c26314d21c3ccbaa0a690c5d7695053486ad384a829a43565c25414d218beecaa0a690d5b7055053486ac382a829a43879945414d21c3ac8320a690d5571190534868f3a6c429a43475d36214d21a3ee8908a690d1c74484534868f3a0c029a43475d06014d21a9ae4300a690d5571180534863d386cba1a431e5c365d0d218f6e0b2e8690c7870597434863d386cb21a431e5c36590d218f6e0b2c8690c7870596434863d386caa1a431e5c36550d218dee4b2a8690c7771595434863db82caa1a431e1c16550d21a3ce7aa28690d1e74d4d434863d386ca21a431e5c36510d218f6e0b288690c7870594434868eb98a821a43475d05310d21a3ceaa188690d1c7550c434870f32a8621a43871954310d21c68a93088690e5453984434863a3aac2
  | 14 => 0xe2a188498f0d43148424c71a2a2c221263a550d6110931cc8a4b088498e1c5458f414c68e3aa87a0a63651c543d0531a38eaa1a8298e1c6550d414c6ca38a86a0a631edd95014131a70e8a80a098d6872540504c61fba2c4282630f1d16214131a74e031ca818d397018e540c68f39ec52a063479cc6095031c72c0304a818d1e73d89540c68e39ac4aa0634d1c56255031a76e0b12a818d3870589540c68e39ac0aa0634bdc96055031a58e4b02a818d3471581540c68f398c0aa0638e580605503187eecaa0a818e3554586430c70fb2a8621863875954310c31c6ca8b088618c3f74582520c61e3a2c1290630f5da541483187eecaa0a418c6f76548520c71d2a4c0290638e5526014831c74a8b00a418e3954580520c734a92c0290638755263d08319aae331e8418e1e5458f420c70eaa2c7a10631edc165508318f0e0b2a8418e1d54d8d420c70eaa0c6a10638d553615083187aeb3266418c3f75593320c61ebb4a9990630fdd954cc831c3acaaa46418e1d54586320c71aaa4c2190638d551610c831a9ae5aa06418d1d75950320c70eaa4c419063c3552620c831e1aa92906418f0e54548320c78aaa4c21906387551610c831e2aa8b086418cd775584320c72bbaac21906395d51610c831d2ca8b086418e5554584320c74aaa2c21906385551610c831c3aa931c8218c5f7558e410c70eaa2c720863875526310431c3ca8b188218e1d5458c410c71ab2a82208638755262cc4318baed29c6218c757694e310c62f3b6a898863475d6544c431c3ecb2a26218e1f65551310c78a38aa89886387550624c431c3aa9b0a6218f1554d05310c6aaba882988638dd96544c431c6ecaaa26218f155494d310c6aabae8698863359db324c431b2ce99926218c3f7458a500c61e3a2c5280630f5da541403187eecaa0a018e2e54988500c716aa4c4280638b9516214031c5aa8b10a018c7b76540500c734b12a0280639998961d5321c3ea8b1ca990c3f7655054c868eb9cc82a6439998961d4f21c3ac9a9ca790c5f7654c53c868eba4c629e431e9c26550f218f2e132a8790d1e73d5143c868f3a6a6a1e438dd506150f21caea630a8790c7a7019443c863cb80ca21e43879954310f21c38caa188790d1d7395242c868eb9ca8216438d9516110b21a3ae929c6590d1d7494c32c872b29ac219643475ce54d072187ced2a28390d1d7395141c861ebb6a820e4387d516310721c38a8b188390d1d7494f31c862f3b4a698e43475d2534c7218baeda986390e1d64d4c31c870eb20a618e431edd95014321ccac530ea910c3f76550548870eaa2c62a443879916315221ccac530ea710c5f7654c538870eb22a629c43875926314e218f4e132a8710c7970995438868e39aa8a1c43471d15350e218f4e1b288710c7970d94438870fb2a8621c4387595
  | 15 => 0x547158953106adb82c4a9883561c16254c41a38e8b02a620d4f7258153106a6392c0a9883551c56054c41a3ce8302a620e5960181531062fbb2a6298839554d61d0c41caca6b088620c5f73582521062e39ac129083175da53148418beeca98a420c6f76548521072d29cc0290839654e6014841cb4a6b00a420e59535805210734a92c029083175d663d08418beeab1e8420c5d7694f421062fbb2a7a1083875955390841c3aa6b0c8420e5553984421072aa9ac221083c354e6210841e1aa72908420f0e53548421078aa9cc2210838754d6110841e2aa6b088420cb775584421071bbaac221083a594d6110841c6aa6b088420e9553584421070aa9ac2210832d5c664cc841c3ac929e6420e1e6454f321070eb22a7990831edc1654c8418f0e0b2a6420e1f6454d321070e322a6990839554f614c841c3aa73168220c3d76952411063abb4a92088387d965350441c3ecaa9a8220f147154d411070ea98c4a088395d965350441caecaa9a8220f165454d411069abac86a08832d9db4250441b2ce7a128220c5f7358a501062e39ac528083175da53140418beeca98a020e4e539885010726a9cc4280839394d6214041c9aa6b10a020c7b765405010734b12a0280839598d61d533187eecaa0a998e395458054cc738b0cc02a6638e9916015331cb4c6b00a998d397015343cc6acb80a921e630f9d85450f31a72e02a28798d9571d5143cc62f3b0a8a1e63565c05450f3193cec2a28798d997015143cc68f3b0a8a1e63879d85450f31a3ce42a28798f157115143cc78d380a8a1e63475c05450f31e32e02a28798d197015143cc61fbb2a821e63a550d6110f31c3cc8a1ca598c6f7654852cc63d384cb216631e5c26590b31c3ccaa1c8598e1d5418d41cc6ca38a86a0e63a558d411073187ee8b14a198c3c7458a50cc70e32286a86631edd95014331c72c8a80a198e5563987548c61fbb2a82a4638d5506150e318deeca90a518d2d72150428c71a2a2c22146347dd1528ca31a9ee4aa06518d1f74548328c61f3b0a8a0c630fdd95410631c3ca8b188318e1d5458c418c63dbb2a0284638bd906255131c9ec6312a898e6462d85544c735b16c0aa2639a18b6055131c76c8302a898e5b63181544c735b10c0aa2639a1886055131ce6c2302a898c3f76550544c696392a82a2634e1c15415131c68a8b0e8698d1e75d91434c68f3a4a8a1a63179d85450d31a3cec2a28698e1e76151434c68f390a8a1a63475c05450d319acea30a8698e5675185434c637bb2a4292634b1d15214931ad0e0a90a498d547150c524c61fba2c0292630f1d160149319a8e2b1e8498e4d6314b424c68e3aa8721263879954390931b28e2a1c8498c7b70594424c63c382ca212631e9c065109318f2e03288498e1c5458c424c68e3aa8621263871954310931b28
  | 16 => 0xcb1bb20c2aa26595d8c6155132ccec430aa89967361d81544cb3830ec0aa2658ed906055132cb6c6302a89966b62181544cb39b08c0aa2659c184605513287eecaa0a89953471550544ca9c382a82a2658b15162d0d32c3ccaa18869961f5458f424cb0e2a2c7a1265475ce5490932a68e2aa4849953870552424ca1f3b0a8a1265475ce5410932a5ae52a0849943f76550424ca9a38aa8212654e1c15410932aa8e2aa4649955870552324ca3bbb2a228a654d1d15114532ae0e0a88a29947b76540504ca9c3a2a0282655c1c5501413287eecaa0a81963554584540cb1caa2c02a0658d9916115032cacc6b08a81967261980540cb38b0cc02a0658e9916015032cb4c6b00a81967261580540cb38b0ac02a0654d5c454d0c32a72e02a6861955571152430caacb80a92186517dd56290c3299eeab14861964f7558a430ca8f39ea8a18650f9d85450c32a6ae22a2861953970151430cac7396a8a1865179d85450c32aaae22a2861955970151430ca4f3b0a8a1865655c45450c32b32e02a2861951e76151430cb0f3b0a8a1865479c85450c32e1ce42a2861971671151430ca8eb88a8a1865c55c45450c32a2ae22a2861971a70151430ca8eb80a8a1865c65c05450c32a32e02a2861943f76550430cb46a1cc421865879914394832c3aa931c841961c6550c420ca2ebb4a719065475d2538c8328daed29c641958d7494e320ca2fbaac899065351c5644c8329b0e0b22641949d74d89320ca673b68499065a3590424c832b1ce929a64194ce7610d320cb0e32286a8865551c543544328eeeca88a21963564544510cb38a8ac028865871914354032ab0e0a1aa01947b76540500cb1cb22a0280659c58550140328beeca98a7a0e595358053d06cab8ea6a1e83279d85350f41b32e029a87a0e954358443d070f31a87296831bdd95214b418f4e132c65a0c797099632d070f32a871968317dcd62943418b8e6b14a1a0e1c6350d50d063dbb2a0286839658d50143418beeca98a720c6f76548529068fb9aa5214834bdc95310a41a3ee6a908520c7b76540509062fbb2a629a83531c95314d41ab0e0a98a6a0d1e75d8d435068f3b0a6a1a83879d85350d41a3ce429a86a0d1d7014d435065b3a8c2a1a838d9d46150d418deeca90a4a0d4c7354852506b4382a4292834d1c543149418bee6b00a4a0c5c73580525065a38ac9992838b59052cc941c3ccaa1c64a0d947150e325063db82ca192831e1c1650c9418f4e032864a0c7970194325070eb20a61928387195430c941b28e2a1864a0f0d43148325072a29ac219283a550d610c941cc8a4b0864a0c7b7654050506ac39aa0282835a1c950141418bee6b10a0a0c5c7358850506ad380c929883565c06494c41a3ce9b14a620d1e74182531072cb00c129883479d36254c41a38e8b12a620d
  | 17 => 0x9087a650d601484393eeca1ea221e99439835110f4ca1ac1a88875c9c35194443c3eeca1aa221e1c7650d5110f8bb8a86a8887c51c54354443c3a86312a221e1d43d815110e4fbb286288871ddd9511444393eeca1ea021e95439875010f4aa1ac3a80875c9c75094043c3eeca1aa021e1c7650d5010f8db8286a8087c61c14354043c3a86312a021e1d43d855010e4fbb286280871edd95014043aace2324a7a15557119253d0aad380c929e85565c06494f42a3ce830ca7a16556118653d0a8f3a0c129e85965806094f42aaee2b12a7a15547158953d0aadb82c4a9e85561c16254f42a9ee4b0aa7a151e7418553d0b2ab08c2a9e8553dc96054f42a3ce8302a7a16596018153d0a2fbb2a629e859354e62d0f42c9ca731087a165a5398351d0b2ca9cc1a8e859694d60d4742cb2a6b06a3a157270d4651d0a2ebb4a628e8517dd953147428eeeca88a3a16565398750d0b2aa9cc3a86859594d61d4342caaa6b0ea1a157271d4250d0a2ebb4a62868517dd953143428f6eca80a1a145f7654c5390a8f3b4a6a1c85879da5350e42a3ae329a872151d7094d4390b0eb2cc7a14858759563d0a42c9acb31e852164d6558f4290a3bbb2a228c851edd950142428beeca98a6a15547154c5350aac382a629a85879954310d428eeeca88a2a1554735445150ab8382a228a851edd95014142ab0e6a80a0a1570715405050a2fbb2a6298859554d6114c42cb2a6b00a6214af7558b4310b17baac5a1885639cb5350c4293cec29a86215957114d4310accb80a6a1885a350e6210c4287aed2a4842146d769524210ac6b9ca921085639ce545084295cec21a842161c6350d5110a9a38a86a88851ddd95114442caac6a88a221671515805110b0e31a86a80854e1c143540428f6eca80a021659635405010b38b0aa0280859398d62d5332a6ce231ca9995357118e54cca9d380c72a6654e5c06395332a3ce630ca9996356118654cca8f398c12a6658e5806095332a6ee2b12a9995347158954cca9db82c4aa6654e1c16255332a5ee4b0aa99951e7318554ccb1ab08c2aa6654bdc96055332a3ce6302a9996396018154cca1fbb2a82a6658b5526290f32c5ca9310879961d5498f42ccb0f2a2c7a16658755163d0b32c3aa9b1a859961d5418d42ccb1d2a4c1a8e658e55260d4732c74a8b06a3996395458351ccab9386a328e650f5da541473287eecaa0a3994777654451ccb1b2a4c3a86658d55261d4332c6ca8b0ea1996355458750ccab938ea1286650f5da541433287eecaa0a19947b7654050ccb26b1cc5aa4650fdd95415232c5aa8312871945e76951438ca8f3b4a8a1c65879da5450e32a3ae32a2871951d70951438cac7b928721465879516310a32c3acb326651961d65593328cb16b2cc9994658b59564cca328eeeca88a31947b76540508
  | 18 => 0x400080080020040018008008002000000800c00100000040000020080000000008000003400000b005801000000100380180020000000004006001000000000c00000000000040010040030000002006801c000003000000c0000000000010000002000000000e000000800000200000000000000000000000000017001000401a000000001000200000000000180080000028016000000800000800400300080000000018000000001000001c00400b0018054004000002000400c002000800000400000080080080030038010000001000000000400700080040060020010010008003001801800e00300000000040010010000004000000801000200100000200020010050018006000001000400000200000000000060000000000002002802001c00300600040120050008000002006000000c0060020000020000003000800400000000000000060030000000002003001000c00e0020000000002001000000000200200180040000040000000000002004800c000000003801000a00000080000020070000004000004000801c002000000000400a0010058014000001000803c02a017003000400200100000000040020000000002000000000801000800080040000010010000002000000800400c000009000400000600200000280000010000006001001000000200000000000000010000000000000002000c000004001800000000e000001400600000080000000030030024008002000800001200000280000000000010018012000005004000c00000080000000000040004000000000801400200200800000040000000000020002001000000400000200080020008deeca90a5a1c777654451d0e3dbb2a0286871bdd95214a438eeeca88a321c7b765405090e37bb2a429287591c55214943ad0e0a90a4a1c7b705845250e3c382c2292871ddc560149438e8e2b00a4a1c77765445150eb2392a228a875c1c151145438f6e0b10a2a1c78705885150e3dbb2a0282875a1c95014143ae0e2a80a0a1c77715885050e3a38ac4282870f5da5490c438baed2a48621e1d75d954310f0f3b6caa1887479cb6550c43a3ae3b2a8621d1d70d954310e8ebacc4a188747dd56250c43b2ee2b128621d94715894310ecdb82c4a1887661c16250c43d1ac43128621d1d759854310e8fbaac2a188763dc96150c43b18e4b0a8621d9b705854310ecc382c2a1887a55846150c43a3aeb3028621d1f755814310ec7b92c0a1887631c96050c43b2ee2b028621d94715814310f4cb00c0a188727dd943d4843c3eeca1ca421e1c7650e5210f87b928729087c31c94394843c3a86b0ca421c7b705865210e3c382c3290878750d60948438eee2b04a421c74715825210e4fbb286290871bdd95214843d2a87308a421e95435845210f4ca1cc02
  | 19 => 0x1801400000100000000080040008004002000000800400600100080100000020000010002000001000000800000100240000000008004002000000002400800a0000008000001003001000600100700100040000030004000000000001000000000600040000000008000038000001803000600300080040000100078004002002003000401200700000180040010000010006000001800c00a01000000140040010010000000002000000c000000001000c00001b001801400400100100000040000010014000008001800800400000180000000060050000000004000003800000000000200000010000024006001001002000200200180000000010048000000003001800000000000200000000000000010000009002800800e002000001400c003000000000200100000040020000000000000000000001c00400000b0004000001000001c00a002000000000000100280080020000000004000000000001c008000001800000e00000000000000000000000000000002800c0060040000000000001000800c000002000000000600100000000060000008000004000002001000c004000000000200000500180000010008004014001004000c01800c0030000008002000000800000d0028000000014000000000600000000100000010000018004008001800400000200180000000030000008000001000000000200000180100060020000018002010001002000c00000280000020030000004000002002000000a001009800000400000000040000010010004000005000003400200200400000180040008000000008000002800000000300000080010000000004000000000800600600000000000000000000000001002000400c00400080000000000030000006004000003000000100000000040000028000000002000000000600200100000140000000000000000001000400000100000000180020068018000001000800400800000100000020030018024010001002800000e00a003800c002000002800000a0010000004000001000000c000002000003000200000080000080050000020004000000000800a000000800400c0010030058000000001000800000000000380000000000004008006000000402a0000008000012002000800400600100180000000000018020004000001000c00e002004000400000600180000040000008008006002000800000000a00000000020230008034002000000000800001200200040000030008000008000000000800c000002000c00000200000000140000008048008003000001c00000300000180020030078000000000002000001000400080000080050000000002000000800000c000000800400400000000040140000020004000002000800c00000000100000080080040
  | 20 => 0x4ba0a18efa0005f38000000a4d0000fa000092007708480009e700000004580002b528bc0000000001cd823e0002a0800159a0005fc912cba200d4c8175cf580000000000184bd91311ea97fa48a4868000000000000000169c72d291000000014800028100000000000000000aed000000000006009e00000003090002024b94a72033800000000000007f89b043400028a871a56b00007f054200000011cc000000000000000000016691280000005ac24740001f90a5800008c8fb1e314b034842e00016bd4a000058780000000005bb14980007175778000a762383652e3000000000000012b400001e851c4b80000001400000000000000055e4c9332800059c52f21f93e8b24a553bc9b4c000000000000000000038380000006920002bac0004cd2ca8000000a2d0920000d4c5d34ef800000000000021ec0000003f3000171200000000009c0000515800077e00012280017be0311cbaf4c6028854140a3d774a8d4420b44d985055c900a50fa4a65df83f0b92b351be853d15c6df4f000005aa30000000006969c146986d0362bb1000000000018700020354f816e38a05b400000048080000000001dd0888f48bc8000155d59e000000000000043b2b60000a9e30a30f073c0000000e906240001664c7a388dd474a2822588846bf7281184cc3e9e53fd81c801e75c594092c71886f00000008e00000000688de43b1223000154250100006a00000005de00017109dd04284743ee24636023940008fe56400000005440a00e140004ba000000000000053c800032c000000000000000000022c4de64de00014f00000001870000000000244000131a0000002d845985da3e48f340008f200000000000000001c455f489931d800153e68c19d0cc513082100000000000005dea2d075a10422f00000007062958000bd60005f0ad286ac0002698000ae20003e080012760001ac1d5c3b684b008800000071500019b000090e3242bcd26c05306582a465a1650002d94eaa62a035850cbd89f234d19494c27200f21b909b60005142a800322110002f5d4fc5c33cf9fc16bc8be3c08000000bc70002bb092e47f08f12cd29a038541ae1800056400012a10ca0000000000e12798000280553800005c13bc1baaf2000176471c51419c83b00d2762216a6e519802e34a80005300000000000000000276aff907e0000000000000000000000000000000008656860005a82778000202142123c0261b045580002baaae000000099887546502c4bb000019500000004755b3a7b0e045651a21dd12b892c23c000000073c373ab4d1fa0000000000000bff46f2fa800037a116ae700005981542254000a57000000000046c0000000f800ae15c000000002f4de000000086935480000000028000000001000000000400100200040000000040000006
  | 21 => 0x96785b0359a03c5fe0000000000396a290000000e181030001dd43986b142eab2cafa0870002eec00000000005cc8580002b7000153200017500010e85a238820e0000000148a47c97cc0016204cd23857613b9c7975c53300023d97b400045497d8000000000143cba000026fa1d8b347c404b000000000028c80002fc00053280000000005b803d569ea971ca2b78c7482e20496d04b2000000000000000000000000003da45d000000000052917840000003ce80000008ea0000000000aa42ed800000000004421782d6a1a18403a80000005071678000b7257b000063474d5661d589761583b224400001d860093856c400045c2c4503e5282248a7179c0002630000000b1a11c9074bbc2d9000201c00081528e8ac4000000000000172800000000008b4741000223c00024e038800000000052380000007720000000000228570000166029d0ab00016de05952889517e8a4317680015243b90b9000138a9d5403146d48400018d800173408b20500001e274618f918c0000000000f2938402d561000000000040100004d8000000051400000000000010ac00002a9144000000183800000000007c97bc0006d8000000000033d369000000000000000000006c60000438cdc12d00000000003b408e17b539ab3719290e40000000000000000000000000000000000002ac0000001f61180c8a50700000003940000e4800064237655380016d09070000d2000097b32f18b83b43c7100000000095b5aa2b0000081000012d42405fa0002b5915a34d520000000009c1c112347aa00000016c57408b207114312f800000019cc0007f31e21a115aa2de5cfad4421e0eb1df1c580005630fd043076004a0b81328798556203ab7c6a882635b8f655647282bb800114a2bb19c00000000000000001648b6e0aa93709408c500000013f049f000000000045d0000000eb232421504c85b4a25482a5dc0a2ab151380000000003ef99b56f0840000000000000045e000000000000000000000003d790a056800028c1d5171a1010002c089ee32f3da02b00000002c091d034c59b00018cc00000000000000006534999864f641060000000000000000284448627427e9ee000000046d028c0000000ff92100009520002c98e9c0000e8af284841215a218900000864ba800033ab7a0000000a3c0000000b8c00010a3f7000000000000028c81d20000000a784d00004312c3074c00015480000000000000000b70b9b2298000000963063a73c00000000000000008b63d896a8b6c00001a0000e5c22453628fd6842884f82d5c66e0003d98000a60bfc142800000084c00024184b000000000000006961f800000006ac122163d2f27e307688a81b475f3d70000000000164800042a6e50001a5c00006f09782a8b2e00000000000005791d70001056000
  | 22 => 0x159080016b200002b24447d400055c00000001b63282124bc06fe10f06040000000001c3c0003301b89aac000aba13c04d86ce000000010cc18000257800084c8d435d80010340000000000000000429af54000ae102127ad3964082ad2a0839a9e31412fcd71696000000000002b60000000000525000000000027e03a190021a5c80001a089e872400000003902103bf00000000000000a2519ea9b4a8800112800000000005b60005f2a2cc4129a130222fc00098e00000000000003f2285d3fc2f117099988240000000000f5a00000009f02f2b752339a0022c0002ee0000d220000000000000000416000000000046ca1b400098400000000000000000000000000000000141600025c80000009e60001dac0000000000000000273020ad74d500004bf00e40007e032b80000000000258ef40005fc4aca5d800075d0000e3c08850e0000f8815a0cd000000000000000003040009d900000000000000f980000000002b4800000000025b80002168170002bf0000a9342ba85400000014f9a740000004b09ee532a000000103c00031d00029ac26a6ef5440e651c200000025a15a2beb29900010e00000001d200000001ad80000001300002938000a2129e800000000000000005260000000000000b903ed000000019e2bc0000ac4000000200400013100020647966d50002134c2a00000000000000000001a64000000000000000000000000000004e3285a771278375058000024a0000048814e849da0001f797680000b08000b3a6c724580014189bf5b69fb0df80c020317880004c5113950000000000017eca5a7c6039800161c3d20b780000003ff37080000002fc4411dfc13254b22d80000000000002028f3c1e04f4a6c43e44a232f8000000be400000000000000000f4ca140001f923340003e300000000009140001b3c0000000002d200000004d6000049008200000000009d200000000003a200007c02ae00031122840003a52e78000000ba215d0d080008335e922c000022f0001da00000001ad1c142207bf559800140c4b00b600005660001fb00015ea74c5d3950955271f2c48d3c00037b0000000b9a00000016acab21620ce1390000000471ae0c0006140490000000b7d05caf4455c55d000000000004c00026a42a6000000000000000027b000040892538026f8ffc00000028596e294900000015e219b000000000000000000000000000000000cee68900026900003fe3a98ff42d2b7f01800000001df0000000222000000291800006810fa3fd10cbc316b9d48b960000001f9c4ea02a1dc29dd008a1b29c00000009263041a5098e0005f10000dec00000000000001e10000b80000bc656c0000f4ea910000b504c82f60eb0f9c19c37e29a00000008d231f80009687cc1e7800129e39611882951540001e1223
  | 23 => 0x888fabfa2a6230c84a3fa03e96f46c09664481a70faa000000267cf9600000000007309670a89ddc0000db2010d4850000000014d40002b501d00000005060000dc00000004ab20f00003a00001fa0000000435800000000016f91ed5a0000000000000014c51e0bac9b241700029c159c7a300000014de01c267000058a0000000000882b950000000000af800000000008053d59b0c00084f00000013280004cba8e139c0001249ed87c2b565e48000b425c400022a1806b80000196c0000003da99c0b4c00000000002d43fc1e0800022841a019000082000000016d54f43ed000000000025b000000000078600024b400000000000000003bc00000013a826300000000000005ec046537404f0000000000000000300800000000016ed3a00003390000000ad90000000754000000000000000000000000000004d4155169667d000069d16e0b300019fc00000000000000000000000000de200000011415949fc2be0dace8e0004419c700000000000000000000096000164600a5db88d800000022b8000000454000008c0000002b808d50e2aa80aa2cc80003115cb00000000f300000016c84e80002410f205e800000001761ad0000000ae87780000aac00000002e800000000037180000000000000d5400053700024200b43e532a22f400000000015700006090002bd00000910000cfc0000002a8845c0008df1db2449330b410002becf50000000000000000000012c40002f80e800016fc00031c1ac00000004799e4400000000007a40000005f780016c00002d90000aa06bf4d91d8d2bc04e59f9a6cb160201f0124d462a3a1912ad8ed8ad4127a35cbce34c20cad1d65e15039f80000005b90000fe40008ec401a6e0000a6000000000000003bd80000000000000000000000440920800000000016b127e21700000007d249400006a4fdea081c8276c00077c1fd818c0007c700000000005c0000187482a6a43f88ac800000028aa37072207500015f8000000397a8800007f24ac00000008112712c540002fa00001f06ba34043b8000c9861c332107800088710a11f025c13726d01b070663200015480000000000e483841c14972dcd60a48028d2958cd000041aa57c000850544a6b400000018200014a827f045000000097f000000086a0e33df27ec0006a00000000eca0001c4a0e408aa35000006c8d41ee0ecaad4bfc00038680008648b93fa80000000000001ec05dc54300000000005360001bd400000000000013548142908de16f200015e800041c0000000000e729b300000000000000000000000bfb18a0000b401e249a0000b8e0003258f3800000000000000000000000000000000000000000000000000000000001ee29780007eb05d1c8c0000004c08000000000000274c000a1f000000138842b0652c2ce5402
  | 24 => 0xf00000c340006ad000000000000000000000000000000001074ab717da8c000007028e00014246183761ad0fa430f4a403c897e416213a3ac02a0652189bdcdbc1b32610170a126b20000000ede82322e000170eb9d42900004063122330000c9c21a00007000005dd00021f000000000005c40000000af80000001493f080010fc000000000000000017a83f89a015c00000000000003102a3c0000004a595b4e9200012f264456025a2a500004a2b8a221961816aac50000000000000000032400078f3ee0a692ba9fa00029140000000002abcf74bf100009bc0000000000000000000000000017e00051f2ae400000038500000205f100000000000000000000414000000075d0b400039aaef8000b6a00000005322bf2390000000b3a44d28f524686411300000000000001c052e20bc000215054832b19d80000000003fd05f09aaba43fc9ea49700003cbadb0000000229248400000000024900006110002ab400000053a8000b140001d9a9e00000000000bc80008920cd0000000000398800000000000003180008c854d2fd80007034180000000000000000075652a55e8edc2ce7925c0a398c68a5355da0312fa17b34f0e8c47a85f3de8dcc99632c476a5e800000000000000005c213595617328a35e0000000062600000000000000ba06540000000000000000000000000126abcf543a648bfe28a000124400071235a80000009ff03f0ba0d9a0000002f3073465d035000000047e30b817cd7a0004b49d78aea00012a800000014e00a000169a62900000000183930002f4065c0000f6800037eabe000029c000000000253086e9c74e01d6161a2e542193d4db63530af08755fa20b023867d6064a91060074fa05f94b90224a1a8b529c80002b684800019d00000001949090da8bc53620421064599422925800e1ef0470c58ac29f62460f206d44142c3911d36a3a94f11e6461876d58b89a83c61ce27886a83ea06205a1bc069210226017301be9af00000000000000002a1835c000000000000080800012b8000a680000f140003054ce9e5525662148ca1e0c940000000000000000000000000062b00027180009f959b06183d4aac3cd01fd1800000001a1c0006e63f6ace53406a20000000ec2ba654f0dfd4ba01f15398d928e0003b5000054400000024f868c1120c9a7d05fc00018c8ddc6da8410021748c5a6e923780000000004c397c80000000001f4c0002a6318a338bdc5b349780000009cc00f00004be0000002fb46206d11ea28d0ace00000006840000004eb8000f860350e300005780000e280000007381e4a5b57542d058494b862e5d50001cf438ebe05782891630bc239d00005f251f09a0000786834053000000044f26b000128899c2c6063127251058da864cc68fc1be1bd15681184e4000154c0e425219
  | 25 => 0xbb80000000000190f04a95344000000000000018c07b60000002038cde3800b20000fac000000000040e5290cbae94c0c7441d780003167c50dd00000760000002529490345000281400035700027280000004f980000004c342e17cd6ee00026e89580005ad000000000000000000006d200000000000000004b78000fee0004cb0150b26780000000086c5df00000000001f401e262134a8c119e19586dc76914686dcb460001fb99247bc000084a6080001e800000012a80000001b8978200000000000000000000000d4600000007f400090911f800003465c0000bbd60e36c56e0af977010758ca310388a6659607790d449e0c500dc93800057c8000000a104fba0582b400021498014b47880000000a2c24700023a535600000000011f20000a680000004f309100000000000d29e717dc729000000000000000009351c84ac0002c9c0000000000000eec0002099b4160223b1cf11b840c13a000186800002c07f844c00079b00b00002c600000000015ce00000000000000000002c8906c91b0000000000372273802d5466bc501000073e43312ba0a8c72000000130400000027509c8e5800007d1bf40002162a282687cc26717218f9140000000000000000000019ec00000000017e000000003b08d00001fb0c1a48913c0d11099dcc1902814510d903ba000250800000000000028e40000000000000e100002c006e40004620002a2d29c000268800000000052623a00004870001858f4c00054a03940000003ec0000764444059020d63e73300005fc0002d65f302dc00000000001e400000014a00000000003fe1ff400000052c00000000005f1a7903aa0003351ad80000840690d9445c0000000001752000000000000000053f800000000000012140000000000510be8479000000000073e33381841f699e00011340a41ac1749d98000a8000020f837a05b00012248b0000119800000000054eaded5ee59636c8f4471027d3c6a0ec00000000000007481c358e91551ba0005a60000000000000250c000be900000000000001b419ac0000000000000000000000000066c0000002554000bc40001e1c1cc607000088000044546b00005189860001610cb009746d80015022c1163206127a000000037108c0004d180007f06e8000000000000000000000002080002b496d6ae61301a8400005700023dc1486a70000ccc9dc00000000017b886700010714fa07a2fa8b2c46e00007000004820000000000000aff0002ca452a0ef00003dcfeca221260000cf05c6352a66c00000026b800000044e0000000000abf55291a00000f00002ac1666b9138d0000000b2000029100000770140dd000002700000009464902bd835923035f34c2d700000000000000c9e3f3348234000000053100000009e800017f4e808510df00006302
  | 26 => 0x436000328a8ec0f6822205ae3ccb280b50a15192d400000000005cc4eb26900000000001b1000000060a00028dca4698934fab054b22c82b4016000081d1c30001148820000000000074300027b400000000000000000000000d780000000002b94000b3800000000000005aa800000000000000000000005ed9650f9e8973ed8001482000000025406c0000c200008d6000049a380000000000000064e67c00000004781a333a980942608c362a6d0a4e9803ff85dd00000000000012700002eb27bc7e800000003d01428d122f80000000000001b709543353070614b20893321aaac00000009500005b872209f97a800063c0002a101aa93144e00009e0ae94802180ae400000005485060000000000000ae81e800980000000d7800000000000023d113600000006d55c638b41e80000008c90002ed8000bb332aa1640000000828001048000347000000042200000005468122089f2856e58d5cf0000fc4b7c000000087a00049404f8c4639c2e29d3ccd23130000000000bf200009b400074b5ea094075000058b22300dc00011809e476a84453200000000000000000e4c1903b700000009404a302a000034342380000000000001814f7679400000000000003c600009884a54de80015302ad000066106e65a0de000000000000028740005884f08000b0400002408a432855f1a504540000000000000000000000000000026100019840005204b600000000000001b5800025d00019e400000007e80000000000ea25140007c80000b000005b721e222c9ca0000ee00004640000000000000003393805c0005e901fa50959255e0000fbc6a00000f897c000067600000013fa0000000000c840005d6a9a800000038d80000000000000a804a60000000e1d76028e1328d3864c000000000000084e0001840ff027a00000cc0007702a380011f40f637da8d80005ce0c420c424eb120001b0857281c03c00000000000bc112000000000000011aa9ea0002aa80000000002b1c00000000000000004ad00005a158801800000016a6a1c5750000000000012a800f08bd65a300000000002b794f800000000000015b60000000000000000000175000000000000000000000002ca800035144e9ef000000000028b800000000018dd72e000000000000093a1eea75800000043d014000000000000000004640000000000000516063c00090c5ef12f43560000000000664b3e37f8000bcc000000000091c000000126807c0004331d680002c223b8360b7452436ea59165ca0309ea92c000000478a12800000035f11b4000941390aead3a200037d04ac8300000002fa0c4a09e25e1fd10f277a2d2145d626add094231c0006c83c501b44a46f9066000170a3665d40250df000004019f9764000000000139260f3eb80000000000ac9
  | 27 => 0x34c0000005c99a14322ac649b860167636358e2160dc00002a99cc8776000453800000000000000008ac00000000005ba0001f71834000000000000000088920d80004740000000b1d4d2bec000000000000000011a400000034527c4e3a2181f59aa813600031600000002e20000d6567a000000000000030b00000000007930000000b063155130bf40100002df0eb00000003469cc000000052e107d2d64b244680010849c3000000126400000000006680000000000ab68274db80000000000000f5c81a85b19f000085e42000022bc5860000000000afe8d800000017e0b060002540000b143ec800000000052780000000001c526d80000000000000000000000000000049856d0000000000000182c28400000000003324615a28000b3875b5e6800000000053a21b087c0000000350c882f705b1e84c0200000000000004b600000003f0a230000e9c0009734b28000000b0054500016e800000000000000004d38000000000000000126028b00023090c22cf5d08a411dc000000298c0920c50002fd400000000000000000002e08000000000367231951c1a03cb29b80003415988c190d01b8000000000050815282bc0bc0000000000c7a2e70000000a740000bd000000000000000000006c1494800171c4834d100017580002d4000000000000000015dcbdd54b2835206146389800000000000000000000005cc22585d80e138706080000005d7800000000048a800176a14a3ee93ec00000040f00000000000001694ae60000000504e6e000007000161011b0000fd51ea1bb27c10e93b0a9000000016143280000000000a731eb0000a24b34347a18c0000004ab800000000000000009e48e700000000000003c1800000082d45600000000000000000000000000000063820d000000050e000000000000000000000017046350000198e760122bd2a140000000002af1326000376ac1121e240000227c00000027f0000d5c3df3d107980000000000000000a710f6180c1448cb35c8310000b254938000f4a2963179934f1638400080012dc04d000030c6f2902000000000000000015549d2000000000011eb633c70000e560000000000000000000191d2345f75ad984800067a3e10000d1600056ba54cdaeb4957101002ea88800004ec12064120623bc000000000000000000000012644dc3200000000bc840406814448064304d3000143092a0000000ce200027f8ab0a9000057f2e8c0002d2000048c0007673db924800013905f1218000000000063800058e343266930600000000000000000f3800000081b000000000000000000000003951ce828000000000016a49027ea22ca9ec6060000948e841029ae3418018000bb904f80016b4a760e980000000e800000003d65e30002cad052b1057200004ec
  | 28 => 0x7510fb00000003e410780000004ab0000000d963f1525037847c9f524e80014120004178000000002165299d41464600000013dc000000000000000006c80000000005e58000fa20000000000000000596a97c0000001158000a6200007380880006270000000ee200047800012e0549000000117656018f1a056be18d22605813328721b78000cc07e9000000000000038588040000000001e8053687f0001084000000125000111400008d00000000000000000b5c30240980000005a7000000068e00042a80012268a604e95380000002b31f5000000016c2d98000a1e35c0001466000000133c44643800013b06b89173e70000b7e22506b8000e4a0003f29f3522c0000000000000693000000011a6c9000000000040e00000000000000000000000000000242800000000000000000002200000a9a9b0000161400002b26a049940e1380c91b680004fc2c8899958649b0002da42fa00000000000000000000c8c5248911c089c0f1200000000001f0000000000052ea5b39a2d484e200000008700000000000000130405000283c00071800006c800000048f11d91002aa00014fc0000000000f000002f300025e0000024253a09400000030d8000d7476028998a0000000169800017a704536833c00000020090000000001ec2e10e32000002a6ec000b1e2cfa3e00000003a8000000086e0000000000000000040000098a23d140c00000000000004426af0000000000b40232aa317f01760001d14bca0004c58794000269000132131890b17a000000000000000000004424c2a9249cc0000001e148e24f955100010e65bc24a8e6c00027b1b09bac000000000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x16194843c1543dc56094843c0e769c85450c32d11719c05450c32d12715c05450c32d11715c05450c32a8481590424c832a8880590424c832a1980995438cb41a1980195430c941b048150c520c941e0543149610c941a48825806054c41a158199153cc841915859cf4250441c16765c45450f31d11719c05450f31a19809954390b31a19801954310931b048150c5210931e05431496110931a28825806055031c15545c663d0831915859d3324c431a19801954310f21a15839516110b21a158494d610cb21a1980d954310e21c15635c46315121c15645c46414d21a148550d6110d21c147550d6110d21c85431c96110d21c147558d4110521a158614d4110521c85631c94110521d04531c94110521c1475591310c521a1586151310c521c85641c9310c521d04541c9310c521d11435c44314121960825c44314121d11735044114121b20825044114121d11744c43114121b40824c43114121ac283d086048421aa284cc86048421a1581995438cb40a1581195430c940b088050c520c940e0943149600c940a44825846154c40a198099153cc840a158694d4110440c15645c6530c440a1980991530c440a19809915388440919859cf4250040919859cc4150040c1a765c05450f30d12715c05450f30a15819954390b30a15811954310930b088050c5210930e09431496010930a24825846155030c19545c263d0830c19545c26310430a15819516310430a1586951310c430c19545c26388430919859d3324c030919859d0314c030a15811954310f20a19839516010b20a198494d600cb20a1581d954310e20a15819516310620c15645c6530c620c19635c06315120c19645c06414d20a188550d6010d20c187550d6010d20c89431c96010d20d11435c04314520960825c04314520c187558d4010120a198614d4010120c89631c94010120d08531c94010120e11631454010120d20721454010120c1875591300c120a1986151300c120c89641c9300c120d08541c9300c120e1164145300c120d4072145300c120ac283d086148020aa284cc86148020a0c825516315110c0d641c95314d10a1581d954310d10a1980d954310d1081c875954310d10a0c825954310d10a15831516110910a19831516010910a158414d610c910a198414d600c910a198315160d0510a198414d60cc510a158315161d0110a158414d61cc110d04741cd5208410d20741c15208410d40731c15208410d08741cd5208010d20741c55208010d40731c55208010a90835906444010aa0825906444010c91645cc6444010a908458c6344010c917458c6344010ac08258c63440108e0825d84344010a908650c4344010c917650c4344010ca0741895244010cc0731895244010d21745485244010d41735485244010cc27318b4244010ca27418b3244010
  | 1 => 0x6f4097c2a3100000000000000001e0b098a2440ca3cfa001b000fc4224000b8781d000cc0a0d000000000004522f00000d80008884984d0698480204820cb2170006c68372908d102a180d4da43001ecec50011c80089000b0006425914665423a10002e340949c072ba30dc3d001cc000b00000c43f1f238b603138c91a00001e8f2602c0ac00651e0001e002f104ea6b00228281c00000000e1c0001810430e444081d87ce86a049c0ac532aa2cc68740000006702000004a16800000038a089224140149e7723048305a3e018007f2e80000690ea1426090006050b03000201010005000001060001030502170802000200010300000705000b040b0b0002030002130103040491b805c76550c43917815c36550c43a84815886250c43a88805886250c43a84825846150c43a90805846150c43a88825806050c43a90815806050c43c1943dc
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xda0005005b004388054bc0e32820000ba024aa86392c221a434059614c725044148680b2c2a0e49886290e4050c825c44314121c80b9904a08822824390174209310c4504868112aa18e4b00869064050c825c04314520a04cb0a63928020241c01631c851500404828132c2a0e4980609070059072145300c120a40492c8b98c888021881742096318d1004212130bb28621a20085202497650c4344010
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
  | 5 => packedAt gbK5 (337702+((h/2638+packedAt gbK5 (300770+(h % 2638)*14) 14) % 10448)*14) 14
  | 4 => packedAt gbK4 (164049+((h/1025+packedAt gbK4 (150724+(h % 1025)*13) 13) % 5404)*13) 13
  | 3 => packedAt gbK3 (9084+((h/48+packedAt gbK3 (8700+(h % 48)*8) 8) % 192)*9) 9
  | 2 => packedAt gbK2 (1161+((h/5+packedAt gbK2 (1136+(h % 5)*5) 5) % 22)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe03ffffc07fffff03f07ff87fff0fff463f1ff
  | 1 => 0xffc07ffff80fffffc007fff87fff0ff87c7e3f
  | 2 => 0xffff80fffff01ffffff81fff83fff07f9f8fc7
  | 3 => 0xffffffe03fffffe00003ffff8fe00ff8
  | 4 => 0xffffff000000003ffffffffffc00000ffff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x29850a44712244900b416584a4b0949421b0db
  | 1 => 0x4293148890e48922c082aac8495909284c562d
  | 2 => 0x850a26112241d2055508131102622041968b46
  | 3 => 0x162c58e2448903b9a6d4c044638cce0ee00db0
  | 4 => 0x183060c3870e1c3e38e71c6670088c0f7b6000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xf8e8e880f8e8e880f8e8e880f8e8e880f8e8e880f8e8e880f8e8e880f8e8e880f8e8e880f8e8e880f8e8e880f8e8e880f8e8e880f8e8e880f8e8e880f8e8e880, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12943
namespace PEqualNP.Outside.L_meta_12943
open PEqualNP.Outside.L_meta_12943.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 16 := bgb_2_0
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
theorem bgb_3_128 : Interval gbAtlas 3 128 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 145 := (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 (concat bgb_3_96 bgb_3_128)))
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
theorem bgb_4_3072 : Interval gbAtlas 4 3072 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3076 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160))) (concat (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)) (concat bgb_4_288 (concat bgb_4_320 bgb_4_352)))) (concat (concat (concat bgb_4_384 (concat bgb_4_416 bgb_4_448)) (concat bgb_4_480 (concat bgb_4_512 bgb_4_544))) (concat (concat bgb_4_576 (concat bgb_4_608 bgb_4_640)) (concat bgb_4_672 (concat bgb_4_704 bgb_4_736))))) (concat (concat (concat (concat bgb_4_768 (concat bgb_4_800 bgb_4_832)) (concat bgb_4_864 (concat bgb_4_896 bgb_4_928))) (concat (concat bgb_4_960 (concat bgb_4_992 bgb_4_1024)) (concat bgb_4_1056 (concat bgb_4_1088 bgb_4_1120)))) (concat (concat (concat bgb_4_1152 (concat bgb_4_1184 bgb_4_1216)) (concat bgb_4_1248 (concat bgb_4_1280 bgb_4_1312))) (concat (concat bgb_4_1344 (concat bgb_4_1376 bgb_4_1408)) (concat bgb_4_1440 (concat bgb_4_1472 bgb_4_1504)))))) (concat (concat (concat (concat (concat bgb_4_1536 (concat bgb_4_1568 bgb_4_1600)) (concat bgb_4_1632 (concat bgb_4_1664 bgb_4_1696))) (concat (concat bgb_4_1728 (concat bgb_4_1760 bgb_4_1792)) (concat bgb_4_1824 (concat bgb_4_1856 bgb_4_1888)))) (concat (concat (concat bgb_4_1920 (concat bgb_4_1952 bgb_4_1984)) (concat bgb_4_2016 (concat bgb_4_2048 bgb_4_2080))) (concat (concat bgb_4_2112 (concat bgb_4_2144 bgb_4_2176)) (concat bgb_4_2208 (concat bgb_4_2240 bgb_4_2272))))) (concat (concat (concat (concat bgb_4_2304 (concat bgb_4_2336 bgb_4_2368)) (concat bgb_4_2400 (concat bgb_4_2432 bgb_4_2464))) (concat (concat bgb_4_2496 (concat bgb_4_2528 bgb_4_2560)) (concat bgb_4_2592 (concat bgb_4_2624 bgb_4_2656)))) (concat (concat (concat bgb_4_2688 (concat bgb_4_2720 bgb_4_2752)) (concat bgb_4_2784 (concat bgb_4_2816 bgb_4_2848))) (concat (concat bgb_4_2880 (concat bgb_4_2912 bgb_4_2944)) (concat (concat bgb_4_2976 bgb_4_3008) (concat bgb_4_3040 bgb_4_3072)))))))
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
theorem bgb_5_7904 : Interval gbAtlas 5 7904 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 7915 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 bgb_5_576)) (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 bgb_5_704))) (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832)) (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960))))) (concat (concat (concat (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184))) (concat (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)) (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 bgb_5_1440)))) (concat (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568)) (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696))) (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 bgb_5_1952)))))) (concat (concat (concat (concat (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048)) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 bgb_5_2176))) (concat (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 bgb_5_2304)) (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432)))) (concat (concat (concat (concat bgb_5_2464 bgb_5_2496) (concat bgb_5_2528 bgb_5_2560)) (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 bgb_5_2688))) (concat (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 bgb_5_2816)) (concat (concat bgb_5_2848 bgb_5_2880) (concat bgb_5_2912 bgb_5_2944))))) (concat (concat (concat (concat bgb_5_2976 (concat bgb_5_3008 bgb_5_3040)) (concat (concat bgb_5_3072 bgb_5_3104) (concat bgb_5_3136 bgb_5_3168))) (concat (concat (concat bgb_5_3200 bgb_5_3232) (concat bgb_5_3264 bgb_5_3296)) (concat (concat bgb_5_3328 bgb_5_3360) (concat bgb_5_3392 bgb_5_3424)))) (concat (concat (concat (concat bgb_5_3456 bgb_5_3488) (concat bgb_5_3520 bgb_5_3552)) (concat (concat bgb_5_3584 bgb_5_3616) (concat bgb_5_3648 bgb_5_3680))) (concat (concat (concat bgb_5_3712 bgb_5_3744) (concat bgb_5_3776 bgb_5_3808)) (concat (concat bgb_5_3840 bgb_5_3872) (concat bgb_5_3904 bgb_5_3936))))))) (concat (concat (concat (concat (concat (concat bgb_5_3968 (concat bgb_5_4000 bgb_5_4032)) (concat (concat bgb_5_4064 bgb_5_4096) (concat bgb_5_4128 bgb_5_4160))) (concat (concat (concat bgb_5_4192 bgb_5_4224) (concat bgb_5_4256 bgb_5_4288)) (concat (concat bgb_5_4320 bgb_5_4352) (concat bgb_5_4384 bgb_5_4416)))) (concat (concat (concat (concat bgb_5_4448 bgb_5_4480) (concat bgb_5_4512 bgb_5_4544)) (concat (concat bgb_5_4576 bgb_5_4608) (concat bgb_5_4640 bgb_5_4672))) (concat (concat (concat bgb_5_4704 bgb_5_4736) (concat bgb_5_4768 bgb_5_4800)) (concat (concat bgb_5_4832 bgb_5_4864) (concat bgb_5_4896 bgb_5_4928))))) (concat (concat (concat (concat bgb_5_4960 (concat bgb_5_4992 bgb_5_5024)) (concat (concat bgb_5_5056 bgb_5_5088) (concat bgb_5_5120 bgb_5_5152))) (concat (concat (concat bgb_5_5184 bgb_5_5216) (concat bgb_5_5248 bgb_5_5280)) (concat (concat bgb_5_5312 bgb_5_5344) (concat bgb_5_5376 bgb_5_5408)))) (concat (concat (concat (concat bgb_5_5440 bgb_5_5472) (concat bgb_5_5504 bgb_5_5536)) (concat (concat bgb_5_5568 bgb_5_5600) (concat bgb_5_5632 bgb_5_5664))) (concat (concat (concat bgb_5_5696 bgb_5_5728) (concat bgb_5_5760 bgb_5_5792)) (concat (concat bgb_5_5824 bgb_5_5856) (concat bgb_5_5888 bgb_5_5920)))))) (concat (concat (concat (concat (concat bgb_5_5952 (concat bgb_5_5984 bgb_5_6016)) (concat (concat bgb_5_6048 bgb_5_6080) (concat bgb_5_6112 bgb_5_6144))) (concat (concat (concat bgb_5_6176 bgb_5_6208) (concat bgb_5_6240 bgb_5_6272)) (concat (concat bgb_5_6304 bgb_5_6336) (concat bgb_5_6368 bgb_5_6400)))) (concat (concat (concat (concat bgb_5_6432 bgb_5_6464) (concat bgb_5_6496 bgb_5_6528)) (concat (concat bgb_5_6560 bgb_5_6592) (concat bgb_5_6624 bgb_5_6656))) (concat (concat (concat bgb_5_6688 bgb_5_6720) (concat bgb_5_6752 bgb_5_6784)) (concat (concat bgb_5_6816 bgb_5_6848) (concat bgb_5_6880 bgb_5_6912))))) (concat (concat (concat (concat bgb_5_6944 (concat bgb_5_6976 bgb_5_7008)) (concat (concat bgb_5_7040 bgb_5_7072) (concat bgb_5_7104 bgb_5_7136))) (concat (concat (concat bgb_5_7168 bgb_5_7200) (concat bgb_5_7232 bgb_5_7264)) (concat (concat bgb_5_7296 bgb_5_7328) (concat bgb_5_7360 bgb_5_7392)))) (concat (concat (concat (concat bgb_5_7424 bgb_5_7456) (concat bgb_5_7488 bgb_5_7520)) (concat (concat bgb_5_7552 bgb_5_7584) (concat bgb_5_7616 bgb_5_7648))) (concat (concat (concat bgb_5_7680 bgb_5_7712) (concat bgb_5_7744 bgb_5_7776)) (concat (concat bgb_5_7808 bgb_5_7840) (concat bgb_5_7872 bgb_5_7904))))))))
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
theorem bgb_6_1792 : Interval gbAtlas 6 1792 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1798 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)) (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792))))))
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
def fullRoots : List Sig := [inputs.getD 5 zero,inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xf8e8e88088888800f8e8e88088888800f8e8e88088888800f8e8e88088888800f8e8e88088888800f8e8e88088888800f8e8e88088888800f8e8e88088888800
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,7,39)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,7,39)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3938511040 * 2 ^ 32 + 3904929792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12943.Model.Repr at out
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

def mono : List Gate := [⟨.and,[4,5]⟩,⟨.and,[1,2]⟩,⟨.or,[1,2]⟩,⟨.and,[0,3]⟩,⟨.or,[7,9]⟩,⟨.and,[7,9]⟩,⟨.or,[4,5]⟩,⟨.and,[8,12]⟩,⟨.or,[6,13]⟩,⟨.or,[11,14]⟩,⟨.and,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3938511040 * 2 ^ 32 + 3904929792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3938511040 * 2 ^ 32 + 3904929792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12943

open PEqualNP.Outside.L_meta_12943 in
theorem PEqualNP.Outside.L_meta_12943 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3938511040 * 2 ^ 32 + 3904929792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3938511040 * 2 ^ 32 + 3904929792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
