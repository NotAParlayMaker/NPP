import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12925.Model
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


end PEqualNP.Outside.L_meta_12925.Model

namespace PEqualNP.Outside.L_meta_12925
open PEqualNP.Outside.L_meta_12925.Model
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

end PEqualNP.Outside.L_meta_12925

namespace PEqualNP.Outside.L_meta_12925
open PEqualNP.Outside.L_meta_12925.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x210a4c0000040a82000000d5000000006071b000000000004804c0000600000000000ca2180001c0028023520000428000242c0001102740000000903007800b000000000000004000000345d2804e7c0080e3c000000000001000c3810004001ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x621fe40c43fa81887f10310ff98621fe30c43fa61887f0c310ff90621fe20c43fa41887f08310fbaa621f654c43eaa9887d15310fba9e21f653c43eaa7887d14f10fba1e21f643c43ea87887d10f10fba9621f652c43eaa5887d14b10fba1621f642c43ea85887d10b10fb99621f632c43ea65887d0cb10fba0621f640c43ea81887d10310fb98621f630c43ea61887d0c310fb90621f620c43ea41887d08310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff99421fe32843fa65087f0ca10bea8c217551843fe83087f90610fea0c21fc41843fe63087f8c610fe98c21fc31843fe43087f88610fe90c21fc21842fca1087fd0210ff20421fa40843fa81087e50210fe20421ff30843fc61087f4c210fe18421ff20843fc41087f48210fe10421ff10843ee21087ec4210ffaa2217f54443fca8885f95110feaa2217d54443f8a8885f15110ffa9a217f53443fca6885f94d10fea9a217d53443f8a6885f14d10ffa1a21fe43443fa86887f10d10ffa92217f52443fca4885f94910fea92217d52443f8a4885f14910ffa1221fe42443fa84887f10910ff99221fe32443fa64887f0c910ffa0a21f741443fc82887d90510fea0a21f541443f882887d10510ff98a21f731443fc62887d8c510fe98a21f531443f862887d0c510ff90a21f721443fc42887d88510fe90a21f521443f842887d08510ffa0221fe40443f480887f50110fca0221fc40443fe60887f8c110fe98221fc30443fe40887f88110fe90221fc20443fe20887ec4110ff08221f610443eea8887d95110faaa221f454443eea6887d94d10faa9a21f453443ee86887d90d10faa1a21f443443eea4887d94910faa9221f452443ee84887d90910faa1221f442443ee64887d8c910fa99221f432443eea0887cd4110fba0221f640443e480887d50110f8a0221f440443ee60887d8c110fa98221f430443ee40887d88110fa90221f420443fea8085fd5010ff2a0217e54043faa8085f55010fe2a0217c54043fea6085fd4c10ff298217e53043faa6085f54c10fe298217c53043fe86087f90c10fea1821fc43043fea4085fd4810ff290217e52043faa4085f54810fe290217c52043fe84087f90810fea1021fc42043fe64087f8c810fe99021fc32042fca2085d94410ffa0821fe41043fa82087f10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xd42c83da85907f10b20ff99641fe32c83dc65907f4cb20f699641fc32c83fea3907f94720bf28e41fd51c82faa3907f14720ffa0e41fe41c83fa83907f10720ff98e41fe31c83fa63907f0c720ff90e41fe21c83fa43907f08720ffa0641fe40c83fa81907f10320ff98641fe30c83fa61907f0c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ffa1c41fe43883fa87107f10e20bea9441ff42883fc85107f50a20fe21441ff32883de65107f8ca20fe99441fc32883d865107fd4620ff28c417e51883eca3105d94620fea8c417d51883eaa3105d54620fe28c41ff41883fc83107f50620fe20c41ff31883fc63107f4c620fe18c41ff21883fc43107f48620fe10c417e50883fe81107f90220fea0441fc40883fe61107f8c220fe98441fc30883fe41107bc8220fd90441ff54482fea8907f95120bf2a241fd54482faa8907f15120be2a241ff53482fea69077d4d20afa9a41fe53482fca6907f54d20bea9a41fc53482f8a6907714d20ae29a41ff43483fc86907f50d20fe21a41ff42483fc84907b90920fea1241ed42483f884907fcc920ff19241ee32483fa64907b4c920fe19241ff51482fea2907f94520fea8a41fc51482f8a2907fd0520ff20a41fd41483f882907fcc520ff18a41fd31483f862907fc8520ff10a41fd21483f842907fd0120ff20241fd40483f880907fcc120ff18241fd30483f860907fc8120fd90241fe20483dc40907fd5020bfaa041fe54082fca8106f950209f2a041fd54082faa8106f550209eaa041fc54082f8a8107fd4c20bfa9841fe53082fca6107794c20af29841fd53082faa6107754c20aea9841fc53082f8a6107fd0c20ff21841fd43083f886105f94820ffa1041fe42083fa84107f10820ff99041ef32083fc64107f4c820fe19041ec32083fea2107f94420bf28841f651082eca2107f54420bea8841f551082eaa2107f14420ffa0841fe41083fa82107f10420ff98841fe31083fa62107f0c420ff90841fe21083fa42107f08420bf28041ff40083fc80107f50020fe20041ff30083fc60107f4c020fe18041ff20083de40107f88020fd10041fd20083da40107e48020ffaa6217f54c43fca9885f95310feaa6217d54c43f8a9885f15310ffa9e217f53c43fca7885f94f10fea9e217d53c43f8a7885f14f10ffa1e21fe43c43fa87887f10f10ffa96217f52c43fca5885f94b10fea96217d52c43f8a5885f14b10ffa1621fe42c43fa85887f10b10ff99621fe32c43fa65887f0cb10ffa0e21f741c43fc83887d90710fea0e21f541c43f883887d10710ff98e21f731c43fc63887d8c710fe98e21f531c43f863887d0c710ff90e21f721c43fc43887d88710fe90e21f521c43f843887d08710ffa0
  | 2 => 0x3fe84207f90840fea1081fc42103fe64207f8c840fe99081fc32103fea2207f94440bf28881f651102eca2207f54440bea8881f551102eaa2207f14440ffa0881fe41103fa82207f10440ff98881fe31103fa62207f0c440ff90881fe21103fa42207f08440bf28081ff401037e80207f90040fd20081fd401037a80207e50040ffaa6617f54cc3fca9985f95330feaa6617d54cc3f8a9985f15330ffa1e61fe43cc3bc87987f50f30eea1e61fc43cc3fea5987f94b30bf29661fd52cc2faa5987f14b30ffa1661fe42cc3fa85987f10b30ff99661df32cc3fc65987f4cb30ee99661fc32cc3fea3987f94730bf28e61fd51cc2faa3987f14730ffa0e61fe41cc3fa83987f10730ff98e61fe31cc3fa63987f0c730ff90e61fe21cc3fa43987f08730ffa0661fe40cc3fa81987f10330ffaa4617f548c3fca9185f95230feaa4617d548c3f8a9185f15230bea9c61ff438c3fc87187f50e30fe21c61ff528c3fca5185f94a30fea94617d528c3f8a5187fd0a30ff21461fd428c3f885187fcca30ff19461de328c3fa65187f0ca30ee19461ff518c3fca3185f94630fb28c6176518c3faa3185f54630faa8c6175518c3f8a3187fd0630ff20c61fd418c3f883187fcc630ff18c61fd318c3f863187fc8630ff10c61fd218c3f843185f94230ffa0461fe408c3fa81187f10230ff98461df308c3f661187fd5130bfaa261fe544c2fca8987f55130beaa261fc544c2f8a8987fd0d30ff21a61de434c3fa86987750d30fe21a61ff524c2fea4987bd4930b7a9261fe524c3faa4987f14930be29261ec524c2d8a4987fd0930ff21261fd424c3f884987fcc930ef99261fe324c3fa6498774c930fe19261ff514c2fea2987f94530fea8a61fc514c2f8a2987fd0530ff20a61fd414c3f882987fcc530ff18a61fd314c3f862987fc8530ff10a61fd214c3f842987fd0130ff20261fd404c3f880987fcc130fd98261fe304c3bc60987fd5030bfaa061fe540c2fca8186f950309f2a061fd540c2faa8186f550309eaa061fc540c2f8a8185f94c30ffa1861fe430c3fa86187f10c30ffa9061fe520c2fca4187b94830b729061fd520c2faa4187b54830b6a9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830ef19061fd320c3f86418770c830ffa8861fe510c2fca2187d94430bb28861fd510c2faa2187d54430baa8861fc510c3fe82187f90430fea0861fc410c3fe62187f8c430fe98861fc310c3fe42187f88430fe90861fc210c2fca0187fd0030ff20061fd400c3f880187fcc030ef98061fe300c3f460187f4c030ee98061f9300c3fea9905fd5320ff2a6417e54c83faa9905f55320fe2a6417c54c83fea7905fd4f20ff29e417e53c83faa7905f54f20fe29e417c53c83fe87907f90f20fea1e41fc43c83fe85907f90b20f721641f
  | 3 => 0x8710ff90e21fea1c43fc43886faa510ffd0a21ff21443fd42887f88510ffcca21ff19443fd32887f86510df94621ffa0c43fe41887fa8310ff10621ff98c43fe31887fa6310ff0c621ff90c43ef21887ee4310ffd4221ff284437e50887faa110df54221fe28443ff54486fea890ff95121bf2a243fd54486faa890ff15121be2a243ff53486fea690ff94d21bf29a43fd53486faa690ff14d21be29a43ff43487fc8690ff50d21fe21a43ff42487fc8490fb90921fea1243ed42487f88490ffcc921ff19243fd32487f86490ffd0521ff20a43fd41487f88290ffcc521ff18a43fd31487f86290ffc8521fb90a43fe21487dc4290ffd4121bfa8243fe50487faa090ff14121be28243ff54086fea810ff95021bf2a043fd54086faa810ff15021be2a043ff53086fea610ff94c21bf29843fd53086faa610ff14c21be29843ff43087fc8610ff50c21fe218437e52087fe8410ff90821fea1043fc42087fe6410ff8c821fe99043fc32086fca210ffd0421fba0843fe41087fa8210ff10421fa20843ff31087fc6210ff4c421fe18843ff21087de4210ff88421fb10843fd21087da4210fd48421ffa8043fe50086fca010ff54021bea8043fc50087fea7a07f94f40bf29e81fd53d02faa7a07f14f40ffa1e81bf43d03fc87a07f50f40dea1e81fc43d03fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681bf42d03fc85a07f50b40dea1681fc42d03fe65a07f8cb40fe99681fc32d03fea3a07f94740bf28e81fd51d02faa3a07f14740ffa0e81fe41d03fa83a07f10740ff98e81fe31d03fa63a07f0c740ff90e81fe21d03fa43a07f08740beaa481ff53903fca7205f94e40fea9c817d53903f8a7207fd0e40ff21c81fd43903f887207fd4a40ff294817e52903faa5205f54a40fe29481ff42903fc85207f50a40fe21481ff32903fc65207f4ca40fe19481ff51903fca3205f94640fb28c817651903faa3205f54640faa8c817551903f8a3207fd0640ff20c81fd41903f883207fcc640ff18c81fd31903f863207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681207fd4d40bfa9a81fe53503faa6a07f14d40be29a81ff435037e86a07f90d40fea1a81bd43503f886a07fd4940bfa9281fe52503faa4a07f14940be29281ff425037e84a07f90940fea1281bd42503f884a07fcc940ff19281fd32503f864a07fd4540bfa8a81fe51503faa2a07f14540be28a81ff41503fc82a07f50540fe20a81ff31503fc62a07f4c540fe18a81ff21503fc42a07f48540fe10a81ff40503f680a07f90140df202817e54103fea6207f94c40bf29881de53102bca6207f54c40bea9881dd53102baa6207f14c40ffa1881fe43103fa86207f10c40ffa9081fe52102fca4207b94840b729081fd52102faa4207b54840b6a9081fc521
  | 4 => 0xff14941be29283ff42507fc84a0ff50941fe21283ff32507fc64a0ff4c941fe19283ff41507ee82a0ff90541df20a83ff50506fea0a0ff94141fea8283fc50506f8a0a0df95041ffa9883fe53106fca620f794c41af29883fd53106faa620f754c41aea9883fc53107fe8620ff90c41fea1883fc43107fea420ff94841bf29083ee52106dca420ff54841bea9083ed52106daa420ff14841ffa1083fe42107fa8420ff10841ff99083fe32107fa6420ff0c841bf28883ff411077e8220ff90441fb20883fd411077a8220fd50441ffa8083fe50106fca020fe94041bd28083fd50106faa020fe54041bca8083fc50107fea998dfd5331ff2a6637e54cc7faa998df55331fe2a6637c54cc7fe8798ff90f31ef21e63fd43cc7ba8798ff10f31ffa9663fe52cc6fca598ff54b31bea9663fc52cc7fe8598ff90b31fea1663fc42cc7fe6598ff8cb31fe99663fc32cc7fe8398fdd0731ff20e63fd41cc7f88398fd10731ffa8663fe50cc6fca198ff54331bea8663fc50cc7fea918dfd5231ff2a4637e548c7faa918df55231fe2a4637c548c6faa718ffd0e31ff21c63fd438c7f88718ffd4a31ff294637e528c7faa518df54a31fe29463ff428c7fc8518ff50a31fe21463ff328c7fc6518ff4ca31fe194637e518c7fe8318ff90631fea0c63fc418c7fe6318f7cc631fb98c63ff508c7fca118df94231fea84637d508c7f8a118ffd5131bfaa263fe544c6fca898ff55131beaa263fc544c6f8a898ffd0d31ff21a63de434c7fa8698f750d31fe21a63ff524c6fea498ff94931fea9263fc524c6f8a498ffd0931ff21263fd424c7f88498ffcc931ff19263fd324c7f86498ffd0531ff20a63fd414c7f88298ffcc531fb98a63fe314c7bc6298ffd4131bfa8263fe504c7faa098ff14131be28263ff540c6fea818ff95031bf2a063fd540c6faa818ff15031be2a0637e530c7fe8618ff90c31fea1863fc430c7fea418ff94831bf29063fd520c6faa418ff14831ffa1063fe420c7fa8418ff10831ff99063fe320c7fa6418ff0c831bf28863ff410c7ee8218ff90431fea0863fc410c7e88218ffcc431ef98863fe310c7ec6218ff4c431ee98863f5310c7fea018ff94031bf28063fd500c6faa018ff14031ffaa6437f54c87fca990df95321feaa6437d54c87f8a990df15321ffa9e437f53c87fca790df94f21fea9e437d53c87f8a790df14f21ffa1e43fe43c87fa8790ff10f21ffa1643fe42c87dc8590ff50b21f6a1643fc42c87fe6590ff8cb21fe99643fc32c87fe8390fdd0721ff20e43fd41c87f88390fd10721ff98e43fe31c87fa6390ff0c721ffa8643fe50c86fca190ff54321bea8643fc50c87fea910dfd5221ff2a4437e54887faa910df55221fe2a4437c54887fea710dfd4e21ff29c437e53887faa710df54e21fe29c437c53887fe
  | 5 => 0xe42bf29c85fd5390afaa7217f14e42ffa1c85fe4390bfa87217f10e42bf29485ff4290b7e85217bd0a42ffa8c85fe5190afca3217f54642bea8c85fc5190bfea1217f94242bf28485fd5090afaa1217f14242ffa9a857f5350bfca6a17f54d42fe29a857c5350bfe86a17f90d42fea1a85fc4350bfe84a17bd0942ff21285be4250bfea2a15fd4542fba8a85775150bfca2a17f54542fe28a857c5150be8a2a15d14542ffa82857f5050bfca0a17f54142fe282857c5050afca8217fd4c42ff298857e5310bfaa6215f54c42fe29885ff4310bfc86217f50c42fe218857e5210bfe84216fd0842ff21085ee4210bfa84216f50842f6a1085ff5110bfca2215f94442fea88857d5110bf8a2217fd4042ff280857e5010bfaa0215f54042fe28085ff54ccafea9997f95332bf2a665fd54ccafaa9997f15332be2a665ff43ccbfc87997f50f32fe21e65ff42ccbfc85997b90b32fea1665ed42ccbf885997fd4732ff28e657e51ccbfaa3995f54732fe28e65ff50ccbfca1995f94332fea86657d50ccbf8a1997fd5232bfaa465fe548cafca9197f55232beaa465fc548caf8a9195f54e32ffa1c65fe438cbbc87197f50e32eea1c65fc438cafca5197fd0a32ff21465fd428cbf885197fcca32ef99465ef328cbfea3197f94632bf28c65fd518cafaa3197f14632ffa8465fe508cafca1197f54232bea8465fc508cbfea8995fd5132ff2a2657e544cbfaa8995f55132fe2a2657c544cbfe86997f90d32fea1a65fc434cbfe84997f90932fea1265fc424cbfe64997bcc932ff19265de324cbfea2995fd4532ff28a65fd514cbf8a2995f14532ffa82657f504cbfca0997f54132fe282657c504cbfea8195fd5032ff2a0657e540cbfaa8195f55032fe2a0657c540cafca6197fd0c32ff21865de430cbfa86197750c32fe218657e520cbfe84197f90832f721065fd420cbda84197f10832ff99065df320cbfc64197b8c832fe99065dd320cbda6419734c832ffa8865fe510cafca2197f54432bea8865fc510cbfea0197f94032bf28065fd500cafaa0197f14032ffa9e83fe53d06fca7a0ff54f41bea9e83fc53d07fe87a0ff90f41fea1e83fc43d07fea5a0ff94b41bf29683fd52d06faa5a0ff14b41ffa1683fe42d07fa85a0ff10b41ff99683fe32d07fa65a0ff0cb41ffa8683fe50d06fca1a0ff54341bea8683fc50d06faa920ffd4e41ff29c837e53907faa720df54e41fe29c83ff43907fc8720ff50e41fe21c83ff52907fca520df94a41fea94837d52907f8a520ffd0a41ff21483fd42907f88520ffcca41ff19483fd32907f86520df94641ffa0c83bf41907ee8320ffd4241ff284837e50907faa120df54241fe28483ff53506fea6a0ff94d41fea9a83fc53506f8a6a0ffd0d41ff21a83fd43507f886a0ffd4941bfa9283fe52507faa4a0
  | 6 => 0xa00c00200403601800c02c01600001401200c01600000200200a00002c00000800201200e02802e02000001e02800600600201200200202c00000200601400c00000601600400400a01a00406a02a01000602000200001201400800001000c00200000a00402001a00a01000000000200803000001c00400200400600000400800400000400000400602c03000403e00200a00401400000000000800001e00601001000000800400400002201c00800000201200200a00602c0320020040100020080060000000b000600400404200000601800402c02000200c00400c00000a00600800800800405000e00200400400601000e00600600c00401200400800400001200800000003e00800000000200002c00600a00600402000601000a01e00400000802000000000a02a01201800400200400400400800800000a00800000400000600600a00203e00003601001000000001400004400000e00001201201c00600000000000003600a00e01a01600000400800c00200600200000203c00200800c00000200000001400000200200000c00400c00200200800600000000200001e01c00201000600400400400c00200802600001000403400200200002601000000a00600000400400000000600e01800000000000800000200000200200400600000000a00c03200611402007600800000000800201a00800e00400001600200000000200401800200002c00601201202400400600400000004001400a00600c00601600001200200000402e03000000600000a01a02000601000a000002002004000000000006002000000006006000002001ff52d0ffca5a1df94b43f7296876e52d0ffaa5a1df54b43f6a96876d52d0ff8a5a1ffd4743ff28e877e51d0ffaa3a1df54743fe28e87ff50d0ffca1a1df94343fea86877d50d0ff8a1a1df55243bf29c87ff4390f7e8721f7d0e43ffa9487fe5290efca521ff54a43bea9487fc5290ffea321ff94643bf28c87fd5190efaa321ff14643ffa8487fe5090efca121ff54243bea8487fc5090ffe86a1f7d0d43ff21a87be4350ffea4a1dfd4943ff29287fd5250ff8a4a1df14943ffa8a877f5150feea2a1ddd4543ff28a87fd5150ff8a2a1df14543fa28a87745150ffea0a1dfd4143ff28287fd5050ff8a0a1df14143bf2a0877e5310ffe8621efd0c43ff21887de4310ffa8621ef50c43eea1887ff5210ffca421df94843fea90877d5210ff8a421ffd4443ff288877e5110ffaa221df54443fe28887ff5010ffca021df94043fea80877d5010ff8a021ffd4f42ff29e857e53d0bbca7a15794f42fea9e857d53d0bbaa7a15754f42fe29e85ff43d0bfc87a17f50f42fe21e85ff51d0bfca3a15f94742fea8e857d51d0bf8a3a17fd4342ff286857e50d0bfaa1a15f54342fe286857d5490bfea7217f94
  | 7 => 0x1135448c34000fa4d3d1a40000002880419d8749550b3073cfe8348000001d05b44818bb0ca106ce80000a8c284d1d9d5b25420e08e101793f57f000149caccefc564464324000000f283cdc65bc4f70001ad0001e0cf5db792a5e4caf82d113112cc14415769ac80008498744a5995af8001cf8720001b4c001d60000000000000ec800167da65275255844000000001ad9c2146c4e04e40000009a400000000009d34c3900000019b8d5c678754000000e15a888fd3b0e007f8bf4df8001809514f457c80018100018dd3d47a0e64f20001a589b85d04b4424001d340016b40007946e40007bd938000000384000810000000b04961bac0012d40000000006019642d8badd64f68000f24001cd52d1a48d7563ca35b60995dd420c208b380000907293f8dd12255dcae8ce0b5d4794a10e40017187dc974fa00105345e000023423144000142d5a40003a014d72db1c1fd09514cc79d10000000001ab806dc14000000444254da8251860f34379471c6cf61e01c40b35e5d8bc00129182c000001a6ced12289a05488c09cccc8ac00016300014249fc0e9ba1178000000ef5b8d428034e886ddb40000000354000000919b200140195a8aa896400000077509db848e057021c219b2d285a816c5398664d857ed605df8770c6d664001684ac8ecc0004385280018302f40010b0000000e2c315c756a5569a001f524dd4c2f9e39be8d3800127d619d50ee4000658d55704c21d5c0017a19f8144000e7801c0004fc000d700004f9c2c0d932400139d94941d11000110dc580002a81915c0fbcfc4751b4800003dc28000000d880000c8654b00af4cf154c4a9711c34f4d9ec99c07408882022c0016f42fc419a11288e209c91d4834450544229db46f0d9dd99a694fc00000401001a02200800400400000001800200200600000600201600200e00000000600600200000000003000009001a01000c00001200600200203201602600e00600000003400800000601800801000000e00800400000c00000000000a00000c02201a00800400001a00201e00800200e00001c01600000800400000000c00001200600c00200204402200800800000e01801c00400200a00400800000000201400c00003200600001400002c01400600000200000a00600001c01800002401000000000000600201202600000405e00e00000e01e00000000000600000c00400a00203c01200000801000200000200200600800000000000001000000200801c00000000a00401400002800405c01a00e08200200600400000600e01200001c00200201000000200200402600c00600600801a00000000801200400400000600000001000e00c00200200000200200000000000000a00400000200000800400000000c01800c00400000000200000200000200000000401e
  | 8 => 0x19a08ad61dc05654e40c084c8628000670000000b700004cd2802c4be06ac42c11c1cd451bf04f00001a0000784f00c1d3800010c9d0d018f394f84f4bfd89506800144ddb83449b16bc4bc3d8f049f05a8294180c2c691aa17502edaa98d41b40c00d1e59029ba4510e8d1051c549051535c5983a8000cd8000000000000001c805f4000000dc4108328feca69c8d68da78b840012c07897b098c000000064abd3205bc82400060800122ca9400000000134994c5e8c110711f8761d003b84d8e7d010fd08f44dddbd8680009e4000a38dd80012055c40006190a4bc54ed670db8001b910b92789217f599000157d4ccde9b5400034c001e5505558d258b980012bdc0984c001adc001780e0c000000e05078001170ea5e05765115bbcbb9bb54d0a611f4001779520ca45680005fc904000000d817b55b8469814001908001050b140009c4099578ad93c8b88000a10c94dcd11c4ec6e80f13a00943e0f08868860c1971599cdf50a0dfc8ccee97484e96d16cda55368001e11bf8f7db11e3540c2781705547b1378000000bc867c000fac458001a50fb4001b00380a5c001a30000000dac0002bccacb4419d33837ceac00000097800163800130800196c8bd0b5721360e693b43fc000740000000105365d3d589634299c48604d995700015040000ac001aa4dd57cc27c000174000e5c000000001cc8001e64874ce4000c75558000000c705311bc3c80295e151cb6d02c000c3c441ab46f586583932d678c44cf80014d80014e590052c43c000cdc9c1209464bb4000000d089ed15d7b896947c0017300000018b070c000001a18000001250b480003089d40c5239218e8559000000165907dd317f8858c54c4d4d4660b25a2c8500015d000092d519d243dd8190cc00010c2c88dda85a74051a09dd865c00000000045c55d330000f3c00000170c000e29c78ceceedb6dc0daec0008958588f81d01200003ac47979ce2515058566caece74b0849c000ae0940c8400130040dacc0003397980000000019400007a80019a8da537d93dcfc000ebc3347c5770000001128f58c591d80000000000013ac688d94000621469319afdb0c48d3fdcdc5ad7d96f0d7825c25800138d2a9039959bed98d8b58a9b30b55885bfc4856ed68089859c00004c5c80009d0000c044c4cf50fc0000006b09880000f59f12b80004c0000000b797397410980009000014880000008b01298f01d987dba8000a80a51a440cce54934a59e08000001454000001a4c0000000014e80007801f98ac0000000003e41489587e52951a934553003129c2b0a04f1cfe5a70a40001ab1064084540e91d380805f03b4000a48f0c7190d9024000000ef0000060000000000000b58b69ca516c000930dc0001400a8472dcc00018e56689bd9687d43118ecd419812f07118f51480
  | 9 => 0x3885a152dc258240015356b1e3cb4000011400075965125c80d82023d561248238ac40a4001c94001640734ab4000001439434000000ce8001d58fb8000001a140000000001999987c0fc00015b497d929009a609e07a4914bd1cbd8d9a993882b40001e13841306d4c7c2801c4a1838c4481557c1dd0ed92c885c8540005905380000017dc00174d32890c7ed644e49da8b0c9287e1ce89a80012f4001d91e319c4000000948d64001e1c000890001b04e3dc680000016d4f855fc6c5b19cd1c1c9389f9b9c62d69417cc8028d1c8f55b74cc508daf491c001d08119e241c862453d10000149488466844d108000d51e606a18a4000ea002447457c24950c138880e307001e9800d254f54f01882a128c1a82d5125ac1cc5a29c50b8c00000047c24dd950314c57a400068c58c3057acf2c159ddc1ed1800019a42610f876413c6d16a12e40011399503d400000000066c000000a7c07c0000000000010f0000838e980007980006c0000d2ccb5cad3d800123d0a8af143da208b586c244e342411187f1898778944fe16f89900018880000fc0000018b97a800000174474436402d2659550156dd17d0f4800b916250ec2dd77562175c0001ad5bd499da1ad44990d04089240019b40015e80012319257e1554000a70000044000000001880000000ff800000171c00000030c0011b80000000016fc0005b13e15c871c5c0b194b8769168000c30000a24fd4000001175d150c0001688e94001c1851851c001da432d528aada9c001c70b10000b2c0011e5850000f313cc9dd4adb157e87b9d68d1997d414f91dc11c1121d707d0b3d8e9c108089e94181341e49708a0699040d48d91de84a0001c900004115e4eb079d758840001d491b5c980013a4b9c96cec461c000db4879430001460000bf800155c9f415c2658fc001e288d0cbc4284b98c99e1c5db50ea9d9d2fd5d4dec9d8c913e8000194b213b88e82ac00000177c5a4000d4c48983d788ed483d7845511b1d6c5cde2d3501500015f0000001d74001aac0000001c1890a91158df0000000ad00000014a4001dac0000011540005b400121cab15119e45e5c30000001198000000000a2c001cb8000eb82e17fc0018e1c39d216d95255a0bbc000594a64ba0db1601005091e491ac00000000126c4800000018480009b4f99d7c055975481c4dbe03f8214000804211829dcd2dcfccff11cd698b29bb8bdcc38e710e8c41bb1194000a280688c4a9d700001e41ce5bc004920c000001c4400000141140950948cf400019bd73c00033c6d8000f959897d40000000000795940009100008e5390000000001080a6cc50c480000003500011f0000001e152455b03319212e0ec14a9314558000101b7181c0018c000068556cb740a887d5740006c9cedaf000000036000104c00005c580d0c00063
  | 10 => 0x28420000a0c46180d804270f48168e4c6b450d191299649b5d6152ed6108d400026c164001ae4a20c610d4000000000f78000000001b88a00520000430d456ad548000998000b1c89c000000a31c88000000000001a0c8c930c001374f8d9dc2c05ddb293700b0c25e69ca8f6db812a198467595cf9c8a83985005058f8291b65bd00ede443a461403800000ce61c0064c000de4001bc88b9ae89502e9bf518cc69a8d565260000000000000000eb40019aca140019d08308ed7c4e1800008cd358401d4644ffc124da1341dc80000018d09800000000013d0318000000000001a3c6107919b0f8178cf140000000d40000000014c0000001b3ccfc0000019cc0e17bc001bd80012f97286f8d6cde1061b7c0014e0adc0003740dc0000016c0001a7cab8bece44000ccd6c800133591c3bc0003f054d62c724984f504552d80000000016e094c200204001609df565c00041d1604ac000001db100c88ca1c00167400095d76c8d80b88882f000000000000000000169da34b6070988cbd4000000574000c64058000470000000000525000434001220f880016b8d153040000018c5c6131c000ca836c00164d1658a1c8446c36856db68000afc0006e05d8a552cc000a4c000d2153800189c0000000000012400011ed020000340000000cd000153d035b942b95d947469c6ec000d680000000000011fca3c000fc86500012aca78d04001b35048000a4477d7d0001268a746cc110c5cd28edc7f51e0cc06803ece1cd004d04d43c4aa1a959e9581c553945782a4fdc18d0595f9dec0015ed189790c0ce6cfd8bd91dcd61bcdbd50add4592cff46bc7c802058812dd89d816900001dc0b400084dd78000c8c93c000000b7c0000000000000013dc8700019713593c154400000076d944000220224a8800000145903c29c184b4c81d6e4300e9db39185754000000000001311979de1cb000064000000136c00039c0005f88f1734cb01f06380016a873160da900001417e5234f10b80000000001708000001cd8000dc8f652e8000001d8dd84909b999c913cba51411e95cd45c0005ec0e40019313e52b47e90c43d06fcc98000000001ccda24b51a4101c6a92c58344944047ac001b08000000001854000000a094c8ee0be99106942cc6b80000000010ddd1d044000f191a12b00001a4001a1c001dc4865bdc16d5f47d9cf576086cae42754bc0014dce50e38000d100bca98000f7400000074cd300000000003f40013a9ac4c010745b8d588a519c001b599190bd8700f8000000d7d85d270001ca0001e500a1a389ac705ae0bcc0053540092147fc000be4ba990478d3bd1d1879ce133c0000000012100013ec00000075c739a04b9482dbe559d9f4000dbddfc1600002698ccd8d0890854b1599a5ccb99fc0000000000015ac0001bc1b8aa4000648
  | 11 => 0x1abdd280013c460cfb0b6514431d794ad43b0815445d559354b463dc3de18635541404070955c9cfa835dcb4bc190c5c4844ddccd5200370001660c88000000001df0001e219c1d2d960321c7d0e05d5724ef96294847cc2e44004903941b1585de45615000003c1d196e8c9ce5905dd403e86a40013f1cf0bf07144b0c299145087b43588
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe51043754394410dd10e51043776294410dd98a51043756294410dd18a51043774294410dd90a51043754294410dd10a51043773294410dd8ca51043753294410dd0ca510427d65d0410dd947410427f65904109f596410433e5490410cf55241043765190410be98241042f960904109fd95410437651504109fd94410427d6510410cf950410433d5410410b798c41042dd6310410bb98841042ed6210410dd94441043b54110410be98041042f960104109f597310437651cc4109fd96310427d658c410d794e310435d538c410dd94631042fa608c410be582310427f654c410dd945310427f650c4109f594310435e530c410d754c3104376510c410be98031042f9600c4109f597210437651c84109fd96210427d6588410db94a210436d5288410dd94621042fa6088410be582210427f6548410dd945210427f65084109f594210436e5208410db54821043765108410be98021042f960084109f992500427d64940109f98e500427d63940109f98a500427d62940109f586500427561940109f597400437651d00109fd96400427d6590010cf952400433d5490010bd98640042f56190010dd946400437a50900109fd9540043765150010de941400427f65100109f994400427d65100109f194400433e5410010cf55040042de6310010b758c40042ee6210010bb58840042f66110010bd584400437651100109f597300437651cc0109fd96300427d658c010d794e300435d538c010bd98630042f5618c010dd946300427f654c010bbd8930042ec624c010dd945300427f650c0109f994300427d650c0109f19430042be640c010af590300435e530c010d754c30042ee620c010bb58830042f6610c010bd5843004376510c0109f597200437651c80109fd96200427d6588010db94a200436d5288010bd98620042f56188010dd946200427f6548010b7d8d20042dc6348010dd945200427f65080109f994200427d65080109f19420042be6408010af59020042de6308010b758c200436e5208010db54820042f66108010bd58420043765108010dd597100437754c4010dd953100437554c4010dd153100437753c4010dd94f100437553c4010dd14f100437752c4010dd94b100437552c4010dd14b10042f56184010dd94610042f96584010de59610042796584010ded5210043795484010be586100437a5184010fc946100427f6544010dd94510042f76544010ddd9510042776544010ddd5110043765444010dd55110043745444010ddd4d10043765344010dd54d10043745344010ddd4910043765244010dd54910043745244010bdd8110043765044010fc90110043f14044010bed95100437b65440109ed95100437b5444010de55110042fb6144010fcd85100437a5144010fc94510043725144010fc90510043f14144010
  | 1 => 0x42dd6315010bb98854042ed62150109f990540433e64150109f98c540435e63150109798c540427d6315010d758c540425d63150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109d984540427e6015010de980540427a60150109f993530427d64d4c109f98b530427d62d4c109f987530437661d4c109d987530427e60d4c10de983530427d6594c10d7d4e530427e6494c109f592530427e6294c109f58a530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c109fd81530427d6054c10af99053042bd6414c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530427e6214c10db988530426e6214c109f588530436d6214c109b588530427e6114c10dd98453042766114c109f980530437a6014c109fd97430427e65d0c109f597430427c65d0c10cf953430433d54d0c10bb98b43042ed62d0c109fd96430427e6590c109f596430427c6590c10d794e430435d5390c109fd95430427e6550c109f595430427c6550c10cf951430433d5450c10d794d430435d5350c10bdd8543042f46150c109fd94430427e6510c109f594430427c6510c109f993520427d64d48109f98f520427d63d48109f987520437661d48109d987520427e60d4810de983520427d6594810dbd4a520427e64948109f592520427e63948109f58e520427f64548109f191520427f63548109f18d520436f62548109fd85520427d61548109fd81520427d6054810af99052042bd6414810b798c52042dd6314810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520427e6114810dd984520427661148109f980520437a60148109fd97420427e65d08109f597420427c65d0810cf953420433d54d0810b798f42042dd63d08109fd96420427e65908109f596420427c6590810db94a420436d52908109fd95420427e65508109f595420427c6550810cf951420433d5450810db949420436d5250810bdd8542042f461508109fd94420427e65108109f594420427c65108109fd97320427e65cc8109f597320427c65cc810d794f320435d53cc8109fd96320427e658c8109f596320427c658c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810d794d320435d534c810db949320436d524c8109fd94320427e650c8109f594320427c650c810f34c8320427e64944109f592510427e63944109f58e510427e62944109f58a51043776494410dd99251043756494410dd19251043776394410dd98e51043756394410dd18e51043774394410dd90
  | 2 => 0x64cc110bd19330443d753cc110f514f30443d643cc110f550f30442f662cc110bd58b30443d732cc110f54cb30443f350cc110fc90330443f140cc110bd9963044376658c1109d99630442f7648c110bd99230442f5648c110bd19230442f5638c110bd98a30442f5628c110f58ca30443d4328c110bd98230443f3508c110fc90230443f1408c110f5cc230443f3308c110bdd9530442f6654c110bd59530442f4654c110bdd9130442f6644c110bd59130442f4644c110f5d4d30443d4534c110f590d30443d5434c110bdd8930443e7624c110b9d8930442f4624c110f918930442e4624c110f5cc930443d5324c110fcd4130443f2404c110fc50130443f3304c110f58c130442f6650c110dd9943044276650c110bdd9030442f6640c110ed99030442b6640c110bd59030443b5640c110ad59030442f4640c110bd98c30442f6620c110f998830442e6620c110bd58830443e5620c110b958830443d6320c110f50c830442f6600c110fcd4030443f2400c110fc50030443d7300c110fc8c030443d5300c110fc4c030443d1300c110bd99720442f465c8110bdd9320442f664c8110bd59320442f464c8110bdd8f20442f663c8110bd58f20442f463c8110f9d4b20443e452c8110f990b20443e542c8110f98cb20443e532c8110fcd4320443f240c8110fc50320443f330c8110fc0c320442f66588110dd99620442766588110bdd9220442f66488110bd59220442f46488110bdd8e20442f66388110bd58e20442f46388110bd58a20443e73288110f90ca20442f66088110fcd4220443f24088110fc50220443f23088110fc4c220443e72088110fcc8220442f76548110bd99520442f56548110bd19520442f76448110bd99120442f56448110bd19120442f76348110f5d8d20442d76348110bd98d20442f56348110bd18d20443d46348110b518d20443e75248110f914920443e64248110f950920443e63248110f94c920443f35048110fc90120443f14048110fc8c120443f13048110fcc8120443e62048110bd994204437665081109d99420442f76408110bd99020443b66408110ad99020442f56408110ed59020442b56408110bd19020442f76308110bd98c20443d66308110b598c20442f56308110f558c20442d56308110bd18c20442f66208110f9cc820443e43208110bd98020443f35008110fc90020443f14008110fccc020443f03008110f9c8020443f22008110f948020443f12008110f8480204427e63d50109f58f540427e62d50109f58b540427e61d5010dd987540427661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d6295010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540427f60550109f581540433d5415010b798c540
  | 3 => 0x910f98c832443d5320c910f94c832443c5320c910bd98032443f2600c910bc98032442f5600c910fc58032442f1600c910bd99350442f564d4110ddd53504437654d4110dd553504437454d4110bd98f50442f563d4110ddd4f504437653d4110dd54f504437453d4110bd98b50442f562d4110ddd4b504437652d4110dd54b504437452d4110dc99750443f364d4110fc99350443f164d4110bc59350443f064d4110fcd5350443f254d4110fc55350443f054d4110fcd8f50443f263d4110fc58f50443f063d4110fcd4f50443f253d4110fc54f50443f053d4110fcd0f50443f243d4110fc50f50443f043d4110fcd8b50443f262d4110fc58b50443f062d4110fcd4b50443f252d4110fc54b50443f052d4110fcd0b50443f242d4110fc50b50443f042d4110fcccb50443f232d4110fc4cb50443f032d4110bd99740442f465d0110edd5340443b454d0110bd98f40442f563d0110edd0f40443b543d0110bd98b40442f562d0110edd0b40443b542d0110fcd4340442f66590110dd99640442766590110bd59240442f66390110bd58e40442f66290110bd58a40442f66090110fcd4240443b74090110fcd0240443f26590110bc99640443726590110bc59240443f35490110fc95240443f15490110fc15240443f36390110fc98e40443f16390110fc18e40443f35390110fc94e40443f15390110fc14e40443f34390110fc90e40443f14390110fc10e40443f36290110fc98a40443f16290110fc18a40443f35290110fc94a40443f15290110fc14a40443f34290110fc90a40443f14290110fc10a40443f33290110fc8ca40443f13290110fc0ca40442f76550110bd99540442f56550110bd19540443b75450110ed15140442f76350110bd18d40443b74350110ed50d40442f76250110bd18940443b74250110ed50940443f35050110fcd0140443b64050110fc99540442f26550110fc19540442f06550110fcd9140443b36450110fcd5140443b35450110fc95140443f15450110fc15140443b05450110fcd8d40443f26350110fc58d40443f06350110fcd4d40443f25350110fc54d40443f05350110fcd0d40443b34350110fc90d40443f14350110ec50d40443f04350110fcd8940443f26250110fc58940443f06250110fcd4940443f25250110fc54940443f05250110fcd0940443b34250110fc90940443f14250110ec50940443f04250110fccc940443f23250110fc4c940443f03250110bd994404437665101109d99440442f66410110bd98c40443d66310110b598c40442f56310110f558c40442d56310110bd98840443e66210110b998840442f56210110f958840442e56210110bd98040442f26010110fcd4040443b74010110fc90040443b54010110fc50040442f665cc110bd19730442f764cc110bd99330442f5
  | 4 => 0xd19543443746550d109d19543443d65350d10f554d43443d74350d10ed90d43442f76250d10bd18943442f76050d10bd18143442f76510d10bd99443442f56510d10bd19443442f66410d10edd5043443b45410d10bd98c43443d75310d10f514c43443b74310d10f590c43443b54310d10f550c43442f66210d10bd58843442f66010d10fc98043442f26010d10bd58043443f16010d10bc58043442f664d4910bd59352442f663d4910bd58f52442f66494910bd59252443765494910dd15252442f66394910bd58e52442f66294910ddd4a52443e75294910bd58252443f16094910bc58252442f76454910edd9152442b76454910bd19152443b46454910ad19152442f76354910f5d8d52442d76354910bd18d52443d46354910b518d52443e75254910dd94952442f76054910fcd8152442f36054910bd99452442f66414910bd59052443765414910dd15052442f66314910bd58c52443775214910f994852443755214910f954852442f765d0910bd99742442f565d0910bd19742442f663d0910f598f42442d663d0910bd58f42443d563d0910b558f42443e752d0910f914b42442f660d0910fc98342442f260d0910bd58342443f160d0910bc58342442f76590910bd99642442f56590910bd19642442f56490910edd5242443b45490910bd98e42442f56390910bd98a42443e65290910f954a42443b74290910f9d0a42442f66090910bd58242442f76550910ddd9542442776550910bd99542442f56550910bd195424437465509109d19542442f76350910bd18d42443e65250910f954942443e74250910ed90942442f76050910bd18142442f76510910bd99442442f56510910bd19442442f66410910edd5042443b45410910bd98c42442f56310910bd98842443e75210910f914842443b74210910f990842443b54210910f950842442f66010910fc98042442f26010910bd58042443f16010910bc58042442f765cc910bd99732442f565cc910bd19732442f764cc910bd99332442f564cc910bd19332443e752cc910f914b32443e642cc910f950b32442f660cc910bd58332442f7658c910bd99632442f5658c910bd19632442f7648c910bd99232442f5648c910bd19232442f5638c910f5d4e32443d4538c910f590e32443d5438c910bd98a32443d7328c910f9cca32442f6608c910bd58232442f7654c910bd99532442f5654c910bd19532442f7644c910bd99132442f5644c910bd19132443e7324c910f58c932442f7604c910fcd8132442f3604c910bd18132443f0604c910bc18132442f7650c910bd99432442f5650c910bd19432442f7640c910bd99032442f5640c910bd19032442f6630c910f5d4c32443d4530c910f590c32443d5430c910bd98832443e7520c910f914832443e6420c910f950832443d7320c
  | 5 => 0x40442f56110110be980404427e65cc110d7d4f304435c53cc110bd98730442f561cc1109f99630442f6618c110bd586304427f654c1109f595304427c654c110d7d4d304435c534c110bbd8930442ec624c110bdd8530442f4614c1109f99430442be640c110af59030442ee620c110bb58830442f6610c110bd58430443d9300c1109f997204436f52c8110db14b20442f661c8110bd587204427e6588110bd98620442f561881109fd95204427d65481109f19520442df6348110b718d204436f5248110db14920442f76148110bd185204427e6508110af99020442bd6408110b798c20442dd6308110bd98420442f56108110fa48020442fb64c4110be59310443f341c4110fc90710443f141c4110fc10710443f331c4110fc8c710443f131c4110fc0c710443f321c4110fc88710443f121c4110fc08710442f76484110bd99210442f56484110bd19210442f76384110bd98e10442f56384110bd18e10442f76284110bd98a10442f56284110bd18a10443f35084110fc90210443f14084110bd98f54442f563d5110bd98b54442f562d5110fcd8354442f66495110ddd5254443b75495110bd98e54442f56395110bd98a54442f56295110bd58254443f16095110bc58254443b75455110dd95154442f76355110f5d8d54442d76355110bd18d54443d46355110b518d54442f76255110f9d8954442e76255110bd18954443e46255110b918954442f76055110fcd8154442f36055110bd99454443775415110ed95054443755415110ed55054443355415110bd98c54443d66315110b598c54442f56315110f558c54442d56315110bd98854443e66215110b998854442f56215110f958854442e56215110fc58054442f664d4d10bd59353442f662d4d10bd58b53442f66494d10bd59253443765494d10dd15253442f66394d10ddd4e53443d75394d10bd98a53442f56294d10bd58253443f16094d10bc58253442f76454d10edd9153442b76454d10bd19153443b46454d10ad19153443d75354d10dd94d53442f76254d10f9d8953442e76254d10bd18953443e46254d10b918953442f76054d10fcd8153442f36054d10bd99453442f66414d10bd59053443765414d10dd15053443775314d10f594c53443755314d10f554c53442f66214d10bd58853442f765d0d10bd99743442f565d0d10bd19743443d753d0d10f514f43442f662d0d10f998b43442e662d0d10bd58b43443e562d0d10b958b43442f660d0d10fc98343442f260d0d10bd58343443f160d0d10bc58343442f76590d10bd99643442f56590d10bd19643442f56490d10edd5243443b45490d10bd98e43443d65390d10f554e43443b74390d10f5d0e43442f66290d10bd58a43442f66090d10bd58243442f76550d10ddd9543442776550d10bd99543442f56550d10b
  | 6 => 0x2f662cc510bd58b31442f660cc510fc98331443f160cc5109f99631442f6618c510bd9963144376658c510bdd9231442f6648c510bd59231442f4648c510bd58e3144376538c510dd14e31442f6628c510bd58a31442f6608c5109f195314435f534c510d714d31442fb604c510be1813144374654c5109d19531442f7644c510bd99131442f5644c510bd19131443d7634c510f5d4d3144376534c510dd14d31443d4534c510f590d31443d5434c510bdd8931442f4624c510fcd8131442f4604c510fc181314427e650c510bd98431442f6650c510dd99431442f7640c510bd99031442f5640c510bd1903144376540c510dd15031442f6630c510f598c3144377530c510dd54c31442f6620c510bd58831442f6600c5109f997214436f52c8510db14b21442fa60c8510be583214437665c85109d99721442f764c8510bd99321442f564c8510bd193214437654c8510dd15321442f763c8510bd98f21442f563c8510bd18f214437752c8510f9d4b214437552c8510f914b21443e642c8510f950b21442f660c8510fc98321443f160c85109f99621442f66188510bd99621443766588510bdd9221442f66488510bd59221442f46488510bdd8e21442f66388510bd58e21442f46388510bd58a21443765288510dd14a21442f660885109f195214436f5248510db14921442fb6048510be181214437465485109d19521442f76448510bd99121442f56448510bd19121442f76348510bd98d21442f56348510bd18d21443e76248510f9d4921443765248510dd14921443e45248510f990921443e54248510fcd8121442f46048510fc181214427e6508510bd98421442f66508510dd99421442f76408510bd99021442f56408510bd19021443765408510dd15021442f76308510bd98c21442f56308510bd18c21442f66208510f998821443775208510dd54821442f660085109f997404433f54d0110cf15340442f661d0110bd587404427e6590110bd98640442f56190110be996404437a6590110be592404437a5490110de15240443f36190110be98640443f26190110bc98640443f16190110fc18640443f34190110fc90640443f14190110fc10640443f33190110fc8c640443f13190110fc0c640443f32190110fc88640443f12190110fc086404427f65501109f595404427c6550110cfd51404433c5450110bdd8540442f46150110be195404437865501109e19540443bb6450110eed51404437a5450110de15140443b85450110eed0d40443b94350110eed0940443b94250110fcd8540442f86150110fc18540443f34150110fc90540443f14150110fc10540443f33150110fc8c540443f13150110fc0c540443f32150110fc88540443f12150110fc085404427e6510110b798c40442dd6310110bb98840442ed6210110bd984
  | 7 => 0x4549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910db548524427e64149109f590524427e63149109f58c524436e62149109f984524437561149109f184524427e60149109f180524427f65d09109f997424427d65d09109f19742442de63d0910b758f424436f52d0910db14b42442f661d0910bd58742442fa60d0910be583424427f65909109f996424427d65909109f196424433f5490910cf152424436e5290910db54a42442f66190910bd586424427f65509109f995424427d65509109f195424436e5250910db54942442f76150910bd185424427f65109109f994424427d65109109f194424433f5410910cf150424436f5210910db14842442f66110910bd58442442fa6010910be580424427f65cc9109f997324427d65cc9109f197324436f52cc910db14b32442f661cc910bd587324427f658c9109f996324427d658c9109f196324435f538c910d714e32442f6618c910bd586324427f654c9109f995324427d654c9109f19532442f7614c910bd18532442fb604c910be181324427f650c9109f994324427d650c9109f194324435f530c910d714c324436f520c910db14832443cd320c910bd98432442f5610c910be98032442f9600c9109f997414433f54d0510cf15341442fa60d0510be583414437665d05109d997414437754d0510edd53414437554d0510ed15341442f663d0510bd58f414437653d0510dd14f41442f662d0510bd58b414437652d0510dd14b41442f660d0510fc98341442f260d0510fc583414427e6590510bd98641442f66590510dd99641442f56490510dd95241443745490510bd98e41442f56390510bd98a41442f56290510fcd8241442f66090510fc182414427c6550510cfd51414433c5450510bed8141442f86050510dd19541442746550510edd9141443b75450510dd95141443745450510ed15141443345450510bdd8d41442f46350510bdd8941442f46250510fcd8141442f46050510fc181414427e6510510b798c41442dd6310510bb98841442ed6210510bd98441442fa6010510bd99441443766510510bd99041443b66410510ddd5041443755410510bd98c41443d66310510b598c41442f56310510f558c41442d56310510dd94c41443745310510bd98841443e66210510b998841442f56210510f958841442e56210510dd94841443745210510bd98041443f26010510bc98041443f160105109f997314435f53cc510d714f31442fa60cc510be583314437665cc5109d99731442f764cc510bd99331442f564cc510bd193314437654cc510dd153314437753cc510f5d4f314437553cc510f514f31443d643cc510f550f3144
  | 8 => 0x10bbd8930842ec624c210af99030842bd640c210d794c308435d530c210bb98830842ed620c210bd98430842f5610c210f64c0308436e5288210db54a20842f66188210bd58620842df6348210b718d20842be6408210af59020842de6308210b758c208436e5208210db54820842f66108210bd58420843e92008210bd597108437565c4210ddd53108437654c4210dd553108437454c4210ddd4f108437653c4210dd54f108437453c4210ddd4b108437652c4210dd54b108437452c4210be597108437965c4210bed9310842f964c42109f98f544427d63d51109f98b544427d62d5110dd587544433f54951109f992544427e63951109f58e544427e62951109f58a544427d6195110dd586544427d6095110de58254442df6355110b718d54442ef6255110bb189544433f64551109fd8d544435f635511097d8d544427c6355110d718d544425c63551109fd89544436f62551109bd89544427c6255110db189544426c62551109fd85544437761551109fd81544437b60551109f994544433d5415110b798c54442dd6315110bb98854442ed6215110cf990544427e6315110d798c544425e63151109f58c544435d63151109758c544427e6215110db988544426e62151109f588544436d62151109b588544427e6115110dd584544427c61151109f980544437960151109f180544427e64d4d109f593534427e62d4d109f58b534437561d4d10d7d4e534427e6494d109f592534427e6394d109f98a534427d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10bbd8953442ec6254d109fd91534433f6454d108fd91534427c6454d10cf191534423c6454d10d7d8d534427f6254d10dbd89534426f6254d109f189534436c6254d109b189534427f6154d10ddd85534427f6054d10ded81534427e6514d10d754c534427e6414d109f590534435e6314d109f988534427d6214d109f98453443756114d109f184534427e6014d109f180534427f65d0d109f997434427d65d0d109f197434435f53d0d10d714f43442ee62d0d10bb58b43442f661d0d10bd58743442fa60d0d10be583434427f6590d109f996434427d6590d109f196434433f5490d10cf152434435e5390d10d754e43442f66190d10bd586434427f6550d109f995434427d6550d109f195434435e5350d10d754d43442f76150d10bd185434427f6510d109f994434427d6510d109f194434433f5410d10cf150434435f5310d10d714c43442f66110d10bd58443442fa6010d10be580434427e64d49109f593524427e63d49109f58f524437561d4910dbd4a524427e64949109f592524427e63949109f58e524427e62949109f586524437561949109f58252443796094910afd9152442bc6454910b7d8d52442dc63549109fd91524433f6
  | 9 => 0xd89538427c6254e10af99053842bd6414e10d754c53842ee6214e10bb588538427e6414e10cf990538423e6414e109f590538433d6414e108f590538435e6314e109f988538436e6214e109b988538427d6214e10db588538426d6214e10dd584538437a6014e109fd97438427e65d0e109f597438427c65d0e10cf953438433d54d0e10bb98b43842ed62d0e10be98343842f960d0e109fd96438427e6590e109f596438427c6590e10d794e438435d5390e109fd95438427e6550e109f595438427c6550e10cf951438433d5450e10d794d438435d5350e10bdd8543842f46150e109fd94438427e6510e109f594438427c6510e10be98043842f96010e109f993528427d64d4a109f98f528427d63d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528427f6454a109f191528427f6354a109f18d528436f6254a10af99052842bd6414a10b798c52842dd6314a10db548528427e6414a10cf990528423e6414a109f590528433d6414a108f590528427e6314a10d798c528425e6314a109f58c528435d6314a109758c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10cf953428433d54d0a10b798f42842dd63d0a10be98342842f960d0a109fd96428427e6590a109f596428427c6590a10db94a428436d5290a109fd95428427e6550a109f595428427c6550a10cf951428433d5450a10db949428436d5250a10bdd8542842f46150a109fd94428427e6510a109f594428427c6510a10be98042842f96010a109fd97328427e65cca109f597328427c65cca10d794f328435d53cca109fd96328427e658ca109f596328427c658ca10db94a328436d528ca109fd95328427e654ca109f595328427c654ca10d794d328435d534ca10db949328436d524ca10bed8132842f8604ca109fd94328427e650ca109f594328427c650ca10f34c832842fa600ca10be580328433e54d0610cf55341842fa60d0610be583418433e5450610cf55141842fb6050610be18141842de6310610b758c41842ee6210610bb58841843b54110610be580418435e53cc610d754f31842fa60cc610be583318435e534c610d754d31842fb604c610be181318436e52c8610db54b21842fa60c8610be583218436e5248610db54921842fb6048610be181218433e5490210cf55240842f66190210bd58640842f96590210de596408437a5490210ee95240843b95490210de15240842fa6190210fc98640843f16190210bed95408437b6550210eed91408437a5450210de15140843bb4350210ee50d40843bb4250210ee50940842f86150210cf950408433d5410210b798c40842dd6310210bb98840842ed6210210bd98440842f56110210d794e308435d538c210bd98630842f5618c2
  | 10 => 0xc42f76250310bd18940c43b74250310ed50940c43f34050310ed90140c42f56510310dd59440c42f66310310f598c40c42d66310310bd58c40c43d56310310b558c40c42f66210310f998840c42e66210310bd58840c43e56210310b958840c43b74010310fc90040c43b54010310fc50040c42f565cc310bdd9330c42f664cc310bd59330c42f464cc310f594f30c43d553cc310f590f30c43d543cc310bd98b30c42f562cc310f5ccb30c43d532cc310bd59630c4375658c310bdd9230c42f6648c310bd59230c42f4648c310bd98a30c42f5628c310f58ca30c43d4328c310f5cc230c43f3308c310bdd9530c42f7644c310bd99130c42f5644c310bd19130c43d6534c310f554d30c43d6434c310f550d30c42f7624c310f9d8930c42e7624c310bd18930c43e4624c310b918930c43d7324c310f54c930c43f3304c310f58c130c42f5650c310dd59430c42f7640c310bd99030c43b6640c310ad99030c42f5640c310ed59030c42b5640c310bd19030c42f6620c310f998830c42e6620c310bd58830c43e5620c310b958830c43d6320c310f50c830c43d7300c310fc8c030c43d5300c310fc4c030c42f565c8310bdd9320c42f664c8310bd59320c42f464c8310bdd8f20c42f663c8310bd58f20c42f463c8310f994b20c43e552c8310f990b20c43e542c8310f98cb20c43e532c8310bd59620c43756588310bdd9220c42f66488310bd59220c42f46488310bdd8e20c42f66388310bd58e20c42f46388310f9cca20c43e43288310f9c8220c43f32088310bdd9520c42f76448310bd99120c42f56448310bd19120c42f76348310f5d8d20c42d76348310bd98d20c42f56348310bd18d20c43d46348310b518d20c43e65248310f954920c43e64248310f950920c43e63248310f94c920c43f32048310f988120c42f56508310dd59420c42f76408310bd99020c43b66408310ad99020c42f56408310ed59020c42b56408310bd19020c42f76308310bd98c20c43d66308310b598c20c42f56308310f558c20c42d56308310bd18c20c43e73208310f90c820c43e72008310fc88020c43e52008310fc48020c427e63d52109f58f548427e62d52109f58b548437561d5210de983548433f54952109f98e548427d63952109f98a548427d6295210de982548433f64552109fd8d548427c63552109fd89548427c6255210cf55054842de6315210b758c54842ee6215210bb588548433e64152109f98c548435e63152109798c548427d6315210d758c548425d63152109f988548436e62152109b988548427d6215210db588548426d6215210dd584548437a60152109f993538427d64d4e109f98b538427d62d4e10dd587538437a60d4e10d7d4e538427e6494e109f592538427e6294e109f58a538427f6454e109f191538435f6354e109f
  | 11 => 0xd55390f10edd0e43c43d74390f10bd98a43c42f56290f10bd98243c42f56090f10bdd9543c43776550f109dd9543c42f66550f10bd59543c42f46550f10dd19543c42746550f10f594d43c43d55350f10f5d0d43c43b64350f10bdd8943c42f46250f10bdd8143c42f46050f10bdd9443c42f66510f10bd59443c42f46510f10edd0c43c43d64310f10ed50c43c43d54310f10bd98843c42f56210f10bd98043c42f56010f10bd99352c42f564d4b10bd98f52c43d663d4b10b598f52c42f563d4b10f558f52c42d563d4b10bd58352c43f160d4b10bc58352c42f66494b10bd59252c43765494b10dd15252c42f66394b10bd58e52c43775294b10f9d4a52c42f76454b10bd19152c42f76354b10bd18d52c43e75254b10dd94952c42f66414b10bd59052c43765414b10dd15052c42f66314b10bd58c52c43775214b10f994852c43755214b10f954852c42f56014b10fc58052c42f16014b10bdd9742c42f665d0b10bd59742c42f465d0b10bd98f42c43d663d0b10b598f42c42f563d0b10f558f42c42d563d0b10bd98342c42f560d0b10bdd9642c42f66590b10bd59642c42f46590b10bd98e42c42f56390b10f994a42c43e55290b10edd0a42c43e74290b10bd98242c42f56090b10bdd9542c43776550b109dd9542c42f66550b10bd59542c42f46550b10dd19542c42746550b10bdd8d42c42f46350b10f994942c43e55250b10f9d0942c43b64250b10bdd8142c42f46050b10bdd9442c42f66510b10bd59442c42f46510b10bd98c42c42f56310b10edd0842c43e64210b10ed50842c43e54210b10bd98042c42f56010b10bdd9732c42f665ccb10bd59732c42f465ccb10bdd9332c42f664ccb10bd59332c42f464ccb10f994b32c43e552ccb10f990b32c43e542ccb10bd98332c42f560ccb10bdd9632c42f6658cb10bd59632c42f4658cb10bdd9232c42f6648cb10bd59232c42f4648cb10f594e32c43d5538cb10f590e32c43d5438cb10f5cca32c43e7328cb10bd98232c42f5608cb10bdd9532c42f6654cb10bd59532c42f4654cb10bdd9132c42f6644cb10bd59132c42f4644cb10f9cc932c43d6324cb10bdd8132c42f4604cb10bdd9432c42f6650cb10bd59432c42f4650cb10bdd9032c42f6640cb10bd59032c42f4640cb10f594c32c43d5530cb10f590c32c43d5430cb10f994832c43e5520cb10f990832c43e5420cb10f5cc832c43e6320cb10f54c832c43e5320cb10f14c832c42f6600cb10bd58032c42f565d0310ed95340c43b554d0310bd98f40c42f563d0310edd0f40c43b543d0310bd98b40c42f562d0310edd0b40c43b542d0310bd59640c43756590310bd98e40c42f56390310bd98a40c42f56290310edd0240c43f34090310bdd9540c43b65450310ed55140c42f76350310bd18d40c43b74350310ed50d4
  | 12 => 0xc8710dd15321c42f763c8710bd98f21c42f563c8710bd18f21c437752c8710dd54b21c43e642c8710f950b21c42f660c8710db94a21c436d5288710be98221c42f96088710dd59621c42f76488710bd99221c42f56488710bd19221c42f76388710bd98e21c42f56388710bd18e21c43765288710f994a21c43e55288710dd14a21c42f66088710fc98221c43f16088710bdd9521c43776548710bdd9121c42f66448710bd59121c42f46448710bdd8d21c42f66348710bd58d21c42f46348710f9d8921c43765248710dd14921c43e64248710f950921c42f46048710db94821c436d5208710be98021c42f96008710dd59421c42f76408710bd99021c42f56408710bd19021c43765408710dd15021c42f76308710bd98c21c42f56308710bd18c21c43e66208710ddd4821c43e65208710dd54821c43e55208710bd98021c43f26008710fc58021c433e54d0310cf55340c42f661d0310bd58740c42f66190310bd58640c433e5450310cf55140c42f76150310bd18540c42de6310310b758c40c42ee6210310bb58840c42f66110310bd58440c435e53cc310d754f30c42f661cc310bd58730c42f6618c310bd58630c435e534c310d754d30c42ef624c310bb18930c42f7614c310bd18530c42be640c310af59030c42ee620c310bb58830c42f6610c310bd58430c436e52c8310db54b20c42f661c8310bd58720c42f66188310bd58620c42df6348310b718d20c436e5248310db54920c42f76148310bd18520c42be6408310af59020c42de6308310b758c20c42f66108310bd58420c42f663d5310bd58f54c42f662d5310bd58b54c42f560d5310fc58354c42f160d5310ddd5254c43b75495310bd98e54c42f56395310bd98a54c42f56295310edd5154c43765455310bdd8d54c42f46355310bdd8954c42f46255310ddd5054c43b65415310dd55054c43b55415310cd55054c42f66315310f598c54c42d66315310bd58c54c43d56315310b558c54c42f66215310f998854c42e66215310bd58854c43e56215310b958854c42f56015310fc58054c42f16015310bd99353c42f564d4f10bd98b53c43e662d4f10b998b53c42f562d4f10f958b53c42e562d4f10bd58353c43f160d4f10bc58353c42f66494f10bd59253c43765494f10dd15253c43775394f10f5d4e53c42f66294f10bd58a53c42f76454f10bd19153c43d75354f10dd94d53c42f76254f10bd18953c42f66414f10bd59053c43765414f10dd15053c43775314f10f594c53c43755314f10f554c53c42f66214f10bd58853c42f56014f10fc58053c42f16014f10bdd9743c42f665d0f10bd59743c42f465d0f10bd98b43c43e662d0f10b998b43c42f562d0f10f958b43c42e562d0f10bd98343c42f560d0f10bdd9643c42f66590f10bd59643c42f46590f10f594e43c43
  | 13 => 0x9f98c52c427d6314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c42de63d0b10b758f42c42f661d0b10bd58742c427f6590b109f99642c427d6590b109f19642c436e5290b10db54a42c42f66190b10bd58642c427f6550b109f99542c427d6550b109f19542c436e5250b10db54942c42f76150b10bd18542c427f6510b109f99442c427d6510b109f19442c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c436e52ccb10db54b32c42f661ccb10bd58732c427f658cb109f99632c427d658cb109f19632c435e538cb10d754e32c42f6618cb10bd58632c427f654cb109f99532c427d654cb109f19532c42f7614cb10bd18532c427f650cb109f99432c427d650cb109f19432c435e530cb10d754c32c436e520cb10db54832c43cd320cb10bd98432c42f5610cb10bd59741c437565d0710ddd5341c437554d0710bd98f41c42f563d0710dd94f41c437453d0710bd98b41c42f562d0710dd94b41c437452d0710bd98341c433e5490710cf55241c42fa6090710be58241c43756590710dd95241c43b65490710ed55241c43745490710bd98e41c42f56390710bd98a41c42f56290710bd98241c43f26090710fc58241c42f76550710ddd9541c43b76450710dd95141c43745450710bdd8d41c42f46350710bdd8941c42f46250710bd18141c433e5410710cf55041c42de6310710b758c41c42ee6210710bb58841c42fa6010710be58041c43756510710ed99041c43775410710ed95041c43755410710ed55041c43355410710bd98c41c43d66310710b598c41c42f56310710f558c41c42d56310710dd94c41c43745310710bd98841c43e66210710b998841c42f56210710f958841c42e56210710dd94841c43745210710bd98041c43f26010710fc58041c42f565cc710dd59731c42f764cc710bd99331c42f564cc710bd19331c437654cc710dd15331c437753cc710dd54f31c43d643cc710f550f31c42f662cc710bd58b31c42f660cc710d794e31c435d538c710be98231c42f9608c710dd59631c42f7648c710bd99231c42f5648c710bd19231c4376538c710f594e31c43d5538c710dd14e31c42f6628c710bd58a31c42f6608c710fc98231c43f1608c710bdd9531c4377654c710bdd9131c42f6644c710bd59131c42f4644c710f5d8d31c4376534c710dd14d31c43d6434c710f550d31c42f7624c710bd18931c42f4604c710d794c31c435d530c710be98031c42f9600c710dd59431c42f7640c710bd99031c42f5640c710bd19031c4376540c710dd15031c43d6630c710ddd4c31c43d6530c710dd54c31c43d5530c710bd98831c42f5620c710bd98031c43f2600c710fc58031c42f565c8710dd59721c42f764c8710bd99321c42f564c8710bd19321c437654
  | 14 => 0x4f200835d53c8020dd947200837551c8020dbd5320083ae54c8020db55320083ad54c8020cb55320082ee63c8020bb18f200836f53c8020f394f200836d53c8020f354f200834d53c8020f994720083e551c8020cf952200833d5488020d794e200835d5388020bb58a200836e5288020bd98620082f56188020dd94620083755188020ee95220083b95488020f694e20083d95388020be58a200837a5288020fa94a20083eb3288020fa0ca20083f26188020fc58620083f25188020fc546200827f6548020cf951200833d5448020b7d8d20082dc6348020d794d200835d5348020dd94520083755148020bbd95200836f65480209bd95200836f5448020eb951200836d5448020eb551200832d5448020f3d8d20082ee6348020bb18d20083cc6348020b318d200836f5348020f394d200836d5348020f354d200834d5348020f994520083e55148020bbd81200836e5048020bed95200837b65480209ed9520083ba5448020ee55120083db6348020f618d20083da5348020f654d20082fb6248020fad89200837a5248020fa94920083f25148020fc54520083eb2148020fa485200827e63d53109f58f54c427e62d53109f58b54c437661d5310de58354c433f54953109f98e54c427d63953109f98a54c427d6295310dd98654c433f64553109fd8d54c427c63553109fd8954c427c6255310dd18554c433d5415310b798c54c42dd6315310bb98854c42ed6215310cf99054c427e6315310d798c54c425e63153109f58c54c435d63153109758c54c427e6215310db98854c426e62153109f58854c436d62153109b58854c43766115310de58054c42ee62d4f10bb58b53c427e64d4f109f59353c427e62d4f10db98b53c426e62d4f109f58b53c436d62d4f109b58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f10dd98653c427f6454f109f19153c435f6354f109fd8953c427c6254f10dd18553c435d5314f109f99053c427d6414f10d798c53c427e6214f109f58853c43766114f10de58053c427f65d0f109f99743c427d65d0f109f19743c42ee62d0f10bb58b43c42f661d0f10bd58743c427f6590f109f99643c427d6590f109f19643c435e5390f10d754e43c42f66190f10bd58643c427f6550f109f99543c427d6550f109f19543c435e5350f10d754d43c42f76150f10bd18543c427f6510f109f99443c427d6510f109f19443c42f66110f10bd58443c42de63d4b10b758f52c427e64d4b109f59352c427e63d4b10d798f52c425e63d4b109f58f52c435d63d4b109758f52c437661d4b10de58352c436f5294b109f99252c427d6494b109f98e52c427d6394b10dd98652c427f6454b109f19152c427f6354b109f18d52c436f6254b10dd18552c436d5214b109f99052c427d6414b1
  | 15 => 0x837551144209fd97410827e65d04209f597410833e54d0420cf553410835e53d0420d754f410837651d0420dd547410827f65904209f996410827d6590420cf952410833d5490420d794e410835d5390420dd946410837551904209fd95410827d65504209f195410833e5450420cf551410835e5350420d754d41082ef6250420bb18941083765150420dd545410827f65104209f994410827d6510420cf950410833d5410420b798c41082dd6310420d794c410835d5310420bb98841082ed6210420dd94441083755110420be98041082f960104209fd97310827e65cc4209f597310833e54cc420cf553310835e53cc420d754f310837651cc420dd547310827f658c4209f996310827d658c420cf952310833d548c420d794e310835d538c420bb98a31082ed628c420dd9463108375518c420be98231082f9608c4209fd95310827d654c4209f195310833e544c420cf551310835e534c420d754d31082ef624c420bb1893108376514c420dd545310827f650c4209f994310827d650c420cf950310833d540c420d794c310835d530c420dd9443108375510c420cf953210833d54c8420d794f210835d53c8420dd947210837551c8420be98321082f960c84209f596210833e5488420cf552210835e5388420d754e210837551884209fd95210833e5448420cf551210835e5348420d754d21083765148420cf950210833d5408420d794c210835d5308420dd94421083755108420be98021082f960084209f992500827d64940209f98e500827d6394020dbcca500836c3294020dd986500837561940209f597400833e54d0020cf553400835e53d0020d754f400837651d0020dd547400827f65900209f596400833e5490020cf552400835e5390020d754e40082ee6290020bb58a40082f66190020bd58640083765190020dd546400827f6550020cf951400833d5450020d794d400835d5350020dd945400837551500209fd94400827e65100209f594400827c6510020cf950400833d5410020b798c40082dd6310020d794c400835d5310020bb98840082ed6210020bd98440082f56110020dd944400837551100209f597300833e54cc020cf553300835e53cc020d754f30083cf32cc020dd947300837551cc0209fd96300827d658c020cf952300833d548c020d794e300835d538c020bb98a30082ed628c020f30ca30082f6618c020bd5863008376518c020dd546300827f654c020cf951300833d544c020d794d300835d534c020bbd8930082ec624c020f3cc93008376514c020dd545300827f650c0209f994300827d650c0209f19430082be640c020af590300833e540c020cf550300835e530c020d754c30082ee620c020bb58830083cc320c020bd98430082f5610c020dd9443008375510c020cf953200833d54c8020d79
  | 16 => 0xd64948209f98e520827d63948209f597420833e54d0820cf55342082de63d0820b758f420835e53d0820d754f420827f65908209f596420833e5490820cf552420835e5390820d754e420836e5290820be98242082f960908209fd95420833e5450820cf551420835e5350820d754d420836e5250820bdd8542082f461508209fd94420827d6510820cf950420833d5410820d794c420835d5310820be98042082f960108209f597320833e54cc820cf553320835e53cc820d754f32082ed65cc820db597320826d65cc820dbd5332083ae54cc820db55332083ad54cc820cb553320836f53cc820f394f320836d53cc820f354f320834d53cc820bb583320827f658c8209f596320833e548c820cf552320835e538c820d754e32082ee628c820db94a32082fa608c820be582320827f654c820cf951320833d544c820d794d320835d534c820db949320827f650c8209f594320833e540c820cf550320835e530c820d754c32083cd320c820be98032082f9600c820db594320826d650c820dbd5032083ae540c820db55032083ad540c820cb55032082ee630c820f398c320836f530c820f394c320836d530c820f354c320834d530c820f390c32083cd430c820fa98032082ed600c820fa58032082be64d4420af593510833e54d4420cf55351082de63d4420b758f510835e53d4420d754f510833e5494420cf552510835e5394420d754e510837751944209f992510827d64944209f98e510827d6394420ddd5251083765494420ed95251083365494420dd55251083b55494420cd55251083745494420ddd4e51083765394420f594e51083565394420dd54e51083d55394420d554e51083745394420f9cca51083e43294420ddd9251083766494420dd59251083746494420ddd8e51083766394420dd58e51083746394420ddd0e51083764394420dd50e51083744394420dd18a51083774294420dd90a51083754294420dd10a51083773294420dd8ca51083753294420dd0ca51083766094420dd182510833e5454420cf551510835e5354420d754d510827f64544209f191510827f63544209f18d51083776554420ddd5151083765454420ed95151083365454420dd55151083b55454420cd55151083745454420ddd4d51083765354420f594d51083565354420dd54d51083d55354420d554d51083745354420f9cc951083e43254420ddd9151083766454420dd59151083746454420ddd8d51083766354420dd58d51083746354420ddd0d51083764354420dd50d51083744354420dd98951083774254420dd90951083754254420dd10951083773254420dd8c951083753254420dd0c951083766054420dd18151083742054420af99051082bd6414420cf950510833d5414420b798c51082dd6314420d794c510835d5314420bd98451
  | 17 => 0x50208f596540833f6395020cf98e540833d6395020cf18e540833e6295020cf18a540833f6195020cf986540833d6195020cf186540833e6095020cf182540833f64550209fd8d540827c63550209fd89540827d62550209fd85540827c6155020cfd95540833f6355020cf98d540833d6355020cf18d540833e6255020cf189540833f6155020cf985540833d6155020cf185540833e6055020cf181540833c2055020af990540833d5415020b798c54082dd6315020bd98454082f561150209f990540833e64150208f990540827e6315020d798c540825e63150209f58c540835d63150209758c540827e6215020db988540826e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a6015020af99353082bd64d4c20cf953530833d54d4c20bd98753082f561d4c209f993530833e64d4c208f993530827d64d4c20cf593530823d64d4c209f98b530836e62d4c209f987530837661d4c209d987530827d61d4c20dd587530827561d4c209f983530837a60d4c209f596530833e5494c20cf552530835f5394c209f992530827d6494c209f986530827d6194c2097596530835f5494c20d7952530839e5494c20c7952530835d5494c20e7552530831d5494c20d715253083cc6294c20d7d92530835e6494c20d7592530835c6494c20d798a530835c6294c20d7d86530835e6194c20d7586530835c6194c20d7982530835c6094c20cf951530833d5454c209fd91530827c6454c20d7d8d530827f6254c209f589530836c6254c209fd85530827c6154c20d7d95530835f5454c20d7951530839e5454c20c7951530835d5454c20e7551530831d5454c20d715153083cc6254c20d7d91530835e6454c20d7591530835c6454c20d7989530835c6254c20d3189530835f6154c20d7985530835d6154c20d7185530835e6054c20d7181530835c2054c20af99053082bd6414c20cf950530833d5414c20b798c530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209798c530827e6214c20db988530826e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c20d794f430835d53d0c20bb98b43082ed62d0c209fd96430827e6590c209f596430827c6590c20cf952430833d5490c20d794e430835d5390c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c20bbd8943082ec6250c20bdd8543082f46150c20bed8143082f86050c209fd94430827e6510c209f594430827c6510c20cf950430833d5410c20d794c430835d5310c209f992520827
  | 18 => 0x9f993514827d64d45209f98f514827d63d4520db90b514836d42d4520b798e51482dd6394520d7d4e514835c5394520ddd4651482bf6454520af19151482df6354520b718d514835f5354520d714d514835f5314520d714c514837551145209f990514827d64145209f98c514827d63145209f997414827d65d05209f197414835f53d0520d714f41482ee62d0520bb58b414837751d0520dd147414827e65905209f596414827c6590520cfd52414833c5490520d7d4e414835c53905209fd95414827e65505209f195414835f5350520d714d414827e65105209f594414827c6510520cfd50414833c5410520b798c41482dd6310520d7d4c414835c5310520bb98841482ed6210520ddd4441483745110520be98041482f960105209f997314827d65cc5209f197314835f53cc520d714f31482ee62cc520bb58b314827e658c5209f596314827c658c520d7d4e314835c538c5209fd95314827e654c5209f195314835f534c520d714d314827e650c5209f594314827c650c520d7d4c314835c530c520bb98831482ed620c520be98031482f9600c5209f997214835f53c8520d714f214835f5388520d714e21483775188520dd14621482fa6088520be582214835f5348520d714d21483775148520dd14521482fb6048520be181214827e6508520d7d4c214835c53085209f997404833f54d0120cf153404835f53d0120d714f40482ee62d0120bb58b40483ad42d01209f996404835f5390120d714e40482f66190120bd586404827f65501209f595404827c6550120cfd51404833c5450120d7d4d404835c5350120bbd8940482ec6250120eb509404827e6510120b798c40482dd6310120d7d4c404835c5310120bb98840482ed6210120bd98440482f561101209f997304835f53cc120d714f30482ee62cc120bb58b30483cd32cc1209f996304835f538c120d714e30483ce328c120bd98630482f5618c1209fd95304827d654c1209f195304835f534c120d714d30482ef624c120bb18930483cd324c1209f99430482be640c120af590304835f530c120d714c30482ee620c120bb58830483ce320c120bd98430482f5610c120d7d4f204835c53c8120f6d4f20483d853c8120fa90b20483e942c8120fa8cb20483e932c8120d7d4e204835c5388120bd98620482f56188120bbd9220482ed6488120bbd8e20482ed6388120f3d4e204836e5388120db14e20483cc5388120d314e20483e66188120f958620483eb5088120b798f54082dd63d5020bd98754082f561d50209f98f540835e63d50209798f540827d63d5020d758f540825d63d50209f98b540836e62d50209f987540837661d50209d987540827d61d5020dd587540827561d50209f983540837a60d50209f596540833f54950209f98e540827d63950209f986540827d619
  | 19 => 0x8544836d62151209f188544827e61151209f584544827e64d4d209f593534827e61d4d209f587534835f54d4d20d7953534835d54d4d20d715353483cf62d4d20d7d93534835e64d4d20d7593534835c64d4d20d7d8b534835d62d4d20d7d87534835e61d4d20d7587534835c61d4d20d7d83534835d60d4d20d7d4e534827e6494d209f592534827e6394d209798e534827d6294d20db58a534827e6194d209f586534827d6094d20de582534827f6454d209f191534835f6354d209fd89534836f6254d209bd89534827f6154d209f185534827f6054d20ded81534827e6514d20d754c534827e6414d209f590534835e6314d209f988534836d6214d209f188534827e6114d209f58453482de6514d20d7994534825e6514d20d7d50534835e5414d20d7550534835c5414d20f3588534835f6414d20d7990534835d6414d20d7190534835f6214d20d7588534834d6214d20d7d84534835e6114d20d7584534835c6114d20d7d80534835d6014d20d7480534827f65d0d209f997434827d65d0d209f197434835f53d0d20d714f43482ee62d0d20bb58b434827f6590d209f996434827d6590d209f196434835f5390d20d714e43482ee6290d20bb58a434827f6550d209f995434827d6550d209f195434835f5350d20d714d43482f76150d20bd185434827f6510d209f994434827d6510d209f194434835f5310d20d714c43482ee6210d20bb58843482fa6010d20be580434827e65d0920cfd53424833c54d0920b798f42482dd63d0920d7d4f424835c53d0920be98342482f960d09209f996424835f5390920d714e42482ee6590920db99642482ed6490920db952424836c5490920bb58e42483cf5390920db94e424836c5390920f314e424834c5390920bb982424827c6550920cfd51424833c5450920d7d4d424835c5350920bdd8542482f46150920bed8142482f86050920db195424826c6550920ebd9142483af5450920db951424836c5450920eb15142482ef6350920f3d4d424836e5350920db14d42483cc5350920d314d42483e76150920f918542483eb6050920bb18142483e860509209f994424835f5310920d714c42482ee6210920eb508424827e65cc920d7d4f324835c53cc920be98332482f960cc9209f996324835f538c920d714e32482ee658c920db996324826e658c920bbd9232482ed648c920bb58e32483cf538c920db94e324836c538c920f314e324834c538c920f390e32483cd438c920bb982324827c654c920d7d4d324835c534c920bed8132482f8604c920db195324826c654c920bbd9132482ed644c920f3d8d32483cf534c920db94d324836c534c920f314d324834c534c920fad8132482ec604c920fa181324827e650c920d7d4c324835c530c920bb98832483cd320c920d7d4f514835c53d4520
  | 20 => 0x83745454620ddd4d51883765354620dd54d51883745354620f9cc951883e43254620ddd9151883766454620dd59151883746454620ddd8d51883766354620dd58d51883746354620ddd0d51883764354620dd50d51883744354620dd58951883774254620dd90951883754254620dd10951883773254620dd8c951883753254620dd0c951883766054620dd181518837551146209fd97418827e65d06209f597418837651d0620dd547418827f65906209f996418827d6590620dd946418837551906209fd95418827d65506209f19541882ef6250620bb18941883765150620dd545418827f65106209f994418827d6510620b798c41882dd6310620bb98841882ed6210620dd94441883755110620be98041882f960106209fd97318827e65cc6209f597318837651cc620dd547318827f658c6209f996318827d658c620bb98a31882ed628c620dd9463188375518c6209fd95318827d654c6209f19531882ef624c620bb1893188376514c620dd545318827f650c6209f994318827d650c620dd9443188375510c620be98031882f9600c620dd94721883765188620dd54621882fa6088620be58221883765148620dd54521882fb6048620be18121883755108620cfd53408833c54d0220dd947408837551d0220cf952408833d5490220bb98a40882ed6290220bd98640882f56190220dd94640883755190220cfd51408833c5450220dd94540883755150220cf950408833d5410220b798c40882dd6310220bb98840882ed6210220bd98440882f56110220dd94440883755110220d7d4f308835c53cc220f3ccb308837651cc220dd547308835e538c220d754e30882ee628c220bb58a30883cc328c220bd98630882f5618c220dd9463088375518c220d7d4d308835c534c220bbd8930882ec624c220f3cc93088376514c220dd54530882be640c220af590308835e530c220d754c30882ee620c220bb58830883cc320c220bd98430882f5610c220dd9443088375510c220dd947208837551c8220bb597208836d65c8220dbd53208836d54c8220bb98f20882ec63c8220dbd4f208836d53c8220f994720883e551c8220be597208837965c8220fc94720883f151c82209f98f544827d63d51209f987544827d61d5120cfd5254482de6395120b758e544827e64951209f98e544835e63951209798e544827d6395120d758e544825d63951209f58a544836d62951209f986544827d61951209f58254483796095120b7d8d54482dc6355120bdd8554482f46155120cfd91544827f6355120d7d8d544825f63551209f18d544835c63551209718d544827f6255120dbd89544827f6155120ddd85544827761551209f185544837461551209d185544827f6055120ded81544827e6515120cf550544833e64151209f98c544827d63151209f98
  | 21 => 0x620c320bb58830c83ce320c320bd98430c82f5610c320bd98754882f561d52209f98f548827d63d5220db58b548827e61d5220dd987548827661d52209f587548837561d52209d587548837a60d5220cfd52548827e63952209f58e548827e61952209f586548833f64552209fd8d548827c63552209fd85548827c6155220cf55054882de6315220b758c54882f66115220bd584548833e64152209f98c548835e63152209798c548827d6315220d758c548825d6315220db588548827e6115220dd984548827661152209f584548837561152209d584548837a6015220bd98753882f561d4e209f993538827d64d4e20db58b538827e61d4e20dd987538827661d4e209f587538837561d4e209d587538837a60d4e20d7d4e538827e6494e209f592538827e6194e209f586538827f6454e209f191538835f6354e20dbd89538827f6154e209f18553882be6414e20af590538835d5314e20bd98453882f56114e209f990538833e6414e208f990538827d6414e20cf590538823d6414e20d798c538836d6214e209f98453883766114e209d984538827d6114e20dd58453882756114e20de980538827f65d0e209f997438827d65d0e209f197438833e54d0e20cf55343882ee62d0e20bb58b438827f6590e209f996438827d6590e209f196438835e5390e20d754e438827f6550e209f995438827d6550e209f195438833e5450e20cf551438835e5350e20d754d43882ef6250e20bb18943882f76150e20bd185438827f6510e209f994438827d6510e209f19443882fa6010e20be580438833e54d0a20cf55342882de63d0a20b758f42882fa60d0a20be583428833e5450a20cf55142882f76150a20bd18542882fb6050a20be181428835e53cca20d754f32882fa60cca20be583328836d65cca20dbd53328836d54cca20dbd4f32883ce53cca20db54f32883cd53cca20fa98332882ed60cca20fa583328835f538ca20d714e328835e534ca20d754d32882fb604ca20be181328835f530ca20d714c32883cd320ca20bb594328836d650ca20dbd50328836d540ca20f398c328836f530ca20f3d4c328834f530ca20db54c32883cc530ca20f390c32883cd430ca20bb580328837751946209f992518827d64946209f98e518827d6394620ddd5251883765494620dd55251883745494620ddd4e51883765394620dd54e51883745394620f9cca51883e43294620ddd9251883766494620dd59251883746494620ddd8e51883766394620dd58e51883746394620ddd0e51883764394620dd50e51883744394620ddd8a51883774294620dd90a51883754294620dd10a51883773294620dd8ca51883753294620dd0ca51883766094620dd182518827f64546209f191518827f63546209f18d51883776554620ddd5151883765454620dd551518
  | 22 => 0xf209fd9153c827c6454f20d7d8d53c827f6154f209f18553c835d5314f209f99053c827d6414f20d798c53c836e6214f209f98453c827d6114f20de58053c827f65d0f209f99743c827d65d0f209f19743c82ee62d0f20bb58b43c827f6590f209f99643c827d6590f209f19643c835f5390f20d714e43c82ee6290f20bb58a43c827f6550f209f99543c827d6550f209f19543c835f5350f20d714d43c82f76150f20bd18543c82fb6050f20be18143c827f6510f209f99443c827d6510f209f19443c82ee6210f20bb58843c833f54d0b20cf15342c82de63d0b20b758f42c833e5490b20cf55242c82fa6090b20be58242c836d6590b20db95242c83ae5490b20eb55242c836c5490b20bb58e42c836e5390b20db14e42c82ee6090b20fa98242c83e96090b20cfd5142c833c5450b20bdd8542c82f46150b20bbd9542c836f6550b20ebd9142c83af5450b20db95142c836c5450b20eb15142c82ef6350b20db94d42c836c5350b20f9d8542c83e46150b20bb18142c833e5410b20cf55042c83ad4210b20be98042c82f96010b20d7d4f32c835c53ccb20d794e32c835d538cb20be98232c82f9608cb20db59632c82ef648cb20bb59232c836e538cb20f394e32c83cd538cb20db14e32c83ce438cb20f350e32c82ee608cb20fa98232c83e9608cb20d7d4d32c835c534cb20bbd9532c836f654cb20bbd9132c82ed644cb20f3d8d32c83cf534cb20db94d32c836c534cb20f314d32c834c534cb20bb18132c835e530cb20d754c32c83cd320cb20be98032c82f9600cb20ddd4651c827e64947209f59251c827e63947209f58e51c827f64547209f19151c827f63547209f18d51c836e4254720db50951c837551147209fd9741c827e65d07209f59741c82ee62d0720bb58b41c827f65907209f99641c827d65907209fd9541c827d65507209f19541c827f65107209f99441c827d6510720b798c41c82dd6310720bb98841c82ed6210720be98041c82f960107209fd9731c827e65cc7209f59731c82ee62cc720bb58b31c827f658c7209f99631c827d658c720be98231c82f9608c7209fd9531c827d654c7209f19531c827f650c7209f99431c827d650c720bb98831c82ed620c720dd94721c837551c8720be98321c82f960c8720dd94421c83755108720be98021c82f96008720cf95340c833d54d0320bb98b40c82ed62d0320eb50b40c82f66190320bd58640c833e5450320cf55140c82ef6250320bb18940c83ad4250320b798c40c82dd6310320bb98840c82ed6210320bd98440c82f56110320d794f30c835d53cc320bb98b30c82ed62cc320f34cb30c835f538c320d714e30c83ce328c320bd98630c82f5618c320d794d30c835d534c320bbd8930c82ec624c320f34c930c82be640c320af59030c835f530c320d714c30c82ee
  | 23 => 0xf996210c27d6588430cf952210c33d5488430b798e210c2dd6388430db94a210c36d5288430dd946210c3755188430be982210c2f960884309fd95210c27d65484309f195210c33e5448430cf551210c2df6348430b718d210c36e5248430db549210c3765148430dd545210c27f65084309f994210c27d6508430cf950210c33d5408430db948210c36d5208430dd944210c37551084309f992500c27d6494030d78ca500c35c3294030dd986500c37561940309f597400c33e54d0030cf553400c36e52d0030db54b400c37651d0030dd547400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c36e5290030db54a400c2f66190030bd586400c3765190030dd546400c27f6550030cf951400c33d5450030db949400c36d5250030dd945400c37551500309fd94400c27e65100309f594400c27c6510030cf950400c33d5410030b798c400c2dd6310030bb988400c2ed6210030db948400c36d5210030bd984400c2f56110030dd944400c3755110030cf953300c33d54cc030db94b300c36d52cc030dd947300c37551cc030d7d53300c39e54cc030d7553300c39d54cc030c7553300c2de62cc030f394b300c35d52cc030f354b300c34d52cc030f5947300c3d551cc030cf952300c33d548c030b758e300c35e538c030db94a300c36d528c030bd986300c2f5618c030dd946300c375518c030ee952300c3b9548c030be58e300c37a538c030f694e300c3ea528c030fa54a300c3da328c030f60ca300c3f2618c030fc586300c3f2518c030fc546300c27f654c030cf951300c33d544c030bbd89300c2ec624c030db949300c36d524c030dd945300c375514c030b7d95300c35f654c03097d95300c35f544c030e7951300c35d544c030e7551300c31d544c030f3d89300c2dc624c030f3189300c2cc624c030f3949300c35d524c030f3549300c34d524c030f5945300c3d5514c030b7d81300c35e504c030bed95300c37b654c0309ed95300c3ba544c030ee551300c2fb634c030f6d8d300c37a534c030f694d300c3eb624c030fa189300c3ea524c030fa549300c3f2514c030fc545300c3db314c030f64c5300c27e63d53209f58f54c836e62d53209f98754c827d61d5320de58354c833f5495320b798e54c82dd63953209f98e54c835e63953209798e54c827d6395320d758e54c825d6395320db98a54c827e61953209f58654c82f76155320bd18554c833f64553209fd8d54c827c63553209fd8554c837761553209dd8554c827c6155320dd18554c82746155320cf55054c833e64153209f98c54c827d6315320db98854c827e61153209f58454c837960153209f99353c827d64d4f20db98b53c827e61d4f209f58753c837960d4f20d7d4e53c827e6494f209f59253c836e6294f209f98653c827d6194
  | 24 => 0x320c35d540c830e7550320c31d540c830b7988320c3ce620c830f3948320c35d520c830f3548320c34d520c830f3908320c3cd420c830f6980320c2dd600c830f6580320c2be64d4430af593510c33e54d4430cf553510c2ee62d4430bb58b510c36e52d4430db54b510c33e5494430cf552510c36e5294430db54a510c37751944309f992510c27d64944309f98a510c27d6294430ddd52510c3765494430ed952510c3365494430dd552510c3b55494430cd552510c3745494430ddd4a510c3765294430f994a510c3665294430dd54a510c3e55294430d954a510c3745294430f58ca510c3d43294430ddd92510c3766494430dd592510c3746494430dd18e510c3774394430dd90e510c3754394430dd10e510c3776294430dd98a510c3756294430dd18a510c3774294430dd90a510c3754294430dd10a510c3773294430dd8ca510c3753294430dd0ca510c3766094430dd182510c33e5454430cf551510c36e5254430db549510c27f64544309f191510c27f62544309f189510c3776554430ddd51510c3765454430ed951510c3365454430dd551510c3b55454430cd551510c3745454430ddd49510c3765254430f9949510c3665254430dd549510c3e55254430d9549510c3745254430f58c9510c3d43254430ddd91510c3766454430dd591510c3746454430dd98d510c3774354430dd90d510c3754354430dd10d510c3776254430dd989510c3756254430dd189510c3774254430dd909510c3754254430dd109510c3773254430dd8c9510c3753254430dd0c9510c3766054430dd181510c3743054430af990510c2bd6414430cf950510c33d5414430bb988510c2ed6214430db948510c36d5214430bd984510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c36e52d0430db54b410c37651d0430dd547410c27f65904309f996410c27d6590430cf952410c33d5490430db94a410c36d5290430dd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c36e5250430db549410c3765150430dd545410c27f65104309f994410c27d6510430cf950410c33d5410430b798c410c2dd6310430bb988410c2ed6210430db948410c36d5210430dd944410c3755110430be980410c2f96010430cf953310c33d54cc430db94b310c36d52cc430dd947310c37551cc430be983310c2f960cc4309f596310c33e548c430cf552310c36e528c430db54a310c375518c4309fd95310c33e544c430cf551310c36e524c430db549310c376514c430cf950310c33d540c430db948310c36d520c430dd944310c375510c430be980310c2f9600c4309fd97210c27e65c84309f597210c33e54c8430cf553210c36e52c8430db54b210c37651c8430dd547210c27f65884309
  | 25 => 0x33c6355030cfd89540c33e6255030cf589540c33c6255030cfd85540c33e6155030cf585540c33c6155030cf981540c33c6055030cf0c1540c2be6415030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6415030cf990540c23e64150309f98c540c35e63150309798c540c27e6215030db988540c26e62150309f588540c36d62150309b588540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c309f592530c27d65d0c30cf953430c33d54d0c30bb98b430c2ed62d0c309fd96430c27d6590c30cf952430c33d5490c30d794e430c2fa6090c30be582430c27f6550c30cf951430c33d5450c30d794d430c2f76150c30bd185430c27f6510c309f594430c33e5410c30cf550430c2fa6010c30be580430c2be64d4830af593520c33e54d4830cf553520c2f661d4830bd587520c33e5494830cf552520c36f52948309f992520c27d64948309f986520c27d6194830dbd52520c36e5494830eb952520c32e5494830db552520c3ad5494830cb552520c36c5494830f318e520c36f6494830db992520c36d6494830db192520c36c6394830dbd0e520c36e4394830db50e520c36c4394830dbd86520c36e6194830db586520c36c6194830db982520c36c6094830cf951520c33d54548309fd91520c27c64548309fd85520c27c6154830dbd95520c36f5454830db951520c3ae5454830cb951520c36d5454830eb551520c32d5454830db151520c3cc6354830dbd91520c36e6454830db591520c36c6454830db98d520c36f4354830db90d520c36d4354830db10d520c36f6154830db985520c36d6154830db185520c36e6054830db181520c36c3054830af990520c2bd6414830cf950520c33d5414830bb988520c36d5214830bd984520c2f561148309fd97420c27e65d08309f597420c33e54d0830cf553420c2de63d0830b758f420c36e52d0830db54b420c27f65908309f996420c27d6590830cf952420c33d5490830db94a420c36d52908309fd95420c27d65508309f195420c33e5450830cf551420c2df6350830b718d420c36e5250830db549420c2f76150830bd185420c2fb6050830be181420c27f65108309f994420c27d6510830cf950420c33d5410830db948420c36d5210830cf953320c33d54cc830d794f320c36e52cc830db54b320c2fa60cc830be583320c27d658c830cf952320c33d548c830db54a320c2dd658c830d7596320c25d658c830d7d52320c39e548c830d7552320c39d548c830c7552320c2de628c830f394a320c35d528c830f354a320c34d528c830b7582320c27f654c830cf951320c33d544c830d794d320c36e524c830cf950320c33d540c830db948320c36d520c830f34c8320c2fa600c830be580320c35f540c830e7950
  | 26 => 0x24c930f6d81324c2dc604c930f6181324c27e650c930b798c324c36f520c930f34c8324c36f52d4530db14b514c27e64d45309f593514c35e43d4530d750f514c27e62d45309f58b514c2ee6294530bb58a514c36f5294530db14a514c3775194530afd91514c2bc6454530bbd89514c2ec6254530dbd49514c36c5254530dbd48514c36c5214530dd544514c27e64145309f590514c27e62145309f588514c27e65d05309f597414c27c65d0530b798f414c2dd63d0530dbd4b414c36c52d0530ddd47414c37451d05309f996414c27d65905309f196414c33f5490530cf152414c36f5290530db14a414c27f65505309f995414c27c6550530dbd49414c36c52505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c2ee6210530bb588414c36f5210530db148414c3775110530dd144414c2fa6010530be580414c27e65cc530dbd4b314c36c52cc530dbd4a314c36c528c530ddd46314c374518c530be982314c2f9608c530dbd49314c36c524c530ddd45314c374514c530bed81314c2f8604c5309f994314c36f520c530db148314c27e65c85309f597214c27c65c8530b798f214c2dd63c8530dbd4b214c36c52c85309f996214c27d65885309f196214c36f5288530db14a214c27f65485309f995214c27c6548530dbd49214c36c52485309f994214c27d65085309f194214c2de6308530b758c214c36f5208530db148214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d0130e750f404c36f52d0130db14b404c27e6590130dbd4a404c36c5290130bd986404c2f561901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c39d4350130dbd49404c36c52501309f994404c2de6310130b758c404c2ee6210130bb588404c36f5210130db148404c2f66110130bd584404c36f52cc130db14b304c3da43cc130f650f304c3eb52cc130fa14b304c3db32cc130f64cb304c36f528c130db14a304c2f6618c130bd586304c2df648c130b7592304c2dd628c130f3d4a304c35c528c130f314a304c34c528c130f5986304c3d5618c130f6d42304c2ee62d5030bb58b540c2f661d5030bd587540c27e63d5030d798f540c27e62d5030db98b540c26e62d50309f58b540c36d62d50309b58b540c27e61d5030dd987540c27661d50309f587540c37561d50309d587540c27e60d5030de983540c27d6595030cfd52540c27e62950309f58a540c27e61950309f586540c23d6595030cf98e540c33c6395030cfd8a540c33e6295030cf58a540c33c6295030cfd86540c33e6195030cf586540c33c6195030cf982540c33c6095030cfd91540c27f63550309f58d540c27f62550309f189540c27f61550309f185540c33f6555030cf98d540c
  | 27 => 0x30f5947308c3d551cc230be597308c37965cc230fc947308c3f151cc2309f98b544c27d62d51309f987544c27d61d5130cfd52544c2ee6295130bb58a544c27e64951309f58e544c35d63951309f98a544c36e62951309b98a544c27d6295130db58a544c26d62951309f986544c27d61951309f582544c3796095130bbd89544c2ec6255130bdd85544c2f46155130cfd91544c27f6355130d7d8d544c27f6255130dbd89544c26f62551309f189544c36c62551309b189544c27f6155130ddd85544c27761551309f185544c37461551309d185544c27f6055130ded81544c27e6515130cf550544c33e64151309f98c544c35d63151309f18c544c27e62151309f588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30bb98b434c2ed62d0d30be983434c2f960d0d309f996434c2de6590d30d7996434c2dd6490d30d7952434c35c5490d30b758a434c2de6090d309f195434c33f5450d30cf151434c2f76150d30bd185434c2fb6050d30be181434c35c6550d3097195434c39f6450d30e7d51434c35e5450d30d7151434c39c5450d30b7d89434c3d76150d30f5185434c3db6050d30b7181434c3d86050d309f994434c2de6310d30e750c434c27e64d49309f593524c27e61d49309f587524c36f54d4930db953524c36d54d4930db153524c3cf63d4930f390f524c3cd43d4930dbd93524c36e64d4930db593524c36c64d4930dbd8f524c36f43d4930db90f524c36d43d4930db10f524c36f61d4930db987524c36d61d4930db187524c36f60d4930db583524c36f5294930db548524c27e64149309f590524c35e4314930d750c524c27e61149309f584524c2ee6514930db994524c36f5414930db950524c36d5414930db150524c3cd6314930f390c524c3cd4314930dbd90524c36e6414930db590524c36c6414930dbd8c524c36f4314930db90c524c34e4314930db50c524c34d4314930db10c524c36f6114930db984524c36d6114930db184524c36f6014930db580524c36d30149309f997424c27d65d09309f197424c2de63d0930b758f424c36f52d0930db14b424c27e65909309f596424c27c6590930b798e424c2dd6390930dbd4a424c36c52909309fd95424c27e65509309f195424c36f5250930db149424c2f76150930bd185424c27e65109309f594424c27c6510930b798c424c2dd6310930dbd48424c36c5210930be980424c2f960109309f997324c36c52cc930b7997324c35e65cc93097997324c2df64cc930b7593324c3cf52cc930d714b324c3cc52cc930d314b324c3ce42cc930f350b324c2de60cc930b758e324c36f528c930db14a324c2fa608c930be582324c36f524c930db149324c2fb604c930be181324c2df644c930b7591324c3cf624c930f3d49324c35c524c930f3149324c34c5
  | 28 => 0x951428c33d5450a30b7d8d428c2dc6350a30db949428c36d5250a30bdd85428c2f46150a309fd94428c27e6510a309f594428c2fa6010a30be580428c36e528ca30db54a328c2fa608ca30be582328c35f548ca30d7552328c3ce528ca30d754a328c3cd528ca30f6982328c2dd608ca30f6582328c36e524ca30db549328c2fb604ca30be181328c3cd320ca30b7594328c35d650ca30d7d50328c35d540ca30f3988328c3cf520ca30d7548328c3cc520ca30f3908328c3cd420ca30b7580328c37751946309f992518c27d64946309f98a518c27d6294630ddd52518c3765494630dd552518c3745494630ddd4a518c3765294630dd54a518c3745294630f58ca518c3d43294630ddd92518c3766494630dd592518c3746494630ddd8e518c3774394630dd90e518c3754394630dd10e518c3776294630dd98a518c3756294630dd18a518c3774294630dd90a518c3754294630dd10a518c3773294630dd8ca518c3753294630dd0ca518c3766094630dd182518c27f64546309f191518c27f62546309f189518c3776554630ddd51518c3765454630dd551518c3745454630ddd49518c3765254630dd549518c3745254630f58c9518c3d43254630ddd91518c3766454630dd591518c3746454630dd58d518c3774354630dd90d518c3754354630dd10d518c3776254630dd989518c3756254630dd189518c3774254630dd909518c3754254630dd109518c3773254630dd8c9518c3753254630dd0c9518c3766054630dd181518c37551146309fd97418c27e65d06309f597418c37651d0630dd547418c27f65906309f996418c27d6590630dd946418c37551906309fd95418c27d65506309f195418c2df6350630b718d418c3765150630dd545418c27f65106309f994418c27d6510630b798c418c2dd6310630bb988418c2ed6210630dd944418c3755110630be980418c2f96010630dd947318c376518c630dd546318c2fa608c630be582318c376514c630dd545318c2fb604c630be181318c375510c6309fd97218c27e65c86309f597218c37651c8630dd547218c27f65886309f996218c27d6588630b798e218c2dd6388630dd946218c37551886309fd95218c27d65486309f195218c2df6348630b718d218c3765148630dd545218c27f65086309f994218c27d6508630dd944218c3755108630be980218c2f96008630cfd53408c33c54d0230dd947408c37551d0230cf952408c33d5490230b798e408c2dd6390230bd986408c2f56190230dd946408c3755190230cfd51408c33c5450230dd945408c3755150230cf950408c33d5410230b798c408c2dd6310230bb988408c2ed6210230bd984408c2f56110230dd944408c3755110230dd947308c37551cc230b7597308c35d65cc230d7d53308c35d54cc230b798b308c35d52cc2
  | 29 => 0x2cc27c6454b309fd8552cc27c6154b30db54852cc27f65d0b309f99742cc27d65d0b30b798f42cc2dd63d0b309fd9642cc27e6590b309f59642cc2de6390b30b758e42cc27f6550b309f59542cc27c6550b30bdd8542cc2f46150b30bed8142cc2f86050b309fd9442cc27e6510b309f59442cc2de6310b30b758c42cc36e52ccb30db54b32cc2fa60ccb30be58332cc2df64ccb30b759332cc35e52ccb30f394b32cc3cd52ccb30f390b32cc3cd42ccb30b798332cc3da60ccb30f658332cc2df654cb30d7d9532cc2df644cb30b759132cc3cf624cb30f3d4932cc35e524cb30f314932cc2dc604cb30db94832cc36d520cb30f34c832cc2fa600cb30be58032cc37751947309f99251cc27d64947309f98a51cc27d62947309fd9151cc27c6454730d790d51cc35d43547309fd8951cc27c6254730dd54451cc27f65d07309f99741cc27d65d0730b798f41cc2dd63d07309fd9641cc27e65907309f59641cc27f65507309f59541cc27c65507309fd9441cc27e65107309f59441cc2de6310730b758c41cc2ee6210730bb58841cc2fa6010730be58041cc37651cc730dd54731cc2fa60cc730be58331cc376510c730dd54431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730b798f21cc2dd63c87309fd9621cc27e65887309f59621cc2fa6088730be58221cc27f65487309f59521cc27c65487309fd9421cc27e65087309f59421cc2de6308730b758c21cc33e54d0330cf55340cc2de63d0330b758f40cc39d43d0330bd98640cc2f56190330cf95140cc33d5450330b7d8d40cc2dc6350330e750d40cc2de6310330b758c40cc2ee6210330bb58840cc2f66110330bd58440cc2f661d5230bd587548c35d63d52309f98b548c27d62d52309f987548c37661d52309d987548c27d61d5230dd587548c27561d5230de983548c33f54952309f98a548c27d62952309f986548c27d6195230cfd91548c27f62552309f189548c27f61552309f185548c33d5415230bb988548c2ed6215230bd984548c2f56115230cf990548c35d63152309f988548c36e62152309b988548c27d6215230db588548c26d62152309f984548c37661152309d984548c27d6115230dd584548c2756115230de980548c33e54d0e30cf553438c2ee62d0e30bb58b438c2fa60d0e30be583438c33e5450e30cf551438c2f76150e30bd185438c2fb6050e30be181438c2f661d4a30bd587528c36f5294a309f992528c27d6494a309f986528c27d6194a309fd91528c27c6454a309fd85528c27c6154a30af990528c2bd6414a30db548528c2f66114a30bd584528c27f65d0a309f997428c27d65d0a30cf953428c33d54d0a30b798f428c2dd63d0a309fd96428c27e6590a309f596428c36e5290a30db54a428c27f6550a309f595428c27c6550a30cf
  | 30 => 0x7c654c440afd9131102bc644c440d794d311035d534c440db949311036d524c440dd9453110375514c4409fd94311027e650c4409f594311035e530c440d754c311036e520c440db5483110376510c440dd544311027f65c84409f997211027d65c8440d794f211035d53c8440db94b211036d52c8440dd947211037551c84409fd96211027e65884409f596211035e5388440d754e211036e5288440db54a21103765188440dd546211027f65484409f595211027c6548440afd9121102bc6448440d794d211035d5348440db949211036d5248440dd945211037551484409fd94211027e65084409f594211035e5308440d754c211036e5208440db54821103765108440dd54421103766194040dd586501035e53d0040d754f401036e52d0040db54b401037651d0040dd547401039e53d0040cf54f401039d53d0040c754f40103ae52d0040cf54b40103ad52d0040cb54b40103b651d0040ed54740102bd6490040cf952401035e5390040d754e401036e5290040db54a40102f66190040bd58640103765190040dd54640102f96490040de95240103ba5490040f694e40103d95390040fa94a40103e95290040fc98640103f16190040fc94640103795190040fc546401037151900409fd95401035e5350040d754d401036e5250040db54940103765150040dd54540102bf6550040cfd95401023f6550040e794d401033d5350040e754d401031d5350040eb949401033d5250040eb549401032d5250040ed94540103b55150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103da5350040f654d40103ea5250040fa54940103f25150040de54540103f15150040dc545401035e63d53309f98b54cc27d62d53309f98754cc27d61d5330de58354cc33f5495330bb98a54cc2ed6295330d798e54cc27e6295330db98a54cc26e62953309f58a54cc36d62953309b58a54cc27e61953309f58654cc2f76155330bd18554cc33f64553309fd8954cc27c62553309fd8554cc37761553309dd8554cc27c6155330dd18554cc2746155330cf55054cc33e6415330d798c54cc27e62153309f58854cc27e61153309f58454cc3796015330cfd5343cc33c54d0f30bb98b43cc2ed62d0f30cf95243cc33d5490f30be98243cc2f96090f30d759643cc35e5490f30e795243cc39d5490f30d715243cc2dd6290f30b798243cc3da6090f30f658243cc33f5450f30cf15143cc2f76150f30bd18543cc2df6550f30d7d9543cc39f6450f30e7d5143cc35e5450f30d715143cc39c5450f30b7d8943cc3d76150f30f518543cc2dc6050f30cf95043cc33d5410f30e750c43cc2fa6010f30be58043cc36f5294b309f99252cc27d6494b30d790e52cc35d4394b309f98652cc27d6194b309fd915
  | 31 => 0x90840d794e421035d5390840db54a421027f6550840cf951421035e5350840d754d421036e5250840bdd8542102f46150840d794c421035d5310840db948421036d5210840be98042102f960108409fd97321027e65cc8409f597321035e53cc840d754f321036e52cc840db54b321027f658c8409f996321027d658c840d794e321035d538c840db94a321036d528c8409fd95321027d654c8409f195321035e534c840d754d321036e524c840db54932102fb604c840be181321027f650c8409f994321027d650c840d794c321035d530c840db948321036d520c840f34c832102de63d4440b758f511035e53d4440d754f51102ee62d4440bb58b511036e52d4440db54b511035e5394440d754e511036e5294440db54a511037751944409f98e511027d63944409f98a511027d6294440ddd4e51103765394440f594e51103565394440dd54e51103d55394440d554e51103745394440ddd4a51103765294440f994a51103665294440dd54a51103e55294440d954a51103745294440dd19251103776394440dd98e51103756394440dd18e51103774394440dd90e51103754394440dd10e51103776294440dd98a51103756294440dd18a51103774294440dd90a51103754294440dd10a51103773294440dd8ca51103753294440dd0ca51103766094440dd182511035e5354440d754d511036e5254440db549511027f63544409f18d511027f62544409f18951103776554440ddd4d51103765354440f594d51103565354440dd54d51103d55354440d554d51103745354440ddd4951103765254440f994951103665254440dd54951103e55254440d954951103745254440dd99151103776354440dd98d51103756354440dd18d51103774354440dd90d51103754354440dd10d51103776254440dd98951103756254440dd18951103774254440dd90951103754254440dd10951103773254440dd8c951103753254440dd0c951103766054440dd18151103744054440b798c51102dd6314440d794c511035d5314440bb98851102ed6214440db948511036d5214440bd98451103755114440d794f411035d53d0440db94b411036d52d0440dd947411037551d0440be98341102f960d04409f596411035e5390440d754e411036e5290440db54a411037551904409fd95411035e5350440d754d411036e5250440db54941103765150440b798c41102dd6310440d794c411035d5310440bb98841102ed6210440db948411036d5210440dd94441103755110440ed50441102fa6010440be580411027f65cc4409f997311027d65cc440d794f311035d53cc440db94b311036d52cc440dd947311037551cc4409fd96311027e658c4409f596311035e538c440d754e311036e528c440db54a3110376518c440dd546311027f654c4409f59531102
  | 32 => 0x9f19731502be64cc540af593315039d43cc540ddd47315037451cc5409f996315027d658c5409f196315035f538c540d714e31502fa608c540be582315027f654c5409f995315027c654c540e750d315027e650c5409f594315027c650c540af99031502bd640c540d7d4c315035c530c540ddd443150374510c540be98031502f9600c5409f997215027d65c85409f19721502be64c8540af59321503ad42c8540ddd47215037451c85409f996215027d65885409f196215036f5288540db14a21502fa6088540be582215027f65485409f995215027c6548540eb509215027e65085409f594215027c6508540af99021502bd6408540dbd48215036c5208540ddd4421503745108540be98021502f96008540eed0f40503b943d0140eed0b40503b942d0140be58740502f66190140bd58640502bd6390140af58a40503b66190140ed58640503bb5090140bb98b53102ed62d4c40bd98753102f561d4c40d7d4e531027e6294c409f58a531027e6194c409f586531035c6494c40d7d8a531035e6294c40d758a531035c6294c40d7d86531035e6194c40d7586531035c6194c40d7982531035c6094c409fd89531027c6254c409fd85531027c6154c40d7d95531035e6454c40d7d89531035e6254c40d7589531035c6254c40d7d85531035e6154c40d7585531035c6154c40d7981531035c6054c40d710153102de6314c40d754c53102ee6214c40bb58853102f66114c40bd584531033e54d0c40d794f431035d53d0c40bb98b43102ed62d0c40be98343102f960d0c409f596431035d5390c409fd95431033e5450c40d794d43102f76150c40bd185431035e5310c40d754c43102fa6010c40be58043102de63d4840b758f521035e53d4840d754f52102f661d4840bd587521035e5394840d754e521036f52948409f98e521027d63948409f986521027d6194840dbd4e521036e5394840f394e521034e5394840db54e52103cd5394840d354e521036c5394840db192521036f6394840db98e521036d6394840db18e521036f4394840db90e521036d4394840db10e521036f6194840db986521036d6194840db186521036e6094840db182521035e5354840d754d521027f63548409f18d521027f61548409f185521036f6554840dbd4d521036e5354840f394d521034e5354840db54d52103cd5354840d354d521036c5354840db991521036f6354840db98d521036d6354840db18d521036f4354840db90d521036d4354840db10d521036f6154840db985521036d6154840db185521036e6054840db181521036c4054840b798c52102dd6314840d794c521035d5314840bb988521036d5214840bd98452102f56114840cf95342102de63d0840b758f421035e53d0840d754f421036e52d0840db54b42102fa60d0840be583421027d65
  | 33 => 0x9531902bf644c640af1913190376514c640dd545319027f650c6409f994319027d650c640dd9443190375510c640be98031902f9600c6409fd97219027e65c86409f597219037651c8640dd547219027f65886409f996219027d6588640dd94621903755188640be98221902f960886409fd95219027d65486409f19521902bf6448640af19121903765148640dd545219027f65086409f994219027d6508640dd94421903755108640be98021902f96008640dd947409037551d0240af597409033d65d0240cf54f409033d52d0240ed94740903b551d0240be597409037965d0240be58740903f251d0240fc547409027e62d4d409f58b535027e61d4d409f587535035f5394d40bbd8953502ec6254d40bdd8553502f46154d40d754c535027e6214d409f588535027e6114d409f584535027e65d0d40bb98b43502ed62d0d40af997435033e65d0d40cf14f43503ae62d0d40af58b43503ad62d0d40ab58b43502be60d0d40af592435035f5390d40d714e43502fa6090d40be582435035f5350d40d714d43502f76150d40bd18543502fb6050d40be181435039f6350d40e7d4d435033c5350d40e714d43502bf6250d40edd8543503b46150d40eed8143502bc6050d40ee181435027e6510d40af990435039d4310d409f98f525027d63d49409f987525027d61d4940dbd4a52502df6354940b718d52502f76154940bd185525036d52149409f98c525027d63149409f984525027d61149409f99742502de63d0940b758f42502be65d0940cf997425039e63d0940af58f425039d63d0940a758f425033c52d0940af98342502bd6490940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bdd8542502f46150940bed8142502f86050940afd8d42503af6250940ebd49425033c5250940eb14942503b76150940ed18542503bb6050940af18142503b860509409f99442502be6410940eb508425027e65cc9409f597325027c65cc940af99332502bd64cc940dbd4b325036c52cc940eb50b325027e658c9409f596325027c658c940af99232502bd648c940d7d4e325035c538c940e750e325027f654c9409f995325027c654c940af99132502bd644c9409f994325027d650c9409f19432502be640c940af590325035f530c940d714c325039d430c940dbd48325036c520c940eb50832503cd320c940be98032502f9600c9409f98f515027d63d45409f98b515027d62d4540ddd4651502df6354540b718d51502ef6254540bb189515037551145409f98c515027d63145409f988515027d6214540de580515027e65d0540ddd4641503745190540be98241502f96090540ddd4541503745150540bed8141502f860505409f99441502de6310540b758c41502ee6210540bb58841502fa60105409f997315027d65cc54
  | 34 => 0xd036e52c8740db54b21d03ad42c87409fd9621d027e65887409f59621d027f65487409f59521d027c6548740db94921d036d5248740eb50921d027f65087409f99421d027d6508740af99021d02bd6408740bd98753902f561d4e40d7d4e539027e6294e409f58a539027e6194e409f58653902ef6254e40bb189539027f6254e40dbd89539026f6254e409f189539036c6254e409b189539027f6154e409f185539035d5314e40bb98853902ed6214e40bd98453902f56114e40bb98b43902ed62d0e40d794e439035d5390e40be98243902f96090e40d794d439035d5350e40bdd8543902f46150e40bed8143902f86050e40bd98752902f561d4a40dbd4a529027e6394a409f58e529027e6194a409f58652902df6354a40b718d529027f6354a40d7d8d529025f6354a409f18d529035c6354a409718d529027f6154a409f18552902de6314a40b758c529036d5214a40bd98452902f56114a40b798f42902dd63d0a40db94a429036d5290a40be98242902f96090a40db949429036d5250a40bdd8542902f46150a40bed8142902f86050a409fd97329027e65cca409f597329035e53cca40d754f329027f658ca409f996329027d658ca40db94a329036d528ca409fd95329027d654ca409f195329035e534ca40d754d329036e524ca40db549329027f650ca409f994329027d650ca40f34c832902fa600ca40be580329037751946409f98e519027d63946409f98a519027d6294640de98251903775394640dd94e51903755394640dd14e51903775294640dd94a51903755294640dd14a51903f26094640ddd9251903776394640dd98e51903756394640dd18e51903774394640dd90e51903754394640dd10e51903776294640dd98a51903756294640dd18a51903774294640dd90a51903754294640dd10a51903773294640dd8ca51903753294640dd0ca51903766094640dc982519037460946409fd8d519027c63546409fd89519027c6254640ddd9551903775354640dd94d51903755354640dd14d51903775254640dd94951903755254640dd14951903f26054640dd59151903776354640dd98d51903756354640dd18d51903774354640dd90d51903754354640dd10d51903776254640dd98951903756254640dd18951903774254640dd90951903754254640dd10951903773254640dd8c951903753254640dd0c951903766054640dd18151903755114640dd94741903765190640dd54641902fa6090640be58241903765150640dd54541902fb6050640be18141902de6310640b758c41902ee6210640bb58841903755110640ed50441902f960106409fd97319027e65cc6409f597319037651cc640dd547319027f658c6409f996319027d658c640dd9463190375518c640be98231902f9608c6409fd95319027d654c6409f1
  | 35 => 0x76248421f9d8921087765248421f994921087e63248421f94c921086f76048421ded42500867e64940219f592500867e63940219f58e500867f64540219f191500867f63540219f18d50087766154021ddd0550087744154021dd88550087752154021af99050086bd6414021b798c50086dd6314021de54050086ee62d4f40bb58b53d035f5394f409f98a53d027d6294f409f98653d027d6194f40bdd8553d02f46154f409fd8953d027c6254f409fd8553d03776154f409dd8553d027c6154f40dd18553d02746154f40d754c53d035e53d0f40d754f43d02ee62d0f40bb58b43d02fa60d0f40be58343d033e53d0f40e794f43d039d53d0f40eb98b43d02bd62d0f40eb58b43d02ad62d0f40af98343d03ba60d0f40ee58343d02f76150f40bd18543d02bf6550f40cfd9543d039f6350f40e7d4d43d033e5350f40e714d43d02bf6250f40edd8543d03b46150f40af18143d035e5310f40d754c43d039d4310f40be98043d02f96010f40b798f52d02dd63d4b40dbd4a52d027e6394b409f58e52d027e6194b409f58652d02f76154b40bd18552d027f6354b409f18d52d027f6154b40ddd8552d02776154b409f18552d03746154b409d18552d036d5214b40b798f42d02dd63d0b40db94b42d036d52d0b40be98342d02f960d0b40e798f42d02bd63d0b40e758f42d029d63d0b40cf94b42d03ae52d0b40eb54b42d02be60d0b40ee98342d03b960d0b40bdd8542d02f46150b40afd9542d033f6550b40afd8d42d03af6250b40ebd4942d033e5250b40eb14942d03b76150b40ed18542d02bc6050b40db94842d036d5210b40eb50842d02fa6010b40be58042d027f65ccb409f99732d027d65ccb40af99332d02bd64ccb40db94b32d036d52ccb40eb50b32d027f658cb409f99632d027d658cb40af99232d02bd648cb40d794e32d035d538cb40e750e32d027f654cb409f59532d027c654cb40af99132d02bd644cb40bed8132d02f8604cb409fd9432d027e650cb409f59432d02be640cb40af59032d035e530cb40d754c32d039d430cb40db94832d036d520cb40eb50832d03cd320cb40ddd4651d027e63947409f58e51d027e62947409f58a51d027f63547409f18d51d027f62547409f18951d02de6314740b758c51d02ee6214740bb58851d03755114740dd94741d037551d0740be98341d02f960d0740b798c41d02dd6310740bb98841d02ed6210740dd94441d03755110740be98041d02f960107409fd9731d027e65cc7409f59731d02be64cc740af59331d035e53cc740d754f31d039d43cc7409fd9631d027e658c7409f59631d027f654c7409f59531d027c654c740d794d31d035d534c740e750d31d027f650c7409f99431d027d650c740af99031d02bd640c7409fd9721d027e65c87409f59721d02be64c8740af59321
  | 36 => 0x50219f580540877960150219e580540867e64d4c219f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530867f6454c219f191530875f6354c219fd81530867c6054c21af99053086bd6414c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6314c21d798c530867e6214c21db988530867e6114c21dd984530867e6014c21de980530867a6014c219f58053087796014c219e580530867f65d0c219f997430867d65d0c219f197430873e54d0c21cf55343086ee62d0c21bb58b430867f6590c219f996430867d6590c219f196430875e5390c21d754e43086ee6290c21bb58a43086f66190c21bd586430867f6550c219f995430867d6550c219f195430873e5450c21cf551430875e5350c21d754d43086f76150c21bd185430867f6510c219f994430867d6510c219f194430867e64948219f592520867e63948219f58e520867d65d0821b798f42086dd63d08219fd96420867d6590821cf952420873d5490821db94a42086f66190821bd586420867f6550821db94942086f761508219fd94420867d6510821cf950420873d5410821eb50842086f66110821bd584420867d65cc8219fd96320867d658c821d794e320875d538c821bd98632086f5618c8219fd95320867f650c8219f594320875e530c821d754c32087cd320c821bd98432086f5610c8219f992510867d64944219f98e510867d63944219f59741086f565d0421dd597410877754d0421dd553410877653d0421dd14f41086f562d0421dd94b41086f560d04219fd96410867d6590421cf952410873d5490421bb98a41086ed6290421bd986410867f65504219fd94410867e65104219f594410867c6510421cf950410873d5410421b798c41086dd6310421bb98841086ed6210421be98041086f96010421bd594410877565104219d59441086f66410421ed99041087775410421ed95041087755410421ed55041087355410421f598c41087d56310421dd94c41087745310421f998841086f56210421f958841087765210421fc98041086f56010421fc58041086f160104219f597310867f658c4219f596310875e538c421d754e31086ee628c421bb58a310867f654c4219fd94310867e650c4219f594310867c650c421d794c310875d530c421bb98831086ed620c421dbd53210876d54c8421f9d0721087e441c8421bb58a210876e5288421bd99221086f46488421bd58a21087765288421f994a21086f560884219fd9521086ef6548421dbd95210866f6548421dbd51210876d5448421bbd85210876e5148421f98c521087e53148421bdd95210877765484219dd9521086f66448421bd19121086f
  | 37 => 0xaf99253486bd6494d21d7d4e534867e6494d21cf992534863e6494d219f592534873d6494d218f592534867e6394d219f58a534876d6294d219f58653487756194d219f982534867d6094d219fd91534867c6454d21d7d8d534867f6254d21dbd89534867f6154d21ddd85534867f6054d219f181534867e6514d21d754c534867e6414d219f590534875e6314d219f980534867d6014d219fd97434867e65d0d219f597434867c65d0d21cfd53434873c54d0d21bb98b43486ed62d0d219fd96434867e6590d219f596434867c6590d21d7d4e434875c5390d219fd95434867e6550d219f595434867c6550d21cfd51434873c5450d21d7d4d434875c5350d21bdd8543486f46150d219fd94434867e6510d219f594434867c6510d21bb98843486ed6210d21bd98443486f56110d219f997424873f54d0921cf15342486de63d0921b758f42486f661d0921bd587424867e6590921bb996424876e6590921bb592424876e5490921db152424876e5390921db14e42486ee61909219f195424873f5450921cf15142486f76150921bd185424876c65509219b19542487af6450921ebd51424876e5450921db15142487ac5450921cb151424876e5350921db14d42487e76150921bb18542487e461509219f99442486ee62109219f997324875f53cc921d714f32486f661cc921bd587324867e658c9219f195324875f534c921d714d32486f7614c921bd185324867e650c921f34c8324867e65d0521cfd53414873c54d0521bb98b41486ed62d05219f996414867f65505219f595414867c6550521cfd51414873c5450521bbd8941486ec62505219f99441486de6310521b758c41486ee6210521bb58841487b54110521be98041486f960105219f997314875f53cc521d714f31486ee62cc521bb58b314867e658c5219fd95314867d654c5219f195314875f534c521d714d31486ef624c521bb189314867e650c521f54c4314877654c8521dd15321487e642c8521f950b21486f560c8521bbd9221486ed6488521f9d46214867e64d41219f593504867e63d41219f58f504876e42d4121db50b504877761d4121ddc87504877b5094121afd9150486bc6454121b7d8d50486dc6354121de540504867e64141219f590504867e63141219f58c504867e63d50219f58f540867e62d5021db98b540867e61d5021dd987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c6355021dd185540867f60550219f181540873d5415021b798c54086dd6315021be98054086f960150219f990540873e64150219f98c540875e63150219798c540867d6315021d758c540865d63150219f988540876e62150219b988540867e6115021dd984540867e6015021de980540867a601
  | 38 => 0xe50c867f64543219f19150c867f63543219f18d50c876e4254321db50950c87756154321ddd0550c87744154321af99050c86bd6414321b798c50c86dd6314321de54050c867e63d52219f58f548876d62d5221dd987548867e60d52219f583548873f54952219f98e548867d63952219f982548867d6095221cfd91548867f63552219f18d548867f60552219f181548873d5415221b798c54886dd6315221be98054886f96015221cf990548867e6315221d798c548865e63152219f58c548875d63152219758c548876d6215221dd984548867e6015221de980548867a60152219f580548877960152219e58054886fa60d4e21be583538867e64d4e219f593538876d62d4e21dd987538867e60d4e21de983538867a60d4e219f583538877960d4e219e583538875f5394e219f992538867d6494e219f982538867d6094e219fd91538867c6454e21d7d8d538867f6054e219f181538875d5314e219f990538867d6414e21d798c538876d6214e21dd984538867e6014e219f580538867f65d0e219f997438867d65d0e219f19743886ee62d0e21bb58b438867f6590e219f996438867d6590e219f196438875e5390e21d754e43886ee6290e21bb58a438867f6550e219f995438867d6550e219f195438875e5350e21d754d43886f76150e21bd185438867f6510e219f994438867d6510e219f19443886f66110e21bd584438873e54d0a21cf55342886de63d0a21b758f42886f661d0a21bd587428873e5450a21cf55142886f76150a21bd18542887ad4210a21d794f328875d53cca21bd98732886f561cca21d794d328875d534ca21bdd8532886f4614ca21f34c8328873e5490621cf55241886ee6290621bb58a418873e5410621cf55041886de6310621b758c41886ee6210621bb58841887b54110621be98041886f96010621d794e318875d538c621bb98a31886ed628c621d794c318875d530c621bb98831886ed620c621f54c431886ed65c8621db597218876f54c8621db55321886f565c8621dd597218877654c8621dd15321886f560c8621b798f50886dd63d4221ded42508867e64942219f592508867e63942219f58e508867f64542219f191508867f63542219f18d50887766154221ddc85508877950142219f98f544867d63d51219f983544867d60d5121cfd5254486de6395121b758e544867e64951219f98e544875e63951219798e544867d6395121d758e544865d63951219f58a544876d62951219f586544877561951219f982544867d6095121cfd91544867f63551219f18d544867f6255121dbd89544867f6155121ddd85544867761551219fd81544867c60551219f994544873d5415121cf990544867e63151219f58c544876d62151219f980544867d60151219f993534867d64d4d219f983534867d60d4d21
  | 39 => 0xc67c6254031dd985500c7774154031dd105500c7763154031dd4c5500c6be6414031af590500c6ee6214031bb588500c7795014031b798f54c86dd63d53219f98f54c875e63d53219798f54c867d63d5321d758f54c865d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c86de6395321b758e54c867e6395321d798e54c865e63953219f58e54c875d63953219758e54c876e62953219f98254c867d6095321cfd9154c867f63553219f18d54c877761553219fd8154c867c6055321cf55054c873e64153219f98c54c867d6315321db98854c877561153219f98054c867d6015321af99353c86bd64d4f219f99353c873e64d4f218f99353c867d64d4f21cf59353c863d64d4f21db98b53c877561d4f219f98353c867d60d4f21d7d4e53c867e6494f219f59253c867e6094f219f58253c867f6454f219f19153c875f6354f219fd8153c867c6054f21d754c53c867e6414f219f59053c875e6314f21db98853c87756114f219f98053c867d6014f219fd9743c867e65d0f219f59743c867c65d0f21d794f43c875d53d0f21bb98b43c86ed62d0f219fd9643c867e6590f219f59643c867c6590f21cf95243c873d5490f21d7d4e43c875c5390f21bd98643c86f56190f219fd9543c867e6550f219f59543c867c6550f21d7d4d43c875c5350f21bdd8543c86f46150f219fd9443c867e6510f219f59443c867c6510f21cf95043c873d5410f21d794c43c875d5310f21bb98843c86ed6210f21b798f42c86dd63d0b21cf95242c873d5490b21bd98642c86f56190b21db59642c876e5490b21eb95242c87ad5490b21db15242c876e5390b21db14e42c86ee6190b21f998642c87e56190b21bd18542c86ef6550b21dbd9542c87af6450b21db95142c876c5450b21db94d42c876c5350b21f9d8542c86ec6150b21f918542c86e46150b21cf95042c873d5410b21bd98442c86f56110b21d794e32c875d538cb21bd98632c86f5618cb21d794c32c875d530cb21f34c832c86f6610cb21bd58432c873e54d0721cf55341c86ee62d0721bb58b41c86f565d0721dd59741c877754d0721ed95341c877554d0721ed55341c877653d0721dd14f41c87e662d0721bd58b41c87e562d0721f990b41c87e542d0721bd58341c873e5450721cf55141c86ef6250721bb18941c86de6310721b758c41c86ee6210721bb58841c86fa6010721be58041c86f56510721dd59441c87b66410721ddd5041c87755410721f598c41c87d56310721dd94c41c87745310721f998841c86f56210721f958841c86e56210721f990841c87e54210721fc98041c86f56010721fc58041c86f16010721d794f31c875d53cc721bb98b31c86ed62cc721d794d31c875d534c721bbd8931c86ec624c721ded4250c867e64943219f59250c867e63943219f58
  | 40 => 0x50141319f990504c67d64141319f988504c67d62141319f98f540c75e63d50319f98b540c67d62d50319f987540c77661d50319f983540c67d60d50319f596540c73f54950319f98a540c67d62950319f982540c67d6095031cfd91540c67f62550319f189540c77461550319fd81540c67c6055031cf550540c6ee6215031bb588540c6fa6015031be580540c67e6415031cf990540c67e6315031d798c540c65e63150319f988540c76e62150319b988540c67d6215031db588540c66d62150319f984540c77661150319f980540c77a60150319e980540c67d6015031de580540c67960150319f992530c67d6494c319f597430c6ee62d0c31bb58b430c67f6590c319f596430c73e5490c31cf552430c75e5390c31bd986430c6f56190c319fd95430c75e5350c31bdd85430c67f6510c319f594430c73e5410c31cf550430c79d4310c31bd984430c6f56110c31dbd4a520c67e64948319f592520c67e60948319f582520c67f64548319f191520c67f60548319f181520c6be6414831af590520c76d5214831be980520c6f960148319fd97420c67e65d08319f597420c73e54d0831cf553420c6de63d0831b758f420c67f65908319f996420c67d6590831b798e420c6dd6390831db94a420c76d5290831bd986420c6f561908319fd95420c67d65508319f195420c73e5450831cf551420c76e5250831db549420c6f76150831bd185420c67f65108319f994420c67d6510831db94b320c76d52cc831bd987320c6f561cc8319f596320c67f654c831db948320c76d520c831f34c8320c6f6610c831bd584320c67e64944319f592510c67d65d0431bd597410c77565d0431ddd53410c77554d0431bd58f410c77653d0431dd94b410c6f560d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd6390431bd986410c67f65504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431bb988410c6ed6210431be980410c6f96010431bd594410c77565104319d594410c6f66410431ed990410c7775410431ed950410c7755410431ed550410c7355410431f598c410c6f56310431f558c410c7765310431f9988410c7e56210431dd948410c7f26010431bd580410c7f16010431bc580410c75f54cc431d7553310c7d741cc431f5107310c6dd638c431d794e310c6f6648c431bd192310c6f5638c431dd94e310c7d6538c431bd582310c67f654c431b7d95310c75f654c43197d95310c75f544c431d7551310c6df614c431d7945310c6f7654c431ddd95310c677654c431bd991310c6f4644c431bdd8d310c7d7634c431dd94d310c7d6534c431f5cc9310c7d5324c431bdd81310c77b50940319f992500c67d64940319f98a500c67d62940319fd91500c67c64540319fd89500
  | 41 => 0xa319fd94428c67e6510a319f594428c6f66110a31bd584428c76e528ca31db54a328c6f6618ca31bd586328c76e524ca31db549328c6f7614ca31bd185328c7cd320ca31cf952418c73d5490631b798e418c6dd6390631cf950418c73d5410631b798c418c6dd6310631bb988418c6ed6210631ed504418c6fa6010631be580418c6dd65cc631d7597318c75f54cc631d7553318c6f565cc631dd597318c77654cc631dd153318c6f560cc631bb98b508c6ed62d4231ded42508c67e64942319f592508c67e62942319f58a508c67f64542319f191508c67f62542319f189508c7766154231ddcc5508c77950142319f98b544c67d62d51319f983544c67d60d5131cfd52544c6ee6295131bb58a544c67e64951319f58e544c75d63951319f98a544c76e62951319b98a544c67d6295131db58a544c66d62951319f586544c77561951319f982544c67d6095131cfd91544c67f6355131d7d8d544c67f62551319f189544c67f6155131ddd85544c67761551319fd81544c67c60551319f994544c73d5415131cf990544c75d63151319f988544c67d62151319f980544c67d60151319f997434c73f54d0d31cf153434c6ee62d0d31bb58b434c6f661d0d31bd587434c67e6590d31b7996434c75e6590d31b7592434c75e5490d31d7152434c6de6190d319f195434c73f5450d31cf151434c6f76150d31bd185434c75c6550d3197195434c79f6450d31e7d51434c75e5450d31d7151434c79c5450d31c7151434c7d76150d31b7185434c7d46150d319f994434c6de6310d319f993524c67d64d49319f983524c67d60d4931af992524c6bd6494931dbd4a524c76d52149319f990524c67d6414931d790c524c75d43149319f980524c67d60149319f997424c67d65d09319f197424c73f54d0931cf153424c6de63d0931b758f424c67e65909319f596424c67c6590931dbd4a424c76c52909319fd95424c67e65509319f195424c73f5450931cf151424c76f5250931db149424c6f76150931bd185424c67e65109319f594424c67c6510931b798c424c6dd6310931bd984424c6f561109319f997324c76f528c931db14a324c6f6618c931bd586324c76f524c931db149324c6f7614c931bd185324c67e650c931f34c8324c67e65d0531cfd53414c73c54d0531b798f414c6dd63d05319f996414c67f65505319f595414c67c6550531cfd51414c73c5450531b7d8d414c6dc63505319f994414c6de6310531b758c414c6ee6210531bb588414c7b54110531be980414c6f96010531dd953314c77454cc531f590f314c7d543cc531bd583314c6df648c531b7592314c7d7518c5319f993504c67d64d4131d790f504c75d43d41319f98b504c67d62d4131ddd87504c77731d4131ded42504c6bf6454131af191504c6ef6254131bb189504c779
  | 42 => 0xd58643cc75d6590f31d795243cc79e5490f31e755243cc75c5490f31b798643cc7d66190f31f558643cc6f46150f31b7d9543cc75f6550f31e7d9143cc75e5450f31d715143cc7d76150f31b718543cc7d46150f31b518543cc73e5410f31cf55043cc6f66110f31bd58443cc6be64d4b31af59352cc76f5294b319f99252cc67d6494b31d790e52cc75d4394b319f98252cc67d6094b319fd9152cc67c6454b319fd8152cc67c6054b31db54852cc67f65d0b319f99742cc67d65d0b31b798f42cc6dd63d0b31db94b42cc76d52d0b319fd9642cc67e6590b319f59642cc73e5490b31cf55242cc6f66190b31bd58642cc67f6550b319f59542cc67c6550b31bdd8542cc6f46150b319fd9442cc67e6510b319f59442cc73e5410b31cf55042cc6de6310b31b758c42cc76e5210b31db54842cc76e52ccb31db54b32cc6f661ccb31bd58732cc76e520cb31db54832cc7cd320cb31bd98432cc6f5610cb31cf95341cc73d54d0731b798f41cc6dd63d0731bd59741cc77565d0731ddd5341cc7b654d0731dd55341cc7b554d0731f598f41cc6f563d0731f558f41cc7d643d0731f550f41cc77652d0731bd58341cc73e5450731cf55141cc6df6350731b718d41cc6de6310731b758c41cc6ee6210731bb58841cc6fa6010731be58041cc6f56510731dd59441cc7b66410731ddd5041cc7755410731f598c41cc6f56310731f558c41cc6d56310731f590c41cc7d54310731f998841cc7e56210731dd94841cc7f26010731bd58041cc7f16010731bc58041cc77b50943319f99250cc67d64943319f98a50cc67d62943319fd9150cc67c6454331d790d50cc75d43543319fd8950cc67c6254331dd58550cc7774154331dd10550cc6be6414331af59050cc6ee6214331bb58850cc7795014331d758f548c67e62d52319f58b548c77661d52319f983548c67d60d5231cfd52548c67e62952319f58a548c67e60952319f582548c73f64552319fd89548c67c62552319fd81548c67c6055231cf550548c6ee6215231bb588548c6fa6015231be580548c73e6415231d758c548c67e6215231db988548c66e62152319f588548c76d62152319b588548c77661152319f980548c77a60152319e980548c67d6015231de580548c6796015231cf953438c73d54d0e31bb98b438c6ed62d0e31bd987438c6f561d0e31cf951438c73d5450e31bdd85438c6f46150e31e750c438c6fa60d4a31be583528c76f5294a319f992528c67d6494a319f982528c67d6094a319fd91528c67c6454a319fd81528c67c6054a31db548528c67f65d0a319f997428c67d65d0a31b798f428c6dd63d0a319fd96428c67e6590a319f596428c6de6390a31b758e428c76e5290a31db54a428c67f6550a319f595428c67c6550a31db949428c76d5250a31bdd85428c6f46150
  | 43 => 0x41107d55390441bd98a41107e65290441f954a41106f560904419fd95411075e5350441d754d411076e5250441db54941106bf6550441cfd95411063f6550441e794d411079d5350441eb94941107ad5250441afd85411073e5150441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141106f46350441f594d41107d55350441edd0d41107b54350441bd18941107e65250441f954941107b74250441ed50941106f76050441b798f50106dd63d4041d794f501075d53d4041bb98b50106ed62d4041db94b501076d52d4041d794e501075d5394041db94a501076d5294041ded42501067e63940419f58e501067e62940419f58a501077b5394041de94e50107da5394041d694e50107795394041f654e50107595394041de14e501077b5294041de94a50107ea5294041da94a50107795294041fa54a50107695294041de14a50107f26194041eed0650107f24194041ee50650107f14194041de192501077b6394041de98e50107796394041de18e501077b4394041de90e50107794394041de10e501077b6294041de98a50107796294041de18a501077b4294041de90a50107794294041de10a501077b3294041de8ca50107793294041de0ca50107786194041ded06501077a4194041de506501075e5354041d754d501076e5254041db549501067f63540419f18d501067f62540419f18950107766154041dd90550107754154041ded95501077b5354041de94d50107da5354041d694d50107795354041f654d50107595354041de14d501077b5254041de94950107ea5254041da94950107795254041fa54950107695254041de14950107f26154041eed0550107f24154041ee50550107f14154041de991501077b6354041de98d50107796354041de18d501077b4354041de90d50107794354041de10d501077b6254041de98950107796254041de189501077b4254041de90950107794254041de109501077b3254041de8c950107793254041de0c9501077a6154041dc985501077b4154041de90550107724154041de50550107714154041de10550106de6314041b758c501075e5314041d754c50106ee6214041bb588501076e5214041db54850106fa6014041de54050106ee62d5331bb58b54cc75e63d53319f98b54cc76e62d53319b98b54cc67d62d5331db58b54cc66d62d5331dd58754cc67e60d53319f58354cc73f5495331bb98a54cc6ed6295331d798e54cc67e6295331db98a54cc66e62953319f58a54cc76d62953319b58a54cc67e60953319f58254cc73f64553319fd8954cc67c6255331ddd8554cc67f60553319f18154cc73d5415331cf99054cc75e63153319f98854cc67d6215331dd58454cc67e60153319f58054cc6ee62d0f31bb58b43cc73e5490f31cf55243cc6f66190f31b
  | 44 => 0x67d6094c41f5186531075c6494c41d7d8a531075e6294c41d758a531075c6294c41d7986531075c6194c41d7d82531075e6094c41d7582531075c6094c419fd89531067c6254c41dd185531067f6054c419f181531075f6554c41f5185531075e6454c41d7d89531075e6254c41d7589531075c6254c41d7985531075c6154c41d5185531075c4154c41d7d81531075e6054c41d7581531075c6054c41b798c531075d5314c41bb98853106ed6214c41be98053106f96014c41d794f431075d53d0c41bb98b43106ed62d0c41bd98743106f561d0c419f596431075d5390c419fd95431075e5350c41bdd85431075e5310c41d754c431079d4310c41bd98443106f56110c41b798f52106dd63d4841d794f521075d53d4841be98352106f960d4841d794e521075d5394841dbd4a521067e63948419f58e521067e60948419f582521076f5394841db94e52107ce5394841d394e521076d5394841f354e521074d5394841db14e52107e46194841db192521076f6394841db98e521076d6394841db18e521076f4394841db90e521076d4394841db10e521076e6194841db186521076f6094841db982521076d6094841db182521075e5354841d754d521067f63548419f18d521077461548419fd81521067c6054841dbd95521076f5354841db94d52107ce5354841d394d521076d5354841f354d521074d5354841db14d52107e46154841db991521076f6354841db98d521076d6354841db18d521076f4354841db90d521076d4354841db10d521076e6154841db18552107646154841db105521076f6054841db981521076d6054841db18152106de6314841b758c521075e5314841d754c52106ee6214841db54852106fa6014841be58052106de63d0841b758f421075e53d0841d754f421076e52d0841db54b42106f661d0841bd587421067d6590841d794e421075d5390841db54a421067f6550841d794d421075d5350841db94942106f76150841d794c421075d5310841db948421076d5210841eb50842106f66110841bd584421067f65cc8419f997321067d65cc841af99332106bd64cc841d794f321075d53cc841db94b321076d52cc841bd98732106f561cc8419fd96321067e658c8419f59632106be648c841af592321075e538c841d754e321076e528c841db54a32106f6618c841bd586321067f654c8419f595321067c654c841d794d321075d534c841db949321076d524c841bdd8532106f4614c8419fd94321067e650c8419f594321075e530c841d754c321076e520c841db54832107cd320c841d794f411075d53d0441db94b411076d52d0441e794f411079d53d0441eb94b41107ad52d0441af592411073e5490441d794e411075d5390441db94a411076d5290441bd59241107765490441ed95241106f66390441f594e
  | 45 => 0x58cb41d794e32d075d538cb41bd98632d06f5618cb419fd9532d067d654cb419f19532d06f7614cb41bd18532d067f650cb419f99432d067d650cb41af99032d06bd640cb41d794c32d075d530cb41db94832d076d520cb41f34c832d077b50943419f98e50d067d63943419f98a50d067d62943419fd8d50d067c63543419fd8950d067c6254341dd58550d06de6314341b758c50d06ee6214341bb58850d07795014341d7d4e539067e6294e419f58a539067e6094e419f582539067f6254e419f189539067f6054e419f181539075d5314e41bb98b43906ed62d0e41d794e439075d5390e41bd98643906f56190e41d794d439075d5350e41bdd8543906f46150e41e750c439076f5294a419f98e529067d6394a419f982529067d6094a419fd8d529067c6354a419fd81529067c6054a41db54852906de63d0a41b758f429076e5290a41db54a42906f66190a41bd586429076e5250a41db54942906f76150a41bd18542907ad4210a419fd97329067e65cca419f59732906be64cca41af593329067f658ca419f996329067d658ca41af99232906bd648ca419fd95329067d654ca419f195329067f650ca419f994329067d650ca41f34c832906f6610ca41bd58432906bd65d0641cf59741906f565d0641dd597419077653d0641dd94b41906f560d0641ded42509067e63942419f58e509067e62942419f58a509067f63542419f18d509067f62542419f18950907766154241ddd05509077950142419f98b535067d62d4d419f983535067d60d4d41d7d4e53506ee6294d41bb58a535075d5314d419f988535067d6214d419f980535067d6014d419f99743506ee62d0d41bb58b435075f5390d41d714e43506f66190d41bd586435075f5350d41d714d43506f76150d41bd185435067e6510d419f98f525067d63d49419f983525067d60d4941b798e52506dd6394941dbd4a525076d52149419f98c525067d63149419f980525067d60149419f99742506de63d0941b758f425076f5290941db14a42506f66190941bd586425076f5250941db14942506f76150941bd185425067e65109419f997325067d65cc9419f197325075f53cc941d714f325067e658c9419f596325067c658c941dbd4a325076c528c9419fd95325067e654c9419f195325075f534c941d714d325076f524c941db149325067e650c9419f594325067c650c941af99032506bd640c941f34c832506f6610c941bd584325077453d0541dd14b41506f560d0541edd46415067e63d41419f58f505067e62d41419f58b505077761d4141ddd07505077b5094141b7d8d50506dc6354141bbd8950506ec6254141de540505067e63141419f58c505067e62141419f58850506ee62d4c41bb58b53106fa60d4c41be583531075f5394c419f98a531067d6294c419f9825310
  | 46 => 0x32db952420cbae5490832eb552420cb6c5490832f398e420caed6390832f358e420cacd6390832db94e420cbce4390832f350e420caee60908329fd95420caf76150832bd185420caef6550832dbd95420cbaf6450832db951420cb6c5450832bbd8d420cbce6350832f358d420cb6e5350832f390d420cbcd4350832f9d85420cbe46150832bb181420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420caee6210832b7d93320cadd64cc832f390b320cbcd42cc832b7983320cadd638c832d794e320caef648c832bb592320caed638c832b358e320cb6e538c832f394e320cbce438c832f350e320caee608c8329fd95320cadf654c832d7d95320ca5f654c832b7d91320cadd644c832b7d89320cb5e524c832f3d09320cbce424c832f3509320cbcc424c832b7181320caef654c832dbd95320ca6f654c832bbd91320caed644c832bbd8d320cbcf634c832db94d320cbce534c832f3d0d320cbce434c832f350d320cbcc434c832bb181320cbcf654c832b3d95320cb4f654c832f3d91320cacf644c832f3991320cbcd644c832b3591320cbcc644c832f3d51320cbce544c832f3551320cbcc544c832f3d85320cbce614c832f3585320cbcc614c832f3d81320cbce604c832f3581320cbcc604c832b3181320cbcd32d4432f34ca510cb7751944329f992510ca7d64944329f982510ca7d6094432f34c9510ca7f64544329f191510cb5e4354432d750d510cb6e4254432db509510ca7f60544329f181510cabe6414432af590510cbcd3214432dd544510cafa6014432be580510cbcd32d4032f34ca500caf66194032bd586500cb7b50940329f992500ca7d64940329f986500cb7661940329d986500ca7d6194032dd586500ca756194032f34c9500ca7f64540329f191500cb5e4354032d750d500cb6e4254032db509500cb5f3254032db8c9500cb5d3254032db4c9500cb4d32540329fd85500ca7c6154032af990500cabd6414032f34c8500caf66114032bd584500cb795014032bb98b53d06ed62d4f41d7d4e53d067e6294f419f58a53d067e6094f419f58253d067f6254f419f18953d07776154f419fd8153d067c6054f41d754c53d075e53d0f41d754f43d06ee62d0f41bb58b43d06f661d0f41bd58743d06f46150f41d794c43d075d5310f41bd98443d06f56110f41b798f52d06dd63d4b41dbd4a52d067e6394b419f58e52d067e6094b419f58252d067f6354b419f18d52d07776154b419fd8152d067c6054b41db54852d06de63d0b41b758f42d076e52d0b41db54b42d06f661d0b41bd58742d06f46150b41db94842d076d5210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d076e52ccb41db54b32d06f661ccb41bd58732d067f658cb419f99632d067d6
  | 47 => 0x582544caf76155132bd185544cafb6055132be181544cb3f64551329fd8d544cb5f63551329fd89544cb6f62551329fd85544cb7761551329dd85544ca7c6155132dd185544ca7461551329fd81544cb7b60551329ed81544ca7c6055132de181544ca7860551329f994544cb3d5415132cf990544ca7e61151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d329f996434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d32bdd85434caf46150d329f994434cb9d4310d329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e65909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424caf76150932bd185424ca7e6510932eb508424cb6f54cc932db553324caed60cc932d7d52324cb5d548c932f3d4a324cadd608c9329f993514ca7d64d45329f983514ca7d60d4532ddd46514cafa6094532be582514cb7551145329f990514ca7d64145329f980514ca7d60145329f993504ca7d64d41329f987504ca7d61d4132bd986504caf56194132ded42504cabe6414132af590504caf66114132bd584504cb7950141329f990504cb3e64141328f990504ca7d6414132cf590504ca3d6414132dbcc8504cb5e32141329f984504cb7661141329d984504ca7d6114132dd584504ca7561141329f98f540cb5e63d50329f98b540cb6e62d50329f987540ca7d61d50329f983540ca7d60d50329f596540cb3f5495032d798e540cb6e62950329f986540ca7d61950329f982540ca7d6095032bdd85540caf46155032cfd91540ca7f6155032ddd85540ca7761550329f185540cb7461550329d185540ca7f60550329f181540cb3d5415032bd984540caf56115032be980540caf960150329f990540cb3e64150329f98c540cb5e63150329f988540cb6e62150329f984540cb7661150329d984540ca7d6115032dd584540ca7561150329f980540cb7a60150329e980540ca7d6015032de580540ca7960150329f992530ca7d6494c329f597430caed62d0c329fd96430ca7d6590c32cf952430cb3d5490c32bb98a430caed6290c32d7596430ca5d6590c32b7592430cb5e5490c32e7952430cb9d5490c32d7152430cbce6290c32b758a430cbcd6290c32b358a430cade6090c329fd95430caf76150c32bd185430cadf6550c32d7d95430cb9f6450c32d7951430cb5c5450c32b7d89430cbce6250c32f3589430cbd76150c32f5185430cadc6050c329fd94430ca7d6510c32cf950430cb3d5410c32b798c430caee6210c32bb588430ca7e64948329f592520cb5e4394832d750e520ca7d65d0832b798f420cadd63d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd6390832bb596420cb6d65908329b596420caed64908
  | 48 => 0x4cca7d6015332bb98b43ccb3e5490f32cf55243ccaee6290f32bb58a43ccaf76150f32bd18543ccb3e5410f32cf55043ccb9d4310f32bb98843ccaed6210f32cf95342ccb3d54d0b32b798f42ccadd63d0b32bb59642ccb6d6590b32db95242ccb6c5490b32bb58e42ccaee6090b32cf95142ccb3d5450b32b7d8d42ccadc6350b32bdd8542ccaf46150b32bbd9542ccb6f6550b32ebd9142ccb6e5450b32eb95142ccb2e5450b32eb55142ccb6c5450b32bbd8d42ccbcf6350b32f318d42ccbe76150b32f918542ccaec6050b32af99351ccabd64d4732ddd4651cca7e64947329f59251cca7e60947329f58251cca7f64547329f19151ccb6e4254732db50951cca7f60547329f18151ccb755114732bd98650ccaf56194332ded4250cca7e64943329f59250cca7e6194332dd98650cca7661943329f58650ccb7561943329d58650cca7f64543329f19150ccb6e4254332db50950cca7f61543329f18550ccabe6414332af59050ccaf66114332bd58450ccb795014332bd987548caf561d5232d758f548cb6e62d52329f987548cb7661d52329d987548ca7d61d5232dd587548ca7561d52329f983548ca7d60d5232cfd52548cb5d63952329f986548ca7d61952329f982548ca7d6095232cfd91548ca7f61552329f185548ca7f60552329f181548cb3d5415232cf990548cb5d6315232db988548ca7e61152329f584548ca7e60152329f580548cb3e54d0e32cf553438caee62d0e32bb58b438cadd6590e32d7596438cb5e5490e32d7152438cadd6290e32b7982438cb3e5450e32cf551438caef6250e32bb189438caf76150e32bd185438cb5f6550e32e7d91438cb5e5450e32e7951438cb1e5450e32e7551438cb5c5450e32b7d89438cbcf6250e32f3189438cbd76150e32f5185438cadc6050e32b798f428cadd63d0a32cf952428cb3d5490a32b798e428cadd6390a32bdd85428caf46150a32cf950428cb3d5410a32b798c428cadd6310a32eb508428cadd65cca32d7597328cadf64cca32b7593328cade60cca32bb597328cb6d65cca32dbd53328cb6d54cca32bb583328cabe64d4632af593518cb7751946329f992518ca7d64946329f982518ca7d60946329fd91518ca7c6454632d790d518cb5d43546329fd81518ca7c6054632dd544518caf66194232bd586508cb7b50942329f992508ca7d6494232dbcca508ca7e6194232dd986508ca7661942329f586508cb7561942329d586508ca7f64542329f191508cb5e4354232d750d508cb5f32542329fd85508ca7c6154232af990508cabd6414232bd984508caf56114232de540508ca7e61d51329f587544ca7e60d51329f583544cb3f54951329f992544ca7d6395132d758e544ca5d63951329f58a544cb6d62951329b58a544ca7e61951329f586544ca7e60951329f
  | 49 => 0x7563d4542dd18f5150b7743d4542dd90f5150b7543d4542dd10f5150b7762d4542ddd0b5150b7642d4542ddd835150b7660d4542dd5835150a7560d4542dd1835150b775194542dd5445150a7e63145429f58c5150a7e60145429f5805150af66514542dd9945150b775314542dd94c5150b755314542dd14c5150be56214542f9d085150bb64214542bd5805150b776414542ddd8c5150b766314542dd58c5150b746314542ddd0c5150b764314542dd50c5150b744314542ddd885150b774214542dd9085150b754214542ddd805150b766014542dd5805150a756014542dd1805150b7751d4142dd1475050a7e63d41429f58f5050b7761d41429f9875050a7d61d4142dd1875050af66194142bd5865050b775194142dd1465050b7b5094142b7d8d5050adc6354142bdd855050af46154142ddd455050b745154142b798c5050add6314142bd9845050af56114142ddd445050b745114142de5405050a7e6314142d798c5050a5e63141429f58c5050b5d63141429758c5050a7e6114142dd9845050a7661141429f5845050b7561141429d5845050b5e6395042d758e5410b5f5394c429f9865310a7d6194c429f9825310a7d6094c429fd855310a7c6154c429fd815310a7c6054c42d754c5310af66114c42bd5845310afa6014c42be5805310b5e53d0c42d754f4310aee62d0c42bb58b4310a7d6590c429fd954310af76150c42bd1854310b5e5310c42d754c4310aee6210c42bb5884310ade63d0842b758f4210b9e63d0842e758f4210abd6490842cf9524210aed6490842db9524210bae5490842db94e4210a7f6550842bdd854210af46150842afd954210b3f65508428fd954210abf6250842cf9494210bb76150842ed1854210aef6550842dbd954210a6f6550842bbd914210baf6450842db9514210bae5450842db94d4210baf4350842eb50d4210be76150842f91854210b7751944429f98e5110a7d63944429f9825110a7d60944429fd8d5110a7c6354442db9095110b6d42544429fd815110a7c6054442b798c5110add6314442dd5445110afa6014442be5805110af66194042bd5865010b7b50940429f98e5010a7d63940429f9865010b7661940429d9865010a7d6194042dd5865010a7561940429fd8d5010a7c6354042cfd095010b6e4254042cf5095010b6d42540429fd855010a7c6154042b798c5010add6314042bd9845010af56114042de5405010af661d5332bd58754ccb5e63d5332db58b54cca7e61d5332dd98754cca7661d53329f58754ccb7561d53329d58754cca7e60d53329f58354ccb3f5495332db58a54cca7e61953329f58654cca7e60953329f58254ccb3f64553329fd8554cca7c61553329fd8154cca7c6055332cf55054ccb3e6415332d798c54ccb6d62153329f98454cca7d61153329f9805
  | 50 => 0x94f42d7d8253d0b5e6094f42d758253d0b5c6094f429fd8553d0a7c6154f429fd8153d0a7c6054f42d7d9553d0b5e6454f42d7d8953d0b5d6254f42d7d8553d0b5e6154f42d758553d0b5c6154f42d7d8153d0b5e6054f42d758153d0b5c6054f42d754c53d0b5e53d0f42d754f43d0aee62d0f42bb58b43d0b5d5390f42d794d43d0af76150f42bd18543d0b5e5310f42d754c43d0b9d4310f42bb98843d0aed6210f42b798f51d0add63d4742d794f51d0b5d53d4742d794e51d0b5d5394742ddd4651d0a7e63947429f58e51d0a7e60947429f58251d0b5e5354742d754d51d0a7f63547429f18d51d0a7f60547429f18151d0ade6314742b758c51d0b5e5314742d754c51d0b755114742be98051d0af96014742b798f50d0add63d4342d794f50d0b5d53d4342d794e50d0b5d5394342bd98650d0af56194342ded4250d0a7e63943429f58e50d0a7e6194342dd98650d0a7661943429f58650d0b7561943429d58650d0b5e5354342d754d50d0a7f63543429f18d50d0a7f61543429f18550d0ade6314342b758c50d0b5e5314342d754c50d0af66114342bd58450d0b795014342bd9875390af561d4e42d7d4e5390a7e6194e429f5865390a7e6094e429f5825390b6c6254e429fd855390a7c6154e429fd815390a7c6054e42d754c5390aed62d0e42d794e4390b5d5390e42bb98a4390aed6290e42d794d4390b5d5350e42bbd894390aec6250e42bdd854390af46150e42b798f4290add63d0a42af5974290b3d65d0a42e798f4290b9d63d0a42bb5974290b6d65d0a42bb98f4290bce63d0a42b398f4290bcd63d0a42bb5874290aed60d0a42b798f5190add63d4642ddd465190a7e63946429f58e5190a7e60946429f5825190a7f63546429f18d5190a7f60546429f1815190b755114642bd9865090af56194242ded425090a7e63942429f58e5090a7e6194242dd9865090a7661942429f5865090b7561942429d5865090a7f63542429f18d5090b3f42542429fd855090a7c6154242b798c5090add6314242bd9845090af56114242de5405090b6d62d4d429f9875350a7d61d4d429f9835350a7d60d4d42d7d4e5350af66194d42bd5865350af76154d42bd1855350afb6054d42be1815350b5d5314d429f9845350a7d6114d429f9805350a7d6014d429f9974350aee62d0d42d7d4e4350b5c5390d42bb98a4350aed6290d42d7d4d4350b5c5350d42bbd894350aec6250d42bdd854350af46150d429f9944350b9d4310d42b798f4250add63d0942bb98f4250bce63d0942b398f4250bcd63d0942bb5874250aed60d0942ebd4a4250abd60909429f98f5150a7d63d45429f9835150a7d60d4542ddd4f5150b7653d4542dd54f5150b7453d4542f9d8b5150be742d4542ed90b5150af560d4542ddd935150b7763d4542dd98f5150b
  | 51 => 0x3bb58b4350ede62d0d43f398b4350ece62d0d43f358b4350edd61d0d43b75834350f9f5390d43af5824350e7e61d49439f5875250e7e60d49439f5835250f6f5294943bd9865250ef56194943bdd855250ef46154943bed815250ef86054943db5485250e7e61149439f5845250e7e60149439f5805250e7e62d45439f58b5150e7e60d45439f5835150fd763d4543f5d0f5150fb643d4543ddd4b5150f7652d4543dd54b5150f7452d4543bd5835150f7764d4543ddd8f5150f7743d4543dd90f5150f7762d4543dd98b5150f7562d4543dd18b5150f7760d4543dd9835150f7560d45439d5835150f7460d4543ddd465150f7551145439f9885150e7d62145439f9805150e7d6014543bd9945150f766514543f558c5150fd74314543ed90c5150f775214543dd9485150f755214543dd1485150ef56014543ddd905150f776314543ddd0c5150f764314543dd50c5150f776214543dd9885150f756214543dd1885150f776014543dd9805150f7560145439d5805150f746014543ddd475050f7451d41439f98b5050e7d62d4143ddd875050e7e61d41439f5875050f7461d4143bd9865050ef56194143ddd465050f745194143ded425050eef6254143bb1895050ef76154143bd1855050f775154143dd1455050eee6214143bb5885050ef66114143bd5845050f775114143dd1445050f7950141439f9885050f6e62141439b9885050e7d6214143db5885050e6d62141439f9845050f7661141439d9845050e7d6114143dd5845050e756114143db98a5410f6d6295043bb98b4310eed62d0c43eb98b4310fad62d0c43af5924310f3e5490c43b75924310f5e5490c43e79524310e7f6550c43bdd854310ef46150c43afd954310f3f6550c438fd954310ebf6350c43cf94d4310fb76150c43ed1854310edf6550c43d7d954310e5f6550c43b7d914310f9f6450c43d79514310f9e5450c43f5d854310fd46150c43dbd4a5210f5e4394843d750e5210e7e61948439f5865210e7e60948439f5825210e7f61548439f1855210e7f60548439f1815210f6d5214843bd9845210ef56114843be9805210ef96014843ddd465110e7e62944439f58a5110e7e60944439f5825110f5e4354443d750d5110e7f62544439f1895110e7f60544439f1815110eee6214443bb5885110f755114443be9805110ef96014443bd9865010ef56194043ded425010e7e62940439f58a5010e7e6194043dd9865010e7661940439f5865010f7561940439d5865010f3f4354043d790d5010f3d4354043d750d5010e7f62540439f1895010e7f61540439f1855010eee6214043bb5885010ef66114043bd5845010f795014043d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0b5c6494f42d7d8a53d0b5d6294f42d7d8653d0b5e6194f42d758653d0b5c61
  | 52 => 0x3b0024006005400a004c0070014000000000e005c0030008006000400000040000040013003c0010024000002800b00140000010000000c003002c011002400300600010000000000001b00180030010007001c00100000000018006000c018000c000001400500040020028017005800200080000000005000c015003c0090008000000c002019000f0028000000c011002c00000000140050001000000300000010034000000800000440010008017000c0160070010002c00200140000014000000000c006c00400e8009005800d0034000000c00100000040000001004808f004000000f4000002000200000040000001000000e00680020038003005c0280094003007000a001c00c0080003004c009000000200d8006003402d00000020004018000c0070000013000001a0024000000000000040090040000009c0000008004000400c0004002000800600276f5294b439f98652d0e7d6194b439f98252d0e7d6094b43db19252d0f6f6394b43dbd8652d0f6e6194b43db58652d0f6c6194b43dbd8252d0f6e6094b43db58252d0f6c6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43dbd9552d0f6e6454b43db58d52d0f6f6154b43db98552d0f6d6154b43db18552d0f6f6054b43db98152d0f6d6054b43db18152d0f6d5214b43bb98b51d0eed62d4743db94b51d0f6d52d4743db94a51d0f6d5294743ddd4651d0e7e62947439f58a51d0e7e60947439f58251d0f6e5254743db54951d0e7f62547439f18951d0e7f60547439f18151d0eee6214743bb58851d0f6e5214743db54851d0f755114743be98051d0ef96014743bb98b50d0eed62d4343db94b50d0f6d52d4343db94a50d0f6d5294343bd98650d0ef56194343ded4250d0e7e62943439f58a50d0e7e6194343dd98650d0e7661943439f58650d0f7561943439d58650d0f6e5254343db54950d0e7f62543439f18950d0e7f61543439f18550d0eee6214343bb58850d0f6e5214343db54850d0ef66114343bd58450d0f795014343bb98b4390eed62d0e43af5974390f3d65d0e43eb98b4390fad62d0e43b75974390f5d65d0e43b798b4390fce62d0e43b398b4390fcd62d0e43b75874390edd60d0e43bd9875290ef561d4a43dbd4a5290e7e6194a439f5865290e7e6094a439f5825290e7f6154a439f1855290e7f6054a439f1815290f6d5214a43bb98b5190eed62d4643ddd465190e7e62946439f58a5190e7e60946439f5825190e7f62546439f1895190e7f60546439f1815190f755114643bd9865090ef56194243ded425090e7e62942439f58a5090e7e6194243dd9865090e7661942439f5865090f7561942439d5865090f3f43542439fd895090e7c62542439fd855090e7c6154243bb9885090eed6214243bd9845090ef56114243de5405090eee62d0d4
  | 53 => 0x38003007c007000400a000c000000000201b4016007c0030000008005800000b400700140020000005018000800040060000034001000000040000004002001c00a002400f00080000000000003400300a800b00080070004010000000900ac0030000001001c00100180090070000006400a00200030000000001c00f00000000074000000400100d8000000800500000000058000000c00800100020000013016c0070034019001c00000040140004000000000200200010000000000c0000028006001000a0004000001c000012000000140000010011004800f000800000000020004000007c014002c0040000002005400100280050004004004c0000054001001c0010014019003c01b00000010034000003800400580000004001000800000600140004004000800400500000000033001800000000010004008000400400000000014006000c005002c0080010001000000600540430004004000800100240010018005001400700000000008001000000400140000000001001800e00a40030010002000800000440260004009000c00000f8003000000100d000400080000018001001c00000080080050005001c027000400600b400000000000004007009800300240120008004002800b008800000000140004002000401a001003e0004003003800600f8004001c0030008003000000500000030020036001c0000000016001004d0040000000000600200000014000002000f0000001002c0010020008004c0050008009001000c00140070000000000407300080030038000000c05d0018007000400f0024001000c001001002200000010024000002000500980010044000000400000000170004004000400a000401b000c0490014001000000e00000070004000002001400000030030029000800c009c00100100170018007000001200080040148001000c0020008017002802100dc00500dc00c007c004002801b006400c00b80020000005000c003000c000000c00000000120044001000003e00280000000003001c00a00040070010015000001e0014001002000100000050008011003c000009000300000030014009001401801500110004000000c02a00100010000001000000a0004001000806e002401300740030008001001c028001000e00240010000009003000000080020004000000800c0008002001400801c800a000001600000030000017001001500080050010006001400c0008003004c000004404e000000d00600000000000010000000000020008063013c00600040080000000009c00800b4000014c00c000000800780030010003000400c0000000004c00400200af0018001003c00300a4000005403c00000000000003009c0020054006009400d000c00e000000300100000000027000400a0000
  | 54 => 0x2001000300000000000003002401400340040004001005800300040040000029001c019003800100900000014005007800901780040000001000400a00040000028003007c0020008003004403e000000100240000014000000000100680000000001001400d00180010004000002c001000c0010000000000c010006000300140030000006000400a003002b000c00200000000004007000c005006001f001c0020014002000800000300050014003000000d0004000001004000280060004010018800a001400200040090000014001c01c001000400080000000001000400600680030000000004400000040130044005000400200080b3003800a0030025000000e000000d001801000000000004002007401400080150000005001c0000004004000801b000000100080020090003003c002001001e0008000000001300080390000000000c0050024000000000400180000008011000c001000800d00580000004004001400e0000007025c00000000000000000000000b000401400000090010017000001a001400000080000018000003400c001400a0018002000c00500100140000003004c000001c0140008000001c025016000a00080020000000000c00300140070014000000800b0000001006400e000c001003c0280008004000402f003800c0038000000400f00000000004002007003d003c00100100010024000000c00100740030004000000001f0000002002000100000280008008000000000ac00100540050000001003000000240020044001000c0030014003000002800000010044003000000100040030008003006000000340120000002002400500300a20044009003800000040020000000004c001002000d00ac00401400030004000000800200180010038015000c00d001400f00340020024003007404800000010030002000c02f0014013001002d000000600140070040003001400f00600020004000000c0010070009000c005007c00200000010020001002c003001c000000000500040000020008001c0000004037000000900100000014004007c005000c013000400200c800400100060030007001000000440840020019000c0190038007001400a000801a0024002001c000000004a0000001000001b000400a0044000000c001000c0000008007000400e0014006001400000000070034005004c00200080060018007001c0020008039000c033002800900d401b0064003004800b0004002000400e00000010040000002c00b0000001000800a004c00b00240040004027000400100440000078001002000000100000000000003c01b003800800180040018006003000a0040012000000a000401c0004001001800b0004000000c00400180050020013002000000000070004000003000a0008006
  | 55 => 0x1001000000040000004008000000b00000090000006001400300140010000007000c008000800b00100020040011008400d0064008001c000001000000a40070014006000000000900010000002000001700f4002001401b00000020000005000400000540000000000008c00100d0002004400a008800e0034003000001b001c01b000001f0008000004800400080000000007001400000400040034002000800d00440070058007004000500040170000000003c005000000000000020000001022c00f00040090000006000000500300250000000000804c0018004001000000280010018025000001100000020008002001000f0008008000400c000800900080040048003003c000021c000000c000001800e010400000000020020001000c004003c00c000000000000010004003000800e00080610010003011c0050000002006400300300000110000007000000f800300100000000000014800200000460044040003801400000080008000002c0010040002000000700100160060009003801300000040030021000c07e00000000008004000400000080000000000000801500000020028027003000800500000028001000c0000040033000c005001c058003400b0008003002400100000030030006002401f001c00000100010008005001801700100030004001002800800c0000001c001004c0000000000000c00100040010028005000000400040120000000003400000600000020003001c001000401200040080010014000000000000100000000000004c00080020038000000c002001001300040030000017006000200180060084002008800800040010014008000c020006c014008c0000004008002800f004000600080070020000000c008000000400680160024000003c004009400c007400a000c017000001600080020004000003c027000800a0000003000c02b0034001003000b00080000008000000c00a0038000000400f00400110010010008c0100004003000000f0000001000c00d0004004002000700000090000077000401b0014000002800f0000001000000200100000014000000001c002800000080000018004002c001000800000f400800140090004004001c000004400c0000000002800600540060000000001801000080060020003002c0030000000000000f00000130088023000800000000120000000003c02300040250010000000c0350004007000400e00dc040000c0090068008001c017007800100040200130001007800400000050008022002c0000008000005c0000004001000c0190000003000c00100240030058001005000c002c00100b004d0000014009003200100000008006000002b00000000004005008800200040070004001004c000000000302200020004000003c002001
  | 56 => 0x200030010007002002600080030000004000000101600020004005002401b001802200040010000006001402100180040038001001c0030048000003401400580100008009000003300440100008000004c00d0000009002400a00040000054001001000f00180130028004000c00400000030000001004c000000002200080020008000000000600040010004002008c00e00000130040008005c0000008006000400100000010014004000c030000c008004000100f8004002000300000010008001000c00700500160040006000000c000000501d400100100130004000000400a00000130000009000c0050000005003c004003800000040040074038009400200000010018011001806100840030058002001400200040010000005000800b000c00400040010060002008c00300200070000002000400700a0000000800000ec00300000000004007002800100000000018000002806900200010000009002000000000200010000003000b000000d0004031004c00c000800300600050008002002c000000400000040010000002000000900c8007009c006000001b0004003004000c00880010024000000001500100170018001001c000005c003001c00d0004004007c000000c00000a003d002800000140030020000001400200100000018002001c00b002807d0004000023000000040000004002004c00000f80100000005008003b0000000000000000cc01e002802700040070010000000800500e800400000170014000001800800ac0180034006000000200080010000002000400f001000100000070000011002000000040000018023000c005000401b0000029002000000140250000014000400c0004002000c0170008010000000200080010010003000c000000400b0000002003800500780050008004004803a00000050038006008c0060010004000400000700000000002000000d004c003001800d000000200340030004001000c001008c020000c00400040020034001004c004000c001000c00000900000030000000000d003000a0030001000000200000000024002000401d0014003008c000000c00000040000000001000800200000000000014000000300280060010001000000100000000008003004c014004800c005c01400280090000006019c014001c003008002200240080024006000000b0008001006000500040050034032004801d00080000004001000002c002400b0000000005800e00cc00900b4010000001800000000008001000000b00180020020006000400700240050000001000405e00000070280003000002d0000009007c041000c068001000f005800400400010018001000c012001000000080090000001001c01b0004002000400c0034000000c0000054001005c0110000003003c00
  | 57 => 0x18000802000040000148002000400000880020000003000c000002000300400000000002002800400200000008001001000f001000800140040000068005c00301d400000000010048000000c00300000260000009007c003000000500000180000059000c00300200010000001005c0020000008000c00200040190054014002c000001000100500010008001000c0000014011000000101580190038000000c011000000b001000000040010004002005400a010000d00000050008027003000100040000000008000800c00180010040000002000200200010004001005001e0048003000000400540010024004000400000140180000005000c0000040024000c0010008002007000c001400000600000000003000c0070008000001002400000000008009000c00100100160000009000000000280000028003008c006005c0000010000000400000200030004007001001a0000023000002f001000b00040000004008007801e001c004001800300040000058001003c00700dc00300880040008012000000001ec000000002e00d4016008800100080020008000000400500000000040000005800600000160000000001800800000020008017006800f00080010004000005400001200000008006000400a000800f000c014009c00000080050018001003800200680210004008008c01e0020000004000e00100090050000000000000400000070000001c00400000180000033000805800000020018000005c002000000700040250010001002000000100230214004000001e006400000000010028000000001b0070002000c031003001c001400000b80060020006002000000580040000007000800100c8001001c0060050035004c0020004001002800b0004000008c000000003200000000040000000000000000010044000000801f000003000000030038005000804d001c000000000b001c030001000d000800300000000000006003801600080000044002000801c0030006000400a0018001002c00a00200000008001000c013000004a000400b000000200000100014068000400c00000080004003000c000000000d00100040010006002800a0008000001400000000080000002001c000009400100380250000019000801d01ac0000080005002000600040060004000000000f0030001002c0050028000001000a000402b00f4000006001100000070038015004c029002800b00100000004000001003000040000068009008c008000801200700010010008000000900100030010005001800000240050004001001800a0000002000000f006c002002000000100010000004000000000540050004006000800200080120018003001400400640020004000000402f002000000080000000000004801c000000c000400500
  | 58 => 0x44005003800e0028000000400e00400160048001008c01a001c006000001c009c02201c000100140020000000001c00900440010008002001000200c000101d400a0020003002c00a000000000080090000002001400500180060030001000c000004800100000150020009001c0000038000000c003000001b000002600140110004002004000000000010000000000800100ec00000480000008006007800000d800400000060004006005c0010000014000400700480020000004000001c0028018000000700000000024001001000600480020000000000000400bc00a0014001000400100040030000019001400b00440380000004005802100040090030004003400c00080000000008000c0000000004001000300980240004002000000000380000000011002000200000000010009000c0000000019000003c0004020004400f000c000002c000000c00000040020018011000c014000c00300280020004001000c00100540570100002001c00a000000b000000f0008004000400200bc003001000100100050000007001400e000c0010008004000802f0024006000800000b40000014006000001c0004016000000500ac0020000000000400600000100020002001c0030014015008400200580110004001000800a00300010028012004c0150018002001001e0000005002c0010000032000000f001000300280090008000000000000380000000000000c00f0010001000000800080010000013018800200000010000001007c014000000c000803300540010028001001800100040040000000000000000400010000004003c04f001400000180220028002001400e0004000000400000080010054005002405c0028008001401100140070008000000000300100000008006005c0000018000005c0060010014000c00000a80000004001003800100000200004000000402f000000000240000004000000c001000001000040010004001000c0040038001000000400680030040008007c004000800700080040090014004800000740040024010005c00a0000008000800000080000018000001800a007400000100100000000004c0000034017000402100240120018011001000200e40040014002000c00000140070004008000c000000000000040060000033001400d000402700180010008004000000000280000010000000c01800000000034000004c03c000800100000040000001003401e007402300500000004010000c0000008000002000a00e400000140030034000000c00c0048019000400100080070000003002000000a80000094000003401a0008001005c00e014000b00240000018001000000300080000014002001400d000001c00040590010000003800f003000400380200004001002c008000400600000
  | 59 => 0x6000000000000000172000004db20b8456486ecf3e941000009f8c00006ec0fc40000d4006f72ace000000024871ddc8054e3480000000432cf0988513dd674fcbfe20343692000068f85714bb608b4000285c41c800000688e9c4eb602e956a8e8a136a6cd0000058b07948c1802a89fc2166642d1b0199e3eca00002520cba35843e00038838d21ac06d12fa83b40c480d7cecd834242205d2c47b800049ea03291ce8000000008e0c921b3a000000000000cb510567408fdd239a081642dcba686f500006ee83201a44356e2d7c263a259077896b0083975449b200004ff001751ec88c85bb8e0203c47fa86b38a5d01ac82ed5128e0f2f0643a477b2926583c890c471846b52361838db129e1109aad8433a0d630b4019c85f39433024680a0c3f914b267297192de2bcd2ede1574ea199a3429c08c84c42418303e9868a88011d54b060a933a014f537633e9344097c4d8e398d20c9ccd03260c70a37800434625accbafa91a30c8274806b9a153982260847517cd248242d05ec9e6e35fe8a7943c90ad4f722c0c41005c404929cb03ca81de47229978a4d840519aa07b461a8e6b44e279806129d281ba443d069600280fb27c1057b8c15119685dc19300004cd82e690a12b074da859e12ef900a15a4126425f00002256851cbbea3c313409a30000057c0000000000013c85146a3dd1540fe5575e6e304be9021041a9571393066131b449a8d1e15e709c6a0900000000000000000002088194c00000000000323e27ace151e5c10940000317ab0938965be0a95973a4a5e8528705ab314eb06538d299464208c0000e3b8945546413bc000106d15a800006821c3f00002ec000013b709cc2af02a205832b024dc400001d9000097300001a29236c000057b248b38745a55208a2c00000000158b80002242341953f8d4456e41749290135a26ca1f44000291d3472857c4b58000000049009cc8cce559600007689348000000000049b6c3dbe000000000005396a4b893fa5f3504a00010739e4100002344a850a4e3320000000000001f1cb118000231d4c5860740000000000000003f22486025a209c000000000000000000000004d400000000000534e000016700001c9047e467ea7d04bec7a5d1f68a9036b234800981c912b927b788d01e260b120a94e57a6c101a895ad39f1f643fd63bdc00000004474000000000003de01438000171b2e4290f0000154e0000001400000100050000005002c004000800000f801e000403a0004003000c006000c001001800d00080070000001000800100300170004023000000000740090024004002000200000050098001000400900680030058005008c000000000200640010008014002800c005000500040030018003001c000002c00c00c000000e8001002800000000000014002000400c0
  | 60 => 0x2c0000b233c94000143e800016d026a824f00001dd49c3956ba6933ffc000000010ac000010d0ee104e50000118cd4207470000ab8d0f02132547c3bd521317d050cc268c2740b8238a2000127e25bf000076dc0000a3c20be489006e80f74a90a794000242d0ca088e4f3da72d149e3758a130803084068941fc1d9147c88e243ea8eab07ee9c108c92067292a46b45738daa1ec2568550ba7c50f3ea7c00000a311f1a174439c8ff70ebe1df80bc80002624176c9de00002ca21c54cc2000000009450e8d298a261637c0033016700005a08f08a2a40a780000000000010e4908050a823c51168cc4bbd0f8f000000001d7000056000001374098e30fa1e2826e12893c6a000000011180b3a8b3433e000048904ca55be967c20224374000181e01f4ae95271222409b46d5c19f0acc30cea3c8e6ea8bf000000002e7a99c01a49d242f5297b0f861b6139c8000390c4bcc3389d903d981bbc00000001a5c9af06060000206a80ac00004c33810000076b11263b148f5d45b108d0fd400006789aa929da8a84000125106240b74d1d18d33adcaff8bd718f3335a74b5604130f57e29c70899a45e543a33ad0650000183295c8bfa817534fc4e70e77a21958300000138000058626d84e8fa62246745220f89211f002a000000010fa4a56000000000002bf21efc0002be719e02894000272b000000000002be04112000055c191d27804100384925e1aca4c28ba198b70bea984c30913fa1abc000000018cf521033b944b22c50130a9acb4082a8414c071513d903a1e6a30cc4c027dd05ea61093a39ab627de5c3d5eb8b164baa94f07272743310240491038ad714ac67404b3a6f0050a7870e65800000008c7d2338bbf515086112c823d52f926cf01848000373a2bc039492682496000003da5d200007d01139166f14b698410a3041100007060540a8970000aa64a2890e70eea0b78af8a3b509f8000023f98b600000000000259100000000000058137ac00014ca80000f6251c8a310000000000001530000151218e800026c83aa813d8a9e1408000094c4275000005b683f0d07a47200000000000094800006c0c00000000aa00000683a796000061b0cbda7f5249e5900ca4800000001dbc100ac4700000000dcb80004dea0000000023648940000000097800009e4ca4080000b5e86015d5959100001c7cfde8000000000000000e71349c5efc28b95110ce04cc800012562804a5cd368a1195898611000020c823ee0bc8381185b50a000000000000004c00005069f990386451036410200000727d0c500001ece0000000136e33889814c9d00001fd600000000000000012ac1618000367ea7b138a8a43078205f942a08d64cf60ac1389ab9b425280e13b524fe21b09c30cf698b10a0e65043da8b8b41ac43140002339444447b083f821
  | 61 => 0x3206ec00000f98000000000009a80bc81c9e000000027fa1d82029839881b021e26a7c0000000000000000002bee0000752c00000000000617800000000000a1bc8b2000040ca4d04d34a8d80a2aa6e411200000000422cbb1800000000fa4aa3a82e34ee0000000000000000000e6aa8f90000a048000069f00008ba09d011d52f3407a423b82c703882eb490d1ce92bf0013827d893200c494340369b692d6e540042f1d4f23e036d95018132348c880148c1f180000a10000007ae00003db4a9d000000005d60c2fa0c0000018700f80000537a4ee4000257d0000b12800029022356195000000000cf6000004217382292a92890c1eba0f687e0883212913682000036e000000003fa000001c6000046080001b242ca07a55170800029b2451c5f8822100009ccd15c8e4505ec16694dd0dda21184ef4051ac2b203a0a9000026e5000000000000bd14848a26c43c8cfc165800002bb014227bc000106880003f5e66f53a7000038709448ee1a8ef000009c800012203b78ab84a1f94940bde00001c11a172b340000f4422ad36bc4d50b769d2221c8a78c0002ae2567496ad373883024740000f28109800002b1c2092a9100000000000285a3b3c5aa800007ad2654000077d8dbd36de1c38e408ba14f2e0001341993000005f89270a65f4c8807f487e8000453e64284302b503e2a7140a3009cf1b28000043f1f494dd80001562a623370215b40000575202e68e066ca79a2f4e9da13f880004fdc2e9c5de8d791b8e125c0001cdb3220ad04a85abd80000a3f01681a36530a213cfe72352045e0000ce789520d9471511f48de7043c1cdd52e11fd217e6da11e5931527620340750922620e8204d3e18e983456a0bcd2b8874357a12c016a8e1b444a0018b7d10f6000000000b004b4408c0000b0d80000000450c000000000006e9400021f235860000f9d97d82aca1344eb1a17c1408776919399f430925b491588baa0d98a62c7260ee518848c6d0e329f9000005890da9c7657d48331407a23d20f89d8400027a7359a59dcf9500000000026c00014fe00004d9800012db00007fd4f8390142b14a6dcb3094f51ab271213d28c13000014fd1e99f6648c600001da95c40f4872b8f719397000000005da80004afe15ace2c2bbd00001cb8db200002ffc9bad4319b0c025c7af80000000570e53b000014c104ca04ed62700004cfa48e1419ab6335e643e0ade00000bfa000012d20542fee0001419000046ae09e80002a264fae8758bdd98d0547414a80001ada37e20000e52a3ee06ba0240cdc9e1d0000a96800000002ffaa045427065d3f485974f6d1b0d2bae6ea0ba9897b31962da44fba2ea507800014de25dc000022d40000f90514c000055aab8e0278343407aa070286c0a340000013542c5d703fd20e5254e14e92e4a00715a262
  | 62 => 0x888742a5b3be296e883989603bc2986051311e34b1a0b94c5587561d3eaa1401f0727063e59b51c10d954f585118d700a3a1610a2654c71b01480a90d8c23261b1138738157c956a250418ec3cd8502035636193ba81d1353c30dcf092be9400a3a1cbbb168d20f677886010e5f4a2e765955a069832802d45628213425746b14314858445dcb0ed2ce26901c186d5824980001b6e58cc00017024afc77f05a52a291e4e8bacc388ece21bc880cd7a83714d088f980901fcd3970798c50481191d5c4614f6387c814287e8941192ac372803c83521359024ca6f85d7a31a12e8524108007341cc0226547c1bea0000363c000068d320c98b507d064b04dc05a86c80a3e2cea8be87c48f411f32606489d9bd80ef800000001bbf1c067acd1078def54ae5f101af141410629d6450c043645963b08350074c553a321cf6282680000b0b558d163c00000000bca00004fe069ed562000000004d780000e6827ec6c088fa1f0242101b8c73327f443be000105280002d90098800025443bb049b00bda55403ca0e2437ca9c454263b712f11e622ac057b155f2b55568e1d1023799a624c018f13f59e5627dc0000e7c837a2fc60514000039f21e6000000011b0325c514c2e9800054f800002a081090a382de47db8566117c47980a88a440000000125700000c988add47321b8289c7100cf28d730142000060d04d853bc000000015fe00000000dc80d543e00237c1ed22ac137c00010888b620000905930f8000309e00005ef801227f8030cf7614800748271d25d1008000090091f8ab9e09d881850cc00003a0a570cbfda3423c547664b62a6e4429629d44cf83f047423fd831303c7048a000158d9b0500000304000198b2a2c4bacad2800005229130936986a53060000cbfa0643d9446500948d1b2e0218f4318959200001fc41a4122936ee52c0000118c573a3c7000011a63bba92ecbbb936747609ee93f69ed52b0e2b140000c4a45ea3950e679f8141ea8f8c0001bc40df60c1cbbaa9ac4bac49ac0000000043690c914019694efc58b11f4013116a40b715e70b8f27528500e2c919d16981f9803f1d82157c0000eb89dc900000000000170329a600fc24a80002a48a728094068800000000000000011c869280002594000001cd4e98a74152e6ed473d972e2eb29f7c0000000000000000001588274e9b148dc135c50fe0000c30192b1e30000042000540a5a50d0a7e009e4ba20e851bb0f21233c8eec7ca840f502647094c926ee3dca7c9487d8eba160826783460b67516062992419fb02ab87738781a817217c69f42a404ee00005c90177034717ee215400002844d2e48483c41d16534c02bcd3c259600967eec48c13d223ba7000fad8d212202883927c000025fa0000fee9f5a4ab472c0000000000008df09310000508c2d908c215
  | 63 => 0xa5028f01f58ac7a10b173800000000659000013e0d22880f2de21de4000000012dc08154cf82cb18442c24aba00003faa554107799a815d470f0f5825382030566026793e44bc84a993e92321478a76191698b4b0000a0842c88000000087a4000000000004668d3f800038624b003300ef84a4688e13f917bd1aac7be112008390000759c49004ed000026680001919000000000001f7239640000a031f9407b00000000000031c0000049c000006705125621104212cc7a4cefaa1fc3144469113213243ab0b13cdaf880c1dc82ee848aa7ce27d478dc5328ac92c9a7938faf90ef28be10b092a07cb56cc00007d4029f566416e80002b243f9600012dca32629fe9c904c1a104342ca3d1538a5a822f400014048000000026543de10820000804cf0329500372836c43b824e000000005888c982b3a4ab4fa1102a252627e944e94190abc1300a3e87b946301cc11bc000022ee1c854901b8a55662d089842acf3b722c84589283d0f5858004f800514dc41110a551fd326984eccc189889479823f05801e7e196e5b38b03a0314332a1a03ac230e14d8936ca69000012be3dcd3369d5222a06d38cc980ef07e6b10499babb75300ab7822727a61dbc15f8d789458545a84bc7eb9b473404947c13b800034ac00004481fa0102e32f85109a2a3f5688241e200003464000066e9296394e2cf0c3481532418279856fa98f39ce6c9d3f5000000001cacc638b313e623a147a9000000009ae52cd233c021c0000d8d81821b5aa33c11421dc55a47f911c98f6e061800001c72929000008240002b4600000000e1b000051580000a5e260d38e0994922095d425e830914952a9744423e50e2f800001be6e452a9800000760000f12aa60252473e94f58271166475040001714413a0000000015b02a07cdcccd167620d29ac92d9210e52004300d7e06db4276000000008970000000000016b9000077993458d5000000000000121b08da774c00000000000000051e800000003f80d3420512666061032f27542d1c14903a917e50000ac6039d84ac077c02e4000000030ae35c9128154300ea00000000b811274060c000091331ba52d0c400000271007c8af413894abe9e24eb42b6f285631e8c490a961c0826f113323853ee845c860300002d186774f9b091f1a823610f21834c044600010b18395457a3cd025680001cae00000001d3d44c2a0e810a800002da2e14857850d38b816f89dd84bf1292000148a9eaa3f7237c8fb680001ff8190400001f8184e00014be00000000145000014df3f14000000000002a6c00000002c2f132c7a34f7b80004f14884491f2a05202c0229408106103fe8c407900bd5000074c0b8000003cbe394ca0892e613e422307ad274204d85b100000bfa05a474e02c7ac3952845af06f999c8508e64a4b1714b342de6
  | 64 => 0x10e4807711aaa0652c58f93189031c55c62895440826bd182abe81af8b018b75a1ea4a6032b43332b442f6e4ffc9b1110f10da5e6c92d8523253a8878c19989435061190b6ca3a7193e00010e6a97e000086d80000139290e4b84f3a00002c76000013e0000451000000002c011ee269b0edc21762c9e9ab52e19ac73ffa5698000223600005225186a806057638414a09e3d000032e435a000010360be410c2c031f5a79440000dd300002fa40001db10000728c8b29b1224cea23907c16cc3bac3380ba308ca0000373cc9a000039c21d410d625322b84448d0ce943a40463c3c67ca6534f181e747f911172e384ad545e17c12f9044f45a19eaf0cc66688c369942252862750b8941539c633dd14d87eb4cd450c82cf165e2ca63e8ceb50354324e20d1290876e038eaaf10589b1a1cf2175898482304aee4dbcc8b8b1a3c3e047152c8ce51aa65df955719b62b903d305dd841d37ba1a3d148083b12ba4528777a8ae2c8c83987e387231e6c7570026089b41b206305528b7f10024180e342bc1124a16901c51ee23814a1595bd82460c341f2425d840a2cb88ff526315f536b4535c888127a39fe15f48bc10e52404279c6e613e838868a448b0234552f08da859b9a2027b6117423c9ca25784107d49b259b11cc52c53208446502aa0f858808894716896c1158a2819ec00007cd1eee15f865f800015cb00000000a9500004f0e00003eb8d39000000005b280002d32000154380003b1600001c58911000000000001fbe0000108c00011ea3b2a48ecc738f0200000e0d3c889294dec7024df99e854502a7751642a7845f8787962d27511c8ea5994db0234446e00015d50d962a709c60c35887644a6a5388ef0b6113a83630cb42399129a1abc8b723eb551a0000000211a47deaa2c19b2b524a1400000000f984b8e590c00000004f5c000000027d405be101d375000014d000008ef82cd39f61b5878e8808528e2c388a600002818a9d091116f35560494c0de850b0000822c60a0b0c262c91d0dfb8a8f2958609c000112f2b36481c5732313462e0e9cfc603210000609112e8a7f00000000c3c9ecb2fec97045e32aac2b7c47fc000287a4e204f28e6c0dd14bfc00006ec000000000ba4dbe856000009e394b400000000000143d8000000023ec16b84bd2930000114512f90e0c5a0d24000001f580000e95000043d0b0410a20000484479681061216000034282d100004b6600005c0000000000000c11800000001bb92d288155752186009fa0f40000a61ce3a00001a104ad10c1197544ce000000024b400002dd40002c371200306cadc0000028262a000003a052b2000000017b604269204190181000000080b6a1bfd4ca000015b72664000000001628f8c4c540000000280347369de136d0a273ab28314be8800008e6000136b8
  | 65 => 0x800000000000345a3c23ec02fd800000000000519449a88bd00000b10da2818a0000a6c80000e733fe6047cd210000226e00000000000259481d029d88e1000086aca2b8b4922c47cccca1aa950000351c0001fd700008ccc3251f05284a24b07ce80001fdc72ac000000000000000df5ab7f275e56d42c727e247f00000fb48dfb45ca5ed043788de296449552c7891b3cce590902c9f220ed6979c1be146a17324ac527591fa4c8c47c8cb70df158aa89483c71e2842aa02dd1722bac2a90583d23d207c0fc29938fbc83fe00003a5cc3f04720ab20000000046556d20c615059a5a3fbc00002bc00004eb4614454ca6ac08c00001209000055421c801db96e30178a070d091c6d00005f1512f117040aa3ca450908fd107ea879149814435e00000c8e18ae20d407b0266a7bc3ccc00000000cac2d700fb01a08000000032a418d1c281f6c6f3c0002a4d2cb09ec80001a8600009f24fb403aa522e000000000004cfc0000000160606764cd00000c39266233714cf081f2736ada12f523485352af3079429842f0800012070efd30120000423896a10d27584000000043c63cbc8c19b2312e65cfce9e1d1851fa81ac0001d47023000007699f0c52d650f8372080e1bba9efcf490bb117d40000d280000012e0000000271421629c3ccffaaca49a0ae885dc9a265120ac0c62600002daa6b20971a1a800008308c10866d1876aca800016a40e667b390fca68e30a800009c30ff40ae6379505a8445127c0000063a4b72e9c000018f00004e6e0d1821e1c9321cc5b8886b80001084509c00011db00005268c800853255e1220000000000000000000287100000000000156b00008bc110a10a6126e42500000eb5510475100000000126800006ba24fa3f4e20412e80d4200002dc40000fa70e9c2e49314800004a2000035094710000000146a148c0000ad78c0d871437648050f8d9b5433d4308ccce1bb11cf089a08641f354d2a44d4a4c964714006a38d8c230100002abcc8f00000d640fb92c400f335f6a0a95c69fe12b5829547f5045421942a6c4c8055c2a1cab9854c15e013d2acbd5542b6a010a734806a83812f5a0f0ca208e744fee6cc94cd256700003c004832b19536800000a50000485224cc000000029c0171c5d480004f460000e7627ad0000040948f069b2e0e9d744381a9a1cec5fe057e94d63016003ca2102b20b3827b92038d1e1caa782483e8987148c0000d441b8400004ddc0dc08b900000000000000056e6a2247b584c82e307ad130b8d9900002f940001b003c2c3470a90a3fb42d02368448a95a57da9ff54059d2e432c1c408e28040533600014cba71932e8000000018f917a40000eb81ec000000ae00001a9b3b8e8ea80c30904000090e4c71000000000000aa284c249e02510c088f7b0e180de44efa4d254a2
  | 66 => 0xe000000004b33ff025a000025a617a000852b32a8f4dde00000000c340458776cf69220c0a06310c7c9078c06367f6894fa0ba28589f106ed80003170446d234113c47ac15582a128020ab09f983ce000035282fecbdf0fc2099865b4bba09a72a028038b0e20b014e04aa5064843320a600000000c66349841b13301bfe0e02a4dcc8a03a3362e25a405a8cdb165eaec08238fc836e44724e20997d2a2e000069812422f542900ff81f272e6e24ed3db00001ff009cc00021ad57c6777c0000000243229080239e1b2d1e649534500001800651955792c853aa00940bb05690ff61f1493a0a07584c0000efb1fc036389c0d2e01b98000042840002334000042a12fda62e27b85f2879e120d201c4009330800000005658000000000009900000000028604ba0a4b883600003174c592a28493000010869f8806c4355d5011828328e000101eaa07538c66e136806833616270057a84e902de56cd1318000474c662101322c62b5a8efc00022853c200000a4500271922ae646a314350000000014aa23b4d0e7d2c0001625359210212689f9f49fe886c98b8bd80d444b14f4580000720000092c006f00003bc0e99800000008b7000020f70000000142f0000000035b49bca4f41548000082f00003a4c02a414f1e692d7c8c3cd11000006868a30f05a86b29c2463400019e438360000de68fbd454e00000000000426e866c43d00000000000000000003090ad9c000146924de74a4ec9a2753d500000f9600000c501a40000000037f2a85456caad4558e4acc000000000005c5530f000039dc000054580003698829096081ef4988000000026671a68ab213d500000000000117a1d9400006fb00001f5120aa11a4000227d1862915c00001054de61c601100115000090d55c28000468c00006b505670eca859858099914990122562ba7ca2fcc78d08c49cb74d481d20e5e83fc54846365059171631ae016c0001aa13e5a000026a000039da13c839b2a6c319025dc56000002fdc6590e3c867900009830000025f00008790538960a000051dcbd0a5bd10b64c9400023501b9c65ccef2195e2d6c476075d990d2d8e53a4fa506971472a798d6e00000b4a8bb00000de419809214fe38000188e05e89b92ba453b697c531b228d0f2643391f39125499c74e86ba96fc07640280e35040625ce000156328eb0000337833fa0d42b2e461c5f70dba0620844c52519c9528a8dcceb69c991d8c70484ec0000393aa9007f986b3000034c46cc13e038d6000071f8000324200002159037457e65e0000179100006654164961f2a32000050600004c7494740001e3c2b569e04b49000027ce52e14a5000025b40000000044f000063a4d3e14481cf877e95b89310442a6d204fd969b00006f1c000000011de816cad78fcc4600000000000000000188044e
  | 67 => 0xa7014abc96b55e0148200000000000191856160f2413f0598022422d940517b010b0329d4d526a6174c613915700b13e522210eaa8000231692e464ca008211400009281a70541e76a80001dbb55f6000105091cc095e9d20e4684322ce60af924a11bf0bec807c201a1d40000276d1d9a9654e365b686e68052000035255fc0634025e944515d26c00000a8d41ab9d46016600003e9a0d312e400001cc8bc32d589f708f995c63cd00000cf91812000095a464496122dfe98380e0000000000ce92ba80e54b02000065719e9330a7e2400013913b6c00000002b1c2136561800004422c7225780b4a0c448a814c11a9800025f05df00000000364a80010e709a506b6467000023c008aa0180000000006c24ce04f51c320b6ca438f70a9560b76746c1ff9a633b9e06b4b1b00004c2200000002805000001591f98000000028712e123664ff2a180fa79ceb01da9b7413580dc00942758a502be60382178134f99022aa81818a8225ca21566f54e600d8007d6479c66b228400000000181043000001d6539a17794f0865852eca19a05c49fa0f76a423503c604d04107ef1a766de047118873ea410ed3e7948625d203a936c09d906e60c654bd00d9029c4e68392a43f4240a3cc40c800000001e80617800028d600015319b8e0000680558a1e57420a03e400001ae3b0661cd4969ab13a48756c73d0fed000028893432a7b35d401a4c25854332ec3c1025324e922ac46bcccda58946aa9cf421f99aa24c806990850c3f0000469d14a9c9c53ce744d1cb0f6311fe93242f598a1155000008501b152fce208457423360000a5d52b10dbc2f8477f8000243e399c00004810000000080f94afa919178e2bb4ef726152cf2a810ae7244e4a2a78280001dfd2b80829ccd4a8d210506cecaaa869248b017756299fef4cf87474f0b941b4440a3891baa1a226f85bdc771109c40428bcd47d8000142018f8ec60ab33ff80648000277408f47718000275636962554b08002c1db06e7141da18e443800001579ae523ec1b4135809e32b1c54885912bba4ba88d7124b0421467eafb0e11a58252229e846dd86f6255c5f8113a0aac3a9a8c88b7ca92b354c71b849ca3a00df00e98e6a26b30c3ca311546180e1e441834cfe83dc00009500d452097338c2d10fa81cdc2110000000000000000000056083fd00003c20d1d99dc29f686347e71a0c2d225d1400002a00000b088bc722a21a466994c440e700900aba0c66a77d306c40d06280bfe1328411000000004d34000061009611a06ac180000fe4256c35a400023300ad41204b6f27a234e400015f5800055b091b930480002a24a5455a6a2b808043ca93b8800000007b085041ba3000000008e307a932586b1919700000c10223d354094b1efe15892161fbf3f241f055aa1e5b05d6b0a11052c2523a
  | 68 => 0x9c000123e1104182e87b8b7d8ec92e58057cb12036e0000337c5ef0d3220ce53093bd80000494770055e81700000000035d000054a0000000007a82570981c00010b9371a44e0cfd1b860fbca104049122b0f3000013a0800055f41a08aab96c12880191556192d1280a8ce09ea016b52888a5057181341968883539b02e454c200010ba91c753860000c0393f85472000000019b700002ce801997f30000af883fa116b51c899dc05801740000a3755f801f615620000c020000026a00007210c3d0dda7a84128090c08ac4eb00860a30169e96480002c5251d019dca778001044e83c90511fd9386ea2e0d91296f424e4dad1faa2a35062515553ba0430c0e35201b5aae4502886309b825b01d220000851233b14ae513c7669bc2109272ec48427884a0036e4000059454ce000135b1a1105c60000e4a25f744666b54d1090db4f686bb87f180000ffa9f340000bf925dc0001525800053ea958c2bc8000415602a813f877135604d8537e1bb4000027a10c903313632000000021b300001a140000a1f00000000000000047f294980001bef05367f7d5cc00000000000000000000000a378c290c0300000000b6195390ae014e5397a8a10000000013784002e3a7f100d8a2413f1ab1445cb276e554e21fd047a5284f987430441034a39740000f6a282b53ec12dc5618384006a8c80a3180003f6829e8da780002416b12d1d10811115600014c4aaa2573899080000e1440fc28ac17d8d710b801a38835a65b08361a740000aa00b5c95e4a7d06ff4aa07f0800011050940000091280001ade17f80be00001f2c3f2c85d06730eb82138125a90413563798ed2096f1da87c513d894d8036e06601eb0be0000026b93a800460000a07c7b30c1239f830a55418b832878854c726a3714d3a1fc081219c50546654045705c14a98497515a8aec492e9ef92a488c8530c1ab53b2908025560d68805a12d251a397534e02ac2c128cb531e09192bdc2b8422827983df41af495929a52f4651a0c30942a1ca46328f9f9ce81c0016204872b640d5458e8f7c85e5170e742815b1e98183000000d0800029728b80d8f242b26a63638d8e90931d0455604782c12265a8aa87629a342db600004e6072843e0645458a05e64430062cc539ade0000a1f82e8278247205e007f805a301b0020401ea1a9516a0d4d0ca069152a88fc00000ed53848772c9dd00003f2c6eed0d024ab49140000c6203d73abc4f0d0b580395196a9e41a01df2056e0efc0001dbe4d620000e788a4b378600011ad21971c86507d2d08ccd138caf68429248e497c732502118374a7c33b4bef0e753aee2fa07a405b70348759400029cf507e27d0b86000057865e40b1a8d7d299a767cb4a06a942707d54b301a100fce9be512e0f06053a1d9134886463bfe4194a07026918d0953920
  | 69 => 0xe71f4d56ba820cf489a414db632355e79c3d54dc4330c979c1731de0965324217b384e1e8546092b946ce000051180000c90a09844a00000b58000146d204f000000a80742ab20000000117f1191480cae7cac59bb64d9a655160617ab15d6069cbf490ff00002f988be80ee499400005228afe4a26a634155935f3c7644794e9000003e291c000015ff060aad3154401f52108643c56c15f2456039dca8280003eae7cbc602074a15d219352a300410000a0052230f4d412624a000001e704440000770800004ae675c0880d520cd257bce44a502044c0000b53085d0696321016b0b7b00000548ac298561a9c9ff810ba0991f4479e95ac009626ac3fbc00018fa14c2000103f80000000abbc000000000000000000033900003400d4b9d150000a6300000000000054980000000222226dc73f800000009ee129a9a3750726448b111f162f6a56315351b9a00008a811890a4c26262d50000000048fe610d50d815a0cb69110b3529ea4fb20001435213f432653cce2da9580ef07bd51431ec351146554ca920d53c8ca37cea50fda425c581138107682a405cc8298910318f820f4d87098d3ffe4748b498513000002c8000190826580ca88fe0bc430aa17fd0d72bb9427409ed4ec9a3e22b6186c90a0adc4bc065140000000000023c4000259f0000a8700000f603db0000125a8000577c5b340000000000075380000d5c32c697fd2b09b7e00000000a558000224e2a552d2000000008031231000019c49190ccb064747a8049032fa85935d82d6c260a1243fa82b2c6ac0c8106ac6f943dd07410000000000006513740a4bcdaea466248e1258c6f0e07475c55c4c06aa08132e730d56e09c3419a9dc06f49a730000753142c2a18169a70a50b981af21be8e5496f01a90f02a54d115167b352c24d8083016e41ae6438f66a25410ae08090ff2002191c98088bb14c720ba38993021461104ca06120b975538421eccd44a3be228caa980b613ec018416fcecb9f6e07da7ea82f6907535ce16ac392071301e208b91d629fb471a06502842a5d0c9c83f559492ec02d01e2c23d842400007e4c0002c0f3b44775484815411802000047c1aae4a7a9554ab711b933b235ad0e992ea00007bf091a1f0d1eba742c0a38288550420dcef8226000002e547109119040600013a9a1e14ef4255924793643f94000157f0f7e17927e0cd071f612c404a1418421602aa4187523480000f0c63c490709ad518493f4a9601403a4239701299fe64a94a4409348b2621e0a6c003605bc5508717494f153e39081a589f90cff00005c7c33c26260b1822a40001fd200007920bfd008d000063d80000d550000000101e0000014e2ae506d04e13cea13dc000165b4098675872f127b3e1e60180001a5d2c2a0000000119b0cdc5fac9a7a752031218b09078bbc51
  | 70 => 0x44800000000753410e0000000000051729c851c021f80ec2a2ec594aabb38de5ac09d68b6600708e0cb65874b0a7c85fc8fd854652aa56d14488e441fb25e18980219c2bba294d4a1869e365a4344d908185504e71f0f4f0e3448a0ad0c961967a160e32acc1c21a30cc84e100001100479c5c38b731db2498082f93911c0b081a8f648b497502a1891687da104f124892f0d258f054850179c6522b3f02060ae94500000000093b4d6c99b301348acc0000953108a0000000267037065cc02788000586a1070a710c09355a26252078eb63f8608f4d8b2b1601fe269899110303bce7b90828190c0fa066250268e6c5348226118a1aa800005ca414c0886000066fcb9b17ba3d445c105e6215c587e302c243a4330452815d01b1b3e0000a6211350f6a3a62467cac48f7d219e5b755ca0f83254457906a01ad72eb69aed1d288c3348660001461a1d44962088c201e2f10c86a644d618393a7242046458d640c708c0d08e1de0460e2e6c631aa7613c82cc019a904e41b81c6813b0000000089b4000010d000000000000e400a2c0000d53a10f000020e89a5a6cc3c8003d00000000327c783147d145d006c29e00000c8000002db93ff800000007d64000006e0000000000008500000a1914eb250548b2316ce0b27b7082a0000000253348a66af0000166656d8a23cd0a16370a0c4f7cb09a1f408c2ab74ebd0c8343ea27e09dc2016200c917cd820fc054d099c8aad214c1bb2103133d0b4e17b45d04e238000010c0000c9696bf2fe82a892921c78000040887788766554800015a2972d32a20000c0180000cfa4f3800008ad037eaf84000155b0d9e9d29426083c2a5c000058caa2754404c040000000222c5e8850105120dbe81b03e618342a5e484cb95213608b28e11162000017c24aecf901bfa1234a8c04ee018735ba1a6803c853727681120f8e97c302aa62fce2f275f00005ee15b2a19e45f073f562682fe5836000069490431baa57147df20751dfc41bc8bda2d253e46ba45ac82cf35f4a02103e921534a442b89141dd7569e5bb83739a28574ca6d516c172b138893785f19077277c9d80b54800018fa795030792c2128e884898c800008ae76480000f2e52c89760bc7993d01e0960145d1e441e4c1bc09a38e0654583f0c8291d04000053e4000164b44b484a85c42c444f1a0a68c25198a0cc41ac02828cb113663f043451668473c63f4000264c3ef8623cc6310b63a0e5cf8c1486fc2808ace014b852b3c629f441cf08d726c08f3d35019ef3fc40b847f328c8306415385f80ded18ca90bc926041600002bc4e402b4902cc34388d2800039be72812068eb24b3a37402aa06d34cae9aad1ffa5dd2da02dbc7e51bb00a0870d00842ac1073093a022187802ee658655310e8b0726a47c3842374052cad00bd89f06587097145
  | 71 => 0x46acac151bd0f724d30ab7c000000030e40a70aef01173fee929c0001e271ff62fd03000a644954a5b8ec089cd252a66193619d0031727df52ac27320000339cae8182d3c9e624cd5f046e15842d14000000025c06b0400026c4293c00bc0000f452a500cb892200000de811c4f558000380e00013c58000284855654929aa042186bf85eb9c7d0f80582cba00df71a8631686a286353f1e0d7150f968b186440a42482ac243803eac8390df4004630e02178fe715284618b54174c42fc6e20000290944f2ad6c182147914ee8e7c208249f1c1237e8645004202b034f4c3b0364562a9eed59715935412142899e01a33aa26704d18206a2e9e3a100000000000a30c0abe8888453a282c0001cad0000ab953f980003cd40000dfa800042c800010d7a26f501c8774e8e12e22ece7930000148452b836d400000002c060000000000013da0000000000000001494a73000000001bc4508836521a884d4b169e643f8231016000f8b216a6e78d731903538aa288a9f824c4de459b0adf9cf33ecea2902f1944a33d66bacd2a9f1900b0a93c9f5953439caa384fbaa490389c9ae8d2c1baf143678b48419b061aa231d8d0d250b32f842648b0863949e244d90d91246173e68605d629dc3ae8066518b042e42d4690078c85362c7e450855d1e9a03448f483b521a72dfa5a6042d196b0ea23ab55518986524658a9556a1ba270a4a9535780e44c5e42191fa24d52b50ab38297a3354bda64c86f1a37f1b4453943cf0ca251fc44541b78f5b10482c8103b221d079c140019585a131fc56f528d157022e685886d617cb1d3217b002d116f20d05e6548996741d4c64e4941a50350e08f045cb91d037ae3b1d53820b60cb46aac37d1321231486550089c2c28b25110d3d1dbf0d32371874718d624f8786056b0f4f2012669d60a0bca2a060d54a6892a3154636943290c3c1fbc910cbde29e00e085d9078b085f426068347a3a3f244ac74dc102244b330e7004b888f1f53f475f5426860c30287ac53d49bb70964a260df6a9fd4196943cb741ea60c928741301a07800d08dac65401131bec33a0375964c2ec07d60dba04923e568db89271f9e09e67f6cbb5268557246208533a4a150402708b7788b1034a0000dc49d0d112a91ad165047645523de04dda7c61ce41ef561b113f49866ea400020962a0c3c795d1800053f8000082c800021aa3cc06fe05f31368a924a46a3371b22a470a8c1da523680000b5783ac00004fdc00000003efe63b05a0a3ad1ebe16a0000129a140652d52cf2b120000066d49f800014d2937094093fd011667f04a11525571210941bc15e1394c120819385c20000802400013a82b5c1d1869f18fc072e5d5d4f2276c10d8848c07b2962000067693b9a9e8019e1bf48a0a12b00007b2400005cd48d40000bd918a31
  | 72 => 0x168c1a4ceee2991047c7208462045b093a74441f18a32271c000038281113ec600000000a0613f21afd2910426483600014d89a8519944dd819489d73d020000000000000001994dbb00000000869147724a2014a69d4b438000491266942b202c012ec3ec89eb10c34c4a9f04c6e094f3c025c79367800000000000c1815292f0a6f9d49a07ca07b2000116b2229000031391f6000000007190f848ecc35ac19acfbc2c543fa28e6107512982af69e408bc9684000081215ef12f64262256c7492251494a4dd0495886624b4261039906a552e838b4ee88000000000006108c52207875a43d326a734e81d0c10e000000005eb000010912f2e332000000000000000000013cb14a25378915208a17a60000ccb92cd0b0450f4e111b4432f438ace6329ce437a2284881155320e27b6c497993f267a234940b026d55f8261537b94c4000039f84fea28b000000000002ad300004db0000105c17de80e5099a24e35be86fc000115e00001b6400015da29942db05238a8d036a0000315000023629850642800051922788807933b355e44a4868283415429bc47e6a226268a51f087a811418ea89e8773229247ec0f086ffa48222aa0d654c80000361285788518af21e48106543a0b270db429cd2b612cb4b96a370f899ac030b0856c8de1d10000000000000000075e049c0000000446000006bf09cb05f000000000b7d54763f60000111a000000014f99f1a00007b40978800000000000db98000173c05c8000256e203425180001792000080b417ea78321e47db0ccf96a137a8af4151f9aef00001c5cb9c80000000000013300000ebc0000c5500003e742de83bd158d4eb80000bcf12fb00006214a0d00002ef0a13c000000017da313c0000b8e4504aa24e8c828945b458c080da5be19b08df851488c658345bc0c5d0c2e27c408a8d30048a561c870c0648eb4509224788e72b0817ea00dc31f90bd1458713465b0451068846dd0808c7f10fa9970b2d145c1ef83ae13e58c571a6c63145680d684a3089251670fb325f84d440001c602c101ce0639a9d00bd0492954d03e72aea8b6c5af22f61c102488efa2a1237a0aa040148f2b1acc19f89a00024049e49d4bc4054d43ee1ab89cf0592194205dc000004900003f884f281bc39507e7412a9a3347a0248cc4803282dc084b0aafa1702d8475ac7250e37446a0000c261e003eb860810201fa30000000096b1085330467cc00021d10f043864dc5a445075616645b50f1a085473649c1a277191e0c74cf899e22b0634bc09514dc469255e4ab785a71f7e3154feb0cda0648a7e138e994b00000c4d2699d6f11025b280001e862fe0833cc1600005138000000000001b400000000000000002ea066a2aba3bd6a4b000890b21b246d6019690e01a568171610800013606d480c0800002bc0000
  | 73 => 0x8dfc139322a402ad6138d8b4d2c27d40000a5942823a6c09b0ea3399037f862f224702564258b0680001d2c0000603a6cb062856646c1051e311a4290cac0000118204cc8a7856f0000000064a800041d6af280c80000000078642b700002cc453315ba20b3515e25286490d3f0bb25ae954807ab51b2000000022d400000ee924c8ffe239a1e10000161146980428481abf303b66ae0000078f4c56201c18318771ea239bd0d092f752768a0c00022fd37a223c82eb9d9c2e786bf46f1187a398e68b47190b18334865b099f024d37c646f9602ab6d2fc27bec153a1da00000000000000048260000f59254150a40000129176b0000000108f1ac442e460f8000079a127e670ce310b4029960000000282958b0af582b0800028da0ad0000223c1150000133b00004966a2f82149dd90d824f1d3e38000304c68fc00007ec00007820a5f1c9849ee04e0191a46f1a4c63482548a1609289f78dc39953524257d03cb1d76268c00302fe25274af05070500800006e035350c2995a0be08e208de8eb7227400605e085b05540a434ca5131b115e1cd4a21ab56519a6988f4716ea16361edca0f193535389e191b0ac023f700e94a8e060b4b4e3c34e720e86530455248a8a80418fc2674adb279f0000abac370800004f032e15761f2600008041388a976000089892f0ac1322ba4e28f549b7937924664663aacd5434a85063694fd41be096cd1796553aac63e07e90000000032a8f2c9dba09fc3b6cfa2127700000000d30a29c572077e0afd800055723f3c40587f91c549964e279fed1f02936864401b3264e0cf511f89d0260c3a94262143b49ce0000bdc989900004810000120a00000b081f5008300000000b98858d01bc000000020ce40c6318057d8000000047bd36100002540b0f946a84cb1b4859fce9b1c0c00003250bbd940f0000000000000003cba1214f920000469a5258aab1a591d4441e54c98f0a2e1057a46ee185a2f304cd55d69a0905e883cca5b1c5318d24fa4000001a242e7a283ff265d25a60000b0081dd245c92b05b59c733a2e7d1c133a3d148c263ed20213433b3a603cfcba90722ccad7c8ad1dcc29442f14287896d26d4a8886bd8e880e5e33a84cc178215ca838d24d84db30a60cf14750000285c32681d1036c2cd64884eb9939633b020501dc01ce01fa9514c8b1c1f41a077b526a121f36f830a0a51848d11d6a5e430ca87210f06239400245b5328297ce58877336f42c912b514a703c072a8ee913a20b1406690d51f1c040062b01e5800020e0a490ce6282200000000000156641e000003f299fb04e80000000000007d0128c00007c419d8000053681a80000441ca068261000000015ea1f704c700000de410d31a02a4f000014670000000000000000caa3464a7184370000781d4b3841800000000000081e
  | 74 => 0x89f493495d8bad21d238282a9d3000d9332b88cf54d68e0114fa76a0a4e15aa000047a07960000090615b08769d250cac6398747800000007a7d3d78c2c000072ccfc806cd000000015cb07b20be2863caf6821900004f68f7780000a68544c5461bca000031580001c024f9080354a000001ffe45d4ca4137b00002ff0da1800055ec00006028000000000000000fa100000000f42063334be190c207254d3c3414c800008180000464c0000a2a23d203140001d0f0f2416a43e3000000008d600001aca000000010f58a8600004f043c6897e471c5ca00000f8a35582de125e93a10d2a93e489207d82462a978d038b3843886f390369be10f0a9b652269e7908a40f14f5620c155e64ec05669d7f102444708ff23b91c7497a504a0f384ce631b10f897c650c45fc44ed1a4732eea0a0dc98ee33832aca1325800019fc23d4d5f80000aaa65bd53f0527319810885ba07df1eaa1dd867189c519a274513ca26fd32543274343973b0da89bfc143a9033b8878a52659ea7380a6e89394905a189aa3801982081468eac345242a66501a2a74d69aa2f0b2627cce9a9670015c00014441b9f3d1e4f849d500003bf250589292be42420000070f2187206c6511013a949291648d8ca60e3129d479ac0001c2f0d001844315a2b65700119d0102a9c1c503e18ffb27a410ca22fcc4199ba0894af18c4b8e502caca20d4619299527a826d02f29a3303069444681ea5008a60148991b654d4a7b64d09925706b0acac0960000475e1d353fc18a52aec0000329a7311c4434dd364a2e913920000dbda2ed00625f300000000000086dc3f4a19f0d0c3494add8050003a0bb0a7221d756ec6d9c267006433607e991c0a1494322afec63ba6ca00f04d5c17e183a2c640175229222e01f051c0afb06c71e5a0d98b4b9b1f0d80a345442070b500e3d1000008aa0b0a982800021b10f6c93ec0000c444b1473a8e87023f1946000117c9f1143022298000000000005085376a6b737b40000000176800006304e6b0000344e00000000a1e221667c151b861620b68544599a26503386db440d24e31d520000e9a0cb31d940000e7b101f0ae490940001f0b3c40ab9d2ae967d585c425548928bd000092910ab99990000a16c4318000412218b4789169d4e4a36a10892206145a0bfc000060918e80001048039a0000892800000001086ad5ca78854512ca0001482873d2bb079242dc007a05326b612f2802253e890206e4a12215649b184bf87e3516473dd452a31135a416985fe9cb5535ca9a52761bf24ae66ef079d00002f66a91467496b5570479c4000200644d886944518ff1261a00007679431000000000820c6125880000608861337dcaf74720830f58b21ee023e8e3b1db4aeecec01f5e1552a12d5189bf6269440141238a3f4420305
  | 75 => 0x11ee9c550000000160e0000000051b15c309513af86a2c000225800005ad120a01e3079084f0000000043f64c30f4000000eba00000000e1600008df43b100003c4600000000f7a44f027d87ed8b9810d67888000000000000000000043a0000000152f99c2451c9c58712a5e843202fe000000000000460000027fb00000000e780391356a123000023de00009bd000000003574656c7cd80000000000000000003cd80000df0000055263d08df30d6c0dfc41e894e2c4953c43ea416a29c9029243e4d512a474c7c1a053d80000150055f01d6934455e07f60be71f9c4038768cabf96e708a63e1447f2234438a9330c790b8d4800616503912bc1904229551e1bdb46a200003129bc00a023c04fe7a8a9317c165921d84a500005c4810703012bca6e9c04002ea371e2948c318a7c0000418c9e200632092ae805079fad0c4e03302daa74b381a697063c8e933d20000049e033f00000000ffd84680000000000003f902e654751fd000000008aac0000b500000000098f93301f72ab6c000047500004c745c22bb4334024a884e8cc9286e010c3d38311000000004f02bbc372c38b0000227006009cc08e790044e10000156d1c7f4c60000055b815707180000cda8745391853dc0000000000000000000fbc00003afd36e0e5943aa28d4bc9aaa5518c772000015e3309a0000a3d800049aeb1595750000000082a400000001f5496550ec18ad385ca17c00022a50d622864dde96d62bcc0000e0aab42535600000fda0440f0691e40001be90000881547fa2281a2e2fccbaf159f168e11c02f203b90056270561a1a1f1ea0000000020252abc96dd327800043fe50b4fd412b732786030fbb27120ec631ec66804172fde627c2361ae1000000012b20d7f1b7e0000fdb00005796006c57c18b30c6435307028ade25b2800ce0e8d852a120000d6700004168a120000038032220000e6296673d042338f7a155117d84fc40000000000071b12a397d24c8a51306dc057f244e5fa93dea55749dcab41491115810d45cd016323d81616146cc7b9da946da6c283050ddf56186c1c3bf979636546744a770e9528125a586c696a3259c9bf8288805e359806202d881643656385c4bd0dc1505832311af800056d60318000201e0ef6a2b48d610f74c768b540001a6d52e4000070f85ca0fdc077cb4e0c86555227450e08171109838712c1902e48926eb877900004fac00005bb04a7299220180002c11000000000c7037d000067d53fe241d11da000013aa608000000009720000339c88c400011bb27ae3f246e12a361114605d1d1890b28b6a1b0cfb888b15de2cf800003fb00001850eb6000000000000000000011688b7c085852132e03a68964800000009b48417a96056f892b43e10c08408e07a01e81307390e9cf0156aa384aa276b0000000
  | 76 => 0xdc51283e5c91680000000973ca8f128c1a70af1d1d9285d00003d380e9a571057846a8b0f072d2b40a9b4a4ea92800001ef8000049a52fa39b55ed89dd2d4e4a18fa700004cde000127501bb3f920001185000000005ac4b2b9865019c61d400029460000a0741410910222886d15e99af634f229ac74e9e3f3e722b740002927000000006621d883568a4cc00012d442dcaff059727461b7c04f4a5483d11b8a0000ec20000514e3ba000010072a9a14cd2e21066379894581589f411c7843f0a9ea5fc2f1219e839e24df4a5c427c6b020dd077a2cd459ea90a468891b1532a1e60dcc127c00016343bca0000a6d0000057ea430a418b17508a91cd5ee237705c057cd2cc8fdf019ab05c9b41fee2a46a57417392454df6845c7091d723e98795425c800029d6568cb97848f00001b246cf8d1115e699e41f2245d22e8a4e4b708c545488180400a0c2a2c2c7248b55821d18384fe43b902f01fba21ec3e3886e1c6690f407102b9106614250de238c526a02700001c8312d8a8a88a000000000770481ca0fe44d6028875380003c480000ec6875b333a000000004fd51ae3c5082b80000000679951712e521540000178a071000041606848da62ce450800cf1e2c246a6ca0d0320bd2d3c2404ce980001a4e00000001450439e4ed8ad3a6374c162434d4c000000000d38e89135d3a1285e00000e3812820eccb1886ab35f253187888143000081410fd116807f400005ee22d11082000121b80000000a95040e9641147024248aa0000370a5dc002c87164c6a000045917623cca000157eab7e3e641c28d4993d80000840d0e6213e029600000000000520c0000b901e6d2fbe00004f784e006ea7ad40001fb11e7c000000000001d7208dcaee00000000000000009d519ae00000000c36492226851c920ec4c687b212f80000000094b13ed890a4e4e8a695fb0f9c3ee2a31531c9f0338f6000137c1f0111842ed146398d51d60a930740a53f48b866380051ed739a69f95624066f461623610ac992328ea030123005631178a230c84a40c4a7267b12791392000065c8847098c45e400000e49f874a6c96d80002bf454e4a2000c00eaf1ec824c47d218af1c7a4cfc2ea2c0a1dae065c00008dd2eca00015cd08a044aa0000000000040a6663c68b00000000000000000001f04233050b86040000000000008a245de199c36724c20a5c7ba09459b750000000159114cf56b498189c5956c27ba62d423e07af4b0a000089f2a96000020b0635ac240b00427873e91eb25426338d8a231c0000000113f20ff17d64df4e1f183512603104582a5840e84358531fabef39727a310e5a25f40444c68424089a1796a42c8d99a8743123d64817a508193840ec8ed15e2027458300d6000000005f7000000003270391801a08f3000043845ae0000000000
  | 77 => 0xbd513fa619000085e800027b347f806454ff9bdc000029781cd84ae1dbe4bb44b8836a0004312d4d41ae8533a8d28c71a2de1b9436cc858188a00004304000101c4586973811a8439162a0565157a106257a7ecc82a162813325375116047e57fa8f6802bac1f2f5e131893c255b4d6853c8cdd80002e7a21a06a5a488418c7e103aa27c21f6070d48d40602391668b850d070d07e83fe8a53235d50ca319c53f1d2038722d4d10d015455f0534038dab2738661068801a5da3ac400008490fec000023a05929eb93d2c5db0f4c96ec572a524c3d1953b280650a13340e65015a83a47eaa3792f1a66c879923ba199686c091c91d91d905fc93be0ff940767f2028e9a8d1c267cb849094c30000038c792a6be3a560674ba923fe0000011026b127d2d4a57f400000004150513500d950721fc07f02169089447c44c0900014d3fe873d0000228706146cc5100837741860000fc000000000ab00af818862974000160c800048ca0f507ac0000000000000000000391e0000000079900006ef83111c0e39bc680ccff138f55a2000020a006a5880abd549c26de2272600539426d608b480104ab84581a3a00009970000070c00000000000532c3b4800000000000953d15e10ec1d780a2c977800015603164c0a982b1b960000d9c915f11f2146000013b250600000c549c4200002e901961d85000099d55898c722b6438f8669000025ba6da90b60000039837f4864800057a20000149021410540194ebaa03a4228000142989ec30107a904c9a492070e79cccbc88b734cc5048638191b2ac65b0020f14f40000000d5649b6614cc00006502bf21f3c13d49b485100c604e412720b064e7446384828d10200297792f60f740e742b1041708cd11488b8c05d8c9e43de952c47a1d7b14923e103e71ad0513e4f54e031c3b179e224c7b80000563a298094b8df80a344994cb385da205a94e88bf1841245871c8f9a187b3d768f18bc615721b42500437103e20c8446c880f275753d238914ad942331ea4f18ec72b4e1b3a6778555954b20987e2cf6b291401d8ab80b748b704a549968da699cd05b0002004f845e1f702258b92a597000084254ec20791d86ac84def8ba519f05408ac8163d0000648116e866a1dfea8407e2a7993d7000011e38cb034e21c3d3199d6640a4add4968212500000000e0892c74aa40000368a83824e0576c0001dab03fc339959e957a16c600015089adb3f3678d84d48675307e6db85370abb00005e80ca793a4413e4f301c28000000095c013e9ef119c899b8a5da506204c021c4001f231ebc900c6fa91d4313057e89309c9a4f3615dcf98134d1de6249c7b294c553ee928c94700db398428b8815986802445f5552723b4040c61bc6cd000057fe000063c25860502abc53a29db53b9a34f149f000e0ed256705d58f
  | 78 => 0x3db24dc1ddc1dd800028e8000159000000e4c00008001dae00000000000000016141cf94cc8fe900002ad13d02365211e0000000000028fe28816229c45577096312d720770000a39400022e71edea24cff283602e161b0c83b030b000032f06b10e5b2e327c287601af80000a5347e216df31d045b00002c160de640b0b1f1358442e2e50884aa341a7464c4b0c278f3a02043d5881d5a3cf077bd13729a200000f940ea1f1e3da60f3000000002d9e6ce09c6937a258c274c748125c17ac219c1928a5842e864ecef60ee70000153c9daa5a947780000637a70047c40000ea825341e66b0a8000003c00f8933cad480000b729e015ea922332d417e43fa80001b387d2000000004242058c1ce81f9290a9564cab94a14cf000004e40db22e942cfc6630000424c5b191b4241000008f2000000003c608270891268200002e3000003f51c5200013828f0e251eb0388830ab606061010e0f0cbf4be80000def0000351819d8c489d2c1b1035d9340025641f6340802983f2119e63951211c2500009d5497f1722411a307429415b03d0e5c68000000043ce17251b82c3a405c0900ec799e832501c48a8a924d090c9495238a9704e0c7cf0c5da06e56ee0b444d10cef1d28723829608290000412c548998d1322027438c887116b4859cc4aab6012b092a12139b9b3dfaaa609a10000503458ac8e580002fd85c8d01981da00904eac048a81b1af47ab9540092e47620000047000042da8ed83c89da64052171534929713d287dbc1e98e642a1022e036285c3529e40c85dc21ca30c40000000112000000000000043d0d889680c750000536647b83a000002fb65c24000243000000fc4402a343560807843ee934e1af00001000809900005d98000240a000039240001bb331c8792c00000001ffa92c11dbab974e148e28ba498b04c9a84f425c03515290a1d8bb4800000006d44822a73f00000000000000000003460f5b000041085e701731621029800010dc960515c80000ed80bf200003a0d39180000000aac4be999be4fa63ebd51e80885766766815e85e90000283932898b43bd200014e897a839367ddc89424e04e3495089e79ec62db01ba427c9614000063c1455000018a637b912210ee00000000f1f15303fc66650f1917423bf6000000010c700006660000262736e2588c356183d06a4523cf872621188c6b910b0a67105b200000658000330246582d510ea248692e0000272000002728896a3ca4feca819519880d499a0000000256524221024b389aa3212e55900001d0300000000000202f28ccb0f43d280003b0e00006ae8000028c00007e30a0a1d5820d42f900002c4e000070c18db46f6000070500000c5c5588f7fabc84f3a28d8d058000000021106f0265518a2263cb450dab00000000d5c92634a365d5829029c70a6a4
  | 79 => 0x6a08bb9206054ac4dfcba3a5aa24e25e2c8189bc125005a000001fae0ee8065400017e400640000b2702da37c8569000008b051daa1b87a1982f1c728b08e4b935b397e695159a0b55377243894f88af44df43d0019b99d451d27d74ea486a800006ffc775800000000000000023b2460914400027952214841c9bc1bfb434c36287bc90c2000040cc0f300001b90964c9918f131f5c975c94d859b1c6c000124985fa01888cad4a5a3944fd83ddc19a0000498e000028f868951d879788a400001b8867e4000000047924728f3916174bdc0728b59102830e08c90e5e0c973aae22b109c873f320813782a6207a4f3c71585c521f3184c38c10bea87c00004b3c91e0c4900003a00000000046c4af940000ee955987110f60aa7311f4aec86c097c01b1273d40cf9a9d000030ad2e98cc540642dcd20d28ab00000000046000002ac66315291bc6320aacc03790b9109e881892462b5c0000a030405231e00e8000122b1f9a090811d102b26e600fe83c50f119e1154c349129b86d233689410904936d340a56c52f9206819e6a2dc635028338ce32ed318857449642be86910a413af0059505bab1109d6a3c543aa298009e6b512be00952c1c0000a739816114e17b8c0e1d5d1936653454213fe214e5d114e61b7f202646893b6817825be8b30c9980003d780acc00029fe580e6cbc519aaf4163c0aa4b8823e1561e4144b728825295a7368ab98d12359e3aa882b0d2d022c1fdcaa01b9239ae318907c81d0000034695070000048856e914c9145464a7984ab682c82ad02cecbd224b11a0a132532b209a343c0000c4e0c64406a019c3d101aa000058751638da934484f24c649a1c2330a4c15a8aabd01f624f4df1215a0a180e486d726e32ad2023d4428bb33db8325886321ed5162adc057000004ebc000114b211500006cd94dfaae900009374fa1a386565a4e94b6e0a9f23021005436800000000584000000000001ff00000094000000000000b3637a67fc955595eb000000000fb83b64da66d40a9a800000008af856aa41511d200013da918f05e6afd559a99e016543dd81091197569608448b399c71780317d57910bc40603c24beb0e274618365c5d903c023460f807dda5f92bb2a5784e705b202000058758876718b85a212b696653dec1b18bc52529475007582249c5a00007d58ba400760b96a0d4e7921d9308aa2680002b3b288a324c07f095900008d003801ca108c40000b5e9fd0185a551893f0bae22b8a890000000003b88fdd58f8c902e1a838070d0000449a4bc157b8f494ed676608f000002fba00006618000000076f40ec000000009dd8c0d170a00007d4cc4f04d310e6630c000000038940000733a213553678340001771584014e05c9844b1bf248190e3a869017c00009e89761000005fd02721db53be9d882dea
  | 80 => 0x277f364c1f3432225bb2cbe888c2c801c8285e93cd5d409b845ae072cdb00d703c1c806099596594b6a1cb0d768207225c6934ae886b5087c0b04d160b1c1d401c1c8aba7e9571423b84d20a7b22da2ab90a284b521b2245821881cd0a9281755e212875792388c78baa012d126cd40dd0887445a62f43b80a7940324790b248bc24756a6bd04004ba0dba9cec27f98d135a20a4c2d9a08c3abe80fd5492369587892bca0c214341a4aed535502cc3f0c55f815119f641583dd498c0f150f129798875a0d82b824e1c30b8db449cc03815470413003276d0fd60241359694ecfde2c0457f2ad64bc39025403436bc9d3095422c65688cc182a11bbc8aed3a783321f0e656436115f707608c201571d4821b46ca5335a5b82d921eed58512d7006012f13570f6204340f78e1023c44d6a02d06e029b800004a90a4f866800004c0c9f98ee04c86a9201058f463fe276855431663430c4a2880691b546de571caa116443ff401c0e5b11f844163f508ca80000000405400016f54608110401d13c212a028dc7101e4d586482e40000f5c199e60ed0051e331d962d614ed1f8e55147b740001a49312c33300000a5c000000013ed000026e62538e38892600004a1000017cf28f48a5d08c00001ea8000149d196200000000000027905ee08e89c081d709c4a72000003c64752946400016d300000000f0a9ba606a04d54ba8811b1e629c2d3d42647492a000126b0a933c8463fc00004dd145e68f455502ca000060b8ae525e350aa7f800aea3720d46805c1978368469c2a38187267f3410148938b8a5435e8a530dc027e7445e794807e1ae34c7a79c07c8a085150a000074f2216000000005f10f101c3a74180001cfe1bd611a900593fb11d8232409f07112c905c1867923190e0664049f823df160402909542bdf28962cb46cd8d8301904eb82a8855b19c2abfc35b80004c1e9a645d00e11000000007da8000061a44b05b91eb70000915400000004a0e20c80000000000000000001ea3181c5914c77000000009d30000000026fc02f48f2972600000000b79145e00004b70000000007105ffc000000041bc4720a292c0d25fe180cd378440094200012861fe80dca000130e13cd260a989060f1e2e533030288e980102d0a0f3d60aa7694f247df80000a9a486258a52bd2049198223512ab29c056020708f62180a37e83e980001f45000045a902c00004178719811c8ae200008cf882500003ac8161ca2d13e355dc64985bf2ba71594239493c91313e8c2e74bed020f3b667ba83fb1ae23742838876e8f573c706aa8cea8dea1e36068093b2a0d1d1826f53972476100403a42d695943ee6577c26b815c1314580941b13c501c2178559986de28fc8f803752a9412c8ae3c293000046640134556ab0206da00003bea09222261ca94f7837b384c
  | 81 => 0x841e0b8b955d4d0241889e988d923ac6300f3b9fc63b40777871718e1488e3fd47d88d5b51a02988ef50000294a8e5d144a5685742947913e0b6038ca177c0be8b8600003d58a9992882d3ea5b41b9205f000047c40000aee0000187ce4a89b901040001331ab934e122a082af92d2000077dd3190000188a823838e11880950a1e0e62001e2f8e7ec91dea8ca000061409ca8000265e3838ff4800000001b54dfe0bb7159e891400005291514686c6f0834d13027340a1c939400be0000d89a7e404c8a36c143000016723d4d5c5a71e299089d800019601cc4000067aa024556c53a0d020efa06ce3bb53ec000045920001505177f4a204785037800008b896c4a1486b600003cf440b000007ba8594776000045820000a48a257497e32f446298a42dae000000013802eba0001478072207a49928a6a0a6f5384098cf4e22e249527344ac11f10295c7ed48dd20370000a1dc3cb9f541f4a161856700b850ae35280000e6e10ac1aec73500001fac5290c758447032c6a94cd709de3b941789529925f0fda11992f7991a556a239d4431c2d2d0c8bdd0a9091c0ffe38d4bfc91c3056a535561606232a3417e03b025cd40544e8c746ab8138ea59a4000136300005fb400007cf000092342a985f712860f34d0c9e4528dc826000010870b906d4c4b804d53e109278fb510a529240000bd2800000006171605a2a622fe7ca06d81d4526a490708e22963365c6a9009b8a1d3cde6978d999a6a3ac00000a878f880898165c8f120ae0f28406475f1fc50b3e13155eca2b40bbc8d503d51a5b28162d20fb10d6e22540da4442a66952c244751b61abb44042caccef9ca91124ac949fa8d15246666ad2fd085c25f48d2ccb8aa9e0000409d53e81481db26e9056308232f3a00010ae950d22689d00d8783491a28852160ea3e53ca6000053197d44884889c000000048f0862c14782543f227214000000028a8241c25504b6465813415bc84a204c0000150611a100007508176896200000b4c0000b56368c3af432c1e0f3c0869ac1f3123d4af60df800000004ef21c783c396a03afc66851949b99000000007e8215004b862f077a00000f6003ac90f2785093807910c42a642fb278acf4da7381f4024b54718231423a39680172a2117c81b2c98f0efc4d3c83b800000002f3e0000000191339103854c7a11f52edaa7b53b3095c0cd806f8416a477000000001d4011e349053d8d880a833d0666f0000214f2704361c8e891a903641fe0db8025d113c91ed4660de809a43c8c0000000000000000000000000007e80002a432a9e480d20f8000429a3161025a6a34410a5a54698fba33ce94244ff800003e86a412532c30320e6bdcbc082254ca881049ce91c11a5000010c1a38f43d866492d1910e09300000cf728e7247e6fa1425209522100a50594
  | 82 => 0xd28188521d0f072a6e3d2d5d892cc17b64fd0f109b6b45fea108b938ea8161a0000ae9800003dc4ac0f8b9c463806693c7f08c3e391471841b1a128157e7010b1322e610f80f846d3a47e57a410a0b89a52d221a9638430a8b356588384ee8276327b2ae0d4e0a6e93a76501c0e7821f00004b544b1a35e5088992400000000000000026c9bd212245530a239baa3d3a6f644f09b4015a6256912400a83d5a0000000186600000000a5e96ad0000921044020691f3e220c4ce19b111665754759a04a4b681f680000000121e811423c0000000000015c2000012f212c528e000021764c809942772556e8e1d0e102fa00005074d90224c00000398a602a7a36948a3c58f87e028ec368d23e99e354de9b84aeb1e3a00002b68bca80004d520000d3385c6296e7bf80169b372d76000069a800000009a6cc911e764868775000fa6a1000e04051e688f6181e73888d72a194e5493050ef1d32073820f80000072511a718ce09a7e050e673e0ed3983c530200000002a75567c6a540000000036c536cce010e30922343cea99ee6443e26e826f95cf00000a41127a9d427a026a123a83f61c1a931507b276f4ac04f982ec29a14e6a546d2b7888e39200001555107e55b201f41d89de8417ea904b291531000062810ab103f0af4000108d88461aee748c6cf05cc4cb000000000000179a2db400000001cc28d6414000002ac2ad2005b00000000aafc370000021521d6882085190d78a1442ca80bf000028ec41c081c19e87ce0000274431a87cf505194730000a300dc1000041546008b3f12be00009eac0001847378a00001a79e47129889ccb32161a2020344c5eea9574c50000053906e8362218144468000277e8ee100ea35b1cd24310cae80e70486872000e242e2e0a4bc83ab8540062a5000d79133a0000637c2a5a5744dbe5b44c9b145656a60000000000016ae3cecaa5297f42049d9043aa7c043ec56001241a9200000000d1a86570d700000606a598000074786370e2f24cc2ed80001b9547d41af82e70a5a000028d11348fd3243a44485269f7b01a60828aca8b5d000000012058d4f43fa4870f798caf15100e580f507d43ed6000000006a600004afc1ba17e83684927159c9fa10a949848000117133586cc159b863745e208202da02583bc60000b2509750000a8ac45d80002a4e83b4000000005de8d040ea85682ca815483f4284300007808d488cb20000ade0145024236103a90608266649b097ac0001df346540000000152d577e2371480a8612402508800000000000713099b26160000561144909f13f0a8b640002b912dfc0034f44a9160e9e454d5a5242136c66ee08ee17a90666000162180002b720000d050000000048bcf688aff575c7c84549232f1abe00012a190cd3f30940400029a048800000c76800046c
  | 83 => 0xca00008a7000000000000000000000009394fbd11590000672c24712055446afdd215069c52620000a542bc53f6e00005028dd400002a703ee0000000000007e8800032be00006eb8435062e2f5080616a225549a3488610dc33a447b46ad29d715908b3c7288684394836c4ff60f4a0eda284c353a9ee17fe9ae0b7b1ccc448c10e1591a34f51687714abb92483d407e54000270d3b5e000128709b236b8342c12f13e50daeafe80001e7c0000655838e8a6a4d4485a400000000000247525b0000000040f49a49d4000000000c3c1d27483c00000001d2f33f033ece3d176e2b6e18d8699930454005cd4d000a7609947e947b61c5200007f7000000004bf00d14a8a19661e6e155ce5f04e7521e9688ebc94bf0a7a002c00007d2089a804840224ef35660000000258755ac0000a05006b38aea19d5930c3a23202c4cdd61c0f350206352d7a694382001711ce27ef539a34a808d189a3658262c4701e0555da82b472c2b6241d0ac78000000040b48218c46000051ac4a40ffcabb6000064dce158dc34dc061b8000000057101770e4b109a01267ba4000114d505a0000acf00000000202400015ea00009d3400007f300001970ae900000000000030816383446245d6149a8f33944820768104d40e648c8b4d000040cc6600c6c1c9e1df2913d6118b3400001e40000000042a817d12fe80000000000000021160000831c000187c07be000121c00004646447c00005fb1e180000fe6188456f4000000026bd000069d93bb9c302a3e9e702ad018f1ed04dd496c000033b626c4108232800000ba000028872e66827842a207b4d1e91b4cd79cca09c849cc72588ba3e7c00000001ee03e3e53e0d9e800027da40e0dd6800027300fbc60f9cac4058a2782eaa6203b12000120483a92f4c2648278104839cc0f54191182511b618546698ca508be4c98a6703940000234cd5927e142f20368f73a4a0161e1db03aa9311153c4e3098e130e24b2aae0e24957811800dfc27d20a016f87b3d2e412371d12408cde58000000085600000000051ca2043f90000198499894b52a9f0000048400008c7109658bc8e003162a8807acdaa82aa2fae4e7c85c0af9174637b00002707462a79fc98128f5460407481c792492d20b024a47000012800000000295237e00000ae6800058668c24e5a0000091600000000b8900003b102b2800000000000b3707db282678e40001e5800001ae400000003c0600001eda3dc30e800013b3a6d5000092740000000000071f881f0d0c0000126d16800001336a0dc72b0b1d49ec216559e293224e4626cdd5800034c82e88b7216ae401e151cfd4800015b682bd17d9314000000014b60bbe282e0000c612b3600000000ed69ef2383874f83a4a3a4084e7afcb7a10d200000000afe09144c0252bd3ea917c4ccaa5dc00
  | 84 => 0x92aa4654aa000000021be29e08d8cc2e8f39287000000001e140000987400009bf44567af42bda1e54e3e9b38ff38a8704667068e840f0b0112193c837268900009afc000000000c269b800008621e7e00007b48000000002b0ae61b5b32
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x84747650e51042ab39ec528821555cf6294410aace7a14a20855573d0a510423bbb285288211d1d94294410e8a64194a20847b75582410433928ac120821179cf65104108bae7b28820846e72d944104236b96ca208211e5c16510410c3ca8b18820861d5458c41043172a2c4208218b5516210410a6ae9288820865663944410432ab1ca2208219998a5110410ccac5288820853775504410431caa4c0208219c94560104108dce5b2c620846d72d96310432ca9cc1188219c945608c410ce4a2b00620845e73d96210422eb9ecb108219a54a6088410ce4a2b04420867251580210423ab8acb200218d95261900108eeeab0c80084757694640042b8b8ca120021179cf65100108bae7b28800846e72d944004236b96ca200211d5c565100108bce6328800845d731944004237390ca200211b5c86510010c3ca8b18800861d5458c40043172a2c4200218b5516210010c6aa9308800847775584400423abb4a2200219598e5110010caac72888008666629444004332b14a2200211d5c5658c010caca730c600847775586300423abb4a31802199d8a514c010cc8c528a600843e74d94300421eba6ca180211b9cb650c0108dae5b28600847571594300421f3a0ca180210f5d0650c0108dce4328600846d72194300430eb24a61802187591530c010c9ca6b10600864d53588300432aa9cc2180211ddd5610c0108eaed288600863664944300431ab24a2180219998a510c010ccac52886008475715962004333294c3100211ddd561880108eaed28c400865763945200432a31ca2900210f9d3650801087ae9b28400845e73d94200422eb9eca100211d5c5650801087ce8328400843d74194200422f398ca10021175cc6508010c5ac9290400864d639482004316b22a4100219358d5208010ccaa5308400847775584200423abb4a2100218d9925108010c6ac9288400865663944200432ab1ca2100211d5db54c40108eaec2a620085567315310042aab98a988021599c854c4010acae42a6200847576d4f100423abb0a7880214d9d053c4010a6ae829e20085667214f10042b2b90a7880211d5db52c40108eaec29620085367414b100429aba0a588021559cc52c4010aaae6296200847576946100423cbb6a9080211e5da51840108ecedaa2200857170551100423b3b0a888021559cc5444010aaae62a220085667215110042b2b90a8880215c9c054440108eceda9a20084767614d100429b3a0a6880214d5d05344010acce429a20085657214d100423b3b6a4880211d9d85244010a6ce829220085357414910042ab398a488021555cc5244010ae2eb20220087315490110042b838eca880211e9db5444010ae4e3aa2200847a7694510042b93b4a2880219c9da5144010ae2e928a2008573759051004398aa482880215cdd54144010
  | 1 => 0x20442e839a4010221b458d2008110bc6ec90040886e376480204437132a4010221d89952008110dc6c890040887a2644802044370b224010221e85912008110d42c890040887c37348020442f139a4010221781cd2008110f80e690040885c0734802044371b1a4010221f098d2008110dc2c690040887c1634802044360b1a40102211d1c563950108e8e2b14a80843f76550540430eaa2c62a0218b5516215010c3cc8b18a80864e639885404326b1cc42a0218b9916215010c9cc6b10a80864d63588540432b31cc22a0219558e6115010cccc5308a80866562984540432d31cc02a0219658e6015010cd4c5300a80866962980540433938cc02a0211b9ca6494c108dae5324a608474715925304237b92c0a98211b1c96054c108beeca98a60861d6454c5304326a9ac429821875926314c10c5cc9310a60862d649885304317322c4298218b5916214c10c9cc6b10a60863664984530431ab24c2298219998a6114c10ccac5308a608639649805304334b14c0298211b9cb65d0c108dae5b2e8608476719974304237390cba18211b5c865d0c108ece232e860847a7019743043172a2c5a18218b55162d0c108ece332c860846e721964304236b90cb218211d9c46590c108ece332a8608477715954304237390caa18211b5c86550c108ece232a860847575d85430423aba8c2a18218d9506150c10caca630a8608476719944304237390ca218211b5c86510c108ece2328860847a70194430422f39cc929021175ce64948108e8e2b24a40845f73581520422e39ac0a90211bdd95214810c5ac8a90a40864d63548520430f324c629021875926314810c3cc8b18a40861d6458c5204316b24c4290219358e6214810c6cc9308a40863564984520432b31cc2290219558e6114810c72c9300a40865963980520422f39ecba1021175cf65d08108ece332e840845e73197420422eb98cba10211d9c465d08108f4e032e840861e5458f420430eaa2c7a10211d9c665908108bce632c840845d73196420423b388cb210211d9c665508108eee2b2a840845e73195420422eb98caa10211d9c465508108eaebb0a840847575185420431b2a0c2a10219994861508108ece3328840845e73194420422eb98ca210211d9c465108108f4e0328840847671997320421f3a0cb990210f5d065cc8108ece232e640847671996320421f3a0cb190210f5d0658c8108ece232c640847671995320423d384ca990210f9d0654c81087ae832a64084767119532042a6392a699021531cd524c8108ece3328640843e74194320421eba0ca190211d9c4650c8108f4e0328640864f654c83204326b2a64190218d5906494410aace6324a2085557319251042b3390c928821595c86494410acce5b1ca20856572d8e51042b33968728821595cb43944108eeeca1ca2
  | 2 => 0x6018221b4589300c110f82c498060886c1624c0304426b39cc990221355ce64c81108e8eab2640885647550b204436231a6590221781c132c8110d64c8a0640886b16450320443d0a128190221f04cb30c8110b62e818640886d3630c320442f0b906190221f08c830c81108ecebb24408847675192204426b398c910221355cc64881108ecebb1c40884767518e204425b3a0c7102212d5d06388110ccccb9944088666650ca2044363b186510221785c03288110d62c920440886b36450220443e01946110221b418d3088110bc0e498440887c3324c2204433332e4110221359ce65481109aae732a40884b774595204425a3a2ca9022135dcd65481109a8e6b2a40884f370595204426b39cc890221355ce64481109e2e1322408847775591204423a3aac89022135dcd64481109a8e6b2240884d67398d2044273b92c6902213cdc163481109acec31a40886c57218d2044368b80c690221b118f5248110d88c629240886c46390920442723b28490221591d54248110d88c6a1240885e07050920442733b46490221b118e32481109c8ec99240886c4634c920442f038264902213c9db5048110da6c7a8240886d063d4120442f1396a090221b4d8e4048110da0c720240884f0765012044359b228090221b4d8d4048110da0c6a0240885e07250120443d0a1280902213c9da3048110da0c718240887c2328c120442783b26090221b418d3048110bc0e498240887c1324c1204436831e4090221599d62048110d88c7102408847675d90204426b39ec810221355cf640811096aed3204088636659902044359384c8102218d9956408110d64e0b20408847675190204425b3a0c810221359cc64081109aae632040884e6721902044279380c8102211d9d7630811096ce9b1840884b574d8c204426abb4c610221959966308110d2cc931840886956498c204432b32ac610221a59916308110d2ac8b1840886c47258c2044368382c6102211d9d4630811096ce831840884b57418c204426b398c610221399c863081109e4e031840884e576cc8204433332e6410221a95933208110d8ac799040884e5760c820443333286410221a95903208110d8ac619040885e1700c82044359326a010221ac5935008110da4c7a8040886d163d402044278bb48010221ac5924008110da4c720040886d16390020442f0b948010221ac9914008110d62c8a0040886d2635002044368b1a80102213c5db3008110d62c998040886d163cc020443e199660102213c5d83008110b62e818040886b1640c02044368b186010221785c83008110f8064180408866665c802044352b264010221b158f2008110d62c910040886d16388020442f0b94401022139dd92008110cccca90040886a56448020442e239a4010221b158d20081109e6ec90040886b164480
  | 3 => 0xd832501109e2ec19280885b2740c940442d8ba064a0221e450c3250110f428419280887c1320c9404432b32cc620221959956310110ccccb31080886c6639884044362b1cc420221999956210110d8cc6b1080886c56358840443393acc0202213c5db5010110da4c7a8080886d163d404044371316a020221b858b5010110c6ccba00808869563d004044352b168020221b498e4010110da2c720080886e2629004044370b1480202212ddd94010110c6ccaa008088695635004044352b128020221ac98140101109e6eca0080886d2635004044368b1a8020221b89894010110dc2c4a0080884e6729933044272b94c9982211d1d564cc110aa8eaa1e60885d0704cb30443593228198221ac59140cc110f2286a06608847675d92304423b3a8c918221399c8648c1109cae43246088656658ca304432b3286518221745c0328c110d62c920460886b364502304432b32e6118221399ca654c1109cae532a60884b774595304425a3a2ca9822139dc9654c1109c8e4b2a60884f3705953044273394c898221395ca644c1109e2e1322608847775591304423a3aac89822139dc9644c1109c8e4b2260884d47650d30442aa3aa8698221741c1434c110d8ea631260886c4531893044363218c498221b150c624c110dc2e031260884d676cc930443623166498221b1189324c110ba0e099260884f276d4130442e939ea098221b8d8b504c110dc0c5a8260886e362901304437031480982213c1d9404c110d66c8a0260885d07350130443c8a1a8098221b8d89404c110dc0c4a0260886e062cc130442ab3ac6098221b118a304c1108ecebb2060884e672d903044272b96c8182212d5da640c110c6ccb32060886b270990304431b32ac818221ac9c1640c1108ecea32060884b674190304426b398c818221399c8640c1109cae432060884f270190304433332cc418221a9992620c110d4ac93106088666655883044353322c418221a9591620c110dc0e0b1060884d5768c8304432b32c6418221a5592320c110d8ac51906088656650c8304434ab206418221b1588320c110ba2e019060886b264d403044358b26a018221b898b500c110dc2c5a8060884f1769003044358b248018221745ce400c110dc4c520060886e16290030443593228018221ac591400c110dc4c4a0060886e162500304432b32e6018221a5593300c110d8ac598060886b1648c030442e8b9c6018221b858a300c1109aeec9806088656654c0304434ab226018221711c9300c110d8ac498060884f3764c03044358b226018221781c9300c110dc2c498060885d3764c03044369bb26018221b4995300c110ea4ca98060886d3644c030443c93226018221b4591300c110f22c89806088691644c030443e1b926018221741c9300c110f80e498060885c0724c030443e1312
  | 4 => 0xa0e6a9480885d273d0a40442e8b9e85202215cdd54290110ae0eaa1480884f3764ca40442783b265202213c9d832901109e2ec19480887c1320ca404426bb9acaa0221351cd65501109cee4b2a80884e4725954044279b82caa02218d5945450110b2ae62a280885a57215140442d2b9686a02216c9c34350110a68eaa1a808859573d0940442d938684a02214d1d542501109e4eda8280885367590140442d8ba4caa0221ac5d26550110ce4ea32a808857275d9140442d93aec8a0221cc9d76450110b62e7b2280885b172d91404433832ea8a0221cc1975450110b62e7aa280885b172d5140442793b4a8a02216c9d25450110e66a92a280886706555140442e9b9aa8a0221741cd5450110bc6e4aa280885e07255140442793b0a8a0221749cc5450110ba2e62a280885e27215140442f0b90a8a02216c9d85450110d64ec2a280885b27515140443993a8a8a0221e49cc5450110b62e62a280887917315140442c8b98a8a0221e89c85450110b62e42a280887a17215140442d0b90a8a02215c1d56350110bc6e4b1a80885e07258d4044368b18c6a02213c9da53501109e2ed29a80886706594d40442d93a4a6a02216c5d253501109e6eca9a80884f07654d40442d9ba2a6a02216c1d15350110bc6e4a9a80885e07254d4044338328a6a02216c9d05350110b62e829a80884f276d0d40442f139686a0221785cb4350110b64eda1a80886b276d0d40442d93ae86a02216c1d74350110f26a7a1a808879053d0d40443d139686a02216c5cb4350110f42e5a1a80885a172d0d40442d8ba486a02215cdd54350110ae0eaa1a80887337550d40442d93aa86a02216c1d54350110e60eaa1a80887937350d40443c9b1a86a0221e418d4350110f24a6a1a80887915350d40442d9b9286a02213c9d84350110b64e821a80887914310d40442b83aac4a022174dcd6250110ba0e6b1280886e16218940442793b4a4a02213c5da5250110ce0cb29280885b27494940442d8ba4a4a02213cdd952501109e0eca9280885b37454940442d83a2a4a022174dcd5250110ba0e6a9280886706514940442d93a0a4a02216c5d052501109e4eda1280885d273d0940442e8b9e84a02216c9db4250110d64eda1280885b275d0940442d83ae84a0221e49cf4250110b62e7a12808879173d0940442c8b9e84a0221e8d4b4250110f40a5a1280885b17490940442b9baa84a02215c1d54250110e66eaa1280885b27550940442d83aa84a0221cc1d54250110b66e6a1280887a37250940443d1b1284a0221e81894250110f44a4a1280887a15250940442793b084a02216c9d04250110f428421280885b274cc940442d8ba664a0221e850b3250110b64e919280885b1748c940443c8a1c64a02213cdd932501109e0ec99280885b2744c940442d8ba264a02213c9
  | 5 => 0x84f170190324432ab28a619221715c8530c9109aaed21864885c57290c32442aa3aa861922199594520c910b8ae629064884e57690832442e2b9c8419221591d5420c910b8ae719064884d7764c832442e8382641922139dd9320c910bc0e099064885c7764c83244363bb26419221719d5320c910b88ea99064885c7744c832442e2ba26419221f0dc1320c910b88e099064887c0704c832442e038264192211d9d6600c910f826530064884f27598032443393acc0192213c5d2600c910d8a64b0064887c13258032442783aac0192213cdd1600c910da6a6b0064886d053580324436921ac019221b450d600c910dc6a4b0064886e0525803244371212c019221b8509600c910da664b0064886e2325803244368992c019221b84c9600c910d8264b0064885577355350442aa39aa9a822159dc954d4110ac8e4aa6a0886356415350442ab398a9a8221555cc54d4110acce42a6a08856572153504429bba2a7a82214d1d153d4110acee4a9ea0885647254f504429bba2a5a82214d1d152d4110aaee6a96a0885547354b50442e9398c9a8221745cc64d4110bc4e4326a0885e1721935044358b26a9a822174dcd54d4110ba0e6aa6a0885e37255350442f0392a9a8221ac59054d4110ba4e62a6a0885d17315350442f1390a9a8221785c854d4110bc4e5b1ea0885e172d8f5044369b1cc7a82216cdd153d4110b60e8a9ea0885e37254f50442f0392a7a82213c9db43d41109e2eda1ea0885e272d0f50442f0b9687a82213c9d843d41109e2ec21ea0885d273d8b50442e8b9ec5a8221b8d8a62d4110b66e8a96a0885b07454b50442e9b9aa5a8221741cd52d41109e4eda16a0884f176d0b50442e939e85a8221745cf42d41109e4ec216a0884f17610b5044279bb265a82213c1d932d41109e4ec196a0884f1760cb50443e099065a8221359cc65d01109aae632e80884e6721974044272b90cba0221655cc54d0110b4ae42a680884747558f40442d2b9687a02214d1d543d01108e8eab16808859573d0b404429a3aa85a022139dc963901109c8e4b1c80884d77358a404426a39ac5202218d9974090110ce4cbaa480886726555240442e9b9aa920221741cd5490110bc6e4aa480885e0725524044398aa0a920221749cc5490110ba2e62a480885e27215240442f0b90a9202215c9d76390110bc6e4b1c80885e07258e40442b93a8c720221b458c6390110bc4e431c80885e17218e4044278bb4a7202213cdd95390110b66e8a9c80885b07454e40442f1b92a720221781c95390110bc4e5a1c80885e172d0e40442b9baa87202215c1d54390110ae4ebb1480885d37358a40442e839ac5202215c9d46290110ba4e631480885d17318a4044370b10c5202213c5da52901109e6eca9480885b37454a40442d83a2a52022174dcd5290110b
  | 6 => 0x24436831ec0a92213c5d36054910dc6a5b02a4884f170990524431ab20a8292213cdc16314910bc2e1290a48847776548524429a3a2a42922139dd95214910b48e8a90a4885c47354852442f1b82a429221359cf65d09109aae7b2e84884f170d974244279b82cba1221359cc65d09109aae632e84886c663d4b4244363318a5a12211d9d660d0910da4c730684886d16398342442793acc1a12219c9d660d0910da4c6b0684886d16358342442783aac1a1221b8d4960d0910dc0a4b0684884d673d96424426ab9ecb212213c5c365909109e6e0b2c84886376515242442d2b90a9212213cdc163909109e0e0b1c84887245494a42442f0b84a521221691d15290910b88e6a9484885e37054a42442e339e8521221785c342909108eceb30484884f170d95424423ab86caa12219c5c365509108eceb32a84884d773595424426a39acaa12213cdc16550910ccae432a84884f27018d4244278b80c6a1221399da5250910cc8cb29284885e17094942442723b2a4a1221991955250910b48e8a9284885c47354942442f1b82a4a1221991974250910b8ce7a1284885e170d09424431a32c84a12211d9d460509109ace630284884d5731814244278b86ca2122135dcd65109109a8e6b2884884f370594424426b398ca21221355cc65109109cce43288488635651504244272bb6a421221c9150521091096eeca108488534755084244273bb28421221591d542109108eceb30084884f27598042443393acc0212213c1d56010910d66a8b0084886b0545804244371a92c021221b81496010910d6684b0084886e2425804244358a12c021221b8509601091096ce9b2e64884b574d973244278b86cb992213cdc165cc9108ecebb26648847575d933244279384c9992213c5c264cc9109e4e032664884f17019332442b23aa8599221a999142cc9108eceb30664884b674d96324425aba6cb192213c5c3658c9109e6e0b2c648847675d92324423abaec9192213c9c2648c9109e2e132464884f2701923244278b80c919221551d5438c910d2cc8a1c6488476759823244278b86ca992212ddd1654c910968e8b2a64884f370595324426ab9cc899221395ca644c9109e4e132264884f170991324423bbaac8992211d1d5644c9109e6e0b2264884f0705913244279380c8992213c5c0644c9109e4ebb0264884f174d81324423b3a8c0992212d9d0604c91096ae830264885b17418132442793a8c0992219c9d4604c910d64e830264884f1741813244358ba0c0992212c5d0604c910dc66430264886d2321813244278b86ca192212ddd1650c910968e8b2864884f370594324425b3a0ca192212d5d0650c9109e4e1b2064884f170d903244279384c8192213c5c2640c9108eeeab20648847475590324423b3a8c8192211d5d4640c9109e4e0320648
  | 7 => 0x82a2212ddd95415110b28e6aa0a8885a47255054442d9b82a82a2214ddd95415110c6eecaa0a88871773550544429a39aa82a221c51cd5415110a28e6aa0a88872772550544429a392a82a221c91c95415110a48e4aa0a888537705505444399b82a82a221c55526315110e2aa8b18a88872554988544436331cc42a221b158e6215110e4aa8b10a8886c6635885444362b1ac42a221cc5516015110da4c6b00a8886d1635805444371312c02a221b858960151109e2e1326a6884f17098b5344273394c929a21395ca6494d10aaae62a4a6884f3745825344369a9ac129a21acdc36454d10d2ae6322a6886b170191534434a326a6a9a218d1925354d10d4ec9b12a6886a464d895344353b20c4a9a21a91906254d10d8ea6312a6886b364d815344358326c0a9a21b8d8b6054d10dc0c5b02a6884f174d815344369a9ec0a9a213c5c26414d10c6ac82a0a6885d17094c534423bbb2a629a214d1d15314d109aeeca98a6885947454c53442e2392a629a2174dc15314d109e6e0b10a6884e672d974344272b96cba1a213c5c365d0d109e6e0b2e86884e6721974344272b90cba1a21b1d4e62d0d10d88a73168688476759834344371314c1a1a21b858a60d0d109e4eb3068688672759834344371312c1a1a21b858960d0d109e0eab0686886d353583434436829ac1a1a21399cb6590d109cae5b2c86884f170d964344279b82cb21a218dd945490d10b2ae62a486887145494e43442e8b84a721a21651d15390d10b88e4a9c86885d37054e43442e33968721a21745c34390d109e6e0b1486884f07058a434423b3acc121a213c5c36550d108eae1b2a868867170d95434423b3accaa1a2139dc96550d109c8e4b2a86884f370595434432ab98caa1a21359da5350d10ca8cb29a86885d17094d434426a3b2a6a1a21951955350d10b28e8a9a86885c47254d43442e9b82a6a1a21951974350d10b8ce5a1a86885d170d0d434431a32c86a1a213c9c06250d109e2e03128688476751814344273390c0a1a21395c86050d109e2e1b2886884e7725944344272392ca21a213cdc16510d109ace632886884e6721944344272b90ca21a218d5945410d109aaeda9886887145414c434425bbb28621a214d1d54310d109aeeca1886885547550c434423b3acc021a213c9d66010d10ce4eb30086884f0755804344359aa2c021a21ac1516010d10da6a6b0086886d0535804344359a1ac021a21b490d6010d10d6286b0086886d1435804344278b84c9a92213c5c263d49109ace7324a4884d57399252442b2b90a9292213cdd16094910dc6a4b04a4886b370d915244352b90c8a9221ac5c06454910d2ec9b1aa48869464d8d524434bb20c6a9221a51906354910d48c9a92a4886c463d49524431a324a4a9221acd936054910d60c9b02a4886d363d815
  | 8 => 0x1530c5108ecebb2642884d673d93214426ab9ec990a21359ce64c85109aae732642884f270993214423b3a8c990a213c9c064c85108eaed2a642886376415321442b2b90a990a211d9d763c851096ce9b1e42884b574d8f214423b3a8c790a213c9c063c8510a68e8a9642887245490b21442b23aa8590a211d9d764885109e4e132442884d673192214426ab98c910a213c9c064885109e4e1b1c428847675991214426b39cc890a21355ce64485109e4e13224288474755912144279380c890a211d9d6634851096ce931a42884b57498d214423a3aac690a213c1c163485108ecec29242884e47650921442b23aa8490a21a919142485109e4e132042884d673190214426ab98c810a21399c864085109e4e0320428847576150214431ab20a810a212d9d0630851096ae831842884f27018c214423bbb2a410a214d1d15208510a3ae62a6808852d72153404431a2a2c3a02219c9956190110ae4ea30c80885707550640443982a28320221749cc4190110ba2e620c80885e27210640442f0b9083202213c5db31901109e6ec98c80885b3744c64044278bb643202213cdd92190110b66e890c808845f73595404422e39acaa02211bdc965501108d8e4b2a808851d731514044296b90a8a02211e9d85450110b32e62a280885a97215140442d4b9686a0221665cf42501109e4eda0a80886706590540442b83aa82a02219c19541501109e4ec20a80885d27310540442e8b9882a0221789c84150110bc2e420a808867065cc540442d93a662a02216c5d33150110f228798a8088791434c5404433832862a02216c9d03150110b62e818a808867065c8540442d93a642a02216c5d32150110f428590a80887a142485404433832842a02216c9d02150110b62e810a808843f74595304421e3a2ca982211bdc9654c1108d8e4b2a608864f531893044326298c498221a6591300c110b90e498060886c9624c0304421fba2ca902210f1d165481108bee6b2a408845c73595204432631ea4902219318c5248110d52c890040885c8734802044364b1a4010221ac59241c4110ba4e620e20885d17310710442f13908388221785c841c41109ace632420884d5731921044273390c908221395c8648411096ce831c20884b57418e1044273390c708221395c8638411096ce831420884b57418a104426b398c508221355cc6284110d62c920420884f17098f5444273b92c7aa221391c963d51109e6e0b1ea8884f17098b544426bb9ac5aa221351cd62d51109e6e0b16a8886b354582544434baa0c6aa221959506355110d8ec7b12a8886c463d895444363b18c4aa221b118c6255110d4ea8312a888666541895444369b1ec0aa221b418f6055110dc6c5b02a8886e062d815444359aa6c0aa2216c5c254151108eeecaa0a8885547355054442b2392a
  | 9 => 0x8e4b28868845e731944344237390ca21a211b5c86510d108baeda98868847475584434431a2a2c221a213c9c66010d108f0eab00868845e73992524422eb9cc9292218b5c86454910c3ec9b1aa48861c64d8d524430fb20c6a9221871906354910c58c9b12a48864c63d89524431a326c2a92211bdd95214910a58e8a90a48854c73548524421f3a0c0292210f5d060149108bce6300a48845d73180524422f39ecba1221175cf65d09108bce632e848845d73197424432731ea5a12219398c52d09108e8eab0e84884f271983424423c3aac1a1221179cf65909108bae7b2c848852d7215242442963a2a521221531cd52909108e8eab0c848845f73595424422e39acaa12211ddc565509108e8e232a848846e7694942442363b2a4a12214b1d15250910a98e6a92848847675d85424422fb9aca21221171cd65109108bce6328848845d731944244237390ca212211b5db52109108e8eab08848863454584424427938cc0212211e1d5601091087ce9b2e648843d74d97324423a3aac3992210f9d3658c91087ae9b2c648847475586324421fba2ca992210f1d1654c9108ecebb0a648847a75d81324425cba0c0992213c9c4604c91087ee8b28648843c74594324421f3a0ca192210f5d0650c910a9ae4298648854d7314832442a73aa6419221531d5320c910b90e0990648847475584324432a29ac21922199149610c9109e4e33006488478755803244364992c019221551cd54d0510ac8e4aa682884757694f414423abb4a5a0a213c9d660d0510ce4eb306828857275182414429b3aec8a0a214d9d254505108ecec2a2828853676151414431b3b0a8a0a21c59cc5450510e2ae62a28288726721514144392b90a8a0a21cc5c05450510c68a831a828863454189414423bbb2a820a21551cd5410510ac8e4aa082886547558c414432ab1ca620a211d5d85310510a6ae829882886c6639884144362b1cc420a21b198d6210510d8ac6b108288664755884144332b14a420a211d5d85210510a6ae829082886d2639804144368b1cc020a21b898a6010510dc2c5300828867265580414436931ac020a21b458d6010510dc4c4b0082886e162580414423b3aec998a21399cb64cc5109cae5b2662884e6729933144272b94c998a213c9c264cc5108ecea32662884f270193314423abb4a998a218dd9054cc510aaae62a662885347454f314438a2a48798a21551d543cc5108ecebb2462884f2709923144273390c918a21395c8648c5109e4e03246288476759913144273394c898a21395ca644c5109e4e13226288474755913144279380c898a211d9d8534c5109a8eca1a62885547550d314434a3228698a213c9c2640c5109ace632062884e6721903144272b90c818a213c9c0640c5108eaec2a0628863564150314423bbb2a618a214d1d
  | 10 => 0x46d72194438422f39cc929421175ce6494a108deeca90a50862d645485284326b1aa429421879926314a10c3ac9318a50861e6458c528430eb22c6294218b5926214a10c9ac7310a50863664584528431ab22c2294219598d6114a10caac6b08a50845e73d97428422eb9ecba1421179cc65d0a108bae632e850861e5458f428430eaa2c7a1421179cc6590a108bae632c850845e73195428422eb98caa14218d9536150a10ccca5b0a850845e73194428422eb98ca214210f9d065cca1087ae832e650843e74196328421eba0cb194210f9d0654ca1087ae832a650854c7254d32842a639aa4994212e5d0604ca1087ce8328650843d741943284327b2a641942193595320ca10b90e099065086c932580328431b2a2c3204219c59561902108f4ec2a281085a972d0d40842ccb9e84a0421879516310210c3aa8b18810862e545884084316aa2c4204218d5516110210caca6b0c610861d6494c308430eb22a6184219394d620c210c9aa6b10610865553584308434cb226018421721c9300c210d92c49806108666525862084316b24a4104219358e5208210c5ac8a90410864d635482084332a92c210421aa5912008210b90e690041086c96348020842ab398a988421555cc54c4210acce42a6210856572153108429b3a0a7884214d5d053c4210acce429e21085657214f108429b3a0a5884214d5d052c4210aace629621085557314b1084237b92c7aa2211b1c963d51108bee6b16a88845c7358b544430fb20c6aa22193d8f6255110c98c7b12a88862f641895444327b18c4aa2219318c6255110ca8c7b0aa88866462d85544421fbb2a82a221471cd5415110a58e4aa0a8886577158c544432a38ac62a2219398e6215110c9ac7310a88864e635885444326b1ac42a22199dc56215110cc8e2b10a88865663584544432ab1ac22a221999896115110ccac4b08a88845e73184544422eb98c22a2211b9c861151108dae4308a88865a63580544432cb1ac02a2219a9896015110cd2c4b00a88867161580544422f398c02a221175cc60151108dce4300a88846d721805444237394c929a211b5ca6494d10c3ae6322a68861c64d8d5344317b26c4a9a218b1936254d10c5ec8312a68862c641895344327b18c4a9a218d1936154d108beeca98a68851c7454c53442a6392a629a210f9d06014d1087ae8300a68846e721805344236b90c029a211b9cb65d0d108dae5b2e868846e721974344236b90cba1a2193d4e62d0d10c98a7316868847475587434427938cc1a1a211e1d560d0d108dce5b2c868846d72d96434428eb98a921a21471d15390d10a98e4a9c8688474755864344237b92caa1a211b1c96550d108eee2b2a868847471195434422f3b4a6a1a21171d95350d10a38e8a9a868854c7254d434423b3aec2a1a211bdc96510d108d
  | 11 => 0xc4362992c0196211ddd563d0310b4ae5a1e81885377550f40c423bbaac5a0621655cf42d0310a6eeaa1681884e77258e40c4272392c72062135dcd62903109a8e6b1481885a572d0d40c429bbaa86a0621655cf4250310a6eeaa1281886556598c40c432ab2ac620621995966210310d8cc731081886c56398840c4332b2ac420621b198d6210310d8ac6b10818869563d0040c4352b1680206212ddd94010310d2ac6a0081886a56250040c4279bb28020621399ca64cc3109cae532661884777559330c42abbaa8798621399c8648c3109cae432461884e67299130c4272b94c89862139dc9644c3109c8e4b2261885577550d30c4363298c498621b154c624c310d8c8631261886c54318930c426b3b66498621b118b324c310d88c499261886c4628c130c4273396c818621395cb640c310c6acb32061886356559030c4273390c818621395c8640c310ccacb31061886a66498830c4352b24c41862199595620c310d4cc8b1061886a56458830c426abb46418621a5592320c310d8ac51906188695640c830c4362b106418621a5593300c310d8ac598061884d7764c030c434ab226018621711c9300c310d8ac498061884f3764c030c426b39cc990621355ce64c83108eeeab2641885677550b20c436231a6590621359cc64883109aae632441884b67418e20c425aba0c710621b1d8c32883109ace732241884d57399120c426bb9ac890621351cd6448310d8ae431a41886c46394920c436231aa490621b118e4248310aceeaa1241886c46350920c42733b46490621b118e3248310d88c699241886c46388120c426b39ec810621355cf6408310c6acb32041886356559020c426b398c810621355cc640831096ce9b1841884b574d8c20c432ab2cc610621a59926308310d2ac931841886556558c20c434b322c610621a55916308310d88e4b1841884b67418c20c425aba0c610621395db3208310d4ac999041886c563cc820c4352b206410621b158c3208310d4ac990041886c563c8020c4273bb24010621a95912008310b88e690041886c56348020c4279bb240106210fdd95415210c3aa8b18a90862d54588548430f322c62a4219398e6215210c9ac7310a90862e64588548432731ac42a4219358d6215210cacc6b08a908655635845484333312c22a421995896115210ce2c3300a90846e729925384236b94c929c2117dd95314e10c3ac8a98a70864d53588538430eb24c629c218b9926214e10c5ac9310a70862e645885384316b22c429c219398d6214e10c6cc8b08a708635645845384333312c229c21995896114e108dce5b2e870846d72d974384237390cba1c211b5c865d0e10c5ca8b16870862d5458b4384237390cb21c211b5c86590e108dce432a870846d72195438431b2a6c2a1c219594f6150e108dce43288708
  | 12 => 0xaa6211ddd9541531096eecaa0a9885377655054c431bbb2a82a621c55526315310e2aa8b18a9887255498854c436331cc42a621b158e6215310e4aa8b10a9886c66358854c4362b1ac42a6218d5516015310e62a8b00a9886d26358054c4368b1ac02a621b89896015310dc2c4b00a9886b25458054c4338aa2c02a621ac5516015310c62a8b00a9886e26258353c4370b12c1a9e21399ca6494f109cae5324a7885557315253c42b8b80a929e21719cb5394f10ba2e1a9ca7885c672d4d53c42e8b86a6a9e218d5905414f10ae2e02a0a7884777654c53c426bbb2a629e21b494d6014f10da2a6b00a7884e672d9743c4272b96cba1e213c5c265d0f109cce432e87884e57219743c4278b80cba1e21399cb6590f109cae5b2c87884e67299643c4272b94cb21e213c5c26590f109e2e032c87885c672d0e43c4273394caa1e21395ca6550f109e2e132a87884f17019543c432ab98caa1e219c5c06550f10ca8cb29a87886546554d43c42ca3a2a6a1e21719cb4350f109cce430287884e57218143c4278b84ca21e21399c86510f109cae432887884f17019443c425bbb28621e2135dd94310f10da4c6b06a5886d16358352c426b39cc929621355ce6494b10acae42a4a5885717015252c42e339ea529621785c35294b10b8ce7a92a5885e170d4952c431ab20a8296215c5c05414b108eeeca90a5884e77654852c4371292c029621b85496014b109ace7b2e85884d573d9742c4278b84cba1621359cc65d0b109aae632e85884f17019742c426b39ecb21621355cf6590b109ace732c85884d57399642c4278b84cb216213c5c06590b10b8ce7a1485884d67399542c426ab9ccaa16213c5c26550b109e2e032a85886657219542c4338b80caa1621991965250b10cc8caa9285885a47454942c42e339e84a1621359cc6050b109aae630285884f17099442c426b398ca21621355cc6510b109e2e032885884b77650842c4273bb284216212d9d365ccb1096ae9b2e65884f17099732c4278b80cb996211d9d764ccb108eaebb2665886666554b32c42b3baa8599621a999142ccb1096ce9b2c65884b574d9632c4278b84cb196213c5c0658cb108ecebb24658847575d9232c432b32aa71962155dd5438cb10d2cc8a1c65884f17099532c4278b80ca996211ddd5644cb108e8eab2265884f37059132c4278382c8996212d9d0604cb1096ae830265884f17099432c425b3a0ca196212d5d0650cb109e2e032865884777559032c423a3aac8196211d9d4640cb108eaea32065884f27019032c4278b80c819621715ca530cb10b8ae521865885577550c32c42e2b9ca419621715ce420cb10aceeaa1065884d7764c832c4273bb2641962171dd9320cb10d8eec99065885c7754c832c42e2baa641962171dd1320cb10b8ae899065885c4704c832
  | 13 => 0x6348020cb6ca31a401065b6594d200832db2aa690041c65515348020d90c7b1240105e171d892008394aa4a490041d254e5248020ce6cb28a4010673655452008398aa2a290041d454d51480208dce5b1aa98846d72d8d54c422f39ec4aa621175cf625531087eecaa0a9886547158c54c432731cc42a6219358e6215310c9cc6b10a98864d6358854c433238ac42a6219698d6015310cb2c6b00a98866a6258054c4334b12c02a6219c9856015310cd4c4b06a78854e72d4e53c4237394c929e211b5ca6494f10a9ce5b1aa78845f7654c53c4237396cba1e211b5cb65d0f108dce432e878846d7219743c4237396cb21e211b5cb6590f108dce532c878846d7299643c4237394caa1e211b5ca6550f10a38e8a9a87886565318543c432aa98c2a1e211b9c86510f108dae4328878865a6358352c42a739ea529621179ce6494b108bae7324a58854e73d8952c4237bb2a429621179cf65d0b108bae7b2e858845e7319742c422eb98cba1621179cf6590b108bae7b2c858845e7399642c422eb9ccb21621179ce6550b108bae732a858852c7454942c4333290c2a1621995486150b108bce6328858845d7319442c421f3a6cb996210f5d365ccb10ccaa530e658843e74d9632c421eba6cb196219554e618cb1087ce8328658843d7419432c42a6b94a619621535ce520cb10a9eea990658854d754c832c423abb4a7a0e211d5da52d07108ecec2a283886395458041c423bbb2a820e214ddd95410710c6eecaa083886556598c41c438aaa4c620e21955956310710e2aa8b1883886577558c41c432a3aac620e219558e5310710a6ae829883886656598841c4392aa4c420e21b198e6210710d8ac731083886656558841c4392aa2c420e21b198d6210710d8ac6b1083886677558841c43323aac420e219958a5210710a6ae829083887315498041c4338b2ac020e21cc5516010710da4c6b0083886d16358041c4371312c020e21b858960107109cce5b2663884e572d9331c4273394c998e21395ca64cc7108eaed2a663885557315331c4273390c918e21395c8648c7109cce532263884e57299131c423b3b0a698e21a5191434c710cb4a6b0063884e67219031c4272b90c818e218d590540c7108eeeca9863884d673d9321c426ab9ec990e21359ce64c87109aae732643884757695321c42b2b90a990e212d9d363c871096ae9b1e43884d67319221c426ab98c910e21359ce64487109aae732243884b67498d21c425aba4c690e211d9d85248710d48c8a12438866a5258021c426b398c810e21355cc6408710c6ac82a043884b67418c21c425aba0c610e211ddd95208710c6aa830a818864e5318930c4326a98c4986219318e5248310c98c6a9241885b170d5254c42d8b86a8aa621399cb63553109cae5b1aa9884d673d8954c426ab9ec4
  | 14 => 0xa930c601065653986300832aa9cc3180411ddd5618c020c6ca8b0c601063554586300832b29ac3180419554d618c0208eaed28c60104777654630083172a6c4980418b553624c020c9ca7b12601064d53d8930083172a0c4980418b550624c020c9ca6312601064d5318930082673b66498041535d7324c020c9ecb992601070d54cc93008333b14a2980419918a514c020ccec4a8a601066462545300821f3a6ca180410f5d3650c02087ce9328601043d74994300821f3a0ca180410f5d0650c02087aeb320601043f75590300821fbb4a8180410f5da540c02087eecaa0601043d76550300830f324a61804187592530c020c3cc8a98601061d6454c30083172a4c4180418b552620c020c9aa7310601062e545883008316aa2c4180419394d620c020c9aa6b10601054d750c83008326b286418041a3590320c020e1aa8190601047575984300831b2a4c2180418d552610c020caca7308601065553984300823bbaac2180418d951610c020c6aa8b08601065653584300832aa9ac2180411d5da510c020c6cc92886010635649443008333314a2180419958a510c0208eeeca88601063664544300831ab22a21804199989510c020ccac4a88601054d73d532008316aa4c7900418b55063c8020a5ae9a9e401070d5494f2008237bb2a7900419398d53c8020e1ca8a9e401070d5454f2008327bb2a790041931d953c8020e4aa928e4010745539472008392aa2a390041d154d51c80208daed294401063654986200831aaa4c3100419594e6188020caaa730c401063654586200831aaa2c3100419594d6188020caaa6b0c40107195454e200823cbb4a510041cc5515188020ea2a6a8c401061e54d8d200830eaa6c690041879506348020c3aa831a401045e7694d200822e3b4a690041179d953480208b8eca9a401065763945200832a31ca29004195d8d5148020ca8c6a8a401064f73d95200832639eca900411b9db5448020a9ae7aa2401052d759512008317b2ca8900418bd955448020c9ecbb1a401070d54d8d2008236bacc6900418b552634802099ce731a401062d5418d2008327b28c690041c35506348020c9aea31a401064f5418d20083472a0c690041935506348020d1aa831a401060d5418d20082373b6a6900414b5d35348020c98c7a9a40104cc7694d20082a6baca69004193d965348020e1aa929a401046c7654d200832631aa690041331d95348020c9ecaa9a401070e5454d2008386aa2a69004193dd95348020a9ceca9a401054c7654d20083263b2a690041131d95348020ccecb28a401072554945200836231ca290041d154e5148020ccecaa8a401072554545200836231aa290041d154d5148020c5aa9b02401064d53d81200832631ca09004196dcf6548020cb0e7b2a401063b65951200831db2aa89004196d97
  | 15 => 0x1d6494c510822fbb2a628841879915314420c3ac8a98a21063654984510831aaa4c2288419594e6114420caaa7308a21047776544510831b322a2288418d5915114420cacc6a88a21065563544510822f39ccba0841175ce65d04208bce732c821045d73996410822f398caa0841175cc6550420c5aa9b12821064d53d894108316aa0c4a08419354c6250420ccec4a8a821045e73d94410822eb9eca20841179ce65104208bae7328821045d7598c410830f2a4c6208418755263104208beeab18821061e5458c410830eaa2c62084117dda53104208baed298821045f7654c410822ebb2a6208418b5526210420c9ca7310821064d5398841083172a2c4208418b5516210420c9ca6b10821064d53588410832b31ca2208419558e5110420cccc5288821066562944410832b31aa2208419558d5110420cccc4a88821066562544410831caa4c0208419694e6010420cb2a7300821067151980410831d2a2c0208418e5516010420cb4a6b00821065953580410833928ac0208419c545601042087ce932e621043d74997310821f3a4cb188410f5d2658c420c5aa9314621064d5398a3108316aa2c5188419354d628c420ccac528c621063954982310832ca9cc1188418e551608c420cb2a6b04621067251582310821f3a0ca988410f5d0654c420c5aa9b12621064d53d893108316aa0c4988419354c624c420ccec4a8a621043e74994310821eba4ca188419c54560c8420c72a9300421065953980210831caa2c0108419654d6008420ce4a2b00421046d760ca5008316aa4c5200419354e62900208deeab14801062d5458a400826639ac5200419354d62900208eaeb30c801063654986400831aaa4c3200419594e6190020caaa730c801047775586400831b2a2c3200418d5516190020caca6b0c801065553586400823abb4a3200411ddd951900208bce7b28801045d73d94400822f39cca20041175ce65100208bce6328801045d73194400822ebacc620041879526310020c3aa9318801045f7558c400830f2a2c6200418755163100208beed298801045d7694c400822fbb2a620041175d95310020c5aa9310801064e539884008326a9cc4200418b9516210020c5aa8b10801064e535884008326a9ac4200411d5d66110020c6ca9308801063554984400832b29cc2200419554e61100208eeeab08801063654584400831aaa2c2200419594d6110020caaa6b08801047576944400832b31ca2200419558e5110020cccc5288801066562944400823bbb2a2200419598d5110020caac6a888010666625444008332b12a220041535d732cc020c9acb996601070d54ccb3008316aa4c5180419354e628c0208deeab14601062d5458a3008326a9ac518041535d4328c020c9eca194601070d540ca300823abacc3180418d952618c020c6a
  | 16 => 0x822fbb4a7a1041175da53d08208beeca9e841045d7654f420831caa2c1210418d9536150820c6aa9b0a841065653d85420832aa9ec2a10418d9506150820c6aa830a841065653185420832aa98c2a10413c5c06150820cb2a7300841063a54580420832ca9ac021041939cd65cc8208daedaa6641054d73d533208316b2ca9990418b59554cc820a5ae9a9e641064d6594f3208386aa4a799041c395153cc820e1aa8a9e641062d545833208326a9ac1990419654d608c820a9ae4a98641064f654c83208326b2a6419041c3951320c820e1aa8990641063954980320831caa2c0190419694d600c8208daedaa0641054d73d503208296baca819041c39cd540c820e1ae6aa0641062d5498c32082a6bacc61904193596630c820e1aa9318641052d74d4c32082a6baca619041c3552530c8208deeca98641064e6354c32083872a2a619041c3551530c820a9eeca98641064f7654c32082a7ba2a619041535d6430c820c9acb218641070d5490c32082a6baa861904193595430c820e1aa8a1864105c87050c3208394aa4c0190411bdd5600c820c5aa8b00641064d535803208394aa2c0190418795263d4420c3aa931ea21061e5458f510830eaa2c7a88418799253d4420c3ac929ea21061e6454f510830eb22a7a88414d9d35194420a6ae9a8ca21055673d4651082aab9ea328841559cf5494420aaae7aa4a2105567315251082aab98a9288414d9d35394420a6ae9a9ca2107165494e510838aaa4a728841c59515394420e2aa8a9ca2107447254e510829b3a0a7288414d5d05394420acaeb994a21072554cca51083a2a9e6528841c95503294420e8aa6194a2105567319251082aab98c928841599c86494420ae4e0324a21056672d8e51082b9386c728841599cb4394420acae5a1ca2104777650e510823a3b28728841559cf4294420aaae7a14a2104747650a51083a29906528841179cc64544208bae6322a21047676d5151082ab39ea8a8841555cf54544208ecec2a2a2105567315151082aab98a8a88411d9db5354420a6ce9a9aa21053574d4d510838b2a4a6a8841c55525354420e2ca8a9aa2107155454d51083a2392a6a88411d9d85354420a6ce829aa2105357414d51082b2bae64a8841c95533254420e8aa7992a210725540c951083a2a9864a8841591c96454420aace6322a2105557319151082b3390c8a88415c9c06454420ac8e4b1aa21056672d0d51082b2b9686a88411ddd943544208e8eca1aa21055673d0951082aab9e84a88411ddd94254420ae4e0212a2105717010951083a299064a88415c9c03254420ae2e0192a21053674081510829aba040a8841559cc2054420aaae6102a21043d76950510821fbb2a828841879526314420c3aa9318a21061e5458c510830eaa2c628841175da5314420c3cc9298a2106
  | 17 => 0xa0414d9c46055020a6ae2302a81043f76550540830eaa4c62a041875516315020c6aa9308a81063554584540830f324c62a041879916315020c9cc7310a81064d63988540831b324c22a0419598e6115020caac7308a81066662984540831b322c22a0419598d6115020caac6b08a81066662584540832cb1cc02a0419c5866015020c6ca930ea61063554987530831b2a2c3a98418d55161d4c20c5ac9316a61063664987530831ab24c3a98418d99161d4c20c6ac8b0ea61051e74d4e530828eba6a729841559c75394c20aaae3a9ca61046e72992530823bb8ac9298411d1c56494c20aace3aa4a61055571d5253082ab388a929841555c45494c20e1aa8314a61054e7299253082abb8ac929841551c56494c20aace3304a61055571982530828f3a0c129841475d06094c20aace2304a61055571182530828f3a6c6a9841475d36354c20aace3b1aa61055571d8d530822f3b6a8a9841559c75454c20aaae3aa2a61045e7615153082ab388a8a9841555c45454c20e1ca8312a61070d5418953082a7394c8a9841531c96454c20aaee2b22a6105547159153082ac382c8a984193d906254c20c9ac8312a61054e7298553082ad384c2a9841531c96154c20c98c5302a6105567198153082aab8cc0a9841479d06054c20a3ae8302a61064c6218153082ab388c0a9841555c46054c20a3ce8102a61051d74081530821ebb4a8298410fdd95414c20c3ca9318a61061d5498c530822fbb2a629841879915314c20c3ac8a98a61063654984530831aaa4c2298419554e6114c20c6ca8b08a61063554584530832aa9ac229841879926314c20c3ac9318a61062e649885308316b24c4298418d9926114c20c6ac9308a610656639845308333314c2298418d9916114c20c6ac8b08a610656635845308333312c2298418e5926014c20ce2c3300a61047671997430823ab8ccba18411b5c965d0c208dce432e861047671197430823ab88cba18411b5d662d0c20c5aa9316861064e5398b4308326a9cc5a18418b95162d0c20c5aa8b16861064e5358b4308326a9ac5a18411d9c66590c208eae332c861046e72196430823b388cb218411d5c46590c208ece332a861047571995430823bb8acaa18411d1c56550c208dce432a861047671195430823ab88caa18411b5d76250c20c5aa9b12861064d53d894308236ba8c4a18418b5506250c20c9aa6312861047575d85430831b2a6c2a18418d5536150c20caca7b0a861065553d85430823aba8c2a18418d9506150c20c6aa830a861065653185430832aa98c2a18418e5536050c20cb2a7b02861047975181430823b38cca218411d5c66510c208dce4328861047671194430823ab88ca218411e9c06510c208bce7324a41045d73992520830f2a4c7a10418755263d0820c3ca8b1e841061d5458f420
  | 18 => 0x20c9208bce7326a29045d73993514822f3b6a6a8a4187d935354520c38c9a9aa29045e7614d514830fb20a6a8a418719053545208eeeca88a29053474544514822fb9acba0a41171cd65d0520c98a7316829064c5358b414822fb9acb20a41171cd65905208bce7b2a829045d73d95414822fb9aca20a41171cd65105208bce6328829045d73194414822f3acc620a41171d563105208beeda98829045d76d4c414822fbb0a620a41175d85310520c9ea7310829064c539884148317aa2c420a4193d4d6210520c98a6b10829066562d44414832da9cc020a419614e6010520c76a8b00829065b53580414832c29ac020a419cd456010520ce0a2b00829064c5398b314832629ac598a410f9d0650c52087ae8328629064c53988314832629ac418a419614e600c520cb0a6b00629065853982214832c29ac110a419314e62d0120c98a6b16809052c7550b404838629a85a024195d4e6190120ca8a730c809065753586404832a29ac320241179cf65501208bae7b2a809045f73595404822e39acaa02419314f6250120c98a6312809052c75509404838629a84a024117ddb53101208baeda98809045f7614c404822ebb0a62024193d4e6210120c98a7310809064f53588404832629ac42024195d4e6110120ca8a7308809065753584404832a29ac2202419314e62cc120c98a6b16609054c754cb30482a73ac651824193996328c120caea730c609065453986304832ba9ac3182419514d618c120c98a7b12609064f531893048326298c498241531d5324c120c98ca992609061e64d4c304830eb26a61824187990530c120c3ac8298609064f53988304832629cc41824193d4d620c120c98a6b1060904cd768c830482a73ac641824193996320c120d1ac9190609065753984304832a29cc21824195d4d610c120ca8a6b08609065753986204832a29cc31024195d4d6188120ca8a6b0c409064d6314e20483273b0a710241935d85388120c9ec829c409064d6414e20483a229cc310241d114d6188120c98e4b1ea81064d6398b540832b31cc3aa0419558e61d5020cacc6b0ea81065563587540828f39ea92a041475cf5495020a6ce3aa4a81053571d52540823bb8ac72a0411d1c56395020a5ce5b1ca8105377158e540829a38ac72a041479cc6195020a3ae630ca81052e72186540829d380c32a0414d9c66095020a6ae3304a81051e73182540828eb98c12a0414d9c46095020a6ae2304a81051e73d91540828eb9ec8aa0414d9c76455020a6ae3b22a81045e73d89540822eb9ec4aa041179cc61550208bae630aa81052e72d8d5408296392c6aa0414ddc56355020a68e2b1aa8105387058d5408296392c2aa041479cc6155020a3ae630aa81052e72185540829d380c2aa0414d9c66055020a6ae3302a81051e73181540828eb98c0a
  | 19 => 0x92886110666629443088332b14a2184411ddd9510c220c6cc8a886110635645443088333312a21844199589510c220998e6b2e411054f73597208832631ea7904411bdd953c8220c9cc6a9e4110665659472088332b2aa3904419c59651c8220ce2caa8e411046f7258f544822f39cc3aa241175ce61d5120c9cc6b14a89064c63d89544832bb1ec2aa2419518f6155120c6ec830aa89065763185544832a318c2aa24199d886155120cb0c7b02a89043f76550544829a38aa82a24155dc554d4d20aa8e2aa6a69055671d9353482aab8ec9a9a4187d9264d4d20a9ae4326a69055671d8b53482aab8ec5a9a4117dd95314d208eee2b20a69047471590534822ebb4a829a4117dd95414d20aaee2aa0a6905547155053482a6b96c829a41535ca6414d20aaee2b20a69055471590534830eb20c829a41535c86414d20aace2320a6905557119053482acb80c829a41479d36214d20a3ae9b10a69055671d8853482aab8ec429a4153dd16214d20a9ae5b08a69051e74184534828eba0c229a41535c86114d20ab2e0308a69064d62d805348326b12c029a411b5cb65d0d208dce432e869064f5398b434832629cc5a1a411b1d562d0d20c98a6b16869047671d96434823ab8ecb21a419314e6290d208d8eab14869064c5358a434823b38ccaa1a411d5c66550d208dee4b2a869047771595434823a38acaa1a411edc16550d20a3ce9a9a869065753d85434832a29ec2a1a4195d4c6150d20ca8a630a86904f170185434823b388ca21a411d5c46510d20a3ae8298869064c5398843482363aac421a419314d6210d20cb0a7300869047875580434822f3acc7a1241171d563d09208beeda9e849045d76d4f424822fbb0a7a1241175d853d0920a9ce72a4849046d7614e4248326b18a721241939945390920c9aec29c849070e7414e4248386ba0a7212419314e6090920caea7b0a849065453d85424831baa0c2a12418d1506150920caea630a849065453185424832c29ec0a12419614c6050920a9ce72a2849046e7615142482373aec6a1241c315353509208dced29a849052e7494d42482a739ca6a124193d8c5350920e1ea829a849064e7614d4248326bb0a6a1241c3d905350920cc8cbb0a849074453d854248332328c2a1241d114c6150920e90a7b0284904cd731814248326298c0a1241d214c6050920dc6c2302849064c539884248387a9a84212419614e60cc920c9ee732c649046e75d92324832732ea71924193d90538c920c9ac829c649064e6590e32482a63aa871924193995438c920c98a7304649065b5318132482363aac8992413a1c1644c920a9cebb1a649064c65d8d32482a739ca6992411b9d8534c920a9cec29a649064e7614d3248327b20a69924193590534c92095ae8302649064c53181324832629cc419241531d53
  | 20 => 0xd7414e328822f3b4a699441175db530ca20a3ae8298651046d76d5032882a7b9aa8194411b5db530ca2099aeda9865105ca70d4c32882a6bb6a619441935db530ca20a9ae9a98651074671d4c32883a2b8ea619441d29c3530ca20b1ae829865105ca7014c32882a73ac8619441539d5430ca20e1aa8a18651064f5358032882ab398a928c41555cc5494620a6ce829ca3105357414e51882b2ba86528c41d1d4c3294620c6ac8324a3105567319251882aab98c928c41595c86494620ae4e0324a31056572d8e51882b9380c728c41599cb4394620acae5a1ca3104777650e518823a3b28728c41559cf6294620aaae7b14a31055673d0a51882aab9e8528c411ddd94294620e8a64194a31053674182518829aba0c128c41559cc6094620aaae6304a31045e73191518822eb98c8a8c411d9db54546208ecec2a2a3105567315151882aab98a8a8c411d9db53546208ecec29aa3105367414d518829aba0a6a8c41595d43254620e8ea6192a3105577359151882aa39ac8a8c4159dc96454620c6ac8322a3105567319151882aab98c8a8c41595c86454620ae4e0322a3105377458d518829a3a2c6a8c4159dc96354620acce5a1aa31056572d0d518823bbb286a8c411d1d94354620ae4e021aa3105717010d518829bba2c4a8c414d1d16254620aaee6b12a3105547358951882ab39e84a8c41555cf4254620ae4e1a12a31057170d09518823a3b284a8c415cdc13254620ae0e0992a310745320c9518829b3a4c0a8c414d5d26054620aace7302a31055573981518823bbb2a228c4117dcd65506208b8e6b2a8310534745454188332312a2a0c41179cf65106208bae7b28831053574944418832b31ca220c419558e5110620cccc5288831066562944418832b31aa220c419558d5110620cccc4a888310665625444188338a8cc020c419c9456010620ce2a2b00831066662946318821fba2ca98c410f1d1654c620cc8c4a8a631067251580318833928ac110c419c5476048620a3ae62a681104cc7358a408823abacc3204411ddd561902208eaed28c811047776546408821f3b0a8a0441475cc545022087eecaa0811061e5458c408830eaa2c6204418b9516210220c5aa8b10811047575984408823bbaac2204411d5da5110220cacc72888110655639444088333314a2204419958a51102208eeeca88811065663544408832ab1aa220441999895110220ccac4a88811051d7414f308823abacc3184411ddd5618c2208eaed28c611047776546308822f3b0a698441475d0534c220c98a631261104ce76cc93088333b14a2984419918a514c220ccec4a8a611066462545308830eb24a61844117dd9530c220c3ac8a98611064e535883088326a9ac418441a3590320c2208eaeb308611047775584308823abb4a2184418d992510c220c6ac
  | 21 => 0x2663b4a49806193d96524c030e1aa9292601864c62549300c2663b2a49806193d95524c030e1ca8a92601870d54549300c2a73b2a498061531d9524c030c98eca92601865765945300c38aaa4a298061b118a514c030e8aa528a601865765545300c38aaa2a298061b1189514c030e8aa4a8a601861d54d81300c335b96ca980619a1cb654c030c76cb2a2601863b65551300c2e8b8ec698061c6552534c030cd6cbb12601866b65189300c365b18c4980619ad96524c030cd6caa92601872954549300c3a529aa4980619cd96514c030ce6caa8a601873154545300c3b0a92a2980619398e6295320c9ac7314a9905717018554c8333390c2aa641995c86155320ce4e030aa9906717018554c821fbb2a82a64117dd95314f208eee2b20a7904747159053c823b38ecb21e411d5c76590f20c98a6b1487904767199543c823ab8ccaa1e411ddc56550f208e8e2b2a879051e74d4d43c8274b90c0a1e411d9c46510f208eae2328879054e7395242c8237baac7216419358c5390b2087cec2a285904f17018542c8266b9ecaa1641539cf6550b20b52e1aa2859054e7395142c82373b0a8a16412b9d85450b208dced29a859052e7494d42c8333b28c2a1641785c06150b2099ae6302859043f7655042c8354a12c021641721c1438cb208bcec29a65904e87059132c82e4b86a6996411b9d8534cb2099cec29a659054e7614d32c83273b0a69964193d90534cb20c9ac829a65907497014d32c8256ba0c0996419314c604cb208beeca9865906c93258032c831632284a8e411ddd951147208bce7b2e839045d73d9741c822f39eca20e41175cf651072087ce9b2e639043d74d9731c828eb9ca9a0641475ce54503208bced29a619064e5318930c8326a98c498641175db530c320c3ac9a98619061d6414c30c8327a9ac418641335da320c320d1ac9190619054c7358b548823bb8ac72a4411d1c5639522087eecaa0a91061d5458c548830f322c62a4419398d6215220c9ac6b10a91065663984548832ab1cc22a4419958a6115220cacc6b08a910655635845488332b12c22a4419c5866015220ce2c3306a71047771592538823a38ac929c4117dd95314e20c3ac8a98a71061d6498c5388317322c429c418b5916214e20c6cc9308a710635649845388332b14c229c418d9916114e20c6ac8b08a71066562584538823b38ccba1c411d5c665d0e208ece232e87104757119743883172a2c5a1c418b55162d0e208ece332c871047571996438823b388cb21c411d5c46590e208ece332a871047571995438823bb8acaa1c411d1c56550e208ece232a871047571195438823abaec2a1c411d5d46150e209e2e030a871047671994438823ab8cca21c411d9c46510e208eae2328871061e5458f428830eaa2c7a14411d5d76150a208eaea30a851051
  | 22 => 0x8618b9526210430c5aa9310821846f75588410c3172a2c4208618b55162104308deed290821846d76948410c32731ca4208619358e52104308deeca90821846d76548410c32731aa4208619358d5210430cacc7288821865563944410c333314a2208619958a5110430cacc6a88821865563544410c333312a220861995895110430c72a9300821866a52980410c334a94c0208619c5466010430c74a8b00821863954580410c335292c0208619a5496010430ce4a2b00821867151580410c338a8ac1988618e552600c430cd2a5300621863954580310c334a92c0188619c945600c43087ce932e421843d74997210c21f3a4cb108610f5d26588430c3aa931c421861d5458e210c32731aa5108619358d5288430caac728c421863954982210c334a94c1108618e5516088430cd2a4b04421867251582210c21f3a0ca908610f5d06548430c3aa9b1a421861d5418d210c327b1aa4908619318d5248430caec6a8a421843e74994210c21eba4ca10861175d83294030c3aa931c801845f7558e400c30eaa2c720061331c96390030c9cc6a94801864d6354a400c23abacc3200618d9526190030c6aa930c801866652986400c332a94c3200611ddd56190030c6ca8b0c801863554586400c333292c3200619954961900308eaed28c801847776546400c30eaa4c620061879516310030c3aa8b18801846d75988400c3172a4c4200618b55262100308deeab10801862e54588400c316aa2c4200611b5da5210030c9cc7290801864d63948400c237bb2a4200619398d5210030c9ac6a90801847575984400c31b2a4c2200618d5526110030ccca5308801866552984400c23bbaac2200618d9516110030c6aa8b08801866652584400c332a92c2200611d5da5110030cacc7288801865563944400c333314a2200619958a51100308eeeca88801865663544400c32ab1aa220061999895110030ccac4a88801854d72d53300c30eaa4c598061c355252cc0308beeca96601864e6254b300c3872a2a598061c355152cc030c9eeca96601871554947300c3a2a94a398061c555151cc030e8aa4a8e601845d7694e300c31b2a4c3180618d552618c030ccca530c601866552986300c31b2a2c3180618d551618c030ccca4b0c601866552586300c23cbb4a718061ca551528c030e62a8a8c601876152546300c3172a6c4980618b553624c030c5ca8312601862d54189300c2363b4a4980611b9d9524c030ccec528a601866462945300c333b12a29806199189514c030c9ee5b2a601864c72d95300c22f3b6a898061535cb544c030a3aeb2a2601861f65951300c30fb2aa89806193d97624c030e1aa9b12601861d54189300c327b28c498061c3550624c030c9aea312601864f54189300c3472a0c49806193550624c030d1aa8312601860d54189300c
  | 23 => 0xcc830c9ce4b2c641845d76d52320c2a6b96a91906187596548c830c3acaaa4641864d6594a320c386aa4a519061c3951528c830e1aa8a94641861d54582320c326a92c119061c3951320c830e1aa8990641863954980320c31caa2c0190619a949600c830a9ae5aa0641851d75950320c387392a819061c35c9540c830c3aa9310641854d75988320c386aa4c419061c3552520c830e1ca8a90641870d54548320c2a7bb2a41906193dd9520c830a9ee8a90641854d75908320c386aa48419061535d5420c830e1aa8a1064185c870508320c38caa4c01906187551600c830e32a8b00641862e5498b510c316aa4c5a88618b95162d4430c5aa8b16a21862e6494b510c316b24a5a88618b99152d4430c5ac8a96a21853674d46510c29aba6a328861599cb5194430acae5a8ca21856672d52510c2b2b96a928861599c85494430acae42a4a21853674d4a510c29aba6a528861c99525294430e4aa9294a2187265454a510c392aa2a528861d11cd5294430a6ce8294a2185357414a510c2aabac6528861c55523294430e8aa5194a218715540ca510c3a2a906528861559cc6494430acce4324a21856572192510c2b9380c928861599cb4394430acae5a1ca2184747650e510c2ab39ec5288615c9c36294430aace7a14a21855573d0a510c23bbb285288611d1d94294430e8a64194a21846e72191510c236b90c8a88611d9db5454430acce5aa2a21856572d51510c23b3b0a8a8861599c85454430acae42a2a21847676d49510c29b3a6a4a88614d5d35254430e4ca9292a21872554949510c3932a2a4a8861c95515254430e88e6a92a21847676149510c29b3a0a4a88614d5d05254430aaaeb192a218715548c9510c3a2a9464a8861c55503254430e8aa4192a21855473591510c2ab398c8a8861599c86454430acae4322a21857270191510c2b339686a8861595cb43544308eeeca1aa2185727010d510c2b8b8086a8861551cd6254430aace7a12a21855573d09510c23bbb284a88611d1d94254430e8a64192a218572700c9510c2b8b8064a88614d9d03054430a6ae8182a218566720c1510c2b2b9060a88610f5da541443087eecaa0a21862e54988510c316aa4c4288618b9516214430c5aa8b10a21846d76948510c317324a4288618b59252144308deeca90a21862e64548510c316b22a4288618d9526114430c6aa9308a21866652984510c332a94c2288611ddd95114430c6cc8a88a21863564544510c333312a2288619958951144308dce532e821846d72997410c237394cb208611b5ca65904308dce432a821846d72195410c30eaa6c6a0861875506350430c9ec6a92821864c63549410c32bb1aa2a08611b9cb65104308dae5b28821846e72994410c236b94ca20861875526310430c3ca8b18821861d5458c410c236bacc420
  | 24 => 0xb14a8185347158a540c28f398c32a0614b9c86195030a5ae430ca81853a70186540c29b38cc12a0614d5c66095030a5ce4304a81852d72182540c29b388c12a0614d5c46095030a5ce5b22a81852d72d91540c29b38ec8aa0614d5c764550308dce430aa81846d72185540c28f39ec4aa061471cd6255030a6ee2b12a81853471589540c29c382c4aa061471cd6155030a3ce630aa81852e72185540c296b90c2aa0614e9c06155030a6ce3302a81853571981540c297390c0aa0614b5c86055030a6ce2302a81853571181540c21fbb2a82a0618b5526215030c5aa8b10a81863554984540c31aaa2c22a0618b9926215030c9cc7310a81862e64588540c32731ac42a0618d9926115030cacc7308a81866662984540c332b14c22a0618d9916115030cacc6b08a81866662584540c332b12c22a0619a58a6015030ce2c3300a81862e5498b430c316aa4c5a18618b95162d0c30c5aa8b16861863954582430c31b2a6c2a18618d5536150c30c6ca830a861863554185430c278b80c2a18618e9516010c30c6ca930ea41863554987520c31b2a2c3a90618d55161d4830a5ce9a94a41852d74d4a520c2b338ea529061595c752948308eee2b24a41847471592520c2b338ea929061595c75494830acce22a4a41856571152520c386aa0c729061539ce6494830acee2b24a41856471592520c2373b6872906159dc54394830ac8e2a1ca41856671982520c2b2b8cc1290614b9d06094830a5ae8304a41856671182520c2b2b88c1290611b9db5454830acce3aa2a41856571d51520c2373b0a8a9061599c45454830acae22a2a41870e5418d520c386aa0c6a9061539ce6454830a98e6b22a41856771591520c2b238ac8a90615a1c164548308daeda1aa4185677150d520c2b238a86a90615a9c04354830ad2e021aa41854e73985520c2b5384c2a9061531cd6154830acce3302a41856571981520c2973a0c0a90614b5d06054830acce2302a41856571181520c2973a060a90614b5d0305483087aed2a0a41843f76550520c3172a4c4290618b55262148308deeca90a41862e64548520c316b22a4290618d9526114830c6aa9308a41866552984520c31b2a2c2290618d5516114830ccaa4b08a41847671997420c23ab8ccba10618755263d0830c3ca8b1e841861d5458f420c32731ca5a10619358e52d0830c9cc6a96841864d6354b420c23b38ccb210611d5c665908308eee2b2a841847471595420c23b388caa10611d5c465508308baebb1a841861d54d8d420c30eaa0c6a106193d8d5250830c98c6a92841847575d85420c31b2a6c2a10618d5536150830ccca5b0a841866552d85420c23aba8c2a10618d9506150830c6aa830a841866652185420c332a90c2a10618e5536050830cd2a5b02841847671994420c23ab8cca210619a54960
  | 25 => 0x71590524c316b20c829261535cc6414930acce2320a49856571190524c2b4b80c8292614b9d36314930a5ae9b18a49856671d8c524c2b2b8ec6292611b5db4314930a9aed218a49870e6490c524c386b248629261539c24314930acee2a18a4985647150c524c2b5b8286292615a1c14314930a9eeca18a49870f7450c524c3a3b8a8629261d11c54314930e96e0a18a49854c7050c524c3a43828629261535cf6114930a5ce8308a49852d74184524c2a6b98c2292615a5c06114930c9cc7a96849864e6314b424c326b18a5a12619398c5290930c9ac6294849847671995424c23ab8ccaa12614b9d35250930ccea5b0a849866452d85424c333a90c2a12619914861509309e2e030a849847671194424c23ab88ca212614b5d05210930c9cc6290849864d63148424c334294c02126193dca65cc9308bcebb26649864e65d4b324c327b20a5992619359052cc930c9ccb216649854c7550b324c32732a85992619314a60cc930cd0a5304649866b52181324c26c382c899261539d7624c930a9cec292649864e76149324c327b20a49926193590524c93093ae8302649846e72993514c236b94c9a8a611b9db5254530c5ec9a92a29862c64d49514c2373b0a4a8a618bd905254530c58c8292a29847776544514c29a3a2a228a611bdc965d05308d8e4b2e829864e6314b414c326b18a5a0a611bdc965905308d8e4b2c829846e72d95414c236b96caa0a611bdc965105308d8e4b28829846e72194414c236b90ca20a6187d5163105308dceb310829846c75588414c237bb6a420a611b5db5210530c9cc7a90829864d63d48414c237bb0a420a611b5d85210530c9cc6290829864d63148414c32ab1ea220a619ad4a6010530cd0a5300829863b54580414c335a92c020a619a1496010530ce6a2b00829867051580414c334294c118a619a149608c530c9cc6296429864d6314b214c21f3a0ca10a610f5d06508530c9cc6290429864d63148214c334294c010a619a1496008530a38eaa1e809864e6314b404c326b18a5a0261c350c52d0130ccea530c809866452986404c333a92c320261991496190130a38eaa1a80985987050d404c327b18a4a02619318c5250130e1a86292809846f76d48404c236bb6a4202619398f5210130c9ac7a90809846f76148404c236bb0a4202619398c5210130c9ac6290809866752984404c332294c22026199d496110130cc8a4b08809866752986304c332294c31826199d49618c130cc8a4b0c609864d6214a304c326bb0a51826193d90528c130c9ac8294609874452986304c3a2292c3182619398d62d5030c98e6b16a81866662987540c332b14c3aa0619998961d5030ccac4b0ea81852e72d52540c296b96a92a0614d9c75495030a6ae3aa4a8184777158a540c23a38ac52a061479cf6295030a6ee2
  | 26 => 0x3bbb28728c61555cf6294630ae4e0314a31855673d0a518c2aab9e8528c611ddd942946308e8eca14a318745320ca518c29b3a0c128c614d5d06094630acce4304a31856572182518c237390c8a8c611b5c864546308ecedaa2a31847676151518c2b3390a8a8c61595c854546308eceda92a31847676149518c29b3a0a4a8c614d5d05254630aaaea192a318747520c9518c2abb9ac8a8c6159dc96454630ac8e4b22a31863564191518c2aab98c8a8c61599c86454630acae4322a31857270191518c29bba2c6a8c614d1d16354630acee4b1aa3185647258d518c2b339686a8c61595cb4354630ae4e1a1aa31857170d0d518c23a3b286a8c614ddd16254630a68e8b12a31855773589518c2ab39e84a8c61555cf42546308eeeca12a31847476509518c2b938084a8c615c5c04254630ae6e0992a318570704c9518c3a299064a8c614d9d26054630a6ae9302a31856672981518c2b2b94c0a8c611ddd951146308dee4b2a831846c72595418c29a3a2a2a0c619518d51506308dce5b28831846d72d94418c29aba4a220c619598e5110630caac7288831866662944418c332b14a220c619598d5110630caac6a88831866662544418c332b12a220c619c5466010630ce4a2b00831867151580418c33928ac118c619c547604c630cacc728c431843f74595218c21e3a2ca90c619518d5148630ce4a2b00431852d72153408c266392c7204611d5d661902308eeeab0c811847576946408c23bbb2a3204610f9d85450230a5ae42a2811843f76550408c30f2a2c620461875516310230c5ca8b10811862d54588408c23abacc2204611ddd561102308eaed288811865663944408c32ab1ca2204619998a5110230ccac5288811847776544408c32b31aa2204619558d5110230cccc4a88811866562544408c266392cb9846153dc965cc230c9cc4a96611865565947308c32ab2aa3984619c59651cc230ce2caa8e611846e72987544c236b94c3aa2619358e6295130c9ec6312a89866762d85544c332316c2aa2618dd906155130caec630aa89866762185544c332310c2aa2619a18b605513087eecaa0a89853471550544c2373acc5a1a611b1d562d0d30a9ce52a4869863754185434c31a2a0c2a1a61539ca5450d308bcec2a2869845e75d89434c32a32ec2a1a61951946150d3099ae430286986d361181434c2b3b8aa9a9261591c554d4930e18a8a1ea49856671d93524c2b2b8ec9a92618bd9264d4930a9ae6326a49856671d8f524c2b2b8ec7a92611b5db43d4930acee2a1ea4985647150f524c386a1887a92611bdd952149308eee2b20a49847471590524c2a6b94862926153dc943149308daed2a0a49846f76550524c2b3b8aa829261591c55414930a9ceb218a49870f5450c524c2a6b9ec829261535ce6414930acee2b20a498564
  | 27 => 0x81179ce65884408bae732c422045e73195211022eb98ca9088187d915348440c38c8a9a422062f645492110316322a4908818dd9151484408bce7328422045d739942110386a9ca5a0081c394d52d0040e1aa6a968020715539474010392a94a3a0081c554d51d0040e4aa4a8e802043d76952401032b29cc3200819554e6190040ccca530c802066552986401032b29ac3200819554d6190040ccca4b0c802066552586401023cbb4a920081d254d5290040ea4a6a8c80207515354640103b1292a320081d85495190040c3ecb29a802061f6554d4010317b2ca4a0081c354e5250040c5ecaa92802070e535494010386a9aa4a00818dd965150040e2aa728a802072552945401031bb2aa2a0081c554d5150040e4aa4a8a802065b6594d401032db2aa6a0081c69515350040cd6cb292802066b6554940103952a2a4a0081d254d5250040ce6cb28a80206736554540103a929aa2a0081d454d5150040ec4a4a8a8020761525454010399b22a2a00819398e6295330c9cc6b14a9985717018554cc32b398c2aa661955cc6155330ce4e030aa9986717018554cc21fbb2a82a661539ca5490f308beeab14879843e7615143cc278b80c2a1e61335cb6550f30a9ce5b2a879859970d5143cc2a7394a8a1e61179d85450f3093cec2a287986576518543cc2e8b80c2a1e61335c86050f3087eecaa087986994358043cc30f32287296611bdd95214b308ece3b2c859847571d9642cc23bb8acaa16611d1c56550b309b2e630285985c87050b32cc26c382c899661725c3524cb3099cec292659849d7418132cc364992c0196618719143547308eeeca88a39846e72d9741cc236b96cba0e611b9cb65107308dae5b28839843e74d9721cc21eba6cb90e614b5ca54d0330a5ae52a2819854c7258f548c23bb8ac52a4611d1c5629523087eecaa0a91862d54588548c326b1cc42a4618b9916215230c9ac6b10a91865563984548c333314c22a4619958a6115230caac6b08a91866662584548c332b12c22a4619c5866015230c5ca8b16871862d5458b438c23abaec2a1c611d5d46150e308eee2b24a51847471592528c237bb2a4294618b5915214a308ece332e851847571997428c30f2a2c7a14618755163d0a308ece332c851847571996428c23bb8acaa14611d1c56550a308ece232a851847571195428c23abaec2a14611d5d46150a309e2e030a851847671994428c23ab8cca21461175db540ca30a9ee4aa065184cd76d48328c2e5386a419461635d0520ca30b94e0290651854e75908328c386aa28419461599c85494630acae42a4a3185367414a518c29aba0a528c61555d43294630e8ea4194a31863564192518c2aab98c928c61599c86494630acae4324a31857270192518c2b3396c728c61595cb6394630acce5a1ca31856572d0e518c2
  | 28 => 0x840cd4a4b00842047671997321023ab8ccb990811d9c6658c8408eae332c642047671195321023ab88ca99081531c9534c840a98e6a92642065953d813210334a96c0990811d9c6650c8408eae3328642054d7294c32102a6b9ca41908153dd5320c840a9aea990642064f654c83210326b2a6419081721c1320c840c9ca7316a22064d5398b511032729ac5a88819354d62d4440c9cc7296a22064d6394b511032731aa5a88819358d52d4440aace7a8ca22055573d4651102b3396a328881595cb5194440acce5a9ca22056572d4e51102b3390a728881595c85394440aace7a94a22055573d4a51103a329ca528881d154e5294440e8ca6a94a2207455354a51102ab398a528881555cc5294440aace6324a2205557319251102b3390c928881595c86494440acce5a1ca22056572d0e511023a3b28728881559cf4294440aaae7a14a2204747650a51103a299065288811d9db5354440acce5a9aa22056572d4d511023b3b0a6a8881599c85354440acae429aa22047676d4951102ab39ea4a8881555cf5254440e8ca7292a2207455394951103a329aa4a8881d154d52544408ecec292a2205567314951102aab98a4a88814d1d16354440acce5a1aa22056572d0d51102b938686a88815c5c343544408eeeca1aa2205727010d51102b8b8086a88814d1d16254440aace7a12a22055573d0951102b938684a88815c5c342544408eeeca12a2205727010951102b8b8084a88815cdc13254440ae0e0992a220745320c951102ab39880a8881555cc4054440acce4202a22056572101511022ebb4a62888117dd95314440c9ca7310a22064d53988511032729ac4288819354d62144408daed290a22064e639485110326b1ca4288811bdd95214440c9cc6a90a22064d63548511032b29cc2288819554e6114440ccca5308a22066552984511023bbb2a2288819598d5114440caac6a88a220666625445110332b12a2288819c54560d04408baeb318822045f7558c411022ebb4a62088117dd953104408daeb310822064e539884110326a9cc4208811bdd56210440c9ca6b10822064d535884110236bb4a4208819398e5210440c9ac7290822046f76548411032731aa4208819358d5210440cacc72888220655639444110333314a2208819958a5110440cacc6a888220655635444110333312a220881995895110440e2aa6a08822072552504411032d29cc0208819654e6010440cd4a53008220669529804110338a8cc0208819694d6010440cb2a6b00822066a525804110334a92c0208819c94560104408dce532e622046d729973110237394cb188811b5ca658c4408dce432a622046d72195311030fb22a69888187191534c440c5ec8a92622062c64549311031bb22a2988811b9ca650c4408dae5328622045e73997211022eb9ccb908
  | 29 => 0x90a4a054c7354852502b238aa4292813c5c66090940ccea430a84a0664521854250278b88c0a1281639cf6250940b62e030a84a049d7318142502d8b88c0a12818b99542cc940c3ccaa1c64a049d739913250256b94c8992811ddc5650c9408e8e2b2864a047671194325023ab88ca1928187590530c940a9ae429864a062d6414832502a6b98a419281539d5320c940a98ea99064a058d744c83250278b8cc019281a650d600c940d5284b0064a06c932580325023bbb2a228a81551cd5114540ac8e4a88a2a04ad72993315030e32a8698a811bdc9650c5408d8e4b2862a046e721943150236b90ca18a818d590510c540cb0a6b0062a049d73993215031632a8490a8117dcd65085408b8e6b2842a045e73194215022eb98ca10a818d5905108540cd0a4b0042a05a972d0f40502ccb9e85a02812bdc9639014093ee6b1480a054e72d4e53102a6b96a729881559c75394c40aaae3a9ca62064d6218a53102ab38cc129881555c66094c40a9ce4304a62054d7218253102ab388c129881555c46094c40a9ce5322a62054d7299153102ac382c4a9881935886254c40a38e8b0aa6205567198153102aab8cc0a9881539c86054c40a9ae4302a6205567118153102aab88c0a988117dd95314c40c9aa7310a62064d53588531032aa9cc2298819554d6114c408daeb316862064e5398b4310326a9cc5a18811bdd562d0c40c5ca8b16862064e5358b4310326a9ac5a18819654d60d0c40caca7b0a862065653185431032d29ac0218819594e61d4840caaa730ea42065653587521032aa9ac3a9081539cf5294840a9ae7a94a42056671d4a52102b2b8ea529081599c75394840acae3a9ca4205667114e52102b2b88a7290819358c63948408daeda1ca4205677150e52102b238a8729081599c66094840acae3304a42054e7318252102a6b98c129081599c46094840acae2304a42046e76d4d52102b338ea6a9081595c753548408dcec29aa4205667114d52102b2b88a6a9081539ce6454840a9ae7322a4205687058d5210326b18c6a90811b9db4354840acee2a1aa4205647150d52102b538086a90815a5c04354840a58e8b0aa4205667198152102b2b8cc0a9081539cc6054840a9ae6302a4205667118152102b2b88c0a9081539cc4054840a9ae6202a42045d7694c521022fbb2a6290819394e6214840c9aa7310a42046f76548521032731aa4290819358d5214840caca7308a420655539845210332a94c2290819594d6114840caaa6b08a42066552584521022ebacc7a108117dd563d0840c3ca8b1e842045d7694f421022fbb2a7a10819398e52d0840c9ac7296842064e6354b4210326b1aa5a10819a54960d0840caca7b0a842065553d854210333296c2a10819594c6150840caaa630a842066652185421032ca9cc0210819654d601
  | 30 => 0x159532d023a38aca996812e1c1644cb40972e830265a04777159432d023a38aca19681535ca530cb40a9ae729065a054f754c832d02a6baa6419681635d1320cb40b90e099065a04777654451d0338a8ac020e811b9cb65cc7408dae5b2e63a046e7299731d0236b94cb98e812b5ca64cc740aa8e2a9e63a061c6550d31d022f39ecb90e81175cf65c87408bce732e43a045d7399721d024eb9cc990e81591c552c8740c58caa1243a045f7654c53902a6392a629c819354d6214e40a98e4a9c87204f17198243902a6392a6a1c811d5d76150e408eaea30a87204f1701854390278b88c0a1c811bdd95214a40a98e6a90a52064d6354852902a639aa5214813c5c66090a40a98e6a92852047575d85429023aba8c2a14813c5c06150a409e2e2302852047671997329023ab8ccb99481531c953cca408ece332c65204757199632902a639aa5194811d9c4654ca408eae232a652054c7254d32902a639aa4994811d9c6650ca408eae3328652054c754c83290327b2a641948193595320ca409e2e330065206c93258032902b3b92a728c81591c95394640acce429ca3205657214e51902abb9aa528c81551cd5294640aace6294a3205557314a51902b3396c728c81595cb6394640ae4e1b1ca3205727018e51902b33968728c81595cb43946408eeeca1ca32055673d8a51902aab9ec528c815c9c36294640ae4e0314a32055673d0a51902aab9e8528c811ddd94294640e8a64194a3205567318251902aab98c128c81599c86094640acae4304a32047676d4d51902b3b92a6a8c81591c953546408ecec29aa3205667214d51902b2b90a6a8c811d9db5254640aaee6a92a32055473549519023b3b0a4a8c81559cc5254640aaae6292a3205577359151902aa39ac8a8c8159dc96454640ac8e4b22a3205377458d51902b3b92c6a8c81591c96354640acce5a1aa32056572d0d519023a3b286a8c814ddd16254640aaee6b12a3205547358951902ab39e84a8c81555cf42546408e8eca12a320745320c951902b938064a8c815c5c03254640aace7302a3205557398151902b3394c0a8c81595ca60546408eeeca88a320672515824190338a8ec0a0c819598d5110640caac6a888320666625444190332b12a220c819c5456010640d6282b00832046e72d963190236b96cb18c819c945608c6408dee4b2a632046c72595319031a322a298c819c945600c6408bce7b2c432045d73d96219033928ac110c8117dcd65486408b8e6b2a432063464545219033928ac010c814bdc953d0240a3ee6a96812063565947409031ab2aa3a04819c59651d0240ce2caa8e812045f7654c53502a6392a629a81551c55314d409e2e330486a065753185435032a298c2a1a813c5c46050d40b1ce5b1a86a05b1701854350256b90c0a1a816c5c46050d408deeca
  | 31 => 0xf322c62a0439398e6215021c9ac7310a810e5563984540872d31cc02a0439658e6015021cd4c5300a810e7271980540871d322c02a0439698d6015021cb2c6b00a810e6a62580540873930ac02a0439c9c560150218dce5324a610c3e74181530861eba0c0a984317dd95314c21c3ac8a98a610e5953580530871a38ac829843875926314c21c5ac9310a610e3564984530871d324c0298438e5926014c21ce4e3300a610e3a64580530871cb22c0298439698d6014c21cd4c4b00a610e7261580530873938ac0298431b9c865d0c218f4e032e8610c79701974308636bacc5a18438b55262d0c218f4e032c8610c79701964308636bacc5218431d5d66190c218ece332a8610c7a70195430863cb80caa18431d5d46150c21c6ca830a8610e3554185430872b298c2a18439554c6150c218dce43288610c7671194430863d380ca218431e5c06510c218bce7324a410c5d73992520862f39ecb21043175cf6590821c6aa930c8410c3e74d96320861eba6cb190439554e618c8218eaec29e8210d357414f41086b8b80a7a08431bdd562904218bce7b288210c5d73d94410862f398ca20843175cc6510421c3ca8b188210e1d5458c4108716aa4c4208438e9516010421c72a8b008210d3575990410869abaca8208431ddd95410421a6eecaa08210e3776550410872ab2cc620843c55526310421caacab188210f155458c410863abb0a6208434d5d05310421ae2e02988210e65659884108792aa4c4208431ddd56210421ccacab108210f25545884108762b1ac4208439958a5210421ce2cb3008210f3154980410871aaa2c0208439c5956010421e62a8b008210ed2635804108768b1ac020843b89896010421dc2c4b008210e72755804108738baac0208439cd516010421d64a8b008210e71545804108758aa2c0208438c5516010421ce4a6b008210e70535804108726a9cc5188430f9d0650c42187ae83286210d657510721086f0b8083908431b5da52884219e2e03244210c757694a21086373b6a8908431d5c365484218eaeb3224210c5e73191500862eb98c8a80430f9d0635402187ae831aa010d7170d0550086b8b8082a80435c5c221540218eeec90aa010d7370485500863dbb2a0280438e5915014021cb2c6a80a010d4e72d4e53d022fbb2a629e819394e62d0f40c9aa731687a06a96258343d02c7396c6a1e81639cb5350f40b32e1a9a87a049e7614d43d031bb28c2a1e812b5c86050f40d3286b0087a054e73d4a52d0237bb2a4296819398e52d0b40c9cc6a9685a06996358342d02c739ec4a1681639cf5250b40b52e1a9285a04ae7614942d031bb28c2a1681275cc6050b40d5284b0085a047671d9732d023ab8ecb996818b99152ccb40c5ccaa1665a047671d9632d023ab8ecb1968187991538cb40c3ccaa1c65a04777
  | 32 => 0x395dc56395321ca8e2b1ca990e4e6398a54c8726b1cc52a643479cf64553218bce6302a990c5d7318154c861fbb2a82a643875ce64d4f21c5ac9316a790e366458753c868f3a6a729e43479d36354f2187ce8302a790c3d7418153c862fbb2a629e43999896114f21c9ca73168790e4d5398b43c868eb9ca921e43479d35390f21a3ce9a9a8790c5e7614d43c863d380ca21e431e5c06510f218beeca988790d4e7395242c86a739ca8a16431b9d85450b21a5ce929a8590c6e7614d42c8733b2ec2a16438d9516110b21caca6b086590d5673d5341c8716aa0c4a0e431d5db5410721aace7aa08390e556558c41c869aba4a620e431d5d85310721ccacb3108390ec66358841c8762b1ac420e43395da42107219ceeca108390ee16298041c8738b2ac020e43b498d6010721da2c6b008390ee26258041c8770b12c020e439c5d56010721ce6a8b008390e715458041c873929ac020e439c14d6010721dc484b008390ee14258041c8726a98c498e434d1d16154321c6ec820aa190d657210550c86b8b8082a86431edd9501432187eecaa0a910e4e635885488726b1ac42a4439698e6015221cb2c7300a910e6962980548873938cc02a4439698d6015221cb2c6b00a910e6962580548873930ac02a4439c9c56015221cd2c5306a710e7271983538873930ac1a9c439c9c560d4e21ab4e1a9ca710d5a70d8d538862fbb2a629c439958a6114e218f4e032e8710c7970197438863d384cb21c431e5c26590e21c9ca6b148710c7a70995438863cb84caa1c43471d15350e21caca630a8710c7a70194438863cb80ca21c438d9506150a21c5aa8b108310e4e5358831886b8b80a990c43569cf50942218bce6322a110c5d7319150886b8b8642a84431edd95014221c3ea8b1ca890e4e6358a544861fbb2a82a243475ce6415121c3ac9a9ca690e2d729925348717322c529a438d9916194d218beeca98a690c7771590534868eba4c629a431b5cb65d0d218d8eab168690e2f5458b43487162a2c5a1a431b5cb6590d218eae3b2c8690c7771595434863db82caa1a431e1c16550d218ecebb0a8690e3454d85434872a29ec2a1a431e9c06510d218f2e03288690c6c75588434863a3aac221a4387d5163d0921c38a8b1e8490d4e739524248636bb4a7212434b9d25390921c68a9b0a8490d2e75d9142486973a4a8a1243539ce54509218dcec2a28490d2e7615142487173b0a8a12434b5c054509218dced29a8490d2e7494d424873232ec2a1243c91536150921e48a830a8490e2c5458b414862f39ecaa0a43175cf6550521c98a6b166290c3e74d95314861eba6ca98a43179ce64d41218bae7326a090c3e7498f504861eba4c7a82435c5c321d41218f6eca80a090c5e73181540862eb98c0aa0430fdd95415021c3aa8b18a810e3954580540870
  | 33 => 0x731dc4c4b008398ee16258041cc738baac020e639cd516010731ce2a8b008398ed24358041cc768a1ac020e639c9496010731a68e8b0aa198e376410550cc6aab9882a86635c5c041543318f6eca80a198c3f76550548c726b1cc42a4639358d6215231cb2c7300a918e6a62980548c734b14c02a4639c9c66015231cb2c6b00a918e6a62580548c734b12c02a4639c9856015231ce4e2b00a918e3654185438c6b5386a5294631bdd95214a318f4e132c8518c7970996428c726b1ca5214634b1d15250a31ccca430a8518e1d5458c418c6b8b80a998c635a9cb50942318dce4322a118c6d72191508c6b8b8662a84631edd95014231c5ea8b14a898e4d6398a544c61fbb2a82a2634b5ca6415131c5ea8b168698e2c5458b434c6a7394a921a638d1536150d31a3cebb228698d1e74951434c6a7394a8a1a63179d85450d31a3cec2a28698e1e76151434c68eb80a8a1a63951976150d31e28a9b0a8698f1454185434c716b26a5292631bdd95214931c3ea8b1e8498e1c5458f424c71a2a6c2a12639914b61509318f4e03288498c7970194424c70e2a2c7a0a631b9ca64d41318dae5326a098c3e7498b504c61eba4c5a82635c5c331d41318f6eca80a098c6e72181540c636b90c0aa0630fdd95415031c5aa8b10a818e3954580540c72731cc42a0638b9916215031c9cc6b10a818e6562984540c72d31cc02a0639a98a6015031cd2c5300a818e7271980540c71d322c02a0639698d6015031cd4c4b00a818e6962580540c73930ac02a0639c9c56015031c6aa930c8618c3e74181520c61eba0c0a90631bdd95214831c5ac8a90a418e6952580520c70eaa4c7a10631e9c065508318f2e032a8418e3654185420c71aaa0c2a1063999486150831ccaa430a8418c5f7558e410c70eaa4c6208638b9516210431c5aa8b108218e3a54580410c71caa2c0208634d5d66410431a6aeb2a08218c7776550410c69bbb2a8208638ddd95410431caacb3188218f155498c410c63bbaac620863955956310431e2aa8b188218e556394c410c732b2cc420863c95526210431ccacab108218f2554588410c762b1ac4208639c5966010431e62a93008218e3554580410c738b2ac020863cc5516010431da4c6b008218ed163580410c771312c020863b85896010431ce4eab008218e7175580410c739aa2c020863ac9516010431ce2a8b008218eb154580410c718aa2c0208639c9496010431aaaea20e6218dd170107310c62ebb4a7188633c5c0648c4318eaed29c6218c5e76d51310c63ab86ca988631d5d6644c4318dce4322a018c6d72191500c61f3a0c4a80630f5d06254031ae2e1a0aa018d7170105500c6b8b8462a80631ddd93154031ae6e098aa018c7b76540500c71cb22a0280639a5895014031c9ac7316a990e566358754c868f39ea92a64
  | 34 => 0x4a020c6e7218d5010636b90c6a8083179cc62540418bae6312a020d7170905501063bbb282a80835cdc141540418f4eda9aa020d6a72d4d50106b4b96a6a8083d41c65354041ea0e2a9aa020c7a7614d50106b5390a6a80835a5c853540418f4eda92a020d5a73d4950106acb9ea4a8083d294e5254041e92a7292a020f607194950107a529aa4a8083d254d5254041ec0e2a92a020c7a7614950106ad398a4a8083565cc5254041ea4a730aa020f515398550107b1294c2a8083d854a6154041e32a7a0aa020f2952d0550107a929c82a8083d454e4154041ec4a520aa020f6152905501069dbaa82a8083c654d4154041e52a4a0aa020d737550550107a929a82a8083d454d4154041ec4a4a0aa020f615250550106b938ec6a80834e1d16354041ad6e4b1aa020d687258d50106b838ac6a80834e9d06354041ad4e431aa020d697218d50106b9388c6a80835a9cb4354041ad2e5a1aa020d7271d0d50106b8b8e86a80835cdc54354041e328621aa020d727110d50106b8b8886a80835c9c76254041a70e8b12a020d5b7358950106ac39ac4a80835c1c56254041a74e8312a020d5a7318950106acb98c4a80835c9c46254041ab4e7a12a020d5973d0950106b938e84a80835c5c74254041ae6e2a12a020f294210950106b938884a80835c5c44254041a74e9992a020d3974cc950106b938e64a80835c5c73254041a74e9192a020d39748c950106b938c64a80835c5c63254041ae6e2992a020d70714c950107a499064a8083cc5d26154041ae4e730aa020d727298550106b939c82a80835c9ca4154041ae6eca0aa020f337450550106b839a82a8083ccd0d4154041e6286a0aa020d70725055010799a1282a8083cc5094154041ab4e620aa020d597310550106b539082a80835a5c841540418baed298a020c5f7654c501072729cc4280839354e6214041c9ca6b10a020e4d535885010636bb4a4280839398e5214041c9ac7290a020c6f76548501072731aa4280839358d5214041cb4a7300a020e59539805010735294c0280839a54a60140418f6eca80a020e5a63540501072cb1aa0280839a9895014041cd2c4a80a020e4e6358b54cc733312c3aa6634b9cb5495331c9cc7314a998e4e6358a54cc733b8ac52a663991c56295331a5ce5b22a998c6e7218154cc636b90c0aa6630fdd95415331a9ce52a48798d4e7295143cc62f3b0a8a1e6395d976150f31c6ca8b088798d2e74d4a52cc70f32287296630f9d06054b3187ae8302a598c6f7654852cc72731ca5a16639398d52d0b31a5ae52a48598d6672d5341cc70eaa0c6a0e631d5db5410731acce5aa08398e556598c41cc66abb48620e6335dd94310731d8ac73108398e656558841cc762b1ac420e634d5d25210731da2c73008398e716558041cc76931ac020e63b458d6010
  | 35 => 0x14d52106b4b80a6a9083d194c6154841e8aa630aa420d4e7399152106a6b9cc8a90834b9d26354841acce331aa420d647158d5210726b18c6a90831b9db4354841acee2a1aa420f0d4310d52106b338886a9083595c44354841acae030aa420d4e7310552106a6b9882a9083599c66054841a58e8b02a420d4f7358152106a639ac0a9083591c56054841a5ce8302a420d4e7318152106a6b98c0a9083599c460548418baed298a420c5f7654c521072729cc4290839354e62148418deeca90a420e4e635485210726b1aa4290839694e6014841cb2a7300a420e6952980521072d29ac0290839654d6014841cd2a4b00a420c5d7598f421062fbaac7a1083175da53d08418beeca9e8420e4e6394b4210726b1ca5a10839398d52d0841c9ac6a968420e6552587421072b29ec2a10839554f6150841ccca5b0a8420f0d53508421072aa9cc2210839554d6110841ccca4b088420ea542584421063d384cb990831e5c265cc841c3ac929e6420e2e6454b3210716b22a5990839954a61cc841caca6b0e6420e6552587321063d384cb190831e5c2658c841c3cc8a9c6420e1d6454e3210716b24a5190839554e618c841caaa6b0c6420e6652586321063d380ca990831e5c0654c841a98e4a9a6420d4c73549321072aa9ec2990839954b614c84196ae830a6420c7a70994321063cb84ca19083535ca530c841a9ae72906420d4f754c832106a6baa641908393d95320c841c9aca9906420f0d5354b411061ebb4a9208831d5da5490441e8aa6a948220e1f6594d411070fb2aa6a08838bd965250441c5ecaa928220f0d53549411063ab86caa088395d965350441caecaa9a8220da572d0d411074a31a86a088399d965250441ccecaa928220f455354941106cab9e84a0883a91894250441c9ca7316a020e4d5398b501072729ac5a80839354d62d4041c9cc7296a020e4d6394b501072731aa5a80839358d52d4041ab4e7a84a020d5973d4250106b5396a1280835a5cb50940418dee4b1ca020c6c7258e501062fb9ac528083171cd6294041ad4e5a9ca020d6972d4e50107a838aa7280835a9c85394041ad2e429ca020d5a73d4a50106acb9ea528083d294e5294041e92a7294a020f4a5354a50107a4a9aa528083d81c55294041ab4e6294a020d597314a50107a929cc328083d454e6194041ec4a530ca020f6152986501069dbaa83280835cdd54194041ab4e6324a020d597319250106b5390c9280835a5c86494041ae4e3b1ca020d6b7258e50106b4392c7280834e9d06394041ad4e431ca020d697218e50106b9388c7280835a9cb4394041ad2e5a1ca020d737150e50106b938ec52808356dcd6294041ab0e6b14a020d3a7418a50106ad398c528083565cc6294041ae4e2314a020d5a73d0a50106acb9e85280835cdc54294041e926419
  | 36 => 0x3b26528065721c13294032d8a6530ca0196c532586500ca663b264a8065721c132540328ece2322a01947571191500caa6b9486a8065535ce4254032ab4e1992a01956a708c9500caac38264a80655a1c13254032c9eec992a01954c764c9500cb263b264a806553dd13254032a9ae8992a01974b704c9500caa638264a8065d21c1325403299eec990a01968e644c8500cb46b226428065b14ca6114032d8a64b08a01947b76540500cb1cb22a0280659c5855014032a9ce5a9ca7a0c6e7218153d0636b90c0a9e8317dd95314f41c9ca731687a0e4d5398b43d06a739ea529683179cc6054b418bae6302a5a0c6f7654852d072731ca5a16839398d52d0b418f6e0b2a65a0c787059532d065a38ac819683535ca530cb41a9ae729065a0d4f754c832d06a6baa64196831bdc963943418d8e4b1ca1a0c5f7358a50d062e39ac528683551cd6154341ac8e4b0aa1a0c7b7654050d062fbb2a629c839594c6150e418deeca90a520e665218542906b8b8682a84831edd95014241c9ea6b14a6a0c5f7654c5350637b92c029a831b1c96014d41ca8a7b0a86a0e4d63d4a5250637bb2a42928317dcd60149418b8e6b00a4a0e6452d8542506a7396a699283539cf524c9418f4e032864a0c7970194325072732a641928393195320c9418dce531ea0a0c6d7298f505062f39cc5a8283175ce62d4141ae2e1a0ea0a0c7b7654050506a7396a729883535cb5394c41ab4e1a9ca620d5970d4e5310637b92c1298831b1c96094c41a3ce9b14a620d5671d8a5310726b10c529883559c66094c41a9ee4b04a620d4c72582531068f3a0c129883539c86094c41a9ae4304a620d56711825310637390c0a98831b5c86054c41a9ce5322a620d4d72991531068f3a4c4a9883559c66254c41aa8e2b12a620e4d6218953106aab80c2a9883559c66054c41a38e8b02a620d4f7258153106a6392c0a9883551c56054c41a3ce8302a620d4e7218153106a6b90c0a9883559c46054c418beeca98a620e4d539885310726a9ac4298839654e6014c41cb2a6b00a620c6d7598b431072729cc5a18839354e62d0c418deeab168620e4e5358b4310726a9ac5a18839554d61d0c41caca7b0a8620e5653584431074aa1ac2218839694e60d4841cb2a7306a420e5a53583521072ca9ac1a9083539cf5294841a9ae7a94a420d6a70d4a52106b4b86a52908317dcd60948418b8e6b04a420d6a70d4e52106b4b86a729083d11c55394841ad4e029ca420d697014e52106973a6c729083599c76394841c9ac631ca420c6d76d0e52106b3b8a8729083599c66094841a9ee6b04a420d4c7358252106973a0c129083539cc6094841a9ae6304a420d6671182521062f398c0a9083175cc60548418dceda9aa420d6a70d4d52106b4b86a6a9083d11c553548418dcec29aa420d6a70
  | 37 => 0x1d5c361550328f4e030aa81947970185540cab8b80c2aa065959cc6155032caae630aa81966672185540cb32b90c2aa0659c9c061550328eae030aa81967170185540ca38b80c2aa0651d9c460550328eae2302a81943f76550540cb1aaa2c22a0658e55160150328eae1308a81963664584540cb2b31ac22a0659998961150328eee0b08a81947671980540ca3ab8cc02a0659c9866015032ce2c3300a81967271980540cb38b8cc02a0658e9916015032cb4c6b00a81966a62580540cb3930ac02a0659c5856015032ce4e2b00a81967171580540cb16aa4c521865555c45490c32ab2e02a4861945f7558a430ca67baac52186593dd56290c32998e0b14861945d75982430ca2f3b0a8a1865555c45450c32ab2e02a2861954f75589430cae4382c4a1865b158b6150c32caeca30a86196c562185430ca66b90c0a1865879914394832c3aa931c841956571152420cab4b80a9210651bdd5639083299eeab1c841964f7558e420ca66382c721065535d64390832c9acb21c841970e5490e420cb26b2a87210651b5d660908328dcec2a2841956571151420cab4b80a8a106553dd56350832b90e0b1a841952e7494d420caa6bac86a1065c31514350832d8ac7b0a841966765185420cb62b18c2a1065335cc6050832d1ac8a16641945d7694e320ca36bb4a719065a3591438c8328beeab2264194d870591320ca673b68499065a3d91424c832b8ee2a1264195c471509320ca673b08499065275d0604c8328deeab2264194e870591320ca673b68699065a3d91434c832b8ee2a1a64195c47150d320ca673b086990652b5d0604c832c9aebb2a64194cd74d95320ca67386ca99065939db654c832a9ae1b2a64194ce70d91320caa6bacc89906553dd5644c832b8ee2b2264195c471591320cae5b82c899065721c1644c83299eeab22641964f75591320cb47ba2c899065b1dc5644c832d88e2b2264196cb70591320ca66382c899065b21c1644c832990e0b2264194ce76191320ca673b6a899065339da544c832d1ec92a264194ce76551320ca66bb2a899065a3d91544c832b8ee2aa264195c471551320ca673b0a899065c3550544c832b8ce22a264195c571151320cae5380a899065725c0544c832a9aeb30a64195ca70985320cae4b84c29906553dd5614c832a9aeb30264195c671981320cae2b8cc09906553dd5604c832b1ce8302641958d74181320cae3388c099065715c4604c832c9aea302641968e74181320ca66ba0c099065a35d0604c83291ae830264196c671181320cb62b88c09906533dd932d44328f4e0322a21947970191510cb0e32286a88658b191425443299eec990a21968e644c8510cb46b2264288651ddd95114432c6ac8a88a21974532544510cb64994c028865b24c96014432ce2a2b00a2194cf764cb500ca66
  | 38 => 0x42caec7a8aa0a165463d455050a3b3b0a2a828595d8c5154142ca8c628aa0a165663d445050b2ab1ea2282855c5c35114142cacc6288a0a1655631445050ab8b80a2282851edd95014142ab0e6a80a0a164f7258c5050b26392c6282859598e6114142caac7308a0a1656635845050b2ab1ac2282851d9c66094c428eae3304a621476711815310a3ab88c0a988517dd95314c42caaa6b08a621659535805310b2729cc5a18850f5da54908428daed2a4842163765d854210b1bb28c2a1085635ce5450842b48e2a1a842166765d854210b33b28c2a10851ddd95114442caac6a88a221671515805110a3b388c6a80851d5c463540428f6eca80a021659635405010b38b0aa0280859398d62d5332ccac530ea9994757098754cca3bb82c3aa6651d9c660d53328eae3306a99953671d5254cca3b38cc12a6651d5c66095332a6ce3b22a9994767118154cca3ab88c0aa6650fdd95415332c9cc6b10a9994767198054cca3ab8cc02a6658b9516210f32c3aa931e85996365418542ccb1aaa0c2a16651b9da5450b32a5ced2a2859962e7695142cca96b84a8a166599d976150b32e4ca9b0a85996676518542ccb932a0c2a16651b5d46050b3299ae6302859953674d4651cca3bbb2a228e651d9c764543328eae3b22a19947b7654050ccb26b1cc5aa4659558e61d52328eae130ea91947770587548ca3b38cc1aa4651d5c660d5232a6ce3aa4a91947671982548ca3ab8cc12a4654d9c764552328ece2302a91947571181548ca1fbb2a82a4659358e62152328ece3300a91947571980548cb16aa4c5a1c658d9506150e32c6aa830a871945e76951438ca8f3b4a8a1c65879da5450e32a3ae12a2871965765d85438cb8b2a6c2a1c6595d946150e32e2ca830a871945d75181438ca66b90c0a1c65879516310a32a6ce9a8ca31947776544518cab4b8665284651d9c764542328eae3b22a11955a70cc9508ca3dbb2a0284651e9c261d51328f2e130ea89947671983544ca3ab8cc1aa2651d9c660951328eae3304a89947570d85544ca3ab80c2aa2659cd876055132ce0c3b02a89967371d81544cb3838ec0aa2651d9c460551328eae2302a89965b63181544cb35b10c0aa2659cd846055132ce0c2302a89965973181544cb34b90c0aa2659c9c46055132ce2e2302a89943f76550544ca3b38cc02a2651d5c66015132c5ea8b16869961e6550c434cb0faa2c7a12658b9954210932ad0e0aa6649955870552324cb39a8ac128a651ddd951145328eee2b26a09947471593504cb38b0ea1282651edd95014132c70e0b20a09962d64cc8504cab4b866428265875923214132ab2e1190a09963664984504cb1ab24c2282658d9916114132c6ac8b08a09947671983540ca3ab8cc1aa0659398e62950328ece3304a81947571982540ca78b80c2aa065
  | 39 => 0xa0a1d71701445050e3dbb2a0282875a1c95014143c9ee6b10a0a1e4c735885050f33314c2282879958a6114143cccc4b08a0a1e65625845050e1ebb4a921887175da5490c43c6ecbb0a8621e37651854310ec6b94a8a188795d976150c43caeca30a8621c76719825210e3ab8cc1290871d9c460548438eae2302a421c6f765485210f32a92c2290879a54960148438eeeca88a221e65625445110f38a8ac0288871d9c462540438eae2312a021c7b765405010f34b12a0280879c58550140438ece3304a7a14757198253d0aab388c929e85555c46494f42ab4e0324a7a15597019253d0aab38ec529e85555c76294f42a9ae5b0ca7a151e7418653d0aab38cc129e85555c66094f42a9ee4b04a7a151e7418253d0aa6b90c129e85559c46094f42aaae2304a7a14767118153d0a3ab88c0a9e8555dc56254f42aa8e2b12a7a155b7058953d0aac382c4a9e85471d16154f42a3ce9302a7a15567198153d0aaab8cc0a9e8553dc96054f42a3ce8302a7a154d7218153d0aab388c0a9e85555c46054f428beeca98a7a164d5398b43d0b2729ac5a1e859594f6150f42caca630a87a164e5398843d0a2ebb4a628e8517dd953147428eeeca88a3a165a5398051d0b2ca9cc028e859694d6014742cb2a6b00a3a16715158051d0b2b29cc3286859554e6194342caca6b0ca1a16555358650d0a2ebb4a62868517dd95314342caca7308a1a16555398450d0b2b29ac2286859554d61143428f6eca80a1a16716154050d0aab38ea729c851d9c66094e428eae3304a721476711815390a3ab88c0a9c8517dd95314e42caca630a8721655531854390b0eb2cc7a14858759563d0a42c9acb31e852164d6558f4290aab39ea328c851ddd951146428ece3b1aa12147571d8d5090a3dbb2a0284851d9c660d4d428eae3306a6a145f7654c5350aac382a629a851d9c66014d428eae3300a6a147675d854350a3b3a8c2a1a85639cf5290942ae6e0a9ea2a15707054f5150ae339ec5a8a85719cf42d4542aace7b26a2a155573d935150a9aba6c7a8a85595cb63d4542acce5a1ea2a14777650f5150aab39ec5a8a85555cf62d4542aace7a16a2a155573d0b5150a9aba0c1a8a85559cc60d4542aaae6306a2a1565721835150a3bbb2a228a851d5da53145428eeeca98a2a15737054c5150ab8382a628a85719cf4214542acae5b18a2a15357418c5150ab2b90c628a855c9c06314542ae2e0318a2a156672d0c5150ab33948628a85595ca43145428eeeca18a2a17154310c5150aab39ec428a85555cf6214542ae4e1b10a2a157170d885150aab39e8428a85555cf4214542acae5b00a2a1535741805150aab398c028a85555cc6014542acae4300a2a14767198f5050a3ab8cc7a82851ddc563d41428e8e2b1ea0a157170d875050ab8b80c3a82851d9db51541
  | 40 => 0x2004800000280000050008000001000080360058000000800000200000000000000800600100060040006001000c00000000020002000000000080200030000003000000000020010000002800000080360000002001000000680060010002000800200000060090000001800400000000018004000001a000000000280080058004000800e0068000001800200380000030000000000e002000200080000010008000000200080000008000004801e006000000000000000000000800000000020038000004000000000020008000000800000000040000002000000a0010004003801f1d9c66094b438eae3304a5a1d667119252d0eb2b88c9296875a9c06494b43ad2e0324a5a1d6671d8e52d0eb2b8ec729687535cf6194b43a5ce830ca5a1d667198252d0eb2b8cc12968753dcd6094b43a5ce8304a5a1d4d7318252d0eb3388c129687595c46094b438ece2302a5a1c757118152d0eb3b8ac6a9687591c56354b43ad6e0b1aa5a1d687058d52d0e963a2c2a96874b9d26054b43acce3302a5a1d657198152d0ea7b9ac0a96874b9d06054b43a9ae6302a5a1d667118152d0eb2b88c0a96871bdd95214b438daed290a3a1c6f7654851d0e3bbb2a228e879a94a6014743cd2a5300a3a1e6a5258051d0f34a92c028e879c5456014743ccca530ca1a1e655298650d0f33292c3286879954961943438daed290a1a1c6f7654850d0f33294c2286879954a6114343ccca4b08a1a1e655258450d0e3dbb2a0286879c5855014343c5acb3168721e2d6558b4390f26b2cc5a1c879359562d0e43acce3a94a521c76719825290e3ab8cc1294871d9c46054a438eae2302a521c6f765485290eb3396a328c871ddd951146438ece3b12a121c7571d895090e3dbb2a028487639cb5390d438ece3306a4a1c75719835250e37bb2a4292875a1c152149438ece3300a4a1c75719805250ee3396c7a8a87719cb43d4543ae6e0a96a2a1d707054b5150eb3396c9a8a87595cb64d4543acce5b1ea2a1d6572d8f5150eb339687a8a87595cb43d4543a6ae9b16a2a1d5573d8b5150e9aba0c1a8a87555cc60d4543acce4306a2a1d65721835150e3bbb2a228a87719cb43145438eaed290a2a1c77765485150eb9b82a428a875c1c15214543acce5b18a2a1d6572d8c5150eb9386c628a875c5c36314543acce5a18a2a1d6572d0c5150eaab9ec428a874d5d06214543aaae6310a2a1d72701885150eb8b80c428a87555cf6014543a6ae8300a2a1d55731805150eb3390c028a87595c860145438ece3316a0a1c757198b5050e3bb8ac5a82871d1c562d4143ae2e1b0ea0a1d71701875050e3b3b6a2a828799d8b5154143cc8c5a8aa0a1c76761455050f33b10a2a8287991885154143cccc5a88a0a1e6562d445050eb8b86a228287999885114143ccac4288
  | 41 => 0x6000000800000000000006000801800080000000008000800200100280020000000800000000000000000003800400080000018000004800a00180000000012007800c004800400900140000006007000200000040008000000800400180000018014000000a000001200080060000000000800000200080020006002000200400060000016007000400000020030000000800000a00140018006002000a0038014002800a00280140008000000000a00500000010006000000c0008004000800400080020050006001800000000000000010000000c001000200500000000000002800400080000010000002001600200120010000000800000a000800580040008018003800c0000004000000400d80000000006001800000000020000008000000200200100008002004000400180040010000001000a003000000300080018014002000400c8000001800a001000400000000008002004800000100000018000001800800580000000002001000800000120028006003000a000000a0000012002800a0030002000000c004000000000120018000002800200080000000006003800c001000a000000000100020010000000000000080000000002001000c000801600280020030018000000e000800a003000200380000050008000800a0018004005800000080040018000002001a0010012000000800000000020002000800400100160028004006802c000801000000100020002000000400a0000000000400000060010002004800000000080040014000800000080080000004000001600380000008002000000c00880100008002003000a000000600000020018004000000200500020000002001800a000000000600000008000000001c0008006002000a0000000000000000080060000004001001200000020030000000800000000020008000001000e004000400000000068000000000400380000098000000000400080000028022000000200100000000000000000000080000000000003800200100000000006002800c00580040038000003000000200020000002000000e001002c0000000000800e00200060000000000001e0008000002800000000180008008000800400580080000000000000200380040000004003000000000040088000000001000700000000008001000e006000a000000200400160000002004800c001000000100040010000000001c0008008000000a00080000018008000000600000080048006000000000580000000000001802c00580000000000004001a0000006006000400000060000000001800a003800200a00020008002001800000300280008008001000e009800a001800400000000000000001001a0008000000001200100180048000003000e00200000010000000000a000800400
  | 42 => 0x2003000000180060020006001801400080020000022000000200080000008008000000a001000000000280000000000000200000060000010002800000280020000006000000400080020008002000000000000080008000000002600080060010000000000400000020020000000000a000000400100020008012001800400280020028000000000c00080000008000000000a000000000e00060010002000800200080000000000000000800380060008002001800c0000000002001000b000400100000030000000000a00c800a001002000480060000000000800400200060010010001000c002000000f8026000000600000000008000000000a000000800300080000006000000400080000008008000000800a80000010008001800800000040028004000800e000800a00400060000010001001a0010010001000c002000200000000000008003000000080080030002000800000000040000004000001400080120008000003000600000000048004006800000200000008002000000400800020000000000001200680040008006000800000a00000040000000000000300000008006000000a00180000008006000800000180060020002000000c00000000000002000802000000180020000003000a00200020000016001000800000000018004001801c00400100028000007800000000000000004001800000280000000000001000000080040000006000000000180000050006001000a000001800400200020000004800a0000010000800200100020028000003000600080000030004000000a002000a0038000001800400800000008006000000c0008002001000200000040000000001000200100020000002003800c0008000000800a000800600000000020006000800a0000012005800a00000040058012001000200080000000000003800a00000000008000000000a00000020010000004001200780100050000000000800380020008006003000000580020060000000001200000020000000002800c001800000100060000000002800800100200058004000000000080000000008000801600100000010002000000000b80000018000007800a000800000300040038002005000a00000060000000002000000280020000016003801e0028000001003200980000000006001000e000000a00080280008014001000c000001200380080000018000000800b00020030004001801a0008000000000600180000028002000000a001001a00380020010000002000000180020008000001800a000001200180040000000000000200000040018000005800c0030000000000600000000000002000000200180040000000000000e00080260018006013000e00000000008006000000400000120020000002801200100
  | 43 => 0x2000000a0000002000800000200120060000000800000000020060004000800a003000200000000018000000000e000000c0030004000000600000000018000002000e003000600000080018030000800000480280008008000000000000000000006003800000580000040000001000000380020010000001000000080020008026002800000200000018006005800600000040010012002800200080000020000000800800000000010000000801600080060018002003000200000000000002000000000000000008000001800200000020028002000000000080000000004000000c00100000058014000000a0008006000000c0058000000001a0000000001000a0000004009800c0008000001000000000120010008000000400000020020006003800000000000078006000003c008000200380000000008000000400000000008000000800a000000e0020004001001200100080020000001000600b00060000000000000000000000000004000000e0020000001800c000800200080020000000002800200000020000000000800000000060000012000800000b800400280240008000000000000180280060002000801800080000008002002000400000020010000002801800080000018002001000200180020008004005000000480080000006000800400000000000004000000e005801e0028002006800200000020000008000800600200020070000000000c0000004000000a0008002002001800000000020004000000a00000000008000000801400100020000002000000000100000018038002801400f0012000000e00380000098006000000200100160000000003801600180020000002000000400000040028002001800a0000004006800e000801600980060038006000000600400000000000004800200000000010002007000000000000040004000800000000040000000000800200000020000004001800400100020050002002000000300000000012003000c0068006006000e0008006000000600500000000000000000e000800000200000000008000000000580000000002000800000080020000000001800600100000000008000000000100000038000003800000080000018004003802400000000020006009000600200000030000001000000000000000004000000a001000000000040008008003000e001800800000000008002001802c00500060008004000000000280000040000001001a0000000005800000180160008000000000200100040030018002000000580020058000000000200580140008000002800000080080000002000000000000000070008003800000280020000000002800000180020010000000800a000800200000060018002000000a0000000000001800000000
  | 44 => 0x4b534c0447105569458892dc3120bec00013771c3d9e944380004718000000013b00000001371554563d1bc25ec4e237ed18f2b4400057f00004be477900014371ce0e3d46d4340366c0004eb8000000139500012e00000c72000108d2214130391c5c30bb03640fb4a7432b98e307f4c3548404b11f8156b4ca8b163fbc5b109557b8272c6ba27f4464418800000004d4000000012a80bc000000000000000000000633400000000003c8c00035013911f49470000000008a934400000002c3c7a5119d73b240d61032bc0c500011fd3c18d8b298001825ac250000170e00018470000daa00014c400000000000f6805480005d3000000008042fdc6540c5547f0b389c8400989e1cdc00000000004730f6d1f11a153b881490000c2841155630000000000000046000002bac77500019b234cc3a73f5c0001e5472c5350000000000000011365104b223b90a173c6800012080004cac8c3676822161b8009000e00000020000014001800600180040018000001000800180000028000004000200000060000000003000200500040008000000000a003000000300000000000008000000200100000002000001200180040008004000800000280020000014000802c00080080000008002001600200020000002000000000c800200000080000016002802c00200020008002000001c0000000000000a002800800300060000000003800000000040000004000800400000100010000000000a004000400280000050000005000e00080060008012003000c0018000002800600200040018000001800200000000008000000001a0088000000000000100040000002005001200a000200000040048006000000400300060000002001800600000000000010001800400000140000008001800000180000020000001000800180000008002001000200080040058004000800c00000060058002004800a00180000038000000800800180060000000000801e0038004000800e00100040008000002800400000060008006002000200380080008004000800a00080120028006000000400000000000004002000000100000000000000000c000800200000040008002001000600100040020004009800000000040000002000000400000020000000000000a0040000000002e0010004007000a005000a002800a000000a000800000000000000000000800000580280000000001800601300040008004000800000100000010000001000a00200040000000000000000100020008000000801000080000038002000004a001000000080000008014002800600080080028000000000600000020008000000800e002000000000000168000001000e0000000000800400080040008000000000800080000018000000002000180080008000001800c0000
  | 45 => 0x44351662bb57da40f80001890e5000017ad18ec5b362b100c55191eb00019f8311400043880002ab88de00001860000528199400068354890000f8622586182984952000168f4ea19600000000000000052e51193c2c0000000cc6667c34a0000659453d1590f4925300ac3544fec056143c9494a619ff2fb8c5510cc0000650000000000018c06944ba0c5e1310a0500001cf07e19e200000002a74cd93788da9000197e4e0d730645c1b2402900866ac0004ce0000000022200014a85e9400014dd35f11f90a100000000f29a170dc84f400000000000a5217a93f722e800000017a2465000069f87f43accfbc0000000000000000000000000000000088451acfb621d8000151c5fb0000edc58f12de000159a5f84000031d41b00000002ee036900000000000f2e000000000000002da91fe666c0003634d040000000000000000000001fe800000a40000001421472c88d0000bc10000dcf00000000000000000000000000001e2000009686ad207da7366c0586158078900007d35ae000000000002d78bb257d458c000113b00013c3077529700000005d3800029083eb59e8085049130024b4c71000124d4ba8b3062183575bf431a3734f176a1cfbf1b307b228b86695d804ac0e4069c00012ff0000000322599567f4c441cb8a3b29d809d0000adb00001750d480000000c226420f0754a4b5324e40001cd803c39908ed2cf06d42530f965a8d7922900b442e1d9dd4eecce54a88d5e4804a1c327199758d4b865058df5000177e00000000be800f0000000289c5d55ac40006454a9000000000000e5d0000a9e41600004f4caa1014c7652b8c000180c000000000000004f0000000000012696a2c1e8234c0005b3cc760000000375400043d814b2b64000310018000010a312e8000587d80926c441b1404e6759b01ff5bd0231360cb20653190900012805c5042a008075d4c482cc5c19848124131d056cad700000000000e09265484e2f6d88400000000000000000076a4838e911d7c2b1429da554cb58b900000004e2c000260800000008b231d0b180cc800000001e215357572b81568000000000016da53b8d4500019ac2958f850ba03e449905ec52942f568a8c2706040006a048a1695113d0e0404329988b72fe078a495c81e572800000014031c500004ea80005818e70185d19957a4ecf545185617dc7ae088c94546c000001a996d4bcc06658612bf00000003454ec5678151263800000fa8000000041c00000002878000161c51f32d143f51940001a14000000077a36040003fc8000548088b11a400000008dc00001bd1ad52b32f3cd0500000000ca18ed5d6400000006e7000000000000004f3000054859ee00000000000000000191c39c5a57297d1500c0c5f53c807b10e8c2435d8cba14fe538416546d742380000000
  | 46 => 0x8e82eb981d0000cab4de0000000056b000000000000000514ff800000000000000662c0003de11f1000195b5d08f6108593931c7854305fcea900002e40d9cc43000136a00002ad0140d0f386c0000000ee859dc0005e4000000006920001a004e3086c3f1c00063a800024443ff0000fe548f13200fb8eae456000069bcc4e0f640005e040000000000427c0004d9400030f00001dbc6d1471000027640004f70e0156e9503000145748b80004df93a300000004575868619c00000008fa0000000000047400011f419b4000000005e00001620000000000065100000550000000000000054f80000000000414c532000148b27e503c2a4400018d04086a30000112c0003c98496000000000000000000000000000010980004a540002584dc30000000000000008e40000ca92b84c047555ea46d226b40be5d8483d000000000005ee10e000040b8000000104c00000000000ef300000000fc4000000000000007b83f7c00017f80005fc153135703ce16d186f5c4950d24954910000000532827a000000016f80f500013be5870cbd4ead79a0000000622c000000084a000000007c97800fb0000000116f0a755ac135c600000087e0f3080e000000061300000000d8600001184c84d2031b450924c80005cb1768000000000000000000000000000000008c1000000043a95f700eccd4250cb3f394c20410682d10e1d4d200009f7000000019d8c3964d45772df86162c84a2617c4eb444a9687276c00000000001004ece330c000000000000000000bb8000241400000001c838549ee4e34a2c48c000012a064c46f4758000104b120000062d000063b97f200011200c88000098c52d0001515018d31300006bc43503e263c8bd81b6d412000110a5134000640000035914f1000169e0000d9e0001a7c18b4e4e26002af0b2c0000000000000000058c400000000003360000233400017740005a24000000128e000131b000000069480000000e4845b80ab55cc0002c9d89a08cc0000648000356000064980002a0c00062845415a2c000145d75d000000005ec0006715161000006400000000001124000000000000003c65a4e5b6d2330fa14bf482d76500014c1400400000003d400012494b450a43d8c9d4548c54b635800011d4a701598c2b000158957c525d479534842f066b0af8e4b2d6197b320c2fe3ab503d24d0455440c2dd1f44ccb0229753000000000000000000610000088320908cc0000e552bf84e00668000090453d29f4000000000051e4000000156e4f44784282137163112b51c4d36325459b40e18cda000000052b00000000000000130d00019e4000190a18ad1fa0000fe6000131700000000000000000000000007b342b0000135800044180000000e5b1c2800057903c600002a817b400000017790001a330000000
  | 47 => 0x900000000001a3147e0434088189f498939c2858000000052e0e708e100015bf5df57cb00003c140a800067e40da31c18cf00003650f3c00016205032bd000043e4000562cb5761d4000000120a0000000077c3d500009725e1495858e085f000000009980000d1800000000000000000629c0000f2c000000000000000000000485000000025b1a7468988b02b850b41e040922d0800000015703b7800003a87105c457e82810f24556d5513348fe45e24359000147d15e05003b9d83600018fa226c000312c747673da903fe901506ecf5f100d96a658cf6026341d34a9d5b504189502fed0c22c4c1ee00000002f94000190d61300000000000b150000000280400031a00000000bd5521c1611c44ed413bcac100000000000ba60000d8555fc00067b00003b94000593d8c50678f5913691554b2c0000000b6861842f12dd8f9d5cfc2020000000648585500016fa000181c4d0485c00008f4000038d6398000000146e291d6270000000302c000408497f4a40f1d37ccd1000019e100000000000000000000000003f6000006d00014100c2d26364f8bc455c90ad0f14d0a00000003a5c00040d80000000000000000000014801e48450203552565940000000cca679400049b800000bc5df1afd8d2214c56826980000000855357400000017774728b334e0400038fca290000000000128800019b707cd51654c80003e0040e0000be100000000000000000000035a1990481d07e0000a2b14fc000000000000000001d5c0000000d98410851e0c4547b0000c000000000000055d68a139200a8ce10000bde00000004f5400044e48a35e7000000000000ab096226d91480000000521478f40a12741d840001d9c4133c00b5d0000a4a58fc000512c0002bc9126000030f18654cf312820944a027000012eb0090837037846f3ef400000000003b0c0000000000451907f2d1c000000000000004ce62f00000000000000000000017045685a19000107a00000001f7c000000162a507c00000000005a0164600010f20000e0b65519d70000000000176f2961a2000001cc40bc00005dc0e70db9839309491259d0000298c36368888af28880000000355449c0000211776405154e000000010f54a4000128325c06b924dd0b15ed819c00000005c70000000007a65100000000000000000000004ec000000000000000000000000042b27c00000a2c6110000553651800019100000001750000083f5e5cb4933816dd00000003324d5a39ac9e106c59c82a680000000342151400000000000000000000144a5fe40000000000597569360f8e6040d1a6325f11ed0000e59192552f2b949dd160800000000001210fff000000000017bc0000d7d000000045cc0006135723110cb043d890cd1b8944860dd1c7127d7ee24f0d5304e02fd2b98707000
  | 48 => 0xcce650000eff1f3d5df01251133a8cbb42a219364da0bf43214000641c7af00017494de816c494168516d801d16b8ee0152508f0000e2409c80120784a1528e14a331b95e751c46fa01701ed23283751cf92fd2c70b2d02980000000000049d64b00002b94275a3e19415c30c98eb55c318a902fce8d00000004fd4000672cbf21051a5644fc78d5f04000000000000011a06354000538164939a025d15c839d1d3400021f000014f845d4e50000000140200000000000000364d70f000000000000000000ffc1efc0000000cff38c4e1819e40005e78b89045c00022a0000000000000000004e2000010ec00000000c1000011f1440000000099d2dd400000000004b7d475000000042b80003e8d0c11f9157e6264abd456995041259de56f850c4cb09b852846d501680b3517017e280da1300015cb5c604ad47d80002edd3432398afa00000000000feb4fd00004f6800000011820b3400000008d1000000013e573600007164134a57560c00000000000cf429c4f8c645585800028f040c0000000055000016b000000014ea00000006060f705f9093f0ae80000000e8e20bc96e2d30430197400000008350000b9a00000006434000000000005640cd50780001ff89180000608000000000006fc000042900019d30b213750828b7301bc54c0001418222052963d88c61dc45e546c4a120000c8b5b990e543f0881000000066a832b1ba0ecd00000000000e123ccc0c8431d8dd114517d37ad06d1aa8000000087b000056126b00000000ec25a0c00000000002058254000018e0000000000000000000000000000000026d6690a4338f06c04d2d66600000006048000000069f0000ddc5bfcf7e530c00061181b700000001db4db862ac7030001a3425cca49000000000008e01b2800029fceef3d29a3d23ec000000000000013c444f811a29653164328af020ac0000c485a3188c000614892b59c9066461c4f31b59453342c47759000000b9d06e09700004f800f06764def1248d7156a40000d996ee47150f4149c8e54bd00000000f8d5898000000000063ed6e234f550a00000ae3374000596062000000005b8c00003ec5fa5fa41b50000000000000000002e22ff082d0e6950f1f840000e496b60000520000083103fc3e1451c6b3136c000000144230d0b5c00000000cfc00000000000000ab000018ec3b68000167400000018254bd800000000001a38aa344b8c914264e8c000000000017d13400ef8000167e578c00033a8000000023a0000000000000000011836818f01000194a5b4000000012ce233c0002b7419d00000000000ee137780005b24a1d28f934c4ee413250554e70001a8a0d0c0001a6cccc2f5159559e4eca2cf501f33552654844ff7386800028940000001270000068000105a55bd535263dd1e83af8ee3000019
  | 49 => 0x3a683fe4d980000000000473800003186a212c08020000cfd4c540004db8000000101d00000002d6d83509d890a1e8c4060000000681c5e1643c116000000000000000000000000062922500002fbda7003480000f8c3c3000000049ac80826bda45000000049f07ab00009fc2e2c4dd00003e059691c051f8000000064f00000000000a754a4c49d5c900004fc8000000187254300000a4161413311f2234146069d8f9e3f9c41200000000000e371fdd1d11ef400000000001abcecc3bf44f7138c6ac0c6d5f4218495321240006a1800000000002b2163d00000000001a94000000000015a4000027862c952600000001934d3400000003abc5d000016470d599fc2ba80000000c7c36981ea00007c853e40000000000575400029a56056344cb0027cb9e05016ac0a0400000017961c2c17600006f94cc055565bc5d6000000033400004964000000115e000000018e80000001735265000048992fa38218931e3056700000000000f6c00000004a19607000091500000000000000308147a170412a000067c00004ee5a891ef679826463e0a621c2523d1ea49dc5238b81000043e21640001a554db36415ab5efd7d04a04cb807f123166e8f355dc07f5000000000001c100002f3000000039713963d38000400c0000fe94e30000637000190b00013370000000000000054b000033100001bd48500000c3f35b874602d44a143b0fec0000b850000000000000000017e6531c00065a0000000042c2d9c00000002943df18452d5404a4a3cb9104810e14448fa40000046202800000007be43b800065f459f31f40005c9c00060a91a435cd30e56b54e5130c1d95f2894600011a30001483000000062300003cd800000000000000e1024ec00000000002db40004bbd42b34d924e14b0c870001026253408b00000002f5d98e3b4478709ac000000159b4b9cfed45d800024a00001d110554fcc97a649c8cb0001a5900002832f9956f0485608000102329cc6fb33140003ab0f5800017fc496c000425d39861b470c000119500000001180000000000053b40001e8946400007d40000bc361089d31a6437f00005b90000000000000057b4000000000000011fc000000053f400000000001edc9f100000000001a5d00005ca54c000022b0ce900508ea0a909cf1701784307c00000000003118000466c4410001135166c6ff0000b2958788450001986000162e622177c64b1902694109b000015d00000000000cb737b80001dcc6ed000025300008051b0c000000003300000003a9c700689000033200000000dbf000000014c4e8a540000000000004b4089f0000e380e24e0e28e813462888bb4cfc4020c8ccfa126414d3c88ab93bd8000000045c349011c000000024b8000000175500000352dfc00000000004c
  | 50 => 0x4188c407450a855946c6000105908fc00000002590000fe860d07ce00016ea5258000267d6df0000155000000037c416d000147200013dd30152210c20d0863cd12341b049a29701e70000b0710581015eec5a13c101ec000057b30a967b59c1a5c35e1a9661ad96228fc0001af8000517cb8d32814ab59910102638b84000000049b13ba5d50658303820b62150c61b70e546450f5252b8ec400012c609002a00065a8d150000000000000000000000000000000004010000000008e567d7c2175c7f64c2000062bd3b64d08000035d0ff296909200013e7573cf3430ed6d92d808a226312fb00014ef00000000000000000000000000005d2891c000000060cc00000009961e740005e64a1f5e980004110000004c26a31252b664400005b140000000000000000000000001f756dc4d00c5400007f022c583000007d848a82074be067a0609102690990605d0fbb3140c960000000407971300000000000000000000062c51c1000000000013b50034a8a00000000de110f00008df4f3d6ef000140f000100b3a180003cbc73c200058542140002fa949202891050000000000007400008ff490400058000002400000000145b0000000000000000012c50000000000000000000000000636580d9bf0000000648d56d3e413b7000000044dc33b5b94000000051b0000000000048764a0c302a000005505a7a0000ceb000103200000002af13c51810000568d87e00011040000000016ca4b0000000000084f0000000000000000002871135a6a269c0006a5d04f308d90e31acc0c2e5cc0d26e991b0fdcd480bec00059ac0002bc5559635c4c100000003639574478d16824ccf9500000000558000000165f3a6004123c982d16ac87d160185800001d50000000000000000017910000bb000000005fe800000000000000ab525dc00012049ab4ac4b7a62ecf5d692c4c955e9a8050e40000000000532cdd315180000000000000055c000000033052c20a88368215909c000082052689be623d7dd0000000000017941180000000c0f00006730000000277c2895b9c71234359055f595fa4b74d89000000052f49476968f4f0000000490c0000000bad2d2800005f0caa5ce8f1c000000000019523c0c0002a7000058d8000000000018f8000000000000000002ceda4f000000060f574b502442000000004aad73c27e9811000000038d1955062d4305c1577529446e0425426500000005694000000000000008a42f24000000000016480003c4572d5325744461978d00000006934000000000000017de282d9f000003be00000000000306546c6d330bc0000000bbc000003414380005d18f500cb451301e449c000192f473522300000001f7858f000000000000000000000000000000012543af12d400000000000000000000000000003fd00
  | 51 => 0x8bd4281798604c000000058b0000000000000000000000000000215d19620ccc3e00000000000000405813a3b4800038c919f1538ac40000000000000100007c0000000004fcf140000000000082900000000000a310001a9e0000b1f1d680000000000552cdb06304000000000053580003d04000228130f3738d69366815f565d72822fd3535fcd23957fc6c85864fb5624000061119b81b798e828450d85b78bd0486535500015a800000516724000552590404a03250d715170000a1921e42b82c00fac06400001a68a8400000f6631c00037e153347d565100019755ded06723540003ea4efe000000000000001b74000000000005c800033452b90000b3a000145251640000338bbe249c0000000d1200017ff33b83ac69940000001162293d7470cbcb6c66348410000000325c00000000005c8074c236d242000000030cc5e2411ceed4fa4ff913605440000000000000000013c1632887a1c38000000156100017d441a00003ad953a000177303bc8ee62819ae354051557843e923c0ba4264158e4378e9e1c08267340c4275a54ef409488d90dc427432340004611011000000003609d10000cf669e00000000ea6387400035082fc11f15da57246a8000005427fc0003e48e160000db140ad7e50dec0001c2034d00016902d840004fb000017cc00047784a9084c00027bc0002f298190000913091c2712a4ca6400000000000c1c3b60e2c09b8f776708d38000123a4628000080543631e89b413413db2b29a212d64de4000079e66440000000f7144f0000000000000000001b40000415c00060e8000204400000000004640ae400011cf20640000000000000189d0e6c00000000005d9c00000011d930180004bc80004b28000000000000000002ac801f67bc248089ca130000d871468000000000015c46f700006da0000bce37f45305520c885dac00020e8f30000000026d45d1001537617a000039883f3477d5240000000218c00000000004910834026c0004fa000000000005a580002a3410a4bc47f3000078568dd039000059e1bb80000000000235000000000000000000000139d58548f1000052236d054200012f7000000057e468d0000a7938e814700000003168478479c00000010d666b4d70559ca9716a4000000157c52f8e92000046c50d4000000009361d81e300000001cec000179cb8e43c435e087c1c439ecd9251797162230dd742ed2ba1d14606013120f38cd2790000f13000053b00018b814f09f8114d7d300005db0b681390000d475be000000006f141acd655680a0a00013ca48a000036101091348000306c9e84cece2a6a216d6001924b261c0003b4c000000000000000000000000000000000015ec0000f5c65357d70000f475adc00000012d5000165e000089e2048e1400007fc419400000008c93
  | 52 => 0x53343df000000000000000000000000000049196e900007302e80ffe58280003e28a96518d2480c1c56300016e444c4d8044254f53dacb2c57e0000237496d029c00007c0adf000134a00007e92914000000000000000000000c623afc000000000000000001eb4000000000000001a000018fd0000000000000000009f5093800024bd89c000000060199c1100143c00018dc30c8000000077c369ca211bd800000008f900007405af867d1bcc7ca67189752ad8038068c08900004285e2800000000001b1000065040005c0447f218084600005cb3210000000000000000004444000000122700006464d3d0e0000000050700002bed9575e4d9454e293220000631220835153e80000000000447553f06fceb12d44a4800000ee3828ce24b9043f56f40000a1828c41a400031dc00001e0000000000027680002c78aa600000b70000bbf00016aa32b122f3494dc03164000405c0004aec41d0af46416200c3d04cd54f00001f600014d067ecd6c0000000208d97243400000780ec84df45ef13d8000319c90208d142413540000000d2e00785162ab400021c51a527880000384e666a55581000000000013182dc82952f8866a5a9d78e2e643c81cc8be9499c0003f2106a1e70b5f1e0c0b441d90785d3c0520000000000042300008fd00017fe00000001164000000000057c131c55800003c9c0003cf0dd91fe44ca00000000001a3c47250d100000000000f0c679c00000000f206a8000250195c053860167dcf6a0000abe420c2752ae02d400010a600000005bb0000470d4d80a1058a4404000000000000000000000000039489300000000000000000125c000097e0000000219c00046ad331000000064040003b5d05a000003005097c028080001a780000000e8900000ac21441ca64ad349000088f0f7400051a58fc000129d184d2ec1cb51af00013de5f7c00000000000000000000000022294b420a0000000000039fc189353000000019a300016c600009f2000111502bc1c2526caa508ec00000003040000f931c9c00047a897149c4e2e52c468a095c79949f580f6a498c64f614e25cd121615e531e69a5a1d393118d09299a63aa0b2a15c05ad00016f253ecc930000d22000000000014453e44000000000062fc0001fa80005ff5198000000050c99fa00000000000bc600000000b14c803dc834707c400044580004cb80000000000339977a000000000000006624000000000015f55220000763577400000000002c180000000000000052503659b500d8f81505d6d200000000a3977152080000000000000111f35887483f0c000670c0005d685f4000080f26600004ff400019b85e4000000050056562004000436562108700000b987c903c55ce54e000000000002a9c0000000d66000103311c00003ac0b3526240004209
  | 53 => 0x59f22e894c50f700dd59f04040ed90356700000663c00058e8e774b1c00000000000f58000181c0000000b980000f6661dc00038981de51449b20ee8f2d315c0000001000529cade1c8107c4eb00002838dc84530fdb478441156bcaaa0b8d3ee011c42464945bd025c0000001081000043a0b9400039d0ea420ec00000017f45aeccbb19a173244c92995ee40b20000a8c00014b31909a3a000144e3f59025000000033080003f8d0520000000000161200000001da4e7900018870d6922b000124f0000fd851d80df00006cd3b6c9b30c9066300001fe506597f2e5907d0ec44b7189c00051512180000000000000000019f100011442e28b3600000002fc000014d03096204a2f4b989a916880000001197000160b00000a84c657b761680003e3d6713ff53821720a3d00017562eac9e3211038256791d624f4d18349c03a5bd800063a51100000000599c000306400000013c70001a01504588a2e9d5e500000b12f4c7341ba80002f4400000019fe000003d08011d50000000422908600000003b000000000000000104a5bb40000000a2800001650000000224949c2b18000563546620b92870d6000000001a714840004e400000000000000000000003024e680000000269000062a11e97835b2156400000002d916ab1a0468326ec7e739b48fc594c00000015f3000000000000004d64000000000000000002f697c4583c0000000000000035300000004ab0d6114719690000000134c772000189500000004f916a4036d49e0000f0f000000000000eb1e400001568000635000039bc2a524500004e88d1417a40004bb931166c40001d9049e4944000000000036ed20043acbe3000000001a0f760000000344c000477400026fc000000000013c40000000dc200000000ea000000000000000ec10000000000000059200000000000626110000000004ec88e724040001b143de000060d000000000002bc1e00000650800000016250000b9d2074000000000000017a42ed45fd15fc0000c7846b0000000574cd2961fc0002e493510000f545930dca442c00039d80000d84c99556800067500004038c53454ce831add08815208304570b09294c690286834c2480f2834f99295bcd10c283169a14ada9142f45c54aa911429399f534e5204018521400009550944fb200007b65228000638960233a18ff000000018d4cef0000ada00f91ae63c40001ca0000000146a5908000000000000000000024bdf337800000013643a6d9560afc00039e048966041da0a141d8105c3b50000000000000000a0000000000000004a200000006208bf100000005988000000000000000000001272000000000000000000000000000000007590000d790000000000000002e00000f6d12c0000af55ef80004a44dfe2aa00006098cc034b08972e0032e
  | 54 => 0x187412c8000000000000011a7462d3100474d43058c8321de0059052088e48682ab395cedd00005f800001695d7094103f4000000000000000003d2c67e00008993a70a995735a0e0000a920001764000000031300005f80000000000046f8e1e3f8905d00000002b34b70299d8b63529540000185e04402b2017ca981a8c9eb09a00005e9c0000000073000000062c0753503400000015ef000000000000005ccd5e2000000068b19180000000000000000000000df40005e1d70b304467240800c94fc166566f8000667149f0000000000000000000002684fc430d8fba2aa597c0120000000081a50a88f700005d45c20000000056c61415a6339000008b14c800000005f0c0004ff8f6f57acdea2dd04445ee80000000e3b113c00000000000000000000170d0a34f08000073f000000002ec0000000000000000000000003f80c9200000000000dda2ec40005eb0dc950f8000000000000008f600000002f2c9675e7c0fe031050500007c2155000000014145da400000000001094b56000000000000000001328000000000004ae3e6c00028b59a200000003a9400000015e0000114100000000000d4100000000000c14000117063641dc453400038e50d55a8400006bc00000011a90000000000000000014504f004bd0000000000000000017290001362116d8a553ac00048dc95e0000ae85bac0000000f793254fd95fdc0000000e7a000019300007a11948b0300000a5273588926113ef5e855764d9c61a238cdc516d4b280000eb90000ef5149000004ad24546858b339a400058a125e317400061c400033b4f2b378400021dc6ef4b00000000006700000005a700000000a9f5344ca669855570115296271000000000000000c100000000609c00055b094200000003e8867f23bc6215c9851d3f4090400000004bd49d543a00000d112c3000000000007d9000034e6301a3650b400000009b000b400017780004260000148cc8a00013290a580001238f291a1c000173c00000000005d0c000000000000000005e540000dc0d1f66ec000000065b000054a39581e55d7c00026f4e052b5000027eda0f60411dc00002b62f1d5b2000181f4e3814136f90e635395433749a5159e000768150603e986c74db533c51615dc000171d528177802c000000000004018bed3d9124a000163434e8000000000045089e9034516015594864854000000029a5ac05a04b9516714080000000362688cc1a11f4ee61dd016e43bc000445c00020e03ae1ae01ae5255238270551a65d0f3728cc40710c40004c958c24d70a6b5b0c00000011ba16048e2179922236f4d3b29a895d52b4b9350000c21a3c00011c52b03fd800000005380341577498022b55d400000000004e1c1a800015524ce4cfe000000000000000000d6a20d80000488000163
  | 55 => 0xe548d0000cf9000000000010df45d10ba1ca4000000000000000000cf8000689c18c52400000001924000000061e898f2218edf4af4000000078e0000c65439c0000000acb04dcf4611590b541040001b8400050c512550bce5a0001a4368e18e7182d1ac40fc58422600ca6084c823de922500015d749d4ae7687920926882f44e24d491ce46714ebd2d6616475431fcd8a2c30000334c90631a8c0700001c900010b8000013e08c800069d400000000000001aa00000000000000000000003e1c00000000004138000609000034f00000000fad614c8893da40004dc0e2204a52be6340146000000065914ec2b3900d575819522400005ea000000000002b58d071cf40000000000304c0000000c6008144e10000d2f51dcb1728a85fc657444e1d785c41ef03842360ecb2954b3446fc58e5230000006829328c80001b90848000094861e0c9b00010b61160aab00008e9000000000019595cdc45208384eb0de5660107c5b800000000000bc24d1490e58a4000385c1ad00000000000000000000000000000000000000000016c000000015860000be030b03bd3f5514300010d211b98401a900000df16cc0ca4000358000021b400035102ef00006c9000004443f40000000a4c43f856e0daca0f6124226020516b0a090314dc955f555400000016b9000000011b4000000125a00016fe00000005fd48800000000217472a4bf0ab31cac00000004cf0000000409c000000000000000004a24749000000053d000056c400000003b40000a5e64b4000686d0d3676c000000000000000000ebc00068c8000610c075196817800000005af0698480884367616540dcc0000264657540461e2904a2305f4000000051200011ee0000000000000000000002d8c0004ef15d2328c000000000051d00000001a410330c5f3bc80001128000126c04b023048b3a2187c3f0009c5d480a3508146d00018b70aa8000000133d00016cb000182e272577f00c40002d2ccd70000c8f3fa4e8f3048d5f4a780005018000120d25200006621a08000615c0000d6d5d401c4b0d547d66d5650cfb639010865b031c2b60d195c557d22e0c7f24a6c25e2604c9a188800064f052f047828f351822d29e19a90d248b9054015c42c13f617fc1d238642c14515a8f00004a3000155e0b7c5262bd8000000000000008b32bb84c61854d6b1ce881c0094e51013d8cb0000000000066f39a800000004ed0ee0000000000008e047300015e81560000000000000000003b253a10d2c0000698000000000000009f4219443650f4000000000019ed16d418d93900000000f34000000000000019bc3f454d542cc0000000c01092c48669891a6000013c4200000000000000018f400015e6110066c3ce0000155c24204084c800000003ca887f664c1cd212c00044a4000000000
  | 56 => 0xe800002183a843bf5db9a7b0b7000024c000039d495c000059a000000000006df51f0115000000030b956a00000003c14bf332c8000176821d4814e2b16a0bb3000000048a580b00008f300000000001a4400000001db0000525cbd63beda1c2628000000119d0001a7f00000002b88000000000000000000000000000000000005bf66cc000544000000292d72dbd7076990b9f030c96464c580764440004549984000000052c8000000175e000050b0e282e015d8000000136004d4000677cacc25e15065ad081300000002100d9663ac9e436513a6091522443b400000000005ec53730f5d0da2d400000000000294109000001ef0b6c00000015c4000000000002c658c8000082164d1bf5a2f49bca825ab97b4044da675f6491905e987361a555d57f400000000004b841d4000000000012c835f8e93000016600012da1b9540c11e461b326000049e800056f15c217800004df00000ddc246000000063399870000000643075b2ed80005eb80001298b5a21c84191d4800000007bb000109153c91936a14000000000000000004ab4000697d91300017aa41c50db00001c300000002d340000001519268d8d837fd60900000005928000316cc083e7c7942bf46a935c8a7b000191a00012cd0000a0600000910000e6e691895b18e0000000000000005d83a7cc2d2a3800000000005fc56f7000000000000000edc0003db899a21c0000000076e0000000430c00002551881dc0003323808757054cc14a953d0bc95a2159097d00000005ae97cf0000cba0000000000168d59bc00000001c6209cac9000000022d5a582050214000000056485aa000000000000000001a390278d2a4a800004fa84bb18955a700019d004f53e50000d97000111a4c5000000000001734c290000bb93f4c000410c0000001870000062e32a14050000000000186a132c0002da4e6310c80000000000053c71800000004120000417818500000003a542c92ce1203302400000005d200002de0000000019489544200000ef0000000174100000000ba40002ded6ca0b58000008c00008f400000003aa000185f000000012bc000363cebd160c0083c6ce99000000000000000000000119800000000000000e286669545000000000005141f1d5b00001179000000049ccb9c000000000000004d34c6354b830062910a9587471c2bfcf3b000135d00000001bd065c5719a0300000001a1800006e8000620c00037f077f0cc43ad3558fb7000085a6a7419100010d70590000000000000000000000000502d7e20000000510c00000000000000fb0000068b00009694c7d68600000000000f21000000066304932a890294d78000000000052a400067540002df00005b040000000000000000064fc000000000050b80002cb80000000000634d6ce367ce304668cb936
  | 57 => 0x8e4c862b3c000000000000000001dd800000000004c1800000003b0654cf8900018ad42587e360a00000000e00257d65b00004a058e40005a5c1710a4400044850cc29b8f8815f84186054e815c698231fc564e662956643cc5511ee463c01a511b3bc18ef5378e4043e00000001a7100002d307d4f821facd761e9c000000012e00000000000000594940a000123e4014590000000000001db0000000000000000000000ccc00015a46642298000452d09a696c0001d8000033588e437983c442fc0004f41a77000000000017940000000000063300000000fc86c2247cf53103d51e08c17f81f0c1d02d140000fec00000012200000cc7000000039600003d3155c34ad2d20000000000000000018c90ad54280000000000075000019d20000d4b000000000000000000b320000000000130b00000000000314000134e3e8400050210dd000158a3f3d91e389537b1670000640d99409fc0f336646d9000172a087974d1ed400000000001184bbb00000002d05118000000059a0000000191259d48c837dced6262c0000001a604224d7a000000000000000000000380c00057f96c200017310000596000000000000000000ba933c0ddd00000000000af8000185c33cc00060393b065992774d58000000175b000180000009543145a9a03b00002c8c27c1f040862a3c06b3231a9f2798c4d69b8c58583092460a541d68597e31c34f0938704b860153a70e98c2103549c50000e72265c00000000005fd800025e40001938d6f3f28000319802c1ed000000008c5637d30a000161b518800000000000000000516800000000004e001680660000000127800004b30000000000025f0cc03a956ed59159b8b9549607560000000438c00000008d20000c24000000000012bc00000003908b660000ba507dc00027cc000000000004b198051540005700e7309cc0000001154044800000017c7368cb77085ce6c0000e2325997ea27b00004cd919267ccb2b00000003ba585b36accb3000015e0000f420000a8154ed73e3e80fc95f14000544c00000000b6000179b20b0000000013652e8ea017d86125474aef648800000002a71c940004f18d7406903390000e430000000034d16905bce803a881f900000000000aba5110000339c10c00000002f300005640bd90001a1400dc4e629b07a60000a006925433419126142784fc22a86e954d0573623933a1e6044900000002994000000000008541a557ec0003b18ce33b64103576c2d0526152b35dc18455f4aa05664c81542c000000156902841115d000001f1400000000004d1c0000bb527e612c2623f51832248473500005ce000092303510f765dc0006299542000000000017510000d4f2c2800065e000058ac000390406e3ce400050e041033d5050000000000007ba0cf0c0a1d0400020547
  | 58 => 0x1e8000059113a4296d2320000e7d000020c15784e4002c8bc1e6800008347ec5cbc06237c89a428410c50000335000000048b139b52a9a1f41bc0002474e0400016375da86e63bdc0000e3066600000000000000000000061ec68848354e600014130e6000000010ab2b000001c7ccf747c000000000003bb000000000000000000324000036c800011a149d2b4000006d901834b54474a2ce2f1f716fc0e451633a1597a0000000000000000014730000000000083e00003c0000000000000000b0000000014e82abc000000000041cd7c94638fb400012063e3000043259cd0cb000029c492a1cbd1d05cb8000000134600012360000f44000000000000000000c1500004de56112d300004cd23e007b22e02601d4460c000000000010fb00000006a11655041553c4501a093ac8f8300002f60000000033c61c21a400062a800000000000000e870000f4019590ce00000000000000487ce52000000030c4000000000000000000000000000195a44d031d279ce293674c9f317093e2f714fc5301983242d26a19843e709bd33253dd3cd26f001b171c9aa3f694b0371d23446dd5932b4c36037a0000628c000475c00000007fd1ffc00000001570000d1601f9a9b567000000005bc21cc000245c0000000e900000000000000000011e20c6460f613c40b4b100000000f9904503b95338da500005741a313e13bf000022d172b3834abb53c15712f14dd10fe4609393cb880bfd66146a94f600005a7000000e3cb18f93d3400021e0b1b2701a0406cc00000000003fec000000000032500000cdc00000000004a9824942dc87455413ff38d8b901ccda6b51bc07d40247214f2c9ca0b6000007d0000026000000000c000000000e4d879000157b4c140003adc2f90c38bd2000000046c80000000000000000002f489a0000b0e000000001d849500000000000000000000000008520000baf21a02f051240000000000359c0005c0000056a98025914057000000048fd96e10d4000086800021980000000bdd32f044c65600000000e2706d034f5f3400011ec0001690a0d00000000f60d5200000005af4bf65a747f80da84370f0800033f0000054d6e80000000371167300009382c4439f1a84082271c0000108f31129105f30080000000f3a327859802b40000e5000000006ce00014343f2c768000048f0000000000000000000000fd0715337c0002a14b78000000000013c8600d8b500001193a100000000000246c0000000b52000116400000000db16a61c980000000000523c0004d5c0ba485d41a305c1bc3ecc439659d39711c8887000030d0001a8e00000004e800000000000000091600000000000baa0000000025800000000003be40004c680005a65a40000000000000000000d0c513cf1e31a400027d8000000000000000001
  | 59 => 0x6258000048c0001decd21187527f00015b61e58000157d93200000000000dd41f5800000018654a08b6b1015213000099100000006248d1d2528151657d1ff58055c84cd000069c9a30000000000000000000000000011b000000000002c209f8afc000000000009d61411539630c000000000000000001e4c000000179d000000034dc000216d0510000b3100017ec0000ddb60346fe0840e0c0001891653c0003a745eb000000000000003550fa806b02d94b2562306c176200012db37a50c064cc0000000c421699617000199e3645024367033600006972748beb0628dac000184166f48ad153c00012203050001302063c93a6a6021215f07cb06a4000000000000007170000000515800001f17e70000317328400000000004b8cd7f370400000010cf000035000002c3231c0000000d012d88f5121ac94f5f6c0003f492a51e6c1eb0000000243c000117c9a52a5000000013744d4107b0000000537d46829f00000000000000000000014b8421000046ec2a96524a070000db6000000036f00003010000000093521b81c700000000000e4a252d88d2e0800044ccf101af514e0e380000001a0b000000045445c953fc00058cc00014cd1220000000000128429dd8e14c8c00c5abd0194b60f8e072c000165c00065cc6ec4d609ae19d0000000000034a10a500017bd27f800032f8628000000000592cf5fb40000000000000010414e517e60f01e600004ea139c000020d8f023b00000000eaa00017093d54c73503800000000000cd092c329d28a31bc00000000005660000000181600000000000000692800060296c406f800001c0e963c94ca20738faf68ac1880000f84397816a0000000035800000016b306ac0002614a360d747cd000010d0000a14038ceba329448c42bcc414c0d4a236845cc0accd9500017d85b84b79479962d0000f65000000000004fd5f192ae0000d314f7c3760000000437118925a80e901003fd2270d7c00002a3000000015a87a80000b405c64722200d3a9377c00038b414300000005bc40000000000000000052f00322c051e456dc7043d140000000000000000000003950000206000000027a8000052952d00010b23fb968a0a6c55b02e40002b1cc3a2b480001a580000a8499b000193b29bc5d310356b24ad0bac206d948300c56d47e4e0f000000000004be000118145e03d16894000000114a44796d14dac0006050000000000059a800000009a0023c0006828f8b2730dcc0000c6c6684a5d2cbc02e583517c3e9d6d30714fa517183a000005af0a997ce000000040b4f154d68b711a94b3e5714203000002259040004720b105a6121e3498d750000dec28c139e00003a457440005fac7ed1ec00000000d0212fd12d2ee9a9c313d62f4a8c4bc000000060bc07249d828062b90cb05600006860
  | 60 => 0x996b0d040001294000000125516445751c6400000016ad3b402b457653995a480004288a9510890752c995b348b4b8f1ac90370c044ab1f680003b5400067d0000000105b000081718c81e92be40006a080001e18000000000000006d813651da00007e61a10000000000010844df0000000000000024980003f840000000000000151800000000000b392ba59ea16dcb465f20000000093603e5056000000000002c70df8000000000000013f800000004750000000117f32b530c46140000958237125da8300010be3d6cf565bed80867584543c580000000fc625d8fc249b4000009963b0000de3633148163684e5346933e0f941d71fec01531585f2356c26c31e400064e80000001a4c5b8176647a400022b8ef145582ae00000000000bbd00000000000000000117500002ca00006480008e1f65380000fbc000000000000004ff0000000000000000000004bb549900000000000000404800000000000000da857d800068a46472d0c6933c3406c144418d025000066a00000000000201cd0e346cdcb000000000014b61168000000000000002eb4db0491000172200018ba0000320406c0003c094c62fd54b52468c645ce46b445c80000000017242067700013ad0000d8c0e7800069b03963844b020000f67000000039f800035640002e30b0855e4bfe00003f560c40000000000000039968080000b491b4525005d0000b4f0000d1168fcc3762a15043cf535b1eb19e31bc0d7b00000e21e5c19700000004d50000000049408f00000000000000000028d400030e000008913fc1f940001a9ca4d0e140006845630348c00029e8d170b55a12115c00000000001ab80e846cd21d6a4d67d50897fb2ab171f000000045ec0002ac560e4f89007000074e29f885e000000053680003884c7e618800000006752824f32589074b441c000618170322a53e63dfc00000000005ec030c0000000000000041e4000397d9790e3c27d355c5e3000000000000000000000067c83926a132f0000000497d80426e400018f490d0001335000021b0001528000055900003a200000000000b94000183850ed4dd0000000669d2c14c9cdaf039898856d13b3439071a1f186702d38000256927b39108be27400004ba41870000000000000000000003e5c6cf1d2800063f8000000000003700002098000000103a14180002489040000000000000000f401e442a8000000192000000000000b2500002b7065970a31840001b0505459d8144000000010251fb00000004a307aa3cf8dd61594235347033a131c9920000000261994300000001d71681255ce061814bfd501cebb6674000096c0000000c260688a5436b4da4018154a61280000c4c6f8000000013442f73ead9b941c800046886b65c84d820000df41bc800054704e8000000002200004a7c000
  | 61 => 0x69980002b08df0202d7a3508d59637e8be800004e95384000000000000000000b3c6b133c80e000000002df54b75f300000240000000115b27b400060300003eb8c1d3e50b3765851db2ea11772245074000078b000000000010b92bdc00051e00000000ccf187da991c8c0000000000000000061b14f3000150760897585ad41fa279494e46310f031d4000421d0f50000000000000064c00000000000000000000000000000f73000012f0000e490000ad5111400068ec000647c0001bac0005db400066600000ce0e130c7c63f0000000229c0003f04000000193d00008c00000000554d68800018510000167197983f000000000016501c147825ce00000000000000000000000003ee400040880000000000551d4a6000000049312f024c523500000aa009cb654d8400002a40003061488486c0001df40000000f5e6738c784c9000000000000000000422c0004958aa40000000000056200000002a2c41e4f5c00060691575aa096554d80000000000227400000000000000d1e46799a05fbc00002343a129100001cc48da0000000000022515bc4c200016595eac65300000000000cb65444000590d4842d2053500000002e6c0001119a352b0d3ed53e00006614cf10000000166400047b0ac53544000118c24455889b767a0000000000000010930000000203000000016c047cc86f03e80000000825208853a0000faa54dc0000000de5625c0000c853d600002e151b04b60de80f768b83b266594464c24910060c0003a08dd84a90e4d00000000000000000142600000000000cf84da40000000000423000013e182000000000000c9d00000003ec400000015cc5ecc0000000b196608a1b32d4fce61747244250388671c00023f978f0aecf9c404cb0b4e7c74f540835f0000a9b50948ce0000000000000000000001235030000000045b090700000e461988620000000141c00044bc03f0000000000077e4f4800058f800004b501c40e0b124870d0900000f42f907ee00011d30000000000019b000000000000002a240112c14d55584476b00003e6000197100013ce000000000000002e8c00000012665d204f23334bcd09851d20268f7d0e2c00000000000000ded2db95880b5c27b211c40a06e578c1c759ed27394fe258d81710b49d80f24125517526847090c8093140412e45505b5005812d162c37192a9029000000000005b3400064e1a080000d321ddc00038d4000162400068419cc674480600005f011a982b69e40004c1c17365007d00000dae36dc00057c80006378e61000024f00003164ed0000000000000000005c5c82a3d2591d0a48e45652c7e266d99475c092cc03f03804e14fbe36e89d75424d883f788544ac89293ee00000000f0a00000000d2000000000003c4929c5be4000084568261f40000000bc8142
  | 62 => 0x14ff100015ee19e0000542000008a484221609de0000448598cefa00000005c6c00000000000000000000000000009605880f5a00000005a4400000012a10b119343058f7b1e7d9991aac0003c3814c5b5ceeb1a8189b3c7c3275e0803934d54613148ab76004d3f1a9913800015d044aca3400017af403c0002a1800000015565e811655415a684ee0000000000000000000000000000000000015ea5db13c9571d15f0001a1a0401191058000000013bf0000c7b129d4d708d8968042c000013400056e00000000b1a39180004fc4ca93d2000008f874246b41fb0000de0524c00035b400000019163f140004dfd582000000000019ca000165c0000ff004c46e35a94fdd5afc000028000050b0462043890961381a100011e000004f5000193719548ab45c496f0001285000154c29a09832fe50c4692059353713d40000dd008b973d3ae043c04987914b6524700011b63f3400000019f60c2800063d490c00005080dbd65761914e40000e3e0000da2256538660b17dc4aa15850a295874dbcca42708ec70000eab56b8000000044200002b000000000000f9817712124a48000278114906e07cc043d58c5e2d8be093460a00000000a7c7622718000208401c5b6000021a8e7c10bd3b100003ab000000041852080000f74202442e3a5000063942f80000000000000065d800066200000000000000103b270c000000000009dc00013ec16b28dd30460ec00000000000000000000192a119469d000000069b4db30c414bb38800004abc875000000000000000000000176400018bc9446464e8b55e154468b40005c40000000000016e8536146000000000005c780003fcc0002bcc000519c0000eec3f05e1800037d800001380006579951691c84d15e86893dd4c1e576000012293eb5a8000047600005ec923b52bc70645a800009603b3336c0000001a892bb0000000153548319dc0000000417000000000002670000000000043a464a01dc3fc192c00059fd11c05c0be708bca7222f581b53084c55aa40001898de765c12fe333800008a000066bc00018500001d995de41dca6d44c0a185b1d13a694c00000003a50000000000168467ac81808658940000000353566923d544c11d85190000eea4a500006694e0751000003d5c00000014291f6ccec0e0c5b2549cfcc5b5484c00006bb1ac00005a30fea00006cb0000000000000000012b745e83da00007435bc000000000005e2000018b000017084c0632000000001071c043c70000000000000000011a80d1400009e4000406800000000006978000235da7d32fd69b618c71b3d0d5b92890000000102c38090700000eee16ec0100a640001e9169f636c810509d2400a6160432c491e5ed554d358cf3f0fe015a5dd19922c5045e4e3d29a3f708640200b5400008d6000177236d400
  | 63 => 0x22d8974000150e2ad03d328800000000abf01fc00012613a500000cb0000000000060e00000001f5c69120f000055600004a347d54f088eb5f54640000000000000000000bc028e4df94ef51b813e8000264c0000000000083cb1d0a788a5615192e13f850d29180004f6400000000f8199c66050e99c400840002b70c470000a8703b4bfa4c98000560181e5868956000000000003744de41c00ba919c536459400007ef4fe80005674318197cbff0000000000000000000000000000000060236800000000b244b88000000039700011b9000036d68300005c940002308000000099e54a91f707582973c60cf400014e917e4f9a43e82883fd40003370552534c0000000000266568e00000005d
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x74250110d2075dc94250110b8283dc942501109a28794942501109a0875494250110aa0865494250110d20755494250110b80835494250110991839d132501109a1829d13250110930855d13250110870855d83250110ac0864c83250110b81844c83250110991841c132cc110aa18299140cc1109c1821c1434c110a448550c624c110ac08050c624c110991841c1324c110cc27318b504c110b108550d404c110cc073189404c110e8143189404c110c467518a304c110aa1841c1620c110c91645c0320c110c91645ce400c1109c0825ce400c110cc17358a400c110c46651c9300c110c85641c9300c110ca1641c9300c110ac182d91300c110a9186991300c110c9376591300c110e8164dc9300c110c91641c9300c110e81641c9300c110cc1861c9300c110cc2651c9300c110d42651c9300c110cc3641c9300c110d82641c9300c110cc1641c9300c110d81641c9300c110c81641c9300c1109c087989300c110e8164989300c1109c087589300c110e8264589300c110e8164589300c110ac287589300c110ac087589300c110cc087589300c1109a1841c132c8110cc0631c132c8110a918399140c8110c9174d8c30c8110cc3635c830c81109c1878c830c8110d81748c830c8110a4685d8c3288110cc3635c03288110a918418d3088110cc0631c930881109c287cc93088110cc1725c06348110c447518d42481109c1831c14248110cc0631c142481109a1841c13248110cc0631c13248110cc0639cb5048110cc0631c94048110b20855094048110e80635094048110ac2868ca3048110cc2768ca3048110cc0631c93048110ac0864c93048110cc0764c93048110c467518e2048110a91841c16308110cc0721c16308110ca1645c03208110cc1635c03208110ca1645ca40081109c0835ca4008110cc1635ca4008110ac186ccb3008110cc176ccb3008110e8164ccb30081108b1875903008110c917458c3008110ca1645c83008110cc1635c83008110ac1860c83008110cc1760c83008110d81740c83008110e81640c83008110c46651cd2008110c85641cd20081108c48758d2008110c91641cd20081108d08758d2008110ac183d912008110aa1869912008110ca3765912008110e8164dcd2008110ca1649cd20081109c2839cd2008110ca1641cd2008110e81641cd2008110cc1861cd2008110cc2651cd2008110d42651cd2008110cc3641cd2008110d82641cd2008110cc1641cd2008110d81641cd2008110c81641cd2008110aa184d8d2008110cc073d8d20081109c08798d2008110ac18698d2008110e816498d20081108e08758d20081109c08758d2008110e826458d2008110e816458d2008110cc38758d2008110ac28758d2008110ac08758d2008110cc08758d20081108c08758d2008110a31849456010410
  | 1 => 0xc477518d4248310c85641cd20083108c48758d2008310c49651c1320ca10989841c1320ca10c89641c9300c210c89641cd20082108c88758d2008210989841c1320c910a48854c9600c910d05735c85450510d11735c05450510d21725c05450510a2682d9054cc510c1475191434c510a1683d9054c8510c247519142485109a1829d33150110c30655d03150110991839d32150110c30655d02150110c89641c9300c110c89641cd20081108c88758d2008110d0473dc95415110d07731c95415110d04731c95415110914875526315110b04825526315110914875516315110b04825516315110924875526215110b04835526215110924875516215110b04835516215110e055458d6215110a33865516015110b10835516015110b20825516015110e115458d6015110e21545896015110c91735c06454d10a2682d945490d10c14651d15350d10c44651c95350d10c44659cb4350d10c50655c34350d10a24825945410d10e105414d6010d10a308550d6010d10a508550d6010d10ca1725c06454910a1683d945490910c24651d15250910c44651cd5250910c44659cf4250910c60655c34250910a14835945410910e20541496010910a30855096010910a60855096010910c247599142cc910aa18099142cc910c1475991438c910a9180991438c910ca174cc8604c910c91748c8604c910a1484594530c9109c0805ca430c910a2484594520c9109c0805ce420c910991841c1320c9109a1841c1320c910944855d1320c9109c0805d1320c910946851c1320c910985841c1320c910b81841c1320c910cc1861c1320c9109c2851c1320c910d42851c1320c910d82841c1320c9109c1841c1320c910d81841c1320c910981841c1320c9109c0874ca600c9109c0874c9600c910ac18214d600c910ac18290d600c910ac183149600c910ac183909600c910cc3874c9600c910ac0874c9600c910cc0874c9600c910ac2854c9600c910ac0854c9600c910ac3844c9600c910ac1844c9600c910ac282d8e63d4110ac283d8a62d4110ac3864c832d4110b10835505490110b20825505490110ac08258c6390110cc1635c86390110ac0835886290110cc1735886290110ac0864c83290110cc1764c83290110a14835945450110a248259454501109a3825cf6450110993835cb64501109a3825cf5450110993835cb5450110c50651cd5450110c60651c95450110d81739c85450110d82735c85450110d81735c85450110a508558c6350110ac08258c63501109a1829d25350110c30655d053501109a1821d74350110d1075dcd4350110b8282dcd43501109928794d43501109908754d4350110a908654d4350110d107554d4350110b808254d4350110a60855886250110ac0835886250110991839d25250110c30655d05250110991831d
  | 2 => 0x914254432e05644c95114432e4132545601443288d841d93294032989841c13294032ac0804c96194032989841c13254032919841c13254032929841c1325403290d841c13254032b09841c13254032b41811c13254032948805d5320cb41a4980195320c941d05435c44354841e05535096110841d11435c44354041d21425c44254041931841c53254041b2182d0d4154041d107350d4154041b1183d094154041d20725094154041a6282d516010731a31849496010731c33645c04154331e055458d6210431e115498d6010431e115458d6010431e21549896010431e21545896010431a5283d516010721a318494d6010721c33645c04154321a31801c56414c21e055458d6210421e115498d6010421e115458d6010421e21549896010421e21545896010421a318414d6010421988805d1320cb40989841c1320cb4084c87595320ca40d41325c03254640a89844c9600c940a48805886254c40a488058c6354840c49651c1320c840b40804c83254440c52735c06155330c53655c06150f308c9861c142ccb30a24825906454630b40804c83254630a31849456010630961801c56414930c25645c46414930c29645c06414930d43711c14314930c60525c06150930989821c14350130c31545c06150c30961801c54354830b08805c9540c830c0d541c96390030c0c76552524c030c0c76951524c030c0c76551524c030e055418a514c030a448654a514c030e0554189514c030a4486549514c030ac181d8c624c030c62725c06155320c63655c06150b208c9861c1438cb20a4880590534cb20c0d7414c604cb20d41719c3530ca20a14835906454620b40804c83254620a31849456010620a0d8414c624c220951801c56414d20c15645c46414d20c19645c06414d20c50535c06150d2084d8714c6050920e4053d846050920a4880590534c920c0d7414c604c920c0e75592320c120a48805906254c20c0d741886054c20c31545c06150820c51535c06150820b08805cd540c820949851c1430c820c0d541cd629002084c8754d629002084f87d97324c020c0e76553324c020c0d75590320c020a0d86550320c02084d87d506348020a0d859506348020c0d7418f5348020c0c765525348020c0c769515348020c0c76551534802084e869d95348020e055418e5148020a448654e5148020e055418d5148020a448654d5148020cc0635c76248020e055458d6210710e115498d6010710e115458d6010710e21549896010710e21545896010710e055458d6215310e115498d6015310e115458d6015310e21549896015310e21545896015310c31645c05414f10a51801965350f10c31645c05414b10a61801965250b10947855d1320cb109c0805d1320cb10985841c1320cb10ac0804c9600cb10a478550c624c310c85641c9300c31
  | 3 => 0xb8b1b3693886720601d000000000000000000572847301c0f0a6000003f120c8002af000149d83023e9f800002745632ed9afc0000000102ca1b0ce2506e80043800001dc0010a0025c3815a003483400058000d380022a9c0000027936a7844838000020800000000000009000340359d6000000020426088000000026000000aba64d2b3e1f9a8052ce0000000000ae0007f05600000932f08780012a348814c5200000000000a400134a832600000aa1e86b0000009a000005a8ce000000018a000000036ea59887035ac6800002f22b06c8591a8d8b63a0001e0ca00000a408cc3800000007d1ce000547280055800a52c41f2ee0030c8328ab62c047842ad18c2f30a1daa4a62287791c001163c00000172000f29631809000000000000031a00000007b3343e8000000000230000000017e0020a000700000c870ecd58e46c8000593a0000000000000000023a00142352100022a0019600000000de000b4000c40000ab4000aa80000000002dc7c8001322e71072c413c9695e000005d000ac92e518943d864590227b922ac32a3a800120eed132250314668f8b91d42eb507c10cc19aac5b12d7000002c8000002c00000000370000028c001c6db0000baecba33a40000000000005e0000078118368364183a010f4900300a1b65b1040aad2c0800001d000000a2000cc800b58005f0000006800000cf00000248000000d244258000025e000a830800001fab9a2cc1152210000009c5504e00066d31620024a00000000000600000364169c2000b2ab0004c926792eac72e09a0a27999034a8200080000000000045224a4800682428f01a000004fa060b1700000618b58850e20400600c03004030000600001058000240700c010040300c0500800004000040600000018090000100800008010040100404000010040100000010060040000c0a000000000000803040000180000406018010000000c0503801000120000c010000040000003008010000700401000000600500400000020040400002004000100100c00000000000e020080000f01414018010000300400008010000103c0400007000040000a00c000240000401000050001300404c61625c05114143c51635c05114142a31811c16414132c52735c06155032c51735c06155032c62725c06155032c61725c06155032ac08058b6150c32ac0805886150c32b05811514350832b09801514350832ac08058f6150832ac08058c6150832c0f75dd1644c832cc3711c1644c832cc0711c1644c832c49851c1644c832cc2811c1644c832cc1811c1644c8329c1801c5544c832d05545c4544c832d09545c0544c832c0d759d0604c832c0d755d0604c832c88805d0604c832c45759c4604c832c85749c4604c832c45755c4604c832c85745c4604c832a19801914354432a29801
  | 4 => 0xae8004432498b42d18000031ead938000005281263a22bd29a0012c001da000006f0009180000124099ea000000000060000000002497a652665a0cc95b686e254b882074ad400040000000c9fe699f8510380000080a70661a200000002186726e8e10889b00b69f60026c00000001be0018432308a9800000000000000286000080001ebd800000009d92a140000000017112d52722b800b32328488e5b8466786e0000000252209e260800bf9921600e6b976beaca00000000004a2de001869a8d80032c002a200000000003987a9e800000a0003520000086a786d2be000109f000cc03e0028eb080000000d79782fb625380059950000fe1ab60a0000000aa4c1a4002f8da8
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x10749ab4e0c29430a41002e3021f5878e251c0140f4c00a900000007120001946000000000b0648680005a806aa608458124bd100364570a1e302100a8700ed0a08001a0e10615811c1644c832a04ca900ba0c0990654819120174181320ca5032840264b0ca0194a0650804c9600cb10c04b2b0838264194212049855163588544428092eaa2c6b10a8884842615458d6015110b00492a8b1ac02a221220985516258054442c0126aa2c4b00a8886081d58099142cc910c083ab01322871922188186a10704c8324431030cc20e09906488460650874ca600c9109204ab08992c0192210c0985d9320ca40443200eb416e6a1a80886042187554d4350110c803a904a9a86a022190075a0f72509404430410c3aaa4a1280886401d48354942501109804ab0899064a02216009550c6250130443102c8412e7200608862021d64989300c110c4043cc8b12601822188087591624c03044310308318e09964088510a57635c03288110a40ca0c639261102210c19818c705092044310308318e09924088680214635094048110c40c20e4382c6102218816420d729002044218130b1ae52004088620619740c83008110a40cbac819060102210c198d9073480204429032d320e6900408862061073d8d2008110c4043ac931a40102218808799163480204431010eb22c69004088430a5e8758d2008110
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 42
  | 6 => 1947
  | 5 => 11355
  | 4 => 6817
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
  | 7 => packedAt gbK7 (770+((h/14+packedAt gbK7 (672+(h % 14)*7) 7) % 96)*7) 7
  | 6 => packedAt gbK6 (60357+((h/649+packedAt gbK6 (52569+(h % 649)*12) 12) % 2570)*12) 12
  | 5 => packedAt gbK5 (484480+((h/3785+packedAt gbK5 (431490+(h % 3785)*14) 14) % 13627)*15) 15
  | 4 => packedAt gbK4 (365841+((h/2272+packedAt gbK4 (334033+(h % 2272)*14) 14) % 10887)*14) 14
  | 3 => packedAt gbK3 (27860+((h/146+packedAt gbK3 (26400+(h % 146)*10) 10) % 702)*10) 10
  | 2 => packedAt gbK2 (3575+((h/16+packedAt gbK2 (3479+(h % 16)*6) 6) % 64)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff83ff1fc3ffffc1c71f8fc0ff1ffffc1331ff
  | 1 => 0x7fc1fe3fc0f1e3e07e3f1ff0fe383806dcecc
  | 2 => 0x7ffe003fff01ffff803fe000ffc03ff8e0f0f
  | 3 => 0xf8000003ffffe03ffffc00000ffffc03f00ff0
  | 4 => 0xfffffffc0000003ffffffffff0000003fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10884020482000000104824221048888011055
  | 1 => 0x3118c60488e224460321908e272119182546cc
  | 2 => 0xc2218a491146581ac80324144a4822718e0b0a
  | 3 => 0x60731492228c0cad564800288c927022f00da0
  | 4 => 0x8442180033089131a4924930c00040435aa000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeeeeaa0feeeeaa0feeeeaa0feeeeaa0feeeeaa0feeeeaa0feeeeaa0feeeeaa0feeeeaa0feeeeaa0feeeeaa0feeeeaa0feeeeaa0feeeeaa0feeeeaa0feeeeaa0, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12925
namespace PEqualNP.Outside.L_meta_12925
open PEqualNP.Outside.L_meta_12925.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6816 : Interval gbAtlas 4 6816 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 6817 := (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_96) (concat bgb_4_192 bgb_4_288)) (concat (concat bgb_4_384 bgb_4_480) (concat bgb_4_576 (concat bgb_4_672 bgb_4_768)))) (concat (concat (concat bgb_4_864 bgb_4_960) (concat bgb_4_1056 bgb_4_1152)) (concat (concat bgb_4_1248 bgb_4_1344) (concat bgb_4_1440 (concat bgb_4_1536 bgb_4_1632))))) (concat (concat (concat (concat bgb_4_1728 bgb_4_1824) (concat bgb_4_1920 bgb_4_2016)) (concat (concat bgb_4_2112 bgb_4_2208) (concat bgb_4_2304 (concat bgb_4_2400 bgb_4_2496)))) (concat (concat (concat bgb_4_2592 bgb_4_2688) (concat bgb_4_2784 bgb_4_2880)) (concat (concat bgb_4_2976 bgb_4_3072) (concat bgb_4_3168 (concat bgb_4_3264 bgb_4_3360)))))) (concat (concat (concat (concat (concat bgb_4_3456 bgb_4_3552) (concat bgb_4_3648 bgb_4_3744)) (concat (concat bgb_4_3840 bgb_4_3936) (concat bgb_4_4032 (concat bgb_4_4128 bgb_4_4224)))) (concat (concat (concat bgb_4_4320 bgb_4_4416) (concat bgb_4_4512 bgb_4_4608)) (concat (concat bgb_4_4704 bgb_4_4800) (concat bgb_4_4896 (concat bgb_4_4992 bgb_4_5088))))) (concat (concat (concat (concat bgb_4_5184 bgb_4_5280) (concat bgb_4_5376 bgb_4_5472)) (concat (concat bgb_4_5568 bgb_4_5664) (concat bgb_4_5760 (concat bgb_4_5856 bgb_4_5952)))) (concat (concat (concat bgb_4_6048 bgb_4_6144) (concat bgb_4_6240 bgb_4_6336)) (concat (concat bgb_4_6432 bgb_4_6528) (concat bgb_4_6624 (concat bgb_4_6720 bgb_4_6816)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfeeefeeefeeeeaa0feeefeeefeeeeaa0feeefeeefeeeeaa0feeefeeefeeeeaa0feeefeeefeeeeaa0feeefeeefeeeeaa0feeefeeefeeeeaa0feeefeeefeeeeaa0
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075694 * 2 ^ 32 + 4277070496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12925.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.and,[3,6]⟩,⟨.or,[0,7]⟩,⟨.and,[2,8]⟩,⟨.or,[0,9]⟩,⟨.or,[1,10]⟩,⟨.or,[2,10]⟩,⟨.and,[3,12]⟩,⟨.or,[9,13]⟩,⟨.or,[6,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075694 * 2 ^ 32 + 4277070496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075694 * 2 ^ 32 + 4277070496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12925

open PEqualNP.Outside.L_meta_12925 in
theorem PEqualNP.Outside.L_meta_12925 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075694 * 2 ^ 32 + 4277070496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075694 * 2 ^ 32 + 4277070496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
